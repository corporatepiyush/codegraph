#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Piyush Katariya
#
# @author Piyush Katariya
"""codegraph_ruby.py -- parse a Ruby tree into a graph and query it.

Targets Ruby 4.0 (released 2025-12-25; there was never a 3.5 -- 3.5 became
4.0). Parses with tree-sitter-ruby.

Read query 1 before anything else. In every other language in this repo the
call graph is mostly complete and the blindspot report is a footnote. In Ruby
it is the headline. `send`, `public_send`, `define_method`, `method_missing`,
`const_get`, `constantize` and `class_eval` on a heredoc all move dispatch from
the syntax tree to run time, and none of them leaves an edge behind. Every
reachability number here -- fan_in, dead-code, the taint walks -- is therefore a
LOWER BOUND, and the bound is loosest exactly where a framework does its most
interesting work. This tool counts the blind spots and tells you how blind it
is instead of quietly rounding them to zero.

Four Ruby facts baked in, all of them verified against the grammar rather than
assumed:

* tree-sitter-ruby 0.23.1 is ABI 14 and predates Ruby 4.0. Ruby 4.0 lets a
  binary logical operator LEAD a continuation line (`x = a` / `  && b`); on
  that shape this grammar sets `has_error` and records a MISSING node -- so it
  shows up as `files.n_missing_nodes`, not as `n_parse_errors`, and the count
  of affected files is in `meta.ruby4_leading_operator_files`. Measured: 0 such
  files in rails 8.2, 1 in a hand-written probe. The point is that it is
  visible at all rather than silently parsed as two statements, which is what
  a line-oriented scanner would do with it.
* Prism has been the default Ruby parser since 3.4, but it ships no Python
  bindings, so tree-sitter is the right tool here and shelling out to Ruby is
  not.
* "Chilled strings" (3.4+): a literal in a file WITHOUT a
  `# frozen_string_literal: true` magic comment warns on mutation but is still
  mutable, and frozen-by-default has NOT landed in 4.0. `has_frozen_literal`
  is per-file, and the string-churn query only fires where the comment is
  absent.
* A heredoc body is a SIBLING of the statement that opens it, not a child. So
  `class_eval <<~RUBY` puts Ruby source in a node that is not inside the call.
  Those bodies are scanned separately and counted as blindness.

Usage:
  python3 codegraph_ruby.py /path/to/repo --report
  python3 codegraph_ruby.py /path/to/repo --list
  python3 codegraph_ruby.py --deps"""
__author__ = "Piyush Katariya"
__license__ = "MIT"

# ---------------------------------------------------------------------------
# Self-contained on purpose: this one file is the whole tool. Copy it anywhere
# and run it. Requires CPython 3.14+ and its bundled SQLite 3.37 or newer --
# 3.37 for STRICT tables, which the schema uses throughout.
#
# Dependencies are declared in DEPS with a reason and installed with
# --install-deps. A grammar-backed analyzer REFUSES to run without its grammar:
# there is no regex fallback, and an empty graph reads exactly like a clean
# repository. codegraph_python.py and codegraph_c.py need no grammar at all.
#
# Nothing here is imported from a sibling file, and the schema below is this
# language's own. Other analyzers in this repo differ wherever their languages
# differ. Edit this file directly.
# ---------------------------------------------------------------------------

import sys as _sys

if _sys.version_info < (3, 14):                          # noqa: E402
    _sys.exit(
        "codegraph needs CPython 3.14 or newer; this is %d.%d.%d at %s.\n"
        "The schema uses STRICT tables (SQLite 3.37+) and codegraph_python.py\n"
        "parses with the running interpreter's own grammar, so on an older\n"
        "Python it would silently see less of a repository than is there.\n"
        "The other analyzers share this floor rather than each having one."
        % (_sys.version_info[0], _sys.version_info[1], _sys.version_info[2],
           _sys.executable))

import argparse
import array
import csv
import hashlib
import importlib
import importlib.util
import os
import re
import sqlite3
import stat
import subprocess
import sys
import time
from dataclasses import dataclass
from dataclasses import dataclass, field
from dataclasses import dataclass, field as dc_field
from typing import Any, Callable, Iterable, Iterator, Optional
from typing import Any, Callable, Iterable, Optional, Sequence
from typing import Any, Callable, Iterator, Optional
from typing import Any, Optional


# ==========================================================================
# _deps.py
# Dependency declaration and optional installation.
#
# Every language analyzer declares exactly what it needs and why. Nothing is
# installed behind the user's back: `ensure()` only reports, and only
# `--install-deps` actually runs pip.
#
# An analyzer must still RUN with nothing installed. A missing grammar downgrades
# the parse from a syntax tree to regex scanning; it never aborts the run. Which
# mode was used is recorded in the `meta` table so a query result can never be
# mistaken for something more precise than it is.
# ==========================================================================

@dataclass(frozen=True)
class Dep:
    """One importable module and the pip requirement that provides it."""
    module: str
    pip: str
    why: str
    optional: bool = True
    #: Minimum version we have actually verified against, for the record.
    verified: str = ""

    @property
    def present(self) -> bool:
        try:
            return importlib.util.find_spec(self.module) is not None
        except (ImportError, ValueError):
            return False

    def version(self) -> str:
        try:
            mod = importlib.import_module(self.module)
        except Exception:
            return ""
        for attr in ("__version__", "VERSION", "version"):
            v = getattr(mod, attr, None)
            if isinstance(v, str):
                return v
            if isinstance(v, tuple):
                return ".".join(str(p) for p in v)
        try:
            from importlib.metadata import version as _v
            return _v(self.pip.split("[")[0].split("=")[0].split(">")[0])
        except Exception:
            return "?"

@dataclass
class DepSet:
    """The dependency surface of one analyzer."""
    lang: str
    deps: list[Dep] = field(default_factory=list)

    def missing(self) -> list[Dep]:
        return [d for d in self.deps if not d.present]

    def present(self) -> list[Dep]:
        return [d for d in self.deps if d.present]

    def required_missing(self) -> list[Dep]:
        return [d for d in self.missing() if not d.optional]

    # -- reporting ---------------------------------------------------------
    def describe(self) -> str:
        out = ["dependencies for codegraph-%s:" % self.lang]
        if not self.deps:
            out.append("  (none -- pure standard library)")
            return "\n".join(out)
        for d in self.deps:
            mark = "ok " if d.present else ("MISSING" if not d.optional else "absent ")
            ver = d.version() if d.present else ""
            tag = "required" if not d.optional else "optional"
            out.append("  [%-7s] %-28s %-10s %s" % (mark, d.pip, ver, tag))
            out.append("             %s" % d.why)
            if d.verified:
                out.append("             verified against %s" % d.verified)
        miss = self.missing()
        if miss:
            out.append("")
            out.append("install with:")
            out.append("  %s" % self.pip_command())
            out.append("or let the tool do it:")
            out.append("  python3 %s --install-deps" % _script_name())
        return "\n".join(out)

    def pip_command(self, missing_only: bool = True) -> str:
        want = self.missing() if missing_only else self.deps
        if not want:
            return "(nothing to install)"
        return "%s -m pip install %s" % (
            sys.executable, " ".join(sorted(d.pip for d in want)))

    # -- installation ------------------------------------------------------
    def install(self, quiet: bool = False, only_binary: bool = True) -> bool:
        """pip-install everything missing. Returns True if all present after."""
        want = self.missing()
        if not want:
            if not quiet:
                print("all dependencies already present")
            return True
        cmd = [sys.executable, "-m", "pip", "install"]
        if only_binary:
            # Source builds of a tree-sitter grammar need a C toolchain and
            # take minutes. If there is no wheel we would rather fail loudly
            # and fall back to regex than silently start compiling.
            cmd += ["--only-binary", ":all:"]
        cmd += sorted(d.pip for d in want)
        if not quiet:
            print("running: %s" % " ".join(cmd))
        proc = subprocess.run(cmd, capture_output=True, text=True)
        rc = proc.returncode
        out = (proc.stdout or "") + (proc.stderr or "")
        if not quiet and out.strip():
            print(out.rstrip())

        if rc != 0 and "externally-managed-environment" in out:
            # A Homebrew or distro Python refuses to be written to (PEP 668).
            # Telling the user to pass --break-system-packages would be
            # advising them to damage the interpreter their OS depends on.
            print(_pep668_advice(self))
            return False
        if rc != 0 and only_binary:
            if not quiet:
                print("no wheel available for this interpreter; "
                      "retrying without --only-binary (needs a C compiler)")
            rc = subprocess.call([c for c in cmd
                                  if c not in ("--only-binary", ":all:")])
        importlib.invalidate_caches()
        still = self.missing()
        if still and not quiet:
            print("still missing: %s" % ", ".join(d.pip for d in still))
            print("the analyzer will run in degraded (regex) mode")
        return not still

def _script_name() -> str:
    import os
    return os.path.basename(sys.argv[0] or "codegraph_<lang>.py")

def _pep668_advice(ds: "DepSet") -> str:
    return (
        "\nthis Python is externally managed (PEP 668) -- pip will not write "
        "to it,\nand overriding that with --break-system-packages can break "
        "the interpreter\nyour OS depends on. Use a virtual environment "
        "instead:\n\n"
        "  python3 -m venv .venv\n"
        "  .venv/bin/pip install %s\n"
        "  .venv/bin/python %s <repo>\n\n"
        "There is no way to run without the grammar: an analyzer with no\n"
        "parser refuses rather than emitting an empty graph, because an\n"
        "empty graph reads exactly like a clean repository."
        % (" ".join(sorted(d.pip for d in ds.missing())), _script_name()))

TREE_SITTER = Dep(
    module="tree_sitter",
    pip="tree-sitter>=0.25",
    why="incremental parser runtime. Without it a grammar-backed analyzer "
        "will NOT run -- there is no regex fallback, because an empty graph "
        "reads exactly like a clean repository",
    verified="0.26.0 (cp314 macOS arm64 wheel)",
)

def grammar(lang: str, module: str, pip: str, verified: str = "") -> Dep:
    return Dep(
        module=module,
        pip=pip,
        why="tree-sitter grammar for %s. Required: without it this analyzer "
            "refuses to run rather than produce an empty graph" % lang,
        verified=verified,
    )


# ==========================================================================
# _ts.py
# tree-sitter loading, with an honest fallback.
#
# Two rules govern this module.
#
# 1. A missing grammar is not an error. The analyzer degrades to regex scanning
#    and says so. A tool that refuses to start is worth less than a tool that
#    tells you which of its answers are approximate.
#
# 2. The parse mode is recorded, per run, in the `meta` table. Every report
#    prints it. `n_parse_errors` on `files` counts tree-sitter ERROR nodes, so a
#    file the grammar could not handle is visible rather than silently thin.
#
# The py-tree-sitter API changed incompatibly at 0.22/0.23 (`Language(ptr, name)`
# became `Language(ptr)`, `Parser.set_language()` became the `parser.language`
# property). Everything here targets the >=0.25 API and probes for the old one so
# an older wheel already on the box does not produce a confusing AttributeError.
# ==========================================================================

MODE_TREE_SITTER = "tree-sitter"

MODE_REGEX = "regex-fallback"

MODE_NATIVE = "native-ast"

MODE_BRACE_SCAN = "brace-scan"

@dataclass
class ParserHandle:
    """A parser plus the story of how we got it."""
    mode: str
    parser: Any = None
    language: Any = None
    lang_name: str = ""
    grammar_pip: str = ""
    grammar_version: str = ""
    runtime_version: str = ""
    note: str = ""

    @property
    def ok(self) -> bool:
        return self.parser is not None

    def parse(self, src: bytes):
        return self.parser.parse(src)

    def banner(self) -> str:
        if self.mode == MODE_TREE_SITTER:
            return "parser: tree-sitter %s + %s %s" % (
                self.runtime_version, self.grammar_pip, self.grammar_version)
        if self.mode == MODE_NATIVE:
            return "parser: %s" % self.note
        return "parser: REGEX FALLBACK (%s) -- spans and nesting are approximate" % self.note

def load(lang_name: str, grammar_module: str, grammar_pip: str,
         symbol: str = "language") -> ParserHandle:
    """Build a tree-sitter parser for `lang_name`, or explain why not."""
    try:
        ts = importlib.import_module("tree_sitter")
    except ImportError:
        return ParserHandle(mode=MODE_REGEX, lang_name=lang_name,
                            grammar_pip=grammar_pip,
                            note="tree_sitter not installed")
    try:
        gm = importlib.import_module(grammar_module)
    except ImportError:
        return ParserHandle(mode=MODE_REGEX, lang_name=lang_name,
                            grammar_pip=grammar_pip,
                            note="%s not installed" % grammar_pip)

    fn = getattr(gm, symbol, None) or getattr(gm, "language", None)
    if fn is None:
        return ParserHandle(mode=MODE_REGEX, lang_name=lang_name,
                            grammar_pip=grammar_pip,
                            note="%s exposes no %s()" % (grammar_module, symbol))
    try:
        ptr = fn()
    except Exception as exc:                                   # pragma: no cover
        return ParserHandle(mode=MODE_REGEX, lang_name=lang_name,
                            grammar_pip=grammar_pip,
                            note="%s() raised %s" % (symbol, exc))

    language = _make_language(ts, ptr, lang_name)
    if language is None:
        return ParserHandle(mode=MODE_REGEX, lang_name=lang_name,
                            grammar_pip=grammar_pip,
                            note="ABI mismatch between tree-sitter runtime and "
                                 "%s -- upgrade both together" % grammar_pip)

    abi_note = _check_abi(ts, language, grammar_pip)
    if abi_note:
        return ParserHandle(mode=MODE_REGEX, lang_name=lang_name,
                            grammar_pip=grammar_pip, note=abi_note)
    parser = _make_parser(ts, language)
    if parser is None:
        return ParserHandle(mode=MODE_REGEX, lang_name=lang_name,
                            grammar_pip=grammar_pip,
                            note="could not attach language to parser")

    return ParserHandle(
        mode=MODE_TREE_SITTER, parser=parser, language=language,
        lang_name=lang_name, grammar_pip=grammar_pip,
        grammar_version=_ver(gm, grammar_pip),
        runtime_version=_ver(ts, "tree-sitter"),
    )

def _make_language(ts: Any, ptr: Any, name: str) -> Optional[Any]:
    if isinstance(ptr, getattr(ts, "Language", ())):
        return ptr
    for args in ((ptr,), (ptr, name)):          # >=0.22 first, then legacy
        try:
            return ts.Language(*args)
        except (TypeError, ValueError):
            continue
        except Exception:
            return None
    return None

def _check_abi(ts: Any, language: Any, grammar_pip: str) -> str:
    """Refuse a grammar the runtime cannot speak, with a message that says why.

    Several grammars have not been rebuilt in well over a year and sit at an
    older ABI than the runtime's floor. When that floor rises, construction
    fails somewhere deep in the C extension with nothing naming the culprit.
    Checking here turns that into one sentence naming the package and the two
    numbers involved.
    """
    abi = getattr(language, "abi_version", None)
    if abi is None:
        abi = getattr(language, "version", None)
    if abi is None:
        return ""
    lo = getattr(ts, "MIN_COMPATIBLE_LANGUAGE_VERSION", None)
    hi = getattr(ts, "LANGUAGE_VERSION", None)
    if lo is not None and abi < lo:
        return ("%s is ABI %d but this tree-sitter runtime accepts %d-%s; "
                "upgrade the grammar or pin tree-sitter lower"
                % (grammar_pip, abi, lo, hi if hi is not None else "?"))
    if hi is not None and abi > hi:
        return ("%s is ABI %d, newer than this tree-sitter runtime supports "
                "(max %d); upgrade tree-sitter" % (grammar_pip, abi, hi))
    return ""

def _make_parser(ts: Any, language: Any) -> Optional[Any]:
    try:                                        # >=0.22
        return ts.Parser(language)
    except TypeError:
        pass
    except Exception:
        return None
    try:
        p = ts.Parser()
        try:
            p.language = language               # >=0.22 property
        except AttributeError:
            p.set_language(language)            # <=0.21
        return p
    except Exception:                                          # pragma: no cover
        return None

def _ver(mod: Any, pip_name: str) -> str:
    v = getattr(mod, "__version__", None)
    if isinstance(v, str):
        return v
    try:
        from importlib.metadata import version
        return version(pip_name.split(">")[0].split("=")[0])
    except Exception:
        return "?"

def walk(node: Any) -> Iterator[Any]:
    """Every node in the subtree, parents before children.

    Uses an explicit stack rather than recursion: a minified bundle or a
    generated parser table nests deep enough to blow the Python stack, and a
    RecursionError halfway through a repo scan is indistinguishable from a
    crash.
    """
    stack = [node]
    while stack:
        n = stack.pop()
        yield n
        stack.extend(reversed(n.children))

def walk_cursor(node: Any) -> Iterator[tuple[Any, int]]:
    """Every node with its depth, using a TreeCursor (much faster than
    touching `.children`, which materialises a Python list per node)."""
    cursor = node.walk()
    depth = 0
    while True:
        yield cursor.node, depth
        if cursor.goto_first_child():
            depth += 1
            continue
        while not cursor.goto_next_sibling():
            if not cursor.goto_parent():
                return
            depth -= 1

def named_children(node: Any, *types: str) -> list[Any]:
    if not types:
        return [c for c in node.named_children]
    want = set(types)
    return [c for c in node.named_children if c.type in want]

def child_by_field(node: Any, field: str) -> Optional[Any]:
    return node.child_by_field_name(field)

def text_of(node: Any, src: bytes) -> str:
    return src[node.start_byte:node.end_byte].decode("utf-8", "replace")

def field_text(node: Any, field: str, src: bytes, default: str = "") -> str:
    c = node.child_by_field_name(field)
    return text_of(c, src) if c is not None else default

def descendants_of_type(node: Any, *types: str) -> Iterator[Any]:
    want = set(types)
    for n in walk(node):
        if n.type in want:
            yield n

def count_types(node: Any, counter_types: dict[str, str]) -> dict[str, int]:
    """One pass over a subtree, counting node types into named buckets.

    `counter_types` maps a tree-sitter node type to the metric it feeds. One
    walk for all metrics: walking a large function body once per metric is the
    difference between a repo scan taking seconds and taking minutes.
    """
    out: dict[str, int] = {}
    for n in walk(node):
        key = counter_types.get(n.type)
        if key is not None:
            out[key] = out.get(key, 0) + 1
    return out

def has_error(node: Any) -> bool:
    return node.has_error

def count_errors(root: Any) -> tuple[int, int]:
    """(error nodes, missing nodes) in the tree.

    A file with errors is still indexed -- tree-sitter recovers and the symbols
    around the damage are real. The count travels with the file row so a query
    can exclude, or specifically hunt, the parts we got wrong.
    """
    if not root.has_error:
        return 0, 0
    errs = miss = 0
    for n in walk(root):
        if n.type == "ERROR":
            errs += 1
        elif n.is_missing:
            miss += 1
    return errs, miss

class Query:
    """A compiled tree-sitter query, tolerant of the 0.24->0.25 API split.

    `Language.query()` was removed in 0.25 in favour of a standalone `Query`
    class and a `QueryCursor` for execution. Both spellings are probed so one
    analyzer source works across the wheels people actually have installed.
    """

    def __init__(self, handle: ParserHandle, source: str):
        self.ok = False
        self._q = None
        self._cursor_cls = None
        if not handle.ok:
            return
        try:
            ts = importlib.import_module("tree_sitter")
            qcls = getattr(ts, "Query", None)
            if qcls is not None:
                try:
                    self._q = qcls(handle.language, source)
                except TypeError:
                    self._q = handle.language.query(source)
            else:
                self._q = handle.language.query(source)
            self._cursor_cls = getattr(ts, "QueryCursor", None)
            self.ok = True
        except Exception:
            self.ok = False
            self._q = None

    def captures(self, node: Any) -> dict[str, list[Any]]:
        if not self.ok:
            return {}
        try:
            if self._cursor_cls is not None:
                return self._cursor_cls(self._q).captures(node)
            return self._q.captures(node)
        except Exception:
            return {}

    def matches(self, node: Any) -> list[Any]:
        if not self.ok:
            return []
        try:
            if self._cursor_cls is not None:
                return self._cursor_cls(self._q).matches(node)
            return self._q.matches(node)
        except Exception:
            return []


# ==========================================================================
# _core.py
# The part of a code graph that does not depend on the language.
#
# Every analyzer in this repo re-reads and re-parses the tree on every run and
# builds the whole graph in a `:memory:` database. A graph file on disk gets read
# after the code it describes has moved on, and a stale graph is worse than none:
# it answers confidently and wrongly.
#
# What lives here: the file walk, the universal schema, the build driver, the
# aggregate pass, the renderer and the CLI. What does not: anything that knows
# what a function looks like. That is the analyzer's job, and it is the only part
# that needs writing per language.
#
# The universal schema is deliberately wider than any one language needs. A
# column that is always zero for Go costs nothing and keeps one query catalogue
# readable across nine languages; a column that exists only for Rust would force
# every shared query to branch.
# ==========================================================================

SCHEMA_VERSION = 1

COMMON_SKIP_DIRS = {
    ".git", ".hg", ".svn", ".jj", ".idea", ".vscode", ".vs", ".claude",
    "node_modules", "bower_components", "vendor", "third_party", "thirdparty",
    "external", "externals", "deps", "Godeps", "_vendor",
    "__pycache__", ".mypy_cache", ".pytest_cache", ".ruff_cache", ".tox",
    ".venv", "venv", "env", ".env", "virtualenv",
    "build", "_build", "dist", "out", "target", "bin", "obj", ".gradle",
    ".next", ".nuxt", ".svelte-kit", ".parcel-cache", ".turbo", ".cache",
    "coverage", "htmlcov", ".nyc_output", "site-packages",
}

GENERATED_MARKERS = (
    "@generated", "DO NOT EDIT", "Code generated by", "AUTO-GENERATED",
    "autogenerated", "This file was automatically generated",
    "Generated by the protocol buffer compiler", "@flow-generated",
)

GENERATED_NAME_RE = re.compile(
    r'(\.min\.|\.bundle\.|[-_.](gen|generated|pb|g)\.|_pb2|\.g\.dart$'
    r'|\.designer\.|^zz_generated)', re.I)

TEST_PATH_RE = re.compile(
    r'(^|/)(tests?|test-d|spec|specs|__tests__|__snapshots__|testing|'
    r'e2e|integration[-_]tests?|testdata|test_data|test-data|'
    r'fixtures?)(/|$)', re.I)

TEST_NAME_RE_BY_LANG: dict[str, "re.Pattern[str]"] = {
    "python": re.compile(r'(^test_|_test\.py$|^conftest\.py$)'),
    "go": re.compile(r'_test\.go$'),
    "rust": re.compile(r'(^tests?\.rs$|_test\.rs$)'),
    "java": re.compile(r'(^Test[A-Z]|Tests?\.java$|TestCase\.java$|IT\.java$)'),
    "javascript": re.compile(r'(\.test\.|\.spec\.|^test-|-test\.)'),
    "typescript": re.compile(r'(\.test\.|\.spec\.|\.test-d\.|^test-|-test\.)'),
    "php": re.compile(r'(Test\.php$|^test_)'),
    "ruby": re.compile(r'(_spec\.rb$|_test\.rb$|^test_)'),
    "c": re.compile(r'(^test_|_test\.[ch]$|^t_)'),
}

TEST_NAME_RE = re.compile(r'(^test_|_test\.|\.test\.|\.spec\.)')

VENDOR_PATH_RE = re.compile(
    r'(^|/)(vendor|third_party|thirdparty|external|node_modules|deps)(/|$)', re.I)

MARKER_RE = re.compile(
    r'\b(TODO|FIXME|XXX|HACK|BUG|NOTE|WARNING|OPTIMIZE|REVIEW|DEPRECATED|'
    r'SAFETY|PANIC|UNSAFE)\b[ \t]*[:\-(]', re.I)

MAGIC_OK = {0, 1, 2, -1, 10, 100, 1000, 8, 16, 32, 64, 128, 256, 512, 1024,
            255, 65535, 4096, 24, 60, 365, 7, 12, 3, 4, 6}

def module_of(rel: str, depth: int = 2) -> str:
    """A stable grouping key for a path.

    Two levels, not one: `src/` alone puts an entire repo in one bucket, and
    the full directory makes every leaf its own module. Two levels is what
    actually separates subsystems in the repos this was tested against.
    """
    parts = rel.replace(os.sep, "/").split("/")
    if len(parts) <= 1:
        return "(root)"
    head = parts[:-1]
    if head and head[0] in ("src", "lib", "source", "internal", "pkg", "app"):
        head = head[:depth + 1]
    else:
        head = head[:depth]
    return "/".join(head) or "(root)"

def is_generated(name: str, head: str) -> bool:
    if GENERATED_NAME_RE.search(name):
        return True
    return any(m in head for m in GENERATED_MARKERS)

@dataclass
class FileRec:
    """One source file, already read and classified."""
    fid: int
    mid: int
    rel: str
    abspath: str
    text: str
    data: bytes
    lang: str
    is_test: bool
    is_generated: bool
    is_vendored: bool

@dataclass
class Buffers:
    """Row accumulators.

    Everything is buffered and flushed with `executemany`. Per-row `INSERT`
    across a million-symbol repo spends more time in the sqlite3 binding layer
    than in parsing.
    """
    params: list[tuple] = field(default_factory=list)
    fields: list[tuple] = field(default_factory=list)
    locals: list[tuple] = field(default_factory=list)
    literals: list[tuple] = field(default_factory=list)
    markers: list[tuple] = field(default_factory=list)
    attributes: list[tuple] = field(default_factory=list)
    imports: list[tuple] = field(default_factory=list)
    hazards: list[tuple] = field(default_factory=list)
    enum_members: list[tuple] = field(default_factory=list)
    edges: dict[tuple[int, int], list[int]] = field(default_factory=dict)
    callsites: set[tuple[int, int, int]] = field(default_factory=set)
    unresolved: dict[tuple[int, str], list[int]] = field(default_factory=dict)
    extra: dict[str, list[tuple]] = field(default_factory=dict)

    def rows(self, table: str) -> list[tuple]:
        """Accumulator for a language-specific table."""
        return self.extra.setdefault(table, [])

    def add_edge(self, caller: int, callee: int, same_file: bool,
                 same_module: bool, line: int = 0) -> None:
        key = (caller, callee)
        e = self.edges.get(key)
        if e is None:
            self.edges[key] = [1, int(same_file), int(same_module),
                               int(caller == callee)]
        else:
            e[0] += 1
        if line:
            self.callsites.add((caller, callee, line))

    def add_unresolved(self, caller: int, name: str, line: int) -> None:
        """A call we saw but could not point at a definition.

        This is the honesty column. Dynamic dispatch, reflection, function
        pointers and cross-language calls all land here, and a query that
        reasons over the call graph can check how blind it is before trusting
        its own answer.
        """
        key = (caller, name)
        u = self.unresolved.get(key)
        if u is None:
            self.unresolved[key] = [1, line]
        else:
            u[0] += 1

    def add_hazard(self, sid: int, pattern: str, category: str,
                   n: int = 1, line: int = 0) -> None:
        self.hazards.append((sid, pattern, category, n, line))

PRAGMAS = """
PRAGMA journal_mode=OFF;
PRAGMA synchronous=OFF;
PRAGMA page_size=16384;
PRAGMA temp_store=MEMORY;
PRAGMA cache_size=-262144;
PRAGMA foreign_keys=OFF;
"""

BASE_SCHEMA = r"""
CREATE TABLE meta(
    key TEXT PRIMARY KEY,
    value TEXT NOT NULL
) WITHOUT ROWID, STRICT;

CREATE TABLE modules(
    id INTEGER PRIMARY KEY,
    name TEXT NOT NULL UNIQUE,
    kind TEXT NOT NULL DEFAULT 'source',
    n_files INT NOT NULL DEFAULT 0,
    n_symbols INT NOT NULL DEFAULT 0,
    n_public INT NOT NULL DEFAULT 0,
    sloc INT NOT NULL DEFAULT 0,
    fan_in INT NOT NULL DEFAULT 0,
    fan_out INT NOT NULL DEFAULT 0,
    instability REAL NOT NULL DEFAULT 0.0
) STRICT;

CREATE TABLE files(
    id INTEGER PRIMARY KEY,
    path TEXT NOT NULL UNIQUE,
    dir TEXT NOT NULL,
    basename TEXT NOT NULL,
    ext TEXT NOT NULL,
    lang TEXT NOT NULL,
    module_id INT REFERENCES modules(id),
    bytes INT NOT NULL,
    lines INT NOT NULL,
    sloc INT NOT NULL,
    blank_lines INT NOT NULL DEFAULT 0,
    comment_lines INT NOT NULL DEFAULT 0,
    doc_lines INT NOT NULL DEFAULT 0,
    max_line_len INT NOT NULL DEFAULT 0,
    sha1 TEXT NOT NULL,
    parsed INT NOT NULL DEFAULT 0,
    is_test INT NOT NULL DEFAULT 0,
    is_generated INT NOT NULL DEFAULT 0,
    is_vendored INT NOT NULL DEFAULT 0,
    n_parse_errors INT NOT NULL DEFAULT 0,
    n_missing_nodes INT NOT NULL DEFAULT 0,
    parse_ms REAL NOT NULL DEFAULT 0.0,
    n_symbols INT NOT NULL DEFAULT 0,
    n_functions INT NOT NULL DEFAULT 0,
    n_types INT NOT NULL DEFAULT 0,
    n_imports INT NOT NULL DEFAULT 0,
    total_cyclo INT NOT NULL DEFAULT 0,
    max_cyclo INT NOT NULL DEFAULT 0,
    total_risk INT NOT NULL DEFAULT 0
) STRICT;

CREATE TABLE symbols(
    id INTEGER PRIMARY KEY,
    file_id INT NOT NULL REFERENCES files(id),
    module_id INT REFERENCES modules(id),
    parent_id INT REFERENCES symbols(id),
    name TEXT NOT NULL,
    qual_name TEXT NOT NULL DEFAULT '',
    kind TEXT NOT NULL,
    line_start INT NOT NULL,
    line_end INT NOT NULL,
    n_lines INT NOT NULL DEFAULT 0,
    byte_start INT NOT NULL DEFAULT 0,
    byte_end INT NOT NULL DEFAULT 0,
    signature TEXT,
    return_type TEXT,
    visibility TEXT NOT NULL DEFAULT '',

    -- shape
    n_params INT NOT NULL DEFAULT 0,
    n_optional_params INT NOT NULL DEFAULT 0,
    n_generic_params INT NOT NULL DEFAULT 0,
    n_overloads INT NOT NULL DEFAULT 0,
    arity_rank INT NOT NULL DEFAULT 0,

    -- flags
    is_public INT NOT NULL DEFAULT 0,
    is_static INT NOT NULL DEFAULT 0,
    is_async INT NOT NULL DEFAULT 0,
    is_generator INT NOT NULL DEFAULT 0,
    is_abstract INT NOT NULL DEFAULT 0,
    is_override INT NOT NULL DEFAULT 0,
    is_exported INT NOT NULL DEFAULT 0,
    is_test INT NOT NULL DEFAULT 0,
    is_deprecated INT NOT NULL DEFAULT 0,
    is_entrypoint INT NOT NULL DEFAULT 0,
    is_generated INT NOT NULL DEFAULT 0,

    -- size
    sloc INT NOT NULL DEFAULT 0,
    body_bytes INT NOT NULL DEFAULT 0,
    n_comment_lines INT NOT NULL DEFAULT 0,
    n_doc_lines INT NOT NULL DEFAULT 0,
    has_doc INT NOT NULL DEFAULT 0,

    -- complexity
    cyclomatic INT NOT NULL DEFAULT 0,
    cognitive INT NOT NULL DEFAULT 0,
    max_nesting INT NOT NULL DEFAULT 0,
    n_tokens INT NOT NULL DEFAULT 0,
    n_operators INT NOT NULL DEFAULT 0,
    n_operands INT NOT NULL DEFAULT 0,
    n_distinct_operators INT NOT NULL DEFAULT 0,
    n_distinct_operands INT NOT NULL DEFAULT 0,
    halstead_volume INT NOT NULL DEFAULT 0,
    maintainability INT NOT NULL DEFAULT 0,

    -- control flow
    n_loops INT NOT NULL DEFAULT 0,
    n_branches INT NOT NULL DEFAULT 0,
    n_returns INT NOT NULL DEFAULT 0,
    n_early_returns INT NOT NULL DEFAULT 0,
    n_switch INT NOT NULL DEFAULT 0,
    n_cases INT NOT NULL DEFAULT 0,
    n_ternary INT NOT NULL DEFAULT 0,
    n_logical INT NOT NULL DEFAULT 0,
    n_try INT NOT NULL DEFAULT 0,
    n_catch INT NOT NULL DEFAULT 0,
    n_catch_broad INT NOT NULL DEFAULT 0,
    n_catch_empty INT NOT NULL DEFAULT 0,
    n_finally INT NOT NULL DEFAULT 0,
    n_throw INT NOT NULL DEFAULT 0,
    n_labels INT NOT NULL DEFAULT 0,
    n_gotos INT NOT NULL DEFAULT 0,

    -- what sits inside a loop
    max_loop_depth INT NOT NULL DEFAULT 0,
    call_in_loop INT NOT NULL DEFAULT 0,
    alloc_in_loop INT NOT NULL DEFAULT 0,
    io_in_loop INT NOT NULL DEFAULT 0,
    await_in_loop INT NOT NULL DEFAULT 0,
    lock_in_loop INT NOT NULL DEFAULT 0,
    concat_in_loop INT NOT NULL DEFAULT 0,
    regex_in_loop INT NOT NULL DEFAULT 0,
    query_in_loop INT NOT NULL DEFAULT 0,
    branch_in_loop INT NOT NULL DEFAULT 0,

    -- data texture
    n_locals INT NOT NULL DEFAULT 0,
    n_assign INT NOT NULL DEFAULT 0,
    n_compound_assign INT NOT NULL DEFAULT 0,
    n_incdec INT NOT NULL DEFAULT 0,
    n_cmp INT NOT NULL DEFAULT 0,
    n_bitop INT NOT NULL DEFAULT 0,
    n_shift INT NOT NULL DEFAULT 0,
    n_arith INT NOT NULL DEFAULT 0,
    n_string_lit INT NOT NULL DEFAULT 0,
    n_regex_lit INT NOT NULL DEFAULT 0,
    n_float_lit INT NOT NULL DEFAULT 0,
    n_magic INT NOT NULL DEFAULT 0,
    n_null_check INT NOT NULL DEFAULT 0,
    n_subscript INT NOT NULL DEFAULT 0,
    n_member_access INT NOT NULL DEFAULT 0,
    n_lambda INT NOT NULL DEFAULT 0,
    n_closure_capture INT NOT NULL DEFAULT 0,

    -- the call graph
    n_calls INT NOT NULL DEFAULT 0,
    n_unique_calls INT NOT NULL DEFAULT 0,
    n_dynamic_calls INT NOT NULL DEFAULT 0,
    n_unresolved_calls INT NOT NULL DEFAULT 0,
    fan_in INT NOT NULL DEFAULT 0,
    fan_out INT NOT NULL DEFAULT 0,
    n_callsites INT NOT NULL DEFAULT 0,
    is_recursive INT NOT NULL DEFAULT 0,
    is_leaf INT NOT NULL DEFAULT 0,
    is_root INT NOT NULL DEFAULT 0,

    -- hazards
    n_hazards INT NOT NULL DEFAULT 0,
    risk_score INT NOT NULL DEFAULT 0
    {EXTRA_SYMBOL_COLS}
) STRICT;

CREATE TABLE params(
    symbol_id INT NOT NULL REFERENCES symbols(id),
    pos INT NOT NULL,
    name TEXT,
    type TEXT NOT NULL DEFAULT '',
    default_value TEXT,
    is_optional INT NOT NULL DEFAULT 0,
    is_variadic INT NOT NULL DEFAULT 0,
    is_ref INT NOT NULL DEFAULT 0,
    is_mutable INT NOT NULL DEFAULT 0,
    is_nullable INT NOT NULL DEFAULT 0,
    is_generic INT NOT NULL DEFAULT 0,
    is_untyped INT NOT NULL DEFAULT 0,
    type_depth INT NOT NULL DEFAULT 0,
    PRIMARY KEY(symbol_id, pos)
) WITHOUT ROWID, STRICT;

CREATE TABLE fields(
    symbol_id INT NOT NULL REFERENCES symbols(id),
    ordinal INT NOT NULL,
    name TEXT NOT NULL,
    type TEXT NOT NULL DEFAULT '',
    visibility TEXT NOT NULL DEFAULT '',
    line INT NOT NULL DEFAULT 0,
    is_static INT NOT NULL DEFAULT 0,
    is_const INT NOT NULL DEFAULT 0,
    is_mutable INT NOT NULL DEFAULT 0,
    is_nullable INT NOT NULL DEFAULT 0,
    is_collection INT NOT NULL DEFAULT 0,
    is_untyped INT NOT NULL DEFAULT 0,
    has_default INT NOT NULL DEFAULT 0,
    type_depth INT NOT NULL DEFAULT 0,
    PRIMARY KEY(symbol_id, ordinal)
) WITHOUT ROWID, STRICT;

CREATE TABLE locals(
    symbol_id INT NOT NULL REFERENCES symbols(id),
    ordinal INT NOT NULL,
    name TEXT NOT NULL,
    type TEXT NOT NULL DEFAULT '',
    line INT NOT NULL DEFAULT 0,
    is_const INT NOT NULL DEFAULT 0,
    is_mutable INT NOT NULL DEFAULT 0,
    is_untyped INT NOT NULL DEFAULT 0,
    has_init INT NOT NULL DEFAULT 0,
    in_loop INT NOT NULL DEFAULT 0,
    scope_depth INT NOT NULL DEFAULT 0,
    PRIMARY KEY(symbol_id, ordinal)
) WITHOUT ROWID, STRICT;

CREATE TABLE edges(
    caller_id INT NOT NULL REFERENCES symbols(id),
    callee_id INT NOT NULL REFERENCES symbols(id),
    n_calls INT NOT NULL DEFAULT 1,
    same_file INT NOT NULL DEFAULT 0,
    same_module INT NOT NULL DEFAULT 0,
    is_self INT NOT NULL DEFAULT 0,
    PRIMARY KEY(caller_id, callee_id)
) WITHOUT ROWID, STRICT;

CREATE TABLE callsites(
    caller_id INT NOT NULL REFERENCES symbols(id),
    callee_id INT NOT NULL REFERENCES symbols(id),
    line INT NOT NULL,
    PRIMARY KEY(caller_id, callee_id, line)
) WITHOUT ROWID, STRICT;

CREATE TABLE unresolved_calls(
    caller_id INT NOT NULL REFERENCES symbols(id),
    name TEXT NOT NULL,
    n INT NOT NULL DEFAULT 1,
    first_line INT NOT NULL DEFAULT 0,
    PRIMARY KEY(caller_id, name)
) WITHOUT ROWID, STRICT;

CREATE TABLE imports(
    id INTEGER PRIMARY KEY,
    file_id INT NOT NULL REFERENCES files(id),
    target TEXT NOT NULL,
    target_id INT REFERENCES files(id),
    alias TEXT,
    kind TEXT NOT NULL DEFAULT 'import',
    line INT NOT NULL DEFAULT 0,
    is_external INT NOT NULL DEFAULT 0,
    is_relative INT NOT NULL DEFAULT 0,
    is_wildcard INT NOT NULL DEFAULT 0,
    is_type_only INT NOT NULL DEFAULT 0,
    is_dynamic INT NOT NULL DEFAULT 0,
    n_names INT NOT NULL DEFAULT 0
) STRICT;

CREATE TABLE hazards(
    symbol_id INT NOT NULL REFERENCES symbols(id),
    pattern TEXT NOT NULL,
    category TEXT NOT NULL,
    n INT NOT NULL DEFAULT 1,
    first_line INT NOT NULL DEFAULT 0,
    PRIMARY KEY(symbol_id, pattern)
) WITHOUT ROWID, STRICT;

CREATE TABLE attributes(
    id INTEGER PRIMARY KEY,
    symbol_id INT REFERENCES symbols(id),
    file_id INT NOT NULL REFERENCES files(id),
    name TEXT NOT NULL,
    args TEXT,
    line INT NOT NULL DEFAULT 0
) STRICT;

CREATE TABLE literals(
    id INTEGER PRIMARY KEY,
    symbol_id INT REFERENCES symbols(id),
    file_id INT NOT NULL REFERENCES files(id),
    kind TEXT NOT NULL,
    value TEXT NOT NULL,
    line INT NOT NULL,
    is_magic INT NOT NULL DEFAULT 0
) STRICT;

CREATE TABLE enum_members(
    symbol_id INT NOT NULL REFERENCES symbols(id),
    ordinal INT NOT NULL,
    name TEXT NOT NULL,
    value TEXT,
    n_fields INT NOT NULL DEFAULT 0,
    PRIMARY KEY(symbol_id, ordinal)
) WITHOUT ROWID, STRICT;

CREATE TABLE markers(
    id INTEGER PRIMARY KEY,
    file_id INT NOT NULL REFERENCES files(id),
    symbol_id INT REFERENCES symbols(id),
    kind TEXT NOT NULL,
    line INT NOT NULL,
    text TEXT
) STRICT;

CREATE VIRTUAL TABLE sym_fts USING fts5(name, qual_name, signature, content='');
"""

BASE_INDEXES = r"""
-- Every query in every catalogue filters `f.is_test=0`, and without this
-- SQLite built the index at run time, per query. Measured on go/kubernetes:
-- package-state-concurrent 2.73s -> 0.037s. `files` is small, so the index
-- costs almost nothing to carry.
CREATE INDEX idx_files_test ON files(is_test);
CREATE INDEX idx_sym_name ON symbols(name);
CREATE INDEX idx_sym_qual ON symbols(qual_name);
CREATE INDEX idx_sym_file_line ON symbols(file_id, line_start);
CREATE INDEX idx_sym_module_kind ON symbols(module_id, kind);
CREATE INDEX idx_sym_parent ON symbols(parent_id) WHERE parent_id IS NOT NULL;
CREATE INDEX idx_sym_kind ON symbols(kind, name);

CREATE INDEX idx_fn_fanin ON symbols(fan_in DESC, name, file_id, cyclomatic, sloc, fan_out) WHERE kind='function';
CREATE INDEX idx_fn_cyclo ON symbols(cyclomatic DESC, name, file_id, sloc, max_nesting, cognitive) WHERE kind='function';
CREATE INDEX idx_fn_cog ON symbols(cognitive DESC, name, file_id, cyclomatic, max_nesting) WHERE kind='function';
CREATE INDEX idx_fn_risk ON symbols(risk_score DESC, name, file_id, cyclomatic) WHERE kind='function';
CREATE INDEX idx_fn_sloc ON symbols(sloc DESC, name, file_id, cyclomatic) WHERE kind='function';
CREATE INDEX idx_fn_nest ON symbols(max_nesting DESC, name, file_id, cyclomatic) WHERE kind='function';
CREATE INDEX idx_fn_rec ON symbols(cyclomatic DESC, name, file_id) WHERE is_recursive=1;
CREATE INDEX idx_fn_leaf ON symbols(fan_in DESC, name, file_id) WHERE is_leaf=1;
CREATE INDEX idx_fn_public ON symbols(fan_in DESC, name, file_id) WHERE is_public=1;
CREATE INDEX idx_fn_loopdepth ON symbols(max_loop_depth DESC, name, file_id, sloc) WHERE max_loop_depth>1;
CREATE INDEX idx_fn_callinloop ON symbols(call_in_loop DESC, name, file_id) WHERE call_in_loop>0;
CREATE INDEX idx_fn_awaitloop ON symbols(await_in_loop DESC, name, file_id) WHERE await_in_loop>0;
CREATE INDEX idx_fn_allocloop ON symbols(alloc_in_loop DESC, name, file_id) WHERE alloc_in_loop>0;
CREATE INDEX idx_fn_ioloop ON symbols(io_in_loop DESC, name, file_id) WHERE io_in_loop>0;
CREATE INDEX idx_fn_queryloop ON symbols(query_in_loop DESC, name, file_id) WHERE query_in_loop>0;
CREATE INDEX idx_fn_dyn ON symbols(n_dynamic_calls DESC, name, file_id) WHERE n_dynamic_calls>0;
CREATE INDEX idx_fn_unres ON symbols(n_unresolved_calls DESC, name, file_id) WHERE n_unresolved_calls>0;
CREATE INDEX idx_fn_catch ON symbols(n_catch_broad DESC, name, file_id) WHERE n_catch_broad>0;
CREATE INDEX idx_fn_magic ON symbols(n_magic DESC, name, file_id) WHERE n_magic>0;
CREATE INDEX idx_fn_nodoc ON symbols(cyclomatic DESC, name, file_id) WHERE has_doc=0 AND kind='function';
CREATE INDEX idx_fn_async ON symbols(name, file_id) WHERE is_async=1;
CREATE INDEX idx_fn_untested ON symbols(fan_in DESC, name) WHERE is_test=0;

CREATE INDEX idx_edge_callee ON edges(callee_id, caller_id);
CREATE INDEX idx_edge_xmod ON edges(caller_id) WHERE same_module=0;
CREATE INDEX idx_cs_callee ON callsites(callee_id, line);
CREATE INDEX idx_unres_name ON unresolved_calls(name, n DESC);

CREATE INDEX idx_haz_cat ON hazards(category, n DESC);
CREATE INDEX idx_haz_pattern ON hazards(pattern, symbol_id);

CREATE INDEX idx_imp_target ON imports(target);
CREATE INDEX idx_imp_file ON imports(file_id, target);
CREATE INDEX idx_imp_resolved ON imports(target_id) WHERE target_id IS NOT NULL;
CREATE INDEX idx_imp_external ON imports(target) WHERE is_external=1;

CREATE INDEX idx_params_sym ON params(symbol_id, pos);
CREATE INDEX idx_params_type ON params(type);
CREATE INDEX idx_params_untyped ON params(symbol_id) WHERE is_untyped=1;
CREATE INDEX idx_fields_sym ON fields(symbol_id, ordinal);
CREATE INDEX idx_fields_type ON fields(type);
CREATE INDEX idx_locals_sym ON locals(symbol_id, ordinal);
CREATE INDEX idx_lit_val ON literals(value, file_id) WHERE is_magic=1;
CREATE INDEX idx_lit_sym ON literals(symbol_id, kind);
CREATE INDEX idx_attr_sym ON attributes(symbol_id, name);
CREATE INDEX idx_attr_name ON attributes(name);
CREATE INDEX idx_mark_kind ON markers(kind, file_id);
CREATE INDEX idx_enum_sym ON enum_members(symbol_id, ordinal);

CREATE INDEX idx_files_module ON files(module_id, sloc DESC);
CREATE INDEX idx_files_lang ON files(lang, sloc DESC);
CREATE INDEX idx_files_err ON files(n_parse_errors DESC) WHERE n_parse_errors>0;
CREATE INDEX idx_files_risk ON files(total_risk DESC, path);
"""

BASE_VIEWS = r"""
CREATE VIEW v_fn AS
SELECT s.id, s.name, s.qual_name, f.path, m.name AS module, s.line_start,
    s.line_end, s.sloc, s.cyclomatic, s.cognitive, s.max_nesting,
    s.fan_in, s.fan_out, s.n_calls, s.n_unresolved_calls, s.is_recursive,
    s.is_public, s.is_async, s.is_test, s.has_doc, s.n_params,
    s.max_loop_depth, s.call_in_loop, s.n_hazards, s.risk_score,
    f.is_test AS in_test_file, f.is_generated AS in_generated_file,
    f.path || ':' || s.line_start AS at
FROM symbols s
JOIN files f ON f.id = s.file_id
LEFT JOIN modules m ON m.id = s.module_id
WHERE s.kind IN ('function','method','constructor','closure');

CREATE VIEW v_type AS
SELECT s.id, s.name, s.qual_name, s.kind, f.path, m.name AS module,
    s.line_start, s.n_lines, s.is_public, s.visibility,
    (SELECT COUNT(*) FROM fields fl WHERE fl.symbol_id=s.id) AS n_fields,
    (SELECT COUNT(*) FROM symbols c WHERE c.parent_id=s.id) AS n_members,
    f.path || ':' || s.line_start AS at
FROM symbols s
JOIN files f ON f.id = s.file_id
LEFT JOIN modules m ON m.id = s.module_id
WHERE s.kind IN ('class','struct','interface','trait','enum','union','record',
                 'protocol','type','module','impl','object','mixin');

CREATE VIEW v_hotspot AS
SELECT *, (cyclomatic*2 + cognitive + max_nesting*5 + call_in_loop*4
    + n_hazards*6 + fan_in) AS heat
FROM v_fn
WHERE in_generated_file = 0
ORDER BY heat DESC;

CREATE VIEW v_blindspot AS
SELECT name, path, module, n_calls, n_unresolved_calls, fan_out,
    CAST(100.0 * n_unresolved_calls / NULLIF(n_calls,0) AS INT) AS pct_blind, at
FROM v_fn
WHERE n_unresolved_calls > 0
ORDER BY n_unresolved_calls DESC;

CREATE VIEW v_untested AS
SELECT * FROM v_fn
WHERE in_test_file = 0 AND is_test = 0 AND in_generated_file = 0
  AND id NOT IN (
    SELECT e.callee_id FROM edges e
    JOIN symbols cs ON cs.id = e.caller_id
    JOIN files cf ON cf.id = cs.file_id
    WHERE cf.is_test = 1 OR cs.is_test = 1);
"""

MATERIALIZE_INDEXES = r"""
CREATE INDEX IF NOT EXISTS ix_mat_edge_caller ON edges(caller_id, is_self);
CREATE INDEX IF NOT EXISTS ix_mat_edge_callee ON edges(callee_id, is_self);
CREATE INDEX IF NOT EXISTS ix_mat_cs_callee ON callsites(callee_id);
CREATE INDEX IF NOT EXISTS ix_mat_unres ON unresolved_calls(caller_id);
CREATE INDEX IF NOT EXISTS ix_mat_haz ON hazards(symbol_id, category);
CREATE INDEX IF NOT EXISTS ix_mat_sym_file ON symbols(file_id, kind);
CREATE INDEX IF NOT EXISTS ix_mat_sym_mod ON symbols(module_id, is_public);
CREATE INDEX IF NOT EXISTS ix_mat_imp_file ON imports(file_id);
CREATE INDEX IF NOT EXISTS ix_mat_files_mod ON files(module_id);
CREATE INDEX IF NOT EXISTS ix_mat_sym_parent ON symbols(parent_id);
"""

MATERIALIZE_BASE = r"""
UPDATE symbols AS s SET fan_out = x.c FROM
    (SELECT caller_id AS id, COUNT(*) AS c FROM edges WHERE is_self=0
     GROUP BY caller_id) AS x WHERE x.id = s.id;

UPDATE symbols AS s SET fan_in = x.c FROM
    (SELECT callee_id AS id, COUNT(*) AS c FROM edges WHERE is_self=0
     GROUP BY callee_id) AS x WHERE x.id = s.id;

UPDATE symbols AS s SET n_callsites = x.c FROM
    (SELECT callee_id AS id, COUNT(*) AS c FROM callsites
     GROUP BY callee_id) AS x WHERE x.id = s.id;

UPDATE symbols AS s SET is_recursive = 1 FROM
    (SELECT DISTINCT caller_id AS id FROM edges WHERE is_self=1) AS x
    WHERE x.id = s.id;

UPDATE symbols AS s SET n_unresolved_calls = x.n FROM
    (SELECT caller_id AS id, SUM(n) AS n FROM unresolved_calls
     GROUP BY caller_id) AS x WHERE x.id = s.id;

UPDATE symbols AS s SET n_hazards = x.n FROM
    (SELECT symbol_id AS id, SUM(n) AS n FROM hazards
     GROUP BY symbol_id) AS x WHERE x.id = s.id;

UPDATE symbols SET is_leaf = (fan_out = 0), is_root = (fan_in = 0);

UPDATE files AS f SET
    n_symbols = x.n_symbols, n_functions = x.n_functions, n_types = x.n_types,
    total_cyclo = x.total_cyclo, max_cyclo = x.max_cyclo, total_risk = x.total_risk
FROM (
    SELECT file_id AS id, COUNT(*) AS n_symbols,
        SUM(kind IN ('function','method','constructor','closure')) AS n_functions,
        SUM(kind IN ('class','struct','interface','trait','enum','union',
                     'record','protocol','type','impl')) AS n_types,
        COALESCE(SUM(cyclomatic),0) AS total_cyclo,
        COALESCE(MAX(cyclomatic),0) AS max_cyclo,
        COALESCE(SUM(risk_score),0) AS total_risk
    FROM symbols GROUP BY file_id) AS x
WHERE x.id = f.id;

UPDATE files AS f SET n_imports = x.c FROM
    (SELECT file_id AS id, COUNT(*) AS c FROM imports GROUP BY file_id) AS x
    WHERE x.id = f.id;

UPDATE modules AS m SET n_symbols = x.n, n_public = x.p FROM
    (SELECT module_id AS id, COUNT(*) AS n, SUM(is_public) AS p
     FROM symbols WHERE module_id IS NOT NULL GROUP BY module_id) AS x
    WHERE x.id = m.id;

UPDATE modules AS m SET n_files = x.c, sloc = x.s FROM
    (SELECT module_id AS id, COUNT(*) AS c, COALESCE(SUM(sloc),0) AS s
     FROM files WHERE module_id IS NOT NULL GROUP BY module_id) AS x
    WHERE x.id = m.id;

UPDATE modules AS m SET fan_out = x.c FROM
    (SELECT s1.module_id AS id, COUNT(DISTINCT s2.module_id) AS c
     FROM edges e JOIN symbols s1 ON s1.id=e.caller_id
     JOIN symbols s2 ON s2.id=e.callee_id
     WHERE s1.module_id <> s2.module_id GROUP BY s1.module_id) AS x
    WHERE x.id = m.id;

UPDATE modules AS m SET fan_in = x.c FROM
    (SELECT s2.module_id AS id, COUNT(DISTINCT s1.module_id) AS c
     FROM edges e JOIN symbols s1 ON s1.id=e.caller_id
     JOIN symbols s2 ON s2.id=e.callee_id
     WHERE s1.module_id <> s2.module_id GROUP BY s2.module_id) AS x
    WHERE x.id = m.id;

UPDATE modules SET instability =
    CASE WHEN (fan_in + fan_out) = 0 THEN 0.0
         ELSE CAST(fan_out AS REAL) / (fan_in + fan_out) END;
"""

class Analyzer:
    """What one language must supply.

    Subclass, fill in the class attributes, implement `parse_file`, and the
    driver below does discovery, schema, aggregation, indexing and the CLI.
    """

    #: short name, e.g. "rust"
    LANG = "?"
    #: what version of the language this was written against, shown in --version
    TARGET = ""
    #: file extensions to parse
    EXTS: tuple[str, ...] = ()
    #: extra directories to skip on top of COMMON_SKIP_DIRS
    SKIP_DIRS: set[str] = set()
    #: files larger than this are counted but not parsed. A 30 MB generated
    #: blob will otherwise dominate the run and teach nobody anything.
    MAX_FILE_BYTES = 4 * 1024 * 1024
    #: A file under the byte cap can still cost gigabytes: 3.99 MB on one
    #: line took 3.36 GB of RSS, because the cap bounds what is read and not
    #: what parsing it allocates. Minified bundles and generated tables are
    #: exactly this shape.
    MAX_LINE_BYTES = 1024 * 1024
    #: what this analyzer needs, and how to install it
    DEPS: DepSet = None            # type: ignore[assignment]
    #: hazard categories -> generates an `n_<cat>` column on symbols
    HAZARD_CATEGORIES: tuple[str, ...] = ()
    #: (column_name, sql_type_and_default) added to symbols
    EXTRA_SYMBOL_COLS: tuple[tuple[str, str], ...] = ()
    #: additional CREATE TABLE statements
    SCHEMA_EXT = ""
    #: additional CREATE INDEX statements, applied after the bulk load
    INDEX_EXT = ""
    #: additional CREATE VIEW statements
    VIEW_EXT = ""
    #: extra UPDATE statements run after the base aggregate pass
    MATERIALIZE_EXT = ""
    #: the risk formula, an SQL expression over `symbols`
    RISK_SQL = "cyclomatic*2 + cognitive + max_nesting*5 + n_hazards*6"
    #: the query catalogue: (name, title, notes, sql)
    QUERIES: list[tuple[str, str, str, str]] = []
    #: triage/metrics queries, kept separate so a bug-fixing agent can
    #: run only QUERIES. Reach them with --metrics.
    METRICS: list[tuple[str, str, str, str]] = []
    #: manifest files worth parsing for module/dependency facts
    MANIFESTS: tuple[str, ...] = ()

    def __init__(self) -> None:
        self.parser: ParserHandle = ParserHandle(mode=MODE_REGEX,
                                                 note="not initialised")
        self.file_id: dict[str, int] = {}
        #: symbol rows, written in one executemany after parsing
        self._sym_rows: list[tuple] = []
        self._n_sym = 0
        self._sym_spec: Optional[list[tuple[str, Any]]] = None
        self._sym_sql = ""

    # -- lifecycle ---------------------------------------------------------
    def setup(self) -> ParserHandle:
        """Build the parser. Called once, before any file is read."""
        raise NotImplementedError

    def parse_file(self, rec: FileRec, db: sqlite3.Connection,
                   bufs: Buffers) -> None:
        """Extract every symbol in one file. Called once per file."""
        raise NotImplementedError

    def resolve_calls(self, db: sqlite3.Connection, bufs: Buffers) -> None:
        """Second pass: turn recorded call names into edges.

        Split from `parse_file` because a call can only be resolved once every
        file has been seen -- forward references are the normal case, not the
        exception.
        """
        raise NotImplementedError

    def parse_manifests(self, root: str, db: sqlite3.Connection) -> None:
        """Optional: read go.mod / Cargo.toml / package.json and friends."""

    def post_build(self, db: sqlite3.Connection) -> None:
        """Optional: anything that needs the finished graph."""

    # -- schema assembly ---------------------------------------------------
    def symbol_columns(self) -> list[tuple[str, str]]:
        cols = [("n_%s" % c, "INT NOT NULL DEFAULT 0")
                for c in self.HAZARD_CATEGORIES]
        cols += list(self.EXTRA_SYMBOL_COLS)
        seen: set[str] = set()
        out: list[tuple[str, str]] = []
        for name, decl in cols:
            if name in seen:
                continue
            seen.add(name)
            out.append((name, decl))
        return out

    def schema_sql(self) -> str:
        extra = self.symbol_columns()
        block = ""
        if extra:
            block = ",\n    " + ",\n    ".join(
                "%s %s" % (n, d) for n, d in extra)
        return (BASE_SCHEMA.replace("{EXTRA_SYMBOL_COLS}", block)
                + "\n" + self.SCHEMA_EXT)

    def materialize_sql(self) -> str:
        parts = [MATERIALIZE_BASE]
        for cat in self.HAZARD_CATEGORIES:
            parts.append(
                "UPDATE symbols AS s SET n_%s = x.n FROM "
                "(SELECT symbol_id AS id, SUM(n) AS n FROM hazards "
                "WHERE category='%s' GROUP BY symbol_id) AS x "
                "WHERE x.id = s.id;" % (cat, cat))
        parts.append(self.MATERIALIZE_EXT)
        parts.append("UPDATE symbols SET risk_score = %s;" % self.RISK_SQL)
        parts.append(
            "UPDATE symbols SET halstead_volume = CAST("
            "(n_operators + n_operands) * "
            "(CASE WHEN (n_distinct_operators + n_distinct_operands) > 1 "
            "THEN 1.0 * (n_distinct_operators + n_distinct_operands) "
            "ELSE 2.0 END) AS INT) WHERE n_tokens > 0;")
        parts.append(
            "UPDATE symbols SET maintainability = MAX(0, CAST("
            "171 - 0.23 * cyclomatic - 16.2 * "
            "(CASE WHEN sloc > 1 THEN 1.0 * sloc / 20.0 ELSE 0.05 END) "
            "AS INT)) WHERE kind IN "
            "('function','method','constructor','closure');")
        return "\n".join(p for p in parts if p.strip())

def _gil_enabled() -> bool:
    """False on a free-threaded (PEP 703) build.

    Worth recording per run: the same source on a free-threaded interpreter has
    genuinely concurrent access to any shared state, so a concurrency finding
    that was theoretical under the GIL is reachable there.
    """
    probe = getattr(sys, "_is_gil_enabled", None)
    return probe() if probe is not None else True

def _concurrency_note(mode: str) -> str:
    """Why this run is single-threaded -- true for THIS analyzer, not in general.

    The tree-sitter measurement does not apply to the analyzers that never load
    it, and asserting it there was a claim about code that is not running.
    """
    if mode == MODE_TREE_SITTER:
        return ("serial: tree-sitter holds the GIL for the whole of parse() "
                "(4 threads measured at 3.8x wall time for 4x work) and its "
                "_binding extension refuses to load in a subinterpreter, so "
                "neither threads nor PEP 734 help. Process-level parallelism "
                "would need symbol ids assigned outside SQLite.")
    return ("serial: this analyzer parses in-process with no third-party "
            "extension. Parallelism would need symbol ids assigned outside "
            "SQLite, which is where they come from today.")

def discover(analyzer: Analyzer, root: str, db: sqlite3.Connection,
             include_tests: bool, include_generated: bool,
             include_vendored: bool, quiet: bool) -> list[FileRec]:
    """Walk the tree, insert every file row, return the parseable ones."""
    skip = COMMON_SKIP_DIRS | set(analyzer.SKIP_DIRS)
    exts = set(analyzer.EXTS)
    mod_id: dict[str, int] = {}
    out: list[FileRec] = []
    n_seen = n_skipped_big = 0

    def module(rel: str) -> int:
        name = module_of(rel)
        mid = mod_id.get(name)
        if mid is None:
            kind = ("test" if TEST_PATH_RE.search(name) else
                    "vendor" if VENDOR_PATH_RE.search(name) else
                    "example" if re.search(r'(^|/)(examples?|samples?|demos?)(/|$)', name, re.I) else
                    "tool" if re.search(r'(^|/)(tools?|scripts?|cmd|bin)(/|$)', name, re.I) else
                    "source")
            mid = db.execute(
                "INSERT INTO modules(name,kind) VALUES(?,?)",
                (name, kind)).lastrowid
            mod_id[name] = mid
        return mid

    real_root = os.path.realpath(root)
    n_skipped_special = 0
    n_skipped_escape = 0
    n_skipped_denied = 0
    n_walk_errors = 0
    n_files = 0
    file_rows: list[tuple] = []

    def _walk_error(exc: OSError) -> None:
        nonlocal n_walk_errors
        n_walk_errors += 1

    for dirpath, dirnames, filenames in os.walk(root, onerror=_walk_error):
        dirnames[:] = [d for d in sorted(dirnames)
                       if d not in skip and not d.startswith(".")]
        for fn in sorted(filenames):
            ext = os.path.splitext(fn)[1]
            if ext not in exts:
                continue
            n_seen += 1
            full = os.path.join(dirpath, fn)
            rel = os.path.relpath(full, root)
            too_big = False
            try:
                st = os.stat(full)
                # A FIFO reports st_size 0, passes the size cap, and then
                # open() blocks forever waiting for a writer. A symlink to
                # /dev/zero reports 0 and reads until the machine dies. Both
                # are storable in a tarball; the symlink is storable in git.
                if not stat.S_ISREG(st.st_mode):
                    n_skipped_special += 1
                    continue
                # A symlink named passwd.c pointing at /etc/passwd was read,
                # hashed, parsed, and any TODO-ish line echoed to stdout. This
                # tool is pointed at code the user did not write and its output
                # gets pasted into reports.
                if os.path.realpath(full) != full and not \
                        os.path.realpath(full).startswith(real_root + os.sep):
                    n_skipped_escape += 1
                    continue
                if st.st_size > analyzer.MAX_FILE_BYTES:
                    n_skipped_big += 1
                    data = b""
                    text = ""
                    too_big = True
                else:
                    with open(full, "rb") as fh:
                        data = fh.read()
                    text = data.decode("utf-8", "replace")
            except PermissionError:
                n_skipped_denied += 1
                continue
            except OSError:
                continue

            # A single 3.99 MB line took 3.36 GB of RSS: the byte cap bounds
            # what is read, not what parsing it costs.
            if not too_big and data:
                longest = max((len(l) for l in data.split(b"\n")), default=0)
                if longest > analyzer.MAX_LINE_BYTES:
                    n_skipped_big += 1
                    too_big = True

            lines = text.splitlines()
            blank = sum(1 for l in lines if not l.strip())
            cmt = sum(1 for l in lines
                      if l.lstrip()[:3] in ("//", "#", "/*", "*", "*/", '"""',
                                            "'''", "--", ";;", "%") and l.strip())
            name_re = TEST_NAME_RE_BY_LANG.get(analyzer.LANG,
                                              TEST_NAME_RE)
            test = bool(TEST_PATH_RE.search(rel) or name_re.search(fn))
            gen = is_generated(fn, text[:2000])
            vend = bool(VENDOR_PATH_RE.search(rel))
            mid = module(rel)
            parse = (not too_big and bool(text)
                     and (include_tests or not test)
                     and (include_generated or not gen)
                     and (include_vendored or not vend))

            # A non-UTF-8 filename arrives surrogate-escaped and sqlite3
            # rejects surrogates, which used to kill the whole scan from
            # outside the try above.
            if _has_surrogates(rel):
                rel = rel.encode("utf-8", "replace").decode("utf-8", "replace")
                fn = fn.encode("utf-8", "replace").decode("utf-8", "replace")
            # The id is assigned here rather than read back from
            # `lastrowid`: a counter from 1 produces exactly the rowids SQLite
            # would have handed out, and it lets every file row go in as one
            # `executemany` after the walk instead of one INSERT per file --
            # 31,157 statements on elasticsearch.
            n_files += 1
            fid = n_files
            file_rows.append(
                (fid, rel, os.path.dirname(rel) or ".", fn, ext, analyzer.LANG,
                 mid, st.st_size, len(lines),
                 sum(1 for l in lines if l.strip()),
                 blank, cmt, max((len(l) for l in lines), default=0),
                 hashlib.sha1(data).hexdigest() if data else "",
                 int(parse), int(test), int(gen), int(vend)))
            analyzer.file_id[rel] = fid
            if parse:
                out.append(FileRec(fid, mid, rel, full, text, data,
                                   analyzer.LANG, test, gen, vend))

    if file_rows:
        db.executemany(
            "INSERT INTO files(id,path,dir,basename,ext,lang,module_id,bytes,"
            "lines,sloc,blank_lines,comment_lines,max_line_len,sha1,parsed,"
            "is_test,is_generated,is_vendored) "
            "VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)", file_rows)
        file_rows.clear()

    for n, why in ((n_skipped_big,
                    "too large or with a pathologically long line -- "
                    "catalogued, not parsed"),
                   (n_skipped_special,
                    "not regular files (fifo, socket, device) -- skipped"),
                   (n_skipped_escape,
                    "symlinks pointing OUTSIDE the tree -- skipped"),
                   (n_skipped_denied, "unreadable (permission denied)"),
                   (n_walk_errors, "director(ies) could not be listed")):
        if n and not quiet:
            print("  %d %s" % (n, why))
    db.execute("INSERT OR REPLACE INTO meta(key,value) VALUES(?,?)",
               ("files_skipped",
                "big=%d special=%d escaping_symlink=%d denied=%d walk_errors=%d"
                % (n_skipped_big, n_skipped_special, n_skipped_escape,
                   n_skipped_denied, n_walk_errors)))
    return out

def _has_surrogates(text: str) -> bool:
    return any("\ud800" <= ch <= "\udfff" for ch in text)

def scan_markers(rec: FileRec, bufs: Buffers) -> None:
    """TODO/FIXME/HACK and friends, with their line and text."""
    for i, line in enumerate(rec.text.splitlines(), 1):
        m = MARKER_RE.search(line)
        if m and ("//" in line or "#" in line or "*" in line or "--" in line):
            bufs.markers.append(
                (rec.fid, None, m.group(1).upper(), i, line.strip()[:200]))

#: Files between incremental flushes of the per-file row buffers. The
#: accumulators used to hold every row until the end of the parse: on
#: elasticsearch that is 444k params, 508k imports and 498k more besides,
#: all live at the moment peak RSS is set. Draining them periodically
#: costs nothing -- the inserts happen either way -- and they are pure
#: appends keyed by an already-assigned symbol_id, so batching does not
#: change a single row or id.
FLUSH_EVERY = 2000

#: Symbol rows held before writing. Large enough that the write is a
#: real batch, small enough that the buffer never shows up in peak RSS.
SYMBOL_BATCH = 4000

def flush_rows(db: sqlite3.Connection, bufs: Buffers) -> None:
    """Write and CLEAR the per-file tables. Safe to call mid-parse.

    Only tables keyed by a symbol_id that already exists. Edges,
    callsites and unresolved calls are NOT here: they are not known
    until `resolve_calls` has seen every file.
    """
    ex = db.executemany
    if bufs.params:
        ex("INSERT OR IGNORE INTO params(symbol_id,pos,name,type,default_value,"
           "is_optional,is_variadic,is_ref,is_mutable,is_nullable,is_generic,"
           "is_untyped,type_depth) VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?)", bufs.params)
    if bufs.fields:
        ex("INSERT OR IGNORE INTO fields(symbol_id,ordinal,name,type,visibility,"
           "line,is_static,is_const,is_mutable,is_nullable,is_collection,"
           "is_untyped,has_default,type_depth) "
           "VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?,?)", bufs.fields)
    if bufs.locals:
        ex("INSERT OR IGNORE INTO locals(symbol_id,ordinal,name,type,line,"
           "is_const,is_mutable,is_untyped,has_init,in_loop,scope_depth) "
           "VALUES(?,?,?,?,?,?,?,?,?,?,?)", bufs.locals)
    if bufs.literals:
        ex("INSERT INTO literals(symbol_id,file_id,kind,value,line,is_magic) "
           "VALUES(?,?,?,?,?,?)", bufs.literals)
    if bufs.markers:
        ex("INSERT INTO markers(file_id,symbol_id,kind,line,text) "
           "VALUES(?,?,?,?,?)", bufs.markers)
    if bufs.attributes:
        ex("INSERT INTO attributes(symbol_id,file_id,name,args,line) "
           "VALUES(?,?,?,?,?)", bufs.attributes)
    if bufs.imports:
        ex("INSERT INTO imports(file_id,target,target_id,alias,kind,line,"
           "is_external,is_relative,is_wildcard,is_type_only,is_dynamic,n_names) "
           "VALUES(?,?,?,?,?,?,?,?,?,?,?,?)", bufs.imports)
    if bufs.hazards:
        ex("INSERT INTO hazards(symbol_id,pattern,category,n,first_line) "
           "VALUES(?,?,?,?,?) ON CONFLICT(symbol_id,pattern) DO UPDATE "
           "SET n = n + excluded.n", bufs.hazards)
    if bufs.enum_members:
        ex("INSERT OR IGNORE INTO enum_members(symbol_id,ordinal,name,value,"
           "n_fields) VALUES(?,?,?,?,?)", bufs.enum_members)
    bufs.params.clear()
    bufs.fields.clear()
    bufs.locals.clear()
    bufs.literals.clear()
    bufs.markers.clear()
    bufs.attributes.clear()
    bufs.imports.clear()
    bufs.hazards.clear()
    bufs.enum_members.clear()

def flush(db: sqlite3.Connection, bufs: Buffers) -> None:
    """Final flush: the per-file tables, then everything resolve_calls produced."""
    flush_rows(db, bufs)
    ex = db.executemany
    if bufs.edges:
        ex("INSERT OR IGNORE INTO edges(caller_id,callee_id,n_calls,same_file,"
           "same_module,is_self) VALUES(?,?,?,?,?,?)",
           # A generator, not a list comprehension: `executemany` takes any
           # iterable, and materialising one costs a fresh tuple per edge --
           # 770k of them on elasticsearch, held alongside the dict they were
           # built from, at exactly the moment peak RSS is set. Measured
           # +530,005 live blocks vs +5, and streaming is no slower.
           ((a, b, v[0], v[1], v[2], v[3]) for (a, b), v in bufs.edges.items()))
    if bufs.callsites:
        ex("INSERT OR IGNORE INTO callsites(caller_id,callee_id,line) "
           "VALUES(?,?,?)", bufs.callsites)
    if bufs.unresolved:
        ex("INSERT OR IGNORE INTO unresolved_calls(caller_id,name,n,first_line) "
           "VALUES(?,?,?,?)",
           ((c, n, v[0], v[1]) for (c, n), v in bufs.unresolved.items()))

_IMPORT_SUFFIXES = ("", ".py", ".pyi", ".ts", ".tsx", ".d.ts", ".mts", ".cts",
                    ".js", ".jsx", ".mjs", ".cjs", ".rb", ".php", ".go",
                    ".rs", ".java")

_IMPORT_INDEXES = ("__init__.py", "index.ts", "index.tsx", "index.js",
                   "index.mjs", "mod.rs", "lib.rs")

def resolve_import_targets(db: sqlite3.Connection, analyzer: "Analyzer") -> int:
    """Point each import row at the file it names, where that file is here.

    Left NULL, `imports.target_id` silently turns every query built on it into
    a tautology: `import-cycles` finds none because the join never matches,
    a barrel's `importers` count is always zero, and "nothing imports this
    export" is true of everything. Those queries did not fail -- they returned
    confident, empty, wrong answers.

    Relative specifiers are resolved against the importing file's directory;
    everything else is tried as a dotted or slashed path from the tree root.
    A bare package name resolves to nothing, which is correct: it is external.
    """
    by_path: dict[str, int] = {}
    for fid, path in db.execute("SELECT id, path FROM files"):
        norm = path.replace(os.sep, "/")
        by_path[norm] = fid
        stem = norm.rsplit(".", 1)[0]
        by_path.setdefault(stem, fid)

    def look(cand: str) -> Optional[int]:
        cand = cand.strip("/")
        if not cand:
            return None
        for suf in _IMPORT_SUFFIXES:
            hit = by_path.get(cand + suf)
            if hit is not None:
                return hit
        for idx in _IMPORT_INDEXES:
            hit = by_path.get("%s/%s" % (cand, idx))
            if hit is not None:
                return hit
        return None

    rows: list[tuple[int, int]] = []
    for iid, fid, target, path in db.execute(
            "SELECT i.id, i.file_id, i.target, f.path FROM imports i "
            "JOIN files f ON f.id=i.file_id WHERE i.target_id IS NULL"):
        if not target:
            continue
        t = target.replace(os.sep, "/").strip()
        here = os.path.dirname(path.replace(os.sep, "/"))
        hit = None
        if t.startswith("."):
            # Python's `..pkg.mod` and JS's `../pkg/mod` both count leading
            # dots, but Python counts one extra: `.` is this package.
            n_up = len(t) - len(t.lstrip("."))
            rest = t[n_up:].replace(".", "/") if "/" not in t else t.lstrip("./")
            base = here
            for _ in range(max(0, n_up - 1)):
                base = os.path.dirname(base)
            hit = look("%s/%s" % (base, rest) if base else rest)
        else:
            hit = look(t.replace(".", "/")) or look("%s/%s" % (here, t))
        if hit is not None and hit != fid:
            rows.append((hit, iid))
    if rows:
        db.executemany("UPDATE imports SET target_id=? WHERE id=?", rows)
    db.execute("INSERT OR REPLACE INTO meta(key,value) VALUES(?,?)",
               ("imports_resolved",
                "%d of %d import rows point at a file in this tree"
                % (len(rows),
                   db.execute("SELECT COUNT(*) FROM imports").fetchone()[0])))
    return len(rows)

def build(analyzer: Analyzer, root: str, db: sqlite3.Connection, *,
          include_tests: bool = True, include_generated: bool = False,
          include_vendored: bool = False, quiet: bool = False) -> int:
    """Parse `root` into the open connection `db`. Returns files parsed."""
    db.executescript(PRAGMAS)
    db.executescript(analyzer.schema_sql())

    handle = analyzer.setup()
    analyzer.parser = handle
    if not quiet:
        print("  " + handle.banner())

    t0 = time.time()
    recs = discover(analyzer, root, db, include_tests, include_generated,
                    include_vendored, quiet)
    t_discover = time.time() - t0
    if not quiet:
        print("  %d %s files discovered in %.1fs"
              % (len(recs), analyzer.LANG, t_discover))

    bufs = Buffers()
    t1 = time.time()
    n_err = 0
    parse_failed: list[tuple[int]] = []
    step = max(1, len(recs) // 20)
    for i, rec in enumerate(recs):
        try:
            scan_markers(rec, bufs)
            analyzer.parse_file(rec, db, bufs)
        except RecursionError:
            n_err += 1
            parse_failed.append((rec.fid,))
        except Exception as exc:
            # One pathological file must not cost the other 40,000. The failure
            # is recorded on the file row so `--report` can show it rather than
            # the run quietly covering less than it claims.
            n_err += 1
            parse_failed.append((rec.fid,))
            if os.environ.get("CODEGRAPH_DEBUG"):
                import traceback
                print("  parse failed: %s: %s" % (rec.rel, exc), file=sys.stderr)
                traceback.print_exc()
        # The source is never read again: from here `recs` is used only for
        # len(). Holding text AND data for every file to the end of the run
        # was 594 MB of elasticsearch's 3.9 GB peak. Outside the try above on
        # purpose -- a failure here must not be swallowed as a parse error.
        rec.text = ""
        rec.data = b""
        if (i + 1) % FLUSH_EVERY == 0:
            flush_rows(db, bufs)
        if not quiet and (i + 1) % step == 0:
            print("  ... %d/%d files" % (i + 1, len(recs)))
    if parse_failed:
        db.executemany("UPDATE files SET parsed=0, "
                       "n_parse_errors=n_parse_errors+1 WHERE id=?",
                       parse_failed)
        parse_failed.clear()
    # Symbols reach the database HERE -- before anything counts or queries the
    # table. Flushing after the count made `n_syms` read 0 and printed
    # "3554 file(s) produced NO symbols" over a perfectly good graph.
    analyzer.flush_symbols(db)
    n_syms = db.execute("SELECT COUNT(*) FROM symbols").fetchone()[0]
    # A parse failure is a correctness signal, not progress noise: a bug in one
    # analyzer once dropped 620 of Django's 2,103 files and 30% of its symbols,
    # and --quiet hid the only line that said so. Failures above a handful are
    # always reported, and the exit path records them for a query to find.
    if n_err and (n_err > len(recs) // 100 or not quiet):
        print("  WARNING: %d of %d file(s) FAILED to parse and contributed"
              " nothing." % (n_err, len(recs)), file=sys.stderr)
        print("           Re-run with CODEGRAPH_DEBUG=1 for the tracebacks.",
              file=sys.stderr)
    if not quiet:
        print("  %d symbols parsed in %.1fs%s"
              % (n_syms, time.time() - t1,
                 " (%d file(s) failed)" % n_err if n_err else ""))
    if recs and n_syms == 0:
        # Not fatal -- a repo really can hold only declarations -- but it is
        # never what the user expected, and silence here reads as success.
        print("  WARNING: %d file(s) were read and produced NO symbols. Every"
              % len(recs))
        print("           query below will be empty for that reason, not"
              " because the")
        print("           code is clean. Check --report for parse errors.")

    t2 = time.time()
    analyzer.resolve_calls(db, bufs)
    flush(db, bufs)
    if not quiet:
        print("  call graph built in %.1fs" % (time.time() - t2))

    resolve_import_targets(db, analyzer)
    try:
        analyzer.parse_manifests(root, db)
    except Exception as exc:
        # Manifests are supplementary. A malformed one must never discard a
        # parse that already succeeded -- a non-object tsconfig in vscode once
        # threw away 3.6 minutes of work at the last step.
        db.execute("INSERT OR REPLACE INTO meta(key,value) VALUES(?,?)",
                   ("manifest_error", "%s: %s" % (type(exc).__name__, exc)))
        if not quiet:
            print("  manifest parsing failed (%s); continuing" % exc,
                  file=sys.stderr)

    t3 = time.time()
    db.executescript(MATERIALIZE_INDEXES)
    db.executescript(analyzer.materialize_sql())
    if not quiet:
        print("  aggregates materialized in %.1fs" % (time.time() - t3))

    db.execute("INSERT INTO sym_fts(rowid,name,qual_name,signature) "
               "SELECT id,name,qual_name,COALESCE(signature,'') FROM symbols")

    t4 = time.time()
    db.executescript(BASE_INDEXES)
    if analyzer.INDEX_EXT:
        db.executescript(analyzer.INDEX_EXT)
    db.executescript(BASE_VIEWS)
    if analyzer.VIEW_EXT:
        db.executescript(analyzer.VIEW_EXT)
    if not quiet:
        print("  indexed in %.1fs" % (time.time() - t4))

    analyzer.post_build(db)

    meta_rows = (
        ("schema_version", str(SCHEMA_VERSION)),
        ("lang", analyzer.LANG),
        ("target", analyzer.TARGET),
        ("root", os.path.abspath(root)),
        ("parse_mode", handle.mode),
        ("parser", handle.banner()),
        ("built_at", time.strftime("%Y-%m-%dT%H:%M:%S")),
        ("files_parsed", str(len(recs))),
        ("files_failed", str(n_err)),
        ("python", sys.version.split()[0]),
        ("sqlite", sqlite3.sqlite_version),
        ("free_threading",
         "yes -- GIL disabled" if not _gil_enabled() else "no -- GIL enabled"),
        ("parse_concurrency", _concurrency_note(handle.mode)),
    )
    db.executemany("INSERT OR REPLACE INTO meta(key,value) VALUES(?,?)", meta_rows)

    db.commit()
    db.execute("ANALYZE")
    return len(recs)

MAX_CELL = 72

def _cell(v: Any) -> str:
    if v is None:
        return "-"
    if isinstance(v, float):
        t = "%.2f" % v
    else:
        t = str(v)
    return t if len(t) <= MAX_CELL else t[:MAX_CELL - 3] + "..."

def render(rows: Sequence[Sequence[Any]], cols: Sequence[str],
           out: Any = sys.stdout) -> None:
    if not rows:
        print(" (no rows)", file=out)
        return
    body = [[_cell(v) for v in r] for r in rows]
    w = [max(len(str(cols[i])), max(len(r[i]) for r in body))
         for i in range(len(cols))]
    print(" " + " ".join(str(cols[i]).ljust(w[i]) for i in range(len(cols))), file=out)
    print(" " + " ".join("-" * w[i] for i in range(len(cols))), file=out)
    for r in body:
        print(" " + " ".join(r[i].ljust(w[i]) for i in range(len(r))), file=out)

def report(db: sqlite3.Connection, analyzer: Analyzer) -> None:
    """A short narrative: how much we saw, and how much we missed."""
    q = lambda s, *a: db.execute(s, a).fetchall()
    one = lambda s, *a: (db.execute(s, a).fetchone() or [0])[0]

    print("\n" + "=" * 78)
    print("OVERVIEW")
    print("-" * 78)
    meta = dict(q("SELECT key,value FROM meta"))
    for k in ("lang", "target", "parser", "root", "built_at"):
        if meta.get(k):
            print(" %-14s %s" % (k, meta[k]))

    files = one("SELECT COUNT(*) FROM files")
    parsed = one("SELECT COUNT(*) FROM files WHERE parsed=1")
    sloc = one("SELECT COALESCE(SUM(sloc),0) FROM files WHERE parsed=1")
    print(" %-14s %d catalogued, %d parsed, %d sloc" % ("files", files, parsed, sloc))
    print(" %-14s %s" % ("symbols", ", ".join(
        "%s=%d" % (k, v) for k, v in
        q("SELECT kind,COUNT(*) FROM symbols GROUP BY kind "
          "ORDER BY COUNT(*) DESC LIMIT 12"))))
    print(" %-14s %d edges, %d call sites, %d unresolved"
          % ("call graph", one("SELECT COUNT(*) FROM edges"),
             one("SELECT COUNT(*) FROM callsites"),
             one("SELECT COALESCE(SUM(n),0) FROM unresolved_calls")))

    print("\n" + "=" * 78)
    print("HOW MUCH OF THIS TO TRUST")
    print("-" * 78)
    err_files = one("SELECT COUNT(*) FROM files WHERE n_parse_errors>0")
    tot_calls = one("SELECT COALESCE(SUM(n_calls),0) FROM symbols")
    unres = one("SELECT COALESCE(SUM(n),0) FROM unresolved_calls")
    if parsed == 0:
        print(" NOTHING WAS PARSED. Every number below is zero because no file")
        print(" was read, not because this repository is empty or clean.")
    elif meta.get("parse_mode") == MODE_REGEX:
        print(" Parsed WITHOUT a grammar: spans and nesting are approximate and")
        print(" call edges are absent. Only the file inventory is reliable.")
    print(" %-30s %d file(s)" % ("files with parse errors", err_files))
    if tot_calls:
        print(" %-30s %d of %d call sites (%d%%)"
              % ("calls we could NOT resolve", unres, tot_calls,
                 100 * unres // tot_calls))
    else:
        print(" %-30s no calls were recorded at all -- this is the absence of"
              % "call resolution")
        print(" %-30s data, not a clean result" % "")
    print(" A high unresolved share means the call-graph queries below see less")
    print(" than they imply. `v_blindspot` lists exactly where.")

    for label, sql in (
        ("BIGGEST MODULES",
         "SELECT name, n_files AS files, sloc, n_symbols AS syms, "
         "ROUND(instability,2) AS instab FROM modules "
         "WHERE n_files>0 ORDER BY sloc DESC LIMIT 12"),
        ("HEAVIEST FUNCTIONS",
         "SELECT name, sloc, cyclomatic AS cyclo, cognitive AS cog, "
         "max_nesting AS nest, fan_in, at FROM v_fn "
         "ORDER BY cyclomatic DESC LIMIT 12"),
        ("MOST DEPENDED ON",
         "SELECT name, fan_in, fan_out, cyclomatic AS cyclo, sloc, at "
         "FROM v_fn ORDER BY fan_in DESC LIMIT 12"),
        ("MARKERS LEFT IN THE CODE",
         "SELECT kind, COUNT(*) AS n FROM markers GROUP BY kind ORDER BY n DESC"),
    ):
        print("\n" + "=" * 78)
        print(label)
        print("-" * 78)
        cur = db.execute(sql)
        render(cur.fetchall(), [d[0] for d in cur.description])

def main(analyzer: Analyzer, argv: Optional[list[str]] = None) -> int:
    ap = argparse.ArgumentParser(
        prog="codegraph_%s.py" % analyzer.LANG,
        description="Parse a %s tree into an in-memory graph and query it in "
                    "one shot. Target: %s" % (analyzer.LANG, analyzer.TARGET),
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="every run re-parses from source; nothing is cached, so an "
               "answer can never describe code that has moved on")
    ap.add_argument("root", nargs="?", default=".", help="tree to parse")
    ap.add_argument("which", nargs="*", type=int, help="1-based query numbers")
    ap.add_argument("--module", default="%", help="module-name LIKE filter")
    ap.add_argument("--limit", type=int, default=-1,
                    help="rows per query; -1 (default) is every row")
    ap.add_argument("--list", action="store_true", help="list the queries")
    ap.add_argument("--metrics", action="store_true",
                    help="run/list the METRICS section instead of QUERIES")
    ap.add_argument("--schema", action="store_true", help="dump the schema")
    ap.add_argument("--report", action="store_true", help="narrative overview")
    ap.add_argument("--sql", help="ad-hoc query against the graph")
    ap.add_argument("--csv", type=int, metavar="N", help="emit query N as CSV")
    ap.add_argument("--json", type=int, metavar="N", help="emit query N as JSON")
    ap.add_argument("--save", metavar="PATH", help="also write the graph to a file")
    ap.add_argument("--force", action="store_true",
                    help="allow --save to overwrite an existing file")
    ap.add_argument("--deps", action="store_true",
                    help="show dependencies and how to install them")
    ap.add_argument("--install-deps", action="store_true",
                    help="pip-install the missing dependencies, then continue")
    ap.add_argument("--include-generated", action="store_true",
                    help="parse generated files too (off by default)")
    ap.add_argument("--include-vendored", action="store_true",
                    help="parse vendored trees too (off by default)")
    ap.add_argument("--no-tests", action="store_true",
                    help="skip test files")
    ap.add_argument("--quiet", action="store_true")
    ap.add_argument("--version", action="store_true")
    a = ap.parse_args(argv)

    if a.version:
        print("codegraph_%s.py  target=%s  schema=v%d  python=%s  sqlite=%s"
              % (analyzer.LANG, analyzer.TARGET, SCHEMA_VERSION,
                 sys.version.split()[0], sqlite3.sqlite_version))
        return 0
    if a.install_deps:
        analyzer.DEPS.install(quiet=a.quiet)
        if a.deps:
            print()
            print(analyzer.DEPS.describe())
            return 0
    elif a.deps:
        print(analyzer.DEPS.describe())
        return 0
    if a.schema:
        print(analyzer.schema_sql())
        print(BASE_INDEXES)
        print(analyzer.INDEX_EXT)
        print(BASE_VIEWS)
        print(analyzer.VIEW_EXT)
        return 0
    if a.list:
        qs = analyzer.METRICS if a.metrics else analyzer.QUERIES
        for i, (name, title, _, _) in enumerate(qs, 1):
            print("%2d. %-26s %s" % (i, name, title))
        return 0

    # --csv and --json are consumed by other programs; progress lines on
    # stdout made the output unparseable, and --quiet was the only escape.
    if a.csv is not None or a.json is not None:
        a.quiet = True

    missing = analyzer.DEPS.missing() if analyzer.DEPS else []
    if missing and not a.quiet:
        print("note: %d dependency/ies absent -- run with --deps to see them"
              % len(missing))

    if not os.path.isdir(a.root):
        # os.walk on a missing path yields nothing silently, so the run used
        # to print a complete, successful-looking report and then traceback in
        # parse_manifests.
        print("not a directory: %s" % a.root, file=sys.stderr)
        return 2

    t0 = time.time()
    db = sqlite3.connect(":memory:")
    n = build(analyzer, os.path.abspath(a.root), db,
              include_tests=not a.no_tests,
              include_generated=a.include_generated,
              include_vendored=a.include_vendored,
              quiet=a.quiet)
    took = time.time() - t0
    p = {"mod": a.module, "lim": a.limit}

    if a.sql:
        try:
            cur = db.execute(a.sql, p) if ":" in a.sql else db.execute(a.sql)
            if cur.description is None:
                # A statement that returns no rows used to traceback on
                # cur.description AFTER being applied, throwing away the run.
                print(" %d row(s) affected" % cur.rowcount)
            else:
                render(cur.fetchall(), [d[0] for d in cur.description])
        except sqlite3.Error as exc:
            print(" query failed: %s" % exc, file=sys.stderr)
            db.close()
            return 2
        db.close()
        return 0
    if a.csv is not None or a.json is not None:
        idx = (a.csv if a.csv is not None else a.json) - 1
        qs_csv = analyzer.METRICS if a.metrics else analyzer.QUERIES
        if not (0 <= idx < len(qs_csv)):
            print("no query %d" % (idx + 1), file=sys.stderr)
            return 2
        cur = db.execute(qs_csv[idx][3], p)
        cols = [d[0] for d in cur.description]
        rows = cur.fetchall()
        if a.csv:
            w = csv.writer(sys.stdout)
            w.writerow(cols)
            w.writerows(rows)
        else:
            import json as _json
            _json.dump([dict(zip(cols, r)) for r in rows], sys.stdout,
                       indent=2, default=str)
            print()
        db.close()
        return 0

    if not a.quiet:
        print("codegraph-%s: %d files parsed into memory in %.1fs "
              "module=%s limit=%s" % (analyzer.LANG, n, took, a.module,
                                      "all" if a.limit < 0 else a.limit))
    if a.report:
        report(db, analyzer)

    qs = analyzer.METRICS if a.metrics else analyzer.QUERIES
    sel = a.which or range(1, len(qs) + 1)
    for k in sel:
        if not (1 <= k <= len(qs)):
            continue
        name, title, notes, sql = qs[k - 1]
        print("\n" + "=" * 78)
        print("Q%d. %s -- %s" % (k, name, title))
        print("-" * 78)
        for line in notes.splitlines():
            print(" " + line)
        print()
        try:
            cur = db.execute(sql, p)
            render(cur.fetchall(), [d[0] for d in cur.description])
        except sqlite3.Error as exc:
            print(" query failed: %s" % exc)

    if a.save:
        # backup() replaces the destination's entire contents. Overwriting an
        # unrelated database on a path typo is not recoverable, and following
        # a symlink to do it is worse.
        try:
            if os.path.lexists(a.save) and not a.force:
                print("\nrefusing to overwrite %s (pass --force)%s"
                      % (a.save,
                         " -- it is a symlink to %s" % os.path.realpath(a.save)
                         if os.path.islink(a.save) else ""),
                      file=sys.stderr)
            else:
                if os.path.islink(a.save):
                    os.unlink(a.save)
                dest = sqlite3.connect(a.save)
                db.backup(dest)
                dest.close()
                print("\n(graph also written to %s)" % a.save)
        except (sqlite3.Error, OSError) as exc:
            # The graph is finished and the answers are already printed; a
            # failed save must not discard them.
            print("\ncould not write %s: %s" % (a.save, exc), file=sys.stderr)
    db.close()
    return 0


# ==========================================================================
# _tsbase.py
# A tree-sitter analyzer that only needs node-type tables to specialise.
#
# Eight of the nine languages here parse with tree-sitter, and the work is the
# same every time: walk the tree, find the things that are functions, find the
# things that are types, count what is inside each body, resolve the calls. Only
# the node-type NAMES differ, and those are data.
#
# So this class does the walking and each language supplies tables:
#
#     FUNC_KINDS      node type -> symbol kind ('function', 'method', ...)
#     TYPE_KINDS      node type -> symbol kind ('class', 'struct', 'trait', ...)
#     NAME_FIELD      field holding the name, per node type or one default
#     LOOP_NODES      node types that are loops
#     BRANCH_NODES    node types that branch
#     NEST_NODES      node types that raise the nesting level
#     CALL_NODES      node types that are calls
#     COUNTERS        node type -> metric column, counted in one pass
#
# What a language still has to write itself is the part that is genuinely
# language-specific: how to read a call's callee name, how to resolve it, what
# its hazards are, and its query catalogue.
#
# Two things this deliberately does NOT hide:
#
# * Nesting. Every language spells `else if` differently and most spell it as a
#   nested `if`, which makes a flat 30-arm dispatch look 30 levels deep. Each
#   language declares `ELSE_FIELD` so the chain can be flattened, because
#   uncorrected it puts every dispatch table above every genuinely nested loop --
#   exactly backwards.
#
# * Blindness. A call whose target is not in the tree is either out of scope or
#   unresolved, and those are different facts. The base keeps them apart.
# ==========================================================================

DOC_PREFIXES = ("///", "/**", "##", '"""', "'''", "#'", "--|")

MAGIC_STR = {str(v) for v in MAGIC_OK} | {
    "0x0", "0x1", "0xff", "0xFF", "0.0", "1.0", "-1", ""}

NUM_RE = re.compile(r'^[-+]?(?:0[xXbBoO][0-9a-fA-F_]+|[\d_]+(?:\.[\d_]*)?'
                    r'(?:[eE][-+]?\d+)?)[uUlLfFdD]*$')

@dataclass
class Scope:
    """Where we are while walking: the enclosing symbol and type."""
    symbol_id: Optional[int] = None
    qual_prefix: str = ""
    type_name: str = ""
    type_id: Optional[int] = None
    depth: int = 0

@dataclass
class BodyStats:
    """Everything counted in one pass over one function body."""
    counts: dict[str, int] = dc_field(default_factory=dict)
    cyclomatic: int = 1
    cognitive: int = 0
    max_nesting: int = 0
    max_loop_depth: int = 0
    n_tokens: int = 0
    operators: set[str] = dc_field(default_factory=set)
    operands: set[str] = dc_field(default_factory=set)
    n_operators: int = 0
    n_operands: int = 0
    #: (callee_text, line, is_dynamic, in_loop)
    calls: list[tuple[str, int, bool, bool]] = dc_field(default_factory=list)
    literals: list[tuple[str, str, int, bool]] = dc_field(default_factory=list)

    def bump(self, key: str, n: int = 1) -> None:
        self.counts[key] = self.counts.get(key, 0) + n

class TreeSitterAnalyzer(Analyzer):
    """Base for every grammar-backed analyzer in this repo."""

    # -- what the language must declare ------------------------------------
    GRAMMAR_MODULE = ""
    GRAMMAR_PIP = ""
    GRAMMAR_SYMBOL = "language"

    FUNC_KINDS: dict[str, str] = {}
    TYPE_KINDS: dict[str, str] = {}
    #: node type -> field name holding its identifier. "" means search children.
    NAME_FIELD: dict[str, str] = {}
    DEFAULT_NAME_FIELD = "name"
    #: node types whose text IS an identifier, used when NAME_FIELD misses
    IDENT_NODES: tuple[str, ...] = ("identifier",)

    BODY_FIELD = "body"
    PARAMS_FIELD = "parameters"
    RETURN_FIELD = "return_type"
    #: field holding the `else` branch, so `else if` chains can be flattened
    ELSE_FIELD = "alternative"
    IF_NODES: tuple[str, ...] = ()

    LOOP_NODES: tuple[str, ...] = ()
    BRANCH_NODES: tuple[str, ...] = ()
    NEST_NODES: tuple[str, ...] = ()
    CALL_NODES: tuple[str, ...] = ()
    #: field on a call node holding the thing being called
    CALL_FUNC_FIELD = "function"
    RETURN_NODES: tuple[str, ...] = ()
    THROW_NODES: tuple[str, ...] = ()
    TRY_NODES: tuple[str, ...] = ()
    CATCH_NODES: tuple[str, ...] = ()
    FINALLY_NODES: tuple[str, ...] = ()
    SWITCH_NODES: tuple[str, ...] = ()
    CASE_NODES: tuple[str, ...] = ()
    LAMBDA_NODES: tuple[str, ...] = ()
    AWAIT_NODES: tuple[str, ...] = ()
    COMMENT_NODES: tuple[str, ...] = ("comment",)
    STRING_NODES: tuple[str, ...] = ("string", "string_literal")
    NUMBER_NODES: tuple[str, ...] = ("number", "integer", "float",
                                     "number_literal", "int_literal")
    #: binary/unary operator node types, for the Halstead proxy
    OPERATOR_NODES: tuple[str, ...] = (
        "binary_expression", "unary_expression", "assignment_expression",
        "augmented_assignment_expression", "update_expression",
        "subscript_expression", "member_expression", "field_expression",
    )
    #: extra node type -> metric column, counted in the same single pass
    COUNTERS: dict[str, str] = {}
    #: substrings of a callee name -> metric column bumped when inside a loop
    LOOP_CALL_COUNTERS: dict[str, str] = {}

    IMPORT_NODES: tuple[str, ...] = ()

    #: node types whose presence anywhere in a body sets a boolean column
    FLAG_NODES: dict[str, str] = {}

    def __init__(self) -> None:
        super().__init__()
        #: name -> [(symbol_id, file_id, module_id, type_name)]
        self.by_name: dict[str, list[tuple[int, int, int, str]]] = {}
        self.by_qual: dict[str, int] = {}
        #: (caller_sid, file_id, module_id, name, line, type_name)
        #: Unresolved call sites, held as parallel COLUMNS rather than one
        #: tuple per row. On elasticsearch this reaches 3.68M rows: as
        #: `list[tuple]` that is 3.68M separate tuple objects at 487 MB, and
        #: they are all live exactly when peak RSS is set. Four `array('i')`
        #: columns plus two string lists is 121 MB, because the strings are
        #: shared rather than copied and only the list spines cost anything.
        #: Measured -366 MB for +0.6s on a 342s build -- 10% of peak for 0.18%
        #: of wall. Signed 32-bit is deliberate: symbol ids and line numbers
        #: cannot approach 2^31 in any real repository, and `array` raises
        #: OverflowError rather than truncating if that is ever wrong.
        self.pend_sid: array.array = array.array("i")
        self.pend_fid: array.array = array.array("i")
        self.pend_mid: array.array = array.array("i")
        self.pend_line: array.array = array.array("i")
        self.pend_name: list[str] = []
        self.pend_type: list[str] = []
        self.n_external = 0
        self.n_resolved = 0
        self.n_unresolved = 0
        self._ext_by_caller: dict[int, int] = {}
        self._sym_cols: set[str] = set()

    # -- lifecycle ---------------------------------------------------------
    def setup(self) -> ParserHandle:
        """Build the parser, or stop.

        There is no regex fallback for a real grammar, and pretending
        otherwise was the worst bug this tool had: with the grammar missing it
        catalogued every file, parsed none, and printed "0 of 0 call sites
        unresolved" -- which reads as a perfectly resolved graph of a clean
        repository rather than as nothing at all. An empty result that looks
        like a finding is the failure mode this whole tool exists to avoid, so
        it refuses instead, and says exactly what to install.
        """
        self.check_metric_columns()
        handle = load(self.LANG, self.GRAMMAR_MODULE, self.GRAMMAR_PIP,
                      self.GRAMMAR_SYMBOL)
        if not handle.ok:
            raise SystemExit(
                "codegraph-%s cannot parse %s without a grammar: %s\n"
                "\n"
                "  %s -m pip install 'tree-sitter>=0.26,<0.27' %s\n"
                "\n"
                "or let the tool do it:\n"
                "\n"
                "  %s --install-deps\n"
                "\n"
                "There is no regex fallback. Producing an empty graph would "
                "look\nidentical to analysing a repository with nothing in it."
                % (self.LANG, self.LANG, handle.note, sys.executable,
                   self.GRAMMAR_PIP.split(">")[0].split("=")[0],
                   os.path.basename(sys.argv[0] or
                                    "codegraph_%s.py" % self.LANG)))
        return handle

    def check_metric_columns(self) -> None:
        """Refuse to run with a metric that has nowhere to go.

        `insert_symbol` drops metric keys the schema does not have, so that one
        typo cannot abort a whole repo scan. The cost of that mercy is a column
        which silently stays zero forever -- every query over it returns
        nothing, and nothing anywhere says why. Checking the node tables
        against the declared columns at startup turns a silent wrong answer
        into a loud one, which is the trade worth making.
        """
        declared = self.known_columns()
        produced: set[str] = set()
        for table in (self.COUNTERS, self.LOOP_CALL_COUNTERS, self.FLAG_NODES):
            produced.update(table.values())
        missing = sorted(produced - declared)
        if missing:
            raise SystemExit(
                "codegraph_%s: these metrics are counted but have no column, "
                "so they would silently stay zero:\n  %s\n"
                "Add them to EXTRA_SYMBOL_COLS."
                % (self.LANG, ", ".join(missing)))

    def known_columns(self) -> set[str]:
        if not self._sym_cols:
            self._sym_cols = set(UNIVERSAL_METRIC_COLS)
            self._sym_cols.update("n_" + c for c in self.HAZARD_CATEGORIES)
            self._sym_cols.update(n for n, _ in self.EXTRA_SYMBOL_COLS)
        return self._sym_cols

    # -- parse -------------------------------------------------------------
    def parse_file(self, rec: FileRec, db: sqlite3.Connection,
                   bufs: Buffers) -> None:
        if not self.parser.ok:
            self.parse_file_fallback(rec, db, bufs)
            return
        tree = self.parser.parse(rec.data)
        root = tree.root_node
        if root.has_error:
            errs, missing = count_errors(root)
            db.execute("UPDATE files SET n_parse_errors=?, n_missing_nodes=? "
                       "WHERE id=?", (errs, missing, rec.fid))
        self.parse_imports(root, rec, bufs)
        self.walk_scope(root, rec, db, bufs, Scope())
        self.emit_module_scope(root, rec, db, bufs)
        self.parse_file_extra(root, rec, db, bufs)

    def parse_file_fallback(self, rec: FileRec, db: sqlite3.Connection,
                            bufs: Buffers) -> None:
        """Unreachable: `setup()` refuses to return without a grammar.

        Kept as a guard so that if a future change makes the parser optional
        again, the failure is a loud exception rather than a silent empty
        graph.
        """
        raise RuntimeError(
            "no grammar for %s -- setup() should already have refused"
            % self.LANG)

    #: Files whose top level is only declarations gain nothing from a
    #: `<module>` symbol. Languages where it is dead weight set this False.
    MODULE_SCOPE_SYMBOL = True

    def emit_module_scope(self, root: Any, rec: FileRec,
                          db: sqlite3.Connection, bufs: Buffers) -> None:
        """One symbol per file for the statements that sit outside everything.

        Without this, top-level code is measured nowhere and its calls never
        become edges -- so a helper invoked only from module scope looks dead,
        an IIFE's whole body is invisible, and a file of pure configuration
        contributes nothing but an entry in `files`.

        The symbol is emitted only when there is something to attribute to it,
        so a file that is entirely class and function declarations does not
        gain a row of zeroes.
        """
        if not self.MODULE_SCOPE_SYMBOL:
            return
        prune = set(self.FUNC_KINDS) | set(self.TYPE_KINDS)
        stats = self.measure(root, rec, prune=prune)
        if not stats.calls and stats.n_tokens < 8:
            return

        m: dict[str, Any] = dict(stats.counts)
        m.update(
            cyclomatic=stats.cyclomatic,
            cognitive=stats.cognitive,
            max_nesting=stats.max_nesting,
            max_loop_depth=stats.max_loop_depth,
            n_tokens=stats.n_tokens,
            n_operators=stats.n_operators,
            n_operands=stats.n_operands,
            n_distinct_operators=len(stats.operators),
            n_distinct_operands=len(stats.operands),
            is_generated=int(rec.is_generated),
            is_test=int(rec.is_test),
        )
        sid = self.insert_symbol(
            db, rec, "<module>", "module", root, rec.rel, None,
            "top-level statements of %s" % rec.rel, "", "", m)
        for text, line, dynamic, in_loop in stats.calls:
            if dynamic or not text:
                continue
            self.add_pending(sid, rec.fid, rec.mid, text, line, "")
        self.emit_hazards(stats, sid, rec, bufs)
        for kindl, value, line, magic in stats.literals:
            bufs.literals.append((sid, rec.fid, kindl, value[:200], line,
                                  int(magic)))
        self.module_scope_extra(root, rec, db, bufs, sid, stats)

    def module_scope_extra(self, root: Any, rec: FileRec,
                           db: sqlite3.Connection, bufs: Buffers,
                           sid: int, stats: BodyStats) -> None:
        """Hook: language rows that belong to top-level code."""

    def parse_file_extra(self, root: Any, rec: FileRec,
                         db: sqlite3.Connection, bufs: Buffers) -> None:
        """Hook for whatever else the language wants from the whole file."""

    def parse_imports(self, root: Any, rec: FileRec, bufs: Buffers) -> None:
        """Default: record each import node's text. Languages usually override."""
        if not self.IMPORT_NODES:
            return
        want = set(self.IMPORT_NODES)
        for node in walk(root):
            if node.type not in want:
                continue
            target = text_of(node, rec.data)[:300]
            bufs.imports.append(
                (rec.fid, target, None, None, node.type,
                 node.start_point[0] + 1, 0, 0, 0, 0, 0, 1))

    # -- scope walk --------------------------------------------------------
    def walk_scope(self, node: Any, rec: FileRec, db: sqlite3.Connection,
                   bufs: Buffers, scope: Scope) -> None:
        """Descend, emitting a symbol for every function and type we meet.

        Iterative rather than recursive: a minified bundle or a generated
        parser table nests deep enough that recursion here raises
        RecursionError halfway through a repo, which is indistinguishable from
        a crash.
        """
        stack: list[tuple[Any, Scope]] = [(c, scope) for c in
                                          reversed(node.named_children)]
        while stack:
            cur, sc = stack.pop()
            kind = self.FUNC_KINDS.get(cur.type)
            if kind:
                sid = self.emit_function(cur, rec, db, bufs, sc, kind)
                inner = Scope(sid, "%s%s." % (sc.qual_prefix,
                                              self.node_name(cur, rec) or "?"),
                              sc.type_name, sc.type_id, sc.depth + 1)
                body = cur.child_by_field_name(self.BODY_FIELD)
                for c in reversed((body or cur).named_children):
                    stack.append((c, inner))
                continue
            kind = self.TYPE_KINDS.get(cur.type)
            if kind:
                sid = self.emit_type(cur, rec, db, bufs, sc, kind)
                name = self.node_name(cur, rec) or "?"
                inner = Scope(sid, "%s%s." % (sc.qual_prefix, name),
                              name, sid, sc.depth + 1)
                body = cur.child_by_field_name(self.BODY_FIELD)
                for c in reversed((body or cur).named_children):
                    stack.append((c, inner))
                continue
            for c in reversed(cur.named_children):
                stack.append((c, sc))

    # -- naming ------------------------------------------------------------
    def node_name(self, node: Any, rec: FileRec) -> str:
        field = self.NAME_FIELD.get(node.type, self.DEFAULT_NAME_FIELD)
        if field:
            child = node.child_by_field_name(field)
            if child is not None:
                return text_of(child, rec.data).strip()
        for c in node.named_children:
            if c.type in self.IDENT_NODES:
                return text_of(c, rec.data).strip()
        return ""

    # -- symbol emission ---------------------------------------------------
    def emit_function(self, node: Any, rec: FileRec, db: sqlite3.Connection,
                      bufs: Buffers, scope: Scope, kind: str) -> int:
        name = self.node_name(node, rec) or "(anonymous)"
        qual = scope.qual_prefix + name
        body = node.child_by_field_name(self.BODY_FIELD) or node
        stats = self.measure(body, rec)

        m: dict[str, Any] = dict(stats.counts)
        m.update(
            cyclomatic=stats.cyclomatic,
            cognitive=stats.cognitive,
            max_nesting=stats.max_nesting,
            max_loop_depth=stats.max_loop_depth,
            n_tokens=stats.n_tokens,
            n_operators=stats.n_operators,
            n_operands=stats.n_operands,
            n_distinct_operators=len(stats.operators),
            n_distinct_operands=len(stats.operands),
            sloc=self.sloc_of(node, rec),
            body_bytes=body.end_byte - body.start_byte,
            is_generated=int(rec.is_generated),
        )
        m.update(self.count_params(node, rec))
        m.update(self.function_flags(node, rec, scope))
        doc = self.docstring_lines(node, rec)
        m["n_doc_lines"] = doc
        m["has_doc"] = 1 if doc else 0

        sid = self.insert_symbol(
            db, rec, name, kind, node, qual, scope.symbol_id,
            self.signature_of(node, rec),
            self.return_type_of(node, rec),
            self.visibility_of(node, rec), m)

        self.emit_params(node, rec, sid, bufs)
        self.emit_attributes(node, rec, sid, bufs)
        for text, line, dynamic, in_loop in stats.calls:
            if dynamic or not text:
                continue
            self.add_pending(sid, rec.fid, rec.mid, text, line,
                                 scope.type_name)
        self.emit_hazards(stats, sid, rec, bufs)
        for kindl, value, line, magic in stats.literals:
            bufs.literals.append((sid, rec.fid, kindl, value[:200], line,
                                  int(magic)))
        self.function_extra(node, rec, db, bufs, sid, scope, stats)

        self.by_name.setdefault(name, []).append(
            (sid, rec.fid, rec.mid, scope.type_name))
        self.by_qual[qual] = sid
        self.by_qual["%s:%s" % (rec.rel, qual)] = sid
        return sid

    def emit_type(self, node: Any, rec: FileRec, db: sqlite3.Connection,
                  bufs: Buffers, scope: Scope, kind: str) -> int:
        name = self.node_name(node, rec) or "(anonymous)"
        qual = scope.qual_prefix + name
        # A class body is executable in most of these languages, and it is
        # where the declarative layer lives: has_many, validates, attr_accessor,
        # objects = Manager(), use SomeTrait. Measuring the type as if it were
        # inert lost 94% of Rails' associations from the call graph.
        body = node.child_by_field_name(self.BODY_FIELD) or node
        prune = set(self.FUNC_KINDS) | set(self.TYPE_KINDS)
        bstats = self.measure(body, rec, prune=prune)

        m: dict[str, Any] = dict(bstats.counts)
        m.update(
            sloc=self.sloc_of(node, rec),
            is_generated=int(rec.is_generated),
            n_tokens=bstats.n_tokens,
            n_operators=bstats.n_operators,
            n_operands=bstats.n_operands,
        )
        m.update(self.type_flags(node, rec, scope))
        doc = self.docstring_lines(node, rec)
        m["n_doc_lines"] = doc
        m["has_doc"] = 1 if doc else 0
        sid = self.insert_symbol(
            db, rec, name, kind, node, qual, scope.symbol_id,
            text_of(node, rec.data).split("{")[0].strip()[:300], "",
            self.visibility_of(node, rec), m)
        self.emit_attributes(node, rec, sid, bufs)
        # Calls made in the class body belong to the class, not to nothing.
        for text, line, dynamic, in_loop in bstats.calls:
            if dynamic or not text:
                continue
            self.add_pending(sid, rec.fid, rec.mid, text, line,
                                 scope.type_name)
        self.emit_hazards(bstats, sid, rec, bufs)
        self.type_extra(node, rec, db, bufs, sid, scope)
        self.by_name.setdefault(name, []).append(
            (sid, rec.fid, rec.mid, scope.type_name))
        self.by_qual[qual] = sid
        return sid

    def insert_symbol(self, db: sqlite3.Connection, rec: FileRec, name: str,
                      kind: str, node: Any, qual: str,
                      parent_id: Optional[int], signature: str,
                      return_type: str, visibility: str,
                      m: dict[str, Any]) -> int:
        ls = node.start_point[0] + 1
        le = node.end_point[0] + 1
        cols = ["file_id", "module_id", "parent_id", "name", "qual_name",
                "kind", "line_start", "line_end", "n_lines", "byte_start",
                "byte_end", "signature", "return_type", "visibility"]
        vals: list[Any] = [rec.fid, rec.mid, parent_id, name, qual[:400], kind,
                           ls, le, le - ls + 1, node.start_byte, node.end_byte,
                           signature[:400], return_type[:200], visibility]
        # One fixed-width row per symbol, buffered. The old form built the
        # column list from whichever metrics were present, which meant 2,544
        # distinct INSERT shapes on javaparser alone -- impossible to batch,
        # so it ran one statement per symbol: 530,881 of them on elasticsearch.
        # Absent metrics take the default declared in the DDL, so the row this
        # writes is byte-for-byte what the variable-width INSERT produced.
        #
        # The id comes from a counter, not `lastrowid`: `id INTEGER PRIMARY
        # KEY` accepts an explicit value, and a counter from 1 hands out
        # exactly the rowids SQLite would have. That is what makes batching
        # possible at all -- Python's sqlite3 refuses `executemany` with
        # `RETURNING`.
        spec = self._sym_spec
        if spec is None:
            # The column list and every default come from the TABLE, via
            # PRAGMA table_info -- not from `symbol_columns()`, which returns
            # only the language's extras. `known_columns()` also covers the 86
            # universal metric columns (cyclomatic, cognitive, fan_in, ...),
            # and building the spec from the wrong one silently dropped all of
            # them: go/terraform's summed metrics fell from 249,472 to 77,760
            # while symbol and edge counts stayed identical. The schema is the
            # only source that cannot disagree with itself.
            fixed = set(cols) | {"id"}
            spec = self._sym_spec = []
            for _cid, cname, ctype, _nn, dflt, _pk in db.execute(
                    "PRAGMA table_info(symbols)").fetchall():
                if cname in fixed:
                    continue
                is_text = "TEXT" in (ctype or "").upper()
                if dflt is None:
                    d = "" if is_text else 0
                elif is_text:
                    d = dflt.strip("'")
                else:
                    d = int(dflt) if dflt.lstrip("-").isdigit() else dflt
                spec.append((cname, d))
            self._sym_sql = (
                "INSERT INTO symbols(id,%s,%s) VALUES(%s)"
                % (",".join(cols), ",".join(n for n, _ in spec),
                   ",".join("?" * (1 + len(cols) + len(spec)))))
        self._n_sym += 1
        sid = self._n_sym
        row = [sid]
        row.extend(vals)
        for k, dflt in spec:
            v = m.get(k, dflt)
            row.append(int(v) if isinstance(v, bool) else v)
        self._sym_rows.append(tuple(row))
        # Drained periodically, not held to the end. Buffering all of them
        # satisfied the no-single-row-DML rule but cost 89 MB on netty alone
        # (310 -> 399 peak) and would scale to roughly 900 MB on elasticsearch:
        # a batch is only free if it is bounded.
        if len(self._sym_rows) >= SYMBOL_BATCH:
            db.executemany(self._sym_sql, self._sym_rows)
            self._sym_rows.clear()
        return sid

    def flush_symbols(self, db: sqlite3.Connection) -> None:
        """Write every buffered symbol. Called once, after the parse loop.

        Nothing may read the `symbols` TABLE before this runs. Resolution uses
        `by_name`/`by_qual`, which live in Python, so the only thing that had
        to move was JavaScript's handler marking.
        """
        if self._sym_rows:
            db.executemany(self._sym_sql, self._sym_rows)
            self._sym_rows.clear()

    # -- the single measuring pass ----------------------------------------
    def measure(self, body: Any, rec: FileRec,
                prune: Optional[set[str]] = None) -> BodyStats:
        """One cursor walk over a function body, computing everything.

        One pass rather than one per metric: a walk over a 2,000-node body is
        cheap, forty of them are not, and the repos this targets have a million
        functions.

        `prune` names node types whose subtrees to skip. Measuring a file's
        top-level statements uses it to stop at every nested function and type,
        because those already have symbols of their own and counting them here
        would double every metric in the file.
        """
        st = BodyStats()
        src = rec.data
        loops = set(self.LOOP_NODES)
        branches = set(self.BRANCH_NODES)
        nests = set(self.NEST_NODES)
        calls = set(self.CALL_NODES)
        counters = self.COUNTERS
        operators = set(self.OPERATOR_NODES)
        strings = set(self.STRING_NODES)
        numbers = set(self.NUMBER_NODES)
        comments = set(self.COMMENT_NODES)
        ifs = set(self.IF_NODES)
        flags = self.FLAG_NODES

        else_field = self.ELSE_FIELD
        want_elif = bool(ifs) and bool(else_field)
        extra_loops = self.extra_loop_ids(body, rec)
        cursor = body.walk()
        depth = 0
        loop_depth = 0
        # (exit_depth) markers so we know when to unwind
        nest_stack: list[int] = []
        loop_stack: list[int] = []

        while True:
            node = cursor.node
            t = node.type

            while nest_stack and nest_stack[-1] >= depth:
                nest_stack.pop()
            while loop_stack and loop_stack[-1] >= depth:
                loop_stack.pop()
                loop_depth = max(0, loop_depth - 1)

            # tree-sitter-ruby gives its anonymous keyword tokens the same
            # `type` strings as the named nodes -- `if`, `while`, `when`,
            # `rescue`. Matching on type alone counted every Ruby construct
            # twice and inflated every complexity metric in that language by
            # roughly 2x. No other grammar collides (`if_statement` != `if`),
            # so requiring a named node is free everywhere else.
            named = node.is_named
            # Decided inline from the parent. `elif_nodes` used to walk
            # the whole body a SECOND time per symbol just to locate
            # `if` nodes; the relationship is local, so ask the parent.
            # Measured -12% wall on kubernetes, byte-identical output.
            is_elif = False
            if want_elif and t in ifs:
                par = node.parent
                if par is not None:
                    if par.type in ifs:
                        alt = par.child_by_field_name(else_field)
                        is_elif = alt is not None and alt.id == node.id
                    else:
                        gp = par.parent
                        if gp is not None and gp.type in ifs:
                            alt = gp.child_by_field_name(else_field)
                            if alt is not None and alt.id == par.id:
                                first = par.named_child(0)
                                is_elif = (first is not None
                                           and first.id == node.id)
            if named and t in nests and not is_elif and node is not body:
                nest_stack.append(depth)
                st.max_nesting = max(st.max_nesting, len(nest_stack))
            if named and (t in loops or node.id in extra_loops):
                loop_stack.append(depth)
                loop_depth += 1
                st.max_loop_depth = max(st.max_loop_depth, loop_depth)
                st.cyclomatic += 1
                st.cognitive += max(1, len(nest_stack))
                st.bump("n_loops")
            elif named and t in branches:
                st.cyclomatic += 1
                st.cognitive += 1 if is_elif else max(1, len(nest_stack))
                st.bump("n_branches")
                if is_elif:
                    st.bump("n_elif")
                if loop_depth:
                    st.bump("branch_in_loop")

            key = counters.get(t)
            if key is not None:
                st.bump(key)
            fkey = flags.get(t)
            if fkey is not None:
                st.counts[fkey] = 1

            if t in calls:
                self.on_call(node, src, st, loop_depth, len(nest_stack))
            elif t in operators:
                st.n_operators += 1
                st.operators.add(t)
            elif t in strings:
                txt = text_of(node, src)
                st.bump("n_string_lit")
                st.operands.add(txt[:40])
                st.n_operands += 1
                self.on_string(node, txt, src, st, loop_depth)
            elif t in numbers:
                txt = text_of(node, src).strip()
                st.n_operands += 1
                st.operands.add(txt)
                magic = txt not in MAGIC_STR and NUM_RE.match(txt) is not None
                if magic:
                    st.bump("n_magic")
                    st.literals.append(("number", txt,
                                        node.start_point[0] + 1, True))
                if "." in txt or "e" in txt.lower():
                    st.bump("n_float_lit")
            elif t in comments:
                st.bump("n_comment_lines",
                        node.end_point[0] - node.start_point[0] + 1)
            elif node.child_count == 0:
                st.n_tokens += 1
                st.n_operands += 1
                st.operands.add(text_of(node, src)[:40])

            self.on_node(node, src, st, loop_depth, len(nest_stack))

            descend = not (prune is not None and node is not body
                           and t in prune)
            if descend and cursor.goto_first_child():
                depth += 1
                continue
            while not cursor.goto_next_sibling():
                if not cursor.goto_parent():
                    st.n_tokens += st.n_operators
                    return st
                depth -= 1

    def extra_loop_ids(self, body: Any, rec: FileRec) -> set[int]:
        """Nodes to treat as loops beyond `LOOP_NODES`, by tree-sitter id.

        Some languages do not iterate with a loop keyword. Ruby's `each do ...
        end` is a block, and counting only `while`/`until`/`for` there gave a
        loop depth of zero on essentially every method in Rails -- which
        silently made every per-iteration query rank by a dead column.

        Empty by default: a language that has real loops should not pay for a
        second traversal.
        """
        return set()

    # -- per-node hooks a language may override ---------------------------
    def on_call(self, node: Any, src: bytes, st: BodyStats,
                loop_depth: int, nest: int) -> None:
        st.bump("n_calls")
        if loop_depth:
            st.bump("call_in_loop")
        fn = node.child_by_field_name(self.CALL_FUNC_FIELD)
        if fn is None:
            st.bump("n_dynamic_calls")
            st.calls.append(("", node.start_point[0] + 1, True, bool(loop_depth)))
            return
        name = text_of(fn, src).strip()
        dynamic = not name or not name[0].isalpha() and name[0] not in "_$"
        st.calls.append((name[:200], node.start_point[0] + 1, dynamic,
                         bool(loop_depth)))
        if dynamic:
            st.bump("n_dynamic_calls")
        if loop_depth:
            base = name.rsplit(".", 1)[-1].rsplit("::", 1)[-1]
            for needle, col in self.LOOP_CALL_COUNTERS.items():
                if needle == base or needle in name:
                    st.bump(col)

    def on_string(self, node: Any, text: str, src: bytes, st: BodyStats,
                  loop_depth: int) -> None:
        """Hook: languages look for SQL, regexes, format strings here."""

    def on_node(self, node: Any, src: bytes, st: BodyStats,
                loop_depth: int, nest: int) -> None:
        """Hook: anything the COUNTERS table cannot express."""

    # -- per-symbol detail a language may override ------------------------
    def function_flags(self, node: Any, rec: FileRec,
                       scope: Scope) -> dict[str, Any]:
        return {}

    def type_flags(self, node: Any, rec: FileRec,
                   scope: Scope) -> dict[str, Any]:
        return {}

    def function_extra(self, node: Any, rec: FileRec, db: sqlite3.Connection,
                       bufs: Buffers, sid: int, scope: Scope,
                       stats: BodyStats) -> None:
        """Hook: rows for the language's own tables."""

    def type_extra(self, node: Any, rec: FileRec, db: sqlite3.Connection,
                   bufs: Buffers, sid: int, scope: Scope) -> None:
        """Hook: rows for the language's own tables."""

    def count_params(self, node: Any, rec: FileRec) -> dict[str, Any]:
        """Arity, set BEFORE the symbol row is written.

        `emit_params` runs after the insert and only fills the `params` table,
        so without this every symbol reported zero parameters while the rows
        sat there -- and every query that ranked by arity returned nothing at
        all, which looks exactly like "this repo has no wide signatures".
        A language whose parameters are not a flat child list overrides this.
        """
        params = node.child_by_field_name(self.PARAMS_FIELD)
        if params is None:
            return {}
        kids = [c for c in params.named_children
                if c.type not in self.COMMENT_NODES]
        optional = sum(
            1 for c in kids
            if c.type.startswith("optional")
            or c.child_by_field_name("value") is not None
            or c.child_by_field_name("default_value") is not None)
        return {"n_params": len(kids), "n_optional_params": optional}

    def emit_params(self, node: Any, rec: FileRec, sid: int,
                    bufs: Buffers) -> None:
        params = node.child_by_field_name(self.PARAMS_FIELD)
        if params is None:
            return
        for pos, p in enumerate(params.named_children):
            if p.type in self.COMMENT_NODES:
                continue
            name = self.node_name(p, rec)
            ptype = ""
            tnode = p.child_by_field_name("type")
            if tnode is not None:
                ptype = text_of(tnode, rec.data).strip()
            if not name:
                name = text_of(p, rec.data).strip()[:80]
            bufs.params.append(
                (sid, pos, name[:120], ptype[:200], None, 0, 0, 0, 0, 0, 0,
                 int(not ptype), ptype.count("<") + ptype.count("[")))

    def emit_attributes(self, node: Any, rec: FileRec, sid: int,
                        bufs: Buffers) -> None:
        """Hook: annotations, decorators, derives, struct tags."""

    def emit_hazards(self, stats: BodyStats, sid: int, rec: FileRec,
                     bufs: Buffers) -> None:
        seen: dict[str, list[Any]] = {}
        for text, line, dynamic, in_loop in stats.calls:
            if not text:
                continue
            cat = self.hazard_of(text)
            if cat is None:
                continue
            pattern, category = cat
            e = seen.get(pattern)
            if e is None:
                seen[pattern] = [category, 1, line]
            else:
                e[1] += 1
        for pattern, (category, n, line) in seen.items():
            bufs.add_hazard(sid, pattern[:120], category, n, line)

    def hazard_of(self, callee: str) -> Optional[tuple[str, str]]:
        """(pattern, category) for a call, or None. Languages override."""
        return None

    # -- text helpers ------------------------------------------------------
    #: Line prefixes that make a line a comment in the languages here. Used
    #: only to keep `sloc` meaning ONE thing across all nine analyzers -- it
    #: previously meant four different things, so any cross-language
    #: comparison in a report was invalid.
    _COMMENT_PREFIX = ("//", "#", "/*", "*", "*/", chr(34)*3, chr(39)*3,
                       "--", "%")

    def sloc_of(self, node: Any, rec: FileRec) -> int:
        """Lines that are neither blank nor comment-only.

        Deliberately prefix-based rather than node-based: a node walk would be
        exact but costs a second traversal per symbol, and the prefix test
        agrees with it on everything except a comment sharing a line with code
        -- which counts as code either way.
        """
        seg = rec.data[node.start_byte:node.end_byte].decode("utf-8", "replace")
        n = 0
        for line in seg.splitlines():
            t = line.strip()
            if t and not t.startswith(self._COMMENT_PREFIX):
                n += 1
        return n

    def signature_of(self, node: Any, rec: FileRec) -> str:
        body = node.child_by_field_name(self.BODY_FIELD)
        end = body.start_byte if body is not None else node.end_byte
        return rec.data[node.start_byte:end].decode("utf-8", "replace").strip()

    def return_type_of(self, node: Any, rec: FileRec) -> str:
        r = node.child_by_field_name(self.RETURN_FIELD)
        return text_of(r, rec.data).strip() if r is not None else ""

    def visibility_of(self, node: Any, rec: FileRec) -> str:
        return ""

    def docstring_lines(self, node: Any, rec: FileRec) -> int:
        """Doc comment immediately above, counted in lines."""
        prev = node.prev_sibling
        n = 0
        while prev is not None and prev.type in self.COMMENT_NODES:
            txt = text_of(prev, rec.data).lstrip()
            if txt.startswith(DOC_PREFIXES):
                n += prev.end_point[0] - prev.start_point[0] + 1
            elif n == 0 and prev.end_point[0] + 1 >= node.start_point[0]:
                n += prev.end_point[0] - prev.start_point[0] + 1
            else:
                break
            prev = prev.prev_sibling
        return n

    # -- call resolution ---------------------------------------------------
    def add_pending(self, sid: int, fid: int, mid: int, name: str,
                    line: int, ty: str = "") -> None:
        """Record a call whose target is not known yet, column-wise.

        Both string columns are interned. `text_of()` decodes a FRESH `str`
        from the source bytes on every call, so 3.68M rows on elasticsearch
        held 3.68M distinct objects for roughly 160k distinct values -- 8x
        duplication on callee names and 23x on types. Interning collapses them
        to one object per value: measured 507 MB -> 74 MB for these two
        columns, 12% of peak RSS, for 2.2s of intern calls on a 342s build.
        """
        self.pend_sid.append(sid)
        self.pend_fid.append(fid)
        self.pend_mid.append(mid)
        self.pend_line.append(line)
        self.pend_name.append(sys.intern(name))
        self.pend_type.append(sys.intern(ty))

    def iter_pending(self):
        """(sid, fid, mid, name, line, type) per recorded call.

        `zip` builds one transient tuple per step instead of holding 3.68M of
        them, which is the entire point of storing this column-wise.
        """
        return zip(self.pend_sid, self.pend_fid, self.pend_mid,
                   self.pend_name, self.pend_line, self.pend_type)

    def resolve_calls(self, db: sqlite3.Connection, bufs: Buffers) -> None:
        """Turn recorded call names into edges, and say what we could not.

        Three outcomes, kept apart on purpose:
          resolved   -> an edge
          external   -> a call that leaves the tree by design (n_external_calls)
          unresolved -> we genuinely lost the thread (unresolved_calls)

        Folding `external` into `unresolved` makes a normal repo read as 70%
        blind when almost all of that is the standard library behaving exactly
        as documented, and the honesty column stops being informative.
        """
        unique: dict[str, tuple[int, int, int, str]] = {
            n: c[0] for n, c in self.by_name.items() if len(c) == 1}
        file_scope: dict[tuple[int, str], int] = {}
        for nm, cands in self.by_name.items():
            for sid, fid, mid, ty in cands:
                file_scope.setdefault((fid, nm), sid)
        type_scope: dict[tuple[str, str], int] = {}
        #: symbol_id -> (file_id, module_id) of the DEFINITION. Needed because
        #: `same_file` and `same_module` describe where the callee lives, and
        #: three of the four lookups below know only the caller's location.
        #: Without this they compared the caller's fid to itself and stamped
        #: every such edge same_file=1: 42% of Java's edges, 45% of
        #: TypeScript's. Every cross-module query was reading a constant.
        sym_loc: dict[int, tuple[int, int]] = {}
        for nm, cands in self.by_name.items():
            for sid, fid, mid, ty in cands:
                sym_loc.setdefault(sid, (fid, mid))
                if ty:
                    type_scope.setdefault((ty, nm), sid)

        for sid, fid, mid, raw, line, ty in self.iter_pending():
            name = self.normalise_callee(raw)
            if not name:
                continue
            base = name.rsplit(".", 1)[-1].rsplit("::", 1)[-1]
            target = None
            if ty:
                target = type_scope.get((ty, base))
                if target is not None:
                    target = (target, fid, mid, ty)
            if target is None:
                q = self.by_qual.get(name)
                if q is not None:
                    target = (q, fid, mid, "")
            if target is None:
                s2 = file_scope.get((fid, base))
                if s2 is not None:
                    target = (s2, fid, mid, "")
            if target is None:
                target = unique.get(base)
            if target is None:
                if self.is_external(name, base, fid):
                    self._ext_by_caller[sid] = self._ext_by_caller.get(sid, 0) + 1
                    self.n_external += 1
                else:
                    bufs.add_unresolved(sid, name[:160], line)
                    self.n_unresolved += 1
                continue
            # Ask where the CALLEE is defined. `target[1]`/`target[2]` are
            # the caller's own fid/mid in three of the four branches above,
            # so comparing them to fid/mid was always true.
            tloc = sym_loc.get(target[0])
            bufs.add_edge(sid, target[0],
                          tloc is not None and tloc[0] == fid,
                          tloc is not None and tloc[1] == mid, line)
            self.n_resolved += 1

        if self._ext_by_caller:
            if "n_external_calls" in self.known_columns():
                db.executemany(
                    "UPDATE symbols SET n_external_calls=? WHERE id=?",
                    [(v, k) for k, v in self._ext_by_caller.items()])
        db.execute(
            "INSERT OR REPLACE INTO meta(key,value) VALUES(?,?)",
            ("calls_resolved",
             "%d in-tree / %d external / %d unresolved (%d%% of in-scope resolved)"
             % (self.n_resolved, self.n_external, self.n_unresolved,
                100 * self.n_resolved
                // max(1, self.n_resolved + self.n_unresolved))))
        self.flush_extra(db, bufs)

    def normalise_callee(self, raw: str) -> str:
        return raw.strip()

    def is_external(self, name: str, base: str, fid: int) -> bool:
        """Languages override with their stdlib/package knowledge."""
        return False

    def flush_extra(self, db: sqlite3.Connection, bufs: Buffers) -> None:
        """Write the language's own accumulated tables."""

UNIVERSAL_METRIC_COLS = """
n_params n_optional_params n_generic_params n_overloads arity_rank
is_public is_static is_async is_generator is_abstract is_override
is_exported is_test is_deprecated is_entrypoint is_generated
sloc body_bytes n_comment_lines n_doc_lines has_doc
cyclomatic cognitive max_nesting n_tokens n_operators n_operands
n_distinct_operators n_distinct_operands halstead_volume maintainability
n_loops n_branches n_returns n_early_returns n_switch n_cases n_ternary
n_logical n_try n_catch n_catch_broad n_catch_empty n_finally n_throw
n_labels n_gotos
max_loop_depth call_in_loop alloc_in_loop io_in_loop await_in_loop
lock_in_loop concat_in_loop regex_in_loop query_in_loop branch_in_loop
n_locals n_assign n_compound_assign n_incdec n_cmp n_bitop n_shift
n_arith n_string_lit n_regex_lit n_float_lit n_magic n_null_check
n_subscript n_member_access n_lambda n_closure_capture
n_calls n_unique_calls n_dynamic_calls n_unresolved_calls
fan_in fan_out n_callsites is_recursive is_leaf is_root
n_hazards risk_score
""".split()


# ==========================================================================
# lang_ruby.py
# codegraph_ruby.py -- parse a Ruby tree into a graph and query it.
#
# Targets Ruby 4.0 (released 2025-12-25; there was never a 3.5 -- 3.5 became
# 4.0). Parses with tree-sitter-ruby.
#
# Read query 1 before anything else. In every other language in this repo the
# call graph is mostly complete and the blindspot report is a footnote. In Ruby
# it is the headline. `send`, `public_send`, `define_method`, `method_missing`,
# `const_get`, `constantize` and `class_eval` on a heredoc all move dispatch from
# the syntax tree to run time, and none of them leaves an edge behind. Every
# reachability number here -- fan_in, dead-code, the taint walks -- is therefore a
# LOWER BOUND, and the bound is loosest exactly where a framework does its most
# interesting work. This tool counts the blind spots and tells you how blind it
# is instead of quietly rounding them to zero.
#
# Four Ruby facts baked in, all of them verified against the grammar rather than
# assumed:
#
# * tree-sitter-ruby 0.23.1 is ABI 14 and predates Ruby 4.0. Ruby 4.0 lets a
#   binary logical operator LEAD a continuation line (`x = a` / `  && b`); on
#   that shape this grammar sets `has_error` and records a MISSING node -- so it
#   shows up as `files.n_missing_nodes`, not as `n_parse_errors`, and the count
#   of affected files is in `meta.ruby4_leading_operator_files`. Measured: 0 such
#   files in rails 8.2, 1 in a hand-written probe. The point is that it is
#   visible at all rather than silently parsed as two statements, which is what
#   a line-oriented scanner would do with it.
# * Prism has been the default Ruby parser since 3.4, but it ships no Python
#   bindings, so tree-sitter is the right tool here and shelling out to Ruby is
#   not.
# * "Chilled strings" (3.4+): a literal in a file WITHOUT a
#   `# frozen_string_literal: true` magic comment warns on mutation but is still
#   mutable, and frozen-by-default has NOT landed in 4.0. `has_frozen_literal`
#   is per-file, and the string-churn query only fires where the comment is
#   absent.
# * A heredoc body is a SIBLING of the statement that opens it, not a child. So
#   `class_eval <<~RUBY` puts Ruby source in a node that is not inside the call.
#   Those bodies are scanned separately and counted as blindness.
#
# Usage:
#   python3 codegraph_ruby.py /path/to/repo --report
#   python3 codegraph_ruby.py /path/to/repo --list
#   python3 codegraph_ruby.py --deps
# ==========================================================================

DEPS = DepSet(lang="ruby", deps=[
    TREE_SITTER,
    grammar("Ruby", "tree_sitter_ruby", "tree-sitter-ruby>=0.23",
            "0.23.1 (ABI 14 -- older than most grammars here; the 0.25 "
            "runtime accepts 13-15 so it loads, but it predates Ruby 4.0 "
            "leading-operator continuation lines)"),
])

HAZARD_CATEGORIES = (
    "sql", "exec", "deserialize", "metaprogram", "io", "net", "crypto",
    "concurrency", "mass_assign", "rails_query", "alloc", "control",
)

HAZARD_CALLS: dict[str, str] = {
    # -- exec: arbitrary code and arbitrary processes ---------------------
    "eval": "exec", "instance_eval": "exec", "class_eval": "exec",
    "module_eval": "exec", "binding.eval": "exec", "Binding.eval": "exec",
    "system": "exec", "exec": "exec", "spawn": "exec", "syscall": "exec",
    "Process.spawn": "exec", "Process.exec": "exec", "Process.fork": "exec",
    "Open3.capture2": "exec", "Open3.capture2e": "exec",
    "Open3.capture3": "exec", "Open3.popen2": "exec", "Open3.popen2e": "exec",
    "Open3.popen3": "exec", "Open3.pipeline": "exec",
    "Kernel.system": "exec", "Kernel.exec": "exec", "Kernel.spawn": "exec",
    "Kernel.open": "exec", "IO.popen": "exec", "PTY.spawn": "exec",
    "`backticks`": "exec", "%x{}": "exec",
    # -- metaprogram: where the call graph goes blind ----------------------
    "send": "metaprogram", "public_send": "metaprogram",
    "__send__": "metaprogram", "define_method": "metaprogram",
    "define_singleton_method": "metaprogram",
    "method_missing": "metaprogram", "respond_to_missing?": "metaprogram",
    "const_get": "metaprogram", "const_set": "metaprogram",
    "const_missing": "metaprogram",
    "constantize": "metaprogram", "safe_constantize": "metaprogram",
    "instance_variable_get": "metaprogram",
    "instance_variable_set": "metaprogram",
    "class_variable_get": "metaprogram", "class_variable_set": "metaprogram",
    "instance_exec": "metaprogram", "class_exec": "metaprogram",
    "method": "metaprogram", "alias_method": "metaprogram",
    "remove_method": "metaprogram", "undef_method": "metaprogram",
    "prepend": "metaprogram", "extend": "metaprogram",
    "included_modules": "metaprogram", "ancestors": "metaprogram",
    "define_attr_method": "metaprogram", "attr_internal": "metaprogram",
    "delegate_missing_to": "metaprogram", "method_defined?": "metaprogram",
    "singleton_class": "metaprogram", "Object.const_get": "metaprogram",
    "ObjectSpace.each_object": "metaprogram",
    # -- deserialize: Brakeman UnsafeReflection / Deserialize --------------
    "Marshal.load": "deserialize", "Marshal.restore": "deserialize",
    "YAML.load": "deserialize", "YAML.unsafe_load": "deserialize",
    "YAML.load_file": "deserialize", "YAML.unsafe_load_file": "deserialize",
    "Psych.load": "deserialize", "Psych.unsafe_load": "deserialize",
    "JSON.load": "deserialize", "Oj.load": "deserialize",
    "CSV.load": "deserialize", "Syck.load": "deserialize",
    # -- rails_query / sql -------------------------------------------------
    "find_by_sql": "sql", "count_by_sql": "sql", "execute": "sql",
    "exec_query": "sql", "exec_update": "sql", "exec_delete": "sql",
    "select_all": "sql", "select_values": "sql", "select_rows": "sql",
    "sanitize_sql": "sql", "sanitize_sql_array": "sql",
    "sanitize_sql_for_conditions": "sql", "quote": "sql",
    "connection.execute": "sql",
    "where": "rails_query", "where!": "rails_query", "rewhere": "rails_query",
    "order": "rails_query", "reorder": "rails_query",
    "pluck": "rails_query", "joins": "rails_query", "left_joins": "rails_query",
    "includes": "rails_query", "preload": "rails_query",
    "eager_load": "rails_query", "references": "rails_query",
    "select": "rails_query", "group": "rails_query", "having": "rails_query",
    "find_by": "rails_query", "find_each": "rails_query",
    "find_in_batches": "rails_query", "in_batches": "rails_query",
    "update_all": "rails_query", "delete_all": "rails_query",
    "destroy_all": "rails_query", "upsert_all": "rails_query",
    "insert_all": "rails_query", "exists?": "rails_query",
    "lock": "rails_query", "distinct": "rails_query", "unscoped": "rails_query",
    # -- mass_assign: Brakeman MassAssignment ------------------------------
    "create": "mass_assign", "create!": "mass_assign",
    "update": "mass_assign", "update!": "mass_assign",
    "update_attributes": "mass_assign", "update_attributes!": "mass_assign",
    "update_attribute": "mass_assign", "assign_attributes": "mass_assign",
    "attributes=": "mass_assign", "permit": "mass_assign",
    "permit!": "mass_assign", "new": "mass_assign",
    "first_or_create": "mass_assign", "find_or_create_by": "mass_assign",
    "find_or_initialize_by": "mass_assign",
    # -- io ----------------------------------------------------------------
    "File.open": "io", "File.read": "io", "File.write": "io",
    "File.readlines": "io", "File.delete": "io", "File.unlink": "io",
    "File.rename": "io", "File.exist?": "io", "File.join": "io",
    "File.expand_path": "io", "File.basename": "io", "File.dirname": "io",
    "IO.read": "io", "IO.write": "io", "IO.readlines": "io",
    "IO.binread": "io", "IO.foreach": "io",
    "Dir.glob": "io", "Dir.entries": "io", "Dir.mkdir": "io",
    "Dir.chdir": "io", "Dir.[]": "io", "Dir.children": "io",
    "FileUtils.rm": "io", "FileUtils.rm_rf": "io", "FileUtils.rm_f": "io",
    "FileUtils.cp": "io", "FileUtils.cp_r": "io", "FileUtils.mv": "io",
    "FileUtils.mkdir_p": "io", "FileUtils.chmod": "io",
    "FileUtils.touch": "io", "FileUtils.ln_s": "io",
    "Tempfile.new": "io", "Tempfile.create": "io", "Pathname.new": "io",
    "StringIO.new": "io",
    # -- net ---------------------------------------------------------------
    "Net::HTTP.get": "net", "Net::HTTP.post": "net",
    "Net::HTTP.start": "net", "Net::HTTP.new": "net",
    "Net::HTTP.get_response": "net", "Net::HTTP.post_form": "net",
    "Net::FTP.open": "net", "Net::SMTP.start": "net",
    "URI.open": "net", "URI.parse": "net", "URI.join": "net",
    "open-uri": "net", "HTTParty.get": "net", "HTTParty.post": "net",
    "Faraday.get": "net", "Faraday.post": "net", "Faraday.new": "net",
    "RestClient.get": "net", "RestClient.post": "net",
    "Excon.get": "net", "Typhoeus.get": "net", "Curl.get": "net",
    "Socket.new": "net", "TCPSocket.new": "net", "TCPServer.new": "net",
    "UDPSocket.new": "net", "OpenURI.open_uri": "net",
    # -- crypto: the weak ones, and SecureRandom as counter-evidence -------
    "Digest::MD5.hexdigest": "crypto", "Digest::MD5.digest": "crypto",
    "Digest::MD5.new": "crypto", "Digest::SHA1.hexdigest": "crypto",
    "Digest::SHA1.digest": "crypto", "Digest::SHA1.new": "crypto",
    "OpenSSL::Digest::MD5": "crypto", "OpenSSL::Digest::SHA1": "crypto",
    "OpenSSL::Cipher.new": "crypto", "OpenSSL::Cipher::Cipher.new": "crypto",
    "rand": "crypto", "srand": "crypto", "Random.rand": "crypto",
    "Random.new": "crypto", "Kernel.rand": "crypto",
    "SecureRandom.hex": "crypto", "SecureRandom.uuid": "crypto",
    "SecureRandom.random_bytes": "crypto", "SecureRandom.base64": "crypto",
    "SecureRandom.urlsafe_base64": "crypto", "SecureRandom.alphanumeric": "crypto",
    "OpenSSL::HMAC.hexdigest": "crypto", "Digest::SHA256.hexdigest": "crypto",
    "BCrypt::Password.create": "crypto",
    # -- concurrency -------------------------------------------------------
    "Thread.new": "concurrency", "Thread.start": "concurrency",
    "Thread.fork": "concurrency", "Thread.current": "concurrency",
    "Thread.kill": "concurrency", "Thread.exclusive": "concurrency",
    "Mutex.new": "concurrency", "Monitor.new": "concurrency",
    "synchronize": "concurrency", "Queue.new": "concurrency",
    "SizedQueue.new": "concurrency", "ConditionVariable.new": "concurrency",
    "Ractor.new": "concurrency", "Ractor.yield": "concurrency",
    "Ractor::Port.new": "concurrency", "Ractor.make_shareable": "concurrency",
    "Fiber.new": "concurrency", "Fiber.yield": "concurrency",
    "Timeout.timeout": "concurrency", "timeout": "concurrency",
    "Concurrent::Promise.execute": "concurrency",
    "Concurrent::Future.execute": "concurrency",
    "ThreadsWait.new": "concurrency", "sleep": "concurrency",
    # -- alloc: rubocop-performance ----------------------------------------
    "map": "alloc", "collect": "alloc", "flat_map": "alloc",
    "select": "alloc", "filter": "alloc", "reject": "alloc",
    "sort_by": "alloc", "group_by": "alloc", "each_with_object": "alloc",
    "uniq": "alloc", "flatten": "alloc", "compact": "alloc",
    "zip": "alloc", "to_a": "alloc", "dup": "alloc", "clone": "alloc",
    "deep_dup": "alloc", "Array.new": "alloc", "Hash.new": "alloc",
    "String.new": "alloc", "gsub": "alloc", "sub": "alloc",
    "split": "alloc", "join": "alloc", "format": "alloc", "sprintf": "alloc",
    # -- control: exception and process control ----------------------------
    "raise": "control", "fail": "control", "throw": "control",
    "catch": "control", "exit": "control", "exit!": "control",
    "abort": "control", "at_exit": "control", "retry": "control",
    "Process.exit": "control", "Kernel.exit": "control",
    "Kernel.abort": "control", "GC.start": "control",
    "ObjectSpace.define_finalizer": "control",
}

METAPROGRAM_APIS: dict[str, str] = {
    "send": "n_send", "public_send": "n_send", "__send__": "n_send",
    "define_method": "n_define_method",
    "define_singleton_method": "n_define_method",
    "method_missing": "n_method_missing",
    "respond_to_missing?": "n_method_missing",
    "const_missing": "n_method_missing",
    "const_get": "n_const_get", "const_set": "n_const_get",
    "constantize": "n_const_get", "safe_constantize": "n_const_get",
    "qualified_const_get": "n_const_get",
    "instance_eval": "n_instance_eval", "instance_exec": "n_instance_eval",
    "class_eval": "n_class_eval", "module_eval": "n_class_eval",
    "class_exec": "n_class_eval",
    "instance_variable_get": "n_instance_var_get",
    "instance_variable_set": "n_instance_var_get",
    "class_variable_get": "n_instance_var_get",
    "class_variable_set": "n_instance_var_get",
    "eval": "n_eval", "binding.eval": "n_eval",
    "alias_method": "n_metaprogram_other",
    "remove_method": "n_metaprogram_other",
    "undef_method": "n_metaprogram_other",
    "method": "n_metaprogram_other",
    "delegate_missing_to": "n_metaprogram_other",
    "attr_internal": "n_metaprogram_other",
}

AR_RELATION = frozenset("""
where rewhere not order reorder group having joins left_joins left_outer_joins
includes preload eager_load references select distinct limit offset lock
readonly unscope unscoped reselect regroup extending only except merge or and
none from create_with""".split())

AR_TERMINAL = frozenset("""
find find_by find_by! first first! last last! take take! pluck pick count sum
average minimum maximum ids exists? any? many? none? empty? size to_a load
find_each find_in_batches in_batches each_with_relation reload""".split())

AR_WRITE = frozenset("""
update_all delete_all destroy_all update_counters increment_counter
decrement_counter touch_all insert_all insert_all! upsert_all""".split())

AR_RAW = frozenset("""
find_by_sql count_by_sql execute exec_query exec_update exec_delete select_all
select_one select_value select_values select_rows""".split())

MASS_ASSIGN_SINKS = frozenset("""
new create create! update update! update_attributes update_attributes!
assign_attributes attributes= first_or_create first_or_create!
find_or_create_by find_or_create_by! find_or_initialize_by build
""".split())

ITER_METHODS = frozenset("""
each each_pair each_key each_value each_entry each_with_index each_with_object
each_slice each_cons each_line each_char each_byte each_index each_object
map map! collect collect! flat_map collect_concat select select! filter
filter! filter_map reject reject! detect find find_all find_each
find_in_batches in_batches partition group_by sort_by min_by max_by
minmax_by sum reduce inject count tally chunk_while slice_when take_while
drop_while times upto downto step cycle loop repeated_permutation
permutation combination product zip each_entry bsearch delete_if keep_if
all? any? none? one? each_batch traverse
""".split())

CHAIN_ALLOC = frozenset("""
map collect flat_map select filter reject sort sort_by uniq compact flatten
reverse to_a entries zip take drop first last values_at group_by partition
filter_map each_with_index each_slice each_cons chars lines bytes split
""".split())

CORE_CLASSES = frozenset("""
Object BasicObject Kernel Module Class Comparable Enumerable String Symbol
Numeric Integer Float Rational Complex Array Hash Set Range Struct Proc
Method UnboundMethod Binding Exception StandardError RuntimeError ArgumentError
TypeError NameError NoMethodError IOError SystemExit NilClass TrueClass
FalseClass Regexp MatchData Time Date DateTime Data IO File Dir Thread Mutex
Queue ConditionVariable Fiber Ractor Process Signal ObjectSpace GC Math
Random Marshal Enumerator Encoding
""".split())

CORE_RECEIVERS = frozenset("""
File Dir IO Kernel Object Module Class Marshal YAML Psych JSON Oj CSV
Net URI OpenURI HTTParty Faraday RestClient Excon Typhoeus Curl
Socket TCPSocket TCPServer UDPSocket UNIXSocket
Digest OpenSSL SecureRandom Base64 Zlib
Thread Mutex Monitor Queue SizedQueue ConditionVariable Fiber Ractor
Process Signal ObjectSpace GC Math Random Time Date DateTime Timeout
Tempfile Pathname StringIO FileUtils Etc Shellwords Open3 PTY
Struct Data Set Enumerator Comparable Enumerable Range Regexp
Rails ActiveRecord ActiveSupport ActionController ActionView ActiveJob
ActionMailer ActiveModel ActiveStorage ActionCable Arel I18n Logger
Minitest RSpec Rack Sidekiq Redis Concurrent ENV ARGF ARGV STDOUT STDERR STDIN
""".split())

CORE_METHODS = frozenset("""
new class inspect to_s to_str to_i to_f to_a to_h to_sym to_proc to_json
freeze frozen? dup clone hash eql? equal? nil? is_a? kind_of? instance_of?
respond_to? tap then yield_self itself display object_id
puts print p pp warn raise fail loop lambda proc format sprintf gets
require require_relative load autoload include extend prepend
each map select reject find detect reduce inject size length count first last
push pop shift unshift append prepend concat join split strip chomp chop
upcase downcase capitalize sub gsub match match? scan start_with? end_with?
include? index slice empty? any? all? none? one? sum min max sort sort_by
uniq compact flatten reverse zip group_by partition each_with_index
each_with_object keys values merge fetch dig store delete key? has_key?
value? has_value? call arity curry super block_given? binding caller
attr_accessor attr_reader attr_writer private public protected module_function
freeze instance_variables methods send public_send respond_to_missing?
""".split())

FROZEN_RE = re.compile(r'^#\s*frozen_string_literal:\s*true', re.M)

MAGIC_ENC_RE = re.compile(r'^#\s*(?:-\*-\s*)?(?:en)?coding[:=]', re.M)

SQL_RE = re.compile(
    r'\b(SELECT\s|INSERT\s+INTO|UPDATE\s+\w|DELETE\s+FROM|FROM\s+\w+|'
    r'WHERE\s|JOIN\s|ORDER\s+BY|GROUP\s+BY|HAVING\s|UNION\s|'
    r'CREATE\s+TABLE|DROP\s+TABLE|ALTER\s+TABLE|TRUNCATE\s)', re.I)

CONTROLLER_RE = re.compile(
    r'<\s*(?:\w+::)*(?:ApplicationController|ActionController::(?:Base|API|Metal)|'
    r'Devise::\w+Controller|InheritedResources::Base)\b')

MODEL_RE = re.compile(
    r'<\s*(?:\w+::)*(?:ApplicationRecord|ActiveRecord::Base|ActiveModel::Base)\b')

JOB_RE = re.compile(
    r'<\s*(?:\w+::)*(?:ApplicationJob|ActiveJob::Base)\b|'
    r'\binclude\s+Sidekiq::(?:Worker|Job)\b|\binclude\s+Resque\b')

AR_CALLBACKS = frozenset("""
before_validation after_validation before_save around_save after_save
before_create around_create after_create before_update around_update
after_update before_destroy around_destroy after_destroy after_commit
after_rollback after_initialize after_find after_touch
before_action after_action around_action before_filter after_filter
skip_before_action prepend_before_action append_before_action
""".split())

AR_ASSOCIATIONS = frozenset("""
belongs_to has_one has_many has_and_belongs_to_many
""".split())

MIXIN_KINDS = {"include": "include", "extend": "extend", "prepend": "prepend"}

ATTR_KINDS = {
    "attr_accessor": "n_attr_accessor", "attr_reader": "n_attr_reader",
    "attr_writer": "n_attr_writer", "attr": "n_attr_reader",
    "mattr_accessor": "n_attr_accessor", "cattr_accessor": "n_attr_accessor",
    "class_attribute": "n_attr_accessor",
    "mattr_reader": "n_attr_reader", "cattr_reader": "n_attr_reader",
    "mattr_writer": "n_attr_writer", "cattr_writer": "n_attr_writer",
    "attr_internal_accessor": "n_attr_accessor",
    "thread_mattr_accessor": "n_attr_accessor",
}

SIMPLE_RECEIVERS = frozenset((
    "constant", "scope_resolution", "identifier", "self",
    "instance_variable", "class_variable", "global_variable", "super",
))

REQUIRE_KINDS = frozenset((
    "require", "require_relative", "require_dependency", "load", "autoload",
    "autoload_at", "gem",
))

ITERATOR_METHODS = frozenset("""
each each_with_index each_with_object each_pair each_key each_value each_line
each_char each_byte each_slice each_cons each_entry reverse_each
map map! flat_map collect collect! select select! filter filter_map reject
reject! find find_all detect find_index sort_by min_by max_by group_by
partition chunk_while slice_when sum reduce inject count tally zip cycle
times upto downto step loop
all? any? none? one? take_while drop_while
delete_if keep_if
""".split())

class RubyAnalyzer(TreeSitterAnalyzer):
    LANG = "ruby"
    TARGET = "Ruby 4.0"
    EXTS = (".rb", ".rake", ".gemspec", ".ru", ".jbuilder", ".arb")
    SKIP_DIRS = {"vendor", "tmp", "log", "public", "db/migrate_backup",
                 ".bundle", "coverage", "node_modules"}
    DEPS = DEPS
    HAZARD_CATEGORIES = HAZARD_CATEGORIES
    MANIFESTS = ("Gemfile", "Gemfile.lock", ".ruby-version", "*.gemspec")

    GRAMMAR_MODULE = "tree_sitter_ruby"
    GRAMMAR_PIP = "tree-sitter-ruby>=0.23"

    # `do_block`/`block`/`lambda` are deliberately NOT symbols. Rails has more
    # than a hundred thousand blocks; making each one a symbol would bury the
    # methods and re-attribute every call inside `User.where(..).each do` to
    # the block instead of the method that owns it. They are counted, and the
    # `blocks` table carries the per-block detail the queries need.
    FUNC_KINDS = {
        "method": "method",
        "singleton_method": "method",
    }
    TYPE_KINDS = {
        "class": "class",
        "module": "module",
    }
    NAME_FIELD = {}
    DEFAULT_NAME_FIELD = "name"
    IDENT_NODES = ("identifier", "constant", "scope_resolution", "setter",
                   "operator")

    BODY_FIELD = "body"
    PARAMS_FIELD = "parameters"
    RETURN_FIELD = ""
    ELSE_FIELD = "alternative"
    # `elsif` is its own node type in this grammar rather than a nested `if`,
    # so the chain flattening in the base finds it through `alternative`.
    IF_NODES = ("if", "elsif", "unless")

    LOOP_NODES = ("while", "until", "for", "while_modifier", "until_modifier")
    BRANCH_NODES = ("if", "elsif", "unless", "if_modifier", "unless_modifier",
                    "when", "in_clause", "rescue", "conditional")
    NEST_NODES = ("if", "unless", "while", "until", "for", "case",
                  "case_match", "do_block", "block", "begin", "lambda",
                  "singleton_class")
    CALL_NODES = ("call",)
    # Ruby's call node names the callee `method`, not `function`; the receiver
    # is a separate field and `on_call` below stitches the two together.
    CALL_FUNC_FIELD = "method"
    COMMENT_NODES = ("comment",)
    STRING_NODES = ("string", "bare_string", "chained_string",
                    "delimited_symbol", "heredoc_body")
    NUMBER_NODES = ("integer", "float", "rational", "complex")
    OPERATOR_NODES = ("binary", "unary", "assignment", "operator_assignment",
                      "element_reference", "conditional", "range",
                      "scope_resolution", "splat_argument",
                      "hash_splat_argument")

    COUNTERS = {
        "return": "n_returns",
        "yield": "n_yield",
        "block_argument": "n_block_pass",
        "do_block": "n_blocks",
        "block": "n_blocks",
        "lambda": "n_lambda",
        "case": "n_switch",
        "case_match": "n_switch",
        "when": "n_cases",
        "in_clause": "n_cases",
        "conditional": "n_ternary",
        "rescue": "n_rescue",
        "rescue_modifier": "n_rescue",
        "ensure": "n_ensure",
        "retry": "n_retry",
        "instance_variable": "n_instance_var",
        "class_variable": "n_class_var",
        "global_variable": "n_global_var",
        "interpolation": "n_string_interp",
        "regex": "n_regex_lit",
        "subshell": "n_subshell",
        "assignment": "n_assign",
        "operator_assignment": "n_compound_assign",
        "element_reference": "n_subscript",
        "hash": "n_hash_lit",
        "array": "n_array_lit",
        "string_array": "n_array_lit",
        "symbol_array": "n_array_lit",
        "heredoc_body": "n_heredoc",
        "alias": "n_alias",
        "undef": "n_alias",
        "super": "n_super",
        "forward_argument": "n_forwarding",
        "forward_parameter": "n_forwarding",
        "uninterpreted": "n_end_data",
    }
    LOOP_CALL_COUNTERS = {
        "where": "query_in_loop", "find_by": "query_in_loop",
        "pluck": "query_in_loop", "count": "query_in_loop",
        "first": "query_in_loop", "execute": "query_in_loop",
        "File.open": "io_in_loop", "File.read": "io_in_loop",
        "synchronize": "lock_in_loop",
        "gsub": "regex_in_loop", "match": "regex_in_loop",
        "Regexp.new": "regex_in_loop",
    }

    EXTRA_SYMBOL_COLS = (
        # -- metaprogramming: the reason query 1 exists -------------------
        ("n_send", "INT NOT NULL DEFAULT 0"),
        ("n_define_method", "INT NOT NULL DEFAULT 0"),
        ("n_method_missing", "INT NOT NULL DEFAULT 0"),
        ("n_const_get", "INT NOT NULL DEFAULT 0"),
        ("n_instance_eval", "INT NOT NULL DEFAULT 0"),
        ("n_class_eval", "INT NOT NULL DEFAULT 0"),
        ("n_instance_var_get", "INT NOT NULL DEFAULT 0"),
        ("n_eval", "INT NOT NULL DEFAULT 0"),
        ("n_metaprogram_other", "INT NOT NULL DEFAULT 0"),
        ("n_metaprogram_total", "INT NOT NULL DEFAULT 0"),
        ("n_metaprogram_dynamic", "INT NOT NULL DEFAULT 0"),
        # -- blocks, procs, yields ----------------------------------------
        ("n_blocks", "INT NOT NULL DEFAULT 0"),
        ("n_block_pass", "INT NOT NULL DEFAULT 0"),
        ("n_block_given", "INT NOT NULL DEFAULT 0"),
        ("n_yield", "INT NOT NULL DEFAULT 0"),
        ("n_proc_new", "INT NOT NULL DEFAULT 0"),
        ("n_symbol_to_proc", "INT NOT NULL DEFAULT 0"),
        ("n_iter_blocks", "INT NOT NULL DEFAULT 0"),
        ("max_block_depth", "INT NOT NULL DEFAULT 0"),
        # -- exception handling -------------------------------------------
        ("n_rescue", "INT NOT NULL DEFAULT 0"),
        ("n_rescue_bare", "INT NOT NULL DEFAULT 0"),
        ("n_rescue_exception", "INT NOT NULL DEFAULT 0"),
        ("n_rescue_empty", "INT NOT NULL DEFAULT 0"),
        ("n_rescue_reraise", "INT NOT NULL DEFAULT 0"),
        ("n_retry", "INT NOT NULL DEFAULT 0"),
        ("n_ensure", "INT NOT NULL DEFAULT 0"),
        ("n_raise", "INT NOT NULL DEFAULT 0"),
        # -- state ---------------------------------------------------------
        ("n_class_var", "INT NOT NULL DEFAULT 0"),
        ("n_instance_var", "INT NOT NULL DEFAULT 0"),
        ("n_global_var", "INT NOT NULL DEFAULT 0"),
        ("n_class_level_ivar", "INT NOT NULL DEFAULT 0"),
        ("n_class_level_write", "INT NOT NULL DEFAULT 0"),
        ("n_attr_accessor", "INT NOT NULL DEFAULT 0"),
        ("n_attr_reader", "INT NOT NULL DEFAULT 0"),
        ("n_attr_writer", "INT NOT NULL DEFAULT 0"),
        # -- ActiveRecord ---------------------------------------------------
        ("n_ar_query", "INT NOT NULL DEFAULT 0"),
        ("n_ar_query_in_block", "INT NOT NULL DEFAULT 0"),
        ("n_ar_terminal", "INT NOT NULL DEFAULT 0"),
        ("n_ar_write", "INT NOT NULL DEFAULT 0"),
        ("n_mass_assign", "INT NOT NULL DEFAULT 0"),
        ("n_permit", "INT NOT NULL DEFAULT 0"),
        ("n_permit_bang", "INT NOT NULL DEFAULT 0"),
        ("n_params_read", "INT NOT NULL DEFAULT 0"),
        ("n_sql_interp", "INT NOT NULL DEFAULT 0"),
        ("n_sql_literal", "INT NOT NULL DEFAULT 0"),
        ("n_sql_sanitized", "INT NOT NULL DEFAULT 0"),
        # -- allocation and per-iteration cost ------------------------------
        ("n_string_interp", "INT NOT NULL DEFAULT 0"),
        ("n_str_lit_in_loop", "INT NOT NULL DEFAULT 0"),
        ("n_collection_lit_in_loop", "INT NOT NULL DEFAULT 0"),
        ("n_chain_array_alloc", "INT NOT NULL DEFAULT 0"),
        ("n_map_chain", "INT NOT NULL DEFAULT 0"),
        ("n_times_map", "INT NOT NULL DEFAULT 0"),
        ("n_range_include", "INT NOT NULL DEFAULT 0"),
        ("n_freeze", "INT NOT NULL DEFAULT 0"),
        ("n_dup_clone", "INT NOT NULL DEFAULT 0"),
        ("n_hash_lit", "INT NOT NULL DEFAULT 0"),
        ("n_array_lit", "INT NOT NULL DEFAULT 0"),
        ("n_heredoc", "INT NOT NULL DEFAULT 0"),
        ("n_subshell", "INT NOT NULL DEFAULT 0"),
        # -- structure and concurrency --------------------------------------
        ("n_monkey_patch", "INT NOT NULL DEFAULT 0"),
        ("n_mixins", "INT NOT NULL DEFAULT 0"),
        ("n_timeout", "INT NOT NULL DEFAULT 0"),
        ("n_thread_new", "INT NOT NULL DEFAULT 0"),
        ("n_mutex", "INT NOT NULL DEFAULT 0"),
        ("n_ractor", "INT NOT NULL DEFAULT 0"),
        ("n_thread_local", "INT NOT NULL DEFAULT 0"),
        ("n_alias", "INT NOT NULL DEFAULT 0"),
        ("n_super", "INT NOT NULL DEFAULT 0"),
        ("n_forwarding", "INT NOT NULL DEFAULT 0"),
        ("n_end_data", "INT NOT NULL DEFAULT 0"),
        ("n_system_call", "INT NOT NULL DEFAULT 0"),
    ("n_constantize", "INT NOT NULL DEFAULT 0"),
    ("n_html_safe", "INT NOT NULL DEFAULT 0"),
    ("n_raw_sql", "INT NOT NULL DEFAULT 0"),
    ("n_weak_hash", "INT NOT NULL DEFAULT 0"),
    ("n_weak_random", "INT NOT NULL DEFAULT 0"),
    ("n_open_call", "INT NOT NULL DEFAULT 0"),
    ("n_sleep_call", "INT NOT NULL DEFAULT 0"),
    ("n_include_in_loop", "INT NOT NULL DEFAULT 0"),
    ("n_enum_in_loop", "INT NOT NULL DEFAULT 0"),
    ("n_count_in_loop", "INT NOT NULL DEFAULT 0"),
    ("n_ar_write_in_loop", "INT NOT NULL DEFAULT 0"),
    ("n_serialize_in_loop", "INT NOT NULL DEFAULT 0"),
    ("n_elif", "INT NOT NULL DEFAULT 0"),
        ("n_external_calls", "INT NOT NULL DEFAULT 0"),
        # -- P2 pack: save/db discipline, enumerable idioms, sorbet ---------
        ("n_save_ignored", "INT NOT NULL DEFAULT 0"),
        ("n_legacy_chain", "INT NOT NULL DEFAULT 0"),
        ("has_sig", "INT NOT NULL DEFAULT 0"),
        # -- file/class role -------------------------------------------------
        ("has_frozen_literal", "INT NOT NULL DEFAULT 0"),
        ("is_controller", "INT NOT NULL DEFAULT 0"),
        ("is_model", "INT NOT NULL DEFAULT 0"),
        ("is_job", "INT NOT NULL DEFAULT 0"),
        ("is_concern", "INT NOT NULL DEFAULT 0"),
        ("is_singleton", "INT NOT NULL DEFAULT 0"),
        ("is_endless", "INT NOT NULL DEFAULT 0"),
        ("is_threaded_entry", "INT NOT NULL DEFAULT 0"),
    )

    SCHEMA_EXT = r"""
CREATE TABLE ruby_modules(
    symbol_id INT NOT NULL PRIMARY KEY REFERENCES symbols(id),
    file_id INT NOT NULL REFERENCES files(id),
    name TEXT NOT NULL,
    is_module INT NOT NULL DEFAULT 0,
    is_concern INT NOT NULL DEFAULT 0,
    has_included_block INT NOT NULL DEFAULT 0,
    has_class_methods_block INT NOT NULL DEFAULT 0,
    superclass TEXT NOT NULL DEFAULT '',
    n_mixins INT NOT NULL DEFAULT 0,
    n_defs INT NOT NULL DEFAULT 0,
    n_class_defs INT NOT NULL DEFAULT 0,
    n_class_ivars INT NOT NULL DEFAULT 0,
    n_class_vars INT NOT NULL DEFAULT 0,
    n_globals INT NOT NULL DEFAULT 0,
    reopens_core INT NOT NULL DEFAULT 0,
    line INT NOT NULL DEFAULT 0
) WITHOUT ROWID, STRICT;

CREATE TABLE mixins(
    id INTEGER PRIMARY KEY,
    host_id INT REFERENCES symbols(id),
    file_id INT NOT NULL REFERENCES files(id),
    host TEXT NOT NULL,
    mixin TEXT NOT NULL,
    mixin_short TEXT NOT NULL,
    kind TEXT NOT NULL,
    in_singleton INT NOT NULL DEFAULT 0,
    line INT NOT NULL
) STRICT;

CREATE TABLE metaprogram_sites(
    id INTEGER PRIMARY KEY,
    symbol_id INT REFERENCES symbols(id),
    file_id INT NOT NULL REFERENCES files(id),
    api TEXT NOT NULL,
    arg TEXT NOT NULL DEFAULT '',
    is_literal INT NOT NULL DEFAULT 0,
    from_params INT NOT NULL DEFAULT 0,
    from_variable INT NOT NULL DEFAULT 0,
    on_heredoc INT NOT NULL DEFAULT 0,
    in_class_body INT NOT NULL DEFAULT 0,
    loop_depth INT NOT NULL DEFAULT 0,
    line INT NOT NULL
) STRICT;

CREATE TABLE blocks(
    id INTEGER PRIMARY KEY,
    symbol_id INT REFERENCES symbols(id),
    file_id INT NOT NULL REFERENCES files(id),
    method TEXT NOT NULL,
    receiver TEXT NOT NULL DEFAULT '',
    style TEXT NOT NULL,
    is_iteration INT NOT NULL DEFAULT 0,
    depth INT NOT NULL DEFAULT 0,
    n_params INT NOT NULL DEFAULT 0,
    body_sloc INT NOT NULL DEFAULT 0,
    n_queries INT NOT NULL DEFAULT 0,
    n_allocs INT NOT NULL DEFAULT 0,
    captures_outer INT NOT NULL DEFAULT 0,
    line INT NOT NULL
) STRICT;

CREATE TABLE ar_queries(
    id INTEGER PRIMARY KEY,
    symbol_id INT REFERENCES symbols(id),
    file_id INT NOT NULL REFERENCES files(id),
    model TEXT NOT NULL DEFAULT '',
    api TEXT NOT NULL,
    build_kind TEXT NOT NULL,
    has_interpolation INT NOT NULL DEFAULT 0,
    is_sanitized INT NOT NULL DEFAULT 0,
    from_params INT NOT NULL DEFAULT 0,
    is_string_arg INT NOT NULL DEFAULT 0,
    loop_depth INT NOT NULL DEFAULT 0,
    chain_len INT NOT NULL DEFAULT 0,
    line INT NOT NULL
) STRICT;

CREATE TABLE ar_callbacks(
    id INTEGER PRIMARY KEY,
    symbol_id INT REFERENCES symbols(id),
    file_id INT NOT NULL REFERENCES files(id),
    host TEXT NOT NULL,
    hook TEXT NOT NULL,
    method TEXT NOT NULL DEFAULT '',
    is_conditional INT NOT NULL DEFAULT 0,
    is_block INT NOT NULL DEFAULT 0,
    is_association INT NOT NULL DEFAULT 0,
    issues_query INT NOT NULL DEFAULT 0,
    target_id INT REFERENCES symbols(id),
    line INT NOT NULL
) STRICT;

CREATE TABLE monkey_patches(
    id INTEGER PRIMARY KEY,
    symbol_id INT REFERENCES symbols(id),
    method_id INT REFERENCES symbols(id),
    file_id INT NOT NULL REFERENCES files(id),
    core_class TEXT NOT NULL,
    method TEXT NOT NULL,
    is_operator INT NOT NULL DEFAULT 0,
    is_singleton INT NOT NULL DEFAULT 0,
    line INT NOT NULL
) STRICT;
"""

    INDEX_EXT = r"""
CREATE INDEX idx_mix_host ON mixins(host_id, mixin_short);
CREATE INDEX idx_mix_short ON mixins(mixin_short, kind);
CREATE INDEX idx_meta_sym ON metaprogram_sites(symbol_id, api);
CREATE INDEX idx_meta_api ON metaprogram_sites(api, from_params DESC);
CREATE INDEX idx_meta_taint ON metaprogram_sites(from_params) WHERE from_params=1;
CREATE INDEX idx_blk_sym ON blocks(symbol_id, is_iteration);
CREATE INDEX idx_blk_iter ON blocks(method, depth DESC) WHERE is_iteration=1;
CREATE INDEX idx_arq_sym ON ar_queries(symbol_id, build_kind);
CREATE INDEX idx_arq_model ON ar_queries(model, api);
CREATE INDEX idx_arq_loop ON ar_queries(symbol_id) WHERE loop_depth > 0;
CREATE INDEX idx_arq_interp ON ar_queries(api) WHERE has_interpolation=1;
CREATE INDEX idx_cb_host ON ar_callbacks(host, hook);
CREATE INDEX idx_cb_query ON ar_callbacks(method) WHERE issues_query=1;
CREATE INDEX idx_mp_class ON monkey_patches(core_class, method);
CREATE INDEX idx_rm_concern ON ruby_modules(is_concern, name);
CREATE INDEX idx_fn_meta ON symbols(n_metaprogram_total DESC, name)
    WHERE n_metaprogram_total > 0;
CREATE INDEX idx_fn_ctrl ON symbols(name, file_id) WHERE is_controller=1;
CREATE INDEX idx_fn_thr ON symbols(name, file_id) WHERE is_threaded_entry=1;
"""

    VIEW_EXT = r"""
CREATE VIEW v_blind AS
SELECT s.id, s.name, s.qual_name, f.path, m.name AS module,
    s.n_calls, s.n_unresolved_calls, s.n_external_calls,
    s.n_metaprogram_total AS meta, s.n_send, s.n_define_method,
    s.n_method_missing, s.n_const_get, s.n_class_eval,
    s.n_metaprogram_total + s.n_unresolved_calls AS blind_total,
    f.path || ':' || s.line_start AS at
FROM symbols s
JOIN files f ON f.id = s.file_id
LEFT JOIN modules m ON m.id = s.module_id
WHERE s.kind = 'method';

CREATE VIEW v_ar AS
SELECT q.id, q.model, q.api, q.build_kind, q.has_interpolation,
    q.is_sanitized, q.from_params, q.loop_depth, s.name AS in_method,
    s.is_controller, s.is_model, f.path || ':' || q.line AS at
FROM ar_queries q
JOIN symbols s ON s.id = q.symbol_id
JOIN files f ON f.id = q.file_id;

CREATE VIEW v_concern AS
SELECT r.name, r.is_concern, r.has_included_block, r.n_defs, r.n_mixins,
    (SELECT COUNT(*) FROM mixins x WHERE x.mixin_short = r.name) AS included_by,
    f.path || ':' || r.line AS at
FROM ruby_modules r JOIN files f ON f.id = r.file_id
WHERE r.is_module = 1;
"""

    MATERIALIZE_EXT = r"""
UPDATE symbols AS s SET n_unique_calls = x.c FROM
    (SELECT caller_id AS id, COUNT(*) AS c FROM edges GROUP BY caller_id) AS x
    WHERE x.id = s.id;

-- blocks.n_queries was declared but never populated -- every block read as
-- query-free, which silently zeroed find-each-missed. Count AR queries whose
-- line falls inside the block's span (line..line+body_sloc), same symbol.
UPDATE blocks AS b SET n_queries = x.c FROM
    (SELECT b2.id AS id, COUNT(*) AS c
     FROM ar_queries aq JOIN blocks b2 ON b2.symbol_id = aq.symbol_id
     WHERE aq.line BETWEEN b2.line AND b2.line + b2.body_sloc
     GROUP BY b2.id) AS x WHERE x.id = b.id;

UPDATE symbols AS s SET n_ar_query_in_block = x.c FROM
    (SELECT symbol_id AS id, COUNT(*) AS c FROM ar_queries
     WHERE loop_depth > 0 GROUP BY symbol_id) AS x WHERE x.id = s.id;

UPDATE symbols AS s SET n_metaprogram_dynamic = x.c FROM
    (SELECT symbol_id AS id, COUNT(*) AS c FROM metaprogram_sites
     WHERE is_literal = 0 GROUP BY symbol_id) AS x WHERE x.id = s.id;

UPDATE symbols AS s SET n_mixins = x.c FROM
    (SELECT host_id AS id, COUNT(*) AS c FROM mixins
     WHERE host_id IS NOT NULL GROUP BY host_id) AS x WHERE x.id = s.id;

-- attr_accessor/reader/writer macros record a FIELD per declared name with
-- the macro base in the `type` column ('attr_accessor'/'attr_reader'/
-- 'attr_writer', from the ATTR_KINDS map); the n_attr_* columns are the
-- per-class totals materialized from those rows, so the attr-coupling query
-- can rank classes without re-deriving the macro spelling.
UPDATE symbols AS s SET n_attr_accessor = x.c FROM
    (SELECT symbol_id AS id, COUNT(*) AS c FROM fields
     WHERE type='attr_accessor' GROUP BY symbol_id) AS x WHERE x.id = s.id;

UPDATE symbols AS s SET n_attr_reader = x.c FROM
    (SELECT symbol_id AS id, COUNT(*) AS c FROM fields
     WHERE type='attr_reader' GROUP BY symbol_id) AS x WHERE x.id = s.id;

UPDATE symbols AS s SET n_attr_writer = x.c FROM
    (SELECT symbol_id AS id, COUNT(*) AS c FROM fields
     WHERE type='attr_writer' GROUP BY symbol_id) AS x WHERE x.id = s.id;

-- A callback names a method by symbol; the edge from the macro to the method
-- does not exist in the tree, so it is stitched here by name within the file.
UPDATE ar_callbacks AS c SET target_id = (
    SELECT s.id FROM symbols s
    WHERE s.file_id = c.file_id AND s.name = c.method AND s.kind = 'method'
    ORDER BY s.line_start LIMIT 1)
WHERE c.method <> '';

UPDATE ar_callbacks AS c SET issues_query = 1
WHERE c.target_id IS NOT NULL AND EXISTS (
    SELECT 1 FROM symbols s WHERE s.id = c.target_id
      AND (s.n_ar_query > 0 OR s.n_rails_query > 0 OR s.n_sql > 0));

UPDATE monkey_patches AS p SET method_id = (
    SELECT s.id FROM symbols s
    WHERE s.file_id = p.file_id AND s.name = p.method
      AND s.line_start = p.line LIMIT 1)
WHERE p.method_id IS NULL;

-- A method is a threaded entry if it spawns, or if the framework runs it on a
-- thread pool: Puma serves controller actions on threads and every job backend
-- worth using runs perform on a worker thread.
UPDATE symbols SET is_threaded_entry = 1
WHERE n_thread_new > 0 OR n_ractor > 0 OR is_job = 1
   OR (is_controller = 1 AND is_public = 1 AND kind = 'method');
"""

    RISK_SQL = (
        "cyclomatic*2 + cognitive + max_nesting*4"
        " + n_eval*30 + n_exec*25 + n_deserialize*20"
        " + n_metaprogram_dynamic*10 + n_metaprogram_total*3"
        " + n_sql_interp*30 + n_permit_bang*20"
        " + (CASE WHEN n_params_read>0 AND n_mass_assign>0 AND n_permit=0"
        "    THEN 25 ELSE 0 END)"
        " + n_ar_query_in_block*12 + query_in_loop*10"
        " + n_rescue_bare*6 + n_rescue_exception*10 + n_rescue_empty*12"
        " + n_monkey_patch*8 + n_timeout*8"
        " + n_class_level_write*10 + n_global_var*4"
        " + n_thread_new*5 + n_crypto*3"
        " + (CASE WHEN is_recursive THEN 10 ELSE 0 END)"
    )

    def __init__(self) -> None:
        super().__init__()
        self.ruby_version = ""
        self.rails_version = ""
        self.n_ruby4_leading_op = 0
        # per-file state, reset in parse_file
        self._frozen = 0
        self._role = (0, 0, 0)
        self._vis: list[tuple[int, int, str]] = []
        # produced by function_flags, drained by function_extra
        self._pend_blocks: list[tuple] = []
        self._pend_meta: list[tuple] = []
        self._pend_ar: list[tuple] = []

    # -- per-file setup ----------------------------------------------------
    def parse_file(self, rec: FileRec, db: sqlite3.Connection,
                   bufs: Buffers) -> None:
        """Classify the file before walking it.

        The Rails role of a file decides how several counters are read -- a
        `params` read in a controller is a request-tainted source, the same
        read in a rake task is not -- so it is settled once, from the path AND
        from the superclass, before any symbol is emitted.
        """
        head = rec.text[:800]
        self._frozen = 1 if FROZEN_RE.search(head) else 0
        rel = rec.rel.replace(os.sep, "/")
        self._role = (
            int("app/controllers/" in rel or bool(CONTROLLER_RE.search(rec.text))),
            int("app/models/" in rel or bool(MODEL_RE.search(rec.text))),
            int("app/jobs/" in rel or "app/workers/" in rel
                or bool(JOB_RE.search(rec.text))),
        )
        self._vis = []
        super().parse_file(rec, db, bufs)

    # -- naming ------------------------------------------------------------
    def node_name(self, node: Any, rec: FileRec) -> str:
        """Method names include `?`, `!`, `=` and the operator forms.

        `def name=` parses as a `setter` wrapping an identifier and `def <=>`
        as an `operator`, so taking the identifier child would silently rename
        `name=` to `name` and collapse a writer onto its reader.
        """
        n = node.child_by_field_name("name")
        if n is not None:
            return text_of(n, rec.data).strip()
        for c in node.named_children:
            if c.type in self.IDENT_NODES:
                return text_of(c, rec.data).strip()
        return ""

    def return_type_of(self, node: Any, rec: FileRec) -> str:
        """Ruby declares no return types. Saying so beats guessing one."""
        return ""

    def signature_of(self, node: Any, rec: FileRec) -> str:
        params = node.child_by_field_name("parameters")
        end = params.end_byte if params is not None else None
        if end is None:
            body = node.child_by_field_name("body")
            end = body.start_byte if body is not None else node.end_byte
        return rec.data[node.start_byte:end].decode("utf-8", "replace").strip()

    def visibility_of(self, node: Any, rec: FileRec) -> str:
        """Ruby visibility is positional, not a keyword on the def.

        A bare `private` in a class body governs every def after it, so the
        ranges are recorded when the class is emitted (which happens first)
        and looked up here. `private def foo` is the other spelling and is
        caught through the parent chain.
        """
        if node.type == "singleton_method":
            return "public"
        parent = node.parent
        if parent is not None and parent.type == "argument_list":
            gp = parent.parent
            if gp is not None and gp.type == "call":
                m = gp.child_by_field_name("method")
                if m is not None:
                    txt = text_of(m, rec.data)
                    if txt in ("private", "protected", "private_class_method"):
                        return "private" if txt != "protected" else "protected"
        line = node.start_point[0] + 1
        vis = "public"
        for lo, hi, v in self._vis:
            if lo <= line <= hi:
                vis = v
        return vis

    # -- flags -------------------------------------------------------------
    def function_flags(self, node: Any, rec: FileRec,
                       scope: Scope) -> dict[str, Any]:
        name = self.node_name(node, rec)
        body = node.child_by_field_name("body")
        vis = self.visibility_of(node, rec)
        singleton = 1 if (node.type == "singleton_method"
                          or _in_singleton_class(node)) else 0
        # sorbet sig{} sits directly above the def as a prev sibling call.
        _prv = node.prev_sibling
        has_sig = 0
        if _prv is not None and _prv.type == "call":
            _pt = text_of(_prv, rec.data).lstrip()
            if _pt.startswith("sig") and _pt.startswith("signature") is False:
                has_sig = 1
        ctrl, model, job = self._role
        out: dict[str, Any] = {
            "is_public": int(vis == "public"),
            "is_static": singleton,
            "is_singleton": singleton,
            "is_endless": int(body is not None
                              and body.type not in ("body_statement", "do")),
            "is_test": int(name.startswith("test_") or name.startswith("test ")
                           or rec.is_test),
            "is_generator": int(_has_yield(node)),
            "is_entrypoint": int(name in ("perform", "perform_now", "call",
                                          "run", "execute", "main")
                                 or (ctrl and vis == "public")),
            "is_controller": ctrl,
            "is_model": model,
            "is_job": job,
            "has_frozen_literal": self._frozen,
            "has_sig": has_sig,
            "is_abstract": int(_raises_not_implemented(node, rec.data)),
        }
        out.update(self._scan_body(node, rec, vis))
        # DEFINING method_missing is what blinds the graph, not calling it: a
        # class with method_missing answers to names that appear nowhere, so
        # every "nothing calls this" claim about its callers is void. Counting
        # only the call sites found 4 of these in Rails; counting the
        # definitions finds the ones that matter.
        if name in ("method_missing", "respond_to_missing?", "const_missing"):
            out["n_method_missing"] = out.get("n_method_missing", 0) + 1
            out["n_metaprogram_total"] = out.get("n_metaprogram_total", 0) + 1
            self._pend_meta.append(
                (rec.fid, "def " + name, "", 0, 0, 1, 0, 0, 0,
                 node.start_point[0] + 1))
        return out

    def type_flags(self, node: Any, rec: FileRec,
                   scope: Scope) -> dict[str, Any]:
        name = self.node_name(node, rec)
        short = name.rsplit("::", 1)[-1]
        ctrl, model, job = self._role
        sup = node.child_by_field_name("superclass")
        suptxt = text_of(sup, rec.data).lstrip("< ").strip() if sup is not None else ""
        meta = self._scan_class_meta(node, rec)
        out = {
            "is_public": 1,
            "is_controller": int(ctrl or "Controller" in short),
            "is_model": model,
            "is_job": job,
            "has_frozen_literal": self._frozen,
            "n_monkey_patch": int(_reopens_core(name, short, scope)),
            "is_concern": int("ActiveSupport::Concern"
                              in text_of(node, rec.data)[:2000]),
            "is_abstract": int("abstract_class" in text_of(node, rec.data)[:2000]),
        }
        out.update(meta)
        return out

    def _scan_class_meta(self, node: Any, rec: FileRec) -> dict[str, int]:
        """Metaprogramming in a CLASS BODY, which is where Rails does most of it.

        `%w[get post].each { |m| define_method(m) { ... } }` at class level
        defines methods that no `def` anywhere accounts for. Scanning only
        method bodies found 149 define_method sites in Rails; the class bodies
        hold roughly as many again. Method, nested class and nested module
        subtrees are pruned because their own hooks already cover them.
        """
        self._pend_meta = []
        self._pend_ar = []
        self._pend_blocks = []
        body = node.child_by_field_name("body")
        if body is None:
            return {}
        src = rec.data
        counts: dict[str, int] = {}

        def bump(k: str, n: int = 1) -> None:
            counts[k] = counts.get(k, 0) + n

        stack = list(body.named_children)
        while stack:
            n = stack.pop()
            t = n.type
            if t in ("method", "singleton_method", "class", "module"):
                continue                     # owned by another hook
            if t == "call":
                mn = n.child_by_field_name("method")
                if mn is not None:
                    meth = text_of(mn, src)
                    if METAPROGRAM_APIS.get(meth) is not None:
                        bump(METAPROGRAM_APIS[meth])
                        bump("n_metaprogram_total")
                    self._call_detail(n, meth, src, rec, 0, True, bump)
            stack.extend(n.named_children)
        return counts

    # -- calls -------------------------------------------------------------
    def on_call(self, node: Any, src: bytes, st: BodyStats,
                loop_depth: int, nest: int) -> None:
        """Build `receiver.method` from Ruby's two-field call node.

        A chained call's receiver is another call whose text can be a whole
        screen, so only a simple receiver is used verbatim; a chain
        contributes just the previous link's method name. That is enough for
        hazard matching, which keys on the last segment.
        """
        st.bump("n_calls")
        if loop_depth:
            st.bump("call_in_loop")
        m = node.child_by_field_name("method")
        if m is None:
            st.bump("n_dynamic_calls")
            st.calls.append(("", node.start_point[0] + 1, True, bool(loop_depth)))
            return
        meth = text_of(m, src).strip()
        recv = node.child_by_field_name("receiver")
        full = meth
        if recv is not None:
            rt = recv.type
            if rt in SIMPLE_RECEIVERS:
                full = text_of(recv, src).strip()[:80] + "." + meth
            elif rt == "call":
                inner = recv.child_by_field_name("method")
                if inner is not None:
                    full = text_of(inner, src).strip()[:40] + "." + meth
            elif rt == "string":
                full = "String#" + meth
        line = node.start_point[0] + 1

        # -- facts RuboCop (Performance/, Security/) and Brakeman check.
        # Recorded as counts; the verdict is a join away, not a rule here.
        if meth in ("system", "exec", "spawn", "syscall"):
            st.bump("n_system_call")
        elif meth in ("constantize", "safe_constantize"):
            st.bump("n_constantize")
        elif meth in ("html_safe", "raw"):
            st.bump("n_html_safe")
        elif meth in ("find_by_sql", "execute", "select_all", "select_values"):
            st.bump("n_raw_sql")
        elif meth in ("md5", "sha1"):
            st.bump("n_weak_hash")
        elif meth in ("rand", "srand"):
            st.bump("n_weak_random")
        elif meth == "open":
            st.bump("n_open_call")
        elif meth == "sleep":
            st.bump("n_sleep_call")
        if loop_depth:
            if meth == "include?":
                st.bump("n_include_in_loop")
            elif meth in ("map", "select", "reject", "each", "detect"):
                st.bump("n_enum_in_loop")
            elif meth in ("count", "size", "length"):
                st.bump("n_count_in_loop")
            elif meth in ("save", "save!", "update", "create", "destroy"):
                st.bump("n_ar_write_in_loop")
            elif meth in ("to_json", "to_yaml", "to_s"):
                st.bump("n_serialize_in_loop")

        col = METAPROGRAM_APIS.get(meth) or METAPROGRAM_APIS.get(full)
        if col is not None:
            st.bump(col)
            st.bump("n_metaprogram_total")
        if meth == "block_given?":
            st.bump("n_block_given")
        elif meth == "raise" or meth == "fail":
            st.bump("n_raise")
        elif meth == "freeze":
            st.bump("n_freeze")
        elif meth in ("dup", "clone"):
            st.bump("n_dup_clone")
        elif full == "Proc.new":
            st.bump("n_proc_new")
        elif meth in ("lambda", "proc") and recv is None:
            st.bump("n_lambda")
        elif full == "Thread.new" or full == "Thread.start":
            st.bump("n_thread_new")
        elif full in ("Mutex.new", "Monitor.new"):
            st.bump("n_mutex")
        elif full.startswith("Ractor."):
            st.bump("n_ractor")
        elif full == "Thread.current":
            st.bump("n_thread_local")
        elif full == "Timeout.timeout" or (meth == "timeout" and recv is None):
            st.bump("n_timeout")
        elif meth == "permit":
            st.bump("n_permit")
        elif meth == "permit!":
            st.bump("n_permit")
            st.bump("n_permit_bang")
        elif meth.startswith("sanitize_sql"):
            st.bump("n_sql_sanitized")
        if meth in MASS_ASSIGN_SINKS:
            st.bump("n_mass_assign")
        if meth in AR_RELATION or meth in AR_TERMINAL or meth in AR_WRITE \
                or meth in AR_RAW:
            st.bump("n_ar_query")
            if meth in AR_TERMINAL:
                st.bump("n_ar_terminal")
            elif meth in AR_WRITE:
                st.bump("n_ar_write")

        # `send(:name)` is a call the graph cannot follow. Marking it dynamic
        # keeps it out of the edge list -- inventing an edge to whatever
        # method happens to share that name would be a lie the queries then
        # reason over -- while still producing a hazard row.
        dynamic = meth in ("send", "public_send", "__send__", "eval",
                           "instance_eval", "class_eval", "module_eval",
                           "instance_exec", "define_method", "const_get",
                           "constantize", "safe_constantize", "method")
        st.calls.append((full[:200], line, dynamic, bool(loop_depth)))
        if dynamic:
            st.bump("n_dynamic_calls")
        if loop_depth:
            base = full.rsplit(".", 1)[-1]
            for needle, colname in self.LOOP_CALL_COUNTERS.items():
                if needle == base or needle == full:
                    st.bump(colname)

    def on_string(self, node: Any, text: str, src: bytes, st: BodyStats,
                  loop_depth: int) -> None:
        # NOTE: `n_str_lit_in_loop` is deliberately NOT counted here. The
        # base's loop_depth only sees while/until/for, and Ruby barely uses
        # them -- across all of Rails those three account for a max_loop_depth
        # sum of 204 against 3,936 iteration blocks. Counting string churn on
        # this signal found 55 sites in a codebase that has thousands. The
        # count lives in `_scan_body`, which tracks BLOCK depth, because in
        # Ruby the loop is the block.
        if not SQL_RE.search(text):
            return
        st.bump("n_sql_literal")
        interpolated = any(c.type == "interpolation" for c in node.named_children)
        if interpolated:
            st.bump("n_sql_interp")
        if loop_depth:
            st.bump("query_in_loop")

    def on_node(self, node: Any, src: bytes, st: BodyStats,
                loop_depth: int, nest: int) -> None:
        t = node.type
        if t == "rescue":
            exc = node.child_by_field_name("exceptions")
            body = node.child_by_field_name("body")
            if exc is None:
                st.bump("n_rescue_bare")
            elif "Exception" in text_of(exc, src):
                st.bump("n_rescue_exception")
            if body is None or not body.named_children:
                st.bump("n_rescue_empty")
            elif _body_is_reraise(body, src):
                st.bump("n_rescue_reraise")
        elif t == "rescue_modifier":
            h = node.child_by_field_name("handler")
            st.bump("n_rescue_bare")
            if h is not None and h.type == "nil":
                st.bump("n_rescue_empty")
        elif t == "block_argument":
            kid = node.named_children[0] if node.named_children else None
            if kid is not None and kid.type in ("simple_symbol",
                                                "delimited_symbol"):
                st.bump("n_symbol_to_proc")
        elif t == "element_reference":
            obj = node.child_by_field_name("object")
            if obj is not None and text_of(obj, src) == "params":
                st.bump("n_params_read")
        elif t == "identifier":
            if node.end_byte - node.start_byte <= 6:
                txt = text_of(node, src)
                if txt == "params":
                    st.bump("n_params_read")
                elif txt == "raise" or txt == "fail":
                    st.bump("n_raise")
                elif txt == "retry":
                    st.bump("n_retry")
        elif t == "subshell":
            # Backticks and %x{} are `exec` with none of exec's visibility.
            # Marked dynamic so it produces a hazard but never an edge.
            st.calls.append(("`backticks`", node.start_point[0] + 1, True,
                             bool(loop_depth)))
        elif t == "heredoc_body":
            txt = text_of(node, src)
            if SQL_RE.search(txt):
                st.bump("n_sql_literal")
                if "#{" in txt:
                    st.bump("n_sql_interp")
        elif t == "assignment" or t == "operator_assignment":
            left = node.child_by_field_name("left")
            if left is not None and left.type in ("class_variable",
                                                  "global_variable"):
                st.bump("n_class_level_write")

    # -- hazards and resolution -------------------------------------------
    def hazard_of(self, callee: str) -> Optional[tuple[str, str]]:
        cat = HAZARD_CALLS.get(callee)
        if cat is not None:
            return callee, cat
        base = callee.rsplit(".", 1)[-1]
        cat = HAZARD_CALLS.get(base)
        if cat is not None:
            return "*." + base, cat
        head = callee.split(".", 1)[0]
        if head in ("Digest", "OpenSSL") or callee.startswith("Digest::"):
            return callee.rsplit(".", 1)[0], "crypto"
        return None

    def extra_loop_ids(self, body: Any, rec: FileRec) -> set[int]:
        """Blocks attached to an iterator, which is how Ruby actually loops.

        Rails uses `while`/`until`/`for` 122 times across 3,461 files. It
        iterates constantly -- with blocks. Without this every Ruby query that
        ranks by loop depth ranks by zero.
        """
        out: set[int] = set()
        src = rec.data
        for n in walk(body):
            if n.type not in ("do_block", "block"):
                continue
            call = n.parent
            if call is None or call.type != "call":
                continue
            meth = call.child_by_field_name("method")
            if meth is None:
                continue
            if text_of(meth, src).strip() in ITERATOR_METHODS:
                out.add(n.id)
        return out

    def normalise_callee(self, raw: str) -> str:
        """`Foo.new` is a call to Foo, and `Foo::Bar.new` to Bar.

        Ruby has no `new` keyword: allocation is an ordinary method call on the
        class object. Resolved literally, `Foo.new` looks for a method called
        `new`, finds none, and lands in unresolved_calls -- 7,774 times in
        Rails, which is most of the object graph. Mapping it to the class is
        what makes "who instantiates this" answerable at all.
        """
        n = raw.strip()
        if n.endswith(".new"):
            recv = n[:-4]
            # `Foo::Bar.new` -> Bar; a lowercase receiver is a variable, not a
            # class, and resolving it would invent an edge.
            last = recv.rsplit("::", 1)[-1].rsplit(".", 1)[-1]
            if last[:1].isupper():
                return last
        return n

    def is_external(self, name: str, base: str, fid: int) -> bool:
        """Distinguish 'left the tree by design' from 'we lost it'.

        Ruby has no import that binds a name, so there is no manifest to
        consult -- only knowledge of the core library and the framework. What
        is left over after this is genuine blindness and is counted as such.
        """
        head = name.split(".", 1)[0].split("::", 1)[0]
        if head in CORE_RECEIVERS:
            return True
        if base in CORE_METHODS and "." not in name:
            return True
        if base in CORE_METHODS and head and head[0].islower():
            return True
        if head.startswith("@") or head == "self":
            return False
        return False

    # -- imports -----------------------------------------------------------
    def parse_imports(self, root: Any, rec: FileRec, bufs: Buffers) -> None:
        src = rec.data
        for n in walk(root):
            if n.type != "call":
                continue
            m = n.child_by_field_name("method")
            if m is None:
                continue
            kind = text_of(m, src)
            if kind not in REQUIRE_KINDS:
                continue
            args = n.child_by_field_name("arguments")
            if args is None or not args.named_children:
                continue
            a0 = args.named_children[0]
            target = text_of(a0, src).strip("\"'`:")
            bufs.imports.append(
                (rec.fid, target[:300], None, None, kind,
                 n.start_point[0] + 1,
                 int(kind in ("require", "gem")),
                 int(kind == "require_relative"), 0, 0,
                 int(kind == "autoload"), len(args.named_children)))

    def parse_file_extra(self, root: Any, rec: FileRec,
                         db: sqlite3.Connection, bufs: Buffers) -> None:
        """Count what the grammar cannot reach into.

        A heredoc body is a sibling of the statement that opens it, so
        `class_eval <<~RUBY ... RUBY` puts real Ruby source in a node that is
        not part of the call and is never parsed as code. Those bodies are the
        single largest source of invisible method definitions in Rails, and
        they are counted here rather than ignored.
        """
        if root.has_error and re.search(r'^\s*(?:&&|\|\||and\b|or\b)',
                                        rec.text, re.M):
            self.n_ruby4_leading_op += 1

    def parse_manifests(self, root: str, db: sqlite3.Connection) -> None:
        for name, pat, key in (
            (".ruby-version", r'(\d+\.\d+(?:\.\d+)?)', "ruby_version"),
            ("Gemfile.lock", r'^\s+rails \((\d+\.\d+\.\d+)', "rails_version"),
            ("Gemfile", r'ruby\s+["\'](\d+\.\d+[.\d]*)', "ruby_version"),
        ):
            path = os.path.join(root, name)
            if not os.path.isfile(path):
                continue
            try:
                text = open(path, encoding="utf-8", errors="replace").read()
            except OSError:
                continue
            m = re.search(pat, text, re.M)
            if m:
                if key == "ruby_version" and not self.ruby_version:
                    self.ruby_version = m.group(1)
                elif key == "rails_version":
                    self.rails_version = m.group(1)
        meta_rows = (
            ("ruby_version", self.ruby_version or "not declared"),
            ("rails_version", self.rails_version or "not a Rails app"),
            ("frozen_string_default",
             "NO -- literals are 'chilled' (warn on mutate) in files without "
             "the magic comment; frozen-by-default has not landed in 4.0"),
            # Ruby source handed to class_eval/instance_eval as a heredoc.
            # Every one of these defines methods in text that is never parsed
            # as code, so it is pure, countable blindness.
            ("ruby_source_in_heredoc_evals",
             str(db.execute("SELECT COUNT(*) FROM metaprogram_sites "
                            "WHERE on_heredoc=1").fetchone()[0])),
            ("ruby4_leading_operator_files", str(self.n_ruby4_leading_op)),
        )
        db.executemany("INSERT OR REPLACE INTO meta(key,value) VALUES(?,?)",
                       meta_rows)

    # -- params ------------------------------------------------------------
    def emit_params(self, node: Any, rec: FileRec, sid: int,
                    bufs: Buffers) -> None:
        params = node.child_by_field_name("parameters")
        if params is None:
            return
        for pos, p in enumerate(params.named_children):
            t = p.type
            nm = p.child_by_field_name("name")
            name = text_of(nm, rec.data).strip() if nm is not None \
                else text_of(p, rec.data).strip()
            dv = p.child_by_field_name("value")
            bufs.params.append(
                (sid, pos, name[:120] or "(anonymous)", t,
                 text_of(dv, rec.data)[:120] if dv is not None else None,
                 int(t in ("optional_parameter", "keyword_parameter")
                     and dv is not None),
                 int(t in ("splat_parameter", "hash_splat_parameter",
                           "forward_parameter")),
                 0, 0, 0, 0, 1, 0))

    # -- the second walk ---------------------------------------------------
    def _scan_body(self, node: Any, rec: FileRec,
                   vis: str) -> dict[str, Any]:
        """Block, AR and metaprogram detail the flat COUNTERS pass cannot see.

        Everything here needs the shape of a subtree, not a node type: whether
        a block is an iteration (its METHOD decides, not its syntax), how deep
        the iteration nesting goes, which model a query chain started from,
        and whether a `send` argument came from `params`. One cursor walk
        computes all of it; the rows are stashed and drained by
        `function_extra`, which is the first hook that knows the symbol id.
        """
        self._pend_blocks = []
        self._pend_meta = []
        self._pend_ar = []
        body = node.child_by_field_name("body")
        if body is None:
            return {}
        src = rec.data
        counts: dict[str, int] = {}
        def bump(k: str, n: int = 1) -> None:
            counts[k] = counts.get(k, 0) + n

        singleton = node.type == "singleton_method" or _in_singleton_class(node)
        cursor = body.walk()
        depth = 0
        iter_stack: list[int] = []          # exit depths of iteration blocks
        max_block = 0
        while True:
            n = cursor.node
            t = n.type
            while iter_stack and iter_stack[-1] >= depth:
                iter_stack.pop()
            idepth = len(iter_stack)

            if t == "do_block" or t == "block":
                parent = n.parent
                meth = ""
                recv = ""
                if parent is not None and parent.type == "call":
                    mn = parent.child_by_field_name("method")
                    meth = text_of(mn, src) if mn is not None else ""
                    rn = parent.child_by_field_name("receiver")
                    if rn is not None and rn.type in SIMPLE_RECEIVERS:
                        recv = text_of(rn, src)[:60]
                    elif rn is not None and rn.type == "call":
                        # `User.all.each` -- the receiver is itself a call
                        # chain; record its text so all-table iteration is
                        # visible to find-each-missed.
                        recv = text_of(rn, src)[:60]
                is_iter = meth in ITER_METHODS
                if is_iter:
                    iter_stack.append(depth)
                    max_block = max(max_block, len(iter_stack))
                    bump("n_iter_blocks")
                ps = n.child_by_field_name("parameters")
                self._pend_blocks.append(
                    (rec.fid, meth[:60], recv,
                     "do_end" if t == "do_block" else "brace",
                     int(is_iter), idepth + (1 if is_iter else 0),
                     len(ps.named_children) if ps is not None else 0,
                     n.end_point[0] - n.start_point[0] + 1,
                     0, 0, 0, n.start_point[0] + 1))
            elif t == "call":
                mn = n.child_by_field_name("method")
                if mn is not None:
                    meth = text_of(mn, src)
                    self._call_detail(n, meth, src, rec, idepth, singleton,
                                      bump)
            elif t in ("array", "hash", "string_array", "symbol_array"):
                if idepth:
                    bump("n_collection_lit_in_loop")
            elif t == "string" or t == "heredoc_body":
                # Allocated afresh on every trip round the block unless the
                # file carries the frozen_string_literal comment.
                if idepth:
                    bump("n_str_lit_in_loop")
            elif t == "instance_variable" and singleton:
                bump("n_class_level_ivar")

            if cursor.goto_first_child():
                depth += 1
                continue
            while not cursor.goto_next_sibling():
                if not cursor.goto_parent():
                    counts["max_block_depth"] = max_block
                    return counts
                depth -= 1

    def _call_detail(self, n: Any, meth: str, src: bytes, rec: FileRec,
                     idepth: int, singleton: bool, bump: Any) -> None:
        """One call, examined for AR shape, metaprogram taint and alloc cost."""
        recv = n.child_by_field_name("receiver")
        args = n.child_by_field_name("arguments")
        line = n.start_point[0] + 1

        # -- chained array allocation (Performance/ChainArrayAllocation)
        if meth in CHAIN_ALLOC and recv is not None and recv.type == "call":
            inner = recv.child_by_field_name("method")
            if inner is not None and text_of(inner, src) in CHAIN_ALLOC:
                bump("n_chain_array_alloc")
                if meth in ("map", "collect") or text_of(inner, src) in (
                        "map", "collect"):
                    bump("n_map_chain")
        # -- Performance/TimesMap
        if meth in ("map", "collect") and recv is not None and recv.type == "call":
            inner = recv.child_by_field_name("method")
            if inner is not None and text_of(inner, src) == "times":
                bump("n_times_map")
        # -- Performance/RangeInclude: cover? is O(1), include? walks
        if meth == "include?" and recv is not None:
            rt = recv.type
            if rt == "range" or (rt == "parenthesized_statements"
                                 and any(c.type == "range"
                                         for c in recv.named_children)):
                bump("n_range_include")
        # -- Rails/SaveBang: `save` (no bang) with the result discarded --
        # rubocop-rails SaveBang wants save! in callbacks; the graph angle
        # is the DISCARDED boolean: save returns false on failure and an
        # expression-statement call throws that away.
        if meth == "save" and not recv \
                or meth == "save" and recv is not None and recv.type != "call":
            par = n.parent
            if par is not None and par.type in (
                    "expression_statement", "body_statement", "do", "then"):
                bump("n_save_ignored")
        # -- fasterer / Performance::SelectMap chain pairs ---------------
        if meth in ("first", "flatten", "each") and recv is not None:
            rtxt = text_of(recv, src)[:120]
            if (meth == "first" and "select" in rtxt) \
                    or (meth == "flatten" and "map" in rtxt) \
                    or (meth == "each" and "reverse" in rtxt):
                bump("n_legacy_chain")

        # -- metaprogramming site, with its argument if we can see it
        api_col = METAPROGRAM_APIS.get(meth)
        if api_col is not None:
            arg = ""
            literal = 0
            from_params = 0
            from_var = 0
            heredoc = 0
            if args is not None and args.named_children:
                a0 = args.named_children[0]
                atxt = text_of(a0, src)
                arg = atxt[:120]
                if a0.type in ("simple_symbol", "delimited_symbol"):
                    literal = 1
                elif a0.type == "string" and not any(
                        c.type == "interpolation" for c in a0.named_children):
                    literal = 1
                elif a0.type == "heredoc_beginning":
                    heredoc = 1
                else:
                    from_var = 1
                if "params" in atxt:
                    from_params = 1
            self._pend_meta.append(
                (rec.fid, meth[:40], arg, literal, from_params, from_var,
                 heredoc, int(singleton), idepth, line))

        # -- ActiveRecord query, resolved back to the model it started from
        kind = ("raw_sql" if meth in AR_RAW else
                "write" if meth in AR_WRITE else
                "terminal" if meth in AR_TERMINAL else
                "relation" if meth in AR_RELATION else "")
        if kind:
            model, chain = _chain_root(n, src)
            atxt = text_of(args, src) if args is not None else ""
            self._pend_ar.append(
                (rec.fid, model[:80], meth[:40], kind,
                 int("#{" in atxt),
                 int("sanitize_sql" in atxt or "?" in atxt or ":" in atxt[:2]),
                 int("params" in atxt),
                 int(args is not None and bool(args.named_children)
                     and args.named_children[0].type in ("string",
                                                         "heredoc_beginning")),
                 idepth, chain, line))

    def function_extra(self, node: Any, rec: FileRec, db: sqlite3.Connection,
                       bufs: Buffers, sid: int, scope: Scope,
                       stats: BodyStats) -> None:
        for row in self._pend_blocks:
            bufs.rows("blocks").append((sid,) + row)
        for row in self._pend_meta:
            bufs.rows("metaprogram_sites").append((sid,) + row)
        for row in self._pend_ar:
            bufs.rows("ar_queries").append((sid,) + row)
        self._pend_blocks = []
        self._pend_meta = []
        self._pend_ar = []

    # -- class bodies ------------------------------------------------------
    def type_extra(self, node: Any, rec: FileRec, db: sqlite3.Connection,
                   bufs: Buffers, sid: int, scope: Scope) -> None:
        """Everything a class body declares: mixins, attrs, callbacks, patches.

        Only the class's OWN body statements are read -- an `include` inside a
        method is a different thing and must not be counted as a mixin -- but
        `class << self`, `included do` and `class_methods do` are descended
        into, because that is where a Concern puts the half of itself that
        matters.
        """
        src = rec.data
        name = self.node_name(node, rec)
        short = name.rsplit("::", 1)[-1].lstrip(":")
        body = node.child_by_field_name("body")
        sup = node.child_by_field_name("superclass")
        suptxt = text_of(sup, src).lstrip("< ").strip() if sup is not None else ""
        # `class String` at the top level reopens ::String and every string in
        # the process changes. `class String` inside `module MyGem` declares
        # MyGem::String, an unrelated class that patches nothing. The scope
        # prefix is what separates them, and getting this wrong would report
        # every namespaced helper as a core patch.
        is_core = _reopens_core(name, short, scope)
        st = {"mixins": 0, "defs": 0, "cdefs": 0, "ivars": 0, "cvars": 0,
              "globals": 0, "included": 0, "class_methods": 0, "concern": 0,
              "attrs": 0}
        for row in self._pend_meta:
            bufs.rows("metaprogram_sites").append((sid,) + row)
        for row in self._pend_ar:
            bufs.rows("ar_queries").append((sid,) + row)
        self._pend_meta = []
        self._pend_ar = []
        self._class_body(node, body, src, rec, bufs, sid, short, is_core,
                         st, 0)
        bufs.rows("ruby_modules").append(
            (sid, rec.fid, name[:200], int(node.type == "module"),
             st["concern"], st["included"], st["class_methods"],
             suptxt[:120], st["mixins"], st["defs"], st["cdefs"],
             st["ivars"], st["cvars"], st["globals"], int(is_core),
             node.start_point[0] + 1))

    def _class_body(self, owner: Any, body: Any, src: bytes, rec: FileRec,
                    bufs: Buffers, sid: int, short: str, is_core: bool,
                    st: dict, in_singleton: int) -> None:
        if body is None:
            return
        for n in body.named_children:
            t = n.type
            if t == "method":
                st["defs"] += 1
                if in_singleton:
                    st["cdefs"] += 1
                if is_core:
                    mn = n.child_by_field_name("name")
                    mtxt = text_of(mn, src) if mn is not None else "?"
                    bufs.rows("monkey_patches").append(
                        (sid, None, rec.fid, short, mtxt[:80],
                         int(mn is not None and mn.type == "operator"),
                         in_singleton, n.start_point[0] + 1))
                continue
            if t == "singleton_method":
                st["defs"] += 1
                st["cdefs"] += 1
                if is_core:
                    mn = n.child_by_field_name("name")
                    bufs.rows("monkey_patches").append(
                        (sid, None, rec.fid, short,
                         (text_of(mn, src) if mn is not None else "?")[:80],
                         int(mn is not None and mn.type == "operator"), 1,
                         n.start_point[0] + 1))
                continue
            if t == "singleton_class":
                self._class_body(owner, n.child_by_field_name("body"), src,
                                 rec, bufs, sid, short, is_core, st, 1)
                continue
            if t == "assignment" or t == "operator_assignment":
                left = n.child_by_field_name("left")
                if left is not None:
                    lt = left.type
                    if lt == "instance_variable":
                        st["ivars"] += 1
                    elif lt == "class_variable":
                        st["cvars"] += 1
                    elif lt == "global_variable":
                        st["globals"] += 1
                continue
            if t != "call":
                continue
            mn = n.child_by_field_name("method")
            if mn is None:
                continue
            meth = text_of(mn, src)
            args = n.child_by_field_name("arguments")
            blk = n.child_by_field_name("block")
            line = n.start_point[0] + 1

            if meth in MIXIN_KINDS and args is not None:
                for a in args.named_children:
                    mx = text_of(a, src).strip()
                    if not mx or not mx[0].isupper():
                        continue
                    st["mixins"] += 1
                    if mx.endswith("Concern"):
                        st["concern"] = 1
                    bufs.rows("mixins").append(
                        (sid, rec.fid, short, mx[:120],
                         mx.rsplit("::", 1)[-1][:80],
                         MIXIN_KINDS[meth], in_singleton, line))
            elif meth in ATTR_KINDS and args is not None:
                # attr_accessor :a, :b defines FOUR methods that appear nowhere
                # in the source. They cannot become symbols without inventing
                # line spans, so they are recorded as fields and every query
                # that counts methods says in its MISLEADS line that they are
                # missing. This is the largest gap between what Ruby source
                # says and what Ruby does.
                for a in args.named_children:
                    an = text_of(a, src).strip(":\"' ")
                    if not an:
                        continue
                    st["attrs"] += 1
                    bufs.fields.append(
                        (sid, st["attrs"], an[:120],
                         ATTR_KINDS[meth][2:], "public", line,
                         in_singleton, 0, 1, 0, 0, 1, 0, 0))
            elif meth in AR_CALLBACKS or meth in AR_ASSOCIATIONS:
                target = ""
                cond = 0
                if args is not None:
                    for a in args.named_children:
                        if a.type in ("simple_symbol", "delimited_symbol") \
                                and not target:
                            target = text_of(a, src).lstrip(":").strip("\"'")
                        elif a.type == "pair":
                            k = a.child_by_field_name("key")
                            if k is not None and text_of(k, src).rstrip(":") \
                                    in ("if", "unless", "on"):
                                cond = 1
                bufs.rows("ar_callbacks").append(
                    (sid, rec.fid, short, meth[:40], target[:80], cond,
                     int(blk is not None), int(meth in AR_ASSOCIATIONS),
                     0, None, line))
            elif meth in ("included", "class_methods", "prepended",
                          "extended", "included_do"):
                if meth == "included":
                    st["included"] = 1
                elif meth == "class_methods":
                    st["class_methods"] = 1
                if blk is not None:
                    self._class_body(owner, blk.child_by_field_name("body"),
                                     src, rec, bufs, sid, short, is_core, st,
                                     1 if meth == "class_methods" else 0)
            elif meth in ("private", "protected", "public",
                          "module_function", "private_class_method"):
                if args is None or not args.named_children:
                    vis = ("private" if meth in ("private", "module_function",
                                                 "private_class_method")
                           else "protected" if meth == "protected" else "public")
                    self._vis.append((line, body.end_point[0] + 1, vis))
        # A bare `private` is an identifier, not a call, so it needs its own
        # pass -- and it is by far the common spelling.
        for n in body.named_children:
            if n.type != "identifier":
                continue
            txt = text_of(n, src)
            if txt in ("private", "protected", "public", "module_function"):
                self._vis.append(
                    (n.start_point[0] + 1, body.end_point[0] + 1,
                     "private" if txt in ("private", "module_function")
                     else "protected" if txt == "protected" else "public"))

    # -- flush -------------------------------------------------------------
    def flush_extra(self, db: sqlite3.Connection, bufs: Buffers) -> None:
        for tbl, sql in (
            ("ruby_modules",
             "INSERT OR IGNORE INTO ruby_modules(symbol_id,file_id,name,"
             "is_module,is_concern,has_included_block,has_class_methods_block,"
             "superclass,n_mixins,n_defs,n_class_defs,n_class_ivars,"
             "n_class_vars,n_globals,reopens_core,line) "
             "VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)"),
            ("mixins",
             "INSERT INTO mixins(host_id,file_id,host,mixin,mixin_short,kind,"
             "in_singleton,line) VALUES(?,?,?,?,?,?,?,?)"),
            ("metaprogram_sites",
             "INSERT INTO metaprogram_sites(symbol_id,file_id,api,arg,"
             "is_literal,from_params,from_variable,on_heredoc,in_class_body,"
             "loop_depth,line) VALUES(?,?,?,?,?,?,?,?,?,?,?)"),
            ("blocks",
             "INSERT INTO blocks(symbol_id,file_id,method,receiver,style,"
             "is_iteration,depth,n_params,body_sloc,n_queries,n_allocs,"
             "captures_outer,line) VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?)"),
            ("ar_queries",
             "INSERT INTO ar_queries(symbol_id,file_id,model,api,build_kind,"
             "has_interpolation,is_sanitized,from_params,is_string_arg,"
             "loop_depth,chain_len,line) VALUES(?,?,?,?,?,?,?,?,?,?,?,?)"),
            ("ar_callbacks",
             "INSERT INTO ar_callbacks(symbol_id,file_id,host,hook,method,"
             "is_conditional,is_block,is_association,issues_query,target_id,"
             "line) VALUES(?,?,?,?,?,?,?,?,?,?,?)"),
            ("monkey_patches",
             "INSERT INTO monkey_patches(symbol_id,method_id,file_id,"
             "core_class,method,is_operator,is_singleton,line) "
             "VALUES(?,?,?,?,?,?,?,?)"),
        ):
            rows = bufs.extra.get(tbl)
            if rows:
                db.executemany(sql, rows)

def _reopens_core(name: str, short: str, scope: Scope) -> bool:
    """True only for a genuine reopening of a core class.

    `class String` at the top level, or `class ::String` anywhere, is the real
    thing. `class String` nested inside a module is `MyModule::String` and
    patches nothing -- counting it would report every namespaced helper in the
    tree as a monkey patch, which is most of them.
    """
    if short not in CORE_CLASSES:
        return False
    if name.startswith("::"):
        return True
    return scope.qual_prefix == ""

def _in_singleton_class(node: Any) -> bool:
    """True if this def sits inside `class << self`, i.e. is a class method."""
    cur = node.parent
    hops = 0
    while cur is not None and hops < 6:
        if cur.type == "singleton_class":
            return True
        if cur.type in ("class", "module", "method"):
            return False
        cur = cur.parent
        hops += 1
    return False

def _has_yield(node: Any) -> bool:
    for n in walk(node):
        if n.type == "yield":
            return True
        if n.type == "call":
            m = n.child_by_field_name("method")
            if m is not None and m.end_byte - m.start_byte == 12:
                return True
    return False

def _raises_not_implemented(node: Any, src: bytes) -> bool:
    body = node.child_by_field_name("body")
    if body is None:
        return False
    return b"NotImplementedError" in src[body.start_byte:body.end_byte]

def _body_is_reraise(body: Any, src: bytes) -> bool:
    txt = src[body.start_byte:body.end_byte].decode("utf-8", "replace")
    return bool(re.search(r'\b(raise|fail|throw)\b', txt))

def _chain_root(node: Any, src: bytes) -> tuple[str, int]:
    """Walk a call chain back to whatever it started from.

    `User.where(x).order(y).pluck(:id)` is three call nodes deep; the model is
    only visible at the bottom. Without this every query would be attributed
    to the previous link in the chain and the model column would read
    `where`, which tells you nothing.
    """
    cur = node
    chain = 0
    while cur is not None and chain < 12:
        recv = cur.child_by_field_name("receiver")
        if recv is None:
            return "", chain
        if recv.type == "call":
            cur = recv
            chain += 1
            continue
        if recv.type in ("constant", "scope_resolution"):
            return src[recv.start_byte:recv.end_byte].decode(
                "utf-8", "replace"), chain
        if recv.type in ("identifier", "instance_variable", "self"):
            return src[recv.start_byte:recv.end_byte].decode(
                "utf-8", "replace"), chain
        return "", chain
    return "", chain

RubyAnalyzer.QUERIES = [
(
    "n-plus-one",
    "An ActiveRecord query inside a block iterating a relation",
    "ANSWERS the N+1 that Rails/FindEach, Rails/InverseOf and\n"
    "     Rails/WhereMissing each see one third of, and that no per-file cop\n"
    "     sees at all when the loop and the query live in different methods.\n"
    "     In Ruby the loop IS a block, so `users.each { |u| u.posts.count }`\n"
    "     has no `for` anywhere and a loop-node scan finds nothing.\n"
    "ACT includes/preload/eager_load the association, or move the work into\n"
    "     one query. depth above 1 means a query nested two blocks deep, which\n"
    "     is N*M, not N.\n"
    "MISLEADS an iteration over a literal array of three symbols is not an N+1\n"
    "     and trip count is invisible here. `Rails/EagerLoading` does not\n"
    "     exist -- do not go looking for it. A query on a memoised relation\n"
    "     runs once and still appears.",
    """SELECT s.name AS in_method, COALESCE(m.name,'') AS module_,
        q.model, q.api, q.build_kind, MAX(q.loop_depth) AS depth,
        COUNT(*) AS queries, s.n_iter_blocks AS iter_blocks,
        s.max_block_depth AS block_depth,
        SUM(q.build_kind IN ('terminal','raw_sql')) AS forced,
        s.is_controller AS ctrl, s.fan_in,
        f.path || ':' || MIN(q.line) AS at
    FROM ar_queries q
    JOIN symbols s ON s.id = q.symbol_id
    JOIN files f ON f.id = q.file_id
    LEFT JOIN modules m ON m.id = s.module_id
    WHERE q.loop_depth > 0 AND f.is_test = 0
      AND COALESCE(m.name,'') LIKE :mod
    GROUP BY s.id, q.model, q.api
    ORDER BY depth DESC, forced DESC, queries DESC LIMIT :lim"""),
(
    "params-to-dynamic-dispatch",
    "Request parameters reaching send, constantize, eval or a backtick",
    "ANSWERS Brakeman's Dangerous Send and Remote Code Execution shapes, but\n"
    "     across function boundaries: the controller that reads params and the\n"
    "     helper that calls send on it are usually not the same method.\n"
    "     Depth is bounded at 4 hops (see the WHERE clause below).\n"
    "ACT an allowlist, always. `send(params[:action])` is remote method\n"
    "     invocation with the attacker choosing the method; constantize on\n"
    "     user input is remote class instantiation. A literal symbol argument\n"
    "     is safe and is shown so you can dismiss those rows fast.\n"
    "MISLEADS `from_params` is a textual test for the word `params` in the\n"
    "     argument, so a local named `params_hash` matches and a value laundered\n"
    "     through three assignments does not. Both directions of error are\n"
    "     present. Confirm each row by reading it.",
    """WITH RECURSIVE walk(root, sym, depth) AS (
        -- bounded at 4 hops: a Rails request path is 2-4 frames from the
        -- controller action to the object that actually dispatches
        SELECT s.id, s.id, 0 FROM symbols s
        WHERE s.n_params_read > 0 AND s.kind = 'method'
        UNION
        SELECT r.root, e.callee_id, r.depth + 1
        FROM walk r JOIN edges e ON e.caller_id = r.sym
        WHERE r.depth < 4 AND e.is_self = 0),
        -- One row per (root, sym) pair. The recursive walk emits one row per
        -- DEPTH at which a symbol is reachable, so joining it straight to
        -- the per-site table counted every site once per distinct path
        -- length. Collapse to the shortest path before counting.
        reach(root, sym, depth) AS (
            SELECT root, sym, MIN(depth) FROM walk GROUP BY root, sym)
    SELECT src.name AS reads_params, s.name AS dispatches_in,
        MIN(reach.depth) AS hops, ms.api,
        SUBSTR(ms.arg, 1, 40) AS argument,
        SUM(ms.is_literal) AS literal_args,
        SUM(ms.from_params) AS param_args,
        SUM(ms.on_heredoc) AS heredoc_args,
        s.n_exec AS exec_calls, s.n_subshell AS backticks,
        src.is_controller AS ctrl,
        f.path || ':' || MIN(ms.line) AS at
    FROM reach
    JOIN symbols src ON src.id = reach.root
    JOIN symbols s ON s.id = reach.sym
    JOIN metaprogram_sites ms ON ms.symbol_id = s.id
    JOIN files f ON f.id = ms.file_id
    LEFT JOIN modules m ON m.id = s.module_id
    WHERE ms.is_literal = 0 AND f.is_test = 0
      AND COALESCE(m.name,'') LIKE :mod
    GROUP BY src.id, s.id, ms.api
    ORDER BY param_args DESC, hops ASC, exec_calls DESC LIMIT :lim"""),
(
    "monkey-patch-blast-radius",
    "Reopened core classes, ranked by how many call sites they could affect",
    "ANSWERS the question a diff cannot: adding `def blank?` to String changes\n"
    "     the behaviour of every String in the process, including the ones in\n"
    "     gems you did not write. This ranks patches by how many call sites in\n"
    "     THIS tree use that method name at all.\n"
    "ACT a refinement (`using`) scopes the change to one file. A helper module\n"
    "     scopes it to what includes it. Neither is a monkey patch. An operator\n"
    "     patch is the worst case -- `<=>` on Array changes sort everywhere.\n"
    "MISLEADS `could_collide` counts every symbol and call site sharing the\n"
    "     name, in this tree only. Gems are not scanned, so the true blast\n"
    "     radius is larger, and a patch that ADDS a method nobody else defines\n"
    "     is far safer than one that REDEFINES an existing core method --\n"
    "     which this cannot tell apart, because the core is not in the tree.\n"
    "     same_name_defs counts `def` only: methods generated by\n"
    "     attr_accessor, delegate or define_method exist at run time and have\n"
    "     no symbol, so the count is low by however many of those there are.\n"
    "     Only a top-level `class String` (or an explicit `class ::String`)\n"
    "     is treated as a reopening -- `class String` nested in a module is a\n"
    "     different class and is correctly excluded.",
    """SELECT p.core_class, p.method, p.is_operator AS operator,
        p.is_singleton AS class_method,
        COUNT(DISTINCT p.id) AS patch_sites,
        (SELECT COUNT(*) FROM symbols s2
         WHERE s2.name = p.method AND s2.kind = 'method') AS same_name_defs,
        (SELECT COUNT(*) FROM unresolved_calls u
         WHERE u.name = p.method OR u.name LIKE '%.' || p.method) AS unresolved_uses,
        (SELECT COUNT(*) FROM callsites cs
         JOIN symbols s3 ON s3.id = cs.callee_id
         WHERE s3.name = p.method) AS resolved_uses,
        (SELECT COUNT(*) FROM symbols s4
         WHERE s4.name = p.method AND s4.kind = 'method')
        + (SELECT COUNT(*) FROM unresolved_calls u2
           WHERE u2.name LIKE '%' || p.method) AS could_collide,
        f.path || ':' || MIN(p.line) AS at
    FROM monkey_patches p
    JOIN files f ON f.id = p.file_id
    LEFT JOIN modules m ON m.id = f.module_id
    WHERE f.is_test = 0 AND COALESCE(m.name,'') LIKE :mod
    GROUP BY p.core_class, p.method
    ORDER BY could_collide DESC, operator DESC LIMIT :lim"""),
(
    "string-churn-unfrozen",
    "String literals allocated per iteration, in files with no frozen magic comment",
    "ANSWERS where the interpreter allocates a fresh String on every trip round\n"
    "     a loop. Ruby 3.4 made bare literals 'chilled' -- they warn when you\n"
    "     mutate them -- but frozen-by-default has still NOT landed in 4.0, so\n"
    "     without the magic comment each evaluation is a real allocation.\n"
    "ACT add `# frozen_string_literal: true` to the top of the file. It is one\n"
    "     line, it is the single cheapest allocation win in Ruby, and\n"
    "     has_frozen tells you which files already have it.\n"
    "MISLEADS an interpolated string allocates whether or not the file is\n"
    "     frozen -- the magic comment cannot help `\"id=#{x}\"`, and interp\n"
    "     is broken out so you can see how much of the count it explains. A\n"
    "     string that is genuinely mutated afterwards MUST stay unfrozen.",
    """SELECT s.name, COALESCE(m.name,'') AS module_,
        s.has_frozen_literal AS has_frozen,
        s.n_str_lit_in_loop AS str_in_loop,
        s.n_string_interp AS interp, s.n_string_lit AS strings,
        s.n_iter_blocks AS iter_blocks, s.max_block_depth AS block_depth,
        s.max_loop_depth AS loop_depth, s.n_freeze AS freezes,
        s.n_dup_clone AS dups, s.fan_in,
        (s.n_str_lit_in_loop * (1 + s.max_block_depth + s.max_loop_depth))
            AS churn,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id = s.file_id
    LEFT JOIN modules m ON m.id = s.module_id
    WHERE s.has_frozen_literal = 0 AND s.n_str_lit_in_loop > 0
      AND f.is_test = 0 AND f.is_generated = 0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY churn DESC, s.fan_in DESC LIMIT :lim"""),
(
    "rescue-swallow",
    "Rescue bodies that discard the error, ranked by what they wrapped",
    "ANSWERS which swallowed exceptions actually hide something. A bare\n"
    "     `rescue` catches StandardError; `rescue Exception` also catches\n"
    "     SignalException, NoMemoryError and Interrupt, so it eats Ctrl-C and\n"
    "     the OOM killer's warning shot. An empty body discards both.\n"
    "ACT name the class you expect. If the method wraps a DB or HTTP call, a\n"
    "     silent rescue turns a timeout into a wrong answer that looks right,\n"
    "     which is the failure mode nobody notices for a quarter.\n"
    "MISLEADS `reraise` counts a raise anywhere in the handler body, so a\n"
    "     handler that logs and re-raises correctly still shows a rescue.\n"
    "     `rescue nil` on a parse you genuinely do not care about is fine and\n"
    "     appears here. Read the io/net/sql columns before acting.",
    """SELECT s.name, COALESCE(m.name,'') AS module_,
        s.n_rescue AS rescues, s.n_rescue_bare AS bare,
        s.n_rescue_exception AS catches_exception,
        s.n_rescue_empty AS empty_, s.n_rescue_reraise AS reraises,
        s.n_retry AS retries, s.n_ensure AS ensures, s.n_raise AS raises,
        s.n_sql + s.n_rails_query AS db, s.n_net AS http, s.n_io AS io,
        s.n_ar_query AS ar_calls, s.fan_in,
        (s.n_rescue_empty*4 + s.n_rescue_exception*3 + s.n_rescue_bare)
          * (1 + s.n_sql + s.n_net + s.n_rails_query) AS severity,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id = s.file_id
    LEFT JOIN modules m ON m.id = s.module_id
    WHERE (s.n_rescue_bare + s.n_rescue_exception + s.n_rescue_empty) > 0
      AND s.n_rescue_reraise = 0
      AND f.is_test = 0 AND COALESCE(m.name,'') LIKE :mod
    ORDER BY severity DESC, s.fan_in DESC LIMIT :lim"""),
(
    "class-state-under-threads",
    "Mutable class-level state reachable from something a thread runs",
    "ANSWERS what rubocop-thread_safety's ten cops look for, raised to the call\n"
    "     graph. A `@@counter`, a class-level `@cache` or a `$global` is shared\n"
    "     by every thread in the process; Puma serves controller actions on\n"
    "     threads and every job backend runs perform on a worker, so those are\n"
    "     threaded entries whether or not the code says Thread.new.\n"
    "     Depth is bounded at 4 hops (see the WHERE clause below).\n"
    "ACT make it immutable after boot, or put it behind a Mutex, or move it to\n"
    "     Thread.current / a request-scoped object. mutexes is the\n"
    "     counter-evidence column.\n"
    "MISLEADS state written once at class-definition time and only read\n"
    "     afterwards is safe and appears here -- this counts writes lexically,\n"
    "     not by when they run. Memoisation into a class ivar is the classic\n"
    "     benign-looking case that is in fact a race under load.",
    """WITH RECURSIVE down(root, sym, depth) AS (
        -- bounded at 4 hops: deeper than a controller action's own service
        -- objects and the answer stops being about that entry point
        SELECT s.id, s.id, 0 FROM symbols s WHERE s.is_threaded_entry = 1
        UNION
        SELECT d.root, e.callee_id, d.depth + 1
        FROM down d JOIN edges e ON e.caller_id = d.sym
        WHERE d.depth < 4 AND e.is_self = 0)
    SELECT entry.name AS threaded_entry, s.name AS touches_state,
        MIN(down.depth) AS hops,
        MAX(s.n_class_var) AS class_vars, MAX(s.n_global_var) AS globals,
        MAX(s.n_class_level_ivar) AS class_ivars,
        MAX(s.n_class_level_write) AS writes,
        MAX(s.n_mutex) AS mutexes, MAX(s.n_thread_local) AS thread_locals,
        MAX(entry.n_thread_new) AS spawns, MAX(entry.is_job) AS job,
        MAX(entry.is_controller) AS ctrl,
        f.path || ':' || MIN(s.line_start) AS at
    FROM down
    JOIN symbols entry ON entry.id = down.root
    JOIN symbols s ON s.id = down.sym
    JOIN files f ON f.id = s.file_id
    LEFT JOIN modules m ON m.id = s.module_id
    WHERE (s.n_class_var + s.n_global_var + s.n_class_level_write) > 0
      AND f.is_test = 0 AND COALESCE(m.name,'') LIKE :mod
    GROUP BY entry.id, s.id
    HAVING mutexes = 0
    ORDER BY writes DESC, class_vars DESC, hops ASC LIMIT :lim"""),
(
    "timeout-blast-radius",
    "Timeout.timeout sites, ranked by what is running inside them",
    "ANSWERS where the most dangerous API in the standard library is used.\n"
    "     Timeout.timeout raises in another thread at an arbitrary bytecode\n"
    "     boundary -- inside an ensure block, halfway through a Mutex handoff,\n"
    "     between a write and its flush. It is unsafe BY DESIGN, not by\n"
    "     misuse, and the damage scales with what was interrupted.\n"
    "ACT use the library's own timeout: Net::HTTP#read_timeout, the driver's\n"
    "     statement_timeout, Redis's connect_timeout. Those unwind cleanly\n"
    "     because they know their own invariants.\n"
    "MISLEADS a Timeout around pure computation is comparatively harmless, and\n"
    "     this cannot see the timeout VALUE -- a 30-minute guard against a\n"
    "     hang is a different thing from a 100ms budget. db/http/io are the\n"
    "     columns that decide which one you are looking at.",
    """SELECT s.name, COALESCE(m.name,'') AS module_,
        s.n_timeout AS timeouts,
        s.n_sql + s.n_rails_query AS db, s.n_net AS http, s.n_io AS io,
        s.n_ensure AS ensures, s.n_mutex AS mutexes,
        s.n_thread_new AS spawns, s.n_rescue AS rescues,
        s.n_ar_write AS ar_writes,
        (SELECT COUNT(*) FROM blocks b
         WHERE b.symbol_id = s.id AND b.method = 'timeout') AS timeout_blocks,
        s.fan_in,
        s.n_timeout * (1 + s.n_sql + s.n_net*2 + s.n_ar_write*3
                       + s.n_ensure*2 + s.n_mutex*3) AS blast,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id = s.file_id
    LEFT JOIN modules m ON m.id = s.module_id
    WHERE s.n_timeout > 0 AND f.is_test = 0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY blast DESC LIMIT :lim"""),
(
    "mass-assignment",
    "params reaching new/create/update with no permit in sight",
    "ANSWERS Brakeman's MassAssignment: a hash straight from the request handed\n"
    "     to a model writer sets whatever columns the attacker names, admin\n"
    "     flags included.\n"
    "ACT strong parameters -- require(:model).permit(:only, :these). The\n"
    "     permit_bang column is the one with no false positives: `permit!`\n"
    "     permits EVERY parameter, so it is exactly as dangerous as no permit\n"
    "     at all while looking like it is doing something.\n"
    "MISLEADS `new` and `create` are counted as sinks whether or not the\n"
    "     argument came from params, so a row with params_reads = 0 is noise.\n"
    "     A permit in a private `xxx_params` method one frame away is not seen\n"
    "     as protecting this method -- check permit_nearby before acting.",
    """SELECT s.name, COALESCE(m.name,'') AS module_,
        s.n_params_read AS params_reads, s.n_mass_assign AS sinks,
        s.n_permit AS permits, s.n_permit_bang AS permit_bang,
        (SELECT COALESCE(SUM(s2.n_permit),0) FROM symbols s2
         WHERE s2.file_id = s.file_id AND s2.kind = 'method') AS permit_nearby,
        s.n_ar_write AS ar_writes, s.is_controller AS ctrl,
        s.is_public AS public_, s.fan_in,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id = s.file_id
    LEFT JOIN modules m ON m.id = s.module_id
    WHERE s.n_mass_assign > 0
      AND (s.n_permit = 0 OR s.n_permit_bang > 0)
      AND s.n_params_read > 0
      AND f.is_test = 0 AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.n_permit_bang DESC, s.n_params_read DESC,
        s.n_mass_assign DESC LIMIT :lim"""),
(
    "callback-cascade",
    "ActiveRecord callbacks that issue queries, and what they pull in behind them",
    "ANSWERS why one `save` turns into eleven queries. A before_save that calls\n"
    "     a method that queries is invisible at the call site -- the caller\n"
    "     wrote `user.save` and got a transaction with a cascade inside it.\n"
    "     Depth is bounded at 3 hops (see the WHERE clause below), because\n"
    "     past three the answer stops being about the callback.\n"
    "ACT move the work out of the callback and into an explicit service\n"
    "     object, or at minimum make it conditional. after_commit is the one\n"
    "     place where a query is defensible; before_* inside the transaction\n"
    "     is holding row locks while it waits.\n"
    "MISLEADS the edge from `before_save :normalize` to `def normalize` does\n"
    "     not exist in the tree -- a symbol is not a call -- so it is stitched\n"
    "     by name WITHIN THE FILE. A callback whose method is inherited from a\n"
    "     concern in another file has target_id NULL and is missing entirely.\n"
    "     Conditional callbacks may never run.",
    """WITH RECURSIVE cascade(cb, sym, depth) AS (
        -- bounded at 3 hops: the callback, what it calls, what that calls
        SELECT c.id, c.target_id, 0 FROM ar_callbacks c
        WHERE c.target_id IS NOT NULL
        UNION
        SELECT cs.cb, e.callee_id, cs.depth + 1
        FROM cascade cs JOIN edges e ON e.caller_id = cs.sym
        WHERE cs.depth < 3 AND e.is_self = 0)
    SELECT c.host, c.hook, c.method, c.is_conditional AS conditional,
        c.is_association AS assoc, c.issues_query AS direct_query,
        MAX(cascade.depth) AS reach,
        COUNT(DISTINCT cascade.sym) AS methods_pulled_in,
        COALESCE(SUM(s.n_ar_query),0) AS ar_calls,
        COALESCE(SUM(s.n_ar_write),0) AS writes,
        COALESCE(SUM(s.n_ar_query_in_block),0) AS queries_in_loops,
        COALESCE(SUM(s.n_net),0) AS http_calls,
        f.path || ':' || c.line AS at
    FROM cascade
    JOIN ar_callbacks c ON c.id = cascade.cb
    JOIN symbols s ON s.id = cascade.sym
    JOIN files f ON f.id = c.file_id
    LEFT JOIN modules m ON m.id = f.module_id
    WHERE f.is_test = 0 AND COALESCE(m.name,'') LIKE :mod
    GROUP BY c.id
    HAVING ar_calls > 0 OR http_calls > 0
    ORDER BY queries_in_loops DESC, ar_calls DESC, reach DESC LIMIT :lim"""),
(
    "mixin-method-collision",
    "Two modules included into one class, both defining the same method",
    "ANSWERS which method actually wins. Ruby's method resolution order is\n"
    "     last-include-wins for `include`, and `prepend` jumps ahead of the\n"
    "     class's own definitions entirely -- so the answer depends on the\n"
    "     order of two lines that look unordered, and reordering them is a\n"
    "     behaviour change nobody reviews.\n"
    "ACT if both are yours, rename one. If one is a gem's, prepend a module of\n"
    "     your own and call super explicitly so the chain is written down.\n"
    "     A collision where either side is `prepend` is the urgent one.\n"
    "MISLEADS only modules defined IN THIS TREE are compared, and only their\n"
    "     literal `def`s. A module that generates its methods with\n"
    "     attr_accessor, delegate or define_method contributes nothing here,\n"
    "     so a real collision between two such modules is invisible -- and\n"
    "     that is the common shape in a Concern. A collision with\n"
    "     ActiveSupport or with a gem is invisible for the same reason.\n"
    "     Matching is on the module's short name, so two different `Trackable`\n"
    "     modules in different namespaces are wrongly treated as one.",
    """WITH mod_defs AS (
        SELECT ms.id AS mod_id, ms.name AS mod_name, md.name AS meth,
               md.id AS meth_id, md.sloc
        FROM symbols ms JOIN symbols md ON md.parent_id = ms.id
        WHERE ms.kind = 'module' AND md.kind = 'method')
    SELECT h.name AS host_class, a.kind AS kind_a, a.mixin_short AS mixin_a,
        b.kind AS kind_b, b.mixin_short AS mixin_b,
        da.meth AS collides_on, da.sloc AS sloc_a, db2.sloc AS sloc_b,
        (a.kind = 'prepend' OR b.kind = 'prepend') AS has_prepend,
        a.line AS line_a, b.line AS line_b,
        CASE WHEN b.line > a.line THEN b.mixin_short ELSE a.mixin_short END
            AS wins_if_plain_include,
        f.path || ':' || h.line_start AS at
    FROM mixins a
    JOIN mixins b ON b.host_id = a.host_id AND b.mixin_short > a.mixin_short
    JOIN symbols h ON h.id = a.host_id
    JOIN files f ON f.id = h.file_id
    JOIN mod_defs da ON da.mod_name = a.mixin_short
    JOIN mod_defs db2 ON db2.mod_name = b.mixin_short AND db2.meth = da.meth
    LEFT JOIN modules m ON m.id = h.module_id
    WHERE f.is_test = 0 AND COALESCE(m.name,'') LIKE :mod
    ORDER BY has_prepend DESC, da.sloc DESC LIMIT :lim"""),
(
    "sql-interpolation",
    "String interpolation inside where, order, pluck and friends",
    "ANSWERS Brakeman's SQLInjection. `where(\"name = '#{params[:q]}'\")` is the\n"
    "     canonical Rails injection, and `order(params[:sort])` is the one\n"
    "     people forget -- ORDER BY is not parameterisable, so it needs an\n"
    "     allowlist rather than a bind.\n"
    "ACT where(name: value) or where(\"name = ?\", value). For order, map the\n"
    "     user's string through a fixed hash of permitted columns.\n"
    "MISLEADS `sanitized` is a weak textual test for sanitize_sql or a bind\n"
    "     placeholder in the argument, so a genuinely safe call can show\n"
    "     sanitized = 0. Interpolation of a constant or of an integer that\n"
    "     never leaves the server is safe and appears here. from_params is the\n"
    "     column that separates the two.",
    """SELECT q.model, q.api, q.build_kind,
        s.name AS in_method, COALESCE(m.name,'') AS module_,
        q.has_interpolation AS interp, q.from_params AS from_params,
        q.is_sanitized AS sanitized, q.is_string_arg AS string_arg,
        q.chain_len AS chain, q.loop_depth AS in_loop,
        s.n_sql_interp AS sql_interp_lits,
        s.n_sql_sanitized AS sanitize_calls,
        s.is_controller AS ctrl, s.fan_in,
        f.path || ':' || q.line AS at
    FROM ar_queries q
    JOIN symbols s ON s.id = q.symbol_id
    JOIN files f ON f.id = q.file_id
    LEFT JOIN modules m ON m.id = s.module_id
    WHERE (q.has_interpolation = 1 OR q.from_params = 1)
      AND q.is_sanitized = 0
      AND f.is_test = 0 AND COALESCE(m.name,'') LIKE :mod
    ORDER BY q.from_params DESC, q.build_kind = 'raw_sql' DESC,
        q.has_interpolation DESC LIMIT :lim"""),
(
    "per-iteration-cost",
    "Collection literals, Range#include? and chained array allocations in loops",
    "ANSWERS the four rubocop-performance cops that only matter inside a loop:\n"
    "     CollectionLiteralInLoop (the array or hash is rebuilt every trip),\n"
    "     RangeInclude (include? walks the range, cover? compares two ends),\n"
    "     ChainArrayAllocation (each link in .map.select.map materialises a\n"
    "     whole new array), and TimesMap.\n"
    "ACT hoist the literal to a frozen constant; swap include? for cover?;\n"
    "     collapse a chain with filter_map, each_with_object or lazy.\n"
    "MISLEADS every one of these is cheap on ten elements and only matters at\n"
    "     scale, and this cannot see collection size or trip count. Sort by\n"
    "     the score, then confirm with a benchmark before changing anything --\n"
    "     a chain rewritten as one pass is usually less readable and needs to\n"
    "     earn that.",
    """SELECT s.name, COALESCE(m.name,'') AS module_,
        s.n_collection_lit_in_loop AS lit_in_loop,
        s.n_chain_array_alloc AS chain_alloc, s.n_map_chain AS map_chains,
        s.n_range_include AS range_include, s.n_times_map AS times_map,
        s.n_str_lit_in_loop AS str_in_loop,
        s.n_iter_blocks AS iter_blocks, s.max_block_depth AS block_depth,
        s.max_loop_depth AS loop_depth, s.call_in_loop AS calls_in_loop,
        s.has_frozen_literal AS frozen_, s.fan_in,
        (s.n_collection_lit_in_loop*4 + s.n_chain_array_alloc*3
         + s.n_range_include*2 + s.n_times_map*3 + s.n_str_lit_in_loop)
          * (1 + s.max_block_depth + s.max_loop_depth) AS cost,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id = s.file_id
    LEFT JOIN modules m ON m.id = s.module_id
    WHERE (s.n_collection_lit_in_loop + s.n_chain_array_alloc
           + s.n_range_include + s.n_times_map) > 0
      AND f.is_test = 0 AND f.is_generated = 0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY cost DESC LIMIT :lim"""),
(
    "rescue-too-broad",
    "rescue Exception and bare rescue: catching what you were never meant to",
    "ANSWERS where the error handling is wider than any error. Bare `rescue`\n"
    "     catches StandardError, which is usually intended -- but\n"
    "     `rescue Exception` also catches SignalException, Interrupt and\n"
    "     NoMemoryError, so it swallows Ctrl-C and turns an OOM into a\n"
    "     confusing retry loop.\n"
    "ACT name the exceptions you can actually handle. If the goal is cleanup,\n"
    "     `ensure` runs without catching anything. If it is logging, re-raise\n"
    "     after logging -- `reraises` shows who already does.\n"
    "MISLEADS a top-level supervisor in a worker process legitimately catches\n"
    "     Exception so it can report before dying. Those are correct and rank\n"
    "     high here; check whether the body re-raises.",
    """SELECT s.name, s.qual_name AS qual,
        s.n_rescue_exception AS rescue_exception, s.n_rescue_bare AS bare,
        s.n_rescue_empty AS empty_bodies, s.n_rescue_reraise AS reraises,
        s.n_ensure AS ensures, s.n_retry AS retries, s.fan_in,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE (s.n_rescue_exception > 0 OR s.n_rescue_bare > 0) AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.n_rescue_exception DESC,
        (s.n_rescue_bare - s.n_rescue_reraise) DESC LIMIT :lim"""),
(
    "threads-without-synchronisation",
    "Thread.new and Ractor next to mutable state, with no Mutex in sight",
    "ANSWERS which concurrency is unguarded. MRI's GIL makes a data race\n"
    "     unlikely to corrupt an object, but it does NOT make check-then-act\n"
    "     atomic: two threads can both see nil and both build the thing.\n"
    "     On JRuby and TruffleRuby the GIL is not there at all.\n"
    "ACT wrap the compound operation in a Mutex, or use a Queue, which is\n"
    "     already thread-safe. For memoisation prefer building eagerly at\n"
    "     boot over lazily under concurrency.\n"
    "MISLEADS a thread that only reads immutable data needs no mutex and is\n"
    "     listed here anyway. `class_writes` is the column that distinguishes\n"
    "     them -- shared MUTABLE state is the actual risk.",
    """SELECT s.name, s.qual_name AS qual, s.n_thread_new AS threads,
        s.n_ractor AS ractors, s.n_mutex AS mutexes,
        s.n_thread_local AS thread_locals,
        s.n_class_level_write AS class_writes, s.n_global_var AS globals,
        s.is_threaded_entry AS threaded_entry, s.fan_in,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE (s.n_thread_new > 0 OR s.n_ractor > 0) AND s.n_mutex = 0
      AND f.is_test=0 AND COALESCE(m.name,'') LIKE :mod
    ORDER BY (s.n_class_level_write + s.n_global_var) DESC,
        s.n_thread_new DESC LIMIT :lim"""),
(
    "eval-family-surface",
    "eval, instance_eval and class_eval: where the program rewrites itself",
    "ANSWERS how much of this codebase is written at run time. `class_eval`\n"
    "     with a string builds methods no editor can jump to and no static\n"
    "     tool can see; `eval` on anything derived from input is remote code\n"
    "     execution.\n"
    "ACT `define_method` with a block does everything `class_eval` with a\n"
    "     string does, keeps the lexical scope, and is visible to tooling.\n"
    "     Reserve string eval for genuine DSL compilation, and never let a\n"
    "     parameter reach it.\n"
    "MISLEADS Rails itself is built on this and the framework rows are\n"
    "     expected. What matters is eval in APPLICATION code, and eval whose\n"
    "     argument came from params -- see params-to-dynamic-dispatch.",
    """SELECT s.name, s.qual_name AS qual, s.n_eval AS evals,
        s.n_instance_eval AS instance_evals, s.n_class_eval AS class_evals,
        s.n_define_method AS define_methods,
        s.n_method_missing AS method_missing, s.n_send AS sends,
        s.n_params_read AS params_reads, s.fan_in,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE (s.n_eval + s.n_instance_eval + s.n_class_eval) > 0 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.n_params_read DESC, s.n_eval DESC,
        (s.n_instance_eval + s.n_class_eval) DESC LIMIT :lim"""),
(
    "shell-out-surface",
    "Backticks, system and exec, ranked by how close request data gets",
    "ANSWERS where Ruby hands a string to a shell. Backticks and the\n"
    "     single-argument form of `system` go through /bin/sh, so a semicolon\n"
    "     anywhere in that string is a second command.\n"
    "ACT use the multi-argument form -- `system(\"git\", \"log\", ref)` --\n"
    "     which execs directly and never involves a shell, so quoting stops\n"
    "     being a security question. Where a shell is genuinely required,\n"
    "     Shellwords.escape every interpolated value.\n"
    "MISLEADS this cannot see whether the argument is a literal. A backtick\n"
    "     running a fixed command is fine and ranks the same as one built by\n"
    "     interpolation -- `interpolations` is the column that separates them.",
    """SELECT s.name, s.qual_name AS qual, s.n_subshell AS backticks,
        s.n_exec AS exec_calls, s.n_string_interp AS interpolations,
        s.n_params_read AS params_reads, s.n_heredoc AS heredocs,
        s.is_controller AS controller, s.is_job AS job, s.fan_in,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE (s.n_subshell > 0 OR s.n_exec > 0) AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.n_params_read DESC, s.n_string_interp DESC,
        (s.n_subshell + s.n_exec) DESC LIMIT :lim"""),
(
    "dead-code",
    "Nothing in this tree calls these",
    "ANSWERS what might be deletable.\n"
    "ACT grep the name as a STRING before deleting: a registry, a config file\n"
    "     or a reflective call keeps a symbol alive with no edge to show it.\n"
    "MISLEADS this is the query most likely to be wrong, and `graph-blindspots`\n"
    "     is the measure of by how much. Anything public is excluded because a\n"
    "     caller outside this tree cannot be seen at all; what is left is\n"
    "     private and unreferenced, which is a much weaker claim than dead.",
    """SELECT s.name, s.kind, s.sloc, s.cyclomatic AS cyclo,
        s.n_external_calls AS ext_calls,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.fan_in=0 AND s.is_public=0 AND s.is_test=0
      AND s.is_entrypoint=0 AND s.is_override=0 AND s.is_abstract=0
      AND s.kind IN ('function','method','closure')
      AND s.name NOT IN ('(anonymous)','<module>')
      AND f.is_test=0 AND f.is_generated=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.sloc DESC LIMIT :lim"""),
("raw-sql-below-a-controller", "find_by_sql, execute or constantize reachable from a controller action",
    "ANSWERS the ranking Brakeman cannot do. It reports every `find_by_sql`\n"
    "     and every `constantize` with a confidence level derived from the call\n"
    "     site alone. The graph adds the part that decides severity: whether a\n"
    "     controller action -- the code an HTTP request actually enters --\n"
    "     can reach it, and in how few hops.\n"
    "ACT for `raw_sql`, move to a parameterised `where`. For `constantize`,\n"
    "     replace with an explicit allow-list hash; a `constantize` on request\n"
    "     data is remote code execution, not a lookup.\n"
    "MISLEADS reachability is not taint -- the SQL may be a frozen constant.\n"
    "     Depth stops at 4 hops. Rails resolves a great deal at runtime\n"
    "     (`send`, `method_missing`, concerns mixed in by string name), and\n"
    "     none of that produces an edge, so absence here proves nothing.",
    """WITH RECURSIVE walk(root, sym, depth) AS (
        SELECT s.id, s.id, 0 FROM symbols s
        JOIN files f ON f.id = s.file_id
        WHERE (s.is_controller = 1 OR s.is_entrypoint = 1 OR s.is_job = 1)
          AND f.is_test = 0
        UNION
        SELECT w.root, e.callee_id, w.depth + 1
        FROM walk w JOIN edges e ON e.caller_id = w.sym
        WHERE w.depth < 4 AND e.is_self = 0),      -- depth bound: 4 hops
    reach(root, sym, depth) AS (
        SELECT root, sym, MIN(depth) FROM walk GROUP BY root, sym)
    SELECT s.name, entry.name AS reached_from, MIN(r.depth) AS hops,
        s.n_raw_sql AS raw_sql, s.n_constantize AS constantize,
        s.n_system_call AS system_calls, s.n_html_safe AS html_safe,
        s.n_open_call AS open_calls, s.fan_in,
        f.path || \':\' || s.line_start AS at
    FROM reach r
    JOIN symbols s ON s.id = r.sym
    JOIN symbols entry ON entry.id = r.root
    JOIN files f ON f.id = s.file_id
    LEFT JOIN modules m ON m.id = s.module_id
    WHERE r.depth > 0 AND f.is_test = 0
      AND (s.n_raw_sql > 0 OR s.n_constantize > 0 OR s.n_system_call > 0
           OR s.n_html_safe > 0)
      AND COALESCE(m.name,\'\') LIKE :mod
    GROUP BY s.id, entry.id
    ORDER BY hops ASC, constantize DESC, raw_sql DESC,
        s.fan_in DESC LIMIT :lim"""),
("write-per-iteration", "save, update or create called inside a loop, ranked by how many callers reach it",
    "ANSWERS the write-side N+1 that RuboCop\'s Rails cops do not cover and\n"
    "     Bullet only catches at runtime on the read side. One `save` per\n"
    "     iteration is one INSERT, one transaction and one round trip per\n"
    "     iteration; a thousand-element collection is a thousand of each. The\n"
    "     read-side N+1 gets all the attention and this one is usually worse.\n"
    "ACT use `insert_all` / `upsert_all`, or wrap the loop in a single\n"
    "     `transaction` block so the commits collapse. `enum_in_loop` next to a\n"
    "     write marks a nested iteration, which multiplies it again.\n"
    "MISLEADS a loop over two records is fine, and the bound is invisible here.\n"
    "     `save` on a non-ActiveRecord object -- a form object, a service --\n"
    "     reads identically and costs nothing. Callbacks that themselves write\n"
    "     are not counted, so the real number can be higher.",
    """SELECT s.name, s.n_ar_write_in_loop AS writes_in_loop,
        s.n_enum_in_loop AS enum_in_loop,
        s.n_count_in_loop AS count_in_loop,
        s.n_serialize_in_loop AS serialize_in_loop,
        s.max_loop_depth AS loop_depth, s.is_model AS in_model,
        s.is_job AS in_job, s.fan_in,
        COUNT(DISTINCT e.caller_id) AS distinct_callers,
        f.path || \':\' || s.line_start AS at
    FROM symbols s
    JOIN files f ON f.id = s.file_id
    LEFT JOIN edges e ON e.callee_id = s.id AND e.is_self = 0
    LEFT JOIN modules m ON m.id = s.module_id
    WHERE s.n_ar_write_in_loop > 0 AND f.is_test = 0
      AND COALESCE(m.name,\'\') LIKE :mod
    GROUP BY s.id
    ORDER BY writes_in_loop DESC, loop_depth DESC,
        distinct_callers DESC LIMIT :lim"""),
(
    "open-injection",
    "Kernel#open with user input (RuboCop Security/Open)",
    "ANSWERS where Kernel#open is called, which for non-file URLs delegates to\n"
    "     open-uri, and for pipes can execute commands. open('|cmd') is RCE.\n"
    "ACT use File.open for files, URI.open for URLs, never open on user input.\n"
    "MISLEADS open on a constant string is safe. The graph sees the call but\n"
    "     not the argument.",
    """SELECT s.name, s.n_open_call AS open_calls,
        s.n_system_call AS system_calls,
        s.n_eval AS eval_calls,
        s.fan_in,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_open_call > 0 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.fan_in DESC, s.n_open_call DESC LIMIT :lim"""),
(
    "send-injection",
    "send or __send__ with dynamic method name (RuboCop Security/Send)",
    "ANSWERS where send is called with a dynamic method name, which can invoke\n"
    "     any method including private ones. If the name is user-controlled, this\n"
    "     is a metaprogramming injection.\n"
    "ACT whitelist allowed method names; use public_send.\n"
    "MISLEADS send in a DSL or internal framework is a valid pattern. The graph\n"
    "     sees the call but not the argument source.",
    """SELECT s.name, s.n_send AS send_calls,
        s.n_define_method AS define_methods,
        s.n_method_missing AS method_missing,
        s.n_const_get AS const_gets,
        s.n_metaprogram_total AS metaprogram_total,
        s.fan_in, s.cyclomatic AS cyclo,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_send > 0 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.fan_in DESC, s.n_send DESC LIMIT :lim"""),
(
    "constantize-injection",
    "constantize on user input (RuboCop Security/Const)",
    "ANSWERS where constantize is called, which converts a string to a class\n"
    "     reference. If the string is user-controlled, an attacker can instantiate\n"
    "     any class in the runtime.\n"
    "ACT use a whitelist hash mapping string names to class constants.\n"
    "MISLEADS constantize on an internal string is safe. The graph sees the call\n"
    "     but not the input source.",
    """SELECT s.name, s.n_constantize AS constantize_calls,
        s.n_const_get AS const_gets,
        s.n_metaprogram_dynamic AS dynamic_metaprogram,
        s.fan_in,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_constantize > 0 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.fan_in DESC, s.n_constantize DESC LIMIT :lim"""),
(
    "string-concat-in-loop",
    "String += or << inside a loop (RuboCop Performance/Concat)",
    "ANSWERS where strings are built with += or << inside a loop, which creates\n"
    "     a new string each iteration. Ruby strings are mutable but += reassigns.\n"
    "ACT use << (in-place) or join an array.\n"
    "MISLEADS a loop with a small constant bound is fine. The column counts\n"
    "     sites, not allocations.",
    """SELECT s.name, s.n_str_lit_in_loop AS str_lit_in_loop,
        s.n_string_interp AS string_interp,
        s.concat_in_loop, s.n_loops AS loops,
        s.cyclomatic AS cyclo, s.fan_in,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.concat_in_loop > 0 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.concat_in_loop DESC, s.n_loops DESC LIMIT :lim"""),
(
    "weak-hash",
    "MD5 or SHA1 used for hashing (RuboCop Security/WeakHash)",
    "ANSWERS where a weak hash algorithm is used for security purposes.\n"
    "ACT use SHA256 or stronger; for passwords use bcrypt/scrypt/argon2.\n"
    "MISLEADS MD5 for a non-security checksum is fine. The graph sees the call\n"
    "     but not the purpose.",
    """SELECT s.name, s.n_weak_hash AS weak_hashs,
        s.n_weak_random AS weak_randoms,
        s.fan_in,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE (s.n_weak_hash + s.n_weak_random) > 0 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.fan_in DESC,
        s.n_weak_hash + s.n_weak_random DESC LIMIT :lim"""),
(
    "html-safe-xss",
    "html_safe on user-controlled string (RuboCop Rails/OutputSafety)",
    "ANSWERS where html_safe is called, which marks a string as safe for HTML\n"
    "     output, bypassing Rails' XSS protection. If the string contains user\n"
    "     input, this is an XSS vulnerability.\n"
    "ACT use sanitize or content_tag; never html_safe on user input.\n"
    "MISLEADS html_safe on a constant or a sanitized string is correct. The\n"
    "     graph sees the call but not the string's source.",
    """SELECT s.name, s.n_html_safe AS html_safe_calls,
        s.n_raw_sql AS raw_sql,
        s.n_params_read AS params_reads,
        s.fan_in,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_html_safe > 0 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.fan_in DESC, s.n_html_safe DESC LIMIT :lim"""),
(
    "sql-injection-ar",
    "ActiveRecord where with string interpolation (RuboCop Rails/Skylight)",
    "ANSWERS where ActiveRecord queries use string interpolation instead of\n"
    "     parameterized queries: where(\"x = #{y}\") instead of where(x: y).\n"
    "ACT use the hash form: where(x: y) or parameterized: where('x = ?', y).\n"
    "MISLEADS interpolation of a constant is safe. n_sql_interp counts sites.\n"
    "     n_sql_sanitized says sanitize was called.",
    """SELECT s.name, s.n_sql_interp AS sql_interp,
        s.n_sql_literal AS sql_literal,
        s.n_sql_sanitized AS sql_sanitized,
        s.n_ar_query AS ar_queries,
        s.fan_in,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_sql_interp > 0 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.fan_in DESC, s.n_sql_interp DESC LIMIT :lim"""),
(
    "eval-injection",
    "eval with user input (RuboCop Security/Eval)",
    "ANSWERS where eval is called, which executes arbitrary Ruby. If the input\n"
    "     is user-controlled, this is RCE.\n"
    "ACT use a parser, a DSL, or a whitelist; never eval user input.\n"
    "MISLEADS eval in a test or irb is correct. The graph sees the call but not\n"
    "     the input source.",
    """SELECT s.name, s.n_eval AS eval_calls,
        s.n_send AS send_calls,
        s.n_constantize AS constantize_calls,
        s.fan_in,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_eval > 0 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.fan_in DESC, s.n_eval DESC LIMIT :lim"""),
(
    "mass-assignment-weak-params",
    "Mass assignment without strong params (RuboCop Rails/MassAssignment)",
    "ANSWERS where params are passed directly to a model constructor or update,\n"
    "     allowing a user to set any attribute.\n"
    "ACT use permit! or require(...).permit(...).\n"
    "MISLEADS n_permit > 0 means strong params ARE used; the risk is where\n"
    "     n_params_read > 0 AND n_permit = 0.",
    """SELECT s.name, s.n_params_read AS params_reads,
        s.n_permit AS permits, s.n_permit_bang AS permit_bangs,
        s.n_mass_assign AS mass_assigns,
        s.fan_in,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_mass_assign > 0 AND s.n_permit=0 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.fan_in DESC, s.n_mass_assign DESC LIMIT :lim"""),
(
    "import-cycle",
    "Circular require dependencies (madge/circular)",
    "ANSWERS which files form a require cycle.\n"
    "ACT break the cycle by extracting shared code.\n"
    "MISLEADS cycles through test files are usually fine. Depth capped at 8.",
    """WITH RECURSIVE walk(start, current, depth) AS (
        SELECT f.id, f.id, 0 FROM files f WHERE f.is_test=0
        UNION
        SELECT w.start, i.target_id, w.depth+1
        FROM walk w JOIN imports i ON i.file_id=w.current
        WHERE w.depth < 8 AND i.target_id IS NOT NULL AND i.is_external=0)
    SELECT f.path, MIN(w.depth) AS shortest_cycle,
        f.path || ':' || 0 AS at
    FROM walk w JOIN files f ON f.id=w.current
    WHERE w.start = w.current AND w.depth > 0
    GROUP BY f.id
    ORDER BY shortest_cycle ASC LIMIT :lim"""),
(
    "thread-coupling",
    "Thread.new or Ractor.new coupling (RuboCop ThreadSafety)",
    "ANSWERS where threads or ractors are spawned, which introduces concurrency.\n"
    "     Without proper synchronization, shared state can race.\n"
    "ACT ensure shared state is synchronized (Mutex) or use message passing.\n"
    "MISLEADS a thread in a test or a background job framework is correct.\n"
    "     The graph sees the spawn but not the synchronization.",
    """SELECT s.name, s.n_thread_new AS thread_news,
        s.n_ractor AS ractor_news,
        s.n_mutex AS mutexes,
        s.n_timeout AS timeouts,
        s.fan_in, s.cyclomatic AS cyclo,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE (s.n_thread_new + s.n_ractor) > 0 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.fan_in DESC,
        s.n_thread_new + s.n_ractor DESC LIMIT :lim"""),
(
    "monkey-patch-surface",
    "Class reopening or module inclusion that modifies existing classes (RuboCop)",
    "ANSWERS where a class is reopened or a module is included/prepended into an\n"
    "     existing class, changing its behavior globally.\n"
    "ACT prefer composition over monkey-patching; if patching, scope it narrowly.\n"
    "MISLEADS Rails and most Ruby frameworks monkey-patch extensively; the\n"
    "     pattern is idiomatic but risky for non-framework code.",
    """SELECT s.name, s.n_monkey_patch AS monkey_patches,
        s.n_mixins AS mixins,
        s.n_define_method AS define_methods,
        s.n_method_missing AS method_missing,
        s.n_alias AS aliases,
        s.fan_in,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE (s.n_monkey_patch + s.n_mixins + s.n_define_method) > 0
      AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.fan_in DESC,
        s.n_monkey_patch + s.n_mixins DESC LIMIT :lim"""),
(
    "ancestor-chain-depth",
    "Superclass depth per class: the monkey-patch resistance meter",
    "ANSWERS how many superclass hops sit between each class and the root of\n"
    "     its inheritance tree. Deep ancestry is where a superclass change\n"
    "     ripples widest and where an include/extend mixin has the most\n"
    "     intervening method-lookup layers to cut through.\n"
    "ACT prefer composition below ~4 levels; at minimum, the deep rows are\n"
    "     the ones to watch when an ancestor changes.\n"
    "MISLEADS walks the superclass TEXT column by exact name, so a\n"
    "     superclass spelled with a different constant path (`Foo::Bar` vs\n"
    "     `Bar` where Bar is a wrapper) breaks the chain at that hop; depth\n"
    "     is capped at 8 (the recursion bound) and includes/extend depth is\n"
    "     NOT counted -- only `class X < Y` ancestry, which matches the\n"
    "     compiler-enforced single-inheritance chain.",
    """WITH RECURSIVE anc(klass, parent, depth) AS (
        SELECT m.name, m.superclass, 1
        FROM ruby_modules m
        WHERE m.superclass <> ''
        UNION ALL
        SELECT anc.klass, m2.superclass, anc.depth+1
        FROM anc JOIN ruby_modules m2 ON m2.name=anc.parent
        WHERE m2.superclass <> '' AND m2.name <> anc.klass
          AND anc.depth < 8)   -- depth bound: 8 hops
    SELECT klass, MAX(depth) AS depth,
        COUNT(DISTINCT parent) AS distinct_ancestors
    FROM anc
    WHERE EXISTS (SELECT 1 FROM ruby_modules rm
                  JOIN symbols s3 ON s3.id=rm.symbol_id
                  JOIN modules m3 ON m3.id=s3.module_id
                  WHERE rm.name=anc.klass
                    AND COALESCE(m3.name,'') LIKE :mod)
    GROUP BY klass
    ORDER BY depth DESC, distinct_ancestors DESC LIMIT :lim"""),
(
    "yield-hubs",
    "Methods that hand control to a block via yield",
    "ANSWERS which methods are callback processing hubs: every `yield`\n"
    "     passes control to whatever block the caller supplied, so a method\n"
    "     dense in yields is the funnel through which behavior is injected.\n"
    "ACT a method yielding in a loop should be documented as a hook; each\n"
    "     yield is a contract point with the caller's block.\n"
    "MISLEADS counts yield KEYWORDS, not distinct block receivers; `yield`\n"
    "     inside a nested lambda in the same method still counts to the\n"
    "     method, and a method that yields through a helper (block.call in\n"
    "     another method) is hidden. block-vs-proc-cost covers the passing\n"
    "     side.",
    """SELECT s.name, s.kind, s.n_yield AS yields,
        s.n_blocks AS blocks, s.max_loop_depth AS depth, s.fan_in,
        s.n_calls, s.sloc,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_yield > 0 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.n_yield DESC, s.fan_in DESC LIMIT :lim"""),
(
    "attr-coupling",
    "Classes exposing state through attr_accessor/reader/writer",
    "ANSWERS which classes publish read/write access to their instance\n"
    "     state via attribute macros -- the coupling surface that makes\n"
    "     internal fields public API. High writer counts mean mutation from\n"
    "     outside; high reader-only counts mean the class is more a data\n"
    "     holder than an object.\n"
    "ACT every attr_accessor is an invitation to mutate from outside: prefer\n"
    "     attr_reader plus a method that changes state with intent.\n"
    "MISLEADS counts the macro DECLARATIONS (one per attribute), not the\n"
    "     generated method call sites; `attr` and `class_attribute` are\n"
    "     grouped with reader; a `mattr_`/`cattr_` variant is counted as an\n"
    "     accessor on the class rather than the instance.",
    """SELECT s.name, s.n_attr_accessor AS accessors,
        s.n_attr_reader AS readers, s.n_attr_writer AS writers,
        s.n_attr_accessor + s.n_attr_reader + s.n_attr_writer AS total_attrs,
        s.sloc, s.fan_in,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE (s.n_attr_accessor + s.n_attr_reader + s.n_attr_writer) > 0
      AND f.is_test=0 AND COALESCE(m.name,'') LIKE :mod
    ORDER BY total_attrs DESC, s.fan_in DESC LIMIT :lim"""),
(
    "heavy-mixins",
    "Modules and concerns included by the most classes",
    "ANSWERS which mixin surfaces spread across the widest class set -- the\n"
    "     gems and core modules every host pulls in, and the ones whose\n"
    "     method-name collisions hurt the most hosts at once.\n"
    "ACT a mixin included by many classes is a coupling axis: changing its\n"
    "     methods changes every host. Keep it stable or split it.\n"
    "MISLEADS counts distinct HOSTS per mixin text, so the same mixin\n"
    "     spelled with and without a namespace prefix splits into two rows;\n"
    "     `include`/`extend`/`prepend` all count equally although the\n"
    "     method-lookup position differs.",
    """SELECT mx.mixin_short AS mixin_, COUNT(DISTINCT mx.host) AS hosts,
        COUNT(DISTINCT CASE WHEN mx.kind='prepend' THEN mx.host END)
            AS prepended_by,
        COUNT(DISTINCT CASE WHEN mx.kind='extend' THEN mx.host END)
            AS extended_by,
        GROUP_CONCAT(DISTINCT mx.kind) AS via,
        f.path || ':' || MIN(mx.line) AS at_any
    FROM mixins mx JOIN files f ON f.id=mx.file_id
    LEFT JOIN modules m ON m.id=f.module_id
    WHERE COALESCE(m.name,'') LIKE :mod
    GROUP BY mx.mixin_short
    ORDER BY hosts DESC, prepended_by DESC LIMIT :lim"""),
(
    "super-overrides",
    "Methods that call super: the override surface",
    "ANSWERS every method whose body reaches back to its ancestor via\n"
    "     `super` -- the precise list of behavioral overrides in this tree.\n"
    "     Each row is a place where the subclass extends, wraps or replaces\n"
    "     the superclass contract.\n"
    "ACT an override with no super-call is a complete replacement; one with\n"
    "     super is a hook. Code review should treat the two differently.\n"
    "MISLEADS counts `super` keywords per method; `super` with explicit\n"
    "     arguments and bare `super` both count once, and a super written as\n"
    "     a delegated message (super.send(:x)) is not seen.",
    """SELECT s.name, s.n_super AS supers,
        s.n_params AS params, s.cyclomatic AS cyclo, s.fan_in,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_super > 0 AND s.kind='method' AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.n_super DESC, s.fan_in DESC LIMIT :lim"""),
(
    "unused-private",
    "Private methods nothing in this class calls",
    "ANSWERS private/protected methods with no resolved caller anywhere --\n"
    "     the internal helpers that nobody invokes. In Ruby, where method\n"
    "     calls through `send` and dynamic dispatch are idiomatic, this is a\n"
    "     candidate list rather than a proof of death.\n"
    "ACT grep the method name as a string before deleting: a symbol call,\n"
    "     a DSL callback, or a `send(:method)` keeps it alive invisibly.\n"
    "MISLEADS visibility comes from the method's declared visibility; a\n"
    "     method called through send/instance_exec/define_method looks\n"
    "     uncalled here, and a private method called ON ITSELF inside the\n"
    "     class counts only if resolution followed the receiver.",
    """SELECT s.name, s.visibility,
        s.n_calls AS calls, s.cyclomatic AS cyclo, s.sloc,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.kind='method' AND s.is_public=0 AND s.visibility IN ('private','protected')
      AND s.fan_in=0 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.sloc DESC LIMIT :lim"""),
(
    "nested-iterators",
    "Methods iterating inside an iteration (reek NestedIterators)",
    "ANSWERS methods with blocks at iteration depth >= 2: the accidental\n"
    "     O(n*m). Each nested level multiplies the work by the outer size.\n"
    "ACT flatten, pluck, or push the inner query into SQL.\n"
    "MISLEADS matrix pipelines and group_by chains are legitimately nested;\n"
    "     depth counts blocks, not data size -- rank by queries_inside\n"
    "     first, because an inner AR query is the expensive half.",
    """SELECT f.path, s.name, COUNT(*) AS nested_iters, MAX(b.depth) AS max_depth,
        SUM(b.n_queries) AS queries_inside
    FROM blocks b
    JOIN symbols s ON s.id = b.symbol_id
    JOIN files f ON f.id = b.file_id
    LEFT JOIN modules m ON m.id = s.module_id
    WHERE b.is_iteration = 1 AND b.depth >= 2
      AND f.is_generated = 0 AND f.is_test = 0 AND COALESCE(m.name,'') LIKE :mod
    GROUP BY b.symbol_id
    ORDER BY queries_inside DESC, nested_iters DESC
    LIMIT :lim"""),
(
    "feature-envy",
    "Methods whose calls mostly leave the object (reek FeatureEnvy)",
    "ANSWERS methods whose foreign calls dominate self calls: the method\n"
    "     wants to move to the class it keeps calling. Each row is a\n"
    "     placement smell -- the data it works on lives elsewhere.\n"
    "ACT move it to the envied class, or extract a value object.\n"
    "MISLEADS DSL receivers, delegation one-liners and AR association\n"
    "     proxies all read as envy; is_self is receiver-text based, so a\n"
    "     call through a local (`items.map`) counts as foreign even when\n"
    "     `items` is the method's own parameter -- which is the point for\n"
    "     params-heavy helpers but noise for pure functions.",
    """SELECT s.name, f.path,
        SUM(CASE WHEN e.is_self = 0 THEN e.n_calls ELSE 0 END) AS foreign_calls,
        SUM(CASE WHEN e.is_self = 1 THEN e.n_calls ELSE 0 END) AS self_calls
    FROM edges e
    JOIN symbols s ON s.id = e.caller_id
    JOIN files f ON f.id = s.file_id
    LEFT JOIN modules m ON m.id = s.module_id
    WHERE f.is_generated = 0 AND f.is_test = 0 AND COALESCE(m.name,'') LIKE :mod
    GROUP BY e.caller_id
    HAVING foreign_calls >= 5 AND foreign_calls > 2 * self_calls
    ORDER BY foreign_calls DESC
    LIMIT :lim"""),
(
    "debugger-surface",
    "binding.pry / debugger / byebug left in application code",
    "ANSWERS the debugger entry points in non-test code: a binding.pry\n"
    "     shipped to production is an interactive session waiting for a\n"
    "     stdin, and byebug breaks under load in the same way.\n"
    "ACT remove before shipping; gate the debugger behind an env flag if it\n"
    "     must survive in the tree.\n"
    "MISLEADS name-based on unresolved calls, so a wrapper around\n"
    "     binding.pry hides it; a debugger behind a development-only\n"
    "     constant is still reported (the row is the review list); test\n"
    "     files are excluded by is_test.",
    """SELECT f.path, s.name, uc.name AS debugger, uc.n, uc.first_line, s.fan_in
    FROM unresolved_calls uc
    JOIN symbols s ON s.id = uc.caller_id
    JOIN files f ON f.id = s.file_id
    LEFT JOIN modules m ON m.id = s.module_id
    WHERE uc.name IN ('binding.pry','byebug','debugger','binding.irb')
      AND f.is_generated = 0 AND f.is_test = 0 AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.fan_in DESC, uc.n DESC
    LIMIT :lim"""),
(
    "unscoped-find-params",
    "find / find_by / where with params and no visible scope (brakeman)",
    "ANSWERS AR lookups fed straight from params: unscoped find. Without an\n"
    "     explicit default scope or tenant filter, params[:id] from one\n"
    "     tenant can read another tenant's row.\n"
    "ACT scope the query to the current account/tenant before the find, or\n"
    "     whitelist the param.\n"
    "MISLEADS from_params is an ARGUMENT-SHAPE flag: params[:id] inside a\n"
    "     method that is itself called with a scoped relation is invisible\n"
    "     (the flag looks at the literal argument, not data flow); a\n"
    "     controller that scopes first then finds is still reported if the\n"
    "     find call's own argument is params-derived.",
    """SELECT f.path, s.name, aq.model, aq.api, aq.build_kind, aq.loop_depth,
        s.fan_in
    FROM ar_queries aq
    JOIN symbols s ON s.id = aq.symbol_id
    JOIN files f ON f.id = aq.file_id
    LEFT JOIN modules m ON m.id = s.module_id
    WHERE aq.from_params = 1
      AND aq.api IN ('find','find_by','find_by!','first','last','take','where')
      AND f.is_generated = 0 AND f.is_test = 0 AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.fan_in DESC
    LIMIT :lim"""),
(
    "find-each-missed",
    "Model.all.each with a query inside the block",
    "ANSWERS the accidental N+1 in its most mechanical form: iterate\n"
    "     EVERY row of a model, and run a query inside the loop.\n"
    "ACT switch to find_each / find_in_batches; or preload and use the\n"
    "     association, which is one query.\n"
    "MISLEADS the block receiver is text (`User.all.each`); a variable\n"
    "     holding the collection reads as 'other' and is missed; n_queries\n"
    "     counts AR calls inside the block body, so a loop that does no\n"
    "     querying is excluded by the HAVING.",
    """SELECT f.path, s.name, b.receiver, b.line, b.n_queries, s.fan_in
    FROM blocks b
    JOIN symbols s ON s.id = b.symbol_id
    JOIN files f ON f.id = b.file_id
    LEFT JOIN modules m ON m.id = s.module_id
    WHERE b.is_iteration = 1
      AND instr(b.receiver, '.all') > 0
      AND b.n_queries > 0
      AND f.is_generated = 0 AND f.is_test = 0 AND COALESCE(m.name,'') LIKE :mod
    ORDER BY b.n_queries DESC, s.fan_in DESC
    LIMIT :lim"""),
(
    "unsafe-deserialization",
    "Marshal.load / YAML.load / Psych.load sites (brakeman UnsafeDeserialization)",
    "ANSWERS the deserialization entry points that can turn attacker bytes\n"
    "     into object construction: Marshal.load on any untrusted input is\n"
    "     remote code execution, and YAML.load is the same in legacy Psych.\n"
    "ACT feed untrusted bytes only to the safe forms: YAML.safe_load,\n"
    "     Psych.safe_load, Marshal never; JSON.load is listed but JSON\n"
    "     cannot construct objects.\n"
    "MISLEADS the capture is the deserialize hazard family, which includes\n"
    "     JSON.load and Oj.load -- rows whose payload cannot execute; the\n"
    "     data origin is NOT tracked, so a Marshal.load on a server-side\n"
    "     constant ranks the same as one on a cookie.",
    """SELECT f.path, s.name, h.pattern AS api, h.n AS sites, h.first_line,
        s.fan_in
    FROM hazards h
    JOIN symbols s ON s.id = h.symbol_id
    JOIN files f ON f.id = s.file_id
    LEFT JOIN modules m ON m.id = s.module_id
    WHERE h.category = 'deserialize'
      AND f.is_generated = 0 AND f.is_test = 0 AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.fan_in DESC, h.n DESC
    LIMIT :lim"""),
(
    "save-without-bang",
    "save (no bang) with the boolean result discarded (Rails/SaveBang)",
    "ANSWERS save calls whose false-on-failure result is thrown away: the\n"
    "     failure is invisible to the caller, and in a callback the save can\n"
    "     silently not happen. rubocop-rails wants save! for this shape.\n"
    "ACT use save! in callbacks and let the exception propagate, or handle\n"
    "     the false branch explicitly.\n"
    "MISLEADS the discard is positional (expression statement): a save whose\n"
    "     result feeds an if (`if record.save`) is correctly absent; save on\n"
    "     a bare receiver that is a method call (a relation) is excluded by\n"
    "     construction; validation-false is the common failure and is not\n"
    "     distinguished from an IO failure.",
    """SELECT f.path, s.name, s.n_save_ignored AS ignored_saves,
        s.n_ar_write AS writes, s.fan_in
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_save_ignored > 0 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.n_save_ignored DESC, s.fan_in DESC
    LIMIT :lim"""),
(
    "legacy-enumerable-idioms",
    "select.first / map.flatten / reverse.each chains (fasterer)",
    "ANSWERS the three chain pairs with a dedicated idiom: select{}.first is\n"
    "     find{}, map{}.flatten is flat_map{}, reverse.each is\n"
    "     reverse_each -- each saves an intermediate array or a pass.\n"
    "ACT swap to the dedicated form; the change is mechanical.\n"
    "MISLEADS text-matched on the chain receiver: `xs.select(&:x).first`\n"
    "     matches, `ys.select(...)` with the call split across a local does\n"
    "     not; a select that is genuinely cheaper than find (all matches\n"
    "     needed elsewhere) still reads as a violation.",
    """SELECT f.path, s.name, s.n_legacy_chain AS legacy_chains,
        s.n_ar_query AS queries, s.fan_in
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_legacy_chain > 0 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.n_legacy_chain DESC, s.fan_in DESC
    LIMIT :lim"""),
(
    "param-clumps",
    "Three or more methods sharing the same parameter set (reek DataClump)",
    "ANSWERS the parameter tuples repeated across methods: a DataClump is\n"
    "     the raw material of a missing value object. Each row names the\n"
    "     shared tuple and how many methods carry it.\n"
    "ACT extract a value object (or a positional struct) and pass it once.\n"
    "MISLEADS the tuple is grouped as WRITTEN (parameter order matters):\n"
    "     two methods with the same params in different orders read as\n"
    "     different clumps; common framework params (request, response)\n"
    "     appear in every method of a class and dominate the list; a\n"
    "     one-off two-method pair is excluded by the HAVING.",
    """WITH sigs(symbol_id, names) AS (
        SELECT p.symbol_id, GROUP_CONCAT(p.name, ',')
        FROM params p GROUP BY p.symbol_id
    )
    SELECT names, COUNT(*) AS n_methods,
        COUNT(DISTINCT s.file_id) AS n_files
    FROM sigs JOIN symbols s ON s.id = sigs.symbol_id
    JOIN files f ON f.id = s.file_id
    LEFT JOIN modules m ON m.id = s.module_id
    WHERE s.kind = 'method' AND f.is_generated = 0 AND f.is_test = 0
      AND COALESCE(m.name,'') LIKE :mod
      AND length(names) - length(replace(names, ',', '')) + 1 >= 3
    GROUP BY names
    HAVING n_methods >= 3
    ORDER BY n_methods DESC, n_files DESC
    LIMIT :lim"""),
(
    "typing-coverage",
    "Methods in sig-using classes that have no sig (sorbet adoption gaps)",
    "ANSWERS public methods missing a sig{} in files where sorbet is in use:\n"
    "     the untyped gap. A class that typed one method proves the author\n"
    "     is adopting sorbet -- the untyped ones are the remainder.\n"
    "ACT add sig{} to the method; if it is deliberately untyped (dynamic\n"
    "     dispatch), say so with a T.untyped comment.\n"
    "MISLEADS has_sig is the prev-sibling text: `sig` on the line before the\n"
    "     def; a sig separated by a comment or wrapped in a helper reads as\n"
    "     absent; files that never use sorbet are excluded by the EXISTS,\n"
    "     so the rows are the ADOPTION gaps, not a raw typing census.",
    """SELECT f.path, s.name,
        (SELECT COUNT(*) FROM symbols m2 JOIN files f2 ON f2.id=m2.file_id
          WHERE f2.id = f.id AND m2.kind='method' AND m2.has_sig=1)
            AS sigs_in_file,
        s.fan_in, s.sloc
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.kind='method' AND s.has_sig = 0 AND s.is_public = 1
      AND EXISTS (SELECT 1 FROM symbols m2
                   WHERE m2.file_id = f.id AND m2.has_sig = 1)
      AND f.is_generated = 0 AND f.is_test = 0 AND COALESCE(m.name,'') LIKE :mod
    ORDER BY sigs_in_file DESC, s.sloc DESC
    LIMIT :lim""")
]

RubyAnalyzer.METRICS = [
(
    "graph-blindspots",
    "Read this first: Ruby's call graph is a lower bound, and here is by how much",
    "ANSWERS how much of every other answer in this catalogue is guesswork.\n"
    "     In every other language this query is a footnote. In Ruby it is the\n"
    "     headline: send, public_send, define_method, method_missing,\n"
    "     const_get and constantize move dispatch out of the syntax tree\n"
    "     entirely, and class_eval on a heredoc defines methods in text this\n"
    "     parser never sees as code. None of that leaves an edge. Every\n"
    "     fan_in, every dead-code claim and every taint path below is a FLOOR.\n"
    "ACT read pct_opaque before you act on any other query for that module. A\n"
    "     module over about 20 percent is one where 'nothing calls this' means\n"
    "     'no LITERAL call site exists' and nothing more. dynamic_meta is the\n"
    "     subset whose argument is not a literal symbol -- those are not even\n"
    "     resolvable in principle without running the program.\n"
    "MISLEADS the receiver is NOT typed -- `api` matches on the method name\n"
    "     alone, so first, size, to_a, empty? and any? on a plain Array or\n"
    "     Hash count as queries. A row whose model column is a local variable\n"
    "     or a CONSTANT is one of those.\n"
    "     this UNDER-counts twice over. Name-based resolution happily\n"
    "     resolves a call to `each` onto whichever single method named `each`\n"
    "     exists in the tree, which produces a confident edge that may be\n"
    "     wrong -- so `resolved` is not the same as `correct`. And external\n"
    "     calls are excluded from pct_opaque on purpose: File.read leaving the\n"
    "     tree is design, not blindness.",
    """SELECT m.name AS module_, COUNT(DISTINCT s.id) AS methods_,
        COALESCE(SUM(s.n_calls),0) AS calls,
        COALESCE(SUM(s.n_external_calls),0) AS external,
        COALESCE(SUM(s.n_unresolved_calls),0) AS unresolved,
        COALESCE(SUM(s.n_metaprogram_total),0) AS meta,
        COALESCE(SUM(s.n_metaprogram_dynamic),0) AS dynamic_meta,
        COALESCE(SUM(s.n_send),0) AS send_,
        COALESCE(SUM(s.n_define_method),0) AS define_method,
        COALESCE(SUM(s.n_method_missing),0) AS method_missing,
        COALESCE(SUM(s.n_class_eval + s.n_instance_eval + s.n_eval),0) AS evals,
        CAST(100.0 * (SUM(s.n_unresolved_calls) + SUM(s.n_metaprogram_total))
             / NULLIF(SUM(s.n_calls),0) AS INT) AS pct_opaque
    FROM symbols s JOIN modules m ON m.id = s.module_id
    WHERE s.kind = 'method' AND m.name LIKE :mod
    GROUP BY m.id HAVING calls > 0
    ORDER BY (SUM(s.n_metaprogram_total) + SUM(s.n_unresolved_calls)) DESC
    LIMIT :lim"""),
(
    "block-vs-proc-cost",
    "Block, proc and symbol-to-proc allocation on the methods called most",
    "ANSWERS the per-call allocation a hot method pays for its own\n"
    "     conveniences. rubocop-performance names four of these:\n"
    "     RedundantBlockCall (block.call is slower than yield),\n"
    "     BlockGivenWithExplicitBlock (an explicit &block param allocates a\n"
    "     Proc just to ask whether one was passed), MethodObjectAsBlock, and\n"
    "     TimesMap.\n"
    "ACT prefer yield over an explicit &block parameter; `&:sym` is faster\n"
    "     than `{ |x| x.sym }` and allocates less; a block passed with & to a\n"
    "     method that only yields is a Proc allocated for nothing.\n"
    "MISLEADS fan_in is static call sites, not call frequency, so a method\n"
    "     with fan_in 2 inside the hottest loop in the app outranks everything\n"
    "     here and does not appear. Nothing on this list is a finding without\n"
    "     a benchmark; it is a candidate list for one.",
    """SELECT s.name, COALESCE(m.name,'') AS module_,
        s.n_blocks AS blocks_, s.n_iter_blocks AS iter_blocks,
        s.n_block_pass AS block_pass, s.n_symbol_to_proc AS sym_to_proc,
        s.n_block_given AS block_given, s.n_yield AS yields,
        s.n_proc_new AS proc_new, s.n_lambda AS lambdas,
        s.n_times_map AS times_map, s.max_block_depth AS depth,
        s.fan_in, s.n_callsites AS sites,
        (s.n_block_pass*2 + s.n_proc_new*3 + s.n_lambda*2 + s.n_times_map*3
         + (CASE WHEN s.n_block_given > 0 AND s.n_block_pass > 0
                 THEN 4 ELSE 0 END)) * MAX(s.fan_in, 1) AS payoff,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id = s.file_id
    LEFT JOIN modules m ON m.id = s.module_id
    WHERE (s.n_block_pass + s.n_proc_new + s.n_lambda + s.n_times_map) > 0
      AND f.is_test = 0 AND f.is_generated = 0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY payoff DESC LIMIT :lim"""),
(
    "frozen-literal-debt",
    "Files without frozen_string_literal, ranked by how much they allocate",
    "ANSWERS which files pay for string allocation they could get for free.\n"
    "     Without the magic comment every literal allocates a new String each\n"
    "     time it is evaluated -- in a loop or a hot method that is pure GC\n"
    "     pressure, and Ruby's allocator does not return the pages to the OS.\n"
    "ACT add `# frozen_string_literal: true` at the top of the file, then fix\n"
    "     whatever breaks -- anything that mutates a literal in place. The\n"
    "     files listed first are where the win is largest.\n"
    "MISLEADS the magic comment is per FILE, so this ranks files by the worst\n"
    "     method inside them. A file with one hot method and forty cold ones\n"
    "     scores as high as one that is hot throughout.",
    """SELECT s.name, s.qual_name AS qual,
        s.has_frozen_literal AS frozen_pragma,
        s.n_str_lit_in_loop AS str_lits_in_loop,
        s.n_string_interp AS interpolations, s.n_dup_clone AS dup_clone,
        s.n_freeze AS freezes, s.max_loop_depth AS depth, s.fan_in,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.has_frozen_literal = 0
      AND (s.n_str_lit_in_loop > 0 OR s.n_string_interp > 2)
      AND f.is_test=0 AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.n_str_lit_in_loop * (1 + s.fan_in) DESC,
        s.n_string_interp DESC LIMIT :lim"""),
(
    "hot-multipliers",
    "Where one fix pays back many times: highest fan-in",
    "ANSWERS which symbols the rest of the tree leans on hardest.\n"
    "ACT a correctness or speed win in a high-fan-in leaf pays back once per\n"
    "     caller. Read it next to sloc: a large fan_in on a tiny function is\n"
    "     usually a name collision rather than a hot leaf.\n"
    "MISLEADS fan_in counts STATIC call sites this parser could resolve, not\n"
    "     runtime frequency, and test callers are included -- in most repos a\n"
    "     test helper outranks production code. Scope with --module first.",
    """SELECT s.name, s.fan_in, s.n_callsites AS sites, s.fan_out,
        s.cyclomatic AS cyclo, s.sloc, s.kind,
        COALESCE(m.name,'') AS module_,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.fan_in > 0 AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.fan_in DESC, s.cyclomatic DESC LIMIT :lim"""),
(
    "risk-ranked",
    "Review order: if you can only read N symbols this week, which N",
    "ANSWERS which code combines complexity with the operations this language\n"
    "     punishes hardest.\n"
    "ACT start at the top. The weights are this analyzer's own -- read\n"
    "     --schema for the formula rather than assuming it matches another\n"
    "     language's.\n"
    "MISLEADS a heuristic, not a finding. Generated and vendored files are\n"
    "     excluded by default, so the real top of the list may sit in code\n"
    "     this filter hid.",
    """SELECT s.name, s.risk_score AS risk, s.cyclomatic AS cyclo,
        s.cognitive AS cog, s.max_nesting AS nest, s.n_hazards AS hazards,
        s.fan_in, s.sloc, f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.risk_score > 0 AND f.is_generated=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.risk_score DESC LIMIT :lim"""),
(
    "parse-coverage",
    "What this run could not read",
    "ANSWERS whether the numbers above cover the code you think they cover.\n"
    "ACT a file with parsed=0 contributed nothing at all; one with errors\n"
    "     contributed only the symbols around the damage. Check meta for\n"
    "     grammar_note before concluding the code is broken -- several\n"
    "     grammars here are a version behind their language.\n"
    "MISLEADS a file can parse perfectly and still be misunderstood. This\n"
    "     shows hard failures only, never wrong interpretations.",
    """SELECT f.path, f.lines, f.bytes, f.n_parse_errors AS error_nodes,
        f.n_missing_nodes AS missing, f.parsed,
        f.is_generated AS generated, f.is_test AS test, f.is_vendored AS vendored
    FROM files f
    LEFT JOIN modules m ON m.id=f.module_id
    WHERE (f.n_parse_errors > 0 OR f.parsed = 0)
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY f.n_parse_errors DESC, f.lines DESC LIMIT :lim"""),
(
    "deep-nesting",
    "Functions with excessive nesting depth (RuboCop Style/NestedTernary)",
    "ANSWERS where a function has max_nesting > 4, making it hard to read.\n"
    "ACT extract nested blocks; use early returns or guard clauses.\n"
    "MISLEADS Ruby blocks are not structural nesting in the same way as if/while,\n"
    "     but the column counts both. A method with a single block is nesting=1.",
    """SELECT s.name, s.max_nesting AS nesting,
        s.cyclomatic AS cyclo, s.cognitive AS cognitive,
        s.n_blocks AS blocks, s.max_block_depth AS block_depth,
        s.sloc, s.fan_in,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.max_nesting > 4 AND s.kind IN ('method','function')
      AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.max_nesting DESC, s.cyclomatic DESC LIMIT :lim"""),
(
    "too-many-params",
    "Methods with too many parameters (RuboCop Metrics/ParameterLists)",
    "ANSWERS where a method has more than 5 parameters.\n"
    "ACT use an options hash or keyword arguments.\n"
    "MISLEADS a delegate or dispatcher may need many params by design.",
    """SELECT s.name, s.n_params, s.n_optional_params,
        s.sloc, s.cyclomatic AS cyclo, s.fan_in,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_params > 5 AND s.kind IN ('method','function')
      AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.n_params DESC, s.fan_in DESC LIMIT :lim"""),
(
    "scattered-concerns",
    "A method called from many different modules (shotgun surgery)",
    "ANSWERS which methods are called from many distinct modules.\n"
    "ACT consider splitting or stabilizing the contract.\n"
    "MISLEADS a core method like `new` or `to_s` is called from everywhere.",
    """SELECT s.name, COUNT(DISTINCT m.id) AS n_caller_modules,
        s.fan_in, s.cyclomatic AS cyclo, s.sloc,
        GROUP_CONCAT(DISTINCT m.name) AS modules,
        f.path || ':' || s.line_start AS at
    FROM symbols s
    JOIN edges e ON e.callee_id=s.id
    JOIN symbols caller ON caller.id=e.caller_id
    LEFT JOIN modules m ON m.id=caller.module_id
    JOIN files f ON f.id=s.file_id
    WHERE s.kind IN ('method','function') AND f.is_test=0
      AND e.is_self=0 AND COALESCE(m.name,'') LIKE :mod
    GROUP BY s.id
    HAVING n_caller_modules > 5
    ORDER BY n_caller_modules DESC, s.fan_in DESC LIMIT :lim""")
]



ANALYZER = RubyAnalyzer()


if __name__ == "__main__":
    try:
        sys.exit(main(ANALYZER))
    except KeyboardInterrupt:
        print("\ninterrupted", file=sys.stderr)
        sys.exit(130)
