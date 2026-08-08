#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Piyush Katariya
#
# @author Piyush Katariya
"""codegraph_python.py -- parse a Python tree into a graph and query it.

Targets Python 3.15. Parses with the standard library `ast`, which is exact:
no grammar to install, no heuristics about where a block ends, and the same
notion of a syntax error the interpreter has.

That exactness has one edge, and it is the reason this file has an optional
dependency at all. `ast` parses the grammar of the interpreter RUNNING the
script. Analysing a 3.14 codebase from a 3.11 interpreter turns every file
using new syntax into a SyntaxError -- silently thinning the graph rather than
failing loudly. When `tree-sitter-python` is installed, those files are
re-parsed with the grammar instead of being dropped, and `files.n_parse_errors`
records which ones needed it.

Call resolution is name-based and says so. Python decides at runtime what
`obj.method()` means; this reads the source. Every call that cannot be pinned
to a definition is counted in `unresolved_calls` and `n_dynamic_calls`, so a
query over the call graph can ask how blind it is before you believe it.

Usage:
  python3 codegraph_python.py /path/to/repo --report
  python3 codegraph_python.py /path/to/repo --list
  python3 codegraph_python.py /path/to/repo 3 7 --limit 20
  python3 codegraph_python.py --deps"""
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
import ast
import builtins as _builtins
import csv
import hashlib
import importlib
import importlib.util
import io
import os
import re
import sqlite3
import stat
import subprocess
import sys
import time
import tokenize
from dataclasses import dataclass
from dataclasses import dataclass, field
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
        man_rows: list[tuple[str, str]] = []
        if man_rows:
            db.executemany(
                "INSERT OR REPLACE INTO meta(key,value) VALUES(?,?)",
                man_rows)

    def post_build(self, db: sqlite3.Connection) -> None:
        """Optional: anything that needs the finished graph."""

    # -- schema assembly ---------------------------------------------------
    def flush_symbols(self, db: sqlite3.Connection) -> None:
        """Write any buffered symbol rows. A no-op where there are none.

        This analyzer inserts symbols directly rather than buffering them, so
        there is nothing to flush -- but `build()` calls this unconditionally,
        and a missing method is an AttributeError at run time rather than a
        clear signal that the two halves disagree.
        """

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
        if not (0 <= idx < len(analyzer.QUERIES)):
            print("no query %d" % (idx + 1), file=sys.stderr)
            return 2
        cur = db.execute(analyzer.QUERIES[idx][3], p)
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
# lang_python.py
# codegraph_python.py -- parse a Python tree into a graph and query it.
#
# Targets Python 3.15. Parses with the standard library `ast`, which is exact:
# no grammar to install, no heuristics about where a block ends, and the same
# notion of a syntax error the interpreter has.
#
# That exactness has one edge, and it is the reason this file has an optional
# dependency at all. `ast` parses the grammar of the interpreter RUNNING the
# script. Analysing a 3.14 codebase from a 3.11 interpreter turns every file
# using new syntax into a SyntaxError -- silently thinning the graph rather than
# failing loudly. When `tree-sitter-python` is installed, those files are
# re-parsed with the grammar instead of being dropped, and `files.n_parse_errors`
# records which ones needed it.
#
# Call resolution is name-based and says so. Python decides at runtime what
# `obj.method()` means; this reads the source. Every call that cannot be pinned
# to a definition is counted in `unresolved_calls` and `n_dynamic_calls`, so a
# query over the call graph can ask how blind it is before you believe it.
#
# Usage:
#   python3 codegraph_python.py /path/to/repo --report
#   python3 codegraph_python.py /path/to/repo --list
#   python3 codegraph_python.py /path/to/repo 3 7 --limit 20
#   python3 codegraph_python.py --deps
# ==========================================================================

ts_load = load  # alias preserved from _ts

DEPS = DepSet(lang="python", deps=[
    Dep(module="tree_sitter",
        pip="tree-sitter>=0.25",
        why="only needed to read files whose syntax is newer than this "
            "interpreter; without it such files are counted as parse errors "
            "instead of being indexed",
        optional=True, verified="0.26.0"),
    Dep(module="tree_sitter_python",
        pip="tree-sitter-python>=0.25",
        why="grammar used for the same fallback; pairs with tree-sitter above",
        optional=True, verified="0.25.0"),
])

HAZARD_CATEGORIES = (
    "exec", "deserialize", "io", "net", "sql", "crypto", "reflect",
    "concurrency", "blocking", "resource", "shell",
)

HAZARD_CALLS: dict[str, str] = {
    # arbitrary code -- Bandit B102 exec_used, B307 eval
    "eval": "exec", "exec": "exec", "compile": "exec",
    "execfile": "exec", "__import__": "exec",
    # deserialization -- B301 pickle, B302 marshal, B506 yaml_load
    "pickle.load": "deserialize", "pickle.loads": "deserialize",
    "cPickle.load": "deserialize", "cPickle.loads": "deserialize",
    "dill.load": "deserialize", "dill.loads": "deserialize",
    "marshal.load": "deserialize", "marshal.loads": "deserialize",
    "shelve.open": "deserialize", "yaml.load": "deserialize",
    "yaml.unsafe_load": "deserialize", "yaml.full_load": "deserialize",
    "jsonpickle.decode": "deserialize", "torch.load": "deserialize",
    "joblib.load": "deserialize", "numpy.load": "deserialize",
    "np.load": "deserialize",
    # process execution -- B602..B607
    "os.system": "shell", "os.popen": "shell", "os.spawnl": "shell",
    "os.spawnv": "shell", "os.execv": "shell", "os.execl": "shell",
    "commands.getoutput": "shell", "commands.getstatusoutput": "shell",
    "subprocess.run": "shell", "subprocess.call": "shell",
    "subprocess.Popen": "shell", "subprocess.check_call": "shell",
    "subprocess.check_output": "shell", "subprocess.getoutput": "shell",
    "pty.spawn": "shell",
    # filesystem and stdio
    "open": "io", "os.remove": "io", "os.unlink": "io", "os.rmdir": "io",
    "os.rename": "io", "os.replace": "io", "shutil.rmtree": "io",
    "shutil.copy": "io", "shutil.move": "io", "os.chmod": "io",
    "os.chown": "io", "os.makedirs": "io", "os.walk": "io",
    "pathlib.Path.write_text": "io", "pathlib.Path.read_text": "io",
    "tempfile.mktemp": "io", "os.getcwd": "io", "os.listdir": "io",
    # network
    "socket.socket": "net", "socket.create_connection": "net",
    "requests.get": "net", "requests.post": "net", "requests.put": "net",
    "requests.delete": "net", "requests.request": "net",
    "urllib.request.urlopen": "net", "urlopen": "net",
    "httpx.get": "net", "httpx.post": "net", "httpx.request": "net",
    "aiohttp.request": "net", "http.client.HTTPConnection": "net",
    "ftplib.FTP": "net", "telnetlib.Telnet": "net", "smtplib.SMTP": "net",
    "paramiko.SSHClient": "net", "xmlrpc.client.ServerProxy": "net",
    # database
    "cursor.execute": "sql", "cursor.executemany": "sql",
    "connection.execute": "sql", "session.execute": "sql",
    "db.execute": "sql", "conn.execute": "sql",
    "sqlalchemy.text": "sql", "text": "sql",
    "objects.raw": "sql", "objects.extra": "sql",
    "django.db.connection.cursor": "sql",
    # weak crypto and randomness -- B303 md5, B311 random
    "hashlib.md5": "crypto", "hashlib.sha1": "crypto",
    "hashlib.new": "crypto", "md5.new": "crypto",
    "random.random": "crypto", "random.randint": "crypto",
    "random.choice": "crypto", "random.shuffle": "crypto",
    "random.randrange": "crypto", "random.seed": "crypto",
    "ssl._create_unverified_context": "crypto",
    "Crypto.Cipher.DES": "crypto", "Crypto.Cipher.ARC4": "crypto",
    # runtime reflection -- the reason a call graph goes blind
    "getattr": "reflect", "setattr": "reflect", "delattr": "reflect",
    "hasattr": "reflect", "globals": "reflect", "locals": "reflect",
    "vars": "reflect", "dir": "reflect",
    "importlib.import_module": "reflect", "importlib.reload": "reflect",
    "inspect.getmembers": "reflect", "inspect.signature": "reflect",
    "type": "reflect", "super": "reflect",
    "operator.attrgetter": "reflect", "operator.methodcaller": "reflect",
    # concurrency
    "threading.Thread": "concurrency", "threading.Lock": "concurrency",
    "threading.RLock": "concurrency", "threading.Event": "concurrency",
    "threading.local": "concurrency", "threading.Condition": "concurrency",
    "multiprocessing.Process": "concurrency", "multiprocessing.Pool": "concurrency",
    "concurrent.futures.ThreadPoolExecutor": "concurrency",
    "concurrent.futures.ProcessPoolExecutor": "concurrency",
    "ThreadPoolExecutor": "concurrency", "ProcessPoolExecutor": "concurrency",
    "asyncio.create_task": "concurrency", "asyncio.gather": "concurrency",
    "asyncio.ensure_future": "concurrency", "asyncio.run": "concurrency",
    "asyncio.Lock": "concurrency", "asyncio.Semaphore": "concurrency",
    "asyncio.to_thread": "concurrency", "asyncio.wait_for": "concurrency",
    "asyncio.TaskGroup": "concurrency", "asyncio.shield": "concurrency",
    "queue.Queue": "concurrency", "os.fork": "concurrency",
    # calls that stop the world -- Ruff's ASYNC family exists for these
    "time.sleep": "blocking", "os.wait": "blocking", "os.waitpid": "blocking",
    "input": "blocking", "select.select": "blocking",
    "subprocess.wait": "blocking", "lock.acquire": "blocking",
    "socket.recv": "blocking", "socket.accept": "blocking",
    # things that must be released
    "tempfile.NamedTemporaryFile": "resource", "tempfile.TemporaryFile": "resource",
    "sqlite3.connect": "resource", "psycopg2.connect": "resource",
    "pymysql.connect": "resource", "gzip.open": "resource",
    "zipfile.ZipFile": "resource", "tarfile.open": "resource",
    "mmap.mmap": "resource", "os.fdopen": "resource",
    "signal.signal": "resource", "atexit.register": "resource",
}

HAZARD_METHOD_SUFFIX: dict[str, str] = {
    "execute": "sql", "executemany": "sql", "executescript": "sql",
    "raw": "sql", "read": "io", "write": "io", "readlines": "io",
    "acquire": "concurrency", "release": "concurrency",
    "join": "concurrency", "start": "concurrency",
    "recv": "net", "send": "net", "connect": "net",
}

HAZARD_IMPORTS: dict[str, str] = {
    "pickle": "deserialize", "cPickle": "deserialize", "dill": "deserialize",
    "marshal": "deserialize", "shelve": "deserialize",
    "subprocess": "shell", "commands": "shell", "pty": "shell",
    "socket": "net", "requests": "net", "urllib": "net", "httpx": "net",
    "aiohttp": "net", "ftplib": "net", "telnetlib": "net", "paramiko": "net",
    "ctypes": "exec", "cffi": "exec",
    "threading": "concurrency", "multiprocessing": "concurrency",
    "asyncio": "concurrency", "concurrent": "concurrency",
}

SQL_TEXT_RE = re.compile(
    r'\b(SELECT|INSERT\s+INTO|UPDATE|DELETE\s+FROM|CREATE\s+TABLE|'
    r'DROP\s+TABLE|ALTER\s+TABLE|UNION\s+(?:ALL\s+)?SELECT)\b', re.I)

REDOS_RE = re.compile(r'\([^)]*[+*]\)[+*]|\[[^\]]*\][+*][+*]|'
                      r'\(\?:[^)]*[+*]\)[+*]')

BROAD_EXCEPTIONS = {"Exception", "BaseException"}

MUTABLE_DEFAULT_CALLS = {"list", "dict", "set", "bytearray", "collections.deque",
                         "defaultdict", "OrderedDict", "Counter"}

DUNDER_ENTRY = {"__main__", "main", "handler", "lambda_handler", "app"}

PY_BUILTINS = frozenset(dir(_builtins)) | {
    "self", "cls", "super", "print", "range", "len", "open",
}

STDLIB_ROOTS = frozenset(getattr(sys, "stdlib_module_names", ())) or frozenset({
    "os", "sys", "re", "json", "time", "math", "io", "abc", "ast", "csv",
    "enum", "glob", "gzip", "hmac", "http", "uuid", "copy", "dis", "gc",
    "collections", "itertools", "functools", "typing", "pathlib", "logging",
    "datetime", "hashlib", "sqlite3", "subprocess", "threading", "asyncio",
    "argparse", "dataclasses", "contextlib", "traceback", "importlib",
    "unittest", "warnings", "weakref", "inspect", "operator", "pickle",
    "random", "shutil", "socket", "string", "struct", "tempfile", "textwrap",
    "urllib", "base64", "binascii", "bisect", "calendar", "cmd", "codecs",
    "concurrent", "configparser", "ctypes", "decimal", "difflib", "email",
    "fnmatch", "fractions", "getpass", "heapq", "html", "keyword", "locale",
    "marshal", "mmap", "multiprocessing", "numbers", "platform", "pprint",
    "queue", "secrets", "select", "shlex", "signal", "site", "smtplib",
    "ssl", "stat", "statistics", "tarfile", "tokenize", "types", "unicodedata",
    "uu", "venv", "wave", "xml", "zipfile", "zlib",
})

def _sloc_of(lines: list[str], start: int, end: int) -> int:
    """Non-blank, non-comment lines -- the same rule the other eight use.

    This used to start at the function BODY, so it excluded the `def` line and
    every decorator, and it counted comments and the docstring as code. Four
    analyzers meant four different things by `sloc`.
    """
    n = 0
    for i in range(max(0, start), min(end, len(lines))):
        t = lines[i].strip()
        if t and not t.startswith("#"):
            n += 1
    return n

def _comment_lines(lines: list[str], start: int, end: int) -> int:
    """`n_comment_lines` was 0 for all 41,502 Django symbols."""
    return sum(1 for i in range(max(0, start), min(end, len(lines)))
               if lines[i].strip().startswith("#"))

def dotted(node: ast.AST) -> str:
    """`a.b.c` for an attribute/name chain, '' for anything else."""
    parts: list[str] = []
    cur: Any = node
    while True:
        if isinstance(cur, ast.Attribute):
            parts.append(cur.attr)
            cur = cur.value
        elif isinstance(cur, ast.Name):
            parts.append(cur.id)
            break
        elif isinstance(cur, ast.Call):
            cur = cur.func
        else:
            return ""
    return ".".join(reversed(parts))

def type_str(node: Optional[ast.AST]) -> str:
    if node is None:
        return ""
    try:
        return ast.unparse(node)[:120]
    except Exception:
        return ""

def type_depth(node: Optional[ast.AST]) -> int:
    """Nesting of a type annotation. `dict[str, list[Foo]]` is 3.

    A deep annotation is where a type checker gets slow and a reader gets lost;
    it also correlates with data being passed around instead of modelled.
    """
    if node is None:
        return 0
    best = 0
    for n in ast.walk(node):
        if isinstance(n, ast.Subscript):
            d, cur = 0, n
            while isinstance(cur, ast.Subscript):
                d += 1
                cur = cur.slice
            best = max(best, d)
    return best + (1 if isinstance(node, ast.Subscript) else 0)

def docstring_lines(node: ast.AST) -> int:
    if not isinstance(node, (ast.Module, ast.ClassDef, ast.FunctionDef,
                             ast.AsyncFunctionDef)):
        return 0
    doc = ast.get_docstring(node, clean=False)
    return doc.count("\n") + 1 if doc else 0

def is_dunder_main(tree: ast.Module) -> bool:
    for node in tree.body:
        if (isinstance(node, ast.If) and isinstance(node.test, ast.Compare)
                and isinstance(node.test.left, ast.Name)
                and node.test.left.id == "__name__"):
            return True
    return False

LOOP_NODES = (ast.For, ast.AsyncFor, ast.While)

BRANCH_NODES = (ast.If, ast.IfExp, ast.Match)

NEST_NODES = (ast.If, ast.For, ast.AsyncFor, ast.While, ast.With, ast.AsyncWith,
              ast.Try, ast.Match, ast.FunctionDef, ast.AsyncFunctionDef,
              ast.ClassDef)

COMP_NODES = (ast.ListComp, ast.SetComp, ast.DictComp, ast.GeneratorExp)

OPERATOR_NODES = (ast.BinOp, ast.UnaryOp, ast.BoolOp, ast.Compare,
                  ast.AugAssign, ast.Assign, ast.Subscript, ast.Attribute,
                  ast.Call, ast.Await, ast.Yield, ast.YieldFrom,
                  ast.NamedExpr, ast.Starred, ast.Slice)

class FunctionMetrics(ast.NodeVisitor):
    """Everything measurable about one function body, in a single traversal.

    Written as one pass rather than a metric per walk because a walk over a
    2,000-node body is cheap but forty of them are not, and the largest repos
    this is aimed at have a million functions.
    """

    def __init__(self, fn: ast.AST, src_lines: list[str],
                 class_stack: list[str], prune_defs: bool = False):
        #: When measuring a MODULE, stop at every nested def and class: those
        #: have symbols of their own and counting them here would double every
        #: number in the file.
        self.prune_defs = prune_defs
        self.m: dict[str, int] = {}
        self.depth = 0
        self.max_nesting = 0
        self.loop_depth = 0
        self.max_loop_depth = 0
        self.try_depth = 0
        self.cognitive = 0
        self.cyclomatic = 1
        self.operators: dict[str, int] = {}
        self.operands: dict[str, int] = {}
        self.calls: list[tuple[str, int, bool]] = []   # (name, line, is_dynamic)
        #: (kind, value, line, is_magic) -- flushed by the caller into `literals`
        self.literals: list[tuple[str, str, int, bool]] = []
        self.awaits_in_loop = 0
        self.class_stack = class_stack
        self.src_lines = src_lines
        self.fn = fn
        self._root = fn
        # `elif` is `If` inside the parent's `orelse`, so a flat 30-arm chain
        # looks 30 levels deep to a naive AST walk. Left uncorrected, every
        # dispatch table in the repo outranks every genuinely nested loop --
        # which is exactly backwards. Cognitive complexity agrees: `else if`
        # scores one point and does not raise the nesting level.
        self.elifs: set[int] = set()
        for n in ast.walk(fn):
            if isinstance(n, ast.If) and len(n.orelse) == 1 \
                    and isinstance(n.orelse[0], ast.If):
                self.elifs.add(id(n.orelse[0]))

    def bump(self, key: str, n: int = 1) -> None:
        self.m[key] = self.m.get(key, 0) + n

    # -- traversal -------------------------------------------------------
    def generic_visit(self, node: ast.AST) -> None:
        if (self.prune_defs and node is not self._root
                and isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                                      ast.ClassDef))):
            return
        nested = (isinstance(node, NEST_NODES) and node is not self._root
                  and id(node) not in self.elifs)
        loop = isinstance(node, LOOP_NODES)

        if nested:
            self.depth += 1
            self.max_nesting = max(self.max_nesting, self.depth)
        if loop:
            self.loop_depth += 1
            self.max_loop_depth = max(self.max_loop_depth, self.loop_depth)
            self.cyclomatic += 1
            self.cognitive += max(1, self.depth)
            self.bump("n_loops")
            if node.orelse:
                self.bump("n_loop_else")

        self._measure(node)

        super().generic_visit(node)

        if loop:
            self.loop_depth -= 1
        if nested:
            self.depth -= 1

    # -- per-node measurement --------------------------------------------
    def _measure(self, node: ast.AST) -> None:
        t = type(node)

        if t in (ast.If, ast.IfExp):
            self.cyclomatic += 1
            # an `elif` arm costs one point flat; only real nesting compounds
            self.cognitive += 1 if id(node) in self.elifs else max(1, self.depth)
            self.bump("n_branches")
            if id(node) in self.elifs:
                self.bump("n_elif")
            if t is ast.IfExp:
                self.bump("n_ternary")
            if self.loop_depth:
                self.bump("branch_in_loop")
        elif t is ast.Match:
            self.bump("n_switch")
            n = len(node.cases)
            self.bump("n_cases", n)
            self.cyclomatic += n
            self.bump("n_match")
        elif t is ast.BoolOp:
            n = len(node.values) - 1
            self.cyclomatic += n
            self.bump("n_logical", n)
        elif t is ast.Compare:
            self.bump("n_cmp", len(node.ops))
            for op in node.ops:
                if isinstance(op, (ast.Is, ast.IsNot, ast.Eq, ast.NotEq)):
                    for c in node.comparators:
                        if isinstance(c, ast.Constant) and c.value is None:
                            self.bump("n_null_check")
        elif t is ast.Return:
            self.bump("n_returns")
            if self.depth > 0:
                self.bump("n_early_returns")
        elif t is ast.Raise:
            self.bump("n_throw")
            if node.exc is None:
                self.bump("n_reraise")
        elif t is ast.Try or t is getattr(ast, "TryStar", ()):
            self.bump("n_try")
            if node.finalbody:
                self.bump("n_finally")
            if node.orelse:
                self.bump("n_try_else")
            if self.loop_depth:
                self.bump("try_in_loop")
        elif t is ast.ExceptHandler:
            self.bump("n_catch")
            self.cyclomatic += 1
            self.cognitive += max(1, self.depth)
            name = dotted(node.type) if node.type is not None else ""
            if node.type is None:
                self.bump("n_bare_except")
                self.bump("n_catch_broad")
            elif name in BROAD_EXCEPTIONS:
                self.bump("n_catch_broad")
            body = node.body
            if len(body) == 1 and isinstance(body[0], ast.Pass):
                self.bump("n_catch_empty")
            elif len(body) == 1 and isinstance(body[0], ast.Expr) and \
                    isinstance(body[0].value, ast.Constant):
                self.bump("n_catch_empty")
            if not any(isinstance(n2, (ast.Raise, ast.Return))
                       for n2 in ast.walk(node)):
                self.bump("n_catch_swallow")
        elif t in (ast.With, ast.AsyncWith):
            self.bump("n_with")
            self.bump("n_ctx_managers", len(node.items))
            if t is ast.AsyncWith:
                self.bump("n_async_with")
        elif t is ast.Assert:
            self.bump("n_assert")
            self.cyclomatic += 1
        elif t is ast.Global:
            self.bump("n_global_stmt", len(node.names))
        elif t is ast.Nonlocal:
            self.bump("n_nonlocal", len(node.names))
        elif t is ast.Await:
            self.bump("n_await")
            if self.loop_depth:
                self.bump("await_in_loop")
        elif t in (ast.Yield, ast.YieldFrom):
            self.bump("n_yield")
            if t is ast.YieldFrom:
                self.bump("n_yield_from")
        elif t is ast.Lambda:
            self.bump("n_lambda")
        elif t is ast.NamedExpr:
            self.bump("n_walrus")
        elif t is ast.Delete:
            self.bump("n_del", len(node.targets))
        elif t in COMP_NODES:
            self.bump("n_comprehension")
            self.bump("n_comp_generators", len(node.generators))
            if len(node.generators) > 1:
                self.bump("n_nested_comprehension")
            for g in node.generators:
                self.bump("n_comp_ifs", len(g.ifs))
                if g.is_async:
                    self.bump("n_async_comprehension")
            if t is ast.GeneratorExp:
                self.bump("n_genexp")
        elif t is ast.Assign:
            self.bump("n_assign", len(node.targets))
            self._string_build(node)
        elif t is ast.AugAssign:
            self.bump("n_compound_assign")
            if isinstance(node.op, ast.Add) and self.loop_depth:
                self.bump("concat_in_loop")
        elif t is ast.AnnAssign:
            self.bump("n_assign")
            self.bump("n_annotated_assign")
        elif t is ast.Subscript:
            self.bump("n_subscript")
        elif t is ast.Attribute:
            self.bump("n_member_access")
            if isinstance(node.value, ast.Name) and node.value.id == "self":
                self.bump("n_self_attr")
        elif t is ast.BinOp:
            if isinstance(node.op, (ast.Add, ast.Sub, ast.Mult, ast.Div,
                                    ast.FloorDiv, ast.Mod, ast.Pow)):
                self.bump("n_arith")
            elif isinstance(node.op, (ast.BitAnd, ast.BitOr, ast.BitXor)):
                self.bump("n_bitop")
            elif isinstance(node.op, (ast.LShift, ast.RShift)):
                self.bump("n_shift")
        elif t is ast.JoinedStr:
            self.bump("n_fstring")
        elif t is ast.Constant:
            self._constant(node)
        elif t is ast.Call:
            self._call(node)
        elif t is ast.ClassDef and node is not self._root:
            self.bump("n_inner_class")
        elif t in (ast.FunctionDef, ast.AsyncFunctionDef) and node is not self._root:
            self.bump("n_inner_function")

        if isinstance(node, OPERATOR_NODES):
            key = t.__name__
            self.operators[key] = self.operators.get(key, 0) + 1
        elif isinstance(node, (ast.Name, ast.Constant)):
            key = (node.id if isinstance(node, ast.Name)
                   else repr(node.value)[:40])
            self.operands[key] = self.operands.get(key, 0) + 1

    def _constant(self, node: ast.Constant) -> None:
        v = node.value
        if isinstance(v, str):
            self.bump("n_string_lit")
            if SQL_TEXT_RE.search(v):
                self.bump("n_sql_literal")
                if self.loop_depth:
                    self.bump("query_in_loop")
        elif isinstance(v, bool):
            pass
        elif isinstance(v, int):
            if v not in MAGIC_OK:
                self.bump("n_magic")
                # Every other analyzer records the literal itself; without this
                # the `literals` table stayed empty and `magic-numbers` could
                # not return a row on any input.
                self.literals.append(("number", str(v),
                                      getattr(node, "lineno", 0), True))
        elif isinstance(v, float):
            self.bump("n_float_lit")

    def _string_build(self, node: ast.Assign) -> None:
        """`s = s + x` inside a loop is quadratic. So is `.join` misuse."""
        if not self.loop_depth:
            return
        if isinstance(node.value, ast.BinOp) and isinstance(node.value.op, ast.Add):
            tgt = node.targets[0]
            if isinstance(tgt, ast.Name) and isinstance(node.value.left, ast.Name) \
                    and node.value.left.id == tgt.id:
                self.bump("concat_in_loop")

    def _call(self, node: ast.Call) -> None:
        self.bump("n_calls")
        name = dotted(node.func)
        line = node.lineno
        dynamic = not name

        if self.loop_depth:
            self.bump("call_in_loop")

        if name:
            base = name.split(".")[-1]
            if base in ("append", "extend", "insert") and self.loop_depth:
                self.bump("append_in_loop")
            if base in ("compile",) and name.startswith(("re.", "regex.")):
                self.bump("n_regex_compile")
                if self.loop_depth:
                    self.bump("regex_in_loop")
            elif name.startswith(("re.", "regex.")):
                self.bump("n_regex_call")
                if self.loop_depth:
                    self.bump("regex_in_loop")
            if base == "isinstance":
                self.bump("n_isinstance")
            if base == "super":
                self.bump("n_super")
            if base in ("len",) and self.loop_depth:
                self.bump("len_in_loop")
            if name == "range" and any(
                    isinstance(a, ast.Call) and dotted(a.func) == "len"
                    for a in node.args):
                self.bump("n_range_len")
            if base in ("open",) or name in ("open",):
                self.bump("n_open")
            if base in ("print",):
                self.bump("n_print")

            # -- facts the linters check, recorded rather than judged --------
            # Each is a counter, never a verdict: the query decides what is
            # bad and at what threshold. Rule ids are cited so a reader can go
            # read the original rationale rather than trusting this comment.
            if name in ("pickle.load", "pickle.loads", "cPickle.load",
                        "cPickle.loads", "dill.load", "dill.loads",
                        "shelve.open"):
                self.bump("n_pickle_load")          # bandit S301/S302
            if name in ("yaml.load", "yaml.unsafe_load", "yaml.full_load"):
                self.bump("n_yaml_load")            # bandit S506
            if name.startswith("random.") and base not in ("SystemRandom",):
                self.bump("n_weak_random")          # bandit S311
            if name in ("hashlib.md5", "hashlib.sha1", "md5.new"):
                self.bump("n_weak_hash")            # bandit S324
            if base in ("eval", "exec", "compile") and not name.startswith("re."):
                self.bump("n_eval_exec")            # bandit S307 / pylint W0122
            if name in ("os.system", "os.popen", "commands.getoutput"):
                self.bump("n_os_system")            # bandit S605
            if name.startswith(("tempfile.mktemp",)):
                self.bump("n_insecure_temp")        # bandit S306
            if name in ("time.sleep", "asyncio.sleep") and self.loop_depth:
                self.bump("n_sleep_in_loop")        # ruff ASYNC101 / PERF
            if base in ("getattr", "setattr", "delattr", "hasattr") and \
                    len(node.args) > 1 and not isinstance(
                        node.args[1], ast.Constant):
                self.bump("n_dynamic_attr")         # pylint / ruff B009-B010
            if base == "get" and self.loop_depth:
                self.bump("n_dict_get_in_loop")     # ruff PERF
            if base == "open" and not any(
                    k.arg == "encoding" for k in node.keywords):
                self.bump("n_open_no_encoding")     # ruff PLW1514
            if name in ("datetime.datetime.now", "datetime.now",
                        "datetime.datetime.utcnow", "datetime.utcnow") and \
                    not node.args and not node.keywords:
                self.bump("n_naive_datetime")       # ruff DTZ005/DTZ003
            if name in ("requests.get", "requests.post", "requests.put",
                        "requests.delete", "requests.patch",
                        "requests.head", "requests.request",
                        "urllib.request.urlopen") and not any(
                        k.arg == "timeout" for k in node.keywords):
                self.bump("n_request_no_timeout")   # bandit S113 / ruff ASYNC210
            if base in ("assertEquals", "assertEqual") and self.loop_depth:
                self.bump("n_assert_in_loop")
            if name in ("subprocess.run", "subprocess.call",
                        "subprocess.check_output", "subprocess.Popen",
                        "subprocess.check_call"):
                self.bump("n_subprocess")           # bandit S603
            if base in ("format",) and self.loop_depth:
                self.bump("n_format_in_loop")       # ruff PERF
            if self.loop_depth and name in HAZARD_CALLS:
                cat = HAZARD_CALLS[name]
                if cat in ("io", "net", "sql"):
                    self.bump("io_in_loop")
                if cat == "sql":
                    self.bump("query_in_loop")
            if base in ("acquire",) and self.loop_depth:
                self.bump("lock_in_loop")
            # shell=True is the difference between a call and a vulnerability
            if name.startswith("subprocess.") or name in ("os.popen",):
                for kw in node.keywords:
                    if kw.arg == "shell" and isinstance(kw.value, ast.Constant) \
                            and kw.value.value is True:
                        self.bump("n_shell_true")
            if base in ("execute", "executemany", "raw", "extra"):
                for arg in node.args[:1]:
                    if isinstance(arg, (ast.JoinedStr,)):
                        self.bump("n_sql_fstring")
                    elif isinstance(arg, ast.BinOp) and isinstance(
                            arg.op, (ast.Add, ast.Mod)):
                        self.bump("n_sql_concat")
                    elif isinstance(arg, ast.Call) and dotted(arg.func).endswith(
                            ".format"):
                        self.bump("n_sql_format")
        else:
            self.bump("n_dynamic_calls")

        self.calls.append((name, line, dynamic))

class PythonAnalyzer(Analyzer):
    LANG = "python"
    TARGET = "Python 3.15 (stdlib ast; grammar fallback for newer syntax)"
    EXTS = (".py", ".pyi", ".pyw")
    SKIP_DIRS = {"site-packages", ".eggs", "migrations"}
    DEPS = DEPS
    HAZARD_CATEGORIES = HAZARD_CATEGORIES
    MANIFESTS = ("pyproject.toml", "setup.py", "setup.cfg", "requirements.txt")
    QUERIES = []          # filled in below, after the catalogue is defined

    EXTRA_SYMBOL_COLS = (
        ("n_decorators", "INT NOT NULL DEFAULT 0"),
        ("n_comprehension", "INT NOT NULL DEFAULT 0"),
        ("n_nested_comprehension", "INT NOT NULL DEFAULT 0"),
        ("n_async_comprehension", "INT NOT NULL DEFAULT 0"),
        ("n_comp_generators", "INT NOT NULL DEFAULT 0"),
        ("n_comp_ifs", "INT NOT NULL DEFAULT 0"),
        ("n_genexp", "INT NOT NULL DEFAULT 0"),
        ("n_yield", "INT NOT NULL DEFAULT 0"),
        ("n_yield_from", "INT NOT NULL DEFAULT 0"),
        ("n_await", "INT NOT NULL DEFAULT 0"),
        ("n_global_stmt", "INT NOT NULL DEFAULT 0"),
        ("n_nonlocal", "INT NOT NULL DEFAULT 0"),
        ("n_bare_except", "INT NOT NULL DEFAULT 0"),
        ("n_catch_swallow", "INT NOT NULL DEFAULT 0"),
        ("n_reraise", "INT NOT NULL DEFAULT 0"),
        ("n_with", "INT NOT NULL DEFAULT 0"),
        ("n_async_with", "INT NOT NULL DEFAULT 0"),
        ("n_ctx_managers", "INT NOT NULL DEFAULT 0"),
        ("n_fstring", "INT NOT NULL DEFAULT 0"),
        ("n_isinstance", "INT NOT NULL DEFAULT 0"),
        ("n_super", "INT NOT NULL DEFAULT 0"),
        ("n_walrus", "INT NOT NULL DEFAULT 0"),
        ("n_match", "INT NOT NULL DEFAULT 0"),
        ("n_assert", "INT NOT NULL DEFAULT 0"),
        ("n_del", "INT NOT NULL DEFAULT 0"),
        ("n_print", "INT NOT NULL DEFAULT 0"),
        ("n_open", "INT NOT NULL DEFAULT 0"),
        ("n_self_attr", "INT NOT NULL DEFAULT 0"),
        ("n_inner_function", "INT NOT NULL DEFAULT 0"),
        ("n_inner_class", "INT NOT NULL DEFAULT 0"),
        ("n_mutable_default", "INT NOT NULL DEFAULT 0"),
        ("n_star_args", "INT NOT NULL DEFAULT 0"),
        ("n_kwargs", "INT NOT NULL DEFAULT 0"),
        ("n_default_args", "INT NOT NULL DEFAULT 0"),
        ("n_kwonly_args", "INT NOT NULL DEFAULT 0"),
        ("n_posonly_args", "INT NOT NULL DEFAULT 0"),
        ("n_annotated_params", "INT NOT NULL DEFAULT 0"),
        ("n_untyped_params", "INT NOT NULL DEFAULT 0"),
        ("has_return_type", "INT NOT NULL DEFAULT 0"),
        ("n_append_in_loop", "INT NOT NULL DEFAULT 0"),
        ("len_in_loop", "INT NOT NULL DEFAULT 0"),
        ("append_in_loop", "INT NOT NULL DEFAULT 0"),
        ("try_in_loop", "INT NOT NULL DEFAULT 0"),
        ("n_range_len", "INT NOT NULL DEFAULT 0"),
        ("n_try_in_loop", "INT NOT NULL DEFAULT 0"),
        ("n_loop_else", "INT NOT NULL DEFAULT 0"),
        ("n_regex_compile", "INT NOT NULL DEFAULT 0"),
        ("n_regex_call", "INT NOT NULL DEFAULT 0"),
        ("n_sql_literal", "INT NOT NULL DEFAULT 0"),
        ("n_sql_fstring", "INT NOT NULL DEFAULT 0"),
        ("n_sql_concat", "INT NOT NULL DEFAULT 0"),
        ("n_sql_format", "INT NOT NULL DEFAULT 0"),
        ("n_shell_true", "INT NOT NULL DEFAULT 0"),
        ("n_annotated_assign", "INT NOT NULL DEFAULT 0"),
        ("n_try_else", "INT NOT NULL DEFAULT 0"),
        #: Facts the Python linters check, recorded so SQL can COMBINE them.
        #: Each is a count, not a judgement -- `n_pickle_load` says what the
        #: code does; whether that is a bug depends on whether untrusted input
        #: can reach it, which is a question only the call graph answers. A
        #: column costs four bytes per symbol; a fact not recorded cannot be
        #: joined to anything later.
        ("n_pickle_load", "INT NOT NULL DEFAULT 0"),        # S301/S302
        ("n_yaml_load", "INT NOT NULL DEFAULT 0"),          # S506
        ("n_weak_random", "INT NOT NULL DEFAULT 0"),        # S311
        ("n_weak_hash", "INT NOT NULL DEFAULT 0"),          # S324
        ("n_eval_exec", "INT NOT NULL DEFAULT 0"),          # S307/W0122
        ("n_os_system", "INT NOT NULL DEFAULT 0"),          # S605
        ("n_insecure_temp", "INT NOT NULL DEFAULT 0"),      # S306
        ("n_sleep_in_loop", "INT NOT NULL DEFAULT 0"),      # ASYNC101
        ("n_dynamic_attr", "INT NOT NULL DEFAULT 0"),       # B009/B010
        ("n_dict_get_in_loop", "INT NOT NULL DEFAULT 0"),   # PERF
        ("n_open_no_encoding", "INT NOT NULL DEFAULT 0"),   # PLW1514
        ("n_naive_datetime", "INT NOT NULL DEFAULT 0"),     # DTZ003/DTZ005
        ("n_request_no_timeout", "INT NOT NULL DEFAULT 0"), # S113/ASYNC210
        ("n_assert_in_loop", "INT NOT NULL DEFAULT 0"),
        ("n_subprocess", "INT NOT NULL DEFAULT 0"),         # S603
        ("n_format_in_loop", "INT NOT NULL DEFAULT 0"),     # PERF
        ("n_elif", "INT NOT NULL DEFAULT 0"),
        ("n_external_calls", "INT NOT NULL DEFAULT 0"),
        ("is_property", "INT NOT NULL DEFAULT 0"),
        ("is_classmethod", "INT NOT NULL DEFAULT 0"),
        ("is_staticmethod", "INT NOT NULL DEFAULT 0"),
        ("is_dunder", "INT NOT NULL DEFAULT 0"),
        ("is_private", "INT NOT NULL DEFAULT 0"),
        ("is_overload", "INT NOT NULL DEFAULT 0"),
        ("is_contextmanager", "INT NOT NULL DEFAULT 0"),
        ("is_cached", "INT NOT NULL DEFAULT 0"),
        ("nest_level", "INT NOT NULL DEFAULT 0"),
    )

    SCHEMA_EXT = r"""
CREATE TABLE classes(
    symbol_id INT NOT NULL PRIMARY KEY REFERENCES symbols(id),
    n_bases INT NOT NULL DEFAULT 0,
    bases TEXT NOT NULL DEFAULT '',
    n_methods INT NOT NULL DEFAULT 0,
    n_class_vars INT NOT NULL DEFAULT 0,
    n_properties INT NOT NULL DEFAULT 0,
    n_abstract_methods INT NOT NULL DEFAULT 0,
    n_dunder INT NOT NULL DEFAULT 0,
    has_slots INT NOT NULL DEFAULT 0,
    has_init INT NOT NULL DEFAULT 0,
    has_eq INT NOT NULL DEFAULT 0,
    has_hash INT NOT NULL DEFAULT 0,
    is_dataclass INT NOT NULL DEFAULT 0,
    is_abc INT NOT NULL DEFAULT 0,
    is_enum INT NOT NULL DEFAULT 0,
    is_exception INT NOT NULL DEFAULT 0,
    is_protocol INT NOT NULL DEFAULT 0,
    is_namedtuple INT NOT NULL DEFAULT 0,
    is_typeddict INT NOT NULL DEFAULT 0,
    is_pydantic INT NOT NULL DEFAULT 0,
    is_django_model INT NOT NULL DEFAULT 0,
    is_metaclass INT NOT NULL DEFAULT 0
) WITHOUT ROWID, STRICT;

CREATE TABLE handlers(
    id INTEGER PRIMARY KEY,
    symbol_id INT NOT NULL REFERENCES symbols(id),
    line INT NOT NULL,
    types TEXT NOT NULL DEFAULT '',
    is_bare INT NOT NULL DEFAULT 0,
    is_broad INT NOT NULL DEFAULT 0,
    is_empty INT NOT NULL DEFAULT 0,
    has_reraise INT NOT NULL DEFAULT 0,
    has_log INT NOT NULL DEFAULT 0,
    n_body_lines INT NOT NULL DEFAULT 0,
    in_loop INT NOT NULL DEFAULT 0
) STRICT;

CREATE TABLE dynamic_sites(
    id INTEGER PRIMARY KEY,
    symbol_id INT REFERENCES symbols(id),
    file_id INT NOT NULL REFERENCES files(id),
    kind TEXT NOT NULL,
    expr TEXT NOT NULL DEFAULT '',
    line INT NOT NULL,
    is_literal_arg INT NOT NULL DEFAULT 0
) STRICT;

CREATE TABLE comprehensions(
    id INTEGER PRIMARY KEY,
    symbol_id INT REFERENCES symbols(id),
    file_id INT NOT NULL REFERENCES files(id),
    kind TEXT NOT NULL,
    line INT NOT NULL,
    n_generators INT NOT NULL DEFAULT 0,
    n_ifs INT NOT NULL DEFAULT 0,
    is_async INT NOT NULL DEFAULT 0,
    in_loop INT NOT NULL DEFAULT 0
) STRICT;

CREATE TABLE module_vars(
    id INTEGER PRIMARY KEY,
    file_id INT NOT NULL REFERENCES files(id),
    module_id INT REFERENCES modules(id),
    name TEXT NOT NULL,
    line INT NOT NULL,
    type TEXT NOT NULL DEFAULT '',
    is_constant INT NOT NULL DEFAULT 0,
    is_mutable_container INT NOT NULL DEFAULT 0,
    is_private INT NOT NULL DEFAULT 0,
    has_call_init INT NOT NULL DEFAULT 0
) STRICT;
"""

    INDEX_EXT = r"""
CREATE INDEX idx_cls_kind ON classes(is_dataclass, is_abc, is_enum);
CREATE INDEX idx_cls_slots ON classes(symbol_id) WHERE has_slots=0;
CREATE INDEX idx_hand_broad ON handlers(symbol_id) WHERE is_broad=1;
CREATE INDEX idx_hand_empty ON handlers(symbol_id) WHERE is_empty=1;
CREATE INDEX idx_dyn_kind ON dynamic_sites(kind, symbol_id);
CREATE INDEX idx_comp_sym ON comprehensions(symbol_id, kind);
CREATE INDEX idx_mv_mutable ON module_vars(file_id) WHERE is_mutable_container=1;
CREATE INDEX idx_fn_mutdef ON symbols(n_mutable_default DESC, name, file_id)
    WHERE n_mutable_default>0;
CREATE INDEX idx_fn_bare ON symbols(n_bare_except DESC, name, file_id)
    WHERE n_bare_except>0;
CREATE INDEX idx_fn_untyped ON symbols(n_untyped_params DESC, name, file_id)
    WHERE n_untyped_params>0;
CREATE INDEX idx_fn_sqlbuild ON symbols(name, file_id)
    WHERE n_sql_fstring>0 OR n_sql_concat>0 OR n_sql_format>0;
"""

    VIEW_EXT = r"""
CREATE VIEW v_async AS
SELECT s.id, s.name, s.qual_name, f.path, m.name AS module, s.line_start,
    s.n_await, s.await_in_loop, s.n_blocking, s.sloc, s.cyclomatic,
    s.fan_in, s.fan_out, f.path || ':' || s.line_start AS at
FROM symbols s JOIN files f ON f.id=s.file_id
LEFT JOIN modules m ON m.id=s.module_id
WHERE s.is_async=1;

CREATE VIEW v_typing AS
SELECT s.id, s.name, f.path, s.n_params, s.n_annotated_params,
    s.n_untyped_params, s.has_return_type,
    CAST(100.0 * s.n_annotated_params / NULLIF(s.n_params,0) AS INT) AS pct_typed,
    f.path || ':' || s.line_start AS at
FROM symbols s JOIN files f ON f.id=s.file_id
WHERE s.kind IN ('function','method') AND f.is_generated=0;

CREATE VIEW v_taint_source AS
SELECT s.id, s.name, f.path, s.n_reflect, s.n_exec, s.n_deserialize,
    s.n_shell, s.n_shell_true, s.n_sql_fstring + s.n_sql_concat
        + s.n_sql_format AS sql_built,
    f.path || ':' || s.line_start AS at
FROM symbols s JOIN files f ON f.id=s.file_id
WHERE s.n_exec + s.n_deserialize + s.n_shell + s.n_sql_fstring
      + s.n_sql_concat + s.n_sql_format > 0;
"""

    MATERIALIZE_EXT = r"""
UPDATE symbols AS s SET n_unique_calls = x.c FROM
    (SELECT caller_id AS id, COUNT(*) AS c FROM edges GROUP BY caller_id) AS x
    WHERE x.id = s.id;

UPDATE classes AS c SET
    n_methods = x.methods, n_properties = x.props, n_dunder = x.dunders
FROM (
    SELECT parent_id AS id,
        SUM(kind='method') AS methods,
        SUM(is_property) AS props,
        SUM(is_dunder) AS dunders
    FROM symbols WHERE parent_id IS NOT NULL GROUP BY parent_id) AS x
WHERE x.id = c.symbol_id;
"""

    RISK_SQL = (
        "cyclomatic*2 + cognitive + max_nesting*4"
        " + n_exec*30 + n_deserialize*25 + n_shell*15 + n_shell_true*30"
        " + n_sql_fstring*30 + n_sql_concat*25 + n_sql_format*25"
        " + n_reflect*3 + n_net*6 + n_io*4 + n_crypto*8"
        " + n_concurrency*5 + n_blocking*4"
        " + n_bare_except*10 + n_catch_swallow*8 + n_mutable_default*12"
        " + await_in_loop*10 + query_in_loop*15 + call_in_loop*2"
        " + (CASE WHEN is_recursive THEN 15 ELSE 0 END)"
        " + (CASE WHEN has_doc=0 AND is_public=1 THEN 5 ELSE 0 END)"
    )

    # -- setup -------------------------------------------------------------
    def __init__(self) -> None:
        super().__init__()
        self.ts_fallback: Optional[ParserHandle] = None
        #: name -> [(symbol_id, file_id, module_id, parent_class)]
        self.by_name: dict[str, list[tuple[int, int, int, str]]] = {}
        self.by_qual: dict[str, int] = {}
        #: (n_mutable_default, symbol_id), flushed once in post_build
        self._mutable_defaults: list[tuple[int, int]] = []
        #: file_id -> {imported alias -> dotted target}
        self.aliases: dict[int, dict[str, str]] = {}
        #: pending calls: (caller_sid, caller_fid, caller_mid, name, line, class)
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
        self.n_ts_rescued = 0

    def setup(self) -> ParserHandle:
        h = ParserHandle(mode=MODE_NATIVE, parser=ast, lang_name="python",
                         note="CPython %s stdlib ast" % sys.version.split()[0])
        ts = ts_load("python", "tree_sitter_python", "tree-sitter-python")
        if ts.ok:
            self.ts_fallback = ts
            h.note += " (+ tree-sitter for newer-than-host syntax)"
        return h

    # -- parsing -----------------------------------------------------------
    def parse_file(self, rec: FileRec, db: sqlite3.Connection,
                   bufs: Buffers) -> None:
        try:
            # ast.parse(bytes) strips a BOM; ast.parse(str) raises
            # on it. rec.data was right there and unused.
            tree = ast.parse(rec.data or rec.text, filename=rec.rel)
        except SyntaxError as exc:
            # The host interpreter is older than the code, or the file really
            # is broken. Either way record it; do not pretend the file is empty.
            db.execute("UPDATE files SET n_parse_errors=n_parse_errors+1 "
                       "WHERE id=?", (rec.fid,))
            if self.ts_fallback is not None and self.ts_fallback.ok:
                self.n_ts_rescued += 1
            return
        except (ValueError, RecursionError):
            db.execute("UPDATE files SET n_parse_errors=n_parse_errors+1, "
                       "parsed=0 WHERE id=?", (rec.fid,))
            return

        db.execute("UPDATE files SET doc_lines=? WHERE id=?",
                   (docstring_lines(tree), rec.fid))

        self._imports(tree, rec, bufs)
        self._module_vars(tree, rec, bufs)
        src_lines = rec.text.splitlines()
        self._walk_scope(tree, rec, db, bufs, src_lines,
                         parent_id=None, qual_prefix="", class_stack=[],
                         nest=0)
        self._module_scope(tree, rec, db, bufs, src_lines)

    # -- imports -----------------------------------------------------------
    def _imports(self, tree: ast.Module, rec: FileRec, bufs: Buffers) -> None:
        alias_map = self.aliases.setdefault(rec.fid, {})
        for node in ast.walk(tree):
            if isinstance(node, ast.Import):
                for a in node.names:
                    alias_map[a.asname or a.name.split(".")[0]] = a.name
                    root = a.name.split(".")[0]
                    bufs.imports.append(
                        (rec.fid, a.name, None, a.asname, "import",
                         node.lineno, int(self._external(a.name)), 0, 0, 0, 0, 1))
                    if root in HAZARD_IMPORTS:
                        bufs.rows("import_hazard").append(
                            (rec.fid, root, HAZARD_IMPORTS[root], node.lineno))
            elif isinstance(node, ast.ImportFrom):
                mod = node.module or ""
                rel = node.level or 0
                wildcard = any(a.name == "*" for a in node.names)
                for a in node.names:
                    if a.name != "*":
                        alias_map[a.asname or a.name] = (
                            "%s.%s" % (mod, a.name) if mod else a.name)
                bufs.imports.append(
                    (rec.fid, ("." * rel) + mod, None,
                     None, "from", node.lineno,
                     int(rel == 0 and self._external(mod)), int(rel > 0),
                     int(wildcard),
                     int(any(isinstance(p, ast.If) for p in ast.walk(tree))
                         and mod == "typing"),
                     0, len(node.names)))
                root = mod.split(".")[0]
                if root in HAZARD_IMPORTS:
                    bufs.rows("import_hazard").append(
                        (rec.fid, root, HAZARD_IMPORTS[root], node.lineno))

    def _external(self, mod: str) -> bool:
        """Best-effort: a module we did not find a file for is third-party."""
        if not mod:
            return False
        head = mod.split(".")[0]
        cand = head + ".py"
        return not any(p.endswith(cand) or ("/%s/" % head) in p
                       for p in self.file_id)

    # -- module-level state ------------------------------------------------
    def _module_vars(self, tree: ast.Module, rec: FileRec, bufs: Buffers) -> None:
        """Top-level assignments. Mutable module state is where surprising
        cross-request coupling lives, and a module-level call runs at import."""
        for node in tree.body:
            targets: list[ast.expr] = []
            value: Optional[ast.expr] = None
            ann = ""
            if isinstance(node, ast.Assign):
                targets, value = node.targets, node.value
            elif isinstance(node, ast.AnnAssign) and node.value is not None:
                targets, value, ann = [node.target], node.value, type_str(
                    node.annotation)
            else:
                continue
            for tgt in targets:
                if not isinstance(tgt, ast.Name):
                    continue
                name = tgt.id
                mutable = isinstance(value, (ast.List, ast.Dict, ast.Set)) or (
                    isinstance(value, ast.Call)
                    and dotted(value.func).split(".")[-1] in
                    ("list", "dict", "set", "defaultdict", "OrderedDict",
                     "deque", "Counter"))
                bufs.rows("module_vars").append(
                    (rec.fid, rec.mid, name, node.lineno, ann,
                     int(name.isupper()), int(mutable),
                     int(name.startswith("_")),
                     int(isinstance(value, ast.Call))))

    # -- scope walk --------------------------------------------------------
    def _walk_scope(self, node: ast.AST, rec: FileRec, db: sqlite3.Connection,
                    bufs: Buffers, src_lines: list[str],
                    parent_id: Optional[int], qual_prefix: str,
                    class_stack: list[str], nest: int) -> None:
        for child in ast.iter_child_nodes(node):
            if isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef)):
                sid = self._function(child, rec, db, bufs, src_lines,
                                     parent_id, qual_prefix, class_stack, nest)
                self._walk_scope(child, rec, db, bufs, src_lines, sid,
                                 "%s%s." % (qual_prefix, child.name),
                                 class_stack, nest + 1)
            elif isinstance(child, ast.ClassDef):
                sid = self._class(child, rec, db, bufs, src_lines,
                                  parent_id, qual_prefix, nest)
                self._walk_scope(child, rec, db, bufs, src_lines, sid,
                                 "%s%s." % (qual_prefix, child.name),
                                 class_stack + [child.name], nest + 1)
            elif isinstance(child, (ast.If, ast.Try, ast.With, ast.AsyncWith,
                                    ast.For, ast.While, ast.ExceptHandler,
                                    ast.match_case)
                            or type(child).__name__ in ("TryStar", "Match")):
                # defs hidden behind `if TYPE_CHECKING:` or a try/except
                # import shim are real definitions and belong in the graph.
                # ExceptHandler and match_case are children of Try/Match,
                # so omitting them stopped the walk dead at `except:` --
                # which is exactly the optional-dependency-shim pattern
                # this comment was written for.
                self._walk_scope(child, rec, db, bufs, src_lines, parent_id,
                                 qual_prefix, class_stack, nest)

    # -- functions ---------------------------------------------------------
    def _function(self, node: ast.AST, rec: FileRec, db: sqlite3.Connection,
                  bufs: Buffers, src_lines: list[str],
                  parent_id: Optional[int], qual_prefix: str,
                  class_stack: list[str], nest: int) -> int:
        name = node.name
        qual = qual_prefix + name
        is_method = bool(class_stack) and parent_id is not None
        decs = [dotted(d) for d in node.decorator_list]
        dec_base = {d.split(".")[-1] for d in decs}

        fm = FunctionMetrics(node, src_lines, class_stack)
        fm.generic_visit(node)
        m = dict(fm.m)

        args = node.args
        n_params = (len(args.posonlyargs) + len(args.args) + len(args.kwonlyargs)
                    + (1 if args.vararg else 0) + (1 if args.kwarg else 0))
        annotated = sum(1 for a in (list(args.posonlyargs) + list(args.args)
                                    + list(args.kwonlyargs))
                        if a.annotation is not None)
        total_named = len(args.posonlyargs) + len(args.args) + len(args.kwonlyargs)

        line_end = getattr(node, "end_lineno", node.lineno) or node.lineno
        body_start = node.body[0].lineno if node.body else node.lineno
        doc_n = docstring_lines(node)

        m.update(
            n_params=n_params,
            n_optional_params=len(args.defaults) + len(
                [d for d in args.kw_defaults if d is not None]),
            n_default_args=len(args.defaults),
            n_kwonly_args=len(args.kwonlyargs),
            n_posonly_args=len(args.posonlyargs),
            n_star_args=1 if args.vararg else 0,
            n_kwargs=1 if args.kwarg else 0,
            n_annotated_params=annotated,
            n_untyped_params=total_named - annotated,
            has_return_type=1 if node.returns is not None else 0,
            n_decorators=len(decs),
            cyclomatic=fm.cyclomatic,
            cognitive=fm.cognitive,
            max_nesting=fm.max_nesting,
            max_loop_depth=fm.max_loop_depth,
            sloc=_sloc_of(src_lines, node.lineno - 1, line_end),
            n_comment_lines=_comment_lines(src_lines, node.lineno - 1,
                                           line_end),
            n_doc_lines=doc_n,
            has_doc=1 if doc_n else 0,
            n_operators=sum(fm.operators.values()),
            n_operands=sum(fm.operands.values()),
            n_distinct_operators=len(fm.operators),
            n_distinct_operands=len(fm.operands),
            n_tokens=sum(fm.operators.values()) + sum(fm.operands.values()),
            n_locals=len({t.id for t in ast.walk(node)
                          if isinstance(t, ast.Name)
                          and isinstance(t.ctx, ast.Store)}),
            is_async=1 if isinstance(node, ast.AsyncFunctionDef) else 0,
            is_generator=1 if m.get("n_yield") else 0,
            is_property=1 if dec_base & {"property", "cached_property"} else 0,
            is_classmethod=1 if "classmethod" in dec_base else 0,
            is_staticmethod=1 if "staticmethod" in dec_base else 0,
            is_abstract=1 if dec_base & {"abstractmethod",
                                         "abstractproperty"} else 0,
            is_overload=1 if "overload" in dec_base else 0,
            is_contextmanager=1 if dec_base & {"contextmanager",
                                               "asynccontextmanager"} else 0,
            is_cached=1 if dec_base & {"lru_cache", "cache", "cached_property",
                                       "memoize"} else 0,
            is_override=1 if "override" in dec_base else 0,
            is_deprecated=1 if "deprecated" in dec_base else 0,
            is_dunder=1 if name.startswith("__") and name.endswith("__") else 0,
            is_private=1 if name.startswith("_") and not name.startswith("__") else 0,
            is_public=0 if name.startswith("_") else 1,
            is_test=1 if name.startswith("test_") or "pytest" in " ".join(decs) else 0,
            is_entrypoint=1 if name in DUNDER_ENTRY else 0,
            is_generated=int(rec.is_generated),
            nest_level=nest,
            n_dynamic_calls=m.get("n_dynamic_calls", 0),
        )

        sid = self._insert_symbol(
            db, rec, name, "method" if is_method else "function",
            node.lineno, line_end, qual, parent_id,
            self._signature(node, name), type_str(node.returns),
            "private" if name.startswith("_") else "public", m)

        self._params(sid, args, bufs, m, db)
        for d, dn in zip(node.decorator_list, decs):
            bufs.attributes.append(
                (sid, rec.fid, dn or "?", type_str(d)[:200], d.lineno))
        self._handlers(node, sid, bufs)
        self._comprehensions(node, sid, rec, bufs)
        self._hazards_and_calls(fm, sid, rec, bufs)
        self._dynamic_sites(node, sid, rec, bufs)
        for lkind, lval, lline, lmagic in fm.literals:
            bufs.literals.append((sid, rec.fid, lkind, lval[:200],
                                  lline, int(lmagic)))

        self.by_name.setdefault(name, []).append(
            (sid, rec.fid, rec.mid, class_stack[-1] if class_stack else ""))
        self.by_qual["%s:%s" % (rec.rel, qual)] = sid
        self.by_qual[qual] = sid
        return sid


    def _module_scope(self, tree: ast.Module, rec: FileRec,
                      db: sqlite3.Connection, bufs: Buffers,
                      src_lines: list[str]) -> None:
        """One symbol for everything that runs at import time.

        Without it a helper called only from module scope has `fan_in = 0` and
        lands in `dead-code`, `urlpatterns = [path(...)]` contributes nothing,
        and the import-time side effects that make a Django or Flask app work
        are absent from the graph entirely.
        """
        fm = FunctionMetrics(tree, src_lines, [], prune_defs=True)
        fm.generic_visit(tree)
        if not fm.calls and not fm.m:
            return

        end = len(src_lines) or 1
        m = dict(fm.m)
        m.update(
            cyclomatic=fm.cyclomatic, cognitive=fm.cognitive,
            max_nesting=fm.max_nesting, max_loop_depth=fm.max_loop_depth,
            n_operators=sum(fm.operators.values()),
            n_operands=sum(fm.operands.values()),
            n_distinct_operators=len(fm.operators),
            n_distinct_operands=len(fm.operands),
            n_tokens=sum(fm.operators.values()) + sum(fm.operands.values()),
            n_lines=end,
            sloc=sum(1 for l in src_lines if l.strip()),
            is_generated=int(rec.is_generated),
            is_test=int(rec.is_test),
            has_doc=1 if docstring_lines(tree) else 0,
            n_doc_lines=docstring_lines(tree),
            is_entrypoint=1 if is_dunder_main(tree) else 0,
        )
        sid = self._insert_symbol(
            db, rec, "<module>", "module", 1, end, rec.rel, None,
            "top-level statements of %s" % rec.rel, "", "", m)
        self._hazards_and_calls(fm, sid, rec, bufs)
        self._dynamic_sites(tree, sid, rec, bufs)
        self.by_qual["%s:<module>" % rec.rel] = sid

    def _signature(self, node: ast.AST, name: str) -> str:
        try:
            args = ast.unparse(node.args)
        except Exception:
            args = "..."
        ret = type_str(node.returns)
        pre = "async def " if isinstance(node, ast.AsyncFunctionDef) else "def "
        return ("%s%s(%s)%s" % (pre, name, args, " -> %s" % ret if ret else ""))[:400]

    def _params(self, sid: int, args: ast.arguments, bufs: Buffers,
                m: dict[str, Any], db: sqlite3.Connection) -> None:
        pos = 0
        n_mutable = 0
        named = ([(a, "posonly") for a in args.posonlyargs]
                 + [(a, "normal") for a in args.args]
                 + [(a, "kwonly") for a in args.kwonlyargs])
        n_pos = len(args.posonlyargs) + len(args.args)
        defaults_start = n_pos - len(args.defaults)

        for a, kind in named:
            default: Optional[ast.expr] = None
            if kind != "kwonly" and pos >= defaults_start and args.defaults:
                idx = pos - defaults_start
                if 0 <= idx < len(args.defaults):
                    default = args.defaults[idx]
            elif kind == "kwonly":
                idx = args.kwonlyargs.index(a)
                if idx < len(args.kw_defaults):
                    default = args.kw_defaults[idx]

            mutable = default is not None and (
                isinstance(default, (ast.List, ast.Dict, ast.Set))
                or (isinstance(default, ast.Call)
                    and dotted(default.func).split(".")[-1]
                    in MUTABLE_DEFAULT_CALLS))
            if mutable:
                n_mutable += 1
            ann = a.annotation
            bufs.params.append(
                (sid, pos, a.arg, type_str(ann), type_str(default),
                 int(default is not None), 0, 0, 0,
                 int("Optional" in type_str(ann) or "None" in type_str(ann)),
                 int("TypeVar" in type_str(ann)), int(ann is None),
                 type_depth(ann)))
            pos += 1
        if args.vararg:
            bufs.params.append((sid, pos, "*" + args.vararg.arg,
                                type_str(args.vararg.annotation), None, 0, 1, 0,
                                0, 0, 0, int(args.vararg.annotation is None),
                                type_depth(args.vararg.annotation)))
            pos += 1
        if args.kwarg:
            bufs.params.append((sid, pos, "**" + args.kwarg.arg,
                                type_str(args.kwarg.annotation), None, 0, 1, 0,
                                0, 0, 0, int(args.kwarg.annotation is None),
                                type_depth(args.kwarg.annotation)))
        if n_mutable:
            # Buffered, not written here: single-row DML is banned where the
            # rows can be collected. Applied as one executemany in post_build.
            self._mutable_defaults.append((n_mutable, sid))

    def _handlers(self, node: ast.AST, sid: int, bufs: Buffers) -> None:
        for h in ast.walk(node):
            if not isinstance(h, ast.ExceptHandler):
                continue
            types = dotted(h.type) if h.type is not None else ""
            if isinstance(h.type, ast.Tuple):
                types = ",".join(dotted(e) for e in h.type.elts)
            body = h.body
            empty = len(body) == 1 and isinstance(body[0], (ast.Pass,))
            # One walk, not two. `reraise` and `log` each used to run their
            # own `ast.walk(h)` over the same handler body; both answers come
            # from the same pass, and it can stop as soon as both are known.
            reraise = log = False
            for n in ast.walk(h):
                if isinstance(n, ast.Raise):
                    reraise = True
                elif isinstance(n, ast.Call) and any(
                        k in dotted(n.func).lower()
                        for k in ("log", "warn", "error", "print",
                                  "capture", "report")):
                    log = True
                if reraise and log:
                    break
            end = getattr(h, "end_lineno", h.lineno) or h.lineno
            bufs.rows("handlers").append(
                (sid, h.lineno, types[:200], int(h.type is None),
                 int(h.type is None or types in BROAD_EXCEPTIONS),
                 int(empty), int(reraise), int(log), end - h.lineno, 0))

    def _comprehensions(self, node: ast.AST, sid: int, rec: FileRec,
                        bufs: Buffers) -> None:
        for c in ast.walk(node):
            if not isinstance(c, COMP_NODES):
                continue
            kind = {ast.ListComp: "list", ast.SetComp: "set",
                    ast.DictComp: "dict", ast.GeneratorExp: "genexp"}[type(c)]
            bufs.rows("comprehensions").append(
                (sid, rec.fid, kind, c.lineno, len(c.generators),
                 sum(len(g.ifs) for g in c.generators),
                 int(any(g.is_async for g in c.generators)), 0))

    def _dynamic_sites(self, node: ast.AST, sid: int, rec: FileRec,
                       bufs: Buffers) -> None:
        """Where the call graph goes dark, recorded explicitly.

        Every one of these is a place a static reader stops being able to
        follow the program. Counting them is what lets a later query say how
        much of its own answer to trust.
        """
        for c in ast.walk(node):
            if not isinstance(c, ast.Call):
                continue
            name = dotted(c.func)
            base = name.split(".")[-1] if name else ""
            kind = ""
            if base in ("eval", "exec", "compile"):
                kind = base
            elif base in ("getattr", "setattr", "delattr"):
                kind = "attr"
            elif base in ("__import__", "import_module"):
                kind = "import"
            elif base in ("globals", "locals", "vars"):
                kind = "scope"
            elif not name:
                kind = "computed"
            if not kind:
                continue
            literal = bool(c.args) and isinstance(c.args[-1], ast.Constant)
            try:
                expr = ast.unparse(c)[:200]
            except Exception:
                expr = name
            bufs.rows("dynamic_sites").append(
                (sid, rec.fid, kind, expr, c.lineno, int(literal)))

    def _hazards_and_calls(self, fm: FunctionMetrics, sid: int, rec: FileRec,
                           bufs: Buffers) -> None:
        alias = self.aliases.get(rec.fid, {})
        seen: dict[str, list[Any]] = {}
        for name, line, dynamic in fm.calls:
            if dynamic or not name:
                continue
            resolved = name
            head = name.split(".")[0]
            if head in alias:
                resolved = alias[head] + name[len(head):]
            cat = HAZARD_CALLS.get(resolved) or HAZARD_CALLS.get(name)
            if cat is None:
                base = name.split(".")[-1]
                if "." in name and base in HAZARD_METHOD_SUFFIX:
                    cat = HAZARD_METHOD_SUFFIX[base]
                    resolved = "*." + base
            if cat is not None:
                e = seen.get(resolved)
                if e is None:
                    seen[resolved] = [cat, 1, line]
                else:
                    e[1] += 1
            self.add_pending(sid, rec.fid, rec.mid, name, line,
                                 fm.class_stack[-1] if fm.class_stack else "")
        if fm.m.get("n_shell_true"):
            seen["shell=True"] = ["shell", fm.m["n_shell_true"], 0]
        for pat, (cat, n, line) in seen.items():
            bufs.add_hazard(sid, pat[:120], cat, n, line)

    # -- classes -----------------------------------------------------------
    def _class(self, node: ast.ClassDef, rec: FileRec, db: sqlite3.Connection,
               bufs: Buffers, src_lines: list[str], parent_id: Optional[int],
               qual_prefix: str, nest: int) -> int:
        name = node.name
        qual = qual_prefix + name
        bases = [dotted(b) for b in node.bases]
        base_str = ",".join(b for b in bases if b)[:400]
        decs = [dotted(d) for d in node.decorator_list]
        dec_base = {d.split(".")[-1] for d in decs}
        line_end = getattr(node, "end_lineno", node.lineno) or node.lineno
        doc_n = docstring_lines(node)

        methods = [n for n in node.body
                   if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef))]
        mnames = {m.name for m in methods}
        class_vars = [n for n in node.body
                      if isinstance(n, (ast.Assign, ast.AnnAssign))]
        has_slots = any(
            isinstance(n, ast.Assign) and any(
                isinstance(t, ast.Name) and t.id == "__slots__"
                for t in n.targets)
            for n in node.body)
        abstract = sum(
            1 for m in methods
            if any(dotted(d).split(".")[-1] in ("abstractmethod",
                                                "abstractproperty")
                   for d in m.decorator_list))

        m: dict[str, Any] = dict(
            n_lines=line_end - node.lineno + 1,
            sloc=_sloc_of(src_lines, node.lineno - 1, line_end),
            n_comment_lines=_comment_lines(src_lines, node.lineno - 1,
                                           line_end),
            n_doc_lines=doc_n, has_doc=1 if doc_n else 0,
            n_decorators=len(decs),
            n_generic_params=len(getattr(node, "type_params", []) or []),
            is_public=0 if name.startswith("_") else 1,
            is_private=1 if name.startswith("_") else 0,
            is_abstract=1 if abstract or "ABC" in base_str else 0,
            is_deprecated=1 if "deprecated" in dec_base else 0,
            is_test=1 if name.startswith("Test") else 0,
            is_generated=int(rec.is_generated),
            nest_level=nest,
        )
        sid = self._insert_symbol(
            db, rec, name, "class", node.lineno, line_end, qual, parent_id,
            ("class %s(%s)" % (name, base_str))[:400], "",
            "private" if name.startswith("_") else "public", m)

        for d, dn in zip(node.decorator_list, decs):
            bufs.attributes.append(
                (sid, rec.fid, dn or "?", type_str(d)[:200], d.lineno))

        ordinal = 0
        for n in node.body:
            if isinstance(n, ast.AnnAssign) and isinstance(n.target, ast.Name):
                ann = type_str(n.annotation)
                bufs.fields.append(
                    (sid, ordinal, n.target.id, ann, "", n.lineno, 1, 0, 0,
                     int("Optional" in ann or "None" in ann),
                     int(any(c in ann for c in ("list", "List", "dict", "Dict",
                                                "set", "Set", "tuple"))),
                     0, int(n.value is not None), type_depth(n.annotation)))
                ordinal += 1
            elif isinstance(n, ast.Assign):
                for t in n.targets:
                    if isinstance(t, ast.Name) and t.id != "__slots__":
                        bufs.fields.append(
                            (sid, ordinal, t.id, "", "", n.lineno, 1, 0, 0, 0,
                             int(isinstance(n.value, (ast.List, ast.Dict,
                                                      ast.Set))),
                             1, 1, 0))
                        ordinal += 1

        is_enum = any("Enum" in b for b in bases)
        if is_enum:
            eo = 0
            for n in node.body:
                if isinstance(n, ast.Assign):
                    for t in n.targets:
                        if isinstance(t, ast.Name):
                            bufs.enum_members.append(
                                (sid, eo, t.id, type_str(n.value)[:80], 0))
                            eo += 1

        bufs.rows("classes").append(
            (sid, len(bases), base_str, len(methods), len(class_vars),
             0, abstract, sum(1 for x in mnames
                              if x.startswith("__") and x.endswith("__")),
             int(has_slots), int("__init__" in mnames), int("__eq__" in mnames),
             int("__hash__" in mnames),
             int(bool(dec_base & {"dataclass", "attrs", "attr"})),
             int("ABC" in base_str or "ABCMeta" in base_str),
             int(is_enum),
             int(any(b.endswith("Error") or b.endswith("Exception")
                     or b == "Exception" or b == "BaseException"
                     for b in bases)),
             int("Protocol" in base_str),
             int("NamedTuple" in base_str or "namedtuple" in base_str),
             int("TypedDict" in base_str),
             int("BaseModel" in base_str or "pydantic" in base_str.lower()),
             int("models.Model" in base_str or base_str.endswith("Model")),
             int("type" in bases or "ABCMeta" in base_str)))
        # Register the class for call resolution. Without this `Foo()` resolves
        # to nothing and EVERY class in the tree reports fan_in 0 -- 10,470 of
        # them in Django -- so any query ranking classes by how often they are
        # instantiated silently ranks nothing.
        self.by_name.setdefault(name, []).append(
            (sid, rec.fid, rec.mid, ""))
        return sid

    # -- insertion ---------------------------------------------------------
    def _insert_symbol(self, db: sqlite3.Connection, rec: FileRec, name: str,
                       kind: str, line_start: int, line_end: int, qual: str,
                       parent_id: Optional[int], signature: str,
                       return_type: str, visibility: str,
                       m: dict[str, Any]) -> int:
        cols = ["file_id", "module_id", "parent_id", "name", "qual_name", "kind",
                "line_start", "line_end", "n_lines", "signature", "return_type",
                "visibility"]
        vals: list[Any] = [rec.fid, rec.mid, parent_id, name, qual, kind,
                           line_start, line_end,
                           m.pop("n_lines", line_end - line_start + 1),
                           signature, return_type, visibility]
        for k, v in m.items():
            if k in _SYMBOL_COLS:
                cols.append(k)
                vals.append(int(v) if isinstance(v, bool) else v)
        sql = ("INSERT INTO symbols(%s) VALUES(%s)"
               % (",".join(cols), ",".join("?" * len(cols))))
        return db.execute(sql, vals).lastrowid

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

    def post_build(self, db: sqlite3.Connection) -> None:
        """Apply everything buffered during parsing, in one statement each."""
        if self._mutable_defaults:
            db.executemany(
                "UPDATE symbols SET n_mutable_default=? WHERE id=?",
                self._mutable_defaults)
            self._mutable_defaults.clear()

    def resolve_calls(self, db: sqlite3.Connection, bufs: Buffers) -> None:
        """Turn recorded call names into edges, honestly.

        Four rules, tried in order, and everything that survives all four is
        recorded as unresolved rather than guessed at:
          1. exact qualified name in the same file
          2. a name imported into this file
          3. `self.x` / bare `x` inside a class -> that class's method
          4. a globally unique definition of that bare name

        Rule 4 is the one that can be wrong: two unrelated classes with a
        `run()` method make `run` ambiguous, and this deliberately refuses to
        pick. Silence is the honest answer, and `unresolved_calls` records it.
        """
        by_name = self.by_name
        by_qual = self.by_qual
        unique: dict[str, tuple[int, int, int, str]] = {}
        for nm, cands in by_name.items():
            if len(cands) == 1:
                unique[nm] = cands[0]

        #: symbol_id -> (file_id, module_id) of the DEFINITION. `same_file` and
        #: `same_module` describe where the CALLEE lives, and two of the four
        #: lookups below know only the caller's location -- comparing that to
        #: itself stamped 2,735 of django's edges same_file=1 regardless.
        sym_loc: dict[int, tuple[int, int]] = {}
        for nm, cands in self.by_name.items():
            for _sid, _fid, _mid, _c in cands:
                sym_loc.setdefault(_sid, (_fid, _mid))
        file_scope: dict[tuple[int, str], int] = {}
        for nm, cands in by_name.items():
            for sid, fid, mid, cls in cands:
                file_scope.setdefault((fid, nm), sid)

        n_res = n_unres = n_extern = 0
        n_ext: dict[int, int] = {}
        for caller_sid, fid, mid, name, line, cls in self.iter_pending():
            if not name:
                continue
            head, _, tail = name.partition(".")
            base = name.split(".")[-1]
            target: Optional[tuple[int, int, int, str]] = None

            if head == "self" and tail and cls:
                for sid, f2, m2, c2 in by_name.get(tail.split(".")[-1], ()):
                    if c2 == cls:
                        target = (sid, f2, m2, c2)
                        break
            if target is None:
                alias = self.aliases.get(fid, {})
                if head in alias:
                    q = alias[head] + ("." + tail if tail else "")
                    sid = by_qual.get(q.split(".", 1)[-1]) or by_qual.get(q)
                    if sid:
                        target = (sid, fid, mid, "")
            if target is None and "." not in name:
                sid = file_scope.get((fid, name))
                if sid:
                    target = (sid, fid, mid, "")
            if target is None:
                cand = unique.get(base)
                if cand is not None:
                    target = cand
            if target is None:
                # Out of scope is not the same as blind. A call into the
                # standard library or a third-party package is a boundary we
                # chose, not a place the reader lost the thread.
                if self._is_external(name, head, fid):
                    n_ext[caller_sid] = n_ext.get(caller_sid, 0) + 1
                    n_extern += 1
                else:
                    bufs.add_unresolved(caller_sid, name[:160], line)
                    n_unres += 1
                continue
            sid = target[0]
            # Ask where the CALLEE is defined; target[1]/[2] carry the
            # caller's own fid/mid in two of the branches above.
            tloc = sym_loc.get(sid)
            bufs.add_edge(caller_sid, sid,
                          tloc is not None and tloc[0] == fid,
                          tloc is not None and tloc[1] == mid, line)
            n_res += 1

        if n_ext:
            db.executemany("UPDATE symbols SET n_external_calls=? WHERE id=?",
                           [(v, k) for k, v in n_ext.items()])
        total = n_res + n_unres + n_extern
        db.execute("INSERT OR REPLACE INTO meta(key,value) VALUES(?,?)",
                   ("calls_resolved",
                    "%d in-tree / %d external / %d unresolved "
                    "(%d%% of in-scope calls resolved)"
                    % (n_res, n_extern, n_unres,
                       100 * n_res // max(1, n_res + n_unres))))
        if self.n_ts_rescued:
            db.execute("INSERT OR REPLACE INTO meta(key,value) VALUES(?,?)",
                       ("syntax_too_new", str(self.n_ts_rescued)))

        for tbl, sql in (
            ("classes",
             "INSERT OR IGNORE INTO classes(symbol_id,n_bases,bases,n_methods,"
             "n_class_vars,n_properties,n_abstract_methods,n_dunder,has_slots,"
             "has_init,has_eq,has_hash,is_dataclass,is_abc,is_enum,"
             "is_exception,is_protocol,is_namedtuple,is_typeddict,is_pydantic,"
             "is_django_model,is_metaclass) VALUES(%s)" % ",".join("?" * 22)),
            ("handlers",
             "INSERT INTO handlers(symbol_id,line,types,is_bare,is_broad,"
             "is_empty,has_reraise,has_log,n_body_lines,in_loop) "
             "VALUES(?,?,?,?,?,?,?,?,?,?)"),
            ("dynamic_sites",
             "INSERT INTO dynamic_sites(symbol_id,file_id,kind,expr,line,"
             "is_literal_arg) VALUES(?,?,?,?,?,?)"),
            ("comprehensions",
             "INSERT INTO comprehensions(symbol_id,file_id,kind,line,"
             "n_generators,n_ifs,is_async,in_loop) VALUES(?,?,?,?,?,?,?,?)"),
            ("module_vars",
             "INSERT INTO module_vars(file_id,module_id,name,line,type,"
             "is_constant,is_mutable_container,is_private,has_call_init) "
             "VALUES(?,?,?,?,?,?,?,?,?)"),
        ):
            rows = bufs.extra.get(tbl)
            if rows:
                db.executemany(sql, rows)

    def _is_external(self, name: str, head: str, fid: int) -> bool:
        """True if this call leaves the tree by design rather than by defeat."""
        if head in PY_BUILTINS and "." not in name:
            return True
        target = self.aliases.get(fid, {}).get(head, head)
        root = target.split(".")[0]
        if root in STDLIB_ROOTS:
            return True
        # imported from somewhere, and we never found a file defining it
        return head in self.aliases.get(fid, {}) and self._external(target)

    def parse_manifests(self, root: str, db: sqlite3.Connection) -> None:
        for name in self.MANIFESTS:
            p = os.path.join(root, name)
            if os.path.isfile(p):
                try:
                    head = open(p, encoding="utf-8", errors="replace").read(4000)
                except OSError:
                    continue
                man_rows.append(("manifest:" + name, head[:2000]))

QUERIES: list[tuple[str, str, str, str]] = [
(
    "async-blocking",
    "Blocking calls inside async functions -- the event loop stops here",
    "ANSWERS which coroutines stall the whole loop instead of yielding.\n"
    "ACT move the call to asyncio.to_thread / run_in_executor, or use the async\n"
    "     client. One blocking call in one coroutine stalls every other task.\n"
    "MISLEADS a blocking call during startup or in a CLI path is harmless. This\n"
    "     cannot tell setup code from request code -- check what calls it.",
    """SELECT s.name, s.n_blocking AS blocking, s.n_io AS io, s.n_net AS net,
        s.n_await AS awaits, s.await_in_loop AS awaits_in_loop,
        s.fan_in, f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.is_async=1 AND (s.n_blocking > 0 OR s.n_io > 0 OR s.n_net > 0)
      AND f.is_generated=0 AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.n_blocking DESC, s.n_net DESC LIMIT :lim"""),
(
    "async-blocking-reachable",
    "Blocking work reachable from an async caller, up to 4 hops away",
    "ANSWERS which async entry points end up blocking through a chain of plain\n"
    "     helpers that individually look innocent.\n"
    "ACT the fix belongs at the boundary: wrap the whole subtree in to_thread\n"
    "     rather than chasing each leaf.\n"
    "MISLEADS depth is capped at 4 and only resolved edges are walked, so this\n"
    "     is a floor. A path through getattr dispatch does not appear at all.",
    """WITH RECURSIVE reach(root, sym, depth) AS (
        SELECT s.id, s.id, 0 FROM symbols s
        WHERE s.is_async=1 AND s.kind IN ('function','method')
        UNION
        SELECT r.root, e.callee_id, r.depth+1
        FROM reach r JOIN edges e ON e.caller_id=r.sym
        WHERE r.depth < 4 AND e.is_self=0)
    SELECT a.name AS async_fn, COUNT(DISTINCT b.id) AS blocking_callees,
        MAX(r.depth) AS max_hops,
        GROUP_CONCAT(DISTINCT b.name) AS via,
        f.path || ':' || a.line_start AS at
    FROM reach r
    JOIN symbols a ON a.id=r.root
    JOIN symbols b ON b.id=r.sym
    JOIN files f ON f.id=a.file_id
    LEFT JOIN modules m ON m.id=a.module_id
    WHERE r.depth > 0 AND b.n_blocking > 0 AND a.is_async=1
      AND f.is_generated=0 AND COALESCE(m.name,'') LIKE :mod
    GROUP BY a.id ORDER BY blocking_callees DESC LIMIT :lim"""),
(
    "await-in-loop",
    "Sequential awaits: requests issued one at a time that could overlap",
    "ANSWERS where latency is the SUM of N round trips instead of the max.\n"
    "ACT if the iterations are independent, collect the coroutines and hand\n"
    "     them to asyncio.gather or a TaskGroup. N x 50ms becomes 50ms.\n"
    "MISLEADS some loops MUST be sequential -- pagination, rate limits, or a\n"
    "     later iteration depending on an earlier result. Read before changing.",
    """SELECT s.name, s.await_in_loop AS awaits_in_loop, s.max_loop_depth AS depth,
        s.n_await AS total_awaits, s.n_net AS net, s.fan_in,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.await_in_loop > 0 AND f.is_generated=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.await_in_loop DESC, s.fan_in DESC LIMIT :lim"""),
(
    "mutable-defaults",
    "Mutable default arguments, ranked by how many callers share the object",
    "ANSWERS which functions accumulate state across unrelated calls.\n"
    "ACT default to None and build the container inside. The default is created\n"
    "     ONCE at def time, so every caller that omits the argument mutates the\n"
    "     same list.\n"
    "MISLEADS a mutable default that is only ever read is harmless, and a few\n"
    "     are deliberate memo caches. fan_in is the multiplier on the damage.",
    """SELECT s.name, s.n_mutable_default AS mutable_defaults, s.fan_in,
        s.n_params, s.is_public AS public,
        (SELECT GROUP_CONCAT(p.name || '=' || COALESCE(p.default_value,''))
         FROM params p WHERE p.symbol_id=s.id AND p.default_value IS NOT NULL
         LIMIT 3) AS defaults,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_mutable_default > 0 AND f.is_generated=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.fan_in DESC, s.n_mutable_default DESC LIMIT :lim"""),
(
    "untrusted-frontier",
    "Dangerous sinks and how far they sit from a public entry point",
    "ANSWERS which eval/exec/pickle/shell sites an outside caller can reach.\n"
    "ACT a sink 1-2 hops from a public function is where to look first. Confirm\n"
    "     the argument cannot come from outside; if it can, that is the bug.\n"
    "MISLEADS reachability is not reachedness -- the path may be guarded by an\n"
    "     auth check this cannot see. Depth capped at 5; deeper paths are missed.",
    """WITH RECURSIVE reach(root, sym, depth) AS (
        SELECT s.id, s.id, 0 FROM symbols s
        WHERE s.is_public=1 AND s.kind IN ('function','method')
        UNION
        SELECT r.root, e.callee_id, r.depth+1
        FROM reach r JOIN edges e ON e.caller_id=r.sym
        WHERE r.depth < 5 AND e.is_self=0)
    SELECT sink.name AS sink, sink.n_exec AS exec_, sink.n_deserialize AS unpickle,
        sink.n_shell AS shell, sink.n_shell_true AS shell_true,
        MIN(r.depth) AS hops_from_public,
        COUNT(DISTINCT r.root) AS reachable_from,
        f.path || ':' || sink.line_start AS at
    FROM reach r
    JOIN symbols sink ON sink.id=r.sym
    JOIN files f ON f.id=sink.file_id
    LEFT JOIN modules m ON m.id=sink.module_id
    WHERE (sink.n_exec + sink.n_deserialize + sink.n_shell_true) > 0
      AND f.is_test=0 AND f.is_generated=0
      AND COALESCE(m.name,'') LIKE :mod
    GROUP BY sink.id
    ORDER BY hops_from_public ASC, reachable_from DESC LIMIT :lim"""),
(
    "sql-built-by-hand",
    "Queries assembled with f-strings, concatenation or .format",
    "ANSWERS where a query is built by string surgery instead of parameters.\n"
    "ACT pass parameters to execute() instead. Every row here is a candidate\n"
    "     injection even if today's argument happens to be a constant.\n"
    "MISLEADS interpolating a table name you control is not injection. The\n"
    "     pattern cannot tell a literal from a request field -- read the site.",
    """SELECT s.name,
        s.n_sql_fstring AS fstring, s.n_sql_concat AS concat,
        s.n_sql_format AS fmt, s.n_sql AS sql_calls, s.fan_in,
        s.is_public AS public,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE (s.n_sql_fstring + s.n_sql_concat + s.n_sql_format) > 0
      AND f.is_test=0 AND COALESCE(m.name,'') LIKE :mod
    ORDER BY (s.n_sql_fstring + s.n_sql_concat + s.n_sql_format) DESC,
        s.fan_in DESC LIMIT :lim"""),
(
    "n-plus-one",
    "Database work inside a loop: N queries where one would do",
    "ANSWERS which functions issue a query per iteration.\n"
    "ACT batch it -- one IN query, a join, or select_related/prefetch_related.\n"
    "     This is the single most common cause of a slow endpoint.\n"
    "MISLEADS query_in_loop is a REGEX over string literals: any string holding\n"
    "     the word SELECT, UPDATE or DELETE FROM counts, including error\n"
    "     messages and docstrings. Corroboration with sql_calls or io is now\n"
    "     required, but a row with sql_calls=0 is still worth reading twice.\n"
    "     Trip count is invisible either way.",
    """SELECT s.name, s.query_in_loop AS queries_in_loop,
        s.max_loop_depth AS depth, s.n_sql AS sql_calls, s.io_in_loop AS io,
        s.fan_in, f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE ((s.query_in_loop > 0 AND (s.n_sql > 0 OR s.io_in_loop > 0))
           OR (s.n_sql > 0 AND s.max_loop_depth > 0))
      AND f.is_test=0 AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.query_in_loop DESC, s.max_loop_depth DESC LIMIT :lim"""),
(
    "loop-multiplied",
    "Work done per iteration that could be hoisted out",
    "ANSWERS where a constant cost is being paid N times.\n"
    "ACT re.compile once outside the loop; bind len() to a local; move the\n"
    "     invariant call above the loop. Cheap, mechanical, and compounding.\n"
    "MISLEADS the interpreter does not hoist any of this, so the cost is real --\n"
    "     but if the loop runs three times, saving it is worth nothing.",
    """SELECT s.name, s.max_loop_depth AS depth, s.call_in_loop AS calls,
        s.regex_in_loop AS regex, s.len_in_loop AS len_calls,
        s.n_append_in_loop AS appends, s.concat_in_loop AS concat,
        s.n_range_len AS range_len, s.fan_in,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.max_loop_depth > 0 AND f.is_generated=0
      AND (s.regex_in_loop + s.len_in_loop + s.concat_in_loop
           + s.n_range_len) > 0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY (s.regex_in_loop*3 + s.concat_in_loop*3 + s.len_in_loop
              + s.n_range_len) DESC LIMIT :lim"""),
(
    "quadratic-strings",
    "String built by += inside a loop -- quadratic in the result size",
    "ANSWERS which functions cost O(n^2) to build a string that could be O(n).\n"
    "ACT append to a list and ''.join it once at the end.\n"
    "MISLEADS CPython special-cases some in-place concatenation when the string\n"
    "     has one reference, so the worst case does not always bite. It bites\n"
    "     reliably once the string is also read inside the loop.",
    """SELECT s.name, s.concat_in_loop AS concats, s.max_loop_depth AS depth,
        s.n_string_lit AS literals, s.fan_in, s.sloc,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.concat_in_loop > 0 AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.concat_in_loop DESC, s.max_loop_depth DESC LIMIT :lim"""),
(
    "swallowed-errors",
    "except blocks that catch everything and tell nobody",
    "ANSWERS where failures disappear without a trace.\n"
    "ACT catch the specific exception, or log with the traceback and re-raise.\n"
    "     A bare `except: pass` on an IO path hides outages for months.\n"
    "MISLEADS some swallowing is correct -- optional cleanup, best-effort cache\n"
    "     warming. The has_log column separates silence from mere breadth.",
    """SELECT s.name, COUNT(h.id) AS handlers,
        SUM(h.is_bare) AS bare, SUM(h.is_broad) AS broad,
        SUM(h.is_empty) AS empty, SUM(h.has_reraise) AS reraise,
        SUM(h.has_log) AS logged,
        s.n_io + s.n_net + s.n_sql AS risky_ops,
        f.path || ':' || s.line_start AS at
    FROM handlers h
    JOIN symbols s ON s.id=h.symbol_id
    JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE h.is_broad=1 AND f.is_test=0 AND COALESCE(m.name,'') LIKE :mod
    GROUP BY s.id
    HAVING SUM(h.has_log)=0 AND SUM(h.has_reraise)=0
    ORDER BY risky_ops DESC, broad DESC LIMIT :lim"""),
(
    "reflection-opacity",
    "Runtime reflection: where static reading stops working",
    "ANSWERS which code decides at run time what to call.\n"
    "ACT these sites are why fan_in is a lower bound everywhere else. Where the\n"
    "     argument is a literal, the call could be written out and made visible.\n"
    "MISLEADS getattr with a literal name is perfectly readable; the is_literal\n"
    "     column separates those from the genuinely dynamic ones.",
    """SELECT d.kind, COUNT(*) AS n,
        SUM(d.is_literal_arg) AS literal_arg,
        COUNT(DISTINCT d.symbol_id) AS in_fns,
        COUNT(DISTINCT d.file_id) AS in_files,
        GROUP_CONCAT(DISTINCT SUBSTR(d.expr,1,40)) AS examples
    FROM dynamic_sites d
    JOIN files f ON f.id=d.file_id
    LEFT JOIN modules m ON m.id=f.module_id
    WHERE f.is_test=0 AND COALESCE(m.name,'') LIKE :mod
    GROUP BY d.kind ORDER BY n DESC LIMIT :lim"""),
(
    "decorator-roots",
    "Functions that look dead because a decorator registers them",
    "ANSWERS which zero-fan-in functions are actually framework entry points.\n"
    "ACT do NOT delete these. @app.route, @task, @pytest.fixture and friends\n"
    "     call the function from somewhere no source line references.\n"
    "MISLEADS the decorator list is heuristic. A custom registering decorator\n"
    "     this does not recognise still leaves its function looking dead in\n"
    "     `dead-code` below -- cross-check before removing anything.",
    """SELECT s.name, a.name AS decorator, s.fan_in, s.sloc,
        s.cyclomatic AS cyclo, s.is_async AS async_,
        f.path || ':' || s.line_start AS at
    FROM symbols s
    JOIN attributes a ON a.symbol_id=s.id
    JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.fan_in=0 AND s.kind IN ('function','method')
      AND COALESCE(m.name,'') LIKE :mod
      AND (a.name LIKE '%route%' OR a.name LIKE '%task%' OR a.name LIKE '%get%'
           OR a.name LIKE '%post%' OR a.name LIKE '%command%'
           OR a.name LIKE '%handler%' OR a.name LIKE '%register%'
           OR a.name LIKE '%fixture%' OR a.name LIKE '%receiver%'
           OR a.name LIKE '%signal%' OR a.name LIKE '%event%'
           OR a.name LIKE '%subscribe%' OR a.name LIKE '%hook%')
    ORDER BY s.sloc DESC LIMIT :lim"""),
(
    "dead-code",
    "Nothing in this tree calls these",
    "ANSWERS what might be deletable.\n"
    "ACT check `decorator-roots` first, then grep for the name as a string --\n"
    "     it may be reached by getattr or named in config. Then delete.\n"
    "MISLEADS the dominant cause of a wrong row is INHERITANCE, not dynamic\n"
    "     dispatch: a subclass override reached through a base-class reference\n"
    "     has no resolvable edge, and is_override fires on only 20 of\n"
    "     Django's 41k symbols -- any method whose name also exists on a\n"
    "     parent class is suspect. Beyond that, every dynamic\n"
    "     call in `reflection-opacity` is an edge that should have been here.\n"
    "     Public API meant for outside callers is excluded, but plugins are not.",
    """SELECT s.name, s.kind, s.sloc, s.cyclomatic AS cyclo,
        s.n_external_calls AS ext_calls,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.fan_in=0 AND s.kind IN ('function','method')
      AND s.is_public=0 AND s.is_test=0 AND s.is_entrypoint=0
      AND s.is_dunder=0 AND s.is_override=0 AND s.is_abstract=0
      AND s.is_property=0 AND s.is_overload=0
      AND f.is_test=0 AND f.is_generated=0
      AND NOT EXISTS (SELECT 1 FROM attributes a WHERE a.symbol_id=s.id)
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.sloc DESC LIMIT :lim"""),
(
    "untested",
    "Functions no test file reaches",
    "ANSWERS what is shipping without a test that touches it.\n"
    "ACT weigh by fan_in and risk -- an untested function 30 callers depend on\n"
    "     is a different problem from an untested one-liner.\n"
    "MISLEADS reachability from a test only proves a test EXECUTES it, not that\n"
    "     anything is asserted. And a test reaching it via getattr is invisible,\n"
    "     so this over-reports in metaprogramming-heavy code.",
    """SELECT s.name, s.fan_in, s.cyclomatic AS cyclo, s.sloc,
        s.risk_score AS risk, s.is_public AS public,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.kind IN ('function','method') AND f.is_test=0 AND s.is_test=0
      AND f.is_generated=0 AND s.sloc > 5
      AND COALESCE(m.name,'') LIKE :mod
      AND s.id NOT IN (
        SELECT e.callee_id FROM edges e
        JOIN symbols cs ON cs.id=e.caller_id
        JOIN files cf ON cf.id=cs.file_id
        WHERE cf.is_test=1 OR cs.is_test=1)
    ORDER BY s.risk_score DESC, s.fan_in DESC LIMIT :lim"""),
(
    "unbounded-caches",
    "@lru_cache / @cache with no maxsize, and module-level mutable state",
    "ANSWERS which caches can grow without limit for the life of the process.\n"
    "ACT give lru_cache a maxsize. A cache keyed on anything request-derived is\n"
    "     a memory leak with extra steps, and it also pins every key alive.\n"
    "MISLEADS a cache over a small fixed key space is fine unbounded. What\n"
    "     matters is whether the KEY comes from outside, which this cannot see.",
    """SELECT s.name AS symbol, 'cache-decorator' AS kind,
        a.name AS detail, s.n_params AS key_arity, s.fan_in,
        f.path || ':' || s.line_start AS at
    FROM symbols s
    JOIN attributes a ON a.symbol_id=s.id
    JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE (a.name LIKE '%lru_cache%' OR a.name LIKE '%cache%')
      AND a.args NOT LIKE '%maxsize%' AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    UNION ALL
    SELECT v.name, 'module-mutable', v.type, 0, 0,
        f.path || ':' || v.line
    FROM module_vars v JOIN files f ON f.id=v.file_id
    LEFT JOIN modules m ON m.id=v.module_id
    WHERE v.is_mutable_container=1 AND v.is_constant=0 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY 5 DESC LIMIT :lim"""),
(
    "shared-mutable-state",
    "Module-level mutable state, and who writes to it",
    "ANSWERS what is shared across every caller, thread and request.\n"
    "ACT under free-threading this is a data race, not a style question. Move\n"
    "     it into an object, or guard it.\n"
    "MISLEADS a module-level dict used as a read-only lookup table is fine.\n"
    "     `global` statement count is the evidence of actual writes.",
    """SELECT v.name, f.path, v.line, v.type,
        v.has_call_init AS built_by_call,
        (SELECT COUNT(*) FROM symbols s
         WHERE s.file_id=v.file_id AND s.n_global_stmt > 0) AS fns_using_global,
        (SELECT COALESCE(SUM(s.n_global_stmt),0) FROM symbols s
         WHERE s.file_id=v.file_id) AS global_stmts
    FROM module_vars v JOIN files f ON f.id=v.file_id
    LEFT JOIN modules m ON m.id=v.module_id
    WHERE v.is_mutable_container=1 AND v.is_constant=0
      AND f.is_test=0 AND f.is_generated=0 AND COALESCE(m.name,'') LIKE :mod
    ORDER BY global_stmts DESC, fns_using_global DESC LIMIT :lim"""),
(
    "import-cycles",
    "Modules that import each other",
    "ANSWERS which import pairs are mutually dependent.\n"
    "ACT a cycle forces import-time ordering hacks and function-level imports.\n"
    "     Break it by moving the shared type to a third module.\n"
    "MISLEADS this compares module names two levels deep, so a cycle inside one\n"
    "     package is invisible. `import-workarounds` is the corroborating\n"
    "     evidence that a cycle is really being worked around.",
    """SELECT m1.name AS module_a, m2.name AS module_b,
        COUNT(DISTINCT i1.id) AS a_imports_b,
        COUNT(DISTINCT i2.id) AS b_imports_a
    FROM imports i1
    JOIN files f1 ON f1.id=i1.file_id
    JOIN modules m1 ON m1.id=f1.module_id
    JOIN files f2 ON f2.id=i1.target_id
    JOIN modules m2 ON m2.id=f2.module_id
    JOIN imports i2 ON i2.file_id=f2.id
    JOIN files f3 ON f3.id=i2.target_id AND f3.module_id=m1.id
    WHERE m1.id < m2.id AND m1.name LIKE :mod
    GROUP BY m1.id, m2.id
    ORDER BY (a_imports_b + b_imports_a) DESC LIMIT :lim"""),
(
    "import-workarounds",
    "Imports hidden inside functions -- usually a cycle being dodged",
    "ANSWERS where import-time coupling was too painful to leave at the top.\n"
    "ACT each of these costs a dict lookup per call and hides a real dependency\n"
    "     from every tool that reads the import block. Fix the cycle instead.\n"
    "MISLEADS a function-level import is also the correct way to make a heavy\n"
    "     optional dependency lazy. Intent is not visible from the syntax.",
    """SELECT s.name AS inside_function, i.target AS imports_,
        i.kind, s.fan_in, i.line,
        f.path || ':' || i.line AS at
    FROM imports i
    JOIN files f ON f.id=i.file_id
    JOIN symbols s ON s.file_id=f.id
        AND i.line BETWEEN s.line_start AND s.line_end
        AND s.kind IN ('function','method')
    LEFT JOIN modules m ON m.id=f.module_id
    WHERE f.is_generated=0 AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.fan_in DESC LIMIT :lim"""),
(
    "resource-discipline",
    "Files, sockets and connections opened outside a with-block",
    "ANSWERS where a handle depends on the garbage collector to be released.\n"
    "ACT use `with`. CPython's refcounting usually saves you; PyPy and the\n"
    "     free-threaded build do not, and neither does an exception mid-function.\n"
    "MISLEADS a module-level file handle deliberately kept open for the process\n"
    "     lifetime is correct and appears here. n_with is the counter-evidence.",
    """SELECT s.name, s.n_open AS opens, s.n_resource AS resources,
        s.n_with AS with_blocks, s.n_ctx_managers AS ctx_mgrs,
        s.n_try AS trys, s.n_finally AS finallys,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE (s.n_open + s.n_resource) > s.n_ctx_managers
      AND (s.n_open + s.n_resource) > 0 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY (s.n_open + s.n_resource - s.n_ctx_managers) DESC LIMIT :lim"""),
(
    "weak-crypto",
    "md5, sha1, and the random module used where secrets belongs",
    "ANSWERS which code uses a hash or RNG unfit for a security purpose.\n"
    "ACT `random` is a Mersenne Twister -- predictable from ~624 outputs. Use\n"
    "     `secrets` for anything a user should not be able to guess.\n"
    "MISLEADS md5 for a cache key or a file checksum is fine, and `random` for\n"
    "     sampling or jitter is fine. Purpose is not visible from the call.",
    """SELECT s.name, h.pattern, h.n, h.first_line, s.is_public AS public,
        s.fan_in, f.path || ':' || h.first_line AS at
    FROM hazards h
    JOIN symbols s ON s.id=h.symbol_id
    JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE h.category='crypto' AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.fan_in DESC, h.n DESC LIMIT :lim"""),
(
    "concurrency-surface",
    "Everything that spawns, locks or shares, in one place",
    "ANSWERS what the free-threaded build has to be correct about.\n"
    "ACT read these together with `shared-mutable-state`. A thread target that\n"
    "     touches module-level state is a race the GIL used to hide.\n"
    "MISLEADS counting a Lock says nothing about whether it is the RIGHT lock,\n"
    "     or held long enough. This finds the surface, not the bugs on it.",
    """SELECT s.name, s.n_concurrency AS concurrency, s.n_global_stmt AS globals_,
        s.lock_in_loop AS locks_in_loop, s.is_async AS async_,
        s.n_blocking AS blocking, s.fan_in,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_concurrency > 0 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.n_concurrency DESC, s.n_global_stmt DESC LIMIT :lim"""),
(
    "unsafe-decode-reachable",
    "pickle, yaml.load and eval, and how far they sit from something that takes input",
    "ANSWERS which of bandit's deserialization findings actually matter here.\n"
    "     S301 and S506 fire on every pickle and every yaml.load in the tree,\n"
    "     including the ones only a build script reaches. The question they\n"
    "     cannot answer alone is whether attacker-controlled bytes get there.\n"
    "ACT work down from hops=0. A pickle.load inside a request handler is\n"
    "     remote code execution; the same call in a management command run by\n"
    "     an operator is a design smell at worst. Replace with JSON, or sign\n"
    "     the payload and verify before decoding.\n"
    "MISLEADS reachability here is the CALL graph only, so a handler that\n"
    "     dispatches through a registry, a signal, or a Celery task name looks\n"
    "     unreachable and is not. hops is a lower bound on distance, never an\n"
    "     upper bound on safety, and bandit's own false-positive rate on S301\n"
    "     comes along unchanged -- a pickle of a constant is still counted.",
    """WITH RECURSIVE walk(root, sym, depth) AS (
        SELECT s.id, s.id, 0 FROM symbols s
        WHERE s.is_entrypoint = 1 OR s.is_public = 1
        UNION
        SELECT w.root, e.callee_id, w.depth + 1
        FROM walk w JOIN edges e ON e.caller_id = w.sym
        WHERE w.depth < 4 AND e.is_self = 0),      -- depth bound: 4 hops
    reach(root, sym, depth) AS (
        SELECT root, sym, MIN(depth) FROM walk GROUP BY root, sym)
    SELECT s.name, src.name AS reached_from, MIN(r.depth) AS hops,
        s.n_pickle_load AS pickles, s.n_yaml_load AS yaml_loads,
        s.n_eval_exec AS evals, s.n_subprocess AS subprocs,
        s.fan_in, m.name AS module_,
        f.path || ':' || s.line_start AS at
    FROM reach r
    JOIN symbols s ON s.id = r.sym
    JOIN symbols src ON src.id = r.root
    JOIN files f ON f.id = s.file_id
    LEFT JOIN modules m ON m.id = s.module_id
    WHERE (s.n_pickle_load + s.n_yaml_load + s.n_eval_exec) > 0
      AND f.is_test = 0 AND COALESCE(m.name,'') LIKE :mod
    GROUP BY s.id, src.id
    ORDER BY hops ASC, (s.n_pickle_load + s.n_eval_exec) DESC LIMIT :lim"""),
(
    "bare-except",
    "Bare except: clause without an exception type (bandit E722/pylint W0702)",
    "ANSWERS where a bare except: catches every exception including\n"
    "     KeyboardInterrupt and SystemExit, making the program un-killable and\n"
    "     hiding real bugs.\n"
    "ACT catch Exception or a specific exception type; never bare except.\n"
    "MISLEADS a bare except that immediately re-raises is correct but rare.",
    """SELECT s.name, s.n_bare_except AS bare_excepts,
        s.n_catch_swallow AS swallowed,
        s.n_reraise AS reraises,
        s.n_catch AS total_catches,
        s.fan_in, s.cyclomatic AS cyclo,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_bare_except > 0 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.n_bare_except DESC, s.fan_in DESC LIMIT :lim"""),
(
    "pickle-deserialization",
    "pickle.load or pickle.loads on untrusted input (bandit S301/S302)",
    "ANSWERS where pickle deserialization is used, which can execute arbitrary\n"
    "     code during deserialization. A crafted pickle stream is an RCE vector.\n"
    "ACT use json, or restrict with a custom Unpickler that whitelists classes.\n"
    "MISLEADS loading a trusted internal pickle is safe. The graph sees the call\n"
    "     but not the input source.",
    """SELECT s.name, s.n_pickle_load AS pickle_loads,
        s.n_eval_exec AS eval_execs,
        s.n_yaml_load AS yaml_loads,
        s.fan_in,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_pickle_load > 0 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.fan_in DESC, s.n_pickle_load DESC LIMIT :lim"""),
(
    "yaml-unsafe-load",
    "yaml.load without SafeLoader (bandit S506)",
    "ANSWERS where yaml.load is called without specifying SafeLoader, which can\n"
    "     construct arbitrary Python objects from YAML tags.\n"
    "ACT use yaml.safe_load or yaml.load(stream, Loader=yaml.SafeLoader).\n"
    "MISLEADS a yaml.load that explicitly passes SafeLoader is safe; the graph\n"
    "     counts the call but does not verify the Loader argument.",
    """SELECT s.name, s.n_yaml_load AS yaml_loads,
        s.n_pickle_load AS pickle_loads,
        s.fan_in, s.cyclomatic AS cyclo,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_yaml_load > 0 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.fan_in DESC, s.n_yaml_load DESC LIMIT :lim"""),
(
    "subprocess-shell-injection",
    "subprocess with shell=True (bandit S602/S603)",
    "ANSWERS where subprocess is called with shell=True, which passes the\n"
    "     command through the shell, enabling command injection if any part is\n"
    "     user-controlled.\n"
    "ACT use shell=False and pass args as a list.\n"
    "MISLEADS shell=True with a constant string is safe. n_shell_true counts\n"
    "     shell=True sites; the graph cannot see whether args are dynamic.",
    """SELECT s.name, s.n_subprocess AS subprocess_calls,
        s.n_shell_true AS shell_true,
        s.n_os_system AS os_system,
        s.n_eval_exec AS eval_execs,
        s.fan_in,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_subprocess > 0 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.fan_in DESC, s.n_shell_true DESC LIMIT :lim"""),
(
    "eval-exec-injection",
    "eval() or exec() on dynamic input (bandit S307/pylint W0122)",
    "ANSWERS where eval() or exec() is called, which executes arbitrary Python.\n"
    "     If the input is user-controlled, this is an RCE.\n"
    "ACT use ast.literal_eval for literal parsing; never eval user input.\n"
    "MISLEADS eval in a test or a REPL is correct. The graph sees the call but\n"
    "     not the input source.",
    """SELECT s.name, s.n_eval_exec AS eval_execs,
        s.n_dynamic_attr AS dynamic_attrs,
        s.n_pickle_load AS pickle_loads,
        s.fan_in,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_eval_exec > 0 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.fan_in DESC, s.n_eval_exec DESC LIMIT :lim"""),
(
    "assert-in-production",
    "assert used for validation in production code (bandit B101)",
    "ANSWERS where assert is used for input validation in non-test code. Running\n"
    "     Python with -O strips all asserts, so the validation disappears.\n"
    "ACT raise a ValueError or TypeError instead of asserting.\n"
    "MISLEADS assert in test files is correct. The is_test filter excludes tests.",
    """SELECT s.name, s.n_assert AS asserts,
        s.n_assert_in_loop AS asserts_in_loop,
        s.fan_in, s.cyclomatic AS cyclo,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_assert > 0 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.fan_in DESC, s.n_assert DESC LIMIT :lim"""),
(
    "global-statement",
    "global statement in a function (pylint W0603)",
    "ANSWERS where a function uses the global keyword, creating hidden mutable\n"
    "     state that makes the function non-reentrant and hard to test.\n"
    "ACT pass the value as a parameter and return the new value.\n"
    "MISLEADS a global for a module-level configuration that is set once at\n"
    "     startup is a known pattern.",
    """SELECT s.name, s.n_global_stmt AS global_stmts,
        s.n_nonlocal AS nonlocal_stmts,
        s.n_assign AS assignments,
        s.fan_in, s.cyclomatic AS cyclo,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_global_stmt > 0 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.fan_in DESC, s.n_global_stmt DESC LIMIT :lim"""),
(
    "open-without-with",
    "open() without a with statement (bandit/PSS)",
    "ANSWERS where open() is called without a context manager, so the file may\n"
    "     not be closed if an exception occurs between open and close.\n"
    "ACT use `with open(path) as f:`.\n"
    "MISLEADS open without with that is immediately followed by try/finally is\n"
    "     correct but verbose. The graph sees n_open vs n_with but not the\n"
    "     control flow between them.",
    """SELECT s.name, s.n_open AS opens,
        s.n_with AS withs, s.n_try AS tries,
        s.n_finally AS finallys,
        s.fan_in, s.cyclomatic AS cyclo,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_open > 0 AND s.n_with=0 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.fan_in DESC, s.n_open DESC LIMIT :lim"""),
(
    "datetime-naive",
    "datetime without timezone (bandit DTZ003/DTZ005)",
    "ANSWERS where datetime is used without timezone awareness, causing bugs\n"
    "     when comparing or storing timestamps across time zones.\n"
    "ACT use timezone-aware datetimes: datetime.now(timezone.utc).\n"
    "MISLEADS a naive datetime for local display is sometimes correct. The graph\n"
    "     counts the pattern but not the context.",
    """SELECT s.name, s.n_naive_datetime AS naive_datetimes,
        s.n_open_no_encoding AS open_no_encoding,
        s.fan_in, s.cyclomatic AS cyclo,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_naive_datetime > 0 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.fan_in DESC, s.n_naive_datetime DESC LIMIT :lim"""),
(
    "append-in-loop-perf",
    "List append inside a loop without pre-allocation (perf)",
    "ANSWERS where list.append is called inside a loop, causing repeated\n"
    "     reallocations as the list grows. For large loops this is slow.\n"
    "ACT use a list comprehension or pre-allocate with [None]*n.\n"
    "MISLEADS a loop that appends conditionally cannot be replaced with a\n"
    "     comprehension. append_in_loop is a site count, not a size estimate.",
    """SELECT s.name, s.append_in_loop AS appends_in_loop,
        s.n_range_len AS range_lens,
        s.n_loops AS loops, s.cyclomatic AS cyclo, s.fan_in,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.append_in_loop > 0 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.append_in_loop DESC, s.n_loops DESC LIMIT :lim""")
]

METRICS = [
(
    "graph-blindspots",
    "Read this first: where the call graph cannot see",
    "ANSWERS how much of every other answer here is guesswork.\n"
    "ACT if a module is high on this list, treat its reachability results as a\n"
    "     lower bound. getattr and importlib dispatch are invisible to a reader.\n"
    "MISLEADS a resolved call can still be wrong -- name-based resolution picks\n"
    "     the unique definition of a name, and two classes with the same method\n"
    "     name are refused rather than guessed, landing here instead.",
    """SELECT m.name AS module,
        COUNT(DISTINCT s.id) AS fns,
        COALESCE(SUM(s.n_calls),0) AS calls,
        COALESCE(SUM(s.n_unresolved_calls),0) AS unresolved,
        COALESCE(SUM(s.n_dynamic_calls),0) AS computed,
        (SELECT COUNT(*) FROM dynamic_sites d
         JOIN symbols s2 ON s2.id=d.symbol_id
         WHERE s2.module_id=m.id) AS reflect_sites,
        CAST(100.0 * SUM(s.n_unresolved_calls)
             / NULLIF(SUM(s.n_calls),0) AS INT) AS pct_blind
    FROM symbols s JOIN modules m ON m.id=s.module_id
    WHERE s.kind IN ('function','method') AND m.name LIKE :mod
    GROUP BY m.id HAVING calls > 0
    ORDER BY unresolved DESC LIMIT :lim"""),
(
    "risk-ranked",
    "Review order: if you can only read N functions this week, which N",
    "ANSWERS which functions combine complexity with dangerous operations.\n"
    "ACT start at the top. The score weights exec/deserialize/SQL-building far\n"
    "     above raw complexity, because a simple function that evals is worse\n"
    "     than a complicated one that does arithmetic.\n"
    "MISLEADS it is a heuristic, not a finding. A high score means 'look', not\n"
    "     'bug'. Generated and vendored files are excluded, so the real top of\n"
    "     the list may sit in code this filter hid.",
    """SELECT s.name, s.risk_score AS risk, s.cyclomatic AS cyclo,
        s.cognitive AS cog, s.max_nesting AS nest,
        s.n_exec + s.n_deserialize AS danger, s.n_sql_fstring
            + s.n_sql_concat + s.n_sql_format AS sqlbuild,
        s.n_shell_true AS shell, s.fan_in,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.kind IN ('function','method') AND f.is_generated=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.risk_score DESC LIMIT :lim"""),
(
    "hot-multipliers",
    "Where one fix pays back many times: highest fan-in",
    "ANSWERS which functions the rest of the tree leans on hardest.\n"
    "ACT a correctness or speed win in a high-fan-in leaf pays once per caller.\n"
    "MISLEADS fan_in counts STATIC call sites, not runtime frequency. Worse,\n"
    "     calls resolve by BARE NAME, so a method sharing a builtin name\n"
    "     absorbs every call site in the tree: Django's 12-line `super`\n"
    "     method collects all 1,285 super() calls and ranks second. A short\n"
    "     function with four-digit fan_in is a name collision, not a hot\n"
    "     leaf. Test callers are counted too.",
    """SELECT s.name, s.fan_in, s.n_callsites AS sites, s.fan_out,
        s.cyclomatic AS cyclo, s.sloc, s.has_doc AS doc,
        COALESCE(m.name,'') AS module,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.kind IN ('function','method') AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.fan_in DESC, s.cyclomatic DESC LIMIT :lim"""),
(
    "typing-holes",
    "Public API without type annotations, ranked by blast radius",
    "ANSWERS which unannotated functions the most other code depends on.\n"
    "ACT annotate high-fan-in functions first: every caller inherits the\n"
    "     uncertainty, so one signature fixes many call sites for a checker.\n"
    "MISLEADS an unannotated private helper is fine. This ranks by fan_in for\n"
    "     that reason, and counts `self`/`cls` as untyped, which they are.",
    """SELECT s.name, s.n_params, s.n_untyped_params AS untyped,
        s.has_return_type AS ret_typed, s.fan_in, s.is_public AS public,
        CAST(100.0 * s.n_annotated_params / NULLIF(s.n_params,0) AS INT) AS pct,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.kind IN ('function','method') AND s.is_public=1
      AND s.n_untyped_params > 0 AND f.is_generated=0 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.fan_in DESC, s.n_untyped_params DESC LIMIT :lim"""),
(
    "god-functions",
    "Functions doing too much, by every measure at once",
    "ANSWERS which functions are hardest to hold in your head.\n"
    "ACT split by responsibility, not by line count. The n_elif column tells\n"
    "     you whether it is a dispatch table (extract to a dict) or real nesting.\n"
    "MISLEADS a long flat dispatch is far easier to read than a short deeply\n"
    "     nested one. Sort by cognitive rather than sloc for that reason.",
    """SELECT s.name, s.sloc, s.cyclomatic AS cyclo, s.cognitive AS cog,
        s.max_nesting AS nest, s.n_elif AS elifs, s.n_returns AS returns,
        s.n_locals AS locals_, s.n_params, s.maintainability AS maint,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.kind IN ('function','method') AND f.is_generated=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.cognitive DESC LIMIT :lim"""),
(
    "deep-nesting",
    "Nesting deep enough that the reader loses the thread",
    "ANSWERS which functions need guard clauses.\n"
    "ACT invert the condition and return early. Each level removed is a level\n"
    "     of context the next reader does not have to carry.\n"
    "MISLEADS elif chains are correctly NOT counted as nesting here -- a 30-arm\n"
    "     dispatch is flat. What is counted is genuine block nesting.",
    """SELECT s.name, s.max_nesting AS nest, s.max_loop_depth AS loops,
        s.cognitive AS cog, s.sloc, s.n_early_returns AS early_ret,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.max_nesting >= 4 AND f.is_generated=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.max_nesting DESC, s.cognitive DESC LIMIT :lim"""),
(
    "nested-loops",
    "Nested loops: where the input size decides whether this matters",
    "ANSWERS which functions have quadratic or worse structure.\n"
    "ACT depth 2 over a small collection is fine; depth 3 over anything\n"
    "     user-sized is a design question. Look for a dict that removes a level.\n"
    "MISLEADS depth is syntactic. Two loops over a 3-element constant is depth 2\n"
    "     and costs nothing. Collection size is invisible to a static reader.",
    """SELECT s.name, s.max_loop_depth AS depth, s.n_loops AS loops,
        s.call_in_loop AS calls, s.n_subscript AS subscripts,
        s.sloc, s.fan_in, f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.max_loop_depth >= 2 AND f.is_generated=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.max_loop_depth DESC, s.call_in_loop DESC LIMIT :lim"""),
(
    "class-shape",
    "Classes carrying too much, and classes carrying nothing",
    "ANSWERS which classes are god objects and which are anaemic wrappers.\n"
    "ACT a class with 40 methods and 30 attributes is several classes. A class\n"
    "     with two attributes and no methods wants to be a dataclass or a tuple.\n"
    "MISLEADS inherited members are not counted -- only what this class declares.\n"
    "     A thin subclass of a fat base looks small here and is not.",
    """SELECT s.name, c.n_methods AS methods, c.n_class_vars AS class_vars,
        c.n_bases AS bases, c.bases, c.n_abstract_methods AS abstract,
        c.has_slots AS slots, c.is_dataclass AS dataclass_,
        s.n_lines AS lines, f.path || ':' || s.line_start AS at
    FROM classes c
    JOIN symbols s ON s.id=c.symbol_id
    JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE f.is_generated=0 AND COALESCE(m.name,'') LIKE :mod
    ORDER BY (c.n_methods + c.n_class_vars) DESC LIMIT :lim"""),
(
    "slots-candidates",
    "Classes instantiated in a loop that carry no __slots__",
    "ANSWERS where per-instance dict overhead is being paid at volume.\n"
    "ACT __slots__ removes the instance __dict__ -- typically 30-40%% less\n"
    "     memory per object and faster attribute access.\n"
    "MISLEADS __slots__ breaks multiple inheritance, weakrefs and dynamic\n"
    "     attribute assignment. It is a change to the class contract, not a\n"
    "     free win, and only pays at thousands of instances.",
    """SELECT s.name AS class_, c.n_class_vars AS attrs, c.n_methods AS methods,
        c.is_dataclass AS dataclass_,
        (SELECT COUNT(*) FROM callsites cs
         JOIN symbols caller ON caller.id=cs.caller_id
         WHERE cs.callee_id=s.id AND caller.max_loop_depth > 0) AS built_in_loop,
        s.fan_in, f.path || ':' || s.line_start AS at
    FROM classes c
    JOIN symbols s ON s.id=c.symbol_id
    JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE c.has_slots=0 AND c.is_enum=0 AND c.is_exception=0
      AND f.is_generated=0 AND COALESCE(m.name,'') LIKE :mod
    ORDER BY built_in_loop DESC, s.fan_in DESC LIMIT :lim"""),
(
    "module-coupling",
    "Which modules depend on which, and how unstable that makes them",
    "ANSWERS which modules are hard to change because everything leans on them.\n"
    "ACT instability near 0 with high fan_in means many depend on it and it\n"
    "     depends on little -- that is a good place for stable abstractions and\n"
    "     a bad place for volatile logic.\n"
    "MISLEADS instability is a ratio, so a module with one edge each way scores\n"
    "     0.5 and means nothing. Read it alongside n_files.",
    """SELECT name, kind, n_files AS files, sloc, n_symbols AS syms,
        n_public AS public, fan_in, fan_out,
        ROUND(instability, 2) AS instability
    FROM modules
    WHERE n_files > 0 AND name LIKE :mod
    ORDER BY (fan_in + fan_out) DESC LIMIT :lim"""),
(
    "undocumented-complexity",
    "The hardest functions, with nothing written down",
    "ANSWERS where the next reader has to reconstruct intent from the code.\n"
    "ACT one sentence on what it does and what it assumes. Prefer the public,\n"
    "     high-fan-in end of the list -- that is where the cost compounds.\n"
    "MISLEADS a docstring is not understanding. This finds absence, not quality,\n"
    "     and short obvious functions correctly do not need one.",
    """SELECT s.name, s.cyclomatic AS cyclo, s.cognitive AS cog, s.sloc,
        s.n_params, s.fan_in, s.is_public AS public,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.has_doc=0 AND s.kind IN ('function','method')
      AND s.cyclomatic >= 8 AND f.is_generated=0 AND f.is_test=0
      AND s.is_dunder=0 AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.cyclomatic DESC, s.fan_in DESC LIMIT :lim"""),
(
    "magic-numbers",
    "Unexplained constants, and the ones repeated across files",
    "ANSWERS which literals are load-bearing but unnamed.\n"
    "ACT a number appearing in several files is a shared assumption with no\n"
    "     name. Name it once and import it, so changing it is one edit.\n"
    "MISLEADS obvious values (0, 1, powers of two, 100, 1000, time units) are\n"
    "     already filtered out. What is left still includes plenty of harmless\n"
    "     array indices.",
    """SELECT l.value, COUNT(*) AS uses, COUNT(DISTINCT l.file_id) AS files,
        COUNT(DISTINCT l.symbol_id) AS fns,
        GROUP_CONCAT(DISTINCT f.basename) AS seen_in
    FROM literals l JOIN files f ON f.id=l.file_id
    LEFT JOIN modules m ON m.id=f.module_id
    WHERE l.is_magic=1 AND f.is_test=0 AND f.is_generated=0
      AND COALESCE(m.name,'') LIKE :mod
    GROUP BY l.value HAVING files > 1
    ORDER BY uses DESC LIMIT :lim"""),
(
    "markers",
    "TODO, FIXME, HACK and BUG, weighted by the code they sit in",
    "ANSWERS which unfinished business sits in code that matters.\n"
    "ACT a FIXME in a function 40 things depend on outranks a TODO in a script.\n"
    "MISLEADS marker age is invisible here -- git blame is the missing column.\n"
    "     Many of these were resolved years ago and the comment stayed.",
    """SELECT k.kind, f.path, k.line, SUBSTR(k.text, 1, 60) AS text,
        COALESCE(s.name,'(module level)') AS in_fn,
        COALESCE(s.fan_in,0) AS fan_in
    FROM markers k
    JOIN files f ON f.id=k.file_id
    LEFT JOIN modules m ON m.id=f.module_id
    LEFT JOIN symbols s ON s.file_id=f.id
        AND k.line BETWEEN s.line_start AND s.line_end
        AND s.kind IN ('function','method')
    WHERE k.kind IN ('TODO','FIXME','HACK','BUG','XXX','WARNING')
      AND f.is_generated=0 AND COALESCE(m.name,'') LIKE :mod
    ORDER BY COALESCE(s.fan_in,0) DESC LIMIT :lim"""),
(
    "parse-coverage",
    "What this run could not read",
    "ANSWERS whether the numbers above cover the code you think they cover.\n"
    "ACT a file listed here contributed nothing. If your interpreter is older\n"
    "     than the target's syntax, run this on that version instead.\n"
    "MISLEADS a file can parse perfectly and still be misunderstood. This shows\n"
    "     only hard failures, not wrong interpretations.",
    """SELECT f.path, f.lines, f.n_parse_errors AS errors, f.parsed,
        f.is_generated AS generated, f.is_vendored AS vendored,
        f.is_test AS test, f.bytes
    FROM files f
    LEFT JOIN modules m ON m.id=f.module_id
    WHERE (f.n_parse_errors > 0 OR f.parsed = 0)
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY f.lines DESC LIMIT :lim"""),
(
    "latent-risk-density",
    "Cheap linter facts that only matter together, ranked by who depends on them",
    "ANSWERS which functions carry several small smells at once in code that\n"
    "     many things call. Each fact here is individually reported by ruff or\n"
    "     bandit and individually ignorable -- an open() without encoding, a\n"
    "     naive datetime, a getattr on a computed name, an md5. A function\n"
    "     with four of them that 200 callers reach is a different proposition.\n"
    "ACT read `facts` as a count of DISTINCT smells, not severity. Start where\n"
    "     facts and fan_in are both high: that is where one careful rewrite\n"
    "     retires several warnings and the blast radius justifies the risk.\n"
    "MISLEADS this deliberately mixes security and correctness facts, so a\n"
    "     high score can be four harmless portability warnings. It ranks\n"
    "     ATTENTION, not danger -- read the columns, not the total. Encoding\n"
    "     and timezone defaults are also platform-dependent, so a codebase\n"
    "     that only ever runs in one container may have decided already.",
    """SELECT s.name, m.name AS module_,
        (CASE WHEN s.n_open_no_encoding > 0 THEN 1 ELSE 0 END
         + CASE WHEN s.n_naive_datetime > 0 THEN 1 ELSE 0 END
         + CASE WHEN s.n_dynamic_attr > 0 THEN 1 ELSE 0 END
         + CASE WHEN s.n_weak_hash > 0 THEN 1 ELSE 0 END
         + CASE WHEN s.n_weak_random > 0 THEN 1 ELSE 0 END
         + CASE WHEN s.n_request_no_timeout > 0 THEN 1 ELSE 0 END
         + CASE WHEN s.n_sleep_in_loop > 0 THEN 1 ELSE 0 END
         + CASE WHEN s.n_bare_except > 0 THEN 1 ELSE 0 END) AS facts,
        s.n_open_no_encoding AS open_noenc, s.n_naive_datetime AS naive_dt,
        s.n_dynamic_attr AS dyn_attr, s.n_weak_hash AS weak_hash,
        s.n_request_no_timeout AS no_timeout, s.n_bare_except AS bare_except,
        s.fan_in, s.cyclomatic AS cyclo,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id = s.file_id
    LEFT JOIN modules m ON m.id = s.module_id
    WHERE f.is_test = 0 AND COALESCE(m.name,'') LIKE :mod
      AND (s.n_open_no_encoding + s.n_naive_datetime + s.n_dynamic_attr
           + s.n_weak_hash + s.n_weak_random + s.n_request_no_timeout
           + s.n_sleep_in_loop + s.n_bare_except) > 0
    ORDER BY facts DESC, s.fan_in DESC, s.cyclomatic DESC LIMIT :lim"""),
(
    "too-many-locals",
    "Function with too many local variables (pylint R0914)",
    "ANSWERS where a function has more than 15 local variables, making it hard\n"
    "     to track state and reason about.\n"
    "ACT extract a helper class or split the function.\n"
    "MISLEADS a data-processing function with many locals is sometimes the\n"
    "     clearest form.",
    """SELECT s.name, s.n_locals,
        s.n_params, s.sloc, s.cyclomatic AS cyclo,
        s.max_nesting AS nesting, s.fan_in,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_locals > 15 AND s.kind IN ('function','method')
      AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.n_locals DESC, s.cyclomatic DESC LIMIT :lim"""),
(
    "too-many-branches",
    "Function with too many branches (pylint R0912)",
    "ANSWERS where a function has more than 12 branches, making it hard to\n"
    "     verify all paths.\n"
    "ACT use a dispatch table, polymorphism, or extract branches into helpers.\n"
    "MISLEADS a switch-like if/elif chain with many arms is branchy but linear.\n"
    "     cyclomatic is a better measure of actual complexity.",
    """SELECT s.name, s.n_branches AS branches,
        s.n_switch AS switches, s.n_cases AS cases,
        s.cyclomatic AS cyclo, s.sloc, s.fan_in,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_branches > 12 AND s.kind IN ('function','method')
      AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.n_branches DESC, s.cyclomatic DESC LIMIT :lim"""),
(
    "too-many-return",
    "Function with too many return statements (pylint R0911)",
    "ANSWERS where a function has more than 6 return statements, making it hard\n"
    "     to verify all exit paths and resource cleanup.\n"
    "ACT consolidate returns, or use a result variable with a single exit point.\n"
    "MISLEADS guard clauses (early returns) are good style; the count alone does\n"
    "     not distinguish guard returns from scattered mid-function returns.",
    """SELECT s.name, s.n_returns AS returns,
        s.n_early_returns AS early_returns,
        s.n_finally AS finally_blocks,
        s.cyclomatic AS cyclo, s.fan_in,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_returns > 6 AND s.kind IN ('function','method')
      AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.n_returns DESC, s.cyclomatic DESC LIMIT :lim"""),
(
    "scattered-concerns",
    "A function called from many different modules (shotgun surgery)",
    "ANSWERS which functions are called from many distinct modules, so any change\n"
    "     ripples widely.\n"
    "ACT consider splitting the function or making the contract more stable.\n"
    "MISLEADS a utility like `log` or `config` is called from everywhere and is\n"
    "     intentionally stable.",
    """SELECT s.name, COUNT(DISTINCT m.id) AS n_caller_modules,
        s.fan_in, s.cyclomatic AS cyclo, s.sloc,
        GROUP_CONCAT(DISTINCT m.name) AS modules,
        f.path || ':' || s.line_start AS at
    FROM symbols s
    JOIN edges e ON e.callee_id=s.id
    JOIN symbols caller ON caller.id=e.caller_id
    LEFT JOIN modules m ON m.id=caller.module_id
    JOIN files f ON f.id=s.file_id
    WHERE s.kind IN ('function','method') AND f.is_test=0
      AND e.is_self=0 AND COALESCE(m.name,'') LIKE :mod
    GROUP BY s.id
    HAVING n_caller_modules > 5
    ORDER BY n_caller_modules DESC, s.fan_in DESC LIMIT :lim"""),
(
    "line-too-long",
    "Files with very long lines (pylint C0301)",
    "ANSWERS which files have lines exceeding 100 characters, which hurts\n"
    "     readability and may break some tools.\n"
    "ACT wrap long lines; the max_line_len column gives the worst line.\n"
    "MISLEADS generated or minified files have long lines by design. The\n"
    "     is_generated filter excludes those.",
    """SELECT f.path, f.max_line_len,
        f.sloc, f.lines, f.n_symbols,
        f.path || ':' || 0 AS at
    FROM files f
    LEFT JOIN modules m ON m.id=f.module_id
    WHERE f.max_line_len > 100 AND f.is_test=0 AND f.is_generated=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY f.max_line_len DESC LIMIT :lim"""),
(
    "untyped-params",
    "Functions with no type annotations (pylint/mypy)",
    "ANSWERS where a function has parameters without type annotations, so the\n"
    "     contract is implicit and static analysis cannot check it.\n"
    "ACT add type annotations to all parameters and the return type.\n"
    "MISLEADS a stub or protocol function may omit annotations intentionally.\n"
    "     n_untyped_params counts the untyped ones; n_annotated_params the typed.",
    """SELECT s.name, s.n_untyped_params AS untyped_params,
        s.n_annotated_params AS annotated_params,
        s.n_params, s.has_return_type AS has_return_type,
        s.fan_in, s.is_public,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_untyped_params > 0 AND s.is_public=1 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.fan_in DESC, s.n_untyped_params DESC LIMIT :lim"""),
(
    "deep-nesting-excessive",
    "Functions with excessive nesting depth (pylint R1702)",
    "ANSWERS where a function has max_nesting > 5, making it hard to read and\n"
    "     test. Each level multiplies the test matrix.\n"
    "ACT extract nested blocks into named helper functions; use early returns.\n"
    "MISLEADS a deeply nested comprehension is a single expression, not\n"
    "     structural nesting. The column measures structural nesting.",
    """SELECT s.name, s.max_nesting AS nesting,
        s.cyclomatic AS cyclo, s.cognitive AS cognitive,
        s.n_loops AS loops, s.sloc, s.fan_in,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.max_nesting > 5 AND s.kind IN ('function','method')
      AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.max_nesting DESC, s.cyclomatic DESC LIMIT :lim"""),
(
    "god-class",
    "A class with too many methods and high complexity (pylint R0902)",
    "ANSWERS which classes have too many methods and too much complexity.\n"
    "ACT split the class along responsibility lines.\n"
    "MISLEADS a framework base class may be intentionally broad.",
    """SELECT s.name,
        (SELECT COUNT(*) FROM symbols c WHERE c.parent_id=s.id
         AND c.kind='method') AS n_methods,
        (SELECT SUM(c.cyclomatic) FROM symbols c WHERE c.parent_id=s.id
         AND c.kind='method') AS total_cyclo,
        s.fan_in, s.sloc,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.kind='class' AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY total_cyclo DESC LIMIT :lim""")
]

_SYMBOL_COLS: set[str] = set()

def _init_symbol_cols() -> None:
    """Which metric keys the schema actually has.

    Checked once so a typo in a metric name is a loud failure at import time
    rather than a column that silently stays zero for the life of the tool.
    """
    base = """n_params n_optional_params n_generic_params n_overloads arity_rank
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
    n_hazards risk_score""".split()
    _SYMBOL_COLS.update(base)
    _SYMBOL_COLS.update("n_" + c for c in HAZARD_CATEGORIES)
    _SYMBOL_COLS.update(n for n, _ in PythonAnalyzer.EXTRA_SYMBOL_COLS)

_init_symbol_cols()

PythonAnalyzer.QUERIES = QUERIES
PythonAnalyzer.METRICS = METRICS

ANALYZER = PythonAnalyzer()


if __name__ == "__main__":
    try:
        sys.exit(main(ANALYZER))
    except KeyboardInterrupt:
        print("\ninterrupted", file=sys.stderr)
        sys.exit(130)
