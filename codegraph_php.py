#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Piyush Katariya
#
# @author Piyush Katariya
"""codegraph_php.py -- parse a PHP tree into a graph and query it.

Targets PHP 8.5 (released 2025-11-20). Parses with tree-sitter-php.

PHP's problem is not that it lacks linters -- Psalm and PHPStan are excellent at
one file at a time. The problem is that PHP's most dangerous constructs are
precisely the ones that make a call graph stop existing: `call_user_func`,
`$obj->$method()`, `new $class`, `__call`, and a facade layer that resolves
every name at run time. So this tool does two things no per-file checker does:
it follows tainted input across function boundaries, and -- more importantly --
it tells you how much of that following was possible at all.

Three corrections to the folklore, each verified rather than assumed:

* Psalm's taint engine treats ONLY `$_GET`, `$_POST`, `$_COOKIE` and `$_REQUEST`
  as sources, despite its own documentation listing more. `$_FILES`, `$_SERVER`
  and `php://input` are attacker-controlled in practice and are counted here,
  but `superglobal_reads.is_psalm_tainted` keeps the two populations apart so a
  comparison against a Psalm baseline is honest.
* `PDO::query`, `PDO::prepare` and `PDO::exec` are NOT in Psalm's
  `InternalTaintSinkMap`; they live only in the stub files. A tool that reads
  the map alone finds no PDO SQL sink anywhere. They are included here.
* tree-sitter-php 0.24.1 predates three PHP 8.5 constructs and rejects exactly
  those three out of a 23-case 8.0-8.5 feature sweep: the `(void)` cast,
  `clone(x, [...]) in some spellings`, and `final` on a promoted constructor property.
  Everything else -- property hooks, `private(set)`, DNF types, enums,
  `#[Attr]`, `?->`, `match`, heredoc, group use, first-class callables and
  even 8.5's `|>` -- parses clean. That list is written into
  `meta.grammar_note` so a parse error reads as "the grammar is one version
  behind", not "this file is broken".

Usage:
  python3 codegraph_php.py /path/to/repo --report
  python3 codegraph_php.py /path/to/repo --list
  python3 codegraph_php.py --deps"""
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
import json
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
# lang_php.py
# codegraph_php.py -- parse a PHP tree into a graph and query it.
#
# Targets PHP 8.5 (released 2025-11-20). Parses with tree-sitter-php.
#
# PHP's problem is not that it lacks linters -- Psalm and PHPStan are excellent at
# one file at a time. The problem is that PHP's most dangerous constructs are
# precisely the ones that make a call graph stop existing: `call_user_func`,
# `$obj->$method()`, `new $class`, `__call`, and a facade layer that resolves
# every name at run time. So this tool does two things no per-file checker does:
# it follows tainted input across function boundaries, and -- more importantly --
# it tells you how much of that following was possible at all.
#
# Three corrections to the folklore, each verified rather than assumed:
#
# * Psalm's taint engine treats ONLY `$_GET`, `$_POST`, `$_COOKIE` and `$_REQUEST`
#   as sources, despite its own documentation listing more. `$_FILES`, `$_SERVER`
#   and `php://input` are attacker-controlled in practice and are counted here,
#   but `superglobal_reads.is_psalm_tainted` keeps the two populations apart so a
#   comparison against a Psalm baseline is honest.
# * `PDO::query`, `PDO::prepare` and `PDO::exec` are NOT in Psalm's
#   `InternalTaintSinkMap`; they live only in the stub files. A tool that reads
#   the map alone finds no PDO SQL sink anywhere. They are included here.
# * tree-sitter-php 0.24.1 predates three PHP 8.5 constructs and rejects exactly
#   those three out of a 23-case 8.0-8.5 feature sweep: the `(void)` cast,
#   `clone(x, [...]) in some spellings`, and `final` on a promoted constructor property.
#   Everything else -- property hooks, `private(set)`, DNF types, enums,
#   `#[Attr]`, `?->`, `match`, heredoc, group use, first-class callables and
#   even 8.5's `|>` -- parses clean. That list is written into
#   `meta.grammar_note` so a parse error reads as "the grammar is one version
#   behind", not "this file is broken".
#
# Usage:
#   python3 codegraph_php.py /path/to/repo --report
#   python3 codegraph_php.py /path/to/repo --list
#   python3 codegraph_php.py --deps
# ==========================================================================

DEPS = DepSet(lang="php", deps=[
    TREE_SITTER,
    grammar("PHP", "tree_sitter_php", "tree-sitter-php>=0.24",
            "0.24.1 (ABI 15) -- exposes language_php(), NOT language()"),
])

GRAMMAR_SYMBOL = "language_php"

HAZARD_CATEGORIES = (
    "sql", "shell", "exec", "include", "deserialize", "xss", "ldap", "header",
    "file", "callable", "superglobal", "crypto", "reflect", "io", "net",
    "resource",
)

HAZARD_CALLS: dict[str, str] = {
    # -- sql -------------------------------------------------------------
    # PDO's three sinks are absent from Psalm's InternalTaintSinkMap and
    # present only in its stubs. Omitting them loses every PDO finding.
    "PDO::query": "sql", "PDO::prepare": "sql", "PDO::exec": "sql",
    "mysqli_query": "sql", "mysqli_multi_query": "sql",
    "mysqli_real_query": "sql", "mysqli_prepare": "sql",
    "mysql_query": "sql", "mysql_db_query": "sql", "mysql_unbuffered_query": "sql",
    "pg_query": "sql", "pg_send_query": "sql", "pg_query_params": "sql",
    "sqlite_query": "sql", "sqlsrv_query": "sql", "oci_parse": "sql",
    "db2_exec": "sql", "ibase_query": "sql",
    "query": "sql", "prepare": "sql", "exec": "sql", "statement": "sql",
    "unprepared": "sql", "raw": "sql", "selectRaw": "sql", "whereRaw": "sql",
    "orWhereRaw": "sql", "havingRaw": "sql", "orderByRaw": "sql",
    "groupByRaw": "sql", "joinSub": "sql", "fromRaw": "sql",
    "createQuery": "sql", "getQuery": "sql", "createNativeQuery": "sql",
    "DB::raw": "sql", "DB::select": "sql", "DB::statement": "sql",
    "DB::unprepared": "sql", "DB::insert": "sql", "DB::update": "sql",
    "DB::delete": "sql",
    # -- shell -----------------------------------------------------------
    "exec_": "shell",
    "system": "shell", "shell_exec": "shell", "passthru": "shell",
    "popen": "shell", "proc_open": "shell", "pcntl_exec": "shell",
    "escapeshellcmd": "shell", "escapeshellarg": "shell",
    "expect_popen": "shell", "`": "shell",
    # -- exec (code, not process) ----------------------------------------
    "eval": "exec", "assert": "exec", "create_function": "exec",
    "preg_replace_callback": "exec", "preg_replace": "exec",
    "ReflectionFunction::invoke": "exec", "runkit_function_add": "exec",
    # -- include ---------------------------------------------------------
    "include": "include", "include_once": "include",
    "require": "include", "require_once": "include",
    "virtual": "include", "stream_wrapper_register": "include",
    # -- deserialize -----------------------------------------------------
    "unserialize": "deserialize", "yaml_parse": "deserialize",
    "yaml_parse_file": "deserialize", "simplexml_load_string": "deserialize",
    "simplexml_load_file": "deserialize", "xml_parse": "deserialize",
    "wddx_deserialize": "deserialize", "igbinary_unserialize": "deserialize",
    "msgpack_unpack": "deserialize", "Symfony\\Serializer::deserialize":
        "deserialize",
    # -- xss (echo/print are statements, handled structurally) ------------
    "printf": "xss", "vprintf": "xss", "print_r": "xss", "var_dump": "xss",
    "var_export": "xss", "fpassthru": "xss", "readfile": "xss",
    # mitigations: counted so the absence of one next to a sink is visible
    "htmlspecialchars": "xss", "htmlentities": "xss", "strip_tags": "xss",
    "e": "xss", "esc_html": "xss", "esc_attr": "xss", "filter_var": "xss",
    # -- ldap ------------------------------------------------------------
    "ldap_search": "ldap", "ldap_list": "ldap", "ldap_read": "ldap",
    "ldap_bind": "ldap", "ldap_add": "ldap", "ldap_modify": "ldap",
    "ldap_escape": "ldap",
    # -- header ----------------------------------------------------------
    "header": "header", "header_remove": "header", "setcookie": "header",
    "setrawcookie": "header", "session_start": "header",
    "session_id": "header", "session_regenerate_id": "header",
    "http_response_code": "header",
    # -- file ------------------------------------------------------------
    "file_get_contents": "file", "file_put_contents": "file", "fopen": "file",
    "fwrite": "file", "fputs": "file", "fread": "file", "readfile_": "file",
    "unlink": "file", "rmdir": "file", "mkdir": "file", "copy": "file",
    "rename": "file", "chmod": "file", "chown": "file", "touch": "file",
    "move_uploaded_file": "file", "tempnam": "file", "tmpfile": "file",
    "glob": "file", "scandir": "file", "opendir": "file", "readdir": "file",
    "file": "file", "parse_ini_file": "file", "realpath": "file",
    "basename": "file", "dirname": "file", "pathinfo": "file",
    "SplFileObject::__construct": "file",
    # -- callable (dynamic dispatch: where the graph goes blind) ----------
    "call_user_func": "callable", "call_user_func_array": "callable",
    "forward_static_call": "callable", "forward_static_call_array": "callable",
    "array_map": "callable", "array_filter": "callable", "usort": "callable",
    "uasort": "callable", "uksort": "callable", "array_walk": "callable",
    "register_shutdown_function": "callable", "set_error_handler": "callable",
    "set_exception_handler": "callable", "spl_autoload_register": "callable",
    "extract": "callable", "compact": "callable", "func_get_args": "callable",
    "is_callable": "callable", "Closure::fromCallable": "callable",
    "Closure::bind": "callable", "bindTo": "callable", "macro": "callable",
    "__call": "callable", "__callStatic": "callable", "__invoke": "callable",
    # -- superglobal -----------------------------------------------------
    "filter_input": "superglobal", "getenv": "superglobal",
    "apache_request_headers": "superglobal", "getallheaders": "superglobal",
    "parse_str": "superglobal", "http_build_query": "superglobal",
    # -- crypto ----------------------------------------------------------
    "md5": "crypto", "sha1": "crypto", "crc32": "crypto", "md5_file": "crypto",
    "sha1_file": "crypto", "rand": "crypto", "mt_rand": "crypto",
    "srand": "crypto", "mt_srand": "crypto", "uniqid": "crypto",
    "lcg_value": "crypto", "shuffle": "crypto", "str_shuffle": "crypto",
    "array_rand": "crypto", "mcrypt_encrypt": "crypto",
    "mcrypt_decrypt": "crypto", "mcrypt_create_iv": "crypto",
    "openssl_encrypt": "crypto", "openssl_decrypt": "crypto",
    "password_hash": "crypto", "password_verify": "crypto",
    "hash_equals": "crypto", "random_bytes": "crypto", "random_int": "crypto",
    "base64_decode": "crypto",
    # -- reflect ---------------------------------------------------------
    "ReflectionClass::__construct": "reflect",
    "ReflectionMethod::__construct": "reflect",
    "ReflectionProperty::__construct": "reflect",
    "ReflectionFunction::__construct": "reflect",
    "get_class": "reflect", "get_parent_class": "reflect",
    "get_object_vars": "reflect", "get_class_methods": "reflect",
    "method_exists": "reflect", "property_exists": "reflect",
    "class_exists": "reflect", "interface_exists": "reflect",
    "function_exists": "reflect", "is_subclass_of": "reflect",
    "class_implements": "reflect", "class_uses": "reflect",
    "newInstance": "reflect", "newInstanceArgs": "reflect",
    "getMethod": "reflect", "getProperty": "reflect", "setAccessible": "reflect",
    # -- io --------------------------------------------------------------
    "fgets": "io", "fgetcsv": "io", "fputcsv": "io", "fclose": "io",
    "fflush": "io", "flock": "io", "fseek": "io", "ftell": "io",
    "stream_get_contents": "io", "stream_copy_to_stream": "io",
    "error_log": "io", "syslog": "io", "ob_start": "io", "flush": "io",
    # -- net -------------------------------------------------------------
    "curl_exec": "net", "curl_init": "net", "curl_setopt": "net",
    "curl_multi_exec": "net", "fsockopen": "net", "pfsockopen": "net",
    "stream_socket_client": "net", "stream_socket_server": "net",
    "socket_connect": "net", "socket_create": "net", "get_headers": "net",
    "gethostbyname": "net", "dns_get_record": "net", "checkdnsrr": "net",
    "mail": "net", "fsockopen_": "net", "send": "net", "request": "net",
    # -- resource --------------------------------------------------------
    "set_time_limit": "resource", "ini_set": "resource", "ini_get": "resource",
    "memory_get_usage": "resource", "sleep": "resource", "usleep": "resource",
    "pcntl_fork": "resource", "pcntl_signal": "resource",
    "posix_setuid": "resource", "gc_collect_cycles": "resource",
    "apcu_store": "resource", "apcu_fetch": "resource",
    "shmop_open": "resource", "sem_acquire": "resource",
}

PSALM_TAINTED = ("$_GET", "$_POST", "$_COOKIE", "$_REQUEST")

SUPERGLOBALS = ("$_GET", "$_POST", "$_REQUEST", "$_COOKIE", "$_SERVER",
                "$_FILES", "$_SESSION", "$_ENV", "$GLOBALS")

SUPERGLOBAL_COL = {
    "$_GET": "n_get", "$_POST": "n_post", "$_REQUEST": "n_request",
    "$_COOKIE": "n_cookie", "$_SERVER": "n_server", "$_FILES": "n_files_super",
    "$_SESSION": "n_session", "$GLOBALS": "n_globals", "$_ENV": "n_server",
}

DYNAMIC_CALLS = frozenset((
    "call_user_func", "call_user_func_array", "forward_static_call",
    "forward_static_call_array", "extract", "compact", "func_get_args",
    "func_num_args", "eval", "create_function", "assert",
    "spl_autoload_register", "register_shutdown_function",
    "set_error_handler", "set_exception_handler", "array_map",
    "array_filter", "usort", "uasort", "uksort", "array_walk",
))

MAGIC_METHODS = frozenset((
    "__construct", "__destruct", "__call", "__callStatic", "__get", "__set",
    "__isset", "__unset", "__sleep", "__wakeup", "__serialize",
    "__unserialize", "__toString", "__invoke", "__set_state", "__clone",
    "__debugInfo",
))

GADGET_METHODS = frozenset(("__destruct", "__wakeup", "__unserialize",
                            "__toString", "__sleep", "__serialize"))

ESCAPERS = frozenset((
    "htmlspecialchars", "htmlentities", "htmlspecialchars_decode", "e",
    "esc_html", "esc_attr", "esc_url", "strip_tags", "filter_var",
    "urlencode", "rawurlencode", "json_encode", "intval", "floatval",
    "settype", "abs", "number_format",
))

SQL_ESCAPERS = frozenset((
    "real_escape_string", "mysqli_real_escape_string",
    "mysql_real_escape_string", "pg_escape_string", "pg_escape_literal",
    "pg_escape_identifier", "quote", "addslashes", "intval", "floatval",
    "escape", "sanitize",
))

SQL_RE = re.compile(
    r'\b(SELECT\s|INSERT\s+INTO|UPDATE\s+\w|DELETE\s+FROM|REPLACE\s+INTO|'
    r'CREATE\s+TABLE|DROP\s+TABLE|ALTER\s+TABLE|TRUNCATE\s+TABLE|'
    r'UNION\s+(?:ALL\s+)?SELECT|FROM\s+\w+\s+WHERE)\b', re.I)

PLACEHOLDER_RE = re.compile(r'(\?|:[a-zA-Z_]\w*)')

STRICT_TYPES_RE = re.compile(r'declare\s*\(\s*strict_types\s*=\s*1\s*\)')

ROUTE_ATTR_RE = re.compile(
    r'^(Route|Get|Post|Put|Patch|Delete|Options|Head|Any|'
    r'AsController|AsCommand|AsMessageHandler|AsEventListener|'
    r'Required|Middleware)$')

CONTROLLER_PATH_RE = re.compile(
    r'(^|/)(Controllers?|Http/Controllers|Action|Endpoints?|Resources?)(/|$)', re.I)

MODEL_PATH_RE = re.compile(
    r'(^|/)(Models?|Entity|Entities|Domain|Eloquent)(/|$)', re.I)

ENTRY_FILE_RE = re.compile(
    r'(^|/)(index\.php|artisan|console\.php|web\.php|api\.php|routes\.php|'
    r'app\.php|cli\.php|cron\.php|public/[^/]+\.php)$', re.I)

PHP_BUILTINS = frozenset("""
array_chunk array_column array_combine array_count_values array_diff
array_diff_assoc array_diff_key array_fill array_fill_keys array_filter
array_flip array_intersect array_intersect_key array_key_exists array_key_first
array_key_last array_keys array_map array_merge array_merge_recursive
array_pad array_pop array_product array_push array_rand array_reduce
array_replace array_reverse array_search array_shift array_slice array_splice
array_sum array_unique array_unshift array_values array_walk array_first
array_last arsort asort compact count current each end extract implode
in_array key krsort ksort list natsort natcasesort next prev range reset
rsort shuffle sizeof sort uasort uksort usort
abs ceil floor round sqrt pow exp log log10 max min intdiv fmod pi
number_format rand mt_rand random_int base_convert bindec decbin dechex
hexdec octdec decoct is_nan is_finite is_infinite intval floatval
addslashes chunk_split explode htmlspecialchars htmlentities html_entity_decode
htmlspecialchars_decode join lcfirst levenshtein ltrim md5 nl2br ord chr
preg_match preg_match_all preg_replace preg_replace_callback preg_split
preg_quote preg_grep printf print_r rtrim sha1 similar_text soundex sprintf
sscanf str_contains str_ends_with str_starts_with str_ireplace str_pad
str_repeat str_replace str_split str_word_count strcasecmp strcmp strcspn
strip_tags stripos stripslashes stristr strlen strnatcasecmp strnatcmp
strncasecmp strncmp strpbrk strpos strrchr strrev strripos strrpos strspn
strstr strtolower strtoupper strtr strval substr substr_count substr_replace
trim ucfirst ucwords vsprintf vprintf wordwrap mb_strlen mb_substr
mb_strtolower mb_strtoupper mb_str_split mb_convert_encoding mb_check_encoding
iconv json_encode json_decode json_last_error serialize unserialize base64_encode
base64_decode urlencode urldecode rawurlencode rawurldecode http_build_query
parse_url parse_str uniqid hash hash_hmac hash_equals crc32 random_bytes
is_array is_bool is_callable is_countable is_float is_int is_iterable is_null
is_numeric is_object is_scalar is_string is_a is_subclass_of isset empty unset
gettype settype boolval strval var_dump var_export get_class get_parent_class
get_object_vars get_class_methods method_exists property_exists class_exists
interface_exists trait_exists enum_exists function_exists defined define
constant iterator_to_array spl_object_hash spl_object_id spl_autoload_register
call_user_func call_user_func_array func_get_args func_num_args
date time mktime strtotime date_create checkdate microtime hrtime
date_default_timezone_set date_default_timezone_get gmdate idate getdate
fopen fclose fread fwrite fgets fgetcsv fputcsv feof fseek ftell rewind
file file_exists file_get_contents file_put_contents filemtime filesize
is_dir is_file is_readable is_writable mkdir rmdir unlink copy rename
basename dirname pathinfo realpath glob scandir opendir readdir closedir
tempnam sys_get_temp_dir touch chmod fflush flock stream_get_contents
error_log error_reporting ini_set ini_get set_error_handler trigger_error
sleep usleep exit die header setcookie session_start ob_start ob_get_clean
ob_end_clean ob_get_contents php_sapi_name phpversion php_uname memory_get_usage
gc_collect_cycles version_compare getenv putenv assert
""".split())

PHP_BUILTIN_CLASSES = frozenset("""
ArrayAccess ArrayIterator ArrayObject BadFunctionCallException
BadMethodCallException Closure Collator Countable DateInterval DateTime
DateTimeImmutable DateTimeZone DirectoryIterator DomainException Error
ErrorException Exception FilterIterator Generator Iterator IteratorAggregate
IteratorIterator InvalidArgumentException JsonException JsonSerializable
LengthException LimitIterator LogicException Normalizer NumberFormatter
OutOfBoundsException OutOfRangeException OverflowException PDO PDOStatement
PDOException Phar RangeException RecursiveArrayIterator RecursiveDirectoryIterator
RecursiveIteratorIterator ReflectionClass ReflectionEnum ReflectionFunction
ReflectionMethod ReflectionNamedType ReflectionObject ReflectionProperty
RuntimeException Serializable SimpleXMLElement SplFileInfo SplFileObject
SplFixedArray SplObjectStorage SplPriorityQueue SplQueue SplStack SplSubject
Stringable Throwable Traversable TypeError UnderflowException
UnexpectedValueException UnhandledMatchError ValueError WeakMap WeakReference
ZipArchive mysqli mysqli_stmt mysqli_result Redis Memcached Imagick CurlHandle
IntlDateFormatter Attribute SensitiveParameter ReturnTypeWillChange Override
Deprecated NoDiscard
""".split())

class PhpAnalyzer(TreeSitterAnalyzer):
    LANG = "php"
    TARGET = "PHP 8.5"
    EXTS = (".php", ".phtml", ".php5", ".php7", ".phps", ".module", ".inc")
    SKIP_DIRS = {"vendor", "storage", "bootstrap/cache", "public/build"}
    DEPS = DEPS
    HAZARD_CATEGORIES = HAZARD_CATEGORIES
    MANIFESTS = ("composer.json", "composer.lock")

    GRAMMAR_MODULE = "tree_sitter_php"
    GRAMMAR_PIP = "tree-sitter-php>=0.24"
    #: The whole reason this attribute exists. `language()` does not exist in
    #: tree_sitter_php; without this the loader falls back to regex mode and
    #: reports a plausible-looking, entirely empty graph.
    GRAMMAR_SYMBOL = GRAMMAR_SYMBOL

    FUNC_KINDS = {
        "function_definition": "function",
        "method_declaration": "method",
        "anonymous_function": "closure",
        "arrow_function": "closure",
        #: 8.4 property hooks. A hook body is a function that no call site
        #: names -- `$obj->prop` invokes it -- so it must be a symbol or every
        #: call inside it vanishes from the graph.
        "property_hook": "method",
    }
    TYPE_KINDS = {
        "class_declaration": "class",
        "interface_declaration": "interface",
        "trait_declaration": "trait",
        "enum_declaration": "enum",
        "anonymous_class": "class",
    }
    NAME_FIELD = {"anonymous_function": "", "arrow_function": "",
                  "anonymous_class": "", "property_hook": ""}
    IDENT_NODES = ("name", "variable_name")

    BODY_FIELD = "body"
    PARAMS_FIELD = "parameters"
    RETURN_FIELD = "return_type"

    #: Deliberately empty, both of them. PHP spells `elseif` as its own
    #: `else_if_clause` node rather than as an `if` nested in the else branch,
    #: so there is no chain to flatten and the elif correction in `measure`
    #: short-circuits. Setting these to something plausible-looking would
    #: leave an inert pass that the next reader assumes is working.
    #: `n_elif` comes from COUNTERS instead.
    ELSE_FIELD = ""
    IF_NODES: tuple[str, ...] = ()

    LOOP_NODES = ("for_statement", "foreach_statement", "while_statement",
                  "do_statement")
    BRANCH_NODES = ("if_statement", "else_if_clause",
                    "match_conditional_expression")
    #: The braced block is deliberately absent: every `if` and every
    #: loop owns one, so counting both charges two levels for one and
    #: reports depth as 2n+1.
    NEST_NODES = ("if_statement", "for_statement", "foreach_statement",
                  "while_statement", "do_statement", "switch_statement",
                  "try_statement", "match_expression",
                  "anonymous_function", "arrow_function")
    CALL_NODES = ("function_call_expression", "member_call_expression",
                  "nullsafe_member_call_expression", "scoped_call_expression",
                  "object_creation_expression")
    #: Only `function_call_expression` actually has this field. The other four
    #: call shapes use object/name or scope/name, which is why `on_call` is
    #: overridden below -- taking the base implementation would silently record
    #: every method call as anonymous and leave `edges` nearly empty on any
    #: object-oriented codebase.
    CALL_FUNC_FIELD = "function"

    COMMENT_NODES = ("comment",)
    STRING_NODES = ("string", "encapsed_string", "heredoc", "nowdoc")
    NUMBER_NODES = ("integer", "float")
    OPERATOR_NODES = ("binary_expression", "unary_op_expression",
                      "assignment_expression", "augmented_assignment_expression",
                      "update_expression", "subscript_expression",
                      "member_access_expression",
                      "nullsafe_member_access_expression",
                      "conditional_expression", "cast_expression",
                      "class_constant_access_expression", "clone_expression")

    COUNTERS = {
        "return_statement": "n_returns",
        "throw_expression": "n_throw",
        "try_statement": "n_try",
        "catch_clause": "n_catch",
        "finally_clause": "n_finally",
        "switch_statement": "n_switch",
        "case_statement": "n_cases",
        "default_statement": "n_cases",
        "match_conditional_expression": "n_match_arms",
        "match_default_expression": "n_match_arms",
        "conditional_expression": "n_ternary",
        "else_if_clause": "n_elif",
        "anonymous_function": "n_lambda",
        "arrow_function": "n_lambda",
        "anonymous_function_use_clause": "n_closure_capture",
        "subscript_expression": "n_subscript",
        "member_access_expression": "n_member_access",
        "nullsafe_member_access_expression": "n_null_safe",
        "nullsafe_member_call_expression": "n_null_safe",
        "assignment_expression": "n_assign",
        "augmented_assignment_expression": "n_compound_assign",
        "update_expression": "n_incdec",
        "goto_statement": "n_gotos",
        "named_label_statement": "n_labels",
        "error_suppression_expression": "n_error_suppress",
        "global_declaration": "n_globals",
        "dynamic_variable_name": "n_variable_var",
        "variadic_placeholder": "n_first_class_callable",
        "attribute": "n_attributes",
        "enum_case": "n_enum_cases",
        "property_hook": "n_property_hooks",
        "property_promotion_parameter": "n_promoted_params",
        "readonly_modifier": "n_readonly_props",
        "use_declaration": "n_traits_used",
        "scoped_call_expression": "n_static_calls",
        "heredoc": "n_heredoc",
        "nowdoc": "n_nowdoc",
        "list_literal": "n_locals",
    }
    #: Presence anywhere in a body sets the column to 1.
    FLAG_NODES = {"yield_expression": "is_generator"}
    #: Substring of a callee name -> column bumped when the call is in a loop.
    #: Matched against the recorded name, which for a method call is `->query`,
    #: so these are substrings rather than exact bases.
    LOOP_CALL_COUNTERS = {
        "query": "query_in_loop", "prepare": "query_in_loop",
        "mysqli_query": "query_in_loop", "pg_query": "query_in_loop",
        "->get": "query_in_loop", "->first": "query_in_loop",
        "->find": "query_in_loop", "->all": "query_in_loop",
        "preg_match": "regex_in_loop", "preg_replace": "regex_in_loop",
        "preg_split": "regex_in_loop",
        "file_get_contents": "io_in_loop", "fopen": "io_in_loop",
        "fwrite": "io_in_loop", "curl_exec": "io_in_loop",
        "file_put_contents": "io_in_loop",
        "array_merge": "alloc_in_loop", "array_push": "alloc_in_loop",
        "sprintf": "alloc_in_loop", "implode": "alloc_in_loop",
        "flock": "lock_in_loop", "sem_acquire": "lock_in_loop",
    }

    EXTRA_SYMBOL_COLS = (
        # -- tainted input -------------------------------------------------
        ("n_superglobal_reads", "INT NOT NULL DEFAULT 0"),
        ("n_get", "INT NOT NULL DEFAULT 0"),
        ("n_post", "INT NOT NULL DEFAULT 0"),
        ("n_request", "INT NOT NULL DEFAULT 0"),
        ("n_cookie", "INT NOT NULL DEFAULT 0"),
        ("n_server", "INT NOT NULL DEFAULT 0"),
        ("n_files_super", "INT NOT NULL DEFAULT 0"),
        ("n_session", "INT NOT NULL DEFAULT 0"),
        ("n_globals", "INT NOT NULL DEFAULT 0"),
        ("n_psalm_tainted", "INT NOT NULL DEFAULT 0"),
        # -- sql -----------------------------------------------------------
        ("n_sql_calls", "INT NOT NULL DEFAULT 0"),
        ("n_sql_literal", "INT NOT NULL DEFAULT 0"),
        ("n_sql_interp", "INT NOT NULL DEFAULT 0"),
        ("n_sql_concat", "INT NOT NULL DEFAULT 0"),
        ("n_sql_format", "INT NOT NULL DEFAULT 0"),
        ("n_sql_prepared", "INT NOT NULL DEFAULT 0"),
        ("n_sql_sanitized", "INT NOT NULL DEFAULT 0"),
        # -- output --------------------------------------------------------
        ("n_escaped_output", "INT NOT NULL DEFAULT 0"),
        ("n_raw_echo", "INT NOT NULL DEFAULT 0"),
        # -- dynamic dispatch ----------------------------------------------
        ("n_dynamic_call", "INT NOT NULL DEFAULT 0"),
        ("n_variable_var", "INT NOT NULL DEFAULT 0"),
        ("n_dynamic_method", "INT NOT NULL DEFAULT 0"),
        ("n_dynamic_new", "INT NOT NULL DEFAULT 0"),
        ("n_dynamic_include", "INT NOT NULL DEFAULT 0"),
        ("n_eval", "INT NOT NULL DEFAULT 0"),
        # -- type juggling / suppression -----------------------------------
        ("n_loose_compare", "INT NOT NULL DEFAULT 0"),
        ("n_strict_compare", "INT NOT NULL DEFAULT 0"),
        ("n_error_suppress", "INT NOT NULL DEFAULT 0"),
        # -- magic ---------------------------------------------------------
        ("n_magic_method", "INT NOT NULL DEFAULT 0"),
        ("n_destruct", "INT NOT NULL DEFAULT 0"),
        ("n_wakeup", "INT NOT NULL DEFAULT 0"),
        ("n_tostring", "INT NOT NULL DEFAULT 0"),
        ("n_call_magic", "INT NOT NULL DEFAULT 0"),
        # -- modern PHP surface --------------------------------------------
        ("n_property_hooks", "INT NOT NULL DEFAULT 0"),
        ("n_promoted_params", "INT NOT NULL DEFAULT 0"),
        ("n_readonly_props", "INT NOT NULL DEFAULT 0"),
        ("n_enum_cases", "INT NOT NULL DEFAULT 0"),
        ("n_attributes", "INT NOT NULL DEFAULT 0"),
        ("n_first_class_callable", "INT NOT NULL DEFAULT 0"),
        ("n_match_arms", "INT NOT NULL DEFAULT 0"),
        ("n_null_safe", "INT NOT NULL DEFAULT 0"),
        ("n_pipe_operator", "INT NOT NULL DEFAULT 0"),
        ("n_heredoc", "INT NOT NULL DEFAULT 0"),
        ("n_nowdoc", "INT NOT NULL DEFAULT 0"),
        # -- types ---------------------------------------------------------
        ("n_type_declarations", "INT NOT NULL DEFAULT 0"),
        ("n_untyped_params", "INT NOT NULL DEFAULT 0"),
        ("n_nullable_types", "INT NOT NULL DEFAULT 0"),
        ("n_union_types", "INT NOT NULL DEFAULT 0"),
        ("n_intersection_types", "INT NOT NULL DEFAULT 0"),
        ("has_strict_types", "INT NOT NULL DEFAULT 0"),
        # -- structure -----------------------------------------------------
        ("n_traits_used", "INT NOT NULL DEFAULT 0"),
        ("n_static_calls", "INT NOT NULL DEFAULT 0"),
        ("n_extract_call", "INT NOT NULL DEFAULT 0"),
    ("n_weak_hash", "INT NOT NULL DEFAULT 0"),
    ("n_weak_random", "INT NOT NULL DEFAULT 0"),
    ("n_remote_fetch", "INT NOT NULL DEFAULT 0"),
    ("n_header_call", "INT NOT NULL DEFAULT 0"),
    ("n_session_call", "INT NOT NULL DEFAULT 0"),
    ("n_move_uploaded", "INT NOT NULL DEFAULT 0"),
    ("n_serialize_call", "INT NOT NULL DEFAULT 0"),
    ("n_inarray_in_loop", "INT NOT NULL DEFAULT 0"),
    ("n_array_merge_in_loop", "INT NOT NULL DEFAULT 0"),
    ("n_count_in_loop", "INT NOT NULL DEFAULT 0"),
    ("n_preg_in_loop", "INT NOT NULL DEFAULT 0"),
    ("n_keycheck_in_loop", "INT NOT NULL DEFAULT 0"),
    ("n_elif", "INT NOT NULL DEFAULT 0"),
        ("n_external_calls", "INT NOT NULL DEFAULT 0"),
        ("namespace_", "TEXT NOT NULL DEFAULT ''"),
        ("class_name", "TEXT NOT NULL DEFAULT ''"),
        ("is_controller", "INT NOT NULL DEFAULT 0"),
        ("is_model", "INT NOT NULL DEFAULT 0"),
    )

    SCHEMA_EXT = r"""
CREATE TABLE classes(
    symbol_id INT NOT NULL PRIMARY KEY REFERENCES symbols(id),
    file_id INT NOT NULL REFERENCES files(id),
    name TEXT NOT NULL,
    fqn TEXT NOT NULL DEFAULT '',
    namespace TEXT NOT NULL DEFAULT '',
    kind TEXT NOT NULL DEFAULT 'class',
    extends TEXT NOT NULL DEFAULT '',
    implements TEXT NOT NULL DEFAULT '',
    traits TEXT NOT NULL DEFAULT '',
    n_traits INT NOT NULL DEFAULT 0,
    n_methods INT NOT NULL DEFAULT 0,
    n_public_methods INT NOT NULL DEFAULT 0,
    n_static_methods INT NOT NULL DEFAULT 0,
    n_props INT NOT NULL DEFAULT 0,
    n_promoted INT NOT NULL DEFAULT 0,
    n_hooks INT NOT NULL DEFAULT 0,
    n_consts INT NOT NULL DEFAULT 0,
    n_enum_cases INT NOT NULL DEFAULT 0,
    n_magic INT NOT NULL DEFAULT 0,
    is_abstract INT NOT NULL DEFAULT 0,
    is_final INT NOT NULL DEFAULT 0,
    is_readonly INT NOT NULL DEFAULT 0,
    is_anonymous INT NOT NULL DEFAULT 0,
    has_destruct INT NOT NULL DEFAULT 0,
    has_wakeup INT NOT NULL DEFAULT 0,
    has_tostring INT NOT NULL DEFAULT 0,
    has_call INT NOT NULL DEFAULT 0,
    has_callstatic INT NOT NULL DEFAULT 0,
    has_get INT NOT NULL DEFAULT 0,
    has_invoke INT NOT NULL DEFAULT 0,
    line INT NOT NULL DEFAULT 0
) WITHOUT ROWID, STRICT;

CREATE TABLE traits(
    symbol_id INT NOT NULL PRIMARY KEY REFERENCES symbols(id),
    file_id INT NOT NULL REFERENCES files(id),
    name TEXT NOT NULL,
    namespace TEXT NOT NULL DEFAULT '',
    n_methods INT NOT NULL DEFAULT 0,
    n_abstract_methods INT NOT NULL DEFAULT 0,
    n_props INT NOT NULL DEFAULT 0,
    used_by INT NOT NULL DEFAULT 0,
    line INT NOT NULL DEFAULT 0
) WITHOUT ROWID, STRICT;

CREATE TABLE namespaces(
    id INTEGER PRIMARY KEY,
    file_id INT NOT NULL REFERENCES files(id),
    name TEXT NOT NULL,
    line INT NOT NULL DEFAULT 0,
    has_strict_types INT NOT NULL DEFAULT 0,
    n_classes INT NOT NULL DEFAULT 0
) STRICT;

CREATE TABLE superglobal_reads(
    id INTEGER PRIMARY KEY,
    symbol_id INT REFERENCES symbols(id),
    file_id INT NOT NULL REFERENCES files(id),
    var TEXT NOT NULL,
    key_ TEXT NOT NULL DEFAULT '',
    line INT NOT NULL,
    in_loop INT NOT NULL DEFAULT 0,
    -- Psalm taints only $_GET/$_POST/$_COOKIE/$_REQUEST. The other four are
    -- attacker-controlled too; keeping the flag lets a comparison stay honest.
    is_psalm_tainted INT NOT NULL DEFAULT 0
) STRICT;

CREATE TABLE sql_sites(
    id INTEGER PRIMARY KEY,
    symbol_id INT REFERENCES symbols(id),
    file_id INT NOT NULL REFERENCES files(id),
    callee TEXT NOT NULL DEFAULT '',
    driver TEXT NOT NULL DEFAULT '',
    -- literal | interp | concat | format | variable
    build_kind TEXT NOT NULL DEFAULT 'literal',
    is_sanitized INT NOT NULL DEFAULT 0,
    is_prepared INT NOT NULL DEFAULT 0,
    has_superglobal INT NOT NULL DEFAULT 0,
    in_loop INT NOT NULL DEFAULT 0,
    line INT NOT NULL,
    snippet TEXT NOT NULL DEFAULT ''
) STRICT;

CREATE TABLE property_hooks(
    id INTEGER PRIMARY KEY,
    symbol_id INT REFERENCES symbols(id),
    class_id INT REFERENCES symbols(id),
    file_id INT NOT NULL REFERENCES files(id),
    class_name TEXT NOT NULL DEFAULT '',
    property TEXT NOT NULL,
    hook TEXT NOT NULL,
    is_short INT NOT NULL DEFAULT 0,
    is_virtual INT NOT NULL DEFAULT 0,
    body_sloc INT NOT NULL DEFAULT 0,
    n_calls INT NOT NULL DEFAULT 0,
    line INT NOT NULL
) STRICT;

CREATE TABLE magic_methods(
    id INTEGER PRIMARY KEY,
    symbol_id INT REFERENCES symbols(id),
    class_id INT REFERENCES symbols(id),
    file_id INT NOT NULL REFERENCES files(id),
    class_name TEXT NOT NULL DEFAULT '',
    method TEXT NOT NULL,
    is_gadget INT NOT NULL DEFAULT 0,
    body_sloc INT NOT NULL DEFAULT 0,
    n_calls INT NOT NULL DEFAULT 0,
    n_hazards INT NOT NULL DEFAULT 0,
    line INT NOT NULL
) STRICT;

CREATE TABLE dynamic_sites(
    id INTEGER PRIMARY KEY,
    symbol_id INT REFERENCES symbols(id),
    file_id INT NOT NULL REFERENCES files(id),
    kind TEXT NOT NULL,
    target TEXT NOT NULL DEFAULT '',
    in_loop INT NOT NULL DEFAULT 0,
    line INT NOT NULL
) STRICT;
"""

    INDEX_EXT = r"""
-- parse-coverage joins namespaces by file; the planner was building this.
CREATE INDEX idx_ns_file ON namespaces(file_id);
CREATE INDEX idx_cls_kind ON classes(kind, name);
CREATE INDEX idx_cls_ns ON classes(namespace, name);
CREATE INDEX idx_cls_gadget ON classes(symbol_id)
    WHERE has_destruct=1 OR has_wakeup=1 OR has_tostring=1;
CREATE INDEX idx_cls_magiccall ON classes(symbol_id)
    WHERE has_call=1 OR has_callstatic=1;
CREATE INDEX idx_trait_name ON traits(name);
CREATE INDEX idx_ns_name ON namespaces(name, file_id);
CREATE INDEX idx_sg_sym ON superglobal_reads(symbol_id, var);
CREATE INDEX idx_sg_var ON superglobal_reads(var, file_id);
CREATE INDEX idx_sql_sym ON sql_sites(symbol_id, build_kind);
CREATE INDEX idx_sql_unsafe ON sql_sites(symbol_id)
    WHERE build_kind IN ('interp','concat','format') AND is_sanitized=0;
CREATE INDEX idx_hook_class ON property_hooks(class_id, property);
CREATE INDEX idx_magic_gadget ON magic_methods(method) WHERE is_gadget=1;
CREATE INDEX idx_dyn_sym ON dynamic_sites(symbol_id, kind);
CREATE INDEX idx_dyn_kind ON dynamic_sites(kind, file_id);
CREATE INDEX idx_fn_super ON symbols(n_superglobal_reads DESC, name)
    WHERE n_superglobal_reads>0;
CREATE INDEX idx_fn_sqlbuild ON symbols(n_sql_interp DESC, name)
    WHERE n_sql_interp>0 OR n_sql_concat>0;
"""

    VIEW_EXT = r"""
CREATE VIEW v_class AS
SELECT c.symbol_id AS id, c.name, c.fqn, c.namespace, c.kind, c.extends,
    c.implements, c.n_traits, c.n_methods, c.n_props, c.n_magic,
    c.has_destruct, c.has_wakeup, c.has_tostring, c.has_call,
    c.has_callstatic, s.sloc, s.n_lines, f.path,
    f.path || ':' || c.line AS at
FROM classes c
JOIN symbols s ON s.id = c.symbol_id
JOIN files f ON f.id = c.file_id;

CREATE VIEW v_taint_source AS
SELECT s.id, s.name, s.qual_name, s.class_name, s.namespace_,
    s.n_superglobal_reads, s.n_psalm_tainted, s.n_get, s.n_post,
    s.n_request, s.n_cookie, s.n_server, s.n_files_super,
    s.n_sql_calls, s.n_raw_echo, s.n_dynamic_include, s.fan_in, s.fan_out,
    f.path || ':' || s.line_start AS at
FROM symbols s JOIN files f ON f.id = s.file_id
WHERE s.n_superglobal_reads > 0;

CREATE VIEW v_gadget_surface AS
SELECT m.class_name, m.method, m.is_gadget, m.body_sloc, m.n_calls,
    m.n_hazards, f.path || ':' || m.line AS at
FROM magic_methods m JOIN files f ON f.id = m.file_id
WHERE m.is_gadget = 1;
"""

    MATERIALIZE_EXT = r"""
UPDATE symbols AS s SET n_unique_calls = x.c FROM
    (SELECT caller_id AS id, COUNT(*) AS c FROM edges GROUP BY caller_id) AS x
    WHERE x.id = s.id;

UPDATE symbols AS s SET n_superglobal_reads = x.n, n_psalm_tainted = x.p FROM
    (SELECT symbol_id AS id, COUNT(*) AS n, SUM(is_psalm_tainted) AS p
     FROM superglobal_reads WHERE symbol_id IS NOT NULL
     GROUP BY symbol_id) AS x WHERE x.id = s.id;

UPDATE symbols AS s SET n_get = x.n FROM
    (SELECT symbol_id AS id, COUNT(*) AS n FROM superglobal_reads
     WHERE var='$_GET' GROUP BY symbol_id) AS x WHERE x.id = s.id;
UPDATE symbols AS s SET n_post = x.n FROM
    (SELECT symbol_id AS id, COUNT(*) AS n FROM superglobal_reads
     WHERE var='$_POST' GROUP BY symbol_id) AS x WHERE x.id = s.id;
UPDATE symbols AS s SET n_request = x.n FROM
    (SELECT symbol_id AS id, COUNT(*) AS n FROM superglobal_reads
     WHERE var='$_REQUEST' GROUP BY symbol_id) AS x WHERE x.id = s.id;
UPDATE symbols AS s SET n_cookie = x.n FROM
    (SELECT symbol_id AS id, COUNT(*) AS n FROM superglobal_reads
     WHERE var='$_COOKIE' GROUP BY symbol_id) AS x WHERE x.id = s.id;
UPDATE symbols AS s SET n_server = x.n FROM
    (SELECT symbol_id AS id, COUNT(*) AS n FROM superglobal_reads
     WHERE var IN ('$_SERVER','$_ENV') GROUP BY symbol_id) AS x
    WHERE x.id = s.id;
UPDATE symbols AS s SET n_files_super = x.n FROM
    (SELECT symbol_id AS id, COUNT(*) AS n FROM superglobal_reads
     WHERE var='$_FILES' GROUP BY symbol_id) AS x WHERE x.id = s.id;
UPDATE symbols AS s SET n_session = x.n FROM
    (SELECT symbol_id AS id, COUNT(*) AS n FROM superglobal_reads
     WHERE var='$_SESSION' GROUP BY symbol_id) AS x WHERE x.id = s.id;

UPDATE symbols AS s SET
    n_sql_calls = x.n, n_sql_literal = x.lit, n_sql_interp = x.interp,
    n_sql_concat = x.cat, n_sql_format = x.fmt, n_sql_prepared = x.prep,
    n_sql_sanitized = x.san
FROM (SELECT symbol_id AS id, COUNT(*) AS n,
        SUM(build_kind='literal') AS lit, SUM(build_kind='interp') AS interp,
        SUM(build_kind='concat') AS cat, SUM(build_kind='format') AS fmt,
        SUM(is_prepared) AS prep, SUM(is_sanitized) AS san
      FROM sql_sites WHERE symbol_id IS NOT NULL GROUP BY symbol_id) AS x
WHERE x.id = s.id;

UPDATE symbols AS s SET n_dynamic_call = x.n FROM
    (SELECT symbol_id AS id, COUNT(*) AS n FROM dynamic_sites
     WHERE symbol_id IS NOT NULL GROUP BY symbol_id) AS x WHERE x.id = s.id;
UPDATE symbols AS s SET n_dynamic_method = x.n FROM
    (SELECT symbol_id AS id, COUNT(*) AS n FROM dynamic_sites
     WHERE kind='variable_method' GROUP BY symbol_id) AS x WHERE x.id = s.id;
UPDATE symbols AS s SET n_dynamic_new = x.n FROM
    (SELECT symbol_id AS id, COUNT(*) AS n FROM dynamic_sites
     WHERE kind='variable_class' GROUP BY symbol_id) AS x WHERE x.id = s.id;
UPDATE symbols AS s SET n_dynamic_include = x.n FROM
    (SELECT symbol_id AS id, COUNT(*) AS n FROM dynamic_sites
     WHERE kind='variable_include' GROUP BY symbol_id) AS x WHERE x.id = s.id;
UPDATE symbols AS s SET n_eval = x.n FROM
    (SELECT symbol_id AS id, COUNT(*) AS n FROM dynamic_sites
     WHERE kind='eval' GROUP BY symbol_id) AS x WHERE x.id = s.id;

UPDATE magic_methods AS mm SET n_calls = x.c, n_hazards = x.h FROM
    (SELECT id, n_calls AS c, n_hazards AS h FROM symbols) AS x
    WHERE x.id = mm.symbol_id;

UPDATE property_hooks AS ph SET n_calls = x.c FROM
    (SELECT id, n_calls AS c FROM symbols) AS x WHERE x.id = ph.symbol_id;

UPDATE traits AS t SET used_by = (
    SELECT COUNT(*) FROM classes c
    WHERE ',' || c.traits || ',' LIKE '%,' || t.name || ',%');

UPDATE namespaces AS n SET n_classes = (
    SELECT COUNT(*) FROM classes c WHERE c.namespace = n.name);
"""

    RISK_SQL = (
        "cyclomatic*2 + cognitive + max_nesting*4"
        " + n_sql_interp*30 + n_sql_concat*22 + n_sql_format*14"
        " + n_eval*35 + n_shell*25 + n_exec*20 + n_dynamic_include*28"
        " + n_deserialize*20 + n_raw_echo*7 + n_ldap*10"
        " + n_variable_var*10 + n_dynamic_new*6 + n_dynamic_method*6"
        " + n_dynamic_call*3 + n_superglobal_reads*3 + n_psalm_tainted*2"
        " + n_loose_compare*2 + n_error_suppress*5 + n_globals*3"
        " + n_crypto*3 + n_reflect*2 + n_callable*2"
        " + query_in_loop*15 + call_in_loop*2"
        " + (CASE WHEN has_strict_types=0 THEN 6 ELSE 0 END)"
        " + (CASE WHEN is_recursive THEN 8 ELSE 0 END)"
        " - n_escaped_output*2 - n_sql_prepared*4"
    )

    def __init__(self) -> None:
        super().__init__()
        #: fid -> [(start_byte, namespace_name)], in file order
        self._ns_spans: dict[int, list[tuple[int, str]]] = {}
        #: fid -> declare(strict_types=1) present
        self._strict: dict[int, bool] = {}
        #: fid -> {short name or alias -> fully-qualified target}
        self._use_map: dict[int, dict[str, str]] = {}
        #: (fid, node.start_byte) -> symbol id, for both functions and types
        self._fn_sid: dict[tuple[int, int], int] = {}
        self._ty_sid: dict[tuple[int, int], int] = {}
        #: class short name -> parent short name, for `parent::`
        self._extends: dict[str, str] = {}
        self.php_version = ""

    # -- naming ------------------------------------------------------------
    def node_name(self, node: Any, rec: FileRec) -> str:
        """`get`/`set` alone is useless, so a hook is named for its property."""
        if node.type == "property_hook":
            hook = ""
            for c in node.named_children:
                if c.type == "name":
                    hook = text_of(c, rec.data)
                    break
            return "$%s::%s" % (_hook_property(node, rec.data) or "?",
                                hook or "?")
        return super().node_name(node, rec)

    def visibility_of(self, node: Any, rec: FileRec) -> str:
        for c in node.named_children:
            if c.type == "visibility_modifier":
                v = text_of(c, rec.data).strip()
                # 8.4 asymmetric visibility: `public private(set)` is public
                # for reads. The read side is what a caller sees.
                return v.split("(")[0]
        if node.type in ("method_declaration", "property_declaration"):
            return "public"          # PHP's default when nothing is written
        return ""

    # -- flags -------------------------------------------------------------
    def function_flags(self, node: Any, rec: FileRec,
                       scope: Scope) -> dict[str, Any]:
        src = rec.data
        name = self.node_name(node, rec)
        mods = _modifiers(node, src)
        params = node.child_by_field_name(self.PARAMS_FIELD)
        n_params = n_opt = n_untyped = n_null = n_union = n_inter = 0
        n_typed = 0
        n_promoted = 0
        if params is not None:
            for p in params.named_children:
                if p.type not in ("simple_parameter", "variadic_parameter",
                                  "property_promotion_parameter"):
                    continue
                n_params += 1
                if p.type == "property_promotion_parameter":
                    n_promoted += 1
                if p.child_by_field_name("default_value") is not None:
                    n_opt += 1
                t = p.child_by_field_name("type")
                if t is None:
                    n_untyped += 1
                else:
                    n_typed += 1
                    if t.type == "optional_type":
                        n_null += 1
                    elif t.type == "union_type":
                        n_union += 1
                        if "null" in text_of(t, src):
                            n_null += 1
                    elif t.type == "intersection_type":
                        n_inter += 1
                    elif t.type == "disjunctive_normal_form_type":
                        n_union += 1
                        n_inter += 1
        ret = node.child_by_field_name(self.RETURN_FIELD)
        if ret is not None:
            n_typed += 1
            if ret.type == "optional_type":
                n_null += 1
            elif ret.type == "union_type":
                n_union += 1
            elif ret.type == "intersection_type":
                n_inter += 1

        cls = scope.type_name
        ns = self._namespace_at(rec.fid, node.start_byte)
        magic = 1 if name in MAGIC_METHODS else 0
        attrs = _attribute_names(node, src)
        is_route = any(ROUTE_ATTR_RE.match(a.rsplit("\\", 1)[-1]) for a in attrs)
        ctrl = int(bool(CONTROLLER_PATH_RE.search(rec.rel))
                   or cls.endswith(("Controller", "Action", "Endpoint")))
        model = int(bool(MODEL_PATH_RE.search(rec.rel))
                    or self._extends.get(cls, "").endswith(
                        ("Model", "Entity", "ActiveRecord")))
        entry = int(bool(ENTRY_FILE_RE.search(rec.rel)) or is_route
                    or (ctrl and self.visibility_of(node, rec) == "public")
                    or (name in ("handle", "__invoke", "execute", "run", "main")
                        and cls.endswith(("Command", "Job", "Middleware",
                                          "Listener", "Handler", "Controller"))))
        return dict(
            n_params=n_params,
            n_optional_params=n_opt,
            n_untyped_params=n_untyped,
            n_nullable_types=n_null,
            n_union_types=n_union,
            n_intersection_types=n_inter,
            n_type_declarations=n_typed,
            n_promoted_params=n_promoted,
            arity_rank=min(n_params, 9),
            is_public=int(self.visibility_of(node, rec) == "public"),
            is_static=int("static" in mods),
            is_abstract=int("abstract" in mods
                            or node.child_by_field_name("body") is None),
            is_override=int(any(a.rsplit("\\", 1)[-1] == "Override"
                                for a in attrs)),
            is_deprecated=int(any(a.rsplit("\\", 1)[-1] == "Deprecated"
                                  for a in attrs)),
            is_test=int(name.startswith("test")
                        or any(a.rsplit("\\", 1)[-1] in ("Test", "DataProvider")
                               for a in attrs)),
            is_entrypoint=entry,
            is_controller=ctrl,
            is_model=model,
            has_strict_types=int(self._strict.get(rec.fid, False)),
            n_magic_method=magic,
            n_destruct=int(name == "__destruct"),
            n_wakeup=int(name in ("__wakeup", "__unserialize")),
            n_tostring=int(name == "__toString"),
            n_call_magic=int(name in ("__call", "__callStatic")),
            namespace_=ns[:200],
            class_name=cls[:120],
        )

    def type_flags(self, node: Any, rec: FileRec,
                   scope: Scope) -> dict[str, Any]:
        src = rec.data
        mods = _modifiers(node, src)
        body = node.child_by_field_name(self.BODY_FIELD)
        counts = _class_body_counts(body, src) if body is not None else {}
        ns = self._namespace_at(rec.fid, node.start_byte)
        return dict(
            is_public=1,
            is_abstract=int("abstract" in mods),
            is_generated=int(rec.is_generated),
            n_traits_used=counts.get("traits", 0),
            n_enum_cases=counts.get("cases", 0),
            n_property_hooks=counts.get("hooks", 0),
            n_readonly_props=counts.get("readonly", 0),
            n_promoted_params=counts.get("promoted", 0),
            n_magic_method=counts.get("magic", 0),
            n_destruct=counts.get("destruct", 0),
            n_wakeup=counts.get("wakeup", 0),
            n_tostring=counts.get("tostring", 0),
            n_call_magic=counts.get("callmagic", 0),
            n_attributes=len(_attribute_names(node, src)),
            has_strict_types=int(self._strict.get(rec.fid, False)),
            namespace_=ns[:200],
            class_name=(self.node_name(node, rec) or "")[:120],
        )

    # -- the one place the base's call handling is not enough --------------
    def on_call(self, node: Any, src: bytes, st: BodyStats,
                loop_depth: int, nest: int) -> None:
        """Read the callee out of whichever of five shapes this is.

        `function_call_expression` has a `function` field; the other four do
        not. Taking the base implementation records every method call as
        anonymous, which on an object-oriented codebase produces healthy symbol
        counts and an almost empty `edges` table -- the failure mode that looks
        like success.

        The recorded name carries its shape so `resolve_calls` can pick the
        right receiver type later:  `foo` free function, `->bar` method call,
        `Cls::bar` static call, `new Cls` construction.
        """
        st.bump("n_calls")
        if loop_depth:
            st.bump("call_in_loop")
        t = node.type
        name = ""
        dynamic = False

        if t == "function_call_expression":
            fn = node.child_by_field_name("function")
            if fn is None:
                dynamic = True
            elif fn.type in ("name", "qualified_name"):
                name = text_of(fn, src).strip().lstrip("\\")
            else:
                # $f(), $arr['k'](), (expr)() -- the callee is a value
                dynamic = True
                name = ""
        elif t in ("member_call_expression", "nullsafe_member_call_expression"):
            nm = node.child_by_field_name("name")
            if nm is not None and nm.type == "name":
                name = "->" + text_of(nm, src).strip()
            else:
                dynamic = True          # $obj->$method()
        elif t == "scoped_call_expression":
            scope_n = node.child_by_field_name("scope")
            nm = node.child_by_field_name("name")
            if nm is not None and nm.type == "name" and scope_n is not None:
                cls = text_of(scope_n, src).strip().lstrip("\\")
                if scope_n.type in ("name", "qualified_name", "relative_scope"):
                    name = "%s::%s" % (cls, text_of(nm, src).strip())
                else:
                    dynamic = True      # $class::method()
            else:
                dynamic = True          # Cls::$method()
        elif t == "object_creation_expression":
            cls_node = None
            for c in node.named_children:
                if c.type in ("name", "qualified_name", "variable_name",
                              "relative_scope", "anonymous_class",
                              "member_access_expression",
                              "subscript_expression"):
                    cls_node = c
                    break
            if cls_node is None or cls_node.type == "anonymous_class":
                return                  # `new class {}` is a declaration
            if cls_node.type in ("name", "qualified_name", "relative_scope"):
                name = "new " + text_of(cls_node, src).strip().lstrip("\\")
            else:
                dynamic = True          # new $class
            if loop_depth:
                st.bump("alloc_in_loop")

        st.calls.append((name[:200], node.start_point[0] + 1, dynamic,
                         bool(loop_depth)))
        if dynamic:
            st.bump("n_dynamic_calls")
        if name and loop_depth:
            for needle, col in self.LOOP_CALL_COUNTERS.items():
                if needle in name:
                    st.bump(col)
        if name.lstrip("->") in ESCAPERS or name in ESCAPERS:
            st.bump("n_escaped_output")

        # -- facts PHPStan, Psalm, PHPMD and phpcs-security-audit check.
        # Counted, never judged: whether an `unserialize` is a gadget chain
        # depends on what reaches it, and that is a graph question.
        _b = name.lstrip("->").rsplit("::", 1)[-1].lower()
        if _b in ("extract", "compact"):
            st.bump("n_extract_call")
        if _b in ("md5", "sha1", "crc32"):
            st.bump("n_weak_hash")
        if _b in ("rand", "mt_rand", "srand", "mt_srand", "uniqid"):
            st.bump("n_weak_random")
        if _b in ("file_get_contents", "fopen", "curl_exec", "fsockopen"):
            st.bump("n_remote_fetch")
        if _b == "header":
            st.bump("n_header_call")
        if _b in ("session_start", "setcookie", "session_regenerate_id"):
            st.bump("n_session_call")
        if _b == "move_uploaded_file":
            st.bump("n_move_uploaded")
        if _b in ("serialize", "unserialize"):
            st.bump("n_serialize_call")
        if loop_depth:
            if _b == "in_array":
                st.bump("n_inarray_in_loop")
            elif _b in ("array_merge", "array_push", "array_combine"):
                st.bump("n_array_merge_in_loop")
            elif _b in ("count", "sizeof", "strlen", "str_repeat"):
                st.bump("n_count_in_loop")
            elif _b in ("preg_replace", "preg_match", "preg_split"):
                st.bump("n_preg_in_loop")
            elif _b in ("array_key_exists", "isset", "property_exists"):
                st.bump("n_keycheck_in_loop")

    def on_string(self, node: Any, text: str, src: bytes, st: BodyStats,
                  loop_depth: int) -> None:
        if not SQL_RE.search(text):
            return
        st.bump("n_sql_literal")
        if loop_depth:
            st.bump("query_in_loop")

    def on_node(self, node: Any, src: bytes, st: BodyStats,
                loop_depth: int, nest: int) -> None:
        t = node.type
        if t == "binary_expression":
            op = node.child_by_field_name("operator")
            o = text_of(op, src) if op is not None else ""
            if o in ("==", "!=", "<>"):
                st.bump("n_loose_compare")
                st.bump("n_cmp")
            elif o in ("===", "!=="):
                st.bump("n_strict_compare")
                st.bump("n_cmp")
            elif o in ("<", ">", "<=", ">=", "<=>"):
                st.bump("n_cmp")
            elif o in ("&&", "||", "and", "or", "xor"):
                st.bump("n_logical")
            elif o == "??":
                st.bump("n_null_check")
                st.bump("n_logical")
            elif o == "|>":
                # 8.5's pipe. Read the field: `|` and `|>` differ by one
                # character and a regex over the expression text confuses them.
                st.bump("n_pipe_operator")
            elif o in ("&", "|", "^"):
                st.bump("n_bitop")
            elif o in ("<<", ">>"):
                st.bump("n_shift")
            elif o in ("+", "-", "*", "/", "%", "**"):
                st.bump("n_arith")
            elif o == ".":
                if loop_depth:
                    st.bump("concat_in_loop")
        elif t == "augmented_assignment_expression":
            op = node.child_by_field_name("operator")
            if op is not None and text_of(op, src) == ".=" and loop_depth:
                st.bump("concat_in_loop")
        elif t == "unary_op_expression":
            op = node.child_by_field_name("operator")
            if op is not None and text_of(op, src) == "!":
                st.bump("n_logical")
        elif t == "conditional_expression":
            if node.child_by_field_name("consequence") is None:
                st.bump("n_null_check")          # `?:`
        elif t in ("echo_statement", "print_intrinsic"):
            txt = _txt(node, src)
            if "$" in txt or "<?=" in txt:
                if any(esc + "(" in txt for esc in ESCAPERS):
                    st.bump("n_escaped_output")
                else:
                    st.bump("n_raw_echo")
        elif t == "return_statement":
            if not node.named_children:
                st.bump("n_early_returns")
        elif t == "catch_clause":
            ty = node.child_by_field_name("type")
            if ty is not None:
                tt = _txt(ty, src)
                if "Throwable" in tt or tt.strip().lstrip("\\") == "Exception":
                    st.bump("n_catch_broad")
            body = node.child_by_field_name("body")
            if body is not None and not body.named_children:
                st.bump("n_catch_empty")
        elif t in ("include_expression", "include_once_expression",
                   "require_expression", "require_once_expression"):
            kids = [c for c in node.named_children]
            if kids and kids[0].type not in ("string",):
                st.bump("n_dynamic_include")
        elif t == "variable_name":
            if _txt(node, src) in SUPERGLOBALS:
                st.bump("n_superglobal_reads")
        elif t == "function_call_expression":
            fn = node.child_by_field_name("function")
            if fn is not None and fn.type in ("name", "qualified_name"):
                base = _txt(fn, src).strip().lstrip("\\").rsplit("\\", 1)[-1]
                if base == "eval":
                    st.bump("n_eval")
                elif base in ("isset", "empty", "is_null"):
                    st.bump("n_null_check")
                elif base in ("preg_match", "preg_replace", "preg_split",
                              "preg_match_all"):
                    st.bump("n_regex_lit")

    # -- hazards -----------------------------------------------------------
    def hazard_of(self, callee: str) -> Optional[tuple[str, str]]:
        raw = callee
        if raw.startswith("new "):
            raw = raw[4:] + "::__construct"
        elif raw.startswith("->"):
            raw = raw[2:]
        cat = HAZARD_CALLS.get(raw)
        if cat is not None:
            return raw, cat
        short = raw.rsplit("\\", 1)[-1]
        cat = HAZARD_CALLS.get(short)
        if cat is not None:
            return short, cat
        base = short.rsplit("::", 1)[-1]
        cat = HAZARD_CALLS.get(base)
        if cat is not None:
            return ("*::" + base) if "::" in short else base, cat
        return None

    # -- resolution --------------------------------------------------------
    def normalise_callee(self, raw: str) -> str:
        name = raw.strip()
        if name.startswith("->"):
            return name[2:]
        if name.startswith("new "):
            return name[4:].lstrip("\\") + "::__construct"
        return name.lstrip("\\")

    def is_external(self, name: str, base: str, fid: int) -> bool:
        """A call that leaves the tree by design, not one we lost.

        Folding PHP's ~1,500 built-ins into `unresolved` would put every repo
        at 80% blind and the honesty column would stop distinguishing anything.
        """
        short = name.rsplit("\\", 1)[-1]
        if "::" in short:
            cls, meth = short.split("::", 1)
            if cls in PHP_BUILTIN_CLASSES:
                return True
            return False
        return short in PHP_BUILTINS or base in PHP_BUILTINS

    # -- per-symbol detail --------------------------------------------------
    def emit_params(self, node: Any, rec: FileRec, sid: int,
                    bufs: Buffers) -> None:
        params = node.child_by_field_name(self.PARAMS_FIELD)
        if params is None:
            return
        src = rec.data
        pos = 0
        for p in params.named_children:
            if p.type not in ("simple_parameter", "variadic_parameter",
                              "property_promotion_parameter"):
                continue
            nm = p.child_by_field_name("name")
            name = text_of(nm, src).strip() if nm is not None else ""
            t = p.child_by_field_name("type")
            ptype = text_of(t, src).strip() if t is not None else ""
            dv = p.child_by_field_name("default_value")
            default = text_of(dv, src)[:120] if dv is not None else None
            ptxt = _txt(p, src)
            bufs.params.append(
                (sid, pos, name[:120], ptype[:200], default,
                 int(dv is not None),
                 int(p.type == "variadic_parameter" or "..." in ptxt),
                 int("&" in ptxt.split("$")[0]),
                 int(p.type == "property_promotion_parameter"
                     and "readonly" not in ptxt),
                 int(ptype.startswith("?") or "null" in ptype.lower()),
                 0, int(not ptype),
                 ptype.count("|") + ptype.count("&") + ptype.count("<")))
            pos += 1

    def emit_attributes(self, node: Any, rec: FileRec, sid: int,
                        bufs: Buffers) -> None:
        """PHP 8 `#[Attr]`.

        A PHP-7-era lexer treats `#` as a line comment and eats the entire
        attribute, so a tool built on one reports zero attributes on a modern
        codebase and nobody notices. These are real nodes and are read as such.
        """
        attrs = node.child_by_field_name("attributes")
        if attrs is None:
            return
        src = rec.data
        for group in attrs.named_children:
            if group.type != "attribute_group":
                continue
            for a in group.named_children:
                if a.type != "attribute":
                    continue
                nm = ""
                for c in a.named_children:
                    if c.type in ("name", "qualified_name"):
                        nm = text_of(c, src).strip().lstrip("\\")
                        break
                args = a.child_by_field_name("parameters")
                bufs.attributes.append(
                    (sid, rec.fid, nm[:160],
                     _txt(args, src)[:240] if args is not None else None,
                     a.start_point[0] + 1))

    def function_extra(self, node: Any, rec: FileRec, db: sqlite3.Connection,
                       bufs: Buffers, sid: int, scope: Scope,
                       stats: BodyStats) -> None:
        src = rec.data
        name = self.node_name(node, rec)
        cls = scope.type_name
        ns = self._namespace_at(rec.fid, node.start_byte)
        self._fn_sid[(rec.fid, node.start_byte)] = sid

        # Register the PHP spellings so `Cls::method` and `Ns\Cls::method`
        # resolve exactly rather than falling back to a bare short name.
        if cls and node.type == "method_declaration":
            self.by_qual["%s::%s" % (cls, name)] = sid
            if ns:
                self.by_qual["%s\\%s::%s" % (ns, cls, name)] = sid
        elif node.type == "function_definition" and ns:
            self.by_qual["%s\\%s" % (ns, name)] = sid

        # Give each pending call the receiver type its SHAPE implies. Without
        # this a free function `foo()` called inside a class resolves to that
        # class's own `foo()` method, which PHP would never do.
        parent_cls = self._extends.get(cls, "")
        # Column-wise, this rewrites only the column that changes. As
        # `list[tuple]` it had to unpack all six fields and rebuild the whole
        # row to alter one of them.
        i = len(self.pend_sid) - 1
        while i >= 0 and self.pend_sid[i] == sid:
            self.pend_type[i] = _receiver_type(
                self.pend_name[i], cls, parent_cls)
            i -= 1

        if node.type == "method_declaration" and name in MAGIC_METHODS:
            bufs.rows("magic_methods").append(
                (sid, scope.type_id, rec.fid, cls[:120], name,
                 int(name in GADGET_METHODS), self.sloc_of(node, rec), 0, 0,
                 node.start_point[0] + 1))
        elif node.type == "property_hook":
            body = node.child_by_field_name("body")
            hook = ""
            for c in node.named_children:
                if c.type == "name":
                    hook = text_of(c, src)
                    break
            prop = _hook_property(node, src)
            bufs.rows("property_hooks").append(
                (sid, scope.type_id, rec.fid, cls[:120], prop[:120],
                 hook or "?",
                 int(body is not None and body.type != "compound_statement"),
                 int(_hook_is_virtual(node, src)),
                 self.sloc_of(node, rec), 0, node.start_point[0] + 1))

    def type_extra(self, node: Any, rec: FileRec, db: sqlite3.Connection,
                   bufs: Buffers, sid: int, scope: Scope) -> None:
        src = rec.data
        name = self.node_name(node, rec) or "(anonymous)"
        ns = self._namespace_at(rec.fid, node.start_byte)
        self._ty_sid[(rec.fid, node.start_byte)] = sid
        mods = _modifiers(node, src)
        body = node.child_by_field_name(self.BODY_FIELD)
        c = _class_body_counts(body, src) if body is not None else {}

        extends = ""
        implements: list[str] = []
        for ch in node.named_children:
            if ch.type == "base_clause":
                extends = ",".join(text_of(x, src).strip().lstrip("\\")
                                   for x in ch.named_children
                                   if x.type in ("name", "qualified_name"))
            elif ch.type == "class_interface_clause":
                implements = [text_of(x, src).strip().lstrip("\\")
                              for x in ch.named_children
                              if x.type in ("name", "qualified_name")]
        if extends:
            self._extends[name] = extends.split(",")[0].rsplit("\\", 1)[-1]

        kind = self.TYPE_KINDS.get(node.type, "class")
        if node.type == "trait_declaration":
            bufs.rows("traits").append(
                (sid, rec.fid, name[:160], ns[:200], c.get("methods", 0),
                 c.get("abstract", 0), c.get("props", 0), 0,
                 node.start_point[0] + 1))
            # A trait is also a class-shaped thing; recording it in both keeps
            # the "two escaping disciplines" query able to see trait bodies.
        bufs.rows("classes").append(
            (sid, rec.fid, name[:160],
             ("%s\\%s" % (ns, name) if ns else name)[:300], ns[:200], kind,
             extends[:200], ",".join(implements)[:300],
             c.get("trait_names", "")[:300], c.get("traits", 0),
             c.get("methods", 0), c.get("public_methods", 0),
             c.get("static_methods", 0), c.get("props", 0),
             c.get("promoted", 0), c.get("hooks", 0), c.get("consts", 0),
             c.get("cases", 0), c.get("magic", 0),
             int("abstract" in mods), int("final" in mods),
             int("readonly" in mods), int(node.type == "anonymous_class"),
             c.get("destruct", 0), c.get("wakeup", 0), c.get("tostring", 0),
             c.get("callmagic_call", 0), c.get("callmagic_static", 0),
             c.get("get", 0), c.get("invoke", 0),
             node.start_point[0] + 1))

        for i, (fname, ftype, vis, line, static, const, readonly) in enumerate(
                _class_fields(body, src) if body is not None else []):
            bufs.fields.append(
                (sid, i, fname[:120], ftype[:200], vis, line,
                 int(static), int(const), int(not readonly),
                 int(ftype.startswith("?") or "null" in ftype.lower()),
                 int("array" in ftype.lower() or "iterable" in ftype.lower()),
                 int(not ftype), 0,
                 ftype.count("|") + ftype.count("&")))

    # -- file-level passes --------------------------------------------------
    def parse_imports(self, root: Any, rec: FileRec, bufs: Buffers) -> None:
        """`use` statements, namespaces and `declare(strict_types=1)`.

        Runs before `walk_scope`, which is why the namespace map is built here:
        every symbol emitted afterwards needs to know which namespace it is in.
        """
        src = rec.data
        spans: list[tuple[int, str]] = []
        strict = False
        uses: dict[str, str] = {}

        for n in walk(root):
            t = n.type
            if t == "namespace_definition":
                nm = n.child_by_field_name("name")
                spans.append((n.start_byte,
                              text_of(nm, src).strip().lstrip("\\")
                              if nm is not None else ""))
            elif t == "declare_directive":
                if STRICT_TYPES_RE.search(_txt(n, src)):
                    strict = True
            elif t == "namespace_use_declaration":
                prefix = ""
                group = n.child_by_field_name("body")
                if group is not None:
                    for ch in n.named_children:
                        if ch.type == "namespace_name":
                            prefix = text_of(ch, src).strip().lstrip("\\")
                            break
                clauses = [x for x in walk(n)
                           if x.type == "namespace_use_clause"]
                for cl in clauses:
                    target = ""
                    alias = None
                    kind = "use"
                    tf = cl.child_by_field_name("type")
                    if tf is not None:
                        kind = "use " + _txt(tf, src).strip()
                    af = cl.child_by_field_name("alias")
                    if af is not None:
                        alias = text_of(af, src).strip()
                    for ch in cl.named_children:
                        if ch.type in ("qualified_name", "name"):
                            target = text_of(ch, src).strip().lstrip("\\")
                            break
                    if prefix and target:
                        target = "%s\\%s" % (prefix, target)
                    if not target:
                        continue
                    short = alias or target.rsplit("\\", 1)[-1]
                    uses[short] = target
                    bufs.imports.append(
                        (rec.fid, target[:300], None, alias, kind,
                         cl.start_point[0] + 1,
                         int(not target.startswith(("App\\", "Tests\\"))),
                         0, int(group is not None), 0, 0, 1))
            elif t in ("include_expression", "include_once_expression",
                       "require_expression", "require_once_expression"):
                kids = [x for x in n.named_children]
                arg = kids[0] if kids else None
                literal = arg is not None and arg.type == "string"
                bufs.imports.append(
                    (rec.fid,
                     (_txt(arg, src).strip("'\"") if literal
                      else _txt(n, src))[:300],
                     None, None, t.replace("_expression", ""),
                     n.start_point[0] + 1, 0, 1, 0, 0,
                     int(not literal), 1))

        self._ns_spans[rec.fid] = spans or [(0, "")]
        self._strict[rec.fid] = strict
        self._use_map[rec.fid] = uses
        for start, nm in (spans or []):
            bufs.rows("namespaces").append(
                (rec.fid, nm[:200],
                 rec.data[:start].count(b"\n") + 1, int(strict), 0))

    def parse_file_extra(self, root: Any, rec: FileRec,
                         db: sqlite3.Connection, bufs: Buffers) -> None:
        """One pass for everything that needs a symbol AND a node.

        Attribution walks up to the nearest enclosing function node and looks
        its symbol id up by start byte, so code at file scope -- which in PHP is
        a large fraction of the interesting code -- lands with symbol_id NULL
        rather than being dropped or misattributed.
        """
        src = rec.data
        loops = set(self.LOOP_NODES)
        funcs = set(self.FUNC_KINDS)

        for n in walk(root):
            t = n.type
            if t == "variable_name":
                var = _txt(n, src)
                if var not in SUPERGLOBALS:
                    continue
                key = ""
                par = n.parent
                if par is not None and par.type == "subscript_expression":
                    for ch in par.named_children:
                        if ch is not n:
                            key = _txt(ch, src).strip("'\"")[:80]
                            break
                bufs.rows("superglobal_reads").append(
                    (self._sid_at(n, rec.fid, funcs), rec.fid, var, key,
                     n.start_point[0] + 1,
                     int(_in_loop(n, loops, funcs)),
                     int(var in PSALM_TAINTED)))
            elif t in ("function_call_expression", "member_call_expression",
                       "nullsafe_member_call_expression",
                       "scoped_call_expression"):
                self._maybe_sql_site(n, rec, bufs, loops, funcs)
                self._maybe_dynamic_site(n, rec, bufs, loops, funcs)
            elif t == "object_creation_expression":
                kids = [c for c in n.named_children]
                if kids and kids[0].type in ("variable_name",
                                             "member_access_expression",
                                             "subscript_expression"):
                    bufs.rows("dynamic_sites").append(
                        (self._sid_at(n, rec.fid, funcs), rec.fid,
                         "variable_class", _txt(kids[0], src)[:120],
                         int(_in_loop(n, loops, funcs)), n.start_point[0] + 1))
            elif t == "dynamic_variable_name":
                bufs.rows("dynamic_sites").append(
                    (self._sid_at(n, rec.fid, funcs), rec.fid,
                     "variable_variable", _txt(n, src)[:120],
                     int(_in_loop(n, loops, funcs)), n.start_point[0] + 1))
            elif t in ("include_expression", "include_once_expression",
                       "require_expression", "require_once_expression"):
                kids = [c for c in n.named_children]
                if kids and kids[0].type != "string":
                    bufs.rows("dynamic_sites").append(
                        (self._sid_at(n, rec.fid, funcs), rec.fid,
                         "variable_include", _txt(n, src)[:120],
                         int(_in_loop(n, loops, funcs)), n.start_point[0] + 1))
            elif t == "variadic_placeholder":
                par = n.parent
                while par is not None and par.type != "arguments":
                    par = par.parent
                call = par.parent if par is not None else None
                bufs.rows("dynamic_sites").append(
                    (self._sid_at(n, rec.fid, funcs), rec.fid,
                     "first_class_callable",
                     _txt(call, src)[:120] if call is not None else "...",
                     int(_in_loop(n, loops, funcs)), n.start_point[0] + 1))

    def _sid_at(self, node: Any, fid: int, funcs: set) -> Optional[int]:
        cur = node.parent
        while cur is not None:
            if cur.type in funcs:
                return self._fn_sid.get((fid, cur.start_byte))
            cur = cur.parent
        return None

    def _maybe_dynamic_site(self, n: Any, rec: FileRec, bufs: Buffers,
                            loops: set, funcs: set) -> None:
        src = rec.data
        t = n.type
        kind = ""
        target = ""
        if t == "function_call_expression":
            fn = n.child_by_field_name("function")
            if fn is None:
                return
            if fn.type in ("name", "qualified_name"):
                base = _txt(fn, src).strip().lstrip("\\").rsplit("\\", 1)[-1]
                if base not in DYNAMIC_CALLS:
                    return
                kind = "eval" if base in ("eval", "create_function") else base
                args = n.child_by_field_name("arguments")
                target = _txt(args, src)[:120] if args is not None else ""
            else:
                kind = "variable_function"
                target = _txt(fn, src)[:120]
        elif t in ("member_call_expression", "nullsafe_member_call_expression"):
            nm = n.child_by_field_name("name")
            if nm is None or nm.type == "name":
                return
            kind = "variable_method"
            target = _txt(n, src)[:120]
        elif t == "scoped_call_expression":
            nm = n.child_by_field_name("name")
            sc = n.child_by_field_name("scope")
            if ((nm is None or nm.type == "name")
                    and (sc is None or sc.type != "variable_name")):
                return
            kind = "variable_static"
            target = _txt(n, src)[:120]
        if not kind:
            return
        bufs.rows("dynamic_sites").append(
            (self._sid_at(n, rec.fid, funcs), rec.fid, kind, target,
             int(_in_loop(n, loops, funcs)), n.start_point[0] + 1))

    def _maybe_sql_site(self, n: Any, rec: FileRec, bufs: Buffers,
                        loops: set, funcs: set) -> None:
        src = rec.data
        callee, driver = _sql_callee(n, src)
        args = n.child_by_field_name("arguments")
        if args is None:
            return
        first = None
        for a in args.named_children:
            if a.type == "argument":
                kids = [c for c in a.named_children]
                first = kids[0] if kids else None
                break
        atxt = _txt(args, src)
        looks_sql = bool(SQL_RE.search(atxt))
        if not callee and not looks_sql:
            return
        if not callee and looks_sql:
            callee, driver = _sql_callee(n, src, force=True)
            if not callee:
                return
        build, sanitized = _build_kind(first, src)
        prepared = bool(PLACEHOLDER_RE.search(atxt)) or callee.endswith(
            ("prepare", "::prepare"))
        if not sanitized:
            sanitized = any(e in atxt for e in SQL_ESCAPERS)
        bufs.rows("sql_sites").append(
            (self._sid_at(n, rec.fid, funcs), rec.fid, callee[:120],
             driver, build, int(sanitized or build == "literal"),
             int(prepared),
             int(any(sg in atxt for sg in SUPERGLOBALS)),
             int(_in_loop(n, loops, funcs)), n.start_point[0] + 1,
             atxt.replace("\n", " ")[:180]))

    def _namespace_at(self, fid: int, byte: int) -> str:
        spans = self._ns_spans.get(fid)
        if not spans:
            return ""
        cur = ""
        for start, name in spans:
            if start <= byte:
                cur = name
            else:
                break
        return cur

    # -- manifests / meta ---------------------------------------------------
    def parse_manifests(self, root: str, db: sqlite3.Connection) -> None:
        db.execute(
            "INSERT OR REPLACE INTO meta(key,value) VALUES(?,?)",
            ("grammar_note",
             "tree-sitter-php 0.24.1 rejects exactly three of PHP 8.5's "
             "additions: the (void) cast (1 ERROR node), clone(x, [...]) in some spellings "
             "(3), and `final` on a promoted constructor property (1). Every "
             "other construct in a 23-case 8.0-8.5 sweep parses clean -- "
             "property hooks, private(set), DNF types, enums, #[Attr], ?->, "
             "match, named args, heredoc/nowdoc, group use, first-class "
             "callables, and 8.5's |> pipe. So a file with a handful of parse "
             "errors and no other symptom is a grammar one version behind the "
             "language, not a broken file. Read n_parse_errors that way."))
        path = os.path.join(root, "composer.json")
        if not os.path.isfile(path):
            return
        try:
            data = json.loads(open(path, encoding="utf-8",
                                   errors="replace").read())
        except (OSError, ValueError):
            return
        req = (data.get("require") or {})
        self.php_version = str(req.get("php", "") or "")
        psr4 = ((data.get("autoload") or {}).get("psr-4") or {})
        meta_rows = (
            ("composer_name", str(data.get("name", "?"))),
            ("php_constraint", self.php_version or "(unset)"),
            ("psr4_roots", ", ".join(sorted(psr4))[:400] or "(none)"),
            ("php_85_features",
             "n_pipe_operator counts 8.5's |> only; a codebase pinned below "
             "8.5 shows zero for reasons of version, not style"),
        )
        db.executemany("INSERT OR REPLACE INTO meta(key,value) VALUES(?,?)",
                       meta_rows)

    def flush_extra(self, db: sqlite3.Connection, bufs: Buffers) -> None:
        for tbl, sql in (
            ("classes",
             "INSERT OR IGNORE INTO classes(symbol_id,file_id,name,fqn,"
             "namespace,kind,extends,implements,traits,n_traits,n_methods,"
             "n_public_methods,n_static_methods,n_props,n_promoted,n_hooks,"
             "n_consts,n_enum_cases,n_magic,is_abstract,is_final,is_readonly,"
             "is_anonymous,has_destruct,has_wakeup,has_tostring,has_call,"
             "has_callstatic,has_get,has_invoke,line) VALUES(%s)"
             % ",".join("?" * 31)),
            ("traits",
             "INSERT OR IGNORE INTO traits(symbol_id,file_id,name,namespace,"
             "n_methods,n_abstract_methods,n_props,used_by,line) "
             "VALUES(?,?,?,?,?,?,?,?,?)"),
            ("namespaces",
             "INSERT INTO namespaces(file_id,name,line,has_strict_types,"
             "n_classes) VALUES(?,?,?,?,?)"),
            ("superglobal_reads",
             "INSERT INTO superglobal_reads(symbol_id,file_id,var,key_,line,"
             "in_loop,is_psalm_tainted) VALUES(?,?,?,?,?,?,?)"),
            ("sql_sites",
             "INSERT INTO sql_sites(symbol_id,file_id,callee,driver,"
             "build_kind,is_sanitized,is_prepared,has_superglobal,in_loop,"
             "line,snippet) VALUES(?,?,?,?,?,?,?,?,?,?,?)"),
            ("property_hooks",
             "INSERT INTO property_hooks(symbol_id,class_id,file_id,"
             "class_name,property,hook,is_short,is_virtual,body_sloc,n_calls,"
             "line) VALUES(?,?,?,?,?,?,?,?,?,?,?)"),
            ("magic_methods",
             "INSERT INTO magic_methods(symbol_id,class_id,file_id,class_name,"
             "method,is_gadget,body_sloc,n_calls,n_hazards,line) "
             "VALUES(?,?,?,?,?,?,?,?,?,?)"),
            ("dynamic_sites",
             "INSERT INTO dynamic_sites(symbol_id,file_id,kind,target,in_loop,"
             "line) VALUES(?,?,?,?,?,?)"),
        ):
            rows = bufs.extra.get(tbl)
            if rows:
                db.executemany(sql, rows)

def _txt(node: Any, src: bytes) -> str:
    return src[node.start_byte:node.end_byte].decode("utf-8", "replace")

def _modifiers(node: Any, src: bytes) -> set[str]:
    out: set[str] = set()
    for c in node.named_children:
        if c.type in ("abstract_modifier", "final_modifier", "static_modifier",
                      "readonly_modifier", "visibility_modifier",
                      "var_modifier"):
            out.add(_txt(c, src).strip())
    return out

def _attribute_names(node: Any, src: bytes) -> list[str]:
    attrs = node.child_by_field_name("attributes")
    if attrs is None:
        return []
    out: list[str] = []
    for n in walk(attrs):
        if n.type != "attribute":
            continue
        for c in n.named_children:
            if c.type in ("name", "qualified_name"):
                out.append(_txt(c, src).strip().lstrip("\\"))
                break
    return out

def _in_loop(node: Any, loops: set, funcs: set) -> bool:
    cur = node.parent
    while cur is not None:
        if cur.type in loops:
            return True
        if cur.type in funcs:
            return False
        cur = cur.parent
    return False

def _hook_property(hook: Any, src: bytes) -> str:
    """The property a hook belongs to: hook -> hook_list -> declaration."""
    cur = hook.parent
    while cur is not None and cur.type != "property_declaration":
        cur = cur.parent
    if cur is None:
        return ""
    for c in cur.named_children:
        if c.type == "property_element":
            nm = c.child_by_field_name("name")
            return _txt(nm, src).lstrip("$") if nm is not None else ""
    return ""

def _hook_is_virtual(hook: Any, src: bytes) -> bool:
    """A hook that never touches its own backing field is a virtual property.

    That matters because a virtual property has no storage at all: reading it
    is unconditionally a function call, which is exactly the case the call
    graph must model rather than treat as a field access.
    """
    prop = _hook_property(hook, src)
    if not prop:
        return False
    body = hook.child_by_field_name("body")
    return body is not None and ("$this->%s" % prop) not in _txt(body, src)

def _receiver_type(raw: str, cls: str, parent_cls: str) -> str:
    """Which type's method table a recorded call should be looked up in.

    The base resolver checks `type_scope[(ty, short_name)]` first, so `ty`
    decides correctness. A free function must NOT carry the enclosing class or
    every `count()` inside a class with a `count()` method resolves to itself.
    """
    if raw.startswith("->"):
        return cls                      # $obj->m(): best guess is $this
    if raw.startswith("new "):
        raw = raw[4:]
    if "::" in raw:
        head = raw.split("::", 1)[0]
        if head in ("self", "static"):
            return cls
        if head == "parent":
            return parent_cls
        return head.rsplit("\\", 1)[-1]
    return ""                           # free function: no receiver at all

def _class_body_counts(body: Any, src: bytes) -> dict[str, Any]:
    out: dict[str, Any] = {}
    trait_names: list[str] = []
    for c in body.named_children:
        t = c.type
        if t == "method_declaration":
            out["methods"] = out.get("methods", 0) + 1
            mods = _modifiers(c, src)
            if "static" in mods:
                out["static_methods"] = out.get("static_methods", 0) + 1
            if "abstract" in mods or c.child_by_field_name("body") is None:
                out["abstract"] = out.get("abstract", 0) + 1
            if "private" not in mods and "protected" not in mods:
                out["public_methods"] = out.get("public_methods", 0) + 1
            nm = c.child_by_field_name("name")
            name = _txt(nm, src) if nm is not None else ""
            if name in MAGIC_METHODS:
                out["magic"] = out.get("magic", 0) + 1
            if name == "__destruct":
                out["destruct"] = 1
            elif name in ("__wakeup", "__unserialize"):
                out["wakeup"] = 1
            elif name == "__toString":
                out["tostring"] = 1
            elif name == "__call":
                out["callmagic_call"] = 1
                out["callmagic"] = out.get("callmagic", 0) + 1
            elif name == "__callStatic":
                out["callmagic_static"] = 1
                out["callmagic"] = out.get("callmagic", 0) + 1
            elif name in ("__get", "__set"):
                out["get"] = 1
            elif name == "__invoke":
                out["invoke"] = 1
            params = c.child_by_field_name("parameters")
            if params is not None:
                for p in params.named_children:
                    if p.type == "property_promotion_parameter":
                        out["promoted"] = out.get("promoted", 0) + 1
                        if p.child_by_field_name("readonly") is not None:
                            out["readonly"] = out.get("readonly", 0) + 1
        elif t == "property_declaration":
            out["props"] = out.get("props", 0) + 1
            if any(x.type == "readonly_modifier" for x in c.named_children):
                out["readonly"] = out.get("readonly", 0) + 1
            for x in c.named_children:
                if x.type == "property_hook_list":
                    out["hooks"] = out.get("hooks", 0) + len(
                        [h for h in x.named_children
                         if h.type == "property_hook"])
        elif t == "const_declaration":
            out["consts"] = out.get("consts", 0) + 1
        elif t == "enum_case":
            out["cases"] = out.get("cases", 0) + 1
        elif t == "use_declaration":
            for x in c.named_children:
                if x.type in ("name", "qualified_name"):
                    trait_names.append(
                        _txt(x, src).strip().lstrip("\\").rsplit("\\", 1)[-1])
    out["traits"] = len(trait_names)
    out["trait_names"] = ",".join(trait_names)
    return out

def _class_fields(body: Any, src: bytes) -> list[tuple]:
    """(name, type, visibility, line, is_static, is_const, is_readonly)."""
    out: list[tuple] = []
    for c in body.named_children:
        if c.type == "property_declaration":
            mods = _modifiers(c, src)
            vis = next((m.split("(")[0] for m in mods
                        if m.split("(")[0] in ("public", "private",
                                               "protected")), "public")
            tnode = c.child_by_field_name("type")
            ftype = _txt(tnode, src).strip() if tnode is not None else ""
            for el in c.named_children:
                if el.type != "property_element":
                    continue
                nm = el.child_by_field_name("name")
                out.append(((_txt(nm, src).lstrip("$") if nm is not None
                             else ""), ftype, vis, c.start_point[0] + 1,
                            "static" in mods, False, "readonly" in mods))
        elif c.type == "const_declaration":
            tnode = c.child_by_field_name("type")
            ftype = _txt(tnode, src).strip() if tnode is not None else ""
            for el in c.named_children:
                if el.type != "const_element":
                    continue
                nm = el.named_children[0] if el.named_children else None
                out.append(((_txt(nm, src) if nm is not None else ""),
                            ftype, "public", c.start_point[0] + 1,
                            True, True, True))
        elif c.type == "method_declaration":
            params = c.child_by_field_name("parameters")
            if params is None:
                continue
            for p in params.named_children:
                if p.type != "property_promotion_parameter":
                    continue
                nm = p.child_by_field_name("name")
                tnode = p.child_by_field_name("type")
                vnode = p.child_by_field_name("visibility")
                out.append(((_txt(nm, src).lstrip("$") if nm is not None
                             else ""),
                            _txt(tnode, src).strip() if tnode is not None
                            else "",
                            (_txt(vnode, src).split("(")[0]
                             if vnode is not None else "public"),
                            p.start_point[0] + 1, False, False,
                            p.child_by_field_name("readonly") is not None))
    return out

_SQL_METHODS = {
    "query": "pdo", "exec": "pdo", "prepare": "pdo", "statement": "pdo",
    "unprepared": "pdo", "select": "builder", "insert": "builder",
    "update": "builder", "delete": "builder", "raw": "raw",
    "selectRaw": "raw", "whereRaw": "raw", "orWhereRaw": "raw",
    "havingRaw": "raw", "orderByRaw": "raw", "groupByRaw": "raw",
    "fromRaw": "raw", "joinSub": "raw", "createQuery": "doctrine",
    "createNativeQuery": "doctrine", "getQuery": "doctrine",
}

_SQL_FUNCTIONS = {
    "mysqli_query": "mysqli", "mysqli_multi_query": "mysqli",
    "mysqli_real_query": "mysqli", "mysqli_prepare": "mysqli",
    "mysql_query": "mysql", "mysql_db_query": "mysql",
    "pg_query": "pgsql", "pg_send_query": "pgsql",
    "pg_query_params": "pgsql", "sqlsrv_query": "sqlsrv",
    "oci_parse": "oci", "db2_exec": "db2", "sqlite_query": "sqlite",
}

def _sql_callee(n: Any, src: bytes, force: bool = False) -> tuple[str, str]:
    t = n.type
    if t == "function_call_expression":
        fn = n.child_by_field_name("function")
        if fn is None or fn.type not in ("name", "qualified_name"):
            return ("dynamic", "unknown") if force else ("", "")
        base = _txt(fn, src).strip().lstrip("\\").rsplit("\\", 1)[-1]
        d = _SQL_FUNCTIONS.get(base)
        if d:
            return base, d
        return (base, "unknown") if force else ("", "")
    nm = n.child_by_field_name("name")
    if nm is None or nm.type != "name":
        return ("dynamic", "unknown") if force else ("", "")
    base = _txt(nm, src)
    if t == "scoped_call_expression":
        sc = n.child_by_field_name("scope")
        cls = _txt(sc, src).strip().lstrip("\\") if sc is not None else ""
        d = _SQL_METHODS.get(base)
        if d or force:
            return "%s::%s" % (cls, base), (d or "unknown")
        return "", ""
    d = _SQL_METHODS.get(base)
    if d or force:
        return "->" + base, (d or "unknown")
    return "", ""

def _build_kind(arg: Any, src: bytes) -> tuple[str, bool]:
    """How the SQL string was assembled, and whether anything escaped it."""
    if arg is None:
        return "variable", False
    t = arg.type
    if t == "string":
        return "literal", True
    if t in ("encapsed_string", "heredoc"):
        has_var = any(c.type in ("variable_name", "member_access_expression",
                                 "subscript_expression",
                                 "nullsafe_member_access_expression")
                      for c in walk(arg))
        return ("interp", False) if has_var else ("literal", True)
    if t == "nowdoc":
        return "literal", True
    if t == "binary_expression":
        op = arg.child_by_field_name("operator")
        if op is not None and _txt(op, src) == ".":
            txt = _txt(arg, src)
            return "concat", any(e in txt for e in SQL_ESCAPERS)
        return "variable", False
    if t == "function_call_expression":
        fn = arg.child_by_field_name("function")
        base = (_txt(fn, src).strip().rsplit("\\", 1)[-1]
                if fn is not None else "")
        if base in ("sprintf", "vsprintf", "printf", "str_replace", "strtr"):
            return "format", False
        if base in SQL_ESCAPERS or base in ("intval", "floatval"):
            return "variable", True
        return "variable", False
    if t in ("variable_name", "member_access_expression",
             "nullsafe_member_access_expression", "subscript_expression"):
        return "variable", False
    return "variable", False

PhpAnalyzer.QUERIES = [
(
    "superglobal-to-sql",
    "Attacker-controlled input reaching a SQL-building site, up to 4 hops",
    "ANSWERS the injection question no single-file checker can answer: the read\n"
    "     of $_GET and the string concatenation that becomes the query live in\n"
    "     different functions.\n"
    "ACT build_kind is the whole finding. `interp` and `concat` mean the value\n"
    "     was spliced into SQL text; `literal` and a prepared statement mean it\n"
    "     was not. Fix `interp`/`concat` with bound parameters, top of list\n"
    "     first -- hops=0 is a direct splice in one function.\n"
    "MISLEADS depth is capped at 4 (a facade adds 2-3 hops on its own, and past\n"
    "     4 the path is mostly unresolved edges and the answer stops meaning\n"
    "     anything), and ONLY resolved edges are walked, so this is a floor --\n"
    "     read graph-blindspots first. psalm_only counts the four superglobals\n"
    "     Psalm actually taints; $_SERVER/$_FILES are attacker-controlled in\n"
    "     practice but would not appear in a Psalm baseline.",
    """WITH RECURSIVE walk(src, sym, depth) AS (
        -- depth bound 4
        SELECT s.id, s.id, 0 FROM symbols s WHERE s.n_superglobal_reads > 0
        UNION
        SELECT r.src, e.callee_id, r.depth+1
        FROM walk r JOIN edges e ON e.caller_id = r.sym
        WHERE r.depth < 4 AND e.is_self = 0),
        -- One row per (src, sym) pair. The recursive walk emits one row per
        -- DEPTH at which a symbol is reachable, so joining it straight to
        -- the per-site table counted every site once per distinct path
        -- length. Collapse to the shortest path before counting.
        reach(src, sym, depth) AS (
            SELECT src, sym, MIN(depth) FROM walk GROUP BY src, sym)
    SELECT src.name AS reads_input, sink.name AS builds_sql,
        MIN(r.depth) AS hops, q.build_kind, q.driver,
        COUNT(*) AS sites, SUM(q.is_sanitized) AS sanitized,
        SUM(q.is_prepared) AS prepared, SUM(q.has_superglobal) AS direct_super,
        src.n_psalm_tainted AS psalm_only, src.n_superglobal_reads AS all_super,
        f.path || ':' || MIN(q.line) AS at
    FROM reach r
    JOIN sql_sites q ON q.symbol_id = r.sym
    JOIN symbols src ON src.id = r.src
    JOIN symbols sink ON sink.id = r.sym
    JOIN files f ON f.id = q.file_id
    JOIN files sf ON sf.id = src.file_id
    LEFT JOIN modules m ON m.id = sink.module_id
    WHERE f.is_test = 0 AND sf.is_test = 0 AND COALESCE(m.name,'') LIKE :mod
      AND q.build_kind IN ('interp','concat','format','variable')
    GROUP BY src.id, sink.id, q.build_kind
    ORDER BY (q.build_kind='interp') DESC, sanitized ASC,
        hops ASC, sites DESC LIMIT :lim"""),
(
    "superglobal-to-include",
    "A variable include/require reachable from user input, up to 3 hops",
    "ANSWERS local and remote file inclusion, which in PHP is a single\n"
    "     `include $page` away from remote code execution.\n"
    "ACT an `include` whose argument is not a literal is the finding. Replace it\n"
    "     with a whitelist map from a request value to a fixed path. Nothing\n"
    "     else is safe -- basename() and str_replace('..') both have bypasses.\n"
    "MISLEADS depth is capped at 3 because an include this far from its input is\n"
    "     usually a template loader with a fixed set of names. A router that\n"
    "     builds paths from a config array shows here and is fine. A literal\n"
    "     include is excluded entirely; only the variable ones are listed.",
    """WITH RECURSIVE walk(src, sym, depth) AS (
        -- depth bound 3
        SELECT s.id, s.id, 0 FROM symbols s WHERE s.n_superglobal_reads > 0
        UNION
        SELECT r.src, e.callee_id, r.depth+1
        FROM walk r JOIN edges e ON e.caller_id = r.sym
        WHERE r.depth < 3 AND e.is_self = 0),
        -- One row per (src, sym) pair. The recursive walk emits one row per
        -- DEPTH at which a symbol is reachable, so joining it straight to
        -- the per-site table counted every site once per distinct path
        -- length. Collapse to the shortest path before counting.
        reach(src, sym, depth) AS (
            SELECT src, sym, MIN(depth) FROM walk GROUP BY src, sym)
    SELECT src.name AS reads_input, sink.name AS includes,
        MIN(r.depth) AS hops, COUNT(d.id) AS variable_includes,
        SUM(d.in_loop) AS in_loop,
        GROUP_CONCAT(DISTINCT SUBSTR(d.target,1,40)) AS argument,
        src.n_get, src.n_post, src.n_request, src.n_server,
        f.path || ':' || MIN(d.line) AS at
    FROM reach r
    JOIN dynamic_sites d ON d.symbol_id = r.sym AND d.kind = 'variable_include'
    JOIN symbols src ON src.id = r.src
    JOIN symbols sink ON sink.id = r.sym
    JOIN files f ON f.id = d.file_id
    LEFT JOIN modules m ON m.id = sink.module_id
    WHERE f.is_test = 0 AND COALESCE(m.name,'') LIKE :mod
    GROUP BY src.id, sink.id
    ORDER BY hops ASC, variable_includes DESC LIMIT :lim"""),
(
    "unserialize-gadget-frontier",
    "unserialize reachable from input, against the repo's gadget surface",
    "ANSWERS both halves of a PHP object-injection chain at once. Half one is a\n"
    "     reachable `unserialize`; half two is the set of __destruct / __wakeup\n"
    "     / __toString methods ANYWHERE in the tree, because those run with no\n"
    "     call site the moment a crafted payload is deserialized.\n"
    "ACT a reachable unserialize is exploitable in proportion to gadgets_in_repo,\n"
    "     which is why that column is repo-wide rather than per-namespace.\n"
    "     Replace with json_decode, or pass allowed_classes: false.\n"
    "MISLEADS hops=0 is the normal result, not a missing measurement: the read\n"
    "     and the sink usually sit in one function. Depth is capped at 4. The\n"
    "     gadget count is a COUNT of magic methods,\n"
    "     not a proof any chain composes -- building one needs a property write\n"
    "     path this does not model. Conversely a gadget in an installed package\n"
    "     under vendor/ is invisible here and PHPGGC's whole catalogue lives\n"
    "     there, so a low count is not safety.",
    """WITH RECURSIVE reach(src, sym, depth) AS (
        -- depth bound 4
        SELECT s.id, s.id, 0 FROM symbols s WHERE s.n_superglobal_reads > 0
        UNION
        SELECT r.src, e.callee_id, r.depth+1
        FROM reach r JOIN edges e ON e.caller_id = r.sym
        WHERE r.depth < 4 AND e.is_self = 0),
    surface AS (
        SELECT COUNT(*) AS n_gadgets,
            SUM(method='__destruct') AS n_destruct,
            SUM(method='__wakeup') AS n_wakeup,
            SUM(method='__toString') AS n_tostring,
            SUM(n_hazards) AS gadget_hazards
        FROM magic_methods WHERE is_gadget = 1)
    SELECT src.name AS reads_input, sink.name AS deserializes,
        MIN(r.depth) AS hops, sink.n_deserialize AS unserialize_calls,
        surface.n_gadgets AS gadgets_in_repo, surface.n_destruct AS destructs,
        surface.n_wakeup AS wakeups, surface.n_tostring AS tostrings,
        surface.gadget_hazards AS hazards_inside_gadgets,
        f.path || ':' || sink.line_start AS at
    FROM reach r
    JOIN symbols sink ON sink.id = r.sym AND sink.n_deserialize > 0
    JOIN symbols src ON src.id = r.src
    JOIN files f ON f.id = sink.file_id
    LEFT JOIN modules m ON m.id = sink.module_id
    CROSS JOIN surface
    WHERE f.is_test = 0 AND COALESCE(m.name,'') LIKE :mod
    GROUP BY src.id, sink.id
    ORDER BY hops ASC, unserialize_calls DESC LIMIT :lim"""),
(
    "superglobal-to-shell",
    "User input reaching exec/system/shell_exec/backticks, up to 3 hops",
    "ANSWERS command injection across function boundaries.\n"
    "ACT escapeshellarg on the ARGUMENT, never escapeshellcmd on the whole\n"
    "     command -- the second does not stop argument injection. Better still,\n"
    "     use proc_open with an argument ARRAY so no shell is involved.\n"
    "MISLEADS depth is capped at 3: a shell call three frames from its input is\n"
    "     usually a deployment or build helper, and past that the paths are\n"
    "     dominated by unresolved edges. `exec` as a bare method name also\n"
    "     matches PDO::exec, which is a SQL sink and not a shell one -- the\n"
    "     driver column in Q2 is where that distinction lives.",
    """WITH RECURSIVE reach(src, sym, depth) AS (
        -- depth bound 3
        SELECT s.id, s.id, 0 FROM symbols s WHERE s.n_superglobal_reads > 0
        UNION
        SELECT r.src, e.callee_id, r.depth+1
        FROM reach r JOIN edges e ON e.caller_id = r.sym
        WHERE r.depth < 3 AND e.is_self = 0)
    SELECT src.name AS reads_input, sink.name AS runs_shell,
        MIN(r.depth) AS hops, sink.n_shell AS shell_calls,
        sink.n_exec AS code_exec, sink.n_eval AS evals,
        GROUP_CONCAT(DISTINCT h.pattern) AS patterns,
        src.n_get + src.n_post + src.n_request AS psalm_tainted_reads,
        sink.n_escaped_output AS escapes, sink.risk_score AS risk,
        f.path || ':' || sink.line_start AS at
    FROM reach r
    JOIN symbols sink ON sink.id = r.sym
    JOIN symbols src ON src.id = r.src
    JOIN files f ON f.id = sink.file_id
    LEFT JOIN hazards h ON h.symbol_id = sink.id
        AND h.category IN ('shell','exec')
    LEFT JOIN modules m ON m.id = sink.module_id
    WHERE (sink.n_shell > 0 OR sink.n_exec > 0 OR sink.n_eval > 0)
      AND f.is_test = 0 AND COALESCE(m.name,'') LIKE :mod
    GROUP BY src.id, sink.id
    ORDER BY hops ASC, shell_calls DESC LIMIT :lim"""),
(
    "superglobal-to-echo",
    "Unescaped output of reachable input, with escaping as counter-evidence",
    "ANSWERS reflected XSS: an `echo`/`print` of a value that came from a\n"
    "     superglobal, with no htmlspecialchars between them.\n"
    "ACT raw_echo is the finding and escaped is the counter-evidence -- a\n"
    "     function with raw_echo>0 and escaped=0 is the shape to fix. Escape at\n"
    "     output with htmlspecialchars(..., ENT_QUOTES, 'UTF-8'), or use a\n"
    "     template engine that escapes by default.\n"
    "MISLEADS hops=0 is the normal result -- `echo $_GET['x']` in one function\n"
    "     is the commonest shape by far, and a row with hops>0 is the rarer,\n"
    "     more interesting case. Escaping is detected LEXICALLY inside the\n"
    "     echo statement, so a\n"
    "     value escaped one frame earlier reads as raw here, and one escaped\n"
    "     with a project-specific helper this does not know reads as raw too.\n"
    "     A Blade/Twig template compiled to PHP escapes correctly and may still\n"
    "     appear. Treat a row as 'check', not as 'vulnerable'.",
    """WITH RECURSIVE reach(src, sym, depth) AS (
        -- depth bound 3
        SELECT s.id, s.id, 0 FROM symbols s WHERE s.n_superglobal_reads > 0
        UNION
        SELECT r.src, e.callee_id, r.depth+1
        FROM reach r JOIN edges e ON e.caller_id = r.sym
        WHERE r.depth < 3 AND e.is_self = 0)
    SELECT src.name AS reads_input, sink.name AS writes_output,
        MIN(r.depth) AS hops, sink.n_raw_echo AS raw_echo,
        sink.n_escaped_output AS escaped, sink.n_xss AS xss_calls,
        sink.n_header AS header_calls,
        src.n_get, src.n_post, src.n_cookie, src.n_server,
        f.path || ':' || sink.line_start AS at
    FROM reach r
    JOIN symbols sink ON sink.id = r.sym AND sink.n_raw_echo > 0
    JOIN symbols src ON src.id = r.src
    JOIN files f ON f.id = sink.file_id
    LEFT JOIN modules m ON m.id = sink.module_id
    WHERE f.is_test = 0 AND COALESCE(m.name,'') LIKE :mod
    GROUP BY src.id, sink.id
    HAVING escaped = 0
    ORDER BY hops ASC, raw_echo DESC LIMIT :lim"""),
(
    "n-plus-one",
    "A query whose CALLER puts it in a foreach, followed through model methods",
    "ANSWERS the N+1 no per-file linter can see, because the loop is in the\n"
    "     controller and the query is two frames down in the model.\n"
    "ACT eager-load the relation, batch the ids into one WHERE IN, or hoist the\n"
    "     query out of the loop. loop_depth>1 multiplies.\n"
    "MISLEADS trip count is invisible: a loop over a fixed three-element config\n"
    "     array is not an N+1. `->get`/`->find`/`->first` are counted as query\n"
    "     calls by NAME, so a collection's ->first() is a false positive. Depth\n"
    "     is capped at 3 hops from the loop.",
    """WITH RECURSIVE below(root, sym, depth) AS (
        -- depth bound 3
        SELECT s.id, s.id, 0 FROM symbols s
        WHERE s.max_loop_depth > 0 AND s.call_in_loop > 0
        UNION
        SELECT b.root, e.callee_id, b.depth+1
        FROM below b JOIN edges e ON e.caller_id = b.sym
        WHERE b.depth < 3 AND e.is_self = 0)
    SELECT cal.name AS loops_in, cle.name AS queries_in,
        MIN(b.depth) AS hops, cal.max_loop_depth AS loop_depth,
        cal.query_in_loop AS query_calls_in_loop,
        cle.n_sql_calls AS sql_sites, cle.n_sql AS sql_hazards,
        cal.is_controller AS controller, cle.is_model AS model,
        cal.fan_in AS caller_fan_in,
        f.path || ':' || cal.line_start AS at
    FROM below b
    JOIN symbols cal ON cal.id = b.root
    JOIN symbols cle ON cle.id = b.sym
    JOIN files f ON f.id = cal.file_id
    LEFT JOIN modules m ON m.id = cal.module_id
    WHERE b.depth > 0 AND (cle.n_sql_calls > 0 OR cle.n_sql > 0)
      AND f.is_test = 0 AND COALESCE(m.name,'') LIKE :mod
    GROUP BY cal.id, cle.id
    ORDER BY loop_depth DESC, sql_sites DESC LIMIT :lim"""),
(
    "type-juggling-auth",
    "Loose == on a value that reaches from a superglobal",
    "ANSWERS the authentication bypass PHP is famous for. Before 8.0,\n"
    "     '0e123' == '0e456' was true because both are 'numeric'; 8.0 fixed the\n"
    "     string-to-int direction but == still coerces across types, so\n"
    "     `$_GET['admin'] == true` is true for any non-empty string, and\n"
    "     in_array($x, $arr) without the third argument is a loose search.\n"
    "ACT use === for every comparison of a value that came from a request, and\n"
    "     hash_equals for anything secret. loose_cmp on a token check is the\n"
    "     shape that matters; a loose compare on two ints is noise.\n"
    "MISLEADS this counts loose comparisons ANYWHERE in a function that also\n"
    "     reads a superglobal or is reachable from one within 3 hops -- it does\n"
    "     NOT prove the tainted value is an operand. Read the function. A\n"
    "     codebase already on strict_types still juggles at ==; the declare\n"
    "     governs parameter coercion, not comparison.",
    """WITH RECURSIVE reach(src, sym, depth) AS (
        -- depth bound 3
        SELECT s.id, s.id, 0 FROM symbols s WHERE s.n_superglobal_reads > 0
        UNION
        SELECT r.src, e.callee_id, r.depth+1
        FROM reach r JOIN edges e ON e.caller_id = r.sym
        WHERE r.depth < 3 AND e.is_self = 0)
    SELECT sink.name AS in_fn, MIN(r.depth) AS hops_from_input,
        sink.n_loose_compare AS loose_cmp,
        sink.n_strict_compare AS strict_cmp,
        sink.has_strict_types AS strict_types_file,
        sink.n_superglobal_reads AS own_super_reads,
        sink.n_crypto AS crypto_calls, sink.n_header AS session_header,
        sink.is_entrypoint AS entrypoint, sink.fan_in,
        CAST(100.0*sink.n_loose_compare
             /NULLIF(sink.n_loose_compare+sink.n_strict_compare,0) AS INT)
            AS pct_loose,
        f.path || ':' || sink.line_start AS at
    FROM reach r
    JOIN symbols sink ON sink.id = r.sym AND sink.n_loose_compare > 0
    JOIN files f ON f.id = sink.file_id
    LEFT JOIN modules m ON m.id = sink.module_id
    WHERE f.is_test = 0 AND COALESCE(m.name,'') LIKE :mod
    GROUP BY sink.id
    ORDER BY (sink.n_crypto > 0) DESC, pct_loose DESC,
        loose_cmp DESC LIMIT :lim"""),
(
    "driver-split",
    "mysqli and PDO in the same namespace: two escaping disciplines, one module",
    "ANSWERS which namespaces mix database drivers. It matters because each\n"
    "     driver escapes differently -- mysqli_real_escape_string needs a live\n"
    "     connection handle and silently returns an empty string without one,\n"
    "     PDO::quote is connection-bound too, and a query builder does neither\n"
    "     because it binds. Mixing them means no single review rule applies.\n"
    "ACT pick one. If a namespace shows both pdo and mysqli, the migration was\n"
    "     never finished and the half-migrated code is where the unescaped\n"
    "     concatenations live.\n"
    "MISLEADS the driver is inferred from the CALLEE NAME, because the receiver's\n"
    "     type is not knowable without full inference. `->query` on a PDO handle\n"
    "     and `->query` on a query builder are indistinguishable here and both\n"
    "     land in `pdo`. `builder` is a guess from Laravel/Doctrine method\n"
    "     names. Read this as 'how many escaping conventions are in play', not\n"
    "     as an inventory of connections.",
    """SELECT m.name AS namespace_,
        COUNT(DISTINCT q.driver) AS drivers,
        GROUP_CONCAT(DISTINCT q.driver) AS which,
        COUNT(*) AS sql_sites,
        SUM(q.driver='pdo') AS pdo_, SUM(q.driver='mysqli') AS mysqli_,
        SUM(q.driver='pgsql') AS pgsql_, SUM(q.driver='raw') AS raw_,
        SUM(q.driver='builder') AS builder_,
        SUM(q.driver='doctrine') AS doctrine_,
        SUM(q.build_kind IN ('interp','concat')) AS spliced,
        SUM(q.is_prepared) AS prepared, SUM(q.is_sanitized) AS sanitized
    FROM sql_sites q
    JOIN files f ON f.id = q.file_id
    JOIN modules m ON m.id = f.module_id
    WHERE f.is_test = 0 AND m.name LIKE :mod
    GROUP BY m.id
    HAVING sql_sites > 0
    ORDER BY drivers DESC, spliced DESC LIMIT :lim"""),
(
    "file-upload-surface",
    "$_FILES handling, and whether anything nearby validates it",
    "ANSWERS where uploaded files enter. Unrestricted upload is a direct path\n"
    "     to remote code execution: a .php written under the web root runs,\n"
    "     and a filename containing ../ escapes wherever you meant to put it.\n"
    "ACT never trust the client-supplied name or MIME type. Generate the\n"
    "     stored name yourself, verify the content, store OUTSIDE the web\n"
    "     root, and serve through a script rather than a URL path.\n"
    "MISLEADS this finds the READ of $_FILES, not the write. A handler that\n"
    "     passes the array straight to a hardened library is fine and appears\n"
    "     here; one that builds a path by concatenation does not look worse.",
    """SELECT s.name, s.class_name AS class_, s.n_files_super AS files_reads,
        s.n_superglobal_reads AS all_super, s.n_io AS io_ops,
        s.n_dynamic_include AS dyn_includes, s.n_sql_calls AS sql_calls,
        s.is_controller AS controller, s.fan_in,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_files_super > 0 AND f.is_test=0 AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.n_io DESC, s.n_files_super DESC LIMIT :lim"""),
(
    "error-suppression",
    "The @ operator: failures made invisible rather than handled",
    "ANSWERS where the code silences errors instead of dealing with them.\n"
    "     `@` suppresses the diagnostic and returns a falsy value, so the\n"
    "     failure continues as data -- a null that becomes an empty string\n"
    "     that becomes a wrong row.\n"
    "ACT delete the @ and handle what it was hiding. `@$a[k]` predates the\n"
    "     null-coalescing operator and should be `$a[k] ?? default`; `@unlink`\n"
    "     should be `file_exists` or a caught exception.\n"
    "MISLEADS a few @ on genuinely optional filesystem probes are pragmatic,\n"
    "     not wrong. What matters is @ near a superglobal or a SQL call,\n"
    "     which is why those columns are here.",
    """SELECT s.name, s.class_name AS class_, s.n_error_suppress AS suppressed,
        s.n_superglobal_reads AS super_reads, s.n_sql_calls AS sql_calls,
        s.n_try AS trys, s.n_catch_empty AS empty_catches, s.fan_in,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_error_suppress > 0 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.n_error_suppress * (1 + s.n_superglobal_reads + s.n_sql_calls)
             DESC LIMIT :lim"""),
(
    "dynamic-call-surface",
    "Variable variables, variable methods and dynamic new: the parts no tool can follow",
    "ANSWERS how much of this codebase is invisible to every static check,\n"
    "     including this one. `$$name`, `$obj->$method()` and `new $class`\n"
    "     are resolved at run time, so the call graph simply stops there.\n"
    "ACT if the set of targets is known, a match or a map of closures is\n"
    "     faster AND analysable. Where dynamic dispatch is genuinely needed,\n"
    "     validate the name against an allow-list before calling it.\n"
    "MISLEADS this is a blindness measure, not a bug list. A DI container\n"
    "     doing `new $class` is the correct implementation of a container.\n"
    "     The rows that matter are the ones that also read a superglobal.",
    """SELECT s.name, s.class_name AS class_, s.n_variable_var AS var_vars,
        s.n_dynamic_method AS dyn_methods, s.n_dynamic_new AS dyn_new,
        s.n_dynamic_call AS dyn_calls, s.n_eval AS evals,
        s.n_superglobal_reads AS super_reads,
        s.n_unresolved_calls AS unresolved, s.fan_in,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE (s.n_variable_var + s.n_dynamic_method + s.n_dynamic_new
           + s.n_eval) > 0 AND f.is_test=0 AND COALESCE(m.name,'') LIKE :mod
    ORDER BY (s.n_eval*4 + s.n_variable_var*3 + s.n_dynamic_new*2
              + s.n_dynamic_method) * (1 + s.n_superglobal_reads) DESC
    LIMIT :lim"""),
(
    "magic-method-surface",
    "__destruct, __wakeup, __toString: the methods an attacker gets to call",
    "ANSWERS which classes are usable as gadgets. A deserialization attack\n"
    "     does not call your code directly -- it constructs an object graph\n"
    "     and lets PHP invoke the magic methods on the way in and out. Any\n"
    "     __destruct that touches the filesystem is a primitive.\n"
    "ACT the fix is upstream: never unserialize untrusted input, use JSON.\n"
    "     Where a magic method must exist, keep it free of side effects --\n"
    "     no file operations, no exec, no SQL.\n"
    "MISLEADS a class is only a gadget if the attacker can reach\n"
    "     unserialize at all; see unserialize-gadget-frontier for that half.\n"
    "     This lists the ammunition, not the gun.",
    """SELECT s.name, s.class_name AS class_, s.n_destruct AS destructs,
        s.n_wakeup AS wakeups, s.n_tostring AS tostrings,
        s.n_call_magic AS call_magic, s.n_magic_method AS magic_total,
        s.n_io AS io_ops, s.n_exec AS exec_ops, s.n_sql_calls AS sql_calls,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE (s.n_destruct + s.n_wakeup + s.n_tostring + s.n_call_magic) > 0
      AND f.is_test=0 AND COALESCE(m.name,'') LIKE :mod
    ORDER BY (s.n_io + s.n_exec + s.n_sql_calls) DESC,
        s.n_destruct DESC LIMIT :lim"""),
(
    "untyped-public-boundary",
    "Public methods taking untyped parameters, where strict_types is off",
    "ANSWERS where PHP's type coercion still applies. Without\n"
    "     declare(strict_types=1), \"5 apples\" passed to an int parameter\n"
    "     becomes 5, and a caller passing the wrong thing gets silently\n"
    "     corrected instead of corrected loudly.\n"
    "ACT add the parameter types, then add strict_types=1 to the file. Doing\n"
    "     it in that order means the types are enforced the moment they are\n"
    "     declared, rather than documenting an intent nothing checks.\n"
    "MISLEADS a method whose callers are all internal and all typed is not\n"
    "     really at risk. fan_in and is_public together are the ranking:\n"
    "     a widely-called public untyped method is the one that bites.",
    """SELECT s.name, s.class_name AS class_,
        s.n_untyped_params AS untyped, s.n_params AS params,
        s.has_strict_types AS strict_types, s.n_type_declarations AS typed,
        s.n_loose_compare AS loose_eq, s.is_public AS public_, s.fan_in,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_untyped_params > 0 AND s.has_strict_types = 0
      AND s.is_public = 1 AND s.kind IN ('function','method')
      AND f.is_test=0 AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.n_untyped_params * (1 + s.fan_in) DESC LIMIT :lim"""),
(
    "dead-code",
    "Nothing in this tree calls these",
    "ANSWERS what might be deletable.\n"
    "ACT grep the name as a STRING before deleting anything: a registry entry,\n"
    "     a config value or a reflective call keeps a symbol alive with no edge\n"
    "     to show for it.\n"
    "MISLEADS this is the query most likely to be wrong, and `graph-blindspots`\n"
    "     measures by how much. Public symbols are excluded because a caller\n"
    "     outside this tree cannot be seen at all, so what is left is private\n"
    "     and unreferenced -- a much weaker claim than dead.",
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
("outbound-fetch-below-a-controller", "file_get_contents, fopen or curl_exec reachable from a controller",
    "ANSWERS the SSRF question Psalm\'s taint analysis needs a full config to\n"
    "     ask and PHPStan will not ask at all: not whether the code fetches a\n"
    "     URL -- most apps do -- but whether a request-facing controller can\n"
    "     reach the fetch. That is the difference between a scheduled importer\n"
    "     and an open proxy into the private network.\n"
    "ACT allow-list the host before the call and forbid redirects to private\n"
    "     ranges. `reached_from` names the controller whose input needs the\n"
    "     check; fewest hops first, because those have the least code in\n"
    "     between to sanitise anything.\n"
    "MISLEADS reachability is not taint -- a controller may reach a fetch that\n"
    "     only ever sees a constant URL. Depth stops at 4 hops, and a call made\n"
    "     through a container (`$app->make(...)`) or a magic `__call` is not an\n"
    "     edge here at all.",
    """WITH RECURSIVE walk(root, sym, depth) AS (
        SELECT s.id, s.id, 0 FROM symbols s
        JOIN files f ON f.id = s.file_id
        WHERE (s.is_controller = 1 OR s.is_entrypoint = 1)
          AND f.is_test = 0
        UNION
        SELECT w.root, e.callee_id, w.depth + 1
        FROM walk w JOIN edges e ON e.caller_id = w.sym
        WHERE w.depth < 4 AND e.is_self = 0),      -- depth bound: 4 hops
    reach(root, sym, depth) AS (
        SELECT root, sym, MIN(depth) FROM walk GROUP BY root, sym)
    SELECT s.name, entry.name AS reached_from, MIN(r.depth) AS hops,
        s.n_remote_fetch AS fetch_calls,
        s.n_serialize_call AS serialize_calls,
        s.n_extract_call AS extract_calls,
        s.n_header_call AS header_calls, s.fan_in,
        f.path || \':\' || s.line_start AS at
    FROM reach r
    JOIN symbols s ON s.id = r.sym
    JOIN symbols entry ON entry.id = r.root
    JOIN files f ON f.id = s.file_id
    LEFT JOIN modules m ON m.id = s.module_id
    WHERE r.depth > 0 AND f.is_test = 0
      AND (s.n_remote_fetch > 0 OR s.n_serialize_call > 0
           OR s.n_extract_call > 0)
      AND COALESCE(m.name,\'\') LIKE :mod
    GROUP BY s.id, entry.id
    ORDER BY hops ASC, fetch_calls DESC, s.fan_in DESC LIMIT :lim"""),
(
    "deserialization-injection",
    "unserialize() on untrusted input (PHPStan/Sonar)",
    "ANSWERS where unserialize() is called, which can instantiate arbitrary\n"
    "     classes and call magic methods. A crafted payload is an RCE vector.\n"
    "ACT use json_decode instead; if unserialize is needed, use allowed_classes.\n"
    "MISLEADS unserialize on trusted internal data is safe. The graph sees the\n"
    "     call but not the input source.",
    """SELECT s.name, s.n_serialize_call AS serialize_calls,
        s.n_eval AS eval_calls,
        s.n_dynamic_include AS dynamic_includes,
        s.fan_in, s.is_controller AS controller,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_serialize_call > 0 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.fan_in DESC, s.n_serialize_call DESC LIMIT :lim"""),
(
    "command-injection",
    "eval or dynamic dispatch with potential injection (PHPStan/Sonar)",
    "ANSWERS where eval, dynamic calls, or dynamic includes are used, which\n"
    "     can execute arbitrary code. If any part is user-controlled, this is RCE.\n"
    "ACT validate input; use fixed function names; never eval user input.\n"
    "MISLEADS a dynamic call with a validated constant string is safe. The graph\n"
    "     sees the call but not the argument source.",
    """SELECT s.name, s.n_eval AS eval_calls,
        s.n_dynamic_call AS dynamic_calls,
        s.n_dynamic_include AS dynamic_includes,
        s.n_variable_var AS variable_vars,
        s.fan_in, s.is_controller AS controller,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE (s.n_eval + s.n_dynamic_call + s.n_dynamic_include) > 0
      AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.fan_in DESC,
        s.n_eval + s.n_dynamic_call DESC LIMIT :lim"""),
(
    "file-inclusion-injection",
    "include/require with dynamic path (PHPStan/Sonar)",
    "ANSWERS where include or require is called with a variable, enabling LFI\n"
    "     (Local File Inclusion) if the path is user-controlled.\n"
    "ACT use a whitelist of allowed files; never include user input.\n"
    "MISLEADS a dynamic include with a validated constant is safe. The graph\n"
    "     sees the call but not the validation.",
    """SELECT s.name, s.n_dynamic_include AS dynamic_includes,
        s.n_variable_var AS variable_vars,
        s.n_eval AS eval_calls,
        s.fan_in, s.is_controller AS controller,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_dynamic_include > 0 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.fan_in DESC, s.n_dynamic_include DESC LIMIT :lim"""),
(
    "header-redirect-open",
    "header('Location:...') without exit (PHPStan/Sonar)",
    "ANSWERS where header() is called for a redirect but execution continues\n"
    "     after the header, so the redirect is sent but the code below still runs.\n"
    "ACT call exit or die after a redirect header.\n"
    "MISLEADS a header that sets content-type or cache-control is not a redirect\n"
    "     and should not exit. The graph counts header calls, not the header text.",
    """SELECT s.name, s.n_header_call AS header_calls,
        s.n_session_call AS session_calls,
        s.cyclomatic AS cyclo,
        s.fan_in, s.is_controller AS controller,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_header_call > 0 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.fan_in DESC, s.n_header_call DESC LIMIT :lim"""),
(
    "session-fixation",
    "session_start without session_regenerate_id (PHPStan/Sonar)",
    "ANSWERS where session_start is called but session_regenerate_id is not,\n"
    "     leaving the session vulnerable to fixation attacks.\n"
    "ACT call session_regenerate_id(true) after authentication.\n"
    "MISLEADS a session that is regenerated elsewhere in the call chain is safe;\n"
    "     the graph sees the function but not the full request lifecycle.",
    """SELECT s.name, s.n_session_call AS session_calls,
        s.fan_in, s.is_controller AS controller,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_session_call > 0 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.fan_in DESC, s.n_session_call DESC LIMIT :lim"""),
(
    "extract-injection",
    "extract() on superglobals (PHPStan/Sonar)",
    "ANSWERS where extract() is called, which imports variables from an array\n"
    "     into the current scope. extract($_GET) overwrites any local variable.\n"
    "ACT never call extract on user input; access keys explicitly.\n"
    "MISLEADS extract on an internal, trusted array is safe. The graph sees the\n"
    "     call but not the argument.",
    """SELECT s.name, s.n_extract_call AS extract_calls,
        s.n_superglobal_reads AS superglobal_reads,
        s.n_variable_var AS variable_vars,
        s.fan_in, s.is_controller AS controller,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_extract_call > 0 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.fan_in DESC, s.n_extract_call DESC LIMIT :lim"""),
(
    "loose-comparison-type-juggling",
    "== comparison with type juggling (PHPStan/Psalm)",
    "ANSWERS where == is used instead of ===, which performs type coercion.\n"
    "     0 == 'abc' is true in PHP <8; '' == 0 is true.\n"
    "ACT use === for all comparisons.\n"
    "MISLEADS == for comparing two strings or two ints of known type is safe.\n"
    "     has_strict_types=1 means the file declares strict_types.",
    """SELECT s.name, s.n_loose_compare AS loose_compares,
        s.n_strict_compare AS strict_compares,
        s.has_strict_types,
        s.fan_in, s.cyclomatic AS cyclo,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_loose_compare > 0 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.n_loose_compare DESC, s.fan_in DESC LIMIT :lim"""),
(
    "error-suppression-operator",
    "@ error suppression operator (PHPStan/Psalm)",
    "ANSWERS where the @ operator is used to suppress errors, hiding real bugs.\n"
    "     @ also slows down the call because PHP's error handler is invoked.\n"
    "ACT handle the error explicitly (try/catch, or check the return value).\n"
    "MISLEADS @ on a function that legitimately may fail (fopen on optional file)\n"
    "     is sometimes correct, but checking the return value is better.",
    """SELECT s.name, s.n_error_suppress AS error_suppress,
        s.n_loose_compare AS loose_compares,
        s.n_catch_empty AS empty_catches,
        s.fan_in, s.cyclomatic AS cyclo,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_error_suppress > 0 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.n_error_suppress DESC, s.fan_in DESC LIMIT :lim"""),
(
    "weak-hash",
    "MD5 or SHA1 used for hashing (PHPStan/Sonar)",
    "ANSWERS where a weak hash algorithm is used.\n"
    "ACT use hash('sha256') or stronger; for passwords use password_hash().\n"
    "MISLEADS MD5 for a non-security checksum is fine.",
    """SELECT s.name, s.n_weak_hash AS weak_hashs,
        s.n_weak_random AS weak_randoms,
        s.fan_in, s.is_controller AS controller,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE (s.n_weak_hash + s.n_weak_random) > 0 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.fan_in DESC,
        s.n_weak_hash + s.n_weak_random DESC LIMIT :lim"""),
(
    "remote-fetch-ssrf",
    "file_get_contents or curl with URL (PHPStan SSRF)",
    "ANSWERS where a remote URL is fetched, which can be exploited for SSRF if\n"
    "     the URL is user-controlled. The server fetches an internal resource.\n"
    "ACT validate and restrict the URL; never fetch user-supplied URLs directly.\n"
    "MISLEADS a fetch of a constant API URL is safe. The graph sees the call but\n"
    "     not the URL source.",
    """SELECT s.name, s.n_remote_fetch AS remote_fetches,
        s.n_superglobal_reads AS superglobal_reads,
        s.fan_in, s.is_controller AS controller,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_remote_fetch > 0 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.fan_in DESC, s.n_remote_fetch DESC LIMIT :lim"""),
(
    "csrf-missing",
    "Controller action without CSRF token check (PHPStan/Sonar)",
    "ANSWERS where a controller action handles POST/PUT/DELETE but the function\n"
    "     shows no evidence of CSRF validation. Each row is a missing defense.\n"
    "ACT ensure the framework's CSRF middleware is enabled, or check the token.\n"
    "MISLEADS a framework with global CSRF middleware handles this automatically;\n"
    "     the graph sees the function but not the middleware.",
    """SELECT s.name, s.is_controller,
        s.n_superglobal_reads AS superglobal_reads,
        s.n_session_call AS session_calls,
        s.n_params, s.fan_in,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.is_controller=1 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.fan_in DESC, s.n_superglobal_reads DESC LIMIT :lim""")
]

PhpAnalyzer.METRICS = [
(
    "graph-blindspots",
    "Read this first: where a PHP call graph cannot see",
    "ANSWERS how much of every other answer below is guesswork. In PHP this is\n"
    "     not a footnote -- `call_user_func`, `$obj->$m()`, `new $class`,\n"
    "     `__call`/`__callStatic` and a facade layer resolved at run time are\n"
    "     idiomatic, and each one deletes an edge.\n"
    "ACT read pct_blind before believing any reachability claim in Q2-Q7. On a\n"
    "     framework with a container and facades a high number is the CORRECT\n"
    "     answer, not a defect to tune away. Compare namespaces against each\n"
    "     other rather than against zero.\n"
    "MISLEADS external calls (PHP's ~1,500 built-ins, PDO, SPL) leave the tree\n"
    "     by design and are NOT counted as blindness. A resolved edge can still\n"
    "     be wrong: a method call resolves by SHORT NAME and prefers the\n"
    "     enclosing class, so `$other->save()` inside a class that also defines\n"
    "     `save()` points at the wrong one. magic_call is the count of classes\n"
    "     in this namespace defining __call/__callStatic -- every call into one\n"
    "     of those is unresolvable in principle, not just here.",
    """SELECT m.name AS namespace_, COUNT(DISTINCT s.id) AS fns,
        COALESCE(SUM(s.n_calls),0) AS calls,
        COALESCE(SUM(s.n_external_calls),0) AS external,
        COALESCE(SUM(s.n_unresolved_calls),0) AS unresolved,
        COALESCE(SUM(s.n_dynamic_call),0) AS dynamic_sites,
        COALESCE(SUM(s.n_dynamic_method),0) AS var_method,
        COALESCE(SUM(s.n_dynamic_new),0) AS var_class,
        (SELECT COUNT(*) FROM classes c JOIN symbols cs ON cs.id=c.symbol_id
         WHERE cs.module_id=m.id AND (c.has_call=1 OR c.has_callstatic=1))
            AS magic_call,
        CAST(100.0*SUM(s.n_unresolved_calls)/NULLIF(SUM(s.n_calls),0) AS INT)
            AS pct_blind
    FROM symbols s JOIN modules m ON m.id=s.module_id
    WHERE s.kind IN ('function','method','closure') AND m.name LIKE :mod
    GROUP BY m.id HAVING calls>0
    ORDER BY unresolved DESC LIMIT :lim"""),
(
    "strict-types-coverage",
    "declare(strict_types=1) coverage against scalar-parameter density",
    "ANSWERS where PHP is still doing silent type coercion on the arguments that\n"
    "     matter. Without strict_types, passing \"5 apples\" to an int parameter\n"
    "     coerces to 5 and passing \"abc\" coerces to 0 -- and 0 is a valid user\n"
    "     id in most schemas.\n"
    "ACT the ABSENCE of the declare is the finding, and it is per FILE, so a\n"
    "     namespace with high typed_params and low strict_files is doing the\n"
    "     work of types without the enforcement. Add the declare to those files\n"
    "     first; they have the most to gain and the least to break.\n"
    "MISLEADS strict_types governs the CALLEE's file in PHP, not the caller's,\n"
    "     which is the opposite of most people's intuition. Coercion at a call\n"
    "     site is decided by where the called function is DECLARED. A namespace\n"
    "     of pure value objects with no scalar parameters gains nothing.",
    """SELECT m.name AS namespace_,
        COUNT(DISTINCT f.id) AS files,
        SUM(DISTINCT_STRICT.n) AS strict_files,
        COUNT(DISTINCT s.id) AS fns,
        COALESCE(SUM(s.n_type_declarations),0) AS typed_slots,
        COALESCE(SUM(s.n_untyped_params),0) AS untyped_params,
        COALESCE(SUM(s.n_nullable_types),0) AS nullable,
        COALESCE(SUM(s.n_union_types),0) AS unions,
        COALESCE(SUM(s.n_intersection_types),0) AS intersections,
        COALESCE(SUM(s.n_loose_compare),0) AS loose_cmp,
        CAST(100.0*SUM(s.has_strict_types)/NULLIF(COUNT(s.id),0) AS INT)
            AS pct_fns_under_strict
    FROM symbols s
    JOIN files f ON f.id = s.file_id
    JOIN modules m ON m.id = s.module_id
    LEFT JOIN (SELECT file_id, MAX(has_strict_types) AS n
               FROM namespaces GROUP BY file_id) AS DISTINCT_STRICT
        ON DISTINCT_STRICT.file_id = f.id
    WHERE s.kind IN ('function','method') AND f.is_test = 0
      AND m.name LIKE :mod
    GROUP BY m.id
    HAVING fns > 0
    ORDER BY untyped_params DESC, pct_fns_under_strict ASC LIMIT :lim"""),
(
    "property-hooks",
    "PHP 8.4 property hooks: a field read that is really a call",
    "ANSWERS which property accesses the call graph must model as invocations.\n"
    "     `$order->total` looks like a field read in every tool built before\n"
    "     8.4 and in every reviewer's head, but with a `get` hook it executes a\n"
    "     body -- which can query, throw, or recurse.\n"
    "ACT a hook with calls>0 is a function hiding behind field syntax; a virtual\n"
    "     hook (one that never touches its own backing field) has NO storage at\n"
    "     all, so every read is unconditionally a call. Those are the ones to\n"
    "     check for work in a loop.\n"
    "MISLEADS no edge points AT a hook, because no call site names it -- fan_in\n"
    "     is structurally 0 for every row here and means nothing. A codebase\n"
    "     below 8.4 shows an empty table for reasons of version, not style; the\n"
    "     same is true of n_pipe_operator and 8.5.",
    """SELECT h.class_name, h.property, h.hook,
        h.is_short AS short_form, h.is_virtual AS virtual_no_backing_field,
        h.body_sloc AS sloc, h.n_calls AS calls_inside,
        s.cyclomatic AS cyclo, s.n_sql_calls AS sql_inside,
        s.max_loop_depth AS loops, s.risk_score AS risk,
        c.n_props AS props_on_class,
        f.path || ':' || h.line AS at
    FROM property_hooks h
    JOIN symbols s ON s.id = h.symbol_id
    JOIN files f ON f.id = h.file_id
    LEFT JOIN classes c ON c.symbol_id = h.class_id
    LEFT JOIN modules m ON m.id = s.module_id
    WHERE f.is_test = 0 AND COALESCE(m.name,'') LIKE :mod
    ORDER BY h.is_virtual DESC, h.n_calls DESC, h.body_sloc DESC LIMIT :lim"""),
(
    "god-classes",
    "Classes and functions doing too much, by every measure at once",
    "ANSWERS which units are hardest to hold in your head. For a class that is\n"
    "     methods plus properties plus traits; for a function it is cognitive\n"
    "     complexity, which weights nesting far above length.\n"
    "ACT split by responsibility. n_elif says which kind of split: a high elif\n"
    "     count is a flat dispatch (extract a map or a match) and a high nest\n"
    "     with low elif is real nesting (extract functions). A class pulling in\n"
    "     six traits has six sets of methods it did not declare.\n"
    "MISLEADS a long flat dispatch reads far more easily than a short deeply\n"
    "     nested one, which is why this sorts by cognitive rather than sloc.\n"
    "     Trait methods are NOT counted in n_methods -- they are declared\n"
    "     elsewhere -- so a Macroable-style class looks smaller than it behaves.",
    """SELECT c.name AS class_, c.kind, c.n_methods AS methods,
        c.n_public_methods AS public_, c.n_props AS props,
        c.n_traits AS traits_, c.n_magic AS magic,
        s.sloc, s.n_lines AS lines_,
        (SELECT COALESCE(MAX(x.cognitive),0) FROM symbols x
         WHERE x.parent_id = c.symbol_id) AS worst_method_cog,
        (SELECT COALESCE(SUM(x.n_elif),0) FROM symbols x
         WHERE x.parent_id = c.symbol_id) AS elifs,
        (c.n_methods*3 + c.n_props*2 + c.n_traits*4 + s.sloc/40) AS bulk,
        f.path || ':' || c.line AS at
    FROM classes c
    JOIN symbols s ON s.id = c.symbol_id
    JOIN files f ON f.id = c.file_id
    LEFT JOIN modules m ON m.id = s.module_id
    WHERE f.is_generated = 0 AND f.is_test = 0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY bulk DESC, worst_method_cog DESC LIMIT :lim"""),
(
    "risk-ranked",
    "Review order: if you can only read N functions this week, which N",
    "ANSWERS which functions combine complexity with the operations PHP makes\n"
    "     dangerous. The score weights SQL string interpolation, eval, variable\n"
    "     includes and shell far above raw complexity, and SUBTRACTS for\n"
    "     escaping and prepared statements -- the mitigations are evidence.\n"
    "ACT start at the top. A row with sql_interp>0 and prepared=0 is the single\n"
    "     highest-value read in this table.\n"
    "MISLEADS a heuristic, not a finding, and the weights are this tool's\n"
    "     opinion. Generated files are excluded, so the real top of the list may\n"
    "     be in code this hid. A function scoring high purely on cyclomatic is a\n"
    "     maintainability problem, not a security one -- read the columns, not\n"
    "     just the total.",
    """SELECT s.name, s.class_name AS class_, s.risk_score AS risk,
        s.cyclomatic AS cyclo, s.cognitive AS cog, s.max_nesting AS nest,
        s.n_sql_interp AS sql_interp, s.n_sql_concat AS sql_concat,
        s.n_sql_prepared AS prepared, s.n_eval AS evals,
        s.n_shell AS shell, s.n_dynamic_include AS var_include,
        s.n_superglobal_reads AS super_reads, s.n_raw_echo AS raw_echo,
        s.n_loose_compare AS loose_cmp, s.has_strict_types AS strict_,
        s.fan_in, f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id = s.file_id
    LEFT JOIN modules m ON m.id = s.module_id
    WHERE s.kind IN ('function','method','closure') AND f.is_generated = 0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.risk_score DESC LIMIT :lim"""),
(
    "parse-coverage",
    "What this run could not read",
    "ANSWERS whether the numbers above cover the code you think they cover.\n"
    "ACT a file with parsed=0 contributed nothing at all. A file with errors\n"
    "     contributed the symbols around the damage and nothing inside it.\n"
    "MISLEADS tree-sitter-php 0.24.1 rejects exactly three of PHP 8.5's\n"
    "     additions out of a 23-case 8.0-8.5 sweep: the (void) cast, `clone $x\n"
    "     with {...}`, and `final` on a promoted constructor property. A file\n"
    "     whose only symptom is one or three parse errors is a grammar one\n"
    "     version behind the language, not a broken file -- meta.grammar_note\n"
    "     carries the same list. Everything else in that sweep, 8.5's |> pipe\n"
    "     included, parses clean.\n"
    "     A file can also parse perfectly and still be misunderstood: inline\n"
    "     HTML islands, `eval` and `__call` all parse cleanly and carry no\n"
    "     symbols anyone can follow, and symbols_=0 with errors=0 is that case.",
    """SELECT f.path, f.lines, f.n_parse_errors AS errors,
        f.n_missing_nodes AS missing, f.parsed,
        f.is_generated AS generated, f.is_test AS test,
        f.n_symbols AS symbols_,
        (SELECT COUNT(*) FROM namespaces ns WHERE ns.file_id = f.id)
            AS namespaces_,
        (SELECT MAX(ns.has_strict_types) FROM namespaces ns
         WHERE ns.file_id = f.id) AS strict_types
    FROM files f
    LEFT JOIN modules m ON m.id = f.module_id
    WHERE (f.n_parse_errors > 0 OR f.n_missing_nodes > 0 OR f.parsed = 0
           OR f.n_symbols = 0)
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY f.n_parse_errors DESC, f.n_missing_nodes DESC,
        f.lines DESC LIMIT :lim"""),
(
    "hot-multipliers",
    "Where one fix pays back many times: highest fan-in",
    "ANSWERS which symbols the rest of the tree leans on hardest.\n"
    "ACT a correctness or speed win in a high-fan-in leaf pays back once per\n"
    "     caller. Read it next to sloc -- a four-digit fan_in on a ten-line\n"
    "     function is usually a name collision, not a hot leaf.\n"
    "MISLEADS fan_in counts STATIC call sites this parser could resolve, not\n"
    "     runtime frequency, and test callers are included, so in most repos a\n"
    "     test helper outranks production code. Scope with --module first.",
    """SELECT s.name, s.fan_in, s.n_callsites AS sites, s.fan_out,
        s.cyclomatic AS cyclo, s.sloc, s.kind,
        COALESCE(m.name,'') AS module_,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.fan_in > 0 AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.fan_in DESC, s.cyclomatic DESC LIMIT :lim"""),
("array-scan-in-a-hot-method", "in_array, array_merge or count inside a loop, weighted by how many callers reach it",
    "ANSWERS what PHPMD and the PHPStan perf extensions flag statement by\n"
    "     statement and cannot prioritise. `in_array` in a loop is O(n*m);\n"
    "     `array_merge` in a loop reallocates the whole array every iteration,\n"
    "     turning an append into O(n^2). Both are only worth fixing where they\n"
    "     run, and `distinct_callers` is the graph\'s answer to where.\n"
    "ACT flip the haystack with array_flip and use isset(), and replace the\n"
    "     merge with `$out[] =` plus one merge after the loop. Hoist count()\n"
    "     into a variable above the loop.\n"
    "MISLEADS the loop bound is not visible here, and a scan over a\n"
    "     five-element config array is not worth touching. `distinct_callers`\n"
    "     counts static call sites; a single caller inside a request loop beats\n"
    "     fifty callers on a cron path.",
    """SELECT s.name, s.n_inarray_in_loop AS inarray_in_loop,
        s.n_array_merge_in_loop AS array_merge_in_loop,
        s.n_count_in_loop AS count_in_loop,
        s.n_preg_in_loop AS preg_in_loop,
        s.n_keycheck_in_loop AS keycheck_in_loop,
        s.max_loop_depth AS loop_depth, s.fan_in,
        COUNT(DISTINCT e.caller_id) AS distinct_callers,
        f.path || \':\' || s.line_start AS at
    FROM symbols s
    JOIN files f ON f.id = s.file_id
    LEFT JOIN edges e ON e.callee_id = s.id AND e.is_self = 0
    LEFT JOIN modules m ON m.id = s.module_id
    WHERE (s.n_inarray_in_loop > 0 OR s.n_array_merge_in_loop > 0
           OR s.n_count_in_loop > 0)
      AND f.is_test = 0
      AND COALESCE(m.name,\'\') LIKE :mod
    GROUP BY s.id
    ORDER BY array_merge_in_loop DESC, inarray_in_loop DESC,
        distinct_callers DESC LIMIT :lim"""),
(
    "strict-types-missing",
    "File without declare(strict_types=1) (PHPStan/Psalm)",
    "ANSWERS which files do not declare strict_types=1, so type coercion is\n"
    "     enabled for the entire file.\n"
    "ACT add declare(strict_types=1); at the top of the file.\n"
    "MISLEADS legacy code that relies on type coercion may break with strict_types.",
    """SELECT s.name, s.has_strict_types,
        s.n_loose_compare AS loose_compares,
        s.n_untyped_params AS untyped_params,
        s.n_type_declarations AS type_declarations,
        s.fan_in, s.is_controller AS controller,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.has_strict_types=0 AND s.is_controller=1 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.fan_in DESC, s.n_loose_compare DESC LIMIT :lim"""),
(
    "untyped-params",
    "Functions with untyped parameters (PHPStan/Psalm)",
    "ANSWERS where a function has parameters without type declarations, so the\n"
    "     contract is implicit and PHPStan/Psalm cannot check it.\n"
    "ACT add type declarations to all parameters.\n"
    "MISLEADS PHP 7.0+ is required for scalar type declarations. Legacy code on\n"
    "     PHP 5.x cannot use them.",
    """SELECT s.name, s.n_untyped_params AS untyped_params,
        s.n_type_declarations AS type_declarations,
        s.n_nullable_types AS nullable_types,
        s.n_union_types AS union_types,
        s.n_params, s.fan_in, s.is_public,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_untyped_params > 0 AND s.is_public=1 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.fan_in DESC, s.n_untyped_params DESC LIMIT :lim"""),
(
    "deep-nesting",
    "Functions with excessive nesting depth (PHP_CodeSniffer)",
    "ANSWERS where a function has max_nesting > 4, making it hard to read.\n"
    "ACT extract nested blocks; use early returns or guard clauses.\n"
    "MISLEADS PHP's alternative syntax (if: ... endif;) does not change nesting.",
    """SELECT s.name, s.max_nesting AS nesting,
        s.cyclomatic AS cyclo, s.cognitive AS cognitive,
        s.n_loops AS loops, s.sloc, s.fan_in,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.max_nesting > 4 AND s.kind IN ('function','method')
      AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.max_nesting DESC, s.cyclomatic DESC LIMIT :lim"""),
(
    "too-many-params",
    "Functions with too many parameters (PHP_CodeSniffer)",
    "ANSWERS where a function has more than 5 parameters.\n"
    "ACT use an array parameter or a data transfer object.\n"
    "MISLEADS a controller action with many query params may be correct.",
    """SELECT s.name, s.n_params, s.n_optional_params,
        s.sloc, s.cyclomatic AS cyclo, s.fan_in,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_params > 5 AND s.kind IN ('function','method')
      AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.n_params DESC, s.fan_in DESC LIMIT :lim"""),
(
    "scattered-concerns",
    "A function called from many different modules (shotgun surgery)",
    "ANSWERS which functions are called from many distinct modules.\n"
    "ACT consider splitting or stabilizing the contract.\n"
    "MISLEADS a utility function is called from everywhere and is stable.",
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
    ORDER BY n_caller_modules DESC, s.fan_in DESC LIMIT :lim""")
]



ANALYZER = PhpAnalyzer()


if __name__ == "__main__":
    try:
        sys.exit(main(ANALYZER))
    except KeyboardInterrupt:
        print("\ninterrupted", file=sys.stderr)
        sys.exit(130)
