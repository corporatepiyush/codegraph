#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Piyush Katariya
#
# @author Piyush Katariya
"""codegraph_typescript.py -- parse a TypeScript tree into a graph and query it.

Targets TypeScript 7.0 (GA 2026-07-08).

This brings its own parser rather than driving `tsc`, and that is a deliberate
choice forced by the release: **TypeScript 7.0 ships with no programmatic API**
-- the stable one is targeted for 7.1, which is why Vue, Angular, Svelte and
webpack cannot use 7.0 yet. Anything that wanted to consume the compiler would
have to pin 5.9 or 6.0. tree-sitter has no such constraint.

TS 7 is a reimplementation (the Go port), not a new language, so the syntax is
essentially 5.x. What it REMOVES matters more than what it adds: `baseUrl`,
`moduleResolution: node10`, `module: amd|umd|system`, `target: es5`, and
`module X {}` as the namespace spelling. `erasableSyntaxOnly` additionally bans
enums, namespaces with runtime code, parameter properties and `import =`.

Two grammars, not one. `<T,>(x: T) => ...` is a generic arrow in `.ts` and a
JSX element in `.tsx`, and no parser can decide which from the text alone --
the file extension is the only disambiguator. This loads both and picks per
file, which is why `setup()` and `parse_file()` are overridden here.

What it looks for that a linter does not: `any` measured by BLAST RADIUS rather
than by count, because every caller of an `any`-returning function inherits the
hole; barrel-file re-export chains, which are a real and invisible build-time
cost; and suppressions sitting on high-fan-in symbols.

Usage:
  python3 codegraph_typescript.py /path/to/repo --report
  python3 codegraph_typescript.py /path/to/repo --list
  python3 codegraph_typescript.py --deps"""
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
        for i, (name, title, _, _) in enumerate(analyzer.QUERIES, 1):
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

    sel = a.which or range(1, len(analyzer.QUERIES) + 1)
    for k in sel:
        if not (1 <= k <= len(analyzer.QUERIES)):
            continue
        name, title, notes, sql = analyzer.QUERIES[k - 1]
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
        # -- facts typescript-eslint and the Node plugins check ------------
        _b = name.rsplit(".", 1)[-1]
        if _b in ("exec", "execSync", "spawnSync") and "child_process" in name:
            st.bump("n_child_process")
        if _b in ("readFileSync", "writeFileSync", "existsSync"):
            st.bump("n_fs_sync")
        if _b in ("push", "concat", "unshift") and loop_depth:
            st.bump("n_array_grow_in_loop")
        if _b in ("indexOf", "includes", "find") and loop_depth:
            st.bump("n_search_in_loop")
        if name in ("Math.random",):
            st.bump("n_math_random")
        if _b in ("parse",) and name.startswith("JSON") and loop_depth:
            st.bump("n_json_parse_in_loop")
        if name in ("process.exit",):
            st.bump("n_process_exit")
        if _b in ("then",) and loop_depth:
            st.bump("n_then_in_loop")
        if _b in ("assign",) and name.startswith("Object") and loop_depth:
            st.bump("n_assign_in_loop")
        if _b in ("dispose", "unsubscribe", "removeEventListener"):
            st.bump("n_dispose_call")     # vscode-style lifecycle pairing
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
# lang_typescript.py
# codegraph_typescript.py -- parse a TypeScript tree into a graph and query it.
#
# Targets TypeScript 7.0 (GA 2026-07-08).
#
# This brings its own parser rather than driving `tsc`, and that is a deliberate
# choice forced by the release: **TypeScript 7.0 ships with no programmatic API**
# -- the stable one is targeted for 7.1, which is why Vue, Angular, Svelte and
# webpack cannot use 7.0 yet. Anything that wanted to consume the compiler would
# have to pin 5.9 or 6.0. tree-sitter has no such constraint.
#
# TS 7 is a reimplementation (the Go port), not a new language, so the syntax is
# essentially 5.x. What it REMOVES matters more than what it adds: `baseUrl`,
# `moduleResolution: node10`, `module: amd|umd|system`, `target: es5`, and
# `module X {}` as the namespace spelling. `erasableSyntaxOnly` additionally bans
# enums, namespaces with runtime code, parameter properties and `import =`.
#
# Two grammars, not one. `<T,>(x: T) => ...` is a generic arrow in `.ts` and a
# JSX element in `.tsx`, and no parser can decide which from the text alone --
# the file extension is the only disambiguator. This loads both and picks per
# file, which is why `setup()` and `parse_file()` are overridden here.
#
# What it looks for that a linter does not: `any` measured by BLAST RADIUS rather
# than by count, because every caller of an `any`-returning function inherits the
# hole; barrel-file re-export chains, which are a real and invisible build-time
# cost; and suppressions sitting on high-fan-in symbols.
#
# Usage:
#   python3 codegraph_typescript.py /path/to/repo --report
#   python3 codegraph_typescript.py /path/to/repo --list
#   python3 codegraph_typescript.py --deps
# ==========================================================================

DEPS = DepSet(lang="typescript", deps=[
    TREE_SITTER,
    grammar("TypeScript", "tree_sitter_typescript",
            "tree-sitter-typescript>=0.23", "0.23.2 (ABI 14)"),
])

HAZARD_CATEGORIES = (
    "unsound", "suppress", "sync_block", "exec", "proto_pollution", "redos",
    "listener", "timer", "cache", "io", "net", "dom", "storage", "crypto",
    "reflect",
)

HAZARD_CALLS: dict[str, str] = {
    # blocking the event loop -- the *Sync family
    "readFileSync": "sync_block", "writeFileSync": "sync_block",
    "existsSync": "sync_block", "readdirSync": "sync_block",
    "statSync": "sync_block", "execSync": "sync_block",
    "spawnSync": "sync_block", "pbkdf2Sync": "sync_block",
    "scryptSync": "sync_block", "deflateSync": "sync_block",
    "gzipSync": "sync_block",
    # arbitrary code
    "eval": "exec", "Function": "exec", "vm.runInNewContext": "exec",
    "vm.runInThisContext": "exec", "child_process.exec": "exec",
    "child_process.execSync": "exec", "require": "exec",
    # prototype pollution -- CWE-1321
    "merge": "proto_pollution", "deepMerge": "proto_pollution",
    "defaultsDeep": "proto_pollution", "mergeWith": "proto_pollution",
    "extend": "proto_pollution", "set": "proto_pollution",
    "setWith": "proto_pollution", "Object.assign": "proto_pollution",
    # subscriptions that must be undone
    "addEventListener": "listener", "removeEventListener": "listener",
    "addListener": "listener", "removeListener": "listener",
    "on": "listener", "off": "listener", "once": "listener",
    "subscribe": "listener", "unsubscribe": "listener",
    "observe": "listener", "disconnect": "listener",
    "IntersectionObserver": "listener", "MutationObserver": "listener",
    "ResizeObserver": "listener", "AbortController": "listener",
    # timers
    "setTimeout": "timer", "setInterval": "timer", "clearTimeout": "timer",
    "clearInterval": "timer", "requestAnimationFrame": "timer",
    "cancelAnimationFrame": "timer", "setImmediate": "timer",
    # unbounded growth
    "Map": "cache", "Set": "cache", "WeakMap": "cache", "WeakSet": "cache",
    "WeakRef": "cache", "FinalizationRegistry": "cache",
    # io / net
    "readFile": "io", "writeFile": "io", "createReadStream": "io",
    "createWriteStream": "io", "pipeline": "io",
    "fetch": "net", "XMLHttpRequest": "net", "WebSocket": "net",
    "EventSource": "net", "axios": "net", "http.request": "net",
    "https.request": "net",
    # dom sinks
    "innerHTML": "dom", "outerHTML": "dom", "insertAdjacentHTML": "dom",
    "document.write": "dom", "dangerouslySetInnerHTML": "dom",
    "execCommand": "dom",
    "localStorage": "storage", "sessionStorage": "storage",
    "indexedDB": "storage",
    "Math.random": "crypto", "createHash": "crypto",
    # runtime reflection
    "Object.defineProperty": "reflect", "Proxy": "reflect",
    "Reflect.get": "reflect", "Reflect.set": "reflect",
    "Reflect.ownKeys": "reflect", "structuredClone": "reflect",
}

REDOS_RE = re.compile(r'\([^)]*[+*]\)[+*]|\[[^\]]*\][+*][+*]|\(\?:[^)]*[+*]\)[+*]')

SUPPRESS_RE = re.compile(
    r'@ts-(ignore|expect-error|nocheck)|eslint-disable(?:-next-line)?')

ANY_RE = re.compile(r'\bany\b')

STRICT_FLAGS = (
    "strict", "noImplicitAny", "strictNullChecks", "strictFunctionTypes",
    "strictBindCallApply", "strictPropertyInitialization",
    "noImplicitThis", "useUnknownInCatchVariables", "alwaysStrict",
    "noUncheckedIndexedAccess", "exactOptionalPropertyTypes",
    "noImplicitOverride", "noImplicitReturns", "noFallthroughCasesInSwitch",
    "verbatimModuleSyntax", "isolatedModules", "erasableSyntaxOnly",
)

BUILTIN_GLOBALS = frozenset("""
Array Object String Number Boolean Symbol BigInt Math JSON Date RegExp Error
TypeError RangeError SyntaxError Promise Map Set WeakMap WeakSet Proxy Reflect
console process Buffer globalThis window document navigator localStorage
setTimeout setInterval clearTimeout clearInterval queueMicrotask structuredClone
fetch URL URLSearchParams TextEncoder TextDecoder AbortController Intl
parseInt parseFloat isNaN isFinite encodeURIComponent decodeURIComponent
require module exports __dirname __filename Function eval undefined NaN Infinity
""".split())

class TypeScriptAnalyzer(TreeSitterAnalyzer):
    LANG = "typescript"
    TARGET = "TypeScript 7.0 (own parser; tsc has no public API before 7.1)"
    EXTS = (".ts", ".tsx", ".mts", ".cts", ".d.ts")
    SKIP_DIRS = {"node_modules", "dist", "lib", "out", "types", ".next"}
    DEPS = DEPS
    HAZARD_CATEGORIES = HAZARD_CATEGORIES
    MANIFESTS = ("tsconfig.json", "package.json", "tsconfig.base.json")

    GRAMMAR_MODULE = "tree_sitter_typescript"
    GRAMMAR_PIP = "tree-sitter-typescript>=0.23"
    GRAMMAR_SYMBOL = "language_typescript"

    FUNC_KINDS = {
        "function_declaration": "function",
        "function_expression": "function",
        "generator_function_declaration": "function",
        "arrow_function": "closure",
        "method_definition": "method",
        "method_signature": "method",
        "function_signature": "function",
        "abstract_method_signature": "method",
    }
    TYPE_KINDS = {
        "class_declaration": "class",
        "abstract_class_declaration": "class",
        "interface_declaration": "interface",
        "type_alias_declaration": "type",
        "enum_declaration": "enum",
        "internal_module": "module",
        "module": "module",
    }
    NAME_FIELD = {"arrow_function": "", "function_expression": ""}
    IDENT_NODES = ("identifier", "property_identifier", "type_identifier",
                   "private_property_identifier", "shorthand_property_identifier")

    BODY_FIELD = "body"
    PARAMS_FIELD = "parameters"
    RETURN_FIELD = "return_type"
    ELSE_FIELD = "alternative"
    IF_NODES = ("if_statement",)

    LOOP_NODES = ("for_statement", "for_in_statement", "while_statement",
                  "do_statement")
    BRANCH_NODES = ("if_statement",)
    #: The braced block is deliberately absent: every `if` and every
    #: loop owns one, so counting both charges two levels for one and
    #: reports depth as 2n+1.
    NEST_NODES = ("if_statement", "for_statement", "for_in_statement",
                  "while_statement", "do_statement", "switch_statement",
                  "try_statement", "arrow_function",
                  "function_expression", "class_body")
    CALL_NODES = ("call_expression", "new_expression")
    CALL_FUNC_FIELD = "function"
    COMMENT_NODES = ("comment",)
    STRING_NODES = ("string", "template_string")
    NUMBER_NODES = ("number",)
    OPERATOR_NODES = ("binary_expression", "unary_expression",
                      "assignment_expression", "augmented_assignment_expression",
                      "update_expression", "subscript_expression",
                      "member_expression", "ternary_expression",
                      "as_expression", "satisfies_expression",
                      "non_null_expression", "spread_element")

    COUNTERS = {
        "return_statement": "n_returns",
        "throw_statement": "n_throw",
        "try_statement": "n_try",
        "catch_clause": "n_catch",
        "finally_clause": "n_finally",
        "switch_statement": "n_switch",
        "switch_case": "n_cases",
        "ternary_expression": "n_ternary",
        "await_expression": "n_await",
        "yield_expression": "n_yield",
        "arrow_function": "n_lambda",
        "as_expression": "n_as_assertion",
        "satisfies_expression": "n_satisfies",
        "non_null_expression": "n_non_null",
        "type_assertion": "n_angle_assertion",
        "optional_chain": "n_optional_chain",
        "spread_element": "n_spread",
        "regex": "n_regex_lit",
        "type_parameters": "n_generic_params",
        "type_arguments": "n_type_args",
        "conditional_type": "n_conditional_type",
        "mapped_type_clause": "n_mapped_type",
        "template_literal_type": "n_template_type",
        "index_signature": "n_index_signature",
        "union_type": "n_union_type",
        "intersection_type": "n_intersection_type",
        "object_pattern": "n_destructure",
        "class_static_block": "n_static_block",
        "decorator": "n_decorators",
        "labeled_statement": "n_labels",
    }
    LOOP_CALL_COUNTERS = {
        "addEventListener": "listener_in_loop",
        "setTimeout": "timer_in_loop",
        "setInterval": "timer_in_loop",
        "JSON.parse": "parse_in_loop",
        "querySelector": "dom_in_loop",
        "querySelectorAll": "dom_in_loop",
    }

    EXTRA_SYMBOL_COLS = (
        #: `<const T>` (TS 5.0). It changes inference for the whole
        #: signature -- literal types survive instead of widening -- so
        #: every call site reads differently.
        ("n_const_type_params", "INT NOT NULL DEFAULT 0"),
        ("n_any_params", "INT NOT NULL DEFAULT 0"),
        ("n_any_total", "INT NOT NULL DEFAULT 0"),
        ("returns_any", "INT NOT NULL DEFAULT 0"),
        ("n_unknown_type", "INT NOT NULL DEFAULT 0"),
        ("n_as_assertion", "INT NOT NULL DEFAULT 0"),
        ("n_as_any", "INT NOT NULL DEFAULT 0"),
        ("n_angle_assertion", "INT NOT NULL DEFAULT 0"),
        ("n_non_null", "INT NOT NULL DEFAULT 0"),
        ("n_satisfies", "INT NOT NULL DEFAULT 0"),
        ("n_suppressions", "INT NOT NULL DEFAULT 0"),
        ("n_ts_ignore", "INT NOT NULL DEFAULT 0"),
        ("n_ts_expect_error", "INT NOT NULL DEFAULT 0"),
        ("n_eslint_disable", "INT NOT NULL DEFAULT 0"),
        ("n_type_args", "INT NOT NULL DEFAULT 0"),
        ("n_conditional_type", "INT NOT NULL DEFAULT 0"),
        ("n_mapped_type", "INT NOT NULL DEFAULT 0"),
        ("n_template_type", "INT NOT NULL DEFAULT 0"),
        ("n_index_signature", "INT NOT NULL DEFAULT 0"),
        ("n_conditional_depth", "INT NOT NULL DEFAULT 0"),
        ("n_infer", "INT NOT NULL DEFAULT 0"),
        ("n_call_sig", "INT NOT NULL DEFAULT 0"),
        ("n_prop_sig", "INT NOT NULL DEFAULT 0"),
        ("n_keyof", "INT NOT NULL DEFAULT 0"),
        ("n_typeof_type", "INT NOT NULL DEFAULT 0"),
        ("n_union_type", "INT NOT NULL DEFAULT 0"),
        ("n_union_members", "INT NOT NULL DEFAULT 0"),
        ("n_intersection_type", "INT NOT NULL DEFAULT 0"),
        ("max_type_depth", "INT NOT NULL DEFAULT 0"),
        ("n_await", "INT NOT NULL DEFAULT 0"),
        ("n_yield", "INT NOT NULL DEFAULT 0"),
        ("n_optional_chain", "INT NOT NULL DEFAULT 0"),
        ("n_spread", "INT NOT NULL DEFAULT 0"),
        ("n_destructure", "INT NOT NULL DEFAULT 0"),
        ("n_static_block", "INT NOT NULL DEFAULT 0"),
        ("n_decorators", "INT NOT NULL DEFAULT 0"),
        ("n_this_refs", "INT NOT NULL DEFAULT 0"),
        ("n_computed_member", "INT NOT NULL DEFAULT 0"),
        ("n_promise_all", "INT NOT NULL DEFAULT 0"),
        ("n_then_chain", "INT NOT NULL DEFAULT 0"),
        ("n_floating_promise", "INT NOT NULL DEFAULT 0"),
        ("n_listener_add", "INT NOT NULL DEFAULT 0"),
        ("n_listener_remove", "INT NOT NULL DEFAULT 0"),
        ("n_timer_set", "INT NOT NULL DEFAULT 0"),
        ("n_timer_clear", "INT NOT NULL DEFAULT 0"),
        ("n_regex_redos", "INT NOT NULL DEFAULT 0"),
        ("n_json_parse", "INT NOT NULL DEFAULT 0"),
        ("n_innerhtml", "INT NOT NULL DEFAULT 0"),
        ("n_proto_write", "INT NOT NULL DEFAULT 0"),
        ("listener_in_loop", "INT NOT NULL DEFAULT 0"),
        ("timer_in_loop", "INT NOT NULL DEFAULT 0"),
        ("parse_in_loop", "INT NOT NULL DEFAULT 0"),
        ("dom_in_loop", "INT NOT NULL DEFAULT 0"),
        ("n_child_process", "INT NOT NULL DEFAULT 0"),
    ("n_fs_sync", "INT NOT NULL DEFAULT 0"),
    ("n_array_grow_in_loop", "INT NOT NULL DEFAULT 0"),
    ("n_search_in_loop", "INT NOT NULL DEFAULT 0"),
    ("n_math_random", "INT NOT NULL DEFAULT 0"),
    ("n_json_parse_in_loop", "INT NOT NULL DEFAULT 0"),
    ("n_process_exit", "INT NOT NULL DEFAULT 0"),
    ("n_then_in_loop", "INT NOT NULL DEFAULT 0"),
    ("n_assign_in_loop", "INT NOT NULL DEFAULT 0"),
    ("n_dispose_call", "INT NOT NULL DEFAULT 0"),
    ("n_elif", "INT NOT NULL DEFAULT 0"),
        ("n_external_calls", "INT NOT NULL DEFAULT 0"),
        ("is_declaration_only", "INT NOT NULL DEFAULT 0"),
        ("is_component", "INT NOT NULL DEFAULT 0"),
        ("is_hook", "INT NOT NULL DEFAULT 0"),
        ("is_handler", "INT NOT NULL DEFAULT 0"),
    )

    SCHEMA_EXT = r"""
CREATE TABLE ts_exports(
    id INTEGER PRIMARY KEY,
    file_id INT NOT NULL REFERENCES files(id),
    name TEXT NOT NULL,
    kind TEXT NOT NULL DEFAULT 'named',
    line INT NOT NULL,
    is_default INT NOT NULL DEFAULT 0,
    is_reexport INT NOT NULL DEFAULT 0,
    is_star INT NOT NULL DEFAULT 0,
    is_type_only INT NOT NULL DEFAULT 0,
    source TEXT
) STRICT;

CREATE TABLE suppressions(
    id INTEGER PRIMARY KEY,
    file_id INT NOT NULL REFERENCES files(id),
    symbol_id INT REFERENCES symbols(id),
    kind TEXT NOT NULL,
    line INT NOT NULL,
    reason TEXT
) STRICT;

CREATE TABLE tsconfigs(
    id INTEGER PRIMARY KEY,
    path TEXT NOT NULL,
    dir TEXT NOT NULL,
    extends TEXT,
    strict INT NOT NULL DEFAULT 0,
    no_implicit_any INT NOT NULL DEFAULT 0,
    strict_null_checks INT NOT NULL DEFAULT 0,
    no_unchecked_indexed_access INT NOT NULL DEFAULT 0,
    exact_optional INT NOT NULL DEFAULT 0,
    verbatim_module_syntax INT NOT NULL DEFAULT 0,
    isolated_modules INT NOT NULL DEFAULT 0,
    erasable_syntax_only INT NOT NULL DEFAULT 0,
    n_strict_flags INT NOT NULL DEFAULT 0,
    target TEXT,
    module TEXT,
    module_resolution TEXT,
    removed_option TEXT
) STRICT;

CREATE TABLE type_defs(
    symbol_id INT NOT NULL PRIMARY KEY REFERENCES symbols(id),
    n_members INT NOT NULL DEFAULT 0,
    n_optional_members INT NOT NULL DEFAULT 0,
    n_readonly_members INT NOT NULL DEFAULT 0,
    n_index_signatures INT NOT NULL DEFAULT 0,
    n_call_signatures INT NOT NULL DEFAULT 0,
    n_extends INT NOT NULL DEFAULT 0,
    extends_names TEXT NOT NULL DEFAULT '',
    n_any_members INT NOT NULL DEFAULT 0,
    is_exported INT NOT NULL DEFAULT 0,
    is_ambient INT NOT NULL DEFAULT 0,
    is_const_enum INT NOT NULL DEFAULT 0
) WITHOUT ROWID, STRICT;

CREATE TABLE listeners(
    id INTEGER PRIMARY KEY,
    symbol_id INT NOT NULL REFERENCES symbols(id),
    file_id INT NOT NULL REFERENCES files(id),
    op TEXT NOT NULL,
    target TEXT NOT NULL DEFAULT '',
    event TEXT NOT NULL DEFAULT '',
    line INT NOT NULL,
    in_loop INT NOT NULL DEFAULT 0
) STRICT;
"""

    INDEX_EXT = r"""
CREATE INDEX idx_exp_file ON ts_exports(file_id, name);
CREATE INDEX idx_exp_star ON ts_exports(file_id) WHERE is_star=1;
CREATE INDEX idx_sup_kind ON suppressions(kind, file_id);
CREATE INDEX idx_sup_sym ON suppressions(symbol_id);
CREATE INDEX idx_td_any ON type_defs(n_any_members DESC) WHERE n_any_members>0;
CREATE INDEX idx_lis_op ON listeners(op, symbol_id);
CREATE INDEX idx_fn_any ON symbols(n_any_total DESC, name, file_id)
    WHERE n_any_total>0;
CREATE INDEX idx_fn_retany ON symbols(fan_in DESC, name) WHERE returns_any=1;
CREATE INDEX idx_fn_sup ON symbols(n_suppressions DESC, name)
    WHERE n_suppressions>0;
"""

    VIEW_EXT = r"""
CREATE VIEW v_any AS
SELECT s.id, s.name, s.qual_name, f.path, m.name AS module,
    s.n_any_params, s.returns_any, s.n_any_total,
    s.n_as_any, s.n_non_null, s.fan_in, s.is_exported,
    f.path || ':' || s.line_start AS at
FROM symbols s JOIN files f ON f.id=s.file_id
LEFT JOIN modules m ON m.id=s.module_id
WHERE s.n_any_total > 0 OR s.returns_any = 1;

CREATE VIEW v_barrel AS
SELECT f.id AS file_id, f.path,
    COUNT(*) AS star_exports,
    GROUP_CONCAT(e.source) AS sources
FROM ts_exports e JOIN files f ON f.id=e.file_id
WHERE e.is_star=1
GROUP BY f.id;
"""

    MATERIALIZE_EXT = r"""
UPDATE symbols AS s SET n_unique_calls = x.c FROM
    (SELECT caller_id AS id, COUNT(*) AS c FROM edges GROUP BY caller_id) AS x
    WHERE x.id = s.id;

UPDATE symbols AS s SET n_suppressions = x.c FROM
    (SELECT symbol_id AS id, COUNT(*) AS c FROM suppressions
     WHERE symbol_id IS NOT NULL GROUP BY symbol_id) AS x WHERE x.id = s.id;

UPDATE symbols AS s SET n_listener_add = x.a, n_listener_remove = x.r FROM
    (SELECT symbol_id AS id,
        SUM(op='add') AS a, SUM(op='remove') AS r
     FROM listeners GROUP BY symbol_id) AS x WHERE x.id = s.id;
"""

    RISK_SQL = (
        "cyclomatic*2 + cognitive + max_nesting*4"
        " + n_any_total*3 + returns_any*10 + n_as_any*8"
        " + n_non_null*2 + n_ts_ignore*12 + n_ts_expect_error*4"
        " + n_exec*30 + n_proto_pollution*20 + n_dom*10"
        " + n_sync_block*12 + n_regex_redos*15"
        " + n_crypto*6 + n_reflect*3"
        " + await_in_loop*8 + n_floating_promise*6"
        " + (CASE WHEN n_listener_add > n_listener_remove THEN 12 ELSE 0 END)"
        " + (CASE WHEN is_recursive THEN 10 ELSE 0 END)"
    )

    def __init__(self) -> None:
        super().__init__()
        self.tsx: Optional[ParserHandle] = None
        self.n_tsx_files = 0
        #: file_id -> {imported name: came from a bare package specifier}
        self._imported: dict[int, dict[str, bool]] = {}

    # -- two grammars, chosen by extension --------------------------------
    def setup(self) -> ParserHandle:
        """`.ts` and `.tsx` are different languages to the parser.

        `const f = <T,>(x: T) => x` is a generic arrow function in `.ts` and an
        unclosed JSX element in `.tsx`. Nothing in the text distinguishes them;
        the extension is the entire signal. Loading one grammar and using it
        for both produces a wall of ERROR nodes in whichever half loses.
        """
        self.check_metric_columns()
        h = load(self.LANG, self.GRAMMAR_MODULE, self.GRAMMAR_PIP,
                 "language_typescript")
        if not h.ok:
            # This override is why the base's refusal did not apply here, and
            # for one commit TypeScript was the only analyzer still printing
            # "REGEX FALLBACK ... approximate" over a graph with no symbols in
            # it -- a live instance of the bug that commit set out to remove.
            raise SystemExit(
                "codegraph-typescript cannot parse without a grammar: %s\n"
                "\n"
                "  %s -m pip install 'tree-sitter>=0.26,<0.27' "
                "tree-sitter-typescript\n"
                "\n"
                "or:  %s --install-deps\n"
                "\n"
                "There is no regex fallback. Producing an empty graph would "
                "look\nidentical to analysing a repository with nothing in it."
                % (h.note, sys.executable,
                   os.path.basename(sys.argv[0] or "codegraph_typescript.py")))
        if h.ok:
            self.tsx = load("tsx", self.GRAMMAR_MODULE, self.GRAMMAR_PIP,
                            "language_tsx")
            if self.tsx.ok:
                h.note = "+ tsx grammar for .tsx files"
        return h

    def parse_file(self, rec: FileRec, db: sqlite3.Connection,
                   bufs: Buffers) -> None:
        use_tsx = rec.rel.endswith(".tsx")
        handle = self.tsx if (use_tsx and self.tsx is not None
                              and self.tsx.ok) else self.parser
        if not handle.ok:
            self.parse_file_fallback(rec, db, bufs)
            return
        if use_tsx:
            self.n_tsx_files += 1
        tree = handle.parse(rec.data)
        root = tree.root_node
        if root.has_error:
            errs, missing = count_errors(root)
            db.execute("UPDATE files SET n_parse_errors=?, n_missing_nodes=? "
                       "WHERE id=?", (errs, missing, rec.fid))
        self.parse_imports(root, rec, bufs)
        self.walk_scope(root, rec, db, bufs, Scope())
        # Reimplementing parse_file for the dual grammar means every step the
        # base performs has to be repeated here. Omitting this one cost 5,675
        # of type-fest's 5,761 calls: `expectType<Foo>(bar)` is a top-level
        # statement, and top-level statements belong to no function.
        self.emit_module_scope(root, rec, db, bufs)
        self.parse_file_extra(root, rec, db, bufs)

    # -- symbol detail -----------------------------------------------------

    def node_name(self, node: Any, rec: FileRec) -> str:
        """What to call a function that carries no name of its own.

        Most modern TypeScript is `const f = (x: T) => ...`: the function node
        has no identifier and the name lives on the declarator, the object key,
        the class field or the `export default`. The inherited fallback --
        search the children for an identifier -- finds the single bare
        PARAMETER and names the function after it, which is worse than leaving
        it anonymous because the name looks real. That cost 42% of call-site
        resolution against the identical JavaScript corpus.
        """
        if node.type in ("arrow_function", "function_expression"):
            cur = node.parent
            hops = 0
            while cur is not None and hops < 4:
                if cur.type in ("variable_declarator", "public_field_definition",
                                "field_definition", "pair", "property_signature",
                                "assignment_expression"):
                    for field in ("name", "left", "key"):
                        got = cur.child_by_field_name(field)
                        if got is not None:
                            return _txt(got, rec.data).strip().strip('"\'`')
                if cur.type == "export_statement":
                    return "default"
                cur = cur.parent
                hops += 1
            return ""
        return super().node_name(node, rec)

    def visibility_of(self, node: Any, rec: FileRec) -> str:
        for c in node.children:
            if c.type == "accessibility_modifier":
                return _txt(c, rec.data)
        name = self.node_name(node, rec)
        if name.startswith("#") or name.startswith("_"):
            return "private"
        return "public" if self._is_exported(node) else ""

    def _is_exported(self, node: Any) -> bool:
        p = node.parent
        while p is not None and p.type in ("variable_declarator",
                                           "lexical_declaration",
                                           "variable_declaration",
                                           "expression_statement"):
            p = p.parent
        return p is not None and p.type == "export_statement"

    def function_flags(self, node: Any, rec: FileRec,
                       scope: Scope) -> dict[str, Any]:
        src = rec.data
        # `<const T>` lives in the SIGNATURE, and `measure` walks the body,
        # so a per-node counter there never sees one.
        tps = node.child_by_field_name("type_parameters")
        n_const_tp = 0
        if tps is not None:
            for tp in tps.named_children:
                if tp.type == "type_parameter" and \
                        src[tp.start_byte:tp.start_byte + 6] == b"const ":
                    n_const_tp += 1
        name = self.node_name(node, rec)
        sig = self.signature_of(node, rec)
        params = node.child_by_field_name("parameters")
        ptxt = _txt(params, src) if params is not None else ""
        ret = node.child_by_field_name("return_type")
        rtxt = _txt(ret, src) if ret is not None else ""
        body = node.child_by_field_name("body")
        exported = self._is_exported(node)
        # A React component is a capitalised function returning JSX; a hook is
        # `use*`. Neither is a language feature, but both change what a
        # fan-in number means, so they are worth flagging.
        btxt = _txt(body, src)[:600] if body is not None else ""
        return dict(
            n_const_type_params=n_const_tp,
            is_public=1 if exported or not name.startswith(("_", "#")) else 0,
            is_exported=int(exported),
            is_async=1 if "async" in sig[:40] else 0,
            is_generator=1 if "*" in sig[:40] else 0,
            is_abstract=1 if node.type == "abstract_method_signature"
                             or "abstract" in sig[:40] else 0,
            is_declaration_only=1 if body is None else 0,
            is_test=1 if name.startswith(("test", "it", "describe")) else 0,
            is_hook=1 if name.startswith("use") and len(name) > 3
                         and name[3].isupper() else 0,
            is_component=1 if (name[:1].isupper()
                               and ("<" in btxt or "jsx" in btxt.lower())) else 0,
            is_handler=1 if re.search(r'\b(req|request|ctx|event)\b', ptxt)
                            and re.search(r'\b(res|response|reply)\b', ptxt) else 0,
            n_any_params=len(ANY_RE.findall(ptxt)),
            returns_any=1 if ANY_RE.search(rtxt) else 0,
            n_any_total=len(ANY_RE.findall(sig)),
            n_unknown_type=sig.count("unknown"),
            max_type_depth=_type_depth(sig),
        )

    def type_flags(self, node: Any, rec: FileRec,
                   scope: Scope) -> dict[str, Any]:
        """Measure the type declaration itself, not just its header.

        The base only runs its counting pass over FUNCTION bodies, which is
        right for every other language here. In TypeScript it is wrong: a
        library like type-fest is 90% type declarations and 10% executable
        code, so counting only functions reports zero conditional types for a
        repo that is made of them. Type-level code IS the code.
        """
        src = rec.data
        txt = _txt(node, src)
        counts: dict[str, int] = {}
        depth = 0
        max_depth = 0
        cursor = node.walk()
        while True:
            n = cursor.node
            t = n.type
            key = _TYPE_COUNTERS.get(t)
            if key is not None:
                counts[key] = counts.get(key, 0) + 1
            if t == "conditional_type":
                depth += 1
                max_depth = max(max_depth, depth)
            elif t == "union_type":
                counts["n_union_members"] = counts.get("n_union_members", 0) \
                    + max(0, len(n.named_children) - 1)
            elif t == "predefined_type" and _txt(n, src) == "any":
                counts["n_any_total"] = counts.get("n_any_total", 0) + 1
            if cursor.goto_first_child():
                continue
            while not cursor.goto_next_sibling():
                if not cursor.goto_parent():
                    counts.update(
                        is_public=int(self._is_exported(node)),
                        is_exported=int(self._is_exported(node)),
                        is_abstract=int(
                            node.type == "abstract_class_declaration"),
                        max_type_depth=max(_type_depth(txt[:4000]), max_depth),
                        n_conditional_depth=max_depth,
                    )
                    return counts
                if cursor.node.type == "conditional_type":
                    depth = max(0, depth - 1)

    def on_node(self, node: Any, src: bytes, st: BodyStats,
                loop_depth: int, nest: int) -> None:
        t = node.type
        if t == "binary_expression":
            # TypeScript is a superset of JavaScript and the JS analyzer counts
            # these; this one did not, so `n_logical` was 0 across all 309,239
            # symbols of vscode while the JS analyzer found 10,004 in webpack.
            # `&&`/`||`/`??` are decision points and belong in cyclomatic.
            op = node.child_by_field_name("operator")
            o = _txt(op, src) if op is not None else ""
            if o in ("&&", "||"):
                st.bump("n_logical")
                st.cyclomatic += 1
            elif o == "??":
                st.bump("n_logical")
                st.cyclomatic += 1
            elif o in ("==", "!=", "===", "!==", "<", ">", "<=", ">="):
                st.bump("n_cmp")
            elif o in ("&", "|", "^"):
                st.bump("n_bitop")
            elif o in ("<<", ">>", ">>>"):
                st.bump("n_shift")
            elif o in ("+", "-", "*", "/", "%", "**"):
                st.bump("n_arith")
        elif t == "as_expression":
            if ANY_RE.search(_txt(node, src)[-24:]):
                st.bump("n_as_any")
        elif t == "await_expression":
            if loop_depth:
                st.bump("await_in_loop")
        elif t == "this":
            st.bump("n_this_refs")
        elif t == "subscript_expression":
            idx = node.child_by_field_name("index")
            if idx is not None and idx.type not in ("number", "string"):
                st.bump("n_computed_member")
        elif t == "union_type":
            st.bump("n_union_members", max(0, len(node.named_children) - 1))
        elif t == "comment":
            txt = _txt(node, src)
            m = SUPPRESS_RE.search(txt)
            if m:
                st.bump("n_suppressions")
                g = m.group(0)
                if "ts-ignore" in g:
                    st.bump("n_ts_ignore")
                elif "ts-expect-error" in g:
                    st.bump("n_ts_expect_error")
                elif "eslint-disable" in g:
                    st.bump("n_eslint_disable")
        elif t == "regex":
            if REDOS_RE.search(_txt(node, src)):
                st.bump("n_regex_redos")
        elif t == "member_expression":
            prop = node.child_by_field_name("property")
            if prop is not None:
                p = _txt(prop, src)
                if p in ("innerHTML", "outerHTML"):
                    st.bump("n_innerhtml")
                elif p in ("__proto__", "constructor", "prototype"):
                    st.bump("n_proto_write")
        elif t == "call_expression":
            fn = node.child_by_field_name("function")
            if fn is None:
                return
            name = _txt(fn, src)
            base = name.rsplit(".", 1)[-1]
            if name in ("JSON.parse",):
                st.bump("n_json_parse")
            elif base in ("all", "allSettled", "race") and "Promise" in name:
                st.bump("n_promise_all")
            elif base == "then":
                st.bump("n_then_chain")
            elif base in ("addEventListener", "addListener", "on", "subscribe",
                          "observe", "once"):
                st.bump("n_listener_add")
            elif base in ("removeEventListener", "removeListener", "off",
                          "unsubscribe", "disconnect"):
                st.bump("n_listener_remove")
            elif base in ("setTimeout", "setInterval", "setImmediate",
                          "requestAnimationFrame"):
                st.bump("n_timer_set")
            elif base in ("clearTimeout", "clearInterval",
                          "cancelAnimationFrame"):
                st.bump("n_timer_clear")
            # A promise-returning call whose result is thrown away is a
            # floating promise: its rejection becomes an unhandled rejection
            # and, since Node 15, kills the process.
            parent = node.parent
            if parent is not None and parent.type == "expression_statement" \
                    and base in ("then", "catch", "finally"):
                st.bump("n_floating_promise")

    def on_string(self, node: Any, text: str, src: bytes, st: BodyStats,
                  loop_depth: int) -> None:
        pass

    def hazard_of(self, callee: str) -> Optional[tuple[str, str]]:
        cat = HAZARD_CALLS.get(callee)
        if cat is not None:
            return callee, cat
        base = callee.rsplit(".", 1)[-1]
        cat = HAZARD_CALLS.get(base)
        if cat is not None:
            return "*." + base, cat
        return None

    def is_external(self, name: str, base: str, fid: int) -> bool:
        """A name from a package left the tree by design.

        Without this every `expectType` from `tsd` and every lodash helper
        counts as a call this tool could not follow, and a normal repository
        reports itself 90%+ blind -- which makes the honesty column useless
        precisely when someone needs it.
        """
        head = name.split(".")[0]
        if head in BUILTIN_GLOBALS or (base in BUILTIN_GLOBALS
                                       and "." not in name):
            return True
        imported = self._imported.get(fid)
        if imported is not None:
            # A bare specifier is a package; a relative one is in this tree and
            # failing to resolve it IS blindness worth reporting.
            for key in (head, base):
                bare = imported.get(key)
                if bare:
                    return True
        return False

    def _note_import(self, rec: FileRec, name: str, source: str) -> None:
        """Remember that `name` came from `source`, for `is_external`."""
        if not name:
            return
        bare = not source.startswith((".", "/"))
        self._imported.setdefault(rec.fid, {})[name.strip()] = bare


    # -- extra tables ------------------------------------------------------
    def function_extra(self, node: Any, rec: FileRec, db: sqlite3.Connection,
                       bufs: Buffers, sid: int, scope: Scope,
                       stats: BodyStats) -> None:
        body = node.child_by_field_name(self.BODY_FIELD)
        if body is None:
            return
        src = rec.data
        loops = set(self.LOOP_NODES)
        for n in walk(body):
            if n.type != "call_expression":
                continue
            fn = n.child_by_field_name("function")
            if fn is None:
                continue
            nm = _txt(fn, src)
            base = nm.rsplit(".", 1)[-1]
            op = ""
            if base in ("addEventListener", "addListener", "on", "subscribe",
                        "observe", "once"):
                op = "add"
            elif base in ("removeEventListener", "removeListener", "off",
                          "unsubscribe", "disconnect"):
                op = "remove"
            if not op:
                continue
            args = n.child_by_field_name("arguments")
            ev = ""
            if args is not None and args.named_children:
                ev = _txt(args.named_children[0], src).strip('"\'`')[:60]
            bufs.rows("listeners").append(
                (sid, rec.fid, op, nm.rsplit(".", 1)[0][:80], ev,
                 n.start_point[0] + 1,
                 int(_in_loop(n, body, loops))))

    def type_extra(self, node: Any, rec: FileRec, db: sqlite3.Connection,
                   bufs: Buffers, sid: int, scope: Scope) -> None:
        src = rec.data
        txt = _txt(node, src)
        body = node.child_by_field_name("body")
        members = list(body.named_children) if body is not None else []
        heritage = [c for c in node.children
                    if c.type in ("extends_clause", "class_heritage",
                                  "extends_type_clause", "implements_clause")]
        ext_names = ",".join(_txt(h, src).replace("extends", "")
                             .replace("implements", "").strip()
                             for h in heritage)[:300]
        n_opt = n_ro = n_idx = n_call = n_any = 0
        for i, mem in enumerate(members):
            mtxt = _txt(mem, src)
            if "?" in mtxt.split(":")[0]:
                n_opt += 1
            if mtxt.lstrip().startswith("readonly"):
                n_ro += 1
            if mem.type == "index_signature":
                n_idx += 1
            if mem.type in ("call_signature", "construct_signature"):
                n_call += 1
            if ANY_RE.search(mtxt):
                n_any += 1
            mname = self.node_name(mem, rec) or mtxt.split(":")[0].strip()[:80]
            mtype = ""
            ta = mem.child_by_field_name("type")
            if ta is not None:
                mtype = _txt(ta, src).lstrip(": ")
            bufs.fields.append(
                (sid, i, mname[:120], mtype[:200], "",
                 mem.start_point[0] + 1, 0, int("readonly" in mtxt[:20]), 0,
                 int("?" in mtxt.split(":")[0] or "null" in mtype
                     or "undefined" in mtype),
                 int(mtype.startswith(("Array", "Map", "Set", "Record"))
                     or mtype.endswith("[]")),
                 int(not mtype), 0, _type_depth(mtype)))
        bufs.rows("type_defs").append(
            (sid, len(members), n_opt, n_ro, n_idx, n_call,
             len(heritage), ext_names, n_any,
             int(self._is_exported(node)),
             int("declare" in txt[:40]),
             int("const enum" in txt[:40])))
        if node.type == "enum_declaration" and body is not None:
            for i, mem in enumerate(body.named_children):
                mtxt = _txt(mem, src)
                nm, _, val = mtxt.partition("=")
                bufs.enum_members.append(
                    (sid, i, nm.strip()[:80], val.strip()[:60] or None, 0))

    def emit_attributes(self, node: Any, rec: FileRec, sid: int,
                        bufs: Buffers) -> None:
        for c in node.children:
            if c.type == "decorator":
                txt = _txt(c, rec.data)
                name = txt.lstrip("@").split("(")[0].strip()
                bufs.attributes.append(
                    (sid, rec.fid, name[:120], txt[:200], c.start_point[0] + 1))

    def parse_imports(self, root: Any, rec: FileRec, bufs: Buffers) -> None:
        src = rec.data
        for n in walk(root):
            if n.type == "import_statement":
                srcn = n.child_by_field_name("source")
                target = _txt(srcn, src).strip('"\'`') if srcn is not None else ""
                txt = _txt(n, src)
                names = [c for c in walk(n) if c.type == "import_specifier"]
                for spec in names:
                    alias = spec.child_by_field_name("alias")
                    nm = spec.child_by_field_name("name")
                    got = alias if alias is not None else nm
                    if got is not None:
                        self._note_import(rec, _txt(got, src), target)
                clause = n.child_by_field_name("import_clause") if hasattr(
                    n, "child_by_field_name") else None
                for c in n.named_children:
                    if c.type == "import_clause":
                        for k in c.named_children:
                            if k.type == "identifier":
                                self._note_import(rec, _txt(k, src), target)
                            elif k.type == "namespace_import":
                                for kk in k.named_children:
                                    if kk.type == "identifier":
                                        self._note_import(
                                            rec, _txt(kk, src), target)
                bufs.imports.append(
                    (rec.fid, target[:300], None, None, "import",
                     n.start_point[0] + 1,
                     int(not target.startswith(".")),
                     int(target.startswith(".")),
                     int("* as" in txt),
                     int(txt.lstrip().startswith("import type")
                         or "{ type " in txt),
                     0, len(names) or 1))
            elif n.type == "export_statement":
                txt = _txt(n, src)
                srcn = n.child_by_field_name("source")
                source = _txt(srcn, src).strip('"\'`') if srcn is not None else None
                is_star = "*" in txt.split("from")[0]
                is_default = "default" in txt[:24]
                type_only = txt.lstrip().startswith("export type")
                if source is not None:
                    bufs.imports.append(
                        (rec.fid, source[:300], None, None, "reexport",
                         n.start_point[0] + 1,
                         int(not source.startswith(".")),
                         int(source.startswith(".")),
                         int(is_star), int(type_only), 0, 1))
                names = [_txt(c, src) for c in walk(n)
                         if c.type == "export_specifier"]
                if not names:
                    names = [self.node_name(n, rec) or ("default" if is_default
                                                        else "*")]
                for nm in names[:40]:
                    bufs.rows("ts_exports").append(
                        (rec.fid, nm.strip()[:120],
                         "star" if is_star else
                         ("default" if is_default else "named"),
                         n.start_point[0] + 1,
                         int(is_default), int(source is not None),
                         int(is_star), int(type_only), source))

    def parse_file_extra(self, root: Any, rec: FileRec,
                         db: sqlite3.Connection, bufs: Buffers) -> None:
        """Suppression comments, recorded with the line they silence."""
        for i, line in enumerate(rec.text.splitlines(), 1):
            m = SUPPRESS_RE.search(line)
            if not m:
                continue
            g = m.group(0)
            kind = ("ts-ignore" if "ts-ignore" in g else
                    "ts-expect-error" if "ts-expect-error" in g else
                    "ts-nocheck" if "ts-nocheck" in g else "eslint-disable")
            reason = line.split(g, 1)[-1].strip(" -:*/")[:160]
            bufs.rows("suppressions").append(
                (rec.fid, None, kind, i, reason or None))
        if rec.rel.endswith(".d.ts"):
            db.execute("UPDATE files SET lang='typescript-decl' WHERE id=?",
                       (rec.fid,))

    def parse_manifests(self, root: str, db: sqlite3.Connection) -> None:
        """Every tsconfig in the tree, and which strict flags it turns off.

        A repo-wide `strict: true` in the root tsconfig means nothing if a
        subdirectory extends it and switches half of it back off, so this maps
        every config rather than just the root one.
        """
        rows = []
        removed_by_ts7 = {
            "baseUrl": "baseUrl (removed in TS 7 -- use relative paths)",
            "downlevelIteration": "downlevelIteration (removed in TS 7)",
            "importsNotUsedAsValues": "importsNotUsedAsValues (removed)",
            "preserveValueImports": "preserveValueImports (removed)",
            "suppressImplicitAnyIndexErrors": "suppressImplicitAnyIndexErrors",
        }
        for dirpath, dirnames, filenames in os.walk(root):
            dirnames[:] = [d for d in dirnames
                           if d not in ("node_modules", ".git", "dist", "out")]
            for fn in filenames:
                if not (fn.startswith("tsconfig") and fn.endswith(".json")):
                    continue
                p = os.path.join(dirpath, fn)
                try:
                    raw = open(p, encoding="utf-8", errors="replace").read()
                except OSError:
                    continue
                cfg = _load_jsonc(raw)
                # A tsconfig whose top level is not an object is legal JSON and
                # exists in the wild (vscode ships one). Reading it as a dict
                # crashed after a 3.6-minute parse and discarded every answer.
                if not isinstance(cfg, dict):
                    continue
                co = cfg.get("compilerOptions") or {}
                mr = str(co.get("moduleResolution", "") or "")
                mod = str(co.get("module", "") or "")
                removed = [v for k, v in removed_by_ts7.items() if k in co]
                if mr.lower() in ("classic", "node", "node10"):
                    removed.append("moduleResolution: %s (removed in TS 7)" % mr)
                if mod.lower() in ("amd", "umd", "system", "none"):
                    removed.append("module: %s (removed in TS 7)" % mod)
                if str(co.get("target", "")).lower() == "es5":
                    removed.append("target: es5 (removed in TS 7)")
                rows.append((
                    os.path.relpath(p, root),
                    os.path.relpath(dirpath, root) or ".",
                    cfg.get("extends"),
                    int(bool(co.get("strict"))),
                    int(bool(co.get("noImplicitAny", co.get("strict")))),
                    int(bool(co.get("strictNullChecks", co.get("strict")))),
                    int(bool(co.get("noUncheckedIndexedAccess"))),
                    int(bool(co.get("exactOptionalPropertyTypes"))),
                    int(bool(co.get("verbatimModuleSyntax"))),
                    int(bool(co.get("isolatedModules"))),
                    int(bool(co.get("erasableSyntaxOnly"))),
                    sum(1 for f in STRICT_FLAGS if co.get(f) is True),
                    str(co.get("target", "")), mod, mr,
                    "; ".join(removed) or None))
        if rows:
            db.executemany(
                "INSERT INTO tsconfigs(path,dir,extends,strict,no_implicit_any,"
                "strict_null_checks,no_unchecked_indexed_access,exact_optional,"
                "verbatim_module_syntax,isolated_modules,erasable_syntax_only,"
                "n_strict_flags,target,module,module_resolution,removed_option)"
                " VALUES(%s)" % ",".join("?" * 16), rows)
        db.execute("INSERT OR REPLACE INTO meta(key,value) VALUES(?,?)",
                   ("tsx_files", str(self.n_tsx_files)))

    def flush_extra(self, db: sqlite3.Connection, bufs: Buffers) -> None:
        for tbl, sql in (
            ("ts_exports",
             "INSERT INTO ts_exports(file_id,name,kind,line,is_default,"
             "is_reexport,is_star,is_type_only,source) "
             "VALUES(?,?,?,?,?,?,?,?,?)"),
            ("suppressions",
             "INSERT INTO suppressions(file_id,symbol_id,kind,line,reason) "
             "VALUES(?,?,?,?,?)"),
            ("type_defs",
             "INSERT OR IGNORE INTO type_defs(symbol_id,n_members,"
             "n_optional_members,n_readonly_members,n_index_signatures,"
             "n_call_signatures,n_extends,extends_names,n_any_members,"
             "is_exported,is_ambient,is_const_enum) "
             "VALUES(?,?,?,?,?,?,?,?,?,?,?,?)"),
            ("listeners",
             "INSERT INTO listeners(symbol_id,file_id,op,target,event,line,"
             "in_loop) VALUES(?,?,?,?,?,?,?)"),
        ):
            rows = bufs.extra.get(tbl)
            if rows:
                db.executemany(sql, rows)
        # Attach each suppression to the symbol it sits inside, so a
        # @ts-ignore on a 40-caller function can be told from one in a script.
        db.execute("""
            UPDATE suppressions AS u SET symbol_id = (
                SELECT s.id FROM symbols s
                WHERE s.file_id = u.file_id
                  AND u.line BETWEEN s.line_start AND s.line_end
                  AND s.kind IN ('function','method','closure')
                ORDER BY s.line_start DESC LIMIT 1)""")

_TYPE_COUNTERS: dict[str, str] = {
    "conditional_type": "n_conditional_type",
    "mapped_type_clause": "n_mapped_type",
    "template_literal_type": "n_template_type",
    "index_signature": "n_index_signature",
    "intersection_type": "n_intersection_type",
    "union_type": "n_union_type",
    "type_parameter": "n_generic_params",
    "type_arguments": "n_type_args",
    "infer_type": "n_infer",
    "index_type_query": "n_keyof",
    "type_query": "n_typeof_type",
    "method_signature": "n_call_sig",
    "property_signature": "n_prop_sig",
    "decorator": "n_decorators",
}

def _txt(node: Any, src: bytes) -> str:
    return src[node.start_byte:node.end_byte].decode("utf-8", "replace")

def _in_loop(node: Any, stop: Any, loops: set) -> bool:
    cur = node.parent
    while cur is not None and cur.id != stop.id:
        if cur.type in loops:
            return True
        cur = cur.parent
    return False

def _type_depth(text: str) -> int:
    """Deepest `<...>` nesting. `Record<string, Array<Map<K, V>>>` is 3.

    Type-instantiation depth is what makes `tsc` slow and, past a point, what
    makes it give up entirely with "type instantiation is excessively deep".
    """
    best = depth = 0
    for ch in text:
        if ch == "<":
            depth += 1
            best = max(best, depth)
        elif ch == ">":
            depth = max(0, depth - 1)
    return best

def _load_jsonc(raw: str) -> Optional[dict]:
    """tsconfig.json is JSONC: comments and trailing commas are legal.

    A strict `json.loads` fails on most real tsconfigs, which would silently
    empty the strictness map -- the exact failure that looks like "this repo
    has no config" rather than "the parser gave up".
    """
    try:
        return json.loads(raw)
    except ValueError:
        pass
    out = []
    i, n = 0, len(raw)
    in_str = False
    while i < n:
        c = raw[i]
        if in_str:
            out.append(c)
            if c == "\\" and i + 1 < n:
                out.append(raw[i + 1])
                i += 2
                continue
            if c == '"':
                in_str = False
            i += 1
            continue
        if c == '"':
            in_str = True
            out.append(c)
            i += 1
            continue
        if c == "/" and i + 1 < n and raw[i + 1] == "/":
            while i < n and raw[i] != "\n":
                i += 1
            continue
        if c == "/" and i + 1 < n and raw[i + 1] == "*":
            i += 2
            while i + 1 < n and not (raw[i] == "*" and raw[i + 1] == "/"):
                i += 1
            i += 2
            continue
        out.append(c)
        i += 1
    text = re.sub(r',(\s*[}\]])', r'\1', "".join(out))
    try:
        return json.loads(text)
    except ValueError:
        return None

TypeScriptAnalyzer.QUERIES = [
(
    "graph-blindspots",
    "Read this first: where the call graph cannot see",
    "ANSWERS how much of every other answer here is guesswork.\n"
    "ACT external calls leave the tree by design and are NOT blindness.\n"
    "     Unresolved means we lost it -- usually a method on a value whose type\n"
    "     only the type checker knows. This tool reads syntax, not types.\n"
    "MISLEADS a type-only module legitimately has almost no edges, and that is\n"
    "     not blindness either. Read `types` next to `fns` before judging.",
    """SELECT COALESCE(m.name,'(root)') AS module,
        COUNT(DISTINCT CASE WHEN s.kind IN ('function','method','closure')
              THEN s.id END) AS fns,
        COUNT(DISTINCT CASE WHEN s.kind IN ('type','interface','enum')
              THEN s.id END) AS types,
        COALESCE(SUM(s.n_calls),0) AS calls,
        COALESCE(SUM(s.n_external_calls),0) AS external,
        COALESCE(SUM(s.n_unresolved_calls),0) AS unresolved,
        COALESCE(SUM(s.n_computed_member),0) AS computed,
        CAST(100.0*SUM(s.n_unresolved_calls)/NULLIF(SUM(s.n_calls),0) AS INT) AS pct_blind
    FROM symbols s LEFT JOIN modules m ON m.id=s.module_id
    WHERE COALESCE(m.name,'') LIKE :mod
    GROUP BY m.id HAVING calls > 0
    ORDER BY unresolved DESC LIMIT :lim"""),
(
    "any-blast-radius",
    "`any` weighted by how much code inherits the hole",
    "ANSWERS which `any` actually costs you. A count of `any` per file is\n"
    "     noise; an EXPORTED function returning `any` silently unchecks every\n"
    "     one of its callers, and that is what this ranks.\n"
    "ACT fix the highest fan_in first -- one signature re-checks many call\n"
    "     sites. Prefer `unknown` plus a narrowing check over `any`.\n"
    "MISLEADS the blast column multiplies by MAX(fan_in,1), so a symbol with\n"
    "     NO known caller scores exactly as if it had one. Read fan_in=0\n"
    "     rows as 'unknown reach', never as 'reach of 1'.\n"
    "     `any` at a genuinely dynamic boundary -- JSON parsing, a plugin\n"
    "     API -- is the right answer and appears here. Test files are excluded,\n"
    "     so a mock typed `any` is NOT here. And a function typed `any` that\n"
    "     nothing calls costs nothing.",
    """SELECT s.name, s.qual_name, s.n_any_params AS any_params,
        s.returns_any AS returns_any, s.n_any_total AS any_total,
        s.n_as_any AS as_any, s.n_non_null AS bang,
        s.fan_in, s.is_exported AS exported,
        (s.n_any_total + s.returns_any*4 + s.n_as_any*3)
            * MAX(s.fan_in,1) AS blast,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE (s.n_any_total > 0 OR s.returns_any = 1)
      AND f.is_test=0 AND f.is_generated=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY blast DESC LIMIT :lim"""),
(
    "suppression-on-hot-code",
    "@ts-ignore and eslint-disable sitting on code many callers depend on",
    "ANSWERS where the type checker was switched off somewhere that matters.\n"
    "ACT `@ts-expect-error` is strictly better than `@ts-ignore`: it FAILS when\n"
    "     the error goes away, so it cannot rot. Convert them, then fix the\n"
    "     high-fan_in ones.\n"
    "MISLEADS a suppression with a written reason next to a known upstream bug\n"
    "     is fine and appears here. The `reason` column is the evidence -- an\n"
    "     empty one is the signal, not the presence of the comment.",
    """SELECT u.kind, COALESCE(s.name,'(file level)') AS in_symbol,
        COALESCE(s.fan_in,0) AS fan_in,
        COALESCE(s.cyclomatic,0) AS cyclo,
        COALESCE(s.is_exported,0) AS exported,
        SUBSTR(COALESCE(u.reason,''),1,44) AS reason,
        f.path || ':' || u.line AS at
    FROM suppressions u
    JOIN files f ON f.id=u.file_id
    LEFT JOIN symbols s ON s.id=u.symbol_id
    LEFT JOIN modules m ON m.id=f.module_id
    WHERE f.is_test=0 AND COALESCE(m.name,'') LIKE :mod
    ORDER BY (u.kind='ts-ignore') DESC, COALESCE(s.fan_in,0) DESC LIMIT :lim"""),
(
    "barrel-blast",
    "Barrel files: how much gets pulled in per import",
    "ANSWERS the build-time cost nobody measures. `export * from './x'` means\n"
    "     importing ONE symbol from the barrel makes the compiler and the\n"
    "     bundler load every module it re-exports, transitively.\n"
    "ACT import from the defining module directly, or replace `export *` with\n"
    "     explicit named re-exports so tree-shaking can work.\n"
    "MISLEADS a barrel in a package's public entry point is deliberate API\n"
    "     design and is correct. The cost only bites on INTERNAL barrels that\n"
    "     the package's own modules import from.",
    """SELECT f.path AS barrel, COUNT(*) AS star_exports,
        (SELECT COUNT(*) FROM imports i WHERE i.target_id=f.id) AS importers,
        (SELECT COUNT(*) FROM ts_exports e2
         WHERE e2.file_id=f.id AND e2.is_star=0) AS named_exports,
        f.sloc,
        GROUP_CONCAT(DISTINCT SUBSTR(e.source,1,26)) AS reexports
    FROM ts_exports e JOIN files f ON f.id=e.file_id
    LEFT JOIN modules m ON m.id=f.module_id
    WHERE e.is_star=1 AND COALESCE(m.name,'') LIKE :mod
    GROUP BY f.id
    ORDER BY star_exports DESC LIMIT :lim"""),
(
    "strictness-map",
    "Which directories opted out of which strict flags",
    "ANSWERS whether `strict: true` at the root actually holds everywhere.\n"
    "ACT a nested tsconfig that extends the root and turns strictNullChecks\n"
    "     back off is where the null bugs live. `removed_option` flags settings\n"
    "     TypeScript 7 no longer accepts at all -- those are build breaks, not\n"
    "     style.\n"
    "MISLEADS this reads the config, not the code. A directory with strict off\n"
    "     and no `any` in it is fine; cross-reference with `any-blast-radius`.",
    """SELECT dir, strict, no_implicit_any AS no_impl_any,
        strict_null_checks AS null_checks,
        no_unchecked_indexed_access AS unchecked_index,
        exact_optional, verbatim_module_syntax AS verbatim,
        erasable_syntax_only AS erasable,
        n_strict_flags AS strict_flags, target, module_resolution AS resolution,
        removed_option AS removed_in_ts7
    FROM tsconfigs
    WHERE dir LIKE :mod
    ORDER BY (removed_option IS NOT NULL) DESC, n_strict_flags ASC LIMIT :lim"""),
(
    "type-depth-blowup",
    "Types deep enough to slow the compiler down",
    "ANSWERS which declarations make `tsc` crawl. Conditional-type recursion\n"
    "     and deep generic instantiation are the documented cause of quadratic\n"
    "     compile time, and past a limit the compiler gives up entirely with\n"
    "     'type instantiation is excessively deep and possibly infinite'.\n"
    "ACT flatten with a named intermediate type, or add an explicit depth\n"
    "     counter to bound the recursion.\n"
    "MISLEADS depth is a syntactic bracket count plus conditional nesting. It\n"
    "     is a proxy for instantiation cost, not a measurement of it. Only\n"
    "     `tsc --extendedDiagnostics` settles which type is actually slow.",
    """SELECT s.name, s.kind, s.max_type_depth AS depth,
        s.n_conditional_type AS conditionals,
        s.n_conditional_depth AS cond_nesting,
        s.n_mapped_type AS mapped, s.n_infer AS infers,
        s.n_union_members AS union_members, s.n_template_type AS template_types,
        s.n_generic_params AS tparams, s.fan_in,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE (s.max_type_depth >= 3 OR s.n_conditional_depth >= 2)
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.n_conditional_depth DESC, s.max_type_depth DESC LIMIT :lim"""),
(
    "listener-leak",
    "Subscriptions added and never removed",
    "ANSWERS the leak no JavaScript or TypeScript linter checks for. Across\n"
    "     ESLint, typescript-eslint, unicorn, Biome, oxlint and CodeQL there is\n"
    "     no rule for this; it is a genuine gap, not a duplicate.\n"
    "ACT every add needs a matching remove on the same target, in a cleanup\n"
    "     path -- a React effect return, a `destroy`, or an AbortController\n"
    "     signal. A listener added inside a loop with no removal grows without\n"
    "     bound.\n"
    "MISLEADS the pairing is per FUNCTION, so an add in `mount` and a remove in\n"
    "     `unmount` looks unbalanced and is correct. Check the owning class\n"
    "     before acting; `target` is there to help you match them by hand.",
    """SELECT s.name, s.qual_name,
        SUM(l.op='add') AS adds, SUM(l.op='remove') AS removes,
        SUM(l.in_loop) AS in_loop,
        GROUP_CONCAT(DISTINCT l.event) AS events,
        GROUP_CONCAT(DISTINCT SUBSTR(l.target,1,20)) AS targets,
        (SELECT COUNT(*) FROM listeners l2
         JOIN symbols s2 ON s2.id=l2.symbol_id
         WHERE s2.parent_id=s.parent_id AND l2.op='remove') AS removes_in_class,
        s.fan_in, f.path || ':' || MIN(l.line) AS at
    FROM listeners l
    JOIN symbols s ON s.id=l.symbol_id
    JOIN files f ON f.id=l.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE f.is_test=0 AND COALESCE(m.name,'') LIKE :mod
    GROUP BY s.id
    HAVING adds > removes
    ORDER BY (adds - removes) DESC, in_loop DESC LIMIT :lim"""),
(
    "timer-leak",
    "Timers started with no matching clear",
    "ANSWERS the other half of the leak nobody lints for. A `setInterval` with\n"
    "     no `clearInterval` runs until the process dies and keeps every\n"
    "     variable its callback closes over alive with it.\n"
    "ACT store the handle and clear it in the teardown path.\n"
    "MISLEADS a `setTimeout` that fires once needs no clear and is counted\n"
    "     here. The dangerous one is `setInterval`, and a timer started inside\n"
    "     a loop or a request handler.",
    """SELECT s.name, s.n_timer_set AS timers_set,
        s.n_timer_clear AS timers_cleared, s.timer_in_loop AS in_loop,
        s.n_closure_capture AS captures, s.is_handler AS handler,
        s.is_component AS component, s.fan_in,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_timer_set > s.n_timer_clear AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY (s.n_timer_set - s.n_timer_clear) DESC,
        s.timer_in_loop DESC LIMIT :lim"""),
(
    "sync-under-handler",
    "Blocking *Sync calls reachable from a request handler, up to 4 hops",
    "ANSWERS which endpoint stops the whole event loop. Node is single\n"
    "     threaded per process: one `readFileSync` in one handler blocks every\n"
    "     other in-flight request, not just its own.\n"
    "ACT use the promise API. `fs/promises`, `execFile`, `pbkdf2` -- every\n"
    "     *Sync has an async twin.\n"
    "MISLEADS a *Sync call at startup, in a CLI, or in a build script is\n"
    "     correct and often preferable. Only rows reachable from a handler are\n"
    "     the finding, which is what the hop count is for.",
    """WITH RECURSIVE down(sym, depth) AS (
        SELECT s.id, 0 FROM symbols s WHERE s.is_handler=1 OR s.is_entrypoint=1
        UNION
        SELECT e.callee_id, d.depth+1 FROM down d
        JOIN edges e ON e.caller_id=d.sym
        WHERE d.depth < 4 AND e.is_self=0),          -- DEPTH BOUND 4
    best AS (SELECT sym, MIN(depth) AS depth FROM down GROUP BY sym)
    SELECT s.name, b.depth AS hops, s.n_sync_block AS sync_calls,
        s.n_exec AS exec_, s.n_io AS io, s.is_async AS async_,
        s.fan_in, f.path || ':' || s.line_start AS at
    FROM best b JOIN symbols s ON s.id=b.sym
    JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_sync_block > 0 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY b.depth ASC, s.n_sync_block DESC LIMIT :lim"""),
(
    "await-in-loop",
    "Sequential awaits that could have overlapped",
    "ANSWERS where latency is the SUM of N round trips instead of the max.\n"
    "ACT if the iterations are independent, build the promises and hand them\n"
    "     to Promise.all. N x 40ms becomes 40ms.\n"
    "MISLEADS some loops MUST be sequential -- pagination, rate limits, or a\n"
    "     later iteration depending on an earlier result. `promise_all` in the\n"
    "     same row means the author already knows the pattern.",
    """SELECT s.name, s.await_in_loop AS awaits_in_loop,
        s.max_loop_depth AS depth, s.n_await AS total_awaits,
        s.n_promise_all AS promise_all, s.n_net AS net_,
        s.fan_in, f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.await_in_loop > 0 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.await_in_loop DESC, s.max_loop_depth DESC LIMIT :lim"""),
(
    "redos-reachable",
    "Regexes that can blow up, and how far they sit from an entry point",
    "ANSWERS which regex a crafted input can hang the process with. A\n"
    "     quantifier inside a quantified group backtracks exponentially.\n"
    "ACT rewrite to avoid nested quantifiers, or bound the input length before\n"
    "     matching. Node has no regex timeout.\n"
    "MISLEADS the pattern detector is shape-based and over-reports: many nested\n"
    "     quantifiers are provably linear because their branches cannot both\n"
    "     match. Confirm with a backtracking analyser before acting.",
    """SELECT s.name, s.n_regex_redos AS suspicious_regexes,
        s.n_regex_lit AS total_regexes, s.regex_in_loop AS in_loop,
        s.is_exported AS exported, s.is_handler AS handler, s.fan_in,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_regex_redos > 0 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.fan_in DESC, s.n_regex_redos DESC LIMIT :lim"""),
(
    "dom-sinks",
    "innerHTML and friends, ranked by reachability from outside",
    "ANSWERS where a string becomes markup the browser will execute.\n"
    "ACT use textContent, or sanitise with a real sanitiser. Framework escape\n"
    "     hatches (dangerouslySetInnerHTML) are named that way for a reason.\n"
    "MISLEADS assigning a constant template to innerHTML is safe and appears\n"
    "     here. This finds the SINK; whether untrusted data reaches it needs a\n"
    "     taint analysis this does not do.",
    """SELECT s.name, s.n_innerhtml AS innerhtml, s.n_dom AS dom_ops,
        s.n_json_parse AS json_parse, s.n_any_params AS any_params,
        s.is_exported AS exported, s.is_component AS component, s.fan_in,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE (s.n_innerhtml > 0 OR s.n_dom > 0) AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.n_innerhtml DESC, s.fan_in DESC LIMIT :lim"""),
(
    "import-cycles",
    "Files that import each other, and whether the cycle is type-only",
    "ANSWERS which import pairs are mutually dependent.\n"
    "ACT a VALUE cycle is a runtime hazard: one side sees a partly initialised\n"
    "     module. A TYPE-ONLY cycle is erased at compile time and is harmless.\n"
    "     Fix the value cycles; convert the rest to `import type`.\n"
    "MISLEADS this compares direct file-to-file edges only, so a three-hop\n"
    "     cycle is invisible and the count UNDERSTATES. Unresolved import\n"
    "     targets (bare package specifiers) are excluded entirely.",
    """SELECT fa.path AS file_a, fb.path AS file_b,
        SUM(ia.is_type_only) AS a_type_only, COUNT(DISTINCT ia.id) AS a_to_b,
        (SELECT COUNT(*) FROM imports ib
         WHERE ib.file_id=fb.id AND ib.target_id=fa.id) AS b_to_a,
        (SELECT SUM(ib2.is_type_only) FROM imports ib2
         WHERE ib2.file_id=fb.id AND ib2.target_id=fa.id) AS b_type_only
    FROM imports ia
    JOIN files fa ON fa.id=ia.file_id
    JOIN files fb ON fb.id=ia.target_id
    LEFT JOIN modules m ON m.id=fa.module_id
    WHERE fa.id < fb.id AND COALESCE(m.name,'') LIKE :mod
      AND EXISTS (SELECT 1 FROM imports ib3
                  WHERE ib3.file_id=fb.id AND ib3.target_id=fa.id)
    GROUP BY fa.id, fb.id
    ORDER BY (a_to_b + b_to_a) DESC LIMIT :lim"""),
(
    "assertion-density",
    "`as` and `!` clustered where types are weakest",
    "ANSWERS where the code is telling the compiler to trust it. Each `as` and\n"
    "     each `!` is a place a runtime type error can no longer be caught.\n"
    "ACT `as unknown as T` is a double assertion and always worth reading.\n"
    "     `!` on a value the checker thinks is nullable is either a missing\n"
    "     guard or a lie.\n"
    "MISLEADS an assertion after a hand-written type guard is correct and\n"
    "     appears here; `satisfies` is the safe alternative and is counted\n"
    "     separately as counter-evidence.",
    """SELECT s.name, s.n_as_assertion AS as_casts, s.n_as_any AS as_any,
        s.n_non_null AS bang, s.n_angle_assertion AS angle_casts,
        s.n_satisfies AS satisfies_, s.n_any_total AS any_,
        s.n_suppressions AS suppressions, s.fan_in, s.is_exported AS exported,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE (s.n_as_assertion + s.n_non_null + s.n_angle_assertion) > 0
      AND f.is_test=0 AND COALESCE(m.name,'') LIKE :mod
    ORDER BY (s.n_as_any*4 + s.n_as_assertion + s.n_non_null) DESC LIMIT :lim"""),
(
    "weak-interfaces",
    "Interfaces and types carrying `any` or an index signature",
    "ANSWERS which shared shapes give up checking for everyone who uses them.\n"
    "ACT an index signature (`[k: string]: any`) makes every property access\n"
    "     legal, including typos. Narrow it to a union of known keys, or use\n"
    "     Record with a concrete value type.\n"
    "MISLEADS an index signature is the correct model for a genuine dictionary\n"
    "     and for JSON-shaped data. The `n_members` column separates a real\n"
    "     interface with one escape hatch from a shape that is all escape.",
    """SELECT s.name, s.kind, t.n_members AS members,
        t.n_any_members AS any_members, t.n_index_signatures AS index_sigs,
        t.n_optional_members AS optional_, t.n_readonly_members AS readonly_,
        t.n_extends AS extends_, t.is_exported AS exported, s.fan_in,
        f.path || ':' || s.line_start AS at
    FROM type_defs t
    JOIN symbols s ON s.id=t.symbol_id
    JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE (t.n_any_members > 0 OR t.n_index_signatures > 0)
      AND f.is_test=0 AND COALESCE(m.name,'') LIKE :mod
    ORDER BY (t.n_any_members + t.n_index_signatures) DESC,
        s.fan_in DESC LIMIT :lim"""),
(
    "dead-exports",
    "Exported and never imported anywhere in this tree",
    "ANSWERS what the public surface carries that nothing here uses.\n"
    "ACT if this is an application, delete it. If it is a library, this is\n"
    "     your published API and the query is telling you its size, not that\n"
    "     it is dead.\n"
    "MISLEADS THIS IS THE QUERY MOST LIKELY TO BE WRONG. A consumer outside\n"
    "     the tree, a barrel re-export, a dynamic import, or a string-keyed\n"
    "     registry all make an export live and invisible here. Check\n"
    "     `barrel-blast` and `graph-blindspots` before deleting anything.",
    """SELECT e.name AS export_, e.kind, f.path,
        e.is_default AS default_, e.is_type_only AS type_only,
        (SELECT COUNT(*) FROM imports i WHERE i.target_id=f.id) AS file_importers,
        COALESCE(s.fan_in,0) AS fan_in, COALESCE(s.sloc,0) AS sloc
    FROM ts_exports e
    JOIN files f ON f.id=e.file_id
    LEFT JOIN symbols s ON s.file_id=f.id AND s.name=e.name
    LEFT JOIN modules m ON m.id=f.module_id
    WHERE e.is_star=0 AND e.is_reexport=0 AND f.is_test=0 AND f.is_generated=0
      AND COALESCE(s.fan_in,0)=0
      AND (SELECT COUNT(*) FROM imports i2 WHERE i2.target_id=f.id)=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY COALESCE(s.sloc,0) DESC LIMIT :lim"""),
(
    "ts7-breaking",
    "Config and syntax TypeScript 7 no longer accepts",
    "ANSWERS what will fail to build on an upgrade, before you attempt it.\n"
    "ACT `baseUrl`, `moduleResolution: node10`, `module: amd|umd|system`,\n"
    "     `target: es5` and `downlevelIteration` are GONE in 7.0, not\n"
    "     deprecated. Fix these first; they are hard build breaks.\n"
    "MISLEADS this reads config only. `erasableSyntaxOnly` additionally bans\n"
    "     enums, runtime namespaces and parameter properties -- the enum and\n"
    "     namespace counts below tell you how much work that flag would be,\n"
    "     but it is opt-in and not required by 7.0 itself.",
    """SELECT c.dir, c.removed_option AS breaks_in_ts7, c.target,
        c.module, c.module_resolution AS resolution,
        c.erasable_syntax_only AS erasable,
        (SELECT COUNT(*) FROM symbols s JOIN files f2 ON f2.id=s.file_id
         WHERE s.kind='enum' AND f2.dir LIKE c.dir || '%') AS enums,
        (SELECT COUNT(*) FROM symbols s2 JOIN files f3 ON f3.id=s2.file_id
         WHERE s2.kind='module' AND f3.dir LIKE c.dir || '%') AS namespaces
    FROM tsconfigs c
    WHERE c.dir LIKE :mod
    ORDER BY (c.removed_option IS NOT NULL) DESC LIMIT :lim"""),
(
    "god-functions",
    "Functions doing too much, by every measure at once",
    "ANSWERS which functions are hardest to hold in your head.\n"
    "ACT split by responsibility. n_elif distinguishes a flat dispatch (extract\n"
    "     a lookup) from real nesting (extract functions).\n"
    "MISLEADS a long flat dispatch reads far more easily than a short deeply\n"
    "     nested one, which is why this sorts by cognitive, not sloc.",
    """SELECT s.name, s.sloc, s.cyclomatic AS cyclo, s.cognitive AS cog,
        s.max_nesting AS nest, s.n_elif AS elifs, s.n_returns AS returns_,
        s.n_params, s.n_any_total AS any_, s.maintainability AS maint,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.kind IN ('function','method','closure') AND f.is_generated=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.cognitive DESC LIMIT :lim"""),
(
    "risk-ranked",
    "Review order: if you can only read N functions this week, which N",
    "ANSWERS which functions combine complexity with unsound typing and\n"
    "     dangerous operations.\n"
    "ACT start at the top. The score weights eval, prototype pollution, `as\n"
    "     any` and @ts-ignore far above raw complexity.\n"
    "MISLEADS a heuristic, not a finding. Generated and vendored files are\n"
    "     excluded, so the real top of the list may be in code this hid.",
    """SELECT s.name, s.risk_score AS risk, s.cyclomatic AS cyclo,
        s.cognitive AS cog, s.n_any_total AS any_, s.n_as_any AS as_any,
        s.n_ts_ignore AS ts_ignore, s.n_exec AS exec_,
        s.n_sync_block AS sync_, s.fan_in,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.kind IN ('function','method','closure') AND f.is_generated=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.risk_score DESC LIMIT :lim"""),
(
    "hot-multipliers",
    "Where one fix pays back many times: highest fan-in",
    "ANSWERS which functions the rest of the tree leans on hardest.\n"
    "ACT a win in a high-fan-in leaf pays once per caller.\n"
    "MISLEADS fan_in counts STATIC call sites this parser could resolve, not\n"
    "     runtime frequency, and TypeScript resolution is name-based -- a\n"
    "     method on an interface-typed value is not attributed here.",
    """SELECT s.name, s.fan_in, s.n_callsites AS sites, s.fan_out,
        s.cyclomatic AS cyclo, s.sloc, s.has_doc AS doc,
        s.is_exported AS exported, s.returns_any AS returns_any,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.kind IN ('function','method','closure')
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.fan_in DESC, s.cyclomatic DESC LIMIT :lim"""),
(
    "module-coupling",
    "Which modules depend on which, and how unstable that makes them",
    "ANSWERS which modules are hard to change because everything leans on them.\n"
    "ACT instability near 0 with high fan_in is a good place for stable\n"
    "     abstractions and a bad place for volatile logic.\n"
    "MISLEADS instability is a ratio, so a module with one edge each way scores\n"
    "     0.5 and means nothing. Read it next to n_files.",
    """SELECT name, kind, n_files AS files, sloc, n_symbols AS syms,
        n_public AS exported, fan_in, fan_out,
        ROUND(instability,2) AS instability
    FROM modules WHERE n_files>0 AND name LIKE :mod
    ORDER BY (fan_in + fan_out) DESC LIMIT :lim"""),
(
    "markers",
    "TODO, FIXME, HACK and BUG, weighted by the code they sit in",
    "ANSWERS which unfinished business sits where it matters.\n"
    "ACT a FIXME in a function forty things depend on outranks a TODO in a\n"
    "     build script.\n"
    "MISLEADS marker age is invisible -- git blame is the missing column.",
    """SELECT k.kind, f.path, k.line, SUBSTR(k.text,1,54) AS text,
        COALESCE(s.name,'(module level)') AS in_fn,
        COALESCE(s.fan_in,0) AS fan_in
    FROM markers k
    JOIN files f ON f.id=k.file_id
    LEFT JOIN modules m ON m.id=f.module_id
    LEFT JOIN symbols s ON s.file_id=f.id
        AND k.line BETWEEN s.line_start AND s.line_end
        AND s.kind IN ('function','method','closure')
    WHERE k.kind IN ('TODO','FIXME','HACK','BUG','XXX','WARNING')
      AND f.is_generated=0 AND COALESCE(m.name,'') LIKE :mod
    ORDER BY COALESCE(s.fan_in,0) DESC LIMIT :lim"""),
(
    "parse-coverage",
    "What this run could not read",
    "ANSWERS whether the numbers above cover the code you think they cover.\n"
    "ACT a file here contributed less than it should have.\n"
    "MISLEADS tree-sitter-typescript 0.23.2 was released 2024-11-11 and is\n"
    "     over a year behind the language. It does not accept `export type {X}\n"
    "     from './y'` in every position, and some `.d.ts` default-export forms\n"
    "     that tsc accepts. Errors here are usually the GRAMMAR being stale,\n"
    "     not the code being wrong -- check the file by hand before believing\n"
    "     it is broken.",
    """SELECT f.path, f.lines, f.n_parse_errors AS error_nodes,
        f.n_missing_nodes AS missing, f.parsed,
        f.is_generated AS generated, f.is_test AS test, f.ext
    FROM files f
    LEFT JOIN modules m ON m.id=f.module_id
    WHERE (f.n_parse_errors>0 OR f.parsed=0)
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY f.n_parse_errors DESC LIMIT :lim"""),
(
    "assertion-escape-hatches",
    "as any, non-null ! and angle-bracket casts: where the type system was told to be quiet",
    "ANSWERS where a type was asserted rather than proved. `x!` claims a\n"
    "     value is not null with no check; `as any` disables every check\n"
    "     downstream of it. Both move a failure from tsc to run time, and\n"
    "     `as any` additionally poisons inference for whatever it flows into.\n"
    "ACT narrow instead of asserting -- an if, a type guard, or `satisfies`,\n"
    "     which checks without widening. Where an assertion is genuinely\n"
    "     needed at a boundary, assert to the specific type, never to any.\n"
    "MISLEADS a single `as any` in a well-fenced adapter is a deliberate,\n"
    "     correct trade. What this ranks is DENSITY on code others call --\n"
    "     the assertions that leak their looseness outwards.",
    """SELECT s.name, s.qual_name AS qual, s.n_as_any AS as_any,
        s.n_non_null AS non_null, s.n_angle_assertion AS angle_casts,
        s.n_as_assertion AS assertions, s.n_satisfies AS satisfies_,
        s.returns_any AS returns_any, s.is_exported AS exported, s.fan_in,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE (s.n_as_any + s.n_non_null + s.n_angle_assertion) > 0
      AND f.is_test=0 AND COALESCE(m.name,'') LIKE :mod
    ORDER BY (s.n_as_any*3 + s.n_non_null + s.n_angle_assertion)
             * (1 + s.fan_in) DESC LIMIT :lim"""),
(
    "suppression-debt",
    "@ts-ignore, @ts-expect-error and eslint-disable, and which are load-bearing",
    "ANSWERS how much of the codebase compiles only because it was told to.\n"
    "     The difference matters: `@ts-expect-error` FAILS when the error goes\n"
    "     away, so it cleans itself up; `@ts-ignore` silently outlives the\n"
    "     problem it was hiding and then hides the next one.\n"
    "ACT convert every `@ts-ignore` to `@ts-expect-error`. The ones that then\n"
    "     fail the build were suppressing nothing and can be deleted; the\n"
    "     rest now tell you when they become unnecessary.\n"
    "MISLEADS a suppression on a known upstream typing bug is the right call\n"
    "     and cannot be distinguished here from one hiding a real defect.\n"
    "     Density plus fan_in is the ranking, not the raw count.",
    """SELECT s.name, s.qual_name AS qual, s.n_ts_ignore AS ts_ignore,
        s.n_ts_expect_error AS ts_expect_error,
        s.n_eslint_disable AS eslint_disable, s.n_suppressions AS total,
        s.n_any_total AS anys, s.is_exported AS exported, s.fan_in,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE (s.n_ts_ignore + s.n_ts_expect_error + s.n_eslint_disable) > 0
      AND f.is_test=0 AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.n_ts_ignore * (1 + s.fan_in) DESC,
        s.n_eslint_disable DESC LIMIT :lim"""),
(
    "type-level-complexity",
    "Conditional and mapped types deep enough to cost compile time",
    "ANSWERS which types are programs. Deeply nested conditional types with\n"
    "     `infer` are evaluated by the compiler on every check, and past a\n"
    "     certain depth they dominate build time or hit the instantiation\n"
    "     limit outright -- the error nobody can read.\n"
    "ACT flatten the conditional chain, or precompute the result as a named\n"
    "     type alias so it is instantiated once instead of at every use.\n"
    "     Measure with `tsc --diagnostics` before and after.\n"
    "MISLEADS depth is structural, not a cost model. A depth-6 type used\n"
    "     twice is free; a depth-3 type instantiated in a hot generic is not.\n"
    "     This finds candidates for the profiler, not verdicts.",
    """SELECT s.name, s.qual_name AS qual, s.max_type_depth AS type_depth,
        s.n_conditional_depth AS cond_depth, s.n_conditional_type AS conds,
        s.n_mapped_type AS mapped, s.n_infer AS infers,
        s.n_template_type AS templates, s.n_union_members AS union_members,
        s.is_exported AS exported, f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE (s.max_type_depth > 2 OR s.n_conditional_depth > 1) AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.n_conditional_depth DESC, s.max_type_depth DESC,
        s.n_infer DESC LIMIT :lim"""),
(
    "index-signature-holes",
    "Index signatures and unknown, where excess-property checking stops applying",
    "ANSWERS which types accept anything. An index signature makes every\n"
    "     property name legal, so a typo in a key is not a type error -- and\n"
    "     under `noUncheckedIndexedAccess` every read is silently possibly\n"
    "     undefined, which most codebases do not have switched on.\n"
    "ACT use Record with a union of the known keys, or a Map when keys are\n"
    "     genuinely open. `unknown` is the right escape hatch where `any`\n"
    "     was reached for, because it forces narrowing at the point of use.\n"
    "MISLEADS an index signature on a genuine dictionary is exactly correct\n"
    "     and appears here. The rows worth reading are exported types where\n"
    "     callers will rely on the shape.",
    """SELECT s.name, s.qual_name AS qual,
        s.n_index_signature AS index_sigs, s.n_unknown_type AS unknowns,
        s.n_any_total AS anys, s.n_keyof AS keyofs,
        s.n_prop_sig AS prop_sigs, s.n_call_sig AS call_sigs,
        s.is_exported AS exported, s.fan_in,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_index_signature > 0 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.is_exported DESC, s.n_index_signature * (1 + s.fan_in) DESC
    LIMIT :lim"""),
(
    "declaration-vs-implementation",
    "Ambient .d.ts declarations, and whether an implementation exists in this tree",
    "ANSWERS which part of the public surface is a promise rather than code.\n"
    "     A `.d.ts` describes something the compiler will trust absolutely\n"
    "     and never verify -- if it drifts from the JavaScript it describes,\n"
    "     every caller type-checks against a fiction.\n"
    "ACT generate declarations from the source with `declaration: true`\n"
    "     rather than hand-writing them. Where they must be hand-written --\n"
    "     describing a JS dependency -- pin the version they were written\n"
    "     against, because nothing else will catch the drift.\n"
    "MISLEADS a type-only package is ALL declarations by design and tops this\n"
    "     list correctly. fan_in of zero on a declaration means nothing in\n"
    "     THIS tree uses it, not that it is dead.",
    """SELECT s.name, s.qual_name AS qual,
        s.is_declaration_only AS declaration_only,
        s.n_call_sig AS call_sigs, s.n_prop_sig AS prop_sigs,
        s.n_type_args AS type_args, s.is_exported AS exported, s.fan_in,
        s.n_any_total AS anys, f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.is_declaration_only = 1 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.is_exported DESC, s.n_any_total DESC, s.fan_in DESC
    LIMIT :lim"""),
]

TypeScriptAnalyzer.QUERIES = TypeScriptAnalyzer.QUERIES + [
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

    ("event-loop-block-below-entry", "synchronous fs or a nested scan reachable from an exported or handler entry point",
    "ANSWERS the question typescript-eslint answers per-file: no-sync,\n"
    "     no-await-in-loop and the perf rules each see one function. The graph\n"
    "     sees the path. A `readFileSync` in a helper is fine until an exported\n"
    "     API reaches it, at which point every consumer of that API inherits a\n"
    "     blocked event loop.\n"
    "ACT for `sync_fs_calls`, move to the promise API. For `search_in_loop`,\n"
    "     hoist a Set. `reached_from` names the exported symbol whose latency\n"
    "     budget this spends.\n"
    "MISLEADS an exported symbol is not necessarily public API -- a barrel file\n"
    "     re-exports everything, so `is_exported` overcounts. Depth is bounded\n"
    "     at 4 hops, and a call through an interface method is only resolved\n"
    "     when the implementation is unambiguous.",
    """WITH RECURSIVE walk(root, sym, depth) AS (
        SELECT s.id, s.id, 0 FROM symbols s
        JOIN files f ON f.id = s.file_id
        WHERE (s.is_exported = 1 OR s.is_handler = 1 OR s.is_entrypoint = 1)
          AND f.is_test = 0
        UNION
        SELECT w.root, e.callee_id, w.depth + 1
        FROM walk w JOIN edges e ON e.caller_id = w.sym
        WHERE w.depth < 4 AND e.is_self = 0),      -- depth bound: 4 hops
    reach(root, sym, depth) AS (
        SELECT root, sym, MIN(depth) FROM walk GROUP BY root, sym)
    SELECT s.name, entry.name AS reached_from, MIN(r.depth) AS hops,
        s.n_fs_sync AS sync_fs_calls, s.n_search_in_loop AS search_in_loop,
        s.n_json_parse_in_loop AS json_parse_in_loop,
        s.n_array_grow_in_loop AS array_grow_in_loop,
        s.is_async AS callee_is_async, s.fan_in,
        f.path || \':\' || s.line_start AS at
    FROM reach r
    JOIN symbols s ON s.id = r.sym
    JOIN symbols entry ON entry.id = r.root
    JOIN files f ON f.id = s.file_id
    LEFT JOIN modules m ON m.id = s.module_id
    WHERE r.depth > 0 AND f.is_test = 0
      AND (s.n_fs_sync > 0 OR s.n_search_in_loop > 0
           OR s.n_json_parse_in_loop > 0)
      AND COALESCE(m.name,\'\') LIKE :mod
    GROUP BY s.id, entry.id
    ORDER BY sync_fs_calls DESC, hops ASC, s.fan_in DESC LIMIT :lim"""),

    ("listener-added-never-removed", "a function that adds listeners and neither removes nor disposes them",
    "ANSWERS the leak no linter states as a rule because the pairing is a\n"
    "     convention, not a syntax: whatever calls addEventListener, `.on` or\n"
    "     `.subscribe` must eventually call the matching remove, or hand the\n"
    "     handle to something that will. A function with adds, zero removes and\n"
    "     zero dispose calls either delegates ownership or leaks -- and the\n"
    "     graph shows how many callers currently assume the former.\n"
    "ACT return the disposable so the caller can own it, or register into a\n"
    "     DisposableStore. `listener_in_loop` marks the version that leaks once\n"
    "     per iteration rather than once per call.\n"
    "MISLEADS the correct case looks identical: a function that adds a listener\n"
    "     and returns the disposable is right, and the return value is not\n"
    "     modelled. A listener on an object that dies with the function is also\n"
    "     fine. Read this as an audit list, not a leak list.",
    """SELECT s.name, s.n_listener_add AS adds,
        s.n_listener_remove AS removes, s.n_dispose_call AS dispose_calls,
        s.listener_in_loop AS adds_in_loop, s.is_async AS is_async,
        s.fan_in, COUNT(DISTINCT e.caller_id) AS distinct_callers,
        f.path || \':\' || s.line_start AS at
    FROM symbols s
    JOIN files f ON f.id = s.file_id
    LEFT JOIN edges e ON e.callee_id = s.id AND e.is_self = 0
    LEFT JOIN modules m ON m.id = s.module_id
    WHERE s.n_listener_add > 0 AND s.n_listener_remove = 0
      AND s.n_dispose_call = 0 AND f.is_test = 0
      AND COALESCE(m.name,\'\') LIKE :mod
    GROUP BY s.id
    ORDER BY adds_in_loop DESC, adds DESC, distinct_callers DESC
    LIMIT :lim"""),
]

ANALYZER = TypeScriptAnalyzer()


if __name__ == "__main__":
    try:
        sys.exit(main(ANALYZER))
    except KeyboardInterrupt:
        print("\ninterrupted", file=sys.stderr)
        sys.exit(130)
