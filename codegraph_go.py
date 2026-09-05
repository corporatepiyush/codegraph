#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Piyush Katariya
#
# @author Piyush Katariya
"""codegraph_go.py -- parse a Go tree into a graph and query it.

Targets Go 1.26. Parses with tree-sitter-go.

Go's compiler and `go vet` already catch most single-function mistakes, so this
does not compete with them. What it adds is the shape no single-file checker
can see: which goroutine spawned under a request handler has no way to stop,
which context stops being propagated three frames down, which interface has
exactly one implementation and is therefore an abstraction over nothing.

Two Go facts this bakes in, both from reading go.mod rather than guessing:

* Loop-variable capture was fixed in Go 1.22. Flagging `for _, v := range` +
  `go func(){ use(v) }` in a module declaring `go 1.22` or later is a false
  positive, so `n_loopvar_capture` is only counted below that line.
* Since Go 1.26 `go mod init` writes `go 1.(N-1).0` rather than the toolchain
  version, so the declared version now systematically lags. It is still the
  right thing to read -- it is what the compiler uses.

Usage:
  python3 codegraph_go.py /path/to/repo --report
  python3 codegraph_go.py /path/to/repo --list
  python3 codegraph_go.py --deps"""
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

#: Line prefixes counted as a comment line during discovery. Hoisted from a
#: literal inside the file loop so the tuple is not re-parsed per file.
_DISCOVER_COMMENT_PREFIXES = ("//", "#", "/*", "*", "*/", '"""', "'''",
                              "--", ";;", "%")

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
CREATE INDEX idx_files_gen ON files(is_generated);
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
CREATE INDEX idx_imp_intra ON imports(file_id) WHERE is_external=0;

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
        self._sym_defaults: Optional[list[Any]] = None
        self._sym_idx: Optional[dict[str, int]] = None

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
                rpath = os.path.realpath(full)
                if rpath != full and \
                        not rpath.startswith(real_root + os.sep):
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
                longest = max(map(len, data.split(b"\n")))
                if longest > analyzer.MAX_LINE_BYTES:
                    n_skipped_big += 1
                    too_big = True

            lines = text.splitlines()
            # One pass over the lines for blank/code/comment/max-length --
            # these were four separate generator sweeps re-running strip() on
            # every line of every file.
            blank = 0
            sloc = 0
            cmt = 0
            max_line = 0
            prefixes = _DISCOVER_COMMENT_PREFIXES
            for l in lines:
                if l.strip():
                    sloc += 1
                    if l.lstrip()[:3] in prefixes:
                        cmt += 1
                else:
                    blank += 1
                n = len(l)
                if n > max_line:
                    max_line = n
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
                 mid, st.st_size, len(lines), sloc, blank, cmt, max_line,
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
        # Comment-marker substring test FIRST: it is far cheaper than the
        # regex and a line failing it can never emit a marker, so most lines
        # skip the regex entirely. Same rows, same order.
        if ("//" in line or "#" in line or "*" in line or "--" in line) \
                and (m := MARKER_RE.search(line)):
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

#: Shared empty for `extra_loop_ids` defaults: one object instead of a fresh
#: set per measured body.
_NO_EXTRA_LOOPS = frozenset()

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
    #: (var_text, kind, line, in_loop) -- http.Request input reads
    input_sites: list[tuple[str, str, int, bool]] = dc_field(default_factory=list)
    #: (value, line) -- G07 credential-shaped string literals
    secrets: list[tuple[str, int]] = dc_field(default_factory=list)
    #: (kind, node, loop_depth) -- language tables filled during the SAME walk
    #: (goroutines/defers/channels) instead of a second traversal per symbol.
    extra_rows: list[tuple[str, Any, int]] = dc_field(default_factory=list)
    #: (var, op, line, in_goroutine) -- wg.Add/Done/Wait sites, so Add/Done/Wait
    #: pair per WaitGroup VARIABLE, not per function text (SA2000 family).
    wg_ops: list[tuple[str, str, int, int]] = dc_field(default_factory=list)
    #: names passed to builtin close(ch) in this body; pairs channel
    #: declarations with their closer (channels.closed_in_fn).
    close_vars: list[str] = dc_field(default_factory=list)

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
        # One-entry cache of the last call node's function text: measure
        # fires on_call and then on_node for the SAME call_expression, and
        # both decoded the function child. Set by on_call, read by on_node.
        self._calltxt_id = -1
        self._calltxt_raw = ""
        # Per-file memo tables, cleared at the top of parse_file.
        self._name_memo: dict[int, str] = {}
        self._sig_memo: dict[int, str] = {}

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
        # The node-type tables never change after start-up, and `measure`
        # consults nine of them per body. Freeze them once here instead of
        # rebuilding ten sets per measured function.
        self._measure_sets = (
            frozenset(self.LOOP_NODES), frozenset(self.BRANCH_NODES),
            frozenset(self.NEST_NODES), frozenset(self.CALL_NODES),
            frozenset(self.OPERATOR_NODES), frozenset(self.STRING_NODES),
            frozenset(self.NUMBER_NODES), frozenset(self.COMMENT_NODES),
            frozenset(self.IF_NODES))
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
        # Per-file name/signature memos: node ids are unique within one tree,
        # and node_name/signature_of were each being recomputed up to four
        # times per function (scope walk, emission, flags, visibility).
        # Cleared here so ids from a previous tree can never be reused.
        self._name_memo = {}
        self._sig_memo = {}
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
        self.emit_input_sites(stats, sid, rec, bufs)
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
        # Bound once: this loop touches every named node in the file, and
        # each self.X below was an attribute walk per node.
        func_get = self.FUNC_KINDS.get
        type_get = self.TYPE_KINDS.get
        body_field = self.BODY_FIELD
        node_name = self.node_name
        while stack:
            cur, sc = stack.pop()
            kind = func_get(cur.type)
            if kind:
                sid = self.emit_function(cur, rec, db, bufs, sc, kind)
                inner = Scope(sid, "%s%s." % (sc.qual_prefix,
                                              node_name(cur, rec) or "?"),
                              sc.type_name, sc.type_id, sc.depth + 1)
                body = cur.child_by_field_name(body_field)
                for c in reversed((body or cur).named_children):
                    stack.append((c, inner))
                continue
            kind = type_get(cur.type)
            if kind:
                sid = self.emit_type(cur, rec, db, bufs, sc, kind)
                name = node_name(cur, rec) or "?"
                inner = Scope(sid, "%s%s." % (sc.qual_prefix, name),
                              name, sid, sc.depth + 1)
                body = cur.child_by_field_name(body_field)
                for c in reversed((body or cur).named_children):
                    stack.append((c, inner))
                continue
            for c in reversed(cur.named_children):
                stack.append((c, sc))

    # -- naming ------------------------------------------------------------
    def node_name(self, node: Any, rec: FileRec) -> str:
        # Memoised per file: the scope walk, symbol emission, flags and
        # visibility all asked for the same node's name, each a fresh decode.
        memo = self._name_memo
        nid = node.id
        hit = memo.get(nid)
        if hit is not None:
            return hit
        field = self.NAME_FIELD.get(node.type, self.DEFAULT_NAME_FIELD)
        if field:
            child = node.child_by_field_name(field)
            if child is not None:
                name = text_of(child, rec.data).strip()
                memo[nid] = name
                return name
        for c in node.named_children:
            if c.type in self.IDENT_NODES:
                name = text_of(c, rec.data).strip()
                memo[nid] = name
                return name
        memo[nid] = ""
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
        self.emit_input_sites(stats, sid, rec, bufs)
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
            # A defaults template plus a key->position index: the row is
            # filled from the template in one C-level extend and then
            # overwritten only for metrics actually present (~40-60 of ~230
            # columns), instead of probing m for every schema column.
            self._sym_defaults = [d for _, d in spec]
            base = 1 + len(cols)
            self._sym_idx = {n: base + i for i, (n, _) in enumerate(spec)}
        self._n_sym += 1
        sid = self._n_sym
        row = [sid]
        row.extend(vals)
        row.extend(self._sym_defaults)
        idx_get = self._sym_idx.get
        for k, v in m.items():
            j = idx_get(k)
            if j is not None:
                row[j] = int(v) if isinstance(v, bool) else v
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
        # Frozen once in setup(): rebuilding ten sets per measured body was
        # ~2013 x 10 set() allocations per repo for values that never change.
        loops, branches, nests, calls, operators, strings, numbers, comments, \
            ifs = self._measure_sets
        counters = self.COUNTERS
        flags = self.FLAG_NODES

        else_field = self.ELSE_FIELD
        want_elif = bool(ifs) and bool(else_field)
        extra_loops = self.extra_loop_ids(body, rec)
        # Locals beat attribute and global lookups in a loop run once per node.
        # `bump` is inlined as a bound dict get: this loop makes hundreds of
        # thousands of counter increments per repo.
        counts = st.counts
        counts_get = counts.get
        counters_get = counters.get
        flags_get = flags.get
        text_of_ = text_of
        on_call = self.on_call
        on_node = self.on_node
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
            if named and (t in loops or
                          (extra_loops and node.id in extra_loops)):
                loop_stack.append(depth)
                loop_depth += 1
                st.max_loop_depth = max(st.max_loop_depth, loop_depth)
                st.cyclomatic += 1
                st.cognitive += max(1, len(nest_stack))
                counts["n_loops"] = counts_get("n_loops", 0) + 1
            elif named and t in branches:
                st.cyclomatic += 1
                st.cognitive += 1 if is_elif else max(1, len(nest_stack))
                counts["n_branches"] = counts_get("n_branches", 0) + 1
                if is_elif:
                    counts["n_elif"] = counts_get("n_elif", 0) + 1
                if loop_depth:
                    counts["branch_in_loop"] = \
                        counts_get("branch_in_loop", 0) + 1

            key = counters_get(t)
            if key is not None:
                counts[key] = counts_get(key, 0) + 1
            fkey = flags_get(t)
            if fkey is not None:
                st.counts[fkey] = 1

            if t in calls:
                on_call(node, src, st, loop_depth, len(nest_stack))
            elif t in operators:
                st.n_operators += 1
                st.operators.add(t)
            elif t in strings:
                txt = text_of_(node, src)
                counts["n_string_lit"] = counts_get("n_string_lit", 0) + 1
                st.operands.add(txt[:40])
                st.n_operands += 1
                self.on_string(node, txt, src, st, loop_depth)
            elif t in numbers:
                txt = text_of_(node, src).strip()
                st.n_operands += 1
                st.operands.add(txt)
                magic = txt not in MAGIC_STR and NUM_RE.match(txt) is not None
                if magic:
                    counts["n_magic"] = counts_get("n_magic", 0) + 1
                    st.literals.append(("number", txt,
                                        node.start_point[0] + 1, True))
                if "." in txt or "e" in txt.lower():
                    counts["n_float_lit"] = counts_get("n_float_lit", 0) + 1
            elif t in comments:
                key = "n_comment_lines"
                counts[key] = counts_get(key, 0) + \
                    node.end_point[0] - node.start_point[0] + 1
            elif node.child_count == 0:
                st.n_tokens += 1
                st.n_operands += 1
                st.operands.add(text_of_(node, src)[:40])

            on_node(node, src, st, loop_depth, len(nest_stack))

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
        return _NO_EXTRA_LOOPS

    # -- per-node hooks a language may override ---------------------------
    def on_call(self, node: Any, src: bytes, st: BodyStats,
                loop_depth: int, nest: int) -> None:
        bump = st.bump
        bump("n_calls")
        if loop_depth:
            bump("call_in_loop")
        fn = node.child_by_field_name(self.CALL_FUNC_FIELD)
        line1 = node.start_point[0] + 1
        if fn is None:
            bump("n_dynamic_calls")
            st.calls.append(("", line1, True, bool(loop_depth)))
            return
        name = text_of(fn, src)
        self._calltxt_id = node.id
        self._calltxt_raw = name
        name = name.strip()
        base = name.rsplit(".", 1)[-1]
        if "." in name and name.split(".", 1)[0] in REQUEST_RECEIVERS:
            kind = REQUEST_METHOD_KINDS.get(base)
            if name.endswith(".URL.Query"):       # r.URL.Query() -> query;
                kind = "query"                    # base "Query" is also db/sql
            if kind is not None:
                st.input_sites.append(
                    (text_of(node, src)[:120], kind, line1,
                     bool(loop_depth)))
        if name == "http.Redirect":
            bump("n_redirect")                 # G26 open-redirect sink
        if (name.startswith("json.") and base in _DECODE_BASES) \
                or base == "Decode":
            # G19/G30: deserialization -- json.Unmarshal / NewDecoder().Decode
            # of whatever reaches the call; whether the input is untrusted is
            # the query's question, not this counter's.
            bump("n_deserialize")
        if name.startswith(("os.Open", "os.ReadFile", "os.WriteFile",
                            "os.Create")):
            args = node.child_by_field_name("arguments")
            first = args.named_children[0] if args is not None \
                and args.named_children else None
            if first is not None and first.type not in (
                    "interpreted_string_literal", "raw_string_literal"):
                # G12: os.* with a non-literal path -- the traversal sink
                bump("n_dynamic_open")
        if name.startswith("zip."):
            # G29: archive/zip access -- entry containment is a check, not a
            # name; this ranks where archives are opened.
            bump("n_zip_read")
        if _AUTH_CALL_RE.search(name) is not None:
            # G01: an auth-family call -- the marker that makes the
            # unauthenticated-input surface query exclude this function.
            bump("n_auth_call")

        # -- facts golangci-lint checks, recorded rather than judged ---------
        # Counters, never verdicts. `n_http_no_timeout` says the code built a
        # client without a timeout; whether that matters depends on whether a
        # request handler reaches it, which is a graph question. Rule ids are
        # cited so the original rationale stays findable.
        if name in ("context.Background", "context.TODO"):
            bump("n_ctx_background_call")     # containedctx / fatcontext
        if name in _HTTP_DEFAULT_CALLS:
            bump("n_http_default_client")     # noctx / bodyclose
        if base in _EXIT_BASES and \
                name.split(".", 1)[0] in _EXIT_PKGS:
            bump("n_exit_call")               # revive deep-exit
        if name == "time.After" and loop_depth:
            bump("n_time_after_in_loop")      # staticcheck SA1023-adjacent
        if name == "time.Tick":
            bump("n_time_tick_call")          # SA1015: leaks a ticker
        if name == "fmt.Errorf":
            txt = text_of(node, src)
            if "%w" not in txt:
                bump("n_errorf_no_wrap")      # errorlint / wrapcheck
        if name in _WEAK_RANDOM_CALLS:
            bump("n_weak_random")             # gosec G404
        if name in _WEAK_CRYPTO_CALLS:
            bump("n_weak_crypto")             # gosec G401/G403/G405
        if name in ("ioutil.ReadAll", "io.ReadAll") and loop_depth:
            bump("n_readall_in_loop")         # PERF: unbounded read per pass
        if name in ("os.Getenv", "os.LookupEnv"):
            bump("n_env_read")                # config surface
        if name in ("json.Unmarshal", "json.NewDecoder", "yaml.Unmarshal",
                    "gob.NewDecoder", "xml.Unmarshal"):
            bump("n_decode_call")             # decode surface for taint
        if name in ("sync.WaitGroup", "wg.Add") or base == "Add" and \
                name.startswith("wg."):
            bump("n_waitgroup_add")           # SA2000 family
        # -- concurrency-lifecycle facts (pack: waitgroup/timer/semaphore) ---
        # Pairing counters, not verdicts: whether a .Wait() is a WaitGroup's
        # or an errgroup's is the query's question, joined against
        # goroutines.has_waitgroup / has_errgroup.
        if base == "Done" and not name.startswith("ctx."):
            bump("n_wg_done")                 # balances n_waitgroup_add
            var = name.split(".", 1)[0]
            if "." in name and IDENT_RE.match(var):
                st.wg_ops.append((var, "Done", line1,
                                  in_goroutine(node), bool(loop_depth)))
        elif base == "Add" and "." in name:
            var = name.split(".", 1)[0]
            if IDENT_RE.match(var):
                st.wg_ops.append((var, "Add", line1,
                                  in_goroutine(node), bool(loop_depth)))
        if base == "Wait":
            bump("n_wait_call")               # wg.Wait / errgroup.Wait
            var = name.split(".", 1)[0] if "." in name else ""
            if IDENT_RE.match(var):
                st.wg_ops.append((var, "Wait", line1,
                                  in_goroutine(node), bool(loop_depth)))
        if name == "time.Sleep":
            bump("n_sleep")                   # latency / SA1004 family
        if base == "Err":
            bump("n_rows_err_check")          # rowserrcheck
        if name in ("time.NewTicker", "time.NewTimer", "time.AfterFunc") or \
                base in ("NewTicker", "NewTimer"):
            bump("n_timer_new")               # SA1015 leak family
        if base == "Stop":
            bump("n_timer_stop")              # the pairing side
        if base in ("SetLimit", "Acquire", "TryAcquire"):
            bump("n_semaphore")               # bounded fan-out idiom
        if base == "cancel":
            bump("n_cancel_called")           # go vet lostcancel
        if base in ("Lock", "RLock"):
            bump("n_lock_call")
        if base in ("Unlock", "RUnlock"):
            bump("n_unlock_call")
        if base == "Close":
            bump("n_close_call")              # bodyclose / sqlclosecheck
        if name in ("reflect.ValueOf", "reflect.TypeOf", "reflect.DeepEqual"):
            bump("n_reflect_call")            # perf + opacity
        if name in ("unsafe.Pointer", "unsafe.Sizeof", "unsafe.Slice",
                    "unsafe.String"):
            bump("n_unsafe_call")             # gosec G103
        if name in ("exec.Command", "exec.CommandContext", "syscall.Exec"):
            bump("n_exec_call")               # gosec G204
        if name in ("filepath.Join", "path.Join") and loop_depth:
            bump("n_pathjoin_in_loop")

        dynamic = not name or not name[0].isalpha() and name[0] not in "_$"
        st.calls.append((name[:200], line1, dynamic,
                         bool(loop_depth)))
        if dynamic:
            bump("n_dynamic_calls")
        if loop_depth:
            base = name.rsplit(".", 1)[-1].rsplit("::", 1)[-1]
            for needle, col in self.LOOP_CALL_COUNTERS.items():
                if needle == base or needle in name:
                    bump(col)

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

    def emit_input_sites(self, stats: BodyStats, sid: int, rec: FileRec,
                         bufs: Buffers) -> None:
        for var, kind, line, in_loop in stats.input_sites:
            bufs.rows("user_input_sites").append(
                (sid, rec.fid, var, kind, line, int(in_loop)))
        for sval, sline in stats.secrets:
            bufs.rows("secret_candidates").append(
                (sid, rec.fid, sval, sline))

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
        # Memoised per file: emit_function and function_flags both asked for
        # the same node's signature, each a fresh decode of the span.
        memo = self._sig_memo
        nid = node.id
        hit = memo.get(nid)
        if hit is not None:
            return hit
        body = node.child_by_field_name(self.BODY_FIELD)
        end = body.start_byte if body is not None else node.end_byte
        sig = rec.data[node.start_byte:end].decode("utf-8", "replace").strip()
        memo[nid] = sig
        return sig

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
# lang_go.py
# codegraph_go.py -- parse a Go tree into a graph and query it.
#
# Targets Go 1.26. Parses with tree-sitter-go.
#
# Go's compiler and `go vet` already catch most single-function mistakes, so this
# does not compete with them. What it adds is the shape no single-file checker
# can see: which goroutine spawned under a request handler has no way to stop,
# which context stops being propagated three frames down, which interface has
# exactly one implementation and is therefore an abstraction over nothing.
#
# Two Go facts this bakes in, both from reading go.mod rather than guessing:
#
# * Loop-variable capture was fixed in Go 1.22. Flagging `for _, v := range` +
#   `go func(){ use(v) }` in a module declaring `go 1.22` or later is a false
#   positive, so `n_loopvar_capture` is only counted below that line.
# * Since Go 1.26 `go mod init` writes `go 1.(N-1).0` rather than the toolchain
#   version, so the declared version now systematically lags. It is still the
#   right thing to read -- it is what the compiler uses.
#
# Usage:
#   python3 codegraph_go.py /path/to/repo --report
#   python3 codegraph_go.py /path/to/repo --list
#   python3 codegraph_go.py --deps
# ==========================================================================

DEPS = DepSet(lang="go", deps=[
    TREE_SITTER,
    grammar("Go", "tree_sitter_go", "tree-sitter-go>=0.25", "0.25.0 (ABI 15)"),
])

#: Longest error-propagation chain the error-fan-out pass will report.
#: An error chain through a recursive cycle is unbounded; 32 is the honest
#: ceiling and is stated in the query's MISLEADS.
ERROR_CHAIN_CAP = 32

HAZARD_CATEGORIES = (
    "goroutine", "channel", "defer", "lock", "atomic", "context", "io", "net",
    "sql", "exec", "unsafe", "reflect", "cgo", "alloc", "panic", "time",
)

#: Request-object receivers for user_input_sites. `w` is a ResponseWriter --
#: w.Header() SETS response headers and is not input -- so it is excluded.
REQUEST_RECEIVERS = frozenset(("r", "req", "request"))
REQUEST_METHOD_KINDS = {
    "FormValue": "query", "PostFormValue": "form",
    "Cookie": "cookie", "MultipartReader": "form",
}
REQUEST_FIELD_KINDS = {"Form": "form", "PostForm": "form",
                       "Header": "header", "Body": "body"}

#: G07: a string literal that names a credential (mirrors the other packs).
SECRET_RE = re.compile(
    r'(api[_-]?key|apikey|secret|password|passwd|pwd|token|bearer|'
    r'access[_-]?key|private[_-]?key|client[_-]?secret|'
    r'auth[_-]?token|jwt|credential|smtp[_-]?pass|db[_-]?pass|'
    r'sk_live|rk_live|pk_live|ghp_|xoxb-|AKIA)', re.I)
SECRET_MIN_LEN = 12

#: G01: auth-family markers (RequireAuth, CheckAuth, jwt, session, login).
AUTH_MARKERS = ("auth", "authorize", "authenticate", "login", "jwt",
                "session", "token")

#: Case-insensitive any-substring test over AUTH_MARKERS, compiled once. The
#: per-call-site equivalent of `any(k in name.lower() for k in AUTH_MARKERS)`
#: without a lower() copy and a generator frame per call node.
_AUTH_CALL_RE = re.compile(
    "|".join(re.escape(k) for k in AUTH_MARKERS), re.I)

#: Hot membership sets for on_call: these were inline tuples scanned
#: linearly at every call node in every function body.
_EXIT_BASES = frozenset(("Fatal", "Fatalf", "Fatalln", "Exit"))
_EXIT_PKGS = frozenset(("log", "os", "logrus", "klog"))
_HTTP_DEFAULT_CALLS = frozenset(("http.Get", "http.Post", "http.PostForm",
                                 "http.Head", "http.DefaultClient.Do"))
_DECODE_BASES = frozenset(("Unmarshal", "NewDecoder"))
_WEAK_RANDOM_CALLS = frozenset(("rand.Int", "rand.Intn", "rand.Float64",
                                "rand.Read", "rand.Int31", "rand.Int63"))
_WEAK_CRYPTO_CALLS = frozenset(("md5.New", "sha1.New", "md5.Sum", "sha1.Sum",
                                "des.NewCipher", "rc4.NewCipher"))

HAZARD_CALLS: dict[str, str] = {
    # goroutine / sync -- staticcheck SA2000, go vet waitgroup
    "sync.WaitGroup": "goroutine", "errgroup.Group": "goroutine",
    "errgroup.WithContext": "goroutine", "singleflight.Do": "goroutine",
    "sync.Once": "goroutine", "OnceFunc": "goroutine", "OnceValue": "goroutine",
    "runtime.Gosched": "goroutine", "runtime.GOMAXPROCS": "goroutine",
    "runtime.LockOSThread": "goroutine", "runtime.Goexit": "goroutine",
    "runtime.NumGoroutine": "goroutine",
    # channel -- SA1017 signal.Notify on an unbuffered channel drops signals
    "close": "channel", "signal.Notify": "channel", "signal.Stop": "channel",
    "signal.NotifyContext": "channel",
    # defer / panic containment
    "recover": "defer", "runtime.SetFinalizer": "defer",
    # lock -- go vet copylocks, SA2001 empty critical section
    "sync.Mutex": "lock", "sync.RWMutex": "lock", "Lock": "lock",
    "Unlock": "lock", "RLock": "lock", "RUnlock": "lock", "TryLock": "lock",
    "sync.Map": "lock", "LoadOrStore": "lock", "sync.Cond": "lock",
    "sync.Pool": "lock",
    # atomic -- SA1027 unaligned 64-bit access
    "atomic.AddInt64": "atomic", "atomic.LoadInt64": "atomic",
    "atomic.StoreInt64": "atomic", "atomic.CompareAndSwapInt64": "atomic",
    "atomic.CompareAndSwapPointer": "atomic", "atomic.Value": "atomic",
    "atomic.Int64": "atomic", "atomic.Bool": "atomic", "atomic.Pointer": "atomic",
    # context -- go vet lostcancel, SA1012 nil context
    "context.Background": "context", "context.TODO": "context",
    "context.WithCancel": "context", "context.WithTimeout": "context",
    "context.WithDeadline": "context", "context.WithValue": "context",
    "context.WithCancelCause": "context", "context.WithoutCancel": "context",
    "context.AfterFunc": "context",
    # io
    "os.Open": "io", "os.Create": "io", "os.OpenFile": "io", "os.ReadFile": "io",
    "os.WriteFile": "io", "os.Remove": "io", "os.RemoveAll": "io",
    "os.MkdirAll": "io", "os.Stat": "io", "os.ReadDir": "io",
    "io.Copy": "io", "io.ReadAll": "io", "ioutil.ReadAll": "io",
    "ioutil.ReadFile": "io", "bufio.NewReader": "io", "bufio.NewWriter": "io",
    "bufio.NewScanner": "io", "filepath.Walk": "io", "filepath.WalkDir": "io",
    "filepath.Glob": "io", "os.CreateTemp": "io",
    # net -- go vet httpresponse, golangci noctx / bodyclose
    "http.Get": "net", "http.Post": "net", "http.PostForm": "net",
    "http.NewRequest": "net", "http.NewRequestWithContext": "net",
    "http.ListenAndServe": "net", "http.ListenAndServeTLS": "net",
    "http.HandleFunc": "net", "http.Handle": "net", "http.Serve": "net",
    "net.Dial": "net", "net.DialTimeout": "net", "net.Listen": "net",
    "grpc.Dial": "net", "grpc.NewClient": "net",
    "httputil.NewSingleHostReverseProxy": "net",
    # sql -- rowserrcheck, sqlclosecheck
    "sql.Open": "sql", "QueryContext": "sql", "QueryRowContext": "sql",
    # The non-Context forms are the older half of database/sql and are still
    # most of what real code calls. Without them n_sql was 0 on every plain
    # Query/Exec and the N+1 query could not fire at all.
    "Query": "sql", "QueryRow": "sql", "Exec": "sql", "Prepare": "sql",
    "Begin": "sql", "Commit": "sql", "Rollback": "sql", "Scan": "sql",
    "ExecContext": "sql", "PrepareContext": "sql", "BeginTx": "sql",
    "gorm.Open": "sql", "Preload": "sql",
    # exec -- SA1005 invalid first argument to exec.Command
    "exec.Command": "exec", "exec.CommandContext": "exec",
    "exec.LookPath": "exec", "syscall.Exec": "exec", "syscall.Syscall": "exec",
    "os.Exit": "exec", "os.StartProcess": "exec",
    # unsafe -- go vet unsafeptr
    "unsafe.Pointer": "unsafe", "unsafe.Slice": "unsafe",
    "unsafe.String": "unsafe", "unsafe.Add": "unsafe",
    "unsafe.SliceData": "unsafe", "unsafe.StringData": "unsafe",
    "reflect.SliceHeader": "unsafe", "reflect.StringHeader": "unsafe",
    # reflect -- SA5008 struct tags, SA9005 marshal with no exported fields
    "reflect.TypeOf": "reflect", "reflect.ValueOf": "reflect",
    "reflect.New": "reflect", "reflect.DeepEqual": "reflect",
    "reflect.MakeSlice": "reflect", "json.Marshal": "reflect",
    "json.Unmarshal": "reflect", "json.NewDecoder": "reflect",
    "json.NewEncoder": "reflect", "yaml.Unmarshal": "reflect",
    "xml.Unmarshal": "reflect", "proto.Unmarshal": "reflect",
    "gob.NewDecoder": "reflect",
    # cgo
    "C.malloc": "cgo", "C.free": "cgo", "C.CString": "cgo",
    "C.GoString": "cgo", "C.GoBytes": "cgo", "C.CBytes": "cgo",
    "cgo.NewHandle": "cgo", "runtime.KeepAlive": "cgo", "runtime.Pinner": "cgo",
    # alloc -- prealloc, perfsprint, makezero, SA6002, SA6005
    "make": "alloc", "new": "alloc", "append": "alloc",
    "bytes.NewBuffer": "alloc", "bytes.NewBufferString": "alloc",
    "strings.Builder": "alloc", "strings.Repeat": "alloc",
    "strings.Split": "alloc", "strings.Join": "alloc", "strings.Fields": "alloc",
    "strings.NewReplacer": "alloc", "fmt.Sprintf": "alloc",
    "fmt.Sprint": "alloc", "fmt.Sprintln": "alloc", "fmt.Errorf": "alloc",
    "strconv.Itoa": "alloc", "strconv.FormatInt": "alloc",
    "regexp.Compile": "alloc", "regexp.MustCompile": "alloc",
    # panic -- log.Fatal in a library is an uncatchable process exit
    "panic": "panic", "log.Fatal": "panic", "log.Fatalf": "panic",
    "log.Fatalln": "panic", "log.Panic": "panic", "log.Panicf": "panic",
    "template.Must": "panic",
    # time -- SA1015 time.Tick leaks a ticker that can never be stopped
    "time.Sleep": "time", "time.After": "time", "time.Tick": "time",
    "time.NewTicker": "time", "time.NewTimer": "time", "time.AfterFunc": "time",
    "time.Now": "time", "time.Since": "time",
}

SQL_RE = re.compile(
    r'\b(SELECT|INSERT\s+INTO|UPDATE|DELETE\s+FROM|CREATE\s+TABLE|'
    r'DROP\s+TABLE|ALTER\s+TABLE)\b', re.I)

HANDLER_SIG_RE = re.compile(
    r'http\.ResponseWriter|\*http\.Request|gin\.Context|echo\.Context|'
    r'fiber\.Ctx|events\.APIGatewayProxyRequest|grpc\.ServerStream')

GO_DIRECTIVE_RE = re.compile(r'^//go:(\w+)', re.M)

BUILD_TAG_RE = re.compile(r'^//go:build\s+(.+)$', re.M)

GENERATED_RE = re.compile(r'^// Code generated .* DO NOT EDIT\.$', re.M)

# Per-function regexes in function_flags, compiled once: one ran for every
# method and closure in the tree, per symbol.
_RECV_TYPE_RE = re.compile(r'\*?([A-Za-z_]\w*)\s*(?:\[[^\]]*\])?\s*\)$')
_ANY_PARAM_RE = re.compile(r'\b(?:any|interface\s*\{\s*\})\b')
_IFACE_RETURN_RE = re.compile(r'\b(?:any|interface\s*\{\s*\}|error)\b')
_NAMED_RESULTS_RE = re.compile(r'\(\s*\w+\s+\w')

# go.mod scans, once per run.
_GOMOD_GO_RE = re.compile(r'^go\s+(\d+)\.(\d+)', re.M)
_GOMOD_MODULE_RE = re.compile(r'^module\s+(\S+)', re.M)

# Fixed-size array type in _est_size, once per struct field.
_ARRAY_LEN_RE = re.compile(r'^\[(\d+)\](.+)$')

STDLIB_ROOTS = frozenset("""
archive bufio builtin bytes cmp compress container context crypto database
debug embed encoding errors expvar flag fmt go hash html image index io iter
log maps math mime net os path plugin reflect regexp runtime slices sort
strconv strings structs sync syscall testing text time unicode unsafe unique
weak
""".split())

BUILTINS = frozenset("""
append cap clear close complex copy delete imag len make max min new panic
print println real recover any bool byte comparable complex64 complex128
error float32 float64 int int8 int16 int32 int64 rune string uint uint8
uint16 uint32 uint64 uintptr true false iota nil
""".split())

class GoAnalyzer(TreeSitterAnalyzer):
    LANG = "go"
    TARGET = "Go 1.26"
    EXTS = (".go",)
    SKIP_DIRS = {"testdata", "vendor"}
    DEPS = DEPS
    HAZARD_CATEGORIES = HAZARD_CATEGORIES
    MANIFESTS = ("go.mod", "go.sum", "go.work")

    #: Go has no executable top level -- only declarations and
    #: `init()`, which is already a function symbol.
    MODULE_SCOPE_SYMBOL = False

    GRAMMAR_MODULE = "tree_sitter_go"
    GRAMMAR_PIP = "tree-sitter-go>=0.25"

    FUNC_KINDS = {
        "function_declaration": "function",
        "method_declaration": "method",
        "func_literal": "closure",
    }
    TYPE_KINDS = {
        "type_spec": "type",
    }
    NAME_FIELD = {"func_literal": ""}
    IDENT_NODES = ("identifier", "field_identifier", "type_identifier",
                   "package_identifier")

    BODY_FIELD = "body"
    PARAMS_FIELD = "parameters"
    RETURN_FIELD = "result"
    ELSE_FIELD = "alternative"
    IF_NODES = ("if_statement",)

    #: `range_clause` is deliberately absent, for the same reason `block`
    #: is: it is a CHILD of `for_statement`, not a sibling of it. Go spells
    #: every range loop as a `for_statement` containing a `range_clause`,
    #: so listing both counted one loop twice -- `for v := range xs` came
    #: back with max_loop_depth 2 and n_loops 2, and two nested ranges
    #: reported depth 3 of 4 loops. Range is the dominant loop form in Go,
    #: so this inflated nearly every function in the language.
    LOOP_NODES = ("for_statement",)
    BRANCH_NODES = ("if_statement",)
    #: `block` is deliberately absent. Every `if` and every `for` owns a
    #: `block`, so counting both charges two levels for one, and a flat
    #: guard-clause function ends up ranked beside a genuinely pyramidal one.
    NEST_NODES = ("if_statement", "for_statement", "expression_switch_statement",
                  "type_switch_statement", "select_statement", "func_literal")
    CALL_NODES = ("call_expression",)
    CALL_FUNC_FIELD = "function"
    COMMENT_NODES = ("comment",)
    STRING_NODES = ("interpreted_string_literal", "raw_string_literal")
    NUMBER_NODES = ("int_literal", "float_literal", "imaginary_literal")
    OPERATOR_NODES = ("binary_expression", "unary_expression",
                      "assignment_statement", "inc_statement", "dec_statement",
                      "index_expression", "selector_expression",
                      "slice_expression", "type_assertion_expression")

    COUNTERS = {
        "return_statement": "n_returns",
        "go_statement": "n_goroutines",
        "defer_statement": "n_defer",
        "select_statement": "n_select",
        "expression_switch_statement": "n_switch",
        "type_switch_statement": "n_type_switch",
        "expression_case": "n_cases",
        "type_case": "n_cases",
        "default_case": "n_select_default",
        "send_statement": "n_chan_send",
        "channel_type": "n_chan_type",
        "func_literal": "n_lambda",
        "type_assertion_expression": "n_type_assert",
        "labeled_statement": "n_labels",
        "goto_statement": "n_gotos",
        "interface_type": "n_iface_literal",
        "composite_literal": "n_composite_lit",
        "type_parameter_list": "n_generic_params",
        "struct_type": "n_struct_literal",
        # Go assignments sat only in the Halstead operator counts, leaving
        # the universal n_assign / n_incdec columns at zero forever.
        "assignment_statement": "n_assign",
        "short_var_declaration": "n_assign",
        "inc_statement": "n_incdec",
        "dec_statement": "n_incdec",
    }
    LOOP_CALL_COUNTERS = {
        "Sprintf": "n_sprintf_in_loop",
        "append": "n_append_in_loop",
        "MustCompile": "regex_in_loop",
        "Compile": "regex_in_loop",
        "Lock": "lock_in_loop",
        "QueryContext": "query_in_loop",
        "Query": "query_in_loop",
        "ExecContext": "query_in_loop",
        # A context deadline/cancel created PER ITERATION leaks a timer each
        # pass (context.WithTimeout) or can never fire (WithCancel recreated
        # every loop) -- the context-built-in-loop query ranks these.
        "WithTimeout": "n_ctx_in_loop",
        "WithDeadline": "n_ctx_in_loop",
        "WithCancel": "n_ctx_in_loop",
    }

    EXTRA_SYMBOL_COLS = (
        ("n_goroutines", "INT NOT NULL DEFAULT 0"),
        ("n_go_in_loop", "INT NOT NULL DEFAULT 0"),
        ("n_defer_in_loop", "INT NOT NULL DEFAULT 0"),
        ("n_defer_close", "INT NOT NULL DEFAULT 0"),
        ("n_recover", "INT NOT NULL DEFAULT 0"),
        ("n_chan_send", "INT NOT NULL DEFAULT 0"),
        ("n_chan_recv", "INT NOT NULL DEFAULT 0"),
        ("n_chan_close", "INT NOT NULL DEFAULT 0"),
        ("n_chan_type", "INT NOT NULL DEFAULT 0"),
        ("n_chan_unbuffered", "INT NOT NULL DEFAULT 0"),
        ("n_select", "INT NOT NULL DEFAULT 0"),
        ("n_select_default", "INT NOT NULL DEFAULT 0"),
        ("n_select_ctx_done", "INT NOT NULL DEFAULT 0"),
        ("n_type_switch", "INT NOT NULL DEFAULT 0"),
        ("n_type_assert", "INT NOT NULL DEFAULT 0"),
        ("n_type_assert_unchecked", "INT NOT NULL DEFAULT 0"),
        ("n_ctx_params", "INT NOT NULL DEFAULT 0"),
        ("n_ctx_background", "INT NOT NULL DEFAULT 0"),
        ("n_ctx_done", "INT NOT NULL DEFAULT 0"),
        ("n_ctx_passed", "INT NOT NULL DEFAULT 0"),
        ("n_ctx_withcancel", "INT NOT NULL DEFAULT 0"),
        ("n_cancel_called", "INT NOT NULL DEFAULT 0"),
        ("n_err_returns", "INT NOT NULL DEFAULT 0"),
        ("n_err_checks", "INT NOT NULL DEFAULT 0"),
        ("n_err_ignored", "INT NOT NULL DEFAULT 0"),
        ("n_err_shadowed", "INT NOT NULL DEFAULT 0"),
        ("n_err_wrapped", "INT NOT NULL DEFAULT 0"),
        ("n_naked_returns", "INT NOT NULL DEFAULT 0"),
        ("n_named_results", "INT NOT NULL DEFAULT 0"),
        ("n_any_params", "INT NOT NULL DEFAULT 0"),
        ("n_iface_params", "INT NOT NULL DEFAULT 0"),
        ("n_iface_returns", "INT NOT NULL DEFAULT 0"),
        ("n_iface_literal", "INT NOT NULL DEFAULT 0"),
        ("n_make_no_cap", "INT NOT NULL DEFAULT 0"),
        ("n_append_in_loop", "INT NOT NULL DEFAULT 0"),
        ("n_sprintf_in_loop", "INT NOT NULL DEFAULT 0"),
        ("n_conv_in_loop", "INT NOT NULL DEFAULT 0"),
        ("n_range_value_copy", "INT NOT NULL DEFAULT 0"),
        ("n_loopvar_capture", "INT NOT NULL DEFAULT 0"),
        ("n_composite_lit", "INT NOT NULL DEFAULT 0"),
        ("n_struct_literal", "INT NOT NULL DEFAULT 0"),
        ("n_unsafe_ops", "INT NOT NULL DEFAULT 0"),
        ("n_cgo_calls", "INT NOT NULL DEFAULT 0"),
        ("n_reflect_ops", "INT NOT NULL DEFAULT 0"),
        ("n_go_directives", "INT NOT NULL DEFAULT 0"),
        ("n_struct_tags", "INT NOT NULL DEFAULT 0"),
        ("n_panics", "INT NOT NULL DEFAULT 0"),
        ("n_log_fatal", "INT NOT NULL DEFAULT 0"),
        ("n_time_tick", "INT NOT NULL DEFAULT 0"),
        ("n_sql_concat", "INT NOT NULL DEFAULT 0"),
        ("n_lock_by_value_params", "INT NOT NULL DEFAULT 0"),
        ("n_nolint", "INT NOT NULL DEFAULT 0"),
        #: Facts golangci-lint's members check, recorded so SQL can combine them
    #: with the call graph. A count, never a judgement: whether a
    #: context.Background() deep in a call chain is wrong depends on whether
    #: something above it had a real context to pass, and only the graph knows.
    ("n_ctx_background_call", "INT NOT NULL DEFAULT 0"),   # containedctx
    ("n_http_default_client", "INT NOT NULL DEFAULT 0"),   # noctx/bodyclose
    ("n_exit_call", "INT NOT NULL DEFAULT 0"),             # revive deep-exit
    ("n_time_after_in_loop", "INT NOT NULL DEFAULT 0"),
    ("n_time_tick_call", "INT NOT NULL DEFAULT 0"),        # SA1015
    ("n_errorf_no_wrap", "INT NOT NULL DEFAULT 0"),        # errorlint
    ("n_weak_random", "INT NOT NULL DEFAULT 0"),           # G404
    ("n_weak_crypto", "INT NOT NULL DEFAULT 0"),           # G401/G403/G405
    ("n_readall_in_loop", "INT NOT NULL DEFAULT 0"),
    ("n_env_read", "INT NOT NULL DEFAULT 0"),
    ("n_redirect", "INT NOT NULL DEFAULT 0"),            # G26 http.Redirect
    ("n_auth_call", "INT NOT NULL DEFAULT 0"),           # G01 auth family
    # -- OWASP P2 pack: sinks for the input-surface family ---------------
    ("n_deserialize", "INT NOT NULL DEFAULT 0"),         # G19/G30 decode
    ("n_dynamic_open", "INT NOT NULL DEFAULT 0"),        # G12 os.* with var
    ("n_zip_read", "INT NOT NULL DEFAULT 0"),            # G29 archive/zip
    ("n_decode_call", "INT NOT NULL DEFAULT 0"),
    ("n_waitgroup_add", "INT NOT NULL DEFAULT 0"),
    ("n_lock_call", "INT NOT NULL DEFAULT 0"),
    ("n_unlock_call", "INT NOT NULL DEFAULT 0"),
    ("n_close_call", "INT NOT NULL DEFAULT 0"),            # bodyclose
    ("n_reflect_call", "INT NOT NULL DEFAULT 0"),
    ("n_unsafe_call", "INT NOT NULL DEFAULT 0"),           # G103
    ("n_exec_call", "INT NOT NULL DEFAULT 0"),             # G204
    ("n_pathjoin_in_loop", "INT NOT NULL DEFAULT 0"),
    ("n_elif", "INT NOT NULL DEFAULT 0"),
        ("n_external_calls", "INT NOT NULL DEFAULT 0"),
        ("receiver_is_pointer", "INT NOT NULL DEFAULT 0"),
        ("receiver_type", "TEXT NOT NULL DEFAULT ''"),
        ("is_handler", "INT NOT NULL DEFAULT 0"),
        ("is_init", "INT NOT NULL DEFAULT 0"),
        # -- P2 pack: context/error/tls/loopvar discipline -----------------
        ("n_ctx_in_loop", "INT NOT NULL DEFAULT 0"),
        ("n_err_nil_return", "INT NOT NULL DEFAULT 0"),
        ("n_loopvar_rebind", "INT NOT NULL DEFAULT 0"),
        ("n_insecure_tls", "INT NOT NULL DEFAULT 0"),
        # -- concurrency-lifecycle pack: pairing counters. Counts only; the
        # judgement (Add inside the goroutine, ticker never stopped, fan-out
        # with no semaphore) needs the call graph, which is the query's job.
        ("n_wg_done", "INT NOT NULL DEFAULT 0"),      # balances wg.Add
        ("n_wait_call", "INT NOT NULL DEFAULT 0"),    # wg.Wait/errgroup.Wait
        ("n_sleep", "INT NOT NULL DEFAULT 0"),        # time.Sleep sites
        ("n_rows_err_check", "INT NOT NULL DEFAULT 0"),   # rowserrcheck
        ("n_timer_new", "INT NOT NULL DEFAULT 0"),    # SA1015 NewTicker/Timer
        ("n_timer_stop", "INT NOT NULL DEFAULT 0"),   # the pairing side
        ("n_semaphore", "INT NOT NULL DEFAULT 0"),    # SetLimit/Acquire
    )

    SCHEMA_EXT = r"""
CREATE TABLE goroutines(
    id INTEGER PRIMARY KEY,
    symbol_id INT NOT NULL REFERENCES symbols(id),
    file_id INT NOT NULL REFERENCES files(id),
    line INT NOT NULL,
    is_closure INT NOT NULL DEFAULT 0,
    target TEXT NOT NULL DEFAULT '',
    has_ctx INT NOT NULL DEFAULT 0,
    has_recover INT NOT NULL DEFAULT 0,
    has_waitgroup INT NOT NULL DEFAULT 0,
    has_errgroup INT NOT NULL DEFAULT 0,
    has_chan_exit INT NOT NULL DEFAULT 0,
    in_loop INT NOT NULL DEFAULT 0,
    loop_depth INT NOT NULL DEFAULT 0,
    body_sloc INT NOT NULL DEFAULT 0
) STRICT;

CREATE TABLE defers(
    id INTEGER PRIMARY KEY,
    symbol_id INT NOT NULL REFERENCES symbols(id),
    line INT NOT NULL,
    target TEXT NOT NULL DEFAULT '',
    in_loop INT NOT NULL DEFAULT 0,
    loop_depth INT NOT NULL DEFAULT 0,
    is_close INT NOT NULL DEFAULT 0,
    is_unlock INT NOT NULL DEFAULT 0,
    is_done INT NOT NULL DEFAULT 0
) STRICT;

CREATE TABLE channels(
    id INTEGER PRIMARY KEY,
    symbol_id INT REFERENCES symbols(id),
    file_id INT NOT NULL REFERENCES files(id),
    name TEXT NOT NULL DEFAULT '',
    elem_type TEXT NOT NULL DEFAULT '',
    capacity INT NOT NULL DEFAULT 0,
    line INT NOT NULL,
    closed_in_fn INT NOT NULL DEFAULT 0
) STRICT;

CREATE TABLE interfaces(
    symbol_id INT NOT NULL PRIMARY KEY REFERENCES symbols(id),
    n_methods INT NOT NULL DEFAULT 0,
    n_embedded INT NOT NULL DEFAULT 0,
    is_exported INT NOT NULL DEFAULT 0,
    is_constraint INT NOT NULL DEFAULT 0,
    methods TEXT NOT NULL DEFAULT ''
) WITHOUT ROWID, STRICT;

CREATE TABLE structs(
    symbol_id INT NOT NULL PRIMARY KEY REFERENCES symbols(id),
    n_fields INT NOT NULL DEFAULT 0,
    n_embedded INT NOT NULL DEFAULT 0,
    n_exported_fields INT NOT NULL DEFAULT 0,
    est_size INT NOT NULL DEFAULT 0,
    est_padding INT NOT NULL DEFAULT 0,
    size_exact INT NOT NULL DEFAULT 0,
    has_mutex INT NOT NULL DEFAULT 0,
    has_ctx_field INT NOT NULL DEFAULT 0,
    n_tagged_fields INT NOT NULL DEFAULT 0
) WITHOUT ROWID, STRICT;

CREATE TABLE implements(
    type_name TEXT NOT NULL,
    interface_id INT NOT NULL REFERENCES symbols(id),
    interface_name TEXT NOT NULL,
    n_methods INT NOT NULL DEFAULT 0,
    in_test INT NOT NULL DEFAULT 0,
    PRIMARY KEY(type_name, interface_id)
) WITHOUT ROWID, STRICT;

CREATE TABLE build_tags(
     id INTEGER PRIMARY KEY,
     file_id INT NOT NULL REFERENCES files(id),
     expr TEXT NOT NULL,
     line INT NOT NULL
 ) STRICT;
 
 -- Longest transitive import chain starting at each module, computed in
 -- Python (the import graph is a DAG; SQL recursion would re-expand paths).
 CREATE TABLE module_depth(
     module_id INT NOT NULL PRIMARY KEY REFERENCES modules(id),
     max_depth INT NOT NULL DEFAULT 0,
     n_direct_imports INT NOT NULL DEFAULT 0,
     n_transitive INT NOT NULL DEFAULT 0
 ) WITHOUT ROWID, STRICT;
 
 -- Longest error-propagation chain starting at each error-returning
 -- function, computed in Python: max_depth is the length of the longest
 -- path f -> g -> h where every hop's callee RETURNS error. A function
 -- whose callees absorb errors terminates a chain at depth 1. Only
 -- symbols with n_err_returns > 0 appear.
 CREATE TABLE error_chain_depth(
     symbol_id INT NOT NULL PRIMARY KEY REFERENCES symbols(id),
     max_depth INT NOT NULL DEFAULT 0
 ) WITHOUT ROWID, STRICT;

 CREATE TABLE user_input_sites(
     id INTEGER PRIMARY KEY,
     symbol_id INT REFERENCES symbols(id),
     file_id INT NOT NULL REFERENCES files(id),
     var TEXT NOT NULL DEFAULT '',
     kind TEXT NOT NULL DEFAULT 'query',
     line INT NOT NULL,
     in_loop INT NOT NULL DEFAULT 0
 ) STRICT;

 CREATE TABLE secret_candidates(
     id INTEGER PRIMARY KEY,
     symbol_id INT REFERENCES symbols(id),
     file_id INT NOT NULL REFERENCES files(id),
     value TEXT NOT NULL,
     line INT NOT NULL
 ) STRICT;

 -- WaitGroup Add/Done/Wait call sites, per WaitGroup VARIABLE (staticcheck
 -- SA2000 family). The Add usually lives in the spawner and the Done in the
 -- spawned function, so pairing them is a cross-function fact no per-file
 -- checker can see; in_goroutine marks sites lexically inside the `go` body.
 CREATE TABLE wg_sites(
     id INTEGER PRIMARY KEY,
     symbol_id INT NOT NULL REFERENCES symbols(id),
     file_id INT NOT NULL REFERENCES files(id),
     line INT NOT NULL,
     var TEXT NOT NULL DEFAULT '',
     op TEXT NOT NULL,
     in_goroutine INT NOT NULL DEFAULT 0,
     in_loop INT NOT NULL DEFAULT 0
 ) STRICT;
 """

    INDEX_EXT = r"""
-- parse-coverage joins build_tags by file; the planner was building this.
CREATE INDEX idx_buildtags_file ON build_tags(file_id);
CREATE INDEX idx_gor_sym ON goroutines(symbol_id);
CREATE INDEX idx_gor_leak ON goroutines(symbol_id)
    WHERE has_ctx=0 AND has_waitgroup=0 AND has_errgroup=0;
CREATE INDEX idx_def_loop ON defers(symbol_id) WHERE in_loop=1;
CREATE INDEX idx_chan_unbuf ON channels(symbol_id) WHERE capacity=0;
CREATE INDEX idx_iface_exp ON interfaces(is_exported, n_methods);
CREATE INDEX idx_impl_iface ON implements(interface_id, in_test);
CREATE INDEX idx_struct_mutex ON structs(symbol_id) WHERE has_mutex=1;
CREATE INDEX idx_fn_handler ON symbols(name, file_id) WHERE is_handler=1;
CREATE INDEX idx_fn_ctxbg ON symbols(n_ctx_background DESC, name)
    WHERE n_ctx_background>0;
CREATE INDEX idx_fn_errign ON symbols(n_err_ignored DESC, name)
    WHERE n_err_ignored>0;
CREATE INDEX idx_errchain ON error_chain_depth(max_depth DESC)
    WHERE max_depth > 1;
CREATE INDEX idx_uinput_sym ON user_input_sites(symbol_id, kind);
CREATE INDEX idx_uinput_kind ON user_input_sites(kind, line) WHERE in_loop=1;
CREATE INDEX idx_secret_sym ON secret_candidates(symbol_id);
CREATE INDEX idx_wg_sym ON wg_sites(symbol_id, op);
"""

    VIEW_EXT = r"""
CREATE VIEW v_goroutine AS
SELECT g.id, s.name AS in_fn, s.qual_name, f.path, g.line, g.is_closure,
    g.has_ctx, g.has_recover, g.has_waitgroup, g.has_errgroup,
    g.in_loop, g.loop_depth, s.is_handler, s.n_ctx_params,
    f.path || ':' || g.line AS at
FROM goroutines g
JOIN symbols s ON s.id=g.symbol_id
JOIN files f ON f.id=g.file_id;

CREATE VIEW v_iface_impls AS
SELECT i.symbol_id AS iface_id, s.name AS iface, i.n_methods,
    i.is_exported, i.is_constraint,
    (SELECT COUNT(*) FROM params p WHERE substr(p.type, -length(s.name)) = s.name
           AND (length(p.type) = length(s.name)
                OR instr('abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_', substr(p.type, -length(s.name)-1, 1)) = 0)) AS used_as_param
FROM interfaces i JOIN symbols s ON s.id=i.symbol_id;
"""

    MATERIALIZE_EXT = r"""
UPDATE symbols AS s SET n_unique_calls = x.c FROM
    (SELECT caller_id AS id, COUNT(*) AS c FROM edges GROUP BY caller_id) AS x
    WHERE x.id = s.id;

UPDATE symbols AS s SET n_go_in_loop = x.c FROM
    (SELECT symbol_id AS id, COUNT(*) AS c FROM goroutines
     WHERE in_loop=1 GROUP BY symbol_id) AS x WHERE x.id = s.id;

UPDATE symbols AS s SET n_defer_in_loop = x.c FROM
    (SELECT symbol_id AS id, COUNT(*) AS c FROM defers
     WHERE in_loop=1 GROUP BY symbol_id) AS x WHERE x.id = s.id;

UPDATE symbols AS s SET n_defer_close = x.c FROM
    (SELECT symbol_id AS id, COUNT(*) AS c FROM defers
     WHERE is_close=1 GROUP BY symbol_id) AS x WHERE x.id = s.id;
"""

    RISK_SQL = (
        "cyclomatic*2 + cognitive + max_nesting*4"
        " + n_unsafe*12 + n_cgo*10 + n_exec*15 + n_reflect*2"
        " + n_err_ignored*8 + n_err_shadowed*10"
        " + n_goroutines*4 + n_go_in_loop*12 + n_defer_in_loop*10"
        " + n_ctx_background*6 + n_panics*6 + n_log_fatal*8"
        " + n_sql_concat*25 + query_in_loop*15 + n_time_tick*8"
        " + lock_in_loop*8 + n_type_assert_unchecked*5"
        " + (CASE WHEN is_recursive THEN 12 ELSE 0 END)"
        " + (CASE WHEN is_handler=1 AND n_ctx_params=0 THEN 10 ELSE 0 END)"
    )

    def __init__(self) -> None:
        super().__init__()
        self.go_version = ""
        self.loopvar_fixed = True

    # -- language-specific extraction --------------------------------------
    def visibility_of(self, node: Any, rec: FileRec) -> str:
        name = self.node_name(node, rec)
        return "public" if name[:1].isupper() else "private"

    def function_flags(self, node: Any, rec: FileRec,
                       scope: Scope) -> dict[str, Any]:
        name = self.node_name(node, rec)
        sig = self.signature_of(node, rec)
        recv = node.child_by_field_name("receiver")
        recv_type = ""
        recv_ptr = 0
        if recv is not None:
            rtxt = text_of(recv, rec.data)
            recv_ptr = 1 if "*" in rtxt else 0
            m = _RECV_TYPE_RE.search(rtxt.strip())
            recv_type = m.group(1) if m else ""
        params = node.child_by_field_name("parameters")
        ptxt = text_of(params, rec.data) if params is not None else ""
        result = node.child_by_field_name("result")
        rtxt = text_of(result, rec.data) if result is not None else ""
        return dict(
            is_public=1 if name[:1].isupper() else 0,
            is_test=1 if name.startswith(("Test", "Benchmark", "Fuzz",
                                          "Example")) else 0,
            is_entrypoint=1 if name in ("main", "init") else 0,
            is_init=1 if name == "init" else 0,
            is_handler=1 if HANDLER_SIG_RE.search(sig) else 0,
            receiver_is_pointer=recv_ptr,
            receiver_type=recv_type,
            n_ctx_params=ptxt.count("context.Context"),
            n_any_params=len(_ANY_PARAM_RE.findall(ptxt)),
            n_iface_params=ptxt.count("interface{") + ptxt.count(" any"),
            n_iface_returns=1 if _IFACE_RETURN_RE.search(rtxt) else 0,
            n_named_results=1 if _NAMED_RESULTS_RE.search(rtxt) else 0,
            n_generic_params=1 if node.child_by_field_name(
                "type_parameters") is not None else 0,
        )

    def type_flags(self, node: Any, rec: FileRec,
                   scope: Scope) -> dict[str, Any]:
        name = self.node_name(node, rec)
        return dict(is_public=1 if name[:1].isupper() else 0)

    def on_node(self, node: Any, src: bytes, st: BodyStats,
                loop_depth: int, nest: int) -> None:
        t = node.type
        if t not in _GO_ONNODE_TYPES:
            return
        bump = st.bump
        if t == "binary_expression":
            # `&&` and `||` are decision points: each one is another path
            # through the function, so each adds to cyclomatic complexity.
            # Without this Go's complexity was understated everywhere, and
            # `n_logical` was 0 across all 114,490 symbols of kubernetes --
            # in a language that uses `err != nil &&` constantly.
            op = node.child_by_field_name("operator")
            o = _txt(op, src) if op is not None else ""
            if o in ("&&", "||"):
                bump("n_logical")
                st.cyclomatic += 1
            elif o in ("==", "!=", "<", ">", "<=", ">="):
                bump("n_cmp")
            elif o in ("&", "|", "^", "&^"):
                bump("n_bitop")
            elif o in ("<<", ">>"):
                bump("n_shift")
            elif o in ("+", "-", "*", "/", "%"):
                bump("n_arith")
        elif t == "selector_expression":
            # Hoisted above the rarer kinds: `pkg.Type.Field`-style selectors
            # are among the most frequent compound nodes in Go source, and
            # this branch used to sit behind ten string comparisons.
            op = node.child_by_field_name("operand")
            fld = node.child_by_field_name("field")
            if op is None or fld is None:
                return
            o = _txt(op, src).strip()
            f = _txt(fld, src).strip()
            if o not in REQUEST_RECEIVERS or f not in REQUEST_FIELD_KINDS:
                return
            if f == "URL":
                par = node.parent
                if par is not None and par.type == "call_expression":
                    fn = par.child_by_field_name("function")
                    if fn is not None and fn.id == node.id:
                        return        # r.URL.Query() handled as a call
            st.input_sites.append(
                (text_of(node, src)[:120], REQUEST_FIELD_KINDS[f],
                 node.start_point[0] + 1, bool(loop_depth)))
        elif t == "call_expression":
            # on_call already decoded this node's function text (measure runs
            # the two hooks back to back for a call node); reuse it.
            if self._calltxt_id == node.id:
                txt = self._calltxt_raw
            else:
                txt = _txt(node.child_by_field_name("function") or node, src)
            if txt == "recover":
                bump("n_recover")
            elif txt == "panic":
                bump("n_panics")
            elif txt.startswith("log.Fatal") or txt.startswith("log.Panic"):
                bump("n_log_fatal")
            elif txt == "close":
                bump("n_chan_close")
                a = node.child_by_field_name("arguments")
                if a is not None and a.named_children:
                    cv = _txt(a.named_children[0], src).strip()
                    if cv:
                        st.close_vars.append(cv[:80])
            elif txt == "make":
                args = node.child_by_field_name("arguments")
                if args is not None:
                    kids = [k for k in args.named_children]
                    atxt = _txt(args, src)
                    if "chan" in atxt and len(kids) < 2:
                        bump("n_chan_unbuffered")
                    elif atxt.startswith("([]") and len(kids) < 3:
                        bump("n_make_no_cap")
                    if "chan" in atxt:
                        # Channel declarations feed the channels table. This
                        # append used to live in a second `call_expression`
                        # branch further down -- unreachable, because this
                        # branch already matched the node type -- so
                        # `channels` was empty on every build.
                        st.extra_rows.append(("chan", node, 0))
            elif txt == "time.Tick":
                bump("n_time_tick")
            elif txt.startswith("context.Background") or \
                    txt.startswith("context.TODO"):
                bump("n_ctx_background")
            elif txt.startswith("context.With"):
                bump("n_ctx_withcancel")
            elif txt.endswith(".Done"):
                bump("n_ctx_done")
            elif txt.startswith("fmt.Errorf"):
                a = node.child_by_field_name("arguments")
                if a is not None and "%w" in _txt(a, src):
                    bump("n_err_wrapped")
            elif txt.startswith("unsafe."):
                bump("n_unsafe_ops")
            elif txt.startswith("C."):
                bump("n_cgo_calls")
            elif txt.startswith("reflect."):
                bump("n_reflect_ops")
            if loop_depth and (txt.startswith("string(")
                               or txt.startswith("[]byte")):
                bump("n_conv_in_loop")
        elif t == "if_statement":
            txt = _txt(node, src)[:160]
            if _ERR_NIL_CHECK_RE.search(txt):
                bump("n_err_checks")
                # nil-error-after-check: the error check leads to a nil
                # return -- the error is dropped at the moment it was
                # detected (nilerr). `return nil, err` is the honest shape.
                cons = node.child_by_field_name("consequence")
                if cons is not None:
                    ctxt = _txt(cons, src)[:200]
                    if _RETURN_NIL_RE.search(ctxt) \
                            and not _RETURN_NIL_ERR_RE.search(ctxt):
                        bump("n_err_nil_return")
            if _COMMA_ERR_ASSIGN_RE.search(txt):
                bump("n_err_shadowed")
        elif t == "assignment_statement" or t == "short_var_declaration":
            txt = _txt(node, src)[:200]
            if _BLANK_ASSIGN_RE.match(txt):
                bump("n_err_ignored")
            elif _BLANK_DISCARD_RE.search(txt) and "_" in txt:
                pass
            if t == "short_var_declaration":
                # `v := v` -- the dead rebind loopvar pattern (go >= 1.22
                # no longer copies per iteration, so the rebind is a lie).
                m = _LOOPVAR_REBIND_RE.match(txt)
                if m:
                    bump("n_loopvar_rebind")
        elif t == "return_statement":
            if not node.named_children:
                bump("n_naked_returns")
            else:
                rt = _txt(node, src)
                # Case-insensitive: `return fmt.Errorf(...)` is the dominant
                # error return and was invisible to a lowercase-only match.
                if "err" in rt.lower():
                    bump("n_err_returns")
        elif t == "unary_expression":
            if node.child_count and node.children[0].type == "<-":
                bump("n_chan_recv")
        elif t == "composite_literal":
            # tls.Config{InsecureSkipVerify: true} -- the accepted-insecure
            # shape gosec G402 hunts by AST; the text scan sees it too.
            ty = node.child_by_field_name("type")
            if ty is not None and "tls.Config" in _txt(ty, src) \
                    and "InsecureSkipVerify" in _txt(node, src)[:400]:
                bump("n_insecure_tls")
        elif t == "type_assertion_expression":
            parent = node.parent
            if parent is None or parent.type not in (
                    "assignment_statement", "short_var_declaration",
                    "expression_list"):
                bump("n_type_assert_unchecked")
        elif t == "field_declaration":
            if "`" in _txt(node, src):
                bump("n_struct_tags")
        elif t == "communication_case":
            txt = _txt(node, src)
            if "ctx.Done()" in txt or ".Done()" in txt:
                bump("n_select_ctx_done")
        elif t == "channel_type":
            pass
        elif t == "range_clause" and loop_depth:
            txt = _txt(node, src)[:120]
            if _RANGE_COPY_RE.match(txt):
                bump("n_range_value_copy")
        elif t == "go_statement":
            st.extra_rows.append(("go", node, loop_depth))
        elif t == "defer_statement":
            st.extra_rows.append(("defer", node, loop_depth))
        # (The old second `call_expression` branch that appended ("chan", ...)
        # here was unreachable -- the first branch above already matched the
        # node type -- so the make(chan) append moved up into it.)

    def on_string(self, node: Any, text: str, src: bytes, st: BodyStats,
                  loop_depth: int) -> None:
        val = text.strip('"\'')
        if len(val) >= SECRET_MIN_LEN and " " not in val \
            and SECRET_RE.search(val):
            # G07: credential-shaped literal -- candidate, not verdict
            st.secrets.append((val[:200], node.start_point[0] + 1))
        if SQL_RE.search(text):
            st.bump("n_sql_literal")
            parent = node.parent
            if parent is not None and parent.type in (
                    "binary_expression",) and "+" in _txt(parent, src)[:400]:
                st.bump("n_sql_concat")
            if loop_depth:
                st.bump("query_in_loop")

    def hazard_of(self, callee: str) -> Optional[tuple[str, str]]:
        cat = HAZARD_CALLS.get(callee)
        if cat is not None:
            return callee, cat
        # A bare name's rsplit would return the name itself, which the lookup
        # above already missed -- skip the allocation for every miss.
        if "." not in callee:
            return None
        base = callee.rsplit(".", 1)[-1]
        cat = HAZARD_CALLS.get(base)
        if cat is not None:
            return "*." + base, cat
        return None

    def is_external(self, name: str, base: str, fid: int) -> bool:
        if base in BUILTINS and "." not in name:
            return True
        head = name.split(".")[0]
        return head in STDLIB_ROOTS or head == "C" or (
            head and head[0].islower() and "." in name
            and head not in self.by_name)

    # -- goroutines, defers, channels, interfaces, structs -----------------
    def function_extra(self, node: Any, rec: FileRec, db: sqlite3.Connection,
                       bufs: Buffers, sid: int, scope: Scope,
                       stats: BodyStats) -> None:
        # Rows are captured during measure's single body walk (see on_node),
        # which tracks loop_depth itself -- this used to re-walk the whole body
        # per symbol, 50% of the analyzer's wall time on kubernetes.
        src = rec.data
        for var, op, line, in_go, in_loop in stats.wg_ops:
            bufs.rows("wg_sites").append(
                (sid, rec.fid, line, var, op, in_go, int(in_loop)))
        for kind, n, depth in stats.extra_rows:
            if kind == "go":
                inner = n.named_children[0] if n.named_children else None
                target = ""
                closure = 0
                btxt = ""
                if inner is not None:
                    fn = inner.child_by_field_name("function")
                    if fn is not None:
                        target = _txt(fn, src)[:120]
                        closure = 1 if fn.type == "func_literal" else 0
                    btxt = _txt(inner, src)
                bufs.rows("goroutines").append(
                    (sid, rec.fid, n.start_point[0] + 1, closure, target,
                     int(".Done()" in btxt or "ctx." in btxt),
                     int("recover(" in btxt),
                     int(".Done()" in btxt and "wg." in btxt
                         or "wg.Done" in btxt or "WaitGroup" in btxt),
                     int("errgroup" in btxt or "g.Go(" in btxt),
                     int("<-" in btxt),
                     int(depth > 0), depth,
                     btxt.count("\n") + 1))
                # wg ops lexically inside the spawned body belong to the
                # SPAWNER's pairing story (SA2000: Add inside the goroutine).
                # on_call already recorded them under the closure symbol's id;
                # this copies them onto the spawn site so the join
                # goroutines -> wg_sites stays within one row.
                for m2 in WG_OP_RE.finditer(btxt):
                    if m2.group(1) != "ctx":
                        bufs.rows("wg_sites").append(
                            (sid, rec.fid, n.start_point[0] + 1,
                             m2.group(1), m2.group(2), 1, int(depth > 0)))
            elif kind == "defer":
                dtxt = _txt(n, src)[:160]
                bufs.rows("defers").append(
                    (sid, n.start_point[0] + 1, dtxt[:120],
                     int(depth > 0), depth,
                     int(".Close()" in dtxt),
                     int(".Unlock()" in dtxt or ".RUnlock()" in dtxt),
                     int(".Done()" in dtxt)))
            elif kind == "chan":
                a = n.child_by_field_name("arguments")
                kids = list(a.named_children)
                cap_ = 0
                if len(kids) > 1:
                    ct = _txt(kids[1], src).strip()
                    cap_ = int(ct) if ct.isdigit() else -1
                # `ch := make(chan T)` / `ch = make(chan T)`: the variable the
                # channel lives in, so close(ch) elsewhere in the SAME function
                # can be paired with its declaration (closed_in_fn).
                nm = ""
                par = n.parent
                if par is not None and par.type in (
                        "assignment_statement", "short_var_declaration"):
                    left = par.child_by_field_name("left")
                    if left is not None:
                        nm = _txt(left, src).strip()[:80]
                bufs.rows("channels").append(
                    (sid, rec.fid, nm,
                     _txt(kids[0], src)[:80] if kids else "",
                     cap_, n.start_point[0] + 1,
                     int(bool(nm) and nm in st.close_vars)))

    def type_extra(self, node: Any, rec: FileRec, db: sqlite3.Connection,
                   bufs: Buffers, sid: int, scope: Scope) -> None:
        src = rec.data
        name = self.node_name(node, rec)
        body = None
        for c in node.named_children:
            if c.type in ("interface_type", "struct_type"):
                body = c
                break
        if body is None:
            return
        if body.type == "interface_type":
            methods = [c for c in body.named_children
                       if c.type == "method_elem"]
            embedded = [c for c in body.named_children
                        if c.type in ("type_elem", "type_identifier",
                                      "qualified_type")]
            txt = _txt(body, src)
            bufs.rows("interfaces").append(
                (sid, len(methods), len(embedded),
                 int(name[:1].isupper()),
                 int("|" in txt or "~" in txt),
                 ",".join(self.node_name(m, rec) for m in methods)[:400]))
        else:
            fields = [c for c in body.named_children
                      if c.type == "field_declaration"]
            ftxt = _txt(body, src)
            n_exp = 0
            n_tag = 0
            n_emb = 0
            size = 0
            for i, fl in enumerate(fields):
                fname = ""
                nm = fl.child_by_field_name("name")
                if nm is not None:
                    fname = _txt(nm, src)
                else:
                    n_emb += 1
                ftype = ""
                tn = fl.child_by_field_name("type")
                if tn is not None:
                    ftype = _txt(tn, src)
                if fname[:1].isupper():
                    n_exp += 1
                if "`" in _txt(fl, src):
                    n_tag += 1
                size += _est_size(ftype)
                bufs.fields.append(
                    (sid, i, (fname or ftype)[:120], ftype[:200],
                     "public" if fname[:1].isupper() else "private",
                     fl.start_point[0] + 1, 0, 0, 1,
                     int(ftype.startswith("*")),
                     int(ftype.startswith("[]") or ftype.startswith("map[")),
                     0, 0, ftype.count("[") + ftype.count("*")))
            bufs.rows("structs").append(
                (sid, len(fields), n_emb, n_exp, size, 0, 0,
                 int("sync.Mutex" in ftxt or "sync.RWMutex" in ftxt),
                 int("context.Context" in ftxt), n_tag))

    def parse_imports(self, root: Any, rec: FileRec, bufs: Buffers) -> None:
        src = rec.data
        # `import_spec` exists only inside an `import_declaration`, which in a
        # clean parse sits at the top level of `source_file`. Walking just
        # those subtrees visits ~15 nodes instead of the whole file; a
        # whole-tree cursor walk per file was ~4% of build wall on gin for
        # rows this narrow. A file with ERROR nodes falls back to the full
        # walk: recovery can relocate nodes, and only the full scan is honest
        # about where `import_spec` ended up.
        if root.has_error:
            def _import_nodes():
                for n, _depth in walk_cursor(root):
                    yield n
        else:
            def _import_nodes():
                for top in root.named_children:
                    if top.type == "import_declaration":
                        for n, _depth in walk_cursor(top):
                            yield n
        for n in _import_nodes():
            if n.type != "import_spec":
                continue
            p = n.child_by_field_name("path")
            if p is None:
                continue
            target = _txt(p, src).strip('"`')
            alias = n.child_by_field_name("name")
            head = target.split("/")[0]
            external = "." in head or head not in STDLIB_ROOTS
            bufs.imports.append(
                (rec.fid, target[:300], None,
                 _txt(alias, src) if alias is not None else None,
                 "import", n.start_point[0] + 1,
                 int(external and "." in head), 0,
                 int(alias is not None and _txt(alias, src) == "."),
                 0, 0, 1))

    def parse_file_extra(self, root: Any, rec: FileRec,
                         db: sqlite3.Connection, bufs: Buffers) -> None:
        head = rec.text[:4000]
        for m in BUILD_TAG_RE.finditer(head):
            bufs.rows("build_tags").append(
                (rec.fid, m.group(1).strip()[:200],
                 head[:m.start()].count("\n") + 1))
        if GENERATED_RE.search(head):
            db.execute("UPDATE files SET is_generated=1 WHERE id=?", (rec.fid,))

    def parse_manifests(self, root: str, db: sqlite3.Connection) -> None:
        gomod = os.path.join(root, "go.mod")
        if not os.path.isfile(gomod):
            return
        try:
            text = open(gomod, encoding="utf-8", errors="replace").read()
        except OSError:
            return
        m = _GOMOD_GO_RE.search(text)
        if m:
            self.go_version = "%s.%s" % (m.group(1), m.group(2))
            # Loop-variable capture was fixed in 1.22; below that the classic
            # `go func(){ use(v) }` inside a range IS the bug, above it is not.
            self.loopvar_fixed = (int(m.group(1)), int(m.group(2))) >= (1, 22)
        mod = _GOMOD_MODULE_RE.search(text)
        db.executemany(
            "INSERT OR REPLACE INTO meta(key,value) VALUES(?,?)",
            (("go_version", self.go_version or "?"),
                     ("module", mod.group(1) if mod else "?"),
                     ("loopvar_per_iteration",
                      "yes (go>=1.22)" if self.loopvar_fixed
                      else "NO -- capture bugs are real in this module")))

    def post_build(self, db: sqlite3.Connection) -> None:
        """Work out which concrete types satisfy which interfaces.

        Go has no `implements` keyword: a type satisfies an interface by having
        its method set, and nothing in the source says so. That makes "how many
        types implement this interface" unanswerable by text search, and it is
        exactly the question the dead-abstraction query needs.

        Done in Python rather than SQL because set containment over method
        names would be a correlated NOT EXISTS per pair in SQLite and is a dict
        lookup here. Cost is O(interfaces x types) -- a fraction of a second on
        a 20k-symbol repo.

        Structural and name-based: it agrees with the compiler on method NAMES
        and ignores signatures, so a type with `Close() error` satisfies an
        interface wanting `Close()` even where Go would disagree. The query
        that uses this says so.
        """
        methods_by_type: dict[str, set[str]] = {}
        types_by_method: dict[str, set[str]] = {}
        test_types: set[str] = set()
        for name, recv, in_test in db.execute(
                "SELECT s.name, s.receiver_type, f.is_test FROM symbols s "
                "JOIN files f ON f.id=s.file_id "
                "WHERE s.kind='method' AND s.receiver_type <> ''"):
            methods_by_type.setdefault(recv, set()).add(name)
            types_by_method.setdefault(name, set()).add(recv)
            if in_test:
                test_types.add(recv)

        rows = []
        for iid, mstr, iname in db.execute(
                "SELECT i.symbol_id, i.methods, s.name FROM interfaces i "
                "JOIN symbols s ON s.id=i.symbol_id "
                "WHERE i.n_methods > 0 AND i.methods <> ''"):
            want = {m for m in mstr.split(",") if m}
            if not want:
                continue
            # Drive from the method side: only types that have EVERY interface
            # method can possibly satisfy it, so intersect the per-method type
            # sets first; the exact subset check then runs over a few
            # candidates, not all 25k types. Same pair set, ~3.5x faster.
            it = iter(types_by_method.get(m, set()) for m in want)
            cand = set(next(it))
            cand.intersection_update(*it)
            for tname in cand:
                if want <= methods_by_type[tname]:
                    rows.append((tname, iid, iname, len(want),
                                 int(tname in test_types)))
        if rows:
            db.executemany(
                "INSERT OR IGNORE INTO implements(type_name,interface_id,"
                "interface_name,n_methods,in_test) VALUES(?,?,?,?,?)", rows)
        db.execute("INSERT OR REPLACE INTO meta(key,value) VALUES(?,?)",
                   ("implements_pairs", str(len(rows))))
        self._module_depth(db)
        self._error_chain_depth(db)

    def _module_depth(self, db: sqlite3.Connection) -> None:
        """Longest transitive import chain and transitive package count per
        module, computed on resolved (in-tree) import edges.

        The import graph is a DAG, so each module is visited once with a
        memoised DFS; SQL recursion over imports would re-expand every path.
        External (stdlib/module) imports terminate a chain at depth 1.
        """
        deps: dict[int, set[int]] = {}
        in_degree: dict[int, int] = {}
        for fmod, tmod in db.execute(
                "SELECT f.module_id, tf.module_id FROM imports i "
                "JOIN files f ON f.id=i.file_id "
                "JOIN files tf ON tf.id=i.target_id "
                "WHERE f.module_id IS NOT NULL AND tf.module_id IS NOT NULL "
                "AND f.module_id <> tf.module_id"):
            if fmod not in deps:
                deps[fmod] = set()
                in_degree.setdefault(fmod, 0)
            if tmod not in deps:
                deps[tmod] = set()
                in_degree.setdefault(tmod, 0)
            if tmod not in deps[fmod]:
                deps[fmod].add(tmod)
                in_degree[tmod] = in_degree.get(tmod, 0) + 1
        if not deps:
            return
        # Kahn topological order: chain length = longest path through DAG.
        depth: dict[int, int] = {m: 0 for m in deps}
        from collections import deque
        q = deque([m for m, d in in_degree.items() if d == 0])
        order: list[int] = []
        while q:
            m = q.popleft()
            order.append(m)
            for t in deps[m]:
                in_degree[t] -= 1
                if in_degree[t] == 0:
                    q.append(t)
        for m in order:
            for t in deps[m]:
                depth[t] = max(depth[t], depth[m] + 1)
        # Count distinct transitive deps per module via set union along the
        # reverse graph (dense-set fold: E unions, each O(nodes) worst case --
        # fine for a module graph, which is small even on huge repos).
        reach: dict[int, set[int]] = {m: set() for m in deps}
        for m in reversed(order):
            for t in deps[m]:
                reach[t].add(m)
                reach[t].update(reach[m])
        rows = [(m, depth[m], len(deps[m]), len(reach[m])) for m in deps]
        db.executemany(
            "INSERT OR REPLACE INTO module_depth(module_id,max_depth,"
            "n_direct_imports,n_transitive) VALUES(?,?,?,?)", rows)

    def _error_chain_depth(self, db: sqlite3.Connection) -> None:
        """Longest error-propagation chain per error-returning function.

        max_depth(f) = 1 + max over error-returning callees g of
        max_depth(g): the length of the longest call chain f -> g -> h
        where every hop returns error, so an error raised at the deepest
        leaf surfaces max_depth frames above it. A callee that absorbs
        errors (logs, returns nil) terminates the chain -- that
        containment is exactly what the query is asking about.

        Only edges BETWEEN error-returning functions are traversed, which
        keeps the walk small even on large repos. Recursion cycles are
        capped at ERROR_CHAIN_CAP (a chain through a cycle is unbounded;
        the cap is the honest answer). Memoised, so each node is expanded
        once per reachable-again path; the call graph is small enough that
        this is a fraction of a second on a 20k-symbol repo.
        """
        err_syms = {r[0] for r in db.execute(
            "SELECT id FROM symbols WHERE n_err_returns > 0")}
        if not err_syms:
            return
        fwd: dict[int, list[int]] = {}
        for cid, lid in db.execute(
                "SELECT caller_id, callee_id FROM edges"):
            if cid in err_syms and lid in err_syms:
                fwd.setdefault(cid, []).append(lid)
        memo: dict[int, int] = {}

        def depth(node: int, on_path: set) -> int:
            got = memo.get(node)
            if got is not None:
                return got
            if node in on_path:
                return ERROR_CHAIN_CAP
            on_path.add(node)
            best = 0
            for nxt in fwd.get(node, ()):
                d = depth(nxt, on_path)
                if d > best:
                    best = d
            on_path.discard(node)
            memo[node] = best + 1
            return best + 1

        rows = [(root, depth(root, set())) for root in err_syms]
        db.executemany(
            "INSERT OR REPLACE INTO error_chain_depth(symbol_id,max_depth)"
            " VALUES(?,?)", rows)

    def flush_extra(self, db: sqlite3.Connection, bufs: Buffers) -> None:
        for tbl, sql in (
            ("goroutines",
             "INSERT INTO goroutines(symbol_id,file_id,line,is_closure,target,"
             "has_ctx,has_recover,has_waitgroup,has_errgroup,has_chan_exit,"
             "in_loop,loop_depth,body_sloc) VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?)"),
            ("defers",
             "INSERT INTO defers(symbol_id,line,target,in_loop,loop_depth,"
             "is_close,is_unlock,is_done) VALUES(?,?,?,?,?,?,?,?)"),
            ("channels",
             "INSERT INTO channels(symbol_id,file_id,name,elem_type,capacity,"
             "line,closed_in_fn) VALUES(?,?,?,?,?,?,?)"),
            ("wg_sites",
             "INSERT INTO wg_sites(symbol_id,file_id,line,var,op,"
             "in_goroutine,in_loop) VALUES(?,?,?,?,?,?,?)"),
            ("interfaces",
             "INSERT OR IGNORE INTO interfaces(symbol_id,n_methods,n_embedded,"
             "is_exported,is_constraint,methods) VALUES(?,?,?,?,?,?)"),
            ("structs",
             "INSERT OR IGNORE INTO structs(symbol_id,n_fields,n_embedded,"
             "n_exported_fields,est_size,est_padding,size_exact,has_mutex,"
             "has_ctx_field,n_tagged_fields) VALUES(?,?,?,?,?,?,?,?,?,?)"),
            ("build_tags",
             "INSERT INTO build_tags(file_id,expr,line) VALUES(?,?,?)"),
            ("user_input_sites",
             "INSERT INTO user_input_sites(symbol_id,file_id,var,kind,line,"
             "in_loop) VALUES(?,?,?,?,?,?)"),
            ("secret_candidates",
             "INSERT INTO secret_candidates(symbol_id,file_id,value,line) "
             "VALUES(?,?,?,?)"),
        ):
            rows = bufs.extra.get(tbl)
            if rows:
                db.executemany(sql, rows)

def _txt(node: Any, src: bytes) -> str:
    return src[node.start_byte:node.end_byte].decode("utf-8", "replace")

#: A receiver prefix that is a plain identifier (wg.Add, t.Stop, g.Wait) --
#: filters out method values and selector chains from wg_ops bookkeeping.
IDENT_RE = re.compile(r"^[A-Za-z_]\w*$")

#: wg.Add/Done/Wait sites inside a `go` statement's text, for the spawner-side
#: copy in function_extra.
WG_OP_RE = re.compile(r"([A-Za-z_]\w*)\.(Add|Done|Wait)\(")

#: Every node type GoAnalyzer.on_node inspects. Identifiers and punctuation
#: dominate a Go tree; one frozenset miss skips the whole 15-arm dispatch for
#: them instead of falling through every comparison.
_GO_ONNODE_TYPES = frozenset((
    "binary_expression", "unary_expression", "channel_type",
    "communication_case", "if_statement", "assignment_statement",
    "short_var_declaration", "return_statement", "composite_literal",
    "call_expression", "selector_expression", "type_assertion_expression",
    "range_clause", "field_declaration", "go_statement", "defer_statement"))

#: Hot-path regexes, compiled once. `re.search(pat_str, ...)` works from the
#: module's compile cache, but the cache lookup ran tens of thousands of
#: times per build; these run in the measure walk and function_flags.
_ERR_NIL_CHECK_RE = re.compile(r'\berr\s*!=\s*nil')
_RETURN_NIL_RE = re.compile(r'\breturn\s+nil\b')
_RETURN_NIL_ERR_RE = re.compile(r'\breturn\s+nil,\s*err\b')
_COMMA_ERR_ASSIGN_RE = re.compile(r'\b\w+\s*,\s*err\s*:=')
_BLANK_ASSIGN_RE = re.compile(r'^\s*_\s*(?:,\s*_\s*)*[:=]')
_BLANK_DISCARD_RE = re.compile(r'\b_\s*,?\s*(?:err)?\s*=\s*\w')
_LOOPVAR_REBIND_RE = re.compile(r'^\s*(\w+)\s*:=\s*\1\b')
_RANGE_COPY_RE = re.compile(r'^\s*\w+\s*,\s*\w+\s*:?=\s*range\b')

def in_goroutine(node: Any) -> int:
    """1 when the call sits lexically inside a `go` statement's body.

    Parent-pointer walk stopped at the enclosing function boundary, so a
    Done() in the spawner reads 0 and a Done() inside the spawned closure
    reads 1. Only reached for wg.Add/Done/Wait sites, which are rare.
    """
    p = node.parent
    while p is not None:
        if p.type == "go_statement":
            return 1
        if p.type in ("function_declaration", "method_declaration",
                      "func_literal"):
            return 0
        p = p.parent
    return 0

def _ancestor_loop_depth(node: Any, stop: Any, loop_types: set) -> int:
    d = 0
    cur = node.parent
    while cur is not None and cur.id != stop.id:
        if cur.type in loop_types:
            d += 1
        cur = cur.parent
    return d

_SIZES = {"bool": 1, "int8": 1, "uint8": 1, "byte": 1, "int16": 2,
          "uint16": 2, "int32": 4, "uint32": 4, "rune": 4, "float32": 4,
          "int": 8, "uint": 8, "int64": 8, "uint64": 8, "float64": 8,
          "uintptr": 8, "complex64": 8, "complex128": 16,
          "string": 16, "error": 16}

def _est_size(t: str) -> int:
    t = t.strip()
    if not t:
        return 0
    if t.startswith("*") or t.startswith("chan") or t.startswith("func") or \
            t.startswith("map["):
        return 8
    if t.startswith("[]"):
        return 24                       # slice header
    if t.startswith("interface") or t == "any":
        return 16
    m = _ARRAY_LEN_RE.match(t)
    if m:
        return int(m.group(1)) * _est_size(m.group(2))
    return _SIZES.get(t, 8)

GoAnalyzer.QUERIES = [
(
    "goroutine-leak-frontier",
    "Goroutines with no context, no WaitGroup and no errgroup",
    "ANSWERS which goroutines have no way to be told to stop.\n"
    "ACT every spawn needs a stop condition and a joiner. A spawn inside a loop\n"
    "     with neither is the top of the list: it fans out per element and\n"
    "     nothing ever collects it.\n"
    "MISLEADS a goroutine that exits because its input channel is closed by\n"
    "     someone else is correct and appears here -- has_chan_exit is the\n"
    "     counter-evidence. has_ctx is a lexical scan of the closure body, so a\n"
    "     context checked one frame deeper is missed.",
    """SELECT s.name AS in_fn, COUNT(g.id) AS spawns,
        SUM(g.in_loop) AS in_loop, MAX(g.loop_depth) AS depth,
        SUM(g.has_ctx) AS with_ctx, SUM(g.has_waitgroup) AS with_wg,
        SUM(g.has_errgroup) AS with_errgroup,
        SUM(g.has_recover) AS with_recover,
        SUM(g.has_chan_exit) AS chan_exit,
        s.is_handler AS handler, s.n_ctx_params AS ctx_params,
        f.path || ':' || MIN(g.line) AS at
    FROM goroutines g
    JOIN symbols s ON s.id=g.symbol_id
    JOIN files f ON f.id=g.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE f.is_test=0 AND COALESCE(m.name,'') LIKE :mod
    GROUP BY s.id
    HAVING with_ctx=0 AND with_wg=0 AND with_errgroup=0
    ORDER BY in_loop DESC, spawns DESC LIMIT :lim"""),
(
    "goroutine-under-handler",
    "Goroutines reachable from a request handler, up to 4 hops",
    "ANSWERS which spawns outlive the request that created them.\n"
    "ACT a goroutine started per request and never joined is how RSS grows all\n"
    "     week and nobody can say why. Give it the request context.\n"
    "MISLEADS depth is capped at 4 and only resolved edges are walked, so this\n"
    "     is a floor. A handler registered by a router this cannot see has no\n"
    "     is_handler flag and its whole subtree is missing.",
    """
WITH RECURSIVE down(root, sym, depth) AS (
        SELECT s.id, s.id, 0 FROM symbols s WHERE s.is_handler=1
        UNION
        SELECT d.root, e.callee_id, d.depth+1
        FROM down d JOIN edges e ON e.caller_id=d.sym
        WHERE d.depth < 4 AND e.is_self=0),
    -- One row per (handler, symbol). `down` holds one row per DEPTH at which
    -- the symbol is reachable, so joining it straight to `goroutines` counted
    -- every goroutine once per distinct path length -- up to 4x on kubernetes.
    reach(root, sym, depth) AS (
        SELECT root, sym, MIN(depth) FROM down GROUP BY root, sym)
    SELECT h.name AS handler, s.name AS spawns_in,
        MIN(reach.depth) AS hops, COUNT(g.id) AS goroutines,
        SUM(g.has_ctx) AS with_ctx, SUM(g.in_loop) AS in_loop,
        f.path || ':' || MIN(g.line) AS at
    FROM reach
    JOIN symbols s ON s.id=reach.sym
    JOIN symbols h ON h.id=reach.root
    JOIN goroutines g ON g.symbol_id=s.id
    JOIN files f ON f.id=g.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE f.is_test=0 AND COALESCE(m.name,'') LIKE :mod
    GROUP BY h.id, s.id
    HAVING with_ctx < goroutines
    ORDER BY hops ASC, goroutines DESC LIMIT :lim"""),
(
    "ctx-propagation-break",
    "Where a live context stops being passed down",
    "ANSWERS the exact function at which cancellation and deadlines are lost:\n"
    "     the caller has a ctx, the callee makes a fresh Background() instead.\n"
    "ACT thread the caller's ctx through. A Background() below a handler means\n"
    "     that work cannot be cancelled when the client hangs up.\n"
    "MISLEADS a genuinely detached background worker is SUPPOSED to call\n"
    "     context.Background(). Check whether the row sits on a request path\n"
    "     before changing it.",
    """SELECT cal.name AS caller, cle.name AS callee,
        cal.n_ctx_params AS caller_ctx, cle.n_ctx_params AS callee_ctx,
        cle.n_ctx_background AS makes_background,
        cle.n_io AS io, cle.n_net AS net_, cle.n_sql AS sql_,
        cle.n_ctx_done AS uses_done, cle.fan_in,
        f.path || ':' || cle.line_start AS at
    FROM edges e
    JOIN symbols cal ON cal.id=e.caller_id
    JOIN symbols cle ON cle.id=e.callee_id
    JOIN files f ON f.id=cle.file_id
    LEFT JOIN modules m ON m.id=cle.module_id
    WHERE cal.n_ctx_params>0
      AND (cle.n_ctx_background>0
           OR (cle.n_ctx_params=0 AND (cle.n_io+cle.n_net+cle.n_sql)>0))
      AND f.is_test=0 AND COALESCE(m.name,'') LIKE :mod
    ORDER BY (cle.n_net*3 + cle.n_sql*3 + cle.n_io) DESC,
        cle.fan_in DESC LIMIT :lim"""),
(
    "defer-lifetime",
    "defer inside a loop: cleanup that waits for the whole function",
    "ANSWERS staticcheck SA9001 -- defers run at FUNCTION exit, not at the end\n"
    "     of the iteration, so a loop over 10,000 files holds 10,000 handles.\n"
    "ACT wrap the loop body in a func(){...}() so the defer fires per iteration,\n"
    "     or close explicitly at the end of the body.\n"
    "MISLEADS a loop with a small constant bound holding a couple of handles is\n"
    "     harmless. The risk scales with trip count, which is invisible here.",
    """SELECT s.name, COUNT(d.id) AS defers, SUM(d.in_loop) AS in_loop,
        MAX(d.loop_depth) AS depth, SUM(d.is_close) AS closes,
        SUM(d.is_unlock) AS unlocks, s.n_loops AS loops, s.fan_in,
        GROUP_CONCAT(DISTINCT SUBSTR(d.target,1,28)) AS targets,
        f.path || ':' || MIN(d.line) AS at
    FROM defers d
    JOIN symbols s ON s.id=d.symbol_id
    JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE d.in_loop=1 AND f.is_test=0 AND COALESCE(m.name,'') LIKE :mod
    GROUP BY s.id
    ORDER BY in_loop DESC, depth DESC LIMIT :lim"""),
(
    "resource-close-cross-layer",
    "Opens a body, rows or file and defers no Close",
    "ANSWERS the cross-function version of bodyclose / sqlclosecheck: the open\n"
    "     and the Close live in different functions, so no per-file checker can\n"
    "     pair them.\n"
    "ACT the function that opens should defer the Close, or return a closer and\n"
    "     say so in its name. callers_that_close is the evidence someone else\n"
    "     is already doing it.\n"
    "MISLEADS a constructor that deliberately returns an open resource is\n"
    "     correct and appears here. Check whether the return type is a Closer.",
    """SELECT s.name, s.n_net AS net_ops, s.n_sql AS sql_ops, s.n_io AS io_ops,
        s.n_defer AS defers, s.n_defer_close AS defer_closes,
        s.return_type,
        (SELECT COUNT(*) FROM edges e2
         JOIN symbols c2 ON c2.id=e2.caller_id
         WHERE e2.callee_id=s.id AND c2.n_defer_close>0) AS callers_that_close,
        s.n_err_ignored AS ignored_errs, s.fan_in,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE (s.n_net + s.n_sql + s.n_io) > 0 AND s.n_defer_close=0
      AND f.is_test=0 AND COALESCE(m.name,'') LIKE :mod
    ORDER BY callers_that_close ASC,
        (s.n_net*3 + s.n_sql*3 + s.n_io) DESC LIMIT :lim"""),
(
    "unchecked-errors",
    "Discarded errors, weighted by how much of the tree calls the discarder",
    "ANSWERS which errcheck findings actually matter: a swallowed error in a\n"
    "     leaf forty callers depend on is a different object from one in a\n"
    "     one-shot init.\n"
    "ACT check it, or wrap with %w so errors.Is still works upstream.\n"
    "MISLEADS the blast column multiplies by MAX(fan_in,1), so a symbol with\n"
    "     NO known caller scores exactly as if it had one. Read fan_in=0\n"
    "     rows as 'unknown reach', never as 'reach of 1'.\n"
    "     `_ = f.Close()` on a read-only file is a deliberate discard and is\n"
    "     counted here. Shadow detection is textual, so an intentional inner\n"
    "     err is a false positive.",
    """SELECT s.name, s.n_err_ignored AS ignored,
        s.n_err_shadowed AS shadowed, s.n_err_checks AS checked,
        s.n_err_wrapped AS wrapped, s.n_err_returns AS err_returns,
        s.n_naked_returns AS naked, s.n_named_results AS named,
        s.fan_in, s.n_err_ignored * MAX(s.fan_in,1) AS blast,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE (s.n_err_ignored + s.n_err_shadowed) > 0
      AND f.is_test=0 AND COALESCE(m.name,'') LIKE :mod
    ORDER BY blast DESC, s.n_err_shadowed DESC LIMIT :lim"""),
(
    "channel-topology",
    "Unbuffered channels, and whether anything can receive",
    "ANSWERS the two channel deadlock shapes: an unbuffered send with no ready\n"
    "     receiver, and a range-over-channel nobody closes. SA1017 is the\n"
    "     special case -- signal.Notify on an unbuffered channel DROPS signals.\n"
    "ACT name the closer for every channel. An unbuffered send while holding a\n"
    "     lock is a deadlock waiting for load.\n"
    "MISLEADS a never-closed channel is fine if nothing ranges over it. A\n"
    "     capacity of -1 means the size is a variable and could be anything.",
    """SELECT s.name AS declared_in, c.elem_type, c.capacity AS cap_,
        s.n_chan_send AS sends, s.n_chan_recv AS recvs,
        s.n_chan_close AS closes, s.n_select AS selects,
        s.n_select_ctx_done AS ctx_done_case,
        s.lock_in_loop AS locks_in_loop, s.n_goroutines AS spawns,
        f.path || ':' || c.line AS at
    FROM channels c
    JOIN symbols s ON s.id=c.symbol_id
    JOIN files f ON f.id=c.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE c.capacity=0 AND f.is_test=0 AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.n_chan_send DESC, spawns DESC LIMIT :lim"""),
(
    "lock-copied-by-value",
    "Types embedding a sync.Mutex passed by value",
    "ANSWERS `go vet copylocks` raised to the call graph: a copied mutex\n"
    "     protects nothing, and the copy is silent.\n"
    "ACT take the type by pointer everywhere, or add a noCopy field so vet\n"
    "     catches the next one.\n"
    "MISLEADS a struct copied before any goroutine exists -- config\n"
    "     construction, test fixtures -- is harmless. An embedded mutex inside\n"
    "     an embedded struct is missed by the has_mutex scan.",
    """
    -- SQLite's LIKE is case-INSENSITIVE for ASCII, and in Go case decides
    -- whether a name is exported. `p.type LIKE '%.' || ty.name` matched the
    -- unexported `groupversion` against every `schema.GroupVersion` in the
    -- tree: 1,449 of 1,715 reported pairs on kubernetes were case collisions.
    -- Equality is case-sensitive and can use idx_params_type.
    WITH mx AS (
        SELECT ty.id AS tid, ty.name AS tname, st.n_fields, st.est_size
        FROM structs st JOIN symbols ty ON ty.id=st.symbol_id
        WHERE st.has_mutex=1
    ),
    hp AS (
        SELECT p.symbol_id AS sid, p.pos, p.name AS pname, p.type AS ptype,
               CASE WHEN substr(rtrim(p.type,'abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_'),-1)='.'
                    THEN substr(p.type, length(rtrim(p.type,'abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_'))+1)
               END AS qualified,
               CASE WHEN substr(p.type,1,2)='[]' THEN substr(p.type,3) END AS sliced
        FROM params p WHERE p.type NOT LIKE '%*%'
    ),
    hit AS (
        SELECT mx.tid, mx.n_fields, mx.est_size, hp.sid, hp.pos, hp.pname, hp.ptype
        FROM hp JOIN mx ON mx.tname = hp.ptype
        UNION
        SELECT mx.tid, mx.n_fields, mx.est_size, hp.sid, hp.pos, hp.pname, hp.ptype
        FROM hp JOIN mx ON mx.tname = hp.qualified
        UNION
        SELECT mx.tid, mx.n_fields, mx.est_size, hp.sid, hp.pos, hp.pname, hp.ptype
        FROM hp JOIN mx ON mx.tname = hp.sliced
    )
    SELECT ty.name AS type_, hit.n_fields AS fields, hit.est_size AS bytes_,
        s.name AS used_in, hit.pos, hit.pname AS param, hit.ptype AS type,
        s.n_goroutines AS spawns, s.fan_in,
        f.path || ':' || s.line_start AS at
    FROM hit
    JOIN symbols ty ON ty.id=hit.tid
    JOIN symbols s ON s.id=hit.sid
    JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE f.is_test=0 AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.n_goroutines DESC, s.fan_in DESC LIMIT :lim"""),
(
    "lock-over-crosspkg-call",
    "A mutex held while calling into another package",
    "ANSWERS where your critical section's duration is somebody else's code --\n"
    "     the contention a profiler shows as time in Lock with no clue why.\n"
    "ACT copy what you need out of the guarded state, unlock, then call out.\n"
    "MISLEADS same_module=0 is a package boundary, not a slowness proof. A\n"
    "     cross-package call to a pure helper costs nothing.",
    """SELECT s.name AS holder, s.n_lock AS locks,
        s.lock_in_loop AS locks_in_loop,
        COUNT(DISTINCT e.callee_id) AS cross_pkg_callees,
        SUM(cle.n_io + cle.n_net + cle.n_sql) AS callee_io,
        SUM(cle.n_chan_send) AS callee_sends,
        MAX(cle.n_lock) AS callee_locks, s.fan_in,
        GROUP_CONCAT(DISTINCT cle.name) AS calls_out,
        f.path || ':' || s.line_start AS at
    FROM symbols s
    JOIN edges e ON e.caller_id=s.id AND e.same_module=0
    JOIN symbols cle ON cle.id=e.callee_id
    JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_lock > 0 AND f.is_test=0 AND COALESCE(m.name,'') LIKE :mod
    GROUP BY s.id
    HAVING callee_io > 0 OR callee_locks > 0 OR callee_sends > 0
    ORDER BY callee_io DESC, s.lock_in_loop DESC LIMIT :lim"""),
(
    "n-plus-one",
    "A query function whose CALLER puts it in a loop",
    "ANSWERS the N+1 no per-file linter can see, because the query and the loop\n"
    "     live in different functions.\n"
    "ACT batch-fetch, join, or move the loop into the query.\n"
    "MISLEADS a loop with a small constant bound is not an N+1, and trip count\n"
    "     is invisible here.",
    """SELECT cal.name AS caller, cal.max_loop_depth AS loop_depth,
        cle.name AS query_fn, cle.n_sql AS sql_ops,
        cle.query_in_loop AS own_loop, e.n_calls AS edges,
        cal.fan_in AS caller_fan_in, cal.is_handler AS handler,
        f.path || ':' || cal.line_start AS at
    FROM edges e
    JOIN symbols cal ON cal.id=e.caller_id
    JOIN symbols cle ON cle.id=e.callee_id
    JOIN files f ON f.id=cal.file_id
    LEFT JOIN modules m ON m.id=cal.module_id
    WHERE cle.n_sql > 0 AND cal.max_loop_depth > 0 AND cal.call_in_loop > 0
      AND f.is_test=0 AND COALESCE(m.name,'') LIKE :mod
    ORDER BY cal.max_loop_depth DESC, cle.n_sql DESC LIMIT :lim"""),
(
    "unsafe-cgo-frontier",
    "unsafe.Pointer and cgo reachable from a handler, up to 5 hops",
    "ANSWERS the only places in a Go binary where memory unsafety is possible.\n"
    "ACT these are the fuzzing targets. Every cgo call also costs a\n"
    "     goroutine-to-thread transition, so a cgo call in a hot path is a\n"
    "     performance finding as well as a safety one.\n"
    "MISLEADS unsafe.Sizeof and unsafe.Alignof are compile-time and completely\n"
    "     safe, yet counted in n_unsafe_ops. Read the hazard patterns, not the\n"
    "     total.",
    """WITH RECURSIVE down(sym, depth) AS (
        SELECT s.id, 0 FROM symbols s
        WHERE s.is_handler=1 OR s.is_entrypoint=1
        UNION
        SELECT e.callee_id, d.depth+1
        FROM down d JOIN edges e ON e.caller_id=d.sym
        WHERE d.depth < 5 AND e.is_self=0),
    best AS (SELECT sym, MIN(depth) AS depth FROM down GROUP BY sym)
    SELECT s.name, b.depth AS hops_from_handler,
        s.n_unsafe_ops AS unsafe_, s.n_cgo_calls AS cgo,
        s.n_reflect_ops AS reflect_, s.n_go_directives AS directives,
        s.n_panics AS panics, s.fan_in,
        f.path || ':' || s.line_start AS at
    FROM best b JOIN symbols s ON s.id=b.sym
    JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE (s.n_unsafe_ops > 0 OR s.n_cgo_calls > 0) AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY b.depth ASC, s.n_cgo_calls DESC LIMIT :lim"""),
(
    "package-state-concurrent",
    "Packages that spawn goroutines and hold unguarded package state",
    "ANSWERS what the race detector would find if the right two goroutines ever\n"
    "     ran together.\n"
    "ACT move the state behind a struct with a mutex, or make it immutable\n"
    "     after init.\n"
    "MISLEADS state written only in init() and read afterwards is safe. This\n"
    "     counts declarations plus goroutine presence in the same package, not\n"
    "     actual concurrent access.",
    """SELECT m.name AS package_,
        SUM(s.n_goroutines) AS spawns, SUM(s.n_lock) AS locks,
        SUM(s.n_atomic) AS atomics, SUM(s.n_time_tick) AS tickers,
        SUM(s.is_init) AS init_funcs,
        COUNT(DISTINCT s.id) AS fns,
        SUM(s.n_chan_send) AS sends
    FROM symbols s
    JOIN files f ON f.id=s.file_id
    JOIN modules m ON m.id=s.module_id
    WHERE f.is_test=0 AND m.name LIKE :mod
    GROUP BY m.id
    HAVING spawns > 0 AND locks = 0 AND atomics = 0
    ORDER BY spawns DESC LIMIT :lim"""),
(
    "dead-code",
    "Nothing in this tree calls these",
    "ANSWERS what might be deletable.\n"
    "ACT exported identifiers are excluded because another module may use them.\n"
    "     What is left is unexported and unreferenced.\n"
    "MISLEADS an unexported function reached only through an interface method\n"
    "     value, or registered in a map of handlers, has no resolvable edge\n"
    "     and appears here wrongly -- and so does a method called on its own\n"
    "     receiver from another FILE in the same package, which resolution\n"
    "     does not always follow. grep the name before deleting anything.",
    """SELECT s.name, s.kind, s.sloc, s.cyclomatic AS cyclo,
        s.receiver_type AS recv, s.n_external_calls AS ext_calls,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.fan_in=0 AND s.kind IN ('function','method')
      AND s.is_public=0 AND s.is_test=0 AND s.is_entrypoint=0
      AND s.is_handler=0 AND f.is_test=0 AND f.is_generated=0
      AND s.name <> '(anonymous)'
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.sloc DESC LIMIT :lim"""),
(
    "defer-in-loop",
    "defer inside a loop: cleanup that piles up until the function returns",
    "ANSWERS where deferred work does not run when the author thinks it does.\n"
    "     `defer` fires at FUNCTION exit, not at the end of the iteration --\n"
    "     so a defer f.Close() in a loop over ten thousand files holds ten\n"
    "     thousand descriptors open, and the loop hits the ulimit.\n"
    "ACT move the body into its own function so the defer scopes to one\n"
    "     iteration, or close explicitly at the end of the loop and drop the\n"
    "     defer. `defer_close` shows which of these are closing something.\n"
    "MISLEADS a defer in a loop that runs a bounded handful of times is fine,\n"
    "     and this cannot see the trip count. The dangerous shape is a defer\n"
    "     over a range of unknown length -- check what the loop iterates.",
    """SELECT s.name, s.receiver_type AS receiver, s.n_defer_in_loop AS defer_in_loop,
        s.n_defer_close AS defer_closes, s.max_loop_depth AS depth,
        s.n_chan_close AS chan_closes, s.n_io AS io_ops, s.fan_in,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_defer_in_loop > 0 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.n_defer_in_loop * (1 + s.fan_in) DESC,
        s.max_loop_depth DESC LIMIT :lim"""),
(
    "context-not-propagated",
    "Functions that take a context and never pass it on",
    "ANSWERS where cancellation stops travelling. A ctx parameter that is\n"
    "     accepted and then ignored means every call below it is\n"
    "     uncancellable: the request times out, the client disconnects, and\n"
    "     the work carries on burning a database connection.\n"
    "ACT pass ctx to every call that accepts one, and use\n"
    "     `ctx.Done()` in any select that could block. A function creating\n"
    "     `context.Background()` deep in a call stack is almost always\n"
    "     severing a chain it should have continued.\n"
    "MISLEADS a leaf function doing pure computation takes ctx for interface\n"
    "     reasons and has nothing to pass it to -- that is correct and shows\n"
    "     up here. Rank by fan_out: severing a chain matters where work follows.",
    """SELECT s.name, s.receiver_type AS receiver, s.n_ctx_params AS ctx_params,
        s.n_ctx_passed AS ctx_passed, s.n_ctx_background AS ctx_background,
        s.n_ctx_done AS ctx_done, s.n_ctx_withcancel AS with_cancel,
        s.n_cancel_called AS cancels, s.n_goroutines AS goroutines,
        s.fan_out, f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_ctx_params > 0 AND s.n_ctx_passed = 0 AND s.fan_out > 0
      AND f.is_test=0 AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.fan_out DESC, s.n_goroutines DESC LIMIT :lim"""),
(
    "error-handling-drift",
    "Ignored errors, shadowed errors, and errors compared instead of unwrapped",
    "ANSWERS where Go's error convention has quietly broken down. An `_`\n"
    "     assignment discards a failure; a re-declared err inside an if\n"
    "     shadows the outer one so the outer stays nil; and `err == ErrFoo`\n"
    "     fails the moment anything in the chain wraps it with %w.\n"
    "ACT check the error or comment why it cannot fail. Use `errors.Is` and\n"
    "     `errors.As` rather than == and type assertions, so wrapping stays\n"
    "     transparent. `err_wrapped` shows who is already doing it.\n"
    "MISLEADS a deliberately ignored error -- a Close on a read-only file, a\n"
    "     fmt.Fprintf to a buffer -- is idiomatic and counted here. The\n"
    "     column that carries real signal is shadowing, which is never intended.",
    """SELECT s.name, s.receiver_type AS receiver, s.n_err_ignored AS ignored,
        s.n_err_shadowed AS shadowed, s.n_err_checks AS checked,
        s.n_err_wrapped AS wrapped, s.n_err_returns AS returns_err,
        s.n_naked_returns AS naked_returns, s.n_panics AS panics,
        s.n_log_fatal AS log_fatal, s.fan_in,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE (s.n_err_ignored > 0 OR s.n_err_shadowed > 0) AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.n_err_shadowed DESC, s.n_err_ignored * (1 + s.fan_in) DESC
    LIMIT :lim"""),
(
    "slice-growth-and-copies",
    "append in a loop with no capacity, and range copying whole structs",
    "ANSWERS where a loop reallocates or copies more than it needs to.\n"
    "     `append` without `make([]T, 0, n)` regrows and copies repeatedly;\n"
    "     `for _, v := range structs` copies every element by value, which\n"
    "     for a large struct is a memcpy per iteration.\n"
    "ACT preallocate with the known length. Range over the index, or use a\n"
    "     pointer element, when the struct is big. `Sprintf` in a loop is the\n"
    "     third form of the same problem -- build with a strings.Builder.\n"
    "MISLEADS a slice that grows a handful of times costs nothing, and Go's\n"
    "     growth is amortised. This is a ranking of where the pattern is\n"
    "     densest and hottest, not a list of defects.",
    """SELECT s.name, s.receiver_type AS receiver,
        s.n_append_in_loop AS append_in_loop, s.n_make_no_cap AS make_no_cap,
        s.n_range_value_copy AS range_copies,
        s.n_sprintf_in_loop AS sprintf_in_loop,
        s.n_conv_in_loop AS conv_in_loop, s.max_loop_depth AS depth,
        s.fan_in, f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE (s.n_append_in_loop + s.n_sprintf_in_loop + s.n_range_value_copy) > 0
      AND f.is_test=0 AND COALESCE(m.name,'') LIKE :mod
    ORDER BY (s.n_append_in_loop*2 + s.n_sprintf_in_loop*3
              + s.n_range_value_copy) * (1 + s.fan_in) DESC LIMIT :lim"""),
(
    "unchecked-type-assertions",
    "Type assertions without the comma-ok form, and interface{} at the boundary",
    "ANSWERS which assertions panic instead of failing. `v := x.(T)` aborts\n"
    "     the goroutine when x is not a T; `v, ok := x.(T)` does not. In a\n"
    "     handler without recover, that is the request AND the process.\n"
    "ACT use the comma-ok form and handle the false branch, or a type switch\n"
    "     with a default. Where the value came from JSON or a plugin, assume\n"
    "     it will eventually be the wrong shape, because it will.\n"
    "MISLEADS an assertion immediately after a type switch that already\n"
    "     proved the type is safe and counted here. `type_switch` in the same\n"
    "     row is the hint that the author did check.",
    """SELECT s.name, s.receiver_type AS receiver,
        s.n_type_assert_unchecked AS unchecked_asserts,
        s.n_type_assert AS asserts_total, s.n_type_switch AS type_switches,
        s.n_any_params AS any_params, s.n_iface_params AS iface_params,
        s.n_recover AS recovers, s.is_handler AS handler, s.fan_in,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_type_assert_unchecked > 0 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.is_handler DESC, s.n_type_assert_unchecked * (1 + s.fan_in) DESC
    LIMIT :lim"""),
(
    "context-severed-by-caller",
    "context.Background() called from a function whose own caller had a real context",
    "ANSWERS the question `containedctx` and `fatcontext` cannot: not whether\n"
    "     a fresh Background() exists, but whether one was NEEDED. A\n"
    "     Background() at main() is correct. The same call two frames below a\n"
    "     handler that was handed a ctx severs cancellation for everything\n"
    "     underneath -- the request is abandoned and the work carries on.\n"
    "ACT thread the caller's ctx down instead of minting a new one. The\n"
    "     `caller` column names a function that already had one; if several\n"
    "     callers appear, the signature needs a ctx parameter.\n"
    "MISLEADS a Background() used to deliberately OUTLIVE the request -- a\n"
    "     fire-and-forget audit write, a cache warm -- is correct and looks\n"
    "     identical here. The tell is whether the result is awaited. This also\n"
    "     inherits containedctx's blind spot: a ctx stored in a struct field\n"
    "     rather than passed is invisible to both.",
    """SELECT callee.name AS makes_background, caller.name AS caller,
        caller.n_ctx_params AS caller_had_ctx,
        callee.n_ctx_background_call AS background_calls,
        callee.n_ctx_params AS callee_ctx_params,
        callee.n_goroutines AS goroutines, callee.fan_in,
        COUNT(DISTINCT e.caller_id) AS callers_with_ctx,
        f.path || ':' || callee.line_start AS at
    FROM edges e
    JOIN symbols caller ON caller.id = e.caller_id
    JOIN symbols callee ON callee.id = e.callee_id
    JOIN files f ON f.id = callee.file_id
    LEFT JOIN modules m ON m.id = callee.module_id
    WHERE callee.n_ctx_background_call > 0
      AND caller.n_ctx_params > 0
      AND callee.n_ctx_params = 0
      AND e.is_self = 0 AND f.is_test = 0
      AND COALESCE(m.name,'') LIKE :mod
    GROUP BY callee.id, caller.id
    ORDER BY callers_with_ctx DESC, callee.fan_in DESC,
        callee.n_goroutines DESC LIMIT :lim"""),
(
    "lock-release-imbalance-reachable",
    "Functions that lock more than they unlock, weighted by what reaches them",
    "ANSWERS which unbalanced locking can actually be hit. Counting Lock and\n"
    "     Unlock per function is trivial and staticcheck does it; the useful\n"
    "     question is whether an HTTP handler or a goroutine reaches the\n"
    "     imbalance, because an unreleased mutex there deadlocks the server\n"
    "     rather than one test.\n"
    "ACT `defer mu.Unlock()` immediately after the Lock is the fix for almost\n"
    "     all of these. Where the imbalance is deliberate -- lock in one\n"
    "     method, unlock in another -- name the pair so the next reader knows.\n"
    "MISLEADS a deferred Unlock IS counted, so a correctly balanced function\n"
    "     shows equal numbers; what appears here is genuinely lopsided text.\n"
    "     But lock and unlock in different FUNCTIONS is a legitimate pattern\n"
    "     for a guard type and reads as an imbalance in both halves. Depth is\n"
    "     bounded at 4 hops, so a deeper caller is simply not seen.",
    """WITH RECURSIVE walk(root, sym, depth) AS (
        SELECT s.id, s.id, 0 FROM symbols s
        WHERE s.is_handler = 1 OR s.n_goroutines > 0
        UNION
        SELECT w.root, e.callee_id, w.depth + 1
        FROM walk w JOIN edges e ON e.caller_id = w.sym
        WHERE w.depth < 4 AND e.is_self = 0),      -- depth bound: 4 hops
    reach(root, sym, depth) AS (
        SELECT root, sym, MIN(depth) FROM walk GROUP BY root, sym)
    SELECT s.name, s.receiver_type AS receiver, entry.name AS reached_from,
        MIN(r.depth) AS hops,
        s.n_lock_call AS locks, s.n_unlock_call AS unlocks,
        s.n_lock_call - s.n_unlock_call AS imbalance,
        s.n_defer_close AS defers, s.n_goroutines AS goroutines,
        s.fan_in, f.path || ':' || s.line_start AS at
    FROM reach r
    JOIN symbols s ON s.id = r.sym
    JOIN symbols entry ON entry.id = r.root
    JOIN files f ON f.id = s.file_id
    LEFT JOIN modules m ON m.id = s.module_id
    WHERE s.n_lock_call > s.n_unlock_call AND f.is_test = 0
      AND COALESCE(m.name,'') LIKE :mod
    GROUP BY s.id, entry.id
    ORDER BY hops ASC, imbalance DESC, s.fan_in DESC LIMIT :lim"""),
(
    "nil-context-deep",
    "context.Background() or context.TODO() deep in a call chain (containedctx)",
    "ANSWERS where a function that is reachable from a request handler creates a\n"
    "     new root context instead of accepting one from its caller, severing\n"
    "     cancellation and deadline propagation.\n"
    "ACT thread the caller's context through, or if a true root is intended\n"
    "     (background worker), document why. n_ctx_background is the count;\n"
    "     is_handler=1 or reachability from one says a real context existed.\n"
    "MISLEADS context.Background() in main() or init() is correct. Reachability\n"
    "     is capped at 4 hops, so a handler six calls away is missed.",
    """WITH RECURSIVE walk(root, sym, depth) AS (
        SELECT s.id, s.id, 0 FROM symbols s WHERE s.is_handler=1
        UNION
        SELECT w.root, e.callee_id, w.depth+1
        FROM walk w JOIN edges e ON e.caller_id=w.sym
        WHERE w.depth < 4 AND e.is_self=0),
    reach(root, sym, depth) AS (
        SELECT root, sym, MIN(depth) FROM walk GROUP BY root, sym)
    SELECT s.name, s.n_ctx_background AS bg_contexts,
        s.n_ctx_withcancel AS with_cancel, s.n_cancel_called AS cancel_called,
        MIN(r.depth) AS hops_from_handler,
        s.fan_in, s.cyclomatic AS cyclo,
        f.path || ':' || s.line_start AS at
    FROM reach r
    JOIN symbols s ON s.id=r.sym
    JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_ctx_background > 0 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    GROUP BY s.id
    ORDER BY hops_from_handler ASC, s.n_ctx_background DESC LIMIT :lim"""),
(
    "error-not-wrapped",
    "errors created without %w wrapping (errorlint)",
    "ANSWERS where fmt.Errorf or errors.New is used without %w, so callers\n"
    "     cannot errors.Is or errors.As the underlying cause.\n"
    "ACT change fmt.Errorf('...: %v', err) to fmt.Errorf('...: %w', err).\n"
    "     n_errorf_no_wrap is the count; n_err_wrapped is the counter-evidence.\n"
    "MISLEADS not every error has a cause to wrap; a sentinel error from\n"
    "     errors.New is intentionally flat.",
    """SELECT s.name, s.n_errorf_no_wrap AS unwrapped_errors,
        s.n_err_wrapped AS wrapped_errors, s.n_err_returns AS err_returns,
        s.fan_in, s.cyclomatic AS cyclo,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_errorf_no_wrap > 0 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.n_errorf_no_wrap DESC, s.fan_in DESC LIMIT :lim"""),
(
    "weak-random-security",
    "math/rand used where crypto/rand is needed (gosec G404)",
    "ANSWERS where math/rand is used for security-sensitive randomness: tokens,\n"
    "     IDs, keys, shuffling. math/rand is deterministic and predictable.\n"
    "ACT replace with crypto/rand or math/rand/v2 with a proper seed for\n"
    "     non-security uses; use crypto/rand for anything security-relevant.\n"
    "MISLEADS math/rand for simulation, testing, or jitter is correct. The\n"
    "     column is a count, not a judgement: whether this call is\n"
    "     security-sensitive depends on the call graph context.",
    """SELECT s.name, s.n_weak_random AS weak_random_calls,
        s.n_decode_call AS decode_calls, s.n_exec_call AS exec_calls,
        s.fan_in, s.is_handler AS handler,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_weak_random > 0 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.fan_in DESC, s.n_weak_random DESC LIMIT :lim"""),
(
    "weak-crypto-security",
    "MD5, SHA1, DES, or RC4 used in cryptographic context (gosec G401-G405)",
    "ANSWERS where a broken or deprecated crypto algorithm is used.\n"
    "ACT replace MD5/SHA1 with SHA256 or stronger; replace DES/RC4 with AES.\n"
    "MISLEADS MD5 for a checksum or ETag is not a security failure. The graph\n"
    "     sees the call, not its purpose.",
    """SELECT s.name, s.n_weak_crypto AS weak_crypto_calls,
        s.n_decode_call AS decode_calls,
        s.fan_in, s.is_handler AS handler,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_weak_crypto > 0 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.fan_in DESC, s.n_weak_crypto DESC LIMIT :lim"""),
(
    "import-cycle",
    "Circular import dependencies (madge/deadcode)",
    "ANSWERS which files form an import cycle, where A imports B and B imports A\n"
    "     (directly or transitively). Cycles cause init-order bugs and block\n"
    "     testability.\n"
    "ACT break the cycle by extracting shared code into a third package, or\n"
    "     use dependency injection.\n"
    "MISLEADS cycles through test files are usually fine. Depth is capped at 8.",
    """WITH RECURSIVE walk(start, current, depth) AS (
        SELECT f.id, f.id, 0 FROM files f WHERE f.is_test=0
        UNION
        SELECT w.start, i.target_id, w.depth+1
        FROM walk w JOIN imports i ON i.file_id=w.current
        WHERE w.depth < 8 AND i.target_id IS NOT NULL AND i.is_external=0)
    SELECT f.path, COUNT(DISTINCT w.start) AS cycle_size,
        MIN(w.depth) AS shortest_cycle,
        f.path || ':' || 0 AS at
    FROM walk w JOIN files f ON f.id=w.current
    WHERE w.start = w.current AND w.depth > 0
    GROUP BY f.id
    ORDER BY shortest_cycle ASC LIMIT :lim"""),
(
    "string-concat-in-loop",
    "String concatenation with += inside a loop (gocritic stringConcat)",
    "ANSWERS where strings are built with += or + in a loop, producing O(n^2)\n"
    "     allocations because Go strings are immutable.\n"
    "ACT use strings.Builder or a []byte then string(b).\n"
    "MISLEADS a loop with a small constant bound (e.g. 3 iterations) pays less\n"
    "     than a Builder allocation. concat_in_loop is a site count, not a\n"
    "     measurement of how many iterations actually ran.",
    """SELECT s.name, s.concat_in_loop, s.n_loops,
        s.n_string_lit AS string_lits, s.cyclomatic AS cyclo,
        s.fan_in,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.concat_in_loop > 0 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.concat_in_loop DESC, s.n_loops DESC LIMIT :lim"""),
(
    "unsafe-pointer-arith",
    "unsafe.Pointer arithmetic or conversion (gosec G103)",
    "ANSWERS where unsafe.Pointer is used for arithmetic, type punning, or\n"
    "     pointer conversion, bypassing Go's type and memory safety.\n"
    "ACT review each site; replace with a safe alternative (encoding/binary,\n"
    "     reflect, or a typed slice) where possible.\n"
    "MISLEADS cgo interop and performance-critical code may legitimately need\n"
    "     unsafe. The n_cgo_calls column tells whether this is a cgo boundary.",
    """SELECT s.name, s.n_unsafe_ops AS unsafe_ops,
        s.n_unsafe_call AS unsafe_calls, s.n_cgo_calls AS cgo_calls,
        s.n_reflect_ops AS reflect_ops,
        s.fan_in, s.cyclomatic AS cyclo,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE (s.n_unsafe_ops > 0 OR s.n_unsafe_call > 0) AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.fan_in DESC, s.n_unsafe_ops DESC LIMIT :lim"""),
(
    "log-fatal-in-handler",
    "log.Fatal or os.Exit in a request handler (revive deep-exit)",
    "ANSWERS where a function reachable from a request handler calls log.Fatal,\n"
    "     log.Panic, or os.Exit, terminating the entire process for one bad\n"
    "     request.\n"
    "ACT return an error to the caller; let the top-level recover middleware\n"
    "     decide whether to exit.\n"
    "MISLEADS log.Fatal in main() or a startup path is correct. Reachability is\n"
    "     from is_handler=1, capped at 4 hops.",
    """WITH RECURSIVE walk(root, sym, depth) AS (
        SELECT s.id, s.id, 0 FROM symbols s WHERE s.is_handler=1
        UNION
        SELECT w.root, e.callee_id, w.depth+1
        FROM walk w JOIN edges e ON e.caller_id=w.sym
        WHERE w.depth < 4 AND e.is_self=0),
    reach(root, sym, depth) AS (
        SELECT root, sym, MIN(depth) FROM walk GROUP BY root, sym)
    SELECT s.name, s.n_log_fatal AS fatal_calls,
        s.n_exit_call AS exit_calls,
        MIN(r.depth) AS hops_from_handler,
        s.fan_in,
        f.path || ':' || s.line_start AS at
    FROM reach r
    JOIN symbols s ON s.id=r.sym
    JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE (s.n_log_fatal > 0 OR s.n_exit_call > 0)
      AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    GROUP BY s.id
    ORDER BY hops_from_handler ASC, s.n_log_fatal DESC LIMIT :lim"""),
(
    "time-after-in-loop",
    "time.After in a loop leaks timers until they fire (performance)",
    "ANSWERS where time.After is used inside a loop, creating a new timer each\n"
    "     iteration that is not garbage collected until it fires. In a tight\n"
    "     loop this is a memory leak.\n"
    "ACT use time.NewTimer and Reset it, or use a select with a time.AfterFunc.\n"
    "MISLEADS a loop with a long sleep between iterations may not leak enough\n"
    "     to matter. n_time_after_in_loop is a count, not a measurement of\n"
    "     how many timers are live at once.",
    """SELECT s.name, s.n_time_after_in_loop AS time_after_in_loop,
        s.n_loops AS loops, s.n_select AS selects,
        s.n_ctx_done AS ctx_done, s.fan_in,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_time_after_in_loop > 0 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.n_time_after_in_loop DESC, s.n_loops DESC LIMIT :lim"""),
(
    "reflect-call-surface",
    "reflect.Call or reflect.ValueOf on dynamic input (gosec G104)",
    "ANSWERS where reflect is used to call methods dynamically, which bypasses\n"
    "     the type system and can be exploited if the input is attacker-controlled.\n"
    "ACT prefer interfaces over reflect; if reflect is needed, validate the\n"
    "     input type before calling.\n"
    "MISLEADS reflect is correct for serialization, testing, and ORM frameworks.\n"
    "     The graph sees the call but not the input source.",
    """SELECT s.name, s.n_reflect_ops AS reflect_ops,
        s.n_reflect_call AS reflect_calls,
        s.n_unsafe_ops AS unsafe_ops, s.n_type_assert AS type_asserts,
        s.fan_in, s.is_handler AS handler,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_reflect_call > 0 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.fan_in DESC, s.n_reflect_call DESC LIMIT :lim"""),
(
    "env-read-in-handler",
    "os.Getenv or os.LookupEnv in a request path (revive env-in-handler)",
    "ANSWERS where environment variables are read inside a function reachable\n"
    "     from a request handler, so each request pays the env-lookup cost and\n"
    "     the value can change between requests without restart.\n"
    "ACT read env vars at startup (init or main) and pass them through.\n"
    "MISLEADS a handler that reads env to decide a feature flag is a valid\n"
    "     pattern if the flag is expected to change at runtime.",
    """WITH RECURSIVE walk(root, sym, depth) AS (
        SELECT s.id, s.id, 0 FROM symbols s WHERE s.is_handler=1
        UNION
        SELECT w.root, e.callee_id, w.depth+1
        FROM walk w JOIN edges e ON e.caller_id=w.sym
        WHERE w.depth < 4 AND e.is_self=0),
    reach(root, sym, depth) AS (
        SELECT root, sym, MIN(depth) FROM walk GROUP BY root, sym)
    SELECT s.name, s.n_env_read AS env_reads,
        MIN(r.depth) AS hops_from_handler,
        s.fan_in, s.cyclomatic AS cyclo,
        f.path || ':' || s.line_start AS at
    FROM reach r
    JOIN symbols s ON s.id=r.sym
    JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_env_read > 0 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    GROUP BY s.id
    ORDER BY hops_from_handler ASC, s.n_env_read DESC LIMIT :lim"""),
(
    "select-without-default",
    "select without a default case (potential goroutine deadlock)",
    "ANSWERS where a select statement has no default case, so the goroutine\n"
    "     blocks until one case is ready. In a hot path this can deadlock.\n"
    "ACT add a default case or a timeout case (with context cancellation) if\n"
    "     blocking is not intended.\n"
    "MISLEADS a select that blocks on purpose (worker pool, pipeline) is correct.\n"
    "     n_select_default counts defaults; n_select_ctx_done counts context\n"
    "     cancellation cases.",
    """SELECT s.name, s.n_select AS selects,
        s.n_select_default AS defaults,
        s.n_select_ctx_done AS ctx_done_cases,
        s.n_chan_send AS chan_sends, s.n_chan_recv AS chan_recvs,
        s.n_goroutines AS goroutines, s.fan_in,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_select > 0 AND s.n_select_default=0 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.n_select DESC, s.n_goroutines DESC LIMIT :lim"""),
(
    "readall-in-loop",
    "io.ReadAll or ioutil.ReadAll inside a loop (performance)",
    "ANSWERS where io.ReadAll is called inside a loop, reading an entire stream\n"
    "     into memory per iteration. For large streams this is an O(n*m) memory\n"
    "     pattern.\n"
    "ACT read once before the loop, or stream with a bufio.Reader.\n"
    "MISLEADS a loop that reads small, bounded payloads (headers, config lines)\n"
    "     is fine. n_readall_in_loop counts sites, not bytes.",
    """SELECT s.name, s.n_readall_in_loop AS readall_in_loop,
        s.n_loops AS loops, s.io_in_loop AS io_in_loop,
        s.alloc_in_loop, s.cyclomatic AS cyclo, s.fan_in,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_readall_in_loop > 0 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.n_readall_in_loop DESC, s.io_in_loop DESC LIMIT :lim"""),
(
    "iface-satisfaction-breadth",
    "Structs that implicitly satisfy the most interfaces",
    "ANSWERS which concrete types are the load-bearing implementations: a type\n"
    "     satisfying many interfaces is the one every swap-in replacement must\n"
    "     match, and the one whose method name changes break the most contracts.\n"
    "ACT test the top rows against the interface list before renaming any\n"
    "     method; these are the types where a signature change is a broad API\n"
    "     break.\n"
    "MISLEADS satisfaction is method-NAME containment only (see the implements\n"
    "     post_build contract): a type is counted as satisfying an interface\n"
    "     even where signatures disagree, and only in-tree implementors exist.",
    """SELECT im.type_name, COUNT(DISTINCT im.interface_id) AS contracts,
        COUNT(DISTINCT CASE WHEN im.in_test=1 THEN im.interface_id END)
            AS test_contracts,
        SUM(im.n_methods) AS methods_matched,
        COUNT(DISTINCT im.interface_name) AS iface_names
    FROM implements im
    WHERE im.in_test=0
      AND EXISTS (SELECT 1 FROM symbols s
                  JOIN modules m ON m.id=s.module_id
                  WHERE s.name=im.type_name
                    AND COALESCE(m.name,'') LIKE :mod)
    GROUP BY im.type_name
    ORDER BY contracts DESC, methods_matched DESC LIMIT :lim"""),
(
    "concurrency-hotspots",
    "Functions that spawn goroutines AND touch channels: contention hubs",
    "ANSWERS the functions where concurrency is personally invented rather\n"
    "     than inherited: goroutine spawns plus channel sends/recvs in one body\n"
    "     are the primitive shapes the sync package exists to replace.\n"
    "ACT check whether each channel has ONE sender and ONE receiver per\n"
    "     message (the safe shape); multiple senders need locks or per-channel\n"
    "     mutexes.\n"
    "MISLEADS a function that spawns goroutines that later touch channels is\n"
    "     invisible here (the edge points at the goroutine's closure, whose\n"
    "     symbol is separate). Counts are per-symbol, and spawns in a loop are\n"
    "     one spawn call regardless of trip count.",
    """SELECT s.name, s.receiver_type AS receiver,
        s.n_goroutines AS spawns, s.n_chan_send AS sends,
        s.n_chan_recv AS recvs, s.n_chan_close AS closes,
        s.n_go_in_loop AS spawns_in_loop,
        s.n_waitgroup_add AS wg_adds, s.n_lock AS mutexes, s.sloc,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_goroutines + s.n_chan_send + s.n_chan_recv > 0
      AND s.kind IN ('function','method') AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY (s.n_goroutines*4 + s.n_chan_send + s.n_chan_recv) DESC,
        s.sloc DESC LIMIT :lim"""),
(
    "unused-exported",
    "Exported symbols nothing in this tree references",
    "ANSWERS the public API surface the repository itself never calls -- the\n"
    "     symbols released to the world but exercised only by external\n"
    "     consumers, if any.\n"
    "ACT for a library, an exported-and-unused symbol is a candidate for a\n"
    "     deprecation note: the tree does not exercise it, so it is the most\n"
    "     likely to rot. For an application, it is a dead export.\n"
    "MISLEADS external consumers are not in this tree, so a genuinely public\n"
    "     API looks identical to a dead one; `dead-code` is the unexported\n"
    "     counterpart. Interface-implementing methods are excluded because\n"
    "     they are reached through the interface, not by name.",
    """SELECT s.name, s.receiver_type AS receiver, s.sloc,
        s.cyclomatic AS cyclo, s.n_external_calls AS ext_calls,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.fan_in=0 AND s.is_public=1 AND s.is_test=0
      AND s.is_entrypoint=0 AND s.is_handler=0 AND f.is_test=0
      AND f.is_generated=0 AND s.name <> '(anonymous)'
      AND s.kind IN ('function','method')
      AND NOT EXISTS (SELECT 1 FROM implements im
                      WHERE im.type_name = COALESCE(s.receiver_type, ''))
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.sloc DESC LIMIT :lim"""),
(
    "receiver-pointer-mix",
    "Value vs pointer receivers per type: the allocation-copy axis",
    "ANSWERS which types mix receiver styles, which is the complaint that\n"
    "     blows up when the struct grows: a value receiver copies the whole\n"
    "     struct on every call, and a type that mixes the two will not get a\n"
    "     consistent compiler error about it.\n"
    "ACT pick ONE style per type -- pointer receivers for anything with a\n"
    "     slice/header inside, value receivers only for tiny immutable types.\n"
    "MISLEADS methods taking a POINTER-typed receiver alias could be misread;\n"
    "     the count is per declared receiver, not per call, so a hot value\n"
    "     receiver is not weightened by its call frequency here.",
    """SELECT s.receiver_type AS receiver,
        COUNT(*) FILTER (WHERE s.receiver_is_pointer=1) AS ptr_methods,
        COUNT(*) FILTER (WHERE s.receiver_is_pointer=0) AS value_methods,
        COUNT(*) AS total_methods,
        CAST(100.0 * COUNT(*) FILTER (WHERE s.receiver_is_pointer=1)
             / NULLIF(COUNT(*), 0) AS INT) AS pct_ptr,
        MAX(f.path) AS sample_path
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.kind='method' AND s.receiver_type <> '' AND f.is_test=0
      AND s.receiver_is_pointer IN (0,1)
      AND COALESCE(m.name,'') LIKE :mod
    GROUP BY s.receiver_type
    HAVING ptr_methods > 0 AND value_methods > 0
    ORDER BY total_methods DESC, pct_ptr DESC LIMIT :lim"""),
(
    "abstraction-reach",
    "Interfaces satisfied by the most distinct types",
    "ANSWERS the interface contracts with the widest implementation base --\n"
    "     the seams that, if they change, every implementor (and every caller\n"
    "     through the interface) must change with them.\n"
    "ACT these are the interfaces worth keeping stable and worth writing\n"
    "     conformance tests for: a change here is a change across the tree.\n"
    "MISLEADS counts in-tree implementors by method-name containment only; an\n"
    "     interface that stdlib or an external module satisfies is invisible.\n"
    "     `single-impl-interface` is the zero-end of this same ranking.",
    """SELECT i.symbol_id AS iface_id, s.name AS iface, i.n_methods AS methods,
        i.is_exported AS exported,
        COUNT(DISTINCT im.type_name) AS implementors,
        COUNT(DISTINCT CASE WHEN im.in_test=1 THEN im.type_name END)
            AS test_implementors,
        GROUP_CONCAT(DISTINCT im.type_name) AS implemented_by,
        f.path || ':' || s.line_start AS at
    FROM interfaces i
    JOIN symbols s ON s.id=i.symbol_id
    JOIN implements im ON im.interface_id=i.symbol_id
    JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE i.is_constraint=0 AND i.n_methods > 0 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    GROUP BY i.symbol_id
    ORDER BY implementors DESC, i.n_methods DESC LIMIT :lim"""),
(
    "internal-package-leak",
    "Imports reaching into /internal/ from outside its root",
    "ANSWERS import statements whose target contains an internal/ segment,\n"
    "     joined with the importer's own path, so the Go-rule check (only\n"
    "     code under the internal root may import it) is visible per row.\n"
    "ACT for each row, decide whether the importer sits under the internal\n"
    "     root: if not, the import is a layering leak that a module boundary\n"
    "     will break later.\n"
    "MISLEADS the tree does not know the module root, so the query cannot\n"
    "     CONFIRM the leak -- it lists candidate rows and lets the path\n"
    "     comparison be done by eye. Stdlib internal/ packages are excluded\n"
    "     by is_external.",
    """SELECT i.target AS imported, i.alias,
        imp.path AS importer_path, fimp.path AS import_file,
        i.line, i.is_external AS external
    FROM imports i
    JOIN files imp ON imp.id=i.file_id
    JOIN files fimp ON fimp.id=i.target_id
    LEFT JOIN modules m ON m.id=imp.module_id
    WHERE instr(i.target, '/internal/') > 0
      AND i.target_id IS NOT NULL AND i.is_external=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY imp.path, i.line LIMIT :lim"""),
(
    "module-dependency-depth",
    "Longest import chain through each package",
    "ANSWERS how deeply each package sits in the import DAG, and how many\n"
    "     distinct packages it transitively depends on -- the numbers that\n"
    "     describe whether a change here drags a long chain along.\n"
    "ACT a package with max_depth>=5 or many transitive deps is a candidate\n"
    "     for dependency trimming; a leaf package (depth 0, few transitives)\n"
    "     is the safe place to put shared code.\n"
    "MISLEADS computed on RESOLVED in-tree imports only, so stdlib and\n"
    "     external modules terminate a chain rather than extending it; depth\n"
    "     is the longest single chain, not an average, and modules that share\n"
    "     no resolved edge with the tree are absent entirely.",
    """SELECT m.name AS package_, md.max_depth AS chain_depth,
        md.n_direct_imports AS direct_imports,
        md.n_transitive AS transitive_deps,
        (SELECT COUNT(*) FROM symbols s WHERE s.module_id=m.id
          AND s.kind IN ('function','method')) AS n_fns
    FROM module_depth md JOIN modules m ON m.id=md.module_id
    WHERE md.max_depth > 0 AND m.name LIKE :mod
    ORDER BY md.n_transitive DESC, md.max_depth DESC LIMIT :lim"""),
(
    "error-fan-out",
    "Error-returning functions ranked by how far a failure propagates",
    "ANSWERS where an error raised deep down surfaces many frames above:\n"
    "     max_depth is the longest chain of error-returning callees reachable\n"
    "     (f -> g -> h where every hop returns error), so a row with depth 4\n"
    "     means the deepest leaf's failure is carried, unwrapped or not,\n"
    "     through four frames. These are the chains where %w discipline and\n"
    "     context (file, line, operation) are cheapest to add and most often\n"
    "     missing.\n"
    "ACT audit the deepest chains first: each hop is a place an error either\n"
    "     gains context (%w), stays bare (fmt.Errorf without %w), or gets\n"
    "     dropped. `error-not-wrapped` and `error-handling-drift` rank the\n"
    "     same functions on the text signals; this ranks the chain itself.\n"
    "MISLEADS depth counts error-RETURNING hops only -- a callee that absorbs\n"
    "     the error (logs and returns nil) terminates the chain, which is the\n"
    "     containment this query is asking about, not a miss. Edges are\n"
    "     name-resolved, so an error passed through an interface or returned\n"
    "     by a closure is invisible and chains undercount. A chain through a\n"
    "     recursive cycle is reported at the cap of 32; the call graph is\n"
    "     walked in Python per root, O(V*(V+E)) on error-returning symbols\n"
    "     only.",
    """SELECT s.name, s.receiver_type AS receiver, e.max_depth,
        s.n_err_returns AS err_returns, s.n_err_checks AS checks,
        s.n_err_ignored AS ignored, s.fan_in, s.sloc,
        f.path || ':' || s.line_start AS at
    FROM error_chain_depth e JOIN symbols s ON s.id=e.symbol_id
    JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_err_returns > 0 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY e.max_depth DESC, s.fan_in DESC LIMIT :lim"""),
(
    "command-exec-surface",
    "Where the process boundary is crossed (gosec G204)",
    "ANSWERS the functions that reach exec.Command / exec.CommandContext /\n"
    "     syscall.Exec -- every place a string becomes a process.\n"
    "ACT each row needs an allowlisted or constant command; a command built\n"
    "     from variables or input is a command-injection review item.\n"
    "MISLEADS arg literalness is NOT captured -- constant commands rank the\n"
    "     same as tainted ones; a wrapper around exec.Command is invisible\n"
    "     to name matching; the capture is the hazard map, so os.Exit and\n"
    "     syscall.Syscall (same category, different risk) are excluded by\n"
    "     the exact-name denylist on purpose.",
    """SELECT f.path, s.name AS caller, h.pattern AS sink, h.n AS sites,
        h.first_line, s.fan_in
    FROM hazards h
    JOIN symbols s ON s.id = h.symbol_id
    JOIN files f ON f.id = s.file_id
    LEFT JOIN modules m ON m.id = s.module_id
    WHERE h.pattern IN ('exec.Command','exec.CommandContext','syscall.Exec')
      AND f.is_generated = 0 AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.fan_in DESC, h.n DESC
    LIMIT :lim"""),
(
    "sensitive-log-surface",
    "Fatal/panic logging in functions that read environment (OWASP G21)",
    "ANSWERS functions that reach the log.Fatal family AND read environment\n"
    "     variables -- the shape of a secret or credential finding its way\n"
    "     into a log line (log.Println(os.Getenv(\"TOKEN\"))).\n"
    "ACT log the redacted value, or nothing; keep tokens out of every log\n"
    "     sink, not just the fatal ones.\n"
    "MISLEADS same-function co-occurrence is NOT data flow -- the env value\n"
    "     may never reach the log call. os.Getenv is environment, not user\n"
    "     input. Only the log.Fatal/Print family is hazard-captured;\n"
    "    logrus/klog/zap and plain log.Print are invisible to name matching,\n"
    "     and log.Fatal in main() or a startup path is correct.",
    """SELECT f.path, s.name AS caller, h.pattern AS sink, h.n AS sites,
        s.n_env_read AS env_reads
    FROM hazards h
    JOIN symbols s ON s.id = h.symbol_id
    JOIN files f ON f.id = s.file_id
    LEFT JOIN modules m ON m.id = s.module_id
    WHERE h.pattern IN ('log.Fatal','log.Fatalf','log.Fatalln',
                        'log.Panic','log.Panicf')
      AND s.n_env_read > 0
      AND f.is_test = 0 AND f.is_generated = 0 AND COALESCE(m.name,'') LIKE :mod
    ORDER BY h.n DESC, s.n_env_read DESC
    LIMIT :lim"""),
(
    "open-redirect-surface",
    "http.Redirect calls in handlers that read request input (OWASP G26)",
    "ANSWERS functions that call http.Redirect AND read request input\n"
    "     (r.URL.Query / r.FormValue / r.Cookie / r.Form) -- the shape of an\n"
    "     unvalidated redirect: http.Redirect(w, r, r.URL.Query().Get(\"next\"), 302).\n"
    "ACT validate the target against an allowlist; never forward a\n"
    "     user-supplied URL.\n"
    "MISLEADS same-function co-occurrence is NOT data flow -- the input value\n"
    "     may never reach the redirect, and a constant redirect beside an\n"
    "     unrelated input read reads as a violation. The argument text is not\n"
    "     captured, so a fixed target cannot be told from an open one; a\n"
    "     wrapper around http.Redirect is invisible to the exact-name capture;"
    "     a request flow through an alias (rr := r) is invisible to the\n"
    "     receiver set {r, req, request}.",
    """SELECT s.name, s.n_redirect AS redirect_calls,
        COUNT(DISTINCT u.id) AS input_sites,
        GROUP_CONCAT(DISTINCT u.kind) AS kinds,
        s.fan_in, f.path || ':' || s.line_start AS at
    FROM symbols s
    JOIN files f ON f.id = s.file_id
    LEFT JOIN modules m ON m.id = s.module_id
    LEFT JOIN user_input_sites u ON u.symbol_id = s.id
    WHERE s.n_redirect > 0 AND u.kind IS NOT NULL
      AND f.is_test = 0 AND f.is_generated = 0 AND COALESCE(m.name,'') LIKE :mod
    GROUP BY s.id
    ORDER BY s.fan_in DESC, s.n_redirect DESC LIMIT :lim"""),
(
    "hardcoded-secret-candidates",
    "Credential-shaped string literals (OWASP G07)",
    "ANSWERS string literals at least 12 chars long whose text names a\n"
    "     credential (password, token, api_key, secret, bearer, jwt, ...) --\n"
    "     the literal that a committed secret looks like.\n"
    "ACT rotate and move to a secret manager; never commit the literal.\n"
    "MISLEADS a format string or test fixture containing the WORD token/pass\n"
    "     reads as a candidate (the filter is the literal's own text, not its\n"
    "     use); values over 200 chars are truncated at capture; a secret\n"
    "     built from parts or read from an env var is invisible here.\n"
    "     This is a candidate list, not a verdict.",
    """SELECT s.name, sc.value AS candidate, sc.line,
        f.path || ':' || sc.line AS at
    FROM secret_candidates sc
    JOIN symbols s ON s.id = sc.symbol_id
    JOIN files f ON f.id = sc.file_id
    LEFT JOIN modules m ON m.id = s.module_id
    WHERE f.is_test = 0 AND f.is_generated = 0 AND COALESCE(m.name,'') LIKE :mod
      AND sc.value NOT LIKE '/%' AND instr(sc.value, '|') = 0
      AND instr(sc.value, '%') = 0
    ORDER BY length(sc.value) DESC LIMIT :lim"""),
(
    "untrusted-deserialization",
    "json decode sites in functions that read request input (OWASP G19)",
    "ANSWERS functions that call json.Unmarshal / Decoder.Decode AND read\n"
    "     request input -- the shape of deserializing an untrusted payload:\n"
    "     json.NewDecoder(r.Body).Decode(&user).\n"
    "ACT validate the payload schema and size before decoding; never decode\n"
    "     into an interface{} from an untrusted source.\n"
    "MISLEADS same-function co-occurrence is NOT data flow -- the decoded\n"
    "     value may not come from the request, and a constant decode beside\n"
    "     an unrelated input read reads as a violation. The Decode capture is\n"
    "     the bare base name, so encoding/json's Decode and a totally\n"
    "     different library's Decode are indistinguishable here.",
    """SELECT s.name, s.n_deserialize AS decode_calls,
        COUNT(DISTINCT u.id) AS input_sites,
        GROUP_CONCAT(DISTINCT u.kind) AS kinds,
        f.path || ':' || s.line_start AS at
    FROM symbols s
    JOIN files f ON f.id = s.file_id
    LEFT JOIN modules m ON m.id = s.module_id
    LEFT JOIN user_input_sites u ON u.symbol_id = s.id
    WHERE s.n_deserialize > 0 AND u.kind IS NOT NULL
      AND f.is_test = 0 AND f.is_generated = 0 AND COALESCE(m.name,'') LIKE :mod
    GROUP BY s.id
    ORDER BY s.n_deserialize DESC, input_sites DESC LIMIT :lim"""),
(
    "path-traversal-surface",
    "os.* with a non-literal path in input-reading functions (OWASP G12)",
    "ANSWERS functions that call os.Open/ReadFile/WriteFile/Create with a\n"
    "     variable path AND read request input -- the shape of path\n"
    "     traversal: os.ReadFile(r.URL.Query().Get(\"f\")).\n"
    "ACT validate the resolved path stays under a configured root; use\n"
    "     filepath.Clean and a prefix check.\n"
    "MISLEADS same-function co-occurrence is NOT data flow -- the input value\n"
    "     may never reach the open, and a constant-open beside an unrelated\n"
    "     input read reads as a violation. The path is not analyzed: a\n"
    "     variable path is assumed suspicious, a literal is not; a\n"
    "     wrapped-open helper is invisible to the os. capture.",
    """SELECT s.name, s.n_dynamic_open AS open_sites,
        COUNT(DISTINCT u.id) AS input_sites,
        GROUP_CONCAT(DISTINCT u.kind) AS kinds,
        f.path || ':' || s.line_start AS at
    FROM symbols s
    JOIN files f ON f.id = s.file_id
    LEFT JOIN modules m ON m.id = s.module_id
    LEFT JOIN user_input_sites u ON u.symbol_id = s.id
    WHERE s.n_dynamic_open > 0 AND u.kind IS NOT NULL
      AND f.is_test = 0 AND f.is_generated = 0 AND COALESCE(m.name,'') LIKE :mod
    GROUP BY s.id
    ORDER BY s.n_dynamic_open DESC, input_sites DESC LIMIT :lim"""),
(
    "zip-slip-surface",
    "archive/zip access sites (OWASP G29)",
    "ANSWERS functions that touch archive/zip -- the surface where an entry\n"
    "     name becomes a filesystem path.\n"
    "ACT validate every entry name against a containment check before\n"
    "     extraction; reject ../ and absolute paths.\n"
    "MISLEADS the containment check is not modeled: a function that checks\n"
    "     each name before extraction ranks the same as one that does not.\n"
    "     The capture is the dotted zip. name; a renamed zip helper is\n"
    "     invisible.",
    """SELECT s.name, s.n_zip_read AS zip_access,
        s.sloc, f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id = s.file_id
    LEFT JOIN modules m ON m.id = s.module_id
    WHERE s.n_zip_read > 0 AND f.is_test = 0 AND f.is_generated = 0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.n_zip_read DESC, s.sloc DESC LIMIT :lim"""),
(
    "mass-assignment-surface",
    "Decode into request-body readers (OWASP G30)",
    "ANSWERS functions that decode JSON in functions that read the request\n"
    "     BODY -- the shape of mass assignment: json.NewDecoder(r.Body)\n"
    "     .Decode(&user) maps every request field onto the struct.\n"
    "ACT bind to a DTO with only the fields you accept; never decode a\n"
    "     request body into a persistent model.\n"
    "MISLEADS same-function co-occurrence is NOT data flow -- the decoded\n"
    "     source may not be the body, and a body read beside an unrelated\n"
    "     decode reads as a violation. Which struct fields the body can set\n"
    "     is not modeled; a schema-validated decode ranks the same as an\n"
    "     unchecked one.",
    """SELECT s.name, s.n_deserialize AS decode_calls,
        COUNT(DISTINCT u.id) AS body_reads,
        f.path || ':' || s.line_start AS at
    FROM symbols s
    JOIN files f ON f.id = s.file_id
    LEFT JOIN modules m ON m.id = s.module_id
    LEFT JOIN user_input_sites u ON u.symbol_id = s.id AND u.kind = 'body'
    WHERE s.n_deserialize > 0 AND u.kind IS NOT NULL
      AND f.is_test = 0 AND f.is_generated = 0 AND COALESCE(m.name,'') LIKE :mod
    GROUP BY s.id
    ORDER BY s.n_deserialize DESC, body_reads DESC LIMIT :lim"""),
(
    "unauthenticated-input-surface",
    "Request input read with no auth call in the function (OWASP G01)",
    "ANSWERS functions that read request input and contain NO auth-family\n"
    "     call (RequireAuth, CheckAuth, jwt, session, login) -- the surface\n"
    "     where a handler may be missing its authorization check.\n"
    "ACT add the auth middleware call; verify the route is in the protected\n"
    "     group.\n"
    "MISLEADS auth usually lives in MIDDLEWARE, not the handler -- this\n"
    "     query sees the handler only, so a fully-protected mux still ranks\n"
    "     every handler as open. A login or public endpoint legitimately has\n"
    "     no auth. The markers are name-based substrings, so a wrapper\n"
    "     around the auth call is invisible and counts as open.",
    """SELECT s.name, COUNT(DISTINCT u.id) AS input_sites,
        GROUP_CONCAT(DISTINCT u.kind) AS kinds,
        f.path || ':' || s.line_start AS at
    FROM symbols s
    JOIN files f ON f.id = s.file_id
    LEFT JOIN modules m ON m.id = s.module_id
    LEFT JOIN user_input_sites u ON u.symbol_id = s.id
    WHERE u.kind IS NOT NULL AND s.n_auth_call = 0
      AND f.is_test = 0 AND f.is_generated = 0 AND COALESCE(m.name,'') LIKE :mod
    GROUP BY s.id
    ORDER BY input_sites DESC, s.sloc DESC LIMIT :lim"""),
(
    "deprecated-stdlib-calls",
    "Call sites of deprecated stdlib entry points (staticcheck SA1019)",
    "ANSWERS where deprecated stdlib functions are still called, with the\n"
    "     replacement inline. The ioutil.* family moved to io/os in Go 1.16.\n"
    "ACT swap to the replacement; each row is mechanical.\n"
    "MISLEADS the denylist ships inline and goes stale with each Go release;\n"
    "     ioutil.WriteFile/Discard/NopCloser and rand.Seed/rand.Read are NOT\n"
    "     hazard-captured and are absent here (rand.Read is contextual\n"
    "     anyway -- crypto/rand where security-relevant, math/rand/v2\n"
    "     elsewhere); a dotted alias (io.ReadAll) is unaffected.",
    """WITH dep(name, replacement) AS (VALUES
        ('ioutil.ReadAll','io.ReadAll'), ('ioutil.ReadFile','os.ReadFile'))
    SELECT f.path, s.name AS caller, h.pattern, dep.replacement, h.n
    FROM hazards h
    JOIN dep ON dep.name = h.pattern
    JOIN symbols s ON s.id = h.symbol_id
    JOIN files f ON f.id = s.file_id
    LEFT JOIN modules m ON m.id = s.module_id
    WHERE f.is_generated = 0 AND COALESCE(m.name,'') LIKE :mod
    ORDER BY h.n DESC
    LIMIT :lim"""),
(
    "deferred-close-unchecked",
    "defer x.Close() whose error return vanishes (staticcheck SA5001)",
    "ANSWERS defer sites where a Close()/Flush() error is silently dropped,\n"
    "     ranked by how much of the tree calls the deferrer: a write error\n"
    "     that surfaces at defer time is exactly the one nobody checks.\n"
    "ACT join the close error into the named return, or accept the loss\n"
    "     deliberately (a comment is cheaper than a bug report).\n"
    "MISLEADS Close errors on read handles are benign; whether THIS Close\n"
    "     returns error is name-inferred, not type-checked; in-loop defers\n"
    "     belong to defer-lifetime and are excluded here.",
    """SELECT f.path, s.name, d.target, d.line, s.fan_in
    FROM defers d
    JOIN symbols s ON s.id = d.symbol_id
    JOIN files f ON f.id = s.file_id
    LEFT JOIN modules m ON m.id = s.module_id
    WHERE d.is_close = 1 AND d.in_loop = 0
      AND f.is_generated = 0 AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.fan_in DESC
    LIMIT :lim"""),
(
    "http-request-no-context",
    "http.NewRequest without a context (noctx territory)",
    "ANSWERS functions that build requests with the context-less\n"
    "     http.NewRequest instead of http.NewRequestWithContext: the request\n"
    "     cannot be cancelled, and a slow peer hangs the caller forever.\n"
    "ACT pass the caller's context (or context.Background() where none\n"
    "     exists) via NewRequestWithContext.\n"
    "MISLEADS a wrapper around NewRequest that threads ctx internally is\n"
    "     invisible to name matching; the plain form in a CLI one-shot is\n"
    "     the legitimate row; the http.Client without a Timeout is a\n"
    "     different (pre-existing) family and does not appear here.",
    """SELECT f.path, s.name AS caller, h.n AS sites, h.first_line, s.fan_in
    FROM hazards h
    JOIN symbols s ON s.id = h.symbol_id
    JOIN files f ON f.id = s.file_id
    LEFT JOIN modules m ON m.id = s.module_id
    WHERE h.pattern = 'http.NewRequest'
      AND f.is_generated = 0 AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.fan_in DESC, h.n DESC
    LIMIT :lim"""),
(
    "file-read-surface",
    "os.ReadFile / os.Open call sites by fan-in",
    "ANSWERS where whole-file reads and opens happen -- the functions most\n"
    "     likely to hit path-traversal (G304) or unbounded reads, ranked by\n"
    "     how much of the tree trusts them.\n"
    "ACT for a read whose path is derived from input, validate the path;\n"
    "     for os.ReadFile of a remote/untrusted file, prefer a reader with\n"
    "     a size limit.\n"
    "MISLEADS path origin is NOT captured -- a constant path ranks the same\n"
    "     as one built from user input; os.Open without a follow-on read\n"
    "     still appears (it IS the open surface); handler-adjacency is\n"
    "     approximated by fan_in.",
    """SELECT f.path, s.name AS caller, h.pattern AS api, h.n AS sites,
        h.first_line, s.fan_in
    FROM hazards h
    JOIN symbols s ON s.id = h.symbol_id
    JOIN files f ON f.id = s.file_id
    LEFT JOIN modules m ON m.id = s.module_id
    WHERE h.pattern IN ('os.ReadFile','os.Open','ioutil.ReadFile')
      AND f.is_generated = 0 AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.fan_in DESC, h.n DESC
    LIMIT :lim"""),
(
    "sql-injection-build",
    "SQL assembled by string concatenation (gosec G201/G202 territory)",
    "ANSWERS functions that build SQL by concatenating string literals: the\n"
    "     value can only be injected if a variable reaches the concat, and\n"
    "     this is the review list for exactly that question, ranked by how\n"
    "     much of the tree trusts the builder.\n"
    "ACT use placeholders (QueryContext with args), or parameterise the\n"
    "     identifier with a whitelist -- concatenation is never the fix.\n"
    "MISLEADS n_sql_concat counts SQL literal sites whose parent is a `+`\n"
    "     expression: a query assembled by Sprintf or passed in whole as a\n"
    "     variable is invisible here, and a concat of two constants (no\n"
    "     injection possible) reads the same as one mixing a variable.\n"
    "     `string-concat-in-loop` owns the generic allocation shape.",
    """SELECT s.name, s.receiver_type AS receiver, s.n_sql_concat AS concat_sql,
        s.query_in_loop, s.fan_in,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_sql_concat > 0 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.n_sql_concat DESC, s.fan_in DESC LIMIT :lim"""),
(
    "context-built-in-loop",
    "context.WithTimeout / WithDeadline / WithCancel inside a loop",
    "ANSWERS deadline/cancel contexts created per iteration: WithTimeout in\n"
    "     a loop leaks one timer per pass until the iteration ends, and\n"
    "     WithCancel recreated every iteration can never be the thing the\n"
    "     body waits on -- the loop restarts it.\n"
    "ACT create the context once before the loop; per-iteration deadlines\n"
    "     belong to the work function, not the loop.\n"
    "MISLEADS the counter is base-name based: a method literally named\n"
    "     WithTimeout on a non-context type also matches; a context created\n"
    "     in a helper called from the loop is invisible; a short loop over\n"
    "     a fixed slice pays little -- this ranks review order.",
    """SELECT s.name, s.n_ctx_in_loop AS in_loop, s.max_loop_depth AS depth,
        s.n_ctx_withcancel AS ctx_creations, s.fan_in,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_ctx_in_loop > 0 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.n_ctx_in_loop DESC, s.fan_in DESC LIMIT :lim"""),
(
    "nil-error-after-check",
    "if err != nil { return nil }: the error is dropped at the check (nilerr)",
    "ANSWERS functions whose error check leads straight to a nil return:\n"
    "     the error is detected and then discarded. Callers cannot tell\n"
    "     success from swallowed failure, and a nil error from a function\n"
    "     that just failed is the hardest-to-reproduce bug class in Go.\n"
    "ACT return the error (`return nil, err` in the multi-value shape); a\n"
    "     deliberately ignored failure needs a comment saying why.\n"
    "MISLEADS the shape is text-matched on the if-consequence: `return 0, nil`\n"
    "     (a zero value plus nil error) is missed, and an if-block that\n"
    "     returns nil BEFORE checking a second condition is caught even when\n"
    "     the later return is honest -- read the row, do not trust it.",
    """SELECT s.name, s.receiver_type AS receiver, s.n_err_nil_return AS dropped,
        s.n_err_checks AS checks, s.n_err_returns AS err_returns,
        s.fan_in, f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_err_nil_return > 0 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.n_err_nil_return DESC, s.fan_in DESC LIMIT :lim"""),
(
    "loopvar-rebind-dead",
    "`v := v` rebinds under go >= 1.22 (copyloopvar territory)",
    "ANSWERS the dead rebind: `for _, v := range xs { v := v ... }`. Before\n"
    "     Go 1.22 the rebind captured a per-iteration copy; from 1.22 the\n"
    "     loop variable already is per-iteration, so the rebind is a no-op\n"
    "     that reads as if it does something.\n"
    "ACT delete the rebind; the semantics are already what the rebind\n"
    "     pretended to provide.\n"
    "MISLEADS gated on the go directive from go.mod: below 1.22 the rebind\n"
    "     is REAL and the row would be a false positive, so nothing fires;\n"
    "     the go directive can be lower than the toolchain actually used;\n"
    "     the text shape is `name := name`, so an unrelated same-name\n"
    "     shadow in a loop body also matches.",
    """SELECT s.name, s.n_loopvar_rebind AS rebinds, s.max_loop_depth AS depth,
        s.fan_in, f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_loopvar_rebind > 0 AND f.is_test=0
      AND (SELECT CAST(substr(value,1,instr(value,'.')-1) AS INT)*100
                + CAST(substr(value,instr(value,'.')+1) AS INT)
           FROM meta WHERE key='go_version') >= 122
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.n_loopvar_rebind DESC, s.fan_in DESC LIMIT :lim"""),
(
    "insecure-tls-config",
    "tls.Config with InsecureSkipVerify: true (gosec G402)",
    "ANSWERS every tls.Config that disables certificate verification: the\n"
    "     connection accepts ANY certificate, which turns TLS into\n"
    "     obfuscated plaintext. One wrong flag in a config struct is the\n"
    "     whole class.\n"
    "ACT use the default verification; if a test or internal service needs\n"
    "     a skip, pin the expected cert instead of disabling the check.\n"
    "MISLEADS text-matched on the composite literal: a config built\n"
    "     field-by-field (`c := tls.Config{}; c.InsecureSkipVerify = true`)\n"
    "     is missed, and a flag set from a variable (`= allowInsecure`)\n"
    "     reads as absent here.",
    """SELECT s.name, s.n_insecure_tls AS insecure_cfgs, s.fan_in,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_insecure_tls > 0 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.n_insecure_tls DESC, s.fan_in DESC LIMIT :lim"""),
# ===========================================================================
# Concurrency-lifecycle pack. Capture added: symbols.n_wg_done / n_wait_call /
# n_sleep / n_rows_err_check / n_timer_new / n_timer_stop / n_semaphore (and
# n_cancel_called, wired after sitting dead), defers.is_done, the wg_sites
# table, and a channels fix -- the make(chan) capture sat in an unreachable
# branch, so `channels` was empty on every build.
# ===========================================================================
(
    "waitgroup-add-inside-goroutine",
    "WaitGroup.Add runs inside the spawned goroutine, not before the spawn (SA2000)",
    "ANSWERS which `go` statements race on their own WaitGroup: the Add that\n"
    "     must happen before Wait fires sits lexically inside the spawned\n"
    "     closure (or inside the named target function), so Wait can observe\n"
    "     a zero counter and return while goroutines are still appearing.\n"
    "ACT hoist `wg.Add(1)` above the `go` line at the spawn site; add a\n"
    "     regression test that runs under -race.\n"
    "MISLEADS a target that deliberately re-adds (batch regrouping) is flagged;\n"
    "     Add sites are matched per receiver variable, so a second, unrelated\n"
    "     counter named like a WaitGroup rides along; a spawned closure that\n"
    "     calls Add one more frame down is missed (one hop only).",
    """WITH spawns AS (
        SELECT g.symbol_id AS sid, g.line AS go_line, g.target,
            s.name AS spawner, s.fan_in, f.path || ':' || g.line AS at
        FROM goroutines g
        JOIN symbols s ON s.id=g.symbol_id
        JOIN files f ON f.id=g.file_id
        LEFT JOIN modules m ON m.id=s.module_id
        WHERE g.has_waitgroup=1 AND f.is_test=0 AND f.is_generated=0
          AND COALESCE(m.name,'') LIKE :mod),
    closure_adds AS (
        SELECT symbol_id, COUNT(*) AS adds
        FROM wg_sites WHERE op='Add' AND in_goroutine=1 GROUP BY symbol_id),
    target_adds AS (
        SELECT t.id AS tid, t.name AS target_fn, COUNT(*) AS adds
        FROM wg_sites w
        JOIN symbols t ON t.id=w.symbol_id
        JOIN files tf ON tf.id=t.file_id AND tf.is_test=0 AND tf.is_generated=0
        WHERE w.op='Add' AND w.in_goroutine=0
        GROUP BY t.id)
    SELECT sp.spawner, sp.at, '(closure)' AS add_site, ca.adds, sp.fan_in
    FROM spawns sp JOIN closure_adds ca ON ca.symbol_id=sp.sid
    UNION ALL
    SELECT sp.spawner, sp.at, ta.target_fn, ta.adds, sp.fan_in
    FROM spawns sp
    JOIN symbols t2 ON t2.name = sp.target
        AND t2.kind IN ('function','method')
    JOIN files tf2 ON tf2.id=t2.file_id AND tf2.is_test=0 AND tf2.is_generated=0
    JOIN target_adds ta ON ta.tid = t2.id
    ORDER BY adds DESC, fan_in DESC LIMIT :lim"""),
(
    "wg-done-missing-in-target",
    "WaitGroup-guarded spawn whose target never calls Done: Wait blocks forever",
    "ANSWERS spawns the spawner arms with a WaitGroup but whose target function\n"
    "     -- nor anything it calls one hop out -- ever balances the Add with a\n"
    "     Done. The first Wait on that counter never returns.\n"
    "ACT put `defer wg.Done()` as the first statement of the target, or switch\n"
    "     the fan-out to an errgroup so Wait is structural.\n"
    "MISLEADS the target may signal completion through a done channel instead\n"
    "     of the WaitGroup (check has_chan_exit); a Done delegated two or more\n"
    "     hops below the target is missed; dead-code targets inflate the list.",
    """WITH spawns AS (
        SELECT g.symbol_id AS sid, g.line AS go_line, g.target,
            s.name AS spawner, f.path || ':' || g.line AS at
        FROM goroutines g
        JOIN symbols s ON s.id=g.symbol_id
        JOIN files f ON f.id=g.file_id
        LEFT JOIN modules m ON m.id=s.module_id
        WHERE g.has_waitgroup=1 AND g.target <> '' AND f.is_test=0
          AND f.is_generated=0 AND COALESCE(m.name,'') LIKE :mod),
    tgt AS (
        SELECT sp.spawner, sp.at, t.id AS tid, t.name AS target_fn, t.fan_in
        FROM spawns sp
        JOIN symbols t ON t.name = sp.target
            AND t.kind IN ('function','method')
        JOIN files tf ON tf.id=t.file_id AND tf.is_test=0 AND tf.is_generated=0)
    SELECT tg.spawner, tg.at, tg.target_fn, tg.fan_in AS target_fan_in
    FROM tgt tg
    WHERE tg.tid NOT IN (SELECT w.symbol_id FROM wg_sites w WHERE w.op='Done')
      AND tg.tid NOT IN (SELECT d.symbol_id FROM defers d WHERE d.is_done=1)
      AND tg.tid NOT IN (SELECT e.caller_id FROM edges e
                         JOIN wg_sites w2 ON w2.symbol_id=e.callee_id
                         WHERE w2.op='Done')
      AND tg.tid NOT IN (SELECT e2.caller_id FROM edges e2
                         JOIN defers d2 ON d2.symbol_id=e2.callee_id
                         WHERE d2.is_done=1)
    ORDER BY target_fan_in DESC LIMIT :lim"""),
(
    "waitgroup-imbalance",
    "A function Adds a WaitGroup more often than it Done/Waits it, and spawns nothing",
    "ANSWERS per-WaitGroup-variable balance inside one function: more Adds than\n"
    "     Dones and Waits combined, with no WaitGroup-carrying spawn that the\n"
    "     Done could have been delegated to -- the counter leaks upward and a\n"
    "     later Wait never fires.\n"
    "ACT pair every Add with a `defer wg.Done()` in the same scope, or hand\n"
    "     the whole counter to one owner.\n"
    "MISLEADS the normal spawner shape (Add here, Done inside the spawned\n"
    "     function) is EXCLUDED only when the spawn is visible as\n"
    "     has_waitgroup; a Done two hops down, or reached through an interface,\n"
    "     still reads as a deficit; two WaitGroups sharing a variable name in\n"
    "     one function are merged.",
    """WITH ops AS (
        SELECT symbol_id, var,
            SUM(op='Add') AS adds, SUM(op='Done') AS dones,
            SUM(op='Wait') AS waits
        FROM wg_sites GROUP BY symbol_id, var),
    delegated AS (
        SELECT DISTINCT symbol_id FROM goroutines WHERE has_waitgroup=1)
    SELECT s.name AS fn, o.var AS wg_var, o.adds, o.dones, o.waits,
        o.adds - o.dones AS unbalanced, s.fan_in,
        f.path || ':' || s.line_start AS at
    FROM ops o
    JOIN symbols s ON s.id=o.symbol_id
    JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE o.adds > o.dones + o.waits
      AND o.symbol_id NOT IN (SELECT symbol_id FROM delegated)
      AND f.is_test=0 AND f.is_generated=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY unbalanced DESC, s.fan_in DESC LIMIT :lim"""),
(
    "double-lock-same-receiver-path",
    "Locking method calls a sibling method on the same receiver that also locks",
    "ANSWERS self-deadlock paths: sync.Mutex is not reentrant, so an edge from\n"
    "     a locking method to another locking method with the SAME receiver\n"
    "     type deadlocks the second time anyone takes the first path.\n"
    "ACT split the inner method into a lock-free variant (fooLocked) and call\n"
    "     that from both entry points.\n"
    "MISLEADS the two methods may lock DIFFERENT mutex fields of one struct\n"
    "     (nesting different locks is legal); the call may sit after an\n"
    "     Unlock on every path, which line-level analysis cannot prove;\n"
    "     only the DIRECT edge is reported, so three-hop cycles stay hidden.",
    """SELECT mo.name AS outer_fn, mo.receiver_type AS recv,
        mi.name AS inner_fn, mi.line_start AS inner_line,
        mo.n_lock_call AS outer_locks, mi.n_lock_call AS inner_locks,
        mo.cyclomatic AS cyclo, mo.fan_in,
        f.path || ':' || mo.line_start AS at
    FROM symbols mo
    JOIN edges e ON e.caller_id=mo.id
    JOIN symbols mi ON mi.id=e.callee_id AND mi.id <> mo.id
        AND mi.n_lock_call>0 AND mi.receiver_type = mo.receiver_type
    JOIN files f ON f.id=mo.file_id
    LEFT JOIN modules m ON m.id=mo.module_id
    WHERE mo.n_lock_call>0 AND mo.receiver_type<>''
      AND f.is_test=0 AND f.is_generated=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY mo.n_lock_call + mo.fan_in DESC, mo.fan_in DESC LIMIT :lim"""),
(
    "os-exit-under-call-tree",
    "os.Exit/log.Fatal buried below an entry point, skipping every caller's defers",
    "ANSWERS exit sites reachable from a handler or main: the process dies\n"
    "     there and the defers of EVERY frame above the exit never run --\n"
    "     flushes, unlocks and acks included. defers_skipped_near counts the\n"
    "     defers in the immediate callers this graph can see.\n"
    "ACT return the error up to main; keep exactly one exit, in main.\n"
    "MISLEADS a legitimate exit in CLI setup reachable only from main is\n"
    "     normal; reachability caps at 8 hops, so a deeper path hides the row;\n"
    "     defers_skipped_near is one hop of callers, not the whole stack.",
    """WITH RECURSIVE down(root, sym, depth) AS (
            SELECT s.id, s.id, 0 FROM symbols s
            WHERE s.is_handler=1 OR s.is_entrypoint=1
            UNION
            SELECT d.root, e.callee_id, d.depth+1
            FROM down d JOIN edges e ON e.caller_id=d.sym
            WHERE d.depth < 8 AND e.is_self=0),
    reach AS (SELECT DISTINCT sym FROM down),
    exit_fns AS (
        SELECT s.id, s.name, s.n_exit_call, s.n_log_fatal, s.fan_in,
            f.path || ':' || s.line_start AS at
        FROM symbols s JOIN files f ON f.id=s.file_id
        LEFT JOIN modules m ON m.id=s.module_id
        WHERE f.is_test=0 AND f.is_generated=0
          AND (s.n_exit_call>0 OR s.n_log_fatal>0)
          AND COALESCE(m.name,'') LIKE :mod)
    SELECT x.name AS exit_fn, x.at, x.n_exit_call, x.n_log_fatal,
        (SELECT COUNT(*) FROM reach WHERE sym=x.id) AS entry_reachable,
        COALESCE((SELECT SUM(c2.n_defer) FROM
              (SELECT DISTINCT e.caller_id FROM edges e
               JOIN reach r ON r.sym=e.caller_id
               WHERE e.callee_id=x.id) dc
            JOIN symbols c2 ON c2.id=dc.caller_id), 0) AS defers_skipped_near,
        x.fan_in
    FROM exit_fns x
    WHERE x.id IN (SELECT sym FROM reach)
    ORDER BY entry_reachable DESC, defers_skipped_near DESC, x.fan_in DESC
    LIMIT :lim"""),
(
    "lock-held-across-io-transitive",
    "Critical section stays held across I/O two or three calls deep",
    "ANSWERS functions that lock and whose transitively-called functions (up to\n"
    "     3 hops) do network, SQL, exec or file I/O: the lock is held for the\n"
    "     duration of someone else's syscall, and every contender queues.\n"
    "ACT copy the guarded state out, unlock, then do the I/O; or move to\n"
    "     per-key locks.\n"
    "MISLEADS the I/O may sit behind an early release this line-ordered view\n"
    "     cannot see; the io callee may be a cold error path; deliberate\n"
    "     write-behind under a lock is a design choice, not a bug.",
    """WITH RECURSIVE lockers AS (
        SELECT s.id FROM symbols s JOIN files f ON f.id=s.file_id
        WHERE s.n_lock_call>0 AND f.is_test=0 AND f.is_generated=0),
    reach(root, node, depth) AS (
        SELECT l.id, e.callee_id, 1 FROM lockers l
        JOIN edges e ON e.caller_id=l.id WHERE e.is_self=0
        UNION
        SELECT r.root, e.callee_id, r.depth+1 FROM reach r
        JOIN edges e ON e.caller_id=r.node
        WHERE r.depth < 3 AND e.is_self=0),
    io_under AS (
        SELECT r.root, COUNT(DISTINCT r.node) AS io_callees,
            MAX(r.depth) AS max_hops
        FROM reach r
        JOIN symbols c ON c.id=r.node
        JOIN files cf ON cf.id=c.file_id
        WHERE (c.n_net>0 OR c.n_sql>0 OR c.n_exec>0 OR c.n_io>0)
          AND cf.is_test=0
        GROUP BY r.root)
    SELECT s.name AS lock_fn, iu.io_callees, iu.max_hops,
        s.n_lock_call AS locks, s.n_unlock_call AS unlocks, s.fan_in,
        f.path || ':' || s.line_start AS at
    FROM io_under iu
    JOIN symbols s ON s.id=iu.root
    JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE COALESCE(m.name,'') LIKE :mod
    ORDER BY io_callees DESC, max_hops DESC, s.fan_in DESC LIMIT :lim"""),
(
    "lock-held-across-dynamic-call",
    "Mutex held while calling through an interface: unknown code in the critical section",
    "ANSWERS functions that both lock and perform dynamic (interface) calls,\n"
    "     weighted by interface-typed parameters: any implementer -- including\n"
    "     one that calls back into the locked type -- runs inside the lock.\n"
    "ACT extract what you need under the lock, unlock, then invoke the\n"
    "     callback; or document the no-reentrancy invariant on the type.\n"
    "MISLEADS n_dynamic_calls counts innocent fmt.Stringer and error-interface\n"
    "     calls too; visitor-style callback-under-lock is a deliberate design;\n"
    "     whether the dispatched method actually touches this type is beyond\n"
    "     name-based dispatch resolution.",
    """SELECT s.name AS lock_fn, s.n_lock_call AS locks,
        s.n_dynamic_calls AS dyn_calls, s.n_iface_params AS iface_params,
        s.n_iface_returns, s.cyclomatic AS cyclo, s.fan_in,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_lock_call>0 AND s.n_dynamic_calls>0
      AND (s.n_iface_params>0 OR s.n_iface_returns>0)
      AND f.is_test=0 AND f.is_generated=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.n_dynamic_calls * s.fan_in DESC LIMIT :lim"""),
(
    "resource-returned-never-closed",
    "Caller of a Rows/Body/File-returning helper never closes it: ownership leak",
    "ANSWERS call sites of helpers that RETURN sql.Rows, an http.Response, a\n"
    "     ReadCloser or a file, where the receiving caller neither defers a\n"
    "     Close nor calls one. The opener looks fine to a per-file linter; the\n"
    "     leak lives one frame up, across the call edge.\n"
    "ACT `defer r.Close()` at each leaking call site, or wrap the resource in\n"
    "     the helper and return a cleanup func instead.\n"
    "MISLEADS the caller may pass the resource onward to a function that\n"
    "     closes it (ownership transfer beyond one hop); a shared\n"
    "     drainAndClose helper reads as never-closed; type matching is on the\n"
    "     return-type TEXT, so custom wrapper types are missed.",
    """WITH openers AS (
        SELECT s.id, s.name AS opener, s.return_type, s.fan_in
        FROM symbols s JOIN files f ON f.id=s.file_id
        WHERE f.is_test=0 AND f.is_generated=0
          AND (instr(s.return_type,'sql.Rows')>0
            OR instr(s.return_type,'sql.Stmt')>0
            OR instr(s.return_type,'sql.Tx')>0
            OR instr(s.return_type,'http.Response')>0
            OR instr(s.return_type,'io.ReadCloser')>0
            OR instr(s.return_type,'io.Closer')>0
            OR instr(s.return_type,'*os.File')>0))
    SELECT o.opener, o.return_type, o.fan_in AS opener_fan_in,
        c.name AS caller_never_closes, c.n_defer_close AS defer_closes,
        cf.path || ':' || cs.line AS at
    FROM openers o
    JOIN callsites cs ON cs.callee_id=o.id
    JOIN symbols c ON c.id=cs.caller_id
    JOIN files cf ON cf.id=c.file_id
    LEFT JOIN modules m ON m.id=c.module_id
    WHERE c.n_defer_close=0 AND c.n_close_call=0
      AND cf.is_test=0 AND cf.is_generated=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY opener_fan_in DESC, c.fan_in DESC LIMIT :lim"""),
(
    "panic-source-reachable-from-entry",
    "panic or unchecked type-assert reachable from a handler/main with no recover guard",
    "ANSWERS functions containing panic() or a forced type assertion that are\n"
    "     reachable from a request handler or entrypoint AND whose direct\n"
    "     callers all lack recover: one bad input kills the process.\n"
    "ACT make the assertion comma-ok and return an error, or add a recover in\n"
    "     the request wrapper at the handler boundary.\n"
    "MISLEADS a recover ANYWHERE on a caller suppresses the row even if that\n"
    "     path is rarely taken; nil-map writes and index-out-of-range panics\n"
    "     carry no panic() call and stay invisible; reachability caps at 8\n"
    "     hops.",
    """WITH RECURSIVE down(root, sym, depth) AS (
            SELECT s.id, s.id, 0 FROM symbols s
            WHERE s.is_handler=1 OR s.is_entrypoint=1
            UNION
            SELECT d.root, e.callee_id, d.depth+1
            FROM down d JOIN edges e ON e.caller_id=d.sym
            WHERE d.depth < 8 AND e.is_self=0),
    reach AS (SELECT DISTINCT sym FROM down),
    panic_fns AS (
        SELECT s.id, s.name,
            s.n_panic + s.n_type_assert_unchecked AS sources, s.fan_in,
            f.path || ':' || s.line_start AS at
        FROM symbols s JOIN files f ON f.id=s.file_id
        LEFT JOIN modules m ON m.id=s.module_id
        WHERE f.is_test=0 AND f.is_generated=0
          AND (s.n_panic>0 OR s.n_type_assert_unchecked>0)
          AND COALESCE(m.name,'') LIKE :mod)
    SELECT p.name AS panic_fn, p.at, p.sources, p.fan_in
    FROM panic_fns p
    WHERE p.id IN (SELECT sym FROM reach)
      AND NOT EXISTS (SELECT 1 FROM edges e JOIN symbols c ON c.id=e.caller_id
                      WHERE e.callee_id=p.id AND c.n_recover>0)
    ORDER BY p.sources DESC, p.fan_in DESC LIMIT :lim"""),
(
    "recover-wrong-side-of-spawn",
    "Spawner has the recover, goroutine body can panic: recover never fires for the child",
    "ANSWERS spawn sites whose own function recovers but whose spawned target\n"
    "     contains panic() or unchecked type assertions and no recover of its\n"
    "     own: recover() only works inside the panicking goroutine, so the\n"
    "     guard the author wrote guards the wrong frame.\n"
    "ACT make the first statement of the goroutine body\n"
    "     `defer func(){ if r := recover(); ... }()`.\n"
    "MISLEADS the target may be panic-free in practice (n_panic counts only\n"
    "     explicit panics and unchecked asserts); inline closure bodies are\n"
    "     counted in the spawner, not as a separate target; a target that\n"
    "     delegates into an existing safe runner is missed.",
    """SELECT sp.name AS spawn_fn, g.line AS go_line,
        f.path || ':' || g.line AS at, sp.n_recover AS recover_in_spawner,
        t.name AS target_fn,
        t.n_panic + t.n_type_assert_unchecked AS panic_sites, t.fan_in
    FROM goroutines g
    JOIN symbols sp ON sp.id=g.symbol_id
    JOIN files f ON f.id=g.file_id
    LEFT JOIN modules m ON m.id=sp.module_id
    JOIN symbols t ON t.name = g.target AND t.kind IN ('function','method')
    JOIN files tf ON tf.id=t.file_id AND tf.is_test=0 AND tf.is_generated=0
    WHERE f.is_test=0 AND f.is_generated=0
      AND g.has_recover=0 AND sp.n_recover>0 AND g.target <> ''
      AND (t.n_panic>0 OR t.n_type_assert_unchecked>0)
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY panic_sites DESC, t.fan_in DESC LIMIT :lim"""),
(
    "goroutine-select-missing-ctx-done",
    "Spawned goroutine selects but never observes cancellation: it outlives its producer",
    "ANSWERS spawns that pass no context whose target runs a select with no\n"
    "     ctx.Done case: when the producer goes away the goroutine blocks in\n"
    "     that select forever -- the leak goleak trips over at shutdown.\n"
    "ACT pass ctx into the target and add a `<-ctx.Done()` case, or close a\n"
    "     done channel the select already watches.\n"
    "MISLEADS the target may exit via a channel close the select DOES watch\n"
    "     (has_chan_exit is filtered, but a close one frame deeper is not\n"
    "     visible); a deliberately immortal daemon loop looks like a leak;\n"
    "     send-side selects guarded by default are fine without ctx.",
    """SELECT sp.name AS spawn_fn, g.line AS go_line,
        f.path || ':' || g.line AS at, t.name AS target_fn,
        t.n_select AS selects, t.n_select_default AS default_cases,
        t.n_chan_recv AS recvs, t.fan_in AS target_fan_in
    FROM goroutines g
    JOIN symbols sp ON sp.id=g.symbol_id
    JOIN files f ON f.id=g.file_id
    LEFT JOIN modules m ON m.id=sp.module_id
    JOIN symbols t ON t.name = g.target AND t.kind IN ('function','method')
    JOIN files tf ON tf.id=t.file_id AND tf.is_test=0 AND tf.is_generated=0
    WHERE f.is_test=0 AND f.is_generated=0
      AND g.has_ctx=0 AND g.has_chan_exit=0 AND g.target <> ''
      AND t.n_select>0 AND t.n_select_ctx_done=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY selects DESC, target_fan_in DESC LIMIT :lim"""),
(
    "ticker-timer-never-stopped",
    "time.NewTicker/NewTimer with no Stop on any nearby path (SA1015 family)",
    "ANSWERS ticker and timer producers that create more tickers than they or\n"
    "     any of their callers Stop: each leaked Ticker holds a runtime timer\n"
    "     and its channel buffer forever.\n"
    "ACT `defer t.Stop()` immediately after NewTicker/NewTimer; replace bare\n"
    "     long-lived time.Tick with a stopped ticker.\n"
    "MISLEADS a Stop two hops below the producer is invisible (one caller hop\n"
    "     is checked); one-shot timer use that outlives the request on purpose\n"
    "     is not a leak; the counts are per function, so two tickers with one\n"
    "     shared Stop still read as a deficit.",
    """SELECT s.name AS timer_fn, s.n_timer_new AS timers,
        s.n_timer_stop AS stops, s.n_sleep AS sleeps,
        s.n_goroutines AS spawns, s.fan_in,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_timer_new > s.n_timer_stop AND s.n_timer_new > 0
      AND f.is_test=0 AND f.is_generated=0
      AND NOT EXISTS (SELECT 1 FROM edges e JOIN symbols c ON c.id=e.caller_id
                      WHERE e.callee_id=s.id AND c.n_timer_stop >= s.n_timer_new)
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.n_timer_new DESC, s.fan_in DESC LIMIT :lim"""),
(
    "unbounded-spawn-fanout",
    "Per-item `go` in a loop with no errgroup or semaphore: concurrency is unbounded",
    "ANSWERS in-loop spawns with neither an errgroup nor any semaphore acquire\n"
    "     (SetLimit/Acquire/TryAcquire) in the spawning function, on handlers\n"
    "     and other high fan-in code: one request over 10,000 items is 10,000\n"
    "     goroutines and whatever they open.\n"
    "ACT wrap with errgroup.SetLimit, a buffered-channel semaphore, or a fixed\n"
    "     worker pool.\n"
    "MISLEADS a loop over a tiny fixed set (config entries) is harmless; a\n"
    "     limiter acquired by a CALLER and passed in reads as absent; a\n"
    "     WaitGroup bounds TIME here, not CONCURRENCY, and is deliberately\n"
    "     not counted as bounding.",
    """SELECT sp.name AS spawn_fn, g.line AS go_line,
        f.path || ':' || g.line AS at, g.loop_depth,
        sp.n_goroutines AS spawns_in_fn, sp.fan_in, sp.is_handler
    FROM goroutines g
    JOIN symbols sp ON sp.id=g.symbol_id
    JOIN files f ON f.id=g.file_id
    LEFT JOIN modules m ON m.id=sp.module_id
    WHERE f.is_test=0 AND f.is_generated=0
      AND g.in_loop=1 AND g.has_errgroup=0 AND sp.n_semaphore=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY g.loop_depth DESC, sp.is_handler DESC, sp.fan_in DESC LIMIT :lim"""),
(
    "http-default-client-under-handler",
    "Handler reaches http.Get/DefaultClient within 4 hops: a request can hang forever",
    "ANSWERS functions using the timeout-less default client (http.Get, Post,\n"
    "     Head, DefaultClient.Do) that are reachable from a request handler\n"
    "     within 4 hops: the missing timeout belongs to the path, not to the\n"
    "     helper's own file.\n"
    "ACT inject a client with explicit Timeout (and transport timeouts) at the\n"
    "     handler boundary; or thread ctx and use NewRequestWithContext.\n"
    "MISLEADS a ctx-aware call through the default client is cancellable\n"
    "     anyway; a custom client built in middleware is invisible; reachability\n"
    "     beyond 4 hops is truncated.",
    """WITH RECURSIVE down(root, sym, depth) AS (
            SELECT s.id, s.id, 0 FROM symbols s WHERE s.is_handler=1
            UNION
            SELECT d.root, e.callee_id, d.depth+1
            FROM down d JOIN edges e ON e.caller_id=d.sym
            WHERE d.depth < 4 AND e.is_self=0),
    reach AS (SELECT DISTINCT sym FROM down)
    SELECT s.name AS default_client_fn, s.n_http_default_client AS sites,
        s.n_net, s.fan_in, f.path || ':' || s.line_start AS at
    FROM reach
    JOIN symbols s ON s.id=reach.sym
    JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE f.is_test=0 AND f.is_generated=0 AND s.n_http_default_client>0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY sites DESC, s.fan_in DESC LIMIT :lim"""),
(
    "errgroup-without-wait",
    "errgroup.Group created but neither the function nor its callers ever Wait",
    "ANSWERS functions that construct an errgroup.Group / WithContext group but\n"
    "     call no Wait themselves -- and none of their callers do either: the\n"
    "     group's errors vanish and WithContext's cancel leaks the ctx.\n"
    "ACT `defer g.Wait()` (and `defer cancel()`) in the scope that owns the\n"
    "     group.\n"
    "MISLEADS g.Go is a plain call, not a `go` statement, so the anchor is the\n"
    "     group CONSTRUCTION and a Wait invoked through an interface or a\n"
    "     helper is invisible; deliberate fire-and-forget groups with their\n"
    "     own done channel are misread; a group handed to another function to\n"
    "     be waited on there reads as never-awaited.",
    """WITH owners AS (
        SELECT h.symbol_id, SUM(h.n) AS sites FROM hazards h
        WHERE h.pattern IN ('errgroup.Group','errgroup.WithContext')
        GROUP BY h.symbol_id),
    waiters AS (
        SELECT s.id FROM symbols s
        WHERE s.n_wait_call>0
           OR EXISTS (SELECT 1 FROM wg_sites w WHERE w.symbol_id=s.id
                      AND w.op='Wait'))
    SELECT s.name AS group_owner, o.sites AS group_sites,
        s.n_wait_call AS own_waits, s.fan_in,
        f.path || ':' || s.line_start AS at
    FROM owners o
    JOIN symbols s ON s.id=o.symbol_id
    JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE f.is_test=0 AND f.is_generated=0
      AND s.id NOT IN (SELECT id FROM waiters)
      AND s.id NOT IN (SELECT e.caller_id FROM edges e
                       JOIN waiters w2 ON w2.id=e.callee_id)
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY group_sites DESC, s.fan_in DESC LIMIT :lim"""),
(
    "channel-never-closed",
    "A channel someone receives from is never closed in its owning function",
    "ANSWERS channels whose owning function receives (or selects) but never\n"
    "     closes, and no other local evidence of a closer exists: every\n"
    "     `for range ch` consumer of this channel terminates only when the\n"
    "     producer happens to close it from another function.\n"
    "ACT have the producer `defer close(ch)` after its send loop, or range in\n"
    "     a select loop that also watches ctx.Done().\n"
    "MISLEADS closed_in_fn is matched per close() ARGUMENT in the owning\n"
    "     function only -- a close in a helper, or of an aliased channel,\n"
    "     reads as never-closed; eternal event-bus channels are a legitimate\n"
    "     design; channels whose size is a variable carry capacity -1 and are\n"
    "     filtered to the never-closed side only.",
    """SELECT s.name AS declared_in, c.name AS chan_var, c.elem_type,
        c.capacity AS cap_, s.n_chan_send AS sends,
        s.n_chan_recv + s.n_select AS recv_sites,
        s.n_goroutines AS spawns, s.fan_in,
        f.path || ':' || c.line AS at
    FROM channels c
    JOIN symbols s ON s.id=c.symbol_id
    JOIN files f ON f.id=c.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE c.closed_in_fn=0 AND f.is_test=0 AND f.is_generated=0
      AND (s.n_chan_recv>0 OR s.n_select>0)
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY recv_sites DESC, s.fan_in DESC LIMIT :lim"""),
(
    "signal-notify-unbuffered",
    "signal.Notify on an unbuffered channel drops signals (SA1017, go vet sigchanyzer)",
    "ANSWERS signal.Notify call sites in functions that also declare an\n"
    "     unbuffered (or variable-sized) channel: the kernel deliverable is\n"
    "     dropped while nothing is receiving on the channel right then.\n"
    "ACT declare the signal channel `make(chan os.Signal, 1)`.\n"
    "MISLEADS the pairing is by same-function presence, so the buffered\n"
    "     channel may live one frame away and be passed in; capacity -1 means\n"
    "     the size is a variable and could be fine; a Notify that never\n"
    "     expects a second signal is harmless.",
    """SELECT s.name AS notify_fn, h.n AS notify_sites,
        c.name AS chan_var, c.capacity AS cap_, s.fan_in,
        f.path || ':' || c.line AS at
    FROM hazards h
    JOIN symbols s ON s.id=h.symbol_id
    JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    JOIN channels c ON c.symbol_id=s.id AND c.capacity<=0
    WHERE h.pattern='signal.Notify' AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.fan_in DESC, h.n DESC LIMIT :lim"""),
(
    "error-chain-terminated-by-discard",
    "A 3+ deep error chain whose top caller discards errors (errcheck x error-fan-out)",
    "ANSWERS deep error-propagation chains (max_depth >= 3) where the caller at\n"
    "     the chain head has discarded error returns: three frames of honest\n"
    "     plumbing feed a caller that throws the failure away.\n"
    "ACT log-or-wrap at the top caller; if the error will never be handled,\n"
    "     delete the plumbing instead.\n"
    "MISLEADS n_err_ignored includes deliberate `_ = fmt.Fprintln`-style\n"
    "     ignores of non-error returns; the discarder may retry instead of\n"
    "     propagating; chain depth counts only hops where EVERY callee returns\n"
    "     error, so aborted branches are invisible.",
    """SELECT s.name AS chain_top, ecd.max_depth, s.fan_in,
        d.name AS discarding_caller, d.n_err_ignored AS ignored,
        df.path || ':' || d.line_start AS at
    FROM error_chain_depth ecd
    JOIN symbols s ON s.id=ecd.symbol_id
    JOIN files sf ON sf.id=s.file_id AND sf.is_test=0
    JOIN edges e ON e.callee_id=s.id
    JOIN symbols d ON d.id=e.caller_id AND d.n_err_ignored>0
    JOIN files df ON df.id=d.file_id AND df.is_test=0 AND df.is_generated=0
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE ecd.max_depth>=3
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY ecd.max_depth DESC, s.fan_in DESC LIMIT :lim"""),
(
    "boundary-bare-error",
    "High fan-in function passes errors through with zero added context (wrapcheck)",
    "ANSWERS heavily-called functions that return errors from external or\n"
    "     unresolved calls without ever wrapping one: callers get `open file`\n"
    "     with no word of WHO was being read or why.\n"
    "ACT add `fmt.Errorf(\"reading config: %w\", err)` once at the boundary --\n"
    "     every caller inherits the context.\n"
    "MISLEADS internal same-module pass-through is fine per wrapcheck's own\n"
    "     defaults; context added by a custom error type is invisible to the\n"
    "     counters; must-style helpers that deliberately return the raw error\n"
    "     are idiomatic.",
    """SELECT s.name AS bare_wrapper, s.n_external_calls AS ext_calls,
        s.n_unresolved_calls AS unresolved, s.n_err_wrapped AS wrapped,
        s.n_err_returns AS err_returns, s.fan_in,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE f.is_test=0 AND f.is_generated=0
      AND s.n_err_returns>0 AND s.n_err_wrapped=0
      AND s.n_external_calls + s.n_unresolved_calls > 0
      AND s.fan_in>=3
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.fan_in DESC, s.n_external_calls DESC LIMIT :lim"""),
(
    "init-side-effects",
    "init() doing I/O, env reads, exec, exits or spawning goroutines (Uber: Avoid init())",
    "ANSWERS init functions whose side effects run at process start -- file and\n"
    "     network I/O, SQL, exec, os.Getenv, os.Exit/log.Fatal, goroutines --\n"
    "     ranked by how many modules import the package: every importer\n"
    "     re-executes the failure.\n"
    "ACT move to an explicit Start/Close owned object; make failure an error\n"
    "     that main decides about.\n"
    "MISLEADS embedding templates and registering database drivers in init is\n"
    "     idiomatic and intentional; var-initializer expressions doing the\n"
    "     same thing carry no is_init flag; import fan-in counts packages,\n"
    "     not runtime executions.",
    """SELECT s.name AS init_fn,
        s.n_io + s.n_net + s.n_sql + s.n_exec + s.n_env_read
            + s.n_goroutines + s.n_exit_call AS side_effects,
        s.n_io, s.n_net, s.n_sql, s.n_exec,
        s.n_env_read AS env_reads, s.n_goroutines AS spawns,
        s.n_exit_call AS exits,
        COALESCE(m.name,'') AS package_, COALESCE(m.fan_in,0) AS import_fan_in,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.is_init=1 AND f.is_test=0
      AND (s.n_io>0 OR s.n_net>0 OR s.n_sql>0 OR s.n_exec>0
           OR s.n_env_read>0 OR s.n_goroutines>0 OR s.n_exit_call>0)
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY side_effects DESC, import_fan_in DESC LIMIT :lim"""),
(
    "rows-err-never-checked",
    "SQL-querying function where neither it nor its callers ever check rows.Err (rowserrcheck)",
    "ANSWERS functions that query and drain rows with no rows.Err() call in\n"
    "     them or in their direct callers: a connection drop mid-iteration\n"
    "     ends the loop looking like SUCCESS.\n"
    "ACT `if err := rows.Err(); err != nil {...}` after each drain loop, or\n"
    "     return rows wrapped in a helper that checks.\n"
    "MISLEADS rows.Scan errors usually surface the same failure one iteration\n"
    "     earlier (not always: the last batch); the check may live in a drain\n"
    "     helper two hops away; n_sql counts Exec with no rows too.",
    """WITH sql_fns AS (
        SELECT s.id, s.name, s.n_sql, s.fan_in,
            f.path || ':' || s.line_start AS at
        FROM symbols s JOIN files f ON f.id=s.file_id
        LEFT JOIN modules m ON m.id=s.module_id
        WHERE s.n_sql>0 AND s.n_rows_err_check=0
          AND f.is_test=0 AND f.is_generated=0
          AND COALESCE(m.name,'') LIKE :mod)
    SELECT q.name AS query_fn, q.n_sql, q.fan_in, q.at
    FROM sql_fns q
    WHERE NOT EXISTS (
        SELECT 1 FROM callsites cs JOIN symbols c ON c.id=cs.caller_id
        WHERE cs.callee_id=q.id AND c.n_rows_err_check>0)
    ORDER BY q.n_sql DESC, q.fan_in DESC LIMIT :lim"""),
(
    "sleep-under-request-path",
    "time.Sleep reachable from a request handler: every request pays the latency",
    "ANSWERS functions containing time.Sleep that are reachable from a handler\n"
    "     within 3 hops, ranked by distance: the same sleep in a background\n"
    "     janitor is fine, on a request path it is a deadline violation.\n"
    "ACT replace with a select on a ctx-aware timer, or move the work off the\n"
    "     request path entirely.\n"
    "MISLEADS tiny backoff sleeps inside retry loops can be intentional (check\n"
    "     ctx_done_checks on the row); poll-wait loops are sometimes the only\n"
    "     option against an external system; reachability caps at 3 hops.",
    """WITH RECURSIVE down(root, sym, depth) AS (
            SELECT s.id, s.id, 0 FROM symbols s WHERE s.is_handler=1
            UNION
            SELECT d.root, e.callee_id, d.depth+1
            FROM down d JOIN edges e ON e.caller_id=d.sym
            WHERE d.depth < 3 AND e.is_self=0),
    reach AS (SELECT sym, MIN(depth) AS hops FROM down GROUP BY sym)
    SELECT s.name AS sleeping_fn, r.hops, s.n_sleep AS sleeps,
        s.n_ctx_done AS ctx_done_checks, s.fan_in,
        f.path || ':' || s.line_start AS at
    FROM reach r
    JOIN symbols s ON s.id=r.sym
    JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE f.is_test=0 AND f.is_generated=0 AND s.n_sleep>0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY r.hops ASC, s.fan_in DESC LIMIT :lim"""),
(
    "captured-var-mutated-after-spawn",
    "Closure goroutine spawned in a loop while the spawner keeps assigning locals",
    "ANSWERS closure spawns inside loops where the spawning function also does\n"
    "     ordinary assignments: the goroutine captures locals by reference\n"
    "     while the spawner's remaining statements mutate them -- the classic\n"
    "     data race the race detector sees only under load.\n"
    "ACT pass the values as parameters to the goroutine\n"
    "     (`go func(v T){...}(v)`), or copy before the spawn.\n"
    "MISLEADS on go >= 1.22 loop variables are per-iteration (the plain local\n"
    "     capture race is still real); a WaitGroup join before the mutation\n"
    "     orders the accesses and is safe but invisible here; n_assign counts\n"
    "     assignments anywhere in the spawner, not specifically after the go\n"
    "     line.",
    """SELECT sp.name AS spawn_fn, g.line AS go_line,
        f.path || ':' || g.line AS at, g.loop_depth,
        sp.n_assign AS assignments, sp.n_loopvar_capture AS loopvar_caps,
        sp.fan_in
    FROM goroutines g
    JOIN symbols sp ON sp.id=g.symbol_id
    JOIN files f ON f.id=g.file_id
    LEFT JOIN modules m ON m.id=sp.module_id
    WHERE f.is_test=0 AND f.is_generated=0
      AND g.is_closure=1 AND g.in_loop=1 AND sp.n_assign>0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY g.loop_depth DESC, sp.fan_in DESC LIMIT :lim"""),
(
    "handler-without-request-context",
    "Request handler takes no context and does network/SQL/spawn work in it",
    "ANSWERS functions with a handler signature but no context.Context\n"
    "     parameter that still do net/sql calls or spawn goroutines: every\n"
    "     client disconnect, timeout and shutdown signal stops at that\n"
    "     signature.\n"
    "ACT add ctx as the first parameter and thread it to the first blocking\n"
    "     call.\n"
    "MISLEADS handlers whose framework injects cancellation another way\n"
    "     (gin's own request-scoped context) are flagged wrongly; a handler\n"
    "     that only reads memory is fine without ctx; a ctx param alone does\n"
    "     not prove it is USED -- see ctx-propagation-break for that side.",
    """SELECT s.name AS handler, s.n_ctx_params AS ctx_params,
        s.n_net + s.n_sql AS blocking_calls, s.n_goroutines AS spawns,
        s.fan_in, f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.is_handler=1 AND s.n_ctx_params=0
      AND (s.n_net>0 OR s.n_sql>0 OR s.n_goroutines>0)
      AND f.is_test=0 AND f.is_generated=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.fan_in DESC LIMIT :lim"""),
(
    "context-in-struct",
    "context.Context stored in a struct field: every method inherits a stale ctx (containedctx)",
    "ANSWERS struct types with a context.Context field, ranked by method count:\n"
    "     the context frozen at construction shadows the caller's deadline on\n"
    "     every method it guards, and the Go wiki's rule is that ctx travels\n"
    "     as the first parameter, never inside a struct.\n"
    "ACT drop the field; pass ctx explicitly to the methods that block.\n"
    "MISLEADS long-lived request objects whose ctx is refreshed per request\n"
    "     look the same as the frozen kind; test fixtures with a ctx field are\n"
    "     harmless; a struct holding a ctx it only forwards at construction\n"
    "     time is a style call, not a bug.",
    """WITH meths AS (
        SELECT receiver_type, COUNT(*) AS n FROM symbols
        WHERE kind='method' AND receiver_type<>'' GROUP BY receiver_type)
    SELECT ty.name AS type_, st.n_fields, COALESCE(meths.n,0) AS methods,
        COALESCE(m.name,'') AS package_, COALESCE(m.fan_in,0) AS import_fan_in,
        f.path || ':' || ty.line_start AS at
    FROM structs st
    JOIN symbols ty ON ty.id=st.symbol_id
    JOIN files f ON f.id=ty.file_id
    LEFT JOIN modules m ON m.id=ty.module_id
    LEFT JOIN meths ON meths.receiver_type=ty.name
    WHERE st.has_ctx_field=1 AND f.is_test=0 AND f.is_generated=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY methods DESC, import_fan_in DESC LIMIT :lim"""),
(
    "blocking-sync-function",
    "Function both spawns goroutines and blocks on net/sql: concurrency the caller cannot see (Google style)",
    "ANSWERS functions that spawn goroutines AND do their own blocking network\n"
    "     or SQL calls, with callers: the Google style guide wants synchronous\n"
    "     functions and the CONCURRENCY decided by the caller -- this shape\n"
    "     hides goroutine lifecycles inside a call that looks like a function.\n"
    "ACT split it: a synchronous core the caller wraps, or a documented async\n"
    "     API that returns a handle.\n"
    "MISLEADS an internal worker pool that fully joins before returning is\n"
    "     synchronous in effect and flagged anyway; the sql/net counters say\n"
    "     nothing about how long the calls block; a wrapper that merely\n"
    "     forwards to one blocking helper is usually fine.",
    """SELECT s.name AS fn, s.n_goroutines AS spawns,
        s.n_net + s.n_sql AS blocking_calls, s.fan_in, s.is_handler,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_goroutines>0 AND (s.n_net>0 OR s.n_sql>0) AND s.fan_in>0
      AND f.is_test=0 AND f.is_generated=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.fan_in DESC LIMIT :lim""")
]

GoAnalyzer.METRICS = [
(
    "graph-blindspots",
    "Read this first: where the call graph cannot see",
    "ANSWERS how much of every other answer here is guesswork.\n"
    "ACT external calls are out of scope by design (stdlib, modules) and are\n"
    "     NOT counted as blindness. Unresolved means we genuinely lost it --\n"
    "     usually an interface method with several implementations.\n"
    "MISLEADS a resolved edge can still be wrong: a call to an interface method\n"
    "     resolves to whichever single implementation exists, and if two exist\n"
    "     this refuses to guess and lands here instead.",
    """SELECT m.name AS package_, COUNT(DISTINCT s.id) AS fns,
        COALESCE(SUM(s.n_calls),0) AS calls,
        COALESCE(SUM(s.n_external_calls),0) AS external,
        COALESCE(SUM(s.n_unresolved_calls),0) AS unresolved,
        COALESCE(SUM(s.n_reflect_ops),0) AS reflect_,
        CAST(100.0*SUM(s.n_unresolved_calls)/NULLIF(SUM(s.n_calls),0) AS INT) AS pct_blind
    FROM symbols s JOIN modules m ON m.id=s.module_id
    WHERE s.kind IN ('function','method') AND m.name LIKE :mod
    GROUP BY m.id HAVING calls>0
    ORDER BY unresolved DESC LIMIT :lim"""),
(
    "single-impl-interface",
    "Interfaces satisfied by exactly one type: abstraction over nothing",
    "ANSWERS a design question no linter asks. One implementor means the\n"
    "     interface is a hypothetical seam, and it costs a dynamic dispatch and\n"
    "     a heap escape at every call.\n"
    "ACT delete it and use the concrete type -- UNLESS it exists for a test\n"
    "     double, or it is declared in the CONSUMER package, which is the\n"
    "     idiomatic Go pattern and is correct.\n"
    "MISLEADS satisfaction is computed on method NAMES, not signatures, so a\n"
    "     type with Close() error matches an interface wanting Close() even\n"
    "     where the Go compiler would not. It also sees only types in THIS\n"
    "     tree, so an implementor in another module is invisible.",
    """WITH t AS (
        SELECT substr(type,
                length(rtrim(type, 'abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_')) + 1)
            AS tail_ident, COUNT(*) AS n
        FROM params
        GROUP BY tail_ident)
    SELECT s.name AS iface, i.n_methods AS methods,
        i.n_embedded AS embedded, i.is_exported AS exported,
        i.is_constraint AS type_constraint,
        COALESCE(SUM(t.n), 0) AS used_as_param,
        (SELECT COUNT(*) FROM implements im
         WHERE im.interface_id=s.id AND im.in_test=0) AS impls,
        (SELECT COUNT(*) FROM implements im2
         WHERE im2.interface_id=s.id AND im2.in_test=1) AS test_impls,
        (SELECT GROUP_CONCAT(im3.type_name) FROM implements im3
         WHERE im3.interface_id=s.id) AS implemented_by,
        i.methods,
        f.path || ':' || s.line_start AS at
    FROM interfaces i
    JOIN symbols s ON s.id=i.symbol_id
    JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    LEFT JOIN t ON t.tail_ident = s.name
    WHERE i.is_constraint=0 AND i.n_methods > 0
      AND f.is_test=0 AND COALESCE(m.name,'') LIKE :mod
      AND (SELECT COUNT(*) FROM implements im4
           WHERE im4.interface_id=s.id AND im4.in_test=0) = 1
    ORDER BY used_as_param DESC, i.n_methods DESC LIMIT :lim"""),
(
    "heap-pressure-loops",
    "Sprintf, uncapped append and conversions inside loops",
    "ANSWERS the ways a Go loop moves work to the heap: formatting, growing a\n"
    "     slice from zero capacity, string/[]byte copies, boxing into any.\n"
    "ACT make([]T, 0, n) when you know n; strconv over Sprintf; take a concrete\n"
    "     type instead of any.\n"
    "MISLEADS none of this is confirmed without `go build -gcflags=-m`. The\n"
    "     compiler's escape analysis may already be stack-allocating the row\n"
    "     you are reading. This is a candidate list for a benchmark.",
    """SELECT s.name, s.n_sprintf_in_loop AS sprintf_loop,
        s.n_append_in_loop AS append_loop, s.n_make_no_cap AS make_no_cap,
        s.n_conv_in_loop AS conv_loop, s.n_any_params AS any_params,
        s.n_iface_params AS iface_params, s.max_loop_depth AS depth,
        s.fan_in,
        (s.n_sprintf_in_loop*4 + s.n_append_in_loop*2 + s.n_make_no_cap*3
         + s.n_conv_in_loop*2 + s.n_any_params) * (1 + s.max_loop_depth)
         AS heap_pressure,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.max_loop_depth > 0
      AND (s.n_sprintf_in_loop + s.n_append_in_loop + s.n_make_no_cap
           + s.n_conv_in_loop + s.n_any_params) > 0
      AND f.is_test=0 AND COALESCE(m.name,'') LIKE :mod
    ORDER BY heap_pressure DESC LIMIT :lim"""),
(
    "range-value-copy",
    "for _, v := range over big structs: a memcpy per element",
    "ANSWERS the silent per-iteration copy that costs est_size bytes every time\n"
    "     round the loop.\n"
    "ACT range over the index and take &s[i], or hold pointers. The win scales\n"
    "     with the struct size.\n"
    "MISLEADS est_size is a 64-bit model estimate. Go lays fields out in\n"
    "     DECLARATION order -- reordering is an open proposal, not a thing the\n"
    "     compiler does -- but it pads for alignment, and nothing here computes\n"
    "     the exact size, which is why size_exact is 0 on every row. Anything\n"
    "     under about 32 bytes copies for free.",
    """WITH mod_struct_max AS (
        SELECT ty.module_id AS mid, MAX(st.est_size) AS mx_est
        FROM structs st JOIN symbols ty ON ty.id=st.symbol_id
        GROUP BY ty.module_id)
    SELECT s.name AS in_fn, s.n_range_value_copy AS range_copies,
        s.max_loop_depth AS depth, s.call_in_loop AS calls_in_loop,
        s.fan_in, s.sloc, mx.mx_est AS biggest_local_struct,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    LEFT JOIN mod_struct_max mx ON mx.mid = s.module_id
    WHERE s.n_range_value_copy > 0 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.n_range_value_copy DESC, s.max_loop_depth DESC LIMIT :lim"""),
(
    "risk-ranked",
    "Review order: if you can only read N functions this week, which N",
    "ANSWERS which functions combine complexity with dangerous operations.\n"
    "ACT start at the top. The score weights unsafe, cgo, exec and SQL building\n"
    "     far above raw complexity.\n"
    "MISLEADS a heuristic, not a finding. Generated and vendored files are\n"
    "     excluded, so the real top of the list may be in code this hid.",
    """SELECT s.name, s.risk_score AS risk, s.cyclomatic AS cyclo,
        s.cognitive AS cog, s.max_nesting AS nest,
        s.n_unsafe + s.n_cgo AS unsafe_, s.n_err_ignored AS err_ign,
        s.n_goroutines AS spawns, s.fan_in,
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
    "ACT a win in a high-fan-in leaf pays once per caller.\n"
    "MISLEADS fan_in counts STATIC call sites, not runtime frequency.",
    """SELECT s.name, s.fan_in, s.n_callsites AS sites, s.fan_out,
        s.cyclomatic AS cyclo, s.sloc, s.has_doc AS doc,
        s.receiver_type AS recv, COALESCE(m.name,'') AS package_,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.kind IN ('function','method') AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.fan_in DESC, s.cyclomatic DESC LIMIT :lim"""),
(
    "god-functions",
    "Functions doing too much, by every measure at once",
    "ANSWERS which functions are hardest to hold in your head.\n"
    "ACT split by responsibility. n_elif tells you whether it is a flat\n"
    "     dispatch (extract a map) or real nesting (extract functions).\n"
    "MISLEADS a long flat dispatch reads far more easily than a short deeply\n"
    "     nested one, which is why this sorts by cognitive rather than sloc.",
    """SELECT s.name, s.sloc, s.cyclomatic AS cyclo, s.cognitive AS cog,
        s.max_nesting AS nest, s.n_elif AS elifs, s.n_returns AS returns_,
        s.n_naked_returns AS naked, s.n_params, s.maintainability AS maint,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.kind IN ('function','method') AND f.is_generated=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.cognitive DESC LIMIT :lim"""),
(
    "module-coupling",
    "Which packages depend on which, and how unstable that makes them",
    "ANSWERS which packages are hard to change because everything leans on them.\n"
    "ACT instability near 0 with high fan_in is a good place for stable\n"
    "     abstractions and a bad place for volatile logic.\n"
    "MISLEADS instability is a ratio, so a package with one edge each way scores\n"
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
    "ACT a FIXME in a function forty things depend on outranks a TODO in a CLI.\n"
    "MISLEADS marker age is invisible -- git blame is the missing column. Many\n"
    "     of these were resolved years ago and the comment stayed.",
    """SELECT k.kind, f.path, k.line, SUBSTR(k.text,1,58) AS text,
        COALESCE(s.name,'(package level)') AS in_fn,
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
    "ACT a file here contributed nothing. Build-tagged files that do not apply\n"
    "     to this platform are the usual innocent explanation.\n"
    "MISLEADS a file can parse perfectly and still be misunderstood. This shows\n"
    "     hard failures only.",
    """SELECT f.path, f.lines, f.n_parse_errors AS errors,
        f.n_missing_nodes AS missing, f.parsed,
        f.is_generated AS generated, f.is_test AS test,
        (SELECT GROUP_CONCAT(b.expr) FROM build_tags b
         WHERE b.file_id=f.id) AS build_tags
    FROM files f
    LEFT JOIN modules m ON m.id=f.module_id
    WHERE (f.n_parse_errors>0 OR f.parsed=0)
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY f.lines DESC LIMIT :lim"""),
(
    "wrapper-function",
    "Function that only calls one other function (gocritic wrapperFunc)",
    "ANSWERS where a function body is a single call to another function, adding\n"
    "     no logic — a wrapper that exists only to rename or forward.\n"
    "ACT inline the call or document why the indirection is needed (interface\n"
    "     conformance, deprecated alias, test seam).\n"
    "MISLEADS a wrapper that satisfies an interface or provides a test seam is\n"
    "     intentional. The graph sees n_calls=1 and n_unique_calls=1 but cannot\n"
    "     see whether the signature differs from the callee.",
    """SELECT s.name, s.n_calls, s.n_unique_calls AS unique_callees,
        s.sloc, s.n_params, s.fan_in,
        (SELECT c.name FROM symbols c JOIN edges e ON e.callee_id=c.id
         WHERE e.caller_id=s.id AND e.is_self=0 LIMIT 1) AS sole_callee,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_calls=1 AND s.n_unique_calls=1 AND s.sloc<=3
      AND s.is_recursive=0
      AND s.kind IN ('function','method') AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.fan_in DESC LIMIT :lim"""),
(
    "naked-return-complex",
    "Naked return in a function with high complexity (golint)",
    "ANSWERS where a function uses naked returns (implicit return of named\n"
    "     results) and has enough complexity that the return value is hard to\n"
    "     trace, which is golint's naked-return warning.\n"
    "ACT use explicit returns in functions with cyclomatic > 10 or > 50 SLOC.\n"
    "MISLEADS naked returns in short functions (defer cleanup, early-exit\n"
    "     patterns) are idiomatic and clear.",
    """SELECT s.name, s.n_naked_returns AS naked_returns,
        s.n_named_results AS named_results,
        s.cyclomatic AS cyclo, s.sloc, s.max_nesting AS nesting,
        s.fan_in,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_naked_returns > 0 AND s.cyclomatic > 10 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.cyclomatic DESC, s.n_naked_returns DESC LIMIT :lim"""),
(
    "scattered-concerns",
    "A function called from many different modules (shotgun-surgery smell)",
    "ANSWERS which functions are called from a high number of distinct modules,\n"
    "     so any change to them ripples across the codebase.\n"
    "ACT consider splitting the function or making the contract more stable.\n"
    "     The modules column lists the dependents.\n"
    "MISLEADS a utility like log.Printf is called from everywhere and is\n"
    "     intentionally stable; high fan_in from many modules is the design.",
    """SELECT s.name, agg.n AS n_caller_modules,
        s.fan_in, s.cyclomatic AS cyclo, s.sloc,
        agg.names AS modules,
        f.path || ':' || s.line_start AS at
    FROM symbols s
    JOIN (SELECT callee_id,
                 COUNT(DISTINCT module_id) AS n,
                 GROUP_CONCAT(DISTINCT module_name) AS names
          FROM (SELECT e.callee_id, m.id AS module_id,
                       m.name AS module_name
                FROM edges e
                JOIN symbols caller ON caller.id=e.caller_id
                LEFT JOIN modules m ON m.id=caller.module_id
                WHERE e.is_self=0 AND COALESCE(m.name,'') LIKE :mod) t
          GROUP BY callee_id HAVING n > 5) agg
      ON agg.callee_id = s.id
    JOIN files f ON f.id=s.file_id
    WHERE s.kind IN ('function','method') AND f.is_test=0
    ORDER BY n_caller_modules DESC, s.fan_in DESC LIMIT :lim"""),
(
    "god-module",
    "A package with too many functions and high total complexity",
    "ANSWERS which modules are god packages: too many functions, too much\n"
    "     complexity, too much coupling for one package.\n"
    "ACT split the package along responsibility lines. The total_cyclo and\n"
    "     n_functions columns quantify the size.\n"
    "MISLEADS a large package may be a framework entrypoint that is intentionally\n"
    "     broad. The instability column (fan_in/(fan_in+fan_out)) tells whether\n"
    "     it is a leaf or a root.",
    """SELECT m.name, m.n_files, m.n_symbols, m.n_public,
        m.sloc, m.fan_in, m.fan_out, m.instability,
        (SELECT SUM(s.cyclomatic) FROM symbols s WHERE s.module_id=m.id
         AND s.kind IN ('function','method')) AS total_cyclo,
        (SELECT COUNT(*) FROM symbols s WHERE s.module_id=m.id
         AND s.kind IN ('function','method')) AS n_functions
    FROM modules m
    WHERE m.n_symbols > 50 AND m.name LIKE :mod
    ORDER BY total_cyclo DESC LIMIT :lim"""),
(
    "deep-call-chain",
    "Functions at the end of a very deep call chain (maintainability)",
    "ANSWERS which functions are reachable only through a long call chain\n"
    "     (depth > 6), making them hard to test in isolation and hard to debug.\n"
    "ACT flatten the call chain or provide a direct entrypoint for testing.\n"
    "MISLEADS depth is from any root (handler or entrypoint), capped at 8.\n"
    "     A function that is deep from one root but shallow from another shows\n"
    "     the minimum.",
    """WITH RECURSIVE walk(root, sym, depth) AS (
        SELECT s.id, s.id, 0 FROM symbols s
        WHERE s.is_handler=1 OR s.is_entrypoint=1
        UNION
        SELECT w.root, e.callee_id, w.depth+1
        FROM walk w JOIN edges e ON e.caller_id=w.sym
        WHERE w.depth < 8 AND e.is_self=0)
    SELECT s.name, MIN(r.min_depth) AS min_depth,
        COUNT(DISTINCT r.root) AS n_entrypoints,
        s.fan_in, s.cyclomatic AS cyclo, s.sloc,
        f.path || ':' || s.line_start AS at
    FROM (SELECT root, sym, MIN(depth) AS min_depth
          FROM walk GROUP BY root, sym) r
    JOIN symbols s ON s.id=r.sym
    JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE f.is_test=0 AND COALESCE(m.name,'') LIKE :mod
    GROUP BY s.id
    HAVING min_depth > 6
    ORDER BY min_depth DESC, s.fan_in DESC LIMIT :lim"""),
(
    "too-many-return-paths",
    "Functions with an excessive number of return paths (maintainability)",
    "ANSWERS where a function has more than 10 return statements, making it\n"
    "     hard to verify all paths are covered and resources are cleaned up.\n"
    "ACT consolidate early returns or use a result struct; ensure defers cover\n"
    "     every path.\n"
    "MISLEADS a dispatch function with one return per case is correct. The\n"
    "     n_early_returns column distinguishes guard clauses from scattered\n"
    "     returns.",
    """SELECT s.name, s.n_returns AS returns,
        s.n_early_returns AS early_returns,
        s.n_defer_close AS defers, s.n_recover AS recovers,
        s.cyclomatic AS cyclo, s.sloc, s.fan_in,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_returns > 10 AND s.kind IN ('function','method')
      AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.n_returns DESC, s.cyclomatic DESC LIMIT :lim"""),
(
    "unused-params",
    "Parameters that are never read in the function body (unparam)",
    "ANSWERS where a function has parameters that are likely unused, based on\n"
    "     the ratio of member accesses and subscripts to the parameter count.\n"
    "     An unused parameter is a maintenance burden and a signal that the\n"
    "     interface is wider than needed.\n"
    "ACT remove the parameter if no caller passes a meaningful value, or rename\n"
    "     to _ to signal intentional unused.\n"
    "MISLEADS a parameter used only in a branch the graph cannot see (a rare\n"
    "     error path) will appear unused. This is a heuristic, not a proof.",
    """SELECT s.name, s.n_params, s.n_optional_params,
        s.n_member_access AS member_access, s.n_subscript AS subscripts,
        s.n_calls, s.sloc, s.fan_in,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_params > 3 AND s.n_member_access + s.n_subscript < s.n_params
      AND s.kind IN ('function','method') AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.n_params DESC, s.fan_in DESC LIMIT :lim"""),
# ---------------------------------------------------------------------------
# Concurrency / cleanup / hygiene metrics (concurrency-lifecycle pack).
# ---------------------------------------------------------------------------
(
    "goroutine-fanout-density",
    "Goroutine pressure per package: spawns, in-loop share, per-ksloc density",
    "ANSWERS which packages put the most goroutine pressure on the runtime: raw\n"
    "     spawn counts, the share spawned per-loop-iteration, and spawns per\n"
    "     thousand SLOC so small hot packages are not hidden by big calm ones.\n"
    "ACT point goleak tests and lifetime review at the top packages first;\n"
    "     every in-loop spawn should have a limiter next to it.\n"
    "MISLEADS a few legitimate long-lived worker pools dominate raw counts;\n"
    "     density punishes small high-concurrency packages; test-driven spawn\n"
    "     counts are excluded here but often dominate real repos.",
    """SELECT m.name AS package_, m.sloc,
        COALESCE(SUM(s.n_goroutines),0) AS spawns,
        COALESCE(SUM(s.n_go_in_loop),0) AS in_loop_spawns,
        ROUND(100.0*COALESCE(SUM(s.n_go_in_loop),0)
              / NULLIF(SUM(s.n_goroutines),0), 1) AS pct_in_loop,
        ROUND(COALESCE(SUM(s.n_goroutines),0)*1000.0/NULLIF(m.sloc,0), 2)
            AS per_ksloc,
        COALESCE(SUM(s.n_semaphore),0) AS limiter_sites,
        COALESCE(SUM(s.is_handler * s.n_goroutines),0) AS under_handlers
    FROM modules m
    JOIN files f ON f.module_id=m.id AND f.is_test=0 AND f.is_generated=0
    JOIN symbols s ON s.file_id=f.id AND s.kind IN ('function','method')
    WHERE m.name LIKE :mod
    GROUP BY m.id
    HAVING spawns>0
    ORDER BY per_ksloc DESC LIMIT :lim"""),
(
    "cleanup-coverage",
    "Functions with real exits and I/O but not a single defer: the cleanup-deficit list",
    "ANSWERS functions doing I/O, SQL or network work with error checks and\n"
    "     return paths but zero defers: every error path leaks whatever the\n"
    "     success path closes by hand.\n"
    "ACT review the top offenders for a missing `defer x.Close()`; set a house\n"
    "     rule that any function opening a resource defers its Close.\n"
    "MISLEADS explicit Close before each return is a correct alternative this\n"
    "     counts as a deficit; n_defer includes deferred log/print that cleans\n"
    "     nothing (excluded here only by being zero); pure functions dilute\n"
    "     nothing because the WHERE already filters to I/O doers.",
    """SELECT s.name, s.n_err_checks AS err_checks, s.n_returns,
        s.n_io + s.n_sql + s.n_net AS io_sites, s.fan_in,
        ROUND(1.0 * s.n_defer / NULLIF(s.n_err_checks + s.n_returns, 0), 2)
            AS cleanup_ratio,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE f.is_test=0 AND f.is_generated=0
      AND s.kind IN ('function','method')
      AND s.n_defer=0 AND (s.n_io + s.n_sql + s.n_net)>0
      AND s.n_err_checks + s.n_returns >= 3
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY io_sites * s.fan_in DESC LIMIT :lim"""),
(
    "open-close-ratio",
    "Close actions vs open sites per package: who owns the descriptors",
    "ANSWERS the module-grain balance between resources opened (io+sql+net\n"
    "     sites) and closes performed (direct Close calls plus close-defers):\n"
    "     below ~0.8 the package is exporting cleanup work to its callers.\n"
    "ACT audit ownership in the worst packages: either the opener defers the\n"
    "     Close, or the return type says who must.\n"
    "MISLEADS read-only opens (os.ReadFile) self-close and inflate the\n"
    "     deficit; opens and closes via wrapper helpers count on different\n"
    "     rows; the ratio says nothing about WHICH paths close, only how\n"
    "     many.",
    """SELECT m.name AS package_,
        COALESCE(SUM(s.n_io + s.n_sql + s.n_net),0) AS open_sites,
        COALESCE(SUM(s.n_close_call),0)
            + (SELECT COUNT(*) FROM defers d
               JOIN symbols ds ON ds.id=d.symbol_id
               JOIN files df ON df.id=ds.file_id
               WHERE df.module_id=m.id AND d.is_close=1) AS close_actions,
        ROUND(1.0*COALESCE(SUM(s.n_close_call),0)
              / NULLIF(SUM(s.n_io + s.n_sql + s.n_net),0), 2) AS ratio
    FROM modules m
    JOIN files f ON f.module_id=m.id AND f.is_test=0 AND f.is_generated=0
    JOIN symbols s ON s.file_id=f.id AND s.kind IN ('function','method')
    WHERE m.name LIKE :mod
    GROUP BY m.id
    HAVING open_sites>5
    ORDER BY open_sites DESC, ratio ASC LIMIT :lim"""),
(
    "lock-balance",
    "Packages that Lock more than they Unlock, defers included",
    "ANSWERS module-grain lock hygiene: Lock/RLock calls vs Unlock/RUnlock\n"
    "     calls, how many of the unlocks are defers, and the deficit rows\n"
    "     that lock strictly more than they release. The function-grain view\n"
    "     is lock-release-imbalance-reachable; this is the screening view.\n"
    "ACT a deficit package gets a defer-unlock sweep: every Lock is followed\n"
    "     by `defer mu.Unlock()` or an explicit release on every path.\n"
    "MISLEADS TryLock failure paths, RWMutex mixing and channels-as-locks are\n"
    "     invisible; a balanced package can still deadlock via nested locking\n"
    "     (double-lock-same-receiver-path); deferred unlocks are counted\n"
    "     inside the unlock total, not added twice.",
    """SELECT m.name AS package_,
        COALESCE(SUM(s.n_lock_call),0) AS locks,
        COALESCE(SUM(s.n_unlock_call),0) AS unlocks,
        (SELECT COUNT(*) FROM defers d
         JOIN symbols ds ON ds.id=d.symbol_id
         JOIN files df ON df.id=ds.file_id
         WHERE df.module_id=m.id AND d.is_unlock=1) AS unlock_defers,
        COALESCE(SUM(s.n_lock_call),0) - COALESCE(SUM(s.n_unlock_call),0)
            AS deficit
    FROM modules m
    JOIN files f ON f.module_id=m.id AND f.is_test=0 AND f.is_generated=0
    JOIN symbols s ON s.file_id=f.id AND s.kind IN ('function','method')
    WHERE m.name LIKE :mod
    GROUP BY m.id
    HAVING locks > unlocks
    ORDER BY deficit DESC LIMIT :lim"""),
(
    "channel-balance",
    "Send/receive/close counts per package, and the unbuffered share",
    "ANSWERS the module-grain channel texture: how much sending and receiving\n"
    "    happens, how often channels get closed, and what share of channel\n"
    "    types are unbuffered -- the screening view for the cross-function\n"
    "    channel pairing queries.\n"
    "ACT packages with heavy sends and few closes feed channel-never-closed\n"
    "    review; mandate `make(chan T, 1)` over bare unbuffered where a\n"
    "    capacity of one is the intent (Uber: Channel Size is One or None).\n"
    "MISLEADS select statements count as both send and receive sites; buffered\n"
    "    channels absorb imbalance by design; real producer/consumer pairing\n"
    "    crosses packages, so the module grain can only screen, not prove.",
    """SELECT m.name AS package_,
        COALESCE(SUM(s.n_chan_send),0) AS sends,
        COALESCE(SUM(s.n_chan_recv),0) AS recvs,
        COALESCE(SUM(s.n_chan_close),0) AS closes,
        COALESCE(SUM(s.n_chan_unbuffered),0) AS unbuf,
        ROUND(100.0*COALESCE(SUM(s.n_chan_unbuffered),0)
              / NULLIF(SUM(s.n_chan_type),0), 1) AS pct_unbuf
    FROM modules m
    JOIN files f ON f.module_id=m.id AND f.is_test=0 AND f.is_generated=0
    JOIN symbols s ON s.file_id=f.id AND s.kind IN ('function','method')
    WHERE m.name LIKE :mod
    GROUP BY m.id
    HAVING sends>0
    ORDER BY sends DESC, unbuf DESC LIMIT :lim"""),
(
    "test-only-fanin",
    "Exported functions whose only callers are _test.go files: production-dead but alive-looking",
    "ANSWERS exported functions with callers where every edge comes from a test\n"
    "    file: no production code path reaches them, but per-file lint and\n"
    "    dead-code reads both keep them alive.\n"
    "ACT delete or unexport; or move the test to exercise the real production\n"
    "    entry path instead of the helper directly.\n"
    "MISLEADS public library APIs are legitimately caller-less in their own\n"
    "    repo (external importers are invisible); entry points and examples\n"
    "    are exempt by is_entrypoint/is_public semantics only partially;\n"
    "    reflection- and registration-based dispatch has no edges at all.",
    """SELECT s.name, s.qual_name, s.sloc, s.fan_in,
        (SELECT COUNT(*) FROM edges e JOIN symbols c ON c.id=e.caller_id
           JOIN files cf ON cf.id=c.file_id
          WHERE e.callee_id=s.id AND cf.is_test=0) AS prod_callers,
        (SELECT COUNT(*) FROM edges e JOIN symbols c ON c.id=e.caller_id
           JOIN files cf ON cf.id=c.file_id
          WHERE e.callee_id=s.id AND cf.is_test=1) AS test_callers,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE f.is_test=0 AND f.is_generated=0
      AND s.is_public=1 AND s.kind IN ('function','method')
      AND s.fan_in>0
      AND NOT EXISTS (SELECT 1 FROM edges e
                        JOIN symbols c ON c.id=e.caller_id
                        JOIN files cf ON cf.id=c.file_id
                       WHERE e.callee_id=s.id AND cf.is_test=0)
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.sloc DESC LIMIT :lim"""),
(
    "wrap-ratio",
    "%w-wrapping share per package, weighted by importers (errorlint / wrapcheck)",
    "ANSWERS the module-grain error-wrapping hygiene: %w-wrapped constructions\n"
    "    vs verbatim fmt.Errorf sites, ranked with the package's import\n"
    "    fan-in, because a module that never wraps breaks errors.Is and\n"
    "    errors.As FOR EVERY caller of that module.\n"
    "ACT mandate %w in the worst packages first; migrate opportunistically\n"
    "    upward from the lowest ratio.\n"
    "MISLEADS deliberate %v at trust boundaries (hiding internals from API\n"
    "    consumers) is correct and counted against you; custom error types\n"
    "    wrap without Errorf and are invisible; raw counts matter less than\n"
    "    the ratio, so a one-function lapse does not sink a package.",
    """SELECT m.name AS package_, m.fan_in AS importers,
        COALESCE(SUM(s.n_err_wrapped),0) AS wrapped,
        COALESCE(SUM(s.n_errorf_no_wrap),0) AS unwrapped,
        ROUND(100.0*COALESCE(SUM(s.n_err_wrapped),0)
              / NULLIF(COALESCE(SUM(s.n_err_wrapped),0)
                       + COALESCE(SUM(s.n_errorf_no_wrap),0), 0), 1)
            AS pct_wrapped
    FROM modules m
    JOIN files f ON f.module_id=m.id AND f.is_test=0 AND f.is_generated=0
    JOIN symbols s ON s.file_id=f.id AND s.kind IN ('function','method')
    WHERE m.name LIKE :mod
    GROUP BY m.id
    HAVING wrapped + unwrapped > 0
    ORDER BY importers DESC, pct_wrapped ASC LIMIT :lim"""),
(
    "wide-interface",
    "Interfaces with the most methods (interfacebloat): every implementer signs the whole contract",
    "ANSWERS interfaces declaring many methods, with how often they appear as a\n"
    "    parameter type: a fat interface forces mocks to implement methods\n"
    "    their tests never call and makes the next implementation a chore.\n"
    "ACT split along the calls actually made at each site (consumer-side\n"
    "    interfaces, one or two methods).\n"
    "MISLEADS a broad interface backed by one canonical implementation is\n"
    "    sometimes the honest shape (database/sql.DB-like handles); used_as_\n"
    "    param matches the interface name as a parameter-type suffix, so a\n"
    "    same-named unrelated type rides along; embedded interfaces inflate\n"
    "    the method count without new surface.",
    """WITH use AS (
        SELECT substr(type,
                length(rtrim(type, 'abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_')) + 1)
            AS tail_ident, COUNT(*) AS n
        FROM params GROUP BY tail_ident)
    SELECT s.name AS iface, i.n_methods AS methods, i.n_embedded AS embedded,
        COALESCE(u.n,0) AS used_as_param,
        (SELECT COUNT(*) FROM implements im
         WHERE im.interface_id=s.id AND im.in_test=0) AS impls,
        f.path || ':' || s.line_start AS at
    FROM interfaces i
    JOIN symbols s ON s.id=i.symbol_id
    JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    LEFT JOIN use u ON u.tail_ident = s.name
    WHERE i.is_constraint=0 AND i.n_methods>=4
      AND f.is_test=0 AND f.is_generated=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY methods DESC, used_as_param DESC LIMIT :lim""")
]

ANALYZER = GoAnalyzer()


if __name__ == "__main__":
    try:
        sys.exit(main(ANALYZER))
    except KeyboardInterrupt:
        print("\ninterrupted", file=sys.stderr)
        sys.exit(130)
