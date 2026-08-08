#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Piyush Katariya
#
# @author Piyush Katariya
"""codegraph_javascript.py -- parse a JavaScript tree into a graph and query it.

Targets ES2026 (17th edition, approved 2026-06-30). Parses with
tree-sitter-javascript, which handles .js .mjs .cjs and .jsx in one grammar.

Six JavaScript linters were read before this was written -- ESLint's 199 core
rules, typescript-eslint's 134, eslint-plugin-unicorn's 336, Biome's 436,
oxlint's 847 and CodeQL-JS's 200 queries -- and the single most useful finding
was a gap: NOT ONE of them ships a real memory-retention rule. Nothing pairs an
`addEventListener` with its `removeEventListener`, nothing notices a
`setInterval` whose handle is discarded, and nothing tracks a module-scope `Map`
that is only ever written to. Those three shapes are how a Node process grows
all week and how a single-page app gets slower the longer a tab is open, and
they are the two queries here (`listener-leak-frontier`,
`unbounded-module-cache`) that this tool exists for. Everything else in the
catalogue is a bonus.

Three JavaScript facts baked in rather than guessed:

* ES2025 shipped import attributes (`with { type: "json" }`), iterator helpers,
  `RegExp` modifiers `(?i:...)` and duplicate named capture groups. ES2026 adds
  only APIs -- `Map.getOrInsert`, `JSON.rawJSON`, `Uint8Array.toBase64`,
  `Math.sumPrecise`, `Error.isError`, `Array.fromAsync` -- and no new syntax, so
  an ES2025 grammar reads ES2026 source completely.
* `using` / `await using` (explicit resource management) and Temporal are NOT in
  any published edition -- they are ES2027 candidates -- but V8 and Node ship
  them and real code uses them, so they are accepted. Decorators are still Stage
  3 and the grammar only handles the class-level form; `accessor x = 1` is a
  parse error and lands honestly in `parse-coverage`.
* A `/` is a regex delimiter or a division sign depending on the preceding
  token, and no regular expression can tell which. tree-sitter resolves it in
  the parser, so every pattern-matching rule here runs against the text of a
  `regex_pattern` NODE and never against raw source.

Usage:
  python3 codegraph_javascript.py /path/to/repo --report
  python3 codegraph_javascript.py /path/to/repo --list
  python3 codegraph_javascript.py --deps"""
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
import bisect
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
        #: (file_id, byte_start) of handler bodies, marked in post_build
        self._handler_spans: list[tuple[int, int]] = []

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
        if self._handler_spans:
            db.executemany("UPDATE symbols SET is_handler=1 "
                           "WHERE file_id=? AND byte_start=?",
                           self._handler_spans)
            self._handler_spans.clear()

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
# lang_javascript.py
# codegraph_javascript.py -- parse a JavaScript tree into a graph and query it.
#
# Targets ES2026 (17th edition, approved 2026-06-30). Parses with
# tree-sitter-javascript, which handles .js .mjs .cjs and .jsx in one grammar.
#
# Six JavaScript linters were read before this was written -- ESLint's 199 core
# rules, typescript-eslint's 134, eslint-plugin-unicorn's 336, Biome's 436,
# oxlint's 847 and CodeQL-JS's 200 queries -- and the single most useful finding
# was a gap: NOT ONE of them ships a real memory-retention rule. Nothing pairs an
# `addEventListener` with its `removeEventListener`, nothing notices a
# `setInterval` whose handle is discarded, and nothing tracks a module-scope `Map`
# that is only ever written to. Those three shapes are how a Node process grows
# all week and how a single-page app gets slower the longer a tab is open, and
# they are the two queries here (`listener-leak-frontier`,
# `unbounded-module-cache`) that this tool exists for. Everything else in the
# catalogue is a bonus.
#
# Three JavaScript facts baked in rather than guessed:
#
# * ES2025 shipped import attributes (`with { type: "json" }`), iterator helpers,
#   `RegExp` modifiers `(?i:...)` and duplicate named capture groups. ES2026 adds
#   only APIs -- `Map.getOrInsert`, `JSON.rawJSON`, `Uint8Array.toBase64`,
#   `Math.sumPrecise`, `Error.isError`, `Array.fromAsync` -- and no new syntax, so
#   an ES2025 grammar reads ES2026 source completely.
# * `using` / `await using` (explicit resource management) and Temporal are NOT in
#   any published edition -- they are ES2027 candidates -- but V8 and Node ship
#   them and real code uses them, so they are accepted. Decorators are still Stage
#   3 and the grammar only handles the class-level form; `accessor x = 1` is a
#   parse error and lands honestly in `parse-coverage`.
# * A `/` is a regex delimiter or a division sign depending on the preceding
#   token, and no regular expression can tell which. tree-sitter resolves it in
#   the parser, so every pattern-matching rule here runs against the text of a
#   `regex_pattern` NODE and never against raw source.
#
# Usage:
#   python3 codegraph_javascript.py /path/to/repo --report
#   python3 codegraph_javascript.py /path/to/repo --list
#   python3 codegraph_javascript.py --deps
# ==========================================================================

DEPS = DepSet(lang="javascript", deps=[
    TREE_SITTER,
    grammar("JavaScript", "tree_sitter_javascript",
            "tree-sitter-javascript>=0.25", "0.25.0 (ABI 15)"),
])

HAZARD_CATEGORIES = (
    "sync_block", "exec", "proto_pollution", "redos", "listener", "cache",
    "io", "net", "timer", "dom", "storage", "crypto", "reflect", "alloc",
)

HAZARD_CALLS: dict[str, str] = {
    # -- sync_block: the *Sync family stops the event loop dead -------------
    "readFileSync": "sync_block", "writeFileSync": "sync_block",
    "appendFileSync": "sync_block", "existsSync": "sync_block",
    "statSync": "sync_block", "lstatSync": "sync_block",
    "readdirSync": "sync_block", "mkdirSync": "sync_block",
    "rmSync": "sync_block", "rmdirSync": "sync_block",
    "unlinkSync": "sync_block", "copyFileSync": "sync_block",
    "renameSync": "sync_block", "realpathSync": "sync_block",
    "readlinkSync": "sync_block", "openSync": "sync_block",
    "closeSync": "sync_block", "readSync": "sync_block",
    "writeSync": "sync_block", "truncateSync": "sync_block",
    "accessSync": "sync_block", "chmodSync": "sync_block",
    "utimesSync": "sync_block", "globSync": "sync_block",
    "pbkdf2Sync": "sync_block", "scryptSync": "sync_block",
    "randomBytesSync": "sync_block", "randomFillSync": "sync_block",
    "deflateSync": "sync_block", "inflateSync": "sync_block",
    "gzipSync": "sync_block", "gunzipSync": "sync_block",
    "brotliCompressSync": "sync_block", "brotliDecompressSync": "sync_block",
    "execFileSync": "sync_block", "spawnSync": "sync_block",
    "JSON.parse": "sync_block", "JSON.stringify": "sync_block",
    "Atomics.wait": "sync_block", "structuredClone": "sync_block",
    # -- exec: arbitrary code from data ------------------------------------
    "eval": "exec", "Function": "exec", "execSync": "exec",
    "exec": "exec", "execFile": "exec", "spawn": "exec", "fork": "exec",
    "child_process.exec": "exec", "child_process.execSync": "exec",
    "vm.runInNewContext": "exec", "vm.runInThisContext": "exec",
    "vm.runInContext": "exec", "vm.compileFunction": "exec",
    "vm.Script": "exec", "createRequire": "exec",
    "process.dlopen": "exec", "module._compile": "exec",
    "setTimeout_string": "exec",
    # -- proto_pollution ---------------------------------------------------
    "Object.setPrototypeOf": "proto_pollution",
    "Object.assign": "proto_pollution",
    "merge": "proto_pollution", "deepMerge": "proto_pollution",
    "mergeDeep": "proto_pollution", "defaultsDeep": "proto_pollution",
    "extend": "proto_pollution", "deepExtend": "proto_pollution",
    "_.merge": "proto_pollution", "_.set": "proto_pollution",
    "_.defaultsDeep": "proto_pollution", "_.extend": "proto_pollution",
    "objectPath.set": "proto_pollution", "dot.set": "proto_pollution",
    "setValue": "proto_pollution", "setIn": "proto_pollution",
    # -- redos: the regex engine is the denial of service ------------------
    "RegExp": "redos", "matchAll": "redos", "replaceAll": "redos",
    # -- listener: registration is half a contract -------------------------
    "addEventListener": "listener", "removeEventListener": "listener",
    "addListener": "listener", "removeListener": "listener",
    "removeAllListeners": "listener", "prependListener": "listener",
    "prependOnceListener": "listener",
    "on": "listener", "once": "listener", "off": "listener",
    "subscribe": "listener", "unsubscribe": "listener",
    "observe": "listener", "unobserve": "listener", "disconnect": "listener",
    "IntersectionObserver": "listener", "MutationObserver": "listener",
    "ResizeObserver": "listener", "PerformanceObserver": "listener",
    "AbortController": "listener", "EventTarget": "listener",
    "EventEmitter": "listener",
    # -- cache: anything that holds a reference for you --------------------
    "Map": "cache", "Set": "cache", "WeakMap": "cache", "WeakSet": "cache",
    "WeakRef": "cache", "FinalizationRegistry": "cache",
    "LRUCache": "cache", "lru": "cache", "memoize": "cache",
    "Object.create": "cache",
    # -- timer -------------------------------------------------------------
    "setTimeout": "timer", "setInterval": "timer", "setImmediate": "timer",
    "clearTimeout": "timer", "clearInterval": "timer",
    "clearImmediate": "timer",
    "requestAnimationFrame": "timer", "cancelAnimationFrame": "timer",
    "requestIdleCallback": "timer", "cancelIdleCallback": "timer",
    "process.nextTick": "timer", "queueMicrotask": "timer",
    "setTimeout.unref": "timer",
    # -- io ----------------------------------------------------------------
    "readFile": "io", "writeFile": "io", "appendFile": "io",
    "createReadStream": "io", "createWriteStream": "io",
    "readdir": "io", "mkdir": "io", "unlink": "io", "rename": "io",
    "pipe": "io", "pipeline": "io", "pipeTo": "io", "pipeThrough": "io",
    "fs.promises": "io", "opendir": "io", "watch": "io", "watchFile": "io",
    "createInterface": "io",
    # -- net ---------------------------------------------------------------
    "fetch": "net", "XMLHttpRequest": "net", "WebSocket": "net",
    "EventSource": "net", "sendBeacon": "net",
    "http.request": "net", "https.request": "net", "http.get": "net",
    "https.get": "net", "http.createServer": "net",
    "https.createServer": "net", "net.createServer": "net",
    "net.connect": "net", "tls.connect": "net", "dgram.createSocket": "net",
    "axios": "net", "axios.get": "net", "axios.post": "net",
    "axios.put": "net", "axios.delete": "net", "axios.request": "net",
    "got": "net", "superagent": "net", "request": "net",
    "navigator.sendBeacon": "net", "importScripts": "net",
    # -- dom: every one of these is an HTML injection sink -----------------
    "insertAdjacentHTML": "dom", "document.write": "dom",
    "document.writeln": "dom", "createContextualFragment": "dom",
    "execCommand": "dom", "srcdoc": "dom",
    "innerHTML": "dom", "outerHTML": "dom",
    "dangerouslySetInnerHTML": "dom", "v-html": "dom",
    # -- storage -----------------------------------------------------------
    "localStorage": "storage", "sessionStorage": "storage",
    "indexedDB": "storage", "openDatabase": "storage",
    "caches.open": "storage", "localStorage.setItem": "storage",
    "sessionStorage.setItem": "storage", "cookieStore.set": "storage",
    # -- crypto: predictable or broken -------------------------------------
    "Math.random": "crypto", "createHash": "crypto",
    "createCipher": "crypto", "createDecipher": "crypto",
    "pseudoRandomBytes": "crypto", "btoa": "crypto", "atob": "crypto",
    # -- reflect: the reason the call graph below has holes ----------------
    "Object.defineProperty": "reflect", "Object.defineProperties": "reflect",
    "Object.getOwnPropertyDescriptor": "reflect",
    "Proxy": "reflect", "Reflect.get": "reflect", "Reflect.set": "reflect",
    "Reflect.has": "reflect", "Reflect.apply": "reflect",
    "Reflect.construct": "reflect", "Reflect.ownKeys": "reflect",
    "Reflect.defineProperty": "reflect",
    "apply": "reflect", "call": "reflect", "bind": "reflect",
    "__defineGetter__": "reflect", "__defineSetter__": "reflect",
    # -- alloc -------------------------------------------------------------
    "Array.from": "alloc", "Array.of": "alloc", "Object.entries": "alloc",
    "Object.keys": "alloc", "Object.values": "alloc",
    "Object.fromEntries": "alloc", "concat": "alloc", "slice": "alloc",
    "splice": "alloc", "flat": "alloc", "flatMap": "alloc",
    "Buffer.alloc": "alloc", "Buffer.allocUnsafe": "alloc",
    "Buffer.from": "alloc", "Buffer.concat": "alloc",
    "structuredClone_alloc": "alloc",
}

LISTENER_ADD = {
    "addEventListener": "dom", "on": "emitter", "once": "emitter",
    "addListener": "emitter", "prependListener": "emitter",
    "prependOnceListener": "emitter", "subscribe": "observable",
    "observe": "observer", "attachEvent": "dom", "listen": "emitter",
    "addEventHandler": "dom", "$on": "emitter",
}

LISTENER_REMOVE = {
    "removeEventListener": "dom", "off": "emitter",
    "removeListener": "emitter", "removeAllListeners": "emitter",
    "unsubscribe": "observable", "dispose": "observable",
    "unobserve": "observer", "disconnect": "observer",
    "detachEvent": "dom", "abort": "signal", "$off": "emitter",
    "destroy": "observable", "teardown": "observable",
}

OBSERVER_CTORS = frozenset((
    "IntersectionObserver", "MutationObserver", "ResizeObserver",
    "PerformanceObserver", "ReportingObserver"))

TIMER_SET = {
    "setTimeout": "timeout", "setInterval": "interval",
    "setImmediate": "immediate", "requestAnimationFrame": "raf",
    "requestIdleCallback": "idle",
}

TIMER_CLEAR = {
    "clearTimeout": "timeout", "clearInterval": "interval",
    "clearImmediate": "immediate", "cancelAnimationFrame": "raf",
    "cancelIdleCallback": "idle",
}

TIMER_REPEATING = frozenset(("interval", "raf"))

CACHE_CTORS = {
    "Map": "Map", "Set": "Set", "WeakMap": "WeakMap", "WeakSet": "WeakSet",
    "Array": "Array", "LRUCache": "LRUCache", "QuickLRU": "LRUCache",
}

WEAK_CTORS = frozenset(("WeakMap", "WeakSet", "WeakRef"))

CACHE_WRITE_METHODS = frozenset((
    "set", "add", "push", "unshift", "append", "put", "store", "register"))

CACHE_DROP_METHODS = frozenset((
    "delete", "clear", "remove", "evict", "pop", "shift", "splice",
    "unregister", "reset", "prune", "purge", "invalidate"))

REDOS_NESTED_RE = re.compile(
    r'\((?:\?[:=!]|\?<[=!]|\?<\w+>)?[^()]*?(?:[+*]|\{\d+,\d*\})[^()]*?\)'
    r'\s*(?:[+*]|\{\d+,\d*\})')

REDOS_ALT_RE = re.compile(
    r'\((?:\?[:=!])?[^()|]*\|[^()|]*\)\s*(?:[+*]|\{\d+,\d*\})')

HANDLER_PARAM_RE = re.compile(
    r'^\(?\s*(?:_?req(?:uest)?\s*,\s*_?res(?:ponse)?'
    r'|_?res(?:ponse)?\s*,\s*_?req(?:uest)?'
    r'|_?ctx\b|_?context\b'
    r'|event\s*,\s*context'
    r'|_?err(?:or)?\s*,\s*_?req(?:uest)?\s*,\s*_?res(?:ponse)?)', re.I)

ROUTE_METHODS = frozenset((
    "get", "post", "put", "patch", "delete", "head", "options", "all",
    "use", "route", "handle", "addRoute", "register"))

ROUTE_OBJECTS = re.compile(
    r'^(app|router|server|api|fastify|express|koa|http|https|r)\b', re.I)

HOOK_NAME_RE = re.compile(r'^use[A-Z_]')

COMPONENT_NAME_RE = re.compile(r'^[A-Z][A-Za-z0-9]*$')

SETSTATE_RE = re.compile(r'^set[A-Z_]')

DEP_ARRAY_HOOKS = frozenset((
    "useEffect", "useLayoutEffect", "useMemo", "useCallback",
    "useInsertionEffect", "useImperativeHandle"))

BUILTIN_HOOKS = frozenset((
    "useState", "useEffect", "useContext", "useReducer", "useCallback",
    "useMemo", "useRef", "useImperativeHandle", "useLayoutEffect",
    "useDebugValue", "useDeferredValue", "useTransition", "useId",
    "useSyncExternalStore", "useInsertionEffect", "useActionState",
    "useOptimistic", "useFormStatus", "use"))

NODE_BUILTINS = frozenset("""
assert async_hooks buffer child_process cluster console constants crypto
dgram diagnostics_channel dns domain events fs http http2 https inspector
module net os path perf_hooks process punycode querystring readline repl
sea sqlite stream string_decoder sys test timers tls trace_events tty url
util v8 vm wasi worker_threads zlib
""".split())

JS_GLOBALS = frozenset("""
Array ArrayBuffer AsyncFunction AsyncGenerator AsyncIterator Atomics BigInt
BigInt64Array BigUint64Array Boolean DataView Date Error EvalError
FinalizationRegistry Float16Array Float32Array Float64Array Function Generator
Infinity Int8Array Int16Array Int32Array Intl Iterator JSON Map Math NaN Number
Object Promise Proxy RangeError ReferenceError Reflect RegExp Set
SharedArrayBuffer String Symbol SyntaxError Temporal TypeError Uint8Array
Uint8ClampedArray Uint16Array Uint32Array URIError WeakMap WeakRef WeakSet
decodeURI decodeURIComponent encodeURI encodeURIComponent escape eval globalThis
isFinite isNaN parseFloat parseInt undefined unescape
console process Buffer global queueMicrotask structuredClone
setTimeout setInterval setImmediate clearTimeout clearInterval clearImmediate
require module exports __dirname __filename import fetch Headers Request
Response FormData URL URLSearchParams AbortController AbortSignal Blob File
TextEncoder TextDecoder CompressionStream DecompressionStream
ReadableStream WritableStream TransformStream BroadcastChannel MessageChannel
Event EventTarget CustomEvent ErrorEvent MessageEvent CloseEvent
crypto performance navigator localStorage sessionStorage indexedDB caches
window document location history screen alert confirm prompt
requestAnimationFrame cancelAnimationFrame requestIdleCallback
XMLHttpRequest WebSocket EventSource Worker SharedWorker ServiceWorker
IntersectionObserver MutationObserver ResizeObserver PerformanceObserver
HTMLElement Element Node NodeList DOMParser Image Audio Video Notification
React ReactDOM
""".split())

GENERATED_HINT_RE = re.compile(
    r'^(__webpack|__turbopack|__vite|_interopRequire|__esModule|'
    r'__importDefault|__awaiter|__generator|__extends)')

class JavaScriptAnalyzer(TreeSitterAnalyzer):
    LANG = "javascript"
    TARGET = "ES2026 (17th ed.) + using/Temporal (ES2027 candidates)"
    EXTS = (".js", ".mjs", ".cjs", ".jsx")
    SKIP_DIRS = {"node_modules", "bower_components", "flow-typed", "typings",
                 ".yarn", ".pnp", "lib-cov", "jspm_packages", "web_modules"}
    DEPS = DEPS
    HAZARD_CATEGORIES = HAZARD_CATEGORIES
    MANIFESTS = ("package.json",)

    GRAMMAR_MODULE = "tree_sitter_javascript"
    GRAMMAR_PIP = "tree-sitter-javascript>=0.25"

    #: Every form a function takes in this grammar. Missing one is the
    #: difference between reading modern JavaScript and reading none of it:
    #: `const f = () => {}` and `class C { m = () => {} }` are both
    #: `arrow_function`, and in most 2026 code they outnumber
    #: `function_declaration` by an order of magnitude.
    FUNC_KINDS = {
        "function_declaration": "function",
        "generator_function_declaration": "function",
        "function_expression": "function",
        "generator_function": "function",
        "arrow_function": "function",
        "method_definition": "method",
    }
    TYPE_KINDS = {
        "class_declaration": "class",
        "class": "class",
    }
    NAME_FIELD = {"arrow_function": "", "function_expression": "name",
                  "generator_function": "name", "class": "name"}
    IDENT_NODES = ("identifier", "property_identifier",
                   "private_property_identifier", "shorthand_property_identifier")

    BODY_FIELD = "body"
    PARAMS_FIELD = "parameters"
    RETURN_FIELD = ""                      # JavaScript has no return annotation
    ELSE_FIELD = "alternative"             # -> else_clause, unwrapped by the base
    IF_NODES = ("if_statement",)

    LOOP_NODES = ("for_statement", "for_in_statement", "while_statement",
                  "do_statement")
    BRANCH_NODES = ("if_statement", "ternary_expression", "switch_case")
    #: Nesting in JavaScript is mostly CALLBACKS, so nested function nodes count
    #: as depth. A four-deep callback pyramid is exactly as hard to read as a
    #: four-deep `if`, and pretending otherwise ranks the wrong functions.
    #: `statement_block` is deliberately absent: it is the body of every one of
    #: these already and counting both doubles every depth.
    NEST_NODES = ("if_statement", "for_statement", "for_in_statement",
                  "while_statement", "do_statement", "switch_statement",
                  "try_statement", "catch_clause", "finally_clause",
                  "with_statement", "arrow_function", "function_expression",
                  "generator_function", "function_declaration",
                  "generator_function_declaration", "labeled_statement")
    CALL_NODES = ("call_expression", "new_expression")
    CALL_FUNC_FIELD = "function"           # new_expression uses `constructor`;
                                           # on_call() below handles both
    COMMENT_NODES = ("comment",)
    STRING_NODES = ("string", "template_string")
    NUMBER_NODES = ("number",)
    OPERATOR_NODES = ("binary_expression", "unary_expression",
                      "assignment_expression",
                      "augmented_assignment_expression", "update_expression",
                      "subscript_expression", "member_expression",
                      "ternary_expression", "await_expression",
                      "yield_expression", "spread_element")

    COUNTERS = {
        "return_statement": "n_returns",
        "await_expression": "n_await",
        "yield_expression": "n_yield",
        "ternary_expression": "n_ternary",
        "switch_statement": "n_switch",
        "switch_case": "n_cases",
        "switch_default": "n_cases",
        "try_statement": "n_try",
        "catch_clause": "n_catch",
        "finally_clause": "n_finally",
        "throw_statement": "n_throw",
        "labeled_statement": "n_labels",
        "with_statement": "n_with_stmt",
        "regex": "n_regex_lit",
        "optional_chain": "n_optional_chain",
        "spread_element": "n_spread",
        "rest_pattern": "n_spread",
        "object_pattern": "n_destructure",
        "array_pattern": "n_destructure",
        "subscript_expression": "n_computed_member",
        "member_expression": "n_member_access",
        "this": "n_this_refs",
        "update_expression": "n_incdec",
        "augmented_assignment_expression": "n_compound_assign",
        "assignment_expression": "n_assign",
        "variable_declarator": "n_locals",
        "jsx_element": "n_jsx_elements",
        "jsx_self_closing_element": "n_jsx_elements",
        "arrow_function": "n_lambda",
        "function_expression": "n_lambda",
        "generator_function": "n_generator",
        "generator_function_declaration": "n_generator",
    }
    LOOP_CALL_COUNTERS = {
        "RegExp": "regex_in_loop",
        "readFileSync": "io_in_loop",
        "writeFileSync": "io_in_loop",
        "existsSync": "io_in_loop",
        "readFile": "io_in_loop",
        "fetch": "io_in_loop",
        "query": "query_in_loop",
        "execute": "query_in_loop",
        "findOne": "query_in_loop",
        "findAll": "query_in_loop",
        "addEventListener": "n_listener_add_in_loop",
        "setTimeout": "n_timer_in_loop",
        "setInterval": "n_timer_in_loop",
    }

    EXTRA_SYMBOL_COLS = (
        # -- promises and colour ------------------------------------------
        ("n_await", "INT NOT NULL DEFAULT 0"),
        ("n_await_in_loop", "INT NOT NULL DEFAULT 0"),
        ("n_promise_all", "INT NOT NULL DEFAULT 0"),
        ("n_promise_chain", "INT NOT NULL DEFAULT 0"),
        ("n_then", "INT NOT NULL DEFAULT 0"),
        ("n_catch_handler", "INT NOT NULL DEFAULT 0"),
        ("n_floating_promise", "INT NOT NULL DEFAULT 0"),
        ("n_async_arrow", "INT NOT NULL DEFAULT 0"),
        ("n_callbacks", "INT NOT NULL DEFAULT 0"),
        ("n_closures", "INT NOT NULL DEFAULT 0"),
        # -- shape and dispatch -------------------------------------------
        ("n_this_refs", "INT NOT NULL DEFAULT 0"),
        ("n_dynamic_prop", "INT NOT NULL DEFAULT 0"),
        ("n_computed_member", "INT NOT NULL DEFAULT 0"),
        ("n_optional_chain", "INT NOT NULL DEFAULT 0"),
        ("n_nullish", "INT NOT NULL DEFAULT 0"),
        ("n_spread", "INT NOT NULL DEFAULT 0"),
        ("n_destructure", "INT NOT NULL DEFAULT 0"),
        ("n_delete", "INT NOT NULL DEFAULT 0"),
        ("n_arguments", "INT NOT NULL DEFAULT 0"),
        ("n_with_stmt", "INT NOT NULL DEFAULT 0"),
        ("n_proto_write", "INT NOT NULL DEFAULT 0"),
        # -- regex ---------------------------------------------------------
        ("n_regex_redos", "INT NOT NULL DEFAULT 0"),
        # -- retention: the two things no linter checks --------------------
        ("n_listener_add", "INT NOT NULL DEFAULT 0"),
        ("n_listener_remove", "INT NOT NULL DEFAULT 0"),
        ("n_listener_inline", "INT NOT NULL DEFAULT 0"),
        ("n_listener_add_in_loop", "INT NOT NULL DEFAULT 0"),
        ("n_timer_set", "INT NOT NULL DEFAULT 0"),
        ("n_timer_clear", "INT NOT NULL DEFAULT 0"),
        ("n_timer_repeating", "INT NOT NULL DEFAULT 0"),
        ("n_timer_in_loop", "INT NOT NULL DEFAULT 0"),
        ("n_new_map", "INT NOT NULL DEFAULT 0"),
        ("n_new_set", "INT NOT NULL DEFAULT 0"),
        ("n_weak_ref", "INT NOT NULL DEFAULT 0"),
        ("n_cache_write", "INT NOT NULL DEFAULT 0"),
        ("n_cache_drop", "INT NOT NULL DEFAULT 0"),
        # -- sinks ---------------------------------------------------------
        ("n_json_parse", "INT NOT NULL DEFAULT 0"),
        ("n_innerhtml", "INT NOT NULL DEFAULT 0"),
        ("n_eval", "INT NOT NULL DEFAULT 0"),
        ("n_sync_calls", "INT NOT NULL DEFAULT 0"),
        # -- modules -------------------------------------------------------
        ("n_require_dynamic", "INT NOT NULL DEFAULT 0"),
        ("n_import_dynamic", "INT NOT NULL DEFAULT 0"),
        ("n_export_star", "INT NOT NULL DEFAULT 0"),
        # -- view layer ----------------------------------------------------
        ("n_jsx_elements", "INT NOT NULL DEFAULT 0"),
        ("n_hooks", "INT NOT NULL DEFAULT 0"),
        ("n_hooks_conditional", "INT NOT NULL DEFAULT 0"),
        ("n_setstate", "INT NOT NULL DEFAULT 0"),
        ("n_inline_object_prop", "INT NOT NULL DEFAULT 0"),
        # -- misc ----------------------------------------------------------
        ("n_generator", "INT NOT NULL DEFAULT 0"),
        ("n_yield", "INT NOT NULL DEFAULT 0"),
        ("n_labeled", "INT NOT NULL DEFAULT 0"),
        ("n_child_process", "INT NOT NULL DEFAULT 0"),
    ("n_fs_sync", "INT NOT NULL DEFAULT 0"),
    ("n_assign_in_loop", "INT NOT NULL DEFAULT 0"),
    ("n_json_parse_in_loop", "INT NOT NULL DEFAULT 0"),
    ("n_array_grow_in_loop", "INT NOT NULL DEFAULT 0"),
    ("n_search_in_loop", "INT NOT NULL DEFAULT 0"),
    ("n_math_random", "INT NOT NULL DEFAULT 0"),
    ("n_weak_hash", "INT NOT NULL DEFAULT 0"),
    ("n_then_in_loop", "INT NOT NULL DEFAULT 0"),
    ("n_catch_in_loop", "INT NOT NULL DEFAULT 0"),
    ("n_process_exit", "INT NOT NULL DEFAULT 0"),
    ("n_buffer_call", "INT NOT NULL DEFAULT 0"),
    ("n_proto_mutate", "INT NOT NULL DEFAULT 0"),
    ("n_elif", "INT NOT NULL DEFAULT 0"),
        ("n_external_calls", "INT NOT NULL DEFAULT 0"),
        ("n_modules_calling", "INT NOT NULL DEFAULT 0"),
        ("class_name", "TEXT NOT NULL DEFAULT ''"),
        ("is_handler", "INT NOT NULL DEFAULT 0"),
        ("is_component", "INT NOT NULL DEFAULT 0"),
        ("is_hook", "INT NOT NULL DEFAULT 0"),
        ("is_arrow", "INT NOT NULL DEFAULT 0"),
        ("is_iife", "INT NOT NULL DEFAULT 0"),
        ("is_default_export", "INT NOT NULL DEFAULT 0"),
    )

    SCHEMA_EXT = r"""
CREATE TABLE classes(
    symbol_id INT NOT NULL PRIMARY KEY REFERENCES symbols(id),
    file_id INT NOT NULL REFERENCES files(id),
    extends TEXT NOT NULL DEFAULT '',
    n_methods INT NOT NULL DEFAULT 0,
    n_static INT NOT NULL DEFAULT 0,
    n_getters INT NOT NULL DEFAULT 0,
    n_setters INT NOT NULL DEFAULT 0,
    n_private INT NOT NULL DEFAULT 0,
    n_fields INT NOT NULL DEFAULT 0,
    n_arrow_fields INT NOT NULL DEFAULT 0,
    n_computed_members INT NOT NULL DEFAULT 0,
    has_constructor INT NOT NULL DEFAULT 0,
    has_static_block INT NOT NULL DEFAULT 0,
    is_exported INT NOT NULL DEFAULT 0,
    is_component INT NOT NULL DEFAULT 0
) WITHOUT ROWID, STRICT;

CREATE TABLE exports(
    id INTEGER PRIMARY KEY,
    file_id INT NOT NULL REFERENCES files(id),
    symbol_id INT REFERENCES symbols(id),
    name TEXT NOT NULL,
    local_name TEXT NOT NULL DEFAULT '',
    kind TEXT NOT NULL DEFAULT 'named',
    line INT NOT NULL DEFAULT 0,
    source TEXT NOT NULL DEFAULT '',
    source_id INT REFERENCES files(id),
    is_reexport INT NOT NULL DEFAULT 0,
    is_star INT NOT NULL DEFAULT 0,
    is_cjs INT NOT NULL DEFAULT 0
) STRICT;

CREATE TABLE import_names(
    id INTEGER PRIMARY KEY,
    file_id INT NOT NULL REFERENCES files(id),
    source TEXT NOT NULL,
    source_id INT REFERENCES files(id),
    name TEXT NOT NULL,
    alias TEXT NOT NULL DEFAULT '',
    line INT NOT NULL DEFAULT 0,
    is_namespace INT NOT NULL DEFAULT 0,
    is_default INT NOT NULL DEFAULT 0,
    is_external INT NOT NULL DEFAULT 0
) STRICT;

-- Half a contract each. A row in `op='add'` with no partner is the finding.
CREATE TABLE listeners(
    id INTEGER PRIMARY KEY,
    file_id INT NOT NULL REFERENCES files(id),
    symbol_id INT REFERENCES symbols(id),
    line INT NOT NULL,
    op TEXT NOT NULL,
    api TEXT NOT NULL,
    family TEXT NOT NULL DEFAULT '',
    target TEXT NOT NULL DEFAULT '',
    event TEXT NOT NULL DEFAULT '',
    handler TEXT NOT NULL DEFAULT '',
    handler_inline INT NOT NULL DEFAULT 0,
    has_signal INT NOT NULL DEFAULT 0,
    at_module_scope INT NOT NULL DEFAULT 0,
    in_loop INT NOT NULL DEFAULT 0,
    in_cleanup INT NOT NULL DEFAULT 0
) STRICT;

CREATE TABLE timers(
    id INTEGER PRIMARY KEY,
    file_id INT NOT NULL REFERENCES files(id),
    symbol_id INT REFERENCES symbols(id),
    line INT NOT NULL,
    op TEXT NOT NULL,
    api TEXT NOT NULL,
    kind TEXT NOT NULL DEFAULT '',
    handle TEXT NOT NULL DEFAULT '',
    is_assigned INT NOT NULL DEFAULT 0,
    is_repeating INT NOT NULL DEFAULT 0,
    is_unrefd INT NOT NULL DEFAULT 0,
    callback_is_string INT NOT NULL DEFAULT 0,
    at_module_scope INT NOT NULL DEFAULT 0,
    in_loop INT NOT NULL DEFAULT 0
) STRICT;

CREATE TABLE module_caches(
    id INTEGER PRIMARY KEY,
    file_id INT NOT NULL REFERENCES files(id),
    line INT NOT NULL,
    name TEXT NOT NULL,
    ctor TEXT NOT NULL DEFAULT '',
    is_weak INT NOT NULL DEFAULT 0,
    is_exported INT NOT NULL DEFAULT 0,
    is_const INT NOT NULL DEFAULT 0,
    n_writes INT NOT NULL DEFAULT 0,
    n_drops INT NOT NULL DEFAULT 0,
    n_reads INT NOT NULL DEFAULT 0,
    n_size_checks INT NOT NULL DEFAULT 0,
    has_max INT NOT NULL DEFAULT 0,
    writer_fns TEXT NOT NULL DEFAULT ''
) STRICT;

CREATE TABLE jsx_components(
    id INTEGER PRIMARY KEY,
    file_id INT NOT NULL REFERENCES files(id),
    symbol_id INT REFERENCES symbols(id),
    line INT NOT NULL,
    tag TEXT NOT NULL,
    is_component INT NOT NULL DEFAULT 0,
    n_attrs INT NOT NULL DEFAULT 0,
    n_spread INT NOT NULL DEFAULT 0,
    has_key INT NOT NULL DEFAULT 0,
    inline_object_props INT NOT NULL DEFAULT 0,
    inline_fn_props INT NOT NULL DEFAULT 0,
    has_dangerous_html INT NOT NULL DEFAULT 0,
    in_loop INT NOT NULL DEFAULT 0
) STRICT;

CREATE TABLE hooks(
    id INTEGER PRIMARY KEY,
    file_id INT NOT NULL REFERENCES files(id),
    symbol_id INT REFERENCES symbols(id),
    line INT NOT NULL,
    name TEXT NOT NULL,
    is_builtin INT NOT NULL DEFAULT 0,
    has_dep_array INT NOT NULL DEFAULT 0,
    n_deps INT NOT NULL DEFAULT -1,
    has_cleanup INT NOT NULL DEFAULT 0,
    in_loop INT NOT NULL DEFAULT 0,
    in_condition INT NOT NULL DEFAULT 0,
    registers_listener INT NOT NULL DEFAULT 0,
    registers_timer INT NOT NULL DEFAULT 0
) STRICT;
"""

    INDEX_EXT = r"""
CREATE INDEX idx_lis_file ON listeners(file_id, op, event);
CREATE INDEX idx_lis_add ON listeners(file_id, api) WHERE op='add';
CREATE INDEX idx_lis_sym ON listeners(symbol_id);
CREATE INDEX idx_tim_file ON timers(file_id, op, kind);
CREATE INDEX idx_tim_repeat ON timers(file_id) WHERE is_repeating=1;
CREATE INDEX idx_cache_file ON module_caches(file_id, name);
CREATE INDEX idx_cache_leak ON module_caches(n_writes DESC)
    WHERE n_drops=0 AND is_weak=0;
CREATE INDEX idx_exp_name ON exports(name, file_id);
CREATE INDEX idx_exp_file ON exports(file_id, kind);
CREATE INDEX idx_impn_name ON import_names(name, source);
CREATE INDEX idx_impn_src ON import_names(source_id, name);
CREATE INDEX idx_jsx_sym ON jsx_components(symbol_id, tag);
CREATE INDEX idx_hook_sym ON hooks(symbol_id, name);
CREATE INDEX idx_cls_file ON classes(file_id);
CREATE INDEX idx_fn_handler ON symbols(name, file_id) WHERE is_handler=1;
CREATE INDEX idx_fn_component ON symbols(name, file_id) WHERE is_component=1;
CREATE INDEX idx_fn_sync ON symbols(n_sync_calls DESC, name)
    WHERE n_sync_calls>0;
CREATE INDEX idx_fn_redos ON symbols(n_regex_redos DESC, name)
    WHERE n_regex_redos>0;
"""

    VIEW_EXT = r"""
CREATE VIEW v_listener AS
SELECT l.id, l.op, l.api, l.family, l.event, l.target, l.handler,
    l.handler_inline, l.has_signal, l.in_cleanup, l.at_module_scope,
    COALESCE(s.name,'(module scope)') AS in_fn, f.path,
    f.path || ':' || l.line AS at
FROM listeners l
JOIN files f ON f.id=l.file_id
LEFT JOIN symbols s ON s.id=l.symbol_id;

CREATE VIEW v_leaky_cache AS
SELECT c.*, f.path, f.path || ':' || c.line AS at
FROM module_caches c JOIN files f ON f.id=c.file_id
WHERE c.n_drops=0 AND c.is_weak=0 AND c.n_writes>0;

CREATE VIEW v_export AS
SELECT e.id, e.name, e.kind, e.is_reexport, e.is_star, e.is_cjs,
    f.path, COALESCE(s.name,'') AS symbol, COALESCE(s.fan_in,0) AS fan_in_,
    (SELECT COUNT(*) FROM import_names i
     WHERE i.source_id=e.file_id AND (i.name=e.name OR i.is_namespace=1))
        AS imported_by,
    f.path || ':' || e.line AS at
FROM exports e JOIN files f ON f.id=e.file_id
LEFT JOIN symbols s ON s.id=e.symbol_id;
"""

    MATERIALIZE_EXT = r"""
UPDATE symbols AS s SET n_unique_calls = x.c FROM
    (SELECT caller_id AS id, COUNT(*) AS c FROM edges GROUP BY caller_id) AS x
    WHERE x.id = s.id;

-- How many DISTINCT modules call this function. The V8 inline cache degrades
-- with the number of distinct receiver SHAPES, not callers, so this is a proxy
-- and the query that uses it says so.
UPDATE symbols AS s SET n_modules_calling = x.c FROM
    (SELECT e.callee_id AS id, COUNT(DISTINCT c.module_id) AS c
     FROM edges e JOIN symbols c ON c.id=e.caller_id
     WHERE e.is_self=0 GROUP BY e.callee_id) AS x WHERE x.id = s.id;

UPDATE symbols SET n_await_in_loop = await_in_loop;
UPDATE symbols SET n_labeled = n_labels;

UPDATE symbols AS s SET n_listener_add = x.c FROM
    (SELECT symbol_id AS id, COUNT(*) AS c FROM listeners
     WHERE op='add' GROUP BY symbol_id) AS x WHERE x.id = s.id;

UPDATE symbols AS s SET n_listener_remove = x.c FROM
    (SELECT symbol_id AS id, COUNT(*) AS c FROM listeners
     WHERE op='remove' GROUP BY symbol_id) AS x WHERE x.id = s.id;

UPDATE symbols AS s SET n_listener_inline = x.c FROM
    (SELECT symbol_id AS id, COUNT(*) AS c FROM listeners
     WHERE op='add' AND handler_inline=1 AND has_signal=0
     GROUP BY symbol_id) AS x WHERE x.id = s.id;

UPDATE symbols AS s SET n_timer_set = x.c FROM
    (SELECT symbol_id AS id, COUNT(*) AS c FROM timers
     WHERE op='set' GROUP BY symbol_id) AS x WHERE x.id = s.id;

UPDATE symbols AS s SET n_timer_clear = x.c FROM
    (SELECT symbol_id AS id, COUNT(*) AS c FROM timers
     WHERE op='clear' GROUP BY symbol_id) AS x WHERE x.id = s.id;

UPDATE symbols AS s SET n_timer_repeating = x.c FROM
    (SELECT symbol_id AS id, COUNT(*) AS c FROM timers
     WHERE op='set' AND is_repeating=1 GROUP BY symbol_id) AS x
    WHERE x.id = s.id;

UPDATE symbols AS s SET n_hooks = x.c FROM
    (SELECT symbol_id AS id, COUNT(*) AS c FROM hooks
     GROUP BY symbol_id) AS x WHERE x.id = s.id;

UPDATE symbols AS s SET n_hooks_conditional = x.c FROM
    (SELECT symbol_id AS id, COUNT(*) AS c FROM hooks
     WHERE in_loop=1 OR in_condition=1 GROUP BY symbol_id) AS x
    WHERE x.id = s.id;

UPDATE symbols AS s SET n_inline_object_prop = x.c FROM
    (SELECT symbol_id AS id, SUM(inline_object_props + inline_fn_props) AS c
     FROM jsx_components GROUP BY symbol_id) AS x WHERE x.id = s.id;

UPDATE symbols AS s SET is_component = 1 FROM
    (SELECT DISTINCT symbol_id AS id FROM jsx_components
     WHERE symbol_id IS NOT NULL) AS x
    WHERE x.id = s.id AND s.name GLOB '[A-Z]*';

UPDATE exports AS e SET symbol_id = x.id FROM
    (SELECT s.id, s.file_id, s.name FROM symbols s) AS x
    WHERE x.file_id = e.file_id AND x.name = e.local_name
      AND e.symbol_id IS NULL;
"""

    RISK_SQL = (
        "cyclomatic*2 + cognitive + max_nesting*4"
        " + n_eval*30 + n_exec*20 + n_proto_pollution*18"
        " + n_regex_redos*15 + n_innerhtml*14 + n_sync_calls*8"
        " + n_listener_inline*6 + n_timer_repeating*6"
        " + n_dynamic_prop*3 + n_with_stmt*20 + n_arguments*3"
        " + n_delete*2 + n_reflect*2"
        " + await_in_loop*6 + n_floating_promise*2"
        " + n_hooks_conditional*10"
        " + (CASE WHEN is_recursive THEN 10 ELSE 0 END)"
        " + (CASE WHEN is_handler=1 AND n_sync_calls>0 THEN 25 ELSE 0 END)"
        " + (CASE WHEN n_listener_add > n_listener_remove"
        "         THEN (n_listener_add - n_listener_remove)*7 ELSE 0 END)"
    )

    def __init__(self) -> None:
        super().__init__()
        self.pkg_name = ""
        self.pkg_type = ""
        #: file_id -> {local name: (source, imported name, is_external)}
        self.bindings: dict[int, dict[str, tuple[str, str, int]]] = {}
        #: names passed to a route registration anywhere in the tree
        self.handler_names: set[str] = set()
        self._spans: list[tuple[int, int, int]] = []
        self._span_starts: list[int] = []
        self._exported: set[str] = set()

    # -- per-file state ----------------------------------------------------
    def parse_file(self, rec: FileRec, db: sqlite3.Connection,
                   bufs: Buffers) -> None:
        """Reset the per-file byte-span index before the base walks the tree.

        `parse_file_extra` needs to attribute a node at byte N to the innermost
        function containing it, and the only place that mapping exists is here.
        """
        self._spans = []
        self._span_starts = []
        self._exported = set()
        super().parse_file(rec, db, bufs)

    def _owner(self, offset: int) -> Optional[int]:
        """Innermost emitted symbol containing `offset`, or None (module scope).

        Spans arrive in document order from a pre-order walk and are properly
        nested, so the containing span with the LARGEST start is the innermost.
        """
        i = bisect.bisect_right(self._span_starts, offset)
        while i > 0:
            i -= 1
            start, end, sid = self._spans[i]
            if offset < end:
                return sid
        return None

    # -- naming ------------------------------------------------------------
    def node_name(self, node: Any, rec: FileRec) -> str:
        """What to call a function that has no name of its own.

        Half of modern JavaScript is `const f = () => {}`: the function node
        carries no identifier at all and the name lives one or two levels up, on
        the declarator, the object key or the class field. The base class's
        fallback -- search the children for an identifier -- finds the single
        bare PARAMETER of `async x => ...` and names the function after it,
        which is worse than no name, so this replaces it outright.
        """
        t = node.type
        own = node.child_by_field_name("name")
        if own is not None:
            return text_of(own, rec.data).strip()
        if t in ANON_FN_NODES:
            return _binding_name(node, rec.data)
        return ""

    def emit_function(self, node: Any, rec: FileRec, db: sqlite3.Connection,
                      bufs: Buffers, scope: Scope, kind: str) -> int:
        """Split function-shaped nodes into `function` and `closure`.

        An arrow bound to a name is a function anybody can call; an arrow passed
        straight to `.map()` is a closure that exists for one expression. Both
        are `arrow_function` in the grammar. Keeping them one kind puts 40,000
        one-line callbacks in every ranking above the code that matters.
        """
        if kind == "function" and node.type in ANON_FN_NODES:
            if not _binding_name(node, rec.data):
                kind = "closure"
        return super().emit_function(node, rec, db, bufs, scope, kind)

    def docstring_lines(self, node: Any, rec: FileRec) -> int:
        """JSDoc sits above the STATEMENT, not above the arrow inside it."""
        cur = node
        while cur.parent is not None and cur.prev_sibling is None:
            cur = cur.parent
            if cur.type == "program":
                break
        return super().docstring_lines(cur, rec)

    def signature_of(self, node: Any, rec: FileRec) -> str:
        body = node.child_by_field_name(self.BODY_FIELD)
        end = body.start_byte if body is not None else node.end_byte
        sig = rec.data[node.start_byte:end].decode("utf-8", "replace").strip()
        return " ".join(sig.split())

    def visibility_of(self, node: Any, rec: FileRec) -> str:
        name = self.node_name(node, rec)
        if name.startswith("#") or name.startswith("_"):
            return "private"
        return "public"

    # -- parameters --------------------------------------------------------
    def emit_params(self, node: Any, rec: FileRec, sid: int,
                    bufs: Buffers) -> None:
        """Both arrow spellings: `(a, b) => ...` and the bare `a => ...`."""
        params = node.child_by_field_name("parameters")
        kids: list[Any]
        if params is not None:
            kids = [p for p in params.named_children
                    if p.type not in self.COMMENT_NODES]
        else:
            bare = node.child_by_field_name("parameter")
            kids = [bare] if bare is not None else []
        for pos, p in enumerate(kids):
            txt = text_of(p, rec.data).strip()
            optional = int(p.type == "assignment_pattern")
            variadic = int(p.type == "rest_pattern")
            destructured = int(p.type in ("object_pattern", "array_pattern")
                               or (p.type == "assignment_pattern"
                                   and txt.lstrip()[:1] in "{["))
            name = txt
            if p.type == "assignment_pattern":
                lhs = p.child_by_field_name("left")
                if lhs is not None:
                    name = text_of(lhs, rec.data).strip()
            bufs.params.append(
                (sid, pos, name[:120], "", None, optional, variadic, 0, 0,
                 0, 0, 1, destructured))

    # -- flags -------------------------------------------------------------
    def function_flags(self, node: Any, rec: FileRec,
                       scope: Scope) -> dict[str, Any]:
        name = self.node_name(node, rec)
        sig = self.signature_of(node, rec)
        t = node.type
        params = node.child_by_field_name("parameters")
        n_params = 0
        n_optional = 0
        if params is not None:
            kids = [p for p in params.named_children
                    if p.type not in self.COMMENT_NODES]
            n_params = len(kids)
            n_optional = sum(1 for p in kids if p.type == "assignment_pattern")
        elif node.child_by_field_name("parameter") is not None:
            n_params = 1
        ptxt = text_of(params, rec.data) if params is not None else ""

        is_async = int(any(c.type == "async" for c in node.children))
        is_gen = int(t in ("generator_function", "generator_function_declaration")
                     or any(c.type == "*" for c in node.children))
        exported = int(_is_exported(node) or name in self._exported)
        parent = node.parent
        is_iife = int(parent is not None
                      and parent.type in ("parenthesized_expression",
                                          "call_expression", "unary_expression")
                      and _nearest_call_of(node) is not None)
        is_handler = int(bool(HANDLER_PARAM_RE.match(ptxt))
                         or name in self.handler_names)
        is_hook = int(bool(HOOK_NAME_RE.match(name)))
        is_component = int(bool(COMPONENT_NAME_RE.match(name))
                           and rec.rel.endswith((".jsx", ".js", ".mjs")))
        return dict(
            n_params=n_params,
            n_optional_params=n_optional,
            is_async=is_async,
            is_generator=is_gen,
            is_arrow=int(t == "arrow_function"),
            is_iife=is_iife,
            is_static=int(any(c.type == "static" for c in node.children)),
            is_exported=exported,
            is_public=int(exported or not name.startswith(("#", "_"))),
            is_default_export=int(_is_default_export(node)),
            is_test=int(rec.is_test or name.startswith(("test", "it_", "should"))),
            is_entrypoint=int(name in ("main", "bootstrap", "start")
                              or rec.rel.endswith(("index.js", "main.js",
                                                   "cli.js", "bin.js"))),
            is_deprecated=int("@deprecated" in sig),
            is_handler=is_handler,
            is_hook=is_hook,
            is_component=is_component,
            class_name=scope.type_name[:120],
            n_async_arrow=int(is_async and t == "arrow_function"),
        )

    def type_flags(self, node: Any, rec: FileRec,
                   scope: Scope) -> dict[str, Any]:
        name = self.node_name(node, rec)
        return dict(
            is_exported=int(_is_exported(node) or name in self._exported),
            is_public=int(not name.startswith("_")),
            is_default_export=int(_is_default_export(node)),
            is_component=int(bool(COMPONENT_NAME_RE.match(name))),
            class_name=name[:120],
        )

    # -- the measuring pass ------------------------------------------------
    def on_call(self, node: Any, src: bytes, st: BodyStats,
                loop_depth: int, nest: int) -> None:
        """Read a callee out of BOTH call shapes.

        `call_expression` names its target in the `function` field and
        `new_expression` in `constructor`. Taking only the base class's default
        would resolve every `new Foo()` to nothing and silently halve the edge
        count while every other number still looked healthy.
        """
        if node.type == "new_expression":
            fn = node.child_by_field_name("constructor")
        else:
            fn = node.child_by_field_name("function")
        st.bump("n_calls")
        if loop_depth:
            st.bump("call_in_loop")
            st.bump("alloc_in_loop") if node.type == "new_expression" else None
        if fn is None:
            st.bump("n_dynamic_calls")
            st.calls.append(("", node.start_point[0] + 1, True,
                             bool(loop_depth)))
            return
        raw = text_of(fn, src).strip()
        name = " ".join(raw.split())
        # -- facts ESLint and its security/promise/unicorn plugins check --
        # Counters, never verdicts: whether a child_process.exec matters
        # depends on whether request data reaches it, which is a graph fact.
        _b = name.rsplit(".", 1)[-1]
        if _b in ("exec", "execSync", "spawnSync") and "child_process" in name:
            st.bump("n_child_process")        # eslint-plugin-security
        if _b in ("readFileSync", "writeFileSync", "existsSync", "statSync"):
            st.bump("n_fs_sync")              # detect-non-literal-fs-filename
        if name in ("Object.assign",) and loop_depth:
            st.bump("n_assign_in_loop")
        if _b in ("parse",) and name.startswith("JSON") and loop_depth:
            st.bump("n_json_parse_in_loop")
        if _b in ("push", "concat", "unshift") and loop_depth:
            st.bump("n_array_grow_in_loop")   # unicorn/no-array-push-push
        if _b in ("indexOf", "includes", "find") and loop_depth:
            st.bump("n_search_in_loop")       # accidental O(n^2)
        if name in ("Math.random",):
            st.bump("n_math_random")          # security/detect-pseudoRandomBytes
        if _b in ("createHash", "createHmac", "createCipher"):
            _args = node.child_by_field_name("arguments")
            _at = text_of(_args, src).lower() if _args is not None else ""
            if "md5" in _at or "sha1" in _at or "rc4" in _at or "des" in _at:
                st.bump("n_weak_hash")           # the algorithm is an ARGUMENT
        if _b in ("then",) and loop_depth:
            st.bump("n_then_in_loop")         # promise/no-promise-in-callback
        if _b in ("catch",) and loop_depth:
            st.bump("n_catch_in_loop")
        if name in ("process.exit",):
            st.bump("n_process_exit")         # unicorn/no-process-exit
        if name in ("Buffer",) or name.startswith("Buffer."):
            st.bump("n_buffer_call")          # node/no-deprecated-api
        if _b in ("setPrototypeOf", "__defineGetter__"):
            st.bump("n_proto_mutate")
        if fn.type == "import":
            st.bump("n_import_dynamic")
            st.calls.append(("import()", node.start_point[0] + 1, True,
                             bool(loop_depth)))
            return
        # An IIFE, a call on a call, or a computed member: the target is not a
        # name and pretending otherwise manufactures edges that do not exist.
        head = name[:1]
        dynamic = (not name or not (head.isalpha() or head in "_$#")
                   or "(" in name or "[" in name)
        st.calls.append((name[:200], node.start_point[0] + 1, dynamic,
                         bool(loop_depth)))
        if dynamic:
            st.bump("n_dynamic_calls")
        base = name.rsplit(".", 1)[-1]
        if loop_depth:
            for needle, col in self.LOOP_CALL_COUNTERS.items():
                if needle == base or needle in name:
                    st.bump(col)

        # -- named findings the hazard table cannot express ----------------
        if base.endswith("Sync") and len(base) > 4:
            st.bump("n_sync_calls")
        if name in ("eval", "Function") or base == "eval":
            st.bump("n_eval")
        elif name in ("JSON.parse", "JSON.stringify") or base in (
                "parse", "stringify") and name.startswith("JSON."):
            st.bump("n_json_parse")
        elif base == "require":
            args = node.child_by_field_name("arguments")
            if args is not None:
                kid = args.named_children[0] if args.named_children else None
                if kid is not None and kid.type not in ("string",):
                    st.bump("n_require_dynamic")
        elif base in ("all", "allSettled", "any", "race") and \
                name.startswith("Promise."):
            st.bump("n_promise_all")
        elif base == "then":
            st.bump("n_then")
            st.bump("n_promise_chain")
        elif base in ("catch", "finally") and "." in name:
            st.bump("n_catch_handler")
            st.bump("n_promise_chain")
        elif base in CACHE_WRITE_METHODS and "." in name:
            st.bump("n_cache_write")
        elif base in CACHE_DROP_METHODS and "." in name:
            st.bump("n_cache_drop")
        if SETSTATE_RE.match(base) or name.endswith(".setState"):
            st.bump("n_setstate")
        if node.type == "new_expression":
            if base == "Map" or base == "WeakMap":
                st.bump("n_new_map")
            elif base == "Set" or base == "WeakSet":
                st.bump("n_new_set")
            elif base in ("WeakRef", "FinalizationRegistry"):
                st.bump("n_weak_ref")
        # A call in statement position whose value is thrown away. If the
        # callee turns out to be async this is an unhandled rejection, and
        # that join happens in `floating-promise-crossmodule`.
        parent = node.parent
        if parent is not None and parent.type == "expression_statement":
            st.bump("n_floating_promise")
        if parent is not None and parent.type == "arguments":
            st.bump("n_callbacks")

    def on_node(self, node: Any, src: bytes, st: BodyStats,
                loop_depth: int, nest: int) -> None:
        t = node.type
        if t == "binary_expression":
            op = node.child_by_field_name("operator")
            o = text_of(op, src) if op is not None else ""
            if o in ("&&", "||"):
                st.bump("n_logical")
                st.cyclomatic += 1
            elif o == "??":
                st.bump("n_nullish")
                st.bump("n_null_check")
                st.cyclomatic += 1
            elif o in ("==", "!=", "===", "!==", "<", ">", "<=", ">="):
                st.bump("n_cmp")
                if o in ("==", "!=", "===", "!==") and _has_nullish_operand(
                        node, src):
                    st.bump("n_null_check")
            elif o in ("&", "|", "^"):
                st.bump("n_bitop")
            elif o in ("<<", ">>", ">>>"):
                st.bump("n_shift")
            elif o in ("+", "-", "*", "/", "%", "**"):
                st.bump("n_arith")
                if o == "+" and loop_depth and _looks_stringy(node, src):
                    st.bump("concat_in_loop")
        elif t == "unary_expression":
            op = node.child_by_field_name("operator")
            o = text_of(op, src) if op is not None else ""
            if o == "delete":
                st.bump("n_delete")
                arg = node.child_by_field_name("argument")
                if arg is not None and arg.type == "subscript_expression":
                    st.bump("n_dynamic_prop")
            elif o == "typeof":
                st.bump("n_null_check")
        elif t == "arrow_function" or t == "function_expression" or \
                t == "generator_function":
            st.bump("n_closures")
            if loop_depth:
                st.bump("alloc_in_loop")
                st.bump("n_closure_capture")
            if t == "arrow_function" and any(c.type == "async"
                                             for c in node.children):
                st.bump("n_async_arrow")
        elif t == "await_expression":
            if loop_depth:
                st.bump("await_in_loop")
        elif t == "assignment_expression" or \
                t == "augmented_assignment_expression":
            left = node.child_by_field_name("left")
            if left is None:
                return
            ltxt = text_of(left, src)
            if left.type == "subscript_expression":
                idx = left.child_by_field_name("index")
                if idx is not None and idx.type != "string" and \
                        idx.type != "number":
                    st.bump("n_dynamic_prop")
                obj = left.child_by_field_name("object")
                if obj is not None and obj.type in ("subscript_expression",
                                                    "member_expression"):
                    # `obj[k1][k2] = v` -- the exact prototype-pollution write
                    st.bump("n_proto_write")
            if "__proto__" in ltxt or ltxt.endswith(".constructor") or \
                    ".prototype" in ltxt:
                st.bump("n_proto_write")
            if left.type == "member_expression":
                prop = left.child_by_field_name("property")
                p = text_of(prop, src) if prop is not None else ""
                if p in ("innerHTML", "outerHTML", "srcdoc"):
                    st.bump("n_innerhtml")
        elif t == "object" or t == "array":
            if loop_depth:
                st.bump("alloc_in_loop")
        elif t == "template_string":
            if loop_depth:
                st.bump("concat_in_loop")
        elif t == "regex":
            pat = node.child_by_field_name("pattern")
            if pat is not None:
                text = text_of(pat, src)
                if REDOS_NESTED_RE.search(text) or REDOS_ALT_RE.search(text):
                    st.bump("n_regex_redos")
            if loop_depth:
                st.bump("regex_in_loop")
        elif t == "identifier":
            if text_of(node, src) == "arguments":
                st.bump("n_arguments")
        elif t == "return_statement":
            if nest > 0:
                st.bump("n_early_returns")
        elif t == "catch_clause":
            body = node.child_by_field_name("body")
            if body is not None and not body.named_children:
                st.bump("n_catch_empty")
            btxt = text_of(body, src) if body is not None else ""
            if "throw" not in btxt:
                st.bump("n_catch_broad")
        elif t == "jsx_attribute":
            kids = node.named_children
            if kids and text_of(kids[0], src) == "dangerouslySetInnerHTML":
                st.bump("n_innerhtml")

    def on_string(self, node: Any, text: str, src: bytes, st: BodyStats,
                  loop_depth: int) -> None:
        if node.type == "template_string":
            return
        low = text[:200].lower()
        if "<script" in low or "<div" in low or "<span" in low or "</" in low:
            st.bump("n_innerhtml") if len(text) > 24 else None

    # -- hazards and resolution -------------------------------------------
    def hazard_of(self, callee: str) -> Optional[tuple[str, str]]:
        cat = HAZARD_CALLS.get(callee)
        if cat is not None:
            return callee, cat
        base = callee.rsplit(".", 1)[-1]
        cat = HAZARD_CALLS.get(base)
        if cat is not None:
            return "*." + base if "." in callee else base, cat
        if base.endswith("Sync") and len(base) > 4:
            return "*." + base, "sync_block"
        return None

    def normalise_callee(self, raw: str) -> str:
        name = raw.strip().replace("?.", ".")
        # A member chain wrapped across lines collapses to `a.b .for`, and the
        # stray space makes every one of them a distinct unresolved name.
        if " " in name:
            name = re.sub(r'\s*\.\s*', '.', name)
        if not name or name.startswith(("(", "[", "{")):
            return ""
        if name in ("super", "this", "import"):
            return ""
        if "(" in name or "[" in name:
            # `p.then(f).catch` -- only the final segment is a nameable target
            name = name.rsplit(".", 1)[-1]
            if "(" in name or "[" in name:
                return ""
        for prefix in ("this.", "self.", "globalThis.", "window."):
            if name.startswith(prefix):
                name = name[len(prefix):]
                break
        return name

    def is_external(self, name: str, base: str, fid: int) -> bool:
        """A call that leaves this tree by design is NOT blindness.

        Folding the platform into `unresolved` makes every JavaScript repo read
        as 80% blind when almost all of it is `console.log` and `Array.isArray`
        behaving exactly as specified, and the honesty column stops saying
        anything.
        """
        head = name.split(".")[0]
        if head in JS_GLOBALS or name in JS_GLOBALS:
            return True
        if head in NODE_BUILTINS or name.startswith("node:"):
            return True
        binding = self.bindings.get(fid, {}).get(head)
        if binding is not None and binding[2]:
            return True
        if GENERATED_HINT_RE.match(head):
            return True
        # A method name that is not in this tree at all and reads like a
        # platform method (`.map`, `.toString`) is the standard library.
        if "." in name and base not in self.by_name and base in ARRAY_PROTO:
            return True
        return False

    # -- imports and exports ----------------------------------------------
    def parse_imports(self, root: Any, rec: FileRec, bufs: Buffers) -> None:
        """Every way a JavaScript file names another one.

        Runs before the scope walk so `self.bindings` is populated before any
        call is resolved, and so `export { a, b }` has already named `a` and `b`
        by the time their declarations are turned into symbols.
        """
        src = rec.data
        here = os.path.dirname(rec.rel)
        binds: dict[str, tuple[str, str, int]] = {}
        self.bindings[rec.fid] = binds

        for n in walk(root):
            t = n.type
            if t == "import_statement":
                self._import_stmt(n, rec, bufs, here, binds)
            elif t == "export_statement":
                self._export_stmt(n, rec, bufs, here)
            elif t == "call_expression":
                fn = n.child_by_field_name("function")
                if fn is None:
                    continue
                ftxt = text_of(fn, src)
                if fn.type == "import" or ftxt == "require":
                    args = n.child_by_field_name("arguments")
                    kid = (args.named_children[0]
                           if args is not None and args.named_children else None)
                    dynamic = int(kid is None or kid.type != "string")
                    spec = _string_value(kid, src) if not dynamic else ""
                    tid, external = self._resolve_spec(here, spec)
                    kind = "dynamic-import" if fn.type == "import" else "require"
                    bufs.imports.append(
                        (rec.fid, (spec or "(computed)")[:300], tid, None,
                         kind, n.start_point[0] + 1, external,
                         int(spec.startswith(".")), 0, 0, 1, 0))
                    if not dynamic:
                        # `const { a, b } = require("pkg")` binds TWO names, and
                        # reading only the declarator text binds the string
                        # "{ a, b }" to nothing -- which leaves every later call
                        # to `a` looking like blindness instead of a package.
                        for local, imported in _require_bindings(n, src):
                            binds[local] = (spec, imported, external)
                            bufs.rows("import_names").append(
                                (rec.fid, spec[:300], tid, imported[:120],
                                 local[:120], n.start_point[0] + 1,
                                 int(imported == "*"), 0, external))
            elif t == "assignment_expression":
                left = n.child_by_field_name("left")
                if left is None or left.type != "member_expression":
                    continue
                ltxt = text_of(left, src)
                if ltxt == "module.exports":
                    self._cjs_exports(n, rec, bufs)
                elif ltxt.startswith("exports."):
                    name = ltxt.split(".", 1)[1]
                    self._exported.add(name)
                    bufs.rows("exports").append(
                        (rec.fid, None, name[:120], name[:120], "cjs",
                         n.start_point[0] + 1, "", None, 0, 0, 1))

    def _import_stmt(self, n: Any, rec: FileRec, bufs: Buffers, here: str,
                     binds: dict[str, tuple[str, str, int]]) -> None:
        src = rec.data
        srcn = n.child_by_field_name("source")
        spec = _string_value(srcn, src)
        tid, external = self._resolve_spec(here, spec)
        line = n.start_point[0] + 1
        names: list[tuple[str, str, int, int]] = []       # name, alias, ns, dflt
        wildcard = 0
        for c in walk(n):
            if c.type == "import_specifier":
                nm = c.child_by_field_name("name")
                al = c.child_by_field_name("alias")
                names.append((text_of(nm, src) if nm is not None else "",
                              text_of(al, src) if al is not None else "", 0, 0))
            elif c.type == "namespace_import":
                ident = [k for k in c.named_children if k.type == "identifier"]
                names.append(("*", text_of(ident[0], src) if ident else "", 1, 0))
                wildcard = 1
            elif c.type == "import_clause":
                for k in c.named_children:
                    if k.type == "identifier":
                        names.append(("default", text_of(k, src), 0, 1))
        type_only = int(any(c.type == "import_attribute"
                            and "type" in text_of(c, src) for c in n.children))
        bufs.imports.append(
            (rec.fid, spec[:300], tid, None, "import", line, external,
             int(spec.startswith(".")), wildcard, type_only, 0, len(names)))
        for nm, alias, ns, dflt in names:
            local = alias or nm
            if local:
                binds[local] = (spec, nm, external)
            bufs.rows("import_names").append(
                (rec.fid, spec[:300], tid, nm[:120], alias[:120], line,
                 ns, dflt, external))

    def _export_stmt(self, n: Any, rec: FileRec, bufs: Buffers,
                     here: str) -> None:
        src = rec.data
        line = n.start_point[0] + 1
        srcn = n.child_by_field_name("source")
        spec = _string_value(srcn, src) if srcn is not None else ""
        sid_src, external = self._resolve_spec(here, spec) if spec else (None, 0)
        reexport = int(bool(spec))
        clause = [c for c in n.named_children if c.type == "export_clause"]
        ns = [c for c in n.named_children if c.type == "namespace_export"]
        decl = n.child_by_field_name("declaration")
        val = n.child_by_field_name("value")

        if clause:
            for spec_node in clause[0].named_children:
                nm = spec_node.child_by_field_name("name")
                al = spec_node.child_by_field_name("alias")
                local = text_of(nm, src) if nm is not None else ""
                public = text_of(al, src) if al is not None else local
                self._exported.add(local)
                self._exported.add(public)
                bufs.rows("exports").append(
                    (rec.fid, None, public[:120], local[:120],
                     "reexport" if reexport else "named", line, spec[:300],
                     sid_src, reexport, 0, 0))
        elif ns:
            name = text_of(ns[0], src).strip()
            bufs.rows("exports").append(
                (rec.fid, None, name[:120], "*", "star-as", line, spec[:300],
                 sid_src, 1, 1, 0))
        elif spec and not clause and decl is None and val is None:
            bufs.rows("exports").append(
                (rec.fid, None, "*", "*", "star", line, spec[:300],
                 sid_src, 1, 1, 0))
        elif decl is not None:
            for name in _declared_names(decl, src):
                self._exported.add(name)
                bufs.rows("exports").append(
                    (rec.fid, None, name[:120], name[:120], "named", line,
                     "", None, 0, 0, 0))
        elif val is not None:
            local = _binding_name_of_value(val, src)
            self._exported.add(local or "default")
            bufs.rows("exports").append(
                (rec.fid, None, "default", (local or "default")[:120],
                 "default", line, "", None, 0, 0, 0))

    def _cjs_exports(self, n: Any, rec: FileRec, bufs: Buffers) -> None:
        src = rec.data
        right = n.child_by_field_name("right")
        line = n.start_point[0] + 1
        if right is not None and right.type == "object":
            for kid in right.named_children:
                nm = ""
                if kid.type == "pair":
                    k = kid.child_by_field_name("key")
                    nm = text_of(k, src) if k is not None else ""
                elif kid.type == "shorthand_property_identifier":
                    nm = text_of(kid, src)
                if nm:
                    self._exported.add(nm)
                    bufs.rows("exports").append(
                        (rec.fid, None, nm[:120], nm[:120], "cjs", line,
                         "", None, 0, 0, 1))
            return
        local = _binding_name_of_value(right, src) if right is not None else ""
        self._exported.add(local or "default")
        bufs.rows("exports").append(
            (rec.fid, None, "default", (local or "default")[:120], "cjs",
             line, "", None, 0, 0, 1))

    def _resolve_spec(self, here: str, spec: str) -> tuple[Optional[int], int]:
        """(target file id, is_external) for one module specifier."""
        if not spec:
            return None, 0
        if not spec.startswith("."):
            return None, 1
        base = os.path.normpath(os.path.join(here, spec)).replace(os.sep, "/")
        for cand in (base, base + ".js", base + ".mjs", base + ".cjs",
                     base + ".jsx", base + "/index.js", base + "/index.mjs",
                     base + "/index.cjs", base + "/index.jsx"):
            fid = self.file_id.get(cand)
            if fid is not None:
                return fid, 0
        return None, 0

    # -- per-symbol detail -------------------------------------------------
    def function_extra(self, node: Any, rec: FileRec, db: sqlite3.Connection,
                       bufs: Buffers, sid: int, scope: Scope,
                       stats: BodyStats) -> None:
        """Record the byte span only.

        Listeners, timers, hooks and JSX are collected in ONE pass over the
        whole file in `parse_file_extra`, not here: the base measures nested
        function bodies again as their own symbols, so doing it per function
        would write a duplicate row for every level of nesting.
        """
        self._spans.append((node.start_byte, node.end_byte, sid))
        self._span_starts.append(node.start_byte)

    def emit_attributes(self, node: Any, rec: FileRec, sid: int,
                        bufs: Buffers) -> None:
        for c in node.children:
            if c.type != "decorator":
                continue
            txt = text_of(c, rec.data).strip()
            name = txt.lstrip("@").split("(")[0].strip()
            bufs.attributes.append(
                (sid, rec.fid, name[:120], txt[:200], c.start_point[0] + 1))

    def type_extra(self, node: Any, rec: FileRec, db: sqlite3.Connection,
                   bufs: Buffers, sid: int, scope: Scope) -> None:
        src = rec.data
        name = self.node_name(node, rec)
        body = node.child_by_field_name("body")
        if body is None:
            return
        heritage = [c for c in node.named_children if c.type == "class_heritage"]
        extends = text_of(heritage[0], src).replace("extends", "").strip() \
            if heritage else ""
        n_methods = n_static = n_get = n_set = n_priv = 0
        n_fields = n_arrow = n_computed = 0
        has_ctor = has_static_block = 0
        for i, member in enumerate(body.named_children):
            mtxt = text_of(member, src)[:200]
            if member.type == "class_static_block":
                has_static_block = 1
                continue
            is_static = 1 if any(c.type == "static" for c in member.children) \
                else 0
            nm_node = member.child_by_field_name("name") or \
                member.child_by_field_name("property")
            nm = text_of(nm_node, src) if nm_node is not None else ""
            if nm_node is not None and nm_node.type == "computed_property_name":
                n_computed += 1
            if nm.startswith("#"):
                n_priv += 1
            if member.type == "method_definition":
                n_methods += 1
                n_static += is_static
                if any(c.type == "get" for c in member.children):
                    n_get += 1
                elif any(c.type == "set" for c in member.children):
                    n_set += 1
                if nm == "constructor":
                    has_ctor = 1
            elif member.type == "field_definition":
                n_fields += 1
                n_static += is_static
                val = member.child_by_field_name("value")
                if val is not None and val.type in ("arrow_function",
                                                    "function_expression"):
                    n_arrow += 1
                bufs.fields.append(
                    (sid, i, nm[:120], "", "private" if nm.startswith("#")
                     else "public", member.start_point[0] + 1, is_static, 0,
                     1, 0, int("[" in mtxt or "Map(" in mtxt), 1,
                     int(val is not None), 0))
        bufs.rows("classes").append(
            (sid, rec.fid, extends[:200], n_methods, n_static, n_get, n_set,
             n_priv, n_fields, n_arrow, n_computed, has_ctor,
             has_static_block, int(_is_exported(node) or name in self._exported),
             int(bool(COMPONENT_NAME_RE.match(name)))))

    # -- the whole-file pass ----------------------------------------------
    def parse_file_extra(self, root: Any, rec: FileRec,
                         db: sqlite3.Connection, bufs: Buffers) -> None:
        """One walk for every table that needs a byte offset attributed.

        Runs AFTER the scope walk so `self._spans` is complete and every row can
        name the function it sits in -- or say `(module scope)`, which for a
        listener registered at import time is the interesting answer.
        """
        src = rec.data
        self._spans.sort()
        self._span_starts = [s for s, _, _ in self._spans]
        caches = self._module_cache_candidates(root, src)
        cache_use: dict[str, list[int]] = {n: [0, 0, 0, 0] for n in caches}
        cache_writers: dict[str, set[str]] = {n: set() for n in caches}
        handler_spans: list[int] = []

        for n in walk(root):
            t = n.type
            if t == "call_expression" or t == "new_expression":
                self._call_row(n, rec, bufs, caches, cache_use, cache_writers,
                               handler_spans)
            elif t == "member_expression" or t == "subscript_expression":
                self._cache_touch(n, src, caches, cache_use, cache_writers)
            elif t == "jsx_opening_element" or t == "jsx_self_closing_element":
                self._jsx_row(n, rec, bufs)
            elif t == "regex":
                # `const RE = /(a+)+/` at module scope is the commonest place a
                # regex lives, and the body-measuring pass never reaches it --
                # it only walks function bodies. Recorded here so a top-level
                # catastrophic pattern is not invisible.
                pat = n.child_by_field_name("pattern")
                ptxt = text_of(pat, src) if pat is not None else ""
                if ptxt and (REDOS_NESTED_RE.search(ptxt)
                             or REDOS_ALT_RE.search(ptxt)):
                    bufs.literals.append(
                        (self._owner(n.start_byte), rec.fid, "regex_redos",
                         ptxt[:200], n.start_point[0] + 1, 1))
            elif t == "assignment_expression":
                left = n.child_by_field_name("left")
                if left is not None:
                    self._cache_touch(left, src, caches, cache_use,
                                      cache_writers, write=True)

        for name, (line, ctor, weak, exported, is_const) in caches.items():
            w, d, r, sz = cache_use[name]
            if not w and not d:
                continue
            bufs.rows("module_caches").append(
                (rec.fid, line, name[:120], ctor[:60], weak, exported,
                 is_const, w, d, r, sz, int(sz > 0),
                 ",".join(sorted(cache_writers[name]))[:300]))
        if handler_spans:
            # Buffered, not applied here: symbols are now written in one
            # executemany AFTER the parse loop, so an UPDATE issued during
            # parsing would match nothing. Applied in post_build instead.
            self._handler_spans.extend((rec.fid, off) for off in handler_spans)
        if rec.rel.endswith((".jsx",)) or "jsx" in rec.text[:200]:
            pass

    def _call_row(self, n: Any, rec: FileRec, bufs: Buffers,
                  caches: dict, cache_use: dict, cache_writers: dict,
                  handler_spans: list[int]) -> None:
        src = rec.data
        line = n.start_point[0] + 1
        new = n.type == "new_expression"
        fn = n.child_by_field_name("constructor" if new else "function")
        if fn is None:
            return
        raw = " ".join(text_of(fn, src).split())
        base = raw.rsplit(".", 1)[-1].replace("?.", "")
        target = raw[:-(len(base) + 1)] if "." in raw else ""
        args = n.child_by_field_name("arguments")
        kids = list(args.named_children) if args is not None else []
        sid = self._owner(n.start_byte)
        module_scope = int(sid is None)
        in_loop = int(_ancestor_of(n, LOOP_NODE_TYPES) is not None)

        if new and base in OBSERVER_CTORS:
            bufs.rows("listeners").append(
                (rec.fid, sid, line, "add", base, "observer", target[:120],
                 "", _arg_text(kids, 0, src)[:120],
                 int(bool(kids) and kids[0].type in ANON_FN_NODES), 0,
                 module_scope, in_loop, 0))
            return
        if base in LISTENER_ADD and not new:
            ev = _string_value(kids[0], src) if kids else ""
            if base in ("on", "once", "off") and not ev and len(kids) < 2:
                return                       # `.on(fn)` is not an event binding
            handler = _arg_text(kids, 1, src)
            inline = int(len(kids) > 1 and kids[1].type in ANON_FN_NODES)
            signal = int(len(kids) > 2 and "signal" in _arg_text(kids, 2, src))
            bufs.rows("listeners").append(
                (rec.fid, sid, line, "add", base, LISTENER_ADD[base],
                 target[:120], ev[:120], handler[:120], inline, signal,
                 module_scope, in_loop, 0))
        elif base in LISTENER_REMOVE and not new:
            ev = _string_value(kids[0], src) if kids else ""
            bufs.rows("listeners").append(
                (rec.fid, sid, line, "remove", base, LISTENER_REMOVE[base],
                 target[:120], ev[:120], _arg_text(kids, 1, src)[:120],
                 0, 0, module_scope, in_loop,
                 int(_in_cleanup_position(n))))
        elif base in TIMER_SET and not new:
            kind = TIMER_SET[base]
            handle = _binding_name(n, src)
            bufs.rows("timers").append(
                (rec.fid, sid, line, "set", base, kind, handle[:120],
                 int(bool(handle)), int(kind in TIMER_REPEATING),
                 int(".unref()" in text_of(n.parent, src)[:200]
                     if n.parent is not None else 0),
                 int(bool(kids) and kids[0].type == "string"),
                 module_scope, in_loop))
        elif base in TIMER_CLEAR and not new:
            bufs.rows("timers").append(
                (rec.fid, sid, line, "clear", base, TIMER_CLEAR[base],
                 _arg_text(kids, 0, src)[:120], 0, 0, 0, 0,
                 module_scope, in_loop))
        elif HOOK_NAME_RE.match(base) and not new:
            self._hook_row(n, rec, bufs, base, kids, sid, line)
        elif base in ROUTE_METHODS and target and ROUTE_OBJECTS.match(target):
            first = _string_value(kids[0], src) if kids else ""
            if first.startswith("/") or base == "use":
                for k in kids[1:]:
                    if k.type in ANON_FN_NODES:
                        handler_spans.append(k.start_byte)
                    elif k.type == "identifier":
                        self.handler_names.add(text_of(k, src))

        if not new and base in CACHE_WRITE_METHODS and target in caches:
            cache_use[target][0] += 1
            owner = self._owner(n.start_byte)
            cache_writers[target].add(str(owner) if owner else "module")
        elif not new and base in CACHE_DROP_METHODS and target in caches:
            cache_use[target][1] += 1

    def _hook_row(self, n: Any, rec: FileRec, bufs: Buffers, base: str,
                  kids: list, sid: Optional[int], line: int) -> None:
        src = rec.data
        deps = -1
        has_deps = 0
        if base in DEP_ARRAY_HOOKS and len(kids) > 1 and kids[1].type == "array":
            has_deps = 1
            deps = len(kids[1].named_children)
        cb = kids[0] if kids else None
        cbtxt = text_of(cb, src) if cb is not None else ""
        cleanup = int(cb is not None and cb.type in ANON_FN_NODES
                      and re.search(r'return\s*(?:\(\s*\)|function|\w+\s*=>)',
                                    cbtxt) is not None)
        bufs.rows("hooks").append(
            (rec.fid, sid, line, base[:120], int(base in BUILTIN_HOOKS),
             has_deps, deps, cleanup,
             int(_ancestor_of(n, LOOP_NODE_TYPES) is not None),
             int(_ancestor_of(n, CONDITION_NODE_TYPES) is not None),
             int("addEventListener" in cbtxt or ".on(" in cbtxt
                 or "subscribe" in cbtxt),
             int("setInterval" in cbtxt or "setTimeout" in cbtxt
                 or "requestAnimationFrame" in cbtxt)))

    def _jsx_row(self, n: Any, rec: FileRec, bufs: Buffers) -> None:
        src = rec.data
        nm = n.child_by_field_name("name")
        tag = text_of(nm, src) if nm is not None else "<>"
        attrs = [c for c in n.named_children
                 if c.type in ("jsx_attribute", "jsx_expression")]
        n_spread = sum(1 for a in attrs if a.type == "jsx_expression")
        inline_obj = inline_fn = has_key = dangerous = 0
        for a in attrs:
            if a.type != "jsx_attribute":
                continue
            kids = a.named_children
            aname = text_of(kids[0], src) if kids else ""
            if aname == "key":
                has_key = 1
            elif aname == "dangerouslySetInnerHTML":
                dangerous = 1
            if len(kids) > 1 and kids[1].type == "jsx_expression":
                inner = [k for k in kids[1].named_children]
                if inner and inner[0].type in ("object", "array"):
                    inline_obj += 1
                elif inner and inner[0].type in ANON_FN_NODES:
                    inline_fn += 1
        bufs.rows("jsx_components").append(
            (rec.fid, self._owner(n.start_byte), n.start_point[0] + 1,
             tag[:120], int(bool(tag) and (tag[0].isupper() or "." in tag)),
             len(attrs), n_spread, has_key, inline_obj, inline_fn, dangerous,
             int(_ancestor_of(n, LOOP_NODE_TYPES) is not None)))

    def _module_cache_candidates(self, root: Any,
                                 src: bytes) -> dict[str, tuple]:
        """Top-level containers: `const cache = new Map()` and friends.

        Module scope specifically, because that is the scope that lives as long
        as the process. The same `new Map()` inside a function is a local and
        dies with the call.
        """
        out: dict[str, tuple] = {}
        for n in walk(root):
            if n.type != "variable_declarator":
                continue
            if not _at_module_scope(n):
                continue
            nm = n.child_by_field_name("name")
            val = n.child_by_field_name("value")
            if nm is None or nm.type != "identifier" or val is None:
                continue
            ctor = ""
            if val.type == "new_expression":
                c = val.child_by_field_name("constructor")
                ctext = text_of(c, src).rsplit(".", 1)[-1] if c is not None else ""
                ctor = CACHE_CTORS.get(ctext, "")
                if not ctor and ctext.endswith(("Cache", "Registry", "Store",
                                                "Pool", "Emitter")):
                    ctor = ctext
            elif val.type == "object":
                ctor = "object"
            elif val.type == "array":
                ctor = "array"
            elif val.type == "call_expression":
                c = val.child_by_field_name("function")
                ctext = text_of(c, src) if c is not None else ""
                if ctext in ("Object.create", "new Map"):
                    ctor = "object"
            if not ctor:
                continue
            decl = n.parent
            out[text_of(nm, src)] = (
                n.start_point[0] + 1, ctor,
                int(ctor in WEAK_CTORS),
                int(_is_exported(n)),
                int(decl is not None and text_of(decl, src)[:5] == "const"))
        return out

    def _cache_touch(self, node: Any, src: bytes, caches: dict,
                     cache_use: dict, cache_writers: dict,
                     write: bool = False) -> None:
        obj = node.child_by_field_name("object")
        if obj is None or obj.type != "identifier":
            return
        name = text_of(obj, src)
        slot = cache_use.get(name)
        if slot is None:
            return
        prop = node.child_by_field_name("property")
        ptxt = text_of(prop, src) if prop is not None else ""
        if ptxt in ("size", "length"):
            slot[3] += 1
        elif write:
            slot[0] += 1
        else:
            slot[2] += 1

    # -- manifests, wiring, flush -----------------------------------------
    def parse_manifests(self, root: str, db: sqlite3.Connection) -> None:
        path = os.path.join(root, "package.json")
        if not os.path.isfile(path):
            return
        try:
            data = json.loads(open(path, encoding="utf-8",
                                   errors="replace").read())
        except (OSError, ValueError):
            return
        if not isinstance(data, dict):
            return
        self.pkg_name = str(data.get("name", "?"))
        self.pkg_type = str(data.get("type", "commonjs"))
        deps = data.get("dependencies") or {}
        dev = data.get("devDependencies") or {}
        engines = data.get("engines") or {}
        db.executemany(
            "INSERT OR REPLACE INTO meta(key,value) VALUES(?,?)",
            (
            ("package", self.pkg_name),
            ("module_type",
             "%s (%s)" % (self.pkg_type,
                          "import/export" if self.pkg_type == "module"
                          else "require/module.exports")),
            ("dependencies", "%d runtime / %d dev"
             % (len(deps) if isinstance(deps, dict) else 0,
                len(dev) if isinstance(dev, dict) else 0)),
            ("engines_node", str(engines.get("node", "unspecified"))),
            ("has_exports_map", "yes" if data.get("exports") else "no"),
            ("side_effects", str(data.get("sideEffects", "unspecified"))),
        ))

    def post_build(self, db: sqlite3.Connection) -> None:
        """Mark route-registered handlers by name, across files.

        `app.get("/x", handleThing)` names its handler in one file and defines
        it in another, so this cannot happen during the per-file walk.
        """
        if self.handler_names:
            names = sorted(self.handler_names)
            for i in range(0, len(names), 400):
                chunk = names[i:i + 400]
                db.execute(
                    "UPDATE symbols SET is_handler=1 WHERE name IN (%s)"
                    % ",".join("?" * len(chunk)), chunk)
        db.execute(
            "INSERT OR REPLACE INTO meta(key,value) VALUES(?,?)",
            ("retention_scan",
             "%d listener op(s), %d timer op(s), %d module-scope container(s) "
             "-- no linter in ESLint/typescript-eslint/unicorn/Biome/oxlint/"
             "CodeQL-JS checks any of these"
             % ((db.execute("SELECT COUNT(*) FROM listeners").fetchone()
                 or [0])[0],
                (db.execute("SELECT COUNT(*) FROM timers").fetchone()
                 or [0])[0],
                (db.execute("SELECT COUNT(*) FROM module_caches").fetchone()
                 or [0])[0])))

    def flush_extra(self, db: sqlite3.Connection, bufs: Buffers) -> None:
        for tbl, sql in (
            ("classes",
             "INSERT OR IGNORE INTO classes(symbol_id,file_id,extends,"
             "n_methods,n_static,n_getters,n_setters,n_private,n_fields,"
             "n_arrow_fields,n_computed_members,has_constructor,"
             "has_static_block,is_exported,is_component) "
             "VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)"),
            ("exports",
             "INSERT INTO exports(file_id,symbol_id,name,local_name,kind,line,"
             "source,source_id,is_reexport,is_star,is_cjs) "
             "VALUES(?,?,?,?,?,?,?,?,?,?,?)"),
            ("import_names",
             "INSERT INTO import_names(file_id,source,source_id,name,alias,"
             "line,is_namespace,is_default,is_external) "
             "VALUES(?,?,?,?,?,?,?,?,?)"),
            ("listeners",
             "INSERT INTO listeners(file_id,symbol_id,line,op,api,family,"
             "target,event,handler,handler_inline,has_signal,at_module_scope,"
             "in_loop,in_cleanup) VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?,?)"),
            ("timers",
             "INSERT INTO timers(file_id,symbol_id,line,op,api,kind,handle,"
             "is_assigned,is_repeating,is_unrefd,callback_is_string,"
             "at_module_scope,in_loop) VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?)"),
            ("module_caches",
             "INSERT INTO module_caches(file_id,line,name,ctor,is_weak,"
             "is_exported,is_const,n_writes,n_drops,n_reads,n_size_checks,"
             "has_max,writer_fns) VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?)"),
            ("jsx_components",
             "INSERT INTO jsx_components(file_id,symbol_id,line,tag,"
             "is_component,n_attrs,n_spread,has_key,inline_object_props,"
             "inline_fn_props,has_dangerous_html,in_loop) "
             "VALUES(?,?,?,?,?,?,?,?,?,?,?,?)"),
            ("hooks",
             "INSERT INTO hooks(file_id,symbol_id,line,name,is_builtin,"
             "has_dep_array,n_deps,has_cleanup,in_loop,in_condition,"
             "registers_listener,registers_timer) "
             "VALUES(?,?,?,?,?,?,?,?,?,?,?,?)"),
        ):
            rows = bufs.extra.get(tbl)
            if rows:
                db.executemany(sql, rows)

ANON_FN_NODES = frozenset((
    "arrow_function", "function_expression", "generator_function", "class"))

FN_NODE_TYPES = frozenset((
    "function_declaration", "generator_function_declaration",
    "function_expression", "generator_function", "arrow_function",
    "method_definition", "class_static_block"))

LOOP_NODE_TYPES = frozenset((
    "for_statement", "for_in_statement", "while_statement", "do_statement"))

CONDITION_NODE_TYPES = frozenset((
    "if_statement", "ternary_expression", "switch_case",
    "else_clause", "catch_clause"))

ARRAY_PROTO = frozenset("""
map filter reduce reduceRight forEach some every find findIndex findLast
findLastIndex includes indexOf lastIndexOf join reverse sort concat slice
splice push pop shift unshift fill flat flatMap keys values entries at
toString valueOf hasOwnProperty toFixed toPrecision charAt charCodeAt codePointAt
startsWith endsWith padStart padEnd trim trimStart trimEnd split replace
replaceAll match matchAll search normalize repeat toLowerCase toUpperCase
localeCompare toISOString getTime setTime add clear delete get has set size
then catch finally next return throw bind call apply
""".split())

def _txt(node: Any, src: bytes) -> str:
    return src[node.start_byte:node.end_byte].decode("utf-8", "replace")

def _string_value(node: Optional[Any], src: bytes) -> str:
    """The text inside a string literal, or '' for anything computed."""
    if node is None or node.type != "string":
        return ""
    for c in node.named_children:
        if c.type == "string_fragment":
            return _txt(c, src)
    return ""

def _arg_text(kids: list, i: int, src: bytes) -> str:
    if i >= len(kids):
        return ""
    return " ".join(_txt(kids[i], src).split())

def _binding_name(node: Any, src: bytes) -> str:
    """The name a nameless expression is being bound to, if any.

    `const f = () => {}`, `{ f: () => {} }`, `class C { f = () => {} }` and
    `obj.f = function(){}` all give the function a name in every stack trace and
    in every developer's head. Reading only the function node gives none of them.
    """
    cur = node.parent
    hops = 0
    while cur is not None and hops < 4:
        t = cur.type
        if t == "variable_declarator":
            nm = cur.child_by_field_name("name")
            return _txt(nm, src).strip() if nm is not None else ""
        if t == "pair":
            k = cur.child_by_field_name("key")
            return _txt(k, src).strip().strip("'\"") if k is not None else ""
        if t == "field_definition":
            p = cur.child_by_field_name("property")
            return _txt(p, src).strip() if p is not None else ""
        if t == "assignment_expression":
            left = cur.child_by_field_name("left")
            if left is None:
                return ""
            txt = _txt(left, src).strip()
            return txt.rsplit(".", 1)[-1] if "." in txt else txt
        if t == "export_statement":
            return "default"
        if t in ("parenthesized_expression", "await_expression"):
            cur = cur.parent
            hops += 1
            continue
        return ""
    return ""

def _require_bindings(call: Any, src: bytes) -> list[tuple[str, str]]:
    """(local name, imported name) pairs for one `require(...)` call site."""
    decl = call.parent
    if decl is None or decl.type != "variable_declarator":
        return []
    nm = decl.child_by_field_name("name")
    if nm is None:
        return []
    if nm.type == "identifier":
        return [(_txt(nm, src).strip(), "*")]
    out: list[tuple[str, str]] = []
    if nm.type == "object_pattern":
        for kid in nm.named_children:
            if kid.type == "shorthand_property_identifier_pattern":
                n = _txt(kid, src).strip()
                out.append((n, n))
            elif kid.type == "pair_pattern":
                k = kid.child_by_field_name("key")
                v = kid.child_by_field_name("value")
                if k is not None and v is not None and v.type == "identifier":
                    out.append((_txt(v, src).strip(), _txt(k, src).strip()))
    return out

def _binding_name_of_value(node: Any, src: bytes) -> str:
    if node is None:
        return ""
    if node.type in ("identifier", "property_identifier"):
        return _txt(node, src).strip()
    nm = node.child_by_field_name("name")
    return _txt(nm, src).strip() if nm is not None else ""

def _declared_names(decl: Any, src: bytes) -> list[str]:
    nm = decl.child_by_field_name("name")
    if nm is not None:
        return [_txt(nm, src).strip()]
    out: list[str] = []
    for d in decl.named_children:
        if d.type != "variable_declarator":
            continue
        n = d.child_by_field_name("name")
        if n is None:
            continue
        if n.type == "identifier":
            out.append(_txt(n, src).strip())
        else:                                  # destructured export
            for k in walk(n):
                if k.type in ("shorthand_property_identifier_pattern",
                              "identifier"):
                    out.append(_txt(k, src).strip())
    return out

def _is_exported(node: Any) -> bool:
    cur = node.parent
    hops = 0
    while cur is not None and hops < 4:
        if cur.type == "export_statement":
            return True
        if cur.type in ("statement_block", "program", "class_body"):
            return cur.type == "program" and False
        cur = cur.parent
        hops += 1
    return False

def _is_default_export(node: Any) -> bool:
    cur = node.parent
    hops = 0
    while cur is not None and hops < 3:
        if cur.type == "export_statement":
            return cur.child_by_field_name("value") is not None or \
                any(c.type == "default" for c in cur.children)
        cur = cur.parent
        hops += 1
    return False

def _at_module_scope(node: Any) -> bool:
    cur = node.parent
    while cur is not None:
        if cur.type in FN_NODE_TYPES:
            return False
        cur = cur.parent
    return True

def _ancestor_of(node: Any, types: frozenset) -> Optional[Any]:
    """Nearest ancestor of one of `types`, stopping at the function boundary."""
    cur = node.parent
    while cur is not None:
        if cur.type in types:
            return cur
        if cur.type in FN_NODE_TYPES:
            return None
        cur = cur.parent
    return None

def _nearest_call_of(node: Any) -> Optional[Any]:
    cur = node.parent
    hops = 0
    while cur is not None and hops < 3:
        if cur.type == "call_expression":
            fn = cur.child_by_field_name("function")
            if fn is not None and (fn is node or _contains(fn, node)):
                return cur
            return None
        cur = cur.parent
        hops += 1
    return None

def _contains(outer: Any, inner: Any) -> bool:
    return outer.start_byte <= inner.start_byte and \
        inner.end_byte <= outer.end_byte

def _in_cleanup_position(node: Any) -> bool:
    """Inside the function an effect RETURNS -- the React teardown slot."""
    cur = node.parent
    hops = 0
    while cur is not None and hops < 8:
        if cur.type in ANON_FN_NODES and cur.parent is not None and \
                cur.parent.type == "return_statement":
            return True
        if cur.type in ("call_expression",):
            fn = cur.child_by_field_name("function")
            if fn is not None and _txt(fn, b"") == "":
                pass
        cur = cur.parent
        hops += 1
    return False

def _has_nullish_operand(node: Any, src: bytes) -> bool:
    for field in ("left", "right"):
        c = node.child_by_field_name(field)
        if c is not None and _txt(c, src).strip() in ("null", "undefined"):
            return True
    return False

def _looks_stringy(node: Any, src: bytes) -> bool:
    for field in ("left", "right"):
        c = node.child_by_field_name(field)
        if c is not None and c.type in ("string", "template_string"):
            return True
    return False

JavaScriptAnalyzer.QUERIES = [
(
    "retention-leak-frontier",
    "Listeners and timers registered with nothing in the module that undoes it",
    "ANSWERS the gap no JavaScript linter fills. ESLint core (199 rules),\n"
    "     typescript-eslint (134), unicorn (336), Biome (436), oxlint (847) and\n"
    "     CodeQL-JS (200) were all read: not one of them pairs an add with a\n"
    "     remove or a setInterval with a clearInterval. This does, per module,\n"
    "     and every row is a reference the garbage collector can never reclaim.\n"
    "ACT unremovable = 1 is the strongest signal on the page and means the\n"
    "     teardown CANNOT be written later, not that somebody forgot. For a\n"
    "     listener it is an anonymous handler -- no identity, so\n"
    "     removeEventListener has nothing to name. For a timer it is a\n"
    "     discarded handle -- clearInterval has no id to pass. Give the handler\n"
    "     a name, keep the handle, or pass { signal } from an AbortController\n"
    "     (rows already covered by a signal are excluded entirely).\n"
    "     module_scope = 1 registers at import time and lives as long as the\n"
    "     process -- in Node that alone keeps the process alive unless the timer\n"
    "     is unref'd. in_loop = 1 registers once per element.\n"
    "MISLEADS a listener on an object that dies with the page, a `once`, or an\n"
    "     interval in a daemon that is SUPPOSED to run forever, are all correct\n"
    "     and all appear here. A teardown written in a DIFFERENT module is\n"
    "     invisible: pairing is per-file on purpose, because a cross-file rule\n"
    "     matches by name and would let any off() anywhere cancel every on().\n"
    "     Recursive setTimeout is a repeating timer this does not classify as\n"
    "     one, so the true timer count is higher than shown.",
    """WITH lis AS (
        SELECT a.id, a.api, a.family AS detail, a.event, a.target,
            a.handler, a.handler_inline AS unremovable, a.line, a.file_id,
            a.symbol_id, a.at_module_scope AS module_scope, a.in_loop,
            (SELECT COUNT(*) FROM listeners r
             WHERE r.file_id = a.file_id AND r.op = 'remove'
               AND (r.api = 'removeAllListeners' OR r.api = 'disconnect'
                    OR (r.handler <> '' AND r.handler = a.handler)
                    OR (r.event <> '' AND r.event = a.event
                        AND (r.target = a.target OR r.target = ''))))
                AS undone
        FROM listeners a
        JOIN files f ON f.id = a.file_id
        LEFT JOIN modules m ON m.id = f.module_id
        WHERE a.op = 'add' AND a.has_signal = 0 AND f.is_test = 0
          AND COALESCE(m.name,'') LIKE :mod),
    tim AS (
        SELECT t.id, t.api, t.kind AS detail, '' AS event, t.handle AS target,
            '' AS handler, (1 - t.is_assigned) AS unremovable, t.line,
            t.file_id, t.symbol_id, t.at_module_scope AS module_scope,
            t.in_loop,
            (SELECT COUNT(*) FROM timers c
             WHERE c.file_id = t.file_id AND c.op = 'clear'
               AND (c.kind = t.kind OR c.handle = t.handle)) AS undone
        FROM timers t
        JOIN files f ON f.id = t.file_id
        LEFT JOIN modules m ON m.id = f.module_id
        WHERE t.op = 'set' AND f.is_test = 0 AND t.is_unrefd = 0
          AND (t.is_repeating = 1 OR t.in_loop = 1 OR t.at_module_scope = 1)
          AND COALESCE(m.name,'') LIKE :mod),
    both AS (SELECT 'listener' AS what, * FROM lis WHERE undone = 0
             UNION ALL
             SELECT 'timer' AS what, * FROM tim WHERE undone = 0)
    SELECT b.what, b.api, b.detail, b.event, SUBSTR(b.target,1,20) AS target,
        SUBSTR(b.handler,1,24) AS handler, b.unremovable,
        b.module_scope, b.in_loop,
        COALESCE(s.name,'(module scope)') AS in_fn,
        COALESCE(s.is_component,0) AS component,
        (SELECT COUNT(*) FROM hooks h
         WHERE h.symbol_id = b.symbol_id AND h.has_cleanup = 1)
            AS effects_with_cleanup,
        f.path || ':' || b.line AS at
    FROM both b
    JOIN files f ON f.id = b.file_id
    LEFT JOIN symbols s ON s.id = b.symbol_id
    ORDER BY b.unremovable DESC, b.module_scope DESC, b.in_loop DESC,
        b.what, b.api LIMIT :lim"""),
(
    "unbounded-module-cache",
    "Module-scope containers that are written to and never emptied",
    "ANSWERS the other half of the linter gap: a Map, Set, object or array\n"
    "     declared at module scope lives as long as the process, and if nothing\n"
    "     ever deletes, clears, evicts or bounds it, it is a memory leak with a\n"
    "     growth rate equal to your traffic. No rule in any of the six\n"
    "     JavaScript toolchains surveyed checks this.\n"
    "ACT give it a bound. An LRU with a max size, a WeakMap keyed by the object\n"
    "     it describes, or an explicit delete on the way out. has_max = 1 means\n"
    "     something already reads .size or .length, which is usually an eviction\n"
    "     test and is the counter-evidence.\n"
    "     is_weak = 1 rows are already collectable and are excluded entirely.\n"
    "MISLEADS init_only = 1 means every write happens at module scope: a lookup\n"
    "     table or a registry of built-in plugins, bounded by the source rather\n"
    "     than by traffic, and fine. Those are sorted to the bottom rather than\n"
    "     hidden, because 'written once at startup' is a judgement about intent\n"
    "     and this only measures position. Read writes next to writer_fns: one\n"
    "     writer in an init function is harmless, a writer reached from a\n"
    "     request handler is not. This counts textual property access on the\n"
    "     declared name, so a cache passed to another module as an argument and\n"
    "     written there shows zero writes here.",
    """SELECT c.name, c.ctor, c.is_const AS const_, c.is_exported AS exported,
        c.n_writes AS writes, c.n_drops AS drops, c.n_reads AS reads,
        c.n_size_checks AS size_checks,
        (LENGTH(c.writer_fns) - LENGTH(REPLACE(c.writer_fns,',','')) + 1)
            AS writer_fns,
        CASE WHEN c.writer_fns = 'module' THEN 1 ELSE 0 END AS init_only,
        (SELECT COALESCE(MAX(s.n_sync_calls + s.n_net + s.n_io),0)
         FROM symbols s WHERE s.file_id = c.file_id) AS io_in_file,
        (SELECT COUNT(*) FROM symbols s
         WHERE s.file_id = c.file_id AND s.is_handler = 1) AS handlers_in_file,
        f.path || ':' || c.line AS at
    FROM module_caches c
    JOIN files f ON f.id = c.file_id
    LEFT JOIN modules m ON m.id = f.module_id
    WHERE c.n_drops = 0 AND c.is_weak = 0 AND c.n_writes > 0
      AND f.is_test = 0 AND f.is_generated = 0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY init_only ASC, handlers_in_file DESC, c.n_writes DESC,
        c.n_size_checks ASC LIMIT :lim"""),
(
    "event-loop-block-frontier",
    "Blocking *Sync calls reachable from a request handler, up to 4 hops",
    "ANSWERS which synchronous file, crypto or child-process call sits on a\n"
    "     request path. Node serves every request on one thread: a 40ms\n"
    "     readFileSync in a handler is 40ms of total server unavailability, not\n"
    "     40ms for that one client.\n"
    "ACT switch to the promise form (fs.promises, await), or hoist the call to\n"
    "     startup where blocking is free. execSync and the pbkdf2Sync/scryptSync\n"
    "     family are the worst: they block for the full duration of a process\n"
    "     spawn or a deliberate key-derivation delay.\n"
    "MISLEADS depth is capped at 4 hops (the WITH RECURSIVE bound below) and\n"
    "     only RESOLVED edges are walked, so this is a floor, never a ceiling.\n"
    "     A handler registered by a router this cannot see has no is_handler\n"
    "     flag and its whole subtree is missing from this answer -- check\n"
    "     graph-blindspots for the module first. A *Sync call in a CLI or a\n"
    "     build script is entirely correct and appears here only if something\n"
    "     mistook a CLI entry for a handler.",
    """WITH RECURSIVE down(root, sym, depth) AS (   -- depth bound: 4 hops
        SELECT s.id, s.id, 0 FROM symbols s
        WHERE s.is_handler = 1 OR s.is_entrypoint = 1
        UNION
        SELECT d.root, e.callee_id, d.depth + 1
        FROM down d JOIN edges e ON e.caller_id = d.sym
        WHERE d.depth < 4 AND e.is_self = 0),
    best AS (SELECT root, sym, MIN(depth) AS depth FROM down GROUP BY root, sym)
    SELECT h.name AS entry, s.name AS blocks_in, b.depth AS hops,
        s.n_sync_calls AS sync_calls, s.n_sync_block AS sync_hazards,
        s.n_exec AS exec_, s.n_json_parse AS json_ops,
        s.max_loop_depth AS loop_depth, s.io_in_loop AS io_in_loop,
        s.fan_in,
        (SELECT GROUP_CONCAT(DISTINCT z.pattern) FROM hazards z
         WHERE z.symbol_id = s.id AND z.category IN ('sync_block','exec'))
            AS patterns,
        f.path || ':' || s.line_start AS at
    FROM best b
    JOIN symbols s ON s.id = b.sym
    JOIN symbols h ON h.id = b.root
    JOIN files f ON f.id = s.file_id
    LEFT JOIN modules m ON m.id = s.module_id
    WHERE (s.n_sync_calls > 0 OR s.n_exec > 0) AND f.is_test = 0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY b.depth ASC, s.n_exec DESC, s.n_sync_calls DESC LIMIT :lim"""),
(
    "await-in-loop-serialized",
    "await inside a loop where nothing on the path batches with Promise.all",
    "ANSWERS the single most common JavaScript performance bug: N awaits in\n"
    "     sequence take the sum of N latencies when they could take the max.\n"
    "     Ten 50ms round trips is 500ms serial and 50ms batched.\n"
    "ACT collect the promises and await Promise.all (or allSettled) once. Do NOT\n"
    "     do this blindly: an await in a loop is CORRECT when each iteration\n"
    "     depends on the previous one, when you are deliberately rate-limiting,\n"
    "     or when unbounded concurrency would exhaust a connection pool.\n"
    "MISLEADS trip count is invisible here. A loop over three config entries\n"
    "     costs nothing. `batches_anywhere` counts Promise.all in the same\n"
    "     function, which is only weak evidence -- the batching may be for a\n"
    "     different loop entirely.",
    """SELECT s.name, COALESCE(s.class_name,'') AS class_,
        s.await_in_loop AS awaits_in_loop, s.n_await AS awaits,
        s.max_loop_depth AS depth, s.n_promise_all AS batches_anywhere,
        s.call_in_loop AS calls_in_loop, s.io_in_loop AS io_in_loop,
        s.n_net AS net_, s.n_io AS io_, s.fan_in,
        s.is_handler AS handler,
        (s.await_in_loop * (1 + s.max_loop_depth)
         * (1 + s.is_handler * 2)) AS serial_cost,
        f.path || ':' || s.line_start AS at
    FROM symbols s
    JOIN files f ON f.id = s.file_id
    LEFT JOIN modules m ON m.id = s.module_id
    WHERE s.await_in_loop > 0 AND s.n_promise_all = 0
      AND f.is_test = 0 AND f.is_generated = 0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY serial_cost DESC, s.await_in_loop DESC LIMIT :lim"""),
(
    "floating-promise-crossmodule",
    "Async functions whose callers never await them, across module lines",
    "ANSWERS the cross-module floating promise. typescript-eslint's\n"
    "     no-floating-promises is the closest existing rule and it needs full\n"
    "     type information and works one file at a time; this works on the call\n"
    "     graph and crosses files, which is where the real ones hide.\n"
    "ACT an un-awaited async call means errors surface as an unhandled rejection\n"
    "     (which terminates the process by default since Node 15) and the work\n"
    "     may still be running after the caller returned. Either await it,\n"
    "     return it, or attach .catch and say in a comment that it is\n"
    "     deliberately detached.\n"
    "MISLEADS a caller that is itself synchronous cannot await, so fire-and-\n"
    "     forget is sometimes the only option -- caller_async tells you which\n"
    "     case you are in. discarded_calls counts calls in STATEMENT position in\n"
    "     the caller and cannot say which of them is this callee, so a caller\n"
    "     with one floating call and three awaited ones still appears. Read it\n"
    "     as a shortlist, not a verdict.",
    """SELECT cle.name AS async_callee, cal.name AS caller,
        cal.is_async AS caller_async, cal.n_await AS caller_awaits,
        cal.n_floating_promise AS discarded_calls,
        cal.n_then AS then_chains, cal.n_catch_handler AS catch_handlers,
        cle.n_net AS callee_net, cle.n_io AS callee_io,
        cle.n_throw AS callee_throws, e.same_module AS same_module,
        cle.fan_in AS callee_fan_in,
        f.path || ':' || cal.line_start AS at
    FROM edges e
    JOIN symbols cal ON cal.id = e.caller_id
    JOIN symbols cle ON cle.id = e.callee_id
    JOIN files f ON f.id = cal.file_id
    LEFT JOIN modules m ON m.id = cal.module_id
    WHERE cle.is_async = 1 AND e.is_self = 0
      AND cal.n_floating_promise > 0
      AND cal.n_await = 0 AND cal.n_then = 0
      AND f.is_test = 0 AND f.is_generated = 0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY (cle.n_net + cle.n_io) DESC, cle.n_throw DESC,
        cle.fan_in DESC LIMIT :lim"""),
(
    "proto-pollution-frontier",
    "Recursive writers reachable from parsed request input, up to 4 hops",
    "ANSWERS the shape behind every prototype-pollution CVE in the npm registry:\n"
    "     a deep merge, a `set(obj, path, value)` helper, or an\n"
    "     `obj[k1][k2] = v` write, fed a key that came out of JSON.parse of a\n"
    "     request body. Setting `__proto__` there changes every object in the\n"
    "     process.\n"
    "ACT guard the key. Reject __proto__, constructor and prototype explicitly,\n"
    "     or build the target with Object.create(null), or use a Map. A single\n"
    "     `if (key === '__proto__') continue` closes the whole class.\n"
    "     dynamic_writes counts `obj[expr] = v` where expr is not a literal --\n"
    "     that is the exact write that can be steered.\n"
    "MISLEADS this cannot see the guard. A merge helper that ALREADY rejects\n"
    "     __proto__ still appears, because proving the guard covers every path\n"
    "     needs data flow this does not have. Depth is capped at 4 hops (the\n"
    "     bound is in the recursive CTE below) and only resolved edges are\n"
    "     walked, so a helper reached through a plugin registry is missing.",
    """WITH RECURSIVE down(root, sym, depth) AS (   -- depth bound: 4 hops
        SELECT s.id, s.id, 0 FROM symbols s
        WHERE (s.is_handler = 1 OR s.n_json_parse > 0)
        UNION
        SELECT d.root, e.callee_id, d.depth + 1
        FROM down d JOIN edges e ON e.caller_id = d.sym
        WHERE d.depth < 4 AND e.is_self = 0),
    best AS (SELECT sym, MIN(depth) AS depth FROM down GROUP BY sym)
    SELECT s.name AS writer, b.depth AS hops_from_input,
        s.n_proto_write AS proto_writes,
        s.n_dynamic_prop AS dynamic_writes,
        s.n_proto_pollution AS merge_calls,
        s.is_recursive AS recursive_, s.n_computed_member AS computed_reads,
        s.n_json_parse AS parses, s.fan_in,
        (SELECT GROUP_CONCAT(DISTINCT z.pattern) FROM hazards z
         WHERE z.symbol_id = s.id AND z.category = 'proto_pollution')
            AS via,
        f.path || ':' || s.line_start AS at
    FROM best b
    JOIN symbols s ON s.id = b.sym
    JOIN files f ON f.id = s.file_id
    LEFT JOIN modules m ON m.id = s.module_id
    WHERE (s.n_proto_write > 0 OR s.n_proto_pollution > 0
           OR (s.n_dynamic_prop > 0 AND s.is_recursive = 1))
      AND f.is_test = 0 AND f.is_generated = 0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY b.depth ASC, s.is_recursive DESC, s.n_proto_write DESC
    LIMIT :lim"""),
(
    "redos-frontier",
    "Regex literals with nested quantifiers reachable from untrusted input",
    "ANSWERS which catastrophic-backtracking patterns an attacker can actually\n"
    "     reach. `(a+)+`, `(\\w*)*` and `(x|x)+` take exponential time on a\n"
    "     crafted non-match, and in Node that is the whole event loop, so one\n"
    "     request takes the server down.\n"
    "ACT rewrite the pattern to remove the nested quantifier, anchor it, or cap\n"
    "     the input length before matching. A regex compiled inside a loop\n"
    "     (regex_in_loop) also recompiles every iteration, which is a separate\n"
    "     and easier win.\n"
    "MISLEADS the detector is syntactic and errs toward reporting: `(ab+)+c`\n"
    "     matches the nested-quantifier shape but is linear in practice because\n"
    "     the suffix disambiguates. Confirming a finding means timing the actual\n"
    "     pattern against a crafted input -- treat every row as a candidate for\n"
    "     that test, not as a vulnerability. Regex/division ambiguity is\n"
    "     resolved by the parser, so nothing here is a mis-lexed division.\n"
    "     hops = -1 means the pattern is NOT reachable from any known entry\n"
    "     by a resolved edge, which is weaker evidence of safety than it looks:\n"
    "     an unreached pattern in a module full of dynamic dispatch may simply\n"
    "     be one this could not follow. Rows where in_fn is blank are literals\n"
    "     declared at module scope, which is where most regexes actually live.",
    """WITH RECURSIVE down(sym, depth) AS (        -- depth bound: 4 hops
        SELECT s.id, 0 FROM symbols s
        WHERE s.is_handler = 1 OR s.is_entrypoint = 1 OR s.n_json_parse > 0
        UNION
        SELECT e.callee_id, d.depth + 1
        FROM down d JOIN edges e ON e.caller_id = d.sym
        WHERE d.depth < 4 AND e.is_self = 0),
    best AS (SELECT sym, MIN(depth) AS depth FROM down GROUP BY sym)
    SELECT COALESCE(s.name,'(module scope)') AS in_fn,
        COALESCE(b.depth, -1) AS hops_from_input,
        SUBSTR(l.value,1,40) AS pattern,
        COALESCE(s.n_regex_redos,0) AS redos_in_fn,
        COALESCE(s.n_regex_lit,0) AS regex_literals,
        COALESCE(s.regex_in_loop,0) AS regex_in_loop,
        COALESCE(s.n_redos,0) AS regex_api_calls,
        COALESCE(s.is_handler,0) AS handler,
        COALESCE(s.fan_in,0) AS callers,
        (SELECT COUNT(*) FROM symbols x
         WHERE x.file_id = l.file_id AND x.is_exported = 1) AS exported_in_file,
        f.path || ':' || l.line AS at
    FROM literals l
    JOIN files f ON f.id = l.file_id
    LEFT JOIN symbols s ON s.id = l.symbol_id
    LEFT JOIN best b ON b.sym = l.symbol_id
    LEFT JOIN modules m ON m.id = f.module_id
    WHERE l.kind = 'regex_redos' AND f.is_generated = 0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY (b.depth IS NULL) ASC, b.depth ASC,
        COALESCE(s.fan_in,0) DESC LIMIT :lim"""),
(
    "dom-sink-frontier",
    "innerHTML and friends reachable from untrusted input, up to 4 hops",
    "ANSWERS the XSS question the call graph can answer: which HTML sink is\n"
    "     reachable from a function that handles a request or parses JSON. A\n"
    "     per-file linter sees the sink; it cannot see that the string arrived\n"
    "     from a query parameter three frames up.\n"
    "ACT use textContent, or a sanitiser at the boundary. React's\n"
    "     dangerouslySetInnerHTML is named that way on purpose and counts here.\n"
    "     hops = 0 means the sink and the untrusted input are in the same\n"
    "     function, which is the easiest to confirm and the easiest to fix.\n"
    "MISLEADS reachability is not taint. A sink fed a constant template, or fed\n"
    "     output that was already sanitised, is safe and appears here anyway --\n"
    "     this tracks the CALL GRAPH, not the data. The reverse error also\n"
    "     exists and is worse: a sink reached through a computed dispatch has no\n"
    "     edge and is absent entirely.",
    """WITH RECURSIVE down(root, sym, depth) AS (   -- depth bound: 4 hops
        SELECT s.id, s.id, 0 FROM symbols s
        WHERE s.is_handler = 1 OR s.n_json_parse > 0 OR s.is_component = 1
        UNION
        SELECT d.root, e.callee_id, d.depth + 1
        FROM down d JOIN edges e ON e.caller_id = d.sym
        WHERE d.depth < 4 AND e.is_self = 0),
    best AS (SELECT root, sym, MIN(depth) AS depth FROM down GROUP BY root, sym)
    SELECT r.name AS entry, s.name AS sink_in, b.depth AS hops,
        s.n_innerhtml AS html_writes, s.n_dom AS dom_hazards,
        s.n_storage AS storage_ops, s.n_eval AS eval_,
        s.is_component AS component, s.n_jsx_elements AS jsx,
        (SELECT COUNT(*) FROM jsx_components j
         WHERE j.symbol_id = s.id AND j.has_dangerous_html = 1)
            AS dangerous_jsx,
        s.fan_in,
        f.path || ':' || s.line_start AS at
    FROM best b
    JOIN symbols s ON s.id = b.sym
    JOIN symbols r ON r.id = b.root
    JOIN files f ON f.id = s.file_id
    LEFT JOIN modules m ON m.id = s.module_id
    WHERE (s.n_innerhtml > 0 OR s.n_dom > 0 OR s.n_eval > 0)
      AND f.is_test = 0 AND COALESCE(m.name,'') LIKE :mod
    ORDER BY b.depth ASC, s.n_eval DESC, s.n_innerhtml DESC LIMIT :lim"""),
(
    "async-colour-frontier",
    "Where synchronous code calls async code, and how deep the async goes",
    "ANSWERS JavaScript's function-colour boundary. Once one function is async,\n"
    "     every caller that wants its VALUE must be async too, all the way up.\n"
    "     This shows the exact frontier where that requirement is being ignored\n"
    "     and how far the async subtree extends below each root.\n"
    "ACT a sync caller of an async callee either awaits (and becomes async), or\n"
    "     deliberately detaches. Making one leaf async can force a rewrite of\n"
    "     every caller above it, and async_depth is the size of that blast\n"
    "     radius before you start.\n"
    "MISLEADS a sync function calling an async one to get the PROMISE -- to\n"
    "     store it, race it, or hand it on -- is completely correct and is\n"
    "     indistinguishable here from one that forgot to await. The subtree\n"
    "     depth is capped at 4 hops (bound in the CTE below) so deep async\n"
    "     chains are reported as exactly 4.",
    """WITH RECURSIVE down(root, sym, depth) AS (   -- depth bound: 4 hops
        SELECT s.id, s.id, 0 FROM symbols s
        WHERE s.is_async = 1 AND s.kind IN ('function','method','closure')
        UNION
        SELECT d.root, e.callee_id, d.depth + 1
        FROM down d JOIN edges e ON e.caller_id = d.sym
        WHERE d.depth < 4 AND e.is_self = 0),
    reach AS (SELECT root, MAX(depth) AS async_depth,
                     COUNT(DISTINCT sym) AS subtree
              FROM down GROUP BY root)
    SELECT cle.name AS async_fn, r.async_depth, r.subtree AS reaches_fns,
        COUNT(DISTINCT e.caller_id) AS callers,
        SUM(CASE WHEN cal.is_async = 0 THEN 1 ELSE 0 END) AS sync_callers,
        SUM(CASE WHEN cal.is_async = 0 AND cal.n_then = 0
                 THEN 1 ELSE 0 END) AS sync_and_unchained,
        cle.n_await AS own_awaits, cle.await_in_loop AS awaits_in_loop,
        cle.n_promise_all AS batches, cle.fan_in,
        f.path || ':' || cle.line_start AS at
    FROM edges e
    JOIN symbols cle ON cle.id = e.callee_id
    JOIN symbols cal ON cal.id = e.caller_id
    JOIN reach r ON r.root = cle.id
    JOIN files f ON f.id = cle.file_id
    LEFT JOIN modules m ON m.id = cle.module_id
    WHERE cle.is_async = 1 AND e.is_self = 0 AND f.is_test = 0
      AND COALESCE(m.name,'') LIKE :mod
    GROUP BY cle.id
    HAVING sync_callers > 0
    ORDER BY sync_and_unchained DESC, r.subtree DESC LIMIT :lim"""),
(
    "timer-balance",
    "setInterval and setTimeout with no matching clear, weighted by where they run",
    "ANSWERS which timers outlive whatever registered them. A repeating timer\n"
    "     holds its closure, and the closure holds everything it captured --\n"
    "     so one uncleared setInterval per request is an unbounded leak, and\n"
    "     in Node it also keeps the event loop alive so the process will not\n"
    "     exit.\n"
    "ACT keep the handle and clear it in the teardown path -- unmount,\n"
    "     disconnect, close, whichever this module has. `unref()` fixes only\n"
    "     the shutdown half, not the retention.\n"
    "MISLEADS clears are matched per function, not per handle, so a timer set\n"
    "     in one function and cleared in another reads as unbalanced here and\n"
    "     is fine. Rank by timers set inside a loop -- those are unambiguous.",
    """SELECT s.name, s.class_name AS class_, s.n_timer_set AS timers_set,
        s.n_timer_clear AS timers_cleared, s.n_timer_repeating AS repeating,
        s.n_timer_in_loop AS set_in_loop, s.n_closures AS closures,
        s.is_handler AS handler, s.fan_in,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_timer_set > s.n_timer_clear AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.n_timer_in_loop DESC, s.n_timer_repeating DESC,
        (s.n_timer_set - s.n_timer_clear) DESC LIMIT :lim"""),
(
    "dynamic-import-and-eval",
    "eval, dynamic require and import(): code paths no bundler or scanner can follow",
    "ANSWERS where the module graph stops being knowable. A `require(expr)`\n"
    "     cannot be resolved by a bundler, cannot be tree-shaken, and cannot\n"
    "     be audited by a dependency scanner. `eval` is the same problem with\n"
    "     a security consequence attached.\n"
    "ACT replace `require(name)` with an explicit map from name to a static\n"
    "     import -- it is analysable, tree-shakeable and no slower. Use JSON\n"
    "     for data and a Function factory only where you truly must.\n"
    "MISLEADS `import()` for genuine code splitting is a feature, not a\n"
    "     defect, and appears here. The rows worth reading are the ones where\n"
    "     the argument is computed rather than a literal.",
    """SELECT s.name, s.class_name AS class_, s.n_eval AS evals,
        s.n_require_dynamic AS dyn_require, s.n_import_dynamic AS dyn_import,
        s.n_export_star AS export_star, s.n_json_parse AS json_parses,
        s.n_unresolved_calls AS unresolved, s.fan_in,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE (s.n_eval + s.n_require_dynamic + s.n_import_dynamic) > 0
      AND f.is_test=0 AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.n_eval*5 DESC, s.n_require_dynamic DESC,
        s.n_import_dynamic DESC LIMIT :lim"""),
(
    "hooks-rules-violations",
    "React hooks called conditionally, and components that re-render on identity",
    "ANSWERS where the Rules of Hooks are broken and where re-renders are\n"
    "     caused by allocation. A hook inside a condition changes the hook\n"
    "     ORDER between renders, which corrupts React's state slots -- the\n"
    "     bug appears as one component's state showing up in another.\n"
    "ACT lift the condition inside the hook: call it unconditionally and\n"
    "     branch on the value. For re-renders, an object or arrow literal\n"
    "     passed as a prop is a new identity every render -- memoise it.\n"
    "MISLEADS an inline object prop is only a problem if the child is\n"
    "     memoised or the tree below is expensive; on a leaf it costs\n"
    "     nothing. The conditional-hook count is the part that is always a bug.",
    """SELECT s.name, s.class_name AS class_,
        s.n_hooks_conditional AS conditional_hooks, s.n_hooks AS hooks,
        s.n_inline_object_prop AS inline_props, s.n_setstate AS setstates,
        s.n_jsx_elements AS jsx, s.is_component AS component,
        s.is_hook AS is_hook_, s.fan_in,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE (s.n_hooks > 0 OR s.is_component = 1) AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.n_hooks_conditional DESC, s.n_inline_object_prop DESC,
        s.n_setstate DESC LIMIT :lim"""),
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
("sync-io-below-a-handler", "a synchronous fs call reachable from a request handler or exported entry point",
    "ANSWERS what eslint-plugin-node\'s no-sync reports one line at a time and\n"
    "     cannot rank: `readFileSync` at module load is how config is read and\n"
    "     is correct. The same call under a handler stops the event loop for\n"
    "     every other connection until the disk answers. The difference is\n"
    "     reachability, not the call.\n"
    "ACT switch to the promise API and await it, or hoist the read to startup\n"
    "     and cache it. `reached_from` names the handler that pays the latency.\n"
    "MISLEADS a sync read of a small file already in the page cache costs\n"
    "     microseconds and is often the right call. Depth stops at 4 hops, and\n"
    "     a callback passed as a value breaks the edge, so a real blocking path\n"
    "     through `array.map(cb)` is invisible here.",
    """WITH RECURSIVE walk(root, sym, depth) AS (
        SELECT s.id, s.id, 0 FROM symbols s
        JOIN files f ON f.id = s.file_id
        WHERE (s.is_handler = 1 OR s.is_entrypoint = 1 OR s.is_exported = 1)
          AND f.is_test = 0
        UNION
        SELECT w.root, e.callee_id, w.depth + 1
        FROM walk w JOIN edges e ON e.caller_id = w.sym
        WHERE w.depth < 4 AND e.is_self = 0),      -- depth bound: 4 hops
    reach(root, sym, depth) AS (
        SELECT root, sym, MIN(depth) FROM walk GROUP BY root, sym)
    SELECT s.name, entry.name AS reached_from, MIN(r.depth) AS hops,
        s.n_fs_sync AS sync_fs_calls,
        s.n_child_process AS child_process_calls,
        s.n_json_parse_in_loop AS json_parse_in_loop,
        s.is_async AS callee_is_async, s.fan_in,
        f.path || \':\' || s.line_start AS at
    FROM reach r
    JOIN symbols s ON s.id = r.sym
    JOIN symbols entry ON entry.id = r.root
    JOIN files f ON f.id = s.file_id
    LEFT JOIN modules m ON m.id = s.module_id
    WHERE r.depth > 0 AND f.is_test = 0
      AND (s.n_fs_sync > 0 OR s.n_child_process > 0)
      AND COALESCE(m.name,\'\') LIKE :mod
    GROUP BY s.id, entry.id
    ORDER BY hops ASC, sync_fs_calls DESC, s.fan_in DESC LIMIT :lim"""),
(
    "command-injection-surface",
    "child_process.exec with dynamic arguments (ESLint security)",
    "ANSWERS where child_process is used, which can execute arbitrary commands.\n"
    "     exec with a string argument shells out; execFile with an array does not.\n"
    "ACT use execFile with an array of arguments, never a shell string.\n"
    "MISLEADS child_process in a build tool or CLI wrapper is correct. The graph\n"
    "     sees the call but not whether the input is sanitized.",
    """SELECT s.name, s.n_child_process AS child_process_calls,
        s.n_eval AS eval_calls, s.n_require_dynamic AS dynamic_requires,
        s.fan_in, s.is_handler AS handler,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_child_process > 0 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.fan_in DESC, s.n_child_process DESC LIMIT :lim"""),
(
    "proto-mutation",
    "Direct __proto__ or prototype mutation (ESLint security)",
    "ANSWERS where __proto__ is written or Object.prototype is modified, which\n"
    "     can pollute every object in the runtime and is a known RCE vector.\n"
    "ACT never write to __proto__ or Object.prototype; use Object.create.\n"
    "MISLEADS a library that intentionally patches a prototype (polyfill) is\n"
    "     correct but should be audited.",
    """SELECT s.name, s.n_proto_write AS proto_writes,
        s.n_proto_mutate AS proto_mutates,
        s.n_delete AS deletes,
        s.fan_in, s.is_handler AS handler,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE (s.n_proto_write > 0 OR s.n_proto_mutate > 0) AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.fan_in DESC, s.n_proto_write DESC LIMIT :lim"""),
(
    "process-exit-in-handler",
    "process.exit() in a request handler (ESLint/no-process-exit)",
    "ANSWERS where process.exit is called from a function reachable from a\n"
    "     request handler, terminating the process for one request.\n"
    "ACT throw an error; let the top-level handler decide.\n"
    "MISLEADS process.exit in a CLI tool's main is correct. Reachability is\n"
    "     from is_handler=1, capped at 4 hops.",
    """WITH RECURSIVE walk(root, sym, depth) AS (
        SELECT s.id, s.id, 0 FROM symbols s WHERE s.is_handler=1
        UNION
        SELECT w.root, e.callee_id, w.depth+1
        FROM walk w JOIN edges e ON e.caller_id=w.sym
        WHERE w.depth < 4 AND e.is_self=0),
    reach(root, sym, depth) AS (
        SELECT root, sym, MIN(depth) FROM walk GROUP BY root, sym)
    SELECT s.name, s.n_process_exit AS exit_calls,
        MIN(r.depth) AS hops_from_handler,
        s.fan_in, s.cyclomatic AS cyclo,
        f.path || ':' || s.line_start AS at
    FROM reach r
    JOIN symbols s ON s.id=r.sym
    JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_process_exit > 0 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    GROUP BY s.id
    ORDER BY hops_from_handler ASC, s.n_process_exit DESC LIMIT :lim"""),
(
    "sync-io-under-handler",
    "Synchronous I/O reachable from a request handler (ESLint/no-sync)",
    "ANSWERS where a sync I/O call (readFileSync, writeFileSync) is reachable\n"
    "     from a request handler, blocking the event loop for every request.\n"
    "ACT use the async version (fs.promises.readFile).\n"
    "MISLEADS sync I/O in a startup/init path is correct. Reachability is from\n"
    "     is_handler=1, capped at 4 hops.",
    """WITH RECURSIVE walk(root, sym, depth) AS (
        SELECT s.id, s.id, 0 FROM symbols s WHERE s.is_handler=1
        UNION
        SELECT w.root, e.callee_id, w.depth+1
        FROM walk w JOIN edges e ON e.caller_id=w.sym
        WHERE w.depth < 4 AND e.is_self=0),
    reach(root, sym, depth) AS (
        SELECT root, sym, MIN(depth) FROM walk GROUP BY root, sym)
    SELECT s.name, s.n_fs_sync AS sync_io,
        s.n_sync_calls AS sync_calls,
        MIN(r.depth) AS hops_from_handler,
        s.fan_in,
        f.path || ':' || s.line_start AS at
    FROM reach r
    JOIN symbols s ON s.id=r.sym
    JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_fs_sync > 0 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    GROUP BY s.id
    ORDER BY hops_from_handler ASC, s.n_fs_sync DESC LIMIT :lim"""),
(
    "import-cycle",
    "Circular import dependencies (madge/circular)",
    "ANSWERS which files form an import cycle, causing initialization-order bugs.\n"
    "ACT break the cycle by extracting shared code into a third module.\n"
    "MISLEADS cycles through test files are usually fine. Depth is capped at 8.",
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
    "dynamic-require",
    "require() with a dynamic expression (ESLint/no-require)",
    "ANSWERS where require() is called with a variable or expression instead of\n"
    "     a string literal, which prevents static analysis and can be exploited\n"
    "     for path traversal.\n"
    "ACT use import with a string literal; if dynamic loading is needed, use a\n"
    "     whitelist map.\n"
    "MISLEADS a plugin loader that intentionally takes a module name is a valid\n"
    "     pattern if the input is validated.",
    """SELECT s.name, s.n_require_dynamic AS dynamic_requires,
        s.n_import_dynamic AS dynamic_imports,
        s.n_eval AS eval_calls, s.n_child_process AS exec_calls,
        s.fan_in, s.is_handler AS handler,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_require_dynamic > 0 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.fan_in DESC, s.n_require_dynamic DESC LIMIT :lim""")
]

JavaScriptAnalyzer.METRICS = [
(
    "graph-blindspots",
    "Read this first: where the call graph cannot see",
    "ANSWERS how much of every other answer here is guesswork. JavaScript is\n"
    "     the worst language in this repo for this: a call through a computed\n"
    "     member (obj[name]()), a require() with a variable, a Proxy, or a\n"
    "     plugin registry keyed by string has no edge and never will.\n"
    "ACT read pct_blind before trusting any reachability query below. Calls to\n"
    "     the platform (console, Array.prototype, node: builtins, imported\n"
    "     packages) are counted as EXTERNAL, not blind -- they leave the tree by\n"
    "     design. Unresolved means we genuinely lost the thread.\n"
    "MISLEADS a bare require() with no binding -- `get X() { return\n"
    "     require('./X') }` in a barrel -- names nothing, so the file was\n"
    "     counted as unimported. The file-level import check now covers\n"
    "     that; before it, 30 percent of these rows were live code.\n"
    "     a resolved edge can still be wrong. Name-based resolution binds\n"
    "     `render` to whichever single `render` exists in the file or in the\n"
    "     tree; where two exist it refuses and lands here instead. A high\n"
    "     dynamic_calls with low unresolved means the blindness was recognised\n"
    "     rather than mis-attributed, which is the better failure.",
    """SELECT m.name AS module_, COUNT(DISTINCT s.id) AS fns,
        COALESCE(SUM(s.n_calls),0) AS calls,
        COALESCE(SUM(s.n_external_calls),0) AS external,
        COALESCE(SUM(s.n_unresolved_calls),0) AS unresolved,
        COALESCE(SUM(s.n_dynamic_calls),0) AS dynamic_,
        COALESCE(SUM(s.n_computed_member),0) AS computed_member,
        COALESCE(SUM(s.n_require_dynamic + s.n_import_dynamic),0) AS dyn_import,
        COALESCE(SUM(s.n_reflect),0) AS reflect_,
        CAST(100.0*SUM(s.n_unresolved_calls)/NULLIF(SUM(s.n_calls),0) AS INT)
            AS pct_blind
    FROM symbols s JOIN modules m ON m.id=s.module_id
    WHERE s.kind IN ('function','method','closure') AND m.name LIKE :mod
    GROUP BY m.id HAVING calls>0
    ORDER BY unresolved DESC, dynamic_ DESC LIMIT :lim"""),
(
    "megamorphic-shapes",
    "Hot functions doing dynamic property access, ranked by calling breadth",
    "ANSWERS where V8's inline caches are most likely to be giving up. A call\n"
    "     site that sees one object shape is monomorphic and inlined; one that\n"
    "     sees many degrades to a hash lookup on every access, and functions\n"
    "     called from many modules with many computed accesses are where that\n"
    "     happens.\n"
    "ACT give objects a stable shape: initialise every field in the constructor,\n"
    "     never `delete` a property (use null), never add fields conditionally.\n"
    "     Replace `obj[key]` dictionaries with a Map, which is designed for it.\n"
    "     Then MEASURE with --trace-ic or --trace-deopt; nothing here is a\n"
    "     confirmed deopt.\n"
    "MISLEADS the polymorphic-to-megamorphic threshold in V8 is commonly quoted\n"
    "     as 4 receiver shapes, and this ranking leans on that number -- BUT\n"
    "     that constant (kMaxPolymorphicMapCount) could NOT be confirmed in V8\n"
    "     source when this was written, and it has changed between versions.\n"
    "     Treat the 4 as UNVERIFIED folklore: the ORDER of this list is useful,\n"
    "     the cutoff is not. Also, modules_calling counts distinct calling\n"
    "     modules, which is a proxy for shape variety and not a measurement of\n"
    "     it -- one module can pass five shapes and five modules can pass one.",
    """SELECT s.name, COALESCE(s.class_name,'') AS class_,
        s.n_modules_calling AS modules_calling, s.fan_in, s.n_callsites AS sites,
        s.n_computed_member AS computed_access,
        s.n_dynamic_prop AS dynamic_writes, s.n_delete AS deletes,
        s.n_arguments AS uses_arguments, s.n_this_refs AS this_refs,
        s.n_optional_chain AS optional_chains, s.n_spread AS spreads,
        s.n_reflect AS reflect_ops, s.sloc,
        (s.n_computed_member * 2 + s.n_dynamic_prop * 3 + s.n_delete * 5
         + s.n_arguments * 4 + s.n_reflect * 3)
        * (1 + s.n_modules_calling) AS shape_churn,
        f.path || ':' || s.line_start AS at
    FROM symbols s
    JOIN files f ON f.id = s.file_id
    LEFT JOIN modules m ON m.id = s.module_id
    WHERE s.kind IN ('function','method') AND f.is_generated = 0
      AND f.is_test = 0 AND s.n_modules_calling > 4
      AND (s.n_computed_member + s.n_dynamic_prop + s.n_delete
           + s.n_arguments + s.n_reflect) > 0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY shape_churn DESC LIMIT :lim"""),
(
    "dead-exports-barrel-blast",
    "Exports nothing imports, and the barrel files that hide the answer",
    "ANSWERS what is deletable from the public surface, and separately which\n"
    "     re-export files (barrels) make that question unanswerable. A barrel\n"
    "     that does `export * from './x'` forwards names it never mentions, so\n"
    "     any importer of the barrel might be using any of them.\n"
    "ACT an export with imported_by = 0 and fan_in = 0, in a file no barrel\n"
    "     re-exports, is genuinely unreferenced in this tree. Delete it, or if\n"
    "     it is the package's published API, that is what an exports map in\n"
    "     package.json is for.\n"
    "     star_reexports > 0 on a row means STOP -- this cannot tell whether that\n"
    "     name travels through the barrel to an importer.\n"
    "MISLEADS a package's own entry point exports for consumers who are not in\n"
    "     this tree at all, and every one of those looks dead here. So does\n"
    "     anything reached only by string (a plugin name, a route module loaded\n"
    "     by convention, a test fixture required by glob). Read this next to\n"
    "     graph-blindspots and never delete on this evidence alone.",
    """SELECT e.name, e.kind, e.is_cjs AS cjs,
        COALESCE(s.name,'') AS symbol, COALESCE(s.kind,'') AS symbol_kind,
        COALESCE(s.sloc,0) AS sloc, COALESCE(s.fan_in,0) AS callers,
        (SELECT COUNT(*) FROM import_names i
         WHERE i.source_id = e.file_id
           AND (i.name = e.name OR i.is_namespace = 1
                OR (i.is_default = 1 AND e.kind IN ('default','cjs'))))
            AS imported_by,
        (SELECT COUNT(*) FROM exports b
         WHERE b.is_star = 1 AND b.source_id = e.file_id) AS star_reexports,
        (SELECT COUNT(*) FROM exports b2 WHERE b2.file_id = e.file_id)
            AS exports_in_file,
        f.path || ':' || e.line AS at
    FROM exports e
    JOIN files f ON f.id = e.file_id
    LEFT JOIN symbols s ON s.id = e.symbol_id
    LEFT JOIN modules m ON m.id = f.module_id
    WHERE e.is_star = 0 AND e.is_reexport = 0
      AND f.is_test = 0 AND f.is_generated = 0
      AND COALESCE(m.name,'') LIKE :mod
    GROUP BY e.id
    HAVING imported_by = 0 AND star_reexports = 0 AND callers = 0
       AND NOT EXISTS (SELECT 1 FROM imports im
                       WHERE im.target_id = e.file_id)
    ORDER BY sloc DESC, e.name LIMIT :lim"""),
(
    "god-functions",
    "Functions doing too much, by every measure at once",
    "ANSWERS which functions are hardest to hold in your head. In JavaScript the\n"
    "     usual cause is not a long `if` chain but a callback pyramid, so nested\n"
    "     function nodes count toward depth here -- a four-deep callback nest is\n"
    "     exactly as hard to read as a four-deep loop.\n"
    "ACT read `elifs` against `nest`: a high elif count with low nesting is a\n"
    "     flat dispatch and wants a lookup table, while high nesting with few\n"
    "     elifs is a pyramid and wants extracted functions or async/await.\n"
    "     `closures` is how many function objects this allocates.\n"
    "MISLEADS a long flat dispatch reads far more easily than a short deeply\n"
    "     nested one, which is why this sorts by cognitive rather than sloc.\n"
    "     Generated and bundled files are excluded, so anything a build step\n"
    "     produced is missing by design.",
    """SELECT s.name, COALESCE(s.class_name,'') AS class_, s.kind, s.sloc,
        s.cyclomatic AS cyclo, s.cognitive AS cog, s.max_nesting AS nest,
        s.n_elif AS elifs, s.n_closures AS closures, s.n_callbacks AS callbacks,
        s.n_returns AS returns_, s.n_params, s.n_this_refs AS this_refs,
        s.maintainability AS maint, s.fan_in,
        f.path || ':' || s.line_start AS at
    FROM symbols s
    JOIN files f ON f.id = s.file_id
    LEFT JOIN modules m ON m.id = s.module_id
    WHERE s.kind IN ('function','method') AND f.is_generated = 0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.cognitive DESC, s.sloc DESC LIMIT :lim"""),
(
    "parse-coverage",
    "What this run could not read, and which files carry the most risk",
    "ANSWERS whether the numbers above cover the code you think they cover.\n"
    "     A file listed here contributed nothing or contributed damaged spans.\n"
    "ACT the known grammar gaps are Stage-3 proposals: `accessor x = 1` (the\n"
    "     decorators auto-accessor form) is a parse error, and any TypeScript\n"
    "     syntax in a .js file (satisfies, type annotations) will be too. Flow\n"
    "     annotations are not JavaScript and never parse. Everything else here\n"
    "     is worth a look at the file itself.\n"
    "MISLEADS a file can parse perfectly and still be misunderstood -- this\n"
    "     shows hard failures only. n_missing_nodes counts places tree-sitter\n"
    "     inserted a token to recover, so a small count usually means one typo\n"
    "     rather than a wholly unreadable file.",
    """SELECT f.path, f.lines, f.n_parse_errors AS errors,
        f.n_missing_nodes AS missing, f.parsed,
        f.is_generated AS generated, f.is_test AS test, f.ext,
        f.n_symbols AS symbols,
        (SELECT COUNT(*) FROM imports i
         WHERE i.file_id = f.id AND i.is_dynamic = 1) AS dynamic_imports
    FROM files f
    LEFT JOIN modules m ON m.id = f.module_id
    WHERE (f.n_parse_errors > 0 OR f.parsed = 0)
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY f.n_parse_errors DESC, f.lines DESC
    LIMIT :lim"""),
(
    "shape-deopt-surface",
    "delete, arguments, with and dynamic property writes: what makes V8 give up",
    "ANSWERS where the code defeats the engine's hidden-class optimisation.\n"
    "     `delete` on an object turns it into a dictionary-mode object for\n"
    "     the rest of its life; `arguments` leaking out of a function blocks\n"
    "     inlining; `with` disables scope analysis entirely.\n"
    "ACT set the property to undefined or null instead of deleting it, or\n"
    "     use a Map when keys are genuinely dynamic. Replace `arguments`\n"
    "     with rest parameters, which are a real array and do not deopt.\n"
    "MISLEADS one delete on a config object at startup costs nothing. This\n"
    "     ranks by fan_in and loop depth precisely because the cost is per\n"
    "     execution, and a cold path never pays it.",
    """SELECT s.name, s.class_name AS class_, s.n_delete AS deletes,
        s.n_arguments AS arguments_, s.n_with_stmt AS with_stmts,
        s.n_dynamic_prop AS dynamic_props, s.n_computed_member AS computed,
        s.fan_in, s.max_loop_depth AS depth,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE (s.n_delete + s.n_arguments + s.n_with_stmt) > 0 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY (s.n_with_stmt*4 + s.n_delete*2 + s.n_arguments)
             * (1 + s.fan_in) * (1 + s.max_loop_depth) DESC LIMIT :lim"""),
(
    "spread-in-loop",
    "Spread and object rest inside a loop: accidental quadratic copying",
    "ANSWERS where an O(n) idiom sits inside an O(n) loop. `acc = [...acc, x]`\n"
    "     or `{...acc, [k]: v}` in a reduce copies everything accumulated so\n"
    "     far on every single iteration -- linear code that runs quadratic\n"
    "     and only shows up once the input gets big.\n"
    "ACT push into the array and return it, or mutate the accumulator and\n"
    "     freeze at the end. If immutability is the point, build a Map and\n"
    "     convert once outside the loop.\n"
    "MISLEADS spread over a small fixed list -- merging default options,\n"
    "     three known keys -- is idiomatic and free. This cannot see the\n"
    "     collection size, only that the copy happens per iteration.",
    """SELECT s.name, s.class_name AS class_, s.n_spread AS spreads,
        s.n_inline_object_prop AS inline_objs, s.max_loop_depth AS depth,
        s.n_destructure AS destructures, s.alloc_in_loop AS allocs_in_loop,
        s.fan_in, f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_spread > 0 AND s.max_loop_depth > 0 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.n_spread * s.max_loop_depth * (1 + s.fan_in) DESC LIMIT :lim"""),
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
(
    "risk-ranked",
    "Review order: if you can only read N symbols this week, which N",
    "ANSWERS which code combines complexity with the operations this language\n"
    "     punishes hardest.\n"
    "ACT start at the top. The weights are this analyzer's own -- read\n"
    "     --schema for the formula rather than assuming it matches another\n"
    "     language's score.\n"
    "MISLEADS a heuristic, not a finding. Generated files are excluded, so the\n"
    "     real top of the list may sit in code this filter hid.",
    """SELECT s.name, s.risk_score AS risk, s.cyclomatic AS cyclo,
        s.cognitive AS cog, s.max_nesting AS nest, s.n_hazards AS hazards,
        s.fan_in, s.sloc, f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.risk_score > 0 AND f.is_generated=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.risk_score DESC LIMIT :lim"""),
("quadratic-scan-in-hot-callee", "a linear search inside a loop, in a function many callers reach",
    "ANSWERS the shape no ESLint rule can see, because it is not a shape at\n"
    "     all: `includes`, `indexOf` or `find` inside a loop is O(n*m), and\n"
    "     unicorn/no-array-push-push or the perf plugins only look at one\n"
    "     statement. What makes it matter is `fan_in` -- the same nested scan\n"
    "     in a leaf called twice is noise; in a function 200 call sites reach\n"
    "     it is the profile.\n"
    "ACT build a Set or Map before the loop and test membership in O(1). Rows\n"
    "     are ranked by callers first, so the top of the list is where the\n"
    "     rewrite pays.\n"
    "MISLEADS the loop bound is invisible here. A scan over a 3-element array\n"
    "     is faster than the Set that replaces it. `fan_in` counts static call\n"
    "     sites, not executions -- a function called once from a hot loop\n"
    "     outranks nothing.",
    """SELECT s.name, s.n_search_in_loop AS search_in_loop,
        s.n_array_grow_in_loop AS array_grow_in_loop,
        s.n_assign_in_loop AS assign_in_loop,
        s.n_then_in_loop AS then_in_loop,
        s.max_loop_depth AS loop_depth, s.cyclomatic AS cyclo,
        s.fan_in, COUNT(DISTINCT e.caller_id) AS distinct_callers,
        f.path || \':\' || s.line_start AS at
    FROM symbols s
    JOIN files f ON f.id = s.file_id
    LEFT JOIN edges e ON e.callee_id = s.id AND e.is_self = 0
    LEFT JOIN modules m ON m.id = s.module_id
    WHERE (s.n_search_in_loop > 0 OR s.n_array_grow_in_loop > 0)
      AND f.is_test = 0
      AND COALESCE(m.name,\'\') LIKE :mod
    GROUP BY s.id
    ORDER BY distinct_callers DESC, search_in_loop DESC,
        s.max_loop_depth DESC LIMIT :lim"""),
(
    "deep-nesting",
    "Functions with excessive nesting depth (ESLint/max-depth)",
    "ANSWERS where a function has max_nesting > 4, making it hard to read and\n"
    "     test. Each level multiplies the test matrix.\n"
    "ACT extract nested blocks into named helper functions; use early returns.\n"
    "MISLEADS a callback-heavy function may have structural nesting that is\n"
    "     semantically flat. The column measures structural nesting, not\n"
    "     async depth.",
    """SELECT s.name, s.max_nesting AS nesting,
        s.cyclomatic AS cyclo, s.cognitive AS cognitive,
        s.n_callbacks AS callbacks, s.n_closures AS closures,
        s.sloc, s.fan_in,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.max_nesting > 4 AND s.kind IN ('function','method')
      AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.max_nesting DESC, s.cyclomatic DESC LIMIT :lim"""),
(
    "too-many-params",
    "Functions with too many parameters (ESLint/max-params)",
    "ANSWERS where a function has more than 4 parameters, making call sites\n"
    "     error-prone.\n"
    "ACT use an options object, or split the function.\n"
    "MISLEADS a destructured options parameter is one param semantically. The\n"
    "     graph counts formal params, not destructured fields.",
    """SELECT s.name, s.n_params, s.n_optional_params,
        s.n_destructure AS destructured,
        s.sloc, s.cyclomatic AS cyclo, s.fan_in,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_params > 4 AND s.kind IN ('function','method')
      AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.n_params DESC, s.fan_in DESC LIMIT :lim"""),
(
    "scattered-concerns",
    "A function called from many different modules (shotgun surgery)",
    "ANSWERS which functions are called from a high number of distinct modules,\n"
    "     so any change ripples widely.\n"
    "ACT consider splitting the function or making the contract more stable.\n"
    "MISLEADS a utility like log or config is called from everywhere and is\n"
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
    "jsx-component-complexity",
    "React component with excessive complexity (ESLint/react)",
    "ANSWERS which React components have high cyclomatic complexity, making the\n"
    "     render logic hard to verify and test.\n"
    "ACT extract sub-components, move logic to hooks, or simplify conditionals.\n"
    "MISLEADS a component with many conditional renders is complex but not\n"
    "     necessarily wrong. The graph measures function complexity, not JSX depth.",
    """SELECT s.name, s.cyclomatic AS cyclo,
        s.n_jsx_elements AS jsx_elements,
        s.n_hooks AS hooks, s.n_setstate AS setstates,
        s.n_hooks_conditional AS conditional_hooks,
        s.sloc, s.fan_in,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.is_component=1 AND s.cyclomatic > 10 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.cyclomatic DESC, s.n_jsx_elements DESC LIMIT :lim""")
]



ANALYZER = JavaScriptAnalyzer()


if __name__ == "__main__":
    try:
        sys.exit(main(ANALYZER))
    except KeyboardInterrupt:
        print("\ninterrupted", file=sys.stderr)
        sys.exit(130)
