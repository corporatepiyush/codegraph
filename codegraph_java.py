#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Piyush Katariya
#
# @author Piyush Katariya
"""codegraph_java.py -- parse a Java tree into a graph and query it.

Targets Java 25 (LTS, GA 2025-09-16). Parses with tree-sitter-java.

SpotBugs, Error Prone and the compiler already catch the single-method mistakes,
so this does not compete with them. What it adds is the shape no per-file
checker can see: which resource is opened in one class and closed in another,
which two functions take the same two locks in opposite orders, which reflective
call is reachable from a public entry point and therefore bounds your
`--add-opens` list and your native-image reflect-config.

Four Java facts this bakes in, because getting any of them wrong dates the tool:

* JEP 491 (JDK 24) REMOVED virtual-thread pinning by `synchronized` and by
  `Object.wait`, and removed `-Djdk.tracePinnedThreads` with it. On Java 24+ a
  `synchronized` block inside a virtual thread is a NON-FINDING and is not
  reported as one. What still pins is JNI and an FFM downcall, so the pinning
  query targets `java.lang.foreign`, `System.loadLibrary` and `native` methods
  reachable from a virtual-thread root -- and says in as many words that
  synchronized is excluded.
* A virtual thread dies with its task, so a ThreadLocal it set cannot leak.
  Only a POOLED carrier can leak one, which is why `is_pooled_executor_root` is
  a separate column from `is_executor_root` rather than a flag on it.
* Compact source files (JEP 512) have no class declaration at all. A file whose
  entire content is `void main() {}` parses to `program > method_declaration`,
  its `owner_type` is empty, and it is a real entry point. Nothing here requires
  a declaring type.
* `sealed`, `non-sealed`, `permits`, `record`, `yield`, `when` and `var` are
  CONTEXTUAL keywords and are legal identifiers. They are read from the grammar,
  never from a regex over the token.

One grammar limitation, recorded in `meta.grammar_note` so nobody has to read
this docstring to find it: tree-sitter-java 0.23.5 predates module import
declarations (JEP 511, final in 25), so `import module java.base;` parses as an
ERROR and raises `files.n_parse_errors` by one -- through no fault of the code
being analysed. Those imports are recovered by a text scan into
`jpms_directives` and the `parse-coverage` query says so.

Usage:
  python3 codegraph_java.py /path/to/repo --report
  python3 codegraph_java.py /path/to/repo --list
  python3 codegraph_java.py --deps"""
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
        #: (column, value, symbol_id) accumulated during parsing
        self._sym_updates: list[tuple[str, int, int]] = []

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
# lang_java.py
# codegraph_java.py -- parse a Java tree into a graph and query it.
#
# Targets Java 25 (LTS, GA 2025-09-16). Parses with tree-sitter-java.
#
# SpotBugs, Error Prone and the compiler already catch the single-method mistakes,
# so this does not compete with them. What it adds is the shape no per-file
# checker can see: which resource is opened in one class and closed in another,
# which two functions take the same two locks in opposite orders, which reflective
# call is reachable from a public entry point and therefore bounds your
# `--add-opens` list and your native-image reflect-config.
#
# Four Java facts this bakes in, because getting any of them wrong dates the tool:
#
# * JEP 491 (JDK 24) REMOVED virtual-thread pinning by `synchronized` and by
#   `Object.wait`, and removed `-Djdk.tracePinnedThreads` with it. On Java 24+ a
#   `synchronized` block inside a virtual thread is a NON-FINDING and is not
#   reported as one. What still pins is JNI and an FFM downcall, so the pinning
#   query targets `java.lang.foreign`, `System.loadLibrary` and `native` methods
#   reachable from a virtual-thread root -- and says in as many words that
#   synchronized is excluded.
# * A virtual thread dies with its task, so a ThreadLocal it set cannot leak.
#   Only a POOLED carrier can leak one, which is why `is_pooled_executor_root` is
#   a separate column from `is_executor_root` rather than a flag on it.
# * Compact source files (JEP 512) have no class declaration at all. A file whose
#   entire content is `void main() {}` parses to `program > method_declaration`,
#   its `owner_type` is empty, and it is a real entry point. Nothing here requires
#   a declaring type.
# * `sealed`, `non-sealed`, `permits`, `record`, `yield`, `when` and `var` are
#   CONTEXTUAL keywords and are legal identifiers. They are read from the grammar,
#   never from a regex over the token.
#
# One grammar limitation, recorded in `meta.grammar_note` so nobody has to read
# this docstring to find it: tree-sitter-java 0.23.5 predates module import
# declarations (JEP 511, final in 25), so `import module java.base;` parses as an
# ERROR and raises `files.n_parse_errors` by one -- through no fault of the code
# being analysed. Those imports are recovered by a text scan into
# `jpms_directives` and the `parse-coverage` query says so.
#
# Usage:
#   python3 codegraph_java.py /path/to/repo --report
#   python3 codegraph_java.py /path/to/repo --list
#   python3 codegraph_java.py --deps
# ==========================================================================

DEPS = DepSet(lang="java", deps=[
    TREE_SITTER,
    grammar("Java", "tree_sitter_java", "tree-sitter-java>=0.23",
            "0.23.5 (ABI 14) -- older than the other grammars here; the "
            "runtime accepts 13-15 so it loads, but it predates Java 25 "
            "module import declarations"),
])

GRAMMAR_NOTE = ("tree-sitter-java 0.23.5 (ABI 14, released 2024-12-21) predates "
                "Java 25 module import declarations (JEP 511); "
                "`import module X;` parses as an ERROR node and adds 1 to "
                "files.n_parse_errors per file that uses one")

HAZARD_CATEGORIES = (
    "reflection", "serialization", "jni", "exec", "io", "net", "sql", "crypto",
    "concurrency", "lock", "alloc", "boxing", "string", "resource", "unsafe",
    "control",
)

HAZARD_CALLS: dict[str, str] = {
    # -- reflection: the frontier that bounds --add-opens and reflect-config --
    "Class.forName": "reflection", "getDeclaredMethod": "reflection",
    "getDeclaredMethods": "reflection", "getDeclaredField": "reflection",
    "getDeclaredFields": "reflection", "getDeclaredConstructor": "reflection",
    "getMethod": "reflection", "getField": "reflection",
    "setAccessible": "reflection", "trySetAccessible": "reflection",
    "newInstance": "reflection", "invoke": "reflection",
    "Proxy.newProxyInstance": "reflection", "MethodHandles.lookup": "reflection",
    "MethodHandles.privateLookupIn": "reflection",
    "privateLookupIn": "reflection", "findVirtual": "reflection",
    "findStatic": "reflection", "findSpecial": "reflection",
    "unreflect": "reflection", "ServiceLoader.load": "reflection",
    "getContextClassLoader": "reflection", "getClassLoader": "reflection",
    "loadClass": "reflection", "defineClass": "reflection",
    "getAnnotation": "reflection", "isAnnotationPresent": "reflection",
    "getEnumConstants": "reflection", "getComponentType": "reflection",
    "Array.newInstance": "reflection",
    # -- serialization / JNDI: the deserialization sink surface -------------
    "new ObjectInputStream": "serialization", "readObject": "serialization",
    "readUnshared": "serialization", "readExternal": "serialization",
    "resolveClass": "serialization", "new XMLDecoder": "serialization",
    "SerializationUtils.deserialize": "serialization",
    "readValue": "serialization", "enableDefaultTyping": "serialization",
    "activateDefaultTyping": "serialization", "Yaml.load": "serialization",
    "new Yaml": "serialization", "fromXML": "serialization",
    "InitialContext.lookup": "serialization", "new InitialContext": "serialization",
    "new ObjectOutputStream": "serialization", "writeObject": "serialization",
    "readResolve": "serialization", "writeReplace": "serialization",
    # -- jni + FFM: what STILL pins a virtual thread after JEP 491 ----------
    "System.loadLibrary": "jni", "System.load": "jni",
    "Runtime.loadLibrary": "jni", "Linker.nativeLinker": "jni",
    "nativeLinker": "jni", "downcallHandle": "jni", "upcallStub": "jni",
    "SymbolLookup.libraryLookup": "jni", "libraryLookup": "jni",
    "loaderLookup": "jni", "Arena.ofConfined": "jni", "Arena.ofShared": "jni",
    "Arena.ofAuto": "jni", "Arena.global": "jni",
    "MemorySegment.ofAddress": "jni", "reinterpret": "jni",
    "allocateFrom": "jni", "MemoryLayout.structLayout": "jni",
    # -- unsafe / direct memory -------------------------------------------
    "Unsafe.getUnsafe": "unsafe", "getUnsafe": "unsafe",
    "allocateMemory": "unsafe", "reallocateMemory": "unsafe",
    "freeMemory": "unsafe", "objectFieldOffset": "unsafe",
    "staticFieldOffset": "unsafe", "arrayBaseOffset": "unsafe",
    "putOrderedObject": "unsafe", "putOrderedLong": "unsafe",
    "copyMemory": "unsafe", "setMemory": "unsafe", "park": "unsafe",
    "ByteBuffer.allocateDirect": "unsafe", "allocateDirect": "unsafe",
    "VarHandle.fullFence": "unsafe", "fullFence": "unsafe",
    "acquireFence": "unsafe", "releaseFence": "unsafe",
    "loadLoadFence": "unsafe", "storeStoreFence": "unsafe",
    # -- exec --------------------------------------------------------------
    "Runtime.exec": "exec", "Runtime.getRuntime": "exec",
    "new ProcessBuilder": "exec", "ProcessBuilder.start": "exec",
    "new ScriptEngineManager": "exec", "getEngineByName": "exec",
    "getEngineByExtension": "exec", "System.exit": "exec",
    "Runtime.halt": "exec", "addShutdownHook": "exec",
    # -- io ----------------------------------------------------------------
    "new FileInputStream": "io", "new FileOutputStream": "io",
    "new FileReader": "io", "new FileWriter": "io",
    "new RandomAccessFile": "io", "new BufferedReader": "io",
    "new BufferedWriter": "io", "new PrintWriter": "io",
    "new InputStreamReader": "io", "new OutputStreamWriter": "io",
    "Files.newInputStream": "io", "Files.newOutputStream": "io",
    "Files.newBufferedReader": "io", "Files.newBufferedWriter": "io",
    "Files.readAllBytes": "io", "Files.readString": "io",
    "Files.write": "io", "Files.lines": "io", "Files.walk": "io",
    "Files.list": "io", "Files.createTempFile": "io", "Files.delete": "io",
    "FileChannel.open": "io", "IOUtils.toByteArray": "io",
    "getResourceAsStream": "io", "new ZipFile": "io",
    "new ZipInputStream": "io", "new GZIPInputStream": "io",
    # -- net ---------------------------------------------------------------
    "new Socket": "net", "new ServerSocket": "net", "new URL": "net",
    "openConnection": "net", "openStream": "net",
    "HttpClient.newHttpClient": "net", "HttpClient.newBuilder": "net",
    "send": "net", "sendAsync": "net", "SocketChannel.open": "net",
    "ServerSocketChannel.open": "net", "Selector.open": "net",
    "new DatagramSocket": "net", "InetAddress.getByName": "net",
    "bind": "net", "connect": "net",
    # -- sql (IIL_PREPARE_STATEMENT_IN_LOOP and friends) -------------------
    # Bare `execute` and `flush` are deliberately absent: in any event-driven
    # codebase they are Executor.execute and Channel.flush, and including them
    # marked a third of netty as database code.
    "executeQuery": "sql", "executeUpdate": "sql", "executeBatch": "sql",
    "prepareStatement": "sql", "prepareCall": "sql",
    "createStatement": "sql", "getConnection": "sql",
    "createQuery": "sql", "createNativeQuery": "sql",
    "createCriteriaQuery": "sql", "getResultList": "sql",
    "getSingleResult": "sql", "findAll": "sql", "findById": "sql",
    "saveAll": "sql", "setAutoCommit": "sql",
    # -- crypto ------------------------------------------------------------
    "MessageDigest.getInstance": "crypto", "Cipher.getInstance": "crypto",
    "KeyGenerator.getInstance": "crypto", "SecretKeySpec": "crypto",
    "new SecureRandom": "crypto", "SecureRandom.getInstance": "crypto",
    "new Random": "crypto", "Math.random": "crypto",
    "SSLContext.getInstance": "crypto", "TrustManagerFactory.getInstance": "crypto",
    "setHostnameVerifier": "crypto", "Signature.getInstance": "crypto",
    "Mac.getInstance": "crypto", "KeyStore.getInstance": "crypto",
    # -- concurrency -------------------------------------------------------
    "Thread.ofVirtual": "concurrency", "Thread.ofPlatform": "concurrency",
    "Thread.startVirtualThread": "concurrency",
    "startVirtualThread": "concurrency",
    "Executors.newVirtualThreadPerTaskExecutor": "concurrency",
    "newVirtualThreadPerTaskExecutor": "concurrency",
    "Executors.newFixedThreadPool": "concurrency",
    "Executors.newCachedThreadPool": "concurrency",
    "Executors.newSingleThreadExecutor": "concurrency",
    "Executors.newScheduledThreadPool": "concurrency",
    "Executors.newWorkStealingPool": "concurrency",
    "new ThreadPoolExecutor": "concurrency", "new ForkJoinPool": "concurrency",
    "ForkJoinPool.commonPool": "concurrency", "new Thread": "concurrency",
    "CompletableFuture.supplyAsync": "concurrency",
    "CompletableFuture.runAsync": "concurrency",
    "supplyAsync": "concurrency", "runAsync": "concurrency",
    "new StructuredTaskScope": "concurrency", "StructuredTaskScope.open": "concurrency",
    "ScopedValue.where": "concurrency", "ScopedValue.newInstance": "concurrency",
    "ThreadLocal.withInitial": "concurrency", "new ThreadLocal": "concurrency",
    "new InheritableThreadLocal": "concurrency",
    "new FastThreadLocal": "concurrency",
    "parallelStream": "concurrency", "Thread.sleep": "concurrency",
    "Thread.currentThread": "concurrency", "Thread.onSpinWait": "concurrency",
    "wait": "concurrency", "notify": "concurrency", "notifyAll": "concurrency",
    "await": "concurrency", "countDown": "concurrency",
    "new CountDownLatch": "concurrency", "new Semaphore": "concurrency",
    "new CyclicBarrier": "concurrency", "new Phaser": "concurrency",
    "AtomicInteger": "concurrency", "AtomicLong": "concurrency",
    "AtomicReference": "concurrency", "compareAndSet": "concurrency",
    "getAndSet": "concurrency", "incrementAndGet": "concurrency",
    "getAndIncrement": "concurrency", "updateAndGet": "concurrency",
    "accumulateAndGet": "concurrency", "lazySet": "concurrency",
    # -- lock --------------------------------------------------------------
    "lock": "lock", "tryLock": "lock", "unlock": "lock",
    "lockInterruptibly": "lock", "new ReentrantLock": "lock",
    "new ReentrantReadWriteLock": "lock", "new StampedLock": "lock",
    "readLock": "lock", "writeLock": "lock", "tryOptimisticRead": "lock",
    "unlockRead": "lock", "unlockWrite": "lock",
    "Collections.synchronizedList": "lock",
    "Collections.synchronizedMap": "lock",
    "Collections.synchronizedSet": "lock",
    "new ConcurrentHashMap": "lock", "computeIfAbsent": "lock",
    # -- alloc -------------------------------------------------------------
    "new StringBuilder": "alloc", "new StringBuffer": "alloc",
    "new ArrayList": "alloc", "new HashMap": "alloc", "new HashSet": "alloc",
    "new LinkedList": "alloc", "new byte": "alloc",
    "Arrays.copyOf": "alloc", "Arrays.copyOfRange": "alloc",
    "System.arraycopy": "alloc", "clone": "alloc",
    "toArray": "alloc", "String.format": "alloc", "format": "alloc",
    "concat": "alloc", "getBytes": "alloc", "toCharArray": "alloc",
    "Collectors.toList": "alloc", "Collectors.toMap": "alloc",
    "Collectors.joining": "alloc", "Collectors.groupingBy": "alloc",
    # -- boxing (DM_BOXED_PRIMITIVE_FOR_PARSING and friends) ---------------
    "Integer.valueOf": "boxing", "Long.valueOf": "boxing",
    "Double.valueOf": "boxing", "Float.valueOf": "boxing",
    "Short.valueOf": "boxing", "Byte.valueOf": "boxing",
    "Character.valueOf": "boxing", "Boolean.valueOf": "boxing",
    "intValue": "boxing", "longValue": "boxing", "doubleValue": "boxing",
    "floatValue": "boxing", "booleanValue": "boxing", "shortValue": "boxing",
    "new Integer": "boxing", "new Long": "boxing", "new Double": "boxing",
    "new Boolean": "boxing", "new Character": "boxing",
    "Integer.parseInt": "boxing", "Long.parseLong": "boxing",
    "Double.parseDouble": "boxing",
    # -- string ------------------------------------------------------------
    "Pattern.compile": "string", "matches": "string", "replaceAll": "string",
    "replaceFirst": "string", "split": "string", "String.join": "string",
    "new String": "string", "substring": "string", "intern": "string",
    "toLowerCase": "string", "toUpperCase": "string",
    "new SimpleDateFormat": "string", "DateTimeFormatter.ofPattern": "string",
    "new Date": "string", "Calendar.getInstance": "string",
    "new DecimalFormat": "string", "new NumberFormat": "string",
    # -- resource ----------------------------------------------------------
    "close": "resource", "closeQuietly": "resource",
    "IOUtils.closeQuietly": "resource", "Cleaner.create": "resource",
    "finalize": "resource", "shutdown": "resource",
    "shutdownNow": "resource", "awaitTermination": "resource",
    "release": "resource", "retain": "resource", "refCnt": "resource",
    "free": "resource", "dispose": "resource",
    # -- control (things that end or divert a thread of control) ------------
    "assertTrue": "control", "requireNonNull": "control",
    "checkArgument": "control", "checkState": "control",
    "printStackTrace": "control", "getStackTrace": "control",
    "fillInStackTrace": "control", "Thread.dumpStack": "control",
    "System.getProperty": "control", "System.setProperty": "control",
    "System.getenv": "control",
}

RESOURCE_TYPES = frozenset("""
FileInputStream FileOutputStream FileReader FileWriter RandomAccessFile
BufferedReader BufferedWriter BufferedInputStream BufferedOutputStream
PrintWriter PrintStream InputStreamReader OutputStreamWriter DataInputStream
DataOutputStream ObjectInputStream ObjectOutputStream ZipFile ZipInputStream
ZipOutputStream GZIPInputStream GZIPOutputStream JarFile Socket ServerSocket
DatagramSocket SocketChannel ServerSocketChannel FileChannel Selector
Scanner Formatter Connection Statement PreparedStatement CallableStatement
ResultSet InputStream OutputStream Reader Writer Arena
""".split())

RESOURCE_OPENERS = frozenset("""
newInputStream newOutputStream newBufferedReader newBufferedWriter
getResourceAsStream openStream openConnection getConnection createStatement
prepareStatement prepareCall executeQuery newDirectoryStream
ofConfined ofShared allocateDirect
""".split())

RESOURCE_OPENERS_QUALIFIED: dict[str, frozenset] = {
    "open": frozenset("Files FileChannel SocketChannel ServerSocketChannel "
                      "DatagramChannel AsynchronousFileChannel Selector "
                      "AsynchronousSocketChannel".split()),
    "accept": frozenset("ServerSocket ServerSocketChannel "
                        "AsynchronousServerSocketChannel".split()),
    "lines": frozenset(["Files"]),
    "walk": frozenset(["Files"]),
    "list": frozenset(["Files"]),
}

def _opens_resource(method: str, receiver: str) -> bool:
    if method in RESOURCE_OPENERS:
        return True
    owners = RESOURCE_OPENERS_QUALIFIED.get(method)
    return bool(owners and receiver.rsplit(".", 1)[-1] in owners)

POOLED_EXECUTOR_RE = re.compile(
    r'\b(?:newFixedThreadPool|newCachedThreadPool|newSingleThreadExecutor|'
    r'newScheduledThreadPool|newSingleThreadScheduledExecutor|'
    r'newWorkStealingPool|ThreadPoolExecutor|ForkJoinPool|commonPool|'
    r'ScheduledThreadPoolExecutor|NioEventLoopGroup|DefaultEventExecutorGroup)\b')

VIRTUAL_THREAD_RE = re.compile(
    r'\b(?:ofVirtual|startVirtualThread|newVirtualThreadPerTaskExecutor|'
    r'StructuredTaskScope)\b')

HANDLER_ANNOTATIONS = frozenset("""
RequestMapping GetMapping PostMapping PutMapping DeleteMapping PatchMapping
Path GET POST PUT DELETE WebServlet MessageMapping KafkaListener
RabbitListener JmsListener EventListener Scheduled Bean
""".split())

HANDLER_METHODS = frozenset("doGet doPost doPut doDelete service onMessage".split())

FRAMEWORK_ANNOTATIONS = frozenset("""
Test BeforeEach AfterEach BeforeAll AfterAll ParameterizedTest RepeatedTest
Before After BeforeClass AfterClass Benchmark Setup TearDown
Autowired Inject Resource PostConstruct PreDestroy Bean Component Service
Repository Controller RestController Configuration Provides Subscribe
JsonCreator JsonProperty Override
""".split())

SQL_RE = re.compile(
    r'\b(SELECT\s|INSERT\s+INTO|UPDATE\s|DELETE\s+FROM|CREATE\s+TABLE|'
    r'DROP\s+TABLE|ALTER\s+TABLE|MERGE\s+INTO)', re.I)

RAW_TYPE_RE = re.compile(
    r'\b(?:List|ArrayList|LinkedList|Map|HashMap|TreeMap|Set|HashSet|TreeSet|'
    r'Collection|Iterator|Iterable|Comparable|Comparator|Class|Optional|'
    r'Future|CompletableFuture|Callable|Enumeration|Queue|Deque|Stream)'
    r'\s+[A-Za-z_$]\w*\s*[=;,)]')

MODULE_IMPORT_RE = re.compile(r'^[ \t]*import[ \t]+module[ \t]+([\w.]+)[ \t]*;',
                              re.M)

GENERATED_ANNO_RE = re.compile(r'@(?:javax\.annotation\.)?Generated\b')

JDK_PACKAGE_ROOTS = frozenset("java javax jdk sun com.sun jakarta".split())

JDK_TYPES = frozenset("""
System Math String StringBuilder StringBuffer Object Objects Integer Long
Double Float Short Byte Character Boolean Number Class Enum Record Void
Thread Runnable Runtime Process ProcessBuilder ThreadLocal ScopedValue
Arrays Collections List ArrayList LinkedList Map HashMap TreeMap LinkedHashMap
ConcurrentHashMap Set HashSet TreeSet LinkedHashSet Collection Iterator
Iterable Queue Deque ArrayDeque PriorityQueue Optional OptionalInt Stream
IntStream LongStream DoubleStream Collectors StreamSupport Comparator
Executors ExecutorService Executor ScheduledExecutorService Future
CompletableFuture CompletionStage ForkJoinPool ForkJoinTask CountDownLatch
Semaphore CyclicBarrier Phaser Exchanger TimeUnit
AtomicInteger AtomicLong AtomicBoolean AtomicReference AtomicIntegerArray
AtomicLongArray LongAdder DoubleAdder LongAccumulator
ReentrantLock ReentrantReadWriteLock StampedLock Condition LockSupport
VarHandle MethodHandle MethodHandles MethodType Unsafe
Files Paths Path File FileSystem FileSystems Channels
ByteBuffer CharBuffer IntBuffer LongBuffer ByteOrder
Charset StandardCharsets StandardOpenOption
Pattern Matcher Random SecureRandom UUID Base64 BitSet
Date Calendar Instant Duration Period LocalDate LocalDateTime LocalTime
ZonedDateTime OffsetDateTime ZoneId ZoneOffset DateTimeFormatter Clock
BigInteger BigDecimal MathContext RoundingMode
Exception RuntimeException Error Throwable IllegalArgumentException
IllegalStateException NullPointerException IndexOutOfBoundsException
UnsupportedOperationException IOException UncheckedIOException
InterruptedException ClassNotFoundException NoSuchMethodException
ReflectiveOperationException SecurityException
Logger LogManager Level Handler
Arena Linker MemorySegment MemoryLayout SymbolLookup ValueLayout FunctionDescriptor
StructuredTaskScope ServiceLoader ClassLoader Module ModuleLayer
Proxy Array Field Method Constructor Modifier AccessibleObject Parameter
Instrumentation
""".split())

JDK_METHODS = frozenset("""
toString equals hashCode getClass clone finalize notify notifyAll
name ordinal values valueOf compareTo
length isEmpty charAt indexOf lastIndexOf trim strip startsWith endsWith
substring toLowerCase toUpperCase concat replace split join chars codePoints
println print printf format append setLength setCharAt reverse
iterator hasNext next stream forEach spliterator
printStackTrace getMessage getLocalizedMessage getCause getStackTrace
""".split())

QUALIFIER_NODES = frozenset("""
identifier this super field_access scoped_identifier type_identifier
scoped_type_identifier generic_type
""".split())

BROAD_EXCEPTIONS = frozenset(
    "Exception Throwable RuntimeException Error".split())

class JavaAnalyzer(TreeSitterAnalyzer):
    LANG = "java"
    TARGET = "Java 25 (LTS)"
    EXTS = (".java",)
    SKIP_DIRS = {"target", "build", ".gradle", "generated-sources",
                 "generated-test-sources"}
    DEPS = DEPS
    HAZARD_CATEGORIES = HAZARD_CATEGORIES
    MANIFESTS = ("pom.xml", "build.gradle", "build.gradle.kts", "module-info.java")

    GRAMMAR_MODULE = "tree_sitter_java"
    GRAMMAR_PIP = "tree-sitter-java>=0.23"

    FUNC_KINDS = {
        "method_declaration": "method",
        "constructor_declaration": "constructor",
        "compact_constructor_declaration": "constructor",
        "annotation_type_element_declaration": "method",
        "static_initializer": "method",
        "lambda_expression": "closure",
    }
    TYPE_KINDS = {
        "class_declaration": "class",
        "interface_declaration": "interface",
        "enum_declaration": "enum",
        "record_declaration": "record",
        "annotation_type_declaration": "type",
    }
    #: `lambda_expression` and `static_initializer` have no name field, and the
    #: base's fallback would otherwise name a lambda after its first parameter.
    NAME_FIELD = {"lambda_expression": "", "static_initializer": ""}
    IDENT_NODES = ("identifier", "type_identifier", "scoped_identifier")

    BODY_FIELD = "body"
    PARAMS_FIELD = "parameters"
    #: NOT "return_type". A Java method's return type is the `type` field, and
    #: the base's default leaves symbols.return_type empty for every row.
    RETURN_FIELD = "type"
    ELSE_FIELD = "alternative"
    IF_NODES = ("if_statement",)

    LOOP_NODES = ("for_statement", "enhanced_for_statement", "while_statement",
                  "do_statement")
    BRANCH_NODES = ("if_statement",)
    #: The braced block is deliberately absent: every `if` and every
    #: loop owns one, so counting both charges two levels for one and
    #: reports depth as 2n+1.
    NEST_NODES = ("if_statement", "for_statement", "enhanced_for_statement",
                  "while_statement", "do_statement", "switch_expression",
                  "try_statement", "try_with_resources_statement",
                  "catch_clause", "synchronized_statement",
                  "lambda_expression")
    #: `method_reference` is here because `executor.submit(this::work)` is how
    #: Java hands work to another thread, and treating it as a non-call breaks
    #: every reachability query at exactly the hop that matters.
    #: `explicit_constructor_invocation` (`super(...)`, `this(...)`) is left out
    #: on purpose: it is counted as a call but has no name that could resolve.
    CALL_NODES = ("method_invocation", "object_creation_expression",
                  "method_reference")
    CALL_FUNC_FIELD = "name"
    COMMENT_NODES = ("line_comment", "block_comment")
    STRING_NODES = ("string_literal", "character_literal")
    NUMBER_NODES = ("decimal_integer_literal", "hex_integer_literal",
                    "octal_integer_literal", "binary_integer_literal",
                    "decimal_floating_point_literal",
                    "hex_floating_point_literal")
    OPERATOR_NODES = ("binary_expression", "unary_expression",
                      "assignment_expression", "update_expression",
                      "array_access", "field_access", "cast_expression",
                      "instanceof_expression", "ternary_expression")

    COUNTERS = {
        "return_statement": "n_returns",
        "throw_statement": "n_throw_sites",
        "try_statement": "n_try",
        "try_with_resources_statement": "n_try_resources",
        "catch_clause": "n_catch",
        "finally_clause": "n_finally",
        "switch_expression": "n_switch",
        "switch_label": "n_cases",
        "ternary_expression": "n_ternary",
        "lambda_expression": "n_lambdas",
        "method_reference": "n_method_refs",
        "instanceof_expression": "n_instanceof",
        "synchronized_statement": "n_synchronized_blocks",
        "labeled_statement": "n_labels",
        "object_creation_expression": "n_alloc_sites",
        "array_creation_expression": "n_alloc_sites",
        "annotation": "n_annotations",
        "marker_annotation": "n_annotations",
        "wildcard": "n_wildcard_types",
        "local_variable_declaration": "n_locals",
        "assignment_expression": "n_assign",
        "update_expression": "n_incdec",
        "type_parameter": "n_generic_params",
        "array_access": "n_subscript",
        "field_access": "n_member_access",
        "explicit_constructor_invocation": "n_calls",
        "resource": "n_resource_open",
    }
    #: Only names with no substring collisions live here; boxing, locks and
    #: allocation are handled in `on_node` where the receiver can be checked.
    LOOP_CALL_COUNTERS = {
        "prepareStatement": "query_in_loop",
        "createQuery": "query_in_loop",
        "createNativeQuery": "query_in_loop",
        "executeQuery": "query_in_loop",
        "executeUpdate": "query_in_loop",
        "getResultList": "query_in_loop",
        "Pattern.compile": "regex_in_loop",
        "new SimpleDateFormat": "n_datefmt_ops",
    }

    EXTRA_SYMBOL_COLS = (
        #: Text blocks (JEP 378). A multi-line SQL or JSON literal inside a
        #: method is where an injection or a drifted schema hides, and it
        #: shows up as neither a long line nor an unusual string.
        ("n_text_blocks", "INT NOT NULL DEFAULT 0"),
        # -- functional / stream texture --
        ("n_lambdas", "INT NOT NULL DEFAULT 0"),
        ("n_method_refs", "INT NOT NULL DEFAULT 0"),
        ("n_streams", "INT NOT NULL DEFAULT 0"),
        ("n_parallel_streams", "INT NOT NULL DEFAULT 0"),
        ("n_collectors", "INT NOT NULL DEFAULT 0"),
        # -- per-element cost --
        ("n_boxing_sites", "INT NOT NULL DEFAULT 0"),
        ("n_boxing_in_loop", "INT NOT NULL DEFAULT 0"),
        ("n_string_concat", "INT NOT NULL DEFAULT 0"),
        # -- concurrency --
        ("n_synchronized_blocks", "INT NOT NULL DEFAULT 0"),
        ("n_synchronized_methods", "INT NOT NULL DEFAULT 0"),
        ("n_lock_acquire", "INT NOT NULL DEFAULT 0"),
        ("n_lock_release", "INT NOT NULL DEFAULT 0"),
        ("n_wait_calls", "INT NOT NULL DEFAULT 0"),
        ("n_volatile_access", "INT NOT NULL DEFAULT 0"),
        ("n_atomic_ops", "INT NOT NULL DEFAULT 0"),
        ("n_threadlocal_ops", "INT NOT NULL DEFAULT 0"),
        ("n_threadlocal_remove", "INT NOT NULL DEFAULT 0"),
        # -- resources --
        ("n_try_resources", "INT NOT NULL DEFAULT 0"),
        ("n_close_calls", "INT NOT NULL DEFAULT 0"),
        ("n_resource_open", "INT NOT NULL DEFAULT 0"),
        ("n_finalizers", "INT NOT NULL DEFAULT 0"),
        # -- exceptions --
        ("n_throws_declared", "INT NOT NULL DEFAULT 0"),
        ("n_throw_sites", "INT NOT NULL DEFAULT 0"),
        ("n_catch_rethrow", "INT NOT NULL DEFAULT 0"),
        # -- reflection / native / unsafe --
        ("n_setaccessible", "INT NOT NULL DEFAULT 0"),
        ("n_native_calls", "INT NOT NULL DEFAULT 0"),
        ("n_ffm_arena", "INT NOT NULL DEFAULT 0"),
        ("n_ffm_downcall", "INT NOT NULL DEFAULT 0"),
        ("n_unsafe_calls", "INT NOT NULL DEFAULT 0"),
        # -- type system --
        ("n_wildcard_types", "INT NOT NULL DEFAULT 0"),
        ("n_raw_types", "INT NOT NULL DEFAULT 0"),
        ("n_unchecked_casts", "INT NOT NULL DEFAULT 0"),
        ("n_instanceof", "INT NOT NULL DEFAULT 0"),
        ("n_null_returns", "INT NOT NULL DEFAULT 0"),
        ("n_optional_ops", "INT NOT NULL DEFAULT 0"),
        # -- annotations and static state --
        ("n_annotations", "INT NOT NULL DEFAULT 0"),
        ("n_suppressions", "INT NOT NULL DEFAULT 0"),
        ("n_static_writes", "INT NOT NULL DEFAULT 0"),
        # -- per-element work --
        ("n_query_calls", "INT NOT NULL DEFAULT 0"),
        ("n_regex_compile", "INT NOT NULL DEFAULT 0"),
        ("n_datefmt_ops", "INT NOT NULL DEFAULT 0"),
        ("n_escaping_allocs", "INT NOT NULL DEFAULT 0"),
        ("n_alloc_sites", "INT NOT NULL DEFAULT 0"),
        # -- dispatch --
        ("n_impl_targets", "INT NOT NULL DEFAULT 0"),
        # -- roots --
        ("is_virtual_thread_root", "INT NOT NULL DEFAULT 0"),
        ("is_executor_root", "INT NOT NULL DEFAULT 0"),
        ("is_pooled_executor_root", "INT NOT NULL DEFAULT 0"),
        ("is_handler", "INT NOT NULL DEFAULT 0"),
        # -- serialization surface --
        ("is_serializable", "INT NOT NULL DEFAULT 0"),
        ("has_serial_uid", "INT NOT NULL DEFAULT 0"),
        # -- shape --
        ("owner_type", "TEXT NOT NULL DEFAULT ''"),
        ("n_elif", "INT NOT NULL DEFAULT 0"),
        ("n_external_calls", "INT NOT NULL DEFAULT 0"),
    )

    SCHEMA_EXT = r"""
CREATE TABLE type_relations(
    id INTEGER PRIMARY KEY,
    child_id INT NOT NULL REFERENCES symbols(id),
    file_id INT NOT NULL REFERENCES files(id),
    child_name TEXT NOT NULL,
    child_kind TEXT NOT NULL DEFAULT '',
    parent_name TEXT NOT NULL,
    kind TEXT NOT NULL,
    is_generic INT NOT NULL DEFAULT 0,
    line INT NOT NULL DEFAULT 0
) STRICT;

CREATE TABLE overrides(
    id INTEGER PRIMARY KEY,
    symbol_id INT NOT NULL REFERENCES symbols(id),
    file_id INT NOT NULL REFERENCES files(id),
    method_name TEXT NOT NULL,
    owner_type TEXT NOT NULL DEFAULT '',
    parent_type TEXT NOT NULL DEFAULT '',
    is_annotated INT NOT NULL DEFAULT 0,
    is_framework_entry INT NOT NULL DEFAULT 0,
    n_params INT NOT NULL DEFAULT 0,
    line INT NOT NULL DEFAULT 0
) STRICT;

CREATE TABLE exceptions(
    id INTEGER PRIMARY KEY,
    symbol_id INT NOT NULL REFERENCES symbols(id),
    file_id INT NOT NULL REFERENCES files(id),
    kind TEXT NOT NULL,
    type TEXT NOT NULL DEFAULT '',
    is_broad INT NOT NULL DEFAULT 0,
    is_empty INT NOT NULL DEFAULT 0,
    rethrows INT NOT NULL DEFAULT 0,
    logs INT NOT NULL DEFAULT 0,
    in_loop INT NOT NULL DEFAULT 0,
    line INT NOT NULL DEFAULT 0
) STRICT;

CREATE TABLE generics(
    id INTEGER PRIMARY KEY,
    symbol_id INT NOT NULL REFERENCES symbols(id),
    file_id INT NOT NULL REFERENCES files(id),
    owner TEXT NOT NULL DEFAULT '',
    name TEXT NOT NULL,
    bound TEXT NOT NULL DEFAULT '',
    is_self_referential INT NOT NULL DEFAULT 0,
    on_type INT NOT NULL DEFAULT 0,
    line INT NOT NULL DEFAULT 0
) STRICT;

CREATE TABLE resources(
    id INTEGER PRIMARY KEY,
    symbol_id INT NOT NULL REFERENCES symbols(id),
    file_id INT NOT NULL REFERENCES files(id),
    name TEXT NOT NULL DEFAULT '',
    type TEXT NOT NULL DEFAULT '',
    opened_by TEXT NOT NULL DEFAULT '',
    in_try_resources INT NOT NULL DEFAULT 0,
    closed_in_fn INT NOT NULL DEFAULT 0,
    in_loop INT NOT NULL DEFAULT 0,
    line INT NOT NULL DEFAULT 0
) STRICT;

CREATE TABLE lock_ops(
    id INTEGER PRIMARY KEY,
    symbol_id INT NOT NULL REFERENCES symbols(id),
    file_id INT NOT NULL REFERENCES files(id),
    lock_name TEXT NOT NULL DEFAULT '',
    op TEXT NOT NULL,
    kind TEXT NOT NULL DEFAULT '',
    acq_order INT NOT NULL DEFAULT 0,
    in_loop INT NOT NULL DEFAULT 0,
    holds_io INT NOT NULL DEFAULT 0,
    holds_sleep INT NOT NULL DEFAULT 0,
    holds_alloc INT NOT NULL DEFAULT 0,
    holds_call INT NOT NULL DEFAULT 0,
    region_sloc INT NOT NULL DEFAULT 0,
    line INT NOT NULL DEFAULT 0
) STRICT;

CREATE TABLE jpms_directives(
    id INTEGER PRIMARY KEY,
    file_id INT NOT NULL REFERENCES files(id),
    kind TEXT NOT NULL,
    module_name TEXT NOT NULL DEFAULT '',
    target TEXT NOT NULL DEFAULT '',
    is_transitive INT NOT NULL DEFAULT 0,
    is_static INT NOT NULL DEFAULT 0,
    line INT NOT NULL DEFAULT 0
) STRICT;
"""

    INDEX_EXT = r"""
CREATE INDEX idx_tr_parent ON type_relations(parent_name, kind);
CREATE INDEX idx_tr_child ON type_relations(child_name);
CREATE INDEX idx_tr_sym ON type_relations(child_id);
CREATE INDEX idx_ovr_name ON overrides(method_name, owner_type);
CREATE INDEX idx_ovr_sym ON overrides(symbol_id);
CREATE INDEX idx_exc_sym ON exceptions(symbol_id, kind);
CREATE INDEX idx_exc_broad ON exceptions(type) WHERE is_broad=1;
CREATE INDEX idx_exc_empty ON exceptions(symbol_id) WHERE is_empty=1;
CREATE INDEX idx_gen_sym ON generics(symbol_id);
CREATE INDEX idx_gen_self ON generics(owner) WHERE is_self_referential=1;
CREATE INDEX idx_res_sym ON resources(symbol_id, in_try_resources);
CREATE INDEX idx_res_open ON resources(type) WHERE in_try_resources=0;
CREATE INDEX idx_lock_sym ON lock_ops(symbol_id, acq_order);
CREATE INDEX idx_lock_name ON lock_ops(lock_name, op);
CREATE INDEX idx_lock_io ON lock_ops(symbol_id) WHERE holds_io=1;
CREATE INDEX idx_jpms_file ON jpms_directives(file_id, kind);
CREATE INDEX idx_fn_handler ON symbols(name, file_id) WHERE is_handler=1;
CREATE INDEX idx_fn_vtroot ON symbols(name, file_id) WHERE is_virtual_thread_root=1;
CREATE INDEX idx_fn_pool ON symbols(name, file_id) WHERE is_pooled_executor_root=1;
CREATE INDEX idx_fn_owner ON symbols(owner_type, name);
CREATE INDEX idx_fn_refl ON symbols(n_reflection DESC, name) WHERE n_reflection>0;
"""

    VIEW_EXT = r"""
CREATE VIEW v_impl_count AS
SELECT s.id AS type_id, s.name AS type_, s.kind, s.is_public,
    COALESCE(m.name,'') AS module,
    (SELECT COUNT(DISTINCT r.child_name) FROM type_relations r
     WHERE r.parent_name = s.name AND r.kind IN ('implements','extends'))
        AS n_impls,
    (SELECT COUNT(DISTINCT r.child_name) FROM type_relations r
     WHERE r.parent_name = s.name AND r.kind = 'permits') AS n_permitted,
    (SELECT COUNT(*) FROM params p WHERE p.type = s.name
        OR p.type LIKE s.name || '<%') AS used_as_param,
    s.n_impl_targets, f.path || ':' || s.line_start AS at
FROM symbols s
JOIN files f ON f.id = s.file_id
LEFT JOIN modules m ON m.id = s.module_id
WHERE s.kind IN ('interface','class','record','enum','type');

CREATE VIEW v_lock_pair AS
SELECT a.symbol_id, a.lock_name AS first_lock, b.lock_name AS second_lock,
    a.acq_order AS first_order, b.acq_order AS second_order, a.file_id, a.line
FROM lock_ops a
JOIN lock_ops b ON b.symbol_id = a.symbol_id AND b.acq_order > a.acq_order
WHERE a.op='acquire' AND b.op='acquire'
  AND a.lock_name <> '' AND b.lock_name <> ''
  AND a.lock_name <> b.lock_name;
"""

    MATERIALIZE_EXT = r"""
UPDATE symbols AS s SET n_unique_calls = x.c FROM
    (SELECT caller_id AS id, COUNT(*) AS c FROM edges GROUP BY caller_id) AS x
    WHERE x.id = s.id;

-- How many distinct types name this one as a supertype. Drives the
-- megamorphic-dispatch query; 0 on an interface means it is an abstraction
-- over nothing that this tree can see.
UPDATE symbols AS s SET n_impl_targets = x.c FROM
    (SELECT parent_name AS nm, COUNT(DISTINCT child_name) AS c
     FROM type_relations WHERE kind IN ('implements','extends')
     GROUP BY parent_name) AS x
    WHERE x.nm = s.name
      AND s.kind IN ('interface','class','record','enum','type');

UPDATE symbols AS s SET n_lock_acquire = x.c FROM
    (SELECT symbol_id AS id, COUNT(*) AS c FROM lock_ops
     WHERE op='acquire' GROUP BY symbol_id) AS x WHERE x.id = s.id;

UPDATE symbols AS s SET n_lock_release = x.c FROM
    (SELECT symbol_id AS id, COUNT(*) AS c FROM lock_ops
     WHERE op='release' GROUP BY symbol_id) AS x WHERE x.id = s.id;

UPDATE symbols AS s SET n_resource_open = x.c FROM
    (SELECT symbol_id AS id, COUNT(*) AS c FROM resources
     GROUP BY symbol_id) AS x WHERE x.id = s.id;

UPDATE symbols AS s SET n_throws_declared = x.c FROM
    (SELECT symbol_id AS id, COUNT(*) AS c FROM exceptions
     WHERE kind='throws' GROUP BY symbol_id) AS x WHERE x.id = s.id;

UPDATE symbols AS s SET n_catch_broad = x.c FROM
    (SELECT symbol_id AS id, COUNT(*) AS c FROM exceptions
     WHERE kind='catch' AND is_broad=1 GROUP BY symbol_id) AS x
    WHERE x.id = s.id;

UPDATE symbols AS s SET n_catch_empty = x.c FROM
    (SELECT symbol_id AS id, COUNT(*) AS c FROM exceptions
     WHERE kind='catch' AND is_empty=1 GROUP BY symbol_id) AS x
    WHERE x.id = s.id;

UPDATE symbols AS s SET n_catch_rethrow = x.c FROM
    (SELECT symbol_id AS id, COUNT(*) AS c FROM exceptions
     WHERE kind='catch' AND rethrows=1 GROUP BY symbol_id) AS x
    WHERE x.id = s.id;

UPDATE symbols SET n_throw = n_throw_sites WHERE n_throw_sites > 0;

-- A type is serializable if it says so OR if any supertype in this tree does.
-- One hop only: a deeper chain is what the reachability query is for.
UPDATE symbols AS s SET is_serializable = 1 WHERE s.id IN (
    SELECT r.child_id FROM type_relations r
    WHERE r.parent_name IN ('Serializable','Externalizable'));

-- Java overloads by arity and by type, so a name alone does not identify a
-- method. This is also why call resolution by simple name lands on whichever
-- overload was seen first; the count is the size of that ambiguity.
UPDATE symbols AS s SET n_overloads = x.c - 1 FROM
    (SELECT owner_type AS ot, name AS nm, COUNT(*) AS c FROM symbols
     WHERE kind IN ('method','constructor') AND owner_type <> ''
     GROUP BY owner_type, name HAVING COUNT(*) > 1) AS x
    WHERE x.ot = s.owner_type AND x.nm = s.name;

UPDATE symbols SET arity_rank = CASE
    WHEN n_params <= 1 THEN 0 WHEN n_params <= 3 THEN 1
    WHEN n_params <= 6 THEN 2 ELSE 3 END
    WHERE kind IN ('function','method','constructor','closure');
"""

    RISK_SQL = (
        "cyclomatic*2 + cognitive + max_nesting*4"
        " + n_reflection*6 + n_serialization*14 + n_jni*10 + n_unsafe*10"
        " + n_exec*15 + n_setaccessible*8"
        " + n_catch_broad*4 + n_catch_empty*10 + n_catch_rethrow*2"
        " + n_lock_acquire*3 + lock_in_loop*10"
        " + query_in_loop*15 + n_string_concat*2 + concat_in_loop*8"
        " + n_boxing_in_loop*6 + regex_in_loop*10"
        " + n_raw_types*3 + n_unchecked_casts*4"
        " + n_static_writes*6 + n_finalizers*12"
        " + (CASE WHEN is_recursive THEN 12 ELSE 0 END)"
        " + (CASE WHEN n_resource_open > n_close_calls + n_try_resources"
        "    THEN 12 ELSE 0 END)"
        " + (CASE WHEN is_serializable=1 AND has_serial_uid=0 THEN 8 ELSE 0 END)"
    )

    def __init__(self) -> None:
        super().__init__()
        #: package roots declared anywhere in the tree; anything else is external
        self.pkg_roots: set[str] = set()
        #: file_id -> {simple type name: fully qualified import target}
        self.file_imports: dict[int, dict[str, str]] = {}
        #: type name -> [supertype names], filled before that type's methods
        self.parents: dict[str, list[str]] = {}
        #: type name -> {volatile field names}
        self.volatile_fields: dict[str, set[str]] = {}
        #: type name -> {mutable static field names}
        self.static_fields: dict[str, set[str]] = {}
        #: type name -> {field names whose declared type is a ThreadLocal}
        self.threadlocal_fields: dict[str, set[str]] = {}
        self.java_release = ""

    # -- naming ------------------------------------------------------------
    def node_name(self, node: Any, rec: FileRec) -> str:
        t = node.type
        if t == "lambda_expression":
            return "(lambda)"
        if t == "static_initializer":
            return "<clinit>"
        return super().node_name(node, rec)

    # -- symbol shape ------------------------------------------------------
    def visibility_of(self, node: Any, rec: FileRec) -> str:
        mods = _modifiers_text(node, rec.data)
        for word in ("public", "protected", "private"):
            if re.search(r'\b%s\b' % word, mods):
                return word
        return "package"

    def function_flags(self, node: Any, rec: FileRec,
                       scope: Scope) -> dict[str, Any]:
        src = rec.data
        name = self.node_name(node, rec)
        mods = _modifiers_text(node, src)
        annos = _annotation_names(node, src)
        sig = self.signature_of(node, rec)
        body = node.child_by_field_name(self.BODY_FIELD)
        btxt = _txt(body, src) if body is not None else ""
        params = node.child_by_field_name("parameters")
        ptxt = _txt(params, src) if params is not None else ""
        is_iface_member = scope.type_name != "" and node.child_by_field_name(
            self.BODY_FIELD) is None

        pooled = bool(POOLED_EXECUTOR_RE.search(btxt))
        virtual = bool(VIRTUAL_THREAD_RE.search(btxt))
        return dict(
            is_public=1 if "public" in mods or (
                not mods and scope.type_name == "") else 0,
            is_static=1 if re.search(r'\bstatic\b', mods) else 0,
            is_abstract=1 if re.search(r'\babstract\b', mods)
                          or (is_iface_member and node.type ==
                              "method_declaration") else 0,
            is_override=1 if "Override" in annos else 0,
            is_deprecated=1 if "Deprecated" in annos else 0,
            is_test=1 if (annos & {"Test", "ParameterizedTest", "RepeatedTest",
                                   "Benchmark"}) or name.startswith("test") else 0,
            is_entrypoint=1 if name == "main" or name == "<clinit>" else 0,
            is_handler=1 if (annos & HANDLER_ANNOTATIONS)
                         or name in HANDLER_METHODS else 0,
            is_virtual_thread_root=int(virtual),
            is_executor_root=int(pooled or virtual),
            is_pooled_executor_root=int(pooled),
            owner_type=scope.type_name[:120],
            n_synchronized_methods=1 if re.search(r'\bsynchronized\b', mods) else 0,
            n_native_calls=1 if re.search(r'\bnative\b', mods) else 0,
            n_finalizers=1 if name == "finalize" else 0,
            n_annotations=len(annos),
            n_suppressions=1 if "SuppressWarnings" in annos else 0,
            n_generic_params=_count_type_params(node),
            n_raw_types=len(RAW_TYPE_RE.findall(sig + " " + btxt[:20000])),
            n_wildcard_types=ptxt.count("?"),
            n_params=_count_params(params),
        )

    def type_flags(self, node: Any, rec: FileRec,
                   scope: Scope) -> dict[str, Any]:
        src = rec.data
        mods = _modifiers_text(node, src)
        annos = _annotation_names(node, src)
        parents = _supertype_names(node, src)
        body = node.child_by_field_name("body")
        btxt = _txt(body, src) if body is not None else ""
        return dict(
            is_public=1 if "public" in mods else 0,
            is_static=1 if re.search(r'\bstatic\b', mods) else 0,
            is_abstract=1 if re.search(r'\babstract\b', mods)
                          or node.type == "interface_declaration" else 0,
            is_deprecated=1 if "Deprecated" in annos else 0,
            is_serializable=1 if ({"Serializable", "Externalizable"}
                                  & set(parents)) else 0,
            has_serial_uid=1 if "serialVersionUID" in btxt[:200000] else 0,
            is_handler=1 if (annos & HANDLER_ANNOTATIONS) else 0,
            owner_type=scope.type_name[:120],
            n_annotations=len(annos),
            n_generic_params=_count_type_params(node),
        )

    # -- the measuring pass ------------------------------------------------
    def on_call(self, node: Any, src: bytes, st: BodyStats,
                loop_depth: int, nest: int) -> None:
        """Read a Java call's callee name.

        The base cannot do this: `method_invocation` has no `function` field --
        it has `object`, `name` and `arguments` -- so the inherited version
        records nothing, resolves nothing, and leaves `edges` empty while every
        other table looks healthy. That silence is the whole reason this
        override exists.
        """
        st.bump("n_calls")
        if loop_depth:
            st.bump("call_in_loop")
        line = node.start_point[0] + 1

        if node.type == "object_creation_expression":
            ty = node.child_by_field_name("type")
            tname = _simple_type(_txt(ty, src)) if ty is not None else ""
            if not tname:
                st.bump("n_dynamic_calls")
                return
            st.calls.append(("new " + tname, line, False, bool(loop_depth)))
            if loop_depth:
                st.bump("alloc_in_loop")
                if tname in ("Integer", "Long", "Double", "Float", "Boolean",
                             "Character", "Short", "Byte"):
                    st.bump("n_boxing_in_loop")
                if tname in ("StringBuilder", "StringBuffer"):
                    st.bump("concat_in_loop")
            if tname in RESOURCE_TYPES:
                st.bump("io_in_loop" if loop_depth else "n_resource_open")
            self._loop_counters("new " + tname, st, loop_depth)
            return

        if node.type == "method_reference":
            # `Type::method`, `this::method`, `Type::new`. No fields on this
            # node, so read the tokens: qualifier, `::`, name.
            kids = [c for c in node.children if c.type != "::"]
            if not kids:
                return
            mref = _txt(kids[-1], src).strip()
            qual = _txt(kids[0], src).strip() if len(kids) > 1 else ""
            if mref == "new":
                st.calls.append(("new " + _simple_type(qual), line, False,
                                 bool(loop_depth)))
            else:
                st.calls.append(
                    (((qual + "." + mref) if qual and len(qual) <= 80
                      else mref)[:200], line, False, bool(loop_depth)))
            return

        nm = node.child_by_field_name("name")
        if nm is None:
            st.bump("n_dynamic_calls")
            st.calls.append(("", line, True, bool(loop_depth)))
            return
        base = _txt(nm, src).strip()
        full = base
        obj = node.child_by_field_name("object")
        if obj is not None and obj.type in QUALIFIER_NODES:
            q = _txt(obj, src).strip()
            if len(q) <= 80 and "\n" not in q:
                full = q + "." + base
        st.calls.append((full[:200], line, False, bool(loop_depth)))

        # -- per-call metric columns, keyed on the simple name --------------
        if base == "stream":
            st.bump("n_streams")
        elif base == "parallelStream":
            st.bump("n_parallel_streams")
            st.bump("n_streams")
        elif base == "parallel":
            st.bump("n_parallel_streams")
        elif base == "collect" or full.startswith("Collectors."):
            st.bump("n_collectors")
        elif base == "valueOf" and full.split(".")[0] in (
                "Integer", "Long", "Double", "Float", "Short", "Byte",
                "Character", "Boolean"):
            st.bump("n_boxing_sites")
            if loop_depth:
                st.bump("n_boxing_in_loop")
        elif base in ("intValue", "longValue", "doubleValue", "floatValue",
                      "booleanValue", "shortValue", "byteValue", "charValue"):
            st.bump("n_boxing_sites")
            if loop_depth:
                st.bump("n_boxing_in_loop")
        elif base in ("setAccessible", "trySetAccessible", "privateLookupIn"):
            st.bump("n_setaccessible")
        elif base in ("load", "loadLibrary") and full.startswith(
                ("System.", "Runtime.")):
            st.bump("n_native_calls")
        elif base in ("ofConfined", "ofShared", "ofAuto", "global",
                      "allocateFrom", "allocate", "reinterpret", "ofAddress"):
            if full.startswith(("Arena.", "MemorySegment.", "SegmentAllocator.")):
                st.bump("n_ffm_arena")
        elif base in ("nativeLinker", "downcallHandle", "upcallStub",
                      "libraryLookup", "loaderLookup", "invokeExact"):
            st.bump("n_ffm_downcall")
        elif base in ("getUnsafe", "allocateMemory", "reallocateMemory",
                      "freeMemory", "objectFieldOffset", "staticFieldOffset",
                      "arrayBaseOffset", "copyMemory", "setMemory",
                      "putOrderedObject", "putOrderedLong", "allocateDirect",
                      "fullFence", "acquireFence", "releaseFence",
                      "loadLoadFence", "storeStoreFence"):
            st.bump("n_unsafe_calls")
        elif base in ("compareAndSet", "weakCompareAndSet", "getAndSet",
                      "incrementAndGet", "decrementAndGet", "getAndIncrement",
                      "getAndDecrement", "getAndAdd", "addAndGet",
                      "updateAndGet", "accumulateAndGet", "lazySet",
                      "compareAndExchange", "getAcquire", "setRelease",
                      "getPlain", "setOpaque"):
            st.bump("n_atomic_ops")
        elif base in ("wait", "notify", "notifyAll", "await", "join",
                      "sleep", "onSpinWait", "park", "awaitTermination"):
            st.bump("n_wait_calls")
        elif base in ("close", "closeQuietly", "shutdown", "shutdownNow",
                      "dispose", "free"):
            st.bump("n_close_calls")
        elif _opens_resource(base, full.rsplit(".", 1)[0] if "." in full else ""):
            st.bump("n_resource_open")
            if loop_depth:
                st.bump("io_in_loop")
        elif base == "compile" and full.startswith("Pattern."):
            st.bump("n_regex_compile")
            if loop_depth:
                st.bump("regex_in_loop")
        elif base in ("matches", "replaceAll", "replaceFirst", "split"):
            st.bump("n_regex_compile")
            if loop_depth:
                st.bump("regex_in_loop")
        elif base in ("ofNullable", "orElse", "orElseGet", "orElseThrow",
                      "isPresent", "ifPresent", "ifPresentOrElse") or (
                base in ("of", "empty") and full.startswith("Optional.")):
            st.bump("n_optional_ops")
        elif base in ("executeQuery", "executeUpdate", "executeBatch",
                      "prepareStatement", "prepareCall", "createQuery",
                      "createNativeQuery", "getResultList", "getSingleResult",
                      "findAll", "findById"):
            st.bump("n_query_calls")
            if loop_depth:
                st.bump("query_in_loop")
        elif base in ("ofPattern", "getInstance") and full.startswith(
                ("DateTimeFormatter.", "Calendar.", "NumberFormat.",
                 "DateFormat.")):
            st.bump("n_datefmt_ops")
        elif base in ("withInitial",) or full.startswith("ThreadLocal."):
            st.bump("n_threadlocal_ops")

        self._loop_counters(full, st, loop_depth)

    def _loop_counters(self, name: str, st: BodyStats, loop_depth: int) -> None:
        if not loop_depth:
            return
        base = name.rsplit(".", 1)[-1]
        for needle, col in self.LOOP_CALL_COUNTERS.items():
            if needle == base or needle == name:
                st.bump(col)

    def on_string(self, node: Any, text: str, src: bytes, st: BodyStats,
                  loop_depth: int) -> None:
        if node.type == "character_literal":
            return
        if SQL_RE.search(text):
            parent = node.parent
            if parent is not None and parent.type == "binary_expression":
                st.bump("n_query_calls")     # SQL assembled by concatenation
            if loop_depth:
                st.bump("query_in_loop")
        # A literal handed straight to Pattern.compile / matches / split is a
        # regex, and one built inside a loop is recompiled per element.
        parent = node.parent
        if parent is not None and parent.type == "argument_list":
            call = parent.parent
            if call is not None and call.type == "method_invocation":
                nm = call.child_by_field_name("name")
                if nm is not None and _txt(nm, src) in (
                        "compile", "matches", "replaceAll", "replaceFirst",
                        "split"):
                    st.bump("n_regex_lit")

    def on_node(self, node: Any, src: bytes, st: BodyStats,
                loop_depth: int, nest: int) -> None:
        t = node.type
        if t == "string_literal" and src[node.start_byte:
                                       node.start_byte + 3] == b'"""':
            # Count the LITERAL, not `multiline_string_fragment`: the
            # fragment splits on every embedded quote, so `{"k": 1}` yields
            # three of them and a JSON block reads as three text blocks.
            st.bump("n_text_blocks")
        if t == "binary_expression":
            op = _field_child(node, "operator")
            if op is None:
                return
            o = _txt(op, src)
            if o in ("&&", "||"):
                st.bump("n_logical")
            elif o in ("==", "!=", "<", ">", "<=", ">="):
                st.bump("n_cmp")
                right = node.child_by_field_name("right")
                left = node.child_by_field_name("left")
                if (right is not None and right.type == "null_literal") or (
                        left is not None and left.type == "null_literal"):
                    st.bump("n_null_check")
            elif o in ("&", "|", "^"):
                st.bump("n_bitop")
            elif o in ("<<", ">>", ">>>"):
                st.bump("n_shift")
            elif o == "+":
                if _has_string_operand(node, src):
                    st.bump("n_string_concat")
                    if loop_depth:
                        st.bump("concat_in_loop")
                else:
                    st.bump("n_arith")
            elif o in ("-", "*", "/", "%"):
                st.bump("n_arith")
        elif t == "assignment_expression":
            op = _field_child(node, "operator")
            if op is not None and _txt(op, src) != "=":
                st.bump("n_compound_assign")
                if _txt(op, src) == "+=" and _has_string_operand(node, src):
                    st.bump("n_string_concat")
                    if loop_depth:
                        st.bump("concat_in_loop")
        elif t == "cast_expression":
            ty = node.child_by_field_name("type")
            if ty is not None and ty.type in ("generic_type",):
                st.bump("n_unchecked_casts")
        elif t == "lambda_expression":
            st.bump("n_lambda")
        elif t == "return_statement":
            kids = node.named_children
            if kids and kids[0].type == "null_literal":
                st.bump("n_null_returns")
            if node.parent is not None and node.parent.type == "block" and \
                    node.parent.parent is not None and \
                    node.parent.parent.type in ("if_statement", "for_statement",
                                                "while_statement",
                                                "switch_expression"):
                st.bump("n_early_returns")
        elif t in ("break_statement", "continue_statement"):
            if node.named_children:          # labelled: a goto in all but name
                st.bump("n_gotos")
        elif t == "object_creation_expression":
            p = node.parent
            if p is not None and (
                    p.type == "return_statement"
                    or (p.type == "assignment_expression"
                        and (p.child_by_field_name("left") is not None
                             and p.child_by_field_name("left").type
                             == "field_access"))):
                st.bump("n_escaping_allocs")
        elif t == "synchronized_statement" and loop_depth:
            st.bump("lock_in_loop")
        elif t == "method_invocation" and loop_depth:
            nm = node.child_by_field_name("name")
            if nm is not None and _txt(nm, src) in ("lock", "tryLock",
                                                    "lockInterruptibly"):
                st.bump("lock_in_loop")

    # -- hazards -----------------------------------------------------------
    def hazard_of(self, callee: str) -> Optional[tuple[str, str]]:
        cat = HAZARD_CALLS.get(callee)
        if cat is not None:
            return callee, cat
        if callee.startswith("new "):
            return None
        base = callee.rsplit(".", 1)[-1]
        cat = HAZARD_CALLS.get(base)
        if cat is not None:
            return "*." + base, cat
        return None

    # -- resolution --------------------------------------------------------
    def is_external(self, name: str, base: str, fid: int) -> bool:
        """True when the call leaves this tree by design, not by blindness.

        Consulted only after in-tree resolution has already failed, so a repo
        that defines its own `Thread` or its own `close` is never mislabelled.
        """
        imports = self.file_imports.get(fid, {})
        if name.startswith("new "):
            tname = name[4:].strip()
            if tname in JDK_TYPES:
                return True
            target = imports.get(tname)
            return bool(target and self._out_of_tree(target))
        head = name.split(".")[0]
        if head in JDK_TYPES:
            return True
        target = imports.get(head)
        if target:
            return self._out_of_tree(target)
        if "." in name and base in JDK_METHODS:
            return True
        return False

    def _out_of_tree(self, target: str) -> bool:
        if target.split(".")[0] in JDK_PACKAGE_ROOTS:
            return True
        return not any(target.startswith(p) for p in self.pkg_roots)

    # -- imports, packages, JPMS -------------------------------------------
    def parse_imports(self, root: Any, rec: FileRec, bufs: Buffers) -> None:
        src = rec.data
        table = self.file_imports.setdefault(rec.fid, {})
        for n in root.named_children:
            if n.type == "package_declaration":
                pkg = ""
                for c in n.named_children:
                    if c.type in ("scoped_identifier", "identifier"):
                        pkg = _txt(c, src).strip()
                if pkg:
                    parts = pkg.split(".")
                    self.pkg_roots.add(".".join(parts[:3]) if len(parts) >= 3
                                       else pkg)
                continue
            if n.type != "import_declaration":
                continue
            txt = _txt(n, src)
            static = " static " in txt
            wildcard = "*" in txt
            target = ""
            for c in n.named_children:
                if c.type in ("scoped_identifier", "identifier"):
                    target = _txt(c, src).strip()
            if not target:
                continue
            simple = target.rsplit(".", 1)[-1]
            if not wildcard:
                table.setdefault(simple, target)
            bufs.imports.append(
                (rec.fid, target[:300], None, None,
                 "import static" if static else "import",
                 n.start_point[0] + 1,
                 int(self._out_of_tree(target)), 0, int(wildcard),
                 0, 0, 1))

    def parse_file_extra(self, root: Any, rec: FileRec,
                         db: sqlite3.Connection, bufs: Buffers) -> None:
        src = rec.data
        # JEP 511 module imports. The grammar is older than the feature, so the
        # statement lands in an ERROR node and has to be read from the text.
        for m in MODULE_IMPORT_RE.finditer(rec.text):
            line = rec.text[:m.start()].count("\n") + 1
            bufs.rows("jpms_directives").append(
                (rec.fid, "import-module", m.group(1), "", 0, 0, line))
            bufs.imports.append(
                (rec.fid, m.group(1)[:300], None, None, "import module",
                 line, 1, 0, 1, 0, 0, 1))
        for n in walk(root):
            if n.type == "requires_module_directive":
                mod = n.child_by_field_name("module")
                txt = _txt(n, src)
                bufs.rows("jpms_directives").append(
                    (rec.fid, "requires",
                     _txt(mod, src) if mod is not None else "", "",
                     int(" transitive" in txt), int(" static" in txt),
                     n.start_point[0] + 1))
            elif n.type in ("exports_module_directive", "opens_module_directive"):
                kids = [c for c in n.named_children
                        if c.type in ("scoped_identifier", "identifier")]
                bufs.rows("jpms_directives").append(
                    (rec.fid, n.type.split("_")[0],
                     _txt(kids[0], src) if kids else "",
                     ",".join(_txt(k, src) for k in kids[1:])[:200], 0, 0,
                     n.start_point[0] + 1))
            elif n.type in ("uses_module_directive", "provides_module_directive"):
                kids = [c for c in n.named_children
                        if c.type in ("scoped_identifier", "identifier")]
                bufs.rows("jpms_directives").append(
                    (rec.fid, n.type.split("_")[0],
                     _txt(kids[0], src) if kids else "",
                     ",".join(_txt(k, src) for k in kids[1:])[:200], 0, 0,
                     n.start_point[0] + 1))
        if GENERATED_ANNO_RE.search(rec.text[:4000]):
            db.execute("UPDATE files SET is_generated=1 WHERE id=?", (rec.fid,))

    # -- params ------------------------------------------------------------
    def emit_params(self, node: Any, rec: FileRec, sid: int,
                    bufs: Buffers) -> None:
        src = rec.data
        params = node.child_by_field_name(self.PARAMS_FIELD)
        if params is None:
            return
        if params.type == "identifier":              # `x -> ...`
            bufs.params.append((sid, 0, _txt(params, src)[:120], "", None,
                                0, 0, 0, 0, 0, 0, 1, 0))
            return
        pos = 0
        for p in params.named_children:
            if p.type in self.COMMENT_NODES:
                continue
            name = ""
            ptype = ""
            variadic = 0
            if p.type == "spread_parameter":
                variadic = 1
                kids = [c for c in p.named_children]
                if kids:
                    ptype = _txt(kids[0], src).strip() + "..."
                for c in kids:
                    if c.type == "variable_declarator":
                        nm = c.child_by_field_name("name")
                        if nm is not None:
                            name = _txt(nm, src).strip()
            elif p.type in ("formal_parameter", "receiver_parameter"):
                tn = p.child_by_field_name("type")
                ptype = _txt(tn, src).strip() if tn is not None else ""
                nm = p.child_by_field_name("name")
                name = _txt(nm, src).strip() if nm is not None else ""
            elif p.type == "identifier":             # inferred lambda params
                name = _txt(p, src).strip()
            else:
                continue
            annos = _annotation_names(p, src)
            bufs.params.append(
                (sid, pos, (name or "?")[:120], ptype[:200], None,
                 int(bool(annos & {"Nullable", "CheckForNull"})), variadic,
                 0, 0, int(bool(annos & {"Nullable", "CheckForNull"})),
                 int("<" in ptype), int(not ptype),
                 ptype.count("<") + ptype.count("[")))
            pos += 1

    def emit_attributes(self, node: Any, rec: FileRec, sid: int,
                        bufs: Buffers) -> None:
        src = rec.data
        for c in node.named_children:
            if c.type != "modifiers":
                continue
            for a in c.named_children:
                if a.type not in ("annotation", "marker_annotation"):
                    continue
                nm = a.child_by_field_name("name")
                args = a.child_by_field_name("arguments")
                bufs.attributes.append(
                    (sid, rec.fid,
                     (_txt(nm, src).rsplit(".", 1)[-1] if nm is not None
                      else "?")[:120],
                     _txt(args, src)[:200] if args is not None else None,
                     a.start_point[0] + 1))
            break

    # -- the language's own tables ----------------------------------------
    def type_extra(self, node: Any, rec: FileRec, db: sqlite3.Connection,
                   bufs: Buffers, sid: int, scope: Scope) -> None:
        src = rec.data
        name = self.node_name(node, rec)
        kind = self.TYPE_KINDS.get(node.type, "type")

        for parent, rel in _supertype_pairs(node, src):
            bufs.rows("type_relations").append(
                (sid, rec.fid, name[:120], kind, parent[:120], rel,
                 int("<" in parent), node.start_point[0] + 1))
        self.parents[name] = [p for p, _ in _supertype_pairs(node, src)]

        tp = node.child_by_field_name("type_parameters")
        if tp is not None:
            for t in tp.named_children:
                if t.type != "type_parameter":
                    continue
                tname = self.node_name(t, rec)
                bound = ""
                for c in t.named_children:
                    if c.type == "type_bound":
                        bound = _txt(c, src).strip()
                bufs.rows("generics").append(
                    (sid, rec.fid, name[:120], tname[:80], bound[:200],
                     int(name in bound), 1, t.start_point[0] + 1))

        body = node.child_by_field_name("body")
        if body is None:
            return
        vol: set[str] = set()
        stat: set[str] = set()
        tls: set[str] = set()
        ordinal = 0
        # A record's components are its fields; they have no field_declaration.
        comps = node.child_by_field_name("parameters")
        if comps is not None:
            for c in comps.named_children:
                if c.type != "formal_parameter":
                    continue
                tn = c.child_by_field_name("type")
                nm = c.child_by_field_name("name")
                ftype = _txt(tn, src).strip() if tn is not None else ""
                fname = _txt(nm, src).strip() if nm is not None else ""
                bufs.fields.append(
                    (sid, ordinal, fname[:120], ftype[:200], "private",
                     c.start_point[0] + 1, 0, 1, 0, 0,
                     int(_is_collection(ftype)), 0, 0,
                     ftype.count("<") + ftype.count("[")))
                ordinal += 1
        for fl in body.named_children:
            if fl.type != "field_declaration":
                continue
            mods = _modifiers_text(fl, src)
            tn = fl.child_by_field_name("type")
            ftype = _txt(tn, src).strip() if tn is not None else ""
            is_static = 1 if re.search(r'\bstatic\b', mods) else 0
            is_final = 1 if re.search(r'\bfinal\b', mods) else 0
            is_volatile = 1 if re.search(r'\bvolatile\b', mods) else 0
            vis = ("public" if "public" in mods else
                   "protected" if "protected" in mods else
                   "private" if "private" in mods else "package")
            for d in fl.named_children:
                if d.type != "variable_declarator":
                    continue
                nm = d.child_by_field_name("name")
                fname = _txt(nm, src).strip() if nm is not None else ""
                if is_volatile:
                    vol.add(fname)
                if is_static and not is_final:
                    stat.add(fname)
                if "ThreadLocal" in ftype:
                    tls.add(fname)
                bufs.fields.append(
                    (sid, ordinal, fname[:120], ftype[:200], vis,
                     fl.start_point[0] + 1, is_static, is_final,
                     1 - is_final, int(_is_nullable(ftype)),
                     int(_is_collection(ftype)), 0,
                     int(d.child_by_field_name("value") is not None),
                     ftype.count("<") + ftype.count("[")))
                ordinal += 1
        if vol:
            self.volatile_fields[name] = vol
        if stat:
            self.static_fields[name] = stat
        if tls:
            self.threadlocal_fields[name] = tls

    def function_extra(self, node: Any, rec: FileRec, db: sqlite3.Connection,
                       bufs: Buffers, sid: int, scope: Scope,
                       stats: BodyStats) -> None:
        src = rec.data
        name = self.node_name(node, rec)
        kind = self.FUNC_KINDS.get(node.type, "method")
        owner = scope.type_name
        fid = rec.fid

        # A constructor is reachable as `new Foo`; register it so an allocation
        # resolves to the constructor rather than to the class symbol.
        if kind == "constructor" and name:
            self.by_qual.setdefault("new " + name, sid)

        # -- declared exceptions --------------------------------------------
        for c in node.named_children:
            if c.type != "throws":
                continue
            for t in c.named_children:
                if t.type in ("type_identifier", "scoped_type_identifier",
                              "generic_type"):
                    tn = _simple_type(_txt(t, src))
                    bufs.rows("exceptions").append(
                        (sid, fid, "throws", tn[:120],
                         int(tn in BROAD_EXCEPTIONS), 0, 0, 0, 0,
                         c.start_point[0] + 1))

        # -- method-level type parameters -----------------------------------
        tp = node.child_by_field_name("type_parameters")
        if tp is not None:
            for t in tp.named_children:
                if t.type != "type_parameter":
                    continue
                tname = self.node_name(t, rec)
                bound = ""
                for c in t.named_children:
                    if c.type == "type_bound":
                        bound = _txt(c, src).strip()
                bufs.rows("generics").append(
                    (sid, fid, ("%s.%s" % (owner, name))[:120], tname[:80],
                     bound[:200], int(tname in bound), 0,
                     t.start_point[0] + 1))

        # -- an @Override, or an inherited name we can name a parent for -----
        annos = _annotation_names(node, src)
        if kind in ("method",) and name:
            parents = self.parents.get(owner, [])
            if "Override" in annos or parents:
                params = node.child_by_field_name("parameters")
                n_par = len([c for c in params.named_children
                             if c.type in ("formal_parameter",
                                           "spread_parameter")]) \
                    if params is not None else 0
                bufs.rows("overrides").append(
                    (sid, fid, name[:120], owner[:120],
                     (parents[0] if parents else "")[:120],
                     int("Override" in annos),
                     int(bool(annos & FRAMEWORK_ANNOTATIONS)
                         or name in HANDLER_METHODS),
                     n_par, node.start_point[0] + 1))

        body = node.child_by_field_name(self.BODY_FIELD) or node
        btxt = _txt(body, src)
        closes = ".close()" in btxt or "closeQuietly" in btxt
        loop_types = set(self.LOOP_NODES)
        volatiles = self.volatile_fields.get(owner, set())
        statics = self.static_fields.get(owner, set())
        tlocals = self.threadlocal_fields.get(owner, set())
        n_vol = 0
        n_static_write = 0
        n_tl_ops = 0
        n_tl_remove = 0
        acq = 0

        for n in walk(body):
            t = n.type
            if t == "synchronized_statement":
                depth = _ancestor_loop_depth(n, body, loop_types)
                target = ""
                for c in n.named_children:
                    if c.type == "parenthesized_expression":
                        target = _txt(c, src).strip("() \t\n")[:80]
                        break
                region = n.child_by_field_name("body")
                flags = _region_flags(region, src) if region is not None \
                    else (0, 0, 0, 0, 0)
                bufs.rows("lock_ops").append(
                    (sid, fid, target or "this", "acquire", "synchronized",
                     acq, int(depth > 0), flags[0], flags[1], flags[2],
                     flags[3], flags[4], n.start_point[0] + 1))
                bufs.rows("lock_ops").append(
                    (sid, fid, target or "this", "release", "synchronized",
                     acq, int(depth > 0), 0, 0, 0, 0, 0,
                     n.end_point[0] + 1))
                acq += 1
            elif t == "method_invocation":
                nm = n.child_by_field_name("name")
                if nm is None:
                    continue
                mname = _txt(nm, src)
                obj = n.child_by_field_name("object")
                recv = _txt(obj, src).strip()[:80] if (
                    obj is not None and obj.type in QUALIFIER_NODES) else ""
                if mname in ("lock", "lockInterruptibly", "tryLock"):
                    depth = _ancestor_loop_depth(n, body, loop_types)
                    region = _enclosing_region(n, body)
                    flags = _region_flags(region, src) if region is not None \
                        else (0, 0, 0, 0, 0)
                    bufs.rows("lock_ops").append(
                        (sid, fid, recv or "?", "acquire",
                         "rwlock" if "ReadLock" in recv or "WriteLock" in recv
                         else "lock",
                         acq, int(depth > 0), flags[0], flags[1], flags[2],
                         flags[3], flags[4], n.start_point[0] + 1))
                    acq += 1
                elif mname in ("unlock", "unlockRead", "unlockWrite"):
                    bufs.rows("lock_ops").append(
                        (sid, fid, recv or "?", "release", "lock",
                         max(0, acq - 1), 0, 0, 0, 0, 0, 0,
                         n.start_point[0] + 1))
                elif _opens_resource(mname, recv):
                    depth = _ancestor_loop_depth(n, body, loop_types)
                    bufs.rows("resources").append(
                        (sid, fid, "", mname[:80],
                         ("%s.%s" % (recv, mname) if recv else mname)[:120],
                         int(_in_try_resources(n, body)), int(closes),
                         int(depth > 0), n.start_point[0] + 1))
                if recv and recv in tlocals:
                    if mname in ("set", "get", "withInitial"):
                        n_tl_ops += 1
                    elif mname == "remove":
                        n_tl_remove += 1
            elif t == "object_creation_expression":
                ty = n.child_by_field_name("type")
                tname = _simple_type(_txt(ty, src)) if ty is not None else ""
                if tname in RESOURCE_TYPES:
                    depth = _ancestor_loop_depth(n, body, loop_types)
                    bufs.rows("resources").append(
                        (sid, fid, "", tname[:80], ("new " + tname)[:120],
                         int(_in_try_resources(n, body)), int(closes),
                         int(depth > 0), n.start_point[0] + 1))
                if "ThreadLocal" in tname:
                    n_tl_ops += 1
            elif t == "resource":
                tn = n.child_by_field_name("type")
                nm = n.child_by_field_name("name")
                val = n.child_by_field_name("value")
                bufs.rows("resources").append(
                    (sid, fid,
                     _txt(nm, src)[:80] if nm is not None else "",
                     (_txt(tn, src) if tn is not None else "")[:80],
                     (_txt(val, src)[:120] if val is not None else ""),
                     1, 1, 0, n.start_point[0] + 1))
            elif t == "catch_clause":
                cb = n.child_by_field_name("body")
                ctxt = _txt(cb, src) if cb is not None else ""
                empty = int(cb is not None and not cb.named_children)
                rethrow = int("throw " in ctxt)
                logs = int("log" in ctxt.lower() or "printStackTrace" in ctxt)
                depth = _ancestor_loop_depth(n, body, loop_types)
                for c in n.named_children:
                    if c.type != "catch_formal_parameter":
                        continue
                    for ct in c.named_children:
                        if ct.type != "catch_type":
                            continue
                        for tt in ct.named_children:
                            tn = _simple_type(_txt(tt, src))
                            bufs.rows("exceptions").append(
                                (sid, fid, "catch", tn[:120],
                                 int(tn in BROAD_EXCEPTIONS), empty, rethrow,
                                 logs, int(depth > 0), n.start_point[0] + 1))
            elif t == "throw_statement":
                kids = n.named_children
                tn = ""
                if kids and kids[0].type == "object_creation_expression":
                    ty = kids[0].child_by_field_name("type")
                    tn = _simple_type(_txt(ty, src)) if ty is not None else ""
                depth = _ancestor_loop_depth(n, body, loop_types)
                bufs.rows("exceptions").append(
                    (sid, fid, "throw", tn[:120],
                     int(tn in BROAD_EXCEPTIONS), 0, 0, 0, int(depth > 0),
                     n.start_point[0] + 1))
            elif t == "identifier":
                txt = _txt(n, src)
                if txt in volatiles:
                    n_vol += 1
            elif t == "assignment_expression":
                left = n.child_by_field_name("left")
                if left is not None:
                    lt = _txt(left, src).strip()
                    if lt.rsplit(".", 1)[-1] in statics:
                        n_static_write += 1
            elif t == "if_statement" and _is_double_checked(n, src):
                bufs.add_hazard(sid, "double-checked-locking", "lock", 1,
                                n.start_point[0] + 1)

        updates: dict[str, int] = {}
        if n_vol:
            updates["n_volatile_access"] = n_vol
        if n_static_write:
            updates["n_static_writes"] = n_static_write
        if n_tl_ops:
            updates["n_threadlocal_ops"] = n_tl_ops
        if n_tl_remove:
            updates["n_threadlocal_remove"] = n_tl_remove
        if updates:
            # Buffered: symbols are written in one executemany AFTER the parse
            # loop, so an UPDATE issued here would match no row -- which is
            # exactly what happened: n_threadlocal_ops silently went from 117
            # to 0 on netty and threadlocal-leak-on-pooled returned nothing.
            for k, v in updates.items():
                self._sym_updates.append((k, v, sid))
        if re.search(r'\bnative\b', _modifiers_text(node, src)):
            bufs.add_hazard(sid, "native-method", "jni", 1,
                            node.start_point[0] + 1)

    # -- manifests and meta -------------------------------------------------
    def parse_manifests(self, root: str, db: sqlite3.Connection) -> None:
        """Read the declared Java release.

        It decides whether half the findings here even apply: virtual threads
        do not exist below 21, records below 16, and JEP 491's removal of
        synchronized pinning landed in 24.
        """
        for fn, pats in (
            ("pom.xml", (r'<maven\.compiler\.release>\s*(\d+)',
                         r'<maven\.compiler\.source>\s*(\d+)',
                         r'<release>\s*(\d+)\s*</release>',
                         r'<source>\s*(\d+)\s*</source>',
                         r'<java\.version>\s*(?:1\.)?(\d+)')),
            ("build.gradle", (r'sourceCompatibility\s*=?\s*[\'"]?(?:1\.)?(\d+)',
                              r'JavaVersion\.VERSION_(?:1_)?(\d+)',
                              r'languageVersion.*?JavaLanguageVersion\.of\((\d+)\)')),
            ("build.gradle.kts", (r'JavaVersion\.VERSION_(?:1_)?(\d+)',
                                  r'JavaLanguageVersion\.of\((\d+)\)')),
        ):
            path = os.path.join(root, fn)
            if not os.path.isfile(path):
                continue
            try:
                text = open(path, encoding="utf-8", errors="replace").read()
            except OSError:
                continue
            for pat in pats:
                m = re.search(pat, text, re.S)
                if m:
                    self.java_release = m.group(1)
                    break
            if self.java_release:
                break

    def post_build(self, db: sqlite3.Connection) -> None:
        if self._sym_updates:
            by_col: dict[str, list[tuple[int, int]]] = {}
            for col, val, sid in self._sym_updates:
                by_col.setdefault(col, []).append((val, sid))
            for col, rows in by_col.items():
                db.executemany(
                    "UPDATE symbols SET %s=%s+? WHERE id=?" % (col, col),
                    rows)
            self._sym_updates.clear()
        rel = self.java_release
        try:
            reln = int(rel)
        except ValueError:
            reln = 0
        meta_rows = (
            ("grammar_note", GRAMMAR_NOTE),
            ("grammar_abi", "14 (tree-sitter-java 0.23.5)"),
            ("java_release", rel or "not declared in pom.xml/build.gradle"),
            ("virtual_threads",
             "available (release >= 21)" if reln >= 21 else
             "NOT available at the declared release -- every virtual-thread "
             "row below is inapplicable" if reln else
             "unknown: no release declared"),
            ("jep491_pinning",
             "synchronized no longer pins (release >= 24); only JNI and FFM "
             "downcalls do" if reln >= 24 else
             "synchronized STILL pins at the declared release (< 24)"
             if reln else
             "unknown: no release declared, assuming 24+ per TARGET"),
            ("packages", ", ".join(sorted(self.pkg_roots)[:12]) or "(none seen)"),
        )
        db.executemany("INSERT OR REPLACE INTO meta(key,value) VALUES(?,?)",
                       meta_rows)

    def flush_extra(self, db: sqlite3.Connection, bufs: Buffers) -> None:
        for tbl, sql in (
            ("type_relations",
             "INSERT INTO type_relations(child_id,file_id,child_name,child_kind,"
             "parent_name,kind,is_generic,line) VALUES(?,?,?,?,?,?,?,?)"),
            ("overrides",
             "INSERT INTO overrides(symbol_id,file_id,method_name,owner_type,"
             "parent_type,is_annotated,is_framework_entry,n_params,line) "
             "VALUES(?,?,?,?,?,?,?,?,?)"),
            ("exceptions",
             "INSERT INTO exceptions(symbol_id,file_id,kind,type,is_broad,"
             "is_empty,rethrows,logs,in_loop,line) "
             "VALUES(?,?,?,?,?,?,?,?,?,?)"),
            ("generics",
             "INSERT INTO generics(symbol_id,file_id,owner,name,bound,"
             "is_self_referential,on_type,line) VALUES(?,?,?,?,?,?,?,?)"),
            ("resources",
             "INSERT INTO resources(symbol_id,file_id,name,type,opened_by,"
             "in_try_resources,closed_in_fn,in_loop,line) "
             "VALUES(?,?,?,?,?,?,?,?,?)"),
            ("lock_ops",
             "INSERT INTO lock_ops(symbol_id,file_id,lock_name,op,kind,"
             "acq_order,in_loop,holds_io,holds_sleep,holds_alloc,holds_call,"
             "region_sloc,line) VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?)"),
            ("jpms_directives",
             "INSERT INTO jpms_directives(file_id,kind,module_name,target,"
             "is_transitive,is_static,line) VALUES(?,?,?,?,?,?,?)"),
        ):
            rows = bufs.extra.get(tbl)
            if rows:
                db.executemany(sql, rows)

def _txt(node: Any, src: bytes) -> str:
    return src[node.start_byte:node.end_byte].decode("utf-8", "replace")

def _field_child(node: Any, field: str) -> Optional[Any]:
    """A field whose value is an unnamed token, which `child_by_field_name`
    still returns but `named_children` never will -- operators, mainly."""
    for i in range(node.child_count):
        if node.field_name_for_child(i) == field:
            return node.child(i)
    return None

def _modifiers_text(node: Any, src: bytes) -> str:
    for c in node.named_children:
        if c.type == "modifiers":
            return _txt(c, src)
    return ""

def _annotation_names(node: Any, src: bytes) -> set[str]:
    out: set[str] = set()
    for c in node.named_children:
        if c.type != "modifiers":
            continue
        for a in c.named_children:
            if a.type in ("annotation", "marker_annotation"):
                nm = a.child_by_field_name("name")
                if nm is not None:
                    out.add(_txt(nm, src).rsplit(".", 1)[-1])
        break
    return out

def _simple_type(text: str) -> str:
    """`java.util.List<String>` -> `List`. Resolution is by simple name, so a
    qualified or parameterised spelling has to collapse to the same key."""
    t = text.strip()
    t = t.split("<")[0].split("[")[0].strip()
    return t.rsplit(".", 1)[-1]

def _supertype_pairs(node: Any, src: bytes) -> list[tuple[str, str]]:
    """(parent simple name, relation) for extends / implements / permits."""
    out: list[tuple[str, str]] = []
    for field, rel in (("superclass", "extends"),
                       ("interfaces", "implements"),
                       ("permits", "permits")):
        c = node.child_by_field_name(field)
        if c is None:
            continue
        # `extends A`, `implements A, B`, `permits A, B` -- the names sit
        # either directly under the clause or inside a `type_list`.
        holders = [c]
        for k in c.named_children:
            if k.type == "type_list":
                holders = [k]
                break
        for h in holders:
            for t in h.named_children:
                if t.type in ("type_identifier", "scoped_type_identifier",
                              "generic_type"):
                    out.append((_simple_type(_txt(t, src)), rel))
    # An interface's `extends` list is also modelled as `interfaces`.
    if node.type == "interface_declaration":
        c = node.child_by_field_name("interfaces")
        if c is None:
            for k in node.named_children:
                if k.type == "extends_interfaces":
                    for t in walk(k):
                        if t.type in ("type_identifier",
                                      "scoped_type_identifier", "generic_type"):
                            out.append((_simple_type(_txt(t, src)), "extends"))
    return out

def _supertype_names(node: Any, src: bytes) -> list[str]:
    return [p for p, _ in _supertype_pairs(node, src)]

def _count_type_params(node: Any) -> int:
    tp = node.child_by_field_name("type_parameters")
    if tp is None:
        return 0
    return sum(1 for c in tp.named_children if c.type == "type_parameter")

def _count_params(params: Any) -> int:
    """Declared parameters, counting a lambda's bare `x ->` as one."""
    if params is None:
        return 0
    if params.type == "identifier":
        return 1
    return sum(1 for c in params.named_children
               if c.type in ("formal_parameter", "spread_parameter",
                             "receiver_parameter", "identifier"))

def _is_collection(t: str) -> bool:
    head = _simple_type(t)
    return ("[" in t or head in (
        "List", "ArrayList", "LinkedList", "Map", "HashMap", "TreeMap",
        "LinkedHashMap", "ConcurrentHashMap", "Set", "HashSet", "TreeSet",
        "LinkedHashSet", "Collection", "Queue", "Deque", "ArrayDeque"))

def _is_nullable(t: str) -> bool:
    head = _simple_type(t)
    return head not in ("int", "long", "short", "byte", "char", "float",
                        "double", "boolean", "void")

def _has_string_operand(node: Any, src: bytes) -> bool:
    """A `+` with a string on either side is concatenation, not arithmetic."""
    for field in ("left", "right"):
        c = node.child_by_field_name(field)
        if c is None:
            continue
        if c.type == "string_literal":
            return True
        if c.type == "binary_expression" and _has_string_operand(c, src):
            return True
    return False

def _ancestor_loop_depth(node: Any, stop: Any, loop_types: set) -> int:
    d = 0
    cur = node.parent
    while cur is not None and cur.id != stop.id:
        if cur.type in loop_types:
            d += 1
        cur = cur.parent
    return d

def _in_try_resources(node: Any, stop: Any) -> bool:
    cur = node.parent
    while cur is not None and cur.id != stop.id:
        if cur.type == "resource_specification":
            return True
        cur = cur.parent
    return False

def _enclosing_region(node: Any, stop: Any) -> Optional[Any]:
    """The block a `lock()` call guards.

    Idiomatic Java is `lock(); try { ... } finally { unlock(); }`, so the try
    block that follows is the critical section. When there is none, the
    enclosing block is the best available over-approximation, and the query
    that reads `holds_io` says so.
    """
    stmt = node
    while stmt is not None and stmt.parent is not None and \
            stmt.parent.type != "block":
        stmt = stmt.parent
    if stmt is None:
        return None
    nxt = stmt.next_named_sibling
    if nxt is not None and nxt.type in ("try_statement",
                                        "try_with_resources_statement"):
        return nxt.child_by_field_name("body") or nxt
    return stmt.parent

_IO_RE = re.compile(r'\.(?:read|write|flush|send|receive|connect|accept|'
                    r'execute|executeQuery|executeUpdate|newInputStream|'
                    r'newOutputStream|transferTo|copy)\s*\(')

_SLEEP_RE = re.compile(r'\.(?:sleep|await|join|wait|park|awaitTermination|'
                       r'get)\s*\(|Thread\.sleep')

def _region_flags(region: Any, src: bytes) -> tuple[int, int, int, int, int]:
    """(holds_io, holds_sleep, holds_alloc, holds_call, region_sloc)."""
    txt = _txt(region, src)
    n_call = 0
    n_alloc = 0
    for n in walk(region):
        if n.type == "method_invocation":
            n_call += 1
        elif n.type in ("object_creation_expression",
                        "array_creation_expression"):
            n_alloc += 1
    return (int(bool(_IO_RE.search(txt))), int(bool(_SLEEP_RE.search(txt))),
            n_alloc, n_call,
            sum(1 for l in txt.splitlines() if l.strip()))

def _is_double_checked(node: Any, src: bytes) -> bool:
    """`if (x == null) { synchronized (..) { if (x == null) { .. } } }`.

    Correct only when the field is volatile, and the Java memory model makes
    the non-volatile form silently broken on real hardware. Detected
    structurally rather than by regex so a formatted-differently instance is
    still caught.
    """
    cond = node.child_by_field_name("condition")
    if cond is None or "null" not in _txt(cond, src):
        return False
    cons = node.child_by_field_name("consequence")
    if cons is None:
        return False
    for n in walk(cons):
        if n.type != "synchronized_statement":
            continue
        for inner in walk(n):
            if inner.type == "if_statement" and inner.id != node.id:
                ic = inner.child_by_field_name("condition")
                if ic is not None and "null" in _txt(ic, src):
                    return True
    return False

JavaAnalyzer.QUERIES = [
(
    "graph-blindspots",
    "Read this first: where the call graph cannot see",
    "ANSWERS how much of every other answer here is guesswork. Java is the\n"
    "     worst case for this: Spring, JPA, JUnit, ServiceLoader and every\n"
    "     `Class.forName` invoke code with no call site in the source, so a\n"
    "     method can be live and still have fan_in=0.\n"
    "ACT external calls leave the tree by design (JDK, dependencies) and are\n"
    "     NOT counted as blindness. Unresolved means we lost it -- usually an\n"
    "     interface method with several implementations. Read reflect_ and\n"
    "     framework_entries as the size of the graph that does not exist.\n"
    "MISLEADS sql_ops comes from a bare METHOD NAME list, so findAll,\n"
    "     getSingleResult and friends match ANY receiver. In a codebase with\n"
    "     no database at all these still fire. Check that the owner type is a\n"
    "     repository or a Connection before believing the row.\n"
    "     a resolved edge can still be wrong: a call on an interface\n"
    "     resolves to whichever single implementation exists, and where two\n"
    "     exist this refuses to guess and lands in unresolved instead. An\n"
    "     allocation resolves to the constructor when one is declared and to\n"
    "     nothing when the class uses the default constructor.",
    """SELECT m.name AS module_, COUNT(DISTINCT s.id) AS fns,
        COALESCE(SUM(s.n_calls),0) AS calls,
        COALESCE(SUM(s.n_external_calls),0) AS external,
        COALESCE(SUM(s.n_unresolved_calls),0) AS unresolved,
        COALESCE(SUM(s.n_reflection),0) AS reflect_,
        COALESCE(SUM(s.is_handler),0) AS handlers,
        (SELECT COUNT(*) FROM overrides o JOIN symbols os ON os.id=o.symbol_id
         WHERE os.module_id=m.id AND o.is_framework_entry=1)
            AS framework_entries,
        CAST(100.0*SUM(s.n_unresolved_calls)/NULLIF(SUM(s.n_calls),0) AS INT)
            AS pct_blind
    FROM symbols s JOIN modules m ON m.id=s.module_id
    WHERE s.kind IN ('function','method','constructor') AND m.name LIKE :mod
    GROUP BY m.id HAVING calls > 0
    ORDER BY unresolved DESC LIMIT :lim"""),
(
    "reflection-frontier",
    "Public entry points that reach Class.forName or setAccessible",
    "ANSWERS the two lists you cannot write by hand: what belongs in\n"
    "     --add-opens, and what belongs in a native-image reflect-config.json.\n"
    "     Anything reachable from the API surface may be invoked reflectively\n"
    "     at run time, and everything else may be closed.\n"
    "ACT for each row, name the classes actually opened and pin them. A\n"
    "     setAccessible on a JDK internal is a future JEP away from throwing.\n"
    "MISLEADS depth is capped at 4 hops and only RESOLVED edges are walked, so\n"
    "     this is a floor, never a ceiling. Reflection that goes through a\n"
    "     framework -- which is most of it -- has no edge at all and cannot\n"
    "     appear. Check graph-blindspots for the module first.",
    """WITH RECURSIVE roots(id) AS (
        SELECT id FROM symbols
        WHERE (is_handler=1 OR is_entrypoint=1 OR (is_public=1 AND fan_in=0))
          AND kind IN ('function','method','constructor')),
    down(sym, depth) AS (
        SELECT id, 0 FROM roots
        UNION
        SELECT e.callee_id, d.depth+1 FROM down d
        JOIN edges e ON e.caller_id=d.sym
        WHERE d.depth < 4 AND e.is_self=0),   -- depth bound: 4 hops
    best AS (SELECT sym, MIN(depth) AS depth FROM down GROUP BY sym)
    SELECT s.name, s.owner_type AS owner, b.depth AS hops_from_api,
        s.n_reflection AS reflect_ops, s.n_setaccessible AS set_accessible,
        s.n_serialization AS deser_ops, s.n_jni AS jni,
        s.fan_in, s.is_public AS public_,
        f.path || ':' || s.line_start AS at
    FROM best b JOIN symbols s ON s.id=b.sym
    JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE (s.n_reflection > 0 OR s.n_setaccessible > 0)
      AND f.is_test=0 AND COALESCE(m.name,'') LIKE :mod
    ORDER BY b.depth ASC, s.n_setaccessible DESC, s.n_reflection DESC
    LIMIT :lim"""),
(
    "deserialization-reachability",
    "Deserialization and JNDI sinks reachable from an entry point",
    "ANSWERS the shape behind every Java RCE of the last decade: attacker\n"
    "     bytes reach readObject, readValue with default typing enabled,\n"
    "     Yaml.load, XMLDecoder or InitialContext.lookup.\n"
    "ACT put an ObjectInputFilter on every stream you did not create, or stop\n"
    "     deserializing untrusted input at all. serial_types_no_uid counts\n"
    "     Serializable types in the same module with no serialVersionUID --\n"
    "     each one is a class whose wire format changes silently on rebuild.\n"
    "MISLEADS depth is capped at 4 hops over resolved edges only. A sink is\n"
    "     not a vulnerability: it is a vulnerability when the bytes are\n"
    "     attacker-controlled, which this cannot see. Jackson without\n"
    "     enableDefaultTyping is not the gadget-chain shape.",
    """WITH RECURSIVE roots(id) AS (
        SELECT id FROM symbols
        WHERE (is_handler=1 OR is_entrypoint=1 OR (is_public=1 AND fan_in=0))
          AND kind IN ('function','method','constructor')),
    down(sym, depth) AS (
        SELECT id, 0 FROM roots
        UNION
        SELECT e.callee_id, d.depth+1 FROM down d
        JOIN edges e ON e.caller_id=d.sym
        WHERE d.depth < 4 AND e.is_self=0),   -- depth bound: 4 hops
    best AS (SELECT sym, MIN(depth) AS depth FROM down GROUP BY sym)
    SELECT s.name, s.owner_type AS owner, b.depth AS hops_from_api,
        s.n_serialization AS deser_ops, s.n_reflection AS reflect_ops,
        (SELECT GROUP_CONCAT(DISTINCT h.pattern) FROM hazards h
         WHERE h.symbol_id=s.id AND h.category='serialization') AS sinks,
        (SELECT COUNT(*) FROM symbols t
         WHERE t.module_id=s.module_id AND t.is_serializable=1
           AND t.has_serial_uid=0) AS serial_types_no_uid,
        s.fan_in, f.path || ':' || s.line_start AS at
    FROM best b JOIN symbols s ON s.id=b.sym
    JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_serialization > 0 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY b.depth ASC, s.n_serialization DESC LIMIT :lim"""),
(
    "resource-open-never-closed",
    "Opened here, closed somewhere else -- or nowhere",
    "ANSWERS the cross-function OS_OPEN_STREAM: the open and the close live in\n"
    "     different methods, so no per-file checker can pair them. A stream\n"
    "     opened in a factory and returned is fine; one opened in a leaf that\n"
    "     nobody closes is a descriptor leak that shows up as EMFILE in\n"
    "     production and nowhere in the tests.\n"
    "ACT wrap it in try-with-resources, or return it and name the method so\n"
    "     the caller knows it owns a closeable. callers_that_close is the\n"
    "     evidence that someone already does.\n"
    "MISLEADS a factory that deliberately hands back an open resource is\n"
    "     correct and appears here -- check whether return_type is a Closeable.\n"
    "     closed_in_fn is a text scan for .close() in the same body, so a close\n"
    "     one frame deeper reads as absent.",
    """WITH RECURSIVE down(sym, depth) AS (
        SELECT symbol_id, 0 FROM resources WHERE in_try_resources=0
        UNION
        SELECT e.callee_id, d.depth+1 FROM down d
        JOIN edges e ON e.caller_id=d.sym
        WHERE d.depth < 3 AND e.is_self=0)    -- depth bound: 3 hops
    SELECT s.name, s.owner_type AS owner,
        COUNT(r.id) AS opens, SUM(r.in_loop) AS opens_in_loop,
        SUM(r.in_try_resources) AS in_twr, s.n_close_calls AS closes,
        s.n_finalizers AS finalizers, s.return_type,
        GROUP_CONCAT(DISTINCT r.type) AS types,
        (SELECT COUNT(*) FROM edges e2 JOIN symbols c2 ON c2.id=e2.caller_id
         WHERE e2.callee_id=s.id
           AND (c2.n_close_calls > 0 OR c2.n_try_resources > 0))
            AS callers_that_close,
        (SELECT COUNT(*) FROM down d WHERE d.sym=s.id) AS on_open_path,
        s.fan_in, f.path || ':' || MIN(r.line) AS at
    FROM resources r
    JOIN symbols s ON s.id=r.symbol_id
    JOIN files f ON f.id=r.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE r.in_try_resources=0 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    GROUP BY s.id
    HAVING closes = 0 AND callers_that_close = 0
    ORDER BY opens_in_loop DESC, opens DESC, s.fan_in DESC LIMIT :lim"""),
(
    "lock-order-inversion",
    "Two locks taken in opposite orders in different methods",
    "ANSWERS the deadlock ring: method A takes L1 then L2, method B takes L2\n"
    "     then L1. Nothing fails until both run at once, which is why it ships.\n"
    "     acq_order is recorded per acquisition per method, so this is a real\n"
    "     ordering comparison and not a co-occurrence count.\n"
    "ACT impose one global lock order and document it. Where you cannot, use\n"
    "     tryLock with a timeout so the ring breaks instead of hanging.\n"
    "MISLEADS lock identity is the receiver's TEXT: `this.lock` and `lock` are\n"
    "     two names for one monitor and read as two locks, while two different\n"
    "     objects both spelled `lock` read as one. Two methods that can never\n"
    "     run concurrently cannot deadlock however they order their locks.",
    """SELECT a.first_lock AS lock_1, a.second_lock AS lock_2,
        sa.name AS takes_1_then_2, sa.owner_type AS owner_a,
        sb.name AS takes_2_then_1, sb.owner_type AS owner_b,
        sa.n_lock_acquire AS a_acquires, sb.n_lock_acquire AS b_acquires,
        MAX(sa.fan_in, sb.fan_in) AS max_fan_in,
        fa.path || ':' || a.line AS at_a,
        fb.path || ':' || b.line AS at_b
    FROM v_lock_pair a
    JOIN v_lock_pair b
      ON b.first_lock = a.second_lock AND b.second_lock = a.first_lock
     AND b.symbol_id <> a.symbol_id
    JOIN symbols sa ON sa.id=a.symbol_id
    JOIN symbols sb ON sb.id=b.symbol_id
    JOIN files fa ON fa.id=a.file_id
    JOIN files fb ON fb.id=b.file_id
    LEFT JOIN modules m ON m.id=sa.module_id
    WHERE a.first_lock < a.second_lock
      AND fa.is_test=0 AND fb.is_test=0 AND COALESCE(m.name,'') LIKE :mod
    ORDER BY max_fan_in DESC LIMIT :lim"""),
(
    "lock-held-across-io",
    "A monitor held while doing IO, sleeping or allocating",
    "ANSWERS where a critical section's duration is somebody else's latency.\n"
    "     This is what a profiler shows as time parked in lock with no clue\n"
    "     why, and it is the difference between a lock that scales and one\n"
    "     that serialises the whole service.\n"
    "ACT copy what you need out of the guarded state, release, then do the IO.\n"
    "     holds_call with a high callee count is the same problem one frame\n"
    "     removed -- you do not know what that callee does.\n"
    "MISLEADS for an explicit lock() the guarded region is the following try\n"
    "     block when there is one and the enclosing block otherwise, which\n"
    "     OVER-estimates: statements after the unlock can be counted in. For\n"
    "     synchronized the region is exact. Check the `kind` column before\n"
    "     acting on a row.",
    """SELECT s.name, s.owner_type AS owner, l.lock_name, l.kind,
        l.holds_io AS io_, l.holds_sleep AS sleeps,
        l.holds_alloc AS allocs, l.holds_call AS calls_out,
        l.region_sloc AS region, l.in_loop AS in_loop,
        s.n_wait_calls AS waits, s.fan_in,
        (l.holds_io*8 + l.holds_sleep*10 + l.holds_call
         + l.holds_alloc) * (1 + l.in_loop*3) AS hold_cost,
        f.path || ':' || l.line AS at
    FROM lock_ops l
    JOIN symbols s ON s.id=l.symbol_id
    JOIN files f ON f.id=l.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE l.op='acquire'
      AND (l.holds_io=1 OR l.holds_sleep=1 OR l.holds_alloc>2)
      AND f.is_test=0 AND COALESCE(m.name,'') LIKE :mod
    ORDER BY hold_cost DESC, s.fan_in DESC LIMIT :lim"""),
(
    "vt-pinning-frontier",
    "Virtual-thread roots reaching JNI or FFM -- NOT synchronized",
    "ANSWERS what still pins a carrier thread after JEP 491. In JDK 24 the\n"
    "     `synchronized` and Object.wait pinning was REMOVED, along with\n"
    "     -Djdk.tracePinnedThreads. A synchronized block inside a virtual\n"
    "     thread is a NON-FINDING and this query deliberately does not report\n"
    "     one. What is left is JNI, native methods and FFM downcalls.\n"
    "ACT a pinned carrier blocks every other virtual thread scheduled on it.\n"
    "     Move the native call behind a bounded platform-thread executor, or\n"
    "     accept it and size the carrier pool for it.\n"
    "MISLEADS depth is capped at 4 hops over resolved edges. Check\n"
    "     meta.java_release first: below 21 there are no virtual threads and\n"
    "     every row here is inapplicable; below 24 synchronized pins too and\n"
    "     this query is then INCOMPLETE rather than wrong.",
    """WITH RECURSIVE down(root, sym, depth) AS (
        SELECT id, id, 0 FROM symbols WHERE is_virtual_thread_root=1
        UNION
        SELECT d.root, e.callee_id, d.depth+1 FROM down d
        JOIN edges e ON e.caller_id=d.sym
        WHERE d.depth < 4 AND e.is_self=0)    -- depth bound: 4 hops
    SELECT r.name AS vt_root, r.owner_type AS root_owner,
        s.name AS pins_in, s.owner_type AS owner,
        MIN(d.depth) AS hops,
        s.n_jni AS jni_ops, s.n_native_calls AS native_,
        s.n_ffm_downcall AS ffm_downcall, s.n_ffm_arena AS ffm_arena,
        s.n_unsafe_calls AS unsafe_,
        s.n_synchronized_blocks AS synchronized_not_a_finding,
        f.path || ':' || s.line_start AS at
    FROM down d
    JOIN symbols s ON s.id=d.sym
    JOIN symbols r ON r.id=d.root
    JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE (s.n_jni > 0 OR s.n_native_calls > 0 OR s.n_ffm_downcall > 0)
      AND f.is_test=0 AND COALESCE(m.name,'') LIKE :mod
    GROUP BY r.id, s.id
    ORDER BY hops ASC, s.n_ffm_downcall DESC, s.n_jni DESC LIMIT :lim"""),
(
    "per-element-cost",
    "String +, boxing, Pattern.compile and prepareStatement inside loops",
    "ANSWERS the work that multiplies by the trip count: a `+` on String in a\n"
    "     loop allocates a new StringBuilder every iteration, Integer.valueOf\n"
    "     outside the -128..127 cache allocates, Pattern.compile re-parses the\n"
    "     regex, and prepareStatement in a loop is SpotBugs\n"
    "     IIL_PREPARE_STATEMENT_IN_LOOP.\n"
    "ACT hoist the compile and the prepare out of the loop; one StringBuilder\n"
    "     for the whole loop; primitive collections or arrays instead of boxed\n"
    "     ones. Weighted by fan_in because a leaf that fifty callers reach pays\n"
    "     fifty times.\n"
    "MISLEADS none of this is confirmed without a profiler. javac already\n"
    "     rewrites simple concatenation to invokedynamic/StringConcatFactory,\n"
    "     which is fast; the loop-carried case it cannot fix. Trip count is\n"
    "     invisible here, and a loop bounded by 3 costs nothing.",
    """SELECT s.name, s.owner_type AS owner,
        s.concat_in_loop AS concat_loop, s.n_string_concat AS concats,
        s.n_boxing_in_loop AS boxing_loop, s.n_boxing_sites AS boxing,
        s.regex_in_loop AS regex_loop, s.n_regex_compile AS regex_compiles,
        s.query_in_loop AS query_loop, s.n_query_calls AS queries,
        s.alloc_in_loop AS alloc_loop, s.max_loop_depth AS depth,
        s.fan_in,
        (s.concat_in_loop*6 + s.n_boxing_in_loop*4 + s.regex_in_loop*10
         + s.query_in_loop*20 + s.alloc_in_loop*2)
        * (1 + s.max_loop_depth) * (1 + MIN(s.fan_in, 20)) AS element_cost,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.max_loop_depth > 0
      AND (s.concat_in_loop + s.n_boxing_in_loop + s.regex_in_loop
           + s.query_in_loop + s.alloc_in_loop) > 0
      AND f.is_test=0 AND f.is_generated=0 AND COALESCE(m.name,'') LIKE :mod
    ORDER BY element_cost DESC LIMIT :lim"""),
(
    "megamorphic-callsites",
    "Interfaces with 3+ implementations, invoked from inside a loop",
    "ANSWERS where the JIT cannot inline. One or two receiver types at a call\n"
    "     site stay monomorphic or bimorphic and inline; three or more go\n"
    "     megamorphic, and the call becomes a real vtable dispatch that also\n"
    "     blocks every optimisation downstream of it.\n"
    "ACT this is a candidate list for a benchmark, not a defect list. Where it\n"
    "     matters, split the loop by type, or make the hot path take the\n"
    "     concrete type. n_impls is also a design signal: 1 means the\n"
    "     interface is an abstraction over nothing.\n"
    "MISLEADS implementation counting is structural and by simple name, so an\n"
    "     implementor in a dependency, or generated by a mock framework, is\n"
    "     invisible -- the true count is a floor. And a call site is only\n"
    "     megamorphic if the receivers actually VARY at run time; three\n"
    "     implementations of which one is ever loaded stays monomorphic.",
    """WITH hot AS (
        SELECT s.id, s.name, s.owner_type, s.max_loop_depth, s.call_in_loop,
               s.n_lambdas, s.n_streams, s.fan_in, s.file_id, s.line_start
        FROM symbols s
        JOIN files f ON f.id = s.file_id
        LEFT JOIN modules m ON m.id = s.module_id
        WHERE s.max_loop_depth > 0 AND s.call_in_loop > 0
          AND f.is_test = 0 AND COALESCE(m.name,'') LIKE :mod
    ),
    hp AS (
        SELECT p.symbol_id AS sid, p.pos AS pos, p.name AS pname, p.type AS ptype,
               CASE WHEN instr(p.type,'<') > 0
                    THEN substr(p.type, 1, instr(p.type,'<') - 1)
                    ELSE p.type END AS base,
               CASE WHEN substr(p.type,-1) = '>' THEN
                    substr(substr(p.type,1,length(p.type)-1),
                           length(rtrim(substr(p.type,1,length(p.type)-1),
                           'abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_$.')) + 1)
               END AS inner_,
               CASE WHEN substr(p.type,-1) = '>' THEN
                    substr(rtrim(substr(p.type,1,length(p.type)-1),
                           'abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_$.'), -1)
               END AS sep
        FROM params p
        WHERE p.symbol_id IN (SELECT id FROM hot)
    ),
    mt AS (
        SELECT i.id AS iid, hp.sid, hp.pos, hp.pname, hp.ptype
        FROM hp JOIN symbols i ON i.name = hp.base
        WHERE i.kind IN ('interface','class') AND i.n_impl_targets >= 3
        UNION
        SELECT i.id, hp.sid, hp.pos, hp.pname, hp.ptype
        FROM hp JOIN symbols i ON i.name = hp.inner_
        WHERE hp.sep = '<'
          AND i.kind IN ('interface','class') AND i.n_impl_targets >= 3
    )
    SELECT i.name AS iface, i.n_impl_targets AS n_impls, i.kind AS iface_kind,
           s.name AS called_from, s.owner_type AS owner,
           mt.pname AS param, mt.ptype AS param_type,
           s.max_loop_depth AS depth, s.call_in_loop AS calls_in_loop,
           s.n_lambdas AS lambdas, s.n_streams AS streams, s.fan_in,
           f.path || ':' || s.line_start AS at
    FROM mt
    JOIN symbols i ON i.id = mt.iid
    JOIN hot s ON s.id = mt.sid
    JOIN files f ON f.id = s.file_id
    ORDER BY i.n_impl_targets DESC, s.max_loop_depth DESC, s.fan_in DESC
    LIMIT :lim"""),
(
    "threadlocal-leak-on-pooled",
    "ThreadLocal set with no remove, reachable from a POOLED executor",
    "ANSWERS the classic container leak: a ThreadLocal set on a pooled worker\n"
    "     outlives the request, pins whatever it references, and in a web\n"
    "     container pins the whole webapp classloader across a redeploy.\n"
    "ACT set in a try, remove in the finally. Every time, not just on the\n"
    "     happy path.\n"
    "MISLEADS a virtual thread is DELIBERATELY excluded from the roots here: it\n"
    "     dies with its task, so a ThreadLocal it set cannot leak, and\n"
    "     including it would fill this list with non-findings. That is why\n"
    "     is_pooled_executor_root is a separate column from is_executor_root.\n"
    "     A ThreadLocal whose value is immutable and small leaks memory you\n"
    "     will never measure.",
    """WITH RECURSIVE down(sym, depth) AS (
        SELECT id, 0 FROM symbols WHERE is_pooled_executor_root=1
        UNION
        SELECT e.callee_id, d.depth+1 FROM down d
        JOIN edges e ON e.caller_id=d.sym
        WHERE d.depth < 5 AND e.is_self=0),   -- depth bound: 5 hops
    best AS (SELECT sym, MIN(depth) AS depth FROM down GROUP BY sym)
    SELECT s.name, s.owner_type AS owner, b.depth AS hops_from_pool,
        s.n_threadlocal_ops AS tl_ops,
        s.n_threadlocal_remove AS tl_removes,
        s.n_try AS trys, s.n_finally AS finallys,
        (SELECT COUNT(*) FROM fields fd
         JOIN symbols ty ON ty.id=fd.symbol_id
         WHERE ty.name=s.owner_type AND fd.type LIKE '%ThreadLocal%')
            AS tl_fields,
        s.fan_in, f.path || ':' || s.line_start AS at
    FROM best b JOIN symbols s ON s.id=b.sym
    JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_threadlocal_ops > 0 AND s.n_threadlocal_remove = 0
      AND f.is_test=0 AND COALESCE(m.name,'') LIKE :mod
    ORDER BY b.depth ASC, s.n_threadlocal_ops DESC LIMIT :lim"""),
(
    "shared-mutable-statics",
    "Non-final static state in modules that start threads",
    "ANSWERS what a race detector would find if the right two threads ever ran\n"
    "     together. SpotBugs MS_SHOULD_BE_FINAL raised to the module: a\n"
    "     mutable static plus a thread in the same module is unsynchronised\n"
    "     shared state waiting for load.\n"
    "ACT make it final, or move it behind a holder with a lock, or make it an\n"
    "     Atomic. A static that is only written in a static initialiser and\n"
    "     read afterwards is already safe -- the JVM guarantees that.\n"
    "MISLEADS this counts declarations and thread-starting code in the same\n"
    "     module, not actual concurrent access, so a static written once at\n"
    "     class-init time is a false positive. volatile_fields is the\n"
    "     counter-evidence that somebody thought about it.",
    """
WITH statics AS (
        SELECT ty.module_id AS mid,
               COUNT(DISTINCT fd.symbol_id || ':' || fd.ordinal) AS mutable_statics,
               GROUP_CONCAT(DISTINCT SUBSTR(fd.name,1,20)) AS names
        FROM fields fd
        JOIN symbols ty ON ty.id = fd.symbol_id
        JOIN files f ON f.id = ty.file_id
        WHERE fd.is_static=1 AND fd.is_const=0 AND f.is_test=0
        GROUP BY ty.module_id
    ),
    agg AS (
        SELECT module_id AS mid,
               SUM(is_executor_root) AS thread_starters,
               SUM(is_pooled_executor_root) AS pooled_starters,
               SUM(is_virtual_thread_root) AS virtual_starters,
               SUM(n_synchronized_blocks + n_lock_acquire) AS lock_ops,
               SUM(n_atomic_ops) AS atomics,
               SUM(n_volatile_access) AS volatile_reads,
               SUM(n_static_writes) AS static_writes
        FROM symbols
        GROUP BY module_id
    )
    SELECT m.name AS module_,
           st.mutable_statics,
           ag.thread_starters, ag.pooled_starters, ag.virtual_starters,
           ag.lock_ops, ag.atomics, ag.volatile_reads, ag.static_writes,
           st.names
    FROM statics st
    JOIN agg ag ON ag.mid = st.mid
    JOIN modules m ON m.id = st.mid
    WHERE m.name LIKE :mod
      AND ag.thread_starters > 0 AND ag.atomics = 0
    ORDER BY st.mutable_statics DESC, ag.thread_starters DESC LIMIT :lim"""),
(
    "exception-contract-drift",
    "throws Exception, a swallowed catch, and a null return",
    "ANSWERS where the type system stopped carrying information. `throws\n"
    "     Exception` tells a caller nothing, an empty catch discards the only\n"
    "     evidence of what went wrong, and returning null after both means the\n"
    "     failure arrives as an NPE three frames away with no stack trace\n"
    "     pointing anywhere near the cause.\n"
    "ACT declare the exceptions you actually throw; if you catch, either\n"
    "     handle it, wrap it with the cause, or rethrow. Return Optional or\n"
    "     throw instead of returning null. Ranked by fan_in: the same sin in a\n"
    "     leaf that forty callers reach is forty times the confusion.\n"
    "MISLEADS a genuinely optional lookup returning null is idiomatic in older\n"
    "     Java and appears here. An empty catch with a comment explaining why\n"
    "     is fine and this cannot read the comment. Test scaffolding often\n"
    "     swallows deliberately, which is why test files are excluded.",
    """SELECT s.name, s.owner_type AS owner,
        (SELECT COUNT(*) FROM exceptions x
         WHERE x.symbol_id=s.id AND x.kind='throws' AND x.is_broad=1)
            AS broad_throws,
        s.n_throws_declared AS throws_declared,
        s.n_catch AS catches, s.n_catch_broad AS broad_catches,
        s.n_catch_empty AS empty_catches,
        s.n_catch_rethrow AS rethrows,
        s.n_null_returns AS null_returns, s.n_optional_ops AS optional_ops,
        s.n_throw_sites AS throws_,
        s.fan_in,
        (s.n_catch_empty*10 + s.n_catch_broad*4 + s.n_null_returns*3)
            * (1 + MIN(s.fan_in,20)) AS drift,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE (s.n_catch_empty > 0 OR s.n_catch_broad > 0)
      AND (s.n_null_returns > 0 OR s.n_catch_empty > 0)
      AND f.is_test=0 AND f.is_generated=0 AND COALESCE(m.name,'') LIKE :mod
    ORDER BY drift DESC LIMIT :lim"""),
(
    "n-plus-one",
    "A DAO or query method whose CALLER puts it in a loop",
    "ANSWERS the N+1 no per-file linter can see, because the query lives in\n"
    "     one method and the loop that drives it lives in another. One page of\n"
    "     results turns into one round trip per row.\n"
    "ACT batch-fetch, add a join fetch, or move the iteration into the query.\n"
    "     A JPA findById inside a loop over entities is the canonical form.\n"
    "MISLEADS a loop with a small constant bound is not an N+1 and trip count\n"
    "     is invisible here. A caller that loops over a two-element array and\n"
    "     queries once per element is fine. Confirm against the query log\n"
    "     before rewriting anything.",
    """SELECT cal.name AS caller, cal.owner_type AS caller_owner,
        cal.max_loop_depth AS loop_depth,
        cle.name AS query_fn, cle.owner_type AS query_owner,
        cle.n_sql AS sql_ops, cle.n_query_calls AS query_calls,
        cle.query_in_loop AS own_loop, e.n_calls AS edges_,
        cal.fan_in AS caller_fan_in, cal.is_handler AS handler,
        cle.fan_in AS query_fan_in,
        f.path || ':' || cal.line_start AS at
    FROM edges e
    JOIN symbols cal ON cal.id=e.caller_id
    JOIN symbols cle ON cle.id=e.callee_id
    JOIN files f ON f.id=cal.file_id
    LEFT JOIN modules m ON m.id=cal.module_id
    WHERE (cle.n_sql > 0 OR cle.n_query_calls > 0)
      AND cal.max_loop_depth > 0 AND cal.call_in_loop > 0
      AND f.is_test=0 AND COALESCE(m.name,'') LIKE :mod
    ORDER BY cal.max_loop_depth DESC, cle.n_query_calls DESC,
        cal.fan_in DESC LIMIT :lim"""),
(
    "false-sharing-and-escape",
    "Contended counters on one cache line, and allocations that escape",
    "ANSWERS two things the JIT cannot fix for you. False sharing: several\n"
    "     mutable fields of one object written by different threads land on\n"
    "     one 64-byte line, and every write invalidates the other core's copy.\n"
    "     Escape: an object stored into a field or returned cannot be scalar-\n"
    "     replaced, so it is a real heap allocation however short its life.\n"
    "ACT for false sharing, @jdk.internal.vm.annotation.Contended (with\n"
    "     -XX:-RestrictContended) or manual padding, or move the counters into\n"
    "     per-thread accumulators and merge -- LongAdder already does this. For\n"
    "     escapes, keep the object local, or reuse a buffer.\n"
    "MISLEADS this is a candidate list for a benchmark and nothing more. False\n"
    "     sharing only costs anything under real cross-core contention, and\n"
    "     escape analysis is a run-time decision that -XX:+PrintEscapeAnalysis\n"
    "     will answer and this cannot. Field ORDER in memory is chosen by the\n"
    "     JVM, not by declaration order, so 'same cache line' is a guess.",
    """
WITH fld AS (
        SELECT symbol_id AS tid,
               COUNT(DISTINCT ordinal) AS mutable_fields,
               SUM(CASE WHEN type IN ('int','long','boolean','short','byte',
                                      'char','float','double')
                        THEN 1 ELSE 0 END) AS primitive_fields
        FROM fields
        WHERE is_const=0 AND is_static=0
        GROUP BY symbol_id
    ),
    mth AS (
        SELECT parent_id AS tid,
               SUM(n_atomic_ops) AS atomic_ops,
               SUM(n_volatile_access) AS volatile_access,
               SUM(n_lock_acquire) AS lock_acquires,
               SUM(n_escaping_allocs) AS escaping_allocs,
               SUM(alloc_in_loop) AS alloc_loop,
               MAX(fan_in) AS hottest_method
        FROM symbols
        WHERE parent_id IS NOT NULL
        GROUP BY parent_id
    )
    SELECT ty.name AS type_, ty.kind,
           fld.mutable_fields,
           fld.primitive_fields,
           (SELECT COUNT(*) FROM attributes a
            WHERE a.symbol_id=ty.id AND a.name='Contended') AS has_contended,
           COALESCE(mth.atomic_ops,0) AS atomic_ops,
           COALESCE(mth.volatile_access,0) AS volatile_access,
           COALESCE(mth.lock_acquires,0) AS lock_acquires,
           COALESCE(mth.escaping_allocs,0) AS escaping_allocs,
           COALESCE(mth.alloc_loop,0) AS alloc_loop,
           COALESCE(mth.hottest_method,0) AS hottest_method,
           f.path || ':' || ty.line_start AS at
    FROM symbols ty
    JOIN fld ON fld.tid = ty.id
    LEFT JOIN mth ON mth.tid = ty.id
    JOIN files f ON f.id = ty.file_id
    LEFT JOIN modules m ON m.id = ty.module_id
    WHERE f.is_test=0 AND COALESCE(m.name,'') LIKE :mod
      AND fld.mutable_fields >= 2
      AND (SELECT COUNT(*) FROM attributes a
           WHERE a.symbol_id=ty.id AND a.name='Contended') = 0
      AND (COALESCE(mth.atomic_ops,0) > 0 OR COALESCE(mth.volatile_access,0) > 0
           OR COALESCE(mth.lock_acquires,0) > 0
           OR COALESCE(mth.escaping_allocs,0) > 0)
    ORDER BY (COALESCE(mth.atomic_ops,0)*3 + COALESCE(mth.volatile_access,0)*2
              + COALESCE(mth.escaping_allocs,0) + COALESCE(mth.alloc_loop,0)) DESC,
             COALESCE(mth.hottest_method,0) DESC LIMIT :lim"""),
(
    "parse-coverage",
    "What this run could not read, and why",
    "ANSWERS whether the numbers above cover the code you think they cover.\n"
    "ACT a file with parsed=0 contributed nothing at all. A file with errors\n"
    "     contributed the symbols around the damage.\n"
    "MISLEADS an error count here is NOT evidence that the code is broken.\n"
    "     tree-sitter-java 0.23.5 predates Java 25 module import declarations\n"
    "     (JEP 511), so every `import module java.base;` parses as an ERROR and\n"
    "     adds exactly one to n_parse_errors through no fault of the source.\n"
    "     The module_imports column counts those, recovered by a text scan; a\n"
    "     row where errors equals module_imports is a clean file. See\n"
    "     meta.grammar_note. Genuine failures are the rows where errors\n"
    "     exceeds module_imports, or parsed=0.",
    """SELECT f.path, f.lines, f.n_parse_errors AS errors,
        f.n_missing_nodes AS missing,
        (SELECT COUNT(*) FROM jpms_directives j
         WHERE j.file_id=f.id AND j.kind='import-module') AS module_imports,
        f.n_parse_errors -
        (SELECT COUNT(*) FROM jpms_directives j
         WHERE j.file_id=f.id AND j.kind='import-module') AS unexplained,
        f.parsed, f.is_generated AS generated, f.is_test AS test_,
        f.n_symbols AS symbols_
    FROM files f
    LEFT JOIN modules m ON m.id=f.module_id
    WHERE (f.n_parse_errors > 0 OR f.parsed = 0)
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY unexplained DESC, f.lines DESC LIMIT :lim"""),
(
    "boxing-in-hot-loop",
    "Integer/Long boxing inside a loop, on methods the tree actually calls",
    "ANSWERS where autoboxing turns an arithmetic loop into an allocation\n"
    "     loop. Every `Integer` in a `long` accumulation is a heap object and\n"
    "     a cache miss; the JIT elides some of it and cannot elide the rest.\n"
    "ACT use the primitive-specialised types -- IntStream over\n"
    "     Stream<Integer>, long over Long, entrySet() iteration over get()\n"
    "     per key. Fix the loop with the highest fan_in first.\n"
    "MISLEADS boxing sites are counted lexically, so a boxed value that never\n"
    "     escapes and is scalar-replaced by C2 counts here and costs nothing\n"
    "     at run time. This is a shortlist to profile, not a verdict.",
    """SELECT s.name, s.owner_type AS owner, s.n_boxing_in_loop AS boxed_in_loop,
        s.n_boxing_sites AS boxed_total, s.max_loop_depth AS depth,
        s.n_alloc_sites AS allocs, s.fan_in, s.n_streams AS streams,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_boxing_in_loop > 0 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.n_boxing_in_loop * (1 + s.fan_in) DESC,
        s.max_loop_depth DESC LIMIT :lim"""),
(
    "regex-and-format-per-call",
    "Pattern.compile and date formatting rebuilt per call instead of once",
    "ANSWERS which methods rebuild an expensive immutable object every time\n"
    "     they run. Pattern.compile parses the regex; SimpleDateFormat\n"
    "     allocates a calendar and a symbol table. Both belong in a field.\n"
    "ACT hoist the Pattern to a static final constant. For dates use\n"
    "     DateTimeFormatter, which IS immutable and thread-safe --\n"
    "     SimpleDateFormat is neither, so a static one is a data race rather\n"
    "     than an optimisation.\n"
    "MISLEADS a compile inside a method that runs once at startup is\n"
    "     harmless, and this cannot tell startup from steady state. fan_in is\n"
    "     the proxy: rank by it rather than by the raw count.",
    """SELECT s.name, s.owner_type AS owner, s.n_regex_compile AS regex_compiles,
        s.n_datefmt_ops AS datefmt_ops, s.fan_in, s.max_loop_depth AS depth,
        s.call_in_loop AS calls_in_loop, s.is_static AS static_,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE (s.n_regex_compile > 0 OR s.n_datefmt_ops > 0)
      AND s.fan_in > 0 AND f.is_test=0 AND COALESCE(m.name,'') LIKE :mod
    ORDER BY (s.n_regex_compile + s.n_datefmt_ops) * (1 + s.fan_in) DESC
    LIMIT :lim"""),
(
    "raw-types-and-unchecked",
    "Generics defeated: raw types, unchecked casts and wildcard soup",
    "ANSWERS where the compiler stopped being able to help. A raw List or an\n"
    "     unchecked cast moves a ClassCastException from compile time to\n"
    "     whichever unlucky request hits it first.\n"
    "ACT parameterise the type. If the cast is genuinely unavoidable at a\n"
    "     serialization or reflection boundary, isolate it in one method with\n"
    "     a SuppressWarnings and a comment, rather than scattering the risk.\n"
    "MISLEADS raw types in code that predates generics and is never touched\n"
    "     are not urgent. Rank by fan_in, and read `suppressed` as evidence\n"
    "     the team already made this decision deliberately.",
    """SELECT s.name, s.owner_type AS owner, s.n_raw_types AS raw_types,
        s.n_unchecked_casts AS unchecked, s.n_wildcard_types AS wildcards,
        s.n_instanceof AS instanceofs, s.n_suppressions AS suppressed,
        s.fan_in, f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE (s.n_raw_types > 0 OR s.n_unchecked_casts > 0) AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY (s.n_raw_types*2 + s.n_unchecked_casts*3) * (1 + s.fan_in) DESC
    LIMIT :lim"""),
(
    "setaccessible-and-finalizers",
    "setAccessible, Unsafe and finalizers: the parts of Java that are leaving",
    "ANSWERS what already warns, or will break, on a modern JDK.\n"
    "     setAccessible against JDK internals fails under strong\n"
    "     encapsulation; sun.misc.Unsafe memory access is deprecated for\n"
    "     removal; finalizers were deprecated in 9 and disabled by default\n"
    "     in 18.\n"
    "ACT replace finalizers with Cleaner, or better with AutoCloseable and\n"
    "     try-with-resources. Replace Unsafe with VarHandle and the FFM API.\n"
    "MISLEADS this cannot tell WHOSE class is being opened. A framework\n"
    "     calling setAccessible on your own entities is normal; the same call\n"
    "     against java.lang is a time bomb. Read the target before acting.",
    """SELECT s.name, s.owner_type AS owner, s.n_setaccessible AS setaccessible,
        s.n_unsafe_calls AS unsafe_calls, s.n_finalizers AS finalizers,
        s.n_native_calls AS native_calls, s.n_ffm_downcall AS ffm_downcalls,
        s.fan_in, f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE (s.n_setaccessible > 0 OR s.n_unsafe_calls > 0
           OR s.n_finalizers > 0) AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.n_finalizers DESC, s.n_unsafe_calls DESC,
        s.n_setaccessible DESC LIMIT :lim"""),
(
    "parallel-stream-hazard",
    "parallelStream() in a body that also blocks, locks or writes shared state",
    "ANSWERS which parallel streams are actively harmful. They run on the\n"
    "     common ForkJoinPool, which the whole JVM shares: one blocking task\n"
    "     in there starves every other parallel stream in the process.\n"
    "ACT if the body does IO, use a dedicated executor -- or virtual threads,\n"
    "     which exist for exactly this. If it takes a lock, the parallelism\n"
    "     is probably fictional. If it mutates shared state, it is a race.\n"
    "MISLEADS a parallel stream over a large in-memory collection doing pure\n"
    "     CPU work is exactly right, and will appear here if it happens to\n"
    "     sit near a lock. Check what the LAMBDA does, not the method.\n"
    "     fan_out rather than fan_in: a parallelStream is usually reached\n"
    "     through a framework or a lambda, so the enclosing method often\n"
    "     has no in-tree caller at all.",
    """SELECT s.name, s.owner_type AS owner, s.n_parallel_streams AS parallel_,
        s.n_streams AS streams, s.n_lock_acquire AS locks,
        s.n_synchronized_blocks AS synced, s.n_io AS io_ops,
        s.n_static_writes AS static_writes, s.fan_out,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_parallel_streams > 0 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY (s.n_io + s.n_lock_acquire + s.n_synchronized_blocks
              + s.n_static_writes) DESC, s.n_parallel_streams DESC LIMIT :lim"""),
]

JavaAnalyzer.QUERIES = JavaAnalyzer.QUERIES + [
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
]

ANALYZER = JavaAnalyzer()


if __name__ == "__main__":
    try:
        sys.exit(main(ANALYZER))
    except KeyboardInterrupt:
        print("\ninterrupted", file=sys.stderr)
        sys.exit(130)
