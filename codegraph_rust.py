#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Piyush Katariya
#
# @author Piyush Katariya
"""codegraph_rust.py -- parse a Rust tree into a graph and query it.

Targets Rust 1.97, edition 2024. Parses with tree-sitter-rust.

rustc and clippy already own the single-function verdict, and 847 clippy lints
is more per-function opinion than anyone needs. What neither can see is shape:
which `unsafe` block is reachable from a `pub` function three frames up, which
`MutexGuard` is still alive at an `.await` two calls down, which `Box<dyn Trait>`
pays a virtual call for a trait that has exactly one implementor.

Three Rust facts this bakes in, read from Cargo.toml rather than assumed:

* Edition 2024 makes `let`-chains legal (`if let Some(x) = o && x > 1`), so the
  grammar parses them and `gen` is a reserved keyword. On edition 2021 the same
  source is a parse error, and `files.n_parse_errors` will say so rather than
  the file going quietly thin.
* `unsafe extern "C"` is the required spelling in 2024. A bare `extern "C" {}`
  block in a 2024 crate is a hard error upstream, which is why the extern
  surface is counted from `foreign_mod_item` nodes and not from a regex.
* `[features]` in Cargo.toml is the only enumeration of what `#[cfg(feature)]`
  can legally name. A cfg naming a feature the manifest does not declare is
  code that nothing in this workspace can compile.

The two blind spots, stated once so no query has to keep apologising:

* Trait-object dispatch. `Box<dyn Renderer>` calling `.render()` has no
  syntactic target. It lands in `unresolved_calls`, and Q1 measures exactly how
  much of everything below is guesswork because of it.
* Macros. `ast_struct! { ... }` in syn defines the types syn is famous for, and
  a syntactic parser sees a `macro_invocation` and a `token_tree`. Locally
  defined `macro_rules!` ARE symbols here and calls to them ARE edges, but what
  they expand to is invisible. The `macros` table is the honest measure of how
  much of a crate is generated this way.

Usage:
  python3 codegraph_rust.py /path/to/crate --report
  python3 codegraph_rust.py /path/to/crate --list
  python3 codegraph_rust.py --deps"""
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
    #: (value, line) -- G07 credential-shaped string literals
    secrets: list[tuple[str, int]] = dc_field(default_factory=list)

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
        self.emit_secrets(stats, sid, rec, bufs)
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
        self.emit_secrets(stats, sid, rec, bufs)
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

    def emit_secrets(self, stats: BodyStats, sid: int, rec: FileRec,
                     bufs: Buffers) -> None:
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
# lang_rust.py
# codegraph_rust.py -- parse a Rust tree into a graph and query it.
#
# Targets Rust 1.97, edition 2024. Parses with tree-sitter-rust.
#
# rustc and clippy already own the single-function verdict, and 847 clippy lints
# is more per-function opinion than anyone needs. What neither can see is shape:
# which `unsafe` block is reachable from a `pub` function three frames up, which
# `MutexGuard` is still alive at an `.await` two calls down, which `Box<dyn Trait>`
# pays a virtual call for a trait that has exactly one implementor.
#
# Three Rust facts this bakes in, read from Cargo.toml rather than assumed:
#
# * Edition 2024 makes `let`-chains legal (`if let Some(x) = o && x > 1`), so the
#   grammar parses them and `gen` is a reserved keyword. On edition 2021 the same
#   source is a parse error, and `files.n_parse_errors` will say so rather than
#   the file going quietly thin.
# * `unsafe extern "C"` is the required spelling in 2024. A bare `extern "C" {}`
#   block in a 2024 crate is a hard error upstream, which is why the extern
#   surface is counted from `foreign_mod_item` nodes and not from a regex.
# * `[features]` in Cargo.toml is the only enumeration of what `#[cfg(feature)]`
#   can legally name. A cfg naming a feature the manifest does not declare is
#   code that nothing in this workspace can compile.
#
# The two blind spots, stated once so no query has to keep apologising:
#
# * Trait-object dispatch. `Box<dyn Renderer>` calling `.render()` has no
#   syntactic target. It lands in `unresolved_calls`, and Q1 measures exactly how
#   much of everything below is guesswork because of it.
# * Macros. `ast_struct! { ... }` in syn defines the types syn is famous for, and
#   a syntactic parser sees a `macro_invocation` and a `token_tree`. Locally
#   defined `macro_rules!` ARE symbols here and calls to them ARE edges, but what
#   they expand to is invisible. The `macros` table is the honest measure of how
#   much of a crate is generated this way.
#
# Usage:
#   python3 codegraph_rust.py /path/to/crate --report
#   python3 codegraph_rust.py /path/to/crate --list
#   python3 codegraph_rust.py --deps
# ==========================================================================

DEPS = DepSet(lang="rust", deps=[
    TREE_SITTER,
    grammar("Rust", "tree_sitter_rust", "tree-sitter-rust>=0.24",
            "0.24.2 (ABI 15)"),
])

HAZARD_CATEGORIES = (
    "unsafe", "panic", "alloc", "clone", "lock", "atomic", "async", "io",
    "ffi", "mem", "exec", "control",
)

HAZARD_CALLS: dict[str, str] = {
    # panic -- clippy::unwrap_used, expect_used, panic, unreachable, todo.
    # borrow/borrow_mut are RefCell's runtime borrow check: a panic that only
    # fires under the interleaving nobody tested.
    "unwrap": "panic", "expect": "panic", "unwrap_err": "panic",
    "expect_err": "panic", "unwrap_unchecked": "panic",
    "unwrap_or_default": "panic", "panic!": "panic", "unreachable!": "panic",
    "todo!": "panic", "unimplemented!": "panic", "assert!": "panic",
    "assert_eq!": "panic", "assert_ne!": "panic", "debug_assert!": "panic",
    "borrow": "panic", "borrow_mut": "panic", "abort": "panic",
    # clone -- clippy::redundant_clone, clone_on_copy, implicit_clone.
    # Cheap individually, and the whole reason a hot loop allocates.
    "clone": "clone", "cloned": "clone", "to_owned": "clone",
    "to_vec": "clone", "to_string": "clone", "into_owned": "clone",
    "clone_from": "clone", "deep_clone": "clone",
    # alloc -- clippy::vec_init_then_push, or_fun_call, format_in_format_args
    "Vec::new": "alloc", "Vec::with_capacity": "alloc", "vec!": "alloc",
    "String::new": "alloc", "String::with_capacity": "alloc",
    "Box::new": "alloc", "Rc::new": "alloc", "Arc::new": "alloc",
    "collect": "alloc", "format!": "alloc", "extend": "alloc",
    "reserve": "alloc", "leak": "alloc", "into_boxed_slice": "alloc",
    "with_capacity": "alloc", "to_vec_in": "alloc",
    # lock -- clippy::await_holding_lock, mut_mutex_lock, rc_buffer
    "lock": "lock", "try_lock": "lock", "read": "lock", "write": "lock",
    "RefCell::new": "lock", "Mutex::new": "lock", "RwLock::new": "lock",
    "Condvar::wait": "lock", "wait_timeout": "lock", "write_owned": "lock",
    "read_owned": "lock", "lock_owned": "lock",
    # atomic -- there is no lint for a wrong Ordering, only review
    "load": "atomic", "store": "atomic", "compare_exchange": "atomic",
    "compare_exchange_weak": "atomic", "fetch_add": "atomic",
    "fetch_sub": "atomic", "fetch_update": "atomic", "fetch_or": "atomic",
    "swap": "atomic", "fence": "atomic", "compiler_fence": "atomic",
    # async -- clippy::async_yields_async, unused_async
    "spawn": "async", "spawn_blocking": "async", "spawn_local": "async",
    "block_on": "async", "join!": "async", "try_join!": "async",
    "select!": "async", "Box::pin": "async", "send": "async", "recv": "async",
    "try_send": "async", "try_recv": "async", "blocking_send": "async",
    "blocking_recv": "async", "join_all": "async", "timeout": "async",
    # io -- the BLOCKING set. Every one of these parks an executor thread if it
    # runs inside an async fn, which is clippy's blocking_op_in_async in spirit
    # and the single most common tokio production incident.
    "File::open": "io", "File::create": "io", "fs::read": "io",
    "fs::read_to_string": "io", "fs::write": "io", "fs::remove_file": "io",
    "fs::create_dir_all": "io", "fs::metadata": "io", "read_to_string": "io",
    "read_to_end": "io", "write_all": "io", "flush": "io",
    "thread::sleep": "io", "TcpStream::connect": "io", "TcpListener::bind": "io",
    "println!": "io", "eprintln!": "io", "print!": "io", "eprint!": "io",
    "stdin": "io", "read_line": "io", "BufReader::new": "io",
    # ffi -- clippy::not_unsafe_ptr_arg_deref, from_raw is the free() half of a
    # pair whose malloc() half is usually in another function
    "from_raw": "ffi", "into_raw": "ffi", "CStr::from_ptr": "ffi",
    "CString::from_raw": "ffi", "CString::into_raw": "ffi",
    "from_raw_parts": "ffi", "from_raw_parts_mut": "ffi",
    "NonNull::new_unchecked": "ffi", "as_ptr": "ffi", "as_mut_ptr": "ffi",
    "from_raw_fd": "ffi", "into_raw_fd": "ffi",
    # mem -- clippy::transmute_*, uninit_assumed_init, mem_forget
    "transmute": "mem", "transmute_copy": "mem", "mem::forget": "mem",
    "MaybeUninit::uninit": "mem", "assume_init": "mem", "ptr::read": "mem",
    "ptr::write": "mem", "copy_nonoverlapping": "mem", "set_len": "mem",
    "get_unchecked": "mem", "get_unchecked_mut": "mem",
    "Pin::new_unchecked": "mem", "Box::leak": "mem", "zeroed": "mem",
    "ptr::null_mut": "mem", "offset": "mem", "add": "mem",
    # exec
    "Command::new": "exec", "process::exit": "exec", "exit": "exec",
    "Command::spawn": "exec", "status": "exec", "output": "exec",
    # control -- catch_unwind is the only place a panic stops being fatal, and
    # `?` is the only non-obvious early return in the language
    "catch_unwind": "control", "resume_unwind": "control",
    "set_hook": "control", "take_hook": "control",
}

BLOCKING_IO = frozenset("""
File::open File::create fs::read fs::read_to_string fs::write fs::remove_file
fs::create_dir_all fs::metadata fs::read_dir read_to_string read_to_end
write_all thread::sleep TcpStream::connect TcpListener::bind read_line
recv_timeout join wait lock_blocking blocking_send blocking_recv
""".split())

ITER_ADAPTERS = frozenset("""
map filter filter_map flat_map flatten fold try_fold scan zip chain take skip
take_while skip_while step_by enumerate rev peekable inspect cloned copied
collect partition unzip windows chunks chunks_exact for_each any all find
find_map position count sum product min_by max_by min_by_key max_by_key
sort_by sort_by_key dedup retain
""".split())

STD_ROOTS = frozenset("""
std core alloc proc_macro test
""".split())

STD_MACROS = frozenset("""
println eprintln print eprint format write writeln panic unreachable todo
unimplemented assert assert_eq assert_ne debug_assert debug_assert_eq
debug_assert_ne vec matches dbg include include_str include_bytes concat
stringify line file column module_path cfg env option_env compile_error
thread_local try_join join select tokio_test
""".split())

PRELUDE = frozenset("""
Some None Ok Err Box Vec String Option Result Rc Arc RefCell Cell Mutex RwLock
HashMap HashSet BTreeMap BTreeSet VecDeque Cow Default Clone Copy Drop From
Into TryFrom TryInto Iterator IntoIterator Send Sync Sized Fn FnMut FnOnce
drop print len is_empty iter into_iter next self Self true false
""".split())

SHARED_MUT_RE = re.compile(r'\b(?:Arc|Mutex|RwLock)\s*<\s*(?:Mutex|RwLock)\s*<')

RC_CELL_RE = re.compile(r'\bRc\s*<\s*(?:RefCell|Cell)\s*<')

WEAK_RE = re.compile(r'\bWeak\s*<')

GUARD_RE = re.compile(
    r'\.\s*(lock|try_lock|read|write|borrow|borrow_mut|lock_owned|'
    r'read_owned|write_owned)\s*\(')

SAFETY_RE = re.compile(r'^\s*(?:/{2,}!?|/\*+|\*)\s*#*\s*SAFETY\b[:\-\s]',
                       re.I | re.M)

ORDERING_RE = re.compile(r'\bOrdering::(Relaxed|Acquire|Release|AcqRel|SeqCst)\b')

CFG_FEATURE_RE = re.compile(r'feature\s*=\s*"([^"]+)"')

TEST_ATTR_RE = re.compile(r'^(?:test|bench|.*::test|rstest|proptest|'
                          r'tokio::test|async_std::test|quickcheck)$')

ARITH_OPS = frozenset(("+", "-", "*", "/", "%", "<<", ">>"))

CMP_OPS = frozenset(("==", "!=", "<", ">", "<=", ">="))

BIT_OPS = frozenset(("&", "|", "^"))

LOGIC_OPS = frozenset(("&&", "||"))

CHECKED_PREFIXES = ("checked_", "wrapping_", "saturating_", "overflowing_",
                    "unchecked_")

#: G07: a string literal that names a credential (mirrors the other packs).
SECRET_RE = re.compile(
    r'(api[_-]?key|apikey|secret|password|passwd|pwd|token|bearer|'
    r'access[_-]?key|private[_-]?key|client[_-]?secret|'
    r'auth[_-]?token|jwt|credential|smtp[_-]?pass|db[_-]?pass|'
    r'sk_live|rk_live|pk_live|ghp_|xoxb-|AKIA)', re.I)
SECRET_MIN_LEN = 12

#: G19: deserialization entry points across serde_json/bincode/ron/toml.
DESER_BASES = frozenset(("from_str", "from_slice", "from_reader", "from_bytes"))

#: G29: the zip crate's entry points.
ZIP_PREFIXES = ("ZipArchive::", "zip::")

class RustAnalyzer(TreeSitterAnalyzer):
    LANG = "rust"
    TARGET = "Rust 1.97 (edition 2024)"
    EXTS = (".rs",)
    SKIP_DIRS = {"target", "tests/fixtures"}
    DEPS = DEPS
    HAZARD_CATEGORIES = HAZARD_CATEGORIES
    MANIFESTS = ("Cargo.toml", "Cargo.lock", "rust-toolchain.toml")

    GRAMMAR_MODULE = "tree_sitter_rust"
    GRAMMAR_PIP = "tree-sitter-rust>=0.24"

    FUNC_KINDS = {
        "function_item": "function",
        # A trait's `fn f(&self);` and an `extern "C" { fn c(); }` declaration.
        # Both are real API surface with no body, so they are symbols with
        # is_abstract=1 rather than holes in the graph.
        "function_signature_item": "function",
        "closure_expression": "closure",
    }
    TYPE_KINDS = {
        "struct_item": "struct",
        "enum_item": "enum",
        "union_item": "union",
        "trait_item": "trait",
        "impl_item": "impl",
        "type_item": "type",
        "mod_item": "module",
        "const_item": "const",
        "static_item": "static",
        # macro_rules! is a definition like any other, and in a macro-heavy
        # crate it is where the code actually lives.
        "macro_definition": "macro",
    }
    #: `impl` has no name field; its identity is the type it is for. Taking
    #: field `type` (and stripping generics in node_name) makes `impl Foo<T>`
    #: register as `Foo`, which is what a `self.method()` call has to match.
    NAME_FIELD = {"impl_item": "type", "closure_expression": ""}
    IDENT_NODES = ("identifier", "type_identifier", "field_identifier")

    BODY_FIELD = "body"
    PARAMS_FIELD = "parameters"
    RETURN_FIELD = "return_type"
    ELSE_FIELD = "alternative"
    IF_NODES = ("if_expression",)

    LOOP_NODES = ("for_expression", "while_expression", "loop_expression")
    BRANCH_NODES = ("if_expression",)
    #: `block` is deliberately absent. Every `if` owns a `block`, so counting
    #: both doubles every nesting number and a flat guard-clause function ends
    #: up ranked beside a genuinely pyramidal one. Match arms are excluded for
    #: the same reason: a 40-arm dispatch is wide, not deep.
    NEST_NODES = ("if_expression", "for_expression", "while_expression",
                  "loop_expression", "match_expression", "closure_expression",
                  "unsafe_block", "async_block")
    #: macro_invocation is a call in every sense that matters: `vec![]`
    #: allocates, `panic!()` diverges, and a local `macro_rules!` target is a
    #: resolvable edge. on_call reads the right field for each node type.
    CALL_NODES = ("call_expression", "macro_invocation")
    CALL_FUNC_FIELD = "function"
    COMMENT_NODES = ("line_comment", "block_comment")
    STRING_NODES = ("string_literal", "raw_string_literal", "char_literal")
    NUMBER_NODES = ("integer_literal", "float_literal")
    OPERATOR_NODES = ("binary_expression", "unary_expression",
                      "assignment_expression", "compound_assignment_expr",
                      "index_expression", "field_expression",
                      "reference_expression", "type_cast_expression",
                      "range_expression", "try_expression")

    COUNTERS = {
        "return_expression": "n_returns",
        "match_expression": "n_switch",
        "match_arm": "n_match_arms",
        "closure_expression": "n_lambda",
        "await_expression": "n_await",
        "try_expression": "n_question_mark",
        "unsafe_block": "n_unsafe_blocks",
        "index_expression": "n_index_expr",
        "field_expression": "n_member_access",
        "type_cast_expression": "n_as_casts",
        "macro_invocation": "n_macro_invocations",
        "let_declaration": "n_locals",
        "assignment_expression": "n_assign",
        "compound_assignment_expr": "n_compound_assign",
        "generic_function": "n_turbofish",
        "pointer_type": "n_raw_ptr",
        "dynamic_type": "n_box_dyn",
        "abstract_type": "n_impl_trait",
        "lifetime": "n_lifetimes",
        "async_block": "n_async_blocks",
        "try_block": "n_try",
        "let_chain": "n_let_chains",
    }
    #: A clone inside a loop is the allocation the profiler blames on malloc.
    #: `needle in name` matches method chains, so `to_owned` catches
    #: `x.as_str().to_owned()`.
    LOOP_CALL_COUNTERS = {
        "clone": "n_clone_in_loop",
        "to_owned": "n_clone_in_loop",
        "to_vec": "n_clone_in_loop",
        "to_string": "n_clone_in_loop",
        "collect": "alloc_in_loop",
        "format!": "alloc_in_loop",
        "vec!": "alloc_in_loop",
        "push": "alloc_in_loop",
        "insert": "alloc_in_loop",
        "lock": "lock_in_loop",
        "borrow_mut": "lock_in_loop",
        "Regex::new": "regex_in_loop",
        "query": "query_in_loop",
        "execute": "query_in_loop",
    }

    EXTRA_SYMBOL_COLS = (
        #: `let ... else { }` (stable 1.65). A diverging early return that
        #: is neither a `match` nor an `if`, so nothing counted it -- modern
        #: Rust read as less branchy than it is. rust-analyzer has 1,023.
        ("n_let_else", "INT NOT NULL DEFAULT 0"),
        # -- unsafe surface (clippy::undocumented_unsafe_blocks, multiple_unsafe_ops_per_block)
        ("n_unsafe_blocks", "INT NOT NULL DEFAULT 0"),
        ("n_unsafe_ops", "INT NOT NULL DEFAULT 0"),
        ("n_safety_comments", "INT NOT NULL DEFAULT 0"),
        ("is_unsafe_fn", "INT NOT NULL DEFAULT 0"),
        # -- panic surface (clippy::unwrap_used, indexing_slicing, arithmetic_side_effects)
        ("n_unwrap", "INT NOT NULL DEFAULT 0"),
        ("n_expect", "INT NOT NULL DEFAULT 0"),
        ("n_panic_macro", "INT NOT NULL DEFAULT 0"),
        ("n_index_expr", "INT NOT NULL DEFAULT 0"),
        ("n_slice_range", "INT NOT NULL DEFAULT 0"),
        ("n_question_mark", "INT NOT NULL DEFAULT 0"),
        ("n_borrow_calls", "INT NOT NULL DEFAULT 0"),
        # -- allocation churn (clippy::redundant_clone, or_fun_call)
        ("n_clone", "INT NOT NULL DEFAULT 0"),
        ("n_clone_in_loop", "INT NOT NULL DEFAULT 0"),
        ("n_to_owned", "INT NOT NULL DEFAULT 0"),
        ("n_collect", "INT NOT NULL DEFAULT 0"),
        ("n_format_macro", "INT NOT NULL DEFAULT 0"),
        #: SQL keywords inside a string literal (on_string); the count was
        #: collected but never declared, so it silently never reached the graph.
        ("n_sql_literal", "INT NOT NULL DEFAULT 0"),
        # -- OWASP P2 pack: sinks for the input-surface family ---------------
        ("n_deserialize", "INT NOT NULL DEFAULT 0"),         # G19 from_str etc
        ("n_zip_read", "INT NOT NULL DEFAULT 0"),            # G29 zip crate
        ("n_with_capacity", "INT NOT NULL DEFAULT 0"),
        ("n_iter_adapters", "INT NOT NULL DEFAULT 0"),
        # -- async (clippy::await_holding_lock, await_holding_refcell_ref)
        ("n_await", "INT NOT NULL DEFAULT 0"),
        ("n_async_blocks", "INT NOT NULL DEFAULT 0"),
        ("n_lock_acquire", "INT NOT NULL DEFAULT 0"),
        ("n_lock_across_await", "INT NOT NULL DEFAULT 0"),
        ("n_blocking_io", "INT NOT NULL DEFAULT 0"),
        ("n_blocking_in_async", "INT NOT NULL DEFAULT 0"),
        ("n_spawn", "INT NOT NULL DEFAULT 0"),
        ("n_spawn_blocking", "INT NOT NULL DEFAULT 0"),
        ("n_channel_ops", "INT NOT NULL DEFAULT 0"),
        ("is_async_fn", "INT NOT NULL DEFAULT 0"),
        # -- shared mutability and atomics
        ("n_atomic_ops", "INT NOT NULL DEFAULT 0"),
        ("n_relaxed_ordering", "INT NOT NULL DEFAULT 0"),
        ("n_seqcst_ordering", "INT NOT NULL DEFAULT 0"),
        ("n_arc_mutex", "INT NOT NULL DEFAULT 0"),
        ("n_rc_refcell", "INT NOT NULL DEFAULT 0"),
        ("n_weak_refs", "INT NOT NULL DEFAULT 0"),
        # -- dispatch and generics (the devirtualisation and mono questions)
        ("n_box_dyn", "INT NOT NULL DEFAULT 0"),
        ("n_dyn_params", "INT NOT NULL DEFAULT 0"),
        ("n_impl_trait", "INT NOT NULL DEFAULT 0"),
        ("n_trait_bounds", "INT NOT NULL DEFAULT 0"),
        ("n_where_predicates", "INT NOT NULL DEFAULT 0"),
        ("n_lifetimes", "INT NOT NULL DEFAULT 0"),
        ("n_hrtb", "INT NOT NULL DEFAULT 0"),
        ("n_turbofish", "INT NOT NULL DEFAULT 0"),
        ("n_mono_instantiations", "INT NOT NULL DEFAULT 0"),
        # -- FFI and raw memory
        ("n_raw_ptr", "INT NOT NULL DEFAULT 0"),
        ("n_transmute", "INT NOT NULL DEFAULT 0"),
        ("n_extern_calls", "INT NOT NULL DEFAULT 0"),
        ("n_from_raw", "INT NOT NULL DEFAULT 0"),
        ("n_into_raw", "INT NOT NULL DEFAULT 0"),
        ("n_static_mut", "INT NOT NULL DEFAULT 0"),
        ("is_extern_fn", "INT NOT NULL DEFAULT 0"),
        # -- attributes (suppression is evidence, not noise)
        ("n_derives", "INT NOT NULL DEFAULT 0"),
        ("n_macro_invocations", "INT NOT NULL DEFAULT 0"),
        ("n_allow_attrs", "INT NOT NULL DEFAULT 0"),
        ("n_expect_attrs", "INT NOT NULL DEFAULT 0"),
        ("n_inline_attrs", "INT NOT NULL DEFAULT 0"),
        ("n_cfg_blocks", "INT NOT NULL DEFAULT 0"),
        ("n_cfg_features", "INT NOT NULL DEFAULT 0"),
        # -- arithmetic and control
        ("n_as_casts", "INT NOT NULL DEFAULT 0"),
        ("n_checked_arith", "INT NOT NULL DEFAULT 0"),
        ("n_arith_unchecked", "INT NOT NULL DEFAULT 0"),
        ("n_match_arms", "INT NOT NULL DEFAULT 0"),
        ("n_let_chains", "INT NOT NULL DEFAULT 0"),
        ("is_const_fn", "INT NOT NULL DEFAULT 0"),
        ("n_lock_in_loop", "INT NOT NULL DEFAULT 0"),
    ("n_to_owned_in_loop", "INT NOT NULL DEFAULT 0"),
    ("n_safe_fallback", "INT NOT NULL DEFAULT 0"),
    ("n_error_swallow", "INT NOT NULL DEFAULT 0"),
    ("n_iter_in_loop", "INT NOT NULL DEFAULT 0"),
    ("n_push_in_loop", "INT NOT NULL DEFAULT 0"),
    ("n_io_in_loop", "INT NOT NULL DEFAULT 0"),
    ("n_block_on", "INT NOT NULL DEFAULT 0"),
    ("n_thread_sleep", "INT NOT NULL DEFAULT 0"),
    ("n_len_in_loop", "INT NOT NULL DEFAULT 0"),
    ("n_borrow_mut", "INT NOT NULL DEFAULT 0"),
    ("n_unwrap_err", "INT NOT NULL DEFAULT 0"),
    ("n_unchecked_call", "INT NOT NULL DEFAULT 0"),
    ("n_elif", "INT NOT NULL DEFAULT 0"),
        ("n_external_calls", "INT NOT NULL DEFAULT 0"),
        # -- where this symbol lives, for the queries that need the receiver
        ("impl_type", "TEXT NOT NULL DEFAULT ''"),
        ("is_trait_method", "INT NOT NULL DEFAULT 0"),
    )

    SCHEMA_EXT = r"""
CREATE TABLE traits(
    symbol_id INT NOT NULL PRIMARY KEY REFERENCES symbols(id),
    file_id INT NOT NULL REFERENCES files(id),
    name TEXT NOT NULL,
    n_required INT NOT NULL DEFAULT 0,   -- fn with no body: an implementor must supply it
    n_provided INT NOT NULL DEFAULT 0,   -- fn with a default body
    n_assoc_types INT NOT NULL DEFAULT 0,
    n_assoc_consts INT NOT NULL DEFAULT 0,
    n_supertraits INT NOT NULL DEFAULT 0,
    is_unsafe INT NOT NULL DEFAULT 0,
    is_public INT NOT NULL DEFAULT 0,
    is_generic INT NOT NULL DEFAULT 0,
    has_assoc_type INT NOT NULL DEFAULT 0,   -- an assoc type makes it non-object-safe
    methods TEXT NOT NULL DEFAULT ''
) WITHOUT ROWID, STRICT;

CREATE TABLE impls(
    id INTEGER PRIMARY KEY,
    symbol_id INT NOT NULL REFERENCES symbols(id),
    file_id INT NOT NULL REFERENCES files(id),
    type_name TEXT NOT NULL DEFAULT '',
    trait_name TEXT NOT NULL DEFAULT '',   -- '' means an inherent impl
    is_unsafe INT NOT NULL DEFAULT 0,      -- `unsafe impl Send for X` -- a promise, unchecked
    is_negative INT NOT NULL DEFAULT 0,    -- `impl !Send for X`
    is_generic INT NOT NULL DEFAULT 0,     -- a blanket impl fans out at mono time
    n_methods INT NOT NULL DEFAULT 0,
    n_unsafe_methods INT NOT NULL DEFAULT 0,
    line INT NOT NULL DEFAULT 0
) STRICT;

CREATE TABLE unsafe_blocks(
    id INTEGER PRIMARY KEY,
    symbol_id INT NOT NULL REFERENCES symbols(id),
    file_id INT NOT NULL REFERENCES files(id),
    line INT NOT NULL,
    sloc INT NOT NULL DEFAULT 0,
    n_ops INT NOT NULL DEFAULT 0,          -- unsafe operations inside one block
    n_deref INT NOT NULL DEFAULT 0,
    n_raw_calls INT NOT NULL DEFAULT 0,
    n_transmute INT NOT NULL DEFAULT 0,
    n_from_raw INT NOT NULL DEFAULT 0,
    has_safety_comment INT NOT NULL DEFAULT 0,
    in_unsafe_fn INT NOT NULL DEFAULT 0,
    in_loop INT NOT NULL DEFAULT 0
) STRICT;

CREATE TABLE derives(
    id INTEGER PRIMARY KEY,
    symbol_id INT REFERENCES symbols(id),
    file_id INT NOT NULL REFERENCES files(id),
    name TEXT NOT NULL,
    is_std INT NOT NULL DEFAULT 0,         -- built-in derive vs a proc macro
    line INT NOT NULL DEFAULT 0
) STRICT;

CREATE TABLE lifetimes(
    id INTEGER PRIMARY KEY,
    symbol_id INT NOT NULL REFERENCES symbols(id),
    file_id INT NOT NULL REFERENCES files(id),
    name TEXT NOT NULL,
    kind TEXT NOT NULL DEFAULT 'param',    -- param | bound | use
    is_static INT NOT NULL DEFAULT 0,
    line INT NOT NULL DEFAULT 0
) STRICT;

CREATE TABLE generic_bounds(
    id INTEGER PRIMARY KEY,
    symbol_id INT NOT NULL REFERENCES symbols(id),
    param TEXT NOT NULL,
    bound TEXT NOT NULL,
    in_where INT NOT NULL DEFAULT 0,
    is_hrtb INT NOT NULL DEFAULT 0,
    line INT NOT NULL DEFAULT 0
) STRICT;

CREATE TABLE macros(
    id INTEGER PRIMARY KEY,
    symbol_id INT REFERENCES symbols(id),
    file_id INT NOT NULL REFERENCES files(id),
    name TEXT NOT NULL,
    kind TEXT NOT NULL DEFAULT 'invocation',  -- definition | invocation | attribute
    n_rules INT NOT NULL DEFAULT 0,
    body_bytes INT NOT NULL DEFAULT 0,      -- how much source the expander hides
    defines_items INT NOT NULL DEFAULT 0,   -- token tree contains fn/struct/impl
    line INT NOT NULL DEFAULT 0
) STRICT;

CREATE TABLE secret_candidates(
    id INTEGER PRIMARY KEY,
    symbol_id INT REFERENCES symbols(id),
    file_id INT NOT NULL REFERENCES files(id),
    value TEXT NOT NULL,
    line INT NOT NULL
) STRICT;

CREATE TABLE cfg_blocks(
    id INTEGER PRIMARY KEY,
    file_id INT NOT NULL REFERENCES files(id),
    symbol_id INT REFERENCES symbols(id),
    expr TEXT NOT NULL,
    feature TEXT NOT NULL DEFAULT '',
    is_test INT NOT NULL DEFAULT 0,
    is_attr_only INT NOT NULL DEFAULT 0,    -- cfg_attr rather than cfg
    line INT NOT NULL DEFAULT 0
) STRICT;

 CREATE TABLE async_points(
     id INTEGER PRIMARY KEY,
     symbol_id INT NOT NULL REFERENCES symbols(id),
     file_id INT NOT NULL REFERENCES files(id),
     line INT NOT NULL,
     in_loop INT NOT NULL DEFAULT 0,
     loop_depth INT NOT NULL DEFAULT 0,
     n_guards_live INT NOT NULL DEFAULT 0,   -- lock guards still in scope here
     guards TEXT NOT NULL DEFAULT '',
     guard_dropped INT NOT NULL DEFAULT 0,   -- an explicit drop() before the await
     expr TEXT NOT NULL DEFAULT '',
     has_refcell_guard INT NOT NULL DEFAULT 0  -- guard value text names RefCell
 ) STRICT;

 -- Dependencies declared in Cargo.toml, for manifest-vs-usage: a declared
 -- crate with no use/import in the tree is dead weight or a dev-only dep.
 CREATE TABLE deps(
     id INTEGER PRIMARY KEY,
     name TEXT NOT NULL,
     version TEXT NOT NULL DEFAULT '',
     is_dev INT NOT NULL DEFAULT 0
 ) STRICT;

CREATE TABLE crate_features(
    id INTEGER PRIMARY KEY,
    name TEXT NOT NULL,
    enables TEXT NOT NULL DEFAULT '',
    is_default INT NOT NULL DEFAULT 0
) STRICT;
"""

    INDEX_EXT = r"""
CREATE INDEX idx_impl_sym ON impls(symbol_id);
CREATE INDEX idx_impl_trait ON impls(trait_name, type_name);
CREATE INDEX idx_impl_type ON impls(type_name);
CREATE INDEX idx_impl_unsafe ON impls(type_name) WHERE is_unsafe=1;
CREATE INDEX idx_trait_pub ON traits(is_public, n_required);
CREATE INDEX idx_unsafe_sym ON unsafe_blocks(symbol_id, line);
CREATE INDEX idx_unsafe_undoc ON unsafe_blocks(n_ops DESC, symbol_id)
    WHERE has_safety_comment=0;
CREATE INDEX idx_derive_name ON derives(name, symbol_id);
CREATE INDEX idx_gb_sym ON generic_bounds(symbol_id);
CREATE INDEX idx_gb_bound ON generic_bounds(bound);
CREATE INDEX idx_macro_name ON macros(name, kind);
CREATE INDEX idx_macro_def ON macros(name) WHERE kind='definition';
CREATE INDEX idx_cfg_feature ON cfg_blocks(feature) WHERE feature<>'';
CREATE INDEX idx_cfg_file ON cfg_blocks(file_id, line);
CREATE INDEX idx_secret_sym ON secret_candidates(symbol_id);
CREATE INDEX idx_async_sym ON async_points(symbol_id, line);
CREATE INDEX idx_async_guard ON async_points(symbol_id)
    WHERE n_guards_live>0;
CREATE INDEX idx_lifetime_sym ON lifetimes(symbol_id, name);
CREATE INDEX idx_fn_unsafe ON symbols(n_unsafe_blocks DESC, name)
    WHERE n_unsafe_blocks>0;
CREATE INDEX idx_fn_panicky ON symbols(n_unwrap DESC, name) WHERE n_unwrap>0;
CREATE INDEX idx_fn_asyncfn ON symbols(name, file_id) WHERE is_async_fn=1;
CREATE INDEX idx_fn_generic ON symbols(n_generic_params DESC, name)
    WHERE n_generic_params>0;
"""

    VIEW_EXT = r"""
CREATE VIEW v_unsafe AS
SELECT u.id, s.name AS in_fn, s.qual_name, s.impl_type, f.path, u.line,
    u.n_ops, u.n_deref, u.n_raw_calls, u.n_transmute, u.n_from_raw,
    u.has_safety_comment, u.in_unsafe_fn, u.in_loop,
    s.is_public, s.fan_in, f.is_test AS in_test_file,
    f.path || ':' || u.line AS at
FROM unsafe_blocks u
JOIN symbols s ON s.id=u.symbol_id
JOIN files f ON f.id=u.file_id;

CREATE VIEW v_impl AS
SELECT i.id, i.type_name, i.trait_name, i.is_unsafe, i.is_negative,
    i.is_generic, i.n_methods, f.path, i.line,
    (SELECT COUNT(*) FROM impls i2 WHERE i2.trait_name=i.trait_name
     AND i.trait_name<>'') AS impls_of_trait,
    f.path || ':' || i.line AS at
FROM impls i JOIN files f ON f.id=i.file_id;

CREATE VIEW v_await AS
SELECT a.id, s.name AS in_fn, s.is_async_fn, f.path, a.line, a.in_loop,
    a.loop_depth, a.n_guards_live, a.guards, a.guard_dropped, a.expr,
    s.fan_in, f.path || ':' || a.line AS at
FROM async_points a
JOIN symbols s ON s.id=a.symbol_id
JOIN files f ON f.id=a.file_id;
"""

    MATERIALIZE_EXT = r"""
UPDATE symbols AS s SET n_unique_calls = x.c FROM
    (SELECT caller_id AS id, COUNT(*) AS c FROM edges GROUP BY caller_id) AS x
    WHERE x.id = s.id;

-- A `match` with k arms is k-1 extra decision points. Counting arms in
-- BRANCH_NODES instead would have charged cognitive complexity per arm, which
-- ranks a flat 40-arm dispatch above a triple-nested loop. It is not.
UPDATE symbols SET n_cases = n_match_arms;
UPDATE symbols SET cyclomatic = cyclomatic + n_match_arms - n_switch
    WHERE n_match_arms > 0;

-- Overflow checks that the author DID write are subtracted from the raw
-- arithmetic count, so the column names what is genuinely unguarded.
UPDATE symbols SET n_arith_unchecked = MAX(0, n_arith - n_checked_arith);

-- Blocking IO is only an incident inside an async fn; elsewhere it is just IO.
UPDATE symbols SET n_blocking_in_async = n_blocking_io WHERE is_async_fn = 1;

UPDATE symbols AS s SET n_lock_across_await = x.c FROM
    (SELECT symbol_id AS id, COUNT(*) AS c FROM async_points
     WHERE n_guards_live > 0 AND guard_dropped = 0 GROUP BY symbol_id) AS x
    WHERE x.id = s.id;

UPDATE symbols AS s SET n_unsafe_ops = x.n FROM
    (SELECT symbol_id AS id, SUM(n_ops) AS n FROM unsafe_blocks
     GROUP BY symbol_id) AS x WHERE x.id = s.id;

UPDATE symbols AS s SET n_safety_comments = x.n FROM
    (SELECT symbol_id AS id, SUM(has_safety_comment) AS n FROM unsafe_blocks
     GROUP BY symbol_id) AS x WHERE x.id = s.id;

UPDATE symbols AS s SET n_derives = x.n FROM
    (SELECT symbol_id AS id, COUNT(*) AS n FROM derives
     WHERE symbol_id IS NOT NULL GROUP BY symbol_id) AS x WHERE x.id = s.id;

-- A call whose target is declared inside `unsafe extern "C" { }`. Only the
-- resolved edges can say this, so it cannot be counted while parsing.
UPDATE symbols AS s SET n_extern_calls = x.n FROM
    (SELECT e.caller_id AS id, COUNT(*) AS n FROM edges e
     JOIN symbols tgt ON tgt.id=e.callee_id
     WHERE tgt.is_extern_fn=1 GROUP BY e.caller_id) AS x WHERE x.id = s.id;

-- Monomorphisation count is a PROXY: distinct modules that call this generic
-- function. rustc instantiates per distinct type-argument tuple, which a
-- syntactic parser cannot enumerate, so this is a floor and never the number.
UPDATE symbols AS s SET n_mono_instantiations = x.c FROM
    (SELECT e.callee_id AS id, COUNT(DISTINCT c.module_id) AS c
     FROM edges e JOIN symbols c ON c.id=e.caller_id
     GROUP BY e.callee_id) AS x
    WHERE x.id = s.id AND s.n_generic_params > 0;
"""

    RISK_SQL = (
        "cyclomatic*2 + cognitive + max_nesting*4"
        " + n_unsafe*10 + n_unsafe_ops*6 + n_mem*8 + n_ffi*8"
        " + (CASE WHEN n_unsafe_blocks>0 AND n_safety_comments=0"
        "         THEN n_unsafe_blocks*8 ELSE 0 END)"
        " + n_transmute*20 + n_exec*15"
        " + n_unwrap*3 + n_panic_macro*4 + n_index_expr*2"
        " + n_lock_across_await*25 + n_blocking_in_async*20"
        " + n_clone_in_loop*6 + alloc_in_loop*4 + lock_in_loop*8"
        " + n_static_mut*15 + n_relaxed_ordering*4"
        " + (CASE WHEN is_unsafe_fn=1 AND has_doc=0 THEN 12 ELSE 0 END)"
        " + (CASE WHEN is_recursive THEN 10 ELSE 0 END)"
        " + n_allow_attrs*2"
    )

    def __init__(self) -> None:
        super().__init__()
        self.edition = ""
        self.rust_version = ""
        self.crate_name = ""
        self.features: set[str] = set()
        #: symbol ids of `impl` and `trait` blocks, so a function inside one
        #: can be classified as a method without re-walking the tree.
        self._impl_like: set[int] = set()
        self._trait_ids: set[int] = set()

    # -- naming -----------------------------------------------------------
    def node_name(self, node: Any, rec: FileRec) -> str:
        """`impl Foo<T> for Bar` must register as `Bar`, not `Bar<T>`.

        Call resolution matches a method call against the enclosing type name.
        Leaving the generic arguments on would make `Widget<T, 4>` a different
        type from `Widget<u8, 4>` and split one type's methods across two
        buckets that nothing ever joins.
        """
        if node.type == "impl_item":
            t = node.child_by_field_name("type")
            if t is None:
                return ""
            return _base_type(text_of(t, rec.data))
        return super().node_name(node, rec)

    def visibility_of(self, node: Any, rec: FileRec) -> str:
        """Rust says this out loud, so there is nothing to infer."""
        for c in node.named_children:
            if c.type == "visibility_modifier":
                txt = text_of(c, rec.data).strip()
                if txt == "pub":
                    return "public"
                return txt          # pub(crate), pub(super), pub(in path)
        return "private"

    def docstring_lines(self, node: Any, rec: FileRec) -> int:
        """Doc comments sit ABOVE the attributes, not next to the item.

        `/// docs` then `#[inline]` then `pub fn` is the normal Rust order, and
        the base walks back only over comment siblings -- it stops at the first
        attribute and reports every documented function as undocumented. That
        would make `has_doc` a constant and quietly break the missing-docs
        half of the safety-doc query.
        """
        prev = node.prev_sibling
        while prev is not None and prev.type in ("attribute_item",):
            prev = prev.prev_sibling
        n = 0
        while prev is not None and prev.type in self.COMMENT_NODES:
            txt = text_of(prev, rec.data).lstrip()
            if txt.startswith(("///", "/**", "//!")):
                n += prev.end_point[0] - prev.start_point[0] + 1
            elif n == 0 and prev.end_point[0] + 1 >= node.start_point[0]:
                n += prev.end_point[0] - prev.start_point[0] + 1
            else:
                break
            prev = prev.prev_sibling
        return n

    # -- symbol kinds ------------------------------------------------------
    def emit_function(self, node: Any, rec: FileRec, db: sqlite3.Connection,
                      bufs: Buffers, scope: Scope, kind: str) -> int:
        """A `function_item` is a method when its grandparent is impl/trait.

        Rust spells free functions and methods with the same node, so the
        distinction has to come from position. Getting it wrong would make
        every `impl` block's contents look like top-level API.
        """
        if kind == "function":
            p = node.parent
            gp = p.parent if p is not None and p.type == "declaration_list" \
                else None
            if gp is not None and gp.type in ("impl_item", "trait_item"):
                kind = "method"
        return super().emit_function(node, rec, db, bufs, scope, kind)

    def emit_type(self, node: Any, rec: FileRec, db: sqlite3.Connection,
                  bufs: Buffers, scope: Scope, kind: str) -> int:
        sid = super().emit_type(node, rec, db, bufs, scope, kind)
        if kind in ("impl", "trait"):
            self._impl_like.add(sid)
            if kind == "trait":
                self._trait_ids.add(sid)
        return sid

    # -- per-symbol flags --------------------------------------------------
    def function_flags(self, node: Any, rec: FileRec,
                       scope: Scope) -> dict[str, Any]:
        """Everything readable from the SIGNATURE rather than the body.

        `measure()` walks the body only, so generics, bounds, lifetimes,
        `dyn` parameters and the `async`/`unsafe`/`const`/`extern` modifiers
        have to be counted here or they are counted nowhere.
        """
        src = rec.data
        name = self.node_name(node, rec)
        mods = ""
        for c in node.named_children:
            if c.type == "function_modifiers":
                mods = text_of(c, src)
                break
        params = node.child_by_field_name("parameters")
        ptxt = text_of(params, src) if params is not None else ""
        ret = node.child_by_field_name("return_type")
        rtxt = text_of(ret, src) if ret is not None else ""
        tp = node.child_by_field_name("type_parameters")
        where = None
        for c in node.named_children:
            if c.type == "where_clause":
                where = c
                break

        n_generic = 0
        n_bounds = 0
        n_life = 0
        n_hrtb = 0
        for sub in (tp, where):
            if sub is None:
                continue
            for n in walk(sub):
                if n.type in ("type_parameter", "const_parameter"):
                    n_generic += 1
                elif n.type == "trait_bounds":
                    n_bounds += 1
                elif n.type in ("lifetime", "lifetime_parameter"):
                    n_life += 1
                elif n.type in ("higher_ranked_trait_bound", "for_lifetimes"):
                    n_hrtb += 1
        n_where = sum(1 for n in walk(where) if n.type == "where_predicate") \
            if where is not None else 0

        sig_types = "%s %s" % (ptxt, rtxt)
        # A `dyn` in the RETURN type is the same virtual call as one in a
        # parameter, just paid by the caller instead.
        n_dyn = sum(1 for sub in (params, ret) if sub is not None
                    for n in walk(sub) if n.type == "dynamic_type")
        n_impl_trait = sum(
            1 for sub in (params, ret) if sub is not None
            for n in walk(sub) if n.type == "abstract_type")
        n_raw = sum(
            1 for sub in (params, ret) if sub is not None
            for n in walk(sub) if n.type == "pointer_type")
        n_life += sum(1 for sub in (params, ret) if sub is not None
                      for n in walk(sub) if n.type == "lifetime")

        # The enclosing impl/trait, so a method knows whose it is.
        impl_type = scope.type_name if scope.type_id in self._impl_like else ""
        is_trait_method = int(scope.type_id in self._trait_ids)
        if not is_trait_method and scope.type_id in self._impl_like:
            # A method in an `impl Trait for Type` block is dispatched through
            # the trait, so fan_in=0 does not mean nobody calls it.
            is_trait_method = int(_impl_has_trait(node))

        attrs = _attr_names(node, src)
        attr_text = " ".join(_attr_args(node, src))
        is_test = int(any(TEST_ATTR_RE.match(a) for a in attrs))
        vis = self.visibility_of(node, rec)
        # `extern "C" fn f()` puts the modifier on the function; a declaration
        # inside `unsafe extern "C" { ... }` puts it on the block, so the
        # function itself looks perfectly ordinary and would be missed.
        p = node.parent
        in_foreign = (p is not None and p.type == "declaration_list"
                      and p.parent is not None
                      and p.parent.type == "foreign_mod_item")

        return dict(
            is_public=int(vis == "public"),
            is_exported=int(vis == "public"),
            is_async=int("async" in mods),
            is_async_fn=int("async" in mods),
            is_unsafe_fn=int("unsafe" in mods),
            is_const_fn=int("const" in mods),
            is_extern_fn=int("extern" in mods or in_foreign),
            is_abstract=int(node.type == "function_signature_item"),
            is_test=is_test,
            is_deprecated=int(any(a == "deprecated" for a in attrs)),
            is_entrypoint=int(name == "main"),
            is_static=int(params is not None
                          and not any(c.type == "self_parameter"
                                      for c in params.named_children)),
            n_generic_params=n_generic,
            n_trait_bounds=n_bounds,
            n_where_predicates=n_where,
            n_lifetimes=n_life,
            n_hrtb=n_hrtb,
            n_dyn_params=n_dyn,
            n_impl_trait=n_impl_trait,
            n_raw_ptr=n_raw,
            n_arc_mutex=len(SHARED_MUT_RE.findall(sig_types)),
            n_rc_refcell=len(RC_CELL_RE.findall(sig_types)),
            n_weak_refs=len(WEAK_RE.findall(sig_types)),
            n_allow_attrs=sum(1 for a in attrs if a == "allow"),
            n_expect_attrs=sum(1 for a in attrs if a == "expect"),
            n_inline_attrs=sum(1 for a in attrs if a.startswith("inline")),
            n_cfg_blocks=sum(1 for a in attrs if a.startswith("cfg")),
            n_cfg_features=len(CFG_FEATURE_RE.findall(attr_text)),
            impl_type=impl_type[:120],
            is_trait_method=is_trait_method,
        )

    def type_flags(self, node: Any, rec: FileRec,
                   scope: Scope) -> dict[str, Any]:
        src = rec.data
        vis = self.visibility_of(node, rec)
        txt = text_of(node, src)
        head = txt.split("{", 1)[0]
        attrs = _attr_names(node, src)
        tp = node.child_by_field_name("type_parameters")
        n_generic = sum(1 for n in walk(tp)
                        if n.type in ("type_parameter", "const_parameter")) \
            if tp is not None else 0
        return dict(
            is_public=int(vis == "public"),
            is_exported=int(vis == "public"),
            is_unsafe_fn=int(_has_anon(node, "unsafe")),
            n_generic_params=n_generic,
            n_static_mut=int(node.type == "static_item"
                             and any(c.type == "mutable_specifier"
                                     for c in node.named_children)),
            n_arc_mutex=len(SHARED_MUT_RE.findall(txt)),
            n_rc_refcell=len(RC_CELL_RE.findall(txt)),
            n_weak_refs=len(WEAK_RE.findall(txt)),
            n_box_dyn=head.count("dyn "),
            n_allow_attrs=sum(1 for a in attrs if a == "allow"),
            n_expect_attrs=sum(1 for a in attrs if a == "expect"),
            n_cfg_blocks=sum(1 for a in attrs if a.startswith("cfg")),
            n_cfg_features=len(CFG_FEATURE_RE.findall(
                " ".join(_attr_args(node, src)))),
            is_test=int(node.type == "mod_item"
                        and any("cfg(test)" in a for a in
                                _attr_args(node, src))),
        )

    # -- the measuring pass ------------------------------------------------
    def on_call(self, node: Any, src: bytes, st: BodyStats,
                loop_depth: int, nest: int) -> None:
        """One handler for two node types: `f()` and `m!()`.

        A macro's callee lives in field `macro`, not `function`, and its name
        is recorded WITH the `!` so `panic!` and a method called `panic` stay
        distinguishable in the hazard table. `normalise_callee` strips it again
        before resolution, which is what lets a call to a local `macro_rules!`
        become a real edge.
        """
        st.bump("n_calls")
        if loop_depth:
            st.bump("call_in_loop")
        if node.type == "macro_invocation":
            m = node.child_by_field_name("macro")
            if m is None:
                st.bump("n_dynamic_calls")
                return
            name = text_of(m, src).strip() + "!"
            st.calls.append((name[:200], node.start_point[0] + 1, False,
                             bool(loop_depth)))
            if name == "format!":
                st.bump("n_format_macro")
            elif name in ("panic!", "unreachable!", "todo!",
                          "unimplemented!"):
                st.bump("n_panic_macro")
            if loop_depth:
                for needle, col in self.LOOP_CALL_COUNTERS.items():
                    if needle == name:
                        st.bump(col)
            return

        fn = node.child_by_field_name(self.CALL_FUNC_FIELD)
        if fn is None:
            st.bump("n_dynamic_calls")
            st.calls.append(("", node.start_point[0] + 1, True,
                             bool(loop_depth)))
            return
        name = text_of(fn, src).strip()
        # -- facts clippy checks, recorded not judged --------------------
        _b = name.rsplit("::", 1)[-1].rsplit(".", 1)[-1]
        if _b in ("lock", "read", "write") and loop_depth:
            st.bump("n_lock_in_loop")
        if _b in ("to_string", "to_owned", "to_vec") and loop_depth:
            st.bump("n_to_owned_in_loop")     # clippy::redundant_clone family
        if _b in ("unwrap_or_else", "unwrap_or_default", "ok_or_else"):
            st.bump("n_safe_fallback")        # the GOOD pattern, for contrast
        if _b in ("iter", "into_iter", "chars", "bytes") and loop_depth:
            st.bump("n_iter_in_loop")
        if _b in ("push", "insert", "extend") and loop_depth:
            st.bump("n_push_in_loop")         # clippy::needless_collect adjacent
        if _b in ("read_to_string", "read_to_end", "write_all") and loop_depth:
            st.bump("n_io_in_loop")
        if _b in ("block_on",):
            st.bump("n_block_on")             # blocking inside async
        if _b in ("sleep",) and "thread" in name:
            st.bump("n_thread_sleep")         # clippy async blocking
        if _b in ("len",) and loop_depth:
            st.bump("n_len_in_loop")
        if _b in ("get_mut", "borrow_mut"):
            st.bump("n_borrow_mut")           # RefCell runtime-panic surface
        if _b in ("expect_err", "unwrap_err"):
            st.bump("n_unwrap_err")
        if _b in ("from_utf8_unchecked", "get_unchecked", "get_unchecked_mut"):
            st.bump("n_unchecked_call")       # clippy::undocumented_unsafe_blocks
        # A turbofish call's `function` field is a `generic_function`; its own
        # `function` child is the real callee, so peel it or every generic call
        # records `foo::<u32>` and resolves to nothing.
        if fn.type == "generic_function":
            inner = fn.child_by_field_name("function")
            if inner is not None:
                name = text_of(inner, src).strip()
        dynamic = not name or (not name[0].isalpha() and name[0] != "_")
        st.calls.append((name[:200], node.start_point[0] + 1, dynamic,
                         bool(loop_depth)))
        if dynamic:
            st.bump("n_dynamic_calls")

        base = name.rsplit(".", 1)[-1].rsplit("::", 1)[-1]
        tail2 = "::".join(name.replace(".", "::").split("::")[-2:])
        if base in DESER_BASES:
            # G19: deserialization entry point (serde_json/bincode/ron/toml
            # all spell from_str/from_slice/from_reader); whether the input
            # is untrusted is the query's question, not this counter's.
            st.bump("n_deserialize")
        if name.startswith(ZIP_PREFIXES):
            # G29: the zip crate -- entry containment is a check, not a
            # name; this ranks where archives are opened.
            st.bump("n_zip_read")
        if base == "unwrap":
            st.bump("n_unwrap")
        elif base == "expect":
            st.bump("n_expect")
        elif base in ("clone", "cloned"):
            st.bump("n_clone")
        elif base in ("to_owned", "to_vec", "to_string"):
            st.bump("n_to_owned")
        elif base == "collect":
            st.bump("n_collect")
        elif base == "with_capacity":
            st.bump("n_with_capacity")
        elif base in ("borrow", "borrow_mut"):
            st.bump("n_borrow_calls")
            st.bump("n_lock_acquire")
        elif base in ("lock", "try_lock", "read", "write", "lock_owned"):
            st.bump("n_lock_acquire")
        elif base == "spawn":
            st.bump("n_spawn")
        elif base in ("spawn_blocking", "block_in_place"):
            st.bump("n_spawn_blocking")
        elif base in ("send", "recv", "try_send", "try_recv",
                      "blocking_send", "blocking_recv"):
            st.bump("n_channel_ops")
        elif base in ("load", "store", "fetch_add", "fetch_sub",
                      "fetch_update", "fetch_or", "compare_exchange",
                      "compare_exchange_weak", "fence"):
            st.bump("n_atomic_ops")
        elif base in ("transmute", "transmute_copy"):
            st.bump("n_transmute")
        elif base in ("from_raw", "from_raw_parts", "from_raw_parts_mut",
                      "from_raw_fd"):
            st.bump("n_from_raw")
        elif base in ("into_raw", "into_raw_fd"):
            st.bump("n_into_raw")
        if base.startswith(CHECKED_PREFIXES):
            st.bump("n_checked_arith")
        if base in ITER_ADAPTERS:
            st.bump("n_iter_adapters")
        if name in BLOCKING_IO or base in BLOCKING_IO or tail2 in BLOCKING_IO:
            st.bump("n_blocking_io")
            if loop_depth:
                st.bump("io_in_loop")
        if loop_depth:
            for needle, col in self.LOOP_CALL_COUNTERS.items():
                if needle == base or needle in name:
                    st.bump(col)

    def on_node(self, node: Any, src: bytes, st: BodyStats,
                loop_depth: int, nest: int) -> None:
        t = node.type
        if t == "let_declaration":
            # A let-else is a `let_declaration` carrying an `alternative`;
            # a plain `let` has no such field. The else arm must diverge,
            # so it is a real branch and counts like an `if`.
            if node.child_by_field_name("alternative") is not None:
                st.bump("n_let_else")
                st.cyclomatic += 1
                st.cognitive += max(1, nest)
            pat = node.child_by_field_name("pattern")
            val = node.child_by_field_name("value")
            if pat is not None and val is not None:
                ptxt = text_of(pat, src).strip()
                # error-swallowing-sites: `let _ = fallible()` -- the result
                # is dropped; clippy let_underscore_must_use territory.
                if ptxt == "_" and val.type in ("call_expression",
                                                "method_invocation",
                                                "await_expression"):
                    st.bump("n_error_swallow")
                # `.map_err(|_| ...)` ignores the error value entirely.
                if ptxt == "_" and "map_err" in text_of(val, src)[:200]:
                    st.bump("n_error_swallow")
        elif t == "binary_expression":
            op = node.child_by_field_name("operator")
            o = op.type if op is not None else ""
            if o in ARITH_OPS:
                st.bump("n_arith")
                if o in ("<<", ">>"):
                    st.bump("n_shift")
            elif o in CMP_OPS:
                st.bump("n_cmp")
            elif o in BIT_OPS:
                st.bump("n_bitop")
            elif o in LOGIC_OPS:
                st.bump("n_logical")
                st.cyclomatic += 1
        elif t == "compound_assignment_expr":
            op = node.child_by_field_name("operator")
            if op is not None and op.type[:-1] in ARITH_OPS:
                st.bump("n_arith")
        elif t == "unary_expression":
            # `*p` on a raw pointer is the deref that makes a block unsafe.
            if node.child_count and node.children[0].type == "*":
                st.bump("n_deref")
        elif t == "index_expression":
            # `v[i]` panics on out of range; `&v[a..b]` panics on a bad range.
            # Both are clippy::indexing_slicing, and both are invisible to a
            # reader scanning for `.unwrap()`.
            if any(c.type == "range_expression" for c in node.named_children):
                st.bump("n_slice_range")
        elif t == "scoped_identifier":
            m = ORDERING_RE.search(text_of(node, src))
            if m is not None:
                if m.group(1) == "Relaxed":
                    st.bump("n_relaxed_ordering")
                elif m.group(1) == "SeqCst":
                    st.bump("n_seqcst_ordering")
        elif t == "await_expression" and loop_depth:
            st.bump("await_in_loop")
        elif t == "generic_type":
            txt = text_of(node, src)[:200]
            if SHARED_MUT_RE.search(txt):
                st.bump("n_arc_mutex")
            if RC_CELL_RE.search(txt):
                st.bump("n_rc_refcell")
            if WEAK_RE.search(txt):
                st.bump("n_weak_refs")
        elif t == "let_declaration":
            if node.child_by_field_name("alternative") is not None:
                st.bump("n_early_returns")     # let ... else { return }
        elif t == "return_expression":
            st.bump("n_early_returns")
        elif t == "match_arm":
            # A `_ =>` arm is the catch-all; it is what makes a match total,
            # and its absence is what makes adding an enum variant a compile
            # error rather than a silent fallthrough.
            pat = node.child_by_field_name("pattern")
            if pat is not None and text_of(pat, src).strip() == "_":
                st.bump("n_catch_broad")

    def on_string(self, node: Any, text: str, src: bytes, st: BodyStats,
                  loop_depth: int) -> None:
        val = text.strip('"\'')
        if len(val) >= SECRET_MIN_LEN and " " not in val \
            and SECRET_RE.search(val):
            # G07: credential-shaped literal -- candidate, not verdict
            st.secrets.append((val[:200], node.start_point[0] + 1))
        if re.search(r'\b(SELECT\s|INSERT\s+INTO|UPDATE\s+\w|DELETE\s+FROM)\b',
                     text, re.I):
            st.bump("n_sql_literal")
            if loop_depth:
                st.bump("query_in_loop")

    # -- hazards and resolution -------------------------------------------
    def hazard_of(self, callee: str) -> Optional[tuple[str, str]]:
        cat = HAZARD_CALLS.get(callee)
        if cat is not None:
            return callee, cat
        # `a.b.lock().unwrap` -> try `unwrap`, then `lock().unwrap`.
        flat = callee.replace(".", "::")
        parts = flat.split("::")
        base = parts[-1]
        cat = HAZARD_CALLS.get(base)
        if cat is not None:
            return "*::" + base, cat
        if len(parts) >= 2:
            cat = HAZARD_CALLS.get("::".join(parts[-2:]))
            if cat is not None:
                return "::".join(parts[-2:]), cat
        return None

    def normalise_callee(self, raw: str) -> str:
        """Strip the macro `!` so a local `macro_rules!` target can resolve.

        The `!` is kept in `stats.calls` for the hazard table, where `panic!`
        and a method named `panic` must not collide. Resolution wants the bare
        name, because that is what `macro_definition` registered.
        """
        return raw.strip().rstrip("!")

    def is_external(self, name: str, base: str, fid: int) -> bool:
        """std, core, alloc, the prelude and the built-in macros.

        These leave the tree by design. Folding them into `unresolved_calls`
        would make a normal crate read as 80% blind when nearly all of it is
        `Option::unwrap` behaving exactly as documented, and the honesty column
        would stop distinguishing anything.
        """
        flat = name.replace(".", "::")
        head = flat.split("::")[0]
        if head in STD_ROOTS or head == "crate" or head == "Self":
            return True
        if base in STD_MACROS and base not in self.by_name:
            return True
        if base in PRELUDE or head in PRELUDE:
            return True
        # A method call on a receiver we cannot type: `x.foo()` where nothing
        # in the tree defines `foo`. That is genuinely lost, not external.
        return False

    # -- language-specific tables -----------------------------------------
    def function_extra(self, node: Any, rec: FileRec, db: sqlite3.Connection,
                       bufs: Buffers, sid: int, scope: Scope,
                       stats: BodyStats) -> None:
        src = rec.data
        body = node.child_by_field_name(self.BODY_FIELD)
        is_unsafe_fn = 0
        for c in node.named_children:
            if c.type == "function_modifiers" and "unsafe" in text_of(c, src):
                is_unsafe_fn = 1
                break
        loop_types = set(self.LOOP_NODES)

        self._emit_generics(node, rec, bufs, sid)
        self._emit_attr_rows(node, rec, bufs, sid)
        # `unsafe` is not a call, so `hazard_of` can never see it and the
        # `n_unsafe` column would sit at zero on a crate that is nothing but
        # unsafe. The hazard row is written here, from the syntax.
        if is_unsafe_fn:
            bufs.add_hazard(sid, "unsafe fn", "unsafe", 1,
                            node.start_point[0] + 1)
        if body is None:
            return

        for n in walk(body):
            if n.type == "unsafe_block":
                bufs.add_hazard(sid, "unsafe {", "unsafe", 1,
                                n.start_point[0] + 1)
                self._emit_unsafe_block(n, rec, bufs, sid, is_unsafe_fn,
                                        _loop_depth(n, body, loop_types))
            elif n.type == "await_expression":
                self._emit_await(n, rec, bufs, sid, body, loop_types)
            elif n.type == "macro_invocation":
                m = n.child_by_field_name("macro")
                if m is None:
                    continue
                tt = None
                for c in n.named_children:
                    if c.type == "token_tree":
                        tt = c
                inner = text_of(tt, src) if tt is not None else ""
                bufs.rows("macros").append(
                    (sid, rec.fid, text_of(m, src)[:120], "invocation", 0,
                     len(inner),
                     int(bool(re.search(r'\b(fn|struct|impl|enum|trait)\s',
                                        inner))),
                     n.start_point[0] + 1))

    def type_extra(self, node: Any, rec: FileRec, db: sqlite3.Connection,
                   bufs: Buffers, sid: int, scope: Scope) -> None:
        src = rec.data
        t = node.type
        self._emit_generics(node, rec, bufs, sid)
        self._emit_attr_rows(node, rec, bufs, sid)

        if t == "trait_item":
            body = node.child_by_field_name("body")
            req = prov = at = ac = 0
            names: list[str] = []
            if body is not None:
                for c in body.named_children:
                    if c.type == "function_signature_item":
                        req += 1
                        names.append(self.node_name(c, rec))
                    elif c.type == "function_item":
                        prov += 1
                        names.append(self.node_name(c, rec))
                    elif c.type == "associated_type":
                        at += 1
                    elif c.type == "const_item":
                        ac += 1
            bounds = node.child_by_field_name("bounds")
            n_super = sum(1 for n in walk(bounds)
                          if n.type in ("type_identifier", "generic_type")) \
                if bounds is not None else 0
            bufs.rows("traits").append(
                (sid, rec.fid, self.node_name(node, rec)[:120], req, prov,
                 at, ac, n_super, int(_has_anon(node, "unsafe")),
                 int(self.visibility_of(node, rec) == "public"),
                 int(node.child_by_field_name("type_parameters") is not None),
                 int(at > 0), ",".join(names)[:400]))
        elif t == "impl_item":
            tr = node.child_by_field_name("trait")
            ty = node.child_by_field_name("type")
            body = node.child_by_field_name("body")
            n_m = n_um = 0
            if body is not None:
                for c in body.named_children:
                    if c.type not in ("function_item",
                                      "function_signature_item"):
                        continue
                    n_m += 1
                    if any(k.type == "function_modifiers"
                           and "unsafe" in text_of(k, src)
                           for k in c.named_children):
                        n_um += 1
            bufs.rows("impls").append(
                (sid, rec.fid,
                 _base_type(text_of(ty, src)) if ty is not None else "",
                 _base_type(text_of(tr, src)) if tr is not None else "",
                 int(_has_anon(node, "unsafe")), int(_has_anon(node, "!")),
                 int(node.child_by_field_name("type_parameters") is not None),
                 n_m, n_um, node.start_point[0] + 1))
        elif t == "macro_definition":
            rules = [c for c in node.named_children if c.type == "macro_rule"]
            txt = text_of(node, src)
            bufs.rows("macros").append(
                (sid, rec.fid, self.node_name(node, rec)[:120], "definition",
                 len(rules), len(txt),
                 int(bool(re.search(r'\b(fn|struct|impl|enum|trait)\s', txt))),
                 node.start_point[0] + 1))
        elif t in ("struct_item", "union_item"):
            self._emit_fields(node, rec, bufs, sid)
        elif t == "enum_item":
            body = node.child_by_field_name("body")
            if body is not None:
                for i, v in enumerate(
                        c for c in body.named_children
                        if c.type == "enum_variant"):
                    vb = v.child_by_field_name("body")
                    bufs.enum_members.append(
                        (sid, i, self.node_name(v, rec)[:120], None,
                         len(vb.named_children) if vb is not None else 0))

    # -- helpers that write rows ------------------------------------------
    def _emit_fields(self, node: Any, rec: FileRec, bufs: Buffers,
                     sid: int) -> None:
        src = rec.data
        body = node.child_by_field_name("body")
        if body is None:
            return
        i = 0
        for f in body.named_children:
            if f.type not in ("field_declaration",):
                continue
            nm = f.child_by_field_name("name")
            tn = f.child_by_field_name("type")
            ftype = text_of(tn, src) if tn is not None else ""
            vis = "public" if any(c.type == "visibility_modifier"
                                  for c in f.named_children) else "private"
            bufs.fields.append(
                (sid, i, (text_of(nm, src) if nm is not None else "_")[:120],
                 ftype[:200], vis, f.start_point[0] + 1, 0, 0, 0,
                 int(ftype.startswith("Option<")),
                 int(ftype.startswith(("Vec<", "HashMap<", "BTreeMap<",
                                       "HashSet<", "VecDeque<", "["))),
                 0, 0, ftype.count("<") + ftype.count("&")))
            i += 1

    def _emit_generics(self, node: Any, rec: FileRec, bufs: Buffers,
                       sid: int) -> None:
        """Type parameters, their bounds and every lifetime, as rows.

        Bounds are what monomorphisation multiplies and what `dyn` erases, so
        they are worth having per-parameter rather than only as a count.
        """
        src = rec.data
        tp = node.child_by_field_name("type_parameters")
        if tp is not None:
            for p in tp.named_children:
                if p.type == "lifetime_parameter":
                    nm = text_of(p, src).strip()
                    bufs.rows("lifetimes").append(
                        (sid, rec.fid, nm[:60], "param",
                         int(nm == "'static"), p.start_point[0] + 1))
                elif p.type in ("type_parameter", "const_parameter"):
                    pname = self.node_name(p, rec) or text_of(p, src)[:40]
                    b = p.child_by_field_name("bounds")
                    if b is None:
                        continue
                    for bd in b.named_children:
                        bufs.rows("generic_bounds").append(
                            (sid, pname[:80], text_of(bd, src)[:160], 0,
                             int(bd.type in ("higher_ranked_trait_bound",
                                             "for_lifetimes")),
                             bd.start_point[0] + 1))
        for c in node.named_children:
            if c.type != "where_clause":
                continue
            for pred in c.named_children:
                if pred.type != "where_predicate":
                    continue
                left = pred.child_by_field_name("left")
                b = pred.child_by_field_name("bounds")
                lname = text_of(left, src)[:80] if left is not None else "?"
                if b is None:
                    continue
                for bd in b.named_children:
                    bufs.rows("generic_bounds").append(
                        (sid, lname, text_of(bd, src)[:160], 1,
                         int(bd.type in ("higher_ranked_trait_bound",
                                         "for_lifetimes")),
                         bd.start_point[0] + 1))
        params = node.child_by_field_name("parameters")
        ret = node.child_by_field_name("return_type")
        for sub in (params, ret):
            if sub is None:
                continue
            for n in walk(sub):
                if n.type != "lifetime":
                    continue
                nm = text_of(n, src).strip()
                bufs.rows("lifetimes").append(
                    (sid, rec.fid, nm[:60], "use", int(nm == "'static"),
                     n.start_point[0] + 1))

    def _emit_attr_rows(self, node: Any, rec: FileRec, bufs: Buffers,
                        sid: int) -> None:
        """`#[derive]`, `#[cfg]` and the rest, from the SIBLINGS above.

        tree-sitter models an attribute as a sibling of the item it decorates,
        not a child, so the whole attribute surface is invisible to anything
        that only looks inside the node.
        """
        src = rec.data
        prev = node.prev_sibling
        while prev is not None and prev.type == "attribute_item":
            a = None
            for c in prev.named_children:
                if c.type == "attribute":
                    a = c
                    break
            if a is None:
                prev = prev.prev_sibling
                continue
            nm = ""
            for c in a.named_children:
                if c.type in ("identifier", "scoped_identifier"):
                    nm = text_of(c, src)
                    break
            args_node = a.child_by_field_name("arguments")
            args = text_of(args_node, src) if args_node is not None else ""
            line = prev.start_point[0] + 1
            bufs.attributes.append((sid, rec.fid, nm[:120], args[:300], line))
            if nm == "derive":
                for d in re.findall(r'[A-Za-z_][\w:]*', args):
                    bufs.rows("derives").append(
                        (sid, rec.fid, d[:80],
                         int(d in _STD_DERIVES), line))
            elif nm in ("cfg", "cfg_attr"):
                feat = CFG_FEATURE_RE.search(args)
                bufs.rows("cfg_blocks").append(
                    (rec.fid, sid, args[:200],
                     feat.group(1)[:80] if feat else "",
                     int("test" in args), int(nm == "cfg_attr"), line))
            prev = prev.prev_sibling

    def _emit_unsafe_block(self, n: Any, rec: FileRec, bufs: Buffers,
                           sid: int, in_unsafe_fn: int, depth: int) -> None:
        """One row per `unsafe { }`, with the ops it contains and its SAFETY note.

        Counting ops per block rather than per function is what separates a
        one-line `unsafe { *p }` from a forty-line block doing six different
        things behind one comment -- clippy::multiple_unsafe_ops_per_block
        exists for exactly that, and the comment usually only explains one.
        """
        src = rec.data
        deref = raw_calls = trans = from_raw = 0
        for c in walk(n):
            if c.type == "unary_expression" and c.child_count \
                    and c.children[0].type == "*":
                deref += 1
            elif c.type == "call_expression":
                fn = c.child_by_field_name("function")
                if fn is None:
                    continue
                # `mem::transmute::<A, B>(x)` -- the turbofish wrapper has to
                # be peeled or the last path segment is the type argument list
                # and every transmute inside an unsafe block reads as zero.
                if fn.type == "generic_function":
                    fn = fn.child_by_field_name("function") or fn
                nm = text_of(fn, src)
                base = nm.replace(".", "::").split("::")[-1]
                if base in ("transmute", "transmute_copy"):
                    trans += 1
                elif base.startswith("from_raw"):
                    from_raw += 1
                elif base in ("get_unchecked", "get_unchecked_mut",
                              "unwrap_unchecked", "set_len",
                              "copy_nonoverlapping", "assume_init",
                              "from_raw_parts", "from_raw_parts_mut"):
                    raw_calls += 1
                else:
                    raw_calls += 1
        txt = src[n.start_byte:n.end_byte].decode("utf-8", "replace")
        bufs.rows("unsafe_blocks").append(
            (sid, rec.fid, n.start_point[0] + 1,
             sum(1 for l in txt.splitlines() if l.strip()),
             deref + raw_calls + trans + from_raw,
             deref, raw_calls, trans, from_raw,
             int(_has_safety_comment(n, src)), in_unsafe_fn, int(depth > 0)))

    def _emit_await(self, n: Any, rec: FileRec, bufs: Buffers, sid: int,
                    body: Any, loop_types: set) -> None:
        """One row per `.await`, with the lock guards still alive at it.

        A `MutexGuard` lives until the end of its block, so an `.await` after
        `let g = m.lock()` holds a std mutex across a yield point -- the tokio
        deadlock that only appears under load. Liveness here is lexical: the
        guard's `let` is in an ancestor block and starts earlier in the file.
        """
        src = rec.data
        guards: list[str] = []
        # The borrow VALUE text (`cell.borrow()`) never names RefCell -- the
        # type lives in the declaration. The enclosing function's signature
        # (params, generics) is the honest textual source: a function whose
        # text mentions RefCell and has a live guard at an await is the trap.
        fn_sig_has_refcell = re.search(
            r'\bRefCell\b', text_of(body.parent, src)[:600]) \
            if body.parent is not None else False
        has_refcell = int(bool(fn_sig_has_refcell))
        dropped = 0
        cur = n.parent
        while cur is not None and cur.id != body.parent.id:
            if cur.type == "block":
                for c in cur.named_children:
                    if c.type != "let_declaration" \
                            or c.start_byte >= n.start_byte:
                        continue
                    val = c.child_by_field_name("value")
                    if val is None or not GUARD_RE.search(text_of(val, src)):
                        continue
                    pat = c.child_by_field_name("pattern")
                    gname = text_of(pat, src).strip() if pat is not None else "_"
                    span = src[c.end_byte:n.start_byte].decode(
                        "utf-8", "replace")
                    if re.search(r'\bdrop\s*\(\s*%s\s*\)' % re.escape(gname),
                                 span):
                        dropped = 1
                        continue
                    guards.append(gname[:40])
            cur = cur.parent
        bufs.rows("async_points").append(
            (sid, rec.fid, n.start_point[0] + 1,
             int(_loop_depth(n, body, loop_types) > 0),
             _loop_depth(n, body, loop_types),
             len(guards), ",".join(guards)[:200], dropped,
             text_of(n, src)[:120].replace("\n", " "), has_refcell))

    # -- file-level --------------------------------------------------------
    def parse_imports(self, root: Any, rec: FileRec, bufs: Buffers) -> None:
        src = rec.data
        for n in root.named_children:
            if n.type == "extern_crate_declaration":
                nm = n.child_by_field_name("name")
                bufs.imports.append(
                    (rec.fid, text_of(nm, src)[:300] if nm is not None else "?",
                     None, None, "extern crate", n.start_point[0] + 1,
                     1, 0, 0, 0, 0, 1))
                continue
            if n.type != "use_declaration":
                continue
            arg = n.child_by_field_name("argument")
            if arg is None:
                continue
            target = text_of(arg, src).replace("\n", " ")
            head = target.split("::")[0].strip()
            relative = head in ("crate", "self", "super")
            external = int(not relative and head not in STD_ROOTS)
            names = target.count(",") + 1 if "{" in target else 1
            alias = None
            if arg.type == "use_as_clause":
                al = arg.child_by_field_name("alias")
                alias = text_of(al, src) if al is not None else None
            bufs.imports.append(
                (rec.fid, target[:300], None, alias, "use",
                 n.start_point[0] + 1, external, int(relative),
                 int("*" in target), 0, 0, names))

    def parse_file_extra(self, root: Any, rec: FileRec,
                         db: sqlite3.Connection, bufs: Buffers) -> None:
        """Inner attributes and top-level cfg, which belong to no symbol."""
        src = rec.data
        for n in root.named_children:
            if n.type != "inner_attribute_item":
                continue
            a = None
            for c in n.named_children:
                if c.type == "attribute":
                    a = c
                    break
            if a is None:
                continue
            nm = ""
            for c in a.named_children:
                if c.type in ("identifier", "scoped_identifier"):
                    nm = text_of(c, src)
                    break
            args_node = a.child_by_field_name("arguments")
            args = text_of(args_node, src) if args_node is not None else ""
            bufs.attributes.append(
                (None, rec.fid, nm[:120], args[:300], n.start_point[0] + 1))
            if nm in ("cfg", "cfg_attr"):
                feat = CFG_FEATURE_RE.search(args)
                bufs.rows("cfg_blocks").append(
                    (rec.fid, None, args[:200],
                     feat.group(1)[:80] if feat else "",
                     int("test" in args), int(nm == "cfg_attr"),
                     n.start_point[0] + 1))

    def parse_manifests(self, root: str, db: sqlite3.Connection) -> None:
        """Cargo.toml: the edition, the MSRV and the feature list.

        The edition decides whether `let`-chains and bare `extern "C"` even
        parse, and `[features]` is the ONLY enumeration of what a
        `#[cfg(feature = "x")]` may legally name. Everything Q12 says depends
        on having read this rather than guessing.

        EVERY manifest one level down is read too, not only the root. Most
        real Rust repos are workspaces whose root manifest is nothing but
        `[workspace]` and whose features all live in the member crates --
        tokio is exactly this shape. Reading only the root would leave the
        declared-feature set empty and make every single `#[cfg(feature)]` in
        the repo look undeclared, which is a query that reports the tool's own
        blindness as a finding about the code.
        """
        paths = [os.path.join(root, "Cargo.toml")]
        try:
            for entry in sorted(os.listdir(root)):
                sub = os.path.join(root, entry, "Cargo.toml")
                if os.path.isfile(sub):
                    paths.append(sub)
        except OSError:
            pass
        paths = [p for p in paths if os.path.isfile(p)]
        if not paths:
            db.execute("INSERT OR REPLACE INTO meta(key,value) VALUES(?,?)",
                       ("edition", "unknown (no Cargo.toml found)"))
            return
        dep_rows: list[tuple] = []
        for i, path in enumerate(paths):
            try:
                text = open(path, encoding="utf-8", errors="replace").read()
            except OSError:
                continue
            # The root manifest wins for edition/name; members only add
            # features, because the root is what the reader thinks they ran on.
            if i == 0 or not self.edition:
                m = re.search(r'^\s*edition\s*=\s*"(\d+)"', text, re.M)
                if m:
                    self.edition = m.group(1)
                m = re.search(r'^\s*rust-version\s*=\s*"([^"]+)"', text, re.M)
                if m:
                    self.rust_version = m.group(1)
                m = re.search(r'^\s*name\s*=\s*"([^"]+)"', text, re.M)
                if m and not self.crate_name:
                    self.crate_name = m.group(1)
            self._read_features(text, db)
            # [dependencies] / [dev-dependencies]: declared crate names for
            # the manifest-vs-usage query. Workspace member manifests are
            # read too, matching the feature reading above.
            for sect, is_dev in (("dependencies", 0), ("dev-dependencies", 1)):
                block = re.search(
                    r'^\[%s\]\s*$(.*?)(?=^\[|\Z)' % sect, text,
                    re.M | re.S)
                if not block:
                    continue
                for dm in re.finditer(
                        r'^\s*([A-Za-z0-9_-]+)\s*=\s*(?:'
                        r'\{\s*version\s*=\s*"([^"]*)"|"([^"]*)")',
                        block.group(1), re.M):
                    dep_rows.append(
                        (dm.group(1)[:120],
                         (dm.group(2) or dm.group(3) or "")[:40], is_dev))

        meta_rows = (
            ("crate", self.crate_name or "?"),
            ("edition", self.edition or "2015 (unset)"),
            ("rust_version", self.rust_version or "(no MSRV declared)"),
            # The grammar accepts let-chains whatever the manifest says --
            # tree-sitter has no notion of an edition. This line is about what
            # RUSTC will do, which is the thing that decides whether an
            # `n_let_chains` hit is normal code or a compile error waiting.
            ("let_chains",
             "yes (edition 2024)" if self.edition == "2024"
             else "NO -- rustc rejects `if let ... && ...` before edition "
                  "2024; the grammar still parses it, so a non-zero "
                  "n_let_chains here is code that does not build"),
            ("declared_features",
             ", ".join(sorted(self.features)) if self.features else "(none)"),
        )
        db.executemany("INSERT OR REPLACE INTO meta(key,value) VALUES(?,?)",
                       meta_rows)
        if dep_rows:
            db.executemany(
                "INSERT INTO deps(name,version,is_dev) VALUES(?,?,?)",
                dep_rows)

    def _read_features(self, text: str, db: sqlite3.Connection) -> None:
        feat_rows: list[tuple] = []
        """`[features]` plus the implicit feature every optional dep declares."""
        block = re.search(r'^\[features\]\s*$(.*?)(?=^\[|\Z)', text,
                          re.M | re.S)
        if block:
            for line in block.group(1).splitlines():
                fm = re.match(r'\s*([A-Za-z0-9_\-]+)\s*=\s*\[(.*?)\]', line)
                if not fm or fm.group(1) in self.features:
                    continue
                name = fm.group(1)
                self.features.add(name)
                feat_rows.append(
                    (name, fm.group(2)[:300], int(name == "default")))
        # `serde = { version = "1", optional = true }` silently declares a
        # feature named `serde`, and `#[cfg(feature = "serde")]` is then legal.
        for dm in re.finditer(
                r'^\s*([A-Za-z0-9_\-]+)\s*=\s*\{[^}]*optional\s*=\s*true',
                text, re.M):
            if dm.group(1) in self.features:
                continue
            self.features.add(dm.group(1))
            feat_rows.append((dm.group(1), "(optional dep)", 0))

        if feat_rows:
            # One statement for every feature, per the no-single-row-DML rule.
            db.executemany(
                "INSERT INTO crate_features(name,enables,is_default) "
                "VALUES(?,?,?)", feat_rows)

    def flush_extra(self, db: sqlite3.Connection, bufs: Buffers) -> None:
        for tbl, sql in (
            ("traits",
             "INSERT OR IGNORE INTO traits(symbol_id,file_id,name,n_required,"
             "n_provided,n_assoc_types,n_assoc_consts,n_supertraits,is_unsafe,"
             "is_public,is_generic,has_assoc_type,methods) "
             "VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?)"),
            ("impls",
             "INSERT INTO impls(symbol_id,file_id,type_name,trait_name,"
             "is_unsafe,is_negative,is_generic,n_methods,n_unsafe_methods,"
             "line) VALUES(?,?,?,?,?,?,?,?,?,?)"),
            ("unsafe_blocks",
             "INSERT INTO unsafe_blocks(symbol_id,file_id,line,sloc,n_ops,"
             "n_deref,n_raw_calls,n_transmute,n_from_raw,has_safety_comment,"
             "in_unsafe_fn,in_loop) VALUES(?,?,?,?,?,?,?,?,?,?,?,?)"),
            ("derives",
             "INSERT INTO derives(symbol_id,file_id,name,is_std,line) "
             "VALUES(?,?,?,?,?)"),
            ("lifetimes",
             "INSERT INTO lifetimes(symbol_id,file_id,name,kind,is_static,"
             "line) VALUES(?,?,?,?,?,?)"),
            ("generic_bounds",
             "INSERT INTO generic_bounds(symbol_id,param,bound,in_where,"
             "is_hrtb,line) VALUES(?,?,?,?,?,?)"),
            ("macros",
             "INSERT INTO macros(symbol_id,file_id,name,kind,n_rules,"
             "body_bytes,defines_items,line) VALUES(?,?,?,?,?,?,?,?)"),
            ("cfg_blocks",
             "INSERT INTO cfg_blocks(file_id,symbol_id,expr,feature,is_test,"
             "is_attr_only,line) VALUES(?,?,?,?,?,?,?)"),
            ("async_points",
             "INSERT INTO async_points(symbol_id,file_id,line,in_loop,"
             "loop_depth,n_guards_live,guards,guard_dropped,expr,"
             "has_refcell_guard) "
             "VALUES(?,?,?,?,?,?,?,?,?,?)"),
            ("secret_candidates",
             "INSERT INTO secret_candidates(symbol_id,file_id,value,line) "
             "VALUES(?,?,?,?)"),
        ):
            rows = bufs.extra.get(tbl)
            if rows:
                db.executemany(sql, rows)

_STD_DERIVES = frozenset("""
Debug Clone Copy PartialEq Eq PartialOrd Ord Hash Default
""".split())

def _base_type(text: str) -> str:
    """`Widget<T, 4>` -> `Widget`, `&mut Foo` -> `Foo`, `[u8; 4]` -> `[u8; 4]`."""
    t = text.strip().lstrip("&")
    t = re.sub(r"^'\w+\s*", "", t).lstrip()
    if t.startswith("mut "):
        t = t[4:]
    t = t.split("<", 1)[0].strip()
    return t.rsplit("::", 1)[-1] if "::" in t else t

def _has_anon(node: Any, token: str) -> bool:
    """`unsafe impl`, `impl !Trait`, `unsafe trait` are anonymous tokens.

    They carry no field and no named node, so the only way to see them is to
    scan the unnamed children -- a text prefix check would also match `unsafe`
    appearing anywhere later in the item body.

    The scan stops at the first NAMED child, which is the trait or type name.
    Everything modifying the item sits before it, on both sides of the `impl`
    keyword: `unsafe` precedes it and `!` follows it.
    """
    for c in node.children:
        if c.is_named:
            return False
        if c.type == token:
            return True
    return False

def _impl_has_trait(node: Any) -> bool:
    """True if this function sits in an `impl Trait for Type` block."""
    p = node.parent
    if p is None or p.type != "declaration_list":
        return False
    gp = p.parent
    return gp is not None and gp.type == "impl_item" \
        and gp.child_by_field_name("trait") is not None

def _attr_names(node: Any, src: bytes) -> list[str]:
    """Names of the `#[...]` attributes immediately above an item."""
    out: list[str] = []
    prev = node.prev_sibling
    while prev is not None and prev.type == "attribute_item":
        for c in prev.named_children:
            if c.type != "attribute":
                continue
            for k in c.named_children:
                if k.type in ("identifier", "scoped_identifier"):
                    out.append(src[k.start_byte:k.end_byte]
                               .decode("utf-8", "replace"))
                    break
            break
        prev = prev.prev_sibling
    return out

def _attr_args(node: Any, src: bytes) -> list[str]:
    out: list[str] = []
    prev = node.prev_sibling
    while prev is not None and prev.type == "attribute_item":
        out.append(src[prev.start_byte:prev.end_byte]
                   .decode("utf-8", "replace"))
        prev = prev.prev_sibling
    return out

def _loop_depth(node: Any, stop: Any, loop_types: set) -> int:
    d = 0
    cur = node.parent
    while cur is not None and cur.id != stop.id:
        if cur.type in loop_types:
            d += 1
        cur = cur.parent
    return d

def _has_safety_comment(node: Any, src: bytes) -> bool:
    """A `// SAFETY:` note above the block, past the wrappers and the run.

    Two things have to be got right or this reads as a repo-wide failure:

    * An `unsafe { }` used as a statement is wrapped in an
      `expression_statement`, and as a value it is the `value` field of a
      `let_declaration`. Either way the comment is the WRAPPER's previous
      sibling, not the block's, so the search climbs until it finds a sibling.
    * A safety note is usually a paragraph, and tree-sitter makes every `//`
      line its own node. Checking only the immediately preceding line finds
      the last line of the note -- `// so the pointer is live here` -- and
      concludes there is no note at all. The whole contiguous run of comments
      is checked instead.
    """
    cur = node
    for _ in range(4):
        prev = cur.prev_sibling
        while prev is not None and prev.type == "attribute_item":
            prev = prev.prev_sibling
        if prev is not None:
            n = 0
            while prev is not None and n < 20 and \
                    prev.type in ("line_comment", "block_comment"):
                txt = src[prev.start_byte:prev.end_byte].decode(
                    "utf-8", "replace")
                if SAFETY_RE.search(txt) is not None:
                    return True
                prev = prev.prev_sibling
                n += 1
            return False
        cur = cur.parent
        if cur is None:
            return False
    return False

RustAnalyzer.QUERIES = [
(
    "unsafe-under-pub-api",
    "unsafe reachable from a public function, up to 4 hops",
    "ANSWERS which `unsafe` a caller outside this crate can reach without\n"
    "     writing `unsafe` themselves -- the exact set that has to be sound\n"
    "     for ALL inputs, not just the ones the crate happens to pass.\n"
    "ACT split by documented: an undocumented block on a public path is where\n"
    "     the soundness argument does not exist in writing. Those are the\n"
    "     fuzzing targets and the review queue, in that order.\n"
    "MISLEADS depth is capped at 4 hops and only RESOLVED edges are walked, so\n"
    "     this is a floor -- an unsafe block five frames down, or one reached\n"
    "     through a trait object, is missing entirely. A `pub` item inside a\n"
    "     private module is not actually reachable from outside the crate;\n"
    "     visibility here is the keyword, not the effective export.",
    """-- depth bounded at 4, and the originating pub fn is deliberately NOT
    -- carried: only the shortest distance matters, and keeping the root would
    -- make this (pub fns x reachable symbols) rows instead of (symbols x 5).
    -- On rust-lang/rust that is the difference between seconds and never.
    WITH RECURSIVE down(sym, depth) AS (
        SELECT s.id, 0 FROM symbols s
        WHERE s.is_public=1 AND s.kind IN ('function','method')
        UNION
        SELECT e.callee_id, d.depth+1
        FROM down d JOIN edges e ON e.caller_id=d.sym
        WHERE d.depth < 4 AND e.is_self=0),
    best AS (SELECT sym, MIN(depth) AS depth FROM down GROUP BY sym)
    SELECT s.name, s.impl_type AS on_type, b.depth AS hops_from_pub,
        s.is_unsafe_fn AS unsafe_fn, s.n_unsafe_blocks AS blocks,
        s.n_unsafe_ops AS ops, s.n_safety_comments AS documented,
        s.n_transmute AS transmutes, s.n_from_raw AS from_raw,
        s.fan_in, f.path || ':' || s.line_start AS at
    FROM best b JOIN symbols s ON s.id=b.sym
    JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE (s.n_unsafe_blocks > 0 OR s.is_unsafe_fn=1)
      AND f.is_test=0 AND COALESCE(m.name,'') LIKE :mod
    ORDER BY (s.n_unsafe_blocks - s.n_safety_comments) DESC,
        b.depth ASC, s.n_unsafe_ops DESC LIMIT :lim"""),
(
    "panic-frontier",
    "unwrap, indexing and unchecked arithmetic on a public or spawned path",
    "ANSWERS where a panic becomes someone else's problem: a `pub` function\n"
    "     panicking aborts a caller who never opted in, and a panic inside a\n"
    "     spawned task kills that task silently while the join handle is\n"
    "     dropped.\n"
    "ACT the ranking is by blast: panic sites times callers. Return a Result\n"
    "     from the ones at the top; `get()` instead of `[]`; `checked_add`\n"
    "     where overflow is possible.\n"
    "MISLEADS the blast column multiplies by MAX(fan_in,1), so a symbol with\n"
    "     NO known caller scores exactly as if it had one. Read fan_in=0\n"
    "     rows as 'unknown reach', never as 'reach of 1'.\n"
    "     an `unwrap` after a checked `is_some()`, on a compile-time\n"
    "     constant, or on a `Mutex` that is never poisoned is correct code and\n"
    "     is counted here in full. Test files are excluded but a helper called\n"
    "     only from tests is not. n_arith_unchecked subtracts explicit\n"
    "     checked_/wrapping_ calls, but overflow only panics in debug builds\n"
    "     -- in release it wraps, which is a different bug.",
    """SELECT s.name, s.impl_type AS on_type, s.is_public AS pub_,
        s.n_unwrap AS unwrap_, s.n_expect AS expect_,
        s.n_panic_macro AS panic_macro, s.n_index_expr AS index_,
        s.n_slice_range AS slices, s.n_arith_unchecked AS unchecked_arith,
        s.n_borrow_calls AS refcell_borrow,
        s.n_spawn AS spawns, s.fan_in, s.return_type,
        (s.n_unwrap + s.n_expect*1 + s.n_panic_macro*2 + s.n_index_expr)
            * MAX(s.fan_in,1) AS blast,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE (s.is_public=1 OR s.n_spawn > 0)
      AND (s.n_unwrap + s.n_expect + s.n_panic_macro + s.n_index_expr
           + s.n_slice_range + s.n_borrow_calls) > 0
      AND s.is_test=0 AND f.is_test=0 AND f.is_generated=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY blast DESC, s.n_panic_macro DESC LIMIT :lim"""),
(
    "lock-held-across-await",
    "A guard still alive at a .await, here or up to 3 frames down",
    "ANSWERS clippy::await_holding_lock raised to the call graph. A std\n"
    "     MutexGuard held across a yield point blocks every other task on that\n"
    "     executor thread; a RefCell borrow held across one panics instead.\n"
    "     The cross-frame half is the part no per-function lint can reach:\n"
    "     the lock is taken here, the await happens in the callee.\n"
    "ACT take what you need out of the guard, drop it, then await. An explicit\n"
    "     `drop(g)` before the await already counts as fixed and is excluded.\n"
    "MISLEADS guard liveness is LEXICAL -- a `let` in an enclosing block that\n"
    "     starts earlier in the file. A guard moved into a closure, returned,\n"
    "     or shadowed is mis-read, and `tokio::sync::Mutex` guards are held\n"
    "     across awaits deliberately and correctly. Check which Mutex it is\n"
    "     before touching the row.",
    """-- depth bounded at 3: the interesting distance is one or two frames,
    -- and an unbounded walk of a large async crate does not return.
    WITH RECURSIVE walk(root, sym, depth) AS (
        SELECT s.id, s.id, 0 FROM symbols s WHERE s.n_lock_acquire > 0
        UNION
        SELECT d.root, e.callee_id, d.depth+1
        FROM walk d JOIN edges e ON e.caller_id=d.sym
        WHERE d.depth < 3 AND e.is_self=0),
        -- One row per (root, sym) pair. The recursive walk emits one row per
        -- DEPTH at which a symbol is reachable, so joining it straight to
        -- the per-site table counted every site once per distinct path
        -- length. Collapse to the shortest path before counting.
        down(root, sym, depth) AS (
            SELECT root, sym, MIN(depth) FROM walk GROUP BY root, sym)
    SELECT h.name AS takes_lock, s.name AS awaits_in,
        MIN(down.depth) AS hops, COUNT(a.id) AS await_points,
        SUM(a.n_guards_live) AS guards_live,
        SUM(a.guard_dropped) AS explicit_drops,
        SUM(a.in_loop) AS in_loop, MAX(a.loop_depth) AS depth,
        h.n_lock_acquire AS locks, s.is_async_fn AS async_,
        GROUP_CONCAT(DISTINCT NULLIF(a.guards,'')) AS guard_names,
        f.path || ':' || MIN(a.line) AS at
    FROM down
    JOIN symbols s ON s.id=down.sym
    JOIN symbols h ON h.id=down.root
    JOIN async_points a ON a.symbol_id=s.id
    JOIN files f ON f.id=a.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE f.is_test=0 AND COALESCE(m.name,'') LIKE :mod
    GROUP BY h.id, s.id
    HAVING guards_live > 0 OR (hops > 0 AND locks > 0 AND await_points > 0)
    ORDER BY guards_live DESC, in_loop DESC, hops ASC LIMIT :lim"""),
(
    "blocking-io-in-async",
    "std blocking calls reachable from an async fn without a spawn_blocking",
    "ANSWERS which executor threads get parked. `fs::read_to_string` or\n"
    "     `thread::sleep` under an async fn stalls every other task sharing\n"
    "     that worker, and the symptom is latency with an idle CPU.\n"
    "ACT move it behind `spawn_blocking`, or use the async filesystem API.\n"
    "     crosses_spawn_blocking is the counter-evidence: a call chain that\n"
    "     already goes through one is fine and is shown so you can skip it.\n"
    "MISLEADS the boundary test is whether ANY function on the path calls\n"
    "     spawn_blocking, not whether THIS call is inside the closure it\n"
    "     passed -- so a function that uses spawn_blocking elsewhere reads as\n"
    "     safe here. Startup and shutdown paths block deliberately. Depth is\n"
    "     capped at 4 hops, so deeper blocking is invisible.",
    """-- depth bounded at 4 hops from each async fn. `crossed` is kept as a
    -- 0/1 FLAG rather than a running sum: a sum makes every distinct path to
    -- the same node a distinct CTE row, which defeats the UNION's dedup and
    -- turns a dense async graph into a combinatorial walk.
    WITH RECURSIVE down(root, sym, depth, crossed) AS (
        SELECT s.id, s.id, 0, MIN(s.n_spawn_blocking,1) FROM symbols s
        WHERE s.is_async_fn=1
        UNION
        SELECT d.root, e.callee_id, d.depth+1,
            MAX(d.crossed, MIN(COALESCE(c.n_spawn_blocking,0),1))
        FROM down d JOIN edges e ON e.caller_id=d.sym
        JOIN symbols c ON c.id=e.callee_id
        WHERE d.depth < 4 AND e.is_self=0)
    SELECT a.name AS async_fn, s.name AS blocks_in,
        MIN(down.depth) AS hops, MAX(s.n_blocking_io) AS blocking_calls,
        MAX(s.io_in_loop) AS in_loop, MAX(down.crossed) AS crosses_spawn_blocking,
        MAX(s.n_await) AS awaits, a.fan_in AS async_fan_in,
        MAX(s.n_io) AS io_hazards,
        f.path || ':' || MIN(s.line_start) AS at
    FROM down
    JOIN symbols s ON s.id=down.sym
    JOIN symbols a ON a.id=down.root
    JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_blocking_io > 0 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    GROUP BY a.id, s.id
    HAVING crosses_spawn_blocking = 0
    ORDER BY blocking_calls DESC, hops ASC LIMIT :lim"""),
(
    "result-that-panics",
    "Functions returning Result or Option that panic anyway",
    "ANSWERS the contradiction a signature cannot express: the return type\n"
    "     promises the caller gets to decide, and the body takes the decision\n"
    "     away. A `-> Result<T, E>` containing `.unwrap()` is an error path\n"
    "     that was designed and then abandoned.\n"
    "ACT the `?` operator is already implied by the signature. On an Option\n"
    "     return `?` propagates ABSENCE and discards the reason, so the fix\n"
    "     there is usually a Result, not a `?`. Ratio of\n"
    "     question_marks to panics tells you whether this is one straggler or\n"
    "     a function that never used its error type.\n"
    "MISLEADS `unwrap` on a value proven present three lines up is correct.\n"
    "     A panic in a builder that only runs at startup, or on a poisoned\n"
    "     mutex where continuing is worse, is a deliberate choice. This finds\n"
    "     the shape, not the intent.",
    """SELECT s.name, s.impl_type AS on_type, s.is_public AS pub_,
        s.return_type,
        s.n_unwrap AS unwrap_, s.n_expect AS expect_,
        s.n_panic_macro AS panics, s.n_index_expr AS index_,
        s.n_question_mark AS question_marks,
        s.n_control AS catch_unwind, s.fan_in, s.cyclomatic AS cyclo,
        CAST(100.0 * (s.n_unwrap + s.n_expect + s.n_panic_macro)
             / NULLIF(s.n_unwrap + s.n_expect + s.n_panic_macro
                      + s.n_question_mark, 0) AS INT) AS pct_panic,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE (s.return_type LIKE '%Result<%' OR s.return_type LIKE '%Option<%')
      AND (s.n_unwrap + s.n_expect + s.n_panic_macro) > 0
      AND s.is_test=0 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY pct_panic DESC, s.fan_in DESC LIMIT :lim"""),
(
    "rc-cycle-risk",
    "Modules full of Rc<RefCell<>> and Arc<Mutex<>> with no Weak anywhere",
    "ANSWERS the only way to leak memory in safe Rust. A reference cycle\n"
    "     through `Rc` never drops, and `Weak` is the single construct that\n"
    "     breaks one -- so its ABSENCE in a module built on shared ownership\n"
    "     is the signal, not the presence of Rc.\n"
    "ACT parent links go in `Weak`, child links in `Rc`. If the module models\n"
    "     a graph or a tree with back-edges and has zero Weak, assume the\n"
    "     cycle exists until someone shows otherwise.\n"
    "MISLEADS an acyclic Rc graph -- a DAG of shared config, an interner --\n"
    "     never leaks and has no reason to use Weak. This counts type\n"
    "     spellings in signatures and bodies, so a cycle formed through a type\n"
    "     alias or a nested struct field is invisible. Arc<Mutex<>> is here\n"
    "     because it is the same shape, but it leaks far less often.",
    """SELECT m.name AS module_, COUNT(DISTINCT s.id) AS symbols_,
        SUM(s.n_rc_refcell) AS rc_refcell, SUM(s.n_arc_mutex) AS arc_mutex,
        SUM(s.n_weak_refs) AS weak_refs,
        SUM(s.n_borrow_calls) AS refcell_borrows,
        SUM(s.n_lock_acquire) AS lock_calls,
        SUM(s.n_clone) AS clones,
        COUNT(DISTINCT CASE WHEN s.kind IN ('struct','enum')
              THEN s.id END) AS types_
    FROM symbols s
    JOIN files f ON f.id=s.file_id
    JOIN modules m ON m.id=s.module_id
    WHERE f.is_test=0 AND m.name LIKE :mod
    GROUP BY m.id
    HAVING (rc_refcell + arc_mutex) > 0 AND weak_refs = 0
    ORDER BY rc_refcell DESC, arc_mutex DESC LIMIT :lim"""),
(
    "ffi-raw-balance",
    "into_raw without a from_raw, and unsafe impl Send on FFI types",
    "ANSWERS the two FFI leaks a per-function lint cannot see. `into_raw`\n"
    "     hands ownership to C and only `from_raw` takes it back; if the crate\n"
    "     has more of the first than the second, something is never freed.\n"
    "     `unsafe impl Send` is a promise to the compiler with no checker\n"
    "     behind it, and on a type holding a raw pointer it is the promise\n"
    "     most often wrong.\n"
    "ACT pair every into_raw with a documented from_raw, or use a wrapper type\n"
    "     with a Drop impl. Every `unsafe impl Send/Sync` needs a comment\n"
    "     saying why the type is actually thread-safe.\n"
    "MISLEADS the balance is counted per MODULE, not per allocation: the\n"
    "     into_raw and the from_raw legitimately live in different crates when\n"
    "     the API is a C ABI, and then an imbalance is correct by design.\n"
    "     Raw pointers behind a safe wrapper are fine and are counted here.",
    """SELECT m.name AS module_,
        SUM(s.n_into_raw) AS into_raw, SUM(s.n_from_raw) AS from_raw,
        SUM(s.n_into_raw) - SUM(s.n_from_raw) AS imbalance,
        SUM(s.n_raw_ptr) AS raw_ptr_types, SUM(s.n_transmute) AS transmutes,
        SUM(s.is_extern_fn) AS extern_fns, SUM(s.n_ffi) AS ffi_hazards,
        SUM(s.n_static_mut) AS static_mut,
        (SELECT COUNT(*) FROM impls i
         JOIN symbols si ON si.id=i.symbol_id
         WHERE si.module_id=m.id AND i.is_unsafe=1) AS unsafe_impls,
        (SELECT GROUP_CONCAT(DISTINCT i2.trait_name) FROM impls i2
         JOIN symbols s2 ON s2.id=i2.symbol_id
         WHERE s2.module_id=m.id AND i2.is_unsafe=1) AS promised
    FROM symbols s
    JOIN files f ON f.id=s.file_id
    JOIN modules m ON m.id=s.module_id
    WHERE f.is_test=0 AND m.name LIKE :mod
    GROUP BY m.id
    HAVING (into_raw + from_raw + unsafe_impls + static_mut) > 0
    ORDER BY ABS(imbalance) DESC, unsafe_impls DESC LIMIT :lim"""),
(
    "safety-doc-debt",
    "unsafe blocks doing several things behind no SAFETY comment",
    "ANSWERS clippy::undocumented_unsafe_blocks and\n"
    "     multiple_unsafe_ops_per_block together, ranked by how much is\n"
    "     riding on the missing comment. A block with six raw operations and\n"
    "     no note is six soundness arguments nobody wrote down.\n"
    "ACT one `// SAFETY:` per block, naming the invariant that makes it sound.\n"
    "     Blocks with the most ops first -- and if the invariant is hard to\n"
    "     state, that is the finding.\n"
    "MISLEADS op counting is coarse: every call inside the block counts, so a\n"
    "     safe helper called from an unsafe block inflates n_ops. The comment\n"
    "     check reads the whole contiguous comment run directly above the\n"
    "     block, which catches a multi-line note but NOT a SAFETY paragraph in\n"
    "     the enclosing function's doc comment or in an `# Safety` rustdoc\n"
    "     section -- a crate that documents at the function level will look\n"
    "     entirely undocumented here. fn_documented is the counter-evidence\n"
    "     column: read it before believing the row.",
    """SELECT s.name AS in_fn, s.impl_type AS on_type, u.line,
        u.n_ops, u.n_deref AS derefs, u.n_transmute AS transmutes,
        u.n_from_raw AS from_raw, u.n_raw_calls AS calls_,
        u.sloc AS block_sloc, u.in_unsafe_fn AS in_unsafe_fn,
        u.in_loop, s.is_public AS pub_, s.has_doc AS fn_documented,
        s.fan_in, f.path || ':' || u.line AS at
    FROM unsafe_blocks u
    JOIN symbols s ON s.id=u.symbol_id
    JOIN files f ON f.id=u.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE u.has_safety_comment = 0 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY u.n_ops DESC, s.fan_in DESC LIMIT :lim"""),
(
    "suppression-clusters",
    "#[allow] sitting on top of code that actually does the thing",
    "ANSWERS where a lint was silenced rather than answered. An `#[allow]` on\n"
    "     a function with no matching hazard is stale and harmless; one on a\n"
    "     function full of unwraps, unsafe or clones is a decision someone\n"
    "     made once and nobody has revisited.\n"
    "ACT `#[expect(...)]` instead of `#[allow(...)]` -- since Rust 1.81 it\n"
    "     warns when the lint stops firing, so the suppression expires by\n"
    "     itself. expect_attrs is the count already doing this.\n"
    "MISLEADS an allow can be perfectly justified, and this cannot read the\n"
    "     reason because there usually is not one. The attribute name is\n"
    "     matched to hazard counts by heuristic, not by which lint it names --\n"
    "     `#[allow(dead_code)]` on a function with unwraps will show up as a\n"
    "     panic suppression, which it is not. Read the args column.",
    """SELECT s.name, s.impl_type AS on_type,
        s.n_allow_attrs AS allows, s.n_expect_attrs AS expects,
        GROUP_CONCAT(DISTINCT SUBSTR(a.args,1,34)) AS suppressed,
        s.n_unwrap + s.n_expect AS panics_,
        s.n_unsafe_blocks AS unsafe_blocks, s.n_clone AS clones,
        s.n_index_expr AS index_, s.n_hazards AS hazards,
        s.is_public AS pub_, s.fan_in, s.risk_score AS risk,
        f.path || ':' || s.line_start AS at
    FROM symbols s
    JOIN attributes a ON a.symbol_id=s.id AND a.name IN ('allow','expect')
    JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE f.is_test=0 AND f.is_generated=0
      AND COALESCE(m.name,'') LIKE :mod
    GROUP BY s.id
    HAVING hazards > 0 OR unsafe_blocks > 0
    ORDER BY s.risk_score DESC, allows DESC LIMIT :lim"""),
(
    "arc-mutex-contention",
    "Arc<Mutex<..>> on hot paths: one lock every caller has to queue behind",
    "ANSWERS which shared-state choices will flatten under load. A single\n"
    "     Mutex behind a high fan_in function is a serialisation point --\n"
    "     throughput stops scaling with cores and latency grows a tail.\n"
    "ACT sharding beats a bigger critical section: per-key locks, a\n"
    "     DashMap-style striped map, or an actor owning the state with a\n"
    "     channel in front. If reads dominate, RwLock or arc-swap.\n"
    "MISLEADS a lock held for three instructions under low contention costs\n"
    "     almost nothing, and this cannot see contention -- only structure.\n"
    "     fan_in is NOT shown because it is zero for every Arc<Mutex>\n"
    "     holder measured -- these are usually struct fields reached\n"
    "     through a method, so the holder itself has no direct callers.",
    """SELECT s.name, s.impl_type AS impl_, s.n_arc_mutex AS arc_mutex,
        s.n_lock_acquire AS locks, s.n_rc_refcell AS rc_refcell,
        s.fan_out, s.max_loop_depth AS depth, s.n_await AS awaits,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_arc_mutex > 0 AND f.is_test=0 AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.n_arc_mutex DESC, s.n_lock_acquire DESC, s.fan_out DESC
    LIMIT :lim"""),
(
    "atomic-ordering-audit",
    "Relaxed and SeqCst orderings, and which functions mix them",
    "ANSWERS whether the memory orderings were chosen or defaulted. Relaxed\n"
    "     guarantees only atomicity, not ordering: it is correct for a\n"
    "     statistics counter and wrong for a flag that publishes data another\n"
    "     thread will read. SeqCst is always correct and always the slowest.\n"
    "ACT for a counter nobody synchronises on, Relaxed is right. For\n"
    "     publishing, use Release/Acquire. Reach for SeqCst only when the\n"
    "     algorithm genuinely needs a single global order.\n"
    "MISLEADS this counts orderings, it does not verify them. A Relaxed load\n"
    "     gating access to non-atomic data is a data race that looks\n"
    "     identical here to a correct Relaxed counter.",
    """SELECT s.name, s.impl_type AS impl_, s.n_atomic_ops AS atomics,
        s.n_relaxed_ordering AS relaxed, s.n_seqcst_ordering AS seqcst,
        s.n_spawn AS spawns, s.is_unsafe_fn AS unsafe_fn, s.fan_in,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_atomic_ops > 0 AND f.is_test=0 AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.n_relaxed_ordering DESC, s.n_atomic_ops DESC LIMIT :lim"""),
(
    "transmute-and-raw-pointers",
    "transmute, raw pointers and static mut: the parts the compiler cannot check",
    "ANSWERS where Rust's guarantees have been switched off by hand.\n"
    "     `transmute` reinterprets bits with no check at all; `static mut` is\n"
    "     a global with no synchronisation and is a hard error to reference\n"
    "     in edition 2024.\n"
    "ACT most transmutes have a safe replacement -- `from_bits`, `as` casts,\n"
    "     `bytemuck`, or a union with a documented invariant. For static mut\n"
    "     use OnceLock, atomics, or a Mutex.\n"
    "MISLEADS FFI code legitimately does all of this, and this cannot tell an\n"
    "     audited FFI shim from an unaudited shortcut. `safety_comments` is\n"
    "     the tell: unsafe with no SAFETY note is the shortlist.",
    """SELECT s.name, s.impl_type AS impl_, s.n_transmute AS transmutes,
        s.n_raw_ptr AS raw_ptrs, s.n_static_mut AS static_mut,
        s.n_from_raw AS from_raw, s.n_into_raw AS into_raw,
        s.n_unsafe_blocks AS unsafe_blocks,
        s.n_safety_comments AS safety_docs, s.is_extern_fn AS extern_,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE (s.n_transmute > 0 OR s.n_static_mut > 0 OR s.n_raw_ptr > 0)
      AND f.is_test=0 AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.n_transmute DESC, s.n_static_mut DESC,
        (s.n_unsafe_blocks - s.n_safety_comments) DESC LIMIT :lim"""),
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
("blocking-work-below-public-api", "a lock, a blocking sleep or I/O inside a loop, reachable from a public function",
    "ANSWERS what clippy sees per-function and cannot connect: `await_holding_lock`\n"
    "     and the perf lints fire on one body at a time. A lock taken inside a\n"
    "     loop is a convoy; the same code three frames under a published API is\n"
    "     a convoy any caller can trigger. This walks down from every `pub`\n"
    "     item and reports what it lands on.\n"
    "ACT hoist the lock out of the loop, or take it once and pass the guard.\n"
    "     `reached_from` names the published function whose contract now\n"
    "     includes this cost; `hops` says how much code sits between them.\n"
    "MISLEADS a `pub` item inside a private module is not part of the crate\'s\n"
    "     API and is counted here anyway -- `pub(crate)` and re-export chains\n"
    "     are not modelled. Depth stops at 4 hops. A lock in a loop over three\n"
    "     elements is fine and looks the same as one over three million.",
    """WITH RECURSIVE walk(root, sym, depth) AS (
        SELECT s.id, s.id, 0 FROM symbols s
        JOIN files f ON f.id = s.file_id
        WHERE s.is_public = 1 AND f.is_test = 0
        UNION
        SELECT w.root, e.callee_id, w.depth + 1
        FROM walk w JOIN edges e ON e.caller_id = w.sym
        WHERE w.depth < 4 AND e.is_self = 0),      -- depth bound: 4 hops
    reach(root, sym, depth) AS (
        SELECT root, sym, MIN(depth) FROM walk GROUP BY root, sym)
    SELECT s.name, entry.name AS reached_from, MIN(r.depth) AS hops,
        s.n_lock_in_loop AS lock_in_loop, s.n_io_in_loop AS io_in_loop,
        s.n_block_on AS block_on, s.n_thread_sleep AS sleeps,
        s.n_push_in_loop AS push_in_loop, s.is_async_fn AS is_async,
        s.fan_in, f.path || \':\' || s.line_start AS at
    FROM reach r
    JOIN symbols s ON s.id = r.sym
    JOIN symbols entry ON entry.id = r.root
    JOIN files f ON f.id = s.file_id
    LEFT JOIN modules m ON m.id = s.module_id
    WHERE r.depth > 0 AND f.is_test = 0
      AND (s.n_lock_in_loop > 0 OR s.n_io_in_loop > 0
           OR s.n_block_on > 0 OR s.n_thread_sleep > 0)
      AND COALESCE(m.name,\'\') LIKE :mod
    GROUP BY s.id, entry.id
    ORDER BY lock_in_loop DESC, io_in_loop DESC, hops ASC,
        s.fan_in DESC LIMIT :lim"""),
("runtime-borrow-panic-surface", "RefCell borrow_mut reachable from a public API, with the allocation churn around it",
    "ANSWERS the half of clippy\'s advice that is a runtime property: a\n"
    "     `borrow_mut()` is a compile-time-free, run-time-checked lock, and two\n"
    "     live borrows on one path is a panic, not an error. Reachability from\n"
    "     a public entry point is what turns that from a local invariant into\n"
    "     a caller-triggerable abort.\n"
    "ACT the columns rank by how hard the path is to reason about:\n"
    "     `borrow_muts` is the panic surface, `to_owned_in_loop` and\n"
    "     `push_in_loop` are the clippy perf lints on the same code, and a\n"
    "     function high in both is the one to restructure first.\n"
    "MISLEADS a single borrow_mut with no reentrancy cannot panic, and most\n"
    "     here are that. Depth is bounded at 4 hops. Interior mutability via\n"
    "     Mutex or atomics does not appear at all.",
    """WITH RECURSIVE walk(root, sym, depth) AS (
        SELECT s.id, s.id, 0 FROM symbols s
        WHERE s.is_public = 1 OR s.is_entrypoint = 1
        UNION
        SELECT w.root, e.callee_id, w.depth + 1
        FROM walk w JOIN edges e ON e.caller_id = w.sym
        WHERE w.depth < 4 AND e.is_self = 0),      -- depth bound: 4 hops
    reach(root, sym, depth) AS (
        SELECT root, sym, MIN(depth) FROM walk GROUP BY root, sym)
    SELECT s.name, entry.name AS reached_from, MIN(r.depth) AS hops,
        s.n_borrow_mut AS borrow_muts, s.n_unwrap_err AS unwraps,
        s.n_to_owned_in_loop AS to_owned_in_loop,
        s.n_push_in_loop AS push_in_loop,
        s.n_lock_in_loop AS lock_in_loop, s.fan_in,
        f.path || \':\' || s.line_start AS at
    FROM reach r
    JOIN symbols s ON s.id = r.sym
    JOIN symbols entry ON entry.id = r.root
    JOIN files f ON f.id = s.file_id
    LEFT JOIN modules m ON m.id = s.module_id
    WHERE s.n_borrow_mut > 0 AND r.depth > 0 AND f.is_test = 0
      AND COALESCE(m.name,\'\') LIKE :mod
    GROUP BY s.id, entry.id
    ORDER BY borrow_muts DESC, hops ASC, s.fan_in DESC LIMIT :lim"""),
(
    "clone-in-loop",
    ".clone() inside a loop (clippy perf/cloned_ref)",
    "ANSWERS where .clone() is called inside a loop, allocating a new object\n"
    "     each iteration. For large objects this is a significant cost.\n"
    "ACT borrow (use &T) if the clone is not needed, or clone once before the loop.\n"
    "MISLEADS a clone that is moved into a collection (Vec<T>) must happen per\n"
    "     iteration. The column counts sites, not allocations.",
    """SELECT s.name, s.n_to_owned_in_loop AS clones_in_loop,
        s.n_loops AS loops,
        s.n_push_in_loop AS pushes_in_loop,
        s.cyclomatic AS cyclo, s.fan_in,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_to_owned_in_loop > 0 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.n_to_owned_in_loop DESC, s.n_loops DESC LIMIT :lim"""),
(
    "unwrap-in-prod",
    ".unwrap() outside of test code (clippy restriction/unwrap_used)",
    "ANSWERS where .unwrap() is called in non-test code, which panics if the\n"
    "     Option/Result is None/Err. In production this is an unhandled crash.\n"
    "ACT use ? or match, or provide a fallback with unwrap_or/unwrap_or_else.\n"
    "MISLEADS unwrap after a contains_key check or on a known-present value is\n"
    "     safe. The graph sees the call but not the preceding check.",
    """SELECT s.name, s.n_unwrap_err AS unwraps,
        s.n_unchecked_call AS unchecked_calls,
        s.fan_in, s.cyclomatic AS cyclo,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_unwrap_err > 0 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.fan_in DESC, s.n_unwrap_err DESC LIMIT :lim"""),
(
    "expect-in-prod",
    ".expect() outside of test code (clippy restriction/expect_used)",
    "ANSWERS where .expect() is called, which panics with a message. Better than\n"
    "     unwrap but still a crash in production.\n"
    "ACT use ? or a proper error type.\n"
    "MISLEADS expect in a main() or init() that cannot recover is acceptable.",
    """SELECT s.name, s.n_unwrap_err AS expects_and_unwraps,
        s.fan_in, s.cyclomatic AS cyclo,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_unwrap_err > 0 AND s.fan_in > 3 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.fan_in DESC, s.n_unwrap_err DESC LIMIT :lim"""),
(
    "float-equality",
    "== comparison on floating point (clippy pedantic/float_cmp)",
    "ANSWERS where == is used on f32/f64, which is unreliable due to floating\n"
    "     point representation. Two values that should be equal may differ by\n"
    "     a tiny epsilon.\n"
    "ACT use (a - b).abs() < EPSILON or the approx crate.\n"
    "MISLEADS == on 0.0 or on values known to be exact (bit patterns) is safe.\n"
    "     The graph counts comparisons but not the operand types.",
    """SELECT s.name, s.n_cmp AS comparisons,
        s.n_arith_unchecked AS unchecked_arith,
        s.cyclomatic AS cyclo, s.fan_in,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_cmp > 3 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.n_cmp DESC, s.fan_in DESC LIMIT :lim"""),
(
    "unsafe-without-comment",
    "unsafe block without a safety comment (clippy/undocumented_unsafe_blocks)",
    "ANSWERS where an unsafe block has no safety comment documenting why it is\n"
    "     safe. Each unsafe block is a human-verified invariant; without a\n"
    "     comment, the invariant is lost.\n"
    "ACT add a `// SAFETY: ...` comment above each unsafe block.\n"
    "MISLEADS an unsafe fn's body is implicitly unsafe; the comment may be on the\n"
    "     fn, not the block. has_safety_comment is a lexical scan.",
    """SELECT s.name,
        (SELECT COUNT(*) FROM unsafe_blocks ub WHERE ub.symbol_id=s.id
         AND ub.has_safety_comment=0) AS uncommented_unsafe,
        (SELECT COUNT(*) FROM unsafe_blocks ub WHERE ub.symbol_id=s.id) AS total_unsafe,
        s.n_raw_ptr, s.n_transmute,
        s.fan_in, s.cyclomatic AS cyclo,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE EXISTS(SELECT 1 FROM unsafe_blocks ub WHERE ub.symbol_id=s.id
         AND ub.has_safety_comment=0)
      AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY uncommented_unsafe DESC, s.fan_in DESC LIMIT :lim"""),
(
    "vec-new-push-in-loop",
    "Vec::new() + push inside a loop (clippy perf/vec_push_in_loop)",
    "ANSWERS where a Vec is created with Vec::new() and then pushed to inside a\n"
    "     loop, causing multiple reallocations. Use with_capacity to pre-allocate.\n"
    "ACT if the final size is knowable, use Vec::with_capacity(n).\n"
    "MISLEADS a loop that pushes conditionally has no knowable size. n_push_in_loop\n"
    "     counts sites, not the Vec's growth pattern.",
    """SELECT s.name, s.n_push_in_loop AS pushes_in_loop,
        s.n_loops AS loops,
        s.n_to_owned_in_loop AS clones_in_loop,
        s.cyclomatic AS cyclo, s.fan_in,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_push_in_loop > 0 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.n_push_in_loop DESC, s.n_loops DESC LIMIT :lim"""),
(
    "transmute-misuse",
    "std::mem::transmute for type punning (clippy/unnecessary_transmute)",
    "ANSWERS where transmute is used, which reinterprets the bits of one type as\n"
    "     another. This is undefined behavior if the sizes don't match or the\n"
    "     target type has different validity invariants.\n"
    "ACT use TryFrom/TryInto, or a safe conversion method.\n"
    "MISLEADS transmute for FFI interop is sometimes necessary. The graph sees\n"
    "     the call but not the types involved.",
    """SELECT s.name, s.n_transmute AS transmutes,
        s.n_from_raw AS from_raw,
        s.n_into_raw AS into_raw,
        s.n_raw_ptr AS raw_ptrs,
        s.fan_in, s.cyclomatic AS cyclo,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_transmute > 0 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.fan_in DESC, s.n_transmute DESC LIMIT :lim"""),
(
    "static-mut-unsafe",
    "static mut without synchronization (clippy/static_mut_refs)",
    "ANSWERS where a static mut is used, which is shared mutable state with no\n"
    "     synchronization. Taking a reference to a static mut is UB if accessed\n"
    "     from multiple threads.\n"
    "ACT use a Mutex, RwLock, or AtomicX, or thread-local storage.\n"
    "MISLEADS a static mut accessed from a single-threaded context with\n"
    "     documented safety is technically safe but fragile.",
    """SELECT s.name, s.n_static_mut AS static_muts,
        s.n_atomic_ops AS atomic_ops,
        s.n_arc_mutex AS arc_mutexes,
        s.fan_in, s.cyclomatic AS cyclo,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_static_mut > 0 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.fan_in DESC, s.n_static_mut DESC LIMIT :lim"""),
(
    "block-on-async",
    ".block_on() on an async runtime (clippy/clippy/block_in_place)",
    "ANSWERS where .block_on() is called, which blocks the current thread to\n"
    "     drive a future. Inside an async context this deadlocks the runtime.\n"
    "ACT use .await, or spawn_blocking for sync code in an async context.\n"
    "MISLEADS block_on in a sync main() to start the runtime is correct. The\n"
    "     graph sees the call but not whether it's inside an async context.",
    """SELECT s.name, s.n_block_on AS block_ons,
        s.is_async_fn, s.n_await AS awaits,
        s.n_spawn_blocking AS spawn_blockings,
        s.fan_in, s.cyclomatic AS cyclo,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_block_on > 0 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.fan_in DESC, s.n_block_on DESC LIMIT :lim"""),
(
    "spawn-without-join",
    "tokio::spawn without storing the JoinHandle (clippy/tokio)",
    "ANSWERS where a task is spawned but the JoinHandle is discarded, so the\n"
    "     runtime may cancel the task at any time and errors are silently lost.\n"
    "ACT store the handle and await it, or use tokio::spawn with proper error\n"
    "     handling.\n"
    "MISLEADS a fire-and-forget background task that is intentionally detached is\n"
    "     a valid pattern for long-running workers.",
    """SELECT s.name, s.n_spawn AS spawns,
        s.n_spawn_blocking AS spawn_blockings,
        s.is_async_fn, s.fan_in,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_spawn > 0 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.fan_in DESC, s.n_spawn DESC LIMIT :lim"""),
(
    "import-cycle",
    "Circular module dependencies (madge/circular)",
    "ANSWERS which files form a use/cycle.\n"
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
    "relaxed-ordering",
    "Atomic with Relaxed ordering where Acquire/Release is needed (clippy/atomic)",
    "ANSWERS where Relaxed memory ordering is used, which provides no\n"
    "     synchronization between threads. For read-modify-write operations\n"
    "     that synchronize, Acquire/Release is needed.\n"
    "ACT use Acquire for loads, Release for stores, AcqRel for RMW.\n"
    "MISLEADS Relaxed for counters that don't synchronize is correct. The graph\n"
    "     counts orderings but not the synchronization intent.",
    """SELECT s.name, s.n_relaxed_ordering AS relaxed,
        s.n_seqcst_ordering AS seqcst,
        s.n_atomic_ops AS atomic_ops,
        s.fan_in, s.cyclomatic AS cyclo,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_relaxed_ordering > 0 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.n_relaxed_ordering DESC, s.fan_in DESC LIMIT :lim"""),
(
    "rc-refcell-mutation",
    "Rc<RefCell> for interior mutability (clippy/rc_buffer)",
    "ANSWERS where Rc<RefCell> is used, which is single-threaded and panics on\n"
    "     double borrow. For multi-threaded code, Arc<Mutex> is needed; for\n"
    "     single-threaded, Rc<Cell> for Copy types is cheaper.\n"
    "ACT use Arc<Mutex> if multi-threaded, or Rc<Cell> for Copy types.\n"
    "MISLEADS Rc<RefCell> for a single-threaded tree structure is correct.",
    """SELECT s.name, s.n_rc_refcell AS rc_refcells,
        s.n_arc_mutex AS arc_mutexes,
        s.n_weak_refs AS weak_refs,
        s.fan_in, s.cyclomatic AS cyclo,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_rc_refcell > 0 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.fan_in DESC, s.n_rc_refcell DESC LIMIT :lim"""),
(
    "len-in-loop",
    ".len() called inside a loop (clippy/len_zero)",
    "ANSWERS where .len() is called inside a loop on a collection, which may\n"
    "     be O(n) for some types (linked lists, certain iterators).\n"
    "ACT hoist .len() outside the loop if the length doesn't change.\n"
    "MISLEADS .len() on Vec is O(1); the column cannot distinguish O(1) from O(n).",
    """SELECT s.name, s.n_len_in_loop AS len_in_loop,
        s.n_loops AS loops,
        s.n_iter_in_loop AS iter_in_loop,
        s.cyclomatic AS cyclo, s.fan_in,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_len_in_loop > 0 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.n_len_in_loop DESC, s.n_loops DESC LIMIT :lim"""),
(
    "trait-breadth",
    "Traits implemented by the most distinct types",
    "ANSWERS the trait contracts with the widest implementor base -- the\n"
    "     seams that, if they change, every impl block (and every generic\n"
    "     bound) must change with them.\n"
    "ACT treat the top rows as breaking-change surfaces: adding a required\n"
    "     method to one of these compiles to errors across the whole crate.\n"
    "MISLEADS counts impl rows per trait NAME; a generic/blanket impl\n"
    "     (`impl<T: Trait>`) is counted once for its declaring type, not once\n"
    "     per concrete instantiator, so blankets undercount real breadth.\n"
    "     `dyn-with-one-impl` is the zero end of this same ranking.",
    """SELECT im.trait_name AS trait_, COUNT(DISTINCT im.type_name) AS impls,
        COUNT(DISTINCT im.file_id) AS in_files,
        SUM(im.n_methods) AS methods_impl,
        SUM(im.n_unsafe_methods) AS unsafe_methods,
        MIN(im.line) AS first_line
    FROM impls im
    WHERE im.trait_name <> ''
    GROUP BY im.trait_name
    HAVING impls >= 2
    ORDER BY impls DESC, methods_impl DESC LIMIT :lim"""),
(
    "macro-density",
    "Macro invocations per module: code generation heat map",
    "ANSWERS which modules lean heaviest on macro invocation -- every call\n"
    "     hides generated code from the call graph, so a module dense in\n"
    "     macro use is partially invisible to everyone after this.\n"
    "ACT a hot module is where a proc-macro bug or an expansion-size\n"
    "     regression hurts most; bodies hidden behind macros there deserve\n"
    "     eyeball coverage.\n"
    "MISLEADS counts invocations and definitions separately; `vec!`,\n"
    "     `println!` and friends from the prelude count as invocations but\n"
    "     are trivial, while a heavy proc macro in a cold module ranks low.\n"
    "     Expansion output is not modeled anywhere.",
    """SELECT m.name AS module_,
        COUNT(*) FILTER (WHERE mc.kind='invocation') AS invocations,
        COUNT(*) FILTER (WHERE mc.kind='definition') AS definitions,
        COUNT(*) FILTER (WHERE mc.kind='attribute') AS attrs,
        COALESCE(SUM(CASE WHEN mc.kind='invocation' THEN mc.body_bytes
                          ELSE 0 END), 0) AS invocation_body_bytes,
        COUNT(DISTINCT mc.file_id) AS in_files
    FROM macros mc
    LEFT JOIN modules m ON m.id=(SELECT f.module_id FROM files f
                                  WHERE f.id=mc.file_id)
    WHERE m.name LIKE :mod
    GROUP BY m.id
    ORDER BY invocations DESC, invocation_body_bytes DESC LIMIT :lim"""),
(
    "impl-fragmentation",
    "Types whose impl blocks are spread across many files",
    "ANSWERS how many distinct files host impl blocks for one type -- the\n"
    "     fragmentation that makes a type's full contract unreadable from\n"
    "     any single file. High fragmentation hides methods from casual\n"
    "     discovery and scatters the changes a trait addition demands.\n"
    "ACT consolidate inherent impls into the defining file; cross-file\n"
    "     trait impls are a real Rust pattern (coherence rules), so expect\n"
    "     the trait rows and judge inherent rows harder.\n"
    "MISLEADS a type and its impls in the same file count as one file here;\n"
    "     `#[cfg(test)]` impls and cfg-gated impls count as distinct\n"
    "     fragments even when small, and same-named types in different\n"
    "     modules merge under a bare type_name.",
    """SELECT im.type_name AS type_, COUNT(DISTINCT im.file_id) AS n_files,
        COUNT(*) AS n_impls,
        COUNT(*) FILTER (WHERE im.trait_name <> '') AS trait_impls,
        COUNT(*) FILTER (WHERE im.trait_name = '') AS inherent_impls,
        GROUP_CONCAT(DISTINCT f.basename) AS in_files
    FROM impls im JOIN files f ON f.id=im.file_id
    WHERE im.type_name <> ''
    GROUP BY im.type_name
    HAVING n_files >= 2
    ORDER BY n_files DESC, n_impls DESC LIMIT :lim"""),
(
    "ffi-crossings",
    "Calls that leave Rust into extern blocks",
    "ANSWERS which functions call FFI-declared extern fns -- every crossing\n"
    "     is a point where Rust's guarantees stop and C's rules begin. A\n"
    "     function dense in FFI calls is a boundary node: the place to audit\n"
    "     pointer lifetimes and null handling.\n"
    "ACT keep the crossing thin: validate pointers and lengths inside the\n"
    "     wrapper, never at the call site; prefer safe bindings (libloading\n"
    "     with a safe layer) over raw extern exposure.\n"
    "MISLEADS the extern fn count comes from foreign_mod_item tracking and\n"
    "     n_ffi (unsafe block ops); a call through a function POINTER\n"
    "     returned from FFI is invisible, and calling an extern fn inside\n"
    "     an unsafe block is counted while the block's safety comment is\n"
    "     not evidence either way.",
    """SELECT s.name, s.n_extern_calls AS ffi_calls,
        s.n_ffi AS ffi_hazards, s.n_unsafe_blocks AS unsafe_blocks,
        s.is_unsafe_fn AS unsafe_fn, s.fan_in, s.sloc,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_extern_calls > 0 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.n_extern_calls DESC, s.n_ffi DESC LIMIT :lim"""),
(
    "deep-module-paths",
    "Calls and imports spelled with long :: chains",
    "ANSWERS where paths are spelled in full instead of imported -- every\n"
    "     `crate::services::auth::db::connect` restates the module layout at\n"
    "     the call site, and a rename anywhere in the chain breaks every\n"
    "     re-statement.\n"
    "ACT import the target once (`use`), or shorten through a root alias;\n"
    "     the deepest rows are the most fragile to module moves.\n"
    "MISLEADS counts `::` segments in the import target text; a module\n"
    "     legitimately nested that deep (a crate convention) is not wrong,\n"
    "     and external crates' long paths are counted the same as local\n"
    "     ones. Calls whose path came from a macro expansion are unseen.",
    """SELECT i.target AS path_, i.is_external AS external,
        (length(i.target) - length(replace(i.target, '::', ''))) / 2 + 1
            AS segments,
        f.path AS importer
    FROM imports i JOIN files f ON f.id=i.file_id
    LEFT JOIN modules m ON m.id=f.module_id
    WHERE (length(i.target) - length(replace(i.target, '::', ''))) / 2 >= 4
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY segments DESC, i.is_external ASC LIMIT :lim"""),
(
    "async-task-hubs",
    "Async functions that spawn background tasks",
    "ANSWERS the async entry points that fire-and-forget tasks (tokio::\n"
    "     spawn / async_std::task::spawn / wasm_bindgen_futures::spawn_local\n"
    "     and friends) -- the roots of every background task tree in the\n"
    "     crate.\n"
    "ACT each row needs a documented lifetime rule: a spawned task that\n"
    "     outlives its context is a leak or a race; prefer scoped tasks\n"
    "     where the API allows. `spawn-without-join` covers the no-join\n"
    "     half; this ranks the hubs.\n"
    "MISLEADS counts spawn CALL SITES per async function; a spawn inside a\n"
    "     helper that the async hub calls is attributed to the helper, and\n"
    "     a spawn spelled through a wrapper function (`my_spawn(|| ...)`) is\n"
    "     invisible unless the wrapper name contains spawn.",
    """SELECT s.name, s.n_spawn AS spawns, s.n_await AS awaits,
        s.max_loop_depth AS depth, s.fan_in,
        s.is_async_fn AS is_async, s.sloc,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_spawn > 0 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.n_spawn DESC, s.fan_in DESC LIMIT :lim"""),
(
    "placeholder-panic-sites",
    "todo!/unimplemented!/unreachable!/panic! in production code",
    "ANSWERS the deployed crash points: todo!() and unimplemented!() compile\n"
    "     and ship, and each one is a panic waiting for the right input.\n"
    "     unreachable!() in an exhaustive-match fallback is the only\n"
    "     deliberate member of the set.\n"
    "ACT replace todo!/unimplemented! with a Result or a proper error path;\n"
    "     unreachable! needs a proof comment next to it.\n"
    "MISLEADS proc-macro expansions are invisible (they never hit this\n"
    "     table); a panicking macro spelled through a local `macro_rules!`\n"
    "     alias is invisible to name matching; test exclusion is\n"
    "     symbols.is_test, which may disagree with cfg(test) on odd trees.",
    """SELECT f.path, s.name AS fn, ma.name AS macro_, ma.line, s.fan_in
    FROM macros ma
    JOIN symbols s ON s.id = ma.symbol_id
    JOIN files f ON f.id = ma.file_id
    LEFT JOIN modules m ON m.id = s.module_id
    WHERE ma.kind = 'invocation'
      AND ma.name IN ('todo','unimplemented','unreachable','panic')
      AND s.is_test = 0 AND f.is_generated = 0 AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.fan_in DESC
    LIMIT :lim"""),
(
    "debug-print-residue",
    "dbg!() outside tests",
    "ANSWERS dbg!() calls in non-test code: the debugging print that ships.\n"
    "     dbg!() prints to stderr AND returns the value, so it also changes\n"
    "     evaluation order (a dbg!(f()) evaluates f() BEFORE the outer\n"
    "     expression context expects it).\n"
    "ACT replace with a proper log or remove; a dbg! that is deliberately\n"
    "     kept for support deserves a comment and a log target instead.\n"
    "MISLEADS name-based on the invocation capture: `eprintln!` is not dbg!\n"
    "     and does not appear; test files are excluded by is_test.",
    """    SELECT f.path, s.name AS fn, ma.line, s.sloc
    FROM macros ma
    JOIN symbols s ON s.id = ma.symbol_id
    JOIN files f ON f.id = ma.file_id
    LEFT JOIN modules m ON m.id = s.module_id
    WHERE ma.kind = 'invocation' AND ma.name = 'dbg'
      AND s.is_test = 0 AND f.is_generated = 0 AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.sloc DESC
    LIMIT :lim"""),
(
    "sql-string-build",
    "SQL text assembled by string building (OWASP G09 / A05)",
    "ANSWERS functions whose string literals contain SQL keywords AND which\n"
    "     also build strings (format!, or more than one string literal) -- the\n"
    "     shape that lets a query be glued together instead of parameterized.\n"
    "ACT use a parameterized statement (rusqlite params!, sea-orm bind); never\n"
    "     interpolate a variable into a SQL string.\n"
    "MISLEADS the pairing is same-function co-occurrence, NOT data flow: the\n"
    "     SQL literal and the format! may be unrelated, and a constant SQL\n"
    "     string beside unrelated string literals reads as a violation. A\n"
    "     constant format! with no interpolated variable is safe. The SQL\n"
    "     test is the literal's own text, so SQL in comments or identifiers\n"
    "     does not count.",
    """SELECT s.name, s.n_sql_literal AS sql_literals,
        s.n_format_macro AS format_calls,
        s.n_string_lit AS string_literals,
        s.fan_in, s.sloc,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id = s.file_id
    LEFT JOIN modules m ON m.id = s.module_id
    WHERE s.n_sql_literal > 0
      AND (s.n_format_macro > 0 OR s.n_string_lit > 1)
      AND f.is_test = 0 AND f.is_generated = 0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.fan_in DESC, s.n_sql_literal DESC LIMIT :lim"""),
(
    "command-build-surface",
    "Command::new sites -- the process boundary (OWASP G10 / A05)",
    "ANSWERS every function that constructs a Command -- the places a string\n"
    "     becomes a process. The string-building columns are context: a\n"
    "     Command::new with format! or literal churn in the same function is\n"
    "     where a built command line is likely.\n"
    "ACT use std::process::Command's argument array; never pass a shell string.\n"
    "MISLEADS .arg() chains are NOT counted (no argument capture), so an\n"
    "     arg-built command and a constant command rank the same. Name-based:\n"
    "     only the bare `Command::new`/`Command::spawn` call text matches;\n"
    "     `std::process::Command::new` is invisible. A constant command is\n"
    "     safe -- the graph sees the construction, not the argument source.",
    """SELECT s.name, h.pattern AS sink, h.n AS command_sites,
        s.n_string_lit AS string_literals,
        s.n_format_macro AS format_calls,
        s.fan_in, s.sloc,
        f.path || ':' || s.line_start AS at
    FROM hazards h
    JOIN symbols s ON s.id = h.symbol_id
    JOIN files f ON f.id = s.file_id
    LEFT JOIN modules m ON m.id = s.module_id
    WHERE h.pattern IN ('Command::new','Command::spawn')
      AND f.is_test = 0 AND f.is_generated = 0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.fan_in DESC, h.n DESC LIMIT :lim"""),
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
    WHERE f.is_test = 0 AND f.is_generated = 0
      AND COALESCE(m.name,'') LIKE :mod
      AND sc.value NOT LIKE '/%' AND instr(sc.value, '|') = 0
      AND instr(sc.value, '%') = 0
    ORDER BY length(sc.value) DESC LIMIT :lim"""),
(
    "untrusted-deserialization",
    "from_str / from_slice / from_reader deserialization sites (OWASP G19)",
    "ANSWERS functions that deserialize (serde_json, bincode, ron, toml all\n"
    "     spell from_str/from_slice/from_reader/from_bytes) -- the surface\n"
    "     where an untrusted payload becomes a value.\n"
    "ACT validate the payload schema and size before deserializing; never\n"
    "     deserialize into a permissive type from an untrusted source.\n"
    "MISLEADS WHICH input is untrusted is not modeled: a from_str on a\n"
    "     constant ranks the same as one on request data. The capture is the\n"
    "     bare base name, so a serialization helper wrapping the call is\n"
    "     invisible.",
    """SELECT s.name, s.n_deserialize AS deserialize_calls,
        s.sloc, f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id = s.file_id
    LEFT JOIN modules m ON m.id = s.module_id
    WHERE s.n_deserialize > 0 AND f.is_test = 0 AND f.is_generated = 0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.n_deserialize DESC, s.sloc DESC LIMIT :lim"""),
(
    "zip-slip-surface",
    "zip crate access sites (OWASP G29)",
    "ANSWERS functions that touch the zip crate (ZipArchive) -- the surface\n"
    "     where an entry name becomes a filesystem path.\n"
    "ACT validate every entry name against a containment check before\n"
    "     extraction; reject ../ and absolute paths.\n"
    "MISLEADS the containment check is not modeled: a function that checks\n"
    "     each name before extraction ranks the same as one that does not.\n"
    "     The capture is the dotted ZipArchive:: name; a renamed zip helper\n"
    "     is invisible.",
    """SELECT s.name, s.n_zip_read AS zip_access,
        s.sloc, f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id = s.file_id
    LEFT JOIN modules m ON m.id = s.module_id
    WHERE s.n_zip_read > 0 AND f.is_test = 0 AND f.is_generated = 0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.n_zip_read DESC, s.sloc DESC LIMIT :lim"""),
(
    "unsafe-in-loop",
    "unsafe blocks inside loop bodies",
    "ANSWERS unsafe blocks in loops: pointer arithmetic paid per iteration\n"
    "     is where memory bugs and hot paths meet. The review order is\n"
    "     n_deref first -- each deref is a place a dangling or misaligned\n"
    "     pointer becomes a fault.\n"
    "ACT hoist the invariant check; prove bounds once outside the loop.\n"
    "MISLEADS a well-audited unsafe hot loop (simd, ring buffers) is the\n"
    "     legitimate row -- this ranks review order, not guilt; n_ops is\n"
    "     syntactic and macro-generated unsafe is invisible; has_safety_comment\n"
    "     is the author's own claim of scrutiny.",
    """SELECT f.path, s.name AS fn, ub.n_ops, ub.n_deref,
        ub.has_safety_comment, ub.line
    FROM unsafe_blocks ub
    JOIN symbols s ON s.id = ub.symbol_id
    JOIN files f ON f.id = ub.file_id
    LEFT JOIN modules m ON m.id = s.module_id
    WHERE ub.in_loop = 1
      AND f.is_generated = 0 AND COALESCE(m.name,'') LIKE :mod
    ORDER BY ub.n_deref DESC, ub.n_ops DESC
    LIMIT :lim"""),
(
    "suppression-without-reason",
    "Bare #[allow(...)] without an explanation (clippy allow-without-reason)",
    "ANSWERS allow attributes with no reason given. The 1.83+ discipline is\n"
    "     #[expect(reason)] over #[allow(...)]: expect FAILS the build when\n"
    "     the lint stops firing, so the suppression cannot go stale; an allow\n"
    "     with no reason is a suppression nobody can audit.\n"
    "ACT add a reason, or convert to #[expect(...)] and let the compiler\n"
    "     verify the lint still fires.\n"
    "MISLEADS the reason is the ARGS text -- a bare `#[allow]` with no parens\n"
    "     at all is the sharpest row; `#[allow(unused)]` with a comment on\n"
    "     the next line is not distinguished from a reason-free allow.",
    """SELECT f.path, s.name AS fn, a.name AS attr, a.args, a.line
    FROM attributes a
    JOIN symbols s ON s.id = a.symbol_id
    JOIN files f ON f.id = a.file_id
    LEFT JOIN modules m ON m.id = s.module_id
    WHERE a.name IN ('allow','expect') AND (a.args IS NULL OR a.args = '')
      AND f.is_generated = 0 AND COALESCE(m.name,'') LIKE :mod
    ORDER BY f.path, a.line
    LIMIT :lim"""),
(
    "refcell-across-await",
    "RefCell borrows still alive at an .await (the async interior-mut trap)",
    "ANSWERS .await points where a RefCell/Rc/Cell borrow guard is live: the\n"
    "     borrow must not outlive the await, or the SAME task can deadlock\n"
    "     itself re-entering the borrow. Unlike a mutex this is not cross-\n"
    "     thread -- it is the task's own re-entry.\n"
    "ACT clone the value out of the borrow before the await, or scope the\n"
    "     borrow to end before the yield point.\n"
    "MISLEADS the flag is the guard VALUE text naming RefCell/Rc/Cell: a\n"
    "     borrow of an already-unwrapped value (a &mut from outside) is not\n"
    "     flagged; lexical liveness -- the guard's let is an ancestor block\n"
    "     -- can over-report when the borrow is actually dropped mid-block\n"
    "     (only an explicit drop() is recognised).",
    """SELECT f.path, s.name AS fn, a.line, a.n_guards_live AS guards_live,
        a.guards, a.guard_dropped, s.fan_in
    FROM async_points a
    JOIN symbols s ON s.id = a.symbol_id
    JOIN files f ON f.id = a.file_id
    LEFT JOIN modules m ON m.id = s.module_id
    WHERE a.has_refcell_guard = 1
      AND f.is_generated = 0 AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.fan_in DESC
    LIMIT :lim"""),
(
    "indexing-slicing-surface",
    "v[i] indexing in production code (clippy indexing-slicing)",
    "ANSWERS functions that index collections directly -- v[i] panics on\n"
    "     out-of-range and is the community's #1 gap between linters and\n"
    "     what they can prove. Rows are the review surface for unchecked\n"
    "     indexing.\n"
    "ACT use .get(i) and handle the Option, or prove the bound once; for\n"
    "     hot paths where the bound is invariant, the panic is cheaper than\n"
    "     the branch -- say which in a comment.\n"
    "MISLEADS n_index_expr counts every index expression in the body: a\n"
    "     range check immediately before each index reads the same as an\n"
    "     unchecked one; a const index (`v[0]` on a fixed array) is\n"
    "     counted and is safe; `noUncheckedIndexedAccess`-style proof is a\n"
    "     type-system matter this syntax-level counter cannot see.",
    """SELECT f.path, s.name AS fn, s.n_index_expr AS indexes,
        s.n_member_access AS field_accesses, s.fan_in, s.sloc
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_index_expr > 0 AND f.is_generated = 0 AND f.is_test = 0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.n_index_expr DESC, s.fan_in DESC
    LIMIT :lim"""),
(
    "dropped-futures",
    "let _ = async_call(): the future is dropped without being awaited",
    "ANSWERS async functions that drop a future into `let _`: the call\n"
    "     never runs unless the future is moved elsewhere. In a request\n"
    "     handler this is a silent no-op; in a spawn-er it is the whole\n"
    "     work item vanishing.\n"
    "ACT await the future, or hand it to a spawner; if the fire-and-forget\n"
    "     is deliberate, the dropped future needs a comment and usually a\n"
    "     task wrapper.\n"
    "MISLEADS the capture is `let _ = <call>` in any function -- the query\n"
    "     reads async functions only, and a let-_ of a NON-future value in\n"
    "     an async fn still counts (the value is dropped, which is usually\n"
    "     also a bug); a future bound to a named variable and dropped later\n"
    "     is invisible here.",
    """SELECT f.path, s.name AS fn, s.n_error_swallow AS dropped,
        s.n_await AS awaits, s.fan_in
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_error_swallow > 0 AND s.is_async_fn = 1
      AND f.is_generated = 0 AND f.is_test = 0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.n_error_swallow DESC, s.fan_in DESC
    LIMIT :lim"""),
(
    "lossy-casts",
    "as-casts that narrow or drop precision (clippy cast_sign_loss family)",
    "ANSWERS type_cast_expression sites: `x as u8` truncates, `f64 as f32`\n"
    "     loses precision, `i64 as u64` flips signs -- each is a value-\n"
    "     changing operation the author may not have meant.\n"
    "ACT prefer From/TryFrom (which cannot lose silently) and handle the\n"
    "     error; keep `as` only for raw-bytes and known-safe ranges.\n"
    "MISLEADS n_as_casts counts ALL as-casts, including widening ones that\n"
    "     cannot lose: a body of `u8 as i64` reads the same as `i64 as u8`;\n"
    "     the target width is not parsed, so the rows are the review list\n"
    "     and the cast_sign_loss/cast_possible_truncation families are the\n"
    "     per-cast verdicts this query lacks.",
    """SELECT f.path, s.name AS fn, s.n_as_casts AS casts,
        s.n_checked_arith AS checked, s.fan_in, s.sloc
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_as_casts > 0 AND f.is_generated = 0 AND f.is_test = 0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.n_as_casts DESC, s.fan_in DESC
    LIMIT :lim"""),
(
    "error-swallowing-sites",
    "let _ = fallible() and .map_err(|_| ...) (clippy let_underscore_must_use)",
    "ANSWERS the shapes that discard errors: `let _ = fallible()` drops the\n"
    "     Result, and `.map_err(|_| ...)` throws away the error value while\n"
    "     keeping the type. Both compile and both erase the reason.\n"
    "ACT handle the Result (match, ?, or .ok() with a comment); a map_err\n"
    "     that replaces the error with a constant loses the context -- use\n"
    "     .map_err(|e| format!(...) with the error in the message) or\n"
    "     anyhow's context.\n"
    "MISLEADS the capture is `let _ = <call>` plus map_err-on-underscore\n"
    "     text: `let _ =` on a non-Result value (a drop of a must-use value)\n"
    "     is arguably the same bug and counts; `.ok()` alone in a chain is\n"
    "     not captured; a deliberate `let _ =` in an FFI shim is the\n"
    "     legitimate row.",
    """SELECT f.path, s.name AS fn, s.n_error_swallow AS swallows,
        s.n_question_mark AS question_marks, s.fan_in
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_error_swallow > 0 AND f.is_generated = 0 AND f.is_test = 0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.n_error_swallow DESC, s.fan_in DESC
    LIMIT :lim"""),
(
    "public-api-doc-debt",
    "Public items without a doc comment, by fan-in (rustc missing_docs)",
    "ANSWERS pub functions/methods that say nothing about themselves: the\n"
    "     API surface where the next reader pays the documentation tax.\n"
    "     fan_in ranks the migration order -- the most-called undocumented\n"
    "     symbol pays first.\n"
    "ACT add a /// doc comment; with #![warn(missing_docs)] the compiler\n"
    "     enforces the debt ceiling.\n"
    "MISLEADS has_doc is the doc-comment/leading-comment scan immediately\n"
    "     above the item: a `//!` module doc or a comment one line further\n"
    "     up reads as absent; a pub item reachable only through a re-export\n"
    "     of a private path is not distinguished; private items are\n"
    "     excluded by is_public.",
    """SELECT s.name, s.kind, s.fan_in, s.sloc,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.is_public = 1 AND s.has_doc = 0 AND s.fan_in > 0
      AND s.kind IN ('function','method')
      AND f.is_generated = 0 AND f.is_test = 0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.fan_in DESC, s.sloc DESC
    LIMIT :lim"""),
(
    "manifest-vs-usage",
    "Cargo.toml dependencies never imported (cargo-machete territory)",
    "ANSWERS declared crates no use statement references: dead weight in\n"
    "     build time and the lockfile, or a dependency used only through\n"
    "     a proc macro that names no path.\n"
    "ACT remove the dependency, or use it; a dev-dependency used only by a\n"
    "     build script or a #[test] in another crate shows as unused here\n"
    "     -- check before deleting.\n"
    "MISLEADS matching is by use-declaration head: `use tokio::time` counts\n"
    "     as using tokio; a dependency used only via a macro expansion\n"
    "     (no textual use path) reads as unused; workspace members and\n"
    "     target-specific deps in non-root manifests are included only if\n"
    "     the member Cargo.toml was read.",
    """    WITH used(dn, dv, dd) AS (
        SELECT d.name, d.version, d.is_dev FROM deps d
        JOIN imports i ON i.target = d.name
        UNION
        SELECT d.name, d.version, d.is_dev FROM deps d
        JOIN imports i ON i.target >= d.name || '::'
                       AND i.target < d.name || '::' || X'FF')
    SELECT d.name, d.version, d.is_dev, 0 AS used
    FROM deps d
    WHERE NOT EXISTS (SELECT 1 FROM used u
                      WHERE u.dn = d.name AND u.dv = d.version
                        AND u.dd = d.is_dev)
    ORDER BY d.is_dev, d.name
    LIMIT :lim""")
]

RustAnalyzer.METRICS = [
(
    "graph-blindspots",
    "Read this first: where the call graph cannot see",
    "ANSWERS how much of every other answer here is guesswork. Rust's blind\n"
    "     spot is trait-object dispatch: `Box<dyn T>` calling `.render()` has\n"
    "     no syntactic target, and neither does anything a macro expands to.\n"
    "ACT external calls (std, core, crates.io) are out of scope BY DESIGN and\n"
    "     are not counted as blindness. Read pct_blind next to dyn_sites and\n"
    "     macro_calls: a module high in both is one this tool is guessing at.\n"
    "MISLEADS a resolved edge can still be wrong. A method call resolves by\n"
    "     name within the enclosing impl and then by unique name across the\n"
    "     tree, so two types with a method of the same name make one of the\n"
    "     two edges arbitrary. Macro bodies are counted as ONE call site each\n"
    "     however many calls they expand to, so macro-heavy crates look far\n"
    "     less connected than they are.",
    """SELECT m.name AS module_, COUNT(DISTINCT s.id) AS fns,
        COALESCE(SUM(s.n_calls),0) AS calls,
        COALESCE(SUM(s.n_external_calls),0) AS external,
        COALESCE(SUM(s.n_unresolved_calls),0) AS unresolved,
        COALESCE(SUM(s.n_box_dyn + s.n_dyn_params),0) AS dyn_sites,
        COALESCE(SUM(s.n_macro_invocations),0) AS macro_calls,
        COALESCE(SUM(s.n_impl_trait),0) AS impl_trait,
        CAST(100.0*SUM(s.n_unresolved_calls)/NULLIF(SUM(s.n_calls),0) AS INT)
            AS pct_blind
    FROM symbols s JOIN modules m ON m.id=s.module_id
    WHERE s.kind IN ('function','method','closure') AND m.name LIKE :mod
    GROUP BY m.id HAVING calls > 0
    ORDER BY unresolved DESC, dyn_sites DESC LIMIT :lim"""),
(
    "clone-churn-per-iteration",
    "Clone and allocation inside loops, weighted by depth and fan-in",
    "ANSWERS where a Rust program allocates for no reason: a `.clone()` to\n"
    "     satisfy the borrow checker, a `collect()` into a temporary, a\n"
    "     `format!` per row. The weight is depth times callers, because a\n"
    "     clone in a doubly-nested loop in a leaf forty things call is a\n"
    "     different object from the same line in a one-shot setup function.\n"
    "ACT borrow instead of cloning; `Cow` where the clone is conditional;\n"
    "     hoist the allocation out and reuse the buffer; `with_capacity` when\n"
    "     the size is known.\n"
    "MISLEADS none of this is confirmed without a profile. `clone()` on a Copy\n"
    "     type is free and is counted here; so is `Arc::clone`, which is a\n"
    "     refcount bump, not a deep copy -- and this cannot tell them apart\n"
    "     because that needs types. Trip count is invisible: a loop bounded at\n"
    "     3 does not care.",
    """SELECT s.name, s.impl_type AS on_type,
        s.n_clone_in_loop AS clones_in_loop, s.alloc_in_loop AS allocs_in_loop,
        s.n_clone AS clones_total, s.n_to_owned AS to_owned,
        s.n_collect AS collects, s.n_format_macro AS formats,
        s.n_with_capacity AS with_capacity, s.n_iter_adapters AS adapters,
        s.max_loop_depth AS depth, s.fan_in,
        (s.n_clone_in_loop*4 + s.alloc_in_loop*3 + s.n_format_macro*2
         + s.n_collect*2) * (1 + s.max_loop_depth) * MAX(s.fan_in,1)
            AS churn,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.max_loop_depth > 0
      AND (s.n_clone_in_loop + s.alloc_in_loop) > 0
      AND f.is_test=0 AND f.is_generated=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY churn DESC LIMIT :lim"""),
(
    "dyn-with-one-impl",
    "Trait objects for traits that have exactly one implementation",
    "ANSWERS the free devirtualisation: `Box<dyn Trait>` costs a vtable\n"
    "     indirection, a heap allocation and an inlining barrier, and if the\n"
    "     trait has one implementor the abstraction buys nothing back.\n"
    "ACT swap the concrete type in, or make the caller generic over the trait\n"
    "     so the call monomorphises -- UNLESS the trait exists for a test\n"
    "     double or a plugin boundary, which are the two good reasons.\n"
    "MISLEADS impl counting is syntactic: an implementor in another crate, one\n"
    "     produced by a blanket `impl<T> Trait for T`, or one generated by a\n"
    "     derive macro is not seen, so a count of 1 means 'look', never\n"
    "     'delete'. is_generic flags blanket impls, which make the count\n"
    "     meaningless on their own.",
    """WITH RECURSIVE dt(sym, pos, rest) AS (
        SELECT symbol_id, pos, type FROM params WHERE instr(type, 'dyn ') > 0
        UNION ALL
        SELECT sym, pos, substr(rest, instr(rest, 'dyn ') + 4)
        FROM dt WHERE instr(rest, 'dyn ') > 0),
    dw(sym, pos, word) AS MATERIALIZED (
        SELECT sym, pos, substr(a, 1, length(a) - length(ltrim(a,
                'abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_')))
        FROM (SELECT sym, pos, substr(rest, instr(rest, 'dyn ') + 4) AS a FROM dt)),
    st(sk, rest) AS (
        SELECT id, signature FROM symbols WHERE instr(signature, 'dyn ') > 0
        UNION ALL
        SELECT sk, substr(rest, instr(rest, 'dyn ') + 4)
        FROM st WHERE instr(rest, 'dyn ') > 0),
    sw(sk, word) AS MATERIALIZED (
        SELECT sk, substr(a, 1, length(a) - length(ltrim(a,
                'abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_')))
        FROM (SELECT sk, substr(rest, instr(rest, 'dyn ') + 4) AS a FROM st))
    SELECT t.name AS trait_, t.n_required AS required_methods,
        t.n_provided AS default_methods, t.is_public AS pub_,
        t.has_assoc_type AS assoc_type,
        COUNT(DISTINCT i.id) AS impls_found,
        GROUP_CONCAT(DISTINCT i.type_name) AS implementors,
        MAX(i.is_generic) AS blanket_impl,
        (SELECT COUNT(*) FROM
            (SELECT DISTINCT sym, pos FROM dw WHERE word = t.name))
            AS dyn_params,
        (SELECT COALESCE(SUM(s2.n_box_dyn),0) FROM symbols s2
         WHERE s2.id IN (SELECT sk FROM sw WHERE word = t.name))
            AS box_dyn_sites,
        f.path || ':' || s.line_start AS at
    FROM traits t
    JOIN symbols s ON s.id=t.symbol_id
    JOIN files f ON f.id=t.file_id
    LEFT JOIN impls i ON i.trait_name = t.name
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE f.is_test=0 AND COALESCE(m.name,'') LIKE :mod
    GROUP BY t.symbol_id
    HAVING impls_found <= 1 AND (dyn_params > 0 OR box_dyn_sites > 0)
    ORDER BY dyn_params DESC, box_dyn_sites DESC LIMIT :lim"""),
(
    "mono-blast-radius",
    "Generic functions whose body gets copied once per instantiation",
    "ANSWERS what makes a Rust build slow and a binary large: rustc emits a\n"
    "     fresh copy of every generic function per distinct type argument, so\n"
    "     body_bytes times instantiations is the code the linker has to chew\n"
    "     through and the icache has to hold.\n"
    "ACT the standard fix is an inner non-generic function taking `&dyn` or a\n"
    "     concrete type, with a thin generic wrapper -- the generic surface\n"
    "     stays, the duplicated body does not. Sort by est_bloat.\n"
    "MISLEADS instantiations is a PROXY: the number of distinct MODULES that\n"
    "     call this function. rustc instantiates per distinct type-argument\n"
    "     tuple, which is a type-checking result no syntactic parser can\n"
    "     enumerate -- one module calling with six types counts as 1, and six\n"
    "     modules calling with the same type counts as 6. Both directions are\n"
    "     wrong; only the ranking is worth anything. Confirm with\n"
    "     `cargo llvm-lines` before doing surgery.",
    """SELECT s.name, s.impl_type AS on_type,
        s.n_generic_params AS type_params, s.n_trait_bounds AS bounds,
        s.n_where_predicates AS where_preds, s.n_hrtb AS hrtb,
        s.n_turbofish AS turbofish_calls,
        s.n_mono_instantiations AS instantiations,
        s.body_bytes, s.sloc, s.fan_in, s.n_inline_attrs AS inline_attr,
        s.body_bytes * MAX(s.n_mono_instantiations,1) AS est_bloat,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_generic_params > 0 AND s.kind IN ('function','method')
      AND f.is_test=0 AND f.is_generated=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY est_bloat DESC LIMIT :lim"""),
(
    "cfg-feature-nobody-builds",
    "#[cfg(feature)] naming a feature Cargo.toml never declares",
    "ANSWERS which conditional code no build in this workspace can compile.\n"
    "     A cfg on an undeclared feature is permanently false: it type-checks\n"
    "     against nothing, no test touches it, and it rots silently until\n"
    "     someone enables the feature and finds three years of drift.\n"
    "ACT declare the feature in [features], or delete the block. Since Rust\n"
    "     1.80 `cargo check` warns about unexpected cfgs -- this finds the\n"
    "     same thing across a workspace and tells you how much code is behind\n"
    "     each one.\n"
    "MISLEADS the root manifest and every manifest ONE level below it are read,\n"
    "     which covers the usual workspace layout but not a nested one --\n"
    "     `crates/foo/bar/Cargo.toml` is invisible and its features will all\n"
    "     look undeclared. Features come from the manifest TEXT, not from\n"
    "     `cargo metadata`, so anything a build script adds is missed, and a\n"
    "     feature enabled only by a dependency's own `[features]` table is not\n"
    "     followed. Check the row against the manifest before deleting code.",
    """SELECT c.feature, COUNT(*) AS cfg_sites,
        COUNT(DISTINCT c.file_id) AS files_,
        (SELECT COUNT(*) FROM crate_features cf
         WHERE cf.name = c.feature) AS declared_in_manifest,
        SUM(c.is_test) AS test_gated,
        SUM(c.is_attr_only) AS cfg_attr_only,
        COUNT(DISTINCT s.id) AS symbols_behind_it,
        COALESCE(SUM(s.sloc),0) AS sloc_behind_it,
        GROUP_CONCAT(DISTINCT f.path) AS in_files
    FROM cfg_blocks c
    JOIN files f ON f.id=c.file_id
    LEFT JOIN symbols s ON s.id=c.symbol_id
    LEFT JOIN modules m ON m.id=f.module_id
    WHERE c.feature <> '' AND COALESCE(m.name,'') LIKE :mod
    GROUP BY c.feature
    HAVING declared_in_manifest = 0
    ORDER BY sloc_behind_it DESC, cfg_sites DESC LIMIT :lim"""),
(
    "alloc-churn-collect-and-format",
    "collect() and format!() where an iterator or a writer would do",
    "ANSWERS where the code allocates a whole collection or a whole String\n"
    "     only to consume it once. `collect::<Vec<_>>()` in the middle of a\n"
    "     chain materialises the entire sequence; `format!` in a loop\n"
    "     allocates per iteration.\n"
    "ACT drop the intermediate collect and keep the iterator lazy. For\n"
    "     strings, write into one reused String with `write!` or push_str,\n"
    "     and reserve with_capacity when the size is known.\n"
    "MISLEADS a collect that is genuinely needed -- to sort, to borrow twice,\n"
    "     to escape a lifetime -- is not waste, and this cannot tell those\n"
    "     apart. Read `with_capacity` as evidence someone already thought.",
    """SELECT s.name, s.impl_type AS impl_, s.n_collect AS collects,
        s.n_format_macro AS formats, s.n_iter_adapters AS adapters,
        s.n_with_capacity AS with_capacity, s.n_to_owned AS to_owned,
        s.max_loop_depth AS depth, s.fan_in,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE (s.n_collect > 0 OR s.n_format_macro > 0) AND s.max_loop_depth > 0
      AND f.is_test=0 AND COALESCE(m.name,'') LIKE :mod
    ORDER BY (s.n_collect + s.n_format_macro) * (1 + s.max_loop_depth)
             * (1 + s.fan_in) DESC LIMIT :lim"""),
(
    "dynamic-dispatch-cost",
    "Box<dyn Trait> and &dyn parameters on the paths that run most",
    "ANSWERS where the code pays for dynamic dispatch. Every call through a\n"
    "     trait object is an indirect jump the compiler cannot inline, and it\n"
    "     blocks the optimisations that would have followed inlining.\n"
    "ACT if the set of implementations is closed, an enum with a match is\n"
    "     both faster and easier to exhaustively handle. If it is open but\n"
    "     small, generics monomorphise it away -- at the cost of code size,\n"
    "     which `mono-blast-radius` measures.\n"
    "MISLEADS dynamic dispatch is the correct choice for plugin boundaries\n"
    "     and for keeping compile times sane, and a Box<dyn Error> in a cold\n"
    "     error path costs nothing. Rank by fan_in, not by count.",
    """SELECT s.name, s.impl_type AS impl_, s.n_box_dyn AS box_dyn,
        s.n_dyn_params AS dyn_params, s.n_impl_trait AS impl_trait,
        s.fan_in, s.max_loop_depth AS depth, s.call_in_loop AS calls_in_loop,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE (s.n_box_dyn > 0 OR s.n_dyn_params > 0) AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY (s.n_box_dyn + s.n_dyn_params) * (1 + s.fan_in)
             * (1 + s.call_in_loop) DESC LIMIT :lim"""),
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
    "box-dyn-overuse",
    "Box<dyn> where generics could work (clippy/box_dyn)",
    "ANSWERS where Box<dyn Trait> is used, which adds a heap allocation and\n"
    "     vtable indirection. A generic <T: Trait> is monomorphized and has\n"
    "     neither.\n"
    "ACT use generics when the number of concrete types is small and known.\n"
    "MISLEADS Box<dyn> for heterogeneous collections or plugin systems is correct.\n"
    "     The graph counts the usage but not the design context.",
    """SELECT s.name, s.n_box_dyn AS box_dyns,
        s.n_dyn_params AS dyn_params,
        s.n_impl_trait AS impl_traits,
        s.fan_in, s.cyclomatic AS cyclo,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_box_dyn > 2 AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.n_box_dyn DESC, s.fan_in DESC LIMIT :lim"""),
(
    "deep-nesting",
    "Functions with excessive nesting depth (clippy/cognitive_complexity)",
    "ANSWERS where a function has max_nesting > 4.\n"
    "ACT extract nested blocks into named helper functions; use early returns.\n"
    "MISLEADS a match with many arms is nesting=1 regardless of arm count.",
    """SELECT s.name, s.max_nesting AS nesting,
        s.cyclomatic AS cyclo, s.cognitive AS cognitive,
        s.n_match_arms AS match_arms,
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
    "Functions with too many parameters (clippy/too_many_arguments)",
    "ANSWERS where a function has more than 7 parameters.\n"
    "ACT use a struct parameter, or split the function.\n"
    "MISLEADS a function with many generic params counts them too.",
    """SELECT s.name, s.n_params, s.n_generic_params,
        s.sloc, s.cyclomatic AS cyclo, s.fan_in,
        f.path || ':' || s.line_start AS at
    FROM symbols s JOIN files f ON f.id=s.file_id
    LEFT JOIN modules m ON m.id=s.module_id
    WHERE s.n_params > 7 AND s.kind IN ('function','method')
      AND f.is_test=0
      AND COALESCE(m.name,'') LIKE :mod
    ORDER BY s.n_params DESC, s.fan_in DESC LIMIT :lim"""),
(
    "scattered-concerns",
    "A function called from many different modules (shotgun surgery)",
    "ANSWERS which functions are called from many distinct modules.\n"
    "ACT consider splitting or stabilizing the contract.\n"
    "MISLEADS a core trait method like Default::default is called from everywhere.",
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



ANALYZER = RustAnalyzer()


if __name__ == "__main__":
    try:
        sys.exit(main(ANALYZER))
    except KeyboardInterrupt:
        print("\ninterrupted", file=sys.stderr)
        sys.exit(130)
