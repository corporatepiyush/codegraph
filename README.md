# codegraph

Parse a source tree into an in-memory SQLite call graph, then ask it hard
questions — the kind that only make sense *across* the codebase, not inside one
file.

```bash
python3 codegraph_javascript.py /path/to/repo --report   # what does it know?
python3 codegraph_javascript.py /path/to/repo --list     # what can it answer?
python3 codegraph_javascript.py /path/to/repo 7 11       # ask it those
python3 codegraph_javascript.py /path/to/repo 7 --csv    # machine-readable
```

One self-contained Python script per language. No server, no daemon, no index
to keep warm. Point it at a repo and it re-reads and re-parses everything,
builds the whole graph in `:memory:`, answers, and exits.

---

## What this is, in one paragraph

A linter reads one file and reports on that file. This builds the **call graph**
and answers questions that span it:

- Which blocking calls can an async request handler reach, four frames down?
- Which `unsafe` blocks can a downstream crate trigger through a safe API?
- Which goroutines spawn under an HTTP handler with no context and no joiner?
- Which mutable default argument is shared by forty callers?
- Which interface has exactly one implementation — an abstraction over nothing?

There is no separate `SELECT` grammar to learn. The whole tool is SQL over a
per-language schema, and every question ships as a named, documented query. The
SQL *is* the product: each query encodes the reasoning, so a consumer — human
or agent — gets an actionable row instead of having to re-derive the analysis.

---

## Quickstart (no clone needed)

Each analyzer is standalone. Grab only the language you need:

```bash
curl -O https://raw.githubusercontent.com/corporatepiyush/codegraph/master/codegraph_javascript.py
python3 codegraph_javascript.py --install-deps       # installs its grammar
python3 codegraph_javascript.py /path/to/repo --report
```

Swap the filename for `codegraph_{c,python,go,rust,java,typescript,php,ruby}.py`.
Nothing else to clone — no package, no config file. `codegraph_python.py`
(stdlib `ast`) and `codegraph_c.py` (brace scanning) need no grammar and always
run.

**Requires CPython 3.14+** and its bundled SQLite 3.37+ (the schema uses
`STRICT` tables). The floor is enforced at startup rather than left to produce a
thinner graph that looks complete.

---

## The two catalogues: act on these, weigh those

Every analyzer ships **two** query lists, because a bug-fixing loop and a
maintainability review want different things.

**`QUERIES` — the "act on it" list (245 across nine languages).**
Rows are *defects or defect risks*: an error swallowed, a lock held across an
I/O call, an alloc without a free, an unbounded regex reaching a handler. These
are what a coding agent should act on.

```
$ python3 codegraph_go.py /repo --list
 1. goroutine-leak-frontier     Goroutines with no context, no WaitGroup and no errgroup
 2. ctx-propagation-break       Where a live context stops being passed down
 ...
```

**`METRICS` — the "weigh it" list (152).** Rows are design or triage facts:
cyclomatic complexity, coupling, footprint. A human decides what they mean;
an agent should not auto-fix them.

```
$ python3 codegraph_go.py /repo --metrics --list
 1. graph-blindspots            Read this first: where the call graph cannot see
 2. risk-ranked                 Review order: if you can only read N functions this week...
```

`--metrics` flips the default list for `--list`, `--csv`, and `--json`. The
plain command runs `QUERIES` only, so a bug-fixing agent sees signal, not noise.

### The notes contract on every query

Each query carries exactly three lines, and they mean what they say:

```
ANSWERS  the question this settles
ACT      what to do with a row
MISLEADS how this metric lies
```

`MISLEADS` is the one that earns its place. A ranking without it gets read as a
finding, and someone spends a day on the top row of a list that was only ever a
heuristic. **If you act on a row, read its `MISLEADS` first** — it names the
dominant way that row can be wrong.

---

## Machine contract (for tools and agents)

The command line is stable and parseable. Rely on these, not on scraping prose.

**Exit codes**
| code | meaning |
|---|---|
| `0` | the run completed; rows may be zero (that is "no finding", not an error) |
| `2` | a query could not run (bad number, a `--sql` error, or a real SQL failure) |

A query that returns nothing is printed as `(no rows)` and is **not** a failure.
An empty result is the tool honestly saying "nothing here matches"; distinguish
it from an error via the exit code, which stays `0`.

**Machine output**
```bash
codegraph_go.py /repo 3 --json     # array of objects, one per row
codegraph_go.py /repo 3 --csv      # header row of column names, then rows
codegraph_go.py /repo --sql "SELECT ..."   # ad-hoc against the graph
codegraph_go.py /repo --save out.db        # persist the graph, e.g. to run many queries
```
`--csv` and `--json` emit *only* the payload on stdout (no progress), and imply
`--quiet`. Every query is executed with bound `:mod` (module filter) and `:lim`
(row limit) parameters.

**The location column.** Every defect-query returns a column named `at`, format
`<path>:<line>`, pointing at the offender. Code that opens a `Closer` but never
closes it, an `unsafe` block with no `SAFETY:` comment, a leaked `ThreadLocal` —
each row carries the exact file and line to open. `--csv`/`--json` preserve it
verbatim, so an agent can jump straight to `path:line` and verify.

**Ad-hoc SQL.** Every query is just SQL over a documented schema. `--schema`
dumps the full DDL so you can write your own against the same tables
(`symbols`, `edges`, `callsites`, `imports`, `hazards`, `meta`, plus per-language
tables). Combine queries by understanding the tables, not by guessing.

**`--save` for repeated queries.** A fresh parse per run is the default because
a graph file goes stale the moment code changes — and a stale graph is worse
than none. When you need many queries over the same snapshot, `--save graph.db`
writes the graph and refuses to overwrite without `--force`.

---

## Filters

- `--module PATTERN` — restrict to a module (a `LIKE` on the module name)
- `--limit N` — rows per query (`-1` is every row)
- `--no-tests` — skip test files
- `--include-generated` / `--include-vendored` — include what is otherwise skippe
  generated and vendored code is excluded by default, because a 40k-line
  generated parser table otherwise tops every complexity chart

Test detection is per language, not one shared regex. A shared one applied
Ruby's `_spec.` to Go and flagged Terraform's production `decoder_spec.go`,
while missing all 221 files in type-fest's `test-d/`.

---

## Honesty about what it cannot see

Static reading of a dynamic language is guesswork at the edges, so the tool
measures its own blindness and reports it before anything else:

- `unresolved_calls` — a call we saw but could not point at a definition
- `n_external_calls` — calls that leave the tree by design (stdlib, packages),
  kept separate from blindness so the blind-share number stays useful
- `n_dynamic_calls` — dispatch computed at runtime
- `files.n_parse_errors` — what the parser could not read
- `meta.parse_mode` — which parser actually ran, recorded rather than assumed

`--report` prints a **HOW MUCH OF THIS TO TRUST** section, and `graph-blindspots`
(likely in `METRICS`) is the one to read first.

---

## Languages

| Script | Target | Parser |
|---|---|---|
| `codegraph_python.py` | Python 3.15 | stdlib `ast` (exact), tree-sitter fallback for newer-than-host syntax |
| `codegraph_c.py` | C11/C17 + GNU/Clang extensions | regex + brace matching |
| `codegraph_java.py` | Java 25 (LTS) | tree-sitter |
| `codegraph_rust.py` | Rust 1.97 / edition 2024 | tree-sitter |
| `codegraph_go.py` | Go 1.26 | tree-sitter |
| `codegraph_javascript.py` | ES2026 | tree-sitter |
| `codegraph_typescript.py` | TypeScript 7 | tree-sitter |
| `codegraph_php.py` | PHP 8.5 | tree-sitter |
| `codegraph_ruby.py` | Ruby 4.0 | tree-sitter |

**Query counts (this revision):**

| Script | QUERIES (act) | METRICS (weigh) | total |
|---|---|---|---|
| `codegraph_python.py` | 32 | 23 | 55 |
| `codegraph_go.py` | 33 | 17 | 50 |
| `codegraph_c.py` | 26 | 26 | 52 |
| `codegraph_java.py` | 24 | 17 | 41 |
| `codegraph_typescript.py` | 24 | 19 | 43 |
| `codegraph_ruby.py` | 31 | 9 | 40 |
| `codegraph_rust.py` | 29 | 14 | 43 |
| `codegraph_javascript.py` | 20 | 14 | 34 |
| `codegraph_php.py` | 26 | 13 | 39 |
| **All** | **245** | **152** | **397** |

(Single source of truth for these numbers: run `codegraph_<lang>.py --list` and
`--metrics --list`. If the table disagrees with the scripts, the scripts win.)

---

## Correctness, and how it is checked

Three classes of bug have been found and fixed here, none of which a test that
merely runs the queries would catch, because each produced confident, plausible,
wrong numbers for a long time.

**Aggregates inflated by fan-out joins.** A `GROUP BY` across two one-to-many
joins multiplies every `SUM` by the other side's row count. One query reported
23,858 thread starters where the truth was 158; another claimed more primitive
fields than the type had fields at all. `COUNT(DISTINCT)`, `MIN` and `MAX`
survive duplication, so each query kept correct columns beside wrong ones, and
`HAVING` survives a positive multiplier — so the right rows came back carrying
wrong numbers, while `ORDER BY` silently ranked by the bug.

**Names matched with `LIKE`.** SQLite's `LIKE` is case-insensitive for ASCII
while `=` and `instr()` are not, and a trailing-wildcard match has no word
boundary. In Go, where case *is* the export rule, an unexported `groupversion`
matched every `schema.GroupVersion` in the tree — 84 percent of that query's
findings were case collisions. Another counted interface `Reader` as used
wherever `MyReader` appeared.

**A node type listed alongside its own child.** Go spells every range loop as a
`for_statement` containing a `range_clause`, and both were in `LOOP_NODES`, so
one loop counted twice. Range is the dominant loop form in Go, so this inflated
the whole language: 47 percent of reported loops did not exist, and cyclomatic
and cognitive complexity — the primary ranking metrics — were 9.5 and 12
percent too high.

What catches these is not a bigger test suite but an **invariant per query**: a
type cannot have more primitive fields than it has fields; a symbol cannot
contain more call sites than its file does. Violations are counted before and
after a fix, because "looks better" is not a result.

---

## One file per language, and nothing else

There are no shared modules, no package, no imports between these files. Each
`codegraph_<lang>.py` contains everything it needs — the schema, the parser
wiring, the metrics, the hazard catalogue, the queries and the CLI. Copy one
file onto a machine and it runs; port it and it still runs.

That also means each analyzer is free to disagree with the others. **The schema
is per language, not universal**, because the languages are not universal:

- Go carries `goroutines`, `defers`, `channels`, `interfaces`, and columns like
  `n_ctx_background` and `n_err_shadowed`.
- Python carries `classes`, `handlers`, `dynamic_sites`, `comprehensions`, and
  columns like `n_mutable_default` and `n_bare_except`.
- Rust carries `unsafe_blocks`, `impls`, `traits`, `async_points`, `cfg_blocks`.

The tables that *do* recur — `files`, `symbols`, `edges`, `callsites`,
`unresolved_calls`, `imports`, `hazards`, `params`, `fields`, `literals`,
`markers`, `meta` — recur because the questions genuinely are the same, not
because a base class forced them to be. Where a language needs a column bent to
a different meaning, it bends it. Hazard categories are declared per language
and become `n_<category>` columns, so `n_goroutine` exists in Go and
`n_deserialize` exists in Python, and neither carries the other's dead weight.
`--schema` dumps whatever that particular file defines.

---

## Dependencies

Every script declares exactly what it needs and why:

```bash
python3 codegraph_javascript.py --deps          # show them
python3 codegraph_javascript.py --install-deps  # install the missing ones
```

Nothing is installed behind your back, and nothing is faked. A grammar-backed
analyzer **refuses to run** without its grammar and prints the exact install
command. There is no regex fallback, because a graph with zero edges is
indistinguishable from a repository with nothing in it — and an earlier version
of this tool did exactly that, reporting "0 of 0 call sites unresolved" over an
empty database.

---

## Licence

MIT
