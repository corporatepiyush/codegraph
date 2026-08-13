# codegraph

Parse a source tree into an in-memory SQLite call graph, then ask it hard
questions — the kind that only make sense *across* the codebase, not inside one
file.

```bash
python3 codegraph_javascript.py /path/to/repo --report   # what does it know?
python3 codegraph_javascript.py /path/to/repo --list     # what can it answer?
python3 codegraph_javascript.py /path/to/repo 7 11       # ask it those
python3 codegraph_javascript.py /path/to/repo --csv 7    # machine-readable
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

Each analyzer is standalone. Grab only the language you need.

**Download once, then run:**
```bash
curl -O https://raw.githubusercontent.com/corporatepiyush/codegraph/master/codegraph_javascript.py
python3 codegraph_javascript.py --install-deps       # installs its grammar
python3 codegraph_javascript.py /path/to/repo --report
```

**Or fetch and execute in one pipe** — no file to manage, the raw GitHub copy is
the script:
```bash
# one-off: analyze a repo without saving anything to disk
curl -sL https://raw.githubusercontent.com/corporatepiyush/codegraph/master/codegraph_javascript.py \
  | python3 - /path/to/repo --report

# install that language's grammar into the running interpreter, then keep going
curl -sL https://raw.githubusercontent.com/corporatepiyush/codegraph/master/codegraph_c.py \
  | python3 - --install-deps
```

The pipe form brings two things to know:

- **`--install-deps` inside a pipe** installs into the interpreter you are
  piping *into* (`python3` from your PATH), exactly as if you had run the file.
  It does not need the file on disk. Grammar-free analyzers (`codegraph_c.py`,
  `codegraph_python.py`) skip the step entirely.
- **Re-running repeatedly from a pipe re-downloads.** For many queries over one
  snapshot, pipe once is fine, but `--save out.db` is the better pattern — and
  if you are going to `--save` anyway, `curl -O` once is the honest choice
  because the next run needs no network at all.

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

**`QUERIES` — the "act on it" list (456 across nine languages).**
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
codegraph_go.py /repo --json 3     # array of objects, one per row
codegraph_go.py /repo --csv 3      # header row of column names, then rows
codegraph_go.py /repo --sql "SELECT ..."   # ad-hoc against the graph
codegraph_go.py /repo --save out.db        # persist the graph for your own tooling
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

## Typical workflows

The whole tool is one command, so the "workflows" are really arguments, but the
shape of a good session is worth spelling out.

**A bug-fixing agent, one shot.** Run the act-list, filter to what it can own,
and verify each row's `MISLEADS` before acting:

```bash
python3 codegraph_go.py /repo --list                 # see what's on the table
python3 codegraph_go.py /repo --json 1               # one query, as JSON
python3 codegraph_go.py /repo 1 3 7                  # a few queries, plain rows
python3 codegraph_go.py /repo --module pkg/util       # one package
python3 codegraph_go.py /repo --no-tests             # prod code only
```

Rows carry an `at` column of `path:line`. An agent reads `at`, opens the file,
applies the fix, and re-runs the same number to confirm the row is gone.

**A human review.** Start with `--metrics --list`, read `graph-blindspots`,
then read the whole weighing list — it prints every metric with its top rows:

```bash
python3 codegraph_java.py /repo --metrics --list   # names + one-line meaning
python3 codegraph_java.py /repo --metrics          # every metric, top rows
python3 codegraph_java.py /repo --metrics --csv 1  # one metric, as CSV
```

**One snapshot, many questions.** Every run re-parses, because a graph file goes
stale the moment code changes — and `root` must be a directory, not a saved
file. To ask many questions without re-parsing per question, save once and then
query the saved copy from your own tooling (it is ordinary SQLite) while the
analyzer keeps re-parsing per run:

```bash
python3 codegraph_rust.py /repo --save snapshot.db --force
python3 codegraph_rust.py /repo --csv 7        # one query, as CSV
sqlite3 snapshot.db "SELECT name, fan_in FROM symbols ORDER BY fan_in DESC LIMIT 10"
```

The saved file is ordinary SQLite — point any tool at it. It is a snapshot for
offline or repeated analysis in *your* tooling, not a way to make the analyzer
skip parsing.

**An ad-hoc question the canned list does not ask.** The graph is queryable
directly. `--schema` tells you the tables; `--sql` runs anything against them:

```bash
python3 codegraph_python.py /repo --schema
python3 codegraph_python.py /repo --sql \
  "SELECT name, fan_in FROM symbols ORDER BY fan_in DESC LIMIT 15"
```

## Performance

Every run re-reads and re-parses the whole tree into an in-memory graph, then
answers. There is no warm index to keep and no server — the cost is paid in
full each time, and it is dominated by parsing, not by asking questions.

Measured on this machine (CPython 3.14, one run each):

| corpus | language | wall |
|---|---|---|
| flask (small) | python | ~0.8 s |
| redis/src | c (regex) | ~7 s |
| playwright | typescript | ~15 s |

A large monorepo (e.g. the Kubernetes tree) is around a minute. The
practical trade-off is deliberate: correctness and simplicity beat a fast stale
index. When the same snapshot is queried repeatedly, `--save` removes the
re-parse cost from every question after the first for that revision.

Parsing is single-process and, for grammar-backed languages, tree-sitter holds
the GIL for the whole of `parse()` — measured at 3.8x wall time for 4x work
with threads, so it is not parallelised. There is no network and no external
service to warm; the cost is the parse itself, paid once per run.

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
|---|---|---|---|---|
| `codegraph_python.py` | 57 | 23 | 80 |
| `codegraph_go.py` | 59 | 17 | 76 |
| `codegraph_c.py` | 43 | 26 | 69 |
| `codegraph_java.py` | 50 | 17 | 67 |
| `codegraph_typescript.py` | 51 | 19 | 70 |
| `codegraph_ruby.py` | 55 | 9 | 64 |
| `codegraph_rust.py` | 51 | 14 | 65 |
| `codegraph_javascript.py` | 41 | 14 | 55 |
| `codegraph_php.py` | 49 | 13 | 62 |
| **All** | **456** | **152** | **608** |

(Single source of truth for these numbers: run `codegraph_<lang>.py --list` and
`--metrics --list`. If the table disagrees with the scripts, the scripts win.)

---

## What each language answers

The queries are listed in full by `--list` / `--metrics --list`; here is the
shape of each catalogue, by language. Every query name below is real — it
appears in that language's `--list` output, where each entry carries its
number for `python3 codegraph_<lang>.py /repo <number>`.

**Every language ships the same recurring core**, so it appears once here and
not under each heading:

- in **all nine** — `graph-blindspots`, `parse-coverage`, `dead-code`,
  `hot-multipliers`, `risk-ranked`
- in **eight of nine** (missing only from Java) — `scattered-concerns`
- in **eight of nine** (all but Go) — some `deep-nesting` variant: TypeScript
  and Python name it `deep-nesting-excessive`, Python also carries the plain
  name; and a `too-many-params` sibling exists in eight (Go alone uses
  `too-many-return-paths` and `unused-params`, Python prefers
  `too-many-locals`).
- in **some** — `markers` (Go, TypeScript, Python), `god-functions`
  (Go, JavaScript, TypeScript, Python), `module-coupling`
  (Go, TypeScript, Python, C), `god-module` (Go only)

### Go (59 act, 17 weigh)

Concurrency is the first citizen — goroutines, locks, contexts:

- **Goroutine lifecycle** — `goroutine-leak-frontier`, `goroutine-under-handler`,
  `package-state-concurrent`, `concurrency-hotspots`, `select-without-default`,
  `channel-topology`
- **Defer discipline** — `defer-lifetime`, `defer-in-loop`
- **Context discipline** — `ctx-propagation-break`, `context-not-propagated`,
  `context-severed-by-caller`, `nil-context-deep`, `context-built-in-loop`,
  `http-request-no-context`
- **Error handling** — `unchecked-errors`, `error-handling-drift`,
  `error-not-wrapped`, `error-fan-out`, `nil-error-after-check`,
  `deferred-close-unchecked`, `resource-close-cross-layer`
- **Locking** — `lock-copied-by-value`, `lock-over-crosspkg-call`,
  `lock-release-imbalance-reachable`
- **Perf / allocation** — `n-plus-one`, `slice-growth-and-copies`,
  `string-concat-in-loop`, `time-after-in-loop`, `readall-in-loop`,
  `file-read-surface`, `loopvar-rebind-dead`, `heap-pressure-loops` (M),
  `range-value-copy` (M)
- **Type & error discipline** — `unchecked-type-assertions`,
  `log-fatal-in-handler`, `env-read-in-handler`, `wrapper-function` (M),
  `naked-return-complex` (M), `too-many-return-paths` (M), `unused-params` (M)
- **Security** — `unsafe-cgo-frontier`, `unsafe-pointer-arith`,
  `weak-random-security`, `weak-crypto-security`, `insecure-tls-config`,
  `command-exec-surface`, `sql-injection-build`, `reflect-call-surface`,
  `hardcoded-secret-candidates`, plus the OWASP input-surface family
  (`open-redirect-surface`, `path-traversal-surface`,
  `unauthenticated-input-surface`, `mass-assignment-surface`,
  `untrusted-deserialization`, `zip-slip-surface`, `sensitive-log-surface`,
  `deprecated-stdlib-calls`)
- **Architecture** — `single-impl-interface` (M), `iface-satisfaction-breadth`,
  `abstraction-reach`, `receiver-pointer-mix`, `internal-package-leak`,
  `module-dependency-depth`, `import-cycle`, `module-coupling` (M),
  `god-functions` (M), `god-module` (M), `hot-multipliers` (M),
  `scattered-concerns` (M), `deep-call-chain` (M), `unused-exported`,
  `dead-code`, `risk-ranked` (M)

### Java (50 act, 17 weigh)

Concurrency under the JVM, resource discipline, and framework/type design:

- **Concurrency & executors** — `vt-pinning-frontier`,
  `threadlocal-leak-on-pooled`, `shared-mutable-statics`, `lock-order-inversion`,
  `lock-held-across-io`, `thread-sleep-in-lock`, `parallel-stream-hazard`,
  `executor-without-shutdown`, `submit-in-loop`, `lock-on-boxed`,
  `false-sharing-and-escape`
- **Correctness smells** — `equals-hashcode-mismatch`, `double-checked-locking`,
  `null-return-ignore`, `reference-equality`, `narrow-calculation`,
  `static-mutable-state`, `missing-super-call`, `overridden-not-annotated`,
  `modern-idiom-candidates`
- **Resources & exceptions** — `resource-open-never-closed`, `files-stream-leak`,
  `exception-contract-drift`, `empty-catch-by-fanin`, `dead-exception`,
  `try-in-loop`, `static-write-in-ctor`, `n-plus-one`
- **Security** — `reflection-frontier`, `deserialization-reachability`,
  `native-surface-reachable`, `banned-api-surface`, `weak-random-surface`,
  `sql-concat-surface`, `xxe-parser-surface`, `zip-slip-surface`,
  `hardcoded-secret-candidates`, `open-redirect-surface`,
  `unauthenticated-input-surface`
- **Design / architecture** — `hierarchy-depth`, `di-bottleneck`,
  `overload-density`, `iface-impl-ratio`, `package-cycle`,
  `annotation-coupling`, `abstract-fanout`, `layer-violations`,
  `megamorphic-callsites` (M), `raw-types-and-unchecked` (M),
  `per-element-cost` (M), `boxing-in-hot-loop` (M), `string-concat-in-loop`,
  `regex-and-format-per-call` (M), `platform-charset-across-module-boundary` (M),
  `serializable-no-uid` (M), `print-stacktrace-leak` (M), `god-class` (M),
  `setaccessible-and-finalizers` (M), `deep-nesting` (M), `too-many-params` (M),
  `suppressed-warnings` (M)

### JavaScript (41 act, 14 weigh)

Event-loop health, listener/timer lifetime, and browser/Node security:

- **Event loop** — `event-loop-block-frontier`, `sync-io-below-a-handler`,
  `sync-io-under-handler`, `await-in-loop-serialized`,
  `floating-promise-crossmodule`, `then-without-catch`,
  `async-colour-frontier`, `process-exit-in-handler`
- **Leaks & lifetime** — `retention-leak-frontier`, `unbounded-module-cache`,
  `timer-balance`, `hooks-rules-violations` (React rules of hooks)
- **Security** — `proto-pollution-frontier`, `redos-frontier`, `dom-sink-frontier`,
  `command-injection-surface`, `proto-mutation`, `object-injection-surface`,
  `open-redirect-surface`, `ssrf-fetch-surface`, `path-traversal-surface`,
  `unchecked-upload-surface`, `zip-slip-surface`, `mass-assignment-surface`,
  `log-injection-surface`, `sensitive-log-surface`,
  `unauthenticated-input-surface`, `hardcoded-secret-candidates`
- **Dynamic dispatch** — `dynamic-import-and-eval`, `dynamic-require`
- **Perf & dependencies** — `includes-in-loop`, `unused-dependencies`,
  `spread-in-loop` (M), `quadratic-scan-in-hot-callee` (M),
  `shape-deopt-surface` (M), `megamorphic-shapes` (M)
- **Architecture** — `import-cycle`, `layer-crossings`,
  `relative-import-depth`, `global-pollution`, `reexport-propagation`,
  `anon-callback-depth`, `destructured-vs-default`, `duplicate-branch-conditions`,
  `dead-exports-barrel-blast` (M), `jsx-component-complexity` (M)

### TypeScript (51 act, 19 weigh)

The type system is a first-class citizen — the any type's blast radius,
suppressions, type-vs-value space:

- **Type hygiene** — `any-blast-radius`, `any-escape-hatch`,
  `assertion-density`, `assertion-escape-hatches`, `non-null-assertion`,
  `unsafe-type-assertion`, `any-interpolation`, `type-vs-value-space`,
  `orphan-types`, `path-alias-utilization`, `ambient-augmentation`,
  `iface-inherit-chain`, `type-export-mismatch`, `type-import-misuse`,
  `mutability-blast`, `weak-interfaces` (M), `index-signature-holes` (M),
  `type-level-complexity` (M), `type-depth-blowup` (M),
  `declaration-vs-implementation` (M)
- **Suppressions** — `suppression-on-hot-code`, `suppression-debt`, `ts-ignore`,
  `suppression-without-reason`, `strictness-map` (M)
- **Async & events** — `floating-promise`, `async-in-loop`, `await-in-loop`,
  `sync-under-handler`, `event-loop-block-below-entry`, `process-exit-in-handler`,
  `listener-leak`, `timer-leak`, `listener-added-never-removed`
- **Security** — `child-process-surface`, `open-redirect-surface`,
  `ssrf-fetch-surface`, `path-traversal-surface`, `unchecked-upload-surface`,
  `zip-slip-surface`, `mass-assignment-surface`, `log-injection-surface`,
  `sensitive-log-surface`, `unauthenticated-input-surface`,
  `hardcoded-secret-candidates`, `redos-reachable`, `redos-surface`,
  `dom-sinks`, `dom-xss-sink`
- **Architecture** — `import-cycles`, `boundary-crossings`,
  `unused-dependencies`, `dead-service-methods`, `barrel-blast` (M),
  `dead-exports` (M), `module-coupling` (M), `ts7-breaking` (M),
  `deprecated-usage`, `duplicate-enum-values`, `mixed-enums`

### Python (57 act, 23 weigh)

Async/event-loop honesty, mutable-state traps, and the dynamic-language escape
hatches:

- **Async** — `async-blocking`, `async-blocking-reachable`, `await-in-loop`
- **Data & performance** — `n-plus-one`, `sql-built-by-hand`,
  `loop-multiplied`, `quadratic-strings`, `append-in-loop-perf`,
  `exception-in-loop`, `closure-in-loop`
- **Error handling** — `swallowed-errors`, `bare-except`, `raise-without-from`,
  `resource-discipline`
- **Mutable state & concurrency** — `mutable-defaults`, `shared-mutable-state`,
  `unbounded-caches`, `global-statement`, `concurrency-surface`,
  `name-shadowing`, `call-in-default-argument`
- **Security** — `untrusted-frontier`, `unsafe-decode-reachable`, `weak-crypto`,
  `pickle-deserialization`, `yaml-unsafe-load`, `subprocess-shell-injection`,
  `eval-exec-injection`, `assert-in-production`, `open-without-with`,
  `datetime-naive`, `request-without-timeout`, `template-injection`,
  `open-redirect-surface`, `ssrf-fetch-surface`, `path-traversal-surface`,
  `unchecked-upload-surface`, `zip-slip-surface`, `log-injection-surface`,
  `xxe-parser-surface`, `unauthenticated-input-surface`,
  `hardcoded-secret-candidates`
- **Reflection & structure** — `reflection-opacity`, `decorator-roots`,
  `decorator-depth`, `import-cycles`, `import-workarounds`,
  `relative-import-depth`, `wildcard-import-rank`, `all-reexports`,
  `non-public-leak`, `method-kind-mix`, `undocumented-export`,
  `suppression-burden`, `untested`, `broad-test-expectation`
- **Design** — `typing-holes` (M), `class-shape` (M), `slots-candidates` (M),
  `god-class` (M), `magic-numbers` (M), `module-coupling` (M),
  `scattered-concerns` (M), `too-many-locals` (M), `too-many-branches` (M),
  `too-many-return` (M), `line-too-long` (M), `untyped-params` (M),
  `deep-nesting` (M), `nested-loops` (M), `latent-risk-density` (M),
  `undocumented-complexity` (M)

### Ruby (55 act, 9 weigh)

Rails/ActiveRecord behaviour, metaprogramming, and the monkey-patch surface:

- **ActiveRecord & DB** — `n-plus-one`, `callback-cascade`, `sql-interpolation`,
  `sql-injection-ar`, `raw-sql-below-a-controller`, `write-per-iteration`,
  `unscoped-find-params`, `mass-assignment`, `mass-assignment-weak-params`,
  `save-without-bang`, `find-each-missed`
- **Metaprogramming & dynamic dispatch** — `params-to-dynamic-dispatch`,
  `eval-family-surface`, `eval-injection`, `send-injection`,
  `constantize-injection`, `shell-out-surface`, `open-injection`,
  `unsafe-deserialization`, `html-safe-xss`
- **Monkey-patching** — `monkey-patch-blast-radius`, `monkey-patch-surface`,
  `ancestor-chain-depth`, `mixin-method-collision`, `heavy-mixins`,
  `super-overrides`, `yield-hubs`, `attr-coupling`
- **Threads & state** — `class-state-under-threads`,
  `threads-without-synchronisation`, `thread-coupling`
- **Perf** — `string-churn-unfrozen`, `per-iteration-cost`,
  `string-concat-in-loop`, `legacy-enumerable-idioms`, `block-vs-proc-cost` (M),
  `frozen-literal-debt` (M)
- **Smells & coverage** — `rescue-swallow`, `rescue-too-broad`,
  `unused-private`, `nested-iterators`, `feature-envy`, `param-clumps`,
  `debugger-surface`, `typing-coverage`, `timeout-blast-radius`,
  `import-cycle`
- **Security** — `open-redirect-surface`, `ssrf-fetch-surface`,
  `path-traversal-surface`, `zip-slip-surface`, `log-injection-surface`,
  `xxe-parser-surface`, `unauthenticated-input-surface`,
  `hardcoded-secret-candidates`, `weak-hash`

### PHP (49 act, 13 weigh)

Superglobal taint tracking is the differentiator — input flows to sinks:

- **Superglobal taint** — `superglobal-to-sql`, `superglobal-to-include`,
  `superglobal-to-shell`, `superglobal-to-echo`, `ssrf-frontier`,
  `type-juggling-auth`, `file-upload-surface`, `unchecked-upload-surface`,
  `unauthenticated-input-surface`
- **Injection, auth & deserialization** — `unserialize-gadget-frontier`,
  `deserialization-injection`, `command-injection`, `file-inclusion-injection`,
  `header-redirect-open`, `open-redirect-surface`, `remote-fetch-ssrf`,
  `extract-injection`, `loose-comparison-type-juggling`, `weak-hash`,
  `session-fixation`, `csrf-missing`, `magic-method-surface`
- **Errors & robustness** — `error-suppression`, `error-suppression-operator`,
  `broad-catch-surface`, `magic-fallback-risk`
- **DB** — `n-plus-one`, `unprepared-sql-hotspots`, `driver-split`
- **Modernization** — `implicit-nullable-params`, `dynamic-property-writes`,
  `bool-flag-methods`, `deprecated-api-frontier`, `dynamic-call-surface`
- **Architecture** — `trait-adoption`, `namespace-instability`, `lsb-hotspots`,
  `psr4-violations`, `iface-coverage`, `abstract-hooks`, `untyped-public-boundary`,
  `npath-explosion`, `maintainability-index-worst`, `god-classes` (M),
  `strict-types-coverage` (M), `strict-types-missing` (M), `untyped-params` (M),
  `array-scan-in-a-hot-method` (M), `property-hooks` (M)
- **Outbound surface** — `outbound-fetch-below-a-controller`
- **Security (shared OWASP family)** — `hardcoded-secret-candidates`,
  `path-traversal-surface`, `xxe-parser-surface`, `log-injection-surface`

### Rust (51 act, 14 weigh)

Unsafe reachability is the central question — what a safe API can pull in:

- **Unsafe** — `unsafe-under-pub-api`, `unsafe-without-comment`,
  `safety-doc-debt`, `transmute-and-raw-pointers`, `transmute-misuse`,
  `static-mut-unsafe`, `unsafe-in-loop`, `ffi-raw-balance`, `ffi-crossings`,
  `suppression-clusters`, `suppression-without-reason`
- **Async** — `lock-held-across-await`, `refcell-across-await`,
  `runtime-borrow-panic-surface`, `blocking-io-in-async`, `block-on-async`,
  `spawn-without-join`, `async-task-hubs`, `dropped-futures`,
  `blocking-work-below-public-api`
- **Panic & error paths** — `panic-frontier`, `result-that-panics`,
  `unwrap-in-prod`, `expect-in-prod`, `placeholder-panic-sites`,
  `error-swallowing-sites`, `debug-print-residue`
- **Memory, casts & perf** — `rc-cycle-risk`, `rc-refcell-mutation`,
  `arc-mutex-contention`, `clone-in-loop`, `vec-new-push-in-loop`, `len-in-loop`,
  `indexing-slicing-surface`, `lossy-casts`, `float-equality`,
  `atomic-ordering-audit`, `relaxed-ordering`, `clone-churn-per-iteration` (M),
  `alloc-churn-collect-and-format` (M), `mono-blast-radius` (M),
  `dynamic-dispatch-cost` (M), `box-dyn-overuse` (M), `dyn-with-one-impl` (M)
- **Architecture & deps** — `trait-breadth`, `macro-density`,
  `impl-fragmentation`, `deep-module-paths`, `import-cycle`,
  `cfg-feature-nobody-builds` (M), `manifest-vs-usage`, `public-api-doc-debt`
- **Security** — `sql-string-build`, `command-build-surface`,
  `untrusted-deserialization`, `zip-slip-surface`,
  `hardcoded-secret-candidates`

### C (43 act, 26 weigh)

Ownership and layout are measured byte-accurately — the regex scanner models
structs, alignment and alloc/free pairs:

- **Memory safety** — `ownership-review`, `memory-leak-surface`,
  `double-free-surface`, `null-deref-surface`, `buffer-overflow-surface`,
  `format-string-injection`, `integer-overflow-surface`,
  `division-by-zero-surface`, `unchecked-conversion-on-an-io-path`,
  `stack-exhaustion`, `toctou-access-open`
- **Concurrency & races** — `race-surface`, `race-condition-surface`,
  `nonreentrant-under-threads`, `signal-handler-unsafe`, `infinite-loop`
- **Allocation** — `allocator-mixing`, `alloc-per-iteration`, `bypass-tax`,
  `alloc-cost` (M)
- **Loops & vectorisation** — `per-element-dispatch`, `loop-invariant-strlen`,
  `nested-loops` (M), `vectorisation-blocked` (M), `explicit-simd` (M)
- **Layout** — `struct-padding` (M), `cache-line-crossers` (M),
  `cache-hostile-layout` (M), `stack-pressure` (M), `cast-density` (M),
  `macro-machinery` (M)
- **Structure & linkage** — `vtable-risk`, `fnptr-blindspot-callers`,
  `recursion-loops`, `global-state-mutation`, `unreferenced-includes`,
  `blast-radius`, `cross-file-struct-coupling`, `extern-linkage-density`,
  `cross-tu-signature-drift`, `linkage-scope-mismatch`,
  `extern-symbol-asymmetry`, `include-cycles`, `header-scope-ratio`,
  `header-fanout` (M), `backend-parity` (M), `config-gated` (M),
  `hand-linked-objects` (M), `profiler-invisible` (M), `module-coupling` (M),
  `undocumented-complexity` (M)
- **Standards (CERT/MISRA)** — `switch-no-default`, `unused-return-value`,
  `macro-side-effect`, `const-cast-away`, `goto-spaghetti` (M),
  `deep-nesting` (M), `too-many-params` (M), `magic-number` (M),
  `error-shape-mix`
- **Security** — `untrusted-frontier`, `risky-process-apis`,
  `hardcoded-secret-candidates`

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
