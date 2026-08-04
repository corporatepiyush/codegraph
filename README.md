# codegraph

Parse a source tree into an in-memory SQLite graph, then ask it hard questions.

One self-contained Python script per language. No server, no daemon, no index to
keep warm. Point it at a repo and it re-reads and re-parses everything, builds
the whole graph in `:memory:`, answers, and exits.

```bash
python3 codegraph_javascript.py /path/to/repo --report
python3 codegraph_javascript.py /path/to/repo --list
python3 codegraph_javascript.py /path/to/repo 8 10 --limit 20
```

That last line runs query 8 (`redos-frontier` — regex literals with nested
quantifiers reachable from untrusted input) and query 10
(`dead-exports-barrel-blast` — exports nothing imports, and the barrel files
that hide the answer), twenty rows each.

Every run re-parses from source because a graph file on disk gets read after the
code it describes has moved on, and **a stale graph is worse than none** — it
answers confidently and wrongly.

## Getting one file

Each analyzer is standalone, so take only the language you need:

```bash
curl -O https://raw.githubusercontent.com/corporatepiyush/codegraph/master/codegraph_javascript.py
```

Swap the filename for `codegraph_{c,python,go,rust,java,typescript,php,ruby}.py`.
To land it somewhere specific, or to grab several at once:

```bash
curl -sSL -o ~/bin/codegraph_go.py https://raw.githubusercontent.com/corporatepiyush/codegraph/master/codegraph_go.py
```

```bash
for L in javascript typescript go rust; do
  curl -sSLO "https://raw.githubusercontent.com/corporatepiyush/codegraph/master/codegraph_${L}.py"
done
```

Then install the grammar it needs and run it — nothing else to clone, no
package to install, no config file:

```bash
python3 codegraph_javascript.py --install-deps
python3 codegraph_javascript.py /path/to/repo --report
```

## Why this instead of a linter

A linter reads one file and tells you about that file. This builds the call
graph and asks questions that only make sense across it:

- *Which blocking calls can an async request handler reach, four frames down?*
- *Which `unsafe` blocks can a downstream crate trigger through safe API?*
- *Which goroutines spawn under an HTTP handler with no context and no joiner?*
- *Which mutable default argument is shared by forty callers?*
- *Which interfaces have exactly one implementation — an abstraction over nothing?*

Every analyzer answers the same four questions — `graph-blindspots`,
`hot-multipliers`, `risk-ranked`, `dead-code`, `parse-coverage` — so that a
check missing from one language is never mistaken for a clean result.

Each query ships with three lines of prose:

```
ANSWERS  the question this settles
ACT      what to do with a row
MISLEADS how this metric lies
```

The third line is the one that earns its place. A ranking without it gets read
as a finding, and someone spends a day on the top row of a list that was only
ever a heuristic.

## Honesty about what it cannot see

Static reading of a dynamic language is guesswork at the edges, so the tool
measures its own blindness and reports it before anything else:

- `unresolved_calls` — a call we saw but could not point at a definition
- `n_external_calls` — calls that leave the tree by design (stdlib, packages),
  kept separate from genuine blindness so the blind-share number stays useful
- `n_dynamic_calls` — dispatch computed at runtime
- `files.n_parse_errors` — what the parser could not read
- `meta.parse_mode` — which parser actually ran, recorded rather than assumed

`--report` prints a **HOW MUCH OF THIS TO TRUST** section, and query 1 in every
catalogue is `graph-blindspots`. Read it first.

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

**Requires CPython 3.14+** and its bundled SQLite 3.37+ (the schema uses
`STRICT` tables). The floor is enforced at startup rather than left to produce a
thinner graph that looks complete.

Version targets were verified against primary sources in August 2026, not
recalled. Three things worth knowing: Python 3.15 is at beta 4 with rc1 due
2026-08-04 and final 2026-10-01; TypeScript 7.0 ships **no programmatic API**
until 7.1, which is why this brings its own parser rather than driving `tsc`;
and `tree-sitter-{ruby,typescript,java}` are the oldest grammars here at ~20
months, which each analyzer records in `meta.grammar_note`.

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

`codegraph_python.py` (stdlib `ast`) and `codegraph_c.py` (brace scanning) need
no grammar and always run.

## Output

```bash
--report          narrative overview, including what it could not read
--list            the query catalogue
--sql "SELECT …"  ad-hoc against the graph
--csv N           query N as CSV
--json N          query N as JSON
--save graph.db   also write the graph to a file (refuses to overwrite;
                  pass --force to allow it)
--schema          dump the schema
--quiet           suppress progress output (implied by --csv and --json)
```

Filters: `--module PATTERN`, `--limit N`, `--no-tests`, `--include-generated`,
`--include-vendored`. Generated and vendored code is excluded by default — a
40k-line generated parser table would otherwise top every complexity chart.

Test detection is per language, not one shared regex. A shared one applied
Ruby's `_spec.` to Go and flagged Terraform's production `decoder_spec.go`,
while missing all 221 files in type-fest's `test-d/`.

## The query catalogue

**201 queries across nine languages.** Every one carries `ANSWERS` / `ACT` /
`MISLEADS`, and every one is graded on real repositories rather than merely
executed — a query that runs, returns rows and ranks by a column that is always
zero looks exactly like a working one.

Five checks exist in every language, so a gap in one is never mistaken for a
clean result: `graph-blindspots`, `hot-multipliers`, `risk-ranked`, `dead-code`,
`parse-coverage`.

### C — `codegraph_c.py`

32 queries. Target: C11/C17.

 1. **`graph-blindspots`** — Read this first: where the call graph cannot see
 2. **`hot-multipliers`** — Where one fix multiplies: highest fan-in, ranked with complexity
 3. **`risk-ranked`** — Security review order: complexity x hazard x recursion
 4. **`untrusted-frontier`** — Parses attacker bytes AND does pointer/size arithmetic
 5. **`stack-exhaustion`** — Self-recursive functions: unbounded input depth is a stack DoS
 6. **`ownership-review`** — Allocates but never frees in the same function
 7. **`alloc-cost`** — Allocations per call, TRANSITIVELY
 8. **`allocator-mixing`** — Files that use libc malloc AND a project allocator
 9. **`alloc-per-iteration`** — malloc/realloc inside a loop body
10. **`bypass-tax`** — Allocates BEFORE it knows the fast path applies
11. **`race-surface`** — Mutable, non-atomic, non-const file-scope state
12. **`module-coupling`** — Cross-module call edges: where a seam would actually cut
13. **`header-fanout`** — Headers whose change rebuilds the most of the tree
14. **`per-element-dispatch`** — A switch INSIDE a loop: type dispatch paid once per element
15. **`loop-invariant-strlen`** — strlen() inside a loop: accidental O(n^2)
16. **`nested-loops`** — Loop depth >= 2: the O(n^k) candidates, with their per-iteration cost
17. **`vectorisation-blocked`** — Loops that CANNOT vectorise: a libm call in the body
18. **`explicit-simd`** — Hand-written intrinsics and branch hints
19. **`struct-padding`** — Byte-accurate layout: bytes lost to alignment holes
20. **`cache-line-crossers`** — Structs just over a 64-byte cache line
21. **`cache-hostile-layout`** — Pointer-dense structs: each pointer field defeats the prefetcher
22. **`stack-pressure`** — Functions with the most locals, and the most pointer locals
23. **`cast-density`** — Pointer casts: where the type system was overruled
24. **`error-shape-mix`** — Functions that report failure in more than one shape
25. **`macro-machinery`** — Function-like macros, by how much work they do
26. **`config-gated`** — Code behind a CONFIG_/HAVE_/USE_ flag
27. **`backend-parity`** — One name, two definitions: which #if-selected backend is the STUB
28. **`profiler-invisible`** — static inline with real fan-in: zero self-time is not zero cost
29. **`undocumented-complexity`** — Complex functions with almost no comments
30. **`hand-linked-objects`** — Build rules and object lists that enumerate their inputs by hand
31. **`parse-coverage`** — How much of the tree this run actually read
32. **`dead-code`** — Nothing in this tree calls these

### Python — `codegraph_python.py`

35 queries. Target: Python 3.15.

 1. **`graph-blindspots`** — Read this first: where the call graph cannot see
 2. **`risk-ranked`** — Review order: if you can only read N functions this week, which N
 3. **`hot-multipliers`** — Where one fix pays back many times: highest fan-in
 4. **`async-blocking`** — Blocking calls inside async functions -- the event loop stops here
 5. **`async-blocking-reachable`** — Blocking work reachable from an async caller, up to 4 hops away
 6. **`await-in-loop`** — Sequential awaits: requests issued one at a time that could overlap
 7. **`mutable-defaults`** — Mutable default arguments, ranked by how many callers share the object
 8. **`untrusted-frontier`** — Dangerous sinks and how far they sit from a public entry point
 9. **`sql-built-by-hand`** — Queries assembled with f-strings, concatenation or .format
10. **`n-plus-one`** — Database work inside a loop: N queries where one would do
11. **`loop-multiplied`** — Work done per iteration that could be hoisted out
12. **`quadratic-strings`** — String built by += inside a loop -- quadratic in the result size
13. **`swallowed-errors`** — except blocks that catch everything and tell nobody
14. **`reflection-opacity`** — Runtime reflection: where static reading stops working
15. **`decorator-roots`** — Functions that look dead because a decorator registers them
16. **`dead-code`** — Nothing in this tree calls these
17. **`untested`** — Functions no test file reaches
18. **`typing-holes`** — Public API without type annotations, ranked by blast radius
19. **`unbounded-caches`** — @lru_cache / @cache with no maxsize, and module-level mutable state
20. **`shared-mutable-state`** — Module-level mutable state, and who writes to it
21. **`import-cycles`** — Modules that import each other
22. **`import-workarounds`** — Imports hidden inside functions -- usually a cycle being dodged
23. **`god-functions`** — Functions doing too much, by every measure at once
24. **`deep-nesting`** — Nesting deep enough that the reader loses the thread
25. **`nested-loops`** — Nested loops: where the input size decides whether this matters
26. **`class-shape`** — Classes carrying too much, and classes carrying nothing
27. **`slots-candidates`** — Classes instantiated in a loop that carry no __slots__
28. **`resource-discipline`** — Files, sockets and connections opened outside a with-block
29. **`weak-crypto`** — md5, sha1, and the random module used where secrets belongs
30. **`concurrency-surface`** — Everything that spawns, locks or shares, in one place
31. **`module-coupling`** — Which modules depend on which, and how unstable that makes them
32. **`undocumented-complexity`** — The hardest functions, with nothing written down
33. **`magic-numbers`** — Unexplained constants, and the ones repeated across files
34. **`markers`** — TODO, FIXME, HACK and BUG, weighted by the code they sit in
35. **`parse-coverage`** — What this run could not read

### Go — `codegraph_go.py`

23 queries. Target: Go 1.26.

 1. **`graph-blindspots`** — Read this first: where the call graph cannot see
 2. **`goroutine-leak-frontier`** — Goroutines with no context, no WaitGroup and no errgroup
 3. **`goroutine-under-handler`** — Goroutines reachable from a request handler, up to 4 hops
 4. **`ctx-propagation-break`** — Where a live context stops being passed down
 5. **`defer-lifetime`** — defer inside a loop: cleanup that waits for the whole function
 6. **`resource-close-cross-layer`** — Opens a body, rows or file and defers no Close
 7. **`unchecked-errors`** — Discarded errors, weighted by how much of the tree calls the discarder
 8. **`channel-topology`** — Unbuffered channels, and whether anything can receive
 9. **`single-impl-interface`** — Interfaces satisfied by exactly one type: abstraction over nothing
10. **`heap-pressure-loops`** — Sprintf, uncapped append and conversions inside loops
11. **`range-value-copy`** — for _, v := range over big structs: a memcpy per element
12. **`lock-copied-by-value`** — Types embedding a sync.Mutex passed by value
13. **`lock-over-crosspkg-call`** — A mutex held while calling into another package
14. **`n-plus-one`** — A query function whose CALLER puts it in a loop
15. **`unsafe-cgo-frontier`** — unsafe.Pointer and cgo reachable from a handler, up to 5 hops
16. **`package-state-concurrent`** — Packages that spawn goroutines and hold unguarded package state
17. **`risk-ranked`** — Review order: if you can only read N functions this week, which N
18. **`hot-multipliers`** — Where one fix pays back many times: highest fan-in
19. **`god-functions`** — Functions doing too much, by every measure at once
20. **`dead-code`** — Nothing in this tree calls these
21. **`module-coupling`** — Which packages depend on which, and how unstable that makes them
22. **`markers`** — TODO, FIXME, HACK and BUG, weighted by the code they sit in
23. **`parse-coverage`** — What this run could not read

### Rust — `codegraph_rust.py`

18 queries. Target: Rust 1.97 / edition 2024.

 1. **`graph-blindspots`** — Read this first: where the call graph cannot see
 2. **`unsafe-under-pub-api`** — unsafe reachable from a public function, up to 4 hops
 3. **`panic-frontier`** — unwrap, indexing and unchecked arithmetic on a public or spawned path
 4. **`lock-held-across-await`** — A guard still alive at a .await, here or up to 3 frames down
 5. **`blocking-io-in-async`** — std blocking calls reachable from an async fn without a spawn_blocking
 6. **`clone-churn-per-iteration`** — Clone and allocation inside loops, weighted by depth and fan-in
 7. **`dyn-with-one-impl`** — Trait objects for traits that have exactly one implementation
 8. **`mono-blast-radius`** — Generic functions whose body gets copied once per instantiation
 9. **`result-that-panics`** — Functions returning Result or Option that panic anyway
10. **`rc-cycle-risk`** — Modules full of Rc<RefCell<>> and Arc<Mutex<>> with no Weak anywhere
11. **`ffi-raw-balance`** — into_raw without a from_raw, and unsafe impl Send on FFI types
12. **`cfg-feature-nobody-builds`** — #[cfg(feature)] naming a feature Cargo.toml never declares
13. **`safety-doc-debt`** — unsafe blocks doing several things behind no SAFETY comment
14. **`suppression-clusters`** — #[allow] sitting on top of code that actually does the thing
15. **`hot-multipliers`** — Where one fix pays back many times: highest fan-in
16. **`risk-ranked`** — Review order: if you can only read N symbols this week, which N
17. **`dead-code`** — Nothing in this tree calls these
18. **`parse-coverage`** — What this run could not read

### Java — `codegraph_java.py`

18 queries. Target: Java 25 (LTS).

 1. **`graph-blindspots`** — Read this first: where the call graph cannot see
 2. **`reflection-frontier`** — Public entry points that reach Class.forName or setAccessible
 3. **`deserialization-reachability`** — Deserialization and JNDI sinks reachable from an entry point
 4. **`resource-open-never-closed`** — Opened here, closed somewhere else -- or nowhere
 5. **`lock-order-inversion`** — Two locks taken in opposite orders in different methods
 6. **`lock-held-across-io`** — A monitor held while doing IO, sleeping or allocating
 7. **`vt-pinning-frontier`** — Virtual-thread roots reaching JNI or FFM -- NOT synchronized
 8. **`per-element-cost`** — String +, boxing, Pattern.compile and prepareStatement inside loops
 9. **`megamorphic-callsites`** — Interfaces with 3+ implementations, invoked from inside a loop
10. **`threadlocal-leak-on-pooled`** — ThreadLocal set with no remove, reachable from a POOLED executor
11. **`shared-mutable-statics`** — Non-final static state in modules that start threads
12. **`exception-contract-drift`** — throws Exception, a swallowed catch, and a null return
13. **`n-plus-one`** — A DAO or query method whose CALLER puts it in a loop
14. **`false-sharing-and-escape`** — Contended counters on one cache line, and allocations that escape
15. **`parse-coverage`** — What this run could not read, and why
16. **`hot-multipliers`** — Where one fix pays back many times: highest fan-in
17. **`risk-ranked`** — Review order: if you can only read N symbols this week, which N
18. **`dead-code`** — Nothing in this tree calls these

### JavaScript — `codegraph_javascript.py`

17 queries. Target: ES2026.

 1. **`graph-blindspots`** — Read this first: where the call graph cannot see
 2. **`retention-leak-frontier`** — Listeners and timers registered with nothing in the module that undoes it
 3. **`unbounded-module-cache`** — Module-scope containers that are written to and never emptied
 4. **`event-loop-block-frontier`** — Blocking *Sync calls reachable from a request handler, up to 4 hops
 5. **`await-in-loop-serialized`** — await inside a loop where nothing on the path batches with Promise.all
 6. **`floating-promise-crossmodule`** — Async functions whose callers never await them, across module lines
 7. **`proto-pollution-frontier`** — Recursive writers reachable from parsed request input, up to 4 hops
 8. **`redos-frontier`** — Regex literals with nested quantifiers reachable from untrusted input
 9. **`megamorphic-shapes`** — Hot functions doing dynamic property access, ranked by calling breadth
10. **`dead-exports-barrel-blast`** — Exports nothing imports, and the barrel files that hide the answer
11. **`dom-sink-frontier`** — innerHTML and friends reachable from untrusted input, up to 4 hops
12. **`async-colour-frontier`** — Where synchronous code calls async code, and how deep the async goes
13. **`god-functions`** — Functions doing too much, by every measure at once
14. **`parse-coverage`** — What this run could not read, and which files carry the most risk
15. **`hot-multipliers`** — Where one fix pays back many times: highest fan-in
16. **`risk-ranked`** — Review order: if you can only read N symbols this week, which N
17. **`dead-code`** — Nothing in this tree calls these

### TypeScript — `codegraph_typescript.py`

24 queries. Target: TypeScript 7.

 1. **`graph-blindspots`** — Read this first: where the call graph cannot see
 2. **`any-blast-radius`** — `any` weighted by how much code inherits the hole
 3. **`suppression-on-hot-code`** — @ts-ignore and eslint-disable sitting on code many callers depend on
 4. **`barrel-blast`** — Barrel files: how much gets pulled in per import
 5. **`strictness-map`** — Which directories opted out of which strict flags
 6. **`type-depth-blowup`** — Types deep enough to slow the compiler down
 7. **`listener-leak`** — Subscriptions added and never removed
 8. **`timer-leak`** — Timers started with no matching clear
 9. **`sync-under-handler`** — Blocking *Sync calls reachable from a request handler, up to 4 hops
10. **`await-in-loop`** — Sequential awaits that could have overlapped
11. **`redos-reachable`** — Regexes that can blow up, and how far they sit from an entry point
12. **`dom-sinks`** — innerHTML and friends, ranked by reachability from outside
13. **`import-cycles`** — Files that import each other, and whether the cycle is type-only
14. **`assertion-density`** — `as` and `!` clustered where types are weakest
15. **`weak-interfaces`** — Interfaces and types carrying `any` or an index signature
16. **`dead-exports`** — Exported and never imported anywhere in this tree
17. **`ts7-breaking`** — Config and syntax TypeScript 7 no longer accepts
18. **`god-functions`** — Functions doing too much, by every measure at once
19. **`risk-ranked`** — Review order: if you can only read N functions this week, which N
20. **`hot-multipliers`** — Where one fix pays back many times: highest fan-in
21. **`module-coupling`** — Which modules depend on which, and how unstable that makes them
22. **`markers`** — TODO, FIXME, HACK and BUG, weighted by the code they sit in
23. **`parse-coverage`** — What this run could not read
24. **`dead-code`** — Nothing in this tree calls these

### PHP — `codegraph_php.py`

16 queries. Target: PHP 8.5.

 1. **`graph-blindspots`** — Read this first: where a PHP call graph cannot see
 2. **`superglobal-to-sql`** — Attacker-controlled input reaching a SQL-building site, up to 4 hops
 3. **`superglobal-to-include`** — A variable include/require reachable from user input, up to 3 hops
 4. **`unserialize-gadget-frontier`** — unserialize reachable from input, against the repo's gadget surface
 5. **`superglobal-to-shell`** — User input reaching exec/system/shell_exec/backticks, up to 3 hops
 6. **`superglobal-to-echo`** — Unescaped output of reachable input, with escaping as counter-evidence
 7. **`n-plus-one`** — A query whose CALLER puts it in a foreach, followed through model methods
 8. **`strict-types-coverage`** — declare(strict_types=1) coverage against scalar-parameter density
 9. **`type-juggling-auth`** — Loose == on a value that reaches from a superglobal
10. **`driver-split`** — mysqli and PDO in the same namespace: two escaping disciplines, one module
11. **`property-hooks`** — PHP 8.4 property hooks: a field read that is really a call
12. **`god-classes`** — Classes and functions doing too much, by every measure at once
13. **`risk-ranked`** — Review order: if you can only read N functions this week, which N
14. **`parse-coverage`** — What this run could not read
15. **`hot-multipliers`** — Where one fix pays back many times: highest fan-in
16. **`dead-code`** — Nothing in this tree calls these

### Ruby — `codegraph_ruby.py`

18 queries. Target: Ruby 4.0.

 1. **`graph-blindspots`** — Read this first: Ruby's call graph is a lower bound, and here is by how much
 2. **`n-plus-one`** — An ActiveRecord query inside a block iterating a relation
 3. **`params-to-dynamic-dispatch`** — Request parameters reaching send, constantize, eval or a backtick
 4. **`monkey-patch-blast-radius`** — Reopened core classes, ranked by how many call sites they could affect
 5. **`string-churn-unfrozen`** — String literals allocated per iteration, in files with no frozen magic comment
 6. **`rescue-swallow`** — Rescue bodies that discard the error, ranked by what they wrapped
 7. **`class-state-under-threads`** — Mutable class-level state reachable from something a thread runs
 8. **`timeout-blast-radius`** — Timeout.timeout sites, ranked by what is running inside them
 9. **`mass-assignment`** — params reaching new/create/update with no permit in sight
10. **`block-vs-proc-cost`** — Block, proc and symbol-to-proc allocation on the methods called most
11. **`callback-cascade`** — ActiveRecord callbacks that issue queries, and what they pull in behind them
12. **`mixin-method-collision`** — Two modules included into one class, both defining the same method
13. **`sql-interpolation`** — String interpolation inside where, order, pluck and friends
14. **`per-iteration-cost`** — Collection literals, Range#include? and chained array allocations in loops
15. **`hot-multipliers`** — Where one fix pays back many times: highest fan-in
16. **`risk-ranked`** — Review order: if you can only read N symbols this week, which N
17. **`dead-code`** — Nothing in this tree calls these
18. **`parse-coverage`** — What this run could not read

## Correctness, and how it is checked

Three classes of bug have been found and fixed here, none of which a test that
merely runs the queries would catch. They are listed because each produced
confident, plausible, wrong numbers for a long time.

**Aggregates inflated by fan-out joins.** A `GROUP BY` across two one-to-many
joins multiplies every `SUM` by the other side's row count. One query reported
23,858 thread starters where the truth was 158; another claimed more primitive
fields than the type had fields at all. `COUNT(DISTINCT)`, `MIN` and `MAX`
survive duplication, so each query kept correct columns beside the wrong ones,
and `HAVING` survives a positive multiplier — so the right rows came back
carrying wrong numbers, while `ORDER BY` silently ranked by the bug.

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

What catches these is not a bigger test suite but an invariant per query: a type
cannot have more primitive fields than it has fields; a symbol cannot contain
more call sites than its file does. Violations are counted before and after a
fix, because "looks better" is not a result.

## Modern language constructs

Each analyzer targets a current language version, and the constructs that
version added are tracked rather than merely parsed without error:

| Language | Recently added, and recorded |
|---|---|
| Java 25 | records, sealed types, pattern-matching `switch`, virtual threads, JEP 491 pinning (`synchronized` is **not** a finding on 24+), text blocks |
| Rust 2024 | `async`/`await`, `unsafe` surface, lifetimes, const generics, associated types, `let ... else` — a real branch, counted toward complexity |
| Go 1.26 | generics, goroutines, channels, `defer`, `errors.Is`/`As`, loop-variable semantics, range-over-func |
| TypeScript 7 | `satisfies`, `const` type parameters, decorators, enums, namespaces, `any` propagation |
| PHP 8.5 | enums, `readonly`, property hooks, attributes, first-class callables, `never` |
| Python 3.15 | `match`, walrus, PEP 695 type parameters, dataclasses, `async`, `@overload` |
| Ruby 4.0 | pattern matching, refinements, metaprogramming, blocks, ActiveRecord idioms, Ractor/Fiber |
| JavaScript ES2026 | private fields, decorators, top-level `await`, optional chaining, generators, workers |

Coverage is established by parsing a fixture of each construct and checking what
the analyzer recorded — not by reading a changelog. That distinction matters:
several constructs that looked missing were already handled, and one that looked
handled was not.

## One file per language, and nothing else

There are no shared modules, no package, no imports between these files. Each
`codegraph_<lang>.py` contains everything it needs — the schema, the parser
wiring, the metrics, the hazard catalogue, the queries and the CLI. Copy one
file onto a machine and it runs.

That also means each analyzer is free to disagree with the others. **The schema
is per language, not universal**, because the languages are not universal:

- Go carries `goroutines`, `defers`, `channels`, `interfaces`, `structs`, and
  columns like `n_ctx_background` and `n_err_shadowed`.
- Python carries `classes`, `handlers`, `dynamic_sites`, `comprehensions`,
  `module_vars`, and columns like `n_mutable_default` and `n_bare_except`.
- Rust carries `unsafe_blocks`, `impls`, `traits`, `async_points`, `cfg_blocks`.

The tables that *do* recur — `files`, `symbols`, `edges`, `callsites`,
`unresolved_calls`, `imports`, `hazards`, `params`, `fields`, `literals`,
`markers`, `meta` — recur because the questions genuinely are the same, not
because a base class forced them to be. Where a language needs a column bent to
a different meaning, it bends it.

Hazard categories are declared per language and become `n_<category>` columns,
so `n_goroutine` exists in Go and `n_deserialize` exists in Python, and neither
carries the other's dead weight.

`--schema` dumps whatever that particular file defines.

## Licence

MIT
