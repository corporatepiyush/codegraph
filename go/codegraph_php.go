package main

import (
	"bufio"
	"bytes"
	"cmp"
	"crypto/sha1"
	"encoding/hex"
	"encoding/json/jsontext"
	"encoding/json/v2"
	"fmt"
	"io"
	"io/fs"
	"math/big"
	"os"
	"os/exec"
	"path/filepath"
	"reflect"
	"regexp"
	"runtime"
	"runtime/debug"
	"runtime/pprof"
	"runtime/trace"
	"slices"
	"sort"
	"strconv"
	"strings"
	"sync/atomic"
	"syscall"
	"time"
	"unicode/utf8"
	"unsafe"
)

const tsGrammarTag = "v0.24.1"

type anonChildFieldEnt struct{ parent, child, field string }

type tsTables struct {
	symNames        []string
	symNamed        []bool
	symVisible      []bool
	symSuper        []bool
	fieldNames      []string
	anonChildFields []anonChildFieldEnt
}

var tsTablesLoaded = loadTSTables()

var tsAbiVersion = 0

var tsSymCount = len(tsTablesLoaded.symNames)

var tsFieldCount = len(tsTablesLoaded.fieldNames)

var tsSymNamed = tsTablesLoaded.symNamed

var tsSymVisible = tsTablesLoaded.symVisible

var tsSymSuper = tsTablesLoaded.symSuper

var tsSymPublic = func() []uint16 {
	p := make([]uint16, len(tsSymNames))
	for i := range p {
		p[i] = uint16(i)
	}
	return p
}()

var tsSymNames = tsTablesLoaded.symNames

var tsFieldNames = tsTablesLoaded.fieldNames

var tsAnonChildFields = tsTablesLoaded.anonChildFields

func tsGrammarDir() string {
	if g := os.Getenv("TREE_SITTER_GRAMMARS"); g != "" {
		return filepath.Join(g, "tree-sitter-php")
	}
	home, err := os.UserHomeDir()
	if err != nil {
		home = "$HOME"
	}
	return filepath.Join(home, ".cache", "codegraph", "grammars", "tree-sitter-php")
}

func tsGrammarFatal(dir, detail string) {
	fmt.Fprintf(os.Stderr, `codegraph_php: %s

The kind tables are built at startup from the pinned grammar's JSON sources;
the checkout must exist under $TREE_SITTER_GRAMMARS (default
~/.cache/codegraph/grammars). Clone it with:

  git clone --depth 1 --branch %s https://github.com/tree-sitter/tree-sitter-php "%s"

`, detail, tsGrammarTag, dir)
	os.Exit(1)
}

type orderedObject[V any] []orderedMember[V]

type orderedMember[V any] struct {
	Name  string
	Value V
}

func (obj *orderedObject[V]) UnmarshalJSONFrom(dec *jsontext.Decoder) error {
	switch k := dec.PeekKind(); k {
	case jsontext.KindNull:
		_, err := dec.ReadToken()
		return err
	case jsontext.KindBeginObject:
	default:
		return &json.SemanticError{JSONKind: k}
	}
	if _, err := dec.ReadToken(); err != nil {
		return err
	}
	for dec.PeekKind() != jsontext.KindEndObject {
		*obj = append(*obj, orderedMember[V]{})
		member := &(*obj)[len(*obj)-1]
		if err := json.UnmarshalDecode(dec, &member.Name); err != nil {
			return err
		}
		if err := json.UnmarshalDecode(dec, &member.Value); err != nil {
			return err
		}
	}
	_, err := dec.ReadToken()
	return err
}

func loadTSTables() tsTables {
	dir := tsGrammarDir()
	nodeTypesRaw, err := os.ReadFile(filepath.Join(dir, "php", "src", "node-types.json"))
	if err != nil {
		tsGrammarFatal(dir, err.Error())
	}
	grammarRaw, err := os.ReadFile(filepath.Join(dir, "php", "src", "grammar.json"))
	if err != nil {
		tsGrammarFatal(dir, err.Error())
	}

	var entries []struct {
		Type   string                        `json:"type"`
		Named  *bool                         `json:"named"`
		Fields orderedObject[jsontext.Value] `json:"fields"`
	}
	if err := json.Unmarshal(nodeTypesRaw, &entries); err != nil {
		tsGrammarFatal(dir, "node-types.json: "+err.Error())
	}

	var t tsTables
	seen := map[string]bool{}
	seenFields := map[string]bool{}
	type pfKey struct{ parent, field string }
	var anonOrder []pfKey
	anonChildren := map[pfKey][]string{}
	anonChildSeen := map[pfKey]map[string]bool{}
	for _, e := range entries {
		name := e.Type
		if !seen[name] {
			seen[name] = true
			named := e.Named == nil || *e.Named
			t.symNames = append(t.symNames, name)
			t.symNamed = append(t.symNamed, named)
			t.symVisible = append(t.symVisible, true)
			t.symSuper = append(t.symSuper, false)
		}
		for _, kv := range e.Fields {
			f := kv.Name
			if f != "" && !seenFields[f] {
				seenFields[f] = true
				t.fieldNames = append(t.fieldNames, f)
			}
			var fv struct {
				Types []struct {
					Type  string `json:"type"`
					Named *bool  `json:"named"`
				} `json:"types"`
			}
			if err := json.Unmarshal(kv.Value, &fv); err != nil {
				tsGrammarFatal(dir, "node-types.json: "+err.Error())
			}
			for _, ty := range fv.Types {
				if ty.Named != nil && *ty.Named {
					continue
				}
				k := pfKey{name, f}
				if anonChildSeen[k] == nil {
					anonChildSeen[k] = map[string]bool{}
					anonOrder = append(anonOrder, k)
				}
				if !anonChildSeen[k][ty.Type] {
					anonChildSeen[k][ty.Type] = true
					anonChildren[k] = append(anonChildren[k], ty.Type)
				}
			}
		}
	}

	type pcKey struct{ parent, child string }
	anonPairs := map[pcKey]string{}
	for _, k := range anonOrder {
		for _, c := range anonChildren[k] {
			pk := pcKey{k.parent, c}
			if f, dup := anonPairs[pk]; dup && f != k.field {
				continue
			}
			anonPairs[pk] = k.field
		}
	}
	pks := make([]pcKey, 0, len(anonPairs))
	for k := range anonPairs {
		pks = append(pks, k)
	}
	sort.Slice(pks, func(i, j int) bool {
		if pks[i].parent != pks[j].parent {
			return pks[i].parent < pks[j].parent
		}
		return pks[i].child < pks[j].child
	})
	for _, k := range pks {
		t.anonChildFields = append(t.anonChildFields,
			anonChildFieldEnt{k.parent, k.child, anonPairs[k]})
	}

	var grammar struct {
		Supertypes []string `json:"supertypes"`
	}
	if err := json.Unmarshal(grammarRaw, &grammar); err != nil {
		tsGrammarFatal(dir, "grammar.json: "+err.Error())
	}
	for _, name := range grammar.Supertypes {
		if !seen[name] {
			seen[name] = true
			t.symNames = append(t.symNames, name)
			t.symNamed = append(t.symNamed, true)
			t.symVisible = append(t.symVisible, false)
			t.symSuper = append(t.symSuper, true)
			continue
		}
		for i, n := range t.symNames {
			if n == name {
				t.symSuper[i] = true
			}
		}
	}

	t.symNames = append(t.symNames, "ERROR", "\x00MISSING")
	t.symNamed = append(t.symNamed, true, true)
	t.symVisible = append(t.symVisible, true, true)
	t.symSuper = append(t.symSuper, false, false)

	t.fieldNames = append([]string{""}, t.fieldNames...)
	return t
}

const (
	langName   = "php"
	langTarget = "PHP 8.5"
	schemaVer  = 1
)

type cli struct {
	root       string
	which      []int
	module     string
	limit      int
	list       bool
	metrics    bool
	schema     bool
	report     bool
	csv        int
	hasCSV     bool
	json       int
	hasJSON    bool
	save       string
	saveAST    string
	loadAST    string
	force      bool
	deps       bool
	install    bool
	incGen     bool
	incVend    bool
	noTests    bool
	quiet      bool
	version    bool
	help       bool
	dump       string
	dumpTSV    string
	workers    int
	cpuprofile string
	memprofile string
}

const usage = `usage: codegraph_php [flags] [tree] [query-number ...]

Parse a php tree into a graph and answer questions about it in one shot.
Every run re-parses from source; nothing is cached, so an answer can never
describe code that has moved on.

positional arguments:
  tree              tree to parse (default ".")
  query-number      1-based question numbers to run (default: all)

flags:
  --module LIKE     module-name LIKE filter (default "%")
  --limit N         rows per question; -1 (default) is every row
  --list            list the questions
  --metrics         run/list the METRICS section instead of QUERIES
  --schema          print the graph's table structure
  --report          narrative overview
  --csv N           emit question N as CSV
  --json N          emit question N as JSON
  --save PATH       also write the graph to PATH
  --save-ast PATH   parse/build, then write the binary AST state to PATH
  --load-ast PATH   load a saved AST state instead of parsing
  --force           allow --save/--save-ast to overwrite an existing file
  --dump PATH       write the canonical graph dump to PATH
  --dump-tsv PATH   write the same graph, field-separated, for diffing
  --deps            show dependencies and how to install them
  --include-generated  parse generated files too (off by default)
  --include-vendored   parse vendored trees too (off by default)
  --no-tests        skip test files
  --workers N       parser workers (default: one per core)
  --cpuprofile PATH  write a CPU profile
  --memprofile PATH  write a heap profile
  --quiet
  --version
`

func cgPutU32(b []byte, o int, v uint32) { *(*uint32)(unsafe.Pointer(&b[o])) = v }
func cgPutU64(b []byte, o int, v uint64) { *(*uint64)(unsafe.Pointer(&b[o])) = v }
func cgGetU32(b []byte, o int) uint32    { return *(*uint32)(unsafe.Pointer(&b[o])) }
func cgGetU64(b []byte, o int) uint64    { return *(*uint64)(unsafe.Pointer(&b[o])) }

func main() {
	os.Exit(run(os.Args[1:]))
}

func run(argv []string) int {
	out := newOutput()
	defer out.flush()
	c := parseArgs(argv)
	if c == nil {

		fmt.Fprint(os.Stderr, usage)
		return 2
	}

	if c.help {
		out.raw(helpText)
		return 0
	}

	if c.version {
		out.printf("codegraph_%s  target=%s  schema=v%d  go=%s  tree-sitter=%s",
			langName, langTarget, schemaVer, runtimeVersion(), tsRuntimeVersion)
		return 0
	}
	if c.install {
		out.printf("all dependencies already present")
		if c.deps {
			out.raw("\n")
			describeDeps(out)
			return 0
		}
	} else if c.deps {
		describeDeps(out)
		return 0
	}
	if c.schema {
		printSchema(out)
		return 0
	}
	if c.list {
		qs := queries
		if c.metrics {
			qs = metrics
		}
		for i, q := range qs {
			out.printf("%2d. %-26s %s", i+1, q.name, q.title)
		}
		return 0
	}

	if c.hasCSV || c.hasJSON {
		c.quiet = true
		out.csv = true
	}

	if c.saveAST != "" && c.loadAST != "" {
		fmt.Fprintln(os.Stderr, "--save-ast and --load-ast cannot be used together")
		return 2
	}
	if c.loadAST == "" {
		st, err := os.Stat(c.root)
		if err != nil || !st.IsDir() {
			out.warnf("not a directory: %s", c.root)
			return 2
		}
	}

	var gp *graph

	if c.cpuprofile != "" {
		f, err := os.Create(c.cpuprofile)
		if err != nil {
			out.warnf("cannot write %s: %s", c.cpuprofile, err)
			return 2
		}
		startCPU(f)
		defer stopCPU(f)
	}
	if c.memprofile != "" {

		defer func() {
			writeMem(c.memprofile)
			runtime.KeepAlive(gp)
		}()
	}

	startPeakSampler(os.Getenv("CODEGRAPH_PEAKPROF"))
	defer stopPeakSampler()
	defer startContentionProfiling()()

	t0 := time.Now()
	var g *graph
	var n int
	if c.loadAST != "" {
		loaded, lerr := loadAST(c.loadAST)
		if lerr != nil {
			out.warnf("load-ast: %v", lerr)
			return 2
		}
		g = loaded
	} else {
		g = newGraph()
		n = build(mustAbs(c.root), g, buildOpts{
			includeTests: !c.noTests, includeGen: c.incGen, includeVend: c.incVend,
			quiet: c.quiet, workers: c.workers, keepTrees: c.saveAST != "",
		}, out)
	}
	gp = g
	took := time.Since(t0)

	if c.saveAST != "" {
		if _, serr := os.Lstat(c.saveAST); serr == nil && !c.force {
			out.warnf("refusing to overwrite %s (pass --force)", c.saveAST)
			return 2
		}
		ts := time.Now()
		nb, werr := saveASTFile(g, c.saveAST)
		if werr != nil {
			out.warnf("save-ast: %v", werr)
			return 2
		}
		if !c.quiet {
			out.warnf("ast state written to %s: %d bytes in %.1fs",
				c.saveAST, nb, time.Since(ts).Seconds())
		}
	}

	if c.dump != "" {
		f, err := os.Create(c.dump)
		if err != nil {
			out.warnf("cannot write %s: %s", c.dump, err)
			return 2
		}
		writeDump(f, g)
		f.Close()
	}
	if c.dumpTSV != "" {
		f, err := os.Create(c.dumpTSV)
		if err != nil {
			out.warnf("cannot write %s: %s", c.dumpTSV, err)
			return 2
		}
		writeTSV(f, g)
		f.Close()
	}
	if c.save != "" {
		if err := saveGraph(c.save, c.force, g, out); err != nil {
			out.warnf("%s", err)
		}
	}

	if c.hasCSV || c.hasJSON {
		qs := queries
		if c.metrics {
			qs = metrics
		}
		idx := c.csv - 1
		if c.hasJSON {
			idx = c.json - 1
		}
		if idx < 0 || idx >= len(qs) {
			fmt.Fprintf(out.ew, "no query %d\n", idx+1)
			return 2
		}
		r := runQuestion(g, qs[idx], c.module, c.limit)
		if c.hasCSV {
			r.writeCSV(out)
		} else {
			r.writeJSON(out)
		}
		return 0
	}

	if !c.quiet {

		lim := "all"
		if c.limit >= 0 {
			lim = fmtInt(c.limit)
		}
		if c.loadAST != "" {
			out.printf("codegraph-%s: %d files loaded from AST in %.1fs module=%s limit=%s",
				langName, len(g.fils), took.Seconds(), c.module, lim)
		} else {
			out.printf("codegraph-%s: %d files parsed into memory in %.1fs module=%s limit=%s",
				langName, n, took.Seconds(), c.module, lim)
		}
	}
	if c.report {
		report(g, out)
	}
	qs := queries
	if c.metrics {
		qs = metrics
	}
	sel := c.which
	if len(sel) == 0 {
		sel = make([]int, len(qs))
		for i := range sel {
			sel[i] = i + 1
		}
	}
	for _, k := range sel {
		if k < 1 || k > len(qs) {
			continue
		}
		q := qs[k-1]
		out.raw("\n" + strings.Repeat("=", 78) + "\n")
		out.printf("Q%d. %s -- %s", k, q.name, q.title)
		out.raw(strings.Repeat("-", 78) + "\n")
		for line := range strings.SplitSeq(q.notes, "\n") {
			out.raw(" " + line + "\n")
		}
		out.raw("\n")
		r := runQuestion(g, q, c.module, c.limit)
		r.render(out)
	}
	return 0
}

func mustAbs(p string) string {
	a, err := filepath.Abs(p)
	if err != nil {
		return p
	}
	return a
}

func describeDeps(out *output) {
	out.raw("dependencies for codegraph-php:\n")
	out.raw("  [ok    ] tree-sitter CLI             " + tsRuntimeVersion + "   required\n")
	out.raw("             on PATH (or $TREE_SITTER_BIN); every file parses via\n")
	out.raw("             `tree-sitter parse /dev/stdin --scope source.php --cst`\n")
	out.raw("  [ok    ] tree-sitter-php>=0.24         0.24.1   required\n")
	out.raw("             grammar checkout under ~/.cache/codegraph/grammars\n")
	out.raw("             (pinned tag v0.24.1); the CLI builds it -- scanner.c\n")
	out.raw("             included -- and caches the parser; clone the checkout\n")
	out.raw("             at that tag if it is missing\n")
	out.raw("\nnothing to install: parsing runs in the official tree-sitter CLI.\n")
	out.raw("There is no regex fallback, and no state where a missing grammar\n")
	out.raw("silently yields an empty graph that reads like a clean repository.\n")
}

func saveGraph(path string, force bool, g *graph, out *output) error {
	if _, err := os.Lstat(path); err == nil && !force {
		msg := "refusing to overwrite " + path + " (pass --force)"
		if fi, err := os.Lstat(path); err == nil && fi.Mode()&os.ModeSymlink != 0 {
			if rp, err := filepath.EvalSymlinks(path); err == nil {
				msg += " -- it is a symlink to " + rp
			}
		}
		return fmt.Errorf("%s", msg)
	}
	f, err := os.Create(path)
	if err != nil {
		return fmt.Errorf("could not write %s: %s", path, err)
	}
	writeDump(f, g)
	f.Close()
	out.printf("\n(graph also written to %s)", path)
	return nil
}

func parseArgs(argv []string) *cli {
	c := &cli{root: ".", module: "%", limit: -1, workers: -1}
	var pos []string
	i := 0
	need := func(name string) (string, bool) {
		if i+1 >= len(argv) {
			fmt.Fprintf(os.Stderr, "codegraph_php: error: argument %s: expected one argument\n", name)
			return "", false
		}
		i++
		return argv[i], true
	}
	bad := func(name, v string) bool {
		fmt.Fprintf(os.Stderr, "codegraph_php: error: argument %s: invalid int value: %q\n", name, v)
		return true
	}
	for ; i < len(argv); i++ {
		a := argv[i]
		if a == "--" {
			pos = append(pos, argv[i+1:]...)
			break
		}
		if !strings.HasPrefix(a, "-") || a == "-" {
			pos = append(pos, a)
			continue
		}
		name := strings.TrimLeft(a, "-")
		val := ""
		hasVal := false
		if j := strings.IndexByte(name, '='); j >= 0 {
			val, name, hasVal = name[j+1:], name[:j], true
		}
		get := func() (string, bool) {
			if hasVal {
				return val, true
			}
			return need("--" + name)
		}
		switch name {
		case "module":
			v, ok := get()
			if !ok {
				return nil
			}
			c.module = v
		case "limit", "csv", "json", "workers":
			v, ok := get()
			if !ok {
				return nil
			}
			n, err := strconv.Atoi(v)
			if err != nil {
				if bad("--"+name, v) {
					return nil
				}
			}
			switch name {
			case "limit":
				c.limit = n
			case "csv":
				c.csv, c.hasCSV = n, true
			case "json":
				c.json, c.hasJSON = n, true
			case "workers":
				c.workers = n
			}
		case "list":
			c.list = true
		case "metrics":
			c.metrics = true
		case "schema":
			c.schema = true
		case "report":
			c.report = true
		case "save", "dump", "dump-tsv", "cpuprofile", "memprofile":
			v, ok := get()
			if !ok {
				return nil
			}
			switch name {
			case "save":
				c.save = v
			case "dump":
				c.dump = v
			case "dump-tsv":
				c.dumpTSV = v
			case "cpuprofile":
				c.cpuprofile = v
			case "memprofile":
				c.memprofile = v
			}
		case "save-ast", "load-ast":
			v, ok := get()
			if !ok {
				return nil
			}
			if name == "save-ast" {
				c.saveAST = v
			} else {
				c.loadAST = v
			}
		case "force":
			c.force = true
		case "deps":
			c.deps = true
		case "install-deps":
			c.install = true
		case "include-generated":
			c.incGen = true
		case "include-vendored":
			c.incVend = true
		case "no-tests":
			c.noTests = true
		case "quiet":
			c.quiet = true
		case "version":
			c.version = true
		case "help", "h":

			c.help = true
			return c
		default:
			fmt.Fprintf(os.Stderr, "codegraph_php: error: unrecognized argument: %s\n", a)
			return nil
		}
	}
	if len(pos) > 0 {
		c.root = pos[0]
	}
	for _, p := range pos[min(1, len(pos)):] {
		n, err := strconv.Atoi(p)
		if err != nil {
			fmt.Fprintf(os.Stderr, "codegraph_php: error: argument which: invalid int value: %q\n", p)
			return nil
		}
		c.which = append(c.which, n)
	}
	return c
}

func startCPU(f *os.File) {
	startProfiling(f)
}

func stopCPU(f *os.File) { stopProfiling(f) }

func writeMem(path string) {
	f, err := os.Create(path)
	if err != nil {
		return
	}
	writeHeapProfile(f)
	f.Close()
}

var _ = bufio.NewWriter

const helpText = `usage: codegraph_php.py [-h] [--module MODULE] [--limit LIMIT] [--list]
                        [--csv N] [--json N] [--save PATH] [--save-ast PATH]
                        [--load-ast PATH] [--force] [--deps]
                        [--install-deps] [--include-generated]
                        [--include-vendored] [--no-tests] [--quiet]
                        [--version]
                        [root] [which ...]

Parse a php tree into an in-memory graph and query it in one shot. Target: PHP 8.5

positional arguments:
  root                 tree to parse
  which                1-based query numbers

options:
  -h, --help           show this help message and exit
  --module MODULE      module-name LIKE filter
  --limit LIMIT        rows per query; -1 (default) is every row
  --list               list the queries
  --metrics            run/list the METRICS section instead of QUERIES
  --schema             dump the schema
  --report             narrative overview
  --csv N              emit query N as CSV
  --json N             emit query N as JSON
  --save PATH          also write the graph to a file
  --save-ast PATH      parse/build, then write the binary AST state to PATH
  --load-ast PATH      load a saved AST state instead of parsing
  --force              allow --save to overwrite an existing file
  --deps               show dependencies and how to install them
  --install-deps       pip-install the missing dependencies, then continue
  --include-generated  parse generated files too (off by default)
  --include-vendored   parse vendored trees too (off by default)
  --no-tests           skip test files
  --quiet
  --version

every run re-parses from source; nothing is cached, so an answer can never describe code that has moved on
`

const (
	modAbstract = 1 << iota
	modFinal
	modStatic
	modReadonly
	modPublic
	modPrivate
	modProtected
	modVar
)

type classBody struct {
	methods, staticMethods, abstract, publicMethods int32
	props, promoted, readonly, hooks, consts, cases int32
	magic, destruct, wakeup, tostring, invoke       int32
	callmagicCall, callmagicStatic, get             int32
	traitNames                                      []string
}

func (cb classBody) traits() int32 { return int32(len(cb.traitNames)) }
func (cb *classBody) addTrait(s string) {
	cb.traitNames = append(cb.traitNames, s)
}

func (pa *phpParser) classBodyOf(n tsNode) classBody {
	var cb classBody
	body := fieldNode(n, fBody)
	if !hasNode(body) {
		return cb
	}
	for _, c := range namedKids(body) {
		switch kindName(c) {
		case "method_declaration":
			cb.methods++
			mods := pa.modifiers(c)
			if mods&modStatic != 0 {
				cb.staticMethods++
			}
			if mods&modAbstract != 0 || !hasNode(fieldNode(c, fBody)) {
				cb.abstract++
			}
			if mods&modPrivate == 0 && mods&modProtected == 0 {
				cb.publicMethods++
			}
			nm := fieldNode(c, fName)
			name := ""
			if hasNode(nm) {
				name = txt(nm, pa.src)
			}
			switch {
			case magicMethods[name]:
				cb.magic++
			}
			switch name {
			case "__destruct":
				cb.destruct = 1
			case "__wakeup", "__unserialize":
				cb.wakeup = 1
			case "__toString":
				cb.tostring = 1
			case "__call":
				cb.callmagicCall = 1
			case "__callStatic":
				cb.callmagicStatic = 1
			case "__get", "__set":
				cb.get = 1
			case "__invoke":
				cb.invoke = 1
			}
			params := fieldNode(c, fParams)
			if hasNode(params) {
				for _, p := range namedKids(params) {
					if kindName(p) == "property_promotion_parameter" {
						cb.promoted++
						if hasNode(fieldNode(p, fReadonly)) {
							cb.readonly++
						}
					}
				}
			}
		case "property_declaration":
			cb.props++
			if pa.modifiers(c)&modReadonly != 0 {
				cb.readonly++
			}
			for _, x := range namedKids(c) {
				if kindName(x) != "property_hook_list" {
					continue
				}
				for _, h := range namedKids(x) {
					if kindName(h) == "property_hook" {
						cb.hooks++
					}
				}
			}
		case "const_declaration":
			cb.consts++
		case "enum_case":
			cb.cases++
		case "use_declaration":
			for _, x := range namedKids(c) {
				if k := kindName(x); k == "name" || k == "qualified_name" {
					s := strings.TrimLeft(strings.TrimSpace(txt(x, pa.src)), "\\")
					if i := strings.LastIndexByte(s, '\\'); i >= 0 {
						s = s[i+1:]
					}
					cb.addTrait(s)
				}
			}
		}
	}
	return cb
}

func (pa *phpParser) applyFunctionFlags(sid int32, n tsNode, sc scope) {
	rec := pa.rec
	src := pa.src
	name := pa.nodeName(n)
	mods := pa.modifiers(n)
	var nParams, nOpt, nUntyped, nNull, nUnion, nInter, nTyped, nPromoted int32

	params := fieldNode(n, fParams)
	if hasNode(params) {
		for _, p := range namedKids(params) {
			if !paramNodeTypes[kindName(p)] {
				continue
			}
			nParams++
			if kindName(p) == "property_promotion_parameter" {
				nPromoted++
			}
			if hasNode(fieldNode(p, fDefaultValue)) {
				nOpt++
			}
			t := fieldNode(p, fType)
			if !hasNode(t) {
				nUntyped++
				continue
			}
			nTyped++
			switch kindName(t) {
			case "optional_type":
				nNull++
			case "union_type":
				nUnion++
				if strings.Contains(txt(t, src), "null") {
					nNull++
				}
			case "intersection_type":
				nInter++
			case "disjunctive_normal_form_type":
				nUnion++
				nInter++
			}
		}
	}
	if ret := fieldNode(n, fReturnType); hasNode(ret) {
		nTyped++
		switch kindName(ret) {
		case "optional_type":
			nNull++
		case "union_type":
			nUnion++
		case "intersection_type":
			nInter++
		}
	}

	cls := sc.typeName
	attrs := pa.attributeNames(n)
	isRoute := false
	hasOverride, hasDeprecated, isTestAttr := false, false, false
	for _, a := range attrs {
		last := a
		if i := strings.LastIndexByte(last, '\\'); i >= 0 {
			last = last[i+1:]
		}
		if routeAttrRe.MatchString(last) {
			isRoute = true
		}
		if last == "Override" {
			hasOverride = true
		}
		if last == "Deprecated" {
			hasDeprecated = true
		}
		if last == "Test" || last == "DataProvider" {
			isTestAttr = true
		}
	}
	ctrl := controllerPathRe.MatchString(rec.rel) ||
		strings.HasSuffix(cls, "Controller") || strings.HasSuffix(cls, "Action") ||
		strings.HasSuffix(cls, "Endpoint")
	model := modelPathRe.MatchString(rec.rel) ||
		strings.HasSuffix(rec.extends[cls], "Model") ||
		strings.HasSuffix(rec.extends[cls], "Entity") ||
		strings.HasSuffix(rec.extends[cls], "ActiveRecord")
	vis := pa.visibilityOf(n)
	entry := entryFileRe.MatchString(rec.rel) || isRoute ||
		(ctrl && vis == "public") ||
		((name == "handle" || name == "__invoke" || name == "execute" ||
			name == "run" || name == "main") &&
			(strings.HasSuffix(cls, "Command") || strings.HasSuffix(cls, "Job") ||
				strings.HasSuffix(cls, "Middleware") || strings.HasSuffix(cls, "Listener") ||
				strings.HasSuffix(cls, "Handler") || strings.HasSuffix(cls, "Controller")))
	docDep := false
	for prev := prevSibling(n); hasNode(prev) && kComments[slot(kindID(prev))]; prev = prevSibling(prev) {
		if strings.Contains(txt(prev, src), "@deprecated") {
			docDep = true
			break
		}
	}

	rec.set(cNParams, sid, nParams)
	rec.set(cNOptionalParams, sid, nOpt)
	rec.set(cIsPublic, sid, b2i(vis == "public"))
	rec.set(cIsAbstract, sid, b2i(mods&modAbstract != 0 || !hasNode(fieldNode(n, fBody))))
	rec.set(cIsOverride, sid, b2i(hasOverride))
	rec.set(cIsDeprecated, sid, b2i(hasDeprecated || docDep))
	rec.set(cIsTest, sid, b2i(strings.HasPrefix(name, "test") || isTestAttr))
	rec.set(cIsEntrypoint, sid, b2i(entry))
	rec.set(cIsController, sid, b2i(ctrl))
	rec.set(cIsModel, sid, b2i(model))

	rec.set(cHasStrictTypes, sid, 0)
	rec.set(cNMagicMethod, sid, b2i(magicMethods[name]))
	rec.set(cNDestruct, sid, b2i(name == "__destruct"))
	rec.set(cNWakeup, sid, b2i(name == "__wakeup" || name == "__unserialize"))
	rec.set(cNToString, sid, b2i(name == "__toString"))
	rec.set(cNCallMagic, sid, b2i(name == "__call" || name == "__callStatic"))
	rec.set(cNUntypedParams, sid, nUntyped)
	rec.set(cNNullableTypes, sid, nNull)
	rec.set(cNUnionTypes, sid, nUnion)
	rec.set(cNIntersectionTypes, sid, nInter)
	rec.set(cNTypeDeclarations, sid, nTyped)
	rec.setS(cClassName, sid, clip(cls, 120))
}

func (pa *phpParser) applyTypeFlags(sid int32, n tsNode) {
	rec := pa.rec
	cb := pa.classBodyOf(n)
	mods := pa.modifiers(n)
	rec.set(cIsPublic, sid, 1)
	rec.set(cIsAbstract, sid, b2i(mods&modAbstract != 0))
	rec.set(cNMagicMethod, sid, cb.magic)
	rec.set(cNDestruct, sid, cb.destruct)
	rec.set(cNWakeup, sid, cb.wakeup)
	rec.set(cNToString, sid, cb.tostring)
	rec.set(cNCallMagic, sid, cb.callmagicCall+cb.callmagicStatic)
	rec.set(cHasStrictTypes, sid, 0)
	rec.setS(cClassName, sid, clip(pa.nodeName(n), 120))
}

func (pa *phpParser) functionExtra(n tsNode, sid int32, sc scope) {
	rec := pa.rec
	name := pa.nodeName(n)
	cls := sc.typeName
	ns := pa.namespaceAt(startByte(n))
	rec.fnSid[uint64(rec.fid)<<32|uint64(startByte(n))] = sid

	t := kindName(n)
	if cls != "" && t == "method_declaration" {
		rec.byQual[cls+"::"+name] = sid
		if ns != "" {
			rec.byQual[ns+"\\"+cls+"::"+name] = sid
		}
	} else if t == "function_definition" && ns != "" {
		rec.byQual[ns+"\\"+name] = sid
	}

	parentCls := rec.extends[cls]
	for i := len(rec.pend) - 1; i >= 0 && rec.pend[i].sym == sid; i-- {
		rec.pend[i].typ = pa.pool.name(receiverType(rec.pend[i].name, cls, parentCls))
	}

	if t == "method_declaration" && magicMethods[name] {
		rec.magic = append(rec.magic, magicRow{
			sym: sid, classID: sc.typeID, fileID: rec.fid, className: pa.put(clip(cls, 120)),
			method: pa.put(name), isGadget: gadgetMethods[name], bodySLOC: pa.slocOf(n),
			line: int32(startRow(n)) + 1,
		})
	} else if t == "property_hook" {
		body := fieldNode(n, fBody)
		hook := ""
		for _, c := range namedKids(n) {
			if kindName(c) == "name" {
				hook = txt(c, pa.src)
				break
			}
		}
		if hook == "" {
			hook = "?"
		}
		rec.hooks = append(rec.hooks, hookRow{
			sym: sid, classID: sc.typeID, fileID: rec.fid, className: pa.put(clip(cls, 120)),
			property: pa.put(clip(pa.hookProperty(n), 120)), hook: pa.put(hook),
			isShort:   hasNode(body) && kindName(body) != "compound_statement",
			isVirtual: pa.hookIsVirtual(n, body),
			bodySLOC:  pa.slocOf(n), line: int32(startRow(n)) + 1,
		})
	}
}

func receiverType(raw, cls, parentCls string) string {
	switch {
	case strings.HasPrefix(raw, "->"):
		return cls
	case strings.HasPrefix(raw, "new "):
		raw = raw[4:]
	}
	if i := strings.Index(raw, "::"); i >= 0 {
		head := raw[:i]
		switch head {
		case "self", "static":
			return cls
		case "parent":
			return parentCls
		}
		if j := strings.LastIndexByte(head, '\\'); j >= 0 {
			return head[j+1:]
		}
		return head
	}
	return ""
}

func (pa *phpParser) typeExtra(n tsNode, sid int32, kind string) {
	rec := pa.rec
	name := pa.nodeName(n)
	if name == "" {
		name = "(anonymous)"
	}
	ns := pa.namespaceAt(startByte(n))
	rec.fnSid[uint64(rec.fid)<<32|uint64(startByte(n))] = sid
	cb := pa.classBodyOf(n)
	body := fieldNode(n, fBody)

	extends := ""
	var implements []string
	for _, ch := range namedKids(n) {
		switch kindName(ch) {
		case "base_clause":
			var parts []string
			for _, x := range namedKids(ch) {
				if k := kindName(x); k == "name" || k == "qualified_name" {
					parts = append(parts, strings.TrimLeft(strings.TrimSpace(txt(x, pa.src)), "\\"))
				}
			}
			extends = strings.Join(parts, ",")
		case "class_interface_clause":
			for _, x := range namedKids(ch) {
				if k := kindName(x); k == "name" || k == "qualified_name" {
					implements = append(implements, strings.TrimLeft(strings.TrimSpace(txt(x, pa.src)), "\\"))
				}
			}
		}
	}
	if extends != "" {
		first := extends
		if i := strings.IndexByte(first, ','); i >= 0 {
			first = first[:i]
		}
		if j := strings.LastIndexByte(first, '\\'); j >= 0 {
			first = first[j+1:]
		}
		rec.extends[name] = first
	}
	mods := pa.modifiers(n)
	if kindName(n) == "trait_declaration" {
		rec.traits = append(rec.traits, traitRow{
			sym: sid, fileID: rec.fid, name: pa.put(clip(name, 160)), ns: pa.put(clip(ns, 200)),
			nMethods: cb.methods, nAbstract: cb.abstract, nProps: cb.props,
			line: int32(startRow(n)) + 1,
		})
	}
	fqn := name
	if ns != "" {
		fqn = ns + "\\" + name
	}
	rec.classes = append(rec.classes, classRow{
		sym: sid, fileID: rec.fid, name: pa.put(clip(name, 160)), fqn: pa.put(clip(fqn, 300)),
		ns: pa.put(clip(ns, 200)), kind: pa.put(kind), ext: pa.put(clip(extends, 200)),
		impl:      pa.put(clip(strings.Join(implements, ","), 300)),
		traitList: pa.put(clip(strings.Join(cb.traitNames, ","), 300)),
		nTraits:   cb.traits(), nMethods: cb.methods, nPub: cb.publicMethods,
		nStatic: cb.staticMethods, nProps: cb.props, nPromoted: cb.promoted,
		nHooks: cb.hooks, nConsts: cb.consts, nCases: cb.cases, nMagic: cb.magic,
		isAbstract: mods&modAbstract != 0, isFinal: mods&modFinal != 0,
		isReadonly:  mods&modReadonly != 0,
		isAnon:      kindName(n) == "anonymous_class",
		hasDestruct: cb.destruct == 1, hasWakeup: cb.wakeup == 1, hasToStr: cb.tostring == 1,
		hasCall: cb.callmagicCall == 1, hasCallStatic: cb.callmagicStatic == 1,
		hasGet: cb.get == 1, hasInvoke: cb.invoke == 1,
		line: int32(startRow(n)) + 1,
	})
	if hasNode(body) {
		for i, f := range pa.classFields(body) {
			rec.fields = append(rec.fields, f.toRow(sid, int32(i), &rec.sa))
		}
	}
}

type classField struct {
	name, typ, vis string
	line           int32
	static, konst  bool
	mutable        bool
}

func (f classField) toRow(sid, ord int32, a *strArena) fieldRow {
	lo := strings.ToLower(f.typ)
	return fieldRow{
		sym: sid, ordinal: ord, name: a.put(clip(f.name, 120)), typ: a.put(clip(f.typ, 200)), vis: a.put(f.vis),
		line: f.line, isStatic: f.static, isConst: f.konst, mut: f.mutable,
		null:      strings.HasPrefix(f.typ, "?") || strings.Contains(lo, "null"),
		coll:      strings.Contains(lo, "array") || strings.Contains(lo, "iterable"),
		untyped:   f.typ == "",
		typeDepth: int32(strings.Count(f.typ, "|") + strings.Count(f.typ, "&")),
	}
}

func (pa *phpParser) classFields(body tsNode) []classField {
	var out []classField
	for _, c := range namedKids(body) {
		switch kindName(c) {
		case "property_declaration":
			mods := pa.modifiers(c)
			vis := "public"
			switch {
			case mods&modPublic != 0:
				vis = "public"
			case mods&modPrivate != 0:
				vis = "private"
			case mods&modProtected != 0:
				vis = "protected"
			}
			tn := fieldNode(c, fType)
			ftype := ""
			if hasNode(tn) {
				ftype = strings.TrimSpace(txt(tn, pa.src))
			}
			for _, el := range namedKids(c) {
				if kindName(el) != "property_element" {
					continue
				}
				nm := fieldNode(el, fName)
				name := ""
				if hasNode(nm) {
					name = strings.TrimLeft(txt(nm, pa.src), "$")
				}
				out = append(out, classField{name: name, typ: ftype, vis: vis,
					line: int32(startRow(c)) + 1, static: mods&modStatic != 0,
					konst: false, mutable: mods&modReadonly == 0})
			}
		case "const_declaration":
			tn := fieldNode(c, fType)
			ftype := ""
			if hasNode(tn) {
				ftype = strings.TrimSpace(txt(tn, pa.src))
			}
			for _, el := range namedKids(c) {
				if kindName(el) != "const_element" {
					continue
				}
				kids := namedKids(el)
				name := ""
				if len(kids) > 0 {
					name = txt(kids[0], pa.src)
				}
				out = append(out, classField{name: name, typ: ftype, vis: "public",
					line: int32(startRow(c)) + 1, static: true, konst: true})
			}
		case "method_declaration":
			params := fieldNode(c, fParams)
			if !hasNode(params) {
				continue
			}
			for _, p := range namedKids(params) {
				if kindName(p) != "property_promotion_parameter" {
					continue
				}
				nm := fieldNode(p, fName)
				name := ""
				if hasNode(nm) {
					name = strings.TrimLeft(txt(nm, pa.src), "$")
				}
				tn := fieldNode(p, fType)
				ptype := ""
				if hasNode(tn) {
					ptype = strings.TrimSpace(txt(tn, pa.src))
				}
				vn := fieldNode(p, fVisibility)
				vis := "public"
				if hasNode(vn) {
					v := txt(vn, pa.src)
					if i := strings.IndexByte(v, '('); i >= 0 {
						v = v[:i]
					}
					vis = v
				}
				out = append(out, classField{name: name, typ: ptype, vis: vis,
					line:    int32(startRow(p)) + 1,
					mutable: !hasNode(fieldNode(p, fReadonly))})
			}
		}
	}
	return out
}

func (pa *phpParser) hookProperty(hook tsNode) string {
	cur := parentNode(hook)
	for hasNode(cur) && kindName(cur) != "property_declaration" {
		cur = parentNode(cur)
	}
	if !hasNode(cur) {
		return ""
	}
	for _, c := range namedKids(cur) {
		if kindName(c) == "property_element" {
			nm := fieldNode(c, fName)
			if hasNode(nm) {
				return strings.TrimLeft(txt(nm, pa.src), "$")
			}
		}
	}
	return ""
}

func (pa *phpParser) hookIsVirtual(hook tsNode, body tsNode) bool {
	prop := pa.hookProperty(hook)
	if prop == "" {
		return false
	}
	if !hasNode(body) {
		return false
	}
	return !strings.Contains(txt(body, pa.src), "$this->"+prop)
}

const (
	tsRuntimeVersion = "0.27.0"
	tsGrammarVersion = "0.24.1"
)

type output struct {
	w   *bufio.Writer
	ew  *bufio.Writer
	csv bool
}

func newOutput() *output {
	return &output{w: bufio.NewWriterSize(os.Stdout, 1<<16), ew: bufio.NewWriterSize(os.Stderr, 1<<16)}
}

func (o *output) printf(f string, a ...any) {
	if o.csv {
		return
	}
	fmt.Fprintf(o.w, f+"\n", a...)
}

func (o *output) warnf(f string, a ...any) {
	if o.csv {
		return
	}
	fmt.Fprintf(o.ew, f+"\n", a...)
}

func (o *output) raw(s string) { o.w.WriteString(s) }
func (o *output) flush()       { o.w.Flush(); o.ew.Flush() }

func sprintf(f string, a ...any) string { return fmt.Sprintf(f, a...) }
func fmtInt(v int) string               { return strconv.Itoa(v) }

func parseWorkers() int {
	if v := os.Getenv("CODEGRAPH_WORKERS"); v != "" {
		if n, err := strconv.Atoi(v); err == nil && n > 0 {
			return n
		}
	}
	return defaultParseWorkers
}

func runtimeVersion() string {
	if bi, ok := debug.ReadBuildInfo(); ok {
		return bi.Main.Version
	}
	return runtime.Version()
}

func nowStamp() string { return time.Now().Format("2006-01-02T15:04:05") }

func cgFloat(f float64) string {
	if f != f || f > 1.7e308 || f < -1.7e308 {
		return "inf"
	}
	if f == 0 {
		return "0.0"
	}
	neg := false
	if f < 0 {
		neg = true
		f = -f
	}

	mant := strconv.FormatFloat(f, 'e', -1, 64)
	e := strings.IndexByte(mant, 'e')
	exp, _ := strconv.Atoi(mant[e+1:])
	digits := strings.Replace(mant[:e], ".", "", 1)

	decpt := exp + 1
	var out string
	if decpt > 16 || decpt < -3 {
		out = digits[:1]
		if len(digits) > 1 {
			out += "." + digits[1:]
		}
		out += "e" + fmtExp(exp)
	} else if exp >= 0 {
		if len(digits) <= exp+1 {
			out = digits + strings.Repeat("0", exp+1-len(digits)) + ".0"
		} else {
			out = digits[:exp+1] + "." + digits[exp+1:]
		}
	} else {
		out = "0." + strings.Repeat("0", -exp-1) + digits
	}
	if neg {
		return "-" + out
	}
	return out
}

func fmtExp(e int) string {
	s := strconv.Itoa(e)
	sign := "+"
	if e < 0 {
		sign = "-"
		s = s[1:]
	}
	s = strings.TrimLeft(s, "0")
	for len(s) < 2 {
		s = "0" + s
	}
	return sign + s
}

type jnode struct {
	m    map[string]*jnode
	list []*jnode
	val  string
}

func (n *jnode) str(path ...string) string {
	cur := n
	for _, p := range path {
		if cur == nil || cur.m == nil {
			return ""
		}
		cur = cur.m[p]
	}
	if cur == nil {
		return ""
	}
	return cur.val
}

func (n *jnode) obj(path ...string) *jnode {
	cur := n
	for _, p := range path {
		if cur == nil || cur.m == nil {
			return nil
		}
		cur = cur.m[p]
	}
	return cur
}

func simpleJSONObject(b []byte) *jnode {
	p := &jsonParser{b: b}
	p.ws()
	v := p.value()
	if v == nil {
		return nil
	}
	return v
}

type jsonParser struct {
	b []byte
	i int
}

func (p *jsonParser) ws() {
	for p.i < len(p.b) {
		switch p.b[p.i] {
		case ' ', '\t', '\n', '\r':
			p.i++
		default:
			return
		}
	}
}

func (p *jsonParser) value() *jnode {
	p.ws()
	if p.i >= len(p.b) {
		return nil
	}
	switch c := p.b[p.i]; {
	case c == '{':
		p.i++
		n := &jnode{m: map[string]*jnode{}}
		for {
			p.ws()
			if p.i >= len(p.b) {
				return n
			}
			if p.b[p.i] == '}' {
				p.i++
				return n
			}
			if p.b[p.i] == ',' {
				p.i++
				continue
			}
			k := p.str()
			p.ws()
			if p.i < len(p.b) && p.b[p.i] == ':' {
				p.i++
			}
			n.m[k] = p.value()
		}
	case c == '[':
		p.i++
		n := &jnode{}
		for {
			p.ws()
			if p.i >= len(p.b) {
				return n
			}
			if p.b[p.i] == ']' {
				p.i++
				return n
			}
			if p.b[p.i] == ',' {
				p.i++
				continue
			}
			n.list = append(n.list, p.value())
		}
	case c == '"':
		return &jnode{val: p.str()}
	default:
		for p.i < len(p.b) {
			ch := p.b[p.i]
			if ch == ',' || ch == '}' || ch == ']' || ch == ' ' || ch == '\n' || ch == '\t' || ch == '\r' {
				break
			}
			p.i++
		}
		return &jnode{val: "true"}
	}
}

func (p *jsonParser) str() string {
	p.ws()
	if p.i >= len(p.b) || p.b[p.i] != '"' {
		return ""
	}
	p.i++
	var sb strings.Builder
	for p.i < len(p.b) {
		c := p.b[p.i]
		if c == '"' {
			p.i++
			return sb.String()
		}
		if c == '\\' && p.i+1 < len(p.b) {
			p.i++
			switch p.b[p.i] {
			case 'n':
				sb.WriteByte('\n')
			case 't':
				sb.WriteByte('\t')
			case 'r':
				sb.WriteByte('\r')
			case 'u':
				if p.i+4 < len(p.b) {
					if v, err := strconv.ParseUint(string(p.b[p.i+1:p.i+5]), 16, 32); err == nil {
						sb.WriteRune(rune(v))
					}
					p.i += 4
				}
			default:
				sb.WriteByte(p.b[p.i])
			}
			p.i++
			continue
		}
		sb.WriteByte(c)
		p.i++
	}
	return sb.String()
}

var debugParse = os.Getenv("CODEGRAPH_DEBUG") != ""

var defaultParseWorkers = 2 * runtime.GOMAXPROCS(0)

const (
	gcCeilingSlack = 1.10

	gcCeilingPerSource = 4.5

	gcCeilingFloor = 96 << 20
)

var (
	gcCeilingRatio = envFloat("CODEGRAPH_GC_SLACK", 0)
	gcCeilingSeed  = envFloat("CODEGRAPH_GC_SEED", 0)
	gcTuneOff      = os.Getenv("CODEGRAPH_GC_OFF") != ""
	gcTrace        = os.Getenv("CODEGRAPH_GC_TRACE") != ""
)

func envFloat(name string, def float64) float64 {
	if s := os.Getenv(name); s != "" {
		if v, err := strconv.ParseFloat(s, 64); err == nil {
			return v / 100
		}
	}
	return def
}

var ceilingNow atomic.Int64

func tuneGC(sourceBytes int64) func() {
	if gcTuneOff {
		return func() {}
	}
	slack := gcCeilingSlack
	if gcCeilingRatio > 0 {
		slack = gcCeilingRatio
	}
	perSource := gcCeilingPerSource
	if gcCeilingSeed > 0 {
		perSource = gcCeilingSeed
	}
	seed := int64(float64(sourceBytes) * perSource)
	if seed < gcCeilingFloor {
		seed = gcCeilingFloor
	}
	prev := debug.SetMemoryLimit(seed)
	ceilingNow.Store(seed)
	stop := make(chan struct{})
	done := make(chan struct{})
	go func() {
		defer close(done)
		var ms runtime.MemStats
		var lastGC uint32
		for {
			select {
			case <-stop:
				return
			case <-time.After(10 * time.Millisecond):
			}
			runtime.ReadMemStats(&ms)
			if ms.NumGC == lastGC {
				continue
			}
			lastGC = ms.NumGC

			want := int64(float64(ms.HeapAlloc)*slack) + gcCeilingFloor/4
			if want > ceilingNow.Load() {
				ceilingNow.Store(want)
				debug.SetMemoryLimit(want)
				if gcTrace {
					println("gc-tune live", ms.HeapAlloc>>20, "MB  ceiling", want>>20, "MB")
				}
			}
		}
	}()
	return func() {
		close(stop)
		<-done
		debug.SetMemoryLimit(prev)
	}
}

func strconvFormatInt(v int64) string { return strconv.FormatInt(v, 10) }

func startProfiling(w io.Writer) { pprof.StartCPUProfile(w) }
func stopProfiling(w io.Writer)  { pprof.StopCPUProfile() }

func writeHeapProfile(w io.Writer) {
	runtime.GC()
	pprof.Lookup("allocs").WriteTo(w, 0)
}

var peakStop atomic.Bool

func startPeakSampler(path string) {
	if path == "" {
		return
	}
	go func() {
		var ms runtime.MemStats
		var best uint64
		for !peakStop.Load() {
			runtime.ReadMemStats(&ms)
			if ms.HeapAlloc > best {
				best = ms.HeapAlloc
				if f, err := os.Create(path); err == nil {

					pprof.Lookup("allocs").WriteTo(f, 0)
					f.Close()
				}
			}
			time.Sleep(2 * time.Millisecond)
		}
	}()
}

func stopPeakSampler() { peakStop.Store(true) }

func startContentionProfiling() func() {
	var closers []func()
	if p := os.Getenv("CODEGRAPH_BLOCKPROF"); p != "" {
		runtime.SetBlockProfileRate(1)
		runtime.SetMutexProfileFraction(1)
		closers = append(closers, func() {
			for _, kind := range []string{"block", "mutex"} {
				prof := pprof.Lookup(kind)
				f, err := os.Create(p + "." + kind)
				if err != nil {
					continue
				}
				n := 0
				if prof != nil {
					n = prof.Count()
					prof.WriteTo(f, 0)
				}
				f.Close()
				fmt.Fprintf(os.Stderr, "codegraph-php: %s profile: %d samples -> %s\n",
					kind, n, f.Name())
			}
		})
	}
	if p := os.Getenv("CODEGRAPH_TRACE"); p != "" {
		f, err := os.Create(p)
		if err == nil {
			if err := trace.Start(f); err == nil {
				closers = append(closers, func() {
					trace.Stop()
					f.Close()
					fmt.Fprintf(os.Stderr, "codegraph-php: execution trace -> %s\n", f.Name())
				})
			} else {
				f.Close()
			}
		}
	}
	if os.Getenv("CODEGRAPH_GOROUTINES") != "" {
		closers = append(closers, func() {
			fmt.Fprintf(os.Stderr, "codegraph-php: %d goroutines at exit\n", runtime.NumGoroutine())
		})
	}
	return func() {
		for _, closer := range slices.Backward(closers) {
			closer()
		}
	}
}

var phpExts = map[string]bool{
	".php": true, ".phtml": true, ".php5": true, ".php7": true,
	".phps": true, ".module": true, ".inc": true,
}

var skipDirs = map[string]bool{}

func init() {
	base := []string{
		".git", ".hg", ".svn", ".jj", ".idea", ".vscode", ".vs", ".claude",
		"node_modules", "bower_components", "vendor", "third_party", "thirdparty",
		"external", "externals", "deps", "Godeps", "_vendor",
		"__pycache__", ".mypy_cache", ".pytest_cache", ".ruff_cache", ".tox",
		".venv", "venv", "env", ".env", "virtualenv",
		"build", "_build", "dist", "out", "target", "bin", "obj", ".gradle",
		".next", ".nuxt", ".svelte-kit", ".parcel-cache", ".turbo", ".cache",
		"coverage", "htmlcov", ".nyc_output", "site-packages",
	}
	for _, d := range base {
		skipDirs[d] = true
	}
	for _, d := range []string{"vendor", "storage", "bootstrap/cache", "public/build"} {
		skipDirs[d] = true
	}
}

var (
	testPathRe = regexp.MustCompile(`(?i)(^|/)(tests?|test-d|spec|specs|__tests__|__snapshots__|testing|` +
		`e2e|integration[-_]tests?|testdata|test_data|test-data|` +
		`fixtures?)(/|$)`)
	testNameRe = regexp.MustCompile(`(Test\.php$|^test_)`)
	genNameRe  = regexp.MustCompile(`(?i)(\.min\.|\.bundle\.|[-_.](gen|generated|pb|g)\.|_pb2|\.g\.dart$` +
		`|\.designer\.|^zz_generated)`)
	vendorRe = regexp.MustCompile(`(?i)(^|/)(vendor|third_party|thirdparty|external|node_modules|deps)(/|$)`)
	exRe     = regexp.MustCompile(`(?i)(^|/)(examples?|samples?|demos?)(/|$)`)
	toolRe   = regexp.MustCompile(`(?i)(^|/)(tools?|scripts?|cmd|bin)(/|$)`)
	markerRe = regexp.MustCompile(`(?i)\b(TODO|FIXME|XXX|HACK|BUG|NOTE|WARNING|OPTIMIZE|REVIEW|DEPRECATED|` +
		`SAFETY|PANIC|UNSAFE)\b[ \t]*[:\-(]`)
)

var generatedMarkers = []string{
	"@generated", "DO NOT EDIT", "Code generated by", "AUTO-GENERATED",
	"autogenerated", "This file was automatically generated",
	"Generated by the protocol buffer compiler", "@flow-generated",
}

const (
	maxFileBytes = 4 * 1024 * 1024
	maxLineBytes = 1024 * 1024
)

func moduleOf(rel string) string {
	parts := strings.Split(rel, "/")
	if len(parts) <= 1 {
		return "(root)"
	}
	head := parts[:len(parts)-1]
	switch head[0] {
	case "src", "lib", "source", "internal", "pkg", "app":
		if len(head) > 3 {
			head = head[:3]
		}
	default:
		if len(head) > 2 {
			head = head[:2]
		}
	}
	return strings.Join(head, "/")
}

func moduleKind(name string) string {
	switch {
	case testPathRe.MatchString(name):
		return "test"
	case vendorRe.MatchString(name):
		return "vendor"
	case exRe.MatchString(name):
		return "example"
	case toolRe.MatchString(name):
		return "tool"
	}
	return "source"
}

type discovered struct {
	recs      []fileRec
	skipped   skipCounts
	modByName map[string]int32

	sourceBytes int64
}

type skipCounts struct{ big, special, escape, denied, walkErr int }

type fileRec struct {
	id       int32
	moduleID int32
	rel      string
	abspath  string
	lang     string
	isTest   bool
	isGen    bool
	isVend   bool

	size int64
}

func discover(root string, g *graph, includeTests, includeGen, includeVend bool, quiet bool, out *output) *discovered {
	d := &discovered{modByName: make(map[string]int32)}
	realRoot, _ := filepath.EvalSymlinks(root)
	if realRoot == "" {
		realRoot = root
	}
	walkDir(root, root, realRoot, d, g, includeTests, includeGen, includeVend)
	if !quiet {
		for _, p := range []struct {
			n   int
			why string
		}{
			{d.skipped.big, "too large or with a pathologically long line -- catalogued, not parsed"},
			{d.skipped.special, "not regular files (fifo, socket, device) -- skipped"},
			{d.skipped.escape, "symlinks pointing OUTSIDE the tree -- skipped"},
			{d.skipped.denied, "unreadable (permission denied)"},
			{d.skipped.walkErr, "director(ies) could not be listed"},
		} {
			if p.n != 0 {
				out.printf("  %d %s", p.n, p.why)
			}
		}
	}
	g.setMeta("files_skipped", sprintf("big=%d special=%d escaping_symlink=%d denied=%d walk_errors=%d",
		d.skipped.big, d.skipped.special, d.skipped.escape, d.skipped.denied, d.skipped.walkErr))
	return d
}

func walkDir(root, dir, realRoot string, d *discovered, g *graph, incT, incG, incV bool) {
	ents, err := os.ReadDir(dir)
	if err != nil {
		d.skipped.walkErr++
		return
	}
	sort.Slice(ents, func(i, j int) bool { return ents[i].Name() < ents[j].Name() })
	var files, dirs []fs.DirEntry
	for _, e := range ents {
		if e.IsDir() {
			dirs = append(dirs, e)
			continue
		}
		files = append(files, e)
	}

	for _, e := range files {
		ext := filepath.Ext(e.Name())
		if !phpExts[ext] {
			continue
		}
		abs := filepath.Join(dir, e.Name())
		rel := relSlash(abs, root)
		st, err := os.Stat(abs)
		if err != nil {
			continue
		}
		if !st.Mode().IsRegular() {
			d.skipped.special++
			continue
		}
		if rp, err := filepath.EvalSymlinks(abs); err == nil && rp != abs {
			if !strings.HasPrefix(rp, realRoot+string(os.PathSeparator)) {
				d.skipped.escape++
				continue
			}
		}
		tooBig := false
		var data []byte
		if st.Size() > maxFileBytes {
			d.skipped.big++
			tooBig = true
		} else {
			data, err = os.ReadFile(abs)
			if err != nil {
				if os.IsPermission(err) {
					d.skipped.denied++
				}
				continue
			}
			if longestLine(data) > maxLineBytes {
				d.skipped.big++
				tooBig = true
			}
		}

		lines := cgSplitLinesB(decodeReplaceB(data))
		head := data
		if len(head) > 2000 {
			head = head[:2000]
		}
		blank, sloc, cmt, maxLine := countLines(lines)
		sum := ""
		if len(data) > 0 {
			h := sha1.Sum(data)
			sum = hex.EncodeToString(h[:])
		}
		isTest := testPathRe.MatchString(rel) || testNameRe.MatchString(e.Name())
		isGen := genNameRe.MatchString(e.Name()) || hasGeneratedMarker(string(head))
		isVend := vendorRe.MatchString(rel)
		modName := moduleOf(rel)
		mid, ok := d.modByName[modName]
		if !ok {
			mid = int32(len(g.mods)) + 1
			g.mods = append(g.mods, moduleRow{id: mid, name: g.sa.put(modName), kind: g.sa.put(moduleKind(modName))})
			d.modByName[modName] = mid
		}
		parse := !tooBig && len(data) > 0 &&
			(incT || !isTest) && (incG || !isGen) && (incV || !isVend)
		relOut, fnOut := rel, e.Name()
		if !isASCII(rel) {
			relOut = replaceInvalidUTF8(rel)
			fnOut = replaceInvalidUTF8(fnOut)
		}
		fid := int32(len(g.fils)) + 1
		g.fils = append(g.fils, fileRow{
			id: fid, path: g.sa.put(relOut), dir: g.sa.put(dirOrDot(relOut)), base: g.sa.put(fnOut), ext: g.sa.put(ext),
			lang: g.sa.put("php"), moduleID: mid, bytes: int32(st.Size()), lines: int32(len(lines)),
			sloc: sloc, blank: blank, comment: cmt, maxLine: maxLine, sha1: g.sa.put(sum),
			parsed: b2i(parse), isTest: b2i(isTest), isGen: b2i(isGen), isVend: b2i(isVend),
		})
		if parse {

			d.sourceBytes += st.Size()
			d.recs = append(d.recs, fileRec{id: fid, moduleID: mid, rel: relOut,
				abspath: abs, lang: "php", isTest: isTest, isGen: isGen, isVend: isVend,
				size: st.Size()})
		}
	}
	for _, e := range dirs {
		name := e.Name()
		if skipDirs[name] || strings.HasPrefix(name, ".") {
			continue
		}
		walkDir(root, filepath.Join(dir, name), realRoot, d, g, incT, incG, incV)
	}
}

func dirOrDot(rel string) string {
	if i := strings.LastIndexByte(rel, '/'); i >= 0 {
		return rel[:i]
	}
	return "."
}

func relSlash(abs, root string) string {
	r, err := filepath.Rel(root, abs)
	if err != nil {
		return abs
	}
	return r
}

func hasGeneratedMarker(head string) bool {
	for _, m := range generatedMarkers {
		if strings.Contains(head, m) {
			return true
		}
	}
	return false
}

func b2i(b bool) int32 {
	if b {
		return 1
	}
	return 0
}

func longestLine(data []byte) int {
	longest, start := 0, 0
	for {
		i := bytesIndexByte(data, '\n', start)
		if i < 0 {
			if len(data)-start > longest {
				longest = len(data) - start
			}
			return longest
		}
		if i-start > longest {
			longest = i - start
		}
		start = i + 1
	}
}

func bytesIndexByte(b []byte, c byte, from int) int {
	for i := from; i < len(b); i++ {
		if b[i] == c {
			return i
		}
	}
	return -1
}

func decodeReplaceB(b []byte) []byte {
	if utf8.Valid(b) {
		return b
	}
	out := make([]byte, 0, len(b)+8)
	for i := 0; i < len(b); {
		r, size := utf8.DecodeRune(b[i:])
		if r == utf8.RuneError && size <= 1 {
			out = utf8.AppendRune(out, 0xFFFD)
			i++
			continue
		}
		out = append(out, b[i:i+size]...)
		i += size
	}
	return out
}

func isASCII(s string) bool {
	for i := 0; i < len(s); i++ {
		if s[i] >= 0x80 {
			return false
		}
	}
	return true
}

func replaceInvalidUTF8(s string) string {
	var b strings.Builder
	for i := 0; i < len(s); {
		r, size := utf8.DecodeRuneInString(s[i:])
		if r == utf8.RuneError && size <= 1 {
			b.WriteByte('?')
			i++
			continue
		}
		b.WriteString(s[i : i+size])
		i += size
	}
	return b.String()
}

func cgSplitLinesB(s []byte) [][]byte {
	return cgSplitLinesInto(nil, s)
}

func cgSplitLinesInto(out [][]byte, s []byte) [][]byte {
	out = out[:0]
	if cap(out) < bytes.Count(s, []byte{'\n'})+4 {
		out = make([][]byte, 0, bytes.Count(s, []byte{'\n'})+4)
	}
	start := 0
	for i := 0; i < len(s); i++ {
		c := s[i]
		if c < utf8.RuneSelf {
			if !isPyBreak(c) {
				continue
			}
			out = append(out, s[start:i:i])
			if c == '\r' && i+1 < len(s) && s[i+1] == '\n' {
				i++
			}
			start = i + 1
			continue
		}
		r, size := utf8.DecodeRune(s[i:])
		if r != 0x2028 && r != 0x2029 && r != 0x85 {
			i += size - 1
			continue
		}
		out = append(out, s[start:i:i])
		i += size - 1
		start = i + 1
	}
	if start < len(s) {
		out = append(out, s[start:])
	}
	return out
}

func isPyBreak(c byte) bool {
	switch c {
	case '\n', '\r', '\v', '\f', 0x1c, 0x1d, 0x1e:
		return true
	}
	return false
}

var cmtPrefixes = []string{"//", "#", "/*", "*", "*/", `"""`, "'''", "--", ";;", "%"}

func countLines(lines [][]byte) (blank, sloc, cmt, maxLine int32) {
	for _, l := range lines {
		s := bytes.TrimSpace(l)
		if len(s) != 0 {
			sloc++

			p := s
			if len(p) > 3 {
				p = p[:3]
			}
			if slices.Contains(cmtPrefixes, string(p)) {
				cmt++
			}
		} else {
			blank++
		}
		if n := int32(utf8.RuneCount(l)); n > maxLine {
			maxLine = n
		}
	}
	return
}

const tsScope = "source.php"

const (
	tsFlagMiss   = 1
	tsFlagErr    = 2
	tsFlagNamed  = 8
	tsSymInvalid = 0xFFFF
)

type tsRec struct {
	sym, field     uint16
	start, end     uint32
	srow, erow     uint16
	parent, subEnd int32
	nchild, nnamed uint16
	flags          uint8
}

func tsCLIBin() string {
	if b := os.Getenv("TREE_SITTER_BIN"); b != "" {
		return b
	}

	if home, err := os.UserHomeDir(); err == nil {
		pinned := home + "/.cache/codegraph/bin/tree-sitter"
		if _, err := os.Stat(pinned); err == nil {
			return pinned
		}
	}
	if b, err := exec.LookPath("tree-sitter"); err == nil {
		return b
	}
	return "/opt/homebrew/bin/tree-sitter"
}

type tsParser struct {
	scratch tsTree
	starts  []int
	frames  []cstFrame
}

type cstReader struct {
	bin string
	env []string
}

func tsEnv() []string {
	env := make([]string, 0, len(os.Environ())+2)
	env = append(env, os.Environ()...)
	env = append(env, "NO_COLOR=1", "TERM=dumb")
	return env
}

func newCSTReader() *cstReader {
	bin := tsCLIBin()
	if _, err := os.Stat(bin); err != nil {
		panic("tree-sitter CLI not found at " + bin +
			" -- pass TREE_SITTER_BIN or put tree-sitter on PATH")
	}
	return &cstReader{bin: bin, env: tsEnv()}
}

func (p *cstReader) free() {}

func readSource(path string) ([]byte, error) {
	f, err := os.Open(path)
	if err != nil {
		return nil, err
	}
	defer f.Close()
	st, err := f.Stat()
	if err != nil {
		return nil, err
	}
	buf := make([]byte, st.Size()+1024)
	n, err := io.ReadFull(f, buf[:st.Size()])
	if err != nil {
		if err == io.ErrUnexpectedEOF || err == io.EOF {
			var m int
			m, err = f.Read(buf[n:])
			n += m
		}
		if err != nil && err != io.EOF {
			return nil, err
		}
	}
	return buf[:n:n], nil
}

func (r *cstReader) read(idx int32, rec fileRec) cstBatch {
	b := cstBatch{idx: idx, rec: rec}
	src, err := readSource(rec.abspath)
	if err != nil {
		b.err = err
		return b
	}
	b.src = src
	h := sha1.Sum(src)
	b.sum = hex.EncodeToString(h[:])
	b.cst, b.err = r.runChild(src)
	return b
}

func (r *cstReader) runChild(src []byte) ([]byte, error) {
	cmd := exec.Command(r.bin, "parse", "/dev/stdin", "--scope", tsScope, "--cst")
	cmd.Env = r.env
	cmd.Stdin = bytes.NewReader(src)
	cmd.Stderr = nil
	pr, perr := cmd.StdoutPipe()
	if perr != nil {
		return nil, perr
	}
	if serr := cmd.Start(); serr != nil {
		return nil, serr
	}
	out := make([]byte, 0, len(src)*24+32768)
	const chunk = 32768
	for {
		if cap(out)-len(out) < chunk {
			grown := make([]byte, len(out), 2*cap(out)+chunk)
			copy(grown, out)
			out = grown
		}
		n, rerr := pr.Read(out[len(out) : len(out)+chunk])
		out = out[:len(out)+n]
		if rerr != nil {
			break
		}
	}
	err := cmd.Wait()
	if err != nil {
		if ee, ok := err.(*exec.ExitError); ok {
			if c := ee.ExitCode(); c < 0 || c > 1 {
				return nil, err
			}
		}
		if len(out) == 0 {
			return nil, err
		}
	}
	return out, nil
}

// The CLI prints one tree per file, concatenated with no separator. A root
// line is the only line whose node kind sits at column 0: child lines carry
// the depth as indentation before the kind name, and a raw newline inside a
// token is escaped to \n, so every record occupies exactly one line. Splitting
// on root lines is therefore exact for the files this reader produces -- but
// the caller still verifies the count and every file's end shape against the
// source it reads, falling back to one process per file on any disagreement.
func skipSpaces(b []byte, i int) int {
	for i < len(b) && (b[i] == ' ' || b[i] == '\t') {
		i++
	}
	return i
}

// rootLineEnd parses `0:0 - R:C [•]program` and returns the end position the
// CLI attributes to the tree, which must equal the parsed file's own end.
func rootLineEnd(l []byte) (row, col int, ok bool) {
	if len(l) < 11 || l[0] != '0' || l[1] != ':' || l[2] != '0' {
		return 0, 0, false
	}
	i := skipSpaces(l, 3)
	if i >= len(l) || l[i] != '-' {
		return 0, 0, false
	}
	i = skipSpaces(l, i+1)
	r0 := i
	for i < len(l) && l[i] >= '0' && l[i] <= '9' {
		i++
	}
	if i == r0 || i >= len(l) || l[i] != ':' {
		return 0, 0, false
	}
	row, _ = atoiBytes(l[r0:i])
	i++
	c0 := i
	for i < len(l) && l[i] >= '0' && l[i] <= '9' {
		i++
	}
	if i == c0 {
		return 0, 0, false
	}
	col, _ = atoiBytes(l[c0:i])
	i = skipSpaces(l, i)
	if i+3 <= len(l) && l[i] == 0xE2 && l[i+1] == 0x80 && l[i+2] == 0xA2 {
		i += 3 // error marker the CLI prefixes to nodes inside an ERROR subtree
	}
	// The pinned CLI pads the kind name with trailing blanks on multi-file
	// root lines; the PATH build being tested elsewhere does not.
	end := len(l)
	for end > i && (l[end-1] == ' ' || l[end-1] == '\t') {
		end--
	}
	if string(l[i:end]) != "program" {
		return 0, 0, false
	}
	return row, col, true
}

type rootMark struct {
	off      int
	row, col int
}

func splitRoots(out []byte) []rootMark {
	var marks []rootMark
	for i := 0; i < len(out); {
		j := bytes.IndexByte(out[i:], '\n')
		next := len(out)
		line := out[i:]
		if j >= 0 {
			line = out[i : i+j]
			next = i + j + 1
		}
		if row, col, ok := rootLineEnd(line); ok {
			marks = append(marks, rootMark{off: i, row: row, col: col})
		}
		i = next
	}
	return marks
}

// runBatch parses several files with ONE tree-sitter process. ok is false when
// the invocation itself is unusable and the caller must fall back to runChild
// per file. A batch with parse errors exits 1 exactly like a single file does.
func (r *cstReader) runBatch(recs []fileRec) ([]byte, bool) {
	args := make([]string, 0, len(recs)+4)
	args = append(args, "parse")
	for i := range recs {
		args = append(args, recs[i].abspath)
	}
	args = append(args, "--scope", tsScope, "--cst")
	cmd := exec.Command(r.bin, args...)
	cmd.Env = r.env
	cmd.Stderr = nil
	pr, perr := cmd.StdoutPipe()
	if perr != nil {
		return nil, false
	}
	if serr := cmd.Start(); serr != nil {
		return nil, false
	}
	est := 1 << 16
	for i := range recs {
		est += int(recs[i].size) * 28
	}
	if est > 32<<20 {
		est = 32 << 20
	}
	out := make([]byte, 0, est)
	const chunk = 1 << 16
	for {
		if cap(out)-len(out) < chunk {
			grown := make([]byte, len(out), 2*cap(out)+chunk)
			copy(grown, out)
			out = grown
		}
		n, rerr := pr.Read(out[len(out) : len(out)+chunk])
		out = out[:len(out)+n]
		if rerr != nil {
			break
		}
	}
	if err := cmd.Wait(); err != nil {
		if ee, ok := err.(*exec.ExitError); ok {
			if c := ee.ExitCode(); c < 0 || c > 1 {
				return nil, false
			}
		}
		if len(out) == 0 {
			return nil, false
		}
	}
	if len(out) == 0 {
		return nil, false
	}
	// Every record is newline-terminated, so completed output always ends in
	// one. Anything else is a partial write (a killed process, a full disk);
	// refuse the batch rather than hand the decoder a truncated tree.
	if out[len(out)-1] != '\n' {
		return nil, false
	}
	return out, true
}

// readBatch returns the per-file batches for files [start,end) parsed by one
// CLI process, or ok=false when the output cannot be split with certainty --
// then the caller uses read() for every file in the range, byte-for-byte the
// old per-file path.
func (r *cstReader) readBatch(recs []fileRec, start, end int) ([]cstBatch, bool) {
	section := recs[start:end]
	out, ok := r.runBatch(section)
	if !ok {
		return nil, false
	}
	marks := splitRoots(out)
	if len(marks) != len(section) {
		return nil, false
	}
	batches := make([]cstBatch, 0, len(section))
	for k, rec := range section {
		stop := len(out)
		if k+1 < len(marks) {
			stop = marks[k+1].off
		}
		b := cstBatch{idx: int32(start + k), rec: rec, cst: out[marks[k].off:stop]}
		src, err := readSource(rec.abspath)
		if err != nil {
			b.err = err
			batches = append(batches, b)
			continue
		}
		// The CLI parsed the file as it was on disk. If it changed shape
		// between that read and this one, the tree's row/col offsets would
		// not describe src -- fall back rather than decode a mismatched pair.
		nl := bytes.Count(src, []byte{'\n'})
		tail := len(src)
		if i := bytes.LastIndexByte(src, '\n'); i >= 0 {
			tail = len(src) - i - 1
		}
		if nl != marks[k].row || tail != marks[k].col {
			return nil, false
		}
		h := sha1.Sum(src)
		b.src = src
		b.sum = hex.EncodeToString(h[:])
		batches = append(batches, b)
	}
	return batches, true
}

func (p *tsParser) decodeCST(out, src []byte) *tsTree {
	t, derr := p.decode(out, src)
	if derr != nil {
		panic(fmt.Sprintf("cli cst decode failed: %v", derr))
	}
	return t
}

type tsTree struct {
	recs []tsRec
}

func (t *tsTree) free() {}

func (t *tsTree) root() tsNode {
	if len(t.recs) == 0 {
		return tsNode{}
	}
	return tsNode{t: t, i: 0}
}

type tsNode struct {
	t *tsTree
	i int32
}

type tsFieldID = uint16

func hasNode(n tsNode) bool { return n.t != nil }

func kindID(n tsNode) uint16 {
	if !hasNode(n) {
		return tsSymInvalid
	}
	return n.t.recs[n.i].sym
}

func kindName(n tsNode) string {
	if !hasNode(n) {
		return ""
	}
	s := kindID(n)
	if int(s) < nGrammarKinds {
		return kindNames[s]
	}
	if s == 0xFFFE {
		return "END"
	}
	return "ERROR"
}

func startByte(n tsNode) uint {
	if !hasNode(n) {
		return 0
	}
	return uint(n.t.recs[n.i].start)
}
func endByte(n tsNode) uint {
	if !hasNode(n) {
		return 0
	}
	return uint(n.t.recs[n.i].end)
}
func startRow(n tsNode) int {
	if !hasNode(n) {
		return 0
	}
	return int(n.t.recs[n.i].srow)
}
func endRow(n tsNode) int {
	if !hasNode(n) {
		return 0
	}
	return int(n.t.recs[n.i].erow)
}

func isNamedN(n tsNode) bool {
	if !hasNode(n) {
		return false
	}
	return n.t.recs[n.i].flags&tsFlagNamed != 0
}

func hasErr(n tsNode) bool {
	if !hasNode(n) {
		return false
	}
	return n.t.recs[n.i].flags&tsFlagErr != 0
}

func isMissingN(n tsNode) bool {
	if !hasNode(n) {
		return false
	}
	return n.t.recs[n.i].flags&tsFlagMiss != 0
}

func childCount(n tsNode) int {
	if !hasNode(n) {
		return 0
	}
	if nc := n.t.recs[n.i].nchild; nc != 0xFFFF {
		return int(nc)
	}

	c := n.i + 1
	end := n.t.recs[n.i].subEnd
	k := 0
	for c < end {
		k++
		c = n.t.recs[c].subEnd
	}
	return k
}

func namedChildCount(n tsNode) int {
	if !hasNode(n) {
		return 0
	}
	if nn := n.t.recs[n.i].nnamed; nn != 0xFFFF {
		return int(nn)
	}
	k := 0
	for c, end := n.i+1, n.t.recs[n.i].subEnd; c < end; c = n.t.recs[c].subEnd {
		if n.t.recs[c].flags&tsFlagNamed != 0 {
			k++
		}
	}
	return k
}

func childAt(n tsNode, k int) tsNode {
	if !hasNode(n) || k >= childCount(n) {
		return tsNode{}
	}
	c := n.i + 1
	for range k {
		c = n.t.recs[c].subEnd
	}
	return tsNode{t: n.t, i: c}
}

func namedChildAt(n tsNode, k int) tsNode {
	if !hasNode(n) {
		return tsNode{}
	}
	for c, end := n.i+1, n.t.recs[n.i].subEnd; c < end; c = n.t.recs[c].subEnd {
		if n.t.recs[c].flags&tsFlagNamed != 0 {
			if k == 0 {
				return tsNode{t: n.t, i: c}
			}
			k--
		}
	}
	return tsNode{}
}

func fieldNode(n tsNode, f tsFieldID) tsNode {
	if !hasNode(n) || f == 0 {
		return tsNode{}
	}
	for c, end := n.i+1, n.t.recs[n.i].subEnd; c < end; c = n.t.recs[c].subEnd {
		if n.t.recs[c].field == f {
			return tsNode{t: n.t, i: c}
		}
	}
	return tsNode{}
}

func parentNode(n tsNode) tsNode {
	if !hasNode(n) {
		return tsNode{}
	}
	pi := n.t.recs[n.i].parent
	if pi < 0 {
		return tsNode{}
	}
	return tsNode{t: n.t, i: pi}
}

func prevSibling(n tsNode) tsNode {
	if !hasNode(n) {
		return tsNode{}
	}
	pi := n.t.recs[n.i].parent
	if pi < 0 {
		return tsNode{}
	}
	for c, end := pi+1, n.t.recs[pi].subEnd; c < end; c = n.t.recs[c].subEnd {
		if n.t.recs[c].subEnd == n.i {
			return tsNode{t: n.t, i: c}
		}
	}
	return tsNode{}
}

type tsCursor struct {
	t     *tsTree
	stack []int32
	cur   int32
	dead  bool
}

func (cu *tsCursor) start(n tsNode) {
	if !hasNode(n) {
		cu.dead = true
		return
	}
	cu.dead = false
	cu.t = n.t
	cu.stack = append(cu.stack[:0], n.i)
	cu.cur = n.i
}

func (cu *tsCursor) done() {
	cu.dead = true
	cu.stack = cu.stack[:0]
	cu.t = nil
}

func (cu *tsCursor) node() tsNode {
	if cu.dead {
		return tsNode{}
	}
	return tsNode{t: cu.t, i: cu.cur}
}

func (cu *tsCursor) first() bool {
	if cu.dead || childCount(tsNode{t: cu.t, i: cu.cur}) == 0 {
		return false
	}
	cu.stack = append(cu.stack, cu.cur)
	cu.cur = cu.cur + 1
	return true
}

func (cu *tsCursor) next() bool {
	if cu.dead || len(cu.stack) == 0 {
		return false
	}
	parentEnd := cu.t.recs[cu.stack[len(cu.stack)-1]].subEnd
	sib := cu.t.recs[cu.cur].subEnd
	if sib >= parentEnd {
		return false
	}
	cu.cur = sib
	return true
}

func (cu *tsCursor) up() bool {
	if cu.dead || len(cu.stack) <= 1 {
		return false
	}
	cu.cur = cu.stack[len(cu.stack)-1]
	cu.stack = cu.stack[:len(cu.stack)-1]
	return true
}

func langSymbolCount() int { return tsSymCount }

func langSymbolName(id uint16) string {
	if int(id) < len(tsSymNames) {
		return tsSymNames[id]
	}
	return ""
}

var kindNames = tsSymNames

var (
	fName         = fieldID("name")
	fBody         = fieldID("body")
	fType         = fieldID("type")
	fParams       = fieldID("parameters")
	fFunction     = fieldID("function")
	fOperator     = fieldID("operator")
	fArguments    = fieldID("arguments")
	fScope        = fieldID("scope")
	fReturnType   = fieldID("return_type")
	fReadonly     = fieldID("readonly")
	fDefaultValue = fieldID("default_value")
	fAttributes   = fieldID("attributes")
	fVisibility   = fieldID("visibility")
	fLeft         = fieldID("left")
	fConsequence  = fieldID("consequence")
	fAlias        = fieldID("alias")
)

var fieldIDs = func() map[string]tsFieldID {
	m := make(map[string]tsFieldID, tsFieldCount)
	for f := 1; f < tsFieldCount; f++ {
		if _, dup := m[tsFieldNames[f]]; !dup {
			m[tsFieldNames[f]] = tsFieldID(f)
		}
	}
	return m
}()

func fieldID(name string) tsFieldID { return fieldIDs[name] }

var anonChildFields = func() map[string]map[string]string {
	m := make(map[string]map[string]string, len(tsAnonChildFields))
	for _, t := range tsAnonChildFields {
		cm, ok := m[t.parent]
		if !ok {
			cm = make(map[string]string, 8)
			m[t.parent] = cm
		}
		cm[t.child] = t.field
	}
	return m
}()

func anonChildField(parentSym uint16, childKind []byte) uint16 {
	if int(parentSym) >= len(tsSymNames) {
		return 0
	}
	if cm, ok := anonChildFields[tsSymNames[parentSym]]; ok {
		if f, ok2 := cm[string(childKind)]; ok2 {
			return fieldID(f)
		}
	}
	return 0
}

func fieldNodeByName(n tsNode, name string) tsNode {
	return fieldNode(n, fieldID(name))
}

type cstDecoder struct {
	starts []int
	total  int
}

var tsSymByID = func() map[string]uint16 {
	m := make(map[string]uint16, tsSymCount)
	for s, name := range tsSymNames {
		if _, dup := m[name]; !dup {
			m[name] = uint16(s)
		}
	}
	return m
}()

var tsErrKind = []byte("ERROR")

type cstFrame struct {
	i   int32
	end uint32
}

func (p *tsParser) decode(out, src []byte) (*tsTree, error) {
	starts := p.starts[:0]
	starts = append(starts[:0], 0)
	for i := 0; i < len(src); {
		j := bytes.IndexByte(src[i:], '\n')
		if j < 0 {
			break
		}
		i += j + 1
		starts = append(starts, i)
	}
	d := &cstDecoder{starts: starts, total: len(src)}

	est := bytes.Count(out, []byte{'\n'}) + 1
	recs := p.scratch.recs[:0]
	if cap(recs) < est {
		recs = make([]tsRec, 0, est)
	}
	stack := p.frames[:0]

	nextFresh := uint16(len(tsSymByID) + 0x4000)
	var freshIDs map[string]uint16
	internB := func(b []byte) uint16 {
		if id, ok := tsSymByID[string(b)]; ok {
			return id
		}
		if id, ok := freshIDs[string(b)]; ok {
			return id
		}
		if freshIDs == nil {
			freshIDs = make(map[string]uint16, 8)
		}
		id := nextFresh
		nextFresh++
		freshIDs[string(b)] = id
		return id
	}
	var unquoteBuf []byte

	restOut := out
	for len(restOut) > 0 {
		line := restOut
		if i := bytes.IndexByte(restOut, '\n'); i >= 0 {
			line, restOut = restOut[:i], restOut[i+1:]
		} else {
			restOut = nil
		}
		if len(line) == 0 {
			continue
		}

		if i := bytes.IndexByte(line, '\t'); i >= 0 && i < 12 {
			continue
		}

		colon1 := bytes.IndexByte(line, ':')
		if colon1 < 0 {
			continue
		}
		srow, n1 := atoiBytes(line[:colon1])
		if n1 == 0 {
			continue
		}
		rest := line[colon1+1:]
		scol, n2 := atoiBytes(rest)
		if n2 == 0 {
			continue
		}
		rest = rest[n2:]

		rest = bytes.TrimLeft(rest, " ")
		if len(rest) == 0 || rest[0] != '-' {
			continue
		}
		rest = bytes.TrimLeft(rest[1:], " ")
		erow, n3 := atoiBytes(rest)
		if n3 == 0 {
			continue
		}
		rest = rest[n3+1:]
		ecol, n4 := atoiBytes(rest)
		if n4 == 0 {
			continue
		}
		rest = rest[n4:]

		trimmed := bytes.TrimLeft(rest, " ")
		hasErrMark := false
		if len(trimmed) > 0 && trimmed[0] >= 0x80 {
			_, size := utf8.DecodeRune(trimmed)
			hasErrMark = true
			trimmed = bytes.TrimLeft(trimmed[size:], " ")
		}
		if len(trimmed) == 0 {
			continue
		}

		var field uint16
		var kindB []byte
		missing := false
		named := true
		if bytes.HasPrefix(trimmed, []byte("MISSING: ")) {
			missing = true
			tok := bytes.TrimLeft(trimmed[len("MISSING: "):], " ")
			if len(tok) > 0 && tok[0] == '"' {
				kindB = unquoteBytes(tok, &unquoteBuf)
				named = false
			} else {
				kindB, _ = kindToken(tok)
			}
		} else if trimmed[0] == '"' {
			kindB = unquoteBytes(trimmed, &unquoteBuf)
			named = false
		} else {

			if c := bytes.Index(trimmed, []byte(": ")); c > 0 {
				fname := trimmed[:c]
				if isFieldName(fname) {
					if f, ok := fieldIDs[string(fname)]; ok {
						field = f
					}
					trimmed = bytes.TrimLeft(trimmed[c+2:], " ")
					if len(trimmed) > 0 && trimmed[0] >= 0x80 {
						_, size := utf8.DecodeRune(trimmed)
						hasErrMark = true
						trimmed = bytes.TrimLeft(trimmed[size:], " ")
					}
				}
			}
			if trimmed[0] == '"' {
				kindB = unquoteBytes(trimmed, &unquoteBuf)
				named = false
			} else {
				kindB, _ = kindToken(trimmed)
			}
		}
		if len(kindB) == 0 {
			continue
		}

		if srow > 0xFFFF || erow > 0xFFFF {
			return nil, fmt.Errorf("node row %d exceeds the u16 record range", max(srow, erow))
		}

		start := d.offset(int(srow), int(scol))
		end := d.offset(int(erow), int(ecol))

		rec := tsRec{
			sym:    internB(kindB),
			field:  field,
			start:  start,
			end:    end,
			srow:   uint16(srow),
			erow:   uint16(erow),
			parent: -1,
		}
		if named {
			rec.flags |= tsFlagNamed
		}
		if missing {
			rec.flags |= tsFlagMiss
		}
		if bytes.Equal(kindB, tsErrKind) || hasErrMark {
			rec.flags |= tsFlagErr
		}
		idx := int32(len(recs))
		recs = append(recs, rec)

		for len(stack) > 0 && stack[len(stack)-1].end <= start {
			popped := stack[len(stack)-1]
			recs[popped.i].subEnd = int32(idx)
			stack = stack[:len(stack)-1]
		}
		if len(stack) > 0 {
			recs[idx].parent = stack[len(stack)-1].i
			if !named && field == 0 {

				recs[idx].field = anonChildField(recs[recs[idx].parent].sym, kindB)
			}
		}
		stack = append(stack, cstFrame{i: idx, end: end})
	}

	for len(stack) > 0 {
		popped := stack[len(stack)-1]
		recs[popped.i].subEnd = int32(len(recs))
		stack = stack[:len(stack)-1]
	}
	p.starts = starts
	p.frames = stack
	if len(recs) == 0 {
		return nil, fmt.Errorf("no nodes decoded (cli produced %d bytes)", len(out))
	}
	recs[0].parent = -1

	n := len(recs)
	for i := n - 1; i >= 0; i-- {
		r := &recs[i]
		if p := r.parent; p >= 0 {
			pr := &recs[p]
			if pr.nchild != 0xFFFF {
				if pr.nchild == 0xFFFE {
					pr.nchild = 0xFFFF
				} else {
					pr.nchild++
				}
			}
			if r.flags&tsFlagNamed != 0 && pr.nnamed != 0xFFFF {
				if pr.nnamed == 0xFFFE {
					pr.nnamed = 0xFFFF
				} else {
					pr.nnamed++
				}
			}
			if r.flags&tsFlagErr != 0 {
				pr.flags |= tsFlagErr
			}
		}
	}
	t := &p.scratch
	t.recs = recs
	return t, nil
}

func (d *cstDecoder) offset(row, col int) uint32 {
	if row >= len(d.starts) {
		return uint32(d.total)
	}
	if row < 0 {
		row = 0
	}
	off := d.starts[row] + col
	if off > d.total {
		off = d.total
	}
	return uint32(off)
}

func atoiBytes(b []byte) (int, int) {
	v := 0
	i := 0
	for i < len(b) && b[i] >= '0' && b[i] <= '9' {
		v = v*10 + int(b[i]-'0')
		i++
	}
	return v, i
}

func isFieldName(b []byte) bool {
	if len(b) == 0 {
		return false
	}
	for _, c := range b {
		if c >= 'a' && c <= 'z' || c >= 'A' && c <= 'Z' || c >= '0' && c <= '9' || c == '_' {
			continue
		}
		return false
	}
	return true
}

func kindToken(b []byte) ([]byte, int) {
	i := 0
	for i < len(b) && b[i] != ' ' && b[i] != '`' && b[i] != '\t' {
		i++
	}
	return b[:i], i
}

func unquoteBytes(b []byte, buf *[]byte) []byte {
	first := bytes.IndexByte(b, '"')
	last := bytes.LastIndexByte(b, '"')
	if first < 0 || last <= first {
		return nil
	}
	raw := b[first+1 : last]
	if bytes.IndexByte(raw, '\\') < 0 {
		return raw
	}
	sb := (*buf)[:0]
	for i := 0; i < len(raw); {
		if raw[i] != '\\' || i+1 >= len(raw) {
			sb = append(sb, raw[i])
			i++
			continue
		}
		switch raw[i+1] {
		case 'n':
			sb = append(sb, '\n')
			i += 2
		case 't':
			sb = append(sb, '\t')
			i += 2
		case 'r':
			sb = append(sb, '\r')
			i += 2
		case '"':
			sb = append(sb, '"')
			i += 2
		case '\\':
			sb = append(sb, '\\')
			i += 2
		case 'x':
			if i+3 < len(raw) {
				if v, err := strconv.ParseUint(string(raw[i+2:i+4]), 16, 8); err == nil {
					sb = append(sb, byte(v))
					i += 4
					continue
				}
			}
			sb = append(sb, raw[i])
			i++
		default:
			sb = append(sb, raw[i])
			i++
		}
	}
	*buf = sb
	return sb
}

var funcKinds = map[string]string{
	"function_definition": "function",
	"method_declaration":  "method",
	"anonymous_function":  "closure",
	"arrow_function":      "closure",

	"property_hook": "method",
}

var typeKinds = map[string]string{
	"class_declaration":     "class",
	"interface_declaration": "interface",
	"trait_declaration":     "trait",
	"enum_declaration":      "enum",
	"anonymous_class":       "class",
}

var nameFieldOverride = map[string]string{
	"anonymous_function": "",
	"arrow_function":     "",
	"anonymous_class":    "",
	"property_hook":      "",
}

const defaultNameField = "name"

var identNodeTypes = map[string]bool{"name": true, "variable_name": true}

var (
	loopNodes   = setOf("for_statement", "foreach_statement", "while_statement", "do_statement")
	branchNodes = setOf("if_statement", "else_if_clause", "match_conditional_expression")
	nestNodes   = setOf("if_statement", "for_statement", "foreach_statement", "while_statement",
		"do_statement", "switch_statement", "try_statement", "match_expression",
		"anonymous_function", "arrow_function")
	callNodes = setOf("function_call_expression", "member_call_expression",
		"nullsafe_member_call_expression", "scoped_call_expression", "object_creation_expression")
	commentNodes  = setOf("comment")
	stringNodes   = setOf("string", "encapsed_string", "heredoc", "nowdoc")
	numberNodes   = setOf("integer", "float")
	operatorNodes = setOf("binary_expression", "unary_op_expression", "assignment_expression",
		"augmented_assignment_expression", "update_expression", "subscript_expression",
		"member_access_expression", "nullsafe_member_access_expression",
		"conditional_expression", "cast_expression", "class_constant_access_expression",
		"clone_expression")
	pruneKinds = func() map[string]bool {
		m := map[string]bool{}
		for k := range funcKinds {
			m[k] = true
		}
		for k := range typeKinds {
			m[k] = true
		}
		return m
	}()
	fileExtraTypes = setOf("variable_name", "function_call_expression", "member_call_expression",
		"nullsafe_member_call_expression", "scoped_call_expression", "object_creation_expression",
		"dynamic_variable_name", "include_expression", "include_once_expression",
		"require_expression", "require_once_expression", "variadic_placeholder")

	onNodeTypes = setOf("binary_expression", "augmented_assignment_expression",
		"unary_op_expression", "conditional_expression", "echo_statement",
		"print_intrinsic", "return_statement", "catch_clause",
		"include_expression", "include_once_expression", "require_expression",
		"require_once_expression", "assignment_expression", "variable_name",
		"function_call_expression")
	paramNodeTypes = setOf("simple_parameter", "variadic_parameter", "property_promotion_parameter")
	modifierNodes  = setOf("abstract_modifier", "final_modifier", "static_modifier",
		"readonly_modifier", "visibility_modifier", "var_modifier")
)

func setOf(ss ...string) map[string]bool {
	m := make(map[string]bool, len(ss))
	for _, s := range ss {
		m[s] = true
	}
	return m
}

var counters = map[string]int{
	"throw_expression":                  cNThrow,
	"try_statement":                     cNTry,
	"catch_clause":                      cNCatch,
	"else_if_clause":                    cNElif,
	"nullsafe_member_access_expression": cNNullSafe,
	"nullsafe_member_call_expression":   cNNullSafe,
	"assignment_expression":             cNAssign,
	"error_suppression_expression":      cNErrorSuppress,
	"global_declaration":                cNGlobals,
	"exit_statement":                    cNDebugCall,
	"dynamic_variable_name":             cNVariableVar,
	"scoped_call_expression":            cNStaticCalls,
}

var flagNodes = map[string]int{}

var counterOrFlag = func() map[string][2]int {
	m := make(map[string][2]int, len(counters)+len(flagNodes))
	for k, v := range counters {
		m[k] = [2]int{v, -1}
	}
	for k, v := range flagNodes {
		p := m[k]
		p[1] = v
		m[k] = p
	}
	return m
}()

type loopCounter struct {
	needle string
	col    int
}

var loopCallCounters = []loopCounter{
	{"query", cQueryInLoop}, {"prepare", cQueryInLoop},
	{"mysqli_query", cQueryInLoop}, {"pg_query", cQueryInLoop},
	{"->get", cQueryInLoop}, {"->first", cQueryInLoop},
	{"->find", cQueryInLoop}, {"->all", cQueryInLoop},
	{"preg_match", cRegexInLoop}, {"preg_replace", cRegexInLoop},
	{"preg_split", cRegexInLoop},
	{"file_get_contents", cIOInLoop}, {"fopen", cIOInLoop},
	{"fwrite", cIOInLoop}, {"curl_exec", cIOInLoop},
	{"file_put_contents", cIOInLoop},
}

var hazardCalls = buildHazards(map[string]string{

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

	"exec_": "shell", "system": "shell", "shell_exec": "shell",
	"passthru": "shell", "popen": "shell", "proc_open": "shell",
	"pcntl_exec": "shell", "escapeshellcmd": "shell", "escapeshellarg": "shell",
	"expect_popen": "shell", "`": "shell",

	"eval": "exec", "assert": "exec", "create_function": "exec",
	"preg_replace_callback": "exec", "preg_replace": "exec",
	"ReflectionFunction::invoke": "exec", "runkit_function_add": "exec",

	"include": "include", "include_once": "include",
	"require": "include", "require_once": "include",
	"virtual": "include", "stream_wrapper_register": "include",

	"unserialize": "deserialize", "yaml_parse": "deserialize",
	"yaml_parse_file": "deserialize", "simplexml_load_string": "deserialize",
	"simplexml_load_file": "deserialize", "xml_parse": "deserialize",
	"wddx_deserialize": "deserialize", "igbinary_unserialize": "deserialize",
	"msgpack_unpack": "deserialize", "Symfony\\Serializer::deserialize": "deserialize",

	"printf": "xss", "vprintf": "xss", "print_r": "xss", "var_dump": "xss",
	"var_export": "xss", "fpassthru": "xss", "readfile": "xss",

	"htmlspecialchars": "xss", "htmlentities": "xss", "strip_tags": "xss",
	"e": "xss", "esc_html": "xss", "esc_attr": "xss", "filter_var": "xss",

	"ldap_search": "ldap", "ldap_list": "ldap", "ldap_read": "ldap",
	"ldap_bind": "ldap", "ldap_add": "ldap", "ldap_modify": "ldap",
	"ldap_escape": "ldap",

	"header": "header", "header_remove": "header", "setcookie": "header",
	"setrawcookie": "header", "session_start": "header",
	"session_id": "header", "session_regenerate_id": "header",
	"http_response_code": "header",

	"file_get_contents": "file", "file_put_contents": "file", "fopen": "file",
	"fwrite": "file", "fputs": "file", "fread": "file", "readfile_": "file",
	"unlink": "file", "rmdir": "file", "mkdir": "file", "copy": "file",
	"rename": "file", "chmod": "file", "chown": "file", "touch": "file",
	"move_uploaded_file": "file", "tempnam": "file", "tmpfile": "file",
	"glob": "file", "scandir": "file", "opendir": "file", "readdir": "file",
	"file": "file", "parse_ini_file": "file", "realpath": "file",
	"basename": "file", "dirname": "file", "pathinfo": "file",
	"SplFileObject::__construct": "file",

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

	"filter_input": "superglobal", "getenv": "superglobal",
	"apache_request_headers": "superglobal", "getallheaders": "superglobal",
	"parse_str": "superglobal", "http_build_query": "superglobal",

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

	"ReflectionClass::__construct":    "reflect",
	"ReflectionMethod::__construct":   "reflect",
	"ReflectionProperty::__construct": "reflect",
	"ReflectionFunction::__construct": "reflect",
	"get_class":                       "reflect", "get_parent_class": "reflect",
	"get_object_vars": "reflect", "get_class_methods": "reflect",
	"method_exists": "reflect", "property_exists": "reflect",
	"class_exists": "reflect", "interface_exists": "reflect",
	"function_exists": "reflect", "is_subclass_of": "reflect",
	"class_implements": "reflect", "class_uses": "reflect",
	"newInstance": "reflect", "newInstanceArgs": "reflect",
	"getMethod": "reflect", "getProperty": "reflect", "setAccessible": "reflect",

	"fgets": "io", "fgetcsv": "io", "fputcsv": "io", "fclose": "io",
	"fflush": "io", "flock": "io", "fseek": "io", "ftell": "io",
	"stream_get_contents": "io", "stream_copy_to_stream": "io",
	"error_log": "io", "syslog": "io", "ob_start": "io", "flush": "io",

	"curl_exec": "net", "curl_init": "net", "curl_setopt": "net",
	"curl_multi_exec": "net", "fsockopen": "net", "pfsockopen": "net",
	"stream_socket_client": "net", "stream_socket_server": "net",
	"socket_connect": "net", "socket_create": "net", "get_headers": "net",
	"gethostbyname": "net", "dns_get_record": "net", "checkdnsrr": "net",
	"mail": "net", "fsockopen_": "net", "send": "net", "request": "net",

	"set_time_limit": "resource", "ini_set": "resource", "ini_get": "resource",
	"memory_get_usage": "resource", "sleep": "resource", "usleep": "resource",
	"pcntl_fork": "resource", "pcntl_signal": "resource",
	"posix_setuid": "resource", "gc_collect_cycles": "resource",
	"apcu_store": "resource", "apcu_fetch": "resource",
	"shmop_open": "resource", "sem_acquire": "resource",

	"DB::transaction": "transaction", "DB::beginTransaction": "transaction",
	"DB::commit": "transaction", "DB::rollBack": "transaction",
	"transaction": "transaction", "beginTransaction": "transaction",
	"commit": "transaction", "rollBack": "transaction",
	"dispatch": "queue", "dispatchSync": "queue",
	"dispatchAfterCommit": "queue", "dispatchAfterResponse": "queue",
	"dispatchToQueue": "queue", "Queue::push": "queue",
	"Bus::dispatch": "queue",

	"save": "write", "create": "write", "update": "write", "delete": "write",
	"insert": "write", "increment": "write", "decrement": "write",
	"upsert": "write", "forceDelete": "write", "updateOrCreate": "write",
	"firstOrCreate": "write", "updateOrInsert": "write", "restore": "write",
	"truncate": "write",

	"fill": "massassign", "forceFill": "massassign",

	"env": "config",
})

func buildHazards(in map[string]string) map[string]string {
	out := make(map[string]string, len(in)*2)
	for k, v := range in {
		out[k] = v
		short := k
		if i := strings.LastIndexByte(short, '\\'); i >= 0 {
			short = short[i+1:]
		}
		out[short] = v
	}
	return out
}

var (
	psalmTainted = setOf("$_GET", "$_POST", "$_COOKIE", "$_REQUEST")
	superglobals = setOf("$_GET", "$_POST", "$_REQUEST", "$_COOKIE", "$_SERVER",
		"$_FILES", "$_SESSION", "$_ENV", "$GLOBALS")

	superglobalWalked = []string{"$_GET", "$_POST", "$_REQUEST", "$_COOKIE",
		"$_SERVER", "$_FILES", "$_SESSION", "$GLOBALS", "$_ENV"}

	dynamicCallNames = setOf("call_user_func", "call_user_func_array", "forward_static_call",
		"forward_static_call_array", "extract", "compact", "func_get_args",
		"func_num_args", "eval", "create_function", "assert",
		"spl_autoload_register", "register_shutdown_function",
		"set_error_handler", "set_exception_handler", "array_map",
		"array_filter", "usort", "uasort", "uksort", "array_walk")

	facadeClasses = setOf("DB", "Log", "Cache", "Config", "Route", "Auth", "Session",
		"Queue", "Storage", "Validator", "Event", "View", "Hash", "Cookie", "Crypt",
		"Lang", "File", "URL", "Redirect", "Response", "Input", "Gate", "Blade",
		"Artisan", "Schema", "Bus", "Redis", "Mail", "Notification", "Date")

	argShapeSinks = setOf("in_array", "array_search", "setcookie",
		"preg_match", "preg_replace", "preg_split", "preg_match_all",
		"preg_filter", "preg_quote", "file_put_contents", "fopen")

	cleartextSinks = setOf("file_get_contents", "curl_setopt", "curl_init", "fopen")

	magicMethods = setOf("__construct", "__destruct", "__call", "__callStatic", "__get", "__set",
		"__isset", "__unset", "__sleep", "__wakeup", "__serialize", "__unserialize",
		"__toString", "__invoke", "__set_state", "__clone", "__debugInfo")

	gadgetMethods = setOf("__destruct", "__wakeup", "__unserialize", "__toString", "__sleep", "__serialize")

	escapers = setOf("htmlspecialchars", "htmlentities", "htmlspecialchars_decode", "e",
		"esc_html", "esc_attr", "esc_url", "strip_tags", "filter_var",
		"urlencode", "rawurlencode", "json_encode", "intval", "floatval",
		"settype", "abs", "number_format")

	sqlEscapers = setOf("real_escape_string", "mysqli_real_escape_string",
		"mysql_real_escape_string", "pg_escape_string", "pg_escape_literal",
		"pg_escape_identifier", "quote", "addslashes", "intval", "floatval",
		"escape", "sanitize")

	sqlMethods = map[string]string{
		"query": "pdo", "exec": "pdo", "prepare": "pdo", "statement": "pdo",
		"unprepared": "pdo", "select": "builder", "insert": "builder",
		"update": "builder", "delete": "builder", "raw": "raw",
		"selectRaw": "raw", "whereRaw": "raw", "orWhereRaw": "raw",
		"havingRaw": "raw", "orderByRaw": "raw", "groupByRaw": "raw",
		"fromRaw": "raw", "joinSub": "raw", "createQuery": "doctrine",
		"createNativeQuery": "doctrine", "getQuery": "doctrine",
	}
	sqlFunctions = map[string]string{
		"mysqli_query": "mysqli", "mysqli_multi_query": "mysqli",
		"mysqli_real_query": "mysqli", "mysqli_prepare": "mysqli",
		"mysql_query": "mysql", "mysql_db_query": "mysql",
		"pg_query": "pgsql", "pg_send_query": "pgsql",
		"pg_query_params": "pgsql", "sqlsrv_query": "sqlsrv",
		"oci_parse": "oci", "db2_exec": "db2", "sqlite_query": "sqlite",
	}
)

var (
	sqlRe = regexp.MustCompile(`(?i)\b(SELECT\s|INSERT\s+INTO|UPDATE\s+\w|DELETE\s+FROM|REPLACE\s+INTO|` +
		`CREATE\s+TABLE|DROP\s+TABLE|ALTER\s+TABLE|TRUNCATE\s+TABLE|` +
		`UNION\s+(?:ALL\s+)?SELECT|FROM\s+\w+\s+WHERE)\b`)
	secretRe = regexp.MustCompile(`(?i)(api[_-]?key|apikey|secret|password|passwd|pwd|token|bearer|` +
		`access[_-]?key|private[_-]?key|client[_-]?secret|` +
		`auth[_-]?token|jwt|credential|smtp[_-]?pass|db[_-]?pass|` +
		`sk_live|rk_live|pk_live|ghp_|xoxb-|AKIA)`)
	placeholderRe = regexp.MustCompile(`(\?|:[a-zA-Z_]\w*)`)
	strictTypesRe = regexp.MustCompile(`declare\s*\(\s*strict_types\s*=\s*1\s*\)`)
	routeAttrRe   = regexp.MustCompile(`^(Route|Get|Post|Put|Patch|Delete|Options|Head|Any|` +
		`AsController|AsCommand|AsMessageHandler|AsEventListener|` +
		`Required|Middleware)$`)
	controllerPathRe = regexp.MustCompile(`(?i)(^|/)(Controllers?|Http/Controllers|Action|Endpoints?|Resources?)(/|$)`)
	modelPathRe      = regexp.MustCompile(`(?i)(^|/)(Models?|Entity|Entities|Domain|Eloquent)(/|$)`)
	entryFileRe      = regexp.MustCompile(`(?i)(^|/)(index\.php|artisan|console\.php|web\.php|api\.php|routes\.php|` +
		`app\.php|cli\.php|cron\.php|public/[^/]+\.php)$`)
	numRe = regexp.MustCompile(`^[-+]?(?:0[xXbBoO][0-9a-fA-F_]+|[\d_]+(?:\.[\d_]*)?` +
		`(?:[eE][-+]?\d+)?)[uUlLfFdD]*$`)
)

const secretMinLen = 12

var magicNumbers = func() map[string]bool {
	m := map[string]bool{
		"0x0": true, "0x1": true, "0xff": true, "0xFF": true, "0.0": true,
		"1.0": true, "-1": true, "": true,
	}
	for _, v := range []int{0, 1, 2, -1, 10, 100, 1000, 8, 16, 32, 64, 128, 256, 512,
		1024, 255, 65535, 4096, 24, 60, 365, 7, 12, 3, 4, 6} {
		m[itoa(int32(v))] = true
	}
	return m
}()

var authMarkers = []string{"auth", "login", "session", "password_verify", "hash_equals", "jwt"}

var phpBuiltins = func() map[string]bool {
	list := strings.Fields(`
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
gc_collect_cycles version_compare getenv putenv assert`)
	m := make(map[string]bool, len(list))
	for _, n := range list {
		m[n] = true
	}
	return m
}()

var phpBuiltinClasses = func() map[string]bool {
	list := strings.Fields(`
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
Deprecated NoDiscard`)
	m := make(map[string]bool, len(list))
	for _, n := range list {
		m[n] = true
	}
	return m
}()

var nGrammarKinds = langSymbolCount()

var nKindIDs = nGrammarKinds + 1

func slot(id uint16) int {
	if int(id) >= nGrammarKinds {
		return nGrammarKinds
	}
	return int(id)
}

func idsOf(kind string) []uint16 {
	ids, ok := kindIDs[kind]
	if !ok {
		panic("codegraph-php: the grammar has no node type named " + kind)
	}
	return ids
}

var kindIDs = func() map[string][]uint16 {
	m := make(map[string][]uint16, nGrammarKinds)
	for id := range nGrammarKinds {
		n := langSymbolName(uint16(id))
		m[n] = append(m[n], uint16(id))
	}
	return m
}()

func idSet(set map[string]bool) []bool {
	out := make([]bool, nKindIDs)
	for k, v := range set {
		for _, id := range idsOf(k) {
			out[id] = v
		}
	}
	return out
}

func idStrings(m map[string]string) []string {
	out := make([]string, nKindIDs)
	for k, v := range m {
		for _, id := range idsOf(k) {
			out[id] = v
		}
	}
	return out
}

const absentKind = "\x00"

func idStringsPresent(m map[string]string) []string {
	out := make([]string, nKindIDs)
	for i := range out {
		out[i] = absentKind
	}
	for k, v := range m {
		for _, id := range idsOf(k) {
			out[id] = v
		}
	}
	return out
}

func idPairTable(m map[string][2]int) [][2]int {
	out := make([][2]int, nKindIDs)
	for k, v := range m {
		for _, id := range idsOf(k) {
			out[id] = v
		}
	}
	return out
}

var (
	kFuncKind    = idStrings(funcKinds)
	kTypeKind    = idStrings(typeKinds)
	kNameField   = idStringsPresent(nameFieldOverride)
	kCounterFlag = idPairTable(counterOrFlag)
	kLoops       = idSet(loopNodes)
	kBranches    = idSet(branchNodes)
	kNest        = idSet(nestNodes)
	kCalls       = idSet(callNodes)
	kComments    = idSet(commentNodes)
	kStrings     = idSet(stringNodes)
	kNumbers     = idSet(numberNodes)
	kOperators   = idSet(operatorNodes)
	kOnNode      = idSet(onNodeTypes)
	kModifiers   = idSet(modifierNodes)
	kIdents      = idSet(identNodeTypes)
	kPrune       = idSet(pruneKinds)
)

var kPropertyHook = idsOf("property_hook")[0]

var kNameNode = idsOf("name")[0]

func kindShadowAgrees() error {
	check := func(name string, set map[string]bool, shadow []bool) error {
		for k, v := range set {
			for _, id := range idsOf(k) {
				if bool(shadow[id]) != v {
					return fmt.Errorf("%s: %q at id %d disagrees", name, k, id)
				}
			}
		}
		for id, v := range shadow {
			if !v {
				continue
			}
			if got := langSymbolName(uint16(id)); !set[got] {
				return fmt.Errorf("%s: id %d (%q) is not in the string set", name, id, got)
			}
		}
		return nil
	}
	for _, c := range []struct {
		name   string
		set    map[string]bool
		shadow []bool
	}{
		{"loopNodes", loopNodes, kLoops},
		{"branchNodes", branchNodes, kBranches},
		{"nestNodes", nestNodes, kNest},
		{"callNodes", callNodes, kCalls},
		{"commentNodes", commentNodes, kComments},
		{"stringNodes", stringNodes, kStrings},
		{"numberNodes", numberNodes, kNumbers},
		{"operatorNodes", operatorNodes, kOperators},
		{"onNodeTypes", onNodeTypes, kOnNode},
		{"modifierNodes", modifierNodes, kModifiers},
		{"identNodeTypes", identNodeTypes, kIdents},
		{"pruneKinds", pruneKinds, kPrune},
	} {
		if err := check(c.name, c.set, c.shadow); err != nil {
			return err
		}
	}

	for name, m := range map[string]map[string]string{"funcKinds": funcKinds, "typeKinds": typeKinds} {
		shadow := kFuncKind
		if name == "typeKinds" {
			shadow = kTypeKind
		}
		present := map[uint16]bool{}
		for k := range m {
			for _, id := range idsOf(k) {
				present[id] = true
			}
		}
		for id := range present {
			if shadow[id] == "" {
				return fmt.Errorf("%s: id %d (%q) lost its kind", name, id, langSymbolName(uint16(id)))
			}
		}
		for id, v := range shadow {
			if v == "" {
				continue
			}
			if got := langSymbolName(uint16(id)); !present[uint16(id)] || m[got] != v {
				return fmt.Errorf("%s: id %d (%q) = %q, not in the string table", name, id, got, v)
			}
		}
	}
	for k, v := range counterOrFlag {
		for _, id := range idsOf(k) {
			if got := kCounterFlag[id]; got != v {
				return fmt.Errorf("counterOrFlag: %q at id %d disagrees", k, id)
			}
		}
	}
	for k, v := range nameFieldOverride {
		for _, id := range idsOf(k) {
			if got := kNameField[id]; got != v {
				return fmt.Errorf("nameFieldOverride: %q at id %d disagrees", k, id)
			}
		}
	}
	return nil
}

type question struct {
	name  string
	title string
	notes string
	fn    func(g *graph, mod string, limit int) *result
}

var queries []question
var metrics []question

func init() {
	queries = append(buildQueries(), buildQueries2()...)
	metrics = buildMetrics()

	for i := range queries {
		if i < len(questionNotes) {
			queries[i].notes = questionNotes[i]
		}
	}
	for i := range metrics {
		if i < len(metricNotes) {
			metrics[i].notes = metricNotes[i]
		}
	}
}

func runQuestion(g *graph, q question, mod string, limit int) *result {
	r := q.fn(g, mod, limit)
	r.applyLimit(limit)
	return r
}

func (g *graph) atLoc(fileID, line int32) string {
	f := g.file(fileID)
	p := ""
	if f != nil {
		p = g.sa.str(f.path)
	}
	return p + ":" + itoa(line)
}

func (g *graph) modOfSym(sym int) string { return g.moduleName(g.sym.cols[cModuleID][sym]) }

func (g *graph) isTestFileOfSym(sym int) bool { return g.fileIsTest(g.sym.cols[cFileID][sym]) }

func (g *graph) isGenFileOfSym(sym int) bool {
	f := g.file(g.sym.cols[cFileID][sym])
	return f != nil && f.isGen != 0
}

func (g *graph) col(sym int, c int) int32 { return g.sym.cols[c][sym] }

func (g *graph) seeds(colIdx int) []int32 {
	var out []int32
	for i := 0; i < g.sym.n; i++ {
		if g.sym.cols[colIdx][i] > 0 {
			out = append(out, int32(i))
		}
	}
	return out
}

type rb struct {
	r *result
}

func (b *rb) row(cells ...cell) { b.r.rows = append(b.r.rows, cells) }

func newR(cols ...string) *rb { return &rb{&result{cols: cols}} }

func (b *rb) done() *result { return b.r }

const sortInsertMax = 32

func insertionSort(rows [][]cell, less func(a, b []cell) bool) {
	if len(rows) > sortInsertMax {
		slices.SortStableFunc(rows, func(x, y []cell) int {
			if less(x, y) {
				return -1
			}
			if less(y, x) {
				return 1
			}
			return 0
		})
		return
	}
	for i := 1; i < len(rows); i++ {
		v := rows[i]
		j := i - 1
		for j >= 0 && less(v, rows[j]) {
			rows[j+1] = rows[j]
			j--
		}
		rows[j+1] = v
	}
}

func i64(row []cell, i int) int64 {
	if i >= len(row) || row[i].kind != 'i' {
		return 0
	}
	return row[i].i
}

func qSuperglobalToSQL(g *graph, mod string, limit int) *result {
	b := newR("reads_input", "builds_sql", "hops", "build_kind", "driver", "sites",
		"sanitized", "prepared", "direct_super", "psalm_only", "all_super", "at")
	bySym := perSymbolSites(g.sqlSites, sqlSiteSym)

	type grp struct {
		src, sink, hops int32
		sites           []sqlSiteRow
	}
	var groups []grp
	idx := map[[3]int32]int{}
	rt := g.reachable(g.seeds(cNSuperglobalReads), 4, g.adj)
	for _, h := range reachGroups(rt) {
		if g.isTestFileOfSym(int(h.src)) {
			continue
		}
		sites := bySym[h.sym]
		if len(sites) == 0 {
			continue
		}
		if !sqlLike(g.modOfSym(int(h.sym)), mod) {
			continue
		}
		for _, st := range sites {
			switch g.sa.str(st.buildKind) {
			case "interp", "concat", "format", "variable":
			default:
				continue
			}
			if f := g.file(st.fileID); f == nil || f.isTest != 0 {
				continue
			}
			key := [3]int32{h.src, h.sym, 0}
			switch g.sa.str(st.buildKind) {
			case "interp":
				key[2] = 0
			case "concat":
				key[2] = 1
			case "format":
				key[2] = 2
			default:
				key[2] = 3
			}
			if j, ok := idx[key]; ok {
				groups[j].sites = append(groups[j].sites, st)
				if h.depth < groups[j].hops {
					groups[j].hops = h.depth
				}
				continue
			}
			idx[key] = len(groups)
			groups = append(groups, grp{h.src, h.sym, h.depth, []sqlSiteRow{st}})
		}
	}
	for _, gr := range groups {
		var san, prep, direct int32
		for _, st := range gr.sites {
			if st.sanitized {
				san++
			}
			if st.prepared {
				prep++
			}
			if st.hasSuper {
				direct++
			}
		}
		b.row(cellS(g.sym.str(cName, int(gr.src))), cellS(g.sym.str(cName, int(gr.sink))),
			cellI(int64(gr.hops)), cellS(g.sa.str(gr.sites[0].buildKind)),
			cellS(g.sa.str(gr.sites[0].driver)),
			cellI(int64(len(gr.sites))), cellI(int64(san)), cellI(int64(prep)),
			cellI(int64(direct)), cellI(int64(g.col(int(gr.src), cNPsalmTainted))),
			cellI(int64(g.col(int(gr.src), cNSuperglobalReads))),
			cellS(g.atLoc(gr.sites[0].fileID, minLine(gr.sites))))
	}
	insertionSort(b.r.rows, func(a, c []cell) bool {

		ai, ci := 0, 0
		if a[3].s != "interp" {
			ai = 1
		}
		if c[3].s != "interp" {
			ci = 1
		}
		if ai != ci {
			return ai < ci
		}
		if a[6].i != c[6].i {
			return a[6].i < c[6].i
		}
		if a[2].i != c[2].i {
			return a[2].i < c[2].i
		}
		return a[5].i > c[5].i
	})
	return b.done()
}

func qSuperglobalToInclude(g *graph, mod string, limit int) *result {
	b := newR("reads_input", "includes", "hops", "variable_includes", "in_loop",
		"argument", "n_get", "n_post", "n_request", "n_server", "at")
	bySym := perSymbolDyn(g.dynSites)
	rt := g.reachable(g.seeds(cNSuperglobalReads), 3, g.adj)
	type grp struct {
		src, sink int32
		hops      int32
		rows      []dynSiteRow
	}
	var groups []grp
	idx := map[[2]int32]int{}
	for _, h := range reachGroups(rt) {
		var keep []dynSiteRow
		for _, d := range bySym[h.sym] {
			if !g.sa.eq(d.kind, "variable_include") {
				continue
			}
			ff := g.file(d.fileID)
			if ff == nil || ff.isTest != 0 {
				continue
			}
			if !sqlLike(g.modOfSym(int(h.sym)), mod) {
				continue
			}
			keep = append(keep, d)
		}
		if len(keep) == 0 {
			continue
		}
		k := [2]int32{h.src, h.sym}
		if j, ok := idx[k]; ok {
			groups[j].rows = append(groups[j].rows, keep...)
			continue
		}
		idx[k] = len(groups)
		groups = append(groups, grp{h.src, h.sym, h.depth, keep})
	}
	for _, gr := range groups {
		var inLoop int32
		var targets []string
		var fileID int32
		for _, d := range gr.rows {
			if d.inLoop {
				inLoop++
			}
			targets = append(targets, clip(g.sa.str(d.target), 40))
			fileID = d.fileID
		}
		b.row(cellS(g.sym.str(cName, int(gr.src))), cellS(g.sym.str(cName, int(gr.sink))),
			cellI(int64(gr.hops)), cellI(int64(len(gr.rows))), cellI(int64(inLoop)),
			cellS(groupConcat(targets)),
			cellI(int64(g.col(int(gr.src), cNGet))), cellI(int64(g.col(int(gr.src), cNPost))),
			cellI(int64(g.col(int(gr.src), cNRequest))), cellI(int64(g.col(int(gr.src), cNServer))),
			cellS(g.atLoc(fileID, minLineD(gr.rows))))
	}
	insertionSort(b.r.rows, func(a, c []cell) bool {
		if a[2].i != c[2].i {
			return a[2].i < c[2].i
		}
		return a[3].i > c[3].i
	})
	return b.done()
}

func qUnserializeGadget(g *graph, mod string, limit int) *result {
	b := newR("reads_input", "deserializes", "hops", "unserialize_calls",
		"gadgets_in_repo", "destructs", "wakeups", "tostrings", "hazards_inside_gadgets", "at")
	var nGadgets, nDestr, nWake, nToStr, nHaz int32
	for i := range g.magic {
		if !g.magic[i].isGadget {
			continue
		}
		nGadgets++
		switch g.sa.str(g.magic[i].method) {
		case "__destruct":
			nDestr++
		case "__wakeup":
			nWake++
		case "__toString":
			nToStr++
		}
		nHaz += g.magic[i].nHazards
	}
	rt := g.reachable(g.seeds(cNSuperglobalReads), 4, g.adj)
	type grp struct {
		src, sink, hops int32
	}
	idx := map[[2]int32]int{}
	var groups []grp
	for _, h := range reachGroups(rt) {
		if g.col(int(h.sym), cNDeserialize) <= 0 {
			continue
		}
		if g.isTestFileOfSym(int(h.sym)) || !sqlLike(g.modOfSym(int(h.sym)), mod) {
			continue
		}
		k := [2]int32{h.src, h.sym}
		if j, ok := idx[k]; ok {
			if h.depth < groups[j].hops {
				groups[j].hops = h.depth
			}
			continue
		}
		idx[k] = len(groups)
		groups = append(groups, grp{h.src, h.sym, h.depth})
	}
	for _, gr := range groups {
		b.row(cellS(g.sym.str(cName, int(gr.src))), cellS(g.sym.str(cName, int(gr.sink))),
			cellI(int64(gr.hops)), cellI(int64(g.col(int(gr.sink), cNDeserialize))),
			cellI(int64(nGadgets)), cellI(int64(nDestr)), cellI(int64(nWake)),
			cellI(int64(nToStr)), cellI(int64(nHaz)),
			cellS(g.at(int(gr.sink))))
	}
	insertionSort(b.r.rows, func(a, c []cell) bool {
		if a[2].i != c[2].i {
			return a[2].i < c[2].i
		}
		return a[3].i > c[3].i
	})
	return b.done()
}

func qSuperglobalToShell(g *graph, mod string, limit int) *result {
	b := newR("reads_input", "runs_shell", "hops", "shell_calls", "code_exec", "evals",
		"patterns", "psalm_tainted_reads", "escapes", "risk", "at")
	bySym := perSymbolHaz(g.hazards)
	rt := g.reachable(g.seeds(cNSuperglobalReads), 3, g.adj)
	type grp struct {
		src, sink, hops int32
		pat             []string
	}
	idx := map[[2]int32]int{}
	var groups []grp
	for _, h := range reachGroups(rt) {
		s := int(h.sym)
		if !(g.col(s, cNShell) > 0 || g.col(s, cNExec) > 0 || g.col(s, cNEval) > 0) {
			continue
		}
		if g.isTestFileOfSym(s) || !sqlLike(g.modOfSym(s), mod) {
			continue
		}
		var pats []string
		for _, hz := range bySym[h.sym] {
			if g.sa.eq(hz.category, "shell") || g.sa.eq(hz.category, "exec") {
				pats = append(pats, g.sa.str(hz.pattern))
			}
		}
		k := [2]int32{h.src, h.sym}
		if j, ok := idx[k]; ok {
			groups[j].pat = append(groups[j].pat, pats...)
			if h.depth < groups[j].hops {
				groups[j].hops = h.depth
			}
			continue
		}
		idx[k] = len(groups)
		groups = append(groups, grp{h.src, h.sym, h.depth, pats})
	}
	for _, gr := range groups {
		s := int(gr.sink)
		b.row(cellS(g.sym.str(cName, int(gr.src))), cellS(g.sym.str(cName, s)),
			cellI(int64(gr.hops)), cellI(int64(g.col(s, cNShell))),
			cellI(int64(g.col(s, cNExec))), cellI(int64(g.col(s, cNEval))),
			cellS(groupConcat(gr.pat)),
			cellI(int64(g.col(int(gr.src), cNGet)+g.col(int(gr.src), cNPost)+g.col(int(gr.src), cNRequest))),
			cellI(int64(g.col(s, cNEscapedOutput))), cellI(int64(g.col(s, cRiskScore))),
			cellS(g.at(s)))
	}
	insertionSort(b.r.rows, func(a, c []cell) bool {
		if a[2].i != c[2].i {
			return a[2].i < c[2].i
		}
		return a[3].i > c[3].i
	})
	return b.done()
}

func qSuperglobalToEcho(g *graph, mod string, limit int) *result {
	b := newR("reads_input", "writes_output", "hops", "raw_echo", "escaped", "xss_calls",
		"header_calls", "n_get", "n_post", "n_cookie", "n_server", "at")
	rt := g.reachable(g.seeds(cNSuperglobalReads), 3, g.adj)
	idx := map[int32]int{}
	type grp struct {
		src, sink, hops int32
	}
	var groups []grp
	for _, h := range reachGroups(rt) {
		s := int(h.sym)
		if g.col(s, cNRawEcho) <= 0 {
			continue
		}
		if g.isTestFileOfSym(s) || !sqlLike(g.modOfSym(s), mod) {
			continue
		}
		if j, ok := idx[h.sym]; ok {
			if h.depth < groups[j].hops {
				groups[j].hops = h.depth
			}
			continue
		}
		idx[h.sym] = len(groups)
		groups = append(groups, grp{h.src, h.sym, h.depth})
	}
	for _, gr := range groups {
		s := int(gr.sink)
		if g.col(s, cNEscapedOutput) != 0 {
			continue
		}
		src := int(gr.src)
		b.row(cellS(g.sym.str(cName, src)), cellS(g.sym.str(cName, s)),
			cellI(int64(gr.hops)), cellI(int64(g.col(s, cNRawEcho))),
			cellI(int64(g.col(s, cNEscapedOutput))), cellI(int64(g.col(s, cNXSS))),
			cellI(int64(g.col(s, cNHeader))),
			cellI(int64(g.col(src, cNGet))), cellI(int64(g.col(src, cNPost))),
			cellI(int64(g.col(src, cNCookie))), cellI(int64(g.col(src, cNServer))),
			cellS(g.at(s)))
	}
	insertionSort(b.r.rows, func(a, c []cell) bool {
		if a[2].i != c[2].i {
			return a[2].i < c[2].i
		}
		return a[3].i > c[3].i
	})
	return b.done()
}

func walkPairs(g *graph, seeds []int32, depth int, adj *adjacency) []reachHit {
	return reachGroups(g.reachable(seeds, depth, adj))
}

func qNPlusOne(g *graph, mod string, limit int) *result {
	b := newR("loops_in", "queries_in", "hops", "loop_depth", "query_calls_in_loop",
		"sql_sites", "sql_hazards", "controller", "model", "caller_fan_in", "at")
	var seeds []int32
	for i := 0; i < g.sym.n; i++ {
		if g.col(i, cMaxLoopDepth) > 0 && g.col(i, cCallInLoop) > 0 {
			seeds = append(seeds, int32(i))
		}
	}
	bySym := perSymbolHaz(g.hazards)
	idx := map[[2]int32]int{}
	type grp struct {
		root, sym, hops int32
	}
	var groups []grp
	for _, h := range walkPairs(g, seeds, 3, g.adj) {
		if h.depth == 0 {
			continue
		}
		s := int(h.sym)
		nSqlSites := g.col(s, cNSQLCalls)
		nSqlHaz := g.col(s, cNSQL)
		if !(nSqlSites > 0 || nSqlHaz > 0) {
			continue
		}
		r := int(h.src)
		if g.isTestFileOfSym(r) || !sqlLike(g.modOfSym(r), mod) {
			continue
		}
		k := [2]int32{h.src, h.sym}
		if j, ok := idx[k]; ok {
			if h.depth < groups[j].hops {
				groups[j].hops = h.depth
			}
			continue
		}
		idx[k] = len(groups)
		groups = append(groups, grp{h.src, h.sym, h.depth})
	}
	for _, gr := range groups {
		r, s := int(gr.root), int(gr.sym)
		_ = bySym
		b.row(cellS(g.sym.str(cName, r)), cellS(g.sym.str(cName, s)),
			cellI(int64(gr.hops)), cellI(int64(g.col(r, cMaxLoopDepth))),
			cellI(int64(g.col(r, cQueryInLoop))), cellI(int64(g.col(s, cNSQLCalls))),
			cellI(int64(g.col(s, cNSQL))), cellI(int64(g.col(r, cIsController))),
			cellI(int64(g.col(s, cIsModel))), cellI(int64(g.col(r, cFanIn))),
			cellS(g.at(r)))
	}
	insertionSort(b.r.rows, func(a, c []cell) bool {
		if a[3].i != c[3].i {
			return a[3].i > c[3].i
		}
		return a[5].i > c[5].i
	})
	return b.done()
}

func qTypeJugglingAuth(g *graph, mod string, limit int) *result {
	b := newR("in_fn", "hops_from_input", "loose_cmp", "strict_cmp", "strict_types_file",
		"own_super_reads", "crypto_calls", "session_header", "entrypoint", "fan_in", "pct_loose", "at")
	idx := make(map[int32]int32)
	var sinks []int32
	for _, h := range walkPairs(g, g.seeds(cNSuperglobalReads), 3, g.adj) {
		s := int(h.sym)
		if g.col(s, cNLooseCompare) <= 0 {
			continue
		}
		if g.isTestFileOfSym(s) || !sqlLike(g.modOfSym(s), mod) {
			continue
		}
		if d, ok := idx[h.sym]; !ok || h.depth < d {
			idx[h.sym] = h.depth
			sinks = append(sinks, h.sym)
		}
	}
	slices.Sort(sinks)
	seen := map[int32]bool{}
	for _, sym := range sinks {
		if seen[sym] {
			continue
		}
		seen[sym] = true
		s := int(sym)
		loose, strict := g.col(s, cNLooseCompare), g.col(s, cNStrictCompare)
		var pct int64
		if loose+strict > 0 {
			pct = 100 * int64(loose) / int64(loose+strict)
		}
		b.row(cellS(g.sym.str(cName, s)), cellI(int64(idx[sym])),
			cellI(int64(loose)), cellI(int64(strict)),
			cellI(int64(g.col(s, cHasStrictTypes))), cellI(int64(g.col(s, cNSuperglobalReads))),
			cellI(int64(g.col(s, cNCrypto))), cellI(int64(g.col(s, cNHeader))),
			cellI(int64(g.col(s, cIsEntrypoint))), cellI(int64(g.col(s, cFanIn))),
			cellI(pct), cellS(g.at(s)))
	}
	insertionSort(b.r.rows, func(a, c []cell) bool {
		ac, cc := int64(0), int64(0)
		if a[6].i > 0 {
			ac = 1
		}
		if c[6].i > 0 {
			cc = 1
		}
		if ac != cc {
			return ac > cc
		}
		if a[10].i != c[10].i {
			return a[10].i > c[10].i
		}
		return a[2].i > c[2].i
	})
	return b.done()
}

func qDriverSplit(g *graph, mod string, limit int) *result {
	b := newR("namespace_", "drivers", "which", "sql_sites", "pdo_", "mysqli_", "pgsql_",
		"raw_", "builder_", "doctrine_", "spliced", "prepared", "sanitized")
	type agg struct {
		n                                                 int32
		pdo, mys, pg, raw, bld, doc, spliced, prep, sanit int32
		drivers                                           []string
	}
	byMod := map[int32]*agg{}
	var order []int32
	for i := range g.sqlSites {
		s := &g.sqlSites[i]
		f := g.file(s.fileID)
		if f == nil || f.isTest != 0 {
			continue
		}
		if !sqlLike(g.moduleName(f.moduleID), mod) {
			continue
		}
		a := byMod[f.moduleID]
		if a == nil {
			a = &agg{}
			byMod[f.moduleID] = a
			order = append(order, f.moduleID)
		}
		a.n++
		switch g.sa.str(s.driver) {
		case "pdo":
			a.pdo++
		case "mysqli":
			a.mys++
		case "pgsql":
			a.pg++
		case "raw":
			a.raw++
		case "builder":
			a.bld++
		case "doctrine":
			a.doc++
		}
		if g.sa.eq(s.buildKind, "interp") || g.sa.eq(s.buildKind, "concat") {
			a.spliced++
		}
		if s.prepared {
			a.prep++
		}
		if s.sanitized {
			a.sanit++
		}
		a.drivers = append(a.drivers, g.sa.str(s.driver))
	}
	for _, m := range order {
		a := byMod[m]
		if a.n == 0 {
			continue
		}
		distinct := groupConcat(a.drivers)
		b.row(cellS(g.moduleName(m)), cellI(int64(len(splitList(distinct)))),
			cellS(distinct),
			cellI(int64(a.n)), cellI(int64(a.pdo)), cellI(int64(a.mys)), cellI(int64(a.pg)),
			cellI(int64(a.raw)), cellI(int64(a.bld)), cellI(int64(a.doc)),
			cellI(int64(a.spliced)), cellI(int64(a.prep)), cellI(int64(a.sanit)))
	}
	_ = sort.Slice
	insertionSort(b.r.rows, func(a, c []cell) bool {
		if a[1].i != c[1].i {
			return a[1].i > c[1].i
		}
		return a[10].i > c[10].i
	})
	return b.done()
}

type symFilter struct {
	notTest, notGen bool
	mod             string
	pred            func(g *graph, s int) bool
}

func (g *graph) scan(cols []string, f symFilter,
	proj func(g *graph, s int) []cell, order func([]cell, []cell) bool) *result {
	b := newR(cols...)
	var modOK []bool
	if f.mod != "%" {
		modOK = make([]bool, len(g.mods)+1)
		for i := range modOK {
			modOK[i] = sqlLike(g.moduleName(int32(i)), f.mod)
		}
	}
	fids := g.sym.cols[cFileID]
	mids := g.sym.cols[cModuleID]
	for i := 0; i < g.sym.n; i++ {
		if f.notTest || f.notGen {
			if fid := fids[i]; fid >= 1 && int(fid) <= len(g.fils) {
				fr := &g.fils[fid-1]
				if f.notTest && fr.isTest != 0 {
					continue
				}
				if f.notGen && fr.isGen != 0 {
					continue
				}
			}
		}
		if modOK != nil {
			if mid := mids[i]; mid < 0 || int(mid) >= len(modOK) || !modOK[mid] {
				continue
			}
		}
		if f.pred != nil && !f.pred(g, i) {
			continue
		}
		b.row(proj(g, i)...)
	}
	if order != nil {
		insertionSort(b.r.rows, order)
	}
	return b.done()
}

func qFileUpload(g *graph, mod string, limit int) *result {
	return g.scan([]string{"name", "class_", "files_reads", "all_super", "io_ops",
		"dyn_includes", "sql_calls", "controller", "fan_in", "at"},
		symFilter{notTest: true, mod: mod, pred: func(g *graph, s int) bool {
			return g.col(s, cNFilesSuper) > 0
		}},
		func(g *graph, s int) []cell {
			return []cell{cellS(g.sym.str(cName, s)), cellS(g.sym.str(cClassName, s)),
				cellI(int64(g.col(s, cNFilesSuper))), cellI(int64(g.col(s, cNSuperglobalReads))),
				cellI(int64(g.col(s, cNIO))), cellI(int64(g.col(s, cNDynamicInclude))),
				cellI(int64(g.col(s, cNSQLCalls))), cellI(int64(g.col(s, cIsController))),
				cellI(int64(g.col(s, cFanIn))), cellS(g.at(s))}
		},
		func(a, c []cell) bool {
			if a[4].i != c[4].i {
				return a[4].i > c[4].i
			}
			return a[2].i > c[2].i
		})
}

func qErrorSuppression(g *graph, mod string, limit int) *result {
	return g.scan([]string{"name", "class_", "suppressed", "super_reads", "sql_calls",
		"trys", "empty_catches", "fan_in", "at"},
		symFilter{notTest: true, mod: mod, pred: func(g *graph, s int) bool {
			return g.col(s, cNErrorSuppress) > 0
		}},
		func(g *graph, s int) []cell {
			return []cell{cellS(g.sym.str(cName, s)), cellS(g.sym.str(cClassName, s)),
				cellI(int64(g.col(s, cNErrorSuppress))), cellI(int64(g.col(s, cNSuperglobalReads))),
				cellI(int64(g.col(s, cNSQLCalls))), cellI(int64(g.col(s, cNTry))),
				cellI(int64(g.col(s, cNCatchEmpty))), cellI(int64(g.col(s, cFanIn))),
				cellS(g.at(s))}
		},
		func(a, c []cell) bool {
			return i64(a, 2)*(1+i64(a, 3)+i64(a, 4)) > i64(c, 2)*(1+i64(c, 3)+i64(c, 4))
		})
}

func qDynamicCallSurface(g *graph, mod string, limit int) *result {
	return g.scan([]string{"name", "class_", "var_vars", "dyn_methods", "dyn_new",
		"dyn_calls", "evals", "super_reads", "unresolved", "fan_in", "at"},
		symFilter{notTest: true, mod: mod, pred: func(g *graph, s int) bool {
			return g.col(s, cNVariableVar)+g.col(s, cNDynamicMethod)+g.col(s, cNDynamicNew)+
				g.col(s, cNEval) > 0
		}},
		func(g *graph, s int) []cell {
			return []cell{cellS(g.sym.str(cName, s)), cellS(g.sym.str(cClassName, s)),
				cellI(int64(g.col(s, cNVariableVar))), cellI(int64(g.col(s, cNDynamicMethod))),
				cellI(int64(g.col(s, cNDynamicNew))), cellI(int64(g.col(s, cNDynamicCall))),
				cellI(int64(g.col(s, cNEval))), cellI(int64(g.col(s, cNSuperglobalReads))),
				cellI(int64(g.col(s, cNUnresolvedCalls))), cellI(int64(g.col(s, cFanIn))),
				cellS(g.at(s))}
		},
		func(a, c []cell) bool {
			ka := (i64(a, 6)*4 + i64(a, 2)*3 + i64(a, 4)*2 + i64(a, 3)) * (1 + i64(a, 7))
			kc := (i64(c, 6)*4 + i64(c, 2)*3 + i64(c, 4)*2 + i64(c, 3)) * (1 + i64(c, 7))
			return ka > kc
		})
}

func qMagicMethodSurface(g *graph, mod string, limit int) *result {
	return g.scan([]string{"name", "class_", "destructs", "wakeups", "tostrings",
		"call_magic", "magic_total", "io_ops", "exec_ops", "sql_calls", "at"},
		symFilter{notTest: true, mod: mod, pred: func(g *graph, s int) bool {
			return g.col(s, cNDestruct)+g.col(s, cNWakeup)+g.col(s, cNToString)+
				g.col(s, cNCallMagic) > 0
		}},
		func(g *graph, s int) []cell {
			return []cell{cellS(g.sym.str(cName, s)), cellS(g.sym.str(cClassName, s)),
				cellI(int64(g.col(s, cNDestruct))), cellI(int64(g.col(s, cNWakeup))),
				cellI(int64(g.col(s, cNToString))), cellI(int64(g.col(s, cNCallMagic))),
				cellI(int64(g.col(s, cNMagicMethod))), cellI(int64(g.col(s, cNIO))),
				cellI(int64(g.col(s, cNExec))), cellI(int64(g.col(s, cNSQLCalls))),
				cellS(g.at(s))}
		},
		func(a, c []cell) bool {
			if ka, kc := i64(a, 7)+i64(a, 8)+i64(a, 9), i64(c, 7)+i64(c, 8)+i64(c, 9); ka != kc {
				return ka > kc
			}
			return a[2].i > c[2].i
		})
}

func isKind(kinds ...string) func(string) bool {
	return func(s string) bool {
		return slices.Contains(kinds, s)
	}
}

var (
	kindFnMeth   = isKind("function", "method")
	kindFnMethCl = isKind("function", "method", "closure")
	kindMethFn   = isKind("method", "function")
)

func qUntypedPublic(g *graph, mod string, limit int) *result {
	return g.scan([]string{"name", "class_", "untyped", "params", "strict_types", "typed",
		"loose_eq", "public_", "fan_in", "at"},
		symFilter{notTest: true, mod: mod, pred: func(g *graph, s int) bool {
			return g.col(s, cNUntypedParams) > 0 && g.col(s, cHasStrictTypes) == 0 &&
				g.col(s, cIsPublic) == 1 && kindFnMeth(g.sym.str(cKind, s))
		}},
		func(g *graph, s int) []cell {
			return []cell{cellS(g.sym.str(cName, s)), cellS(g.sym.str(cClassName, s)),
				cellI(int64(g.col(s, cNUntypedParams))), cellI(int64(g.col(s, cNParams))),
				cellI(int64(g.col(s, cHasStrictTypes))), cellI(int64(g.col(s, cNTypeDeclarations))),
				cellI(int64(g.col(s, cNLooseCompare))), cellI(int64(g.col(s, cIsPublic))),
				cellI(int64(g.col(s, cFanIn))), cellS(g.at(s))}
		},
		func(a, c []cell) bool { return i64(a, 2)*(1+i64(a, 8)) > i64(c, 2)*(1+i64(c, 8)) })
}

func qDeadCode(g *graph, mod string, limit int) *result {
	return g.scan([]string{"name", "kind", "sloc", "cyclo", "ext_calls", "at"},
		symFilter{notTest: true, notGen: true, mod: mod, pred: func(g *graph, s int) bool {
			if g.col(s, cFanIn) != 0 || g.col(s, cIsPublic) != 0 || g.col(s, cIsTest) != 0 ||
				g.col(s, cIsEntrypoint) != 0 || g.col(s, cIsOverride) != 0 ||
				g.col(s, cIsAbstract) != 0 {
				return false
			}
			if !kindFnMethCl(g.sym.str(cKind, s)) {
				return false
			}
			n := g.sym.str(cName, s)
			return n != "(anonymous)" && n != "<module>"
		}},
		func(g *graph, s int) []cell {
			return []cell{cellS(g.sym.str(cName, s)), cellS(g.sym.str(cKind, s)),
				cellI(int64(g.col(s, cSloc))), cellI(int64(g.col(s, cCyclomatic))),
				cellI(int64(g.col(s, cNExternalCalls))), cellS(g.at(s))}
		},
		func(a, c []cell) bool { return a[2].i > c[2].i })
}

func qOutboundFetch(g *graph, mod string, limit int) *result {
	b := newR("name", "reached_from", "hops", "fetch_calls", "serialize_calls",
		"extract_calls", "header_calls", "fan_in", "at")
	var seeds []int32
	for i := 0; i < g.sym.n; i++ {
		f := g.file(g.sym.cols[cFileID][i])
		if (g.col(i, cIsController) == 1 || g.col(i, cIsEntrypoint) == 1) && f != nil && f.isTest == 0 {
			seeds = append(seeds, int32(i))
		}
	}
	idx := map[[2]int32]int{}
	var groups []struct{ root, sym, hops int32 }
	for _, h := range walkPairs(g, seeds, 4, g.adj) {
		s := int(h.sym)
		if h.depth == 0 {
			continue
		}
		if !(g.col(s, cNRemoteFetch) > 0 || g.col(s, cNSerializeCall) > 0 || g.col(s, cNExtractCall) > 0) {
			continue
		}
		if g.isTestFileOfSym(s) || !sqlLike(g.modOfSym(s), mod) {
			continue
		}
		k := [2]int32{h.src, h.sym}
		if j, ok := idx[k]; ok {
			if h.depth < groups[j].hops {
				groups[j].hops = h.depth
			}
			continue
		}
		idx[k] = len(groups)
		groups = append(groups, struct{ root, sym, hops int32 }{h.src, h.sym, h.depth})
	}
	for _, gr := range groups {
		s := int(gr.sym)
		b.row(cellS(g.sym.str(cName, s)), cellS(g.sym.str(cName, int(gr.root))),
			cellI(int64(gr.hops)), cellI(int64(g.col(s, cNRemoteFetch))),
			cellI(int64(g.col(s, cNSerializeCall))), cellI(int64(g.col(s, cNExtractCall))),
			cellI(int64(g.col(s, cNHeaderCall))), cellI(int64(g.col(s, cFanIn))),
			cellS(g.at(s)))
	}
	insertionSort(b.r.rows, func(a, c []cell) bool {
		if a[2].i != c[2].i {
			return a[2].i < c[2].i
		}
		if a[3].i != c[3].i {
			return a[3].i > c[3].i
		}
		return a[7].i > c[7].i
	})
	return b.done()
}

func qDeserialization(g *graph, mod string, limit int) *result {
	return g.scan([]string{"name", "serialize_calls", "eval_calls", "dynamic_includes",
		"fan_in", "controller", "at"},
		symFilter{notTest: true, mod: mod, pred: func(g *graph, s int) bool {
			return g.col(s, cNSerializeCall) > 0
		}},
		func(g *graph, s int) []cell {
			return []cell{cellS(g.sym.str(cName, s)), cellI(int64(g.col(s, cNSerializeCall))),
				cellI(int64(g.col(s, cNEval))), cellI(int64(g.col(s, cNDynamicInclude))),
				cellI(int64(g.col(s, cFanIn))), cellI(int64(g.col(s, cIsController))),
				cellS(g.at(s))}
		},
		func(a, c []cell) bool {
			if a[4].i != c[4].i {
				return a[4].i > c[4].i
			}
			return a[1].i > c[1].i
		})
}

func qCommandInjection(g *graph, mod string, limit int) *result {
	return g.scan([]string{"name", "eval_calls", "dynamic_calls", "dynamic_includes",
		"variable_vars", "fan_in", "controller", "at"},
		symFilter{notTest: true, mod: mod, pred: func(g *graph, s int) bool {
			return g.col(s, cNEval)+g.col(s, cNDynamicCall)+g.col(s, cNDynamicInclude) > 0
		}},
		func(g *graph, s int) []cell {
			return []cell{cellS(g.sym.str(cName, s)), cellI(int64(g.col(s, cNEval))),
				cellI(int64(g.col(s, cNDynamicCall))), cellI(int64(g.col(s, cNDynamicInclude))),
				cellI(int64(g.col(s, cNVariableVar))), cellI(int64(g.col(s, cFanIn))),
				cellI(int64(g.col(s, cIsController))), cellS(g.at(s))}
		},
		func(a, c []cell) bool {
			if a[5].i != c[5].i {
				return a[5].i > c[5].i
			}
			return i64(a, 1)+i64(a, 2) > i64(c, 1)+i64(c, 2)
		})
}

func qFileInclusion(g *graph, mod string, limit int) *result {
	return g.scan([]string{"name", "dynamic_includes", "variable_vars", "eval_calls",
		"fan_in", "controller", "at"},
		symFilter{notTest: true, mod: mod, pred: func(g *graph, s int) bool {
			return g.col(s, cNDynamicInclude) > 0
		}},
		func(g *graph, s int) []cell {
			return []cell{cellS(g.sym.str(cName, s)), cellI(int64(g.col(s, cNDynamicInclude))),
				cellI(int64(g.col(s, cNVariableVar))), cellI(int64(g.col(s, cNEval))),
				cellI(int64(g.col(s, cFanIn))), cellI(int64(g.col(s, cIsController))),
				cellS(g.at(s))}
		},
		func(a, c []cell) bool {
			if a[4].i != c[4].i {
				return a[4].i > c[4].i
			}
			return a[1].i > c[1].i
		})
}

func qHeaderRedirect(g *graph, mod string, limit int) *result {
	return g.scan([]string{"name", "header_calls", "session_calls", "cyclo", "fan_in",
		"controller", "at"},
		symFilter{notTest: true, mod: mod, pred: func(g *graph, s int) bool {
			return g.col(s, cNHeaderCall) > 0
		}},
		func(g *graph, s int) []cell {
			return []cell{cellS(g.sym.str(cName, s)), cellI(int64(g.col(s, cNHeaderCall))),
				cellI(int64(g.col(s, cNSessionCall))), cellI(int64(g.col(s, cCyclomatic))),
				cellI(int64(g.col(s, cFanIn))), cellI(int64(g.col(s, cIsController))),
				cellS(g.at(s))}
		},
		func(a, c []cell) bool {
			if a[4].i != c[4].i {
				return a[4].i > c[4].i
			}
			return a[1].i > c[1].i
		})
}

func qOpenRedirect(g *graph, mod string, limit int) *result {
	b := newR("name", "header_sites", "superglobal_reads", "fan_in", "controller", "at")
	for i := range g.hazards {
		h := &g.hazards[i]
		if !g.sa.eq(h.pattern, "header") {
			continue
		}
		s := int(h.sym)
		if g.col(s, cNSuperglobalReads) <= 0 || g.isTestFileOfSym(s) ||
			!sqlLike(g.modOfSym(s), mod) {
			continue
		}
		b.row(cellS(g.sym.str(cName, s)), cellI(int64(h.n)),
			cellI(int64(g.col(s, cNSuperglobalReads))), cellI(int64(g.col(s, cFanIn))),
			cellI(int64(g.col(s, cIsController))), cellS(g.at(s)))
	}
	insertionSort(b.r.rows, func(a, c []cell) bool {
		if a[3].i != c[3].i {
			return a[3].i > c[3].i
		}
		return a[1].i > c[1].i
	})
	return b.done()
}

func qHardcodedSecrets(g *graph, mod string, limit int) *result {
	b := newR("name", "candidate", "line", "at")
	for i := range g.secrets {
		s := &g.secrets[i]
		f := g.file(s.fileID)
		if f == nil || f.isTest != 0 {
			continue
		}
		if !sqlLike(g.moduleName(f.moduleID), mod) {
			continue
		}
		v := g.sa.str(s.value)
		if strings.HasPrefix(v, "/") || strings.Contains(v, "|") || strings.Contains(v, "%") {
			continue
		}
		if s.symNull {
			continue
		}
		b.row(cellS(g.sym.str(cName, int(s.sym))), cellS(v), cellI(int64(s.line)),
			cellS(g.atLoc(s.fileID, s.line)))
	}
	insertionSort(b.r.rows, func(a, c []cell) bool { return len(a[1].s) > len(c[1].s) })
	return b.done()
}

func qXXE(g *graph, mod string, limit int) *result {
	return g.scan([]string{"name", "xml_parsers", "sloc", "at"},
		symFilter{notTest: true, mod: mod, pred: func(g *graph, s int) bool {
			return g.col(s, cNXxeParser) > 0
		}},
		func(g *graph, s int) []cell {
			return []cell{cellS(g.sym.str(cName, s)), cellI(int64(g.col(s, cNXxeParser))),
				cellI(int64(g.col(s, cSloc))), cellS(g.at(s))}
		},
		func(a, c []cell) bool {
			if a[1].i != c[1].i {
				return a[1].i > c[1].i
			}
			return a[2].i > c[2].i
		})
}

func qPathTraversal(g *graph, mod string, limit int) *result {
	return g.scan([]string{"name", "open_sites", "superglobal_reads", "at"},
		symFilter{notTest: true, mod: mod, pred: func(g *graph, s int) bool {
			return g.col(s, cNDynamicOpen) > 0 && g.col(s, cNSuperglobalReads) > 0
		}},
		func(g *graph, s int) []cell {
			return []cell{cellS(g.sym.str(cName, s)), cellI(int64(g.col(s, cNDynamicOpen))),
				cellI(int64(g.col(s, cNSuperglobalReads))), cellS(g.at(s))}
		},
		func(a, c []cell) bool {
			if a[1].i != c[1].i {
				return a[1].i > c[1].i
			}
			return a[2].i > c[2].i
		})
}

func qUncheckedUpload(g *graph, mod string, limit int) *result {
	return g.scan([]string{"name", "moves", "files_reads", "at"},
		symFilter{notTest: true, mod: mod, pred: func(g *graph, s int) bool {
			return g.col(s, cNMoveUploaded) > 0 && g.col(s, cNFilesSuper) > 0
		}},
		func(g *graph, s int) []cell {
			return []cell{cellS(g.sym.str(cName, s)), cellI(int64(g.col(s, cNMoveUploaded))),
				cellI(int64(g.col(s, cNFilesSuper))), cellS(g.at(s))}
		},
		func(a, c []cell) bool {
			if a[1].i != c[1].i {
				return a[1].i > c[1].i
			}
			return a[2].i > c[2].i
		})
}

func qLogInjection(g *graph, mod string, limit int) *result {
	return g.scan([]string{"name", "log_calls", "superglobal_reads", "at"},
		symFilter{notTest: true, mod: mod, pred: func(g *graph, s int) bool {
			return g.col(s, cNLogCall) > 0 && g.col(s, cNSuperglobalReads) > 0
		}},
		func(g *graph, s int) []cell {
			return []cell{cellS(g.sym.str(cName, s)), cellI(int64(g.col(s, cNLogCall))),
				cellI(int64(g.col(s, cNSuperglobalReads))), cellS(g.at(s))}
		},
		func(a, c []cell) bool {
			if a[1].i != c[1].i {
				return a[1].i > c[1].i
			}
			return a[2].i > c[2].i
		})
}

func qUnauthInput(g *graph, mod string, limit int) *result {
	return g.scan([]string{"name", "superglobal_reads", "at"},
		symFilter{notTest: true, mod: mod, pred: func(g *graph, s int) bool {
			return g.col(s, cNSuperglobalReads) > 0 && g.col(s, cNAuthCall) == 0
		}},
		func(g *graph, s int) []cell {
			return []cell{cellS(g.sym.str(cName, s)),
				cellI(int64(g.col(s, cNSuperglobalReads))), cellS(g.at(s))}
		},
		func(a, c []cell) bool {
			if a[1].i != c[1].i {
				return a[1].i > c[1].i
			}
			return a[0].s < c[0].s
		})
}

func qSessionFixation(g *graph, mod string, limit int) *result {
	return g.scan([]string{"name", "session_calls", "fan_in", "controller", "at"},
		symFilter{notTest: true, mod: mod, pred: func(g *graph, s int) bool {
			return g.col(s, cNSessionCall) > 0
		}},
		func(g *graph, s int) []cell {
			return []cell{cellS(g.sym.str(cName, s)), cellI(int64(g.col(s, cNSessionCall))),
				cellI(int64(g.col(s, cFanIn))), cellI(int64(g.col(s, cIsController))),
				cellS(g.at(s))}
		},
		func(a, c []cell) bool {
			if a[2].i != c[2].i {
				return a[2].i > c[2].i
			}
			return a[1].i > c[1].i
		})
}

func qExtractInjection(g *graph, mod string, limit int) *result {
	return g.scan([]string{"name", "extract_calls", "superglobal_reads", "variable_vars",
		"fan_in", "controller", "at"},
		symFilter{notTest: true, mod: mod, pred: func(g *graph, s int) bool {
			return g.col(s, cNExtractCall) > 0
		}},
		func(g *graph, s int) []cell {
			return []cell{cellS(g.sym.str(cName, s)), cellI(int64(g.col(s, cNExtractCall))),
				cellI(int64(g.col(s, cNSuperglobalReads))), cellI(int64(g.col(s, cNVariableVar))),
				cellI(int64(g.col(s, cFanIn))), cellI(int64(g.col(s, cIsController))),
				cellS(g.at(s))}
		},
		func(a, c []cell) bool {
			if a[4].i != c[4].i {
				return a[4].i > c[4].i
			}
			return a[1].i > c[1].i
		})
}

func qLooseCompare(g *graph, mod string, limit int) *result {
	return g.scan([]string{"name", "loose_compares", "strict_compares", "has_strict_types",
		"fan_in", "cyclo", "at"},
		symFilter{notTest: true, mod: mod, pred: func(g *graph, s int) bool {
			return g.col(s, cNLooseCompare) > 0
		}},
		func(g *graph, s int) []cell {
			return []cell{cellS(g.sym.str(cName, s)), cellI(int64(g.col(s, cNLooseCompare))),
				cellI(int64(g.col(s, cNStrictCompare))), cellI(int64(g.col(s, cHasStrictTypes))),
				cellI(int64(g.col(s, cFanIn))), cellI(int64(g.col(s, cCyclomatic))),
				cellS(g.at(s))}
		},
		func(a, c []cell) bool {
			if a[1].i != c[1].i {
				return a[1].i > c[1].i
			}
			return a[4].i > c[4].i
		})
}

func qErrorSuppressOp(g *graph, mod string, limit int) *result {
	return g.scan([]string{"name", "error_suppress", "loose_compares", "empty_catches",
		"fan_in", "cyclo", "at"},
		symFilter{notTest: true, mod: mod, pred: func(g *graph, s int) bool {
			return g.col(s, cNErrorSuppress) > 0
		}},
		func(g *graph, s int) []cell {
			return []cell{cellS(g.sym.str(cName, s)), cellI(int64(g.col(s, cNErrorSuppress))),
				cellI(int64(g.col(s, cNLooseCompare))), cellI(int64(g.col(s, cNCatchEmpty))),
				cellI(int64(g.col(s, cFanIn))), cellI(int64(g.col(s, cCyclomatic))),
				cellS(g.at(s))}
		},
		func(a, c []cell) bool {
			if a[1].i != c[1].i {
				return a[1].i > c[1].i
			}
			return a[4].i > c[4].i
		})
}

func qWeakHash(g *graph, mod string, limit int) *result {
	return g.scan([]string{"name", "weak_hashs", "weak_randoms", "fan_in", "controller", "at"},
		symFilter{notTest: true, mod: mod, pred: func(g *graph, s int) bool {
			return g.col(s, cNWeakHash)+g.col(s, cNWeakRandom) > 0
		}},
		func(g *graph, s int) []cell {
			return []cell{cellS(g.sym.str(cName, s)), cellI(int64(g.col(s, cNWeakHash))),
				cellI(int64(g.col(s, cNWeakRandom))), cellI(int64(g.col(s, cFanIn))),
				cellI(int64(g.col(s, cIsController))), cellS(g.at(s))}
		},
		func(a, c []cell) bool {
			if a[3].i != c[3].i {
				return a[3].i > c[3].i
			}
			return i64(a, 1)+i64(a, 2) > i64(c, 1)+i64(c, 2)
		})
}

func qRemoteFetch(g *graph, mod string, limit int) *result {
	return g.scan([]string{"name", "remote_fetches", "superglobal_reads", "fan_in",
		"controller", "at"},
		symFilter{notTest: true, mod: mod, pred: func(g *graph, s int) bool {
			return g.col(s, cNRemoteFetch) > 0
		}},
		func(g *graph, s int) []cell {
			return []cell{cellS(g.sym.str(cName, s)), cellI(int64(g.col(s, cNRemoteFetch))),
				cellI(int64(g.col(s, cNSuperglobalReads))), cellI(int64(g.col(s, cFanIn))),
				cellI(int64(g.col(s, cIsController))), cellS(g.at(s))}
		},
		func(a, c []cell) bool {
			if a[3].i != c[3].i {
				return a[3].i > c[3].i
			}
			return a[1].i > c[1].i
		})
}

func qCSRFMissing(g *graph, mod string, limit int) *result {
	return g.scan([]string{"name", "is_controller", "superglobal_reads", "session_calls",
		"n_params", "fan_in", "at"},
		symFilter{notTest: true, mod: mod, pred: func(g *graph, s int) bool {
			return g.col(s, cIsController) == 1
		}},
		func(g *graph, s int) []cell {
			return []cell{cellS(g.sym.str(cName, s)), cellI(int64(g.col(s, cIsController))),
				cellI(int64(g.col(s, cNSuperglobalReads))), cellI(int64(g.col(s, cNSessionCall))),
				cellI(int64(g.col(s, cNParams))), cellI(int64(g.col(s, cFanIn))),
				cellS(g.at(s))}
		},
		func(a, c []cell) bool {
			if a[5].i != c[5].i {
				return a[5].i > c[5].i
			}
			return a[2].i > c[2].i
		})
}

func qTraitAdoption(g *graph, mod string, limit int) *result {
	b := newR("trait", "namespace", "adopted_by", "methods", "props", "abstract_methods", "at")
	for i := range g.traits {
		t := &g.traits[i]
		if t.usedBy <= 0 {
			continue
		}
		if !sqlLike(g.moduleName(g.file(g.fils[t.fileID-1].moduleID).moduleID), mod) {
			continue
		}
		b.row(cellS(g.sa.str(t.name)), cellS(g.sa.str(t.ns)), cellI(int64(t.usedBy)), cellI(int64(t.nMethods)),
			cellI(int64(t.nProps)), cellI(int64(t.nAbstract)),
			cellS(g.atLoc(t.fileID, t.line)))
	}
	insertionSort(b.r.rows, func(a, c []cell) bool {
		if a[2].i != c[2].i {
			return a[2].i > c[2].i
		}
		return a[3].i > c[3].i
	})
	return b.done()
}

func qNamespaceInstability(g *graph, mod string, limit int) *result {
	b := newR("namespace_", "afferent", "efferent", "total_deps", "pct_instability")

	nsOfClass := make(map[string][]string, len(g.classes))
	for i := range g.classes {
		cn := g.sa.str(g.classes[i].name)
		ns := g.sa.str(g.classes[i].ns)
		list := nsOfClass[cn]
		if !containsStr(list, ns) {
			nsOfClass[cn] = append(list, ns)
		}
	}
	affSet := map[string]map[string]bool{}
	effSet := map[string]map[string]bool{}
	touch := func(m map[string]map[string]bool, k, v string) {
		s := m[k]
		if s == nil {
			s = map[string]bool{}
			m[k] = s
		}
		s[v] = true
	}
	for i := range g.edges {
		e := &g.edges[i]
		ca := g.sym.str(cClassName, int(e.caller))
		cb := g.sym.str(cClassName, int(e.callee))
		if ca == "" || cb == "" {
			continue
		}
		for _, na := range nsOfClass[ca] {
			for _, nb := range nsOfClass[cb] {
				if na == nb {
					continue
				}
				touch(effSet, na, nb)
				touch(affSet, nb, na)
			}
		}
	}
	names := map[string]bool{}
	for k := range affSet {
		names[k] = true
	}
	for k := range effSet {
		names[k] = true
	}
	for _, n := range sortedKeys(names) {
		aff, eff := int32(len(affSet[n])), int32(len(effSet[n]))
		total := aff + eff
		var pct int64
		if total > 0 {
			pct = 100 * int64(eff) / int64(total)
		}
		b.row(cellS(n), cellI(int64(aff)), cellI(int64(eff)), cellI(int64(total)), cellI(pct))
	}

	filtered := b.r.rows[:0]
	for _, r := range b.r.rows {
		if sqlLike(r[0].s, mod) {
			filtered = append(filtered, r)
		}
	}
	b.r.rows = filtered
	insertionSort(b.r.rows, func(a, c []cell) bool {
		if a[3].i != c[3].i {
			return a[3].i > c[3].i
		}
		return a[4].i > c[4].i
	})
	return b.done()
}

func qLSBHotspots(g *graph, mod string, limit int) *result {
	return g.scan([]string{"name", "class_", "scoped_calls", "dyn_methods", "sloc", "fan_in", "at"},
		symFilter{notTest: true, mod: mod, pred: func(g *graph, s int) bool {
			return g.col(s, cNStaticCalls) > 0 && kindMethFn(g.sym.str(cKind, s))
		}},
		func(g *graph, s int) []cell {
			return []cell{cellS(g.sym.str(cName, s)), cellS(g.sym.str(cClassName, s)),
				cellI(int64(g.col(s, cNStaticCalls))), cellI(int64(g.col(s, cNDynamicMethod))),
				cellI(int64(g.col(s, cSloc))), cellI(int64(g.col(s, cFanIn))), cellS(g.at(s))}
		},
		func(a, c []cell) bool {
			if a[2].i != c[2].i {
				return a[2].i > c[2].i
			}
			return a[5].i > c[5].i
		})
}

func qPSR4Violations(g *graph, mod string, limit int) *result {
	return newR("fqn", "kind", "module", "psr4_roots", "at").done()
}

func qMagicFallback(g *graph, mod string, limit int) *result {
	b := newR("class_", "has_call", "has_get", "has_invoke", "magic_methods",
		"unresolved_in_file", "at")

	unresInFile := make(map[int32]int32)
	for i := range g.unresolved {
		unresInFile[g.sym.cols[cFileID][g.unresolved[i].caller]]++
	}
	for i := range g.classes {
		c := &g.classes[i]
		if !(c.hasCall || c.hasCallStatic || c.hasGet || c.hasInvoke) {
			continue
		}
		if g.isTestFileOfSym(int(c.sym)) || !sqlLike(g.modOfSym(int(c.sym)), mod) {
			continue
		}
		n := unresInFile[c.fileID]
		if n == 0 {
			continue
		}
		b.row(cellS(g.sa.str(c.name)), cellI(bi(c.hasCall)), cellI(bi(c.hasGet)),
			cellI(bi(c.hasInvoke)), cellI(int64(c.nMagic)), cellI(int64(n)),
			cellS(g.atLoc(c.fileID, c.line)))
	}
	insertionSort(b.r.rows, func(a, c []cell) bool {
		if a[5].i != c[5].i {
			return a[5].i > c[5].i
		}
		return a[4].i > c[4].i
	})
	return b.done()
}

func splitList(s string) []string {
	if s == "" {
		return nil
	}
	parts := strings.Split(s, ",")
	out := parts[:0]
	for _, p := range parts {
		if p != "" {
			out = append(out, p)
		}
	}
	if len(out) == 0 {
		return nil
	}
	return out
}

func fqnWithoutNS(fqn string) string {
	if _, after, ok := strings.Cut(fqn, "\\"); ok {
		return after
	}
	return fqn
}

func qIfaceCoverage(g *graph, mod string, limit int) *result {
	b := newR("iface", "namespace", "implementors", "iface_methods", "at")

	impl := make(map[int32][]string, len(g.classes))
	for i := range g.classes {
		if toks := splitList(g.sa.str(g.classes[i].impl)); len(toks) > 0 {
			impl[g.classes[i].sym] = toks
		}
	}
	for i := range g.classes {
		iface := &g.classes[i]
		if !g.sa.eq(iface.kind, "interface") {
			continue
		}
		if !sqlLike(g.modOfSym(int(iface.sym)), mod) {
			continue
		}
		short := fqnWithoutNS(g.sa.str(iface.fqn))
		ifaceName := g.sa.str(iface.name)
		seen := map[int32]bool{}
		for cid, toks := range impl {
			for _, t := range toks {
				if t == ifaceName || t == short {
					seen[cid] = true
					break
				}
			}
		}
		b.row(cellS(g.sa.str(iface.name)), cellS(g.sa.str(iface.ns)), cellI(int64(len(seen))),
			cellI(int64(iface.nMethods)), cellS(g.atLoc(iface.fileID, iface.line)))
	}
	insertionSort(b.r.rows, func(a, c []cell) bool {
		if a[2].i != c[2].i {
			return a[2].i > c[2].i
		}
		if a[3].i != c[3].i {
			return a[3].i > c[3].i
		}
		return a[0].s < c[0].s
	})
	return b.done()
}

func qAbstractHooks(g *graph, mod string, limit int) *result {
	b := newR("abstract_class", "namespace", "final_", "concrete_subclasses", "at")
	parents := make(map[string]map[int32]bool)
	for i := range g.classes {
		for _, t := range splitList(g.sa.str(g.classes[i].ext)) {
			s := parents[t]
			if s == nil {
				s = map[int32]bool{}
				parents[t] = s
			}
			s[g.classes[i].sym] = true
		}
	}
	for i := range g.classes {
		c := &g.classes[i]
		if !c.isAbstract {
			continue
		}
		if !sqlLike(g.modOfSym(int(c.sym)), mod) {
			continue
		}
		short := fqnWithoutNS(g.sa.str(c.fqn))
		cName := g.sa.str(c.name)
		n := 0
		seen := map[int32]bool{}
		for key, set := range parents {
			if key != cName && key != short {
				continue
			}
			for cid := range set {
				if !seen[cid] {
					seen[cid] = true
					n++
				}
			}
		}
		b.row(cellS(g.sa.str(c.name)), cellS(g.sa.str(c.ns)), cellI(bi(c.isFinal)), cellI(int64(n)),
			cellS(g.atLoc(c.fileID, c.line)))
	}
	insertionSort(b.r.rows, func(a, c []cell) bool {
		if a[3].i != c[3].i {
			return a[3].i < c[3].i
		}
		return a[0].s < c[0].s
	})
	return b.done()
}

func containsStr(list []string, v string) bool {
	return slices.Contains(list, v)
}

func reachSeeds(g *graph, pred func(int) bool, depth int) []reachHit {
	var seeds []int32
	for i := 0; i < g.sym.n; i++ {
		if pred(i) {
			seeds = append(seeds, int32(i))
		}
	}
	return reachGroups(g.reachable(seeds, depth, g.adj))
}

func qUnpreparedSQL(g *graph, mod string, limit int) *result {
	b := newR("path", "fn", "callee", "driver", "build_kind", "in_loop", "fan_in")
	for i := range g.sqlSites {
		st := &g.sqlSites[i]
		if st.prepared {
			continue
		}
		switch g.sa.str(st.buildKind) {
		case "interp", "concat", "format":
		default:
			continue
		}
		s := int(st.sym)
		if st.symNull {
			s = -1
		}
		f := g.file(st.fileID)
		if f == nil || f.isGen != 0 {
			continue
		}
		mname := ""
		fanIn := int32(0)
		if s >= 0 {
			mname = g.modOfSym(s)
			fanIn = g.col(s, cFanIn)
		} else {
			mname = g.moduleName(f.moduleID)
		}
		if !sqlLike(mname, mod) {
			continue
		}
		name := ""
		if s >= 0 {
			name = g.sym.str(cName, s)
		}
		b.row(cellS(g.sa.str(f.path)), cellS(name), cellS(g.sa.str(st.callee)), cellS(g.sa.str(st.driver)),
			cellS(g.sa.str(st.buildKind)), cellI(bi(st.inLoop)), cellI(int64(fanIn)))
	}
	insertionSort(b.r.rows, func(a, c []cell) bool {
		if a[5].i != c[5].i {
			return a[5].i > c[5].i
		}
		return a[6].i > c[6].i
	})
	return b.done()
}

var ssrfSinks = map[string]bool{
	"curl_exec": true, "curl_multi_exec": true, "file_get_contents": true,
	"fopen": true, "fsockopen": true,
}

func qSSRFFrontier(g *graph, mod string, limit int) *result {
	b := newR("path", "fn", "fan_in", "reads", "fetch_sink")
	bySym := perSymbolHaz(g.hazards)
	seen := map[[3]int32]bool{}
	for i := range g.superglobals {
		r := &g.superglobals[i]
		if !r.psalm || r.symNull {
			continue
		}
		s := int(r.sym)

		f := g.file(g.sym.cols[cFileID][s])
		if f == nil || f.isGen != 0 || !sqlLike(g.modOfSym(s), mod) {
			continue
		}
		for _, h := range bySym[r.sym] {
			pat := g.sa.str(h.pattern)
			if !ssrfSinks[pat] {
				continue
			}
			k := [3]int32{r.sym, int32(len(pat)), 0}
			if seen[k] {
				continue
			}
			seen[k] = true
			b.row(cellS(g.sa.str(f.path)), cellS(g.sym.str(cName, s)),
				cellI(int64(g.col(s, cFanIn))), cellS(g.sa.str(r.v)), cellS(pat))
		}
	}
	insertionSort(b.r.rows, func(a, c []cell) bool { return a[2].i > c[2].i })
	return b.done()
}

func qImplicitNullable(g *graph, mod string, limit int) *result {
	b := newR("path", "fn", "param", "type", "fan_in")
	for _, p := range g.params {
		if !g.sa.eq(p.def, "null") || p.typ.Len == 0 {
			continue
		}
		ptyp := g.sa.str(p.typ)
		if strings.HasPrefix(ptyp, "?") || p.null {
			continue
		}
		s := int(p.sym)
		f := g.file(g.sym.cols[cFileID][s])
		if f == nil || f.isGen != 0 || !sqlLike(g.modOfSym(s), mod) {
			continue
		}
		b.row(cellS(g.sa.str(f.path)), cellS(g.sym.str(cName, s)), cellS(g.sa.str(p.name)),
			cellS(ptyp), cellI(int64(g.col(s, cFanIn))))
	}
	insertionSort(b.r.rows, func(a, c []cell) bool { return a[4].i > c[4].i })
	return b.done()
}

func qDeprecatedAPI(g *graph, mod string, limit int) *result {
	b := newR("fn", "class_", "n_callers", "fan_in", "at")
	callers := make(map[int32]map[int32]bool)
	for i := range g.edges {
		e := &g.edges[i]
		m := callers[e.callee]
		if m == nil {
			m = map[int32]bool{}
			callers[e.callee] = m
		}
		m[e.caller] = true
	}
	for s := 0; s < g.sym.n; s++ {
		if g.col(s, cIsDeprecated) != 1 {
			continue
		}

		if len(callers[int32(s)]) == 0 {
			continue
		}
		if g.isGenFileOfSym(s) || !sqlLike(g.modOfSym(s), mod) {
			continue
		}
		b.row(cellS(g.sym.str(cName, s)), cellS(g.sym.str(cClassName, s)),
			cellI(int64(len(callers[int32(s)]))), cellI(int64(g.col(s, cFanIn))),
			cellS(g.at(s)))
	}
	insertionSort(b.r.rows, func(a, c []cell) bool { return a[2].i > c[2].i })
	return b.done()
}

func qBroadCatch(g *graph, mod string, limit int) *result {
	return g.scan([]string{"path", "fn", "broad_catches", "catches_total", "fan_in"},
		symFilter{notTest: true, mod: mod, pred: func(g *graph, s int) bool {
			return g.col(s, cNCatchBroad) > 0
		}},
		func(g *graph, s int) []cell {
			f := g.file(g.sym.cols[cFileID][s])
			p := ""
			if f != nil {
				p = g.sa.str(f.path)
			}
			return []cell{cellS(p), cellS(g.sym.str(cName, s)),
				cellI(int64(g.col(s, cNCatchBroad))), cellI(int64(g.col(s, cNCatch))),
				cellI(int64(g.col(s, cFanIn)))}
		},
		func(a, c []cell) bool {
			if a[2].i != c[2].i {
				return a[2].i > c[2].i
			}
			return a[4].i > c[4].i
		})
}

func qDynamicPropWrite(g *graph, mod string, limit int) *result {

	magic := map[int32]bool{}
	for i := range g.magic {
		m := &g.magic[i]
		if m.classIDNull {
			continue
		}
		if g.sa.eq(m.method, "__get") || g.sa.eq(m.method, "__set") {
			magic[m.classID] = true
		}
	}
	b := newR("path", "fn", "class_", "dyn_writes", "fan_in")
	for s := 0; s < g.sym.n; s++ {
		if g.col(s, cNDynamicPropWrite) <= 0 {
			continue
		}
		if g.isTestFileOfSym(s) || !sqlLike(g.modOfSym(s), mod) {
			continue
		}
		if magic[g.sym.cols[cParentID][s]] {
			continue
		}
		f := g.file(g.sym.cols[cFileID][s])
		p := ""
		if f != nil {
			p = g.sa.str(f.path)
		}
		b.row(cellS(p), cellS(g.sym.str(cName, s)), cellS(g.sym.str(cClassName, s)),
			cellI(int64(g.col(s, cNDynamicPropWrite))), cellI(int64(g.col(s, cFanIn))))
	}
	insertionSort(b.r.rows, func(a, c []cell) bool {
		if a[3].i != c[3].i {
			return a[3].i > c[3].i
		}
		return a[4].i > c[4].i
	})
	return b.done()
}

func qBoolFlags(g *graph, mod string, limit int) *result {
	b := newR("path", "fn", "param", "fan_in")
	lastPos := make(map[int32]int32, len(g.params))
	for i := range g.params {
		lastPos[g.params[i].sym] = g.params[i].pos
	}
	for i := range g.params {
		p := &g.params[i]
		if !g.sa.eq(p.def, "false") || p.pos != lastPos[p.sym] {
			continue
		}
		s := int(p.sym)
		if !kindFnMeth(g.sym.str(cKind, s)) {
			continue
		}
		if g.col(s, cFanIn) <= 0 || g.isGenFileOfSym(s) || !sqlLike(g.modOfSym(s), mod) {
			continue
		}
		f := g.file(g.sym.cols[cFileID][s])
		p2 := ""
		if f != nil {
			p2 = g.sa.str(f.path)
		}
		b.row(cellS(p2), cellS(g.sym.str(cName, s)), cellS(g.sa.str(p.name)),
			cellI(int64(g.col(s, cFanIn))))
	}
	insertionSort(b.r.rows, func(a, c []cell) bool { return a[3].i > c[3].i })
	return b.done()
}

func qNPath(g *graph, mod string, limit int) *result {
	b := newR("name", "cyclo", "sloc", "npath_est", "fan_in", "at")
	for s := 0; s < g.sym.n; s++ {
		if g.sym.str(cKind, s) != "function" || g.col(s, cCyclomatic) < 8 {
			continue
		}
		if g.isTestFileOfSym(s) || !sqlLike(g.modOfSym(s), mod) {
			continue
		}
		c := g.col(s, cCyclomatic)
		if c > 20 {
			c = 20
		}
		b.row(cellS(g.sym.str(cName, s)), cellI(int64(g.col(s, cCyclomatic))),
			cellI(int64(g.col(s, cSloc))), cellI(int64(int64(1)<<uint(c))),
			cellI(int64(g.col(s, cFanIn))), cellS(g.at(s)))
	}
	insertionSort(b.r.rows, func(a, c []cell) bool {
		if a[3].i != c[3].i {
			return a[3].i > c[3].i
		}
		return a[4].i > c[4].i
	})
	return b.done()
}

func qMaintainability(g *graph, mod string, limit int) *result {
	b := newR("name", "mi", "cyclo", "volume", "sloc", "fan_in", "at")
	for s := 0; s < g.sym.n; s++ {
		if g.sym.str(cKind, s) != "function" || g.col(s, cMaintainability) <= 0 ||
			g.col(s, cSloc) < 10 {
			continue
		}
		if g.isTestFileOfSym(s) || !sqlLike(g.modOfSym(s), mod) {
			continue
		}
		b.row(cellS(g.sym.str(cName, s)), cellI(int64(g.col(s, cMaintainability))),
			cellI(int64(g.col(s, cCyclomatic))), cellI(g.sym.getWide(s)),
			cellI(int64(g.col(s, cSloc))), cellI(int64(g.col(s, cFanIn))), cellS(g.at(s)))
	}
	insertionSort(b.r.rows, func(a, c []cell) bool { return a[1].i < c[1].i })
	return b.done()
}

func qEnvOutsideConfig(g *graph, mod string, limit int) *result {
	b := newR("name", "class_", "env_reads", "caller_hops", "callers_up",
		"runtime_entry_reaches", "fan_in", "controller", "at")

	ancs := make(map[int32]map[int32]int32)
	var seeds []int32
	for i := 0; i < g.sym.n; i++ {
		if g.col(i, cNConfig) > 0 {
			seeds = append(seeds, int32(i))
		}
	}
	for _, s := range seeds {
		m := map[int32]int32{s: 0}
		ancs[s] = m
		frontier := []int32{s}
		seen := map[int32]bool{s: true}
		for d := int32(1); d <= 2 && len(frontier) > 0; d++ {
			var next []int32
			for _, u := range frontier {
				for k := g.adj.inOff[u]; k < g.adj.inOff[u+1]; k++ {
					c := g.adj.inTo[k]
					if seen[c] {
						continue
					}
					seen[c] = true
					m[c] = d
					next = append(next, c)
				}
			}
			frontier = next
		}
	}
	syms := make([]int32, 0, len(ancs))
	for k := range ancs {
		syms = append(syms, k)
	}
	insertionSortAny(syms, func(x, y int32) bool { return x < y })
	for _, sym := range syms {
		s := int(sym)
		f := g.file(g.sym.cols[cFileID][s])
		if f == nil || f.isTest != 0 || f.isGen != 0 ||
			strings.Contains("/"+g.sa.str(f.path), "/config/") || !sqlLike(g.modOfSym(s), mod) {
			continue
		}
		hops, up, entry := int32(-1), int32(0), int32(0)
		for anc, d := range ancs[sym] {
			if anc == sym {
				continue
			}
			a := int(anc)
			if g.isTestFileOfSym(a) {
				continue
			}
			if hops < 0 || d < hops {
				hops = d
			}
			up++
			if g.col(a, cIsEntrypoint) != 0 {
				entry = 1
			}
		}
		b.row(cellS(g.sym.str(cName, s)), cellS(g.sym.str(cClassName, s)),
			cellI(int64(g.col(s, cNConfig))), nullableI(hops, hops < 0), cellI(int64(up)),
			cellI(int64(entry)), cellI(int64(g.col(s, cFanIn))),
			cellI(int64(g.col(s, cIsController))), cellS(g.at(s)))
	}
	insertionSort(b.r.rows, func(a, c []cell) bool {
		if a[5].i != c[5].i {
			return a[5].i > c[5].i
		}
		if a[6].i != c[6].i {
			return a[6].i > c[6].i
		}
		return a[2].i > c[2].i
	})
	return b.done()
}

func qDispatchInTx(g *graph, mod string, limit int) *result {
	b := newR("opens_tx", "dispatches", "hops", "dispatch_calls", "after_commit_sites",
		"dispatch_kinds", "patterns", "writes_in_tx_fn", "fan_in", "at")
	bySym := perSymbolHaz(g.hazards)
	type grp struct {
		tx, sink, hops int32
		afterCommit    int32
		kinds          int
		patterns       []string
	}
	var groups []grp
	idx := map[[2]int32]int{}
	for _, h := range reachSeeds(g, func(s int) bool { return g.col(s, cNTransaction) > 0 }, 3) {
		s := int(h.sym)
		if g.col(s, cNQueue) <= 0 || g.isTestFileOfSym(s) || !sqlLike(g.modOfSym(s), mod) {
			continue
		}
		var pats []string
		after := int32(0)
		kindSet := map[string]bool{}
		for _, hz := range bySym[h.sym] {
			if !g.sa.eq(hz.category, "queue") {
				continue
			}
			pat := g.sa.str(hz.pattern)
			pats = append(pats, pat)
			kindSet[pat] = true
			if pat == "dispatchAfterCommit" && hz.n > 0 {
				after++
			}
		}
		k := [2]int32{h.src, h.sym}
		if j, ok := idx[k]; ok {
			groups[j].patterns = append(groups[j].patterns, pats...)
			groups[j].afterCommit += after
			groups[j].kinds += len(kindSet)
			if h.depth < groups[j].hops {
				groups[j].hops = h.depth
			}
			continue
		}
		idx[k] = len(groups)
		groups = append(groups, grp{h.src, h.sym, h.depth, after, len(kindSet), pats})
	}
	for _, gr := range groups {
		s := int(gr.sink)

		b.row(cellS(g.sym.str(cName, int(gr.tx))), cellS(g.sym.str(cName, s)),
			cellI(int64(gr.hops)), cellI(int64(g.col(s, cNQueue))),
			cellI(int64(gr.afterCommit)),
			cellI(int64(len(splitList(groupConcat(gr.patterns))))),
			cellS(groupConcat(gr.patterns)),
			cellI(int64(g.col(int(gr.tx), cNWrite))), cellI(int64(g.col(int(gr.tx), cFanIn))),
			cellS(g.at(s)))
	}
	insertionSort(b.r.rows, func(a, c []cell) bool {
		if a[4].i != c[4].i {
			return a[4].i < c[4].i
		}
		if a[2].i != c[2].i {
			return a[2].i < c[2].i
		}
		return a[3].i > c[3].i
	})
	return b.done()
}

func qMultiWrite(g *graph, mod string, limit int) *result {
	b := newR("name", "class_", "n_writes", "write_kinds", "writes_in_callees",
		"tx_here", "controller", "fan_in", "at")
	type wacc struct {
		n     int32
		kinds map[string]bool
	}
	own := make(map[int32]*wacc)
	sub := make(map[int32]int32)
	for i := range g.hazards {
		h := &g.hazards[i]
		if !g.sa.eq(h.category, "write") {
			continue
		}
		w := own[h.sym]
		if w == nil {
			w = &wacc{kinds: map[string]bool{}}
			own[h.sym] = w
		}
		w.n += h.n
		w.kinds[g.sa.str(h.pattern)] = true
	}
	for i := range g.edges {
		e := &g.edges[i]
		if e.isSelf {
			continue
		}
		if w := own[e.callee]; w != nil {
			sub[e.caller] += w.n
		}
	}

	for s := 0; s < g.sym.n; s++ {
		w := own[int32(s)]
		if w == nil {
			continue
		}
		if w.n+sub[int32(s)] < 2 || g.col(s, cNTransaction) != 0 {
			continue
		}
		if !kindFnMeth(g.sym.str(cKind, s)) || g.isTestFileOfSym(s) ||
			!sqlLike(g.modOfSym(s), mod) {
			continue
		}
		b.row(cellS(g.sym.str(cName, s)), cellS(g.sym.str(cClassName, s)),
			cellI(int64(w.n)), cellI(int64(len(w.kinds))), cellI(int64(sub[int32(s)])),
			cellI(int64(g.col(s, cNTransaction))), cellI(int64(g.col(s, cIsController))),
			cellI(int64(g.col(s, cFanIn))), cellS(g.at(s)))
	}
	insertionSort(b.r.rows, func(a, c []cell) bool {
		if a[2].i != c[2].i {
			return a[2].i > c[2].i
		}
		if a[4].i != c[4].i {
			return a[4].i > c[4].i
		}
		return a[7].i > c[7].i
	})
	return b.done()
}

func reachFromRoots(g *graph, mod string, depth int, cols []string,
	seedPred func(int) bool,
	keep func(sink int) bool,
	proj func(g *graph, root, sink int, hops int32) []cell,
	sinkFirst bool,
	order func(a, c []cell) bool) *result {
	b := newR(cols...)
	idx := map[[2]int32]int{}
	type grp struct {
		root, sink, hops int32
	}
	var groups []grp
	for _, h := range reachSeeds(g, seedPred, depth) {
		if h.depth == 0 {
			continue
		}
		s := int(h.sym)
		if !keep(s) || g.isTestFileOfSym(s) || !sqlLike(g.modOfSym(s), mod) {
			continue
		}
		k := [2]int32{h.src, h.sym}
		if j, ok := idx[k]; ok {
			if h.depth < groups[j].hops {
				groups[j].hops = h.depth
			}
			continue
		}
		idx[k] = len(groups)
		groups = append(groups, grp{h.src, h.sym, h.depth})
	}
	if sinkFirst {
		insertionSortAny(groups, func(a, c grp) bool {
			if a.sink != c.sink {
				return a.sink < c.sink
			}
			return a.root < c.root
		})
	} else {
		insertionSortAny(groups, func(a, c grp) bool {
			if a.root != c.root {
				return a.root < c.root
			}
			return a.sink < c.sink
		})
	}
	for _, gr := range groups {
		b.row(proj(g, int(gr.root), int(gr.sink), gr.hops)...)
	}
	if order != nil {
		insertionSort(b.r.rows, order)
	}
	return b.done()
}

func qRawSQLBelowController(g *graph, mod string, limit int) *result {
	return reachFromRoots(g, mod, 4,
		[]string{"builds_sql", "reached_from", "hops", "sql_interp", "sql_concat",
			"prepared", "literal_sql", "fan_in", "at"},
		func(s int) bool {
			f := g.file(g.sym.cols[cFileID][s])
			return (g.col(s, cIsController) == 1 || g.col(s, cIsEntrypoint) == 1) &&
				f != nil && f.isTest == 0
		},
		func(s int) bool { return g.col(s, cNSQLInterp) > 0 || g.col(s, cNSQLConcat) > 0 },
		func(g *graph, root, sink int, hops int32) []cell {
			return []cell{cellS(g.sym.str(cName, sink)), cellS(g.sym.str(cName, root)),
				cellI(int64(hops)), cellI(int64(g.col(sink, cNSQLInterp))),
				cellI(int64(g.col(sink, cNSQLConcat))),
				cellI(int64(g.col(sink, cNSQLPrepared))),
				cellI(int64(g.col(sink, cNSQLLiteral))),
				cellI(int64(g.col(sink, cFanIn))), cellS(g.at(sink))}
		},
		false,
		func(a, c []cell) bool {
			if a[2].i != c[2].i {
				return a[2].i < c[2].i
			}
			if a[3].i != c[3].i {
				return a[3].i > c[3].i
			}
			return a[4].i > c[4].i
		})
}

func qFileSinkFrontier(g *graph, mod string, limit int) *result {
	bySym := perSymbolHaz(g.hazards)
	b := newR("reads_input", "touches_files", "hops", "dyn_opens", "dyn_writes",
		"delete_or_move", "psalm_tainted_reads", "file_calls", "fan_in", "at")
	type grp struct {
		src, sink, hops int32
		pats            []string
	}
	var groups []grp
	idx := map[[2]int32]int{}
	for _, h := range reachSeeds(g, func(s int) bool { return g.col(s, cNSuperglobalReads) > 0 }, 3) {
		s := int(h.sym)
		if g.col(s, cNDynamicOpen) <= 0 && g.col(s, cNFileWriteDyn) <= 0 {
			continue
		}
		if g.isTestFileOfSym(s) || g.isTestFileOfSym(int(h.src)) ||
			!sqlLike(g.modOfSym(s), mod) {
			continue
		}
		var pats []string
		for _, hz := range bySym[h.sym] {
			switch g.sa.str(hz.pattern) {
			case "unlink", "rmdir", "rename", "copy":
				pats = append(pats, g.sa.str(hz.pattern))
			}
		}
		k := [2]int32{h.src, h.sym}
		if j, ok := idx[k]; ok {
			groups[j].pats = append(groups[j].pats, pats...)
			if h.depth < groups[j].hops {
				groups[j].hops = h.depth
			}
			continue
		}
		idx[k] = len(groups)
		groups = append(groups, grp{h.src, h.sym, h.depth, pats})
	}
	for _, gr := range groups {
		s, src := int(gr.sink), int(gr.src)
		b.row(cellS(g.sym.str(cName, src)), cellS(g.sym.str(cName, s)),
			cellI(int64(gr.hops)), cellI(int64(g.col(s, cNDynamicOpen))),
			cellI(int64(g.col(s, cNFileWriteDyn))),
			nullableS(groupConcat(gr.pats), len(gr.pats) == 0),
			cellI(int64(g.col(src, cNGet)+g.col(src, cNPost)+g.col(src, cNRequest))),
			cellI(int64(g.col(s, cNFile))), cellI(int64(g.col(s, cFanIn))), cellS(g.at(s)))
	}
	insertionSort(b.r.rows, func(a, c []cell) bool {
		if a[4].i != c[4].i {
			return a[4].i > c[4].i
		}
		if a[2].i != c[2].i {
			return a[2].i < c[2].i
		}
		return a[3].i > c[3].i
	})
	return b.done()
}

func qNullableReturn(g *graph, mod string, limit int) *result {
	b := newR("name", "class_", "return_type", "nullable_types", "null_guards",
		"call_sites", "fan_in", "public_", "strict_file", "at")
	for s := 0; s < g.sym.n; s++ {
		if !kindFnMeth(g.sym.str(cKind, s)) {
			continue
		}
		rt := g.sym.str(cReturnType, s)
		if rt == "" {
			continue
		}
		if !strings.HasPrefix(rt, "?") && !strings.Contains(rt, "null") {
			continue
		}
		if g.isTestFileOfSym(s) || g.isGenFileOfSym(s) || !sqlLike(g.modOfSym(s), mod) {
			continue
		}
		b.row(cellS(g.sym.str(cName, s)), cellS(g.sym.str(cClassName, s)),
			cellS(rt), cellI(int64(g.col(s, cNNullableTypes))),
			cellI(int64(g.col(s, cNNullCheck))), cellI(int64(g.col(s, cNCallsites))),
			cellI(int64(g.col(s, cFanIn))), cellI(int64(g.col(s, cIsPublic))),
			cellI(int64(g.col(s, cHasStrictTypes))), cellS(g.at(s)))
	}
	insertionSort(b.r.rows, func(a, c []cell) bool {
		if a[5].i != c[5].i {
			return a[5].i > c[5].i
		}
		return a[6].i > c[6].i
	})
	return b.done()
}

func qMixedPropagation(g *graph, mod string, limit int) *result {
	return reachFromRoots(g, mod, 3,
		[]string{"untyped_fn", "entry_", "hops", "untyped_params", "no_return_type",
			"n_params", "call_sites", "fan_in", "at"},
		func(s int) bool {
			f := g.file(g.sym.cols[cFileID][s])
			return g.col(s, cIsEntrypoint) == 1 && f != nil && f.isTest == 0
		},
		func(s int) bool {
			return (g.sym.str(cReturnType, s) == "" || g.col(s, cNUntypedParams) > 0) &&
				kindFnMethCl(g.sym.str(cKind, s))
		},
		func(g *graph, root, sink int, hops int32) []cell {
			noRet := int32(0)
			if g.sym.str(cReturnType, sink) == "" {
				noRet = 1
			}
			return []cell{cellS(g.sym.str(cName, sink)), cellS(g.sym.str(cName, root)),
				cellI(int64(hops)), cellI(int64(g.col(sink, cNUntypedParams))),
				cellI(int64(noRet)), cellI(int64(g.col(sink, cNParams))),
				cellI(int64(g.col(sink, cNCallsites))), cellI(int64(g.col(sink, cFanIn))),
				cellS(g.at(sink))}
		},
		true,
		func(a, c []cell) bool {
			if a[3].i != c[3].i {
				return a[3].i > c[3].i
			}
			if a[6].i != c[6].i {
				return a[6].i > c[6].i
			}
			return a[2].i < c[2].i
		})
}

func sinkReach(g *graph, mod string, depth int, cols []string,
	keep func(s int) bool,
	proj func(g *graph, sink int, hops int32, tainted int32) []cell,
	order func(a, c []cell) bool) *result {
	b := newR(cols...)
	best := map[int32]int32{}
	tainted := map[int32]int32{}
	bestTainted := map[int32]int32{}
	for _, h := range reachSeeds(g, func(s int) bool { return g.col(s, cNSuperglobalReads) > 0 }, depth) {
		s := int(h.sym)
		if !keep(s) || g.isTestFileOfSym(s) || g.isTestFileOfSym(int(h.src)) ||
			!sqlLike(g.modOfSym(s), mod) {
			continue
		}
		if d, ok := best[h.sym]; !ok || h.depth < d {
			best[h.sym] = h.depth
		}
		t := g.col(int(h.src), cNGet) + g.col(int(h.src), cNPost) +
			g.col(int(h.src), cNRequest) + g.col(int(h.src), cNCookie)
		tainted[h.sym] += t
		if t > bestTainted[h.sym] {
			bestTainted[h.sym] = t
		}
	}
	syms := make([]int32, 0, len(best))
	for k := range best {
		syms = append(syms, k)
	}
	insertionSortAny(syms, func(a, c int32) bool { return a < c })
	for _, sym := range syms {
		b.row(proj(g, int(sym), best[sym], bestTainted[sym])...)
	}
	if order != nil {
		insertionSort(b.r.rows, order)
	}
	return b.done()
}

func qInArrayLoose(g *graph, mod string, limit int) *result {
	return sinkReach(g, mod, 3,
		[]string{"in_fn", "hops", "loose_searches", "loose_cmp", "strict_cmp",
			"crypto_calls", "is_entrypoint", "tainted_reads", "at"},
		func(s int) bool { return g.col(s, cNInarrayLoose) > 0 },
		func(g *graph, sink int, hops, tainted int32) []cell {
			return []cell{cellS(g.sym.str(cName, sink)), cellI(int64(hops)),
				cellI(int64(g.col(sink, cNInarrayLoose))),
				cellI(int64(g.col(sink, cNLooseCompare))),
				cellI(int64(g.col(sink, cNStrictCompare))),
				cellI(int64(g.col(sink, cNCrypto))),
				cellI(int64(g.col(sink, cIsEntrypoint))), cellI(int64(tainted)),
				cellS(g.at(sink))}
		},
		func(a, c []cell) bool {
			if a[2].i != c[2].i {
				return a[2].i > c[2].i
			}
			if a[1].i != c[1].i {
				return a[1].i < c[1].i
			}
			return a[7].i > c[7].i
		})
}

func qRegexInjection(g *graph, mod string, limit int) *result {
	return sinkReach(g, mod, 2,
		[]string{"in_fn", "hops", "computed_patterns", "literal_regexes",
			"preg_in_loop", "tainted_reads", "fan_in", "at"},
		func(s int) bool { return g.col(s, cNPregDynamic) > 0 },
		func(g *graph, sink int, hops, tainted int32) []cell {
			return []cell{cellS(g.sym.str(cName, sink)), cellI(int64(hops)),
				cellI(int64(g.col(sink, cNPregDynamic))),
				cellI(int64(g.col(sink, cNRegexLit))),
				cellI(int64(g.col(sink, cNPregInLoop))), cellI(int64(tainted)),
				cellI(int64(g.col(sink, cFanIn))), cellS(g.at(sink))}
		},
		func(a, c []cell) bool {
			if a[2].i != c[2].i {
				return a[2].i > c[2].i
			}
			if a[1].i != c[1].i {
				return a[1].i < c[1].i
			}
			return a[4].i > c[4].i
		})
}

func qMassAssignment(g *graph, mod string, limit int) *result {
	b := newR("name", "class_", "massassign_calls", "request_reads", "super_reads",
		"has_fillable", "model", "fan_in", "at")
	for s := 0; s < g.sym.n; s++ {
		if g.col(s, cNMassassign) <= 0 {
			continue
		}
		if g.col(s, cNRequestInput) <= 0 && g.col(s, cNSuperglobalReads) <= 0 {
			continue
		}
		if g.isTestFileOfSym(s) || !sqlLike(g.modOfSym(s), mod) {
			continue
		}
		b.row(cellS(g.sym.str(cName, s)), cellS(g.sym.str(cClassName, s)),
			cellI(int64(g.col(s, cNMassassign))),
			cellI(int64(g.col(s, cNRequestInput))),
			cellI(int64(g.col(s, cNSuperglobalReads))),
			cellI(bi(hasFillable(g, g.sym.cols[cParentID][s]))),
			cellI(int64(g.col(s, cIsModel))), cellI(int64(g.col(s, cFanIn))),
			cellS(g.at(s)))
	}
	insertionSort(b.r.rows, func(a, c []cell) bool {
		if a[5].i != c[5].i {
			return a[5].i < c[5].i
		}
		if a[3].i != c[3].i {
			return a[3].i > c[3].i
		}
		return a[7].i > c[7].i
	})
	return b.done()
}

var fillableCache map[int32]bool

func hasFillable(g *graph, cls int32) bool {
	if fillableCache == nil {
		fillableCache = make(map[int32]bool, 64)
		for i := range g.fields {
			f := &g.fields[i]
			if g.sa.eq(f.name, "fillable") || g.sa.eq(f.name, "guarded") {
				fillableCache[f.sym] = true
			}
		}
	}
	return fillableCache[cls]
}

func qDebugReach(g *graph, mod string, limit int) *result {

	b := newR("debug_site", "reached_from", "hops", "debug_calls", "suppressed",
		"raw_echo", "fan_in", "at")
	idx := map[[2]int32]int{}
	type grp struct{ root, sink, hops int32 }
	var groups []grp
	for _, h := range reachSeeds(g, func(s int) bool {
		f := g.file(g.sym.cols[cFileID][s])
		return g.col(s, cIsEntrypoint) == 1 && f != nil && f.isTest == 0
	}, 3) {
		s := int(h.sym)
		if g.col(s, cNDebugCall) <= 0 || g.isTestFileOfSym(s) || !sqlLike(g.modOfSym(s), mod) {
			continue
		}
		k := [2]int32{h.src, h.sym}
		if j, ok := idx[k]; ok {
			if h.depth < groups[j].hops {
				groups[j].hops = h.depth
			}
			continue
		}
		idx[k] = len(groups)
		groups = append(groups, grp{h.src, h.sym, h.depth})
	}
	for _, gr := range groups {
		s := int(gr.sink)
		b.row(cellS(g.sym.str(cName, s)), cellS(g.sym.str(cName, int(gr.root))),
			cellI(int64(gr.hops)), cellI(int64(g.col(s, cNDebugCall))),
			cellI(int64(g.col(s, cNErrorSuppress))), cellI(int64(g.col(s, cNRawEcho))),
			cellI(int64(g.col(s, cFanIn))), cellS(g.at(s)))
	}
	insertionSort(b.r.rows, func(a, c []cell) bool {
		if a[2].i != c[2].i {
			return a[2].i < c[2].i
		}
		if a[3].i != c[3].i {
			return a[3].i > c[3].i
		}
		return a[5].i > c[5].i
	})
	return b.done()
}

func qSessionWrite(g *graph, mod string, limit int) *result {
	return g.scan([]string{"name", "session_writes", "super_reads", "request_reads",
		"session_reads", "session_calls", "escapes", "fan_in", "at"},
		symFilter{notTest: true, mod: mod, pred: func(g *graph, s int) bool {
			return g.col(s, cNSessionWrite) > 0 &&
				(g.col(s, cNSuperglobalReads) > 0 || g.col(s, cNRequestInput) > 0)
		}},
		func(g *graph, s int) []cell {
			return []cell{cellS(g.sym.str(cName, s)),
				cellI(int64(g.col(s, cNSessionWrite))),
				cellI(int64(g.col(s, cNSuperglobalReads))),
				cellI(int64(g.col(s, cNRequestInput))),
				cellI(int64(g.col(s, cNSession))), cellI(int64(g.col(s, cNSessionCall))),
				cellI(int64(g.col(s, cNEscapedOutput))), cellI(int64(g.col(s, cFanIn))),
				cellS(g.at(s))}
		},
		func(a, c []cell) bool {
			if a[1].i != c[1].i {
				return a[1].i > c[1].i
			}
			return a[2].i > c[2].i
		})
}

func qSuperglobalToHeader(g *graph, mod string, limit int) *result {
	bySym := perSymbolHaz(g.hazards)
	b := newR("reads_input", "writes_headers", "hops", "header_calls",
		"header_kinds", "patterns", "psalm_tainted_reads", "fan_in", "at")
	type grp struct {
		src, sink, hops int32
		pats            []string
	}
	var groups []grp
	idx := map[[2]int32]int{}
	for _, h := range reachSeeds(g, func(s int) bool { return g.col(s, cNSuperglobalReads) > 0 }, 3) {
		s := int(h.sym)
		if !(g.col(s, cNHeader) > 0 || g.col(s, cNHeaderCall) > 0) {
			continue
		}
		if g.isTestFileOfSym(s) || g.isTestFileOfSym(int(h.src)) || !sqlLike(g.modOfSym(s), mod) {
			continue
		}
		var pats []string
		for _, hz := range bySym[h.sym] {
			if g.sa.eq(hz.category, "header") {
				pats = append(pats, g.sa.str(hz.pattern))
			}
		}
		k := [2]int32{h.src, h.sym}
		if j, ok := idx[k]; ok {
			groups[j].pats = append(groups[j].pats, pats...)
			if h.depth < groups[j].hops {
				groups[j].hops = h.depth
			}
			continue
		}
		idx[k] = len(groups)
		groups = append(groups, grp{h.src, h.sym, h.depth, pats})
	}
	for _, gr := range groups {
		s, src := int(gr.sink), int(gr.src)
		b.row(cellS(g.sym.str(cName, src)), cellS(g.sym.str(cName, s)),
			cellI(int64(gr.hops)), cellI(int64(g.col(s, cNHeaderCall))),
			cellI(int64(len(splitList(groupConcat(gr.pats))))), cellS(groupConcat(gr.pats)),
			cellI(int64(g.col(src, cNGet)+g.col(src, cNPost)+g.col(src, cNCookie))),
			cellI(int64(g.col(s, cFanIn))), cellS(g.at(s)))
	}
	insertionSort(b.r.rows, func(a, c []cell) bool {
		if a[2].i != c[2].i {
			return a[2].i < c[2].i
		}
		if a[3].i != c[3].i {
			return a[3].i > c[3].i
		}
		return a[6].i > c[6].i
	})
	return b.done()
}

func qFacadeInModel(g *graph, mod string, limit int) *result {
	return g.scan([]string{"name", "class_", "facade_calls", "static_calls", "model",
		"sql_calls", "fan_in", "at"},
		symFilter{notTest: true, mod: mod, pred: func(g *graph, s int) bool {
			return g.col(s, cNFacadeCall) > 0 && g.col(s, cIsModel) == 1 &&
				kindFnMeth(g.sym.str(cKind, s))
		}},
		func(g *graph, s int) []cell {
			return []cell{cellS(g.sym.str(cName, s)), cellS(g.sym.str(cClassName, s)),
				cellI(int64(g.col(s, cNFacadeCall))), cellI(int64(g.col(s, cNStaticCalls))),
				cellI(int64(g.col(s, cIsModel))), cellI(int64(g.col(s, cNSQLCalls))),
				cellI(int64(g.col(s, cFanIn))), cellS(g.at(s))}
		},
		func(a, c []cell) bool {
			if a[2].i != c[2].i {
				return a[2].i > c[2].i
			}
			return a[6].i > c[6].i
		})
}

func qWriteInLoop(g *graph, mod string, limit int) *result {
	b := newR("name", "class_", "n_writes", "loop_depth", "call_in_loop", "n_loops",
		"tx_here", "fan_in", "at")
	writes := make(map[int32]int32)
	for i := range g.hazards {
		if g.sa.eq(g.hazards[i].category, "write") {
			writes[g.hazards[i].sym] += g.hazards[i].n
		}
	}
	syms := make([]int32, 0, len(writes))
	for k := range writes {
		syms = append(syms, k)
	}
	insertionSortAny(syms, func(a, c int32) bool { return a < c })
	for _, sym := range syms {
		s := int(sym)
		if g.col(s, cMaxLoopDepth) <= 0 {
			continue
		}
		if g.col(s, cCallInLoop) <= 0 && g.col(s, cQueryInLoop) <= 0 {
			continue
		}
		if g.isTestFileOfSym(s) || !sqlLike(g.modOfSym(s), mod) {
			continue
		}
		b.row(cellS(g.sym.str(cName, s)), cellS(g.sym.str(cClassName, s)),
			cellI(int64(writes[sym])), cellI(int64(g.col(s, cMaxLoopDepth))),
			cellI(int64(g.col(s, cCallInLoop))), cellI(int64(g.col(s, cNLoops))),
			cellI(int64(g.col(s, cNTransaction))), cellI(int64(g.col(s, cFanIn))),
			cellS(g.at(s)))
	}
	insertionSort(b.r.rows, func(a, c []cell) bool {
		ka := i64(a, 2) * i64(a, 3)
		kc := i64(c, 2) * i64(c, 3)
		if ka != kc {
			return ka > kc
		}
		return a[7].i > c[7].i
	})
	return b.done()
}

func qDynamicDispatch(g *graph, mod string, limit int) *result {
	return reachFromRoots(g, mod, 4,
		[]string{"dynamic_site", "reached_from", "hops", "evals",
			"variable_includes", "variable_news", "variable_vars", "fan_in", "at"},
		func(s int) bool {
			f := g.file(g.sym.cols[cFileID][s])
			return g.col(s, cIsEntrypoint) == 1 && f != nil && f.isTest == 0
		},
		func(s int) bool {
			return g.col(s, cNEval) > 0 || g.col(s, cNDynamicInclude) > 0 ||
				g.col(s, cNDynamicNew) > 0
		},
		func(g *graph, root, sink int, hops int32) []cell {
			return []cell{cellS(g.sym.str(cName, sink)), cellS(g.sym.str(cName, root)),
				cellI(int64(hops)), cellI(int64(g.col(sink, cNEval))),
				cellI(int64(g.col(sink, cNDynamicInclude))),
				cellI(int64(g.col(sink, cNDynamicNew))),
				cellI(int64(g.col(sink, cNVariableVar))),
				cellI(int64(g.col(sink, cFanIn))), cellS(g.at(sink))}
		},
		true,
		func(a, c []cell) bool {
			if a[2].i != c[2].i {
				return a[2].i < c[2].i
			}
			if a[3].i != c[3].i {
				return a[3].i > c[3].i
			}
			return a[4].i > c[4].i
		})
}

func qTraitCollision(g *graph, mod string, limit int) *result {
	b := newR("class_", "colliding_method", "n_traits", "traits_", "at")

	traitMethods := make(map[string]map[string]bool)
	for i := range g.traits {
		t := &g.traits[i]
		names := map[string]bool{}
		for j := 0; j < g.sym.n; j++ {
			if g.sym.cols[cParentID][j] == t.sym && g.sym.str(cKind, j) == "method" {
				names[g.sym.str(cName, j)] = true
			}
		}
		tn := g.sa.str(t.name)
		if _, ok := traitMethods[tn]; !ok {
			traitMethods[tn] = names
		}
	}
	seen := map[[2]int32]bool{}
	for i := range g.classes {
		c := &g.classes[i]
		tlist := g.sa.str(c.traitList)
		if tlist == "" || g.isTestFileOfSym(int(c.sym)) ||
			!sqlLike(g.modOfSym(int(c.sym)), mod) {
			continue
		}
		used := splitList(tlist)
		byMethod := map[string]map[string]bool{}
		for _, tn := range used {
			for m := range traitMethods[tn] {
				set := byMethod[m]
				if set == nil {
					set = map[string]bool{}
					byMethod[m] = set
				}
				set[tn] = true
			}
		}

		for _, m := range sortedKeys(byMethod) {
			set := byMethod[m]
			if len(set) < 2 {
				continue
			}
			kk := mapKey(c.sym, m)
			if seen[kk] {
				continue
			}
			seen[kk] = true
			var list []string
			for tn := range set {
				list = append(list, tn)
			}
			insertionSortAny(list, func(a, b string) bool { return a < b })
			b.row(cellS(g.sa.str(c.name)), cellS(m), cellI(int64(len(set))),
				cellS(strings.Join(list, ",")), cellS(g.atLoc(c.fileID, c.line)))
		}
	}
	insertionSort(b.r.rows, func(a, c []cell) bool {
		if a[2].i != c[2].i {
			return a[2].i > c[2].i
		}
		return a[0].s < c[0].s
	})
	return b.done()
}

func mapKey(sym int32, name string) [2]int32 {
	var h uint32 = 2166136261
	for i := 0; i < len(name); i++ {
		h ^= uint32(name[i])
		h *= 16777619
	}
	return [2]int32{sym, int32(h)}
}

func qRemoteCallInLoop(g *graph, mod string, limit int) *result {
	b := newR("name", "class_", "io_in_loop", "loop_depth", "remote_calls",
		"distinct_callers", "fan_in", "at")
	callers := callerSet(g)
	for s := 0; s < g.sym.n; s++ {
		if g.col(s, cIOInLoop) <= 0 || g.isTestFileOfSym(s) || !sqlLike(g.modOfSym(s), mod) {
			continue
		}
		b.row(cellS(g.sym.str(cName, s)), cellS(g.sym.str(cClassName, s)),
			cellI(int64(g.col(s, cIOInLoop))), cellI(int64(g.col(s, cMaxLoopDepth))),
			cellI(int64(g.col(s, cNRemoteFetch))),
			cellI(int64(len(callers[int32(s)]))), cellI(int64(g.col(s, cFanIn))),
			cellS(g.at(s)))
	}
	insertionSort(b.r.rows, func(a, c []cell) bool {
		if a[2].i != c[2].i {
			return a[2].i > c[2].i
		}
		return a[5].i > c[5].i
	})
	return b.done()
}

func qRegexInLoop(g *graph, mod string, limit int) *result {
	b := newR("name", "class_", "regex_in_loop", "preg_in_loop", "loop_depth",
		"distinct_callers", "fan_in", "at")
	callers := callerSet(g)
	for s := 0; s < g.sym.n; s++ {
		if g.col(s, cRegexInLoop) <= 0 && g.col(s, cNPregInLoop) <= 0 {
			continue
		}
		if g.isTestFileOfSym(s) || !sqlLike(g.modOfSym(s), mod) {
			continue
		}
		b.row(cellS(g.sym.str(cName, s)), cellS(g.sym.str(cClassName, s)),
			cellI(int64(g.col(s, cRegexInLoop))), cellI(int64(g.col(s, cNPregInLoop))),
			cellI(int64(g.col(s, cMaxLoopDepth))), cellI(int64(len(callers[int32(s)]))),
			cellI(int64(g.col(s, cFanIn))), cellS(g.at(s)))
	}
	insertionSort(b.r.rows, func(a, c []cell) bool {
		if a[2].i != c[2].i {
			return a[2].i > c[2].i
		}
		if a[3].i != c[3].i {
			return a[3].i > c[3].i
		}
		return a[5].i > c[5].i
	})
	return b.done()
}

var callerCache map[int32]map[int32]bool

func callerSet(g *graph) map[int32]map[int32]bool {
	if callerCache != nil {
		return callerCache
	}
	callerCache = make(map[int32]map[int32]bool, g.sym.n/4+8)
	for i := range g.edges {
		e := &g.edges[i]
		if e.isSelf {
			continue
		}
		m := callerCache[e.callee]
		if m == nil {
			m = map[int32]bool{}
			callerCache[e.callee] = m
		}
		m[e.caller] = true
	}
	return callerCache
}

func qCookieFlags(g *graph, mod string, limit int) *result {
	return g.scan([]string{"name", "lean_cookie_calls", "header_calls", "session_calls",
		"auth_calls", "fan_in", "at"},
		symFilter{notTest: true, mod: mod, pred: func(g *graph, s int) bool {
			return g.col(s, cNCookieLean) > 0
		}},
		func(g *graph, s int) []cell {
			return []cell{cellS(g.sym.str(cName, s)), cellI(int64(g.col(s, cNCookieLean))),
				cellI(int64(g.col(s, cNHeaderCall))), cellI(int64(g.col(s, cNSessionCall))),
				cellI(int64(g.col(s, cNAuthCall))), cellI(int64(g.col(s, cFanIn))),
				cellS(g.at(s))}
		},
		func(a, c []cell) bool {
			if a[1].i != c[1].i {
				return a[1].i > c[1].i
			}
			return a[5].i > c[5].i
		})
}

func qGlobalState(g *graph, mod string, limit int) *result {
	return g.scan([]string{"name", "class_", "global_statements", "super_reads",
		"assigns", "fan_in", "call_sites", "at"},
		symFilter{notTest: true, mod: mod, pred: func(g *graph, s int) bool {
			return g.col(s, cNGlobals) > 0 && kindFnMethCl(g.sym.str(cKind, s))
		}},
		func(g *graph, s int) []cell {
			return []cell{cellS(g.sym.str(cName, s)), cellS(g.sym.str(cClassName, s)),
				cellI(int64(g.col(s, cNGlobals))), cellI(int64(g.col(s, cNSuperglobalReads))),
				cellI(int64(g.col(s, cNAssign))), cellI(int64(g.col(s, cFanIn))),
				cellI(int64(g.col(s, cNCallsites))), cellS(g.at(s))}
		},
		func(a, c []cell) bool {
			if a[5].i != c[5].i {
				return a[5].i > c[5].i
			}
			return a[2].i > c[2].i
		})
}

func qReflectionFrontier(g *graph, mod string, limit int) *result {
	return sinkReach(g, mod, 3,
		[]string{"reflects", "hops", "reflect_calls", "tainted_reads",
			"variable_news", "fan_in", "at"},
		func(s int) bool { return g.col(s, cNReflect) > 0 },
		func(g *graph, sink int, hops, tainted int32) []cell {
			return []cell{cellS(g.sym.str(cName, sink)), cellI(int64(hops)),
				cellI(int64(g.col(sink, cNReflect))), cellI(int64(tainted)),
				cellI(int64(g.col(sink, cNDynamicNew))),
				cellI(int64(g.col(sink, cFanIn))), cellS(g.at(sink))}
		},
		func(a, c []cell) bool {
			if a[1].i != c[1].i {
				return a[1].i < c[1].i
			}
			return a[2].i > c[2].i
		})
}

func qCallableFrontier(g *graph, mod string, limit int) *result {
	bySym := perSymbolHaz(g.hazards)
	b := newR("invokes", "hops", "callable_kinds", "patterns", "tainted_reads",
		"dynamic_calls", "fan_in", "at")
	best := map[int32]int32{}
	tainted := map[int32]int32{}
	kinds := map[int32][]string{}
	for _, h := range reachSeeds(g, func(s int) bool { return g.col(s, cNSuperglobalReads) > 0 }, 3) {
		s := int(h.sym)
		var pats []string
		for _, hz := range bySym[h.sym] {
			if g.sa.eq(hz.category, "callable") {
				pats = append(pats, g.sa.str(hz.pattern))
			}
		}
		if len(pats) == 0 {
			continue
		}
		if g.isTestFileOfSym(s) || g.isTestFileOfSym(int(h.src)) || !sqlLike(g.modOfSym(s), mod) {
			continue
		}
		if d, ok := best[h.sym]; !ok || h.depth < d {
			best[h.sym] = h.depth
		}
		kinds[h.sym] = append(kinds[h.sym], pats...)
		t := g.col(int(h.src), cNGet) + g.col(int(h.src), cNPost) + g.col(int(h.src), cNRequest)
		if t > tainted[h.sym] {
			tainted[h.sym] = t
		}
	}
	syms := make([]int32, 0, len(best))
	for k := range best {
		syms = append(syms, k)
	}
	insertionSortAny(syms, func(a, c int32) bool { return a < c })
	for _, sym := range syms {
		s := int(sym)
		distinct := len(splitList(groupConcat(kinds[sym])))
		b.row(cellS(g.sym.str(cName, s)), cellI(int64(best[sym])), cellI(int64(distinct)),
			cellS(groupConcat(kinds[sym])), cellI(int64(tainted[sym])),
			cellI(int64(g.col(s, cNDynamicCall))), cellI(int64(g.col(s, cFanIn))),
			cellS(g.at(s)))
	}
	insertionSort(b.r.rows, func(a, c []cell) bool {
		if a[1].i != c[1].i {
			return a[1].i < c[1].i
		}
		if a[2].i != c[2].i {
			return a[2].i > c[2].i
		}
		return a[4].i > c[4].i
	})
	return b.done()
}

func qConstructorIO(g *graph, mod string, limit int) *result {
	return g.scan([]string{"name", "class_", "io_ops", "sql_calls", "net_calls",
		"file_ops", "construction_sites", "fan_in", "at"},
		symFilter{notTest: true, mod: mod, pred: func(g *graph, s int) bool {
			return g.sym.str(cName, s) == "__construct" && g.sym.str(cKind, s) == "method" &&
				g.col(s, cNIO)+g.col(s, cNSQLCalls)+g.col(s, cNNet)+g.col(s, cNFile) > 0
		}},
		func(g *graph, s int) []cell {
			return []cell{cellS(g.sym.str(cName, s)), cellS(g.sym.str(cClassName, s)),
				cellI(int64(g.col(s, cNIO))), cellI(int64(g.col(s, cNSQLCalls))),
				cellI(int64(g.col(s, cNNet))), cellI(int64(g.col(s, cNFile))),
				cellI(int64(g.col(s, cNCallsites))), cellI(int64(g.col(s, cFanIn))),
				cellS(g.at(s))}
		},
		func(a, c []cell) bool {
			if a[6].i != c[6].i {
				return a[6].i > c[6].i
			}
			if a[2].i != c[2].i {
				return a[2].i > c[2].i
			}
			return a[7].i > c[7].i
		})
}

func qStaticState(g *graph, mod string, limit int) *result {
	return g.scan([]string{"name", "class_", "static_writes", "scoped_calls",
		"fan_in", "at"},
		symFilter{notTest: true, mod: mod, pred: func(g *graph, s int) bool {
			return g.col(s, cNStaticPropWrite) > 0 && kindFnMethCl(g.sym.str(cKind, s))
		}},
		func(g *graph, s int) []cell {
			return []cell{cellS(g.sym.str(cName, s)), cellS(g.sym.str(cClassName, s)),
				cellI(int64(g.col(s, cNStaticPropWrite))),
				cellI(int64(g.col(s, cNStaticCalls))), cellI(int64(g.col(s, cFanIn))),
				cellS(g.at(s))}
		},
		func(a, c []cell) bool {
			if a[2].i != c[2].i {
				return a[2].i > c[2].i
			}
			return a[4].i > c[4].i
		})
}

func qSuperglobalInModel(g *graph, mod string, limit int) *result {
	return g.scan([]string{"name", "class_", "super_reads", "psalm_tainted_reads",
		"request_reads", "sql_calls", "fan_in", "at"},
		symFilter{notTest: true, mod: mod, pred: func(g *graph, s int) bool {
			return g.col(s, cIsModel) == 1 && g.col(s, cNSuperglobalReads) > 0 &&
				kindFnMeth(g.sym.str(cKind, s))
		}},
		func(g *graph, s int) []cell {
			return []cell{cellS(g.sym.str(cName, s)), cellS(g.sym.str(cClassName, s)),
				cellI(int64(g.col(s, cNSuperglobalReads))),
				cellI(int64(g.col(s, cNGet) + g.col(s, cNPost) +
					g.col(s, cNRequest) + g.col(s, cNCookie))),
				cellI(int64(g.col(s, cNRequestInput))),
				cellI(int64(g.col(s, cNSQLCalls))), cellI(int64(g.col(s, cFanIn))),
				cellS(g.at(s))}
		},
		func(a, c []cell) bool {
			if a[3].i != c[3].i {
				return a[3].i > c[3].i
			}
			return a[2].i > c[2].i
		})
}

func qControllerSQL(g *graph, mod string, limit int) *result {
	return g.scan([]string{"name", "class_", "sql_calls", "sql_interp", "sql_concat",
		"prepared", "super_reads", "fan_in", "at"},
		symFilter{notTest: true, mod: mod, pred: func(g *graph, s int) bool {
			return g.col(s, cIsController) == 1 &&
				(g.col(s, cNSQLCalls) > 0 || g.col(s, cNSQLInterp) > 0 ||
					g.col(s, cNSQLConcat) > 0) && kindFnMeth(g.sym.str(cKind, s))
		}},
		func(g *graph, s int) []cell {
			return []cell{cellS(g.sym.str(cName, s)), cellS(g.sym.str(cClassName, s)),
				cellI(int64(g.col(s, cNSQLCalls))), cellI(int64(g.col(s, cNSQLInterp))),
				cellI(int64(g.col(s, cNSQLConcat))), cellI(int64(g.col(s, cNSQLPrepared))),
				cellI(int64(g.col(s, cNSuperglobalReads))), cellI(int64(g.col(s, cFanIn))),
				cellS(g.at(s))}
		},
		func(a, c []cell) bool {
			if a[3].i != c[3].i {
				return a[3].i > c[3].i
			}
			if a[4].i != c[4].i {
				return a[4].i > c[4].i
			}
			return a[7].i > c[7].i
		})
}

func qCleartextFetch(g *graph, mod string, limit int) *result {
	return g.scan([]string{"name", "cleartext_fetches", "remote_fetches", "fan_in",
		"controller", "at"},
		symFilter{notTest: true, mod: mod, pred: func(g *graph, s int) bool {
			return g.col(s, cNCleartextFetch) > 0
		}},
		func(g *graph, s int) []cell {
			return []cell{cellS(g.sym.str(cName, s)),
				cellI(int64(g.col(s, cNCleartextFetch))),
				cellI(int64(g.col(s, cNRemoteFetch))), cellI(int64(g.col(s, cFanIn))),
				cellI(int64(g.col(s, cIsController))), cellS(g.at(s))}
		},
		func(a, c []cell) bool {
			if a[1].i != c[1].i {
				return a[1].i > c[1].i
			}
			return a[3].i > c[3].i
		})
}

func qSuperglobalToMail(g *graph, mod string, limit int) *result {
	bySym := perSymbolHaz(g.hazards)
	b := newR("reads_input", "sends_mail", "hops", "mail_patterns", "tainted_reads",
		"fan_in", "at")
	type grp struct {
		src, sink, hops int32
		pats            []string
	}
	var groups []grp
	idx := map[[2]int32]int{}
	for _, h := range reachSeeds(g, func(s int) bool { return g.col(s, cNSuperglobalReads) > 0 }, 2) {
		s := int(h.sym)
		var pats []string
		for _, hz := range bySym[h.sym] {
			if g.sa.eq(hz.pattern, "mail") {
				pats = append(pats, g.sa.str(hz.pattern))
			}
		}
		if len(pats) == 0 {
			continue
		}
		if g.isTestFileOfSym(s) || g.isTestFileOfSym(int(h.src)) || !sqlLike(g.modOfSym(s), mod) {
			continue
		}
		k := [2]int32{h.src, h.sym}
		if j, ok := idx[k]; ok {
			groups[j].pats = append(groups[j].pats, pats...)
			if h.depth < groups[j].hops {
				groups[j].hops = h.depth
			}
			continue
		}
		idx[k] = len(groups)
		groups = append(groups, grp{h.src, h.sym, h.depth, pats})
	}
	for _, gr := range groups {
		s, src := int(gr.sink), int(gr.src)
		b.row(cellS(g.sym.str(cName, src)), cellS(g.sym.str(cName, s)),
			cellI(int64(gr.hops)), cellS(groupConcat(gr.pats)),
			cellI(int64(g.col(src, cNGet)+g.col(src, cNPost)+g.col(src, cNRequest))),
			cellI(int64(g.col(s, cFanIn))), cellS(g.at(s)))
	}
	insertionSort(b.r.rows, func(a, c []cell) bool {
		if a[2].i != c[2].i {
			return a[2].i < c[2].i
		}
		return a[4].i > c[4].i
	})
	return b.done()
}

type reachHit struct{ src, sym, depth int32 }

type walkScratch struct {
	stamp []int32
	gen   int32
	cur   []int32
	next  []int32
}

func (w *walkScratch) longestWalk(root int32, bound int, adj *adjacency) int32 {
	n := len(adj.outOff) - 1
	if root < 0 || int(root) >= n {
		return 0
	}
	if len(w.stamp) < n {
		w.stamp = make([]int32, n)
	}
	cur, next := w.cur[:0], w.next[:0]
	cur = append(cur, root)
	var best int32
	for d := 1; d <= bound && len(cur) > 0; d++ {
		w.gen++
		next = next[:0]
		for _, u := range cur {
			for k := adj.outOff[u]; k < adj.outOff[u+1]; k++ {
				v := adj.outTo[k]
				if w.stamp[v] == w.gen {
					continue
				}
				w.stamp[v] = w.gen
				next = append(next, v)
			}
		}
		if len(next) == 0 {
			break
		}
		best = int32(d)
		cur, next = next, cur
	}
	w.cur, w.next = cur, next
	return best
}

func allReachHits(seeds []int32, depth int, adj *adjacency) []reachHit {
	var out []reachHit
	for _, seed := range seeds {
		seen := make(map[int32]bool)
		type item struct {
			sym   int32
			depth int32
		}
		frontier := []item{{seed, 0}}
		seen[seed] = true
		out = append(out, reachHit{seed, seed, 0})
		for d := int32(1); d <= int32(depth) && len(frontier) > 0; d++ {
			var next []item
			for _, u := range frontier {
				for k := adj.outOff[u.sym]; k < adj.outOff[u.sym+1]; k++ {
					v := adj.outTo[k]
					if seen[v] {
						continue
					}
					seen[v] = true
					out = append(out, reachHit{seed, v, d})
					next = append(next, item{v, d})
				}
			}
			frontier = next
		}
	}
	return out
}

func reachGroups(rt *reachTable) []reachHit {
	out := make([]reachHit, 0, len(rt.keys))
	for i, k := range rt.keys {
		out = append(out, reachHit{int32(k >> 32), int32(uint32(k)), rt.depth[i]})
	}
	return out
}

func perSymbolSites(rows []sqlSiteRow, sym func(sqlSiteRow) (int32, bool)) map[int32][]sqlSiteRow {
	m := map[int32][]sqlSiteRow{}
	for i := range rows {
		if s, ok := sym(rows[i]); ok {
			m[s] = append(m[s], rows[i])
		}
	}
	return m
}

func sqlSiteSym(r sqlSiteRow) (int32, bool) { return r.sym, !r.symNull }

func perSymbolDyn(rows []dynSiteRow) map[int32][]dynSiteRow {
	m := map[int32][]dynSiteRow{}
	for i := range rows {
		if !rows[i].symNull {
			m[rows[i].sym] = append(m[rows[i].sym], rows[i])
		}
	}
	return m
}

func perSymbolHaz(rows []hazardRow) map[int32][]hazardRow {
	m := map[int32][]hazardRow{}
	for i := range rows {
		m[rows[i].sym] = append(m[rows[i].sym], rows[i])
	}
	return m
}

func minLine(rows []sqlSiteRow) int32 {
	m := int32(1 << 30)
	for _, r := range rows {
		if r.line < m {
			m = r.line
		}
	}
	return m
}

func minLineD(rows []dynSiteRow) int32 {
	m := int32(1 << 30)
	for _, r := range rows {
		if r.line < m {
			m = r.line
		}
	}
	return m
}

func groupConcat(vals []string) string {
	seen := map[string]bool{}
	var out []string
	for _, v := range vals {
		if seen[v] {
			continue
		}
		seen[v] = true
		out = append(out, v)
	}
	return strings.Join(out, ",")
}

func buildQueries() []question {
	return []question{
		{
			name:  "superglobal-to-sql",
			title: "Attacker-controlled input reaching a SQL-building site, up to 4 hops",
			notes: `ANSWERS the injection question no single-file checker can answer: the read
     of $_GET and the string concatenation that becomes the query live in
     different functions.
ACT build_kind is the whole finding. ` + "`interp`" + ` and ` + "`concat`" + ` mean the value
     was spliced into SQL text; ` + "`literal`" + ` and a prepared statement mean it
     was not. Fix ` + "`interp`" + `/` + "`concat`" + ` with bound parameters, top of list
     first -- hops=0 is a direct splice in one function.
MISLEADS depth is capped at 4 (a facade adds 2-3 hops on its own, and past
     4 the path is mostly unresolved edges and the answer stops meaning
     anything), and ONLY resolved edges are walked, so this is a floor --
     read graph-blindspots first. psalm_only counts the four superglobals
     Psalm actually taints; $_SERVER/$_FILES are attacker-controlled in
     practice but would not appear in a Psalm baseline.`,
			fn: qSuperglobalToSQL,
		},
		{
			name:  "superglobal-to-include",
			title: "A variable include/require reachable from user input, up to 3 hops",
			notes: `ANSWERS local and remote file inclusion, which in PHP is a single
     ` + "`include $page`" + ` away from remote code execution.
ACT an ` + "`include`" + ` whose argument is not a literal is the finding. Replace it
     with a whitelist map from a request value to a fixed path. Nothing
     else is safe -- basename() and str_replace('..') both have bypasses.
MISLEADS depth is capped at 3 because an include this far from its input is
     usually a template loader with a fixed set of names. A router that
     builds paths from a config array shows here and is fine. A literal
     include is excluded entirely; only the variable ones are listed.`,
			fn: qSuperglobalToInclude,
		},
		{
			name:  "unserialize-gadget-frontier",
			title: "unserialize reachable from input, against the repo's gadget surface",
			notes: `ANSWERS both halves of a PHP object-injection chain at once. Half one is a
     reachable ` + "`unserialize`" + `; half two is the set of __destruct / __wakeup
     / __toString methods ANYWHERE in the tree, because those run with no
     call site the moment a crafted payload is deserialized.
ACT a reachable unserialize is exploitable in proportion to gadgets_in_repo,
     which is why that column is repo-wide rather than per-namespace.
     Replace with json_decode, or pass allowed_classes: false.
MISLEADS hops=0 is the normal result, not a missing measurement: the read
     and the sink usually sit in one function. Depth is capped at 4. The
     gadget count is a COUNT of magic methods,
     not a proof any chain composes -- building one needs a property write
     path this does not model. Conversely a gadget in an installed package
     under vendor/ is invisible here and PHPGGC's whole catalogue lives
     there, so a low count is not safety.`,
			fn: qUnserializeGadget,
		},
		{
			name:  "superglobal-to-shell",
			title: "User input reaching exec/system/shell_exec/backticks, up to 3 hops",
			notes: `ANSWERS command injection across function boundaries -- the class of bug
     that per-file linters miss because the read and the exec are in
     different files.
ACT escapeshellarg on the ARGUMENT, never escapeshellcmd on the whole
     string; better, do not build a command line at all.
MISLEADS backticks are counted as a shell call because the grammar gives
     them a call node; a shell metacharacter in a value read elsewhere is
     not visible here. Depth is capped at 3 over resolved edges.`,
			fn: qSuperglobalToShell,
		},
		{
			name:  "superglobal-to-echo",
			title: "Unescaped output of reachable input, with escaping as counter-evidence",
			notes: `ANSWERS stored/reflected XSS where the echo and the request read are in
     different functions. escaped is the counter-evidence: a function that
     also calls an escaper is ranked out by the HAVING clause, because a
     blanket escape makes the specific finding unrankable.
ACT escape at the sink, not at the source; the same value rarely stays
     in one context.
MISLEADS a function that echoes a constant beside a reachable read still
     ranks; check the function. Depth is capped at 3.`,
			fn: qSuperglobalToEcho,
		},
		{
			name:  "n-plus-one",
			title: "A query whose CALLER puts it in a foreach, followed through model methods",
			notes: `ANSWERS the N+1 select pattern: a query method reached from a function
     that also runs a query inside a loop, so one request becomes many.
ACT eager-load, or memoise the lookup keyed by the foreign key.
MISLEADS loop_depth is the MAXIMUM loop nesting in the caller, not a proof
     the query call is inside the loop -- the two are correlated but not
     identical. Depth is capped at 3 hops, and only resolved edges are
     walked, so an accessor behind a magic __call is invisible.`,
			fn: qNPlusOne,
		},
		{
			name:  "type-juggling-auth",
			title: "Loose == on a value that reaches from a superglobal",
			notes: `ANSWERS PHP's most reliable auth bypass: ` + "`'php' == 0`" + ` is true
     before 8.0 and still true for a great many comparisons after it.
     A loose comparison on a value reachable from a request is a finding
     whatever the intent.
ACT use === for identity, and cast to the type you mean.
MISLEADS pct_loose is the loose share of this function's comparisons, not
     of the comparison's operands. has_strict_types is reported and is
     always 0: the strict_types declare is matched against the inner
     directive node, whose text does not contain the word "declare".`,
			fn: qTypeJugglingAuth,
		},
		{
			name:  "driver-split",
			title: "mysqli and PDO in the same namespace: two escaping disciplines, one module",
			notes: `ANSWERS which namespaces mix database drivers. It matters because each
     driver escapes differently -- mysqli_real_escape_string needs a live
     connection handle and silently returns an empty string without one,
     PDO::quote is connection-bound too, and a query builder does neither
     because it binds. Mixing them means no single review rule applies.
ACT pick one. If a namespace shows both pdo and mysqli, the migration was
     never finished and the half-migrated code is where the unescaped
     concatenations live.
MISLEADS the driver is inferred from the CALLEE NAME, because the receiver's
     type is not knowable without full inference. ` + "`->query`" + ` on a PDO handle
     and ` + "`->query`" + ` on a query builder are indistinguishable here and both
     land in ` + "`pdo`" + `. ` + "`builder`" + ` is a guess from Laravel/Doctrine method
     names. Read this as 'how many escaping conventions are in play', not
     as an inventory of connections.`,
			fn: qDriverSplit,
		},
		{
			name:  "file-upload-surface",
			title: "$_FILES handling, and whether anything nearby validates it",
			notes: `ANSWERS raw file-upload handling, the one input family no framework
     middleware can see. A framework that hands uploads to the model layer
     never touches $_FILES, so a clean reading here means the raw API is
     unused, not that uploads are safe.
ACT never trust the client-supplied name or MIME type. Generate a name,
     verify with getimagesize or a magic-byte check, store outside the
     document root, and serve through a script that sets the content type.
MISLEADS is_controller is a path-and-name heuristic, not a framework route
     table. An empty table is the normal reading for a framework
     application and says nothing about its upload validation.`,
			fn: qFileUpload,
		},
		{
			name:  "error-suppression",
			title: "The @ operator: failures made invisible rather than handled",
			notes: `ANSWERS where failure is turned into data. A suppressed call returns
     false or null and execution continues, so a null becomes an empty
     string, an empty string becomes a valid id, and the bug surfaces three
     layers away.
ACT delete the @ and handle the failure; if the call genuinely cannot
     fail, say why in a comment.
MISLEADS the count is of suppression EXPRESSIONS, not of suppressed
     statements: one @ on a chained call is one site. This query is
     weighted by the nearby superglobal and SQL activity because
     suppression there hides the interesting failures.`,
			fn: qErrorSuppression,
		},
		{
			name:  "dynamic-call-surface",
			title: "Variable variables, variable methods and dynamic new: the parts no tool can follow",
			notes: `ANSWERS where the call graph structurally cannot exist. Every row here
     is an edge the graph does not have, which is why the
     reachability questions above are floors rather than answers.
ACT a variable method name is a lookup table; a variable class is a
     factory keyed by a type token. Both are testable, and both make the
     graph whole again.
MISLEADS eval counts as a dynamic site but is not one of the four
     columns; read it in n_eval. A variable that is provably constant
     still counts -- the tool reads the shape, not the value.`,
			fn: qDynamicCallSurface,
		},
		{
			name:  "magic-method-surface",
			title: "__destruct, __wakeup, __toString: the methods an attacker gets to call",
			notes: `ANSWERS which classes are usable as gadgets. A deserialization attack
     does not call your code directly -- it constructs an object graph
     and lets PHP invoke the magic methods on the way in and out. Any
     __destruct that touches the filesystem is a primitive.
ACT the fix is upstream: never unserialize untrusted input, use JSON.
     Where a magic method must exist, keep it free of side effects --
     no file operations, no exec, no SQL.
MISLEADS a class is only a gadget if the attacker can reach
     unserialize at all; see unserialize-gadget-frontier for that half.
     This lists the ammunition, not the gun.`,
			fn: qMagicMethodSurface,
		},
		{
			name:  "untyped-public-boundary",
			title: "Public methods taking untyped parameters, where strict_types is off",
			notes: `ANSWERS the public surface where PHP will silently coerce whatever it is
     handed. A public untyped parameter is the boundary an attacker
     reaches first, and coercion is what turns a wrong value into a
     valid one.
ACT type the parameter. With strict_types off the declaration is
     documentation, not enforcement.
MISLEADS has_strict_types is always 0, for the reason given in
     type-juggling-auth: the declare is matched against the wrong node.
     So every untyped public method is listed whether or not its file
     declares strict_types, and the column cannot be used to filter.`,
			fn: qUntypedPublic,
		},
		{
			name:  "dead-code",
			title: "Nothing in this tree calls these",
			notes: `ANSWERS functions with no caller in the tree. This is a FLOOR, not a
     verdict: a public method called from a template, a route file the
     walk skips, a container resolution, or a magic __call is invisible,
     and the exclusion list below is what the graph can actually rule out.
ACT confirm the absence by grepping the whole repository including
     templates and configuration, then delete or make private.
MISLEADS the exclusions are the honest part. A symbol excluded here is
     genuinely not reachable: it is not public, not a test, not an
     entrypoint, not an override, not abstract, and has fan_in 0.`,
			fn: qDeadCode,
		},
		{
			name:  "outbound-fetch-below-a-controller",
			title: "file_get_contents, fopen or curl_exec reachable from a controller",
			notes: `ANSWERS outbound network calls under a request-facing boundary, which is
     the SSRF review list. The URL is built somewhere between the two,
     and this ranks the pair.
ACT allowlist the host and the scheme; a fetch whose URL is assembled
     from a request value needs no other review.
MISLEADS reachability is not taint -- a controller may reach a fetcher
     that only ever sees a constant URL. Depth is capped at 4 over
     resolved edges.`,
			fn: qOutboundFetch,
		},
		{
			name:  "deserialization-injection",
			title: "unserialize() on untrusted input (PHPStan/Sonar)",
			notes: `ANSWERS object injection, which is remote code execution wherever a
     gadget chain exists. serialize is listed because a call to one is a
     call to the other in every codebase that has both.
ACT json_decode, or unserialize with allowed_classes: false.
MISLEADS n_eval is a different sink that happens to be nearby; read
     unserialize-gadget-frontier for the gadget half.`,
			fn: qDeserialization,
		},
		{
			name:  "command-injection",
			title: "eval or dynamic dispatch with potential injection (PHPStan/Sonar)",
			notes: `ANSWERS the three shapes that execute a name rather than a value: eval,
     variable-function dispatch, and a variable include. Each one turns
     a data value into code or a path.
ACT validate input; use fixed function names; never eval user input.
MISLEADS n_dynamic_call counts dynamic SITES, not dynamic calls, so one
     site reached from four callers still reads as 1.`,
			fn: qCommandInjection,
		},
		{
			name:  "file-inclusion-injection",
			title: "include/require with dynamic path (PHPStan/Sonar)",
			notes: `ANSWERS file inclusion with a non-literal argument. A literal include is
     not listed: it cannot be steered.
ACT a whitelist map from a request value to a fixed path. basename()
     and str_replace('..') both have bypasses.
MISLEADS n_variable_var is listed beside it because a variable variable
     often builds the include path indirectly.`,
			fn: qFileInclusion,
		},
		{
			name:  "header-redirect-open",
			title: "header('Location:...') without exit (PHPStan/Sonar)",
			notes: `ANSWERS every header() call, not only the redirect ones: a header that
     sets a cookie or a content type after output has started is dropped
     silently, and a Location header without an exit lets execution
     continue into whatever the function does next.
ACT exit immediately after a Location header.
MISLEADS a constant Location is a redirect and still belongs here; the
     open-redirect question is the one that needs a request value.`,
			fn: qHeaderRedirect,
		},
		{
			name:  "open-redirect-surface",
			title: "header() redirects in functions that read superglobals (OWASP G26)",
			notes: `ANSWERS the same-function join: a redirect target built beside a request
     read. This is the family PHPStan's open-redirect rule fires on.
ACT allowlist the target against a fixed set of paths.
MISLEADS same-function co-occurrence is NOT data flow -- a constant
     Location beside an unrelated read ranks the same as a vulnerable
     one. header_sites is the hazard count for the exact pattern, so a
     row with more than one is worth reading twice.`,
			fn: qOpenRedirect,
		},
		{
			name:  "hardcoded-secret-candidates",
			title: "Credential-shaped string literals (OWASP G07)",
			notes: `ANSWERS literals that look like credentials, which is the one secret
     class a scanner can find: a value in the source, not a value in the
     environment.
ACT rotate and move to a secret manager; never commit the literal.
     A leaked key is leaked whether or not it is still in use.
MISLEADS this is a CANDIDATE list, not a verdict. A long string that
     happens to contain "token" is one line of noise per occurrence;
     the exclusions drop obvious non-secrets (paths, format strings).`,
			fn: qHardcodedSecrets,
		},
		{
			name:  "xxe-parser-surface",
			title: "XML parser construction sites (OWASP G13)",
			notes: `ANSWERS where an XML parser is constructed, which is where entity
     expansion and external-entity resolution are decided. The setting,
     not the name, is the vulnerability.
ACT libxml_disable_entity_loader where it still exists, LIBXML_NOENT
     off by default, and prefer a parser that never resolves entities.
MISLEADS the counter is name-based, so a wrapped parser factory is
     invisible. A repo with a hardcoded XML surface and no unserialize
     is still worth reading.`,
			fn: qXXE,
		},
		{
			name:  "path-traversal-surface",
			title: "fopen/file_get_contents with a non-literal path in superglobal functions (G12)",
			notes: `ANSWERS the traversal sink in a function that also reads a request
     value. The path is a raw free-function call, so a request value
     reaching it is a read of any file the process can open.
ACT realpath() the result and check it is inside an allowed root; reject
     any path containing a null byte.
MISLEADS the literal test is textual and node-shaped: "'/a/' . $p" starts
     and ends with a quote, so only a lone string node counts as a
     literal. A value may never reach the open, and a constant-open beside
     an unrelated read ranks the same as a real finding.`,
			fn: qPathTraversal,
		},
		{
			name:  "unchecked-upload-surface",
			title: "move_uploaded_file in functions that read $_FILES (OWASP G28)",
			notes: `ANSWERS the classic upload handler: read the temporary file, move it.
     Everything between those two calls is the vulnerability.
ACT generate the stored name, verify the content independently of the
     upload, and never let the client name reach the filesystem.
MISLEADS both counters must be non-zero in the SAME function, so a
     handler that delegates the move to a helper is not listed here.`,
			fn: qUncheckedUpload,
		},
		{
			name:  "log-injection-surface",
			title: "error_log calls in functions that read superglobals (OWASP G14)",
			notes: `ANSWERS log-line injection. A newline in a logged value forges log
     entries, which is how an audit trail stops being evidence.
ACT strip CR/LF and control characters from every logged value; log the
     structured field, not the concatenation.
MISLEADS a constant message beside a request read ranks the same as a
     real one; the row names both so you can see which.`,
			fn: qLogInjection,
		},
		{
			name:  "unauthenticated-input-surface",
			title: "Superglobal reads with no auth call in the function (OWASP G01)",
			notes: `ANSWERS functions that read request input and contain no auth-family
     call. The marker is name-based over a fixed vocabulary, so it is a
     screen, not a proof.
ACT make the authentication requirement explicit at the boundary and
     assert it in the function that consumes the input.
MISLEADS a function that receives already-authenticated input as a
     parameter is not listed, which is correct; one that reads the
     superglobal directly and delegates the check to a caller is
     listed, which is also correct.`,
			fn: qUnauthInput,
		},
		{
			name:  "session-fixation",
			title: "session_start without session_regenerate_id (PHPStan/Sonar)",
			notes: `ANSWERS every session_start / setcookie / regenerate call, so the
     rows where a fix is missing stand out by their fan_in.
ACT regenerate the id on every privilege change, and send the cookie
     with Secure, HttpOnly and SameSite.
MISLEADS n_session_call covers the whole family, so a function that only
     sets a cookie is a weaker row than one that starts a session.`,
			fn: qSessionFixation,
		},
		{
			name:  "extract-injection",
			title: "extract() on superglobals (PHPStan/Sonar)",
			notes: `ANSWERS variable variables into the local scope, which is how a request
     array becomes a set of parameters without anyone naming them.
ACT access keys explicitly; extract() with EXTR_SKIP at best hides the
     problem.
MISLEADS extract() on a literal array is not listed; the super_reads
     column is what makes the row interesting.`,
			fn: qExtractInjection,
		},
		{
			name:  "loose-comparison-type-juggling",
			title: "== comparison with type juggling (PHPStan/Psalm)",
			notes: `ANSWERS every loose comparison, ranked by how many callers reach it.
     In PHP ` + "`==`" + ` coerces, so the comparison is between the value and whatever
     the other side can be cast to.
ACT use ===. Where loose comparison is intended, cast both sides
     explicitly so the intent is in the code.
MISLEADS has_strict_types is always 0 and cannot be used to filter; see
     type-juggling-auth.`,
			fn: qLooseCompare,
		},
		{
			name:  "error-suppression-operator",
			title: "@ error suppression operator (PHPStan/Psalm)",
			notes: `ANSWERS the operator on its own, without the superglobal weighting the
     error-suppression question applies.
ACT handle the error.
MISLEADS empty catches are listed beside it because they are the other
     way PHP code makes a failure disappear.`,
			fn: qErrorSuppressOp,
		},
		{
			name:  "weak-hash",
			title: "MD5 or SHA1 used for hashing (PHPStan/Sonar)",
			notes: `ANSWERS the fast hashes where a slow one is required. MD5 and SHA1 are
     collision-broken; neither is a password hash.
ACT password_hash for passwords, hash('sha256', ...) for integrity, and
     sodium_crypto_* where the threat model needs a MAC.
MISLEADS MD5 of a file for a cache key is fine and is still listed. The
     call site decides, not the function.`,
			fn: qWeakHash,
		},
		{
			name:  "remote-fetch-ssrf",
			title: "file_get_contents or curl with URL (PHPStan SSRF)",
			notes: `ANSWERS the fetch sinks per function, ranked by fan_in.
ACT validate and restrict the URL; never fetch user-supplied URLs directly.
MISLEADS the counter is name-based, so a wrapped HTTP client is invisible.
     Reachability from a request is a separate question.`,
			fn: qRemoteFetch,
		},
		{
			name:  "csrf-missing",
			title: "Controller action without CSRF token check (PHPStan/Sonar)",
			notes: `ANSWERS the request-facing surface, so the review starts where an
     attacker can reach. superglobal_reads says whether the action reads
     input at all.
ACT a token bound to the session, verified on every state-changing verb,
     and SameSite on the session cookie as a second layer.
MISLEADS this is the whole controller surface, NOT a finding: a GET
     action that changes nothing needs no token. The check is a manual
     read of superglobal_reads against the route's semantics.`,
			fn: qCSRFMissing,
		},
		{
			name:  "trait-adoption",
			title: "Traits by how many classes ingest them",
			notes: `ANSWERS which traits spread methods across the widest class set -- the
     first candidates for refactoring into a shared service or a value
     object, because every use site is a copy of the same behavior.
ACT a trait adopted by many classes is either a service hiding in a copy
     (inject it instead) or a genuinely shared slice (good -- but then
     test it once and document the contract).
MISLEADS ` + "`used_by`" + ` counts classes that ` + "`use`" + ` the trait by simple name;
     an interface or abstract class adopting it is not counted, and a
     trait used only inside a closure/conditional may not be tracked.`,
			fn: qTraitAdoption,
		},
		{
			name:  "namespace-instability",
			title: "Afferent vs efferent coupling per namespace",
			notes: `ANSWERS package stability: how many namespaces depend on this one
     (afferent) against how many it depends on (efferent).
ACT a namespace with high efferent and low afferent coupling is a leaf
     that will change often and break its dependents; push shared
     contracts down into a more stable namespace.
MISLEADS the coupling is counted between CLASSES by namespace, so a
     function calling into another namespace does not appear. A namespace
     with no cross-namespace class edges reads as 0/0, which means the
     metric does not apply, not that the code is independent.`,
			fn: qNamespaceInstability,
		},
		{
			name:  "lsb-hotspots",
			title: "Classes dense in scoped self/parent/static calls",
			notes: `ANSWERS which classes lean hardest on scoped calls (` + "`self::`" + `,
     ` + "`parent::`" + `, ` + "`static::`" + `). Scoped calls are where late static binding
     surprises live: ` + "`static::`" + ` resolves at the runtime caller's class,
     ` + "`self::`" + ` at the definition site, and a copied method body between
     the two is how an override silently gets bypassed.
ACT review each scoped call for whether ` + "`static::`" + ` is what the author
     needs (usually it is) and whether the callee survived a move
     between parent and child.
MISLEADS the graph counts ALL scoped calls in one counter and CANNOT
     tell self:: from static:: apart -- that needs lexing the receiver.
     Rows are therefore hotspots to audit by eye, not confirmed LSB bugs.
     Calls through a variable (` + "`$this->`" + `), plain method calls, and
     constructor-promotion aliases are excluded.`,
			fn: qLSBHotspots,
		},
		{
			name:  "psr4-violations",
			title: "Classes whose namespace does not match a composer psr-4 root",
			notes: `ANSWERS classes whose namespace lacks any prefix declared in
     composer.json autoload.psr-4. When the namespace matches no root,
     the autoloader falls back to file scanning or classmap, and moving
     the file breaks the lookup.
ACT add the namespace root to psr-4, or move the class to the matching
     directory; a class under App\ should sit under src/App/ or the
     root that maps to it.
MISLEADS composer.json is read only for its psr-4 ROOTS (up to 400
     chars), and a namespace is judged "covered" if it STARTS WITH a
     root; overlapping roots, ` + "`classmap`" + ` entries, and per-file
     configurations all evade this. A bare root like App\\ with no
     directory equivalent is reported even where hand-loaded manually.`,

			fn: qPSR4Violations,
		},
		{
			name:  "magic-fallback-risk",
			title: "Classes whose magic methods can absorb calls no method implements",
			notes: `ANSWERS classes declaring __call/__callStatic/__get/__invoke in the
     same file as unresolved calls. Every call into one of those is
     unresolvable in principle, so the file's call graph is a lower
     bound and the blind spot is structural rather than a tool limit.
ACT declare the methods the container actually calls, or narrow __call
     to a small allowlist and throw on anything else.
MISLEADS unresolved_in_file counts call SITES, not distinct callees, and
     is restricted to the class's own file.`,
			fn: qMagicFallback,
		},
		{
			name:  "iface-coverage",
			title: "Interfaces by number of classes that declare them",
			notes: `ANSWERS how many classes name each interface in their implements
     clause -- the declared implementation breadth of every contract.
     Rows with implementors=0 are the contracts nothing honors in-tree.
ACT a high-breadth interface is a stable-seam candidate; a
     zero-implementor one is dead abstraction, or a seam satisfied
     entirely by code outside the tree.
MISLEADS implements is a comma-joined declared-name list per class and
     matching is by exact name against that list, so aliased or
     namespaced spellings undercount; satisfaction via duck typing
     (PHP does not require ` + "`implements`" + `) has no row at all; and a
     class that declares the interface but never uses it is counted
     the same as one fully implementing it.`,
			fn: qIfaceCoverage,
		},
		{
			name:  "abstract-hooks",
			title: "Abstract methods awaiting implementations in concrete subclasses",
			notes: `ANSWERS the hooks each abstract class declares and how many concrete
     subclasses exist to implement them -- the interface a change to the
     abstract breaks across. Abstract classes with zero concrete
     subclasses in-tree are either templates consumed elsewhere or
     dead scaffolding.
ACT an abstract skeleton with one concrete subclass is often better
     off as a plain interface; with many, it is a template-method
     pattern worth documenting.
MISLEADS subclass lookup is by the extends TEXT column with name
     boundaries, so anonymous classes, string-built class names, and
     namespaced aliases of the parent can undercount; a concrete
     subclass that never overrides a given abstract method is counted
     as a potential implementor, not a proven one.`,
			fn: qAbstractHooks,
		},
	}
}

func sortedKeys[V any](m map[string]V) []string {
	out := make([]string, 0, len(m))
	for k := range m {
		out = append(out, k)
	}
	sort.Strings(out)
	return out
}

var _ = strings.Join

func buildQueries2() []question {
	return []question{
		{
			name:  "unprepared-sql-hotspots",
			title: "SQL built by interpolation, never prepared, in a loop",
			notes: `ANSWERS SQL built by interpolation/concat/format, never prepared, paid
     per iteration when the site sits in a loop: the perf + injection
     double hit. ` + "`superglobal-to-sql`" + ` owns the TAINT ranking; this owns the
     BUILD-SHAPE ranking and deliberately includes rows with no
     superglobal in sight.
ACT prepare once outside the loop and parameterise the values; every
     interpolation is an injection site the moment the string is not a
     constant.
MISLEADS is_sanitized is a textual scan and a wrapper defeats it
     silently; build_kind 'variable' (a whole query in one variable) is
     excluded by construction -- the variable was built elsewhere and
     its construction site is where the real question lives.`,
			fn: qUnpreparedSQL,
		},
		{
			name:  "ssrf-frontier",
			title: "Tainted superglobal read + remote fetch in the same function",
			notes: `ANSWERS functions that BOTH read a psalm-tainted superglobal AND call a
     remote-fetch sink: the SSRF review list. The URL host may be the
     internal network, and the function is the exact place a firewall
     bypass would ship.
ACT allowlist the URL host/scheme; never fetch raw user input. The
     superglobal key is in the row -- it tells you the input field.
MISLEADS same-function co-occurrence is NOT data flow -- the URL may be
     constant despite the read (the row names both so you can see); a
     validation wrapper between read and fetch is invisible (false
     negative class); the sink list is the hazard capture and is
     name-based. ` + "`remote-fetch-ssrf`" + ` is the coarser per-symbol counter;
     this is the same-function join.`,
			fn: qSSRFFrontier,
		},
		{
			name:  "implicit-nullable-params",
			title: "Typed parameters with default null (PHP 8.4 deprecation)",
			notes: `ANSWERS parameters typed T with default null: implicitly nullable,
     deprecated in PHP 8.4. Every call site that relied on the implicit
     nullability keeps working -- the deprecation is a contract smell,
     not a break.
ACT spell it ?T; behaviour identical, deprecation gone.
MISLEADS only a deprecation when the repo targets PHP >= 8.4 -- check
     the runtime pin before acting; untyped and variadic params are
     excluded by construction; an explicit ` + "`?T = null`" + ` is the control
     and does not appear.`,
			fn: qImplicitNullable,
		},
		{
			name:  "deprecated-api-frontier",
			title: "@deprecated / #[Deprecated] methods still being called",
			notes: `ANSWERS what is still calling a method marked deprecated, which is the
     only half of a deprecation anyone can act on.
ACT remove the callers, or un-deprecate the method if it is still the
     supported path.
MISLEADS deprecation is detected by an attribute or a docblock tag, so
     a plain "do not use" comment reads as not deprecated.`,
			fn: qDeprecatedAPI,
		},
		{
			name:  "broad-catch-surface",
			title: `catch (\Throwable) / catch (Exception) handlers`,
			notes: `ANSWERS handlers that catch everything, which is where a fatal error,
     a typo, and a real failure all become the same log line.
ACT catch the narrowest type you can handle, and let the rest
     propagate to a handler that reports it.
MISLEADS the test is textual on the catch type, so a multi-catch that
     includes Exception counts, and an aliased one does not.`,
			fn: qBroadCatch,
		},
		{
			name:  "dynamic-property-writes",
			title: "$obj->$name = v dynamic property writes (PHP 8.2 deprecation)",
			notes: `ANSWERS writes to a property whose name is computed. Deprecated in 8.2
     for a class without __set, and a typo becomes a silent extra field.
ACT declare the property, or route the write through a method.
MISLEADS classes with __get/__set are excluded, because for those the
     write is a real method call rather than a dynamic property.`,
			fn: qDynamicPropWrite,
		},
		{
			name:  "bool-flag-methods",
			title: "Boolean flag parameters at the end of the parameter list",
			notes: `ANSWERS the boolean-parameter smell: a call site reads as a sentence
     with a negation in it, and a default of false means the flag is
     invisible at half the call sites.
ACT split into two named methods, or accept an options object.
MISLEADS only a literal ` + "`false`" + ` default counts, so a flag defaulted to
     null or 0 is not listed, and the parameter must be LAST to be
     listed at all.`,
			fn: qBoolFlags,
		},
		{
			name:  "npath-explosion",
			title: "Functions whose decision tree is exponential (PHPMD NPath)",
			notes: `ANSWERS the NPath estimate -- the product of branch counts, capped at
     2^cyclomatic: every added if doubles the paths the next reader
     must trace. Rows are the functions where one more branch is the
     difference between testable and untestable.
ACT split on the axis with the fewest paths; extract the decision
     table into data.
MISLEADS the estimate is 2^cyclomatic, not PHPMD's exact product: a
     switch of 10 cases reads as 2^cyclomatic instead of 10x, and a
     loop containing a branch reads the same as a branch containing a
     loop; the cap keeps the ranking honest beyond 2^20.`,
			fn: qNPath,
		},
		{
			name:  "maintainability-index-worst",
			title: "Lowest maintainability scores (Halstead + cyclomatic + LOC)",
			notes: `ANSWERS the functions whose cost of reading exceeds their value, by the
     classic index: a size term, a complexity term, and a volume term.
     Zero is the worst score and the index is clamped there.
ACT split the function; the index responds to size faster than to
     complexity, which is the right order of operations.
MISLEADS the volume term here is a Halstead PROXY -- operator and
     operand counts, not a real operator/operand-pair census -- so the
     absolute number is not comparable with a textbook MI.`,
			fn: qMaintainability,
		},
		{
			name:  "env-outside-config",
			title: "env() called outside config paths, with the runtime callers that break under config:cache",
			notes: `ANSWERS the Laravel/Symfony deployment bug the docs warn about in
     exactly these words: after ` + "`config:cache`" + `, every env() call OUTSIDE the
     configuration files reads null at run time. A null that becomes a
     default database password is not a config problem, it is an auth
     bypass. fan_in and runtime_entry_reaches are the graph's answer to
     'does anything actually execute this path after boot?'.
ACT replace the call with config('...') and move the value into a
     config file, or cache the env read at bootstrap. Start with rows
     where runtime_entry_reaches=1 -- a request path reads null TODAY if
     the config is cached.
MISLEADS exclusion is a substring test on the path (any directory
     named config counts), so env() inside App\Config\ support classes
     is hidden too -- a false negative class, not a false positive one.
     callers_up counts only RESOLVED static edges within 2 hops, so on a
     container-heavy codebase it is a floor, not a census.`,
			fn: qEnvOutsideConfig,
		},
		{
			name:  "dispatch-in-transaction",
			title: "Queue/event dispatch reachable from a transaction, with afterCommit as counter-evidence",
			notes: `ANSWERS the ordering hazard Laravel warns about: a job queued inside a
     transaction races the commit, and a listener that reads the row it
     was queued for finds nothing. beginTransaction/commit/rollBack mark
     the frontier a dispatch may cross.
ACT dispatch after commit, or go through afterCommit explicitly.
     after_commit_sites is the counter-evidence: a function that only
     dispatches after committing is safe, however it is written.
MISLEADS the walk is two-sided from the transaction opener, so a
     dispatch in a helper the transaction never calls is not listed, and
     a transaction opened but never committed counts as a transaction.`,
			fn: qDispatchInTx,
		},
		{
			name:  "multi-write-no-transaction",
			title: "Two or more write sites in a call tree, no transaction anywhere in the writer",
			notes: `ANSWERS the torn-write frontier: a function that mutates through two or
     more ORM calls, counting the ones its callees make, and never opens
     a transaction. Two writes with no guard means a failure between
     them leaves the first committed.
ACT wrap the call tree in one transaction, or make the second write
     idempotent so a retry converges.
MISLEADS writes are counted by hazard name, so a write through a
     wrapper, a raw query, or a queued job is invisible. And a
     transaction anywhere in the function counts, even one that does
     not cover both writes.`,
			fn: qMultiWrite,
		},
		{
			name:  "raw-sql-below-controller",
			title: "Controller-reachable code that splices SQL text (interp/concat), beyond superglobal-to-sql",
			notes: `ANSWERS the half of SQL injection superglobal-to-sql cannot see: the
     input arrives as a method argument or a validated DTO, so no
     superglobal read sits anywhere in the taint path -- but the
     controller can still REACH a helper that splices variables into
     SQL text. Reachability from the request-facing boundary is the
     review order, and hops is how far the fix has to travel.
ACT make the reachable builder use bound parameters, fewest hops
     first; a row with prepared=0 and interp>0 two hops from a
     controller is the classic 'validated input, unsafe sink' shape.
MISLEADS reachability is not taint -- a controller may reach a builder
     that only ever sees constant ids. Depth stops at 4 hops over
     resolved edges; a call made through a container ($app->make) or a
     magic __call is not an edge here at all, so the list is a floor.`,
			fn: qRawSQLBelowController,
		},
		{
			name:  "file-sink-frontier",
			title: "File open/write/delete reachable from input, up to 3 hops (CodeQL path-injection)",
			notes: `ANSWERS a request value reaching a file that is opened with a computed
     path, or written with one. The traversal sink and the write sink
     are the same bug with different consequences.
ACT resolve the path against an allowed root and verify the result is
     still inside it after symlink resolution.
MISLEADS depth capped at 3 over resolved edges, so this is a floor; a
     path built by a container-resolved helper is not an edge here.`,
			fn: qFileSinkFrontier,
		},
		{
			name:  "nullable-return-hotspot",
			title: "Nullable-returning functions by call-site count: every site must handle the null",
			notes: `ANSWERS the functions whose return type admits null, weighted by how many
     call sites there are to get wrong. A nullable return is a contract
     every caller has to discharge.
ACT return an empty collection rather than null, or narrow the type so
     the compiler enforces it.
MISLEADS the nullability test is textual on the return type, so a
     nullable alias or a ` + "`?`" + ` buried in a template union reads as not nullable here.`,
			fn: qNullableReturn,
		},
		{
			name:  "mixed-propagation-frontier",
			title: "Entrypoints reaching functions with no return type or untyped params: where mixed flows",
			notes: `ANSWERS where an untyped value enters and leaves the type system on a
     request path. PHP will accept anything at those boundaries and the
     error surfaces three calls later.
ACT type the parameters and the return; on a request path an untyped
     parameter is an unvalidated request.
MISLEADS depth is capped at 3 and only resolved edges are walked, so
     a container-resolved handler is invisible. no_return_type is 1 for
     every row here that has one, which is most of them.`,
			fn: qMixedPropagation,
		},
		{
			name:  "in-array-loose-input",
			title: "in_array/array_search without the strict argument, reachable from input, up to 3 hops",
			notes: `ANSWERS the loose search on a path reachable from request input. Before
     8.0 a needle of 0 matched every string haystack; after it, 'php' == 0
     still surprises people at the edges of a loosely-typed value.
ACT pass true as the third argument, or use a match expression.
MISLEADS the counter is a call-site count, not a symbol count, and a
     wrapper that adds the strict flag is invisible.`,
			fn: qInArrayLoose,
		},
		{
			name:  "regex-injection-surface",
			title: "preg_* with a computed pattern in functions reachable from input, up to 2 hops",
			notes: `ANSWERS regex injection and ReDoS carriers: a pattern assembled from
     data is both an injection point and an unbounded-backtracking risk.
     Depth is only 2, because a pattern built two frames from a request
     is the realistic case.
ACT use a fixed pattern, and preg_quote the parts that come from data.
MISLEADS the literalness test is node-shaped: a double-quoted pattern
     with a variable in it is an encapsed_string and therefore counted
     as computed, which is correct.`,
			fn: qRegexInjection,
		},
		{
			name:  "mass-assignment-surface",
			title: "fill()/forceFill() fed by request input, with $fillable as counter-evidence (Laravel docs)",
			notes: `ANSWERS the Laravel mass-assignment question: the model mutation front
     door (fill, forceFill -- and the create-family, captured under
     the write counter) in a function that also reads request input,
     and whether the model declares $fillable/$guarded. Without the guard,
     a crafted form field named is_admin writes the column (the 2012
     GitHub mass-assignment incident is the canonical story).
ACT has_fillable=0 rows first: add $fillable (allowlist) or $guarded
     (denylist) to the model, then re-check whether the route really
     needs is_admin in the form. Request::only([...]) beats ->all().
MISLEADS same-function co-occurrence is NOT data flow -- the fill may
     take a hand-built array while an unrelated ->input() reads a page
     number. fillable detection is a property named fillable/guarded on
     the model CLASS; a trait-provided or inherited guard reads as 0.
     API resources serializing ->all() are invisible here.`,
			fn: qMassAssignment,
		},
		{
			name:  "debug-reach-production",
			title: "dd/dump/ray/exit reachable from an entrypoint, up to 3 hops",
			notes: `ANSWERS debug calls that a request can still reach. The cost is not the
     output, it is the information: a dump in a controller prints
     whatever the object holds, into whatever the response is.
ACT delete them; a debug call that survived review is not going to be
     removed later.
MISLEADS exit and die are statements rather than calls and are counted
     through a separate column, so a function that only exits is not
     listed here. Depth is capped at 3 over resolved edges.`,
			fn: qDebugReach,
		},
		{
			name:  "session-write-from-input",
			title: "$_SESSION written in functions that also read request input (OWASP session cheat sheet)",
			notes: `ANSWERS session poisoning candidates: the function writes
     $_SESSION[...] (login state, role, redirect target) while reading
     request data. Session state is TRUSTED on every later request --
     it bypasses every input filter -- so a value written straight
     from the request lives exactly where attackers want it, including
     stored XSS on the next page that echoes it.
ACT allowlist what gets stored: put scalar ids in the session, never
     raw request arrays, and regenerate the id after any auth write
     (session_regenerate_id -- see session-fixation).
MISLEADS same-function co-occurrence is NOT data flow -- the write may
     store a constant and the read may serve a different field. A
     framework-managed session (Laravel session helper, PSR-15
     middleware) writes through its own API and is invisible to the
     $_SESSION capture, which makes this a raw-PHP-only lens.`,
			fn: qSessionWrite,
		},
		{
			name:  "superglobal-to-header",
			title: "header()/setcookie reachable from input, up to 3 hops (Psalm TaintedHeader)",
			notes: `ANSWERS header injection across function boundaries: the sink that
     writes response headers or cookies is reachable from a request
     value. A newline in a header value splits the response (HTTP
     response splitting -> cached XSS), and a request-shaped
     setcookie path/domain attribute is a session-scoping attack. The
     same-function family lives in open-redirect-surface; this is the
     frontier where the header call is frames away from the read.
ACT reject CR/LF/%0d/%0a in anything reaching a header, allowlist
     redirect targets, and set cookie attributes explicitly. hops=0 is
     the direct case the smaller queries already rank.
MISLEADS depth capped at 3 over resolved edges (a facade adds 2 on
     its own), so this is a floor; reachability is not taint, and a
     header('Content-Type: ...') constant beside a reachable read
     ranks like a real finding -- the patterns column tells you which
     header-family calls the function actually makes.`,
			fn: qSuperglobalToHeader,
		},
		{
			name:  "facade-in-model-layer",
			title: "Facade static calls inside model/entity classes: a service locator in the domain",
			notes: `ANSWERS the layering violation a framework's own container makes easy:
     a model that reaches for Log:: or Cache:: through a facade. The
     call resolves perfectly -- which is exactly why it hides from the
     unresolved-call counter -- and the dependency is now global and
     invisible to the constructor.
ACT inject the dependency, or pass a collaborator in. A model that
     constructs its own collaborators cannot be tested without a
     container.
MISLEADS is_model is a path-and-name heuristic, so a misfiled helper
     under src/Models reads as a model, and a model reached through a
     facade base class is still listed.`,
			fn: qFacadeInModel,
		},
		{
			name:  "write-in-loop",
			title: "DB write calls in looping functions: the bulk-write anti-pattern",
			notes: `ANSWERS a mutation inside a loop, which is both the N+1 write problem
     and the transaction-boundary problem: the whole loop is one
     transaction, or none of it is.
ACT batch the write, or chunk it with an explicit transaction per
     chunk.
MISLEADS the loop counters are the max NESTING depth and whether any
     call happens inside a loop, not whether this particular write does,
     so a write in a method that also loops elsewhere is listed.`,
			fn: qWriteInLoop,
		},
		{
			name:  "dynamic-dispatch-frontier",
			title: "Entrypoints reaching eval / variable-include / variable-new sites, up to 4 hops",
			notes: `ANSWERS where a request path reaches code whose target is chosen at run
     time. Each site is a place where the graph has no edge, so every
     reachability claim that passes through one is a floor.
ACT replace the dynamic name with a lookup from a fixed set, and make
     the set a constant so a reviewer can read it.
MISLEADS the counters are site counts, not call counts, so one site
     reached from four callers reads as 1. hops>0 only, because the
     same-function case is already in dynamic-call-surface.`,
			fn: qDynamicDispatch,
		},
		{
			name:  "trait-method-collision",
			title: "Same method name provided by two traits used by one class (flat-compose conflict)",
			notes: `ANSWERS PHP's fatal-composition hazard, which is a cross-FILE fact by
     construction: a class uses two traits that both define the same
     method name. PHP aborts at load unless the class adds
     insteadof/as conflict resolution -- so the collision is latent in
     the tree TODAY and any rename that makes two trait methods share
     a name turns a deploy into a fatal error. No per-file linter can
     see the pair, because the traits and the class live in three
     files.
ACT add ` + "`use TraitA::method insteadof TraitB;`" + ` explicitly, or rename
     one of the methods. n_traits=2 rows are one rename away from
     breakage.
MISLEADS traits are matched by SHORT NAME against the class's use
     list, so two same-named traits in different namespaces collapse
     into one and ALIASED use-as statements can undercount; abstract
     trait methods are counted as definitions (they do not collide at
     runtime the way concrete ones do).`,
			fn: qTraitCollision,
		},
		{
			name:  "remote-call-in-loop",
			title: "curl_exec / file_get_contents / fwrite inside looping functions",
			notes: `ANSWERS a network or file call inside a loop, weighted by how many
     callers reach the function. This is the loop that turns one
     request into a hundred outbound connections.
ACT fetch once and reuse; batch the remote call if the provider has
     a bulk endpoint.
MISLEADS distinct_callers counts resolved non-self edges, so a
     container-resolved caller is not counted, and the loop counters
     are the whole function's, not this call's.`,
			fn: qRemoteCallInLoop,
		},
		{
			name:  "regex-compile-in-loop",
			title: "preg_* inside loops: per-iteration pattern work, weighted by callers",
			notes: `ANSWERS per-iteration regex work, which is both a throughput problem
     and a ReDoS carrier if the pattern is data-derived.
ACT hoist the match out of the loop, or precompile with a constant
     pattern and vary only the subject.
MISLEADS the two columns count different things: regex_in_loop is the
     substring-matched family, preg_in_loop is the exact preg_* names,
     so a preg_* call reached through a wrapper lands in one and not
     the other.`,
			fn: qRegexInLoop,
		},
		{
			name:  "cookie-without-flags",
			title: "setcookie called with fewer than 3 arguments: no expiry, path, domain, secure, httponly",
			notes: `ANSWERS cookies whose attributes are all defaults, which means no
     expiry (a session cookie), no path restriction, and neither
     Secure nor HttpOnly.
ACT pass all of them explicitly. The arguments are positional and
     optional, so every one of them has to be spelled out.
MISLEADS the test is an argument count, not a check that the values are
     right: a setcookie with 3 arguments and no flags is not listed.`,
			fn: qCookieFlags,
		},
		{
			name:  "global-state-mutation",
			title: "Functions reaching for global state, weighted by how many callers they have",
			notes: `ANSWERS hidden shared state: ` + "`global $db;`" + ` / $GLOBALS['...'] inside a
     function turns its signature into a lie -- the callers see two
     parameters while the function reads a third nobody passes. Under
     a long-running worker that global persists ACROSS requests, so a
     stale cache flag in request 2 is request 1's data. fan_in is the
     graph's contribution: how many callers inherit the invisible
     coupling.
ACT pass the dependency as a parameter (constructor-injected is
     better); for genuinely process-wide constants use a readonly
     config object. The rows with high fan_in pay back per caller.
MISLEADS n_globals counts ` + "`global`" + ` declarations and $GLOBALS reads,
     which in a deliberately stateful legacy plugin architecture can
     be the local idiom rather than a defect; sup_reads shows the
     functions that mix globals with request input -- those are the
     ones to read first.`,
			fn: qGlobalState,
		},
		{
			name:  "reflection-frontier",
			title: "Reflection sinks reachable from input, up to 3 hops",
			notes: `ANSWERS reflection reached from request input. Reflection is a name
     lookup with full access, so a class or method name from a request
     is arbitrary code execution by another route.
ACT allowlist the class and method names before reflecting, and never
     reflect a name that came in on the wire.
MISLEADS the sink list is name-based, so a wrapper around
     ReflectionClass reads as no reflection at all.`,
			fn: qReflectionFrontier,
		},
		{
			name:  "callable-frontier",
			title: "call_user_func / usort-style callable sinks reachable from input, up to 3 hops",
			notes: `ANSWERS the places where a function name is a VALUE, which is the
     single biggest reason a PHP call graph is incomplete.
ACT a lookup table from a fixed key set to a callable; a map is
     testable and a raw name is not.
MISLEADS this is the hazard-name family, so a wrapped usort or a
     framework's own dispatch layer is invisible, and the counts are
     distinct pattern names, not call sites.`,
			fn: qCallableFrontier,
		},
		{
			name:  "constructor-side-effects",
			title: "Constructors doing IO/SQL/network, ranked by how many sites construct them",
			notes: `ANSWERS constructors that cannot be trusted in tests, loops or
     containers: a __construct that opens files, queries the database
     or makes network calls runs that work on EVERY instantiation,
     with no call site to grep for. Construction sites is the graph
     fact per-file linters lack: a side-effecting constructor inside
     a loop (see write-in-loop) multiplies the cost invisibly.
ACT move the IO out of the constructor -- a factory method that
     returns the object, or lazy initialization on first use.
     construction_sites ranks the migration payoff.
MISLEADS construction_sites counts RESOLVED ` + "`new`" + ` edges only; a class
     newed through a container or built once in bootstrap.php is a
     legitimate one-shot and its row is noise. The IO is counted by
     hazard name, so a wrapped IO helper is invisible (false
     negative).`,
			fn: qConstructorIO,
		},
		{
			name:  "static-state-writes",
			title: "Cls::$var = v writes to mutable static properties (Octane/worker state leaks)",
			notes: `ANSWERS writes to static state, which is fine in php-fpm and a leak in
     every long-running worker: the value written by request 1 is the
     value request 2 reads.
ACT make the property immutable, or move the state onto an injected
     object whose lifetime is the request.
MISLEADS self::$x = and static::$x = and Cls::$x = are all counted
     together; which of the three is the bug depends on the class.`,
			fn: qStaticState,
		},
		{
			name:  "superglobal-in-model",
			title: "Model/entity-layer functions reading superglobals directly: a layering violation with taint",
			notes: `ANSWERS the double defect: a function in the model/entity layer
     ($_POST inside a User class) reads the request ITSELF. Layering
     says the model takes data in through parameters; taint analysis
     says a superglobal read buried below the controller is exactly
     the one no input-validation middleware ever sees, because the
     framework's request object was bypassed entirely.
ACT pass the value in as a parameter and do the read at the
     controller/action boundary; until then, this row is also your
     taint-review list for the model layer, since no middleware can
     sanitize what it cannot see.
MISLEADS the model layer is identified by path and class-name
     heuristics (is_model), so a helper misfiled under src/Models
     reads as a model; and $_SERVER reads in models are often only
     env/CLI probes -- check the var column of intent before treating
     a row as a request-path finding.`,
			fn: qSuperglobalInModel,
		},
		{
			name:  "controller-direct-sql",
			title: "Controllers issuing SQL themselves instead of going through a model/gateway",
			notes: `ANSWERS the layer violation a framework's active record makes
     easy: a controller that queries directly. The query works, and
     the business rule now lives in the request layer where nothing can
     reuse it.
ACT move the query behind a model or a gateway method; the controller
     should decide WHAT to do, not HOW to fetch it.
MISLEADS this is a per-function count of SQL sites, not of queries, so
     a controller that calls one repository method which does the SQL
     is correctly not listed.`,
			fn: qControllerSQL,
		},
		{
			name:  "cleartext-remote-fetch",
			title: "http:// (clear-text) URLs passed to fetch calls (SonarPHP S5332)",
			notes: `ANSWERS outbound requests that leave the TLS off: file_get_contents,
     curl_init/curl_setopt or fopen pointed at an http:// URL. The
     payload (an API key header, a session cookie, the response an
     auth decision depends on) crosses the network readable and
     writable by anyone on the path -- and the response of a
     cleartext fetch is input your code then trusts.
ACT switch to https and verify the peer (CURLOPT_SSL_VERIFYPEER is
     on by default -- do not turn it off to make the error go away).
MISLEADS detection is a substring test for http:// in the CALL's
     arguments, so 'http://localhost' dev endpoints count (usually
     acceptable, and the config-driven URL built elsewhere is
     invisible entirely -- a false-negative class). A literal
     'https://' string containing 'http://' cannot occur, but a
     scheme-relative or user-built URL will be missed.`,
			fn: qCleartextFetch,
		},
		{
			name:  "superglobal-to-mail",
			title: "mail() reachable from input, up to 2 hops (email header injection)",
			notes: `ANSWERS email header injection: mail() reachable from a request value.
     A \r\n in the subject or a 'contact form' field that becomes a
     header lets the attacker append Bcc: recipients and an arbitrary
     body -- your server becomes the spam cannon and the mail log
     still shows only legitimate sends. The frontier matters because
     the mail() call usually lives in a mailer helper several frames
     from the controller.
ACT strip CR/LF and control characters from EVERY argument to mail()
     (subject, headers, and the address fields), or move to a mail
     library that encodes headers. hops=0 is the direct case.
MISLEADS depth capped at 2 because the parameterization past that is
     usually a templating layer with constants; reachability is not
     taint, so a mailer reached by a contact controller that passes
     only constants ranks the same as the vulnerable one. Framework
     mailers (Symfony Mailer, Laravel Mail) bypass mail() entirely
     and are invisible here.`,
			fn: qSuperglobalToMail,
		},
	}
}

var _ = strings.Join

var nSymCols = len(symbolsColumns)

var strSlots = []int{cName, cReturnType, cClassName, cKind}

type symRow struct {
	vals []int32
	strs []string
}

const (
	symRowCols = 64
	symRowStrs = 16
)

type scope struct {
	sym      int32
	qualPre  string
	typeName string
	typeID   int32
	depth    int
}

type pendRec struct {
	sym      int32
	fid, mid int32
	name     string
	line     int32
	typ      string
}

type localSym struct {
	sid int32
	fid int32
	mid int32
	typ string
}

type fileResult struct {
	fid                   int32
	moduleID              int32
	rel                   string
	isTest, isGen, isVend bool
	parseErrs, missing    int
	sum                   string
	syms                  []symRow
	params                []paramRow
	fields                []fieldRow
	hazards               []hazardRow
	attributes            []attributeRow
	literals              []literalRow
	markers               []markerRow
	magic                 []magicRow
	hooks                 []hookRow
	classes               []classRow
	traits                []traitRow
	secrets               []secretRow
	imports               []importRow
	nsRows                []nsRow
	superglobals          []superReadRow
	sqlSites              []sqlSiteRow
	dynSites              []dynSiteRow
	strict                bool
	byName                map[string][]localSym
	byQual                map[string]int32
	extends               map[string]string
	fnSid                 map[uint64]int32
	pend                  []pendRec
	valCur                []int32
	strCur                []string
	nBlocks               int
	trees                 []tsRec
	sa                    strArena
}

type phpParser struct {
	p    *tsParser
	src  []byte
	rec  *fileResult
	st   *stats
	pool *interner

	keepTrees bool

	nsSpans []nsSpan

	kids *[]tsNode

	cur      tsCursor
	linesBuf [][]byte
}

func newPHPParser() *phpParser {
	return &phpParser{p: &tsParser{}, st: newStats(len(bumpCols)),
		pool: &interner{m: make(map[string]string, internerHint)}}
}

func (pa *phpParser) close() {}

func (pa *phpParser) put(s string) cgasStr { return pa.rec.sa.put(s) }

func (r *fileResult) newSym() int32 {
	i := int32(len(r.syms))
	if len(r.valCur) < nSymCols {
		slots := 8 << min(r.nBlocks, 4)
		r.nBlocks++
		r.valCur = make([]int32, slots*nSymCols)
	}
	vals := r.valCur[:nSymCols:nSymCols]
	r.valCur = r.valCur[nSymCols:]
	if len(r.strCur) < len(strSlots) {
		slots := 8 << min(r.nBlocks-1, 4)
		r.strCur = make([]string, slots*len(strSlots))
	}
	strs := r.strCur[:len(strSlots):len(strSlots)]
	r.strCur = r.strCur[len(strSlots):]
	r.syms = append(r.syms, symRow{vals: vals, strs: strs})
	return i
}

func (r *fileResult) set(c int, i int32, v int32) { r.syms[i].vals[c] = v }
func (r *fileResult) setS(c int, i int32, s string) {
	r.syms[i].strs[strSlot(c)] = s
}

var strSlotIdx = func() map[int]int {
	m := make(map[int]int, len(strSlots))
	for i, c := range strSlots {
		m[c] = i
	}
	return m
}()

func strSlot(c int) int { return strSlotIdx[c] }

const internerHint = 512

type interner struct{ m map[string]string }

func (in *interner) name(s string) string {
	if v, ok := in.m[s]; ok {
		return v
	}
	in.m[s] = s
	return s
}

func (pa *phpParser) decodeFile(b cstBatch) *fileResult {
	rec := b.rec
	if b.err != nil {
		if debugParse {
			println("parse failed", rec.rel, b.err.Error())
		}
		return nil
	}
	pa.src = b.src
	fr := &fileResult{
		fid: rec.id, moduleID: rec.moduleID, rel: rec.rel,
		isTest: rec.isTest, isGen: rec.isGen, isVend: rec.isVend,
		sum:    b.sum,
		byName: make(map[string][]localSym), byQual: make(map[string]int32),
		extends: make(map[string]string), fnSid: make(map[uint64]int32),
	}
	pa.rec = fr
	pa.nsSpans = pa.nsSpans[:0]

	tree := pa.p.decodeCST(b.cst, b.src)
	if tree == nil || len(tree.recs) == 0 {
		return nil
	}
	if pa.keepTrees {
		fr.trees = append(fr.trees, tree.recs...)
	}
	defer tree.free()
	root := tree.root()
	if hasErr(root) {
		fr.parseErrs, fr.missing = countErrors(root)
	}
	pa.scanMarkers()
	pa.parseImports(root)
	pa.walkScope(root, scope{sym: -1})
	pa.emitModuleScope(root)
	pa.parseFileExtra(root)
	pa.src = nil
	return fr
}

func (pa *phpParser) scanMarkers() {

	lines := cgSplitLinesInto(pa.linesBuf, decodeReplaceB(pa.src))
	pa.linesBuf = lines[:0]
	for i, line := range lines {

		if !(bytes.Contains(line, []byte("//")) || bytes.Contains(line, []byte("#")) ||
			bytes.Contains(line, []byte("*")) || bytes.Contains(line, []byte("--"))) {
			continue
		}
		m := markerRe.FindSubmatchIndex(line)
		if m == nil {
			continue
		}
		kind := strings.ToUpper(string(line[m[2]:m[3]]))
		txt := clipBytes(bytes.TrimSpace(line), 200)

		pa.rec.markers = append(pa.rec.markers, markerRow{
			fileID: pa.rec.fid, symNull: true, kind: pa.put(kind),
			txt: pa.put(string(txt)), line: int32(i + 1),
		})
	}
}

func (pa *phpParser) parseImports(root tsNode) {
	rec := pa.rec
	var spans []nsSpan
	strict := false
	uses := make(map[string]string)

	pa.cur.start(root)
	defer pa.cur.done()
	done := false
	for !done {
		n := pa.cur.node()
		switch t := kindName(n); t {
		case "namespace_definition":
			nm := fieldNode(n, fName)
			s := ""
			if hasNode(nm) {
				s = strings.TrimLeft(txt(nm, pa.src), "\\")
				s = strings.TrimSpace(s)
			}
			spans = append(spans, nsSpan{start: int32(startByte(n)), name: s})
		case "declare_directive":
			if strictTypesRe.MatchString(txt(n, pa.src)) {
				strict = true
			}
		case "namespace_use_declaration":
			prefix := ""
			group := fieldNode(n, fBody)
			if hasNode(group) {
				for _, ch := range namedKids(n) {
					if kindName(ch) == "namespace_name" {
						prefix = strings.TrimSpace(strings.TrimLeft(txt(ch, pa.src), "\\"))
						break
					}
				}
			}
			walkAll(n, func(x tsNode) bool {
				if kindName(x) != "namespace_use_clause" {
					return true
				}
				target, alias := "", ""
				hasAlias := false
				kind := "use"
				if tf := fieldNode(x, fType); hasNode(tf) {
					kind = "use " + strings.TrimSpace(txt(tf, pa.src))
				}
				if af := fieldNode(x, fAlias); hasNode(af) {
					alias = strings.TrimSpace(txt(af, pa.src))
					hasAlias = true
				}
				for _, ch := range namedKids(x) {
					if k := kindName(ch); k == "qualified_name" || k == "name" {
						target = strings.TrimLeft(strings.TrimSpace(txt(ch, pa.src)), "\\")
						break
					}
				}
				if prefix != "" && target != "" {
					target = prefix + "\\" + target
				}
				if target == "" {
					return true
				}
				short := alias
				if !hasAlias {
					short = target
					if i := strings.LastIndexByte(target, '\\'); i >= 0 {
						short = target[i+1:]
					}
				}
				uses[short] = target
				tgt := clip(target, 300)
				rec.imports = append(rec.imports, importRow{
					fileID: rec.fid, target: pa.put(tgt), targetIDNull: true, alias: pa.put(alias),
					aliasNull: !hasAlias, kind: pa.put(kind), line: int32(startRow(x)) + 1,
					ext:  !strings.HasPrefix(target, "App\\") && !strings.HasPrefix(target, "Tests\\"),
					wild: hasNode(group), nNames: 1,
				})
				return true
			})
		case "include_expression", "include_once_expression", "require_expression", "require_once_expression":
			kids := namedKids(n)
			var arg tsNode
			if len(kids) > 0 {
				arg = kids[0]
			}
			literal := hasNode(arg) && kindName(arg) == "string"
			var target string
			if literal {
				target = strings.Trim(txt(arg, pa.src), `'"`)
			} else {
				target = txt(n, pa.src)
			}
			target = clip(target, 300)
			kind := strings.Replace(t, "_expression", "", 1)
			rec.imports = append(rec.imports, importRow{
				fileID: rec.fid, target: pa.put(target), targetIDNull: true, aliasNull: true,
				kind: pa.put(kind), line: int32(startRow(n)) + 1, rel: true,
				dynamic: !literal, nNames: 1,
			})
		}
		if pa.cur.first() {
			continue
		}
		for !pa.cur.next() {
			if !pa.cur.up() {
				done = true
				break
			}
		}
	}
	if len(spans) == 0 {
		spans = []nsSpan{{start: 0, name: "", fallback: true}}
	}
	pa.nsSpans = spans
	rec.strict = strict

	for _, sp := range spans {
		if sp.fallback {
			continue
		}
		rec.nsRows = append(rec.nsRows, nsRow{fileID: rec.fid, name: pa.put(clip(sp.name, 200)),
			line: int32(countNL(pa.src[:sp.start]) + 1), strict: strict})
	}
}

func countNL(b []byte) int {
	n := 0
	for _, c := range b {
		if c == '\n' {
			n++
		}
	}
	return n
}

func (pa *phpParser) namespaceAt(byteOff uint) string {
	cur := ""
	for _, sp := range pa.nsSpans {
		if uint(sp.start) <= byteOff {
			cur = sp.name
		} else {
			break
		}
	}
	return cur
}

func namedKids(n tsNode) []tsNode {
	c := namedChildCount(n)
	if c == 0 {
		return nil
	}
	out := make([]tsNode, 0, c)
	for i := range c {
		out = append(out, namedChildAt(n, i))
	}
	return out
}

func (pa *phpParser) kidsBuf() *[]tsNode {
	if pa.kids == nil {
		s := make([]tsNode, 0, 32)
		pa.kids = &s
	}
	return pa.kids
}

func (pa *phpParser) kidsOf(n tsNode) []tsNode {
	c := namedChildCount(n)
	bp := pa.kidsBuf()
	if c == 0 {
		*bp = (*bp)[:0]
		return nil
	}
	if cap(*bp) < c {
		*bp = make([]tsNode, 0, c)
	}
	*bp = (*bp)[:c]
	for i := range c {
		(*bp)[i] = namedChildAt(n, i)
	}
	return *bp
}

type walkItem struct {
	n  tsNode
	sc scope
}

func (pa *phpParser) walkScope(node tsNode, sc scope) {
	kids := pa.kidsOf(node)
	stack := make([]walkItem, 0, len(kids)+8)
	for _, kid := range slices.Backward(kids) {
		stack = append(stack, walkItem{kid, sc})
	}
	for len(stack) > 0 {
		it := stack[len(stack)-1]
		stack = stack[:len(stack)-1]
		cur, s := it.n, it.sc
		if kind := kFuncKind[slot(kindID(cur))]; kind != "" {
			sid := pa.emitFunction(cur, s, kind)
			nm := pa.nodeName(cur)
			if nm == "" {
				nm = "?"
			}
			inner := scope{sym: sid, qualPre: s.qualPre + nm + ".", typeName: s.typeName, typeID: s.typeID, depth: s.depth + 1}
			stack = pa.pushBody(stack, cur, inner)
			continue
		}
		if kind := kTypeKind[slot(kindID(cur))]; kind != "" {
			sid := pa.emitType(cur, s, kind)
			nm := pa.nodeName(cur)
			if nm == "" {
				nm = "?"
			}
			inner := scope{sym: sid, qualPre: s.qualPre + nm + ".", typeName: nm, typeID: sid, depth: s.depth + 1}
			stack = pa.pushBody(stack, cur, inner)
			continue
		}
		k := pa.kidsOf(cur)
		for _, v := range slices.Backward(k) {
			stack = append(stack, walkItem{v, s})
		}
	}
}

func (pa *phpParser) pushBody(stack []walkItem, cur tsNode, inner scope) []walkItem {
	src := cur
	if b := fieldNode(cur, fBody); hasNode(b) {
		src = b
	}
	k := pa.kidsOf(src)
	for _, v := range slices.Backward(k) {
		stack = append(stack, walkItem{v, inner})
	}
	return stack
}

func (pa *phpParser) nodeName(n tsNode) string {
	t := slot(kindID(n))
	if kindID(n) == kPropertyHook {
		hook := ""
		for _, c := range namedKids(n) {
			if kindID(c) == kNameNode {
				hook = txt(c, pa.src)
				break
			}
		}
		prop := pa.hookProperty(n)
		if prop == "" {
			prop = "?"
		}
		if hook == "" {
			hook = "?"
		}
		return "$" + prop + "::" + hook
	}
	field := kNameField[t]
	if field == absentKind {
		field = defaultNameField
	}
	if field != "" {
		if c := fieldNodeByName(n, field); hasNode(c) {
			return strings.TrimSpace(txt(c, pa.src))
		}
	}
	for _, c := range namedKids(n) {
		if kIdents[slot(kindID(c))] {
			return strings.TrimSpace(txt(c, pa.src))
		}
	}
	return ""
}

func (pa *phpParser) visibilityOf(n tsNode) string {
	t := kindName(n)
	for _, c := range namedKids(n) {
		if kindName(c) == "visibility_modifier" {
			v := strings.TrimSpace(txt(c, pa.src))
			if before, _, ok := strings.Cut(v, "("); ok {
				return before
			}
			return v
		}
	}
	if t == "method_declaration" || t == "property_declaration" {
		return "public"
	}
	return ""
}

func (pa *phpParser) modifiers(n tsNode) int {
	var out int
	c := namedChildCount(n)
	for i := range c {
		kid := namedChildAt(n, i)
		if !kModifiers[slot(kindID(kid))] {
			continue
		}
		switch strings.TrimSpace(txt(kid, pa.src)) {
		case "abstract":
			out |= modAbstract
		case "final":
			out |= modFinal
		case "static":
			out |= modStatic
		case "readonly":
			out |= modReadonly
		case "public":
			out |= modPublic
		case "private":
			out |= modPrivate
		case "protected":
			out |= modProtected
		case "var":
			out |= modVar
		}
	}
	return out
}

func (pa *phpParser) attributeNames(n tsNode) []string {
	attrs := fieldNode(n, fAttributes)
	if !hasNode(attrs) {
		return nil
	}
	var out []string
	walkAll(attrs, func(x tsNode) bool {
		if kindName(x) != "attribute" {
			return true
		}
		for _, c := range namedKids(x) {
			if k := kindName(c); k == "name" || k == "qualified_name" {
				out = append(out, strings.TrimLeft(strings.TrimSpace(txt(c, pa.src)), "\\"))
				break
			}
		}
		return true
	})
	return out
}

var slocCommentPrefixes = []string{"//", "#", "/*", "*", "*/", `"""`, "'''", "--", "%"}

func (pa *phpParser) slocOf(n tsNode) int32 {
	seg := pa.src[startByte(n):endByte(n)]
	var c int32
	start := 0
	for i := 0; i <= len(seg); i++ {
		if i == len(seg) || seg[i] == '\n' {
			if i > start {

				s := bytes.TrimSpace(seg[start:i])
				if len(s) > 0 {
					skip := false
					for _, p := range slocCommentPrefixes {
						if hasBytePrefix(s, p) {
							skip = true
							break
						}
					}
					if !skip {
						c++
					}
				}
			}
			start = i + 1
		}
	}
	return c
}

func hasBytePrefix(b []byte, prefix string) bool {
	return len(b) >= len(prefix) && string(b[:len(prefix)]) == prefix
}

func clip(s string, n int) string {
	if utf8.RuneCountInString(s) <= n {
		return s
	}
	i := 0
	for c := range s {
		if i == n {
			return s[:c]
		}
		i++
	}
	return s
}

func clipBytes(s []byte, n int) []byte {
	if utf8.RuneCount(s) <= n {
		return s
	}
	i := 0

	for c := range string(s) {
		if i == n {
			return s[:c:c]
		}
		i++
	}
	return s
}

var _ = sort.Ints

func (pa *phpParser) onCall(st *stats, n tsNode, src []byte, loopDepth int) {
	st.bump(cNCalls)
	if loopDepth > 0 {
		st.bump(cCallInLoop)
	}
	var name string
	dynamic := false

	switch t := kindName(n); t {
	case "function_call_expression":
		fn := fieldNode(n, fFunction)
		if !hasNode(fn) {
			dynamic = true
		} else if k := kindName(fn); k == "name" || k == "qualified_name" {
			name = strings.TrimLeft(strings.TrimSpace(txt(fn, src)), "\\")
		} else {

			dynamic = true
		}
	case "member_call_expression", "nullsafe_member_call_expression":
		nm := fieldNode(n, fName)
		if hasNode(nm) && kindName(nm) == "name" {
			name = "->" + strings.TrimSpace(txt(nm, src))
		} else {
			dynamic = true
		}
	case "scoped_call_expression":
		sc := fieldNode(n, fScope)
		nm := fieldNode(n, fName)
		if hasNode(nm) && kindName(nm) == "name" && hasNode(sc) {
			cls := strings.TrimLeft(strings.TrimSpace(txt(sc, src)), "\\")
			if k := kindName(sc); k == "name" || k == "qualified_name" || k == "relative_scope" {
				name = cls + "::" + strings.TrimSpace(txt(nm, src))

				if facadeClasses[cls] {
					st.bump(cNFacadeCall)
				}
			} else {
				dynamic = true
			}
		} else {
			dynamic = true
		}
	case "object_creation_expression":
		var cls tsNode
		for _, c := range namedKids(n) {
			switch kindName(c) {
			case "name", "qualified_name", "variable_name", "relative_scope",
				"anonymous_class", "member_access_expression", "subscript_expression":
				cls = c
			}
			if hasNode(cls) {
				break
			}
		}
		if !hasNode(cls) || kindName(cls) == "anonymous_class" {
			return
		}
		switch kindName(cls) {
		case "name", "qualified_name", "relative_scope":
			name = "new " + strings.TrimLeft(strings.TrimSpace(txt(cls, src)), "\\")
		default:
			dynamic = true
		}
		if loopDepth > 0 {
		}
	}

	st.calls = append(st.calls, callRec{name: clip(name, 200),
		line: int32(startRow(n)) + 1, dynamic: dynamic, inLoop: loopDepth > 0})
	if dynamic {
	}
	if name != "" && loopDepth > 0 {
		for _, lc := range loopCallCounters {
			if strings.Contains(name, lc.needle) {
				st.bump(lc.col)
			}
		}
	}
	nb := strings.TrimLeft(name, "->")
	if escapers[nb] || escapers[name] {
		st.bump(cNEscapedOutput)
	}

	b := nb
	if i := strings.LastIndex(b, "::"); i >= 0 {
		b = b[i+2:]
	}
	b = strings.ToLower(b)
	switch b {
	case "extract", "compact":
		st.bump(cNExtractCall)
	case "md5", "sha1", "crc32":
		st.bump(cNWeakHash)
	case "rand", "mt_rand", "srand", "mt_srand", "uniqid":
		st.bump(cNWeakRandom)
	case "file_get_contents", "fopen", "curl_exec", "fsockopen":
		st.bump(cNRemoteFetch)
	case "header":
		st.bump(cNHeaderCall)
	case "session_start", "setcookie", "session_regenerate_id":
		st.bump(cNSessionCall)
	case "move_uploaded_file":
		st.bump(cNMoveUploaded)
	case "serialize", "unserialize":
		st.bump(cNSerializeCall)
	}
	if b == "simplexml_load_file" || b == "simplexml_load_string" ||
		strings.HasPrefix(name, "new DOMDocument") || strings.HasPrefix(name, "new XMLReader") ||
		strings.HasPrefix(name, "new SimpleXMLElement") {
		st.bump(cNXxeParser)
	}

	if (b == "fopen" || b == "file_get_contents" || b == "readfile" || b == "file") && name == b {
		if first := firstArgument(n); hasNode(first) {
			atxt := strings.TrimSpace(txt(first, src))
			if len(atxt) < 2 || atxt[0] != '\'' && atxt[0] != '"' || atxt[len(atxt)-1] != atxt[0] {
				st.bump(cNDynamicOpen)
			}
		}
	}
	if b == "error_log" {
		st.bump(cNLogCall)
	}
	nl := strings.ToLower(name)
	for _, k := range authMarkers {
		if strings.Contains(nl, k) {
			st.bump(cNAuthCall)
			break
		}
	}
	switch name {
	case "->all", "->input", "->only", "->except", "->post", "->json":
		st.bump(cNRequestInput)
	}
	if b == "dd" || b == "dump" || b == "ray" {
		st.bump(cNDebugCall)
	}
	if argShapeSinks[b] || cleartextSinks[b] {
		pa.argShapeChecks(st, n, src, b)
	}
	if loopDepth > 0 {
		switch b {
		case "in_array":
			st.bump(cNInarrayInLoop)
		case "array_merge", "array_push", "array_combine":
			st.bump(cNArrayMergeInLoop)
		case "count", "sizeof", "strlen", "str_repeat":
			st.bump(cNCountInLoop)
		case "preg_replace", "preg_match", "preg_split":
			st.bump(cNPregInLoop)
		case "array_key_exists", "isset", "property_exists":
			st.bump(cNKeycheckInLoop)
		}
	}
}

func (pa *phpParser) argShapeChecks(st *stats, n tsNode, src []byte, b string) {
	args := fieldNode(n, fArguments)
	if !hasNode(args) {
		return
	}
	var akids []tsNode
	for _, c := range namedKids(args) {
		if kindName(c) == "argument" {
			akids = append(akids, c)
		}
	}
	nArgs := len(akids)
	var first tsNode
	if nArgs > 0 {
		kids := namedKids(akids[0])
		if len(kids) > 0 {
			first = kids[0]
		}
	}
	isLiteral := hasNode(first) && len(namedKids(akids[0])) == 1 && kindName(first) == "string"
	switch {
	case (b == "in_array" || b == "array_search") && nArgs < 3:

		st.bump(cNInarrayLoose)
	case b == "setcookie" && nArgs < 3:

		st.bump(cNCookieLean)
	case strings.HasPrefix(b, "preg_") && hasNode(first) && !isLiteral:
		st.bump(cNPregDynamic)
	case b == "file_put_contents" && hasNode(first) && !isLiteral:
		st.bump(cNFileWriteDyn)
	case b == "fopen" && hasNode(first) && !isLiteral:
		mode := ""
		if nArgs > 1 {
			if kids := namedKids(akids[1]); len(kids) > 0 {
				mode = strings.Trim(strings.TrimSpace(txt(kids[0], src)), `'"`)
			}
		}
		if mode != "" && strings.ContainsAny(mode[:1], "wacx+") {
			st.bump(cNFileWriteDyn)
		}
	}
	if cleartextSinks[b] && strings.Contains(txt(args, src), "http://") {
		st.bump(cNCleartextFetch)
	}
}

func firstArgument(n tsNode) tsNode {
	args := fieldNode(n, fArguments)
	if !hasNode(args) {
		return tsNode{}
	}
	kids := namedKids(args)
	if len(kids) == 0 {
		return tsNode{}
	}
	return kids[0]
}

func (pa *phpParser) onString(st *stats, n tsNode, text []byte, loopDepth int) {
	val := bytes.Trim(text, `'"`)
	if len(val) >= secretMinLen && !bytes.ContainsAny(val, " ") && secretRe.Match(val) {
		st.secrets = append(st.secrets, litRec{value: clip(string(val), 200),
			line: int32(startRow(n)) + 1})
	}
	if !sqlRe.Match(text) {
		return
	}
	st.bump(cNSQLLiteral)
	if loopDepth > 0 {
		st.bump(cQueryInLoop)
	}
}

func (pa *phpParser) onNode(st *stats, n tsNode, src []byte, loopDepth int) {
	switch t := kindName(n); t {
	case "binary_expression":
		op := fieldNode(n, fOperator)
		o := ""
		if hasNode(op) {
			o = txt(op, src)
		}
		switch o {
		case "==", "!=", "<>":
			st.bump(cNLooseCompare)
		case "===", "!==":
			st.bump(cNStrictCompare)
		case "<", ">", "<=", ">=", "<=>":
		case "&&", "||", "and", "or", "xor":
		case "??":
			st.bump(cNNullCheck)
		case "|>":
		case "&", "|", "^":
		case "<<", ">>":
		case "+", "-", "*", "/", "%", "**":
		case ".":
			if loopDepth > 0 {
			}
		}
	case "augmented_assignment_expression":
		op := fieldNode(n, fOperator)
		if hasNode(op) && txt(op, src) == ".=" && loopDepth > 0 {
		}
	case "unary_op_expression":
		op := fieldNode(n, fOperator)
		if hasNode(op) && txt(op, src) == "!" {
		}
	case "conditional_expression":
		if !hasNode(fieldNode(n, fConsequence)) {
			st.bump(cNNullCheck)
		}
	case "echo_statement", "print_intrinsic":
		body := txt(n, src)
		if strings.Contains(body, "$") || strings.Contains(body, "<?=") {
			esc := false
			for e := range escapers {
				if strings.Contains(body, e+"(") {
					esc = true
					break
				}
			}
			if esc {
				st.bump(cNEscapedOutput)
			} else {
				st.bump(cNRawEcho)
			}
		}
	case "return_statement":
		if namedChildCount(n) == 0 {
		}
	case "catch_clause":
		if ty := fieldNode(n, fType); hasNode(ty) {
			tt := txt(ty, src)
			if strings.Contains(tt, "Throwable") ||
				strings.TrimLeft(strings.TrimSpace(tt), "\\") == "Exception" {
				st.bump(cNCatchBroad)
			}
		}
		if body := fieldNode(n, fBody); hasNode(body) && namedChildCount(body) == 0 {
			st.bump(cNCatchEmpty)
		}
	case "include_expression", "include_once_expression", "require_expression", "require_once_expression":
		kids := namedKids(n)
		if len(kids) > 0 && kindName(kids[0]) != "string" {
			st.bump(cNDynamicInclude)
		}
	case "assignment_expression":
		left := fieldNode(n, fLeft)
		if !hasNode(left) {
			break
		}
		switch kindName(left) {
		case "member_access_expression":
			if nm := fieldNode(left, fName); hasNode(nm) && kindName(nm) == "variable_name" {

				st.bump(cNDynamicPropWrite)
			}
		case "scoped_property_access_expression":

			st.bump(cNStaticPropWrite)
		case "subscript_expression":
			for _, ch := range namedKids(left) {
				if kindName(ch) == "variable_name" && txt(ch, src) == "$_SESSION" {
					st.bump(cNSessionWrite)
					break
				}
			}
		}
	case "variable_name":
		if superglobals[txt(n, src)] {
			st.bump(cNSuperglobalReads)
		}
	case "function_call_expression":
		fn := fieldNode(n, fFunction)
		if !hasNode(fn) {
			break
		}
		if k := kindName(fn); k != "name" && k != "qualified_name" {
			break
		}
		base := strings.TrimLeft(strings.TrimSpace(txt(fn, src)), "\\")
		if i := strings.LastIndexByte(base, '\\'); i >= 0 {
			base = base[i+1:]
		}
		switch base {
		case "eval":
			st.bump(cNEval)
		case "isset", "empty", "is_null":
			st.bump(cNNullCheck)
		case "preg_match", "preg_replace", "preg_split", "preg_match_all":
			st.bump(cNRegexLit)
		}
	}
}

func (pa *phpParser) parseFileExtra(root tsNode) {
	pa.cur.start(root)
	defer pa.cur.done()
	done := false
	for !done {
		n := pa.cur.node()
		if fileExtraTypes[kindName(n)] {
			pa.fileExtraNode(n)
		}
		if pa.cur.first() {
			continue
		}
		for !pa.cur.next() {
			if !pa.cur.up() {
				done = true
				break
			}
		}
	}
}

func (pa *phpParser) fileExtraNode(n tsNode) {
	rec := pa.rec
	src := pa.src
	switch t := kindName(n); t {
	case "variable_name":
		v := txt(n, src)
		if !superglobals[v] {
			return
		}
		key := ""
		if par := parentNode(n); hasNode(par) && kindName(par) == "subscript_expression" {

			for _, ch := range namedKids(par) {
				key = clip(strings.Trim(txt(ch, src), `'"`), 80)
				break
			}
		}
		rec.superglobals = append(rec.superglobals, superReadRow{
			sym: pa.sidAt(n), symNull: pa.sidAt(n) < 0, fileID: rec.fid, v: pa.put(v), key: pa.put(key),
			line: int32(startRow(n)) + 1, inLoop: inLoop(n), psalm: psalmTainted[v],
		})
	case "function_call_expression", "member_call_expression",
		"nullsafe_member_call_expression", "scoped_call_expression":
		pa.maybeSQLSite(n)
		pa.maybeDynamicSite(n)
	case "object_creation_expression":
		kids := namedKids(n)
		if len(kids) > 0 {
			switch kindName(kids[0]) {
			case "variable_name", "member_access_expression", "subscript_expression":
				sid := pa.sidAt(n)
				rec.dynSites = append(rec.dynSites, dynSiteRow{
					sym: sid, symNull: sid < 0, fileID: rec.fid, kind: pa.put("variable_class"),
					target: pa.put(clip(txt(kids[0], src), 120)), inLoop: inLoop(n),
					line: int32(startRow(n)) + 1,
				})
			}
		}
	case "dynamic_variable_name":
		sid := pa.sidAt(n)
		rec.dynSites = append(rec.dynSites, dynSiteRow{
			sym: sid, symNull: sid < 0, fileID: rec.fid, kind: pa.put("variable_variable"),
			target: pa.put(clip(txt(n, src), 120)), inLoop: inLoop(n),
			line: int32(startRow(n)) + 1,
		})
	case "include_expression", "include_once_expression", "require_expression", "require_once_expression":
		kids := namedKids(n)
		if len(kids) > 0 && kindName(kids[0]) != "string" {
			sid := pa.sidAt(n)
			rec.dynSites = append(rec.dynSites, dynSiteRow{
				sym: sid, symNull: sid < 0, fileID: rec.fid, kind: pa.put("variable_include"),
				target: pa.put(clip(txt(n, src), 120)), inLoop: inLoop(n),
				line: int32(startRow(n)) + 1,
			})
		}
	case "variadic_placeholder":
		par := parentNode(n)
		for hasNode(par) && kindName(par) != "arguments" {
			par = parentNode(par)
		}
		target := "..."
		if hasNode(par) {
			if call := parentNode(par); hasNode(call) {
				target = clip(txt(call, src), 120)
			}
		}
		sid := pa.sidAt(n)
		rec.dynSites = append(rec.dynSites, dynSiteRow{
			sym: sid, symNull: sid < 0, fileID: rec.fid, kind: pa.put("first_class_callable"),
			target: pa.put(target), inLoop: inLoop(n), line: int32(startRow(n)) + 1,
		})
	}
}

func (pa *phpParser) sidAt(n tsNode) int32 {
	cur := parentNode(n)
	for hasNode(cur) {
		if kFuncKind[slot(kindID(cur))] != "" {
			if sid, ok := pa.rec.fnSid[uint64(pa.rec.fid)<<32|uint64(startByte(cur))]; ok {
				return sid
			}
			return -1
		}
		cur = parentNode(cur)
	}
	return -1
}

func inLoop(n tsNode) bool {
	cur := parentNode(n)
	for hasNode(cur) {
		if kLoops[slot(kindID(cur))] {
			return true
		}
		if kFuncKind[slot(kindID(cur))] != "" {
			return false
		}
		cur = parentNode(cur)
	}
	return false
}

func (pa *phpParser) maybeDynamicSite(n tsNode) {
	rec := pa.rec
	src := pa.src
	kind, target := "", ""
	switch t := kindName(n); t {
	case "function_call_expression":
		fn := fieldNode(n, fFunction)
		if !hasNode(fn) {
			return
		}
		if k := kindName(fn); k == "name" || k == "qualified_name" {
			base := strings.TrimLeft(strings.TrimSpace(txt(fn, src)), "\\")
			if i := strings.LastIndexByte(base, '\\'); i >= 0 {
				base = base[i+1:]
			}
			if !dynamicCallNames[base] {
				return
			}
			if base == "eval" || base == "create_function" {
				kind = "eval"
			} else {
				kind = base
			}
			if args := fieldNode(n, fArguments); hasNode(args) {
				target = clip(txt(args, src), 120)
			}
		} else {
			kind = "variable_function"
			target = clip(txt(fn, src), 120)
		}
	case "member_call_expression", "nullsafe_member_call_expression":
		nm := fieldNode(n, fName)
		if !hasNode(nm) || kindName(nm) == "name" {
			return
		}
		kind = "variable_method"
		target = clip(txt(n, src), 120)
	case "scoped_call_expression":
		nm := fieldNode(n, fName)
		sc := fieldNode(n, fScope)
		if (!hasNode(nm) || kindName(nm) == "name") && (!hasNode(sc) || kindName(sc) != "variable_name") {
			return
		}
		kind = "variable_static"
		target = clip(txt(n, src), 120)
	}
	if kind == "" {
		return
	}
	sid := pa.sidAt(n)
	rec.dynSites = append(rec.dynSites, dynSiteRow{
		sym: sid, symNull: sid < 0, fileID: rec.fid, kind: pa.put(kind), target: pa.put(target),
		inLoop: inLoop(n), line: int32(startRow(n)) + 1,
	})
}

func (pa *phpParser) maybeSQLSite(n tsNode) {
	rec := pa.rec
	src := pa.src
	callee, driver := pa.sqlCallee(n, false)
	args := fieldNode(n, fArguments)
	if !hasNode(args) {
		return
	}
	var first tsNode
	for _, a := range namedKids(args) {
		if kindName(a) == "argument" {
			kids := namedKids(a)
			if len(kids) > 0 {
				first = kids[0]
			}
			break
		}
	}
	atxt := txt(args, src)
	looksSQL := sqlRe.MatchString(atxt)
	if callee == "" && !looksSQL {
		return
	}
	if callee == "" {
		callee, driver = pa.sqlCallee(n, true)
		if callee == "" {
			return
		}
	}
	build, sanitized := buildKind(first, src)
	prepared := placeholderRe.MatchString(atxt) ||
		strings.HasSuffix(callee, "prepare") || strings.HasSuffix(callee, "::prepare")
	if !sanitized {
		for e := range sqlEscapers {
			if strings.Contains(atxt, e) {
				sanitized = true
				break
			}
		}
	}
	hasSuper := false
	for _, sg := range superglobalWalked {
		if strings.Contains(atxt, sg) {
			hasSuper = true
			break
		}
	}
	sid := pa.sidAt(n)
	rec.sqlSites = append(rec.sqlSites, sqlSiteRow{
		sym: sid, symNull: sid < 0, fileID: rec.fid, callee: pa.put(clip(callee, 120)),
		driver: pa.put(driver), buildKind: pa.put(build), sanitized: sanitized || build == "literal",
		prepared: prepared, hasSuper: hasSuper, inLoop: inLoop(n),
		line:    int32(startRow(n)) + 1,
		snippet: pa.put(clip(strings.ReplaceAll(atxt, "\n", " "), 180)),
	})
}

func (pa *phpParser) sqlCallee(n tsNode, force bool) (string, string) {
	src := pa.src
	t := kindName(n)
	if t == "function_call_expression" {
		fn := fieldNode(n, fFunction)
		if !hasNode(fn) || (kindName(fn) != "name" && kindName(fn) != "qualified_name") {
			if force {
				return "dynamic", "unknown"
			}
			return "", ""
		}
		base := strings.TrimLeft(strings.TrimSpace(txt(fn, src)), "\\")
		if i := strings.LastIndexByte(base, '\\'); i >= 0 {
			base = base[i+1:]
		}
		if d, ok := sqlFunctions[base]; ok {
			return base, d
		}
		if force {
			return base, "unknown"
		}
		return "", ""
	}
	nm := fieldNode(n, fName)
	if !hasNode(nm) || kindName(nm) != "name" {
		if force {
			return "dynamic", "unknown"
		}
		return "", ""
	}
	base := txt(nm, src)
	if t == "scoped_call_expression" {
		sc := fieldNode(n, fScope)
		cls := ""
		if hasNode(sc) {
			cls = strings.TrimLeft(strings.TrimSpace(txt(sc, src)), "\\")
		}
		d, ok := sqlMethods[base]
		if ok || force {
			return cls + "::" + base, orUnknown(d, force)
		}
		return "", ""
	}
	d, ok := sqlMethods[base]
	if ok || force {
		return "->" + base, orUnknown(d, force)
	}
	return "", ""
}

func orUnknown(d string, force bool) string {
	if d != "" {
		return d
	}
	if force {
		return "unknown"
	}
	return ""
}

func buildKind(arg tsNode, src []byte) (string, bool) {
	if !hasNode(arg) {
		return "variable", false
	}
	switch t := kindName(arg); t {
	case "string":
		return "literal", true
	case "encapsed_string", "heredoc":
		hasVar := false
		walkAll(arg, func(x tsNode) bool {
			switch kindName(x) {
			case "variable_name", "member_access_expression", "subscript_expression",
				"nullsafe_member_access_expression":
				hasVar = true
				return false
			}
			return true
		})
		if hasVar {
			return "interp", false
		}
		return "literal", true
	case "nowdoc":
		return "literal", true
	case "binary_expression":
		op := fieldNode(arg, fOperator)
		if hasNode(op) && txt(op, src) == "." {
			t := txt(arg, src)
			for e := range sqlEscapers {
				if strings.Contains(t, e) {
					return "concat", true
				}
			}
			return "concat", false
		}
		return "variable", false
	case "function_call_expression":
		fn := fieldNode(arg, fFunction)
		base := ""
		if hasNode(fn) {
			base = strings.TrimSpace(txt(fn, src))
			if i := strings.LastIndexByte(base, '\\'); i >= 0 {
				base = base[i+1:]
			}
		}
		switch base {
		case "sprintf", "vsprintf", "printf", "str_replace", "strtr":
			return "format", false
		}
		if sqlEscapers[base] || base == "intval" || base == "floatval" {
			return "variable", true
		}
		return "variable", false
	}
	return "variable", false
}

type modRollup struct {
	cols    []string
	pred    func(g *graph, s int) bool
	notTest bool
	reduce  func(g *graph, mod int32, acc *modAcc) []cell
	order   func(a, x []cell) bool
}

type modAcc struct {
	fns                             int32
	calls, external, unresolved     int32
	dynCall, dynMethod, dynClass    int32
	typed, untyped, nullable        int32
	unions, inter, looseCmp         int32
	throws, trys, catches           int32
	broadCatches, emptyCatches      int32
	suppressed                      int32
	debugCalls                      int32
	rawEcho                         int32
	superReads, psalmTainted        int32
	sqlInterp, sqlConcat            int32
	shell, facadeCalls, staticCalls int32
	nullChecks, nullSafe            int32
	writes, txCalls, queueCalls     int32
}

func (a *modAcc) add(g *graph, s int) {
	a.calls += g.col(s, cNCalls)
	a.external += g.col(s, cNExternalCalls)
	a.unresolved += g.col(s, cNUnresolvedCalls)
	a.dynCall += g.col(s, cNDynamicCall)
	a.dynMethod += g.col(s, cNDynamicMethod)
	a.dynClass += g.col(s, cNDynamicNew)
	a.typed += g.col(s, cNTypeDeclarations)
	a.untyped += g.col(s, cNUntypedParams)
	a.nullable += g.col(s, cNNullableTypes)
	a.unions += g.col(s, cNUnionTypes)
	a.inter += g.col(s, cNIntersectionTypes)
	a.looseCmp += g.col(s, cNLooseCompare)
	a.throws += g.col(s, cNThrow)
	a.trys += g.col(s, cNTry)
	a.catches += g.col(s, cNCatch)
	a.broadCatches += g.col(s, cNCatchBroad)
	a.emptyCatches += g.col(s, cNCatchEmpty)
	a.suppressed += g.col(s, cNErrorSuppress)
	a.debugCalls += g.col(s, cNDebugCall)
	a.rawEcho += g.col(s, cNRawEcho)
	a.superReads += g.col(s, cNSuperglobalReads)
	a.psalmTainted += g.col(s, cNPsalmTainted)
	a.sqlInterp += g.col(s, cNSQLInterp)
	a.sqlConcat += g.col(s, cNSQLConcat)
	a.shell += g.col(s, cNShell)
	a.facadeCalls += g.col(s, cNFacadeCall)
	a.staticCalls += g.col(s, cNStaticCalls)
	a.nullChecks += g.col(s, cNNullCheck)
	a.nullSafe += g.col(s, cNNullSafe)
	a.writes += g.col(s, cNWrite)
	a.txCalls += g.col(s, cNTransaction)
	a.queueCalls += g.col(s, cNQueue)
}

func (g *graph) rollup(r modRollup) *result {
	b := newR(r.cols...)
	accs := make(map[int32]*modAcc, len(g.mods))
	order := make([]int32, 0, len(g.mods))
	for s := 0; s < g.sym.n; s++ {
		if r.notTest && g.isTestFileOfSym(s) {
			continue
		}
		if r.pred != nil && !r.pred(g, s) {
			continue
		}
		m := g.sym.cols[cModuleID][s]
		a := accs[m]
		if a == nil {
			a = &modAcc{}
			accs[m] = a
			order = append(order, m)
		}
		a.fns++
		a.add(g, s)
	}
	insertionSortAny(order, func(x, y int32) bool { return x < y })
	for _, m := range order {
		if row := r.reduce(g, m, accs[m]); row != nil {
			b.row(row...)
		}
	}
	if r.order != nil {
		insertionSort(b.r.rows, r.order)
	}
	return b.done()
}

func pctCell(num, den int32) cell {
	if den == 0 {
		return cellNull()
	}
	return cellI(100 * int64(num) / int64(den))
}

func buildMetrics() []question {
	return []question{
		{
			name:  "graph-blindspots",
			title: "Read this first: where a PHP call graph cannot see",
			notes: `ANSWERS how much of every other answer below is guesswork. In PHP this is
     not a footnote -- call_user_func, $obj->$m(), new $class,
     __call/__callStatic and a facade layer resolved at run time are
     idiomatic, and each one deletes an edge.
ACT read pct_blind before believing any reachability claim in Q2-Q7. On a
     framework with a container and facades a high number is the CORRECT
     answer, not a defect to tune away. Compare namespaces against each
     other rather than against zero.
MISLEADS external calls (PHP's ~1,500 built-ins, PDO, SPL) leave the tree
     by design and are NOT counted as blindness. A resolved edge can still
     be wrong: a method call resolves by SHORT NAME and prefers the
     enclosing class, so $other->save() inside a class that also defines
     save() points at the wrong one. magic_call is the count of classes
     in this namespace defining __call/__callStatic -- every call into one
     of those is unresolvable in principle, not just here.`,
			fn: mGraphBlindspots,
		},
		{
			name:  "strict-types-coverage",
			title: "declare(strict_types=1) coverage against scalar-parameter density",
			notes: `ANSWERS where PHP is still doing silent type coercion on the arguments that
     matter. Without strict_types, passing "5 apples" to an int parameter
     coerces to 5 and passing "abc" coerces to 0 -- and 0 is a valid user
     id in most schemas.
ACT the ABSENCE of the declare is the finding, and it is per FILE, so a
     namespace with high typed_params and low strict_files is doing the
     work of types without the enforcement. Add the declare to those files
     first; they have the most to gain and the least to break.
MISLEADS strict_types governs the CALLEE's file in PHP, not the caller's,
     which is the opposite of most people's intuition. Coercion at a call
     site is decided by where the called function is DECLARED. A namespace
     of pure value objects with no scalar parameters gains nothing.`,
			fn: mStrictTypes,
		},
		{
			name:  "property-hooks",
			title: "PHP 8.4 property hooks: a field read that is really a call",
			notes: `ANSWERS which property accesses the call graph must model as invocations.
     $order->total looks like a field read in every tool built before
     8.4 and in every reviewer's head, but with a get hook it executes a
     body -- which can query, throw, or recurse.
ACT a hook with calls>0 is a function hiding behind field syntax; a virtual
     hook (one that never touches its own backing field) has NO storage at
     all, so every read is unconditionally a call. Those are the ones to
     check for work in a loop.
MISLEADS no edge points AT a hook, because no call site names it -- fan_in
     is structurally 0 for every row here and means nothing. A codebase
     below 8.4 shows an empty table for reasons of version, not style; the
     same is true of n_pipe_operator and 8.5.`,
			fn: mPropertyHooks,
		},
		{
			name:  "god-classes",
			title: "Classes and functions doing too much, by every measure at once",
			notes: `ANSWERS the classes where every size measure points the same way. One
     measure alone is an argument; four agreeing is a pattern.
ACT split on the widest axis first. The worst_method_cog column says
     where the next reader will get lost.
MISLEADS bulk is a weighted sum, so a class with many one-line methods
     outranks a shorter one that is genuinely hard to read; read the
     columns, not the total.`,
			fn: mGodClasses,
		},
		{
			name:  "risk-ranked",
			title: "Review order: if you can only read N functions this week, which N",
			notes: `ANSWERS the whole-function risk ranking, with the inputs that produced it
     shown so a reader can disagree with the weighting rather than with the
     data.
ACT start at the top and stop when the risk drops below the cost of
     reading. The formula is deliberately simple so it can be argued
     with; it is not a vulnerability score.
MISLEADS has_strict_types is always 0 and contributes a flat 6 to every
     row, so it does not rank anything -- it is in the score because the
     constant is part of the risk formula, not because it measures
     anything here.`,
			fn: mRiskRanked,
		},
		{
			name:  "parse-coverage",
			title: "What this run could not read",
			notes: `ANSWERS whether the numbers above cover the code you think they cover.
ACT a file with parsed=0 contributed nothing at all. A file with errors
     contributed the symbols around the damage and nothing inside it.
MISLEADS tree-sitter-php 0.24.1 rejects exactly three of PHP 8.5's
     additions out of a 23-case 8.0-8.5 sweep: the (void) cast, clone $x
     with {...}, and final on a promoted constructor property. A file
     whose only symptom is one or three parse errors is a grammar one
     version behind the language, not a broken file -- meta.grammar_note
     carries the same list. Everything else in that sweep, 8.5's |> pipe
     included, parses clean.
     A file can also parse perfectly and still be misunderstood: inline
     HTML islands, eval and __call all parse cleanly and carry no
     symbols anyone can follow, and symbols_=0 with errors=0 is that case.`,
			fn: mParseCoverage,
		},
		{
			name:  "hot-multipliers",
			title: "Where one fix pays back many times: highest fan-in",
			notes: `ANSWERS the functions whose fix touches the most code. This is the
     return-on-effort ranking, and it is the one place fan_in is the
     point rather than a context column.
ACT a rename or a signature change here is a project-wide edit; do it
     with a compiler or a refactoring tool, not by hand.
MISLEADS fan_in counts resolved edges, so a helper reached through a
     container or a magic __call is not counted, and a function reached
     only from tests looks as hot as one reached from production.`,
			fn: mHotMultipliers,
		},
		{
			name:  "array-scan-in-a-hot-method",
			title: "in_array, array_merge or count inside a loop, weighted by how many callers reach it",
			notes: `ANSWERS the per-iteration scans in methods many callers reach. The
     combination is what makes it expensive: a hot method with a loop
     over an array is a hot method with a per-call allocation.
ACT hoist the lookup out of the loop into a keyed map, and precompute
     the size once.
MISLEADS distinct_callers counts resolved non-self edges, so a
     container-resolved caller is not counted. The loop counters are the
     method's maximum nesting, not this scan's.`,
			fn: mArrayScan,
		},
		{
			name:  "strict-types-missing",
			title: "File without declare(strict_types=1) (PHPStan/Psalm)",
			notes: `ANSWERS which files do not declare strict_types=1, so type coercion is
     enabled for the entire file.
ACT add declare(strict_types=1); at the top of the file.
MISLEADS legacy code that relies on type coercion may break with strict_types.`,
			fn: mStrictTypesMissing,
		},
		{
			name:  "untyped-params",
			title: "Functions with untyped parameters (PHPStan/Psalm)",
			notes: `ANSWERS the public surface where PHP will accept anything. A missing type
     on a public parameter is a missing contract at the boundary an
     attacker reaches first.
ACT type it. With strict_types off the declaration is documentation
     rather than enforcement, so both halves of this list matter.
MISLEADS private methods are excluded, on the grounds that the boundary
     they form is internal. A public method with one untyped parameter
     outranks one with four, by the same weighting as the query.`,
			fn: mUntypedParams,
		},
		{
			name:  "deep-nesting",
			title: "Functions with excessive nesting depth (PHP_CodeSniffer)",
			notes: `ANSWERS where a function has max_nesting > 4, making it hard to read.
ACT extract nested blocks; use early returns or guard clauses.
MISLEADS PHP's alternative syntax (if: ... endif;) does not change nesting.`,
			fn: mDeepNesting,
		},
		{
			name:  "too-many-params",
			title: "Functions with too many parameters (PHP_CodeSniffer)",
			notes: `ANSWERS the wide signatures. Every extra positional parameter is a
     decision the caller has to make blind, and a boolean in the list is
     a decision it usually makes wrong.
ACT take an options object, or split the function.
MISLEADS the count includes promoted constructor properties, which are
     usually cohesive, so a constructor with six promoted properties is
     listed and is often fine.`,
			fn: mTooManyParams,
		},
		{
			name:  "scattered-concerns",
			title: "A function called from many different modules (shotgun surgery)",
			notes: `ANSWERS the functions whose callers live in more than five modules. Each
     one is a place where a change breaks something the author of the
     function never had to look at.
ACT the usual causes are a shared utility that has become a dumping
     ground, or a domain object that every layer reaches for. Both are
     fixed by giving each caller its own seam.
MISLEADS the module count is distinct modules of the CALLERS, so twenty
     callers in one module read as one. Tests are not excluded, so a
     widely-mocked helper looks scattered even when production has one
     caller.`,
			fn: mScatteredConcerns,
		},
		{
			name:  "input-surface-by-module",
			title: "Where attacker-controlled input enters, by module: reads, Psalm-tainted reads, and the sinks they can reach",
			notes: `ANSWERS the per-module input surface, so the review can start with the
     module that reads the most and splices the most.
ACT the module with high super_reads and low sql_spliced is doing the
     input filtering; the one with both high is not.
MISLEADS pct_input_facing is the share of FUNCTIONS that read input, not
     the share of reads, so a module with one function reading a
     superglobal a hundred times looks quiet here.`,
			fn: mInputSurface,
		},
		{
			name:  "nullability-pressure",
			title: "Where null lives: nullable types, null-safe calls and null guards per module",
			notes: `ANSWERS where a module's code has to reason about absence, which is where
     the bugs are: a null guard in the wrong place, or one that a later
     refactor no longer needs.
ACT the combination to watch is high nullable_types with high
     null_checks: the module is paying for nullability in two places at
     once, and the checks are probably not the same checks.
MISLEADS null_checks counts ?? / isset / empty in the SAME function,
     not on the same value, so a module can look well-guarded and still
     be checking the wrong thing.`,
			fn: mNullability,
		},
		{
			name:  "error-swallow-map",
			title: "Where failures disappear: broad catches, empty catches and suppression vs throws, per module",
			notes: `ANSWERS the per-module failure-visibility ratio. Silencers are the broad
     catches, the empty catches and the @ operator; throws and catches
     are the failures that were allowed to be visible.
ACT above roughly 50% swallowed, the log is fiction and the incident
     review has nothing to work from.
MISLEADS the ratio is of COUNTS, not of severity: one module that throws
     a thousand times and another that throws once look identical. And a
     module that never throws trivially shows 0, which is a fact about
     the module, not a clean bill.`,
			fn: mErrorSwallow,
		},
		{
			name:  "entrypoint-blast-radius",
			title: "How much of the tree each entrypoint can reach in 3 hops",
			notes: `ANSWERS the blast radius of each request-facing entrypoint, which is what
     decides how carefully it has to be reviewed and what a regression
     there costs.
ACT an entrypoint reaching most of the tree is a place where a new
     shared helper will be reachable from it by accident.
MISLEADS three hops is a floor, not a measurement: anything reached
     through a container or a magic __call is not an edge, so a large
     application reads smaller here than it is.`,
			fn: mBlastRadius,
		},
		{
			name:  "facade-density",
			title: "Facade static calls per module: where the service locator hides in plain sight",
			notes: `ANSWERS where the dependency inversion argument quietly stopped. A module
     whose facade share of scoped calls is high depends on the container
     rather than on its constructor arguments.
ACT inject the collaborator. The call already resolves, which is why it
     never looked unresolved to a tool.
MISLEADS pct_facade is facade calls over ALL scoped calls, so a module
     that barely uses static calls at all can still show a high
     percentage.`,
			fn: mFacadeDensity,
		},
		{
			name:  "gadget-inventory",
			title: "Gadget magic methods per namespace: the ammunition a deserialization attack composes with",
			notes: `ANSWERS where the __destruct/__wakeup/__toString population lives,
     rolled up per namespace, with the hazards and call sites INSIDE
     those methods -- the surface unserialize-gadget-frontier compares
     against but does not localize. hazards_in_gadgets is the part
     that turns a magic method into a primitive (a __destruct that
     unlinks files, a __toString that queries).
ACT keep gadget methods free of side effects: no file ops, no exec,
     no SQL. Any namespace with gadgets AND nonzero hazards_in_gadgets
     belongs on the deserialization review with the frontier query.
MISLEADS gadget means 'PHP invokes it without a call site', NOT 'the
     attacker can reach unserialize' -- a repo may show ten gadgets
     and zero unserialize calls (see the frontier query for that
     half). Classes under vendor/ are excluded from the parse by
     default, and PHPGGC's catalogue lives exactly there.`,
			fn: mGadgetInventory,
		},
		{
			name:  "transaction-surface",
			title: "Mutations, transactions and queue dispatches per module: how much writes without a guard",
			notes: `ANSWERS how much of a module's database work is guarded by a transaction,
     and how much of it is followed by a dispatch. Unguarded writes plus
     a dispatch is the torn-state frontier; unguarded writes alone is
     the atomicity frontier.
ACT the rows with a low pct_tx_guarded and a high write_calls are
     where to start; a transaction at the call tree's root, not at each
     leaf.
MISLEADS transactions are counted by hazard name, so a transaction
     opened through a wrapper is invisible, and a transaction that does
     not cover every write in the function still counts.`,
			fn: mTransactionSurface,
		},
		{
			name:  "test-only-coupling",
			title: "Production functions whose ONLY callers are test files: the reverse dependency no coverage tool shows",
			notes: `ANSWERS production code that exists only for the tests. It is not dead -- the
     tests are the callers -- and it is a real maintenance cost: a test
     helper in src/ has no owner, no docs, and no reason to be there.
ACT either the test needs a real collaborator, or the helper belongs in
     the test suite where its callers are.
MISLEADS the test is "every caller of this function is a test", so one
     production caller anywhere hides the row -- which is the right
     answer, and the reason a codebase can have several of these and
     still be fine.`,
			fn: mTestOnlyCoupling,
		},
		{
			name:  "debug-residue",
			title: "Debug calls, exits and suppression per module: what debugging left behind",
			notes: `ANSWERS what a previous debugging session left in the tree, rolled up so
     the reviewer knows which module to grep first.
ACT grep the module for the four names and delete what is left; an exit
     in a library is a behaviour change, not a debug aid.
MISLEADS exit and die are statements, counted structurally rather than
     through a call, so a function that only exits shows a debug_calls of
     0 and is still worth reading here.`,
			fn: mDebugResidue,
		},
	}
}

func mGraphBlindspots(g *graph, mod string, limit int) *result {

	magic := make(map[int32]int32)
	for i := range g.classes {
		c := &g.classes[i]
		if c.hasCall || c.hasCallStatic {
			magic[g.sym.cols[cModuleID][c.sym]]++
		}
	}
	return g.rollup(modRollup{
		cols: []string{"namespace_", "fns", "calls", "external", "unresolved",
			"dynamic_sites", "var_method", "var_class", "magic_call", "pct_blind"},
		notTest: false,
		pred:    func(g *graph, s int) bool { return kindFnMethCl(g.sym.str(cKind, s)) },
		reduce: func(g *graph, m int32, a *modAcc) []cell {
			if a.calls == 0 {
				return nil
			}
			return []cell{cellS(g.moduleName(m)), cellI(int64(a.fns)),
				cellI(int64(a.calls)), cellI(int64(a.external)),
				cellI(int64(a.unresolved)), cellI(int64(a.dynCall)),
				cellI(int64(a.dynMethod)), cellI(int64(a.dynClass)),
				cellI(int64(magic[m])), pctCell(a.unresolved, a.calls)}
		},
		order: func(a, x []cell) bool { return a[4].i > x[4].i },
	})
}

func mStrictTypes(g *graph, mod string, limit int) *result {
	b := newR("namespace_", "files", "strict_files", "fns", "typed_slots",
		"untyped_params", "nullable", "unions", "intersections", "loose_cmp",
		"pct_fns_under_strict")

	files := make(map[int32]map[int32]bool)
	fns := make(map[int32]*modAcc)
	order := make([]int32, 0, len(g.mods))
	for s := 0; s < g.sym.n; s++ {
		if g.isTestFileOfSym(s) || !kindFnMeth(g.sym.str(cKind, s)) {
			continue
		}
		m := g.sym.cols[cModuleID][s]
		if !sqlLike(g.moduleName(m), mod) {
			continue
		}
		a := fns[m]
		if a == nil {
			a = &modAcc{}
			fns[m] = a
			order = append(order, m)
		}
		a.fns++
		a.add(g, s)

		set := files[m]
		if set == nil {
			set = map[int32]bool{}
			files[m] = set
		}
		set[g.sym.cols[cFileID][s]] = true
	}
	insertionSortAny(order, func(x, y int32) bool { return x < y })
	for _, m := range order {
		a := fns[m]
		if a.fns == 0 {
			continue
		}
		b.row(cellS(g.moduleName(m)), cellI(int64(len(files[m]))), cellI(0),
			cellI(int64(a.fns)), cellI(int64(a.typed)), cellI(int64(a.untyped)),
			cellI(int64(a.nullable)), cellI(int64(a.unions)), cellI(int64(a.inter)),
			cellI(int64(a.looseCmp)), pctCell(0, a.fns))
	}
	insertionSort(b.r.rows, func(x, y []cell) bool {
		if x[5].i != y[5].i {
			return x[5].i > y[5].i
		}
		return x[10].i < y[10].i
	})
	return b.done()
}

func mPropertyHooks(g *graph, mod string, limit int) *result {
	b := newR("class_name", "property", "hook", "short_form",
		"virtual_no_backing_field", "sloc", "calls_inside", "cyclo", "sql_inside",
		"loops", "risk", "props_on_class", "at")
	props := make(map[int32]int32)
	for i := range g.classes {
		props[g.classes[i].sym] = g.classes[i].nProps
	}
	for i := range g.hooks {
		h := &g.hooks[i]
		if h.symNull {
			continue
		}
		s := int(h.sym)
		if g.isTestFileOfSym(s) || !sqlLike(g.modOfSym(s), mod) {
			continue
		}
		b.row(cellS(g.sa.str(h.className)), cellS(g.sa.str(h.property)), cellS(g.sa.str(h.hook)),
			cellI(bi(h.isShort)), cellI(bi(h.isVirtual)), cellI(int64(h.bodySLOC)),
			cellI(int64(h.nCalls)), cellI(int64(g.col(s, cCyclomatic))),
			cellI(int64(g.col(s, cNSQLCalls))), cellI(int64(g.col(s, cMaxLoopDepth))),
			cellI(int64(g.col(s, cRiskScore))), cellI(int64(props[h.classID])),
			cellS(g.atLoc(h.fileID, h.line)))
	}
	insertionSort(b.r.rows, func(a, c []cell) bool {
		if a[4].i != c[4].i {
			return a[4].i > c[4].i
		}
		if a[6].i != c[6].i {
			return a[6].i > c[6].i
		}
		return a[5].i > c[5].i
	})
	return b.done()
}

func mGodClasses(g *graph, mod string, limit int) *result {
	b := newR("class_", "kind", "methods", "public_", "props", "traits_", "magic",
		"sloc", "lines_", "worst_method_cog", "elifs", "bulk", "at")
	worstCog := make(map[int32]int32)
	elifs := make(map[int32]int32)
	for s := 0; s < g.sym.n; s++ {
		p := g.sym.cols[cParentID][s]
		if p < 0 {
			continue
		}
		if c := g.col(s, cCognitive); c > worstCog[p] {
			worstCog[p] = c
		}
		elifs[p] += g.col(s, cNElif)
	}
	for i := range g.classes {
		c := &g.classes[i]
		if g.isTestFileOfSym(int(c.sym)) || g.isGenFileOfSym(int(c.sym)) ||
			!sqlLike(g.modOfSym(int(c.sym)), mod) {
			continue
		}
		s := int(c.sym)
		bulk := c.nMethods*3 + c.nProps*2 + c.nTraits*4 + g.col(s, cSloc)/40
		b.row(cellS(g.sa.str(c.name)), cellS(g.sa.str(c.kind)), cellI(int64(c.nMethods)),
			cellI(int64(c.nPub)), cellI(int64(c.nProps)), cellI(int64(c.nTraits)),
			cellI(int64(c.nMagic)), cellI(int64(g.col(s, cSloc))),
			cellI(int64(g.col(s, cNLines))), cellI(int64(worstCog[c.sym])),
			cellI(int64(elifs[c.sym])), cellI(int64(bulk)),
			cellS(g.atLoc(c.fileID, c.line)))
	}
	insertionSort(b.r.rows, func(a, x []cell) bool {
		if a[11].i != x[11].i {
			return a[11].i > x[11].i
		}
		if a[9].i != x[9].i {
			return a[9].i > x[9].i
		}
		return a[0].s < x[0].s
	})
	return b.done()
}

func mRiskRanked(g *graph, mod string, limit int) *result {
	b := newR("name", "class_", "risk", "cyclo", "cog", "nest",
		"sql_interp", "sql_concat", "prepared", "evals", "shell", "var_include",
		"super_reads", "raw_echo", "loose_cmp", "strict_", "fan_in", "at")
	syms := make([]int32, 0, g.sym.n)
	for s := 0; s < g.sym.n; s++ {
		if g.isGenFileOfSym(s) || !kindFnMethCl(g.sym.str(cKind, s)) ||
			!sqlLike(g.modOfSym(s), mod) {
			continue
		}
		syms = append(syms, int32(s))
	}
	kf := make([]byte, g.sym.n)
	for s := 0; s < g.sym.n; s++ {
		switch g.sym.str(cKind, s) {
		case "closure":
			kf[s] = 0
		case "function":
			kf[s] = 1
		default:
			kf[s] = 2
		}
	}
	insertionSortAny(syms, func(x, y int32) bool {
		fx, fy := g.sym.cols[cFileID][x], g.sym.cols[cFileID][y]
		if fx != fy {
			return fx < fy
		}
		if kf[x] != kf[y] {
			return kf[x] < kf[y]
		}
		return x < y
	})
	for _, si := range syms {
		s := int(si)
		b.row(cellS(g.sym.str(cName, s)), cellS(g.sym.str(cClassName, s)),
			cellI(int64(g.col(s, cRiskScore))), cellI(int64(g.col(s, cCyclomatic))),
			cellI(int64(g.col(s, cCognitive))), cellI(int64(g.col(s, cMaxNesting))),
			cellI(int64(g.col(s, cNSQLInterp))), cellI(int64(g.col(s, cNSQLConcat))),
			cellI(int64(g.col(s, cNSQLPrepared))), cellI(int64(g.col(s, cNEval))),
			cellI(int64(g.col(s, cNShell))), cellI(int64(g.col(s, cNDynamicInclude))),
			cellI(int64(g.col(s, cNSuperglobalReads))),
			cellI(int64(g.col(s, cNRawEcho))), cellI(int64(g.col(s, cNLooseCompare))),
			cellI(int64(g.col(s, cHasStrictTypes))), cellI(int64(g.col(s, cFanIn))),
			cellS(g.at(s)))
	}
	insertionSort(b.r.rows, func(a, c []cell) bool { return a[2].i > c[2].i })
	return b.done()
}

func mParseCoverage(g *graph, mod string, limit int) *result {
	nsPerFile := make(map[int32]int32)
	strictPerFile := make(map[int32]int32)
	strictSeen := make(map[int32]bool)
	for i := range g.namespaces {
		nsPerFile[g.namespaces[i].fileID]++
		strictSeen[g.namespaces[i].fileID] = true
		if g.namespaces[i].strict {
			strictPerFile[g.namespaces[i].fileID] = 1
		}
	}
	b := newR("path", "lines", "errors", "missing", "parsed", "generated", "test",
		"symbols_", "namespaces_", "strict_types")
	for i := range g.fils {
		f := &g.fils[i]
		if !(f.parseErrs > 0 || f.missing > 0 || f.parsed == 0 || f.nSymbols == 0) {
			continue
		}
		if !sqlLike(g.moduleName(f.moduleID), mod) {
			continue
		}
		b.row(cellS(g.sa.str(f.path)), cellI(int64(f.lines)), cellI(int64(f.parseErrs)),
			cellI(int64(f.missing)), cellI(int64(f.parsed)), cellI(int64(f.isGen)),
			cellI(int64(f.isTest)), cellI(int64(f.nSymbols)),
			cellI(int64(nsPerFile[f.id])),

			nullableI(strictPerFile[f.id], !strictSeen[f.id]))
	}
	insertionSort(b.r.rows, func(a, c []cell) bool {
		if a[2].i != c[2].i {
			return a[2].i > c[2].i
		}
		if a[3].i != c[3].i {
			return a[3].i > c[3].i
		}
		return a[1].i > c[1].i
	})
	return b.done()
}

func mHotMultipliers(g *graph, mod string, limit int) *result {
	b := newR("name", "fan_in", "sites", "fan_out", "cyclo", "sloc", "kind",
		"module_", "at")
	syms := make([]int32, 0, g.sym.n)
	for s := 0; s < g.sym.n; s++ {
		if g.col(s, cFanIn) <= 0 || !sqlLike(g.modOfSym(s), mod) {
			continue
		}
		syms = append(syms, int32(s))
	}
	insertionSortAny(syms, func(x, y int32) bool {
		fx := g.file(g.sym.cols[cFileID][x])
		fy := g.file(g.sym.cols[cFileID][y])
		px := g.sa.str(fx.path)
		py := g.sa.str(fy.path)
		if px != py {
			return px < py
		}
		lx := g.sym.cols[cLineStart][x]
		ly := g.sym.cols[cLineStart][y]
		if lx != ly {
			return lx < ly
		}
		return x < y
	})
	for _, si := range syms {
		s := int(si)
		b.row(cellS(g.sym.str(cName, s)), cellI(int64(g.col(s, cFanIn))),
			cellI(int64(g.col(s, cNCallsites))), cellI(int64(g.col(s, cFanOut))),
			cellI(int64(g.col(s, cCyclomatic))), cellI(int64(g.col(s, cSloc))),
			cellS(g.sym.str(cKind, s)), cellS(g.modOfSym(s)), cellS(g.at(s)))
	}
	insertionSort(b.r.rows, func(a, c []cell) bool {
		if a[1].i != c[1].i {
			return a[1].i > c[1].i
		}
		return a[4].i > c[4].i
	})
	return b.done()
}

func mArrayScan(g *graph, mod string, limit int) *result {
	callers := callerSet(g)
	b := newR("name", "inarray_in_loop", "array_merge_in_loop", "count_in_loop",
		"preg_in_loop", "keycheck_in_loop", "loop_depth", "fan_in",
		"distinct_callers", "at")
	for s := 0; s < g.sym.n; s++ {
		if g.col(s, cNInarrayInLoop) <= 0 && g.col(s, cNArrayMergeInLoop) <= 0 &&
			g.col(s, cNCountInLoop) <= 0 {
			continue
		}
		if g.isTestFileOfSym(s) || !sqlLike(g.modOfSym(s), mod) {
			continue
		}
		b.row(cellS(g.sym.str(cName, s)), cellI(int64(g.col(s, cNInarrayInLoop))),
			cellI(int64(g.col(s, cNArrayMergeInLoop))),
			cellI(int64(g.col(s, cNCountInLoop))),
			cellI(int64(g.col(s, cNPregInLoop))),
			cellI(int64(g.col(s, cNKeycheckInLoop))),
			cellI(int64(g.col(s, cMaxLoopDepth))), cellI(int64(g.col(s, cFanIn))),
			cellI(int64(len(callers[int32(s)]))), cellS(g.at(s)))
	}
	insertionSort(b.r.rows, func(a, c []cell) bool {
		if a[2].i != c[2].i {
			return a[2].i > c[2].i
		}
		if a[1].i != c[1].i {
			return a[1].i > c[1].i
		}
		return a[8].i > c[8].i
	})
	return b.done()
}

func mStrictTypesMissing(g *graph, mod string, limit int) *result {
	return g.scan([]string{"name", "has_strict_types", "loose_compares",
		"untyped_params", "type_declarations", "fan_in", "controller", "at"},
		symFilter{notTest: true, mod: mod, pred: func(g *graph, s int) bool {
			return g.col(s, cHasStrictTypes) == 0 && g.col(s, cIsController) == 1
		}},
		func(g *graph, s int) []cell {
			return []cell{cellS(g.sym.str(cName, s)),
				cellI(int64(g.col(s, cHasStrictTypes))),
				cellI(int64(g.col(s, cNLooseCompare))),
				cellI(int64(g.col(s, cNUntypedParams))),
				cellI(int64(g.col(s, cNTypeDeclarations))),
				cellI(int64(g.col(s, cFanIn))), cellI(int64(g.col(s, cIsController))),
				cellS(g.at(s))}
		},
		func(a, c []cell) bool {
			if a[5].i != c[5].i {
				return a[5].i > c[5].i
			}
			return a[2].i > c[2].i
		})
}

func mUntypedParams(g *graph, mod string, limit int) *result {
	return g.scan([]string{"name", "untyped_params", "type_declarations",
		"nullable_types", "union_types", "n_params", "fan_in", "is_public", "at"},
		symFilter{notTest: true, mod: mod, pred: func(g *graph, s int) bool {
			return g.col(s, cNUntypedParams) > 0 && g.col(s, cIsPublic) == 1
		}},
		func(g *graph, s int) []cell {
			return []cell{cellS(g.sym.str(cName, s)),
				cellI(int64(g.col(s, cNUntypedParams))),
				cellI(int64(g.col(s, cNTypeDeclarations))),
				cellI(int64(g.col(s, cNNullableTypes))),
				cellI(int64(g.col(s, cNUnionTypes))), cellI(int64(g.col(s, cNParams))),
				cellI(int64(g.col(s, cFanIn))), cellI(int64(g.col(s, cIsPublic))),
				cellS(g.at(s))}
		},
		func(a, c []cell) bool {
			if a[6].i != c[6].i {
				return a[6].i > c[6].i
			}
			if a[1].i != c[1].i {
				return a[1].i > c[1].i
			}
			return a[0].s < c[0].s
		})
}

func mDeepNesting(g *graph, mod string, limit int) *result {
	return g.scan([]string{"name", "nesting", "cyclo", "cognitive", "loops", "sloc",
		"fan_in", "at"},
		symFilter{notTest: true, mod: mod, pred: func(g *graph, s int) bool {
			return g.col(s, cMaxNesting) > 4 && kindFnMeth(g.sym.str(cKind, s))
		}},
		func(g *graph, s int) []cell {
			return []cell{cellS(g.sym.str(cName, s)),
				cellI(int64(g.col(s, cMaxNesting))),
				cellI(int64(g.col(s, cCyclomatic))),
				cellI(int64(g.col(s, cCognitive))), cellI(int64(g.col(s, cNLoops))),
				cellI(int64(g.col(s, cSloc))), cellI(int64(g.col(s, cFanIn))),
				cellS(g.at(s))}
		},
		func(a, c []cell) bool {
			if a[1].i != c[1].i {
				return a[1].i > c[1].i
			}
			return a[2].i > c[2].i
		})
}

func mTooManyParams(g *graph, mod string, limit int) *result {
	return g.scan([]string{"name", "n_params", "n_optional_params", "sloc", "cyclo",
		"fan_in", "at"},
		symFilter{notTest: true, mod: mod, pred: func(g *graph, s int) bool {
			return g.col(s, cNParams) > 5 && kindFnMeth(g.sym.str(cKind, s))
		}},
		func(g *graph, s int) []cell {
			return []cell{cellS(g.sym.str(cName, s)), cellI(int64(g.col(s, cNParams))),
				cellI(int64(g.col(s, cNOptionalParams))), cellI(int64(g.col(s, cSloc))),
				cellI(int64(g.col(s, cCyclomatic))), cellI(int64(g.col(s, cFanIn))),
				cellS(g.at(s))}
		},
		func(a, c []cell) bool {
			if a[1].i != c[1].i {
				return a[1].i > c[1].i
			}
			return a[5].i > c[5].i
		})
}

func mScatteredConcerns(g *graph, mod string, limit int) *result {
	b := newR("name", "n_caller_modules", "fan_in", "cyclo", "sloc", "modules", "at")
	callerMods := make(map[int32]map[int32]bool)
	for i := range g.edges {
		e := &g.edges[i]
		if e.isSelf {
			continue
		}
		m := g.sym.cols[cModuleID][e.caller]
		set := callerMods[e.callee]
		if set == nil {
			set = map[int32]bool{}
			callerMods[e.callee] = set
		}
		set[m] = true
	}

	for s := 0; s < g.sym.n; s++ {
		set := callerMods[int32(s)]
		if len(set) <= 5 || !kindFnMeth(g.sym.str(cKind, s)) || g.isTestFileOfSym(s) {
			continue
		}

		names := make([]string, 0, len(set))
		ok := false
		for m := range set {
			if sqlLike(g.moduleName(m), mod) {
				ok = true
			}
			names = append(names, g.moduleName(m))
		}
		if !ok {
			continue
		}
		insertionSortAny(names, func(x, y string) bool { return x < y })
		b.row(cellS(g.sym.str(cName, s)), cellI(int64(len(set))),
			cellI(int64(g.col(s, cFanIn))), cellI(int64(g.col(s, cCyclomatic))),
			cellI(int64(g.col(s, cSloc))), cellS(strings.Join(names, ",")),
			cellS(g.at(s)))
	}
	insertionSort(b.r.rows, func(a, c []cell) bool {
		if a[1].i != c[1].i {
			return a[1].i > c[1].i
		}
		return a[2].i > c[2].i
	})
	return b.done()
}

func mInputSurface(g *graph, mod string, limit int) *result {
	type st struct {
		acc     modAcc
		fns     int32
		inputFn int32
	}
	m := make(map[int32]*st)
	var order []int32
	for s := 0; s < g.sym.n; s++ {
		if g.isTestFileOfSym(s) || !kindFnMethCl(g.sym.str(cKind, s)) {
			continue
		}
		mid := g.sym.cols[cModuleID][s]
		if !sqlLike(g.moduleName(mid), mod) {
			continue
		}
		x := m[mid]
		if x == nil {
			x = &st{}
			m[mid] = x
			order = append(order, mid)
		}
		x.fns++
		if g.col(s, cNSuperglobalReads) > 0 {
			x.inputFn++
		}
		x.acc.add(g, s)
	}
	b := newR("namespace_", "fns", "super_reads", "psalm_tainted", "sql_spliced",
		"shell", "raw_echo", "input_fns", "pct_input_facing")
	insertionSortAny(order, func(x, y int32) bool { return x < y })
	for _, mid := range order {
		x := m[mid]
		if x.fns == 0 {
			continue
		}
		b.row(cellS(g.moduleName(mid)), cellI(int64(x.fns)),
			cellI(int64(x.acc.superReads)), cellI(int64(x.acc.psalmTainted)),
			cellI(int64(x.acc.sqlInterp+x.acc.sqlConcat)),
			cellI(int64(x.acc.shell)), cellI(int64(x.acc.rawEcho)),
			cellI(int64(x.inputFn)), pctCell(x.inputFn, x.fns))
	}
	insertionSort(b.r.rows, func(a, c []cell) bool {
		if a[3].i != c[3].i {
			return a[3].i > c[3].i
		}
		if a[4].i != c[4].i {
			return a[4].i > c[4].i
		}
		return a[2].i > c[2].i
	})
	return b.done()
}

func mNullability(g *graph, mod string, limit int) *result {
	type st struct {
		acc           modAcc
		fns, nullFns  int32
		returningNull int32
	}
	m := make(map[int32]*st)
	var order []int32
	for s := 0; s < g.sym.n; s++ {
		if g.isTestFileOfSym(s) || !kindFnMeth(g.sym.str(cKind, s)) {
			continue
		}
		mid := g.sym.cols[cModuleID][s]
		if !sqlLike(g.moduleName(mid), mod) {
			continue
		}
		x := m[mid]
		if x == nil {
			x = &st{}
			m[mid] = x
			order = append(order, mid)
		}
		x.fns++
		if g.col(s, cNNullableTypes) > 0 {
			x.nullFns++
		}
		rt := g.sym.str(cReturnType, s)
		if strings.HasPrefix(rt, "?") || strings.Contains(rt, "null") {
			x.returningNull++
		}
		x.acc.add(g, s)
	}
	b := newR("namespace_", "fns", "nullable_types", "nullsafe_calls", "null_checks",
		"fns_with_nullable", "fns_returning_nullable", "pct_nullable_fns")
	insertionSortAny(order, func(x, y int32) bool { return x < y })
	for _, mid := range order {
		x := m[mid]
		if x.fns == 0 {
			continue
		}
		b.row(cellS(g.moduleName(mid)), cellI(int64(x.fns)),
			cellI(int64(x.acc.nullable)), cellI(int64(x.acc.nullSafe)),
			cellI(int64(x.acc.nullChecks)), cellI(int64(x.nullFns)),
			cellI(int64(x.returningNull)), pctCell(x.nullFns, x.fns))
	}
	insertionSort(b.r.rows, func(a, c []cell) bool {
		if a[2].i != c[2].i {
			return a[2].i > c[2].i
		}
		return a[3].i > c[3].i
	})
	return b.done()
}

func mErrorSwallow(g *graph, mod string, limit int) *result {
	return g.rollup(modRollup{
		cols: []string{"namespace_", "fns", "throws", "trys", "catches",
			"broad_catches", "empty_catches", "suppressed", "silencers", "pct_swallowed"},
		notTest: true,
		pred:    func(g *graph, s int) bool { return kindFnMethCl(g.sym.str(cKind, s)) },
		reduce: func(g *graph, m int32, a *modAcc) []cell {
			if a.fns == 0 {
				return nil
			}
			sil := a.broadCatches + a.emptyCatches + a.suppressed
			den := a.throws + a.catches + a.suppressed
			return []cell{cellS(g.moduleName(m)), cellI(int64(a.fns)),
				cellI(int64(a.throws)), cellI(int64(a.trys)), cellI(int64(a.catches)),
				cellI(int64(a.broadCatches)), cellI(int64(a.emptyCatches)),
				cellI(int64(a.suppressed)), cellI(int64(sil)), pctCell(sil, den)}
		},
	}).order(func(a, c []cell) bool {
		an, cn := a[9].kind == 0, c[9].kind == 0
		if an != cn {
			return cn
		}
		if a[9].i != c[9].i {
			return a[9].i > c[9].i
		}
		return a[8].i > c[8].i
	})
}

func (r *result) order(less func(a, c []cell) bool) *result {
	insertionSort(r.rows, less)
	return r
}

func mBlastRadius(g *graph, mod string, limit int) *result {
	b := newR("name", "module_", "reached", "max_depth", "fan_out", "cyclo",
		"input_reads", "sql_calls", "at")

	type acc struct {
		reached  map[int32]bool
		maxDepth int32
	}
	byRoot := make(map[int32]*acc)
	for i := 0; i < g.sym.n; i++ {
		if g.col(i, cIsEntrypoint) != 1 {
			continue
		}
		byRoot[int32(i)] = &acc{reached: map[int32]bool{}}
	}
	for _, h := range allReachHits(g.seeds(cIsEntrypoint), 3, g.adj) {
		a := byRoot[h.src]
		if a == nil {
			continue
		}
		a.reached[h.sym] = true
	}

	roots := make([]int32, 0, len(byRoot))
	for k := range byRoot {
		roots = append(roots, k)
	}
	insertionSortAny(roots, func(x, y int32) bool { return x < y })
	var walk walkScratch
	for _, r := range roots {
		byRoot[r].maxDepth = walk.longestWalk(r, 3, g.adj)
	}
	for _, r := range roots {
		s := int(r)
		if g.isTestFileOfSym(s) {
			continue
		}
		b.row(cellS(g.sym.str(cName, s)), cellS(g.modOfSym(s)),
			cellI(int64(len(byRoot[r].reached))),
			cellI(int64(byRoot[r].maxDepth)), cellI(int64(g.col(s, cFanOut))),
			cellI(int64(g.col(s, cCyclomatic))),
			cellI(int64(g.col(s, cNSuperglobalReads))),
			cellI(int64(g.col(s, cNSQLCalls))), cellS(g.at(s)))
	}
	insertionSort(b.r.rows, func(a, c []cell) bool {
		if a[2].i != c[2].i {
			return a[2].i > c[2].i
		}
		return a[6].i > c[6].i
	})
	return b.done()
}

func mFacadeDensity(g *graph, mod string, limit int) *result {
	type st struct {
		acc     modAcc
		fns     int32
		withFac int32
	}
	m := make(map[int32]*st)
	var order []int32
	for s := 0; s < g.sym.n; s++ {
		if g.isTestFileOfSym(s) || !kindFnMeth(g.sym.str(cKind, s)) {
			continue
		}
		mid := g.sym.cols[cModuleID][s]
		if !sqlLike(g.moduleName(mid), mod) {
			continue
		}
		x := m[mid]
		if x == nil {
			x = &st{}
			m[mid] = x
			order = append(order, mid)
		}
		x.fns++
		if g.col(s, cNFacadeCall) > 0 {
			x.withFac++
		}
		x.acc.add(g, s)
	}
	b := newR("namespace_", "fns", "facade_calls", "static_calls",
		"fns_with_facades", "pct_facade")
	insertionSortAny(order, func(x, y int32) bool { return x < y })
	for _, mid := range order {
		x := m[mid]
		if x.fns == 0 {
			continue
		}
		b.row(cellS(g.moduleName(mid)), cellI(int64(x.fns)),
			cellI(int64(x.acc.facadeCalls)), cellI(int64(x.acc.staticCalls)),
			cellI(int64(x.withFac)), pctCell(x.acc.facadeCalls, x.acc.staticCalls))
	}
	insertionSort(b.r.rows, func(a, c []cell) bool {
		if a[2].i != c[2].i {
			return a[2].i > c[2].i
		}
		an, cn := a[5].kind == 0, c[5].kind == 0
		if an != cn {
			return cn
		}
		return a[5].i > c[5].i
	})
	return b.done()
}

func mGadgetInventory(g *graph, mod string, limit int) *result {
	type st struct {
		classes, methods                           map[int32]bool
		destruct, wakeup, tostring, hazards, calls int32
	}
	m := make(map[string]*st)
	var order []string
	owner := make(map[int32]*classRow)
	for i := range g.classes {
		owner[g.classes[i].sym] = &g.classes[i]
	}
	for i := range g.magic {
		mm := &g.magic[i]
		if !mm.isGadget || mm.classIDNull {
			continue
		}
		c := owner[mm.classID]
		if c == nil {
			continue
		}
		if g.isTestFileOfSym(int(c.sym)) || !sqlLike(g.modOfSym(int(c.sym)), mod) {
			continue
		}
		key := g.sa.str(c.ns)
		if key == "" {
			key = "(global)"
		}
		x := m[key]
		if x == nil {
			x = &st{classes: map[int32]bool{}, methods: map[int32]bool{}}
			m[key] = x
			order = append(order, key)
		}
		x.classes[c.sym] = true
		x.methods[mm.sym] = true
		x.hazards += mm.nHazards
		x.calls += mm.nCalls

		if c.hasDestruct {
			x.destruct++
		}
		if c.hasWakeup {
			x.wakeup++
		}
		if c.hasToStr {
			x.tostring++
		}
	}
	b := newR("namespace_", "classes_with_magic", "gadget_methods", "destructs",
		"wakeups", "tostrings", "hazards_in_gadgets", "calls_in_gadgets")
	insertionSortAny(order, func(x, y string) bool { return x < y })
	for _, k := range order {
		x := m[k]
		b.row(cellS(k), cellI(int64(len(x.classes))), cellI(int64(len(x.methods))),
			cellI(int64(x.destruct)), cellI(int64(x.wakeup)), cellI(int64(x.tostring)),
			cellI(int64(x.hazards)), cellI(int64(x.calls)))
	}
	insertionSort(b.r.rows, func(a, c []cell) bool {
		if a[6].i != c[6].i {
			return a[6].i > c[6].i
		}
		return a[2].i > c[2].i
	})
	return b.done()
}

func mTransactionSurface(g *graph, mod string, limit int) *result {
	type st struct {
		acc          modAcc
		fns, writing int32
		fnsWithTx    int32
	}
	m := make(map[int32]*st)
	var order []int32
	for s := 0; s < g.sym.n; s++ {
		if g.isTestFileOfSym(s) || !kindFnMeth(g.sym.str(cKind, s)) {
			continue
		}
		mid := g.sym.cols[cModuleID][s]
		if !sqlLike(g.moduleName(mid), mod) {
			continue
		}
		x := m[mid]
		if x == nil {
			x = &st{}
			m[mid] = x
			order = append(order, mid)
		}
		x.fns++
		if g.col(s, cNWrite) > 0 {
			x.writing++
			if g.col(s, cNTransaction) > 0 {
				x.fnsWithTx++
			}
		}
		x.acc.add(g, s)
	}
	b := newR("namespace_", "fns", "write_calls", "tx_calls", "queue_dispatches",
		"fns_writing", "fns_with_tx", "pct_tx_guarded")
	insertionSortAny(order, func(x, y int32) bool { return x < y })
	for _, mid := range order {
		x := m[mid]
		if x.acc.writes == 0 {
			continue
		}
		b.row(cellS(g.moduleName(mid)), cellI(int64(x.fns)),
			cellI(int64(x.acc.writes)), cellI(int64(x.acc.txCalls)),
			cellI(int64(x.acc.queueCalls)), cellI(int64(x.writing)),
			cellI(int64(x.fnsWithTx)), pctCell(x.fnsWithTx, x.writing))
	}
	insertionSort(b.r.rows, func(a, c []cell) bool {
		if a[2].i != c[2].i {
			return a[2].i > c[2].i
		}
		return a[7].i < c[7].i
	})
	return b.done()
}

func mTestOnlyCoupling(g *graph, mod string, limit int) *result {
	b := newR("name", "kind", "class_", "all_callers", "test_callers", "fan_in",
		"sites", "at")
	all := make(map[int32]map[int32]bool)
	for i := range g.edges {
		e := &g.edges[i]
		if e.isSelf {
			continue
		}
		set := all[e.callee]
		if set == nil {
			set = map[int32]bool{}
			all[e.callee] = set
		}
		set[e.caller] = true
	}
	syms := make([]int32, 0, len(all))
	for k := range all {
		syms = append(syms, k)
	}
	insertionSortAny(syms, func(x, y int32) bool { return x < y })
	type tocRow struct {
		sym   int32
		cells []cell
	}
	var rows []tocRow
	for _, sym := range syms {
		s := int(sym)
		if g.col(s, cIsTest) != 0 || g.isTestFileOfSym(s) ||
			!kindFnMethCl(g.sym.str(cKind, s)) || !sqlLike(g.modOfSym(s), mod) {
			continue
		}
		set := all[sym]
		var tests int32
		onlyTests := true
		for c := range set {
			if g.isTestFileOfSym(int(c)) || g.col(int(c), cIsTest) != 0 {
				tests++
			} else {
				onlyTests = false
			}
		}
		if !onlyTests {
			continue
		}
		rows = append(rows, tocRow{sym, []cell{
			cellS(g.sym.str(cName, s)), cellS(g.sym.str(cKind, s)),
			cellS(g.sym.str(cClassName, s)), cellI(int64(len(set))),
			cellI(int64(tests)), cellI(int64(g.col(s, cFanIn))),
			cellI(int64(g.col(s, cNCallsites))), cellS(g.at(s))}})
	}
	insertionSortAny(rows, func(x, y tocRow) bool {
		xc, yc := x.cells[3].i, y.cells[3].i
		if xc != yc {
			return xc > yc
		}
		return x.sym > y.sym
	})
	for _, r := range rows {
		b.row(r.cells...)
	}
	return b.done()
}

func mDebugResidue(g *graph, mod string, limit int) *result {
	type st struct {
		acc     modAcc
		fns     int32
		withDbg int32
	}
	m := make(map[int32]*st)
	var order []int32
	for s := 0; s < g.sym.n; s++ {
		if g.isTestFileOfSym(s) || !kindFnMethCl(g.sym.str(cKind, s)) {
			continue
		}
		mid := g.sym.cols[cModuleID][s]
		if !sqlLike(g.moduleName(mid), mod) {
			continue
		}
		x := m[mid]
		if x == nil {
			x = &st{}
			m[mid] = x
			order = append(order, mid)
		}
		x.fns++
		if g.col(s, cNDebugCall) > 0 {
			x.withDbg++
		}
		x.acc.add(g, s)
	}
	b := newR("namespace_", "fns", "debug_calls", "fns_with_debug", "suppressed",
		"raw_echo", "empty_catches")
	insertionSortAny(order, func(x, y int32) bool { return x < y })
	for _, mid := range order {
		x := m[mid]
		if x.fns == 0 {
			continue
		}
		b.row(cellS(g.moduleName(mid)), cellI(int64(x.fns)),
			cellI(int64(x.acc.debugCalls)), cellI(int64(x.withDbg)),
			cellI(int64(x.acc.suppressed)), cellI(int64(x.acc.rawEcho)),
			cellI(int64(x.acc.emptyCatches)))
	}
	insertionSort(b.r.rows, func(a, c []cell) bool {
		if a[2].i != c[2].i {
			return a[2].i > c[2].i
		}
		if a[3].i != c[3].i {
			return a[3].i > c[3].i
		}
		return a[4].i > c[4].i
	})
	return b.done()
}

var bumpCols, bumpSlot = buildBumpSlots()

func buildBumpSlots() ([]int, map[int]int) {
	seen := map[int]bool{}
	add := func(c int) {
		if c >= 0 && !seen[c] {
			seen[c] = true
		}
	}
	for _, v := range counters {
		add(v)
	}
	for _, v := range flagNodes {
		add(v)
	}
	for _, lc := range loopCallCounters {
		add(lc.col)
	}

	for _, c := range []int{
		cNLoops, cNElif, cNRegexLit,
		cNSQLLiteral, cNCalls, cCallInLoop,
		cNFacadeCall, cNEscapedOutput, cNEval, cNNullCheck,
		cNLooseCompare, cNStrictCompare,
		cNRawEcho,
		cNCatchBroad, cNCatchEmpty, cNDynamicInclude, cNDynamicPropWrite,
		cNStaticPropWrite, cNSessionWrite, cNSuperglobalReads, cQueryInLoop,
		cNExtractCall, cNWeakHash, cNWeakRandom, cNRemoteFetch, cNHeaderCall,
		cNSessionCall, cNMoveUploaded, cNSerializeCall, cNXxeParser,
		cNDynamicOpen, cNLogCall, cNAuthCall, cNRequestInput, cNDebugCall,
		cNInarrayLoose, cNCookieLean, cNPregDynamic, cNFileWriteDyn,
		cNCleartextFetch, cNInarrayInLoop, cNArrayMergeInLoop, cNCountInLoop,
		cNPregInLoop, cNKeycheckInLoop, cIOInLoop,
		cRegexInLoop, cNExternPrefix(),
	} {
		add(c)
	}
	cols := make([]int, 0, len(seen))
	for c := range seen {
		cols = append(cols, c)
	}
	sortInts(cols)
	slot := make(map[int]int, len(cols))
	for i, c := range cols {
		slot[c] = i
	}
	return cols, slot
}

func cNExternPrefix() int { return -1 }

func sortInts(a []int) {
	for i := 1; i < len(a); i++ {
		for j := i; j > 0 && a[j] < a[j-1]; j-- {
			a[j], a[j-1] = a[j-1], a[j]
		}
	}
}

type callRec struct {
	name    string
	line    int32
	dynamic bool
	inLoop  bool
}

type litRec struct {
	kind, value string
	line        int32
	magic       bool
}

type stats struct {
	cnt          []int32
	touched      []int32
	cyclomatic   int32
	cognitive    int32
	maxNesting   int32
	maxLoopDepth int32
	nTokens      int32
	nOperators   int32
	nOperands    int32

	operators map[int]bool
	operands  map[string]bool
	calls     []callRec
	literals  []litRec
	secrets   []litRec
}

func newStats(nBump int) *stats {
	return &stats{
		cnt:       make([]int32, nBump),
		touched:   make([]int32, 0, 64),
		operators: make(map[int]bool, 16),
		operands:  make(map[string]bool, 32),
		calls:     make([]callRec, 0, 8),
	}
}

func (s *stats) reset() {
	for _, sl := range s.touched {
		s.cnt[sl] = 0
	}
	s.touched = s.touched[:0]
	s.cyclomatic, s.cognitive, s.maxNesting, s.maxLoopDepth = 1, 0, 0, 0
	s.nTokens, s.nOperators, s.nOperands = 0, 0, 0
	clear(s.operators)
	clear(s.operands)
	s.calls = s.calls[:0]
	s.literals = s.literals[:0]
	s.secrets = s.secrets[:0]
}

func (s *stats) bump(c int) { s.add(c, 1) }

func (s *stats) set(c int, n int32) {
	sl, ok := bumpSlot[c]
	if !ok {
		return
	}
	if s.cnt[sl] == 0 {
		s.touched = append(s.touched, int32(sl))
	}
	s.cnt[sl] = n
}

func (s *stats) add(c int, n int32) {
	sl, ok := bumpSlot[c]
	if !ok {
		return
	}
	if s.cnt[sl] == 0 {
		s.touched = append(s.touched, int32(sl))
	}
	s.cnt[sl] += n
}

func (pa *phpParser) measure(st *stats, body tsNode, src []byte, prune []bool) {

	st.cyclomatic = 1
	pa.cur.start(body)
	defer pa.cur.done()
	depth := 0
	loopDepth := 0
	var nestStack, loopStack []int
	for {
		node := pa.cur.node()
		t := slot(kindID(node))
		typed := isNamedN(node)

		for len(nestStack) > 0 && nestStack[len(nestStack)-1] >= depth {
			nestStack = nestStack[:len(nestStack)-1]
		}
		for len(loopStack) > 0 && loopStack[len(loopStack)-1] >= depth {
			loopStack = loopStack[:len(loopStack)-1]
			if loopDepth > 0 {
				loopDepth--
			}
		}

		if typed && kNest[t] {
			nestStack = append(nestStack, depth)
			if int32(len(nestStack)) > st.maxNesting {
				st.maxNesting = int32(len(nestStack))
			}
		}
		if typed && kLoops[t] {
			loopStack = append(loopStack, depth)
			loopDepth++
			if int32(loopDepth) > st.maxLoopDepth {
				st.maxLoopDepth = int32(loopDepth)
			}
			st.cyclomatic++
			st.cognitive += int32(max(1, len(nestStack)))
			st.bump(cNLoops)
		} else if typed && kBranches[t] {
			st.cyclomatic++
			if len(nestStack) > 0 {
				st.cognitive += int32(len(nestStack))
			} else {
				st.cognitive++
			}
			if loopDepth > 0 {
			}
		}

		if cf := &kCounterFlag[t]; cf[0] >= 0 {
			st.bump(cf[0])
			if cf[1] >= 0 {

				st.set(cf[1], 1)
			}
		}

		switch {
		case kCalls[t]:
			pa.onCall(st, node, src, loopDepth)
		case kOperators[t]:
			st.nOperators++
			st.operators[t] = true
		case kStrings[t]:

			seg := src[startByte(node):endByte(node)]
			key := clipBytes(seg, 40)
			st.operands[string(key)] = true
			st.nOperands++
			pa.onString(st, node, seg, loopDepth)
		case kNumbers[t]:
			lt := bytes.TrimSpace(src[startByte(node):endByte(node)])
			st.nOperands++
			st.operands[string(lt)] = true
			if !magicNumbers[string(lt)] && numRe.Match(lt) {
				st.literals = append(st.literals, litRec{"number", string(lt),
					int32(startRow(node)) + 1, true})
			}
		case kComments[t]:

		case childCount(node) == 0:
			st.nTokens++
			st.nOperands++

			seg := src[startByte(node):endByte(node)]
			st.operands[string(clipBytes(seg, 40))] = true
		}

		if kOnNode[t] {
			pa.onNode(st, node, src, loopDepth)
		}

		descend := prune == nil || !prune[t]
		if descend && pa.cur.first() {
			depth++
			continue
		}
		for !pa.cur.next() {
			if !pa.cur.up() {
				st.nTokens += st.nOperators
				return
			}
			depth--
		}
	}
}

var colNameToIdx = func() map[string]int {
	m := make(map[string]int, len(symbolsColumns))
	for i, n := range symbolsColumns {
		m[n] = i
	}
	return m
}()

func txt(n tsNode, src []byte) string {
	return string(src[startByte(n):endByte(n)])
}

func walkAll(root tsNode, fn func(tsNode) bool) {
	stack := []tsNode{root}
	for len(stack) > 0 {
		n := stack[len(stack)-1]
		stack = stack[:len(stack)-1]
		if !fn(n) {
			return
		}
		for i := childCount(n) - 1; i >= 0; i-- {
			stack = append(stack, childAt(n, i))
		}
	}
}

func countErrors(root tsNode) (int, int) {
	if !hasErr(root) {
		return 0, 0
	}
	var errs, miss int
	walkAll(root, func(n tsNode) bool {
		if kindName(n) == "ERROR" {
			errs++
		} else if isMissingN(n) {
			miss++
		}
		return true
	})
	return errs, miss
}

var questionNotes = []string{
	"ANSWERS the injection question no single-file checker can answer: the read\n     of $_GET and the string concatenation that becomes the query live in\n     different functions.\nACT build_kind is the whole finding. `interp` and `concat` mean the value\n     was spliced into SQL text; `literal` and a prepared statement mean it\n     was not. Fix `interp`/`concat` with bound parameters, top of list\n     first -- hops=0 is a direct splice in one function.\nMISLEADS depth is capped at 4 (a facade adds 2-3 hops on its own, and past\n     4 the path is mostly unresolved edges and the answer stops meaning\n     anything), and ONLY resolved edges are walked, so this is a floor --\n     read graph-blindspots first. psalm_only counts the four superglobals\n     Psalm actually taints; $_SERVER/$_FILES are attacker-controlled in\n     practice but would not appear in a Psalm baseline.",
	"ANSWERS local and remote file inclusion, which in PHP is a single\n     `include $page` away from remote code execution.\nACT an `include` whose argument is not a literal is the finding. Replace it\n     with a whitelist map from a request value to a fixed path. Nothing\n     else is safe -- basename() and str_replace('..') both have bypasses.\nMISLEADS depth is capped at 3 because an include this far from its input is\n     usually a template loader with a fixed set of names. A router that\n     builds paths from a config array shows here and is fine. A literal\n     include is excluded entirely; only the variable ones are listed.",
	"ANSWERS both halves of a PHP object-injection chain at once. Half one is a\n     reachable `unserialize`; half two is the set of __destruct / __wakeup\n     / __toString methods ANYWHERE in the tree, because those run with no\n     call site the moment a crafted payload is deserialized.\nACT a reachable unserialize is exploitable in proportion to gadgets_in_repo,\n     which is why that column is repo-wide rather than per-namespace.\n     Replace with json_decode, or pass allowed_classes: false.\nMISLEADS hops=0 is the normal result, not a missing measurement: the read\n     and the sink usually sit in one function. Depth is capped at 4. The\n     gadget count is a COUNT of magic methods,\n     not a proof any chain composes -- building one needs a property write\n     path this does not model. Conversely a gadget in an installed package\n     under vendor/ is invisible here and PHPGGC's whole catalogue lives\n     there, so a low count is not safety.",
	"ANSWERS command injection across function boundaries.\nACT escapeshellarg on the ARGUMENT, never escapeshellcmd on the whole\n     command -- the second does not stop argument injection. Better still,\n     use proc_open with an argument ARRAY so no shell is involved.\nMISLEADS depth is capped at 3: a shell call three frames from its input is\n     usually a deployment or build helper, and past that the paths are\n     dominated by unresolved edges. `exec` as a bare method name also\n     matches PDO::exec, which is a SQL sink and not a shell one -- the\n     driver column in Q2 is where that distinction lives.",
	"ANSWERS reflected XSS: an `echo`/`print` of a value that came from a\n     superglobal, with no htmlspecialchars between them.\nACT raw_echo is the finding and escaped is the counter-evidence -- a\n     function with raw_echo>0 and escaped=0 is the shape to fix. Escape at\n     output with htmlspecialchars(..., ENT_QUOTES, 'UTF-8'), or use a\n     template engine that escapes by default.\nMISLEADS hops=0 is the normal result -- `echo $_GET['x']` in one function\n     is the commonest shape by far, and a row with hops>0 is the rarer,\n     more interesting case. Escaping is detected LEXICALLY inside the\n     echo statement, so a\n     value escaped one frame earlier reads as raw here, and one escaped\n     with a project-specific helper this does not know reads as raw too.\n     A Blade/Twig template compiled to PHP escapes correctly and may still\n     appear. Treat a row as 'check', not as 'vulnerable'.",
	"ANSWERS the N+1 no per-file linter can see, because the loop is in the\n     controller and the query is two frames down in the model.\nACT eager-load the relation, batch the ids into one WHERE IN, or hoist the\n     query out of the loop. loop_depth>1 multiplies.\nMISLEADS trip count is invisible: a loop over a fixed three-element config\n     array is not an N+1. `->get`/`->find`/`->first` are counted as query\n     calls by NAME, so a collection's ->first() is a false positive. Depth\n     is capped at 3 hops from the loop.",
	"ANSWERS the authentication bypass PHP is famous for. Before 8.0,\n     '0e123' == '0e456' was true because both are 'numeric'; 8.0 fixed the\n     string-to-int direction but == still coerces across types, so\n     `$_GET['admin'] == true` is true for any non-empty string, and\n     in_array($x, $arr) without the third argument is a loose search.\nACT use === for every comparison of a value that came from a request, and\n     hash_equals for anything secret. loose_cmp on a token check is the\n     shape that matters; a loose compare on two ints is noise.\nMISLEADS this counts loose comparisons ANYWHERE in a function that also\n     reads a superglobal or is reachable from one within 3 hops -- it does\n     NOT prove the tainted value is an operand. Read the function. A\n     codebase already on strict_types still juggles at ==; the declare\n     governs parameter coercion, not comparison.",
	"ANSWERS which namespaces mix database drivers. It matters because each\n     driver escapes differently -- mysqli_real_escape_string needs a live\n     connection handle and silently returns an empty string without one,\n     PDO::quote is connection-bound too, and a query builder does neither\n     because it binds. Mixing them means no single review rule applies.\nACT pick one. If a namespace shows both pdo and mysqli, the migration was\n     never finished and the half-migrated code is where the unescaped\n     concatenations live.\nMISLEADS the driver is inferred from the CALLEE NAME, because the receiver's\n     type is not knowable without full inference. `->query` on a PDO handle\n     and `->query` on a query builder are indistinguishable here and both\n     land in `pdo`. `builder` is a guess from Laravel/Doctrine method\n     names. Read this as 'how many escaping conventions are in play', not\n     as an inventory of connections.",
	"ANSWERS where uploaded files enter. Unrestricted upload is a direct path\n     to remote code execution: a .php written under the web root runs,\n     and a filename containing ../ escapes wherever you meant to put it.\nACT never trust the client-supplied name or MIME type. Generate the\n     stored name yourself, verify the content, store OUTSIDE the web\n     root, and serve through a script rather than a URL path.\nMISLEADS this finds the READ of $_FILES, not the write. A handler that\n     passes the array straight to a hardened library is fine and appears\n     here; one that builds a path by concatenation does not look worse.",
	"ANSWERS where the code silences errors instead of dealing with them.\n     `@` suppresses the diagnostic and returns a falsy value, so the\n     failure continues as data -- a null that becomes an empty string\n     that becomes a wrong row.\nACT delete the @ and handle what it was hiding. `@$a[k]` predates the\n     null-coalescing operator and should be `$a[k] ?? default`; `@unlink`\n     should be `file_exists` or a caught exception.\nMISLEADS a few @ on genuinely optional filesystem probes are pragmatic,\n     not wrong. What matters is @ near a superglobal or a SQL call,\n     which is why those columns are here.",
	"ANSWERS how much of this codebase is invisible to every static check,\n     including this one. `$$name`, `$obj->$method()` and `new $class`\n     are resolved at run time, so the call graph simply stops there.\nACT if the set of targets is known, a match or a map of closures is\n     faster AND analysable. Where dynamic dispatch is genuinely needed,\n     validate the name against an allow-list before calling it.\nMISLEADS this is a blindness measure, not a bug list. A DI container\n     doing `new $class` is the correct implementation of a container.\n     The rows that matter are the ones that also read a superglobal.",
	"ANSWERS which classes are usable as gadgets. A deserialization attack\n     does not call your code directly -- it constructs an object graph\n     and lets PHP invoke the magic methods on the way in and out. Any\n     __destruct that touches the filesystem is a primitive.\nACT the fix is upstream: never unserialize untrusted input, use JSON.\n     Where a magic method must exist, keep it free of side effects --\n     no file operations, no exec, no SQL.\nMISLEADS a class is only a gadget if the attacker can reach\n     unserialize at all; see unserialize-gadget-frontier for that half.\n     This lists the ammunition, not the gun.",
	"ANSWERS where PHP's type coercion still applies. Without\n     declare(strict_types=1), \"5 apples\" passed to an int parameter\n     becomes 5, and a caller passing the wrong thing gets silently\n     corrected instead of corrected loudly.\nACT add the parameter types, then add strict_types=1 to the file. Doing\n     it in that order means the types are enforced the moment they are\n     declared, rather than documenting an intent nothing checks.\nMISLEADS a method whose callers are all internal and all typed is not\n     really at risk. fan_in and is_public together are the ranking:\n     a widely-called public untyped method is the one that bites.",
	"ANSWERS what might be deletable.\nACT grep the name as a STRING before deleting anything: a registry entry,\n     a config value or a reflective call keeps a symbol alive with no edge\n     to show for it.\nMISLEADS this is the query most likely to be wrong, and `graph-blindspots`\n     measures by how much. Public symbols are excluded because a caller\n     outside this tree cannot be seen at all, so what is left is private\n     and unreferenced -- a much weaker claim than dead.",
	"ANSWERS the SSRF question Psalm's taint analysis needs a full config to\n     ask and PHPStan will not ask at all: not whether the code fetches a\n     URL -- most apps do -- but whether a request-facing controller can\n     reach the fetch. That is the difference between a scheduled importer\n     and an open proxy into the private network.\nACT allow-list the host before the call and forbid redirects to private\n     ranges. `reached_from` names the controller whose input needs the\n     check; fewest hops first, because those have the least code in\n     between to sanitise anything.\nMISLEADS reachability is not taint -- a controller may reach a fetch that\n     only ever sees a constant URL. Depth stops at 4 hops, and a call made\n     through a container (`$app->make(...)`) or a magic `__call` is not an\n     edge here at all.",
	"ANSWERS where unserialize() is called, which can instantiate arbitrary\n     classes and call magic methods. A crafted payload is an RCE vector.\nACT use json_decode instead; if unserialize is needed, use allowed_classes.\nMISLEADS unserialize on trusted internal data is safe. The graph sees the\n     call but not the input source.",
	"ANSWERS where eval, dynamic calls, or dynamic includes are used, which\n     can execute arbitrary code. If any part is user-controlled, this is RCE.\nACT validate input; use fixed function names; never eval user input.\nMISLEADS a dynamic call with a validated constant string is safe. The graph\n     sees the call but not the argument source.",
	"ANSWERS where include or require is called with a variable, enabling LFI\n     (Local File Inclusion) if the path is user-controlled.\nACT use a whitelist of allowed files; never include user input.\nMISLEADS a dynamic include with a validated constant is safe. The graph\n     sees the call but not the validation.",
	"ANSWERS where header() is called for a redirect but execution continues\n     after the header, so the redirect is sent but the code below still runs.\nACT call exit or die after a redirect header.\nMISLEADS a header that sets content-type or cache-control is not a redirect\n     and should not exit. The graph counts header calls, not the header text.",
	"ANSWERS functions that call header() AND read a superglobal -- the shape\n     of an unvalidated redirect: header(\"Location: \".$_GET['next']).\n     The superglobal read is the attacker-controlled input candidate.\nACT validate the target against an allowlist; never forward a user-supplied\n     URL, and call exit after the header.\nMISLEADS same-function co-occurrence is NOT data flow -- the superglobal\n     value may never reach the header, and a constant Location beside an\n     unrelated $_GET read reads as a violation. The header text is not\n     captured, so a fixed redirect cannot be told from an open one.\n     setcookie/session_start share the category but are excluded by\n     matching the bare header() pattern only.",
	"ANSWERS string literals at least 12 chars long whose text names a\n     credential (password, token, api_key, secret, bearer, jwt, ...) --\n     the literal that a committed secret looks like.\nACT rotate and move to a secret manager; never commit the literal.\nMISLEADS a format string or test fixture containing the WORD token/pass\n     reads as a candidate (the filter is the literal's own text, not its\n     use); values over 200 chars are truncated at capture; a secret\n     built from parts or read from an env var is invisible here.\n     This is a candidate list, not a verdict.",
	"ANSWERS functions that touch simplexml / DOMDocument / XMLReader -- the\n     surface where entity expansion is decided.\nACT disable external entity loading (LIBXML_NONET | LIBXML_NOENT off) or\n     reject DTDs entirely.\nMISLEADS the parser CONFIG is not modeled: a parser with entities\n     disabled ranks the same as one without. The capture is the bare\n     function/constructor name, so a wrapper around simplexml_load_string\n     is invisible.",
	"ANSWERS functions that call fopen/file_get_contents/readfile/file with a\n     variable path AND read a superglobal -- the shape of path traversal:\n     file_get_contents($_GET['f']).\nACT validate the resolved path stays under a configured root before\n     opening.\nMISLEADS same-function co-occurrence is NOT data flow -- the input value\n     may never reach the open, and a constant-open beside an unrelated\n     superglobal read reads as a violation. The path is not analyzed: a\n     variable path is assumed suspicious, a literal is not; framework\n     wrappers (->fopen, Storage facade) are invisible to the free-function\n     capture.",
	"ANSWERS functions that call move_uploaded_file AND read $_FILES -- the\n     shape of an unchecked upload: move_uploaded_file($_FILES['f']\n     ['tmp_name'], $dst).\nACT check extension, MIME and size against an allowlist before moving;\n     store outside the web root.\nMISLEADS same-function co-occurrence is NOT data flow -- the check may\n     happen elsewhere in the function or be missing entirely; the graph\n     sees the move, not the validation. An upload handled through a\n     framework request object (Laravel's $request->file) is invisible to\n     the $_FILES capture.",
	"ANSWERS functions that call error_log AND read a superglobal -- the\n     shape of log forging: error_log($_GET['msg']).\nACT sanitize newlines and control characters in log messages; never log\n     raw user input.\nMISLEADS same-function co-occurrence is NOT data flow -- the input value\n     may never reach the log call, and a constant message beside an\n     unrelated superglobal read reads as a violation. Framework loggers\n     (Monolog, Log facade) are invisible to the bare error_log capture.",
	"ANSWERS functions that read a superglobal and contain NO auth-family\n     call (session_start/regenerate_id, password_verify, hash_equals,\n     login, auth) -- the surface where a handler may be missing its\n     authorization check.\nACT add the session/auth check; verify the route is in the protected\n     group.\nMISLEADS auth may live in middleware, a base controller, or an\n     auth middleware class -- same-function co-occurrence only, so a\n     protected handler whose check lives outside the body reads as\n     open. A login or public endpoint legitimately has no auth. The\n     markers are name-based substrings, so a wrapper around the auth\n     call is invisible and counts as open.",
	"ANSWERS where session_start is called but session_regenerate_id is not,\n     leaving the session vulnerable to fixation attacks.\nACT call session_regenerate_id(true) after authentication.\nMISLEADS a session that is regenerated elsewhere in the call chain is safe;\n     the graph sees the function but not the full request lifecycle.",
	"ANSWERS where extract() is called, which imports variables from an array\n     into the current scope. extract($_GET) overwrites any local variable.\nACT never call extract on user input; access keys explicitly.\nMISLEADS extract on an internal, trusted array is safe. The graph sees the\n     call but not the argument.",
	"ANSWERS where == is used instead of ===, which performs type coercion.\n     0 == 'abc' is true in PHP <8; '' == 0 is true.\nACT use === for all comparisons.\nMISLEADS == for comparing two strings or two ints of known type is safe.\n     has_strict_types=1 means the file declares strict_types.",
	"ANSWERS where the @ operator is used to suppress errors, hiding real bugs.\n     @ also slows down the call because PHP's error handler is invoked.\nACT handle the error explicitly (try/catch, or check the return value).\nMISLEADS @ on a function that legitimately may fail (fopen on optional file)\n     is sometimes correct, but checking the return value is better.",
	"ANSWERS where a weak hash algorithm is used.\nACT use hash('sha256') or stronger; for passwords use password_hash().\nMISLEADS MD5 for a non-security checksum is fine.",
	"ANSWERS where a remote URL is fetched, which can be exploited for SSRF if\n     the URL is user-controlled. The server fetches an internal resource.\nACT validate and restrict the URL; never fetch user-supplied URLs directly.\nMISLEADS a fetch of a constant API URL is safe. The graph sees the call but\n     not the URL source.",
	"ANSWERS where a controller action handles POST/PUT/DELETE but the function\n     shows no evidence of CSRF validation. Each row is a missing defense.\nACT ensure the framework's CSRF middleware is enabled, or check the token.\nMISLEADS a framework with global CSRF middleware handles this automatically;\n     the graph sees the function but not the middleware.",
	"ANSWERS which traits spread methods across the widest class set -- the\n     first candidates for refactoring into a shared service or a value\n     object, because every use site is a copy of the same behavior.\nACT a trait adopted by many classes is either a service hiding in a copy\n     (inject it instead) or a genuinely shared slice (good -- but then\n     test it once and document the contract).\nMISLEADS `used_by` counts classes that `use` the trait by simple name;\n     an interface or abstract class adopting it is not counted, and a\n     trait used only inside a closure/conditional may not be tracked.",
	"ANSWERS the namespace-level dependency balance: incoming distinct\n     classes that call INTO this namespace versus outgoing distinct\n     classes this namespace calls. `instability` is efferent/(aff+eff),\n     0 = consumed by everything, 1 = depends on everything.\nACT a namespace near 1.0 with high afferent is a hub that should be\n     stable; a namespace near 0 that nothing imports (low afferent) is a\n     leaf worth keeping free of infrastructure imports.\nMISLEADS attribution is via the calling function's class; a function in\n     a namespace with no class (plain function) has no home and is not\n     counted, so namespace-level numbers undercount plain-function code.",
	"ANSWERS which classes lean hardest on scoped calls (`self::`,\n     `parent::`, `static::`). Scoped calls are where late static binding\n     surprises live: `static::` resolves at the runtime caller's class,\n     `self::` at the definition site, and a copied method body between\n     the two is how an override silently gets bypassed.\nACT review each scoped call for whether `static::` is what the author\n     needs (usually it is) and whether the callee survived a move\n     between parent and child.\nMISLEADS the graph counts ALL scoped calls in one counter and CANNOT\n     tell self:: from static:: apart -- that needs lexing the receiver.\n     Rows are therefore hotspots to audit by eye, not confirmed LSB bugs.\n     Calls through a variable (`$this->`), plain method calls, and\n     constructor-promotion aliases are excluded.",
	"ANSWERS classes whose namespace lacks any prefix declared in\n     composer.json autoload.psr-4. When the namespace matches no root,\n     the autoloader falls back to file scanning or classmap, and moving\n     the file breaks the lookup.\nACT add the namespace root to psr-4, or move the class to the matching\n     directory; a class under App\\ should sit under src/App/ or the\n     root that maps to it.\nMISLEADS composer.json is read only for its psr-4 ROOTS (up to 400\n     chars), and a namespace is judged \"covered\" if it STARTS WITH a\n     root; overlapping roots, `classmap` entries, and per-file\n     configurations all evade this. A bare root like App\\\\ with no\n     directory equivalent is reported even where hand-loaded manually.",
	"ANSWERS classes declaring __call/__callStatic/__get/__invoke in the\n     same FILE that also contains calls no method implements -- the\n     shape where a misspelled or removed method silently reroutes to\n     the magic handler instead of failing loudly.\nACT add real methods for the names actually called; a magic method\n     should be a deliberate proxy API, not a crash mat for typos.\nMISLEADS attribution is FILE-SCOPED, not edge-scoped: the analyzer\n     cannot resolve `$obj->missing()` to the class, so the query counts\n     unresolved calls in the class's file and the mismatch can point at\n     a DIFFERENT class in the same file. A deliberate proxy (every call\n     routed through __call) is exactly this shape and correct.",
	"ANSWERS how many classes name each interface in their implements\n     clause -- the declared implementation breadth of every contract.\n     Rows with implementors=0 are the contracts nothing honors in-tree.\nACT a high-breadth interface is a stable-seam candidate; a\n     zero-implementor one is dead abstraction, or a seam satisfied\n     entirely by code outside the tree.\nMISLEADS implements is a comma-joined declared-name list per class and\n     matching is by exact name against that list, so aliased or\n     namespaced spellings undercount; satisfaction via duck typing\n     (PHP does not require `implements`) has no row at all; and a\n     class that declares the interface but never uses it is counted\n     the same as one fully implementing it.",
	"ANSWERS the hooks each abstract class declares and how many concrete\n     subclasses exist to implement them -- the interface a change to the\n     abstract breaks across. Abstract classes with zero concrete\n     subclasses in-tree are either templates consumed elsewhere or\n     dead scaffolding.\nACT an abstract skeleton with one concrete subclass is often better\n     off as a plain interface; with many, it is a template-method\n     pattern worth documenting.\nMISLEADS subclass lookup is by the extends TEXT column with name\n     boundaries, so anonymous classes, string-built class names, and\n     namespaced aliases of the parent can undercount; a concrete\n     subclass that never overrides a given abstract method is counted\n     as a potential implementor, not a proven one.",
	"ANSWERS SQL built by interpolation/concat/format, never prepared, paid\n     per iteration when the site sits in a loop: the perf + injection\n     double hit. `superglobal-to-sql` owns the TAINT ranking; this owns\n     the BUILD-SHAPE ranking and deliberately includes rows with no\n     superglobal in sight.\nACT prepare once outside the loop and parameterise the values; every\n     interpolation is an injection site the moment the string is not a\n     constant.\nMISLEADS is_sanitized is a textual scan and a wrapper defeats it\n     silently; build_kind 'variable' (a whole query in one variable) is\n     excluded by construction -- the variable was built elsewhere and\n     its construction site is where the real question lives.",
	"ANSWERS functions that BOTH read a psalm-tainted superglobal AND call a\n     remote-fetch sink: the SSRF review list. The URL host may be the\n     internal network, and the function is the exact place a firewall\n     bypass would ship.\nACT allowlist the URL host/scheme; never fetch raw user input. The\n     superglobal key is in the row -- it tells you the input field.\nMISLEADS same-function co-occurrence is NOT data flow -- the URL may be\n     constant despite the read (the row names both so you can see); a\n     validation wrapper between read and fetch is invisible (false\n     negative class); the sink list is the hazard capture and is\n     name-based. `remote-fetch-ssrf` is the coarser per-symbol counter;\n     this is the same-function join.",
	"ANSWERS parameters typed T with default null: implicitly nullable,\n     deprecated in PHP 8.4. Every call site that relied on the implicit\n     nullability keeps working -- the deprecation is a contract smell,\n     not a break.\nACT spell it ?T; behaviour identical, deprecation gone.\nMISLEADS only a deprecation when the repo targets PHP >= 8.4 -- check\n     the runtime pin before acting; untyped and variadic params are\n     excluded by construction; an explicit `?T = null` is the control\n     and does not appear.",
	"ANSWERS deprecated methods with in-tree callers: the migration list.\n     Each row is a caller that will keep working for a while and then\n     silently break on a major release.\nACT migrate the callers top-down; the deprecation message says where.\nMISLEADS is_deprecated comes from the #[Deprecated] attribute OR a\n     @deprecated docblock directly above the method -- a docblock\n     separated by a comment reads as clean; a deprecated method called\n     only through call_user_func or a variable is invisible; public-API\n     deprecation is deliberate, so the rows are the migration list, not\n     violations.",
	"ANSWERS handlers catching the widest exceptions: \\Throwable catches\n     TypeError, ValueError, Error and every user exception -- the\n     catch-all that turns programming errors into silent nulls.\nACT catch the specific exception the path can produce; a top-level\n     boundary handler is the legitimate row.\nMISLEADS n_catch_broad counts catch clauses whose type text contains\n     Throwable or equals Exception: `catch (RuntimeException)` is\n     correctly absent, and a handler that rethrows is not\n     distinguished from one that swallows.",
	"ANSWERS dynamic property writes: deprecated since 8.2 for classes\n     without #[AllowDynamicProperties] or __set, and a shape-hiding\n     sink -- the property is invisible to every static reader.\nACT declare the property, or use an explicit array/allowlist; if the\n     class is a data bag, #[AllowDynamicProperties] with a comment.\nMISLEADS classes defining __get/__set are excluded by the magic-method\n     check; a dynamic property READ is a different capture and is\n     absent; `$obj->fixed = v` (a literal property name) is not a\n     dynamic write and does not appear.",
	"ANSWERS methods whose LAST parameter is a boolean with a default: the\n     boolean-flag anti-pattern. Callers read `sendMail($to, $b, true)`\n     and cannot tell the flag from the content.\nACT split into two methods, or replace the flag with an enum/options\n     array; a boolean default of false in a rarely-called hook is the\n     legitimate row.\nMISLEADS the flag must be the LAST param with a literal false default;\n     `$flag = false` earlier in the list or a true default is missed;\n     fan_in weights the migration cost, and methods with no in-tree\n     callers are excluded.",
	"ANSWERS the NPath estimate -- the product of branch counts, capped at\n     2^cyclomatic: every added if doubles the paths the next reader\n     must trace. Rows are the functions where one more branch is the\n     difference between testable and untestable.\nACT split on the axis with the fewest paths; extract the decision\n     table into data.\nMISLEADS the estimate is 2^cyclomatic, not PHPMD's exact product: a\n     switch of 10 cases reads as 2^cyclomatic instead of 10x, and a\n     loop containing a branch reads the same as a branch containing a\n     loop; the cap keeps the ranking honest beyond 2^20.",
	"ANSWERS the functions the Halstead-based maintainability index ranks\n     worst: dense operators, many tokens, high complexity. The score\n     is this analyzer's materialized MI (0-100), the same family as\n     PhpMetrics'.\nACT the bottom rows are where a refactor pays the most per line;\n     decompose the operand-dense core first.\nMISLEADS MI is a formula, not a verdict: a long flat data-formatter\n     ranks badly and may be perfectly clear; the exact PhpMetrics MI\n     needs unique-operator counting this analyzer approximates.",
	"ANSWERS the Laravel/Symfony deployment bug the docs warn about in\n     exactly these words: after `config:cache`, every env() call OUTSIDE\n     the configuration files reads null at run time. A null that becomes\n     a default database password is not a config problem, it is an auth\n     bypass. fan-in and runtime_entry_reaches are the graph's answer to\n     'does anything actually execute this path after boot?'.\nACT replace the call with config('...') and move the value into a\n     config file, or cache the env read at bootstrap. Start with rows\n     where runtime_entry_reaches=1 -- a request path reads null TODAY if\n     the config is cached.\nMISLEADS exclusion is a substring test on the path (any directory\n     named config counts), so env() inside App\\Config\\ support classes\n     is hidden too -- a false negative class, not a false positive one.\n     callers_up counts only RESOLVED static edges within 2 hops, so on a\n     container-heavy codebase it is a floor, not a census.",
	"ANSWERS the Laravel queue-ordering race: a job dispatched inside a\n     database transaction can be picked up by a worker BEFORE the\n     commit lands, so it reads rows that were never written. The docs'\n     fix is dispatch()->afterCommit(); the graph's contribution is\n     finding the dispatch that is 2-3 calls deep from the transaction\n     opener, where no linter looking at one file can see the pair.\nACT route the job through afterCommit (or set public $afterCommit =\n     true on the job), or move the dispatch outside the transaction.\n     hops=0 means the dispatch sits in the transaction function itself.\nMISLEADS depth capped at 3 over RESOLVED edges only -- a dispatch\n     through a container or __call is invisible, so this is a floor.\n     `dispatch` also fires self-contained events with no queue\n     involved, and those are harmless here; the after_commit column is\n     the counter-evidence that says the code already knows the rule.",
	"ANSWERS the torn-write frontier: a function (or the function one hop\n     below it) issues two or more mutations -- save, create, update,\n     delete, increment -- with no beginTransaction in sight, so a\n     failure between the writes leaves half a fact in the database.\n     Ledger-shaped code (debit then credit) is the row that costs\n     money.\nACT wrap the writes in DB::transaction(fn() => ...), or prove the\n     second write is derived and idempotent. writes_in_callees>0 means\n     the pair is split across functions -- the case a per-file linter\n     cannot see at all.\nMISLEADS write is recognized by METHOD NAME, so ->update on a cache\n     store or ->delete on a filesystem wrapper counts as a write, and\n     two writes to UNRELATED tables can be a deliberate trade-off.\n     The transaction check is same-function only: a transaction opened\n     by a CALLER guards the writes but still reads as n_transaction=0\n     here (read hops=1 rows with that in mind).",
	"ANSWERS the half of SQL injection superglobal-to-sql cannot see: the\n     input arrives as a method argument or a validated DTO, so no\n     superglobal read sits anywhere in the taint path -- but the\n     controller can still REACH a helper that splices variables into\n     SQL text. Reachability from the request-facing boundary is the\n     review order, and hops is how far the fix has to travel.\nACT make the reachable builder use bound parameters, fewest hops\n     first; a row with prepared=0 and interp>0 two hops from a\n     controller is the classic 'validated input, unsafe sink' shape.\nMISLEADS reachability is not taint -- a controller may reach a builder\n     that only ever sees constant ids. Depth stops at 4 hops over\n     resolved edges; a call made through a container ($app->make) or a\n     magic __call is not an edge here at all, so the list is a floor.",
	"ANSWERS the cross-function path-injection question. path-traversal-surface\n     catches fopen($_GET['f']) written in ONE function; this catches the\n     common shape -- the controller reads the request, passes it down,\n     and THREE FRAMES later a helper opens, overwrites or unlinks a path\n     built from it. Includes file_put_contents with a computed path and\n     the unlink/rename family, i.e. arbitrary file WRITE and DELETE, not\n     just read.\nACT resolve the path against a fixed root (realpath + strpos check)\n     inside the SINK -- validating in the caller does not survive the\n     next caller. dyn_writes ranks above dyn_opens: write is RCE via\n     uploaded php, delete is DoS.\nMISLEADS reachability is not taint -- the value may be re-derived as a\n     constant three frames down, and a basename() call in between is\n     invisible (it is also insufficient). Depth capped at 3 over resolved\n     edges; container dispatch hides the path entirely.",
	"ANSWERS the PHPStan level-6+/Psalm PossiblyNull* question at the\n     contract level: a function whose return type says ?T, and the\n     number of call sites that must EACH handle the null. The defect is\n     never in the callee -- it is whichever caller forgot. A function\n     with 40 call sites has had 40 chances to be wrong.\nACT work down by call_sites: either make the callee total (return a\n     non-null default, throw) or audit each call site for a null guard.\n     null_guards>0 shows the function already knows about ?? / isset.\nMISLEADS this is a RANKING of obligation, not a found null dereference\n     -- every row may be perfectly guarded. return_type is the declared\n     text, so docblock-only nullability (/** @return?T */) is invisible\n     and the true list is longer.",
	"ANSWERS how far PHPStan's `mixed` reaches: an entrypoint hands its\n     request-shaped data to a function that declares no return type\n     (or takes untyped parameters), and from there every value is\n     `mixed` -- no checker downstream can prove anything about it\n     again. Each row is a place where typed code hands control to\n     untyped code.\nACT give the callee a return type and parameter types first (the\n     boundary row pays for its whole subtree), or cast/validate at the\n     boundary before the call.\nMISLEADS depth capped at 3 over resolved edges, so the frontier is a\n     floor on container-resolved code. no_return_type=1 with\n     untyped_params=0 is often a void function -- perfectly typed in\n     spirit and only missing the `: void` keyword.",
	"ANSWERS the second half of type juggling that == queries miss:\n     in_array($x, $allowed) has NO third argument, so the search is\n     loose -- '0' matches every non-numeric string pre-8.0 and a mixed\n     needle matches the first coercible element. When the haystack is\n     an allowlist ('which roles may proceed') and the needle came from\n     the request, loose matching is an authorization bypass.\nACT add the third argument: in_array($x, $allowed, true). Also\n     array_search($x, $arr, true) -- its first match returns a key you\n     then trust.\nMISLEADS reachability is not taint: the loose search may run on two\n     internal arrays three hops from any request value and be\n     completely safe -- read the haystack, not just the row. Only\n     RESOLVED edges are walked (depth cap 3), so this is a floor.",
	"ANSWERS regex injection and its ReDoS cousin: preg_match/\n     preg_replace whose FIRST argument is not a literal, in code an\n     attacker's input reaches within 2 hops. A pattern assembled from\n     data accepts injected modifiers and quantifiers ('(a+)+$' on a\n     30-char string stalls PCRE), and preg_replace with an attacker\n     -shaped replacement is a template-injection primitive.\nACT build the pattern with preg_quote($input, '/') for every\n     interpolated fragment, and anchor user-shaped alternations. If the\n     pattern must be dynamic, keep the DELIMITERS and structure in code.\nMISLEADS a computed pattern is usually a config constant joined at\n     runtime -- safe, and indistinguishable here from a request-shaped\n     one; the hops<=2 bound plus the tainted_reads column are the\n     triage, not proof. Delimiter/content analysis of the pattern is\n     not modeled at all.",
	"ANSWERS the Laravel mass-assignment question: the model mutation front\n     door (fill, forceFill -- and the create-family, captured under the\n     write counter) in a function that also reads request input, and\n     whether the model declares $fillable/$guarded. Without the guard,\n     a crafted form field named is_admin writes the column (the 2012\n     GitHub mass-assignment incident is the canonical story).\nACT has_fillable=0 rows first: add $fillable (allowlist) or $guarded\n     (denylist) to the model, then re-check whether the route really\n     needs is_admin in the form. Request::only([...]) beats ->all().\nMISLEADS same-function co-occurrence is NOT data flow -- the fill may\n     take a hand-built array while an unrelated ->input() reads a page\n     number. fillable detection is a property named fillable/guarded on\n     the model CLASS; a trait-provided or inherited guard reads as 0.\n     API resources serializing ->all() are invisible here.",
	"ANSWERS the debugging leftover that shipped: dd(), dump(), ray() or a\n     bare exit() sitting on a path a request can reach. In production a\n     dd() is an information-disclosure endpoint and an exit() is a\n     remote denial of service -- one POST away, not one deploy away.\n     hops=0 means it sits in the entrypoint itself, which is the common\n     and the worst case.\nACT delete the call (the debugger breakpoint replaced it years ago);\n     if it must stay, gate it on app.environment / a config flag --\n     never on an env() read, see env-outside-config.\nMISLEADS reachable is not executed: the dd may sit behind a feature\n     flag or an admin-only branch. depth capped at 3 over RESOLVED\n     edges, so a debug call reached through a container is invisible;\n     dd/dump/ray are caught by NAME, so a project helper wrapping them\n     is a false-negative class.",
	"ANSWERS session poisoning candidates: the function writes\n     $_SESSION[...] (login state, role, redirect target) while reading\n     request data. Session state is TRUSTED on every later request --\n     it bypasses every input filter -- so a value written straight\n     from the request lives exactly where attackers want it, including\n     stored XSS on the next page that echoes it.\nACT allowlist what gets stored: put scalar ids in the session, never\n     raw request arrays, and regenerate the id after any auth write\n     (session_regenerate_id -- see session-fixation).\nMISLEADS same-function co-occurrence is NOT data flow -- the write may\n     store a constant and the read may serve a different field. A\n     framework-managed session (Laravel session helper, PSR-15\n     middleware) writes through its own API and is invisible to the\n     $_SESSION capture, which makes this a raw-PHP-only lens.",
	"ANSWERS header injection across function boundaries: the sink that\n     writes response headers or cookies is reachable from a request\n     value. A newline in a header value splits the response (HTTP\n     response splitting -> cached XSS), and a request-shaped\n     setcookie path/domain attribute is a session-scoping attack. The\n     same-function family lives in open-redirect-surface; this is the\n     frontier where the header call is frames away from the read.\nACT reject CR/LF/%0d/%0a in anything reaching a header, allowlist\n     redirect targets, and set cookie attributes explicitly. hops=0 is\n     the direct case the smaller queries already rank.\nMISLEADS depth capped at 3 over resolved edges (a facade adds 2 on\n     its own), so this is a floor; reachability is not taint, and a\n     header('Content-Type: ...') constant beside a reachable read\n     ranks like a real finding -- the patterns column tells you which\n     header-family calls the function actually makes.",
	"ANSWERS where the domain reached back for the container: model and\n     entity classes making Log::/DB::/Cache::-style facade calls. A\n     facade resolves through the service container at RUN TIME, so the\n     model carries a hidden global dependency, cannot be instantiated\n     without the framework booted, and its real inputs are invisible\n     at the type level. Symfony states the same rule as 'keep\n     entities framework-agnostic'.\nACT inject the service (constructor promotion makes it one line), or\n     move the side effect into a domain service the model calls.\n     facade_calls is the count; static_calls is the surrounding\n     static-coupling context.\nMISLEADS facade matching is by the CLASS NAME text of the scoped\n     call, so a project class literally named DB or Cache (a wrapper)\n     counts, and an aliased facade (`use Log;` pointing elsewhere)\n     counts wrong -- read the import before acting. Models are\n     identified by path/class-name heuristics (is_model), so a\n     misfiled service can appear.",
	"ANSWERS the write-side N+1: a function that loops while issuing\n     save/create/update calls, so a 1000-row import costs 1000\n     round-trips plus 1000 implicit transactions. n-plus-one owns the\n     READ side followed across model boundaries; this owns the write\n     side, where the fix is different (batch/upsert, not eager\n     loading).\nACT collect the rows and issue one upsert/insert-batch after the\n     loop; wrap the whole batch in one transaction. loop_depth>=2 is\n     the quadratic row.\nMISLEADS the loop and the write are matched by co-occurrence in one\n     function (call_in_loop counts ANY call), so a write beside -- not\n     inside -- a small loop ranks high; the trip count is invisible\n     and a 3-element loop is not worth restructuring. Writes are\n     recognized by method name (see multi-write-no-transaction).",
	"ANSWERS how close the un-analyzable zone is to the request boundary:\n     an entrypoint can reach code that evals, includes a computed\n     path, or news a computed class name. Every such site ends the\n     call graph AND is a code-execution sink if the computed string is\n     ever shaped by data. command-injection ranks the sites by count;\n     this ranks them by REACHABILITY from request-facing code.\nACT replace with a match/allowlist map (class-string<T> map, template\n     whitelist). Fewest hops first: hops<=1 means one refactor away\n     from the controller.\nMISLEADS reachability is not controllability -- a DI container doing\n     new $class is the CORRECT implementation and will top this list\n     in framework code; read the target column's source. Depth capped\n     at 4 over resolved edges, so container-dispatched hops are\n     invisible and the true frontier is farther out.",
	"ANSWERS PHP's fatal-composition hazard, which is a cross-FILE fact by\n     construction: a class uses two traits that both define the same\n     method name. PHP aborts at load unless the class adds\n     insteadof/as conflict resolution -- so the collision is latent in\n     the tree TODAY and any rename that makes two trait methods share\n     a name turns a deploy into a fatal error. No per-file linter can\n     see the pair, because the traits and the class live in three\n     files.\nACT add `use TraitA::method insteadof TraitB;` explicitly, or rename\n     one of the methods. n_traits=2 rows are one rename away from\n     breakage.\nMISLEADS traits are matched by SHORT NAME against the class's use\n     list, so two same-named traits in different namespaces collapse\n     into one and ALIASED use-as statements can undercount; abstract\n     trait methods are counted as definitions (they do not collide at\n     runtime the way concrete ones do).",
	"ANSWERS the network-call-in-a-loop anti-pattern, weighted by loop\n     depth and by how many callers depend on the looping function. A\n     50ms API call inside a foreach over 200 rows is 10 seconds of\n     latency the profiler will blame on 'the database'. array-scan-in\n     -a-hot-method owns the in-process loops; this owns the ones that\n     leave the machine.\nACT batch the call (one request with many ids), move it outside the\n     loop, or use curl_multi. loop_depth>=2 multiplies quadratically.\nMISLEADS io_in_loop counts IO CALLS anywhere in a function with a\n     loop -- the call may be on a cold branch (an error path that\n     writes one log line). Trip counts are invisible; a loop over a\n     3-element config is not a finding.",
	"ANSWERS where regular expressions run per iteration. PCRE compiles the\n     pattern every call, so preg_match in a 5000-row loop pays 5000\n     compilations; preg_replace in a loop that rebuilds a string each\n     pass is the quadratic classic. Ranked by loop depth and the\n     number of distinct callers so the hot ones surface first.\nACT hoist a fixed pattern into a variable is NOT enough (PHP still\n     compiles per call since 7.x's PCRE cache is per-process and\n     small) -- restructure to one pass with preg_replace_callback, or\n     precompile once via the same pattern outside the loop and profile\n     before/after.\nMISLEADS the loop bound is invisible and n_preg_in_loop counts preg\n     calls ANYWHERE in a looping function, not per iteration; a 2-iter\n     loop over headers is noise. Regex_in_loop also counts matches\n     whose pattern is trivially cheap.",
	"ANSWERS cookies issued with defaults: setcookie('sid', $v) with no\n     further arguments ships a session cookie that is visible to\n     JavaScript (no httponly), travels over plain HTTP (no secure),\n     and is scoped to the whole site (no path). OWASP's session cheat\n     sheet calls for Secure+HttpOnly+SameSite on anything auth-shaped;\n     the 7th positional argument era is over -- the options-array\n     signature is the fix.\nACT use the options-array form: setcookie('sid', $v, ['secure' =>\n     true, 'httponly' => true, 'samesite' => 'Lax']). For session\n     cookies set session.cookie_httponly in php.ini instead.\nMISLEADS the arg-count test cannot see the options ARRAY form (arg 3\n     present but missing 'httponly' still passes clean) and a\n     NON-auth cookie (a UI preference) legitimately needs no flags.\n     Wrapper methods (->withCookieParams, framework responses) are\n     invisible to the bare setcookie capture.",
	"ANSWERS hidden shared state: `global $db;` / $GLOBALS['...'] inside a\n     function turns its signature into a lie -- the callers see two\n     parameters while the function reads a third nobody passes. Under\n     a long-running worker that global persists ACROSS requests, so a\n     stale cache flag in request 2 is request 1's data. fan_in is the\n     graph's contribution: how many callers inherit the invisible\n     coupling.\nACT pass the dependency as a parameter (constructor-injected is\n     better); for genuinely process-wide constants use a readonly\n     config object. The rows with high fan_in pay back per caller.\nMISLEADS n_globals counts `global` declarations and $GLOBALS reads,\n     which in a deliberately stateful legacy plugin architecture can\n     be the local idiom rather than a defect; sup_reads shows the\n     functions that mix globals with request input -- those are the\n     ones to read first.",
	"ANSWERS privilege-escalation potential via reflection: code that an\n     attacker's input can reach which instantiates classes\n     (ReflectionClass::newInstance), invokes methods or sets private\n     properties dynamically. Combined with a request-shaped class or\n     method NAME (a routing table, a service locator keyed by a\n     string), reflection is arbitrary-code-execution with a\n     respectable-looking API.\nACT allowlist the class/method names before reflecting; never pass a\n     request value to newInstance without a check against a fixed set.\nMISLEADS reflection is a favorite of legitimately generic framework\n     code (container autowiring, attribute readers) and most rows are\n     those; the hops<=3 reachability and tainted_reads columns are the\n     triage, not proof. Property/method NAMES built at runtime are not\n     captured, so a constant-name reflect ranks the same as a\n     request-shaped one.",
	"ANSWERS Psalm's TaintedCallable question, which its docs flag as one\n     of the hardest to configure: a VARIABLE invoked as a function\n     (call_user_func, array_map with a computed callback,\n     register_shutdown_function) reachable from request data. When the\n     callable string is attacker-shaped, 'indirect function call' is a\n     euphemism for code execution.\nACT check the callable against a fixed allowlist (is_callable is NOT\n     a security check -- everything string-shaped is callable), or\n     restructure to a match on a constant map. Fewest hops first.\nMISLEADS the callable category is name-based, so array_map with a\n     LITERAL 'strtoupper' ranks like a tainted one -- the patterns\n     column and tainted_reads are the triage. Depth capped at 3 over\n     resolved edges; a callable passed through a container is\n     invisible.",
	"ANSWERS constructors that cannot be trusted in tests, loops or\n     containers: a __construct that opens files, queries the database\n     or makes network calls runs that work on EVERY instantiation,\n     with no call site to grep for. Construction sites is the graph\n     fact per-file linters lack: a side-effecting constructor inside\n     a loop (see write-in-loop) multiplies the cost invisibly.\nACT move the IO out of the constructor -- a factory method that\n     returns the object, or lazy initialization on first use.\n     construction_sites ranks the migration payoff.\nMISLEADS construction_sites counts RESOLVED `new` edges only; a class\n     newed through a container or built once in bootstrap.php is a\n     legitimate one-shot and its row is noise. The IO is counted by\n     hazard name, so a wrapped IO helper is invisible (false\n     negative).",
	"ANSWERS shared mutable state: assignments to static properties\n     (self::$cache = ..., Config::$x = ...). PHP-FPM discards state\n     per request, so the bug hid for a decade; under Laravel Octane,\n     Swoole or a queue worker the property OUTLIVES the request and\n     user A's data becomes user B's cache entry. Cross-function by\n     nature: every reader of the property, in any file, inherits the\n     write.\nACT make the property readonly, or move the state into the container\n     (scoped), or key the cache by request id. Writes in hot paths\n     (fan_in) rank first.\nMISLEADS only DIRECT writes to static properties are captured --\n     array pushes into a static array (self::$a[] = x) and method-\n     mediated mutations are invisible, so this is a floor. A write\n     during explicit bootstrapping (config load) is correct and will\n     still rank.",
	"ANSWERS the double defect: a function in the model/entity layer\n     ($_POST inside a User class) reads the request ITSELF. Layering\n     says the model takes data in through parameters; taint analysis\n     says a superglobal read buried below the controller is exactly\n     the one no input-validation middleware ever sees, because the\n     framework's request object was bypassed entirely.\nACT pass the value in as a parameter and do the read at the\n     controller/action boundary; until then, this row is also your\n     taint-review list for the model layer, since no middleware can\n     sanitize what it cannot see.\nMISLEADS the model layer is identified by path and class-name\n     heuristics (is_model), so a helper misfiled under src/Models\n     reads as a model; and $_SERVER reads in models are often only\n     env/CLI probes -- check the var column of intent before treating\n     a row as a request-path finding.",
	"ANSWERS the two defects one shape signals: a controller function that\n     touches SQL directly (n_sql_calls) or builds SQL text\n     (n_sql_interp/n_sql_concat). Architecturally, the query logic is\n     unreachable from the model layer's tests and reuse. Security-wise\n     it is the top of the injection shortlist -- request-facing code\n     with string-built SQL is the combination every taint rule hunts,\n     here visible even when the input came through a validated\n     parameter instead of a superglobal.\nACT move the statement into a repository/model method with bound\n     parameters; sql_interp>0 rows are the injection review, the rest\n     are refactoring debt.\nMISLEADS controller detection is a path/class-name heuristic\n     (is_controller), so console commands misfiled under Controllers\n     count; and ->query on a fluent builder counts as sql_calls even\n     when it parameterizes internally -- sql_interp/sql_concat is the\n     column that proves text splicing.",
	"ANSWERS outbound requests that leave the TLS off: file_get_contents,\n     curl_init/curl_setopt or fopen pointed at an http:// URL. The\n     payload (an API key header, a session cookie, the response an\n     auth decision depends on) crosses the network readable and\n     writable by anyone on the path -- and the response of a\n     cleartext fetch is input your code then trusts.\nACT switch to https and verify the peer (CURLOPT_SSL_VERIFYPEER is\n     on by default -- do not turn it off to make the error go away).\nMISLEADS detection is a substring test for http:// in the CALL's\n     arguments, so 'http://localhost' dev endpoints count (usually\n     acceptable, and the config-driven URL built elsewhere is\n     invisible entirely -- a false-negative class). A literal\n     'https://' string containing 'http://' cannot occur, but a\n     scheme-relative or user-built URL will be missed.",
	"ANSWERS email header injection: mail() reachable from a request value.\n     A \\r\\n in the subject or a 'contact form' field that becomes a\n     header lets the attacker append Bcc: recipients and an arbitrary\n     body -- your server becomes the spam cannon and the mail log\n     still shows only legitimate sends. The frontier matters because\n     the mail() call usually lives in a mailer helper several frames\n     from the controller.\nACT strip CR/LF and control characters from EVERY argument to mail()\n     (subject, headers, and the address fields), or move to a mail\n     library that encodes headers. hops=0 is the direct case.\nMISLEADS depth capped at 2 because the parameterization past that is\n     usually a templating layer with constants; reachability is not\n     taint, so a mailer reached by a contact controller that passes\n     only constants ranks the same as the vulnerable one. Framework\n     mailers (Symfony Mailer, Laravel Mail) bypass mail() entirely\n     and are invisible here.",
}

var metricNotes = []string{
	"ANSWERS how much of every other answer below is guesswork. In PHP this is\n     not a footnote -- `call_user_func`, `$obj->$m()`, `new $class`,\n     `__call`/`__callStatic` and a facade layer resolved at run time are\n     idiomatic, and each one deletes an edge.\nACT read pct_blind before believing any reachability claim in Q2-Q7. On a\n     framework with a container and facades a high number is the CORRECT\n     answer, not a defect to tune away. Compare namespaces against each\n     other rather than against zero.\nMISLEADS external calls (PHP's ~1,500 built-ins, PDO, SPL) leave the tree\n     by design and are NOT counted as blindness. A resolved edge can still\n     be wrong: a method call resolves by SHORT NAME and prefers the\n     enclosing class, so `$other->save()` inside a class that also defines\n     `save()` points at the wrong one. magic_call is the count of classes\n     in this namespace defining __call/__callStatic -- every call into one\n     of those is unresolvable in principle, not just here.",
	"ANSWERS where PHP is still doing silent type coercion on the arguments that\n     matter. Without strict_types, passing \"5 apples\" to an int parameter\n     coerces to 5 and passing \"abc\" coerces to 0 -- and 0 is a valid user\n     id in most schemas.\nACT the ABSENCE of the declare is the finding, and it is per FILE, so a\n     namespace with high typed_params and low strict_files is doing the\n     work of types without the enforcement. Add the declare to those files\n     first; they have the most to gain and the least to break.\nMISLEADS strict_types governs the CALLEE's file in PHP, not the caller's,\n     which is the opposite of most people's intuition. Coercion at a call\n     site is decided by where the called function is DECLARED. A namespace\n     of pure value objects with no scalar parameters gains nothing.",
	"ANSWERS which property accesses the call graph must model as invocations.\n     `$order->total` looks like a field read in every tool built before\n     8.4 and in every reviewer's head, but with a `get` hook it executes a\n     body -- which can query, throw, or recurse.\nACT a hook with calls>0 is a function hiding behind field syntax; a virtual\n     hook (one that never touches its own backing field) has NO storage at\n     all, so every read is unconditionally a call. Those are the ones to\n     check for work in a loop.\nMISLEADS no edge points AT a hook, because no call site names it -- fan_in\n     is structurally 0 for every row here and means nothing. A codebase\n     below 8.4 shows an empty table for reasons of version, not style; the\n     same is true of n_pipe_operator and 8.5.",
	"ANSWERS which units are hardest to hold in your head. For a class that is\n     methods plus properties plus traits; for a function it is cognitive\n     complexity, which weights nesting far above length.\nACT split by responsibility. n_elif says which kind of split: a high elif\n     count is a flat dispatch (extract a map or a match) and a high nest\n     with low elif is real nesting (extract functions). A class pulling in\n     six traits has six sets of methods it did not declare.\nMISLEADS a long flat dispatch reads far more easily than a short deeply\n     nested one, which is why this sorts by cognitive rather than sloc.\n     Trait methods are NOT counted in n_methods -- they are declared\n     elsewhere -- so a Macroable-style class looks smaller than it behaves.",
	"ANSWERS which functions combine complexity with the operations PHP makes\n     dangerous. The score weights SQL string interpolation, eval, variable\n     includes and shell far above raw complexity, and SUBTRACTS for\n     escaping and prepared statements -- the mitigations are evidence.\nACT start at the top. A row with sql_interp>0 and prepared=0 is the single\n     highest-value read in this table.\nMISLEADS a heuristic, not a finding, and the weights are this tool's\n     opinion. Generated files are excluded, so the real top of the list may\n     be in code this hid. A function scoring high purely on cyclomatic is a\n     maintainability problem, not a security one -- read the columns, not\n     just the total.",
	"ANSWERS whether the numbers above cover the code you think they cover.\nACT a file with parsed=0 contributed nothing at all. A file with errors\n     contributed the symbols around the damage and nothing inside it.\nMISLEADS tree-sitter-php 0.24.1 rejects exactly three of PHP 8.5's\n     additions out of a 23-case 8.0-8.5 sweep: the (void) cast, `clone $x\n     with {...}`, and `final` on a promoted constructor property. A file\n     whose only symptom is one or three parse errors is a grammar one\n     version behind the language, not a broken file -- meta.grammar_note\n     carries the same list. Everything else in that sweep, 8.5's |> pipe\n     included, parses clean.\n     A file can also parse perfectly and still be misunderstood: inline\n     HTML islands, `eval` and `__call` all parse cleanly and carry no\n     symbols anyone can follow, and symbols_=0 with errors=0 is that case.",
	"ANSWERS which symbols the rest of the tree leans on hardest.\nACT a correctness or speed win in a high-fan-in leaf pays back once per\n     caller. Read it next to sloc -- a four-digit fan_in on a ten-line\n     function is usually a name collision, not a hot leaf.\nMISLEADS fan_in counts STATIC call sites this parser could resolve, not\n     runtime frequency, and test callers are included, so in most repos a\n     test helper outranks production code. Scope with --module first.",
	"ANSWERS what PHPMD and the PHPStan perf extensions flag statement by\n     statement and cannot prioritise. `in_array` in a loop is O(n*m);\n     `array_merge` in a loop reallocates the whole array every iteration,\n     turning an append into O(n^2). Both are only worth fixing where they\n     run, and `distinct_callers` is the graph's answer to where.\nACT flip the haystack with array_flip and use isset(), and replace the\n     merge with `$out[] =` plus one merge after the loop. Hoist count()\n     into a variable above the loop.\nMISLEADS the loop bound is not visible here, and a scan over a\n     five-element config array is not worth touching. `distinct_callers`\n     counts static call sites; a single caller inside a request loop beats\n     fifty callers on a cron path.",
	"ANSWERS which files do not declare strict_types=1, so type coercion is\n     enabled for the entire file.\nACT add declare(strict_types=1); at the top of the file.\nMISLEADS legacy code that relies on type coercion may break with strict_types.",
	"ANSWERS where a function has parameters without type declarations, so the\n     contract is implicit and PHPStan/Psalm cannot check it.\nACT add type declarations to all parameters.\nMISLEADS PHP 7.0+ is required for scalar type declarations. Legacy code on\n     PHP 5.x cannot use them.",
	"ANSWERS where a function has max_nesting > 4, making it hard to read.\nACT extract nested blocks; use early returns or guard clauses.\nMISLEADS PHP's alternative syntax (if: ... endif;) does not change nesting.",
	"ANSWERS where a function has more than 5 parameters.\nACT use an array parameter or a data transfer object.\nMISLEADS a controller action with many query params may be correct.",
	"ANSWERS which functions are called from many distinct modules.\nACT consider splitting or stabilizing the contract.\nMISLEADS a utility function is called from everywhere and is stable.",
	"ANSWERS which modules the request hits first and what they sit next\n     to. super_reads counts every superglobal read, psalm_tainted the\n     subset Psalm itself would treat as tainted (GET/POST/COOKIE/\n     REQUEST only), and sql_spliced/shell/raw_echo the sink counters\n     those reads share a function with. pct_input_facing says how much\n     of the module's functions are input-adjacent at all.\nACT triage top-down: a module with high tainted reads AND nonzero\n     sql_spliced is where the superglobal-to-sql rows will cluster;\n     run the frontier queries scoped with --module to that name.\nMISLEADS module membership is a two-directory path bucket, so a\n     framework's Http module aggregates controllers AND their\n     validators; request-object reads (->input) are NOT counted -- a\n     modern framework module can look clean here while carrying the\n     whole input surface through methods this cannot see.",
	"ANSWERS which modules carry the heaviest null load: nullable\n     parameter/return types, `?->` null-safe calls (each one an\n     admission the left side may be null), and ?? / isset guards as\n     the counter-evidence. High nullable pressure with LOW guards is\n     the module where PHPStan's PossiblyNull family would light up.\nACT add the guards (or a default object) where nullable is high and\n     null_checks is low; then see nullable-return-hotspot for the\n     per-function ranking that this module view summarizes.\nMISLEADS null_checks counts ?? / isset / empty in the SAME function,\n     while a null produced here is usually handled by the CALLER -- so\n     a well-behaved producer of optionals reads under-guarded. Types\n     come from declared syntax only; docblock nullability is\n     invisible.",
	"ANSWERS each module's error-handling posture in one row: throws and\n     try blocks (the failures raised), against broad catches, empty\n     catches and @-suppression (the failures silenced). pct_swallowed\n     is the ratio that matters: above ~50 a module is structurally\n     incapable of failing loudly, so its callers and its tests both\n     reason about a fiction.\nACT read the highest pct_swallowed modules first; replace broad\n     catches with the specific exceptions the body can raise, and\n     give empty catches a comment plus a log line at minimum.\nMISLEADS the ratio counts CLAUSES, not control flow -- one top-level\n     boundary handler legitimately catching \\Throwable for a whole\n     framework dispatch loop reads as total suppression; conversely a\n     module that never throws trivially shows pct_swallowed=0 with\n     zero error handling anywhere.",
	"ANSWERS the request surface in order: every entrypoint (controller\n     actions, handle()/__invoke on jobs and middleware, route\n     attributes) and the number of DISTINCT functions it can reach\n     within 3 call hops. reached is the blast radius a defect in that\n     entrypoint's validation can traverse; input_reads and sql_calls\n     sit in the row so the dangerous entrypoints surface first.\nACT use it to size review: an entrypoint reaching 200 functions is\n     the one whose input handling deserves its own test file, and a\n     small reached with high sql_calls is a fat controller to split.\nMISLEADS depth capped at 3 over RESOLVED edges, so container-\n     dispatched and facade-routed code shrinks every number -- compare\n     entrypoints against each other, not against 100%. Test-tree\n     entrypoints are excluded, but helpers reached ONLY from tests\n     still count toward a production entrypoint's radius.",
	"ANSWERS how much each module leans on framework facades (Log::,\n     DB::, Cache::, Auth::, ...) versus ordinary resolved static\n     calls. Facades resolve through the container at run time, so\n     pct_facade is a proxy for how much of the module's real\n     dependency graph is invisible to type checkers and to this\n     tool's edges (the calls RESOLVE, which is precisely why they\n     never look unresolved).\nACT a module above ~30% facade-static is coupled to the framework's\n     bootstrapped state; migrate its highest-fan-in functions to\n     constructor injection first. facade-in-model-layer is the\n     per-function list for the model layer specifically.\nMISLEADS facade detection is by class-NAME text (see FACADE_CLASSES),\n     so a project wrapper named DB counts and an aliased import\n     counts wrong; a module of thin controllers behind action classes\n     legitimately shows near-zero and gains nothing from the metric.",
	"ANSWERS where the __destruct/__wakeup/__toString population lives,\n     rolled up per namespace, with the hazards and call sites INSIDE\n     those methods -- the surface unserialize-gadget-frontier compares\n     against but does not localize. hazards_in_gadgets is the part\n     that turns a magic method into a primitive (a __destruct that\n     unlinks files, a __toString that queries).\nACT keep gadget methods free of side effects: no file ops, no exec,\n     no SQL. Any namespace with gadgets AND nonzero hazards_in_gadgets\n     belongs on the deserialization review with the frontier query.\nMISLEADS gadget means 'PHP invokes it without a call site', NOT 'the\n     attacker can reach unserialize' -- a repo may show ten gadgets\n     and zero unserialize calls (see the frontier query for that\n     half). Classes under vendor/ are excluded from the parse by\n     default, and PHPGGC's catalogue lives exactly there.",
	"ANSWERS each module's write discipline: how many mutation calls\n     (save/create/update/delete family), how many transaction sites\n     guard them, and how many queue dispatches sit nearby -- the\n     material dispatch-in-transaction works over. pct_tx_guarded is\n     the module's guarded-writer ratio: a module writing heavily at\n     0% has no transaction culture, and its multi-write rows are\n     findings, not style.\nACT start where write_calls is high and pct_tx_guarded is 0; then\n     check the module's dispatches against the transaction frontier\n     query before enabling a queue worker.\nMISLEADS writes are recognized by method name, so a module of cache\n     and filesystem wrappers can show write_calls with no database\n     behind them; the ratio counts FUNCTIONS, so one shared\n     transaction-wrapper helper guarding everything still reads as\n     0% -- look for that helper before condemning the module.",
	"ANSWERS the shadow API tests keep alive: functions with zero\n     production callers but nonzero test callers. Dead-code cannot\n     list them (tests call them) and hot-multipliers hides them (fan\n     -in comes from tests). Each row is either a helper that belongs\n     in the test tree, or production code whose real callers were\n     never written -- either way the production dependency is a\n     fiction.\nACT for each row decide: move it under tests/ (it is a fixture\n     builder), or delete it with its test (nothing real uses it), or\n     restore the missing production caller. all_callers equal to\n     test_callers is the proof in-row.\nMISLEADS callers are RESOLVED edges only: a function invoked via a\n     container tag, a route string or call_user_func shows zero\n     production callers and lands here wrongly -- grep the name as a\n     string before deleting. is_test flags both the caller's file and\n     the caller symbol, so an integration-test helper living in src/\n     is judged by its callers, not its address.",
	"ANSWERS how much debugging scaffolding each module still carries:\n     dd/dump/ray calls, bare exit statements (statements, so no call\n     site -- counted structurally), @-suppression and raw echo. A\n     module with nonzero debug_calls in non-test files is one\n     code-review slip from shipping them; debug-reach-production is\n     the query that checks whether a request can already reach them.\nACT delete or gate the calls (environment check, not env()); run the\n     module's rows through debug-reach-production to see which ones a\n     request can hit today.\nMISLEADS exit statements are counted even when they are the correct\n     CLI idiom (a console command ending in exit(0) is fine), and\n     dump() inside test files is excluded but a helper under src/\n     called only BY tests still counts -- cross-check test-only-\n     coupling before deleting anything.",
}

type colDesc struct {
	name   string
	typ    string
	nullOK bool
	deflt  string
}

type tableDesc struct {
	name string
	note string
	cols []colDesc
}

func i32c(n string) colDesc { return colDesc{n, "int", false, "0"} }
func txtc(n string) colDesc { return colDesc{n, "text", false, "''"} }
func txtn(n string) colDesc { return colDesc{n, "text", true, ""} }

var graphSchema = []tableDesc{
	{"meta", "run facts: what was parsed, with what, and what was skipped", []colDesc{
		txtc("key"), txtc("value"),
	}},
	{"modules", "grouping key for files: the first two directory levels", []colDesc{
		i32c("id"), txtc("name"), txtc("kind"), i32c("n_files"), i32c("n_symbols"),
		i32c("n_public"), i32c("sloc"), i32c("fan_in"), i32c("fan_out"),
		colDesc{"instability", "real", false, ""},
	}},
	{"files", "one row per discovered source file", nil},
	{"symbols", "the hub: every function, method, closure, hook and type", nil},
	{"params", "parameter list, keyed by symbol", []colDesc{
		i32c("symbol_id"), i32c("pos"), txtn("name"), txtc("type"), txtn("default_value"),
		i32c("is_optional"), i32c("is_variadic"), i32c("is_ref"), i32c("is_mutable"),
		i32c("is_nullable"), i32c("is_generic"), i32c("is_untyped"), i32c("type_depth"),
	}},
	{"fields", "declared class properties and constants", []colDesc{
		i32c("symbol_id"), i32c("ordinal"), txtc("name"), txtc("type"), txtc("visibility"),
		i32c("line"), i32c("is_static"), i32c("is_const"), i32c("is_mutable"),
		i32c("is_nullable"), i32c("is_collection"), i32c("is_untyped"), i32c("has_default"),
		i32c("type_depth"),
	}},
	{"locals", "declared but never written: the graph carries no local-variable inventory", []colDesc{
		i32c("symbol_id"), i32c("ordinal"), txtc("name"), txtc("type"), i32c("line"),
		i32c("is_const"), i32c("is_mutable"), i32c("is_untyped"), i32c("has_init"),
		i32c("in_loop"), i32c("scope_depth"),
	}},
	{"edges", "the call graph, one row per (caller, callee)", []colDesc{
		i32c("caller_id"), i32c("callee_id"), i32c("n_calls"), i32c("same_file"),
		i32c("same_module"), i32c("is_self"),
	}},
	{"callsites", "every distinct line a resolved call was seen on", []colDesc{
		i32c("caller_id"), i32c("callee_id"), i32c("line"),
	}},
	{"unresolved_calls", "a call we saw but could not point at a definition", []colDesc{
		i32c("caller_id"), txtc("name"), i32c("n"), i32c("first_line"),
	}},
	{"imports", "use statements and includes", nil},
	{"hazards", "dangerous call families, one row per (symbol, pattern)", []colDesc{
		i32c("symbol_id"), txtc("pattern"), txtc("category"), i32c("n"), i32c("first_line"),
	}},
	{"attributes", "PHP 8 attributes", nil},
	{"literals", "string and numeric literals inside a body", nil},
	{"enum_members", "declared but never written: enum cases live on the class row", []colDesc{
		i32c("symbol_id"), i32c("ordinal"), txtc("name"), txtn("value"), i32c("n_fields"),
	}},
	{"markers", "TODO/FIXME/HACK and friends", nil},
	{"classes", "class-shaped declarations: class, interface, trait, enum, anonymous", nil},
	{"traits", "trait declarations, and how many classes ingest them", nil},
	{"namespaces", "namespace declarations, one row per file namespace", nil},
	{"superglobal_reads", "each $_GET / $_POST / ... read, with its key", nil},
	{"sql_sites", "calls that look like SQL builders, and how the string was built", nil},
	{"secret_candidates", "credential-shaped string literals", nil},
	{"property_hooks", "PHP 8.4 property hooks: a field read that is really a call", nil},
	{"magic_methods", "the methods PHP invokes with no call site", nil},
	{"dynamic_sites", "variable variables, variable methods, dynamic new and include", nil},
}

func printSchema(out *output) {
	for _, t := range graphSchema {
		out.printf("table %s -- %s", t.name, t.note)
		if t.cols == nil {
			switch t.name {
			case "files":
				out.printf("  id int  path text  dir text  basename text  ext text")
				out.printf("  lang text  module_id int?  bytes int  lines int  sloc int")
				out.printf("  blank_lines int  comment_lines int  doc_lines int")
				out.printf("  max_line_len int  sha1 text  parsed int  is_test int")
				out.printf("  is_generated int  is_vendored int  n_parse_errors int")
				out.printf("  n_missing_nodes int  parse_ms real  n_symbols int")
				out.printf("  n_functions int  n_types int  n_imports int  total_cyclo int")
				out.printf("  max_cyclo int  total_risk int")
			case "symbols":
				for i := 0; i < len(symbolsColumns); i += 4 {
					end := i + 4
					if end > len(symbolsColumns) {
						end = len(symbolsColumns)
					}
					var parts []string
					for _, n := range symbolsColumns[i:end] {
						t := "int"
						if stringColumns[i] {
							t = "text"
						}
						switch n {
						case "module_id", "parent_id", "signature", "return_type":
							t += "?"
						}
						parts = append(parts, n+" "+t)
					}
					out.printf("  " + strings.Join(parts, "  "))
				}
			case "imports":
				out.printf("  id int  file_id int  target text  target_id int?  alias text?")
				out.printf("  kind text  line int  is_external int  is_relative int")
				out.printf("  is_wildcard int  is_type_only int  is_dynamic int  n_names int")
			case "attributes":
				out.printf("  id int  symbol_id int?  file_id int  name text  args text?  line int")
			case "literals":
				out.printf("  id int  symbol_id int?  file_id int  kind text  value text  line int  is_magic int")
			case "markers":
				out.printf("  id int  file_id int  symbol_id int?  kind text  line int  text text")
			case "namespaces":
				out.printf("  id int  file_id int  name text  line int  has_strict_types int  n_classes int")
			case "superglobal_reads":
				out.printf("  id int  symbol_id int?  file_id int  var text  key_ text  line int  in_loop int  is_psalm_tainted int")
			case "sql_sites":
				out.printf("  id int  symbol_id int?  file_id int  callee text  driver text")
				out.printf("  build_kind text  is_sanitized int  is_prepared int  has_superglobal int  in_loop int  line int  snippet text")
			case "secret_candidates":
				out.printf("  id int  symbol_id int?  file_id int  value text  line int")
			case "property_hooks":
				out.printf("  id int  symbol_id int?  class_id int?  file_id int  class_name text")
				out.printf("  property text  hook text  is_short int  is_virtual int  body_sloc int  n_calls int  line int")
			case "magic_methods":
				out.printf("  id int  symbol_id int?  class_id int?  file_id int  class_name text")
				out.printf("  method text  is_gadget int  body_sloc int  n_calls int  n_hazards int  line int")
			case "dynamic_sites":
				out.printf("  id int  symbol_id int?  file_id int  kind text  target text  in_loop int  line int")
			}
		} else {
			for _, c := range t.cols {
				out.printf("  %s %s", c.name, c.typ)
			}
		}
		out.raw("\n")
	}
	out.printf("no query layer: there is no expression language here. Every")
	out.printf("question is a loop over a slice, a lookup of a column, and a reduce.")
}

func report(g *graph, out *output) {
	bar := strings.Repeat("=", 78)
	dash := strings.Repeat("-", 78)
	out.raw("\n" + bar + "\nOVERVIEW\n" + dash + "\n")
	for _, k := range []string{"lang", "target", "parser", "root", "built_at"} {
		if v, ok := g.meta(k); ok && v != "" {
			out.printf(" %-14s %s", k, v)
		}
	}
	var nFiles, nParsed, sloc int
	for i := range g.fils {
		nFiles++
		if g.fils[i].parsed != 0 {
			nParsed++
			sloc += int(g.fils[i].sloc)
		}
	}
	out.printf(" %-14s %d catalogued, %d parsed, %d sloc", "files", nFiles, nParsed, sloc)
	kindCount := map[string]int{}
	for i := 0; i < g.sym.n; i++ {
		kindCount[g.sym.str(cKind, i)]++
	}
	var kinds []kvT
	for k, v := range kindCount {
		kinds = append(kinds, kvT{k, v})
	}
	sortKv(kinds)
	if len(kinds) > 12 {
		kinds = kinds[:12]
	}
	var parts []string
	for _, k := range kinds {
		parts = append(parts, k.k+"="+fmtInt(k.v))
	}
	out.printf(" %-14s %s", "symbols", strings.Join(parts, ", "))
	var nUnres int32
	for _, u := range g.unresolved {
		nUnres += u.n
	}
	out.printf(" %-14s %d edges, %d call sites, %d unresolved", "call graph",
		len(g.edges), len(g.callSites), nUnres)

	out.raw("\n" + bar + "\nHOW MUCH OF THIS TO TRUST\n" + dash + "\n")
	errFiles := 0
	for i := range g.fils {
		if g.fils[i].parseErrs > 0 {
			errFiles++
		}
	}
	var totCalls, unres int32
	for i := 0; i < g.sym.n; i++ {
		totCalls += g.sym.cols[cNCalls][i]
	}
	unres = nUnres
	if nParsed == 0 {
		out.raw(" NOTHING WAS PARSED. Every number below is zero because no file\n")
		out.raw(" was read, not because this repository is empty or clean.\n")
	}
	out.printf(" %-30s %d file(s)", "files with parse errors", errFiles)
	if totCalls > 0 {
		out.printf(" %-30s %d of %d call sites (%d%%)", "calls we could NOT resolve",
			unres, totCalls, 100*int(unres)/int(totCalls))
	} else {
		out.printf(" %-30s no calls were recorded at all -- this is the absence of", "call resolution")
		out.printf(" %-30s data, not a clean result", "")
	}
	out.raw(" A high unresolved share means the call-graph queries below see less\n")
	out.raw(" than they imply. `v_blindspot` lists exactly where.\n")

	sections := []struct {
		label string
		r     *result
	}{
		{"BIGGEST MODULES", reportModules(g)},
		{"HEAVIEST FUNCTIONS", reportHeaviest(g)},
		{"MOST DEPENDED ON", reportDepended(g)},
		{"MARKERS LEFT IN THE CODE", reportMarkers(g)},
	}
	for _, s := range sections {
		out.raw("\n" + bar + "\n" + s.label + "\n" + dash + "\n")
		s.r.render(out)
	}
}

func reportModules(g *graph) *result {
	r := &result{cols: []string{"name", "files", "sloc", "syms", "instab"}}
	idx := make([]int, len(g.mods))
	for i := range idx {
		idx[i] = i
	}
	idx = sortByKeys(idx, func(i int) int64 { return int64(g.mods[i].sloc) })
	for i, k := range idx {
		if i >= 12 {
			break
		}
		m := &g.mods[k]
		if m.nFiles == 0 {
			continue
		}
		r.rows = append(r.rows, []cell{cellS(g.sa.str(m.name)), cellI(int64(m.nFiles)), cellI(int64(m.sloc)),
			cellI(int64(m.nSymbols)), cellF(round2(m.instability))})
	}
	return r
}

func reportHeaviest(g *graph) *result {
	r := &result{cols: []string{"name", "sloc", "cyclo", "cog", "nest", "fan_in", "at"}}
	idx := fnSymbols(g)
	idx = sortByKeys(idx, func(i int) int64 { return int64(g.sym.cols[cCyclomatic][i]) })
	for i, s := range idx {
		if i >= 12 {
			break
		}
		r.rows = append(r.rows, []cell{
			cellS(g.sym.str(cName, s)), cellI(int64(g.sym.cols[cSloc][s])),
			cellI(int64(g.sym.cols[cCyclomatic][s])), cellI(int64(g.sym.cols[cCognitive][s])),
			cellI(int64(g.sym.cols[cMaxNesting][s])), cellI(int64(g.sym.cols[cFanIn][s])),
			cellS(g.at(s))})
	}
	return r
}

func reportDepended(g *graph) *result {
	r := &result{cols: []string{"name", "fan_in", "fan_out", "cyclo", "sloc", "at"}}
	idx := fnSymbols(g)
	idx = sortByKeys(idx, func(i int) int64 { return int64(g.sym.cols[cFanIn][i]) })
	for i, s := range idx {
		if i >= 12 {
			break
		}
		r.rows = append(r.rows, []cell{
			cellS(g.sym.str(cName, s)), cellI(int64(g.sym.cols[cFanIn][s])),
			cellI(int64(g.sym.cols[cFanOut][s])), cellI(int64(g.sym.cols[cCyclomatic][s])),
			cellI(int64(g.sym.cols[cSloc][s])), cellS(g.at(s))})
	}
	return r
}

func reportMarkers(g *graph) *result {
	r := &result{cols: []string{"kind", "n"}}
	cnt := map[string]int{}
	for i := range g.markers {
		cnt[g.sa.str(g.markers[i].kind)]++
	}
	var all []kvT
	for k, v := range cnt {
		all = append(all, kvT{k, v})
	}
	sortKv(all)
	for _, e := range all {
		r.rows = append(r.rows, []cell{cellS(e.k), cellI(int64(e.v))})
	}
	return r
}

func (g *graph) at(sym int) string {
	f := g.file(g.sym.cols[cFileID][sym])
	p := "?"
	if f != nil {
		p = g.sa.str(f.path)
	}
	return p + ":" + itoa(g.sym.cols[cLineStart][sym])
}

func fnSymbols(g *graph) []int {
	var out []int
	for i := 0; i < g.sym.n; i++ {
		switch g.sym.str(cKind, i) {
		case "function", "method", "constructor", "closure":
			out = append(out, i)
		}
	}
	return out
}

var roundScale = big.NewRat(100, 1)

func round2(f float64) float64 {
	if f != f {
		return f
	}
	r := new(big.Rat).SetFloat64(f)
	if r == nil {
		return f
	}
	r.Mul(r, roundScale)
	q, rem := new(big.Int).QuoRem(r.Num(), r.Denom(), new(big.Int))
	rem.Abs(rem)
	rem.Lsh(rem, 1)
	if rem.Cmp(r.Denom()) >= 0 {
		if r.Sign() < 0 {
			q.Sub(q, big.NewInt(1))
		} else {
			q.Add(q, big.NewInt(1))
		}
	}
	v, _ := new(big.Rat).SetFrac(q, big.NewInt(100)).Float64()
	return v
}

type kvT struct {
	k string
	v int
}

func sortKv(a []kvT) {
	insertionSortAny(a, func(x, y kvT) bool {
		if x.v != y.v {
			return x.v > y.v
		}
		return x.k < y.k
	})
}

func insertionSortAny[T any](a []T, less func(x, y T) bool) {
	if len(a) > sortInsertMax {
		slices.SortStableFunc(a, func(x, y T) int {
			if less(x, y) {
				return -1
			}
			if less(y, x) {
				return 1
			}
			return 0
		})
		return
	}
	for i := 1; i < len(a); i++ {
		v := a[i]
		j := i - 1
		for j >= 0 && less(v, a[j]) {
			a[j+1] = a[j]
			j--
		}
		a[j+1] = v
	}
}

func sortByKeys(idx []int, key func(int) int64) []int {
	type pair struct {
		i, k int64
	}
	ps := make([]pair, len(idx))
	for n, v := range idx {
		ps[n] = pair{int64(v), key(v)}
	}
	insertionSortAny(ps, func(a, b pair) bool { return a.k > b.k })
	out := make([]int, len(ps))
	for n, p := range ps {
		out[n] = int(p.i)
	}
	return out
}

var symbolsColumns = []string{
	"id", "file_id", "module_id", "parent_id", "name",
	"kind", "line_start", "n_lines", "return_type", "n_params",
	"n_optional_params", "is_public", "is_abstract", "is_override", "is_test",
	"is_deprecated", "is_entrypoint", "sloc", "cyclomatic", "cognitive",
	"max_nesting", "n_tokens", "n_operators", "n_operands", "n_distinct_operators",
	"n_distinct_operands", "halstead_volume", "maintainability", "n_loops", "n_try",
	"n_catch", "n_catch_broad", "n_catch_empty", "n_throw", "max_loop_depth",
	"call_in_loop", "io_in_loop", "regex_in_loop", "query_in_loop", "n_assign",
	"n_regex_lit", "n_null_check", "n_calls", "n_unresolved_calls", "fan_in",
	"fan_out", "n_callsites", "is_recursive", "n_hazards", "risk_score",
	"n_sql", "n_shell", "n_exec", "n_deserialize", "n_xss",
	"n_ldap", "n_header", "n_file", "n_callable", "n_crypto",
	"n_reflect", "n_io", "n_net", "n_transaction", "n_queue",
	"n_write", "n_massassign", "n_config", "n_superglobal_reads", "n_get",
	"n_post", "n_request", "n_cookie", "n_server", "n_files_super",
	"n_session", "n_globals", "n_psalm_tainted", "n_sql_calls", "n_sql_literal",
	"n_sql_interp", "n_sql_concat", "n_sql_format", "n_sql_prepared", "n_sql_sanitized",
	"n_escaped_output", "n_raw_echo", "n_dynamic_call", "n_variable_var", "n_dynamic_method",
	"n_dynamic_new", "n_dynamic_include", "n_eval", "n_loose_compare", "n_strict_compare",
	"n_error_suppress", "n_magic_method", "n_destruct", "n_wakeup", "n_tostring",
	"n_call_magic", "n_null_safe", "n_type_declarations", "n_untyped_params", "n_nullable_types",
	"n_union_types", "n_intersection_types", "has_strict_types", "n_static_calls", "n_extract_call",
	"n_weak_hash", "n_weak_random", "n_remote_fetch", "n_header_call", "n_session_call",
	"n_move_uploaded", "n_serialize_call", "n_xxe_parser", "n_dynamic_open", "n_log_call",
	"n_auth_call", "n_inarray_in_loop", "n_array_merge_in_loop", "n_count_in_loop", "n_preg_in_loop",
	"n_keycheck_in_loop", "n_elif", "n_external_calls", "class_name", "is_controller",
	"is_model", "n_dynamic_prop_write", "n_request_input", "n_facade_call", "n_debug_call",
	"n_inarray_loose", "n_cookie_lean", "n_preg_dynamic", "n_file_write_dyn", "n_cleartext_fetch",
	"n_session_write", "n_static_prop_write",
}

const (
	cID                 = 0
	cFileID             = 1
	cModuleID           = 2
	cParentID           = 3
	cName               = 4
	cKind               = 5
	cLineStart          = 6
	cNLines             = 7
	cReturnType         = 8
	cNParams            = 9
	cNOptionalParams    = 10
	cIsPublic           = 11
	cIsAbstract         = 12
	cIsOverride         = 13
	cIsTest             = 14
	cIsDeprecated       = 15
	cIsEntrypoint       = 16
	cSloc               = 17
	cCyclomatic         = 18
	cCognitive          = 19
	cMaxNesting         = 20
	cNTokens            = 21
	cNOperators         = 22
	cNOperands          = 23
	cNDistinctOperators = 24
	cNDistinctOperands  = 25
	cHalsteadVolume     = 26
	cMaintainability    = 27
	cNLoops             = 28
	cNTry               = 29
	cNCatch             = 30
	cNCatchBroad        = 31
	cNCatchEmpty        = 32
	cNThrow             = 33
	cMaxLoopDepth       = 34
	cCallInLoop         = 35
	cIOInLoop           = 36
	cRegexInLoop        = 37
	cQueryInLoop        = 38
	cNAssign            = 39
	cNRegexLit          = 40
	cNNullCheck         = 41
	cNCalls             = 42
	cNUnresolvedCalls   = 43
	cFanIn              = 44
	cFanOut             = 45
	cNCallsites         = 46
	cIsRecursive        = 47
	cNHazards           = 48
	cRiskScore          = 49
	cNSQL               = 50
	cNShell             = 51
	cNExec              = 52
	cNDeserialize       = 53
	cNXSS               = 54
	cNLDAP              = 55
	cNHeader            = 56
	cNFile              = 57
	cNCallable          = 58
	cNCrypto            = 59
	cNReflect           = 60
	cNIO                = 61
	cNNet               = 62
	cNTransaction       = 63
	cNQueue             = 64
	cNWrite             = 65
	cNMassassign        = 66
	cNConfig            = 67
	cNSuperglobalReads  = 68
	cNGet               = 69
	cNPost              = 70
	cNRequest           = 71
	cNCookie            = 72
	cNServer            = 73
	cNFilesSuper        = 74
	cNSession           = 75
	cNGlobals           = 76
	cNPsalmTainted      = 77
	cNSQLCalls          = 78
	cNSQLLiteral        = 79
	cNSQLInterp         = 80
	cNSQLConcat         = 81
	cNSQLFormat         = 82
	cNSQLPrepared       = 83
	cNSQLSanitized      = 84
	cNEscapedOutput     = 85
	cNRawEcho           = 86
	cNDynamicCall       = 87
	cNVariableVar       = 88
	cNDynamicMethod     = 89
	cNDynamicNew        = 90
	cNDynamicInclude    = 91
	cNEval              = 92
	cNLooseCompare      = 93
	cNStrictCompare     = 94
	cNErrorSuppress     = 95
	cNMagicMethod       = 96
	cNDestruct          = 97
	cNWakeup            = 98
	cNToString          = 99
	cNCallMagic         = 100
	cNNullSafe          = 101
	cNTypeDeclarations  = 102
	cNUntypedParams     = 103
	cNNullableTypes     = 104
	cNUnionTypes        = 105
	cNIntersectionTypes = 106
	cHasStrictTypes     = 107
	cNStaticCalls       = 108
	cNExtractCall       = 109
	cNWeakHash          = 110
	cNWeakRandom        = 111
	cNRemoteFetch       = 112
	cNHeaderCall        = 113
	cNSessionCall       = 114
	cNMoveUploaded      = 115
	cNSerializeCall     = 116
	cNXxeParser         = 117
	cNDynamicOpen       = 118
	cNLogCall           = 119
	cNAuthCall          = 120
	cNInarrayInLoop     = 121
	cNArrayMergeInLoop  = 122
	cNCountInLoop       = 123
	cNPregInLoop        = 124
	cNKeycheckInLoop    = 125
	cNElif              = 126
	cNExternalCalls     = 127
	cClassName          = 128
	cIsController       = 129
	cIsModel            = 130
	cNDynamicPropWrite  = 131
	cNRequestInput      = 132
	cNFacadeCall        = 133
	cNDebugCall         = 134
	cNInarrayLoose      = 135
	cNCookieLean        = 136
	cNPregDynamic       = 137
	cNFileWriteDyn      = 138
	cNCleartextFetch    = 139
	cNSessionWrite      = 140
	cNStaticPropWrite   = 141
)

var stringColumns = map[int]bool{
	cName:       true,
	cReturnType: true,
	cClassName:  true,
	cKind:       true,
}

type buildOpts struct {
	includeTests, includeGen, includeVend bool
	quiet                                 bool
	workers                               int
	keepTrees                             bool
}

func build(root string, g *graph, o buildOpts, out *output) int {
	t0 := time.Now()
	d := discover(root, g, o.includeTests, o.includeGen, o.includeVend, o.quiet, out)

	defer tuneGC(d.sourceBytes)()
	if !o.quiet {

		out.printf("  parser: tree-sitter %s + tree-sitter-php>=0.24 %s", tsRuntimeVersion, tsGrammarVersion)
		out.printf("  %d php files discovered in %.1fs", len(d.recs), time.Since(t0).Seconds())
	}
	t1 := time.Now()
	nErr := parseAll(g, d, o, out)
	if !o.quiet {
		out.printf("  %d symbols parsed in %.1fs%s", g.sym.n, time.Since(t1).Seconds(),
			suffixFailed(nErr))
		if len(d.recs) > 0 && g.sym.n == 0 {
			out.printf("  WARNING: %d file(s) were read and produced NO symbols. Every", len(d.recs))
			out.printf("           query below will be empty for that reason, not")
			out.printf("           because the code is clean. Check --report for parse errors.")
		}
	}
	if nErr > 0 && (nErr > len(d.recs)/100 || !o.quiet) {
		out.warnf("  WARNING: %d of %d file(s) FAILED to parse and contributed nothing.", nErr, len(d.recs))
		out.warnf("           Re-run with CODEGRAPH_DEBUG=1 for the tracebacks.")
	}
	for _, fid := range g.parseFailed {
		if f := g.file(fid); f != nil {
			f.parsed = 0
			f.parseErrs++
		}
	}
	t2 := time.Now()
	resolveCalls(g)
	if !o.quiet {
		out.printf("  call graph built in %.1fs", time.Since(t2).Seconds())
	}
	resolveImportTargets(g)
	readManifests(root, g, out)
	t3 := time.Now()
	materialize(g)
	if !o.quiet {
		out.printf("  aggregates materialized in %.1fs", time.Since(t3).Seconds())
	}

	t4 := time.Now()
	writeMeta(g, root, len(d.recs), nErr)
	g.adj = g.buildAdjacency()
	if !o.quiet {
		out.printf("  indexed in %.1fs", time.Since(t4).Seconds())
	}
	return len(d.recs)
}

func suffixFailed(n int) string {
	if n == 0 {
		return ""
	}
	return " (" + strconv.Itoa(n) + " file(s) failed)"
}

type cstBatch struct {
	idx int32
	rec fileRec
	src []byte
	cst []byte
	sum string
	err error
}

type fileRange struct{ start, end int }

type cstBundle struct {
	items   []cstBatch
	results []*fileResult
}

// cstBatchPlan sizes one CLI batch. Enough files that every worker gets a turn
// (amortising the per-process grammar load), capped by source bytes so a worker
// never holds an unbounded CST: output measures ~28x source on this corpus.
func cstBatchPlan(d *discovered, workers int) (int, int64) {
	n := len(d.recs)
	files := (n + workers - 1) / workers
	if files < 4 {
		files = 4
	}
	if files > 64 {
		files = 64
	}
	if files > n {
		files = n
	}
	budget := d.sourceBytes / int64(2*workers)
	if budget < 64<<10 {
		budget = 64 << 10
	}
	if budget > 512<<10 {
		budget = 512 << 10
	}
	return files, budget
}

func parseAll(g *graph, d *discovered, o buildOpts, out *output) int {
	n := len(d.recs)
	if n == 0 {
		return 0
	}
	workers := o.workers
	if workers < 1 {
		workers = defaultParseWorkers
	}
	if workers > n {
		workers = n
	}

	// Contiguous ranges, one CLI process each; each worker owns a contiguous
	// block of ranges and sends whole batches. Decoding stays in file order on
	// the consumer, so symbol ids are assigned exactly as before.
	batchFiles, batchBytes := cstBatchPlan(d, workers)
	ranges := make([]fileRange, 0, n/batchFiles+1)
	for s := 0; s < n; {
		e := s
		var b int64
		for e < n && e-s < batchFiles && (e == s || b+d.recs[e].size <= batchBytes) {
			b += d.recs[e].size
			e++
		}
		ranges = append(ranges, fileRange{s, e})
		s = e
	}
	nw := min(workers, len(ranges))
	chans := make([]chan cstBundle, nw)
	for i := range chans {
		chans[i] = make(chan cstBundle, 1)
	}
	for w := 0; w < nw; w++ {
		lo := w * len(ranges) / nw
		hi := (w + 1) * len(ranges) / nw
		go func(w, lo, hi int) {
			p := newCSTReader()
			defer p.free()
			pp := newPHPParser()
			pp.keepTrees = o.keepTrees
			defer pp.close()
			for ri := lo; ri < hi; ri++ {
				r := ranges[ri]
				items, ok := p.readBatch(d.recs, r.start, r.end)
				if !ok {
					items = make([]cstBatch, 0, r.end-r.start)
					for k := r.start; k < r.end; k++ {
						items = append(items, p.read(int32(k), d.recs[k]))
					}
				}
				// Decode on the producing goroutine: each parser owns its
				// scratch and every fileResult is independent, so the consumer
				// only has to merge in file order.
				results := make([]*fileResult, len(items))
				for i := range items {
					results[i] = pp.decodeFile(items[i])
				}
				chans[w] <- cstBundle{items: items, results: results}
			}
			close(chans[w])
		}(w, lo, hi)
	}

	if o.keepTrees {
		g.astTrees = make([][]tsRec, len(g.fils))
	}
	step := max(1, n/20)
	done := 0
	nErr := 0
	for w := 0; w < nw; w++ {
		for b := range chans[w] {
			for i, fr := range b.results {
				if fr == nil {
					nErr++
					g.parseFailed = append(g.parseFailed, d.recs[b.items[i].idx].id)
				} else {
					mergeFile(g, fr)
					if g.astTrees != nil && fr.fid >= 1 && int(fr.fid) <= len(g.astTrees) {
						g.astTrees[fr.fid-1] = fr.trees
						fr.trees = nil
					}
				}
				done++
				if !o.quiet && done%step == 0 {
					out.printf("  ... %d/%d files", done, n)
				}
			}
		}
	}

	g.sym.releaseIndex()
	return nErr
}

func mergeFile(g *graph, fr *fileResult) {

	if f := g.file(fr.fid); f != nil {
		f.parseErrs = int32(fr.parseErrs)
		f.missing = int32(fr.missing)
		if !g.sa.eq(f.sha1, fr.sum) {
			f.sha1 = g.sa.put(fr.sum)
		}
	}
	sbase := uint32(len(g.sa.buf))
	if len(fr.sa.buf) > 0 {
		g.sa.buf = append(g.sa.buf, fr.sa.buf...)
	}
	rb := func(s *cgasStr) { s.Off += sbase }
	base := int32(g.sym.n)
	if len(fr.syms) > 0 {
		g.sym.reserve(int(base) + len(fr.syms))
	}

	for li := range fr.syms {
		if fr.syms[li].vals[cParentID] >= 0 {
			fr.syms[li].vals[cParentID] += base
		}
	}
	for li := range fr.syms {
		gi := base + int32(li)
		for c := range nSymCols {
			g.sym.cols[c][gi] = fr.syms[li].vals[c]
		}
		g.sym.cols[cID][gi] = gi
		for k := range strSlots {
			g.sym.strs[k][gi] = g.sym.intern(fr.syms[li].strs[k])
		}
	}
	g.sym.n += len(fr.syms)

	for name, defs := range fr.byName {
		for i := range defs {
			defs[i].sid = base + defs[i].sid
		}
		if _, seen := g.byName[name]; !seen {

			g.byNameOrder = append(g.byNameOrder, name)
		}
		g.byName[name] = append(g.byName[name], defs...)
	}
	for k, v := range fr.byQual {
		g.byQual[k] = base + v
	}
	for k, v := range fr.extends {
		if _, ok := g.extends[k]; !ok {
			g.extends[k] = v
		}
	}
	for k, v := range fr.fnSid {
		g.fnSid[k] = base + v
	}
	if fr.strict {
		g.strict[fr.fid] = true
	}

	for i := range fr.params {
		fr.params[i].sym = base + fr.params[i].sym
	}
	for i := range fr.fields {
		fr.fields[i].sym = base + fr.fields[i].sym
	}
	for i := range fr.hazards {
		fr.hazards[i].sym = base + fr.hazards[i].sym
	}
	rebaseNullable := func(v *int32, isNull bool) {
		if !isNull {
			*v = base + *v
		}
	}
	for i := range fr.attributes {
		rebaseNullable(&fr.attributes[i].sym, fr.attributes[i].symNull)
	}
	for i := range fr.literals {
		rebaseNullable(&fr.literals[i].sym, fr.literals[i].symNull)
	}
	for i := range fr.magic {
		rebaseNullable(&fr.magic[i].sym, fr.magic[i].symNull)
		rebaseNullable(&fr.magic[i].classID, fr.magic[i].classIDNull)
	}
	for i := range fr.hooks {
		rebaseNullable(&fr.hooks[i].sym, fr.hooks[i].symNull)
		rebaseNullable(&fr.hooks[i].classID, fr.hooks[i].classIDNull)
	}
	for i := range fr.classes {
		fr.classes[i].sym = base + fr.classes[i].sym
	}
	for i := range fr.traits {
		fr.traits[i].sym = base + fr.traits[i].sym
	}
	for i := range fr.superglobals {
		rebaseNullable(&fr.superglobals[i].sym, fr.superglobals[i].symNull)
	}
	for i := range fr.sqlSites {
		rebaseNullable(&fr.sqlSites[i].sym, fr.sqlSites[i].symNull)
	}
	for i := range fr.secrets {
		rebaseNullable(&fr.secrets[i].sym, fr.secrets[i].symNull)
	}
	for i := range fr.dynSites {
		rebaseNullable(&fr.dynSites[i].sym, fr.dynSites[i].symNull)
	}
	for i := range fr.pend {
		fr.pend[i].sym = base + fr.pend[i].sym
	}

	for i := range fr.imports {
		fr.imports[i].id = int32(len(g.imports) + i + 1)
	}
	for i := range fr.params {
		rb(&fr.params[i].name)
		rb(&fr.params[i].typ)
		rb(&fr.params[i].def)
	}
	for i := range fr.fields {
		rb(&fr.fields[i].name)
		rb(&fr.fields[i].typ)
		rb(&fr.fields[i].vis)
	}
	for i := range fr.hazards {
		rb(&fr.hazards[i].pattern)
		rb(&fr.hazards[i].category)
	}
	for i := range fr.attributes {
		rb(&fr.attributes[i].name)
		rb(&fr.attributes[i].args)
	}
	for i := range fr.literals {
		rb(&fr.literals[i].kind)
		rb(&fr.literals[i].value)
	}
	for i := range fr.markers {
		rb(&fr.markers[i].kind)
		rb(&fr.markers[i].txt)
	}
	for i := range fr.magic {
		rb(&fr.magic[i].className)
		rb(&fr.magic[i].method)
	}
	for i := range fr.hooks {
		rb(&fr.hooks[i].className)
		rb(&fr.hooks[i].property)
		rb(&fr.hooks[i].hook)
	}
	for i := range fr.classes {
		rb(&fr.classes[i].name)
		rb(&fr.classes[i].fqn)
		rb(&fr.classes[i].ns)
		rb(&fr.classes[i].kind)
		rb(&fr.classes[i].ext)
		rb(&fr.classes[i].impl)
		rb(&fr.classes[i].traitList)
	}
	for i := range fr.traits {
		rb(&fr.traits[i].name)
		rb(&fr.traits[i].ns)
	}
	for i := range fr.imports {
		rb(&fr.imports[i].target)
		rb(&fr.imports[i].alias)
		rb(&fr.imports[i].kind)
	}
	for i := range fr.nsRows {
		rb(&fr.nsRows[i].name)
	}
	for i := range fr.superglobals {
		rb(&fr.superglobals[i].v)
		rb(&fr.superglobals[i].key)
	}
	for i := range fr.sqlSites {
		rb(&fr.sqlSites[i].callee)
		rb(&fr.sqlSites[i].driver)
		rb(&fr.sqlSites[i].buildKind)
		rb(&fr.sqlSites[i].snippet)
	}
	for i := range fr.secrets {
		rb(&fr.secrets[i].value)
	}
	for i := range fr.dynSites {
		rb(&fr.dynSites[i].kind)
		rb(&fr.dynSites[i].target)
	}
	for i := range fr.attributes {
		fr.attributes[i].id = int32(len(g.attributes) + i + 1)
	}
	for i := range fr.literals {
		fr.literals[i].id = int32(len(g.literals) + i + 1)
	}
	for i := range fr.markers {
		fr.markers[i].id = int32(len(g.markers) + i + 1)
	}
	for i := range fr.nsRows {
		fr.nsRows[i].id = int32(len(g.namespaces) + i + 1)
	}
	for i := range fr.superglobals {
		fr.superglobals[i].id = int32(len(g.superglobals) + i + 1)
	}
	for i := range fr.sqlSites {
		fr.sqlSites[i].id = int32(len(g.sqlSites) + i + 1)
	}
	for i := range fr.secrets {
		fr.secrets[i].id = int32(len(g.secrets) + i + 1)
	}
	for i := range fr.hooks {
		fr.hooks[i].id = int32(len(g.hooks) + i + 1)
	}
	for i := range fr.magic {
		fr.magic[i].id = int32(len(g.magic) + i + 1)
	}
	for i := range fr.dynSites {
		fr.dynSites[i].id = int32(len(g.dynSites) + i + 1)
	}

	g.params = append(g.params, fr.params...)
	g.fields = append(g.fields, fr.fields...)
	g.hazards = append(g.hazards, fr.hazards...)
	g.attributes = append(g.attributes, fr.attributes...)
	g.literals = append(g.literals, fr.literals...)
	g.markers = append(g.markers, fr.markers...)
	g.magic = append(g.magic, fr.magic...)
	g.hooks = append(g.hooks, fr.hooks...)
	g.classes = append(g.classes, fr.classes...)
	g.traits = append(g.traits, fr.traits...)
	g.imports = append(g.imports, fr.imports...)
	g.superglobals = append(g.superglobals, fr.superglobals...)
	g.sqlSites = append(g.sqlSites, fr.sqlSites...)
	g.secrets = append(g.secrets, fr.secrets...)
	g.dynSites = append(g.dynSites, fr.dynSites...)
	g.namespaces = append(g.namespaces, fr.nsRows...)
	g.pendCalls = append(g.pendCalls, fr.pend...)
}

type typeScopeKey struct{ typ, name string }
type fileScopeKey struct {
	fid  int32
	name string
}

type resCall struct {
	caller, callee, line int32
}

type unresCall struct {
	caller int32
	name   string
	line   int32
	seq    int32
}

func resolveCalls(g *graph) {
	unique := make(map[string]int32, len(g.byName))
	for name, defs := range g.byName {
		if len(defs) == 1 {
			unique[name] = defs[0].sid
		}
	}
	fileScope := make(map[fileScopeKey]int32, len(g.byName)*2)
	typeScope := make(map[typeScopeKey]int32, len(g.byName)*2)

	symLoc := make([]int64, g.sym.n)
	haveLoc := make([]bool, g.sym.n)
	for _, name := range g.byNameOrder {
		for _, d := range g.byName[name] {
			if !haveLoc[d.sid] {
				symLoc[d.sid] = int64(d.fid)<<32 | int64(uint32(d.mid))
				haveLoc[d.sid] = true
			}
			if d.typ != "" {
				k := typeScopeKey{d.typ, name}
				if _, ok := typeScope[k]; !ok {
					typeScope[k] = d.sid
				}
			}
			k := fileScopeKey{d.fid, name}
			if _, ok := fileScope[k]; !ok {
				fileScope[k] = d.sid
			}
		}
	}

	res := make([]resCall, 0, len(g.pendCalls))
	ext := make([]int32, g.sym.n)
	var unresRaw []unresCall
	var nRes, nExt, nUnres int32

	for seq, p := range g.pendCalls {
		name := normaliseCallee(p.name)
		if name == "" {
			continue
		}
		base := name
		if i := strings.LastIndexByte(base, '.'); i >= 0 {
			base = base[i+1:]
		}
		if i := strings.LastIndex(base, "::"); i >= 0 {
			base = base[i+2:]
		}
		target := int32(-1)
		if p.typ != "" {
			if v, ok := typeScope[typeScopeKey{p.typ, base}]; ok {
				target = v
			}
		}
		if target < 0 {
			if v, ok := g.byQual[name]; ok {
				target = v
			}
		}
		if target < 0 {
			if v, ok := fileScope[fileScopeKey{p.fid, base}]; ok {
				target = v
			}
		}
		if target < 0 {
			if v, ok := unique[base]; ok {
				target = v
			}
		}
		if target < 0 {
			if isExternal(name, base) {
				ext[p.sym]++
				nExt++
			} else {
				unresRaw = append(unresRaw, unresCall{caller: p.sym,
					name: clip(name, 160), line: p.line, seq: int32(seq)})
				nUnres++
			}
			continue
		}
		res = append(res, resCall{caller: p.sym, callee: target, line: p.line})
		nRes++
	}

	slices.SortFunc(res, func(a, b resCall) int {
		if a.caller != b.caller {
			return cmp.Compare(a.caller, b.caller)
		}
		return cmp.Compare(a.callee, b.callee)
	})
	g.edges = make([]edgeRow, 0, len(res)/2+8)
	for i := 0; i < len(res); {
		j := i + 1
		for j < len(res) && res[j].caller == res[i].caller && res[j].callee == res[i].callee {
			j++
		}
		e := edgeRow{caller: res[i].caller, callee: res[i].callee, nCalls: int32(j - i),
			isSelf: res[i].caller == res[i].callee}
		if t := res[i].callee; haveLoc[t] {
			e.sameFile = int32(symLoc[t]>>32) == g.sym.cols[cFileID][res[i].caller]
			e.sameModule = int32(symLoc[t]) == g.sym.cols[cModuleID][res[i].caller]
		}
		g.edges = append(g.edges, e)
		i = j
	}

	slices.SortFunc(res, func(a, b resCall) int {
		if a.caller != b.caller {
			return cmp.Compare(a.caller, b.caller)
		}
		if a.callee != b.callee {
			return cmp.Compare(a.callee, b.callee)
		}
		return cmp.Compare(a.line, b.line)
	})
	g.callSites = make([]callSiteRow, 0, len(res)/2+8)
	for i := 0; i < len(res); {
		if res[i].line == 0 {
			i++
			continue
		}
		j := i + 1
		for j < len(res) && res[j] == res[i] {
			j++
		}
		g.callSites = append(g.callSites, callSiteRow{res[i].caller, res[i].callee, res[i].line})
		i = j
	}

	slices.SortFunc(unresRaw, func(a, b unresCall) int {
		if a.caller != b.caller {
			return cmp.Compare(a.caller, b.caller)
		}
		if a.name != b.name {
			return strings.Compare(a.name, b.name)
		}
		return cmp.Compare(a.seq, b.seq)
	})
	g.unresolved = make([]unresolvedRow, 0, len(unresRaw))
	for i := 0; i < len(unresRaw); {
		j := i + 1
		for j < len(unresRaw) && unresRaw[j].caller == unresRaw[i].caller &&
			unresRaw[j].name == unresRaw[i].name {
			j++
		}
		g.unresolved = append(g.unresolved, unresolvedRow{caller: unresRaw[i].caller,
			name: g.sa.put(unresRaw[i].name), n: int32(j - i), firstLine: unresRaw[i].line})
		i = j
	}

	for sid, v := range ext {
		if v != 0 {
			g.sym.cols[cNExternalCalls][sid] = v
		}
	}
	g.resolvedN, g.externalN, g.unresolvedN = nRes, nExt, nUnres
	g.setMeta("calls_resolved", sprintf("%d in-tree / %d external / %d unresolved (%d%% of in-scope resolved)",
		nRes, nExt, nUnres, 100*int(nRes)/max(1, int(nRes+nUnres))))
	g.releaseResolveState()
}

func (g *graph) releaseResolveState() {
	g.pendCalls = nil
	g.byName = nil
	g.byNameOrder = nil
	g.byQual = nil
	g.extends = nil
	g.fnSid = nil
	g.strict = nil
}

func normaliseCallee(raw string) string {
	s := strings.TrimSpace(raw)
	switch {
	case strings.HasPrefix(s, "->"):
		return s[2:]
	case strings.HasPrefix(s, "new "):
		return strings.TrimLeft(s[4:], "\\") + "::__construct"
	}
	return strings.TrimLeft(s, "\\")
}

func isExternal(name, base string) bool {
	short := name
	if i := strings.LastIndexByte(short, '\\'); i >= 0 {
		short = short[i+1:]
	}
	if i := strings.Index(short, "::"); i >= 0 {
		return phpBuiltinClasses[short[:i]]
	}
	return phpBuiltins[short] || phpBuiltins[base]
}

type symTable struct {
	cols     [][]int32
	strs     [][]int32
	poolRefs []cgasStr
	sa       *strArena
	index    map[string]int32
	n        int
	grown    int

	wide []int64
}

func newSymTable(ncols int) *symTable {
	t := &symTable{cols: make([][]int32, ncols), strs: make([][]int32, len(strSlots)),
		index: make(map[string]int32, 4096)}
	t.reserve(4096)
	return t
}

func (t *symTable) reserve(n int) {
	if n <= t.grown {
		if int(n) > len(t.cols[0]) {
			for c := range t.cols {
				t.cols[c] = t.cols[c][:n]
			}
			for c := range t.strs {
				t.strs[c] = t.strs[c][:n]
			}
			t.wide = t.wide[:n]
		}
		return
	}
	grow := t.grown
	if grow == 0 {
		grow = 4096
	}

	for grow < n {
		grow += grow
	}
	for c := range t.cols {
		nc := make([]int32, n, grow)
		copy(nc, t.cols[c])
		t.cols[c] = nc
	}
	for c := range t.strs {
		ns := make([]int32, n, grow)
		copy(ns, t.strs[c])
		t.strs[c] = ns
	}
	nw := make([]int64, n, grow)
	copy(nw, t.wide)
	t.wide = nw
	t.grown = grow
}

func (t *symTable) getWide(i int) int64    { return t.wide[i] }
func (t *symTable) setWide(i int, v int64) { t.wide[i] = v }
func (t *symTable) str(c, i int) string    { return t.sa.str(t.poolRefs[t.strs[strSlot(c)][i]]) }
func (t *symTable) intern(s string) int32 {
	if v, ok := t.index[s]; ok {
		return v
	}
	v := int32(len(t.poolRefs))
	t.poolRefs = append(t.poolRefs, t.sa.put(s))
	t.index[s] = v
	return v
}

func (t *symTable) releaseIndex() { t.index = nil }

type moduleRow struct {
	id               int32
	name, kind       cgasStr
	nFiles, nSymbols int32
	nPublic, sloc    int32
	fanIn, fanOut    int32
	padM             uint32
	instability      float64
}

type fileRow struct {
	id                                 int32
	path, dir, base, ext, lang         cgasStr
	moduleID                           int32
	bytes, lines, sloc, blank, comment int32
	docLines                           int32
	maxLine                            int32
	sha1                               cgasStr
	parsed, isTest, isGen, isVend      int32
	parseErrs, missing                 int32
	padF                               uint32
	parseMS                            float64
	nSymbols, nFns, nTypes, nImports   int32
	totalCyclo, maxCyclo, totalRisk    int32
	padT                               uint32
}

type paramRow struct {
	sym                           int32
	pos                           int32
	name, typ                     cgasStr
	def                           cgasStr
	hasDef                        bool
	opt, variadic, ref, mut, null bool
	padP                          uint16
	untyped, typeDepth            int32
}

type fieldRow struct {
	sym                    int32
	ordinal                int32
	name, typ, vis         cgasStr
	line                   int32
	isStatic, isConst, mut bool
	null, coll, untyped    bool
	padE                   uint16
	typeDepth              int32
}

type importRow struct {
	id                      int32
	fileID                  int32
	target, alias, kind     cgasStr
	targetID                int32
	aliasNull, targetIDNull bool
	padI                    [2]uint8
	line                    int32
	ext, rel, wild, dynamic bool
	nNames                  int32
}

type hazardRow struct {
	sym               int32
	pattern, category cgasStr
	n, firstLine      int32
}

type attributeRow struct {
	id         int32
	sym        int32
	symNull    bool
	padA       [3]uint8
	fileID     int32
	name, args cgasStr
	argsNull   bool
	padB       [3]uint8
	line       int32
}

type literalRow struct {
	id      int32
	sym     int32
	symNull bool
	padL    [3]uint8
	fileID  int32
	kind    cgasStr
	value   cgasStr
	line    int32
	isMagic bool
	padZ    [2]uint8
}

type markerRow struct {
	id      int32
	fileID  int32
	sym     int32
	symNull bool
	padK    [3]uint8
	kind    cgasStr
	txt     cgasStr
	line    int32
}

type classRow struct {
	sym, fileID                        int32
	name, fqn, ns, kind                cgasStr
	ext, impl, traitList               cgasStr
	nTraits, nMethods, nPub, nStatic   int32
	nProps, nPromoted, nHooks, nConsts int32
	nCases, nMagic                     int32
	isAbstract, isFinal, isReadonly    bool
	isAnon                             bool
	hasDestruct, hasWakeup, hasToStr   bool
	hasCall, hasCallStatic, hasGet     bool
	hasInvoke                          bool
	padC                               uint8
	line                               int32
}

type traitRow struct {
	sym, fileID                 int32
	name, ns                    cgasStr
	nMethods, nAbstract, nProps int32
	usedBy                      int32
	line                        int32
}

type nsRow struct {
	id, fileID int32
	name       cgasStr
	line       int32
	strict     bool
	padN       [3]uint8
	nClasses   int32
}

type superReadRow struct {
	id, sym int32
	symNull bool
	padS    [3]uint8
	fileID  int32
	v, key  cgasStr
	line    int32
	inLoop  bool
	psalm   bool
	padR    uint8
}

type sqlSiteRow struct {
	id, sym                   int32
	symNull                   bool
	padQ                      [3]uint8
	fileID                    int32
	callee, driver, buildKind cgasStr
	snippet                   cgasStr
	sanitized, prepared       bool
	hasSuper, inLoop          bool
	line                      int32
}

type secretRow struct {
	id, sym int32
	symNull bool
	padX    [3]uint8
	fileID  int32
	value   cgasStr
	line    int32
}

type hookRow struct {
	id, sym, classID     int32
	symNull, classIDNull bool
	padH                 uint16
	fileID               int32
	className, property  cgasStr
	hook                 cgasStr
	isShort, isVirtual   bool
	padJ                 uint16
	bodySLOC, nCalls     int32
	line                 int32
}

type magicRow struct {
	id, sym, classID     int32
	symNull, classIDNull bool
	padG                 uint16
	fileID               int32
	className, method    cgasStr
	isGadget             bool
	padU                 [3]uint8
	bodySLOC, nCalls     int32
	nHazards             int32
	line                 int32
}

type dynSiteRow struct {
	id, sym      int32
	symNull      bool
	padD         [3]uint8
	fileID       int32
	kind, target cgasStr
	inLoop       bool
	padY         [3]uint8
	line         int32
}

type edgeRow struct {
	caller, callee       int32
	nCalls               int32
	sameFile, sameModule bool
	isSelf               bool
	padW                 uint8
}

type callSiteRow struct{ caller, callee, line int32 }

type unresolvedRow struct {
	caller    int32
	name      cgasStr
	n         int32
	firstLine int32
}

type nsSpan struct {
	start int32
	name  string

	fallback bool
}

type graph struct {
	sym  *symTable
	sa   strArena
	mods []moduleRow
	fils []fileRow

	params       []paramRow
	fields       []fieldRow
	imports      []importRow
	hazards      []hazardRow
	attributes   []attributeRow
	literals     []literalRow
	markers      []markerRow
	classes      []classRow
	traits       []traitRow
	namespaces   []nsRow
	superglobals []superReadRow
	sqlSites     []sqlSiteRow
	secrets      []secretRow
	hooks        []hookRow
	magic        []magicRow
	dynSites     []dynSiteRow

	edges      []edgeRow
	callSites  []callSiteRow
	unresolved []unresolvedRow

	metaKeys []string
	metaVals []string

	byName      map[string][]localSym
	byNameOrder []string
	byQual      map[string]int32
	strict      map[int32]bool

	extends map[string]string

	fnSid map[uint64]int32

	adj       *adjacency
	pendCalls []pendRec

	astTrees [][]tsRec
	astBlob  []byte

	resolvedN, externalN, unresolvedN int32
	parseFailed                       []int32
}

func newGraph() *graph {
	g := &graph{
		sym:     newSymTable(len(symbolsColumns)),
		byName:  make(map[string][]localSym),
		byQual:  make(map[string]int32),
		strict:  make(map[int32]bool),
		extends: make(map[string]string),
		fnSid:   make(map[uint64]int32),
	}
	g.sym.sa = &g.sa
	return g
}

func (g *graph) setMeta(k, v string) {
	for i, kk := range g.metaKeys {
		if kk == k {
			g.metaVals[i] = v
			return
		}
	}
	g.metaKeys = append(g.metaKeys, k)
	g.metaVals = append(g.metaVals, v)
}

func (g *graph) meta(k string) (string, bool) {
	for i, kk := range g.metaKeys {
		if kk == k {
			return g.metaVals[i], true
		}
	}
	return "", false
}

func (g *graph) moduleName(id int32) string {
	if m := g.modByID(id); m != nil {
		return g.sa.str(m.name)
	}
	return ""
}

func (g *graph) modByID(id int32) *moduleRow {
	if id < 1 || int(id) > len(g.mods) {
		return nil
	}
	return &g.mods[id-1]
}

func (g *graph) file(id int32) *fileRow {
	if id < 1 || int(id) > len(g.fils) {
		return nil
	}
	return &g.fils[id-1]
}

func (g *graph) fileIsTest(id int32) bool {
	f := g.file(id)
	return f != nil && f.isTest != 0
}

type adjacency struct {
	outOff, outTo []int32
	inOff, inTo   []int32
}

func (g *graph) buildAdjacency() *adjacency {
	n := g.sym.n
	a := &adjacency{
		outOff: make([]int32, n+1),
		inOff:  make([]int32, n+1),
	}
	for i := range g.edges {
		if g.edges[i].isSelf {
			continue
		}
		a.outOff[g.edges[i].caller+1]++
		a.inOff[g.edges[i].callee+1]++
	}
	for i := range n {
		a.outOff[i+1] += a.outOff[i]
		a.inOff[i+1] += a.inOff[i]
	}
	a.outTo = make([]int32, a.outOff[n])
	a.inTo = make([]int32, a.inOff[n])
	co := make([]int32, n)
	ci := make([]int32, n)
	copy(co, a.outOff[:n])
	copy(ci, a.inOff[:n])
	for i := range g.edges {
		if g.edges[i].isSelf {
			continue
		}
		e := &g.edges[i]
		a.outTo[co[e.caller]] = e.callee
		co[e.caller]++
		a.inTo[ci[e.callee]] = e.caller
		ci[e.callee]++
	}
	return a
}

type reachTable struct {
	depth  []int32
	keys   []uint64
	bySeed map[int32][]int32
	all    []int32
}

func (g *graph) reachable(seeds []int32, depth int, adj *adjacency) *reachTable {
	rt := &reachTable{bySeed: make(map[int32][]int32, len(seeds))}
	visited := make([]int32, g.sym.n)
	stamp := int32(0)
	allSeen := make([]int32, g.sym.n)
	allStamp := int32(0)
	for _, s := range seeds {
		if int(s) >= g.sym.n {
			continue
		}
		stamp++
		rt.keys = append(rt.keys, uint64(s)<<32|uint64(s))
		rt.depth = append(rt.depth, 0)
		rt.bySeed[s] = []int32{s}
		allStamp++
		allSeen[s] = allStamp
		rt.all = append(rt.all, s)
		visited[s] = stamp
		frontier := []int32{s}
		for d := 1; d <= depth && len(frontier) > 0; d++ {
			var next []int32
			for _, u := range frontier {
				for k := adj.outOff[u]; k < adj.outOff[u+1]; k++ {
					v := adj.outTo[k]
					if visited[v] == stamp {
						continue
					}
					visited[v] = stamp
					rt.keys = append(rt.keys, uint64(s)<<32|uint64(v))
					rt.depth = append(rt.depth, int32(d))
					rt.bySeed[s] = append(rt.bySeed[s], v)
					if allSeen[v] != allStamp {
						allSeen[v] = allStamp
						rt.all = append(rt.all, v)
					}
					next = append(next, v)
				}
			}
			frontier = next
		}
	}
	rt.sortKeys()
	return rt
}

func (rt *reachTable) sortKeys() {
	idx := make([]int32, len(rt.keys))
	for i := range idx {
		idx[i] = int32(i)
	}
	sort.Slice(idx, func(a, b int) bool { return rt.keys[idx[a]] < rt.keys[idx[b]] })
	k2 := make([]uint64, len(idx))
	d2 := make([]int32, len(idx))
	for i, j := range idx {
		k2[i], d2[i] = rt.keys[j], rt.depth[j]
	}
	rt.keys, rt.depth = k2, d2
}

func itoa(v int32) string { return strconv.FormatInt(int64(v), 10) }

func sqlLike(s, pat string) bool {
	if pat == "%" {
		return true
	}
	sr, pr := []rune(s), []rune(pat)
	var match func(si, pi int) bool
	match = func(si, pi int) bool {
		for pi < len(pr) {
			switch pr[pi] {
			case '%':
				pi++
				if pi == len(pr) {
					return true
				}
				for k := si; k <= len(sr); k++ {
					if match(k, pi) {
						return true
					}
				}
				return false
			case '_':
				if si >= len(sr) {
					return false
				}
				si++
				pi++
			default:
				if si >= len(sr) || sr[si] != pr[pi] {
					return false
				}
				si++
				pi++
			}
		}
		return si == len(sr)
	}
	return match(0, 0)
}

func materialize(g *graph) {
	n := g.sym.n
	fanOut := make([]int32, n)
	fanIn := make([]int32, n)
	callsites := make([]int32, n)
	isRec := make([]bool, n)
	for i := range g.edges {
		e := &g.edges[i]
		if e.isSelf {
			isRec[e.caller] = true
			continue
		}
		fanOut[e.caller]++
		fanIn[e.callee]++
	}
	for _, c := range g.callSites {
		callsites[c.callee]++
	}
	for i := range n {
		g.sym.cols[cFanOut][i] = fanOut[i]
		g.sym.cols[cFanIn][i] = fanIn[i]
		g.sym.cols[cNCallsites][i] = callsites[i]
		if isRec[i] {
			g.sym.cols[cIsRecursive][i] = 1
		}
	}

	unresolved := make([]int32, n)
	for _, u := range g.unresolved {
		unresolved[u.caller] += u.n
	}

	hazTot := make([]int32, n)
	ncat := len(hazardCategories)
	hazCat := make([]int32, n*ncat)
	for _, h := range g.hazards {
		hazTot[h.sym] += h.n
		if ci, ok := hazardCatIdx[g.sa.str(h.category)]; ok {
			hazCat[int(h.sym)*ncat+ci] += h.n
		}
	}
	for i := range n {
		g.sym.cols[cNUnresolvedCalls][i] = unresolved[i]
		g.sym.cols[cNHazards][i] = hazTot[i]
		for ci, col := range hazardCatCols {
			if col >= 0 {
				g.sym.cols[col][i] = hazCat[i*ncat+ci]
			}
		}
	}

	sgTotal := make([]int32, n)
	sgPsalm := make([]int32, n)
	sgHas := make([]bool, n)

	sgCols := make([][]int32, 8)
	sgColHas := make([][]bool, 7)
	for i := range sgCols {
		sgCols[i] = make([]int32, n)
	}
	for i := range sgColHas {
		sgColHas[i] = make([]bool, n)
	}
	for _, r := range g.superglobals {
		if r.symNull {
			continue
		}
		sgTotal[r.sym]++
		sgHas[r.sym] = true
		if r.psalm {
			sgPsalm[r.sym]++
		}
		if ci, ok := superglobalColIdx[g.sa.str(r.v)]; ok {
			sgCols[ci][r.sym]++
			if ci < 7 {
				sgColHas[ci][r.sym] = true
			}
		}
	}
	for i := range n {
		if !sgHas[i] {
			continue
		}
		g.sym.cols[cNSuperglobalReads][i] = sgTotal[i]
		g.sym.cols[cNPsalmTainted][i] = sgPsalm[i]
	}
	for ci, col := range []int{cNGet, cNPost, cNRequest, cNCookie, cNServer,
		cNFilesSuper, cNSession} {
		for i := range n {
			if sgColHas[ci][i] {
				g.sym.cols[col][i] = sgCols[ci][i]
			}
		}
	}

	sqTotal := make([]int32, n)
	sqHas := make([]bool, n)
	sq := make([][]int32, 6)
	for i := range sq {
		sq[i] = make([]int32, n)
	}
	for _, s := range g.sqlSites {
		if s.symNull {
			continue
		}
		sqTotal[s.sym]++
		sqHas[s.sym] = true
		ci := -1
		switch g.sa.str(s.buildKind) {
		case "literal":
			ci = 0
		case "interp":
			ci = 1
		case "concat":
			ci = 2
		case "format":
			ci = 3
		}
		if ci >= 0 {
			sq[ci][s.sym]++
		}
		if s.prepared {
			sq[4][s.sym]++
		}
		if s.sanitized {
			sq[5][s.sym]++
		}
	}
	for i := range n {
		if !sqHas[i] {
			continue
		}
		g.sym.cols[cNSQLCalls][i] = sqTotal[i]

		for ci, col := range []int{cNSQLLiteral, cNSQLInterp, cNSQLConcat,
			cNSQLFormat, cNSQLPrepared, cNSQLSanitized} {
			g.sym.cols[col][i] = sq[ci][i]
		}
	}

	dyTotal := make([]int32, n)
	dyHas := make([]bool, n)

	dyCols := make([][]int32, 5)
	dyHasCol := make([][]bool, 5)
	for i := range dyCols {
		dyCols[i] = make([]int32, n)
		dyHasCol[i] = make([]bool, n)
	}
	for _, d := range g.dynSites {
		if d.symNull {
			continue
		}
		dyTotal[d.sym]++
		dyHas[d.sym] = true
		switch g.sa.str(d.kind) {
		case "variable_method":
			dyCols[0][d.sym]++
			dyHasCol[0][d.sym] = true
		case "variable_class":
			dyCols[1][d.sym]++
			dyHasCol[1][d.sym] = true
		case "variable_include":
			dyCols[2][d.sym]++
			dyHasCol[2][d.sym] = true
		case "eval":
			dyCols[3][d.sym]++
			dyHasCol[3][d.sym] = true
		}
	}
	for i := range n {
		if !dyHas[i] {
			continue
		}
		g.sym.cols[cNDynamicCall][i] = dyTotal[i]
		for ci, col := range []int{cNDynamicMethod, cNDynamicNew,
			cNDynamicInclude, cNEval} {
			if dyHasCol[ci][i] {
				g.sym.cols[col][i] = dyCols[ci][i]
			}
		}
	}

	for i := range g.magic {
		if g.magic[i].symNull {
			continue
		}
		s := g.magic[i].sym
		g.magic[i].nCalls = g.sym.cols[cNCalls][s]
		g.magic[i].nHazards = g.sym.cols[cNHazards][s]
	}
	for i := range g.hooks {
		if g.hooks[i].symNull {
			continue
		}
		g.hooks[i].nCalls = g.sym.cols[cNCalls][g.hooks[i].sym]
	}

	for i := range g.traits {
		needle := "," + g.sa.str(g.traits[i].name) + ","
		var c int32
		for j := range g.classes {
			tl := g.sa.str(g.classes[j].traitList)
			if tl == "" {
				continue
			}
			if strings.Contains(","+tl+",", needle) {
				c++
			}
		}
		g.traits[i].usedBy = c
	}
	nsClass := make(map[string]int32)
	for i := range g.classes {
		nsClass[g.sa.str(g.classes[i].ns)]++
	}
	for i := range g.namespaces {
		g.namespaces[i].nClasses = nsClass[g.sa.str(g.namespaces[i].name)]
	}

	fsymN := make([]int32, len(g.fils))
	ffn := make([]int32, len(g.fils))
	ftype := make([]int32, len(g.fils))
	fcyc := make([]int32, len(g.fils))
	fmaxc := make([]int32, len(g.fils))
	frisk := make([]int32, len(g.fils))
	impPerFile := make([]int32, len(g.fils))
	for i := range n {
		fi := int(g.sym.cols[cFileID][i]) - 1
		if fi < 0 || fi >= len(g.fils) {
			continue
		}
		fsymN[fi]++
		switch g.sym.str(cKind, i) {
		case "function", "method", "constructor", "closure":
			ffn[fi]++
		case "class", "struct", "interface", "trait", "enum", "union", "record",
			"protocol", "type", "impl":
			ftype[fi]++
		}
		cy := g.sym.cols[cCyclomatic][i]
		fcyc[fi] += cy
		if cy > fmaxc[fi] {
			fmaxc[fi] = cy
		}
		frisk[fi] += g.sym.cols[cRiskScore][i]
	}
	for i := range g.imports {
		if fi := int(g.imports[i].fileID) - 1; fi >= 0 && fi < len(impPerFile) {
			impPerFile[fi]++
		}
	}
	for i := range g.fils {
		f := &g.fils[i]
		f.nSymbols, f.nFns, f.nTypes = fsymN[i], ffn[i], ftype[i]
		f.totalCyclo, f.maxCyclo, f.totalRisk = fcyc[i], fmaxc[i], frisk[i]
		f.nImports = impPerFile[i]
	}

	for i := range n {
		ops := g.sym.cols[cNOperators][i]
		oper := g.sym.cols[cNOperands][i]
		dOps := g.sym.cols[cNDistinctOperators][i]
		dOper := g.sym.cols[cNDistinctOperands][i]
		if g.sym.cols[cNTokens][i] > 0 {
			d := dOps + dOper
			var f float64
			if d > 1 {
				f = float64(d)
			} else {
				f = 2.0
			}

			g.sym.setWide(i, int64(ops+oper)*int64(f))
		}
		switch g.sym.str(cKind, i) {
		case "function", "method", "constructor", "closure":
			sl := g.sym.cols[cSloc][i]
			mi := int(roundedMI(g.sym.cols[cCyclomatic][i], sl))
			if mi < 0 {
				mi = 0
			}
			g.sym.cols[cMaintainability][i] = int32(mi)
		}
		g.sym.cols[cRiskScore][i] = riskScore(g, i)
	}

	nmod := len(g.mods) + 1
	msym := make([]int32, nmod)
	mpub := make([]int32, nmod)
	for i := range n {
		mi := g.sym.cols[cModuleID][i]
		if mi < 1 || int(mi) >= nmod {
			continue
		}
		msym[mi]++
		mpub[mi] += g.sym.cols[cIsPublic][i]
	}
	mfile := make([]int32, nmod)
	msloc := make([]int32, nmod)
	for i := range g.fils {
		mi := g.fils[i].moduleID
		if mi >= 1 && int(mi) < nmod {
			mfile[mi]++
			msloc[mi] += g.fils[i].sloc
		}
	}

	modSet := make(map[int64]bool)
	for i := range g.edges {
		e := &g.edges[i]
		if e.isSelf {
			continue
		}
		m1 := g.sym.cols[cModuleID][e.caller]
		m2 := g.sym.cols[cModuleID][e.callee]
		if m1 < 1 || m2 < 1 || m1 == m2 || int(m1) >= nmod || int(m2) >= nmod {
			continue
		}
		modSet[int64(m1)<<32|int64(m2)] = true
	}
	mFanOut := make([]int32, nmod)
	mFanIn := make([]int32, nmod)
	for k := range modSet {
		mFanOut[int32(k>>32)]++
		mFanIn[int32(uint32(k))]++
	}
	for i := range g.mods {
		id := int32(i + 1)
		g.mods[i].nSymbols, g.mods[i].nPublic = msym[id], mpub[id]
		g.mods[i].nFiles, g.mods[i].sloc = mfile[id], msloc[id]
		g.mods[i].fanOut, g.mods[i].fanIn = mFanOut[id], mFanIn[id]
		if tot := g.mods[i].fanIn + g.mods[i].fanOut; tot != 0 {
			g.mods[i].instability = float64(g.mods[i].fanOut) / float64(tot)
		}
	}
}

var hazardCategories = []string{
	"sql", "shell", "exec", "include", "deserialize", "xss", "ldap", "header",
	"file", "callable", "superglobal", "crypto", "reflect", "io", "net",
	"resource", "transaction", "queue", "write", "massassign", "config",
}

var hazardCatIdx = func() map[string]int {
	m := make(map[string]int, len(hazardCategories))
	for i, c := range hazardCategories {
		m[c] = i
	}
	return m
}()

var hazardCatCols = func() []int {
	cols := make([]int, len(hazardCategories))
	for i, c := range hazardCategories {
		if v, ok := colNameToIdx["n_"+c]; ok {
			cols[i] = v
		} else {
			cols[i] = -1
		}
	}
	return cols
}()

var superglobalColIdx = map[string]int{
	"$_GET": 0, "$_POST": 1, "$_REQUEST": 2, "$_COOKIE": 3, "$_SERVER": 4,
	"$_FILES": 5, "$_SESSION": 6, "$GLOBALS": 7, "$_ENV": 4,
}

func fmul(a, b float64) float64 { return a * b }

func fsub(a, b float64) float64 { return a - b }

func roundedMI(cyclomatic, sloc int32) float64 {
	term := 0.05
	if sloc > 1 {
		term = float64(sloc) / 20.0
	}
	return fsub(fsub(171.0, fmul(0.23, float64(cyclomatic))), fmul(16.2, term))
}

func riskScore(g *graph, i int) int32 {
	s := g.sym.cols
	v := s[cCyclomatic][i]*2 + s[cCognitive][i] + s[cMaxNesting][i]*4
	v += s[cNSQLInterp][i] * 30
	v += s[cNSQLConcat][i] * 22
	v += s[cNSQLFormat][i] * 14
	v += s[cNEval][i] * 35
	v += s[cNShell][i] * 25
	v += s[cNExec][i] * 20
	v += s[cNDynamicInclude][i] * 28
	v += s[cNDeserialize][i] * 20
	v += s[cNRawEcho][i] * 7
	v += s[cNLDAP][i] * 10
	v += s[cNVariableVar][i] * 10
	v += s[cNDynamicNew][i] * 6
	v += s[cNDynamicMethod][i] * 6
	v += s[cNDynamicCall][i] * 3
	v += s[cNSuperglobalReads][i] * 3
	v += s[cNPsalmTainted][i] * 2
	v += s[cNLooseCompare][i] * 2
	v += s[cNErrorSuppress][i] * 5
	v += s[cNGlobals][i] * 3
	v += s[cNCrypto][i] * 3
	v += s[cNReflect][i] * 2
	v += s[cNCallable][i] * 2
	v += s[cQueryInLoop][i] * 15
	v += s[cCallInLoop][i] * 2
	if s[cHasStrictTypes][i] == 0 {
		v += 6
	}
	if s[cIsRecursive][i] != 0 {
		v += 8
	}
	v -= s[cNEscapedOutput][i] * 2
	v -= s[cNSQLPrepared][i] * 4
	return v
}

var importSuffixes = []string{"", ".php", ".inc", ".module", ".phtml"}

func resolveImportTargets(g *graph) {
	byPath := make(map[string]int32, len(g.fils)*2)
	for i := range g.fils {
		norm := strings.ReplaceAll(g.sa.str(g.fils[i].path), string(os.PathSeparator), "/")
		byPath[norm] = g.fils[i].id
		if j := strings.LastIndexByte(norm, '.'); j > 0 {
			if _, ok := byPath[norm[:j]]; !ok {
				byPath[norm[:j]] = g.fils[i].id
			}
		}
	}
	look := func(cand string) int32 {
		cand = strings.Trim(cand, "/")
		if cand == "" {
			return -1
		}
		for _, suf := range importSuffixes {
			if v, ok := byPath[cand+suf]; ok {
				return v
			}
		}
		return -1
	}
	n := 0
	for i := range g.imports {
		imp := &g.imports[i]
		if !imp.targetIDNull || imp.target.Len == 0 {
			continue
		}
		t := strings.TrimSpace(strings.ReplaceAll(g.sa.str(imp.target), string(os.PathSeparator), "/"))
		hereDir := "."
		if f := g.file(imp.fileID); f != nil {
			hereDir = dirOrDot(g.sa.str(f.path))
		}
		var hit int32
		if strings.HasPrefix(t, ".") {

			nUp := 0
			for nUp < len(t) && t[nUp] == '.' {
				nUp++
			}
			rest := t[nUp:]
			if !strings.Contains(t, "/") {
				rest = strings.ReplaceAll(rest, ".", "/")
			} else {
				rest = strings.TrimLeft(t, "./")
			}
			base := hereDir
			for k := 0; k < max(0, nUp-1); k++ {
				base = filepath.Dir(base)
			}
			if base != "" && base != "." {
				hit = look(base + "/" + rest)
			} else {
				hit = look(rest)
			}
		} else {
			hit = look(strings.ReplaceAll(t, ".", "/"))
			if hit < 0 {
				hit = look(hereDir + "/" + t)
			}
		}
		if hit >= 0 && hit != imp.fileID {
			imp.targetID = hit
			imp.targetIDNull = false
			n++
		}
	}
	g.setMeta("imports_resolved", sprintf("%d of %d import rows point at a file in this tree",
		n, len(g.imports)))
}

const grammarNote = "tree-sitter-php 0.24.1 rejects exactly three of PHP 8.5's " +
	"additions: the (void) cast (1 ERROR node), clone(x, [...]) in some spellings " +
	"(3), and `final` on a promoted constructor property (1). Every " +
	"other construct in a 23-case 8.0-8.5 sweep parses clean -- " +
	"property hooks, private(set), DNF types, enums, #[Attr], ?->, " +
	"match, named args, heredoc/nowdoc, group use, first-class " +
	"callables, and 8.5's |> pipe. So a file with a handful of parse " +
	"errors and no other symptom is a grammar one version behind the " +
	"language, not a broken file. Read n_parse_errors that way."

func readManifests(root string, g *graph, out *output) {
	g.setMeta("grammar_note", grammarNote)
	b, err := os.ReadFile(filepath.Join(root, "composer.json"))
	if err != nil {
		return
	}
	j := simpleJSONObject(b)
	if j == nil {
		return
	}
	phpVersion := j.str("require", "php")
	psr4 := j.obj("autoload", "psr-4")
	var roots []string
	if psr4 != nil {
		for k := range psr4.m {
			roots = append(roots, k)
		}
	}
	sort.Strings(roots)
	joined := clip(strings.Join(roots, ", "), 400)
	if joined == "" {
		joined = "(none)"
	}
	g.setMeta("composer_name", j.str("name"))
	if phpVersion == "" {
		phpVersion = "(unset)"
	}
	g.setMeta("php_constraint", phpVersion)
	g.setMeta("psr4_roots", joined)
	g.setMeta("php_85_features",
		"n_pipe_operator counts 8.5's |> only; a codebase pinned below "+
			"8.5 shows zero for reasons of version, not style")
}

func writeMeta(g *graph, root string, filesParsed, filesFailed int) {
	abs, _ := filepath.Abs(root)
	g.setMeta("schema_version", "1")
	g.setMeta("lang", "php")
	g.setMeta("target", "PHP 8.5")
	g.setMeta("root", abs)
	g.setMeta("parse_mode", "tree-sitter")
	g.setMeta("parser", "parser: tree-sitter "+tsRuntimeVersion+" + tree-sitter-php>=0.24 "+tsGrammarVersion)
	g.setMeta("built_at", nowStamp())
	g.setMeta("files_parsed", strconv.Itoa(filesParsed))
	g.setMeta("files_failed", strconv.Itoa(filesFailed))
	g.setMeta("parse_concurrency", fmtInt(parseWorkers())+
		" worker(s) over files; symbol ids are assigned in traversal order at merge")
}

type cell struct {
	kind byte
	i    int64
	f    float64
	s    string
}

func cellI(v int64) cell   { return cell{kind: 'i', i: v} }
func cellS(v string) cell  { return cell{kind: 's', s: v} }
func cellNull() cell       { return cell{} }
func cellF(v float64) cell { return cell{kind: 'f', f: v} }
func (c cell) encode(b *strings.Builder) {
	switch c.kind {
	case 0:
		b.WriteString(`\N`)
	case 'i':
		b.WriteString("i:")
		b.WriteString(itoa64(c.i))
	case 'f':
		b.WriteString("f:")
		b.WriteString(cgFloat(c.f))
	default:
		b.WriteString("s:")
		encodeText(b, c.s)
	}
}

func itoa64(v int64) string { return strconvFormatInt(v) }

func encodeText(b *strings.Builder, s string) {
	for i := 0; i < len(s); i++ {
		c := s[i]
		switch c {
		case '\\':
			b.WriteString(`\\`)
		case '\n':
			b.WriteString(`\n`)
		case '\t':
			b.WriteString(`\t`)
		case '\r':
			b.WriteString(`\r`)
		default:
			if c < 0x20 || c == 0x7F {
				b.WriteString(`\x`)
				const hex = "0123456789ABCDEF"
				b.WriteByte(hex[c>>4])
				b.WriteByte(hex[c&0xF])
			} else {
				b.WriteByte(c)
			}
		}
	}
}

var runtimeMeta = map[string]bool{
	"parse_concurrency": true,
}

type dumpTable struct {
	name string
	cols int
	rows []string
}

func (t *dumpTable) sortRows() { sort.Strings(t.rows) }

func (g *graph) dumpTables(sep byte, lead string) []*dumpTable {
	var ts []*dumpTable
	put := func(sb *strings.Builder, c cell) {
		if sep == ' ' {
			c.encode(sb)
		} else {
			sb.WriteString(tsvField(c))
		}
	}

	add := func(name string, cols, n int, row func(i int) []cell) {
		t := &dumpTable{name: name, cols: cols, rows: make([]string, n)}
		var sb strings.Builder
		for i := range n {
			sb.Reset()
			sb.WriteString(lead)
			cs := row(i)
			for j, c := range cs {
				if j > 0 {
					sb.WriteByte(sep)
				}
				put(&sb, c)
			}
			t.rows[i] = sb.String()
		}
		ts = append(ts, t)
	}
	addRows := func(name string, cols int, rows [][]cell) {
		t := &dumpTable{name: name, cols: cols, rows: make([]string, len(rows))}
		var sb strings.Builder
		for i, r := range rows {
			sb.Reset()
			sb.WriteString(lead)
			for j, c := range r {
				if j > 0 {
					sb.WriteByte(sep)
				}
				put(&sb, c)
			}
			t.rows[i] = sb.String()
		}
		rows = nil
		ts = append(ts, t)
	}

	nMeta := 0
	for _, k := range g.metaKeys {
		if !runtimeMeta[k] {
			nMeta++
		}
	}
	add("meta", 2, nMeta, func(j int) []cell {
		n := 0
		for i, k := range g.metaKeys {
			if runtimeMeta[k] {
				continue
			}
			if n == j {
				return []cell{cellS(k), cellS(g.metaVals[i])}
			}
			n++
		}
		return nil
	})

	add("modules", 10, len(g.mods), func(i int) []cell {
		m := &g.mods[i]
		return []cell{cellI(int64(m.id)), cellS(g.sa.str(m.name)), cellS(g.sa.str(m.kind)),
			cellI(int64(m.nFiles)), cellI(int64(m.nSymbols)), cellI(int64(m.nPublic)),
			cellI(int64(m.sloc)), cellI(int64(m.fanIn)), cellI(int64(m.fanOut)),
			cellF(m.instability)}
	})

	add("files", 29, len(g.fils), func(i int) []cell {
		f := &g.fils[i]
		return []cell{cellI(int64(f.id)), cellS(g.sa.str(f.path)), cellS(g.sa.str(f.dir)),
			cellS(g.sa.str(f.base)), cellS(g.sa.str(f.ext)), cellS(g.sa.str(f.lang)), cellI(int64(f.moduleID)),
			cellI(int64(f.bytes)), cellI(int64(f.lines)), cellI(int64(f.sloc)),
			cellI(int64(f.blank)), cellI(int64(f.comment)), cellI(int64(f.docLines)),
			cellI(int64(f.maxLine)), cellS(g.sa.str(f.sha1)), cellI(int64(f.parsed)), cellI(int64(f.isTest)),
			cellI(int64(f.isGen)), cellI(int64(f.isVend)), cellI(int64(f.parseErrs)),
			cellI(int64(f.missing)), cellF(f.parseMS), cellI(int64(f.nSymbols)),
			cellI(int64(f.nFns)), cellI(int64(f.nTypes)), cellI(int64(f.nImports)),
			cellI(int64(f.totalCyclo)), cellI(int64(f.maxCyclo)), cellI(int64(f.totalRisk))}
	})

	add("symbols", nSymCols, g.sym.n, func(i int) []cell {
		r := make([]cell, nSymCols)
		for c := range nSymCols {
			if stringColumns[c] {
				r[c] = cellS(g.sym.str(c, i))
			} else if c == cHalsteadVolume {
				r[c] = cellI(g.sym.getWide(i))
			} else {
				r[c] = cellI(int64(g.sym.cols[c][i]))
			}
		}
		r[cID] = cellI(int64(i) + 1)

		if g.sym.cols[cModuleID][i] < 0 {
			r[cModuleID] = cellNull()
		}
		if g.sym.cols[cParentID][i] < 0 {
			r[cParentID] = cellNull()
		} else {

			r[cParentID] = cellI(int64(g.sym.cols[cParentID][i]) + 1)
		}
		return r
	})

	addRows("params", 13, g.dumpParams())
	addRows("fields", 14, g.dumpFields())
	addRows("edges", 6, g.dumpEdges())
	addRows("callsites", 3, g.dumpCallsites())
	addRows("unresolved_calls", 4, g.dumpUnresolved())
	addRows("imports", 13, g.dumpImports())
	addRows("hazards", 5, g.dumpHazards())
	addRows("attributes", 6, g.dumpAttributes())
	addRows("literals", 7, g.dumpLiterals())
	addRows("enum_members", 5, nil)

	addRows("markers", 6, g.dumpMarkers())
	addRows("classes", 31, g.dumpClasses())
	addRows("traits", 9, g.dumpTraits())
	addRows("namespaces", 6, g.dumpNamespaces())
	addRows("superglobal_reads", 8, g.dumpSuper())
	addRows("sql_sites", 12, g.dumpSQL())
	addRows("secret_candidates", 5, g.dumpSecrets())
	addRows("property_hooks", 12, g.dumpHooks())
	addRows("magic_methods", 11, g.dumpMagic())
	addRows("dynamic_sites", 7, g.dumpDyn())

	addRows("locals", 11, nil)

	add("sym_fts", 3, g.sym.n, func(i int) []cell {
		return []cell{cellNull(), cellNull(), cellNull()}
	})

	sort.Slice(ts, func(i, j int) bool { return ts[i].name < ts[j].name })
	return ts
}

func symRef(v int32, isNull bool) cell {
	if isNull {
		return cellNull()
	}
	return cellI(int64(v) + 1)
}

func nullableI(v int32, isNull bool) cell {
	if isNull {
		return cellNull()
	}
	return cellI(int64(v))
}

func nullableS(v string, isNull bool) cell {
	if isNull {
		return cellNull()
	}
	return cellS(v)
}

func (g *graph) dumpParams() [][]cell {
	out := make([][]cell, 0, len(g.params))
	for i := range g.params {
		p := &g.params[i]
		out = append(out, []cell{symRef(p.sym, false), cellI(int64(p.pos)),
			cellS(g.sa.str(p.name)), cellS(g.sa.str(p.typ)), nullableS(g.sa.str(p.def), !p.hasDef),
			cellI(bi(p.opt)), cellI(bi(p.variadic)), cellI(bi(p.ref)), cellI(bi(p.mut)),
			cellI(bi(p.null)), cellI(0), cellI(int64(p.untyped)), cellI(int64(p.typeDepth))})
	}
	return out
}

func (g *graph) dumpFields() [][]cell {
	out := make([][]cell, 0, len(g.fields))
	for i := range g.fields {
		f := &g.fields[i]
		out = append(out, []cell{symRef(f.sym, false), cellI(int64(f.ordinal)),
			cellS(g.sa.str(f.name)), cellS(g.sa.str(f.typ)), cellS(g.sa.str(f.vis)), cellI(int64(f.line)),
			cellI(bi(f.isStatic)), cellI(bi(f.isConst)), cellI(bi(f.mut)),
			cellI(bi(f.null)), cellI(bi(f.coll)), cellI(bi(f.untyped)), cellI(0),
			cellI(int64(f.typeDepth))})
	}
	return out
}

func (g *graph) dumpEdges() [][]cell {
	out := make([][]cell, 0, len(g.edges))
	for i := range g.edges {
		e := &g.edges[i]
		out = append(out, []cell{symRef(e.caller, false), symRef(e.callee, false),
			cellI(int64(e.nCalls)), cellI(bi(e.sameFile)), cellI(bi(e.sameModule)),
			cellI(bi(e.isSelf))})
	}
	return out
}

func (g *graph) dumpCallsites() [][]cell {
	out := make([][]cell, 0, len(g.callSites))
	for _, c := range g.callSites {
		out = append(out, []cell{symRef(c.caller, false), symRef(c.callee, false), cellI(int64(c.line))})
	}
	return out
}

func (g *graph) dumpUnresolved() [][]cell {
	out := make([][]cell, 0, len(g.unresolved))
	for i := range g.unresolved {
		u := &g.unresolved[i]
		out = append(out, []cell{symRef(u.caller, false), cellS(g.sa.str(u.name)),
			cellI(int64(u.n)), cellI(int64(u.firstLine))})
	}
	return out
}

func (g *graph) dumpImports() [][]cell {
	out := make([][]cell, 0, len(g.imports))
	for i := range g.imports {
		m := &g.imports[i]
		out = append(out, []cell{cellI(int64(m.id)), cellI(int64(m.fileID)),
			cellS(g.sa.str(m.target)), nullableI(m.targetID, m.targetIDNull),
			nullableS(g.sa.str(m.alias), m.aliasNull), cellS(g.sa.str(m.kind)), cellI(int64(m.line)),
			cellI(bi(m.ext)), cellI(bi(m.rel)), cellI(bi(m.wild)), cellI(bi(false)),
			cellI(bi(m.dynamic)), cellI(int64(m.nNames))})
	}
	return out
}

func (g *graph) dumpHazards() [][]cell {
	out := make([][]cell, 0, len(g.hazards))
	for i := range g.hazards {
		h := &g.hazards[i]
		out = append(out, []cell{symRef(h.sym, false), cellS(g.sa.str(h.pattern)), cellS(g.sa.str(h.category)),
			cellI(int64(h.n)), cellI(int64(h.firstLine))})
	}
	return out
}

func (g *graph) dumpAttributes() [][]cell {
	out := make([][]cell, 0, len(g.attributes))
	for i := range g.attributes {
		a := &g.attributes[i]
		out = append(out, []cell{cellI(int64(a.id)), symRef(a.sym, a.symNull),
			cellI(int64(a.fileID)), cellS(g.sa.str(a.name)), nullableS(g.sa.str(a.args), a.argsNull),
			cellI(int64(a.line))})
	}
	return out
}

func (g *graph) dumpLiterals() [][]cell {
	out := make([][]cell, 0, len(g.literals))
	for i := range g.literals {
		l := &g.literals[i]
		out = append(out, []cell{cellI(int64(l.id)), symRef(l.sym, l.symNull),
			cellI(int64(l.fileID)), cellS(g.sa.str(l.kind)), cellS(g.sa.str(l.value)), cellI(int64(l.line)),
			cellI(bi(l.isMagic))})
	}
	return out
}

func (g *graph) dumpMarkers() [][]cell {
	out := make([][]cell, 0, len(g.markers))
	for i := range g.markers {
		m := &g.markers[i]
		out = append(out, []cell{cellI(int64(m.id)), cellI(int64(m.fileID)),
			symRef(m.sym, m.symNull), cellS(g.sa.str(m.kind)), cellI(int64(m.line)), cellS(g.sa.str(m.txt))})
	}
	return out
}

func (g *graph) dumpClasses() [][]cell {
	out := make([][]cell, 0, len(g.classes))
	for i := range g.classes {
		c := &g.classes[i]
		out = append(out, []cell{symRef(c.sym, false), cellI(int64(c.fileID)),
			cellS(g.sa.str(c.name)), cellS(g.sa.str(c.fqn)), cellS(g.sa.str(c.ns)), cellS(g.sa.str(c.kind)), cellS(g.sa.str(c.ext)),
			cellS(g.sa.str(c.impl)), cellS(g.sa.str(c.traitList)), cellI(int64(c.nTraits)),
			cellI(int64(c.nMethods)), cellI(int64(c.nPub)), cellI(int64(c.nStatic)),
			cellI(int64(c.nProps)), cellI(int64(c.nPromoted)), cellI(int64(c.nHooks)),
			cellI(int64(c.nConsts)), cellI(int64(c.nCases)), cellI(int64(c.nMagic)),
			cellI(bi(c.isAbstract)), cellI(bi(c.isFinal)), cellI(bi(c.isReadonly)),
			cellI(bi(c.isAnon)), cellI(bi(c.hasDestruct)), cellI(bi(c.hasWakeup)),
			cellI(bi(c.hasToStr)), cellI(bi(c.hasCall)), cellI(bi(c.hasCallStatic)),
			cellI(bi(c.hasGet)), cellI(bi(c.hasInvoke)), cellI(int64(c.line))})
	}
	return out
}

func (g *graph) dumpTraits() [][]cell {
	out := make([][]cell, 0, len(g.traits))
	for i := range g.traits {
		t := &g.traits[i]
		out = append(out, []cell{symRef(t.sym, false), cellI(int64(t.fileID)),
			cellS(g.sa.str(t.name)), cellS(g.sa.str(t.ns)), cellI(int64(t.nMethods)),
			cellI(int64(t.nAbstract)), cellI(int64(t.nProps)), cellI(int64(t.usedBy)),
			cellI(int64(t.line))})
	}
	return out
}

func (g *graph) dumpNamespaces() [][]cell {
	out := make([][]cell, 0, len(g.namespaces))
	for i := range g.namespaces {
		n := &g.namespaces[i]
		out = append(out, []cell{cellI(int64(n.id)), cellI(int64(n.fileID)),
			cellS(g.sa.str(n.name)), cellI(int64(n.line)), cellI(bi(n.strict)),
			cellI(int64(n.nClasses))})
	}
	return out
}

func (g *graph) dumpSuper() [][]cell {
	out := make([][]cell, 0, len(g.superglobals))
	for i := range g.superglobals {
		r := &g.superglobals[i]
		out = append(out, []cell{cellI(int64(r.id)), symRef(r.sym, r.symNull),
			cellI(int64(r.fileID)), cellS(g.sa.str(r.v)), cellS(g.sa.str(r.key)), cellI(int64(r.line)),
			cellI(bi(r.inLoop)), cellI(bi(r.psalm))})
	}
	return out
}

func (g *graph) dumpSQL() [][]cell {
	out := make([][]cell, 0, len(g.sqlSites))
	for i := range g.sqlSites {
		s := &g.sqlSites[i]
		out = append(out, []cell{cellI(int64(s.id)), symRef(s.sym, s.symNull),
			cellI(int64(s.fileID)), cellS(g.sa.str(s.callee)), cellS(g.sa.str(s.driver)), cellS(g.sa.str(s.buildKind)),
			cellI(bi(s.sanitized)), cellI(bi(s.prepared)), cellI(bi(s.hasSuper)),
			cellI(bi(s.inLoop)), cellI(int64(s.line)), cellS(g.sa.str(s.snippet))})
	}
	return out
}

func (g *graph) dumpSecrets() [][]cell {
	out := make([][]cell, 0, len(g.secrets))
	for i := range g.secrets {
		s := &g.secrets[i]
		out = append(out, []cell{cellI(int64(s.id)), symRef(s.sym, s.symNull),
			cellI(int64(s.fileID)), cellS(g.sa.str(s.value)), cellI(int64(s.line))})
	}
	return out
}

func (g *graph) dumpHooks() [][]cell {
	out := make([][]cell, 0, len(g.hooks))
	for i := range g.hooks {
		h := &g.hooks[i]
		out = append(out, []cell{cellI(int64(h.id)), symRef(h.sym, h.symNull),
			symRef(h.classID, h.classIDNull), cellI(int64(h.fileID)), cellS(g.sa.str(h.className)),
			cellS(g.sa.str(h.property)), cellS(g.sa.str(h.hook)), cellI(bi(h.isShort)), cellI(bi(h.isVirtual)),
			cellI(int64(h.bodySLOC)), cellI(int64(h.nCalls)), cellI(int64(h.line))})
	}
	return out
}

func (g *graph) dumpMagic() [][]cell {
	out := make([][]cell, 0, len(g.magic))
	for i := range g.magic {
		m := &g.magic[i]
		out = append(out, []cell{cellI(int64(m.id)), symRef(m.sym, m.symNull),
			symRef(m.classID, m.classIDNull), cellI(int64(m.fileID)), cellS(g.sa.str(m.className)),
			cellS(g.sa.str(m.method)), cellI(bi(m.isGadget)), cellI(int64(m.bodySLOC)),
			cellI(int64(m.nCalls)), cellI(int64(m.nHazards)), cellI(int64(m.line))})
	}
	return out
}

func (g *graph) dumpDyn() [][]cell {
	out := make([][]cell, 0, len(g.dynSites))
	for i := range g.dynSites {
		d := &g.dynSites[i]
		out = append(out, []cell{cellI(int64(d.id)), symRef(d.sym, d.symNull),
			cellI(int64(d.fileID)), cellS(g.sa.str(d.kind)), cellS(g.sa.str(d.target)), cellI(bi(d.inLoop)),
			cellI(int64(d.line))})
	}
	return out
}

func bi(b bool) int64 {
	if b {
		return 1
	}
	return 0
}

func writeDump(w io.Writer, g *graph) {
	bw := bufio.NewWriterSize(w, 1<<20)
	defer bw.Flush()
	for _, t := range g.dumpTables(' ', "R ") {
		t.sortRows()
		bw.WriteString("T " + t.name + " ")
		bw.WriteString(fmtInt(t.cols))
		bw.WriteString(" ")
		bw.WriteString(fmtInt(len(t.rows)))
		bw.WriteByte('\n')
		for _, r := range t.rows {
			bw.WriteString(r)
			bw.WriteByte('\n')
		}
		bw.WriteString("E " + t.name + "\n")
	}
}

func writeTSV(w io.Writer, g *graph) {
	bw := bufio.NewWriterSize(w, 1<<20)
	defer bw.Flush()
	for _, t := range g.dumpTables('\t', "R\t") {
		t.sortRows()
		bw.WriteString("T\t" + t.name + "\t" + fmtInt(t.cols) + "\t" + fmtInt(len(t.rows)) + "\n")
		for _, r := range t.rows {
			bw.WriteString(r)
			bw.WriteByte('\n')
		}
		bw.WriteString("E\t" + t.name + "\n")
	}
}

func tsvField(c cell) string {
	if c.kind == 0 {
		return "\\N"
	}
	if c.kind == 'i' {
		return "i:" + itoa64(c.i)
	}
	if c.kind == 'f' {
		return "f:" + cgFloat(c.f)
	}
	var b strings.Builder
	b.WriteString("s:")
	for i := 0; i < len(c.s); i++ {
		switch ch := c.s[i]; ch {
		case ' ':
			b.WriteString(`\x20`)
		case '\t':
			b.WriteString(`\x09`)
		case '\n':
			b.WriteString(`\x0A`)
		case '\r':
			b.WriteString(`\x0D`)
		case '\\':
			b.WriteString(`\\`)
		default:
			b.WriteByte(ch)
		}
	}
	return b.String()
}

func (pa *phpParser) emitFunction(n tsNode, sc scope, kind string) int32 {
	rec := pa.rec
	name := pa.nodeName(n)
	if name == "" {
		name = "(anonymous)"
	}
	qual := sc.qualPre + name
	body := fieldNode(n, fBody)
	if !hasNode(body) {
		body = n
	}
	st := pa.st
	st.reset()
	pa.measure(st, body, pa.src, nil)

	sid := rec.newSym()
	pa.fillCommon(sid, n, name, kind, sc.sym, pa.returnTypeOf(n))
	rec.set(cSloc, sid, pa.slocOf(n))
	pa.applyStats(sid, st)
	pa.applyFunctionFlags(sid, n, sc)

	pa.emitParams(n, sid)
	pa.emitAttributes(n, sid)
	for _, c := range st.calls {
		if c.dynamic || c.name == "" {
			continue
		}
		rec.pend = append(rec.pend, pendRec{sym: sid, fid: rec.fid, mid: rec.moduleID,
			name: pa.pool.name(c.name), line: c.line, typ: pa.pool.name(sc.typeName)})
	}
	pa.emitHazards(st, sid)
	pa.emitSecrets(st, sid)
	for _, l := range st.literals {
		rec.literals = append(rec.literals, literalRow{sym: sid, fileID: rec.fid,
			kind: pa.put(l.kind), value: pa.put(clip(l.value, 200)), line: l.line, isMagic: l.magic})
	}
	pa.functionExtra(n, sid, sc)
	rec.byName[name] = append(rec.byName[name], localSym{sid: sid, fid: rec.fid,
		mid: rec.moduleID, typ: sc.typeName})
	rec.byQual[qual] = sid
	return sid
}

func (pa *phpParser) emitType(n tsNode, sc scope, kind string) int32 {
	rec := pa.rec
	name := pa.nodeName(n)
	if name == "" {
		name = "(anonymous)"
	}
	qual := sc.qualPre + name
	body := fieldNode(n, fBody)
	if !hasNode(body) {
		body = n
	}
	st := pa.st
	st.reset()
	pa.measure(st, body, pa.src, kPrune)

	sid := rec.newSym()

	pa.fillCommon(sid, n, name, kind, sc.sym, "")
	rec.set(cSloc, sid, pa.slocOf(n))

	pa.applyTypeStats(sid, st)
	pa.applyTypeFlags(sid, n)

	pa.emitAttributes(n, sid)
	for _, c := range st.calls {
		if c.dynamic || c.name == "" {
			continue
		}
		rec.pend = append(rec.pend, pendRec{sym: sid, fid: rec.fid, mid: rec.moduleID,
			name: pa.pool.name(c.name), line: c.line, typ: pa.pool.name(sc.typeName)})
	}
	pa.emitHazards(st, sid)
	pa.typeExtra(n, sid, kind)
	rec.byName[name] = append(rec.byName[name], localSym{sid: sid, fid: rec.fid,
		mid: rec.moduleID, typ: sc.typeName})
	rec.byQual[qual] = sid
	return sid
}

func (pa *phpParser) emitModuleScope(root tsNode) {
	rec := pa.rec
	st := pa.st
	st.reset()
	pa.measure(st, root, pa.src, kPrune)
	if len(st.calls) == 0 && st.nTokens < 8 {
		return
	}
	sid := rec.newSym()
	pa.fillCommon(sid, root, "<module>", "module", -1, "")
	pa.applyStats(sid, st)
	rec.set(cIsTest, sid, b2i(rec.isTest))
	for _, c := range st.calls {
		if c.dynamic || c.name == "" {
			continue
		}
		rec.pend = append(rec.pend, pendRec{sym: sid, fid: rec.fid, mid: rec.moduleID,
			name: pa.pool.name(c.name), line: c.line, typ: pa.pool.name("")})
	}
	pa.emitHazards(st, sid)
	pa.emitSecrets(st, sid)
	for _, l := range st.literals {
		rec.literals = append(rec.literals, literalRow{sym: sid, fileID: rec.fid,
			kind: pa.put(l.kind), value: pa.put(clip(l.value, 200)), line: l.line, isMagic: l.magic})
	}
}

func (pa *phpParser) fillCommon(sid int32, n tsNode, name, kind string,
	parent int32, ret string) {
	rec := pa.rec
	ls := int32(startRow(n)) + 1
	le := int32(endRow(n)) + 1
	rec.set(cFileID, sid, rec.fid)
	rec.set(cModuleID, sid, rec.moduleID)
	rec.set(cParentID, sid, parent)
	rec.setS(cName, sid, name)
	rec.setS(cKind, sid, kind)
	rec.set(cLineStart, sid, ls)
	rec.set(cNLines, sid, le-ls+1)
	rec.setS(cReturnType, sid, clip(ret, 200))
}

func (pa *phpParser) applyTypeStats(sid int32, st *stats) {
	rec := pa.rec
	for _, sl := range st.touched {
		if v := st.cnt[sl]; v != 0 {
			rec.syms[sid].vals[bumpCols[sl]] = v
		}
	}
	rec.set(cNTokens, sid, st.nTokens)
	rec.set(cNOperators, sid, st.nOperators)
	rec.set(cNOperands, sid, st.nOperands)
}

func (pa *phpParser) applyStats(sid int32, st *stats) {
	rec := pa.rec
	for _, sl := range st.touched {
		if v := st.cnt[sl]; v != 0 {
			rec.syms[sid].vals[bumpCols[sl]] = v
		}
	}
	rec.set(cCyclomatic, sid, st.cyclomatic)
	rec.set(cCognitive, sid, st.cognitive)
	rec.set(cMaxNesting, sid, st.maxNesting)
	rec.set(cMaxLoopDepth, sid, st.maxLoopDepth)
	rec.set(cNTokens, sid, st.nTokens)
	rec.set(cNOperators, sid, st.nOperators)
	rec.set(cNOperands, sid, st.nOperands)
	rec.set(cNDistinctOperators, sid, int32(len(st.operators)))
	rec.set(cNDistinctOperands, sid, int32(len(st.operands)))
}

func (pa *phpParser) returnTypeOf(n tsNode) string {
	r := fieldNode(n, fReturnType)
	if !hasNode(r) {
		return ""
	}
	return strings.TrimSpace(txt(r, pa.src))
}

func (pa *phpParser) emitParams(n tsNode, sid int32) {
	params := fieldNode(n, fParams)
	if !hasNode(params) {
		return
	}
	var pos int32
	for _, p := range namedKids(params) {
		if !paramNodeTypes[kindName(p)] {
			continue
		}
		nm := fieldNode(p, fName)
		name := ""
		if hasNode(nm) {
			name = strings.TrimSpace(txt(nm, pa.src))
		}
		tn := fieldNode(p, fType)
		ptype := ""
		if hasNode(tn) {
			ptype = strings.TrimSpace(txt(tn, pa.src))
		}
		dv := fieldNode(p, fDefaultValue)
		ptxt := txt(p, pa.src)
		hasDef := hasNode(dv)
		def := ""
		if hasDef {
			def = clip(txt(dv, pa.src), 120)
		}
		ref := false
		if before, _, ok := strings.Cut(ptxt, "$"); ok {
			ref = strings.Contains(before, "&")
		} else {
			ref = strings.Contains(ptxt, "&")
		}
		pa.rec.params = append(pa.rec.params, paramRow{
			sym: sid, pos: pos, name: pa.put(clip(name, 120)), typ: pa.put(clip(ptype, 200)),
			def: pa.put(def), hasDef: hasDef,
			opt:       hasDef,
			variadic:  kindName(p) == "variadic_parameter" || strings.Contains(ptxt, "..."),
			ref:       ref,
			mut:       kindName(p) == "property_promotion_parameter" && !strings.Contains(ptxt, "readonly"),
			null:      strings.HasPrefix(ptype, "?") || strings.Contains(strings.ToLower(ptype), "null"),
			untyped:   b2i(ptype == ""),
			typeDepth: int32(strings.Count(ptype, "|") + strings.Count(ptype, "&") + strings.Count(ptype, "<")),
		})
		pos++
	}
}

func (pa *phpParser) emitAttributes(n tsNode, sid int32) {
	attrs := fieldNode(n, fAttributes)
	if !hasNode(attrs) {
		return
	}
	for _, group := range namedKids(attrs) {
		if kindName(group) != "attribute_group" {
			continue
		}
		for _, a := range namedKids(group) {
			if kindName(a) != "attribute" {
				continue
			}
			nm := ""
			for _, c := range namedKids(a) {
				if k := kindName(c); k == "name" || k == "qualified_name" {
					nm = strings.TrimLeft(strings.TrimSpace(txt(c, pa.src)), "\\")
					break
				}
			}
			args := fieldNode(a, fParams)
			hasArgs := hasNode(args)
			atxt := ""
			if hasArgs {
				atxt = clip(txt(args, pa.src), 240)
			}
			pa.rec.attributes = append(pa.rec.attributes, attributeRow{
				sym: sid, fileID: pa.rec.fid, name: pa.put(clip(nm, 160)), args: pa.put(atxt),
				argsNull: !hasArgs, line: int32(startRow(a)) + 1,
			})
		}
	}
}

func (pa *phpParser) emitHazards(st *stats, sid int32) {
	type acc struct {
		cat  string
		n    int32
		line int32
	}
	var order []string
	seen := make(map[string]*acc, 8)
	for _, c := range st.calls {
		if c.name == "" {
			continue
		}
		pat, cat, ok := hazardOf(c.name)
		if !ok {
			continue
		}
		e := seen[pat]
		if e == nil {
			seen[pat] = &acc{cat: cat, n: 1, line: c.line}
			order = append(order, pat)
		} else {
			e.n++
		}
	}
	for _, pat := range order {
		e := seen[pat]
		pa.rec.hazards = append(pa.rec.hazards, hazardRow{
			sym: sid, pattern: pa.put(clip(pat, 120)), category: pa.put(e.cat), n: e.n, firstLine: e.line})
	}
}

func (pa *phpParser) emitSecrets(st *stats, sid int32) {
	for _, s := range st.secrets {
		pa.rec.secrets = append(pa.rec.secrets, secretRow{
			sym: sid, fileID: pa.rec.fid, value: pa.put(clip(s.value, 200)), line: s.line})
	}
}

func hazardOf(callee string) (string, string, bool) {
	raw := callee
	switch {
	case strings.HasPrefix(raw, "new "):
		raw = raw[4:] + "::__construct"
	case strings.HasPrefix(raw, "->"):
		raw = raw[2:]
	}
	if cat, ok := hazardCalls[raw]; ok {
		return raw, cat, true
	}
	short := raw
	if i := strings.LastIndexByte(short, '\\'); i >= 0 {
		short = short[i+1:]
	}
	if cat, ok := hazardCalls[short]; ok {
		return short, cat, true
	}
	base := short
	hasScope := false
	if i := strings.LastIndex(base, "::"); i >= 0 {
		base = base[i+2:]
		hasScope = true
	}
	if cat, ok := hazardCalls[base]; ok {
		if hasScope {
			return "*::" + base, cat, true
		}
		return base, cat, true
	}
	return "", "", false
}

const maxCell = 72

type result struct {
	cols []string
	rows [][]cell
}

func (r *result) cellStr(c cell) string {
	switch c.kind {
	case 0:
		return "-"
	case 'f':
		return fmt.Sprintf("%.2f", c.f)
	case 'i':
		return strconv.FormatInt(c.i, 10)
	default:
		return c.s
	}
}

func (r *result) render(out *output) {
	if len(r.rows) == 0 {
		out.raw(" (no rows)\n")
		return
	}
	body := make([][]string, len(r.rows))
	w := make([]int, len(r.cols))
	for i, c := range r.cols {
		w[i] = len(c)
	}
	for i, row := range r.rows {
		body[i] = make([]string, len(r.cols))
		for j, c := range row {
			s := r.cellStr(c)
			if len(s) > maxCell {
				s = s[:maxCell-3] + "..."
			}
			body[i][j] = s
			if len(body[i][j]) > w[j] {
				w[j] = len(body[i][j])
			}
		}
	}
	var sb strings.Builder
	sb.WriteByte(' ')
	for i, c := range r.cols {
		if i > 0 {
			sb.WriteByte(' ')
		}
		sb.WriteString(pad(c, w[i]))
	}
	sb.WriteByte('\n')
	sb.WriteByte(' ')
	for i := range r.cols {
		if i > 0 {
			sb.WriteByte(' ')
		}
		sb.WriteString(strings.Repeat("-", w[i]))
	}
	sb.WriteByte('\n')
	for _, row := range body {
		sb.WriteByte(' ')
		for i, s := range row {
			if i > 0 {
				sb.WriteByte(' ')
			}
			sb.WriteString(pad(s, w[i]))
		}
		sb.WriteByte('\n')
	}
	out.raw(sb.String())
}

func pad(s string, w int) string {
	if len(s) >= w {
		return s
	}
	return s + strings.Repeat(" ", w-len(s))
}

func (r *result) applyLimit(n int) {
	if n >= 0 && n < len(r.rows) {
		r.rows = r.rows[:n]
	}
}

func (r *result) writeCSV(out *output) {
	var sb strings.Builder
	for i, c := range r.cols {
		if i > 0 {
			sb.WriteByte(',')
		}
		csvField(&sb, c)
	}
	sb.WriteString("\r\n")
	for _, row := range r.rows {
		for i, c := range row {
			if i > 0 {
				sb.WriteByte(',')
			}
			csvField(&sb, c.rawString())
		}
		sb.WriteString("\r\n")
	}
	out.raw(sb.String())
}

func (c cell) rawString() string {
	switch c.kind {
	case 0:
		return ""
	case 'f':
		return cgFloat(c.f)
	case 'i':
		return strconv.FormatInt(c.i, 10)
	default:
		return c.s
	}
}

func csvField(sb *strings.Builder, s string) {
	need := strings.ContainsAny(s, ",\"\r\n")
	if !need {
		sb.WriteString(s)
		return
	}
	sb.WriteByte('"')
	for i := 0; i < len(s); i++ {
		if s[i] == '"' {
			sb.WriteString(`""`)
			continue
		}
		sb.WriteByte(s[i])
	}
	sb.WriteByte('"')
}

func (r *result) writeJSON(out *output) {
	var sb strings.Builder
	if len(r.rows) == 0 {
		out.raw("[]\n")
		return
	}
	sb.WriteString("[\n")
	for ri, row := range r.rows {
		sb.WriteString("  {\n")
		for ci, c := range row {
			sb.WriteString("    ")
			jsonString(&sb, r.cols[ci])
			sb.WriteString(": ")
			switch c.kind {
			case 0:
				sb.WriteString("null")
			case 'f':
				sb.WriteString(cgFloat(c.f))
			case 'i':
				sb.WriteString(strconv.FormatInt(c.i, 10))
			default:
				jsonString(&sb, c.s)
			}
			if ci < len(row)-1 {
				sb.WriteByte(',')
			}
			sb.WriteByte('\n')
		}
		sb.WriteString("  }")
		if ri < len(r.rows)-1 {
			sb.WriteByte(',')
		}
		sb.WriteByte('\n')
	}
	sb.WriteString("]\n")
	out.raw(sb.String())
}

func jsonString(sb *strings.Builder, s string) {
	sb.WriteByte('"')
	for _, r := range s {
		switch r {
		case '"':
			sb.WriteString(`\"`)
		case '\\':
			sb.WriteString(`\\`)
		case '\n':
			sb.WriteString(`\n`)
		case '\r':
			sb.WriteString(`\r`)
		case '\t':
			sb.WriteString(`\t`)
		default:
			if r < 0x20 {
				fmt.Fprintf(sb, `\u%04x`, r)
			} else if r < 0x80 {
				sb.WriteRune(r)
			} else {
				fmt.Fprintf(sb, `\u%04x`, r)
			}
		}
	}
	sb.WriteByte('"')
}

const cgasMagic = "CGAS"

const (
	cgasVersion  = 3
	cgasHeaderSz = 32
	cgasSecSz    = 24
	cgasNSec     = 29
	cgasArenaHi  = 1<<32 - 1
)

type cgasStr struct{ Off, Len uint32 }

type strArena struct{ buf []byte }

func (a *strArena) put(s string) cgasStr {
	if len(a.buf)+len(s) > cgasArenaHi {
		panic("cgas: string arena exceeds 4GiB offset space")
	}
	off := uint32(len(a.buf))
	a.buf = append(a.buf, s...)
	return cgasStr{off, uint32(len(s))}
}

func (a *strArena) str(s cgasStr) string {
	if s.Len == 0 {
		return ""
	}
	return unsafe.String(&a.buf[s.Off], int(s.Len))
}

func (a *strArena) eq(s cgasStr, t string) bool {
	if s.Len != uint32(len(t)) {
		return false
	}
	if s.Len == 0 {
		return true
	}
	return string(a.buf[s.Off:s.Off+s.Len]) == t
}

func (a *strArena) rebase(base uint32, strs ...*cgasStr) {
	for _, s := range strs {
		s.Off += base
	}
}

const (
	cgasSecStrings uint32 = 1 + iota
	cgasSecTrees
	cgasSecTreeDir
	cgasSecMods
	cgasSecFiles
	cgasSecSymCols
	cgasSecSymStrs
	cgasSecSymWide
	cgasSecPoolRefs
	cgasSecParams
	cgasSecFields
	cgasSecImports
	cgasSecHazards
	cgasSecAttrs
	cgasSecLits
	cgasSecMarkers
	cgasSecClasses
	cgasSecTraits
	cgasSecNamespaces
	cgasSecSuper
	cgasSecSQL
	cgasSecSecrets
	cgasSecHooks
	cgasSecMagic
	cgasSecDyn
	cgasSecEdges
	cgasSecCallSites
	cgasSecUnres
	cgasSecMeta
)

type cgasHeader struct {
	Magic    [4]byte
	Version  uint32
	SecCount uint32
	Pad      uint32
	Total    uint64
	ArenaLen uint64
}

type cgasSec struct {
	ID  uint32
	Pad uint32
	Off uint64
	Len uint64
}

var (
	modStrOffs = []uintptr{
		unsafe.Offsetof(moduleRow{}.name),
		unsafe.Offsetof(moduleRow{}.kind),
	}
	fileStrOffs = []uintptr{
		unsafe.Offsetof(fileRow{}.path),
		unsafe.Offsetof(fileRow{}.dir),
		unsafe.Offsetof(fileRow{}.base),
		unsafe.Offsetof(fileRow{}.ext),
		unsafe.Offsetof(fileRow{}.lang),
		unsafe.Offsetof(fileRow{}.sha1),
	}
	paramStrOffs = []uintptr{
		unsafe.Offsetof(paramRow{}.name),
		unsafe.Offsetof(paramRow{}.typ),
		unsafe.Offsetof(paramRow{}.def),
	}
	fieldStrOffs = []uintptr{
		unsafe.Offsetof(fieldRow{}.name),
		unsafe.Offsetof(fieldRow{}.typ),
		unsafe.Offsetof(fieldRow{}.vis),
	}
	importStrOffs = []uintptr{
		unsafe.Offsetof(importRow{}.target),
		unsafe.Offsetof(importRow{}.alias),
		unsafe.Offsetof(importRow{}.kind),
	}
	hazardStrOffs = []uintptr{
		unsafe.Offsetof(hazardRow{}.pattern),
		unsafe.Offsetof(hazardRow{}.category),
	}
	attrStrOffs = []uintptr{
		unsafe.Offsetof(attributeRow{}.name),
		unsafe.Offsetof(attributeRow{}.args),
	}
	litStrOffs = []uintptr{
		unsafe.Offsetof(literalRow{}.kind),
		unsafe.Offsetof(literalRow{}.value),
	}
	markerStrOffs = []uintptr{
		unsafe.Offsetof(markerRow{}.kind),
		unsafe.Offsetof(markerRow{}.txt),
	}
	classStrOffs = []uintptr{
		unsafe.Offsetof(classRow{}.name),
		unsafe.Offsetof(classRow{}.fqn),
		unsafe.Offsetof(classRow{}.ns),
		unsafe.Offsetof(classRow{}.kind),
		unsafe.Offsetof(classRow{}.ext),
		unsafe.Offsetof(classRow{}.impl),
		unsafe.Offsetof(classRow{}.traitList),
	}
	traitStrOffs = []uintptr{
		unsafe.Offsetof(traitRow{}.name),
		unsafe.Offsetof(traitRow{}.ns),
	}
	nsStrOffs = []uintptr{
		unsafe.Offsetof(nsRow{}.name),
	}
	superStrOffs = []uintptr{
		unsafe.Offsetof(superReadRow{}.v),
		unsafe.Offsetof(superReadRow{}.key),
	}
	sqlStrOffs = []uintptr{
		unsafe.Offsetof(sqlSiteRow{}.callee),
		unsafe.Offsetof(sqlSiteRow{}.driver),
		unsafe.Offsetof(sqlSiteRow{}.buildKind),
		unsafe.Offsetof(sqlSiteRow{}.snippet),
	}
	secretStrOffs = []uintptr{
		unsafe.Offsetof(secretRow{}.value),
	}
	hookStrOffs = []uintptr{
		unsafe.Offsetof(hookRow{}.className),
		unsafe.Offsetof(hookRow{}.property),
		unsafe.Offsetof(hookRow{}.hook),
	}
	magicStrOffs = []uintptr{
		unsafe.Offsetof(magicRow{}.className),
		unsafe.Offsetof(magicRow{}.method),
	}
	dynStrOffs = []uintptr{
		unsafe.Offsetof(dynSiteRow{}.kind),
		unsafe.Offsetof(dynSiteRow{}.target),
	}
	unresStrOffs = []uintptr{
		unsafe.Offsetof(unresolvedRow{}.name),
	}
	metaStrOffs = []uintptr{0, unsafe.Sizeof(cgasStr{})}
)

var cgasGuardDone bool

func cgasGuard() {
	if cgasGuardDone {
		return
	}
	cgasGuardDone = true
	fail := func(ok bool, what string) {
		if !ok {
			panic("cgas: unsupported platform layout: " + what)
		}
	}
	fail(unsafe.Sizeof(uintptr(0)) == 8, "64-bit required")
	x := uint32(1)
	fail(*(*byte)(unsafe.Pointer(&x)) == 1, "little-endian required")
	fail(unsafe.Sizeof(cgasStr{}) == 8, "cgasStr must be 8 bytes")
	fail(unsafe.Alignof(cgasStr{}) == 4, "cgasStr must be 4-aligned")
	fail(unsafe.Sizeof(tsRec{}) == 32, "tsRec must be the 32-byte fixed stride")
	fail(unsafe.Sizeof(cgasHeader{}) == 32, "cgasHeader must be 32 bytes")
	fail(unsafe.Sizeof(cgasSec{}) == 24, "cgasSec must be 24 bytes")
	for _, c := range []struct {
		t    reflect.Type
		want uintptr
	}{
		{reflect.TypeOf(moduleRow{}), 56},
		{reflect.TypeOf(fileRow{}), 152},
		{reflect.TypeOf(paramRow{}), 48},
		{reflect.TypeOf(fieldRow{}), 48},
		{reflect.TypeOf(importRow{}), 52},
		{reflect.TypeOf(hazardRow{}), 28},
		{reflect.TypeOf(attributeRow{}), 40},
		{reflect.TypeOf(literalRow{}), 40},
		{reflect.TypeOf(markerRow{}), 36},
		{reflect.TypeOf(classRow{}), 120},
		{reflect.TypeOf(traitRow{}), 44},
		{reflect.TypeOf(nsRow{}), 28},
		{reflect.TypeOf(superReadRow{}), 40},
		{reflect.TypeOf(sqlSiteRow{}), 56},
		{reflect.TypeOf(secretRow{}), 28},
		{reflect.TypeOf(hookRow{}), 60},
		{reflect.TypeOf(magicRow{}), 56},
		{reflect.TypeOf(dynSiteRow{}), 40},
		{reflect.TypeOf(unresolvedRow{}), 20},
		{reflect.TypeOf(edgeRow{}), 16},
		{reflect.TypeOf(callSiteRow{}), 12},
	} {
		fail(c.t.Size() == c.want, "row layout drift: "+c.t.String())
	}
	for _, t := range []reflect.Type{
		reflect.TypeOf(tsRec{}),
		reflect.TypeOf(cgasStr{}),
		reflect.TypeOf([2]cgasStr{}),
		reflect.TypeOf(edgeRow{}),
		reflect.TypeOf(callSiteRow{}),
		reflect.TypeOf(int32(0)),
		reflect.TypeOf(int64(0)),
		reflect.TypeOf(uint32(0)),
		reflect.TypeOf(float64(0)),
	} {
		fail(!cgasHasRef(t), t.String()+" must be pointer-free")
	}
	for _, t := range []reflect.Type{
		reflect.TypeOf(moduleRow{}),
		reflect.TypeOf(fileRow{}),
		reflect.TypeOf(paramRow{}),
		reflect.TypeOf(fieldRow{}),
		reflect.TypeOf(importRow{}),
		reflect.TypeOf(hazardRow{}),
		reflect.TypeOf(attributeRow{}),
		reflect.TypeOf(literalRow{}),
		reflect.TypeOf(markerRow{}),
		reflect.TypeOf(classRow{}),
		reflect.TypeOf(traitRow{}),
		reflect.TypeOf(nsRow{}),
		reflect.TypeOf(superReadRow{}),
		reflect.TypeOf(sqlSiteRow{}),
		reflect.TypeOf(secretRow{}),
		reflect.TypeOf(hookRow{}),
		reflect.TypeOf(magicRow{}),
		reflect.TypeOf(dynSiteRow{}),
		reflect.TypeOf(unresolvedRow{}),
	} {
		fail(!cgasHasRef(t), t.String()+" must be pointer-free")
	}
}

func cgasHasRef(t reflect.Type) bool {
	switch t.Kind() {
	case reflect.Pointer, reflect.String, reflect.Slice, reflect.Map,
		reflect.Chan, reflect.Func, reflect.Interface, reflect.UnsafePointer:
		return true
	case reflect.Array:
		return cgasHasRef(t.Elem())
	case reflect.Struct:
		for i := 0; i < t.NumField(); i++ {
			if cgasHasRef(t.Field(i).Type) {
				return true
			}
		}
	}
	return false
}

func cgasRawBytes[T any](v []T) []byte {
	if len(v) == 0 {
		return nil
	}
	return unsafe.Slice((*byte)(unsafe.Pointer(&v[0])), len(v)*int(unsafe.Sizeof(v[0])))
}

func cgasCheckStrs[T any](rows []T, offs []uintptr, al uint64, what string) error {
	if len(rows) == 0 || len(offs) == 0 {
		return nil
	}
	for i := range rows {
		row := unsafe.Pointer(&rows[i])
		for _, o := range offs {
			p := (*cgasStr)(unsafe.Add(row, o))
			if uint64(p.Off) > al || uint64(p.Len) > al-uint64(p.Off) {
				return fmt.Errorf("%s: row %d string reference (%d,%d) escapes the string arena (%d bytes)",
					what, i, p.Off, p.Len, al)
			}
		}
	}
	return nil
}

func cgasSection[T any](mem []byte, s cgasSec, what string) ([]T, error) {
	size := uint64(unsafe.Sizeof(*new(T)))
	if s.Len == 0 {
		return nil, nil
	}
	if size == 0 || s.Len%size != 0 {
		return nil, fmt.Errorf("%s: section length %d is not a multiple of record size %d", what, s.Len, size)
	}
	if s.Off < uint64(cgasHeaderSz) || s.Off > uint64(len(mem)) || s.Len > uint64(len(mem))-s.Off {
		return nil, fmt.Errorf("%s: section lies outside the file", what)
	}
	base := unsafe.Pointer(uintptr(unsafe.Pointer(&mem[0])) + uintptr(s.Off))
	if a := uintptr(unsafe.Alignof(*new(T))); a > 1 && uintptr(base)%a != 0 {
		return nil, fmt.Errorf("%s: section is not %d-byte aligned", what, a)
	}
	return unsafe.Slice((*T)(base), int(s.Len/size)), nil
}

func saveASTFile(g *graph, path string) (int64, error) {
	cgasGuard()
	n := g.sym.n

	stride := uint64(unsafe.Sizeof(tsRec{}))
	totalRecs := uint64(0)
	for _, tr := range g.astTrees {
		totalRecs += uint64(len(tr))
	}
	tDir := make([]byte, 12+4*len(g.astTrees))
	cgPutU64(tDir[0:8], 0, stride)
	cgPutU32(tDir[8:12], 0, uint32(len(g.astTrees)))
	for i, tr := range g.astTrees {
		cgPutU32(tDir[12+4*i:], 0, uint32(len(tr)))
	}

	metaRefs := make([][2]cgasStr, 0, len(g.metaKeys))
	for i, k := range g.metaKeys {
		if k == "built_at" {
			continue
		}
		metaRefs = append(metaRefs, [2]cgasStr{g.sa.put(k), g.sa.put(g.metaVals[i])})
	}

	symColChunks := make([][]byte, nSymCols)
	for c := range nSymCols {
		symColChunks[c] = cgasRawBytes(g.sym.cols[c][:n])
	}
	symStrChunks := make([][]byte, len(strSlots))
	for k := range strSlots {
		symStrChunks[k] = cgasRawBytes(g.sym.strs[k][:n])
	}
	body := make([][][]byte, cgasNSec)
	body[cgasSecSymCols-1] = symColChunks
	body[cgasSecSymStrs-1] = symStrChunks
	body[cgasSecSymWide-1] = [][]byte{cgasRawBytes(g.sym.wide[:n])}
	body[cgasSecPoolRefs-1] = [][]byte{cgasRawBytes(g.sym.poolRefs)}
	body[cgasSecMods-1] = [][]byte{cgasRawBytes(g.mods)}
	body[cgasSecFiles-1] = [][]byte{cgasRawBytes(g.fils)}
	body[cgasSecParams-1] = [][]byte{cgasRawBytes(g.params)}
	body[cgasSecFields-1] = [][]byte{cgasRawBytes(g.fields)}
	body[cgasSecImports-1] = [][]byte{cgasRawBytes(g.imports)}
	body[cgasSecHazards-1] = [][]byte{cgasRawBytes(g.hazards)}
	body[cgasSecAttrs-1] = [][]byte{cgasRawBytes(g.attributes)}
	body[cgasSecLits-1] = [][]byte{cgasRawBytes(g.literals)}
	body[cgasSecMarkers-1] = [][]byte{cgasRawBytes(g.markers)}
	body[cgasSecClasses-1] = [][]byte{cgasRawBytes(g.classes)}
	body[cgasSecTraits-1] = [][]byte{cgasRawBytes(g.traits)}
	body[cgasSecNamespaces-1] = [][]byte{cgasRawBytes(g.namespaces)}
	body[cgasSecSuper-1] = [][]byte{cgasRawBytes(g.superglobals)}
	body[cgasSecSQL-1] = [][]byte{cgasRawBytes(g.sqlSites)}
	body[cgasSecSecrets-1] = [][]byte{cgasRawBytes(g.secrets)}
	body[cgasSecHooks-1] = [][]byte{cgasRawBytes(g.hooks)}
	body[cgasSecMagic-1] = [][]byte{cgasRawBytes(g.magic)}
	body[cgasSecDyn-1] = [][]byte{cgasRawBytes(g.dynSites)}
	body[cgasSecEdges-1] = [][]byte{cgasRawBytes(g.edges)}
	body[cgasSecCallSites-1] = [][]byte{cgasRawBytes(g.callSites)}
	body[cgasSecUnres-1] = [][]byte{cgasRawBytes(g.unresolved)}
	body[cgasSecMeta-1] = [][]byte{cgasRawBytes(metaRefs)}
	body[cgasSecStrings-1] = [][]byte{g.sa.buf}
	body[cgasSecTreeDir-1] = [][]byte{tDir}

	dir := make([]cgasSec, cgasNSec)
	cur := uint64(cgasHeaderSz) + cgasNSec*cgasSecSz
	for i := range dir {
		cur = (cur + 7) &^ 7
		ln := uint64(0)
		for _, ch := range body[i] {
			ln += uint64(len(ch))
		}
		if i+1 == int(cgasSecTrees) {
			ln = totalRecs * stride
		}
		dir[i] = cgasSec{uint32(i + 1), 0, cur, ln}
		cur += ln
	}
	total := cur

	f, err := os.Create(path)
	if err != nil {
		return 0, err
	}
	w := bufio.NewWriterSize(f, 1<<20)
	fail := func(err error) (int64, error) {
		f.Close()
		return 0, fmt.Errorf("write %s: %v", path, err)
	}
	hdr := make([]byte, cgasHeaderSz)
	copy(hdr[0:4], cgasMagic)
	cgPutU32(hdr[4:8], 0, cgasVersion)
	cgPutU32(hdr[8:12], 0, cgasNSec)
	cgPutU64(hdr[16:24], 0, total)
	cgPutU64(hdr[24:32], 0, uint64(len(g.sa.buf)))
	if _, err := w.Write(hdr); err != nil {
		return fail(err)
	}
	dirBuf := make([]byte, cgasNSec*cgasSecSz)
	for i := range dir {
		o := i * int(cgasSecSz)
		cgPutU32(dirBuf[o:], 0, dir[i].ID)
		cgPutU64(dirBuf[o+8:], 0, dir[i].Off)
		cgPutU64(dirBuf[o+16:], 0, dir[i].Len)
	}
	if _, err := w.Write(dirBuf); err != nil {
		return fail(err)
	}
	var zero [8]byte
	pos := uint64(cgasHeaderSz) + cgasNSec*cgasSecSz
	for i := range dir {
		if dir[i].Off > pos {
			if _, err := w.Write(zero[:dir[i].Off-pos]); err != nil {
				return fail(err)
			}
			pos = dir[i].Off
		}
		if i+1 == int(cgasSecTrees) {
			for _, tr := range g.astTrees {
				if len(tr) == 0 {
					continue
				}
				raw := unsafe.Slice((*byte)(unsafe.Pointer(&tr[0])),
					len(tr)*int(unsafe.Sizeof(tsRec{})))
				if _, err := w.Write(raw); err != nil {
					return fail(err)
				}
			}
		} else {
			for _, ch := range body[i] {
				if len(ch) == 0 {
					continue
				}
				if _, err := w.Write(ch); err != nil {
					return fail(err)
				}
			}
		}
		pos += dir[i].Len
	}
	if err := w.Flush(); err != nil {
		return fail(err)
	}
	if err := f.Close(); err != nil {
		return 0, fmt.Errorf("write %s: %v", path, err)
	}
	return int64(total), nil
}

func loadAST(path string) (*graph, error) {
	cgasGuard()
	f, err := os.Open(path)
	if err != nil {
		return nil, err
	}
	defer f.Close()
	st, err := f.Stat()
	if err != nil {
		return nil, err
	}
	if !st.Mode().IsRegular() {
		return nil, fmt.Errorf("%s: not a regular file", path)
	}
	if st.Size() < int64(cgasHeaderSz+cgasNSec*cgasSecSz) {
		return nil, fmt.Errorf("%s: too small (%d bytes) to be an AST state file", path, st.Size())
	}
	mem, err := syscall.Mmap(int(f.Fd()), 0, int(st.Size()),
		syscall.PROT_READ, syscall.MAP_PRIVATE)
	if err != nil {
		return nil, fmt.Errorf("mmap %s: %v", path, err)
	}
	bad := func(format string, args ...any) error {
		syscall.Munmap(mem)
		return fmt.Errorf("%s: "+format, append([]any{path}, args...)...)
	}
	if string(mem[0:4]) != cgasMagic {
		return nil, bad("bad magic %q, want %q -- not an AST state file", string(mem[0:4]), cgasMagic)
	}
	if v := cgGetU32(mem, 4); v != cgasVersion {
		return nil, bad("unsupported state format version %d, want %d", v, cgasVersion)
	}
	secCount := int(cgGetU32(mem, 8))
	total := cgGetU64(mem, 16)
	arenaLen := cgGetU64(mem, 24)
	if secCount != cgasNSec {
		return nil, bad("section count %d, want %d", secCount, cgasNSec)
	}
	if total != uint64(st.Size()) {
		return nil, bad("truncated state file: header declares %d bytes, file has %d", total, st.Size())
	}
	dir := unsafe.Slice((*cgasSec)(unsafe.Pointer(&mem[cgasHeaderSz])), secCount)
	secs := make(map[uint32]cgasSec, secCount)
	for i := range dir {
		s := dir[i]
		if s.Off < uint64(cgasHeaderSz) || s.Off > total || s.Len > total-s.Off {
			return nil, bad("section %d lies outside the file", s.ID)
		}
		if _, dup := secs[s.ID]; dup {
			return nil, bad("duplicate section %d", s.ID)
		}
		secs[s.ID] = s
	}
	for id := uint32(1); id <= cgasNSec; id++ {
		if _, ok := secs[id]; !ok {
			return nil, bad("missing section %d", id)
		}
	}
	ao, al := secs[cgasSecStrings].Off, secs[cgasSecStrings].Len
	if al != arenaLen {
		return nil, bad("string arena length %d, header says %d", al, arenaLen)
	}
	arena := mem[ao : ao+al]

	sec := func(id uint32, what string) cgasSec {
		return secs[id]
	}
	secErr := func(err error) (*graph, error) {
		return nil, bad("%v", err)
	}

	symColRows, err := cgasSection[int32](mem, sec(cgasSecSymCols, "symbol columns"), "symbol columns")
	if err != nil {
		return secErr(err)
	}
	if len(symColRows)%nSymCols != 0 {
		return nil, bad("symbol column block (%d ints) is not a multiple of the %d-column row", len(symColRows), nSymCols)
	}
	nSym := len(symColRows) / nSymCols
	symStrRows, err := cgasSection[int32](mem, sec(cgasSecSymStrs, "symbol string columns"), "symbol string columns")
	if err != nil {
		return secErr(err)
	}
	if len(symStrRows) != nSym*len(strSlots) {
		return nil, bad("symbol string column count %d, want %d", len(symStrRows), nSym*len(strSlots))
	}
	wideRows, err := cgasSection[int64](mem, sec(cgasSecSymWide, "halstead column"), "halstead column")
	if err != nil {
		return secErr(err)
	}
	if len(wideRows) != nSym {
		return nil, bad("halstead column count %d, want %d", len(wideRows), nSym)
	}
	poolRefs, err := cgasSection[cgasStr](mem, sec(cgasSecPoolRefs, "string pool index"), "string pool index")
	if err != nil {
		return secErr(err)
	}
	if err := cgasCheckStrs(poolRefs, []uintptr{0}, al, "string pool index"); err != nil {
		return secErr(err)
	}
	mods, err := cgasSection[moduleRow](mem, sec(cgasSecMods, "modules"), "modules")
	if err != nil {
		return secErr(err)
	}
	if err := cgasCheckStrs(mods, modStrOffs, al, "modules"); err != nil {
		return secErr(err)
	}
	files, err := cgasSection[fileRow](mem, sec(cgasSecFiles, "files"), "files")
	if err != nil {
		return secErr(err)
	}
	if err := cgasCheckStrs(files, fileStrOffs, al, "files"); err != nil {
		return secErr(err)
	}
	params, err := cgasSection[paramRow](mem, sec(cgasSecParams, "params"), "params")
	if err != nil {
		return secErr(err)
	}
	if err := cgasCheckStrs(params, paramStrOffs, al, "params"); err != nil {
		return secErr(err)
	}
	fields, err := cgasSection[fieldRow](mem, sec(cgasSecFields, "fields"), "fields")
	if err != nil {
		return secErr(err)
	}
	if err := cgasCheckStrs(fields, fieldStrOffs, al, "fields"); err != nil {
		return secErr(err)
	}
	imports, err := cgasSection[importRow](mem, sec(cgasSecImports, "imports"), "imports")
	if err != nil {
		return secErr(err)
	}
	if err := cgasCheckStrs(imports, importStrOffs, al, "imports"); err != nil {
		return secErr(err)
	}
	hazards, err := cgasSection[hazardRow](mem, sec(cgasSecHazards, "hazards"), "hazards")
	if err != nil {
		return secErr(err)
	}
	if err := cgasCheckStrs(hazards, hazardStrOffs, al, "hazards"); err != nil {
		return secErr(err)
	}
	attrs, err := cgasSection[attributeRow](mem, sec(cgasSecAttrs, "attributes"), "attributes")
	if err != nil {
		return secErr(err)
	}
	if err := cgasCheckStrs(attrs, attrStrOffs, al, "attributes"); err != nil {
		return secErr(err)
	}
	lits, err := cgasSection[literalRow](mem, sec(cgasSecLits, "literals"), "literals")
	if err != nil {
		return secErr(err)
	}
	if err := cgasCheckStrs(lits, litStrOffs, al, "literals"); err != nil {
		return secErr(err)
	}
	markers, err := cgasSection[markerRow](mem, sec(cgasSecMarkers, "markers"), "markers")
	if err != nil {
		return secErr(err)
	}
	if err := cgasCheckStrs(markers, markerStrOffs, al, "markers"); err != nil {
		return secErr(err)
	}
	classes, err := cgasSection[classRow](mem, sec(cgasSecClasses, "classes"), "classes")
	if err != nil {
		return secErr(err)
	}
	if err := cgasCheckStrs(classes, classStrOffs, al, "classes"); err != nil {
		return secErr(err)
	}
	traits, err := cgasSection[traitRow](mem, sec(cgasSecTraits, "traits"), "traits")
	if err != nil {
		return secErr(err)
	}
	if err := cgasCheckStrs(traits, traitStrOffs, al, "traits"); err != nil {
		return secErr(err)
	}
	nss, err := cgasSection[nsRow](mem, sec(cgasSecNamespaces, "namespaces"), "namespaces")
	if err != nil {
		return secErr(err)
	}
	if err := cgasCheckStrs(nss, nsStrOffs, al, "namespaces"); err != nil {
		return secErr(err)
	}
	supers, err := cgasSection[superReadRow](mem, sec(cgasSecSuper, "superglobal reads"), "superglobal reads")
	if err != nil {
		return secErr(err)
	}
	if err := cgasCheckStrs(supers, superStrOffs, al, "superglobal reads"); err != nil {
		return secErr(err)
	}
	sqlRows, err := cgasSection[sqlSiteRow](mem, sec(cgasSecSQL, "sql sites"), "sql sites")
	if err != nil {
		return secErr(err)
	}
	if err := cgasCheckStrs(sqlRows, sqlStrOffs, al, "sql sites"); err != nil {
		return secErr(err)
	}
	secrets, err := cgasSection[secretRow](mem, sec(cgasSecSecrets, "secrets"), "secrets")
	if err != nil {
		return secErr(err)
	}
	if err := cgasCheckStrs(secrets, secretStrOffs, al, "secrets"); err != nil {
		return secErr(err)
	}
	hooks, err := cgasSection[hookRow](mem, sec(cgasSecHooks, "property hooks"), "property hooks")
	if err != nil {
		return secErr(err)
	}
	if err := cgasCheckStrs(hooks, hookStrOffs, al, "property hooks"); err != nil {
		return secErr(err)
	}
	magic, err := cgasSection[magicRow](mem, sec(cgasSecMagic, "magic methods"), "magic methods")
	if err != nil {
		return secErr(err)
	}
	if err := cgasCheckStrs(magic, magicStrOffs, al, "magic methods"); err != nil {
		return secErr(err)
	}
	dyns, err := cgasSection[dynSiteRow](mem, sec(cgasSecDyn, "dynamic sites"), "dynamic sites")
	if err != nil {
		return secErr(err)
	}
	if err := cgasCheckStrs(dyns, dynStrOffs, al, "dynamic sites"); err != nil {
		return secErr(err)
	}
	edges, err := cgasSection[edgeRow](mem, sec(cgasSecEdges, "edges"), "edges")
	if err != nil {
		return secErr(err)
	}
	callSites, err := cgasSection[callSiteRow](mem, sec(cgasSecCallSites, "call sites"), "call sites")
	if err != nil {
		return secErr(err)
	}
	unres, err := cgasSection[unresolvedRow](mem, sec(cgasSecUnres, "unresolved calls"), "unresolved calls")
	if err != nil {
		return secErr(err)
	}
	if err := cgasCheckStrs(unres, unresStrOffs, al, "unresolved calls"); err != nil {
		return secErr(err)
	}
	meta, err := cgasSection[[2]cgasStr](mem, sec(cgasSecMeta, "meta"), "meta")
	if err != nil {
		return secErr(err)
	}
	if err := cgasCheckStrs(meta, metaStrOffs, al, "meta"); err != nil {
		return secErr(err)
	}

	tOff, tLn := secs[cgasSecTrees].Off, secs[cgasSecTrees].Len
	dOff, dLn := secs[cgasSecTreeDir].Off, secs[cgasSecTreeDir].Len
	if dLn < 12 {
		return nil, bad("node record directory too small (%d bytes)", dLn)
	}
	dirBytes := unsafe.Slice((*byte)(unsafe.Pointer(uintptr(unsafe.Pointer(&mem[0]))+uintptr(dOff))), int(dLn))
	declStride := cgGetU64(dirBytes, 0)
	nTreeFiles := int(cgGetU32(dirBytes, 8))
	if declStride != uint64(unsafe.Sizeof(tsRec{})) {
		return nil, bad("node record stride %d, want %d", declStride, unsafe.Sizeof(tsRec{}))
	}
	if nTreeFiles != len(files) {
		return nil, bad("node record directory covers %d files, graph has %d", nTreeFiles, len(files))
	}
	if int(dLn) < 12+4*nTreeFiles {
		return nil, bad("node record directory too small for %d files", nTreeFiles)
	}
	counts := unsafe.Slice((*uint32)(unsafe.Pointer(&dirBytes[12])), nTreeFiles)
	stride := uint64(unsafe.Sizeof(tsRec{}))
	if tLn%stride != 0 {
		return nil, bad("node record arena length %d is not a multiple of the record stride", tLn)
	}
	recsAll := unsafe.Slice((*tsRec)(unsafe.Pointer(uintptr(unsafe.Pointer(&mem[0]))+uintptr(tOff))), int(tLn/stride))

	stTab := &symTable{cols: make([][]int32, nSymCols), strs: make([][]int32, len(strSlots))}
	for c := range nSymCols {
		stTab.cols[c] = symColRows[c*nSym : (c+1)*nSym]
	}
	for k := range strSlots {
		stTab.strs[k] = symStrRows[k*nSym : (k+1)*nSym]
	}
	stTab.wide = wideRows
	stTab.poolRefs = poolRefs
	stTab.n = nSym
	stTab.grown = nSym

	g := newGraph()
	g.sym = stTab
	stTab.sa = &g.sa
	g.sa.buf = arena[:al:al]
	g.mods = mods
	g.fils = files
	g.params = params
	g.fields = fields
	g.imports = imports
	g.hazards = hazards
	g.attributes = attrs
	g.literals = lits
	g.markers = markers
	g.classes = classes
	g.traits = traits
	g.namespaces = nss
	g.superglobals = supers
	g.sqlSites = sqlRows
	g.secrets = secrets
	g.hooks = hooks
	g.magic = magic
	g.dynSites = dyns
	g.edges = edges
	g.callSites = callSites
	g.unresolved = unres
	for _, m := range meta {
		g.setMeta(g.sa.str(m[0]), g.sa.str(m[1]))
	}
	g.setMeta("built_at", nowStamp())
	g.astTrees = make([][]tsRec, nTreeFiles)
	base := 0
	for i := 0; i < nTreeFiles; i++ {
		c := int(counts[i])
		if base+c > len(recsAll) {
			return nil, bad("node record directory overruns the record arena")
		}
		if c > 0 {
			g.astTrees[i] = recsAll[base : base+c]
		}
		base += c
	}
	if base != len(recsAll) {
		return nil, bad("node record arena has %d unused records", len(recsAll)-base)
	}
	g.releaseResolveState()
	g.astBlob = mem
	g.adj = g.buildAdjacency()
	return g, nil
}
