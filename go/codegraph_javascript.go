package main

import (
	"bufio"
	"bytes"
	"crypto/sha1"
	"encoding/hex"
	"encoding/json/jsontext"
	"fmt"
	"io"
	"math"
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
	"sync"
	"syscall"
	"time"
	"unicode"
	"unicode/utf8"
	"unsafe"
)

const (
	grammarTag     = "v0.25.0"
	grammarName    = "tree-sitter-javascript"
	grammarSources = "https://github.com/tree-sitter/" + grammarName
)

type tsAnonField struct {
	kind, token, field string
}

type kindTableSet struct {
	abiVersion    int
	symCount      int
	fieldCount    int
	symNamed      []bool
	symVisible    []bool
	symSuper      []bool
	symPublic     []uint16
	symNames      []string
	fieldNames    []string
	anonFieldList []tsAnonField
}

var kindTables = loadKindTables()

var (
	tsAbiVersion = kindTables.abiVersion
	tsSymCount   = kindTables.symCount
	tsFieldCount = kindTables.fieldCount
	tsSymNamed   = kindTables.symNamed
	tsSymVisible = kindTables.symVisible
	tsSymSuper   = kindTables.symSuper
	tsSymPublic  = kindTables.symPublic
	tsSymNames   = kindTables.symNames
	tsFieldNames = kindTables.fieldNames
)

var tsAnonFieldList = kindTables.anonFieldList

func kindGrammarDir() string {
	grammars := os.Getenv("TREE_SITTER_GRAMMARS")
	if grammars == "" {
		home, err := os.UserHomeDir()
		if err != nil {
			fmt.Fprintf(os.Stderr, "codegraph-javascript: cannot resolve the "+
				"grammar directory ($HOME: %v)\n", err)
			os.Exit(1)
		}
		grammars = filepath.Join(home, ".cache", "codegraph", "grammars")
	}
	return filepath.Join(grammars, grammarName)
}

func loadKindTables() *kindTableSet {
	gd := kindGrammarDir()
	clone := "git clone --depth 1 --branch " + grammarTag + " " +
		grammarSources + " " + gd
	nodeTypesPath := filepath.Join(gd, "src", "node-types.json")
	grammarPath := filepath.Join(gd, "src", "grammar.json")
	for _, p := range [2]string{nodeTypesPath, grammarPath} {
		if _, err := os.Stat(p); err != nil {
			fmt.Fprintf(os.Stderr, "codegraph-javascript: the pinned grammar "+
				"sources are missing under %s\n  clone them with:\n    %s\n", gd, clone)
			os.Exit(1)
		}
	}
	nodeTypes := readOJSONFile(nodeTypesPath)
	grammar := readOJSONFile(grammarPath)

	type symEntry struct {
		name                 string
		named, visible, weak bool
	}
	var syms []symEntry
	var fields []string
	seenFields := map[string]bool{}
	addField := func(name string) {
		if name == "" || seenFields[name] {
			return
		}
		seenFields[name] = true
		fields = append(fields, name)
	}
	type symKey struct {
		name  string
		named bool
	}
	seen := map[symKey]bool{}

	for _, e := range nodeTypes.arr {
		name := e.member("type").str()
		named := true
		if ne := e.member("named"); ne.isBool() {
			named = ne.b
		}
		k := symKey{name, named}
		if seen[k] {
			continue
		}
		seen[k] = true
		syms = append(syms, symEntry{name: name, named: named, visible: true})
		for _, f := range e.member("fields").keyList() {
			addField(f)
		}
	}

	for _, st := range grammar.member("supertypes").arr {
		name := st.str()
		found := false
		for i := range syms {
			if syms[i].name == name {
				found = true
				syms[i].weak = true
			}
		}
		if !found {
			syms = append(syms, symEntry{name: name, named: true, weak: true})
		}
	}
	syms = append(syms,
		symEntry{name: "ERROR", named: true, visible: true},
		symEntry{name: "\x00MISSING", named: true, visible: true},
	)

	t := &kindTableSet{abiVersion: 0, symCount: len(syms)}
	t.symNamed = make([]bool, len(syms))
	t.symVisible = make([]bool, len(syms))
	t.symSuper = make([]bool, len(syms))
	t.symPublic = make([]uint16, len(syms))
	t.symNames = make([]string, len(syms))
	for i, s := range syms {
		t.symNamed[i] = s.named
		t.symVisible[i] = s.visible
		t.symSuper[i] = s.weak
		t.symPublic[i] = uint16(i)
		t.symNames[i] = s.name
	}
	t.fieldCount = len(fields) + 1
	t.fieldNames = append([]string{""}, fields...)

	type triple struct{ kind, token, field string }
	var anon []triple
	for _, e := range nodeTypes.arr {
		k := e.member("type").str()
		fe := e.member("fields")
		for _, fname := range fe.keyList() {
			for _, ty := range fe.member(fname).member("types").arrList() {
				named := true
				if nb := ty.member("named"); nb.isBool() {
					named = nb.b
				}
				if !named {
					anon = append(anon, triple{k, ty.member("type").str(), fname})
				}
			}
		}
	}

	rank := map[[2]string]int{}
	ranked := map[string]bool{}
	for _, a := range anon {
		if ranked[a.kind] {
			continue
		}
		ranked[a.kind] = true
		for i, f := range ruleFieldOrder(grammar, a.kind) {
			rank[[2]string{a.kind, f}] = i
		}
	}
	sort.SliceStable(anon, func(i, j int) bool {
		a, b := anon[i], anon[j]
		ra, ok := rank[[2]string{a.kind, a.field}]
		if !ok {
			ra = 99
		}
		rb, ok := rank[[2]string{b.kind, b.field}]
		if !ok {
			rb = 99
		}
		if a.kind != b.kind {
			return a.kind < b.kind
		}
		if ra != rb {
			return ra < rb
		}
		if a.token != b.token {
			return a.token < b.token
		}
		return a.field < b.field
	})
	t.anonFieldList = make([]tsAnonField, len(anon))
	for i, a := range anon {
		t.anonFieldList[i] = tsAnonField{kind: a.kind, token: a.token, field: a.field}
	}
	return t
}

func ruleFieldOrder(grammar *ojson, name string) []string {
	var order []string
	seen := map[string]bool{}
	var walk func(r *ojson)
	walk = func(r *ojson) {
		if !r.isObj() {
			return
		}
		if r.member("type").str() == "FIELD" {
			if n := r.member("name").str(); n != "" && !seen[n] {
				seen[n] = true
				order = append(order, n)
			}
		}
		for _, m := range r.member("members").arrList() {
			walk(m)
		}
		walk(r.member("content"))
	}
	walk(grammar.member("rules").member(name))
	return order
}

type ojson struct {
	kind byte
	b    bool
	s    string
	arr  []*ojson
	keys []string
	obj  map[string]*ojson
}

func (o *ojson) member(key string) *ojson {
	if o == nil || o.kind != 'o' {
		return nil
	}
	return o.obj[key]
}

func (o *ojson) str() string {
	if o == nil || o.kind != 's' {
		return ""
	}
	return o.s
}

func (o *ojson) isBool() bool { return o != nil && o.kind == 'b' }
func (o *ojson) isObj() bool  { return o != nil && o.kind == 'o' }

func (o *ojson) keyList() []string {
	if o == nil {
		return nil
	}
	return o.keys
}

func (o *ojson) arrList() []*ojson {
	if o == nil {
		return nil
	}
	return o.arr
}

func readOJSONFile(path string) *ojson {
	data, err := os.ReadFile(path)
	if err != nil {
		fmt.Fprintf(os.Stderr, "codegraph-javascript: cannot read %s: %v\n", path, err)
		os.Exit(1)
	}
	v, err := decodeOJSON(jsontext.NewDecoder(bytes.NewReader(data)))
	if err != nil {
		fmt.Fprintf(os.Stderr, "codegraph-javascript: cannot decode %s: %v\n", path, err)
		os.Exit(1)
	}
	return v
}

func decodeOJSON(dec *jsontext.Decoder) (*ojson, error) {
	switch dec.PeekKind() {
	case '{':
		if _, err := dec.ReadToken(); err != nil {
			return nil, err
		}
		o := &ojson{kind: 'o', obj: map[string]*ojson{}}
		for dec.PeekKind() != '}' {
			kt, err := dec.ReadToken()
			if err != nil {
				return nil, err
			}
			key := kt.String()
			v, err := decodeOJSON(dec)
			if err != nil {
				return nil, err
			}
			if _, dup := o.obj[key]; !dup {
				o.keys = append(o.keys, key)
			}
			o.obj[key] = v
		}
		if _, err := dec.ReadToken(); err != nil {
			return nil, err
		}
		return o, nil
	case '[':
		if _, err := dec.ReadToken(); err != nil {
			return nil, err
		}
		o := &ojson{kind: 'a'}
		for dec.PeekKind() != ']' {
			v, err := decodeOJSON(dec)
			if err != nil {
				return nil, err
			}
			o.arr = append(o.arr, v)
		}
		if _, err := dec.ReadToken(); err != nil {
			return nil, err
		}
		return o, nil
	case '"':
		tok, err := dec.ReadToken()
		if err != nil {
			return nil, err
		}
		return &ojson{kind: 's', s: tok.String()}, nil
	case 't', 'f':
		tok, err := dec.ReadToken()
		if err != nil {
			return nil, err
		}
		return &ojson{kind: 'b', b: tok.Bool()}, nil
	case '0':
		tok, err := dec.ReadToken()
		if err != nil {
			return nil, err
		}
		return &ojson{kind: 'n', s: tok.String()}, nil
	default:
		if _, err := dec.ReadToken(); err != nil {
			return nil, err
		}
		return &ojson{}, nil
	}
}

const tsScope = "source.js"

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
		p := filepath.Join(home, ".cache", "codegraph", "bin", "tree-sitter")
		if _, err := os.Stat(p); err == nil {
			return p
		}
	}
	if b, err := exec.LookPath("tree-sitter"); err == nil {
		return b
	}
	return "/opt/homebrew/bin/tree-sitter"
}

type tsParser struct {
	bin  string
	argv []string
}

var spawnEnv []string
var spawnDevnull uintptr

func spawnInit(bin string) {
	if spawnEnv == nil {
		spawnEnv = append(os.Environ(), "NO_COLOR=1", "TERM=dumb")
	}
	if spawnDevnull == 0 {
		fd, err := syscall.Open(os.DevNull, syscall.O_RDWR, 0)
		if err != nil {
			panic("open /dev/null: " + err.Error())
		}
		spawnDevnull = uintptr(fd)
	}
}

func tsParserNew() *tsParser {
	bin := tsCLIBin()
	const installHint = " -- install it with: cargo install tree-sitter-cli" +
		" --version 0.25.10 --root $HOME/.cache/codegraph (or set TREE_SITTER_BIN)"
	if _, err := os.Stat(bin); err != nil {
		panic("tree-sitter CLI not found at " + bin + installHint)
	}
	out, err := exec.Command(bin, "--version").Output()
	if err != nil || !bytes.HasPrefix(out, []byte("tree-sitter 0.25.")) {
		panic("tree-sitter CLI at " + bin + " is not 0.25.x (got " +
			strings.TrimSpace(string(out)) + ") -- error recovery must match the reference" +
			installHint)
	}
	spawnInit(bin)
	return &tsParser{bin: bin, argv: []string{bin, "parse", "/dev/stdin",
		"--scope", tsScope, "--cst"}}
}

func (p *tsParser) free() {}

func pipePair() (int, int, bool) {
	var fd [2]int
	if err := syscall.Pipe(fd[:]); err != nil {
		return -1, -1, false
	}
	r, w := fd[0], fd[1]
	syscall.CloseOnExec(r)
	syscall.CloseOnExec(w)
	return r, w, true
}

func writeAllFD(fd int, b []byte) {
	for len(b) > 0 {
		n, err := syscall.Write(fd, b)
		if n > 0 {
			b = b[n:]
			continue
		}
		if err == syscall.EINTR {
			continue
		}
		return
	}
}

func (p *tsParser) parse(src []byte, buf []byte) []byte {
	inR, inW, ok := pipePair()
	if !ok {
		return nil
	}
	outR, outW, ok := pipePair()
	if !ok {
		syscall.Close(inR)
		syscall.Close(inW)
		return nil
	}
	fds := [3]uintptr{uintptr(inR), uintptr(outW), spawnDevnull}
	pid, _, serr := syscall.StartProcess(p.bin, p.argv,
		&syscall.ProcAttr{Files: fds[:], Env: spawnEnv})
	if serr != nil {
		syscall.Close(inR)
		syscall.Close(inW)
		syscall.Close(outR)
		syscall.Close(outW)
		return nil
	}
	syscall.Close(inR)
	syscall.Close(outW)
	writeAllFD(inW, src)
	syscall.Close(inW)
	out := buf[:0]
	readFailed := false
	for {
		if len(out) == cap(out) {
			grown := make([]byte, len(out), 2*cap(out)+1<<16)
			copy(grown, out)
			out = grown
		}
		n, rerr := syscall.Read(outR, out[len(out):cap(out)])
		if n > 0 {
			out = out[:len(out)+n]
		}
		if rerr == syscall.EINTR {
			continue
		}
		if rerr != nil {
			readFailed = true
			break
		}
		if n == 0 {
			break
		}
	}
	syscall.Close(outR)
	var ws syscall.WaitStatus
	for {
		_, werr := syscall.Wait4(pid, &ws, 0, nil)
		if werr == syscall.EINTR {
			continue
		}
		break
	}
	if (readFailed || !ws.Exited() || ws.ExitStatus() != 0) && len(out) == 0 {
		return nil
	}
	return out
}

type tsTree struct {
	recs []tsRec
}

var recPool sync.Pool

func (t *tsTree) free() {
	if c := cap(t.recs); c >= 1<<12 && c <= 1<<23 {
		b := t.recs[:c]
		recPool.Put(&b)
	}
	t.recs = nil
}

func (t *tsTree) root() tsNode {
	if t == nil || len(t.recs) == 0 {
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

func sameNode(a, b tsNode) bool { return a.t == b.t && a.i == b.i }

var (
	nsym     int
	symNames []string
	symNamed []bool

	symErrorMissing int
)

func init() {
	nsym = tsSymCount
	symNames = make([]string, nsym)
	symNamed = make([]bool, nsym)
	copy(symNames, tsSymNames[:])

	for s := 0; s < nsym; s++ {
		symNamed[s] = tsSymNamed[s] && tsSymVisible[s]
	}

	symErrorMissing = -1
	for s := 0; s < nsym; s++ {
		if tsSymNames[s] == "ERROR" {
			symErrorMissing = s
			break
		}
	}
	if symErrorMissing < 0 {
		panic("kind table lacks the reserved ERROR entry -- pinned grammar sources out of sync")
	}
}

func symOf(n tsNode) int {
	if !hasNode(n) {
		return symErrorMissing
	}
	s := int(n.t.recs[n.i].sym)
	if s >= len(symNames) {
		return symErrorMissing
	}
	return s
}

func isNamed(n tsNode) bool { return symNamed[symOf(n)] }

func symLookup(name string, named bool) int {
	s := tsSymLookupRaw(name, named)
	if s == 0 && name != "end" {
		s = tsSymLookupRaw(name, !named)
	}
	return int(s)
}

func tsSymLookupRaw(name string, named bool) uint16 {
	if named && len(name) <= 5 && "ERROR"[:len(name)] == name {
		return tsSymInvalid
	}
	for s := range tsSymCount {
		if (!tsSymVisible[s] && !tsSymSuper[s]) || tsSymNamed[s] != named {
			continue
		}
		if tsSymNames[s] == name {
			return tsSymPublic[s]
		}
	}
	return 0
}

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

var anonFields = func() map[uint16]map[uint16][]uint16 {
	symOfName := func(name string) uint16 {
		for s, n := range tsSymNames {
			if n == name {
				return uint16(s)
			}
		}
		return tsSymInvalid
	}
	m := make(map[uint16]map[uint16][]uint16, 32)
	for _, a := range tsAnonFieldList {
		f := fieldID(a.field)
		p, c := symOfName(a.kind), symOfName(a.token)
		if f == 0 || p == tsSymInvalid || c == tsSymInvalid {
			continue
		}
		inner := m[p]
		if inner == nil {
			inner = make(map[uint16][]uint16, 8)
			m[p] = inner
		}
		inner[c] = append(inner[c], f)
	}
	return m
}()

var (
	fLeft        = fieldID("left")
	fRight       = fieldID("right")
	fFunction    = fieldID("function")
	fArguments   = fieldID("arguments")
	fConstructor = fieldID("constructor")
	fName        = fieldID("name")
	fBody        = fieldID("body")
	fParameters  = fieldID("parameters")
	fCondition   = fieldID("condition")
	fProperty    = fieldID("property")
	fObject      = fieldID("object")
	fSource      = fieldID("source")
	fValue       = fieldID("value")
	fPattern     = fieldID("pattern")
	fAlternative = fieldID("alternative")
	fOperator    = fieldID("operator")
	fArgument    = fieldID("argument")
	fIndex       = fieldID("index")
	fAlias       = fieldID("alias")
	fKey         = fieldID("key")
	fParameter   = fieldID("parameter")
	fDeclaration = fieldID("declaration")
)

func startByte(n tsNode) int {
	if !hasNode(n) {
		return 0
	}
	return int(n.t.recs[n.i].start)
}
func endByte(n tsNode) int {
	if !hasNode(n) {
		return 0
	}
	return int(n.t.recs[n.i].end)
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

func hasError(n tsNode) bool {
	if !hasNode(n) {
		return false
	}
	return n.t.recs[n.i].flags&tsFlagErr != 0
}

func isMissing(n tsNode) bool {
	if !hasNode(n) {
		return false
	}
	return n.t.recs[n.i].flags&tsFlagMiss != 0
}

func field(n tsNode, f tsFieldID) (tsNode, bool) {
	if !hasNode(n) || f == 0 {
		return tsNode{}, false
	}
	for c, end := n.i+1, n.t.recs[n.i].subEnd; c < end; c = n.t.recs[c].subEnd {
		if n.t.recs[c].field == f {
			return tsNode{t: n.t, i: c}, true
		}
	}
	return tsNode{}, false
}

func parent(n tsNode) (tsNode, bool) {
	if !hasNode(n) {
		return tsNode{}, false
	}
	pi := n.t.recs[n.i].parent
	if pi < 0 {
		return tsNode{}, false
	}
	return tsNode{t: n.t, i: pi}, true
}

func prevSibling(n tsNode) (tsNode, bool) {
	if !hasNode(n) {
		return tsNode{}, false
	}
	pi := n.t.recs[n.i].parent
	if pi < 0 {
		return tsNode{}, false
	}
	for c, end := pi+1, n.t.recs[pi].subEnd; c < end; c = n.t.recs[c].subEnd {
		if n.t.recs[c].subEnd == n.i {
			return tsNode{t: n.t, i: c}, true
		}
	}
	return tsNode{}, false
}

func namedChildAt(n tsNode, i int) tsNode {
	if !hasNode(n) {
		return tsNode{}
	}
	for c, end := n.i+1, n.t.recs[n.i].subEnd; c < end; c = n.t.recs[c].subEnd {
		if isNamed(tsNode{t: n.t, i: c}) {
			if i == 0 {
				return tsNode{t: n.t, i: c}
			}
			i--
		}
	}
	return tsNode{}
}

type tsCursor struct {
	t     *tsTree
	stack []int32
	cur   int32

	dead   bool
	pooled bool
}

var cursorPool = sync.Pool{New: func() any { return new(tsCursor) }}

func (c *tsCursor) init(n tsNode) {
	c.pooled = false
	if !hasNode(n) {
		c.dead = true
		c.t = nil
		c.stack = c.stack[:0]
		return
	}
	c.dead = false
	c.t = n.t
	c.stack = append(c.stack[:0], n.i)
	c.cur = n.i
}

func cursorNew(n tsNode) *tsCursor {
	c := cursorPool.Get().(*tsCursor)
	c.init(n)
	return c
}

func (c *tsCursor) free() {
	if c.pooled {
		return
	}
	c.pooled = true
	c.dead = true
	c.t = nil
	c.stack = c.stack[:0]
	cursorPool.Put(c)
}

func (c *tsCursor) node() tsNode {
	if c.dead {
		return tsNode{}
	}
	return tsNode{t: c.t, i: c.cur}
}

func (c *tsCursor) first() bool {
	if c.dead || childCount(tsNode{t: c.t, i: c.cur}) == 0 {
		return false
	}
	c.stack = append(c.stack, c.cur)
	c.cur = c.cur + 1
	return true
}

func (c *tsCursor) next() bool {
	if c.dead || len(c.stack) == 0 {
		return false
	}
	parentEnd := c.t.recs[c.stack[len(c.stack)-1]].subEnd
	sib := c.t.recs[c.cur].subEnd
	if sib >= parentEnd {
		return false
	}
	c.cur = sib
	return true
}

func (c *tsCursor) up() bool {
	if c.dead || len(c.stack) <= 1 {
		return false
	}
	c.cur = c.stack[len(c.stack)-1]
	c.stack = c.stack[:len(c.stack)-1]
	return true
}

func forEachChild(n tsNode, fn func(c tsNode)) {
	var cur tsCursor
	cur.init(n)
	if !cur.first() {
		return
	}
	fn(cur.node())
	for cur.next() {
		fn(cur.node())
	}
}

func eachNamedChild(n tsNode, fn func(c tsNode)) {
	var cur tsCursor
	cur.init(n)
	if !cur.first() {
		return
	}
	for {
		k := cur.node()
		if isNamed(k) {
			fn(k)
		}
		if !cur.next() {
			return
		}
	}
}

func hasNamedChild(n tsNode) bool {
	var cur tsCursor
	cur.init(n)
	if !cur.first() {
		return false
	}
	for {
		if isNamed(cur.node()) {
			return true
		}
		if !cur.next() {
			return false
		}
	}
}

func countNamedChildren(n tsNode) int {
	c := 0
	eachNamedChild(n, func(tsNode) { c++ })
	return c
}

var tsErrKind = []byte("ERROR")

var namedSymByID, anonSymByID = func() (map[string]uint16, map[string]uint16) {
	named := make(map[string]uint16, tsSymCount)
	anon := make(map[string]uint16, 64)
	for s := range tsSymCount {
		m := &named
		if !tsSymNamed[s] {
			m = &anon
		}
		if _, dup := (*m)[tsSymNames[s]]; !dup {
			(*m)[tsSymNames[s]] = uint16(s)
		}
	}
	return named, anon
}()

type cstDecoder struct {
	starts     []int
	total      int
	totalWidth int
}

func digitsm1(n int) int {
	if n <= 0 {
		return 0
	}
	c := 0
	for n > 0 {
		n /= 10
		c++
	}
	return c - 1
}

var cstLineStarts []int

func decodeCST(out, src []byte) (*tsTree, error) {
	if cap(cstLineStarts) < 1024 {
		cstLineStarts = make([]int, 1, 1024)
	}
	d := &cstDecoder{
		starts: cstLineStarts[:1],
		total:  len(src),
	}
	for i, b := range src {
		if b == '\n' {
			d.starts = append(d.starts, i+1)
		}
	}
	cstLineStarts = d.starts

	d.totalWidth = 1
	{
		lineStart, row := 0, 0
		for i := 0; i <= len(src); i++ {
			if i < len(src) && src[i] != '\n' {
				continue
			}
			line := src[lineStart:i]
			if i == len(src) && len(line) == 0 {
				break
			}
			if n := len(line); n > 0 && line[n-1] == '\r' {
				line = line[:n-1]
			}
			if w := digitsm1(row) + digitsm1(utf8.RuneCount(line)) + 1; w > d.totalWidth {
				d.totalWidth = w
			}
			row++
			lineStart = i + 1
		}
	}

	want := bytes.Count(out, []byte{'\n'}) + 1
	var recs []tsRec
	if b, ok := recPool.Get().(*[]tsRec); ok && cap(*b) >= want {
		recs = (*b)[:0]
	} else {
		recs = make([]tsRec, 0, want)
	}
	type frame struct {
		depth int
		i     int32
	}
	var stack []frame

	nextFresh := 0x4000
	var freshNamed, freshAnon map[string]uint16
	internB := func(b []byte, kindNamed bool) uint16 {
		m, mf := namedSymByID, &freshNamed
		if !kindNamed {
			m, mf = anonSymByID, &freshAnon
		}
		if id, ok := m[string(b)]; ok {
			return id
		}
		if id, ok := (*mf)[string(b)]; ok {
			return id
		}
		if *mf == nil {
			*mf = make(map[string]uint16, 8)
		}
		id := uint16(nextFresh)
		nextFresh++
		(*mf)[string(b)] = id
		return id
	}
	var unquoteBuf []byte

	applyAnonField := func(p *tsRec, pi int32, c *tsRec, ci int32) {
		if c.field != 0 || c.flags&tsFlagNamed != 0 {
			return
		}
		cands := anonFields[p.sym][c.sym]
		if len(cands) == 0 {
			return
		}
		for _, f := range cands {
			used := false
			for j := pi + 1; j < ci; j++ {
				if recs[j].field == f {
					used = true
					break
				}
			}
			if !used {
				c.field = f
				return
			}
		}
		c.field = cands[0]
	}

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

		pad := 0
		for pad < len(rest) && rest[pad] == ' ' {
			pad++
		}
		padEnd := max(d.totalWidth-digitsm1(erow)-digitsm1(ecol), 1)
		depth := max((pad-padEnd)>>1, 0)
		rest = rest[pad:]

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

		if named && !missing && !bytes.Equal(kindB, tsErrKind) && srow == erow && scol == ecol {
			missing = true
		}

		if srow > 0xFFFF || erow > 0xFFFF {
			return nil, fmt.Errorf("node span %d..%d exceeds the %d-row record limit", srow, erow, 0xFFFF)
		}
		start := d.offset(int(srow), int(scol))
		end := d.offset(int(erow), int(ecol))

		rec := tsRec{
			sym:    internB(kindB, named),
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

		for len(stack) > 0 && stack[len(stack)-1].depth >= depth {
			popped := stack[len(stack)-1]
			recs[popped.i].subEnd = int32(idx)
			stack = stack[:len(stack)-1]
		}
		if len(stack) > 0 {
			pi := stack[len(stack)-1].i
			recs[idx].parent = pi
			applyAnonField(&recs[pi], pi, &recs[idx], idx)
		}
		stack = append(stack, frame{depth: depth, i: idx})
	}

	for len(stack) > 0 {
		popped := stack[len(stack)-1]
		recs[popped.i].subEnd = int32(len(recs))
		stack = stack[:len(stack)-1]
	}
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
	return &tsTree{recs: recs}, nil
}

func (d *cstDecoder) offset(row, col int) uint32 {
	if row >= len(d.starts) {
		return uint32(d.total)
	}
	if row < 0 {
		row = 0
	}
	off := min(d.starts[row]+col, d.total)
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

const maxPipelineDepth = 8

func defaultParseWorkers() int { return runtime.GOMAXPROCS(0) }

const symBlock = 2048

type symStore struct {
	blocks [][]int32

	ids   [][3]uint32
	pool  []sref
	strs  *[]byte
	mu    *sync.Mutex
	byStr map[string]uint32
}

func newSymStore() *symStore {
	return &symStore{byStr: make(map[string]uint32, 1024), mu: new(sync.Mutex)}
}

func (s *symStore) intern(v string) uint32 {
	if id, ok := s.byStr[v]; ok {
		return id
	}
	s.mu.Lock()
	defer s.mu.Unlock()
	if id, ok := s.byStr[v]; ok {
		return id
	}
	base := uint32(len(*s.strs))
	*s.strs = append(*s.strs, v...)
	r := sref{base, uint32(len(v))}
	id := uint32(len(s.pool))
	s.pool = append(s.pool, r)
	s.byStr[s.view(r)] = id
	return id
}

func (s *symStore) view(r sref) string {
	if r.n == 0 {
		return ""
	}
	return unsafe.String(&(*s.strs)[r.o], int(r.n))
}

func (s *symStore) n() int { return len(s.ids) }

func (s *symStore) grow() int {
	n := len(s.ids)
	s.ids = append(s.ids, [3]uint32{})
	if n%symBlock == 0 {
		s.blocks = append(s.blocks, make([]int32, symBlock*numStoreCols))
	}
	return n
}

func (s *symStore) at(i, col int) int32 {
	slot := colSlot[col]
	if slot < 0 {
		return 0
	}
	return s.blocks[i/symBlock][(i%symBlock)*numStoreCols+int(slot)]
}

func (s *symStore) set(i, col int, v int32) {
	slot := colSlot[col]
	if slot < 0 {
		return
	}
	s.blocks[i/symBlock][(i%symBlock)*numStoreCols+int(slot)] = v
}
func (s *symStore) inc(i, col int) { s.set(i, col, s.at(i, col)+1) }
func (s *symStore) scol(i, col int) string {
	t := textCol[col]
	if t < 0 {
		return ""
	}
	return s.view(s.pool[s.ids[i][t]])
}

func (s *symStore) setStr(i, slot int, v string) {
	if slot < 0 || slot >= len(s.ids[i]) {
		return
	}
	s.ids[i][slot] = s.intern(v)
}

const (
	tName = iota
	tKind
	tClass
)

var textCol [numSymCols]int

func init() {
	for i := range textCol {
		textCol[i] = -1
	}
	for i, c := range symCols {
		if c.kind == 2 {
			switch c.name {
			case "name":
				textCol[i] = tName
			case "kind":
				textCol[i] = tKind
			case "class_name":
				textCol[i] = tClass
			}
		}
	}
}

type nilInt = int32

const nullID nilInt = 0

const arenaLimit = 1<<32 - 1

type sref struct {
	o, n uint32
}

func (g *Graph) put(v string) sref {
	if v == "" {
		return sref{}
	}
	g.strsMu.Lock()
	defer g.strsMu.Unlock()
	if len(g.strs)+len(v) > arenaLimit {
		panic("string arena overflows 4GiB")
	}
	o := uint32(len(g.strs))
	g.strs = append(g.strs, v...)
	return sref{o, uint32(len(v))}
}

func (g *Graph) s(r sref) string {
	if r.n == 0 {
		return ""
	}
	return unsafe.String(&g.strs[r.o], int(r.n))
}

func (e *fileCtx) put(v string) sref {
	if v == "" {
		return sref{}
	}
	g := e.e.g
	g.strsMu.Lock()
	if len(g.strs)+len(v) > arenaLimit {
		g.strsMu.Unlock()
		panic("string arena overflows 4GiB")
	}
	o := uint32(len(g.strs))
	g.strs = append(g.strs, v...)
	g.strsMu.Unlock()
	return sref{o, uint32(len(v))}
}

func (e *fileCtx) s(r sref) string {
	if r.n == 0 {
		return ""
	}
	return unsafe.String(&e.e.g.strs[r.o], int(r.n))
}

func shiftStrs[T any](rows []T, offs []uintptr, base uint32) {
	if len(rows) == 0 || base == 0 {
		return
	}
	size := unsafe.Sizeof(rows[0])
	raw := unsafe.Slice((*byte)(unsafe.Pointer(&rows[0])), len(rows)*int(size))
	for i := range rows {
		row := raw[i*int(size) : (i+1)*int(size)]
		for _, o := range offs {
			r := (*sref)(unsafe.Pointer(&row[o]))
			r.o += base
		}
	}
}

type Module struct {
	id, nFiles, nSymbols, nPublic, sloc, fanIn, fanOut int32
	name, kind                                         sref
	instability                                        float64
}

type File struct {
	id, moduleID, bytes, lines, sloc, blank, comment, doc, maxLine int32
	path, dir, base, ext, lang, sha1                               sref
	parsed, isTest, isGen, isVendored                              bool
	nParseErrors, nMissing                                         int32
	parseMS                                                        float64
	nSymbols, nFuncs, nTypes, nImports                             int32
	totalCycles, maxCycles, totalRisk                              int32
}

type Param struct {
	symID, pos                                  int32
	name, typ                                   sref
	defaultNull                                 bool
	optional, variadic, ref, mut, nullable, gen bool
	untyped, depth                              int32
}

type FieldRow struct {
	symID, ordinal, line                        int32
	name, typ, vis                              sref
	static, konst, mut, nullable, coll, untyped bool
	hasDefault, depth                           int32
}

type Edge struct {
	caller, callee, nCalls    int32
	sameFile, sameMod, isSelf bool
}

type Callsite struct{ caller, callee, line int32 }

type Unresolved struct {
	caller     int32
	name       sref
	n, firstLn int32
}

type Import struct {
	id, fileID, targetID, line, isExternal, isRel, isWild, isTypeOnly int32
	isDynamic, nNames                                                 int32
	target, alias, kind                                               sref
	aliasNull                                                         bool
}

type Hazard struct {
	symID             int32
	pattern, category sref
	n, firstLine      int32
}

type Attribute struct {
	id, symID, fileID, line int32
	name, args              sref
}

type Literal struct {
	id, symID, fileID, line int32
	kind, value             sref
	isMagic                 bool
}

type EnumMember struct {
	symID, ordinal, nFields int32
	name, value             sref
	valueNull               bool
}

type Marker struct {
	id, fileID, symID, line int32
	kind, text              sref
}

type ClassRow struct {
	symID, fileID                                       int32
	extends                                             sref
	nMethods, nStatic, nGetters, nSetters, nPrivate     int32
	nFields, nArrow, nComputed, hasCtor, hasStaticBlock int32
	exported, component                                 bool
}

type ExportRow struct {
	id, fileID, symID, sourceID, line int32
	name, localName, kind, source     sref
	reexport, star, cjs               bool
}

type ImportName struct {
	id, fileID, sourceID, line int32
	source, name, alias        sref
	ns, def, external          bool
}

type Listener struct {
	id, fileID, symID, line                   int32
	op, api, family, target, event, handler   sref
	inline, signal, atModule, inLoop, inClean bool
}

type Timer struct {
	id, fileID, symID, line               int32
	op, api, kind, handle                 sref
	assigned, repeating, unrefd, cbString bool
	atModule, inLoop, asyncCB             bool
}

type ModuleCache struct {
	id, fileID, line               int32
	name, ctor, writers            sref
	weak, exported, konst          bool
	nWrites, nDrops, nReads, nSize int32
	hasMax                         bool
}

type DepRow struct {
	id, dev            int32
	name, version, dir sref
}

type JSXComp struct {
	id, fileID, symID, line, nAttrs, nSpread int32
	tag                                      sref
	component, hasKey, danger, inLoop        bool

	inlineObj, inlineFn int32
}

type HookRow struct {
	id, fileID, symID, line, nDeps        int32
	name                                  sref
	builtin, hasDeps, cleanup             bool
	inLoop, inCond, regListener, regTimer bool
}

type UserInput struct {
	id, symID, fileID, line int32
	kind, varName           sref
	inLoop                  bool
}

type Route struct {
	id, fileID, symID, line, nMw int32
	method, path, handler        sref
	inline, async                bool
}

type Secret struct {
	id, symID, fileID, line int32
	value                   sref
}

type metaRow [2]sref

func (m Module) Name(g *Graph) string     { return g.s(m.name) }
func (m Module) Kind(g *Graph) string     { return g.s(m.kind) }
func (f File) Path(g *Graph) string       { return g.s(f.path) }
func (f File) Dir(g *Graph) string        { return g.s(f.dir) }
func (f File) Base(g *Graph) string       { return g.s(f.base) }
func (f File) Ext(g *Graph) string        { return g.s(f.ext) }
func (f File) Lang(g *Graph) string       { return g.s(f.lang) }
func (f File) Sha1(g *Graph) string       { return g.s(f.sha1) }
func (p Param) Name(g *Graph) string      { return g.s(p.name) }
func (p Param) Typ(g *Graph) string       { return g.s(p.typ) }
func (f FieldRow) Name(g *Graph) string   { return g.s(f.name) }
func (f FieldRow) Typ(g *Graph) string    { return g.s(f.typ) }
func (f FieldRow) Vis(g *Graph) string    { return g.s(f.vis) }
func (u Unresolved) Name(g *Graph) string { return g.s(u.name) }
func (i Import) Target(g *Graph) string   { return g.s(i.target) }
func (i Import) Alias(g *Graph) string    { return g.s(i.alias) }
func (i Import) Kind(g *Graph) string     { return g.s(i.kind) }
func (h Hazard) Pattern(g *Graph) string  { return g.s(h.pattern) }
func (h Hazard) Category(g *Graph) string { return g.s(h.category) }
func (a Attribute) Name(g *Graph) string  { return g.s(a.name) }
func (a Attribute) Args(g *Graph) string  { return g.s(a.args) }
func (l Literal) Kind(g *Graph) string    { return g.s(l.kind) }
func (l Literal) Value(g *Graph) string   { return g.s(l.value) }
func (e EnumMember) Name(g *Graph) string { return g.s(e.name) }
func (e EnumMember) Value(g *Graph) string {
	return g.s(e.value)
}
func (m Marker) Kind(g *Graph) string { return g.s(m.kind) }
func (m Marker) Text(g *Graph) string { return g.s(m.text) }
func (c ClassRow) Extends(g *Graph) string {
	return g.s(c.extends)
}
func (e ExportRow) Name(g *Graph) string { return g.s(e.name) }
func (e ExportRow) LocalName(g *Graph) string {
	return g.s(e.localName)
}
func (e ExportRow) Kind(g *Graph) string { return g.s(e.kind) }
func (e ExportRow) Source(g *Graph) string {
	return g.s(e.source)
}
func (n ImportName) Source(g *Graph) string { return g.s(n.source) }
func (n ImportName) Name(g *Graph) string   { return g.s(n.name) }
func (n ImportName) Alias(g *Graph) string  { return g.s(n.alias) }
func (l Listener) Op(g *Graph) string       { return g.s(l.op) }
func (l Listener) Api(g *Graph) string      { return g.s(l.api) }
func (l Listener) Family(g *Graph) string   { return g.s(l.family) }
func (l Listener) Target(g *Graph) string   { return g.s(l.target) }
func (l Listener) Event(g *Graph) string    { return g.s(l.event) }
func (l Listener) Handler(g *Graph) string  { return g.s(l.handler) }
func (t Timer) Op(g *Graph) string          { return g.s(t.op) }
func (t Timer) Api(g *Graph) string         { return g.s(t.api) }
func (t Timer) Kind(g *Graph) string        { return g.s(t.kind) }
func (t Timer) Handle(g *Graph) string      { return g.s(t.handle) }
func (c ModuleCache) Name(g *Graph) string  { return g.s(c.name) }
func (c ModuleCache) Ctor(g *Graph) string  { return g.s(c.ctor) }
func (c ModuleCache) Writers(g *Graph) string {
	return g.s(c.writers)
}
func (d DepRow) Name(g *Graph) string    { return g.s(d.name) }
func (d DepRow) Version(g *Graph) string { return g.s(d.version) }
func (d DepRow) Dir(g *Graph) string     { return g.s(d.dir) }
func (j JSXComp) Tag(g *Graph) string    { return g.s(j.tag) }
func (h HookRow) Name(g *Graph) string   { return g.s(h.name) }
func (u UserInput) Kind(g *Graph) string { return g.s(u.kind) }
func (u UserInput) VarName(g *Graph) string {
	return g.s(u.varName)
}
func (r Route) Method(g *Graph) string  { return g.s(r.method) }
func (r Route) Path(g *Graph) string    { return g.s(r.path) }
func (r Route) Handler(g *Graph) string { return g.s(r.handler) }
func (s Secret) Value(g *Graph) string  { return g.s(s.value) }

type Graph struct {
	Meta   []metaRow
	strs   []byte
	strsMu sync.Mutex

	Modules []Module
	Files   []File

	Syms *symStore

	Params     []Param
	Fields     []FieldRow
	Edges      []Edge
	Callsites  []Callsite
	Unresolved []Unresolved
	Imports    []Import
	Hazards    []Hazard
	Attrs      []Attribute
	Literals   []Literal
	Enums      []EnumMember
	Markers    []Marker

	Classes     []ClassRow
	Exports     []ExportRow
	ImportNames []ImportName
	Listeners   []Listener
	Timers      []Timer
	Caches      []ModuleCache
	Deps        []DepRow
	JSX         []JSXComp
	Hooks       []HookRow
	UserInput   []UserInput
	Routes      []Route
	Secrets     []Secret

	entHooks     []int32
	hazBySym     [][]int32
	uiBySym      []int32
	uiFormBySym  []int32
	fanIn        []int32
	callersBySym [][]int32

	symsByFile map[int32][]int32

	hndFile    []int32
	hndSpan    []int32
	fileByPath map[string]int32
	modByName  map[string]int32

	astTrees []*tsTree
	astBlob  []byte
}

func (g *Graph) nSym() int          { return g.Syms.n() }
func (g *Graph) name(id int) string { return g.Syms.scol(id, cNAME) }
func (g *Graph) kind(id int) string { return g.Syms.scol(id, cKIND) }
func (g *Graph) at(fid, line int32) string {
	return g.s(g.Files[fid-1].path) + ":" + strconv.Itoa(int(line))
}

func (g *Graph) modName(mid int32) string {
	if mid == nullID {
		return ""
	}
	return g.s(g.Modules[mid-1].name)
}

func (g *Graph) filePath(fid int32) string {
	if fid == nullID || int(fid) > len(g.Files) {
		return ""
	}
	return g.s(g.Files[fid-1].path)
}
func (f *File) clean() bool { return !f.isTest && !f.isGen }

func (g *Graph) buildIndex() {
	n := g.nSym()
	g.entHooks = make([]int32, n+1)
	g.hazBySym = make([][]int32, n+1)
	g.uiBySym = make([]int32, n+1)
	g.uiFormBySym = make([]int32, n+1)
	g.symsByFile = make(map[int32][]int32)
	for id := range n {
		fid := g.Syms.at(id, cFILEID)
		g.symsByFile[fid] = append(g.symsByFile[fid], int32(id))
	}
	for i := range g.Hooks {
		if int(g.Hooks[i].symID) < n {
			g.entHooks[g.Hooks[i].symID]++
		}
	}
	for i := range g.UserInput {
		if int(g.UserInput[i].symID) < n {
			g.uiBySym[g.UserInput[i].symID]++
			if g.s(g.UserInput[i].kind) == "form" {
				g.uiFormBySym[g.UserInput[i].symID]++
			}
		}
	}

	g.fanIn = make([]int32, n+1)
	g.callersBySym = make([][]int32, n+1)
	for i := range g.Edges {
		if g.Edges[i].isSelf {
			continue
		}
		g.fanIn[g.Edges[i].callee]++
		g.callersBySym[g.Edges[i].callee] = append(g.callersBySym[g.Edges[i].callee], g.Edges[i].caller)
	}
	g.fileByPath = make(map[string]int32, len(g.Files))
	for i := range g.Files {
		g.fileByPath[g.s(g.Files[i].path)] = int32(i + 1)
	}
	g.modByName = make(map[string]int32, len(g.Modules))
	for i := range g.Modules {
		g.modByName[g.s(g.Modules[i].name)] = int32(i + 1)
	}
}

const (
	kInt = iota
	kFloat
	kText
	kNull
)

type Cell struct {
	s    string
	i    int64
	f    float64
	kind uint8
}

func I(v int) Cell     { return Cell{i: int64(v), kind: kInt} }
func I32(v int32) Cell { return Cell{i: int64(v), kind: kInt} }
func I64(v int64) Cell { return Cell{i: v, kind: kInt} }
func F(v float64) Cell { return Cell{f: v, kind: kFloat} }
func S(v string) Cell  { return Cell{s: v, kind: kText} }
func Null() Cell       { return Cell{kind: kNull} }
func MaybeS(v string) Cell {
	if v == "" {
		return Cell{kind: kNull}
	}
	return Cell{s: v, kind: kText}
}

func (c Cell) str() string {
	switch c.kind {
	case kInt:
		return strconv.FormatInt(c.i, 10)
	case kFloat:
		return cgReprFloat(c.f)
	case kNull:
		return "-"
	}
	return c.s
}

type Table struct {
	Cols []string
	Rows [][]Cell
}

func (t *Table) add(cells ...Cell) { t.Rows = append(t.Rows, cells) }

func (t *Table) sortIdx(terms ...orderTerm) []int {
	idx := make([]int, len(t.Rows))
	for i := range idx {
		idx[i] = i
	}
	orderBy(idx, terms)
	return idx
}

func (t *Table) take(terms []orderTerm, limit int) {
	idx := t.sortIdx(terms...)
	if limit >= 0 && limit < len(idx) {
		idx = idx[:limit]
	}
	rows := make([][]Cell, len(idx))
	for i, j := range idx {
		rows[i] = t.Rows[j]
	}
	t.Rows = rows
}

type Question struct {
	Name, Title, Notes string
	Run                func(g *Graph, mod string, lim int) *Table
}

func maxI(a, b int) int {
	if a > b {
		return a
	}
	return b
}

const grammarVersion = "go-tree-sitter 0.25.0 + tree-sitter-javascript 0.25.0"

type columnShape struct {
	name string
	kind string
	opt  bool
}

type tableShape struct {
	name string
	note string
	cols []columnShape
}

var graphShape = []tableShape{
	{name: "attributes",
		note: "the annotation/attribute forms this language has",
		cols: []columnShape{
			{"id", "int", false},
			{"symbol_id", "int", true},
			{"file_id", "int", false},
			{"name", "text", false},
			{"args", "text", true},
			{"line", "int", false},
		}},
	{name: "callsites",
		note: "every distinct line a resolved call was seen on",
		cols: []columnShape{
			{"caller_id", "int", false},
			{"callee_id", "int", false},
			{"line", "int", false},
		}},
	{name: "classes",
		note: "class-shaped declarations: class, constructor, prototype, object literal",
		cols: []columnShape{
			{"symbol_id", "int", false},
			{"file_id", "int", false},
			{"extends", "text", false},
			{"n_methods", "int", false},
			{"n_static", "int", false},
			{"n_getters", "int", false},
			{"n_setters", "int", false},
			{"n_private", "int", false},
			{"n_fields", "int", false},
			{"n_arrow_fields", "int", false},
			{"n_computed_members", "int", false},
			{"has_constructor", "int", false},
			{"has_static_block", "int", false},
			{"is_exported", "int", false},
			{"is_component", "int", false},
		}},
	{name: "deps",
		note: "dependencies declared in the manifest, against what is used",
		cols: []columnShape{
			{"id", "int", false},
			{"name", "text", false},
			{"version", "text", false},
			{"is_dev", "int", false},
			{"dir", "text", false},
		}},
	{name: "edges",
		note: "the call graph, one row per (caller, callee)",
		cols: []columnShape{
			{"caller_id", "int", false},
			{"callee_id", "int", false},
			{"n_calls", "int", false},
			{"same_file", "int", false},
			{"same_module", "int", false},
			{"is_self", "int", false},
		}},
	{name: "enum_members",
		note: "the cases of an enum, with their values",
		cols: []columnShape{
			{"symbol_id", "int", false},
			{"ordinal", "int", false},
			{"name", "text", false},
			{"value", "text", true},
			{"n_fields", "int", false},
		}},
	{name: "exports",
		note: "an exported name: what it is, and whether it is re-exported",
		cols: []columnShape{
			{"id", "int", false},
			{"file_id", "int", false},
			{"symbol_id", "int", true},
			{"name", "text", false},
			{"local_name", "text", false},
			{"kind", "text", false},
			{"line", "int", false},
			{"source", "text", false},
			{"source_id", "int", true},
			{"is_reexport", "int", false},
			{"is_star", "int", false},
			{"is_cjs", "int", false},
		}},
	{name: "fields",
		note: "declared properties and constants",
		cols: []columnShape{
			{"symbol_id", "int", false},
			{"ordinal", "int", false},
			{"name", "text", false},
			{"type", "text", false},
			{"visibility", "text", false},
			{"line", "int", false},
			{"is_static", "int", false},
			{"is_const", "int", false},
			{"is_mutable", "int", false},
			{"is_nullable", "int", false},
			{"is_collection", "int", false},
			{"is_untyped", "int", false},
			{"has_default", "int", false},
			{"type_depth", "int", false},
		}},
	{name: "files",
		note: "one row per discovered source file",
		cols: []columnShape{
			{"id", "int", false},
			{"path", "text", false},
			{"dir", "text", false},
			{"basename", "text", false},
			{"ext", "text", false},
			{"lang", "text", false},
			{"module_id", "int", true},
			{"bytes", "int", false},
			{"lines", "int", false},
			{"sloc", "int", false},
			{"blank_lines", "int", false},
			{"comment_lines", "int", false},
			{"doc_lines", "int", false},
			{"max_line_len", "int", false},
			{"sha1", "text", false},
			{"parsed", "int", false},
			{"is_test", "int", false},
			{"is_generated", "int", false},
			{"is_vendored", "int", false},
			{"n_parse_errors", "int", false},
			{"n_missing_nodes", "int", false},
			{"parse_ms", "real", false},
			{"n_symbols", "int", false},
			{"n_functions", "int", false},
			{"n_types", "int", false},
			{"n_imports", "int", false},
			{"total_cyclo", "int", false},
			{"max_cyclo", "int", false},
			{"total_risk", "int", false},
		}},
	{name: "hazards",
		note: "dangerous call families, one row per (symbol, pattern)",
		cols: []columnShape{
			{"symbol_id", "int", false},
			{"pattern", "text", false},
			{"category", "text", false},
			{"n", "int", false},
			{"first_line", "int", false},
		}},
	{name: "hooks",
		note: "a framework lifecycle hook and the method it points at",
		cols: []columnShape{
			{"id", "int", false},
			{"file_id", "int", false},
			{"symbol_id", "int", true},
			{"line", "int", false},
			{"name", "text", false},
			{"is_builtin", "int", false},
			{"has_dep_array", "int", false},
			{"n_deps", "int", false},
			{"has_cleanup", "int", false},
			{"in_loop", "int", false},
			{"in_condition", "int", false},
			{"registers_listener", "int", false},
			{"registers_timer", "int", false},
		}},
	{name: "import_names",
		note: "the individual names one import binds",
		cols: []columnShape{
			{"id", "int", false},
			{"file_id", "int", false},
			{"source", "text", false},
			{"source_id", "int", true},
			{"name", "text", false},
			{"alias", "text", false},
			{"line", "int", false},
			{"is_namespace", "int", false},
			{"is_default", "int", false},
			{"is_external", "int", false},
		}},
	{name: "imports",
		note: "use statements and includes",
		cols: []columnShape{
			{"id", "int", false},
			{"file_id", "int", false},
			{"target", "text", false},
			{"target_id", "int", true},
			{"alias", "text", true},
			{"kind", "text", false},
			{"line", "int", false},
			{"is_external", "int", false},
			{"is_relative", "int", false},
			{"is_wildcard", "int", false},
			{"is_type_only", "int", false},
			{"is_dynamic", "int", false},
			{"n_names", "int", false},
		}},
	{name: "jsx_components",
		note: "a JSX element: the component, and the props passed to it",
		cols: []columnShape{
			{"id", "int", false},
			{"file_id", "int", false},
			{"symbol_id", "int", true},
			{"line", "int", false},
			{"tag", "text", false},
			{"is_component", "int", false},
			{"n_attrs", "int", false},
			{"n_spread", "int", false},
			{"has_key", "int", false},
			{"inline_object_props", "int", false},
			{"inline_fn_props", "int", false},
			{"has_dangerous_html", "int", false},
			{"in_loop", "int", false},
		}},
	{name: "listeners",
		note: "an event listener registration: target, event, handler",
		cols: []columnShape{
			{"id", "int", false},
			{"file_id", "int", false},
			{"symbol_id", "int", true},
			{"line", "int", false},
			{"op", "text", false},
			{"api", "text", false},
			{"family", "text", false},
			{"target", "text", false},
			{"event", "text", false},
			{"handler", "text", false},
			{"handler_inline", "int", false},
			{"has_signal", "int", false},
			{"at_module_scope", "int", false},
			{"in_loop", "int", false},
			{"in_cleanup", "int", false},
		}},
	{name: "literals",
		note: "string and numeric literals inside a body",
		cols: []columnShape{
			{"id", "int", false},
			{"symbol_id", "int", true},
			{"file_id", "int", false},
			{"kind", "text", false},
			{"value", "text", false},
			{"line", "int", false},
			{"is_magic", "int", false},
		}},
	{name: "locals",
		note: "declared but never written: there is no local-variable inventory",
		cols: []columnShape{
			{"symbol_id", "int", false},
			{"ordinal", "int", false},
			{"name", "text", false},
			{"type", "text", false},
			{"line", "int", false},
			{"is_const", "int", false},
			{"is_mutable", "int", false},
			{"is_untyped", "int", false},
			{"has_init", "int", false},
			{"in_loop", "int", false},
			{"scope_depth", "int", false},
		}},
	{name: "markers",
		note: "TODO/FIXME/HACK and friends",
		cols: []columnShape{
			{"id", "int", false},
			{"file_id", "int", false},
			{"symbol_id", "int", true},
			{"kind", "text", false},
			{"line", "int", false},
			{"text", "text", true},
		}},
	{name: "meta",
		note: "run facts: what was parsed, with what, and what was skipped",
		cols: []columnShape{
			{"key", "text", false},
			{"value", "text", false},
		}},
	{name: "module_caches",
		note: "a module-level cache: its key, its value, and its bounds",
		cols: []columnShape{
			{"id", "int", false},
			{"file_id", "int", false},
			{"line", "int", false},
			{"name", "text", false},
			{"ctor", "text", false},
			{"is_weak", "int", false},
			{"is_exported", "int", false},
			{"is_const", "int", false},
			{"n_writes", "int", false},
			{"n_drops", "int", false},
			{"n_reads", "int", false},
			{"n_size_checks", "int", false},
			{"has_max", "int", false},
			{"writer_fns", "text", false},
		}},
	{name: "modules",
		note: "grouping key for files: the first two directory levels",
		cols: []columnShape{
			{"id", "int", false},
			{"name", "text", false},
			{"kind", "text", false},
			{"n_files", "int", false},
			{"n_symbols", "int", false},
			{"n_public", "int", false},
			{"sloc", "int", false},
			{"fan_in", "int", false},
			{"fan_out", "int", false},
			{"instability", "real", false},
		}},
	{name: "params",
		note: "parameter list, keyed by symbol",
		cols: []columnShape{
			{"symbol_id", "int", false},
			{"pos", "int", false},
			{"name", "text", true},
			{"type", "text", false},
			{"default_value", "text", true},
			{"is_optional", "int", false},
			{"is_variadic", "int", false},
			{"is_ref", "int", false},
			{"is_mutable", "int", false},
			{"is_nullable", "int", false},
			{"is_generic", "int", false},
			{"is_untyped", "int", false},
			{"type_depth", "int", false},
		}},
	{name: "routes",
		note: "a route: the method, the path, and the handler behind it",
		cols: []columnShape{
			{"id", "int", false},
			{"file_id", "int", false},
			{"symbol_id", "int", true},
			{"line", "int", false},
			{"method", "text", false},
			{"path", "text", false},
			{"handler", "text", false},
			{"handler_inline", "int", false},
			{"handler_async", "int", false},
			{"n_middlewares", "int", false},
		}},
	{name: "secret_candidates",
		note: "credential-shaped string literals",
		cols: []columnShape{
			{"id", "int", false},
			{"symbol_id", "int", true},
			{"file_id", "int", false},
			{"value", "text", false},
			{"line", "int", false},
		}},
	{name: "sym_fts",
		note: "a contentless full-text index over (name, qual_name, signature): every column reads back empty, and the four shadow b-tree tables beside it are not reproduced at all",
		cols: []columnShape{
			{"name", "any", true},
			{"qual_name", "any", true},
			{"signature", "any", true},
		}},
	{name: "symbols",
		note: "the hub: every function, method, closure, hook and type",
		cols: symShape()},
	{name: "timers",
		note: "a timer or interval: what it schedules and how often",
		cols: []columnShape{
			{"id", "int", false},
			{"file_id", "int", false},
			{"symbol_id", "int", true},
			{"line", "int", false},
			{"op", "text", false},
			{"api", "text", false},
			{"kind", "text", false},
			{"handle", "text", false},
			{"is_assigned", "int", false},
			{"is_repeating", "int", false},
			{"is_unrefd", "int", false},
			{"callback_is_string", "int", false},
			{"at_module_scope", "int", false},
			{"in_loop", "int", false},
			{"is_async_cb", "int", false},
		}},
	{name: "unresolved_calls",
		note: "a call we saw but could not point at a definition",
		cols: []columnShape{
			{"caller_id", "int", false},
			{"name", "text", false},
			{"n", "int", false},
			{"first_line", "int", false},
		}},
	{name: "user_input_sites",
		note: "a value that came in from outside the program: an\n                         argument, an environment variable, a request field",
		cols: []columnShape{
			{"id", "int", false},
			{"symbol_id", "int", true},
			{"file_id", "int", false},
			{"var", "text", false},
			{"kind", "text", false},
			{"line", "int", false},
			{"in_loop", "int", false},
		}},
}

func symShape() []columnShape {
	out := make([]columnShape, 0, numStoreCols+1)
	for c, sc := range symCols {
		if colSlot[c] < 0 && c != cID {
			continue
		}
		kind := "int"
		opt := false
		if sc.kind == 2 {
			kind = "text"
		}
		if c == cMODULEID || c == cPARENTID {
			opt = true
		}
		out = append(out, columnShape{sc.name, kind, opt})
	}
	return out
}

func schemaNative() string {
	var b strings.Builder
	for _, t := range graphShape {
		b.WriteString("table ")
		b.WriteString(t.name)
		b.WriteString(" -- ")
		b.WriteString(t.note)
		b.WriteByte('\n')
		line := "  "
		for i, c := range t.cols {
			piece := c.name
			if c.opt {
				piece += "?"
			}
			piece += " " + c.kind
			if i > 0 && len(line)+1+len(piece) > schemaLine {
				b.WriteString(line)
				b.WriteByte('\n')
				line = "  "
			}
			if len(line) > 2 {
				line += " "
			}
			line += piece
		}
		if len(line) > 2 {
			b.WriteString(line)
			b.WriteByte('\n')
		}
		b.WriteByte('\n')
	}
	b.WriteString("no query layer: there is no expression language here. Every\n")
	b.WriteString("question is a loop over a slice, a lookup of a column, and a reduce.\n")
	return b.String()
}

const schemaLine = 78

var queries = []Question{
	{Name: "retention-leak-frontier", Title: "Listeners and timers registered with nothing in the module that undoes it", Notes: "ANSWERS the gap no JavaScript linter fills. ESLint core (199 rules),\n     typescript-eslint (134), unicorn (336), Biome (436), oxlint (847) and\n     CodeQL-JS (200) were all read: not one of them pairs an add with a\n     remove or a setInterval with a clearInterval. This does, per module,\n     and every row is a reference the garbage collector can never reclaim.\nACT unremovable = 1 is the strongest signal on the page and means the\n     teardown CANNOT be written later, not that somebody forgot. For a\n     listener it is an anonymous handler -- no identity, so\n     removeEventListener has nothing to name. For a timer it is a\n     discarded handle -- clearInterval has no id to pass. Give the handler\n     a name, keep the handle, or pass { signal } from an AbortController\n     (rows already covered by a signal are excluded entirely).\n     module_scope = 1 registers at import time and lives as long as the\n     process -- in Node that alone keeps the process alive unless the timer\n     is unref'd. in_loop = 1 registers once per element.\nMISLEADS a listener on an object that dies with the page, a `once`, or an\n     interval in a daemon that is SUPPOSED to run forever, are all correct\n     and all appear here. A teardown written in a DIFFERENT module is\n     invisible: pairing is per-file on purpose, because a cross-file rule\n     matches by name and would let any off() anywhere cancel every on().\n     Recursive setTimeout is a repeating timer this does not classify as\n     one, so the true timer count is higher than shown."},
	{Name: "unbounded-module-cache", Title: "Module-scope containers that are written to and never emptied", Notes: "ANSWERS the other half of the linter gap: a Map, Set, object or array\n     declared at module scope lives as long as the process, and if nothing\n     ever deletes, clears, evicts or bounds it, it is a memory leak with a\n     growth rate equal to your traffic. No rule in any of the six\n     JavaScript toolchains surveyed checks this.\nACT give it a bound. An LRU with a max size, a WeakMap keyed by the object\n     it describes, or an explicit delete on the way out. has_max = 1 means\n     something already reads .size or .length, which is usually an eviction\n     test and is the counter-evidence.\n     is_weak = 1 rows are already collectable and are excluded entirely.\nMISLEADS init_only = 1 means every write happens at module scope: a lookup\n     table or a registry of built-in plugins, bounded by the source rather\n     than by traffic, and fine. Those are sorted to the bottom rather than\n     hidden, because 'written once at startup' is a judgement about intent\n     and this only measures position. Read writes next to writer_fns: one\n     writer in an init function is harmless, a writer reached from a\n     request handler is not. This counts textual property access on the\n     declared name, so a cache passed to another module as an argument and\n     written there shows zero writes here."},
	{Name: "event-loop-block-frontier", Title: "Blocking *Sync calls reachable from a request handler, up to 4 hops", Notes: "ANSWERS which synchronous file, crypto or child-process call sits on a\n     request path. Node serves every request on one thread: a 40ms\n     readFileSync in a handler is 40ms of total server unavailability, not\n     40ms for that one client.\nACT switch to the promise form (fs.promises, await), or hoist the call to\n     startup where blocking is free. execSync and the pbkdf2Sync/scryptSync\n     family are the worst: they block for the full duration of a process\n     spawn or a deliberate key-derivation delay.\nMISLEADS depth is capped at 4 hops (the WITH RECURSIVE bound below) and\n     only RESOLVED edges are walked, so this is a floor, never a ceiling.\n     A handler registered by a router this cannot see has no is_handler\n     flag and its whole subtree is missing from this answer -- check\n     graph-blindspots for the module first. A *Sync call in a CLI or a\n     build script is entirely correct and appears here only if something\n     mistook a CLI entry for a handler."},
	{Name: "await-in-loop-serialized", Title: "await inside a loop where nothing on the path batches with Promise.all", Notes: "ANSWERS the single most common JavaScript performance bug: N awaits in\n     sequence take the sum of N latencies when they could take the max.\n     Ten 50ms round trips is 500ms serial and 50ms batched.\nACT collect the promises and await Promise.all (or allSettled) once. Do NOT\n     do this blindly: an await in a loop is CORRECT when each iteration\n     depends on the previous one, when you are deliberately rate-limiting,\n     or when unbounded concurrency would exhaust a connection pool.\nMISLEADS trip count is invisible here. A loop over three config entries\n     costs nothing. `batches_anywhere` counts Promise.all in the same\n     function, which is only weak evidence -- the batching may be for a\n     different loop entirely."},
	{Name: "floating-promise-crossmodule", Title: "Async functions whose callers never await them, across module lines", Notes: "ANSWERS the cross-module floating promise. typescript-eslint's\n     no-floating-promises is the closest existing rule and it needs full\n     type information and works one file at a time; this works on the call\n     graph and crosses files, which is where the real ones hide.\nACT an un-awaited async call means errors surface as an unhandled rejection\n     (which terminates the process by default since Node 15) and the work\n     may still be running after the caller returned. Either await it,\n     return it, or attach .catch and say in a comment that it is\n     deliberately detached.\nMISLEADS a caller that is itself synchronous cannot await, so fire-and-\n     forget is sometimes the only option -- caller_async tells you which\n     case you are in. discarded_calls counts calls in STATEMENT position in\n     the caller and cannot say which of them is this callee, so a caller\n     with one floating call and three awaited ones still appears. Read it\n     as a shortlist, not a verdict."},
	{Name: "proto-pollution-frontier", Title: "Recursive writers reachable from parsed request input, up to 4 hops", Notes: "ANSWERS the shape behind every prototype-pollution CVE in the npm registry:\n     a deep merge, a `set(obj, path, value)` helper, or an\n     `obj[k1][k2] = v` write, fed a key that came out of JSON.parse of a\n     request body. Setting `__proto__` there changes every object in the\n     process.\nACT guard the key. Reject __proto__, constructor and prototype explicitly,\n     or build the target with Object.create(null), or use a Map. A single\n     `if (key === '__proto__') continue` closes the whole class.\n     dynamic_writes counts `obj[expr] = v` where expr is not a literal --\n     that is the exact write that can be steered.\nMISLEADS this cannot see the guard. A merge helper that ALREADY rejects\n     __proto__ still appears, because proving the guard covers every path\n     needs data flow this does not have. Depth is capped at 4 hops (the\n     bound is in the recursive CTE below) and only resolved edges are\n     walked, so a helper reached through a plugin registry is missing."},
	{Name: "redos-frontier", Title: "Regex literals with nested quantifiers reachable from untrusted input", Notes: "ANSWERS which catastrophic-backtracking patterns an attacker can actually\n     reach. `(a+)+`, `(\\w*)*` and `(x|x)+` take exponential time on a\n     crafted non-match, and in Node that is the whole event loop, so one\n     request takes the server down.\nACT rewrite the pattern to remove the nested quantifier, anchor it, or cap\n     the input length before matching. A regex compiled inside a loop\n     (regex_in_loop) also recompiles every iteration, which is a separate\n     and easier win.\nMISLEADS the detector is syntactic and errs toward reporting: `(ab+)+c`\n     matches the nested-quantifier shape but is linear in practice because\n     the suffix disambiguates. Confirming a finding means timing the actual\n     pattern against a crafted input -- treat every row as a candidate for\n     that test, not as a vulnerability. Regex/division ambiguity is\n     resolved by the parser, so nothing here is a mis-lexed division.\n     hops = -1 means the pattern is NOT reachable from any known entry\n     by a resolved edge, which is weaker evidence of safety than it looks:\n     an unreached pattern in a module full of dynamic dispatch may simply\n     be one this could not follow. Rows where in_fn is blank are literals\n     declared at module scope, which is where most regexes actually live."},
	{Name: "dom-sink-frontier", Title: "innerHTML and friends reachable from untrusted input, up to 4 hops", Notes: "ANSWERS the XSS question the call graph can answer: which HTML sink is\n     reachable from a function that handles a request or parses JSON. A\n     per-file linter sees the sink; it cannot see that the string arrived\n     from a query parameter three frames up.\nACT use textContent, or a sanitiser at the boundary. React's\n     dangerouslySetInnerHTML is named that way on purpose and counts here.\n     hops = 0 means the sink and the untrusted input are in the same\n     function, which is the easiest to confirm and the easiest to fix.\nMISLEADS reachability is not taint. A sink fed a constant template, or fed\n     output that was already sanitised, is safe and appears here anyway --\n     this tracks the CALL GRAPH, not the data. The reverse error also\n     exists and is worse: a sink reached through a computed dispatch has no\n     edge and is absent entirely."},
	{Name: "async-colour-frontier", Title: "Where synchronous code calls async code, and how deep the async goes", Notes: "ANSWERS JavaScript's function-colour boundary. Once one function is async,\n     every caller that wants its VALUE must be async too, all the way up.\n     This shows the exact frontier where that requirement is being ignored\n     and how far the async subtree extends below each root.\nACT a sync caller of an async callee either awaits (and becomes async), or\n     deliberately detaches. Making one leaf async can force a rewrite of\n     every caller above it, and async_depth is the size of that blast\n     radius before you start.\nMISLEADS a sync function calling an async one to get the PROMISE -- to\n     store it, race it, or hand it on -- is completely correct and is\n     indistinguishable here from one that forgot to await. The subtree\n     depth is capped at 4 hops (bound in the CTE below) so deep async\n     chains are reported as exactly 4."},
	{Name: "timer-balance", Title: "setInterval and setTimeout with no matching clear, weighted by where they run", Notes: "ANSWERS which timers outlive whatever registered them. A repeating timer\n     holds its closure, and the closure holds everything it captured --\n     so one uncleared setInterval per request is an unbounded leak, and\n     in Node it also keeps the event loop alive so the process will not\n     exit.\nACT keep the handle and clear it in the teardown path -- unmount,\n     disconnect, close, whichever this module has. `unref()` fixes only\n     the shutdown half, not the retention.\nMISLEADS clears are matched per function, not per handle, so a timer set\n     in one function and cleared in another reads as unbalanced here and\n     is fine. Rank by timers set inside a loop -- those are unambiguous."},
	{Name: "dynamic-import-and-eval", Title: "eval, dynamic require and import(): code paths no bundler or scanner can follow", Notes: "ANSWERS where the module graph stops being knowable. A `require(expr)`\n     cannot be resolved by a bundler, cannot be tree-shaken, and cannot\n     be audited by a dependency scanner. `eval` is the same problem with\n     a security consequence attached.\nACT replace `require(name)` with an explicit map from name to a static\n     import -- it is analysable, tree-shakeable and no slower. Use JSON\n     for data and a Function factory only where you truly must.\nMISLEADS `import()` for genuine code splitting is a feature, not a\n     defect, and appears here. The rows worth reading are the ones where\n     the argument is computed rather than a literal."},
	{Name: "hooks-rules-violations", Title: "React hooks called conditionally, and components that re-render on identity", Notes: "ANSWERS where the Rules of Hooks are broken and where re-renders are\n     caused by allocation. A hook inside a condition changes the hook\n     ORDER between renders, which corrupts React's state slots -- the\n     bug appears as one component's state showing up in another.\nACT lift the condition inside the hook: call it unconditionally and\n     branch on the value. For re-renders, an object or arrow literal\n     passed as a prop is a new identity every render -- memoise it.\nMISLEADS an inline object prop is only a problem if the child is\n     memoised or the tree below is expensive; on a leaf it costs\n     nothing. The conditional-hook count is the part that is always a bug."},
	{Name: "dead-code", Title: "Nothing in this tree calls these", Notes: "ANSWERS what might be deletable.\nACT grep the name as a STRING before deleting anything: a registry entry,\n     a config value or a reflective call keeps a symbol alive with no edge\n     to show for it.\nMISLEADS this is the query most likely to be wrong, and `graph-blindspots`\n     measures by how much. Public symbols are excluded because a caller\n     outside this tree cannot be seen at all, so what is left is private\n     and unreferenced -- a much weaker claim than dead."},
	{Name: "sync-io-below-a-handler", Title: "a synchronous fs call reachable from a request handler or exported entry point", Notes: "ANSWERS what eslint-plugin-node's no-sync reports one line at a time and\n     cannot rank: `readFileSync` at module load is how config is read and\n     is correct. The same call under a handler stops the event loop for\n     every other connection until the disk answers. The difference is\n     reachability, not the call.\nACT switch to the promise API and await it, or hoist the read to startup\n     and cache it. `reached_from` names the handler that pays the latency.\nMISLEADS a sync read of a small file already in the page cache costs\n     microseconds and is often the right call. Depth stops at 4 hops, and\n     a callback passed as a value breaks the edge, so a real blocking path\n     through `array.map(cb)` is invisible here."},
	{Name: "command-injection-surface", Title: "child_process.exec with dynamic arguments (ESLint security)", Notes: "ANSWERS where child_process is used, which can execute arbitrary commands.\n     exec with a string argument shells out; execFile with an array does not.\nACT use execFile with an array of arguments, never a shell string.\nMISLEADS child_process in a build tool or CLI wrapper is correct. The graph\n     sees the call but not whether the input is sanitized."},
	{Name: "open-redirect-surface", Title: "location.href writes in functions that read request input (OWASP G26)", Notes: "ANSWERS functions that assign location.href / window.location AND read\n     request input (req.query / req.params / req.headers) -- the shape of\n     a client-side open redirect: location.href = req.query.next.\nACT validate the target against an allowlist; never forward a\n     user-supplied URL.\nMISLEADS same-function co-occurrence is NOT data flow -- the input value\n     may never reach the assignment, and a constant redirect beside an\n     unrelated input read reads as a violation. The assignment target is\n     matched textually (location.href / window.location); location.assign\n     and location.replace calls are not captured; a wrapper around the\n     sink is invisible to it."},
	{Name: "ssrf-fetch-surface", Title: "fetch/http calls in functions that read request input (OWASP G27)", Notes: "ANSWERS functions that fetch a URL (fetch, axios, got, superagent, http.request) AND read request input -- the shape of server-side request forgery: fetch(req.query.url).\nACT validate the URL scheme and host against an allowlist; never fetch a\n     user-supplied URL.\nMISLEADS same-function co-occurrence is NOT data flow -- the input value\n     may never reach the fetch, and a constant URL beside an unrelated\n     input read reads as a violation. The capture is the dotted call\n     text: an http client assigned to a variable (const c = axios.create())\n     and used via c.get is invisible; a wrapper around fetch is too."},
	{Name: "hardcoded-secret-candidates", Title: "Credential-shaped string literals (OWASP G07)", Notes: "ANSWERS string literals at least 12 chars long whose text names a\n     credential (password, token, api_key, secret, bearer, jwt, ...) --\n     the literal that a committed secret looks like.\nACT rotate and move to a secret manager; never commit the literal.\nMISLEADS a format string or test fixture containing the WORD token/pass\n     reads as a candidate (the filter is the literal's own text, not its\n     use); values over 200 chars are truncated at capture; a secret\n     interpolated into a template string is invisible; a secret built\n     from parts or read from an env var is invisible here. This is a\n     candidate list, not a verdict."},
	{Name: "path-traversal-surface", Title: "fs.* with a non-literal path in input-reading functions (OWASP G12)", Notes: "ANSWERS functions that call fs.readFile/writeFile with a variable path\n     AND read request input -- the shape of path traversal:\n     fs.readFile(req.query.f).\nACT validate the resolved path stays under a configured root; use\n     path.resolve and a prefix check.\nMISLEADS same-function co-occurrence is NOT data flow -- the input value\n     may never reach the read, and a constant-read beside an unrelated\n     input read reads as a violation. The path is not analyzed: a\n     variable path is assumed suspicious, a literal is not; a\n     destructured fs import (const {readFile} = require('fs')) is\n     invisible to the fs. capture."},
	{Name: "unchecked-upload-surface", Title: "fs.writeFile fed from req.files with no visible check (OWASP G28)", Notes: "ANSWERS functions that write a file whose data argument is req.files /\n     req.file -- the shape of an unchecked upload: fs.writeFile(dst,\n     req.files.f.data).\nACT check extension, MIME and size against an allowlist before saving;\n     store outside the web root.\nMISLEADS the writeFile data argument is matched textually -- an upload\n     assigned to a local (const d = req.files.f.data) before the write\n     is invisible; multer middleware configuration (diskStorage\n     destination) is not captured at all; the size/type check is not\n     modeled, so a checked write ranks the same as an unchecked one."},
	{Name: "zip-slip-surface", Title: "Archive extraction sites (OWASP G29)", Notes: "ANSWERS functions that touch archive libraries (unzipper, adm-zip,\n     jszip, yauzl) -- the surface where an entry name becomes a\n     filesystem path.\nACT validate every entry name against a containment check before\n     extraction; reject ../ and absolute paths.\nMISLEADS the containment check is not modeled: a function that checks\n     each name before extraction ranks the same as one that does not.\n     The capture needs zip/unzip in the call text, so a renamed\n     extraction helper is invisible."},
	{Name: "mass-assignment-surface", Title: "Object.assign in functions that read request input (OWASP G30)", Notes: "ANSWERS functions that call Object.assign AND read request input -- the\n     shape of mass assignment: Object.assign(user, req.body).\nACT whitelist the fields you accept; never assign a request body whole.\nMISLEADS same-function co-occurrence is NOT data flow -- the assigned\n     source may not be request input, and a constant object beside an\n     unrelated input read reads as a violation. The spread shape\n     {...req.body} is invisible to the Object.assign capture; a\n     per-field whitelist elsewhere in the function is not modeled."},
	{Name: "log-injection-surface", Title: "Logger calls in functions that read request input (OWASP G14)", Notes: "ANSWERS functions that call a logger level method (logger.info,\n     winston/pino) AND read request input -- the shape of log forging:\n     logger.info(req.headers['user-agent']).\nACT sanitize newlines and control characters in log messages; never log\n     raw request input.\nMISLEADS same-function co-occurrence is NOT data flow -- the input value\n     may never reach the log call, and a constant message beside an\n     unrelated input read reads as a violation. The capture needs the\n     word logger in the call text, so a differently-named logger is\n     invisible."},
	{Name: "sensitive-log-surface", Title: "console.* calls in functions that read request input (OWASP G21)", Notes: "ANSWERS functions that call console.log/info/warn/error AND read request\n     input -- the shape of request data (tokens, bodies) ending up in\n     stdout logs: console.log(req.headers.authorization).\nACT route through a structured logger with redaction; never console-log\n     raw request input.\nMISLEADS same-function co-occurrence is NOT data flow -- the input value\n     may never reach the console call, and a constant message beside an\n     unrelated input read reads as a violation. The capture is the\n     dotted console. call; a destructured console alias is invisible."},
	{Name: "unauthenticated-input-surface", Title: "Request input read with no auth call in the function (OWASP G01)", Notes: "ANSWERS functions that read request input and contain NO auth-family\n     call (passport, isAuthenticated, jwt, login) -- the surface where\n     a handler may be missing its authorization check.\nACT add the auth middleware call; verify the route is in the protected\n     group.\nMISLEADS auth usually lives in MIDDLEWARE or a router guard -- this\n     query sees the handler only, so a fully-protected app still ranks\n     every handler as open. A login or public endpoint legitimately has\n     no auth. The markers are name-based substrings, so a wrapper\n     around the auth call is invisible and counts as open."},
	{Name: "proto-mutation", Title: "Direct __proto__ or prototype mutation (ESLint security)", Notes: "ANSWERS where __proto__ is written or Object.prototype is modified, which\n     can pollute every object in the runtime and is a known RCE vector.\nACT never write to __proto__ or Object.prototype; use Object.create.\nMISLEADS a library that intentionally patches a prototype (polyfill) is\n     correct but should be audited."},
	{Name: "process-exit-in-handler", Title: "process.exit() in a request handler (ESLint/no-process-exit)", Notes: "ANSWERS where process.exit is called from a function reachable from a\n     request handler, terminating the process for one request.\nACT throw an error; let the top-level handler decide.\nMISLEADS process.exit in a CLI tool's main is correct. Reachability is\n     from is_handler=1, capped at 4 hops."},
	{Name: "sync-io-under-handler", Title: "Synchronous I/O reachable from a request handler (ESLint/no-sync)", Notes: "ANSWERS where a sync I/O call (readFileSync, writeFileSync) is reachable\n     from a request handler, blocking the event loop for every request.\nACT use the async version (fs.promises.readFile).\nMISLEADS sync I/O in a startup/init path is correct. Reachability is from\n     is_handler=1, capped at 4 hops."},
	{Name: "import-cycle", Title: "Circular import dependencies (madge/circular)", Notes: "ANSWERS which files form an import cycle, causing initialization-order bugs.\nACT break the cycle by extracting shared code into a third module.\nMISLEADS cycles through test files are usually fine. Depth is capped at 8."},
	{Name: "dynamic-require", Title: "require() with a dynamic expression (ESLint/no-require)", Notes: "ANSWERS where require() is called with a variable or expression instead of\n     a string literal, which prevents static analysis and can be exploited\n     for path traversal.\nACT use import with a string literal; if dynamic loading is needed, use a\n     whitelist map.\nMISLEADS a plugin loader that intentionally takes a module name is a valid\n     pattern if the input is validated."},
	{Name: "anon-callback-depth", Title: "Anonymous callbacks per file: the accidental-callback-hell meter", Notes: "ANSWERS where a single file accumulates anonymous closures -- the shape\n     that becomes un-nameable state and un-testable behavior. High counts\n     in one file mean reads nest but the file also does the most work\n     through closures.\nACT name the callbacks that carry real logic; leave only trivial\n     adapters anonymous.\nMISLEADS counts symbols named `(anonymous)` only; an arrow assigned to a\n     const is named and invisible here, so this UNDERcounts closures and\n     says nothing about nesting depth, which `deep-nesting` measures."},
	{Name: "destructured-vs-default", Title: "Destructured imports vs default imports per file", Notes: "ANSWERS how each file prefers to take module surfaces: named\n     destructuring (import_names.alias set) versus default imports\n     (is_default). The ratio says whether the module's API is consumed\n     by name or funneled through one default.\nACT a file at 0% named is likely importing CJS-style `require(x).default`\n     chains or a barrel; a file at 100% named is depending on the export\n     names being STABLE across upgrades.\nMISLEADS counts import SPECIFIERS, not symbols: `import {a, b}` is two\n     rows; `import x from` is one. Namespace imports (import_names\n     is_namespace) are excluded from both buckets."},
	{Name: "relative-import-depth", Title: "Files reaching up more than one directory with ../", Notes: "ANSWERS which files climb the tree with `../` -- every level is a\n     directory rename away from breaking, and the depth is the\n     encapsulation cost of the layout. Long relative chains are the\n     shape a path-alias or a test helper move fixes.\nACT replace chains of depth >= 2 with a package alias or a shared file\n     closer to the root; a depth-1 `../` is normal package structure.\nMISLEADS counts `../` SEGMENTS in the specifier string, so a path alias\n     doing the same work is invisible and a deeply nested module hugging\n     its config (../ 2x but inside the same package) is over-reported."},
	{Name: "global-pollution", Title: "Direct assignments onto window / globalThis / global", Notes: "ANSWERS where a file writes onto the ambient object instead of exporting\n     -- the assignments that collide across bundles, make tests bleed\n     into each other, and hide dependencies.\nACT replace with explicit exports, or a namespace object imported by\n     name; if the assignment is a deliberate polyfill, say so in a\n     comment and expect this row forever.\nMISLEADS counts `window.x = ...`-style member assignments whose left\n     operand begins with window./globalThis./global.; `window[\"x\"]`\n     subscript form, `global.x` inside a worker where it is legitimate,\n     and assignments performed by CALLED code are all invisible."},
	{Name: "reexport-propagation", Title: "Barrel files re-exporting imported symbols", Notes: "ANSWERS the files that re-export what they import (index.js barrels and\n     CJS `module.exports = {...}` passthroughs). Each row is a symbol\n     whose true definition lives ANOTHER file deep, which makes the\n     module graph shallower at the cost of the barrel's indirection.\nACT keep barrels to one level; a barrel re-exporting a re-export buries\n     the source of truth two edits away.\nMISLEADS relies on exports.is_reexport/source_id being populated for the\n     import-then-export shape; a barrel that assigns `module.exports.x =\n     importedModule.x` is not flagged unless it routes through the\n     exporter visitor, and STAR exports of namespaces read as one row."},
	{Name: "then-without-catch", Title: "Functions that .then() and never .catch()/.finally(): floating rejections", Notes: "ANSWERS functions whose bodies chain .then() and never attach a\n     .catch() or .finally() to any promise: an unhandled-rejection\n     candidate every time the chain's input rejects.\nACT attach a rejection handler, or convert to await inside a try/catch.\n     Returning the promise for the CALLER to catch is fine -- and this\n     query will still flag it, because the counter is per-function-body.\nMISLEADS n_then counts every .then in the body and n_catch_handler every\n     .catch/.finally, WITHOUT pairing them: a function with two chains,\n     one caught and one not, is NOT flagged (counter-balance), and a\n     chain handed back to a caller that catches it IS flagged\n     (false positive by design -- the rows are the review list).\n     await-style callers never .then and are absent; a bare `then(fn)`\n     identifier (no dot) also counts, which is a rare name collision."},
	{Name: "includes-in-loop", Title: "includes/indexOf/find inside loop bodies (the accidental O(n^2))", Notes: "ANSWERS functions that scan a collection from inside a loop: every\n     iteration walks the collection again, and the loop is quadratic\n     in the product of the sizes. This is the dominant hot-path\n     surprise in JavaScript.\nACT use a Set/Map for membership, or restructure so the scan happens\n     once.\nMISLEADS the counter counts sites in loop bodies only: a scan that is\n     itself the loop's iteration (for..of over a Set) is absent, and a\n     small fixed-size inner loop (e.g. 3 elements) pays little -- this\n     ranks review order, not measured cost."},
	{Name: "object-injection-surface", Title: "Dynamic bracket writes: obj[computedKey] = v", Notes: "ANSWERS assignments whose target key is computed at run time: the\n     object-injection sink (eslint-security\n     detect-object-injection). When the key comes from request data,\n     the write can land on __proto__/constructor or on a property the\n     author never meant to expose.\nACT validate the key against an allowlist, or use a Map; never write\n     with an unvalidated request-derived key.\nMISLEADS n_dynamic_prop counts ALL computed-key writes: a constant-\n     derived key (a local variable) is indistinguishable from a\n     request-derived one at the syntax level, so the rows are the\n     review surface; reads through a computed key are a different\n     counter and are absent."},
	{Name: "duplicate-branch-conditions", Title: "if (a) ... else if (a): the second branch can never run (sonarjs)", Notes: "ANSWERS if/else-if chains where a later condition repeats an earlier\n     one: the repeated branch is dead code and its body hides a\n     mistake -- the author meant a different condition.\nACT change the second condition, or merge the branches.\nMISLEADS text equality only: `a === 1` vs `a == 1` or a re-ordered\n     expression are NOT detected; an if inside an if (nesting, not an\n     else-if chain) is not compared."},
	{Name: "unused-dependencies", Title: "package.json dependencies never imported (knip/machete territory)", Notes: "ANSWERS declared dependencies no import in the tree references: dead\n     weight in install time and lockfile surface, or a module used only\n     through a global/plugin the importer cannot see.\nACT remove the dependency, or import it where it is actually used; a\n     dependency used only by a build script or a global side effect\n     shows as unused here -- check before deleting.\nMISLEADS matching is target-basename: `import x from 'lodash/merge'`\n     counts as using lodash; a dependency used only via a package\n     internal (no import statement) reads as unused; devDependencies\n     used only by scripts (no source import) are the dominant\n     legitimate row."},
	{Name: "layer-crossings", Title: "routes/views/pages files importing db/api/server files", Notes: "ANSWERS the layer crossings in the conventional web stack: a route or\n     page module importing a data-access module. The fix is the same\n     as in every layering rule -- route through a service/interface --\n     but the directory convention is the cheapest detector there is.\nACT move the data access behind a service module, or accept the\n     crossing deliberately and say why in a comment.\nMISLEADS pure directory-name convention: a `routes/` dir that is not a\n     web layer (e.g. a routing library) misreads, and a `db/` helper\n     that is really a pure utility is flagged; a crossing through a\n     barrel (routes/ importing api/index) is matched on the barrel's\n     dir."},
	{Name: "swallowed-error-catch", Title: "Empty or silent catch blocks: errors caught and swallowed (ESLint no-empty)", Notes: "ANSWERS where an error is caught and discarded: an EMPTY catch block, or a\n     catch whose body never rethrows (n_catch_broad). The failure mode is\n     silence: the request answers 200 with a half-built response, the\n     retry never happens, and nothing in the logs says why.\nACT at minimum log with context and decide; rethrow or wrap with the\n     operation's name. If the swallow is deliberate (best-effort cleanup),\n     say so in a comment so the next reader does not 'fix' it into noise.\nMISLEADS broad = the catch body contains no throw, so a legitimate\n     fallback-and-continue path ranks here; a catch that assigns to a\n     variable the code below genuinely handles is not distinguishable\n     from a swallow at syntax level. Empty catches are listed first\n     because those cannot be defended as handling."},
	{Name: "test-only-callers", Title: "Private functions whose only callers live in test files", Notes: "ANSWERS production code that production code does not use. A private\n     function called exclusively from tests is one of two things: an API\n     so tangled the only way in is a test, or dead production logic kept\n     alive by its own test. Either way the test is pinning behaviour\n     nothing real exercises.\nACT delete the pair, or inline the function into the test, or admit it is\n     public API and export it properly. Do not keep a private helper\n     solely because its test passes.\nMISLEADS dynamic dispatch (a string-keyed registry, an exported object\n     method called externally) has no edge, so a genuinely-used helper\n     reads as test-only here -- check graph-blindspots for the module\n     before deleting. Public symbols are excluded entirely because a\n     library's exports are legitimately consumed outside this tree."},
	{Name: "unawaited-async-majority", Title: "Async functions most callers treat as fire-and-forget (CodeQL js/missing-await)", Notes: "ANSWERS the aggregate shape behind unhandled rejections: async functions\n     where MORE THAN HALF of the production callers neither await, chain\n     .then, nor attach .catch. One floating call is a typo; a majority is\n     a function the codebase has already decided to fire-and-forget,\n     which means every error path in it is dead.\nACT make the contract explicit: either the callers await (and the\n     function's errors become real), or the function catches internally\n     and reports, or its name says plainly that it detaches\n     (scheduleX, fireAndForgetX).\nMISLEADS a caller may legitimately take the PROMISE without awaiting --\n     to store it, race it, or return it -- and this counts that caller as\n     discarding. The per-edge pairs are in floating-promise-crossmodule;\n     this is the module-wide verdict, so read both before refactoring."},
	{Name: "handler-writes-shared-cache", Title: "Request handlers writing module-scope containers: state that outlives the request", Notes: "ANSWERS handlers that write to a container declared OUTSIDE themselves\n     (n_cache_write counts .set/.push/.add on a dotted receiver). The\n     write outlives the request: two concurrent requests now race on one\n     object, one user's data can surface in another user's response, and\n     in a multi-worker deploy the caches disagree per process.\nACT key the state by request and keep it request-local, or make the\n     module container an explicit store with keyed access and eviction\n     (see unbounded-module-cache for the growth half).\nMISLEADS the counter is receiver-name based: res.setHeader and\n     res.set(...) also bump n_cache_write, so a handler that only sets\n     response headers ranks here. Read writer_fns/ctor via\n     unbounded-module-cache to separate real shared containers from\n     header writes before acting."},
	{Name: "listener-add-in-request-path", Title: "Event listeners registered inside request handlers (retention multiplied by traffic)", Notes: "ANSWERS the multiplicative retention leak: a listener registered per\n     REQUEST accumulates one per request for the life of the target.\n     retention-leak-frontier catches the unpaired add; this catches the\n     worse shape -- an add that is paired but still grows, because the\n     handler runs many times and the remove (if any) runs at most once.\nACT register once at startup, or pass { once: true }, or hold the handler\n     and remove it in the request's finally path. Verify with a counter\n     in dev: listenerCount() must be flat across two requests.\nMISLEADS is_handler is inferred from (req,res)-shaped parameters and\n     route registrations, so a middleware misidentified as a handler puts\n     a legitimate per-install addListener here; and an emitter created\n     INSIDE the handler dies with the request, so its listener is safe --\n     ownership of the target is not visible."},
	{Name: "json-parse-unguarded", Title: "JSON.parse of untrusted input with no try in the function", Notes: "ANSWERS where malformed input kills the request -- or since Node 15, an\n     uncaught throw inside a promise kills the PROCESS. JSON.parse of a\n     request body/header/param without a try block on the path is the\n     classic: one hand-crafted body `{` and the worker is gone\n     (nodebestpractices 6.10/6.14: validate incoming JSON, limit payload).\nACT parse inside try/catch and answer 400, or put body-parsing middleware\n     (express.json) at the edge and stop hand-parsing strings.\nMISLEADS the try may sit in the CALLER -- reachability of a guard across\n     frames is not modeled, so a function whose every caller wraps it\n     still appears. Same-function co-occurrence of an input read and a\n     parse is not proof the parsed string came from that input."},
	{Name: "effect-dep-array-misuse", Title: "React effect/callback hooks missing the dependency array entirely, or passing []", Notes: "ANSWERS the two exhaustive-deps shapes that are bugs rather than style:\n     a useEffect/useCallback/useMemo with NO dependency array at all\n     (runs on every render -- useLayoutEffect with no array is a re-render\n     loop waiting for a paint), and one passed an EMPTY array when it\n     reads reactive values (the stale-closure bug: it renders with the\n     first render's values forever).\nACT name the real dependencies, or if [] is correct because nothing\n     reactive is read, extract the reactive read so that stays true.\nMISLEADS n_deps = 0 is only a bug when the effect body READS state or\n     props, which the hook row cannot see; a genuinely static effect\n     ([] on purpose) ranks here. Missing-array rows include hooks the\n     author left unmanaged deliberately -- read the body before acting."},
	{Name: "effect-registers-no-cleanup", Title: "Effects that subscribe or start timers and return no cleanup", Notes: "ANSWERS the React shape of the retention leak: an effect whose body\n     registers a listener or starts a timer but whose callback returns\n     no teardown. Every mount adds one subscription; StrictMode mounts\n     twice in dev, and a long-lived SPA accumulates for the life of the\n     tab -- exactly the pairing rule no linter in the ecosystem checks\n     at the registration site.\nACT return the unsubscribe/clear from the effect callback -- the\n     half-contract language of retention-leak-frontier applies per mount\n     here.\nMISLEADS has_cleanup is a textual test for a returned function in the\n     effect callback: a cleanup taken from a variable\n     (`return unsub;` where unsub is declared above) registers, but a\n     subscription torn down by a ref or a parent is invisible, so a fully\n     managed effect still appears. has_cleanup=1 rows are excluded."},
	{Name: "process-exit-in-exported", Title: "process.exit() inside exported functions: a library killing its host", Notes: "ANSWERS the cross-file version of process-exit-in-handler: an EXPORTED\n     function calls process.exit, so any application that imports it can\n     be killed by it. eslint-plugin-n/no-process-exit flags the call;\n     only the graph can say who is exposed to it (eslint-plugin-n also\n     ships process-exit-as-throw for the same reason: exit is a control\n     transfer every caller inherits).\nACT throw instead, and let the application's top level decide; in a CLI\n    entry point the call is fine -- which is why is_exported, not the\n    call itself, is the filter here.\nMISLEADS an exported function that is only the package's own bin entry\n    (is_entrypoint) is SUPPOSED to exit; cross-package exposure needs an\n    importer outside this tree, which the graph cannot see, so a\n    bin-only export is a false row. exitCode assignment without the call\n    is not captured."},
	{Name: "weak-crypto-hash", Title: "md5/sha1/DES chosen as the algorithm argument (OWASP crypto", Notes: "ANSWERS functions that select a broken algorithm by passing its name as\n     the algorithm argument (n_weak_hash: createHash/createHmac/\n     createCipher with md5/sha1/rc4/des in the argument text). For\n     passwords this is a credential-store defect (OWASP A02: use\n     bcrypt/scrypt/argon2); for signatures, md5 is forgeable.\nACT for passwords use a memory-hard KDF; elsewhere move to sha256+ and a\n     MAC. createCipher is a deprecated API -- replace with createCipheriv\n     and an authenticated mode.\nMISLEADS the algorithm name is read from the argument TEXT: a variable\n    holding 'md5' constructed elsewhere is invisible, and md5 used for a\n    non-adversarial checksum (cache keys, etags) is defensible -- which\n    is why input_reads and handler flags rank the rows, not the hash\n    count alone."},
	{Name: "predictable-random-token", Title: "Math.random in functions that also touch auth: guessable session material", Notes: "ANSWERS the co-occurrence that turns Math.random from a smell into a\n    vulnerability: the same function uses the auth family (login, jwt,\n    session, passport) and Math.random. Math.random is not a CSPRNG --\n    its output is predictable from a few observed values, which is the\n    known session-token forgery (eslint-plugin-security\n    detect-pseudoRandomBytes family, OWASP session management).\nACT use crypto.randomUUID() or crypto.getRandomValues / randomBytes for\n    anything an attacker must not guess.\nMISLEADS same-function co-occurrence is not data flow: the random value\n    may feed a display shuffle while the token comes from a real CSPRNG\n    elsewhere. The auth markers are name substrings, so a wrapper named\n    e.g. `verify()` is invisible and counts as auth here only if its\n    name matches."},
	{Name: "timer-callback-as-string", Title: "setTimeout/setInterval whose callback is a string: implied eval", Notes: "ANSWERS timers whose callback is a STRING (`setTimeout(\"doIt()\", 100)`).\n    The string is compiled and run as program text -- the implied-eval\n    sink (ESLint no-implied-eval): CSP unsafe-eval breaks, the code is\n    invisible to every static tool, and any interpolation into the\n    string is code injection by another name.\nACT pass a function reference or an arrow; keep the delay as the second\n    argument.\nMISLEADS only literal-string callbacks are captured, so the rarer\n    variable-held string is missed; a string constant that never\n    interpolates is still a real (if stale) eval. These rows are rare,\n    which is exactly why each one is worth reading."},
	{Name: "uncaught-exception-swallowed", Title: "process.on('uncaughtException'/'unhandledRejection') handlers", Notes: "ANSWERS where the process-level safety nets are installed. Both events\n    are terminal by design: after an uncaughtException the process is in\n    an unspecified state, and swallowing it to keep serving is how a\n    corrupt-memory process serves 500s for a week (nodebestpractices\n    2.10 / 6.23: make the error observable, then let it die; unhandled\n    rejections crash Node by default since v15 -- an empty handler\n    silently reverses that).\nACT log, flush metrics, close the server, THEN process.exit(1) and let\n    the supervisor restart. For unhandledRejection either log-and-exit\n    or remove the handler and fix the floating promises\n    (floating-promise-crossmodule is the shortlist).\nMISLEADS the handler BODY is not analyzed: a well-behaved log-and-exit\n    and a bare swallow rank identically -- whether process.exit appears\n    inside is the one thing visible (exit_calls column). A test that\n    installs the handler is excluded by is_test, but an installer in a\n    library shipped to applications is the row to chase. The exit_calls\n    column reads the hazards table, so a handler that exits via a\n    helper shows 0."},
	{Name: "cache-scoped-to-call", Title: "A Map/Set built inside a function and written to: a cache that caches nothing", Notes: "ANSWERS functions that construct a fresh Map or Set AND write entries to\n    it. Scope wins: the container is born on entry and dies on return,\n    so if the writes were meant to be a memo/cache/index across calls,\n    they memo nothing -- every call recomputes, and the 'cache' is just\n    a slower object literal. This is the inverse of\n    unbounded-module-cache (which finds containers that live too long);\n    this finds the one that lives too little.\nACT hoist the container to module scope (then it needs the eviction\n    story unbounded-module-cache asks for), or key it by the caller's\n    context and pass it in; if the writes are genuinely per-call\n    bookkeeping, use locals and stop dressing them as a cache.\nMISLEADS n_cache_write counts .set/.push/.add on ANY dotted receiver, so\n    a local Map used as a DEDUPLICATION set within one call is correct\n    code and appears here; only the intent (memo vs bookkeeping) separates\n    them, and intent is not visible. Module-scope containers are excluded\n    because there the pattern is correct."},
	{Name: "module-scope-sync-io", Title: "Synchronous fs/crypto calls at module load: the cold-start tax every require pays", Notes: "ANSWERS top-level *Sync calls (the `<module>` symbol of each file).\n    Unlike a handler-path sync call, this blocks ONCE at startup -- but\n    it is paid by every importer in the graph: CLI cold start, server\n    boot, and worst, a LIBRARY doing it, which taxes every require in\n    every consumer (eslint-plugin-n/no-sync at module scope;\n    nodebestpractices 7.1 territory).\nACT hoist to lazy: read config on first use, or accept it deliberately\n    for a CLI entry -- is_entrypoint files get a pass.\nMISLEADS module scope includes IIFE initialisation that may be genuinely\n    one-time cheap (a small config read already in page cache), and the\n    `<module>` symbol aggregates everything top-level, so a single\n    readFileSync in a guarded init block ranks the same as a loop of\n    them; a sync call inside an IIFE at top level lands here too. The\n    per-call-path version of this question is sync-io-below-a-handler."},
	{Name: "private-symbol-imported", Title: "Underscore-prefixed symbols imported across files", Notes: "ANSWERS files that import another file's `_`-named export -- the\n    convention that says 'internal, no stability guarantee'. Every such\n    import is a hidden API dependency: the provider can never rename or\n    reshape it without breaking an importer the convention promised was\n    impossible.\nACT either promote the symbol to a real documented export, or copy the\n    small helper into the importer; if both files are yours, extract a\n    third shared module so the underscore means what it says.\nMISLEADS convention only: `_` also prefixes intentionally-published\n    internals in some packages (lodash-style), and a leading underscore\n    on a re-export passes through the ORIGINAL name, so barrels can hide\n    the crossing. Matched by exact first character, so names like `__` \n    are the same rule, not a separate finding."},
	{Name: "then-in-loop", Title: ".then() inside a loop body: detached chains, interleaved order", Notes: "ANSWERS promise chains created PER ITERATION (`for (...) p.then(...)`).\n    Unlike await-in-loop (which serialises but keeps order), each .then\n    detaches: the loop finishes before any callback runs, iterations\n    interleave arbitrarily, and a rejection surfaces with no one\n    attached (eslint-plugin-promise/no-promise-in-callback territory,\n    seen at loop granularity).\nACT collect into an array and await Promise.all once after the loop, or\n    await inside the loop if order really matters -- but then say why in\n    a comment.\nMISLEADS a .then on a promise created BEFORE the loop (one subscription,\n    reused) still counts -- the counter is positional; and a deliberately\n    parallel fan-out with individual .catch per item is a defensible\n    pattern that ranks here. Loop trip size is invisible."},
	{Name: "module-scope-floating-promise", Title: "Fire-and-forget async calls at module load: startup races nothing can await", Notes: "ANSWERS top-level statement-position async calls (`init()` at import\n    time with no await/then in sight). The module finishes loading\n    before the work does: importers see half-initialised state, an\n    unhandled rejection at boot crashes the process AFTER exports were\n    consumed, and two imports of the same module race the same init.\n    (CodeQL js/missing-await at the module boundary.)\nACT export an explicit async init and let the entry point await it, or\n    guard with a module-level promise that importers await.\nMISLEADS `<module>` aggregates the whole top level, so one deliberate\n    `server.listen()`-style detach colours the file; a top-level await\n    elsewhere in the file (module-top-level-await) already serialises\n    this, in which case the row is stale. Statement-position counting\n    cannot say WHICH call is async, so a file with ten top-level calls\n    and one async one lists ten -- read it as a file to open, not a\n    line to fix."},
	{Name: "module-top-level-await", Title: "Top-level await in a module: every importer waits for it", Notes: "ANSWERS files whose top level awaits (the `<module>` symbol). TLA\n    serialises the ENTIRE import graph behind this module: a network\n    call at top level delays every consumer's boot, and in a CommonJS\n    interop or an unbundled library it is a hard error\n    (eslint-plugin-n/no-top-level-await).\nACT push the await into an explicit init function the entry calls, or\n    accept it knowingly in an application entry (is_entrypoint), which\n    is the one place the cost is intended.\nMISLEADS counts await EXPRESSIONS attributed to the `<module>` symbol;\n    an await inside a top-level function declaration is the function's,\n    not the module's, so only true top-level rows appear. CommonJS\n    files cannot use TLA at all, so CJS repos will show nothing here\n    -- which is silence, not safety: the CJS equivalent is the\n    module-scope floating promise this catalogue tracks separately."},
	{Name: "duplicate-listener-registration", Title: "The same event registered twice on the same target in one module", Notes: "ANSWERS files that call add-style APIs twice for one (target, event)\n    pair. Both handlers run: a 'save' event firing two analytics calls,\n    a change listener double-applying a diff. Usually it is a merge or a\n    copy-paste remnant; in React it is the double-mount StrictMode\n    exposes immediately.\nACT keep one registration, or if two handlers are intended, name them\n    apart and say why -- then the pair stops reading as an accident.\nMISLEADS pairing is textual on (file, target, event): a target that is\n    re-created between the two adds (two sockets, per-item emitters in a\n    loop) is safe and still flagged; a registration removed between the\n    two adds is not tracked temporally. Empty-target adds (this-bound\n    emitters) group by '' and can over-count in files with several\n    distinct emitters; and two adds of the same event where one is\n    { once: true } are usually intentional staging. Check the two\n    handler texts before treating a row as a merge."},
	{Name: "graceful-shutdown-missing", Title: "A server starts here, and nothing in the module handles SIGTERM/SIGINT", Notes: "ANSWERS files that call listen/createServer (n_server_start) with no\n    signal listener anywhere in the file. On SIGTERM (every container\n    orchestrator's stop signal) the process dies mid-request: connections\n    reset, in-flight writes are lost (nodebestpractices 2.6 'exit\n    gracefully' and the Docker 8.6 shutdown practice).\nACT register process.on('SIGTERM') -> server.close() -> drain -> exit,\n    and give health checks a draining state so the load balancer stops\n    sending traffic first.\nMISLEADS pairing is per-FILE: a server started here and shut down from\n    the module that imports it reads as missing and may be fine -- the\n    graph pairs textually, not across the import. A file that only\n    DEFINES app.listen (a library exposing the method) counts as a\n    server start, which is the loudest false positive here -- that is\n    the express-lib shape. Filter with :mod before reading the list."},
	{Name: "env-read-at-depth", Title: "process.env read deep in the call tree: configuration far from the edge", Notes: "ANSWERS functions that read process.env and how far UP the call graph\n    they sit (hops_to_edge: 0 means the reader is itself a root; 4+ is\n    buried). Configuration at depth is untestable (every test must set\n    the env or mock the module), un-typeable, and invisible: nothing in\n    the signature says the function behaves differently per environment\n    (eslint-plugin-n/no-process-env; 12-factor says config at the edge).\nACT inject the value: read env at the entry/config module and pass the\n    setting down. Rows at depth 0 near an entry point are the correct\n    shape and can be ignored.\nMISLEADS depth is capped at 4 hops (bound in the CTE) and walks RESOLVED\n    edges only, so an env read behind a dynamic dispatch reads as\n    depth 0 (edge) when it may be buried; and depth measures CALLERS\n    above, not users below -- a shallow-but-megamorphic helper can\n    still leak config widely. fan_in is the second axis for a reason."},
	{Name: "promise-executor-async", Title: "new Promise(async ...): executor throws never reject the caller's promise", Notes: "ANSWERS executors declared async. A throw inside them rejects the\n    EXECUTOR's own ignored promise, not the one the caller holds: the\n    caller's promise never settles, every await of it hangs forever, and\n    the timeout that eventually fires names the wrong line.\nACT write a synchronous executor and resolve/reject explicitly; if you\n    need async work, chain it: new Promise((res, rej) =>\n    doWork().then(res, rej)) -- or drop the wrapper and just return the\n    async function's promise.\nMISLEADS one async executor poisons every await of that promise, but\n    the counter is per FUNCTION, so a function with one good and one\n    async executor shows one row; the async wrapper may also be a habit\n    that never misfires (an executor with no throw). The hanging await\n    is the caller's symptom, so the review order is callers (fan_in),\n    not the executor count."},
	{Name: "promise-executor-return", Title: "A Promise executor's return value is silently discarded (no-promise-executor-return)", Notes: "ANSWERS executors that `return` a value. In any other function return\n    hands a result to the caller; here it is thrown away, and the code\n    reads as if the promise resolved to it. The usual cause is a\n    refactored callback whose `return doWork()` was kept when the\n    wrapper was added -- and the value the author meant to propagate\n    never leaves.\nACT call resolve(value) explicitly, or drop the executor entirely: an\n    async function IS the promise constructor for this shape.\nMISLEADS a bare `return;` (no value) is excluded, but a return whose\n    purpose is control flow (early exit before resolve) reads the same\n    as a discarded result value. The executor count is per function:\n    open the body and check each return before rewrapping anything."},
	{Name: "async-callback-in-array-method", Title: "An async function passed where the return value is discarded (forEach, emitters, timers)", Notes: "ANSWERS call sites that hand an ASYNC function to an API that will not\n    await it: array.forEach(async x => ...), emitter.on('evt', async ...),\n    timers with async callbacks. The promise comes back and nobody holds\n    it: one rejection is an unhandledRejection (process death since\n    Node 15), and forEach silently runs CONCURRENTLY where the code\n    reads sequential (eslint-plugin-promise/no-callback-in-promise\n    family).\nACT for-of with await when order matters, Promise.all(items.map(...))\n    when it does not; for emitters and timers, catch inside the callback\n    -- the caller cannot.\nMISLEADS the counter flags ANY argument-position async function, so an\n    emitter handler that is deliberately detached (and catches\n    internally) is listed; promise-returning APIs called with async\n    arrows (React effects, queue.add(async ...)) are CORRECT and appear\n    here -- read the callee, not just the row."},
	{Name: "regex-from-input", Title: "new RegExp built from non-literal data: ReDoS and injection by construction", Notes: "ANSWERS patterns compiled at run time from a variable\n    (security/detect-non-literal-regexp). Two defects in one site: a\n    pattern from user input can be catastrophic on purpose (ReDoS --\n    the attacker supplies `(a+)+$`), and metacharacters in the input\n    silently change what matches (a `.` matches everything), which is a\n    validation bypass where the regex is a guard. redos-frontier covers\n    literal patterns; this covers the ones no literal scan can see.\nACT escape the input (XRegExp.escape or a hand-rolled escape) and reuse\n    the compiled RegExp -- compiling per call is also a hot-path cost\n    (regex_in_loop).\nMISLEADS non-literal is not attacker-controlled: a pattern built from\n    another module's constant string is safe and still listed; input_reads\n    is same-function co-occurrence, not data flow, so a dynamic regex\n    beside an unrelated req read rows identically to the real thing.\n    If a row's regex has no literal anywhere, the ReDoS question moves\n    to whoever supplies the string."},
	{Name: "sendfile-traversal-surface", Title: "res.sendFile/res.download in functions that read request input (express taint)", Notes: "ANSWERS the express-shaped path traversal: a handler chain that reads\n    req.* AND calls res.sendFile/sendfile/download. `res.sendFile(req\n    .params.file)` streams any path the process can read -- /etc/passwd\n    included -- and res.download inherits the same header-setting path.\n    path-traversal-surface covers the fs.* form of the sink; this is the\n    response-native one.\nACT resolve against a fixed root and verify the result still starts\n    with it (path.resolve + prefix check), or keep a whitelist of\n    servable names. Never pass request text to the sink directly.\nMISLEADS same-function co-occurrence is not data flow -- a constant\n    path beside an unrelated req read still rows; the root/containment\n    check (sendFile's root option, a resolve+prefix guard) is not\n    modeled, so a properly rooted sendFile ranks like a raw one. The\n    fs.* form of this sink is path-traversal-surface, not here."},
	{Name: "lazy-require-in-function", Title: "require() at call depth: a dependency the import graph cannot show (n/global-require)", Notes: "ANSWERS literal require() calls INSIDE function bodies. Each one is a\n    dependency invisible to bundlers, dependency auditors and this\n    tool's import graph, plus a (cached, but real) module lookup on\n    every call path that reaches it. Half are deliberate lazy loads to\n    break import cycles or defer heavy modules -- which is exactly the\n    decision that should be visible in one place, not scattered.\nACT hoist to the top and let the module graph tell the truth; if the\n    cycle is real, extract the shared piece; if the deferral is about\n    startup cost, centralise the laziness in one loader module.\nMISLEADS dynamic require(expr) is counted separately\n    (n_require_dynamic) and excluded here, so a plugin-loader pattern\n    that must stay lazy ranks cleanly zero. A hoisted require inside\n    a try/catch for optional dependencies (soft-require) is the\n    legitimate row to expect at the top."},
	{Name: "async-route-handler", Title: "Async handlers/middleware on routes: Express 4 does not catch their rejections", Notes: "ANSWERS route registrations whose terminal callback is async. Express 4\n    (the installed majority) does not await handlers: a rejected promise\n    is an unhandledRejection -- the request hangs until the client times\n    out AND, since Node 15, the crash default applies to the process.\n    Express 5 traps them; the registration site, not the handler, is\n    where the contract is decided.\nACT wrap with an asyncHandler shim that forwards via next(err), or move\n    to Express 5 / a framework that traps, or try/catch inside and call\n    next(err) yourself.\nMISLEADS express version is NOT read: on Express 5 these rows are\n    already safe; middleware libraries that legitimately return promises\n    (compression, static) may be flagged by the textual async test; a\n    wrapped async handler (`router.get(p, wrap(asyncFn))`) hides the\n    async from this test entirely -- absence of rows is weak evidence\n    of safety wherever a wrap helper exists."},
	{Name: "route-handler-unresolved", Title: "A route names its handler, and nothing in this tree defines it", Notes: "ANSWERS registrations like `app.get('/x', showUser)` where no function\n    of that name exists anywhere in the tree. At request time that is a\n    500 (Express calls undefined()), at build time it is a rename that\n    missed one string, and no bundler or linter catches it because the\n    connection is by NAME through the route call.\nACT fix the name, or import the handler -- then the call site and the\n    definition agree and this row disappears.\nMISLEADS matching is by exact name against functions/methods/closures in\n    this tree only: a handler attached at RUN time by a plugin, or\n    defined in a package outside the analysed tree, reads as unresolved\n    and would be a false row; and a handler defined TWICE in the tree\n    passes this check while still binding to the wrong one at run\n    time. The count of matching definitions is shown so both cases\n    are visible."},
	{Name: "repeating-async-timer", Title: "setInterval with an async callback: an uncollected rejection every tick", Notes: "ANSWERS timers whose callback is an async function (timers.is_async_cb).\n    Each tick returns a promise nobody holds: the first failing tick is\n    an unhandledRejection (process exit since Node 15), and with\n    setInterval the failures repeat -- a poller whose endpoint died\n    kills the process on schedule.\nACT make the callback synchronous and wrap the body: (async () => {\n    try { ... } catch (e) { log(e) } })() inside a non-async function,\n    or .catch on a named handler. Prefer setTimeout chains that await\n    the previous run, so ticks cannot overlap.\nMISLEADS a callback that cannot reject (no await, no throw) is flagged\n    anyway -- the test is syntactic; and a repeating timer whose work is\n    best-effort by design may prefer to die loudly, which is a policy\n    this cannot see. Timers inside test files are excluded, so a test\n    helper's async tick is invisible here."},
}
var metrics = []Question{
	{Name: "graph-blindspots", Title: "Read this first: where the call graph cannot see", Notes: "ANSWERS how much of every other answer here is guesswork. JavaScript is\n     the worst language in this repo for this: a call through a computed\n     member (obj[name]()), a require() with a variable, a Proxy, or a\n     plugin registry keyed by string has no edge and never will.\nACT read pct_blind before trusting any reachability query below. Calls to\n     the platform (console, Array.prototype, node: builtins, imported\n     packages) are counted as EXTERNAL, not blind -- they leave the tree by\n     design. Unresolved means we genuinely lost the thread.\nMISLEADS a bare require() with no binding -- `get X() { return\n     require('./X') }` in a barrel -- names nothing, so the file was\n     counted as unimported. The file-level import check now covers\n     that; before it, 30 percent of these rows were live code.\n     a resolved edge can still be wrong. Name-based resolution binds\n     `render` to whichever single `render` exists in the file or in the\n     tree; where two exist it refuses and lands here instead. A high\n     dynamic_calls with low unresolved means the blindness was recognised\n     rather than mis-attributed, which is the better failure."},
	{Name: "megamorphic-shapes", Title: "Hot functions doing dynamic property access, ranked by calling breadth", Notes: "ANSWERS where V8's inline caches are most likely to be giving up. A call\n     site that sees one object shape is monomorphic and inlined; one that\n     sees many degrades to a hash lookup on every access, and functions\n     called from many modules with many computed accesses are where that\n     happens.\nACT give objects a stable shape: initialise every field in the constructor,\n     never `delete` a property (use null), never add fields conditionally.\n     Replace `obj[key]` dictionaries with a Map, which is designed for it.\n     Then MEASURE with --trace-ic or --trace-deopt; nothing here is a\n     confirmed deopt.\nMISLEADS the polymorphic-to-megamorphic threshold in V8 is commonly quoted\n     as 4 receiver shapes, and this ranking leans on that number -- BUT\n     that constant (kMaxPolymorphicMapCount) could NOT be confirmed in V8\n     source when this was written, and it has changed between versions.\n     Treat the 4 as UNVERIFIED folklore: the ORDER of this list is useful,\n     the cutoff is not. Also, modules_calling counts distinct calling\n     modules, which is a proxy for shape variety and not a measurement of\n     it -- one module can pass five shapes and five modules can pass one."},
	{Name: "dead-exports-barrel-blast", Title: "Exports nothing imports, and the barrel files that hide the answer", Notes: "ANSWERS what is deletable from the public surface, and separately which\n     re-export files (barrels) make that question unanswerable. A barrel\n     that does `export * from './x'` forwards names it never mentions, so\n     any importer of the barrel might be using any of them.\nACT an export with imported_by = 0 and fan_in = 0, in a file no barrel\n     re-exports, is genuinely unreferenced in this tree. Delete it, or if\n     it is the package's published API, that is what an exports map in\n     package.json is for.\n     star_reexports > 0 on a row means STOP -- this cannot tell whether that\n     name travels through the barrel to an importer.\nMISLEADS a package's own entry point exports for consumers who are not in\n     this tree at all, and every one of those looks dead here. So does\n     anything reached only by string (a plugin name, a route module loaded\n     by convention, a test fixture required by glob). Read this next to\n     graph-blindspots and never delete on this evidence alone."},
	{Name: "god-functions", Title: "Functions doing too much, by every measure at once", Notes: "ANSWERS which functions are hardest to hold in your head. In JavaScript the\n     usual cause is not a long `if` chain but a callback pyramid, so nested\n     function nodes count toward depth here -- a four-deep callback nest is\n     exactly as hard to read as a four-deep loop.\nACT read `elifs` against `nest`: a high elif count with low nesting is a\n     flat dispatch and wants a lookup table, while high nesting with few\n     elifs is a pyramid and wants extracted functions or async/await.\n     `closures` is how many function objects this allocates.\nMISLEADS a long flat dispatch reads far more easily than a short deeply\n     nested one, which is why this sorts by cognitive rather than sloc.\n     Generated and bundled files are excluded, so anything a build step\n     produced is missing by design."},
	{Name: "parse-coverage", Title: "What this run could not read, and which files carry the most risk", Notes: "ANSWERS whether the numbers above cover the code you think they cover.\n     A file listed here contributed nothing or contributed damaged spans.\nACT the known grammar gaps are Stage-3 proposals: `accessor x = 1` (the\n     decorators auto-accessor form) is a parse error, and any TypeScript\n     syntax in a .js file (satisfies, type annotations) will be too. Flow\n     annotations are not JavaScript and never parse. Everything else here\n     is worth a look at the file itself.\nMISLEADS a file can parse perfectly and still be misunderstood -- this\n     shows hard failures only. n_missing_nodes counts places tree-sitter\n     inserted a token to recover, so a small count usually means one typo\n     rather than a wholly unreadable file."},
	{Name: "shape-deopt-surface", Title: "delete, arguments, with and dynamic property writes: what makes V8 give up", Notes: "ANSWERS where the code defeats the engine's hidden-class optimisation.\n     `delete` on an object turns it into a dictionary-mode object for\n     the rest of its life; `arguments` leaking out of a function blocks\n     inlining; `with` disables scope analysis entirely.\nACT set the property to undefined or null instead of deleting it, or\n     use a Map when keys are genuinely dynamic. Replace `arguments`\n     with rest parameters, which are a real array and do not deopt.\nMISLEADS one delete on a config object at startup costs nothing. This\n     ranks by fan_in and loop depth precisely because the cost is per\n     execution, and a cold path never pays it."},
	{Name: "spread-in-loop", Title: "Spread and object rest inside a loop: accidental quadratic copying", Notes: "ANSWERS where an O(n) idiom sits inside an O(n) loop. `acc = [...acc, x]`\n     or `{...acc, [k]: v}` in a reduce copies everything accumulated so\n     far on every single iteration -- linear code that runs quadratic\n     and only shows up once the input gets big.\nACT push into the array and return it, or mutate the accumulator and\n     freeze at the end. If immutability is the point, build a Map and\n     convert once outside the loop.\nMISLEADS spread over a small fixed list -- merging default options,\n     three known keys -- is idiomatic and free. This cannot see the\n     collection size, only that the copy happens per iteration."},
	{Name: "hot-multipliers", Title: "Where one fix pays back many times: highest fan-in", Notes: "ANSWERS which symbols the rest of the tree leans on hardest.\nACT a correctness or speed win in a high-fan-in leaf pays back once per\n     caller. Read it next to sloc -- a four-digit fan_in on a ten-line\n     function is usually a name collision, not a hot leaf.\nMISLEADS fan_in counts STATIC call sites this parser could resolve, not\n     runtime frequency, and test callers are included, so in most repos a\n     test helper outranks production code. Scope with --module first."},
	{Name: "risk-ranked", Title: "Review order: if you can only read N symbols this week, which N", Notes: "ANSWERS which code combines complexity with the operations this language\n     punishes hardest.\nACT start at the top. The weights are this analyzer's own -- read\n     --schema for the formula rather than assuming it matches another\n     language's score.\nMISLEADS a heuristic, not a finding. Generated files are excluded, so the\n     real top of the list may sit in code this filter hid."},
	{Name: "quadratic-scan-in-hot-callee", Title: "a linear search inside a loop, in a function many callers reach", Notes: "ANSWERS the shape no ESLint rule can see, because it is not a shape at\n     all: `includes`, `indexOf` or `find` inside a loop is O(n*m), and\n     unicorn/no-array-push-push or the perf plugins only look at one\n     statement. What makes it matter is `fan_in` -- the same nested scan\n     in a leaf called twice is noise; in a function 200 call sites reach\n     it is the profile.\nACT build a Set or Map before the loop and test membership in O(1). Rows\n     are ranked by callers first, so the top of the list is where the\n     rewrite pays.\nMISLEADS the loop bound is invisible here. A scan over a 3-element array\n     is faster than the Set that replaces it. `fan_in` counts static call\n     sites, not executions -- a function called once from a hot loop\n     outranks nothing."},
	{Name: "deep-nesting", Title: "Functions with excessive nesting depth (ESLint/max-depth)", Notes: "ANSWERS where a function has max_nesting > 4, making it hard to read and\n     test. Each level multiplies the test matrix.\nACT extract nested blocks into named helper functions; use early returns.\nMISLEADS a callback-heavy function may have structural nesting that is\n     semantically flat. The column measures structural nesting, not\n     async depth."},
	{Name: "too-many-params", Title: "Functions with too many parameters (ESLint/max-params)", Notes: "ANSWERS where a function has more than 4 parameters, making call sites\n     error-prone.\nACT use an options object, or split the function.\nMISLEADS a destructured options parameter is one param semantically. The\n     graph counts formal params, not destructured fields."},
	{Name: "scattered-concerns", Title: "A function called from many different modules (shotgun surgery)", Notes: "ANSWERS which functions are called from a high number of distinct modules,\n     so any change ripples widely.\nACT consider splitting the function or making the contract more stable.\nMISLEADS a utility like log or config is called from everywhere and is\n     intentionally stable."},
	{Name: "jsx-component-complexity", Title: "React component with excessive complexity (ESLint/react)", Notes: "ANSWERS which React components have high cyclomatic complexity, making the\n     render logic hard to verify and test.\nACT extract sub-components, move logic to hooks, or simplify conditionals.\nMISLEADS a component with many conditional renders is complex but not\n     necessarily wrong. The graph measures function complexity, not JSX depth."},
	{Name: "async-surface", Title: "Where the async surface concentrates, module by module", Notes: "ANSWERS how much of each module speaks in promises: the share of async\n    functions, awaits, then-links, and statement-position discards. A\n    module at 90% async with few catch handlers treats errors\n    differently from a callback-era module at 0% -- and the mixed\n    modules are where function-colour bugs live.\nACT read the extremes first: a high-async module with low\n    catch_handlers is the natural hunting ground for the promise\n    queries; a 0% module next to a 100% one marks a colour boundary\n    worth a second look at the seam.\nMISLEADS pct_async counts function DEFINITIONS, not call time -- a\n    tiny async wrapper outweighs a thousand-line sync renderer in this\n    ratio; `<module>` top-level code is excluded, so boot-time awaits\n    are missing; and then_links includes .catch/.finally links\n    (n_promise_chain), so a well-handled chain also counts as links."},
	{Name: "throw-catch-balance", Title: "Throws vs catch blocks, module by module: where errors can escape", Notes: "ANSWERS the arithmetic of error propagation per module: how many throw\n    sites exist, how many try/catch blocks exist to meet them, and how\n    many of those catches are empty. A module throwing 40 errors with 3\n    catches relies on its CALLERS to handle everything -- a design fact,\n    fine for a library, risky for a request path.\nACT read with the call graph in mind: a high throw count that escapes\n    to callers is a contract, and the contract should be documented or\n    the throws converted to result values. Empty catches shrink the\n    real coverage below what this ratio suggests.\nMISLEADS pairing is NOT modeled: a try may catch a callee's throw, a\n    throw may be caught three frames up, and promise rejections never\n    appear as throw statements at all -- pct_paired is catch SITES per\n    throw SITE, not proof any error is handled. Await-style error\n    handling is invisible to n_throw entirely."},
	{Name: "blocking-surface", Title: "Event-loop blocking operations per module: the latency triage map", Notes: "ANSWERS where the *Sync calls, exec calls and JSON megaparses live,\n    weighted into one number per module. On Node's single thread every\n    row here is time the WHOLE process stops; this is the map for\n    deciding which module's blocking is on a request path (drill into\n    event-loop-block-frontier) and which only slows the CLI.\nACT start with sync_fs and exec_ columns: filesystem and subprocess\n    blocking is milliseconds-to-seconds; JSON ops only matter on large\n    payloads. Anything with io_in_loop multiplies.\nMISLEADS counts CALL SITES, not executions: a sync call at startup is\n    ranked beside one in a hot loop unless you read the loop columns;\n    and *Sync coverage is name-based (base ends with Sync), so a\n    wrapped blocking call inside a library is invisible. The weight\n    (x3/x2) is this tool's own judgement, not a measurement."},
	{Name: "env-coupling", Title: "process.env reads per module: the configuration-at-distance map", Notes: "ANSWERS which modules reach for the environment directly and how many\n    distinct functions do it. Every direct env read is a hidden input:\n    it makes the module untestable without env setup, invisible in its\n    signature, and impossible to configure per-instance (eslint\n    -plugin-n/no-process-env; 12-factor puts config at the edge).\nACT route the values through one config module imported explicitly --\n    then this metric should trend toward one reading module plus the\n    config module itself. reader_fns names the functions to convert.\nMISLEADS NODE_ENV and npm-lifecycle reads (process.env.NODE_ENV) are\n    idiomatic and dominate the count in well-run repos; the counter\n    is per member expression, so `process.env.A && process.env.B` is\n    two reads in one function. Handlers reading env per request are\n    the rows worth acting on, not the count itself."},
	{Name: "listener-balance", Title: "Event-listener add/remove balance per module: the retention ledger", Notes: "ANSWERS the module-level ledger behind retention-leak-frontier: how\n    many add-style registrations, how many removals, how many of the\n    adds are anonymous inline handlers with no way to be removed later,\n    and how many sit at module scope where they live for the process.\nACT a module with adds >> removes is not automatically leaking (it may\n    register once at init), but every unbalanced module deserves one\n    question answered: who tears this down? If the answer is 'the GC,\n    when the target dies', confirm the target is per-instance.\nMISLEADS pairing is counted, not matched: one removeAllListeners at\n    teardown legitimately outweighs ten adds, and the count cannot see\n    removal in a DIFFERENT module at all. inline_anon already excludes\n    signal-covered adds, but an AbortController passed as a variable\n    and aborted elsewhere is ownership this count cannot see."},
	{Name: "input-surface-map", Title: "Where request input enters the code, by kind and module", Notes: "ANSWERS the attack surface in one table: how many Express-style input\n    reads (query, body, headers, cookies, files, params) each module\n    contains and how many distinct functions do the reading. Every\n    input-site kind is a different validation problem -- body is JSON\n    mass-assignment, path is traversal, header is injection -- and this\n    says where the guards have to be.\nACT pick the module with the widest spread of kinds and check it has\n    validation AT the entry, not beside each sink; then feed the sink\n    queries (ssrf-fetch, path-traversal, mass-assignment) the top\n    module as :mod.\nMISLEADS capture is shape-based on req./request. receivers: an input\n    read into a local by a helper and consumed elsewhere breaks the\n    chain, and a non-Express framework (Koa ctx, Fastify request\n    destructured at the signature) records nothing -- a zero here is\n    not a zero surface. Counts are reads, not distinct values."},
	{Name: "promise-chain-depth", Title: "The longest .then chains: debugging cost ranked per function", Notes: "ANSWERS which functions carry the deepest promise chains. Every\n    additional .then is a frame an exception must climb and a place\n    where one missing return silently drops the rest of the chain --\n    three or more links is where 'what order did this actually run in'\n    becomes a question only the debugger can answer.\nACT flatten to async/await: each chain here converts to a straight\n    line of awaits inside one try/catch, which also fixes the\n    missing-return class for free. Leave genuinely detached chains\n    (post-response side effects) alone.\nMISLEADS n_promise_chain counts .then/.catch/.finally LINKS in the\n    body, not verified sequential depth: two independent one-link\n    chains read the same as one three-link chain, and awaits are NOT\n    counted, so a converted function drops out even if it is the\n    hardest to follow. Per-file nesting is invisible."},
	{Name: "callback-fanout", Title: "Callback and closure density: the indirection meter", Notes: "ANSWERS how much of a function's work is delegated to nameless callbacks\n    (n_callbacks counts functions passed as call arguments; closures\n    counts function expressions allocated). High density means control\n    flow is assembled at run time: stack traces alternate frames, and\n    the function's real behaviour lives in its arguments.\nACT name the callbacks that carry logic (top-level helpers instead of\n    inline arrows) -- naming one callback converts a pyramid into a\n    call graph edge that every tool here can then follow.\nMISLEADS indirection weights callbacks by nesting depth, which rewards\n    flat callback farms over shallow pyramids; a function passing\n    already-named function REFERENCES counts the same as one inventing\n    arrows inline; and React components legitimately allocate closures\n    per render, so a high count there may be idiomatic."},
	{Name: "production-reach", Title: "Share of each module's functions that production code actually reaches", Notes: "ANSWERS the reachability ledger: per module, how many functions have at\n    least one non-test caller, how many are called only by tests, and\n    how many are called by nothing at all. A module at 30% production\n    reach is mostly ceremony; its tests are testing each other.\nACT test_only rows are the interesting ones -- production code that\n    only tests want is either about to be deleted or about to be\n    needed; unreferenced rows are dead-code's answer at module grain.\nMISLEADS reach is by RESOLVED edges: exports consumed outside this\n    tree, string-dispatched handlers and dynamic calls have no edge, so\n    a library's public API reads as unreferenced -- this metric is\n    honest for applications, misleading for libraries. Callers that are\n    module top level count as production."},
	{Name: "module-coupling", Title: "Import-graph coupling per module: internal edges and package weight", Notes: "ANSWERS how wired-in each module is: how many sibling files it imports,\n    how many import IT, and how many external packages it pulls. The\n    internal counts are the change-ripple radius (this is madge's\n    dependency count per module); the package count is the supply-chain\n    and install surface concentrated where you least want it.\nACT the highest imported_by module is your stability contract -- change\n    it last and version it carefully; the highest imports_internal is\n    your aggregation hub -- the first candidate for splitting when a\n    build or test feels slow.\nMISLEADS resolved RELATIVE imports only: require() of a computed\n    specifier and import() both land as unresolved targets and are\n    absent, so coupling is a floor. Package counts dedupe by specifier\n    prefix, so one lodash imported three ways is one package. Test-file\n    imports are excluded from both sides."},
	{Name: "middleware-chain-depth", Title: "Route registrations ranked by middleware chain length", Notes: "ANSWERS the depth of the middleware stack each route assembles before\n    its terminal handler runs. Every extra layer is a function that can\n    forget next(), change req semantics for everything after it, and\n    add latency to every hit of that route -- chains of 4+ are where\n    'which layer ate this request' debugging starts.\nACT flatten per-route chains into a router-level `use` for the shared\n    prefix so the route line names only what is specific to it, and\n    make sure ONE of the layers owns error forwarding.\nMISLEADS counts fn-shaped ARGUMENTS at the registration site: a\n    middleware factory call (auth(config)) is one layer here whatever\n    it expands to at run time, and an array spread of middlewares\n    counts as one. Route tables built in loops over data register one\n    row per registration, so a data-driven API reads as tiny -- check\n    the loop, not this metric, for the real route count."},
	{Name: "route-surface", Title: "API shape per module: methods, middleware mounts, async handlers", Notes: "ANSWERS the HTTP surface each module exposes: how many routes by\n    method, how many bare middleware mounts, and how many terminal\n    handlers are async (the Express 4 rejection-trapping question that\n    async-route-handler answers per route).\nACT a module whose routes skew heavily POST is state-mutating surface\n    -- it deserves the CSRF/rate-limit conversation first; a module\n    with many use mounts is middleware-heavy and wants\n    middleware-chain-depth read alongside.\nMISLEADS counts REGISTRATION sites, not effective routes: a use('/x',\n    router) mount hides the sub-router's routes under one row, and\n    parametrised paths ('/u/:id') count as one whatever the traffic.\n    Built-in body parsers (express.json()) count as middleware mounts\n    and are the benign majority in most apps; async_handlers is the\n    column to act on."},
}

const numSymCols = 207

var droppedColNames = strings.Fields(`
qual_name line_end n_lines byte_end signature return_type visibility
n_generic_params n_overloads arity_rank is_static is_generator
is_deprecated is_generated body_bytes n_comment_lines n_doc_lines has_doc
n_branches n_early_returns n_switch n_cases n_ternary n_logical n_finally
n_gotos lock_in_loop concat_in_loop query_in_loop branch_in_loop n_locals
n_assign n_compound_assign n_incdec n_cmp n_bitop n_shift n_arith
n_string_lit n_float_lit n_magic n_null_check n_subscript n_member_access
n_closure_capture n_listener n_cache n_timer n_alloc n_async_arrow
n_nullish n_listener_add_in_loop n_weak_ref n_cache_drop n_generator
n_yield n_catch_in_loop n_buffer_call is_arrow is_iife is_default_export
id
`)

const numStoreCols = numSymCols - 62

var colSlot [numSymCols]int16

func init() {
	drop := make(map[string]bool, len(droppedColNames))
	for _, n := range droppedColNames {
		drop[n] = true
	}
	slot := int16(0)
	for i, c := range symCols {
		if drop[c.name] {
			colSlot[i] = -1
			continue
		}
		colSlot[i] = slot
		slot++
	}
	if int(slot) != numStoreCols {
		panic("column split: slot count mismatch: got " +
			strconv.Itoa(int(slot)) + " want " + strconv.Itoa(numStoreCols) +
			" names=" + strconv.Itoa(len(droppedColNames)))
	}
	wide := 0
	for i, c := range symCols {
		s := colSlot[i]
		if s < 0 {
			continue
		}
		if c.name == "byte_start" || c.name == "halstead_volume" {
			symColW[s] = 4
			wide++
		} else {
			symColW[s] = 2
		}
	}
	if wide != 2 {
		panic("packed symbol row: byte_start/halstead_volume slots not found in symCols")
	}
	off := int32(0)
	for s := 0; s < numStoreCols; s++ {
		if symColW[s] != 2 && symColW[s] != 4 {
			panic("packed symbol row: slot " + strconv.Itoa(s) + " has no width")
		}
		symColOff[s] = off
		off += int32(symColW[s])
	}
	symColOff[numStoreCols] = off
}

var symColW [numStoreCols]uint8
var symColOff [numStoreCols + 1]int32

const (
	cID                 = 0
	cFILEID             = 1
	cMODULEID           = 2
	cPARENTID           = 3
	cNAME               = 4
	cQUALNAME           = 5
	cKIND               = 6
	cLINESTART          = 7
	cLINEEND            = 8
	cNLINES             = 9
	cBYTESTART          = 10
	cBYTEEND            = 11
	cSIGNATURE          = 12
	cRETURNTYPE         = 13
	cVISIBILITY         = 14
	cNPARAMS            = 15
	cNOPTIONALPARAMS    = 16
	cNGENERICPARAMS     = 17
	cNOVERLOADS         = 18
	cARITYRANK          = 19
	cISPUBLIC           = 20
	cISSTATIC           = 21
	cISASYNC            = 22
	cISGENERATOR        = 23
	cISABSTRACT         = 24
	cISOVERRIDE         = 25
	cISEXPORTED         = 26
	cISTEST             = 27
	cISDEPRECATED       = 28
	cISENTRYPOINT       = 29
	cISGENERATED        = 30
	cSLOC               = 31
	cBODYBYTES          = 32
	cNCOMMENTLINES      = 33
	cNDOCLINES          = 34
	cHASDOC             = 35
	cCYCLOMATIC         = 36
	cCOGNITIVE          = 37
	cMAXNESTING         = 38
	cNTOKENS            = 39
	cNOPERATORS         = 40
	cNOPERANDS          = 41
	cNDISTINCTOPERATORS = 42
	cNDISTINCTOPERANDS  = 43
	cHALSTEADVOLUME     = 44
	cMAINTAINABILITY    = 45
	cNLOOPS             = 46
	cNBRANCHES          = 47
	cNRETURNS           = 48
	cNEARLYRETURNS      = 49
	cNSWITCH            = 50
	cNCASES             = 51
	cNTERNARY           = 52
	cNLOGICAL           = 53
	cNTRY               = 54
	cNCATCH             = 55
	cNCATCHBROAD        = 56
	cNCATCHEMPTY        = 57
	cNFINALLY           = 58
	cNTHROW             = 59
	cNLABELS            = 60
	cNGOTOS             = 61
	cMAXLOOPDEPTH       = 62
	cCALLINLOOP         = 63
	cALLOCINLOOP        = 64
	cIOINLOOP           = 65
	cAWAITINLOOP        = 66
	cLOCKINLOOP         = 67
	cCONCATINLOOP       = 68
	cREGEXINLOOP        = 69
	cQUERYINLOOP        = 70
	cBRANCHINLOOP       = 71
	cNLOCALS            = 72
	cNASSIGN            = 73
	cNCOMPOUNDASSIGN    = 74
	cNINCDEC            = 75
	cNCMP               = 76
	cNBITOP             = 77
	cNSHIFT             = 78
	cNARITH             = 79
	cNSTRINGLIT         = 80
	cNREGEXLIT          = 81
	cNFLOATLIT          = 82
	cNMAGIC             = 83
	cNNULLCHECK         = 84
	cNSUBSCRIPT         = 85
	cNMEMBERACCESS      = 86
	cNLAMBDA            = 87
	cNCLOSURECAPTURE    = 88
	cNCALLS             = 89
	cNUNIQUECALLS       = 90
	cNDYNAMICCALLS      = 91
	cNUNRESOLVEDCALLS   = 92
	cFANIN              = 93
	cFANOUT             = 94
	cNCALLSITES         = 95
	cISRECURSIVE        = 96
	cISLEAF             = 97
	cISROOT             = 98
	cNHAZARDS           = 99
	cRISKSCORE          = 100
	cNSYNCBLOCK         = 101
	cNEXEC              = 102
	cNPROTOPOLLUTION    = 103
	cNREDOS             = 104
	cNLISTENER          = 105
	cNCACHE             = 106
	cNIO                = 107
	cNNET               = 108
	cNTIMER             = 109
	cNDOM               = 110
	cNSTORAGE           = 111
	cNCRYPTO            = 112
	cNREFLECT           = 113
	cNALLOC             = 114
	cNAWAIT             = 115
	cNAWAITINLOOP       = 116
	cNPROMISEALL        = 117
	cNPROMISECHAIN      = 118
	cNTHEN              = 119
	cNCATCHHANDLER      = 120
	cNFLOATINGPROMISE   = 121
	cNASYNCARROW        = 122
	cNCALLBACKS         = 123
	cNCLOSURES          = 124
	cNTHISREFS          = 125
	cNDYNAMICPROP       = 126
	cNCOMPUTEDMEMBER    = 127
	cNOPTIONALCHAIN     = 128
	cNNULLISH           = 129
	cNSPREAD            = 130
	cNDESTRUCTURE       = 131
	cNDELETE            = 132
	cNARGUMENTS         = 133
	cNWITHSTMT          = 134
	cNPROTOWRITE        = 135
	cNGLOBALWRITE       = 136
	cNREGEXREDOS        = 137
	cNLISTENERADD       = 138
	cNLISTENERREMOVE    = 139
	cNLISTENERINLINE    = 140
	cNLISTENERADDINLOOP = 141
	cNTIMERSET          = 142
	cNTIMERCLEAR        = 143
	cNTIMERREPEATING    = 144
	cNTIMERINLOOP       = 145
	cNNEWMAP            = 146
	cNNEWSET            = 147
	cNWEAKREF           = 148
	cNCACHEWRITE        = 149
	cNCACHEDROP         = 150
	cNJSONPARSE         = 151
	cNINNERHTML         = 152
	cNEVAL              = 153
	cNSYNCCALLS         = 154
	cNREQUIREDYNAMIC    = 155
	cNIMPORTDYNAMIC     = 156
	cNEXPORTSTAR        = 157
	cNJSXELEMENTS       = 158
	cNHOOKS             = 159
	cNHOOKSCONDITIONAL  = 160
	cNSETSTATE          = 161
	cNINLINEOBJECTPROP  = 162
	cNGENERATOR         = 163
	cNYIELD             = 164
	cNLABELED           = 165
	cNCHILDPROCESS      = 166
	cNREDIRECT          = 167
	cNAUTHCALL          = 168
	cNFETCH             = 169
	cNDYNAMICOPEN       = 170
	cNUPLOADSAVE        = 171
	cNZIPREAD           = 172
	cNMASSASSIGN        = 173
	cNLOGCALL           = 174
	cNCONSOLELOG        = 175
	cNFSSYNC            = 176
	cNASSIGNINLOOP      = 177
	cNDUPCOND           = 178
	cNJSONPARSEINLOOP   = 179
	cNARRAYGROWINLOOP   = 180
	cNSEARCHINLOOP      = 181
	cNMATHRANDOM        = 182
	cNWEAKHASH          = 183
	cNTHENINLOOP        = 184
	cNCATCHINLOOP       = 185
	cNPROCESSEXIT       = 186
	cNBUFFERCALL        = 187
	cNPROTOMUTATE       = 188
	cNELIF              = 189
	cNEXTERNALCALLS     = 190
	cNMODULESCALLING    = 191
	cCLASSNAME          = 192
	cISHANDLER          = 193
	cISCOMPONENT        = 194
	cISHOOK             = 195
	cISARROW            = 196
	cISIIFE             = 197
	cISDEFAULTEXPORT    = 198
	cNENVREAD           = 199
	cNPROMISEEXECASYNC  = 200
	cNPROMISEEXECRETURN = 201
	cNASYNCARG          = 202
	cNREGEXDYNAMIC      = 203
	cNSENDFILE          = 204
	cNLAZYREQUIRE       = 205
	cNSERVERSTART       = 206
)

var symCols = [...]struct {
	name string
	kind uint8
}{
	{"id", 0},
	{"file_id", 0},
	{"module_id", 0},
	{"parent_id", 0},
	{"name", 2},
	{"qual_name", 2},
	{"kind", 2},
	{"line_start", 0},
	{"line_end", 0},
	{"n_lines", 0},
	{"byte_start", 0},
	{"byte_end", 0},
	{"signature", 2},
	{"return_type", 2},
	{"visibility", 2},
	{"n_params", 0},
	{"n_optional_params", 0},
	{"n_generic_params", 0},
	{"n_overloads", 0},
	{"arity_rank", 0},
	{"is_public", 0},
	{"is_static", 0},
	{"is_async", 0},
	{"is_generator", 0},
	{"is_abstract", 0},
	{"is_override", 0},
	{"is_exported", 0},
	{"is_test", 0},
	{"is_deprecated", 0},
	{"is_entrypoint", 0},
	{"is_generated", 0},
	{"sloc", 0},
	{"body_bytes", 0},
	{"n_comment_lines", 0},
	{"n_doc_lines", 0},
	{"has_doc", 0},
	{"cyclomatic", 0},
	{"cognitive", 0},
	{"max_nesting", 0},
	{"n_tokens", 0},
	{"n_operators", 0},
	{"n_operands", 0},
	{"n_distinct_operators", 0},
	{"n_distinct_operands", 0},
	{"halstead_volume", 0},
	{"maintainability", 0},
	{"n_loops", 0},
	{"n_branches", 0},
	{"n_returns", 0},
	{"n_early_returns", 0},
	{"n_switch", 0},
	{"n_cases", 0},
	{"n_ternary", 0},
	{"n_logical", 0},
	{"n_try", 0},
	{"n_catch", 0},
	{"n_catch_broad", 0},
	{"n_catch_empty", 0},
	{"n_finally", 0},
	{"n_throw", 0},
	{"n_labels", 0},
	{"n_gotos", 0},
	{"max_loop_depth", 0},
	{"call_in_loop", 0},
	{"alloc_in_loop", 0},
	{"io_in_loop", 0},
	{"await_in_loop", 0},
	{"lock_in_loop", 0},
	{"concat_in_loop", 0},
	{"regex_in_loop", 0},
	{"query_in_loop", 0},
	{"branch_in_loop", 0},
	{"n_locals", 0},
	{"n_assign", 0},
	{"n_compound_assign", 0},
	{"n_incdec", 0},
	{"n_cmp", 0},
	{"n_bitop", 0},
	{"n_shift", 0},
	{"n_arith", 0},
	{"n_string_lit", 0},
	{"n_regex_lit", 0},
	{"n_float_lit", 0},
	{"n_magic", 0},
	{"n_null_check", 0},
	{"n_subscript", 0},
	{"n_member_access", 0},
	{"n_lambda", 0},
	{"n_closure_capture", 0},
	{"n_calls", 0},
	{"n_unique_calls", 0},
	{"n_dynamic_calls", 0},
	{"n_unresolved_calls", 0},
	{"fan_in", 0},
	{"fan_out", 0},
	{"n_callsites", 0},
	{"is_recursive", 0},
	{"is_leaf", 0},
	{"is_root", 0},
	{"n_hazards", 0},
	{"risk_score", 0},
	{"n_sync_block", 0},
	{"n_exec", 0},
	{"n_proto_pollution", 0},
	{"n_redos", 0},
	{"n_listener", 0},
	{"n_cache", 0},
	{"n_io", 0},
	{"n_net", 0},
	{"n_timer", 0},
	{"n_dom", 0},
	{"n_storage", 0},
	{"n_crypto", 0},
	{"n_reflect", 0},
	{"n_alloc", 0},
	{"n_await", 0},
	{"n_await_in_loop", 0},
	{"n_promise_all", 0},
	{"n_promise_chain", 0},
	{"n_then", 0},
	{"n_catch_handler", 0},
	{"n_floating_promise", 0},
	{"n_async_arrow", 0},
	{"n_callbacks", 0},
	{"n_closures", 0},
	{"n_this_refs", 0},
	{"n_dynamic_prop", 0},
	{"n_computed_member", 0},
	{"n_optional_chain", 0},
	{"n_nullish", 0},
	{"n_spread", 0},
	{"n_destructure", 0},
	{"n_delete", 0},
	{"n_arguments", 0},
	{"n_with_stmt", 0},
	{"n_proto_write", 0},
	{"n_global_write", 0},
	{"n_regex_redos", 0},
	{"n_listener_add", 0},
	{"n_listener_remove", 0},
	{"n_listener_inline", 0},
	{"n_listener_add_in_loop", 0},
	{"n_timer_set", 0},
	{"n_timer_clear", 0},
	{"n_timer_repeating", 0},
	{"n_timer_in_loop", 0},
	{"n_new_map", 0},
	{"n_new_set", 0},
	{"n_weak_ref", 0},
	{"n_cache_write", 0},
	{"n_cache_drop", 0},
	{"n_json_parse", 0},
	{"n_innerhtml", 0},
	{"n_eval", 0},
	{"n_sync_calls", 0},
	{"n_require_dynamic", 0},
	{"n_import_dynamic", 0},
	{"n_export_star", 0},
	{"n_jsx_elements", 0},
	{"n_hooks", 0},
	{"n_hooks_conditional", 0},
	{"n_setstate", 0},
	{"n_inline_object_prop", 0},
	{"n_generator", 0},
	{"n_yield", 0},
	{"n_labeled", 0},
	{"n_child_process", 0},
	{"n_redirect", 0},
	{"n_auth_call", 0},
	{"n_fetch", 0},
	{"n_dynamic_open", 0},
	{"n_upload_save", 0},
	{"n_zip_read", 0},
	{"n_mass_assign", 0},
	{"n_log_call", 0},
	{"n_console_log", 0},
	{"n_fs_sync", 0},
	{"n_assign_in_loop", 0},
	{"n_dup_cond", 0},
	{"n_json_parse_in_loop", 0},
	{"n_array_grow_in_loop", 0},
	{"n_search_in_loop", 0},
	{"n_math_random", 0},
	{"n_weak_hash", 0},
	{"n_then_in_loop", 0},
	{"n_catch_in_loop", 0},
	{"n_process_exit", 0},
	{"n_buffer_call", 0},
	{"n_proto_mutate", 0},
	{"n_elif", 0},
	{"n_external_calls", 0},
	{"n_modules_calling", 0},
	{"class_name", 2},
	{"is_handler", 0},
	{"is_component", 0},
	{"is_hook", 0},
	{"is_arrow", 0},
	{"is_iife", 0},
	{"is_default_export", 0},
	{"n_env_read", 0},
	{"n_promise_exec_async", 0},
	{"n_promise_exec_return", 0},
	{"n_async_arg", 0},
	{"n_regex_dynamic", 0},
	{"n_send_file", 0},
	{"n_lazy_require", 0},
	{"n_server_start", 0},
}

type jpair struct {
	key string
	val any
}

type jobj struct{ pairs []jpair }

func (o *jobj) get(k string) (any, bool) {
	if o == nil {
		return nil, false
	}
	for _, p := range o.pairs {
		if p.key == k {
			return p.val, true
		}
	}
	return nil, false
}

type jparser struct {
	s   string
	i   int
	bad bool
}

func parseJSON(s string) (any, bool) {
	p := &jparser{s: s}
	p.ws()
	v := p.value()
	p.ws()
	if p.bad || p.i != len(s) {
		return nil, false
	}
	return v, true
}

func (p *jparser) ws() {
	for p.i < len(p.s) {
		switch p.s[p.i] {
		case ' ', '\t', '\n', '\r':
			p.i++
		default:
			return
		}
	}
}

func (p *jparser) value() any {
	if p.bad || p.i >= len(p.s) {
		p.bad = true
		return nil
	}
	switch c := p.s[p.i]; {
	case c == '{':
		p.i++
		o := &jobj{}
		p.ws()
		if p.i < len(p.s) && p.s[p.i] == '}' {
			p.i++
			return o
		}
		for {
			p.ws()
			k, ok := p.str()
			if !ok {
				p.bad = true
				return nil
			}
			p.ws()
			if p.i >= len(p.s) || p.s[p.i] != ':' {
				p.bad = true
				return nil
			}
			p.i++
			p.ws()
			v := p.value()
			o.pairs = append(o.pairs, jpair{k, v})
			p.ws()
			if p.i < len(p.s) && p.s[p.i] == ',' {
				p.i++
				continue
			}
			if p.i < len(p.s) && p.s[p.i] == '}' {
				p.i++
				return o
			}
			p.bad = true
			return nil
		}
	case c == '[':
		p.i++
		var arr []any
		p.ws()
		if p.i < len(p.s) && p.s[p.i] == ']' {
			p.i++
			return arr
		}
		for {
			p.ws()
			arr = append(arr, p.value())
			p.ws()
			if p.i < len(p.s) && p.s[p.i] == ',' {
				p.i++
				continue
			}
			if p.i < len(p.s) && p.s[p.i] == ']' {
				p.i++
				return arr
			}
			p.bad = true
			return nil
		}
	case c == '"':
		s, ok := p.str()
		if !ok {
			return nil
		}
		return s
	case strings.HasPrefix(p.s[p.i:], "true"):
		p.i += 4
		return true
	case strings.HasPrefix(p.s[p.i:], "false"):
		p.i += 5
		return false
	case strings.HasPrefix(p.s[p.i:], "null"):
		p.i += 4
		return nil
	default:
		start := p.i
		for p.i < len(p.s) {
			c := p.s[p.i]
			if (c >= '0' && c <= '9') || c == '-' || c == '+' || c == '.' ||
				c == 'e' || c == 'E' {
				p.i++
				continue
			}
			break
		}
		f, err := strconv.ParseFloat(p.s[start:p.i], 64)
		if err != nil {
			p.bad = true
			return nil
		}
		return f
	}
}

func (p *jparser) str() (string, bool) {
	if p.i >= len(p.s) || p.s[p.i] != '"' {
		p.bad = true
		return "", false
	}
	p.i++
	var b strings.Builder
	for p.i < len(p.s) {
		c := p.s[p.i]
		if c == '"' {
			p.i++
			return b.String(), true
		}
		if c == '\\' {
			p.i++
			if p.i >= len(p.s) {
				break
			}
			switch p.s[p.i] {
			case 'n':
				b.WriteByte('\n')
			case 't':
				b.WriteByte('\t')
			case 'r':
				b.WriteByte('\r')
			case 'b':
				b.WriteByte('\b')
			case 'f':
				b.WriteByte('\f')
			case 'u':
				if p.i+4 < len(p.s) {
					n, err := strconv.ParseUint(p.s[p.i+1:p.i+5], 16, 32)
					if err == nil {
						b.WriteRune(rune(n))
						p.i += 4
					}
				}
			default:
				b.WriteByte(p.s[p.i])
			}
			p.i++
			continue
		}
		b.WriteByte(c)
		p.i++
	}
	p.bad = true
	return "", false
}

func jstr(v any) string {
	switch t := v.(type) {
	case []any:
		parts := make([]string, 0, len(t))
		for _, e := range t {
			parts = append(parts, jrepr(e))
		}
		return "[" + strings.Join(parts, ", ") + "]"
	case *jobj:
		parts := make([]string, 0, len(t.pairs))
		for _, p := range t.pairs {
			parts = append(parts, "'"+p.key+"': "+jrepr(p.val))
		}
		return "{" + strings.Join(parts, ", ") + "}"
	}
	return jrepr(v)
}

func jrepr(v any) string {
	switch t := v.(type) {
	case string:
		return "'" + t + "'"
	case []any, *jobj:
		return jstr(v)
	}
	return jstrScalar(v)
}

func jstrScalar(v any) string {
	switch t := v.(type) {
	case string:
		return t
	case float64:
		if t == float64(int64(t)) {
			return strconv.FormatInt(int64(t), 10)
		}
		return cgReprFloat(t)
	case bool:
		if t {
			return "True"
		}
		return "False"
	case nil:
		return "None"
	}
	return ""
}

func (g *Graph) parseManifest(root string) {
	path := filepath.Join(root, "package.json")
	if st, err := os.Stat(path); err != nil || !st.Mode().IsRegular() {
		return
	}
	raw, err := os.ReadFile(path)
	if err != nil {
		return
	}
	v, ok := parseJSON(string(raw))
	if !ok {
		return
	}
	data, ok := v.(*jobj)
	if !ok {
		return
	}
	name := "?"
	if s, ok := data.get("name"); ok {
		name = jstrScalar(s)
	}
	pkgType := "commonjs"
	if s, ok := data.get("type"); ok {
		pkgType = jstrScalar(s)
	}
	depsV, _ := data.get("dependencies")
	depsObj, _ := depsV.(*jobj)
	devV, _ := data.get("devDependencies")
	devObj, _ := devV.(*jobj)
	engV, _ := data.get("engines")
	engObj, _ := engV.(*jobj)
	for _, sect := range []struct {
		o     *jobj
		isDev int32
	}{{depsObj, 0}, {devObj, 1}} {
		if sect.o == nil {
			continue
		}
		for _, p := range sect.o.pairs {
			g.Deps = append(g.Deps, DepRow{id: int32(len(g.Deps) + 1),
				name: g.put(clip(p.key, 120)), version: g.put(clip(jstrScalar(p.val), 40)),
				dev: sect.isDev, dir: g.put(".")})
		}
	}
	engine := "unspecified"
	if engObj != nil {
		if s, ok := engObj.get("node"); ok {
			engine = jstrScalar(s)
		}
	}
	sideEffects := "unspecified"
	if s, ok := data.get("sideEffects"); ok {
		sideEffects = jstr(s)
	}
	exports := "no"
	if s, ok := data.get("exports"); ok && s != nil {
		exports = "yes"
	}
	kind := "require/module.exports"
	if pkgType == "module" {
		kind = "import/export"
	}
	nDeps, nDev := 0, 0
	if depsObj != nil {
		nDeps = len(depsObj.pairs)
	}
	if devObj != nil {
		nDev = len(devObj.pairs)
	}
	g.setMetaRaw("package", name)
	g.setMetaRaw("module_type", pkgType+" ("+kind+")")
	g.setMetaRaw("dependencies", sprintf("%d runtime / %d dev", nDeps, nDev))
	g.setMetaRaw("engines_node", engine)
	g.setMetaRaw("has_exports_map", exports)
	g.setMetaRaw("side_effects", sideEffects)
}

const (
	maxFileBytes = 4 * 1024 * 1024

	maxLineBytes = 1024 * 1024
)

var commonSkipDirs = map[string]bool{
	".git": true, ".hg": true, ".svn": true, ".jj": true, ".idea": true,
	".vscode": true, ".vs": true, ".claude": true, "node_modules": true,
	"bower_components": true, "vendor": true, "third_party": true,
	"thirdparty": true, "external": true, "externals": true, "deps": true,
	"Godeps": true, "_vendor": true, "__pycache__": true, ".mypy_cache": true,
	".pytest_cache": true, ".ruff_cache": true, ".tox": true, ".venv": true,
	"venv": true, "env": true, ".env": true, "virtualenv": true,
	"build": true, "_build": true, "dist": true, "out": true, "target": true,
	"bin": true, "obj": true, ".gradle": true, ".next": true, ".nuxt": true,
	".svelte-kit": true, ".parcel-cache": true, ".turbo": true, ".cache": true,
	"coverage": true, "htmlcov": true, ".nyc_output": true, "site-packages": true,
}

var jsSkipDirs = map[string]bool{
	"node_modules": true, "bower_components": true, "flow-typed": true,
	"typings": true, ".yarn": true, ".pnp": true, "lib-cov": true,
	"jspm_packages": true, "web_modules": true,
}

var jsExts = map[string]bool{".js": true, ".mjs": true, ".cjs": true, ".jsx": true}

var (
	reGeneratedName = regexp.MustCompile(`(?i)(\.min\.|\.bundle\.|[-_.](gen|generated|pb|g)\.|_pb2|\.g\.dart$|\.designer\.|^zz_generated)`)
	reTestPath      = regexp.MustCompile(`(?i)(^|/)(tests?|test-d|spec|specs|__tests__|__snapshots__|testing|e2e|integration[-_]tests?|testdata|test_data|test-data|fixtures?)(/|$)`)
	reTestNameJS    = regexp.MustCompile(`(\.test\.|\.spec\.|^test-|-test\.)`)
	reVendorPath    = regexp.MustCompile(`(?i)(^|/)(vendor|third_party|thirdparty|external|node_modules|deps)(/|$)`)
	reExamplePath   = regexp.MustCompile(`(?i)(^|/)(examples?|samples?|demos?)(/|$)`)
	reToolPath      = regexp.MustCompile(`(?i)(^|/)(tools?|scripts?|cmd|bin)(/|$)`)
)

var generatedMarkers = []string{
	"@generated", "DO NOT EDIT", "Code generated by", "AUTO-GENERATED",
	"autogenerated", "This file was automatically generated",
	"Generated by the protocol buffer compiler", "@flow-generated",
}

var lineCommentPrefixes = map[string]bool{
	"//": true, "#": true, "/*": true, "*": true, "*/": true,
	"\"\"\"": true, "'''": true, "--": true, ";;": true, "%": true,
}

func isGenerated(name, head string) bool {
	if reGeneratedName.MatchString(name) {
		return true
	}
	for _, m := range generatedMarkers {
		if strings.Contains(head, m) {
			return true
		}
	}
	return false
}

func moduleOf(rel string) string {
	parts := strings.Split(rel, "/")
	if len(parts) <= 1 {
		return "(root)"
	}
	head := parts[:len(parts)-1]
	if len(head) > 0 {
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
	}
	s := strings.Join(head, "/")
	if s == "" {
		return "(root)"
	}
	return s
}

func moduleKind(name string) string {
	switch {
	case reTestPath.MatchString(name):
		return "test"
	case reVendorPath.MatchString(name):
		return "vendor"
	case reExamplePath.MatchString(name):
		return "example"
	case reToolPath.MatchString(name):
		return "tool"
	}
	return "source"
}

type discovered struct {
	fid        int32
	moduleID   int32
	rel, full  string
	data       []byte
	text       string
	parse      bool
	isTest     bool
	isGen      bool
	isVendored bool
}

type discoverStats struct {
	big, nSpecial, escape, denied, walkErr, n int
}

type discovery struct {
	g        *Graph
	stats    discoverStats
	files    []discovered
	modIdx   map[string]int32
	opts     *Options
	realRoot string
	strs     []byte

	enqueue func(*discovered)
}

func (d *discovery) put(v string) sref {
	if v == "" {
		return sref{}
	}
	if len(d.strs)+len(v) > arenaLimit {
		panic("discovery string arena overflows 4GiB")
	}
	o := uint32(len(d.strs))
	d.strs = append(d.strs, v...)
	return sref{o, uint32(len(v))}
}

func (d *discovery) walkTree(root, realRoot string) {
	var rec func(dir string, rel string)
	rec = func(dir, rel string) {
		f, err := os.Open(dir)
		if err != nil {
			d.stats.walkErr++
			return
		}
		ents, err := f.ReadDir(-1)
		f.Close()
		if err != nil {
			d.stats.walkErr++
			return
		}
		sort.Slice(ents, func(i, j int) bool { return ents[i].Name() < ents[j].Name() })

		var dirs, files []string
		for _, e := range ents {
			if e.IsDir() {
				n := e.Name()
				if commonSkipDirs[n] || jsSkipDirs[n] || strings.HasPrefix(n, ".") {
					continue
				}
				dirs = append(dirs, n)
			} else {
				files = append(files, e.Name())
			}
		}
		sort.Strings(files)
		for _, n := range files {
			d.consider(dir, rel, n)
		}
		for _, n := range dirs {
			sub := filepath.Join(dir, n)
			sr := n
			if rel != "" {
				sr = rel + "/" + n
			}
			rec(sub, sr)
		}
	}
	rec(root, "")
}

func (d *discovery) consider(dir, rel, fn string) {
	ext := filepath.Ext(fn)
	if !jsExts[ext] {
		return
	}
	d.stats.n++
	full := filepath.Join(dir, fn)
	relPath := fn
	if rel != "" {
		relPath = rel + "/" + fn
	}
	st, err := os.Lstat(full)
	if err != nil {
		return
	}
	if !st.Mode().IsRegular() {

		if st.Mode()&os.ModeSymlink != 0 {
			d.considerSymlink(full, relPath, fn, ext)
			return
		}
		d.stats.nSpecial++
		return
	}
	d.read(full, relPath, fn, ext, st.Size(), d.opts)
}

func (d *discovery) considerSymlink(full, relPath, fn, ext string) {
	real, err := filepath.EvalSymlinks(full)
	if err != nil {
		d.stats.escape++
		return
	}
	if real == full {
		return
	}
	if !(strings.HasPrefix(real, d.realRoot+string(filepath.Separator))) {
		d.stats.escape++
		return
	}
	st, err := os.Stat(full)
	if err != nil || !st.Mode().IsRegular() {
		d.stats.nSpecial++
		return
	}
	d.read(full, relPath, fn, ext, st.Size(), d.opts)
}

func (d *discovery) read(full, relPath, fn, ext string, size int64, o *Options) {
	tooBig := false
	var data []byte
	if size > maxFileBytes {
		d.stats.big++
		tooBig = true
	} else {
		b, err := os.ReadFile(full)
		if err != nil {
			if os.IsPermission(err) {
				d.stats.denied++
			}
			return
		}
		data = b
	}
	text := decodeReplace(data)
	if !tooBig && len(data) > 0 {
		longest := 0
		for rest := data; len(rest) > 0; {
			i := bytes.IndexByte(rest, '\n')
			n := len(rest)
			if i >= 0 {
				n = i
			}
			if n > longest {
				longest = n
			}
			if i < 0 {
				break
			}
			rest = rest[i+1:]
		}
		if longest > maxLineBytes {
			d.stats.big++
			tooBig = true
			data = nil
			text = ""
		}
	}
	if tooBig {
		data = nil
		text = ""
	}

	var nLines, blank, cmt, slocN, maxLen int32
	cgLines(text, func(l string) {
		nLines++
		ls := strings.TrimLeftFunc(l, isCgSpace)
		if ls == "" {
			blank++
		} else {
			slocN++
			p := ls
			if len(p) > 3 {
				p = p[:3]
			}
			if lineCommentPrefixes[p] {
				cmt++
			}
		}
		if n := int32(utf8.RuneCountInString(l)); n > maxLen {
			maxLen = n
		}
	})
	isTest := reTestPath.MatchString(relPath) || reTestNameJS.MatchString(fn)
	head := text
	if len(head) > 2000 {
		head = head[:2000]
	}
	isGen := isGenerated(fn, head)
	isVend := reVendorPath.MatchString(relPath)
	modID := d.moduleID(moduleOf(relPath))
	parse := !tooBig && text != "" && (o.IncludeTests || !isTest) &&
		(o.IncludeGenerated || !isGen) && (o.IncludeVendored || !isVend)

	sum := ""
	if len(data) > 0 {
		h := sha1.Sum(data)
		sum = hex.EncodeToString(h[:])
	}
	fid := d.g.addFile(File{
		id: d.g.nFiles(), moduleID: modID, bytes: int32(size), lines: nLines,
		sloc: slocN, blank: blank, comment: cmt, maxLine: maxLen,
		path: d.put(relPath), dir: d.put(dirOf(relPath)), base: d.put(fn), ext: d.put(ext),
		lang: d.put("javascript"), sha1: d.put(sum), parsed: parse, isTest: isTest,
		isGen: isGen, isVendored: isVend,
	})
	if parse {
		rec := discovered{
			fid: fid, moduleID: modID, rel: relPath,
			full: full, data: data, text: text, parse: true,
			isTest: isTest, isGen: isGen, isVendored: isVend,
		}
		d.files = append(d.files, rec)
		if d.enqueue != nil {
			d.enqueue(&rec)
		}
	}
}

func dirOf(rel string) string {
	i := strings.LastIndexByte(rel, '/')
	if i < 0 {
		return "."
	}
	return rel[:i]
}

func decodeReplace(b []byte) string {
	if utf8.Valid(b) {
		return string(b)
	}
	return strings.ToValidUTF8(string(b), "�")
}

func (g *Graph) nFiles() int32 { return int32(len(g.Files) + 1) }

func (g *Graph) addFile(f File) int32 {
	g.Files = append(g.Files, f)
	return f.id
}

func (g *Graph) addModule(name, kind sref) int32 {
	g.Modules = append(g.Modules, Module{id: int32(len(g.Modules) + 1), name: name, kind: kind})
	return int32(len(g.Modules))
}

func (d *discovery) moduleID(name string) int32 {
	if id, ok := d.modIdx[name]; ok {
		return id
	}
	id := d.g.addModule(d.put(name), d.put(moduleKind(name)))
	d.modIdx[name] = id
	return id
}

func (d *discovery) run(root string, o *Options) {
	realRoot, err := filepath.EvalSymlinks(root)
	if err != nil {
		realRoot = root
	}
	d.realRoot = realRoot
	d.walkTree(root, realRoot)
}

type Options struct {
	Root             string
	IncludeTests     bool
	IncludeGenerated bool
	IncludeVendored  bool
	Quiet            bool
	Workers          int
	GCPercent        int
	Batch            int
	KeepTrees        bool
}

type emitter struct {
	g       *Graph
	parser  *tsParser
	handler map[string]bool
	opts    *Options

	nameExists map[string]bool
	byNameIdx  map[string][]gname
	byQual     map[string]int32
	graph      *Graph

	pendSid, pendFid, pendMid, pendLine []int32
	pendName, pendType                  []string
	nExtByCaller                        map[int32]int32
	nResolved, nExternal, nUnresolved   int32
	bindingsByFile                      map[int32]map[string]binding
}

type fileResult struct {
	ctx  *fileCtx
	recs []tsRec
}

func (e *emitter) decodeOne(r *discovered, tree *tsTree) *fileResult {
	f := newFileCtx(e, r)
	f.scanMarkers()
	if tree == nil {
		return &fileResult{ctx: f}
	}
	root := tree.root()
	defer tree.free()
	if hasError(root) {
		errs, missing := countErrors(root)
		f.parseErrors, f.missingNodes = errs, missing
	}
	f.parseImports(root)
	f.walkScope(root)
	f.emitModuleScope(root)
	f.parseFileExtra(root)
	var keep []tsRec
	if e.opts.KeepTrees {
		keep = tree.recs
		tree.recs = nil
	}
	return &fileResult{ctx: f, recs: keep}
}

func countErrors(root tsNode) (int32, int32) {
	var errs, miss int32
	cur := cursorNew(root)
	defer cur.free()
	for {
		n := cur.node()
		if symOf(n) == symErrorMissing {
			errs++
		} else if isMissing(n) {
			miss++
		}
		if cur.first() {
			continue
		}
		for !cur.next() {
			if !cur.up() {
				return errs, miss
			}
		}
	}
}

func (e *fileCtx) emitModuleScope(root tsNode) {
	st := e.measurePrunedModule(root)
	if len(st.calls) == 0 && st.nTokens < 8 {
		return
	}
	loc := e.newSymbol()
	m := e.m(loc)
	copy(m, st.m)
	m[cCYCLOMATIC] = st.cyclomatic
	m[cCOGNITIVE] = st.cognitive
	m[cMAXNESTING] = st.maxNesting
	m[cNTOKENS] = st.nTokens
	m[cNOPERATORS] = st.nOperators
	m[cNOPERANDS] = st.nOperands
	m[cNDISTINCTOPERATORS] = int32(len(st.operators))
	m[cNDISTINCTOPERANDS] = int32(len(st.operands))
	m[cMAXLOOPDEPTH] = st.maxLoopDepth
	if e.rec.isGen {
		m[cISGENERATED] = 1
	}
	if e.rec.isTest {
		m[cISTEST] = 1
	}
	e.symNames[loc] = "<module>"
	e.symQuals[loc] = clip(e.rec.rel, 400)
	e.symKinds[loc] = "module"
	e.symSigs[loc] = "top-level statements of " + e.rec.rel
	e.symRets[loc] = ""
	e.symVis[loc] = ""
	e.symClass[loc] = ""

	m[cLINESTART] = int32(startRow(root)) + 1
	m[cLINEEND] = int32(endRow(root)) + 1
	m[cNLINES] = m[cLINEEND] - m[cLINESTART] + 1
	m[cBYTESTART] = int32(startByte(root))
	m[cBYTEEND] = int32(endByte(root))
	m[cPARENTID] = -1
	for _, c := range st.calls {
		if c.dynamic || c.text == "" {
			continue
		}
		e.pend = append(e.pend, pendCall{loc, e.fid, e.rec.moduleID, c.line, c.text, ""})
	}
	e.emitHazards(st, loc)
	for _, u := range st.inputSites {
		e.uinput = append(e.uinput, UserInput{0, loc, e.fid, u.line, e.put(u.kind), e.put(u.varname), u.inLoop})
	}
	for _, s := range st.secrets {
		e.secrets = append(e.secrets, Secret{0, loc, e.fid, s.line, e.put(s.value)})
	}
	for _, l := range st.literals {
		e.lits = append(e.lits, Literal{0, loc, e.fid, l.line, e.put(cKindNumber), e.put(clip(l.value, 200)), l.magic})
	}
}

func (e *fileCtx) measurePrunedModule(root tsNode) *bodyStats {

	return e.measurePruned(root)
}

type localToGlobal []int32

var l2gPool = sync.Pool{New: func() any { s := make(localToGlobal, 0, 64); return &s }}

func (e *emitter) apply(r *fileResult) {
	f := r.ctx
	g := e.g
	if e.opts.KeepTrees && len(r.recs) > 0 {
		for len(g.astTrees) < int(f.fid) {
			g.astTrees = append(g.astTrees, nil)
		}
		g.astTrees[f.fid-1] = &tsTree{recs: r.recs}
		r.recs = nil
	}

	n := len(f.symNames)

	lp := l2gPool.Get().(*localToGlobal)
	if cap(*lp) < n {
		*lp = make(localToGlobal, n)
	}
	l2g := (*lp)[:n]
	clear(l2g)
	for i := range n {
		l2g[i] = int32(g.Syms.grow())
		id := int(l2g[i])
		s := g.Syms
		blk := s.blocks[id/symBlock]
		row := blk[(id%symBlock)*numStoreCols:]
		src := f.symCols[i]
		for c, slot := range colSlot {
			if slot >= 0 {
				row[slot] = src[c]
			}
		}
		row[colSlot[cFILEID]] = f.fid
		row[colSlot[cMODULEID]] = f.rec.moduleID
		s.setStr(id, tName, f.symNames[i])
		s.setStr(id, tKind, f.symKinds[i])
		s.setStr(id, tClass, f.symClass[i])

		if p := src[cPARENTID]; p < 0 {
			row[colSlot[cPARENTID]] = 0
		} else {
			row[colSlot[cPARENTID]] = l2g[p] + 1
		}
	}
	remap := func(l int32) int32 {
		if l < 0 || int(l) >= len(l2g) {
			return 0
		}
		return l2g[l] + 1
	}
	_ = remap
	appendRows(g, f, l2g, remap)
	if len(f.params) > 0 {
		g.Params = append(g.Params, f.params...)
	}
	if len(f.fields) > 0 {
		g.Fields = append(g.Fields, f.fields...)
	}
	if len(f.lits) > 0 {
		g.Literals = append(g.Literals, f.lits...)
	}
	if len(f.marks) > 0 {
		g.Markers = append(g.Markers, f.marks...)
	}
	if len(f.attrs) > 0 {
		g.Attrs = append(g.Attrs, f.attrs...)
	}
	if len(f.imps) > 0 {
		g.Imports = append(g.Imports, f.imps...)
	}
	if len(f.hazs) > 0 {
		g.Hazards = append(g.Hazards, f.hazs...)
	}
	if len(f.classes) > 0 {
		g.Classes = append(g.Classes, f.classes...)
	}
	if len(f.impNames) > 0 {
		g.ImportNames = append(g.ImportNames, f.impNames...)
	}
	if len(f.listeners) > 0 {
		g.Listeners = append(g.Listeners, f.listeners...)
	}
	if len(f.timers) > 0 {
		g.Timers = append(g.Timers, f.timers...)
	}
	for i := range f.caches {
		c := &f.caches[i]
		labels := make([]string, 0, len(f.cacheWriters[i]))
		for _, w := range f.cacheWriters[i] {
			if w < 0 {
				labels = append(labels, "module")
			} else {
				labels = append(labels, itoa32(l2g[w]+1))
			}
		}

		sort.Strings(labels)
		c.writers = g.put(clip(strings.Join(labels, ","), 300))
	}
	f.cacheWriters = nil
	if len(f.caches) > 0 {
		g.Caches = append(g.Caches, f.caches...)
	}
	if len(f.jsx) > 0 {
		g.JSX = append(g.JSX, f.jsx...)
	}
	if len(f.hooks) > 0 {
		g.Hooks = append(g.Hooks, f.hooks...)
	}
	if len(f.uinput) > 0 {
		g.UserInput = append(g.UserInput, f.uinput...)
	}
	if len(f.routes) > 0 {
		g.Routes = append(g.Routes, f.routes...)
	}
	if len(f.secrets) > 0 {
		g.Secrets = append(g.Secrets, f.secrets...)
	}
	if len(f.exports) > 0 {
		g.Exports = append(g.Exports, f.exports...)
	}
	for i := range f.byName {
		nr := f.byName[i]
		e.addByName(nr.name, l2g[nr.local]+1, nr.fileID, nr.moduleID, nr.typeName)
	}
	for i := range f.byQual {
		q := f.byQual[i]
		e.byQual[q.qual] = l2g[q.local] + 1
		if q.relKey != "" {
			e.byQual[q.relKey] = l2g[q.local] + 1
		}
	}
	for _, p := range f.pend {
		e.pendSid = append(e.pendSid, l2g[p.sid]+1)
		e.pendFid = append(e.pendFid, p.fid)
		e.pendMid = append(e.pendMid, p.mid)
		e.pendLine = append(e.pendLine, p.line)
		e.pendName = append(e.pendName, p.name)
		e.pendType = append(e.pendType, p.typeName)
	}
	for _, h := range f.handlerSpans {
		g.hndFile = append(g.hndFile, f.fid)
		g.hndSpan = append(g.hndSpan, h)
	}
	for _, h := range f.handlerNames {
		e.handler[h] = true
	}
	e.bindingsByFile[f.fid] = f.bindings
	f.bindings = nil
	f.symCols = nil
	f.symNames, f.symQuals, f.symKinds, f.symSigs = nil, nil, nil, nil
	f.symRets, f.symVis, f.symClass = nil, nil, nil

	*lp = l2g[:0]
	l2gPool.Put(lp)
}

func appendRows(g *Graph, f *fileCtx, l2g localToGlobal, remap func(int32) int32) {

	fixParams(f.params, remap)
	fixFields(f.fields, remap)
	fixLits(f.lits, remap)
	fixHaz(f.hazs, remap)
	fixAttrs(f.attrs, remap)
	fixClasses(f.classes, remap)
	fixUI(f.uinput, remap)
	fixSecrets(f.secrets, remap)
	fixListeners(f.listeners, remap)
	fixTimers(f.timers, remap)
	fixJSX(f.jsx, remap)
	fixHooks(f.hooks, remap)
	fixRoutes(f.routes, remap)
	fixMarks(f.marks, remap)
	_ = g
	_ = l2g
}

func fixParams(p []Param, r func(int32) int32) {
	for i := range p {
		p[i].symID = r(p[i].symID)
	}
}
func fixFields(p []FieldRow, r func(int32) int32) {
	for i := range p {
		p[i].symID = r(p[i].symID)
	}
}

func fixOwner(id *int32, r func(int32) int32) {
	if *id >= 0 {
		*id = r(*id)
	} else {
		*id = 0
	}
}

func fixLits(p []Literal, r func(int32) int32) {
	for i := range p {
		fixOwner(&p[i].symID, r)
	}
}
func fixHaz(p []Hazard, r func(int32) int32) {
	for i := range p {
		p[i].symID = r(p[i].symID)
	}
}
func fixAttrs(p []Attribute, r func(int32) int32) {
	for i := range p {
		p[i].symID = r(p[i].symID)
	}
}
func fixClasses(p []ClassRow, r func(int32) int32) {
	for i := range p {
		p[i].symID = r(p[i].symID)
	}
}
func fixUI(p []UserInput, r func(int32) int32) {
	for i := range p {
		fixOwner(&p[i].symID, r)
	}
}
func fixSecrets(p []Secret, r func(int32) int32) {
	for i := range p {
		fixOwner(&p[i].symID, r)
	}
}
func fixListeners(p []Listener, r func(int32) int32) {
	for i := range p {
		fixOwner(&p[i].symID, r)
	}
}
func fixTimers(p []Timer, r func(int32) int32) {
	for i := range p {
		fixOwner(&p[i].symID, r)
	}
}
func fixJSX(p []JSXComp, r func(int32) int32) {
	for i := range p {
		fixOwner(&p[i].symID, r)
	}
}
func fixHooks(p []HookRow, r func(int32) int32) {
	for i := range p {
		fixOwner(&p[i].symID, r)
	}
}
func fixRoutes(p []Route, r func(int32) int32) {
	for i := range p {
		fixOwner(&p[i].symID, r)
	}
}
func fixMarks(p []Marker, r func(int32) int32) {
	for i := range p {
		if p[i].symID != 0 {
			p[i].symID = r(p[i].symID)
		}
	}
}

func (e *emitter) addByName(name string, sid, fid, mid int32, typeName string) {
	e.byNameIdx[name] = append(e.byNameIdx[name], gname{sid, fid, mid, typeName})
	e.nameExists[name] = true
}

type buildStats struct {
	FilesParsed int
	Failed      int
}

func build(o *Options) (*Graph, *buildStats, error) {
	initTables()

	g := &Graph{Syms: newSymStore()}
	g.Syms.strs = &g.strs
	g.Syms.mu = &g.strsMu
	e := &emitter{
		opts: o,
		g:    g, parser: tsParserNew(),
		handler: map[string]bool{}, nExtByCaller: map[int32]int32{},
		byNameIdx: map[string][]gname{}, byQual: map[string]int32{},
		nameExists: map[string]bool{}, graph: g,
		bindingsByFile: map[int32]map[string]binding{},
	}

	defer e.parser.free()
	d := &discovery{g: g, modIdx: map[string]int32{}, opts: o}
	workers := max(o.Workers, 1)
	st := &buildStats{}
	e.parseAll(d, o, workers, st)
	if o.KeepTrees {
		for len(g.astTrees) < len(g.Files) {
			g.astTrees = append(g.astTrees, nil)
		}
	}
	g.setMeta("files_skipped", "big=%d special=%d escaping_symlink=%d denied=%d walk_errors=%d",
		d.stats.big, d.stats.nSpecial, d.stats.escape,
		d.stats.denied, d.stats.walkErr)

	e.resolveCalls()
	e.resolveImportTargets()
	g.parseManifest(o.Root)
	g.buildIndex()
	g.materialize(e.nExtByCaller, e.handler)
	return g, st, nil
}

func (e *emitter) parseAll(d *discovery, o *Options, workers int, st *buildStats) {
	p := e.parser
	type cstJob struct {
		rec *discovered
		buf []byte
	}
	depth := max(workers, 1)
	if depth > maxPipelineDepth {
		depth = maxPipelineDepth
	}
	cst := make(chan *cstJob, depth)

	var readBusy, decodeBusy int64
	instrument := os.Getenv("CG_PIPELINE") != ""
	t0 := time.Now()

	d.enqueue = func(rec *discovered) {
		s := time.Now()
		out := p.parse(rec.data, nil)
		if instrument {
			readBusy += int64(time.Since(s))
		}
		cst <- &cstJob{rec, out}
	}
	go func() {
		defer close(cst)
		d.run(o.Root, o)
	}()

	type fixup struct {
		fid              int32
		errs, missingNds int32
	}
	var soft []fixup
	for j := range cst {
		s := time.Now()
		var tree *tsTree
		if j.buf != nil {
			var derr error
			tree, derr = decodeCST(j.buf, j.rec.data)
			if derr != nil {
				panic(fmt.Sprintf("cli cst decode failed: %v", derr))
			}
		}
		res := e.decodeOne(j.rec, tree)
		e.apply(res)
		if instrument {
			decodeBusy += int64(time.Since(s))
		}
		if fc := res.ctx; fc.parseErrors > 0 || fc.missingNodes > 0 {
			soft = append(soft, fixup{j.rec.fid, fc.parseErrors, fc.missingNodes})
		}
	}
	st.FilesParsed = len(d.files)
	if len(d.strs) > 0 {
		base := uint32(len(e.g.strs))
		e.g.strs = append(e.g.strs, d.strs...)
		shiftStrs(e.g.Files, fileStrOffs, base)
		shiftStrs(e.g.Modules, moduleStrOffs, base)
		d.strs = nil
	}

	for _, fx := range soft {
		fr := &e.g.Files[fx.fid-1]
		fr.nParseErrors, fr.nMissing = fx.errs, fx.missingNds
	}
	if instrument {
		wall := int64(time.Since(t0))
		fmt.Fprintf(os.Stderr, "pipeline: wall=%dms readerBusy=%dms decoderBusy=%dms overlap=%.0f%%\n",
			wall/1e6, readBusy/1e6, decodeBusy/1e6,
			100*float64(readBusy+decodeBusy)/float64(wall))
	}
}

var funcKind = map[string]string{
	"function_declaration":           "function",
	"generator_function_declaration": "function",
	"function_expression":            "function",
	"generator_function":             "function",
	"arrow_function":                 "function",
	"method_definition":              "method",
}

var typeKind = map[string]string{
	"class_declaration": "class",
	"class":             "class",
}

var loopNodes = map[string]bool{
	"for_statement": true, "for_in_statement": true,
	"while_statement": true, "do_statement": true,
}

var branchNodes = map[string]bool{
	"if_statement": true, "ternary_expression": true, "switch_case": true,
}

var nestNodes = map[string]bool{
	"if_statement": true, "for_statement": true, "for_in_statement": true,
	"while_statement": true, "do_statement": true, "switch_statement": true,
	"try_statement": true, "catch_clause": true, "finally_clause": true,
	"with_statement": true, "arrow_function": true, "function_expression": true,
	"generator_function": true, "function_declaration": true,
	"generator_function_declaration": true, "labeled_statement": true,
}

var callNodes = map[string]bool{"call_expression": true, "new_expression": true}

var operatorNodes = map[string]bool{
	"binary_expression": true, "unary_expression": true,
	"assignment_expression": true, "augmented_assignment_expression": true,
	"update_expression": true, "subscript_expression": true,
	"member_expression": true, "ternary_expression": true,
	"await_expression": true, "yield_expression": true, "spread_element": true,
}

var stringNodes = map[string]bool{"string": true, "template_string": true}
var numberNodes = map[string]bool{"number": true}
var commentNodes = map[string]bool{"comment": true}
var ifNodes = map[string]bool{"if_statement": true}

var counterCols = map[string]int{
	"return_statement":                cNRETURNS,
	"await_expression":                cNAWAIT,
	"yield_expression":                cNYIELD,
	"ternary_expression":              cNTERNARY,
	"switch_statement":                cNSWITCH,
	"switch_case":                     cNCASES,
	"switch_default":                  cNCASES,
	"try_statement":                   cNTRY,
	"catch_clause":                    cNCATCH,
	"finally_clause":                  cNFINALLY,
	"throw_statement":                 cNTHROW,
	"labeled_statement":               cNLABELS,
	"with_statement":                  cNWITHSTMT,
	"regex":                           cNREGEXLIT,
	"optional_chain":                  cNOPTIONALCHAIN,
	"spread_element":                  cNSPREAD,
	"rest_pattern":                    cNSPREAD,
	"object_pattern":                  cNDESTRUCTURE,
	"array_pattern":                   cNDESTRUCTURE,
	"subscript_expression":            cNCOMPUTEDMEMBER,
	"member_expression":               cNMEMBERACCESS,
	"this":                            cNTHISREFS,
	"update_expression":               cNINCDEC,
	"augmented_assignment_expression": cNCOMPOUNDASSIGN,
	"assignment_expression":           cNASSIGN,
	"variable_declarator":             cNLOCALS,
	"jsx_element":                     cNJSXELEMENTS,
	"jsx_self_closing_element":        cNJSXELEMENTS,
	"arrow_function":                  cNLAMBDA,
	"function_expression":             cNLAMBDA,
	"generator_function":              cNGENERATOR,
	"generator_function_declaration":  cNGENERATOR,
}

type loopCall struct {
	needle string
	col    int
}

var loopCallCols = []loopCall{
	{"RegExp", cREGEXINLOOP},
	{"readFileSync", cIOINLOOP},
	{"writeFileSync", cIOINLOOP},
	{"existsSync", cIOINLOOP},
	{"readFile", cIOINLOOP},
	{"fetch", cIOINLOOP},
	{"query", cQUERYINLOOP},
	{"execute", cQUERYINLOOP},
	{"findOne", cQUERYINLOOP},
	{"findAll", cQUERYINLOOP},
	{"addEventListener", cNLISTENERADDINLOOP},
	{"setTimeout", cNTIMERINLOOP},
	{"setInterval", cNTIMERINLOOP},
}

type nodePlan struct {
	named    bool
	elifCand bool
	nest     bool
	loop     bool
	branch   bool
	counter  int
	isAssign bool
	flag     int
	kind     uint8
}

const (
	kPlain = iota
	kCall
	kOperator
	kString
	kNumber
	kComment
)

var plans []nodePlan
var symFuncKind []string
var symTypeKind []string
var symIsAnonym []bool

func buildPlans() {

	nsym := len(symNames)
	plans = make([]nodePlan, nsym)
	symFuncKind = make([]string, nsym)
	symTypeKind = make([]string, nsym)
	symIsAnonym = make([]bool, nsym)
	lookup := func(name string) int {
		s := symLookup(name, true)
		if s == 0 {
			s = -1
		}
		return s
	}
	for s := range nsym {
		name := symNames[s]
		named := symNamed[s]
		p := nodePlan{named: named, counter: -1, flag: -1}
		if callNodes[name] {
			p.kind = kCall
		} else if operatorNodes[name] {
			p.kind = kOperator
		} else if stringNodes[name] {
			p.kind = kString
		} else if numberNodes[name] {
			p.kind = kNumber
		} else if commentNodes[name] {
			p.kind = kComment
		}
		p.elifCand = ifNodes[name]
		p.nest = named && nestNodes[name]
		p.loop = loopNodes[name]
		p.branch = named && branchNodes[name]
		if c, ok := counterCols[name]; ok {
			p.counter = c
		}
		p.isAssign = named && name == "assignment_expression"
		plans[s] = p
	}
	for name, k := range funcKind {
		if s := lookup(name); s >= 0 {
			symFuncKind[s] = k
			symIsAnonym[s] = anonFnNodes[name]
		}
	}
	for name, k := range typeKind {
		if s := lookup(name); s >= 0 {
			symTypeKind[s] = k
		}
	}
}

var anonFnNodes = map[string]bool{
	"arrow_function": true, "function_expression": true,
	"generator_function": true, "class": true,
}

var fnNodeTypes = map[string]bool{
	"function_declaration": true, "generator_function_declaration": true,
	"function_expression": true, "generator_function": true,
	"arrow_function": true, "method_definition": true, "class_static_block": true,
}

var loopNodeTypes = map[string]bool{
	"for_statement": true, "for_in_statement": true,
	"while_statement": true, "do_statement": true,
}

var condNodeTypes = map[string]bool{
	"if_statement": true, "ternary_expression": true, "switch_case": true,
	"else_clause": true, "catch_clause": true,
}

var (
	symSMethodDefinition, symSClassStaticBlock                                 int
	symSClassDeclaration, symSClass                                            int
	symSImport, symSImportStatement                                            int
	symSExportStatement, symSVariableDeclarator                                int
	symSAssignmentExpression, symSCallExpr, symSNewExpr                        int
	symSMemberExpression, symSSubscriptExpression                              int
	symSJSXOpening, symSJSXSelfClosing, symSRegex                              int
	symSIfStatement, symSElseClause, symSCatchClause                           int
	symSTernary, symSSwitchCase, symSForStatement, symSForIn                   int
	symSWhile, symSDo, symSArrow, symSFuncExpr, symSGenFunc, symSDirective     int
	symSReturnStatement, symSExpressionStatement, symSArguments                int
	symSBinary, symSUnary, symSAwait, symSAugAssign                            int
	symSObject, symSArray, symSTemplateString, symSIdentifier, symSJXAttribute int
	symSTry, symSFinally, symSLabeled, symSWith, symSOptionalChain             int
	symSClassBody, symSProgram, symSDefault, symSParenthesized                 int
	symSImportSpecifier, symSNamespaceImport, symSImportClause                 int
	symSComment, symSClassHeritage, symSPair, symSFieldDefinition              int
	symSProperty, symSIndex, symSPattern, symSJSXExpression                    int
)

func initTables() {
	need(&symSMethodDefinition, "method_definition")
	need(&symSClassStaticBlock, "class_static_block")
	need(&symSClassDeclaration, "class_declaration")
	need(&symSClass, "class")
	need(&symSExportStatement, "export_statement")
	need(&symSVariableDeclarator, "variable_declarator")
	need(&symSAssignmentExpression, "assignment_expression")
	need(&symSCallExpr, "call_expression")
	need(&symSNewExpr, "new_expression")
	need(&symSMemberExpression, "member_expression")
	need(&symSSubscriptExpression, "subscript_expression")
	need(&symSJSXOpening, "jsx_opening_element")
	need(&symSJSXSelfClosing, "jsx_self_closing_element")
	need(&symSRegex, "regex")
	need(&symSIfStatement, "if_statement")
	need(&symSElseClause, "else_clause")
	need(&symSCatchClause, "catch_clause")
	need(&symSTernary, "ternary_expression")
	need(&symSSwitchCase, "switch_case")
	need(&symSForStatement, "for_statement")
	need(&symSForIn, "for_in_statement")
	need(&symSWhile, "while_statement")
	need(&symSDo, "do_statement")
	need(&symSArrow, "arrow_function")
	need(&symSFuncExpr, "function_expression")
	need(&symSGenFunc, "generator_function")
	need(&symSDirective, "")
	need(&symSReturnStatement, "return_statement")
	need(&symSExpressionStatement, "expression_statement")
	need(&symSArguments, "arguments")
	need(&symSBinary, "binary_expression")
	need(&symSUnary, "unary_expression")
	need(&symSAwait, "await_expression")
	need(&symSAugAssign, "augmented_assignment_expression")
	need(&symSObject, "object")
	need(&symSArray, "array")
	need(&symSTemplateString, "template_string")
	need(&symSIdentifier, "identifier")
	need(&symSJXAttribute, "jsx_attribute")
	need(&symSTry, "try_statement")
	need(&symSFinally, "finally_clause")
	need(&symSLabeled, "labeled_statement")
	need(&symSWith, "with_statement")
	need(&symSOptionalChain, "optional_chain")
	need(&symSClassBody, "class_body")
	need(&symSProgram, "program")
	need(&symSDefault, "default")
	need(&symSParenthesized, "parenthesized_expression")
	need(&symSImportSpecifier, "import_specifier")
	need(&symSNamespaceImport, "namespace_import")
	need(&symSImportClause, "import_clause")
	need(&symSComment, "comment")
	need(&symSClassHeritage, "class_heritage")
	need(&symSPair, "pair")
	need(&symSFieldDefinition, "field_definition")
	need(&symSProperty, "property_identifier")
	need(&symSIndex, "index")
	need(&symSPattern, "pattern")
	need(&symSJSXExpression, "jsx_expression")
	need(&symSImport, "import")
	need(&symSImportStatement, "import_statement")
	buildPlans()
}

func need(t *int, name string) {
	s := symLookup(name, true)
	if s == 0 {
		s = symLookup(name, false)
	}
	*t = s
}

type callRec struct {
	text    string
	line    int32
	dynamic bool
	inLoop  bool
}

type litRec struct {
	kind  string
	value string
	line  int32
	magic bool
}

type inputRec struct {
	varname string
	kind    string
	line    int32
	inLoop  bool
}

type secretRec struct {
	value string
	line  int32
}

type bodyStats struct {
	m                                               []int32
	cyclomatic, cognitive, maxNesting, maxLoopDepth int32
	nTokens, nOperators, nOperands                  int32
	operators, operands                             map[string]bool
	calls                                           []callRec
	literals                                        []litRec
	inputSites                                      []inputRec
	secrets                                         []secretRec
}

func newBodyStats() *bodyStats {
	return &bodyStats{
		m:         make([]int32, numSymCols),
		operators: map[string]bool{},
		operands:  map[string]bool{},
		calls:     make([]callRec, 0, 16),
		literals:  make([]litRec, 0, 8),
	}
}

func (b *bodyStats) reset() {
	for i := range b.m {
		b.m[i] = 0
	}
	b.cyclomatic, b.cognitive, b.maxNesting, b.maxLoopDepth = 1, 0, 0, 0
	b.nTokens, b.nOperators, b.nOperands = 0, 0, 0
	clear(b.operators)
	clear(b.operands)
	b.calls = b.calls[:0]
	b.literals = b.literals[:0]
	b.inputSites = b.inputSites[:0]
	b.secrets = b.secrets[:0]
}

func (e *fileCtx) measure(body tsNode) *bodyStats {
	return e.measureWalk(body, false)
}

func (e *fileCtx) measurePruned(body tsNode) *bodyStats {
	return e.measureWalk(body, true)
}

func (e *fileCtx) measureWalk(body tsNode, prune bool) *bodyStats {
	st := e.stats
	st.reset()
	cur := cursorNew(body)
	defer cur.free()
	depth := int32(0)
	loopDepth := int32(0)
	var nestStack, loopStack []int32

	for {
		node := cur.node()
		for len(nestStack) > 0 && nestStack[len(nestStack)-1] >= depth {
			nestStack = nestStack[:len(nestStack)-1]
		}
		for len(loopStack) > 0 && loopStack[len(loopStack)-1] >= depth {
			loopStack = loopStack[:len(loopStack)-1]
			if loopDepth > 0 {
				loopDepth--
			}
		}

		s := symOf(node)
		p := plans[s]
		t := symNames[s]

		isElif := false
		if p.elifCand {
			if par, ok := parent(node); ok {
				if symOf(par) == symSIfStatement {
					if alt, ok := field(par, fAlternative); ok {
						isElif = sameNode(alt, node)
					}
				} else if gp, ok2 := parent(par); ok2 && symOf(gp) == symSIfStatement {
					if alt, ok3 := field(gp, fAlternative); ok3 && sameNode(alt, par) {
						if first := namedChildAt(par, 0); hasNode(first) {
							isElif = sameNode(first, node)
						}
					}
				}
			}
		}

		if p.nest && !isElif {
			nestStack = append(nestStack, depth)
			if int32(len(nestStack)) > st.maxNesting {
				st.maxNesting = int32(len(nestStack))
			}
		}
		nest := int32(len(nestStack))
		if p.named && p.loop {
			loopStack = append(loopStack, depth)
			loopDepth++
			if loopDepth > st.maxLoopDepth {
				st.maxLoopDepth = loopDepth
			}
			st.cyclomatic++
			if nest > 1 {
				st.cognitive += nest
			} else {
				st.cognitive++
			}
			st.m[cNLOOPS]++
		} else if p.branch {
			st.cyclomatic++
			if isElif {
				st.cognitive++
			} else if nest > 1 {
				st.cognitive += nest
			} else {
				st.cognitive++
			}
			st.m[cNBRANCHES]++
			if isElif {
				st.m[cNELIF]++
			}
			if loopDepth > 0 {
				st.m[cBRANCHINLOOP]++
			}
		}

		if p.counter >= 0 {
			st.m[p.counter]++
		}
		if p.isAssign {
			if left, ok := field(node, fLeft); ok {
				lt := clip(e.text(left), 80)
				if strings.HasPrefix(lt, "window.") || strings.HasPrefix(lt, "globalThis.") ||
					strings.HasPrefix(lt, "global.") {
					st.m[cNGLOBALWRITE]++
				}
			}
		}

		switch p.kind {
		case kPlain:
			if childCount(node) == 0 {
				st.nTokens++
				st.nOperands++
				st.operands[clip(e.text(node), 40)] = true
			}
		case kCall:
			e.onCall(node, st, loopDepth, nest, t)
		case kOperator:
			st.nOperators++
			st.operators[t] = true
		case kString:
			txt := e.text(node)
			st.m[cNSTRINGLIT]++
			st.operands[clip(txt, 40)] = true
			st.nOperands++
			e.onString(node, txt, st, loopDepth)
		case kNumber:
			txt := cgStrip(e.text(node))
			st.nOperands++
			st.operands[txt] = true
			if !magicNumbers[txt] && reNum.MatchString(txt) {
				st.m[cNMAGIC]++
				st.literals = append(st.literals, litRec{"number", txt, int32(startRow(node)) + 1, true})
			}
			if strings.Contains(txt, ".") || strings.Contains(strings.ToLower(txt), "e") {
				st.m[cNFLOATLIT]++
			}
		case kComment:
			st.m[cNCOMMENTLINES] += int32(endRow(node) - startRow(node) + 1)
		}

		e.onNode(node, st, loopDepth, nest, t)

		descend := true
		if prune && s < len(symFuncKind) &&
			(symFuncKind[s] != "" || symTypeKind[s] != "") {
			descend = false
		}
		if descend && cur.first() {
			depth++
			continue
		}
		for !cur.next() {
			if !cur.up() {
				st.nTokens += st.nOperators
				return st
			}
			depth--
		}
	}
}

type binding struct {
	source, imported string
	external         bool
}

type mcCand struct {
	line           int32
	ctor           string
	weak, exported bool
	konst          bool
}

type span struct {
	start, end int32
	sid        int32
}

type scope struct {
	symbolID   int32
	qualPrefix string
	typeName   string
	typeID     int32
	depth      int
}

type fileCtx struct {
	e     *emitter
	fid   int32
	src   []byte
	rec   *discovered
	stats *bodyStats

	spans      []span
	spanStarts []int32
	exported   map[string]bool
	bindings   map[string]binding
	mcCands    map[string]mcCand

	params       []Param
	fields       []FieldRow
	lits         []Literal
	marks        []Marker
	attrs        []Attribute
	imps         []Import
	hazs         []Hazard
	classes      []ClassRow
	exports      []ExportRow
	impNames     []ImportName
	listeners    []Listener
	timers       []Timer
	caches       []ModuleCache
	cacheWriters [][]int32
	jsx          []JSXComp
	hooks        []HookRow
	uinput       []UserInput
	routes       []Route
	secrets      []Secret

	symNames []string
	symQuals []string
	symKinds []string
	symSigs  []string
	symRets  []string
	symVis   []string
	symClass []string
	symCols  [][]int32

	byName       []nameRef
	byQual       []qualRef
	pend         []pendCall
	handlerNames []string
	mcUse        map[string]*[4]int32
	mcWriters    map[string]map[int32]bool

	head string

	parseErrors, missingNodes int32
	mcOrder                   []string
	handlerSpans              []int32
}

type nameRef struct {
	name     string
	local    int32
	fileID   int32
	moduleID int32
	typeName string
}

type qualRef struct {
	qual   string
	local  int32
	relKey string
}

type pendCall struct {
	sid, fid, mid, line int32
	name                string
	typeName            string
}

func newFileCtx(e *emitter, r *discovered) *fileCtx {
	f := &fileCtx{
		e: e, fid: r.fid, src: r.data, rec: r,
		stats: newBodyStats(), exported: map[string]bool{},
		bindings: map[string]binding{}, mcCands: map[string]mcCand{},
		mcUse: map[string]*[4]int32{}, mcWriters: map[string]map[int32]bool{},
	}
	h := ""
	if len(r.text) > 200 {
		h = r.text[:200]
	}
	f.head = h
	return f
}

func (e *fileCtx) text(n tsNode) string {
	return decodeReplace(e.src[startByte(n):endByte(n)])
}

func (e *fileCtx) namedChildren(n tsNode) []tsNode {
	var out []tsNode
	eachNamedChild(n, func(c tsNode) { out = append(out, c) })
	return out
}

func isExported(n tsNode) bool {
	cur := n
	for range 4 {
		p, ok := parent(cur)
		if !ok {
			return false
		}
		pt := symOf(p)
		if pt == symSExportStatement {
			return true
		}

		if pt == symSClassBody || pt == symSProgram || symNames[pt] == "statement_block" {
			return false
		}
		cur = p
	}
	return false
}

func (e *fileCtx) isDefaultExport(n tsNode) bool {
	cur := n
	for range 3 {
		p, ok := parent(cur)
		if !ok {
			return false
		}
		if symOf(p) == symSExportStatement {
			if _, ok2 := field(p, fValue); ok2 {
				return true
			}
			dflt := false
			forEachChild(p, func(c tsNode) {
				if symOf(c) == symSDefault {
					dflt = true
				}
			})
			return dflt
		}
		cur = p
	}
	return false
}

func atModuleScope(n tsNode) bool {
	cur := n
	for {
		p, ok := parent(cur)
		if !ok {
			return true
		}
		if fnNodeTypes[symNames[symOf(p)]] {
			return false
		}
		cur = p
	}
}

func (e *fileCtx) nodeName(n tsNode) string {
	if own, ok := field(n, fName); ok {
		return strings.TrimSpace(e.text(own))
	}
	t := symNames[symOf(n)]
	if anonFnNodes[t] {
		return e.bindingName(n)
	}
	return ""
}

func (e *fileCtx) bindingName(n tsNode) string {
	cur := n
	for range 4 {
		p, ok := parent(cur)
		if !ok {
			return ""
		}
		switch symNames[symOf(p)] {
		case "variable_declarator":
			if nm, ok2 := field(p, fName); ok2 {
				return strings.TrimSpace(e.text(nm))
			}
			return ""
		case "pair":
			if k, ok2 := field(p, fKey); ok2 {
				return strings.Trim(strings.TrimSpace(e.text(k)), "'\"")
			}
			return ""
		case "field_definition":
			if pr, ok2 := field(p, fProperty); ok2 {
				return strings.TrimSpace(e.text(pr))
			}
			return ""
		case "assignment_expression":
			left, ok2 := field(p, fLeft)
			if !ok2 {
				return ""
			}
			txt := strings.TrimSpace(e.text(left))
			if i := strings.LastIndex(txt, "."); i >= 0 {
				return txt[i+1:]
			}
			return txt
		case "export_statement":
			return "default"
		case "parenthesized_expression", "await_expression":
			cur = p
			continue
		}
		return ""
	}
	return ""
}

type workItem struct {
	node  tsNode
	scope scope
}

var workStackPool = sync.Pool{New: func() any { s := make([]workItem, 0, 32); return &s }}

func (e *fileCtx) walkScope(root tsNode) {
	sp := workStackPool.Get().(*[]workItem)
	stack := (*sp)[:0]

	defer func() { *sp = stack[:0]; workStackPool.Put(sp) }()
	eachNamedChild(root, func(c tsNode) {
		stack = append(stack, workItem{c, scope{symbolID: -1}})
	})

	for i, j := 0, len(stack)-1; i < j; i, j = i+1, j-1 {
		stack[i], stack[j] = stack[j], stack[i]
	}
	for len(stack) > 0 {
		cur := stack[len(stack)-1]
		stack = stack[:len(stack)-1]
		s := symOf(cur.node)
		kind := ""
		if s < len(symFuncKind) {
			kind = symFuncKind[s]
		}
		if kind != "" {
			nm := e.nodeName(cur.node)

			if kind == "function" && symIsAnonym[s] && e.bindingName(cur.node) == "" {
				kind = "closure"
			}
			local := e.emitFunction(cur.node, kind, cur.scope)
			inner := scope{symbolID: local, qualPrefix: cur.scope.qualPrefix + nmOrQ(nm) + ".",
				typeName: cur.scope.typeName, typeID: cur.scope.typeID, depth: cur.scope.depth + 1}
			body, ok := field(cur.node, fBody)
			target := cur.node
			if ok {
				target = body
			}
			pushChildren(&stack, target, inner)
			continue
		}
		if s < len(symTypeKind) {
			if k2 := symTypeKind[s]; k2 != "" {
				local := e.emitType(cur.node, k2, cur.scope)
				nm := e.nodeName(cur.node)
				if nm == "" {
					nm = "?"
				}
				inner := scope{symbolID: local, qualPrefix: cur.scope.qualPrefix + nm + ".",
					typeName: nm, typeID: local, depth: cur.scope.depth + 1}
				body, ok := field(cur.node, fBody)
				target := cur.node
				if ok {
					body, ok2 := body, true
					_ = body
					_ = ok2
				}
				if ok {
					target = body
				}
				pushChildren(&stack, target, inner)
				continue
			}
		}
		pushChildren(&stack, cur.node, cur.scope)
	}
}

func nmOrQ(nm string) string {
	if nm == "" {
		return "?"
	}
	return nm
}

func pushChildren(stack *[]workItem, n tsNode, sc scope) {
	kids := make([]tsNode, 0, 8)
	eachNamedChild(n, func(c tsNode) { kids = append(kids, c) })
	for _, kid := range slices.Backward(kids) {
		*stack = append(*stack, workItem{kid, sc})
	}
}

func (e *fileCtx) newSymbol() int32 {
	loc := int32(len(e.symNames))
	e.symNames = append(e.symNames, "")
	e.symQuals = append(e.symQuals, "")
	e.symKinds = append(e.symKinds, "")
	e.symSigs = append(e.symSigs, "")
	e.symRets = append(e.symRets, "")
	e.symVis = append(e.symVis, "")
	e.symClass = append(e.symClass, "")

	e.symCols = append(e.symCols, make([]int32, numSymCols))
	return loc
}

func (e *fileCtx) m(loc int32) []int32 { return e.symCols[loc] }

var reHandlerParam = regexp.MustCompile(`(?i)^\(?\s*(?:_?req(?:uest)?\s*,\s*_?res(?:ponse)?|_?res(?:ponse)?\s*,\s*_?req(?:uest)?|_?ctx\b|_?context\b|event\s*,\s*context|_?err(?:or)?\s*,\s*_?req(?:uest)?\s*,\s*_?res(?:ponse)?)`)

var reHookName = regexp.MustCompile(`^use[A-Z_]`)
var reComponentName = regexp.MustCompile(`^[A-Z][A-Za-z0-9]*$`)
var reSetState = regexp.MustCompile(`^set[A-Z_]`)
var reGeneratedHint = regexp.MustCompile(`^(__webpack|__turbopack|__vite|_interopRequire|__esModule|__importDefault|__awaiter|__generator|__extends)`)
var reNum = regexp.MustCompile(`^[-+]?(?:0[xXbBoO][0-9a-fA-F_]+|[\d_]+(?:\.[\d_]*)?(?:[eE][-+]?\d+)?)[uUlLfFdD]*$`)
var reHookCleanup = regexp.MustCompile(`return\s*(?:\(\s*\)|function|\w+\s*=>)`)

var magicNumbers = func() map[string]bool {
	m := map[string]bool{"0x0": true, "0x1": true, "0xff": true, "0xFF": true,
		"0.0": true, "1.0": true, "-1": true, "": true}
	for _, v := range []int{0, 1, 2, -1, 10, 100, 1000, 8, 16, 32, 64, 128, 256, 512, 1024,
		255, 65535, 4096, 24, 60, 365, 7, 12, 3, 4, 6} {
		m[strconv.Itoa(v)] = true
	}
	return m
}()

func (e *fileCtx) emitFunction(n tsNode, kind string, sc scope) int32 {
	name0 := e.nodeName(n)
	name := name0
	if name == "" {
		name = "(anonymous)"
	}
	qual := sc.qualPrefix + name
	body, ok := field(n, fBody)
	if !ok {
		body = n
	}
	st := e.measure(body)
	loc := e.newSymbol()
	m := e.m(loc)

	copy(m[cCYCLOMATIC:], []int32{st.cyclomatic, st.cognitive, st.maxNesting, st.nTokens,
		st.nOperators, st.nOperands, int32(len(st.operators)), int32(len(st.operands))})
	m[cMAXLOOPDEPTH] = st.maxLoopDepth
	m[cSLOC] = e.slocOf(n)
	m[cBODYBYTES] = int32(endByte(body) - startByte(body))
	if e.rec.isGen {
		m[cISGENERATED] = 1
	}

	copy(m, st.m)

	m[cCYCLOMATIC] = st.cyclomatic
	m[cCOGNITIVE] = st.cognitive
	m[cMAXNESTING] = st.maxNesting
	m[cNTOKENS] = st.nTokens
	m[cNOPERATORS] = st.nOperators
	m[cNOPERANDS] = st.nOperands
	m[cNDISTINCTOPERATORS] = int32(len(st.operators))
	m[cNDISTINCTOPERANDS] = int32(len(st.operands))
	m[cSLOC] = e.slocOf(n)
	m[cBODYBYTES] = int32(endByte(body) - startByte(body))
	m[cMAXLOOPDEPTH] = st.maxLoopDepth

	sig := e.signatureOf(n)
	e.functionFlags(n, loc, sc, name0, sig, m)

	doc := e.docstringLines(e.statementOf(n))
	m[cNDOCLINES] = doc
	if doc > 0 {
		m[cHASDOC] = 1
	}

	e.symNames[loc] = name
	e.symQuals[loc] = clip(qual, 400)
	e.symKinds[loc] = kind
	e.symSigs[loc] = clip(sig, 400)
	e.symRets[loc] = ""
	e.symVis[loc] = e.visibilityOf(name0)
	e.symClass[loc] = clip(sc.typeName, 120)
	m[cLINESTART] = int32(startRow(n)) + 1
	m[cLINEEND] = int32(endRow(n)) + 1
	m[cNLINES] = m[cLINEEND] - m[cLINESTART] + 1
	m[cBYTESTART] = int32(startByte(n))
	m[cBYTEEND] = int32(endByte(n))
	m[cPARENTID] = sc.symbolID

	e.emitParams(n, loc)
	e.emitAttributes(n, loc)
	for _, c := range st.calls {
		if c.dynamic || c.text == "" {
			continue
		}
		e.pend = append(e.pend, pendCall{loc, e.fid, e.rec.moduleID, c.line, c.text, sc.typeName})
	}
	e.emitHazards(st, loc)
	for _, u := range st.inputSites {
		e.uinput = append(e.uinput, UserInput{0, loc, e.fid, u.line, e.put(u.kind), e.put(u.varname), u.inLoop})
	}
	for _, s := range st.secrets {
		e.secrets = append(e.secrets, Secret{0, loc, e.fid, s.line, e.put(s.value)})
	}
	for _, l := range st.literals {
		e.lits = append(e.lits, Literal{0, loc, e.fid, l.line, e.put(cKindNumber), e.put(clip(l.value, 200)), l.magic})
	}
	e.spans = append(e.spans, span{int32(startByte(n)), int32(endByte(n)), loc})

	e.byName = append(e.byName, nameRef{name, loc, e.fid, e.rec.moduleID, sc.typeName})
	e.byQual = append(e.byQual, qualRef{qual, loc, e.rec.rel + ":" + qual})
	return loc
}

func (e *fileCtx) statementOf(n tsNode) tsNode {
	cur := n
	for {
		p, ok := parent(cur)
		if !ok {
			break
		}
		if _, has := prevSibling(cur); has {
			break
		}
		cur = p
		if symOf(cur) == symSProgram {
			break
		}
	}
	return cur
}

func (e *fileCtx) visibilityOf(name string) string {
	if strings.HasPrefix(name, "#") || strings.HasPrefix(name, "_") {
		return "private"
	}
	return "public"
}

func (e *fileCtx) signatureOf(n tsNode) string {
	body, ok := field(n, fBody)
	end := endByte(n)
	if ok {
		end = startByte(body)
	}
	return strings.Join(cgSplit(strings.TrimSpace(decodeReplace(e.src[startByte(n):end]))), " ")
}

func (e *fileCtx) slocOf(n tsNode) int32 {
	seg := decodeReplace(e.src[startByte(n):endByte(n)])
	var cnt int32
	cgLines(seg, func(l string) {
		t := strings.TrimFunc(l, isCgSpace)
		if t == "" {
			return
		}
		switch {
		case strings.HasPrefix(t, "//"), strings.HasPrefix(t, "#"),
			strings.HasPrefix(t, "/*"), strings.HasPrefix(t, "*"),
			strings.HasPrefix(t, "*/"), strings.HasPrefix(t, `"""`),
			strings.HasPrefix(t, "'''"), strings.HasPrefix(t, "--"),
			strings.HasPrefix(t, "%"):
			return
		}
		cnt++
	})
	return cnt
}

var docPrefixes = []string{"///", "/**", "##", `"""`, "'''", "#'", "--|"}

func (e *fileCtx) docstringLines(n tsNode) int32 {
	prev, ok := prevSibling(n)
	var cnt int32
	for ok {
		if !commentNodes[symNames[symOf(prev)]] {
			break
		}
		txt := strings.TrimLeft(e.text(prev), " \t\r\n\v\f")
		isDoc := false
		for _, p := range docPrefixes {
			if strings.HasPrefix(txt, p) {
				isDoc = true
				break
			}
		}
		if isDoc {
			cnt += int32(endRow(prev) - startRow(prev) + 1)
		} else if cnt == 0 && int(endRow(prev)+1) >= int(startRow(n)) {
			cnt += int32(endRow(prev) - startRow(prev) + 1)
		} else {
			break
		}
		prev, ok = prevSibling(prev)
	}
	return cnt
}

func (e *fileCtx) functionFlags(n tsNode, loc int32, sc scope, name0, sig string, m []int32) {
	t := symNames[symOf(n)]
	params, hasParams := field(n, fParameters)
	nParams, nOpt := 0, 0
	ptxt := ""
	if hasParams {
		eachNamedChild(params, func(p tsNode) {
			if commentNodes[symNames[symOf(p)]] {
				return
			}
			nParams++
			if symNames[symOf(p)] == "assignment_pattern" {
				nOpt++
			}
		})
		ptxt = e.text(params)
	} else if _, ok := field(n, fParameter); ok {
		nParams = 1
	}

	isAsync, isGen, isStatic := false, false, false
	forEachChild(n, func(c tsNode) {
		switch symNames[symOf(c)] {
		case "async":
			isAsync = true
		case "*":
			isGen = true
		case "static":
			isStatic = true
		}
	})
	if t == "generator_function" || t == "generator_function_declaration" {
		isGen = true
	}
	exported := isExported(n) || e.exported[name0]
	parentOK, isIife := false, false
	if p, ok := parent(n); ok {
		parentOK = true
		ps := symOf(p)
		if ps == symSParenthesized || ps == symSCallExpr || ps == symSUnary {
			isIife = hasNode(e.nearestCallOf(n))
		}
	}
	_ = parentOK

	isHandler := reHandlerParam.MatchString(ptxt)
	m[cNPARAMS] = int32(nParams)
	m[cNOPTIONALPARAMS] = int32(nOpt)
	setInt(m, cISASYNC, isAsync)
	setInt(m, cISGENERATOR, isGen)
	setInt(m, cISARROW, t == "arrow_function")
	setInt(m, cISIIFE, isIife)
	setInt(m, cISSTATIC, isStatic)
	setInt(m, cISEXPORTED, exported)
	setInt(m, cISPUBLIC, exported || !(strings.HasPrefix(name0, "#") || strings.HasPrefix(name0, "_")))
	setInt(m, cISDEFAULTEXPORT, e.isDefaultExport(n))
	setInt(m, cISTEST, e.rec.isTest || strings.HasPrefix(name0, "test") ||
		strings.HasPrefix(name0, "it_") || strings.HasPrefix(name0, "should"))
	setInt(m, cISENTRYPOINT, name0 == "main" || name0 == "bootstrap" || name0 == "start" ||
		strings.HasSuffix(e.rec.rel, "index.js") || strings.HasSuffix(e.rec.rel, "main.js") ||
		strings.HasSuffix(e.rec.rel, "cli.js") || strings.HasSuffix(e.rec.rel, "bin.js"))
	setInt(m, cISDEPRECATED, strings.Contains(sig, "@deprecated"))
	setInt(m, cISHANDLER, isHandler)
	setInt(m, cISHOOK, reHookName.MatchString(name0))
	setInt(m, cISCOMPONENT, reComponentName.MatchString(name0) &&
		(strings.HasSuffix(e.rec.rel, ".jsx") || strings.HasSuffix(e.rec.rel, ".js") ||
			strings.HasSuffix(e.rec.rel, ".mjs")))

	if isAsync && t == "arrow_function" {
		m[cNASYNCARROW] = 1
	} else {
		m[cNASYNCARROW] = 0
	}
}

func setInt(m []int32, col int, v bool) {
	if v {
		m[col] = 1
	} else {
		m[col] = 0
	}
}

func (e *fileCtx) nearestCallOf(n tsNode) tsNode {
	cur := n
	for range 3 {
		p, ok := parent(cur)
		if !ok {
			return tsNode{}
		}
		if symOf(p) == symSCallExpr {
			fn, ok2 := field(p, fFunction)
			if ok2 && (sameNode(fn, n) || (startByte(fn) <= startByte(n) && endByte(n) <= endByte(fn))) {
				return p
			}
			return tsNode{}
		}
		cur = p
	}
	return tsNode{}
}

func (e *fileCtx) emitParams(n tsNode, loc int32) {
	params, ok := field(n, fParameters)
	var kids []tsNode
	if ok {
		eachNamedChild(params, func(p tsNode) {
			if !commentNodes[symNames[symOf(p)]] {
				kids = append(kids, p)
			}
		})
	} else if bare, ok2 := field(n, fParameter); ok2 {
		kids = []tsNode{bare}
	}
	for pos, p := range kids {
		txt := strings.TrimSpace(e.text(p))
		pt := symNames[symOf(p)]
		optional := pt == "assignment_pattern"
		variadic := pt == "rest_pattern"
		destructured := false
		if pt == "object_pattern" || pt == "array_pattern" {
			destructured = true
		} else if pt == "assignment_pattern" {
			t := txt
			t = strings.TrimLeftFunc(t, isCgSpace)
			if len(t) > 0 && (t[0] == '{' || t[0] == '[') {
				destructured = true
			}
		}
		name := txt
		if pt == "assignment_pattern" {
			if lhs, ok2 := field(p, fLeft); ok2 {
				name = strings.TrimSpace(e.text(lhs))
			}
		}
		e.params = append(e.params, Param{loc, int32(pos), e.put(clip(name, 120)), e.put(""), true,
			optional, variadic, false, false, false, false, 1, int32(boolToInt(destructured))})
	}
}

func boolToInt(b bool) int {
	if b {
		return 1
	}
	return 0
}

func (e *fileCtx) emitAttributes(n tsNode, loc int32) {
	forEachChild(n, func(c tsNode) {
		if symNames[symOf(c)] != "decorator" {
			return
		}
		txt := strings.TrimSpace(e.text(c))
		name := strings.TrimSpace(strings.SplitN(strings.TrimLeft(txt, "@"), "(", 2)[0])
		e.attrs = append(e.attrs, Attribute{0, loc, e.fid, int32(startRow(c)) + 1, e.put(clip(name, 120)), e.put(clip(txt, 200))})
	})
}

func (e *fileCtx) emitType(n tsNode, kind string, sc scope) int32 {
	name0 := e.nodeName(n)
	name := name0
	if name == "" {
		name = "(anonymous)"
	}
	qual := sc.qualPrefix + name
	body, ok := field(n, fBody)
	if !ok {
		body = n
	}
	st := e.measurePruned(body)
	loc := e.newSymbol()
	m := e.m(loc)
	copy(m, st.m)
	m[cSLOC] = e.slocOf(n)
	if e.rec.isGen {
		m[cISGENERATED] = 1
	}
	m[cNTOKENS] = st.nTokens
	m[cNOPERATORS] = st.nOperators
	m[cNOPERANDS] = st.nOperands
	exported := isExported(n) || e.exported[name0]
	setInt(m, cISEXPORTED, exported)
	setInt(m, cISPUBLIC, !strings.HasPrefix(name, "_"))
	setInt(m, cISDEFAULTEXPORT, e.isDefaultExport(n))
	setInt(m, cISCOMPONENT, reComponentName.MatchString(name))
	doc := e.docstringLines(e.statementOf(n))
	m[cNDOCLINES] = doc
	if doc > 0 {
		m[cHASDOC] = 1
	}
	sig := ""
	if i := strings.Index(e.text(n), "{"); i >= 0 {
		sig = strings.TrimSpace(e.text(n)[:i])
	} else {
		sig = strings.TrimSpace(e.text(n))
	}
	e.symNames[loc] = name
	e.symQuals[loc] = clip(qual, 400)
	e.symKinds[loc] = kind
	e.symSigs[loc] = clip(sig, 400)
	e.symRets[loc] = ""
	e.symVis[loc] = e.visibilityOf(name)
	e.symClass[loc] = clip(name0, 120)
	m[cLINESTART] = int32(startRow(n)) + 1
	m[cLINEEND] = int32(endRow(n)) + 1
	m[cNLINES] = m[cLINEEND] - m[cLINESTART] + 1
	m[cBYTESTART] = int32(startByte(n))
	m[cBYTEEND] = int32(endByte(n))
	m[cPARENTID] = sc.symbolID

	e.emitAttributes(n, loc)
	for _, c := range st.calls {
		if c.dynamic || c.text == "" {
			continue
		}
		e.pend = append(e.pend, pendCall{loc, e.fid, e.rec.moduleID, c.line, c.text, sc.typeName})
	}
	e.emitHazards(st, loc)
	e.typeExtra(n, loc)
	e.byName = append(e.byName, nameRef{name, loc, e.fid, e.rec.moduleID, sc.typeName})
	e.byQual = append(e.byQual, qualRef{qual, loc, ""})
	return loc
}

func (e *fileCtx) typeExtra(n tsNode, loc int32) {
	body, ok := field(n, fBody)
	if !ok {
		return
	}
	name := e.nodeName(n)
	extends := ""
	found := false
	eachNamedChild(n, func(c tsNode) {
		if !found && symNames[symOf(c)] == "class_heritage" {
			extends = strings.TrimSpace(strings.ReplaceAll(e.text(c), "extends", ""))
			found = true
		}
	})
	var nMethods, nStatic, nGet, nSet, nPriv, nFields, nArrow, nComputed int32
	hasCtor, hasStaticBlock := false, false
	idx := int32(0)
	eachNamedChild(body, func(member tsNode) {
		i := idx
		idx++
		mtxt := clip(e.text(member), 200)
		if symNames[symOf(member)] == "class_static_block" {
			hasStaticBlock = true
			return
		}
		isStatic := false
		forEachChild(member, func(c tsNode) {
			if symNames[symOf(c)] == "static" {
				isStatic = true
			}
		})
		nmNode, hasName := field(member, fName)
		if !hasName {
			nmNode, hasName = field(member, fProperty)
		}
		nm := ""
		if hasName {
			nm = e.text(nmNode)
		}
		if hasName && symNames[symOf(nmNode)] == "computed_property_name" {
			nComputed++
		}
		if strings.HasPrefix(nm, "#") {
			nPriv++
		}
		switch symNames[symOf(member)] {
		case "method_definition":
			nMethods++
			if isStatic {
				nStatic++
			}
			isGet, isSet := false, false
			forEachChild(member, func(c tsNode) {
				switch symNames[symOf(c)] {
				case "get":
					isGet = true
				case "set":
					isSet = true
				}
			})
			if isGet {
				nGet++
			} else if isSet {
				nSet++
			}
			if nm == "constructor" {
				hasCtor = true
			}
		case "field_definition":
			nFields++
			if isStatic {
				nStatic++
			}
			val, hasVal := field(member, fValue)
			isFn := false
			if hasVal {
				vt := symNames[symOf(val)]
				isFn = vt == "arrow_function" || vt == "function_expression"
				if isFn {
					nArrow++
				}
			}
			vis := "public"
			if strings.HasPrefix(nm, "#") {
				vis = "private"
			}
			e.fields = append(e.fields, FieldRow{symID: loc, ordinal: i,
				line: int32(startRow(member)) + 1, name: e.put(clip(nm, 120)), typ: e.put(""),
				vis: e.put(vis), static: isStatic, konst: false, mut: true, nullable: false,
				coll:    strings.Contains(mtxt, "[") || strings.Contains(mtxt, "Map("),
				untyped: true, hasDefault: int32(boolToInt(hasVal)), depth: 0})
		}
	})
	exported := isExported(n) || e.exported[name]
	e.classes = append(e.classes, ClassRow{symID: loc, fileID: e.fid,
		extends: e.put(clip(extends, 200)), nMethods: nMethods, nStatic: nStatic,
		nGetters: nGet, nSetters: nSet, nPrivate: nPriv, nFields: nFields,
		nArrow: nArrow, nComputed: nComputed, hasCtor: int32(boolToInt(hasCtor)),
		hasStaticBlock: int32(boolToInt(hasStaticBlock)), exported: exported,
		component: reComponentName.MatchString(name)})
}

func (e *fileCtx) emitHazards(st *bodyStats, loc int32) {
	type hz struct {
		cat  string
		n    int32
		line int32
	}
	seen := map[string]*hz{}
	var order []string
	for _, c := range st.calls {
		if c.text == "" {
			continue
		}
		pattern, cat, ok := hazardOf(c.text)
		if !ok || pattern == "" {
			continue
		}
		if v, ok2 := seen[pattern]; ok2 {
			v.n++
		} else {
			seen[pattern] = &hz{cat, 1, c.line}
			order = append(order, pattern)
		}
	}
	for _, k := range order {
		v := seen[k]
		e.hazs = append(e.hazs, Hazard{symID: loc, pattern: e.put(clip(k, 120)),
			category: e.put(v.cat), n: v.n, firstLine: v.line})
	}
}

func hazardOf(callee string) (string, string, bool) {
	if cat, ok := hazardCalls[callee]; ok && cat != "" {
		return callee, cat, true
	}
	base := callee
	if i := strings.LastIndex(callee, "."); i >= 0 {
		base = callee[i+1:]
	}
	if cat, ok := hazardCalls[base]; ok && cat != "" {
		if strings.Contains(callee, ".") {
			return "*." + base, cat, true
		}
		return base, cat, true
	}
	if len(base) > 4 && strings.HasSuffix(base, "Sync") {
		return "*." + base, "sync_block", true
	}
	return "", "", false
}

const cKindNumber = "number"
const cKindRegexRedos = "regex_redos"

var (
	childProcessBases = map[string]bool{"exec": true, "execSync": true, "spawnSync": true}
	fsRWBases         = map[string]bool{"readFile": true, "readFileSync": true, "writeFile": true, "writeFileSync": true}
	fsWriteBases      = map[string]bool{"writeFile": true, "writeFileSync": true}
	fsSyncBases       = map[string]bool{"readFileSync": true, "writeFileSync": true, "existsSync": true, "statSync": true}
	arrayGrowBases    = map[string]bool{"push": true, "concat": true, "unshift": true}
	searchBases       = map[string]bool{"indexOf": true, "includes": true, "find": true}
	weakHashBases     = map[string]bool{"createHash": true, "createHmac": true, "createCipher": true}
	sendFileBases     = map[string]bool{"sendFile": true, "sendfile": true, "download": true}
	zipExtractBases   = map[string]bool{"extract": true, "extractAll": true, "extractAllTo": true, "extractFiles": true}
	logLevels         = map[string]bool{"debug": true, "info": true, "warn": true, "warning": true, "error": true, "fatal": true, "trace": true, "log": true}
	authMarkers       = []string{"auth", "login", "jwt", "isauthenticated", "passport", "session"}
	cacheWriteMethods = map[string]bool{"set": true, "add": true, "push": true, "unshift": true, "append": true, "put": true, "store": true, "register": true}
	cacheDropMethods  = map[string]bool{"delete": true, "clear": true, "remove": true, "evict": true, "pop": true, "shift": true, "splice": true, "unregister": true, "reset": true, "prune": true, "purge": true, "invalidate": true}

	reqBases         = map[string]bool{"req": true, "request": true}
	userInputMembers = map[string]string{"query": "query", "body": "body", "headers": "header",
		"cookies": "cookie", "files": "form", "params": "path"}
)

var reSecret = regexp.MustCompile(`(?i)(api[_-]?key|apikey|secret|password|passwd|pwd|token|bearer|access[_-]?key|private[_-]?key|client[_-]?secret|auth[_-]?token|jwt|credential|smtp[_-]?pass|db[_-]?pass|sk_live|rk_live|pk_live|ghp_|xoxb-|AKIA)`)

const secretMinLen = 12

var reRedosNested = regexp.MustCompile(`\((?:\?[:=!]|\?<[=!]|\?<\w+>)?[^()]*?(?:[+*]|\{\d+,\d*\})[^()]*?\)\s*(?:[+*]|\{\d+,\d*\})`)
var reRedosAlt = regexp.MustCompile(`\((?:\?[:=!])?[^()|]*\|[^()|]*\)\s*(?:[+*]|\{\d+,\d*\})`)

func (e *fileCtx) onCall(node tsNode, st *bodyStats, loopDepth, nest int32, t string) {
	isNew := t == "new_expression"
	var fn tsNode
	var ok bool
	if isNew {
		fn, ok = field(node, fConstructor)
	} else {
		fn, ok = field(node, fFunction)
	}
	st.m[cNCALLS]++
	if loopDepth > 0 {
		st.m[cCALLINLOOP]++
		if isNew {
			st.m[cALLOCINLOOP]++
		}
	}
	line := int32(startRow(node)) + 1
	if !ok {
		st.m[cNDYNAMICCALLS]++
		st.calls = append(st.calls, callRec{"", line, true, loopDepth > 0})
		return
	}
	raw := strings.TrimSpace(e.text(fn))
	name := strings.Join(cgSplit(raw), " ")
	base := name
	if i := strings.LastIndex(name, "."); i >= 0 {
		base = name[i+1:]
	}
	lname := strings.ToLower(name)

	if childProcessBases[base] && strings.Contains(name, "child_process") {
		st.m[cNCHILDPROCESS]++
	}
	if base == "fetch" || strings.HasPrefix(name, "axios.") || strings.HasPrefix(name, "got.") ||
		strings.HasPrefix(name, "superagent.") || strings.HasPrefix(name, "node-fetch") ||
		strings.HasPrefix(name, "http.request") || strings.HasPrefix(name, "https.request") {
		st.m[cNFETCH]++
	}
	if fsRWBases[base] && strings.HasPrefix(name, "fs.") {
		args, hasArgs := field(node, fArguments)
		first := namedChildAt(args, 0)
		if hasArgs && hasNode(first) {
			ft := symNames[symOf(first)]
			if ft != "string" && ft != "template_string" {
				st.m[cNDYNAMICOPEN]++
			}
		}
	}
	if fsWriteBases[base] && strings.HasPrefix(name, "fs.") {
		args, hasArgs := field(node, fArguments)
		if hasArgs {
			hit := false
			eachNamedChild(args, func(a tsNode) {
				at := symNames[symOf(a)]
				if at == "member_expression" || at == "identifier" {
					t2 := strings.TrimSpace(e.text(a))
					if strings.HasPrefix(t2, "req.") || strings.HasPrefix(t2, "request.") ||
						strings.HasPrefix(t2, "file") {
						hit = true
					}
				}
			})
			if hit {
				st.m[cNUPLOADSAVE]++
			}
		}
	}
	if strings.Contains(lname, "unzip") ||
		(strings.Contains(lname, "zip") && zipExtractBases[base]) {
		st.m[cNZIPREAD]++
	}
	if base == "assign" && strings.HasPrefix(name, "Object.") {
		st.m[cNMASSASSIGN]++
	}
	if logLevels[base] && strings.Contains(lname, "logger") {
		st.m[cNLOGCALL]++
	}
	if strings.HasPrefix(name, "console.") && logLevels[base] {
		st.m[cNCONSOLELOG]++
	}
	for _, k := range authMarkers {
		if strings.Contains(lname, k) {
			st.m[cNAUTHCALL]++
			break
		}
	}
	if fsSyncBases[base] {
		st.m[cNFSSYNC]++
	}
	if name == "Object.assign" && loopDepth > 0 {
		st.m[cNASSIGNINLOOP]++
	}
	if base == "parse" && strings.HasPrefix(name, "JSON") && loopDepth > 0 {
		st.m[cNJSONPARSEINLOOP]++
	}
	if arrayGrowBases[base] && loopDepth > 0 {
		st.m[cNARRAYGROWINLOOP]++
	}
	if searchBases[base] && loopDepth > 0 {
		st.m[cNSEARCHINLOOP]++
	}
	if name == "Math.random" {
		st.m[cNMATHRANDOM]++
	}
	if weakHashBases[base] {
		args, hasArgs := field(node, fArguments)
		at := ""
		if hasArgs {
			at = strings.ToLower(e.text(args))
		}
		if strings.Contains(at, "md5") || strings.Contains(at, "sha1") ||
			strings.Contains(at, "rc4") || strings.Contains(at, "des") {
			st.m[cNWEAKHASH]++
		}
	}
	if base == "then" && loopDepth > 0 {
		st.m[cNTHENINLOOP]++
	}
	if base == "catch" && loopDepth > 0 {
		st.m[cNCATCHINLOOP]++
	}
	if name == "process.exit" {
		st.m[cNPROCESSEXIT]++
	}
	if name == "Buffer" || strings.HasPrefix(name, "Buffer.") {
		st.m[cNBUFFERCALL]++
	}
	if base == "setPrototypeOf" || base == "__defineGetter__" {
		st.m[cNPROTOMUTATE]++
	}
	if symOf(fn) == symSImport {
		st.m[cNIMPORTDYNAMIC]++
		st.calls = append(st.calls, callRec{"import()", line, true, loopDepth > 0})
		return
	}

	dynamic := name == "" || !(unicode.IsLetter(rune(name[0])) || strings.ContainsRune("_$#", rune(name[0]))) ||
		strings.Contains(name, "(") || strings.Contains(name, "[")
	st.calls = append(st.calls, callRec{clip(name, 200), line, dynamic, loopDepth > 0})
	if dynamic {
		st.m[cNDYNAMICCALLS]++
	}
	if loopDepth > 0 {
		for _, lc := range loopCallCols {
			if lc.needle == base || strings.Contains(name, lc.needle) {
				st.m[lc.col]++
			}
		}
	}

	if len(base) > 4 && strings.HasSuffix(base, "Sync") {
		st.m[cNSYNCCALLS]++
	}
	switch {
	case name == "eval" || name == "Function" || base == "eval":
		st.m[cNEVAL]++
	case name == "JSON.parse" || name == "JSON.stringify" ||
		((base == "parse" || base == "stringify") && strings.HasPrefix(name, "JSON.")):
		st.m[cNJSONPARSE]++
	case base == "require":
		args, hasArgs := field(node, fArguments)
		if hasArgs {
			kid := namedChildAt(args, 0)
			if hasNode(kid) {
				if symNames[symOf(kid)] != "string" {
					st.m[cNREQUIREDYNAMIC]++
				} else if !atModuleScope(node) {

					st.m[cNLAZYREQUIRE]++
				}
			}
		}
	case (base == "all" || base == "allSettled" || base == "any" || base == "race") &&
		strings.HasPrefix(name, "Promise."):
		st.m[cNPROMISEALL]++
	case base == "then":
		st.m[cNTHEN]++
		st.m[cNPROMISECHAIN]++
	case (base == "catch" || base == "finally") && strings.Contains(name, "."):
		st.m[cNCATCHHANDLER]++
		st.m[cNPROMISECHAIN]++
	case cacheWriteMethods[base] && strings.Contains(name, "."):
		st.m[cNCACHEWRITE]++
	case cacheDropMethods[base] && strings.Contains(name, "."):
		st.m[cNCACHEDROP]++
	}
	if reSetState.MatchString(base) || strings.HasSuffix(name, ".setState") {
		st.m[cNSETSTATE]++
	}

	if isNew && base == "RegExp" {
		if ra, hasArgs := field(node, fArguments); hasArgs {
			if r0 := namedChildAt(ra, 0); hasNode(r0) {
				rt := symNames[symOf(r0)]
				if rt != "string" && rt != "template_string" {
					st.m[cNREGEXDYNAMIC]++
				}
			}
		}
	}
	if isNew && base == "Promise" {
		if pa, hasArgs := field(node, fArguments); hasArgs {
			ex := namedChildAt(pa, 0)
			if hasNode(ex) && anonFnNodes[symNames[symOf(ex)]] {
				isAsync := false
				forEachChild(ex, func(c tsNode) {
					if symNames[symOf(c)] == "async" {
						isAsync = true
					}
				})
				if isAsync {
					st.m[cNPROMISEEXECASYNC]++
				}
				if executorReturnsValue(ex) {
					st.m[cNPROMISEEXECRETURN]++
				}
			}
		}
	}
	callArgs, hasCallArgs := field(node, fArguments)
	if hasCallArgs {
		eachNamedChild(callArgs, func(a tsNode) {
			if !anonFnNodes[symNames[symOf(a)]] {
				return
			}
			as := false
			forEachChild(a, func(c tsNode) {
				if symNames[symOf(c)] == "async" {
					as = true
				}
			})
			if as {
				st.m[cNASYNCARG]++
			}
		})
	}
	if sendFileBases[base] && strings.Contains(name, ".") {
		st.m[cNSENDFILE]++
	}
	if (base == "listen" || base == "createServer") && !isNew {
		st.m[cNSERVERSTART]++
	}
	if isNew {
		switch base {
		case "Map", "WeakMap":
			st.m[cNNEWMAP]++
		case "Set", "WeakSet":
			st.m[cNNEWSET]++
		case "WeakRef", "FinalizationRegistry":
			st.m[cNWEAKREF]++
		}
	}

	if p, ok := parent(node); ok {
		switch symOf(p) {
		case symSExpressionStatement:
			st.m[cNFLOATINGPROMISE]++
		case symSArguments:
			st.m[cNCALLBACKS]++
		}
	}
}

func executorReturnsValue(ex tsNode) bool {
	body, ok := field(ex, fBody)
	if !ok {
		body = ex
	}
	found := false
	cur := cursorNew(body)
	defer cur.free()
	for {
		if symOf(cur.node()) == symSReturnStatement {
			eachNamedChild(cur.node(), func(tsNode) { found = true })
			if found {
				return true
			}
		}
		if cur.first() {
			continue
		}
		for !cur.next() {
			if !cur.up() {
				return found
			}
		}
	}
}

func (e *fileCtx) onNode(node tsNode, st *bodyStats, loopDepth, nest int32, t string) {
	switch t {
	case "binary_expression":
		op := ""
		if o, ok := field(node, fOperator); ok {
			op = e.text(o)
		}
		switch op {
		case "&&", "||":
			st.m[cNLOGICAL]++
			st.cyclomatic++
		case "??":
			st.m[cNNULLISH]++
			st.m[cNNULLCHECK]++
			st.cyclomatic++
		case "==", "!=", "===", "!==", "<", ">", "<=", ">=":
			st.m[cNCMP]++
			if op == "==" || op == "!=" || op == "===" || op == "!==" {
				if e.hasNullishOperand(node) {
					st.m[cNNULLCHECK]++
				}
			}
		case "&", "|", "^":
			st.m[cNBITOP]++
		case "<<", ">>", ">>>":
			st.m[cNSHIFT]++
		case "+", "-", "*", "/", "%", "**":
			st.m[cNARITH]++
			if op == "+" && loopDepth > 0 && e.looksStringy(node) {
				st.m[cCONCATINLOOP]++
			}
		}
	case "member_expression":
		obj, ok1 := field(node, fObject)
		prop, ok2 := field(node, fProperty)
		if !ok1 || !ok2 {
			return
		}
		base := e.text(obj)
		if base == "process.env" {
			st.m[cNENVREAD]++
		}
		kind, isUI := userInputMembers[e.text(prop)]
		if !reqBases[base] || !isUI {
			return
		}
		varname := clip(e.text(node), 120)
		if par, ok3 := parent(node); ok3 && symOf(par) == symSMemberExpression {
			varname = clip(e.text(par), 120)
		}
		st.inputSites = append(st.inputSites, inputRec{varname, kind, int32(startRow(node)) + 1, loopDepth > 0})
	case "assignment_expression":
		left, ok := field(node, fLeft)
		if ok && symNames[symOf(left)] == "member_expression" {
			o, ok1 := field(left, fObject)
			p, ok2 := field(left, fProperty)
			if ok1 && ok2 {
				ot, pt := e.text(o), e.text(p)
				if (ot == "location" && pt == "href") || (ot == "window" && pt == "location") {
					st.m[cNREDIRECT]++
				}
			}
		}
	case "unary_expression":
		op := ""
		if o, ok := field(node, fOperator); ok {
			op = e.text(o)
		}
		if op == "delete" {
			st.m[cNDELETE]++
			if arg, ok2 := field(node, fArgument); ok2 && symNames[symOf(arg)] == "subscript_expression" {
				st.m[cNDYNAMICPROP]++
			}
		} else if op == "typeof" {
			st.m[cNNULLCHECK]++
		}
	case "arrow_function", "function_expression", "generator_function":
		st.m[cNCLOSURES]++
		if loopDepth > 0 {
			st.m[cALLOCINLOOP]++
			st.m[cNCLOSURECAPTURE]++
		}
		if t == "arrow_function" {
			as := false
			forEachChild(node, func(c tsNode) {
				if symNames[symOf(c)] == "async" {
					as = true
				}
			})
			if as {
				st.m[cNASYNCARROW]++
			}
		}
	case "await_expression":
		if loopDepth > 0 {
			st.m[cAWAITINLOOP]++
		}
	case "augmented_assignment_expression":
		e.assignmentShape(node, st)
	case "if_statement":
		cond, ok1 := field(node, fCondition)
		alt, ok2 := field(node, fAlternative)
		if !ok1 || !ok2 {
			return
		}
		var c2 tsNode
		if symNames[symOf(alt)] == "if_statement" {
			c2, _ = field(alt, fCondition)
		} else if symNames[symOf(alt)] == "else_clause" {
			inner := namedChildAt(alt, 0)
			if hasNode(inner) && symNames[symOf(inner)] == "if_statement" {
				c2, _ = field(inner, fCondition)
			}
		}
		if hasNode(c2) && e.text(cond) == e.text(c2) {
			st.m[cNDUPCOND]++
		}
	case "object", "array":
		if loopDepth > 0 {
			st.m[cALLOCINLOOP]++
		}
	case "template_string":
		if loopDepth > 0 {
			st.m[cCONCATINLOOP]++
		}
	case "regex":
		if pat, ok := field(node, fPattern); ok {
			text := e.text(pat)
			if reRedosNested.MatchString(text) || reRedosAlt.MatchString(text) {
				st.m[cNREGEXREDOS]++
			}
		}
		if loopDepth > 0 {
			st.m[cREGEXINLOOP]++
		}
	case "identifier":
		if e.text(node) == "arguments" {
			st.m[cNARGUMENTS]++
		}
	case "return_statement":
		if nest > 0 {
			st.m[cNEARLYRETURNS]++
		}
	case "catch_clause":
		body, ok := field(node, fBody)
		if ok && !hasNamedChild(body) {
			st.m[cNCATCHEMPTY]++
		}
		btxt := ""
		if ok {
			btxt = e.text(body)
		}
		if !strings.Contains(btxt, "throw") {
			st.m[cNCATCHBROAD]++
		}
	case "jsx_attribute":
		first := namedChildAt(node, 0)
		if hasNode(first) && e.text(first) == "dangerouslySetInnerHTML" {
			st.m[cNINNERHTML]++
		}
	}
}

func (e *fileCtx) assignmentShape(node tsNode, st *bodyStats) {
	left, ok := field(node, fLeft)
	if !ok {
		return
	}
	ltxt := e.text(left)
	if symNames[symOf(left)] == "subscript_expression" {
		idx, has := field(left, fIndex)
		if has {
			it := symNames[symOf(idx)]
			if it != "string" && it != "number" {
				st.m[cNDYNAMICPROP]++
			}
		}
		if obj, has2 := field(left, fObject); has2 {
			ot := symNames[symOf(obj)]
			if ot == "subscript_expression" || ot == "member_expression" {

				st.m[cNPROTOWRITE]++
			}
		}
	}
	if strings.Contains(ltxt, "__proto__") || strings.HasSuffix(ltxt, ".constructor") ||
		strings.Contains(ltxt, ".prototype") {
		st.m[cNPROTOWRITE]++
	}
	if symNames[symOf(left)] == "member_expression" {
		p := ""
		if pn, has := field(left, fProperty); has {
			p = e.text(pn)
		}
		if p == "innerHTML" || p == "outerHTML" || p == "srcdoc" {
			st.m[cNINNERHTML]++
		}
	}
}

func (e *fileCtx) hasNullishOperand(node tsNode) bool {
	for _, f1 := range []tsFieldID{fLeft, fRight} {
		if c, ok := field(node, f1); ok {
			t := strings.TrimSpace(e.text(c))
			if t == "null" || t == "undefined" {
				return true
			}
		}
	}
	return false
}

func (e *fileCtx) looksStringy(node tsNode) bool {
	for _, f1 := range []tsFieldID{fLeft, fRight} {
		if c, ok := field(node, f1); ok {
			t := symNames[symOf(c)]
			if t == "string" || t == "template_string" {
				return true
			}
		}
	}
	return false
}

func (e *fileCtx) onString(node tsNode, text string, st *bodyStats, loopDepth int32) {
	if symNames[symOf(node)] == "template_string" {
		return
	}
	val := strings.Trim(text, "\"'")
	if len(val) >= secretMinLen && !strings.Contains(val, " ") && reSecret.MatchString(val) {
		st.secrets = append(st.secrets, secretRec{clip(val, 200), int32(startRow(node)) + 1})
	}
	low := strings.ToLower(clip(text, 200))
	if strings.Contains(low, "<script") || strings.Contains(low, "<div") ||
		strings.Contains(low, "<span") || strings.Contains(low, "</") {
		if len(text) > 24 {
			st.m[cNINNERHTML]++
		}
	}
}

func specIsExternal(spec string) bool {
	return spec != "" && !strings.HasPrefix(spec, ".")
}

func (e *fileCtx) parseImports(root tsNode) {
	src := e.rec.rel
	here := dirOf(src)
	cur := cursorNew(root)
	defer cur.free()
	for {
		n := cur.node()
		switch symOf(n) {
		case symSImportStatement:
			e.importStmt(n, here)
		case symSExportStatement:
			e.exportStmt(n, here)
		case symSCallExpr:
			fn, ok := field(n, fFunction)
			if !ok {
				break
			}
			ftxt := e.text(fn)
			if symOf(fn) != symSImport && ftxt != "require" {
				break
			}
			args, hasArgs := field(n, fArguments)
			kid := namedChildAt(args, 0)
			dynamic := true
			if hasArgs && hasNode(kid) && symNames[symOf(kid)] == "string" {
				dynamic = false
			}
			spec := ""
			if !dynamic {
				spec = stringValue(kid, e.src)
			}
			external := specIsExternal(spec)
			kind := "require"
			if symOf(fn) == symSImport {
				kind = "dynamic-import"
			}
			target := spec
			if target == "" {
				target = "(computed)"
			}
			e.imps = append(e.imps, Import{id: 0, fileID: e.fid, targetID: 0,
				line: int32(startRow(n)) + 1, isExternal: int32(boolToInt(external)),
				isRel:     int32(boolToInt(strings.HasPrefix(spec, "."))),
				isDynamic: 1, target: e.put(clip(target, 300)), aliasNull: true, kind: e.put(kind)})
			if !dynamic {

				for _, b := range requireBindings(n, e.src) {
					e.bindings[b.local] = binding{spec, b.imported, external}
					e.impNames = append(e.impNames, ImportName{id: 0, fileID: e.fid,
						sourceID: 0, line: int32(startRow(n)) + 1,
						source: e.put(clip(spec, 300)), name: e.put(clip(b.imported, 120)),
						alias: e.put(clip(b.local, 120)), ns: b.imported == "*",
						external: external})
				}
			}
		case symSAssignmentExpression:
			left, ok := field(n, fLeft)
			if !ok || symNames[symOf(left)] != "member_expression" {
				break
			}
			ltxt := e.text(left)
			if ltxt == "module.exports" {
				e.cjsExports(n)
			} else if strings.HasPrefix(ltxt, "exports.") {
				name := strings.SplitN(ltxt, ".", 2)[1]
				e.exported[name] = true
				e.exports = append(e.exports, ExportRow{0, e.fid, 0, 0,
					int32(startRow(n)) + 1, e.put(clip(name, 120)), e.put(clip(name, 120)), e.put("cjs"), e.put(""), false, false, true})
			}
		case symSVariableDeclarator:
			e.cacheCandidate(n)
		}
		if cur.first() {
			continue
		}
		for !cur.next() {
			if !cur.up() {
				return
			}
		}
	}
}

func (e *fileCtx) importStmt(n tsNode, here string) {
	spec := ""
	if srcn, ok := field(n, fSource); ok {
		spec = stringValue(srcn, e.src)
	}
	external := specIsExternal(spec)
	line := int32(startRow(n)) + 1
	type impName struct {
		name, alias string
		ns, def     int32
	}
	var names []impName
	wildcard := int32(0)

	cur := cursorNew(n)
	defer cur.free()
	for {
		switch symOf(cur.node()) {
		case symSImportSpecifier:
			nm, ok1 := field(cur.node(), fName)
			al, ok2 := field(cur.node(), fAlias)
			var a, b string
			if ok1 {
				a = e.text(nm)
			}
			if ok2 {
				b = e.text(al)
			}
			names = append(names, impName{a, b, 0, 0})
		case symSNamespaceImport:

			alias := ""
			eachNamedChild(cur.node(), func(k tsNode) {
				if alias == "" && symNames[symOf(k)] == "identifier" {
					alias = e.text(k)
				}
			})
			names = append(names, impName{"*", alias, 1, 0})
			wildcard = 1
		case symSImportClause:
			eachNamedChild(cur.node(), func(k tsNode) {
				if symNames[symOf(k)] == "identifier" {
					names = append(names, impName{"default", e.text(k), 0, 1})
				}
			})
		}
		if cur.first() {
			continue
		}
		for !cur.next() {
			if !cur.up() {
				goto done
			}
		}
	}
done:
	typeOnly := int32(0)
	forEachChild(n, func(c tsNode) {
		if symNames[symOf(c)] == "import_attribute" && strings.Contains(e.text(c), "type") {
			typeOnly = 1
		}
	})
	e.imps = append(e.imps, Import{id: 0, fileID: e.fid, targetID: 0, line: line,
		isExternal: int32(boolToInt(external)),
		isRel:      int32(boolToInt(strings.HasPrefix(spec, "."))),
		isWild:     wildcard, isTypeOnly: typeOnly, nNames: int32(len(names)),
		target: e.put(clip(spec, 300)), aliasNull: true, kind: e.put("import")})
	for _, nm := range names {
		local := nm.alias
		if local == "" {
			local = nm.name
		}
		if local != "" {
			e.bindings[local] = binding{spec, nm.name, external}
		}
		e.impNames = append(e.impNames, ImportName{0, e.fid, 0, line, e.put(clip(spec, 300)),
			e.put(clip(nm.name, 120)), e.put(clip(nm.alias, 120)), nm.ns != 0, nm.def != 0, external})
	}
}

func (e *fileCtx) exportStmt(n tsNode, here string) {
	line := int32(startRow(n)) + 1
	spec := ""
	if srcn, ok := field(n, fSource); ok {
		spec = stringValue(srcn, e.src)
	}

	var sidSrc int32
	reexport := spec != ""
	var clause, ns []tsNode
	eachNamedChild(n, func(c tsNode) {
		switch symNames[symOf(c)] {
		case "export_clause":
			clause = append(clause, c)
		case "namespace_export":
			ns = append(ns, c)
		}
	})
	decl, hasDecl := field(n, fDeclaration)
	val, hasVal := field(n, fValue)

	switch {
	case len(clause) > 0:
		eachNamedChild(clause[0], func(specNode tsNode) {
			nm, ok1 := field(specNode, fName)
			al, ok2 := field(specNode, fAlias)
			local := ""
			if ok1 {
				local = e.text(nm)
			}
			public := local
			if ok2 {
				public = e.text(al)
			}
			e.exported[local] = true
			e.exported[public] = true
			kind := "named"
			if reexport {
				kind = "reexport"
			}
			e.exports = append(e.exports, ExportRow{0, e.fid, 0, sidSrc, line,
				e.put(clip(public, 120)), e.put(clip(local, 120)), e.put(kind), e.put(clip(spec, 300)), reexport, false, false})
		})
	case len(ns) > 0:
		name := strings.TrimSpace(e.text(ns[0]))
		e.exports = append(e.exports, ExportRow{0, e.fid, 0, sidSrc, line,
			e.put(clip(name, 120)), e.put("*"), e.put("star-as"), e.put(clip(spec, 300)), true, true, false})
	case spec != "" && !hasDecl && !hasVal:
		e.exports = append(e.exports, ExportRow{0, e.fid, 0, sidSrc, line,
			e.put("*"), e.put("*"), e.put("star"), e.put(clip(spec, 300)), true, true, false})
	case hasDecl:
		for _, name := range e.declaredNames(decl) {
			e.exported[name] = true
			e.exports = append(e.exports, ExportRow{0, e.fid, 0, 0, line,
				e.put(clip(name, 120)), e.put(clip(name, 120)), e.put("named"), e.put(""), false, false, false})
		}
	case hasVal:
		local := bindingNameOfValue(val, e.src)
		if local == "" {
			local = "default"
		}
		e.exported[local] = true
		e.exports = append(e.exports, ExportRow{0, e.fid, 0, 0, line,
			e.put("default"), e.put(clip(local, 120)), e.put("default"), e.put(""), false, false, false})
	}
}

func (e *fileCtx) cjsExports(n tsNode) {
	line := int32(startRow(n)) + 1
	right, has := field(n, fRight)
	if has && symNames[symOf(right)] == "object" {
		eachNamedChild(right, func(kid tsNode) {
			nm := ""
			switch symNames[symOf(kid)] {
			case "pair":
				if k, ok := field(kid, fKey); ok {
					nm = e.text(k)
				}
			case "shorthand_property_identifier":
				nm = e.text(kid)
			}
			if nm != "" {
				e.exported[nm] = true
				e.exports = append(e.exports, ExportRow{0, e.fid, 0, 0, line,
					e.put(clip(nm, 120)), e.put(clip(nm, 120)), e.put("cjs"), e.put(""), false, false, true})
			}
		})
		return
	}
	local := ""
	if has {
		local = bindingNameOfValue(right, e.src)
	}
	if local == "" {
		local = "default"
	}
	e.exported[local] = true
	e.exports = append(e.exports, ExportRow{0, e.fid, 0, 0, line,
		e.put("default"), e.put(clip(local, 120)), e.put("cjs"), e.put(""), false, false, true})
}

func walkAll(root tsNode, fn func(tsNode)) {
	cur := cursorNew(root)
	defer cur.free()
	for {
		fn(cur.node())
		if cur.first() {
			continue
		}
		for !cur.next() {
			if !cur.up() {
				return
			}
		}
	}
}

func (e *fileCtx) declaredNames(decl tsNode) []string {
	if nm, ok := field(decl, fName); ok {
		return []string{strings.TrimSpace(e.text(nm))}
	}
	var out []string
	eachNamedChild(decl, func(d tsNode) {
		if symNames[symOf(d)] != "variable_declarator" {
			return
		}
		n, ok := field(d, fName)
		if !ok {
			return
		}
		if symNames[symOf(n)] == "identifier" {
			out = append(out, strings.TrimSpace(e.text(n)))
			return
		}

		walkAll(n, func(c tsNode) {
			t := symNames[symOf(c)]
			if t == "shorthand_property_identifier_pattern" || t == "identifier" {
				out = append(out, strings.TrimSpace(e.text(c)))
			}
		})
	})
	return out
}

func stringValue(n tsNode, src []byte) string {
	if !hasNode(n) || symNames[symOf(n)] != "string" {
		return ""
	}
	out := ""
	eachNamedChild(n, func(c tsNode) {
		if out == "" && symNames[symOf(c)] == "string_fragment" {
			out = string(src[startByte(c):endByte(c)])
		}
	})
	return out
}

type reqBinding struct{ local, imported string }

func requireBindings(call tsNode, src []byte) []reqBinding {
	decl, ok := parent(call)
	if !ok || symNames[symOf(decl)] != "variable_declarator" {
		return nil
	}
	nm, ok := field(decl, fName)
	if !ok {
		return nil
	}
	txt := func(n tsNode) string { return strings.TrimSpace(string(src[startByte(n):endByte(n)])) }
	if symNames[symOf(nm)] == "identifier" {
		return []reqBinding{{txt(nm), "*"}}
	}
	var out []reqBinding
	if symNames[symOf(nm)] == "object_pattern" {
		eachNamedChild(nm, func(kid tsNode) {
			switch symNames[symOf(kid)] {
			case "shorthand_property_identifier_pattern":
				n := txt(kid)
				out = append(out, reqBinding{n, n})
			case "pair_pattern":
				k, ok1 := field(kid, fKey)
				v, ok2 := field(kid, fValue)
				if ok1 && ok2 && symNames[symOf(v)] == "identifier" {
					out = append(out, reqBinding{txt(v), txt(k)})
				}
			}
		})
	}
	return out
}

func bindingNameOfValue(n tsNode, src []byte) string {
	if !hasNode(n) {
		return ""
	}
	t := symNames[symOf(n)]
	if t == "identifier" || t == "property_identifier" {
		return strings.TrimSpace(string(src[startByte(n):endByte(n)]))
	}
	if nm, ok := field(n, fName); ok {
		return strings.TrimSpace(string(src[startByte(nm):endByte(nm)]))
	}
	return ""
}

func (e *fileCtx) cacheCandidate(n tsNode) {
	if !atModuleScope(n) {
		return
	}
	nm, ok := field(n, fName)
	if !ok || symNames[symOf(nm)] != "identifier" {
		return
	}
	val, ok2 := field(n, fValue)
	if !ok2 {
		return
	}
	ctor := ""
	switch symNames[symOf(val)] {
	case "new_expression":
		c, has := field(val, fConstructor)
		ctext := ""
		if has {
			ctext = e.text(c)
			if i := strings.LastIndex(ctext, "."); i >= 0 {
				ctext = ctext[i+1:]
			}
		}
		ctor = cacheCtors[ctext]
		if ctor == "" {
			for _, suf := range []string{"Cache", "Registry", "Store", "Pool", "Emitter"} {
				if strings.HasSuffix(ctext, suf) {
					ctor = ctext
					break
				}
			}
		}
	case "object":
		ctor = "object"
	case "array":
		ctor = "array"
	case "call_expression":
		c, has := field(val, fFunction)
		ctext := ""
		if has {
			ctext = e.text(c)
		}
		if ctext == "Object.create" || ctext == "new Map" {
			ctor = "object"
		}
	}
	if ctor == "" {
		return
	}
	decl, hasDecl := parent(n)
	konst := hasDecl && len(e.text(decl)) >= 5 && e.text(decl)[:5] == "const"
	cand := mcCand{int32(startRow(n)) + 1, ctor, weakCtors[ctor], isExported(n), konst}
	key := e.text(nm)
	if _, exists := e.mcCands[key]; !exists {
		e.mcOrder = append(e.mcOrder, key)
	}
	e.mcCands[key] = cand
}

func (e *fileCtx) cacheTouch(n tsNode, write bool) {
	obj, ok := field(n, fObject)
	if !ok || symNames[symOf(obj)] != "identifier" {
		return
	}
	name := e.text(obj)
	slot, ok := e.mcUse[name]
	if !ok {
		return
	}
	ptxt := ""
	if p, has := field(n, fProperty); has {
		ptxt = e.text(p)
	}
	if ptxt == "size" || ptxt == "length" {
		slot[3]++
	} else if write {
		slot[0]++
	} else {
		slot[2]++
	}
}

func (e *fileCtx) owner(off int32) int32 {
	i := sort.Search(len(e.spanStarts), func(k int) bool { return e.spanStarts[k] > off })
	for i--; i >= 0; i-- {
		if off < e.spans[i].end {
			return e.spans[i].sid
		}
	}
	return -1
}

func (e *fileCtx) parseFileExtra(root tsNode) {
	sort.SliceStable(e.spans, func(i, j int) bool {
		if e.spans[i].start != e.spans[j].start {
			return e.spans[i].start < e.spans[j].start
		}
		if e.spans[i].end != e.spans[j].end {
			return e.spans[i].end < e.spans[j].end
		}
		return e.spans[i].sid < e.spans[j].sid
	})
	e.spanStarts = e.spanStarts[:0]
	for _, s := range e.spans {
		e.spanStarts = append(e.spanStarts, s.start)
	}
	for _, k := range e.mcOrder {
		e.mcUse[k] = &[4]int32{}
		e.mcWriters[k] = map[int32]bool{}
	}
	var handlerSpans []int32
	anyCache := len(e.mcOrder) > 0

	cur := cursorNew(root)
	defer cur.free()
	depth := 0
	type frame struct {
		depth        int
		loops, conds []int
	}
	var scopes []frame
	var loops, conds []int
	for {
		n := cur.node()
		for len(scopes) > 0 && depth <= scopes[len(scopes)-1].depth {
			loops, conds = scopes[len(scopes)-1].loops, scopes[len(scopes)-1].conds
			scopes = scopes[:len(scopes)-1]
		}
		for len(loops) > 0 && loops[len(loops)-1] >= depth {
			loops = loops[:len(loops)-1]
		}
		for len(conds) > 0 && conds[len(conds)-1] >= depth {
			conds = conds[:len(conds)-1]
		}
		inLoop, inCond := len(loops) > 0, len(conds) > 0
		s := symOf(n)
		t := symNames[s]
		switch s {
		case symSCallExpr, symSNewExpr:
			e.callRow(n, anyCache, handlerSpans, inLoop, inCond)
		case symSMemberExpression, symSSubscriptExpression:
			if anyCache {
				e.cacheTouch(n, false)
			}
		case symSJSXOpening, symSJSXSelfClosing:
			e.jsxRow(n, inLoop)
		case symSRegex:

			ptxt := ""
			if pat, ok := field(n, fPattern); ok {
				ptxt = e.text(pat)
			}
			if ptxt != "" && (reRedosNested.MatchString(ptxt) || reRedosAlt.MatchString(ptxt)) {
				e.lits = append(e.lits, Literal{id: 0,
					symID: e.owner(int32(startByte(n))), fileID: e.fid,
					line: int32(startRow(n)) + 1, kind: e.put(cKindRegexRedos),
					value: e.put(clip(ptxt, 200)), isMagic: true})
			}
		case symSAssignmentExpression:
			if left, ok := field(n, fLeft); ok && anyCache {
				e.cacheTouch(left, true)
			}
		}
		_ = t
		if cur.first() {
			if fnNodeTypes[t] {
				scopes = append(scopes, frame{depth, append([]int(nil), loops...), append([]int(nil), conds...)})
				loops, conds = nil, nil
			}
			if loopNodeTypes[t] {
				loops = append(loops, depth)
			} else if condNodeTypes[t] {
				conds = append(conds, depth)
			}
			depth++
			continue
		}
		for !cur.next() {
			if !cur.up() {
				goto done
			}
			depth--
		}
	}
done:
	for _, key := range e.mcOrder {
		c := e.mcCands[key]
		slot := e.mcUse[key]
		w, dr, r, sz := slot[0], slot[1], slot[2], slot[3]
		if w == 0 && dr == 0 {
			continue
		}

		var ws []int32
		for k := range e.mcWriters[key] {
			ws = append(ws, k)
		}
		slices.Sort(ws)
		e.caches = append(e.caches, ModuleCache{id: 0, fileID: e.fid, line: c.line,
			name: e.put(clip(key, 120)), ctor: e.put(clip(c.ctor, 60)), weak: c.weak,
			exported: c.exported, konst: c.konst, nWrites: w, nDrops: dr,
			nReads: r, nSize: sz, hasMax: sz > 0})
		e.cacheWriters = append(e.cacheWriters, ws)
	}
	e.handlerSpans = append(e.handlerSpans, handlerSpans...)
}

func (e *fileCtx) callRow(n tsNode, anyCache bool, handlerSpans []int32, inLoop, inCond bool) {
	line := int32(startRow(n)) + 1
	isNew := symOf(n) == symSNewExpr
	var fn tsNode
	var ok bool
	if isNew {
		fn, ok = field(n, fConstructor)
	} else {
		fn, ok = field(n, fFunction)
	}
	if !ok {
		return
	}
	raw := strings.Join(cgSplit(e.text(fn)), " ")
	base := raw
	if i := strings.LastIndex(raw, "."); i >= 0 {
		base = raw[i+1:]
	}
	base = strings.ReplaceAll(base, "?.", "")
	target := ""
	if strings.Contains(raw, ".") {
		target = raw[:len(raw)-(len(base)+1)]
	}
	var kids []tsNode
	if args, has := field(n, fArguments); has {
		eachNamedChild(args, func(c tsNode) { kids = append(kids, c) })
	}
	sid := e.owner(int32(startByte(n)))
	moduleScope := sid < 0
	argText := func(i int) string {
		if i >= len(kids) {
			return ""
		}
		return strings.Join(cgSplit(e.text(kids[i])), " ")
	}
	firstType := func(i int) string {
		if i >= len(kids) {
			return ""
		}
		return symNames[symOf(kids[i])]
	}
	isAnon := func(i int) bool {
		return i < len(kids) && anonFnNodes[symNames[symOf(kids[i])]]
	}
	argAsync := func(i int) bool {
		if i >= len(kids) {
			return false
		}
		a := false
		forEachChild(kids[i], func(c tsNode) {
			if symNames[symOf(c)] == "async" {
				a = true
			}
		})
		return a
	}

	if isNew && observerCtors[base] {
		e.listeners = append(e.listeners, Listener{0, e.fid, sid, line, e.put("add"), e.put(base),
			e.put("observer"), e.put(clip(target, 120)), e.put(""), e.put(clip(argText(0), 120)), isAnon(0), false,
			moduleScope, inLoop, false})
		return
	}
	fam, isAdd := listenerAdd[base]
	if isAdd && !isNew {
		ev := ""
		if len(kids) > 0 {
			ev = stringValue(kids[0], e.src)
		}
		if (base == "on" || base == "once" || base == "off") && ev == "" && len(kids) < 2 {
			return
		}
		e.listeners = append(e.listeners, Listener{0, e.fid, sid, line, e.put("add"), e.put(base), e.put(fam),
			e.put(clip(target, 120)), e.put(clip(ev, 120)), e.put(clip(argText(1), 120)), isAnon(1),
			len(kids) > 2 && strings.Contains(argText(2), "signal"),
			moduleScope, inLoop, false})
		return
	}
	rfam, isRem := listenerRemove[base]
	if isRem && !isNew {
		ev := ""
		if len(kids) > 0 {
			ev = stringValue(kids[0], e.src)
		}
		e.listeners = append(e.listeners, Listener{0, e.fid, sid, line, e.put("remove"), e.put(base), e.put(rfam),
			e.put(clip(target, 120)), e.put(clip(ev, 120)), e.put(clip(argText(1), 120)), false, false,
			moduleScope, inLoop, e.inCleanupPosition(n)})
		return
	}
	if skind, ok := timerSet[base]; ok && !isNew {
		handle := e.bindingName(n)
		unrefd := false
		if p, has := parent(n); has {
			unrefd = strings.Contains(clip(e.text(p), 200), ".unref()")
		}
		e.timers = append(e.timers, Timer{0, e.fid, sid, line, e.put("set"), e.put(base), e.put(skind),
			e.put(clip(handle, 120)), handle != "", timerRepeating[skind], unrefd,
			firstType(0) == "string", moduleScope, inLoop, isAnon(0) && argAsync(0)})
		return
	}
	if ckind, ok := timerClear[base]; ok && !isNew {

		e.timers = append(e.timers, Timer{0, e.fid, sid, line, e.put("clear"), e.put(base), e.put(ckind),
			e.put(clip(argText(0), 120)), false, false, false, false, moduleScope, inLoop, false})
		return
	}
	if reHookName.MatchString(base) && !isNew {
		e.hookRow(base, kids, sid, line, inLoop, inCond)
		return
	}
	if routeMethods[base] && target != "" && reRouteObjects.MatchString(target) {
		first := ""
		if len(kids) > 0 {
			first = stringValue(kids[0], e.src)
		}
		if strings.HasPrefix(first, "/") || base == "use" {
			var fns []int
			for i, k := range kids {
				t := symNames[symOf(k)]
				if anonFnNodes[t] || t == "identifier" {
					fns = append(fns, i)
				}
			}
			term := -1
			if len(fns) > 0 {
				term = fns[len(fns)-1]
			}
			handler := ""
			inline, hasAsync := false, false
			if term >= 0 {
				handler = clip(strings.TrimSpace(e.text(kids[term])), 120)
				inline = anonFnNodes[symNames[symOf(kids[term])]]
				hasAsync = inline && argAsync(term)
			}
			e.routes = append(e.routes, Route{id: 0, fileID: e.fid, symID: sid,
				line: line, method: e.put(clip(base, 20)), path: e.put(clip(first, 120)),
				handler: e.put(handler), inline: inline, async: hasAsync,
				nMw: int32(maxI(len(fns)-1, 0))})
			for i, k := range kids {
				if i == 0 {
					continue
				}
				t := symNames[symOf(k)]
				if anonFnNodes[t] {
					handlerSpans = append(handlerSpans, int32(startByte(k)))
				} else if t == "identifier" {
					e.handlerNames = append(e.handlerNames, e.text(k))
				}
			}
		}
	}
	if anyCache && !isNew {
		if cacheWriteMethods[base] {
			if slot, ok := e.mcUse[target]; ok {
				slot[0]++
				e.mcWriters[target][e.owner(int32(startByte(n)))] = true
			}
		} else if cacheDropMethods[base] {
			if slot, ok := e.mcUse[target]; ok {
				slot[1]++
			}
		}
	}
}

func itoa32(v int32) string {
	const digits = "0123456789"
	if v == 0 {
		return "0"
	}
	neg := v < 0
	if neg {
		v = -v
	}
	var b [12]byte
	i := len(b)
	for v > 0 {
		i--
		b[i] = digits[v%10]
		v /= 10
	}
	if neg {
		i--
		b[i] = '-'
	}
	return string(b[i:])
}

func (e *fileCtx) inCleanupPosition(n tsNode) bool {
	cur := n
	for range 8 {
		p, ok := parent(cur)
		if !ok {
			return false
		}
		if anonFnNodes[symNames[symOf(p)]] {
			if gp, ok2 := parent(p); ok2 && symOf(gp) == symSReturnStatement {
				return true
			}
		}
		cur = p
	}
	return false
}

func (e *fileCtx) hookRow(base string, kids []tsNode, sid int32, line int32, inLoop, inCond bool) {
	nDeps := int32(-1)
	hasDeps := false
	if depArrayHooks[base] && len(kids) > 1 && symNames[symOf(kids[1])] == "array" {
		hasDeps = true
		nDeps = int32(countNamedChildren(kids[1]))
	}
	cbtxt := ""
	if len(kids) > 0 {
		cbtxt = e.text(kids[0])
	}
	cleanup := len(kids) > 0 && anonFnNodes[symNames[symOf(kids[0])]] &&
		reHookCleanup.MatchString(cbtxt)
	e.hooks = append(e.hooks, HookRow{id: 0, fileID: e.fid, symID: sid, line: line,
		name: e.put(clip(base, 120)), builtin: builtinHooks[base], hasDeps: hasDeps,
		nDeps: nDeps, cleanup: cleanup, inLoop: inLoop, inCond: inCond,
		regListener: strings.Contains(cbtxt, "addEventListener") ||
			strings.Contains(cbtxt, ".on(") || strings.Contains(cbtxt, "subscribe"),
		regTimer: strings.Contains(cbtxt, "setInterval") ||
			strings.Contains(cbtxt, "setTimeout") ||
			strings.Contains(cbtxt, "requestAnimationFrame")})
}

func (e *fileCtx) jsxRow(n tsNode, inLoop bool) {
	tag := "<>"
	if nm, ok := field(n, fName); ok {
		tag = e.text(nm)
	}
	var attrs []tsNode
	eachNamedChild(n, func(c tsNode) {
		t := symNames[symOf(c)]
		if t == "jsx_attribute" || t == "jsx_expression" {
			attrs = append(attrs, c)
		}
	})
	nSpread := 0
	inlineObj, inlineFn, hasKey, dangerous := 0, 0, 0, 0
	for _, a := range attrs {
		if symNames[symOf(a)] == "jsx_expression" {
			nSpread++
			continue
		}
		kids := e.namedChildren(a)
		aname := ""
		if len(kids) > 0 {
			aname = e.text(kids[0])
		}
		if aname == "key" {
			hasKey = 1
		} else if aname == "dangerouslySetInnerHTML" {
			dangerous = 1
		}
		if len(kids) > 1 && symNames[symOf(kids[1])] == "jsx_expression" {
			inner := e.namedChildren(kids[1])
			if len(inner) > 0 {
				t := symNames[symOf(inner[0])]
				if t == "object" || t == "array" {
					inlineObj++
				} else if anonFnNodes[t] {
					inlineFn++
				}
			}
		}
	}
	isComp := tag != "" && (unicodeIsUpper(tag[0]) || strings.Contains(tag, "."))
	e.jsx = append(e.jsx, JSXComp{id: 0, fileID: e.fid,
		symID: e.owner(int32(startByte(n))), line: int32(startRow(n)) + 1,
		tag: e.put(clip(tag, 120)), component: isComp, nAttrs: int32(len(attrs)),
		nSpread: int32(nSpread), hasKey: hasKey == 1, inlineObj: int32(inlineObj),
		inlineFn: int32(inlineFn), danger: dangerous == 1, inLoop: inLoop})
}

func unicodeIsUpper(b byte) bool { return b >= 'A' && b <= 'Z' }

var reMarker = regexp.MustCompile(`(?i)\b(TODO|FIXME|XXX|HACK|BUG|NOTE|WARNING|OPTIMIZE|REVIEW|DEPRECATED|SAFETY|PANIC|UNSAFE)\b[ \t]*[:\-(\xa0]`)

func (e *fileCtx) scanMarkers() {
	lineNo := int32(0)
	cgLines(e.rec.text, func(line string) {
		lineNo++

		if !(strings.Contains(line, "//") || strings.Contains(line, "#") ||
			strings.Contains(line, "*") || strings.Contains(line, "--")) {
			return
		}
		m := reMarker.FindStringSubmatchIndex(line)
		if m == nil {
			return
		}
		kind := strings.ToUpper(line[m[2]:m[3]])
		e.marks = append(e.marks, Marker{id: 0, fileID: e.fid, symID: 0,
			kind: e.put(kind), line: lineNo, text: e.put(clip(strings.TrimSpace(line), 200))})
	})
}

func (g *Graph) setMeta(k, format string, args ...any) {
	v := sprintf(format, args...)
	for i := range g.Meta {
		if g.s(g.Meta[i][0]) == k {
			g.Meta[i][1] = g.put(v)
			return
		}
	}
	g.Meta = append(g.Meta, metaRow{g.put(k), g.put(v)})
}

func (g *Graph) setMetaRaw(k, v string) {
	for i := range g.Meta {
		if g.s(g.Meta[i][0]) == k {
			g.Meta[i][1] = g.put(v)
			return
		}
	}
	g.Meta = append(g.Meta, metaRow{g.put(k), g.put(v)})
}

var hazardCol = func() map[string]int {
	m := map[string]int{}
	for i, c := range symCols {
		if c.kind == 0 && len(c.name) > 2 && c.name[:2] == "n_" {
			m[c.name] = i
		}
	}
	return m
}()

func (g *Graph) materialize(extByCaller map[int32]int32, handlerNames map[string]bool) {
	n := g.nSym()

	for i := range g.Edges {
		e := &g.Edges[i]
		if !e.isSelf {
			g.incID(e.caller, cFANOUT)
			g.incID(e.callee, cFANIN)
		}
	}
	callersOf := map[int32]bool{}
	for i := range g.Callsites {
		g.incID(g.Callsites[i].callee, cNCALLSITES)
	}
	for i := range g.Edges {
		if g.Edges[i].isSelf {
			callersOf[g.Edges[i].caller] = true
		}
	}
	for sid := range callersOf {
		g.setID(sid, cISRECURSIVE, 1)
	}
	unresBy := map[int32]int32{}
	for i := range g.Unresolved {
		unresBy[g.Unresolved[i].caller] += g.Unresolved[i].n
	}
	for sid, v := range unresBy {
		g.setID(sid, cNUNRESOLVEDCALLS, v)
	}
	hazBy := map[int32]int32{}
	catBy := map[[2]int32]int32{}
	for i := range g.Hazards {
		h := &g.Hazards[i]
		hazBy[h.symID] += h.n
		if col, ok := hazardCol["n_"+g.s(h.category)]; ok {
			catBy[[2]int32{h.symID, int32(col)}] += h.n
		}
	}
	for sid, v := range hazBy {
		g.setID(sid, cNHAZARDS, v)
	}
	for k, v := range catBy {
		g.setID(k[0], int(k[1]), v)
	}
	for id := range n {
		g.Syms.set(id, cISLEAF, b2i(g.Syms.at(id, cFANOUT) == 0))
		g.Syms.set(id, cISROOT, b2i(g.Syms.at(id, cFANIN) == 0))
	}

	byCaller := map[int32]int32{}
	for i := range g.Edges {
		byCaller[g.Edges[i].caller]++
	}
	for sid, v := range byCaller {
		g.setID(sid, cNUNIQUECALLS, v)
	}

	modsCalling := map[int32]map[int32]bool{}
	for i := range g.Edges {
		if g.Edges[i].isSelf {
			continue
		}
		mid := g.Syms.at(int(g.Edges[i].caller)-1, cMODULEID)
		s := modsCalling[g.Edges[i].callee]
		if s == nil {
			s = map[int32]bool{}
			modsCalling[g.Edges[i].callee] = s
		}
		s[mid] = true
	}
	for sid, s := range modsCalling {
		g.setID(sid, cNMODULESCALLING, int32(len(s)))
	}
	listenAdd := map[int32]int32{}
	listenRem := map[int32]int32{}
	listenInline := map[int32]int32{}
	timerSetBy := map[int32]int32{}
	timerClearBy := map[int32]int32{}
	timerRep := map[int32]int32{}
	hooksBy := map[int32]int32{}
	hooksCond := map[int32]int32{}
	jsxInline := map[int32]int32{}

	for i := range g.Listeners {
		l := &g.Listeners[i]
		if l.symID == 0 {
			continue
		}
		switch {
		case g.s(l.op) == "add":
			listenAdd[l.symID]++
			if l.inline && !l.signal {
				listenInline[l.symID]++
			}
		case g.s(l.op) == "remove":
			listenRem[l.symID]++
		}
	}
	for i := range g.Timers {
		t := &g.Timers[i]
		if t.symID == 0 {
			continue
		}
		if g.s(t.op) == "set" {
			timerSetBy[t.symID]++
			if t.repeating {
				timerRep[t.symID]++
			}
		} else if g.s(t.op) == "clear" {
			timerClearBy[t.symID]++
		}
	}
	for i := range g.Hooks {
		h := &g.Hooks[i]
		if h.symID == 0 {
			continue
		}
		hooksBy[h.symID]++
		if h.inLoop || h.inCond {
			hooksCond[h.symID]++
		}
	}
	for i := range g.JSX {
		j := &g.JSX[i]
		if j.symID != 0 {
			jsxInline[j.symID] += j.inlineObj + j.inlineFn
		}
	}
	for sid, v := range listenAdd {
		g.setID(sid, cNLISTENERADD, v)
	}
	for sid, v := range listenRem {
		g.setID(sid, cNLISTENERREMOVE, v)
	}
	for sid, v := range listenInline {
		g.setID(sid, cNLISTENERINLINE, v)
	}
	for sid, v := range timerSetBy {
		g.setID(sid, cNTIMERSET, v)
	}
	for sid, v := range timerClearBy {
		g.setID(sid, cNTIMERCLEAR, v)
	}
	for sid, v := range timerRep {
		g.setID(sid, cNTIMERREPEATING, v)
	}
	for sid, v := range hooksBy {
		g.setID(sid, cNHOOKS, v)
	}
	for sid, v := range hooksCond {
		g.setID(sid, cNHOOKSCONDITIONAL, v)
	}
	for sid, v := range jsxInline {
		g.setID(sid, cNINLINEOBJECTPROP, v)
	}

	jsxOwner := map[int32]bool{}
	for i := range g.JSX {
		if sid := g.JSX[i].symID; sid > 0 {
			jsxOwner[sid] = true
		}
	}
	for id := range n {
		g.Syms.set(id, cNAWAITINLOOP, g.Syms.at(id, cAWAITINLOOP))
		g.Syms.set(id, cNLABELED, g.Syms.at(id, cNLABELS))
		if !jsxOwner[int32(id+1)] {
			continue
		}
		name := g.Syms.scol(id, cNAME)
		if name != "" && name[0] >= 'A' && name[0] <= 'Z' {
			g.Syms.set(id, cISCOMPONENT, 1)
		}
	}

	nameToSym := map[[2]any]int32{}
	for id := range n {
		k := [2]any{g.Syms.at(id, cFILEID), g.Syms.scol(id, cNAME)}
		nameToSym[k] = int32(id + 1)
	}
	for i := range g.Exports {
		ex := &g.Exports[i]
		if ex.symID != 0 {
			continue
		}
		if sid, ok := nameToSym[[2]any{ex.fileID, g.s(ex.localName)}]; ok {
			ex.symID = sid
		}
	}

	perFile := map[int32]*[7]int32{}
	for id := range n {
		fid := g.Syms.at(id, cFILEID)
		p := perFile[fid]
		if p == nil {
			p = &[7]int32{}
			perFile[fid] = p
		}
		p[0]++
		k := g.Syms.scol(id, cKIND)
		if k == "function" || k == "method" || k == "constructor" || k == "closure" {
			p[1]++
		}
		if k == "class" || k == "struct" || k == "interface" || k == "trait" ||
			k == "enum" || k == "union" || k == "record" || k == "protocol" ||
			k == "type" || k == "impl" {
			p[2]++
		}
		cy := g.Syms.at(id, cCYCLOMATIC)
		p[3] += cy
		if cy > p[4] {
			p[4] = cy
		}
		p[5] += g.Syms.at(id, cRISKSCORE)
	}
	impPerFile := map[int32]int32{}
	for i := range g.Imports {
		impPerFile[g.Imports[i].fileID]++
	}
	for i := range g.Files {
		f := &g.Files[i]
		if p, ok := perFile[f.id]; ok {
			f.nSymbols, f.nFuncs, f.nTypes = p[0], p[1], p[2]
			f.totalCycles, f.maxCycles, f.totalRisk = p[3], p[4], p[5]
		}
		f.nImports = impPerFile[f.id]
	}

	modSyms := map[int32]*[2]int32{}
	for id := range n {
		mid := g.Syms.at(id, cMODULEID)
		if mid == 0 {
			continue
		}
		p := modSyms[mid]
		if p == nil {
			p = &[2]int32{}
			modSyms[mid] = p
		}
		p[0]++
		p[1] += g.Syms.at(id, cISPUBLIC)
	}
	modFiles := map[int32]*[2]int32{}
	for i := range g.Files {
		f := &g.Files[i]
		if f.moduleID == 0 {
			continue
		}
		p := modFiles[f.moduleID]
		if p == nil {
			p = &[2]int32{}
			modFiles[f.moduleID] = p
		}
		p[0]++
		p[1] += f.sloc
	}
	modFanOut := map[int32]map[int32]bool{}
	modFanIn := map[int32]map[int32]bool{}
	for i := range g.Edges {
		m1 := g.Syms.at(int(g.Edges[i].caller)-1, cMODULEID)
		m2 := g.Syms.at(int(g.Edges[i].callee)-1, cMODULEID)
		if m1 == 0 || m2 == 0 || m1 == m2 {
			continue
		}
		s := modFanOut[m1]
		if s == nil {
			s = map[int32]bool{}
			modFanOut[m1] = s
		}
		s[m2] = true
		s2 := modFanIn[m2]
		if s2 == nil {
			s2 = map[int32]bool{}
			modFanIn[m2] = s2
		}
		s2[m1] = true
	}
	for i := range g.Modules {
		m := &g.Modules[i]
		if p, ok := modSyms[m.id]; ok {
			m.nSymbols, m.nPublic = p[0], p[1]
		}
		if p, ok := modFiles[m.id]; ok {
			m.nFiles, m.sloc = p[0], p[1]
		}
		fo, fi := int32(len(modFanOut[m.id])), int32(len(modFanIn[m.id]))
		m.fanOut, m.fanIn = fo, fi
		if fo+fi != 0 {
			m.instability = float64(fo) / float64(fo+fi)
		} else {
			m.instability = 0.0
		}
	}

	for sid, v := range extByCaller {
		if sid != 0 {
			g.setID(sid, cNEXTERNALCALLS, v)
		}
	}

	for name := range handlerNames {
		for id := range n {
			if g.Syms.scol(id, cNAME) == name {
				g.Syms.set(id, cISHANDLER, 1)
			}
		}
	}

	spans := map[[2]int32]bool{}
	for i := range g.hndFile {
		spans[[2]int32{g.hndFile[i], g.hndSpan[i]}] = true
	}
	for id := range n {
		if spans[[2]int32{g.Syms.at(id, cFILEID), g.Syms.at(id, cBYTESTART)}] {
			g.Syms.set(id, cISHANDLER, 1)
		}
	}

	for id := range n {
		g.Syms.set(id, cRISKSCORE, riskScore(g, id))
		if g.Syms.at(id, cNTOKENS) > 0 {
			no, nd := g.Syms.at(id, cNOPERATORS), g.Syms.at(id, cNOPERANDS)
			distinct := float64(g.Syms.at(id, cNDISTINCTOPERATORS) + g.Syms.at(id, cNDISTINCTOPERANDS))
			mult := 2.0
			if int64(g.Syms.at(id, cNDISTINCTOPERATORS))+int64(g.Syms.at(id, cNDISTINCTOPERANDS)) > 1 {
				mult = distinct
			}
			g.Syms.set(id, cHALSTEADVOLUME, int32(float64(no+nd)*mult))
		}
		k := g.Syms.scol(id, cKIND)
		if k == "function" || k == "method" || k == "constructor" || k == "closure" {
			sloc := float64(g.Syms.at(id, cSLOC))
			sl := 0.05
			if g.Syms.at(id, cSLOC) > 1 {
				sl = sloc / 20.0
			}
			v := maintScore(float64(g.Syms.at(id, cCYCLOMATIC)), sl)
			iv := max(int64(v), 0)
			g.Syms.set(id, cMAINTAINABILITY, int32(iv))
		}
	}
}

func (g *Graph) setID(sid int32, col int, v int32) { g.Syms.set(int(sid)-1, col, v) }

func (g *Graph) incID(sid int32, col int) { g.Syms.inc(int(sid)-1, col) }

func maintScore(cyclo, sl float64) float64 {
	return fsub(fsub(171.0, fmul(0.23, cyclo)), fmul(16.2, sl))
}

//go:noinline
func fmul(a, b float64) float64 { return a * b }

//go:noinline
func fsub(a, b float64) float64 { return a - b }

func b2i(b bool) int32 {
	if b {
		return 1
	}
	return 0
}

func riskScore(g *Graph, id int) int32 {
	s := g.Syms
	v := float64(s.at(id, cCYCLOMATIC))*2 +
		float64(s.at(id, cCOGNITIVE)) +
		float64(s.at(id, cMAXNESTING))*4 +
		float64(s.at(id, cNEVAL))*30 +
		float64(s.at(id, cNEXEC))*20 +
		float64(s.at(id, cNPROTOPOLLUTION))*18 +
		float64(s.at(id, cNREGEXREDOS))*15 +
		float64(s.at(id, cNINNERHTML))*14 +
		float64(s.at(id, cNSYNCCALLS))*8 +
		float64(s.at(id, cNLISTENERINLINE))*6 +
		float64(s.at(id, cNTIMERREPEATING))*6 +
		float64(s.at(id, cNDYNAMICPROP))*3 +
		float64(s.at(id, cNWITHSTMT))*20 +
		float64(s.at(id, cNARGUMENTS))*3 +
		float64(s.at(id, cNDELETE))*2 +
		float64(s.at(id, cNREFLECT))*2 +
		float64(s.at(id, cAWAITINLOOP))*6 +
		float64(s.at(id, cNFLOATINGPROMISE))*2 +
		float64(s.at(id, cNHOOKSCONDITIONAL))*10
	if s.at(id, cISRECURSIVE) == 1 {
		v += 10
	}
	if s.at(id, cISHANDLER) == 1 && s.at(id, cNSYNCCALLS) > 0 {
		v += 25
	}
	add, rem := s.at(id, cNLISTENERADD), s.at(id, cNLISTENERREMOVE)
	if add > rem {
		v += float64(add-rem) * 7
	}
	return int32(v)
}

type rawEdge struct {
	caller, callee int32
	sameFile       bool
	sameMod        bool
	isSelf         bool
	nCalls         int32
	firstLine      int32
}

func (e *emitter) resolveCalls() {
	g := e.g

	unique := make(map[string]int32, len(e.byNameIdx))
	for name, cands := range e.byNameIdx {
		if len(cands) == 1 {
			unique[name] = cands[0].sid
		}
	}

	type typedKey struct{ ty, name string }
	fileScope := map[fileKey]int32{}
	typeScope2 := map[typedKey]int32{}

	symLoc := make(map[int32][2]int32, len(e.byNameIdx)*2)
	for name, cands := range e.byNameIdx {
		for _, c := range cands {
			kk := fileKey{c.fid, name}
			if _, seen := fileScope[kk]; !seen {
				fileScope[kk] = c.sid
			}
			if _, done := symLoc[c.sid]; !done {
				symLoc[c.sid] = [2]int32{c.fid, c.mid}
			}
			if c.typeName != "" {
				tk := typedKey{c.typeName, name}
				if _, seen := typeScope2[tk]; !seen {
					typeScope2[tk] = c.sid
				}
			}
		}
	}
	edges := make([]rawEdge, 0, len(e.pendSid))
	seen := make(map[uint64]int32, len(e.pendSid)/2)
	unres := map[unresKey]int32{}
	unresOrder := make([]unresKey, 0, 64)
	unresFirst := map[unresKey]int32{}
	var callsites []Callsite
	csSeen := map[Callsite]bool{}

	for i := range e.pendSid {
		sid := e.pendSid[i]
		fid := e.pendFid[i]
		mid := e.pendMid[i]
		line := e.pendLine[i]
		raw := e.pendName[i]
		ty := e.pendType[i]
		name := normaliseCallee(raw)
		if name == "" {
			continue
		}
		base := name
		if j := strings.LastIndex(name, "."); j >= 0 {
			base = name[j+1:]
		}
		if j := strings.LastIndex(base, "::"); j >= 0 {
			base = base[j+1:]
		}
		target := int32(0)
		if ty != "" {
			if s, ok := typeScope2[typedKey{ty, base}]; ok {
				target = s
			}
		}
		if target == 0 {
			if s, ok := e.byQual[name]; ok {
				target = s
			}
		}
		if target == 0 {
			if s, ok := fileScope[fileKey{fid, base}]; ok {
				target = s
			}
		}
		if target == 0 {
			if s, ok := unique[base]; ok {
				target = s
			}
		}
		if target == 0 {
			if e.isExternal(name, base, fid) {
				e.nExtByCaller[sid]++
				e.nExternal++
			} else {
				k := unresKey{sid, clip(name, 160)}
				if _, ok := unresFirst[k]; !ok {
					unresFirst[k] = line
					unresOrder = append(unresOrder, k)
				}
				unres[k]++
				e.nUnresolved++
			}
			continue
		}
		loc, hasLoc := symLoc[target]
		sameFile := hasLoc && loc[0] == fid
		sameMod := hasLoc && loc[1] == mid
		self := target == sid
		key := uint64(uint32(sid))<<32 | uint64(uint32(target))
		if idx, ok := seen[key]; ok {
			edges[idx].nCalls++
		} else {
			seen[key] = int32(len(edges))
			edges = append(edges, rawEdge{sid, target, sameFile, sameMod, self, 1, line})
		}
		if line != 0 {
			cs := Callsite{sid, target, line}
			if !csSeen[cs] {
				csSeen[cs] = true
				callsites = append(callsites, cs)
			}
		}
		e.nResolved++
	}

	g.Edges = make([]Edge, len(edges))
	for i, re := range edges {
		g.Edges[i] = Edge{re.caller, re.callee, re.nCalls, re.sameFile, re.sameMod, re.isSelf}
	}
	sort.SliceStable(callsites, func(i, j int) bool {
		if callsites[i].caller != callsites[j].caller {
			return callsites[i].caller < callsites[j].caller
		}
		if callsites[i].callee != callsites[j].callee {
			return callsites[i].callee < callsites[j].callee
		}
		return callsites[i].line < callsites[j].line
	})
	g.Callsites = callsites

	g.Unresolved = make([]Unresolved, 0, len(unresOrder))
	for _, k := range unresOrder {
		g.Unresolved = append(g.Unresolved, Unresolved{k.caller, g.put(k.name),
			unres[k], unresFirst[k]})
	}

	e.pendSid, e.pendFid, e.pendMid, e.pendLine = nil, nil, nil, nil
	e.pendName, e.pendType = nil, nil
	e.byNameIdx = nil
	e.byQual = nil
	g.setMeta("calls_resolved", "%d in-tree / %d external / %d unresolved (%d%% of in-scope resolved)",
		e.nResolved, e.nExternal, e.nUnresolved,
		100*e.nResolved/maxI32(1, e.nResolved+e.nUnresolved))
}

type fileKey struct {
	fid  int32
	name string
}

type unresKey struct {
	caller int32
	name   string
}

type gname struct {
	sid, fid, mid int32
	typeName      string
}

func maxI32(a, b int32) int32 {
	if a > b {
		return a
	}
	return b
}

func normaliseCallee(raw string) string {
	name := strings.TrimSpace(raw)
	name = strings.ReplaceAll(name, "?.", ".")
	if strings.Contains(name, " ") {
		name = reSpaceDot.ReplaceAllString(name, ".")
	}
	if name == "" {
		return ""
	}
	switch name[0] {
	case '(', '[', '{':
		return ""
	}
	if name == "super" || name == "this" || name == "import" {
		return ""
	}
	if strings.Contains(name, "(") || strings.Contains(name, "[") {

		if i := strings.LastIndex(name, "."); i >= 0 {
			name = name[i+1:]
		} else {
			return ""
		}
		if strings.Contains(name, "(") || strings.Contains(name, "[") {
			return ""
		}
	}
	for _, prefix := range []string{"this.", "self.", "globalThis.", "window."} {
		if strings.HasPrefix(name, prefix) {
			name = name[len(prefix):]
			break
		}
	}
	return name
}

func (e *emitter) isExternal(name, base string, fid int32) bool {
	head := name
	if before, _, ok := strings.Cut(name, "."); ok {
		head = before
	}
	if jsGlobals[head] || jsGlobals[name] {
		return true
	}
	if nodeBuiltins[head] || strings.HasPrefix(name, "node:") {
		return true
	}
	if b, ok := e.bindingsByFile[fid][head]; ok && b.external {
		return true
	}
	if reGeneratedHint.MatchString(head) {
		return true
	}

	if strings.Contains(name, ".") {
		if _, defined := e.nameExists[base]; !defined && arrayProto[base] {
			return true
		}
	}
	return false
}

func (e *emitter) resolveImportTargets() {
	g := e.g
	byPath := make(map[string]int32, len(g.Files)*2)
	for i := range g.Files {
		p := strings.ReplaceAll(g.s(g.Files[i].path), "/", "/")
		byPath[p] = int32(i + 1)
		if k := strings.LastIndex(p, "."); k > 0 {
			stem := p[:k]
			if _, ok := byPath[stem]; !ok {
				byPath[stem] = int32(i + 1)
			}
		}
	}

	specCandidates := func(base string) []string {
		return []string{base, base + ".js", base + ".mjs", base + ".cjs",
			base + ".jsx", base + "/index.js", base + "/index.mjs",
			base + "/index.cjs", base + "/index.jsx"}
	}
	specHit := func(here, spec string) int32 {
		if spec == "" || !strings.HasPrefix(spec, ".") {
			return 0
		}
		base := normPath(joinPath(here, spec))
		for _, cand := range specCandidates(base) {
			if id, ok := byPath[cand]; ok {
				return id
			}
		}
		return 0
	}
	for i := range g.Imports {
		im := &g.Imports[i]
		if im.targetID != 0 || g.s(im.target) == "" {
			continue
		}
		im.targetID = specHit(dirOf(g.s(g.Files[im.fileID-1].path)), g.s(im.target))
	}
	for i := range g.ImportNames {
		in := &g.ImportNames[i]
		if in.sourceID != 0 || g.s(in.source) == "" {
			continue
		}
		in.sourceID = specHit(dirOf(g.s(g.Files[in.fileID-1].path)), g.s(in.source))
	}
	for i := range g.Exports {
		ex := &g.Exports[i]
		if ex.sourceID != 0 || g.s(ex.source) == "" {
			continue
		}
		ex.sourceID = specHit(dirOf(g.s(g.Files[ex.fileID-1].path)), g.s(ex.source))
	}
	importSuffixes := []string{"", ".py", ".pyi", ".ts", ".tsx", ".d.ts", ".mts", ".cts",
		".js", ".jsx", ".mjs", ".cjs", ".rb", ".php", ".go", ".rs", ".java"}
	importIndexes := []string{"__init__.py", "index.ts", "index.tsx", "index.js",
		"index.mjs", "mod.rs", "lib.rs"}
	look := func(cand string) int32 {
		cand = strings.Trim(cand, "/")
		if cand == "" {
			return 0
		}
		for _, suf := range importSuffixes {
			if hit, ok := byPath[cand+suf]; ok {
				return hit
			}
		}
		for _, idx := range importIndexes {
			if hit, ok := byPath[cand+"/"+idx]; ok {
				return hit
			}
		}
		return 0
	}

	n := 0
	for i := range g.Imports {
		im := &g.Imports[i]
		if im.targetID != 0 || g.s(im.target) == "" {
			continue
		}
		fid := im.fileID
		path := g.s(g.Files[fid-1].path)
		t := strings.TrimSpace(strings.ReplaceAll(g.s(im.target), "/", "/"))
		here := dirOf(path)
		var hit int32
		if strings.HasPrefix(t, ".") {
			nUp := len(t) - len(strings.TrimLeft(t, "."))
			var rest string
			if !strings.Contains(t, "/") {
				rest = strings.ReplaceAll(t[nUp:], ".", "/")
			} else {
				rest = strings.TrimLeft(t, "./")
			}
			base := here
			for k := 0; k < maxI(0, nUp-1); k++ {
				base = dirOf(base)
			}
			if base != "" && base != "." {
				hit = look(base + "/" + rest)
			} else {
				hit = look(rest)
			}
		} else {
			hit = look(strings.ReplaceAll(t, ".", "/"))
			if hit == 0 {
				hit = look(here + "/" + t)
			}
		}
		if hit != 0 && hit != fid {
			im.targetID = hit
			n++
		}
	}
	g.setMeta("imports_resolved", "%d of %d import rows point at a file in this tree",
		n, len(g.Imports))
}

func sprintf(format string, args ...any) string { return fmt.Sprintf(format, args...) }

func stdout() *os.File { return os.Stdout }

func createFile(path string) (*os.File, error) { return os.Create(path) }

var reSpaceDot = regexp.MustCompile(`\s*\.\s*`)

func normPath(p string) string {
	if p == "" {
		return "."
	}
	rooted := p[0] == '/'
	var out []string
	for _, part := range splitSlash(p) {
		switch part {
		case "", ".":
			continue
		case "..":
			if len(out) > 0 && out[len(out)-1] != ".." {
				out = out[:len(out)-1]
			} else if !rooted {
				out = append(out, "..")
			}
		default:
			out = append(out, part)
		}
	}
	res := joinSlash(out)
	if rooted {
		return "/" + res
	}
	if res == "" {
		return "."
	}
	return res
}

func splitSlash(p string) []string {
	var out []string
	start := 0
	for i := 0; i < len(p); i++ {
		if p[i] == '/' {
			out = append(out, p[start:i])
			start = i + 1
		}
	}
	return append(out, p[start:])
}

func joinSlash(parts []string) string {
	var out strings.Builder
	for i, p := range parts {
		if i > 0 {
			out.WriteString("/")
		}
		out.WriteString(p)
	}
	return out.String()
}

func joinPath(a, b string) string {
	if a == "" {
		return b
	}
	if b == "" {
		return a
	}
	return a + "/" + b
}

var hazardCalls = map[string]string{}

func init() {
	type kv struct{ name, cat string }
	tbl := []kv{

		{"readFileSync", "sync_block"}, {"writeFileSync", "sync_block"},
		{"appendFileSync", "sync_block"}, {"existsSync", "sync_block"},
		{"statSync", "sync_block"}, {"lstatSync", "sync_block"},
		{"readdirSync", "sync_block"}, {"mkdirSync", "sync_block"},
		{"rmSync", "sync_block"}, {"rmdirSync", "sync_block"},
		{"unlinkSync", "sync_block"}, {"copyFileSync", "sync_block"},
		{"renameSync", "sync_block"}, {"realpathSync", "sync_block"},
		{"readlinkSync", "sync_block"}, {"openSync", "sync_block"},
		{"closeSync", "sync_block"}, {"readSync", "sync_block"},
		{"writeSync", "sync_block"}, {"truncateSync", "sync_block"},
		{"accessSync", "sync_block"}, {"chmodSync", "sync_block"},
		{"utimesSync", "sync_block"}, {"globSync", "sync_block"},
		{"pbkdf2Sync", "sync_block"}, {"scryptSync", "sync_block"},
		{"randomBytesSync", "sync_block"}, {"randomFillSync", "sync_block"},
		{"deflateSync", "sync_block"}, {"inflateSync", "sync_block"},
		{"gzipSync", "sync_block"}, {"gunzipSync", "sync_block"},
		{"brotliCompressSync", "sync_block"}, {"brotliDecompressSync", "sync_block"},
		{"execFileSync", "sync_block"}, {"spawnSync", "sync_block"},
		{"JSON.parse", "sync_block"}, {"JSON.stringify", "sync_block"},
		{"Atomics.wait", "sync_block"}, {"structuredClone", "sync_block"},

		{"eval", "exec"}, {"Function", "exec"}, {"execSync", "exec"},
		{"exec", "exec"}, {"execFile", "exec"}, {"spawn", "exec"}, {"fork", "exec"},
		{"child_process.exec", "exec"}, {"child_process.execSync", "exec"},
		{"vm.runInNewContext", "exec"}, {"vm.runInThisContext", "exec"},
		{"vm.runInContext", "exec"}, {"vm.compileFunction", "exec"},
		{"vm.Script", "exec"}, {"createRequire", "exec"},
		{"process.dlopen", "exec"}, {"module._compile", "exec"},
		{"setTimeout_string", "exec"},

		{"Object.setPrototypeOf", "proto_pollution"},
		{"Object.assign", "proto_pollution"},
		{"merge", "proto_pollution"}, {"deepMerge", "proto_pollution"},
		{"mergeDeep", "proto_pollution"}, {"defaultsDeep", "proto_pollution"},
		{"extend", "proto_pollution"}, {"deepExtend", "proto_pollution"},
		{"_.merge", "proto_pollution"}, {"_.set", "proto_pollution"},
		{"_.defaultsDeep", "proto_pollution"}, {"_.extend", "proto_pollution"},
		{"objectPath.set", "proto_pollution"}, {"dot.set", "proto_pollution"},
		{"setValue", "proto_pollution"}, {"setIn", "proto_pollution"},

		{"RegExp", "redos"}, {"matchAll", "redos"}, {"replaceAll", "redos"},

		{"addEventListener", "listener"}, {"removeEventListener", "listener"},
		{"addListener", "listener"}, {"removeListener", "listener"},
		{"removeAllListeners", "listener"}, {"prependListener", "listener"},
		{"prependOnceListener", "listener"},
		{"on", "listener"}, {"once", "listener"}, {"off", "listener"},
		{"subscribe", "listener"}, {"unsubscribe", "listener"},
		{"observe", "listener"}, {"unobserve", "listener"}, {"disconnect", "listener"},
		{"IntersectionObserver", "listener"}, {"MutationObserver", "listener"},
		{"ResizeObserver", "listener"}, {"PerformanceObserver", "listener"},
		{"AbortController", "listener"}, {"EventTarget", "listener"},
		{"EventEmitter", "listener"},

		{"Map", "cache"}, {"Set", "cache"}, {"WeakMap", "cache"}, {"WeakSet", "cache"},
		{"WeakRef", "cache"}, {"FinalizationRegistry", "cache"},
		{"LRUCache", "cache"}, {"lru", "cache"}, {"memoize", "cache"},
		{"Object.create", "cache"},

		{"setTimeout", "timer"}, {"setInterval", "timer"}, {"setImmediate", "timer"},
		{"clearTimeout", "timer"}, {"clearInterval", "timer"},
		{"clearImmediate", "timer"},
		{"requestAnimationFrame", "timer"}, {"cancelAnimationFrame", "timer"},
		{"requestIdleCallback", "timer"}, {"cancelIdleCallback", "timer"},
		{"process.nextTick", "timer"}, {"queueMicrotask", "timer"},
		{"setTimeout.unref", "timer"},

		{"readFile", "io"}, {"writeFile", "io"}, {"appendFile", "io"},
		{"createReadStream", "io"}, {"createWriteStream", "io"},
		{"readdir", "io"}, {"mkdir", "io"}, {"unlink", "io"}, {"rename", "io"},
		{"pipe", "io"}, {"pipeline", "io"}, {"pipeTo", "io"}, {"pipeThrough", "io"},
		{"fs.promises", "io"}, {"opendir", "io"}, {"watch", "io"}, {"watchFile", "io"},
		{"createInterface", "io"},

		{"fetch", "net"}, {"XMLHttpRequest", "net"}, {"WebSocket", "net"},
		{"EventSource", "net"}, {"sendBeacon", "net"},
		{"http.request", "net"}, {"https.request", "net"}, {"http.get", "net"},
		{"https.get", "net"}, {"http.createServer", "net"},
		{"https.createServer", "net"}, {"net.createServer", "net"},
		{"net.connect", "net"}, {"tls.connect", "net"}, {"dgram.createSocket", "net"},
		{"axios", "net"}, {"axios.get", "net"}, {"axios.post", "net"},
		{"axios.put", "net"}, {"axios.delete", "net"}, {"axios.request", "net"},
		{"got", "net"}, {"superagent", "net"}, {"request", "net"},
		{"navigator.sendBeacon", "net"}, {"importScripts", "net"},

		{"insertAdjacentHTML", "dom"}, {"document.write", "dom"},
		{"document.writeln", "dom"}, {"createContextualFragment", "dom"},
		{"execCommand", "dom"}, {"srcdoc", "dom"},
		{"innerHTML", "dom"}, {"outerHTML", "dom"},
		{"dangerouslySetInnerHTML", "dom"}, {"v-html", "dom"},

		{"localStorage", "storage"}, {"sessionStorage", "storage"},
		{"indexedDB", "storage"}, {"openDatabase", "storage"},
		{"caches.open", "storage"}, {"localStorage.setItem", "storage"},
		{"sessionStorage.setItem", "storage"}, {"cookieStore.set", "storage"},

		{"Math.random", "crypto"}, {"createHash", "crypto"},
		{"createCipher", "crypto"}, {"createDecipher", "crypto"},
		{"pseudoRandomBytes", "crypto"}, {"btoa", "crypto"}, {"atob", "crypto"},

		{"Object.defineProperty", "reflect"}, {"Object.defineProperties", "reflect"},
		{"Object.getOwnPropertyDescriptor", "reflect"},
		{"Proxy", "reflect"}, {"Reflect.get", "reflect"}, {"Reflect.set", "reflect"},
		{"Reflect.has", "reflect"}, {"Reflect.apply", "reflect"},
		{"Reflect.construct", "reflect"}, {"Reflect.ownKeys", "reflect"},
		{"Reflect.defineProperty", "reflect"},
		{"apply", "reflect"}, {"call", "reflect"}, {"bind", "reflect"},
		{"__defineGetter__", "reflect"}, {"__defineSetter__", "reflect"},

		{"Array.from", "alloc"}, {"Array.of", "alloc"}, {"Object.entries", "alloc"},
		{"Object.keys", "alloc"}, {"Object.values", "alloc"},
		{"Object.fromEntries", "alloc"}, {"concat", "alloc"}, {"slice", "alloc"},
		{"splice", "alloc"}, {"flat", "alloc"}, {"flatMap", "alloc"},
		{"Buffer.alloc", "alloc"}, {"Buffer.allocUnsafe", "alloc"},
		{"Buffer.from", "alloc"}, {"Buffer.concat", "alloc"},
		{"structuredClone_alloc", "alloc"},
	}
	for _, e := range tbl {
		hazardCalls[e.name] = e.cat
	}
}

var listenerAdd = map[string]string{
	"addEventListener": "dom", "on": "emitter", "once": "emitter",
	"addListener": "emitter", "prependListener": "emitter",
	"prependOnceListener": "emitter", "subscribe": "observable",
	"observe": "observer", "attachEvent": "dom", "listen": "emitter",
	"addEventHandler": "dom", "$on": "emitter",
}

var listenerRemove = map[string]string{
	"removeEventListener": "dom", "off": "emitter",
	"removeListener": "emitter", "removeAllListeners": "emitter",
	"unsubscribe": "observable", "dispose": "observable",
	"unobserve": "observer", "disconnect": "observer",
	"detachEvent": "dom", "abort": "signal", "$off": "emitter",
	"destroy": "observable", "teardown": "observable",
}

var observerCtors = map[string]bool{
	"IntersectionObserver": true, "MutationObserver": true, "ResizeObserver": true,
	"PerformanceObserver": true, "ReportingObserver": true,
}

var timerSet = map[string]string{
	"setTimeout": "timeout", "setInterval": "interval",
	"setImmediate": "immediate", "requestAnimationFrame": "raf",
	"requestIdleCallback": "idle",
}

var timerClear = map[string]string{
	"clearTimeout": "timeout", "clearInterval": "interval",
	"clearImmediate": "immediate", "cancelAnimationFrame": "raf",
	"cancelIdleCallback": "idle",
}

var timerRepeating = map[string]bool{"interval": true, "raf": true}

var cacheCtors = map[string]string{
	"Map": "Map", "Set": "Set", "WeakMap": "WeakMap", "WeakSet": "WeakSet",
	"Array": "Array", "LRUCache": "LRUCache", "QuickLRU": "LRUCache",
}

var weakCtors = map[string]bool{"WeakMap": true, "WeakSet": true, "WeakRef": true}

var routeMethods = map[string]bool{
	"get": true, "post": true, "put": true, "patch": true, "delete": true,
	"head": true, "options": true, "all": true, "use": true, "route": true,
	"handle": true, "addRoute": true, "register": true,
}

var depArrayHooks = map[string]bool{
	"useEffect": true, "useLayoutEffect": true, "useMemo": true,
	"useCallback": true, "useInsertionEffect": true, "useImperativeHandle": true,
}

var builtinHooks = map[string]bool{
	"useState": true, "useEffect": true, "useContext": true, "useReducer": true,
	"useCallback": true, "useMemo": true, "useRef": true,
	"useImperativeHandle": true, "useLayoutEffect": true, "useDebugValue": true,
	"useDeferredValue": true, "useTransition": true, "useId": true,
	"useSyncExternalStore": true, "useInsertionEffect": true, "useActionState": true,
	"useOptimistic": true, "useFormStatus": true, "use": true,
}

var reRouteObjects = regexp.MustCompile(`(?i)^(app|router|server|api|fastify|express|koa|http|https|r)\b`)

var arrayProto = func() map[string]bool {
	m := map[string]bool{}
	for s := range strings.FieldsSeq(`map filter reduce reduceRight forEach some every
		find findIndex findLast findLastIndex includes indexOf lastIndexOf join
		reverse sort concat slice splice push pop shift unshift fill flat flatMap
		keys values entries at toString valueOf hasOwnProperty toFixed toPrecision
		charAt charCodeAt codePointAt startsWith endsWith padStart padEnd trim
		trimStart trimEnd split replace replaceAll match matchAll search normalize
		repeat toLowerCase toUpperCase localeCompare toISOString getTime setTime
		add clear delete get has set size then catch finally next return throw
		bind call apply`) {
		m[s] = true
	}
	return m
}()

var nodeBuiltins = func() map[string]bool {
	m := map[string]bool{}
	for s := range strings.FieldsSeq(`assert async_hooks buffer child_process
		cluster console constants crypto dgram diagnostics_channel dns domain
		events fs http http2 https inspector module net os path perf_hooks
		process punycode querystring readline repl sea sqlite stream
		string_decoder sys test timers tls trace_events tty url util v8 vm
		wasi worker_threads zlib`) {
		m[s] = true
	}
	return m
}()

var jsGlobals = func() map[string]bool {
	m := map[string]bool{}
	for s := range strings.FieldsSeq(`Array ArrayBuffer AsyncFunction
		AsyncGenerator AsyncIterator Atomics BigInt BigInt64Array BigUint64Array
		Boolean DataView Date Error EvalError FinalizationRegistry Float16Array
		Float32Array Float64Array Function Generator Infinity Int8Array Int16Array
		Int32Array Intl Iterator JSON Map Math NaN Number Object Promise Proxy
		RangeError ReferenceError Reflect RegExp Set SharedArrayBuffer String
		Symbol SyntaxError Temporal TypeError Uint8Array Uint8ClampedArray
		Uint16Array Uint32Array URIError WeakMap WeakRef WeakSet decodeURI
		decodeURIComponent encodeURI encodeURIComponent escape eval globalThis
		isFinite isNaN parseFloat parseInt undefined unescape console process
		Buffer global queueMicrotask structuredClone setTimeout setInterval
		setImmediate clearTimeout clearInterval clearImmediate require module
		exports __dirname __filename import fetch Headers Request Response
		FormData URL URLSearchParams AbortController AbortSignal Blob File
		TextEncoder TextDecoder CompressionStream DecompressionStream
		ReadableStream WritableStream TransformStream BroadcastChannel MessageChannel
		Event EventTarget CustomEvent ErrorEvent MessageEvent CloseEvent crypto
		performance navigator localStorage sessionStorage indexedDB caches window
		document location history screen alert confirm prompt
		requestAnimationFrame cancelAnimationFrame requestIdleCallback
		XMLHttpRequest WebSocket EventSource Worker SharedWorker ServiceWorker
		IntersectionObserver MutationObserver ResizeObserver PerformanceObserver
		HTMLElement Element Node NodeList DOMParser Image Audio Video Notification
		React ReactDOM`) {
		m[s] = true
	}
	return m
}()

func cgLines(s string, fn func(line string)) {
	if s == "" {
		return
	}
	start := 0
	i := 0
	for i < len(s) {
		c := s[i]
		if c < utf8.RuneSelf {
			brk := false
			switch c {
			case '\n', '\v', '\f', '\r', 0x1c, 0x1d, 0x1e:
				brk = true
			}
			if brk {
				fn(s[start:i])
				if c == '\r' && i+1 < len(s) && s[i+1] == '\n' {
					i++
				}
				i++
				start = i
				continue
			}
			i++
			continue
		}
		r, w := utf8.DecodeRuneInString(s[i:])
		if r == 0x85 || r == 0x2028 || r == 0x2029 {
			fn(s[start:i])
			i += w
			start = i
			continue
		}
		i += w
	}
	if start < len(s) {
		fn(s[start:])
	}
}

func isCgSpace(r rune) bool {
	return unicode.IsSpace(r) || (r >= 0x1c && r <= 0x1f)
}

func cgStrip(s string) string { return strings.TrimFunc(s, isCgSpace) }

func cgSplit(s string) []string { return strings.FieldsFunc(s, isCgSpace) }

func clip(s string, n int) string {
	if n <= 0 {
		return ""
	}
	cnt := 0
	for i := range s {
		if cnt == n {
			return s[:i]
		}
		cnt++
	}
	return s
}

func cgReprFloat(f float64) string {
	if math.IsInf(f, 1) {
		return "inf"
	}
	if math.IsInf(f, -1) {
		return "-inf"
	}
	if math.IsNaN(f) {
		return "nan"
	}
	if f == 0 {
		if math.Signbit(f) {
			return "-0.0"
		}
		return "0.0"
	}
	neg := f < 0
	if neg {
		f = -f
	}
	mant := strconv.FormatFloat(f, 'e', -1, 64)
	epos := strings.IndexByte(mant, 'e')
	digits := strings.Replace(mant[:epos], ".", "", 1)
	exp, _ := strconv.Atoi(mant[epos+1:])
	decpt := exp + 1

	var b strings.Builder
	if neg {
		b.WriteByte('-')
	}
	switch {
	case decpt <= -4 || decpt > 16:
		b.WriteByte(digits[0])
		if len(digits) > 1 {
			b.WriteByte('.')
			b.WriteString(digits[1:])
		}
		e := decpt - 1
		b.WriteByte('e')
		if e < 0 {
			b.WriteByte('-')
			e = -e
		} else {
			b.WriteByte('+')
		}
		if e < 10 {
			b.WriteByte('0')
		}
		b.WriteString(strconv.Itoa(e))
	case decpt <= 0:
		b.WriteString("0.")
		for i := 0; i < -decpt; i++ {
			b.WriteByte('0')
		}
		b.WriteString(digits)
	case decpt >= len(digits):
		b.WriteString(digits)
		for i := 0; i < decpt-len(digits); i++ {
			b.WriteByte('0')
		}
		b.WriteString(".0")
	default:
		b.WriteString(digits[:decpt])
		b.WriteByte('.')
		b.WriteString(digits[decpt:])
	}
	return b.String()
}

func lowerASCII(r rune) rune {
	if r >= 'A' && r <= 'Z' {
		return r + 32
	}
	return r
}

func likeMatch(pattern, s string) bool {
	p := []rune(pattern)
	t := []rune(s)
	pi, ti := 0, 0
	star, mark := -1, 0
	for ti < len(t) {
		if pi < len(p) {
			c := p[pi]
			switch {
			case c == '%':
				star = pi
				pi++
				mark = ti
				continue
			case c == '_' || lowerASCII(c) == lowerASCII(t[ti]):
				pi++
				ti++
				continue
			}
		}
		if star >= 0 {
			pi = star + 1
			mark++
			ti = mark
			continue
		}
		return false
	}
	for pi < len(p) && p[pi] == '%' {
		pi++
	}
	return pi == len(p)
}

func instr(hay, needle string) int {
	if needle == "" {
		return 1
	}
	before, _, ok := strings.Cut(hay, needle)
	if !ok {
		return 0
	}
	return utf8.RuneCountInString(before) + 1
}

func sqlLen(s string) int { return utf8.RuneCountInString(s) }

func groupConcatDistinctOrder(vals []string) string {
	seen := make(map[string]bool, len(vals))
	out := make([]string, 0, len(vals))
	for _, v := range vals {
		if !seen[v] {
			seen[v] = true
			out = append(out, v)
		}
	}
	return strings.Join(out, ",")
}

func groupConcatDistinct(vals []string) string {
	if len(vals) == 0 {
		return ""
	}
	out := append([]string(nil), vals...)
	sort.Strings(out)
	seen := make(map[string]bool, len(out))
	uniq := out[:0]
	for _, v := range out {
		if !seen[v] {
			seen[v] = true
			uniq = append(uniq, v)
		}
	}
	return strings.Join(uniq, ",")
}

type orderTerm struct {
	less func(a, b int) bool
}

func byInt(get func(i int) int) orderTerm {
	return orderTerm{less: func(a, b int) bool { return get(a) < get(b) }}
}

func byIntDesc(get func(i int) int) orderTerm {
	return orderTerm{less: func(a, b int) bool { return get(a) > get(b) }}
}

func byStr(get func(i int) string) orderTerm {
	return orderTerm{less: func(a, b int) bool { return get(a) < get(b) }}
}

func byBoolDesc(get func(i int) bool) orderTerm {
	return orderTerm{less: func(a, b int) bool { return get(a) && !get(b) }}
}

func orderBy(idx []int, terms []orderTerm) {
	sort.SliceStable(idx, func(i, j int) bool {
		a, b := idx[i], idx[j]
		for _, t := range terms {
			if t.less(a, b) {
				return true
			}
			if t.less(b, a) {
				return false
			}
		}
		return false
	})
}

func sortedIDs[V any](m map[int32]V) []int32 {
	out := make([]int32, 0, len(m))
	for k := range m {
		out = append(out, k)
	}
	slices.Sort(out)
	return out
}

func sortedReachPairs(m map[reachPair]int32) []reachPair {
	out := make([]reachPair, 0, len(m))
	for k := range m {
		out = append(out, k)
	}
	sort.Slice(out, func(i, j int) bool {
		if out[i].root != out[j].root {
			return out[i].root < out[j].root
		}
		return out[i].sym < out[j].sym
	})
	return out
}

type rootSym struct{ root, sym int32 }

func sortedPairs[V any](m map[rootSym]V) []rootSym {
	out := make([]rootSym, 0, len(m))
	for k := range m {
		out = append(out, k)
	}
	sort.Slice(out, func(i, j int) bool {
		if out[i].root != out[j].root {
			return out[i].root < out[j].root
		}
		return out[i].sym < out[j].sym
	})
	return out
}

func sortedNames[V any](m map[string]V) []string {
	out := make([]string, 0, len(m))
	for k := range m {
		out = append(out, k)
	}
	sort.Strings(out)
	return out
}

type reachPair struct{ root, sym int32 }

type reachOut struct {
	depth map[reachPair]int32
	syms  []int32
}

func (g *Graph) reachDown(entries []int32, maxDepth int32) *reachOut {
	out := &reachOut{depth: make(map[reachPair]int32, len(entries)*4)}
	queue := make([]reachPair, 0, len(entries)*4)
	byCaller := map[int32][]int32{}
	for i := range g.Edges {
		if g.Edges[i].isSelf {
			continue
		}
		byCaller[g.Edges[i].caller] = append(byCaller[g.Edges[i].caller], g.Edges[i].callee)
	}
	for _, e := range entries {
		k := reachPair{e, e}
		out.depth[k] = 0
		queue = append(queue, k)
	}
	for qi := 0; qi < len(queue); qi++ {
		cur := queue[qi]
		if cur.depthOf(out) >= maxDepth {
			continue
		}
		for _, cal := range byCaller[cur.sym] {
			nk := reachPair{cur.root, cal}
			if _, seen := out.depth[nk]; !seen {
				out.depth[nk] = out.depth[cur] + 1
				queue = append(queue, nk)
			}
		}
	}
	for k := range out.depth {
		out.syms = append(out.syms, k.sym)
	}
	return out
}

func (r reachPair) depthOf(o *reachOut) int32 { return o.depth[r] }

func (g *Graph) reachDownAll(entries []int32, maxDepth int32) map[int32]int32 {
	full := g.reachDown(entries, maxDepth)
	best := make(map[int32]int32, len(full.depth))
	for k, v := range full.depth {
		if old, ok := best[k.sym]; !ok || v < old {
			best[k.sym] = v
		}
	}
	return best
}

func (g *Graph) reachDownMax(entries []int32, maxDepth int32) (maxDepthBy map[int32]int32,
	subtree map[int32]int32) {
	byCaller := map[int32][]int32{}
	for i := range g.Edges {
		if g.Edges[i].isSelf {
			continue
		}
		byCaller[g.Edges[i].caller] = append(byCaller[g.Edges[i].caller], g.Edges[i].callee)
	}
	maxDepthBy = make(map[int32]int32, len(entries))
	subtree = make(map[int32]int32, len(entries))
	seen := make(map[[3]int32]bool, len(entries)*4)
	type step struct {
		root, sym, depth int32
	}
	queue := make([]step, 0, len(entries)*4)
	for _, e := range entries {
		queue = append(queue, step{e, e, 0})
		seen[[3]int32{e, e, 0}] = true
	}
	for qi := 0; qi < len(queue); qi++ {
		cur := queue[qi]
		if cur.depth > maxDepthBy[cur.root] {
			maxDepthBy[cur.root] = cur.depth
		}
		if cur.depth >= maxDepth {
			continue
		}
		for _, cal := range byCaller[cur.sym] {
			k := [3]int32{cur.root, cal, cur.depth + 1}
			if seen[k] {
				continue
			}
			seen[k] = true
			queue = append(queue, step{k[0], k[1], k[2]})
		}
	}

	pairs := make(map[[2]int32]bool, len(seen))
	for k := range seen {
		pk := [2]int32{k[0], k[1]}
		if !pairs[pk] {
			pairs[pk] = true
			subtree[k[0]]++
		}
	}
	return maxDepthBy, subtree
}

func (g *Graph) reachUp(entries []int32, maxDepth int32) map[int32]int32 {
	byCallee := map[int32][]int32{}
	for i := range g.Edges {
		if g.Edges[i].isSelf {
			continue
		}
		byCallee[g.Edges[i].callee] = append(byCallee[g.Edges[i].callee], g.Edges[i].caller)
	}
	best := make(map[int32]int32, len(entries))
	queue := make([]int32, 0, len(entries))
	for _, e := range entries {
		if _, ok := best[e]; !ok {
			best[e] = 0
			queue = append(queue, e)
		}
	}
	for qi := 0; qi < len(queue); qi++ {
		cur := queue[qi]
		if best[cur] >= maxDepth {
			continue
		}
		nd := best[cur] + 1
		for _, caller := range byCallee[cur] {
			if old, ok := best[caller]; !ok || nd > old {
				best[caller] = nd
				queue = append(queue, caller)
			}
		}
	}
	return best
}

type fileFilter int

const (
	fNotTest fileFilter = iota
	fNotTestGen
	fNotGen
	fAny
)

func (f fileFilter) ok(fl *File) bool {
	switch f {
	case fNotTest:
		return !fl.isTest
	case fNotTestGen:
		return !fl.isTest && !fl.isGen
	case fNotGen:
		return !fl.isGen
	}
	return true
}

func (g *Graph) kindsOf(symID int32) (int, string) {
	var vals []string
	n := 0
	for i := range g.UserInput {
		if g.UserInput[i].symID == symID {
			n++
			vals = append(vals, g.s(g.UserInput[i].kind))
		}
	}
	return n, groupConcatDistinct(vals)
}

func (g *Graph) formReads(symID int32) int {
	n := 0
	for i := range g.UserInput {
		if g.UserInput[i].symID == symID && g.s(g.UserInput[i].kind) == "form" {
			n++
		}
	}
	return n
}

func (g *Graph) hazPatternList(symID int32, cats ...string) string {
	var vals []string
	for i := range g.Hazards {
		h := &g.Hazards[i]
		if h.symID != symID {
			continue
		}
		if slices.Contains(cats, g.s(h.category)) {
			vals = append(vals, g.s(h.pattern))
		}
	}
	if len(vals) == 0 {
		return ""
	}

	return groupConcatDistinct(vals)
}

func (g *Graph) defsInTree(name string) int32 {
	n := int32(0)
	for id := 0; id < g.nSym(); id++ {
		if g.Syms.scol(id, cNAME) != name {
			continue
		}
		switch g.Syms.scol(id, cKIND) {
		case "function", "method", "closure":
			n++
		}
	}
	return n
}

func (g *Graph) atLine(fid, line int32) string { return g.at(fid, line) }

func eachSym(g *Graph, ff fileFilter, mod string, fn func(id int)) {
	for id := 0; id < g.nSym(); id++ {
		fl := &g.Files[g.Syms.at(id, cFILEID)-1]
		if !ff.ok(fl) {
			continue
		}
		if !likeMatch(mod, g.modName(fl.moduleID)) {
			continue
		}
		fn(id)
	}
}

func isFnKind(k string) bool {
	return k == "function" || k == "method" || k == "closure"
}

func init() {
	queries[0].Run = q1
	queries[1].Run = q2
	queries[2].Run = q3
	queries[3].Run = q4
	queries[4].Run = q5
	queries[5].Run = q6
	queries[6].Run = q7
	queries[7].Run = q8
	queries[8].Run = q9
	queries[9].Run = q10
	queries[10].Run = q11
	queries[11].Run = q12
	queries[12].Run = q13
	queries[13].Run = q14
	queries[14].Run = q15
	queries[15].Run = q16
	queries[16].Run = q17
	queries[17].Run = q18
	queries[18].Run = q19
	queries[19].Run = q20
	queries[20].Run = q21
	queries[21].Run = q22
	queries[22].Run = q23
	queries[23].Run = q24
	queries[24].Run = q25
	queries[25].Run = q26
	queries[26].Run = q27
	queries[27].Run = q28
	queries[28].Run = q29
	queries[29].Run = q30
}

func q1(g *Graph, mod string, lim int) *Table {
	t := &Table{Cols: []string{"what", "api", "detail", "event", "target", "handler",
		"unremovable", "module_scope", "in_loop", "in_fn", "component",
		"effects_with_cleanup", "at"}}
	type row struct {
		what, api, detail, event, target, handler string
		unremovable, moduleScope, inLoop          int32
		symID                                     int32
		fileID, line                              int32
	}
	var rows []row
	for i := range g.Listeners {
		a := &g.Listeners[i]
		if a.Op(g) != "add" || a.signal {
			continue
		}
		fl := &g.Files[a.fileID-1]
		if fl.isTest || !likeMatch(mod, g.modName(fl.moduleID)) {
			continue
		}
		undone := false
		for j := range g.Listeners {
			r := &g.Listeners[j]
			if r.fileID != a.fileID || r.Op(g) != "remove" {
				continue
			}
			if r.Api(g) == "removeAllListeners" || r.Api(g) == "disconnect" ||
				(r.Handler(g) != "" && r.Handler(g) == a.Handler(g)) ||
				(r.Event(g) != "" && r.Event(g) == a.Event(g) && (r.Target(g) == a.Target(g) || r.Target(g) == "")) {
				undone = true
				break
			}
		}
		if undone {
			continue
		}
		rows = append(rows, row{"listener", a.Api(g), a.Family(g), a.Event(g),
			clip(a.Target(g), 20), clip(a.Handler(g), 24), b2i(a.inline),
			b2i(a.atModule), b2i(a.inLoop), a.symID, a.fileID, a.line})
	}
	for i := range g.Timers {
		x := &g.Timers[i]
		if x.Op(g) != "set" || x.unrefd {
			continue
		}
		if !(x.repeating || x.inLoop || x.atModule) {
			continue
		}
		fl := &g.Files[x.fileID-1]
		if fl.isTest || !likeMatch(mod, g.modName(fl.moduleID)) {
			continue
		}
		undone := false
		for j := range g.Timers {
			c := &g.Timers[j]
			if c.fileID != x.fileID || c.Op(g) != "clear" {
				continue
			}
			if c.Kind(g) == x.Kind(g) || c.Handle(g) == x.Handle(g) {
				undone = true
				break
			}
		}
		if undone {
			continue
		}
		rows = append(rows, row{"timer", x.Api(g), x.Kind(g), "", clip(x.Handle(g), 20), "",
			1 - b2i(x.assigned), b2i(x.atModule), b2i(x.inLoop), x.symID, x.fileID, x.line})
	}
	for _, r := range rows {
		inFn := "(module scope)"
		comp := int32(0)
		clean := int32(0)
		if r.symID != 0 && int(r.symID) <= g.nSym() {
			id := int(r.symID) - 1
			inFn = g.Syms.scol(id, cNAME)
			comp = g.Syms.at(id, cISCOMPONENT)

			for k := range g.Hooks {
				if g.Hooks[k].symID == r.symID && g.Hooks[k].cleanup {
					clean++
				}
			}
		}
		t.add(S(r.what), S(r.api), S(r.detail), S(r.event), S(r.target), S(r.handler),
			I32(r.unremovable), I32(r.moduleScope), I32(r.inLoop), S(inFn), I32(comp),
			I32(clean), S(g.at(r.fileID, r.line)))
	}
	t.take([]orderTerm{
		byIntDesc(func(i int) int { return int(t.Rows[i][6].i) }),
		byIntDesc(func(i int) int { return int(t.Rows[i][7].i) }),
		byIntDesc(func(i int) int { return int(t.Rows[i][8].i) }),
		byStr(func(i int) string { return t.Rows[i][0].s }),
		byStr(func(i int) string { return t.Rows[i][1].s }),
	}, lim)
	return t
}

func q2(g *Graph, mod string, lim int) *Table {
	t := &Table{Cols: []string{"name", "ctor", "const_", "exported", "writes", "drops",
		"reads", "size_checks", "writer_fns", "init_only", "io_in_file",
		"handlers_in_file", "at"}}
	for i := range g.Caches {
		c := &g.Caches[i]
		if c.nDrops != 0 || c.weak || c.nWrites <= 0 {
			continue
		}
		fl := &g.Files[c.fileID-1]
		if !fl.clean() || !likeMatch(mod, g.modName(fl.moduleID)) {
			continue
		}
		io, handlers := int32(0), int32(0)
		for _, id := range g.symsByFile[c.fileID] {
			v := g.Syms.at(int(id), cNSYNCCALLS) + g.Syms.at(int(id), cNNET) + g.Syms.at(int(id), cNIO)
			if v > io {
				io = v
			}
			if g.Syms.at(int(id), cISHANDLER) == 1 {
				handlers++
			}
		}

		nw := int32(sqlLen(c.Writers(g)) - sqlLen(stringsReplaceAll(c.Writers(g), ",")) + 1)
		initOnly := b2i(c.Writers(g) == "module")
		t.add(S(c.Name(g)), S(c.Ctor(g)), I32(b2i(c.konst)), I32(b2i(c.exported)),
			I32(c.nWrites), I32(c.nDrops), I32(c.nReads), I32(c.nSize), I32(nw),
			I32(initOnly), I32(io), I32(handlers), S(g.at(c.fileID, c.line)))
	}
	t.take([]orderTerm{
		byInt(func(i int) int { return int(t.Rows[i][9].i) }),
		byIntDesc(func(i int) int { return int(t.Rows[i][11].i) }),
		byIntDesc(func(i int) int { return int(t.Rows[i][4].i) }),
		byInt(func(i int) int { return int(t.Rows[i][7].i) }),
	}, lim)
	return t
}

func q3(g *Graph, mod string, lim int) *Table {
	t := &Table{Cols: []string{"entry", "blocks_in", "hops", "sync_calls",
		"sync_hazards", "exec_", "json_ops", "loop_depth", "io_in_loop", "fan_in",
		"patterns", "at"}}
	var entries []int32
	for id := 0; id < g.nSym(); id++ {
		if g.Syms.at(id, cISHANDLER) == 1 || g.Syms.at(id, cISENTRYPOINT) == 1 {
			entries = append(entries, int32(id+1))
		}
	}
	full := g.reachDown(entries, 4)

	for _, k := range sortedReachPairs(full.depth) {
		depth := full.depth[k]
		id := int(k.sym) - 1
		fl := &g.Files[g.Syms.at(id, cFILEID)-1]
		if !(g.Syms.at(id, cNSYNCCALLS) > 0 || g.Syms.at(id, cNEXEC) > 0) {
			continue
		}
		if fl.isTest || !likeMatch(mod, g.modName(fl.moduleID)) {
			continue
		}
		t.add(S(g.name(int(k.root)-1)), S(g.Syms.scol(id, cNAME)), I32(depth),
			I32(g.Syms.at(id, cNSYNCCALLS)), I32(g.Syms.at(id, cNSYNCBLOCK)),
			I32(g.Syms.at(id, cNEXEC)), I32(g.Syms.at(id, cNJSONPARSE)),
			I32(g.Syms.at(id, cMAXLOOPDEPTH)), I32(g.Syms.at(id, cIOINLOOP)),
			I32(g.Syms.at(id, cFANIN)),
			MaybeS(g.hazPatternList(k.sym, "sync_block", "exec")),
			S(g.atLine(fl.id, g.Syms.at(id, cLINESTART))))
	}
	t.take([]orderTerm{
		byInt(func(i int) int { return int(t.Rows[i][2].i) }),
		byIntDesc(func(i int) int { return int(t.Rows[i][5].i) }),
		byIntDesc(func(i int) int { return int(t.Rows[i][3].i) }),
	}, lim)
	return t
}

func q4(g *Graph, mod string, lim int) *Table {
	t := &Table{Cols: []string{"name", "class_", "awaits_in_loop", "awaits", "depth",
		"batches_anywhere", "calls_in_loop", "io_in_loop", "net_", "io_", "fan_in",
		"handler", "serial_cost", "at"}}
	eachSym(g, fNotTestGen, mod, func(id int) {
		aw := g.Syms.at(id, cAWAITINLOOP)
		if aw <= 0 || g.Syms.at(id, cNPROMISEALL) != 0 {
			return
		}

		nest := g.Syms.at(id, cMAXLOOPDEPTH)
		hd := g.Syms.at(id, cISHANDLER)
		cost := aw * (1 + nest) * (1 + hd*2)
		fid := g.Syms.at(id, cFILEID)
		t.add(S(g.Syms.scol(id, cNAME)), S(g.Syms.scol(id, cCLASSNAME)), I32(aw),
			I32(g.Syms.at(id, cNAWAIT)), I32(g.Syms.at(id, cMAXLOOPDEPTH)),
			I32(g.Syms.at(id, cNPROMISEALL)),
			I32(g.Syms.at(id, cCALLINLOOP)), I32(g.Syms.at(id, cIOINLOOP)),
			I32(g.Syms.at(id, cNNET)), I32(g.Syms.at(id, cNIO)),
			I32(g.Syms.at(id, cFANIN)), I32(hd), I32(cost),
			S(g.atLine(fid, g.Syms.at(id, cLINESTART))))
	})
	t.take([]orderTerm{
		byIntDesc(func(i int) int { return int(t.Rows[i][12].i) }),
		byIntDesc(func(i int) int { return int(t.Rows[i][2].i) }),
	}, lim)
	return t
}

func q5(g *Graph, mod string, lim int) *Table {
	t := &Table{Cols: []string{"async_callee", "caller", "caller_async", "caller_awaits",
		"discarded_calls", "then_chains", "catch_handlers", "callee_net", "callee_io",
		"callee_throws", "same_module", "callee_fan_in", "at"}}
	for i := range g.Edges {
		e := &g.Edges[i]
		if e.isSelf {
			continue
		}
		cal, cle := int(e.caller)-1, int(e.callee)-1
		if g.Syms.at(cle, cISASYNC) != 1 {
			continue
		}
		if g.Syms.at(cal, cNFLOATINGPROMISE) <= 0 || g.Syms.at(cal, cNAWAIT) != 0 ||
			g.Syms.at(cal, cNTHEN) != 0 {
			continue
		}
		fl := &g.Files[g.Syms.at(cal, cFILEID)-1]
		if !fl.clean() || !likeMatch(mod, g.modName(g.Syms.at(cal, cMODULEID))) {
			continue
		}
		t.add(S(g.Syms.scol(cle, cNAME)), S(g.Syms.scol(cal, cNAME)),
			I32(g.Syms.at(cal, cISASYNC)), I32(g.Syms.at(cal, cNAWAIT)),
			I32(g.Syms.at(cal, cNFLOATINGPROMISE)), I32(g.Syms.at(cal, cNTHEN)),
			I32(g.Syms.at(cal, cNCATCHHANDLER)), I32(g.Syms.at(cle, cNNET)),
			I32(g.Syms.at(cle, cNIO)), I32(g.Syms.at(cle, cNTHROW)),
			I32(b2i(e.sameMod)), I32(g.Syms.at(cle, cFANIN)),
			S(g.atLine(fl.id, g.Syms.at(cal, cLINESTART))))
	}
	take(t, lim, byIntDesc(func(i int) int {
		return int(t.Rows[i][7].i + t.Rows[i][8].i)
	}), byIntDesc(func(i int) int { return int(t.Rows[i][9].i) }),
		byIntDesc(func(i int) int { return int(t.Rows[i][11].i) }))
	return t
}

func q6(g *Graph, mod string, lim int) *Table {
	t := &Table{Cols: []string{"writer", "hops_from_input", "proto_writes",
		"dynamic_writes", "merge_calls", "recursive_", "computed_reads", "parses",
		"fan_in", "via", "at"}}
	var entries []int32
	for id := 0; id < g.nSym(); id++ {
		if g.Syms.at(id, cISHANDLER) == 1 || g.Syms.at(id, cNJSONPARSE) > 0 {
			entries = append(entries, int32(id+1))
		}
	}
	best := g.reachDownAll(entries, 4)
	for _, sym := range sortedIDs(best) {
		depth := best[sym]
		id := int(sym) - 1
		pw, dp, pp := g.Syms.at(id, cNPROTOWRITE), g.Syms.at(id, cNDYNAMICPROP), g.Syms.at(id, cNPROTOPOLLUTION)
		rec := g.Syms.at(id, cISRECURSIVE)
		if !(pw > 0 || pp > 0 || (dp > 0 && rec == 1)) {
			continue
		}
		fl := &g.Files[g.Syms.at(id, cFILEID)-1]
		if !fl.clean() || !likeMatch(mod, g.modName(g.Syms.at(id, cMODULEID))) {
			continue
		}
		t.add(S(g.Syms.scol(id, cNAME)), I32(depth), I32(pw), I32(dp), I32(pp),
			I32(rec), I32(g.Syms.at(id, cNCOMPUTEDMEMBER)),
			I32(g.Syms.at(id, cNJSONPARSE)), I32(g.Syms.at(id, cFANIN)),
			MaybeS(g.hazPatternList(sym, "proto_pollution")),
			S(g.atLine(fl.id, g.Syms.at(id, cLINESTART))))
	}
	take(t, lim, byInt(func(i int) int { return int(t.Rows[i][1].i) }),
		byIntDesc(func(i int) int { return int(t.Rows[i][5].i) }),
		byIntDesc(func(i int) int { return int(t.Rows[i][2].i) }))
	return t
}

func q7(g *Graph, mod string, lim int) *Table {
	t := &Table{Cols: []string{"in_fn", "hops_from_input", "pattern", "redos_in_fn",
		"regex_literals", "regex_in_loop", "regex_api_calls", "handler", "callers",
		"exported_in_file", "at"}}
	var entries []int32
	for id := 0; id < g.nSym(); id++ {
		if g.Syms.at(id, cISHANDLER) == 1 || g.Syms.at(id, cISENTRYPOINT) == 1 ||
			g.Syms.at(id, cNJSONPARSE) > 0 {
			entries = append(entries, int32(id+1))
		}
	}
	best := g.reachDownAll(entries, 4)
	for i := range g.Literals {
		l := &g.Literals[i]
		if l.Kind(g) != cKindRegexRedos {
			continue
		}
		fl := &g.Files[l.fileID-1]
		if fl.isGen || !likeMatch(mod, g.modName(fl.moduleID)) {
			continue
		}
		inFn, hops := "(module scope)", int32(-1)
		if l.symID != 0 && int(l.symID) <= g.nSym() {
			id := int(l.symID) - 1
			inFn = g.Syms.scol(id, cNAME)
			if d, ok := best[l.symID]; ok {
				hops = d
			}
		}
		col := func(c int) int32 {
			if l.symID == 0 || int(l.symID) > g.nSym() {
				return 0
			}
			return g.Syms.at(int(l.symID)-1, c)
		}
		exported := int32(0)
		for _, id := range g.symsByFile[l.fileID] {
			if g.Syms.at(int(id), cISEXPORTED) == 1 {
				exported++
			}
		}
		t.add(S(inFn), I32(hops), S(clip(l.Value(g), 40)),
			I32(col(cNREGEXREDOS)), I32(col(cNREGEXLIT)), I32(col(cREGEXINLOOP)),
			I32(col(cNREDOS)), I32(col(cISHANDLER)), I32(col(cFANIN)),
			I32(exported), S(g.at(l.fileID, l.line)))
	}
	take(t, lim,
		byInt(func(i int) int {
			if t.Rows[i][1].i < 0 {
				return 1
			}
			return 0
		}),
		byInt(func(i int) int { return int(t.Rows[i][1].i) }),
		byIntDesc(func(i int) int { return int(t.Rows[i][8].i) }))
	return t
}

func q8(g *Graph, mod string, lim int) *Table {
	t := &Table{Cols: []string{"entry", "sink_in", "hops", "html_writes", "dom_hazards",
		"storage_ops", "eval_", "component", "jsx", "dangerous_jsx", "fan_in", "at"}}
	var entries []int32
	for id := 0; id < g.nSym(); id++ {
		if g.Syms.at(id, cISHANDLER) == 1 || g.Syms.at(id, cNJSONPARSE) > 0 ||
			g.Syms.at(id, cISCOMPONENT) == 1 {
			entries = append(entries, int32(id+1))
		}
	}
	full := g.reachDown(entries, 4)
	for _, k := range sortedReachPairs(full.depth) {
		best := full.depth[k]
		sym := k.sym
		id := int(sym) - 1
		if !(g.Syms.at(id, cNINNERHTML) > 0 || g.Syms.at(id, cNDOM) > 0 || g.Syms.at(id, cNEVAL) > 0) {
			continue
		}
		fl := &g.Files[g.Syms.at(id, cFILEID)-1]
		if fl.isTest || !likeMatch(mod, g.modName(g.Syms.at(id, cMODULEID))) {
			continue
		}
		danger := int32(0)
		for i := range g.JSX {
			if g.JSX[i].symID == sym && g.JSX[i].danger {
				danger++
			}
		}
		t.add(S(g.name(int(k.root)-1)), S(g.Syms.scol(id, cNAME)), I32(best),
			I32(g.Syms.at(id, cNINNERHTML)), I32(g.Syms.at(id, cNDOM)),
			I32(g.Syms.at(id, cNSTORAGE)), I32(g.Syms.at(id, cNEVAL)),
			I32(g.Syms.at(id, cISCOMPONENT)), I32(g.Syms.at(id, cNJSXELEMENTS)),
			I32(danger), I32(g.Syms.at(id, cFANIN)),
			S(g.atLine(fl.id, g.Syms.at(id, cLINESTART))))
	}
	take(t, lim, byInt(func(i int) int { return int(t.Rows[i][2].i) }),
		byIntDesc(func(i int) int { return int(t.Rows[i][6].i) }),
		byIntDesc(func(i int) int { return int(t.Rows[i][3].i) }))
	return t
}

func q9(g *Graph, mod string, lim int) *Table {
	t := &Table{Cols: []string{"async_fn", "async_depth", "reaches_fns", "callers",
		"sync_callers", "sync_and_unchained", "own_awaits", "awaits_in_loop",
		"batches", "fan_in", "at"}}
	var entries []int32
	for id := 0; id < g.nSym(); id++ {
		if g.Syms.at(id, cISASYNC) == 1 && isFnKind(g.Syms.scol(id, cKIND)) {
			entries = append(entries, int32(id+1))
		}
	}

	maxDepth, subtree := g.reachDownMax(entries, 4)
	type acc struct {
		callers, syncCallers, syncUnchained map[int32]bool
	}
	agg := map[int32]*acc{}
	for i := range g.Edges {
		e := &g.Edges[i]
		if e.isSelf {
			continue
		}
		cle := int(e.callee) - 1
		if g.Syms.at(cle, cISASYNC) != 1 {
			continue
		}
		fl := &g.Files[g.Syms.at(cle, cFILEID)-1]
		if fl.isTest || !likeMatch(mod, g.modName(g.Syms.at(cle, cMODULEID))) {
			continue
		}
		a := agg[e.callee]
		if a == nil {
			a = &acc{map[int32]bool{}, map[int32]bool{}, map[int32]bool{}}
			agg[e.callee] = a
		}
		a.callers[e.caller] = true
		cal := int(e.caller) - 1
		if g.Syms.at(cal, cISASYNC) == 0 {
			a.syncCallers[e.caller] = true
			if g.Syms.at(cal, cNTHEN) == 0 {
				a.syncUnchained[e.caller] = true
			}
		}
	}
	for _, cle := range sortedIDs(agg) {
		a := agg[cle]
		if len(a.syncCallers) == 0 {
			continue
		}
		id := int(cle) - 1
		t.add(S(g.Syms.scol(id, cNAME)), I32(maxDepth[cle]), I32(subtree[cle]),
			I32(int32(len(a.callers))), I32(int32(len(a.syncCallers))), I32(int32(len(a.syncUnchained))),
			I32(g.Syms.at(id, cNAWAIT)), I32(g.Syms.at(id, cAWAITINLOOP)),
			I32(g.Syms.at(id, cNPROMISEALL)), I32(g.Syms.at(id, cFANIN)),
			S(g.atLine(g.Files[g.Syms.at(id, cFILEID)-1].id,
				g.Syms.at(id, cLINESTART))))
	}
	take(t, lim,
		byIntDesc(func(i int) int { return int(t.Rows[i][5].i) }),
		byIntDesc(func(i int) int { return int(t.Rows[i][2].i) }))
	return t
}

func q10(g *Graph, mod string, lim int) *Table {
	t := &Table{Cols: []string{"name", "class_", "timers_set", "timers_cleared",
		"repeating", "set_in_loop", "closures", "handler", "fan_in", "at"}}
	eachSym(g, fNotTest, mod, func(id int) {
		set, clr := g.Syms.at(id, cNTIMERSET), g.Syms.at(id, cNTIMERCLEAR)
		if set <= clr {
			return
		}
		fid := g.Syms.at(id, cFILEID)
		t.add(S(g.Syms.scol(id, cNAME)), S(g.Syms.scol(id, cCLASSNAME)), I32(set),
			I32(clr), I32(g.Syms.at(id, cNTIMERREPEATING)),
			I32(g.Syms.at(id, cNTIMERINLOOP)), I32(g.Syms.at(id, cNCLOSURES)),
			I32(g.Syms.at(id, cISHANDLER)), I32(g.Syms.at(id, cFANIN)),
			S(g.atLine(fid, g.Syms.at(id, cLINESTART))))
	})
	take(t, lim,
		byIntDesc(func(i int) int { return int(t.Rows[i][5].i) }),
		byIntDesc(func(i int) int { return int(t.Rows[i][4].i) }),
		byIntDesc(func(i int) int { return int(t.Rows[i][2].i - t.Rows[i][3].i) }))
	return t
}

func q11(g *Graph, mod string, lim int) *Table {
	t := &Table{Cols: []string{"name", "class_", "evals", "dyn_require", "dyn_import",
		"export_star", "json_parses", "unresolved", "fan_in", "at"}}
	eachSym(g, fNotTest, mod, func(id int) {
		ev, dr, di := g.Syms.at(id, cNEVAL), g.Syms.at(id, cNREQUIREDYNAMIC), g.Syms.at(id, cNIMPORTDYNAMIC)
		if ev+dr+di <= 0 {
			return
		}
		fid := g.Syms.at(id, cFILEID)
		t.add(S(g.Syms.scol(id, cNAME)), S(g.Syms.scol(id, cCLASSNAME)), I32(ev),
			I32(dr), I32(di), I32(g.Syms.at(id, cNEXPORTSTAR)),
			I32(g.Syms.at(id, cNJSONPARSE)), I32(g.Syms.at(id, cNUNRESOLVEDCALLS)),
			I32(g.Syms.at(id, cFANIN)), S(g.atLine(fid, g.Syms.at(id, cLINESTART))))
	})
	take(t, lim,
		byIntDesc(func(i int) int { return int(t.Rows[i][2].i) * 5 }),
		byIntDesc(func(i int) int { return int(t.Rows[i][3].i) }),
		byIntDesc(func(i int) int { return int(t.Rows[i][4].i) }))
	return t
}

func q12(g *Graph, mod string, lim int) *Table {
	t := &Table{Cols: []string{"name", "class_", "conditional_hooks", "hooks",
		"inline_props", "setstates", "jsx", "component", "is_hook_", "fan_in", "at"}}
	eachSym(g, fNotTest, mod, func(id int) {
		h, comp := g.Syms.at(id, cNHOOKS), g.Syms.at(id, cISCOMPONENT)
		if !(h > 0 || comp == 1) {
			return
		}
		fid := g.Syms.at(id, cFILEID)
		t.add(S(g.Syms.scol(id, cNAME)), S(g.Syms.scol(id, cCLASSNAME)),
			I32(g.Syms.at(id, cNHOOKSCONDITIONAL)), I32(h),
			I32(g.Syms.at(id, cNINLINEOBJECTPROP)), I32(g.Syms.at(id, cNSETSTATE)),
			I32(g.Syms.at(id, cNJSXELEMENTS)), I32(comp),
			I32(g.Syms.at(id, cISHOOK)), I32(g.Syms.at(id, cFANIN)),
			S(g.atLine(fid, g.Syms.at(id, cLINESTART))))
	})
	take(t, lim,
		byIntDesc(func(i int) int { return int(t.Rows[i][2].i) }),
		byIntDesc(func(i int) int { return int(t.Rows[i][4].i) }),
		byIntDesc(func(i int) int { return int(t.Rows[i][5].i) }))
	return t
}

func q13(g *Graph, mod string, lim int) *Table {
	t := &Table{Cols: []string{"name", "kind", "sloc", "cyclo", "ext_calls", "at"}}
	eachSym(g, fNotTestGen, mod, func(id int) {
		if g.Syms.at(id, cFANIN) != 0 || g.Syms.at(id, cISPUBLIC) != 0 ||
			g.Syms.at(id, cISTEST) != 0 || g.Syms.at(id, cISENTRYPOINT) != 0 ||
			g.Syms.at(id, cISOVERRIDE) != 0 || g.Syms.at(id, cISABSTRACT) != 0 {
			return
		}
		if !isFnKind(g.Syms.scol(id, cKIND)) {
			return
		}
		nm := g.Syms.scol(id, cNAME)
		if nm == "(anonymous)" || nm == "<module>" {
			return
		}
		fid := g.Syms.at(id, cFILEID)
		t.add(S(nm), S(g.Syms.scol(id, cKIND)), I32(g.Syms.at(id, cSLOC)),
			I32(g.Syms.at(id, cCYCLOMATIC)), I32(g.Syms.at(id, cNEXTERNALCALLS)),
			S(g.atLine(fid, g.Syms.at(id, cLINESTART))))
	})
	take(t, lim, byIntDesc(func(i int) int { return int(t.Rows[i][2].i) }))
	return t
}

func q14(g *Graph, mod string, lim int) *Table {
	t := &Table{Cols: []string{"name", "reached_from", "hops", "sync_fs_calls",
		"child_process_calls", "json_parse_in_loop", "callee_is_async", "fan_in", "at"}}
	var entries []int32
	for id := 0; id < g.nSym(); id++ {
		fl := &g.Files[g.Syms.at(id, cFILEID)-1]
		if fl.isTest {
			continue
		}
		if g.Syms.at(id, cISHANDLER) == 1 || g.Syms.at(id, cISENTRYPOINT) == 1 ||
			g.Syms.at(id, cISEXPORTED) == 1 {
			entries = append(entries, int32(id+1))
		}
	}
	full := g.reachDown(entries, 4)
	best := map[rootSym]int32{}
	for k, v := range full.depth {
		pk := rootSym{k.root, k.sym}
		if old, ok := best[pk]; !ok || v < old {
			best[pk] = v
		}
	}
	for _, p := range sortedPairs(best) {
		id := int(p.sym) - 1
		if best[p] <= 0 {
			continue
		}
		fs, cp := g.Syms.at(id, cNFSSYNC), g.Syms.at(id, cNCHILDPROCESS)
		if !(fs > 0 || cp > 0) {
			continue
		}
		fl := &g.Files[g.Syms.at(id, cFILEID)-1]
		if fl.isTest || !likeMatch(mod, g.modName(g.Syms.at(id, cMODULEID))) {
			continue
		}
		t.add(S(g.Syms.scol(id, cNAME)), S(g.name(int(p.root)-1)), I32(best[p]), I32(fs),
			I32(cp), I32(g.Syms.at(id, cNJSONPARSEINLOOP)),
			I32(g.Syms.at(id, cISASYNC)), I32(g.Syms.at(id, cFANIN)),
			S(g.atLine(fl.id, g.Syms.at(id, cLINESTART))))
	}
	take(t, lim, byInt(func(i int) int { return int(t.Rows[i][2].i) }),
		byIntDesc(func(i int) int { return int(t.Rows[i][3].i) }),
		byIntDesc(func(i int) int { return int(t.Rows[i][7].i) }))
	return t
}

func simpleSym(g *Graph, mod string, lim int, cols []string, ff fileFilter,
	keep func(id int) bool, emit func(t *Table, id int), terms func(t *Table) []orderTerm) *Table {
	t := &Table{Cols: cols}
	eachSym(g, ff, mod, func(id int) {
		if keep != nil && !keep(id) {
			return
		}
		emit(t, id)
	})
	t.take(terms(t), lim)
	return t
}

func q15(g *Graph, mod string, lim int) *Table {
	return simpleSym(g, mod, lim,
		[]string{"name", "child_process_calls", "eval_calls", "dynamic_requires",
			"fan_in", "handler", "at"}, fNotTest,
		func(id int) bool { return g.Syms.at(id, cNCHILDPROCESS) > 0 },
		func(t *Table, id int) {
			fid := g.Syms.at(id, cFILEID)
			t.add(S(g.Syms.scol(id, cNAME)), I32(g.Syms.at(id, cNCHILDPROCESS)),
				I32(g.Syms.at(id, cNEVAL)), I32(g.Syms.at(id, cNREQUIREDYNAMIC)),
				I32(g.Syms.at(id, cFANIN)), I32(g.Syms.at(id, cISHANDLER)),
				S(g.atLine(fid, g.Syms.at(id, cLINESTART))))
		},
		func(t *Table) []orderTerm {
			return []orderTerm{
				byIntDesc(func(i int) int { return int(t.Rows[i][4].i) }),
				byIntDesc(func(i int) int { return int(t.Rows[i][1].i) })}
		})
}

func inputSurface(g *Graph, mod string, lim int, cols []string, ff fileFilter,
	pred func(id int) bool, withFormsOnly bool, measureCell func(id int) Cell,
	withFanIn bool, terms func(t *Table) []orderTerm) *Table {
	t := &Table{Cols: cols}
	eachSym(g, ff, mod, func(id int) {
		if !pred(id) {
			return
		}
		sid := int32(id + 1)
		var n int32
		var kinds Cell
		if withFormsOnly {
			n = int32(g.formReads(sid))
			if n == 0 {
				return
			}
			kinds = Null()
		} else {
			cnt, ks := g.kindsOf(sid)
			if cnt == 0 {
				return
			}
			n = int32(cnt)
			kinds = MaybeS(ks)
		}
		fid := g.Syms.at(id, cFILEID)
		row := []Cell{S(g.Syms.scol(id, cNAME)), measureCell(id), I32(n), kinds}
		if withFanIn {
			row = append(row, I32(g.Syms.at(id, cFANIN)))
		}
		row = append(row, S(g.atLine(fid, g.Syms.at(id, cLINESTART))))
		t.add(row...)
	})
	t.take(terms(t), lim)
	return t
}

func q16(g *Graph, mod string, lim int) *Table {
	return inputSurface(g, mod, lim,
		[]string{"name", "redirect_writes", "input_sites", "kinds", "fan_in", "at"},
		fNotTest,
		func(id int) bool { return g.Syms.at(id, cNREDIRECT) > 0 }, false,
		func(id int) Cell { return I32(g.Syms.at(id, cNREDIRECT)) },
		true,
		func(t *Table) []orderTerm {
			return []orderTerm{
				byIntDesc(func(i int) int { return int(t.Rows[i][4].i) }),
				byIntDesc(func(i int) int { return int(t.Rows[i][1].i) })}
		})
}

func q17(g *Graph, mod string, lim int) *Table {
	return inputSurface(g, mod, lim,
		[]string{"name", "fetch_calls", "input_sites", "kinds", "at"},
		fNotTest,
		func(id int) bool { return g.Syms.at(id, cNFETCH) > 0 }, false,
		func(id int) Cell { return I32(g.Syms.at(id, cNFETCH)) },
		false,
		func(t *Table) []orderTerm {
			return []orderTerm{
				byIntDesc(func(i int) int { return int(t.Rows[i][1].i) }),
				byIntDesc(func(i int) int { return int(t.Rows[i][2].i) })}
		})
}

func q18(g *Graph, mod string, lim int) *Table {
	t := &Table{Cols: []string{"name", "candidate", "line", "at"}}
	for i := range g.Secrets {
		sc := &g.Secrets[i]
		if sc.symID == 0 || int(sc.symID) > g.nSym() {
			continue
		}
		id := int(sc.symID) - 1
		fl := &g.Files[sc.fileID-1]
		if fl.isTest || !likeMatch(mod, g.modName(g.Syms.at(id, cMODULEID))) {
			continue
		}
		if likeMatch("/%", sc.Value(g)) || instr(sc.Value(g), "|") != 0 || instr(sc.Value(g), "%") != 0 {
			continue
		}
		t.add(S(g.Syms.scol(id, cNAME)), S(sc.Value(g)), I32(sc.line),
			S(g.at(sc.fileID, sc.line)))
	}
	take(t, lim, byIntDesc(func(i int) int { return sqlLen(t.Rows[i][1].s) }))
	return t
}

func q19(g *Graph, mod string, lim int) *Table {
	return inputSurface(g, mod, lim,
		[]string{"name", "open_sites", "input_sites", "kinds", "at"},
		fNotTest,
		func(id int) bool { return g.Syms.at(id, cNDYNAMICOPEN) > 0 }, false,
		func(id int) Cell { return I32(g.Syms.at(id, cNDYNAMICOPEN)) },
		false,
		func(t *Table) []orderTerm {
			return []orderTerm{
				byIntDesc(func(i int) int { return int(t.Rows[i][1].i) }),
				byIntDesc(func(i int) int { return int(t.Rows[i][2].i) })}
		})
}

func q20(g *Graph, mod string, lim int) *Table {
	return inputSurface(g, mod, lim,
		[]string{"name", "save_calls", "form_reads", "at"},
		fNotTest,
		func(id int) bool { return g.Syms.at(id, cNUPLOADSAVE) > 0 }, true,
		func(id int) Cell { return I32(g.Syms.at(id, cNUPLOADSAVE)) },
		false,
		func(t *Table) []orderTerm {
			return []orderTerm{
				byIntDesc(func(i int) int { return int(t.Rows[i][1].i) }),
				byIntDesc(func(i int) int { return int(t.Rows[i][2].i) })}
		})
}

func q21(g *Graph, mod string, lim int) *Table {
	return simpleSym(g, mod, lim,
		[]string{"name", "zip_access", "sloc", "at"}, fNotTest,
		func(id int) bool { return g.Syms.at(id, cNZIPREAD) > 0 },
		func(t *Table, id int) {
			fid := g.Syms.at(id, cFILEID)
			t.add(S(g.Syms.scol(id, cNAME)), I32(g.Syms.at(id, cNZIPREAD)),
				I32(g.Syms.at(id, cSLOC)),
				S(g.atLine(fid, g.Syms.at(id, cLINESTART))))
		},
		func(t *Table) []orderTerm {
			return []orderTerm{
				byIntDesc(func(i int) int { return int(t.Rows[i][1].i) }),
				byIntDesc(func(i int) int { return int(t.Rows[i][2].i) })}
		})
}

func q22(g *Graph, mod string, lim int) *Table {
	return inputSurface(g, mod, lim,
		[]string{"name", "assigns", "input_sites", "kinds", "at"},
		fNotTest,
		func(id int) bool { return g.Syms.at(id, cNMASSASSIGN) > 0 }, false,
		func(id int) Cell { return I32(g.Syms.at(id, cNMASSASSIGN)) },
		false,
		func(t *Table) []orderTerm {
			return []orderTerm{
				byIntDesc(func(i int) int { return int(t.Rows[i][1].i) }),
				byIntDesc(func(i int) int { return int(t.Rows[i][2].i) })}
		})
}

func q23(g *Graph, mod string, lim int) *Table {
	return inputSurface(g, mod, lim,
		[]string{"name", "log_calls", "input_sites", "kinds", "at"},
		fNotTest,
		func(id int) bool { return g.Syms.at(id, cNLOGCALL) > 0 }, false,
		func(id int) Cell { return I32(g.Syms.at(id, cNLOGCALL)) },
		false,
		func(t *Table) []orderTerm {
			return []orderTerm{
				byIntDesc(func(i int) int { return int(t.Rows[i][1].i) }),
				byIntDesc(func(i int) int { return int(t.Rows[i][2].i) })}
		})
}

func q24(g *Graph, mod string, lim int) *Table {
	return inputSurface(g, mod, lim,
		[]string{"name", "console_calls", "input_sites", "kinds", "at"},
		fNotTest,
		func(id int) bool { return g.Syms.at(id, cNCONSOLELOG) > 0 }, false,
		func(id int) Cell { return I32(g.Syms.at(id, cNCONSOLELOG)) },
		false,
		func(t *Table) []orderTerm {
			return []orderTerm{
				byIntDesc(func(i int) int { return int(t.Rows[i][1].i) }),
				byIntDesc(func(i int) int { return int(t.Rows[i][2].i) })}
		})
}

func q25(g *Graph, mod string, lim int) *Table {
	t := &Table{Cols: []string{"name", "input_sites", "kinds", "at"}}

	var sloc []int32
	eachSym(g, fNotTest, mod, func(id int) {
		if g.Syms.at(id, cNAUTHCALL) != 0 {
			return
		}
		cnt, kinds := g.kindsOf(int32(id + 1))
		if cnt == 0 {
			return
		}
		fid := g.Syms.at(id, cFILEID)
		sloc = append(sloc, g.Syms.at(id, cSLOC))
		t.add(S(g.Syms.scol(id, cNAME)), I32(int32(cnt)), MaybeS(kinds),
			S(g.atLine(fid, g.Syms.at(id, cLINESTART))))
	})
	take(t, lim,
		byIntDesc(func(i int) int { return int(t.Rows[i][1].i) }),
		byIntDesc(func(i int) int { return int(sloc[i]) }))
	return t
}

func q26(g *Graph, mod string, lim int) *Table {
	return simpleSym(g, mod, lim,
		[]string{"name", "proto_writes", "proto_mutates", "deletes", "fan_in",
			"handler", "at"}, fNotTest,
		func(id int) bool {
			return g.Syms.at(id, cNPROTOWRITE) > 0 || g.Syms.at(id, cNPROTOMUTATE) > 0
		},
		func(t *Table, id int) {
			fid := g.Syms.at(id, cFILEID)
			t.add(S(g.Syms.scol(id, cNAME)), I32(g.Syms.at(id, cNPROTOWRITE)),
				I32(g.Syms.at(id, cNPROTOMUTATE)), I32(g.Syms.at(id, cNDELETE)),
				I32(g.Syms.at(id, cFANIN)), I32(g.Syms.at(id, cISHANDLER)),
				S(g.atLine(fid, g.Syms.at(id, cLINESTART))))
		},
		func(t *Table) []orderTerm {
			return []orderTerm{
				byIntDesc(func(i int) int { return int(t.Rows[i][4].i) }),
				byIntDesc(func(i int) int { return int(t.Rows[i][1].i) })}
		})
}

func q27(g *Graph, mod string, lim int) *Table {
	t := &Table{Cols: []string{"name", "exit_calls", "hops_from_handler", "fan_in",
		"cyclo", "at"}}
	var entries []int32
	for id := 0; id < g.nSym(); id++ {
		if g.Syms.at(id, cISHANDLER) == 1 {
			entries = append(entries, int32(id+1))
		}
	}
	full := g.reachDown(entries, 4)
	best := map[int32]int32{}
	for k, v := range full.depth {
		if old, ok := best[k.sym]; !ok || v < old {
			best[k.sym] = v
		}
	}
	for _, sym := range sortedIDs(best) {
		depth := best[sym]
		id := int(sym) - 1
		if g.Syms.at(id, cNPROCESSEXIT) <= 0 {
			continue
		}
		fl := &g.Files[g.Syms.at(id, cFILEID)-1]
		if fl.isTest || !likeMatch(mod, g.modName(g.Syms.at(id, cMODULEID))) {
			continue
		}
		t.add(S(g.Syms.scol(id, cNAME)), I32(g.Syms.at(id, cNPROCESSEXIT)),
			I32(depth), I32(g.Syms.at(id, cFANIN)), I32(g.Syms.at(id, cCYCLOMATIC)),
			S(g.atLine(fl.id, g.Syms.at(id, cLINESTART))))
	}
	take(t, lim, byInt(func(i int) int { return int(t.Rows[i][2].i) }),
		byIntDesc(func(i int) int { return int(t.Rows[i][1].i) }))
	return t
}

func q28(g *Graph, mod string, lim int) *Table {
	t := &Table{Cols: []string{"name", "sync_io", "sync_calls", "hops_from_handler", "at"}}
	var entries []int32
	for id := 0; id < g.nSym(); id++ {
		if g.Syms.at(id, cISHANDLER) == 1 {
			entries = append(entries, int32(id+1))
		}
	}
	full := g.reachDown(entries, 4)
	best := map[int32]int32{}
	for k, v := range full.depth {
		if old, ok := best[k.sym]; !ok || v < old {
			best[k.sym] = v
		}
	}
	for _, sym := range sortedIDs(best) {
		depth := best[sym]
		id := int(sym) - 1
		if g.Syms.at(id, cNFSSYNC) <= 0 {
			continue
		}
		fl := &g.Files[g.Syms.at(id, cFILEID)-1]
		if fl.isTest || !likeMatch(mod, g.modName(g.Syms.at(id, cMODULEID))) {
			continue
		}
		t.add(S(g.Syms.scol(id, cNAME)), I32(g.Syms.at(id, cNFSSYNC)),
			I32(g.Syms.at(id, cNSYNCCALLS)), I32(depth),
			S(g.atLine(fl.id, g.Syms.at(id, cLINESTART))))
	}
	take(t, lim,
		byIntDesc(func(i int) int { return int(t.Rows[i][1].i) }),
		byIntDesc(func(i int) int { return int(t.Rows[i][4].i) }))
	return t
}

func q29(g *Graph, mod string, lim int) *Table {
	t := &Table{Cols: []string{"path", "shortest_cycle", "at"}}
	byFile := map[int32][]int32{}
	for i := range g.Imports {
		im := &g.Imports[i]
		if im.targetID == 0 || im.isExternal != 0 {
			continue
		}
		byFile[im.fileID] = append(byFile[im.fileID], im.targetID)
	}
	best := map[int32]int32{}
	for i := range g.Files {
		f := &g.Files[i]
		if f.isTest {
			continue
		}
		best[f.id] = -1
		type fr struct {
			cur   int32
			depth int32
		}
		queue := []fr{{f.id, 0}}
		seen := map[int32]bool{f.id: true}
		for qi := 0; qi < len(queue); qi++ {
			cur := queue[qi]
			if cur.depth >= 8 {
				continue
			}
			for _, t := range byFile[cur.cur] {
				if t == f.id {
					if best[f.id] < 0 || cur.depth+1 < best[f.id] {
						best[f.id] = cur.depth + 1
					}
					continue
				}
				if !seen[t] {
					seen[t] = true
					queue = append(queue, fr{t, cur.depth + 1})
				}
			}
		}
	}
	for i := range g.Files {
		f := &g.Files[i]
		d := best[f.id]
		if d <= 0 {
			continue
		}
		t.add(S(f.Path(g)), I32(d), S(f.Path(g)+":0"))
	}
	take(t, lim, byInt(func(i int) int { return int(t.Rows[i][1].i) }))
	return t
}

func q30(g *Graph, mod string, lim int) *Table {
	return simpleSym(g, mod, lim,
		[]string{"name", "dynamic_requires", "dynamic_imports", "eval_calls",
			"exec_calls", "fan_in", "handler", "at"}, fNotTest,
		func(id int) bool { return g.Syms.at(id, cNREQUIREDYNAMIC) > 0 },
		func(t *Table, id int) {
			fid := g.Syms.at(id, cFILEID)
			t.add(S(g.Syms.scol(id, cNAME)), I32(g.Syms.at(id, cNREQUIREDYNAMIC)),
				I32(g.Syms.at(id, cNIMPORTDYNAMIC)), I32(g.Syms.at(id, cNEVAL)),
				I32(g.Syms.at(id, cNCHILDPROCESS)), I32(g.Syms.at(id, cFANIN)),
				I32(g.Syms.at(id, cISHANDLER)),
				S(g.atLine(fid, g.Syms.at(id, cLINESTART))))
		},
		func(t *Table) []orderTerm {
			return []orderTerm{
				byIntDesc(func(i int) int { return int(t.Rows[i][5].i) }),
				byIntDesc(func(i int) int { return int(t.Rows[i][1].i) })}
		})
}

func take(t *Table, lim int, terms ...orderTerm) {
	t.take(terms, lim)
}

func stringsReplaceAll(s, old string) string {
	out := ""
	for {
		i := indexOf(s, old)
		if i < 0 {
			return out + s
		}
		out += s[:i]
		s = s[i+len(old):]
	}
}

func indexOf(s, sub string) int {
	n := 0
	for i := 0; i+len(sub) <= len(s); i++ {
		if s[i:i+len(sub)] == sub {
			return i
		}
		_ = n
		n++
	}
	return -1
}

func init() {
	for i, f := range []func(*Graph, string, int) *Table{
		q31, q32, q33, q34, q35, q36, q37, q38, q39, q40, q41, q42, q43, q44, q45,
		q46, q47, q48, q49, q50, q51, q52, q53, q54, q55, q56, q57, q58, q59, q60} {
		queries[30+i].Run = f
	}
}

func q31(g *Graph, mod string, lim int) *Table {
	t := &Table{Cols: []string{"path", "anon_closures", "distinct_names", "sloc"}}
	for fid := int32(1); int(fid) <= len(g.Files); fid++ {
		f := &g.Files[fid-1]
		if f.isTest || !likeMatch(mod, g.modName(f.moduleID)) {
			continue
		}
		anon, distinct := int32(0), map[string]bool{}
		for _, id := range g.symsByFile[fid] {
			nm := g.Syms.scol(int(id), cNAME)
			distinct[nm] = true
			if nm == "(anonymous)" && isFnKind(g.Syms.scol(int(id), cKIND)) {
				anon++
			}
		}
		if anon == 0 {
			continue
		}
		t.add(S(g.s(f.path)), I32(anon), I32(int32(len(distinct))), I32(f.sloc))
	}
	take(t, lim,
		byIntDesc(func(i int) int { return int(t.Rows[i][1].i) }),
		byIntDesc(func(i int) int { return int(t.Rows[i][3].i) }))
	return t
}

func q32(g *Graph, mod string, lim int) *Table {
	t := &Table{Cols: []string{"path", "default_imports", "ns_imports", "named_imports",
		"pct_named"}}
	perFile := map[int32]*[4]int64{}
	var order []int32
	for i := range g.ImportNames {
		n := &g.ImportNames[i]
		p := perFile[n.fileID]
		if p == nil {
			p = &[4]int64{}
			perFile[n.fileID] = p
			order = append(order, n.fileID)
		}
		p[0]++
		switch {
		case n.def:
			p[1]++
		case n.ns:
			p[2]++
		default:
			p[3]++
		}
	}
	for _, fid := range order {
		f := &g.Files[fid-1]
		if f.isTest || !likeMatch(mod, g.modName(f.moduleID)) {
			continue
		}
		p := perFile[fid]
		pct := int64(0)
		if p[0] != 0 {
			pct = int64(100.0 * float64(p[3]) / float64(p[0]))
		}
		t.add(S(g.s(f.path)), I64(p[1]), I64(p[2]), I64(p[3]), I64(pct))
	}
	take(t, lim,
		byIntDesc(func(i int) int { return int(t.Rows[i][4].i) }),
		byIntDesc(func(i int) int { return int(t.Rows[i][3].i) }))
	return t
}

func q33(g *Graph, mod string, lim int) *Table {
	t := &Table{Cols: []string{"path", "max_up", "deep_imports"}}
	perFile := map[int32]*[2]int64{}
	var order []int32
	for i := range g.Imports {
		im := &g.Imports[i]

		up := int64(sqlLen(im.Target(g))-sqlLen(strings.ReplaceAll(im.Target(g), "../", ""))) / 3
		if up <= 0 {
			continue
		}
		p := perFile[im.fileID]
		if p == nil {
			p = &[2]int64{}
			perFile[im.fileID] = p
			order = append(order, im.fileID)
		}
		if up > p[0] {
			p[0] = up
		}
		if instr(im.Target(g), "../") > 0 {
			p[1]++
		}
	}
	for _, fid := range order {
		f := &g.Files[fid-1]
		if f.isTest || !likeMatch(mod, g.modName(f.moduleID)) {
			continue
		}
		t.add(S(g.s(f.path)), I64(perFile[fid][0]), I64(perFile[fid][1]))
	}
	take(t, lim,
		byIntDesc(func(i int) int { return int(t.Rows[i][1].i) }),
		byIntDesc(func(i int) int { return int(t.Rows[i][2].i) }))
	return t
}

func q34(g *Graph, mod string, lim int) *Table {
	return simpleSym(g, mod, lim,
		[]string{"name", "global_writes", "kind", "sloc", "at"}, fNotTest,
		func(id int) bool { return g.Syms.at(id, cNGLOBALWRITE) > 0 },
		func(t *Table, id int) {
			fid := g.Syms.at(id, cFILEID)
			t.add(S(g.Syms.scol(id, cNAME)), I32(g.Syms.at(id, cNGLOBALWRITE)),
				S(g.Syms.scol(id, cKIND)), I32(g.Syms.at(id, cSLOC)),
				S(g.atLine(fid, g.Syms.at(id, cLINESTART))))
		},
		func(t *Table) []orderTerm {
			return []orderTerm{
				byIntDesc(func(i int) int { return int(t.Rows[i][1].i) }),
				byIntDesc(func(i int) int { return int(t.Rows[i][3].i) })}
		})
}

func q35(g *Graph, mod string, lim int) *Table {
	t := &Table{Cols: []string{"barrel", "n_reexports", "from_files", "symbols_",
		"first_line"}}
	type acc struct {
		n     int64
		srcs  map[int32]bool
		names []string
		first int32
	}
	per := map[int32]*acc{}
	var order []int32
	for i := range g.Exports {
		e := &g.Exports[i]
		if !e.reexport {
			continue
		}
		a := per[e.fileID]
		if a == nil {
			a = &acc{srcs: map[int32]bool{}, first: e.line}
			per[e.fileID] = a
			order = append(order, e.fileID)
		}
		a.n++
		if e.sourceID != 0 {

			a.srcs[e.sourceID] = true
		}
		a.names = append(a.names, e.Name(g))
		if e.line < a.first {
			a.first = e.line
		}
	}
	for _, fid := range order {
		f := &g.Files[fid-1]
		if f.isTest || !likeMatch(mod, g.modName(f.moduleID)) {
			continue
		}
		a := per[fid]
		t.add(S(g.s(f.path)), I64(a.n), I64(int64(len(a.srcs))),
			S(groupConcatDistinctOrder(a.names)), I32(a.first))
	}
	take(t, lim,
		byIntDesc(func(i int) int { return int(t.Rows[i][1].i) }),
		byIntDesc(func(i int) int { return int(t.Rows[i][2].i) }))
	return t
}

func q36(g *Graph, mod string, lim int) *Table {
	t := &Table{Cols: []string{"path", "name", "then_sites", "handlers", "fan_in",
		"async_fn", "sloc"}}
	eachSym(g, fNotTestGen, mod, func(id int) {
		th := g.Syms.at(id, cNTHEN)
		if th <= 0 || g.Syms.at(id, cNCATCHHANDLER) != 0 {
			return
		}
		fid := g.Syms.at(id, cFILEID)
		t.add(S(g.filePath(fid)), S(g.Syms.scol(id, cNAME)), I32(th),
			I32(0), I32(g.Syms.at(id, cFANIN)), I32(g.Syms.at(id, cISASYNC)),
			I32(g.Syms.at(id, cSLOC)))
	})
	take(t, lim,
		byIntDesc(func(i int) int { return int(t.Rows[i][2].i) }),
		byIntDesc(func(i int) int { return int(t.Rows[i][4].i) }))
	return t
}

func q37(g *Graph, mod string, lim int) *Table {
	t := &Table{Cols: []string{"path", "name", "searches_in_loop", "loops", "fan_in", "at"}}
	eachSym(g, fNotTest, mod, func(id int) {
		if g.Syms.at(id, cNSEARCHINLOOP) <= 0 {
			return
		}
		fid := g.Syms.at(id, cFILEID)
		t.add(S(g.filePath(fid)), S(g.Syms.scol(id, cNAME)),
			I32(g.Syms.at(id, cNSEARCHINLOOP)), I32(g.Syms.at(id, cNLOOPS)),
			I32(g.Syms.at(id, cFANIN)),
			S(g.atLine(fid, g.Syms.at(id, cLINESTART))))
	})
	take(t, lim,
		byIntDesc(func(i int) int { return int(t.Rows[i][2].i) }),
		byIntDesc(func(i int) int { return int(t.Rows[i][4].i) }))
	return t
}

func q38(g *Graph, mod string, lim int) *Table {
	t := &Table{Cols: []string{"path", "name", "dynamic_writes", "proto_writes",
		"fan_in", "at"}}
	eachSym(g, fNotTest, mod, func(id int) {
		if g.Syms.at(id, cNDYNAMICPROP) <= 0 {
			return
		}
		fid := g.Syms.at(id, cFILEID)
		t.add(S(g.filePath(fid)), S(g.Syms.scol(id, cNAME)),
			I32(g.Syms.at(id, cNDYNAMICPROP)), I32(g.Syms.at(id, cNPROTOWRITE)),
			I32(g.Syms.at(id, cFANIN)),
			S(g.atLine(fid, g.Syms.at(id, cLINESTART))))
	})
	take(t, lim,
		byIntDesc(func(i int) int { return int(t.Rows[i][2].i) }),
		byIntDesc(func(i int) int { return int(t.Rows[i][4].i) }))
	return t
}

func q39(g *Graph, mod string, lim int) *Table {
	t := &Table{Cols: []string{"path", "name", "dup_conds", "cyclo", "fan_in", "at"}}
	eachSym(g, fNotTest, mod, func(id int) {
		if g.Syms.at(id, cNDUPCOND) <= 0 {
			return
		}
		fid := g.Syms.at(id, cFILEID)
		t.add(S(g.filePath(fid)), S(g.Syms.scol(id, cNAME)),
			I32(g.Syms.at(id, cNDUPCOND)), I32(g.Syms.at(id, cCYCLOMATIC)),
			I32(g.Syms.at(id, cFANIN)),
			S(g.atLine(fid, g.Syms.at(id, cLINESTART))))
	})
	take(t, lim,
		byIntDesc(func(i int) int { return int(t.Rows[i][2].i) }),
		byIntDesc(func(i int) int { return int(t.Rows[i][4].i) }))
	return t
}

func q40(g *Graph, mod string, lim int) *Table {
	t := &Table{Cols: []string{"name", "version", "is_dev", "used"}}
	if len(g.Deps) == 0 {
		return t
	}
	byPrefix := make([][]int32, len(g.Deps))
	for i := range byPrefix {
		byPrefix[i] = nil
	}
	for i := range g.Imports {
		tgt := g.Imports[i].Target(g)
		for d := range g.Deps {
			name := g.Deps[d].Name(g)
			if tgt == name {
				byPrefix[d] = append(byPrefix[d], int32(i))
			} else if strings.HasPrefix(tgt, name+"/") && tgt < name+"/\xff" {
				byPrefix[d] = append(byPrefix[d], int32(i))
			}
		}
	}
	for d := range g.Deps {
		if len(byPrefix[d]) > 0 {
			continue
		}
		t.add(S(g.Deps[d].Name(g)), S(g.Deps[d].Version(g)), I32(g.Deps[d].dev), I(0))
	}
	take(t, lim,
		byInt(func(i int) int { return int(t.Rows[i][2].i) }),
		byStr(func(i int) string { return t.Rows[i][0].s }))
	return t
}

func q41(g *Graph, mod string, lim int) *Table {
	t := &Table{Cols: []string{"from_file", "to_file", "line", "target"}}
	has := func(dir, part string) bool {
		return strings.Contains("/"+dir+"/", part)
	}
	for i := range g.Imports {
		im := &g.Imports[i]
		if im.targetID == 0 {
			continue
		}
		fc := &g.Files[im.fileID-1]
		ft := &g.Files[im.targetID-1]
		if fc.id == ft.id {
			continue
		}
		if !(has(fc.Dir(g), "/routes/") || has(fc.Dir(g), "/views/") || has(fc.Dir(g), "/pages/")) {
			continue
		}
		if !(has(ft.Dir(g), "/db/") || has(ft.Dir(g), "/api/") || has(ft.Dir(g), "/server/")) {
			continue
		}
		if !likeMatch(mod, g.modName(fc.moduleID)) {
			continue
		}
		t.add(S(fc.Path(g)), S(ft.Path(g)), I32(im.line), S(im.Target(g)))
	}
	take(t, lim,
		byStr(func(i int) string { return t.Rows[i][0].s }),
		byInt(func(i int) int { return int(t.Rows[i][2].i) }))
	return t
}

func q42(g *Graph, mod string, lim int) *Table {
	return simpleSym(g, mod, lim,
		[]string{"name", "empty_catches", "silent_catches", "try_blocks", "throws_",
			"fan_in", "handler", "at"}, fNotTestGen,
		func(id int) bool {
			return g.Syms.at(id, cNCATCHEMPTY) > 0 || g.Syms.at(id, cNCATCHBROAD) > 0
		},
		func(t *Table, id int) {
			fid := g.Syms.at(id, cFILEID)
			t.add(S(g.Syms.scol(id, cNAME)), I32(g.Syms.at(id, cNCATCHEMPTY)),
				I32(g.Syms.at(id, cNCATCHBROAD)), I32(g.Syms.at(id, cNTRY)),
				I32(g.Syms.at(id, cNTHROW)), I32(g.Syms.at(id, cFANIN)),
				I32(g.Syms.at(id, cISHANDLER)),
				S(g.atLine(fid, g.Syms.at(id, cLINESTART))))
		},
		func(t *Table) []orderTerm {
			return []orderTerm{
				byIntDesc(func(i int) int { return int(t.Rows[i][1].i) }),
				byIntDesc(func(i int) int { return int(t.Rows[i][2].i) }),
				byIntDesc(func(i int) int { return int(t.Rows[i][5].i) })}
		})
}

func q43(g *Graph, mod string, lim int) *Table {
	t := &Table{Cols: []string{"name", "test_callers", "callers", "sloc", "cyclo",
		"module_", "at"}}
	prod := map[int32]map[int32]bool{}
	all := map[int32]map[int32]bool{}
	for i := range g.Edges {
		e := &g.Edges[i]
		if e.isSelf {
			continue
		}
		m := all[e.callee]
		if m == nil {
			m = map[int32]bool{}
			all[e.callee] = m
		}
		m[e.caller] = true
		cid := int(e.caller) - 1
		if g.Files[g.Syms.at(cid, cFILEID)-1].isTest || g.Syms.at(cid, cISTEST) == 1 {
			continue
		}
		pm := prod[e.callee]
		if pm == nil {
			pm = map[int32]bool{}
			prod[e.callee] = pm
		}
		pm[e.caller] = true
	}
	for _, callee := range sortedIDs(all) {
		m := all[callee]
		if len(prod[callee]) != 0 {
			continue
		}
		id := int(callee) - 1
		nm := g.Syms.scol(id, cNAME)
		if !(g.Syms.at(id, cISPUBLIC) == 0 || (len(nm) > 0 && nm[0] == '_')) {
			continue
		}
		if !isFnKind(g.Syms.scol(id, cKIND)) {
			continue
		}
		fl := &g.Files[g.Syms.at(id, cFILEID)-1]
		if !fl.clean() || !likeMatch(mod, g.modName(g.Syms.at(id, cMODULEID))) {
			continue
		}
		t.add(S(nm), I32(int32(len(m)-len(prod[callee]))), I32(int32(len(m))),
			I32(g.Syms.at(id, cSLOC)), I32(g.Syms.at(id, cCYCLOMATIC)),
			S(g.modName(g.Syms.at(id, cMODULEID))),
			S(g.atLine(fl.id, g.Syms.at(id, cLINESTART))))
	}
	take(t, lim,
		byIntDesc(func(i int) int { return int(t.Rows[i][1].i) }),
		byIntDesc(func(i int) int { return int(t.Rows[i][3].i) }))
	return t
}

func q44(g *Graph, mod string, lim int) *Table {
	t := &Table{Cols: []string{"async_fn", "callers", "discarding", "pct_discarding",
		"side_effects", "throws_", "at"}}
	prod := map[int32]map[int32]bool{}
	discard := map[int32]map[int32]bool{}
	for i := range g.Edges {
		e := &g.Edges[i]
		if e.isSelf {
			continue
		}
		cid := int(e.caller) - 1
		if g.Files[g.Syms.at(cid, cFILEID)-1].isTest {
			continue
		}
		m := prod[e.callee]
		if m == nil {
			m = map[int32]bool{}
			prod[e.callee] = m
		}
		m[e.caller] = true
		if g.Syms.at(cid, cNAWAIT) == 0 && g.Syms.at(cid, cNTHEN) == 0 &&
			g.Syms.at(cid, cNCATCHHANDLER) == 0 {
			d := discard[e.callee]
			if d == nil {
				d = map[int32]bool{}
				discard[e.callee] = d
			}
			d[e.caller] = true
		}
	}
	for _, callee := range sortedIDs(prod) {
		m := prod[callee]
		d := discard[callee]
		if len(m) <= 1 || len(d) == 0 || 2*len(d) < len(m) {
			continue
		}
		id := int(callee) - 1
		if g.Syms.at(id, cISASYNC) != 1 {
			continue
		}
		fl := &g.Files[g.Syms.at(id, cFILEID)-1]
		if !fl.clean() || !likeMatch(mod, g.modName(g.Syms.at(id, cMODULEID))) {
			continue
		}
		pct := int64(100.0 * float64(len(d)) / float64(len(m)))
		t.add(S(g.Syms.scol(id, cNAME)), I32(int32(len(m))), I32(int32(len(d))), I64(pct),
			I32(g.Syms.at(id, cNNET)+g.Syms.at(id, cNIO)),
			I32(g.Syms.at(id, cNTHROW)),
			S(g.atLine(fl.id, g.Syms.at(id, cLINESTART))))
	}
	take(t, lim,
		byIntDesc(func(i int) int { return int(t.Rows[i][3].i) }),
		byIntDesc(func(i int) int { return int(t.Rows[i][4].i) }))
	return t
}

func q45(g *Graph, mod string, lim int) *Table {
	return simpleSym(g, mod, lim,
		[]string{"name", "container_writes", "containers_made", "handler_async",
			"fan_in", "module_", "at"}, fNotTestGen,
		func(id int) bool {
			return g.Syms.at(id, cISHANDLER) == 1 && g.Syms.at(id, cNCACHEWRITE) > 0
		},
		func(t *Table, id int) {
			fid := g.Syms.at(id, cFILEID)
			t.add(S(g.Syms.scol(id, cNAME)), I32(g.Syms.at(id, cNCACHEWRITE)),
				I32(g.Syms.at(id, cNNEWMAP)+g.Syms.at(id, cNNEWSET)),
				I32(g.Syms.at(id, cISASYNC)), I32(g.Syms.at(id, cFANIN)),
				S(g.modName(g.Syms.at(id, cMODULEID))),
				S(g.atLine(fid, g.Syms.at(id, cLINESTART))))
		},
		func(t *Table) []orderTerm {
			return []orderTerm{
				byIntDesc(func(i int) int { return int(t.Rows[i][1].i) }),
				byIntDesc(func(i int) int { return int(t.Rows[i][4].i) })}
		})
}

func q46(g *Graph, mod string, lim int) *Table {
	return simpleSym(g, mod, lim,
		[]string{"name", "listener_adds", "listener_removes", "inline_handlers",
			"timers_set", "handler_async", "fan_in", "module_", "at"}, fNotTestGen,
		func(id int) bool {
			return g.Syms.at(id, cISHANDLER) == 1 && g.Syms.at(id, cNLISTENERADD) > 0
		},
		func(t *Table, id int) {
			fid := g.Syms.at(id, cFILEID)
			t.add(S(g.Syms.scol(id, cNAME)), I32(g.Syms.at(id, cNLISTENERADD)),
				I32(g.Syms.at(id, cNLISTENERREMOVE)),
				I32(g.Syms.at(id, cNLISTENERINLINE)),
				I32(g.Syms.at(id, cNTIMERSET)), I32(g.Syms.at(id, cISASYNC)),
				I32(g.Syms.at(id, cFANIN)),
				S(g.modName(g.Syms.at(id, cMODULEID))),
				S(g.atLine(fid, g.Syms.at(id, cLINESTART))))
		},
		func(t *Table) []orderTerm {
			return []orderTerm{
				byIntDesc(func(i int) int { return int(t.Rows[i][1].i) }),
				byIntDesc(func(i int) int { return int(t.Rows[i][6].i) })}
		})
}

func q47(g *Graph, mod string, lim int) *Table {
	t := &Table{Cols: []string{"name", "parses", "try_blocks", "handler",
		"input_reads", "fan_in", "at"}}
	eachSym(g, fNotTestGen, mod, func(id int) {
		if g.Syms.at(id, cNJSONPARSE) <= 0 || g.Syms.at(id, cNTRY) != 0 {
			return
		}
		sid := int32(id + 1)
		reads := int32(g.uiBySym[sid])
		hd := g.Syms.at(id, cISHANDLER)
		if hd != 1 && reads == 0 {
			return
		}
		fid := g.Syms.at(id, cFILEID)
		t.add(S(g.Syms.scol(id, cNAME)), I32(g.Syms.at(id, cNJSONPARSE)),
			I32(0), I32(hd), I32(reads), I32(g.Syms.at(id, cFANIN)),
			S(g.atLine(fid, g.Syms.at(id, cLINESTART))))
	})
	take(t, lim,
		byIntDesc(func(i int) int { return int(t.Rows[i][3].i) }),
		byIntDesc(func(i int) int { return int(t.Rows[i][4].i) }),
		byIntDesc(func(i int) int { return int(t.Rows[i][1].i) }))
	return t
}

var effectHooks = map[string]bool{
	"useEffect": true, "useLayoutEffect": true, "useCallback": true,
	"useMemo": true, "useImperativeHandle": true, "useInsertionEffect": true,
}

func q48(g *Graph, mod string, lim int) *Table {
	t := &Table{Cols: []string{"name", "no_dep_array", "deps", "in_loop",
		"in_condition", "registers_listener", "registers_timer", "cleanup", "in_fn", "at"}}
	for i := range g.Hooks {
		h := &g.Hooks[i]
		if !effectHooks[h.Name(g)] {
			continue
		}
		if h.hasDeps && h.nDeps != 0 {
			continue
		}
		fl := &g.Files[h.fileID-1]
		if !fl.clean() || !likeMatch(mod, g.modName(fl.moduleID)) {
			continue
		}
		t.add(S(h.Name(g)), I32(b2i(h.hasDeps)), I32(h.nDeps), I32(b2i(h.inLoop)),
			I32(b2i(h.inCond)), I32(b2i(h.regListener)), I32(b2i(h.regTimer)),
			I32(b2i(h.cleanup)), S(g.ownerName(h.symID)), S(g.at(h.fileID, h.line)))
	}
	take(t, lim,
		byInt(func(i int) int { return int(t.Rows[i][1].i) }),
		byIntDesc(func(i int) int { return int(t.Rows[i][5].i) }),
		byInt(func(i int) int { return int(findColon(t.Rows[i][9].s)) }))
	return t
}

func q49(g *Graph, mod string, lim int) *Table {
	t := &Table{Cols: []string{"name", "registers_listener", "registers_timer",
		"no_dep_array", "deps", "in_condition", "in_fn", "at"}}
	for i := range g.Hooks {
		h := &g.Hooks[i]
		if !(h.regListener || h.regTimer) || h.cleanup {
			continue
		}
		fl := &g.Files[h.fileID-1]
		if !fl.clean() || !likeMatch(mod, g.modName(fl.moduleID)) {
			continue
		}
		t.add(S(h.Name(g)), I32(b2i(h.regListener)), I32(b2i(h.regTimer)),
			I32(b2i(h.hasDeps)), I32(h.nDeps), I32(b2i(h.inCond)),
			S(g.ownerName(h.symID)), S(g.at(h.fileID, h.line)))
	}
	take(t, lim,
		byIntDesc(func(i int) int { return int(t.Rows[i][1].i) }),
		byIntDesc(func(i int) int { return int(t.Rows[i][2].i) }),
		byInt(func(i int) int { return int(findColon(t.Rows[i][7].s)) }))
	return t
}

func (g *Graph) ownerName(sid int32) string {
	if sid == 0 || int(sid) > g.nSym() {
		return "(module scope)"
	}
	return g.Syms.scol(int(sid)-1, cNAME)
}

func findColon(s string) int64 { return int64(indexOfByte(s, ':')) }

func indexOfByte(s string, b byte) int {
	for i := 0; i < len(s); i++ {
		if s[i] == b {
			return i
		}
	}
	return len(s)
}

func q50(g *Graph, mod string, lim int) *Table {
	return simpleSym(g, mod, lim,
		[]string{"name", "exit_calls", "is_entrypoint", "fan_in", "module_", "at"},
		fNotTestGen,
		func(id int) bool {
			return g.Syms.at(id, cNPROCESSEXIT) > 0 && g.Syms.at(id, cISEXPORTED) == 1
		},
		func(t *Table, id int) {
			fid := g.Syms.at(id, cFILEID)
			t.add(S(g.Syms.scol(id, cNAME)), I32(g.Syms.at(id, cNPROCESSEXIT)),
				I32(g.Syms.at(id, cISENTRYPOINT)), I32(g.Syms.at(id, cFANIN)),
				S(g.modName(g.Syms.at(id, cMODULEID))),
				S(g.atLine(fid, g.Syms.at(id, cLINESTART))))
		},
		func(t *Table) []orderTerm {
			return []orderTerm{
				byIntDesc(func(i int) int { return int(t.Rows[i][3].i) }),
				byIntDesc(func(i int) int { return int(t.Rows[i][1].i) })}
		})
}

func q51(g *Graph, mod string, lim int) *Table {
	t := &Table{Cols: []string{"name", "weak_hashes", "input_reads", "handler",
		"crypto_hazards", "fan_in", "at"}}
	eachSym(g, fNotTestGen, mod, func(id int) {
		if g.Syms.at(id, cNWEAKHASH) <= 0 {
			return
		}
		fid := g.Syms.at(id, cFILEID)
		t.add(S(g.Syms.scol(id, cNAME)), I32(g.Syms.at(id, cNWEAKHASH)),
			I32(g.uiBySym[int32(id+1)]), I32(g.Syms.at(id, cISHANDLER)),
			I32(g.Syms.at(id, cNCRYPTO)), I32(g.Syms.at(id, cFANIN)),
			S(g.atLine(fid, g.Syms.at(id, cLINESTART))))
	})
	take(t, lim,
		byIntDesc(func(i int) int { return int(t.Rows[i][2].i) }),
		byIntDesc(func(i int) int { return int(t.Rows[i][1].i) }),
		byIntDesc(func(i int) int { return int(t.Rows[i][5].i) }))
	return t
}

func q52(g *Graph, mod string, lim int) *Table {
	return simpleSym(g, mod, lim,
		[]string{"name", "random_calls", "auth_calls", "handler", "exported",
			"fan_in", "at"}, fNotTestGen,
		func(id int) bool {
			return g.Syms.at(id, cNMATHRANDOM) > 0 && g.Syms.at(id, cNAUTHCALL) > 0
		},
		func(t *Table, id int) {
			fid := g.Syms.at(id, cFILEID)
			t.add(S(g.Syms.scol(id, cNAME)), I32(g.Syms.at(id, cNMATHRANDOM)),
				I32(g.Syms.at(id, cNAUTHCALL)), I32(g.Syms.at(id, cISHANDLER)),
				I32(g.Syms.at(id, cISEXPORTED)), I32(g.Syms.at(id, cFANIN)),
				S(g.atLine(fid, g.Syms.at(id, cLINESTART))))
		},
		func(t *Table) []orderTerm {
			return []orderTerm{
				byIntDesc(func(i int) int { return int(t.Rows[i][2].i) }),
				byIntDesc(func(i int) int { return int(t.Rows[i][1].i) }),
				byIntDesc(func(i int) int { return int(t.Rows[i][5].i) })}
		})
}

func q53(g *Graph, mod string, lim int) *Table {
	t := &Table{Cols: []string{"in_fn", "api", "kind", "module_scope", "in_loop",
		"repeating", "at"}}
	for i := range g.Timers {
		x := &g.Timers[i]
		if x.Op(g) != "set" || !x.cbString {
			continue
		}
		fl := &g.Files[x.fileID-1]
		if fl.isTest || !likeMatch(mod, g.modName(fl.moduleID)) {
			continue
		}
		t.add(S(g.ownerName(x.symID)), S(g.s(x.api)), S(g.s(x.kind)), I32(b2i(x.atModule)),
			I32(b2i(x.inLoop)), I32(b2i(x.repeating)), S(g.at(x.fileID, x.line)))
	}
	take(t, lim,
		byIntDesc(func(i int) int { return int(t.Rows[i][5].i) }),
		byIntDesc(func(i int) int { return int(t.Rows[i][3].i) }),
		byIntDesc(func(i int) int { return int(t.Rows[i][4].i) }))
	return t
}

func q54(g *Graph, mod string, lim int) *Table {
	t := &Table{Cols: []string{"event", "target", "in_fn", "exit_calls", "at"}}
	execBy := map[int32]int32{}
	for i := range g.Hazards {
		if g.Hazards[i].Category(g) == "exec" {
			execBy[g.Hazards[i].symID] += g.Hazards[i].n
		}
	}
	for i := range g.Listeners {
		l := &g.Listeners[i]
		if l.Op(g) != "add" {
			continue
		}
		if l.Event(g) != "uncaughtException" && l.Event(g) != "unhandledRejection" {
			continue
		}
		fl := &g.Files[l.fileID-1]
		if fl.isTest || !likeMatch(mod, g.modName(fl.moduleID)) {
			continue
		}
		t.add(S(g.s(l.event)), S(g.s(l.target)), S(g.ownerName(l.symID)),
			I32(execBy[l.symID]), S(g.at(l.fileID, l.line)))
	}
	take(t, lim,
		byBoolDesc(func(i int) bool { return t.Rows[i][1].s == "process" }),
		byStr(func(i int) string { return t.Rows[i][0].s }))
	return t
}

func q55(g *Graph, mod string, lim int) *Table {
	return simpleSym(g, mod, lim,
		[]string{"name", "containers", "writes", "fan_in", "handler", "recursive_", "at"},
		fNotTestGen,
		func(id int) bool {
			return (g.Syms.at(id, cNNEWMAP) > 0 || g.Syms.at(id, cNNEWSET) > 0) &&
				g.Syms.at(id, cNCACHEWRITE) > 0 && isFnKind(g.Syms.scol(id, cKIND))
		},
		func(t *Table, id int) {
			fid := g.Syms.at(id, cFILEID)
			t.add(S(g.Syms.scol(id, cNAME)),
				I32(g.Syms.at(id, cNNEWMAP)+g.Syms.at(id, cNNEWSET)),
				I32(g.Syms.at(id, cNCACHEWRITE)), I32(g.Syms.at(id, cFANIN)),
				I32(g.Syms.at(id, cISHANDLER)), I32(g.Syms.at(id, cISRECURSIVE)),
				S(g.atLine(fid, g.Syms.at(id, cLINESTART))))
		},
		func(t *Table) []orderTerm {
			return []orderTerm{
				byIntDesc(func(i int) int { return int(t.Rows[i][2].i) }),
				byIntDesc(func(i int) int { return int(t.Rows[i][3].i) })}
		})
}

func q56(g *Graph, mod string, lim int) *Table {
	return simpleSym(g, mod, lim,
		[]string{"module_symbol", "sync_calls", "io_hazards", "exec_hazards", "entry",
			"module_", "at"}, fNotTestGen,
		func(id int) bool {
			return g.Syms.scol(id, cKIND) == "module" && g.Syms.at(id, cNSYNCCALLS) > 0
		},
		func(t *Table, id int) {
			fid := g.Syms.at(id, cFILEID)
			t.add(S(g.Syms.scol(id, cNAME)), I32(g.Syms.at(id, cNSYNCCALLS)),
				I32(g.Syms.at(id, cNIO)), I32(g.Syms.at(id, cNEXEC)),
				I32(g.Syms.at(id, cISENTRYPOINT)),
				S(g.modName(g.Syms.at(id, cMODULEID))),
				S(g.atLine(fid, g.Syms.at(id, cLINESTART))))
		},
		func(t *Table) []orderTerm {
			return []orderTerm{
				byIntDesc(func(i int) int { return int(t.Rows[i][1].i) }),
				byIntDesc(func(i int) int { return int(t.Rows[i][3].i) })}
		})
}

func q57(g *Graph, mod string, lim int) *Table {
	t := &Table{Cols: []string{"name", "alias", "from_file", "module_", "at"}}
	for i := range g.ImportNames {
		n := &g.ImportNames[i]
		if nm := n.Name(g); nm == "" || nm[0] != '_' {
			continue
		}
		if n.sourceID == 0 {
			continue
		}
		f := &g.Files[n.fileID-1]
		tf := &g.Files[n.sourceID-1]
		if f.isTest || tf.isTest || f.isGen {
			continue
		}
		if !likeMatch(mod, g.modName(f.moduleID)) {
			continue
		}
		t.add(S(g.s(n.name)), S(g.s(n.alias)), S(g.s(n.source)),
			S(g.modName(f.moduleID)), S(g.at(n.fileID, n.line)))
	}

	take(t, lim,
		byStr(func(i int) string { return findPath(t.Rows[i][4].s) }),
		byInt(func(i int) int { return int(findColon(t.Rows[i][4].s)) }))
	return t
}

func findPath(s string) string {
	if i := indexOfByte(s, ':'); i >= 0 {
		return s[:i]
	}
	return s
}

func q58(g *Graph, mod string, lim int) *Table {
	return simpleSym(g, mod, lim,
		[]string{"name", "then_sites_in_loop", "awaits_in_loop", "then_sites",
			"catch_handlers", "loops", "fan_in", "at"}, fNotTestGen,
		func(id int) bool { return g.Syms.at(id, cNTHENINLOOP) > 0 },
		func(t *Table, id int) {
			fid := g.Syms.at(id, cFILEID)
			t.add(S(g.Syms.scol(id, cNAME)), I32(g.Syms.at(id, cNTHENINLOOP)),
				I32(g.Syms.at(id, cAWAITINLOOP)), I32(g.Syms.at(id, cNTHEN)),
				I32(g.Syms.at(id, cNCATCHHANDLER)), I32(g.Syms.at(id, cNLOOPS)),
				I32(g.Syms.at(id, cFANIN)),
				S(g.atLine(fid, g.Syms.at(id, cLINESTART))))
		},
		func(t *Table) []orderTerm {
			return []orderTerm{
				byIntDesc(func(i int) int { return int(t.Rows[i][1].i) }),
				byIntDesc(func(i int) int { return int(t.Rows[i][6].i) })}
		})
}

func q59(g *Graph, mod string, lim int) *Table {
	return simpleSym(g, mod, lim,
		[]string{"module_symbol", "detached_calls", "awaits", "net_hazards",
			"io_hazards", "module_", "at"}, fNotTestGen,
		func(id int) bool {
			if g.Syms.scol(id, cKIND) != "module" {
				return false
			}
			fp := g.Syms.at(id, cNFLOATINGPROMISE)
			if fp <= 1 || g.Syms.at(id, cNAWAIT) != 0 {
				return false
			}
			side := g.Syms.at(id, cNNET) + g.Syms.at(id, cNIO) + g.Syms.at(id, cNEXEC) +
				g.Syms.at(id, cNTIMERSET) + g.Syms.at(id, cNCHILDPROCESS) +
				g.Syms.at(id, cNSERVERSTART)
			return side > 0
		},
		func(t *Table, id int) {
			fid := g.Syms.at(id, cFILEID)
			t.add(S(g.Syms.scol(id, cNAME)), I32(g.Syms.at(id, cNFLOATINGPROMISE)),
				I32(g.Syms.at(id, cNAWAIT)), I32(g.Syms.at(id, cNNET)),
				I32(g.Syms.at(id, cNIO)),
				S(g.modName(g.Syms.at(id, cMODULEID))),
				S(g.atLine(fid, g.Syms.at(id, cLINESTART))))
		},
		func(t *Table) []orderTerm {
			return []orderTerm{byIntDesc(func(i int) int { return int(t.Rows[i][1].i) })}
		})
}

func q60(g *Graph, mod string, lim int) *Table {
	return simpleSym(g, mod, lim,
		[]string{"module_symbol", "top_level_awaits", "detached_calls", "net_hazards",
			"entry", "module_", "at"}, fNotTestGen,
		func(id int) bool {
			return g.Syms.scol(id, cKIND) == "module" && g.Syms.at(id, cNAWAIT) > 0
		},
		func(t *Table, id int) {
			fid := g.Syms.at(id, cFILEID)
			t.add(S(g.Syms.scol(id, cNAME)), I32(g.Syms.at(id, cNAWAIT)),
				I32(g.Syms.at(id, cNFLOATINGPROMISE)), I32(g.Syms.at(id, cNNET)),
				I32(g.Syms.at(id, cISENTRYPOINT)),
				S(g.modName(g.Syms.at(id, cMODULEID))),
				S(g.atLine(fid, g.Syms.at(id, cLINESTART))))
		},
		func(t *Table) []orderTerm {
			return []orderTerm{byIntDesc(func(i int) int { return int(t.Rows[i][1].i) })}
		})
}

func init() {
	for i, f := range []func(*Graph, string, int) *Table{
		q61, q62, q63, q64, q65, q66, q67, q68, q69, q70, q71, q72} {
		queries[60+i].Run = f
	}
	for i, f := range []func(*Graph, string, int) *Table{
		m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16,
		m17, m18, m19, m20, m21, m22, m23, m24, m25, m26} {
		metrics[i].Run = f
	}
}

func q61(g *Graph, mod string, lim int) *Table {
	t := &Table{Cols: []string{"target", "event", "adds", "inline_adds", "module_", "at"}}
	type key struct {
		fid    int32
		target string
		event  string
	}
	agg := map[key]*[3]int32{}
	var order []key
	for i := range g.Listeners {
		l := &g.Listeners[i]
		if l.Op(g) != "add" {
			continue
		}
		if g.Files[l.fileID-1].isTest {
			continue
		}
		k := key{l.fileID, g.s(l.target), g.s(l.event)}
		v := agg[k]
		if v == nil {
			v = &[3]int32{0, 0, 0}
			agg[k] = v
			order = append(order, k)
		}
		v[0]++
		if l.inline {
			v[1]++
		}
		if v[2] == 0 || l.line < v[2] {
			v[2] = l.line
		}
	}
	for _, k := range order {
		v := agg[k]
		if v[0] <= 1 {
			continue
		}
		f := &g.Files[k.fid-1]
		if !likeMatch(mod, g.modName(f.moduleID)) {
			continue
		}
		t.add(S(k.target), S(k.event), I32(v[0]), I32(v[1]),
			S(g.modName(f.moduleID)), S(g.at(k.fid, v[2])))
	}
	take(t, lim,
		byIntDesc(func(i int) int { return int(t.Rows[i][2].i) }),
		byIntDesc(func(i int) int { return int(t.Rows[i][3].i) }))
	return t
}

func q62(g *Graph, mod string, lim int) *Table {
	t := &Table{Cols: []string{"path", "starts", "line", "module_", "at"}}
	starts := map[int32]*[2]int32{}
	var order []int32
	for id := 0; id < g.nSym(); id++ {
		v := g.Syms.at(id, cNSERVERSTART)
		if v <= 0 {
			continue
		}
		fid := g.Syms.at(id, cFILEID)
		if g.Files[fid-1].isTest {
			continue
		}
		s := starts[fid]
		if s == nil {
			s = &[2]int32{g.Syms.at(id, cLINESTART), 0}
			starts[fid] = s
			order = append(order, fid)
		} else if g.Syms.at(id, cLINESTART) < s[0] {
			s[0] = g.Syms.at(id, cLINESTART)
		}
		s[1] += v
	}
	signals := map[string]bool{"SIGTERM": true, "SIGINT": true, "SIGUSR2": true,
		"exit": true, "beforeExit": true}
	for _, fid := range order {
		f := &g.Files[fid-1]
		has := false
		for i := range g.Listeners {
			l := &g.Listeners[i]
			if l.fileID == fid && l.Op(g) == "add" && signals[l.Event(g)] {
				has = true
				break
			}
		}
		if has || f.isGen || !likeMatch(mod, g.modName(f.moduleID)) {
			continue
		}
		s := starts[fid]
		t.add(S(g.s(f.path)), I32(s[1]), I32(s[0]), S(g.modName(f.moduleID)),
			S(g.at(fid, s[0])))
	}
	take(t, lim,
		byIntDesc(func(i int) int { return int(t.Rows[i][1].i) }),
		byStr(func(i int) string { return t.Rows[i][0].s }))
	return t
}

func q63(g *Graph, mod string, lim int) *Table {
	t := &Table{Cols: []string{"name", "hops_to_edge", "env_reads", "fan_in",
		"handler", "entry", "module_", "at"}}
	var entries []int32
	for id := 0; id < g.nSym(); id++ {
		if g.Syms.at(id, cNENVREAD) > 0 {
			entries = append(entries, int32(id+1))
		}
	}

	best := g.reachUp(entries, 4)
	for _, sym := range sortedIDs(best) {
		depth := best[sym]
		id := int(sym) - 1
		if g.Syms.at(id, cNENVREAD) <= 0 {
			continue
		}
		fl := &g.Files[g.Syms.at(id, cFILEID)-1]
		if !fl.clean() || !likeMatch(mod, g.modName(g.Syms.at(id, cMODULEID))) {
			continue
		}
		t.add(S(g.Syms.scol(id, cNAME)), I32(depth), I32(g.Syms.at(id, cNENVREAD)),
			I32(g.Syms.at(id, cFANIN)), I32(g.Syms.at(id, cISHANDLER)),
			I32(g.Syms.at(id, cISENTRYPOINT)),
			S(g.modName(g.Syms.at(id, cMODULEID))),
			S(g.atLine(fl.id, g.Syms.at(id, cLINESTART))))
	}
	take(t, lim,
		byIntDesc(func(i int) int { return int(t.Rows[i][1].i) }),
		byIntDesc(func(i int) int { return int(t.Rows[i][3].i) }))
	return t
}

func oneCounter(g *Graph, mod string, lim int, cols []string, ff fileFilter,
	col int, withFanIn bool, extra func(id int) []Cell, tail func(id int) []Cell,
	terms func(t *Table) []orderTerm) *Table {
	t := &Table{Cols: cols}
	eachSym(g, ff, mod, func(id int) {
		v := g.Syms.at(id, col)
		if v <= 0 {
			return
		}
		fid := g.Syms.at(id, cFILEID)
		row := []Cell{S(g.Syms.scol(id, cNAME)), I32(v)}
		row = append(row, extra(id)...)
		if withFanIn {
			row = append(row, I32(g.Syms.at(id, cFANIN)))
		}
		if tail != nil {
			row = append(row, tail(id)...)
		}
		row = append(row, S(g.atLine(fid, g.Syms.at(id, cLINESTART))))
		t.add(row...)
	})
	t.take(terms(t), lim)
	return t
}

func q64(g *Graph, mod string, lim int) *Table {
	return oneCounter(g, mod, lim,
		[]string{"name", "async_executors", "batches", "awaits", "fan_in", "at"},
		fNotTestGen, cNPROMISEEXECASYNC, true,
		func(id int) []Cell {
			return []Cell{I32(g.Syms.at(id, cNPROMISEALL)), I32(g.Syms.at(id, cNAWAIT))}
		},
		nil,
		func(t *Table) []orderTerm {
			return []orderTerm{
				byIntDesc(func(i int) int { return int(t.Rows[i][1].i) }),
				byIntDesc(func(i int) int { return int(t.Rows[i][4].i) })}
		})
}

func q65(g *Graph, mod string, lim int) *Table {
	return oneCounter(g, mod, lim,
		[]string{"name", "executor_returns", "async_executors", "awaits", "fan_in", "at"},
		fNotTestGen, cNPROMISEEXECRETURN, true,
		func(id int) []Cell {
			return []Cell{I32(g.Syms.at(id, cNPROMISEEXECASYNC)), I32(g.Syms.at(id, cNAWAIT))}
		},
		nil,
		func(t *Table) []orderTerm {
			return []orderTerm{
				byIntDesc(func(i int) int { return int(t.Rows[i][1].i) }),
				byIntDesc(func(i int) int { return int(t.Rows[i][4].i) })}
		})
}

func q66(g *Graph, mod string, lim int) *Table {
	return oneCounter(g, mod, lim,
		[]string{"name", "async_args", "listener_adds", "timers_set", "callback_args",
			"fan_in", "handler", "at"}, fNotTestGen, cNASYNCARG, true,
		func(id int) []Cell {
			return []Cell{I32(g.Syms.at(id, cNLISTENERADD)),
				I32(g.Syms.at(id, cNTIMERSET)), I32(g.Syms.at(id, cNCALLBACKS))}
		},
		func(id int) []Cell { return []Cell{I32(g.Syms.at(id, cISHANDLER))} },
		func(t *Table) []orderTerm {
			return []orderTerm{
				byIntDesc(func(i int) int { return int(t.Rows[i][1].i) }),
				byIntDesc(func(i int) int { return int(t.Rows[i][2].i) }),
				byIntDesc(func(i int) int { return int(t.Rows[i][5].i) })}
		})
}

func q67(g *Graph, mod string, lim int) *Table {
	return oneCounter(g, mod, lim,
		[]string{"name", "dynamic_regexes", "input_reads", "regex_literals",
			"regex_in_loop", "fan_in", "handler", "at"}, fNotTestGen, cNREGEXDYNAMIC, true,
		func(id int) []Cell {
			return []Cell{I32(g.uiBySym[int32(id+1)]), I32(g.Syms.at(id, cNREGEXLIT)),
				I32(g.Syms.at(id, cREGEXINLOOP))}
		},
		func(id int) []Cell { return []Cell{I32(g.Syms.at(id, cISHANDLER))} },
		func(t *Table) []orderTerm {
			return []orderTerm{
				byIntDesc(func(i int) int { return int(t.Rows[i][1].i) }),
				byIntDesc(func(i int) int { return int(t.Rows[i][2].i) })}
		})
}

func q68(g *Graph, mod string, lim int) *Table {
	return oneCounter(g, mod, lim,
		[]string{"name", "file_sends", "input_reads", "fs_dynamic_opens", "handler",
			"at"}, fNotTestGen, cNSENDFILE, false,
		func(id int) []Cell {
			return []Cell{I32(g.uiBySym[int32(id+1)]),
				I32(g.Syms.at(id, cNDYNAMICOPEN)), I32(g.Syms.at(id, cISHANDLER))}
		},
		nil,
		func(t *Table) []orderTerm {
			return []orderTerm{
				byIntDesc(func(i int) int { return int(t.Rows[i][2].i) }),
				byIntDesc(func(i int) int { return int(t.Rows[i][1].i) })}
		})
}

func q69(g *Graph, mod string, lim int) *Table {
	return oneCounter(g, mod, lim,
		[]string{"name", "lazy_requires", "dynamic_requires", "calls_", "fan_in",
			"handler", "module_", "at"}, fNotTestGen, cNLAZYREQUIRE, true,
		func(id int) []Cell {
			return []Cell{I32(g.Syms.at(id, cNREQUIREDYNAMIC)),
				I32(g.Syms.at(id, cNCALLS))}
		},
		func(id int) []Cell {
			return []Cell{I32(g.Syms.at(id, cISHANDLER)),
				S(g.modName(g.Syms.at(id, cMODULEID)))}
		},
		func(t *Table) []orderTerm {
			return []orderTerm{
				byIntDesc(func(i int) int { return int(t.Rows[i][1].i) }),
				byIntDesc(func(i int) int { return int(t.Rows[i][4].i) })}
		})
}

func q70(g *Graph, mod string, lim int) *Table {
	t := &Table{Cols: []string{"method", "path", "handler", "middlewares", "inline",
		"defs_in_tree", "module_", "at"}}
	for i := range g.Routes {
		r := &g.Routes[i]
		if !r.async {
			continue
		}
		fl := &g.Files[r.fileID-1]
		if fl.isTest || !likeMatch(mod, g.modName(fl.moduleID)) {
			continue
		}
		t.add(S(g.s(r.method)), S(g.s(r.path)), S(g.s(r.handler)), I32(r.nMw), I32(b2i(r.inline)),
			I32(g.defsInTree(g.s(r.handler))), S(g.modName(fl.moduleID)),
			S(g.at(r.fileID, r.line)))
	}
	take(t, lim,
		byIntDesc(func(i int) int { return int(t.Rows[i][3].i) }),
		byInt(func(i int) int { return int(findColon(t.Rows[i][7].s)) }))
	return t
}

func q71(g *Graph, mod string, lim int) *Table {
	t := &Table{Cols: []string{"method", "path", "handler", "middlewares", "module_", "at"}}
	for i := range g.Routes {
		r := &g.Routes[i]
		if r.inline || r.Handler(g) == "" {
			continue
		}
		fl := &g.Files[r.fileID-1]
		if fl.isTest || !likeMatch(mod, g.modName(fl.moduleID)) {
			continue
		}
		if g.defsInTree(g.s(r.handler)) > 0 {
			continue
		}
		t.add(S(g.s(r.method)), S(g.s(r.path)), S(g.s(r.handler)), I32(r.nMw),
			S(g.modName(fl.moduleID)), S(g.at(r.fileID, r.line)))
	}
	take(t, lim, byInt(func(i int) int { return int(findColon(t.Rows[i][5].s)) }))
	return t
}

func q72(g *Graph, mod string, lim int) *Table {
	t := &Table{Cols: []string{"in_fn", "api", "kind", "module_scope", "in_loop",
		"repeating", "handle_kept", "fn_is_async", "at"}}
	for i := range g.Timers {
		x := &g.Timers[i]
		if x.Op(g) != "set" || !x.asyncCB {
			continue
		}
		fl := &g.Files[x.fileID-1]
		if fl.isTest || !likeMatch(mod, g.modName(fl.moduleID)) {
			continue
		}
		async := int32(0)
		if x.symID != 0 && int(x.symID) <= g.nSym() {
			async = g.Syms.at(int(x.symID)-1, cISASYNC)
		}
		t.add(S(g.ownerName(x.symID)), S(g.s(x.api)), S(g.s(x.kind)), I32(b2i(x.atModule)),
			I32(b2i(x.inLoop)), I32(b2i(x.repeating)), I32(b2i(x.assigned)),
			I32(async), S(g.at(x.fileID, x.line)))
	}
	take(t, lim,
		byIntDesc(func(i int) int { return int(t.Rows[i][5].i) }),
		byIntDesc(func(i int) int { return int(t.Rows[i][4].i) }),
		byIntDesc(func(i int) int { return int(t.Rows[i][3].i) }))
	return t
}

func m1(g *Graph, mod string, lim int) *Table {
	t := &Table{Cols: []string{"module_", "fns", "calls", "external", "unresolved",
		"dynamic_", "computed_member", "dyn_import", "reflect_", "pct_blind"}}
	type acc struct {
		fns                               int64
		calls, ext, unres, dyn, comp, imp int64
		refl                              int64
	}
	agg := map[int32]*acc{}
	for id := 0; id < g.nSym(); id++ {
		if !isFnKind(g.Syms.scol(id, cKIND)) {
			continue
		}
		mid := g.Syms.at(id, cMODULEID)
		if mid == 0 || !likeMatch(mod, g.Modules[mid-1].Name(g)) {
			continue
		}
		a := agg[mid]
		if a == nil {
			a = &acc{}
			agg[mid] = a
		}
		a.fns++
		a.calls += int64(g.Syms.at(id, cNCALLS))
		a.ext += int64(g.Syms.at(id, cNEXTERNALCALLS))
		a.unres += int64(g.Syms.at(id, cNUNRESOLVEDCALLS))
		a.dyn += int64(g.Syms.at(id, cNDYNAMICCALLS))
		a.comp += int64(g.Syms.at(id, cNCOMPUTEDMEMBER))
		a.imp += int64(g.Syms.at(id, cNREQUIREDYNAMIC) + g.Syms.at(id, cNIMPORTDYNAMIC))
		a.refl += int64(g.Syms.at(id, cNREFLECT))
	}
	for _, mid := range sortedIDs(agg) {
		a := agg[mid]
		if a.calls <= 0 {
			continue
		}
		pct := int64(100.0 * float64(a.unres) / float64(a.calls))
		t.add(S(g.Modules[mid-1].Name(g)), I64(a.fns), I64(a.calls), I64(a.ext),
			I64(a.unres), I64(a.dyn), I64(a.comp), I64(a.imp), I64(a.refl), I64(pct))
	}
	take(t, lim,
		byIntDesc(func(i int) int { return int(t.Rows[i][4].i) }),
		byIntDesc(func(i int) int { return int(t.Rows[i][5].i) }))
	return t
}

func m2(g *Graph, mod string, lim int) *Table {
	t := &Table{Cols: []string{"name", "class_", "modules_calling", "fan_in", "sites",
		"computed_access", "dynamic_writes", "deletes", "uses_arguments", "this_refs",
		"optional_chains", "spreads", "reflect_ops", "sloc", "shape_churn", "at"}}
	eachSym(g, fNotTestGen, mod, func(id int) {
		k := g.Syms.scol(id, cKIND)
		if k != "function" && k != "method" {
			return
		}
		if g.Syms.at(id, cNMODULESCALLING) <= 4 {
			return
		}
		comp := g.Syms.at(id, cNCOMPUTEDMEMBER)
		dp := g.Syms.at(id, cNDYNAMICPROP)
		del := g.Syms.at(id, cNDELETE)
		arg := g.Syms.at(id, cNARGUMENTS)
		ref := g.Syms.at(id, cNREFLECT)
		if comp+dp+del+arg+ref <= 0 {
			return
		}
		churn := (comp*2 + dp*3 + del*5 + arg*4 + ref*3) * (1 + g.Syms.at(id, cNMODULESCALLING))
		fid := g.Syms.at(id, cFILEID)
		t.add(S(g.Syms.scol(id, cNAME)), S(g.Syms.scol(id, cCLASSNAME)),
			I32(g.Syms.at(id, cNMODULESCALLING)), I32(g.Syms.at(id, cFANIN)),
			I32(g.Syms.at(id, cNCALLSITES)), I32(comp), I32(dp), I32(del), I32(arg),
			I32(g.Syms.at(id, cNTHISREFS)), I32(g.Syms.at(id, cNOPTIONALCHAIN)),
			I32(g.Syms.at(id, cNSPREAD)), I32(ref), I32(g.Syms.at(id, cSLOC)),
			I32(churn), S(g.atLine(fid, g.Syms.at(id, cLINESTART))))
	})
	take(t, lim, byIntDesc(func(i int) int { return int(t.Rows[i][14].i) }))
	return t
}

func m3(g *Graph, mod string, lim int) *Table {
	t := &Table{Cols: []string{"name", "kind", "cjs", "symbol", "symbol_kind", "sloc",
		"callers", "imported_by", "star_reexports", "exports_in_file", "at"}}
	importedIn := map[int32][]string{}
	for i := range g.ImportNames {
		n := &g.ImportNames[i]
		if n.sourceID == 0 {
			continue
		}
		importedIn[n.sourceID] = append(importedIn[n.sourceID], g.s(n.name))
	}
	starRe := map[int32]int32{}
	exportsIn := map[int32]int32{}
	for i := range g.Exports {
		e := &g.Exports[i]
		exportsIn[e.fileID]++
		if e.star && e.sourceID != 0 {
			starRe[e.sourceID]++
		}
	}
	anyImport := map[int32]bool{}
	for i := range g.Imports {
		if g.Imports[i].targetID != 0 {
			anyImport[g.Imports[i].targetID] = true
		}
	}
	for i := range g.Exports {
		e := &g.Exports[i]
		if e.star || e.reexport {
			continue
		}
		fl := &g.Files[e.fileID-1]
		if !fl.clean() || !likeMatch(mod, g.modName(fl.moduleID)) {
			continue
		}
		importedBy := int32(0)
		for _, nm := range importedIn[e.fileID] {
			if nm == e.Name(g) {
				importedBy++
			}
		}

		nsSeen := map[string]bool{}
		for j := range g.ImportNames {
			n := &g.ImportNames[j]
			if n.sourceID != e.fileID {
				continue
			}
			if n.ns && !nsSeen[g.s(n.name)] {
				nsSeen[g.s(n.name)] = true
				importedBy++
			}
			if n.def && (e.Kind(g) == "default" || e.Kind(g) == "cjs" &&
				!nsSeen[n.Name(g)+"\x00def"]) {
				nsSeen[n.Name(g)+"\x00def"] = true
				importedBy++
			}
		}
		callers := int32(0)
		symName, symKind, sloc := "", "", int32(0)
		if e.symID != 0 && int(e.symID) <= g.nSym() {
			id := int(e.symID) - 1
			symName, symKind = g.Syms.scol(id, cNAME), g.Syms.scol(id, cKIND)
			callers, sloc = g.Syms.at(id, cFANIN), g.Syms.at(id, cSLOC)
		}
		if importedBy != 0 || starRe[e.fileID] != 0 || callers != 0 || anyImport[e.fileID] {
			continue
		}
		t.add(S(g.s(e.name)), S(g.s(e.kind)), I32(b2i(e.cjs)), S(symName), S(symKind),
			I32(sloc), I32(callers), I32(importedBy), I32(starRe[e.fileID]),
			I32(exportsIn[e.fileID]), S(g.at(e.fileID, e.line)))
	}
	take(t, lim,
		byIntDesc(func(i int) int { return int(t.Rows[i][5].i) }),
		byStr(func(i int) string { return t.Rows[i][0].s }))
	return t
}

func m4(g *Graph, mod string, lim int) *Table {
	t := &Table{Cols: []string{"name", "class_", "kind", "sloc", "cyclo", "cog", "nest",
		"elifs", "closures", "callbacks", "returns_", "n_params", "this_refs", "maint",
		"fan_in", "at"}}
	eachSym(g, fNotGen, mod, func(id int) {
		k := g.Syms.scol(id, cKIND)
		if k != "function" && k != "method" {
			return
		}
		fid := g.Syms.at(id, cFILEID)
		t.add(S(g.Syms.scol(id, cNAME)), S(g.Syms.scol(id, cCLASSNAME)), S(k),
			I32(g.Syms.at(id, cSLOC)), I32(g.Syms.at(id, cCYCLOMATIC)),
			I32(g.Syms.at(id, cCOGNITIVE)), I32(g.Syms.at(id, cMAXNESTING)),
			I32(g.Syms.at(id, cNELIF)), I32(g.Syms.at(id, cNCLOSURES)),
			I32(g.Syms.at(id, cNCALLBACKS)), I32(g.Syms.at(id, cNRETURNS)),
			I32(g.Syms.at(id, cNPARAMS)), I32(g.Syms.at(id, cNTHISREFS)),
			I32(g.Syms.at(id, cMAINTAINABILITY)), I32(g.Syms.at(id, cFANIN)),
			S(g.atLine(fid, g.Syms.at(id, cLINESTART))))
	})
	take(t, lim,
		byIntDesc(func(i int) int { return int(t.Rows[i][5].i) }),
		byIntDesc(func(i int) int { return int(t.Rows[i][3].i) }))
	return t
}

func m5(g *Graph, mod string, lim int) *Table {
	t := &Table{Cols: []string{"path", "lines", "errors", "missing", "parsed",
		"generated", "test", "ext", "symbols", "dynamic_imports"}}
	dyn := map[int32]int32{}
	for i := range g.Imports {
		if g.Imports[i].isDynamic != 0 {
			dyn[g.Imports[i].fileID]++
		}
	}
	for i := range g.Files {
		f := &g.Files[i]
		if !(f.nParseErrors > 0 || !f.parsed) {
			continue
		}
		if !likeMatch(mod, g.modName(f.moduleID)) {
			continue
		}
		t.add(S(g.s(f.path)), I32(f.lines), I32(f.nParseErrors), I32(f.nMissing),
			I32(b2i(f.parsed)), I32(b2i(f.isGen)), I32(b2i(f.isTest)), S(g.s(f.ext)),
			I32(f.nSymbols), I32(dyn[f.id]))
	}
	take(t, lim,
		byIntDesc(func(i int) int { return int(t.Rows[i][2].i) }),
		byIntDesc(func(i int) int { return int(t.Rows[i][1].i) }))
	return t
}

func m6(g *Graph, mod string, lim int) *Table {
	t := &Table{Cols: []string{"name", "class_", "deletes", "arguments_", "with_stmts",
		"dynamic_props", "computed", "fan_in", "depth", "at"}}
	eachSym(g, fNotTest, mod, func(id int) {
		del, arg, wth := g.Syms.at(id, cNDELETE), g.Syms.at(id, cNARGUMENTS), g.Syms.at(id, cNWITHSTMT)
		if del+arg+wth <= 0 {
			return
		}
		fid, depth, fin := g.Syms.at(id, cFILEID), g.Syms.at(id, cMAXLOOPDEPTH), g.Syms.at(id, cFANIN)
		weight := (wth*4 + del*2 + arg) * (1 + fin) * (1 + depth)
		t.add(S(g.Syms.scol(id, cNAME)), S(g.Syms.scol(id, cCLASSNAME)), I32(del),
			I32(arg), I32(wth), I32(g.Syms.at(id, cNDYNAMICPROP)),
			I32(g.Syms.at(id, cNCOMPUTEDMEMBER)), I32(fin), I32(depth),
			S(g.atLine(fid, g.Syms.at(id, cLINESTART))))
		_ = weight
		weights = append(weights, weight)
	})

	weights = weights[:len(t.Rows)]
	take(t, lim, byIntDesc(func(i int) int { return int(weights[i]) }))
	return t
}

var weights []int32

func m7(g *Graph, mod string, lim int) *Table {
	t := &Table{Cols: []string{"name", "class_", "spreads", "inline_objs", "depth",
		"destructures", "allocs_in_loop", "fan_in", "at"}}
	var w []int32
	eachSym(g, fNotTest, mod, func(id int) {
		sp := g.Syms.at(id, cNSPREAD)
		depth := g.Syms.at(id, cMAXLOOPDEPTH)
		if !(sp > 0 && depth > 0) {
			return
		}
		fid, fin := g.Syms.at(id, cFILEID), g.Syms.at(id, cFANIN)
		t.add(S(g.Syms.scol(id, cNAME)), S(g.Syms.scol(id, cCLASSNAME)), I32(sp),
			I32(g.Syms.at(id, cNINLINEOBJECTPROP)), I32(depth),
			I32(g.Syms.at(id, cNDESTRUCTURE)), I32(g.Syms.at(id, cALLOCINLOOP)),
			I32(fin), S(g.atLine(fid, g.Syms.at(id, cLINESTART))))
		w = append(w, sp*depth*(1+fin))
	})
	take(t, lim, byIntDesc(func(i int) int { return int(w[i]) }))
	return t
}

func m8(g *Graph, mod string, lim int) *Table {
	t := &Table{Cols: []string{"name", "fan_in", "sites", "fan_out", "cyclo", "sloc",
		"kind", "module_", "at"}}
	eachSym(g, fAny, mod, func(id int) {
		if g.Syms.at(id, cFANIN) <= 0 {
			return
		}
		fid := g.Syms.at(id, cFILEID)
		t.add(S(g.Syms.scol(id, cNAME)), I32(g.Syms.at(id, cFANIN)),
			I32(g.Syms.at(id, cNCALLSITES)), I32(g.Syms.at(id, cFANOUT)),
			I32(g.Syms.at(id, cCYCLOMATIC)), I32(g.Syms.at(id, cSLOC)),
			S(g.Syms.scol(id, cKIND)), S(g.modName(g.Syms.at(id, cMODULEID))),
			S(g.atLine(fid, g.Syms.at(id, cLINESTART))))
	})
	take(t, lim,
		byIntDesc(func(i int) int { return int(t.Rows[i][1].i) }),
		byIntDesc(func(i int) int { return int(t.Rows[i][4].i) }))
	return t
}

func m9(g *Graph, mod string, lim int) *Table {
	return simpleSym(g, mod, lim,
		[]string{"name", "risk", "cyclo", "cog", "nest", "hazards", "fan_in", "sloc", "at"},
		fNotGen,
		func(id int) bool { return g.Syms.at(id, cRISKSCORE) > 0 },
		func(t *Table, id int) {
			fid := g.Syms.at(id, cFILEID)
			t.add(S(g.Syms.scol(id, cNAME)), I32(g.Syms.at(id, cRISKSCORE)),
				I32(g.Syms.at(id, cCYCLOMATIC)), I32(g.Syms.at(id, cCOGNITIVE)),
				I32(g.Syms.at(id, cMAXNESTING)), I32(g.Syms.at(id, cNHAZARDS)),
				I32(g.Syms.at(id, cFANIN)), I32(g.Syms.at(id, cSLOC)),
				S(g.atLine(fid, g.Syms.at(id, cLINESTART))))
		},
		func(t *Table) []orderTerm {
			return []orderTerm{byIntDesc(func(i int) int { return int(t.Rows[i][1].i) })}
		})
}

func m10(g *Graph, mod string, lim int) *Table {
	t := &Table{Cols: []string{"name", "search_in_loop", "array_grow_in_loop",
		"assign_in_loop", "then_in_loop", "loop_depth", "cyclo", "fan_in",
		"distinct_callers", "at"}}
	callers := map[int32]map[int32]bool{}
	for i := range g.Edges {
		if g.Edges[i].isSelf {
			continue
		}
		m := callers[g.Edges[i].callee]
		if m == nil {
			m = map[int32]bool{}
			callers[g.Edges[i].callee] = m
		}
		m[g.Edges[i].caller] = true
	}
	eachSym(g, fNotTest, mod, func(id int) {
		if !(g.Syms.at(id, cNSEARCHINLOOP) > 0 || g.Syms.at(id, cNARRAYGROWINLOOP) > 0) {
			return
		}
		fid := g.Syms.at(id, cFILEID)
		t.add(S(g.Syms.scol(id, cNAME)), I32(g.Syms.at(id, cNSEARCHINLOOP)),
			I32(g.Syms.at(id, cNARRAYGROWINLOOP)), I32(g.Syms.at(id, cNASSIGNINLOOP)),
			I32(g.Syms.at(id, cNTHENINLOOP)), I32(g.Syms.at(id, cMAXLOOPDEPTH)),
			I32(g.Syms.at(id, cCYCLOMATIC)), I32(g.Syms.at(id, cFANIN)),
			I32(int32(len(callers[int32(id+1)]))),
			S(g.atLine(fid, g.Syms.at(id, cLINESTART))))
	})
	take(t, lim,
		byIntDesc(func(i int) int { return int(t.Rows[i][8].i) }),
		byIntDesc(func(i int) int { return int(t.Rows[i][1].i) }),
		byIntDesc(func(i int) int { return int(t.Rows[i][5].i) }))
	return t
}

func m11(g *Graph, mod string, lim int) *Table {
	return simpleSym(g, mod, lim,
		[]string{"name", "nesting", "cyclo", "cognitive", "callbacks", "closures",
			"sloc", "fan_in", "at"}, fNotTest,
		func(id int) bool {
			k := g.Syms.scol(id, cKIND)
			return g.Syms.at(id, cMAXNESTING) > 4 && (k == "function" || k == "method")
		},
		func(t *Table, id int) {
			fid := g.Syms.at(id, cFILEID)
			t.add(S(g.Syms.scol(id, cNAME)), I32(g.Syms.at(id, cMAXNESTING)),
				I32(g.Syms.at(id, cCYCLOMATIC)), I32(g.Syms.at(id, cCOGNITIVE)),
				I32(g.Syms.at(id, cNCALLBACKS)), I32(g.Syms.at(id, cNCLOSURES)),
				I32(g.Syms.at(id, cSLOC)), I32(g.Syms.at(id, cFANIN)),
				S(g.atLine(fid, g.Syms.at(id, cLINESTART))))
		},
		func(t *Table) []orderTerm {
			return []orderTerm{
				byIntDesc(func(i int) int { return int(t.Rows[i][1].i) }),
				byIntDesc(func(i int) int { return int(t.Rows[i][2].i) })}
		})
}

func m12(g *Graph, mod string, lim int) *Table {
	return simpleSym(g, mod, lim,
		[]string{"name", "n_params", "n_optional_params", "destructured", "sloc",
			"cyclo", "fan_in", "at"}, fNotTest,
		func(id int) bool {
			k := g.Syms.scol(id, cKIND)
			return g.Syms.at(id, cNPARAMS) > 4 && (k == "function" || k == "method")
		},
		func(t *Table, id int) {
			fid := g.Syms.at(id, cFILEID)
			t.add(S(g.Syms.scol(id, cNAME)), I32(g.Syms.at(id, cNPARAMS)),
				I32(g.Syms.at(id, cNOPTIONALPARAMS)), I32(g.Syms.at(id, cNDESTRUCTURE)),
				I32(g.Syms.at(id, cSLOC)), I32(g.Syms.at(id, cCYCLOMATIC)),
				I32(g.Syms.at(id, cFANIN)),
				S(g.atLine(fid, g.Syms.at(id, cLINESTART))))
		},
		func(t *Table) []orderTerm {
			return []orderTerm{
				byIntDesc(func(i int) int { return int(t.Rows[i][1].i) }),
				byIntDesc(func(i int) int { return int(t.Rows[i][6].i) })}
		})
}

func m13(g *Graph, mod string, lim int) *Table {
	t := &Table{Cols: []string{"name", "n_caller_modules", "fan_in", "cyclo", "sloc",
		"modules", "at"}}
	type acc struct {
		mods map[int32]string
	}
	agg := map[int32]*acc{}
	for i := range g.Edges {
		e := &g.Edges[i]
		if e.isSelf {
			continue
		}
		a := agg[e.callee]
		if a == nil {
			a = &acc{map[int32]string{}}
			agg[e.callee] = a
		}
		mid := g.Syms.at(int(e.caller)-1, cMODULEID)
		a.mods[mid] = g.modName(mid)
	}

	callees := make([]int32, 0, len(agg))
	for callee := range agg {
		callees = append(callees, callee)
	}
	slices.Sort(callees)
	for _, callee := range callees {
		a := agg[callee]
		if len(a.mods) <= 5 {
			continue
		}
		id := int(callee) - 1
		k := g.Syms.scol(id, cKIND)
		if k != "function" && k != "method" {
			continue
		}
		fl := &g.Files[g.Syms.at(id, cFILEID)-1]
		if fl.isTest {
			continue
		}

		var names []string
		seen := map[int32]bool{}
		for mid := range a.mods {
			if seen[mid] {
				continue
			}
			seen[mid] = true
			if likeMatch(mod, a.mods[mid]) {
				names = append(names, a.mods[mid])
			}
		}
		if len(names) == 0 {
			continue
		}

		t.add(S(g.Syms.scol(id, cNAME)), I32(int32(len(a.mods))), I32(g.Syms.at(id, cFANIN)),
			I32(g.Syms.at(id, cCYCLOMATIC)), I32(g.Syms.at(id, cSLOC)),
			S(groupConcatDistinct(names)),
			S(g.atLine(fl.id, g.Syms.at(id, cLINESTART))))
	}
	take(t, lim,
		byIntDesc(func(i int) int { return int(t.Rows[i][1].i) }),
		byIntDesc(func(i int) int { return int(t.Rows[i][2].i) }))
	return t
}

func m14(g *Graph, mod string, lim int) *Table {
	return simpleSym(g, mod, lim,
		[]string{"name", "cyclo", "jsx_elements", "hooks", "setstates",
			"conditional_hooks", "sloc", "fan_in", "at"}, fNotTest,
		func(id int) bool {
			return g.Syms.at(id, cISCOMPONENT) == 1 && g.Syms.at(id, cCYCLOMATIC) > 10
		},
		func(t *Table, id int) {
			fid := g.Syms.at(id, cFILEID)
			t.add(S(g.Syms.scol(id, cNAME)), I32(g.Syms.at(id, cCYCLOMATIC)),
				I32(g.Syms.at(id, cNJSXELEMENTS)), I32(g.Syms.at(id, cNHOOKS)),
				I32(g.Syms.at(id, cNSETSTATE)),
				I32(g.Syms.at(id, cNHOOKSCONDITIONAL)),
				I32(g.Syms.at(id, cSLOC)), I32(g.Syms.at(id, cFANIN)),
				S(g.atLine(fid, g.Syms.at(id, cLINESTART))))
		},
		func(t *Table) []orderTerm {
			return []orderTerm{
				byIntDesc(func(i int) int { return int(t.Rows[i][1].i) }),
				byIntDesc(func(i int) int { return int(t.Rows[i][2].i) })}
		})
}

func m15(g *Graph, mod string, lim int) *Table {
	t := &Table{Cols: []string{"module_", "fns", "async_fns", "pct_async", "awaits",
		"awaits_in_loop", "then_links", "catch_handlers", "batches"}}
	type acc struct{ v [8]int64 }
	agg := map[int32]*acc{}
	for id := 0; id < g.nSym(); id++ {
		fl := &g.Files[g.Syms.at(id, cFILEID)-1]
		if !fl.clean() {
			continue
		}
		mid := g.Syms.at(id, cMODULEID)
		if mid == 0 || !likeMatch(mod, g.Modules[mid-1].Name(g)) || !isFnKind(g.Syms.scol(id, cKIND)) {
			continue
		}
		a := agg[mid]
		if a == nil {
			a = &acc{}
			agg[mid] = a
		}
		a.v[0]++
		a.v[1] += int64(g.Syms.at(id, cISASYNC))
		a.v[2] += int64(g.Syms.at(id, cNAWAIT))
		a.v[3] += int64(g.Syms.at(id, cAWAITINLOOP))
		a.v[4] += int64(g.Syms.at(id, cNPROMISECHAIN))
		a.v[5] += int64(g.Syms.at(id, cNCATCHHANDLER))
		a.v[6] += int64(g.Syms.at(id, cNPROMISEALL))
	}
	for _, mid := range sortedIDs(agg) {
		a := agg[mid]
		pct := int64(0)
		if a.v[0] != 0 {
			pct = int64(100.0 * float64(a.v[1]) / float64(a.v[0]))
		}
		t.add(S(g.Modules[mid-1].Name(g)), I64(a.v[0]), I64(a.v[1]), I64(pct),
			I64(a.v[2]), I64(a.v[3]), I64(a.v[4]), I64(a.v[5]), I64(a.v[6]))
	}
	take(t, lim,
		byIntDesc(func(i int) int { return int(t.Rows[i][2].i) }),
		byIntDesc(func(i int) int { return int(t.Rows[i][6].i) }))
	return t
}

func m16(g *Graph, mod string, lim int) *Table {
	t := &Table{Cols: []string{"module_", "throws_", "try_blocks", "catch_blocks",
		"empty_catches", "pct_paired"}}
	type acc struct{ v [4]int64 }
	agg := map[int32]*acc{}
	for id := 0; id < g.nSym(); id++ {
		fl := &g.Files[g.Syms.at(id, cFILEID)-1]
		if !fl.clean() {
			continue
		}
		mid := g.Syms.at(id, cMODULEID)
		if mid == 0 || !likeMatch(mod, g.Modules[mid-1].Name(g)) || !isFnKind(g.Syms.scol(id, cKIND)) {
			continue
		}
		a := agg[mid]
		if a == nil {
			a = &acc{}
			agg[mid] = a
		}
		a.v[0] += int64(g.Syms.at(id, cNTHROW))
		a.v[1] += int64(g.Syms.at(id, cNTRY))
		a.v[2] += int64(g.Syms.at(id, cNCATCH))
		a.v[3] += int64(g.Syms.at(id, cNCATCHEMPTY))
	}
	for _, mid := range sortedIDs(agg) {
		a := agg[mid]
		if a.v[0] <= 0 {
			continue
		}
		m := min(a.v[0], a.v[2])
		pct := int64(0)
		if a.v[0] != 0 {
			pct = int64(100.0 * float64(m) / float64(a.v[0]))
		}
		t.add(S(g.Modules[mid-1].Name(g)), I64(a.v[0]), I64(a.v[1]), I64(a.v[2]),
			I64(a.v[3]), I64(pct))
	}
	take(t, lim,
		byIntDesc(func(i int) int { return int(t.Rows[i][1].i) }),
		byIntDesc(func(i int) int { return int(t.Rows[i][4].i) }))
	return t
}

func m17(g *Graph, mod string, lim int) *Table {
	t := &Table{Cols: []string{"module_", "sync_calls", "sync_fs", "exec_calls",
		"json_ops", "io_in_loop", "child_process", "blocking_weight"}}
	type acc struct{ v [6]int64 }
	agg := map[int32]*acc{}
	for id := 0; id < g.nSym(); id++ {
		fl := &g.Files[g.Syms.at(id, cFILEID)-1]
		if !fl.clean() {
			continue
		}
		mid := g.Syms.at(id, cMODULEID)
		if mid == 0 || !likeMatch(mod, g.Modules[mid-1].Name(g)) {
			continue
		}
		a := agg[mid]
		if a == nil {
			a = &acc{}
			agg[mid] = a
		}
		a.v[0] += int64(g.Syms.at(id, cNSYNCCALLS))
		a.v[1] += int64(g.Syms.at(id, cNFSSYNC))
		a.v[2] += int64(g.Syms.at(id, cNEXEC))
		a.v[3] += int64(g.Syms.at(id, cNJSONPARSE))
		a.v[4] += int64(g.Syms.at(id, cIOINLOOP))
		a.v[5] += int64(g.Syms.at(id, cNCHILDPROCESS))
	}
	for _, mid := range sortedIDs(agg) {
		a := agg[mid]
		w := a.v[0]*3 + a.v[1]*2 + a.v[2]*2 + a.v[3]
		if w <= 0 {
			continue
		}
		t.add(S(g.Modules[mid-1].Name(g)), I64(a.v[0]), I64(a.v[1]), I64(a.v[2]),
			I64(a.v[3]), I64(a.v[4]), I64(a.v[5]), I64(w))
	}
	take(t, lim, byIntDesc(func(i int) int { return int(t.Rows[i][7].i) }))
	return t
}

func m18(g *Graph, mod string, lim int) *Table {
	t := &Table{Cols: []string{"module_", "env_reads", "reader_fns",
		"handlers_reading_env", "entry_readers"}}
	type acc struct {
		reads                   int64
		readers, handlers, ents map[int32]bool
	}
	agg := map[int32]*acc{}
	for id := 0; id < g.nSym(); id++ {
		fl := &g.Files[g.Syms.at(id, cFILEID)-1]
		if !fl.clean() {
			continue
		}
		mid := g.Syms.at(id, cMODULEID)
		if mid == 0 || !likeMatch(mod, g.Modules[mid-1].Name(g)) {
			continue
		}
		a := agg[mid]
		if a == nil {
			a = &acc{reads: 0, readers: map[int32]bool{},
				handlers: map[int32]bool{}, ents: map[int32]bool{}}
			agg[mid] = a
		}
		if g.Syms.at(id, cNENVREAD) <= 0 {
			continue
		}
		a.reads += int64(g.Syms.at(id, cNENVREAD))
		a.readers[int32(id+1)] = true
		if g.Syms.at(id, cISHANDLER) == 1 {
			a.handlers[int32(id+1)] = true
		}
		if g.Syms.at(id, cISENTRYPOINT) == 1 {
			a.ents[int32(id+1)] = true
		}
	}
	for _, mid := range sortedIDs(agg) {
		a := agg[mid]
		if a.reads <= 0 {
			continue
		}
		t.add(S(g.Modules[mid-1].Name(g)), I64(a.reads), I64(int64(len(a.readers))),
			I64(int64(len(a.handlers))), I64(int64(len(a.ents))))
	}
	t.take([]orderTerm{
		byIntDesc(func(i int) int { return int(t.Rows[i][1].i) }),
		byIntDesc(func(i int) int { return int(t.Rows[i][3].i) }),
	}, lim)
	return t
}

func m19(g *Graph, mod string, lim int) *Table {
	t := &Table{Cols: []string{"module_", "adds", "removes", "inline_anon", "at_scope",
		"in_loop", "unbalanced"}}
	type acc struct{ adds, removes, inline, scope, loop int64 }
	agg := map[int32]*acc{}
	for i := range g.Listeners {
		l := &g.Listeners[i]
		fl := &g.Files[l.fileID-1]
		if fl.isTest {
			continue
		}
		a := agg[fl.moduleID]
		if a == nil {
			a = &acc{}
			agg[fl.moduleID] = a
		}
		switch l.Op(g) {
		case "add":
			a.adds++
			if l.inline && !l.signal {
				a.inline++
			}
			if l.atModule {
				a.scope++
			}
			if l.inLoop {
				a.loop++
			}
		case "remove":
			a.removes++
		}
	}
	for _, mid := range sortedIDs(agg) {
		a := agg[mid]
		if !likeMatch(mod, g.modName(mid)) {
			continue
		}
		un := max(a.adds-a.removes, 0)
		t.add(S(g.modName(mid)), I64(a.adds), I64(a.removes), I64(a.inline),
			I64(a.scope), I64(a.loop), I64(un))
	}
	take(t, lim,
		byIntDesc(func(i int) int { return int(t.Rows[i][6].i) }),
		byIntDesc(func(i int) int { return int(t.Rows[i][3].i) }))
	return t
}

func m20(g *Graph, mod string, lim int) *Table {
	t := &Table{Cols: []string{"module_", "query_reads", "body_reads", "header_reads",
		"cookie_reads", "form_reads", "path_reads", "fns_reading_input",
		"files_reading_input"}}
	type acc struct {
		v          [6]int64
		fns, files map[int32]bool
	}
	agg := map[int32]*acc{}
	kinds := []string{"query", "body", "header", "cookie", "form", "path"}
	for i := range g.UserInput {
		u := &g.UserInput[i]
		fl := &g.Files[u.fileID-1]
		if fl.isTest {
			continue
		}
		mid := fl.moduleID
		if !likeMatch(mod, g.modName(mid)) {
			continue
		}
		a := agg[mid]
		if a == nil {
			a = &acc{fns: map[int32]bool{}, files: map[int32]bool{}}
			agg[mid] = a
		}
		for k, kind := range kinds {
			if u.Kind(g) == kind {
				a.v[k]++
			}
		}
		if u.symID != 0 {
			a.fns[u.symID] = true
		}
		a.files[u.fileID] = true
	}
	for _, mid := range sortedIDs(agg) {
		a := agg[mid]
		t.add(S(g.modName(mid)), I64(a.v[0]), I64(a.v[1]), I64(a.v[2]), I64(a.v[3]),
			I64(a.v[4]), I64(a.v[5]), I64(int64(len(a.fns))), I64(int64(len(a.files))))
	}
	take(t, lim,
		byIntDesc(func(i int) int { return int(t.Rows[i][7].i) }),
		byIntDesc(func(i int) int { return int(t.Rows[i][2].i) }))
	return t
}

func m21(g *Graph, mod string, lim int) *Table {
	return simpleSym(g, mod, lim,
		[]string{"name", "chain_links", "then_sites", "handlers", "awaits",
			"then_in_loop", "fan_in", "at"}, fNotTestGen,
		func(id int) bool {
			return g.Syms.at(id, cNPROMISECHAIN) >= 2 && isFnKind(g.Syms.scol(id, cKIND))
		},
		func(t *Table, id int) {
			fid := g.Syms.at(id, cFILEID)
			t.add(S(g.Syms.scol(id, cNAME)), I32(g.Syms.at(id, cNPROMISECHAIN)),
				I32(g.Syms.at(id, cNTHEN)), I32(g.Syms.at(id, cNCATCHHANDLER)),
				I32(g.Syms.at(id, cNAWAIT)), I32(g.Syms.at(id, cNTHENINLOOP)),
				I32(g.Syms.at(id, cFANIN)),
				S(g.atLine(fid, g.Syms.at(id, cLINESTART))))
		},
		func(t *Table) []orderTerm {
			return []orderTerm{
				byIntDesc(func(i int) int { return int(t.Rows[i][1].i) }),
				byIntDesc(func(i int) int { return int(t.Rows[i][2].i) }),
				byIntDesc(func(i int) int { return int(t.Rows[i][6].i) })}
		})
}

func m22(g *Graph, mod string, lim int) *Table {
	t := &Table{Cols: []string{"name", "callback_args", "closures", "lambdas", "nest",
		"indirection", "fan_in", "cyclo", "at"}}
	var w []int32
	eachSym(g, fNotTestGen, mod, func(id int) {
		k := g.Syms.scol(id, cKIND)
		if !(g.Syms.at(id, cNCALLBACKS) >= 3 && (k == "function" || k == "method")) {
			return
		}
		fid, nest := g.Syms.at(id, cFILEID), g.Syms.at(id, cMAXNESTING)
		t.add(S(g.Syms.scol(id, cNAME)), I32(g.Syms.at(id, cNCALLBACKS)),
			I32(g.Syms.at(id, cNCLOSURES)), I32(g.Syms.at(id, cNLAMBDA)),
			I32(nest), I32(g.Syms.at(id, cNCALLBACKS)*(1+nest)),
			I32(g.Syms.at(id, cFANIN)), I32(g.Syms.at(id, cCYCLOMATIC)),
			S(g.atLine(fid, g.Syms.at(id, cLINESTART))))
		w = append(w, g.Syms.at(id, cNCALLBACKS)*(1+nest))
	})
	take(t, lim,
		byIntDesc(func(i int) int { return int(w[i]) }),
		byIntDesc(func(i int) int { return int(t.Rows[i][1].i) }))
	return t
}

func m23(g *Graph, mod string, lim int) *Table {
	t := &Table{Cols: []string{"module_", "fns", "unreferenced", "test_only",
		"pct_prod_reachable"}}
	prod := map[int32]map[int32]bool{}
	for i := range g.Edges {
		e := &g.Edges[i]
		if e.isSelf {
			continue
		}
		cid := int(e.caller) - 1
		if g.Files[g.Syms.at(cid, cFILEID)-1].isTest || g.Syms.at(cid, cISTEST) == 1 {
			continue
		}
		m := prod[e.callee]
		if m == nil {
			m = map[int32]bool{}
			prod[e.callee] = m
		}
		m[e.caller] = true
	}
	type acc struct {
		fns, unref, testOnly, reach int64
	}
	agg := map[int32]*acc{}
	for id := 0; id < g.nSym(); id++ {
		if !isFnKind(g.Syms.scol(id, cKIND)) {
			continue
		}
		fl := &g.Files[g.Syms.at(id, cFILEID)-1]
		if !fl.clean() {
			continue
		}
		mid := g.Syms.at(id, cMODULEID)
		if mid == 0 || !likeMatch(mod, g.Modules[mid-1].Name(g)) {
			continue
		}
		a := agg[mid]
		if a == nil {
			a = &acc{}
			agg[mid] = a
		}
		a.fns++
		p := len(prod[int32(id+1)])
		fin := g.Syms.at(id, cFANIN)
		switch {
		case p == 0 && fin == 0:
			a.unref++
		case p == 0 && fin > 0:
			a.testOnly++
		}
		if p > 0 {
			a.reach++
		}
	}
	for _, mid := range sortedIDs(agg) {
		a := agg[mid]
		pct := int64(0)
		if a.fns != 0 {
			pct = int64(100.0 * float64(a.reach) / float64(a.fns))
		}
		t.add(S(g.Modules[mid-1].Name(g)), I64(a.fns), I64(a.unref), I64(a.testOnly),
			I64(pct))
	}
	take(t, lim,
		byInt(func(i int) int { return int(t.Rows[i][4].i) }),
		byIntDesc(func(i int) int { return int(t.Rows[i][3].i) }))
	return t
}

func m24(g *Graph, mod string, lim int) *Table {
	t := &Table{Cols: []string{"module_", "imports_internal", "imported_by_files",
		"external_packages", "coupling"}}
	filesOf := map[int32]map[int32]bool{}
	targetsOf := map[int32]map[int32]bool{}
	extPkgs := map[int32]map[string]bool{}
	for i := range g.Imports {
		im := &g.Imports[i]
		sf := &g.Files[im.fileID-1]
		if sf.isTest {
			continue
		}
		if im.isExternal != 0 {
			m, ok := extPkgs[sf.moduleID]
			if !ok {
				m = map[string]bool{}
				extPkgs[sf.moduleID] = m
			}
			m[g.s(im.target)] = true
			continue
		}
		if im.targetID == 0 {
			continue
		}
		tf := &g.Files[im.targetID-1]
		m, ok := targetsOf[sf.moduleID]
		if !ok {
			m = map[int32]bool{}
			targetsOf[sf.moduleID] = m
		}
		m[im.targetID] = true

		if tf.isTest {
			continue
		}
		fm, ok := filesOf[tf.moduleID]
		if !ok {
			fm = map[int32]bool{}
			filesOf[tf.moduleID] = fm
		}
		fm[im.fileID] = true
	}
	for i := range g.Modules {
		m := &g.Modules[i]
		if !likeMatch(mod, m.Name(g)) || m.Kind(g) != "source" {
			continue
		}
		ii := len(targetsOf[m.id])
		ibf := len(filesOf[m.id])
		ep := len(extPkgs[m.id])
		t.add(S(g.s(m.name)), I64(int64(ii)), I64(int64(ibf)), I64(int64(ep)), I64(int64(ii+ibf)))
	}
	take(t, lim,
		byIntDesc(func(i int) int { return int(t.Rows[i][4].i) }),
		byIntDesc(func(i int) int { return int(t.Rows[i][3].i) }))
	return t
}

func m25(g *Graph, mod string, lim int) *Table {
	t := &Table{Cols: []string{"method", "path", "middlewares", "handler", "inline",
		"module_", "at"}}
	for i := range g.Routes {
		r := &g.Routes[i]
		if r.nMw <= 0 {
			continue
		}
		fl := &g.Files[r.fileID-1]
		if fl.isTest || !likeMatch(mod, g.modName(fl.moduleID)) {
			continue
		}
		t.add(S(g.s(r.method)), S(g.s(r.path)), I32(r.nMw), S(g.s(r.handler)),
			I32(b2i(r.inline)), S(g.modName(fl.moduleID)),
			S(g.at(r.fileID, r.line)))
	}
	take(t, lim,
		byIntDesc(func(i int) int { return int(t.Rows[i][2].i) }),
		byInt(func(i int) int { return int(findColon(t.Rows[i][6].s)) }))
	return t
}

func m26(g *Graph, mod string, lim int) *Table {
	t := &Table{Cols: []string{"module_", "routes_", "get_", "post_", "put_patch",
		"delete_", "middleware_mounts", "async_handlers", "files_"}}
	type acc struct{ v [7]int64 }
	agg := map[int32]*acc{}
	files := map[int32]map[int32]bool{}
	for i := range g.Routes {
		r := &g.Routes[i]
		fl := &g.Files[r.fileID-1]
		if fl.isTest {
			continue
		}
		mid := fl.moduleID
		if !likeMatch(mod, g.modName(mid)) {
			continue
		}
		a := agg[mid]
		if a == nil {
			a = &acc{}
			agg[mid] = a
			files[mid] = map[int32]bool{}
		}
		a.v[0]++
		switch r.Method(g) {
		case "get":
			a.v[1]++
		case "post":
			a.v[2]++
		case "put", "patch":
			a.v[3]++
		case "delete":
			a.v[4]++
		case "use":
			a.v[5]++
		}
		if r.async {
			a.v[6]++
		}
		files[mid][r.fileID] = true
	}
	for _, mid := range sortedIDs(agg) {
		a := agg[mid]
		t.add(S(g.modName(mid)), I64(a.v[0]), I64(a.v[1]), I64(a.v[2]), I64(a.v[3]),
			I64(a.v[4]), I64(a.v[5]), I64(a.v[6]), I64(int64(len(files[mid]))))
	}
	take(t, lim,
		byIntDesc(func(i int) int { return int(t.Rows[i][1].i) }),
		byIntDesc(func(i int) int { return int(t.Rows[i][6].i) }))
	return t
}

var _ = strings.Contains

func printReport(g *Graph) {
	w := bufio.NewWriterSize(stdout(), 1<<16)
	defer w.Flush()
	line := func(s string) { fmt.Fprintln(w, s) }

	rule := func(title string) {
		line("")
		line(strings.Repeat("=", 78))
		line(title)
		line(strings.Repeat("-", 78))
	}

	rule("OVERVIEW")

	line(fmt.Sprintf(" %-14s %s", "grammar", grammarVersion))
	for _, k := range []string{"lang", "target", "root"} {
		if v := g.metaGet(k); v != "" {
			line(fmt.Sprintf(" %-14s %s", k, v))
		}
	}
	parsed := 0
	sloc := int32(0)
	for i := range g.Files {
		if g.Files[i].parsed {
			parsed++
			sloc += g.Files[i].sloc
		}
	}
	line(fmt.Sprintf(" %-14s %d catalogued, %d parsed, %d sloc", "files",
		len(g.Files), parsed, sloc))
	kinds := map[string]int{}
	for id := 0; id < g.nSym(); id++ {
		kinds[g.Syms.scol(id, cKIND)]++
	}
	type kv struct {
		k string
		n int
	}
	var ks []kv
	for _, k := range sortedNames(kinds) {
		ks = append(ks, kv{k, kinds[k]})
	}

	sort.SliceStable(ks, func(i, j int) bool {
		if ks[i].n != ks[j].n {
			return ks[i].n > ks[j].n
		}
		return ks[i].k < ks[j].k
	})
	if len(ks) > 12 {
		ks = ks[:12]
	}
	parts := make([]string, 0, len(ks))
	for _, e := range ks {
		parts = append(parts, fmt.Sprintf("%s=%d", e.k, e.n))
	}
	line(fmt.Sprintf(" %-14s %s", "symbols", strings.Join(parts, ", ")))
	totCalls, unres := int32(0), int32(0)
	for id := 0; id < g.nSym(); id++ {
		totCalls += g.Syms.at(id, cNCALLS)
	}
	for i := range g.Unresolved {
		unres += g.Unresolved[i].n
	}
	line(fmt.Sprintf(" %-14s %d edges, %d call sites, %d unresolved", "call graph",
		len(g.Edges), len(g.Callsites), unres))

	rule("HOW MUCH OF THIS TO TRUST")
	errFiles := 0
	for i := range g.Files {
		if g.Files[i].nParseErrors > 0 {
			errFiles++
		}
	}
	if parsed == 0 {
		line(" NOTHING WAS PARSED. Every number below is zero because no file")
		line(" was read, not because this repository is empty or clean.")
	}
	line(fmt.Sprintf(" %-30s %d file(s)", "files with parse errors", errFiles))
	if totCalls > 0 {
		line(fmt.Sprintf(" %-30s %d of %d call sites (%d%%)",
			"calls we could NOT resolve", unres, totCalls,
			100*unres/totCalls))
	} else {
		line(" no calls were recorded at all -- this is the absence of")
		line(" call resolution data, not a clean result")
	}
	line(" A high unresolved share means the call-graph queries below see less")
	line(" than they imply. `v_blindspot` lists exactly where.")

	rule("BIGGEST MODULES")
	mods := make([]Module, len(g.Modules))
	copy(mods, g.Modules)
	sort.SliceStable(mods, func(i, j int) bool {
		if mods[i].sloc != mods[j].sloc {
			return mods[i].sloc > mods[j].sloc
		}
		return mods[i].id < mods[j].id
	})
	t := &Table{Cols: []string{"name", "files", "sloc", "syms", "instab"}}
	n := 0
	for i := range mods {
		m := &mods[i]
		if m.nFiles <= 0 {
			continue
		}
		t.add(S(g.s(m.name)), I32(m.nFiles), I32(m.sloc), I32(m.nSymbols), F(m.instability))
		n++
		if n == 12 {
			break
		}
	}
	render(w, t)

	rule("HEAVIEST FUNCTIONS")
	heavy := append([]int32(nil), g.heavyFuncs(12)...)
	t = &Table{Cols: []string{"name", "sloc", "cyclo", "cog", "nest", "fan_in", "at"}}
	for _, id := range heavy {
		k := int(id) - 1
		fid := g.Syms.at(k, cFILEID)
		t.add(S(g.Syms.scol(k, cNAME)), I32(g.Syms.at(k, cSLOC)),
			I32(g.Syms.at(k, cCYCLOMATIC)), I32(g.Syms.at(k, cCOGNITIVE)),
			I32(g.Syms.at(k, cMAXNESTING)), I32(g.Syms.at(k, cFANIN)),
			S(g.atLine(fid, g.Syms.at(k, cLINESTART))))
	}
	render(w, t)

	rule("MOST DEPENDED ON")
	hot := append([]int32(nil), g.hotFuncs(12)...)
	t = &Table{Cols: []string{"name", "fan_in", "fan_out", "cyclo", "sloc", "at"}}
	for _, id := range hot {
		k := int(id) - 1
		fid := g.Syms.at(k, cFILEID)
		t.add(S(g.Syms.scol(k, cNAME)), I32(g.Syms.at(k, cFANIN)),
			I32(g.Syms.at(k, cFANOUT)), I32(g.Syms.at(k, cCYCLOMATIC)),
			I32(g.Syms.at(k, cSLOC)),
			S(g.atLine(fid, g.Syms.at(k, cLINESTART))))
	}
	render(w, t)

	rule("MARKERS LEFT IN THE CODE")
	mk := map[string]int{}
	for i := range g.Markers {
		mk[g.s(g.Markers[i].kind)]++
	}
	var ms []kv
	for _, k := range sortedNames(mk) {
		ms = append(ms, kv{k, mk[k]})
	}
	sort.SliceStable(ms, func(i, j int) bool {
		if ms[i].n != ms[j].n {
			return ms[i].n > ms[j].n
		}
		return ms[i].k < ms[j].k
	})
	t = &Table{Cols: []string{"kind", "n"}}
	for _, e := range ms {
		t.add(S(e.k), I(e.n))
	}
	render(w, t)
}

func (g *Graph) fnScanOrder() []int32 {
	files := make([]int, len(g.Files))
	for i := range files {
		files[i] = i
	}
	sort.Slice(files, func(a, b int) bool {
		return g.Files[files[a]].Path(g) < g.Files[files[b]].Path(g)
	})
	var out []int32
	for _, fi := range files {
		syms := g.symsByFile[int32(fi+1)]
		s := append([]int32(nil), syms...)
		sort.SliceStable(s, func(a, b int) bool {
			return g.kind(int(s[a])) < g.kind(int(s[b]))
		})
		for _, id := range s {
			if isFnKind(g.kind(int(id))) {
				out = append(out, id+1)
			}
		}
	}
	return out
}

func (g *Graph) heavyFuncs(n int) []int32 {
	out := g.fnScanOrder()
	sort.SliceStable(out, func(i, j int) bool {
		a, b := int(out[i])-1, int(out[j])-1
		return g.Syms.at(a, cCYCLOMATIC) > g.Syms.at(b, cCYCLOMATIC)
	})
	if len(out) > n {
		out = out[:n]
	}
	return out
}

func (g *Graph) hotFuncs(n int) []int32 {
	out := g.fnScanOrder()
	sort.SliceStable(out, func(i, j int) bool {
		a, b := int(out[i])-1, int(out[j])-1
		return g.Syms.at(a, cFANIN) > g.Syms.at(b, cFANIN)
	})
	if len(out) > n {
		out = out[:n]
	}
	return out
}

func (g *Graph) writeSelf(path string) error {
	f, err := createFile(path)
	if err != nil {
		return err
	}
	defer f.Close()
	w := bufio.NewWriterSize(f, 1<<20)
	fmt.Fprintf(w, "# codegraph-javascript graph, schema v%d, lang=%s\n",
		schemaVer, langName)
	for _, m := range g.Meta {
		fmt.Fprintf(w, "M %s\t%s\n", g.s(m[0]), g.s(m[1]))
	}
	for i := range g.Modules {
		m := &g.Modules[i]
		fmt.Fprintf(w, "U %d\t%s\t%s\t%d\t%d\t%d\t%d\t%d\t%d\t%g\n", m.id, m.Name(g),
			m.Kind(g), m.nFiles, m.nSymbols, m.nPublic, m.sloc, m.fanIn, m.fanOut,
			m.instability)
	}
	for i := range g.Files {
		fp := &g.Files[i]
		fmt.Fprintf(w, "F %d\t%s\t%s\t%s\t%s\t%s\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t"+
			"%s\t%d\t%d\t%d\t%d\t%d\t%d\t%g\t%d\t%d\t%d\t%d\t%d\t%d\t%d\n",
			fp.id, fp.Path(g), fp.Dir(g), fp.Base(g), fp.Ext(g), fp.Lang(g), fp.moduleID, fp.bytes,
			fp.lines, fp.sloc, fp.blank, fp.comment, fp.doc, fp.maxLine, fp.Sha1(g),
			b2i(fp.parsed), b2i(fp.isTest), b2i(fp.isGen), b2i(fp.isVendored),
			fp.nParseErrors, fp.nMissing, fp.parseMS, fp.nSymbols, fp.nFuncs,
			fp.nTypes, fp.nImports, fp.totalCycles, fp.maxCycles, fp.totalRisk)
	}
	for id := 0; id < g.nSym(); id++ {
		w.WriteString("S")
		for c := range numSymCols {
			if colSlot[c] < 0 && c != cID {
				continue
			}
			w.WriteByte('\t')
			if c == cID {
				w.WriteString(strconv.Itoa(id + 1))
			} else if tc := textCol[c]; tc >= 0 {
				w.WriteString(escapeTabs(g.s(g.Syms.pool[g.Syms.ids[id][tc]])))
			} else if c == cMODULEID || c == cPARENTID {
				v := g.Syms.at(id, c)
				if v == 0 {
					w.WriteString("\\N")
				} else {
					w.WriteString(strconv.Itoa(int(v)))
				}
			} else {
				w.WriteString(strconv.Itoa(int(g.Syms.at(id, c))))
			}
		}
		w.WriteByte('\n')
	}
	for i := range g.Edges {
		e := &g.Edges[i]
		fmt.Fprintf(w, "E %d\t%d\t%d\t%d\t%d\t%d\n", e.caller, e.callee, e.nCalls,
			b2i(e.sameFile), b2i(e.sameMod), b2i(e.isSelf))
	}
	for i := range g.Callsites {
		c := &g.Callsites[i]
		fmt.Fprintf(w, "C %d\t%d\t%d\n", c.caller, c.callee, c.line)
	}
	for i := range g.Unresolved {
		u := &g.Unresolved[i]
		fmt.Fprintf(w, "N %d\t%s\t%d\t%d\n", u.caller, escapeTabs(g.s(u.name)), u.n, u.firstLn)
	}
	for i := range g.Params {
		p := &g.Params[i]
		fmt.Fprintf(w, "P %d\t%d\t%s\t%s\t%d\t%d\t%d\n", p.symID, p.pos,
			escapeTabs(g.s(p.name)), escapeTabs(g.s(p.typ)), b2i(p.optional), b2i(p.variadic),
			b2i(p.untyped != 0))
	}
	for i := range g.Imports {
		m := &g.Imports[i]
		tid := "\\N"
		if m.targetID != 0 {
			tid = strconv.Itoa(int(m.targetID))
		}
		fmt.Fprintf(w, "I %d\t%d\t%s\t%s\t%s\t%d\t%d\t%d\t%d\n", m.id, m.fileID,
			escapeTabs(g.s(m.target)), tid, g.s(m.kind), m.line, m.isExternal, m.isRel, m.nNames)
	}
	return w.Flush()
}

func escapeTabs(s string) string {
	if !strings.ContainsAny(s, "\t\n\r") {
		return s
	}
	r := strings.NewReplacer("\t", "\\t", "\n", "\\n", "\r", "\\r")
	return r.Replace(s)
}

const maxCell = 72

func cellText(c Cell) string {
	if c.kind == kNull {
		return "-"
	}
	if c.kind == kFloat {
		s := fmt.Sprintf("%.2f", c.f)
		if len(s) <= maxCell {
			return s
		}
		return s[:maxCell-3] + "..."
	}
	s := c.str()
	if len(s) <= maxCell {
		return s
	}
	return s[:maxCell-3] + "..."
}

func render(w io.Writer, t *Table) {
	if len(t.Rows) == 0 {
		fmt.Fprintln(w, " (no rows)")
		return
	}

	for i, r := range t.Rows {
		if len(r) != len(t.Cols) {
			fmt.Fprintf(os.Stderr, "codegraph-javascript: question row %d has "+
				"%d cells for %d columns\n", i, len(r), len(t.Cols))
		}
	}
	body := make([][]string, len(t.Rows))
	for i, r := range t.Rows {
		n := min(len(r), len(t.Cols))
		body[i] = make([]string, n)
		for j := 0; j < n; j++ {
			body[i][j] = cellText(r[j])
		}
	}
	w2 := make([]int, len(t.Cols))
	for i, col := range t.Cols {
		w2[i] = utf8.RuneCountInString(col)
	}
	for _, r := range body {
		for i, c := range r {
			if n := utf8.RuneCountInString(c); n > w2[i] {
				w2[i] = n
			}
		}
	}
	var b strings.Builder
	b.WriteByte(' ')
	for i, c := range t.Cols {
		if i > 0 {
			b.WriteByte(' ')
		}
		b.WriteString(pad(c, w2[i]))
	}
	b.WriteByte('\n')
	b.WriteByte(' ')
	for i := range t.Cols {
		if i > 0 {
			b.WriteByte(' ')
		}
		b.WriteString(strings.Repeat("-", w2[i]))
	}
	b.WriteByte('\n')
	for _, r := range body {
		b.WriteByte(' ')
		for i, c := range r {
			if i > 0 {
				b.WriteByte(' ')
			}
			b.WriteString(pad(c, w2[i]))
		}
		b.WriteByte('\n')
	}
	io.WriteString(w, b.String())
}

func pad(s string, n int) string {
	d := n - utf8.RuneCountInString(s)
	if d <= 0 {
		return s
	}
	return s + strings.Repeat(" ", d)
}

func writeCSV(w io.Writer, t *Table) {
	var b strings.Builder
	csvRow(&b, t.Cols)
	for _, r := range t.Rows {
		cells := make([]string, len(r))
		for i, c := range r {
			if c.kind == kNull {
				cells[i] = ""
			} else {
				cells[i] = c.str()
			}
		}
		csvRow(&b, cells)
	}
	io.WriteString(w, b.String())
}

func csvRow(b *strings.Builder, cells []string) {
	for i, c := range cells {
		if i > 0 {
			b.WriteByte(',')
		}
		if strings.ContainsAny(c, ",\"\r\n") {
			b.WriteByte('"')
			b.WriteString(strings.ReplaceAll(c, "\"", "\"\""))
			b.WriteByte('"')
		} else {
			b.WriteString(c)
		}
	}
	b.WriteString("\r\n")
}

func writeJSON(w io.Writer, t *Table) {
	var b strings.Builder
	if len(t.Rows) == 0 {
		b.WriteString("[]")
	} else {
		b.WriteString("[\n")
		for ri, r := range t.Rows {
			b.WriteString("  {\n")
			for ci, c := range r {
				b.WriteString("    ")
				b.WriteString(jsonString(t.Cols[ci]))
				b.WriteString(": ")
				b.WriteString(jsonCell(c))
				if ci < len(r)-1 {
					b.WriteByte(',')
				}
				b.WriteByte('\n')
			}
			b.WriteString("  }")
			if ri < len(t.Rows)-1 {
				b.WriteByte(',')
			}
			b.WriteByte('\n')
		}
		b.WriteByte(']')
	}
	b.WriteByte('\n')
	io.WriteString(w, b.String())
}

func jsonCell(c Cell) string {
	switch c.kind {
	case kNull:
		return "null"
	case kInt:
		return strconv.FormatInt(c.i, 10)
	case kFloat:
		return cgReprFloat(c.f)
	}
	return jsonString(c.s)
}

func jsonString(s string) string {
	var b strings.Builder
	b.WriteByte('"')
	for _, r := range s {
		switch r {
		case '"':
			b.WriteString("\\\"")
		case '\\':
			b.WriteString("\\\\")
		case '\n':
			b.WriteString("\\n")
		case '\r':
			b.WriteString("\\r")
		case '\t':
			b.WriteString("\\t")
		case '\b':
			b.WriteString("\\b")
		case '\f':
			b.WriteString("\\f")
		default:
			if r < 0x20 {
				b.WriteString("\\u")
				const hex = "0123456789abcdef"
				b.WriteByte('0')
				b.WriteByte('0')
				b.WriteByte(hex[(r>>4)&0xF])
				b.WriteByte(hex[r&0xF])
			} else if r < 0x7f {
				b.WriteRune(r)
			} else if r < 0x10000 {
				b.WriteString("\\u")
				const hex = "0123456789abcdef"
				b.WriteByte(hex[(r>>12)&0xF])
				b.WriteByte(hex[(r>>8)&0xF])
				b.WriteByte(hex[(r>>4)&0xF])
				b.WriteByte(hex[r&0xF])
			} else {
				b.WriteString("\\u")
				const hex = "0123456789abcdef"
				v := r - 0x10000
				hi := 0xD800 + (v >> 10)
				lo := 0xDC00 + (v & 0x3FF)
				for _, x := range [2]rune{hi, lo} {
					b.WriteByte(hex[(x>>12)&0xF])
					b.WriteByte(hex[(x>>8)&0xF])
					b.WriteByte(hex[(x>>4)&0xF])
					b.WriteByte(hex[x&0xF])
				}
			}
		}
	}
	b.WriteByte('"')
	return b.String()
}

type dumper struct {
	w   *bufio.Writer
	buf []byte
}

func (d *dumper) s(v string) { d.buf = append(d.buf, "s:"...); d.escape(v) }
func (d *dumper) i(v int32) {
	d.buf = append(d.buf, 'i', ':')
	d.buf = strconv.AppendInt(d.buf, int64(v), 10)
}
func (d *dumper) n() { d.buf = append(d.buf, "\\N"...) }
func (d *dumper) f(v float64) {
	d.buf = append(d.buf, 'f', ':')
	d.buf = append(d.buf, cgReprFloat(v)...)
}

func (d *dumper) escape(v string) {
	for i := 0; i < len(v); i++ {
		c := v[i]
		switch c {
		case '\\':
			d.buf = append(d.buf, '\\', '\\')
		case '\n':
			d.buf = append(d.buf, '\\', 'n')
		case '\t':
			d.buf = append(d.buf, '\\', 't')
		case '\r':
			d.buf = append(d.buf, '\\', 'r')
		default:
			if c < 0x20 || c == 0x7F {
				const hex = "0123456789ABCDEF"
				d.buf = append(d.buf, '\\', 'x', hex[c>>4], hex[c&0xF])
			} else {
				d.buf = append(d.buf, c)
			}
		}
	}
}

func (d *dumper) flushBuf() {
	d.w.Write(d.buf)
	d.buf = d.buf[:0]
}

func (d *dumper) table(name string, ncols int, rows []string) {
	d.flushBuf()
	d.w.WriteString("T ")
	d.w.WriteString(name)
	d.w.WriteByte(' ')
	d.w.WriteString(strconv.Itoa(ncols))
	d.w.WriteByte(' ')
	d.w.WriteString(strconv.Itoa(len(rows)))
	d.w.WriteByte('\n')
	sort.Strings(rows)
	for _, r := range rows {
		d.w.WriteString(r)
		d.w.WriteByte('\n')
	}
	d.w.WriteString("E ")
	d.w.WriteString(name)
	d.w.WriteByte('\n')
}

func (d *dumper) row() { d.buf = append(d.buf, 'R', ' ') }

func emit(g *Graph, w io.Writer) {
	d := &dumper{w: bufio.NewWriterSize(w, 1<<20)}
	d.table("attributes", 6, func() []string {
		rows := make([]string, 0, len(g.Attrs))
		for i := range g.Attrs {
			a := &g.Attrs[i]
			d.row()
			d.i(int32(i + 1))
			d.buf = append(d.buf, ' ')
			if a.symID != 0 {
				d.i(a.symID)
			} else {
				d.n()
			}
			d.buf = append(d.buf, ' ')
			d.i(a.fileID)
			d.buf = append(d.buf, ' ')
			d.s(g.s(a.name))
			d.buf = append(d.buf, ' ')
			d.s(g.s(a.args))
			d.buf = append(d.buf, ' ')
			d.i(a.line)
			rows = append(rows, string(d.buf))
			d.buf = d.buf[:0]
		}
		return rows
	}())
	d.table("callsites", 3, func() []string {
		rows := make([]string, 0, len(g.Callsites))
		for i := range g.Callsites {
			c := &g.Callsites[i]
			d.row()
			d.i(c.caller)
			d.buf = append(d.buf, ' ')
			d.i(c.callee)
			d.buf = append(d.buf, ' ')
			d.i(c.line)
			rows = append(rows, string(d.buf))
			d.buf = d.buf[:0]
		}
		return rows
	}())
	d.table("classes", 15, func() []string {
		rows := make([]string, 0, len(g.Classes))
		for i := range g.Classes {
			c := &g.Classes[i]
			d.row()
			d.i(c.symID)
			for _, v := range []int32{c.fileID} {
				d.buf = append(d.buf, ' ')
				d.i(v)
			}
			d.buf = append(d.buf, ' ')
			d.s(g.s(c.extends))
			for _, v := range []int32{c.nMethods, c.nStatic, c.nGetters, c.nSetters,
				c.nPrivate, c.nFields, c.nArrow, c.nComputed, c.hasCtor,
				c.hasStaticBlock, b2i(c.exported), b2i(c.component)} {
				d.buf = append(d.buf, ' ')
				d.i(v)
			}
			rows = append(rows, string(d.buf))
			d.buf = d.buf[:0]
		}
		return rows
	}())
	d.table("deps", 5, func() []string {
		rows := make([]string, 0, len(g.Deps))
		for i := range g.Deps {
			p := &g.Deps[i]
			d.row()
			d.i(int32(i + 1))
			d.buf = append(d.buf, ' ')
			d.s(g.s(p.name))
			d.buf = append(d.buf, ' ')
			d.s(g.s(p.version))
			d.buf = append(d.buf, ' ')
			d.i(p.dev)
			d.buf = append(d.buf, ' ')
			d.s(g.s(p.dir))
			rows = append(rows, string(d.buf))
			d.buf = d.buf[:0]
		}
		return rows
	}())
	d.table("edges", 6, func() []string {
		rows := make([]string, 0, len(g.Edges))
		for i := range g.Edges {
			e := &g.Edges[i]
			d.row()
			d.i(e.caller)
			for _, v := range []int32{e.callee, e.nCalls, b2i(e.sameFile), b2i(e.sameMod), b2i(e.isSelf)} {
				d.buf = append(d.buf, ' ')
				d.i(v)
			}
			rows = append(rows, string(d.buf))
			d.buf = d.buf[:0]
		}
		return rows
	}())
	d.table("enum_members", 5, func() []string {
		rows := make([]string, 0, len(g.Enums))
		for i := range g.Enums {
			c := &g.Enums[i]
			d.row()
			d.i(c.symID)
			d.buf = append(d.buf, ' ')
			d.i(c.ordinal)
			d.buf = append(d.buf, ' ')
			d.s(g.s(c.name))
			d.buf = append(d.buf, ' ')
			if c.valueNull {
				d.n()
			} else {
				d.s(g.s(c.value))
			}
			d.buf = append(d.buf, ' ')
			d.i(c.nFields)
			rows = append(rows, string(d.buf))
			d.buf = d.buf[:0]
		}
		return rows
	}())
	d.table("exports", 12, func() []string {
		rows := make([]string, 0, len(g.Exports))
		for i := range g.Exports {
			c := &g.Exports[i]
			d.row()
			d.i(int32(i + 1))
			d.buf = append(d.buf, ' ')
			d.i(c.fileID)
			d.buf = append(d.buf, ' ')
			if c.symID != 0 {
				d.i(c.symID)
			} else {
				d.n()
			}
			d.buf = append(d.buf, ' ')
			d.s(g.s(c.name))
			d.buf = append(d.buf, ' ')
			d.s(g.s(c.localName))
			d.buf = append(d.buf, ' ')
			d.s(g.s(c.kind))
			d.buf = append(d.buf, ' ')
			d.i(c.line)
			d.buf = append(d.buf, ' ')
			d.s(g.s(c.source))
			d.buf = append(d.buf, ' ')
			if c.sourceID != 0 {
				d.i(c.sourceID)
			} else {
				d.n()
			}
			for _, v := range []int32{b2i(c.reexport), b2i(c.star), b2i(c.cjs)} {
				d.buf = append(d.buf, ' ')
				d.i(v)
			}
			rows = append(rows, string(d.buf))
			d.buf = d.buf[:0]
		}
		return rows
	}())
	d.table("fields", 14, func() []string {
		rows := make([]string, 0, len(g.Fields))
		for i := range g.Fields {
			c := &g.Fields[i]
			d.row()
			d.i(c.symID)
			d.buf = append(d.buf, ' ')
			d.i(c.ordinal)
			d.buf = append(d.buf, ' ')
			d.s(g.s(c.name))
			d.buf = append(d.buf, ' ')
			d.s(g.s(c.typ))
			d.buf = append(d.buf, ' ')
			d.s(g.s(c.vis))
			for _, v := range []int32{c.line, b2i(c.static), b2i(c.konst), b2i(c.mut),
				b2i(c.nullable), b2i(c.coll), b2i(c.untyped), c.hasDefault, c.depth} {
				d.buf = append(d.buf, ' ')
				d.i(v)
			}
			rows = append(rows, string(d.buf))
			d.buf = d.buf[:0]
		}
		return rows
	}())
	d.dumpFiles()
	d.table("hazards", 5, func() []string {
		rows := make([]string, 0, len(g.Hazards))
		for i := range g.Hazards {
			c := &g.Hazards[i]
			d.row()
			d.i(c.symID)
			d.buf = append(d.buf, ' ')
			d.s(g.s(c.pattern))
			d.buf = append(d.buf, ' ')
			d.s(g.s(c.category))
			d.buf = append(d.buf, ' ')
			d.i(c.n)
			d.buf = append(d.buf, ' ')
			d.i(c.firstLine)
			rows = append(rows, string(d.buf))
			d.buf = d.buf[:0]
		}
		return rows
	}())
	d.table("hooks", 13, func() []string {
		rows := make([]string, 0, len(g.Hooks))
		for i := range g.Hooks {
			c := &g.Hooks[i]
			d.row()
			d.i(int32(i + 1))
			d.buf = append(d.buf, ' ')
			d.i(c.fileID)
			d.buf = append(d.buf, ' ')
			if c.symID != 0 {
				d.i(c.symID)
			} else {
				d.n()
			}
			d.buf = append(d.buf, ' ')
			d.i(c.line)
			d.buf = append(d.buf, ' ')
			d.s(g.s(c.name))
			for _, v := range []int32{b2i(c.builtin), b2i(c.hasDeps), c.nDeps,
				b2i(c.cleanup), b2i(c.inLoop), b2i(c.inCond), b2i(c.regListener), b2i(c.regTimer)} {
				d.buf = append(d.buf, ' ')
				d.i(v)
			}
			rows = append(rows, string(d.buf))
			d.buf = d.buf[:0]
		}
		return rows
	}())
	d.table("import_names", 10, func() []string {
		rows := make([]string, 0, len(g.ImportNames))
		for i := range g.ImportNames {
			c := &g.ImportNames[i]
			d.row()
			d.i(int32(i + 1))
			d.buf = append(d.buf, ' ')
			d.i(c.fileID)
			d.buf = append(d.buf, ' ')
			d.s(g.s(c.source))
			d.buf = append(d.buf, ' ')
			if c.sourceID != 0 {
				d.i(c.sourceID)
			} else {
				d.n()
			}
			d.buf = append(d.buf, ' ')
			d.s(g.s(c.name))
			d.buf = append(d.buf, ' ')
			d.s(g.s(c.alias))
			d.buf = append(d.buf, ' ')
			d.i(c.line)
			for _, v := range []int32{b2i(c.ns), b2i(c.def), b2i(c.external)} {
				d.buf = append(d.buf, ' ')
				d.i(v)
			}
			rows = append(rows, string(d.buf))
			d.buf = d.buf[:0]
		}
		return rows
	}())
	d.table("imports", 13, func() []string {
		rows := make([]string, 0, len(g.Imports))
		for i := range g.Imports {
			c := &g.Imports[i]
			d.row()
			d.i(int32(i + 1))
			d.buf = append(d.buf, ' ')
			d.i(c.fileID)
			d.buf = append(d.buf, ' ')
			d.s(g.s(c.target))
			d.buf = append(d.buf, ' ')
			if c.targetID != 0 {
				d.i(c.targetID)
			} else {
				d.n()
			}
			d.buf = append(d.buf, ' ')
			if c.aliasNull {
				d.n()
			} else {
				d.s(g.s(c.alias))
			}
			d.buf = append(d.buf, ' ')
			d.s(g.s(c.kind))
			d.buf = append(d.buf, ' ')
			d.i(c.line)
			for _, v := range []int32{c.isExternal, c.isRel, c.isWild, c.isTypeOnly,
				c.isDynamic, c.nNames} {
				d.buf = append(d.buf, ' ')
				d.i(v)
			}
			rows = append(rows, string(d.buf))
			d.buf = d.buf[:0]
		}
		return rows
	}())
	d.table("jsx_components", 13, func() []string {
		rows := make([]string, 0, len(g.JSX))
		for i := range g.JSX {
			c := &g.JSX[i]
			d.row()
			d.i(int32(i + 1))
			d.buf = append(d.buf, ' ')
			d.i(c.fileID)
			d.buf = append(d.buf, ' ')
			if c.symID != 0 {
				d.i(c.symID)
			} else {
				d.n()
			}
			d.buf = append(d.buf, ' ')
			d.i(c.line)
			d.buf = append(d.buf, ' ')
			d.s(g.s(c.tag))
			for _, v := range []int32{b2i(c.component), c.nAttrs, c.nSpread,
				b2i(c.hasKey), c.inlineObj, c.inlineFn,
				b2i(c.danger), b2i(c.inLoop)} {
				d.buf = append(d.buf, ' ')
				d.i(v)
			}
			rows = append(rows, string(d.buf))
			d.buf = d.buf[:0]
		}
		return rows
	}())
	d.table("listeners", 15, func() []string {
		rows := make([]string, 0, len(g.Listeners))
		for i := range g.Listeners {
			c := &g.Listeners[i]
			d.row()
			d.i(int32(i + 1))
			d.buf = append(d.buf, ' ')
			d.i(c.fileID)
			d.buf = append(d.buf, ' ')
			if c.symID != 0 {
				d.i(c.symID)
			} else {
				d.n()
			}
			d.buf = append(d.buf, ' ')
			d.i(c.line)
			d.buf = append(d.buf, ' ')
			d.s(g.s(c.op))
			for _, s := range []string{g.s(c.api), g.s(c.family), g.s(c.target), g.s(c.event), g.s(c.handler)} {
				d.buf = append(d.buf, ' ')
				d.s(s)
			}
			for _, v := range []bool{c.inline, c.signal, c.atModule, c.inLoop, c.inClean} {
				d.buf = append(d.buf, ' ')
				d.i(b2i(v))
			}
			rows = append(rows, string(d.buf))
			d.buf = d.buf[:0]
		}
		return rows
	}())
	d.table("literals", 7, func() []string {
		rows := make([]string, 0, len(g.Literals))
		for i := range g.Literals {
			c := &g.Literals[i]
			d.row()
			d.i(int32(i + 1))
			d.buf = append(d.buf, ' ')
			if c.symID != 0 {
				d.i(c.symID)
			} else {
				d.n()
			}
			d.buf = append(d.buf, ' ')
			d.i(c.fileID)
			d.buf = append(d.buf, ' ')
			d.s(g.s(c.kind))
			d.buf = append(d.buf, ' ')
			d.s(g.s(c.value))
			d.buf = append(d.buf, ' ')
			d.i(c.line)
			d.buf = append(d.buf, ' ')
			d.i(b2i(c.isMagic))
			rows = append(rows, string(d.buf))
			d.buf = d.buf[:0]
		}
		return rows
	}())
	d.table("locals", 11, nil)
	d.table("markers", 6, func() []string {
		rows := make([]string, 0, len(g.Markers))
		for i := range g.Markers {
			c := &g.Markers[i]
			d.row()
			d.i(int32(i + 1))
			d.buf = append(d.buf, ' ')
			d.i(c.fileID)
			d.buf = append(d.buf, ' ')
			if c.symID != 0 {
				d.i(c.symID)
			} else {
				d.n()
			}
			d.buf = append(d.buf, ' ')
			d.s(g.s(c.kind))
			d.buf = append(d.buf, ' ')
			d.i(c.line)
			d.buf = append(d.buf, ' ')
			d.s(g.s(c.text))
			rows = append(rows, string(d.buf))
			d.buf = d.buf[:0]
		}
		return rows
	}())
	d.dumpMeta()
	d.table("module_caches", 14, func() []string {
		rows := make([]string, 0, len(g.Caches))
		for i := range g.Caches {
			c := &g.Caches[i]
			d.row()
			d.i(int32(i + 1))
			d.buf = append(d.buf, ' ')
			d.i(c.fileID)
			d.buf = append(d.buf, ' ')
			d.i(c.line)
			d.buf = append(d.buf, ' ')
			d.s(g.s(c.name))
			d.buf = append(d.buf, ' ')
			d.s(g.s(c.ctor))
			for _, v := range []int32{b2i(c.weak), b2i(c.exported), b2i(c.konst),
				c.nWrites, c.nDrops, c.nReads, c.nSize, b2i(c.hasMax)} {
				d.buf = append(d.buf, ' ')
				d.i(v)
			}
			d.buf = append(d.buf, ' ')
			d.s(g.s(c.writers))
			rows = append(rows, string(d.buf))
			d.buf = d.buf[:0]
		}
		return rows
	}())
	d.table("modules", 10, func() []string {
		rows := make([]string, 0, len(g.Modules))
		for i := range g.Modules {
			m := &g.Modules[i]
			d.row()
			d.i(m.id)
			d.buf = append(d.buf, ' ')
			d.s(g.s(m.name))
			d.buf = append(d.buf, ' ')
			d.s(g.s(m.kind))
			for _, v := range []int32{m.nFiles, m.nSymbols, m.nPublic, m.sloc, m.fanIn, m.fanOut} {
				d.buf = append(d.buf, ' ')
				d.i(v)
			}
			d.buf = append(d.buf, ' ')
			d.f(m.instability)
			rows = append(rows, string(d.buf))
			d.buf = d.buf[:0]
		}
		return rows
	}())
	d.table("params", 13, func() []string {
		rows := make([]string, 0, len(g.Params))
		for i := range g.Params {
			p := &g.Params[i]
			d.row()
			d.i(p.symID)
			for _, v := range []int32{p.pos} {
				d.buf = append(d.buf, ' ')
				d.i(v)
			}
			d.buf = append(d.buf, ' ')
			d.s(g.s(p.name))
			d.buf = append(d.buf, ' ')
			d.s(g.s(p.typ))
			d.buf = append(d.buf, ' ')
			d.n()
			for _, v := range []int32{b2i(p.optional), b2i(p.variadic), b2i(p.ref),
				b2i(p.mut), b2i(p.nullable), b2i(p.gen), p.untyped, p.depth} {
				d.buf = append(d.buf, ' ')
				d.i(v)
			}
			rows = append(rows, string(d.buf))
			d.buf = d.buf[:0]
		}
		return rows
	}())
	d.table("routes", 10, func() []string {
		rows := make([]string, 0, len(g.Routes))
		for i := range g.Routes {
			c := &g.Routes[i]
			d.row()
			d.i(int32(i + 1))
			d.buf = append(d.buf, ' ')
			d.i(c.fileID)
			d.buf = append(d.buf, ' ')
			if c.symID != 0 {
				d.i(c.symID)
			} else {
				d.n()
			}
			d.buf = append(d.buf, ' ')
			d.i(c.line)
			d.buf = append(d.buf, ' ')
			d.s(g.s(c.method))
			for _, s := range []string{g.s(c.path), g.s(c.handler)} {
				d.buf = append(d.buf, ' ')
				d.s(s)
			}
			for _, v := range []int32{b2i(c.inline), b2i(c.async), c.nMw} {
				d.buf = append(d.buf, ' ')
				d.i(v)
			}
			rows = append(rows, string(d.buf))
			d.buf = d.buf[:0]
		}
		return rows
	}())
	d.table("secret_candidates", 5, func() []string {
		rows := make([]string, 0, len(g.Secrets))
		for i := range g.Secrets {
			c := &g.Secrets[i]
			d.row()
			d.i(int32(i + 1))
			d.buf = append(d.buf, ' ')
			if c.symID != 0 {
				d.i(c.symID)
			} else {
				d.n()
			}
			d.buf = append(d.buf, ' ')
			d.i(c.fileID)
			d.buf = append(d.buf, ' ')
			d.s(g.s(c.value))
			d.buf = append(d.buf, ' ')
			d.i(c.line)
			rows = append(rows, string(d.buf))
			d.buf = d.buf[:0]
		}
		return rows
	}())
	d.table("sym_fts", 3, func() []string {
		rows := make([]string, 0, g.nSym())
		for i := 0; i < g.nSym(); i++ {
			rows = append(rows, "R \\N \\N \\N")
		}
		return rows
	}())
	d.dumpSymbols()
	d.table("timers", 15, func() []string {
		rows := make([]string, 0, len(g.Timers))
		for i := range g.Timers {
			c := &g.Timers[i]
			d.row()
			d.i(int32(i + 1))
			d.buf = append(d.buf, ' ')
			d.i(c.fileID)
			d.buf = append(d.buf, ' ')
			if c.symID != 0 {
				d.i(c.symID)
			} else {
				d.n()
			}
			d.buf = append(d.buf, ' ')
			d.i(c.line)
			d.buf = append(d.buf, ' ')
			d.s(g.s(c.op))
			for _, s := range []string{g.s(c.api), g.s(c.kind), g.s(c.handle)} {
				d.buf = append(d.buf, ' ')
				d.s(s)
			}
			for _, v := range []bool{c.assigned, c.repeating, c.unrefd, c.cbString,
				c.atModule, c.inLoop, c.asyncCB} {
				d.buf = append(d.buf, ' ')
				d.i(b2i(v))
			}
			rows = append(rows, string(d.buf))
			d.buf = d.buf[:0]
		}
		return rows
	}())
	d.table("unresolved_calls", 4, func() []string {
		rows := make([]string, 0, len(g.Unresolved))
		for i := range g.Unresolved {
			c := &g.Unresolved[i]
			d.row()
			d.i(c.caller)
			d.buf = append(d.buf, ' ')
			d.s(g.s(c.name))
			d.buf = append(d.buf, ' ')
			d.i(c.n)
			d.buf = append(d.buf, ' ')
			d.i(c.firstLn)
			rows = append(rows, string(d.buf))
			d.buf = d.buf[:0]
		}
		return rows
	}())
	d.table("user_input_sites", 7, func() []string {
		rows := make([]string, 0, len(g.UserInput))
		for i := range g.UserInput {
			c := &g.UserInput[i]
			d.row()
			d.i(int32(i + 1))
			d.buf = append(d.buf, ' ')
			if c.symID != 0 {
				d.i(c.symID)
			} else {
				d.n()
			}
			d.buf = append(d.buf, ' ')
			d.i(c.fileID)
			d.buf = append(d.buf, ' ')
			d.s(g.s(c.varName))
			d.buf = append(d.buf, ' ')
			d.s(g.s(c.kind))
			d.buf = append(d.buf, ' ')
			d.i(c.line)
			d.buf = append(d.buf, ' ')
			d.i(b2i(c.inLoop))
			rows = append(rows, string(d.buf))
			d.buf = d.buf[:0]
		}
		return rows
	}())
	d.flushBuf()
	d.w.Flush()
}

func (d *dumper) dumpFiles() {
	g := dGraph
	rows := make([]string, 0, len(g.Files))
	for i := range g.Files {
		f := &g.Files[i]
		d.row()
		d.i(f.id)
		d.buf = append(d.buf, ' ')
		d.s(g.s(f.path))
		for _, s := range []string{g.s(f.dir), g.s(f.base), g.s(f.ext), g.s(f.lang)} {
			d.buf = append(d.buf, ' ')
			d.s(s)
		}
		d.buf = append(d.buf, ' ')
		d.i(f.moduleID)
		for _, v := range []int32{f.bytes, f.lines, f.sloc, f.blank, f.comment, f.doc,
			f.maxLine} {
			d.buf = append(d.buf, ' ')
			d.i(v)
		}
		d.buf = append(d.buf, ' ')
		d.s(g.s(f.sha1))
		for _, v := range []int32{b2i(f.parsed), b2i(f.isTest), b2i(f.isGen),
			b2i(f.isVendored), f.nParseErrors, f.nMissing} {
			d.buf = append(d.buf, ' ')
			d.i(v)
		}
		d.buf = append(d.buf, ' ')
		d.f(f.parseMS)
		for _, v := range []int32{f.nSymbols, f.nFuncs, f.nTypes, f.nImports,
			f.totalCycles, f.maxCycles, f.totalRisk} {
			d.buf = append(d.buf, ' ')
			d.i(v)
		}
		rows = append(rows, string(d.buf))
		d.buf = d.buf[:0]
	}
	d.table("files", 29, rows)
}

func (d *dumper) dumpMeta() {
	g := dGraph
	rows := make([]string, 0, len(g.Meta))
	for _, m := range g.Meta {
		d.row()
		d.s(g.s(m[0]))
		d.buf = append(d.buf, ' ')
		d.s(g.s(m[1]))
		rows = append(rows, string(d.buf))
		d.buf = d.buf[:0]
	}
	d.table("meta", 2, rows)
}

func (d *dumper) dumpSymbols() {
	g := dGraph
	rows := make([]string, 0, g.nSym())
	width := 0
	for c := range symCols {
		if colSlot[c] >= 0 || c == cID {
			width++
		}
	}
	for i := 0; i < g.nSym(); i++ {
		d.row()
		for c := range numSymCols {
			if colSlot[c] < 0 && c != cID {
				continue
			}
			if c > 0 {
				d.buf = append(d.buf, ' ')
			}
			if c == cID {
				d.i(int32(i + 1))
			} else if tc := textCol[c]; tc >= 0 {
				d.s(g.s(g.Syms.pool[g.Syms.ids[i][tc]]))
			} else if symCols[c].kind == 1 {
				d.f(0.0)
			} else if c == cMODULEID || c == cPARENTID {
				v := g.Syms.at(i, c)
				if v == 0 {
					d.n()
				} else {
					d.i(v)
				}
			} else {
				d.i(g.Syms.at(i, c))
			}
		}
		rows = append(rows, string(d.buf))
		d.buf = d.buf[:0]
	}
	d.table("symbols", width, rows)
}

var dGraph *Graph

func dumpTo(g *Graph, w io.Writer) error {
	dGraph = g
	defer func() { dGraph = nil }()
	emit(g, w)
	return nil
}

var _ = strings.Join

const (
	langName   = "javascript"
	targetName = "ES2026 (17th ed.) + using/Temporal (ES2027 candidates)"
	schemaVer  = 1
)

var usageText = `usage: codegraph_javascript [-h] [--module MODULE] [--limit LIMIT]
                          [--csv N] [--json N] [--save PATH] [--save-ast PATH]
                          [--load-ast PATH] [--force] [--deps]
                          [--install-deps] [--include-generated]
                          [--include-vendored] [--no-tests] [--quiet]
                          [--version] [--dump PATH] [--workers N]
                          [--cpuprofile PATH] [--memprofile PATH]
                          [--blockprofile PATH] [--mutexprofile PATH]
                          [--trace PATH]
                          [root] [which ...]

Parse a javascript tree into a graph and query it in one shot. Target: ` + targetName + `

every run re-parses from source; nothing is cached, so an answer can never
describe code that has moved on.  --save-ast PATH writes the parsed state
(trees, tables, strings) to a binary file after the run's parse; --load-ast
PATH restores that state instead of parsing, and answers from it.  The two
flags are mutually exclusive.

--workers N is accepted for compatibility and changes nothing: the reader
runs exactly one tree-sitter child at a time, so N does not size a farm.
Measured over pipeline depths 1..16 the wall, CPU and peak RSS are flat; N
only sets how many CST buffers may be in flight, and the decoder is never
the constraint.  There is no setting on this port that raises parse
parallelism, because parse parallelism is what costs this tool its CPU
advantage over the reference.
`

type cli struct {
	root             string
	which            []int
	module           string
	limit            int
	list             bool
	metrics          bool
	schema           bool
	report           bool
	csv              int
	hasCSV           bool
	json             int
	hasJSON          bool
	save             string
	saveAST          string
	loadAST          string
	force            bool
	deps             bool
	installDeps      bool
	includeGenerated bool
	includeVendored  bool
	noTests          bool
	quiet            bool
	version          bool
	dump             string
	workers          int
	cpuProfile       string
	memProfile       string
	blockProfile     string
	mutexProfile     string
	traceProfile     string
}

func cgPutU32(b []byte, o int, v uint32) { *(*uint32)(unsafe.Pointer(&b[o])) = v }
func cgPutU64(b []byte, o int, v uint64) { *(*uint64)(unsafe.Pointer(&b[o])) = v }

func cgGetU32(b []byte, o int) uint32 { return *(*uint32)(unsafe.Pointer(&b[o])) }
func cgGetU64(b []byte, o int) uint64 { return *(*uint64)(unsafe.Pointer(&b[o])) }

func main() { os.Exit(run(os.Args[1:])) }

func run(argv []string) int {
	c, err := parseArgs(argv)
	if err != nil {
		fmt.Fprintf(os.Stderr, "%v\n", err)
		fmt.Fprint(os.Stderr, usageText)
		return 2
	}
	if c.version {
		fmt.Printf("codegraph_javascript  target=%s  schema=v%d  go=%s  "+
			"tree-sitter=%s\n", targetName, schemaVer, runtime.Version(), grammarVersion)
		return 0
	}
	if c.deps || c.installDeps {
		printDeps()
		return 0
	}
	if c.schema {
		fmt.Print(schemaNative())
		return 0
	}
	if c.list {
		qs := queries
		if c.metrics {
			qs = metrics
		}
		for i, q := range qs {
			fmt.Printf("%2d. %-26s %s\n", i+1, q.Name, q.Title)
		}
		return 0
	}

	if c.hasCSV || c.hasJSON {
		c.quiet = true
	}
	if c.saveAST != "" && c.loadAST != "" {
		fmt.Fprintln(os.Stderr, "--save-ast and --load-ast cannot be used together")
		return 2
	}
	if c.loadAST == "" {
		if st, err := os.Stat(c.root); err != nil || !st.IsDir() {
			fmt.Fprintf(os.Stderr, "not a directory: %s\n", c.root)
			return 2
		}
	}

	gogc := 30
	if v := os.Getenv("CG_GOGC"); v != "" {
		if n, err := strconv.Atoi(v); err == nil {
			gogc = n
		}
	}
	debug.SetGCPercent(gogc)
	stopProf := startProfiling(c)
	defer stopProf()

	abs, _ := filepath.Abs(c.root)
	opts := &Options{
		Root: abs, IncludeTests: !c.noTests,
		IncludeGenerated: c.includeGenerated, IncludeVendored: c.includeVendored,
		Quiet: c.quiet, Workers: c.workers, GCPercent: gogc,
		KeepTrees: c.saveAST != "",
	}
	t0 := time.Now()
	var g *Graph
	var bs *buildStats
	if c.loadAST != "" {
		g, err = loadAST(c.loadAST)
		if err != nil {
			fmt.Fprintf(os.Stderr, "load-ast: %v\n", err)
			return 2
		}
		nParsed := 0
		for i := range g.Files {
			if g.Files[i].parsed {
				nParsed++
			}
		}
		bs = &buildStats{FilesParsed: nParsed}
	} else {
		g, bs, err = build(opts)
		if err != nil {
			fmt.Fprintf(os.Stderr, "%v\n", err)
			return 2
		}
		g.setMetaRaw("schema_version", strconv.Itoa(schemaVer))
		g.setMetaRaw("lang", langName)
		g.setMetaRaw("target", targetName)
		g.setMetaRaw("root", abs)
		g.setMetaRaw("parse_mode", "tree-sitter")
		g.setMetaRaw("files_parsed", strconv.Itoa(bs.FilesParsed))
		g.setMetaRaw("files_failed", strconv.Itoa(bs.Failed))
		g.setMetaRaw("retention_scan", retentionScan(g))
	}
	took := time.Since(t0)

	if c.saveAST != "" {
		if _, serr := os.Lstat(c.saveAST); serr == nil && !c.force {
			fmt.Fprintf(os.Stderr, "refusing to overwrite %s (pass --force)\n", c.saveAST)
			return 2
		}
		ts := time.Now()
		nb, werr := saveASTFile(g, c.saveAST)
		if werr != nil {
			fmt.Fprintf(os.Stderr, "save-ast: %v\n", werr)
			return 2
		}
		if !c.quiet {
			fmt.Fprintf(os.Stderr, "ast state written to %s: %d bytes in %.1fs\n",
				c.saveAST, nb, time.Since(ts).Seconds())
		}
	}

	if c.dump != "" {
		f, err := os.Create(c.dump)
		if err != nil {
			fmt.Fprintf(os.Stderr, "could not write %s: %v\n", c.dump, err)
			return 2
		}
		if err := dumpTo(g, bufio.NewWriterSize(f, 1<<20)); err != nil {
			f.Close()
			fmt.Fprintf(os.Stderr, "dump failed: %v\n", err)
			return 2
		}
		f.Close()
	}
	if c.memProfile != "" {
		writeMemProfile(c.memProfile)
	}
	if c.hasCSV || c.hasJSON {
		qs := queries
		if c.metrics {
			qs = metrics
		}

		idx := c.csv - 1
		if !c.hasCSV {
			idx = c.json - 1
		}
		if idx < 0 || idx >= len(qs) {
			fmt.Fprintf(os.Stderr, "no query %d\n", idx+1)
			return 2
		}
		tab := runQuery(g, qs[idx], c.module, c.limit)
		w := bufio.NewWriter(os.Stdout)
		if c.hasCSV {
			writeCSV(w, tab)
		} else {
			writeJSON(w, tab)
		}
		w.Flush()
		return 0
	}
	if !c.quiet {
		limit := "all"
		if c.limit >= 0 {
			limit = strconv.Itoa(c.limit)
		}
		if c.loadAST != "" {
			fmt.Printf("codegraph-%s: %d files loaded from AST in %.1fs "+
				"module=%s limit=%s\n", langName, bs.FilesParsed, took.Seconds(),
				c.module, limit)
		} else {
			fmt.Printf("codegraph-%s: %d files parsed into memory in %.1fs "+
				"module=%s limit=%s\n", langName, bs.FilesParsed, took.Seconds(),
				c.module, limit)
		}
	}
	if c.report {
		printReport(g)
	}
	qs := queries
	if c.metrics {
		qs = metrics
	}
	sel := c.which
	if len(sel) == 0 {
		sel = make([]int, 0, len(qs))
		for i := range qs {
			sel = append(sel, i+1)
		}
	}
	out := bufio.NewWriter(os.Stdout)
	defer out.Flush()
	for _, k := range sel {
		if k < 1 || k > len(qs) {
			continue
		}
		q := qs[k-1]
		fmt.Fprintf(out, "\n%s\n", strings.Repeat("=", 78))
		fmt.Fprintf(out, "Q%d. %s -- %s\n", k, q.Name, q.Title)
		fmt.Fprintf(out, "%s\n", strings.Repeat("-", 78))
		for line := range strings.SplitSeq(q.Notes, "\n") {
			fmt.Fprintf(out, " %s\n", line)
		}
		fmt.Fprintln(out)
		tab := runQuery(g, q, c.module, c.limit)
		render(out, tab)
	}
	if c.save != "" {
		if st, err := os.Lstat(c.save); err == nil && !c.force {
			fmt.Fprintf(os.Stderr, "\nrefusing to overwrite %s (pass --force)%s\n",
				c.save, symlinkNote(st, c.save))
		} else {
			if err == nil && st.Mode()&os.ModeSymlink != 0 {
				os.Remove(c.save)
			}
			if err := g.writeSelf(c.save); err != nil {
				fmt.Fprintf(os.Stderr, "\ncould not write %s: %v\n", c.save, err)
			} else {
				fmt.Fprintf(out, "\n(graph also written to %s)\n", c.save)
			}
		}
	}
	return 0
}

func symlinkNote(st os.FileInfo, path string) string {
	if st.Mode()&os.ModeSymlink == 0 {
		return ""
	}
	real, err := filepath.EvalSymlinks(path)
	if err != nil {
		return ""
	}
	return " -- it is a symlink to " + real
}

func retentionScan(g *Graph) string {
	return sprintf("%d listener op(s), %d timer op(s), %d module-scope container(s) "+
		"-- no linter in ESLint/typescript-eslint/unicorn/Biome/oxlint/CodeQL-JS "+
		"checks any of these", len(g.Listeners), len(g.Timers), len(g.Caches))
}

func (g *Graph) metaGet(k string) string {
	for i := range g.Meta {
		if g.s(g.Meta[i][0]) == k {
			return g.s(g.Meta[i][1])
		}
	}
	return ""
}

func runQuery(g *Graph, q Question, mod string, lim int) *Table {
	if q.Run == nil {
		return &Table{Cols: []string{}}
	}
	return q.Run(g, mod, lim)
}

func parseArgs(argv []string) (*cli, error) {
	c := &cli{root: ".", module: "%", limit: -1, workers: defaultParseWorkers()}
	positional := 0
	for i := 0; i < len(argv); i++ {
		a := argv[i]

		if len(a) >= 2 && a[0] == '-' && a[1] >= '0' && a[1] <= '9' {
			n, e := strconv.Atoi(a)
			if e != nil {
				return nil, fmt.Errorf("argument which: invalid int value: %q", a)
			}
			if positional == 0 {
				c.root = a
			} else {
				c.which = append(c.which, n)
			}
			positional++
			continue
		}
		if len(a) < 2 || a[0] != '-' {
			if positional == 0 {
				c.root = a
			} else {
				n, e := strconv.Atoi(a)
				if e != nil {
					return nil, fmt.Errorf("argument which: invalid int value: %q", a)
				}
				c.which = append(c.which, n)
			}
			positional++
			continue
		}
		name, inline := a, ""
		hasInline := false
		if k := strings.IndexByte(a, '='); k > 0 {
			name, inline, hasInline = a[:k], a[k+1:], true
		}
		take := func() (string, error) {
			if hasInline {
				return inline, nil
			}
			if i+1 >= len(argv) {
				return "", fmt.Errorf("argument %s: expected one argument", name)
			}
			i++
			return argv[i], nil
		}
		takeInt := func() (int, error) {
			v, err := take()
			if err != nil {
				return 0, err
			}
			n, e := strconv.Atoi(v)
			if e != nil {
				return 0, fmt.Errorf("argument %s: invalid int value: %q", name, v)
			}
			return n, nil
		}
		var err error
		switch name {
		case "-h", "--help":
			fmt.Print(usageText)
			os.Exit(0)
		case "--module":
			c.module, err = take()
		case "--limit":
			c.limit, err = takeInt()
		case "--list":
			c.list = true
		case "--metrics":
			c.metrics = true
		case "--schema":
			c.schema = true
		case "--report":
			c.report = true
		case "--csv":
			c.csv, err = takeInt()
			c.hasCSV = err == nil
		case "--json":
			c.json, err = takeInt()
			c.hasJSON = err == nil
		case "--save":
			c.save, err = take()
		case "--save-ast":
			c.saveAST, err = take()
		case "--load-ast":
			c.loadAST, err = take()
		case "--force":
			c.force = true
		case "--deps":
			c.deps = true
		case "--install-deps":
			c.installDeps = true
		case "--include-generated":
			c.includeGenerated = true
		case "--include-vendored":
			c.includeVendored = true
		case "--no-tests":
			c.noTests = true
		case "--quiet":
			c.quiet = true
		case "--version":
			c.version = true
		case "--dump":
			c.dump, err = take()
		case "--workers":
			c.workers, err = takeInt()
		case "--cpuprofile":
			c.cpuProfile, err = take()
		case "--memprofile":
			c.memProfile, err = take()
		case "--blockprofile":
			c.blockProfile, err = take()
		case "--mutexprofile":
			c.mutexProfile, err = take()
		case "--trace":
			c.traceProfile, err = take()
		default:
			return nil, fmt.Errorf("unrecognized arguments: %s", a)
		}
		if err != nil {
			return nil, err
		}
	}
	if c.workers < 1 {
		c.workers = 1
	}
	return c, nil
}

func printDeps() {
	fmt.Println("codegraph-javascript dependencies")
	fmt.Println("  the official `tree-sitter` CLI binary on PATH (or $TREE_SITTER_BIN),")
	fmt.Println("  version 0.25.x, with the tree-sitter-javascript grammar registered")
	fmt.Println("  for it. One child process parses one file: `tree-sitter parse")
	fmt.Println("  /dev/stdin --scope source.js --cst`. There is no C in this build and")
	fmt.Println("  nothing is linked in, so the program REFUSES at startup rather than")
	fmt.Println("  emitting an empty graph -- an empty graph reads exactly like a clean")
	fmt.Println("  repository.")
}

func startProfiling(c *cli) func() {
	var closers []func()
	if c.cpuProfile != "" {
		f, err := os.Create(c.cpuProfile)
		if err == nil {
			if err := pprof.StartCPUProfile(f); err == nil {
				closers = append(closers, func() { pprof.StopCPUProfile(); f.Close() })
			} else {
				f.Close()
			}
		}
	}
	if c.blockProfile != "" {
		runtime.SetBlockProfileRate(1)
	}
	if c.mutexProfile != "" {
		runtime.SetMutexProfileFraction(1)
	}
	if c.traceProfile != "" {
		if f, err := os.Create(c.traceProfile); err == nil {
			if err := trace.Start(f); err == nil {
				closers = append(closers, func() {
					trace.Stop()
					fmt.Fprintf(os.Stderr, "goroutines at exit: %d\n",
						runtime.NumGoroutine())
					f.Close()
				})
			} else {
				f.Close()
			}
		}
	}

	if p := os.Getenv("CG_PEAKHEAP"); p != "" {
		stop := make(chan struct{})
		done := make(chan struct{})
		go func() {
			defer close(done)
			var ms runtime.MemStats
			best := uint64(0)
			for {
				select {
				case <-stop:
					return
				case <-time.After(10 * time.Millisecond):
				}
				runtime.ReadMemStats(&ms)
				if ms.HeapAlloc <= best {
					continue
				}
				best = ms.HeapAlloc
				if f, err := os.Create(p); err == nil {
					pprof.WriteHeapProfile(f)
					f.Close()
				}
			}
		}()
		closers = append(closers, func() {
			close(stop)
			<-done
			fmt.Fprintf(os.Stderr, "peak heap sampled: %s\n", p)
		})
	}
	return func() {
		for _, closer := range slices.Backward(closers) {
			closer()
		}
		if c.blockProfile != "" {
			if f, err := os.Create(c.blockProfile); err == nil {
				pprof.Lookup("block").WriteTo(f, 0)
				f.Close()
			}
		}
		if c.mutexProfile != "" {
			if f, err := os.Create(c.mutexProfile); err == nil {
				pprof.Lookup("mutex").WriteTo(f, 0)
				f.Close()
			}
		}
	}
}

func writeMemProfile(path string) {
	f, err := os.Create(path)
	if err != nil {
		return
	}
	runtime.GC()
	pprof.WriteHeapProfile(f)
	f.Close()
}

const cgasMagic = "CGAS"

const (
	cgasVersion  = 3
	cgasHeaderSz = 32
	cgasSecSz    = 24
	cgasNSec     = 32
	cgasArenaLo  = 1 << 20
)

const (
	cgasSecStrings uint32 = 1 + iota
	cgasSecTrees
	cgasSecTreeDir
	cgasSecFiles
	cgasSecMods
	cgasSecSymIDs
	cgasSecSymBlocks
	cgasSecSymPool
	cgasSecParams
	cgasSecFields
	cgasSecEdges
	cgasSecCallsites
	cgasSecUnres
	cgasSecImps
	cgasSecHaz
	cgasSecAttrs
	cgasSecLits
	cgasSecEnums
	cgasSecMarks
	cgasSecClasses
	cgasSecExports
	cgasSecImpNames
	cgasSecListeners
	cgasSecTimers
	cgasSecCaches
	cgasSecDeps
	cgasSecJSX
	cgasSecHooks
	cgasSecUIs
	cgasSecRoutes
	cgasSecSecs
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
	fileStrOffs = []uintptr{
		unsafe.Offsetof(File{}.path),
		unsafe.Offsetof(File{}.dir),
		unsafe.Offsetof(File{}.base),
		unsafe.Offsetof(File{}.ext),
		unsafe.Offsetof(File{}.lang),
		unsafe.Offsetof(File{}.sha1),
	}
	moduleStrOffs = []uintptr{
		unsafe.Offsetof(Module{}.name),
		unsafe.Offsetof(Module{}.kind),
	}
	paramStrOffs = []uintptr{
		unsafe.Offsetof(Param{}.name),
		unsafe.Offsetof(Param{}.typ),
	}
	fieldStrOffs = []uintptr{
		unsafe.Offsetof(FieldRow{}.name),
		unsafe.Offsetof(FieldRow{}.typ),
		unsafe.Offsetof(FieldRow{}.vis),
	}
	unresStrOffs = []uintptr{
		unsafe.Offsetof(Unresolved{}.name),
	}
	importStrOffs = []uintptr{
		unsafe.Offsetof(Import{}.target),
		unsafe.Offsetof(Import{}.alias),
		unsafe.Offsetof(Import{}.kind),
	}
	hazardStrOffs = []uintptr{
		unsafe.Offsetof(Hazard{}.pattern),
		unsafe.Offsetof(Hazard{}.category),
	}
	attrStrOffs = []uintptr{
		unsafe.Offsetof(Attribute{}.name),
		unsafe.Offsetof(Attribute{}.args),
	}
	literalStrOffs = []uintptr{
		unsafe.Offsetof(Literal{}.kind),
		unsafe.Offsetof(Literal{}.value),
	}
	enumStrOffs = []uintptr{
		unsafe.Offsetof(EnumMember{}.name),
		unsafe.Offsetof(EnumMember{}.value),
	}
	markerStrOffs = []uintptr{
		unsafe.Offsetof(Marker{}.kind),
		unsafe.Offsetof(Marker{}.text),
	}
	classStrOffs = []uintptr{
		unsafe.Offsetof(ClassRow{}.extends),
	}
	exportStrOffs = []uintptr{
		unsafe.Offsetof(ExportRow{}.name),
		unsafe.Offsetof(ExportRow{}.localName),
		unsafe.Offsetof(ExportRow{}.kind),
		unsafe.Offsetof(ExportRow{}.source),
	}
	impNameStrOffs = []uintptr{
		unsafe.Offsetof(ImportName{}.source),
		unsafe.Offsetof(ImportName{}.name),
		unsafe.Offsetof(ImportName{}.alias),
	}
	listenerStrOffs = []uintptr{
		unsafe.Offsetof(Listener{}.op),
		unsafe.Offsetof(Listener{}.api),
		unsafe.Offsetof(Listener{}.family),
		unsafe.Offsetof(Listener{}.target),
		unsafe.Offsetof(Listener{}.event),
		unsafe.Offsetof(Listener{}.handler),
	}
	timerStrOffs = []uintptr{
		unsafe.Offsetof(Timer{}.op),
		unsafe.Offsetof(Timer{}.api),
		unsafe.Offsetof(Timer{}.kind),
		unsafe.Offsetof(Timer{}.handle),
	}
	cacheStrOffs = []uintptr{
		unsafe.Offsetof(ModuleCache{}.name),
		unsafe.Offsetof(ModuleCache{}.ctor),
		unsafe.Offsetof(ModuleCache{}.writers),
	}
	depStrOffs = []uintptr{
		unsafe.Offsetof(DepRow{}.name),
		unsafe.Offsetof(DepRow{}.version),
		unsafe.Offsetof(DepRow{}.dir),
	}
	jsxStrOffs = []uintptr{
		unsafe.Offsetof(JSXComp{}.tag),
	}
	hookStrOffs = []uintptr{
		unsafe.Offsetof(HookRow{}.name),
	}
	uiStrOffs = []uintptr{
		unsafe.Offsetof(UserInput{}.kind),
		unsafe.Offsetof(UserInput{}.varName),
	}
	routeStrOffs = []uintptr{
		unsafe.Offsetof(Route{}.method),
		unsafe.Offsetof(Route{}.path),
		unsafe.Offsetof(Route{}.handler),
	}
	secretStrOffs = []uintptr{
		unsafe.Offsetof(Secret{}.value),
	}
	metaStrOffs = []uintptr{0, 8}
	poolStrOffs = []uintptr{0}
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
	fail(unsafe.Sizeof(sref{}) == 8, "sref must be 8 bytes")
	fail(unsafe.Alignof(sref{}) == 4, "sref must be 4-byte aligned")
	fail(unsafe.Sizeof(tsRec{}) == 32, "tsRec must be the 32-byte fixed stride")
	fail(unsafe.Sizeof(metaRow{}) == 16, "metaRow must be 16 bytes")
	for _, t := range []reflect.Type{
		reflect.TypeOf(sref{}),
		reflect.TypeOf(tsRec{}),
		reflect.TypeOf([3]uint32{}),
		reflect.TypeOf(metaRow{}),
		reflect.TypeOf(Module{}),
		reflect.TypeOf(File{}),
		reflect.TypeOf(Param{}),
		reflect.TypeOf(FieldRow{}),
		reflect.TypeOf(Edge{}),
		reflect.TypeOf(Callsite{}),
		reflect.TypeOf(Unresolved{}),
		reflect.TypeOf(Import{}),
		reflect.TypeOf(Hazard{}),
		reflect.TypeOf(Attribute{}),
		reflect.TypeOf(Literal{}),
		reflect.TypeOf(EnumMember{}),
		reflect.TypeOf(Marker{}),
		reflect.TypeOf(ClassRow{}),
		reflect.TypeOf(ExportRow{}),
		reflect.TypeOf(ImportName{}),
		reflect.TypeOf(Listener{}),
		reflect.TypeOf(Timer{}),
		reflect.TypeOf(ModuleCache{}),
		reflect.TypeOf(DepRow{}),
		reflect.TypeOf(JSXComp{}),
		reflect.TypeOf(HookRow{}),
		reflect.TypeOf(UserInput{}),
		reflect.TypeOf(Route{}),
		reflect.TypeOf(Secret{}),
		reflect.TypeOf(int32(0)),
		reflect.TypeOf(uint32(0)),
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

func cgasRowBytes[T any](rows []T) []byte {
	if len(rows) == 0 {
		return nil
	}
	return unsafe.Slice((*byte)(unsafe.Pointer(&rows[0])), len(rows)*int(unsafe.Sizeof(rows[0])))
}

func cgasCheckStrs[T any](rows []T, offs []uintptr, arenaLen uint64, what string) error {
	if len(rows) == 0 || len(offs) == 0 {
		return nil
	}
	size := int(unsafe.Sizeof(rows[0]))
	raw := cgasRowBytes(rows)
	for i := range rows {
		row := raw[i*size : (i+1)*size]
		for _, o := range offs {
			r := (*sref)(unsafe.Pointer(&row[o]))
			if uint64(r.o) > arenaLen || uint64(r.n) > arenaLen-uint64(r.o) {
				return fmt.Errorf("row %d: string reference (%d,%d) escapes the string arena (%d bytes)",
					i, r.o, r.n, arenaLen)
			}
		}
	}
	return nil
}

var padSpans sync.Map

func t2Size(t reflect.Type) uintptr {
	return t.Size()
}

func padMap(t reflect.Type) [][2]uintptr {
	if v, ok := padSpans.Load(t); ok {
		return v.([][2]uintptr)
	}
	type span struct{ a, b uintptr }
	var fs []span
	for t.Kind() == reflect.Array {
		t = t.Elem()
	}
	if t.Kind() == reflect.Struct {
		for i := 0; i < t.NumField(); i++ {
			f := t.Field(i)
			fs = append(fs, span{f.Offset, f.Offset + f.Type.Size()})
		}
	} else {
		one := t.Size()
		for at := uintptr(0); at+one <= t2Size(t); at += one {
			fs = append(fs, span{at, at + one})
		}
	}
	sort.Slice(fs, func(i, j int) bool { return fs[i].a < fs[j].a })
	var gaps [][2]uintptr
	at := uintptr(0)
	for _, f := range fs {
		if f.a > at {
			gaps = append(gaps, [2]uintptr{at, f.a})
		}
		if f.b > at {
			at = f.b
		}
	}
	if t2Size(t) > at {
		gaps = append(gaps, [2]uintptr{at, t2Size(t)})
	}
	padSpans.Store(t, gaps)
	return gaps
}

func zapPad[T any](rows []T) {
	if len(rows) == 0 {
		return
	}
	spans := padMap(reflect.TypeOf(rows[0]))
	if len(spans) == 0 {
		return
	}
	size := int(unsafe.Sizeof(rows[0]))
	raw := cgasRowBytes(rows)
	for i := range rows {
		row := raw[i*size : (i+1)*size]
		for _, sp := range spans {
			clear(row[sp[0]:sp[1]])
		}
	}
}

func cgasCastRows[T any](mem []byte, off, ln uint64, what string) ([]T, error) {
	if ln == 0 {
		return nil, nil
	}
	size := uint64(unsafe.Sizeof(*new(T)))
	if ln%size != 0 {
		return nil, fmt.Errorf("section length %d is not a multiple of record size %d", ln, size)
	}
	if off < uint64(cgasHeaderSz) || off > uint64(len(mem)) || ln > uint64(len(mem))-off {
		return nil, fmt.Errorf("section lies outside the file")
	}
	base := unsafe.Pointer(uintptr(unsafe.Pointer(&mem[0])) + uintptr(off))
	if a := uintptr(unsafe.Alignof(*new(T))); a > 1 && uintptr(base)%a != 0 {
		return nil, fmt.Errorf("section is not %d-byte aligned", a)
	}
	return unsafe.Slice((*T)(base), int(ln/size)), nil
}

func saveASTFile(g *Graph, path string) (int64, error) {
	cgasGuard()
	sy := g.Syms
	nBlocks := (len(sy.ids) + symBlock - 1) / symBlock
	if len(sy.blocks) != nBlocks {
		return 0, fmt.Errorf("symbol store holds %d column blocks, want %d for %d symbols",
			len(sy.blocks), nBlocks, len(sy.ids))
	}
	for _, b := range sy.blocks {
		if len(b) != symBlock*numStoreCols {
			return 0, fmt.Errorf("symbol column block holds %d cells, want %d",
				len(b), symBlock*numStoreCols)
		}
	}
	zapPad(g.Modules)
	zapPad(g.Files)
	zapPad(g.Params)
	zapPad(g.Fields)
	zapPad(g.Edges)
	zapPad(g.Callsites)
	zapPad(g.Unresolved)
	zapPad(g.Imports)
	zapPad(g.Hazards)
	zapPad(g.Attrs)
	zapPad(g.Literals)
	zapPad(g.Enums)
	zapPad(g.Markers)
	zapPad(g.Classes)
	zapPad(g.Exports)
	zapPad(g.ImportNames)
	zapPad(g.Listeners)
	zapPad(g.Timers)
	zapPad(g.Caches)
	zapPad(g.Deps)
	zapPad(g.JSX)
	zapPad(g.Hooks)
	zapPad(g.UserInput)
	zapPad(g.Routes)
	zapPad(g.Secrets)
	zapPad(g.Meta)
	zapPad(sy.ids)
	zapPad(sy.pool)
	arenaLen := uint64(len(g.strs))
	strErr := func(what string, err error) (int64, error) {
		return 0, fmt.Errorf("%s: %v", what, err)
	}
	if err := cgasCheckStrs(g.Files, fileStrOffs, arenaLen, "files"); err != nil {
		return strErr("files", err)
	}
	if err := cgasCheckStrs(g.Modules, moduleStrOffs, arenaLen, "modules"); err != nil {
		return strErr("modules", err)
	}
	if err := cgasCheckStrs(g.Params, paramStrOffs, arenaLen, "params"); err != nil {
		return strErr("params", err)
	}
	if err := cgasCheckStrs(g.Fields, fieldStrOffs, arenaLen, "fields"); err != nil {
		return strErr("fields", err)
	}
	if err := cgasCheckStrs(g.Unresolved, unresStrOffs, arenaLen, "unresolved"); err != nil {
		return strErr("unresolved", err)
	}
	if err := cgasCheckStrs(g.Imports, importStrOffs, arenaLen, "imports"); err != nil {
		return strErr("imports", err)
	}
	if err := cgasCheckStrs(g.Hazards, hazardStrOffs, arenaLen, "hazards"); err != nil {
		return strErr("hazards", err)
	}
	if err := cgasCheckStrs(g.Attrs, attrStrOffs, arenaLen, "attributes"); err != nil {
		return strErr("attributes", err)
	}
	if err := cgasCheckStrs(g.Literals, literalStrOffs, arenaLen, "literals"); err != nil {
		return strErr("literals", err)
	}
	if err := cgasCheckStrs(g.Enums, enumStrOffs, arenaLen, "enum members"); err != nil {
		return strErr("enum members", err)
	}
	if err := cgasCheckStrs(g.Markers, markerStrOffs, arenaLen, "markers"); err != nil {
		return strErr("markers", err)
	}
	if err := cgasCheckStrs(g.Classes, classStrOffs, arenaLen, "classes"); err != nil {
		return strErr("classes", err)
	}
	if err := cgasCheckStrs(g.Exports, exportStrOffs, arenaLen, "exports"); err != nil {
		return strErr("exports", err)
	}
	if err := cgasCheckStrs(g.ImportNames, impNameStrOffs, arenaLen, "import names"); err != nil {
		return strErr("import names", err)
	}
	if err := cgasCheckStrs(g.Listeners, listenerStrOffs, arenaLen, "listeners"); err != nil {
		return strErr("listeners", err)
	}
	if err := cgasCheckStrs(g.Timers, timerStrOffs, arenaLen, "timers"); err != nil {
		return strErr("timers", err)
	}
	if err := cgasCheckStrs(g.Caches, cacheStrOffs, arenaLen, "module caches"); err != nil {
		return strErr("module caches", err)
	}
	if err := cgasCheckStrs(g.Deps, depStrOffs, arenaLen, "dependencies"); err != nil {
		return strErr("dependencies", err)
	}
	if err := cgasCheckStrs(g.JSX, jsxStrOffs, arenaLen, "jsx components"); err != nil {
		return strErr("jsx components", err)
	}
	if err := cgasCheckStrs(g.Hooks, hookStrOffs, arenaLen, "hooks"); err != nil {
		return strErr("hooks", err)
	}
	if err := cgasCheckStrs(g.UserInput, uiStrOffs, arenaLen, "input sites"); err != nil {
		return strErr("input sites", err)
	}
	if err := cgasCheckStrs(g.Routes, routeStrOffs, arenaLen, "routes"); err != nil {
		return strErr("routes", err)
	}
	if err := cgasCheckStrs(g.Secrets, secretStrOffs, arenaLen, "secrets"); err != nil {
		return strErr("secrets", err)
	}
	if err := cgasCheckStrs(g.Meta, metaStrOffs, arenaLen, "meta"); err != nil {
		return strErr("meta", err)
	}
	packedRowSz := int(symColOff[numStoreCols])
	packed := make([]byte, nBlocks*symBlock*packedRowSz)
	for i, b := range sy.blocks {
		base := i * symBlock * packedRowSz
		for r := 0; r < symBlock; r++ {
			src := b[r*numStoreCols : (r+1)*numStoreCols]
			rowOff := base + r*packedRowSz
			for sc := 0; sc < numStoreCols; sc++ {
				v := src[sc]
				if v < 0 || (symColW[sc] == 2 && v > 0xFFFF) {
					return 0, fmt.Errorf("symbol column slot %d holds %d, does not fit its packed width",
						sc, v)
				}
				o := rowOff + int(symColOff[sc])
				packed[o] = byte(v)
				packed[o+1] = byte(v >> 8)
				if symColW[sc] == 4 {
					packed[o+2] = byte(v >> 16)
					packed[o+3] = byte(v >> 24)
				}
			}
		}
	}
	parts := make([][][]byte, cgasNSec+1)
	add := func(id uint32, b []byte) {
		if len(b) > 0 {
			parts[id] = append(parts[id], b)
		}
	}
	add(cgasSecStrings, g.strs)
	add(cgasSecTreeDir, func() []byte {
		d := make([]byte, 12+4*len(g.astTrees))
		cgPutU64(d[0:8], 0, uint64(unsafe.Sizeof(tsRec{})))
		cgPutU32(d[8:12], 0, uint32(len(g.astTrees)))
		for i := range g.astTrees {
			n := uint32(0)
			if tr := g.astTrees[i]; tr != nil {
				n = uint32(len(tr.recs))
			}
			cgPutU32(d[12+4*i:], 0, n)
		}
		return d
	}())
	add(cgasSecFiles, cgasRowBytes(g.Files))
	add(cgasSecMods, cgasRowBytes(g.Modules))
	add(cgasSecSymIDs, cgasRowBytes(sy.ids))
	add(cgasSecSymBlocks, packed)
	add(cgasSecSymPool, cgasRowBytes(sy.pool))
	add(cgasSecParams, cgasRowBytes(g.Params))
	add(cgasSecFields, cgasRowBytes(g.Fields))
	add(cgasSecEdges, cgasRowBytes(g.Edges))
	add(cgasSecCallsites, cgasRowBytes(g.Callsites))
	add(cgasSecUnres, cgasRowBytes(g.Unresolved))
	add(cgasSecImps, cgasRowBytes(g.Imports))
	add(cgasSecHaz, cgasRowBytes(g.Hazards))
	add(cgasSecAttrs, cgasRowBytes(g.Attrs))
	add(cgasSecLits, cgasRowBytes(g.Literals))
	add(cgasSecEnums, cgasRowBytes(g.Enums))
	add(cgasSecMarks, cgasRowBytes(g.Markers))
	add(cgasSecClasses, cgasRowBytes(g.Classes))
	add(cgasSecExports, cgasRowBytes(g.Exports))
	add(cgasSecImpNames, cgasRowBytes(g.ImportNames))
	add(cgasSecListeners, cgasRowBytes(g.Listeners))
	add(cgasSecTimers, cgasRowBytes(g.Timers))
	add(cgasSecCaches, cgasRowBytes(g.Caches))
	add(cgasSecDeps, cgasRowBytes(g.Deps))
	add(cgasSecJSX, cgasRowBytes(g.JSX))
	add(cgasSecHooks, cgasRowBytes(g.Hooks))
	add(cgasSecUIs, cgasRowBytes(g.UserInput))
	add(cgasSecRoutes, cgasRowBytes(g.Routes))
	add(cgasSecSecs, cgasRowBytes(g.Secrets))
	add(cgasSecMeta, cgasRowBytes(g.Meta))
	for i := range g.astTrees {
		if tr := g.astTrees[i]; tr != nil && len(tr.recs) > 0 {
			add(cgasSecTrees, cgasRowBytes(tr.recs))
		}
	}
	type placed struct {
		id      uint32
		off, ln uint64
	}
	dir := make([]placed, 0, cgasNSec)
	cur := uint64(cgasHeaderSz) + cgasNSec*cgasSecSz
	for id := uint32(1); id <= cgasNSec; id++ {
		ln := uint64(0)
		for _, b := range parts[id] {
			ln += uint64(len(b))
		}
		cur = (cur + 7) &^ 7
		dir = append(dir, placed{id, cur, ln})
		cur += ln
	}
	total := cur
	f, err := os.Create(path)
	if err != nil {
		return 0, err
	}
	fail := func(err error) (int64, error) {
		f.Close()
		return 0, fmt.Errorf("write %s: %v", path, err)
	}
	hdr := make([]byte, cgasHeaderSz)
	copy(hdr[0:4], cgasMagic)
	cgPutU32(hdr[4:8], 0, cgasVersion)
	cgPutU32(hdr[8:12], 0, cgasNSec)
	cgPutU64(hdr[16:24], 0, total)
	cgPutU64(hdr[24:32], 0, arenaLen)
	dbuf := make([]byte, cgasNSec*cgasSecSz)
	for i, p := range dir {
		o := i * int(cgasSecSz)
		cgPutU32(dbuf[o:], 0, p.id)
		cgPutU64(dbuf[o+8:], 0, p.off)
		cgPutU64(dbuf[o+16:], 0, p.ln)
	}
	if err := f.Truncate(int64(total)); err != nil {
		return fail(err)
	}
	mem, merr := syscall.Mmap(int(f.Fd()), 0, int(total),
		syscall.PROT_READ|syscall.PROT_WRITE, syscall.MAP_SHARED)
	if merr != nil {
		w := bufio.NewWriterSize(f, 1<<20)
		if _, err := w.Write(hdr); err != nil {
			return fail(err)
		}
		if _, err := w.Write(dbuf); err != nil {
			return fail(err)
		}
		var zero [8]byte
		pos := uint64(cgasHeaderSz) + cgasNSec*cgasSecSz
		for _, p := range dir {
			if p.off > pos {
				if _, err := w.Write(zero[:p.off-pos]); err != nil {
					return fail(err)
				}
			}
			pos = p.off + p.ln
			for _, b := range parts[p.id] {
				if _, err := w.Write(b); err != nil {
					return fail(err)
				}
			}
		}
		if err := w.Flush(); err != nil {
			return fail(err)
		}
	} else {
		copy(mem[0:], hdr)
		copy(mem[cgasHeaderSz:], dbuf)
		for _, p := range dir {
			at := p.off
			for _, b := range parts[p.id] {
				copy(mem[at:], b)
				at += uint64(len(b))
			}
		}
		if err := syscall.Munmap(mem); err != nil {
			return fail(err)
		}
		if err := f.Sync(); err != nil {
			return fail(err)
		}
	}
	if err := f.Close(); err != nil {
		return 0, fmt.Errorf("write %s: %v", path, err)
	}
	return int64(total), nil
}

func loadAST(path string) (*Graph, error) {
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
	bad := func(format string, args ...any) (*Graph, error) {
		syscall.Munmap(mem)
		return nil, fmt.Errorf("%s: "+format, append([]any{path}, args...)...)
	}
	if string(mem[0:4]) != cgasMagic {
		return bad("bad magic %q, want %q -- not an AST state file", string(mem[0:4]), cgasMagic)
	}
	if v := cgGetU32(mem, 4); v != cgasVersion {
		return bad("unsupported state format version %d, want %d", v, cgasVersion)
	}
	secCount := int(cgGetU32(mem, 8))
	total := cgGetU64(mem, 16)
	arenaLen := cgGetU64(mem, 24)
	if secCount != cgasNSec {
		return bad("section count %d, want %d", secCount, cgasNSec)
	}
	if total != uint64(st.Size()) {
		return bad("truncated state file: header declares %d bytes, file has %d", total, st.Size())
	}
	dir := unsafe.Slice((*cgasSec)(unsafe.Pointer(&mem[cgasHeaderSz])), secCount)
	secs := make(map[uint32]cgasSec, secCount)
	for i := range dir {
		sc := dir[i]
		if sc.Off < uint64(cgasHeaderSz) || sc.Off > total || sc.Len > total-sc.Off {
			return bad("section %d lies outside the file", sc.ID)
		}
		if _, dup := secs[sc.ID]; dup {
			return bad("duplicate section %d", sc.ID)
		}
		secs[sc.ID] = sc
	}
	for id := uint32(1); id <= cgasNSec; id++ {
		if _, ok := secs[id]; !ok {
			return bad("missing section %d", id)
		}
	}
	ao, al := secs[cgasSecStrings].Off, secs[cgasSecStrings].Len
	if al != arenaLen {
		return bad("string arena length %d, header says %d", al, arenaLen)
	}
	g := &Graph{Syms: newSymStore()}
	g.Syms.strs = &g.strs
	g.Syms.mu = &g.strsMu
	g.strs = mem[ao : ao+al]
	g.astBlob = mem
	dec := func(id uint32) (uint64, uint64) {
		return secs[id].Off, secs[id].Len
	}
	check := func(what string, err error) (*Graph, error) {
		return bad("%s: %v", what, err)
	}
	off, ln := dec(cgasSecSymIDs)
	symIDs, err := cgasCastRows[[3]uint32](mem, off, ln, "symbol text ids")
	if err != nil {
		return check("symbol text ids", err)
	}
	off, ln = dec(cgasSecSymBlocks)
	packedRowSz := uint64(symColOff[numStoreCols])
	if ln%(packedRowSz*symBlock) != 0 {
		return bad("symbol column store length %d is not a multiple of the packed block size %d",
			ln, packedRowSz*symBlock)
	}
	nBlocksPacked := ln / (packedRowSz * symBlock)
	symFlat := make([]int32, nBlocksPacked*symBlock*numStoreCols)
	for blk := uint64(0); blk < nBlocksPacked; blk++ {
		base := off + blk*packedRowSz*symBlock
		for r := uint64(0); r < symBlock; r++ {
			rowOff := base + r*packedRowSz
			dst := symFlat[(blk*symBlock+r)*numStoreCols : (blk*symBlock+r+1)*numStoreCols]
			for sc := 0; sc < numStoreCols; sc++ {
				o := rowOff + uint64(symColOff[sc])
				if symColW[sc] == 2 {
					dst[sc] = int32(uint16(mem[o]) | uint16(mem[o+1])<<8)
				} else {
					dst[sc] = int32(uint32(mem[o]) | uint32(mem[o+1])<<8 |
						uint32(mem[o+2])<<16 | uint32(mem[o+3])<<24)
				}
			}
		}
	}
	nBlocks := (len(symIDs) + symBlock - 1) / symBlock
	if len(symFlat) != nBlocks*symBlock*numStoreCols {
		return bad("symbol column store holds %d cells, want %d for %d symbols",
			len(symFlat), nBlocks*symBlock*numStoreCols, len(symIDs))
	}
	off, ln = dec(cgasSecSymPool)
	poolRows, err := cgasCastRows[sref](mem, off, ln, "symbol text pool")
	if err != nil {
		return check("symbol text pool", err)
	}
	for i := range symIDs {
		for j := range symIDs[i] {
			if int(symIDs[i][j]) >= len(poolRows) {
				return bad("symbol %d text reference %d escapes the string pool (%d entries)",
					i, symIDs[i][j], len(poolRows))
			}
		}
	}
	if err := cgasCheckStrs(poolRows, poolStrOffs, arenaLen, "symbol text pool"); err != nil {
		return check("symbol text pool", err)
	}
	off, ln = dec(cgasSecFiles)
	files, err := cgasCastRows[File](mem, off, ln, "files")
	if err != nil {
		return check("files", err)
	}
	if err := cgasCheckStrs(files, fileStrOffs, arenaLen, "files"); err != nil {
		return check("files", err)
	}
	off, ln = dec(cgasSecMods)
	mods, err := cgasCastRows[Module](mem, off, ln, "modules")
	if err != nil {
		return check("modules", err)
	}
	if err := cgasCheckStrs(mods, moduleStrOffs, arenaLen, "modules"); err != nil {
		return check("modules", err)
	}
	off, ln = dec(cgasSecParams)
	params, err := cgasCastRows[Param](mem, off, ln, "params")
	if err != nil {
		return check("params", err)
	}
	if err := cgasCheckStrs(params, paramStrOffs, arenaLen, "params"); err != nil {
		return check("params", err)
	}
	off, ln = dec(cgasSecFields)
	fields, err := cgasCastRows[FieldRow](mem, off, ln, "fields")
	if err != nil {
		return check("fields", err)
	}
	if err := cgasCheckStrs(fields, fieldStrOffs, arenaLen, "fields"); err != nil {
		return check("fields", err)
	}
	off, ln = dec(cgasSecEdges)
	edges, err := cgasCastRows[Edge](mem, off, ln, "edges")
	if err != nil {
		return check("edges", err)
	}
	off, ln = dec(cgasSecCallsites)
	callsites, err := cgasCastRows[Callsite](mem, off, ln, "callsites")
	if err != nil {
		return check("callsites", err)
	}
	off, ln = dec(cgasSecUnres)
	unres, err := cgasCastRows[Unresolved](mem, off, ln, "unresolved calls")
	if err != nil {
		return check("unresolved calls", err)
	}
	if err := cgasCheckStrs(unres, unresStrOffs, arenaLen, "unresolved calls"); err != nil {
		return check("unresolved calls", err)
	}
	off, ln = dec(cgasSecImps)
	imps, err := cgasCastRows[Import](mem, off, ln, "imports")
	if err != nil {
		return check("imports", err)
	}
	if err := cgasCheckStrs(imps, importStrOffs, arenaLen, "imports"); err != nil {
		return check("imports", err)
	}
	off, ln = dec(cgasSecHaz)
	haz, err := cgasCastRows[Hazard](mem, off, ln, "hazards")
	if err != nil {
		return check("hazards", err)
	}
	if err := cgasCheckStrs(haz, hazardStrOffs, arenaLen, "hazards"); err != nil {
		return check("hazards", err)
	}
	off, ln = dec(cgasSecAttrs)
	attrs, err := cgasCastRows[Attribute](mem, off, ln, "attributes")
	if err != nil {
		return check("attributes", err)
	}
	if err := cgasCheckStrs(attrs, attrStrOffs, arenaLen, "attributes"); err != nil {
		return check("attributes", err)
	}
	off, ln = dec(cgasSecLits)
	lits, err := cgasCastRows[Literal](mem, off, ln, "literals")
	if err != nil {
		return check("literals", err)
	}
	if err := cgasCheckStrs(lits, literalStrOffs, arenaLen, "literals"); err != nil {
		return check("literals", err)
	}
	off, ln = dec(cgasSecEnums)
	enums, err := cgasCastRows[EnumMember](mem, off, ln, "enum members")
	if err != nil {
		return check("enum members", err)
	}
	if err := cgasCheckStrs(enums, enumStrOffs, arenaLen, "enum members"); err != nil {
		return check("enum members", err)
	}
	off, ln = dec(cgasSecMarks)
	marks, err := cgasCastRows[Marker](mem, off, ln, "markers")
	if err != nil {
		return check("markers", err)
	}
	if err := cgasCheckStrs(marks, markerStrOffs, arenaLen, "markers"); err != nil {
		return check("markers", err)
	}
	off, ln = dec(cgasSecClasses)
	classes, err := cgasCastRows[ClassRow](mem, off, ln, "classes")
	if err != nil {
		return check("classes", err)
	}
	if err := cgasCheckStrs(classes, classStrOffs, arenaLen, "classes"); err != nil {
		return check("classes", err)
	}
	off, ln = dec(cgasSecExports)
	exports, err := cgasCastRows[ExportRow](mem, off, ln, "exports")
	if err != nil {
		return check("exports", err)
	}
	if err := cgasCheckStrs(exports, exportStrOffs, arenaLen, "exports"); err != nil {
		return check("exports", err)
	}
	off, ln = dec(cgasSecImpNames)
	impNames, err := cgasCastRows[ImportName](mem, off, ln, "import names")
	if err != nil {
		return check("import names", err)
	}
	if err := cgasCheckStrs(impNames, impNameStrOffs, arenaLen, "import names"); err != nil {
		return check("import names", err)
	}
	off, ln = dec(cgasSecListeners)
	listeners, err := cgasCastRows[Listener](mem, off, ln, "listeners")
	if err != nil {
		return check("listeners", err)
	}
	if err := cgasCheckStrs(listeners, listenerStrOffs, arenaLen, "listeners"); err != nil {
		return check("listeners", err)
	}
	off, ln = dec(cgasSecTimers)
	timers, err := cgasCastRows[Timer](mem, off, ln, "timers")
	if err != nil {
		return check("timers", err)
	}
	if err := cgasCheckStrs(timers, timerStrOffs, arenaLen, "timers"); err != nil {
		return check("timers", err)
	}
	off, ln = dec(cgasSecCaches)
	caches, err := cgasCastRows[ModuleCache](mem, off, ln, "module caches")
	if err != nil {
		return check("module caches", err)
	}
	if err := cgasCheckStrs(caches, cacheStrOffs, arenaLen, "module caches"); err != nil {
		return check("module caches", err)
	}
	off, ln = dec(cgasSecDeps)
	deps, err := cgasCastRows[DepRow](mem, off, ln, "dependencies")
	if err != nil {
		return check("dependencies", err)
	}
	if err := cgasCheckStrs(deps, depStrOffs, arenaLen, "dependencies"); err != nil {
		return check("dependencies", err)
	}
	off, ln = dec(cgasSecJSX)
	jsx, err := cgasCastRows[JSXComp](mem, off, ln, "jsx components")
	if err != nil {
		return check("jsx components", err)
	}
	if err := cgasCheckStrs(jsx, jsxStrOffs, arenaLen, "jsx components"); err != nil {
		return check("jsx components", err)
	}
	off, ln = dec(cgasSecHooks)
	hooks, err := cgasCastRows[HookRow](mem, off, ln, "hooks")
	if err != nil {
		return check("hooks", err)
	}
	if err := cgasCheckStrs(hooks, hookStrOffs, arenaLen, "hooks"); err != nil {
		return check("hooks", err)
	}
	off, ln = dec(cgasSecUIs)
	uis, err := cgasCastRows[UserInput](mem, off, ln, "input sites")
	if err != nil {
		return check("input sites", err)
	}
	if err := cgasCheckStrs(uis, uiStrOffs, arenaLen, "input sites"); err != nil {
		return check("input sites", err)
	}
	off, ln = dec(cgasSecRoutes)
	routes, err := cgasCastRows[Route](mem, off, ln, "routes")
	if err != nil {
		return check("routes", err)
	}
	if err := cgasCheckStrs(routes, routeStrOffs, arenaLen, "routes"); err != nil {
		return check("routes", err)
	}
	off, ln = dec(cgasSecSecs)
	secs2, err := cgasCastRows[Secret](mem, off, ln, "secrets")
	if err != nil {
		return check("secrets", err)
	}
	if err := cgasCheckStrs(secs2, secretStrOffs, arenaLen, "secrets"); err != nil {
		return check("secrets", err)
	}
	off, ln = dec(cgasSecMeta)
	meta, err := cgasCastRows[metaRow](mem, off, ln, "meta")
	if err != nil {
		return check("meta", err)
	}
	if err := cgasCheckStrs(meta, nil, arenaLen, "meta"); err != nil {
		return check("meta", err)
	}
	tOff, tLn := secs[cgasSecTrees].Off, secs[cgasSecTrees].Len
	dOff, dLn := secs[cgasSecTreeDir].Off, secs[cgasSecTreeDir].Len
	if dLn < 12 {
		return bad("node record directory too small (%d bytes)", dLn)
	}
	dirBytes := unsafe.Slice((*byte)(unsafe.Pointer(uintptr(unsafe.Pointer(&mem[0]))+uintptr(dOff))), int(dLn))
	declStride := cgGetU64(dirBytes, 0)
	nTreeFiles := int(cgGetU32(dirBytes, 8))
	if declStride != uint64(unsafe.Sizeof(tsRec{})) {
		return bad("node record stride %d, want %d", declStride, unsafe.Sizeof(tsRec{}))
	}
	if nTreeFiles != len(files) {
		return bad("node record directory covers %d files, graph has %d", nTreeFiles, len(files))
	}
	if int(dLn) < 12+4*nTreeFiles {
		return bad("node record directory too small for %d files", nTreeFiles)
	}
	var counts []uint32
	if nTreeFiles > 0 {
		counts = unsafe.Slice((*uint32)(unsafe.Pointer(&dirBytes[12])), nTreeFiles)
	}
	stride := uint64(unsafe.Sizeof(tsRec{}))
	if tLn%stride != 0 {
		return bad("node record arena length %d is not a multiple of the record stride", tLn)
	}
	recsAll := unsafe.Slice((*tsRec)(unsafe.Pointer(uintptr(unsafe.Pointer(&mem[0]))+uintptr(tOff))), int(tLn/stride))
	if tLn > 0 && uintptr(unsafe.Alignof(tsRec{})) > 1 &&
		uintptr(unsafe.Pointer(&recsAll[0]))%uintptr(unsafe.Alignof(tsRec{})) != 0 {
		return bad("node record arena is not %d-byte aligned", unsafe.Alignof(tsRec{}))
	}
	g.Syms.ids = symIDs
	g.Syms.blocks = make([][]int32, nBlocks)
	for i := range g.Syms.blocks {
		g.Syms.blocks[i] = symFlat[i*symBlock*numStoreCols : (i+1)*symBlock*numStoreCols]
	}
	g.Syms.pool = poolRows
	g.Syms.byStr = make(map[string]uint32, len(poolRows))
	for i := range poolRows {
		g.Syms.byStr[g.Syms.view(poolRows[i])] = uint32(i)
	}
	g.Meta = meta
	g.Modules = mods
	g.Files = files
	g.Params = params
	g.Fields = fields
	g.Edges = edges
	g.Callsites = callsites
	g.Unresolved = unres
	g.Imports = imps
	g.Hazards = haz
	g.Attrs = attrs
	g.Literals = lits
	g.Enums = enums
	g.Markers = marks
	g.Classes = classes
	g.Exports = exports
	g.ImportNames = impNames
	g.Listeners = listeners
	g.Timers = timers
	g.Caches = caches
	g.Deps = deps
	g.JSX = jsx
	g.Hooks = hooks
	g.UserInput = uis
	g.Routes = routes
	g.Secrets = secs2
	g.astTrees = make([]*tsTree, nTreeFiles)
	base := 0
	for i := 0; i < nTreeFiles; i++ {
		n := int(counts[i])
		if base+n > len(recsAll) {
			return bad("node record directory overruns the record arena")
		}
		if n > 0 {
			g.astTrees[i] = &tsTree{recs: recsAll[base : base+n]}
		}
		base += n
	}
	if base != len(recsAll) {
		return bad("node record arena has %d unused records", len(recsAll)-base)
	}
	g.buildIndex()
	return g, nil
}
