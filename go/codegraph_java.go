package main

import (
	"bufio"
	"bytes"
	"crypto/sha1"
	"encoding/csv"
	"encoding/hex"
	"encoding/json"
	"encoding/json/jsontext"
	jsonv2 "encoding/json/v2"
	"fmt"
	"io"
	"iter"
	"maps"
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
	tsGrammarTag  = "v0.23.5"
	tsGrammarRepo = "https://github.com/tree-sitter/tree-sitter-java"
)

var tsTablesData = initTSTables()

var (
	tsAbiVersion = 0
	tsSymCount   = len(tsTablesData.symNames)
	tsFieldCount = len(tsTablesData.fieldNames)
	tsSymNamed   = tsTablesData.symNamed
	tsSymVisible = tsTablesData.symVisible
	tsSymSuper   = tsTablesData.symSuper
	tsSymPublic  = tsTablesData.symPublic
	tsSymNames   = tsTablesData.symNames
	tsFieldNames = tsTablesData.fieldNames
	tsAnonField  = tsTablesData.anonField
)

type tsTables struct {
	symPublic  []uint16
	symNames   []string
	fieldNames []string
	anonField  []uint16
	symNamed   []bool
	symVisible []bool
	symSuper   []bool
}

func tsGrammarsBase() string {
	if d := os.Getenv("TREE_SITTER_GRAMMARS"); d != "" {
		return d
	}
	home, err := os.UserHomeDir()
	if err != nil {
		fmt.Fprintln(os.Stderr, "codegraph_java: cannot resolve home:", err)
		os.Exit(1)
	}
	return filepath.Join(home, ".cache", "codegraph", "grammars")
}

func tsGrammarDir() string {
	return filepath.Join(tsGrammarsBase(), "tree-sitter-java")
}

func tsGrammarFatal(gd string, err error) {
	msg := ""
	if err != nil {
		msg = ": " + err.Error()
	}
	home, _ := os.UserHomeDir()
	fmt.Fprintf(os.Stderr, `codegraph_java: the pinned grammar's JSON sources are missing under %s%s
this port reads its kind tables from them at startup (no generated file, no C).
run:
  mkdir -p %s
  git clone --depth 1 --branch %s %s %s
then make sure %s lists that parent directory under "parser-directories" so
the tree-sitter CLI resolves --scope source.java.`,
		gd, msg, filepath.Dir(gd), tsGrammarTag, tsGrammarRepo, gd,
		filepath.Join(home, ".config", "tree-sitter", "config.json"))
	os.Exit(1)
}

func tsReadJSON(path string, v any) {
	gd := filepath.Dir(filepath.Dir(path))
	b, err := os.ReadFile(path)
	if err != nil {
		tsGrammarFatal(gd, err)
	}
	if err := jsonv2.Unmarshal(b, v); err != nil {
		tsGrammarFatal(gd, err)
	}
}

type tsNTType struct {
	Type  string `json:"type"`
	Named *bool  `json:"named"`
}

type tsNTField struct {
	Types []tsNTType `json:"types"`
}

type tsOrderedObj []tsKV

type tsKV struct {
	Key  string
	Spec tsNTField
}

func (o *tsOrderedObj) UnmarshalJSONFrom(dec *jsontext.Decoder) error {
	tok, err := dec.ReadToken()
	if err != nil {
		return err
	}
	if tok.Kind() != '{' {
		return fmt.Errorf("expected a JSON object, got %v", tok)
	}
	for dec.PeekKind() != '}' {
		nameTok, err := dec.ReadToken()
		if err != nil {
			return err
		}
		key := nameTok.String()
		var spec tsNTField
		if err := jsonv2.UnmarshalDecode(dec, &spec); err != nil {
			return err
		}

		replaced := false
		for i := range *o {
			if (*o)[i].Key == key {
				(*o)[i].Spec = spec
				replaced = true
				break
			}
		}
		if !replaced {
			*o = append(*o, tsKV{Key: key, Spec: spec})
		}
	}
	_, err = dec.ReadToken()
	return err
}

type tsNodeType struct {
	Type   string       `json:"type"`
	Named  *bool        `json:"named"`
	Fields tsOrderedObj `json:"fields"`
}

type tsGrammar struct {
	Supertypes []string `json:"supertypes"`
}

func initTSTables() *tsTables {
	gd := tsGrammarDir()
	ntPath := filepath.Join(gd, "src", "node-types.json")
	grPath := filepath.Join(gd, "src", "grammar.json")
	if _, err := os.Stat(ntPath); err != nil {
		tsGrammarFatal(gd, nil)
	}
	if _, err := os.Stat(grPath); err != nil {
		tsGrammarFatal(gd, nil)
	}
	var nodeTypes []tsNodeType
	tsReadJSON(ntPath, &nodeTypes)
	var grammar tsGrammar
	tsReadJSON(grPath, &grammar)

	type kindFields struct {
		order []string
		anon  map[string]bool
	}
	kinds := map[string]*kindFields{}
	var order []string
	var fields []string
	seenField := map[string]bool{}

	namedOf := func(name string) bool {
		for i := range nodeTypes {
			if nodeTypes[i].Type == name {
				if nodeTypes[i].Named != nil {
					return *nodeTypes[i].Named
				}
				return true
			}
		}
		return true
	}

	for i := range nodeTypes {
		e := &nodeTypes[i]
		kf := kinds[e.Type]
		if kf == nil {
			kf = &kindFields{anon: map[string]bool{}}
			kinds[e.Type] = kf
			order = append(order, e.Type)
		}
		for _, kv := range e.Fields {
			if kv.Key != "" && !seenField[kv.Key] {
				seenField[kv.Key] = true
				fields = append(fields, kv.Key)
			}
			anonOnly := len(kv.Spec.Types) > 0
			for _, ty := range kv.Spec.Types {
				if ty.Named == nil || *ty.Named {
					anonOnly = false
					break
				}
			}
			if prev, ok := kf.anon[kv.Key]; ok {
				kf.anon[kv.Key] = prev && anonOnly
			} else {
				kf.anon[kv.Key] = anonOnly
				kf.order = append(kf.order, kv.Key)
			}
		}
	}

	type sym struct {
		name                 string
		named, visible, supr bool
	}
	var syms []sym
	for _, name := range order {
		syms = append(syms, sym{name: name, named: namedOf(name), visible: true})
	}
	inSyms := map[string]bool{}
	for _, s := range syms {
		inSyms[s.name] = true
	}
	for _, name := range grammar.Supertypes {
		if !inSyms[name] {
			inSyms[name] = true
			syms = append(syms, sym{name: name, named: true, supr: true})
		} else {
			for j := range syms {
				if syms[j].name == name {
					syms[j].supr = true
				}
			}
		}
	}
	syms = append(syms,
		sym{name: "ERROR", named: true, visible: true},
		sym{name: "\x00MISSING", named: true, visible: true})

	t := &tsTables{
		symPublic:  make([]uint16, len(syms)),
		symNames:   make([]string, len(syms)),
		anonField:  make([]uint16, len(syms)),
		symNamed:   make([]bool, len(syms)),
		symVisible: make([]bool, len(syms)),
		symSuper:   make([]bool, len(syms)),
	}
	fieldID := map[string]uint16{}
	t.fieldNames = append(t.fieldNames, "")
	for i, f := range fields {
		fieldID[f] = uint16(i + 1)
		t.fieldNames = append(t.fieldNames, f)
	}
	for i, s := range syms {
		t.symNamed[i] = s.named
		t.symVisible[i] = s.visible
		t.symSuper[i] = s.supr
		t.symPublic[i] = uint16(i)
		t.symNames[i] = s.name
		if kf := kinds[s.name]; kf != nil {
			for _, f := range kf.order {
				if kf.anon[f] {
					t.anonField[i] = fieldID[f]
					break
				}
			}
		}
	}
	return t
}

const tsScope = "source.java"

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
	bin     string
	recs    []tsRec
	starts  []int
	stack   []cstFrame
	env     []string
	devnull *os.File
	cfgPath string
}

type cstFrame struct {
	i   int32
	end uint32
}

func newTSParser() *tsParser {
	bin := tsCLIBin()
	if _, err := os.Stat(bin); err != nil {
		panic("tree-sitter CLI not found at " + bin +
			" -- install the pinned version with: cargo install tree-sitter-cli --version 0.25.10 --root \"$HOME/.cache/codegraph\" (or set TREE_SITTER_BIN)")
	}
	devnull, dnerr := os.OpenFile(os.DevNull, os.O_RDWR, 0)
	if dnerr != nil {
		panic("open /dev/null: " + dnerr.Error())
	}
	cfgPath := ""
	if home, err := os.UserHomeDir(); err == nil {
		c := home + "/.config/tree-sitter/config.json"
		if _, serr := os.Stat(c); serr == nil {
			cfgPath = c
		}
	}
	return &tsParser{bin: bin, env: append(os.Environ(), "NO_COLOR=1", "TERM=dumb"),
		devnull: devnull, cfgPath: cfgPath}
}

func blockingPipe() (*os.File, *os.File, error) {
	var fds [2]int
	if err := syscall.Pipe(fds[:]); err != nil {
		return nil, nil, err
	}
	syscall.CloseOnExec(fds[0])
	syscall.CloseOnExec(fds[1])
	return os.NewFile(uintptr(fds[0]), "pipe"), os.NewFile(uintptr(fds[1]), "pipe"), nil
}

func readPipe(r *os.File, buf *[]byte, est int) ([]byte, error) {
	out := (*buf)[:0]
	if cap(out) < est {
		out = make([]byte, 0, est)
	}
	for {
		if len(out) == cap(out) {
			grown := make([]byte, len(out), 2*cap(out))
			copy(grown, out)
			out = grown
		}
		n, err := r.Read(out[len(out):cap(out)])
		out = out[:len(out)+n]
		if err != nil {
			*buf = out
			return out, err
		}
	}
}

func writeAll(f *os.File, b []byte) error {
	for len(b) > 0 {
		n, err := f.Write(b)
		b = b[n:]
		if err != nil {
			return err
		}
	}
	return nil
}

func (p *tsParser) parse(src []byte, buf []byte) []byte {
	cmd := exec.Command(p.bin, "parse", "/dev/stdin", "--scope", tsScope,
		"--cst", "--config-path", p.cfgPath)
	cmd.Env = p.env
	cmd.Stderr = p.devnull
	inR, inW, perr := blockingPipe()
	if perr != nil {
		return nil
	}
	outR, outW, oerr := blockingPipe()
	if oerr != nil {
		inR.Close()
		inW.Close()
		return nil
	}
	cmd.Stdin = inR
	cmd.Stdout = outW
	if serr := cmd.Start(); serr != nil {
		inR.Close()
		inW.Close()
		outR.Close()
		outW.Close()
		return nil
	}
	inR.Close()
	outW.Close()
	writeAll(inW, src)
	inW.Close()
	est := 24*len(src) + 4096
	if est < 64<<10 {
		est = 64 << 10
	}
	out, rerr := readPipe(outR, &buf, est)
	outR.Close()
	err := cmd.Wait()
	if err != nil && len(out) == 0 {
		return nil
	}
	if rerr != nil && rerr != io.EOF && len(out) == 0 {
		return nil
	}
	return out
}

type tsTree struct {
	recs []tsRec
}

func (t *tsTree) close() {}

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

func (n tsNode) ok() bool { return n.t != nil }

func (n tsNode) kindID() uint16 {
	if !n.ok() {
		return tsSymInvalid
	}
	return n.t.recs[n.i].sym
}

func (n tsNode) isNamed() bool {
	if !n.ok() {
		return false
	}
	return n.t.recs[n.i].flags&tsFlagNamed != 0
}

func (n tsNode) isMissing() bool {
	if !n.ok() {
		return false
	}
	return n.t.recs[n.i].flags&tsFlagMiss != 0
}

func (n tsNode) hasError() bool {
	if !n.ok() {
		return false
	}
	return n.t.recs[n.i].flags&tsFlagErr != 0
}

func (n tsNode) startByte() int { return int(n.t.recs[n.i].start) }

func (n tsNode) endByte() int {
	if !n.ok() {
		return 0
	}
	return int(n.t.recs[n.i].end)
}

func (n tsNode) startRow() int { return int(n.t.recs[n.i].srow) }

func (n tsNode) endRow() int {
	if !n.ok() {
		return 0
	}
	return int(n.t.recs[n.i].erow)
}

func (n tsNode) childCount() int {
	if !n.ok() {
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

func (n tsNode) namedChildCount() int {
	if !n.ok() {
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

func (n tsNode) child(k int) tsNode {
	if !n.ok() || k >= n.childCount() {
		return tsNode{}
	}
	c := n.i + 1
	for range k {
		c = n.t.recs[c].subEnd
	}
	return tsNode{t: n.t, i: c}
}

func (n tsNode) namedChild(k int) tsNode {
	if !n.ok() {
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

func (n tsNode) childByFieldName(f tsFieldID) tsNode {
	if !n.ok() || f == 0 {
		return tsNode{}
	}
	for c, end := n.i+1, n.t.recs[n.i].subEnd; c < end; c = n.t.recs[c].subEnd {
		if n.t.recs[c].field == f {
			return tsNode{t: n.t, i: c}
		}
	}
	return tsNode{}
}

func (n tsNode) parent() tsNode {
	if !n.ok() {
		return tsNode{}
	}
	pi := n.t.recs[n.i].parent
	if pi < 0 {
		return tsNode{}
	}
	return tsNode{t: n.t, i: pi}
}

func (n tsNode) prevSibling() tsNode {
	if !n.ok() {
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

func (n tsNode) nextNamedSibling() tsNode {
	if !n.ok() {
		return tsNode{}
	}
	pi := n.t.recs[n.i].parent
	if pi < 0 {
		return tsNode{}
	}
	for c, end := n.t.recs[n.i].subEnd, n.t.recs[pi].subEnd; c < end; c = n.t.recs[c].subEnd {
		if n.t.recs[c].flags&tsFlagNamed != 0 {
			return tsNode{t: n.t, i: c}
		}
	}
	return tsNode{}
}

func (n tsNode) sameAs(o tsNode) bool { return n.t == o.t && n.i == o.i }

func (n tsNode) fieldNameIs(i int, name string) bool {
	c := n.child(i)
	if !c.ok() {
		return false
	}
	if fid := c.t.recs[c.i].field; fid != 0 && int(fid) < len(tsFieldNames) {
		return tsFieldNames[fid] == name
	}
	return false
}

type tsCursor struct {
	t      *tsTree
	stack  []int32
	cur    int32
	dead   bool
	pooled bool
}

var cursorPool = sync.Pool{New: func() any { return new(tsCursor) }}

func tsWalk(n tsNode) *tsCursor {
	cu := cursorPool.Get().(*tsCursor)
	cu.pooled = false
	if !n.ok() {
		cu.dead = true
		return cu
	}
	cu.dead = false
	cu.t = n.t
	cu.stack = append(cu.stack[:0], n.i)
	cu.cur = n.i
	return cu
}

func (cu *tsCursor) free() {
	if cu.pooled {
		return
	}
	cu.pooled = true
	cu.dead = true
	cu.t = nil
	cu.stack = cu.stack[:0]
	cursorPool.Put(cu)
}

func (cu *tsCursor) node() tsNode {
	if cu.dead {
		return tsNode{}
	}
	return tsNode{t: cu.t, i: cu.cur}
}

func (cu *tsCursor) first() bool {
	if cu.dead {
		return false
	}
	end := cu.t.recs[cu.cur].subEnd
	if cu.cur+1 >= end {
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

func tsSymbolName(i int) string {
	if i >= 0 && i < len(tsSymNames) {
		return tsSymNames[i]
	}
	return ""
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

func tsFieldIDForName(name string) tsFieldID {
	for f := 1; f < tsFieldCount; f++ {
		if tsFieldNames[f] == name {
			return tsFieldID(f)
		}
	}
	return 0
}

var (
	fName         = tsFieldIDForName("name")
	fType         = tsFieldIDForName("type")
	fBody         = tsFieldIDForName("body")
	fParameters   = tsFieldIDForName("parameters")
	fValue        = tsFieldIDForName("value")
	fObject       = tsFieldIDForName("object")
	fTypeParams   = tsFieldIDForName("type_parameters")
	fLeft         = tsFieldIDForName("left")
	fArguments    = tsFieldIDForName("arguments")
	fCondition    = tsFieldIDForName("condition")
	fAlternative  = tsFieldIDForName("alternative")
	fRight        = tsFieldIDForName("right")
	fModule       = tsFieldIDForName("module")
	fKey          = tsFieldIDForName("key")
	fInterfaces   = tsFieldIDForName("interfaces")
	fDefaultValue = tsFieldIDForName("default_value")
	fConsequence  = tsFieldIDForName("consequence")
	fSuperclass   = tsFieldIDForName("superclass")
	fPermits      = tsFieldIDForName("permits")
)

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

func decodeCST(p *tsParser, out, src []byte) (*tsTree, error) {
	starts := p.starts
	if cap(starts) == 0 {
		starts = make([]int, 1, 4096)
	} else {
		starts = starts[:1]
	}
	total := len(src)
	for i := 0; i < len(src); {
		j := bytes.IndexByte(src[i:], '\n')
		if j < 0 {
			break
		}
		i += j + 1
		starts = append(starts, i)
	}
	p.starts = starts
	d := &cstDecoder{starts: starts, total: total}

	recs := p.recs[:0]
	var stack []cstFrame
	stack = p.stack[:0]

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

		if srow > 0xFFFF || erow > 0xFFFF {
			return nil, fmt.Errorf("line %d-%d exceeds the 16-bit record line range", srow, erow)
		}

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
			par := stack[len(stack)-1].i
			recs[idx].parent = par

			if !named {
				if f := tsAnonField[recs[par].sym]; f != 0 {
					recs[idx].field = f
				}
			}
		}
		stack = append(stack, cstFrame{i: idx, end: end})
	}

	for len(stack) > 0 {
		popped := stack[len(stack)-1]
		recs[popped.i].subEnd = int32(len(recs))
		stack = stack[:len(stack)-1]
	}
	if len(recs) == 0 {
		p.recs = recs
		p.stack = stack[:0]
		return nil, fmt.Errorf("no nodes decoded (cli produced %d bytes)", len(out))
	}
	recs[0].parent = -1

	n := len(recs)
	for i := n - 1; i >= 0; i-- {
		r := &recs[i]
		if pi := r.parent; pi >= 0 {
			pr := &recs[pi]
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

	for i := range recs {
		f := tsAnonField[recs[i].sym]
		if f == 0 {
			continue
		}
		n := 0
		for c, end := int(i)+1, int(recs[i].subEnd); c < end; c = int(recs[c].subEnd) {
			if recs[c].field == f {
				n++
			}
		}
		if n > 1 {
			for c, end := int(i)+1, int(recs[i].subEnd); c < end; c = int(recs[c].subEnd) {
				if recs[c].field == f {
					recs[c].field = 0
				}
			}
		}
	}
	p.recs = recs
	p.stack = stack[:0]
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

func writeCSV(out *bufio.Writer, cols []string, rows [][]any) {
	w := csv.NewWriter(out)

	w.UseCRLF = true
	_ = w.Write(cols)
	for _, r := range rows {
		rec := make([]string, len(r))
		for i, v := range r {
			rec[i] = cellText(v)
		}
		_ = w.Write(rec)
	}
	w.Flush()
}

func writeJSON(out *bufio.Writer, cols []string, rows [][]any) {
	enc := json.NewEncoder(out)
	enc.SetEscapeHTML(false)
	enc.SetIndent("", "  ")
	items := make([]jsonRow, 0, len(rows))
	for _, r := range rows {
		vals := make([]any, len(cols))
		for i := range cols {
			if i < len(r) {
				vals[i] = jsonValue(r[i])
			}
		}
		items = append(items, jsonRow{keys: cols, vals: vals})
	}
	_ = enc.Encode(items)
}

type jsonRow struct {
	keys []string
	vals []any
}

func (r jsonRow) MarshalJSON() ([]byte, error) {
	var b bytes.Buffer
	b.WriteByte('{')
	for i, k := range r.keys {
		if i > 0 {
			b.WriteByte(',')
		}
		kb, err := encodeOne(k)
		if err != nil {
			return nil, err
		}
		b.Write(kb)
		b.WriteByte(':')
		vb, err := encodeOne(r.vals[i])
		if err != nil {
			return nil, err
		}
		b.Write(vb)
	}
	b.WriteByte('}')
	return b.Bytes(), nil
}

func encodeOne(v any) ([]byte, error) {
	var buf bytes.Buffer
	e := json.NewEncoder(&buf)
	e.SetEscapeHTML(false)
	if err := e.Encode(v); err != nil {
		return nil, err
	}
	b := buf.Bytes()
	if n := len(b); n > 0 && b[n-1] == '\n' {
		b = b[:n-1]
	}
	return b, nil
}

func jsonValue(v any) any {
	switch t := v.(type) {
	case nil:
		return nil
	case string:
		return t
	case bool:
		return t
	case int:
		return int64(t)
	case int32:
		return int64(t)
	case int64:
		return t
	case uint32:
		return int64(t)
	case float64:

		return json.RawMessage(cgRepr(t))
	case float32:
		return json.RawMessage(cgRepr(float64(t)))
	default:
		return cellText(v)
	}
}

func cellText(v any) string {
	switch t := v.(type) {
	case nil:
		return ""
	case string:
		return t
	case bool:
		if t {
			return "True"
		}
		return "False"
	case int:
		return strconv.Itoa(t)
	case int32:
		return strconv.FormatInt(int64(t), 10)
	case int64:
		return strconv.FormatInt(t, 10)
	case uint32:
		return strconv.FormatUint(uint64(t), 10)
	case float64:
		return cgRepr(t)
	case float32:
		return cgRepr(float64(t))
	default:
		return sprintf("%v", v)
	}
}

const nullStr uint32 = 0

const (
	chunkMin = 1 << 13
	chunkMax = 1 << 20
	offBits  = 20
	offMask  = (1 << offBits) - 1
)

type Interner struct {
	chunks [][]byte
	used   int

	pos []uint32
	ln  []uint32
	idx map[string]uint32

	next uint32
}

const nullReserved = "\x00nil"

func NewInterner() *Interner {
	it := &Interner{idx: make(map[string]uint32, 1<<12)}
	it.intern(nullReserved)
	return it
}

func (it *Interner) intern(s string) uint32 {
	if id, ok := it.idx[s]; ok {
		return id
	}
	n := len(s)
	if n >= chunkMax {

		it.chunks = append(it.chunks, make([]byte, n))
		it.used = n
		return it.commit(uint32(len(it.chunks)-1)<<offBits, n)
	}
	if last := len(it.chunks) - 1; last < 0 || it.used+n > len(it.chunks[last]) {
		size := chunkMin
		for i := 0; i < len(it.chunks) && size < chunkMax; i++ {
			size *= 2
		}
		if n > size {
			size = n
		}
		it.chunks = append(it.chunks, make([]byte, size))
		it.used = 0
	}
	pos := uint32(len(it.chunks)-1)<<offBits | uint32(it.used)
	copy(it.chunks[len(it.chunks)-1][it.used:], s)
	it.used += n
	return it.commit(pos, n)
}

func (it *Interner) commit(pos uint32, n int) uint32 {
	id := it.next
	it.next++
	it.pos = append(it.pos, pos)
	it.ln = append(it.ln, uint32(n))

	it.idx[it.view(pos, n)] = id
	return id
}

func (it *Interner) view(pos uint32, n int) string {
	if n == 0 {
		return ""
	}
	b := it.chunks[pos>>offBits][pos&offMask : (pos&offMask)+uint32(n)]
	return unsafe.String(unsafe.SliceData(b), n)
}

func (it *Interner) get(id uint32) string {
	if id == nullStr {
		return ""
	}
	return it.view(it.pos[id], int(it.ln[id]))
}

func (it *Interner) count() int { return int(it.next) }

func (it *Interner) reserve(n int) {
	if n <= len(it.pos) {
		return
	}
	if cap(it.pos) < n {
		pos := make([]uint32, len(it.pos), n)
		copy(pos, it.pos)
		it.pos = pos
		ln := make([]uint32, len(it.ln), n)
		copy(ln, it.ln)
		it.ln = ln
	}
	m := make(map[string]uint32, n)
	maps.Copy(m, it.idx)
	it.idx = m
}

func fsub(a, b float64) float64 { return a - b }

func fmul(a, b float64) float64 { return a * b }

func likeMatch(s, pattern string) bool {
	if pattern == "%" {
		return true
	}
	return likeAt(strings.ToLower(s), strings.ToLower(pattern), 0, 0)
}

func likeAt(s, p string, si, pi int) bool {
	for pi < len(p) {
		switch p[pi] {
		case '%':
			for k := si; k <= len(s); k++ {
				if likeAt(s, p, k, pi+1) {
					return true
				}
			}
			return false
		case '_':
			if si >= len(s) {
				return false
			}
			_, sz := decodeRune(s[si:])
			si += sz
			pi++
		default:
			if si >= len(s) || s[si] != p[pi] {
				return false
			}
			si++
			pi++
		}
	}
	return si == len(s)
}

func toF(v any) (float64, bool) {
	switch x := v.(type) {
	case int:
		return float64(x), true
	case int32:
		return float64(x), true
	case int64:
		return float64(x), true
	case float64:
		return x, true
	}
	return 0, false
}

func strOf(v any) string {
	if s, ok := v.(string); ok {
		return s
	}
	return ""
}

type sortKey struct {
	col      int
	asc      bool
	coalesce string
	hasCo    bool
}

func sortRows(rows [][]any, keys ...sortKey) {
	sort.SliceStable(rows, func(a, b int) bool {
		for _, k := range keys {
			av, bv := rows[a][k.col], rows[b][k.col]
			if k.hasCo {
				av, bv = k.coalesce, k.coalesce
			}
			an, bn := av == nil, bv == nil
			if an || bn {
				if an && bn {
					continue
				}

				if k.asc {
					return an
				}
				return bn
			}
			c := compareVals(av, bv)
			if c == 0 {
				continue
			}
			if k.asc {
				return c < 0
			}
			return c > 0
		}
		return false
	})
}

func compareVals(a, b any) int {
	as, aIsStr := a.(string)
	bs, bIsStr := b.(string)
	if aIsStr && bIsStr {
		return strings.Compare(as, bs)
	}
	af, aok := toF(a)
	bf, bok := toF(b)
	if aok && bok {
		switch {
		case af < bf:
			return -1
		case af > bf:
			return 1
		}
		return 0
	}
	return strings.Compare(strOf(a), strOf(b))
}

func limitRows(rows [][]any, lim int) [][]any {
	if lim >= 0 && len(rows) > lim {
		return rows[:lim]
	}
	return rows
}

func (g *Graph) at(fid, line int32) string {
	return g.Files[fid-1].Path(g.Str) + ":" + itoa(int(line))
}

func itoa(v int) string {
	if v == 0 {
		return "0"
	}
	neg := v < 0
	if neg {
		v = -v
	}
	var b [24]byte
	i := len(b)
	for v > 0 {
		i--
		b[i] = byte('0' + v%10)
		v /= 10
	}
	if neg {
		i--
		b[i] = '-'
	}
	return string(b[i:])
}

func (g *Graph) modName(mid int32) string { return g.Str.get(g.Mod[mid-1].Name) }

func walkPre(root tsNode, fn func(tsNode) bool) {
	stack := []tsNode{root}
	for len(stack) > 0 {
		n := stack[len(stack)-1]
		stack = stack[:len(stack)-1]
		if !fn(n) {
			return
		}
		for i := int(n.childCount()) - 1; i >= 0; i-- {
			if c := n.child(i); c.ok() {
				stack = append(stack, c)
			}
		}
	}
}

func decodeRune(s string) (rune, int) { return utf8.DecodeRuneInString(s) }

const helpText = `usage: codegraph_java.py [-h] [--module MODULE] [--limit LIMIT] [--list]
                         [--csv N] [--json N] [--save PATH] [--save-ast PATH]
                         [--load-ast PATH] [--force] [--deps]
                         [--install-deps] [--include-generated]
                         [--include-vendored] [--no-tests] [--quiet]
                         [--version]
                         [root] [which ...]

Parse a java tree into an in-memory graph and query it in one shot. Target: Java 25 (LTS)

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

var runtimeMeta = map[string]bool{"built_at": true,
	"free_threading": true, "parse_concurrency": true}

type dumpBuf struct {
	w *bufio.Writer

	scratch []byte
	arena   []byte
	offs    []int32
}

func (d *dumpBuf) row(b []byte) {
	d.arena = append(d.arena, b...)
	d.offs = append(d.offs, int32(len(d.arena)))
}

func (d *dumpBuf) table(name string, ncols int) {
	a := d.arena
	o := d.offs
	idx := make([]int32, len(o))
	for i := range idx {
		idx[i] = int32(i)
	}
	sort.Slice(idx, func(x, y int) bool {
		sx, ex := rowBounds(a, o, idx[x])
		sy, ey := rowBounds(a, o, idx[y])
		return bytesLess(a[sx:ex], a[sy:ey])
	})
	w := d.w
	w.WriteString("T ")
	w.WriteString(name)
	w.WriteByte(' ')
	w.WriteString(strconv.Itoa(ncols))
	w.WriteByte(' ')
	w.WriteString(strconv.Itoa(len(o)))
	w.WriteByte('\n')
	for _, i := range idx {
		s, e := rowBounds(a, o, i)
		w.Write(a[s:e])
		w.WriteByte('\n')
	}
	w.WriteString("E ")
	w.WriteString(name)
	w.WriteByte('\n')
	d.arena = a[:0]
	d.offs = o[:0]
}

func rowBounds(a []byte, o []int32, i int32) (int, int) {
	s := 0
	if i > 0 {
		s = int(o[i-1])
	}
	return s, int(o[i])
}

func bytesLess(a, b []byte) bool {
	n := min(len(b), len(a))
	for i := 0; i < n; i++ {
		if a[i] != b[i] {
			return a[i] < b[i]
		}
	}
	return len(a) < len(b)
}

func encInt(b []byte, v int64) []byte {
	b = append(b, 'i', ':')
	return strconv.AppendInt(b, v, 10)
}

func encNull(b []byte) []byte { return append(b, '\\', 'N') }

func encText(b []byte, s string) []byte {
	b = append(b, 's', ':')
	return escText(b, s)
}

func escText(b []byte, s string) []byte {
	for i := 0; i < len(s); {
		c := s[i]
		if c < 0x80 {
			switch c {
			case '\\':
				b = append(b, '\\', '\\')
			case '\n':
				b = append(b, '\\', 'n')
			case '\t':
				b = append(b, '\\', 't')
			case '\r':
				b = append(b, '\\', 'r')
			default:
				if c < 0x20 || c == 0x7F {
					b = append(b, '\\', 'x',
						"0123456789ABCDEF"[c>>4], "0123456789ABCDEF"[c&0xf])
				} else {
					b = append(b, c)
				}
			}
			i++
			continue
		}
		_, sz := decodeRuneLen(s[i:])
		b = append(b, s[i:i+sz]...)
		i += sz
	}
	return b
}

func decodeRuneLen(s string) (rune, int) {
	if len(s) == 0 {
		return 0, 1
	}
	if s[0] < 0x80 {
		return rune(s[0]), 1
	}

	n := 1
	switch {
	case s[0]&0xe0 == 0xc0:
		n = 2
	case s[0]&0xf0 == 0xe0:
		n = 3
	case s[0]&0xf8 == 0xf0:
		n = 4
	}
	if n > len(s) {
		n = len(s)
	}
	return rune(s[0]), n
}

func cgRepr(f float64) string {
	if f != f {
		return "nan"
	}
	if f > 1.7976931348623157e308 {
		return "inf"
	}
	if f < -1.7976931348623157e308 {
		return "-inf"
	}
	neg := false
	if f < 0 {
		neg = true
		f = -f
	}
	if f == 0 {
		if math.Signbit(f) {
			return "-0.0"
		}
		return "0.0"
	}
	mant := strconv.FormatFloat(f, 'e', -1, 64)
	epos := strings.IndexByte(mant, 'e')
	digits := strings.Replace(mant[:epos], ".", "", 1)
	exp, _ := strconv.Atoi(mant[epos+1:])
	decpt := exp + 1
	var out string
	switch {
	case decpt <= -4 || decpt > 16:
		es := "e+"
		e := exp
		if e < 0 {
			es = "e-"
			e = -e
		}
		out = digits[:1]
		if len(digits) > 1 {
			out += "." + digits[1:]
		}
		out += es
		if e < 10 {
			out += "0"
		}
		out += strconv.Itoa(e)
	case decpt <= 0:
		out = "0." + strings.Repeat("0", -decpt) + digits
	case decpt >= len(digits):
		out = digits + strings.Repeat("0", decpt-len(digits)) + ".0"
	default:
		out = digits[:decpt] + "." + digits[decpt:]
	}
	if neg {
		return "-" + out
	}
	return out
}

func encFloat(b []byte, f float64) []byte {
	b = append(b, 'f', ':')
	return append(b, cgRepr(f)...)
}

func writeDump(path string, g *Graph) error {
	f, err := os.Create(path)
	if err != nil {
		return err
	}
	defer f.Close()
	d := &dumpBuf{w: bufio.NewWriterSize(f, 1<<20),
		scratch: make([]byte, 0, 1<<16), arena: make([]byte, 0, 1<<20)}
	s := g.Str
	b := d.scratch[:0]

	d.putAttrs(g)
	d.putCallsites(g)
	d.putEdges(g)
	d.putEnumMembers(g)
	d.putExceptions(g)
	d.putFields(g)

	for i := range g.Files {
		f := &g.Files[i]
		b = b[:0]
		b = append(b, 'R', ' ')
		b = encInt(b, int64(f.ID))
		for _, v := range [5]string{f.Path(s), f.Dir(s), f.Basename(s), f.Ext(s), f.Lang(s)} {
			b = append(b, ' ')
			b = encText(b, v)
		}
		for _, v := range [8]int32{f.ModuleID, f.Bytes, f.Lines, f.Sloc, f.Blank,
			f.Comment, f.DocLines, f.MaxLine} {
			b = append(b, ' ')
			b = encInt(b, int64(v))
		}
		b = append(b, ' ')
		b = encText(b, f.SHA1(s))
		for _, v := range [6]int32{f.Parsed, f.IsTest, f.IsGen, f.IsVend,
			f.NParsErr, f.NMissing} {
			b = append(b, ' ')
			b = encInt(b, int64(v))
		}
		b = append(b, ' ')
		b = encFloat(b, f.ParseMs)
		for _, v := range [7]int32{f.NSymbols, f.NFuncs, f.NTypes, f.NImports,
			f.TotalCyc, f.MaxCyc, f.TotalRisk} {
			b = append(b, ' ')
			b = encInt(b, int64(v))
		}
		d.row(b)
	}
	d.table("files", 29)

	d.putGenerics(g)
	d.putHazards(g)
	d.putImports(g)
	d.putJPMS(g)
	d.putLiterals(g)
	d.putLocals(g)
	d.putLocks(g)
	d.putMarkers(g)

	for i := range g.Meta {
		if runtimeMeta[s.get(g.Meta[i].K)] {
			continue
		}
		b = append(b[:0], 'R', ' ')
		b = encText(b, s.get(g.Meta[i].K))
		b = append(b, ' ')
		b = encText(b, s.get(g.Meta[i].V))
		d.row(b)
	}
	d.table("meta", 2)

	for i := range g.Mod {
		m := &g.Mod[i]
		b = b[:0]
		b = append(b, 'R', ' ')
		b = encInt(b, int64(m.ID))
		b = append(b, ' ')
		b = encText(b, s.get(m.Name))
		b = append(b, ' ')
		b = encText(b, s.get(m.Kind))
		for _, v := range [6]int32{m.NFiles, m.NSymbols, m.NPublic, m.Sloc, m.FanIn, m.FanOut} {
			b = append(b, ' ')
			b = encInt(b, int64(v))
		}
		b = append(b, ' ')
		b = encFloat(b, m.Instability)
		d.row(b)
	}
	d.table("modules", 10)

	d.putMonitorOps(g)
	d.putOverrides(g)
	d.putParams(g)
	d.putReach(g)
	d.putResources(g)
	d.putSecrets(g)

	nullRow := []byte("R \\N \\N \\N")
	for i := 0; i < len(g.Sym); i++ {
		d.row(nullRow)
	}
	d.table("sym_fts", 3)

	for i := range g.Sym {
		x := &g.Sym[i]
		b = b[:0]
		b = append(b, 'R')
		for i := range symNCols {
			b = append(b, ' ')
			b = encSymCol(b, g, x, i)
		}
		d.row(b)
	}
	d.table("symbols", symNCols)
	d.putTypeRel(g)
	d.putUnresolved(g)
	d.putInputSites(g)

	return d.w.Flush()
}

func (d *dumpBuf) line() []byte { return append(d.scratch[:0], 'R') }

func (d *dumpBuf) i(b []byte, v int32) []byte {
	b = append(b, ' ')
	return encInt(b, int64(v))
}

func (d *dumpBuf) ts(b []byte, s *Interner, v uint32) []byte {
	b = append(b, ' ')
	return encText(b, s.get(v))
}

func (d *dumpBuf) putParams(g *Graph) {
	s := g.Str
	for i := range g.Params {
		p := &g.Params[i]
		b := d.line()
		b = d.i(b, p.SymID)
		b = d.i(b, p.Pos)
		b = d.ts(b, s, p.Name)
		b = d.ts(b, s, p.Type)
		b = append(b, ' ')
		if p.HasDefault == 0 {
			b = encNull(b)
		} else {
			b = encText(b, s.get(p.Default))
		}
		for _, v := range [7]int32{p.IsOptional, p.IsVariadic, p.IsRef, p.IsMutable,
			p.IsNullable, p.IsGeneric, p.IsUntyped} {
			b = d.i(b, v)
		}
		b = d.i(b, p.TypeDepth)
		d.row(b)
	}
	d.table("params", 13)
}

func (d *dumpBuf) putFields(g *Graph) {
	s := g.Str
	for i := range g.Fields {
		f := &g.Fields[i]
		b := d.line()
		b = d.i(b, f.SymID)
		b = d.i(b, f.Ordinal)
		b = d.ts(b, s, f.Name)
		b = d.ts(b, s, f.Type)
		b = d.ts(b, s, f.Vis)
		b = d.i(b, f.Line)
		for _, v := range [8]int32{f.IsStatic, f.IsConst, f.IsMutable, f.IsNullable,
			f.IsColl, f.IsUntyped, f.HasDefault, f.TypeDepth} {
			b = d.i(b, v)
		}
		d.row(b)
	}
	d.table("fields", 14)
}

func (d *dumpBuf) putEnumMembers(g *Graph) {
	s := g.Str
	for i := range g.EnumMem {
		m := &g.EnumMem[i]
		b := d.line()
		b = d.i(b, m.SymID)
		b = d.i(b, m.Ordinal)
		b = d.ts(b, s, m.Name)
		b = append(b, ' ')
		if m.HasValue == 0 {
			b = encNull(b)
		} else {
			b = encText(b, s.get(m.Value))
		}
		b = d.i(b, m.NFlds)
		d.row(b)
	}
	d.table("enum_members", 5)
}

func (d *dumpBuf) putLocals(g *Graph) {
	s := g.Str
	for i := range g.Locals {
		l := &g.Locals[i]
		b := d.line()
		b = d.i(b, l.SymID)
		b = d.i(b, l.Ordinal)
		b = d.ts(b, s, l.Name)
		b = d.ts(b, s, l.Type)
		b = d.i(b, l.Line)
		for _, v := range [6]int32{l.IsConst, l.IsMutable, l.IsUntyped, l.HasInit,
			l.InLoop, l.ScopeDepth} {
			b = d.i(b, v)
		}
		d.row(b)
	}
	d.table("locals", 11)
}

func (d *dumpBuf) putEdges(g *Graph) {
	for i := range g.Edges {
		e := &g.Edges[i]
		b := d.line()
		b = d.i(b, e.Caller)
		b = d.i(b, e.Callee)
		b = d.i(b, e.NCalls)
		b = d.i(b, e.SameFile)
		b = d.i(b, e.SameMod)
		b = d.i(b, e.IsSelf)
		d.row(b)
	}
	d.table("edges", 6)
}

func (d *dumpBuf) putCallsites(g *Graph) {
	for i := range g.Callsite {
		c := &g.Callsite[i]
		b := d.line()
		b = d.i(b, c.Caller)
		b = d.i(b, c.Callee)
		b = d.i(b, c.Line)
		d.row(b)
	}
	d.table("callsites", 3)
}

func (d *dumpBuf) putUnresolved(g *Graph) {
	s := g.Str
	for i := range g.Unres {
		u := &g.Unres[i]
		b := d.line()
		b = d.i(b, u.Caller)
		b = d.ts(b, s, u.Name)
		b = d.i(b, u.N)
		b = d.i(b, u.Line)
		d.row(b)
	}
	d.table("unresolved_calls", 4)
}

func (d *dumpBuf) putImports(g *Graph) {
	s := g.Str
	for i := range g.Imports {
		m := &g.Imports[i]
		b := d.line()
		b = d.i(b, m.ID)
		b = d.i(b, m.FileID)
		b = d.ts(b, s, m.Target)
		b = append(b, ' ')
		if m.TargetID < 0 {
			b = encNull(b)
		} else {
			b = encInt(b, int64(m.TargetID))
		}
		b = append(b, ' ')
		if m.HasAlias == 0 {
			b = encNull(b)
		} else {
			b = encText(b, s.get(m.Alias))
		}
		b = d.ts(b, s, m.Kind)
		b = d.i(b, m.Line)
		for _, v := range [6]int32{m.IsExternal, m.IsRelative, m.IsWildcard,
			m.IsTypeOnly, m.IsDynamic, m.NNames} {
			b = d.i(b, v)
		}
		d.row(b)
	}
	d.table("imports", 13)
}

func (d *dumpBuf) putHazards(g *Graph) {
	s := g.Str
	for i := range g.Hazards {
		h := &g.Hazards[i]
		b := d.line()
		b = d.i(b, h.SymID)
		b = d.ts(b, s, h.Pat)
		b = d.ts(b, s, h.Cat)
		b = d.i(b, h.N)
		b = d.i(b, h.Line)
		d.row(b)
	}
	d.table("hazards", 5)
}

func (d *dumpBuf) putAttrs(g *Graph) {
	s := g.Str
	for i := range g.Attrs {
		a := &g.Attrs[i]
		b := d.line()
		b = d.i(b, a.ID)
		b = d.i(b, a.SymID)
		b = d.i(b, a.FileID)
		b = d.ts(b, s, a.Name)
		b = append(b, ' ')
		if a.HasArgs == 0 {
			b = encNull(b)
		} else {
			b = encText(b, s.get(a.Args))
		}
		b = d.i(b, a.Line)
		d.row(b)
	}
	d.table("attributes", 6)
}

func (d *dumpBuf) putLiterals(g *Graph) {
	s := g.Str
	for i := range g.Lits {
		l := &g.Lits[i]
		b := d.line()
		b = d.i(b, l.ID)
		b = d.i(b, l.SymID)
		b = d.i(b, l.FileID)
		b = d.ts(b, s, l.Kind)
		b = d.ts(b, s, l.Value)
		b = d.i(b, l.Line)
		b = d.i(b, l.IsMagic)
		d.row(b)
	}
	d.table("literals", 7)
}

func (d *dumpBuf) putMarkers(g *Graph) {
	s := g.Str
	for i := range g.Markers {
		m := &g.Markers[i]
		b := d.line()
		b = d.i(b, m.ID)
		b = d.i(b, m.FileID)
		b = append(b, ' ')
		if m.SymID < 0 {
			b = encNull(b)
		} else {
			b = encInt(b, int64(m.SymID))
		}
		b = d.ts(b, s, m.Kind)
		b = d.i(b, m.Line)
		b = d.ts(b, s, m.Text)
		d.row(b)
	}
	d.table("markers", 6)
}

func (d *dumpBuf) putTypeRel(g *Graph) {
	s := g.Str
	for i := range g.TypeRel {
		t := &g.TypeRel[i]
		b := d.line()
		b = d.i(b, t.ID)
		b = d.i(b, t.ChildID)
		b = d.i(b, t.FileID)
		b = d.ts(b, s, t.ChildName)
		b = d.ts(b, s, t.ChildKind)
		b = d.ts(b, s, t.ParentNam)
		b = d.ts(b, s, t.Kind)
		b = d.i(b, t.IsGeneric)
		b = d.i(b, t.Line)
		d.row(b)
	}
	d.table("type_relations", 9)
}

func (d *dumpBuf) putOverrides(g *Graph) {
	s := g.Str
	for i := range g.Over {
		o := &g.Over[i]
		b := d.line()
		b = d.i(b, o.ID)
		b = d.i(b, o.SymID)
		b = d.i(b, o.FileID)
		b = d.ts(b, s, o.MethodName)
		b = d.ts(b, s, o.OwnerType)
		b = d.ts(b, s, o.ParentType)
		b = d.i(b, o.IsAnnotated)
		b = d.i(b, o.IsFwEntry)
		b = d.i(b, o.NParams)
		b = d.i(b, o.Line)
		d.row(b)
	}
	d.table("overrides", 10)
}

func (d *dumpBuf) putExceptions(g *Graph) {
	s := g.Str
	for i := range g.Excepts {
		e := &g.Excepts[i]
		b := d.line()
		b = d.i(b, e.ID)
		b = d.i(b, e.SymID)
		b = d.i(b, e.FileID)
		b = d.ts(b, s, e.Kind)
		b = d.ts(b, s, e.Type)
		for _, v := range [6]int32{e.IsBroad, e.IsEmpty, e.Rethrows, e.Logs,
			e.InLoop, e.Restores} {
			b = d.i(b, v)
		}
		b = d.i(b, e.Line)
		d.row(b)
	}
	d.table("exceptions", 12)
}

func (d *dumpBuf) putMonitorOps(g *Graph) {
	s := g.Str
	for i := range g.MonOps {
		o := &g.MonOps[i]
		b := d.line()
		b = d.i(b, o.ID)
		b = d.i(b, o.SymID)
		b = d.i(b, o.FileID)
		b = d.ts(b, s, o.Monitor)
		b = d.ts(b, s, o.Op)
		b = d.i(b, o.InSync)
		b = d.i(b, o.Line)
		d.row(b)
	}
	d.table("monitor_ops", 7)
}

func (d *dumpBuf) putGenerics(g *Graph) {
	s := g.Str
	for i := range g.Gens {
		t := &g.Gens[i]
		b := d.line()
		b = d.i(b, t.ID)
		b = d.i(b, t.SymID)
		b = d.i(b, t.FileID)
		b = d.ts(b, s, t.Owner)
		b = d.ts(b, s, t.Name)
		b = d.ts(b, s, t.Bound)
		b = d.i(b, t.SelfRef)
		b = d.i(b, t.OnType)
		b = d.i(b, t.Line)
		d.row(b)
	}
	d.table("generics", 9)
}

func (d *dumpBuf) putResources(g *Graph) {
	s := g.Str
	for i := range g.Res {
		r := &g.Res[i]
		b := d.line()
		b = d.i(b, r.ID)
		b = d.i(b, r.SymID)
		b = d.i(b, r.FileID)
		b = d.ts(b, s, r.Name)
		b = d.ts(b, s, r.Type)
		b = d.ts(b, s, r.OpenedBy)
		b = d.i(b, r.InTryResources)
		b = d.i(b, r.ClosedInFn)
		b = d.i(b, r.InLoop)
		b = d.i(b, r.Line)
		d.row(b)
	}
	d.table("resources", 10)
}

func (d *dumpBuf) putLocks(g *Graph) {
	s := g.Str
	for i := range g.Locks {
		o := &g.Locks[i]
		b := d.line()
		b = d.i(b, o.ID)
		b = d.i(b, o.SymID)
		b = d.i(b, o.FileID)
		b = d.ts(b, s, o.LockName)
		b = d.ts(b, s, o.Op)
		b = d.ts(b, s, o.Kind)
		for _, v := range [7]int32{o.AcqOrder, o.InLoop, o.HoldsIO, o.HoldsSleep,
			o.HoldsAlloc, o.HoldsCall, o.RegionSloc} {
			b = d.i(b, v)
		}
		b = d.i(b, o.Line)
		d.row(b)
	}
	d.table("lock_ops", 14)
}

func (d *dumpBuf) putJPMS(g *Graph) {
	s := g.Str
	for i := range g.JPMS {
		j := &g.JPMS[i]
		b := d.line()
		b = d.i(b, j.ID)
		b = d.i(b, j.FileID)
		b = d.ts(b, s, j.Kind)
		b = d.ts(b, s, j.ModuleNam)
		b = d.ts(b, s, j.Target)
		b = d.i(b, j.Transitive)
		b = d.i(b, j.IsStatic)
		b = d.i(b, j.Line)
		d.row(b)
	}
	d.table("jpms_directives", 8)
}

func (d *dumpBuf) putInputSites(g *Graph) {
	s := g.Str
	for i := range g.UISites {
		u := &g.UISites[i]
		b := d.line()
		b = d.i(b, u.ID)
		b = d.i(b, u.SymID)
		b = d.i(b, u.FileID)
		b = d.ts(b, s, u.Var)
		b = d.ts(b, s, u.Kind)
		b = d.i(b, u.Line)
		b = d.i(b, u.InLoop)
		d.row(b)
	}
	d.table("user_input_sites", 7)
}

func (d *dumpBuf) putSecrets(g *Graph) {
	s := g.Str
	for i := range g.Secrets {
		v := &g.Secrets[i]
		b := d.line()
		b = d.i(b, v.ID)
		b = d.i(b, v.SymID)
		b = d.i(b, v.FileID)
		b = d.ts(b, s, v.Value)
		b = d.i(b, v.Line)
		d.row(b)
	}
	d.table("secret_candidates", 5)
}

func (d *dumpBuf) putReach(g *Graph) {
	for i := range g.Reach {
		r := &g.Reach[i]
		b := d.line()
		b = d.i(b, r.Root)
		b = d.i(b, r.Sym)
		b = d.i(b, r.Depth)
		d.row(b)
	}
	d.table("reach", 3)
}

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
	{name: "exceptions",
		note: "a throw, and the catch clauses that could take it",
		cols: []columnShape{
			{"id", "int", false},
			{"symbol_id", "int", false},
			{"file_id", "int", false},
			{"kind", "text", false},
			{"type", "text", false},
			{"is_broad", "int", false},
			{"is_empty", "int", false},
			{"rethrows", "int", false},
			{"logs", "int", false},
			{"in_loop", "int", false},
			{"restores", "int", false},
			{"line", "int", false},
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
	{name: "generics",
		note: "a generic type or method declaration, and its parameters",
		cols: []columnShape{
			{"id", "int", false},
			{"symbol_id", "int", false},
			{"file_id", "int", false},
			{"owner", "text", false},
			{"name", "text", false},
			{"bound", "text", false},
			{"is_self_referential", "int", false},
			{"on_type", "int", false},
			{"line", "int", false},
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
	{name: "jpms_directives",
		note: "module-info directives: requires, exports, opens, uses",
		cols: []columnShape{
			{"id", "int", false},
			{"file_id", "int", false},
			{"kind", "text", false},
			{"module_name", "text", false},
			{"target", "text", false},
			{"is_transitive", "int", false},
			{"is_static", "int", false},
			{"line", "int", false},
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
	{name: "lock_ops",
		note: "a locking operation: what was locked, and whether it is released",
		cols: []columnShape{
			{"id", "int", false},
			{"symbol_id", "int", false},
			{"file_id", "int", false},
			{"lock_name", "text", false},
			{"op", "text", false},
			{"kind", "text", false},
			{"acq_order", "int", false},
			{"in_loop", "int", false},
			{"holds_io", "int", false},
			{"holds_sleep", "int", false},
			{"holds_alloc", "int", false},
			{"holds_call", "int", false},
			{"region_sloc", "int", false},
			{"line", "int", false},
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
	{name: "monitor_ops",
		note: "a synchronized block, and what it guards",
		cols: []columnShape{
			{"id", "int", false},
			{"symbol_id", "int", false},
			{"file_id", "int", false},
			{"monitor", "text", false},
			{"op", "text", false},
			{"in_sync", "int", false},
			{"line", "int", false},
		}},
	{name: "overrides",
		note: "a method that overrides a supertype method",
		cols: []columnShape{
			{"id", "int", false},
			{"symbol_id", "int", false},
			{"file_id", "int", false},
			{"method_name", "text", false},
			{"owner_type", "text", false},
			{"parent_type", "text", false},
			{"is_annotated", "int", false},
			{"is_framework_entry", "int", false},
			{"n_params", "int", false},
			{"line", "int", false},
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
	{name: "reach",
		note: "a symbol reachable from an entry point, and at what depth",
		cols: []columnShape{
			{"root", "int", false},
			{"sym", "int", false},
			{"min_depth", "int", false},
		}},
	{name: "resources",
		note: "a resource opened: what, where, and how it is closed",
		cols: []columnShape{
			{"id", "int", false},
			{"symbol_id", "int", false},
			{"file_id", "int", false},
			{"name", "text", false},
			{"type", "text", false},
			{"opened_by", "text", false},
			{"in_try_resources", "int", false},
			{"closed_in_fn", "int", false},
			{"in_loop", "int", false},
			{"line", "int", false},
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
	{name: "symbols",
		note: "the hub: every function, method, closure, hook and type",
		cols: []columnShape{
			{"id", "int", false},
			{"file_id", "int", false},
			{"module_id", "int", true},
			{"parent_id", "int", true},
			{"name", "text", false},
			{"qual_name", "text", false},
			{"kind", "text", false},
			{"line_start", "int", false},
			{"line_end", "int", false},
			{"n_lines", "int", false},
			{"byte_start", "int", false},
			{"byte_end", "int", false},
			{"signature", "text", true},
			{"return_type", "text", true},
			{"visibility", "text", false},
			{"n_params", "int", false},
			{"n_optional_params", "int", false},
			{"n_generic_params", "int", false},
			{"n_overloads", "int", false},
			{"arity_rank", "int", false},
			{"is_public", "int", false},
			{"is_static", "int", false},
			{"is_async", "int", false},
			{"is_generator", "int", false},
			{"is_abstract", "int", false},
			{"is_override", "int", false},
			{"is_exported", "int", false},
			{"is_test", "int", false},
			{"is_deprecated", "int", false},
			{"is_entrypoint", "int", false},
			{"is_generated", "int", false},
			{"sloc", "int", false},
			{"body_bytes", "int", false},
			{"n_comment_lines", "int", false},
			{"n_doc_lines", "int", false},
			{"has_doc", "int", false},
			{"cyclomatic", "int", false},
			{"cognitive", "int", false},
			{"max_nesting", "int", false},
			{"n_tokens", "int", false},
			{"n_operators", "int", false},
			{"n_operands", "int", false},
			{"n_distinct_operators", "int", false},
			{"n_distinct_operands", "int", false},
			{"halstead_volume", "int", false},
			{"maintainability", "int", false},
			{"n_loops", "int", false},
			{"n_branches", "int", false},
			{"n_returns", "int", false},
			{"n_early_returns", "int", false},
			{"n_switch", "int", false},
			{"n_cases", "int", false},
			{"n_ternary", "int", false},
			{"n_logical", "int", false},
			{"n_try", "int", false},
			{"n_catch", "int", false},
			{"n_catch_broad", "int", false},
			{"n_catch_empty", "int", false},
			{"n_finally", "int", false},
			{"n_throw", "int", false},
			{"n_labels", "int", false},
			{"n_gotos", "int", false},
			{"max_loop_depth", "int", false},
			{"call_in_loop", "int", false},
			{"alloc_in_loop", "int", false},
			{"io_in_loop", "int", false},
			{"await_in_loop", "int", false},
			{"lock_in_loop", "int", false},
			{"concat_in_loop", "int", false},
			{"regex_in_loop", "int", false},
			{"query_in_loop", "int", false},
			{"branch_in_loop", "int", false},
			{"n_locals", "int", false},
			{"n_assign", "int", false},
			{"n_compound_assign", "int", false},
			{"n_incdec", "int", false},
			{"n_cmp", "int", false},
			{"n_bitop", "int", false},
			{"n_shift", "int", false},
			{"n_arith", "int", false},
			{"n_string_lit", "int", false},
			{"n_regex_lit", "int", false},
			{"n_float_lit", "int", false},
			{"n_magic", "int", false},
			{"n_null_check", "int", false},
			{"n_subscript", "int", false},
			{"n_member_access", "int", false},
			{"n_lambda", "int", false},
			{"n_closure_capture", "int", false},
			{"n_calls", "int", false},
			{"n_unique_calls", "int", false},
			{"n_dynamic_calls", "int", false},
			{"n_unresolved_calls", "int", false},
			{"fan_in", "int", false},
			{"fan_out", "int", false},
			{"n_callsites", "int", false},
			{"is_recursive", "int", false},
			{"is_leaf", "int", false},
			{"is_root", "int", false},
			{"n_hazards", "int", false},
			{"risk_score", "int", false},
			{"n_reflection", "int", false},
			{"n_serialization", "int", false},
			{"n_jni", "int", false},
			{"n_exec", "int", false},
			{"n_io", "int", false},
			{"n_net", "int", false},
			{"n_sql", "int", false},
			{"n_crypto", "int", false},
			{"n_concurrency", "int", false},
			{"n_lock", "int", false},
			{"n_alloc", "int", false},
			{"n_boxing", "int", false},
			{"n_string", "int", false},
			{"n_resource", "int", false},
			{"n_unsafe", "int", false},
			{"n_control", "int", false},
			{"n_text_blocks", "int", false},
			{"n_lambdas", "int", false},
			{"n_method_refs", "int", false},
			{"n_streams", "int", false},
			{"n_parallel_streams", "int", false},
			{"n_collectors", "int", false},
			{"n_boxing_sites", "int", false},
			{"n_boxing_in_loop", "int", false},
			{"n_string_concat", "int", false},
			{"n_synchronized_blocks", "int", false},
			{"n_synchronized_methods", "int", false},
			{"n_lock_acquire", "int", false},
			{"n_lock_release", "int", false},
			{"n_wait_calls", "int", false},
			{"n_volatile_access", "int", false},
			{"n_atomic_ops", "int", false},
			{"n_threadlocal_ops", "int", false},
			{"n_threadlocal_remove", "int", false},
			{"n_try_resources", "int", false},
			{"n_close_calls", "int", false},
			{"n_resource_open", "int", false},
			{"n_finalizers", "int", false},
			{"n_throws_declared", "int", false},
			{"n_throw_sites", "int", false},
			{"n_catch_rethrow", "int", false},
			{"n_setaccessible", "int", false},
			{"n_native_calls", "int", false},
			{"n_ffm_arena", "int", false},
			{"n_ffm_downcall", "int", false},
			{"n_unsafe_calls", "int", false},
			{"n_wildcard_types", "int", false},
			{"n_raw_types", "int", false},
			{"n_unchecked_casts", "int", false},
			{"n_instanceof", "int", false},
			{"n_null_returns", "int", false},
			{"n_optional_ops", "int", false},
			{"n_annotations", "int", false},
			{"n_suppressions", "int", false},
			{"n_static_writes", "int", false},
			{"n_query_calls", "int", false},
			{"n_regex_compile", "int", false},
			{"n_datefmt_ops", "int", false},
			{"n_escaping_allocs", "int", false},
			{"n_alloc_sites", "int", false},
			{"n_impl_targets", "int", false},
			{"is_virtual_thread_root", "int", false},
			{"is_executor_root", "int", false},
			{"is_pooled_executor_root", "int", false},
			{"is_handler", "int", false},
			{"is_serializable", "int", false},
			{"has_serial_uid", "int", false},
			{"owner_type", "text", false},
			{"n_runtime_exec", "int", false},
			{"n_print_stacktrace", "int", false},
			{"n_default_charset", "int", false},
			{"n_parse_no_radix", "int", false},
			{"n_equals_in_loop", "int", false},
			{"n_weak_random", "int", false},
			{"n_redirect", "int", false},
			{"n_auth_call", "int", false},
			{"n_xxe_parser", "int", false},
			{"n_zip_read", "int", false},
			{"n_timeout_set", "int", false},
			{"n_executor_create", "int", false},
			{"n_submit_in_loop", "int", false},
			{"n_future_get", "int", false},
			{"n_monitor_call", "int", false},
			{"n_string_intern", "int", false},
			{"n_raw_statement", "int", false},
			{"n_read_object", "int", false},
			{"n_load_library", "int", false},
			{"n_elif", "int", false},
			{"n_external_calls", "int", false},
			{"n_ref_eq", "int", false},
			{"n_narrow_calc", "int", false},
			{"n_dead_exception", "int", false},
			{"n_super_calls", "int", false},
			{"n_static_write_ctor", "int", false},
			{"n_modern_idioms", "int", false},
			{"is_flex_constructor", "int", false},
			{"n_resilience_annos", "int", false},
			{"n_api_version_attr", "int", false},
			{"is_http_exchange_client", "int", false},
			{"n_ee12_annos", "int", false},
			{"n_jspecify_annos", "int", false},
			{"n_notify_single", "int", false},
			{"n_run_called_directly", "int", false},
			{"n_compareto_negate", "int", false},
			{"n_bigDecimal_from_double", "int", false},
			{"n_compareto_specific", "int", false},
			{"n_volatile_compound", "int", false},
			{"n_shared_datefmt_use", "int", false},
			{"n_listener_add", "int", false},
			{"n_listener_remove", "int", false},
			{"n_thread_alloc", "int", false},
			{"n_spel_eval", "int", false},
			{"n_format_in_loop", "int", false},
			{"n_static_coll_add", "int", false},
			{"n_static_coll_remove", "int", false},
		}},
	{name: "type_relations",
		note: "a type a symbol refers to: extends, implements, throws",
		cols: []columnShape{
			{"id", "int", false},
			{"child_id", "int", false},
			{"file_id", "int", false},
			{"child_name", "text", false},
			{"child_kind", "text", false},
			{"parent_name", "text", false},
			{"kind", "text", false},
			{"is_generic", "int", false},
			{"line", "int", false},
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

type Sym struct {
	ID        int32
	FileID    int32
	ModuleID  int32
	ParentID  int32
	Name      uint32
	QualName  uint32
	Kind      uint32
	LineStart int32
	LineEnd   int32
	NLines    int32
	ByteStart int32
	ByteEnd   int32
	Signature uint32
	RetType   uint32
	Vis       uint32

	NParams         int32
	NOptionalParams int32
	NGenericParams  int32
	NOverloads      int32
	ArityRank       int32

	flags uint32

	Sloc       int32
	BodyBytes  int32
	NCommentLn int32
	NDocLines  int32
	HasDoc     int32

	Cyclomatic       int32
	Cognitive        int32
	MaxNesting       int32
	NTokens          int32
	NOperators       int32
	NOperands        int32
	NDistinctOps     int32
	NDistinctOperand int32
	HalsteadVolume   int32
	Maintainability  int32

	NLoops        int32
	NBranches     int32
	NReturns      int32
	NEarlyReturns int32
	NSwitch       int32
	NCases        int32
	NTernary      int32
	NLogical      int32
	NTry          int32
	NCatch        int32
	NCatchBroad   int32
	NCatchEmpty   int32
	NFinally      int32
	NThrow        int32
	NLabels       int32
	NGotos        int32

	MaxLoopDepth int32
	CallInLoop   int32
	AllocInLoop  int32
	IOInLoop     int32
	LockInLoop   int32
	ConcatInLoop int32
	RegexInLoop  int32
	QueryInLoop  int32
	BranchInLoop int32

	NLocals        int32
	NAssign        int32
	NCompoundAssgn int32
	NIncDec        int32
	NCmp           int32
	NBitop         int32
	NShift         int32
	NArith         int32
	NStringLit     int32
	NRegexLit      int32
	NFloatLit      int32
	NMagic         int32
	NNullCheck     int32
	NSubscript     int32
	NMemberAccess  int32
	NLambda        int32

	NCalls       int32
	NUniqueCalls int32
	NUnresolved  int32
	FanIn        int32
	FanOut       int32
	NCallsites   int32

	NHazards  int32
	RiskScore int32

	NReflection    int32
	NSerialization int32
	NJNI           int32
	NExec          int32
	NIO            int32
	NNet           int32
	NSql           int32
	NCrypto        int32
	NConcurrency   int32
	NLock          int32
	NAlloc         int32
	NBoxing        int32
	NString        int32
	NResource      int32
	NUnsafe        int32
	NControl       int32

	NTextBlocks           int32
	NLambdas              int32
	NMethodRefs           int32
	NStreams              int32
	NParallelStreams      int32
	NCollectors           int32
	NBoxingSites          int32
	NBoxingInLoop         int32
	NStringConcat         int32
	NSyncBlocks           int32
	NSyncMethods          int32
	NLockAcquire          int32
	NLockRelease          int32
	NWaitCalls            int32
	NVolatileAccess       int32
	NAtomicOps            int32
	NThreadlocalOps       int32
	NThreadlocalRem       int32
	NTryResources         int32
	NCloseCalls           int32
	NResourceOpen         int32
	NFinalizers           int32
	NThrowsDeclared       int32
	NThrowSites           int32
	NCatchRethrow         int32
	NSetAccessible        int32
	NNativeCalls          int32
	NFFMArena             int32
	NFFMDowncall          int32
	NUnsafeCalls          int32
	NWildcardTypes        int32
	NRawTypes             int32
	NUncheckedCasts       int32
	NInstanceof           int32
	NNullReturns          int32
	NOptionalOps          int32
	NAnnotations          int32
	NSuppressions         int32
	NStaticWrites         int32
	NQueryCalls           int32
	NRegexCompile         int32
	NDatefmtOps           int32
	NEscapingAllocs       int32
	NAllocSites           int32
	NImplTargets          int32
	OwnerType             uint32
	NRuntimeExec          int32
	NPrintStacktrace      int32
	NDefaultCharset       int32
	NParseNoRadix         int32
	NEqualsInLoop         int32
	NWeakRandom           int32
	NRedirect             int32
	NAuthCall             int32
	NXXEParser            int32
	NZipRead              int32
	NTimeoutSet           int32
	NExecutorCreate       int32
	NSubmitInLoop         int32
	NFutureGet            int32
	NMonitorCall          int32
	NStringIntern         int32
	NRawStatement         int32
	NReadObject           int32
	NLoadLibrary          int32
	NElif                 int32
	NExternalCalls        int32
	NRefEq                int32
	NNarrowCalc           int32
	NDeadException        int32
	NSuperCalls           int32
	NStaticWriteCtor      int32
	NModernIdioms         int32
	NResilienceAnnos      int32
	NApiVersionAttr       int32
	NEe12Annos            int32
	NJSpecifyAnnos        int32
	NNotifySingle         int32
	NRunCalledDirectly    int32
	NBigDecimalFromDouble int32
	NVolatileCompound     int32
	NSharedDatefmtUse     int32
	NListenerAdd          int32
	NListenerRemove       int32
	NThreadAlloc          int32
	NSpelEval             int32
	NFormatInLoop         int32
	NStaticCollAdd        int32
	NStaticCollRemove     int32
}

const (
	fPublic = 1 << iota
	fStatic
	fAbstract
	fOverride
	fTest
	fDeprecated
	fEntrypoint
	fHandler
	fLeaf
	fRoot
	fRecursive
	fVtRoot
	fExecRoot
	fPoolRoot
	fSerializable
	fHasSerialUID
	fHTTPExchange
	fFlexCtor
)

func (s *Sym) getFlag(f uint32) int32 {
	if s.flags&f != 0 {
		return 1
	}
	return 0
}

func (s *Sym) setFlag(f uint32, v int32) {
	if v != 0 {
		s.flags |= f
	} else {
		s.flags &^= f
	}
}

const (
	kindFunction = iota
	kindMethod
	kindConstructor
	kindClosure
	kindClass
	kindInterface
	kindEnum
	kindRecord
	kindType
	kindModule
)

var kindNames = [...]string{
	"function", "method", "constructor", "closure", "class", "interface",
	"enum", "record", "type", "module",
}

func (g *Graph) kindOf(s *Sym) string { return kindNames[s.Kind] }

func isFnKind(k uint32) bool {
	return k == kindFunction || k == kindMethod || k == kindConstructor ||
		k == kindClosure
}

func isTypeKind(k uint32) bool {
	switch k {
	case kindClass, kindInterface, kindEnum, kindRecord, kindType:
		return true
	}
	return false
}

func countsAsType(k uint32) bool {
	switch k {
	case kindClass, kindInterface, kindEnum, kindRecord, kindType:
		return true
	}
	return false
}

type Module struct {
	ID          int32
	Name        uint32
	Kind        uint32
	NFiles      int32
	NSymbols    int32
	NPublic     int32
	Sloc        int32
	FanIn       int32
	FanOut      int32
	Instability float64
}

type File struct {
	ID        int32
	full      uint32
	path      uint32
	dir       uint32
	basename  uint32
	ext       uint32
	lang      uint32
	ModuleID  int32
	Bytes     int32
	Lines     int32
	Sloc      int32
	Blank     int32
	Comment   int32
	DocLines  int32
	MaxLine   int32
	sha1      uint32
	Parsed    int32
	IsTest    int32
	IsGen     int32
	IsVend    int32
	NParsErr  int32
	NMissing  int32
	ParseMs   float64
	NSymbols  int32
	NFuncs    int32
	NTypes    int32
	NImports  int32
	TotalCyc  int32
	MaxCyc    int32
	TotalRisk int32
}

func (f File) Full(it *Interner) string     { return it.get(f.full) }
func (f File) Path(it *Interner) string     { return it.get(f.path) }
func (f File) Dir(it *Interner) string      { return it.get(f.dir) }
func (f File) Basename(it *Interner) string { return it.get(f.basename) }
func (f File) Ext(it *Interner) string      { return it.get(f.ext) }
func (f File) Lang(it *Interner) string     { return it.get(f.lang) }
func (f File) SHA1(it *Interner) string     { return it.get(f.sha1) }

type Param struct {
	SymID      int32
	Pos        int32
	Name       uint32
	Type       uint32
	HasDefault int32
	Default    uint32
	IsOptional int32
	IsVariadic int32
	IsRef      int32
	IsMutable  int32
	IsNullable int32
	IsGeneric  int32
	IsUntyped  int32
	TypeDepth  int32
}

type Field struct {
	SymID      int32
	Ordinal    int32
	Name       uint32
	Type       uint32
	Vis        uint32
	Line       int32
	IsStatic   int32
	IsConst    int32
	IsMutable  int32
	IsNullable int32
	IsColl     int32
	IsUntyped  int32
	HasDefault int32
	TypeDepth  int32
}

type Local struct {
	SymID      int32
	Ordinal    int32
	Name       uint32
	Type       uint32
	Line       int32
	IsConst    int32
	IsMutable  int32
	IsUntyped  int32
	HasInit    int32
	InLoop     int32
	ScopeDepth int32
}

type EnumMember struct {
	SymID    int32
	Ordinal  int32
	Name     uint32
	Value    uint32
	HasValue int32
	NFlds    int32
}

type Edge struct {
	Caller   int32
	Callee   int32
	NCalls   int32
	SameFile int32
	SameMod  int32
	IsSelf   int32
}

type Callsite struct{ Caller, Callee, Line int32 }

type Unres struct {
	Caller int32
	Name   uint32
	N      int32
	Line   int32
}

type Import struct {
	ID         int32
	FileID     int32
	Target     uint32
	TargetID   int32
	HasAlias   int32
	Alias      uint32
	Kind       uint32
	Line       int32
	IsExternal int32
	IsRelative int32
	IsWildcard int32
	IsTypeOnly int32
	IsDynamic  int32
	NNames     int32
}

type Hazard struct {
	SymID int32
	Pat   uint32
	Cat   uint32
	N     int32
	Line  int32
}

type Attr struct {
	ID      int32
	SymID   int32
	FileID  int32
	Name    uint32
	Args    uint32
	HasArgs int32
	Line    int32
}

type Literal struct {
	ID      int32
	SymID   int32
	FileID  int32
	Kind    uint32
	Value   uint32
	Line    int32
	IsMagic int32
}

type Marker struct {
	ID     int32
	FileID int32
	SymID  int32
	Kind   uint32
	Line   int32
	Text   uint32
}

type TypeRel struct {
	ID        int32
	ChildID   int32
	FileID    int32
	ChildName uint32
	ChildKind uint32
	ParentNam uint32
	Kind      uint32
	IsGeneric int32
	Line      int32
}

type Override struct {
	ID          int32
	SymID       int32
	FileID      int32
	MethodName  uint32
	OwnerType   uint32
	ParentType  uint32
	IsAnnotated int32
	IsFwEntry   int32
	NParams     int32
	Line        int32
}

type Exception struct {
	ID       int32
	SymID    int32
	FileID   int32
	Kind     uint32
	Type     uint32
	IsBroad  int32
	IsEmpty  int32
	Rethrows int32
	Logs     int32
	InLoop   int32
	Restores int32
	Line     int32
}

type MonitorOp struct {
	ID      int32
	SymID   int32
	FileID  int32
	Monitor uint32
	Op      uint32
	InSync  int32
	Line    int32
}

type Generic struct {
	ID      int32
	SymID   int32
	FileID  int32
	Owner   uint32
	Name    uint32
	Bound   uint32
	SelfRef int32
	OnType  int32
	Line    int32
}

type Resource struct {
	ID             int32
	SymID          int32
	FileID         int32
	Name           uint32
	Type           uint32
	OpenedBy       uint32
	InTryResources int32
	ClosedInFn     int32
	InLoop         int32
	Line           int32
}

type LockOp struct {
	ID         int32
	SymID      int32
	FileID     int32
	LockName   uint32
	Op         uint32
	Kind       uint32
	AcqOrder   int32
	InLoop     int32
	HoldsIO    int32
	HoldsSleep int32
	HoldsAlloc int32
	HoldsCall  int32
	RegionSloc int32
	Line       int32
}

type JPMS struct {
	ID         int32
	FileID     int32
	Kind       uint32
	ModuleNam  uint32
	Target     uint32
	Transitive int32
	IsStatic   int32
	Line       int32
}

type InputSite struct {
	ID     int32
	SymID  int32
	FileID int32
	Var    uint32
	Kind   uint32
	Line   int32
	InLoop int32
}

type Secret struct {
	ID     int32
	SymID  int32
	FileID int32
	Value  uint32
	Line   int32
}

type Reach struct {
	Root  int32
	Sym   int32
	Depth int32
}

type MetaKV struct{ K, V uint32 }

type CSR[T any] struct {
	Off []int32
	Idx []int32
	Val []T
}

func BuildCSR[T any](nkeys int, keys []int32, vals []T) CSR[T] {
	c := CSR[T]{Off: make([]int32, nkeys+1)}
	for _, k := range keys {
		c.Off[k+1]++
	}
	for i := range nkeys {
		c.Off[i+1] += c.Off[i]
	}
	c.Idx = make([]int32, len(keys))
	c.Val = make([]T, len(vals))
	fill := make([]int32, nkeys)
	copy(fill, c.Off[:nkeys])
	for i, k := range keys {
		at := fill[k]
		fill[k]++
		c.Idx[at] = int32(i)
		c.Val[at] = vals[i]
	}
	return c
}

func (c CSR[T]) lo(k int32) int32 { return c.Off[k] }
func (c CSR[T]) hi(k int32) int32 { return c.Off[k+1] }

type Graph struct {
	Str *Interner

	Mod   []Module
	Files []File
	Sym   []Sym

	Params   []Param
	Fields   []Field
	Locals   []Local
	EnumMem  []EnumMember
	Edges    []Edge
	Callsite []Callsite
	Unres    []Unres
	Imports  []Import
	Hazards  []Hazard
	Attrs    []Attr
	Lits     []Literal
	Markers  []Marker
	TypeRel  []TypeRel
	Over     []Override
	Excepts  []Exception
	MonOps   []MonitorOp
	Gens     []Generic
	Res      []Resource
	Locks    []LockOp
	JPMS     []JPMS
	UISites  []InputSite
	Secrets  []Secret
	Reach    []Reach
	Meta     []MetaKV

	Out CSR[Edge]
	In  CSR[Edge]

	byQual    map[string]int32
	fileScope map[scopeKey]int32
	typeScope map[scopeKey]int32
	unique    map[string]int32
	symLoc    []fileMod
	fileIdx   map[string]int32
	modIdx    map[string]int32

	nameOrder []int32

	PkgRoots    []uint32
	pkgRootSet  map[string]bool
	pkgRootLens []int

	FileImports map[int32]map[string]uint32

	symAdds []symAdd

	astTrees []*tsTree
	astBlob  []byte
}

type scopeKey struct {
	a uint32
	b uint32
}

type fileMod struct{ fid, mid int32 }

func NewGraph() *Graph {
	return &Graph{
		Str:         NewInterner(),
		byQual:      make(map[string]int32, 1<<14),
		fileScope:   make(map[scopeKey]int32, 1<<14),
		typeScope:   make(map[scopeKey]int32, 1<<14),
		unique:      make(map[string]int32, 1<<12),
		fileIdx:     make(map[string]int32, 1<<10),
		modIdx:      make(map[string]int32, 1<<6),
		pkgRootSet:  make(map[string]bool, 1<<6),
		FileImports: make(map[int32]map[string]uint32, 1<<10),
	}
}

func (g *Graph) addMeta(k, v string) {
	ki := g.Str.intern(k)
	for i := range g.Meta {
		if g.Meta[i].K == ki {
			g.Meta[i].V = g.Str.intern(v)
			return
		}
	}
	g.Meta = append(g.Meta, MetaKV{ki, g.Str.intern(v)})
}

func (g *Graph) meta(k string) string {
	for i := range g.Meta {
		if g.Str.get(g.Meta[i].K) == k {
			return g.Str.get(g.Meta[i].V)
		}
	}
	return ""
}

func (g *Graph) buildCallGraph() {

	n := len(g.Sym) + 1
	keys := make([]int32, len(g.Edges))
	vals := make([]Edge, len(g.Edges))
	for i, e := range g.Edges {
		keys[i], vals[i] = e.Caller, e
	}
	g.Out = BuildCSR(n, keys, vals)
	keys = keys[:0]
	vals = vals[:0]
	for _, e := range g.Edges {
		keys = append(keys, e.Callee)
		vals = append(vals, e)
	}
	g.In = BuildCSR(n, keys, vals)
}

func (g *Graph) outOfTree(target string) bool {
	if jdkPackageRoots[firstSegment(target)] {
		return true
	}
	if g.pkgRootLens == nil {
		seen := make(map[int]bool, 4)
		for _, p := range g.PkgRoots {
			seen[len(g.Str.get(p))] = true
		}
		g.pkgRootLens = make([]int, 0, len(seen))
		for n := range seen {
			g.pkgRootLens = append(g.pkgRootLens, n)
		}
		sort.Ints(g.pkgRootLens)
	}
	for _, n := range g.pkgRootLens {
		if n <= len(target) && g.pkgRootSet[target[:n]] {
			return false
		}
	}
	return true
}

func (g *Graph) buildIndexes() {
	n := len(g.Sym)
	// unique is a name -> id map for names with exactly one definition.  A
	// second definition overwrites the entry with the 0 sentinel, which is
	// what resolve() treats as "not unique" (it only assigns a non-zero
	// target), so no separate candidate slices are needed.
	for i := range g.Sym {
		name := g.Str.get(g.Sym[i].Name)
		if _, seen := g.unique[name]; seen {
			g.unique[name] = 0
		} else {
			g.unique[name] = int32(i + 1)
		}
	}

	g.symLoc = make([]fileMod, n+1)
	typeScopes := make(map[scopeKey]int32, n)
	for i := range g.Sym {
		s := &g.Sym[i]
		g.symLoc[s.ID] = fileMod{s.FileID, s.ModuleID}
		fsKey := scopeKey{s.Name, uint32(s.FileID)}
		if _, seen := g.fileScope[fsKey]; !seen {
			g.fileScope[fsKey] = s.ID
		}
		if owner := g.Str.get(s.OwnerType); owner != "" {
			oid := g.Str.intern(owner)
			tsKey := scopeKey{s.Name, oid}
			if _, seen := typeScopes[tsKey]; !seen {
				typeScopes[tsKey] = s.ID
			}
		}
	}
	g.typeScope = typeScopes

	for i := range g.Sym {
		s := &g.Sym[i]
		qual := g.Str.get(s.QualName)
		if isFnKind(s.Kind) {
			g.byQual[qual] = s.ID
			g.byQual[g.Files[s.FileID-1].Path(g.Str)+":"+qual] = s.ID
		} else if isTypeKind(s.Kind) {
			g.byQual[qual] = s.ID
		}
		if s.Kind == kindConstructor {
			key := "new " + g.Str.get(s.Name)
			if _, ok := g.byQual[key]; !ok {
				g.byQual[key] = s.ID
			}
		}
	}
	for i := range g.Files {
		g.fileIdx[g.Files[i].Path(g.Str)] = g.Files[i].ID
	}
	for i := range g.Mod {
		g.modIdx[g.Str.get(g.Mod[i].Name)] = g.Mod[i].ID
	}

	g.nameOrder = make([]int32, n)
	for i := range g.nameOrder {
		g.nameOrder[i] = int32(i + 1)
	}
	sort.Slice(g.nameOrder, func(a, b int) bool {
		ia, ib := g.nameOrder[a], g.nameOrder[b]
		na, nb := g.Str.get(g.Sym[ia-1].Name), g.Str.get(g.Sym[ib-1].Name)
		if na != nb {
			return na < nb
		}
		return ia < ib
	})
}

func (g *Graph) nameRange(n string) (int32, int32) {
	lo := sort.Search(len(g.nameOrder), func(i int) bool {
		return g.Str.get(g.Sym[g.nameOrder[i]-1].Name) >= n
	})
	hi := lo
	for hi < len(g.nameOrder) && g.Str.get(g.Sym[g.nameOrder[hi]-1].Name) == n {
		hi++
	}
	return int32(lo), int32(hi)
}

const symNCols = 216

func encSymCol(b []byte, g *Graph, s *Sym, i int) []byte {
	switch i {
	case 0:
		return encInt(b, int64(s.ID))
	case 1:
		return encInt(b, int64(s.FileID))
	case 2:
		return encInt(b, int64(s.ModuleID))
	case 3:
		if s.ParentID < 0 {
			return encNull(b)
		}
		return encInt(b, int64(s.ParentID))
	case 4:
		return encText(b, g.Str.get(s.Name))
	case 5:
		return encText(b, g.Str.get(s.QualName))
	case 6:
		return encText(b, kindNames[s.Kind])
	case 7:
		return encInt(b, int64(s.LineStart))
	case 8:
		return encInt(b, int64(s.LineEnd))
	case 9:
		return encInt(b, int64(s.NLines))
	case 10:
		return encInt(b, int64(s.ByteStart))
	case 11:
		return encInt(b, int64(s.ByteEnd))
	case 12:
		return encText(b, g.Str.get(s.Signature))
	case 13:
		return encText(b, g.Str.get(s.RetType))
	case 14:
		return encText(b, g.Str.get(s.Vis))
	case 15:
		return encInt(b, int64(s.NParams))
	case 16:
		return encInt(b, int64(s.NOptionalParams))
	case 17:
		return encInt(b, int64(s.NGenericParams))
	case 18:
		return encInt(b, int64(s.NOverloads))
	case 19:
		return encInt(b, int64(s.ArityRank))
	case 20:
		return encInt(b, int64(s.getFlag(fPublic)))
	case 21:
		return encInt(b, int64(s.getFlag(fStatic)))
	case 22:
		return encInt(b, 0)
	case 23:
		return encInt(b, 0)
	case 24:
		return encInt(b, int64(s.getFlag(fAbstract)))
	case 25:
		return encInt(b, int64(s.getFlag(fOverride)))
	case 26:
		return encInt(b, 0)
	case 27:
		return encInt(b, int64(s.getFlag(fTest)))
	case 28:
		return encInt(b, int64(s.getFlag(fDeprecated)))
	case 29:
		return encInt(b, int64(s.getFlag(fEntrypoint)))
	case 30:
		return encInt(b, 0)
	case 31:
		return encInt(b, int64(s.Sloc))
	case 32:
		return encInt(b, int64(s.BodyBytes))
	case 33:
		return encInt(b, int64(s.NCommentLn))
	case 34:
		return encInt(b, int64(s.NDocLines))
	case 35:
		return encInt(b, int64(s.HasDoc))
	case 36:
		return encInt(b, int64(s.Cyclomatic))
	case 37:
		return encInt(b, int64(s.Cognitive))
	case 38:
		return encInt(b, int64(s.MaxNesting))
	case 39:
		return encInt(b, int64(s.NTokens))
	case 40:
		return encInt(b, int64(s.NOperators))
	case 41:
		return encInt(b, int64(s.NOperands))
	case 42:
		return encInt(b, int64(s.NDistinctOps))
	case 43:
		return encInt(b, int64(s.NDistinctOperand))
	case 44:
		return encInt(b, int64(s.HalsteadVolume))
	case 45:
		return encInt(b, int64(s.Maintainability))
	case 46:
		return encInt(b, int64(s.NLoops))
	case 47:
		return encInt(b, int64(s.NBranches))
	case 48:
		return encInt(b, int64(s.NReturns))
	case 49:
		return encInt(b, int64(s.NEarlyReturns))
	case 50:
		return encInt(b, int64(s.NSwitch))
	case 51:
		return encInt(b, int64(s.NCases))
	case 52:
		return encInt(b, int64(s.NTernary))
	case 53:
		return encInt(b, int64(s.NLogical))
	case 54:
		return encInt(b, int64(s.NTry))
	case 55:
		return encInt(b, int64(s.NCatch))
	case 56:
		return encInt(b, int64(s.NCatchBroad))
	case 57:
		return encInt(b, int64(s.NCatchEmpty))
	case 58:
		return encInt(b, int64(s.NFinally))
	case 59:
		return encInt(b, int64(s.NThrow))
	case 60:
		return encInt(b, int64(s.NLabels))
	case 61:
		return encInt(b, int64(s.NGotos))
	case 62:
		return encInt(b, int64(s.MaxLoopDepth))
	case 63:
		return encInt(b, int64(s.CallInLoop))
	case 64:
		return encInt(b, int64(s.AllocInLoop))
	case 65:
		return encInt(b, int64(s.IOInLoop))
	case 66:
		return encInt(b, 0)
	case 67:
		return encInt(b, int64(s.LockInLoop))
	case 68:
		return encInt(b, int64(s.ConcatInLoop))
	case 69:
		return encInt(b, int64(s.RegexInLoop))
	case 70:
		return encInt(b, int64(s.QueryInLoop))
	case 71:
		return encInt(b, int64(s.BranchInLoop))
	case 72:
		return encInt(b, int64(s.NLocals))
	case 73:
		return encInt(b, int64(s.NAssign))
	case 74:
		return encInt(b, int64(s.NCompoundAssgn))
	case 75:
		return encInt(b, int64(s.NIncDec))
	case 76:
		return encInt(b, int64(s.NCmp))
	case 77:
		return encInt(b, int64(s.NBitop))
	case 78:
		return encInt(b, int64(s.NShift))
	case 79:
		return encInt(b, int64(s.NArith))
	case 80:
		return encInt(b, int64(s.NStringLit))
	case 81:
		return encInt(b, int64(s.NRegexLit))
	case 82:
		return encInt(b, int64(s.NFloatLit))
	case 83:
		return encInt(b, int64(s.NMagic))
	case 84:
		return encInt(b, int64(s.NNullCheck))
	case 85:
		return encInt(b, int64(s.NSubscript))
	case 86:
		return encInt(b, int64(s.NMemberAccess))
	case 87:
		return encInt(b, int64(s.NLambda))
	case 88:
		return encInt(b, 0)
	case 89:
		return encInt(b, int64(s.NCalls))
	case 90:
		return encInt(b, int64(s.NUniqueCalls))
	case 91:
		return encInt(b, 0)
	case 92:
		return encInt(b, int64(s.NUnresolved))
	case 93:
		return encInt(b, int64(s.FanIn))
	case 94:
		return encInt(b, int64(s.FanOut))
	case 95:
		return encInt(b, int64(s.NCallsites))
	case 96:
		return encInt(b, int64(s.getFlag(fRecursive)))
	case 97:
		return encInt(b, int64(s.getFlag(fLeaf)))
	case 98:
		return encInt(b, int64(s.getFlag(fRoot)))
	case 99:
		return encInt(b, int64(s.NHazards))
	case 100:
		return encInt(b, int64(s.RiskScore))
	case 101:
		return encInt(b, int64(s.NReflection))
	case 102:
		return encInt(b, int64(s.NSerialization))
	case 103:
		return encInt(b, int64(s.NJNI))
	case 104:
		return encInt(b, int64(s.NExec))
	case 105:
		return encInt(b, int64(s.NIO))
	case 106:
		return encInt(b, int64(s.NNet))
	case 107:
		return encInt(b, int64(s.NSql))
	case 108:
		return encInt(b, int64(s.NCrypto))
	case 109:
		return encInt(b, int64(s.NConcurrency))
	case 110:
		return encInt(b, int64(s.NLock))
	case 111:
		return encInt(b, int64(s.NAlloc))
	case 112:
		return encInt(b, int64(s.NBoxing))
	case 113:
		return encInt(b, int64(s.NString))
	case 114:
		return encInt(b, int64(s.NResource))
	case 115:
		return encInt(b, int64(s.NUnsafe))
	case 116:
		return encInt(b, int64(s.NControl))
	case 117:
		return encInt(b, int64(s.NTextBlocks))
	case 118:
		return encInt(b, int64(s.NLambdas))
	case 119:
		return encInt(b, int64(s.NMethodRefs))
	case 120:
		return encInt(b, int64(s.NStreams))
	case 121:
		return encInt(b, int64(s.NParallelStreams))
	case 122:
		return encInt(b, int64(s.NCollectors))
	case 123:
		return encInt(b, int64(s.NBoxingSites))
	case 124:
		return encInt(b, int64(s.NBoxingInLoop))
	case 125:
		return encInt(b, int64(s.NStringConcat))
	case 126:
		return encInt(b, int64(s.NSyncBlocks))
	case 127:
		return encInt(b, int64(s.NSyncMethods))
	case 128:
		return encInt(b, int64(s.NLockAcquire))
	case 129:
		return encInt(b, int64(s.NLockRelease))
	case 130:
		return encInt(b, int64(s.NWaitCalls))
	case 131:
		return encInt(b, int64(s.NVolatileAccess))
	case 132:
		return encInt(b, int64(s.NAtomicOps))
	case 133:
		return encInt(b, int64(s.NThreadlocalOps))
	case 134:
		return encInt(b, int64(s.NThreadlocalRem))
	case 135:
		return encInt(b, int64(s.NTryResources))
	case 136:
		return encInt(b, int64(s.NCloseCalls))
	case 137:
		return encInt(b, int64(s.NResourceOpen))
	case 138:
		return encInt(b, int64(s.NFinalizers))
	case 139:
		return encInt(b, int64(s.NThrowsDeclared))
	case 140:
		return encInt(b, int64(s.NThrowSites))
	case 141:
		return encInt(b, int64(s.NCatchRethrow))
	case 142:
		return encInt(b, int64(s.NSetAccessible))
	case 143:
		return encInt(b, int64(s.NNativeCalls))
	case 144:
		return encInt(b, int64(s.NFFMArena))
	case 145:
		return encInt(b, int64(s.NFFMDowncall))
	case 146:
		return encInt(b, int64(s.NUnsafeCalls))
	case 147:
		return encInt(b, int64(s.NWildcardTypes))
	case 148:
		return encInt(b, int64(s.NRawTypes))
	case 149:
		return encInt(b, int64(s.NUncheckedCasts))
	case 150:
		return encInt(b, int64(s.NInstanceof))
	case 151:
		return encInt(b, int64(s.NNullReturns))
	case 152:
		return encInt(b, int64(s.NOptionalOps))
	case 153:
		return encInt(b, int64(s.NAnnotations))
	case 154:
		return encInt(b, int64(s.NSuppressions))
	case 155:
		return encInt(b, int64(s.NStaticWrites))
	case 156:
		return encInt(b, int64(s.NQueryCalls))
	case 157:
		return encInt(b, int64(s.NRegexCompile))
	case 158:
		return encInt(b, int64(s.NDatefmtOps))
	case 159:
		return encInt(b, int64(s.NEscapingAllocs))
	case 160:
		return encInt(b, int64(s.NAllocSites))
	case 161:
		return encInt(b, int64(s.NImplTargets))
	case 162:
		return encInt(b, int64(s.getFlag(fVtRoot)))
	case 163:
		return encInt(b, int64(s.getFlag(fExecRoot)))
	case 164:
		return encInt(b, int64(s.getFlag(fPoolRoot)))
	case 165:
		return encInt(b, int64(s.getFlag(fHandler)))
	case 166:
		return encInt(b, int64(s.getFlag(fSerializable)))
	case 167:
		return encInt(b, int64(s.getFlag(fHasSerialUID)))
	case 168:
		return encText(b, g.Str.get(s.OwnerType))
	case 169:
		return encInt(b, int64(s.NRuntimeExec))
	case 170:
		return encInt(b, int64(s.NPrintStacktrace))
	case 171:
		return encInt(b, int64(s.NDefaultCharset))
	case 172:
		return encInt(b, int64(s.NParseNoRadix))
	case 173:
		return encInt(b, int64(s.NEqualsInLoop))
	case 174:
		return encInt(b, int64(s.NWeakRandom))
	case 175:
		return encInt(b, int64(s.NRedirect))
	case 176:
		return encInt(b, int64(s.NAuthCall))
	case 177:
		return encInt(b, int64(s.NXXEParser))
	case 178:
		return encInt(b, int64(s.NZipRead))
	case 179:
		return encInt(b, int64(s.NTimeoutSet))
	case 180:
		return encInt(b, int64(s.NExecutorCreate))
	case 181:
		return encInt(b, int64(s.NSubmitInLoop))
	case 182:
		return encInt(b, int64(s.NFutureGet))
	case 183:
		return encInt(b, int64(s.NMonitorCall))
	case 184:
		return encInt(b, int64(s.NStringIntern))
	case 185:
		return encInt(b, int64(s.NRawStatement))
	case 186:
		return encInt(b, int64(s.NReadObject))
	case 187:
		return encInt(b, int64(s.NLoadLibrary))
	case 188:
		return encInt(b, int64(s.NElif))
	case 189:
		return encInt(b, int64(s.NExternalCalls))
	case 190:
		return encInt(b, int64(s.NRefEq))
	case 191:
		return encInt(b, int64(s.NNarrowCalc))
	case 192:
		return encInt(b, int64(s.NDeadException))
	case 193:
		return encInt(b, int64(s.NSuperCalls))
	case 194:
		return encInt(b, int64(s.NStaticWriteCtor))
	case 195:
		return encInt(b, int64(s.NModernIdioms))
	case 196:
		return encInt(b, int64(s.getFlag(fFlexCtor)))
	case 197:
		return encInt(b, int64(s.NResilienceAnnos))
	case 198:
		return encInt(b, int64(s.NApiVersionAttr))
	case 199:
		return encInt(b, int64(s.getFlag(fHTTPExchange)))
	case 200:
		return encInt(b, int64(s.NEe12Annos))
	case 201:
		return encInt(b, int64(s.NJSpecifyAnnos))
	case 202:
		return encInt(b, int64(s.NNotifySingle))
	case 203:
		return encInt(b, int64(s.NRunCalledDirectly))
	case 204:
		return encInt(b, 0)
	case 205:
		return encInt(b, int64(s.NBigDecimalFromDouble))
	case 206:
		return encInt(b, 0)
	case 207:
		return encInt(b, int64(s.NVolatileCompound))
	case 208:
		return encInt(b, int64(s.NSharedDatefmtUse))
	case 209:
		return encInt(b, int64(s.NListenerAdd))
	case 210:
		return encInt(b, int64(s.NListenerRemove))
	case 211:
		return encInt(b, int64(s.NThreadAlloc))
	case 212:
		return encInt(b, int64(s.NSpelEval))
	case 213:
		return encInt(b, int64(s.NFormatInLoop))
	case 214:
		return encInt(b, int64(s.NStaticCollAdd))
	case 215:
		return encInt(b, int64(s.NStaticCollRemove))
	}
	panic("unknown symbols column index")
}

const maxFileBytes = 4 * 1024 * 1024
const maxLineBytes = 1024 * 1024

var commonSkipDirs = []string{
	".git", ".hg", ".svn", ".jj", ".idea", ".vscode", ".vs", ".claude",
	"node_modules", "bower_components", "vendor", "third_party", "thirdparty",
	"external", "externals", "deps", "Godeps", "_vendor", "__pycache__",
	".mypy_cache", ".pytest_cache", ".ruff_cache", ".tox", ".venv", "venv",
	"env", ".env", "virtualenv", "build", "_build", "dist", "out", "target",
	"bin", "obj", ".gradle", ".next", ".nuxt", ".svelte-kit", ".parcel-cache",
	".turbo", ".cache", "coverage", "htmlcov", ".nyc_output", "site-packages",
	"generated-sources", "generated-test-sources",
}

var generatedMarkers = []string{
	"@generated", "DO NOT EDIT", "Code generated by", "AUTO-GENERATED",
	"autogenerated", "This file was automatically generated",
	"Generated by the protocol buffer compiler", "@flow-generated",
}

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
	if len(head) == 0 {
		return "(root)"
	}
	return strings.Join(head, "/")
}

func isGeneratedName(name string) bool {
	lo := strings.ToLower(name)
	if strings.Contains(lo, ".min.") || strings.Contains(lo, ".bundle.") ||
		strings.Contains(lo, "_pb2") || strings.HasSuffix(lo, ".g.dart") ||
		strings.Contains(lo, ".designer.") || strings.HasPrefix(lo, "zz_generated") {
		return true
	}
	for _, suf := range []string{"gen.", "generated.", "pb.", "g."} {
		from := 0
		for {
			i := strings.Index(lo[from:], suf)
			if i < 0 {
				break
			}
			i += from
			from = i + 1
			if i > 0 {
				switch lo[i-1] {
				case '-', '_', '.':
					return true
				}
			}
		}
	}
	return false
}

func isGenerated(name, head string) bool {
	if isGeneratedName(name) {
		return true
	}
	for _, m := range generatedMarkers {
		if strings.Contains(head, m) {
			return true
		}
	}
	return false
}

type cgLines struct {
	s     string
	i     int
	start int
	done  bool
}

func newPyLines(s string) *cgLines { return &cgLines{s: s} }

func (it *cgLines) next() (string, bool) {
	if it.done {
		return "", false
	}
	s, n := it.s, len(it.s)
	for it.i < n {
		var w int
		switch s[it.i] {
		case '\r':
			if it.i+1 < n && s[it.i+1] == '\n' {
				w = 2
			} else {
				w = 1
			}
		case '\n', '\v', '\f', 0x1c, 0x1d, 0x1e:
			w = 1
		default:
			if s[it.i] < 0x80 {
				it.i++
				continue
			}
			r, sz := utf8.DecodeRuneInString(s[it.i:])
			if r == 0x85 || r == 0x2028 || r == 0x2029 {
				w = sz
			} else {
				it.i += sz
				continue
			}
		}
		line := s[it.start:it.i]
		it.i += w
		it.start = it.i
		return line, true
	}
	it.done = true
	if it.start < n {
		line := s[it.start:]
		it.start = n
		return line, true
	}
	return "", false
}

func cgDecode(b []byte) string {
	if utf8.Valid(b) {
		return string(b)
	}
	var sb strings.Builder
	sb.Grow(len(b) + 8)
	for i := 0; i < len(b); {
		c := b[i]
		if c < 0x80 {
			sb.WriteByte(c)
			i++
			continue
		}
		r, sz := utf8.DecodeRune(b[i:])
		if r != utf8.RuneError || sz > 1 {
			sb.WriteRune(r)
			i += sz
			continue
		}
		n := 1
		switch {
		case c >= 0xC2 && c <= 0xDF:
			n = 2
		case c >= 0xE0 && c <= 0xEF:
			n = 3
		case c >= 0xF0 && c <= 0xF4:
			n = 4
		}
		for n > 1 && i+n <= len(b) && b[i+n]&0xC0 == 0x80 {
			n++
		}
		if n > 1 && i+n > len(b) {
			n = len(b) - i
		}
		sb.WriteRune(utf8.RuneError)
		i += n
	}
	return sb.String()
}

func toValidUTF8(s string) string {
	if utf8.ValidString(s) {
		return s
	}
	return cgDecode([]byte(s))
}

func isPySpace(r rune) bool {
	if r >= 0x1c && r <= 0x1f {
		return true
	}
	return unicode.IsSpace(r)
}

func cgStrip(s string) string  { return strings.TrimFunc(s, isPySpace) }
func cgLStrip(s string) string { return strings.TrimLeftFunc(s, isPySpace) }

var commentPrefixes = map[string]bool{
	"//": true, "#": true, "/*": true, "*": true, "*/": true,
	`"""`: true, "'''": true, "--": true, ";;": true, "%": true,
}

type discovered struct {
	str    *Interner
	files  []File
	parsed []int32
	mods   []Module
	sk     struct{ big, special, escape, denied, walkErr int32 }
	modIDs map[string]int32
}

func moduleKindName(name string) string {
	lo := "/" + strings.ToLower(name) + "/"
	if segMatch(lo, "test", "tests", "test-d", "spec", "specs", "__tests__",
		"__snapshots__", "testing", "e2e", "integration-tests",
		"integration_tests", "testdata", "test_data", "test-data", "fixture",
		"fixtures") {
		return "test"
	}
	if segMatch(lo, "vendor", "third_party", "thirdparty", "external",
		"node_modules", "deps") {
		return "vendor"
	}
	if segMatch(lo, "example", "examples", "sample", "samples", "demo",
		"demos") {
		return "example"
	}
	if segMatch(lo, "tool", "tools", "script", "scripts", "cmd", "bin") {
		return "tool"
	}
	return "source"
}

func segMatch(p string, segs ...string) bool {
	for _, s := range segs {
		if strings.Contains(p, "/"+s+"/") {
			return true
		}
	}
	return false
}

func isTestPath(rel string) bool {
	return segMatch("/"+strings.ToLower(rel)+"/", "test", "tests", "test-d",
		"spec", "specs", "__tests__", "__snapshots__", "testing", "e2e",
		"integration-tests", "integration_tests", "testdata", "test_data",
		"test-data", "fixture", "fixtures")
}

func isVendorPath(rel string) bool {
	return segMatch("/"+strings.ToLower(rel)+"/", "vendor", "third_party",
		"thirdparty", "external", "node_modules", "deps")
}

func isTestName(fn string) bool {
	if len(fn) > 4 && fn[:4] == "Test" {
		c := fn[4]
		if c >= 'A' && c <= 'Z' {
			return true
		}
	}
	return strings.HasSuffix(fn, "Tests.java") ||
		strings.HasSuffix(fn, "Test.java") ||
		strings.HasSuffix(fn, "TestCase.java") ||
		strings.HasSuffix(fn, "IT.java")
}

type discoverOpts struct {
	includeTests, includeGenerated, includeVendored bool
}

func discover(root string, o discoverOpts, str *Interner) *discovered {
	d := &discovered{modIDs: map[string]int32{}, str: str}
	realRoot := evalSym(root)
	skip := make(map[string]bool, len(commonSkipDirs))
	for _, k := range commonSkipDirs {
		skip[k] = true
	}
	var walk func(dir, rel string)
	walk = func(dir, rel string) {
		ents, err := os.ReadDir(dir)
		if err != nil {
			d.sk.walkErr++
			return
		}
		var dirs, files []string
		for _, e := range ents {
			nm := e.Name()
			if e.IsDir() {
				if skip[nm] || strings.HasPrefix(nm, ".") {
					continue
				}
				dirs = append(dirs, nm)
			} else {
				files = append(files, nm)
			}
		}
		sort.Strings(dirs)
		sort.Strings(files)

		for _, fn := range files {
			d.one(dir, rel, fn, realRoot, o)
		}
		for _, dn := range dirs {
			childRel := dn
			if rel != "" {
				childRel = rel + "/" + dn
			}
			walk(filepath.Join(dir, dn), childRel)
		}
	}
	walk(root, "")
	return d
}

func (d *discovered) one(dir, rel, fn, realRoot string, o discoverOpts) {
	if cgExt(fn) != ".java" {
		return
	}
	full := filepath.Join(dir, fn)
	if rel == "" {
		rel = fn
	} else {
		rel = rel + "/" + fn
	}
	rel = toValidUTF8(rel)
	fn = toValidUTF8(fn)

	tooBig := false
	var data []byte
	var text string

	lst, err := os.Lstat(full)
	if err != nil {
		return
	}
	if lst.Mode()&os.ModeSymlink != 0 {

		rp := evalSym(full)
		if rp != full && !strings.HasPrefix(rp, realRoot+"/") {
			d.sk.escape++
			return
		}
		if lst, err = os.Stat(full); err != nil {
			return
		}
	}

	if !lst.Mode().IsRegular() {
		d.sk.special++
		return
	}
	if lst.Size() > maxFileBytes {
		d.sk.big++
		tooBig = true
	} else {
		data, err = os.ReadFile(full)
		if err != nil {
			if os.IsPermission(err) {
				d.sk.denied++
			}
			return
		}

		if utf8.Valid(data) {
			text = unsafe.String(unsafe.SliceData(data), len(data))
		} else {
			text = cgDecode(data)
		}
	}

	if !tooBig && len(data) > 0 {
		longest, start := 0, 0
		for i := 0; i <= len(data); i++ {
			if i == len(data) || data[i] == '\n' {
				if i-start > longest {
					longest = i - start
				}
				start = i + 1
			}
		}
		if longest > maxLineBytes {
			d.sk.big++
			tooBig = true
		}
	}

	blank, cmt, maxLine, nLines := 0, 0, 0, 0
	it := newPyLines(text)
	for {
		line, ok := it.next()
		if !ok {
			break
		}
		nLines++
		if ll := utf8.RuneCountInString(line); ll > maxLine {
			maxLine = ll
		}
		stripped := cgStrip(line)
		if stripped == "" {
			blank++
		} else {
			t := clipNRunes(cgLStrip(line), 3)
			if commentPrefixes[t] {
				cmt++
			}
		}
	}
	nSloc := nLines - blank

	head := text
	if len(head) > 2000 {
		head = head[:2000]
	}
	test := isTestPath(rel) || isTestName(fn)
	gen := isGenerated(fn, head)
	vend := isVendorPath(rel)
	mname := moduleOf(rel)
	mid, ok := d.modIDs[mname]
	if !ok {
		mid = int32(len(d.mods) + 1)
		d.mods = append(d.mods, Module{ID: mid, Name: d.str.intern(mname),
			Kind: d.str.intern(moduleKindName(mname))})
		d.modIDs[mname] = mid
	}
	parse := !tooBig && text != "" &&
		(o.includeTests || !test) &&
		(o.includeGenerated || !gen) &&
		(o.includeVendored || !vend)

	sha := ""
	if len(data) > 0 {
		h := sha1.Sum(data)
		sha = hex.EncodeToString(h[:])
	}
	dirPath := "."
	if i := strings.LastIndex(rel, "/"); i >= 0 {
		dirPath = rel[:i]
	}
	d.files = append(d.files, File{
		ID: int32(len(d.files) + 1), full: d.str.intern(full), path: d.str.intern(rel),
		dir: d.str.intern(dirPath), basename: d.str.intern(fn),
		ext: d.str.intern(".java"), lang: d.str.intern("java"), ModuleID: mid, Bytes: int32(lst.Size()),
		Lines: int32(nLines), Sloc: int32(nSloc), Blank: int32(blank),
		Comment: int32(cmt), MaxLine: int32(maxLine), sha1: d.str.intern(sha),
		Parsed: b2i(parse), IsTest: b2i(test), IsGen: b2i(gen), IsVend: b2i(vend),
	})
	if parse {
		d.parsed = append(d.parsed, int32(len(d.files)-1))
	}
}

func cgExt(name string) string {
	i := strings.LastIndexByte(name, '.')
	if i <= 0 {
		return ""
	}
	return name[i:]
}

func b2i(b bool) int32 {
	if b {
		return 1
	}
	return 0
}

func evalSym(p string) string {
	r, err := filepath.EvalSymlinks(p)
	if err != nil {
		return p
	}
	return r
}

func isWordRune(r rune) bool {
	if r < 0x80 {
		return isWordByte(byte(r))
	}
	return unicode.IsLetter(r) || unicode.IsDigit(r)
}

func isWordByte(b byte) bool {
	return b == '_' || (b >= '0' && b <= '9') ||
		(b >= 'a' && b <= 'z') || (b >= 'A' && b <= 'Z')
}

func wordBoundaryOK(s string, i, j int) bool {
	if i > 0 {
		if isWordByte(s[i-1]) {
			return false
		}
		if r, _ := utf8.DecodeLastRuneInString(s[:i]); isWordRune(r) {
			return false
		}
	}
	if j < len(s) {
		if isWordByte(s[j]) {
			return false
		}
		if r, _ := utf8.DecodeRuneInString(s[j:]); isWordRune(r) {
			return false
		}
	}
	return true
}

func hasWord(s, w string) bool {
	if w == "" {
		return false
	}
	for from := 0; from < len(s); {
		i := strings.Index(s[from:], w)
		if i < 0 {
			return false
		}
		i += from
		from = i + 1
		if i > 0 && isWordByte(s[i-1]) {
			continue
		}
		return true
	}
	return false
}

func hasWordBounds(s, w string) bool {
	if w == "" {
		return false
	}
	for from := 0; from < len(s); {
		i := strings.Index(s[from:], w)
		if i < 0 {
			return false
		}
		i += from
		from = i + 1
		if wordBoundaryOK(s, i, i+len(w)) {
			return true
		}
	}
	return false
}

var markerWords = []string{"TODO", "FIXME", "XXX", "HACK", "BUG", "NOTE",
	"WARNING", "OPTIMIZE", "REVIEW", "DEPRECATED", "SAFETY", "PANIC", "UNSAFE"}

func findMarker(line string) (string, int) {
	for _, w := range markerWords {
		for from := 0; from < len(line); {
			i := indexFold(line[from:], w)
			if i < 0 {
				break
			}
			i += from
			from = i + 1
			if i > 0 {
				if r, _ := utf8.DecodeLastRuneInString(line[:i]); isWordRune(r) {
					continue
				}
			}
			j := i + len(w)
			if j < len(line) {
				if r, _ := utf8.DecodeRuneInString(line[j:]); isWordRune(r) {
					continue
				}
			}
			k := j
			for k < len(line) && (line[k] == ' ' || line[k] == '\t') {
				k++
			}
			if k < len(line) {
				switch line[k] {
				case ':', '-', '(':
					return w, i
				}
			}
		}
	}
	return "", -1
}

func indexFold(s, w string) int {
	if len(w) == 0 {
		return 0
	}
	c0 := lowerASCII(w[0])
	for i := 0; i+len(w) <= len(s); i++ {
		if lowerASCII(s[i]) != c0 {
			continue
		}
		j := 1
		for j < len(w) && lowerASCII(s[i+j]) == lowerASCII(w[j]) {
			j++
		}
		if j == len(w) {
			return i
		}
	}
	return -1
}

func lowerASCII(b byte) byte {
	if b >= 'A' && b <= 'Z' {
		return b + ('a' - 'A')
	}
	return b
}

const keepRows = 8192

func trimRows[T any](s []T) []T {
	if cap(s) > keepRows {
		return nil
	}
	return s[:0]
}

func (fo *fileOut) reset(fidx int32, str *Interner) {
	fo.idx = fidx
	fo.str = str
	fo.src = nil
	fo.kind = nil
	fo.pkgRoots = fo.pkgRoots[:0]
	fo.fileImports = nil
	fo.parseErr, fo.missing, fo.genOverride, fo.failed = 0, 0, 0, 0
	fo.syms = trimRows(fo.syms)
	fo.params = fo.params[:0]
	fo.fields = fo.fields[:0]
	fo.lits = fo.lits[:0]
	fo.markers = fo.markers[:0]
	fo.attrs = fo.attrs[:0]
	fo.imports = fo.imports[:0]
	fo.hazards = fo.hazards[:0]
	fo.typeRel = fo.typeRel[:0]
	fo.over = fo.over[:0]
	fo.excepts = fo.excepts[:0]
	fo.monOps = fo.monOps[:0]
	fo.gens = fo.gens[:0]
	fo.res = fo.res[:0]
	fo.locks = fo.locks[:0]
	fo.jpms = fo.jpms[:0]
	fo.uisites = fo.uisites[:0]
	fo.secrets = fo.secrets[:0]
	fo.pending = fo.pending[:0]
	fo.ops = trimRows(fo.ops)
	fo.identSpans = trimRows(fo.identSpans)
	if cap(fo.evBuf) > 65536 {
		fo.evBuf = nil
	} else {
		fo.evBuf = fo.evBuf[:0]
	}
	fo.symAdds = fo.symAdds[:0]
	fo.recs = fo.recs[:0]
}

func (x *xctx) one(fo *fileOut, fidx int, f *File, dstr *Interner, cst, data []byte) *fileOut {
	fo.reset(int32(fidx), x.str)

	clear(x.opdSeen)
	x.sc.dropPins()
	x.out = fo
	x.nextID = 0
	x.rec = f
	x.dstr = dstr
	x.rel = f.Path(dstr)
	if data == nil {
		fo.failed = 1
		return fo
	}
	fo.src = data
	x.src = data
	x.asciiOK = isASCII(data)
	if x.asciiOK {
		x.asciiTxt = unsafe.String(unsafe.SliceData(data), len(data))
	}

	if utf8.Valid(data) {
		x.text = unsafe.String(unsafe.SliceData(data), len(data))
		x.textOK = true
	} else {
		x.text = cgDecode(data)
		x.textOK = false
	}

	x.scanMarkers()
	x.parseFile(cst, data, x.text, f)
	head := x.text
	if len(head) > 4000 {
		head = head[:4000]
	}
	if hasGeneratedAnno(head) {
		fo.genOverride = 1
	}
	return fo
}

func isASCII(b []byte) bool {
	for _, c := range b {
		if c >= 0x80 {
			return false
		}
	}
	return true
}

func readManifests(g *Graph, root string) {
	rel := ""
	for _, mp := range manifestPatterns {
		path := root + "/" + mp[0]
		st, err := os.Stat(path)
		if err != nil || !st.Mode().IsRegular() {
			continue
		}
		data, err := os.ReadFile(path)
		if err != nil {
			continue
		}
		re, err := regexp.Compile("(?s)" + mp[1])
		if err != nil {
			continue
		}
		if mm := re.FindSubmatch(data); mm != nil {
			rel = string(mm[1])
			break
		}
		if rel != "" {
			break
		}
	}
	g.addMeta("java_release", rel)
}

const maxCell = 72

type query struct {
	name, title, notes string
	run                func(g *Graph, mod string, lim int) ([]string, [][]any)
}

var cellBuf [64]byte

func cell(v any) string {
	var t string
	switch x := v.(type) {
	case nil:
		return "-"
	case float64:
		t = round2Str(x)
	case int:
		t = strconv.Itoa(x)
	case int32:
		t = strconv.FormatInt(int64(x), 10)
	case int64:
		t = strconv.FormatInt(x, 10)
	case string:
		t = x
	default:
		t = fmt.Sprint(x)
	}
	if len(t) <= maxCell && isASCIIz(t) {
		return t
	}
	if utf8.RuneCountInString(t) <= maxCell {
		return t
	}
	r := []rune(t)
	return string(r[:maxCell-3]) + "..."
}

func isASCIIz(s string) bool {
	for i := 0; i < len(s); i++ {
		if s[i] >= 0x80 {
			return false
		}
	}
	return true
}

func round2Str(f float64) string {
	b := strconv.AppendFloat(cellBuf[:0], f, 'f', 2, 64)
	return string(b)
}

func render(w *bufio.Writer, cols []string, rows [][]any) {
	if len(rows) == 0 {
		fmt.Fprintln(w, " (no rows)")
		return
	}
	nc := len(cols)
	flat := make([]string, len(rows)*nc)
	widths := make([]int, nc)
	pad := make([]string, 81)
	for i := range pad {
		pad[i] = strings.Repeat(" ", i)
	}
	for i, c := range cols {
		widths[i] = runeWidth(c)
	}
	for i, r := range rows {
		row := flat[i*nc : i*nc+nc]
		for j := range cols {
			if j < len(r) {
				row[j] = cell(r[j])
			}
			if w := runeWidth(row[j]); w > widths[j] {
				widths[j] = w
			}
		}
	}
	buf := make([]byte, 0, 256)
	line := func(cells []string) {
		buf = append(buf[:0], ' ')
		for i, c := range cells {
			if i > 0 {
				buf = append(buf, ' ')
			}
			buf = append(buf, c...)
			if k := widths[i] - runeWidth(c); k > 0 {
				if k < len(pad) {
					buf = append(buf, pad[k]...)
				} else {
					for ; k >= len(pad); k -= len(pad) {
						buf = append(buf, pad[len(pad)-1]...)
					}
					buf = append(buf, pad[k]...)
				}
			}
		}
		buf = append(buf, '\n')
		w.Write(buf)
	}
	line(cols)
	dashes := make([]string, nc)
	for i := range cols {
		dashes[i] = strings.Repeat("-", widths[i])
	}
	line(dashes)
	for i := 0; i < len(rows); i++ {
		line(flat[i*nc : i*nc+nc])
	}
}

func runeWidth(s string) int {
	if isASCIIz(s) {
		return len(s)
	}
	return utf8.RuneCountInString(s)
}

func reportGraph(w *bufio.Writer, g *Graph) {
	fmt.Fprintf(w, "\n%s\n", strings.Repeat("=", 78))
	fmt.Fprintln(w, "OVERVIEW")
	fmt.Fprintln(w, strings.Repeat("-", 78))
	for _, k := range []string{"lang", "target", "parser", "root", "built_at"} {
		if v := g.meta(k); v != "" {
			fmt.Fprintf(w, " %-14s %s\n", k, v)
		}
	}
	files := len(g.Files)
	parsed := 0
	sloc := int32(0)
	for i := range g.Files {
		if g.Files[i].Parsed == 1 {
			parsed++
			sloc += g.Files[i].Sloc
		}
	}
	fmt.Fprintf(w, " %-14s %d catalogued, %d parsed, %d sloc\n", "files", files,
		parsed, sloc)
	kindCount := map[string]int{}
	for i := range g.Sym {
		kindCount[g.kindOf(&g.Sym[i])]++
	}
	type kc struct {
		k string
		n int
	}
	var ks []kc
	for k, n := range kindCount {
		ks = append(ks, kc{k, n})
	}
	sort.Slice(ks, func(a, b int) bool {
		if ks[a].n != ks[b].n {
			return ks[a].n > ks[b].n
		}
		return ks[a].k < ks[b].k
	})
	if len(ks) > 12 {
		ks = ks[:12]
	}
	parts := make([]string, len(ks))
	for i, e := range ks {
		parts[i] = fmt.Sprintf("%s=%d", e.k, e.n)
	}
	fmt.Fprintf(w, " %-14s %s\n", "symbols", strings.Join(parts, ", "))
	fmt.Fprintf(w, " %-14s %d edges, %d call sites, %d unresolved\n", "call graph",
		len(g.Edges), len(g.Callsite), totalUnres(g))

	fmt.Fprintf(w, "\n%s\n", strings.Repeat("=", 78))
	fmt.Fprintln(w, "HOW MUCH OF THIS TO TRUST")
	fmt.Fprintln(w, strings.Repeat("-", 78))
	errFiles := 0
	for i := range g.Files {
		if g.Files[i].NParsErr > 0 {
			errFiles++
		}
	}
	totCalls := int32(0)
	for i := range g.Sym {
		totCalls += g.Sym[i].NCalls
	}
	unres := totalUnres(g)
	if parsed == 0 {
		fmt.Fprintln(w, " NOTHING WAS PARSED. Every number below is zero because no file")
		fmt.Fprintln(w, " was read, not because this repository is empty or clean.")
	}
	fmt.Fprintf(w, " %-30s %d file(s)\n", "files with parse errors", errFiles)
	if totCalls > 0 {
		fmt.Fprintf(w, " %-30s %d of %d call sites (%d%%)\n",
			"calls we could NOT resolve", unres, totCalls, 100*unres/totCalls)
	} else {
		fmt.Fprintf(w, " %-30s no calls were recorded at all -- this is the absence of\n",
			"call resolution")
		fmt.Fprintf(w, " %-30s data, not a clean result\n", "")
	}
	fmt.Fprintln(w, " A high unresolved share means the call-graph queries below see less")
	fmt.Fprintln(w, " than they imply. `v_blindspot` lists exactly where.")

	sections := []struct {
		label string
		cols  []string
		fn    func() [][]any
	}{
		{"BIGGEST MODULES", []string{"name", "files", "sloc", "syms", "instab"},
			func() [][]any { return reportModules(g) }},
		{"HEAVIEST FUNCTIONS",
			[]string{"name", "sloc", "cyclo", "cog", "nest", "fan_in", "at"},
			func() [][]any { return reportFn(g, byCyclo) }},
		{"MOST DEPENDED ON",
			[]string{"name", "fan_in", "fan_out", "cyclo", "sloc", "at"},
			func() [][]any { return reportFn(g, byFanIn) }},
		{"MARKERS LEFT IN THE CODE", []string{"kind", "n"},
			func() [][]any { return reportMarkers(g) }},
	}
	for _, sec := range sections {
		fmt.Fprintf(w, "\n%s\n%s\n", strings.Repeat("=", 78), sec.label)
		fmt.Fprintln(w, strings.Repeat("-", 78))
		render(w, sec.cols, sec.fn())
	}
}

func totalUnres(g *Graph) int32 {
	n := int32(0)
	for i := range g.Unres {
		n += g.Unres[i].N
	}
	return n
}

func round2(f float64) float64 { return float64(int64(f*100+copySign(0.5, f))) / 100 }

func copySign(a, b float64) float64 {
	if b < 0 {
		return -a
	}
	return a
}

func reportModules(g *Graph) [][]any {
	rows := make([][]any, 0, len(g.Mod))
	for i := range g.Mod {
		m := &g.Mod[i]
		if m.NFiles == 0 {
			continue
		}
		rows = append(rows, []any{g.Str.get(m.Name), int(m.NFiles), int(m.Sloc),
			int(m.NSymbols), round2(m.Instability)})
	}
	sortRows(rows, sortKey{col: 2, asc: false})
	return limitRows(rows, 12)
}

type fnOrder int

const (
	byCyclo fnOrder = iota
	byFanIn
)

func reportFn(g *Graph, how fnOrder) [][]any {
	cols := []any{}
	rows := make([][]any, 0, 64)
	for i := range g.Sym {
		s := &g.Sym[i]
		if !isFnKind(s.Kind) {
			continue
		}
		if how == byCyclo {
			rows = append(rows, []any{g.Str.get(s.Name), int(s.Sloc),
				int(s.Cyclomatic), int(s.Cognitive), int(s.MaxNesting),
				int(s.FanIn), g.at(s.FileID, s.LineStart)})
		} else {
			rows = append(rows, []any{g.Str.get(s.Name), int(s.FanIn),
				int(s.FanOut), int(s.Cyclomatic), int(s.Sloc),
				g.at(s.FileID, s.LineStart)})
		}
	}
	if how == byCyclo {
		sortRows(rows, sortKey{col: 2, asc: false})
	} else {
		sortRows(rows, sortKey{col: 1, asc: false})
	}
	_ = cols
	return limitRows(rows, 12)
}

func reportMarkers(g *Graph) [][]any {
	m := map[string]int{}
	for i := range g.Markers {
		m[g.Str.get(g.Markers[i].Kind)]++
	}
	type kc struct {
		k string
		n int
	}
	var ks []kc
	for k, n := range m {
		ks = append(ks, kc{k, n})
	}
	sort.Slice(ks, func(a, b int) bool {
		if ks[a].n != ks[b].n {
			return ks[a].n > ks[b].n
		}
		return ks[a].k < ks[b].k
	})
	rows := make([][]any, len(ks))
	for i, e := range ks {
		rows[i] = []any{e.k, e.n}
	}
	return rows
}

type jkinds struct {
	names      []string
	nodeCount  int
	isLoop     []bool
	isBranch   []bool
	isNest     []bool
	isCall     []bool
	isOperator []bool
	isString   []bool
	isNumber   []bool
	isComment  []bool
	isIf       []bool
	prune      []bool
	bump       []func(*Sym, int32)
	funcKind   []string
	typeKind   []string
	trackIden  []bool
}

var kinds *jkinds

var bumpByName = func() map[string]func(*Sym, int32) {
	m := map[string]func(*Sym, int32){}
	maps.Copy(m, map[string]func(*Sym, int32){
		"n_returns":             func(s *Sym, n int32) { s.NReturns += n },
		"n_throw_sites":         func(s *Sym, n int32) { s.NThrowSites += n },
		"n_try":                 func(s *Sym, n int32) { s.NTry += n },
		"n_try_resources":       func(s *Sym, n int32) { s.NTryResources += n },
		"n_catch":               func(s *Sym, n int32) { s.NCatch += n },
		"n_finally":             func(s *Sym, n int32) { s.NFinally += n },
		"n_switch":              func(s *Sym, n int32) { s.NSwitch += n },
		"n_cases":               func(s *Sym, n int32) { s.NCases += n },
		"n_ternary":             func(s *Sym, n int32) { s.NTernary += n },
		"n_lambdas":             func(s *Sym, n int32) { s.NLambdas += n },
		"n_method_refs":         func(s *Sym, n int32) { s.NMethodRefs += n },
		"n_instanceof":          func(s *Sym, n int32) { s.NInstanceof += n },
		"n_synchronized_blocks": func(s *Sym, n int32) { s.NSyncBlocks += n },
		"n_labels":              func(s *Sym, n int32) { s.NLabels += n },
		"n_alloc_sites":         func(s *Sym, n int32) { s.NAllocSites += n },
		"n_annotations":         func(s *Sym, n int32) { s.NAnnotations += n },
		"n_wildcard_types":      func(s *Sym, n int32) { s.NWildcardTypes += n },
		"n_locals":              func(s *Sym, n int32) { s.NLocals += n },
		"n_assign":              func(s *Sym, n int32) { s.NAssign += n },
		"n_incdec":              func(s *Sym, n int32) { s.NIncDec += n },
		"n_generic_params":      func(s *Sym, n int32) { s.NGenericParams += n },
		"n_subscript":           func(s *Sym, n int32) { s.NSubscript += n },
		"n_member_access":       func(s *Sym, n int32) { s.NMemberAccess += n },
		"n_calls":               func(s *Sym, n int32) { s.NCalls += n },
		"n_resource_open":       func(s *Sym, n int32) { s.NResourceOpen += n },
		"n_elif":                func(s *Sym, n int32) { s.NElif += n },
		"call_in_loop":          func(s *Sym, n int32) { s.CallInLoop += n },
		"branch_in_loop":        func(s *Sym, n int32) { s.BranchInLoop += n },
		"alloc_in_loop":         func(s *Sym, n int32) { s.AllocInLoop += n },
		"io_in_loop":            func(s *Sym, n int32) { s.IOInLoop += n },
		"lock_in_loop":          func(s *Sym, n int32) { s.LockInLoop += n },
		"concat_in_loop":        func(s *Sym, n int32) { s.ConcatInLoop += n },
		"regex_in_loop":         func(s *Sym, n int32) { s.RegexInLoop += n },
		"query_in_loop":         func(s *Sym, n int32) { s.QueryInLoop += n },
	})
	return m
}()

const maxKindID = 65536

func init() {

	n := maxKindID
	names := make([]string, n)
	for i := range n {
		names[i] = tsSymbolName(i)
	}
	k := &jkinds{names: names, nodeCount: n}
	mk := func() []bool {
		b := make([]bool, n)
		return b
	}
	k.isLoop, k.isBranch, k.isNest = mk(), mk(), mk()
	k.isCall, k.isOperator, k.isString = mk(), mk(), mk()
	k.isNumber, k.isComment, k.isIf = mk(), mk(), mk()
	k.prune, k.trackIden = mk(), mk()
	k.bump = make([]func(*Sym, int32), n)
	k.funcKind = make([]string, n)
	k.typeKind = make([]string, n)
	for i, name := range names {
		if loops[name] {
			k.isLoop[i] = true
		}
		if branches[name] {
			k.isBranch[i] = true
		}
		if nests[name] {
			k.isNest[i] = true
		}
		if callNodes[name] {
			k.isCall[i] = true
		}
		if operatorNodes[name] {
			k.isOperator[i] = true
		}
		if stringNodes[name] {
			k.isString[i] = true
		}
		if numberNodes[name] {
			k.isNumber[i] = true
		}
		if commentNodes[name] {
			k.isComment[i] = true
		}
		if ifNodes[name] {
			k.isIf[i] = true
		}
		if fn, ok := funcKindOf[name]; ok {
			k.funcKind[i] = kindNames[fn]
			k.prune[i] = true
		}
		if fn, ok := typeKindOf[name]; ok {
			k.typeKind[i] = kindNames[fn]
			k.prune[i] = true
		}
		if col, ok := counters[name]; ok {
			if f, ok := bumpByName[col]; ok {
				k.bump[i] = f
			}
		}
	}
	kinds = k
}

type pending struct {
	sym   int32
	name  uint32
	line  int32
	owner string
}

type fileOut struct {
	idx  int32
	src  []byte
	str  *Interner
	kind []string
	syms []Sym
	recs []tsRec

	params  []Param
	fields  []Field
	lits    []Literal
	markers []Marker
	attrs   []Attr
	imports []Import
	hazards []Hazard
	typeRel []TypeRel
	over    []Override
	excepts []Exception
	monOps  []MonitorOp
	gens    []Generic
	res     []Resource
	locks   []LockOp
	jpms    []JPMS
	uisites []InputSite
	secrets []Secret
	pending []pending

	parseErr    int32
	missing     int32
	genOverride int32
	pkgRoots    []string
	fileImports map[string]uint32

	ops        []linkOp
	identSpans [][2]uint32
	symAdds    []symAdd
	evBuf      []event
	failed     int32
}

type typeDelta struct {
	typeGens []genRec
	name     uint32
	parents  []uint32
	vol      []string
	stat     []string
	tl       []string
	df       []string
	scl      []string
}

type throwRec struct {
	name string
	line int32
}

type genRec struct {
	name, bound string
	owner       string
	line        int32
}

type linkOp struct {
	isType       bool
	delta        typeDelta
	sym          int32
	closes       int32
	kind         string
	name         string
	owner        string
	line         int32
	identLo      int32
	identHi      int32
	events       []event
	throws       []throwRec
	gens         []genRec
	wantOverride int32
	isAnnotated  int32
	isFwEntry    int32
	nPar         int32
	native       int32
}

type symAdd struct {
	col   int8
	val   int32
	symID int32
}

const (
	addVolAccess = iota
	addStaticWrites
	addThreadlocalOps
	addThreadlocalRemove
	addVolatileCompound
	addSharedDatefmtUse
	addStaticCollAdd
	addStaticCollRemove
	addJSpecifyAnnos
)

type xctx struct {
	jk       *jkinds
	str      *Interner
	dstr     *Interner
	kindLoc  map[string]uint32
	p        *tsParser
	out      *fileOut
	rec      *File
	src      []byte
	text     string
	asciiOK  bool
	asciiTxt string
	// textOK is set when text aliases src byte-for-byte (the file was valid
	// UTF-8), so a node's byte range indexes text directly and a token slice
	// needs no decode/allocation.  For invalid UTF-8, text is the decoded
	// form and offsets do not line up.
	textOK bool
	rel    string

	trackIdentifiers bool
	curBody          tsNode
	nextID           int32
	keepTrees        bool

	sc  bstatsScratch
	bst bstats

	opSeen  []bool
	opIds   []uint16
	opdSeen map[string]int32
	opdGen  int32
	annos   map[string]bool

	walkStack []stackItem
}

type scope struct {
	symID    int32
	qualPre  string
	typeName string
	typeID   int32
}

func newXctx(p *tsParser, str *Interner) *xctx {
	return &xctx{jk: kinds, str: str, p: p,
		kindLoc: make(map[string]uint32, 16),
		opSeen:  make([]bool, maxKindID),
		opIds:   make([]uint16, 0, 16),
		opdSeen: make(map[string]int32, 4096)}
}

func (x *xctx) kindID(name string) uint32 {
	if v, ok := x.kindLoc[name]; ok {
		return v
	}
	v := x.str.intern(name)
	x.kindLoc[name] = v
	return v
}

func (x *xctx) name(n tsNode) string {
	t := x.jk.names[n.kindID()]
	if t == "lambda_expression" {
		return "(lambda)"
	}
	if t == "static_initializer" {
		return "<clinit>"
	}
	if c := n.childByFieldName(fName); c.ok() {
		return strings.TrimSpace(x.txt(c))
	}
	for i := 0; i < n.namedChildCount(); i++ {
		c := n.namedChild(i)
		switch x.jk.names[c.kindID()] {
		case "identifier", "type_identifier", "scoped_identifier":
			return strings.TrimSpace(x.txt(c))
		}
	}
	return ""
}

func (x *xctx) modifiers(n tsNode) string {
	for i := 0; i < n.namedChildCount(); i++ {
		c := n.namedChild(i)
		if x.jk.names[c.kindID()] == "modifiers" {
			return x.txt(c)
		}
	}
	return ""
}

func (x *xctx) annotations(n tsNode) map[string]bool {
	if x.annos == nil {
		x.annos = make(map[string]bool, 8)
	} else {
		clear(x.annos)
	}
	out := x.annos
	for c := range eachNamedKid(n) {
		if x.jk.names[c.kindID()] != "modifiers" {
			continue
		}
		for a := range eachNamedKid(c) {
			an := x.jk.names[a.kindID()]
			if an != "annotation" && an != "marker_annotation" {
				continue
			}
			nm := a.childByFieldName(fName)
			if nm.ok() {
				out[lastSegment(x.txt(nm))] = true
			}
		}
		break
	}
	return out
}

var ee12GenericAnnos = newSet("Query", "Find", "FindAll", "Save", "Delete",
	"Insert", "Update")

func (x *xctx) qualifiedEE12Annos(n tsNode) int32 {
	generic := ee12GenericAnnos
	cnt := 0
	for c := range eachNamedKid(n) {
		if x.jk.names[c.kindID()] != "modifiers" {
			continue
		}
		for a := range eachNamedKid(c) {
			an := x.jk.names[a.kindID()]
			if an != "annotation" && an != "marker_annotation" {
				continue
			}
			nm := a.childByFieldName(fName)
			if !nm.ok() {
				continue
			}
			full := x.txt(nm)
			simple := lastSegment(full)
			if !jakartaEE12Annotations[simple] {
				continue
			}
			if strings.Contains(full, ".") && generic[simple] {
				pkg := full[:strings.LastIndexByte(full, '.')]
				if !strings.HasPrefix(pkg, "jakarta.") &&
					!strings.HasPrefix(pkg, "javax.") {
					continue
				}
			}
			cnt++
		}
	}
	return int32(cnt)
}

func (x *xctx) annotationArgValues(n tsNode, arg string) []string {
	var vals []string
	for c := range eachNamedKid(n) {
		if x.jk.names[c.kindID()] != "modifiers" {
			continue
		}
		for a := range eachNamedKid(c) {
			an := x.jk.names[a.kindID()]
			if an != "annotation" && an != "marker_annotation" {
				continue
			}
			args := a.childByFieldName(fArguments)
			if !args.ok() {
				continue
			}
			for e := range eachNamedKid(args) {
				if x.jk.names[e.kindID()] != "element_value_pair" {
					continue
				}
				k := e.childByFieldName(fKey)
				v := e.childByFieldName(fValue)
				if !k.ok() || !v.ok() {
					continue
				}
				if lastSegment(x.txt(k)) == arg {
					vals = append(vals, clipStr(x.txt(v), 120))
				}
			}
		}
		break
	}
	return vals
}

func (x *xctx) supertypePairs(n tsNode) [][2]string {
	var out [][2]string
	add := func(field tsFieldID, rel string) {
		c := n.childByFieldName(field)
		if !c.ok() {
			return
		}
		holders := []tsNode{c}
		for k := range eachNamedKid(c) {
			if x.jk.names[k.kindID()] == "type_list" {
				holders = []tsNode{k}
				break
			}
		}
		for _, h := range holders {
			for t := range eachNamedKid(h) {
				switch x.jk.names[t.kindID()] {
				case "type_identifier", "scoped_type_identifier", "generic_type":
					out = append(out, [2]string{simpleType(x.txt(t)), rel})
				}
			}
		}
	}
	add(fSuperclass, "extends")
	add(fInterfaces, "implements")
	add(fPermits, "permits")

	if x.jk.names[n.kindID()] == "interface_declaration" {
		if c := n.childByFieldName(fInterfaces); !c.ok() {
			for k := range eachNamedKid(n) {
				if x.jk.names[k.kindID()] != "extends_interfaces" {
					continue
				}
				walkPre(k, func(m tsNode) bool {
					switch x.jk.names[m.kindID()] {
					case "type_identifier", "scoped_type_identifier", "generic_type":
						out = append(out, [2]string{simpleType(x.txt(m)), "extends"})
					}
					return true
				})
			}
		}
	}
	return out
}

func (x *xctx) countTypeParams(n tsNode) int32 {
	tp := n.childByFieldName(fTypeParams)
	if !tp.ok() {
		return 0
	}
	var c int32
	for i := 0; i < tp.namedChildCount(); i++ {
		if x.jk.names[tp.namedChild(i).kindID()] == "type_parameter" {
			c++
		}
	}
	return c
}

func (x *xctx) countParams(params tsNode) int32 {
	if !params.ok() {
		return 0
	}
	if x.jk.names[params.kindID()] == "identifier" {
		return 1
	}
	var c int32
	for k := range eachNamedKid(params) {
		switch x.jk.names[k.kindID()] {
		case "formal_parameter", "spread_parameter", "receiver_parameter",
			"identifier":
			c++
		}
	}
	return c
}

var collectionHeadsSimple = newSet("List", "ArrayList", "LinkedList", "Map",
	"HashMap", "TreeMap", "LinkedHashMap", "ConcurrentHashMap", "Set", "HashSet",
	"TreeSet", "LinkedHashSet", "Collection", "Queue", "Deque", "ArrayDeque")

func isCollectionType(t string) bool {
	return strings.Contains(t, "[") || collectionHeadsSimple[simpleType(t)]
}

var primitives = newSet("int", "long", "short", "byte", "char", "float",
	"double", "boolean", "void")

func isNullableType(t string) bool { return !primitives[simpleType(t)] }

func (x *xctx) isFlexConstructor(n tsNode) bool {
	body := n.childByFieldName(fBody)
	if !body.ok() || !body.hasError() {
		return false
	}
	flex := false
	walkPre(body, func(m tsNode) bool {
		if x.jk.names[m.kindID()] != "ERROR" {
			return true
		}
		t := strings.TrimSpace(x.txt(m))
		if strings.HasPrefix(t, "super(") || strings.HasPrefix(t, "this(") ||
			t == "()" {
			flex = true
			return false
		}
		return true
	})
	return flex
}

func (x *xctx) inTryResources(n tsNode) bool {
	return x.ancestorTypes(n, x.curBody, "resource_specification")
}

func (x *xctx) inSynchronized(n tsNode) bool {
	return x.ancestorTypes(n, x.curBody, "synchronized_statement")
}

func (x *xctx) slocOf(n tsNode) int32 {
	return countCodeLines(x.src[int(n.startByte()):int(n.endByte())])
}

func countCodeLines(seg []byte) int32 {
	var cnt int32
	start := 0
	for i := 0; i <= len(seg); i++ {
		if i == len(seg) {
			if lineCounts(seg[start:i]) {
				cnt++
			}
			break
		}
		var w int
		switch c := seg[i]; {
		case c == '\r':
			w = 1
			if i+1 < len(seg) && seg[i+1] == '\n' {
				w = 2
			}
		case c == '\n' || c == '\v' || c == '\f' || c == 0x1c || c == 0x1d ||
			c == 0x1e:
			w = 1
		case c == 0xc2 && i+1 < len(seg) && seg[i+1] == 0x85:
			w = 2
		case c == 0xe2 && i+2 < len(seg) && seg[i+1] == 0x80 &&
			(seg[i+2] == 0xa8 || seg[i+2] == 0xa9):
			w = 3
		default:
			continue
		}
		if lineCounts(seg[start:i]) {
			cnt++
		}
		i += w - 1
		start = i + 1
	}
	return cnt
}

func lineCounts(line []byte) bool {
	i := 0
	for i < len(line) {
		r, sz := utf8.DecodeRune(line[i:])
		if !isPySpace(r) {
			break
		}
		i += sz
	}
	if i >= len(line) {
		return false
	}
	rest := line[i:]
	switch {
	case len(rest) >= 2 && rest[0] == '/' && rest[1] == '/',
		rest[0] == '#',
		len(rest) >= 2 && rest[0] == '/' && rest[1] == '*',
		rest[0] == '*',
		len(rest) >= 2 && rest[0] == '-' && rest[1] == '-',
		len(rest) >= 2 && rest[0] == ';' && rest[1] == ';',
		rest[0] == '%',
		len(rest) >= 3 && rest[0] == '"' && rest[1] == '"' && rest[2] == '"',
		len(rest) >= 3 && rest[0] == '\'' && rest[1] == '\'' && rest[2] == '\'':
		return false
	}
	return true
}

func (x *xctx) signatureOf(n tsNode) string {
	s := int(n.startByte())
	end := int(n.endByte())
	if b := n.childByFieldName(fBody); b.ok() {
		end = int(b.startByte())
	}
	if x.asciiOK {
		return strings.TrimSpace(x.asciiTxt[s:end])
	}
	if x.textOK {
		return strings.TrimSpace(x.text[s:end])
	}
	return strings.TrimSpace(cgDecode(x.src[s:end]))
}

func (x *xctx) docstringLines(n tsNode) int32 {
	var n2 int32
	prev := n.prevSibling()
	for prev.ok() && commentNodes[x.jk.names[prev.kindID()]] {
		txt := cgLStrip(x.txt(prev))
		sp, ep := prev.startRow(), prev.endRow()
		switch {
		case hasDocPrefix(txt):
			n2 += int32(ep-sp) + 1
		case n2 == 0 && ep+1 >= n.startRow():
			n2 += int32(ep-sp) + 1
		default:
			return n2
		}
		prev = prev.prevSibling()
	}
	return n2
}

var docPrefixes = []string{"///", "/**", "##", `"""`, "'''", "#'", "--|"}

func hasDocPrefix(s string) bool {
	for _, p := range docPrefixes {
		if strings.HasPrefix(s, p) {
			return true
		}
	}
	return false
}

var funcKindOf = map[string]uint32{
	"method_declaration":                  kindMethod,
	"constructor_declaration":             kindConstructor,
	"compact_constructor_declaration":     kindConstructor,
	"annotation_type_element_declaration": kindMethod,
	"static_initializer":                  kindMethod,
	"lambda_expression":                   kindClosure,
}

var typeKindOf = map[string]uint32{
	"class_declaration":           kindClass,
	"interface_declaration":       kindInterface,
	"enum_declaration":            kindEnum,
	"record_declaration":          kindRecord,
	"annotation_type_declaration": kindType,
}

var counters = map[string]string{
	"return_statement":                "n_returns",
	"throw_statement":                 "n_throw_sites",
	"try_statement":                   "n_try",
	"try_with_resources_statement":    "n_try_resources",
	"catch_clause":                    "n_catch",
	"finally_clause":                  "n_finally",
	"switch_expression":               "n_switch",
	"switch_label":                    "n_cases",
	"ternary_expression":              "n_ternary",
	"lambda_expression":               "n_lambdas",
	"method_reference":                "n_method_refs",
	"instanceof_expression":           "n_instanceof",
	"synchronized_statement":          "n_synchronized_blocks",
	"labeled_statement":               "n_labels",
	"object_creation_expression":      "n_alloc_sites",
	"array_creation_expression":       "n_alloc_sites",
	"annotation":                      "n_annotations",
	"marker_annotation":               "n_annotations",
	"wildcard":                        "n_wildcard_types",
	"local_variable_declaration":      "n_locals",
	"assignment_expression":           "n_assign",
	"update_expression":               "n_incdec",
	"type_parameter":                  "n_generic_params",
	"array_access":                    "n_subscript",
	"field_access":                    "n_member_access",
	"explicit_constructor_invocation": "n_calls",
	"resource":                        "n_resource_open",
}

var loopCallCounters = [][2]string{
	{"prepareStatement", "query_in_loop"},
	{"createQuery", "query_in_loop"},
	{"createNativeQuery", "query_in_loop"},
	{"executeQuery", "query_in_loop"},
	{"executeUpdate", "query_in_loop"},
	{"getResultList", "query_in_loop"},
	{"Pattern.compile", "regex_in_loop"},
	{"new SimpleDateFormat", "n_datefmt_ops"},
	{"format", "n_format_in_loop"},
}

func newSet(names ...string) map[string]bool {
	m := make(map[string]bool, len(names))
	for _, n := range names {
		m[n] = true
	}
	return m
}

func newSetFrom(s string) map[string]bool {
	return newSet(strings.Fields(s)...)
}

var loops = newSetFrom(`for_statement enhanced_for_statement while_statement do_statement`)
var branches = newSetFrom(`if_statement`)
var nests = newSetFrom(`if_statement for_statement enhanced_for_statement
	while_statement do_statement switch_expression try_statement
	try_with_resources_statement catch_clause synchronized_statement
	lambda_expression`)
var callNodes = newSetFrom(`method_invocation object_creation_expression method_reference`)
var operatorNodes = newSetFrom(`binary_expression unary_expression assignment_expression
	update_expression array_access field_access cast_expression
	instanceof_expression ternary_expression`)
var stringNodes = newSetFrom(`string_literal character_literal`)
var numberNodes = newSetFrom(`decimal_integer_literal hex_integer_literal
	octal_integer_literal binary_integer_literal decimal_floating_point_literal
	hex_floating_point_literal`)
var commentNodes = newSetFrom(`line_comment block_comment`)
var ifNodes = newSetFrom(`if_statement`)
var qualifierNodes = newSetFrom(`identifier this super field_access scoped_identifier
	type_identifier scoped_type_identifier generic_type`)

var hazardCalls = func() map[string]string {
	src := `
Class.forName reflection|getDeclaredMethod reflection|getDeclaredMethods reflection|
getDeclaredField reflection|getDeclaredFields reflection|getDeclaredConstructor reflection|
getMethod reflection|getField reflection|setAccessible reflection|
trySetAccessible reflection|newInstance reflection|invoke reflection|
Proxy.newProxyInstance reflection|MethodHandles.lookup reflection|
MethodHandles.privateLookupIn reflection|privateLookupIn reflection|findVirtual reflection|
findStatic reflection|findSpecial reflection|unreflect reflection|
ServiceLoader.load reflection|getContextClassLoader reflection|getClassLoader reflection|
loadClass reflection|defineClass reflection|getAnnotation reflection|
isAnnotationPresent reflection|getEnumConstants reflection|getComponentType reflection|
Array.newInstance reflection|
new ObjectInputStream serialization|readObject serialization|readUnshared serialization|
readExternal serialization|resolveClass serialization|new XMLDecoder serialization|
SerializationUtils.deserialize serialization|readValue serialization|
enableDefaultTyping serialization|activateDefaultTyping serialization|Yaml.load serialization|
new Yaml serialization|fromXML serialization|InitialContext.lookup serialization|
new InitialContext serialization|new ObjectOutputStream serialization|writeObject serialization|
readResolve serialization|writeReplace serialization|
System.loadLibrary jni|System.load jni|Runtime.loadLibrary jni|Linker.nativeLinker jni|
nativeLinker jni|downcallHandle jni|upcallStub jni|SymbolLookup.libraryLookup jni|
libraryLookup jni|loaderLookup jni|Arena.ofConfined jni|Arena.ofShared jni|
Arena.ofAuto jni|Arena.global jni|MemorySegment.ofAddress jni|reinterpret jni|
allocateFrom jni|MemoryLayout.structLayout jni|
Unsafe.getUnsafe unsafe|getUnsafe unsafe|allocateMemory unsafe|reallocateMemory unsafe|
freeMemory unsafe|objectFieldOffset unsafe|staticFieldOffset unsafe|
arrayBaseOffset unsafe|putOrderedObject unsafe|putOrderedLong unsafe|
copyMemory unsafe|setMemory unsafe|park unsafe|ByteBuffer.allocateDirect unsafe|
allocateDirect unsafe|VarHandle.fullFence unsafe|fullFence unsafe|acquireFence unsafe|
releaseFence unsafe|loadLoadFence unsafe|storeStoreFence unsafe|
Runtime.exec exec|Runtime.getRuntime exec|new ProcessBuilder exec|ProcessBuilder.start exec|
new ScriptEngineManager exec|getEngineByName exec|getEngineByExtension exec|
System.exit exec|Runtime.halt exec|addShutdownHook exec|
new FileInputStream io|new FileOutputStream io|new FileReader io|new FileWriter io|
new RandomAccessFile io|new BufferedReader io|new BufferedWriter io|new PrintWriter io|
new InputStreamReader io|new OutputStreamWriter io|Files.newInputStream io|
Files.newOutputStream io|Files.newBufferedReader io|Files.newBufferedWriter io|
Files.readAllBytes io|Files.readString io|Files.write io|Files.lines io|Files.walk io|
Files.list io|Files.createTempFile io|Files.delete io|FileChannel.open io|
IOUtils.toByteArray io|getResourceAsStream io|new ZipFile io|new ZipInputStream io|
new GZIPInputStream io|
new Socket net|new ServerSocket net|new URL net|openConnection net|openStream net|
HttpClient.newHttpClient net|HttpClient.newBuilder net|send net|sendAsync net|
SocketChannel.open net|ServerSocketChannel.open net|Selector.open net|
new DatagramSocket net|InetAddress.getByName net|bind net|connect net|
executeQuery sql|executeUpdate sql|executeBatch sql|prepareStatement sql|prepareCall sql|
createStatement sql|getConnection sql|createQuery sql|createNativeQuery sql|
createCriteriaQuery sql|getResultList sql|getSingleResult sql|findAll sql|findById sql|
saveAll sql|setAutoCommit sql|
MessageDigest.getInstance crypto|Cipher.getInstance crypto|KeyGenerator.getInstance crypto|
SecretKeySpec crypto|new SecureRandom crypto|SecureRandom.getInstance crypto|
new Random crypto|Math.random crypto|SSLContext.getInstance crypto|
TrustManagerFactory.getInstance crypto|setHostnameVerifier crypto|
Signature.getInstance crypto|Mac.getInstance crypto|KeyStore.getInstance crypto|
Thread.ofVirtual concurrency|Thread.ofPlatform concurrency|Thread.startVirtualThread concurrency|
startVirtualThread concurrency|Executors.newVirtualThreadPerTaskExecutor concurrency|
newVirtualThreadPerTaskExecutor concurrency|Executors.newFixedThreadPool concurrency|
Executors.newCachedThreadPool concurrency|Executors.newSingleThreadExecutor concurrency|
Executors.newScheduledThreadPool concurrency|Executors.newWorkStealingPool concurrency|
new ThreadPoolExecutor concurrency|new ForkJoinPool concurrency|ForkJoinPool.commonPool concurrency|
new Thread concurrency|CompletableFuture.supplyAsync concurrency|
CompletableFuture.runAsync concurrency|supplyAsync concurrency|runAsync concurrency|
new StructuredTaskScope concurrency|StructuredTaskScope.open concurrency|
ScopedValue.where concurrency|ScopedValue.newInstance concurrency|
ThreadLocal.withInitial concurrency|new ThreadLocal concurrency|
new InheritableThreadLocal concurrency|new FastThreadLocal concurrency|parallelStream concurrency|
Thread.sleep concurrency|Thread.currentThread concurrency|Thread.onSpinWait concurrency|
wait concurrency|notify concurrency|notifyAll concurrency|await concurrency|
countDown concurrency|new CountDownLatch concurrency|new Semaphore concurrency|
new CyclicBarrier concurrency|new Phaser concurrency|AtomicInteger concurrency|
AtomicLong concurrency|AtomicReference concurrency|compareAndSet concurrency|
getAndSet concurrency|incrementAndGet concurrency|getAndIncrement concurrency|
updateAndGet concurrency|accumulateAndGet concurrency|lazySet concurrency|
lock lock|tryLock lock|unlock lock|lockInterruptibly lock|new ReentrantLock lock|
new ReentrantReadWriteLock lock|new StampedLock lock|readLock lock|writeLock lock|
tryOptimisticRead lock|unlockRead lock|unlockWrite lock|
Collections.synchronizedList lock|Collections.synchronizedMap lock|
Collections.synchronizedSet lock|new ConcurrentHashMap lock|computeIfAbsent lock|
new StringBuilder alloc|new StringBuffer alloc|new ArrayList alloc|new HashMap alloc|
new HashSet alloc|new LinkedList alloc|new byte alloc|Arrays.copyOf alloc|
Arrays.copyOfRange alloc|System.arraycopy alloc|clone alloc|toArray alloc|
String.format alloc|format alloc|concat alloc|getBytes alloc|toCharArray alloc|
Collectors.toList alloc|Collectors.toMap alloc|Collectors.joining alloc|
Collectors.groupingBy alloc|
Integer.valueOf boxing|Long.valueOf boxing|Double.valueOf boxing|Float.valueOf boxing|
Short.valueOf boxing|Byte.valueOf boxing|Character.valueOf boxing|Boolean.valueOf boxing|
intValue boxing|longValue boxing|doubleValue boxing|floatValue boxing|booleanValue boxing|
shortValue boxing|new Integer boxing|new Long boxing|new Double boxing|new Boolean boxing|
new Character boxing|Integer.parseInt boxing|Long.parseLong boxing|
Double.parseDouble boxing|
Pattern.compile string|matches string|replaceAll string|replaceFirst string|split string|
String.join string|new String string|substring string|intern string|toLowerCase string|
toUpperCase string|new SimpleDateFormat string|DateTimeFormatter.ofPattern string|
new Date string|Calendar.getInstance string|new DecimalFormat string|new NumberFormat string|
close resource|closeQuietly resource|IOUtils.closeQuietly resource|Cleaner.create resource|
finalize resource|shutdown resource|shutdownNow resource|awaitTermination resource|
release resource|retain resource|refCnt resource|free resource|dispose resource|
assertTrue control|requireNonNull control|checkArgument control|checkState control|
printStackTrace control|getStackTrace control|fillInStackTrace control|
Thread.dumpStack control|System.getProperty control|System.setProperty control|
System.getenv control`
	m := map[string]string{}
	for pair := range strings.SplitSeq(src, "|") {
		fields := strings.Fields(pair)

		if len(fields) < 2 {
			continue
		}
		m[strings.Join(fields[:len(fields)-1], " ")] = fields[len(fields)-1]
	}
	return m
}()

var resourceTypes = newSetFrom(`FileInputStream FileOutputStream FileReader FileWriter
	RandomAccessFile BufferedReader BufferedWriter BufferedInputStream
	BufferedOutputStream PrintWriter PrintStream InputStreamReader OutputStreamWriter
	DataInputStream DataOutputStream ObjectInputStream ObjectOutputStream ZipFile
	ZipInputStream ZipOutputStream GZIPInputStream GZIPOutputStream JarFile Socket
	ServerSocket DatagramSocket SocketChannel ServerSocketChannel FileChannel
	Selector Scanner Formatter Connection Statement PreparedStatement CallableStatement
	ResultSet InputStream OutputStream Reader Writer Arena`)

var resourceOpeners = newSetFrom(`newInputStream newOutputStream newBufferedReader
	newBufferedWriter getResourceAsStream openStream openConnection getConnection
	createStatement prepareStatement prepareCall executeQuery newDirectoryStream
	ofConfined ofShared allocateDirect`)

var resourceOpenersQualified = map[string]map[string]bool{
	"open":   newSet("Files", "FileChannel", "SocketChannel", "ServerSocketChannel", "DatagramChannel", "AsynchronousFileChannel", "Selector", "AsynchronousSocketChannel"),
	"accept": newSet("ServerSocket", "ServerSocketChannel", "AsynchronousServerSocketChannel"),
	"lines":  newSet("Files"),
	"walk":   newSet("Files"),
	"list":   newSet("Files"),
}

func opensResource(method, receiver string) bool {
	if resourceOpeners[method] {
		return true
	}
	owners, ok := resourceOpenersQualified[method]
	if !ok {
		return false
	}
	if i := strings.LastIndexByte(receiver, '.'); i >= 0 {
		receiver = receiver[i+1:]
	}
	return owners[receiver]
}

var pooledExecutorWords = []string{"newFixedThreadPool", "newCachedThreadPool",
	"newSingleThreadExecutor", "newScheduledThreadPool",
	"newSingleThreadScheduledExecutor", "newWorkStealingPool", "ThreadPoolExecutor",
	"ForkJoinPool", "commonPool", "ScheduledThreadPoolExecutor",
	"NioEventLoopGroup", "DefaultEventExecutorGroup"}

var virtualThreadWords = []string{"ofVirtual", "startVirtualThread",
	"newVirtualThreadPerTaskExecutor", "StructuredTaskScope"}

var handlerAnnotations = newSetFrom(`RequestMapping GetMapping PostMapping PutMapping
	DeleteMapping PatchMapping Path GET POST PUT DELETE WebServlet MessageMapping
	KafkaListener RabbitListener JmsListener EventListener Scheduled Bean`)

var resilienceAnnotations = newSetFrom(`Retryable ConcurrencyLimit RateLimiter
	CircuitBreaker Bulkhead Timeout`)

var httpExchangeAnnotations = newSetFrom(`HttpExchange GetExchange PostExchange
	PutExchange DeleteExchange PatchExchange`)

var jakartaEE12Annotations = newSetFrom(`Query Find FindAll Save Delete Insert Update
	AttributeOverride TenantId TenantIdResolver MultiTenant IdGeneratorType
	UsingReflection Persists SubqueryProvider CTEProvider RunInTransaction
	ClaimAttributes RunAs DeclareRoles RolesAllowed PermitAll DenyAll`)

var handlerMethods = newSetFrom(`doGet doPost doPut doDelete service onMessage`)

var narrowScopeAnnotations = newSetFrom(`RequestScope SessionScope RefreshScope
	ApplicationScope`)

var formatFieldTypes = []string{"SimpleDateFormat", "NumberFormat", "DecimalFormat",
	"Calendar"}

var threadSafeCollections = newSetFrom(`ConcurrentHashMap ConcurrentLinkedQueue
	ConcurrentLinkedDeque ConcurrentSkipListMap ConcurrentSkipListSet
	CopyOnWriteArrayList CopyOnWriteArraySet LinkedBlockingQueue ArrayBlockingQueue
	PriorityBlockingQueue LinkedBlockingDeque DelayQueue SynchronousQueue`)

var staticCollAdds = newSetFrom(`add addAll put putAll offer push addFirst addLast
	insertElementAt addElement incrementAndGet addAndGet`)

var staticCollRemoves = newSetFrom(`remove removeAll clear removeIf poll pop
	removeFirst removeLast retainAll trimToSize removeElement decrementAndGet`)

var frameworkAnnotations = newSetFrom(`Test BeforeEach AfterEach BeforeAll AfterAll
	ParameterizedTest RepeatedTest Before After BeforeClass AfterClass Benchmark
	Setup TearDown Autowired Inject Resource PostConstruct PreDestroy Bean
	Component Service Repository Controller RestController Configuration Provides
	Subscribe JsonCreator JsonProperty Override`)

var broadExceptions = newSetFrom(`Exception Throwable RuntimeException Error`)

var sqlPatterns = [][2]string{
	{"select", ""}, {"insert", "into"}, {"update", ""}, {"delete", "from"},
	{"create", "table"}, {"drop", "table"}, {"alter", "table"},
	{"merge", "into"},
}

func sqlSearch(s string) bool {
	lo := strings.ToLower(s)
	for _, p := range sqlPatterns {
		kw, follow := p[0], p[1]
		for from := 0; from < len(lo); {
			i := strings.Index(lo[from:], kw)
			if i < 0 {
				break
			}
			i += from
			from = i + 1
			if i > 0 {
				if r, _ := utf8.DecodeLastRuneInString(s[:i]); isWordRune(r) {
					continue
				}
			}
			j := i + len(kw)
			if j >= len(lo) || !isPySpaceByte(lo[j]) {
				continue
			}
			j++
			if follow == "" {
				return true
			}
			if strings.HasPrefix(lo[j:], follow) {
				return true
			}
		}
	}
	return false
}

func isPySpaceByte(b byte) bool {
	switch b {
	case ' ', '\t', '\n', '\r', '\v', '\f', 0x1c, 0x1d, 0x1e:
		return true
	}
	return b >= 0x80
}

var collectionHeads = []string{"List", "ArrayList", "LinkedList", "Map",
	"HashMap", "TreeMap", "Set", "HashSet", "TreeSet", "Collection", "Iterator",
	"Iterable", "Comparable", "Comparator", "Class", "Optional", "Future",
	"CompletableFuture", "Callable", "Enumeration", "Queue", "Deque", "Stream"}

func rawTypeCountBounded(s string) int {
	if len(s) > 20000 {
		s = s[:20000]
	}
	return rawTypeCount(s)
}

func rawTypeCount(s string) int {
	n := 0
	for _, head := range collectionHeads {
		for from := 0; from < len(s); {
			i := strings.Index(s[from:], head)
			if i < 0 {
				break
			}
			i += from
			from = i + 1
			if i > 0 {
				if r, _ := utf8.DecodeLastRuneInString(s[:i]); isWordRune(r) {
					continue
				}
			}
			j := i + len(head)

			k := skipSpace(s, j)
			if k == j {
				continue
			}

			if k >= len(s) {
				continue
			}
			c := s[k]
			if !(c == '_' || c == '$' || (c >= 'a' && c <= 'z') ||
				(c >= 'A' && c <= 'Z')) {
				continue
			}

			m := k + 1
			for m < len(s) {
				if isWordByte(s[m]) {
					m++
					continue
				}
				if s[m] < 0x80 {
					break
				}
				r, sz := utf8.DecodeRuneInString(s[m:])
				if !isWordRune(r) {
					break
				}
				m += sz
			}

			p := skipSpace(s, m)
			if p >= len(s) {
				continue
			}
			switch s[p] {
			case '=', ';', ',', ')':
				n++
			}
		}
	}
	return n
}

func skipSpace(s string, i int) int {
	for i < len(s) {
		switch s[i] {
		case ' ', '\t', '\n', '\r', '\f', '\v':
			i++
		default:
			return i
		}
	}
	return i
}

var jdkPackageRoots = newSetFrom(`java javax jdk sun com.sun jakarta`)

var jdkTypes = newSetFrom(`System Math String StringBuilder StringBuffer Object
	Objects Integer Long Double Float Short Byte Character Boolean Number Class
	Enum Record Void Thread Runnable Runtime Process ProcessBuilder ThreadLocal
	ScopedValue Arrays Collections List ArrayList LinkedList Map HashMap TreeMap
	LinkedHashMap ConcurrentHashMap Set HashSet TreeSet LinkedHashSet Collection
	Iterator Iterable Queue Deque ArrayDeque PriorityQueue Optional OptionalInt
	Stream IntStream LongStream DoubleStream Collectors StreamSupport Comparator
	Executors ExecutorService Executor ScheduledExecutorService Future
	CompletableFuture CompletionStage ForkJoinPool ForkJoinTask CountDownLatch
	Semaphore CyclicBarrier Phaser Exchanger TimeUnit AtomicInteger AtomicLong
	AtomicBoolean AtomicReference AtomicIntegerArray AtomicLongArray LongAdder
	DoubleAdder LongAccumulator ReentrantLock ReentrantReadWriteLock StampedLock
	Condition LockSupport VarHandle MethodHandle MethodHandles MethodType Unsafe
	Files Paths Path File FileSystem FileSystems Channels ByteBuffer CharBuffer
	IntBuffer LongBuffer ByteOrder Charset StandardCharsets StandardOpenOption
	Pattern Matcher Random SecureRandom UUID Base64 BitSet Date Calendar Instant
	Duration Period LocalDate LocalDateTime LocalTime ZonedDateTime OffsetDateTime
	ZoneId ZoneOffset DateTimeFormatter Clock BigInteger BigDecimal MathContext
	RoundingMode Exception RuntimeException Error Throwable
	IllegalArgumentException IllegalStateException NullPointerException
	IndexOutOfBoundsException UnsupportedOperationException IOException
	UncheckedIOException InterruptedException ClassNotFoundException
	NoSuchMethodException ReflectiveOperationException SecurityException Logger
	LogManager Level Handler Arena Linker MemorySegment MemoryLayout
	SymbolLookup ValueLayout FunctionDescriptor StructuredTaskScope ServiceLoader
	ClassLoader Module ModuleLayer Proxy Array Field Method Constructor Modifier
	AccessibleObject Parameter Instrumentation`)

var jdkMethods = newSetFrom(`toString equals hashCode getClass clone finalize
	notify notifyAll name ordinal values valueOf compareTo length isEmpty charAt
	indexOf lastIndexOf trim strip startsWith endsWith substring toLowerCase
	toUpperCase concat replace split join chars codePoints println print printf
	format append setLength setCharAt reverse iterator hasNext next stream forEach
	spliterator printStackTrace getMessage getLocalizedMessage getCause
	getStackTrace`)

var xxeEntryBases = newSetFrom(`newDocumentBuilder newSAXParser newXMLReader
	createXMLStreamReader createSAXParser`)

var zipCtorPrefixes = []string{"new Zip", "new Jar"}

var boxValueOfTypes = newSetFrom(`Integer Long Double Float Short Byte Character
	Boolean`)
var boxUnboxBases = newSetFrom(`intValue longValue doubleValue floatValue
	booleanValue shortValue byteValue charValue`)
var setAccessibleBases = newSetFrom(`setAccessible trySetAccessible privateLookupIn`)
var ffmArenaBases = newSetFrom(`ofConfined ofShared ofAuto global allocateFrom
	allocate reinterpret ofAddress`)
var ffmDowncallBases = newSetFrom(`nativeLinker downcallHandle upcallStub
	libraryLookup loaderLookup invokeExact`)
var unsafeBases = newSetFrom(`getUnsafe allocateMemory reallocateMemory freeMemory
	objectFieldOffset staticFieldOffset arrayBaseOffset copyMemory setMemory
	putOrderedObject putOrderedLong allocateDirect fullFence acquireFence
	releaseFence loadLoadFence storeStoreFence`)
var atomicBases = newSetFrom(`compareAndSet weakCompareAndSet getAndSet
	incrementAndGet decrementAndGet getAndIncrement getAndDecrement getAndAdd
	addAndGet updateAndGet accumulateAndGet lazySet compareAndExchange getAcquire
	setRelease getPlain setOpaque`)
var waitBases = newSetFrom(`wait notify notifyAll await join sleep onSpinWait park
	awaitTermination`)
var closeBases = newSetFrom(`close closeQuietly shutdown shutdownNow dispose free`)
var regexMethodBases = newSetFrom(`matches replaceAll replaceFirst split`)
var optionalBases = newSetFrom(`ofNullable orElse orElseGet orElseThrow isPresent
	ifPresent ifPresentOrElse`)
var queryCallBases = newSetFrom(`executeQuery executeUpdate executeBatch
	prepareStatement prepareCall createQuery createNativeQuery getResultList
	getSingleResult findAll findById`)

var javaReqReceivers = newSet("request", "req", "httpRequest", "servletRequest")

var javaInputKinds = map[string]string{
	"getParameter": "query", "getParameterMap": "query",
	"getParameterValues": "query", "getHeader": "header", "getHeaders": "header",
	"getCookies": "cookie", "getPart": "form", "getParts": "form",
	"getInputStream": "body", "getReader": "body",
}

var authMarkers = []string{"auth", "security", "login", "jwt", "token",
	"isauthenticated", "hasrole"}

const secretMinLen = 12

var secretRe = regexp.MustCompile(`(?i)(api[_-]?key|apikey|secret|password|passwd|pwd|token|bearer|access[_-]?key|private[_-]?key|client[_-]?secret|auth[_-]?token|jwt|credential|smtp[_-]?pass|db[_-]?pass|sk_live|rk_live|pk_live|ghp_|xoxb-|AKIA)`)

var ioRe = regexp.MustCompile(`\.(?:read|write|flush|send|receive|connect|accept|execute|executeQuery|executeUpdate|newInputStream|newOutputStream|transferTo|copy)\s*\(`)

var sleepRe = regexp.MustCompile(`(?:\.(?:sleep|await|join|wait|park|awaitTermination|get)\s*\(|Thread\.sleep)`)

func hasGeneratedAnno(s string) bool {
	for from := 0; from < len(s); {
		i := strings.Index(s[from:], "@")
		if i < 0 {
			return false
		}
		i += from
		from = i + 1
		if strings.HasPrefix(s[i+1:], "javax.annotation.Generated") {
			j := i + 1 + len("javax.annotation.Generated")
			if wordBoundaryOK(s, i, j) {
				return true
			}
			continue
		}
		if strings.HasPrefix(s[i+1:], "Generated") {
			j := i + 1 + len("Generated")
			if wordBoundaryOK(s, i, j) {
				return true
			}
		}
	}
	return false
}

func findModuleImports(text string) [][2]any {
	var out [][2]any
	it := newPyLines(text)
	for i := 0; ; i++ {
		line, ok := it.next()
		if !ok {
			break
		}
		t := cgLStrip(line)
		if !strings.HasPrefix(t, "import") {
			continue
		}
		rest := strings.TrimLeft(t[6:], " \t")
		if !strings.HasPrefix(rest, "module") {
			continue
		}
		rest = strings.TrimLeft(rest[6:], " \t")
		j := 0
		for j < len(rest) && (isWordByte(rest[j]) || rest[j] == '.') {
			j++
		}
		if j == 0 {
			continue
		}
		name := rest[:j]
		rest = strings.TrimRight(rest[j:], " \t")
		if !strings.HasSuffix(rest, ";") {
			continue
		}
		out = append(out, [2]any{name, i + 1})
	}
	return out
}

var manifestPatterns = [][2]string{
	{"pom.xml", `<maven\.compiler\.release>\s*(\d+)`},
	{"pom.xml", `<maven\.compiler\.source>\s*(\d+)`},
	{"pom.xml", `<release>\s*(\d+)\s*</release>`},
	{"pom.xml", `<source>\s*(\d+)\s*</source>`},
	{"pom.xml", `<java\.version>\s*(?:1\.)?(\d+)`},
	{"build.gradle", `sourceCompatibility\s*=?\s*['"]?(?:1\.)?(\d+)`},
	{"build.gradle", `JavaVersion\.VERSION_(?:1_)?(\d+)`},
	{"build.gradle", `languageVersion.*?JavaLanguageVersion\.of\((\d+)\)`},
	{"build.gradle.kts", `JavaVersion\.VERSION_(?:1_)?(\d+)`},
	{"build.gradle.kts", `JavaLanguageVersion\.of\((\d+)\)`},
}

var magicStrings = func() map[string]bool {
	m := map[string]bool{"": true, "0x0": true, "0x1": true, "0xff": true,
		"0xFF": true, "0.0": true, "1.0": true, "-1": true}
	for _, v := range []string{"0", "1", "2", "-1", "10", "100", "1000", "8",
		"16", "32", "64", "128", "256", "512", "1024", "255", "65535", "4096",
		"24", "60", "365", "7", "12", "3", "4", "6"} {
		m[v] = true
	}
	return m
}()

var numLiteralRe = regexp.MustCompile(`^[-+]?(?:0[xXbBoO][0-9a-fA-F_]+|[\d_]+(?:\.[\d_]*)?(?:[eE][-+]?\d+)?)[uUlLfFdD]*$`)

func isMagicNum(txt string) bool {
	if magicStrings[txt] {
		return false
	}
	return numLiteralRe.MatchString(txt)
}

func simpleType(text string) string {
	t := strings.TrimSpace(text)
	if i := strings.IndexByte(t, '<'); i >= 0 {
		t = t[:i]
	}
	if i := strings.IndexByte(t, '['); i >= 0 {
		t = t[:i]
	}
	t = strings.TrimSpace(t)
	if i := strings.LastIndexByte(t, '.'); i >= 0 {
		t = t[i+1:]
	}
	return t
}

func lastSegment(s string) string {
	if i := strings.LastIndexByte(s, '.'); i >= 0 {
		return s[i+1:]
	}
	return s
}

func firstSegment(s string) string {
	if before, _, ok := strings.Cut(s, "."); ok {
		return before
	}
	return s
}

func (x *xctx) onCall(node tsNode, st *bstats, loopDepth, nest int32) {
	st.s.NCalls++
	if loopDepth > 0 {
		st.s.CallInLoop++
	}
	line := int32(node.startRow()) + 1
	kind := x.jk.names[node.kindID()]

	if kind == "object_creation_expression" {
		ty := node.childByFieldName(fType)
		var tname string
		if ty.ok() {
			tname = simpleType(x.txt(ty))
		}
		if tname == "" {
			return
		}
		st.addCall("new "+tname, line, boolI32(loopDepth > 0))
		if strings.HasPrefix(tname, "Zip") || strings.HasPrefix(tname, "Jar") {
			st.s.NZipRead++
		}
		if loopDepth > 0 {
			st.s.AllocInLoop++
			if boxValueOfTypes[tname] {
				st.s.NBoxingInLoop++
			}
			if tname == "StringBuilder" || tname == "StringBuffer" {
				st.s.ConcatInLoop++
			}
		}

		if tname == "BigDecimal" {
			args := node.childByFieldName(fArguments)
			if args.ok() && args.namedChildCount() > 0 {
				first := args.namedChild(0)
				ft := x.jk.names[first.kindID()]
				if ft == "decimal_floating_point_literal" || ft == "identifier" {
					st.s.NBigDecimalFromDouble++
				}
			}
		}
		if resourceTypes[tname] {
			if loopDepth > 0 {
				st.s.IOInLoop++
			} else {
				st.s.NResourceOpen++
			}
		}
		if tname == "Thread" {
			st.s.NThreadAlloc++
		}
		x.loopCounters("new "+tname, st, loopDepth)
		return
	}

	if kind == "method_reference" {

		nkids := int(node.childCount())
		var lastKid, firstKid tsNode
		kept := 0
		for i := range nkids {
			c := node.child(i)
			if !c.ok() || x.jk.names[c.kindID()] == "::" {
				continue
			}
			if kept == 0 {
				firstKid = c
			}
			lastKid = c
			kept++
		}
		if kept == 0 {
			return
		}
		mref := strings.TrimSpace(x.txt(lastKid))
		qual := ""
		if kept > 1 {
			qual = strings.TrimSpace(x.txt(firstKid))
		}
		if mref == "new" {
			st.addCall("new "+simpleType(qual), line, boolI32(loopDepth > 0))
		} else {
			full := mref
			if qual != "" && len(qual) <= 80 {
				full = qual + "." + mref
			}
			st.addCall(clipStr(full, 200), line, boolI32(loopDepth > 0))
		}
		return
	}

	nm := node.childByFieldName(fName)
	if !nm.ok() {
		st.calls = append(st.calls, callRec{"", line, 1})
		if loopDepth > 0 {
			st.calls[len(st.calls)-1].inLoop = 1
		}
		return
	}
	base := strings.TrimSpace(x.txt(nm))
	full := base
	obj := node.childByFieldName(fObject)
	recv := ""
	if obj.ok() {
		recv = strings.TrimSpace(x.txt(obj))
		if qualifierNodes[x.jk.names[obj.kindID()]] && len(recv) <= 80 &&
			!strings.ContainsRune(recv, '\n') {
			full = recv + "." + base
		}
		recv = clipStr(recv, 120)
	}
	b := lastSegment(full)

	switch {
	case b == "exec" && (strings.Contains(full, "Runtime") ||
		strings.Contains(recv, "Runtime")):
		st.s.NRuntimeExec++
	case b == "start" && strings.Contains(recv, "ProcessBuilder"):
		st.s.NRuntimeExec++
	}
	switch b {
	case "printStackTrace":
		st.s.NPrintStacktrace++
	case "getBytes", "toString":
		if strings.Contains(full, "String") {
			st.s.NDefaultCharset++
		}
	case "parseInt", "parseLong", "parseDouble":
		switch firstSegment(full) {
		case "Integer", "Long", "Double":
			st.s.NParseNoRadix++
		}
	case "equals":
		if loopDepth > 0 {
			st.s.NEqualsInLoop++
		}
	case "getInstance":
		if strings.Contains(full, "Random") && strings.HasPrefix(full, "Random") {
			st.s.NWeakRandom++
		}
	case "setSoTimeout", "setConnectTimeout", "setReadTimeout":
		st.s.NTimeoutSet++
	case "newFixedThreadPool", "newCachedThreadPool", "newSingleThreadExecutor",
		"newWorkStealingPool":
		st.s.NExecutorCreate++
	case "submit", "execute":
		if loopDepth > 0 {
			st.s.NSubmitInLoop++
		}
	case "get":
		if strings.Contains(full, "Future") {
			st.s.NFutureGet++
		}
	case "wait", "notify", "notifyAll":
		st.s.NMonitorCall++
	case "intern":
		st.s.NStringIntern++
	case "createStatement", "prepareCall":
		st.s.NRawStatement++
	case "readObject", "readUnshared":
		st.s.NReadObject++
	case "loadLibrary", "load":
		if strings.Contains(full, "System") {
			st.s.NLoadLibrary++
		}
	}
	if full == "Math.random" || full == "Random.nextInt" || full == "Random.nextLong" {
		st.s.NWeakRandom++
	}
	switch {
	case b == "notify":
		st.s.NNotifySingle++
	case b == "run" && obj.ok() && x.jk.names[obj.kindID()] != "this":
		st.s.NRunCalledDirectly++
	}
	switch {
	case strings.HasPrefix(b, "add") && (strings.Contains(b, "Listener") ||
		strings.Contains(b, "Handler")):
		st.s.NListenerAdd++
	case strings.HasPrefix(b, "remove") && (strings.Contains(b, "Listener") ||
		strings.Contains(b, "Handler")):
		st.s.NListenerRemove++
	}
	switch b {
	case "parseExpression", "eval", "evaluate", "evaluateExpression":
		st.s.NSpelEval++
	}
	if javaReqReceivers[recv] {
		if kind2, ok := javaInputKinds[base]; ok {
			st.inputSites = append(st.inputSites,
				inputSite{clipStr(full, 120), x.str.intern(kind2), line,
					boolI32(loopDepth > 0)})
		}
	}
	if base == "sendRedirect" {
		st.s.NRedirect++
	}
	if xxeEntryBases[base] {
		st.s.NXXEParser++
	}
	for _, p := range zipCtorPrefixes {
		if strings.HasPrefix(full, p) {
			st.s.NZipRead++
			break
		}
	}
	{
		fl := strings.ToLower(full)
		for _, m := range authMarkers {
			if strings.Contains(fl, m) {
				st.s.NAuthCall++
				break
			}
		}
	}
	st.addCall(clipStr(full, 200), line, boolI32(loopDepth > 0))

	switch {
	case base == "stream":
		st.s.NStreams++
	case base == "parallelStream":
		st.s.NParallelStreams++
		st.s.NStreams++
	case base == "parallel":
		st.s.NParallelStreams++
	case base == "collect" || strings.HasPrefix(full, "Collectors."):
		st.s.NCollectors++
	case base == "valueOf" && boxValueOfTypes[firstSegment(full)]:
		st.s.NBoxingSites++
		if loopDepth > 0 {
			st.s.NBoxingInLoop++
		}
	case boxUnboxBases[base]:
		st.s.NBoxingSites++
		if loopDepth > 0 {
			st.s.NBoxingInLoop++
		}
	case setAccessibleBases[base]:
		st.s.NSetAccessible++
	case (base == "load" || base == "loadLibrary") &&
		(strings.HasPrefix(full, "System.") || strings.HasPrefix(full, "Runtime.")):
		st.s.NNativeCalls++
	case ffmArenaBases[base]:
		if strings.HasPrefix(full, "Arena.") || strings.HasPrefix(full, "MemorySegment.") ||
			strings.HasPrefix(full, "SegmentAllocator.") {
			st.s.NFFMArena++
		}
	case ffmDowncallBases[base]:
		st.s.NFFMDowncall++
	case unsafeBases[base]:
		st.s.NUnsafeCalls++
	case atomicBases[base]:
		st.s.NAtomicOps++
	case waitBases[base]:
		st.s.NWaitCalls++
	case closeBases[base]:
		st.s.NCloseCalls++
	case opensResource(base, receiverOf(full)):
		st.s.NResourceOpen++
		if loopDepth > 0 {
			st.s.IOInLoop++
		}
	case base == "compile" && strings.HasPrefix(full, "Pattern."):
		st.s.NRegexCompile++
		if loopDepth > 0 {
			st.s.RegexInLoop++
		}
	case regexMethodBases[base]:
		st.s.NRegexCompile++
		if loopDepth > 0 {
			st.s.RegexInLoop++
		}
	case optionalBases[base] || ((base == "of" || base == "empty") &&
		strings.HasPrefix(full, "Optional.")):
		st.s.NOptionalOps++
	case queryCallBases[base]:
		st.s.NQueryCalls++
		if loopDepth > 0 {
			st.s.QueryInLoop++
		}
	case (base == "ofPattern" || base == "getInstance") &&
		(strings.HasPrefix(full, "DateTimeFormatter.") ||
			strings.HasPrefix(full, "Calendar.") ||
			strings.HasPrefix(full, "NumberFormat.") ||
			strings.HasPrefix(full, "DateFormat.")):
		st.s.NDatefmtOps++
	case base == "withInitial" || strings.HasPrefix(full, "ThreadLocal."):
		st.s.NThreadlocalOps++
	}

	x.loopCounters(full, st, loopDepth)
}

func receiverOf(full string) string {
	if i := strings.LastIndexByte(full, '.'); i >= 0 {
		return full[:i]
	}
	return ""
}

func (x *xctx) loopCounters(name string, st *bstats, loopDepth int32) {
	if loopDepth == 0 {
		return
	}
	base := lastSegment(name)
	for _, nc := range loopCallCounters {
		if nc[0] == base || nc[0] == name {
			switch nc[1] {
			case "query_in_loop":
				st.s.QueryInLoop++
			case "regex_in_loop":
				st.s.RegexInLoop++
			case "n_datefmt_ops":
				st.s.NDatefmtOps++
			case "n_format_in_loop":
				st.s.NFormatInLoop++
			}
		}
	}
}

func boolI32(b bool) int32 {
	if b {
		return 1
	}
	return 0
}

func (x *xctx) onString(node tsNode, text string, st *bstats, loopDepth int32) {
	if x.jk.names[node.kindID()] == "character_literal" {
		return
	}
	val := strings.Trim(text, "\"'")
	if len([]rune(val)) >= secretMinLen && !strings.Contains(val, " ") &&
		secretRe.MatchString(val) {
		st.secrets = append(st.secrets, secretRec{clipStr(val, 200),
			int32(node.startRow()) + 1})
	}
	if x.jk.names[node.kindID()] == "string_literal" && strings.HasPrefix(text, `"""`) {
		st.s.NModernIdioms++
	}
	if sqlSearch(text) {
		parent := node.parent()
		if parent.ok() && x.jk.names[parent.kindID()] == "binary_expression" {
			st.s.NQueryCalls++
		}
		if loopDepth > 0 {
			st.s.QueryInLoop++
		}
	}

	parent := node.parent()
	if parent.ok() && x.jk.names[parent.kindID()] == "argument_list" {
		call := parent.parent()
		if call.ok() && x.jk.names[call.kindID()] == "method_invocation" {
			nm := call.childByFieldName(fName)
			if nm.ok() {
				switch x.txt(nm) {
				case "compile", "matches", "replaceAll", "replaceFirst", "split":
					st.s.NRegexLit++
				}
			}
		}
	}
}

func (x *xctx) onNode(node tsNode, st *bstats, loopDepth, nest int32,
	ascii bool, astr string) {
	t := x.jk.names[node.kindID()]
	switch t {
	case "string_literal":
		if int(node.endByte())-int(node.startByte()) >= 3 &&
			bytesEq(node, x.src, `"""`) {
			st.s.NTextBlocks++
		}
		return
	case "identifier":

		if x.trackIdentifiers {
			st.events = append(st.events, event{kind: evIdent, line: 0,
				s1: "", f1: int32(node.startByte()), f2: int32(node.endByte())})
		}
		return
	case "binary_expression":
		x.onBinary(node, st, loopDepth)
		return
	case "unary_expression":
		// The old body selected a single non-comment child and switched on
		// its name with no cases -- no state was ever written.  Keep the
		// case so the shape of onNode is unchanged; nothing to count.
		return
	case "assignment_expression":
		x.onAssign(node, st, loopDepth)
		return
	case "cast_expression":
		ty := node.childByFieldName(fType)
		if ty.ok() && x.jk.names[ty.kindID()] == "generic_type" {
			st.s.NUncheckedCasts++
		}
		return
	case "lambda_expression":
		st.s.NLambda++
		return
	case "update_expression":
		base := ""
		for i := 0; i < node.namedChildCount(); i++ {
			k := node.namedChild(i)
			if x.jk.names[k.kindID()] != "comment" {
				base = lastSegment(strings.TrimSpace(x.txt(k)))
				break
			}
		}
		st.events = append(st.events, event{kind: evUpdate, s1: base})
		return
	case "return_statement":
		if kids := node.namedChild(0); kids.ok() && x.jk.names[kids.kindID()] == "null_literal" {
			st.s.NNullReturns++
		}

		p := node.parent()
		if p.ok() && x.jk.names[p.kindID()] == "block" {
			if pp := p.parent(); pp.ok() {
				switch x.jk.names[pp.kindID()] {
				case "if_statement", "for_statement", "while_statement",
					"switch_expression":
					st.s.NEarlyReturns++
				}
			}
		}
		return
	case "break_statement", "continue_statement":
		if node.namedChildCount() > 0 {
			st.s.NGotos++
		}
		return
	case "object_creation_expression":
		x.onNewExpr(node, st, loopDepth)
		return
	case "synchronized_statement":
		if loopDepth > 0 {
			st.s.LockInLoop++
		}
		x.pushSync(node, st, loopDepth)
		return
	case "method_invocation":
		if loopDepth > 0 {
			nm := node.childByFieldName(fName)
			if nm.ok() {
				switch x.txt(nm) {
				case "lock", "tryLock", "lockInterruptibly":
					st.s.LockInLoop++
				}
			}
		} else if obj := node.childByFieldName(fObject); obj.ok() &&
			x.txt(obj) == "super" {

			st.s.NSuperCalls++
		}
		x.pushMethodInv(node, st, loopDepth)
		return
	case "switch_expression", "switch_statement":
		if strings.Contains(clipStr(x.txt(node), 2000), "->") {
			st.s.NModernIdioms++
		}
		return
	case "instanceof_expression":
		if node.childByFieldName(fName).ok() {
			st.s.NModernIdioms++
		}
		return
	case "resource", "catch_clause", "throw_statement", "if_statement":
		switch t {
		case "resource":
			x.pushResource(node, st)
		case "catch_clause":
			x.pushCatch(node, st, loopDepth)
		case "throw_statement":
			x.pushThrow(node, st, loopDepth)
		default:
			if isDoubleChecked(node, x) {
				st.events = append(st.events, event{kind: evIfDCL,
					line: int32(node.startRow()) + 1})
			}
		}
	}
}

func bytesEq(n tsNode, src []byte, lit string) bool {
	s, e := int(n.startByte()), int(n.startByte())+len(lit)
	if e > len(src) {
		return false
	}
	return string(src[s:e]) == lit
}

func eachNamedKid(n tsNode) iter.Seq[tsNode] {
	return func(yield func(tsNode) bool) {
		c := n.namedChildCount()
		for i := range c {
			if !yield(n.namedChild(i)) {
				return
			}
		}
	}
}

func (x *xctx) onBinary(node tsNode, st *bstats, loopDepth int32) {
	op := fieldChild(node, "operator")
	if !op.ok() {
		return
	}
	o := x.txt(op)
	switch o {
	case "&&", "||":
		st.s.NLogical++
	case "==", "!=", "<", ">", "<=", ">=":
		st.s.NCmp++
		right := node.childByFieldName(fRight)
		left := node.childByFieldName(fLeft)
		if (right.ok() && x.jk.names[right.kindID()] == "null_literal") ||
			(left.ok() && x.jk.names[left.kindID()] == "null_literal") {
			st.s.NNullCheck++
		}

		if right.ok() && left.ok() {
			pairs := [][2]tsNode{{left, right}, {right, left}}
			for _, pr := range pairs {
				if x.jk.names[pr[0].kindID()] == "method_invocation" {
					nm := pr[0].childByFieldName(fName)
					_ = nm
				}
			}
		}
		if (o == "==" || o == "!=") && right.ok() && left.ok() {
			litTypes := []string{"decimal_integer_literal",
				"decimal_floating_point_literal", "null_literal", "string_literal"}
			rt := x.jk.names[right.kindID()]
			lt := x.jk.names[left.kindID()]
			if !containsStr(litTypes, rt) && !containsStr(litTypes, lt) {
				st.s.NRefEq++
			}
		}
	case "&", "|", "^":
		st.s.NBitop++
	case "<<", ">>", ">>>":
		st.s.NShift++
	case "+":
		if hasStringOperand(node, x) {
			st.s.NStringConcat++
			if loopDepth > 0 {
				st.s.ConcatInLoop++
			}
		} else {
			st.s.NArith++
		}
	case "-":
		st.s.NArith++
	case "*", "/", "%":
		st.s.NArith++

		par := node.parent()
		if par.ok() && x.jk.names[par.kindID()] == "variable_declarator" {
			ty := par.childByFieldName(fType)
			if !ty.ok() && par.parent().ok() {
				ty = par.parent().childByFieldName(fType)
			}
			if ty.ok() && strings.HasPrefix(cgLStrip(x.txt(ty)), "long") {
				st.s.NNarrowCalc++
			}
		}
	}
}

func containsStr(list []string, s string) bool {
	return slices.Contains(list, s)
}

func hasStringOperand(node tsNode, x *xctx) bool {
	for _, f := range [2]tsFieldID{fLeft, fRight} {
		c := node.childByFieldName(f)
		if !c.ok() {
			continue
		}
		if x.jk.names[c.kindID()] == "string_literal" {
			return true
		}
		if x.jk.names[c.kindID()] == "binary_expression" && hasStringOperand(c, x) {
			return true
		}
	}
	return false
}

func fieldChild(node tsNode, field string) tsNode {
	n := node.childCount()
	for i := range n {
		if node.fieldNameIs(i, field) {
			return node.child(i)
		}
	}
	return tsNode{}
}

func (x *xctx) onAssign(node tsNode, st *bstats, loopDepth int32) {
	op := fieldChild(node, "operator")
	opText := ""
	if op.ok() {
		opText = x.txt(op)
	}
	if op.ok() && opText != "=" {
		st.s.NCompoundAssgn++
		if opText == "+=" && hasStringOperand(node, x) {
			st.s.NStringConcat++
			if loopDepth > 0 {
				st.s.ConcatInLoop++
			}
		}
	}
	left := node.childByFieldName(fLeft)
	if left.ok() && x.jk.names[left.kindID()] == "field_access" {
		obj := left.childByFieldName(fObject)
		ot := ""
		if obj.ok() {
			ot = x.txt(obj)
		}
		if ot != "" && ot != "this" {

			st.s.NStaticWriteCtor++
		}
	}
	lt := ""
	if left.ok() {
		lt = strings.TrimSpace(x.txt(left))
	}
	st.events = append(st.events, event{kind: evAssign, line: loopDepth,
		s1: lastSegment(lt), s2: opText})
}

func (x *xctx) onNewExpr(node tsNode, st *bstats, loopDepth int32) {
	p := node.parent()
	if p.ok() {
		pt := x.jk.names[p.kindID()]
		if pt == "return_statement" {
			st.s.NEscapingAllocs++
		} else if pt == "assignment_expression" {
			l := p.childByFieldName(fLeft)
			if l.ok() && x.jk.names[l.kindID()] == "field_access" {
				st.s.NEscapingAllocs++
			}
		}
		if pt == "expression_statement" {

			ty := node.childByFieldName(fType)
			tname := ""
			if ty.ok() {
				tname = simpleType(x.txt(ty))
			}
			if strings.Contains(tname, "Exception") || strings.Contains(tname, "Error") ||
				strings.Contains(tname, "Throwable") {
				st.s.NDeadException++
			}
		}
	}
	ty := node.childByFieldName(fType)
	tname := ""
	if ty.ok() {
		tname = simpleType(x.txt(ty))
	}
	var inTry int32
	if x.inTryResources(node) {
		inTry = 1
	}
	st.events = append(st.events, event{kind: evObjCreate,
		line: int32(node.startRow()) + 1, depth: loopDepth, f1: inTry,
		s1: tname})
}

func (x *xctx) pushSync(node tsNode, st *bstats, loopDepth int32) {
	target := ""
	cnt := int(node.namedChildCount())
	for i := range cnt {
		c := node.namedChild(i)
		if x.jk.names[c.kindID()] == "parenthesized_expression" {
			target = clipStr(strings.Trim(x.txt(c), "() \t\n"), 80)
			break
		}
	}
	region := node.childByFieldName(fBody)
	var f1, f2, f3, f4, f5 int32
	if region.ok() {
		f1, f2, f3, f4, f5 = x.regionFlags(region)
	}
	sp, ep := node.startRow(), node.endRow()
	st.events = append(st.events, event{kind: evSync,
		line: int32(sp) + 1, endLine: int32(ep) + 1, depth: loopDepth,
		f1: f1, f2: f2, f3: f3, f4: f4, f5: f5, s1: target})
}

func (x *xctx) pushMethodInv(node tsNode, st *bstats, loopDepth int32) {
	nm := node.childByFieldName(fName)
	if !nm.ok() {
		return
	}
	mname := x.txt(nm)
	recv := ""
	obj := node.childByFieldName(fObject)
	if obj.ok() && qualifierNodes[x.jk.names[obj.kindID()]] {
		recv = clipStr(strings.TrimSpace(x.txt(obj)), 80)
	}
	var f1, f2, f3, f4, f5 int32
	if mname == "lock" || mname == "lockInterruptibly" || mname == "tryLock" {
		if region := x.enclosingRegion(node); region.ok() {
			f1, f2, f3, f4, f5 = x.regionFlags(region)
		}
	}
	var inTry, inSync int32
	if x.inTryResources(node) {
		inTry = 1
	}
	if x.inSynchronized(node) {
		inSync = 1
	}
	st.events = append(st.events, event{kind: evMethodInv,
		line: int32(node.startRow()) + 1, depth: loopDepth,
		f1: inTry, f2: inSync, f3: f1, f4: f2, f5: f3, f6: f4, f7: f5,
		s1: mname, s2: recv})
}

func (x *xctx) pushResource(node tsNode, st *bstats) {
	tn := node.childByFieldName(fType)
	nm := node.childByFieldName(fName)
	val := node.childByFieldName(fValue)
	var t, n, v string
	if tn.ok() {
		t = x.txt(tn)
	}
	if nm.ok() {
		n = x.txt(nm)
	}
	if val.ok() {
		v = x.txt(val)
	}
	st.events = append(st.events, event{kind: evResource,
		line: int32(node.startRow()) + 1,
		s1:   clipStr(n, 80), s2: clipStr(t, 80), s3: clipStr(v, 120)})
}

func (x *xctx) pushCatch(node tsNode, st *bstats, loopDepth int32) {
	cb := node.childByFieldName(fBody)
	ctxt := ""
	empty := 0
	if cb.ok() {
		ctxt = x.txt(cb)
		if cb.namedChildCount() == 0 {
			empty = 1
		}
	}
	rethrow := boolI32(strings.Contains(ctxt, "throw "))
	logs := boolI32(strings.Contains(strings.ToLower(ctxt), "log") ||
		strings.Contains(ctxt, "printStackTrace"))
	restores := boolI32(strings.Contains(ctxt, "interrupt"))
	var types []string
	for c := range eachNamedKid(node) {
		if x.jk.names[c.kindID()] != "catch_formal_parameter" {
			continue
		}
		for ct := range eachNamedKid(c) {
			if x.jk.names[ct.kindID()] != "catch_type" {
				continue
			}
			for tt := range eachNamedKid(ct) {
				types = append(types, simpleType(x.txt(tt)))
			}
		}
	}
	st.events = append(st.events, event{kind: evCatch,
		line: int32(node.startRow()) + 1, depth: loopDepth,
		f1: int32(empty), f2: rethrow, f3: logs, f4: restores,
		s1: strings.Join(types, "\x00")})
}

func (x *xctx) pushThrow(node tsNode, st *bstats, loopDepth int32) {
	tn := ""
	if first := node.namedChild(0); first.ok() &&
		x.jk.names[first.kindID()] == "object_creation_expression" {
		ty := first.childByFieldName(fType)
		if ty.ok() {
			tn = simpleType(x.txt(ty))
		}
	}
	st.events = append(st.events, event{kind: evThrow,
		line: int32(node.startRow()) + 1, depth: loopDepth, s1: tn})
}

func (x *xctx) regionFlags(region tsNode) (int32, int32, int32, int32, int32) {
	txt := x.txt(region)
	var nCall, nAlloc int32
	walkPre(region, func(n tsNode) bool {
		switch x.jk.names[n.kindID()] {
		case "method_invocation":
			nCall++
		case "object_creation_expression", "array_creation_expression":
			nAlloc++
		}
		return true
	})
	var io, slp, sloc int32
	if ioRe.MatchString(txt) {
		io = 1
	}
	if sleepRe.MatchString(txt) {
		slp = 1
	}
	it := newPyLines(txt)
	for {
		l, ok := it.next()
		if !ok {
			break
		}
		if cgStrip(l) != "" {
			sloc++
		}
	}
	return io, slp, nAlloc, nCall, sloc
}

func (x *xctx) enclosingRegion(node tsNode) tsNode {
	stmt := node
	for stmt.ok() {
		p := stmt.parent()
		if !p.ok() {
			return tsNode{}
		}
		if x.jk.names[p.kindID()] == "block" {
			break
		}
		stmt = p
	}
	if !stmt.ok() {
		return tsNode{}
	}
	nxt := stmt.nextNamedSibling()
	if nxt.ok() {
		switch x.jk.names[nxt.kindID()] {
		case "try_statement", "try_with_resources_statement":
			if b := nxt.childByFieldName(fBody); b.ok() {
				return b
			}
			return nxt
		}
	}
	return stmt.parent()
}

func (x *xctx) ancestorTypes(node tsNode, stop tsNode, want string) bool {
	cur := node.parent()
	for cur.ok() && (!stop.ok() || !cur.sameAs(stop)) {
		if x.jk.names[cur.kindID()] == want {
			return true
		}
		cur = cur.parent()
	}
	return false
}

func isDoubleChecked(node tsNode, x *xctx) bool {
	cond := node.childByFieldName(fCondition)
	if !cond.ok() || !strings.Contains(x.txt(cond), "null") {
		return false
	}
	cons := node.childByFieldName(fConsequence)
	if !cons.ok() {
		return false
	}
	found := false
	walkPre(cons, func(n tsNode) bool {
		if x.jk.names[n.kindID()] != "synchronized_statement" {
			return true
		}
		walkPre(n, func(m tsNode) bool {
			if x.jk.names[m.kindID()] == "if_statement" && !m.sameAs(node) {
				ic := m.childByFieldName(fCondition)
				if ic.ok() && strings.Contains(x.txt(ic), "null") {
					found = true
					return false
				}
			}
			return true
		})
		return !found
	})
	return found
}

func init() {
	queries[0].run = qReflectionFrontier
	queries[1].run = qDeserializationReach
	queries[2].run = qResourceOpenNeverClosed
	queries[3].run = qLockOrderInversion
	queries[4].run = qLockHeldAcrossIO
	queries[5].run = qVTPinningFrontier
	queries[6].run = qThreadlocalLeakOnPooled
	queries[7].run = qSharedMutableStatics
	queries[8].run = qExceptionContractDrift
	queries[9].run = qNPlusOne
	queries[10].run = qSqlConcatSurface
	queries[11].run = qFalseSharingAndEscape
	queries[12].run = qParallelStreamHazard
	queries[13].run = qDeadCode
	queries[14].run = qNativeSurfaceReachable
	queries[15].run = qEqualsHashcodeMismatch
	queries[16].run = qThreadSleepInLock
	queries[17].run = qDoubleCheckedLocking
	queries[18].run = qStringConcatInLoop
	queries[19].run = qExecutorWithoutShutdown
	queries[20].run = qSubmitInLoop
	queries[21].run = qNullReturnIgnore
	queries[22].run = qStaticMutableState
	queries[23].run = qWeakRandom
	queries[24].run = qWeakRandomSurface
	queries[25].run = qOpenRedirectSurface
	queries[26].run = qHardcodedSecrets
	queries[27].run = qXXEParserSurface
	queries[28].run = qZipSlipSurface
	queries[29].run = qUnauthenticatedInputSurface
	queries[30].run = qOverriddenNotAnnotated
	queries[31].run = qHierarchyDepth
	queries[32].run = qDIBottleneck
	queries[33].run = qOverloadDensity
	queries[34].run = qIfaceImplRatio
	queries[35].run = qPackageCycle
	queries[36].run = qAnnotationCoupling
	queries[37].run = qAbstractFanout
	queries[38].run = qLayerViolations
	queries[39].run = qEmptyCatchByFanin
}

func qReflectionFrontier(g *Graph, mod string, lim int) ([]string, [][]any) {
	cols := []string{"name", "owner", "hops_from_api", "reflect_ops",
		"set_accessible", "deser_ops", "jni", "fan_in", "public_", "at"}
	type acc struct {
		hops int32
		s    *Sym
	}
	best := map[int32]*acc{}
	for _, r := range g.Reach {
		root := &g.Sym[r.Root-1]
		if !(root.getFlag(fHandler) == 1 || root.getFlag(fEntrypoint) == 1 ||
			(root.getFlag(fPublic) == 1 && root.FanIn == 0)) || !isEntryKind(root) {
			continue
		}
		s := &g.Sym[r.Sym-1]
		if s.NReflection == 0 && s.NSetAccessible == 0 {
			continue
		}
		f := &g.Files[s.FileID-1]
		if f.IsTest != 0 || !likeMatch(g.modName(s.ModuleID), mod) {
			continue
		}
		e := best[s.ID]
		if e == nil {
			e = &acc{s: s, hops: math.MaxInt32}
			best[s.ID] = e
		}
		if r.Depth < e.hops {
			e.hops = r.Depth
		}
	}

	rows := make([][]any, 0, len(best))
	for i := range g.Sym {
		e, ok := best[g.Sym[i].ID]
		if !ok {
			continue
		}
		s := e.s
		rows = append(rows, []any{g.Str.get(s.Name), g.Str.get(s.OwnerType),
			int(e.hops), int(s.NReflection), int(s.NSetAccessible),
			int(s.NSerialization), int(s.NJNI), int(s.FanIn), int(s.getFlag(fPublic)),
			g.at(s.FileID, s.LineStart)})
	}
	sortRows(rows, sortKey{col: 2, asc: true}, sortKey{col: 4, asc: false},
		sortKey{col: 3, asc: false})
	return cols, limitRows(rows, lim)
}

func qDeserializationReach(g *Graph, mod string, lim int) ([]string, [][]any) {
	cols := []string{"name", "owner", "hops_from_api", "deser_ops",
		"reflect_ops", "sinks", "serial_types_no_uid", "fan_in", "at"}
	noUID := map[int32]int32{}
	for i := range g.Sym {
		s := &g.Sym[i]
		if s.getFlag(fSerializable) == 1 && s.getFlag(fHasSerialUID) == 0 {
			noUID[s.ModuleID]++
		}
	}

	sinkOf := map[int32][]string{}
	sinkSeen := map[int32]map[uint32]bool{}
	best := map[int32]*Sym{}
	hops := map[int32]int32{}
	for _, r := range g.Reach {
		root := &g.Sym[r.Root-1]
		if !(root.getFlag(fHandler) == 1 || root.getFlag(fEntrypoint) == 1 ||
			(root.getFlag(fPublic) == 1 && root.FanIn == 0)) || !isEntryKind(root) {
			continue
		}
		s := &g.Sym[r.Sym-1]
		if s.NSerialization == 0 {
			continue
		}
		f := &g.Files[s.FileID-1]
		if f.IsTest != 0 || !likeMatch(g.modName(s.ModuleID), mod) {
			continue
		}
		if d, ok := hops[s.ID]; !ok || r.Depth < d {
			best[s.ID] = s
			hops[s.ID] = r.Depth
		}
	}
	for i := range g.Hazards {
		h := &g.Hazards[i]
		if g.Str.get(h.Cat) != "serialization" {
			continue
		}
		seen := sinkSeen[h.SymID]
		if seen == nil {
			seen = map[uint32]bool{}
			sinkSeen[h.SymID] = seen
		}
		if !seen[h.Pat] {
			seen[h.Pat] = true
			sinkOf[h.SymID] = append(sinkOf[h.SymID], g.Str.get(h.Pat))
		}
	}
	for id := range sinkOf {
		sort.Strings(sinkOf[id])
	}
	rows := make([][]any, 0, len(best))
	for i := range g.Sym {
		s := &g.Sym[i]
		if _, ok := best[s.ID]; !ok {
			continue
		}
		var sinks any
		if p := sinkOf[s.ID]; len(p) > 0 {
			sinks = strings.Join(p, ",")
		}
		rows = append(rows, []any{g.Str.get(s.Name), g.Str.get(s.OwnerType),
			int(hops[s.ID]), int(s.NSerialization), int(s.NReflection), sinks,
			int(noUID[s.ModuleID]), int(s.FanIn), g.at(s.FileID, s.LineStart)})
	}
	sortRows(rows, sortKey{col: 2, asc: true}, sortKey{col: 3, asc: false})
	return cols, limitRows(rows, lim)
}

func qResourceOpenNeverClosed(g *Graph, mod string, lim int) ([]string, [][]any) {
	cols := []string{"name", "owner", "opens", "opens_in_loop", "in_twr",
		"closes", "finalizers", "return_type", "types", "callers_that_close",
		"on_open_path", "fan_in", "at"}
	type grp struct {
		opens, inLoop, twr int32
		firstLine          int32
		types              *concatDistinct
		closers            map[int32]bool
		closerEdges        int32
	}
	groups := map[int32]*grp{}
	var order []int32

	for _, r := range g.Res {
		if r.InTryResources != 0 {
			continue
		}
		s := &g.Sym[r.SymID-1]
		f := &g.Files[r.FileID-1]
		if f.IsTest != 0 || !likeMatch(g.modName(s.ModuleID), mod) {
			continue
		}
		gp := groups[s.ID]
		if gp == nil {
			gp = &grp{types: newConcat(), firstLine: r.Line,
				closers: map[int32]bool{}}
			groups[s.ID] = gp
			order = append(order, s.ID)
		}
		gp.opens++
		gp.inLoop += r.InLoop
		gp.twr += r.InTryResources
		if r.Line < gp.firstLine {
			gp.firstLine = r.Line
		}
		gp.types.addStr(g.Str.get(r.Type))
	}
	if len(groups) == 0 {
		return cols, nil
	}

	for i := range g.Edges {
		e := &g.Edges[i]
		gp := groups[e.Callee]
		if gp == nil {
			continue
		}
		c := &g.Sym[e.Caller-1]

		if c.NCloseCalls > 0 || c.NTryResources > 0 {
			gp.closers[e.Caller] = true
			gp.closerEdges++
		}
	}

	seedSeen := make(map[int32]bool, len(groups)*2)
	seeds := make([]int32, 0, len(groups)*2)
	for i := range g.Res {
		if g.Res[i].InTryResources != 0 {
			continue
		}
		id := g.Res[i].SymID
		if !seedSeen[id] {
			seedSeen[id] = true
			seeds = append(seeds, id)
		}
	}
	down := downDepths(g, seeds, 3)
	sort.SliceStable(order, func(x, y int) bool { return order[x] < order[y] })
	rows := make([][]any, 0, len(groups))
	for _, id := range order {
		gp := groups[id]
		s := &g.Sym[id-1]
		if s.NCloseCalls != 0 || gp.closerEdges != 0 {
			continue
		}
		n := down[id]
		rows = append(rows, []any{g.Str.get(s.Name), g.Str.get(s.OwnerType),
			int(gp.opens), int(gp.inLoop), int(gp.twr), int(s.NCloseCalls),
			int(s.NFinalizers), g.Str.get(s.RetType), gp.types.String(),
			int(gp.closerEdges), int(n), int(s.FanIn),
			g.at(s.FileID, gp.firstLine)})
	}
	sortRows(rows, sortKey{col: 3, asc: false}, sortKey{col: 2, asc: false},
		sortKey{col: 11, asc: false})
	return cols, limitRows(rows, lim)
}

type lockPair struct {
	symID               int32
	first, second       uint32
	firstOrder, secondO int32
	fileID, line        int32
}

func lockPairs(g *Graph) []lockPair {
	bySym := map[int32][]*LockOp{}
	for i := range g.Locks {
		l := &g.Locks[i]
		if g.Str.get(l.Op) != "acquire" {
			continue
		}
		bySym[l.SymID] = append(bySym[l.SymID], l)
	}
	var out []lockPair
	for sym, ops := range bySym {
		for i := range ops {
			for j := i + 1; j < len(ops); j++ {
				a, b := ops[i], ops[j]
				if g.Str.get(a.LockName) == "" || g.Str.get(b.LockName) == "" {
					continue
				}
				if a.LockName == b.LockName {
					continue
				}
				out = append(out, lockPair{symID: sym, first: a.LockName,
					second: b.LockName, firstOrder: a.AcqOrder,
					secondO: b.AcqOrder, fileID: a.FileID, line: a.Line})
			}
		}
	}
	sort.Slice(out, func(a, b int) bool {
		if out[a].symID != out[b].symID {
			return out[a].symID < out[b].symID
		}
		return out[a].firstOrder < out[b].firstOrder
	})
	return out
}

func qLockOrderInversion(g *Graph, mod string, lim int) ([]string, [][]any) {
	cols := []string{"lock_1", "lock_2", "takes_1_then_2", "owner_a",
		"takes_2_then_1", "owner_b", "a_acquires", "b_acquires", "max_fan_in",
		"at_a", "at_b"}
	pairs := lockPairs(g)
	rows := [][]any{}
	for _, a := range pairs {
		sa := &g.Sym[a.symID-1]
		fa := &g.Files[a.fileID-1]
		if fa.IsTest != 0 || !likeMatch(g.modName(sa.ModuleID), mod) {
			continue
		}
		if g.Str.get(a.first) >= g.Str.get(a.second) {
			continue
		}
		for _, b := range pairs {
			if b.symID == a.symID || b.first != a.second || b.second != a.first {
				continue
			}
			sb := &g.Sym[b.symID-1]
			fb := &g.Files[b.fileID-1]
			if fb.IsTest != 0 {
				continue
			}
			rows = append(rows, []any{g.Str.get(a.first), g.Str.get(a.second),
				g.Str.get(sa.Name), g.Str.get(sa.OwnerType),
				g.Str.get(sb.Name), g.Str.get(sb.OwnerType),
				int(sa.NLockAcquire), int(sb.NLockAcquire),
				int(maxI32(sa.FanIn, sb.FanIn)),
				g.at(a.fileID, a.line), g.at(b.fileID, b.line)})
		}
	}
	sortRows(rows, sortKey{col: 8, asc: false})
	return cols, limitRows(rows, lim)
}

func qLockHeldAcrossIO(g *Graph, mod string, lim int) ([]string, [][]any) {
	cols := []string{"name", "owner", "lock_name", "kind", "io_", "sleeps",
		"allocs", "calls_out", "region", "in_loop", "waits", "fan_in",
		"hold_cost", "at"}
	rows := [][]any{}
	for i := range g.Locks {
		l := &g.Locks[i]
		if g.Str.get(l.Op) != "acquire" {
			continue
		}
		if l.HoldsIO != 1 && l.HoldsSleep != 1 && l.HoldsAlloc <= 2 {
			continue
		}
		s := &g.Sym[l.SymID-1]
		f := &g.Files[l.FileID-1]
		if f.IsTest != 0 || !likeMatch(g.modName(s.ModuleID), mod) {
			continue
		}
		cost := (l.HoldsIO*8 + l.HoldsSleep*10 + l.HoldsCall + l.HoldsAlloc) *
			(1 + l.InLoop*3)
		rows = append(rows, []any{g.Str.get(s.Name), g.Str.get(s.OwnerType),
			g.Str.get(l.LockName), g.Str.get(l.Kind), int(l.HoldsIO),
			int(l.HoldsSleep), int(l.HoldsAlloc), int(l.HoldsCall),
			int(l.RegionSloc), int(l.InLoop), int(s.NWaitCalls),
			int(s.FanIn), int(cost), g.at(l.FileID, l.Line)})
	}
	sortRows(rows, sortKey{col: 12, asc: false}, sortKey{col: 11, asc: false})
	return cols, limitRows(rows, lim)
}

func qVTPinningFrontier(g *Graph, mod string, lim int) ([]string, [][]any) {
	cols := []string{"vt_root", "root_owner", "pins_in", "owner", "hops",
		"jni_ops", "native_", "ffm_downcall", "ffm_arena", "unsafe_",
		"synchronized_not_a_finding", "at"}
	type acc struct {
		hops int32
		s    *Sym
	}
	best := map[[2]int32]*acc{}
	for _, r := range g.Reach {
		root := &g.Sym[r.Root-1]
		if root.getFlag(fVtRoot) != 1 {
			continue
		}
		s := &g.Sym[r.Sym-1]
		if s.NJNI == 0 && s.NNativeCalls == 0 && s.NFFMDowncall == 0 {
			continue
		}
		f := &g.Files[s.FileID-1]
		if f.IsTest != 0 || !likeMatch(g.modName(s.ModuleID), mod) {
			continue
		}
		k := [2]int32{root.ID, s.ID}
		e := best[k]
		if e == nil {
			e = &acc{s: s, hops: math.MaxInt32}
			best[k] = e
		}
		if r.Depth < e.hops {
			e.hops = r.Depth
		}
	}
	type pair struct {
		root int32
		e    *acc
	}
	ordered := make([]pair, 0, len(best))
	for k, e := range best {
		ordered = append(ordered, pair{k[0], e})
	}
	sort.Slice(ordered, func(a, b int) bool {
		x, y := best[[2]int32{ordered[a].root, ordered[b].e.s.ID}],
			best[[2]int32{ordered[a].root, ordered[b].e.s.ID}]
		_ = x
		_ = y
		return ordered[a].root < ordered[b].root
	})
	rows := make([][]any, 0, len(ordered))
	for _, p := range ordered {
		s := p.e.s
		root := &g.Sym[p.root-1]
		rows = append(rows, []any{g.Str.get(root.Name),
			g.Str.get(root.OwnerType), g.Str.get(s.Name),
			g.Str.get(s.OwnerType), int(p.e.hops), int(s.NJNI),
			int(s.NNativeCalls), int(s.NFFMDowncall), int(s.NFFMArena),
			int(s.NUnsafeCalls), int(s.NSyncBlocks),
			g.at(s.FileID, s.LineStart)})
	}
	sortRows(rows, sortKey{col: 4, asc: true}, sortKey{col: 7, asc: false},
		sortKey{col: 5, asc: false})
	return cols, limitRows(rows, lim)
}

func qThreadlocalLeakOnPooled(g *Graph, mod string, lim int) ([]string, [][]any) {
	cols := []string{"name", "owner", "hops_from_pool", "tl_ops", "tl_removes",
		"trys", "finallys", "tl_fields", "fan_in", "at"}
	var seeds []int32
	for i := range g.Sym {
		if g.Sym[i].getFlag(fPoolRoot) == 1 {
			seeds = append(seeds, g.Sym[i].ID)
		}
	}
	down := downClosure(g, seeds, 5, 0)
	tlFields := map[string]int32{}
	for i := range g.Fields {
		fd := &g.Fields[i]
		if !strings.Contains(g.Str.get(fd.Type), "ThreadLocal") {
			continue
		}
		t := &g.Sym[fd.SymID-1]
		tlFields[g.Str.get(t.Name)]++
	}
	rows := [][]any{}
	for id, hops := range down {
		s := &g.Sym[id-1]
		if s.NThreadlocalOps == 0 || s.NThreadlocalRem != 0 {
			continue
		}
		f := &g.Files[s.FileID-1]
		if f.IsTest != 0 || !likeMatch(g.modName(s.ModuleID), mod) {
			continue
		}
		rows = append(rows, []any{g.Str.get(s.Name), g.Str.get(s.OwnerType),
			int(hops), int(s.NThreadlocalOps), int(s.NThreadlocalRem),
			int(s.NTry), int(s.NFinally),
			int(tlFields[g.Str.get(s.OwnerType)]), int(s.FanIn),
			g.at(s.FileID, s.LineStart)})
	}
	sortRows(rows, sortKey{col: 2, asc: true}, sortKey{col: 3, asc: false})
	return cols, limitRows(rows, lim)
}

func qSharedMutableStatics(g *Graph, mod string, lim int) ([]string, [][]any) {
	cols := []string{"module_", "mutable_statics", "thread_starters",
		"pooled_starters", "virtual_starters", "lock_ops", "atomics",
		"volatile_reads", "static_writes", "names"}
	statics := map[int32]*concatDistinct{}
	statCount := map[int32]int32{}
	seenField := map[[2]int32]bool{}
	for i := range g.Fields {
		fd := &g.Fields[i]
		if fd.IsStatic != 1 || fd.IsConst != 0 {
			continue
		}
		ty := &g.Sym[fd.SymID-1]
		f := &g.Files[ty.FileID-1]
		if f.IsTest != 0 {
			continue
		}
		k := [2]int32{fd.SymID, fd.Ordinal}
		if seenField[k] {
			continue
		}
		seenField[k] = true
		statCount[ty.ModuleID]++
		c := statics[ty.ModuleID]
		if c == nil {
			c = newConcat()
			statics[ty.ModuleID] = c
		}
		c.addStr(suffixN(g.Str.get(fd.Name), 20))
	}
	type agg struct {
		thread, pooled, virt, locks, atomics, vol, writes int32
	}
	a := map[int32]*agg{}
	for i := range g.Sym {
		s := &g.Sym[i]
		e := a[s.ModuleID]
		if e == nil {
			e = &agg{}
			a[s.ModuleID] = e
		}
		e.thread += s.getFlag(fExecRoot)
		e.pooled += s.getFlag(fPoolRoot)
		e.virt += s.getFlag(fVtRoot)
		e.locks += s.NSyncBlocks + s.NLockAcquire
		e.atomics += s.NAtomicOps
		e.vol += s.NVolatileAccess
		e.writes += s.NStaticWrites
	}
	rows := [][]any{}
	for mid, n := range statCount {
		ag := a[mid]
		if ag == nil || ag.thread == 0 || ag.atomics != 0 {
			continue
		}
		m := &g.Mod[mid-1]
		if !likeMatch(g.Str.get(m.Name), mod) {
			continue
		}
		rows = append(rows, []any{g.Str.get(m.Name), int(n), int(ag.thread),
			int(ag.pooled), int(ag.virt), int(ag.locks), int(ag.atomics),
			int(ag.vol), int(ag.writes), statics[mid].String()})
	}
	sortRows(rows, sortKey{col: 1, asc: false}, sortKey{col: 2, asc: false})
	return cols, limitRows(rows, lim)
}

func qExceptionContractDrift(g *Graph, mod string, lim int) ([]string, [][]any) {
	cols := []string{"name", "owner", "broad_throws", "throws_declared",
		"catches", "broad_catches", "empty_catches", "rethrows", "null_returns",
		"optional_ops", "throws_", "fan_in", "drift", "at"}
	broad := map[int32]int32{}
	for i := range g.Excepts {
		e := &g.Excepts[i]
		if g.Str.get(e.Kind) == "throws" && e.IsBroad == 1 {
			broad[e.SymID]++
		}
	}
	rows := [][]any{}
	for i := range g.Sym {
		s := &g.Sym[i]
		if s.NCatchEmpty == 0 && s.NCatchBroad == 0 {
			continue
		}
		if s.NNullReturns == 0 && s.NCatchEmpty == 0 {
			continue
		}
		f := &g.Files[s.FileID-1]
		if f.IsTest != 0 || f.IsGen != 0 || !likeMatch(g.modName(s.ModuleID), mod) {
			continue
		}
		drift := (s.NCatchEmpty*10 + s.NCatchBroad*4 + s.NNullReturns*3) *
			(1 + minI32(s.FanIn, 20))
		rows = append(rows, []any{g.Str.get(s.Name), g.Str.get(s.OwnerType),
			int(broad[s.ID]), int(s.NThrowsDeclared), int(s.NCatch),
			int(s.NCatchBroad), int(s.NCatchEmpty), int(s.NCatchRethrow),
			int(s.NNullReturns), int(s.NOptionalOps), int(s.NThrowSites),
			int(s.FanIn), int(drift), g.at(s.FileID, s.LineStart)})
	}
	sortRows(rows, sortKey{col: 12, asc: false})
	return cols, limitRows(rows, lim)
}

func qNPlusOne(g *Graph, mod string, lim int) ([]string, [][]any) {
	cols := []string{"caller", "caller_owner", "loop_depth", "query_fn",
		"query_owner", "sql_ops", "query_calls", "own_loop", "edges_",
		"caller_fan_in", "handler", "query_fan_in", "at"}
	rows := [][]any{}
	for i := range g.Edges {
		e := &g.Edges[i]
		cal := &g.Sym[e.Caller-1]
		cle := &g.Sym[e.Callee-1]
		if cle.NSql == 0 && cle.NQueryCalls == 0 {
			continue
		}
		if cal.MaxLoopDepth == 0 || cal.CallInLoop == 0 {
			continue
		}
		f := &g.Files[cal.FileID-1]
		if f.IsTest != 0 || !likeMatch(g.modName(cal.ModuleID), mod) {
			continue
		}
		rows = append(rows, []any{g.Str.get(cal.Name),
			g.Str.get(cal.OwnerType), int(cal.MaxLoopDepth),
			g.Str.get(cle.Name), g.Str.get(cle.OwnerType), int(cle.NSql),
			int(cle.NQueryCalls), int(cle.QueryInLoop), int(e.NCalls),
			int(cal.FanIn), int(cal.getFlag(fHandler)), int(cle.FanIn),
			g.at(cal.FileID, cal.LineStart)})
	}
	sortRows(rows, sortKey{col: 2, asc: false}, sortKey{col: 6, asc: false},
		sortKey{col: 9, asc: false})
	return cols, limitRows(rows, lim)
}

func qSqlConcatSurface(g *Graph, mod string, lim int) ([]string, [][]any) {
	cols := []string{"name", "sink", "sql_hazards", "query_calls",
		"query_loops", "fan_in", "at"}
	rows := [][]any{}
	for i := range g.Hazards {
		h := &g.Hazards[i]
		if g.Str.get(h.Cat) != "sql" {
			continue
		}
		s := &g.Sym[h.SymID-1]
		if s.NQueryCalls == 0 {
			continue
		}
		f := &g.Files[s.FileID-1]
		if f.IsTest != 0 || !likeMatch(g.modName(s.ModuleID), mod) {
			continue
		}
		rows = append(rows, []any{g.Str.get(s.Name), g.Str.get(h.Pat),
			int(h.N), int(s.NQueryCalls), int(s.QueryInLoop), int(s.FanIn),
			g.at(s.FileID, s.LineStart)})
	}
	sortRows(rows, sortKey{col: 5, asc: false}, sortKey{col: 2, asc: false})
	return cols, limitRows(rows, lim)
}

func qFalseSharingAndEscape(g *Graph, mod string, lim int) ([]string, [][]any) {
	cols := []string{"type_", "kind", "mutable_fields", "primitive_fields",
		"has_contended", "atomic_ops", "volatile_access", "lock_acquires",
		"escaping_allocs", "alloc_loop", "hottest_method", "at"}
	type fld struct{ mutable, prim int32 }
	fields := map[int32]*fld{}
	seenOrd := map[[2]int32]bool{}
	prims := newSet("int", "long", "boolean", "short", "byte", "char", "float",
		"double")
	for i := range g.Fields {
		f := &g.Fields[i]
		if f.IsConst == 1 || f.IsStatic == 1 {
			continue
		}
		k := [2]int32{f.SymID, f.Ordinal}
		if !seenOrd[k] {
			seenOrd[k] = true
			e := fields[f.SymID]
			if e == nil {
				e = &fld{}
				fields[f.SymID] = e
			}
			e.mutable++
		}
		if prims[g.Str.get(f.Type)] {
			e := fields[f.SymID]
			if e == nil {
				e = &fld{}
				fields[f.SymID] = e
			}
			e.prim++
		}
	}
	type mth struct {
		atomic, vol, lock, esc, alloc, hottest int32
	}
	methods := map[int32]*mth{}
	for i := range g.Sym {
		s := &g.Sym[i]
		if s.ParentID < 0 {
			continue
		}
		e := methods[s.ParentID]
		if e == nil {
			e = &mth{}
			methods[s.ParentID] = e
		}
		e.atomic += s.NAtomicOps
		e.vol += s.NVolatileAccess
		e.lock += s.NLockAcquire
		e.esc += s.NEscapingAllocs
		e.alloc += s.AllocInLoop
		if s.FanIn > e.hottest {
			e.hottest = s.FanIn
		}
	}
	ai := g.buildAttrIndex()
	contended := newSet("Contended")
	rows := [][]any{}
	for i := range g.Sym {
		ty := &g.Sym[i]
		fd := fields[ty.ID]
		if fd == nil || fd.mutable < 2 {
			continue
		}
		f := &g.Files[ty.FileID-1]
		if f.IsTest != 0 || !likeMatch(g.modName(ty.ModuleID), mod) {
			continue
		}
		if len(g.attrsOf(&ai, ty.ID, contended)) > 0 {
			continue
		}
		m := methods[ty.ID]
		var a, v, l, e2, al, h int32
		if m != nil {
			a, v, l, e2, al, h = m.atomic, m.vol, m.lock, m.esc, m.alloc, m.hottest
		}
		if a == 0 && v == 0 && l == 0 && e2 == 0 {
			continue
		}
		rows = append(rows, []any{g.Str.get(ty.Name), g.kindOf(ty),
			int(fd.mutable), int(fd.prim), 0, int(a), int(v), int(l), int(e2),
			int(al), int(h), g.at(ty.FileID, ty.LineStart),
			a*3 + v*2 + e2 + al})
	}
	sortRows(rows, sortKey{col: 12, asc: false}, sortKey{col: 10, asc: false})
	for i := range rows {
		rows[i] = rows[i][:12]
	}
	return cols, limitRows(rows, lim)
}

func symbolQuery(g *Graph, mod string, lim int, skipGen bool,
	keep func(*Sym) bool,
	cols []string,
	project func(*Sym, *File) []any,
	order ...sortKey) ([]string, [][]any) {
	rows := [][]any{}
	for i := range g.Sym {
		s := &g.Sym[i]
		f := &g.Files[s.FileID-1]
		if f.IsTest != 0 {
			continue
		}
		if skipGen && f.IsGen != 0 {
			continue
		}
		if !likeMatch(g.modName(s.ModuleID), mod) {
			continue
		}
		if !keep(s) {
			continue
		}
		rows = append(rows, project(s, f))
	}
	sortRows(rows, order...)
	return cols, limitRows(rows, lim)
}

func qParallelStreamHazard(g *Graph, mod string, lim int) ([]string, [][]any) {
	return symbolQuery(g, mod, lim, false,
		func(s *Sym) bool { return s.NParallelStreams > 0 },
		[]string{"name", "owner", "parallel_", "streams", "locks", "synced",
			"io_ops", "static_writes", "fan_out", "at"},
		func(s *Sym, f *File) []any {
			return []any{g.Str.get(s.Name), g.Str.get(s.OwnerType),
				int(s.NParallelStreams), int(s.NStreams), int(s.NLockAcquire),
				int(s.NSyncBlocks), int(s.NIO), int(s.NStaticWrites),
				int(s.FanOut), g.at(s.FileID, s.LineStart),
				s.NIO + s.NLockAcquire + s.NSyncBlocks + s.NStaticWrites}
		},
		sortKey{col: 10, asc: false}, sortKey{col: 2, asc: false})
}

func qDeadCode(g *Graph, mod string, lim int) ([]string, [][]any) {
	return symbolQuery(g, mod, lim, true,
		func(s *Sym) bool {
			return s.FanIn == 0 && s.getFlag(fPublic) == 0 && s.getFlag(fTest) == 0 &&
				s.getFlag(fEntrypoint) == 0 && s.getFlag(fOverride) == 0 && s.getFlag(fAbstract) == 0 &&
				s.getFlag(fHTTPExchange) == 0 && kindsPlain[g.kindOf(s)] &&
				g.Str.get(s.Name) != "(anonymous)" &&
				g.Str.get(s.Name) != "<module>"
		},
		[]string{"name", "kind", "sloc", "cyclo", "ext_calls", "at"},
		func(s *Sym, f *File) []any {
			return []any{g.Str.get(s.Name), g.kindOf(s), int(s.Sloc),
				int(s.Cyclomatic), int(s.NExternalCalls),
				g.at(s.FileID, s.LineStart)}
		},
		sortKey{col: 2, asc: false})
}

func qNativeSurfaceReachable(g *Graph, mod string, lim int) ([]string, [][]any) {
	cols := []string{"name", "reached_from", "hops", "exec_calls",
		"deserializes", "loads_native", "raw_sql", "fan_in", "at"}
	rows := [][]any{}
	for _, r := range g.Reach {
		s := &g.Sym[r.Sym-1]
		entry := &g.Sym[r.Root-1]
		if entry.getFlag(fEntrypoint) != 1 && entry.getFlag(fPublic) != 1 && entry.getFlag(fHandler) != 1 {
			continue
		}
		if s.NRuntimeExec == 0 && s.NReadObject == 0 && s.NLoadLibrary == 0 &&
			s.NRawStatement == 0 {
			continue
		}
		if r.Depth == 0 {
			continue
		}
		f := &g.Files[s.FileID-1]
		ef := &g.Files[entry.FileID-1]
		if f.IsTest != 0 || ef.IsTest != 0 ||
			!likeMatch(g.modName(s.ModuleID), mod) {
			continue
		}
		rows = append(rows, []any{g.Str.get(s.Name), g.Str.get(entry.Name),
			int(r.Depth), int(s.NRuntimeExec), int(s.NReadObject),
			int(s.NLoadLibrary), int(s.NRawStatement), int(s.FanIn),
			g.at(s.FileID, s.LineStart)})
	}
	sortRows(rows, sortKey{col: 2, asc: true}, sortKey{col: 3, asc: false},
		sortKey{col: 4, asc: false}, sortKey{col: 7, asc: false})
	return cols, limitRows(rows, lim)
}

func qEqualsHashcodeMismatch(g *Graph, mod string, lim int) ([]string, [][]any) {
	cols := []string{"name", "kind", "has_equals", "has_hashcode", "sloc", "at"}
	eq := map[int32]int32{}
	hc := map[int32]int32{}
	for i := range g.Over {
		o := &g.Over[i]
		s := &g.Sym[o.SymID-1]
		switch g.Str.get(o.MethodName) {
		case "equals":
			eq[s.ParentID]++
		case "hashCode":
			hc[s.ParentID]++
		}
	}
	rows := [][]any{}
	for i := range g.Sym {
		s := &g.Sym[i]
		if s.Kind != kindClass && s.Kind != kindInterface {
			continue
		}
		f := &g.Files[s.FileID-1]
		if f.IsTest != 0 || !likeMatch(g.modName(s.ModuleID), mod) {
			continue
		}
		e, h := eq[s.ID], hc[s.ID]
		if !((e > 0 && h == 0) || (e == 0 && h > 0)) {
			continue
		}
		rows = append(rows, []any{g.Str.get(s.Name), g.kindOf(s),
			int(e), int(h), int(s.Sloc), g.at(s.FileID, s.LineStart)})
	}
	sortRows(rows, sortKey{col: 4, asc: false}, sortKey{col: 4, asc: false})
	sortRows(rows, sortKey{col: 2, asc: false}, sortKey{col: 3, asc: false},
		sortKey{col: 4, asc: false})
	return cols, limitRows(rows, lim)
}

func qThreadSleepInLock(g *Graph, mod string, lim int) ([]string, [][]any) {
	return symbolQuery(g, mod, lim, false,
		func(s *Sym) bool {
			return s.NSyncBlocks+s.NSyncMethods > 0 && s.NWaitCalls > 0
		},
		[]string{"name", "sync_blocks", "sync_methods", "lock_acquires",
			"wait_calls", "fan_in", "cyclo", "at"},
		func(s *Sym, f *File) []any {
			return []any{g.Str.get(s.Name), int(s.NSyncBlocks),
				int(s.NSyncMethods), int(s.NLockAcquire), int(s.NWaitCalls),
				int(s.FanIn), int(s.Cyclomatic), g.at(s.FileID, s.LineStart)}
		},
		sortKey{col: 4, asc: false}, sortKey{col: 5, asc: false})
}

func qDoubleCheckedLocking(g *Graph, mod string, lim int) ([]string, [][]any) {
	cols := []string{"name", "pattern", "sites", "sync_blocks",
		"volatile_access", "cyclo", "fan_in", "at"}
	rows := [][]any{}
	for i := range g.Hazards {
		h := &g.Hazards[i]
		if g.Str.get(h.Pat) != "double-checked-locking" {
			continue
		}
		s := &g.Sym[h.SymID-1]
		f := &g.Files[s.FileID-1]
		if f.IsTest != 0 || !likeMatch(g.modName(s.ModuleID), mod) {
			continue
		}
		rows = append(rows, []any{g.Str.get(s.Name), g.Str.get(h.Pat),
			int(h.N), int(s.NSyncBlocks), int(s.NVolatileAccess),
			int(s.Cyclomatic), int(s.FanIn), g.at(s.FileID, s.LineStart)})
	}
	sortRows(rows, sortKey{col: 6, asc: false}, sortKey{col: 2, asc: false})
	return cols, limitRows(rows, lim)
}

func qStringConcatInLoop(g *Graph, mod string, lim int) ([]string, [][]any) {
	return symbolQuery(g, mod, lim, false,
		func(s *Sym) bool { return s.ConcatInLoop > 0 },
		[]string{"name", "concat_sites", "concat_in_loop", "loops", "cyclo",
			"fan_in", "at"},
		func(s *Sym, f *File) []any {
			return []any{g.Str.get(s.Name), int(s.NStringConcat),
				int(s.ConcatInLoop), int(s.NLoops), int(s.Cyclomatic),
				int(s.FanIn), g.at(s.FileID, s.LineStart)}
		},
		sortKey{col: 2, asc: false}, sortKey{col: 3, asc: false})
}

func qExecutorWithoutShutdown(g *Graph, mod string, lim int) ([]string, [][]any) {
	return symbolQuery(g, mod, lim, false,
		func(s *Sym) bool { return s.NExecutorCreate > 0 && s.NCloseCalls == 0 },
		[]string{"name", "executors_created", "submits_in_loop", "future_gets",
			"close_calls", "is_pooled_executor_root", "fan_in", "at"},
		func(s *Sym, f *File) []any {
			return []any{g.Str.get(s.Name), int(s.NExecutorCreate),
				int(s.NSubmitInLoop), int(s.NFutureGet), int(s.NCloseCalls),
				int(s.getFlag(fPoolRoot)), int(s.FanIn), g.at(s.FileID, s.LineStart)}
		},
		sortKey{col: 1, asc: false}, sortKey{col: 6, asc: false})
}

func qSubmitInLoop(g *Graph, mod string, lim int) ([]string, [][]any) {
	return symbolQuery(g, mod, lim, false,
		func(s *Sym) bool { return s.NSubmitInLoop > 0 },
		[]string{"name", "submits_in_loop", "executors", "future_gets", "loops",
			"cyclo", "fan_in", "at"},
		func(s *Sym, f *File) []any {
			return []any{g.Str.get(s.Name), int(s.NSubmitInLoop),
				int(s.NExecutorCreate), int(s.NFutureGet), int(s.NLoops),
				int(s.Cyclomatic), int(s.FanIn), g.at(s.FileID, s.LineStart)}
		},
		sortKey{col: 1, asc: false}, sortKey{col: 6, asc: false})
}

func qNullReturnIgnore(g *Graph, mod string, lim int) ([]string, [][]any) {
	return symbolQuery(g, mod, lim, false,
		func(s *Sym) bool { return s.NNullReturns > 0 && s.FanIn > 5 },
		[]string{"name", "null_returns", "fan_in", "n_calls", "cyclo",
			"optional_ops", "at"},
		func(s *Sym, f *File) []any {
			return []any{g.Str.get(s.Name), int(s.NNullReturns),
				int(s.FanIn), int(s.NCalls), int(s.Cyclomatic),
				int(s.NOptionalOps), g.at(s.FileID, s.LineStart)}
		},
		sortKey{col: 2, asc: false}, sortKey{col: 1, asc: false})
}

func qStaticMutableState(g *Graph, mod string, lim int) ([]string, [][]any) {
	return symbolQuery(g, mod, lim, false,
		func(s *Sym) bool { return s.NStaticWrites > 0 && s.getFlag(fStatic) == 0 },
		[]string{"name", "static_writes", "is_static", "sync_blocks",
			"atomic_ops", "volatile_access", "fan_in", "cyclo", "at"},
		func(s *Sym, f *File) []any {
			return []any{g.Str.get(s.Name), int(s.NStaticWrites),
				int(s.getFlag(fStatic)), int(s.NSyncBlocks), int(s.NAtomicOps),
				int(s.NVolatileAccess), int(s.FanIn), int(s.Cyclomatic),
				g.at(s.FileID, s.LineStart)}
		},
		sortKey{col: 6, asc: false}, sortKey{col: 1, asc: false})
}

func qWeakRandom(g *Graph, mod string, lim int) ([]string, [][]any) {
	return symbolQuery(g, mod, lim, false,
		func(s *Sym) bool { return s.NWeakRandom > 0 },
		[]string{"name", "weak_random_calls", "loadLibrary_calls", "fan_in",
			"handler", "at"},
		func(s *Sym, f *File) []any {
			return []any{g.Str.get(s.Name), int(s.NWeakRandom),
				int(s.NLoadLibrary), int(s.FanIn), int(s.getFlag(fHandler)),
				g.at(s.FileID, s.LineStart)}
		},
		sortKey{col: 3, asc: false}, sortKey{col: 1, asc: false})
}

func qWeakRandomSurface(g *Graph, mod string, lim int) ([]string, [][]any) {
	cols := []string{"name", "random_sites", "random_calls", "fan_in", "at"}
	want := newSet("new Random", "Math.random")
	rows := [][]any{}
	for i := range g.Hazards {
		h := &g.Hazards[i]
		if !want[g.Str.get(h.Pat)] {
			continue
		}
		s := &g.Sym[h.SymID-1]
		f := &g.Files[s.FileID-1]
		if f.IsTest != 0 || !likeMatch(g.modName(s.ModuleID), mod) {
			continue
		}
		rows = append(rows, []any{g.Str.get(s.Name), int(h.N),
			int(s.NWeakRandom), int(s.FanIn), g.at(s.FileID, s.LineStart)})
	}
	sortRows(rows, sortKey{col: 3, asc: false}, sortKey{col: 1, asc: false})
	return cols, limitRows(rows, lim)
}

func qOpenRedirectSurface(g *Graph, mod string, lim int) ([]string, [][]any) {
	cols := []string{"name", "redirect_calls", "input_sites", "kinds",
		"fan_in", "at"}
	rows := [][]any{}
	for i := range g.Sym {
		s := &g.Sym[i]
		if s.NRedirect == 0 {
			continue
		}
		f := &g.Files[s.FileID-1]
		if f.IsTest != 0 || !likeMatch(g.modName(s.ModuleID), mod) {
			continue
		}
		ids := map[int32]bool{}
		kinds := newConcat()
		for j := range g.UISites {
			u := &g.UISites[j]
			if u.SymID == s.ID {
				ids[u.ID] = true
				kinds.addStr(g.Str.get(u.Kind))
			}
		}
		if len(ids) == 0 {
			continue
		}
		rows = append(rows, []any{g.Str.get(s.Name), int(s.NRedirect),
			int(len(ids)), kinds.String(), int(s.FanIn),
			g.at(s.FileID, s.LineStart)})
	}
	sortRows(rows, sortKey{col: 4, asc: false}, sortKey{col: 1, asc: false})
	return cols, limitRows(rows, lim)
}

func qHardcodedSecrets(g *Graph, mod string, lim int) ([]string, [][]any) {
	cols := []string{"name", "candidate", "line", "at"}
	rows := [][]any{}
	for i := range g.Secrets {
		sc := &g.Secrets[i]
		s := &g.Sym[sc.SymID-1]
		f := &g.Files[sc.FileID-1]
		if f.IsTest != 0 || !likeMatch(g.modName(s.ModuleID), mod) {
			continue
		}
		v := g.Str.get(sc.Value)
		if strings.HasPrefix(v, "/") || strings.Contains(v, "|") ||
			strings.Contains(v, "%") {
			continue
		}
		rows = append(rows, []any{g.Str.get(s.Name), v, int(sc.Line),
			g.at(sc.FileID, sc.Line)})
	}
	sortRows(rows, sortKey{col: 1, asc: false})
	return cols, limitRows(rows, lim)
}

func qXXEParserSurface(g *Graph, mod string, lim int) ([]string, [][]any) {
	return symbolQuery(g, mod, lim, false,
		func(s *Sym) bool { return s.NXXEParser > 0 },
		[]string{"name", "xml_parsers", "sloc", "at"},
		func(s *Sym, f *File) []any {
			return []any{g.Str.get(s.Name), int(s.NXXEParser), int(s.Sloc),
				g.at(s.FileID, s.LineStart)}
		},
		sortKey{col: 1, asc: false}, sortKey{col: 2, asc: false})
}

func qZipSlipSurface(g *Graph, mod string, lim int) ([]string, [][]any) {
	return symbolQuery(g, mod, lim, false,
		func(s *Sym) bool { return s.NZipRead > 0 },
		[]string{"name", "zip_access", "sloc", "at"},
		func(s *Sym, f *File) []any {
			return []any{g.Str.get(s.Name), int(s.NZipRead), int(s.Sloc),
				g.at(s.FileID, s.LineStart)}
		},
		sortKey{col: 1, asc: false}, sortKey{col: 2, asc: false})
}

func qUnauthenticatedInputSurface(g *Graph, mod string, lim int) ([]string, [][]any) {
	cols := []string{"name", "input_sites", "kinds", "at"}
	ai := g.buildAttrIndex()
	guard := newSet("PreAuthorize", "Secured", "RolesAllowed")
	rows := [][]any{}
	for i := range g.Sym {
		s := &g.Sym[i]
		if s.NAuthCall != 0 {
			continue
		}
		f := &g.Files[s.FileID-1]
		if f.IsTest != 0 || !likeMatch(g.modName(s.ModuleID), mod) {
			continue
		}
		ids := map[int32]bool{}
		kinds := newConcatSorted()
		for j := range g.UISites {
			u := &g.UISites[j]
			if u.SymID == s.ID {
				ids[u.ID] = true
				kinds.addStr(g.Str.get(u.Kind))
			}
		}
		if len(ids) == 0 {
			continue
		}
		guarded := false
		for _, at := range g.attrsOf(&ai, s.ID, nil) {
			n := g.Str.get(at.Name)
			if strings.Contains(n, "PreAuthorize") ||
				strings.Contains(n, "Secured") ||
				strings.Contains(n, "RolesAllowed") {
				guarded = true
				break
			}
		}
		_ = guard
		if guarded {
			continue
		}
		rows = append(rows, []any{g.Str.get(s.Name), int(len(ids)),
			kinds.String(), g.at(s.FileID, s.LineStart)})
	}
	sortRows(rows, sortKey{col: 1, asc: false}, sortKey{col: 3, asc: false})
	return cols, limitRows(rows, lim)
}

func qOverriddenNotAnnotated(g *Graph, mod string, lim int) ([]string, [][]any) {
	cols := []string{"name", "owner_type", "parent_type", "is_annotated",
		"fan_in", "cyclo", "at"}
	rows := [][]any{}
	for i := range g.Over {
		o := &g.Over[i]
		if o.IsAnnotated != 0 {
			continue
		}
		s := &g.Sym[o.SymID-1]
		f := &g.Files[o.FileID-1]
		if f.IsTest != 0 || !likeMatch(g.modName(s.ModuleID), mod) {
			continue
		}
		rows = append(rows, []any{g.Str.get(s.Name), g.Str.get(o.OwnerType),
			g.Str.get(o.ParentType), int(o.IsAnnotated), int(s.FanIn),
			int(s.Cyclomatic), g.at(s.FileID, s.LineStart)})
	}
	sortRows(rows, sortKey{col: 4, asc: false})
	return cols, limitRows(rows, lim)
}

func qHierarchyDepth(g *Graph, mod string, lim int) ([]string, [][]any) {
	cols := []string{"class_", "depth", "distinct_ancestors", "defs", "at"}
	type row struct {
		child int32
		anc   uint32
		depth int32
	}
	type edge struct{ parent uint32 }

	extends := map[int32][]edge{}
	for i := range g.TypeRel {
		t := &g.TypeRel[i]
		if g.Str.get(t.Kind) != "extends" {
			continue
		}
		extends[t.ChildID] = append(extends[t.ChildID], edge{t.ParentNam})
	}

	trip := map[[3]uint32]bool{}
	maxDepth := map[int32]int32{}
	ancs := map[int32]map[uint32]bool{}
	note := func(child int32, anc uint32, depth int32) {
		if depth > maxDepth[child] {
			maxDepth[child] = depth
		}
		m := ancs[child]
		if m == nil {
			m = map[uint32]bool{}
			ancs[child] = m
		}
		m[anc] = true
	}
	var frontier []row
	for i := range g.TypeRel {
		t := &g.TypeRel[i]
		if g.Str.get(t.Kind) != "extends" {
			continue
		}
		tk := [3]uint32{uint32(t.ChildID), t.ParentNam, 1}
		if trip[tk] {
			continue
		}
		trip[tk] = true
		note(t.ChildID, t.ParentNam, 1)
		frontier = append(frontier, row{t.ChildID, t.ParentNam, 1})
	}
	for d := int32(2); d <= 10 && len(frontier) > 0; d++ {
		var next []row
		for _, r := range frontier {

			for _, sc := range g.symByName(g.Str.get(r.anc), kindsClassOnly) {
				for _, e := range extends[sc.ID] {
					tk := [3]uint32{uint32(r.child), e.parent, uint32(d)}
					if trip[tk] {
						continue
					}
					trip[tk] = true
					note(r.child, e.parent, d)
					next = append(next, row{r.child, e.parent, d})
				}
			}
		}
		frontier = next
	}
	defs := map[int32]int32{}
	for i := range g.TypeRel {
		t := &g.TypeRel[i]
		if g.Str.get(t.Kind) == "extends" {
			defs[t.ChildID]++
		}
	}
	rows := [][]any{}
	for _, id := range g.scanOrder() {
		s := &g.Sym[id-1]
		if s.Kind != kindClass {
			continue
		}
		d, ok := maxDepth[id]
		if !ok {
			continue
		}
		f := &g.Files[s.FileID-1]
		if f.IsTest != 0 || !likeMatch(g.modName(s.ModuleID), mod) {
			continue
		}
		rows = append(rows, []any{g.Str.get(s.Name), int(d),
			int(len(ancs[id])), int(defs[id]), g.at(s.FileID, s.LineStart)})
	}
	sortRows(rows, sortKey{col: 1, asc: false}, sortKey{col: 2, asc: false})
	return cols, limitRows(rows, lim)
}

func qDIBottleneck(g *Graph, mod string, lim int) ([]string, [][]any) {
	cols := []string{"name", "kind", "annotations", "inbound_callers",
		"cyclo", "sloc", "at"}
	inbound := map[int32]map[int32]bool{}
	for i := range g.Edges {
		e := &g.Edges[i]
		callee := &g.Sym[e.Callee-1]
		if callee.ParentID < 0 {
			continue
		}
		m := inbound[callee.ParentID]
		if m == nil {
			m = map[int32]bool{}
			inbound[callee.ParentID] = m
		}
		m[e.Caller] = true
	}
	rows := [][]any{}
	for _, id := range g.scanOrder(kindClass, kindInterface) {
		s := &g.Sym[id-1]
		if s.NAnnotations == 0 || len(inbound[s.ID]) == 0 {
			continue
		}
		f := &g.Files[s.FileID-1]
		if f.IsTest != 0 || !likeMatch(g.modName(s.ModuleID), mod) {
			continue
		}
		rows = append(rows, []any{g.Str.get(s.Name), g.kindOf(s),
			int(s.NAnnotations), int(len(inbound[s.ID])), int(s.Cyclomatic),
			int(s.Sloc), g.at(s.FileID, s.LineStart)})
	}
	sortRows(rows, sortKey{col: 3, asc: false}, sortKey{col: 2, asc: false})
	return cols, limitRows(rows, lim)
}

func qOverloadDensity(g *Graph, mod string, lim int) ([]string, [][]any) {
	cols := []string{"owner", "name", "overloads", "total_defs", "sloc",
		"fan_in", "at"}
	type odKey struct {
		parent int32
		name   uint32
	}
	total := map[odKey]int32{}
	for i := range g.Sym {
		s := &g.Sym[i]
		if s.Kind != kindMethod {
			continue
		}
		total[odKey{s.ParentID, s.Name}]++
	}
	type acc struct {
		overloads, total, fanIn, minLine, minSloc int32
	}
	groups := map[odKey]*acc{}
	var order []odKey
	for _, id := range g.scanOrderModuleKind() {
		s := &g.Sym[id-1]
		if s.Kind != kindMethod || s.NOverloads == 0 {
			continue
		}
		f := &g.Files[s.FileID-1]
		if f.IsTest != 0 || !likeMatch(g.modName(s.ModuleID), mod) {
			continue
		}
		k := odKey{s.ParentID, s.Name}
		a := groups[k]
		if a == nil {
			a = &acc{minLine: s.LineStart, minSloc: s.Sloc,
				total: total[k]}
			groups[k] = a
			order = append(order, k)
		}
		if s.NOverloads > a.overloads {
			a.overloads = s.NOverloads
		}
		if s.FanIn > a.fanIn {
			a.fanIn = s.FanIn
		}
		if s.LineStart < a.minLine {
			a.minLine = s.LineStart
		}
		if s.Sloc < a.minSloc {
			a.minSloc = s.Sloc
		}
	}
	type odRow struct {
		row    []any
		parent int32
		name   string
	}
	sorted := make([]odRow, 0, len(order))
	for _, k := range order {
		a := groups[k]
		pc := &g.Sym[k.parent-1]

		at := ""
		for i := range g.Sym {
			s := &g.Sym[i]
			if s.ParentID == k.parent && s.Name == k.name {
				at = g.at(s.FileID, a.minLine)
				break
			}
		}
		sorted = append(sorted, odRow{[]any{g.Str.get(pc.Name), g.Str.get(k.name),
			int(a.overloads), int(a.total), int(a.minSloc), int(a.fanIn), at},
			k.parent, g.Str.get(k.name)})
	}
	sort.SliceStable(sorted, func(i, j int) bool {
		a, b := &sorted[i], &sorted[j]
		ai, bi := a.row[2].(int), b.row[2].(int)
		if ai != bi {
			return ai > bi
		}
		if a.parent != b.parent {
			return a.parent < b.parent
		}
		return a.name < b.name
	})
	rows := make([][]any, len(sorted))
	for i := range sorted {
		rows[i] = sorted[i].row
	}
	return cols, limitRows(rows, lim)
}

func qIfaceImplRatio(g *Graph, mod string, lim int) ([]string, [][]any) {
	cols := []string{"iface", "kind", "implementors", "overriders",
		"methods", "at"}
	overriders := map[uint32]int32{}
	for i := range g.Over {
		overriders[g.Over[i].ParentType]++
	}
	rows := [][]any{}
	for _, id := range g.scanOrder(kindClass, kindInterface) {
		s := &g.Sym[id-1]
		if s.NImplTargets == 0 {
			continue
		}
		f := &g.Files[s.FileID-1]
		if f.IsTest != 0 || !likeMatch(g.modName(s.ModuleID), mod) {
			continue
		}
		methods := int32(0)
		for j := range g.Sym {
			m := &g.Sym[j]
			if m.ParentID == s.ID && m.Kind == kindMethod {
				methods++
			}
		}
		rows = append(rows, []any{g.Str.get(s.Name), g.kindOf(s),
			int(s.NImplTargets), int(overriders[s.Name]), int(methods),
			g.at(s.FileID, s.LineStart)})
	}
	sortRows(rows, sortKey{col: 2, asc: false}, sortKey{col: 4, asc: false})
	return cols, limitRows(rows, lim)
}

func qPackageCycle(g *Graph, mod string, lim int) ([]string, [][]any) {
	cols := []string{"file_a", "file_b", "a_line", "b_line"}
	byTarget := map[int32][]int32{}
	for i := range g.Imports {
		im := &g.Imports[i]
		if im.TargetID < 0 {
			continue
		}
		byTarget[im.TargetID] = append(byTarget[im.TargetID], im.ID)
	}
	byID := map[int32]*Import{}
	for i := range g.Imports {
		byID[g.Imports[i].ID] = &g.Imports[i]
	}
	rows := [][]any{}
	for i := range g.Imports {
		ia := &g.Imports[i]
		if ia.TargetID < 0 || ia.FileID >= ia.TargetID {
			continue
		}
		fa := &g.Files[ia.FileID-1]
		if !likeMatch(fa.Path(g.Str), mod) {
			continue
		}
		for _, jbid := range byTarget[ia.FileID] {
			ib := byID[jbid]
			if ib.TargetID != ia.FileID {
				continue
			}
			fb := &g.Files[ib.FileID-1]
			rows = append(rows, []any{fa.Path(g.Str), fb.Path(g.Str), int(ia.Line),
				int(ib.Line)})
		}
	}
	sortRows(rows, sortKey{col: 0, asc: true}, sortKey{col: 1, asc: true})
	return cols, limitRows(rows, lim)
}

func qAnnotationCoupling(g *Graph, mod string, lim int) ([]string, [][]any) {
	cols := []string{"name", "kind", "annotations", "sloc", "per_kloc",
		"fan_in", "at"}
	rows := [][]any{}
	for i := range g.Sym {
		s := &g.Sym[i]
		if s.NAnnotations < 2 ||
			(s.Kind != kindClass && s.Kind != kindInterface) {
			continue
		}
		f := &g.Files[s.FileID-1]
		if f.IsTest != 0 || !likeMatch(g.modName(s.ModuleID), mod) {
			continue
		}
		var perKloc any
		if s.Sloc != 0 {
			perKloc = cut(1000.0 * float64(s.NAnnotations) / float64(s.Sloc))
		}
		rows = append(rows, []any{g.Str.get(s.Name), g.kindOf(s),
			int(s.NAnnotations), int(s.Sloc), perKloc, int(s.FanIn),
			g.at(s.FileID, s.LineStart)})
	}
	sortRows(rows, sortKey{col: 2, asc: false}, sortKey{col: 4, asc: false})
	return cols, limitRows(rows, lim)
}

func qAbstractFanout(g *Graph, mod string, lim int) ([]string, [][]any) {
	cols := []string{"parent", "method", "override_impls", "distinct_owners",
		"owners", "at_any"}
	type acc struct {
		n       int32
		owners  *concatDistinct
		minLine int32
		minFile int32
	}
	groups := map[[2]uint32]*acc{}
	var keys [][2]uint32
	for _, oi := range g.overrideOrder() {
		o := &g.Over[oi]
		f := &g.Files[o.FileID-1]
		if !likeMatch(g.Str.get(g.Mod[f.ModuleID-1].Name), mod) {
			continue
		}
		k := [2]uint32{o.ParentType, o.MethodName}
		e := groups[k]
		if e == nil {
			e = &acc{owners: newConcat(), minLine: o.Line, minFile: o.FileID}
			groups[k] = e
			keys = append(keys, k)
		}
		e.n++
		e.owners.add(o.OwnerType, g.Str.get(o.OwnerType))

		if o.Line < e.minLine {
			e.minLine, e.minFile = o.Line, o.FileID
		}
	}
	rows := make([][]any, 0, len(groups))
	for _, k := range keys {
		e := groups[k]
		rows = append(rows, []any{g.Str.get(k[0]), g.Str.get(k[1]),
			int(e.n), int(len(e.owners.out)), e.owners.String(),
			g.at(e.minFile, e.minLine)})
	}
	sortRows(rows, sortKey{col: 2, asc: false}, sortKey{col: 3, asc: false})
	return cols, limitRows(rows, lim)
}

func qLayerViolations(g *Graph, mod string, lim int) ([]string, [][]any) {
	cols := []string{"caller", "callee", "caller_method", "callee_method",
		"n_calls", "at"}
	isWeb := func(o string) bool {
		l := strings.ToLower(o)
		return strings.HasSuffix(l, "controller") ||
			strings.HasSuffix(l, "resource") ||
			strings.HasSuffix(l, "servlet") ||
			strings.HasSuffix(l, "action")
	}
	isData := func(o string) bool {
		l := strings.ToLower(o)
		return strings.HasSuffix(l, "dao") || strings.HasSuffix(l, "repository") ||
			strings.HasSuffix(l, "mapper") || strings.HasSuffix(l, "db")
	}
	rows := [][]any{}
	for i := range g.Edges {
		e := &g.Edges[i]
		cal := &g.Sym[e.Caller-1]
		cle := &g.Sym[e.Callee-1]
		if cal.ID == cle.ID {
			continue
		}
		f := &g.Files[cal.FileID-1]
		if f.IsTest != 0 || !likeMatch(g.modName(cal.ModuleID), mod) {
			continue
		}
		co, ce := g.Str.get(cal.OwnerType), g.Str.get(cle.OwnerType)
		if !isWeb(co) || !isData(ce) {
			continue
		}
		rows = append(rows, []any{co, ce, g.Str.get(cal.Name),
			g.Str.get(cle.Name), int(e.NCalls), g.at(cal.FileID, cal.LineStart)})
	}
	sortRows(rows, sortKey{col: 4, asc: false})
	return cols, limitRows(rows, lim)
}

func qEmptyCatchByFanin(g *Graph, mod string, lim int) ([]string, [][]any) {
	cols := []string{"path", "name", "caught", "line", "fan_in"}
	rows := [][]any{}
	for i := range g.Excepts {
		e := &g.Excepts[i]
		if g.Str.get(e.Kind) != "catch" || e.IsEmpty != 1 {
			continue
		}
		s := &g.Sym[e.SymID-1]
		f := &g.Files[e.FileID-1]
		if f.IsGen != 0 || !likeMatch(g.modName(s.ModuleID), mod) {
			continue
		}
		rows = append(rows, []any{f.Path(g.Str), g.Str.get(s.Name),
			g.Str.get(e.Type), int(e.Line), int(s.FanIn)})
	}
	sortRows(rows, sortKey{col: 4, asc: false})
	return cols, limitRows(rows, lim)
}

func init() {
	queries[40].run = qTryInLoop
	queries[41].run = qFilesStreamLeak
	queries[42].run = qBannedApiSurface
	queries[43].run = qLockOnBoxed
	queries[44].run = qStaticWriteInCtor
	queries[45].run = qMissingSuperCall
	queries[46].run = qDeadException
	queries[47].run = qReferenceEquality
	queries[48].run = qNarrowCalculation
	queries[49].run = qModernIdioms
	queries[50].run = qFlexConstructorPrologues
	queries[51].run = qResilienceAnnotations
	queries[52].run = qHTTPExchangeClients
	queries[53].run = qAPIVersionDrift
	queries[54].run = qJSpecifyViolations
	queries[55].run = qNotifyWithoutNotifyAll
	queries[56].run = qThreadRunNotStart
	queries[57].run = qBigDecimalFromDouble
	queries[58].run = qProxyBypassSelfInvocation
	queries[59].run = qTransactionalCheckedCommit
	queries[60].run = qPrototypeBeanIntoSingleton
	queries[61].run = qReturnedResourceNeverClosed
	queries[62].run = qLockAcquireWithoutRelease
	queries[63].run = qTransitiveBlockUnderLock
	queries[64].run = qWaitNotifyOutsideSync
	queries[65].run = qInterruptSwallowed
	queries[66].run = qSharedFormatFieldUse
	queries[67].run = qStringFormatInLoop
	queries[68].run = qCommonPoolFromEntry
	queries[69].run = qStaticWriteFromEntry
	queries[70].run = qListenerAddRemoveImbalance
	queries[71].run = qExpressionEvalFromInput
	queries[72].run = qVolatileCompoundUpdate
	queries[73].run = qManualThreadAllocation
	queries[74].run = qScheduledOverlapRisk
	queries[75].run = qEventListenerSyncBurden
	queries[76].run = qCacheEvictDrift
	queries[77].run = qPrivateProxyAnnotation
	queries[78].run = qStaticCollectionGrows
	queries[79].run = qSharedBeanMutableCollection
}

func qTryInLoop(g *Graph, mod string, lim int) ([]string, [][]any) {
	cols := []string{"path", "name", "handlers_in_loops", "any_broad", "fan_in"}
	type acc struct {
		n     int32
		broad int32
	}
	groups := map[int32]*acc{}
	for i := range g.Excepts {
		e := &g.Excepts[i]
		if g.Str.get(e.Kind) != "catch" || e.InLoop != 1 {
			continue
		}
		s := &g.Sym[e.SymID-1]
		f := &g.Files[e.FileID-1]
		if f.IsGen != 0 || !likeMatch(g.modName(s.ModuleID), mod) {
			continue
		}
		a := groups[s.ID]
		if a == nil {
			a = &acc{}
			groups[s.ID] = a
		}
		a.n++
		if e.IsBroad == 1 {
			a.broad = 1
		}
	}
	rows := [][]any{}
	for i := range g.Sym {
		s := &g.Sym[i]
		a, ok := groups[s.ID]
		if !ok {
			continue
		}
		f := &g.Files[s.FileID-1]
		rows = append(rows, []any{f.Path(g.Str), g.Str.get(s.Name), int(a.n),
			int(a.broad), int(s.FanIn)})
	}
	sortRows(rows, sortKey{col: 3, asc: false}, sortKey{col: 4, asc: false})
	return cols, limitRows(rows, lim)
}

func qFilesStreamLeak(g *Graph, mod string, lim int) ([]string, [][]any) {
	cols := []string{"path", "name", "opened_by", "line", "fan_in"}
	want := newSet("lines", "walk", "list")
	rows := [][]any{}
	for i := range g.Res {
		r := &g.Res[i]
		if !want[g.Str.get(r.Type)] || r.ClosedInFn != 0 || r.InTryResources != 0 {
			continue
		}
		s := &g.Sym[r.SymID-1]
		f := &g.Files[r.FileID-1]
		if f.IsGen != 0 || !likeMatch(g.modName(s.ModuleID), mod) {
			continue
		}
		rows = append(rows, []any{f.Path(g.Str), g.Str.get(s.Name),
			g.Str.get(r.OpenedBy), int(r.Line), int(s.FanIn)})
	}
	sortRows(rows, sortKey{col: 4, asc: false})
	return cols, limitRows(rows, lim)
}

func qBannedApiSurface(g *Graph, mod string, lim int) ([]string, [][]any) {
	cols := []string{"path", "caller", "banned_api", "why", "n"}
	why := map[string]string{
		"System.exit":      "kills the host process; servers never return",
		"Runtime.halt":     "no shutdown hooks, no finally",
		"Unsafe.getUnsafe": "deprecated memory access; use VarHandle",
	}
	rows := [][]any{}
	for i := range g.Hazards {
		h := &g.Hazards[i]
		w, ok := why[g.Str.get(h.Pat)]
		if !ok {
			continue
		}
		s := &g.Sym[h.SymID-1]
		f := &g.Files[s.FileID-1]
		if f.IsGen != 0 || f.IsTest != 0 || !likeMatch(g.modName(s.ModuleID), mod) {
			continue
		}
		rows = append(rows, []any{f.Path(g.Str), g.Str.get(s.Name),
			g.Str.get(h.Pat), w, int(h.N)})
	}
	sortRows(rows, sortKey{col: 4, asc: false})
	return cols, limitRows(rows, lim)
}

func qLockOnBoxed(g *Graph, mod string, lim int) ([]string, [][]any) {
	cols := []string{"name", "owner", "lock_name", "field_type", "line", "fan_in"}
	boxed := newSet("Integer", "Long", "Boolean", "Character", "Byte", "Short",
		"Float", "Double")
	rows := [][]any{}
	for i := range g.Locks {
		lo := &g.Locks[i]
		if g.Str.get(lo.Op) != "acquire" {
			continue
		}
		s := &g.Sym[lo.SymID-1]
		if s.ParentID < 0 {
			continue
		}
		c := &g.Sym[s.ParentID-1]
		for j := range g.Fields {
			fd := &g.Fields[j]
			if fd.SymID != c.ID || fd.Name != lo.LockName {
				continue
			}

			simple := g.Str.get(fd.Type)
			if k := strings.IndexByte(simple, '.'); k >= 0 {
				simple = simple[k+1:]
			}
			if !boxed[simple] {
				continue
			}
			f := &g.Files[s.FileID-1]
			if f.IsGen != 0 || !likeMatch(g.modName(s.ModuleID), mod) {
				continue
			}
			rows = append(rows, []any{g.Str.get(s.Name),
				g.Str.get(s.OwnerType), g.Str.get(lo.LockName),
				g.Str.get(fd.Type), int(lo.Line), int(s.FanIn)})
		}
	}
	sortRows(rows, sortKey{col: 5, asc: false})
	return cols, limitRows(rows, lim)
}

func qStaticWriteInCtor(g *Graph, mod string, lim int) ([]string, [][]any) {
	return symbolQuery(g, mod, lim, true,
		func(s *Sym) bool {
			return s.Kind == kindConstructor && s.NStaticWriteCtor > 0
		},
		[]string{"name", "owner", "static_writes", "fan_in", "at"},
		func(s *Sym, f *File) []any {
			return []any{g.Str.get(s.Name), g.Str.get(s.OwnerType),
				int(s.NStaticWriteCtor), int(s.FanIn), g.at(s.FileID, s.LineStart)}
		},
		sortKey{col: 2, asc: false}, sortKey{col: 3, asc: false})
}

func qMissingSuperCall(g *Graph, mod string, lim int) ([]string, [][]any) {
	return symbolQuery(g, mod, lim, true,
		func(s *Sym) bool {
			if s.Kind != kindMethod || s.NSuperCalls != 0 {
				return false
			}
			n := g.Str.get(s.Name)
			return strings.Contains(n, "onCreate") || n == "init" ||
				strings.Contains(n, "doGet") || n == "service" ||
				strings.Contains(n, "onResume") || strings.Contains(n, "onDestroy")
		},
		[]string{"name", "owner", "super_calls", "fan_in", "at"},
		func(s *Sym, f *File) []any {
			return []any{g.Str.get(s.Name), g.Str.get(s.OwnerType),
				int(s.NSuperCalls), int(s.FanIn), g.at(s.FileID, s.LineStart)}
		},
		sortKey{col: 3, asc: false})
}

func qDeadException(g *Graph, mod string, lim int) ([]string, [][]any) {
	return symbolQuery(g, mod, lim, true,
		func(s *Sym) bool { return s.NDeadException > 0 },
		[]string{"name", "owner", "dead_exc", "fan_in", "at"},
		func(s *Sym, f *File) []any {
			return []any{g.Str.get(s.Name), g.Str.get(s.OwnerType),
				int(s.NDeadException), int(s.FanIn), g.at(s.FileID, s.LineStart)}
		},
		sortKey{col: 2, asc: false}, sortKey{col: 3, asc: false})
}

func qReferenceEquality(g *Graph, mod string, lim int) ([]string, [][]any) {
	return symbolQuery(g, mod, lim, true,
		func(s *Sym) bool { return s.NRefEq > 0 && s.NBoxingSites > 0 },
		[]string{"name", "owner", "ref_eqs", "boxing_sites", "fan_in", "at"},
		func(s *Sym, f *File) []any {
			return []any{g.Str.get(s.Name), g.Str.get(s.OwnerType),
				int(s.NRefEq), int(s.NBoxingSites), int(s.FanIn),
				g.at(s.FileID, s.LineStart)}
		},
		sortKey{col: 2, asc: false}, sortKey{col: 3, asc: false})
}

func qNarrowCalculation(g *Graph, mod string, lim int) ([]string, [][]any) {
	return symbolQuery(g, mod, lim, true,
		func(s *Sym) bool { return s.NNarrowCalc > 0 },
		[]string{"name", "owner", "narrow_calcs", "fan_in", "at"},
		func(s *Sym, f *File) []any {
			return []any{g.Str.get(s.Name), g.Str.get(s.OwnerType),
				int(s.NNarrowCalc), int(s.FanIn), g.at(s.FileID, s.LineStart)}
		},
		sortKey{col: 2, asc: false}, sortKey{col: 3, asc: false})
}

func qModernIdioms(g *Graph, mod string, lim int) ([]string, [][]any) {
	return symbolQuery(g, mod, lim, true,
		func(s *Sym) bool { return s.NModernIdioms > 0 },
		[]string{"name", "owner", "idioms", "sloc", "fan_in", "at"},
		func(s *Sym, f *File) []any {
			return []any{g.Str.get(s.Name), g.Str.get(s.OwnerType),
				int(s.NModernIdioms), int(s.Sloc), int(s.FanIn),
				g.at(s.FileID, s.LineStart)}
		},
		sortKey{col: 2, asc: false}, sortKey{col: 3, asc: false})
}

func qFlexConstructorPrologues(g *Graph, mod string, lim int) ([]string, [][]any) {
	cols := []string{"name", "owner", "fan_in", "n_params", "module", "at"}
	rows := [][]any{}
	g.forEachSymbol(nil, func(s *Sym, f *File) {
		if s.getFlag(fFlexCtor) != 1 || f.IsTest != 0 ||
			!likeMatch(g.modName(s.ModuleID), mod) {
			return
		}
		rows = append(rows, []any{g.Str.get(s.Name), g.Str.get(s.OwnerType),
			int(s.FanIn), int(s.NParams), g.modName(s.ModuleID),
			g.at(s.FileID, s.LineStart)})
	})
	sortRows(rows, sortKey{col: 1, asc: true}, sortKey{col: 0, asc: true})
	return cols, limitRows(rows, lim)
}

func qResilienceAnnotations(g *Graph, mod string, lim int) ([]string, [][]any) {
	cols := []string{"name", "owner", "resilience_annos", "n_annos",
		"db_calls", "exec_calls", "fan_in", "at"}
	want := newSet("Retryable", "ConcurrencyLimit", "RateLimiter", "CircuitBreaker",
		"Bulkhead", "Timeout")
	ai := g.buildAttrIndex()
	rows := [][]any{}
	for _, id := range g.scanOrder(kindFunction, kindMethod) {
		s := &g.Sym[id-1]
		if s.NResilienceAnnos == 0 {
			continue
		}
		f := &g.Files[s.FileID-1]
		if f.IsTest != 0 || !likeMatch(g.modName(s.ModuleID), mod) {
			continue
		}
		names := newConcat()
		for _, a := range g.attrsOf(&ai, s.ID, want) {
			names.add(a.Name, g.Str.get(a.Name))
		}
		rows = append(rows, []any{g.Str.get(s.Name), g.Str.get(s.OwnerType),
			names.String(), int(s.NResilienceAnnos), int(s.NQueryCalls),
			int(s.NRuntimeExec), int(s.FanIn), g.at(s.FileID, s.LineStart)})
	}
	sortRows(rows, sortKey{col: 3, asc: false}, sortKey{col: 4, asc: false},
		sortKey{col: 6, asc: false})
	return cols, limitRows(rows, lim)
}

func qHTTPExchangeClients(g *Graph, mod string, lim int) ([]string, [][]any) {
	cols := []string{"client_interface", "module", "exchange_methods", "methods",
		"at"}
	want := newSet("HttpExchange", "GetExchange", "PostExchange",
		"PutExchange", "DeleteExchange", "PatchExchange")
	ai := g.buildAttrIndex()
	rows := [][]any{}
	for i := range g.Sym {
		s := &g.Sym[i]
		if s.getFlag(fHTTPExchange) != 1 {
			continue
		}
		f := &g.Files[s.FileID-1]
		if f.IsTest != 0 || !likeMatch(g.modName(s.ModuleID), mod) {
			continue
		}
		if len(g.attrsOf(&ai, s.ID, want)) == 0 {
			continue
		}
		names := newConcat()
		n := int32(0)
		for j := range g.Sym {
			c := &g.Sym[j]
			if c.OwnerType == s.Name && c.Kind == kindMethod {
				names.add(c.Name, g.Str.get(c.Name))
				n++
			}
		}
		rows = append(rows, []any{g.Str.get(s.Name), g.modName(s.ModuleID),
			int(n), names.String(), g.at(s.FileID, s.LineStart)})
	}
	sortRows(rows, sortKey{col: 2, asc: false})
	return cols, limitRows(rows, lim)
}

func qAPIVersionDrift(g *Graph, mod string, lim int) ([]string, [][]any) {
	cols := []string{"controller", "method", "version_args", "version_attrs",
		"fan_in", "at"}
	ai := g.buildAttrIndex()
	rows := [][]any{}
	for i := range g.Sym {
		s := &g.Sym[i]
		if s.Kind != kindMethod || s.NApiVersionAttr == 0 ||
			s.OwnerType == nullStr {
			continue
		}
		f := &g.Files[s.FileID-1]
		if f.IsTest != 0 || !likeMatch(g.modName(s.ModuleID), mod) {
			continue
		}
		versioned := false
		for j := range g.Sym {
			t := &g.Sym[j]
			if t.OwnerType == s.OwnerType && t.Name == s.Name && t.ID != s.ID {
				versioned = true
				break
			}
		}
		if !versioned {
			continue
		}
		var args any
		for _, a := range g.attrsOf(&ai, s.ID, nil) {
			if a.HasArgs == 1 && strings.Contains(g.Str.get(a.Args), "version") {
				args = g.Str.get(a.Args)
			}
		}
		rows = append(rows, []any{g.Str.get(s.OwnerType), g.Str.get(s.Name),
			args, int(s.NApiVersionAttr), int(s.FanIn),
			g.at(s.FileID, s.LineStart)})
	}
	sortRows(rows, sortKey{col: 0, asc: true}, sortKey{col: 1, asc: true})
	return cols, limitRows(rows, lim)
}

func qJSpecifyViolations(g *Graph, mod string, lim int) ([]string, [][]any) {
	cols := []string{"name", "owner", "null_annos", "null_returns", "fan_in",
		"n_params", "at"}
	rows := [][]any{}
	for _, id := range g.scanOrderFileLine(kindFunction, kindMethod) {
		s := &g.Sym[id-1]
		if s.NJSpecifyAnnos == 0 || s.NNullReturns == 0 {
			continue
		}
		f := &g.Files[s.FileID-1]
		if f.IsTest != 0 || !likeMatch(g.modName(s.ModuleID), mod) {
			continue
		}
		rows = append(rows, []any{g.Str.get(s.Name), g.Str.get(s.OwnerType),
			int(s.NJSpecifyAnnos), int(s.NNullReturns), int(s.FanIn),
			int(s.NParams), g.at(s.FileID, s.LineStart)})
	}
	sortRows(rows, sortKey{col: 4, asc: false}, sortKey{col: 3, asc: false})
	return cols, limitRows(rows, lim)
}

func qNotifyWithoutNotifyAll(g *Graph, mod string, lim int) ([]string, [][]any) {
	cols := []string{"name", "owner", "notify_calls", "monitor_ops", "fan_in",
		"at"}
	rows := [][]any{}
	for _, id := range g.scanOrderFileLine(kindFunction, kindMethod) {
		s := &g.Sym[id-1]
		if s.NNotifySingle == 0 {
			continue
		}
		f := &g.Files[s.FileID-1]
		if f.IsTest != 0 || !likeMatch(g.modName(s.ModuleID), mod) {
			continue
		}
		rows = append(rows, []any{g.Str.get(s.Name), g.Str.get(s.OwnerType),
			int(s.NNotifySingle), int(s.NMonitorCall), int(s.FanIn),
			g.at(s.FileID, s.LineStart)})
	}
	sortRows(rows, sortKey{col: 4, asc: false}, sortKey{col: 2, asc: false})
	return cols, limitRows(rows, lim)
}

func qThreadRunNotStart(g *Graph, mod string, lim int) ([]string, [][]any) {
	cols := []string{"name", "owner", "run_calls", "thread_file", "fan_in", "at"}
	poolInFile := map[int32]bool{}
	for i := range g.Sym {
		s := &g.Sym[i]
		if s.NExecutorCreate > 0 || s.getFlag(fVtRoot) == 1 {
			poolInFile[s.FileID] = true
		}
	}
	rows := [][]any{}
	for _, id := range g.scanOrderFileLine() {
		s := &g.Sym[id-1]
		if s.Kind != kindFunction && s.Kind != kindMethod {
			continue
		}
		if s.NRunCalledDirectly == 0 {
			continue
		}
		f := &g.Files[s.FileID-1]
		if f.IsTest != 0 || !likeMatch(g.modName(s.ModuleID), mod) {
			continue
		}
		rows = append(rows, []any{g.Str.get(s.Name), g.Str.get(s.OwnerType),
			int(s.NRunCalledDirectly), boolI32(poolInFile[s.FileID]),
			int(s.FanIn), g.at(s.FileID, s.LineStart)})
	}
	sortRows(rows, sortKey{col: 3, asc: false}, sortKey{col: 4, asc: false})
	return cols, limitRows(rows, lim)
}

func qBigDecimalFromDouble(g *Graph, mod string, lim int) ([]string, [][]any) {
	cols := []string{"name", "owner", "bad_ctors", "total_allocs", "fan_in", "at"}
	rows := [][]any{}
	for _, id := range g.scanOrderFileLine(kindFunction, kindMethod) {
		s := &g.Sym[id-1]
		if s.NBigDecimalFromDouble == 0 {
			continue
		}
		f := &g.Files[s.FileID-1]
		if f.IsTest != 0 || !likeMatch(g.modName(s.ModuleID), mod) {
			continue
		}
		rows = append(rows, []any{g.Str.get(s.Name), g.Str.get(s.OwnerType),
			int(s.NBigDecimalFromDouble), int(s.NAllocSites), int(s.FanIn),
			g.at(s.FileID, s.LineStart)})
	}
	sortRows(rows, sortKey{col: 2, asc: false}, sortKey{col: 4, asc: false})
	return cols, limitRows(rows, lim)
}

func selfOnlyCallees(g *Graph) map[int32]bool {
	out := map[int32]bool{}
	for i := range g.Edges {
		e := &g.Edges[i]
		caller := &g.Sym[e.Caller-1]
		callee := &g.Sym[e.Callee-1]
		if callee.OwnerType == nullStr || caller.OwnerType != callee.OwnerType {
			continue
		}
		external := false
		lo, hi := g.In.lo(callee.ID), g.In.hi(callee.ID)
		for p := lo; p < hi; p++ {
			in := &g.In.Val[p]
			c2 := &g.Sym[in.Caller-1]
			if in.Callee != callee.ID {
				continue
			}
			if c2.OwnerType != callee.OwnerType || c2.OwnerType == nullStr {
				if g.Files[c2.FileID-1].IsTest == 0 {
					external = true
					break
				}
			}
		}
		if !external {
			out[callee.ID] = true
		}
	}
	return out
}

var proxyAnnoNames = newSet("Transactional", "Async", "Cacheable", "CacheEvict",
	"CachePut", "Caching", "Retryable", "Validated")

func qProxyBypassSelfInvocation(g *Graph, mod string, lim int) ([]string, [][]any) {
	cols := []string{"name", "owner", "proxy_annos", "n_annos", "calls_made", "at"}
	ai := g.buildAttrIndex()
	selfOnly := selfOnlyCallees(g)
	rows := [][]any{}
	for _, id := range g.scanOrder(kindFunction, kindMethod) {
		s := &g.Sym[id-1]
		if !selfOnly[s.ID] {
			continue
		}
		f := &g.Files[s.FileID-1]
		if f.IsTest != 0 || f.IsGen != 0 || !likeMatch(g.modName(s.ModuleID), mod) {
			continue
		}
		names := newConcat()
		for _, a := range g.attrsOf(&ai, s.ID, proxyAnnoNames) {
			names.add(a.Name, g.Str.get(a.Name))
		}
		if len(names.out) == 0 {
			continue
		}
		rows = append(rows, []any{g.Str.get(s.Name), g.Str.get(s.OwnerType),
			names.String(), int(len(names.out)), int(s.NCalls),
			g.at(s.FileID, s.LineStart)})
	}
	sortRows(rows, sortKey{col: 3, asc: false}, sortKey{col: 4, asc: false})
	return cols, limitRows(rows, lim)
}

func qTransactionalCheckedCommit(g *Graph, mod string, lim int) ([]string, [][]any) {
	cols := []string{"name", "owner", "tx_args", "checked_thrown", "callers", "at"}
	ai := g.buildAttrIndex()
	tx := newSet("Transactional")
	checked := map[int32]int32{}
	for i := range g.Excepts {
		e := &g.Excepts[i]
		if g.Str.get(e.Kind) != "throws" {
			continue
		}
		t := g.Str.get(e.Type)
		if t == "" || broadExceptions[t] {
			continue
		}
		checked[e.SymID]++
	}
	rows := [][]any{}
	for _, id := range g.scanOrder() {
		s := &g.Sym[id-1]
		n, ok := checked[s.ID]
		if !ok {
			continue
		}
		txAttrs := g.attrsOf(&ai, s.ID, tx)
		if len(txAttrs) == 0 {
			continue
		}
		var args any
		for _, a := range txAttrs {
			args = g.Str.get(a.Args)
		}
		if sa, ok := args.(string); ok && strings.Contains(sa, "rollbackFor") {
			continue
		}
		f := &g.Files[s.FileID-1]
		if f.IsTest != 0 || f.IsGen != 0 || !likeMatch(g.modName(s.ModuleID), mod) {
			continue
		}
		rows = append(rows, []any{g.Str.get(s.Name), g.Str.get(s.OwnerType),
			args, int(n), int(s.FanIn), g.at(s.FileID, s.LineStart)})
	}
	sortRows(rows, sortKey{col: 3, asc: false}, sortKey{col: 4, asc: false})
	return cols, limitRows(rows, lim)
}

var singletonAnnos = newSet("Component", "Service", "Repository", "Controller",
	"RestController", "ControllerAdvice", "Configuration", "Singleton")

func qPrototypeBeanIntoSingleton(g *Graph, mod string, lim int) ([]string, [][]any) {
	cols := []string{"singleton_bean", "n_proto_fields", "fields_", "types_", "at"}
	ai := g.buildAttrIndex()
	proto := map[uint32]bool{}
	for i := range g.Sym {
		t := &g.Sym[i]
		if !kindsBean[g.kindOf(t)] {
			continue
		}
		for _, a := range g.attrsOf(&ai, t.ID, nil) {
			n := g.Str.get(a.Name)
			if narrowScopeAnnotations[n] || (n == "Scope" && a.HasArgs == 1 &&
				strings.Contains(g.Str.get(a.Args), "prototype")) {
				proto[t.Name] = true
			}
		}
	}
	rows := [][]any{}
	for i := range g.Sym {
		s := &g.Sym[i]
		if s.Kind != kindClass {
			continue
		}
		if len(g.attrsOf(&ai, s.ID, singletonAnnos)) == 0 {
			continue
		}
		f := &g.Files[s.FileID-1]
		if f.IsTest != 0 || f.IsGen != 0 || !likeMatch(g.modName(s.ModuleID), mod) {
			continue
		}
		fields := newConcat()
		types := newConcat()
		n := int32(0)
		for j := range g.Fields {
			fd := &g.Fields[j]
			if fd.SymID != s.ID {
				continue
			}
			t := g.Str.get(fd.Type)
			if proto[g.Str.intern(simpleTypeBefore(t))] {
				n++
				fields.addStr(g.Str.get(fd.Name))
				types.addStr(t)
			}
		}
		if n == 0 {
			continue
		}
		rows = append(rows, []any{g.Str.get(s.Name), int(n), fields.String(),
			types.String(), g.at(s.FileID, s.LineStart)})
	}
	sortRows(rows, sortKey{col: 1, asc: false})
	return cols, limitRows(rows, lim)
}

var closeableReturns = newSet("InputStream", "OutputStream", "Reader", "Writer",
	"Stream", "IntStream", "LongStream", "DoubleStream", "Connection",
	"Channel", "Socket", "ServerSocket", "DatagramSocket", "RandomAccessFile",
	"Scanner", "ObjectInput", "ObjectOutput", "Closeable", "AutoCloseable",
	"FileInputStream", "FileOutputStream", "FileReader", "FileWriter",
	"BufferedReader", "BufferedWriter", "BufferedInputStream",
	"BufferedOutputStream", "InputStreamReader", "OutputStreamWriter",
	"PrintWriter", "PrintStream", "DataInputStream", "DataOutputStream",
	"ObjectInputStream", "ObjectOutputStream", "ZipFile", "ZipInputStream",
	"ZipOutputStream", "GZIPInputStream", "GZIPOutputStream", "JarFile",
	"Statement", "PreparedStatement", "CallableStatement", "ResultSet",
	"JsonReader", "JsonWriter")

func qReturnedResourceNeverClosed(g *Graph, mod string, lim int) ([]string, [][]any) {
	cols := []string{"name", "owner", "return_type", "n_opens", "n_callers",
		"n_closing", "at"}
	opens := map[int32]int32{}
	for i := range g.Res {
		r := &g.Res[i]
		if r.InTryResources == 0 {
			opens[r.SymID]++
		}
	}
	callers := map[int32]int32{}
	closing := map[int32]int32{}
	seenCaller := map[[2]int32]bool{}
	seenCloser := map[[2]int32]bool{}
	for i := range g.Edges {
		e := &g.Edges[i]
		c := &g.Sym[e.Caller-1]
		if g.Files[c.FileID-1].IsTest != 0 {
			continue
		}
		k := [2]int32{e.Callee, e.Caller}
		if !seenCaller[k] {
			seenCaller[k] = true
			callers[e.Callee]++
		}
		if (c.NCloseCalls > 0 || c.NTryResources > 0) && !seenCloser[k] {
			seenCloser[k] = true
			closing[e.Callee]++
		}
	}
	rows := [][]any{}
	for _, id := range g.scanOrder() {
		s := &g.Sym[id-1]
		n, ok := opens[s.ID]

		if _, called := callers[s.ID]; !ok || !called || closing[s.ID] != 0 {
			continue
		}
		if !closeableReturns[simpleTypeBefore(g.Str.get(s.RetType))] {
			continue
		}
		f := &g.Files[s.FileID-1]
		if f.IsTest != 0 || f.IsGen != 0 || !likeMatch(g.modName(s.ModuleID), mod) {
			continue
		}
		rows = append(rows, []any{g.Str.get(s.Name), g.Str.get(s.OwnerType),
			g.Str.get(s.RetType), int(n), int(callers[s.ID]),
			int(closing[s.ID]), g.at(s.FileID, s.LineStart)})
	}
	sortRows(rows, sortKey{col: 4, asc: false}, sortKey{col: 3, asc: false})
	return cols, limitRows(rows, lim)
}

func qLockAcquireWithoutRelease(g *Graph, mod string, lim int) ([]string, [][]any) {
	cols := []string{"name", "owner", "n_acq", "io_in_body", "waits", "callers",
		"at"}
	acq := map[int32]int32{}
	first := map[int32]int32{}
	rel := map[int32]bool{}
	for i := range g.Locks {
		l := &g.Locks[i]
		if g.Str.get(l.Op) == "acquire" && g.Str.get(l.Kind) == "lock" {
			acq[l.SymID]++
			if v, ok := first[l.SymID]; !ok || l.Line < v {
				first[l.SymID] = l.Line
			}
		}
		if g.Str.get(l.Op) == "release" {
			rel[l.SymID] = true
		}
	}
	rows := [][]any{}
	for _, id := range g.scanOrder() {
		s := &g.Sym[id-1]
		n, ok := acq[s.ID]
		if !ok || rel[s.ID] {
			continue
		}
		f := &g.Files[s.FileID-1]
		if f.IsTest != 0 || f.IsGen != 0 || !likeMatch(g.modName(s.ModuleID), mod) {
			continue
		}
		rows = append(rows, []any{g.Str.get(s.Name), g.Str.get(s.OwnerType),
			int(n), int(s.NIO), int(s.NWaitCalls), int(s.FanIn),
			g.at(s.FileID, first[s.ID])})
	}
	sortRows(rows, sortKey{col: 2, asc: false}, sortKey{col: 5, asc: false})
	return cols, limitRows(rows, lim)
}

func qTransitiveBlockUnderLock(g *Graph, mod string, lim int) ([]string, [][]any) {
	cols := []string{"name", "owner", "hops", "block_ops", "locks_held",
		"callers", "at"}
	var seeds []int32
	for i := range g.Locks {
		l := &g.Locks[i]
		if g.Str.get(l.Op) == "acquire" && l.HoldsCall > 0 {
			seeds = append(seeds, l.SymID)
		}
	}

	down := downClosure(g, seeds, 2, 1)
	rows := [][]any{}
	for _, id := range g.scanOrderFileLine() {
		s := &g.Sym[id-1]
		d, ok := down[s.ID]
		if !ok {
			continue
		}
		nb := s.NWaitCalls + s.NIO + s.NQueryCalls
		if nb == 0 {
			continue
		}
		f := &g.Files[s.FileID-1]
		if f.IsTest != 0 || f.IsGen != 0 || !likeMatch(g.modName(s.ModuleID), mod) {
			continue
		}
		rows = append(rows, []any{g.Str.get(s.Name), g.Str.get(s.OwnerType),
			int(d), int(nb), int(s.NLockAcquire + s.NSyncBlocks),
			int(s.FanIn), g.at(s.FileID, s.LineStart)})
	}
	sortRows(rows, sortKey{col: 2, asc: true}, sortKey{col: 3, asc: false})
	return cols, limitRows(rows, lim)
}

func qWaitNotifyOutsideSync(g *Graph, mod string, lim int) ([]string, [][]any) {
	cols := []string{"name", "owner", "op", "monitor", "bare_sites", "n_in_sync",
		"callers", "at"}
	classMonitors := map[uint32]bool{}
	for i := range g.Locks {
		l := &g.Locks[i]
		if g.Str.get(l.Op) != "acquire" {
			continue
		}
		n := g.Str.get(l.LockName)
		if n != "" && n != "this" {
			classMonitors[l.LockName] = true
		}
	}
	type key struct {
		sym, mon, op uint32
	}
	type agg struct {
		sites, inSync, firstLine int32
	}
	groups := map[key]*agg{}
	var order []key
	for i := range g.MonOps {
		mo := &g.MonOps[i]
		k := key{uint32(mo.SymID), mo.Monitor, mo.Op}
		a := groups[k]
		if a == nil {
			a = &agg{firstLine: mo.Line}
			groups[k] = a
			order = append(order, k)
		}
		a.sites++
		a.inSync += mo.InSync
		if mo.Line < a.firstLine {
			a.firstLine = mo.Line
		}
	}
	rows := [][]any{}
	for _, k := range order {
		a := groups[k]
		if a.inSync >= a.sites || !classMonitors[k.mon] {
			continue
		}
		s := &g.Sym[k.sym-1]
		f := &g.Files[s.FileID-1]
		if f.IsTest != 0 || f.IsGen != 0 || !likeMatch(g.modName(s.ModuleID), mod) {
			continue
		}
		rows = append(rows, []any{g.Str.get(s.Name), g.Str.get(s.OwnerType),
			g.Str.get(k.op), g.Str.get(k.mon), int(a.sites - a.inSync),
			int(a.inSync), int(s.FanIn), g.at(s.FileID, a.firstLine)})
	}
	sortRows(rows, sortKey{col: 4, asc: false}, sortKey{col: 6, asc: false})
	return cols, limitRows(rows, lim)
}

func qInterruptSwallowed(g *Graph, mod string, lim int) ([]string, [][]any) {
	cols := []string{"name", "owner", "swallowed", "caught", "callers", "at"}
	lines := map[int32]map[int32]bool{}
	types := map[int32]string{}
	for i := range g.Excepts {
		e := &g.Excepts[i]
		if g.Str.get(e.Kind) != "catch" ||
			g.Str.get(e.Type) != "InterruptedException" {
			continue
		}
		if e.Rethrows != 0 || e.Restores != 0 {
			continue
		}
		s := &g.Sym[e.SymID-1]
		f := &g.Files[e.FileID-1]
		if f.IsTest != 0 || f.IsGen != 0 || !likeMatch(g.modName(s.ModuleID), mod) {
			continue
		}
		m := lines[e.SymID]
		if m == nil {
			m = map[int32]bool{}
			lines[e.SymID] = m
		}
		m[e.Line] = true
		types[e.SymID] = g.Str.get(e.Type)
	}
	rows := [][]any{}
	for _, id := range g.scanOrder() {
		s := &g.Sym[id-1]
		m, ok := lines[s.ID]
		if !ok {
			continue
		}
		first := int32(0)
		for l := range m {
			if first == 0 || l < first {
				first = l
			}
		}
		rows = append(rows, []any{g.Str.get(s.Name), g.Str.get(s.OwnerType),
			int(len(m)), types[s.ID], int(s.FanIn), g.at(s.FileID, first)})
	}
	sortRows(rows, sortKey{col: 2, asc: false}, sortKey{col: 4, asc: false})
	return cols, limitRows(rows, lim)
}

func qSharedFormatFieldUse(g *Graph, mod string, lim int) ([]string, [][]any) {
	cols := []string{"name", "owner", "shared_uses", "callers", "at"}
	rows := [][]any{}
	for _, id := range g.scanOrderFileLine(kindFunction, kindMethod, kindConstructor) {
		s := &g.Sym[id-1]
		if s.NSharedDatefmtUse == 0 {
			continue
		}
		f := &g.Files[s.FileID-1]
		if f.IsTest != 0 || f.IsGen != 0 || !likeMatch(g.modName(s.ModuleID), mod) {
			continue
		}
		rows = append(rows, []any{g.Str.get(s.Name), g.Str.get(s.OwnerType),
			int(s.NSharedDatefmtUse), int(s.FanIn), g.at(s.FileID, s.LineStart)})
	}
	sortRows(rows, sortKey{col: 2, asc: false}, sortKey{col: 3, asc: false})
	return cols, limitRows(rows, lim)
}

func qStringFormatInLoop(g *Graph, mod string, lim int) ([]string, [][]any) {
	cols := []string{"name", "owner", "fmt_in_loop", "depth", "callers", "at"}
	rows := [][]any{}
	for _, id := range g.scanOrderFileLine(kindFunction, kindMethod, kindConstructor) {
		s := &g.Sym[id-1]
		if s.NFormatInLoop == 0 {
			continue
		}
		f := &g.Files[s.FileID-1]
		if f.IsTest != 0 || f.IsGen != 0 || !likeMatch(g.modName(s.ModuleID), mod) {
			continue
		}
		rows = append(rows, []any{g.Str.get(s.Name), g.Str.get(s.OwnerType),
			int(s.NFormatInLoop), int(s.MaxLoopDepth), int(s.FanIn),
			g.at(s.FileID, s.LineStart)})
	}
	sortRows(rows, sortKey{col: 2, asc: false}, sortKey{col: 4, asc: false})
	return cols, limitRows(rows, lim)
}

func entryReach(g *Graph, maxDepth int32) map[[2]int32]int32 {
	var roots []int32
	for _, id := range g.scanOrderFileLine(kindFnMethCon...) {
		if isEntryRoot(&g.Sym[id-1]) {
			roots = append(roots, id)
		}
	}
	reach := downFromRoots(g, roots, maxDepth)

	for k := range reach {
		if g.Files[g.Sym[k[0]-1].FileID-1].IsTest != 0 {
			delete(reach, k)
		}
	}
	return reach
}

func qCommonPoolFromEntry(g *Graph, mod string, lim int) ([]string, [][]any) {
	cols := []string{"name", "owner", "hops", "n_entry_paths", "parallel_ops",
		"at"}
	reach := entryReach(g, 3)
	hops := map[int32]int32{}
	paths := map[int32]int32{}
	for k, d := range reach {
		if d == 0 {
			continue
		}
		if v, ok := hops[k[1]]; !ok || d < v {
			hops[k[1]] = d
		}
		paths[k[1]]++
	}
	rows := [][]any{}
	for _, id := range g.scanOrder() {
		s := &g.Sym[id-1]
		d, ok := hops[s.ID]
		if !ok || s.NParallelStreams == 0 {
			continue
		}
		f := &g.Files[s.FileID-1]
		if f.IsTest != 0 || f.IsGen != 0 ||
			!likeMatch(g.modName(s.ModuleID), mod) {
			continue
		}
		rows = append(rows, []any{g.Str.get(s.Name), g.Str.get(s.OwnerType),
			int(d), int(paths[s.ID]), int(s.NParallelStreams),
			g.at(s.FileID, s.LineStart)})
	}
	sortRows(rows, sortKey{col: 2, asc: true}, sortKey{col: 4, asc: false})
	return cols, limitRows(rows, lim)
}

func qStaticWriteFromEntry(g *Graph, mod string, lim int) ([]string, [][]any) {
	cols := []string{"name", "owner", "hops", "n_entry_paths", "static_writes",
		"volatile_refs", "at"}
	reach := entryReach(g, 3)
	hops := map[int32]int32{}
	paths := map[int32]int32{}
	bad := map[int32]bool{}
	for k, d := range reach {
		if d == 0 {
			continue
		}
		if v, ok := hops[k[1]]; !ok || d < v {
			hops[k[1]] = d
		}
		paths[k[1]]++
		if g.Files[g.Sym[k[0]-1].FileID-1].IsTest != 0 {
			bad[k[1]] = true
		}
	}
	rows := [][]any{}
	for _, id := range g.scanOrder() {
		s := &g.Sym[id-1]
		d, ok := hops[s.ID]
		if !ok || s.NStaticWrites == 0 {
			continue
		}
		f := &g.Files[s.FileID-1]
		if f.IsTest != 0 || f.IsGen != 0 || !likeMatch(g.modName(s.ModuleID), mod) {
			continue
		}
		rows = append(rows, []any{g.Str.get(s.Name), g.Str.get(s.OwnerType),
			int(d), int(paths[s.ID]), int(s.NStaticWrites),
			int(s.NVolatileAccess), g.at(s.FileID, s.LineStart)})
	}
	sortRows(rows, sortKey{col: 4, asc: false}, sortKey{col: 2, asc: true})
	return cols, limitRows(rows, lim)
}

func qListenerAddRemoveImbalance(g *Graph, mod string, lim int) ([]string, [][]any) {
	cols := []string{"class_", "adds", "removes", "net_added", "registering_fns",
		"at"}
	type led struct{ adds, removes, fns int32 }
	byOwner := map[uint32]*led{}
	for i := range g.Sym {
		s := &g.Sym[i]
		if s.OwnerType == nullStr {
			continue
		}
		if s.Kind != kindFunction && s.Kind != kindMethod {
			continue
		}
		e := byOwner[s.OwnerType]
		if e == nil {
			e = &led{}
			byOwner[s.OwnerType] = e
		}
		e.adds += s.NListenerAdd
		e.removes += s.NListenerRemove
		e.fns++
	}
	rows := [][]any{}
	for _, id := range g.scanOrder(kindClass, kindInterface) {
		s := &g.Sym[id-1]
		e, ok := byOwner[s.Name]
		if !ok || e.adds <= e.removes {
			continue
		}
		f := &g.Files[s.FileID-1]
		if f.IsTest != 0 || f.IsGen != 0 || !likeMatch(g.modName(s.ModuleID), mod) {
			continue
		}
		rows = append(rows, []any{g.Str.get(s.Name), int(e.adds),
			int(e.removes), int(e.adds - e.removes), int(e.fns),
			g.at(s.FileID, s.LineStart)})
	}
	sortRows(rows, sortKey{col: 1, asc: false}, sortKey{col: 0, asc: true})
	return cols, limitRows(rows, lim)
}

func qExpressionEvalFromInput(g *Graph, mod string, lim int) ([]string, [][]any) {
	cols := []string{"name", "owner", "hops", "n_entry_paths", "reads_input",
		"eval_calls", "at"}
	reach := entryReach(g, 3)
	hops := map[int32]int32{}
	paths := map[int32]int32{}
	for k, d := range reach {
		if d == 0 {
			continue
		}
		if v, ok := hops[k[1]]; !ok || d < v {
			hops[k[1]] = d
		}
		paths[k[1]]++
	}
	withInput := map[int32]bool{}
	for i := range g.UISites {
		withInput[g.UISites[i].SymID] = true
	}
	rows := [][]any{}
	for _, id := range g.scanOrder() {
		s := &g.Sym[id-1]
		if s.NSpelEval == 0 {
			continue
		}
		d, reach1 := hops[s.ID]
		if !reach1 && !withInput[s.ID] {
			continue
		}
		f := &g.Files[s.FileID-1]
		if f.IsTest != 0 || f.IsGen != 0 || !likeMatch(g.modName(s.ModuleID), mod) {
			continue
		}
		if !reach1 {
			d = 0
		}
		rows = append(rows, []any{g.Str.get(s.Name), g.Str.get(s.OwnerType),
			int(d), int(paths[s.ID]), boolI32(withInput[s.ID]),
			int(s.NSpelEval), g.at(s.FileID, s.LineStart)})
	}
	sortRows(rows, sortKey{col: 5, asc: false}, sortKey{col: 2, asc: true})
	return cols, limitRows(rows, lim)
}

func qVolatileCompoundUpdate(g *Graph, mod string, lim int) ([]string, [][]any) {
	cols := []string{"name", "owner", "bad_updates", "volatile_refs", "callers",
		"at"}
	rows := [][]any{}
	for _, id := range g.scanOrderFileLine(kindFunction, kindMethod, kindConstructor) {
		s := &g.Sym[id-1]
		if s.NVolatileCompound == 0 {
			continue
		}
		f := &g.Files[s.FileID-1]
		if f.IsTest != 0 || f.IsGen != 0 || !likeMatch(g.modName(s.ModuleID), mod) {
			continue
		}
		rows = append(rows, []any{g.Str.get(s.Name), g.Str.get(s.OwnerType),
			int(s.NVolatileCompound), int(s.NVolatileAccess), int(s.FanIn),
			g.at(s.FileID, s.LineStart)})
	}
	sortRows(rows, sortKey{col: 2, asc: false}, sortKey{col: 4, asc: false})
	return cols, limitRows(rows, lim)
}

func qManualThreadAllocation(g *Graph, mod string, lim int) ([]string, [][]any) {
	cols := []string{"name", "owner", "raw_threads", "has_pool_infra", "callers",
		"at"}
	poolInFile := map[int32]bool{}
	for i := range g.Sym {
		s := &g.Sym[i]
		if s.getFlag(fExecRoot) == 1 || s.getFlag(fPoolRoot) == 1 ||
			s.getFlag(fVtRoot) == 1 {
			poolInFile[s.FileID] = true
		}
	}
	rows := [][]any{}
	for _, id := range g.scanOrderFileLine(kindFunction, kindMethod, kindConstructor) {
		s := &g.Sym[id-1]
		if s.NThreadAlloc == 0 {
			continue
		}
		f := &g.Files[s.FileID-1]
		if f.IsTest != 0 || f.IsGen != 0 || !likeMatch(g.modName(s.ModuleID), mod) {
			continue
		}
		rows = append(rows, []any{g.Str.get(s.Name), g.Str.get(s.OwnerType),
			int(s.NThreadAlloc), boolI32(poolInFile[s.FileID]), int(s.FanIn),
			g.at(s.FileID, s.LineStart)})
	}
	sortRows(rows, sortKey{col: 2, asc: false}, sortKey{col: 3, asc: false})
	return cols, limitRows(rows, lim)
}

func qScheduledOverlapRisk(g *Graph, mod string, lim int) ([]string, [][]any) {
	cols := []string{"name", "owner", "trigger_args", "fixed_rate", "io_ops",
		"db_calls", "locks", "overlap_cost", "at"}
	ai := g.buildAttrIndex()
	want := newSet("Scheduled")
	rows := [][]any{}
	for _, id := range g.scanOrder() {
		s := &g.Sym[id-1]
		attrs := g.attrsOf(&ai, s.ID, want)
		if len(attrs) == 0 {
			continue
		}
		f := &g.Files[s.FileID-1]
		if f.IsTest != 0 || f.IsGen != 0 || !likeMatch(g.modName(s.ModuleID), mod) {
			continue
		}
		var args strings.Builder
		fixed := 0
		for _, a := range attrs {
			args.WriteString(g.Str.get(a.Args))
			if strings.Contains(args.String(), "fixedRate") {
				fixed = 1
			}
		}
		var argOut any
		if args.String() != "" {
			argOut = args.String()
		}
		cost := s.NIO*2 + s.NQueryCalls*2 + s.NWaitCalls*3 + s.NLockAcquire +
			s.NSyncBlocks
		rows = append(rows, []any{g.Str.get(s.Name), g.Str.get(s.OwnerType),
			argOut, fixed, int(s.NIO), int(s.NQueryCalls),
			int(s.NLockAcquire + s.NSyncBlocks), int(cost),
			g.at(s.FileID, s.LineStart)})
	}
	sortRows(rows, sortKey{col: 7, asc: false}, sortKey{col: 5, asc: false})
	return cols, limitRows(rows, lim)
}

func qEventListenerSyncBurden(g *Graph, mod string, lim int) ([]string, [][]any) {
	cols := []string{"name", "owner", "listener_annos", "io_ops", "db_calls",
		"waits", "sync_cost", "publishers_reaching", "at"}
	ai := g.buildAttrIndex()
	want := newSet("EventListener", "TransactionalEventListener", "Subscribe")
	rows := [][]any{}
	for _, id := range g.scanOrder() {
		s := &g.Sym[id-1]
		attrs := g.attrsOf(&ai, s.ID, want)
		if len(attrs) == 0 {
			continue
		}
		if s.NIO == 0 && s.NQueryCalls == 0 && s.NWaitCalls == 0 {
			continue
		}
		f := &g.Files[s.FileID-1]
		if f.IsTest != 0 || f.IsGen != 0 || !likeMatch(g.modName(s.ModuleID), mod) {
			continue
		}
		names := newConcat()
		for _, a := range attrs {
			names.add(a.Name, g.Str.get(a.Name))
		}
		cost := s.NIO*3 + s.NQueryCalls*2 + s.NWaitCalls*3
		rows = append(rows, []any{g.Str.get(s.Name), g.Str.get(s.OwnerType),
			names.String(), int(s.NIO), int(s.NQueryCalls), int(s.NWaitCalls),
			int(cost), int(s.FanIn), g.at(s.FileID, s.LineStart)})
	}
	sortRows(rows, sortKey{col: 6, asc: false}, sortKey{col: 7, asc: false})
	return cols, limitRows(rows, lim)
}

func qCacheEvictDrift(g *Graph, mod string, lim int) ([]string, [][]any) {
	cols := []string{"name", "owner", "unmatched_names", "evict_args", "callers",
		"at"}
	ai := g.buildAttrIndex()

	cacheEvictAnnos := newSet("CacheEvict")
	populated := populatedArgs(g, "Cacheable", "Caching")
	rows := [][]any{}
	for _, id := range g.scanOrder() {
		s := &g.Sym[id-1]
		attrs := g.attrsOf(&ai, s.ID, cacheEvictAnnos)
		if len(attrs) == 0 {
			continue
		}
		f := &g.Files[s.FileID-1]
		if f.IsTest != 0 || f.IsGen != 0 || !likeMatch(g.modName(s.ModuleID), mod) {
			continue
		}
		names := newConcat()
		firstLine := int32(0)
		unmatched := 0
		for _, a := range attrs {

			if a.Args != nullStr && populated[a.Args] {
				continue
			}
			names.addStr(g.Str.get(a.Args))
			unmatched++
			if firstLine == 0 || a.Line < firstLine {
				firstLine = a.Line
			}
		}
		if unmatched == 0 {
			continue
		}
		rows = append(rows, []any{g.Str.get(s.Name), g.Str.get(s.OwnerType),
			int(unmatched), names.String(), int(s.FanIn),
			g.at(s.FileID, firstLine)})
	}
	sortRows(rows, sortKey{col: 2, asc: false}, sortKey{col: 4, asc: false})
	return cols, limitRows(rows, lim)
}

func qPrivateProxyAnnotation(g *Graph, mod string, lim int) ([]string, [][]any) {
	cols := []string{"name", "owner", "visibility", "proxy_annos", "n_annos",
		"callers", "at"}
	ai := g.buildAttrIndex()
	rows := [][]any{}
	for _, id := range g.scanOrder() {
		s := &g.Sym[id-1]
		attrs := g.attrsOf(&ai, s.ID, proxyAnnoNames)
		if len(attrs) == 0 {
			continue
		}
		if g.Str.get(s.Vis) != "private" {
			continue
		}
		if s.Kind != kindFunction && s.Kind != kindMethod {
			continue
		}
		f := &g.Files[s.FileID-1]
		if f.IsTest != 0 || f.IsGen != 0 || !likeMatch(g.modName(s.ModuleID), mod) {
			continue
		}
		names := newConcat()
		for _, a := range attrs {
			names.add(a.Name, g.Str.get(a.Name))
		}
		rows = append(rows, []any{g.Str.get(s.Name), g.Str.get(s.OwnerType),
			g.Str.get(s.Vis), names.String(), int(len(names.out)),
			int(s.FanIn), g.at(s.FileID, s.LineStart)})
	}
	sortRows(rows, sortKey{col: 4, asc: false}, sortKey{col: 5, asc: false})
	return cols, limitRows(rows, lim)
}

func qStaticCollectionGrows(g *Graph, mod string, lim int) ([]string, [][]any) {
	cols := []string{"class_", "adds", "removes", "net_added", "touching_fns",
		"static_collections", "collection_fields", "at"}
	type growth struct {
		adds, removes, fns int32
		order              int
	}
	byOwner := map[uint32]*growth{}

	for _, id := range g.scanOrderModuleKind() {
		s := &g.Sym[id-1]
		if s.OwnerType == nullStr {
			continue
		}
		if s.Kind != kindFunction && s.Kind != kindMethod {
			continue
		}
		e := byOwner[s.OwnerType]
		if e == nil {
			e = &growth{order: len(byOwner)}
			byOwner[s.OwnerType] = e
		}
		e.adds += s.NStaticCollAdd
		e.removes += s.NStaticCollRemove
		e.fns++
	}
	var classOrder []int32
	for _, id := range g.scanOrder(kindClass) {
		s := &g.Sym[id-1]
		if _, ok := byOwner[s.Name]; ok {
			classOrder = append(classOrder, id)
		}
	}
	sort.SliceStable(classOrder, func(i, j int) bool {
		return byOwner[g.Sym[classOrder[i]-1].Name].order <
			byOwner[g.Sym[classOrder[j]-1].Name].order
	})
	rows := [][]any{}
	for _, id := range classOrder {
		s := &g.Sym[id-1]
		e := byOwner[s.Name]
		if e.adds <= e.removes {
			continue
		}
		names := newConcat()
		n := int32(0)
		for j := range g.Fields {
			fd := &g.Fields[j]
			if fd.SymID == s.ID && fd.IsStatic == 1 && fd.IsConst == 0 {
				n++
				names.addStr(g.Str.get(fd.Name))
			}
		}
		if n == 0 {
			continue
		}
		f := &g.Files[s.FileID-1]
		if f.IsTest != 0 || f.IsGen != 0 || !likeMatch(g.modName(s.ModuleID), mod) {
			continue
		}
		rows = append(rows, []any{g.Str.get(s.Name), int(e.adds),
			int(e.removes), int(e.adds - e.removes), int(e.fns), int(n),
			names.String(), g.at(s.FileID, s.LineStart)})
	}
	sortRows(rows, sortKey{col: 3, asc: false}, sortKey{col: 1, asc: false})
	return cols, limitRows(rows, lim)
}

func qSharedBeanMutableCollection(g *Graph, mod string, lim int) ([]string, [][]any) {
	cols := []string{"bean", "unsafe_collections", "field_types", "callers", "at"}
	ai := g.buildAttrIndex()
	rows := [][]any{}
	for _, id := range g.scanOrder(kindClass) {
		s := &g.Sym[id-1]
		if len(g.attrsOf(&ai, s.ID, singletonAnnos)) == 0 {
			continue
		}
		types := newConcat()
		n := int32(0)
		for j := range g.Fields {
			fd := &g.Fields[j]
			if fd.SymID != s.ID || fd.IsColl != 1 || fd.IsStatic == 1 {
				continue
			}
			head := simpleTypeBefore(g.Str.get(fd.Type))
			if threadSafeCollections[head] {
				continue
			}
			n++
			types.addStr(head)
		}
		if n == 0 {
			continue
		}
		f := &g.Files[s.FileID-1]
		if f.IsTest != 0 || f.IsGen != 0 || !likeMatch(g.modName(s.ModuleID), mod) {
			continue
		}
		rows = append(rows, []any{g.Str.get(s.Name), int(n), types.String(),
			int(s.FanIn), g.at(s.FileID, s.LineStart)})
	}
	sortRows(rows, sortKey{col: 1, asc: false}, sortKey{col: 3, asc: false})
	return cols, limitRows(rows, lim)
}

var _ = sort.Ints

var queries = []query{
	{
		name:  "reflection-frontier",
		title: "Public entry points that reach Class.forName or setAccessible",
		notes: "ANSWERS the two lists you cannot write by hand: what belongs in\n     --add-opens, and what belongs in a native-image reflect-config.json.\n     Anything reachable from the API surface may be invoked reflectively\n     at run time, and everything else may be closed.\nACT for each row, name the classes actually opened and pin them. A\n     setAccessible on a JDK internal is a future JEP away from throwing.\nMISLEADS depth is capped at 4 hops and only RESOLVED edges are walked, so\n     this is a floor, never a ceiling. Reflection that goes through a\n     framework -- which is most of it -- has no edge at all and cannot\n     appear. Check graph-blindspots for the module first.",
		run:   nil,
	},
	{
		name:  "deserialization-reachability",
		title: "Deserialization and JNDI sinks reachable from an entry point",
		notes: "ANSWERS the shape behind every Java RCE of the last decade: attacker\n     bytes reach readObject, readValue with default typing enabled,\n     Yaml.load, XMLDecoder or InitialContext.lookup.\nACT put an ObjectInputFilter on every stream you did not create, or stop\n     deserializing untrusted input at all. serial_types_no_uid counts\n     Serializable types in the same module with no serialVersionUID --\n     each one is a class whose wire format changes silently on rebuild.\nMISLEADS depth is capped at 4 hops over resolved edges only. A sink is\n     not a vulnerability: it is a vulnerability when the bytes are\n     attacker-controlled, which this cannot see. Jackson without\n     enableDefaultTyping is not the gadget-chain shape.",
		run:   nil,
	},
	{
		name:  "resource-open-never-closed",
		title: "Opened here, closed somewhere else -- or nowhere",
		notes: "ANSWERS the cross-function OS_OPEN_STREAM: the open and the close live in\n     different methods, so no per-file checker can pair them. A stream\n     opened in a factory and returned is fine; one opened in a leaf that\n     nobody closes is a descriptor leak that shows up as EMFILE in\n     production and nowhere in the tests.\nACT wrap it in try-with-resources, or return it and name the method so\n     the caller knows it owns a closeable. callers_that_close is the\n     evidence that someone already does.\nMISLEADS a factory that deliberately hands back an open resource is\n     correct and appears here -- check whether return_type is a Closeable.\n     closed_in_fn is a text scan for .close() in the same body, so a close\n     one frame deeper reads as absent.",
		run:   nil,
	},
	{
		name:  "lock-order-inversion",
		title: "Two locks taken in opposite orders in different methods",
		notes: "ANSWERS the deadlock ring: method A takes L1 then L2, method B takes L2\n     then L1. Nothing fails until both run at once, which is why it ships.\n     acq_order is recorded per acquisition per method, so this is a real\n     ordering comparison and not a co-occurrence count.\nACT impose one global lock order and document it. Where you cannot, use\n     tryLock with a timeout so the ring breaks instead of hanging.\nMISLEADS lock identity is the receiver's TEXT: `this.lock` and `lock` are\n     two names for one monitor and read as two locks, while two different\n     objects both spelled `lock` read as one. Two methods that can never\n     run concurrently cannot deadlock however they order their locks.",
		run:   nil,
	},
	{
		name:  "lock-held-across-io",
		title: "A monitor held while doing IO, sleeping or allocating",
		notes: "ANSWERS where a critical section's duration is somebody else's latency.\n     This is what a profiler shows as time parked in lock with no clue\n     why, and it is the difference between a lock that scales and one\n     that serialises the whole service.\nACT copy what you need out of the guarded state, release, then do the IO.\n     holds_call with a high callee count is the same problem one frame\n     removed -- you do not know what that callee does.\nMISLEADS for an explicit lock() the guarded region is the following try\n     block when there is one and the enclosing block otherwise, which\n     OVER-estimates: statements after the unlock can be counted in. For\n     synchronized the region is exact. Check the `kind` column before\n     acting on a row.",
		run:   nil,
	},
	{
		name:  "vt-pinning-frontier",
		title: "Virtual-thread roots reaching JNI or FFM -- NOT synchronized",
		notes: "ANSWERS what still pins a carrier thread after JEP 491. In JDK 24 the\n     `synchronized` and Object.wait pinning was REMOVED, along with\n     -Djdk.tracePinnedThreads. A synchronized block inside a virtual\n     thread is a NON-FINDING and this query deliberately does not report\n     one. What is left is JNI, native methods and FFM downcalls.\nACT a pinned carrier blocks every other virtual thread scheduled on it.\n     Move the native call behind a bounded platform-thread executor, or\n     accept it and size the carrier pool for it.\nMISLEADS depth is capped at 4 hops over resolved edges. Check\n     meta.java_release first: below 21 there are no virtual threads and\n     every row here is inapplicable; below 24 synchronized pins too and\n     this query is then INCOMPLETE rather than wrong.",
		run:   nil,
	},
	{
		name:  "threadlocal-leak-on-pooled",
		title: "ThreadLocal set with no remove, reachable from a POOLED executor",
		notes: "ANSWERS the classic container leak: a ThreadLocal set on a pooled worker\n     outlives the request, pins whatever it references, and in a web\n     container pins the whole webapp classloader across a redeploy.\nACT set in a try, remove in the finally. Every time, not just on the\n     happy path.\nMISLEADS a virtual thread is DELIBERATELY excluded from the roots here: it\n     dies with its task, so a ThreadLocal it set cannot leak, and\n     including it would fill this list with non-findings. That is why\n     is_pooled_executor_root is a separate column from is_executor_root.\n     A ThreadLocal whose value is immutable and small leaks memory you\n     will never measure.",
		run:   nil,
	},
	{
		name:  "shared-mutable-statics",
		title: "Non-final static state in modules that start threads",
		notes: "ANSWERS what a race detector would find if the right two threads ever ran\n     together. SpotBugs MS_SHOULD_BE_FINAL raised to the module: a\n     mutable static plus a thread in the same module is unsynchronised\n     shared state waiting for load.\nACT make it final, or move it behind a holder with a lock, or make it an\n     Atomic. A static that is only written in a static initialiser and\n     read afterwards is already safe -- the JVM guarantees that.\nMISLEADS this counts declarations and thread-starting code in the same\n     module, not actual concurrent access, so a static written once at\n     class-init time is a false positive. volatile_fields is the\n     counter-evidence that somebody thought about it.",
		run:   nil,
	},
	{
		name:  "exception-contract-drift",
		title: "throws Exception, a swallowed catch, and a null return",
		notes: "ANSWERS where the type system stopped carrying information. `throws\n     Exception` tells a caller nothing, an empty catch discards the only\n     evidence of what went wrong, and returning null after both means the\n     failure arrives as an NPE three frames away with no stack trace\n     pointing anywhere near the cause.\nACT declare the exceptions you actually throw; if you catch, either\n     handle it, wrap it with the cause, or rethrow. Return Optional or\n     throw instead of returning null. Ranked by fan_in: the same sin in a\n     leaf that forty callers reach is forty times the confusion.\nMISLEADS a genuinely optional lookup returning null is idiomatic in older\n     Java and appears here. An empty catch with a comment explaining why\n     is fine and this cannot read the comment. Test scaffolding often\n     swallows deliberately, which is why test files are excluded.",
		run:   nil,
	},
	{
		name:  "n-plus-one",
		title: "A DAO or query method whose CALLER puts it in a loop",
		notes: "ANSWERS the N+1 no per-file linter can see, because the query lives in\n     one method and the loop that drives it lives in another. One page of\n     results turns into one round trip per row.\nACT batch-fetch, add a join fetch, or move the iteration into the query.\n     A JPA findById inside a loop over entities is the canonical form.\nMISLEADS a loop with a small constant bound is not an N+1 and trip count\n     is invisible here. A caller that loops over a two-element array and\n     queries once per element is fine. Confirm against the query log\n     before rewriting anything.",
		run:   nil,
	},
	{
		name:  "sql-concat-surface",
		title: "SQL activity beside string-built query text (OWASP G09)",
		notes: "ANSWERS functions that both execute SQL (a sql-category hazard call) and\n     carry query activity -- the surface where a query is assembled by\n     concatenation instead of parameters.\nACT use PreparedStatement placeholders; never splice a variable into a\n     query string.\nMISLEADS n_query_calls is ONE counter for two shapes: query-method calls\n     AND string literals with SQL text whose parent is a concatenation.\n     The concat bump cannot be isolated in SQL, so a function with only\n     constant queries ranks the same as one building them -- same-function\n     co-occurrence, NOT data flow. Bare execute/flush are absent from the\n     sql hazards by design (Executor.execute / Channel.flush in\n     event-driven code would flood the rows). Resolution is name-based.",
		run:   nil,
	},
	{
		name:  "false-sharing-and-escape",
		title: "Contended counters on one cache line, and allocations that escape",
		notes: "ANSWERS two things the JIT cannot fix for you. False sharing: several\n     mutable fields of one object written by different threads land on\n     one 64-byte line, and every write invalidates the other core's copy.\n     Escape: an object stored into a field or returned cannot be scalar-\n     replaced, so it is a real heap allocation however short its life.\nACT for false sharing, @jdk.internal.vm.annotation.Contended (with\n     -XX:-RestrictContended) or manual padding, or move the counters into\n     per-thread accumulators and merge -- LongAdder already does this. For\n     escapes, keep the object local, or reuse a buffer.\nMISLEADS this is a candidate list for a benchmark and nothing more. False\n     sharing only costs anything under real cross-core contention, and\n     escape analysis is a run-time decision that -XX:+PrintEscapeAnalysis\n     will answer and this cannot. Field ORDER in memory is chosen by the\n     JVM, not by declaration order, so 'same cache line' is a guess.",
		run:   nil,
	},
	{
		name:  "parallel-stream-hazard",
		title: "parallelStream() in a body that also blocks, locks or writes shared state",
		notes: "ANSWERS which parallel streams are actively harmful. They run on the\n     common ForkJoinPool, which the whole JVM shares: one blocking task\n     in there starves every other parallel stream in the process.\nACT if the body does IO, use a dedicated executor -- or virtual threads,\n     which exist for exactly this. If it takes a lock, the parallelism\n     is probably fictional. If it mutates shared state, it is a race.\nMISLEADS a parallel stream over a large in-memory collection doing pure\n     CPU work is exactly right, and will appear here if it happens to\n     sit near a lock. Check what the LAMBDA does, not the method.\n     fan_out rather than fan_in: a parallelStream is usually reached\n     through a framework or a lambda, so the enclosing method often\n     has no in-tree caller at all.",
		run:   nil,
	},
	{
		name:  "dead-code",
		title: "Nothing in this tree calls these",
		notes: "ANSWERS what might be deletable.\nACT grep the name as a STRING before deleting anything: a registry entry,\n     a config value or a reflective call keeps a symbol alive with no edge\n     to show for it.\nMISLEADS this is the query most likely to be wrong, and `graph-blindspots`\n     measures by how much. Public symbols are excluded because a caller\n     outside this tree cannot be seen at all, so what is left is private\n     and unreferenced -- a much weaker claim than dead. Methods of an\n     @HttpExchange interface are excluded explicitly: their\n     implementation is a generated proxy, so fan_in=0 is their NORMAL.",
		run:   nil,
	},
	{
		name:  "native-surface-reachable",
		title: "Runtime.exec / readObject / loadLibrary reachable from a public entry point",
		notes: "ANSWERS what find-sec-bugs and SpotBugs report one call at a time:\n     COMMAND_INJECTION, OBJECT_DESERIALIZATION and the JNI loaders. Each\n     alone is a fact, not a finding -- a loadLibrary in a static\n     initialiser is how JNI works. What matters is whether an outside\n     caller can steer one, so this walks the call graph from every public\n     or entry-point method and reports the ones that land on it.\nACT read `reached_from`: that is the method whose arguments an attacker\n     controls. Fewest hops first -- a 1-hop reach has almost no code\n     between the boundary and the sink.\nMISLEADS reachability is not taint. A method may reach exec() and pass it\n     only a constant. Depth is bounded at 4 hops, so a deeper path is not\n     seen, and reflection or a DI container breaks the edge entirely.",
		run:   nil,
	},
	{
		name:  "equals-hashcode-mismatch",
		title: "equals() overridden without hashCode() or vice versa (SpotBugs EI/EQ)",
		notes: "ANSWERS which types override equals() but not hashCode() (or vice versa),\n     violating the contract: equal objects must have equal hash codes.\n     A type in a HashMap/HashSet with this mismatch silently loses entries.\nACT implement both or neither. If equals is overridden, hashCode must use\n     the same fields.\nMISLEADS a type that is never hashed is technically safe, but the graph\n     cannot prove that. enum types auto-generate both and should be excluded.",
		run:   nil,
	},
	{
		name:  "thread-sleep-in-lock",
		title: "Thread.sleep() in a synchronized method or block (SpotBugs SWL)",
		notes: "ANSWERS where Thread.sleep is called while holding a lock, blocking other\n     threads unnecessarily. The lock is held for the full sleep duration.\nACT move the sleep outside the synchronized block, or use wait/notify.\nMISLEADS a sleep inside a lock that is intentionally serializing (e.g. a\n     rate limiter) is correct but rare.",
		run:   nil,
	},
	{
		name:  "double-checked-locking",
		title: "Broken double-checked locking pattern (PMD DC)",
		notes: "ANSWERS where the double-checked locking pattern is detected by the\n     analyzer's hazard scan: a null check followed by a synchronized block.\n     Without volatile, a partially constructed object can be published.\nACT use volatile + synchronized, or use an inner-holder idiom, or use\n     Supplier.computeIfAbsent.\nMISLEADS with volatile on the field, double-checked locking is correct in\n     Java 5+. The hazard scan is lexical, not dataflow.",
		run:   nil,
	},
	{
		name:  "string-concat-in-loop",
		title: "String concatenation with + inside a loop (PMD AppendCharacterWithChar)",
		notes: "ANSWERS where string concatenation happens inside a loop using the +\n     operator, which creates a new StringBuilder and String per iteration.\nACT use StringBuilder.append outside the loop, or collect parts and join.\nMISLEADS a loop with a small constant bound pays less than a StringBuilder.\n     concat_in_loop is a site count, not an allocation measurement.",
		run:   nil,
	},
	{
		name:  "executor-without-shutdown",
		title: "ExecutorService created but never shut down (SpotBugs/sonar)",
		notes: "ANSWERS where an ExecutorService is created but shutdown() is never called,\n     so threads keep running after the task is done.\nACT call shutdown() in a finally block or try-with-resources.\nMISLEADS a shared application-wide executor that lives for the JVM lifetime\n     should not be shut down per-task. The graph sees creation but not\n     lifecycle ownership.",
		run:   nil,
	},
	{
		name:  "submit-in-loop",
		title: "ExecutorService.submit inside a loop (PMD/sonar)",
		notes: "ANSWERS where tasks are submitted to an ExecutorService inside a loop\n     without bounding the queue, so the queue grows unboundedly.\nACT use a bounded queue, a Semaphore to limit in-flight tasks, or batch.\nMISLEADS a loop with a small constant bound and a bounded executor is fine.\n     n_submit_in_loop counts sites, not queue depth.",
		run:   nil,
	},
	{
		name:  "null-return-ignore",
		title: "Function that can return null with high fan_in (SpotBugs NP)",
		notes: "ANSWERS which widely-called functions return null, so every caller must\n     null-check. A high fan_in function returning null is a NullPointerException\n     factory.\nACT return Optional<T>, an empty collection, or a sentinel, instead of null.\nMISLEADS a function that returns null for a genuine 'not found' is correct\n     if the contract is documented. The graph sees the null return count\n     but not the contract.",
		run:   nil,
	},
	{
		name:  "static-mutable-state",
		title: "Static mutable fields written from non-static methods (SpotBugs ST)",
		notes: "ANSWERS where a non-static method writes to a static field, creating shared\n     mutable state that makes the class non-thread-safe and non-reentrant.\nACT make the field instance-scoped, or synchronize access, or use AtomicX.\nMISLEADS a static field written once in a static initializer or a\n     synchronized block is fine. The graph sees the write but not the\n     synchronization context.",
		run:   nil,
	},
	{
		name:  "weak-random",
		title: "java.util.Random for security-sensitive operations (SpotBugs/sonar)",
		notes: "ANSWERS where java.util.Random is used, which is predictable and not\n     cryptographically secure. Use SecureRandom for tokens, keys, IDs.\nACT replace with SecureRandom for security-sensitive uses.\nMISLEADS Random for simulation, testing, or load balancing is correct.\n     The graph sees the call, not its purpose.",
		run:   nil,
	},
	{
		name:  "weak-random-surface",
		title: "new Random() / Math.random construction sites (OWASP G06)",
		notes: "ANSWERS the constructor-level use of predictable randomness: new Random()\n     or Math.random() -- the sites where a token, ID or key could be\n     predicted. The companion weak-random query ranks the method-call\n     surface; this one ranks the construction surface.\nACT replace with SecureRandom for anything security-sensitive.\nMISLEADS the graph sees the call, not its purpose: Random for simulation,\n     testing or load balancing is correct. \"Security-adjacent\" context is\n     NOT modeled -- this is a surface, not a verdict. new SecureRandom is\n     excluded (it IS the fix). n_weak_random additionally counts\n     Random.nextInt/nextLong/Math.random calls AND falsely flags\n     SecureRandom.getInstance (a find-sec-bugs PREDICTABLE_RANDOM\n     heuristic), which is why this query reads the hazards table instead.",
		run:   nil,
	},
	{
		name:  "open-redirect-surface",
		title: "sendRedirect calls in methods that read request input (OWASP G26)",
		notes: "ANSWERS methods that call response.sendRedirect AND read HttpServletRequest\n     input (getParameter / getHeader / getCookies) -- the shape of an\n     unvalidated redirect: sendRedirect(request.getParameter(\"next\")).\nACT validate the target against an allowlist; never forward a\n     user-supplied URL.\nMISLEADS same-function co-occurrence is NOT data flow -- the input value\n     may never reach the redirect, and a constant redirect beside an\n     unrelated input read reads as a violation. The argument text is not\n     captured, so a fixed target cannot be told from an open one. The\n     sink is the bare sendRedirect base name, and the source is the\n     receiver set {request, req, httpRequest, servletRequest} -- an\n     input flow through a derived variable is invisible to both.",
		run:   nil,
	},
	{
		name:  "hardcoded-secret-candidates",
		title: "Credential-shaped string literals (OWASP G07)",
		notes: "ANSWERS string literals at least 12 chars long whose text names a\n     credential (password, token, api_key, secret, bearer, jwt, ...) --\n     the literal that a committed secret looks like.\nACT rotate and move to a secret manager; never commit the literal.\nMISLEADS a format string or test fixture containing the WORD token/pass\n     reads as a candidate (the filter is the literal's own text, not its\n     use); values over 200 chars are truncated at capture; a secret\n     built from parts or read from an env var is invisible here.\n     This is a candidate list, not a verdict.",
		run:   nil,
	},
	{
		name:  "xxe-parser-surface",
		title: "XML parser construction sites (OWASP G13)",
		notes: "ANSWERS methods that construct a parser (DocumentBuilderFactory,\n     SAXParserFactory, XMLReader, XMLInputFactory) -- the surface where\n     entity expansion is decided.\nACT disable external entities and DTDs (FEATURE_SECURE_PROCESSING,\n     disallow-doctype-decl) on every parser.\nMISLEADS the parser CONFIG is not modeled: a parser with entities\n     disabled ranks the same as one without. The capture is the bare\n     entry method name, so a factory wrapped in a helper is invisible.",
		run:   nil,
	},
	{
		name:  "zip-slip-surface",
		title: "Archive construction sites (OWASP G29)",
		notes: "ANSWERS methods that construct ZipFile / ZipInputStream / JarFile -- the\n     surface where an entry name becomes a filesystem path.\nACT validate every entry name against a containment check before\n     extraction; reject ../ and absolute paths.\nMISLEADS the containment check is not modeled: a method that checks each\n     name before extraction ranks the same as one that does not. The\n     capture is the constructor name, so a zip helper wrapped in another\n     class is invisible.",
		run:   nil,
	},
	{
		name:  "unauthenticated-input-surface",
		title: "Request input read with no auth call in the method (OWASP G01)",
		notes: "ANSWERS methods that read HttpServletRequest input and contain NO\n     auth-family call (securityContext, isAuthenticated, login, jwt) --\n     the surface where a controller method may be missing its\n     authorization check.\nACT add the security annotation or auth check; verify the route is in\n     the protected group.\nMISLEADS auth usually lives on a SECURITY FILTER, an @PreAuthorize\n     annotation, or a base controller -- annotations ARE visible\n     (attributes table) and exclude a method; a filter-chain or base-\n     class check still reads as open. A login or public endpoint\n     legitimately has no auth. The markers are name-based substrings.\n     Resolution is name-based.",
		run:   nil,
	},
	{
		name:  "overridden-not-annotated",
		title: "Method overrides a parent but @Override annotation is missing (PMD/sonar)",
		notes: "ANSWERS which methods are recorded in the overrides table without the\n     @Override annotation, so a parent signature change silently breaks the\n     override without a compiler error.\nACT add @Override to every method in the overrides table where is_annotated=0.\nMISLEADS a method that accidentally has the same signature as a parent\n     without intending to override will get a false @Override; but that is\n     a compiler error, so it is caught immediately.",
		run:   nil,
	},
	{
		name:  "hierarchy-depth",
		title: "Inheritance depth per class: the fragile-base-class meter",
		notes: "ANSWERS how many extends-hops sit between each class and its root\n     ancestor. Deep hierarchies are where a base-class change ripples\n     widest, and each level adds indirection that refactoring tools must\n     walk.\nACT prefer composition over inheritance above depth ~4; at minimum,\n     the deep rows are the ones to watch when the base changes.\nMISLEADS resolution of type_relations is by simple NAME, so two classes\n     sharing a name in different packages are conflated; depth is capped\n     at 10 hops (the bound in the recursion) and anything cycling through\n     a name loop stops there. Interface `extends` is excluded -- only\n     class extends is walked, matching what the compiler enforces.",
		run:   nil,
	},
	{
		name:  "di-bottleneck",
		title: "Annotation-heavy classes with the most inbound dependents",
		notes: "ANSWERS the classes a framework wire-up (annotations) AND the call graph\n     agree on as central: annotated types that also receive the most\n     calls. These are the beans a rename or signature change breaks across\n     the whole injection graph.\nACT before changing such a class, sweep its callers with git log; the\n     annotation count is the framework-lock-in half, fan_in the\n     compile-time half.\nMISLEADS annotation count is a lock-in PROXY: a class with three\n     unrelated annotations ranks as if framework-coupled. inbound_callers\n     counts distinct callers of any method the class owns, and a bean\n     reached purely through a container (reflection, proxied lookup) has\n     no edge and is invisible here.",
		run:   nil,
	},
	{
		name:  "overload-density",
		title: "Types with the most methods sharing one name",
		notes: "ANSWERS where overloading is densest: many same-named methods per owner.\n     Each overload is a call-distribution hazard -- the analyzer resolves\n     calls by simple name and cannot tell them apart, so ambiguity grows\n     with the count.\nACT if a name has many overloads, the callers deserve a look: a\n     re-ordered parameter list across overloads is how a call silently\n     binds to the wrong one.\nMISLEADS n_overloads counts (name, owner) collisions minus one; two\n     same-named methods in DIFFERENT owners each report n_overloads=0,\n     which is correct for dispatch but understates name noise.",
		run:   nil,
	},
	{
		name:  "iface-impl-ratio",
		title: "Interfaces by implementation breadth",
		notes: "ANSWERS the interface contracts with the most concrete implementors.\n     High breadth is a stable-seam signal; low breadth (with megamorphic-\n     callsites) is the dead-abstraction end.\nACT high-breadth rows are the interfaces to version carefully and\n     conformance-test; every new implementor multiplies the blast radius\n     of a signature change.\nMISLEADS n_impl_targets counts by simple-name matching against the\n     type_relations implementors list, so generics collapse and two\n     same-named types merge; only in-tree implementations are visible.",
		run:   nil,
	},
	{
		name:  "package-cycle",
		title: "Mutual file imports: the 2-cycle of the dependency graph",
		notes: "ANSWERS pairs of files that import each other. Two files can never be\n     loaded lazily this way, and the pair is where a cycle longer than 2\n     usually starts growing.\nACT break the cycle by moving the shared interface into a third file.\nMISLEADS finds 2-cycles of FILES only (imports.target_id), not packages\n     and not cycles of length >= 3 -- a longer cycle needs an SCC walk and\n     does not appear here. Java import statements name PACKAGES, so the\n     shared resolver matches ~0 imports on real corpora (documented in\n     CLAUDE.md as the correct answer, not a bug): this query returns rows\n     only where an in-tree FILE import happens (e.g. two files in the\n     same package importing each other's simple names), so on a real\n     Java corpus it is a true negative -- the fixture pair proves the\n     query is live, not dead. Simple-name import resolution means\n     same-named files in different packages can pair spuriously.",
		run:   nil,
	},
	{
		name:  "annotation-coupling",
		title: "Classes by annotation density: framework lock-in heat map",
		notes: "ANSWERS which classes carry the most annotations relative to their own\n     size -- the files most locked to whatever framework supplies those\n     annotations, and the hardest to port or mock.\nACT review whether the single-heavy file is doing one job through many\n     annotations (a god-class symptom) or is a legitimately framework-\n     bound adapter.\nMISLEADS n_annotations counts annotation SITES, so a file of ten\n     `@SuppressWarnings` ranks ahead of a service with one `@Service`;\n     density per sloc is the adjustment, and built-in markers like\n     @Override are counted as annotations too.",
		run:   nil,
	},
	{
		name:  "abstract-fanout",
		title: "Abstract methods with the most override implementations",
		notes: "ANSWERS the contract points every subclass must implement or inherit:\n     abstract methods whose override count is highest are the change\n     points that force edits across the widest subclass set.\nACT a change to an abstract method here is a change to every subclass\n     below it -- treat the top rows as breaking changes.\nMISLEADS override rows are matched by simple NAME to parent_type, so an\n     overloaded parent method merges its implementations; only in-tree\n     overrides count, and a method marked abstract by a supertype outside\n     the tree has no record here.",
		run:   nil,
	},
	{
		name:  "layer-violations",
		title: "Web-layer classes calling persistence-layer classes directly",
		notes: "ANSWERS edges that skip the service layer: a class named like a\n     controller/resource/servlet calling one named like a DAO/repository/\n     mapper. The heuristic is name-shape only -- we do not model Spring\n     stereotypes -- so the same rows describe both real violations and\n     false positives; the SME-layer name is the intended middle-man.\nACT for each row check whether a service-layer class mediates the call;\n     if not, the controller owns a data-access detail it should not.\nMISLEADS pure naming heuristics: a `UserRepository` used INSIDE a\n     `UserController` that is itself a legit bounded-context adapter is\n     reported. Names are boundary-tested (suffix match), not substring,\n     so `MyControllerHelper` does not match; annotations are not\n     considered, so a @RestController is detected only by name. Edges are\n     method-to-method, so the suffixes tested are the OWNER class names.",
		run:   nil,
	},
	{
		name:  "empty-catch-by-fanin",
		title: "Catch blocks that discard the exception entirely (PMD EmptyCatchBlock)",
		notes: "ANSWERS catch blocks whose body is empty -- the exception is swallowed\n     and the caller can never learn the failure -- ranked by how much of\n     the tree depends on the swallower.\nACT log, rethrow, or narrow the catch; empty is never the answer. A\n     comment inside the braces is not empty (the analyzer sees the\n     comment node), but a comment is still swallowing.\nMISLEADS deliberately broad boundary catches (a controller's top-level\n     try that converts everything to a 500) are the dominant legitimate\n     row; is_empty is structural (no named children), so a catch whose\n     body is only a comment does not fire.",
		run:   nil,
	},
	{
		name:  "try-in-loop",
		title: "Exception handlers inside loop bodies (perflint PERF203 analogue)",
		notes: "ANSWERS handlers inside loop bodies: a thrown exception walks the stack\n     per iteration, and caught-as-control-flow hides the cost.\nACT hoist validation out of the loop; prove the throw is exceptional.\nMISLEADS the try itself is JIT-cheap -- the THROW is the cost, and this\n     query cannot see throw frequency; a parse-until-valid retry loop is\n     the dominant legitimate row; is_broad names the catch-all shape.",
		run:   nil,
	},
	{
		name:  "files-stream-leak",
		title: "Files.lines / Files.walk / Files.list never closed",
		notes: "ANSWERS functions that open a file-backed Stream and never close it:\n     the file handle stays open until the stream is GC'd, which on a\n     busy server exhausts descriptors long before memory.\nACT use try-with-resources around the stream; a Stream is AutoCloseable.\nMISLEADS closed_in_fn is a text scan for .close() in the same body, so a\n     close one frame deeper (a helper) reads as absent; readAllLines and\n     the other List-returning forms are NOT file-backed streams and are\n     correctly absent from the capture.",
		run:   nil,
	},
	{
		name:  "banned-api-surface",
		title: "System.exit, Runtime.halt and Unsafe reachable from application code",
		notes: "ANSWERS call sites of the APIs disciplined JVM codebases ban: System.exit\n     anywhere but main, Runtime.halt (no shutdown hooks, no finally),\n     and sun.misc.Unsafe memory access.\nACT gate process-exit behind a dedicated lifecycle class (or delete);\n     replace Unsafe with VarHandle and the FFM API.\nMISLEADS the denylist is the hazard capture, which is name-based: the\n     bare-spelling form (`exit(...)` via a static import) and Thread.stop\n     are NOT captured and are absent; CLI tools and main methods are the\n     dominant legitimate row.",
		run:   nil,
	},
	{
		name:  "lock-on-boxed",
		title: "Synchronization on boxed-typed fields (Error Prone LockOnBoxedValues)",
		notes: "ANSWERS locks whose receiver is a field of a boxed type: the monitor\n     object is not the field but the boxed VALUE, and the box is\n     replaced on every assignment -- two threads can hold \"the same\"\n     lock on two different boxes.\nACT lock on a dedicated final Object field, never on a boxed value.\nMISLEADS lock_name is the receiver TEXT of the lock call, matched\n     against the owner class's fields by name; a local boxed variable\n     (not a field) is invisible; a lock on a String literal is caught\n     only when the string is a field.",
		run:   nil,
	},
	{
		name:  "static-write-in-ctor",
		title: "Constructors that write static fields",
		notes: "ANSWERS constructor-time writes to Class.staticField: every\n     construction overwrites shared state, so the last instance built\n     wins -- a cross-instance coupling that looks like per-instance\n     initialization.\nACT make the field instance-level, or initialize it in a static block\n     once and document the shared intent.\nMISLEADS the capture is any class-qualified write in the body; the\n     query reads constructors only, and a write through a local\n     object (`obj.field =`) reads as static here -- the row is the\n     review list, and `this.x =` is excluded by construction.",
		run:   nil,
	},
	{
		name:  "missing-super-call",
		title: "Framework lifecycle hooks that never call super()",
		notes: "ANSWERS overrides of the lifecycle-ish method names (onCreate, init,\n     doGet, service, onResume...) whose body has no super() call: the\n     parent's contract is silently skipped, and on Android-style\n     lifecycles that is a missing super call error waiting to ship.\nACT call super first, then the subclass work.\nMISLEADS name-based on the method name -- a hook named otherwise but\n     equally contract-bound is absent; a super call inside a lambda or\n     nested class in the body is still counted (per-body counter);\n     interfaces have no super and are excluded by the name list.",
		run:   nil,
	},
	{
		name:  "dead-exception",
		title: "new Exception(...); -- created, never thrown, never assigned",
		notes: "ANSWERS exception objects constructed in expression-statement position:\n     the statement does nothing, and its author almost certainly meant\n     to throw it -- the error path silently does nothing.\nACT throw it, assign it, or delete the line.\nMISLEADS the parent check is positional: `new X()` as the last call in\n     a method body whose next line is `throw` reads as dead here when\n     it is really a variable-holding idiom; a non-exception object\n     (`new StringBuilder()`) is correctly absent.",
		run:   nil,
	},
	{
		name:  "reference-equality",
		title: "== on non-literal operands in boxed-heavy code (Error Prone ReferenceEquality)",
		notes: "ANSWERS == / != comparisons between two non-literal operands in\n     functions that also box: Integer == Integer compares references,\n     not values, and the cache range (-128..127) makes it pass in\n     tests and fail in production.\nACT use .equals() (or Objects.equals) for values; keep == only for\n     identity, which this query cannot tell apart.\nMISLEADS co-occurrence, not types: n_ref_eq counts every non-literal\n     == in the body and n_boxing_sites every boxed operation -- a\n     body with `==` on two String CONCAT results plus unrelated\n     boxing reads as a violation; enum == and null checks are\n     excluded only when the operand is a literal.",
		run:   nil,
	},
	{
		name:  "narrow-calculation",
		title: "int arithmetic assigned to long (Error Prone NarrowCalculation)",
		notes: "ANSWERS `long x = a * b` where the product is computed in int width:\n     the multiplication overflows before the widening. A day counter\n     computing seconds overflowed for two billion of the same unit.\nACT widen one operand first (`(long) a * b` or `a * (long) b`).\nMISLEADS the parent is the variable declarator ONLY: a product\n     assigned through a cast or a helper is invisible; a long-typed\n     operand in the product is not distinguished from two int\n     operands -- the row is the review list, not a verdict.",
		run:   nil,
	},
	{
		name:  "modern-idiom-candidates",
		title: "Pattern instanceof, arrow switch, text blocks (OpenRewrite fixes)",
		notes: "ANSWERS functions already touching one modern idiom: the migration\n     surface for the rest. Pattern matching instanceof and arrow\n     switches are the two biggest readability wins per edit.\nACT apply the remaining idioms in the row's body; OpenRewrite is the\n     mechanical half.\nMISLEADS text-matched: a `->` inside a lambda in a switch arm or a\n     comment reads as an arrow switch; a text block of size one line\n     is still counted; this ranks bodies that STARTED the migration,\n     not bodies that need it from zero.",
		run:   nil,
	},
	{
		name:  "flex-constructor-prologues",
		title: "JEP 513: constructors running statements before super()/this()",
		notes: "ANSWERS which constructors use flexible constructor bodies (Java 25,\n     final in JEP 513): validation or field computation BEFORE the\n     super call. The prologue cannot read instance state -- not even\n     fields of the class being built -- so any code there that looks\n     at `this` is a compile error waiting for the next edit.\nACT keep prologues to argument validation and static helpers; move\n     anything that touches instance state after the super call.\nMISLEADS tree-sitter-java 0.23.x does not know JEP 513: it recovers\n     the constructor (prologue statements survive and ARE counted)\n     but emits one ERROR node per site, so files.n_parse_errors\n     overcounts by exactly this many. The super()/this() invocation\n     itself is dropped from the tree, so n_super_calls undercounts\n     here by one.",
		run:   nil,
	},
	{
		name:  "resilience-annotation-surface",
		title: "Spring Framework 7 @Retryable / @ConcurrencyLimit sites",
		notes: "ANSWERS where framework-native resilience is declared: retry with\n     backoff, concurrency limits, circuit breakers. A @Retryable\n     multiplies every side effect inside the method by maxAttempts --\n     an insert retried 3 times is three inserts unless it is\n     idempotent, and a retry around non-atomic state writes is a\n     corruption generator.\nACT check idempotency FIRST on every row that also writes state; a\n     @ConcurrencyLimit number that exceeds the downstream pool size\n     is decoration.\nMISLEADS counts SITES, not activation: these annotations are inert\n    unless @EnableResilientMethods (or the equivalent config) is\n    present somewhere, which this scan does not chase; jakarta or\n    SmallRye annotations sharing the simple name are counted too.",
		run:   nil,
	},
	{
		name:  "http-exchange-clients",
		title: "Spring 7 declarative HTTP clients (@HttpExchange interfaces)",
		notes: "ANSWERS which interfaces are declarative HTTP clients: their methods\n     have NO implementation in this tree -- Spring generates the proxy\n     from the annotations. Every one reads as dead code and every one\n     is a network boundary whose timeouts, retries and error mapping\n     live entirely in configuration.\nACT audit each client's @GetExchange/@PostExchange set against the\n     remote service's actual contract; a renamed remote endpoint\n     surfaces here as nothing at all until runtime.\nMISLEADS recognition is by the annotation simple name only -- a\n     custom meta-annotation wrapping @HttpExchange is invisible;\n     interface default methods are real code, not proxy stubs, so a\n     default method on such an interface is ordinary Java.",
		run:   nil,
	},
	{
		name:  "api-version-drift",
		title: "Spring Framework 7 API versioning: same path, different versions",
		notes: "ANSWERS version-skew inside one controller: methods mapped to the same\n     path (or same name) carrying different `version` attributes. The\n     whole point of first-class API versioning is that v1 and v2 of an\n     operation stay reviewable side by side; when they drift apart in\n     behaviour without a version bump, clients silently get the old\n     semantics.\nACT pair each row's versions and diff them; if they differ beyond the\n     intended change, bump the version attribute instead of editing in\n     place.\nMISLEADS pairs by METHOD NAME, which catches the common\n     sayHello-v1/sayHello-v2 spelling but misses renamed pairs; the\n     version attribute lives on the annotation, so a controller-level\n     version inherited by all methods shows as zero per-method\n     attributes here.",
		run:   nil,
	},
	{
		name:  "jspecify-null-contract-violations",
		title: "@NonNull parameters on methods that can return null (Spring 7 JSpecify)",
		notes: "ANSWERS where JSpecify nullability (Spring 7's adopted standard) makes\n    a contract the implementation breaks: the method takes @NonNull\n    parameters and also contains `return null`. Callers compiled\n    against the annotations will trust them; the null arrives anyway.\nACT either drop the null return (Optional, a sentinel, or throw) or\n    annotate the return @Nullable and force every caller to handle it.\nMISLEADS the null-return count is textual (`return null`); a null\n    returned only behind a guard that proves impossibility still\n    counts, and a @Nullable RETURN annotation (rather than parameter)\n    is correct here and indistinguishable from none at this scan's\n    granularity.",
		run:   nil,
	},
	{
		name:  "notify-without-notifyall",
		title: "Object.notify() where notifyAll() is the safer contract (PMD UseNotifyAllInsteadOfNotify)",
		notes: "ANSWERS monitor wake-ups that pick ONE arbitrary waiter. If two threads\n     wait for different conditions on the same monitor, notify() wakes\n     the wrong one and both stall -- the lost-wakeup shape. The graph\n     adds what PMD cannot: fan_in says how many code paths can be\n     waiting, and the same-file wait() count says whether multiple\n     conditions share the monitor.\nACT replace with notifyAll() unless every waiter waits on the SAME\n     predicate in a loop -- then notify() is correct and cheaper.\nMISLEADS single-waiter monitors are common and correct; check the\n     wait loop's predicate before acting. Counted by simple name, so\n     custom notify() methods on other classes count too.",
		run:   nil,
	},
	{
		name:  "thread-run-not-start",
		title: ".run() called directly: executes in the CALLER'S thread (PMD DontCallThreadRun)",
		notes: "ANSWERS task launches that never launched: `x.run()` executes the body\n     inline, synchronously -- no new thread, no concurrency, and any\n     blocking inside it now blocks the caller. The author almost always\n     meant `x.start()`. The query ranks by whether the same file also\n     allocates Threads/executors, which separates real launch sites\n     from same-named run() helpers.\nACT replace .run() with .start(), or extract a Runnable and pass it to\n     the executor you already have.\nMISLEADS counted by simple NAME on any receiver -- a genuine call to a\n    domain method named run() (a benchmark harness, Runnable.run passed\n    deliberately inline) counts too; the file-level Thread-allocation\n    column is the tiebreaker, not proof.",
		run:   nil,
	},
	{
		name:  "bigdecimal-from-double",
		title: "new BigDecimal(double): binary error baked into money math (SpotBugs DMI_BIGDECIMAL)",
		notes: "ANSWERS BigDecimal constructions from floating-point literals or\n     variables: new BigDecimal(0.1) is exactly\n     0.1000000000000000055511151231257827... -- the double's binary\n     error, preserved forever in your 'exact' decimal. Money math that\n     chose BigDecimal for correctness keeps the bug it chose it to\n     avoid.\nACT use the String constructor or BigDecimal.valueOf(double), which\n     routes through Double.toString.\nMISLEADS identifier-typed arguments count too (a double variable may\n    hold an exact value like 0.5); only literals and bare identifiers\n    are captured -- a method call returning double is not seen and may\n    still construct imprecise values.",
		run:   nil,
	},
	{
		name:  "proxy-bypass-self-invocation",
		title: "@Transactional/@Async/@Cacheable called ONLY from the same bean: the proxy is bypassed",
		notes: "ANSWERS the Spring defect no linter can see: proxy-managed annotations\n     (@Transactional, @Async, @Cacheable, @CacheEvict, @CachePut,\n     @Caching, @Retryable, @Validated) on methods whose only inbound\n     resolved calls come from a sibling in the SAME bean. The reference\n     says it plainly: in proxy mode, self-invocation does not lead to\n     an actual transaction -- and the same interceptor machinery carries\n     the rest of the family, so the retry, the cache and the async hop\n     are all skipped too.\nACT move the annotated method into another bean, inject the bean into\n     itself, or drop the annotation and call the behaviour directly\n     without expecting the semantics.\nMISLEADS resolves calls by simple name within the bean, so an external\n     call that resolved to the method through a same-named overload in\n     another class hides the bypass; AspectJ-mode weaving (mode=ASPECTJ)\n     makes self-invocation WORK, and this query has no way to see that\n     configuration. Test-file callers are ignored by design.",
		run:   nil,
	},
	{
		name:  "transactional-checked-exception-commit",
		title: "@Transactional without rollbackFor on a method that declares checked exceptions: it COMMITS",
		notes: "ANSWERS the default-rollback trap: Spring rolls @Transactional back on\n     RuntimeException and Error ONLY. A method that declares (or\n     throws) a checked exception and carries @Transactional with no\n     rollbackFor has every write COMMITTED on the failure path -- the\n     caller saw the exception and assumes the transaction unwound. It\n     did not.\nACT add rollbackFor=Exception.class, throw a runtime exception, or move\n     the checked failure outside the transaction boundary. Then verify\n     every caller actually compensates on the exception.\nMISLEADS the throws-declaration count is a floor for checked failure\n     paths: an unchecked exception thrown from a helper reached by this\n     method rolls back and never appears here. Args text is truncated\n     at 200 chars, so an annotation whose rollbackFor sits beyond that\n     reads as absent.",
		run:   nil,
	},
	{
		name:  "prototype-bean-into-singleton",
		title: "Prototype/request-scoped bean field-injected into a singleton: ONE instance for the whole app",
		notes: "ANSWERS the Spring scope-capture defect: a field whose declared type is\n     a @RequestScope/@SessionScope/@Scope(\"prototype\") bean, living in\n     a singleton-stereotyped class (@Component/@Service/...). The\n     reference is explicit that a prototype injected into a singleton\n     is injected ONCE: every request thread shares that one 'per-\n     request' instance, with its state and its ThreadLocals.\nACT inject ObjectProvider<T> / Provider<T> and call getObject() per\n     use, or make the scoped bean a method parameter (or use\n     @Lookup). Delete the field.\nMISLEADS matches the field's declared type by simple NAME across the\n     tree, so two same-named classes in different packages can create a\n     false row (check the import); constructor/parameter injection is\n     the same defect and is NOT listed -- only fields are visible to\n     this scan.",
		run:   nil,
	},
	{
		name:  "returned-resource-never-closed",
		title: "Method opens a closeable, returns it, and NO caller ever closes anything",
		notes: "ANSWERS the ownership half of Sonar S2095 that per-method checkers\n     cannot reach: the method opens a resource outside try-with-\n     resources and hands it back as its return value (Stream, Reader,\n     Connection...), but not one caller of the method closes anything.\n     The opener is fine; the LEAK lives in every caller that treats the\n     return value as self-cleaning.\nACT wrap the call site in try-with-resources, or push the opening into\n     the callers' try-with-resources and return a supplier instead.\nMISLEADS n_closing counts callers that close ANYTHING or use try-with-\n     resources -- it cannot prove they close THIS return value, and a\n     close two frames deeper is invisible. Return types are matched by\n     simple name, so a same-named non-closeable in another package\n     can appear.",
		run:   nil,
	},
	{
		name:  "lock-acquire-without-release",
		title: "Explicit Lock acquired, never released in the method -- every caller inherits the leak",
		notes: "ANSWERS the cross-function face of Sonar S2222: the rule only checks\n     the acquiring method, but the CONSEQUENCE is cross-function --\n     callers.length is how many code paths silently inherit a lock that\n     is never given back on some path (an exception between lock() and\n     unlock() that has no finally). One bad method starves every caller.\nACT move the unlock into a finally, or switch to try-with-resources\n     with a close()=unlock adapter. Check each caller's error paths\n     after fixing.\nMISLEADS deliberate hand-offs (acquire here, release on another\n     thread through a queue) are real designs and appear here; only\n     explicit java.util.concurrent Lock acquires are listed --\n     synchronized releases itself at block exit and is excluded.",
		run:   nil,
	},
	{
		name:  "transitive-block-under-lock",
		title: "Guarded region calls out to a method that blocks -- the blocking lives 1-2 hops away",
		notes: "ANSWERS the transitive version of lock-held-across-io: the critical\n     section itself is clean, but it CALLS a helper whose body sleeps,\n     waits, does IO or runs queries. Every thread contending the lock\n     now waits on somebody else's database. Per-method checkers see\n     neither half of this; only the call graph connects them.\nACT hoist the call outside the guarded region, or pre-compute what the\n     helper needs. If the call is required, document that the lock is\n     held for the helper's worst-case latency.\nMISLEADS capped at 2 hops over RESOLVED edges, so blocking behind an\n     interface dispatch to 2+ implementations is invisible; a helper's\n     n_io/n_wait counts prove the calls EXIST, not that they execute on\n     every path through the guarded region.",
		run:   nil,
	},
	{
		name:  "wait-notify-outside-sync",
		title: "wait()/notify() outside any synchronized block, on a monitor OTHER methods lock",
		notes: "ANSWERS the cross-method monitor mismatch (IntelliJ 'wait()/notify()\n     outside synchronized', SpotBugs MWN family): a wait or notify\n     whose call site sits in NO synchronized region of its method,\n     while the same monitor name IS locked by synchronized blocks\n     elsewhere in the tree. wait() outside the monitor's synchronized\n     region throws IllegalMonitorStateException -- or, if the author\n     'fixed' that by synchronizing the wrong object, it hangs forever.\nACT put the wait/notify inside synchronized (theMonitor) with its\n     condition check in a while loop, or move to a\n     java.util.concurrent primitive (BlockingQueue, Condition).\nMISLEADS the monitor is the textual receiver (`queue` in queue.wait()),\n     matched by name against lock_ops targets, so an aliased local and\n     a field can collide; a method that synchronizes on a DIFFERENT\n     object via a computed expression reads as unsynchronized here.",
		run:   nil,
	},
	{
		name:  "interrupt-swallowed",
		title: "InterruptedException caught, never rethrown, interrupt flag never restored (S2142)",
		notes: "ANSWERS where the cancellation signal dies: a catch of\n     InterruptedException whose body neither rethrows nor calls\n     interrupt() again (Sonar S2142, Error Prone\n     InterruptedExceptionSwallowed). The thread's interrupted status is\n     CLEARED the moment the catch runs; swallowing it means executor\n     shutdown, future cancellation and deadline timers stop working\n     through this code -- and callers up the stack never learn.\nACT restore the flag (Thread.currentThread().interrupt()) in every\n     catch you cannot rethrow, or wrap in InterruptedException and\n     rethrow. Rank by callers: every one of them is now uncancellable.\nMISLEADS a body that handles cancellation some other way -- parking,\n     a volatile cancelled flag checked elsewhere -- reads as swallowed\n     because the scan looks for the literal interrupt() call; a catch\n     that delegates to a helper which restores the flag is invisible.",
		run:   nil,
	},
	{
		name:  "shared-format-field-use",
		title: "Methods using a shared SimpleDateFormat/NumberFormat/Calendar field: not thread-safe",
		notes: "ANSWERS shared non-thread-safe formatters (PMD UnsynchronizedStatic-\n     Formatter family): SimpleDateFormat, NumberFormat, DecimalFormat\n     and Calendar all MUTATE internal state when used, and a field of\n     one of these types is shared by every caller of the class. Two\n     threads formatting concurrently get garbled dates or\n     ArrayIndexOutOfBoundsException deep inside DateFormat.\nACT make the field a per-call local, or switch to DateTimeFormatter\n     (immutable and thread-safe), or guard every use with a lock.\nMISLEADS single-threaded classes (a command-line tool, a\n     ThreadConfined worker) are correct and appear here; only fields of\n     the OWNING class are visible, so a formatter borrowed through a\n     getter from another class is not counted.",
		run:   nil,
	},
	{
		name:  "string-format-in-loop",
		title: "String.format-style formatting inside a loop, on the hot paths callers actually hit",
		notes: "ANSWERS per-element formatting cost: .format(...) called inside a loop\n     re-parses the format string for EVERY element (general knowledge;\n     same family as PMD's append-in-loop rules). The graph adds which\n     of these sites are hot: callers and loop depth turn a micro-\n     inefficiency into a profileable sink.\nACT hoist a MessageFormat/compiled format out of the loop, or build\n     with StringBuilder when no localization is needed.\nMISLEADS matched by the base name format, so LocalDate.format in a\n     loop counts too -- also a per-element cost, but a different fix;\n     a format call inside a STREAM pipeline's lambda may sit outside\n     the textual loop and be missed.",
		run:   nil,
	},
	{
		name:  "common-pool-from-entry",
		title: "parallelStream() on the COMMON pool, reachable from a request entry point",
		notes: "ANSWERS the transitive version of parallel-stream-hazard: the\n     parallelStream() itself sits in a helper, but the path that\n     triggers it starts at a request handler or public entry point.\n     Parallel streams run on the shared ForkJoinPool.commonPool -- one\n     request-driven parallel fan-out starves every OTHER consumer of\n     the common pool in the JVM, including unrelated background work.\nACT inside request paths use a dedicated ForkJoinPool/submission\n     executor, or a plain stream. Reserve commonPool for batch tools\n     that own the process.\nMISLEADS capped at 3 hops over RESOLVED edges (a floor, never a\n     ceiling); parallelism behind a framework-dispatched interface\n     method has no edge and cannot appear; n_paths counts DISTINCT\n     entry roots, not runtime frequencies.",
		run:   nil,
	},
	{
		name:  "static-write-from-entry",
		title: "Static mutable state written on a path reachable from a request entry point",
		notes: "ANSWERS the reachability half of the shared-statics story that Q8/Q23\n     cannot see: which static-field WRITES are on live request paths?\n     A static write in a bootstrap tool is config; the same write\n     reached from a handler is a data race between request threads on\n     every request. Reachability, not just presence, is what a reviewer\n     needs to triage.\nACT make it immutable, confine it to the request (a local or a\n     request-scoped bean), or guard every read AND write with one lock\n     -- and check the OTHER writers the query does not show.\nMISLEADS capped at 3 hops over RESOLVED edges; a write reached only via\n     framework reflection (no call edge) cannot appear; n_entry_paths\n     counts distinct entry roots, not request frequencies -- a write on\n     one rarely-hit admin path ranks the same as a hot one.",
		run:   nil,
	},
	{
		name:  "listener-add-remove-imbalance",
		title: "Classes registering listeners/handlers with no removal anywhere in the class",
		notes: "ANSWERS the listener-lifetime ledger: addXxxListener/addXxxHandler\n     calls versus removeXxxListener/removeXxxHandler calls, per class.\n     A registration without a removal pins the listener (and everything\n     it captures) for the life of the SUBJECT -- the classic listener\n     leak, and the classic Android/ClassLoader/ApplicationContext leak\n     shape. Per-file linters see one call site; the ledger needs the\n     whole class (and its whole lifetime).\nACT pair every add with a remove in the symmetric lifecycle hook\n     (dispose/destroy/onDestroy), or use a weak listener API.\nMISLEADS global listeners that SHOULD live for the process lifetime\n     (a metrics registry, a shutdown hook registered once) are correct\n     and appear here; classes are matched by simple name, and a removal\n     that lives in a DIFFERENT class than the add reads as imbalance.",
		run:   nil,
	},
	{
		name:  "expression-eval-from-input",
		title: "SpEL/ScriptEngine evaluation reachable from entry points or sharing the method's input reads",
		notes: "ANSWERS the dynamic-evaluation sink of the OWASP injection family:\n     parseExpression (SpEL), eval (ScriptEngine), evaluate\n     (ELProcessor) -- sites where a string becomes CODE -- that are\n     reachable from request handlers/entry points, or that live in a\n     method that itself reads request input. CodeQL's expression-\n     injection family: the graph supplies the reachability half.\nACT never pass raw input to an evaluator; allow-list the expression\n     grammar, use SimpleEvaluationContext (SpEL) with no type\n     references, or pre-compile constant expressions.\nMISLEADS reachability is capped at 3 hops over RESOLVED edges and is\n     NOT taint: a constant expression reached from a handler is a\n     non-issue. `eval` is matched by simple name, so a domain method\n     called eval on an unrelated class counts -- check the owner.",
		run:   nil,
	},
	{
		name:  "volatile-compound-update",
		title: "volatileField++ / += on a volatile field: the compound update is not atomic (Error Prone)",
		notes: "ANSWERS Error Prone NonAtomicVolatileUpdate: a compound update\n     (++, --, +=, -=) of a volatile field is a read-modify-write, and\n     volatile gives visibility, NOT atomicity -- two threads updating\n     concurrently lose increments forever. The field being volatile\n     makes the author FEEL safe, which is exactly why the bug ships.\nACT replace with AtomicInteger/LongAdder (or any CAS), or guard every\n     access to the field with one lock. Then check the readers the\n     volatile was bought for: they keep working unchanged.\nMISLEADS fields are matched by simple name within the owner class, so\n     a shadowing local of the same name can produce a row; a compound\n     update provably confined to one thread ( constructors, thread-\n     confined builders) is a false positive here.",
		run:   nil,
	},
	{
		name:  "manual-thread-allocation",
		title: "new Thread(...) beside existing executor/virtual-thread infrastructure",
		notes: "ANSWERS unmanaged threads: `new Thread(...)` sites in files that also\n     own executors or virtual-thread roots. Two thread-management\n     regimes in one file means one of them is bypassing the lifecycle\n     -- no shutdown, no naming, no queueing, no backpressure -- and\n     `new Thread` per request is an unbounded thread factory pointed at\n     production (general knowledge; the DeadThread-adjacent shape).\nACT submit to the existing executor instead; if a dedicated thread is\n     genuinely required, name it and own its shutdown explicitly.\nMISLEADS the infra column is file-granular: a main() that builds the\n     executor and a helper that spawns one named daemon in the same\n     file can be a legitimate pair; Thread SUBCLASSES are not counted\n     (exact `new Thread` only).",
		run:   nil,
	},
	{
		name:  "scheduled-overlap-risk",
		title: "@Scheduled tasks whose body does IO/locking: overlap and starvation risk",
		notes: "ANSWERS the scheduling defect family from the Spring reference: a\n     fixedRate task that runs longer than its period piles up (and with\n     a pool larger than one thread, OVERLAPS itself); the default\n     single-thread scheduler serializes ALL @Scheduled methods behind\n     the slowest one. An @Scheduled method that does IO, runs queries\n     or takes locks is the one that makes every other task late.\nACT prefer fixedDelay for anything with IO, or add\n     @Async/scheduler pool sizing and make the task idempotent under\n     overlap. Check what ELSE is scheduled in this module (see the\n     scheduler-surface metric) before resizing.\nMISLEADS activation is a configuration fact: whether the scheduler has\n     one thread or eight lives in config this scan does not read; the\n     cost column counts SITES, so an IO call behind a conditional reads\n     the same as one on every execution.",
		run:   nil,
	},
	{
		name:  "event-listener-sync-burden",
		title: "@EventListener/@Subscribe handlers doing IO: they run synchronously in the PUBLISHER's thread",
		notes: "ANSWERS the eventing defect from the Spring reference (and Guava's\n     EventBus docs): listeners run inline in whatever thread PUBLISHES\n     the event unless someone explicitly configured async dispatch.\n     A listener that does IO, runs queries or waits therefore extends\n     the publisher's transaction and its latency -- and a handler on a\n     request path silently inherits every listener's runtime.\nACT annotate the listener @Async, move the work to a queue, or split\n    the event into an acknowledgement plus a job. Then measure the\n    publisher's new tail latency.\nMISLEADS recognition is by annotation simple name; a context WIDE\n    async multicaster (ApplicationEventMulticaster taskExecutor) makes\n    every row here a non-issue, and this scan cannot see that config;\n    the cost column counts sites, not executed frequency.",
		run:   nil,
	},
	{
		name:  "cache-evict-drift",
		title: "@CacheEvict on cache names that NO @Cacheable/@Caching in the tree populates",
		notes: "ANSWERS cache-name drift: @CacheEvict (or @CachePut) naming a cache\n     that nothing @Cacheable in this tree ever populates. Either the\n     name is a typo silently evicting nothing (the stale entry stays\n     hot), or the producer lives outside this tree and the coupling is\n     invisible -- both are review facts, and the first is a live\n     correctness bug in production caching.\nACT diff the name against the producer; fix the typo or document the\n     external producer next to the annotation.\nMISLEADS names are compared as the RAW annotation-args text, so\n     @Cacheable(value=\"a\") vs @CacheEvict(\"a\") differ textually and\n     read as drift when they are the same cache; multi-name annotations\n     truncated at 200 chars can miss a real match.",
		run:   nil,
	},
	{
		name:  "private-proxy-annotation",
		title: "@Transactional/@Async/@Cacheable on a PRIVATE method: the proxy never sees it",
		notes: "ANSWERS the hard boundary of Spring proxy semantics the reference\n     states for visibility: private methods are never advised --\n     neither JDK proxies (which only see interface methods) nor CGLIB\n     subclasses (which cannot override private) can intercept them.\n     The annotation parses, the IDE paints it, and at runtime NOTHING\n     it promises happens: no transaction, no cache, no async hop, no\n     retry.\nACT make the method public on an interface (JDK proxy) or at least\n     public/protected on a class proxy -- Spring 6.0+ advises protected\n     and package-visible on class proxies -- and move the logic into a\n     collaborator bean instead.\nMISLEADS pure AspectJ weaving DOES advise private methods; recognition\n     is by annotation simple name, so a NON-Spring annotation that\n     happens to share a name counts too. Protected/package-private on\n     class proxies is legal since 6.0 and deliberately NOT listed.",
		run:   nil,
	},
	{
		name:  "static-collection-grows-never-pruned",
		title: "Static collection fields with add/put calls and no clear/remove anywhere in the class",
		notes: "ANSWERS unbounded growth: classes whose static collection fields get\n     add/put/offer calls but where NO method in the class ever calls\n     remove/clear on them. Every key that arrives once stays forever --\n     a slow heap leak that profiles as 'old gen', usually keyed by\n     user, session or filename. No per-file linter can see the ABSENCE\n     of a pruning method; that is a whole-class (graph) fact.\nACT bound it: a maximum size with eviction (Caffeine, an LRU), or a\n     removal on the symmetric lifecycle event. If it is genuinely a\n     process-lifetime registry, say so in a comment and bound the KEY\n     domain instead.\nMISLEADS receivers are matched by field NAME, so a same-named local\n     collection's add() counts and a differently-named alias of the\n     static hides it; pruning via `set`/replace-style calls is not\n     counted as removal and reads as growth.",
		run:   nil,
	},
	{
		name:  "shared-bean-mutable-collection",
		title: "Mutable (non-concurrent) collection fields inside singleton-stereotyped beans",
		notes: "ANSWERS shared-state-on-a-singleton: instance fields whose type is an\n     ordinary (non-concurrent) collection, in a class annotated with a\n     singleton stereotype (@Component/@Service/@Repository/...). One\n     bean instance serves every request thread; an ArrayList/HashMap\n     field on it is unsynchronized shared mutable state -- corrupted\n     under load, and invisible in single-threaded tests.\nACT switch to a concurrent type (ConcurrentHashMap,\n     CopyOnWriteArrayList), make the field immutable, or move the\n     state into the request scope where it belongs.\nMISLEADS thread-safety is judged by the declared SIMPLE type name, so\n     a thread-safe WRAPPER created at construction\n     (Collections.synchronizedList) reads as unsafe; beans whose\n     stereotype is custom meta-annotated are invisible to this scan.",
		run:   nil,
	},
}

var metrics = []query{
	{
		name:  "graph-blindspots",
		title: "Read this first: where the call graph cannot see",
		notes: "ANSWERS how much of every other answer here is guesswork. Java is the\n     worst case for this: Spring, JPA, JUnit, ServiceLoader and every\n     `Class.forName` invoke code with no call site in the source, so a\n     method can be live and still have fan_in=0. @HttpExchange client\n     interfaces are the newest member of that family -- their methods\n     are implemented by a generated proxy -- which is why they carry\n     is_http_exchange_client=1 and are exempt from dead-code.\nACT external calls leave the tree by design (JDK, dependencies) and are\n     NOT counted as blindness. Unresolved means we lost it -- usually an\n     interface method with several implementations. Read reflect_ and\n     framework_entries as the size of the graph that does not exist.\nMISLEADS sql_ops comes from a bare METHOD NAME list, so findAll,\n     getSingleResult and friends match ANY receiver. In a codebase with\n     no database at all these still fire. Check that the owner type is a\n     repository or a Connection before believing the row.\n     a resolved edge can still be wrong: a call on an interface\n     resolves to whichever single implementation exists, and where two\n     exist this refuses to guess and lands in unresolved instead. An\n     allocation resolves to the constructor when one is declared and to\n     nothing when the class uses the default constructor.",
		run:   nil,
	},
	{
		name:  "per-element-cost",
		title: "String +, boxing, Pattern.compile and prepareStatement inside loops",
		notes: "ANSWERS the work that multiplies by the trip count: a `+` on String in a\n     loop allocates a new StringBuilder every iteration, Integer.valueOf\n     outside the -128..127 cache allocates, Pattern.compile re-parses the\n     regex, and prepareStatement in a loop is SpotBugs\n     IIL_PREPARE_STATEMENT_IN_LOOP.\nACT hoist the compile and the prepare out of the loop; one StringBuilder\n     for the whole loop; primitive collections or arrays instead of boxed\n     ones. Weighted by fan_in because a leaf that fifty callers reach pays\n     fifty times.\nMISLEADS none of this is confirmed without a profiler. javac already\n     rewrites simple concatenation to invokedynamic/StringConcatFactory,\n     which is fast; the loop-carried case it cannot fix. Trip count is\n     invisible here, and a loop bounded by 3 costs nothing.",
		run:   nil,
	},
	{
		name:  "megamorphic-callsites",
		title: "Interfaces with 3+ implementations, invoked from inside a loop",
		notes: "ANSWERS where the JIT cannot inline. One or two receiver types at a call\n     site stay monomorphic or bimorphic and inline; three or more go\n     megamorphic, and the call becomes a real vtable dispatch that also\n     blocks every optimisation downstream of it.\nACT this is a candidate list for a benchmark, not a defect list. Where it\n     matters, split the loop by type, or make the hot path take the\n     concrete type. n_impls is also a design signal: 1 means the\n     interface is an abstraction over nothing.\nMISLEADS implementation counting is structural and by simple name, so an\n     implementor in a dependency, or generated by a mock framework, is\n     invisible -- the true count is a floor. And a call site is only\n     megamorphic if the receivers actually VARY at run time; three\n     implementations of which one is ever loaded stays monomorphic.",
		run:   nil,
	},
	{
		name:  "parse-coverage",
		title: "What this run could not read, and why",
		notes: "ANSWERS whether the numbers above cover the code you think they cover.\nACT a file with parsed=0 contributed nothing at all. A file with errors\n     contributed the symbols around the damage.\nMISLEADS an error count here is NOT evidence that the code is broken.\n     tree-sitter-java 0.23.5 predates Java 25 module import declarations\n     (JEP 511), so every `import module java.base;` parses as an ERROR and\n     adds exactly one to n_parse_errors through no fault of the source.\n     The module_imports column counts those, recovered by a text scan; a\n     row where errors equals module_imports is a clean file. See\n     meta.grammar_note. Genuine failures are the rows where errors\n     exceeds module_imports, or parsed=0.",
		run:   nil,
	},
	{
		name:  "boxing-in-hot-loop",
		title: "Integer/Long boxing inside a loop, on methods the tree actually calls",
		notes: "ANSWERS where autoboxing turns an arithmetic loop into an allocation\n     loop. Every `Integer` in a `long` accumulation is a heap object and\n     a cache miss; the JIT elides some of it and cannot elide the rest.\nACT use the primitive-specialised types -- IntStream over\n     Stream<Integer>, long over Long, entrySet() iteration over get()\n     per key. Fix the loop with the highest fan_in first.\nMISLEADS boxing sites are counted lexically, so a boxed value that never\n     escapes and is scalar-replaced by C2 counts here and costs nothing\n     at run time. This is a shortlist to profile, not a verdict.",
		run:   nil,
	},
	{
		name:  "regex-and-format-per-call",
		title: "Pattern.compile and date formatting rebuilt per call instead of once",
		notes: "ANSWERS which methods rebuild an expensive immutable object every time\n     they run. Pattern.compile parses the regex; SimpleDateFormat\n     allocates a calendar and a symbol table. Both belong in a field.\nACT hoist the Pattern to a static final constant. For dates use\n     DateTimeFormatter, which IS immutable and thread-safe --\n     SimpleDateFormat is neither, so a static one is a data race rather\n     than an optimisation.\nMISLEADS a compile inside a method that runs once at startup is\n     harmless, and this cannot tell startup from steady state. fan_in is\n     the proxy: rank by it rather than by the raw count.",
		run:   nil,
	},
	{
		name:  "raw-types-and-unchecked",
		title: "Generics defeated: raw types, unchecked casts and wildcard soup",
		notes: "ANSWERS where the compiler stopped being able to help. A raw List or an\n     unchecked cast moves a ClassCastException from compile time to\n     whichever unlucky request hits it first.\nACT parameterise the type. If the cast is genuinely unavoidable at a\n     serialization or reflection boundary, isolate it in one method with\n     a SuppressWarnings and a comment, rather than scattering the risk.\nMISLEADS raw types in code that predates generics and is never touched\n     are not urgent. Rank by fan_in, and read `suppressed` as evidence\n     the team already made this decision deliberately.",
		run:   nil,
	},
	{
		name:  "setaccessible-and-finalizers",
		title: "setAccessible, Unsafe and finalizers: the parts of Java that are leaving",
		notes: "ANSWERS what already warns, or will break, on a modern JDK.\n     setAccessible against JDK internals fails under strong\n     encapsulation; sun.misc.Unsafe memory access is deprecated for\n     removal; finalizers were deprecated in 9 and disabled by default\n     in 18.\nACT replace finalizers with Cleaner, or better with AutoCloseable and\n     try-with-resources. Replace Unsafe with VarHandle and the FFM API.\nMISLEADS this cannot tell WHOSE class is being opened. A framework\n     calling setAccessible on your own entities is normal; the same call\n     against java.lang is a time bomb. Read the target before acting.",
		run:   nil,
	},
	{
		name:  "hot-multipliers",
		title: "Where one fix pays back many times: highest fan-in",
		notes: "ANSWERS which symbols the rest of the tree leans on hardest.\nACT a correctness or speed win in a high-fan-in leaf pays back once per\n     caller. Read it next to sloc -- a four-digit fan_in on a ten-line\n     function is usually a name collision, not a hot leaf.\nMISLEADS fan_in counts STATIC call sites this parser could resolve, not\n     runtime frequency, and test callers are included, so in most repos a\n     test helper outranks production code. Scope with --module first.",
		run:   nil,
	},
	{
		name:  "risk-ranked",
		title: "Review order: if you can only read N symbols this week, which N",
		notes: "ANSWERS which code combines complexity with the operations this language\n     punishes hardest.\nACT start at the top. The weights are this analyzer's own -- read\n     --schema for the formula rather than assuming it matches another\n     language's score.\nMISLEADS a heuristic, not a finding. Generated files are excluded, so the\n     real top of the list may sit in code this filter hid.",
		run:   nil,
	},
	{
		name:  "platform-charset-across-module-boundary",
		title: "default-charset conversion called from more than one module",
		notes: "ANSWERS the question SpotBugs' DM_DEFAULT_ENCODING raises 21,497 times on\n     a large tree and cannot rank: every `new String(bytes)`, `getBytes()`\n     and `FileWriter` without an explicit Charset is platform-dependent.\n     Most are harmless because one module owns both ends. The dangerous\n     ones are read by callers in OTHER modules, where the two sides can\n     disagree about encoding and the bug only shows on a machine whose\n     file.encoding differs.\nACT pass StandardCharsets.UTF_8 explicitly. `caller_modules` is the blast\n     radius: each one is a module that inherited an encoding it never\n     chose.\nMISLEADS a module boundary is not a process boundary -- if the whole tree\n     always runs under one JVM with a fixed -Dfile.encoding, none of this\n     fires in practice. Since JEP 400 (Java 18) the default is UTF-8\n     anyway, so on a modern-only codebase this is a portability warning\n     rather than a bug.",
		run:   nil,
	},
	{
		name:  "serializable-no-uid",
		title: "Serializable class without serialVersionUID (SpotBugs SE)",
		notes: "ANSWERS which Serializable types do not declare serialVersionUID, so any\n     class change (adding a field, changing a method) breaks deserialization\n     of previously serialized instances.\nACT add `private static final long serialVersionUID = 1L;` (or let the\n     IDE generate it).\nMISLEADS a class that is never serialized does not need a UID, but if it\n     implements Serializable, the contract expects one.",
		run:   nil,
	},
	{
		name:  "print-stacktrace-leak",
		title: "printStackTrace() instead of proper logging (PMD/sonar)",
		notes: "ANSWERS where printStackTrace is called, which writes to stderr without\n     context, structured format, or log level. In production this is lost.\nACT use a logger: log.error('context', exception).\nMISLEADS printStackTrace in a test or a CLI main is acceptable. The graph\n     cannot distinguish production from test context.",
		run:   nil,
	},
	{
		name:  "god-class",
		title: "A class with too many methods and high coupling (PMD GodClass)",
		notes: "ANSWERS which classes have too many methods, too much complexity, and too\n     many dependencies, making them hard to maintain and test.\nACT split the class along responsibility lines.\nMISLEADS a framework base class or a facade may be intentionally broad.\n     The instability ratio (fan_in/(fan_in+fan_out)) tells whether it is\n     a leaf or a root.",
		run:   nil,
	},
	{
		name:  "deep-nesting",
		title: "Functions with excessive nesting depth (PMD/sonar)",
		notes: "ANSWERS where a function has max_nesting > 4, making it hard to read,\n     test, and verify all paths. Each level adds a branch to the test matrix.\nACT extract nested blocks into helper functions; use early returns.\nMISLEADS a switch-case with many arms is nesting=1 regardless of case count.\n     This measures structural nesting, not case count.",
		run:   nil,
	},
	{
		name:  "too-many-params",
		title: "Functions with too many parameters (PMD/sonar)",
		notes: "ANSWERS where a function has more than 5 parameters, making the call site\n     hard to read and error-prone (argument order confusion).\nACT introduce a parameter object, or use builder/fluent API.\nMISLEADS a constructor that initializes fields may need many params. A\n     delegate/dispatch function may need many params by design.",
		run:   nil,
	},
	{
		name:  "suppressed-warnings",
		title: "Functions with @SuppressWarnings annotations (sonar)",
		notes: "ANSWERS where @SuppressWarnings is used, which silences compiler warnings.\n     Each site is a deferred fix: the warning was real enough to suppress.\nACT review each suppression; fix the underlying issue if possible.\nMISLEADS @SuppressWarnings('unchecked') for generics interop is often\n     unavoidable. The graph counts suppressions but not their reasons.",
		run:   nil,
	},
	{
		name:  "ee12-spec-surface",
		title: "Jakarta EE 12 specification annotations in use (Data/Query/Persistence/Security)",
		notes: "ANSWERS which parts of the EE 12 platform this tree actually leans on:\n    Jakarta Data repositories, Query 1.0 providers, Persistence 4.0,\n    Security 5.0 role model. Platform GA is July 2026, so this is the\n    forward-compatibility map -- code using EE 11-only APIs will need\n    migration attention when the platform lands.\nACT group rows by module to see whether EE 12 usage is contained or\n    smeared; smearing is what turns the next platform upgrade into a\n    cross-cutting project.\nMISLEADS the row GATE (n_ee12_annos) verifies the package when an\n    annotation is spelled qualified -- a qualified mypkg.Query does\n    not count -- but UNQUALIFIED uses still count on the simple name,\n    and the specs_seen column lists simple names for the same reason:\n    treat it as a hint, not a census. Absence of rows never means\n    EE-incompatible -- XML descriptors and convention-over-\n    configuration wiring are invisible here.",
		run:   nil,
	},
	{
		name:  "java25-adoption",
		title: "Java 25 language-feature adoption per module (JEP 511/512/513)",
		notes: "ANSWERS how far each module has moved onto the Java 25 surface:\n    flexible constructor bodies, module imports, compact source\n    files, pattern switches. A module at zero on a Java-25 baseline\n    is either new code worth reviewing or old code the team has not\n    touched -- both facts worth knowing before a modernisation push.\nACT pick ONE feature per modernisation pass and sweep it module-wide;\n    mixed-style modules are where review attention goes to die.\nMISLEADS flex-ctor counts come from ERROR recovery (see\n    flex-constructor-prologues), so they are exact only while\n    tree-sitter-java predates JEP 513; module imports are recovered by\n    text scan and count per FILE; preview features need\n    --enable-preview and may vanish.",
		run:   nil,
	},
	{
		name:  "spring7-readiness",
		title: "Spring Framework 7 surface per module: resilience, versioning, HTTP clients",
		notes: "ANSWERS which modules already speak Spring 7 (resilience annotations,\n     API versioning, declarative clients) and which are still on the\n     pre-7 idioms. Useful as an upgrade checklist: the modules with\n     zero across the board are the ones whose controllers will need\n     the most migration eyes.\nACT sort the upgrade order by this table, not by module size -- a\n     small module deep on Spring 6 idioms costs more than a big one\n     already half-migrated.\nMISLEADS annotation SIMPLE NAMES again; a module can be perfectly\n    Spring-7-ready with zero rows here if it uses none of these three\n    features.",
		run:   nil,
	},
	{
		name:  "null-contract-density",
		title: "JSpecify nullability coverage: annotated vs public methods per module",
		notes: "ANSWERS how much of each module's public surface carries explicit\n     nullability (@NonNull/@Nullable). Nullability is only useful when\n     it is NEARLY UNIVERSAL -- one unannotated method in a fully\n     annotated package poisons the inference for every caller that\n     trusts the tooling.\nACT for the top module, finish the sweep rather than starting a new\n    one: partial null-safety has most of the cost and none of the\n    benefit.\nMISLEADS counts ANNOTATION SITES, not completeness -- a method with no\n    nullable parameters correctly carries no @NonNull, so low density\n    can be genuine cleanliness; only intra-JSpecify projects benefit.",
		run:   nil,
	},
	{
		name:  "framework-lock-in-map",
		title: "Framework coupling per class: handler + DI + EE12 annotation load",
		notes: "ANSWERS which classes carry the heaviest framework annotation load --\n    the map of what stops this codebase from being plain Java. High\n    annotation density is not a defect; UNIFORM density is invisible\n    architecture and this makes it visible per class so extraction\n    candidates stand out.\nACT classes at the top with few callers (low fan_in) are extraction\n    candidates: all framework, little use. Classes at the top WITH\n    high fan_in are your actual architecture -- document them.\nMISLEADS annotation COUNT is not coupling DEPTH: one @Transactional\n    pulls in less than five lifecycle callbacks; generated code\n    (excluded here) often carries heavy annotations legitimately.",
		run:   nil,
	},
	{
		name:  "spring-proxy-surface",
		title: "Per module: proxy-managed annotations and how much of the surface is inert",
		notes: "ANSWERS how much of a module's declared Spring semantics actually can\n     fire: methods carrying @Transactional/@Async/@Cacheable-family\n     annotations, of those how many are PRIVATE (never advised by any\n     proxy), how many are reachable ONLY by self-invocation (the\n     reference's own bypass case), and how many declare checked\n     exceptions without rollbackFor (the default-commit-on-checked\n     trap). High inert fractions mean the module's annotations are\n     documentation, not behaviour.\nACT read proxy-bypass-self-invocation and private-proxy-annotation\n     for the named rows; treat annotation-only guarantees in code\n     review accordingly.\nMISLEADS recognition is by annotation SIMPLE name, so non-Spring\n     annotations sharing a spelling count; AspectJ-mode weaving makes\n     both the private and the self-invocation columns legitimate --\n     this scan cannot see the config that enables it.",
		run:   nil,
	},
	{
		name:  "monitor-pressure-map",
		title: "Per module: guarded region sizes, monitor operations and the lock-owning functions",
		notes: "ANSWERS where the serialization pressure lives: total guarded SLOC per\n     module, how many functions acquire monitors, and where wait/\n     notify sit relative to them. A module with thousands of guarded\n     lines has a scalability ceiling no profiler will name directly;\n     the region sizes are the raw material for 'what exactly is held\n     while we do this'.\nACT read with lock-held-across-io and lock-order-inversion: the big\n     regions are where those bugs pay double. Shrink regions to the\n     shared-state touch itself.\nMISLEADS region size for explicit lock() is the following try block\n     (or enclosing block), which can over-count; modules with only\n     java.util.concurrent primitives and no synchronized/lock() calls\n     read as zero-pressure here.",
		run:   nil,
	},
	{
		name:  "listener-registration-surface",
		title: "Per module: listener/handler registrations versus deregistrations",
		notes: "ANSWERS the module-level listener ledger: how many addXxxListener/\n     addXxxHandler registrations and removeXxxListener/\n     removeXxxHandler deregistrations exist, and in how many\n     functions. A module that registers listeners and never removes\n     them owns a leak surface that grows with every component\n     lifecycle.\nACT read with listener-add-remove-imbalance for the per-class rows;\n     any module where remove_sites is a small fraction of add_sites\n     deserves a lifecycle audit.\nMISLEADS matched by method-name prefix (add*/remove* + 'Listener' or\n     'Handler'), so framework dispatch methods with those shapes count\n     too; process-lifetime registrations are correct rows, not bugs.",
		run:   nil,
	},
	{
		name:  "thread-creation-mix",
		title: "Per module: raw `new Thread` sites versus executor and virtual-thread roots",
		notes: "ANSWERS the module's thread budget shape: how many threads are created\n     by hand with `new Thread(...)`, and how much managed\n     infrastructure (executor roots, pooled roots, virtual-thread\n     roots) already exists. Raw threads escape every policy the\n     managed side implements -- naming, limits, shutdown, propagation\n     of context.\nACT read with manual-thread-allocation for the named sites; a module\n     with raw_threads high and executor_roots zero has NO policy to\n     bypass -- it has none at all.\nMISLEADS Thread SUBCLASSES and thread factories are not counted, so\n     the raw column is a floor; virtual-thread roots are release-\n     gated (JDK 21+) and read zero on older code regardless of intent.",
		run:   nil,
	},
	{
		name:  "closeable-ownership-surface",
		title: "Per module: resource opens, try-with-resources share, and unmanaged opens",
		notes: "ANSWERS the module's resource-hygiene posture: how many resources are\n     opened, what share sit in try-with-resources, how many are closed\n     in the opening function at all, and how many are neither --\n     opened bare, never closed locally, ownership undecided. That last\n     column is where descriptor leaks breed (Sonar S2095's empirical\n     weak spot: open in one place, close in another).\nACT read with resource-open-never-closed and returned-resource-never-\n     closed for the named rows; drive the twr share toward 100%.\nMISLEADS opened_by is a text scan for known opener names, so a\n     wrapper factory's opens count once and helper-close patterns read\n     as 'closed in fn' only when the close is textual in the same\n     body.",
		run:   nil,
	},
	{
		name:  "exception-path-map",
		title: "Per module: interrupt handling, broad and empty catches, declared throws",
		notes: "ANSWERS the module's exception-path hygiene in one row: how many\n     InterruptedException catches exist and how many swallow the\n     signal (no rethrow, no interrupt restore), plus broad catches,\n     empty catches and declared throws. Cancellation behaviour and\n     error transparency are per-module cultures; this is the measuring\n     stick.\nACT read with interrupt-swallowed and empty-catch-by-fanin for the\n     named rows; a module with high swallow counts will not cancel\n     cleanly under executor shutdown.\nMISLEADS swallow detection needs the literal interrupt() text or a\n     rethrow in the catch body -- a catch that delegates cancellation\n     to a helper reads as swallowed; catch types are simple names, so\n     a custom subclass of InterruptedException is missed.",
		run:   nil,
	},
	{
		name:  "scheduler-surface",
		title: "Per module: @Scheduled tasks, fixedRate vs fixedDelay split, IO-heavy bodies",
		notes: "ANSWERS the module's background-task surface: how many @Scheduled\n     methods exist, how many use fixedRate (the overlap-prone trigger)\n     versus fixedDelay (the self-spacing one), and how many have\n     IO/query bodies that determine the scheduler pool size you\n     actually need. All of them share one scheduler by default -- the\n     count IS the contention story.\nACT read with scheduled-overlap-risk for the named rows; size the\n     scheduler pool for the IO-heavy count, or move those tasks to\n     dedicated executors.\nMISLEADS cron-style @Scheduled entries have neither fixedRate nor\n     fixedDelay in args and read as neither; activation is a config\n     fact (@EnableScheduling) this scan does not chase.",
		run:   nil,
	},
	{
		name:  "expression-eval-surface",
		title: "Per module: SpEL/ScriptEngine evaluation sites and how many also read request input",
		notes: "ANSWERS the module's dynamic-code-execution surface: parseExpression /\n     eval / evaluate sites, how many distinct functions hold them, and\n     how many of those functions ALSO read request input directly\n     (getParameter/getHeader/...). The second column is the injection\n     pre-screen; the first is the audit scope for expression-language\n     hardening (OWASP injection family).\nACT read with expression-eval-from-input for the named rows; any\n     module where with_input_sites > 0 gets a taint review of those\n     methods, not a config review.\nMISLEADS `eval` is matched by simple name, so a domain eval() on an\n     unrelated class counts toward the surface; input reads in the\n     SAME method are visible -- input flowing through callers is the\n     reachability query's job, and capped at 3 hops there.",
		run:   nil,
	},
}

func isEntryRoot(s *Sym) bool {
	return s.getFlag(fHandler) == 1 || s.getFlag(fEntrypoint) == 1 ||
		(s.getFlag(fPublic) == 1 && s.FanIn == 0)
}

func isEntryKind(s *Sym) bool {
	return s.Kind == kindFunction || s.Kind == kindMethod ||
		s.Kind == kindConstructor
}

func downClosure(g *Graph, seeds []int32, maxDepth, fromDepth int32) map[int32]int32 {
	seen := map[[2]int32]bool{}
	best := make(map[int32]int32, len(seeds)*4)
	var frontier []int32
	for _, s := range seeds {
		k := [2]int32{s, 0}
		if seen[k] {
			continue
		}
		seen[k] = true
		if fromDepth <= 0 {
			best[s] = 0
		}
		frontier = append(frontier, s)
	}
	for d := int32(1); d <= maxDepth && len(frontier) > 0; d++ {
		var next []int32
		for _, sym := range frontier {
			lo, hi := g.Out.lo(sym), g.Out.hi(sym)
			for p := lo; p < hi; p++ {
				e := g.Out.Val[p]
				if e.IsSelf == 1 {
					continue
				}
				k := [2]int32{e.Callee, d}
				if seen[k] {
					continue
				}
				seen[k] = true
				if d >= fromDepth {
					if v, ok := best[e.Callee]; !ok || d < v {
						best[e.Callee] = d
					}
				}
				next = append(next, e.Callee)
			}
		}
		frontier = next
	}
	return best
}

func downDepths(g *Graph, seeds []int32, maxDepth int32) map[int32]int32 {
	seen := map[[2]int32]bool{}
	depths := map[int32]int32{}
	var frontier []int32
	for _, s := range seeds {
		k := [2]int32{s, 0}
		if seen[k] {
			continue
		}
		seen[k] = true
		depths[s]++
		frontier = append(frontier, s)
	}
	for d := int32(1); d <= maxDepth && len(frontier) > 0; d++ {
		var next []int32
		for _, sym := range frontier {
			lo, hi := g.Out.lo(sym), g.Out.hi(sym)
			for p := lo; p < hi; p++ {
				e := g.Out.Val[p]
				if e.IsSelf == 1 {
					continue
				}
				k := [2]int32{e.Callee, d}
				if seen[k] {
					continue
				}
				seen[k] = true
				depths[e.Callee]++
				next = append(next, e.Callee)
			}
		}
		frontier = next
	}
	return depths
}

func downFromRoots(g *Graph, roots []int32, maxDepth int32) map[[2]int32]int32 {
	seen := map[[3]uint32]bool{}
	best := make(map[[2]int32]int32, len(roots)*8)
	var frontier [][2]int32
	for _, r := range roots {
		k := [3]uint32{uint32(r), uint32(r), 0}
		if seen[k] {
			continue
		}
		seen[k] = true
		best[[2]int32{r, r}] = 0
		frontier = append(frontier, [2]int32{r, r})
	}
	for d := int32(1); d <= maxDepth && len(frontier) > 0; d++ {
		var next [][2]int32
		for _, pr := range frontier {
			lo, hi := g.Out.lo(pr[1]), g.Out.hi(pr[1])
			for p := lo; p < hi; p++ {
				e := g.Out.Val[p]
				if e.IsSelf == 1 {
					continue
				}
				k := [3]uint32{uint32(pr[0]), uint32(e.Callee), uint32(d)}
				if seen[k] {
					continue
				}
				seen[k] = true
				kk := [2]int32{pr[0], e.Callee}
				if v, ok := best[kk]; !ok || d < v {
					best[kk] = d
				}
				next = append(next, kk)
			}
		}
		frontier = next
	}
	return best
}

type concatDistinct struct {
	seen   map[uint32]bool
	out    []string
	sorted bool
}

func newConcat() *concatDistinct {
	return &concatDistinct{seen: map[uint32]bool{}}
}

func newConcatSorted() *concatDistinct {
	return &concatDistinct{seen: map[uint32]bool{}, sorted: true}
}

func (c *concatDistinct) add(id uint32, s string) {
	if c.seen[id] {
		return
	}
	c.seen[id] = true
	c.out = append(c.out, s)
}

func (c *concatDistinct) addStr(s string) {
	if slices.Contains(c.out, s) {
		return
	}
	c.out = append(c.out, s)
}

func (c *concatDistinct) String() any {
	if len(c.out) == 0 {
		return nil
	}
	if c.sorted {
		sort.Strings(c.out)
	}
	var out strings.Builder
	for i, s := range c.out {
		if i > 0 {
			out.WriteString(",")
		}
		out.WriteString(s)
	}
	return out.String()
}

type attrIndex struct {
	off []int32
	idx []int32
}

func (g *Graph) buildAttrIndex() attrIndex {
	keys := make([]int32, len(g.Attrs))
	for i, a := range g.Attrs {
		keys[i] = a.SymID
	}
	ai := attrIndex{off: make([]int32, len(g.Sym)+2)}
	for _, k := range keys {
		ai.off[k+1]++
	}
	for i := 0; i < len(g.Sym)+1; i++ {
		ai.off[i+1] += ai.off[i]
	}
	ai.idx = make([]int32, len(keys))
	fill := make([]int32, len(g.Sym)+1)
	copy(fill, ai.off[:len(g.Sym)+1])
	for i, k := range keys {
		at := fill[k]
		fill[k]++
		ai.idx[at] = int32(i)
	}
	return ai
}

func (a attrIndex) row(sid int32) (int32, int32) {
	if int(sid)+1 >= len(a.off) {
		return 0, 0
	}
	return a.off[sid], a.off[sid+1]
}

func (g *Graph) attrsOf(ai *attrIndex, sid int32, names map[string]bool) []*Attr {
	lo, hi := ai.row(sid)
	var out []*Attr
	for p := lo; p < hi; p++ {
		at := &g.Attrs[ai.idx[p]]
		if names == nil || names[g.Str.get(at.Name)] {
			out = append(out, at)
		}
	}
	return out
}

func populatedArgs(g *Graph, names ...string) map[uint32]bool {
	want := newSet(names...)
	out := make(map[uint32]bool, len(g.Attrs)/8)
	for i := range g.Attrs {
		a := &g.Attrs[i]
		if a.Args != nullStr && want[g.Str.get(a.Name)] {
			out[a.Args] = true
		}
	}
	return out
}

func (g *Graph) symByName(name string, kinds map[string]bool) []*Sym {
	lo, hi := g.nameRange(name)
	var out []*Sym
	for p := lo; p < hi; p++ {
		s := &g.Sym[g.nameOrder[p]-1]
		if kinds == nil || kinds[g.kindOf(s)] {
			out = append(out, s)
		}
	}
	return out
}

func kindSet(names ...string) map[string]bool { return newSet(names...) }

var (
	kindsClass = kindSet("class", "interface")

	kindsClassOnly = kindSet("class")
	kindsPlain     = kindSet("function", "method", "closure")
	kindsBean      = kindSet("class", "interface", "record", "enum", "type")
)

func cut(f float64) int64 {
	if f < 0 {
		return int64(-float64(int64(-f)))
	}
	return int64(f)
}

func roundTo(f float64, places int) float64 {
	p := 1.0
	for range places {
		p *= 10
	}
	if f < 0 {
		return -floorTo(-f*p+0.5) / p
	}
	return floorTo(f*p+0.5) / p
}

func floorTo(f float64) float64 {
	i := int64(f)
	if float64(i) == f {
		return f
	}
	if f < 0 {
		return float64(i - 1)
	}
	return float64(i)
}

func simpleTypeBefore(t string) string {
	if before, _, ok := strings.Cut(t, "<"); ok {
		return before
	}
	return t
}

func suffixN(t string, n int) string {
	if len(t) <= n {
		return t
	}
	return t[len(t)-n:]
}

func minI32(a, b int32) int32 {
	if a < b {
		return a
	}
	return b
}

func maxI32(a, b int32) int32 {
	if a > b {
		return a
	}
	return b
}

func (g *Graph) scanOrder(kinds ...uint32) []int32 {
	order := make([]int32, 0, len(g.Sym))
	for i := range g.Sym {
		order = append(order, int32(i+1))
	}
	if len(kinds) == 0 {
		return order
	}
	pos := make(map[uint32]int, len(kinds))
	for i, k := range kinds {
		pos[k] = i
	}
	out := order[:0]
	for _, id := range order {
		if _, ok := pos[g.Sym[id-1].Kind]; ok {
			out = append(out, id)
		}
	}

	sort.SliceStable(out, func(a, b int) bool {
		x, y := &g.Sym[out[a]-1], &g.Sym[out[b]-1]
		px, py := pos[x.Kind], pos[y.Kind]
		if px != py {
			return px < py
		}
		nx, ny := g.Str.get(x.Name), g.Str.get(y.Name)
		if nx != ny {
			return nx < ny
		}
		return x.ID < y.ID
	})
	return out
}

func (g *Graph) forEachSymbol(kinds []uint32, fn func(*Sym, *File)) {
	for _, id := range g.scanOrder(kinds...) {
		s := &g.Sym[id-1]
		fn(s, &g.Files[s.FileID-1])
	}
}

func (g *Graph) scanOrderModuleKind() []int32 {
	order := make([]int32, 0, len(g.Sym))
	for i := range g.Sym {
		order = append(order, int32(i+1))
	}
	sort.SliceStable(order, func(a, b int) bool {
		x, y := &g.Sym[order[a]-1], &g.Sym[order[b]-1]
		if x.ModuleID != y.ModuleID {
			return x.ModuleID < y.ModuleID
		}
		kx, ky := kindNames[x.Kind], kindNames[y.Kind]
		if kx != ky {
			return kx < ky
		}
		return x.ID < y.ID
	})
	return order
}

func (g *Graph) overrideOrder() []int32 {
	order := make([]int32, len(g.Over))
	for i := range order {
		order[i] = int32(i)
	}
	sort.SliceStable(order, func(a, b int) bool {
		x, y := &g.Over[order[a]], &g.Over[order[b]]
		px, py := g.Str.get(x.ParentType), g.Str.get(y.ParentType)
		if px != py {
			return px < py
		}
		return x.ID < y.ID
	})
	return order
}

var (
	kindFnMethCon = []uint32{kindFunction, kindMethod, kindConstructor}
)

func (g *Graph) scanOrderFileLine(kinds ...uint32) []int32 {
	order := make([]int32, 0, len(g.Sym))
	for i := range g.Sym {
		order = append(order, int32(i+1))
	}
	if len(kinds) > 0 {
		pos := make(map[uint32]bool, len(kinds))
		for _, k := range kinds {
			pos[k] = true
		}
		out := order[:0]
		for _, id := range order {
			if pos[g.Sym[id-1].Kind] {
				out = append(out, id)
			}
		}
		order = out
	}
	sort.SliceStable(order, func(a, b int) bool {
		x, y := &g.Sym[order[a]-1], &g.Sym[order[b]-1]
		if x.FileID != y.FileID {
			return x.FileID < y.FileID
		}
		if x.LineStart != y.LineStart {
			return x.LineStart < y.LineStart
		}
		return x.ID < y.ID
	})
	return order
}

func (g *Graph) forEachFileLine(kinds []uint32, fn func(*Sym, *File)) {
	for _, id := range g.scanOrderFileLine(kinds...) {
		s := &g.Sym[id-1]
		fn(s, &g.Files[s.FileID-1])
	}
}

func init() {
	metrics[0].run = mGraphBlindspots
	metrics[1].run = mPerElementCost
	metrics[2].run = mMegamorphicCallsites
	metrics[3].run = mParseCoverage
	metrics[4].run = mBoxingInHotLoop
	metrics[5].run = mRegexAndFormatPerCall
	metrics[6].run = mRawTypesAndUnchecked
	metrics[7].run = mSetAccessibleAndFinalizers
	metrics[8].run = mHotMultipliers
	metrics[9].run = mRiskRanked
	metrics[10].run = mPlatformCharset
	metrics[11].run = mSerializableNoUID
	metrics[12].run = mPrintStacktraceLeak
	metrics[13].run = mGodClass
	metrics[14].run = mDeepNesting
	metrics[15].run = mTooManyParams
	metrics[16].run = mSuppressedWarnings
	metrics[17].run = mEE12SpecSurface
	metrics[18].run = mJava25Adoption
	metrics[19].run = mSpring7Readiness
	metrics[20].run = mNullContractDensity
	metrics[21].run = mFrameworkLockInMap
	metrics[22].run = mSpringProxySurface
	metrics[23].run = mMonitorPressureMap
	metrics[24].run = mListenerRegistrationSurface
	metrics[25].run = mThreadCreationMix
	metrics[26].run = mCloseableOwnershipSurface
	metrics[27].run = mExceptionPathMap
	metrics[28].run = mSchedulerSurface
	metrics[29].run = mExpressionEvalSurface
}

func mGraphBlindspots(g *Graph, mod string, lim int) ([]string, [][]any) {
	cols := []string{"module_", "fns", "calls", "external", "unresolved",
		"reflect_", "handlers", "framework_entries", "pct_blind"}
	type agg struct {
		fns, calls, ext, unres, refl, handlers int32
	}
	byMod := map[int32]*agg{}
	order := []int32{}
	for _, id := range g.scanOrder() {
		s := &g.Sym[id-1]
		if s.Kind != kindFunction && s.Kind != kindMethod &&
			s.Kind != kindConstructor {
			continue
		}
		if !likeMatch(g.modName(s.ModuleID), mod) {
			continue
		}
		a := byMod[s.ModuleID]
		if a == nil {
			a = &agg{}
			byMod[s.ModuleID] = a
			order = append(order, s.ModuleID)
		}
		a.calls += s.NCalls
		a.ext += s.NExternalCalls
		a.unres += s.NUnresolved
		a.refl += s.NReflection
		a.handlers += s.getFlag(fHandler)
	}
	for _, mid := range order {
		a := byMod[mid]
		a.fns = countFnInModule(g, mid)
		if a.calls == 0 {
			continue
		}
		fe := int32(0)
		for i := range g.Over {
			o := &g.Over[i]
			if o.IsFwEntry == 1 && g.Sym[o.SymID-1].ModuleID == mid {
				fe++
			}
		}
		var pct any
		if a.calls != 0 {
			pct = cut(100.0 * float64(a.unres) / float64(a.calls))
		}
		rowsAppend(&rows, []any{g.modName(mid), int(a.fns), int(a.calls),
			int(a.ext), int(a.unres), int(a.refl), int(a.handlers), int(fe),
			pct})
	}
	sortRows(rows, sortKey{col: 4, asc: false})
	return cols, limitRows(rows, lim)
}

func countFnInModule(g *Graph, mid int32) int32 {
	n := int32(0)
	for i := range g.Sym {
		s := &g.Sym[i]
		if s.ModuleID == mid && (s.Kind == kindFunction ||
			s.Kind == kindMethod || s.Kind == kindConstructor) {
			n++
		}
	}
	return n
}

var rows [][]any

func rowsAppend(dst *[][]any, r []any) { *dst = append(*dst, r) }

func mPerElementCost(g *Graph, mod string, lim int) ([]string, [][]any) {
	cols := []string{"name", "owner", "concat_loop", "concats", "boxing_loop",
		"boxing", "regex_loop", "regex_compiles", "query_loop", "queries",
		"alloc_loop", "depth", "fan_in", "element_cost", "at"}
	rows = nil
	g.forEachFileLine(nil, func(s *Sym, f *File) {
		if s.MaxLoopDepth == 0 || f.IsTest != 0 || f.IsGen != 0 ||
			!likeMatch(g.modName(s.ModuleID), mod) {
			return
		}
		cost := s.ConcatInLoop + s.NBoxingInLoop + s.RegexInLoop +
			s.QueryInLoop + s.AllocInLoop
		if cost == 0 {
			return
		}
		ec := (s.ConcatInLoop*6 + s.NBoxingInLoop*4 + s.RegexInLoop*10 +
			s.QueryInLoop*20 + s.AllocInLoop*2) *
			(1 + s.MaxLoopDepth) * (1 + minI32(s.FanIn, 20))
		rows = append(rows, []any{g.Str.get(s.Name), g.Str.get(s.OwnerType),
			int(s.ConcatInLoop), int(s.NStringConcat), int(s.NBoxingInLoop),
			int(s.NBoxingSites), int(s.RegexInLoop), int(s.NRegexCompile),
			int(s.QueryInLoop), int(s.NQueryCalls), int(s.AllocInLoop),
			int(s.MaxLoopDepth), int(s.FanIn), int(ec),
			g.at(s.FileID, s.LineStart)})
	})
	sortRows(rows, sortKey{col: 13, asc: false})
	return cols, limitRows(rows, lim)
}

func mMegamorphicCallsites(g *Graph, mod string, lim int) ([]string, [][]any) {
	cols := []string{"iface", "n_impls", "iface_kind", "called_from", "owner",
		"param", "param_type", "depth", "calls_in_loop", "lambdas", "streams",
		"fan_in", "at"}
	type mtKey struct {
		iid, sid, pos int32
		pname, ptype  string
	}
	seenMT := map[mtKey]bool{}
	var hot []*Sym
	for _, id := range g.scanOrder() {
		s := &g.Sym[id-1]
		f := &g.Files[s.FileID-1]
		if s.MaxLoopDepth == 0 || s.CallInLoop == 0 || f.IsTest != 0 ||
			!likeMatch(g.modName(s.ModuleID), mod) {
			continue
		}
		hot = append(hot, s)
	}
	rows = nil
	for _, s := range hot {
		for i := range g.Params {
			p := &g.Params[i]
			if p.SymID != s.ID {
				continue
			}
			pt := g.Str.get(p.Type)

			names := []string{pt}
			if k := strings.IndexByte(pt, '<'); k > 0 {
				names[0] = pt[:k]
			}
			if strings.HasSuffix(pt, ">") {
				x := pt[:len(pt)-1]
				rt := strings.TrimRight(x, "abcdefghijklmnopqrstuvwxyz"+
					"ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_$.")
				if len(rt) < len(x) && rt[len(rt)-1] == '<' {
					names = append(names, x[len(rt):])
				}
			}
			for _, nm := range names {
				if nm == "" {
					continue
				}
				for _, iface := range g.symByName(nm, kindsClass) {
					if iface.NImplTargets < 3 {
						continue
					}
					k := mtKey{iface.ID, s.ID, p.Pos, g.Str.get(p.Name), pt}
					if seenMT[k] {
						continue
					}
					seenMT[k] = true
					rows = append(rows, []any{g.Str.get(iface.Name),
						int(iface.NImplTargets), g.kindOf(iface),
						g.Str.get(s.Name), g.Str.get(s.OwnerType),
						g.Str.get(p.Name), pt, int(s.MaxLoopDepth),
						int(s.CallInLoop), int(s.NLambdas), int(s.NStreams),
						int(s.FanIn), g.at(s.FileID, s.LineStart)})
				}
			}
		}
	}
	sortRows(rows, sortKey{col: 1, asc: false}, sortKey{col: 7, asc: false},
		sortKey{col: 11, asc: false})
	return cols, limitRows(rows, lim)
}

func mParseCoverage(g *Graph, mod string, lim int) ([]string, [][]any) {
	cols := []string{"path", "lines", "errors", "missing", "module_imports",
		"unexplained", "parsed", "generated", "test_", "symbols_"}
	modImports := map[int32]int32{}
	for i := range g.JPMS {
		if g.Str.get(g.JPMS[i].Kind) == "import-module" {
			modImports[g.JPMS[i].FileID]++
		}
	}
	rows = nil
	for i := range g.Files {
		f := &g.Files[i]
		if f.NParsErr == 0 && f.Parsed != 0 {
			continue
		}
		if !likeMatch(g.modName(f.ModuleID), mod) {
			continue
		}
		mi := modImports[f.ID]
		rows = append(rows, []any{f.Path(g.Str), int(f.Lines), int(f.NParsErr),
			int(f.NMissing), int(mi), int(f.NParsErr - mi), int(f.Parsed),
			int(f.IsGen), int(f.IsTest), int(f.NSymbols)})
	}
	sortRows(rows, sortKey{col: 5, asc: false}, sortKey{col: 1, asc: false})
	return cols, limitRows(rows, lim)
}

func mBoxingInHotLoop(g *Graph, mod string, lim int) ([]string, [][]any) {
	cols := []string{"name", "owner", "boxed_in_loop", "boxed_total", "depth",
		"allocs", "fan_in", "streams", "at"}
	rows = nil
	g.forEachFileLine(nil, func(s *Sym, f *File) {
		if s.NBoxingInLoop == 0 || f.IsTest != 0 ||
			!likeMatch(g.modName(s.ModuleID), mod) {
			return
		}
		rows = append(rows, []any{g.Str.get(s.Name), g.Str.get(s.OwnerType),
			int(s.NBoxingInLoop), int(s.NBoxingSites), int(s.MaxLoopDepth),
			int(s.NAllocSites), int(s.FanIn), int(s.NStreams),
			g.at(s.FileID, s.LineStart), s.NBoxingInLoop * (1 + s.FanIn)})
	})
	sortRows(rows, sortKey{col: 9, asc: false}, sortKey{col: 4, asc: false})
	stripLast(rows)
	return cols, limitRows(rows, lim)
}

func mRegexAndFormatPerCall(g *Graph, mod string, lim int) ([]string, [][]any) {
	cols := []string{"name", "owner", "regex_compiles", "datefmt_ops", "fan_in",
		"depth", "calls_in_loop", "static_", "at"}
	rows = nil
	g.forEachFileLine(nil, func(s *Sym, f *File) {
		if (s.NRegexCompile == 0 && s.NDatefmtOps == 0) || s.FanIn == 0 ||
			f.IsTest != 0 || !likeMatch(g.modName(s.ModuleID), mod) {
			return
		}
		rows = append(rows, []any{g.Str.get(s.Name), g.Str.get(s.OwnerType),
			int(s.NRegexCompile), int(s.NDatefmtOps), int(s.FanIn),
			int(s.MaxLoopDepth), int(s.CallInLoop), int(s.getFlag(fStatic)),
			g.at(s.FileID, s.LineStart),
			(s.NRegexCompile + s.NDatefmtOps) * (1 + s.FanIn)})
	})
	sortRows(rows, sortKey{col: 9, asc: false})
	stripLast(rows)
	return cols, limitRows(rows, lim)
}

func mRawTypesAndUnchecked(g *Graph, mod string, lim int) ([]string, [][]any) {
	cols := []string{"name", "owner", "raw_types", "unchecked", "wildcards",
		"instanceofs", "suppressed", "fan_in", "at"}
	rows = nil
	g.forEachFileLine(nil, func(s *Sym, f *File) {
		if (s.NRawTypes == 0 && s.NUncheckedCasts == 0) || f.IsTest != 0 ||
			!likeMatch(g.modName(s.ModuleID), mod) {
			return
		}
		rows = append(rows, []any{g.Str.get(s.Name), g.Str.get(s.OwnerType),
			int(s.NRawTypes), int(s.NUncheckedCasts), int(s.NWildcardTypes),
			int(s.NInstanceof), int(s.NSuppressions), int(s.FanIn),
			g.at(s.FileID, s.LineStart),
			(s.NRawTypes*2 + s.NUncheckedCasts*3) * (1 + s.FanIn)})
	})
	sortRows(rows, sortKey{col: 9, asc: false})
	stripLast(rows)
	return cols, limitRows(rows, lim)
}

func mSetAccessibleAndFinalizers(g *Graph, mod string, lim int) ([]string, [][]any) {
	cols := []string{"name", "owner", "setaccessible", "unsafe_calls",
		"finalizers", "native_calls", "ffm_downcalls", "fan_in", "at"}
	rows = nil
	g.forEachFileLine(nil, func(s *Sym, f *File) {
		if s.NSetAccessible == 0 && s.NUnsafeCalls == 0 && s.NFinalizers == 0 {
			return
		}
		if f.IsTest != 0 || !likeMatch(g.modName(s.ModuleID), mod) {
			return
		}
		rows = append(rows, []any{g.Str.get(s.Name), g.Str.get(s.OwnerType),
			int(s.NSetAccessible), int(s.NUnsafeCalls), int(s.NFinalizers),
			int(s.NNativeCalls), int(s.NFFMDowncall), int(s.FanIn),
			g.at(s.FileID, s.LineStart)})
	})
	sortRows(rows, sortKey{col: 4, asc: false}, sortKey{col: 3, asc: false},
		sortKey{col: 2, asc: false})
	return cols, limitRows(rows, lim)
}

func mHotMultipliers(g *Graph, mod string, lim int) ([]string, [][]any) {
	cols := []string{"name", "fan_in", "sites", "fan_out", "cyclo", "sloc",
		"kind", "module_", "at"}
	rows = nil
	g.forEachFileLine(nil, func(s *Sym, f *File) {
		if s.FanIn == 0 || !likeMatch(g.modName(s.ModuleID), mod) {
			return
		}
		rows = append(rows, []any{g.Str.get(s.Name), int(s.FanIn),
			int(s.NCallsites), int(s.FanOut), int(s.Cyclomatic), int(s.Sloc),
			g.kindOf(s), g.modName(s.ModuleID), g.at(s.FileID, s.LineStart)})
	})
	sortRows(rows, sortKey{col: 1, asc: false}, sortKey{col: 4, asc: false})
	return cols, limitRows(rows, lim)
}

func mRiskRanked(g *Graph, mod string, lim int) ([]string, [][]any) {
	cols := []string{"name", "risk", "cyclo", "cog", "nest", "hazards", "fan_in",
		"sloc", "at"}
	rows = nil
	g.forEachFileLine(nil, func(s *Sym, f *File) {
		if s.RiskScore == 0 || f.IsGen != 0 ||
			!likeMatch(g.modName(s.ModuleID), mod) {
			return
		}
		rows = append(rows, []any{g.Str.get(s.Name), int(s.RiskScore),
			int(s.Cyclomatic), int(s.Cognitive), int(s.MaxNesting),
			int(s.NHazards), int(s.FanIn), int(s.Sloc),
			g.at(s.FileID, s.LineStart)})
	})
	sortRows(rows, sortKey{col: 1, asc: false})
	return cols, limitRows(rows, lim)
}

func mPlatformCharset(g *Graph, mod string, lim int) ([]string, [][]any) {
	cols := []string{"name", "callers", "caller_modules", "charset_calls",
		"radixless_parses", "interns", "fan_in", "at"}
	callers := map[int32]map[int32]bool{}
	mods := map[int32]map[int32]bool{}
	for i := range g.Edges {
		e := &g.Edges[i]
		s := &g.Sym[e.Callee-1]
		c := &g.Sym[e.Caller-1]
		if s.NDefaultCharset == 0 || e.SameMod != 0 || e.IsSelf != 0 {
			continue
		}
		if g.Files[s.FileID-1].IsTest != 0 || g.Files[c.FileID-1].IsTest != 0 {
			continue
		}
		if !likeMatch(g.modName(s.ModuleID), mod) {
			continue
		}
		m := callers[s.ID]
		if m == nil {
			m = map[int32]bool{}
			callers[s.ID] = m
		}
		m[e.Caller] = true
		m2 := mods[s.ID]
		if m2 == nil {
			m2 = map[int32]bool{}
			mods[s.ID] = m2
		}
		m2[c.ModuleID] = true
	}
	rows = nil
	for _, id := range g.scanOrder() {
		s := &g.Sym[id-1]
		m, ok := callers[s.ID]
		if !ok || len(m) <= 1 {
			continue
		}
		rows = append(rows, []any{g.Str.get(s.Name), int(len(m)),
			int(len(mods[s.ID])), int(s.NDefaultCharset),
			int(s.NParseNoRadix), int(s.NStringIntern), int(s.FanIn),
			g.at(s.FileID, s.LineStart)})
	}
	sortRows(rows, sortKey{col: 2, asc: false}, sortKey{col: 3, asc: false},
		sortKey{col: 6, asc: false})
	return cols, limitRows(rows, lim)
}

func mSerializableNoUID(g *Graph, mod string, lim int) ([]string, [][]any) {
	cols := []string{"name", "kind", "is_serializable", "has_serial_uid", "sloc",
		"at"}
	rows = nil
	for _, id := range g.scanOrder(kindClass, kindInterface) {
		s := &g.Sym[id-1]
		if s.flags&fSerializable == 0 || s.getFlag(fHasSerialUID) != 0 {
			continue
		}
		f := &g.Files[s.FileID-1]
		if f.IsTest != 0 || !likeMatch(g.modName(s.ModuleID), mod) {
			continue
		}
		rows = append(rows, []any{g.Str.get(s.Name), g.kindOf(s),
			s.getFlag(fSerializable), s.getFlag(fHasSerialUID), int(s.Sloc),
			g.at(s.FileID, s.LineStart)})
	}
	sortRows(rows, sortKey{col: 4, asc: false})
	return cols, limitRows(rows, lim)
}

func mPrintStacktraceLeak(g *Graph, mod string, lim int) ([]string, [][]any) {
	cols := []string{"name", "stacktrace_calls", "declared_throws", "catches",
		"broad_catches", "fan_in", "cyclo", "at"}
	rows = nil
	g.forEachFileLine(nil, func(s *Sym, f *File) {
		if s.NPrintStacktrace == 0 || f.IsTest != 0 ||
			!likeMatch(g.modName(s.ModuleID), mod) {
			return
		}
		rows = append(rows, []any{g.Str.get(s.Name), int(s.NPrintStacktrace),
			int(s.NThrowsDeclared), int(s.NCatch), int(s.NCatchBroad),
			int(s.FanIn), int(s.Cyclomatic), g.at(s.FileID, s.LineStart)})
	})
	sortRows(rows, sortKey{col: 1, asc: false}, sortKey{col: 5, asc: false})
	return cols, limitRows(rows, lim)
}

func mGodClass(g *Graph, mod string, lim int) ([]string, [][]any) {
	cols := []string{"name", "n_methods", "total_cyclo", "fan_in", "sloc", "at"}
	type mc struct{ n, cyclo int32 }
	byParent := map[int32]*mc{}
	for i := range g.Sym {
		s := &g.Sym[i]
		if s.ParentID < 0 ||
			(s.Kind != kindFunction && s.Kind != kindMethod) {
			continue
		}
		m := byParent[s.ParentID]
		if m == nil {
			m = &mc{}
			byParent[s.ParentID] = m
		}
		m.n++
		m.cyclo += s.Cyclomatic
	}
	rows = nil
	for _, id := range g.scanOrderFileLine(kindClass) {
		s := &g.Sym[id-1]
		f := &g.Files[s.FileID-1]
		if f.IsTest != 0 || !likeMatch(g.modName(s.ModuleID), mod) {
			continue
		}

		n := 0
		var cyclo any
		if m, ok := byParent[s.ID]; ok {
			n, cyclo = int(m.n), int(m.cyclo)
		}
		rows = append(rows, []any{g.Str.get(s.Name), n, cyclo, int(s.FanIn),
			int(s.Sloc), g.at(s.FileID, s.LineStart), cyclo})
	}
	sortRows(rows, sortKey{col: 6, asc: false})
	stripLast(rows)
	return cols, limitRows(rows, lim)
}

func mDeepNesting(g *Graph, mod string, lim int) ([]string, [][]any) {
	cols := []string{"name", "nesting", "cyclo", "cognitive", "loops", "sloc",
		"fan_in", "at"}
	rows = nil
	for _, id := range g.scanOrderFileLine() {
		s := &g.Sym[id-1]
		if s.MaxNesting <= 4 ||
			(s.Kind != kindFunction && s.Kind != kindMethod) {
			continue
		}
		f := &g.Files[s.FileID-1]
		if f.IsTest != 0 || !likeMatch(g.modName(s.ModuleID), mod) {
			continue
		}
		rows = append(rows, []any{g.Str.get(s.Name), int(s.MaxNesting),
			int(s.Cyclomatic), int(s.Cognitive), int(s.NLoops), int(s.Sloc),
			int(s.FanIn), g.at(s.FileID, s.LineStart)})
	}
	sortRows(rows, sortKey{col: 1, asc: false}, sortKey{col: 2, asc: false})
	return cols, limitRows(rows, lim)
}

func mTooManyParams(g *Graph, mod string, lim int) ([]string, [][]any) {
	cols := []string{"name", "n_params", "n_optional_params", "n_generic_params",
		"sloc", "cyclo", "fan_in", "is_public", "at"}
	rows = nil
	for _, id := range g.scanOrderFileLine() {
		s := &g.Sym[id-1]
		if s.NParams <= 5 ||
			(s.Kind != kindFunction && s.Kind != kindMethod) {
			continue
		}
		f := &g.Files[s.FileID-1]
		if f.IsTest != 0 || !likeMatch(g.modName(s.ModuleID), mod) {
			continue
		}
		rows = append(rows, []any{g.Str.get(s.Name), int(s.NParams),
			int(s.NOptionalParams), int(s.NGenericParams), int(s.Sloc),
			int(s.Cyclomatic), int(s.FanIn), int(s.getFlag(fPublic)),
			g.at(s.FileID, s.LineStart)})
	}
	sortRows(rows, sortKey{col: 1, asc: false}, sortKey{col: 6, asc: false})
	return cols, limitRows(rows, lim)
}

func mSuppressedWarnings(g *Graph, mod string, lim int) ([]string, [][]any) {
	cols := []string{"name", "suppressions", "annotations", "unchecked_casts",
		"raw_types", "fan_in", "cyclo", "at"}
	rows = nil
	g.forEachFileLine(nil, func(s *Sym, f *File) {
		if s.NSuppressions == 0 || f.IsTest != 0 ||
			!likeMatch(g.modName(s.ModuleID), mod) {
			return
		}
		rows = append(rows, []any{g.Str.get(s.Name), int(s.NSuppressions),
			int(s.NAnnotations), int(s.NUncheckedCasts), int(s.NRawTypes),
			int(s.FanIn), int(s.Cyclomatic), g.at(s.FileID, s.LineStart)})
	})
	sortRows(rows, sortKey{col: 1, asc: false}, sortKey{col: 5, asc: false})
	return cols, limitRows(rows, lim)
}

func mEE12SpecSurface(g *Graph, mod string, lim int) ([]string, [][]any) {
	cols := []string{"module", "annotated_symbols", "ee12_anno_sites",
		"specs_seen", "files"}
	ee12Specs := newSet("Query", "Find", "FindAll", "Save", "Delete", "Insert",
		"Update", "TenantId", "RunInTransaction", "RolesAllowed", "PermitAll",
		"DeclareRoles", "RunAs", "Persists", "CTEProvider", "SubqueryProvider")
	ai := g.buildAttrIndex()
	type acc struct {
		syms, sites, files int32
		specs              *concatDistinct
	}
	byMod := map[int32]*acc{}
	var order []int32
	for _, id := range g.scanOrder() {
		s := &g.Sym[id-1]
		f := &g.Files[s.FileID-1]
		if s.NEe12Annos == 0 || f.IsTest != 0 ||
			!likeMatch(g.modName(s.ModuleID), mod) {
			continue
		}
		a := byMod[s.ModuleID]
		if a == nil {
			a = &acc{specs: newConcat()}
			byMod[s.ModuleID] = a
			order = append(order, s.ModuleID)
		}
		a.syms++
		a.sites += s.NEe12Annos
		a.files++
		for _, at := range g.attrsOf(&ai, s.ID, ee12Specs) {
			a.specs.add(at.Name, g.Str.get(at.Name))
		}
	}
	rows = nil
	for _, mid := range order {
		a := byMod[mid]
		rows = append(rows, []any{g.modName(mid), int(a.syms), int(a.sites),
			a.specs.String(), int(a.files)})
	}
	sortRows(rows, sortKey{col: 1, asc: false})
	return cols, limitRows(rows, lim)
}

func mJava25Adoption(g *Graph, mod string, lim int) ([]string, [][]any) {
	cols := []string{"module", "flex_ctors", "modern_idiom_methods",
		"methods_total"}
	type acc struct {
		flex, modern, total int32
	}
	byMod := map[int32]*acc{}
	var order []int32
	for _, id := range g.scanOrderFileLine(kindFunction, kindMethod, kindConstructor) {
		s := &g.Sym[id-1]
		f := &g.Files[s.FileID-1]
		if f.IsTest != 0 || !likeMatch(g.modName(s.ModuleID), mod) {
			continue
		}
		a := byMod[s.ModuleID]
		if a == nil {
			a = &acc{}
			byMod[s.ModuleID] = a
			order = append(order, s.ModuleID)
		}
		a.flex += s.getFlag(fFlexCtor)
		a.total++
		if s.NModernIdioms > 0 {
			a.modern++
		}
	}
	rows = nil
	for _, mid := range order {
		a := byMod[mid]
		rows = append(rows, []any{g.modName(mid), int(a.flex), int(a.modern),
			int(a.total)})
	}
	sortRows(rows, sortKey{col: 1, asc: false}, sortKey{col: 2, asc: false})
	return cols, limitRows(rows, lim)
}

func mSpring7Readiness(g *Graph, mod string, lim int) ([]string, [][]any) {
	cols := []string{"module", "resilience_methods", "versioned_endpoints",
		"http_clients", "methods_total"}
	type acc struct{ resil, ver, total int32 }
	byMod := map[int32]*acc{}
	var order []int32
	for _, id := range g.scanOrderFileLine() {
		s := &g.Sym[id-1]
		if s.Kind != kindFunction && s.Kind != kindMethod {
			continue
		}
		f := &g.Files[s.FileID-1]
		if f.IsTest != 0 || !likeMatch(g.modName(s.ModuleID), mod) {
			continue
		}
		a := byMod[s.ModuleID]
		if a == nil {
			a = &acc{}
			byMod[s.ModuleID] = a
			order = append(order, s.ModuleID)
		}
		a.total++
		if s.NResilienceAnnos > 0 {
			a.resil++
		}
		if s.NApiVersionAttr > 0 {
			a.ver++
		}
	}
	http := map[int32]int32{}
	for i := range g.Sym {
		if g.Sym[i].getFlag(fHTTPExchange) == 1 {
			http[g.Sym[i].ModuleID]++
		}
	}
	rows = nil
	for _, mid := range order {
		a := byMod[mid]
		rows = append(rows, []any{g.modName(mid), int(a.resil), int(a.ver),
			int(http[mid]), int(a.total)})
	}
	sortRows(rows, sortKey{col: 1, asc: false}, sortKey{col: 3, asc: false})
	return cols, limitRows(rows, lim)
}

func mNullContractDensity(g *Graph, mod string, lim int) ([]string, [][]any) {
	cols := []string{"module", "annotated_methods", "public_methods",
		"pct_public_annotated"}
	type acc struct{ ann, pub int32 }
	byMod := map[int32]*acc{}
	var order []int32
	for _, id := range g.scanOrderFileLine() {
		s := &g.Sym[id-1]
		if s.Kind != kindFunction && s.Kind != kindMethod {
			continue
		}
		f := &g.Files[s.FileID-1]
		if f.IsTest != 0 || !likeMatch(g.modName(s.ModuleID), mod) {
			continue
		}
		a := byMod[s.ModuleID]
		if a == nil {
			a = &acc{}
			byMod[s.ModuleID] = a
			order = append(order, s.ModuleID)
		}
		if s.NJSpecifyAnnos > 0 {
			a.ann++
		}
		if s.getFlag(fPublic) == 1 {
			a.pub++
		}
	}
	rows = nil
	for _, mid := range order {
		a := byMod[mid]
		if a.pub == 0 {
			continue
		}
		rows = append(rows, []any{g.modName(mid), int(a.ann), int(a.pub),
			roundTo(100.0*float64(a.ann)/float64(a.pub), 1)})
	}
	sortRows(rows, sortKey{col: 3, asc: true})
	return cols, limitRows(rows, lim)
}

func mFrameworkLockInMap(g *Graph, mod string, lim int) ([]string, [][]any) {
	cols := []string{"type_", "kind", "annos", "ee12_annos", "fan_in", "sloc",
		"module", "at"}
	rows = nil
	for _, id := range g.scanOrder(kindClass, kindInterface, kindRecord,
		kindEnum) {
		s := &g.Sym[id-1]
		if s.NAnnotations < 4 {
			continue
		}
		f := &g.Files[s.FileID-1]
		if f.IsTest != 0 || f.IsGen != 0 || !likeMatch(g.modName(s.ModuleID), mod) {
			continue
		}
		rows = append(rows, []any{g.Str.get(s.Name), g.kindOf(s),
			int(s.NAnnotations), int(s.NEe12Annos), int(s.FanIn), int(s.Sloc),
			g.modName(s.ModuleID), g.at(s.FileID, s.LineStart)})
	}
	sortRows(rows, sortKey{col: 2, asc: false}, sortKey{col: 3, asc: false})
	return cols, limitRows(rows, lim)
}

func mSpringProxySurface(g *Graph, mod string, lim int) ([]string, [][]any) {
	cols := []string{"module_", "proxy_annotated", "private_never_advised",
		"self_invoked_only", "throws_checked", "at"}
	ai := g.buildAttrIndex()
	selfOnly := selfOnlyCallees(g)
	type acc struct {
		n, priv, self, throws int32
		atPath                string
		atLine                int32
	}
	byMod := map[int32]*acc{}
	var order []int32
	for _, id := range g.scanOrder() {
		s := &g.Sym[id-1]
		if len(g.attrsOf(&ai, s.ID, proxyAnnoNames)) == 0 {
			continue
		}
		f := &g.Files[s.FileID-1]
		if f.IsTest != 0 || !likeMatch(g.modName(s.ModuleID), mod) {
			continue
		}
		a := byMod[s.ModuleID]
		if a == nil {
			a = &acc{}
			byMod[s.ModuleID] = a
			order = append(order, s.ModuleID)
		}
		a.n++
		if g.Str.get(s.Vis) == "private" {
			a.priv++
		}
		if selfOnly[s.ID] {
			a.self++
		}
		if s.NThrowsDeclared > 0 {
			a.throws++
		}
		if a.atPath == "" || f.Path(g.Str) < a.atPath {
			a.atPath = f.Path(g.Str)
		}
		if a.atLine == 0 || s.LineStart < a.atLine {
			a.atLine = s.LineStart
		}
	}
	rows = nil
	for _, mid := range order {
		a := byMod[mid]
		rows = append(rows, []any{g.modName(mid), int(a.n), int(a.priv),
			int(a.self), int(a.throws), a.atPath + ":" + itoa(int(a.atLine))})
	}
	sortRows(rows, sortKey{col: 1, asc: false})
	return cols, limitRows(rows, lim)
}

func mMonitorPressureMap(g *Graph, mod string, lim int) ([]string, [][]any) {
	cols := []string{"module_", "locking_fns", "lock_regions", "guarded_sloc",
		"wait_notify_ops", "at"}
	type acc struct {
		fns, regions, sloc, mon int32
		atPath                  string
		atLine                  int32
	}
	byMod := map[int32]*acc{}
	var order []int32
	for _, id := range g.scanOrder() {
		s := &g.Sym[id-1]
		if s.Kind != kindFunction && s.Kind != kindMethod {
			continue
		}
		f := &g.Files[s.FileID-1]
		if f.IsTest != 0 || !likeMatch(g.modName(s.ModuleID), mod) {
			continue
		}
		var regions, sloc int32
		for j := range g.Locks {
			l := &g.Locks[j]
			if l.SymID == s.ID && g.Str.get(l.Op) == "acquire" {
				regions++
				sloc += l.RegionSloc
			}
		}
		ops := int32(0)
		for j := range g.MonOps {
			if g.MonOps[j].SymID == s.ID {
				ops++
			}
		}
		if regions == 0 && ops == 0 {
			continue
		}
		a := byMod[s.ModuleID]
		if a == nil {
			a = &acc{}
			byMod[s.ModuleID] = a
			order = append(order, s.ModuleID)
		}
		a.fns++
		a.regions += regions
		a.sloc += sloc
		a.mon += ops
		if a.atPath == "" || f.Path(g.Str) < a.atPath {
			a.atPath = f.Path(g.Str)
		}
		if a.atLine == 0 || s.LineStart < a.atLine {
			a.atLine = s.LineStart
		}
	}
	rows = nil
	for _, mid := range order {
		a := byMod[mid]
		rows = append(rows, []any{g.modName(mid), int(a.fns), int(a.regions),
			int(a.sloc), int(a.mon), a.atPath + ":" + itoa(int(a.atLine))})
	}
	sortRows(rows, sortKey{col: 3, asc: false})
	return cols, limitRows(rows, lim)
}

func mListenerRegistrationSurface(g *Graph, mod string, lim int) ([]string, [][]any) {
	cols := []string{"module_", "add_sites", "remove_sites", "registering_fns",
		"pct_removed", "at"}
	type acc struct {
		adds, rem, fns int32
		atPath         string
		atLine         int32
	}
	byMod := map[int32]*acc{}
	var order []int32
	for _, id := range g.scanOrderFileLine() {
		s := &g.Sym[id-1]
		if s.NListenerAdd == 0 && s.NListenerRemove == 0 {
			continue
		}
		if s.Kind != kindFunction && s.Kind != kindMethod {
			continue
		}
		f := &g.Files[s.FileID-1]
		if f.IsTest != 0 || !likeMatch(g.modName(s.ModuleID), mod) {
			continue
		}
		a := byMod[s.ModuleID]
		if a == nil {
			a = &acc{}
			byMod[s.ModuleID] = a
			order = append(order, s.ModuleID)
		}
		a.adds += s.NListenerAdd
		a.rem += s.NListenerRemove
		if s.NListenerAdd > 0 {
			a.fns++
		}
		if a.atPath == "" || f.Path(g.Str) < a.atPath {
			a.atPath = f.Path(g.Str)
		}
		if a.atLine == 0 || s.LineStart < a.atLine {
			a.atLine = s.LineStart
		}
	}
	rows = nil
	for _, mid := range order {
		a := byMod[mid]
		var pct any
		if a.adds != 0 {
			pct = cut(100.0 * float64(minI32(a.rem, a.adds)) / float64(a.adds))
		}
		rows = append(rows, []any{g.modName(mid), int(a.adds), int(a.rem),
			int(a.fns), pct, a.atPath + ":" + itoa(int(a.atLine))})
	}
	sortRows(rows, sortKey{col: 1, asc: false})
	return cols, limitRows(rows, lim)
}

func mThreadCreationMix(g *Graph, mod string, lim int) ([]string, [][]any) {
	cols := []string{"module_", "raw_threads", "executor_roots", "pooled_roots",
		"virtual_roots", "at"}
	type acc struct {
		raw, exec, pooled, virt int32
		atPath                  string
		atLine                  int32
	}
	byMod := map[int32]*acc{}
	var order []int32
	for _, id := range g.scanOrderFileLine() {
		s := &g.Sym[id-1]
		if s.NThreadAlloc == 0 && s.getFlag(fExecRoot) == 0 &&
			s.getFlag(fPoolRoot) == 0 && s.getFlag(fVtRoot) == 0 {
			continue
		}
		if s.Kind != kindFunction && s.Kind != kindMethod &&
			s.Kind != kindConstructor {
			continue
		}
		f := &g.Files[s.FileID-1]
		if f.IsTest != 0 || !likeMatch(g.modName(s.ModuleID), mod) {
			continue
		}
		a := byMod[s.ModuleID]
		if a == nil {
			a = &acc{}
			byMod[s.ModuleID] = a
			order = append(order, s.ModuleID)
		}
		a.raw += s.NThreadAlloc
		if s.getFlag(fExecRoot) == 1 {
			a.exec++
		}
		if s.getFlag(fPoolRoot) == 1 {
			a.pooled++
		}
		if s.getFlag(fVtRoot) == 1 {
			a.virt++
		}
		if a.atPath == "" || f.Path(g.Str) < a.atPath {
			a.atPath = f.Path(g.Str)
		}
		if a.atLine == 0 || s.LineStart < a.atLine {
			a.atLine = s.LineStart
		}
	}
	rows = nil
	for _, mid := range order {
		a := byMod[mid]
		rows = append(rows, []any{g.modName(mid), int(a.raw), int(a.exec),
			int(a.pooled), int(a.virt), a.atPath + ":" + itoa(int(a.atLine))})
	}
	sortRows(rows, sortKey{col: 1, asc: false}, sortKey{col: 2, asc: false})
	return cols, limitRows(rows, lim)
}

func mCloseableOwnershipSurface(g *Graph, mod string, lim int) ([]string, [][]any) {
	cols := []string{"module_", "opens", "twr", "closed", "unmanaged", "twr_pct",
		"at"}
	type acc struct {
		opens, twr, closed, unmanaged int32
		atPath, atLine                any
	}
	byMod := map[int32]*acc{}
	var order []int32
	for i := range g.Res {
		r := &g.Res[i]
		s := &g.Sym[r.SymID-1]
		f := &g.Files[r.FileID-1]
		if f.IsTest != 0 {
			continue
		}
		a := byMod[s.ModuleID]
		if a == nil {
			a = &acc{}
			byMod[s.ModuleID] = a
			order = append(order, s.ModuleID)
		}
		a.opens++
		a.twr += r.InTryResources
		a.closed += r.ClosedInFn
		if r.InTryResources == 0 && r.ClosedInFn == 0 {
			a.unmanaged++
		}
		if a.atPath == nil || f.Path(g.Str) < a.atPath.(string) {
			a.atPath = f.Path(g.Str)
		}
		if a.atLine == nil || int(r.Line) < a.atLine.(int) {
			a.atLine = int(r.Line)
		}
	}
	rows = nil
	for _, mid := range order {
		a := byMod[mid]
		m := &g.Mod[mid-1]
		if !likeMatch(g.Str.get(m.Name), mod) {
			continue
		}
		var pct any
		if a.opens != 0 {
			pct = cut(100.0 * float64(a.twr) / float64(a.opens))
		}
		var at any
		if a.atPath != nil {
			at = a.atPath.(string) + ":" + itoa(a.atLine.(int))
		}
		rows = append(rows, []any{g.Str.get(m.Name), int(a.opens), int(a.twr),
			int(a.closed), int(a.unmanaged), pct, at})
	}
	sortRows(rows, sortKey{col: 4, asc: false}, sortKey{col: 1, asc: false})
	return cols, limitRows(rows, lim)
}

func mExceptionPathMap(g *Graph, mod string, lim int) ([]string, [][]any) {
	cols := []string{"module_", "interrupt_catches", "swallowed_interrupts",
		"broad_catches", "empty_catches", "declared_throws", "at"}
	type acc struct {
		interrupt, swallowed, broad, empty, throws int32
		seen                                       map[int32]bool
		atPath, atLine                             any
	}
	byMod := map[int32]*acc{}
	var order []int32
	for i := range g.Excepts {
		x := &g.Excepts[i]
		s := &g.Sym[x.SymID-1]
		f := &g.Files[x.FileID-1]
		if f.IsTest != 0 || !likeMatch(g.modName(s.ModuleID), mod) {
			continue
		}
		a := byMod[s.ModuleID]
		if a == nil {
			a = &acc{seen: map[int32]bool{}}
			byMod[s.ModuleID] = a
			order = append(order, s.ModuleID)
		}
		if g.Str.get(x.Kind) == "catch" {
			if g.Str.get(x.Type) == "InterruptedException" {
				if !a.seen[x.SymID] {
					a.seen[x.SymID] = true
					a.interrupt++
				}
				if x.Rethrows == 0 && x.Restores == 0 {
					a.swallowed++
				}
			}
			if x.IsBroad == 1 {
				a.broad++
			}
			if x.IsEmpty == 1 {
				a.empty++
			}
		}
		if g.Str.get(x.Kind) == "throws" {
			a.throws++
		}
		if a.atPath == nil || f.Path(g.Str) < a.atPath.(string) {
			a.atPath = f.Path(g.Str)
		}
		if a.atLine == nil || int(x.Line) < a.atLine.(int) {
			a.atLine = int(x.Line)
		}
	}
	rows = nil
	for _, mid := range order {
		a := byMod[mid]
		var at any
		if a.atPath != nil {
			at = a.atPath.(string) + ":" + itoa(a.atLine.(int))
		}
		rows = append(rows, []any{g.modName(mid), int(a.interrupt),
			int(a.swallowed), int(a.broad), int(a.empty), int(a.throws), at})
	}
	sortRows(rows, sortKey{col: 2, asc: false}, sortKey{col: 3, asc: false})
	return cols, limitRows(rows, lim)
}

func mSchedulerSurface(g *Graph, mod string, lim int) ([]string, [][]any) {
	cols := []string{"module_", "scheduled_methods", "fixed_rate", "fixed_delay",
		"io_heavy", "at"}
	ai := g.buildAttrIndex()
	scheduledAnnos := newSet("Scheduled")
	type acc struct {
		methods, rate, delay, heavy int32
		atPath, atLine              any
	}
	byMod := map[int32]*acc{}
	var order []int32
	for _, id := range g.scanOrder() {
		s := &g.Sym[id-1]
		attrs := g.attrsOf(&ai, s.ID, scheduledAnnos)
		if len(attrs) == 0 {
			continue
		}
		f := &g.Files[s.FileID-1]
		if f.IsTest != 0 || !likeMatch(g.modName(s.ModuleID), mod) {
			continue
		}
		a := byMod[s.ModuleID]
		if a == nil {
			a = &acc{}
			byMod[s.ModuleID] = a
			order = append(order, s.ModuleID)
		}
		a.methods++
		var args strings.Builder
		for _, at := range attrs {
			args.WriteString(g.Str.get(at.Args))
		}
		if strings.Contains(args.String(), "fixedRate") {
			a.rate++
		}
		if strings.Contains(args.String(), "fixedDelay") {
			a.delay++
		}
		if s.NIO > 0 || s.NQueryCalls > 0 {
			a.heavy++
		}
		if a.atPath == nil || f.Path(g.Str) < a.atPath.(string) {
			a.atPath = f.Path(g.Str)
		}
		if a.atLine == nil || int(attrs[0].Line) < a.atLine.(int) {
			a.atLine = int(attrs[0].Line)
		}
	}
	rows = nil
	for _, mid := range order {
		a := byMod[mid]
		var at any
		if a.atPath != nil {
			at = a.atPath.(string) + ":" + itoa(a.atLine.(int))
		}
		rows = append(rows, []any{g.modName(mid), int(a.methods), int(a.rate),
			int(a.delay), int(a.heavy), at})
	}
	sortRows(rows, sortKey{col: 1, asc: false}, sortKey{col: 4, asc: false})
	return cols, limitRows(rows, lim)
}

func mExpressionEvalSurface(g *Graph, mod string, lim int) ([]string, [][]any) {
	cols := []string{"module_", "eval_calls", "eval_fns", "with_input_sites", "at"}
	withInput := map[int32]bool{}
	for i := range g.UISites {
		withInput[g.UISites[i].SymID] = true
	}
	type acc struct {
		calls, fns, input int32
		atPath            string
		atLine            int32
	}
	byMod := map[int32]*acc{}
	var order []int32
	for _, id := range g.scanOrderFileLine() {
		s := &g.Sym[id-1]
		if s.NSpelEval == 0 {
			continue
		}
		if s.Kind != kindFunction && s.Kind != kindMethod {
			continue
		}
		f := &g.Files[s.FileID-1]
		if f.IsTest != 0 || !likeMatch(g.modName(s.ModuleID), mod) {
			continue
		}
		a := byMod[s.ModuleID]
		if a == nil {
			a = &acc{}
			byMod[s.ModuleID] = a
			order = append(order, s.ModuleID)
		}
		a.calls += s.NSpelEval
		a.fns++
		if withInput[s.ID] {
			a.input++
		}
		if a.atPath == "" || f.Path(g.Str) < a.atPath {
			a.atPath = f.Path(g.Str)
		}
		if a.atLine == 0 || s.LineStart < a.atLine {
			a.atLine = s.LineStart
		}
	}
	rows = nil
	for _, mid := range order {
		a := byMod[mid]
		at := ""
		if a.atPath != "" {
			at = a.atPath + ":" + itoa(int(a.atLine))
		}
		rows = append(rows, []any{g.modName(mid), int(a.calls), int(a.fns),
			int(a.input), at})
	}
	sortRows(rows, sortKey{col: 1, asc: false}, sortKey{col: 3, asc: false})
	return cols, limitRows(rows, lim)
}

func stripLast(rows [][]any) {
	for i := range rows {
		rows[i] = rows[i][:len(rows[i])-1]
	}
}

var _ = sort.Ints

type bstats struct {
	s            Sym
	cyclomatic   int32
	cognitive    int32
	maxNesting   int32
	maxLoopDepth int32
	nTokens      int32
	nOperators   int32
	nOperands    int32
	nDistOps     int32
	nDistOperand int32

	opSet []bool

	calls      []callRec
	lits       []litRec
	inputSites []inputSite
	secrets    []secretRec
	events     []event
	idents     [][2]uint32
}

type bstatsScratch struct {
	opSet      []bool
	calls      []callRec
	lits       []litRec
	inputSites []inputSite
	secrets    []secretRec
	events     []event
	idents     [][2]uint32
	nestStack  []int32
	loopStack  []int32
}

func (s *bstatsScratch) reset(st *bstats) {
	st.opSet = s.opSet[:0]
	st.calls = s.calls[:0]
	st.lits = s.lits[:0]
	st.inputSites = s.inputSites[:0]
	st.secrets = s.secrets[:0]
	st.events = s.events[:0]
	st.idents = s.idents[:0]
}

func (s *bstatsScratch) keep(st *bstats) {
	s.opSet = st.opSet
	s.calls = st.calls
	s.lits = st.lits
	s.inputSites = st.inputSites
	s.secrets = st.secrets
	s.events = st.events
	s.idents = st.idents
}

func (s *bstatsScratch) dropPins() {
	if cap(s.calls) > 512 {
		s.calls = nil
	}
	if cap(s.lits) > 512 {
		s.lits = nil
	}
	if cap(s.inputSites) > 512 {
		s.inputSites = nil
	}
	if cap(s.secrets) > 512 {
		s.secrets = nil
	}
	if cap(s.events) > 4096 {
		s.events = nil
	}
}

type callRec struct {
	name   string
	line   int32
	inLoop int32
}

type litRec struct {
	kind  string
	value string
	line  int32
	magic int32
}

type inputSite struct {
	varName string
	kind    uint32
	line    int32
	inLoop  int32
}

type secretRec struct {
	value string
	line  int32
}

type evKind uint8

const (
	evSync evKind = iota
	evMethodInv
	evObjCreate
	evResource
	evCatch
	evThrow
	evIfDCL
	evAssign
	evUpdate
	evIdent
)

type event struct {
	kind                       evKind
	line                       int32
	endLine                    int32
	depth                      int32
	f1, f2, f3, f4, f5, f6, f7 int32
	s1, s2, s3                 string
}

func (st *bstats) addCall(name string, line int32, inLoop int32) {
	st.calls = append(st.calls, callRec{name, line, inLoop})
}

func (x *xctx) addOperand(st *bstats, s string) {
	if x.opdSeen[s] != x.opdGen {
		x.opdSeen[s] = x.opdGen
		st.nDistOperand++
	}
}

func (x *xctx) addOp(st *bstats, id uint16) {
	if !x.opSeen[id] {
		x.opSeen[id] = true
		x.opIds = append(x.opIds, id)
		st.nDistOps++
	}
}

func (x *xctx) resetOps() {
	for _, id := range x.opIds {
		x.opSeen[id] = false
	}
	x.opIds = x.opIds[:0]
}

func (x *xctx) measure(body tsNode, prune bool) *bstats {

	st := &x.bst
	var zero bstats
	*st = zero
	st.cyclomatic = 1

	sc := &x.sc
	sc.reset(st)
	defer sc.keep(st)
	defer x.resetOps()
	x.opdGen++
	cur := tsWalk(body)
	defer cur.free()
	var depth int32
	var loopDepth int32
	nestStack, loopStack := sc.nestStack[:0], sc.loopStack[:0]
	defer func() { sc.nestStack, sc.loopStack = nestStack, loopStack }()
	ascii := x.asciiOK
	astr := x.asciiTxt

	for {
		node := cur.node()
		kind := node.kindID()

		for len(nestStack) > 0 && nestStack[len(nestStack)-1] >= depth {
			nestStack = nestStack[:len(nestStack)-1]
		}
		for len(loopStack) > 0 && loopStack[len(loopStack)-1] >= depth {
			loopStack = loopStack[:len(loopStack)-1]
			loopDepth--
			if loopDepth < 0 {
				loopDepth = 0
			}
		}

		isElif := false
		if x.jk.isIf[kind] {
			par := node.parent()
			if par.ok() {
				if x.jk.isIf[par.kindID()] {
					alt := par.childByFieldName(fAlternative)
					isElif = alt.ok() && alt.sameAs(node)
				} else {
					gp := par.parent()
					if gp.ok() && x.jk.isIf[gp.kindID()] {
						alt := gp.childByFieldName(fAlternative)
						if alt.ok() && alt.sameAs(par) {
							first := par.namedChild(0)
							isElif = first.ok() && first.sameAs(node)
						}
					}
				}
			}
		}

		if node.isNamed() && x.jk.isNest[kind] && !isElif {
			nestStack = append(nestStack, depth)
			if int32(len(nestStack)) > st.maxNesting {
				st.maxNesting = int32(len(nestStack))
			}
		}
		if node.isNamed() {
			if x.jk.isLoop[kind] {
				loopStack = append(loopStack, depth)
				loopDepth++
				if loopDepth > st.maxLoopDepth {
					st.maxLoopDepth = loopDepth
				}
				st.cyclomatic++
				st.cognitive += maxi32(1, int32(len(nestStack)))
				st.s.NLoops++
			} else if x.jk.isBranch[kind] {
				st.cyclomatic++
				if isElif {
					st.cognitive++
					st.s.NElif++
				} else {
					st.cognitive += maxi32(1, int32(len(nestStack)))
				}
				st.s.NBranches++
				if loopDepth > 0 {
					st.s.BranchInLoop++
				}
			}
		}
		nest := int32(len(nestStack))

		if fn := x.jk.bump[kind]; fn != nil {
			fn(&st.s, 1)
		}

		if x.jk.isCall[kind] {
			x.onCall(node, st, loopDepth, nest)
		} else if x.jk.isOperator[kind] {
			st.nOperators++
			x.addOp(st, kind)
		} else if x.jk.isString[kind] {
			txt := x.sliceToken(node, ascii, astr)
			st.s.NStringLit++
			x.addOperand(st, cgPrefix(txt, 40))
			st.nOperands++
			x.onString(node, txt, st, loopDepth)
		} else if x.jk.isNumber[kind] {
			txt := cgStrip(x.sliceToken(node, ascii, astr))
			st.nOperands++
			x.addOperand(st, txt)
			if isMagicNum(txt) {
				st.s.NMagic++
				st.lits = append(st.lits, litRec{"number", txt,
					int32(node.startRow()) + 1, 1})
			}
			if strings.ContainsAny(txt, ".") ||
				strings.ContainsAny(strings.ToLower(txt), "e") {
				st.s.NFloatLit++
			}
		} else if x.jk.isComment[kind] {
			sp, ep := node.startRow(), node.endRow()
			st.s.NCommentLn += int32(ep-sp) + 1
		} else if node.childCount() == 0 {
			st.nTokens++
			st.nOperands++
			x.addOperand(st, cgPrefix(x.sliceToken(node, ascii, astr), 40))
		}

		x.onNode(node, st, loopDepth, nest, ascii, astr)

		descend := !(prune && x.jk.prune[kind])
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

func maxi32(a, b int32) int32 {
	if a > b {
		return a
	}
	return b
}

func (x *xctx) sliceToken(n tsNode, ascii bool, astr string) string {
	s, e := int(n.startByte()), int(n.endByte())
	if ascii {
		return astr[s:e]
	}
	if x.textOK {
		return x.text[s:e]
	}
	return cgDecode(x.src[s:e])
}

func (x *xctx) txt(n tsNode) string {
	s, e := int(n.startByte()), int(n.endByte())
	if x.asciiOK {
		return x.asciiTxt[s:e]
	}
	if x.textOK {
		return x.text[s:e]
	}
	return cgDecode(x.src[s:e])
}

func clipNRunes(s string, n int) string {
	if len(s) <= n {
		return s
	}
	c := 0
	for i := range s {
		if c == n {
			return s[:i]
		}
		c++
	}
	return s
}

func cgPrefix(s string, n int) string { return clipNRunes(s, n) }

func clipStr(s string, n int) string { return clipNRunes(s, n) }

type edgeKey struct{ a, b int32 }
type csKey struct{ a, b, line int32 }

func (l *linker) resolve() {
	g := l.g

	n := len(g.Sym)
	edgeIdx := make(map[edgeKey]int32, n)
	callsites := make(map[csKey]bool, n+n/2)
	unresIdx := make(map[[2]uint32]int32, n+n/2)
	g.Edges = make([]Edge, 0, n)
	g.Callsite = make([]Callsite, 0, n+n/2)
	g.Unres = make([]Unres, 0, n+n/2)

	l.pending.each(func(p *gpending) {
		name := strings.TrimSpace(g.Str.get(p.name))
		if name == "" {
			return
		}
		base := lastSegment(name)
		if i := strings.LastIndex(base, "::"); i >= 0 {
			base = base[i+2:]
		}
		target := int32(0)
		if p.owner != nullStr {
			if t, ok := g.typeScope[scopeKey{g.Str.intern(base), p.owner}]; ok {
				target = t
			}
		}
		if target == 0 {
			if t, ok := g.byQual[name]; ok {
				target = t
			}
		}
		if target == 0 {
			if t, ok := g.fileScope[scopeKey{g.Str.intern(base),
				uint32(p.fid)}]; ok {
				target = t
			}
		}
		if target == 0 {
			if t, ok := g.unique[base]; ok {
				target = t
			}
		}
		if target == 0 {
			if l.isExternal(name, base, p.fid) {
				l.extBy[p.sym]++
				l.nExt++
			} else {
				k := [2]uint32{uint32(p.sym), g.Str.intern(clipStr(name, 160))}
				if i, ok := unresIdx[k]; ok {
					g.Unres[i].N++
				} else {
					unresIdx[k] = int32(len(g.Unres))
					g.Unres = append(g.Unres, Unres{Caller: p.sym,
						Name: k[1], N: 1, Line: p.line})
				}
				l.nUnres++
			}
			return
		}

		tl := g.symLoc[target]
		ek := edgeKey{p.sym, target}
		if i, ok := edgeIdx[ek]; ok {
			g.Edges[i].NCalls++
		} else {
			edgeIdx[ek] = int32(len(g.Edges))
			g.Edges = append(g.Edges, Edge{Caller: p.sym, Callee: target,
				NCalls: 1, SameFile: boolI32(tl.fid == p.fid),
				SameMod: boolI32(tl.mid == g.symLoc[p.sym].mid),
				IsSelf:  boolI32(target == p.sym)})
		}
		l.nRes++
		if p.line != 0 {
			k := csKey{p.sym, target, p.line}
			if !callsites[k] {
				callsites[k] = true
				g.Callsite = append(g.Callsite, Callsite{p.sym, target, p.line})
			}
		}
	})
	for sid, n := range l.extBy {
		g.Sym[sid-1].NExternalCalls = n
	}
	pct := int32(0)
	if l.nRes+l.nUnres > 0 {
		pct = 100 * l.nRes / (l.nRes + l.nUnres)
	}
	g.buildCallGraph()
	g.addMeta("calls_resolved", sprintf("%d in-tree / %d external / %d unresolved (%d%% of in-scope resolved)",
		l.nRes, l.nExt, l.nUnres, pct))
}

func (l *linker) isExternal(name, base string, fid int32) bool {
	imports := l.g.FileImports[fid]
	if strings.HasPrefix(name, "new ") {
		tname := strings.TrimSpace(name[4:])
		if jdkTypes[tname] {
			return true
		}
		if id, ok := imports[tname]; ok {
			return l.g.outOfTree(l.g.Str.get(id))
		}
		return false
	}
	head := firstSegment(name)
	if jdkTypes[head] {
		return true
	}
	if id, ok := imports[head]; ok {
		return l.g.outOfTree(l.g.Str.get(id))
	}
	if strings.Contains(name, ".") && jdkMethods[base] {
		return true
	}
	return false
}

var importSuffixes = []string{"", ".py", ".pyi", ".ts", ".tsx", ".d.ts",
	".mts", ".cts", ".js", ".jsx", ".mjs", ".cjs", ".rb", ".php", ".go",
	".rs", ".java"}
var importIndexes = []string{"__init__.py", "index.ts", "index.tsx",
	"index.js", "index.mjs", "mod.rs", "lib.rs"}

func (g *Graph) resolveImportTargets() int {
	byPath := make(map[string]int32, len(g.Files)*2)
	for i := range g.Files {
		norm := g.Files[i].Path(g.Str)
		byPath[norm] = g.Files[i].ID

		if d := strings.LastIndexByte(norm, '.'); d > 0 {
			stem := norm[:d]
			if _, ok := byPath[stem]; !ok {
				byPath[stem] = g.Files[i].ID
			}
		}
	}

	var scratch []byte
	look := func(cand string) int32 {
		cand = strings.Trim(cand, "/")
		if cand == "" {
			return 0
		}
		for _, suf := range importSuffixes {
			scratch = append(append(scratch[:0], cand...), suf...)
			if v, ok := byPath[string(scratch)]; ok {
				return v
			}
		}
		for _, idx := range importIndexes {
			scratch = append(append(scratch[:0], cand...), '/')
			scratch = append(scratch, idx...)
			if v, ok := byPath[string(scratch)]; ok {
				return v
			}
		}
		return 0
	}
	n := 0
	for i := range g.Imports {
		im := &g.Imports[i]
		if im.TargetID >= 0 {
			continue
		}
		target := g.Str.get(im.Target)
		if target == "" {
			continue
		}
		t := strings.TrimSpace(target)
		path := g.Files[im.FileID-1].Path(g.Str)
		here := "."
		if i := strings.LastIndexByte(path, '/'); i >= 0 {
			here = path[:i]
		}
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
			for i := 0; i < int(maxi32(0, int32(nUp)-1)); i++ {
				base = pathDir(base)
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
		if hit != 0 && hit != im.FileID {
			im.TargetID = hit
			n++
		}
	}
	g.addMeta("imports_resolved",
		sprintf("%d of %d import rows point at a file in this tree",
			n, len(g.Imports)))
	return n
}

func pathDir(p string) string {
	if i := strings.LastIndexByte(p, '/'); i > 0 {
		return p[:i]
	}
	return ""
}

func (g *Graph) materialize() {

	fanOut := make(map[int32]int32)
	fanIn := make(map[int32]int32)
	recursive := map[int32]bool{}
	for _, e := range g.Edges {
		if e.IsSelf == 0 {
			fanOut[e.Caller]++
			fanIn[e.Callee]++
		} else {
			recursive[e.Caller] = true
		}
	}
	callsites := make(map[int32]int32)
	for _, c := range g.Callsite {
		callsites[c.Callee]++
	}
	unres := make(map[int32]int32)
	for _, u := range g.Unres {
		unres[u.Caller] += u.N
	}

	folded := g.Hazards[:0]
	seenHaz := make(map[[2]uint32]int32, len(g.Hazards))
	for _, h := range g.Hazards {
		k := [2]uint32{uint32(h.SymID), h.Pat}
		if at, ok := seenHaz[k]; ok {
			g.Hazards[at].N += h.N
			continue
		}
		seenHaz[k] = int32(len(folded))
		folded = append(folded, h)
	}
	g.Hazards = folded
	haz := make(map[int32]int32)
	hazCat := make(map[int32]map[string]int32)
	for _, h := range g.Hazards {
		haz[h.SymID] += h.N
		m := hazCat[h.SymID]
		if m == nil {
			m = map[string]int32{}
			hazCat[h.SymID] = m
		}
		m[g.Str.get(h.Cat)] += h.N
	}
	for i := range g.Sym {
		s := &g.Sym[i]
		s.FanOut = fanOut[s.ID]
		s.FanIn = fanIn[s.ID]
		s.NCallsites = callsites[s.ID]
		if recursive[s.ID] {
			s.flags |= fRecursive
		}
		s.NUnresolved = unres[s.ID]
		s.NHazards = haz[s.ID]
		s.setFlag(fLeaf, boolI32(s.FanOut == 0))
		s.setFlag(fRoot, boolI32(s.FanIn == 0))
		if m := hazCat[s.ID]; m != nil {
			for cat, n := range m {
				setCatColumn(s, cat, n)
			}
		}
	}

	agg := make(map[int32]*[6]int32, len(g.Files))
	for i := range g.Sym {
		s := &g.Sym[i]
		a := agg[s.FileID]
		if a == nil {
			a = &[6]int32{}
			agg[s.FileID] = a
		}
		a[0]++
		if isFnKind(s.Kind) {
			a[1]++
		}
		if countsAsType(s.Kind) {
			a[2]++
		}
		a[3] += s.Cyclomatic
		if s.Cyclomatic > a[4] {
			a[4] = s.Cyclomatic
		}
		a[5] += s.RiskScore
	}
	nImp := make(map[int32]int32)
	for _, im := range g.Imports {
		nImp[im.FileID]++
	}
	for i := range g.Files {
		f := &g.Files[i]
		f.NImports = nImp[f.ID]
		if a := agg[f.ID]; a != nil {
			f.NSymbols, f.NFuncs, f.NTypes = a[0], a[1], a[2]
			f.TotalCyc, f.MaxCyc, f.TotalRisk = a[3], a[4], a[5]
		}
	}

	modSyms := make(map[int32]int32)
	modPub := make(map[int32]int32)
	for i := range g.Sym {
		s := &g.Sym[i]
		modSyms[s.ModuleID]++
		modPub[s.ModuleID] += s.getFlag(fPublic)
	}
	modFiles := make(map[int32]int32)
	modSloc := make(map[int32]int32)
	for i := range g.Files {
		f := &g.Files[i]
		modFiles[f.ModuleID]++
		modSloc[f.ModuleID] += f.Sloc
	}

	outSeen := make(map[[2]int32]map[int32]bool)
	inSeen := make(map[[2]int32]map[int32]bool)
	for _, e := range g.Edges {
		a := g.Sym[e.Caller-1]
		b := g.Sym[e.Callee-1]
		if a.ModuleID == b.ModuleID {
			continue
		}
		m := outSeen[[2]int32{a.ModuleID, 0}]
		if m == nil {
			m = map[int32]bool{}
			outSeen[[2]int32{a.ModuleID, 0}] = m
		}
		m[b.ModuleID] = true
		m2 := inSeen[[2]int32{b.ModuleID, 0}]
		if m2 == nil {
			m2 = map[int32]bool{}
			inSeen[[2]int32{b.ModuleID, 0}] = m2
		}
		m2[a.ModuleID] = true
	}
	for i := range g.Mod {
		m := &g.Mod[i]
		m.NSymbols = modSyms[m.ID]
		m.NPublic = modPub[m.ID]
		m.NFiles = modFiles[m.ID]
		m.Sloc = modSloc[m.ID]
		m.FanOut = int32(len(outSeen[[2]int32{m.ID, 0}]))
		m.FanIn = int32(len(inSeen[[2]int32{m.ID, 0}]))
		if m.FanIn+m.FanOut == 0 {
			m.Instability = 0.0
		} else {
			m.Instability = float64(m.FanOut) / float64(m.FanIn+m.FanOut)
		}
	}

	uniq := make(map[int32]int32)
	for _, e := range g.Edges {
		uniq[e.Caller]++
	}
	implT := make(map[string]int32)
	for _, t := range g.TypeRel {
		k := g.Str.get(t.Kind)
		if k == "implements" || k == "extends" {
			implT[g.Str.get(t.ParentNam)]++
		}
	}

	implT = make(map[string]int32)
	seenChild := map[[2]uint32]bool{}
	for _, t := range g.TypeRel {
		k := g.Str.get(t.Kind)
		if k != "implements" && k != "extends" {
			continue
		}
		kk := [2]uint32{t.ParentNam, t.ChildName}
		if seenChild[kk] {
			continue
		}
		seenChild[kk] = true
		implT[g.Str.get(t.ParentNam)]++
	}
	lkAcq := make(map[int32]int32)
	lkRel := make(map[int32]int32)
	for _, o := range g.Locks {
		if g.Str.get(o.Op) == "acquire" {
			lkAcq[o.SymID]++
		} else {
			lkRel[o.SymID]++
		}
	}
	resOpen := make(map[int32]int32)
	for _, r := range g.Res {
		resOpen[r.SymID]++
	}
	throwsDecl := make(map[int32]int32)
	catchBroad := make(map[int32]int32)
	catchEmpty := make(map[int32]int32)
	catchRethrow := make(map[int32]int32)
	for _, e := range g.Excepts {
		switch g.Str.get(e.Kind) {
		case "throws":
			throwsDecl[e.SymID]++
		case "catch":
			if e.IsBroad == 1 {
				catchBroad[e.SymID]++
			}
			if e.IsEmpty == 1 {
				catchEmpty[e.SymID]++
			}
			if e.Rethrows == 1 {
				catchRethrow[e.SymID]++
			}
		}
	}
	serial := make(map[int32]bool)
	for _, t := range g.TypeRel {
		pn := g.Str.get(t.ParentNam)
		if pn == "Serializable" || pn == "Externalizable" {
			serial[t.ChildID] = true
		}
	}
	overCount := make(map[[2]uint32]int32)
	for i := range g.Sym {
		s := &g.Sym[i]
		if (s.Kind == kindMethod || s.Kind == kindConstructor) &&
			s.OwnerType != nullStr {
			overCount[[2]uint32{s.OwnerType, s.Name}]++
		}
	}
	httpTypes := make(map[uint32]bool)
	for i := range g.Sym {
		if g.Sym[i].getFlag(fHTTPExchange) == 1 {
			httpTypes[g.Sym[i].Name] = true
		}
	}

	for i := range g.Sym {
		s := &g.Sym[i]
		s.NUniqueCalls = uniq[s.ID]
		if serial[s.ID] {
			s.flags |= fSerializable
		}
		if c := overCount[[2]uint32{s.OwnerType, s.Name}]; c > 1 {
			s.NOverloads = c - 1
		}
		s.NLockAcquire = lkAcq[s.ID]
		s.NLockRelease = lkRel[s.ID]

		if n, ok := resOpen[s.ID]; ok {
			s.NResourceOpen = n
		}
		s.NThrowsDeclared = throwsDecl[s.ID]
		s.NCatchBroad = catchBroad[s.ID]
		s.NCatchEmpty = catchEmpty[s.ID]
		s.NCatchRethrow = catchRethrow[s.ID]
		if s.NThrowSites > 0 {
			s.NThrow = s.NThrowSites
		}
		if isTypeKind(s.Kind) {
			s.NImplTargets = implT[g.Str.get(s.Name)]
		}
		if s.Kind == kindMethod && s.OwnerType != nullStr && s.getFlag(fAbstract) == 1 &&
			httpTypes[s.OwnerType] {
			s.flags |= fHTTPExchange
		}
		if isFnKind(s.Kind) {
			switch {
			case s.NParams <= 1:
				s.ArityRank = 0
			case s.NParams <= 3:
				s.ArityRank = 1
			case s.NParams <= 6:
				s.ArityRank = 2
			default:
				s.ArityRank = 3
			}
		}
	}

	for i := range g.Sym {
		s := &g.Sym[i]
		risk := int32(2*s.Cyclomatic + s.Cognitive + 4*s.MaxNesting)
		risk += 6*s.NReflection + 14*s.NSerialization + 10*s.NJNI +
			10*s.NUnsafe + 15*s.NExec + 8*s.NSetAccessible
		risk += 4*s.NCatchBroad + 10*s.NCatchEmpty + 2*s.NCatchRethrow
		risk += 3*s.NLockAcquire + 10*s.LockInLoop
		risk += 15*s.QueryInLoop + 2*s.NStringConcat + 8*s.ConcatInLoop
		risk += 6*s.NBoxingInLoop + 10*s.RegexInLoop
		risk += 3*s.NRawTypes + 4*s.NUncheckedCasts
		risk += 6*s.NStaticWrites + 12*s.NFinalizers
		if s.getFlag(fRecursive) == 1 {
			risk += 12
		}
		if s.NResourceOpen > s.NCloseCalls+s.NTryResources {
			risk += 12
		}
		if s.getFlag(fSerializable) == 1 && s.getFlag(fHasSerialUID) == 0 {
			risk += 8
		}
		s.RiskScore = risk

		if s.NTokens > 0 {
			d := float64(s.NDistinctOps + s.NDistinctOperand)
			var mult float64 = 2.0
			if s.NDistinctOps+s.NDistinctOperand > 1 {
				mult = d
			}
			s.HalsteadVolume = int32(float64(s.NOperators+s.NOperands) * mult)
		}
		if isFnKind(s.Kind) {
			slocTerm := 0.05
			if s.Sloc > 1 {
				slocTerm = float64(s.Sloc) / 20.0
			}

			m := fsub(fsub(171, fmul(0.23, float64(s.Cyclomatic))),
				fmul(16.2, slocTerm))
			mi := max(int32(m), 0)
			s.Maintainability = mi
		}
	}

	g.buildReach()

	for _, v := range g.symAdds {
		if v.symID <= 0 {
			continue
		}
		s := &g.Sym[v.symID-1]
		switch v.col {
		case addVolAccess:
			s.NVolatileAccess += v.val
		case addStaticWrites:
			s.NStaticWrites += v.val
		case addThreadlocalOps:
			s.NThreadlocalOps += v.val
		case addThreadlocalRemove:
			s.NThreadlocalRem += v.val
		case addVolatileCompound:
			s.NVolatileCompound += v.val
		case addSharedDatefmtUse:
			s.NSharedDatefmtUse += v.val
		case addStaticCollAdd:
			s.NStaticCollAdd += v.val
		case addStaticCollRemove:
			s.NStaticCollRemove += v.val
		case addJSpecifyAnnos:
			s.NJSpecifyAnnos += v.val
		}
	}
	g.symAdds = nil
}

func setCatColumn(s *Sym, cat string, n int32) {
	switch cat {
	case "reflection":
		s.NReflection = n
	case "serialization":
		s.NSerialization = n
	case "jni":
		s.NJNI = n
	case "exec":
		s.NExec = n
	case "io":
		s.NIO = n
	case "net":
		s.NNet = n
	case "sql":
		s.NSql = n
	case "crypto":
		s.NCrypto = n
	case "concurrency":
		s.NConcurrency = n
	case "lock":
		s.NLock = n
	case "alloc":
		s.NAlloc = n
	case "boxing":
		s.NBoxing = n
	case "string":
		s.NString = n
	case "resource":
		s.NResource = n
	case "unsafe":
		s.NUnsafe = n
	case "control":
		s.NControl = n
	}
}

func (g *Graph) buildReach() {
	isSink := func(s *Sym) bool {
		return s.NReflection > 0 || s.NSetAccessible > 0 || s.NSerialization > 0 ||
			s.NRuntimeExec > 0 || s.NReadObject > 0 || s.NLoadLibrary > 0 ||
			s.NRawStatement > 0 || s.NJNI > 0 || s.NNativeCalls > 0 ||
			s.NFFMDowncall > 0
	}

	type pair struct{ sink, anc int32 }
	best := make(map[[2]int32]int32, 4096)
	var cur []pair
	for i := range g.Sym {
		if !isSink(&g.Sym[i]) {
			continue
		}
		s := g.Sym[i].ID
		best[[2]int32{s, s}] = 0
		cur = append(cur, pair{s, s})
	}
	for depth := int32(1); depth <= 4 && len(cur) > 0; depth++ {
		var next []pair
		for _, pr := range cur {
			lo, hi := g.In.lo(pr.anc), g.In.hi(pr.anc)
			for p := lo; p < hi; p++ {
				e := g.In.Val[p]
				if e.IsSelf == 1 {
					continue
				}
				k := [2]int32{pr.sink, e.Caller}
				if d, ok := best[k]; ok && d <= depth {
					continue
				}
				best[k] = depth
				next = append(next, pair{pr.sink, e.Caller})
			}
		}
		cur = next
	}
	keys := make([][2]int32, 0, len(best))
	for k := range best {
		keys = append(keys, k)
	}
	sort.Slice(keys, func(a, b int) bool {
		if keys[a][0] != keys[b][0] {
			return keys[a][0] < keys[b][0]
		}
		return keys[a][1] < keys[b][1]
	})
	for _, k := range keys {
		g.Reach = append(g.Reach, Reach{Root: k[1], Sym: k[0], Depth: best[k]})
	}
}

func sprintf(format string, args ...any) string {
	return fmt.Sprintf(format, args...)
}

type typeInfo struct {
	parents []string
	vol     map[string]bool
	stat    map[string]bool
	tl      map[string]bool
	df      map[string]bool
	scl     map[string]bool
}

type linker struct {
	g       *Graph
	types   map[string]*typeInfo
	pending pendStore
	extBy   map[int32]int32
	nExt    int32
	nRes    int32
	nUnres  int32
}

type gpending struct {
	sym   int32
	fid   int32
	name  uint32
	owner uint32
	line  int32
}

const pendBlock = 8192

type pendStore struct {
	blocks [][]gpending
	n      int
}

func (ps *pendStore) append(p gpending) {
	bi := len(ps.blocks) - 1
	if bi < 0 || len(ps.blocks[bi]) == pendBlock {
		ps.blocks = append(ps.blocks, make([]gpending, 0, pendBlock))
		bi++
	}
	ps.blocks[bi] = append(ps.blocks[bi], p)
	ps.n++
}

func (ps *pendStore) each(fn func(p *gpending)) {
	for _, b := range ps.blocks {
		for i := range b {
			fn(&b[i])
		}
	}
}

var globalKindByName = func() map[string]uint32 {
	m := map[string]uint32{}
	for i, n := range kindNames {
		m[n] = uint32(i)
	}
	return m
}()

func newLinker(g *Graph) *linker {
	return &linker{g: g, types: map[string]*typeInfo{},
		extBy: map[int32]int32{}}
}

func (l *linker) link(fo *fileOut) {
	g := l.g
	base := int32(len(g.Sym))
	fid := g.Files[fo.idx].ID
	rb := func(id int32) int32 { return reb(id, base) }

	for i := range fo.syms {
		s := fo.syms[i]
		s.ID += base
		s.ParentID = reb(s.ParentID, base)
		s.Kind = globalKindByName[fo.str.get(s.Kind)]
		g.Sym = append(g.Sym, s)
	}

	for i := range fo.params {
		p := &fo.params[i]
		p.SymID = rb(p.SymID)
		g.Params = append(g.Params, *p)
	}
	for i := range fo.fields {
		f := &fo.fields[i]
		f.SymID = rb(f.SymID)
		g.Fields = append(g.Fields, *f)
	}
	for i := range fo.lits {
		v := &fo.lits[i]
		v.ID = int32(len(g.Lits) + 1)
		v.SymID = rb(v.SymID)
		g.Lits = append(g.Lits, *v)
	}
	for i := range fo.markers {
		m := &fo.markers[i]
		m.ID = int32(len(g.Markers) + 1)
		m.SymID = rb(m.SymID)
		g.Markers = append(g.Markers, *m)
	}
	for i := range fo.attrs {
		a := &fo.attrs[i]
		a.ID = int32(len(g.Attrs) + 1)
		a.SymID = rb(a.SymID)
		g.Attrs = append(g.Attrs, *a)
	}
	for i := range fo.hazards {
		h := &fo.hazards[i]
		h.SymID = rb(h.SymID)
		g.Hazards = append(g.Hazards, *h)
	}
	for i := range fo.typeRel {
		t := &fo.typeRel[i]
		t.ID = int32(len(g.TypeRel) + 1)
		t.ChildID = rb(t.ChildID)
		g.TypeRel = append(g.TypeRel, *t)
	}
	for i := range fo.gens {
		t := &fo.gens[i]
		t.ID = int32(len(g.Gens) + 1)
		t.SymID = rb(t.SymID)
		g.Gens = append(g.Gens, *t)
	}
	for i := range fo.jpms {
		t := &fo.jpms[i]
		t.ID = int32(len(g.JPMS) + 1)
		g.JPMS = append(g.JPMS, *t)
	}
	for i := range fo.uisites {
		t := &fo.uisites[i]
		t.ID = int32(len(g.UISites) + 1)
		t.SymID = rb(t.SymID)
		g.UISites = append(g.UISites, *t)
	}
	for i := range fo.secrets {
		t := &fo.secrets[i]
		t.ID = int32(len(g.Secrets) + 1)
		t.SymID = rb(t.SymID)
		g.Secrets = append(g.Secrets, *t)
	}
	for i := range fo.pending {
		p := &fo.pending[i]
		l.pending.append(gpending{sym: rb(p.sym), fid: fid,
			name: p.name, line: p.line,
			owner: g.Str.intern(p.owner)})
	}
	for i := range fo.symAdds {
		a := fo.symAdds[i]
		a.symID = rb(a.symID)
		l.g.symAdds = append(l.g.symAdds, a)
	}

	for _, r := range fo.pkgRoots {
		l.g.PkgRoots = append(l.g.PkgRoots, l.g.Str.intern(r))
		l.g.pkgRootSet[strings.Clone(r)] = true

		l.g.pkgRootLens = nil
	}
	if fo.fileImports != nil {

		m := make(map[string]uint32, len(fo.fileImports))
		keys := make([]string, 0, len(fo.fileImports))
		for k := range fo.fileImports {
			keys = append(keys, k)
		}
		sort.Strings(keys)
		for _, k := range keys {
			m[strings.Clone(k)] = fo.fileImports[k]
		}
		g.FileImports[fid] = m
	}
	for i := range fo.imports {
		im := &fo.imports[i]
		im.ID = int32(len(g.Imports) + 1)
		im.FileID = fid
		if im.Kind == g.Str.intern("import") || im.Kind == g.Str.intern("import static") {
			im.IsExternal = boolI32(l.g.outOfTree(g.Str.get(im.Target)))
		}
		g.Imports = append(g.Imports, *im)
	}

	for i := range fo.ops {
		lo := &fo.ops[i]
		lo.sym = rb(lo.sym)
		if lo.isType {
			for _, gr := range lo.delta.typeGens {
				g.Gens = append(g.Gens, Generic{ID: int32(len(g.Gens) + 1),
					SymID: lo.sym, FileID: fid,
					Owner:   g.Str.intern(clipStr(gr.owner, 120)),
					Name:    g.Str.intern(clipStr(gr.name, 80)),
					Bound:   g.Str.intern(clipStr(gr.bound, 200)),
					SelfRef: boolI32(gr.owner != "" && strings.Contains(gr.bound, gr.owner)),
					OnType:  1, Line: gr.line})
			}
			l.applyDelta(fo, lo.delta)
			continue
		}
		l.functionExtra(fo, lo, fo.src)
	}
}

func reb(id, base int32) int32 {
	if id < 0 {
		return -1
	}
	return id + base
}

func (l *linker) applyDelta(fo *fileOut, d typeDelta) {
	name := strings.Clone(fo.str.get(d.name))
	ti := l.types[name]
	if ti == nil {
		ti = &typeInfo{}
		l.types[name] = ti
	}
	ti.parents = ti.parents[:0]
	for _, p := range d.parents {
		ti.parents = append(ti.parents, strings.Clone(fo.str.get(p)))
	}

	if m := setOf(d.vol); m != nil {
		ti.vol = m
	}
	if m := setOf(d.stat); m != nil {
		ti.stat = m
	}
	if m := setOf(d.tl); m != nil {
		ti.tl = m
	}
	if m := setOf(d.df); m != nil {
		ti.df = m
	}
	if m := setOf(d.scl); m != nil {
		ti.scl = m
	}
}

func setOf(names []string) map[string]bool {
	if len(names) == 0 {
		return nil
	}
	m := make(map[string]bool, len(names))
	for _, n := range names {

		m[strings.Clone(n)] = true
	}
	return m
}

func (l *linker) info(name string) *typeInfo {
	if name == "" {
		return nil
	}
	return l.types[name]
}

func (l *linker) functionExtra(fo *fileOut, lo *linkOp, src []byte) {
	g := l.g
	sid := lo.sym
	fid := g.Files[fo.idx].ID
	line := lo.line

	for _, t := range lo.throws {
		g.Excepts = append(g.Excepts, Exception{ID: int32(len(g.Excepts) + 1),
			SymID: sid, FileID: fid, Kind: g.Str.intern("throws"),
			Type:    g.Str.intern(clipStr(t.name, 120)),
			IsBroad: boolI32(broadExceptions[t.name]),
			IsEmpty: 0, Rethrows: 0, Logs: 0, InLoop: 0, Restores: 0,
			Line: t.line})
	}
	if len(lo.gens) > 0 {
		owner := clipStr(lo.owner+"."+lo.name, 120)
		for _, gr := range lo.gens {
			g.Gens = append(g.Gens, Generic{ID: int32(len(g.Gens) + 1),
				SymID: sid, FileID: fid, Owner: g.Str.intern(owner),
				Name:    g.Str.intern(clipStr(gr.name, 80)),
				Bound:   g.Str.intern(clipStr(gr.bound, 200)),
				SelfRef: boolI32(strings.Contains(gr.bound, gr.name)),
				OnType:  0, Line: gr.line})
		}
	}
	if lo.wantOverride == 1 {
		parents := []string(nil)
		if ti := l.info(lo.owner); ti != nil {
			parents = ti.parents
		}
		p0 := ""
		if len(parents) > 0 {
			p0 = parents[0]
		}
		emit := lo.isAnnotated == 1 || len(parents) > 0
		if emit {
			g.Over = append(g.Over, Override{ID: int32(len(g.Over) + 1),
				SymID: sid, FileID: fid,
				MethodName:  g.Str.intern(clipStr(lo.name, 120)),
				OwnerType:   g.Str.intern(clipStr(lo.owner, 120)),
				ParentType:  g.Str.intern(clipStr(p0, 120)),
				IsAnnotated: lo.isAnnotated, IsFwEntry: lo.isFwEntry,
				NParams: lo.nPar, Line: line})
		}
	}

	ti := l.info(lo.owner)
	var volatiles, statics, tlocals, datefmts, statcolls map[string]bool
	if ti != nil {
		volatiles, statics = ti.vol, ti.stat
		tlocals, datefmts, statcolls = ti.tl, ti.df, ti.scl
	}
	var nVol, nStaticWrite, nTLOps, nTLRem, nVolCmp, nDFUse, nCollAdd, nCollRem int32
	acq := int32(0)

	for _, ev := range lo.events {
		switch ev.kind {
		case evSync:
			target := ev.s1
			if target == "" {
				target = "this"
			}
			g.Locks = append(g.Locks, LockOp{ID: int32(len(g.Locks) + 1),
				SymID: sid, FileID: fid, LockName: g.Str.intern(target),
				Op: g.Str.intern("acquire"), Kind: g.Str.intern("synchronized"),
				AcqOrder: acq, InLoop: boolI32(ev.depth > 0),
				HoldsIO: ev.f1, HoldsSleep: ev.f2, HoldsAlloc: ev.f3,
				HoldsCall: ev.f4, RegionSloc: ev.f5, Line: ev.line})
			g.Locks = append(g.Locks, LockOp{ID: int32(len(g.Locks) + 1),
				SymID: sid, FileID: fid, LockName: g.Str.intern(target),
				Op: g.Str.intern("release"), Kind: g.Str.intern("synchronized"),
				AcqOrder: acq, InLoop: boolI32(ev.depth > 0), Line: ev.endLine})
			acq++
		case evMethodInv:
			mname, recv := ev.s1, ev.s2
			switch mname {
			case "lock", "lockInterruptibly", "tryLock":
				kind := "lock"
				if strings.Contains(recv, "ReadLock") ||
					strings.Contains(recv, "WriteLock") {
					kind = "rwlock"
				}
				lockName := recv
				if lockName == "" {
					lockName = "?"
				}
				g.Locks = append(g.Locks, LockOp{
					ID: int32(len(g.Locks) + 1), SymID: sid, FileID: fid,
					LockName: g.Str.intern(lockName), Op: g.Str.intern("acquire"),
					Kind: g.Str.intern(kind), AcqOrder: acq, InLoop: boolI32(ev.depth > 0),
					HoldsIO: ev.f3, HoldsSleep: ev.f4, HoldsAlloc: ev.f5,
					HoldsCall: ev.f6, RegionSloc: ev.f7, Line: ev.line})
				acq++
			case "unlock", "unlockRead", "unlockWrite":
				lockName := recv
				if lockName == "" {
					lockName = "?"
				}
				g.Locks = append(g.Locks, LockOp{
					ID: int32(len(g.Locks) + 1), SymID: sid, FileID: fid,
					LockName: g.Str.intern(lockName), Op: g.Str.intern("release"),
					Kind: g.Str.intern("lock"), AcqOrder: maxi32(0, acq-1), Line: ev.line})
			default:
				if opensResource(mname, recv) {
					ob := mname
					if recv != "" {
						ob = recv + "." + mname
					}
					g.Res = append(g.Res, Resource{ID: int32(len(g.Res) + 1),
						SymID: sid, FileID: fid, Name: g.Str.intern(""),
						Type:           g.Str.intern(clipStr(mname, 80)),
						OpenedBy:       g.Str.intern(clipStr(ob, 120)),
						InTryResources: ev.f1, ClosedInFn: lo.closes,
						InLoop: boolI32(ev.depth > 0), Line: ev.line})
				}
			}
			if recv != "" && tlocals[recv] {
				switch mname {
				case "set", "get", "withInitial":
					nTLOps++
				case "remove":
					nTLRem++
				}
			}
			switch mname {
			case "wait", "notify", "notifyAll":
				mon := lastSegment(recv)
				g.MonOps = append(g.MonOps, MonitorOp{
					ID: int32(len(g.MonOps) + 1), SymID: sid, FileID: fid,
					Monitor: g.Str.intern(clipStr(mon, 80)),
					Op:      g.Str.intern(mname), InSync: ev.f2, Line: ev.line})
			}
			if baseRecv := lastSegment(recv); recv != "" && statcolls[baseRecv] {
				if staticCollAdds[mname] {
					nCollAdd++
				} else if staticCollRemoves[mname] {
					nCollRem++
				}
			}
		case evObjCreate:
			if resourceTypes[ev.s1] {
				g.Res = append(g.Res, Resource{ID: int32(len(g.Res) + 1),
					SymID: sid, FileID: fid, Name: g.Str.intern(""),
					Type:           g.Str.intern(clipStr(ev.s1, 80)),
					OpenedBy:       g.Str.intern(clipStr("new "+ev.s1, 120)),
					InTryResources: ev.f1, ClosedInFn: lo.closes,
					InLoop: boolI32(ev.depth > 0), Line: ev.line})
			}
			if strings.Contains(ev.s1, "ThreadLocal") {
				nTLOps++
			}
		case evResource:
			g.Res = append(g.Res, Resource{ID: int32(len(g.Res) + 1),
				SymID: sid, FileID: fid,
				Name:           g.Str.intern(clipStr(ev.s1, 80)),
				Type:           g.Str.intern(clipStr(ev.s2, 80)),
				OpenedBy:       g.Str.intern(clipStr(ev.s3, 120)),
				InTryResources: 1, ClosedInFn: 1, Line: ev.line})
		case evCatch:
			var types []string
			if ev.s1 != "" {
				types = strings.Split(ev.s1, "\x00")
			}
			for _, t := range types {
				g.Excepts = append(g.Excepts, Exception{
					ID: int32(len(g.Excepts) + 1), SymID: sid, FileID: fid,
					Kind: g.Str.intern("catch"), Type: g.Str.intern(clipStr(t, 120)),
					IsBroad: boolI32(broadExceptions[t]), IsEmpty: ev.f1,
					Rethrows: ev.f2, Logs: ev.f3, InLoop: boolI32(ev.depth > 0),
					Restores: ev.f4, Line: ev.line})
			}
		case evThrow:
			g.Excepts = append(g.Excepts, Exception{
				ID: int32(len(g.Excepts) + 1), SymID: sid, FileID: fid,
				Kind: g.Str.intern("throw"), Type: g.Str.intern(clipStr(ev.s1, 120)),
				IsBroad: boolI32(broadExceptions[ev.s1]),
				InLoop:  boolI32(ev.depth > 0), Line: ev.line})
		case evAssign:
			if statics[ev.s1] {
				nStaticWrite++
			}
			if ev.s2 != "" && ev.s2 != "=" && volatiles[ev.s1] {
				nVolCmp++
			}
		case evUpdate:
			if volatiles[ev.s1] {
				nVolCmp++
			}
		case evIfDCL:
			g.Hazards = append(g.Hazards, Hazard{SymID: sid,
				Pat: g.Str.intern("double-checked-locking"), Cat: g.Str.intern("lock"),
				N: 1, Line: ev.line})
		}
	}

	if volatiles != nil || datefmts != nil {
		for i := lo.identLo; i < lo.identHi; i++ {
			sp := fo.identSpans[i]
			nb := string(src[sp[0]:sp[1]])
			if volatiles[nb] {
				nVol++
			}
			if datefmts[nb] {
				nDFUse++
			}
		}
	}
	add := func(col int8, v int32) {
		if v > 0 {
			g.symAdds = append(g.symAdds, symAdd{col: col, val: v, symID: sid})
		}
	}
	add(addVolAccess, nVol)
	add(addStaticWrites, nStaticWrite)
	add(addThreadlocalOps, nTLOps)
	add(addThreadlocalRemove, nTLRem)
	add(addVolatileCompound, nVolCmp)
	add(addSharedDatefmtUse, nDFUse)
	add(addStaticCollAdd, nCollAdd)
	add(addStaticCollRemove, nCollRem)
	if lo.native == 1 {
		g.Hazards = append(g.Hazards, Hazard{SymID: sid,
			Pat: g.Str.intern("native-method"), Cat: g.Str.intern("jni"), N: 1, Line: line})
	}
}

func (x *xctx) parseFile(cst, data []byte, text string, rec *File) {
	tree, terr := decodeCST(x.p, cst, data)
	if terr != nil {
		panic(fmt.Sprintf("cli cst decode failed: %v", terr))
	}
	defer tree.close()
	if x.keepTrees {
		x.out.recs = append(x.out.recs[:0], tree.recs...)
	}
	root := tree.root()
	if root.hasError() {
		x.out.parseErr, x.out.missing = countErrors(root, x.jk)
	}
	x.parseImports(root)
	x.walkScope(root, scope{symID: -1})
	x.emitModuleScope(root, text)
	x.parseFileExtra(root, text)
}

func countErrors(root tsNode, jk *jkinds) (int32, int32) {
	var errs, miss int32
	walkPre(root, func(n tsNode) bool {
		if jk.names[n.kindID()] == "ERROR" {
			errs++
		} else if n.isMissing() {
			miss++
		}
		return true
	})
	return errs, miss
}

func (x *xctx) parseImports(root tsNode) {
	for n := range eachNamedKid(root) {
		t := x.jk.names[n.kindID()]
		if t == "package_declaration" {
			pkg := ""
			for c := range eachNamedKid(n) {
				ct := x.jk.names[c.kindID()]
				if ct == "scoped_identifier" || ct == "identifier" {
					pkg = strings.TrimSpace(x.txt(c))
				}
			}
			if pkg != "" {
				parts := strings.Split(pkg, ".")
				r3 := pkg
				if len(parts) >= 3 {
					r3 = strings.Join(parts[:3], ".")
				}
				x.out.pkgRoots = append(x.out.pkgRoots, r3)
			}
			continue
		}
		if t != "import_declaration" {
			continue
		}
		txt := x.txt(n)
		static := strings.Contains(txt, " static ")
		wildcard := strings.Contains(txt, "*")
		target := ""
		for c := range eachNamedKid(n) {
			ct := x.jk.names[c.kindID()]
			if ct == "scoped_identifier" || ct == "identifier" {
				target = strings.TrimSpace(x.txt(c))
			}
		}
		if target == "" {
			continue
		}
		if !wildcard {
			if x.out.fileImports == nil {
				x.out.fileImports = map[string]uint32{}
			}
			simple := lastSegment(target)
			if _, ok := x.out.fileImports[simple]; !ok {
				x.out.fileImports[simple] = x.str.intern(target)
			}
		}
		kind := "import"
		if static {
			kind = "import static"
		}
		x.out.imports = append(x.out.imports, Import{
			FileID: x.rec.ID, Target: x.str.intern(clipStr(target, 300)),
			TargetID: -1, HasAlias: 0, Kind: x.str.intern(kind),
			Line: int32(n.startRow()) + 1, IsExternal: 0,
			IsRelative: 0, IsWildcard: boolI32(wildcard), IsTypeOnly: 0,
			IsDynamic: 0, NNames: 1,
		})
	}
}

func (x *xctx) parseFileExtra(root tsNode, text string) {

	for _, m := range findModuleImports(text) {
		name := m[0].(string)
		line := int32(m[1].(int))
		x.out.jpms = append(x.out.jpms, JPMS{FileID: x.rec.ID,
			Kind: x.str.intern("import-module"), ModuleNam: x.str.intern(name),
			Target: x.str.intern(""), Line: line})
		x.out.imports = append(x.out.imports, Import{
			FileID: x.rec.ID, Target: x.str.intern(clipStr(name, 300)),
			TargetID: -1, HasAlias: 0, Kind: x.str.intern("import module"),
			Line: line, IsExternal: 1, IsRelative: 0, IsWildcard: 1,
			IsTypeOnly: 0, IsDynamic: 0, NNames: 1,
		})
	}

	for top := range eachNamedKid(root) {
		if x.jk.names[top.kindID()] == "module_declaration" {
			x.walkModuleDirectives(top)
		}
	}
}

func (x *xctx) walkModuleDirectives(top tsNode) {
	cur := tsWalk(top)
	defer cur.free()
	for {
		n := cur.node()
		t := x.jk.names[n.kindID()]
		switch t {
		case "requires_module_directive":
			mod := n.childByFieldName(fModule)
			txt := x.txt(n)
			name := ""
			if mod.ok() {
				name = x.txt(mod)
			}
			x.out.jpms = append(x.out.jpms, JPMS{FileID: x.rec.ID,
				Kind: x.str.intern("requires"), ModuleNam: x.str.intern(name),
				Transitive: boolI32(strings.Contains(txt, " transitive")),
				IsStatic:   boolI32(strings.Contains(txt, " static")),
				Line:       int32(n.startRow()) + 1})
		case "exports_module_directive", "opens_module_directive",
			"uses_module_directive", "provides_module_directive":
			var kids []tsNode
			for c := range eachNamedKid(n) {
				ct := x.jk.names[c.kindID()]
				if ct == "scoped_identifier" || ct == "identifier" {
					kids = append(kids, c)
				}
			}
			first, rest := "", ""
			if len(kids) > 0 {
				first = x.txt(kids[0])
			}
			for i := 1; i < len(kids); i++ {
				if i > 1 {
					rest += ","
				}
				rest += x.txt(kids[i])
			}
			x.out.jpms = append(x.out.jpms, JPMS{FileID: x.rec.ID,
				Kind:      x.str.intern(strings.SplitN(t, "_", 2)[0]),
				ModuleNam: x.str.intern(first),
				Target:    x.str.intern(clipStr(rest, 200)),
				Line:      int32(n.startRow()) + 1})
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

type stackItem struct {
	n  tsNode
	sc scope
}

func (x *xctx) walkScope(root tsNode, sc scope) {

	stack := x.walkStack[:0]
	for i := root.namedChildCount() - 1; i >= 0; i-- {
		stack = append(stack, stackItem{root.namedChild(i), sc})
	}
	for len(stack) > 0 {
		it := stack[len(stack)-1]
		stack = stack[:len(stack)-1]
		cur, s := it.n, it.sc
		k := cur.kindID()
		if fk := x.jk.funcKind[k]; fk != "" {
			sid := x.emitFunction(cur, fk, s)
			nm := x.name(cur)
			if nm == "" {
				nm = "?"
			}
			stack = x.pushBody(stack, cur, scope{sid, s.qualPre + nm + ".",
				s.typeName, s.typeID})
			continue
		}
		if tk := x.jk.typeKind[k]; tk != "" {
			sid := x.emitType(cur, tk, s)
			nm := x.name(cur)
			if nm == "" {
				nm = "?"
			}
			stack = x.pushBody(stack, cur, scope{sid, s.qualPre + nm + ".", nm, sid})
			continue
		}
		for i := cur.namedChildCount() - 1; i >= 0; i-- {
			stack = append(stack, stackItem{cur.namedChild(i), s})
		}
	}
	x.walkStack = stack[:0]
}

func (x *xctx) pushBody(stack []stackItem, node tsNode, inner scope) []stackItem {
	body := node.childByFieldName(fBody)
	if !body.ok() {
		body = node
	}
	for i := body.namedChildCount() - 1; i >= 0; i-- {
		stack = append(stack, stackItem{body.namedChild(i), inner})
	}
	return stack
}

func (x *xctx) emitFunction(node tsNode, kind string, sc scope) int32 {
	name := x.name(node)
	if name == "" {
		name = "(anonymous)"
	}
	qual := sc.qualPre + name
	body := node.childByFieldName(fBody)
	if !body.ok() {
		body = node
	}
	x.trackIdentifiers = true
	x.curBody = body
	st := x.measure(body, false)
	x.trackIdentifiers = false
	x.curBody = tsNode{}

	m := &st.s
	m.Cyclomatic = st.cyclomatic
	m.Cognitive = st.cognitive
	m.MaxNesting = st.maxNesting
	m.MaxLoopDepth = st.maxLoopDepth
	m.NTokens = st.nTokens
	m.NOperators = st.nOperators
	m.NOperands = st.nOperands
	m.NDistinctOps = st.nDistOps
	m.NDistinctOperand = st.nDistOperand
	m.Sloc = x.slocOf(node)
	m.BodyBytes = int32(body.endByte()) - int32(body.startByte())

	if params := node.childByFieldName(fParameters); params.ok() {
		var nNamed, optional int32
		for pi := 0; pi < params.namedChildCount(); pi++ {
			c := params.namedChild(pi)
			ct := x.jk.names[c.kindID()]
			if commentNodes[ct] {
				continue
			}
			nNamed++
			if strings.HasPrefix(ct, "optional") ||
				c.childByFieldName(fValue).ok() ||
				c.childByFieldName(fDefaultValue).ok() {
				optional++
			}
		}
		m.NParams = nNamed
		m.NOptionalParams = optional
	}
	x.functionFlags(node, name, kind, sc, m)

	doc := x.docstringLines(node)
	m.NDocLines = doc
	m.HasDoc = boolI32(doc > 0)

	rt := ""
	if r := node.childByFieldName(fType); r.ok() {
		rt = strings.TrimSpace(x.txt(r))
	}
	sid := x.insertSymbol(name, kind, qual, sc.symID, node, x.signatureOf(node),
		rt, x.visibilityOf(node), m)

	x.emitParams(node, sid)
	x.emitAttributes(node, sid)
	for _, c := range st.calls {
		if c.name == "" {
			continue
		}
		x.out.pending = append(x.out.pending, pending{sid,
			x.str.intern(clipStr(c.name, 200)), c.line, sc.typeName})
	}
	x.emitHazards(st, sid)
	x.emitInputSites(st, sid)
	for _, l := range st.lits {
		x.out.lits = append(x.out.lits, Literal{SymID: sid, FileID: x.rec.ID,
			Kind:  x.str.intern(l.kind),
			Value: x.str.intern(clipStr(l.value, 200)),
			Line:  l.line, IsMagic: l.magic})
	}

	btxt := x.txt(body)
	closes := int32(0)
	if strings.Contains(btxt, ".close()") || strings.Contains(btxt, "closeQuietly") {
		closes = 1
	}
	lo := linkOp{sym: sid, closes: closes, kind: kind, name: name,
		owner: sc.typeName, line: int32(node.startRow()) + 1,
		identLo: int32(len(x.out.identSpans))}

	evLo := int32(len(x.out.evBuf))
	for _, ev := range st.events {
		if ev.kind == evIdent {
			x.out.identSpans = append(x.out.identSpans, [2]uint32{uint32(ev.f1), uint32(ev.f2)})
			continue
		}
		x.out.evBuf = append(x.out.evBuf, ev)
	}
	lo.events = x.out.evBuf[evLo:]
	lo.identHi = int32(len(x.out.identSpans))
	x.captureDtails(node, &lo)
	x.out.ops = append(x.out.ops, lo)
	return sid
}

func (x *xctx) captureDtails(node tsNode, lo *linkOp) {
	for ci := 0; ci < node.namedChildCount(); ci++ {
		c := node.namedChild(ci)
		if x.jk.names[c.kindID()] != "throws" {
			continue
		}
		for ti := 0; ti < c.namedChildCount(); ti++ {
			t := c.namedChild(ti)
			switch x.jk.names[t.kindID()] {
			case "type_identifier", "scoped_type_identifier", "generic_type":
				lo.throws = append(lo.throws, throwRec{
					name: simpleType(x.txt(t)),
					line: int32(c.startRow()) + 1})
			}
		}
	}
	if tp := node.childByFieldName(fTypeParams); tp.ok() {
		for ti := 0; ti < tp.namedChildCount(); ti++ {
			t := tp.namedChild(ti)
			if x.jk.names[t.kindID()] != "type_parameter" {
				continue
			}
			bound := ""
			for c := range eachNamedKid(t) {
				if x.jk.names[c.kindID()] == "type_bound" {
					bound = strings.TrimSpace(x.txt(c))
				}
			}
			lo.gens = append(lo.gens, genRec{
				name:  clipStr(x.name(t), 80),
				bound: clipStr(bound, 200),
				line:  int32(t.startRow()) + 1})
		}
	}
	annos := x.annotations(node)
	if lo.kind == "method" && lo.name != "" {
		lo.wantOverride = 1
		lo.isAnnotated = boolI32(annos["Override"])
		fw := 0
		for a := range annos {
			if frameworkAnnotations[a] {
				fw = 1
				break
			}
		}
		if handlerMethods[lo.name] {
			fw = 1
		}
		lo.isFwEntry = int32(fw)
		if params := node.childByFieldName(fParameters); params.ok() {
			var n int32
			for c := range eachNamedKid(params) {
				switch x.jk.names[c.kindID()] {
				case "formal_parameter", "spread_parameter":
					n++
				}
			}
			lo.nPar = n
		}
	}
	lo.native = boolI32(hasWord(x.modifiers(node), "native"))
}

func (x *xctx) functionFlags(node tsNode, name, kind string, sc scope,
	m *Sym) {
	mods := x.modifiers(node)
	annos := x.annotations(node)
	sig := x.signatureOf(node)
	body := node.childByFieldName(fBody)
	btxt := ""
	if body.ok() {
		btxt = x.txt(body)
	}
	ptxt := ""
	if p := node.childByFieldName(fParameters); p.ok() {
		ptxt = x.txt(p)
	}
	isIfaceMember := sc.typeName != "" && !body.ok()

	pooled := false
	for _, w := range pooledExecutorWords {
		if hasWordBounds(btxt, w) {
			pooled = true
			break
		}
	}
	virtual := false
	for _, w := range virtualThreadWords {
		if hasWordBounds(btxt, w) {
			virtual = true
			break
		}
	}
	isCtor := x.jk.names[node.kindID()] == "constructor_declaration"
	flex := int32(0)
	if isCtor && x.isFlexConstructor(node) {
		flex = 1
	}
	var resil, jspec int32
	for a := range annos {
		if resilienceAnnotations[a] {
			resil++
		}
		switch a {
		case "NonNull", "Nullable", "CheckForNull":
			jspec++
		}
	}
	// A "version" argument cannot exist unless the modifiers text spells it,
	// so skip the nested annotation walk for the ~all functions without it.
	verAttr := 0
	if strings.Contains(mods, "version") {
		verAttr = len(x.annotationArgValues(node, "version"))
	}

	hasPub := strings.Contains(mods, "public")
	hasProt := strings.Contains(mods, "protected")
	hasPriv := strings.Contains(mods, "private")
	_ = hasProt
	_ = hasPriv
	var isPub int32
	if hasPub || (mods == "" && sc.typeName == "") {
		isPub = 1
	}
	var isAbs int32
	if hasWordBounds(mods, "abstract") || (isIfaceMember &&
		x.jk.names[node.kindID()] == "method_declaration") {
		isAbs = 1
	}
	params := node.childByFieldName(fParameters)

	m.setFlag(fPublic, isPub)
	m.setFlag(fStatic, boolI32(hasWordBounds(mods, "static")))
	m.setFlag(fAbstract, isAbs)
	m.setFlag(fOverride, boolI32(annos["Override"]))
	m.setFlag(fDeprecated, boolI32(annos["Deprecated"]))
	isTest := 0
	for _, a := range []string{"Test", "ParameterizedTest", "RepeatedTest",
		"Benchmark"} {
		if annos[a] {
			isTest = 1
		}
	}
	if strings.HasPrefix(name, "test") {
		isTest = 1
	}
	m.setFlag(fTest, int32(isTest))
	m.setFlag(fEntrypoint, boolI32(name == "main" || name == "<clinit>"))
	handler := 0
	for a := range annos {
		if handlerAnnotations[a] {
			handler = 1
			break
		}
	}
	if handlerMethods[name] {
		handler = 1
	}
	m.setFlag(fHandler, int32(handler))
	m.setFlag(fVtRoot, boolI32(virtual))
	m.setFlag(fExecRoot, boolI32(pooled || virtual))
	m.setFlag(fPoolRoot, boolI32(pooled))
	m.OwnerType = x.str.intern(clipStr(sc.typeName, 120))
	m.NSyncMethods = boolI32(hasWordBounds(mods, "synchronized"))
	m.NNativeCalls = boolI32(hasWordBounds(mods, "native"))
	m.NFinalizers = boolI32(name == "finalize")
	m.NAnnotations = int32(len(annos))
	m.NSuppressions = boolI32(annos["SuppressWarnings"])
	m.NGenericParams = x.countTypeParams(node)

	m.NRawTypes = int32(rawTypeCount(sig) + rawTypeCountBounded(btxt))
	m.NWildcardTypes = int32(strings.Count(ptxt, "?"))
	m.NParams = x.countParams(params)
	m.setFlag(fFlexCtor, flex)
	m.NResilienceAnnos = resil
	m.NApiVersionAttr = int32(minI(verAttr, 9))
	m.NJSpecifyAnnos = jspec
	m.NEe12Annos = x.qualifiedEE12Annos(node)
}

func minI(a, b int) int {
	if a < b {
		return a
	}
	return b
}

func (x *xctx) visibilityOf(node tsNode) string {
	mods := x.modifiers(node)
	switch {
	case hasWordBounds(mods, "public"):
		return "public"
	case hasWordBounds(mods, "protected"):
		return "protected"
	case hasWordBounds(mods, "private"):
		return "private"
	}
	return "package"
}

func (x *xctx) insertSymbol(name, kind, qual string, parentID int32,
	node tsNode, signature, retType, visibility string, m *Sym) int32 {
	x.nextID++
	s := *m
	s.ID = x.nextID
	s.FileID = x.rec.ID
	s.ModuleID = x.rec.ModuleID
	s.ParentID = parentID
	s.Name = x.str.intern(name)
	s.QualName = x.str.intern(clipStr(qual, 400))
	s.Kind = x.kindID(kind)
	ls := int32(node.startRow()) + 1
	le := int32(node.endRow()) + 1
	s.LineStart = ls
	s.LineEnd = le
	s.NLines = le - ls + 1
	s.ByteStart = int32(node.startByte())
	s.ByteEnd = int32(node.endByte())
	s.Signature = x.str.intern(clipStr(signature, 400))
	s.RetType = x.str.intern(clipStr(retType, 200))
	s.Vis = x.str.intern(visibility)
	s.OwnerType = x.str.intern(x.str.get(s.OwnerType))
	x.out.syms = append(x.out.syms, s)
	return x.nextID
}

func (x *xctx) emitParams(node tsNode, sid int32) {
	params := node.childByFieldName(fParameters)
	if !params.ok() {
		return
	}
	if x.jk.names[params.kindID()] == "identifier" {
		x.out.params = append(x.out.params, Param{SymID: sid,
			Name: x.str.intern(clipStr(x.txt(params), 120)),
			Type: x.str.intern(""), HasDefault: 0, Default: nullStr,
			IsOptional: 0, IsVariadic: 0, IsRef: 0, IsMutable: 0,
			IsNullable: 0, IsGeneric: 0, IsUntyped: 1, TypeDepth: 0})
		return
	}
	pos := int32(0)
	for pi := 0; pi < params.namedChildCount(); pi++ {
		p := params.namedChild(pi)
		pt := x.jk.names[p.kindID()]
		if commentNodes[pt] {
			continue
		}
		var name, ptype string
		variadic := int32(0)
		switch pt {
		case "spread_parameter":
			variadic = 1
			kn := p.namedChildCount()
			if kn > 0 {
				ptype = strings.TrimSpace(x.txt(p.namedChild(0))) + "..."
			}
			for k := range kn {
				c := p.namedChild(k)
				if x.jk.names[c.kindID()] == "variable_declarator" {
					if nm := c.childByFieldName(fName); nm.ok() {
						name = strings.TrimSpace(x.txt(nm))
					}
				}
			}
		case "formal_parameter", "receiver_parameter":
			if tn := p.childByFieldName(fType); tn.ok() {
				ptype = strings.TrimSpace(x.txt(tn))
			}
			if nm := p.childByFieldName(fName); nm.ok() {
				name = strings.TrimSpace(x.txt(nm))
			}
		case "identifier":
			name = strings.TrimSpace(x.txt(p))
		default:
			continue
		}
		annos := x.annotations(p)
		jspec := 0
		for _, a := range []string{"NonNull", "Nullable", "CheckForNull"} {
			if annos[a] {
				jspec = 1
			}
		}
		if jspec == 1 {
			x.out.symAdds = append(x.out.symAdds,
				symAdd{col: addJSpecifyAnnos, val: 1, symID: sid})
		}
		if name == "" {
			name = "?"
		}
		x.out.params = append(x.out.params, Param{
			SymID: sid, Pos: pos, Name: x.str.intern(clipStr(name, 120)),
			Type: x.str.intern(clipStr(ptype, 200)), HasDefault: 0,
			Default: nullStr, IsOptional: int32(jspec), IsVariadic: variadic,
			IsRef: 0, IsMutable: 0, IsNullable: int32(jspec),
			IsGeneric: boolI32(strings.Contains(ptype, "<")),
			IsUntyped: boolI32(ptype == ""),
			TypeDepth: int32(strings.Count(ptype, "<") +
				strings.Count(ptype, "["))})
		pos++
	}
}

func (x *xctx) emitAttributes(node tsNode, sid int32) {
	for ci := 0; ci < node.namedChildCount(); ci++ {
		c := node.namedChild(ci)
		if x.jk.names[c.kindID()] != "modifiers" {
			continue
		}
		for ai := 0; ai < c.namedChildCount(); ai++ {
			a := c.namedChild(ai)
			at := x.jk.names[a.kindID()]
			if at != "annotation" && at != "marker_annotation" {
				continue
			}
			nm := a.childByFieldName(fName)
			args := a.childByFieldName(fArguments)
			name := "?"
			if nm.ok() {
				name = clipStr(lastSegment(x.txt(nm)), 120)
			}
			at2 := Attr{SymID: sid, FileID: x.rec.ID,
				Name: x.str.intern(name), Line: int32(a.startRow()) + 1}
			if args.ok() {
				at2.HasArgs = 1
				at2.Args = x.str.intern(clipStr(x.txt(args), 200))
			}
			x.out.attrs = append(x.out.attrs, at2)
		}
		break
	}
}

func (x *xctx) emitHazards(st *bstats, sid int32) {
	type key struct {
		cat  uint32
		n    int32
		line int32
	}
	var order []string
	seen := map[string]*key{}
	for _, c := range st.calls {
		if c.name == "" {
			continue
		}
		pat, cat, ok := hazardOf(c.name)
		if !ok {
			continue
		}
		if e, exists := seen[pat]; exists {
			e.n++
			continue
		}
		k := &key{x.str.intern(cat), 1, c.line}
		seen[pat] = k
		order = append(order, pat)
	}
	for _, pat := range order {
		k := seen[pat]
		x.out.hazards = append(x.out.hazards, Hazard{SymID: sid,
			Pat: x.str.intern(clipStr(pat, 120)), Cat: k.cat, N: k.n, Line: k.line})
	}
}

func hazardOf(callee string) (string, string, bool) {
	if cat, ok := hazardCalls[callee]; ok {
		return callee, cat, true
	}
	if strings.HasPrefix(callee, "new ") {
		return "", "", false
	}
	base := lastSegment(callee)
	if cat, ok := hazardCalls[base]; ok {
		return "*." + base, cat, true
	}
	return "", "", false
}

func (x *xctx) emitInputSites(st *bstats, sid int32) {
	for _, s := range st.inputSites {
		x.out.uisites = append(x.out.uisites, InputSite{SymID: sid,
			FileID: x.rec.ID, Var: x.str.intern(s.varName), Kind: s.kind,
			Line: s.line, InLoop: s.inLoop})
	}
	for _, s := range st.secrets {
		x.out.secrets = append(x.out.secrets, Secret{SymID: sid,
			FileID: x.rec.ID, Value: x.str.intern(s.value), Line: s.line})
	}
}

func (x *xctx) emitType(node tsNode, kind string, sc scope) int32 {
	name := x.name(node)
	if name == "" {
		name = "(anonymous)"
	}
	qual := sc.qualPre + name
	body := node.childByFieldName(fBody)
	if !body.ok() {
		body = node
	}
	x.curBody = body
	bstats := x.measure(body, true)
	x.curBody = tsNode{}

	m := &bstats.s
	m.Sloc = x.slocOf(node)
	m.NTokens = bstats.nTokens
	m.NOperators = bstats.nOperators
	m.NOperands = bstats.nOperands
	x.typeFlags(node, name, kind, sc, m)

	doc := x.docstringLines(node)
	m.NDocLines = doc
	m.HasDoc = boolI32(doc > 0)

	sig := strings.TrimSpace(strings.SplitN(x.txt(node), "{", 2)[0])
	sid := x.insertSymbol(name, kind, qual, sc.symID, node,
		clipStr(sig, 300), "", x.visibilityOf(node), m)

	x.emitAttributes(node, sid)
	for _, c := range bstats.calls {
		if c.name == "" {
			continue
		}
		x.out.pending = append(x.out.pending, pending{sid,
			x.str.intern(clipStr(c.name, 200)), c.line, sc.typeName})
	}
	x.emitHazards(bstats, sid)
	x.typeExtra(node, name, kind, body, sid)
	return sid
}

func (x *xctx) typeFlags(node tsNode, name, kind string, sc scope, m *Sym) {
	mods := x.modifiers(node)
	annos := x.annotations(node)
	parents := x.supertypePairs(node)
	body := node.childByFieldName(fBody)
	btxt := ""
	if body.ok() {
		btxt = x.txt(body)
	}
	serial := 0
	for _, p := range parents {
		if p[0] == "Serializable" || p[0] == "Externalizable" {
			serial = 1
		}
	}
	httpClient := 0
	if x.jk.names[node.kindID()] == "interface_declaration" {
		for a := range annos {
			if httpExchangeAnnotations[a] {
				httpClient = 1
				break
			}
		}
	}
	m.setFlag(fPublic, boolI32(strings.Contains(mods, "public")))
	m.setFlag(fStatic, boolI32(hasWordBounds(mods, "static")))
	var abs int32
	if hasWordBounds(mods, "abstract") ||
		x.jk.names[node.kindID()] == "interface_declaration" {
		abs = 1
	}
	m.setFlag(fAbstract, abs)
	m.setFlag(fDeprecated, boolI32(annos["Deprecated"]))
	m.setFlag(fSerializable, int32(serial))
	head := btxt
	if len(head) > 200000 {
		head = head[:200000]
	}
	m.setFlag(fHasSerialUID, boolI32(strings.Contains(head, "serialVersionUID")))
	handler := 0
	for a := range annos {
		if handlerAnnotations[a] {
			handler = 1
			break
		}
	}
	m.setFlag(fHandler, int32(handler))
	m.OwnerType = x.str.intern(clipStr(sc.typeName, 120))
	m.NAnnotations = int32(len(annos))
	m.NGenericParams = x.countTypeParams(node)
	m.setFlag(fHTTPExchange, int32(httpClient))
	m.NEe12Annos = x.qualifiedEE12Annos(node)
}

func (x *xctx) typeExtra(node tsNode, name, kind string, body tsNode,
	sid int32) {
	line := int32(node.startRow()) + 1
	pairs := x.supertypePairs(node)
	for _, pr := range pairs {
		x.out.typeRel = append(x.out.typeRel, TypeRel{ChildID: sid,
			FileID: x.rec.ID, ChildName: x.str.intern(clipStr(name, 120)),
			ChildKind: x.str.intern(kind), ParentNam: x.str.intern(clipStr(pr[0], 120)),
			Kind:      x.str.intern(pr[1]),
			IsGeneric: boolI32(strings.Contains(pr[0], "<")), Line: line})
	}
	td := typeDelta{name: x.str.intern(name)}
	for _, p := range pairs {
		td.parents = append(td.parents, x.str.intern(p[0]))
	}

	if tp := node.childByFieldName(fTypeParams); tp.ok() {
		for ti := 0; ti < tp.namedChildCount(); ti++ {
			t := tp.namedChild(ti)
			if x.jk.names[t.kindID()] != "type_parameter" {
				continue
			}
			bound := ""
			for c := range eachNamedKid(t) {
				if x.jk.names[c.kindID()] == "type_bound" {
					bound = strings.TrimSpace(x.txt(c))
				}
			}
			td.typeGens = append(td.typeGens, genRec{name: x.name(t),
				bound: bound, owner: name,
				line: int32(t.startRow()) + 1})
		}
	}
	if !body.ok() {
		x.out.ops = append(x.out.ops, linkOp{isType: true, delta: td, sym: sid})
		return
	}

	comps := node.childByFieldName(fParameters)
	ordinal := int32(0)
	if comps.ok() {
		for ci := 0; ci < comps.namedChildCount(); ci++ {
			c := comps.namedChild(ci)
			if x.jk.names[c.kindID()] != "formal_parameter" {
				continue
			}
			tn := c.childByFieldName(fType)
			nm := c.childByFieldName(fName)
			ftype, fname := "", ""
			if tn.ok() {
				ftype = strings.TrimSpace(x.txt(tn))
			}
			if nm.ok() {
				fname = strings.TrimSpace(x.txt(nm))
			}
			x.out.fields = append(x.out.fields, Field{SymID: sid,
				Ordinal: ordinal, Name: x.str.intern(clipStr(fname, 120)),
				Type: x.str.intern(clipStr(ftype, 200)),
				Vis:  x.str.intern("private"), Line: int32(c.startRow()) + 1,
				IsConst: 1, IsColl: boolI32(isCollectionType(ftype)),
				TypeDepth: int32(strings.Count(ftype, "<") +
					strings.Count(ftype, "["))})
			ordinal++
		}
	}
	for bi := 0; bi < body.namedChildCount(); bi++ {
		fl := body.namedChild(bi)
		if x.jk.names[fl.kindID()] != "field_declaration" {
			continue
		}
		mods := x.modifiers(fl)
		tn := fl.childByFieldName(fType)
		ftype := ""
		if tn.ok() {
			ftype = strings.TrimSpace(x.txt(tn))
		}
		isStatic := boolI32(hasWordBounds(mods, "static"))
		isFinal := boolI32(hasWordBounds(mods, "final"))
		isVol := boolI32(hasWordBounds(mods, "volatile"))
		vis := "package"
		switch {
		case strings.Contains(mods, "public"):
			vis = "public"
		case strings.Contains(mods, "protected"):
			vis = "protected"
		case strings.Contains(mods, "private"):
			vis = "private"
		}
		for di := 0; di < fl.namedChildCount(); di++ {
			d := fl.namedChild(di)
			if x.jk.names[d.kindID()] != "variable_declarator" {
				continue
			}
			nm := d.childByFieldName(fName)
			fname := ""
			if nm.ok() {
				fname = strings.TrimSpace(x.txt(nm))
			}
			if isVol == 1 {
				td.vol = append(td.vol, fname)
			}
			if isStatic == 1 && isFinal == 0 {
				td.stat = append(td.stat, fname)
			}
			if strings.Contains(ftype, "ThreadLocal") {
				td.tl = append(td.tl, fname)
			}
			for _, k := range formatFieldTypes {
				if strings.Contains(ftype, k) {
					td.df = append(td.df, fname)
					break
				}
			}
			if isStatic == 1 && isFinal == 0 && isCollectionType(ftype) {
				td.scl = append(td.scl, fname)
			}
			x.out.fields = append(x.out.fields, Field{SymID: sid,
				Ordinal: ordinal, Name: x.str.intern(clipStr(fname, 120)),
				Type: x.str.intern(clipStr(ftype, 200)),
				Vis:  x.str.intern(vis), Line: int32(fl.startRow()) + 1,
				IsStatic: isStatic, IsConst: isFinal, IsMutable: 1 - isFinal,
				IsNullable: boolI32(isNullableType(ftype)),
				IsColl:     boolI32(isCollectionType(ftype)),
				HasDefault: boolI32(d.childByFieldName(fValue).ok()),
				TypeDepth: int32(strings.Count(ftype, "<") +
					strings.Count(ftype, "["))})
			ordinal++
		}
	}
	x.out.ops = append(x.out.ops, linkOp{isType: true, delta: td, sym: sid})
}

func (x *xctx) emitModuleScope(root tsNode, text string) {
	x.curBody = root
	st := x.measure(root, true)
	x.curBody = tsNode{}
	if len(st.calls) == 0 && st.nTokens < 8 {
		return
	}
	m := &st.s
	m.Cyclomatic = st.cyclomatic
	m.Cognitive = st.cognitive
	m.MaxNesting = st.maxNesting
	m.MaxLoopDepth = st.maxLoopDepth
	m.NTokens = st.nTokens
	m.NOperators = st.nOperators
	m.NOperands = st.nOperands
	m.NDistinctOps = st.nDistOps
	m.NDistinctOperand = st.nDistOperand
	m.setFlag(fTest, boolI32(x.rec.IsTest == 1))
	sid := x.insertSymbol("<module>", "module", x.rel, -1, root,
		"top-level statements of "+x.rel, "", "", m)
	for _, c := range st.calls {
		if c.name == "" {
			continue
		}
		x.out.pending = append(x.out.pending, pending{sid,
			x.str.intern(clipStr(c.name, 200)), c.line, ""})
	}
	x.emitHazards(st, sid)
	x.emitInputSites(st, sid)
	for _, l := range st.lits {
		x.out.lits = append(x.out.lits, Literal{SymID: sid, FileID: x.rec.ID,
			Kind:  x.str.intern(l.kind),
			Value: x.str.intern(clipStr(l.value, 200)),
			Line:  l.line, IsMagic: l.magic})
	}
}

func (x *xctx) scanMarkers() {
	it := newPyLines(x.text)
	for i := 0; ; i++ {
		line, ok := it.next()
		if !ok {
			break
		}

		if !(strings.Contains(line, "//") || strings.Contains(line, "#") ||
			strings.Contains(line, "*") || strings.Contains(line, "--")) {
			continue
		}
		word, _ := findMarker(line)
		if word == "" {
			continue
		}
		x.out.markers = append(x.out.markers, Marker{FileID: x.rec.ID,
			SymID: -1, Kind: x.str.intern(word), Line: int32(i + 1),
			Text: x.str.intern(clipStr(strings.TrimSpace(line), 200))})
	}
}

const (
	targetJava = "Java 25 (LTS)"
	schemaVer  = 2

	parserBanner = "parser: tree-sitter CLI (official binary, CST over stdin) + tree-sitter-java>=0.23 0.23.5"
	grammarNote  = "tree-sitter-java 0.23.5 (ABI 14, released 2024-12-21) predates " +
		"Java 25 module import declarations (JEP 511); `import module X;` parses as " +
		"an ERROR node and adds 1 to files.n_parse_errors per file that uses one"

	grammarABI = "14 (tree-sitter-java 0.23.5)"
)

type options struct {
	root             string
	which            []int
	module           string
	limit            int
	list             bool
	metrics          bool
	schema           bool
	report           bool
	sql              string
	csv              int
	json             int
	csvSet           bool
	jsonSet          bool
	save             string
	saveAST          string
	loadAST          string
	force            bool
	deps             bool
	includeGenerated bool
	includeVendored  bool
	noTests          bool
	quiet            bool
	version          bool
	help             bool
	dump             string
	threads          int

	cpuProfile       string
	memProfile       string
	blockProfile     string
	mutexProfile     string
	traceProfile     string
	goroutineProfile string
}

const gcPercent = 30

func cgPutU32(b []byte, o int, v uint32) { *(*uint32)(unsafe.Pointer(&b[o])) = v }
func cgPutU64(b []byte, o int, v uint64) { *(*uint64)(unsafe.Pointer(&b[o])) = v }

func cgGetU32(b []byte, o int) uint32 { return *(*uint32)(unsafe.Pointer(&b[o])) }
func cgGetU64(b []byte, o int) uint64 { return *(*uint64)(unsafe.Pointer(&b[o])) }

func main() {
	if os.Getenv("GOGC") == "" {
		debug.SetGCPercent(gcPercent)
	}
	os.Exit(run(os.Args[1:]))
}

func usage(w *bufio.Writer) {
	fmt.Fprintln(w, "usage: codegraph_java ROOT [N...] [--module P] [--limit N]")
	fmt.Fprintln(w, "       [--list] [--metrics] [--schema] [--report]")
	fmt.Fprintln(w, "       [--csv N] [--json N] [--save PATH] [--dump PATH] [--force]")
	fmt.Fprintln(w, "       [--save-ast PATH] [--load-ast PATH]")
	fmt.Fprintln(w, "       [--deps] [--include-generated] [--include-vendored]")
	fmt.Fprintln(w, "       [--no-tests] [--quiet] [--version] [--threads N]")
}

func parseArgs(argv []string) (*options, error) {
	o := &options{root: ".", module: "%", limit: -1, threads: 0}
	seenPositional := false
	csvSet, jsonSet := false, false
	for i := 0; i < len(argv); i++ {
		a := argv[i]
		need := func() (string, error) {
			if i+1 >= len(argv) {
				return "", fmt.Errorf("flag %s needs a value", a)
			}
			i++
			return argv[i], nil
		}
		switch {
		case a == "-h" || a == "--help":

			o.help = true
			return o, nil
		case a == "--list":
			o.list = true
		case a == "--metrics":
			o.metrics = true
		case a == "--schema":
			o.schema = true
		case a == "--report":
			o.report = true
		case a == "--quiet":
			o.quiet = true
		case a == "--force":
			o.force = true
		case a == "--deps":
			o.deps = true
		case a == "--version":
			o.version = true
		case a == "--include-generated":
			o.includeGenerated = true
		case a == "--include-vendored":
			o.includeVendored = true
		case a == "--no-tests":
			o.noTests = true
		case a == "--module":
			v, err := need()
			if err != nil {
				return nil, err
			}
			o.module = v
		case a == "--limit":
			v, err := need()
			if err != nil {
				return nil, err
			}
			n, err := strconv.Atoi(v)
			if err != nil {
				return nil, fmt.Errorf("--limit wants a number")
			}
			o.limit = n
		case a == "--threads":
			v, err := need()
			if err != nil {
				return nil, err
			}
			n, err := strconv.Atoi(v)
			if err != nil {
				return nil, fmt.Errorf("--threads wants a number")
			}
			o.threads = n
		case a == "--cpuprofile" || a == "--cpu-profile":
			v, err := need()
			if err != nil {
				return nil, err
			}
			o.cpuProfile = v
		case a == "--memprofile" || a == "--mem-profile":
			v, err := need()
			if err != nil {
				return nil, err
			}
			o.memProfile = v
		case a == "--blockprofile" || a == "--block-profile":
			v, err := need()
			if err != nil {
				return nil, err
			}
			o.blockProfile = v
		case a == "--mutexprofile" || a == "--mutex-profile":
			v, err := need()
			if err != nil {
				return nil, err
			}
			o.mutexProfile = v
		case a == "--traceprofile" || a == "--trace-profile":
			v, err := need()
			if err != nil {
				return nil, err
			}
			o.traceProfile = v
		case a == "--goroutineprofile" || a == "--goroutine-profile":
			v, err := need()
			if err != nil {
				return nil, err
			}
			o.goroutineProfile = v
		case a == "--save":
			v, err := need()
			if err != nil {
				return nil, err
			}
			o.save = v
		case a == "--save-ast":
			v, err := need()
			if err != nil {
				return nil, err
			}
			o.saveAST = v
		case a == "--load-ast":
			v, err := need()
			if err != nil {
				return nil, err
			}
			o.loadAST = v
		case a == "--dump":
			v, err := need()
			if err != nil {
				return nil, err
			}
			o.dump = v
		case a == "--csv":
			v, err := need()
			if err != nil {
				return nil, err
			}
			n, err := strconv.Atoi(v)
			if err != nil {
				return nil, fmt.Errorf("--csv wants a number")
			}
			o.csv, csvSet = n, true
		case a == "--json":
			v, err := need()
			if err != nil {
				return nil, err
			}
			n, err := strconv.Atoi(v)
			if err != nil {
				return nil, fmt.Errorf("--json wants a number")
			}
			o.json, jsonSet = n, true
		case strings.HasPrefix(a, "--"):
			return nil, fmt.Errorf("unknown flag %s", a)
		default:

			if !seenPositional {
				seenPositional = true
				o.root = a
				continue
			}
			n, err := strconv.Atoi(a)
			if err != nil {
				return nil, fmt.Errorf("query numbers must be integers, got %s", a)
			}
			o.which = append(o.which, n)
		}
	}
	o.csvSet, o.jsonSet = csvSet, jsonSet
	return o, nil
}

func run(argv []string) int {
	o, err := parseArgs(argv)
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		usage(bufio.NewWriter(os.Stderr))
		return 2
	}
	out := bufio.NewWriterSize(os.Stdout, 1<<20)
	defer out.Flush()
	if o.help {
		out.WriteString(helpText)
		return 0
	}

	stop, err := startProfiling(o)
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		return 2
	}
	defer stop()

	if o.version {
		fmt.Fprintf(out, "codegraph_java  target=%s  schema=v%d  go=%s\n",
			targetJava, schemaVer, runtime.Version())
		return 0
	}
	if o.deps {
		fmt.Fprintln(out, "dependencies for codegraph-java:")
		fmt.Fprintln(out, "  [ok     ] `tree-sitter` CLI on PATH       0.25.10    required")
		fmt.Fprintln(out, "             (or $TREE_SITTER_BIN); one child process parses one file via")
		fmt.Fprintln(out, "             `tree-sitter parse /dev/stdin --scope source.java --cst`. Nothing is")
		fmt.Fprintln(out, "             linked in and there is no C in this build, so a missing CLI aborts at")
		fmt.Fprintln(out, "             startup -- there is no regex fallback, because an empty graph reads")
		fmt.Fprintln(out, "             exactly like a clean repository")
		fmt.Fprintln(out, "             verified against 0.25.10 (external CLI, spawned per file)")
		fmt.Fprintln(out, "  [ok     ] tree-sitter-java grammar       0.23.5     required")
		fmt.Fprintln(out, "             tree-sitter grammar for Java, registered with that CLI. Required: without it this analyzer refuses to run rather than produce an empty graph")
		fmt.Fprintln(out, "             verified against 0.23.5 (ABI 14) -- older than the other grammars here; the runtime accepts 13-15 so it loads, but it predates Java 25 module import declarations")
		return 0
	}
	if o.schema {
		out.WriteString(schemaNative())
		return 0
	}
	catalogue := queries
	if o.metrics {
		catalogue = metrics
	}
	if o.list {
		for i, q := range catalogue {
			fmt.Fprintf(out, "%2d. %-26s %s\n", i+1, q.name, q.title)
		}
		return 0
	}
	if o.csvSet || o.jsonSet {
		o.quiet = true
		idx := o.csv - 1
		if o.jsonSet {
			idx = o.json - 1
		}
		if idx < 0 || idx >= len(catalogue) {
			fmt.Fprintf(os.Stderr, "no query %d\n", idx+1)
			return 2
		}
	}
	if o.saveAST != "" && o.loadAST != "" {
		fmt.Fprintln(os.Stderr, "--save-ast and --load-ast cannot be used together")
		return 2
	}
	if o.loadAST == "" {
		st, err := os.Stat(o.root)
		if err != nil || !st.IsDir() {
			fmt.Fprintf(os.Stderr, "not a directory: %s\n", o.root)
			return 2
		}
	}

	t0 := time.Now()
	var g *Graph
	var nFiles int
	if o.loadAST != "" {
		g, err = loadAST(o.loadAST)
		if err != nil {
			fmt.Fprintf(os.Stderr, "load-ast: %v\n", err)
			return 2
		}
		nFiles = len(g.Files)
	} else {
		g, nFiles, err = buildGraph(o, out)
		if err != nil {
			fmt.Fprintln(os.Stderr, err)
			return 2
		}
	}
	took := time.Since(t0)

	if o.saveAST != "" {
		if _, serr := os.Lstat(o.saveAST); serr == nil && !o.force {
			fmt.Fprintf(os.Stderr, "refusing to overwrite %s (pass --force)\n", o.saveAST)
			return 2
		}
		ts := time.Now()
		nb, werr := saveASTFile(g, o.saveAST)
		if werr != nil {
			fmt.Fprintf(os.Stderr, "save-ast: %v\n", werr)
			return 2
		}
		if !o.quiet {
			fmt.Fprintf(os.Stderr, "ast state written to %s: %d bytes in %.1fs\n",
				o.saveAST, nb, time.Since(ts).Seconds())
		}
	}

	if o.dump != "" {
		if err := writeDump(o.dump, g); err != nil {
			fmt.Fprintf(os.Stderr, "could not write %s: %s\n", o.dump, err)
			return 2
		}
	}
	if o.save != "" {
		if err := saveGraph(o.save, g, o.force, out); err != nil {
			fmt.Fprintf(os.Stderr, "could not write %s: %s\n", o.save, err)
		}
	}

	if o.csvSet || o.jsonSet {
		idx := o.csv - 1
		if o.jsonSet {
			idx = o.json - 1
		}
		if idx < 0 || idx >= len(catalogue) {
			fmt.Fprintf(os.Stderr, "no query %d\n", idx+1)
			return 2
		}
		q := catalogue[idx]
		var cols []string
		var rows [][]any
		if q.run != nil {
			cols, rows = q.run(g, o.module, o.limit)
		}
		if o.csvSet {
			writeCSV(out, cols, rows)
		} else {
			writeJSON(out, cols, rows)
		}
		return 0
	}
	if !o.quiet {
		lim := "all"
		if o.limit >= 0 {
			lim = strconv.Itoa(o.limit)
		}
		if o.loadAST != "" {
			fmt.Fprintf(out, "codegraph-java: %d files loaded from AST in %.1fs module=%s limit=%s\n",
				nFiles, took.Seconds(), o.module, lim)
		} else {
			fmt.Fprintf(out, "codegraph-java: %d files parsed into memory in %.1fs module=%s limit=%s\n",
				nFiles, took.Seconds(), o.module, lim)
		}
	}
	if o.report {
		reportGraph(out, g)
	}
	sel := o.which
	if len(sel) == 0 {
		for i := 1; i <= len(catalogue); i++ {
			sel = append(sel, i)
		}
	}
	for _, k := range sel {
		if k < 1 || k > len(catalogue) {
			continue
		}
		q := catalogue[k-1]
		fmt.Fprintf(out, "\n%s\n", strings.Repeat("=", 78))
		fmt.Fprintf(out, "Q%d. %s -- %s\n", k, q.name, q.title)
		fmt.Fprintln(out, strings.Repeat("-", 78))
		for line := range strings.SplitSeq(q.notes, "\n") {
			fmt.Fprintf(out, " %s\n", line)
		}
		fmt.Fprintln(out)
		var cols []string
		var rows [][]any
		if q.run != nil {
			cols, rows = q.run(g, o.module, o.limit)
		}
		render(out, cols, rows)
	}
	return 0
}

func buildGraph(o *options, out *bufio.Writer) (*Graph, int, error) {
	g := NewGraph()
	if !o.quiet {
		fmt.Fprintln(out, "  "+parserBanner)
	}
	td := time.Now()
	disc := discover(o.root, discoverOpts{
		includeTests: !o.noTests, includeGenerated: o.includeGenerated,
		includeVendored: o.includeVendored}, g.Str)
	g.Files = disc.files
	g.Mod = disc.mods
	sk := disc.sk
	if !o.quiet {
		for _, m := range [][2]any{{int(sk.big),
			"too large or with a pathologically long line -- catalogued, not parsed"},
			{int(sk.special), "not regular files (fifo, socket, device) -- skipped"},
			{int(sk.escape), "symlinks pointing OUTSIDE the tree -- skipped"},
			{int(sk.denied), "unreadable (permission denied)"},
			{int(sk.walkErr), "director(ies) could not be listed"}} {
			if m[0].(int) != 0 {
				fmt.Fprintf(out, "  %v %s\n", m[0], m[1])
			}
		}
	}

	total := 0
	for i := range g.Files {
		total += int(g.Files[i].Bytes)
	}

	if n := total/400 + total/4000; n > 64 {
		g.Sym = make([]Sym, 0, n)

		g.Params = make([]Param, 0, n*3/5)
		g.Imports = make([]Import, 0, n*3/5)
		g.Attrs = make([]Attr, 0, n/2)
	}
	g.addMeta("files_skipped", sprintf(
		"big=%d special=%d escaping_symlink=%d denied=%d walk_errors=%d",
		sk.big, sk.special, sk.escape, sk.denied, sk.walkErr))

	g.Str.reserve(total/300 + 64)
	if !o.quiet {
		fmt.Fprintf(out, "  %d java files discovered in %.1fs\n",
			len(disc.parsed), time.Since(td).Seconds())
	}

	t1 := time.Now()
	if o.saveAST != "" {
		g.astTrees = make([]*tsTree, len(g.Files))
	}
	l := extractAll(g, disc, o.saveAST != "", o.quiet, out, o.threads)
	nSym := len(g.Sym)
	if !o.quiet {
		fmt.Fprintf(out, "  %d symbols parsed in %.1fs\n", nSym,
			time.Since(t1).Seconds())
	}
	if len(disc.parsed) > 0 && nSym == 0 {
		fmt.Fprintln(out, "  WARNING: every file was read and produced NO symbols.")
	}

	tIdx := time.Now()
	g.buildIndexes()
	t2 := time.Now()
	l.resolve()
	g.resolveImportTargets()
	readManifests(g, o.root)
	tMat := time.Now()
	g.materialize()
	if !o.quiet {
		fmt.Fprintf(out, "  call graph built in %.1fs\n", time.Since(t2).Seconds())
		fmt.Fprintf(out, "  aggregates materialized in %.1fs\n",
			time.Since(tMat).Seconds())
		fmt.Fprintf(out, "  indexed in %.1fs\n", time.Since(tIdx).Seconds())
	}

	rel := g.meta("java_release")
	reln, _ := strconv.Atoi(rel)
	flexCtors := 0
	resil, verAttr, httpClients, ee12 := 0, 0, 0, 0
	for i := range g.Sym {
		s := &g.Sym[i]
		if s.getFlag(fFlexCtor) == 1 {
			flexCtors++
		}
		if s.NResilienceAnnos > 0 {
			resil++
		}
		if s.NApiVersionAttr > 0 {
			verAttr++
		}
		if s.getFlag(fHTTPExchange) == 1 {
			httpClients++
		}
		if s.NEe12Annos > 0 || s.NJSpecifyAnnos > 0 {
			ee12++
		}
	}
	g.addMeta("schema_version", strconv.Itoa(schemaVer))
	g.addMeta("lang", "java")
	g.addMeta("target", targetJava)
	abs, _ := filepath.Abs(o.root)
	g.addMeta("root", abs)
	g.addMeta("parse_mode", "tree-sitter")
	g.addMeta("parser", parserBanner)
	g.addMeta("built_at", time.Now().Format("2006-01-02T15:04:05"))
	g.addMeta("files_parsed", strconv.Itoa(len(disc.parsed)))
	g.addMeta("files_failed", "0")
	g.addMeta("grammar_note", grammarNote)
	g.addMeta("grammar_abi", grammarABI)
	if rel == "" {
		rel = "not declared in pom.xml/build.gradle"
	}
	g.addMeta("java_release", rel)
	switch {
	case reln >= 21:
		g.addMeta("virtual_threads",
			"available (release >= 21)")
	case reln > 0:
		g.addMeta("virtual_threads",
			"NOT available at the declared release -- every virtual-thread row below is inapplicable")
	default:
		g.addMeta("virtual_threads", "unknown: no release declared")
	}
	switch {
	case reln >= 24:
		g.addMeta("jep491_pinning",
			"synchronized no longer pins (release >= 24); only JNI and FFM downcalls do")
	case reln > 0:
		g.addMeta("jep491_pinning",
			"synchronized STILL pins at the declared release (< 24)")
	default:
		g.addMeta("jep491_pinning",
			"unknown: no release declared, assuming 24+ per TARGET")
	}
	g.addMeta("jep513_flexible_ctors", sprintf(
		"%d constructor(s) run statements before super()/this(); the grammar recovers them but files.n_parse_errors counts one per site until tree-sitter-java ships JEP 513 support",
		flexCtors))
	g.addMeta("spring7_surface", sprintf(
		"resilience=%d api-versioned=%d http-exchange-clients=%d",
		resil, verAttr, httpClients))
	g.addMeta("jakarta_ee12", sprintf(
		"EE12 spec annotations on %d symbol(s) (Data/Query/Persistence/Security families; platform GA July 2026)",
		ee12))
	pkgs := make([]string, len(g.PkgRoots))
	for i := range g.PkgRoots {
		pkgs[i] = g.Str.get(g.PkgRoots[i])
	}
	if len(g.pkgRootSet) == 0 {
		g.addMeta("packages", "(none seen)")
	} else {
		uniq := make([]string, 0, len(g.pkgRootSet))
		for p := range g.pkgRootSet {
			uniq = append(uniq, p)
		}
		sortStrings(uniq)
		if len(uniq) > 12 {
			uniq = uniq[:12]
		}
		g.addMeta("packages", strings.Join(uniq, ", "))
	}
	_ = pkgs
	if o.memProfile != "" {
		writeHeapProfile(o.memProfile)
	}
	return g, len(disc.parsed), nil
}

func sortStrings(s []string) {
	for i := 1; i < len(s); i++ {
		for j := i; j > 0 && s[j] < s[j-1]; j-- {
			s[j], s[j-1] = s[j-1], s[j]
		}
	}
}

func startProfiling(o *options) (func(), error) {
	var closers []func()
	if o.cpuProfile != "" {
		f, err := os.Create(o.cpuProfile)
		if err != nil {
			return nil, err
		}
		if err := pprof.StartCPUProfile(f); err != nil {
			f.Close()
			return nil, err
		}
		closers = append(closers, func() { pprof.StopCPUProfile(); f.Close() })
	}
	if o.blockProfile != "" {
		runtime.SetBlockProfileRate(1)
	}
	if o.mutexProfile != "" {
		runtime.SetMutexProfileFraction(1)
	}
	if o.traceProfile != "" {
		f, err := os.Create(o.traceProfile)
		if err != nil {
			return nil, err
		}
		if err := trace.Start(f); err != nil {
			f.Close()
			return nil, err
		}
		closers = append(closers, func() { trace.Stop(); f.Close() })
	}
	if o.memProfile != "" {

		runtime.MemProfileRate = 1
	}
	return func() {
		for _, closer := range slices.Backward(closers) {
			closer()
		}
		writeRuntimeProfile(o.blockProfile, "block")
		writeRuntimeProfile(o.mutexProfile, "mutex")
		writeRuntimeProfile(o.goroutineProfile, "goroutine")
	}, nil
}

func writeRuntimeProfile(path, name string) {
	if path == "" {
		return
	}
	f, err := os.Create(path)
	if err != nil {
		return
	}
	_ = pprof.Lookup(name).WriteTo(f, 0)
	f.Close()
}

func writeHeapProfile(path string) {
	f, err := os.Create(path)
	if err != nil {
		return
	}
	runtime.GC()
	_ = pprof.Lookup("heap").WriteTo(f, 0)
	f.Close()
}

type parsedFile struct {
	src  []byte
	cst  []byte
	fidx int32
}

func extractAll(g *Graph, disc *discovered, keepTrees bool, quiet bool,
	out *bufio.Writer, threads int) *linker {
	p := newTSParser()
	x := newXctx(p, g.Str)
	x.keepTrees = keepTrees
	l := newLinker(g)
	fo := new(fileOut)
	step := max(len(disc.parsed)/20, 1)
	done := 0

	consume := func(r parsedFile) {
		f := &disc.files[r.fidx]
		clear(x.kindLoc)
		x.one(fo, int(r.fidx), f, disc.str, r.cst, r.src)
		if fo.failed == 1 {
			g.Files[fo.idx].Parsed = 0
			g.Files[fo.idx].NParsErr++
		} else {
			g.Files[fo.idx].NParsErr = fo.parseErr
			g.Files[fo.idx].NMissing = fo.missing
		}
		if fo.genOverride == 1 {
			g.Files[fo.idx].IsGen = 1
		}
		l.link(fo)
		if g.astTrees != nil && fo.idx >= 0 && int(fo.idx) < len(g.astTrees) {
			g.astTrees[fo.idx] = &tsTree{recs: fo.recs}
			fo.recs = nil
		}
		done++
		if !quiet && done%step == 0 {
			fmt.Fprintf(out, "  ... %d/%d files\n", done, len(disc.parsed))
		}
	}

	n := len(disc.parsed)
	nw := threads
	if nw <= 0 {
		nw = runtime.GOMAXPROCS(0)
		if nw > 8 {
			nw = 8
		}
	}
	if nw > n {
		nw = n
	}
	// Each worker runs the exact per-file command the serial path ran, so the
	// CST bytes are identical.  Decode/link stays on this goroutine in file
	// order, so every observable ordering (interner ids, symbol ids, edges)
	// is unchanged; only the waiting for child processes overlaps.
	//
	// Worker w takes files w, w+nw, w+2nw, ...; the main goroutine reads the
	// workers' channels round-robin, which is exactly file order.  A worker
	// never waits on another worker, so this cannot deadlock, and each in-
	// flight result carries its own buffers; consumed buffers are recycled
	// opportunistically per worker (non-blocking send/receive).
	//
	// INVARIANT: a worker goroutine must not touch anything the main
	// goroutine can mutate.  The only shared structures it reaches are the
	// discovery slices (never written again) and the path strings computed
	// below before any goroutine starts.  In particular it must not call
	// Interner.get: File.Full(disc.str) reads pos/ln slice headers while the
	// main goroutine's intern/commit appends to them.
	if nw > 1 {
		paths := make([]string, n)
		for i, fidx := range disc.parsed {
			paths[i] = disc.files[fidx].Full(disc.str)
		}
		outs := make([]chan parsedFile, nw)
		rets := make([]chan []byte, nw)
		for i := range outs {
			outs[i] = make(chan parsedFile, 1)
			// Capacity 2 so the consumer can return BOTH buffers (source and
			// CST) of the file it just consumed without one being dropped.
			rets[i] = make(chan []byte, 2)
		}
		var wg sync.WaitGroup
		for w := 0; w < nw; w++ {
			wp := newTSParser()
			wg.Add(1)
			go func(w int, wp *tsParser) {
				defer wg.Done()
				for i := w; i < n; i += nw {
					fidx := disc.parsed[i]
					var cstBuf, srcBuf []byte
					select {
					case cstBuf = <-rets[w]:
					default:
					}
					select {
					case srcBuf = <-rets[w]:
					default:
					}
					src, err := readWholeFile(paths[i], srcBuf[:0])
					if err != nil {
						src = nil
					}
					cst := wp.parse(src, cstBuf[:0])
					outs[w] <- parsedFile{src: src, cst: cst, fidx: fidx}
				}
			}(w, wp)
		}
		for i := 0; i < n; i++ {
			w := i % nw
			r := <-outs[w]
			consume(r)
			if cap(r.cst) > 0 {
				select {
				case rets[w] <- r.cst[:0]:
				default:
				}
			}
			if cap(r.src) > 0 {
				select {
				case rets[w] <- r.src[:0]:
				default:
				}
			}
		}
		wg.Wait()
		return l
	}

	var cstBuf, srcBuf []byte
	for _, fidx := range disc.parsed {
		f := &disc.files[fidx]
		src, err := readWholeFile(f.Full(disc.str), srcBuf[:0])
		if err != nil {
			src = nil
		} else {
			srcBuf = src
		}
		cst := p.parse(src, cstBuf[:0])
		cstBuf = cst
		consume(parsedFile{src: src, cst: cst, fidx: fidx})
	}
	return l
}

func readWholeFile(path string, dst []byte) ([]byte, error) {
	f, err := os.Open(path)
	if err != nil {
		return nil, err
	}
	defer f.Close()
	for {
		if len(dst) == cap(dst) {
			grown := make([]byte, len(dst), 2*cap(dst)+4096)
			copy(grown, dst)
			dst = grown
		}
		n, err := f.Read(dst[len(dst):cap(dst)])
		dst = dst[:len(dst)+n]
		if err != nil {
			if err == io.EOF {
				return dst, nil
			}
			return nil, err
		}
	}
}

func saveGraph(path string, g *Graph, force bool, out *bufio.Writer) error {
	if _, err := os.Lstat(path); err == nil && !force {
		fmt.Fprintf(os.Stderr, "\nrefusing to overwrite %s (pass --force)\n", path)
		return nil
	}
	if err := writeDump(path, g); err != nil {
		return err
	}
	return nil
}

const cgasMagic = "CGAS"

const (
	cgasVersion  = 3
	cgasHeaderSz = 32
	cgasSecSz    = 24
	cgasNSec     = 34
	cgasSymRowSz = 13*4 + 177*2
)

const (
	cgasSecStrings uint32 = 1 + iota
	cgasSecTrees
	cgasSecTreeDir
	cgasSecFiles
	cgasSecMods
	cgasSecSyms
	cgasSecParams
	cgasSecFields
	cgasSecLocals
	cgasSecEnumMem
	cgasSecEdges
	cgasSecCallsites
	cgasSecUnres
	cgasSecImports
	cgasSecHazards
	cgasSecAttrs
	cgasSecLits
	cgasSecMarkers
	cgasSecTypeRel
	cgasSecOvers
	cgasSecExcepts
	cgasSecMonOps
	cgasSecGens
	cgasSecRes
	cgasSecLocks
	cgasSecJPMS
	cgasSecUISites
	cgasSecSecrets
	cgasSecReach
	cgasSecMeta
	cgasSecStrPos
	cgasSecStrLn
	cgasSecStrChunks
	cgasSecPkgRoots
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
	fail(unsafe.Sizeof("") == 16, "string must be 16 bytes")
	g := "cgas-layout-guard"
	h := *(*[2]uintptr)(unsafe.Pointer(&g))
	fail(h[1] == uintptr(len(g)) &&
		h[0] == uintptr(unsafe.Pointer(unsafe.StringData(g))), "string header word order")
	fail(unsafe.Sizeof(tsRec{}) == 32, "tsRec must be the 32-byte fixed stride")
	fail(cgasSymRowSz == 406 && 13*4+177*2 == 406, "sym packed row must stay 406 bytes")
	fail(unsafe.Sizeof(File{}) == 128, "File must be the 128-byte offset-native row")
	cw := Sym{ID: 3, FileID: 5, ModuleID: 7, ParentID: 9, Name: 11, QualName: 13,
		Kind: 15, LineStart: 17, ByteStart: 19, ByteEnd: 21, Signature: 23, RetType: 25,
		Vis: 27, flags: 29, HalsteadVolume: 31, OwnerType: 33, NStaticCollRemove: 35}
	var ce, cd cgasSymCodec
	ce.b = make([]byte, cgasSymRowSz)
	ce.enc = true
	ce.id = cw.ID
	ce.symRow(&cw)
	cx := Sym{}
	cd.b = ce.b
	cd.enc = false
	cd.symRow(&cx)
	fail(ce.err == nil && ce.o == cgasSymRowSz && cd.o == cgasSymRowSz &&
		cx.ID == 3 && cx.FileID == 5 && cx.ModuleID == 7 && cx.ParentID == 9 &&
		cx.Name == 11 && cx.QualName == 13 && cx.Kind == 15 && cx.LineStart == 17 &&
		cx.ByteStart == 19 && cx.ByteEnd == 21 && cx.Signature == 23 && cx.RetType == 25 &&
		cx.Vis == 27 && cx.flags == 29 && cx.HalsteadVolume == 31 && cx.OwnerType == 33 &&
		cx.NStaticCollRemove == 35, "sym packed-row codec round-trip")
	for _, t := range []reflect.Type{
		reflect.TypeOf(tsRec{}),
		reflect.TypeOf(File{}),
		reflect.TypeOf(Sym{}),
		reflect.TypeOf(Module{}),
		reflect.TypeOf(Param{}),
		reflect.TypeOf(Field{}),
		reflect.TypeOf(Local{}),
		reflect.TypeOf(EnumMember{}),
		reflect.TypeOf(Edge{}),
		reflect.TypeOf(Callsite{}),
		reflect.TypeOf(Unres{}),
		reflect.TypeOf(Import{}),
		reflect.TypeOf(Hazard{}),
		reflect.TypeOf(Attr{}),
		reflect.TypeOf(Literal{}),
		reflect.TypeOf(Marker{}),
		reflect.TypeOf(TypeRel{}),
		reflect.TypeOf(Override{}),
		reflect.TypeOf(Exception{}),
		reflect.TypeOf(MonitorOp{}),
		reflect.TypeOf(Generic{}),
		reflect.TypeOf(Resource{}),
		reflect.TypeOf(LockOp{}),
		reflect.TypeOf(JPMS{}),
		reflect.TypeOf(InputSite{}),
		reflect.TypeOf(Secret{}),
		reflect.TypeOf(Reach{}),
		reflect.TypeOf(MetaKV{}),
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

func cgasRows[T any](mem []byte, off, ln uint64, what string) ([]T, error) {
	if ln == 0 {
		return nil, nil
	}
	size := uint64(unsafe.Sizeof(*new(T)))
	if ln%size != 0 {
		return nil, fmt.Errorf("%s: section length %d is not a multiple of record size %d", what, ln, size)
	}
	if off < uint64(cgasHeaderSz) || off > uint64(len(mem)) || ln > uint64(len(mem))-off {
		return nil, fmt.Errorf("%s: section lies outside the file", what)
	}
	base := unsafe.Pointer(uintptr(unsafe.Pointer(&mem[0])) + uintptr(off))
	if a := uintptr(unsafe.Alignof(*new(T))); a > 1 && uintptr(base)%a != 0 {
		return nil, fmt.Errorf("%s: section is not %d-byte aligned", what, a)
	}
	return unsafe.Slice((*T)(base), int(ln/size)), nil
}

type cgasOut struct {
	w   *bufio.Writer
	pos uint64
}

func (o *cgasOut) put(b []byte) error {
	o.pos += uint64(len(b))
	_, err := o.w.Write(b)
	return err
}

func cgasPutRows[T any](o *cgasOut, rows []T) error {
	if len(rows) == 0 {
		return nil
	}
	return o.put(unsafe.Slice((*byte)(unsafe.Pointer(&rows[0])), len(rows)*int(unsafe.Sizeof(rows[0]))))
}

type cgasSymCodec struct {
	b   []byte
	o   int
	enc bool
	id  int32
	err error
}

func (c *cgasSymCodec) w32(v *int32) {
	if c.err != nil {
		return
	}
	if c.enc {
		*(*uint32)(unsafe.Pointer(&c.b[c.o])) = uint32(*v)
	} else {
		*v = int32(*(*uint32)(unsafe.Pointer(&c.b[c.o])))
	}
	c.o += 4
}

func (c *cgasSymCodec) w32u(v *uint32) {
	if c.err != nil {
		return
	}
	if c.enc {
		*(*uint32)(unsafe.Pointer(&c.b[c.o])) = *v
	} else {
		*v = *(*uint32)(unsafe.Pointer(&c.b[c.o]))
	}
	c.o += 4
}

func (c *cgasSymCodec) w16u(v *uint32, name string) {
	if c.err != nil {
		return
	}
	if c.enc {
		if *v > 65535 {
			c.err = fmt.Errorf("symbol %d: %s = %d exceeds uint16 storage", c.id, name, *v)
			return
		}
		*(*uint16)(unsafe.Pointer(&c.b[c.o])) = uint16(*v)
	} else {
		*v = uint32(*(*uint16)(unsafe.Pointer(&c.b[c.o])))
	}
	c.o += 2
}

func (c *cgasSymCodec) w16(v *int32, name string) {
	if c.err != nil {
		return
	}
	if c.enc {
		if *v < 0 || *v > 65535 {
			c.err = fmt.Errorf("symbol %d: %s = %d exceeds uint16 storage", c.id, name, *v)
			return
		}
		*(*uint16)(unsafe.Pointer(&c.b[c.o])) = uint16(*v)
	} else {
		*v = int32(*(*uint16)(unsafe.Pointer(&c.b[c.o])))
	}
	c.o += 2
}

func (c *cgasSymCodec) symRow(s *Sym) {
	c.w32(&s.ID)
	c.w32(&s.FileID)
	c.w16(&s.ModuleID, "ModuleID")
	c.w32(&s.ParentID)
	c.w32u(&s.Name)
	c.w32u(&s.QualName)
	c.w16u(&s.Kind, "Kind")
	c.w16(&s.LineStart, "LineStart")
	c.w16(&s.LineEnd, "LineEnd")
	c.w16(&s.NLines, "NLines")
	c.w32(&s.ByteStart)
	c.w32(&s.ByteEnd)
	c.w32u(&s.Signature)
	c.w32u(&s.RetType)
	c.w32u(&s.Vis)
	c.w16(&s.NParams, "NParams")
	c.w16(&s.NOptionalParams, "NOptionalParams")
	c.w16(&s.NGenericParams, "NGenericParams")
	c.w16(&s.NOverloads, "NOverloads")
	c.w16(&s.ArityRank, "ArityRank")
	c.w32u(&s.flags)
	c.w16(&s.Sloc, "Sloc")
	c.w16(&s.BodyBytes, "BodyBytes")
	c.w16(&s.NCommentLn, "NCommentLn")
	c.w16(&s.NDocLines, "NDocLines")
	c.w16(&s.HasDoc, "HasDoc")
	c.w16(&s.Cyclomatic, "Cyclomatic")
	c.w16(&s.Cognitive, "Cognitive")
	c.w16(&s.MaxNesting, "MaxNesting")
	c.w16(&s.NTokens, "NTokens")
	c.w16(&s.NOperators, "NOperators")
	c.w16(&s.NOperands, "NOperands")
	c.w16(&s.NDistinctOps, "NDistinctOps")
	c.w16(&s.NDistinctOperand, "NDistinctOperand")
	c.w32(&s.HalsteadVolume)
	c.w16(&s.Maintainability, "Maintainability")
	c.w16(&s.NLoops, "NLoops")
	c.w16(&s.NBranches, "NBranches")
	c.w16(&s.NReturns, "NReturns")
	c.w16(&s.NEarlyReturns, "NEarlyReturns")
	c.w16(&s.NSwitch, "NSwitch")
	c.w16(&s.NCases, "NCases")
	c.w16(&s.NTernary, "NTernary")
	c.w16(&s.NLogical, "NLogical")
	c.w16(&s.NTry, "NTry")
	c.w16(&s.NCatch, "NCatch")
	c.w16(&s.NCatchBroad, "NCatchBroad")
	c.w16(&s.NCatchEmpty, "NCatchEmpty")
	c.w16(&s.NFinally, "NFinally")
	c.w16(&s.NThrow, "NThrow")
	c.w16(&s.NLabels, "NLabels")
	c.w16(&s.NGotos, "NGotos")
	c.w16(&s.MaxLoopDepth, "MaxLoopDepth")
	c.w16(&s.CallInLoop, "CallInLoop")
	c.w16(&s.AllocInLoop, "AllocInLoop")
	c.w16(&s.IOInLoop, "IOInLoop")
	c.w16(&s.LockInLoop, "LockInLoop")
	c.w16(&s.ConcatInLoop, "ConcatInLoop")
	c.w16(&s.RegexInLoop, "RegexInLoop")
	c.w16(&s.QueryInLoop, "QueryInLoop")
	c.w16(&s.BranchInLoop, "BranchInLoop")
	c.w16(&s.NLocals, "NLocals")
	c.w16(&s.NAssign, "NAssign")
	c.w16(&s.NCompoundAssgn, "NCompoundAssgn")
	c.w16(&s.NIncDec, "NIncDec")
	c.w16(&s.NCmp, "NCmp")
	c.w16(&s.NBitop, "NBitop")
	c.w16(&s.NShift, "NShift")
	c.w16(&s.NArith, "NArith")
	c.w16(&s.NStringLit, "NStringLit")
	c.w16(&s.NRegexLit, "NRegexLit")
	c.w16(&s.NFloatLit, "NFloatLit")
	c.w16(&s.NMagic, "NMagic")
	c.w16(&s.NNullCheck, "NNullCheck")
	c.w16(&s.NSubscript, "NSubscript")
	c.w16(&s.NMemberAccess, "NMemberAccess")
	c.w16(&s.NLambda, "NLambda")
	c.w16(&s.NCalls, "NCalls")
	c.w16(&s.NUniqueCalls, "NUniqueCalls")
	c.w16(&s.NUnresolved, "NUnresolved")
	c.w16(&s.FanIn, "FanIn")
	c.w16(&s.FanOut, "FanOut")
	c.w16(&s.NCallsites, "NCallsites")
	c.w16(&s.NHazards, "NHazards")
	c.w16(&s.RiskScore, "RiskScore")
	c.w16(&s.NReflection, "NReflection")
	c.w16(&s.NSerialization, "NSerialization")
	c.w16(&s.NJNI, "NJNI")
	c.w16(&s.NExec, "NExec")
	c.w16(&s.NIO, "NIO")
	c.w16(&s.NNet, "NNet")
	c.w16(&s.NSql, "NSql")
	c.w16(&s.NCrypto, "NCrypto")
	c.w16(&s.NConcurrency, "NConcurrency")
	c.w16(&s.NLock, "NLock")
	c.w16(&s.NAlloc, "NAlloc")
	c.w16(&s.NBoxing, "NBoxing")
	c.w16(&s.NString, "NString")
	c.w16(&s.NResource, "NResource")
	c.w16(&s.NUnsafe, "NUnsafe")
	c.w16(&s.NControl, "NControl")
	c.w16(&s.NTextBlocks, "NTextBlocks")
	c.w16(&s.NLambdas, "NLambdas")
	c.w16(&s.NMethodRefs, "NMethodRefs")
	c.w16(&s.NStreams, "NStreams")
	c.w16(&s.NParallelStreams, "NParallelStreams")
	c.w16(&s.NCollectors, "NCollectors")
	c.w16(&s.NBoxingSites, "NBoxingSites")
	c.w16(&s.NBoxingInLoop, "NBoxingInLoop")
	c.w16(&s.NStringConcat, "NStringConcat")
	c.w16(&s.NSyncBlocks, "NSyncBlocks")
	c.w16(&s.NSyncMethods, "NSyncMethods")
	c.w16(&s.NLockAcquire, "NLockAcquire")
	c.w16(&s.NLockRelease, "NLockRelease")
	c.w16(&s.NWaitCalls, "NWaitCalls")
	c.w16(&s.NVolatileAccess, "NVolatileAccess")
	c.w16(&s.NAtomicOps, "NAtomicOps")
	c.w16(&s.NThreadlocalOps, "NThreadlocalOps")
	c.w16(&s.NThreadlocalRem, "NThreadlocalRem")
	c.w16(&s.NTryResources, "NTryResources")
	c.w16(&s.NCloseCalls, "NCloseCalls")
	c.w16(&s.NResourceOpen, "NResourceOpen")
	c.w16(&s.NFinalizers, "NFinalizers")
	c.w16(&s.NThrowsDeclared, "NThrowsDeclared")
	c.w16(&s.NThrowSites, "NThrowSites")
	c.w16(&s.NCatchRethrow, "NCatchRethrow")
	c.w16(&s.NSetAccessible, "NSetAccessible")
	c.w16(&s.NNativeCalls, "NNativeCalls")
	c.w16(&s.NFFMArena, "NFFMArena")
	c.w16(&s.NFFMDowncall, "NFFMDowncall")
	c.w16(&s.NUnsafeCalls, "NUnsafeCalls")
	c.w16(&s.NWildcardTypes, "NWildcardTypes")
	c.w16(&s.NRawTypes, "NRawTypes")
	c.w16(&s.NUncheckedCasts, "NUncheckedCasts")
	c.w16(&s.NInstanceof, "NInstanceof")
	c.w16(&s.NNullReturns, "NNullReturns")
	c.w16(&s.NOptionalOps, "NOptionalOps")
	c.w16(&s.NAnnotations, "NAnnotations")
	c.w16(&s.NSuppressions, "NSuppressions")
	c.w16(&s.NStaticWrites, "NStaticWrites")
	c.w16(&s.NQueryCalls, "NQueryCalls")
	c.w16(&s.NRegexCompile, "NRegexCompile")
	c.w16(&s.NDatefmtOps, "NDatefmtOps")
	c.w16(&s.NEscapingAllocs, "NEscapingAllocs")
	c.w16(&s.NAllocSites, "NAllocSites")
	c.w16(&s.NImplTargets, "NImplTargets")
	c.w32u(&s.OwnerType)
	c.w16(&s.NRuntimeExec, "NRuntimeExec")
	c.w16(&s.NPrintStacktrace, "NPrintStacktrace")
	c.w16(&s.NDefaultCharset, "NDefaultCharset")
	c.w16(&s.NParseNoRadix, "NParseNoRadix")
	c.w16(&s.NEqualsInLoop, "NEqualsInLoop")
	c.w16(&s.NWeakRandom, "NWeakRandom")
	c.w16(&s.NRedirect, "NRedirect")
	c.w16(&s.NAuthCall, "NAuthCall")
	c.w16(&s.NXXEParser, "NXXEParser")
	c.w16(&s.NZipRead, "NZipRead")
	c.w16(&s.NTimeoutSet, "NTimeoutSet")
	c.w16(&s.NExecutorCreate, "NExecutorCreate")
	c.w16(&s.NSubmitInLoop, "NSubmitInLoop")
	c.w16(&s.NFutureGet, "NFutureGet")
	c.w16(&s.NMonitorCall, "NMonitorCall")
	c.w16(&s.NStringIntern, "NStringIntern")
	c.w16(&s.NRawStatement, "NRawStatement")
	c.w16(&s.NReadObject, "NReadObject")
	c.w16(&s.NLoadLibrary, "NLoadLibrary")
	c.w16(&s.NElif, "NElif")
	c.w16(&s.NExternalCalls, "NExternalCalls")
	c.w16(&s.NRefEq, "NRefEq")
	c.w16(&s.NNarrowCalc, "NNarrowCalc")
	c.w16(&s.NDeadException, "NDeadException")
	c.w16(&s.NSuperCalls, "NSuperCalls")
	c.w16(&s.NStaticWriteCtor, "NStaticWriteCtor")
	c.w16(&s.NModernIdioms, "NModernIdioms")
	c.w16(&s.NResilienceAnnos, "NResilienceAnnos")
	c.w16(&s.NApiVersionAttr, "NApiVersionAttr")
	c.w16(&s.NEe12Annos, "NEe12Annos")
	c.w16(&s.NJSpecifyAnnos, "NJSpecifyAnnos")
	c.w16(&s.NNotifySingle, "NNotifySingle")
	c.w16(&s.NRunCalledDirectly, "NRunCalledDirectly")
	c.w16(&s.NBigDecimalFromDouble, "NBigDecimalFromDouble")
	c.w16(&s.NVolatileCompound, "NVolatileCompound")
	c.w16(&s.NSharedDatefmtUse, "NSharedDatefmtUse")
	c.w16(&s.NListenerAdd, "NListenerAdd")
	c.w16(&s.NListenerRemove, "NListenerRemove")
	c.w16(&s.NThreadAlloc, "NThreadAlloc")
	c.w16(&s.NSpelEval, "NSpelEval")
	c.w16(&s.NFormatInLoop, "NFormatInLoop")
	c.w16(&s.NStaticCollAdd, "NStaticCollAdd")
	c.w16(&s.NStaticCollRemove, "NStaticCollRemove")
}

func cgasUnpackSyms(mem []byte, off, ln uint64) ([]Sym, error) {
	if ln == 0 {
		return nil, nil
	}
	if ln%cgasSymRowSz != 0 {
		return nil, fmt.Errorf("symbols: section length %d is not a multiple of record size %d", ln, cgasSymRowSz)
	}
	if off < uint64(cgasHeaderSz) || off > uint64(len(mem)) || ln > uint64(len(mem))-off {
		return nil, fmt.Errorf("symbols: section lies outside the file")
	}
	rows := mem[off : off+ln]
	out := make([]Sym, ln/cgasSymRowSz)
	var c cgasSymCodec
	for i := range out {
		c.b = rows[i*cgasSymRowSz:]
		c.o = 0
		c.enc = false
		c.err = nil
		c.symRow(&out[i])
	}
	return out, nil
}

func saveASTFile(g *Graph, path string) (int64, error) {
	cgasGuard()
	it := g.Str
	chunkLens := make([]uint32, len(it.chunks))
	high := make([]int32, len(it.chunks))
	for i := range it.pos {
		c := it.pos[i] >> offBits
		if int(c) >= len(high) {
			return 0, fmt.Errorf("interner string %d names chunk %d of %d", i, c, len(high))
		}
		e := int32(it.pos[i]&offMask) + int32(it.ln[i])
		if e > high[c] {
			high[c] = e
		}
		if int(e) > len(it.chunks[c]) {
			return 0, fmt.Errorf("interner string %d spans %d bytes past its chunk", i, e)
		}
	}
	arenaLen := uint64(0)
	for i := range it.chunks {
		chunkLens[i] = uint32(high[i])
		arenaLen += uint64(high[i])
	}
	builtAtV := ^uint32(0)
	builtAtK := ^uint32(0)
	for _, m := range g.Meta {
		if g.Str.get(m.K) == "built_at" {
			builtAtK, builtAtV = m.K, m.V
			break
		}
	}
	builtAtC, builtAtO, builtAtE := int32(-1), int32(0), int32(0)
	if int(builtAtV) < len(it.pos) {
		c := int32(it.pos[builtAtV] >> offBits)
		o := it.pos[builtAtV] & offMask
		e := int32(o + it.ln[builtAtV])
		if int(c) < len(high) && e <= high[c] {
			builtAtC, builtAtO, builtAtE = c, int32(o), e
		}
	}
	metaSkip := -1
	for i := range g.Meta {
		if g.Meta[i].K == builtAtK {
			metaSkip = i
			break
		}
	}
	if len(g.Sym) > 0 {
		row := make([]byte, cgasSymRowSz)
		var c cgasSymCodec
		for i := range g.Sym {
			c.b = row
			c.o = 0
			c.enc = true
			c.id = g.Sym[i].ID
			c.err = nil
			c.symRow(&g.Sym[i])
			if c.err != nil {
				return 0, fmt.Errorf("save symbols: %w", c.err)
			}
		}
	}
	nMeta := len(g.Meta)
	if metaSkip >= 0 {
		nMeta--
	}
	tDir := make([]byte, 12+4*len(g.astTrees))
	cgPutU64(tDir[0:8], 0, uint64(unsafe.Sizeof(tsRec{})))
	cgPutU32(tDir[8:12], 0, uint32(len(g.astTrees)))
	totalRecs := uint64(0)
	for i := range g.astTrees {
		n := uint32(0)
		if tr := g.astTrees[i]; tr != nil {
			n = uint32(len(tr.recs))
			totalRecs += uint64(n)
		}
		cgPutU32(tDir[12+4*i:], 0, n)
	}
	secLen := func(id uint32) uint64 {
		switch id {
		case cgasSecStrChunks:
			return uint64(len(chunkLens)) * 4
		case cgasSecStrPos:
			return uint64(len(it.pos)) * 4
		case cgasSecStrLn:
			return uint64(len(it.ln)) * 4
		case cgasSecFiles:
			return uint64(len(g.Files)) * uint64(unsafe.Sizeof(File{}))
		case cgasSecMods:
			return uint64(len(g.Mod)) * uint64(unsafe.Sizeof(Module{}))
		case cgasSecSyms:
			return uint64(len(g.Sym)) * cgasSymRowSz
		case cgasSecParams:
			return uint64(len(g.Params)) * uint64(unsafe.Sizeof(Param{}))
		case cgasSecFields:
			return uint64(len(g.Fields)) * uint64(unsafe.Sizeof(Field{}))
		case cgasSecLocals:
			return uint64(len(g.Locals)) * uint64(unsafe.Sizeof(Local{}))
		case cgasSecEnumMem:
			return uint64(len(g.EnumMem)) * uint64(unsafe.Sizeof(EnumMember{}))
		case cgasSecEdges:
			return uint64(len(g.Edges)) * uint64(unsafe.Sizeof(Edge{}))
		case cgasSecCallsites:
			return uint64(len(g.Callsite)) * uint64(unsafe.Sizeof(Callsite{}))
		case cgasSecUnres:
			return uint64(len(g.Unres)) * uint64(unsafe.Sizeof(Unres{}))
		case cgasSecImports:
			return uint64(len(g.Imports)) * uint64(unsafe.Sizeof(Import{}))
		case cgasSecHazards:
			return uint64(len(g.Hazards)) * uint64(unsafe.Sizeof(Hazard{}))
		case cgasSecAttrs:
			return uint64(len(g.Attrs)) * uint64(unsafe.Sizeof(Attr{}))
		case cgasSecLits:
			return uint64(len(g.Lits)) * uint64(unsafe.Sizeof(Literal{}))
		case cgasSecMarkers:
			return uint64(len(g.Markers)) * uint64(unsafe.Sizeof(Marker{}))
		case cgasSecTypeRel:
			return uint64(len(g.TypeRel)) * uint64(unsafe.Sizeof(TypeRel{}))
		case cgasSecOvers:
			return uint64(len(g.Over)) * uint64(unsafe.Sizeof(Override{}))
		case cgasSecExcepts:
			return uint64(len(g.Excepts)) * uint64(unsafe.Sizeof(Exception{}))
		case cgasSecMonOps:
			return uint64(len(g.MonOps)) * uint64(unsafe.Sizeof(MonitorOp{}))
		case cgasSecGens:
			return uint64(len(g.Gens)) * uint64(unsafe.Sizeof(Generic{}))
		case cgasSecRes:
			return uint64(len(g.Res)) * uint64(unsafe.Sizeof(Resource{}))
		case cgasSecLocks:
			return uint64(len(g.Locks)) * uint64(unsafe.Sizeof(LockOp{}))
		case cgasSecJPMS:
			return uint64(len(g.JPMS)) * uint64(unsafe.Sizeof(JPMS{}))
		case cgasSecUISites:
			return uint64(len(g.UISites)) * uint64(unsafe.Sizeof(InputSite{}))
		case cgasSecSecrets:
			return uint64(len(g.Secrets)) * uint64(unsafe.Sizeof(Secret{}))
		case cgasSecReach:
			return uint64(len(g.Reach)) * uint64(unsafe.Sizeof(Reach{}))
		case cgasSecMeta:
			return uint64(nMeta) * uint64(unsafe.Sizeof(MetaKV{}))
		case cgasSecPkgRoots:
			return uint64(len(g.PkgRoots)) * 4
		case cgasSecTreeDir:
			return uint64(len(tDir))
		case cgasSecTrees:
			return totalRecs * uint64(unsafe.Sizeof(tsRec{}))
		case cgasSecStrings:
			return arenaLen
		}
		return 0
	}
	dir := make([]cgasSec, cgasNSec)
	cur := uint64(cgasHeaderSz) + cgasNSec*cgasSecSz
	for i := range dir {
		cur = (cur + 7) &^ 7
		dir[i] = cgasSec{uint32(i + 1), 0, cur, secLen(uint32(i + 1))}
		cur += dir[i].Len
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
	out := &cgasOut{w: bufio.NewWriterSize(f, 1<<20)}
	hdr := make([]byte, cgasHeaderSz)
	copy(hdr[0:4], cgasMagic)
	cgPutU32(hdr[4:8], 0, cgasVersion)
	cgPutU32(hdr[8:12], 0, cgasNSec)
	cgPutU64(hdr[16:24], 0, total)
	cgPutU64(hdr[24:32], 0, arenaLen)
	dirBuf := make([]byte, cgasNSec*cgasSecSz)
	for i := range dir {
		o := i * int(cgasSecSz)
		cgPutU32(dirBuf[o:], 0, dir[i].ID)
		cgPutU64(dirBuf[o+8:], 0, dir[i].Off)
		cgPutU64(dirBuf[o+16:], 0, dir[i].Len)
	}
	werr := func() error {
		if err := out.put(hdr); err != nil {
			return err
		}
		if err := out.put(dirBuf); err != nil {
			return err
		}
		var pad [8]byte
		for i := range dir {
			if dir[i].Off > out.pos {
				if err := out.put(pad[:dir[i].Off-out.pos]); err != nil {
					return err
				}
			}
			var serr error
			switch dir[i].ID {
			case cgasSecStrChunks:
				serr = cgasPutRows(out, chunkLens)
			case cgasSecStrPos:
				serr = cgasPutRows(out, it.pos)
			case cgasSecStrLn:
				serr = cgasPutRows(out, it.ln)
			case cgasSecFiles:
				serr = cgasPutRows(out, g.Files)
			case cgasSecMods:
				serr = cgasPutRows(out, g.Mod)
			case cgasSecSyms:
				serr = cgasPutSyms(out, g.Sym)
			case cgasSecParams:
				serr = cgasPutRows(out, g.Params)
			case cgasSecFields:
				serr = cgasPutRows(out, g.Fields)
			case cgasSecLocals:
				serr = cgasPutRows(out, g.Locals)
			case cgasSecEnumMem:
				serr = cgasPutRows(out, g.EnumMem)
			case cgasSecEdges:
				serr = cgasPutRows(out, g.Edges)
			case cgasSecCallsites:
				serr = cgasPutRows(out, g.Callsite)
			case cgasSecUnres:
				serr = cgasPutRows(out, g.Unres)
			case cgasSecImports:
				serr = cgasPutRows(out, g.Imports)
			case cgasSecHazards:
				serr = cgasPutRows(out, g.Hazards)
			case cgasSecAttrs:
				serr = cgasPutRows(out, g.Attrs)
			case cgasSecLits:
				serr = cgasPutRows(out, g.Lits)
			case cgasSecMarkers:
				serr = cgasPutRows(out, g.Markers)
			case cgasSecTypeRel:
				serr = cgasPutRows(out, g.TypeRel)
			case cgasSecOvers:
				serr = cgasPutRows(out, g.Over)
			case cgasSecExcepts:
				serr = cgasPutRows(out, g.Excepts)
			case cgasSecMonOps:
				serr = cgasPutRows(out, g.MonOps)
			case cgasSecGens:
				serr = cgasPutRows(out, g.Gens)
			case cgasSecRes:
				serr = cgasPutRows(out, g.Res)
			case cgasSecLocks:
				serr = cgasPutRows(out, g.Locks)
			case cgasSecJPMS:
				serr = cgasPutRows(out, g.JPMS)
			case cgasSecUISites:
				serr = cgasPutRows(out, g.UISites)
			case cgasSecSecrets:
				serr = cgasPutRows(out, g.Secrets)
			case cgasSecReach:
				serr = cgasPutRows(out, g.Reach)
			case cgasSecMeta:
				if metaSkip >= 0 {
					if serr = cgasPutRows(out, g.Meta[:metaSkip]); serr == nil {
						serr = cgasPutRows(out, g.Meta[metaSkip+1:])
					}
				} else {
					serr = cgasPutRows(out, g.Meta)
				}
			case cgasSecPkgRoots:
				serr = cgasPutRows(out, g.PkgRoots)
			case cgasSecTreeDir:
				serr = out.put(tDir)
			case cgasSecTrees:
				serr = cgasPutTrees(out, g.astTrees)
			case cgasSecStrings:
				serr = cgasPutArena(out, it.chunks, high, builtAtC, builtAtO, builtAtE)
			}
			if serr != nil {
				return serr
			}
		}
		return nil
	}()
	if werr != nil {
		return fail(werr)
	}
	if terr := out.w.Flush(); terr != nil {
		return fail(terr)
	}
	if err := f.Close(); err != nil {
		return 0, fmt.Errorf("write %s: %v", path, err)
	}
	return int64(total), nil
}

func cgasPutSyms(out *cgasOut, syms []Sym) error {
	if len(syms) == 0 {
		return nil
	}
	const batch = 161 * cgasSymRowSz
	scratch := make([]byte, 0, batch)
	row := make([]byte, cgasSymRowSz)
	var c cgasSymCodec
	for i := range syms {
		c.b = row
		c.o = 0
		c.enc = true
		c.id = syms[i].ID
		c.err = nil
		c.symRow(&syms[i])
		if c.err != nil {
			return fmt.Errorf("save symbols: %w", c.err)
		}
		scratch = append(scratch, row...)
		if len(scratch)+cgasSymRowSz > batch {
			if err := out.put(scratch); err != nil {
				return err
			}
			scratch = scratch[:0]
		}
	}
	if len(scratch) > 0 {
		if err := out.put(scratch); err != nil {
			return err
		}
	}
	return nil
}

func cgasPutTrees(out *cgasOut, trees []*tsTree) error {
	for _, tr := range trees {
		if tr == nil || len(tr.recs) == 0 {
			continue
		}
		if err := out.put(unsafe.Slice((*byte)(unsafe.Pointer(&tr.recs[0])),
			len(tr.recs)*int(unsafe.Sizeof(tsRec{})))); err != nil {
			return err
		}
	}
	return nil
}

func cgasPutArena(out *cgasOut, chunks [][]byte, high []int32, zc, zo, ze int32) error {
	var zeros [4096]byte
	for i := range chunks {
		h := int(high[i])
		if h == 0 {
			continue
		}
		ch := chunks[i][:h]
		if zc >= 0 && i == int(zc) {
			if err := out.put(ch[:zo]); err != nil {
				return err
			}
			for n := int(ze - zo); n > 0; {
				k := n
				if k > len(zeros) {
					k = len(zeros)
				}
				if err := out.put(zeros[:k]); err != nil {
					return err
				}
				n -= k
			}
			if err := out.put(ch[ze:]); err != nil {
				return err
			}
			continue
		}
		if err := out.put(ch); err != nil {
			return err
		}
	}
	return nil
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
		syscall.PROT_READ|syscall.PROT_WRITE, syscall.MAP_PRIVATE)
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
	memPtr := &mem[0]
	dec := func(id uint32) (uint64, uint64) {
		return secs[id].Off, secs[id].Len
	}
	decErr := func(err error) (*Graph, error) {
		return nil, bad("%v", err)
	}
	off, ln := dec(cgasSecStrChunks)
	chunkLens, err := cgasRows[uint32](mem, off, ln, "interner chunk lengths")
	if err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecStrPos)
	strPos, err := cgasRows[uint32](mem, off, ln, "interner offsets")
	if err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecStrLn)
	strLn, err := cgasRows[uint32](mem, off, ln, "interner lengths")
	if err != nil {
		return decErr(err)
	}
	if len(strPos) != len(strLn) {
		return nil, bad("interner offset/length counts differ (%d vs %d)", len(strPos), len(strLn))
	}
	var sum uint64
	for _, c := range chunkLens {
		sum += uint64(c)
	}
	if sum > al {
		return nil, bad("interner chunk table sums to %d bytes, arena holds %d", sum, al)
	}
	chunks := make([][]byte, 0, len(chunkLens))
	cur := ao
	for _, c := range chunkLens {
		chunks = append(chunks, mem[cur:cur+uint64(c)])
		cur += uint64(c)
	}
	for i := range strPos {
		c := strPos[i] >> offBits
		o := strPos[i] & offMask
		if int(c) >= len(chunks) || int(o)+int(strLn[i]) > len(chunks[c]) {
			return nil, bad("interner string %d references (%d,%d) beyond its chunk", i, strPos[i], strLn[i])
		}
	}
	off, ln = dec(cgasSecFiles)
	files, err := cgasRows[File](mem, off, ln, "files")
	if err != nil {
		return decErr(err)
	}
	for i := range files {
		f := &files[i]
		for _, id := range [7]uint32{f.full, f.path, f.dir, f.basename, f.ext, f.lang, f.sha1} {
			if int(id) >= len(strPos) {
				return nil, bad("file %d string id %d out of range (%d interned strings)", f.ID, id, len(strPos))
			}
		}
	}
	off, ln = dec(cgasSecMods)
	mods, err := cgasRows[Module](mem, off, ln, "modules")
	if err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecSyms)
	syms, err := cgasUnpackSyms(mem, off, ln)
	if err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecParams)
	params, err := cgasRows[Param](mem, off, ln, "params")
	if err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecFields)
	fields, err := cgasRows[Field](mem, off, ln, "fields")
	if err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecLocals)
	locals, err := cgasRows[Local](mem, off, ln, "locals")
	if err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecEnumMem)
	enumMem, err := cgasRows[EnumMember](mem, off, ln, "enum members")
	if err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecEdges)
	edges, err := cgasRows[Edge](mem, off, ln, "edges")
	if err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecCallsites)
	callsites, err := cgasRows[Callsite](mem, off, ln, "callsites")
	if err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecUnres)
	unres, err := cgasRows[Unres](mem, off, ln, "unresolved calls")
	if err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecImports)
	imports, err := cgasRows[Import](mem, off, ln, "imports")
	if err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecHazards)
	hazards, err := cgasRows[Hazard](mem, off, ln, "hazards")
	if err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecAttrs)
	attrs, err := cgasRows[Attr](mem, off, ln, "annotations")
	if err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecLits)
	lits, err := cgasRows[Literal](mem, off, ln, "literals")
	if err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecMarkers)
	markers, err := cgasRows[Marker](mem, off, ln, "markers")
	if err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecTypeRel)
	typeRel, err := cgasRows[TypeRel](mem, off, ln, "type relations")
	if err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecOvers)
	overs, err := cgasRows[Override](mem, off, ln, "overrides")
	if err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecExcepts)
	excepts, err := cgasRows[Exception](mem, off, ln, "exceptions")
	if err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecMonOps)
	monOps, err := cgasRows[MonitorOp](mem, off, ln, "monitor operations")
	if err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecGens)
	gens, err := cgasRows[Generic](mem, off, ln, "generics")
	if err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecRes)
	res, err := cgasRows[Resource](mem, off, ln, "resources")
	if err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecLocks)
	locks, err := cgasRows[LockOp](mem, off, ln, "lock operations")
	if err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecJPMS)
	jpms, err := cgasRows[JPMS](mem, off, ln, "module declarations")
	if err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecUISites)
	uisites, err := cgasRows[InputSite](mem, off, ln, "input sites")
	if err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecSecrets)
	secrets, err := cgasRows[Secret](mem, off, ln, "secrets")
	if err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecReach)
	reach, err := cgasRows[Reach](mem, off, ln, "reach rows")
	if err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecMeta)
	meta, err := cgasRows[MetaKV](mem, off, ln, "meta")
	if err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecPkgRoots)
	pkgRoots, err := cgasRows[uint32](mem, off, ln, "package roots")
	if err != nil {
		return decErr(err)
	}
	for _, id := range pkgRoots {
		if int(id) >= len(strPos) {
			return nil, bad("package root id %d out of range (%d interned strings)", id, len(strPos))
		}
	}
	tOff, tLn := secs[cgasSecTrees].Off, secs[cgasSecTrees].Len
	dOff, dLn := secs[cgasSecTreeDir].Off, secs[cgasSecTreeDir].Len
	if dLn < 12 {
		return nil, bad("node record directory too small (%d bytes)", dLn)
	}
	dirBytes := unsafe.Slice((*byte)(unsafe.Pointer(uintptr(unsafe.Pointer(memPtr))+uintptr(dOff))), int(dLn))
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
	recsAll := unsafe.Slice((*tsRec)(unsafe.Pointer(uintptr(unsafe.Pointer(memPtr))+uintptr(tOff))), int(tLn/stride))
	g := NewGraph()
	g.astBlob = mem
	it := g.Str
	it.chunks = chunks
	it.pos = strPos
	it.ln = strLn
	it.next = uint32(len(strPos))
	it.used = 0
	if len(chunks) > 0 {
		it.used = len(chunks[len(chunks)-1])
	}
	it.idx = make(map[string]uint32, len(strPos))
	for i := range strPos {
		it.idx[it.view(strPos[i], int(strLn[i]))] = uint32(i)
	}
	g.PkgRoots = pkgRoots
	g.pkgRootSet = make(map[string]bool, len(pkgRoots))
	for i := range pkgRoots {
		g.pkgRootSet[g.Str.get(pkgRoots[i])] = true
	}
	g.Mod = mods
	g.Files = files
	g.Sym = syms
	g.Params = params
	g.Fields = fields
	g.Locals = locals
	g.EnumMem = enumMem
	g.Edges = edges
	g.Callsite = callsites
	g.Unres = unres
	g.Imports = imports
	g.Hazards = hazards
	g.Attrs = attrs
	g.Lits = lits
	g.Markers = markers
	g.TypeRel = typeRel
	g.Over = overs
	g.Excepts = excepts
	g.MonOps = monOps
	g.Gens = gens
	g.Res = res
	g.Locks = locks
	g.JPMS = jpms
	g.UISites = uisites
	g.Secrets = secrets
	g.Reach = reach
	g.Meta = meta
	g.addMeta("built_at", time.Now().Format("2006-01-02T15:04:05"))
	g.astTrees = make([]*tsTree, nTreeFiles)
	base := 0
	for i := 0; i < nTreeFiles; i++ {
		n := int(counts[i])
		if base+n > len(recsAll) {
			return nil, bad("node record directory overruns the record arena")
		}
		if n > 0 {
			g.astTrees[i] = &tsTree{recs: recsAll[base : base+n]}
		}
		base += n
	}
	if base != len(recsAll) {
		return nil, bad("node record arena has %d unused records", len(recsAll)-base)
	}
	g.buildIndexes()
	g.buildCallGraph()
	return g, nil
}
