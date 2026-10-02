package main

import (
	"bufio"
	"bytes"
	"crypto/sha1"
	"encoding/hex"
	"encoding/json/jsontext"
	"encoding/json/v2"
	"fmt"
	"io"
	"io/fs"
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

const tsGrammarTag = "v0.24.2"

var tsAbiVersion = 0

type tsAnonChildField struct{ parent, child, field string }
type tsKindTables struct {
	symCount, fieldCount int
	symNamed, symVisible []bool
	symNames, fieldNames []string
	anonChildFields      []tsAnonChildField
}

func grammarBaseDir() string {
	if base := os.Getenv("TREE_SITTER_GRAMMARS"); base != "" {
		return base
	}
	home, err := os.UserHomeDir()
	if err != nil {
		return ""
	}
	return filepath.Join(home, ".cache", "codegraph", "grammars")
}
func tsGrammarFatal(dir string, err error) {
	fmt.Fprintf(os.Stderr, "codegraph-rust: grammar sources not usable at %s (%v)\n", dir, err)
	fmt.Fprintf(os.Stderr, "run: git clone --depth 1 --branch %s https://github.com/tree-sitter/tree-sitter-rust %s\n",
		tsGrammarTag, dir)
	os.Exit(1)
}
func jsonObject(raw []byte) ([]string, map[string]jsontext.Value) {
	dec := jsontext.NewDecoder(bytes.NewReader(raw))
	if tok, err := dec.ReadToken(); err != nil || tok.Kind() != '{' {
		return nil, nil
	}
	var keys []string
	vals := make(map[string]jsontext.Value)
	for dec.PeekKind() != '}' {
		nameTok, err := dec.ReadToken()
		if err != nil {
			return keys, vals
		}
		key := nameTok.String()
		val, err := dec.ReadValue()
		if err != nil {
			return keys, vals
		}
		keys = append(keys, key)
		vals[key] = val.Clone()
	}
	return keys, vals
}
func jsonArray(raw []byte) ([]jsontext.Value, error) {
	dec := jsontext.NewDecoder(bytes.NewReader(raw))
	if tok, err := dec.ReadToken(); err != nil {
		return nil, err
	} else if tok.Kind() != '[' {
		return nil, fmt.Errorf("not a JSON array")
	}
	var elems []jsontext.Value
	for dec.PeekKind() != ']' {
		val, err := dec.ReadValue()
		if err != nil {
			return nil, err
		}
		elems = append(elems, val.Clone())
	}
	return elems, nil
}
func anonDirectMembers(rules map[string]any, ruleName string, seen map[string]bool, out map[string]bool) {
	if seen[ruleName] {
		return
	}
	rule, ok := rules[ruleName]
	if !ok {
		return
	}
	seen[ruleName] = true
	var walk func(n any)
	walk = func(n any) {
		switch v := n.(type) {
		case []any:
			for _, m := range v {
				walk(m)
			}
		case map[string]any:
			switch v["type"] {
			case "STRING":
				if s, ok := v["value"].(string); ok {
					out[s] = true
				}
			case "ALIAS":
				named := true
				if b, ok := v["named"].(bool); ok {
					named = b
				}
				if !named {
					if s, ok := v["value"].(string); ok {
						out[s] = true
					}
				}
			case "SYMBOL":
				if s, ok := v["name"].(string); ok && strings.HasPrefix(s, "_") {
					anonDirectMembers(rules, s, seen, out)
				}
			default:
				for _, m := range v {
					walk(m)
				}
			}
		}
	}
	walk(rule)
}
func buildTsKindTables() tsKindTables {
	dir := filepath.Join(grammarBaseDir(), "tree-sitter-rust")
	nodeTypesRaw, err := os.ReadFile(filepath.Join(dir, "src", "node-types.json"))
	if err != nil {
		tsGrammarFatal(dir, err)
	}
	grammarRaw, err := os.ReadFile(filepath.Join(dir, "src", "grammar.json"))
	if err != nil {
		tsGrammarFatal(dir, err)
	}
	var grammar struct {
		Rules      map[string]any `json:"rules"`
		Supertypes []string       `json:"supertypes"`
	}
	if err := json.Unmarshal(grammarRaw, &grammar); err != nil {
		tsGrammarFatal(dir, fmt.Errorf("grammar.json: %w", err))
	}
	nodeTypes, err := jsonArray(nodeTypesRaw)
	if err != nil {
		tsGrammarFatal(dir, fmt.Errorf("node-types.json: %w", err))
	}
	type sym struct {
		name                  string
		named, visible, super bool
	}
	var syms []sym
	var fields []string
	seenFields := make(map[string]bool)
	addField := func(name string) {
		if name == "" || seenFields[name] {
			return
		}
		seenFields[name] = true
		fields = append(fields, name)
	}
	seen := make(map[string]bool)
	type ak struct{ parent, field string }
	anonSets := make(map[ak]map[string]bool)
	var anonOrder []ak
	addAnon := func(parent, field, child string) {
		k := ak{parent, field}
		set, ok := anonSets[k]
		if !ok {
			set = make(map[string]bool)
			anonSets[k] = set
			anonOrder = append(anonOrder, k)
		}
		set[child] = true
	}
	for _, raw := range nodeTypes {
		keys, obj := jsonObject(raw)
		if obj == nil {
			continue
		}
		var name string
		named := true
		var fieldsRaw jsontext.Value
		for _, k := range keys {
			switch k {
			case "type":
				json.Unmarshal(obj[k], &name)
			case "named":
				var b bool
				if json.Unmarshal(obj[k], &b) == nil {
					named = b
				}
			case "fields":
				fieldsRaw = obj[k]
			}
		}
		if !seen[name] {
			seen[name] = true
			syms = append(syms, sym{name: name, named: named, visible: true})
		}
		if len(fieldsRaw) == 0 {
			continue
		}
		fkeys, fvals := jsonObject(fieldsRaw)
		for _, f := range fkeys {
			addField(f)
			_, evals := jsonObject(fvals[f])
			if evals == nil {
				continue
			}
			typesRaw, ok := evals["types"]
			if !ok || len(typesRaw) == 0 {
				continue
			}
			types, err := jsonArray(typesRaw)
			if err != nil {
				continue
			}
			for _, traw := range types {
				_, tvals := jsonObject(traw)
				if tvals == nil {
					continue
				}
				var tname string
				tnamed := true
				json.Unmarshal(tvals["type"], &tname)
				if braw, ok := tvals["named"]; ok {
					var b bool
					if json.Unmarshal(braw, &b) == nil {
						tnamed = b
					}
				}
				if !tnamed {
					addAnon(name, f, tname)
				} else if strings.HasPrefix(tname, "_") {
					out := make(map[string]bool)
					anonDirectMembers(grammar.Rules, tname, make(map[string]bool), out)
					for c := range out {
						addAnon(name, f, c)
					}
				}
			}
		}
	}
	type pk struct{ parent, child string }
	anonPairs := make(map[pk]string)
	for _, k := range anonOrder {
		for c := range anonSets[k] {
			key := pk{k.parent, c}
			if f, ok := anonPairs[key]; ok && f != k.field {
				continue
			}
			anonPairs[key] = k.field
		}
	}
	anonSorted := make([]tsAnonChildField, 0, len(anonPairs))
	for p, f := range anonPairs {
		anonSorted = append(anonSorted, tsAnonChildField{p.parent, p.child, f})
	}
	sort.Slice(anonSorted, func(i, j int) bool {
		if anonSorted[i].parent != anonSorted[j].parent {
			return anonSorted[i].parent < anonSorted[j].parent
		}
		return anonSorted[i].child < anonSorted[j].child
	})
	for _, name := range grammar.Supertypes {
		if !seen[name] {
			seen[name] = true
			syms = append(syms, sym{name: name, named: true, super: true})
		} else {
			for i := range syms {
				if syms[i].name == name {
					syms[i].super = true
				}
			}
		}
	}
	syms = append(syms, sym{name: "ERROR", named: true, visible: true})
	syms = append(syms, sym{name: "\x00MISSING", named: true, visible: true})
	t := tsKindTables{
		symCount:   len(syms),
		fieldCount: len(fields) + 1,
		symNamed:   make([]bool, len(syms)),
		symVisible: make([]bool, len(syms)),
		symNames:   make([]string, len(syms)),
		fieldNames: make([]string, len(fields)+1),
	}
	for i, s := range syms {
		t.symNamed[i], t.symVisible[i] = s.named, s.visible
		t.symNames[i] = s.name
	}
	copy(t.fieldNames[1:], fields)
	t.anonChildFields = anonSorted
	return t
}

var tsKindT = buildTsKindTables()
var (
	tsSymCount        = tsKindT.symCount
	tsFieldCount      = tsKindT.fieldCount
	tsSymNamed        = tsKindT.symNamed
	tsSymVisible      = tsKindT.symVisible
	tsSymNames        = tsKindT.symNames
	tsFieldNames      = tsKindT.fieldNames
	tsAnonChildFields = tsKindT.anonChildFields
)

const tsScope = "source.rust"
const (
	tsRecSize    = 32
	tsFlagMiss   = 1
	tsFlagErr    = 2
	tsFlagExtra  = 4
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
	_              [3]byte
}

func tsCLIBin() string {
	if b := os.Getenv("TREE_SITTER_BIN"); b != "" {
		return b
	}
	if b := filepath.Join(os.Getenv("HOME"), ".cache", "codegraph", "bin", "tree-sitter"); b != "" {
		if _, err := os.Stat(b); err == nil {
			return b
		}
	}
	if b, err := exec.LookPath("tree-sitter"); err == nil {
		return b
	}
	return "/opt/homebrew/bin/tree-sitter"
}

type tsParser struct {
	bin                                              string
	outBuf                                           []byte
	env                                              []string
	devnull                                          *os.File
	startsSlab                                       []int
	recsSlab                                         []tsRec
	stackSlab                                        []cstFrame
	unquoteSlab                                      []byte
	freshIDs                                         map[string]uint16
	missingMark                                      map[string]int
	tPrev, tOff, tNoff, tKids, tNkids, tFill, tNfill []int32
	tree                                             tsTree
}

type cstFrame struct {
	i     int32
	end   uint32
	depth int32
}

func tsParserNew() *tsParser {
	bin := tsCLIBin()
	if _, err := os.Stat(bin); err != nil {
		panic("tree-sitter CLI not found at " + bin + " -- see setup.sh")
	}
	env := append(os.Environ(), "NO_COLOR=1", "TERM=dumb")
	devnull, err := os.OpenFile(os.DevNull, os.O_WRONLY, 0)
	if err != nil {
		devnull = nil
	}
	return &tsParser{bin: bin, env: env, devnull: devnull,
		freshIDs: map[string]uint16{}, missingMark: map[string]int{}}
}
func (p *tsParser) free() {
	if p.devnull != nil {
		p.devnull.Close()
	}
}
func (p *tsParser) readCST(src, buf []byte) ([]byte, bool) {
	inR, inW, perr := os.Pipe()
	if perr != nil {
		return buf, false
	}
	outR, outW, perr := os.Pipe()
	if perr != nil {
		inR.Close()
		inW.Close()
		return buf, false
	}
	cmd := exec.Command(p.bin, "parse", "/dev/stdin", "--scope", tsScope, "--cst")
	cmd.Env = p.env
	cmd.Stdin = inR
	cmd.Stdout = outW
	cmd.Stderr = p.devnull
	if serr := cmd.Start(); serr != nil {
		inR.Close()
		inW.Close()
		outR.Close()
		outW.Close()
		return buf, false
	}
	inR.Close()
	outW.Close()
	for v := src; len(v) > 0; {
		n, werr := inW.Write(v)
		if werr != nil || n <= 0 {
			break
		}
		v = v[n:]
	}
	inW.Close()
	// The CST listing runs 20-40x the source bytes (one line per node, with
	// indentation), so size the scratch buffer from the input. The doubling
	// below still covers an underestimate, and the pool bounds retention.
	est := len(src) * 40
	if est < 1<<16 {
		est = 1 << 16
	}
	if est > 4<<20 {
		est = 4 << 20
	}
	if cap(buf) < est {
		buf = make([]byte, 0, est)
	}
	buf = buf[:0]
	for {
		off := len(buf)
		if off == cap(buf) {
			grow := make([]byte, off, cap(buf)*2+1<<16)
			copy(grow, buf)
			buf = grow
		}
		end := off + 32768
		if end > cap(buf) {
			end = cap(buf)
		}
		n, rerr := outR.Read(buf[off:end])
		buf = buf[:off+n]
		if rerr != nil {
			break
		}
	}
	outR.Close()
	err := cmd.Wait()
	if err != nil && len(buf) == 0 {
		return buf, false
	}
	return buf, true
}

type tsTree struct {
	recs  []tsRec
	prev  []int32
	off   []int32
	kids  []int32
	noff  []int32
	nkids []int32
}

func slabI32(dst []int32, n int) []int32 {
	if cap(dst) < n {
		return make([]int32, n, n+n/4+64)
	}
	return dst[:n]
}

func (t *tsTree) index(p *tsParser) {
	if cap(p.tPrev) > 1<<18 || cap(p.tOff) > 1<<18 || cap(p.tKids) > 1<<19 {
		p.tPrev, p.tOff, p.tNoff, p.tKids, p.tNkids, p.tFill, p.tNfill = nil, nil, nil, nil, nil, nil, nil
	}
	n := len(t.recs)
	t.prev = slabI32(p.tPrev, n)
	p.tPrev = t.prev
	for i := range t.prev {
		t.prev[i] = -1
	}
	t.off = slabI32(p.tOff, n+1)
	p.tOff = t.off
	t.noff = slabI32(p.tNoff, n+1)
	p.tNoff = t.noff
	for i := range n {
		nc, nn := 0, 0
		for c, end := i+1, int(t.recs[i].subEnd); c < end; c = int(t.recs[c].subEnd) {
			nc++
			if t.recs[c].flags&tsFlagNamed != 0 {
				nn++
			}
		}
		t.off[i+1] = int32(nc)
		t.noff[i+1] = int32(nn)
	}
	for i := 1; i <= n; i++ {
		t.off[i] += t.off[i-1]
		t.noff[i] += t.noff[i-1]
	}
	t.kids = slabI32(p.tKids, int(t.off[n]))
	p.tKids = t.kids
	t.nkids = slabI32(p.tNkids, int(t.noff[n]))
	p.tNkids = t.nkids
	fill := slabI32(p.tFill, n)
	p.tFill = fill
	nfill := slabI32(p.tNfill, n)
	p.tNfill = nfill
	copy(fill, t.off[:n])
	copy(nfill, t.noff[:n])
	for i := range n {
		last := int32(-1)
		for c, end := i+1, int(t.recs[i].subEnd); c < end; c = int(t.recs[c].subEnd) {
			t.kids[fill[i]] = int32(c)
			fill[i]++
			if t.recs[c].flags&tsFlagNamed != 0 {
				t.nkids[nfill[i]] = int32(c)
				nfill[i]++
			}
			t.prev[c] = last
			last = int32(c)
		}
	}
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

func hasNode(n tsNode) bool { return n.t != nil }
func kindID(n tsNode) uint16 {
	if !hasNode(n) {
		return tsSymInvalid
	}
	return n.t.recs[n.i].sym
}
func nSymbol(n tsNode) uint16 { return kindID(n) }
func nodeKindName(s uint16) string {
	if int(s) < tsSymCount {
		return tsSymNames[s]
	}
	if s == 0xFFFE {
		return "_ERROR"
	}
	if s == 0xFFFF {
		return "ERROR"
	}
	return ""
}
func startByte(n tsNode) uint { return uint(n.t.recs[n.i].start) }
func endByte(n tsNode) uint {
	if !hasNode(n) {
		return 0
	}
	return uint(n.t.recs[n.i].end)
}
func nStartByte(n tsNode) uint { return startByte(n) }
func nEndByte(n tsNode) uint   { return endByte(n) }
func nStartRow(n tsNode) uint {
	if !hasNode(n) {
		return 0
	}
	return uint(n.t.recs[n.i].srow)
}
func nEndRow(n tsNode) uint {
	if !hasNode(n) {
		return 0
	}
	return uint(n.t.recs[n.i].erow)
}
func nIsNamed(n tsNode) bool {
	if !hasNode(n) {
		return false
	}
	return n.t.recs[n.i].flags&tsFlagNamed != 0
}
func nHasError(n tsNode) bool {
	if !hasNode(n) {
		return false
	}
	return n.t.recs[n.i].flags&tsFlagErr != 0
}
func nIsMissing(n tsNode) bool {
	if !hasNode(n) {
		return false
	}
	return n.t.recs[n.i].flags&tsFlagMiss != 0
}
func nChildCount(n tsNode) uint32 {
	if !hasNode(n) {
		return 0
	}
	if nc := n.t.recs[n.i].nchild; nc != 0xFFFF {
		return uint32(nc)
	}
	c := n.i + 1
	end := n.t.recs[n.i].subEnd
	k := 0
	for c < end {
		k++
		c = n.t.recs[c].subEnd
	}
	return uint32(k)
}
func nNamedChildCount(n tsNode) uint32 {
	if !hasNode(n) {
		return 0
	}
	if nn := n.t.recs[n.i].nnamed; nn != 0xFFFF {
		return uint32(nn)
	}
	k := 0
	for c, end := n.i+1, n.t.recs[n.i].subEnd; c < end; c = n.t.recs[c].subEnd {
		if n.t.recs[c].flags&tsFlagNamed != 0 {
			k++
		}
	}
	return uint32(k)
}
func nChildAt(n tsNode, k uint32) tsNode {
	if !hasNode(n) || k >= nChildCount(n) {
		return tsNode{}
	}
	return tsNode{t: n.t, i: n.t.kids[n.t.off[n.i]+int32(k)]}
}
func nNamedChildAt(n tsNode, k uint32) tsNode {
	if !hasNode(n) || k >= nNamedChildCount(n) {
		return tsNode{}
	}
	return tsNode{t: n.t, i: n.t.nkids[n.t.noff[n.i]+int32(k)]}
}
func nField(n tsNode, f uint16) tsNode {
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
func nParent(n tsNode) tsNode {
	if !hasNode(n) {
		return tsNode{}
	}
	pi := n.t.recs[n.i].parent
	if pi < 0 {
		return tsNode{}
	}
	return tsNode{t: n.t, i: pi}
}
func nPrevSibling(n tsNode) tsNode {
	if !hasNode(n) {
		return tsNode{}
	}
	pi := n.t.recs[n.i].parent
	if pi < 0 {
		return tsNode{}
	}
	if p := n.t.prev[n.i]; p >= 0 {
		return tsNode{t: n.t, i: p}
	}
	return tsNode{}
}
func nValid(n tsNode) bool { return hasNode(n) }
func tsNodeId(n tsNode) uintptr {
	if !hasNode(n) {
		return 0
	}
	return uintptr(n.i) + 1
}

type tsCursor struct {
	t     *tsTree
	stack []int32
	cur   int32
	dead  bool
}

func (cu *tsCursor) reset(n tsNode) {
	if !hasNode(n) {
		cu.dead = true
		return
	}
	cu.dead = false
	cu.t = n.t
	cu.stack = append(cu.stack[:0], n.i)
	cu.cur = n.i
}
func (cu *tsCursor) close() {
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
	if cu.dead || nChildCount(tsNode{t: cu.t, i: cu.cur}) == 0 {
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
func tsWalk(n tsNode) *tsCursor {
	c := &tsCursor{}
	c.reset(n)
	return c
}
func tsKindCount() int            { return tsSymCount }
func tsKindName(id uint16) string { return nodeKindName(id) }
func tsKindIsNamed(id uint16) bool {
	return tsSymNamed[id] && tsSymVisible[id]
}

var kindIDs = map[string][]uint16{}

func kindIs(n tsNode, k string) bool {
	s := nSymbol(n)
	return slices.Contains(kindIDs[k], s)
}

var fieldIDs = func() map[string]uint16 {
	m := make(map[string]uint16, tsFieldCount)
	for f := 1; f < tsFieldCount; f++ {
		if _, dup := m[tsFieldNames[f]]; !dup {
			m[tsFieldNames[f]] = uint16(f)
		}
	}
	return m
}()

func tsFieldID(name string) uint16 { return fieldIDs[name] }

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
			return tsFieldID(f)
		}
	}
	return 0
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
var mashtag = []byte("#")

func (p *tsParser) decodeCST(out, src []byte) *tsTree {
	if cap(p.recsSlab) > 1<<18 {
		p.recsSlab = nil
	}
	if cap(p.stackSlab) > 1<<14 {
		p.stackSlab = nil
	}
	if cap(p.startsSlab) > 1<<18 {
		p.startsSlab = nil
	}
	starts := p.startsSlab[:0]
	totalWidth := 1
	{
		lineNo, lineStart := 0, 0
		for lineStart < len(src) {
			j := bytes.IndexByte(src[lineStart:], '\n')
			if j < 0 {
				break
			}
			i := lineStart + j
			n := i - lineStart
			if n > 0 && src[i-1] == '\r' {
				n--
			}
			if v := digits10(lineNo) + digits10(n) + 1; v > totalWidth {
				totalWidth = v
			}
			starts = append(starts, lineStart)
			lineNo++
			lineStart = i + 1
		}
		n := len(src) - lineStart
		if n > 0 && src[len(src)-1] == '\r' {
			n--
		}
		if v := digits10(lineNo) + digits10(n) + 1; v > totalWidth {
			totalWidth = v
		}
		starts = append(starts, lineStart)
	}
	d := &cstDecoder{starts: starts, total: len(src)}
	recs := p.recsSlab[:0]
	if cap(recs) == 0 && len(out) > 1024 {
		recs = make([]tsRec, 0, len(out)/32+64)
	}
	stack := p.stackSlab[:0]
	nextFresh := uint16(len(tsSymByID) + 0x4000)
	clear(p.freshIDs)
	freshIDs := p.freshIDs
	unquoteBuf := p.unquoteSlab[:0]
	defer func() { p.unquoteSlab = unquoteBuf }()
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
	missingMarks := p.missingMark
	clear(missingMarks)
	hasMissing := false
	{
		line := out
		for i := bytes.Index(line, []byte("(MISSING ")); i >= 0; {
			rest := line[i+len("(MISSING "):]
			var kind []byte
			if len(rest) > 0 && rest[0] == '"' {
				kind = unquoteBytes(rest, &unquoteBuf)
			} else if j := bytes.Index(rest, []byte(" [")); j > 0 {
				kind = rest[:j]
			}
			b := rest
			if len(kind) > 0 {
				b = b[bytes.Index(b, kind)+len(kind):]
			}
			mk := func() (int, int, bool) {
				l := bytes.IndexByte(b, '[')
				if l < 0 {
					return 0, 0, false
				}
				b = b[l+1:]
				r, n1 := atoiBytes(b)
				if n1 == 0 {
					return 0, 0, false
				}
				b = bytes.TrimLeft(b[n1:], ", ")
				c, n2 := atoiBytes(b)
				if n2 == 0 {
					return 0, 0, false
				}
				b = b[n2:]
				return r, c, true
			}
			sr, sc, ok1 := mk()
			er, ec, ok2 := mk()
			if len(kind) > 0 && ok1 && ok2 {
				key := string(kind) + "\x00" + itoa(int(d.offset(sr, sc))) + ":" + itoa(int(d.offset(er, ec)))
				missingMarks[key]++
			}
			line = line[i+len("(MISSING "):]
			i = bytes.Index(line, []byte("(MISSING "))
		}
	}
	hasMissing = len(missingMarks) > 0
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
		spaces := len(rest) - len(bytes.TrimLeft(rest, " "))
		depth := int32(-1)
		if diff := spaces - rwWidth(totalWidth, erow, ecol); diff >= 0 {
			depth = int32(diff / 2)
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
		if srow > 65534 || erow > 65534 {
			panic(sprintf("tree-sitter row %d exceeds the 16-bit line-number range",
				max(srow, erow)))
		}
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
		if !missing && hasMissing {
			if key := string(kindB) + "\x00" + itoa(int(start)) + ":" + itoa(int(end)); missingMarks[key] > 0 {
				missingMarks[key]--
				rec.flags |= tsFlagMiss
			}
		}
		if bytes.Equal(kindB, tsErrKind) || hasErrMark {
			rec.flags |= tsFlagErr
		}
		idx := int32(len(recs))
		recs = append(recs, rec)
		for len(stack) > 0 {
			top := stack[len(stack)-1]
			if depth >= 0 {
				if top.depth < 0 {
					if top.end > start {
						break
					}
				} else if top.depth < depth {
					break
				}
			} else if top.end > start {
				break
			}
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
		stack = append(stack, cstFrame{i: idx, end: end, depth: depth})
	}
	for len(stack) > 0 {
		popped := stack[len(stack)-1]
		recs[popped.i].subEnd = int32(len(recs))
		stack = stack[:len(stack)-1]
	}
	if len(recs) == 0 {
		return nil
	}
	recs[0].parent = -1
	for i := range recs {
		r := &recs[i]
		if r.flags&(tsFlagNamed|tsFlagMiss) == tsFlagNamed &&
			r.start == r.end && r.flags&tsFlagErr != 0 &&
			int(r.subEnd) == i+1 && tsSymNames[r.sym] != "ERROR" {
			r.flags |= tsFlagMiss
		}
	}
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
	p.startsSlab = starts
	p.recsSlab = recs
	p.stackSlab = stack
	t := &p.tree
	t.recs = recs
	t.index(p)
	return t
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
func digits10(v int) int {
	n := 0
	for {
		n++
		v /= 10
		if v == 0 {
			return n
		}
	}
}
func rwWidth(totalWidth, row, col int) int {
	w := max(totalWidth-digits10(row)-digits10(col), 1)
	return w
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

var hazardCategories = []string{"unsafe", "panic", "alloc", "clone", "lock",
	"atomic", "async", "io", "ffi", "mem", "exec", "control"}
var hazardCol = map[string]int{
	"unsafe": cNUnsafe, "panic": cNPanic, "alloc": cNAlloc, "clone": cNClone,
	"lock": cNLock, "atomic": cNAtomic, "async": cNAsync, "io": cNIO,
	"ffi": cNFfi, "mem": cNMem, "exec": cNExec, "control": cNControl,
}

type buildOpts struct {
	includeTests     bool
	includeGenerated bool
	includeVendored  bool
	quiet            bool
	workers          int
	keepTrees        bool
}

var opts = buildOpts{includeTests: true, workers: defaultParseWorkers}

const langName = "rust"
const targetVersion = "Rust 1.97 (edition 2024)"

const pipeDepth = 2

type cstItem struct {
	idx int
	rec srcFile
	buf []byte
	ok  bool
	res *fileResult
}

func build(root string, g *Graph) (int, error) {
	if !opts.quiet {
		printfln("  " + parserBanner)
	}
	t0 := time.Now()
	dis, st := discover(root, g, opts.quiet)
	g.SetMeta("files_skipped", sprintf(
		"big=%d special=%d escaping_symlink=%d denied=%d walk_errors=%d",
		st.big, st.special, st.escape, st.denied, st.walkErr))
	tDiscover := time.Since(t0)
	if !opts.quiet {
		printfln("  %d %s files discovered in %.1fs", len(dis.files), langName,
			tDiscover.Seconds())
	}
	for i, name := range dis.modOrder {
		g.Modules = append(g.Modules, ModuleRow{ID: int32(i + 1), name: cgPut(name),
			kind: cgPut(dis.kinds[i])})
	}
	g.byName = map[string][]byNameEntry{}
	g.byQual = map[string]int32{}
	n := len(dis.files)
	nFailed := 0
	parsed := 0
	var trees [][]tsRec
	if opts.keepTrees {
		trees = make([][]tsRec, len(g.Files))
	}
	step := max(n/20, 1)
	tParse := time.Now()
	if n > 0 {
		// Parse and decode files with a pool of workers: each owns its own
		// tree-sitter parser and decode slabs, so everything up to and
		// including fileResult is private state. The consumer merges results
		// strictly in file order, so symbol ids and every dump row are
		// unchanged by the worker count.
		workers := opts.workers
		if workers < 1 {
			workers = 1
		}
		if workers > n {
			workers = n
		}
		if workers > 64 {
			workers = 64
		}
		freeBufs := make(chan []byte, workers+2)
		freeRes := make(chan *fileResult, workers+2)
		cstCh := make(chan cstItem, workers+2)
		jobs := make(chan int, workers)
		go func() {
			for i := range n {
				jobs <- i
			}
			close(jobs)
		}()
		var wg sync.WaitGroup
		for w := 0; w < workers; w++ {
			wg.Add(1)
			go func() {
				defer wg.Done()
				rp := newFileParser()
				defer rp.close()
				for i := range jobs {
					sf := dis.files[i]
					var buf []byte
					select {
					case buf = <-freeBufs:
					default:
					}
					buf, ok := rp.p.readCST(sf.data, buf)
					it := cstItem{idx: i, rec: sf, buf: buf, ok: ok}
					if ok {
						var res *fileResult
						select {
						case res = <-freeRes:
						default:
							res = new(fileResult)
						}
						res.reset(i, sf.rel)
						scanMarkers(sf, res)
						rp.decodeFile(sf, res, buf)
						it.res = res
					}
					cstCh <- it
				}
			}()
		}
		go func() {
			wg.Wait()
			close(cstCh)
		}()
		done := 0
		pending := map[int]cstItem{}
		process := func(it cstItem) {
			done++
			if !opts.quiet && done%step == 0 {
				printfln("  ... %d/%d files", done, n)
			}
			fr := &g.Files[it.rec.id-1]
			if !it.ok {
				nFailed++
				fr.Parsed = 0
				fr.NParseErrors++
			} else {
				res := it.res
				fr.NParseErrors = res.nErr
				fr.NMissingNodes = res.nMissing
				mergeResult(g, res)
				parsed++
				if trees != nil {
					trees[it.rec.id-1] = res.recs
					res.recs = nil
				}
				if cap(res.ar) > 1<<20 {
					res.ar = nil
				}
				select {
				case freeRes <- res:
				default:
				}
			}
			dis.files[it.idx].data = nil
			if cap(it.buf) > 2<<20 {
				it.buf = make([]byte, 0, 1<<20)
			}
			select {
			case freeBufs <- it.buf:
			default:
			}
		}
		for it := range cstCh {
			if it.idx != done {
				pending[it.idx] = it
				continue
			}
			process(it)
			for {
				nx, ok := pending[done]
				if !ok {
					break
				}
				delete(pending, done)
				process(nx)
			}
		}
		close(freeBufs)
		close(freeRes)
	}
	if nFailed > 0 && (nFailed > parsed/100 || !opts.quiet) {
		eprintln("  WARNING: " + itoa(nFailed) + " of " + itoa(len(dis.files)) +
			" file(s) FAILED to parse and contributed nothing.")
		eprintln("           Re-run with CODEGRAPH_DEBUG=1 for the tracebacks.")
	}
	if parsed > 0 && len(g.SymName) == 0 && !opts.quiet {
		eprintln("  WARNING: " + itoa(parsed) + " file(s) were read and produced NO symbols.")
	}
	tParseDur := time.Since(tParse)
	if !opts.quiet {
		suffix := ""
		if nFailed > 0 {
			suffix = sprintf(" (%d file(s) failed)", nFailed)
		}
		printfln("  %d symbols parsed in %.1fs%s", len(g.SymName),
			tParseDur.Seconds(), suffix)
	}
	tGraph := time.Now()
	resolveCalls(g)
	if !opts.quiet {
		printfln("  call graph built in %.1fs", time.Since(tGraph).Seconds())
	}
	nImp := resolveImportTargets(g)
	g.SetMeta("imports_resolved", sprintf("%d of %d import rows point at a file in this tree",
		nImp, len(g.Imports)))
	readManifests(root, g)
	den := g.nResolved + g.nUnresolved
	pct := 0
	if den > 0 {
		pct = 100 * g.nResolved / den
	}
	g.SetMeta("calls_resolved", sprintf(
		"%d in-tree / %d external / %d unresolved (%d%% of in-scope resolved)",
		g.nResolved, g.nExternal, g.nUnresolved, pct))
	tAgg := time.Now()
	materialize(g)
	if !opts.quiet {
		printfln("  aggregates materialized in %.1fs", time.Since(tAgg).Seconds())
	}
	g.SetMeta("schema_version", "1")
	g.SetMeta("lang", langName)
	g.SetMeta("target", targetVersion)
	g.SetMeta("root", root)
	g.SetMeta("parse_mode", "tree-sitter")
	g.SetMeta("parser", parserBanner)
	g.SetMeta("files_parsed", itoa(parsed))
	g.SetMeta("files_failed", itoa(nFailed))
	g.Meta = append(g.Meta, MetaRow{key: cgPutExt("built_at"),
		value: cgPutExt(time.Now().Format("2006-01-02T15:04:05"))})
	if trees != nil {
		g.astTrees = make([]*tsTree, len(trees))
		for i := range trees {
			if len(trees[i]) > 0 {
				g.astTrees[i] = &tsTree{recs: trees[i]}
			}
		}
	}
	return parsed, nil
}
func materialize(g *Graph) {
	n := int32(len(g.SymName))
	fanOut := make([]int32, n+1)
	fanIn := make([]int32, n+1)
	csites := make([]int32, n+1)
	unres := make([]int32, n+1)
	hazN := make([]int32, n+1)
	uniqCalls := make([]int32, n+1)
	hazCat := map[string]map[int32]int32{}
	for _, c := range hazardCategories {
		hazCat[c] = map[int32]int32{}
	}
	for i := range g.Edges {
		e := &g.Edges[i]
		if e.Caller >= 1 && e.Caller <= n {
			uniqCalls[e.Caller]++
		}
		if e.IsSelf == 0 {
			fanOut[e.Caller]++
			fanIn[e.Callee]++
		}
	}
	for i := range g.Callsites {
		csites[g.Callsites[i].Callee]++
	}
	for i := range g.Unresolved {
		u := &g.Unresolved[i]
		unres[u.Caller] += int32(u.N)
	}
	for i := range g.Hazards {
		h := &g.Hazards[i]
		hazN[h.SymID] += h.N
		if m, ok := hazCat[h.Category()]; ok && h.SymID >= 1 && h.SymID <= n {
			m[h.SymID] += h.N
		}
	}
	self := map[int32]bool{}
	for i := range g.Edges {
		if g.Edges[i].IsSelf == 1 {
			self[g.Edges[i].Caller] = true
		}
	}
	for sid := int32(1); sid <= n; sid++ {
		g.Set(sid, cFanOut, fanOut[sid])
		g.Set(sid, cFanIn, fanIn[sid])
		g.Set(sid, cNCallsites, csites[sid])
		g.Set(sid, cNUnresolvedCalls, unres[sid])
		g.Set(sid, cNHazards, hazN[sid])
		g.Set(sid, cIsRecursive, boolT(self[sid]))
		g.Set(sid, cIsLeaf, boolT(fanOut[sid] == 0))
		g.Set(sid, cIsRoot, boolT(fanIn[sid] == 0))
		g.Set(sid, cNUniqueCalls, uniqCalls[sid])
		for c, m := range hazCat {
			if v, ok := m[sid]; ok {
				g.Set(sid, int32(hazardCol[c]), v)
			}
		}
	}
	agg := map[int32]*fileAgg{}
	for i := range g.Files {
		agg[g.Files[i].ID] = &fileAgg{id: g.Files[i].ID}
	}
	for sid := int32(1); sid <= n; sid++ {
		a := agg[g.SymFile[sid-1]]
		if a == nil {
			continue
		}
		a.nSym++
		if isFnKind(g.SymKind[sid-1].Str()) {
			a.nFn++
		}
		if countsAsType(g.SymKind[sid-1].Str()) {
			a.nType++
		}
		cy := g.Mv(sid, cCyclomatic)
		a.totCyc += cy
		if cy > a.maxCyc {
			a.maxCyc = cy
		}
		a.totRisk += g.Mv(sid, cRiskScore)
	}
	impCount := map[int32]int32{}
	for i := range g.Imports {
		impCount[g.Imports[i].FileID]++
	}
	for i := range g.Files {
		f := &g.Files[i]
		if a := agg[f.ID]; a != nil {
			f.NSymbols, f.NFunctions, f.NTypes = a.nSym, a.nFn, a.nType
			f.TotalCyclo, f.MaxCyclo, f.TotalRisk = a.totCyc, a.maxCyc, a.totRisk
		}
		f.NImports = impCount[f.ID]
	}
	magg := map[int32]*modAgg{}
	getMod := func(id int32) *modAgg {
		a := magg[id]
		if a == nil {
			a = &modAgg{}
			magg[id] = a
		}
		return a
	}
	for sid := int32(1); sid <= n; sid++ {
		mid := g.SymModule[sid-1]
		if mid < 0 {
			continue
		}
		a := getMod(mid)
		a.nSym++
		a.nPub += g.Mv(sid, cIsPublic)
	}
	for i := range g.Files {
		f := &g.Files[i]
		if f.ModuleID < 0 {
			continue
		}
		a := getMod(f.ModuleID)
		a.nFiles++
		a.sloc += f.Sloc
	}
	modOut := map[int32]map[int32]bool{}
	modIn := map[int32]map[int32]bool{}
	for i := range g.Edges {
		e := &g.Edges[i]
		c := g.SymModule[e.Caller-1]
		k := g.SymModule[e.Callee-1]
		if c < 0 || k < 0 || c == k {
			continue
		}
		if modOut[c] == nil {
			modOut[c] = map[int32]bool{}
		}
		modOut[c][k] = true
		if modIn[k] == nil {
			modIn[k] = map[int32]bool{}
		}
		modIn[k][c] = true
	}
	for i := range g.Modules {
		m := &g.Modules[i]
		a := magg[m.ID]
		if a != nil {
			m.NSymbols, m.NPublic = a.nSym, a.nPub
			m.NFiles, m.Sloc = a.nFiles, a.sloc
		}
		m.FanOut = int32(len(modOut[m.ID]))
		m.FanIn = int32(len(modIn[m.ID]))
		if m.FanIn+m.FanOut == 0 {
			m.Instability = 0.0
		} else {
			m.Instability = fdiv(float64(m.FanOut), float64(m.FanIn+m.FanOut))
		}
	}
	lockAcross := map[int32]int32{}
	for i := range g.AsyncPoints {
		a := &g.AsyncPoints[i]
		if a.NGuardsLive > 0 && a.GuardDropped == 0 {
			lockAcross[a.SymID]++
		}
	}
	unsafeOps := map[int32]int32{}
	safetyDocs := map[int32]int32{}
	derives := map[int32]int32{}
	for i := range g.UnsafeBlks {
		u := &g.UnsafeBlks[i]
		unsafeOps[u.SymID] += u.NOps
		safetyDocs[u.SymID] += u.HasSafety
	}
	for i := range g.Derives {
		if g.Derives[i].SymID > 0 {
			derives[g.Derives[i].SymID]++
		}
	}
	externCalls := map[int32]int32{}
	for i := range g.Edges {
		if g.Edges[i].Callee >= 1 && g.Edges[i].Callee <= n &&
			g.Mv(g.Edges[i].Callee, cIsExternFn) == 1 {
			externCalls[g.Edges[i].Caller]++
		}
	}
	monoMods := map[int32]map[int32]bool{}
	for i := range g.Edges {
		k := g.Edges[i].Callee
		if k < 1 || k > n {
			continue
		}
		if monoMods[k] == nil {
			monoMods[k] = map[int32]bool{}
		}
		monoMods[k][g.SymModule[g.Edges[i].Caller-1]] = true
	}
	bySymbol := map[int32][]int32{}
	for i := range g.Edges {
		bySymbol[g.Edges[i].Callee] = append(bySymbol[g.Edges[i].Callee],
			g.SymModule[g.Edges[i].Caller-1])
	}
	_ = bySymbol
	for sid := int32(1); sid <= n; sid++ {
		arms := g.Mv(sid, cNMatchArms)
		sw := g.Mv(sid, cNSwitch)
		g.Set(sid, cNCases, arms)
		if arms > 0 {
			g.Set(sid, cCyclomatic, g.Mv(sid, cCyclomatic)+arms-sw)
		}
		v := max(g.Mv(sid, cNArith)-g.Mv(sid, cNCheckedArith), 0)
		g.Set(sid, cNArithUnchecked, v)
		if g.Mv(sid, cIsAsyncFn) == 1 {
			g.Set(sid, cNBlockingInAsync, g.Mv(sid, cNBlockingIO))
		}
		g.Set(sid, cNLockAcrossAwait, lockAcross[sid])
		g.Set(sid, cNUnsafeOps, unsafeOps[sid])
		g.Set(sid, cNSafetyComments, safetyDocs[sid])
		g.Set(sid, cNDerives, derives[sid])
		g.Set(sid, cNExternCalls, externCalls[sid])
		if g.Mv(sid, cNGenericParams) > 0 {
			g.Set(sid, cNMonoInstantiations, int32(len(monoMods[sid])))
		}
	}
	for sid := int32(1); sid <= n; sid++ {
		g.Set(sid, cRiskScore, riskScore(g, sid))
		if g.Mv(sid, cNTokens) > 0 {
			d := g.Mv(sid, cNDistinctOperators) + g.Mv(sid, cNDistinctOperands)
			f := 2.0
			if d > 1 {
				f = float64(d)
			}
			g.Set(sid, cHalsteadVolume,
				int32(fmul(float64(g.Mv(sid, cNOperators)+g.Mv(sid, cNOperands)), f)))
		}
		k := g.SymKind[sid-1].Str()
		if k == kFunction || k == kMethod || k == kClosure {
			sloc := float64(g.Mv(sid, cSloc))
			base := 0.05
			if sloc > 1 {
				base = sloc / 20.0
			}
			v := max(int32(fsub(fsub(171.0, fmul(0.23, float64(g.Mv(sid, cCyclomatic)))),
				fmul(16.2, base))), 0)
			g.Set(sid, cMaintainability, v)
		}
	}
}
func countsAsType(k string) bool {
	switch k {
	case "class", "struct", "interface", "trait", "enum", "union", "record",
		"protocol", "type", "impl":
		return true
	}
	return false
}

type fileAgg struct {
	id                      int32
	nSym, nFn, nType        int32
	totCyc, maxCyc, totRisk int32
}
type modAgg struct {
	nSym, nPub, nFiles, sloc int32
}

func riskScore(g *Graph, sid int32) int32 {
	m := func(c int) int32 { return g.Mv(sid, int32(c)) }
	v := m(cCyclomatic)*2 + m(cCognitive) + m(cMaxNesting)*4 +
		m(cNUnsafe)*10 + m(cNUnsafeOps)*6 + m(cNMem)*8 + m(cNFfi)*8
	if m(cNUnsafeBlocks) > 0 && m(cNSafetyComments) == 0 {
		v += m(cNUnsafeBlocks) * 8
	}
	v += m(cNTransmute)*20 + m(cNExec)*15
	v += m(cNUnwrap)*3 + m(cNPanicMacro)*4 + m(cNIndexExpr)*2
	v += m(cNLockAcrossAwait)*25 + m(cNBlockingInAsync)*20
	v += m(cNCloneInLoop)*6 + m(cAllocInLoop)*4 + m(cLockInLoop)*8
	v += m(cNStaticMut)*15 + m(cNRelaxedOrdering)*4
	if m(cIsUnsafeFn) == 1 && m(cHasDoc) == 0 {
		v += 12
	}
	if m(cIsRecursive) == 1 {
		v += 10
	}
	v += m(cNAllowAttrs) * 2
	return v
}
func fmul(a, b float64) float64 { return a * b }
func fsub(a, b float64) float64 { return a - b }
func fdiv(a, b float64) float64 { return a / b }

var _ = math.Abs
var _ = runtime.NumCPU
var _ = time.Now

var defaultParseWorkers = runtime.GOMAXPROCS(0) * 2
var runFns = []runFn{
	qUnsafeUnderPubAPI, qPanicFrontier, qLockHeldAcrossAwait, qBlockingIOInAsync,
	qResultThatPanics, qRCCycleRisk, qFFIRawBalance, qSafetyDocDebt,
	qSuppressionClusters, qArcMutexContention, qAtomicOrderingAudit,
	qTransmuteAndRawPointers, qDeadCode, qBlockingWorkBelowPublicAPI,
	qRuntimeBorrowPanicSurface, qCloneInLoop, qUnwrapInProd, qExpectInProd,
	qFloatEquality, qUnsafeWithoutComment, qVecNewPushInLoop, qTransmuteMisuse,
	qStaticMutUnsafe, qBlockOnAsync, qSpawnWithoutJoin, qImportCycle,
	qRelaxedOrdering, qRCRefcellMutation, qLenInLoop, qTraitBreadth,
	qMacroDensity, qImplFragmentation, qFFICrossings, qDeepModulePaths,
	qAsyncTaskHubs, qPlaceholderPanicSites, qDebugPrintResidue, qSQLStringBuild,
	qCommandBuildSurface, qHardcodedSecretCandidates, qUntrustedDeserialization,
	qZipSlipSurface, qUnsafeInLoop, qSuppressionWithoutReason,
	qRefcellAcrossAwait, qIndexingSlicingSurface, qDroppedFutures,
	qLossyCasts, qErrorSwallowingSites, qPublicAPIDocDebt, qManifestVsUsage,
	qTransitivePanicSurface, qResultUnwrappedByCaller, qMutexPoisonCascade,
	qPanicInDropImpl, qPanicInExternFn, qAwaitInLoop, qBlockingInCriticalSection,
	qSyncLockInAsyncFn, qBlockOnInAsyncContext, qOSThreadInAsync,
	qSpawnedTaskPanic, qSpawnInLoop, qSpawnJoinBalance, qChannelOpInLoop,
	qDeepAsyncCallChain, qSwallowedErrorBelowPubAPI, qExitSkippingDrop,
	qExplicitLeakSurface, qNeedlessUnsafeFn, qGratuitousUnsafeImpl,
	qMacroDefinedUnsafe, qMutualRecursion, qUncalledPubAPI,
	qGlobalMutableState, qDuplicateDependencyVersions, qNeedlesslyAsyncFn,
	qAllocationLoopUnderPubAPI, qRCInPublicSignature, qPtrArgSurface,
	qTestOnlyCallers,
}
var metricFns = []runFn{
	mGraphBlindspots, mCloneChurnPerIteration, mDynWithOneImpl, mMonoBlastRadius,
	mCfgFeatureNobodyBuilds, mAllocChurnCollectAndFormat, mDynamicDispatchCost,
	mHotMultipliers, mRiskRanked, mParseCoverage, mBoxDynOveruse, mDeepNesting,
	mTooManyParams, mScatteredConcerns, mUnsafeDensity, mAsyncBlockingRatio,
	mPanicDensity, mTraitCoupling, mAwaitRiskDensity, mErrorPropagationStyle,
	mTaskStructure, mMacroOpaqueBytes, mAPISurfaceBloat, mExternalCoupling,
}

type runFn = func(*qctx) *result

var catalogue []query
var metricsCatalogue []query

func init() {
	catalogue = make([]query, len(catalogueMeta))
	for i, e := range catalogueMeta {
		catalogue[i] = query{name: e.name, title: e.title, notes: e.notes}
	}
	for i := range catalogue {
		catalogue[i].run = func(g *Graph, mod string, lim int) *result { return runFns[i](&qctx{g: g, mod: mod}) }
	}
	metricsCatalogue = make([]query, len(metricsMeta))
	for i, e := range metricsMeta {
		metricsCatalogue[i] = query{name: e.name, title: e.title, notes: e.notes}
	}
	for i := range metricsCatalogue {
		metricsCatalogue[i].run = func(g *Graph, mod string, lim int) *result { return metricFns[i](&qctx{g: g, mod: mod}) }
	}
}

var showMetrics bool

func queries() []query {
	if showMetrics {
		return metricsCatalogue
	}
	return catalogue
}
func qUnsafeUnderPubAPI(q *qctx) *result {
	g := q.g
	w := newReachWalk(g)
	for sid := int32(1); sid <= int32(g.N()); sid++ {
		if q.mv(sid, cIsPublic) != 1 ||
			!(q.isKind(sid, kFunction) || q.isKind(sid, kMethod)) {
			continue
		}
		w.recordBest(sid, 0)
		w.each(sid, 4, func(s, d int32) { w.recordBest(s, d) })
	}
	return q.simple([]string{"name", "on_type", "hops_from_pub", "unsafe_fn",
		"blocks", "ops", "documented", "transmutes", "from_raw", "fan_in", "at"},
		func(sid int32) bool {
			d := w.minBest(sid)
			if d < 0 || sFileTest[sid] {
				return false
			}
			return q.mv(sid, cNUnsafeBlocks) > 0 || q.mv(sid, cIsUnsafeFn) == 1
		},
		func(sid int32) []cell {
			return []cell{cs(q.name(sid)), cs(q.impl(sid)),
				ci32(w.minBest(sid)), ci32(q.mv(sid, cIsUnsafeFn)),
				ci32(q.mv(sid, cNUnsafeBlocks)), ci32(q.mv(sid, cNUnsafeOps)),
				ci32(q.mv(sid, cNSafetyComments)), ci32(q.mv(sid, cNTransmute)),
				ci32(q.mv(sid, cNFromRaw)), ci32(q.mv(sid, cFanIn)),
				cs(q.at(sid))}
		},
		func(a, b *rowRec) bool {
			x, y := a.c[4].i-a.c[6].i, b.c[4].i-b.c[6].i
			if x != y {
				return x > y
			}
			if a.c[2].i != b.c[2].i {
				return a.c[2].i < b.c[2].i
			}
			if a.c[5].i != b.c[5].i {
				return a.c[5].i > b.c[5].i
			}
			return a.id < b.id
		})
}
func qPanicFrontier(q *qctx) *result {
	return q.simple([]string{"name", "on_type", "pub_", "unwrap_", "expect_",
		"panic_macro", "index_", "slices", "unchecked_arith", "refcell_borrow",
		"spawns", "fan_in", "return_type", "blast", "at"},
		func(sid int32) bool {
			if q.mv(sid, cIsPublic) != 1 && q.mv(sid, cNSpawn) == 0 {
				return false
			}
			if q.mv(sid, cNUnwrap)+q.mv(sid, cNExpect)+q.mv(sid, cNPanicMacro)+
				q.mv(sid, cNIndexExpr)+q.mv(sid, cNSliceRange)+
				q.mv(sid, cNBorrowCalls) == 0 {
				return false
			}
			return q.mv(sid, cIsTest) == 0 && !sFileTest[sid] && !sFileGen[sid]
		},
		func(sid int32) []cell {
			blast := (q.mv(sid, cNUnwrap) + q.mv(sid, cNExpect) +
				2*q.mv(sid, cNPanicMacro) + q.mv(sid, cNIndexExpr)) *
				q.max1(q.mv(sid, cFanIn))
			return []cell{cs(q.name(sid)), cs(q.impl(sid)),
				ci32(q.mv(sid, cIsPublic)), ci32(q.mv(sid, cNUnwrap)),
				ci32(q.mv(sid, cNExpect)), ci32(q.mv(sid, cNPanicMacro)),
				ci32(q.mv(sid, cNIndexExpr)), ci32(q.mv(sid, cNSliceRange)),
				ci32(q.mv(sid, cNArithUnchecked)), ci32(q.mv(sid, cNBorrowCalls)),
				ci32(q.mv(sid, cNSpawn)), ci32(q.mv(sid, cFanIn)),
				cs(q.g.SymRet[sid-1].Str()), ci(int64(blast)), cs(q.at(sid))}
		},
		func(a, b *rowRec) bool {
			if a.c[13].i != b.c[13].i {
				return a.c[13].i > b.c[13].i
			}
			if a.c[5].i != b.c[5].i {
				return a.c[5].i > b.c[5].i
			}
			return a.id < b.id
		})
}

type lockAwaitGrp struct {
	hops, points, guards, drops, inLoop, maxDepth, minLine int32
	names                                                  []string
}

func qLockHeldAcrossAwait(q *qctx) *result {
	g := q.g
	type key struct{ a, b int32 }
	groups := map[key]*lockAwaitGrp{}
	var keys []key
	w := newReachWalk(g)
	w.includeSelf = true
	for sid := int32(1); sid <= int32(g.N()); sid++ {
		if q.mv(sid, cNLockAcquire) == 0 {
			continue
		}
		w.each(sid, 3, func(s, d int32) {
			if sFileTest[s] || !q.modOK(s) {
				return
			}
			k := key{sid, s}
			p, ok := groups[k]
			if !ok {
				p = &lockAwaitGrp{hops: d, minLine: 1 << 30}
				groups[k] = p
				keys = append(keys, k)
			}
			for _, ai := range asyncBySym[s] {
				a := &g.AsyncPoints[ai]
				p.points++
				p.guards += a.NGuardsLive
				p.drops += a.GuardDropped
				p.inLoop += a.InLoop
				if a.LoopDepth > p.maxDepth {
					p.maxDepth = a.LoopDepth
				}
				if a.Guards() != "" {
					p.names = append(p.names, a.Guards())
				}
				if a.Line < p.minLine {
					p.minLine = a.Line
				}
			}
		})
	}
	r := &result{cols: []string{"takes_lock", "awaits_in", "hops",
		"await_points", "guards_live", "explicit_drops", "in_loop", "depth",
		"locks", "async_", "guard_names", "at"}}
	var rs []rowRec
	for _, k := range keys {
		p := groups[k]
		locks := q.mv(k.a, cNLockAcquire)
		if !(p.guards > 0 || (p.hops > 0 && locks > 0 && p.points > 0)) {
			continue
		}
		rs = append(rs, rowRec{id: k.a, c: []cell{
			cs(q.name(k.a)), cs(q.name(k.b)), ci32(p.hops), ci32(p.points),
			ci32(p.guards), ci32(p.drops), ci32(p.inLoop), ci32(p.maxDepth),
			ci32(locks), ci32(q.mv(k.b, cIsAsyncFn)),
			groupConcatNull(p.names),
			cs(sFilePath[k.b] + ":" + itoa(int(p.minLine)))}})
	}
	sortRows(rs, func(a, b *rowRec) bool {
		if a.c[4].i != b.c[4].i {
			return a.c[4].i > b.c[4].i
		}
		if a.c[6].i != b.c[6].i {
			return a.c[6].i > b.c[6].i
		}
		if a.c[2].i != b.c[2].i {
			return a.c[2].i < b.c[2].i
		}
		return a.id < b.id
	})
	fill(r, rs)
	return r
}

type asyncGrp struct {
	hops, blocking, inLoop, crossed, awaits, io int32
}

func qBlockingIOInAsync(q *qctx) *result {
	g := q.g
	type key struct{ a, b int32 }
	groups := map[key]*asyncGrp{}
	var keys []key
	w := newReachWalk(g)
	w.includeSelf = true
	for sid := int32(1); sid <= int32(g.N()); sid++ {
		if q.mv(sid, cIsAsyncFn) != 1 {
			continue
		}
		hasSB := q.mv(sid, cNSpawnBlocking) > 0
		w.each(sid, 4, func(s, d int32) {
			if sFileTest[s] || !q.modOK(s) {
				return
			}
			k := key{sid, s}
			p, ok := groups[k]
			if !ok {
				p = &asyncGrp{hops: d}
				groups[k] = p
				keys = append(keys, k)
			}
			if hasSB || q.mv(s, cNSpawnBlocking) > 0 {
				p.crossed = 1
			}
			if d < p.hops {
				p.hops = d
			}
			setMax(&p.blocking, q.mv(s, cNBlockingIO))
			setMax(&p.inLoop, q.mv(s, cIOInLoop))
			setMax(&p.awaits, q.mv(s, cNAwait))
			setMax(&p.io, q.mv(s, cNIO))
		})
	}
	r := &result{cols: []string{"async_fn", "blocks_in", "hops",
		"blocking_calls", "in_loop", "crosses_spawn_blocking", "awaits",
		"async_fan_in", "io_hazards", "at"}}
	var rs []rowRec
	for _, k := range keys {
		p := groups[k]
		if p.blocking == 0 || p.crossed == 1 {
			continue
		}
		rs = append(rs, rowRec{id: k.a, c: []cell{
			cs(q.name(k.a)), cs(q.name(k.b)), ci32(p.hops), ci32(p.blocking),
			ci32(p.inLoop), ci32(p.crossed), ci32(p.awaits),
			ci32(q.mv(k.a, cFanIn)), ci32(p.io), cs(q.at(k.b))}})
	}
	sortRows(rs, func(a, b *rowRec) bool {
		if a.c[3].i != b.c[3].i {
			return a.c[3].i > b.c[3].i
		}
		if a.c[2].i != b.c[2].i {
			return a.c[2].i < b.c[2].i
		}
		return a.id < b.id
	})
	fill(r, rs)
	return r
}
func qResultThatPanics(q *qctx) *result {
	return q.simple([]string{"name", "on_type", "pub_", "return_type",
		"unwrap_", "expect_", "panics", "index_", "question_marks",
		"catch_unwind", "fan_in", "cyclo", "pct_panic", "at"},
		func(sid int32) bool {
			rt := q.g.SymRet[sid-1].Str()
			if !likeSubstr(rt, "Result<") && !likeSubstr(rt, "Option<") {
				return false
			}
			return q.mv(sid, cNUnwrap)+q.mv(sid, cNExpect)+
				q.mv(sid, cNPanicMacro) > 0 &&
				q.mv(sid, cIsTest) == 0 && !sFileTest[sid]
		},
		func(sid int32) []cell {
			p := q.mv(sid, cNUnwrap) + q.mv(sid, cNExpect) + q.mv(sid, cNPanicMacro)
			pct := int32(0)
			if den := p + q.mv(sid, cNQuestionMark); den != 0 {
				pct = sqliteCastInt(100.0 * float64(p) / float64(den))
			}
			return []cell{cs(q.name(sid)), cs(q.impl(sid)),
				ci32(q.mv(sid, cIsPublic)), cs(q.g.SymRet[sid-1].Str()),
				ci32(q.mv(sid, cNUnwrap)), ci32(q.mv(sid, cNExpect)),
				ci32(q.mv(sid, cNPanicMacro)), ci32(q.mv(sid, cNIndexExpr)),
				ci32(q.mv(sid, cNQuestionMark)), ci32(q.mv(sid, cNControl)),
				ci32(q.mv(sid, cFanIn)), ci32(q.mv(sid, cCyclomatic)),
				ci32(pct), cs(q.at(sid))}
		},
		func(a, b *rowRec) bool {
			if a.c[12].i != b.c[12].i {
				return a.c[12].i > b.c[12].i
			}
			if a.c[10].i != b.c[10].i {
				return a.c[10].i > b.c[10].i
			}
			return a.id < b.id
		})
}
func qRCCycleRisk(q *qctx) *result {
	g := q.g
	type agg struct {
		syms, types                         int32
		rc, arc, weak, borrow, lock, clones int32
	}
	aggs := map[int32]*agg{}
	var order []int32
	for sid := int32(1); sid <= int32(g.N()); sid++ {
		if sFileTest[sid] {
			continue
		}
		m := g.SymModule[sid-1]
		if m < 0 {
			continue
		}
		a, ok := aggs[m]
		if !ok {
			a = &agg{}
			aggs[m] = a
			order = append(order, m)
		}
		a.syms++
		if q.isKind(sid, kStruct, kEnum) {
			a.types++
		}
		a.rc += q.mv(sid, cNRcRefcell)
		a.arc += q.mv(sid, cNArcMutex)
		a.weak += q.mv(sid, cNWeakRefs)
		a.borrow += q.mv(sid, cNBorrowCalls)
		a.lock += q.mv(sid, cNLockAcquire)
		a.clones += q.mv(sid, cNClone)
	}
	r := &result{cols: []string{"module_", "symbols_", "rc_refcell",
		"arc_mutex", "weak_refs", "refcell_borrows", "lock_calls", "clones",
		"types_"}}
	var rs []rowRec
	for _, m := range order {
		if !likeMatch(q.mod, g.modName(m)) {
			continue
		}
		a := aggs[m]
		if a.rc+a.arc == 0 || a.weak != 0 {
			continue
		}
		rs = append(rs, rowRec{id: m, c: []cell{cs(g.modName(m)), ci32(a.syms),
			ci32(a.rc), ci32(a.arc), ci32(a.weak), ci32(a.borrow), ci32(a.lock),
			ci32(a.clones), ci32(a.types)}})
	}
	sortRows(rs, func(a, b *rowRec) bool {
		if a.c[2].i != b.c[2].i {
			return a.c[2].i > b.c[2].i
		}
		if a.c[3].i != b.c[3].i {
			return a.c[3].i > b.c[3].i
		}
		return a.id < b.id
	})
	fill(r, rs)
	return r
}
func qFFIRawBalance(q *qctx) *result {
	g := q.g
	type agg struct {
		into, from, raw, trans, ext, ffi, stat, unsafeImpls int32
		promised                                            []string
	}
	aggs := map[int32]*agg{}
	var order []int32
	get := func(m int32) *agg {
		a, ok := aggs[m]
		if !ok {
			a = &agg{}
			aggs[m] = a
			order = append(order, m)
		}
		return a
	}
	for sid := int32(1); sid <= int32(g.N()); sid++ {
		if sFileTest[sid] {
			continue
		}
		m := g.SymModule[sid-1]
		if m < 0 {
			continue
		}
		a := get(m)
		a.into += q.mv(sid, cNIntoRaw)
		a.from += q.mv(sid, cNFromRaw)
		a.raw += q.mv(sid, cNRawPtr)
		a.trans += q.mv(sid, cNTransmute)
		a.ext += q.mv(sid, cIsExternFn)
		a.ffi += q.mv(sid, cNFfi)
		a.stat += q.mv(sid, cNStaticMut)
	}
	for i := range g.Impls {
		im := &g.Impls[i]
		if im.IsUnsafe != 1 || im.SymID < 1 || int(im.SymID) > g.N() {
			continue
		}
		m := g.SymModule[im.SymID-1]
		if m < 0 {
			continue
		}
		if _, ok := aggs[m]; !ok {
			continue
		}
		a := get(m)
		a.unsafeImpls++
		a.promised = append(a.promised, im.TraitName())
	}
	r := &result{cols: []string{"module_", "into_raw", "from_raw",
		"imbalance", "raw_ptr_types", "transmutes", "extern_fns", "ffi_hazards",
		"static_mut", "unsafe_impls", "promised"}}
	var rs []rowRec
	for _, m := range order {
		if !likeMatch(q.mod, g.modName(m)) {
			continue
		}
		a := aggs[m]
		if a.into+a.from+a.unsafeImpls+a.stat == 0 {
			continue
		}
		rs = append(rs, rowRec{id: m, c: []cell{cs(g.modName(m)), ci32(a.into),
			ci32(a.from), ci32(a.into - a.from), ci32(a.raw), ci32(a.trans),
			ci32(a.ext), ci32(a.ffi), ci32(a.stat), ci32(a.unsafeImpls),
			groupConcatNull(a.promised)}})
	}
	sortRows(rs, func(a, b *rowRec) bool {
		if abs32(a.c[3].i) != abs32(b.c[3].i) {
			return abs32(a.c[3].i) > abs32(b.c[3].i)
		}
		if a.c[9].i != b.c[9].i {
			return a.c[9].i > b.c[9].i
		}
		return a.id < b.id
	})
	fill(r, rs)
	return r
}
func qSafetyDocDebt(q *qctx) *result {
	g := q.g
	r := &result{cols: []string{"in_fn", "on_type", "line", "n_ops", "derefs",
		"transmutes", "from_raw", "calls_", "block_sloc", "in_unsafe_fn",
		"in_loop", "pub_", "fn_documented", "fan_in", "at"}}
	var rs []rowRec
	for i := range g.UnsafeBlks {
		u := &g.UnsafeBlks[i]
		sid := u.SymID
		if u.HasSafety != 0 || sFileTest[sid] || !q.modOK(sid) {
			continue
		}
		rs = append(rs, rowRec{id: sid, c: []cell{
			cs(q.name(sid)), cs(q.impl(sid)), ci32(u.Line), ci32(u.NOps),
			ci32(u.NDeref), ci32(u.NTransmute), ci32(u.NFromRaw),
			ci32(u.NRawCalls), ci32(u.Sloc), ci32(u.InUnsafeFn), ci32(u.InLoop),
			ci32(q.mv(sid, cIsPublic)), ci32(q.mv(sid, cHasDoc)),
			ci32(q.mv(sid, cFanIn)),
			cs(sFilePath[sid] + ":" + itoa(int(u.Line)))}})
	}
	sortRows(rs, func(a, b *rowRec) bool {
		if a.c[3].i != b.c[3].i {
			return a.c[3].i > b.c[3].i
		}
		if a.c[13].i != b.c[13].i {
			return a.c[13].i > b.c[13].i
		}
		return a.id < b.id
	})
	fill(r, rs)
	return r
}
func qSuppressionClusters(q *qctx) *result {
	g := q.g
	r := &result{cols: []string{"name", "on_type", "allows", "expects",
		"suppressed", "panics_", "unsafe_blocks", "clones", "index_",
		"hazards", "pub_", "fan_in", "risk", "at"}}
	var rs []rowRec
	for sid := int32(1); sid <= int32(g.N()); sid++ {
		if sFileTest[sid] || sFileGen[sid] || !q.modOK(sid) {
			continue
		}
		var names []string
		for _, ai := range attrBySym[sid] {
			a := &g.Attributes[ai]
			if a.Name() == "allow" || a.Name() == "expect" {
				names = append(names, clip(a.Args(), 34))
			}
		}
		if len(names) == 0 {
			continue
		}
		haz := q.mv(sid, cNHazards)
		ub := q.mv(sid, cNUnsafeBlocks)
		if haz == 0 && ub == 0 {
			continue
		}
		rs = append(rs, rowRec{id: sid, c: []cell{
			cs(q.name(sid)), cs(q.impl(sid)), ci32(q.mv(sid, cNAllowAttrs)),
			ci32(q.mv(sid, cNExpectAttrs)), cs(groupConcatDistinct(names)),
			ci32(q.mv(sid, cNUnwrap) + q.mv(sid, cNExpect)), ci32(ub),
			ci32(q.mv(sid, cNClone)), ci32(q.mv(sid, cNIndexExpr)), ci32(haz),
			ci32(q.mv(sid, cIsPublic)), ci32(q.mv(sid, cFanIn)),
			ci32(q.mv(sid, cRiskScore)), cs(q.at(sid))}})
	}
	sortRows(rs, func(a, b *rowRec) bool {
		if a.c[12].i != b.c[12].i {
			return a.c[12].i > b.c[12].i
		}
		if a.c[2].i != b.c[2].i {
			return a.c[2].i > b.c[2].i
		}
		return a.id < b.id
	})
	fill(r, rs)
	return r
}
func qArcMutexContention(q *qctx) *result {
	return q.simple([]string{"name", "impl_", "arc_mutex", "locks", "rc_refcell",
		"fan_out", "depth", "awaits", "at"},
		func(sid int32) bool { return q.mv(sid, cNArcMutex) > 0 && !sFileTest[sid] },
		func(sid int32) []cell {
			return []cell{cs(q.name(sid)), cs(q.impl(sid)),
				ci32(q.mv(sid, cNArcMutex)), ci32(q.mv(sid, cNLockAcquire)),
				ci32(q.mv(sid, cNRcRefcell)), ci32(q.mv(sid, cFanOut)),
				ci32(q.mv(sid, cMaxLoopDepth)), ci32(q.mv(sid, cNAwait)),
				cs(q.at(sid))}
		},
		func(a, b *rowRec) bool {
			if a.c[2].i != b.c[2].i {
				return a.c[2].i > b.c[2].i
			}
			if a.c[3].i != b.c[3].i {
				return a.c[3].i > b.c[3].i
			}
			if a.c[5].i != b.c[5].i {
				return a.c[5].i > b.c[5].i
			}
			return a.id < b.id
		})
}
func qAtomicOrderingAudit(q *qctx) *result {
	return q.simple([]string{"name", "impl_", "atomics", "relaxed", "seqcst",
		"spawns", "unsafe_fn", "fan_in", "at"},
		func(sid int32) bool { return q.mv(sid, cNAtomicOps) > 0 && !sFileTest[sid] },
		func(sid int32) []cell {
			return []cell{cs(q.name(sid)), cs(q.impl(sid)),
				ci32(q.mv(sid, cNAtomicOps)), ci32(q.mv(sid, cNRelaxedOrdering)),
				ci32(q.mv(sid, cNSeqcstOrdering)), ci32(q.mv(sid, cNSpawn)),
				ci32(q.mv(sid, cIsUnsafeFn)), ci32(q.mv(sid, cFanIn)),
				cs(q.at(sid))}
		},
		func(a, b *rowRec) bool {
			if a.c[3].i != b.c[3].i {
				return a.c[3].i > b.c[3].i
			}
			if a.c[2].i != b.c[2].i {
				return a.c[2].i > b.c[2].i
			}
			return a.id < b.id
		})
}
func qTransmuteAndRawPointers(q *qctx) *result {
	return q.simple([]string{"name", "impl_", "transmutes", "raw_ptrs",
		"static_mut", "from_raw", "into_raw", "unsafe_blocks", "safety_docs",
		"extern_", "at"},
		func(sid int32) bool {
			return (q.mv(sid, cNTransmute) > 0 || q.mv(sid, cNStaticMut) > 0 ||
				q.mv(sid, cNRawPtr) > 0) && !sFileTest[sid]
		},
		func(sid int32) []cell {
			return []cell{cs(q.name(sid)), cs(q.impl(sid)),
				ci32(q.mv(sid, cNTransmute)), ci32(q.mv(sid, cNRawPtr)),
				ci32(q.mv(sid, cNStaticMut)), ci32(q.mv(sid, cNFromRaw)),
				ci32(q.mv(sid, cNIntoRaw)), ci32(q.mv(sid, cNUnsafeBlocks)),
				ci32(q.mv(sid, cNSafetyComments)), ci32(q.mv(sid, cIsExternFn)),
				cs(q.at(sid))}
		},
		func(a, b *rowRec) bool {
			if a.c[2].i != b.c[2].i {
				return a.c[2].i > b.c[2].i
			}
			if a.c[4].i != b.c[4].i {
				return a.c[4].i > b.c[4].i
			}
			x, y := a.c[7].i-a.c[8].i, b.c[7].i-b.c[8].i
			if x != y {
				return x > y
			}
			return a.id < b.id
		})
}
func qDeadCode(q *qctx) *result {
	return q.simple([]string{"name", "kind", "sloc", "cyclo", "ext_calls", "at"},
		func(sid int32) bool {
			if !q.isKind(sid, kFunction, kMethod, kClosure) {
				return false
			}
			n := q.name(sid)
			if n == "(anonymous)" || n == "<module>" {
				return false
			}
			return q.mv(sid, cFanIn) == 0 && q.mv(sid, cIsPublic) == 0 &&
				q.mv(sid, cIsTest) == 0 && q.mv(sid, cIsEntrypoint) == 0 &&
				q.mv(sid, cIsOverride) == 0 && q.mv(sid, cIsAbstract) == 0 &&
				!sFileTest[sid] && !sFileGen[sid]
		},
		func(sid int32) []cell {
			return []cell{cs(q.name(sid)), cs(q.g.SymKind[sid-1].Str()),
				ci32(q.mv(sid, cSloc)), ci32(q.mv(sid, cCyclomatic)),
				ci32(q.mv(sid, cNExternalCalls)), cs(q.at(sid))}
		},
		func(a, b *rowRec) bool {
			if a.c[2].i != b.c[2].i {
				return a.c[2].i > b.c[2].i
			}
			fa, fb := q.g.SymFile[a.id-1], q.g.SymFile[b.id-1]
			if fa != fb {
				return fa < fb
			}
			ka, kb := q.g.SymKind[a.id-1].Str(), q.g.SymKind[b.id-1].Str()
			if ka != kb {
				return ka < kb
			}
			return a.id < b.id
		})
}
func qBlockingWorkBelowPublicAPI(q *qctx) *result {
	ts := q.reachPairs(4,
		func(sid int32) bool { return q.mv(sid, cIsPublic) == 1 && !sFileTest[sid] },
		func(root, sym, hops int32) bool {
			return hops > 0 && !sFileTest[sym] && q.modOK(sym) &&
				(q.mv(sym, cNLockInLoop) > 0 || q.mv(sym, cNIOInLoop) > 0 ||
					q.mv(sym, cNBlockOn) > 0 || q.mv(sym, cNThreadSleep) > 0)
		})
	return q.fromReach([]string{"name", "reached_from", "hops", "lock_in_loop",
		"io_in_loop", "block_on", "sleeps", "push_in_loop", "is_async",
		"fan_in", "at"}, ts,
		func(t tri) []cell {
			return []cell{cs(q.name(t.sym)), cs(q.name(t.root)), ci32(t.hops),
				ci32(q.mv(t.sym, cNLockInLoop)), ci32(q.mv(t.sym, cNIOInLoop)),
				ci32(q.mv(t.sym, cNBlockOn)), ci32(q.mv(t.sym, cNThreadSleep)),
				ci32(q.mv(t.sym, cNPushInLoop)), ci32(q.mv(t.sym, cIsAsyncFn)),
				ci32(q.mv(t.sym, cFanIn)), cs(q.at(t.sym))}
		},
		func(a, b *rowRec) bool {
			if a.c[3].i != b.c[3].i {
				return a.c[3].i > b.c[3].i
			}
			if a.c[4].i != b.c[4].i {
				return a.c[4].i > b.c[4].i
			}
			if a.c[2].i != b.c[2].i {
				return a.c[2].i < b.c[2].i
			}
			if a.c[9].i != b.c[9].i {
				return a.c[9].i > b.c[9].i
			}
			if a.id != b.id {
				return a.id < b.id
			}
			return a.x < b.x
		})
}
func qRuntimeBorrowPanicSurface(q *qctx) *result {
	ts := q.reachPairs(4,
		func(sid int32) bool {
			return q.mv(sid, cIsPublic) == 1 || q.mv(sid, cIsEntrypoint) == 1
		},
		func(root, sym, hops int32) bool {
			return hops > 0 && q.mv(sym, cNBorrowMut) > 0 && !sFileTest[sym] &&
				q.modOK(sym)
		})
	return q.fromReach([]string{"name", "reached_from", "hops", "borrow_muts",
		"unwraps", "to_owned_in_loop", "push_in_loop", "lock_in_loop", "fan_in",
		"at"}, ts,
		func(t tri) []cell {
			return []cell{cs(q.name(t.sym)), cs(q.name(t.root)), ci32(t.hops),
				ci32(q.mv(t.sym, cNBorrowMut)), ci32(q.mv(t.sym, cNUnwrapErr)),
				ci32(q.mv(t.sym, cNToOwnedInLoop)), ci32(q.mv(t.sym, cNPushInLoop)),
				ci32(q.mv(t.sym, cNLockInLoop)), ci32(q.mv(t.sym, cFanIn)),
				cs(q.at(t.sym))}
		},
		func(a, b *rowRec) bool {
			if a.c[3].i != b.c[3].i {
				return a.c[3].i > b.c[3].i
			}
			if a.c[2].i != b.c[2].i {
				return a.c[2].i < b.c[2].i
			}
			if a.c[8].i != b.c[8].i {
				return a.c[8].i > b.c[8].i
			}
			if a.id != b.id {
				return a.id < b.id
			}
			return a.x < b.x
		})
}
func qCloneInLoop(q *qctx) *result {
	return q.simple([]string{"name", "clones_in_loop", "loops",
		"pushes_in_loop", "cyclo", "fan_in", "at"},
		func(sid int32) bool { return q.mv(sid, cNToOwnedInLoop) > 0 && !sFileTest[sid] },
		func(sid int32) []cell {
			return []cell{cs(q.name(sid)), ci32(q.mv(sid, cNToOwnedInLoop)),
				ci32(q.mv(sid, cNLoops)), ci32(q.mv(sid, cNPushInLoop)),
				ci32(q.mv(sid, cCyclomatic)), ci32(q.mv(sid, cFanIn)),
				cs(q.at(sid))}
		},
		func(a, b *rowRec) bool {
			if a.c[1].i != b.c[1].i {
				return a.c[1].i > b.c[1].i
			}
			if a.c[2].i != b.c[2].i {
				return a.c[2].i > b.c[2].i
			}
			return a.id < b.id
		})
}
func qUnwrapInProd(q *qctx) *result {
	return q.simple([]string{"name", "unwraps", "unchecked_calls", "fan_in",
		"cyclo", "at"},
		func(sid int32) bool { return q.mv(sid, cNUnwrapErr) > 0 && !sFileTest[sid] },
		func(sid int32) []cell {
			return []cell{cs(q.name(sid)), ci32(q.mv(sid, cNUnwrapErr)),
				ci32(q.mv(sid, cNUncheckedCall)), ci32(q.mv(sid, cFanIn)),
				ci32(q.mv(sid, cCyclomatic)), cs(q.at(sid))}
		},
		func(a, b *rowRec) bool {
			if a.c[3].i != b.c[3].i {
				return a.c[3].i > b.c[3].i
			}
			if a.c[1].i != b.c[1].i {
				return a.c[1].i > b.c[1].i
			}
			return a.id < b.id
		})
}
func qExpectInProd(q *qctx) *result {
	return q.simple([]string{"name", "expects_and_unwraps", "fan_in", "cyclo",
		"at"},
		func(sid int32) bool {
			return q.mv(sid, cNUnwrapErr) > 0 && q.mv(sid, cFanIn) > 3 &&
				!sFileTest[sid]
		},
		func(sid int32) []cell {
			return []cell{cs(q.name(sid)), ci32(q.mv(sid, cNUnwrapErr)),
				ci32(q.mv(sid, cFanIn)), ci32(q.mv(sid, cCyclomatic)),
				cs(q.at(sid))}
		},
		func(a, b *rowRec) bool {
			if a.c[2].i != b.c[2].i {
				return a.c[2].i > b.c[2].i
			}
			if a.c[1].i != b.c[1].i {
				return a.c[1].i > b.c[1].i
			}
			return a.id < b.id
		})
}
func qFloatEquality(q *qctx) *result {
	return q.simple([]string{"name", "comparisons", "unchecked_arith", "cyclo",
		"fan_in", "at"},
		func(sid int32) bool { return q.mv(sid, cNCmp) > 3 && !sFileTest[sid] },
		func(sid int32) []cell {
			return []cell{cs(q.name(sid)), ci32(q.mv(sid, cNCmp)),
				ci32(q.mv(sid, cNArithUnchecked)), ci32(q.mv(sid, cCyclomatic)),
				ci32(q.mv(sid, cFanIn)), cs(q.at(sid))}
		},
		func(a, b *rowRec) bool {
			if a.c[1].i != b.c[1].i {
				return a.c[1].i > b.c[1].i
			}
			if a.c[4].i != b.c[4].i {
				return a.c[4].i > b.c[4].i
			}
			return a.id < b.id
		})
}
func qUnsafeWithoutComment(q *qctx) *result {
	return q.simple([]string{"name", "uncommented_unsafe", "total_unsafe",
		"n_raw_ptr", "n_transmute", "fan_in", "cyclo", "at"},
		func(sid int32) bool {
			idx := unsafeBySym[sid]
			if len(idx) == 0 || sFileTest[sid] {
				return false
			}
			for _, j := range idx {
				if g0.UnsafeBlks[j].HasSafety == 0 {
					return true
				}
			}
			return false
		},
		func(sid int32) []cell {
			idx := unsafeBySym[sid]
			nUn, tot := int32(0), int32(0)
			for _, j := range idx {
				tot++
				if g0.UnsafeBlks[j].HasSafety == 0 {
					nUn++
				}
			}
			return []cell{cs(q.name(sid)), ci32(nUn), ci32(tot),
				ci32(q.mv(sid, cNRawPtr)), ci32(q.mv(sid, cNTransmute)),
				ci32(q.mv(sid, cFanIn)), ci32(q.mv(sid, cCyclomatic)),
				cs(q.at(sid))}
		},
		func(a, b *rowRec) bool {
			if a.c[1].i != b.c[1].i {
				return a.c[1].i > b.c[1].i
			}
			if a.c[5].i != b.c[5].i {
				return a.c[5].i > b.c[5].i
			}
			return a.id < b.id
		})
}
func qVecNewPushInLoop(q *qctx) *result {
	return q.simple([]string{"name", "pushes_in_loop", "loops",
		"clones_in_loop", "cyclo", "fan_in", "at"},
		func(sid int32) bool { return q.mv(sid, cNPushInLoop) > 0 && !sFileTest[sid] },
		func(sid int32) []cell {
			return []cell{cs(q.name(sid)), ci32(q.mv(sid, cNPushInLoop)),
				ci32(q.mv(sid, cNLoops)), ci32(q.mv(sid, cNToOwnedInLoop)),
				ci32(q.mv(sid, cCyclomatic)), ci32(q.mv(sid, cFanIn)),
				cs(q.at(sid))}
		},
		func(a, b *rowRec) bool {
			if a.c[1].i != b.c[1].i {
				return a.c[1].i > b.c[1].i
			}
			if a.c[2].i != b.c[2].i {
				return a.c[2].i > b.c[2].i
			}
			return a.id < b.id
		})
}
func qTransmuteMisuse(q *qctx) *result {
	return q.simple([]string{"name", "transmutes", "from_raw", "into_raw",
		"raw_ptrs", "fan_in", "cyclo", "at"},
		func(sid int32) bool { return q.mv(sid, cNTransmute) > 0 && !sFileTest[sid] },
		func(sid int32) []cell {
			return []cell{cs(q.name(sid)), ci32(q.mv(sid, cNTransmute)),
				ci32(q.mv(sid, cNFromRaw)), ci32(q.mv(sid, cNIntoRaw)),
				ci32(q.mv(sid, cNRawPtr)), ci32(q.mv(sid, cFanIn)),
				ci32(q.mv(sid, cCyclomatic)), cs(q.at(sid))}
		},
		func(a, b *rowRec) bool {
			if a.c[5].i != b.c[5].i {
				return a.c[5].i > b.c[5].i
			}
			if a.c[1].i != b.c[1].i {
				return a.c[1].i > b.c[1].i
			}
			return a.id < b.id
		})
}
func qStaticMutUnsafe(q *qctx) *result {
	return q.simple([]string{"name", "static_muts", "atomic_ops", "arc_mutexes",
		"fan_in", "cyclo", "at"},
		func(sid int32) bool { return q.mv(sid, cNStaticMut) > 0 && !sFileTest[sid] },
		func(sid int32) []cell {
			return []cell{cs(q.name(sid)), ci32(q.mv(sid, cNStaticMut)),
				ci32(q.mv(sid, cNAtomicOps)), ci32(q.mv(sid, cNArcMutex)),
				ci32(q.mv(sid, cFanIn)), ci32(q.mv(sid, cCyclomatic)),
				cs(q.at(sid))}
		},
		func(a, b *rowRec) bool {
			if a.c[4].i != b.c[4].i {
				return a.c[4].i > b.c[4].i
			}
			if a.c[1].i != b.c[1].i {
				return a.c[1].i > b.c[1].i
			}
			return a.id < b.id
		})
}
func qBlockOnAsync(q *qctx) *result {
	return q.simple([]string{"name", "block_ons", "is_async_fn", "awaits",
		"spawn_blockings", "fan_in", "cyclo", "at"},
		func(sid int32) bool { return q.mv(sid, cNBlockOn) > 0 && !sFileTest[sid] },
		func(sid int32) []cell {
			return []cell{cs(q.name(sid)), ci32(q.mv(sid, cNBlockOn)),
				ci32(q.mv(sid, cIsAsyncFn)), ci32(q.mv(sid, cNAwait)),
				ci32(q.mv(sid, cNSpawnBlocking)), ci32(q.mv(sid, cFanIn)),
				ci32(q.mv(sid, cCyclomatic)), cs(q.at(sid))}
		},
		func(a, b *rowRec) bool {
			if a.c[5].i != b.c[5].i {
				return a.c[5].i > b.c[5].i
			}
			if a.c[1].i != b.c[1].i {
				return a.c[1].i > b.c[1].i
			}
			return a.id < b.id
		})
}
func qSpawnWithoutJoin(q *qctx) *result {
	return q.simple([]string{"name", "spawns", "spawn_blockings", "is_async_fn",
		"fan_in", "at"},
		func(sid int32) bool { return q.mv(sid, cNSpawn) > 0 && !sFileTest[sid] },
		func(sid int32) []cell {
			return []cell{cs(q.name(sid)), ci32(q.mv(sid, cNSpawn)),
				ci32(q.mv(sid, cNSpawnBlocking)), ci32(q.mv(sid, cIsAsyncFn)),
				ci32(q.mv(sid, cFanIn)), cs(q.at(sid))}
		},
		func(a, b *rowRec) bool {
			if a.c[4].i != b.c[4].i {
				return a.c[4].i > b.c[4].i
			}
			if a.c[1].i != b.c[1].i {
				return a.c[1].i > b.c[1].i
			}
			return a.id < b.id
		})
}
func qImportCycle(q *qctx) *result {
	g := q.g
	adj := map[int32][]int32{}
	for i := range g.Imports {
		im := &g.Imports[i]
		if im.TargetID > 0 && im.IsExternal == 0 {
			adj[im.FileID] = append(adj[im.FileID], im.TargetID)
		}
	}
	var rs []rowRec
	for i := range g.Files {
		f := &g.Files[i]
		if f.IsTest == 1 {
			continue
		}
		type key struct{ start, cur int32 }
		dist := map[key]int32{}
		var keys []key
		queue := []int32{f.ID}
		dist[key{f.ID, f.ID}] = 0
		for h := 0; h < len(queue); h++ {
			cur := queue[h]
			d := dist[key{f.ID, cur}]
			if d >= 8 {
				continue
			}
			for _, n := range adj[cur] {
				k := key{f.ID, n}
				if _, ok := dist[k]; ok {
					continue
				}
				dist[k] = d + 1
				keys = append(keys, k)
				queue = append(queue, n)
			}
		}
		shortest := int32(-1)
		for _, k := range keys {
			if k.cur == f.ID && dist[k] > 0 {
				if shortest < 0 || dist[k] < shortest {
					shortest = dist[k]
				}
			}
		}
		if shortest > 0 {
			rs = append(rs, rowRec{id: f.ID, c: []cell{cs(f.Path()), ci32(shortest),
				cs(f.Path() + ":" + "0")}})
		}
	}
	sortRows(rs, func(a, b *rowRec) bool {
		if a.c[1].i != b.c[1].i {
			return a.c[1].i < b.c[1].i
		}
		return a.id < b.id
	})
	r := &result{cols: []string{"path", "shortest_cycle", "at"}}
	fill(r, rs)
	return r
}
func qRelaxedOrdering(q *qctx) *result {
	return q.simple([]string{"name", "relaxed", "seqcst", "atomic_ops", "fan_in",
		"cyclo", "at"},
		func(sid int32) bool {
			return q.mv(sid, cNRelaxedOrdering) > 0 && !sFileTest[sid]
		},
		func(sid int32) []cell {
			return []cell{cs(q.name(sid)), ci32(q.mv(sid, cNRelaxedOrdering)),
				ci32(q.mv(sid, cNSeqcstOrdering)), ci32(q.mv(sid, cNAtomicOps)),
				ci32(q.mv(sid, cFanIn)), ci32(q.mv(sid, cCyclomatic)),
				cs(q.at(sid))}
		},
		func(a, b *rowRec) bool {
			if a.c[1].i != b.c[1].i {
				return a.c[1].i > b.c[1].i
			}
			if a.c[4].i != b.c[4].i {
				return a.c[4].i > b.c[4].i
			}
			return a.id < b.id
		})
}
func qRCRefcellMutation(q *qctx) *result {
	return q.simple([]string{"name", "rc_refcells", "arc_mutexes", "weak_refs",
		"fan_in", "cyclo", "at"},
		func(sid int32) bool { return q.mv(sid, cNRcRefcell) > 0 && !sFileTest[sid] },
		func(sid int32) []cell {
			return []cell{cs(q.name(sid)), ci32(q.mv(sid, cNRcRefcell)),
				ci32(q.mv(sid, cNArcMutex)), ci32(q.mv(sid, cNWeakRefs)),
				ci32(q.mv(sid, cFanIn)), ci32(q.mv(sid, cCyclomatic)),
				cs(q.at(sid))}
		},
		func(a, b *rowRec) bool {
			if a.c[4].i != b.c[4].i {
				return a.c[4].i > b.c[4].i
			}
			if a.c[1].i != b.c[1].i {
				return a.c[1].i > b.c[1].i
			}
			return a.id < b.id
		})
}
func qLenInLoop(q *qctx) *result {
	return q.simple([]string{"name", "len_in_loop", "loops", "iter_in_loop",
		"cyclo", "fan_in", "at"},
		func(sid int32) bool { return q.mv(sid, cNLenInLoop) > 0 && !sFileTest[sid] },
		func(sid int32) []cell {
			return []cell{cs(q.name(sid)), ci32(q.mv(sid, cNLenInLoop)),
				ci32(q.mv(sid, cNLoops)), ci32(q.mv(sid, cNIterInLoop)),
				ci32(q.mv(sid, cCyclomatic)), ci32(q.mv(sid, cFanIn)),
				cs(q.at(sid))}
		},
		func(a, b *rowRec) bool {
			if a.c[1].i != b.c[1].i {
				return a.c[1].i > b.c[1].i
			}
			if a.c[2].i != b.c[2].i {
				return a.c[2].i > b.c[2].i
			}
			return a.id < b.id
		})
}
func qTraitBreadth(q *qctx) *result {
	g := q.g
	type agg struct {
		types, files, methods, unsafeM, minLine int32
		seenType, seenFile                      map[int32]bool
	}
	aggs := map[string]*agg{}
	var names []string
	for i := range g.Impls {
		im := &g.Impls[i]
		if im.TraitName() == "" {
			continue
		}
		a, ok := aggs[im.TraitName()]
		if !ok {
			a = &agg{seenType: map[int32]bool{}, seenFile: map[int32]bool{},
				minLine: 1 << 30}
			aggs[im.TraitName()] = a
			names = append(names, im.TraitName())
		}
		if !a.seenType[hashStr(im.TypeName())] {
			a.seenType[hashStr(im.TypeName())] = true
			a.types++
		}
		if !a.seenFile[im.FileID] {
			a.seenFile[im.FileID] = true
			a.files++
		}
		a.methods += im.NMethods
		a.unsafeM += im.NUnsafeMethods
		if im.Line < a.minLine {
			a.minLine = im.Line
		}
	}
	r := &result{cols: []string{"trait_", "impls", "in_files", "methods_impl",
		"unsafe_methods", "first_line"}}
	var rs []rowRec
	for _, n := range names {
		a := aggs[n]
		if a.types < 2 {
			continue
		}
		rs = append(rs, rowRec{c: []cell{cs(n), ci32(a.types), ci32(a.files),
			ci32(a.methods), ci32(a.unsafeM), ci32(a.minLine)}})
	}
	sortRows(rs, func(a, b *rowRec) bool {
		if a.c[1].i != b.c[1].i {
			return a.c[1].i > b.c[1].i
		}
		if a.c[3].i != b.c[3].i {
			return a.c[3].i > b.c[3].i
		}
		if a.c[0].s != b.c[0].s {
			return a.c[0].s < b.c[0].s
		}
		return false
	})
	fill(r, rs)
	return r
}
func qMacroDensity(q *qctx) *result {
	g := q.g
	type agg struct {
		inv, def, attr, bytes, files int32
		seen                         map[int32]bool
	}
	aggs := map[int32]*agg{}
	var order []int32
	for i := range g.Macros {
		m := &g.Macros[i]
		fid := m.FileID
		if fid < 1 || int(fid) > len(g.Files) {
			continue
		}
		mid := g.Files[fid-1].ModuleID
		if mid < 0 {
			continue
		}
		a, ok := aggs[mid]
		if !ok {
			a = &agg{seen: map[int32]bool{}}
			aggs[mid] = a
			order = append(order, mid)
		}
		switch m.Kind() {
		case "invocation":
			a.inv++
			a.bytes += m.BodyBytes
		case "definition":
			a.def++
		case "attribute":
			a.attr++
		}
		if !a.seen[fid] {
			a.seen[fid] = true
			a.files++
		}
	}
	r := &result{cols: []string{"module_", "invocations", "definitions", "attrs",
		"invocation_body_bytes", "in_files"}}
	var rs []rowRec
	for _, m := range order {
		if !likeMatch(q.mod, g.modName(m)) {
			continue
		}
		a := aggs[m]
		rs = append(rs, rowRec{id: m, c: []cell{cs(g.modName(m)), ci32(a.inv),
			ci32(a.def), ci32(a.attr), ci32(a.bytes), ci32(a.files)}})
	}
	sortRows(rs, func(a, b *rowRec) bool {
		if a.c[1].i != b.c[1].i {
			return a.c[1].i > b.c[1].i
		}
		if a.c[4].i != b.c[4].i {
			return a.c[4].i > b.c[4].i
		}
		return a.id < b.id
	})
	fill(r, rs)
	return r
}
func qImplFragmentation(q *qctx) *result {
	g := q.g
	type agg struct {
		files, impls, traitImpls, inhImpls int32
		names                              map[int32]bool
	}
	aggs := map[string]*agg{}
	var names []string
	for i := range g.Impls {
		im := &g.Impls[i]
		if im.TypeName() == "" {
			continue
		}
		a, ok := aggs[im.TypeName()]
		if !ok {
			a = &agg{names: map[int32]bool{}}
			aggs[im.TypeName()] = a
			names = append(names, im.TypeName())
		}
		if !a.names[im.FileID] {
			a.names[im.FileID] = true
			a.files++
		}
		a.impls++
		if im.TraitName() != "" {
			a.traitImpls++
		} else {
			a.inhImpls++
		}
	}
	r := &result{cols: []string{"type_", "n_files", "n_impls", "trait_impls",
		"inherent_impls", "in_files"}}
	var rs []rowRec
	for _, n := range names {
		a := aggs[n]
		if a.files < 2 {
			continue
		}
		var bases []string
		for fi := range g.Files {
			if a.names[g.Files[fi].ID] {
				bases = append(bases, g.Files[fi].Base())
			}
		}
		rs = append(rs, rowRec{c: []cell{cs(n), ci32(a.files), ci32(a.impls),
			ci32(a.traitImpls), ci32(a.inhImpls), cs(groupConcatDistinct(bases))}})
	}
	sortRows(rs, func(a, b *rowRec) bool {
		if a.c[1].i != b.c[1].i {
			return a.c[1].i > b.c[1].i
		}
		if a.c[2].i != b.c[2].i {
			return a.c[2].i > b.c[2].i
		}
		if a.c[0].s != b.c[0].s {
			return a.c[0].s < b.c[0].s
		}
		return false
	})
	fill(r, rs)
	return r
}
func qFFICrossings(q *qctx) *result {
	return q.simple([]string{"name", "ffi_calls", "ffi_hazards", "unsafe_blocks",
		"unsafe_fn", "fan_in", "sloc", "at"},
		func(sid int32) bool { return q.mv(sid, cNExternCalls) > 0 && !sFileTest[sid] },
		func(sid int32) []cell {
			return []cell{cs(q.name(sid)), ci32(q.mv(sid, cNExternCalls)),
				ci32(q.mv(sid, cNFfi)), ci32(q.mv(sid, cNUnsafeBlocks)),
				ci32(q.mv(sid, cIsUnsafeFn)), ci32(q.mv(sid, cFanIn)),
				ci32(q.mv(sid, cSloc)), cs(q.at(sid))}
		},
		func(a, b *rowRec) bool {
			if a.c[1].i != b.c[1].i {
				return a.c[1].i > b.c[1].i
			}
			if a.c[2].i != b.c[2].i {
				return a.c[2].i > b.c[2].i
			}
			return a.id < b.id
		})
}
func qDeepModulePaths(q *qctx) *result {
	g := q.g
	r := &result{cols: []string{"path_", "external", "segments", "importer"}}
	var rs []rowRec
	for i := range g.Imports {
		im := &g.Imports[i]
		n := countOccurrences(im.Target(), "::")
		if n < 4 {
			continue
		}
		segs := int32(n + 1)
		if !likeMatch(q.mod, fileModName(im.FileID)) {
			continue
		}
		rs = append(rs, rowRec{id: int32(im.ID), c: []cell{cs(im.Target()),
			ci32(im.IsExternal), ci32(segs), cs(filePathByID[im.FileID])}})
	}
	sortRows(rs, func(a, b *rowRec) bool {
		if a.c[2].i != b.c[2].i {
			return a.c[2].i > b.c[2].i
		}
		if a.c[1].i != b.c[1].i {
			return a.c[1].i < b.c[1].i
		}
		return a.id < b.id
	})
	fill(r, rs)
	return r
}
func qAsyncTaskHubs(q *qctx) *result {
	return q.simple([]string{"name", "spawns", "awaits", "depth", "fan_in",
		"is_async", "sloc", "at"},
		func(sid int32) bool { return q.mv(sid, cNSpawn) > 0 && !sFileTest[sid] },
		func(sid int32) []cell {
			return []cell{cs(q.name(sid)), ci32(q.mv(sid, cNSpawn)),
				ci32(q.mv(sid, cNAwait)), ci32(q.mv(sid, cMaxLoopDepth)),
				ci32(q.mv(sid, cFanIn)), ci32(q.mv(sid, cIsAsyncFn)),
				ci32(q.mv(sid, cSloc)), cs(q.at(sid))}
		},
		func(a, b *rowRec) bool {
			if a.c[1].i != b.c[1].i {
				return a.c[1].i > b.c[1].i
			}
			if a.c[4].i != b.c[4].i {
				return a.c[4].i > b.c[4].i
			}
			return a.id < b.id
		})
}
func qPlaceholderPanicSites(q *qctx) *result {
	g := q.g
	r := &result{cols: []string{"path", "fn", "macro_", "line", "fan_in"}}
	var rs []rowRec
	for i := range g.Macros {
		m := &g.Macros[i]
		if m.Kind() != "invocation" {
			continue
		}
		if m.Name() != "todo" && m.Name() != "unimplemented" &&
			m.Name() != "unreachable" && m.Name() != "panic" {
			continue
		}
		sid := m.SymID
		if sid < 1 || int(sid) > g.N() {
			continue
		}
		if q.mv(sid, cIsTest) == 1 || sFileGen[sid] || !q.modOK(sid) {
			continue
		}
		rs = append(rs, rowRec{id: sid, x: int32(i), s: m.Name(),
			c: []cell{cs(sFilePath[sid]), cs(q.name(sid)),
				cs(m.Name()), ci32(m.Line), ci32(q.mv(sid, cFanIn))}})
	}
	sortRows(rs, func(a, b *rowRec) bool {
		if a.c[4].i != b.c[4].i {
			return a.c[4].i > b.c[4].i
		}
		if a.s != b.s {
			return a.s < b.s
		}
		return a.x < b.x
	})
	fill(r, rs)
	return r
}
func qDebugPrintResidue(q *qctx) *result {
	g := q.g
	r := &result{cols: []string{"path", "fn", "line", "sloc"}}
	var rs []rowRec
	for i := range g.Macros {
		m := &g.Macros[i]
		if m.Kind() != "invocation" || m.Name() != "dbg" {
			continue
		}
		sid := m.SymID
		if sid < 1 || int(sid) > g.N() {
			continue
		}
		if q.mv(sid, cIsTest) == 1 || sFileGen[sid] || !q.modOK(sid) {
			continue
		}
		rs = append(rs, rowRec{id: sid, c: []cell{cs(sFilePath[sid]), cs(q.name(sid)),
			ci32(m.Line), ci32(q.mv(sid, cSloc))}})
	}
	sortRows(rs, func(a, b *rowRec) bool {
		if a.c[3].i != b.c[3].i {
			return a.c[3].i > b.c[3].i
		}
		return a.id < b.id
	})
	fill(r, rs)
	return r
}
func qSQLStringBuild(q *qctx) *result {
	return q.simple([]string{"name", "sql_literals", "format_calls",
		"string_literals", "fan_in", "sloc", "at"},
		func(sid int32) bool {
			return q.mv(sid, cNSqlLiteral) > 0 &&
				(q.mv(sid, cNFormatMacro) > 0 || q.mv(sid, cNStringLit) > 1) &&
				!sFileTest[sid] && !sFileGen[sid]
		},
		func(sid int32) []cell {
			return []cell{cs(q.name(sid)), ci32(q.mv(sid, cNSqlLiteral)),
				ci32(q.mv(sid, cNFormatMacro)), ci32(q.mv(sid, cNStringLit)),
				ci32(q.mv(sid, cFanIn)), ci32(q.mv(sid, cSloc)), cs(q.at(sid))}
		},
		func(a, b *rowRec) bool {
			if a.c[4].i != b.c[4].i {
				return a.c[4].i > b.c[4].i
			}
			if a.c[1].i != b.c[1].i {
				return a.c[1].i > b.c[1].i
			}
			return a.id < b.id
		})
}
func qCommandBuildSurface(q *qctx) *result {
	g := q.g
	r := &result{cols: []string{"name", "sink", "command_sites",
		"string_literals", "format_calls", "fan_in", "sloc", "at"}}
	var rs []rowRec
	for i := range g.Hazards {
		h := &g.Hazards[i]
		if h.Pattern() != "Command::new" && h.Pattern() != "Command::spawn" {
			continue
		}
		sid := h.SymID
		if sFileTest[sid] || sFileGen[sid] || !q.modOK(sid) {
			continue
		}
		rs = append(rs, rowRec{id: sid, c: []cell{cs(q.name(sid)), cs(h.Pattern()),
			ci32(h.N), ci32(q.mv(sid, cNStringLit)),
			ci32(q.mv(sid, cNFormatMacro)), ci32(q.mv(sid, cFanIn)),
			ci32(q.mv(sid, cSloc)), cs(q.at(sid))}})
	}
	sortRows(rs, func(a, b *rowRec) bool {
		if a.c[5].i != b.c[5].i {
			return a.c[5].i > b.c[5].i
		}
		if a.c[2].i != b.c[2].i {
			return a.c[2].i > b.c[2].i
		}
		return a.id < b.id
	})
	fill(r, rs)
	return r
}
func qHardcodedSecretCandidates(q *qctx) *result {
	g := q.g
	r := &result{cols: []string{"name", "candidate", "line", "at"}}
	var rs []rowRec
	for i := range g.Secrets {
		s := &g.Secrets[i]
		sid := s.SymID
		if sid < 1 || int(sid) > g.N() {
			continue
		}
		if sFileTest[sid] || sFileGen[sid] || !q.modOK(sid) {
			continue
		}
		if strings.HasPrefix(s.Value(), "/") ||
			strings.ContainsRune(s.Value(), '|') || strings.ContainsRune(s.Value(), '%') {
			continue
		}
		rs = append(rs, rowRec{id: sid, c: []cell{cs(q.name(sid)), cs(s.Value()),
			ci32(s.Line),
			cs(sFilePath[sid] + ":" + itoa(int(s.Line)))}})
	}
	sortRows(rs, func(a, b *rowRec) bool {
		if len(b.c[1].s) != len(a.c[1].s) {
			return len(b.c[1].s) < len(a.c[1].s)
		}
		return a.id < b.id
	})
	fill(r, rs)
	return r
}
func qUntrustedDeserialization(q *qctx) *result {
	return q.simple([]string{"name", "deserialize_calls", "sloc", "at"},
		func(sid int32) bool {
			return q.mv(sid, cNDeserialize) > 0 && !sFileTest[sid] && !sFileGen[sid]
		},
		func(sid int32) []cell {
			return []cell{cs(q.name(sid)), ci32(q.mv(sid, cNDeserialize)),
				ci32(q.mv(sid, cSloc)), cs(q.at(sid))}
		},
		func(a, b *rowRec) bool {
			if a.c[1].i != b.c[1].i {
				return a.c[1].i > b.c[1].i
			}
			if a.c[2].i != b.c[2].i {
				return a.c[2].i > b.c[2].i
			}
			return a.id < b.id
		})
}
func qZipSlipSurface(q *qctx) *result {
	return q.simple([]string{"name", "zip_access", "sloc", "at"},
		func(sid int32) bool {
			return q.mv(sid, cNZipRead) > 0 && !sFileTest[sid] && !sFileGen[sid]
		},
		func(sid int32) []cell {
			return []cell{cs(q.name(sid)), ci32(q.mv(sid, cNZipRead)),
				ci32(q.mv(sid, cSloc)), cs(q.at(sid))}
		},
		func(a, b *rowRec) bool {
			if a.c[1].i != b.c[1].i {
				return a.c[1].i > b.c[1].i
			}
			if a.c[2].i != b.c[2].i {
				return a.c[2].i > b.c[2].i
			}
			return a.id < b.id
		})
}
func qUnsafeInLoop(q *qctx) *result {
	g := q.g
	r := &result{cols: []string{"path", "fn", "n_ops", "n_deref",
		"has_safety_comment", "line"}}
	var rs []rowRec
	for i := range g.UnsafeBlks {
		u := &g.UnsafeBlks[i]
		sid := u.SymID
		if u.InLoop != 1 || sFileGen[sid] || !q.modOK(sid) {
			continue
		}
		rs = append(rs, rowRec{id: sid, c: []cell{cs(sFilePath[sid]), cs(q.name(sid)),
			ci32(u.NOps), ci32(u.NDeref), ci32(u.HasSafety), ci32(u.Line)}})
	}
	sortRows(rs, func(a, b *rowRec) bool {
		if a.c[3].i != b.c[3].i {
			return a.c[3].i > b.c[3].i
		}
		if a.c[2].i != b.c[2].i {
			return a.c[2].i > b.c[2].i
		}
		return a.id < b.id
	})
	fill(r, rs)
	return r
}
func qSuppressionWithoutReason(q *qctx) *result {
	g := q.g
	r := &result{cols: []string{"path", "fn", "attr", "args", "line"}}
	var rs []rowRec
	for i := range g.Attributes {
		a := &g.Attributes[i]
		if a.Name() != "allow" && a.Name() != "expect" {
			continue
		}
		if a.Args() != "" {
			continue
		}
		sid := a.SymID
		if sid < 1 || int(sid) > g.N() {
			continue
		}
		if sFileGen[sid] || !q.modOK(sid) {
			continue
		}
		rs = append(rs, rowRec{id: sid, c: []cell{cs(sFilePath[sid]), cs(q.name(sid)),
			cs(a.Name()), cs(a.Args()), ci32(a.Line)}})
	}
	sortRows(rs, func(a, b *rowRec) bool {
		if a.c[0].s != b.c[0].s {
			return a.c[0].s < b.c[0].s
		}
		if a.c[4].i != b.c[4].i {
			return a.c[4].i < b.c[4].i
		}
		return a.id < b.id
	})
	fill(r, rs)
	return r
}
func qRefcellAcrossAwait(q *qctx) *result {
	g := q.g
	r := &result{cols: []string{"path", "fn", "line", "guards_live", "guards",
		"guard_dropped", "fan_in"}}
	var rs []rowRec
	for i := range g.AsyncPoints {
		a := &g.AsyncPoints[i]
		sid := a.SymID
		if a.HasRefcellGuard != 1 || sFileGen[sid] || !q.modOK(sid) {
			continue
		}
		rs = append(rs, rowRec{id: sid, c: []cell{cs(sFilePath[sid]), cs(q.name(sid)),
			ci32(a.Line), ci32(a.NGuardsLive), cs(a.Guards()),
			ci32(a.GuardDropped), ci32(q.mv(sid, cFanIn))}})
	}
	sortRows(rs, func(a, b *rowRec) bool {
		if a.c[6].i != b.c[6].i {
			return a.c[6].i > b.c[6].i
		}
		return a.id < b.id
	})
	fill(r, rs)
	return r
}
func qIndexingSlicingSurface(q *qctx) *result {
	return q.simple([]string{"path", "fn", "indexes", "field_accesses",
		"fan_in", "sloc"},
		func(sid int32) bool {
			return q.mv(sid, cNIndexExpr) > 0 && !sFileGen[sid] && !sFileTest[sid]
		},
		func(sid int32) []cell {
			return []cell{cs(sFilePath[sid]), cs(q.name(sid)),
				ci32(q.mv(sid, cNIndexExpr)), ci32(q.mv(sid, cNMemberAccess)),
				ci32(q.mv(sid, cFanIn)), ci32(q.mv(sid, cSloc))}
		},
		func(a, b *rowRec) bool {
			if a.c[2].i != b.c[2].i {
				return a.c[2].i > b.c[2].i
			}
			if a.c[4].i != b.c[4].i {
				return a.c[4].i > b.c[4].i
			}
			return a.id < b.id
		})
}
func qDroppedFutures(q *qctx) *result {
	return q.simple([]string{"path", "fn", "dropped", "awaits", "fan_in"},
		func(sid int32) bool {
			return q.mv(sid, cNErrorSwallow) > 0 && q.mv(sid, cIsAsyncFn) == 1 &&
				!sFileGen[sid] && !sFileTest[sid]
		},
		func(sid int32) []cell {
			return []cell{cs(sFilePath[sid]), cs(q.name(sid)),
				ci32(q.mv(sid, cNErrorSwallow)), ci32(q.mv(sid, cNAwait)),
				ci32(q.mv(sid, cFanIn))}
		},
		func(a, b *rowRec) bool {
			if a.c[2].i != b.c[2].i {
				return a.c[2].i > b.c[2].i
			}
			if a.c[4].i != b.c[4].i {
				return a.c[4].i > b.c[4].i
			}
			return a.id < b.id
		})
}
func qLossyCasts(q *qctx) *result {
	return q.simple([]string{"path", "fn", "casts", "checked", "fan_in", "sloc"},
		func(sid int32) bool {
			return q.mv(sid, cNAsCasts) > 0 && !sFileGen[sid] && !sFileTest[sid]
		},
		func(sid int32) []cell {
			return []cell{cs(sFilePath[sid]), cs(q.name(sid)),
				ci32(q.mv(sid, cNAsCasts)), ci32(q.mv(sid, cNCheckedArith)),
				ci32(q.mv(sid, cFanIn)), ci32(q.mv(sid, cSloc))}
		},
		func(a, b *rowRec) bool {
			if a.c[2].i != b.c[2].i {
				return a.c[2].i > b.c[2].i
			}
			if a.c[4].i != b.c[4].i {
				return a.c[4].i > b.c[4].i
			}
			return a.id < b.id
		})
}
func qErrorSwallowingSites(q *qctx) *result {
	return q.simple([]string{"path", "fn", "swallows", "question_marks", "fan_in"},
		func(sid int32) bool {
			return q.mv(sid, cNErrorSwallow) > 0 && !sFileGen[sid] && !sFileTest[sid]
		},
		func(sid int32) []cell {
			return []cell{cs(sFilePath[sid]), cs(q.name(sid)),
				ci32(q.mv(sid, cNErrorSwallow)),
				ci32(q.mv(sid, cNQuestionMark)), ci32(q.mv(sid, cFanIn))}
		},
		func(a, b *rowRec) bool {
			if a.c[2].i != b.c[2].i {
				return a.c[2].i > b.c[2].i
			}
			if a.c[4].i != b.c[4].i {
				return a.c[4].i > b.c[4].i
			}
			return a.id < b.id
		})
}
func qPublicAPIDocDebt(q *qctx) *result {
	return q.simple([]string{"name", "kind", "fan_in", "sloc", "at"},
		func(sid int32) bool {
			return q.mv(sid, cIsPublic) == 1 && q.mv(sid, cHasDoc) == 0 &&
				q.mv(sid, cFanIn) > 0 && q.isKind(sid, kFunction, kMethod) &&
				!sFileGen[sid] && !sFileTest[sid]
		},
		func(sid int32) []cell {
			return []cell{cs(q.name(sid)), cs(q.g.SymKind[sid-1].Str()),
				ci32(q.mv(sid, cFanIn)), ci32(q.mv(sid, cSloc)), cs(q.at(sid))}
		},
		func(a, b *rowRec) bool {
			if a.c[2].i != b.c[2].i {
				return a.c[2].i > b.c[2].i
			}
			if a.c[3].i != b.c[3].i {
				return a.c[3].i > b.c[3].i
			}
			if a.c[0].s != b.c[0].s {
				return a.c[0].s < b.c[0].s
			}
			fa, fb := q.g.SymFile[a.id-1], q.g.SymFile[b.id-1]
			if fa != fb {
				return fa < fb
			}
			return a.id < b.id
		})
}
func qManifestVsUsage(q *qctx) *result {
	g := q.g
	used := map[string]bool{}
	for i := range g.Imports {
		t := g.Imports[i].Target()
		for j := range g.Deps {
			d := &g.Deps[j]
			if t == d.Name() || strings.HasPrefix(t, d.Name()+"::") {
				used[d.Name()+"@"+d.Version()+itoa(int(d.IsDev))] = true
			}
		}
	}
	r := &result{cols: []string{"name", "version", "is_dev", "used"}}
	var rs []rowRec
	for i := range g.Deps {
		d := &g.Deps[i]
		if used[d.Name()+"@"+d.Version()+itoa(int(d.IsDev))] {
			continue
		}
		rs = append(rs, rowRec{id: d.ID, c: []cell{cs(d.Name()), cs(d.Version()),
			ci32(d.IsDev), ci32(0)}})
	}
	sortRows(rs, func(a, b *rowRec) bool {
		if a.c[2].i != b.c[2].i {
			return a.c[2].i < b.c[2].i
		}
		if a.c[0].s != b.c[0].s {
			return a.c[0].s < b.c[0].s
		}
		return a.id < b.id
	})
	fill(r, rs)
	return r
}
func qTransitivePanicSurface(q *qctx) *result {
	ts := q.reachPairs(4,
		func(sid int32) bool {
			return (q.mv(sid, cIsPublic) == 1 || q.mv(sid, cIsEntrypoint) == 1) &&
				(q.isKind(sid, kFunction) || q.isKind(sid, kMethod)) &&
				q.mv(sid, cIsTest) == 0
		},
		func(root, sym, hops int32) bool {
			return hops > 0 && q.mv(sym, cIsTest) == 0 && !sFileTest[sym] &&
				!sFileGen[sym] && q.modOK(sym) &&
				(q.mv(sym, cNUnwrap)+q.mv(sym, cNExpect)+q.mv(sym, cNPanicMacro)+
					q.mv(sym, cNIndexExpr)+q.mv(sym, cNSliceRange)) > 0
		})
	return q.fromReach([]string{"name", "reached_from", "hops", "unwraps",
		"expects", "panic_macros", "index_ops", "slices", "fan_in", "at"}, ts,
		func(t tri) []cell {
			return []cell{cs(q.name(t.sym)), cs(q.name(t.root)), ci32(t.hops),
				ci32(q.mv(t.sym, cNUnwrap)), ci32(q.mv(t.sym, cNExpect)),
				ci32(q.mv(t.sym, cNPanicMacro)), ci32(q.mv(t.sym, cNIndexExpr)),
				ci32(q.mv(t.sym, cNSliceRange)), ci32(q.mv(t.sym, cFanIn)),
				cs(q.at(t.sym))}
		},
		func(a, b *rowRec) bool {
			x := a.c[3].i + a.c[4].i + a.c[5].i + a.c[6].i
			y := b.c[3].i + b.c[4].i + b.c[5].i + b.c[6].i
			if x != y {
				return x > y
			}
			if a.c[2].i != b.c[2].i {
				return a.c[2].i < b.c[2].i
			}
			if a.x != b.x {
				return a.x < b.x
			}
			return a.id < b.id
		})
}
func qResultUnwrappedByCaller(q *qctx) *result {
	g := q.g
	r := &result{cols: []string{"unwrapping_caller", "returns_result",
		"return_type", "caller_unwraps", "caller_expects",
		"callee_question_marks", "callee_fan_in", "cyclo", "at"}}
	var rs []rowRec
	for i := range g.Edges {
		e := &g.Edges[i]
		if e.IsSelf != 0 {
			continue
		}
		c, k := e.Caller, e.Callee
		if c < 1 || k < 1 || int(c) > g.N() || int(k) > g.N() {
			continue
		}
		rt := g.SymRet[k-1].Str()
		if !likeSubstr(rt, "Result<") && !likeSubstr(rt, "Option<") {
			continue
		}
		if q.mv(c, cNUnwrap)+q.mv(c, cNExpect) == 0 {
			continue
		}
		if q.mv(c, cIsTest) == 1 || q.mv(k, cIsTest) == 1 ||
			sFileTest[c] || sFileGen[c] || !q.modOK(c) {
			continue
		}
		rs = append(rs, rowRec{id: c, x: int32(i), c: []cell{cs(q.name(c)), cs(q.name(k)), cs(rt),
			ci32(q.mv(c, cNUnwrap)), ci32(q.mv(c, cNExpect)),
			ci32(q.mv(k, cNQuestionMark)), ci32(q.mv(k, cFanIn)),
			ci32(q.mv(c, cCyclomatic)), cs(q.at(c))}})
	}
	sortRows(rs, func(a, b *rowRec) bool {
		x := a.c[3].i + a.c[4].i
		y := b.c[3].i + b.c[4].i
		if x != y {
			return x > y
		}
		if a.c[6].i != b.c[6].i {
			return a.c[6].i > b.c[6].i
		}
		cfa, cfb := q.mv(a.id, cFanIn), q.mv(b.id, cFanIn)
		if cfa != cfb {
			return cfa > cfb
		}
		if a.c[0].s != b.c[0].s {
			return a.c[0].s < b.c[0].s
		}
		if a.id != b.id {
			return a.id < b.id
		}
		return a.x < b.x
	})
	fill(r, rs)
	return r
}
func qMutexPoisonCascade(q *qctx) *result {
	return q.simple([]string{"name", "on_type", "lock_acquires", "unwraps",
		"expects", "awaits", "cascade_blast", "fan_in", "at"},
		func(sid int32) bool {
			return q.mv(sid, cNLockAcquire) > 0 &&
				(q.mv(sid, cNUnwrap)+q.mv(sid, cNExpect)) > 0 &&
				q.mv(sid, cIsTest) == 0 && !sFileTest[sid] && !sFileGen[sid]
		},
		func(sid int32) []cell {
			blast := (q.mv(sid, cNUnwrap) + q.mv(sid, cNExpect)) *
				q.max1(q.mv(sid, cFanIn))
			return []cell{cs(q.name(sid)), cs(q.impl(sid)),
				ci32(q.mv(sid, cNLockAcquire)), ci32(q.mv(sid, cNUnwrap)),
				ci32(q.mv(sid, cNExpect)), ci32(q.mv(sid, cNAwait)),
				ci(int64(blast)), ci32(q.mv(sid, cFanIn)), cs(q.at(sid))}
		},
		func(a, b *rowRec) bool {
			if a.c[6].i != b.c[6].i {
				return a.c[6].i > b.c[6].i
			}
			if a.c[2].i != b.c[2].i {
				return a.c[2].i > b.c[2].i
			}
			return a.id < b.id
		})
}
func qPanicInDropImpl(q *qctx) *result {
	g := q.g
	r := &result{cols: []string{"type_", "drop_method", "unwraps", "expects",
		"panic_macros", "index_ops", "refcell_borrows", "fan_in", "at"}}
	var rs []rowRec
	for i := range g.Impls {
		im := &g.Impls[i]
		if im.TraitName() != "Drop" {
			continue
		}
		for _, s := range childByParent[im.SymID] {
			if !q.isKind(s, kFunction, kMethod) {
				continue
			}
			if q.mv(s, cNUnwrap)+q.mv(s, cNExpect)+q.mv(s, cNPanicMacro)+
				q.mv(s, cNIndexExpr)+q.mv(s, cNBorrowCalls) == 0 {
				continue
			}
			if q.mv(s, cIsTest) == 1 || sFileTest[s] || sFileGen[s] || !q.modOK(s) {
				continue
			}
			rs = append(rs, rowRec{id: s, x: int32(i),
				c: []cell{cs(im.TypeName()), cs(q.name(s)),
					ci32(q.mv(s, cNUnwrap)), ci32(q.mv(s, cNExpect)),
					ci32(q.mv(s, cNPanicMacro)), ci32(q.mv(s, cNIndexExpr)),
					ci32(q.mv(s, cNBorrowCalls)), ci32(q.mv(s, cFanIn)),
					cs(q.at(s))}})
		}
	}
	sortRows(rs, func(a, b *rowRec) bool {
		x := a.c[2].i + a.c[3].i + a.c[4].i
		y := b.c[2].i + b.c[3].i + b.c[4].i
		if x != y {
			return x > y
		}
		if a.c[7].i != b.c[7].i {
			return a.c[7].i > b.c[7].i
		}
		if a.c[0].s != b.c[0].s {
			return a.c[0].s < b.c[0].s
		}
		if a.x != b.x {
			return a.x < b.x
		}
		return a.id < b.id
	})
	fill(r, rs)
	return r
}
func qPanicInExternFn(q *qctx) *result {
	return q.simple([]string{"name", "unwraps", "expects", "panic_macros",
		"index_ops", "ffi_calls_out", "unsafe_blocks", "fan_in", "at"},
		func(sid int32) bool {
			return q.mv(sid, cIsExternFn) == 1 &&
				(q.mv(sid, cNUnwrap)+q.mv(sid, cNExpect)+q.mv(sid, cNPanicMacro)+
					q.mv(sid, cNIndexExpr)) > 0 &&
				q.mv(sid, cIsTest) == 0 && !sFileTest[sid] && !sFileGen[sid]
		},
		func(sid int32) []cell {
			return []cell{cs(q.name(sid)), ci32(q.mv(sid, cNUnwrap)),
				ci32(q.mv(sid, cNExpect)), ci32(q.mv(sid, cNPanicMacro)),
				ci32(q.mv(sid, cNIndexExpr)), ci32(q.mv(sid, cNExternCalls)),
				ci32(q.mv(sid, cNUnsafeBlocks)), ci32(q.mv(sid, cFanIn)),
				cs(q.at(sid))}
		},
		func(a, b *rowRec) bool {
			x := a.c[1].i + a.c[2].i + a.c[3].i
			y := b.c[1].i + b.c[2].i + b.c[3].i
			if x != y {
				return x > y
			}
			if a.c[7].i != b.c[7].i {
				return a.c[7].i > b.c[7].i
			}
			return a.id < b.id
		})
}
func qAwaitInLoop(q *qctx) *result {
	return q.simple([]string{"name", "on_type", "awaits_in_loop", "awaits_total",
		"channel_ops", "locks", "async_fn", "pub_", "fan_in", "at"},
		func(sid int32) bool {
			return q.mv(sid, cAwaitInLoop) > 0 && q.mv(sid, cIsTest) == 0 &&
				!sFileTest[sid] && !sFileGen[sid]
		},
		func(sid int32) []cell {
			return []cell{cs(q.name(sid)), cs(q.impl(sid)),
				ci32(q.mv(sid, cAwaitInLoop)), ci32(q.mv(sid, cNAwait)),
				ci32(q.mv(sid, cNChannelOps)), ci32(q.mv(sid, cNLockAcquire)),
				ci32(q.mv(sid, cIsAsyncFn)), ci32(q.mv(sid, cIsPublic)),
				ci32(q.mv(sid, cFanIn)), cs(q.at(sid))}
		},
		func(a, b *rowRec) bool {
			if a.c[2].i != b.c[2].i {
				return a.c[2].i > b.c[2].i
			}
			if a.c[8].i != b.c[8].i {
				return a.c[8].i > b.c[8].i
			}
			return a.id < b.id
		})
}
func qBlockingInCriticalSection(q *qctx) *result {
	ts := q.reachPairsSelf(3,
		func(sid int32) bool { return q.mv(sid, cNLockAcquire) > 0 },
		func(root, sym, hops int32) bool {
			return !sFileTest[sym] && q.modOK(sym) &&
				(q.mv(sym, cNBlockingIO) > 0 || q.mv(sym, cNThreadSleep) > 0 ||
					q.mv(sym, cNBlockOn) > 0)
		})
	return q.fromReach([]string{"takes_lock", "blocking_callee", "hops",
		"blocking_calls", "sleeps", "block_ons", "blocking_in_loop", "at"}, ts,
		func(t tri) []cell {
			return []cell{cs(q.name(t.root)), cs(q.name(t.sym)), ci32(t.hops),
				ci32(q.mv(t.sym, cNBlockingIO)), ci32(q.mv(t.sym, cNThreadSleep)),
				ci32(q.mv(t.sym, cNBlockOn)), ci32(q.mv(t.sym, cIOInLoop)),
				cs(q.at(t.sym))}
		},
		func(a, b *rowRec) bool {
			x := a.c[3].i + a.c[4].i + a.c[5].i
			y := b.c[3].i + b.c[4].i + b.c[5].i
			if x != y {
				return x > y
			}
			if a.c[2].i != b.c[2].i {
				return a.c[2].i < b.c[2].i
			}
			if a.x != b.x {
				return a.x < b.x
			}
			return a.id < b.id
		})
}
func qSyncLockInAsyncFn(q *qctx) *result {
	return q.simple([]string{"name", "on_type", "lock_acquires", "awaits",
		"guards_across_await", "arc_mutex_fields", "rc_refcell_fields", "pub_",
		"fan_in", "at"},
		func(sid int32) bool {
			return q.mv(sid, cIsAsyncFn) == 1 && q.mv(sid, cNLockAcquire) > 0 &&
				q.mv(sid, cIsTest) == 0 && !sFileTest[sid] && !sFileGen[sid]
		},
		func(sid int32) []cell {
			return []cell{cs(q.name(sid)), cs(q.impl(sid)),
				ci32(q.mv(sid, cNLockAcquire)), ci32(q.mv(sid, cNAwait)),
				ci32(q.mv(sid, cNLockAcrossAwait)),
				ci32(q.mv(sid, cNArcMutex)), ci32(q.mv(sid, cNRcRefcell)),
				ci32(q.mv(sid, cIsPublic)), ci32(q.mv(sid, cFanIn)),
				cs(q.at(sid))}
		},
		func(a, b *rowRec) bool {
			if a.c[2].i != b.c[2].i {
				return a.c[2].i > b.c[2].i
			}
			if a.c[4].i != b.c[4].i {
				return a.c[4].i > b.c[4].i
			}
			return a.id < b.id
		})
}
func qBlockOnInAsyncContext(q *qctx) *result {
	ts := q.reachPairsSelf(3,
		func(sid int32) bool { return q.mv(sid, cIsAsyncFn) == 1 },
		func(root, sym, hops int32) bool {
			return q.mv(sym, cNBlockOn) > 0 && !sFileTest[sym] && q.modOK(sym)
		})
	return q.fromReach([]string{"async_fn", "blocks_in", "hops", "block_ons",
		"other_blocking", "async_fan_in", "at"}, ts,
		func(t tri) []cell {
			return []cell{cs(q.name(t.root)), cs(q.name(t.sym)), ci32(t.hops),
				ci32(q.mv(t.sym, cNBlockOn)), ci32(q.mv(t.sym, cNBlockingIO)),
				ci32(q.mv(t.root, cFanIn)), cs(q.at(t.sym))}
		},
		func(a, b *rowRec) bool {
			if a.c[3].i != b.c[3].i {
				return a.c[3].i > b.c[3].i
			}
			if a.c[2].i != b.c[2].i {
				return a.c[2].i < b.c[2].i
			}
			if a.x != b.x {
				return a.x < b.x
			}
			return a.id < b.id
		})
}
func qOSThreadInAsync(q *qctx) *result {
	ts := q.reachPairsSelf(3,
		func(sid int32) bool { return q.mv(sid, cIsAsyncFn) == 1 },
		func(root, sym, hops int32) bool {
			return q.mv(sym, cNThreadSpawn) > 0 && !sFileTest[sym] && q.modOK(sym)
		})
	return q.fromReach([]string{"async_fn", "spawns_thread", "hops",
		"thread_spawns", "total_spawns", "spawn_blockings", "async_fan_in",
		"at"}, ts,
		func(t tri) []cell {
			return []cell{cs(q.name(t.root)), cs(q.name(t.sym)), ci32(t.hops),
				ci32(q.mv(t.sym, cNThreadSpawn)), ci32(q.mv(t.sym, cNSpawn)),
				ci32(q.mv(t.sym, cNSpawnBlocking)), ci32(q.mv(t.root, cFanIn)),
				cs(q.at(t.sym))}
		},
		func(a, b *rowRec) bool {
			if a.c[3].i != b.c[3].i {
				return a.c[3].i > b.c[3].i
			}
			if a.c[2].i != b.c[2].i {
				return a.c[2].i < b.c[2].i
			}
			if a.x != b.x {
				return a.x < b.x
			}
			return a.id < b.id
		})
}
func qSpawnedTaskPanic(q *qctx) *result {
	g := q.g
	r := &result{cols: []string{"spawns_tasks", "task_body", "unwraps", "expects",
		"panic_macros", "index_ops", "spawns_here", "spawner_is_async", "at"}}
	var rs []rowRec
	for p := int32(1); p <= int32(g.N()); p++ {
		if q.mv(p, cNSpawn) == 0 {
			continue
		}
		for _, c := range childByParent[p] {
			if g.SymKind[c-1].Str() != kClosure {
				continue
			}
			if q.mv(c, cNUnwrap)+q.mv(c, cNExpect)+q.mv(c, cNPanicMacro)+
				q.mv(c, cNIndexExpr) == 0 {
				continue
			}
			if q.mv(p, cIsTest) == 1 || q.mv(c, cIsTest) == 1 ||
				sFileTest[c] || sFileGen[c] || !q.modOK(p) {
				continue
			}
			rs = append(rs, rowRec{id: c, c: []cell{cs(q.name(p)), cs(q.name(c)),
				ci32(q.mv(c, cNUnwrap)), ci32(q.mv(c, cNExpect)),
				ci32(q.mv(c, cNPanicMacro)), ci32(q.mv(c, cNIndexExpr)),
				ci32(q.mv(p, cNSpawn)), ci32(q.mv(p, cIsAsyncFn)), cs(q.at(c))}})
		}
	}
	sortRows(rs, func(a, b *rowRec) bool {
		x := a.c[2].i + a.c[3].i + a.c[4].i
		y := b.c[2].i + b.c[3].i + b.c[4].i
		if x != y {
			return x > y
		}
		if a.c[6].i != b.c[6].i {
			return a.c[6].i > b.c[6].i
		}
		return a.id < b.id
	})
	fill(r, rs)
	return r
}
func qSpawnInLoop(q *qctx) *result {
	return q.simple([]string{"name", "on_type", "spawns_in_loop", "spawns_total",
		"spawn_blockings", "joins", "loop_nesting", "fan_in", "at"},
		func(sid int32) bool {
			return q.mv(sid, cNSpawnInLoop) > 0 && q.mv(sid, cIsTest) == 0 &&
				!sFileTest[sid] && !sFileGen[sid]
		},
		func(sid int32) []cell {
			return []cell{cs(q.name(sid)), cs(q.impl(sid)),
				ci32(q.mv(sid, cNSpawnInLoop)), ci32(q.mv(sid, cNSpawn)),
				ci32(q.mv(sid, cNSpawnBlocking)), ci32(q.mv(sid, cNJoinCalls)),
				ci32(q.mv(sid, cMaxLoopDepth)), ci32(q.mv(sid, cFanIn)),
				cs(q.at(sid))}
		},
		func(a, b *rowRec) bool {
			if a.c[2].i != b.c[2].i {
				return a.c[2].i > b.c[2].i
			}
			if a.c[7].i != b.c[7].i {
				return a.c[7].i > b.c[7].i
			}
			return a.id < b.id
		})
}
func qSpawnJoinBalance(q *qctx) *result {
	g := q.g
	groups := q.modGroups([]int{cNSpawn, cNSpawnBlocking, cNThreadSpawn,
		cNJoinCalls}, []string{kFunction, kMethod}, true, true)
	spawning := map[int32]int32{}
	for sid := int32(1); sid <= int32(g.N()); sid++ {
		if !q.isKind(sid, kFunction, kMethod) || sFileTest[sid] || sFileGen[sid] {
			continue
		}
		if q.mv(sid, cNSpawn) == 0 {
			continue
		}
		spawning[g.SymModule[sid-1]]++
	}
	r := &result{cols: []string{"module_", "spawns", "spawn_blocking",
		"thread_spawns", "joins", "detached", "spawning_fns"}}
	var rs []rowRec
	for _, p := range groups {
		detached := p.cols[0] - p.cols[3]
		if !(p.cols[0] > p.cols[3]) {
			continue
		}
		rs = append(rs, rowRec{id: p.id, c: []cell{cs(g.modName(p.id)),
			ci32(p.cols[0]), ci32(p.cols[1]), ci32(p.cols[2]), ci32(p.cols[3]),
			ci32(detached), ci32(spawning[p.id])}})
	}
	sortRows(rs, func(a, b *rowRec) bool {
		if a.c[5].i != b.c[5].i {
			return a.c[5].i > b.c[5].i
		}
		if a.c[1].i != b.c[1].i {
			return a.c[1].i > b.c[1].i
		}
		return a.id < b.id
	})
	fill(r, rs)
	return r
}
func qChannelOpInLoop(q *qctx) *result {
	return q.simple([]string{"name", "on_type", "channel_ops", "awaits",
		"awaits_in_loop", "loop_nesting", "fan_in", "at"},
		func(sid int32) bool {
			return q.mv(sid, cNChannelOps) > 0 && q.mv(sid, cMaxLoopDepth) > 0 &&
				q.mv(sid, cIsTest) == 0 && !sFileTest[sid] && !sFileGen[sid]
		},
		func(sid int32) []cell {
			return []cell{cs(q.name(sid)), cs(q.impl(sid)),
				ci32(q.mv(sid, cNChannelOps)), ci32(q.mv(sid, cNAwait)),
				ci32(q.mv(sid, cAwaitInLoop)),
				ci32(q.mv(sid, cMaxLoopDepth)), ci32(q.mv(sid, cFanIn)),
				cs(q.at(sid))}
		},
		func(a, b *rowRec) bool {
			if a.c[2].i != b.c[2].i {
				return a.c[2].i > b.c[2].i
			}
			if a.c[6].i != b.c[6].i {
				return a.c[6].i > b.c[6].i
			}
			return a.id < b.id
		})
}
func qDeepAsyncCallChain(q *qctx) *result {
	g := q.g
	w := newReachWalk(g)
	type st struct{ depth, n int32 }
	stats := map[int32]st{}
	for sid := int32(1); sid <= int32(g.N()); sid++ {
		if q.mv(sid, cIsAsyncFn) != 1 || q.mv(sid, cIsTest) != 0 {
			continue
		}
		d, n := w.pairStats(sid, 8)
		stats[sid] = st{d, n}
	}
	r := &result{cols: []string{"async_entry", "chain_depth",
		"callees_downstream", "fan_in", "sloc", "at"}}
	var rs []rowRec
	for sid := int32(1); sid <= int32(g.N()); sid++ {
		s, ok := stats[sid]
		if !ok || s.depth < 4 {
			continue
		}
		if !q.modOK(sid) {
			continue
		}
		rs = append(rs, rowRec{id: sid, c: []cell{cs(q.name(sid)), ci32(s.depth),
			ci32(s.n), ci32(q.mv(sid, cFanIn)),
			ci32(q.mv(sid, cSloc)), cs(q.at(sid))}})
	}
	sortRows(rs, func(a, b *rowRec) bool {
		if a.c[1].i != b.c[1].i {
			return a.c[1].i > b.c[1].i
		}
		if a.c[2].i != b.c[2].i {
			return a.c[2].i > b.c[2].i
		}
		return a.id < b.id
	})
	fill(r, rs)
	return r
}
func qSwallowedErrorBelowPubAPI(q *qctx) *result {
	ts := q.reachPairs(3,
		func(sid int32) bool {
			return (q.mv(sid, cIsPublic) == 1 || q.mv(sid, cIsEntrypoint) == 1) &&
				(q.isKind(sid, kFunction) || q.isKind(sid, kMethod)) &&
				q.mv(sid, cIsTest) == 0
		},
		func(root, sym, hops int32) bool {
			return hops > 0 && q.mv(sym, cNErrorSwallow) > 0 &&
				q.mv(sym, cIsTest) == 0 && !sFileTest[sym] && !sFileGen[sym] &&
				q.modOK(sym)
		})
	return q.fromReach([]string{"name", "reached_from", "hops", "swallows",
		"propagates", "fan_in", "at"}, ts,
		func(t tri) []cell {
			return []cell{cs(q.name(t.sym)), cs(q.name(t.root)), ci32(t.hops),
				ci32(q.mv(t.sym, cNErrorSwallow)),
				ci32(q.mv(t.sym, cNQuestionMark)), ci32(q.mv(t.sym, cFanIn)),
				cs(q.at(t.sym))}
		},
		func(a, b *rowRec) bool {
			if a.c[3].i != b.c[3].i {
				return a.c[3].i > b.c[3].i
			}
			if a.c[2].i != b.c[2].i {
				return a.c[2].i < b.c[2].i
			}
			if a.x != b.x {
				return a.x < b.x
			}
			return a.id < b.id
		})
}
func qExitSkippingDrop(q *qctx) *result {
	g := q.g
	ts := q.reachPairsSelf(4,
		func(sid int32) bool {
			return (q.mv(sid, cIsPublic) == 1 || q.mv(sid, cIsEntrypoint) == 1) &&
				(q.isKind(sid, kFunction) || q.isKind(sid, kMethod)) &&
				q.mv(sid, cIsTest) == 0
		},
		func(root, sym, hops int32) bool { return !sFileTest[sym] })
	type row struct {
		rec          rowRec
		hops, n, fan int32
	}
	var rows []row
	for _, t := range ts {
		if sFileTest[t.sym] || !q.modOK(t.sym) {
			continue
		}
		for _, hi := range hazBySym[t.sym] {
			h := &g.Hazards[hi]
			if h.Pattern() != "exit" && h.Pattern() != "process::exit" &&
				h.Pattern() != "*::exit" && h.Pattern() != "abort" {
				continue
			}
			rows = append(rows, row{rowRec{id: t.sym, c: []cell{
				cs(q.name(t.sym)), cs(h.Pattern()), ci32(h.N),
				cs(q.name(t.root)), ci32(t.hops), ci32(q.mv(t.sym, cFanIn)),
				cs(q.at(t.sym))}}, t.hops, h.N, q.mv(t.sym, cFanIn)})
		}
	}
	sort.SliceStable(rows, func(i, j int) bool {
		a, b := &rows[i], &rows[j]
		if a.hops != b.hops {
			return a.hops < b.hops
		}
		if a.n != b.n {
			return a.n > b.n
		}
		if a.fan != b.fan {
			return a.fan > b.fan
		}
		return a.rec.id < b.rec.id
	})
	r := &result{cols: []string{"calls_exit", "sink", "exit_sites",
		"reached_from", "hops", "fan_in", "at"}}
	fill(r, []rowRec{})
	rs := make([]rowRec, len(rows))
	for i := range rows {
		rs[i] = rows[i].rec
	}
	fill(r, rs)
	return r
}
func qExplicitLeakSurface(q *qctx) *result {
	g := q.g
	r := &result{cols: []string{"name", "leak_site", "leak_calls", "category",
		"pub_", "fan_in", "at"}}
	var rs []rowRec
	for i := range g.Hazards {
		h := &g.Hazards[i]
		if h.Pattern() != "mem::forget" && h.Pattern() != "Box::leak" &&
			h.Pattern() != "leak" {
			continue
		}
		sid := h.SymID
		if sFileTest[sid] || sFileGen[sid] || !q.modOK(sid) {
			continue
		}
		rs = append(rs, rowRec{id: sid, c: []cell{cs(q.name(sid)), cs(h.Pattern()),
			ci32(h.N), cs(h.Category()), ci32(q.mv(sid, cIsPublic)),
			ci32(q.mv(sid, cFanIn)), cs(q.at(sid))}})
	}
	sortRows(rs, func(a, b *rowRec) bool {
		if a.c[2].i != b.c[2].i {
			return a.c[2].i > b.c[2].i
		}
		if a.c[5].i != b.c[5].i {
			return a.c[5].i > b.c[5].i
		}
		return a.id < b.id
	})
	fill(r, rs)
	return r
}
func qNeedlessUnsafeFn(q *qctx) *result {
	return q.simple([]string{"name", "on_type", "unsafe_fn", "unsafe_blocks",
		"unsafe_ops", "transmutes", "raw_ptrs", "pub_", "fan_in", "at"},
		func(sid int32) bool {
			return q.mv(sid, cIsUnsafeFn) == 1 && q.mv(sid, cNUnsafeBlocks) == 0 &&
				q.mv(sid, cNUnsafeOps) == 0 && q.mv(sid, cNTransmute) == 0 &&
				q.mv(sid, cNFromRaw) == 0 && q.mv(sid, cIsTest) == 0 &&
				!sFileTest[sid] && !sFileGen[sid]
		},
		func(sid int32) []cell {
			return []cell{cs(q.name(sid)), cs(q.impl(sid)),
				ci32(q.mv(sid, cIsUnsafeFn)), ci32(q.mv(sid, cNUnsafeBlocks)),
				ci32(q.mv(sid, cNUnsafeOps)), ci32(q.mv(sid, cNTransmute)),
				ci32(q.mv(sid, cNRawPtr)), ci32(q.mv(sid, cIsPublic)),
				ci32(q.mv(sid, cFanIn)), cs(q.at(sid))}
		},
		func(a, b *rowRec) bool {
			if a.c[8].i != b.c[8].i {
				return a.c[8].i > b.c[8].i
			}
			sa, sb := q.mv(a.id, cSloc), q.mv(b.id, cSloc)
			if sa != sb {
				return sa > sb
			}
			fa, fb := q.g.SymFile[a.id-1], q.g.SymFile[b.id-1]
			if fa != fb {
				return fa < fb
			}
			la, lb := q.g.SymLine[a.id-1], q.g.SymLine[b.id-1]
			if la != lb {
				return la < lb
			}
			return a.id < b.id
		})
}
func qGratuitousUnsafeImpl(q *qctx) *result {
	g := q.g
	r := &result{cols: []string{"type_", "trait_", "unsafe_blocks", "raw_ptrs",
		"transmutes", "impl_fan_in", "impls_of_trait", "at"}}
	var rs []rowRec
	for i := range g.Impls {
		im := &g.Impls[i]
		if im.IsUnsafe != 1 {
			continue
		}
		var ub, rp, tr int32
		for _, m := range childByParent[im.SymID] {
			if !q.isKind(m, kFunction, kMethod) {
				continue
			}
			ub += q.mv(m, cNUnsafeBlocks)
			rp += q.mv(m, cNRawPtr)
			tr += q.mv(m, cNTransmute)
		}
		if ub != 0 || rp != 0 || tr != 0 {
			continue
		}
		if sFileTest[im.SymID] || !likeMatch(q.mod, g.ModName[im.SymID-1]) {
			continue
		}
		nTrait := int32(0)
		for j := range g.Impls {
			if g.Impls[j].TraitName() == im.TraitName() {
				nTrait++
			}
		}
		rs = append(rs, rowRec{id: im.SymID, c: []cell{cs(im.TypeName()),
			cs(im.TraitName()), ci32(ub), ci32(rp), ci32(tr),
			ci32(q.mv(im.SymID, cFanIn)), ci32(nTrait),
			cs(sFilePath[im.SymID] + ":" + itoa(int(im.Line)))}})
	}
	sortRows(rs, func(a, b *rowRec) bool {
		if a.c[5].i != b.c[5].i {
			return a.c[5].i > b.c[5].i
		}
		if a.c[1].s != b.c[1].s {
			return a.c[1].s < b.c[1].s
		}
		if a.c[0].s != b.c[0].s {
			return a.c[0].s < b.c[0].s
		}
		return a.id < b.id
	})
	fill(r, rs)
	return r
}
func qMacroDefinedUnsafe(q *qctx) *result {
	g := q.g
	invocations := map[string]int32{}
	for i := range g.Macros {
		m := &g.Macros[i]
		if m.Kind() == "invocation" {
			invocations[m.Name()]++
		}
	}
	r := &result{cols: []string{"macro_", "unsafe_tokens", "body_bytes",
		"defines_items", "call_sites", "at"}}
	var rs []rowRec
	for i := range g.Macros {
		m := &g.Macros[i]
		if m.Kind() != "definition" || m.NUnsafe == 0 {
			continue
		}
		sid := m.SymID
		if sFileTest[sid] || sFileGen[sid] {
			continue
		}
		if !likeMatch(q.mod, g.ModName[sid-1]) {
			continue
		}
		rs = append(rs, rowRec{id: sid, x: int32(i),
			c: []cell{cs(m.Name()), ci32(m.NUnsafe),
				ci32(m.BodyBytes), ci32(m.DefinesItems), ci32(invocations[m.Name()]),
				cs(sFilePath[sid] + ":" + itoa(int(m.Line)))}})
	}
	sortRows(rs, func(a, b *rowRec) bool {
		if a.c[4].i != b.c[4].i {
			return a.c[4].i > b.c[4].i
		}
		if a.c[1].i != b.c[1].i {
			return a.c[1].i > b.c[1].i
		}
		if a.c[0].s != b.c[0].s {
			return a.c[0].s < b.c[0].s
		}
		return a.x < b.x
	})
	fill(r, rs)
	return r
}
func qMutualRecursion(q *qctx) *result {
	g := q.g
	best := map[int32]int32{}
	w := newReachWalk(g)
	w.reportRoot = true
	for sid := int32(1); sid <= int32(g.N()); sid++ {
		if !(q.isKind(sid, kFunction) || q.isKind(sid, kMethod)) ||
			q.mv(sid, cIsTest) == 1 {
			continue
		}
		w.each(sid, 6, func(s, d int32) {
			if s != sid {
				return
			}
			if old, ok := best[sid]; !ok || d < old {
				best[sid] = d
			}
		})
	}
	r := &result{cols: []string{"name", "on_type", "cycle_len", "fan_in", "pub_",
		"at"}}
	var rs []rowRec
	for sid := int32(1); sid <= int32(g.N()); sid++ {
		d, ok := best[sid]
		if !ok || d == 0 {
			continue
		}
		if sFileTest[sid] || !q.modOK(sid) {
			continue
		}
		rs = append(rs, rowRec{id: sid, c: []cell{cs(q.name(sid)), cs(q.impl(sid)),
			ci32(d), ci32(q.mv(sid, cFanIn)), ci32(q.mv(sid, cIsPublic)),
			cs(q.at(sid))}})
	}
	sortRows(rs, func(a, b *rowRec) bool {
		if a.c[2].i != b.c[2].i {
			return a.c[2].i < b.c[2].i
		}
		if a.c[3].i != b.c[3].i {
			return a.c[3].i > b.c[3].i
		}
		return a.id < b.id
	})
	fill(r, rs)
	return r
}
func qUncalledPubAPI(q *qctx) *result {
	return q.simple([]string{"name", "on_type", "trait_disp", "sloc", "cyclo",
		"has_doc", "at"},
		func(sid int32) bool {
			return q.mv(sid, cIsPublic) == 1 && q.mv(sid, cFanIn) == 0 &&
				q.isKind(sid, kFunction, kMethod) &&
				q.mv(sid, cIsEntrypoint) == 0 && q.mv(sid, cIsAbstract) == 0 &&
				q.mv(sid, cIsTest) == 0 && !sFileTest[sid] && !sFileGen[sid]
		},
		func(sid int32) []cell {
			return []cell{cs(q.name(sid)), cs(q.impl(sid)),
				ci32(q.mv(sid, cIsTraitMethod)), ci32(q.mv(sid, cSloc)),
				ci32(q.mv(sid, cCyclomatic)), ci32(q.mv(sid, cHasDoc)),
				cs(q.at(sid))}
		},
		func(a, b *rowRec) bool {
			if a.c[3].i != b.c[3].i {
				return a.c[3].i > b.c[3].i
			}
			if a.c[4].i != b.c[4].i {
				return a.c[4].i > b.c[4].i
			}
			if a.c[0].s != b.c[0].s {
				return a.c[0].s < b.c[0].s
			}
			fa, fb := q.g.SymFile[a.id-1], q.g.SymFile[b.id-1]
			if fa != fb {
				return fa < fb
			}
			return a.id < b.id
		})
}
func qGlobalMutableState(q *qctx) *result {
	g := q.g
	locking := map[int32]int32{}
	for sid := int32(1); sid <= int32(g.N()); sid++ {
		if !(q.isKind(sid, kFunction, kMethod)) || q.mv(sid, cIsTest) == 1 {
			continue
		}
		if q.mv(sid, cNLockAcquire) == 0 {
			continue
		}
		locking[g.SymModule[sid-1]]++
	}
	return q.simple([]string{"global_", "kind", "static_mut_", "nested_locks",
		"signature", "locking_fns_in_module", "at"},
		func(sid int32) bool {
			if g.SymKind[sid-1].Str() != kStatic {
				return false
			}
			sig := g.SymSig[sid-1].Str()
			return (q.mv(sid, cNStaticMut) > 0 || q.mv(sid, cNArcMutex) > 0 ||
				likeSubstr(sig, "Mutex<") || likeSubstr(sig, "RwLock<") ||
				likeSubstr(sig, "Atomic")) && !sFileTest[sid] && !sFileGen[sid]
		},
		func(sid int32) []cell {
			return []cell{cs(q.name(sid)), cs(g.SymKind[sid-1].Str()),
				ci32(q.mv(sid, cNStaticMut)), ci32(q.mv(sid, cNArcMutex)),
				cs(g.SymSig[sid-1].Str()), ci32(locking[g.SymModule[sid-1]]),
				cs(q.at(sid))}
		},
		func(a, b *rowRec) bool {
			if a.c[2].i != b.c[2].i {
				return a.c[2].i > b.c[2].i
			}
			if a.c[5].i != b.c[5].i {
				return a.c[5].i > b.c[5].i
			}
			if a.c[0].s != b.c[0].s {
				return a.c[0].s < b.c[0].s
			}
			return a.id < b.id
		})
}
func qDuplicateDependencyVersions(q *qctx) *result {
	g := q.g
	type agg struct {
		versions, decls, dev int32
		vset                 map[string]bool
		vorder               []string
	}
	aggs := map[string]*agg{}
	var names []string
	for i := range g.Deps {
		d := &g.Deps[i]
		a, ok := aggs[d.Name()]
		if !ok {
			a = &agg{vset: map[string]bool{}}
			aggs[d.Name()] = a
			names = append(names, d.Name())
		}
		if !a.vset[d.Version()] {
			a.vset[d.Version()] = true
			a.vorder = append(a.vorder, d.Version())
			a.versions++
		}
		a.decls++
		a.dev += d.IsDev
	}
	r := &result{cols: []string{"name", "versions", "version_list",
		"declarations", "dev_declarations"}}
	var rs []rowRec
	for _, n := range names {
		a := aggs[n]
		if a.versions <= 1 {
			continue
		}
		rs = append(rs, rowRec{c: []cell{cs(n), ci32(a.versions),
			cs(groupConcatDistinct(a.vorder)), ci32(a.decls), ci32(a.dev)}})
	}
	sortRows(rs, func(a, b *rowRec) bool {
		if a.c[1].i != b.c[1].i {
			return a.c[1].i > b.c[1].i
		}
		if a.c[3].i != b.c[3].i {
			return a.c[3].i > b.c[3].i
		}
		if a.c[0].s != b.c[0].s {
			return a.c[0].s < b.c[0].s
		}
		return false
	})
	fill(r, rs)
	return r
}
func qNeedlesslyAsyncFn(q *qctx) *result {
	return q.simple([]string{"name", "on_type", "awaits", "async_blocks",
		"trait_method", "pub_", "fan_in", "at"},
		func(sid int32) bool {
			return q.mv(sid, cIsAsyncFn) == 1 && q.mv(sid, cNAwait) == 0 &&
				q.mv(sid, cNAsyncBlocks) == 0 && q.mv(sid, cIsTest) == 0 &&
				!sFileTest[sid] && !sFileGen[sid]
		},
		func(sid int32) []cell {
			return []cell{cs(q.name(sid)), cs(q.impl(sid)),
				ci32(q.mv(sid, cNAwait)), ci32(q.mv(sid, cNAsyncBlocks)),
				ci32(q.mv(sid, cIsTraitMethod)), ci32(q.mv(sid, cIsPublic)),
				ci32(q.mv(sid, cFanIn)), cs(q.at(sid))}
		},
		func(a, b *rowRec) bool {
			if a.c[6].i != b.c[6].i {
				return a.c[6].i > b.c[6].i
			}
			if a.c[7].i != b.c[7].i {
				return a.c[7].i > b.c[7].i
			}
			return a.id < b.id
		})
}
func qAllocationLoopUnderPubAPI(q *qctx) *result {
	ts := q.reachPairs(4,
		func(sid int32) bool {
			return (q.mv(sid, cIsPublic) == 1 || q.mv(sid, cIsEntrypoint) == 1) &&
				(q.isKind(sid, kFunction) || q.isKind(sid, kMethod)) &&
				q.mv(sid, cIsTest) == 0
		},
		func(root, sym, hops int32) bool {
			return hops > 0 && q.mv(sym, cIsTest) == 0 && !sFileTest[sym] &&
				!sFileGen[sym] && q.modOK(sym) &&
				(q.mv(sym, cNCloneInLoop) > 0 || q.mv(sym, cAllocInLoop) > 0 ||
					q.mv(sym, cNToOwnedInLoop) > 0)
		})
	return q.fromReach([]string{"name", "reached_from", "hops",
		"clones_in_loop", "allocs_in_loop", "to_owned_in_loop", "with_capacity",
		"fan_in", "at"}, ts,
		func(t tri) []cell {
			return []cell{cs(q.name(t.sym)), cs(q.name(t.root)), ci32(t.hops),
				ci32(q.mv(t.sym, cNCloneInLoop)), ci32(q.mv(t.sym, cAllocInLoop)),
				ci32(q.mv(t.sym, cNToOwnedInLoop)),
				ci32(q.mv(t.sym, cNWithCapacity)), ci32(q.mv(t.sym, cFanIn)),
				cs(q.at(t.sym))}
		},
		func(a, b *rowRec) bool {
			x := a.c[3].i + a.c[4].i
			y := b.c[3].i + b.c[4].i
			if x != y {
				return x > y
			}
			if a.c[2].i != b.c[2].i {
				return a.c[2].i < b.c[2].i
			}
			if a.x != b.x {
				return a.x < b.x
			}
			return a.id < b.id
		})
}
func qRCInPublicSignature(q *qctx) *result {
	g := q.g
	r := &result{cols: []string{"name", "param", "param_type", "pub_", "fan_in",
		"at"}}
	var rs []rowRec
	for i := range g.Params {
		p := &g.Params[i]
		sid := p.SymID
		if q.mv(sid, cIsPublic) != 1 {
			continue
		}
		t := p.Type()
		if !(likeSubstr(t, "Rc<") || likeSubstr(t, "Rc <") ||
			likeSubstr(t, "RefCell<") || likeSubstr(t, "RefCell <") ||
			likeSubstr(t, "rc::Rc<") || likeSubstr(t, "cell::RefCell<")) {
			continue
		}
		if q.mv(sid, cIsTest) == 1 || sFileTest[sid] || sFileGen[sid] ||
			!q.modOK(sid) {
			continue
		}
		rs = append(rs, rowRec{id: sid, c: []cell{cs(q.name(sid)), cs(p.Name()), cs(t),
			ci32(1), ci32(q.mv(sid, cFanIn)), cs(q.at(sid))}})
	}
	sortRows(rs, func(a, b *rowRec) bool {
		if a.c[4].i != b.c[4].i {
			return a.c[4].i > b.c[4].i
		}
		if a.c[0].s != b.c[0].s {
			return a.c[0].s < b.c[0].s
		}
		fa, fb := q.g.SymFile[a.id-1], q.g.SymFile[b.id-1]
		if fa != fb {
			return fa < fb
		}
		return a.id < b.id
	})
	fill(r, rs)
	return r
}
func qPtrArgSurface(q *qctx) *result {
	g := q.g
	r := &result{cols: []string{"name", "param", "param_type", "pub_", "fan_in",
		"at"}}
	var rs []rowRec
	for i := range g.Params {
		p := &g.Params[i]
		sid := p.SymID
		t := p.Type()
		if !(likeSubstr(t, "&mut Vec<") || likeSubstr(t, "&mut Vec <") ||
			likeSubstr(t, "&mut String") || likeSubstr(t, "&mut PathBuf") ||
			likeSubstr(t, "&mut HashMap<") || likeSubstr(t, "&mut HashSet<")) {
			continue
		}
		if q.mv(sid, cIsTest) == 1 || sFileTest[sid] || sFileGen[sid] ||
			!q.modOK(sid) {
			continue
		}
		rs = append(rs, rowRec{id: sid, c: []cell{cs(q.name(sid)), cs(p.Name()), cs(t),
			ci32(q.mv(sid, cIsPublic)), ci32(q.mv(sid, cFanIn)), cs(q.at(sid))}})
	}
	sortRows(rs, func(a, b *rowRec) bool {
		if a.c[4].i != b.c[4].i {
			return a.c[4].i > b.c[4].i
		}
		sa, sb := q.mv(a.id, cSloc), q.mv(b.id, cSloc)
		if sa != sb {
			return sa > sb
		}
		fa, fb := q.g.SymFile[a.id-1], q.g.SymFile[b.id-1]
		if fa != fb {
			return fa < fb
		}
		la, lb := q.g.SymLine[a.id-1], q.g.SymLine[b.id-1]
		if la != lb {
			return la < lb
		}
		return a.id < b.id
	})
	fill(r, rs)
	return r
}
func qTestOnlyCallers(q *qctx) *result {
	g := q.g
	fromTests := map[int32]int32{}
	for i := range g.Edges {
		e := &g.Edges[i]
		c := e.Caller
		if c < 1 || int(c) > g.N() {
			continue
		}
		if sFileTest[c] || q.mv(c, cIsTest) == 1 {
			fromTests[e.Callee]++
		}
	}
	return q.simple([]string{"name", "on_type", "callers_total", "from_tests",
		"pub_", "at"},
		func(sid int32) bool {
			if !q.isKind(sid, kFunction, kMethod) {
				return false
			}
			return q.mv(sid, cFanIn) > 0 && fromTests[sid] == q.mv(sid, cFanIn) &&
				q.mv(sid, cIsTest) == 0 && !sFileTest[sid] && !sFileGen[sid]
		},
		func(sid int32) []cell {
			return []cell{cs(q.name(sid)), cs(q.impl(sid)),
				ci32(q.mv(sid, cFanIn)), ci32(fromTests[sid]),
				ci32(q.mv(sid, cIsPublic)), cs(q.at(sid))}
		},
		func(a, b *rowRec) bool {
			if a.c[2].i != b.c[2].i {
				return a.c[2].i > b.c[2].i
			}
			if a.c[0].s != b.c[0].s {
				return a.c[0].s < b.c[0].s
			}
			return a.id < b.id
		})
}

var _ = strings.HasPrefix

func mGraphBlindspots(q *qctx) *result {
	g := q.g
	groups := q.modGroups([]int{cNCalls, cNExternalCalls, cNUnresolvedCalls,
		cNBoxDyn, cNDynParams, cNMacroInvocations, cNImplTrait},
		[]string{kFunction, kMethod, kClosure}, false, false)
	dyn := map[int32]int32{}
	macro := map[int32]int32{}
	for sid := int32(1); sid <= int32(g.N()); sid++ {
		if !q.isKind(sid, kFunction, kMethod, kClosure) {
			continue
		}
		dyn[g.SymModule[sid-1]] += q.mv(sid, cNBoxDyn) + q.mv(sid, cNDynParams)
		macro[g.SymModule[sid-1]] += q.mv(sid, cNMacroInvocations)
	}
	r := &result{cols: []string{"module_", "fns", "calls", "external",
		"unresolved", "dyn_sites", "macro_calls", "impl_trait", "pct_blind"}}
	var rs []rowRec
	for _, p := range groups {
		if p.cols[0] == 0 {
			continue
		}
		pct := int32(0)
		if p.cols[0] != 0 {
			pct = sqliteCastInt(100.0 * float64(p.cols[2]) / float64(p.cols[0]))
		}
		rs = append(rs, rowRec{id: p.id, c: []cell{cs(g.modName(p.id)),
			ci32(p.nSyms), ci32(p.cols[0]), ci32(p.cols[1]), ci32(p.cols[2]),
			ci32(dyn[p.id]), ci32(macro[p.id]), ci32(p.cols[6]), ci32(pct)}})
	}
	sortRows(rs, func(a, b *rowRec) bool {
		if a.c[4].i != b.c[4].i {
			return a.c[4].i > b.c[4].i
		}
		if a.c[5].i != b.c[5].i {
			return a.c[5].i > b.c[5].i
		}
		return a.id < b.id
	})
	fill(r, rs)
	return r
}
func mCloneChurnPerIteration(q *qctx) *result {
	return q.simple([]string{"name", "on_type", "clones_in_loop", "allocs_in_loop",
		"clones_total", "to_owned", "collects", "formats", "with_capacity",
		"adapters", "depth", "fan_in", "churn", "at"},
		func(sid int32) bool {
			return q.mv(sid, cMaxLoopDepth) > 0 &&
				(q.mv(sid, cNCloneInLoop)+q.mv(sid, cAllocInLoop)) > 0 &&
				!sFileTest[sid] && !sFileGen[sid]
		},
		func(sid int32) []cell {
			churn := (q.mv(sid, cNCloneInLoop)*4 + q.mv(sid, cAllocInLoop)*3 +
				q.mv(sid, cNFormatMacro)*2 + q.mv(sid, cNCollect)*2) *
				(1 + q.mv(sid, cMaxLoopDepth)) * q.max1(q.mv(sid, cFanIn))
			return []cell{cs(q.name(sid)), cs(q.impl(sid)),
				ci32(q.mv(sid, cNCloneInLoop)), ci32(q.mv(sid, cAllocInLoop)),
				ci32(q.mv(sid, cNClone)), ci32(q.mv(sid, cNToOwned)),
				ci32(q.mv(sid, cNCollect)), ci32(q.mv(sid, cNFormatMacro)),
				ci32(q.mv(sid, cNWithCapacity)), ci32(q.mv(sid, cNIterAdapters)),
				ci32(q.mv(sid, cMaxLoopDepth)), ci32(q.mv(sid, cFanIn)),
				ci(int64(churn)), cs(q.at(sid))}
		},
		func(a, b *rowRec) bool {
			if a.c[12].i != b.c[12].i {
				return a.c[12].i > b.c[12].i
			}
			return a.id < b.id
		})
}
func mDynWithOneImpl(q *qctx) *result {
	g := q.g
	dynParams := map[int32]int32{}
	for i := range g.Params {
		p := &g.Params[i]
		for _, w := range dynWords(p.Type()) {
			dynParams[hashStr(w)]++
		}
	}
	boxDyn := map[int32]int32{}
	for sid := int32(1); sid <= int32(g.N()); sid++ {
		for _, w := range dynWords(g.SymSig[sid-1].Str()) {
			boxDyn[hashStr(w)] += q.mv(sid, cNBoxDyn)
			break
		}
	}
	implsByTrait := map[string][]string{}
	for i := range g.Impls {
		im := &g.Impls[i]
		if im.TraitName() == "" {
			continue
		}
		implsByTrait[im.TraitName()] = append(implsByTrait[im.TraitName()],
			im.TypeName())
	}
	r := &result{cols: []string{"trait_", "required_methods", "default_methods",
		"pub_", "assoc_type", "impls_found", "implementors", "blanket_impl",
		"dyn_params", "box_dyn_sites", "at"}}
	var rs []rowRec
	for i := range g.Traits {
		t := &g.Traits[i]
		if sFileTest[t.SymID] || !q.modOK(t.SymID) {
			continue
		}
		var nImpl, blanket int32
		var names []string
		for _, tn := range implsByTrait[t.Name()] {
			nImpl++
			names = append(names, tn)
		}
		for j := range g.Impls {
			if g.Impls[j].TraitName() == t.Name() && g.Impls[j].IsGeneric == 1 {
				blanket = 1
			}
		}
		dp := dynParams[hashStr(t.Name())]
		bd := boxDyn[hashStr(t.Name())]
		if nImpl > 1 || (dp == 0 && bd == 0) {
			continue
		}
		rs = append(rs, rowRec{id: t.SymID, c: []cell{cs(t.Name()),
			ci32(t.NRequired), ci32(t.NProvided), ci32(t.IsPublic),
			ci32(t.HasAssocType), ci32(nImpl),
			groupConcatSortedOrNull(names), ci32(blanket), ci32(dp), ci32(bd),
			cs(q.at(t.SymID))}})
	}
	sortRows(rs, func(a, b *rowRec) bool {
		if a.c[8].i != b.c[8].i {
			return a.c[8].i > b.c[8].i
		}
		if a.c[9].i != b.c[9].i {
			return a.c[9].i > b.c[9].i
		}
		return a.id < b.id
	})
	fill(r, rs)
	return r
}
func dynWords(s string) []string {
	var out []string
	for {
		i := strings.Index(s, "dyn ")
		if i < 0 {
			return out
		}
		rest := s[i+4:]
		j := 0
		for j < len(rest) {
			c := rest[j]
			if c == '_' || (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') ||
				(c >= '0' && c <= '9') {
				j++
				continue
			}
			break
		}
		if j > 0 {
			out = append(out, rest[:j])
		}
		s = rest
	}
}
func mMonoBlastRadius(q *qctx) *result {
	return q.simple([]string{"name", "on_type", "type_params", "bounds",
		"where_preds", "hrtb", "turbofish_calls", "instantiations",
		"body_bytes", "sloc", "fan_in", "inline_attr", "est_bloat", "at"},
		func(sid int32) bool {
			return q.mv(sid, cNGenericParams) > 0 &&
				q.isKind(sid, kFunction, kMethod) && !sFileTest[sid] &&
				!sFileGen[sid]
		},
		func(sid int32) []cell {
			bloat := q.mv(sid, cBodyBytes) * q.max1(q.mv(sid, cNMonoInstantiations))
			return []cell{cs(q.name(sid)), cs(q.impl(sid)),
				ci32(q.mv(sid, cNGenericParams)), ci32(q.mv(sid, cNTraitBounds)),
				ci32(q.mv(sid, cNWherePredicates)), ci32(q.mv(sid, cNHrtb)),
				ci32(q.mv(sid, cNTurbofish)),
				ci32(q.mv(sid, cNMonoInstantiations)),
				ci32(q.mv(sid, cBodyBytes)), ci32(q.mv(sid, cSloc)),
				ci32(q.mv(sid, cFanIn)), ci32(q.mv(sid, cNInlineAttrs)),
				ci(int64(bloat)), cs(q.at(sid))}
		},
		func(a, b *rowRec) bool {
			if a.c[12].i != b.c[12].i {
				return a.c[12].i > b.c[12].i
			}
			return a.id < b.id
		})
}
func mCfgFeatureNobodyBuilds(q *qctx) *result {
	g := q.g
	declared := map[string]int32{}
	for i := range g.Feat {
		declared[g.Feat[i].Name()]++
	}
	type agg struct {
		sites, files, testGated, attrOnly, syms, sloc int32
		paths                                         map[int32]bool
		fileOrder                                     []int32
		seenFile                                      map[int32]bool
		seenSym                                       map[int32]bool
	}
	aggs := map[string]*agg{}
	var names []string
	for i := range g.CfgBlocks {
		c := &g.CfgBlocks[i]
		if c.Feature() == "" {
			continue
		}
		if !likeMatch(q.mod, g.modName(g.Files[c.FileID-1].ModuleID)) {
			continue
		}
		a, ok := aggs[c.Feature()]
		if !ok {
			a = &agg{paths: map[int32]bool{}, seenFile: map[int32]bool{},
				seenSym: map[int32]bool{}}
			aggs[c.Feature()] = a
			names = append(names, c.Feature())
		}
		a.sites++
		if !a.seenFile[c.FileID] {
			a.seenFile[c.FileID] = true
			a.files++
		}
		a.testGated += c.IsTest
		a.attrOnly += c.IsAttrOnly
		if c.SymID > 0 && int(c.SymID) <= g.N() {
			if !a.seenSym[c.SymID] {
				a.seenSym[c.SymID] = true
				a.syms++
			}
			a.sloc += q.mv(c.SymID, cSloc)
		}
		if !a.paths[c.FileID] {
			a.paths[c.FileID] = true
			a.fileOrder = append(a.fileOrder, c.FileID)
		}
	}
	r := &result{cols: []string{"feature", "cfg_sites", "files_",
		"declared_in_manifest", "test_gated", "cfg_attr_only",
		"symbols_behind_it", "sloc_behind_it", "in_files"}}
	var rs []rowRec
	for _, n := range names {
		a := aggs[n]
		if declared[n] != 0 {
			continue
		}
		paths := make([]string, 0, len(a.fileOrder))
		for _, fid := range a.fileOrder {
			paths = append(paths, g.Files[fid-1].Path())
		}
		rs = append(rs, rowRec{c: []cell{cs(n), ci32(a.sites), ci32(a.files),
			ci32(0), ci32(a.testGated), ci32(a.attrOnly), ci32(a.syms),
			ci32(a.sloc), cs(groupConcatDistinct(paths))}})
	}
	sortRows(rs, func(a, b *rowRec) bool {
		if a.c[7].i != b.c[7].i {
			return a.c[7].i > b.c[7].i
		}
		if a.c[1].i != b.c[1].i {
			return a.c[1].i > b.c[1].i
		}
		if a.c[0].s != b.c[0].s {
			return a.c[0].s < b.c[0].s
		}
		return false
	})
	fill(r, rs)
	return r
}
func mAllocChurnCollectAndFormat(q *qctx) *result {
	return q.simple([]string{"name", "impl_", "collects", "formats", "adapters",
		"with_capacity", "to_owned", "depth", "fan_in", "at"},
		func(sid int32) bool {
			return (q.mv(sid, cNCollect) > 0 || q.mv(sid, cNFormatMacro) > 0) &&
				q.mv(sid, cMaxLoopDepth) > 0 && !sFileTest[sid]
		},
		func(sid int32) []cell {
			return []cell{cs(q.name(sid)), cs(q.impl(sid)),
				ci32(q.mv(sid, cNCollect)), ci32(q.mv(sid, cNFormatMacro)),
				ci32(q.mv(sid, cNIterAdapters)), ci32(q.mv(sid, cNWithCapacity)),
				ci32(q.mv(sid, cNToOwned)), ci32(q.mv(sid, cMaxLoopDepth)),
				ci32(q.mv(sid, cFanIn)), cs(q.at(sid))}
		},
		func(a, b *rowRec) bool {
			x := (a.c[2].i + a.c[3].i) * (1 + a.c[6].i) * (1 + a.c[7].i)
			y := (b.c[2].i + b.c[3].i) * (1 + b.c[6].i) * (1 + b.c[7].i)
			if x != y {
				return x > y
			}
			return a.id < b.id
		})
}
func mDynamicDispatchCost(q *qctx) *result {
	return q.simple([]string{"name", "impl_", "box_dyn", "dyn_params",
		"impl_trait", "fan_in", "depth", "calls_in_loop", "at"},
		func(sid int32) bool {
			return (q.mv(sid, cNBoxDyn) > 0 || q.mv(sid, cNDynParams) > 0) &&
				!sFileTest[sid]
		},
		func(sid int32) []cell {
			return []cell{cs(q.name(sid)), cs(q.impl(sid)),
				ci32(q.mv(sid, cNBoxDyn)), ci32(q.mv(sid, cNDynParams)),
				ci32(q.mv(sid, cNImplTrait)), ci32(q.mv(sid, cFanIn)),
				ci32(q.mv(sid, cMaxLoopDepth)), ci32(q.mv(sid, cCallInLoop)),
				cs(q.at(sid))}
		},
		func(a, b *rowRec) bool {
			x := (a.c[2].i + a.c[3].i) * (1 + a.c[5].i) * (1 + a.c[7].i)
			y := (b.c[2].i + b.c[3].i) * (1 + b.c[5].i) * (1 + b.c[7].i)
			if x != y {
				return x > y
			}
			return a.id < b.id
		})
}
func mHotMultipliers(q *qctx) *result {
	return q.simple([]string{"name", "fan_in", "sites", "fan_out", "cyclo",
		"sloc", "kind", "module_", "at"},
		func(sid int32) bool { return q.mv(sid, cFanIn) > 0 },
		func(sid int32) []cell {
			return []cell{cs(q.name(sid)), ci32(q.mv(sid, cFanIn)),
				ci32(q.mv(sid, cNCallsites)), ci32(q.mv(sid, cFanOut)),
				ci32(q.mv(sid, cCyclomatic)), ci32(q.mv(sid, cSloc)),
				cs(q.g.SymKind[sid-1].Str()), cs(q.g.ModName[sid-1]), cs(q.at(sid))}
		},
		func(a, b *rowRec) bool {
			if a.c[1].i != b.c[1].i {
				return a.c[1].i > b.c[1].i
			}
			if a.c[4].i != b.c[4].i {
				return a.c[4].i > b.c[4].i
			}
			pa, pb := sFilePath[a.id], sFilePath[b.id]
			if pa != pb {
				return pa < pb
			}
			la, lb := q.g.SymLine[a.id-1], q.g.SymLine[b.id-1]
			if la != lb {
				return la < lb
			}
			return a.id < b.id
		})
}
func mRiskRanked(q *qctx) *result {
	return q.simple([]string{"name", "risk", "cyclo", "cog", "nest", "hazards",
		"fan_in", "sloc", "at"},
		func(sid int32) bool { return q.mv(sid, cRiskScore) > 0 && !sFileGen[sid] },
		func(sid int32) []cell {
			return []cell{cs(q.name(sid)), ci32(q.mv(sid, cRiskScore)),
				ci32(q.mv(sid, cCyclomatic)), ci32(q.mv(sid, cCognitive)),
				ci32(q.mv(sid, cMaxNesting)), ci32(q.mv(sid, cNHazards)),
				ci32(q.mv(sid, cFanIn)), ci32(q.mv(sid, cSloc)), cs(q.at(sid))}
		},
		func(a, b *rowRec) bool {
			if a.c[1].i != b.c[1].i {
				return a.c[1].i > b.c[1].i
			}
			fa, fb := q.g.SymFile[a.id-1], q.g.SymFile[b.id-1]
			if fa != fb {
				return fa < fb
			}
			la, lb := q.g.SymLine[a.id-1], q.g.SymLine[b.id-1]
			if la != lb {
				return la < lb
			}
			return a.id < b.id
		})
}
func mParseCoverage(q *qctx) *result {
	g := q.g
	r := &result{cols: []string{"path", "lines", "bytes", "error_nodes",
		"missing", "parsed", "generated", "test", "vendored"}}
	var rs []rowRec
	for i := range g.Files {
		f := &g.Files[i]
		if f.NParseErrors == 0 && f.Parsed == 1 {
			continue
		}
		if !likeMatch(q.mod, g.modName(f.ModuleID)) {
			continue
		}
		rs = append(rs, rowRec{id: f.ID, c: []cell{cs(f.Path()), ci32(f.Lines),
			ci32(f.Bytes), ci32(f.NParseErrors), ci32(f.NMissingNodes),
			ci32(f.Parsed), ci32(f.IsGenerated), ci32(f.IsTest),
			ci32(f.IsVendored)}})
	}
	sortRows(rs, func(a, b *rowRec) bool {
		if a.c[3].i != b.c[3].i {
			return a.c[3].i > b.c[3].i
		}
		if a.c[1].i != b.c[1].i {
			return a.c[1].i > b.c[1].i
		}
		return a.id < b.id
	})
	fill(r, rs)
	return r
}
func mBoxDynOveruse(q *qctx) *result {
	return q.simple([]string{"name", "box_dyns", "dyn_params", "impl_traits",
		"fan_in", "cyclo", "at"},
		func(sid int32) bool { return q.mv(sid, cNBoxDyn) > 2 && !sFileTest[sid] },
		func(sid int32) []cell {
			return []cell{cs(q.name(sid)), ci32(q.mv(sid, cNBoxDyn)),
				ci32(q.mv(sid, cNDynParams)), ci32(q.mv(sid, cNImplTrait)),
				ci32(q.mv(sid, cFanIn)), ci32(q.mv(sid, cCyclomatic)),
				cs(q.at(sid))}
		},
		func(a, b *rowRec) bool {
			if a.c[1].i != b.c[1].i {
				return a.c[1].i > b.c[1].i
			}
			if a.c[4].i != b.c[4].i {
				return a.c[4].i > b.c[4].i
			}
			return a.id < b.id
		})
}
func mDeepNesting(q *qctx) *result {
	return q.simple([]string{"name", "nesting", "cyclo", "cognitive",
		"match_arms", "sloc", "fan_in", "at"},
		func(sid int32) bool {
			return q.mv(sid, cMaxNesting) > 4 && q.isKind(sid, kFunction, kMethod) &&
				!sFileTest[sid]
		},
		func(sid int32) []cell {
			return []cell{cs(q.name(sid)), ci32(q.mv(sid, cMaxNesting)),
				ci32(q.mv(sid, cCyclomatic)), ci32(q.mv(sid, cCognitive)),
				ci32(q.mv(sid, cNMatchArms)), ci32(q.mv(sid, cSloc)),
				ci32(q.mv(sid, cFanIn)), cs(q.at(sid))}
		},
		func(a, b *rowRec) bool {
			if a.c[1].i != b.c[1].i {
				return a.c[1].i > b.c[1].i
			}
			if a.c[2].i != b.c[2].i {
				return a.c[2].i > b.c[2].i
			}
			return a.id < b.id
		})
}
func mTooManyParams(q *qctx) *result {
	return q.simple([]string{"name", "n_params", "n_generic_params", "sloc",
		"cyclo", "fan_in", "at"},
		func(sid int32) bool {
			return q.mv(sid, cNParams) > 7 && q.isKind(sid, kFunction, kMethod) &&
				!sFileTest[sid]
		},
		func(sid int32) []cell {
			return []cell{cs(q.name(sid)), ci32(q.mv(sid, cNParams)),
				ci32(q.mv(sid, cNGenericParams)), ci32(q.mv(sid, cSloc)),
				ci32(q.mv(sid, cCyclomatic)), ci32(q.mv(sid, cFanIn)),
				cs(q.at(sid))}
		},
		func(a, b *rowRec) bool {
			if a.c[1].i != b.c[1].i {
				return a.c[1].i > b.c[1].i
			}
			if a.c[5].i != b.c[5].i {
				return a.c[5].i > b.c[5].i
			}
			return a.id < b.id
		})
}
func mScatteredConcerns(q *qctx) *result {
	g := q.g
	mods := map[int32]map[int32]bool{}
	for i := range g.Edges {
		e := &g.Edges[i]
		if e.IsSelf != 0 {
			continue
		}
		k := e.Callee
		if k < 1 || int(k) > g.N() {
			continue
		}
		if !q.isKind(k, kFunction, kMethod) || sFileTest[k] {
			continue
		}
		if mods[k] == nil {
			mods[k] = map[int32]bool{}
		}
		mods[k][g.SymModule[e.Caller-1]] = true
	}
	r := &result{cols: []string{"name", "n_caller_modules", "fan_in", "cyclo",
		"sloc", "modules", "at"}}
	var rs []rowRec
	for sid := int32(1); sid <= int32(g.N()); sid++ {
		if !q.isKind(sid, kFunction, kMethod) || sFileTest[sid] {
			continue
		}
		if !likeMatch(q.mod, g.ModName[sid-1]) {
			continue
		}
		n := int32(len(mods[sid]))
		if n <= 5 {
			continue
		}
		ids := make([]int32, 0, len(mods[sid]))
		for m := range mods[sid] {
			ids = append(ids, m)
		}
		slices.Sort(ids)
		names := make([]string, 0, len(ids))
		for _, m := range ids {
			names = append(names, g.modName(m))
		}
		rs = append(rs, rowRec{id: sid, c: []cell{cs(q.name(sid)), ci32(n),
			ci32(q.mv(sid, cFanIn)), ci32(q.mv(sid, cCyclomatic)),
			ci32(q.mv(sid, cSloc)), cs(groupConcatDistinct(names)),
			cs(q.at(sid))}})
	}
	sortRows(rs, func(a, b *rowRec) bool {
		if a.c[1].i != b.c[1].i {
			return a.c[1].i > b.c[1].i
		}
		if a.c[2].i != b.c[2].i {
			return a.c[2].i > b.c[2].i
		}
		return a.id < b.id
	})
	fill(r, rs)
	return r
}
func mUnsafeDensity(q *qctx) *result {
	g := q.g
	groups := q.modGroups([]int{cNUnsafeBlocks, cNUnsafeOps, cNTransmute,
		cNRawPtr, cSloc}, []string{kFunction, kMethod}, true, true)
	fnsUnsafe := map[int32]int32{}
	undoc := map[int32]int32{}
	for sid := int32(1); sid <= int32(g.N()); sid++ {
		if !q.isKind(sid, kFunction, kMethod) || sFileTest[sid] || sFileGen[sid] {
			continue
		}
		if q.mv(sid, cNUnsafeBlocks) > 0 {
			fnsUnsafe[g.SymModule[sid-1]]++
		}
		undoc[g.SymModule[sid-1]] += q.mv(sid, cNUnsafeBlocks) -
			q.mv(sid, cNSafetyComments)
	}
	r := &result{cols: []string{"module_", "fns_total", "fns_unsafe",
		"unsafe_blocks", "unsafe_ops", "undocumented_blocks", "transmutes",
		"raw_ptrs", "sloc_", "ops_per_ksloc"}}
	var rs []rowRec
	for _, p := range groups {
		if p.cols[0] == 0 {
			continue
		}
		rs = append(rs, rowRec{id: p.id, c: []cell{cs(g.modName(p.id)), ci32(p.nSyms),
			ci32(fnsUnsafe[p.id]), ci32(p.cols[0]), ci32(p.cols[1]),
			ci32(undoc[p.id]), ci32(p.cols[2]), ci32(p.cols[3]), ci32(p.cols[4]),
			castOverNull(p.cols[1], p.cols[4])}})
	}
	sortRows(rs, func(a, b *rowRec) bool {
		if a.c[4].i != b.c[4].i {
			return a.c[4].i > b.c[4].i
		}
		if a.c[5].i != b.c[5].i {
			return a.c[5].i > b.c[5].i
		}
		return a.id < b.id
	})
	fill(r, rs)
	return r
}
func mAsyncBlockingRatio(q *qctx) *result {
	g := q.g
	groups := q.modGroups([]int{cNAwait, cNSpawn, cNSpawnBlocking,
		cNBlockingIO, cNBlockingInAsync, cNLockAcrossAwait, cNThreadSleep,
		cNBlockOn}, []string{kFunction, kMethod}, true, true)
	asyncFns := map[int32]int32{}
	for sid := int32(1); sid <= int32(g.N()); sid++ {
		if !q.isKind(sid, kFunction, kMethod) || sFileTest[sid] || sFileGen[sid] {
			continue
		}
		if q.mv(sid, cIsAsyncFn) == 1 {
			asyncFns[g.SymModule[sid-1]]++
		}
	}
	r := &result{cols: []string{"module_", "async_fns", "awaits", "spawns",
		"spawn_blocking", "blocking_io", "blocking_in_async",
		"guards_across_await", "sleeps", "block_ons",
		"pct_blocking_in_async"}}
	var rs []rowRec
	for _, p := range groups {
		if asyncFns[p.id] == 0 && p.cols[3] == 0 {
			continue
		}
		rs = append(rs, rowRec{id: p.id, c: []cell{cs(g.modName(p.id)),
			ci32(asyncFns[p.id]), ci32(p.cols[0]), ci32(p.cols[1]), ci32(p.cols[2]),
			ci32(p.cols[3]), ci32(p.cols[4]), ci32(p.cols[5]), ci32(p.cols[6]),
			ci32(p.cols[7]), castPctOverNull(p.cols[4], p.cols[3])}})
	}
	sortRows(rs, func(a, b *rowRec) bool {
		if a.c[6].i != b.c[6].i {
			return a.c[6].i > b.c[6].i
		}
		if a.c[5].i != b.c[5].i {
			return a.c[5].i > b.c[5].i
		}
		return a.id < b.id
	})
	fill(r, rs)
	return r
}
func mPanicDensity(q *qctx) *result {
	g := q.g
	groups := q.modGroups([]int{cNUnwrap, cNExpect, cNPanicMacro, cNIndexExpr,
		cNSliceRange, cNBorrowCalls, cNSafeFallback, cSloc},
		[]string{kFunction, kMethod}, true, true)
	panicky := map[int32]int32{}
	for sid := int32(1); sid <= int32(g.N()); sid++ {
		if !q.isKind(sid, kFunction, kMethod) || sFileTest[sid] || sFileGen[sid] {
			continue
		}
		if q.mv(sid, cNUnwrap)+q.mv(sid, cNExpect)+q.mv(sid, cNPanicMacro) > 0 {
			panicky[g.SymModule[sid-1]]++
		}
	}
	r := &result{cols: []string{"module_", "fns_panicky", "unwraps", "expects",
		"panic_macros", "index_ops", "slices", "refcell_borrows",
		"safe_fallbacks", "sloc_", "panics_per_ksloc"}}
	var rs []rowRec
	for _, p := range groups {
		if p.cols[0]+p.cols[1]+p.cols[2]+p.cols[3] == 0 {
			continue
		}
		rs = append(rs, rowRec{id: p.id, c: []cell{cs(g.modName(p.id)),
			ci32(panicky[p.id]), ci32(p.cols[0]), ci32(p.cols[1]), ci32(p.cols[2]),
			ci32(p.cols[3]), ci32(p.cols[4]), ci32(p.cols[5]), ci32(p.cols[6]),
			ci32(p.cols[7]), castOverNull(p.cols[0]+p.cols[1]+p.cols[2]+p.cols[3],
				p.cols[7])}})
	}
	sortRows(rs, func(a, b *rowRec) bool {
		if a.c[10].i != b.c[10].i {
			return a.c[10].i > b.c[10].i
		}
		if a.c[2].i != b.c[2].i {
			return a.c[2].i > b.c[2].i
		}
		return a.id < b.id
	})
	fill(r, rs)
	return r
}
func mTraitCoupling(q *qctx) *result {
	g := q.g
	implCount := map[string]int32{}
	implNames := map[string][]string{}
	for i := range g.Impls {
		im := &g.Impls[i]
		if im.TraitName() == "" {
			continue
		}
		implCount[im.TraitName()]++
		implNames[im.TraitName()] = append(implNames[im.TraitName()], im.TypeName())
	}
	boundUsers := map[string]map[int32]bool{}
	boundWhere := map[string]int32{}
	for i := range g.GenBounds {
		b := &g.GenBounds[i]
		appendSet(boundUsers, b.Bound(), b.SymID)
		boundWhere[b.Bound()] += b.InWhere
	}
	r := &result{cols: []string{"trait_", "required_methods", "pub_", "impls",
		"generic_users", "where_clauses", "implementors", "at"}}
	var rs []rowRec
	for i := range g.Traits {
		t := &g.Traits[i]
		if sFileTest[t.SymID] || !q.modOK(t.SymID) {
			continue
		}
		nImpl := implCount[t.Name()]
		nUsers := int32(len(boundUsers[t.Name()]))
		if nImpl+nUsers == 0 {
			continue
		}
		rows := nImpl
		if rows == 0 {
			rows = 1
		}
		where := boundWhere[t.Name()] * rows
		rs = append(rs, rowRec{id: t.SymID, c: []cell{cs(t.Name()), ci32(t.NRequired),
			ci32(t.IsPublic), ci32(nImpl), ci32(nUsers),
			ci32(where),
			groupConcatSortedOrNull(implNames[t.Name()]), cs(q.at(t.SymID))}})
	}
	sortRows(rs, func(a, b *rowRec) bool {
		if a.c[3].i != b.c[3].i {
			return a.c[3].i > b.c[3].i
		}
		if a.c[4].i != b.c[4].i {
			return a.c[4].i > b.c[4].i
		}
		return a.id < b.id
	})
	fill(r, rs)
	return r
}
func appendSet(m map[string]map[int32]bool, k string, v int32) map[int32]bool {
	if m[k] == nil {
		m[k] = map[int32]bool{}
	}
	m[k][v] = true
	return m[k]
}
func mAwaitRiskDensity(q *qctx) *result {
	g := q.g
	type agg struct {
		syms, points, inLoop, guards, drops, refcell int32
		seenSym                                      map[int32]bool
	}
	aggs := map[int32]*agg{}
	var order []int32
	for i := range g.AsyncPoints {
		a := &g.AsyncPoints[i]
		if sFileTest[a.SymID] {
			continue
		}
		m := g.SymModule[a.SymID-1]
		if m < 0 || !likeMatch(q.mod, g.modName(m)) {
			continue
		}
		ag, ok := aggs[m]
		if !ok {
			ag = &agg{seenSym: map[int32]bool{}}
			aggs[m] = ag
			order = append(order, m)
		}
		if !ag.seenSym[a.SymID] {
			ag.seenSym[a.SymID] = true
			ag.syms++
		}
		ag.points++
		ag.inLoop += a.InLoop
		ag.guards += a.NGuardsLive
		ag.drops += a.GuardDropped
		ag.refcell += a.HasRefcellGuard
	}
	r := &result{cols: []string{"module_", "fns_awaiting", "await_points",
		"in_loop_points", "guard_live_sites", "explicit_drops",
		"refcell_guard_sites", "pct_guarded"}}
	var rs []rowRec
	for _, m := range order {
		ag := aggs[m]
		if ag.points == 0 {
			continue
		}
		pct := int32(0)
		if ag.points != 0 {
			pct = sqliteCastInt(100.0 * float64(ag.guards) / float64(ag.points))
		}
		rs = append(rs, rowRec{id: m, c: []cell{cs(g.modName(m)), ci32(ag.syms),
			ci32(ag.points), ci32(ag.inLoop), ci32(ag.guards), ci32(ag.drops),
			ci32(ag.refcell), ci32(pct)}})
	}
	sortRows(rs, func(a, b *rowRec) bool {
		if a.c[4].i != b.c[4].i {
			return a.c[4].i > b.c[4].i
		}
		if a.c[3].i != b.c[3].i {
			return a.c[3].i > b.c[3].i
		}
		return a.id < b.id
	})
	fill(r, rs)
	return r
}
func mErrorPropagationStyle(q *qctx) *result {
	g := q.g
	groups := q.modGroups([]int{cNQuestionMark, cNUnwrap, cNExpect,
		cNErrorSwallow, cNSafeFallback}, []string{kFunction, kMethod}, true, true)
	propagating := map[int32]int32{}
	for sid := int32(1); sid <= int32(g.N()); sid++ {
		if !q.isKind(sid, kFunction, kMethod) || sFileTest[sid] || sFileGen[sid] {
			continue
		}
		if q.mv(sid, cNQuestionMark) > 0 {
			propagating[g.SymModule[sid-1]]++
		}
	}
	r := &result{cols: []string{"module_", "fns_propagating", "question_marks",
		"unwraps_expects", "swallows", "safe_fallbacks", "pct_propagated"}}
	var rs []rowRec
	for _, p := range groups {
		if p.cols[0]+p.cols[1]+p.cols[2]+p.cols[3] == 0 {
			continue
		}
		den := p.cols[0] + p.cols[1] + p.cols[2] + p.cols[3]
		pct := int32(0)
		if den != 0 {
			pct = sqliteCastInt(100.0 * float64(p.cols[0]) / float64(den))
		}
		rs = append(rs, rowRec{id: p.id, c: []cell{cs(g.modName(p.id)),
			ci32(propagating[p.id]), ci32(p.cols[0]),
			ci32(p.cols[1] + p.cols[2]), ci32(p.cols[3]), ci32(p.cols[4]),
			ci32(pct)}})
	}
	sortRows(rs, func(a, b *rowRec) bool {
		if a.c[6].i != b.c[6].i {
			return a.c[6].i < b.c[6].i
		}
		if a.c[3].i != b.c[3].i {
			return a.c[3].i > b.c[3].i
		}
		return a.id < b.id
	})
	fill(r, rs)
	return r
}
func mTaskStructure(q *qctx) *result {
	g := q.g
	groups := q.modGroups([]int{cNSpawn, cNSpawnBlocking, cNThreadSpawn,
		cNJoinCalls, cNChannelOps}, []string{kFunction, kMethod}, true, true)
	spawning := map[int32]int32{}
	for sid := int32(1); sid <= int32(g.N()); sid++ {
		if !q.isKind(sid, kFunction, kMethod) || sFileTest[sid] || sFileGen[sid] {
			continue
		}
		if q.mv(sid, cNSpawn) > 0 {
			spawning[g.SymModule[sid-1]]++
		}
	}
	r := &result{cols: []string{"module_", "spawns", "spawn_blocking",
		"thread_spawns", "joins", "channel_ops", "spawning_fns"}}
	var rs []rowRec
	for _, p := range groups {
		if p.cols[0]+p.cols[2] == 0 {
			continue
		}
		rs = append(rs, rowRec{id: p.id, c: []cell{cs(g.modName(p.id)), ci32(p.cols[0]),
			ci32(p.cols[1]), ci32(p.cols[2]), ci32(p.cols[3]), ci32(p.cols[4]),
			ci32(spawning[p.id])}})
	}
	sortRows(rs, func(a, b *rowRec) bool {
		if a.c[1].i != b.c[1].i {
			return a.c[1].i > b.c[1].i
		}
		if a.c[3].i != b.c[3].i {
			return a.c[3].i > b.c[3].i
		}
		return a.id < b.id
	})
	fill(r, rs)
	return r
}
func mMacroOpaqueBytes(q *qctx) *result {
	g := q.g
	type agg struct {
		files, inv, def, bytes int32
		seen                   map[int32]bool
	}
	aggs := map[int32]*agg{}
	var order []int32
	for i := range g.Macros {
		m := &g.Macros[i]
		fid := m.FileID
		if fid < 1 || int(fid) > len(g.Files) {
			continue
		}
		mid := g.Files[fid-1].ModuleID
		if mid < 0 || !likeMatch(q.mod, g.modName(mid)) {
			continue
		}
		a, ok := aggs[mid]
		if !ok {
			a = &agg{seen: map[int32]bool{}}
			aggs[mid] = a
			order = append(order, mid)
		}
		if !a.seen[fid] {
			a.seen[fid] = true
			a.files++
		}
		a.bytes += m.BodyBytes
		if m.Kind() == "invocation" {
			a.inv++
		} else if m.Kind() == "definition" {
			a.def++
		}
	}
	r := &result{cols: []string{"module_", "module_sloc", "files_with_macros",
		"invocations", "definitions", "hidden_bytes", "hidden_per_ksloc"}}
	var rs []rowRec
	for _, m := range order {
		a := aggs[m]
		if a.bytes == 0 {
			continue
		}
		sloc := g.Modules[m-1].Sloc
		rs = append(rs, rowRec{id: m, c: []cell{cs(g.modName(m)), ci32(sloc),
			ci32(a.files), ci32(a.inv), ci32(a.def), ci32(a.bytes),
			castOverNull(a.bytes, sloc)}})
	}
	sortRows(rs, func(a, b *rowRec) bool {
		if a.c[5].i != b.c[5].i {
			return a.c[5].i > b.c[5].i
		}
		if a.c[3].i != b.c[3].i {
			return a.c[3].i > b.c[3].i
		}
		return a.id < b.id
	})
	fill(r, rs)
	return r
}
func mAPISurfaceBloat(q *qctx) *result {
	g := q.g
	groups := q.modGroups(nil, []string{kFunction, kMethod, kStruct, kEnum,
		kTrait, kImpl}, true, true)
	pubNoCallers := map[int32]int32{}
	pubSyms := map[int32]int32{}
	for sid := int32(1); sid <= int32(g.N()); sid++ {
		if !q.isKind(sid, kFunction, kMethod, kStruct, kEnum, kTrait, kImpl) ||
			sFileTest[sid] || sFileGen[sid] {
			continue
		}
		if q.mv(sid, cIsPublic) == 1 {
			pubSyms[g.SymModule[sid-1]]++
			if q.mv(sid, cFanIn) == 0 && q.isKind(sid, kFunction, kMethod) {
				pubNoCallers[g.SymModule[sid-1]]++
			}
		}
	}
	r := &result{cols: []string{"module_", "symbols_", "pub_symbols",
		"pct_public", "pub_no_callers"}}
	var rs []rowRec
	for _, p := range groups {
		np := pubSyms[p.id]
		if np == 0 {
			continue
		}
		pct := int32(0)
		if p.nSyms != 0 {
			pct = sqliteCastInt(100.0 * float64(np) / float64(p.nSyms))
		}
		rs = append(rs, rowRec{id: p.id, c: []cell{cs(g.modName(p.id)), ci32(p.nSyms),
			ci32(np), ci32(pct), ci32(pubNoCallers[p.id])}})
	}
	sortRows(rs, func(a, b *rowRec) bool {
		if a.c[4].i != b.c[4].i {
			return a.c[4].i > b.c[4].i
		}
		if a.c[3].i != b.c[3].i {
			return a.c[3].i > b.c[3].i
		}
		return a.id < b.id
	})
	fill(r, rs)
	return r
}
func mExternalCoupling(q *qctx) *result {
	g := q.g
	type agg struct {
		extUses, distinct, wildcards int32
		crates                       map[string]bool
		targets                      map[string]bool
	}
	aggs := map[int32]*agg{}
	var order []int32
	for i := range g.Imports {
		im := &g.Imports[i]
		fid := im.FileID
		if fid < 1 || int(fid) > len(g.Files) {
			continue
		}
		m := g.Files[fid-1].ModuleID
		if m < 0 || !likeMatch(q.mod, g.modName(m)) {
			continue
		}
		a, ok := aggs[m]
		if !ok {
			a = &agg{crates: map[string]bool{}, targets: map[string]bool{}}
			aggs[m] = a
			order = append(order, m)
		}
		if im.IsExternal == 1 {
			a.extUses++
			head := im.Target()
			if j := strings.Index(head, "::"); j >= 0 {
				head = head[:j]
			}
			a.crates[head] = true
		}
		if !a.targets[im.Target()] {
			a.targets[im.Target()] = true
			a.distinct++
		}
		a.wildcards += im.IsWildcard
	}
	r := &result{cols: []string{"module_", "external_crates", "external_uses",
		"distinct_paths", "wildcard_imports"}}
	var rs []rowRec
	for _, m := range order {
		a := aggs[m]
		if a.extUses == 0 {
			continue
		}
		rs = append(rs, rowRec{id: m, c: []cell{cs(g.modName(m)),
			ci32(int32(len(a.crates))), ci32(a.extUses), ci32(a.distinct),
			ci32(a.wildcards)}})
	}
	sortRows(rs, func(a, b *rowRec) bool {
		if a.c[1].i != b.c[1].i {
			return a.c[1].i > b.c[1].i
		}
		if a.c[2].i != b.c[2].i {
			return a.c[2].i > b.c[2].i
		}
		return a.id < b.id
	})
	fill(r, rs)
	return r
}

var catalogueMeta = []catEntry{
	{`unsafe-under-pub-api`, `unsafe reachable from a public function, up to 4 hops`, "ANSWERS which `unsafe` a caller outside this crate can reach without\n     writing `unsafe` themselves -- the exact set that has to be sound\n     for ALL inputs, not just the ones the crate happens to pass.\nACT split by documented: an undocumented block on a public path is where\n     the soundness argument does not exist in writing. Those are the\n     fuzzing targets and the review queue, in that order.\nMISLEADS depth is capped at 4 hops and only RESOLVED edges are walked, so\n     this is a floor -- an unsafe block five frames down, or one reached\n     through a trait object, is missing entirely. A `pub` item inside a\n     private module is not actually reachable from outside the crate;\n     visibility here is the keyword, not the effective export."},
	{`panic-frontier`, `unwrap, indexing and unchecked arithmetic on a public or spawned path`, "ANSWERS where a panic becomes someone else's problem: a `pub` function\n     panicking aborts a caller who never opted in, and a panic inside a\n     spawned task kills that task silently while the join handle is\n     dropped.\nACT the ranking is by blast: panic sites times callers. Return a Result\n     from the ones at the top; `get()` instead of `[]`; `checked_add`\n     where overflow is possible.\nMISLEADS the blast column multiplies by MAX(fan_in,1), so a symbol with\n     NO known caller scores exactly as if it had one. Read fan_in=0\n     rows as 'unknown reach', never as 'reach of 1'.\n     an `unwrap` after a checked `is_some()`, on a compile-time\n     constant, or on a `Mutex` that is never poisoned is correct code and\n     is counted here in full. Test files are excluded but a helper called\n     only from tests is not. n_arith_unchecked subtracts explicit\n     checked_/wrapping_ calls, but overflow only panics in debug builds\n     -- in release it wraps, which is a different bug."},
	{`lock-held-across-await`, `A guard still alive at a .await, here or up to 3 frames down`, "ANSWERS clippy::await_holding_lock raised to the call graph. A std\n     MutexGuard held across a yield point blocks every other task on that\n     executor thread; a RefCell borrow held across one panics instead.\n     The cross-frame half is the part no per-function lint can reach:\n     the lock is taken here, the await happens in the callee.\nACT take what you need out of the guard, drop it, then await. An explicit\n     `drop(g)` before the await already counts as fixed and is excluded.\nMISLEADS guard liveness is LEXICAL -- a `let` in an enclosing block that\n     starts earlier in the file. A guard moved into a closure, returned,\n     or shadowed is mis-read, and `tokio::sync::Mutex` guards are held\n     across awaits deliberately and correctly. Check which Mutex it is\n     before touching the row."},
	{`blocking-io-in-async`, `std blocking calls reachable from an async fn without a spawn_blocking`, "ANSWERS which executor threads get parked. `fs::read_to_string` or\n     `thread::sleep` under an async fn stalls every other task sharing\n     that worker, and the symptom is latency with an idle CPU.\nACT move it behind `spawn_blocking`, or use the async filesystem API.\n     crosses_spawn_blocking is the counter-evidence: a call chain that\n     already goes through one is fine and is shown so you can skip it.\nMISLEADS the boundary test is whether ANY function on the path calls\n     spawn_blocking, not whether THIS call is inside the closure it\n     passed -- so a function that uses spawn_blocking elsewhere reads as\n     safe here. Startup and shutdown paths block deliberately. Depth is\n     capped at 4 hops, so deeper blocking is invisible."},
	{`result-that-panics`, `Functions returning Result or Option that panic anyway`, "ANSWERS the contradiction a signature cannot express: the return type\n     promises the caller gets to decide, and the body takes the decision\n     away. A `-> Result<T, E>` containing `.unwrap()` is an error path\n     that was designed and then abandoned.\nACT the `?` operator is already implied by the signature. On an Option\n     return `?` propagates ABSENCE and discards the reason, so the fix\n     there is usually a Result, not a `?`. Ratio of\n     question_marks to panics tells you whether this is one straggler or\n     a function that never used its error type.\nMISLEADS `unwrap` on a value proven present three lines up is correct.\n     A panic in a builder that only runs at startup, or on a poisoned\n     mutex where continuing is worse, is a deliberate choice. This finds\n     the shape, not the intent."},
	{`rc-cycle-risk`, `Modules full of Rc<RefCell<>> and Arc<Mutex<>> with no Weak anywhere`, "ANSWERS the only way to leak memory in safe Rust. A reference cycle\n     through `Rc` never drops, and `Weak` is the single construct that\n     breaks one -- so its ABSENCE in a module built on shared ownership\n     is the signal, not the presence of Rc.\nACT parent links go in `Weak`, child links in `Rc`. If the module models\n     a graph or a tree with back-edges and has zero Weak, assume the\n     cycle exists until someone shows otherwise.\nMISLEADS an acyclic Rc graph -- a DAG of shared config, an interner --\n     never leaks and has no reason to use Weak. This counts type\n     spellings in signatures and bodies, so a cycle formed through a type\n     alias or a nested struct field is invisible. Arc<Mutex<>> is here\n     because it is the same shape, but it leaks far less often."},
	{`ffi-raw-balance`, `into_raw without a from_raw, and unsafe impl Send on FFI types`, "ANSWERS the two FFI leaks a per-function lint cannot see. `into_raw`\n     hands ownership to C and only `from_raw` takes it back; if the crate\n     has more of the first than the second, something is never freed.\n     `unsafe impl Send` is a promise to the compiler with no checker\n     behind it, and on a type holding a raw pointer it is the promise\n     most often wrong.\nACT pair every into_raw with a documented from_raw, or use a wrapper type\n     with a Drop impl. Every `unsafe impl Send/Sync` needs a comment\n     saying why the type is actually thread-safe.\nMISLEADS the balance is counted per MODULE, not per allocation: the\n     into_raw and the from_raw legitimately live in different crates when\n     the API is a C ABI, and then an imbalance is correct by design.\n     Raw pointers behind a safe wrapper are fine and are counted here."},
	{`safety-doc-debt`, `unsafe blocks doing several things behind no SAFETY comment`, "ANSWERS clippy::undocumented_unsafe_blocks and\n     multiple_unsafe_ops_per_block together, ranked by how much is\n     riding on the missing comment. A block with six raw operations and\n     no note is six soundness arguments nobody wrote down.\nACT one `// SAFETY:` per block, naming the invariant that makes it sound.\n     Blocks with the most ops first -- and if the invariant is hard to\n     state, that is the finding.\nMISLEADS op counting is coarse: every call inside the block counts, so a\n     safe helper called from an unsafe block inflates n_ops. The comment\n     check reads the whole contiguous comment run directly above the\n     block, which catches a multi-line note but NOT a SAFETY paragraph in\n     the enclosing function's doc comment or in an `# Safety` rustdoc\n     section -- a crate that documents at the function level will look\n     entirely undocumented here. fn_documented is the counter-evidence\n     column: read it before believing the row."},
	{`suppression-clusters`, `#[allow] sitting on top of code that actually does the thing`, "ANSWERS where a lint was silenced rather than answered. An `#[allow]` on\n     a function with no matching hazard is stale and harmless; one on a\n     function full of unwraps, unsafe or clones is a decision someone\n     made once and nobody has revisited.\nACT `#[expect(...)]` instead of `#[allow(...)]` -- since Rust 1.81 it\n     warns when the lint stops firing, so the suppression expires by\n     itself. expect_attrs is the count already doing this.\nMISLEADS an allow can be perfectly justified, and this cannot read the\n     reason because there usually is not one. The attribute name is\n     matched to hazard counts by heuristic, not by which lint it names --\n     `#[allow(dead_code)]` on a function with unwraps will show up as a\n     panic suppression, which it is not. Read the args column."},
	{`arc-mutex-contention`, `Arc<Mutex<..>> on hot paths: one lock every caller has to queue behind`, `ANSWERS which shared-state choices will flatten under load. A single
     Mutex behind a high fan_in function is a serialisation point --
     throughput stops scaling with cores and latency grows a tail.
ACT sharding beats a bigger critical section: per-key locks, a
     DashMap-style striped map, or an actor owning the state with a
     channel in front. If reads dominate, RwLock or arc-swap.
MISLEADS a lock held for three instructions under low contention costs
     almost nothing, and this cannot see contention -- only structure.
     fan_in is NOT shown because it is zero for every Arc<Mutex>
     holder measured -- these are usually struct fields reached
     through a method, so the holder itself has no direct callers.`},
	{`atomic-ordering-audit`, `Relaxed and SeqCst orderings, and which functions mix them`, `ANSWERS whether the memory orderings were chosen or defaulted. Relaxed
     guarantees only atomicity, not ordering: it is correct for a
     statistics counter and wrong for a flag that publishes data another
     thread will read. SeqCst is always correct and always the slowest.
ACT for a counter nobody synchronises on, Relaxed is right. For
     publishing, use Release/Acquire. Reach for SeqCst only when the
     algorithm genuinely needs a single global order.
MISLEADS this counts orderings, it does not verify them. A Relaxed load
     gating access to non-atomic data is a data race that looks
     identical here to a correct Relaxed counter.`},
	{`transmute-and-raw-pointers`, `transmute, raw pointers and static mut: the parts the compiler cannot check`, "ANSWERS where Rust's guarantees have been switched off by hand.\n     `transmute` reinterprets bits with no check at all; `static mut` is\n     a global with no synchronisation and is a hard error to reference\n     in edition 2024.\nACT most transmutes have a safe replacement -- `from_bits`, `as` casts,\n     `bytemuck`, or a union with a documented invariant. For static mut\n     use OnceLock, atomics, or a Mutex.\nMISLEADS FFI code legitimately does all of this, and this cannot tell an\n     audited FFI shim from an unaudited shortcut. `safety_comments` is\n     the tell: unsafe with no SAFETY note is the shortlist."},
	{`dead-code`, `Nothing in this tree calls these`, "ANSWERS what might be deletable.\nACT grep the name as a STRING before deleting: a registry, a config file\n     or a reflective call keeps a symbol alive with no edge to show it.\nMISLEADS this is the query most likely to be wrong, and `graph-blindspots`\n     is the measure of by how much. Anything public is excluded because a\n     caller outside this tree cannot be seen at all; what is left is\n     private and unreferenced, which is a much weaker claim than dead."},
	{`blocking-work-below-public-api`, `a lock, a blocking sleep or I/O inside a loop, reachable from a public function`, "ANSWERS what clippy sees per-function and cannot connect: `await_holding_lock`\n     and the perf lints fire on one body at a time. A lock taken inside a\n     loop is a convoy; the same code three frames under a published API is\n     a convoy any caller can trigger. This walks down from every `pub`\n     item and reports what it lands on.\nACT hoist the lock out of the loop, or take it once and pass the guard.\n     `reached_from` names the published function whose contract now\n     includes this cost; `hops` says how much code sits between them.\nMISLEADS a `pub` item inside a private module is not part of the crate's\n     API and is counted here anyway -- `pub(crate)` and re-export chains\n     are not modelled. Depth stops at 4 hops. A lock in a loop over three\n     elements is fine and looks the same as one over three million."},
	{`runtime-borrow-panic-surface`, `RefCell borrow_mut reachable from a public API, with the allocation churn around it`, "ANSWERS the half of clippy's advice that is a runtime property: a\n     `borrow_mut()` is a compile-time-free, run-time-checked lock, and two\n     live borrows on one path is a panic, not an error. Reachability from\n     a public entry point is what turns that from a local invariant into\n     a caller-triggerable abort.\nACT the columns rank by how hard the path is to reason about:\n     `borrow_muts` is the panic surface, `to_owned_in_loop` and\n     `push_in_loop` are the clippy perf lints on the same code, and a\n     function high in both is the one to restructure first.\nMISLEADS a single borrow_mut with no reentrancy cannot panic, and most\n     here are that. Depth is bounded at 4 hops. Interior mutability via\n     Mutex or atomics does not appear at all."},
	{`clone-in-loop`, `.clone() inside a loop (clippy perf/cloned_ref)`, `ANSWERS where .clone() is called inside a loop, allocating a new object
     each iteration. For large objects this is a significant cost.
ACT borrow (use &T) if the clone is not needed, or clone once before the loop.
MISLEADS a clone that is moved into a collection (Vec<T>) must happen per
     iteration. The column counts sites, not allocations.`},
	{`unwrap-in-prod`, `.unwrap() outside of test code (clippy restriction/unwrap_used)`, `ANSWERS where .unwrap() is called in non-test code, which panics if the
     Option/Result is None/Err. In production this is an unhandled crash.
ACT use ? or match, or provide a fallback with unwrap_or/unwrap_or_else.
MISLEADS unwrap after a contains_key check or on a known-present value is
     safe. The graph sees the call but not the preceding check.`},
	{`expect-in-prod`, `.expect() outside of test code (clippy restriction/expect_used)`, `ANSWERS where .expect() is called, which panics with a message. Better than
     unwrap but still a crash in production.
ACT use ? or a proper error type.
MISLEADS expect in a main() or init() that cannot recover is acceptable.`},
	{`float-equality`, `== comparison on floating point (clippy pedantic/float_cmp)`, `ANSWERS where == is used on f32/f64, which is unreliable due to floating
     point representation. Two values that should be equal may differ by
     a tiny epsilon.
ACT use (a - b).abs() < EPSILON or the approx crate.
MISLEADS == on 0.0 or on values known to be exact (bit patterns) is safe.
     The graph counts comparisons but not the operand types.`},
	{`unsafe-without-comment`, `unsafe block without a safety comment (clippy/undocumented_unsafe_blocks)`, "ANSWERS where an unsafe block has no safety comment documenting why it is\n     safe. Each unsafe block is a human-verified invariant; without a\n     comment, the invariant is lost.\nACT add a `// SAFETY: ...` comment above each unsafe block.\nMISLEADS an unsafe fn's body is implicitly unsafe; the comment may be on the\n     fn, not the block. has_safety_comment is a lexical scan."},
	{`vec-new-push-in-loop`, `Vec::new() + push inside a loop (clippy perf/vec_push_in_loop)`, `ANSWERS where a Vec is created with Vec::new() and then pushed to inside a
     loop, causing multiple reallocations. Use with_capacity to pre-allocate.
ACT if the final size is knowable, use Vec::with_capacity(n).
MISLEADS a loop that pushes conditionally has no knowable size. n_push_in_loop
     counts sites, not the Vec's growth pattern.`},
	{`transmute-misuse`, `std::mem::transmute for type punning (clippy/unnecessary_transmute)`, `ANSWERS where transmute is used, which reinterprets the bits of one type as
     another. This is undefined behavior if the sizes don't match or the
     target type has different validity invariants.
ACT use TryFrom/TryInto, or a safe conversion method.
MISLEADS transmute for FFI interop is sometimes necessary. The graph sees
     the call but not the types involved.`},
	{`static-mut-unsafe`, `static mut without synchronization (clippy/static_mut_refs)`, `ANSWERS where a static mut is used, which is shared mutable state with no
     synchronization. Taking a reference to a static mut is UB if accessed
     from multiple threads.
ACT use a Mutex, RwLock, or AtomicX, or thread-local storage.
MISLEADS a static mut accessed from a single-threaded context with
     documented safety is technically safe but fragile.`},
	{`block-on-async`, `.block_on() on an async runtime (clippy/clippy/block_in_place)`, `ANSWERS where .block_on() is called, which blocks the current thread to
     drive a future. Inside an async context this deadlocks the runtime.
ACT use .await, or spawn_blocking for sync code in an async context.
MISLEADS block_on in a sync main() to start the runtime is correct. The
     graph sees the call but not whether it's inside an async context.`},
	{`spawn-without-join`, `tokio::spawn without storing the JoinHandle (clippy/tokio)`, `ANSWERS where a task is spawned but the JoinHandle is discarded, so the
     runtime may cancel the task at any time and errors are silently lost.
ACT store the handle and await it, or use tokio::spawn with proper error
     handling.
MISLEADS a fire-and-forget background task that is intentionally detached is
     a valid pattern for long-running workers.`},
	{`import-cycle`, `Circular module dependencies (madge/circular)`, `ANSWERS which files form a use/cycle.
ACT break the cycle by extracting shared code.
MISLEADS cycles through test files are usually fine. Depth capped at 8.`},
	{`relaxed-ordering`, `Atomic with Relaxed ordering where Acquire/Release is needed (clippy/atomic)`, `ANSWERS where Relaxed memory ordering is used, which provides no
     synchronization between threads. For read-modify-write operations
     that synchronize, Acquire/Release is needed.
ACT use Acquire for loads, Release for stores, AcqRel for RMW.
MISLEADS Relaxed for counters that don't synchronize is correct. The graph
     counts orderings but not the synchronization intent.`},
	{`rc-refcell-mutation`, `Rc<RefCell> for interior mutability (clippy/rc_buffer)`, `ANSWERS where Rc<RefCell> is used, which is single-threaded and panics on
     double borrow. For multi-threaded code, Arc<Mutex> is needed; for
     single-threaded, Rc<Cell> for Copy types is cheaper.
ACT use Arc<Mutex> if multi-threaded, or Rc<Cell> for Copy types.
MISLEADS Rc<RefCell> for a single-threaded tree structure is correct.`},
	{`len-in-loop`, `.len() called inside a loop (clippy/len_zero)`, `ANSWERS where .len() is called inside a loop on a collection, which may
     be O(n) for some types (linked lists, certain iterators).
ACT hoist .len() outside the loop if the length doesn't change.
MISLEADS .len() on Vec is O(1); the column cannot distinguish O(1) from O(n).`},
	{`trait-breadth`, `Traits implemented by the most distinct types`, "ANSWERS the trait contracts with the widest implementor base -- the\n     seams that, if they change, every impl block (and every generic\n     bound) must change with them.\nACT treat the top rows as breaking-change surfaces: adding a required\n     method to one of these compiles to errors across the whole crate.\nMISLEADS counts impl rows per trait NAME; a generic/blanket impl\n     (`impl<T: Trait>`) is counted once for its declaring type, not once\n     per concrete instantiator, so blankets undercount real breadth.\n     `dyn-with-one-impl` is the zero end of this same ranking."},
	{`macro-density`, `Macro invocations per module: code generation heat map`, "ANSWERS which modules lean heaviest on macro invocation -- every call\n     hides generated code from the call graph, so a module dense in\n     macro use is partially invisible to everyone after this.\nACT a hot module is where a proc-macro bug or an expansion-size\n     regression hurts most; bodies hidden behind macros there deserve\n     eyeball coverage.\nMISLEADS counts invocations and definitions separately; `vec!`,\n     `println!` and friends from the prelude count as invocations but\n     are trivial, while a heavy proc macro in a cold module ranks low.\n     Expansion output is not modeled anywhere."},
	{`impl-fragmentation`, `Types whose impl blocks are spread across many files`, "ANSWERS how many distinct files host impl blocks for one type -- the\n     fragmentation that makes a type's full contract unreadable from\n     any single file. High fragmentation hides methods from casual\n     discovery and scatters the changes a trait addition demands.\nACT consolidate inherent impls into the defining file; cross-file\n     trait impls are a real Rust pattern (coherence rules), so expect\n     the trait rows and judge inherent rows harder.\nMISLEADS a type and its impls in the same file count as one file here;\n     `#[cfg(test)]` impls and cfg-gated impls count as distinct\n     fragments even when small, and same-named types in different\n     modules merge under a bare type_name."},
	{`ffi-crossings`, `Calls that leave Rust into extern blocks`, `ANSWERS which functions call FFI-declared extern fns -- every crossing
     is a point where Rust's guarantees stop and C's rules begin. A
     function dense in FFI calls is a boundary node: the place to audit
     pointer lifetimes and null handling.
ACT keep the crossing thin: validate pointers and lengths inside the
     wrapper, never at the call site; prefer safe bindings (libloading
     with a safe layer) over raw extern exposure.
MISLEADS the extern fn count comes from foreign_mod_item tracking and
     n_ffi (unsafe block ops); a call through a function POINTER
     returned from FFI is invisible, and calling an extern fn inside
     an unsafe block is counted while the block's safety comment is
     not evidence either way.`},
	{`deep-module-paths`, `Calls and imports spelled with long :: chains`, "ANSWERS where paths are spelled in full instead of imported -- every\n     `crate::services::auth::db::connect` restates the module layout at\n     the call site, and a rename anywhere in the chain breaks every\n     re-statement.\nACT import the target once (`use`), or shorten through a root alias;\n     the deepest rows are the most fragile to module moves.\nMISLEADS counts `::` segments in the import target text; a module\n     legitimately nested that deep (a crate convention) is not wrong,\n     and external crates' long paths are counted the same as local\n     ones. Calls whose path came from a macro expansion are unseen."},
	{`async-task-hubs`, `Async functions that spawn background tasks`, "ANSWERS the async entry points that fire-and-forget tasks (tokio::\n     spawn / async_std::task::spawn / wasm_bindgen_futures::spawn_local\n     and friends) -- the roots of every background task tree in the\n     crate.\nACT each row needs a documented lifetime rule: a spawned task that\n     outlives its context is a leak or a race; prefer scoped tasks\n     where the API allows. `spawn-without-join` covers the no-join\n     half; this ranks the hubs.\nMISLEADS counts spawn CALL SITES per async function; a spawn inside a\n     helper that the async hub calls is attributed to the helper, and\n     a spawn spelled through a wrapper function (`my_spawn(|| ...)`) is\n     invisible unless the wrapper name contains spawn."},
	{`placeholder-panic-sites`, `todo!/unimplemented!/unreachable!/panic! in production code`, "ANSWERS the deployed crash points: todo!() and unimplemented!() compile\n     and ship, and each one is a panic waiting for the right input.\n     unreachable!() in an exhaustive-match fallback is the only\n     deliberate member of the set.\nACT replace todo!/unimplemented! with a Result or a proper error path;\n     unreachable! needs a proof comment next to it.\nMISLEADS proc-macro expansions are invisible (they never hit this\n     table); a panicking macro spelled through a local `macro_rules!`\n     alias is invisible to name matching; test exclusion is\n     symbols.is_test, which may disagree with cfg(test) on odd trees."},
	{`debug-print-residue`, `dbg!() outside tests`, "ANSWERS dbg!() calls in non-test code: the debugging print that ships.\n     dbg!() prints to stderr AND returns the value, so it also changes\n     evaluation order (a dbg!(f()) evaluates f() BEFORE the outer\n     expression context expects it).\nACT replace with a proper log or remove; a dbg! that is deliberately\n     kept for support deserves a comment and a log target instead.\nMISLEADS name-based on the invocation capture: `eprintln!` is not dbg!\n     and does not appear; test files are excluded by is_test."},
	{`sql-string-build`, `SQL text assembled by string building (OWASP G09 / A05)`, `ANSWERS functions whose string literals contain SQL keywords AND which
     also build strings (format!, or more than one string literal) -- the
     shape that lets a query be glued together instead of parameterized.
ACT use a parameterized statement (rusqlite params!, sea-orm bind); never
     interpolate a variable into a SQL string.
MISLEADS the pairing is same-function co-occurrence, NOT data flow: the
     SQL literal and the format! may be unrelated, and a constant SQL
     string beside unrelated string literals reads as a violation. A
     constant format! with no interpolated variable is safe. The SQL
     test is the literal's own text, so SQL in comments or identifiers
     does not count.`},
	{`command-build-surface`, `Command::new sites -- the process boundary (OWASP G10 / A05)`, "ANSWERS every function that constructs a Command -- the places a string\n     becomes a process. The string-building columns are context: a\n     Command::new with format! or literal churn in the same function is\n     where a built command line is likely.\nACT use std::process::Command's argument array; never pass a shell string.\nMISLEADS .arg() chains are NOT counted (no argument capture), so an\n     arg-built command and a constant command rank the same. Name-based:\n     only the bare `Command::new`/`Command::spawn` call text matches;\n     `std::process::Command::new` is invisible. A constant command is\n     safe -- the graph sees the construction, not the argument source."},
	{`hardcoded-secret-candidates`, `Credential-shaped string literals (OWASP G07)`, `ANSWERS string literals at least 12 chars long whose text names a
     credential (password, token, api_key, secret, bearer, jwt, ...) --
     the literal that a committed secret looks like.
ACT rotate and move to a secret manager; never commit the literal.
MISLEADS a format string or test fixture containing the WORD token/pass
     reads as a candidate (the filter is the literal's own text, not its
     use); values over 200 chars are truncated at capture; a secret
     built from parts or read from an env var is invisible here.
     This is a candidate list, not a verdict.`},
	{`untrusted-deserialization`, `from_str / from_slice / from_reader deserialization sites (OWASP G19)`, `ANSWERS functions that deserialize (serde_json, bincode, ron, toml all
     spell from_str/from_slice/from_reader/from_bytes) -- the surface
     where an untrusted payload becomes a value.
ACT validate the payload schema and size before deserializing; never
     deserialize into a permissive type from an untrusted source.
MISLEADS WHICH input is untrusted is not modeled: a from_str on a
     constant ranks the same as one on request data. The capture is the
     bare base name, so a serialization helper wrapping the call is
     invisible.`},
	{`zip-slip-surface`, `zip crate access sites (OWASP G29)`, `ANSWERS functions that touch the zip crate (ZipArchive) -- the surface
     where an entry name becomes a filesystem path.
ACT validate every entry name against a containment check before
     extraction; reject ../ and absolute paths.
MISLEADS the containment check is not modeled: a function that checks
     each name before extraction ranks the same as one that does not.
     The capture is the dotted ZipArchive:: name; a renamed zip helper
     is invisible.`},
	{`unsafe-in-loop`, `unsafe blocks inside loop bodies`, `ANSWERS unsafe blocks in loops: pointer arithmetic paid per iteration
     is where memory bugs and hot paths meet. The review order is
     n_deref first -- each deref is a place a dangling or misaligned
     pointer becomes a fault.
ACT hoist the invariant check; prove bounds once outside the loop.
MISLEADS a well-audited unsafe hot loop (simd, ring buffers) is the
     legitimate row -- this ranks review order, not guilt; n_ops is
     syntactic and macro-generated unsafe is invisible; has_safety_comment
     is the author's own claim of scrutiny.`},
	{`suppression-without-reason`, `Bare #[allow(...)] without an explanation (clippy allow-without-reason)`, "ANSWERS allow attributes with no reason given. The 1.83+ discipline is\n     #[expect(reason)] over #[allow(...)]: expect FAILS the build when\n     the lint stops firing, so the suppression cannot go stale; an allow\n     with no reason is a suppression nobody can audit.\nACT add a reason, or convert to #[expect(...)] and let the compiler\n     verify the lint still fires.\nMISLEADS the reason is the ARGS text -- a bare `#[allow]` with no parens\n     at all is the sharpest row; `#[allow(unused)]` with a comment on\n     the next line is not distinguished from a reason-free allow."},
	{`refcell-across-await`, `RefCell borrows still alive at an .await (the async interior-mut trap)`, `ANSWERS .await points where a RefCell/Rc/Cell borrow guard is live: the
     borrow must not outlive the await, or the SAME task can deadlock
     itself re-entering the borrow. Unlike a mutex this is not cross-
     thread -- it is the task's own re-entry.
ACT clone the value out of the borrow before the await, or scope the
     borrow to end before the yield point.
MISLEADS the flag is the guard VALUE text naming RefCell/Rc/Cell: a
     borrow of an already-unwrapped value (a &mut from outside) is not
     flagged; lexical liveness -- the guard's let is an ancestor block
     -- can over-report when the borrow is actually dropped mid-block
     (only an explicit drop() is recognised).`},
	{`indexing-slicing-surface`, `v[i] indexing in production code (clippy indexing-slicing)`, "ANSWERS functions that index collections directly -- v[i] panics on\n     out-of-range and is the community's #1 gap between linters and\n     what they can prove. Rows are the review surface for unchecked\n     indexing.\nACT use .get(i) and handle the Option, or prove the bound once; for\n     hot paths where the bound is invariant, the panic is cheaper than\n     the branch -- say which in a comment.\nMISLEADS n_index_expr counts every index expression in the body: a\n     range check immediately before each index reads the same as an\n     unchecked one; a const index (`v[0]` on a fixed array) is\n     counted and is safe; `noUncheckedIndexedAccess`-style proof is a\n     type-system matter this syntax-level counter cannot see."},
	{`dropped-futures`, `let _ = async_call(): the future is dropped without being awaited`, "ANSWERS async functions that drop a future into `let _`: the call\n     never runs unless the future is moved elsewhere. In a request\n     handler this is a silent no-op; in a spawn-er it is the whole\n     work item vanishing.\nACT await the future, or hand it to a spawner; if the fire-and-forget\n     is deliberate, the dropped future needs a comment and usually a\n     task wrapper.\nMISLEADS the capture is `let _ = <call>` in any function -- the query\n     reads async functions only, and a let-_ of a NON-future value in\n     an async fn still counts (the value is dropped, which is usually\n     also a bug); a future bound to a named variable and dropped later\n     is invisible here."},
	{`lossy-casts`, `as-casts that narrow or drop precision (clippy cast_sign_loss family)`, "ANSWERS type_cast_expression sites: `x as u8` truncates, `f64 as f32`\n     loses precision, `i64 as u64` flips signs -- each is a value-\n     changing operation the author may not have meant.\nACT prefer From/TryFrom (which cannot lose silently) and handle the\n     error; keep `as` only for raw-bytes and known-safe ranges.\nMISLEADS n_as_casts counts ALL as-casts, including widening ones that\n     cannot lose: a body of `u8 as i64` reads the same as `i64 as u8`;\n     the target width is not parsed, so the rows are the review list\n     and the cast_sign_loss/cast_possible_truncation families are the\n     per-cast verdicts this query lacks."},
	{`error-swallowing-sites`, `let _ = fallible() and .map_err(|_| ...) (clippy let_underscore_must_use)`, "ANSWERS the shapes that discard errors: `let _ = fallible()` drops the\n     Result, and `.map_err(|_| ...)` throws away the error value while\n     keeping the type. Both compile and both erase the reason.\nACT handle the Result (match, ?, or .ok() with a comment); a map_err\n     that replaces the error with a constant loses the context -- use\n     .map_err(|e| format!(...) with the error in the message) or\n     anyhow's context.\nMISLEADS the capture is `let _ = <call>` plus map_err-on-underscore\n     text: `let _ =` on a non-Result value (a drop of a must-use value)\n     is arguably the same bug and counts; `.ok()` alone in a chain is\n     not captured; a deliberate `let _ =` in an FFI shim is the\n     legitimate row."},
	{`public-api-doc-debt`, `Public items without a doc comment, by fan-in (rustc missing_docs)`, "ANSWERS pub functions/methods that say nothing about themselves: the\n     API surface where the next reader pays the documentation tax.\n     fan_in ranks the migration order -- the most-called undocumented\n     symbol pays first.\nACT add a /// doc comment; with #![warn(missing_docs)] the compiler\n     enforces the debt ceiling.\nMISLEADS has_doc is the doc-comment/leading-comment scan immediately\n     above the item: a `//!` module doc or a comment one line further\n     up reads as absent; a pub item reachable only through a re-export\n     of a private path is not distinguished; private items are\n     excluded by is_public."},
	{`manifest-vs-usage`, `Cargo.toml dependencies never imported (cargo-machete territory)`, "ANSWERS declared crates no use statement references: dead weight in\n     build time and the lockfile, or a dependency used only through\n     a proc macro that names no path.\nACT remove the dependency, or use it; a dev-dependency used only by a\n     build script or a #[test] in another crate shows as unused here\n     -- check before deleting.\nMISLEADS matching is by use-declaration head: `use tokio::time` counts\n     as using tokio; a dependency used only via a macro expansion\n     (no textual use path) reads as unused; workspace members and\n     target-specific deps in non-root manifests are included only if\n     the member Cargo.toml was read."},
	{`transitive-panic-surface`, `unwrap, expect, panic! and indexing reachable THROUGH the call graph from a pub or main entry`, "ANSWERS the panic surface no per-function lint can see: clippy::unwrap_used\n     judges one body; this walks resolved edges up to 4 hops from every\n     `pub` or `main` entry and names the helper whose panic a caller can\n     actually trigger. hops=1 is the cheapest fix -- one frame between the\n     API and the panic is a contained signature change.\nACT convert the top rows to Result and let the panic become the caller's\n     choice; get() instead of []; checked arithmetic where overflow is\n     possible. reached_from tells you whose contract changes.\nMISLEADS resolved edges only and capped at 4 hops, so a panic behind a\n     trait object or five frames down is invisible; an unwrap proven safe\n     by a caller-side check still counts in full; `pub` inside a private\n     module is not real external reachability but is counted."},
	{`result-unwrapped-by-caller`, `callee returns Result/Option, caller .unwrap()s it -- the seam where error handling is abandoned`, "ANSWERS the pairing the type system flags but no per-function tool can\n     see: the callee's signature says the CALLER decides what an error\n     means, and the caller decides to panic. callee_question_marks shows\n     whether the callee did its half (propagating) only to have the\n     caller throw the decision away.\nACT at the top rows make the caller propagate (`?` or match); if the\n     callee is infallible in practice, change ITS signature instead -- a\n     Result nobody matches is API noise that trains callers to unwrap.\nMISLEADS co-occurrence, not data flow: the caller's unwraps may be on\n     OTHER values than this callee's result, and an unwrap of a value\n     proven present two lines up is correct. Read callee_question_marks\n     before concluding the callee designed for errors."},
	{`mutex-poison-cascade`, `lock().unwrap() sites -- the second dominoes of a poisoned mutex, ranked by how many callers they take down`, `ANSWERS the cascade the std docs describe but nothing measures: one panic
     while a thread holds the mutex poisons it, and EVERY later lock()
     unwrap in the path panics too. Each row here is a lock-acquiring
     function that also unwraps; fan_in is how many call sites join the
     cascade once the first panic happens.
ACT decide the poison policy once: unwrap_or_else(|e| e.into_inner())
     when the data is consistent despite the panic, or propagate a Result
     so the caller sees the lock is dead. The default unwrap converts one
     failure into every failure after it.
MISLEADS counts functions that lock AND unwrap somewhere -- the unwrap is
     usually the guard's but the chain is not proven per-site; a mutex
     nobody has poisoned yet makes every row look safe until the first
     panic, and an unwrapped lock in main() is deliberate fail-fast.`},
	{`panic-in-drop-impl`, `Drop impl methods that can panic -- a panic while unwinding aborts the process`, `ANSWERS Drop impls whose methods contain panic sites. A panic raised while
     ALREADY unwinding aborts the process: no catch_unwind intercepts it,
     the original error is lost, and in a server that means the request
     handler takes down the worker. unwrap/expect/index in a Drop is the
     classic double-panic.
ACT make Drop infallible: drain fallible work into a method the caller
     invokes (try_close), and in Drop only log-and-continue. Never let a
     destructor be the first place an error is noticed.
MISLEADS sees panic sites in the impl's OWN methods only -- a Drop
     delegating to a panicking helper one frame down is invisible here;
     derive-generated drops never appear, and an unwrap of a value the
     same Drop just checked is correct but counted.`},
	{`panic-in-extern-fn`, `extern "C" fns containing panic sites -- since Rust 1.81 the process aborts at the boundary`, "ANSWERS body-ful `extern \"C\" fn` items that can panic. Before 1.81 that\n     panic unwound into C (UB); now it aborts the whole process: the C\n     caller gets no error return, its cleanup handlers never run. Every\n     unwrap/index inside an exported fn is a crash the FFI side cannot\n     catch.\nACT wrap the body in catch_unwind and return an error code, or audit out\n     every panic site -- the boundary contract is `no unwind`, and the\n     compiler cannot enforce it for you.\nMISLEADS only fn items with the extern modifier and a body count; a panic\n     reached from C through a function POINTER, or one frame past the\n     exported fn, is invisible; declarations inside extern blocks have no\n     body and can never appear (correctly)."},
	{`await-in-loop`, `.await inside a loop body -- N items take N sequential round-trips (tokio tutorial anti-pattern)`, `ANSWERS sequential awaiting: each iteration parks this task until the
     remote finishes, so a 100-item loop is 100 latencies back to back.
     The fix the tokio tutorial gives is concurrency: join_all, or
     buffered() on a stream -- which only helps if the loop body is
     independent per iteration.
ACT batch the futures and join them, UNLESS iteration N+1 consumes N's
     result (paging, pagination tokens) -- that dependency is exactly
     what this query cannot see, so read the loop before rewrites.
MISLEADS a deliberate retry/poll loop (await, check, sleep, repeat) is
     the correct shape and ranks here in full; the column counts SITES,
     so one await in a 2-iteration loop reads like one in a million; the
     awaited future's own concurrency is invisible.`},
	{`blocking-in-critical-section`, `a lock acquired, then a blocking call reached while it is held -- here or up to 3 frames down`, `ANSWERS the sync cousin of await_holding_lock: a guard still alive while
     file I/O, a sleep or a block_on runs. Every other thread that wants
     that lock queues behind the blocking call -- the convoy is
     invisible per-function because the lock and the block live in
     different frames.
ACT narrow the critical section: copy what you need out, drop the
     guard, THEN do the I/O. If the guard must live across the call,
     the call should take plain data, not run while holding.
MISLEADS hops=0 rows are lexical (the guard's let is still in scope);
     hops>0 rows only say the lock was taken UP-STACK -- the callee may
     have been handed plain data and hold nothing. tokio::sync::Mutex
     guards crossing awaits are deliberate and correct.`},
	{`sync-lock-in-async-fn`, `async fns acquiring std-sync locks -- prefer tokio::sync or a critical section too short to care`, `ANSWERS async functions that call lock/read/write/borrow at all. A std
     Mutex under contention BLOCKS the executor thread instead of
     yielding; tokio's shared-state guide says to prefer tokio::sync::Mutex
     or keep std guards out of anything that yields.
ACT read guards_across_await first: zero means the guard never crosses a
     yield and a short critical section on a std Mutex is fine -- the
     row is then a style note, not an incident. Non-zero: switch the type
     or shrink the section before someone extends the fn.
MISLEADS counts acquisitions, not hold times; an uncontended std Mutex
     is a few instructions and most are; RefCell borrows count too (the
     acquire shape is the same) and are single-task by construction, so
     they cannot stall other tasks at all.`},
	{`block-on-in-async-context`, `.block_on() reached from an async fn -- blocking the thread that should be polling`, `ANSWERS block_on called from an async fn directly (hops=0) or through up
     to 3 frames. Inside a runtime, block_on steals the worker thread to
     drive one future while every task on that thread waits -- and if the
     inner future needs the same runtime, the task deadlocks on itself.
ACT await the future instead; for genuinely blocking work use
     spawn_blocking. block_on before the runtime starts (a sync main) is
     the one correct spelling and is excluded only by being unreachable
     from an async fn.
MISLEADS the boundary test is structural -- ANY async fn up-stack counts,
     so a helper that only sync mains call but also sits under one async
     fn appears; startup/shutdown sequencing that blocks deliberately is
     counted; depth capped at 3 hops.`},
	{`os-thread-in-async`, `thread::spawn reached from an async fn -- OS threads the runtime cannot see, count, or cancel`, "ANSWERS raw OS threads created under an async fn, directly or up to 3\n     frames down. Each thread costs real memory and scheduler time, is\n     invisible to the runtime's shutdown, and outlives the future that\n     spawned it if that future is cancelled first.\nACT tokio::spawn for concurrent CPU work, spawn_blocking for blocking\n     work; keep raw threads only for genuine long-lived workers created\n     once at startup -- which is the legitimate row.\nMISLEADS name-based: `thread::spawn` and `std::thread::spawn` match, but\n     `Builder::new().spawn()` (no `thread` in the call text) does not; a\n     one-time dedicated worker thread inside an async setup fn is fine\n     and is counted here anyway."},
	{`spawned-task-panic`, `closures handed to spawn that contain panic sites -- the task dies silently when the handle is dropped`, "ANSWERS task bodies with unwraps/panics inside. A panicked task stores the\n     error in its JoinHandle; if nobody keeps the handle (see\n     spawn-without-join) the error is dropped on the floor: no log, no\n     propagation, the work just never happened.\nACT keep the body infallible or send failures out over a channel/JoinSet\n     someone actually drains. If the handle IS awaited elsewhere this is\n     half as bad -- check spawn-without-join for the other half.\nMISLEADS sees panic sites in the closure LITERALLY passed to spawn, not\n     two calls deeper inside the task -- walk the closure's own edges for\n     that; a panic caught by the spawner's catch_unwind still counts;\n     `tokio::spawn(my_fn())` passes a fn's output, not a closure, and is\n     invisible here."},
	{`spawn-in-loop`, `spawn calls inside loop bodies -- one task per item is unbounded concurrency`, `ANSWERS spawns (tasks or threads) whose call site sits in a loop: input
     of size N becomes N live tasks at once, each holding its state. The
     tokio tutorial's join-all works for a finite handful, not for a
     request-driven fan-out with no ceiling.
ACT bound the concurrency: buffered(stream, N) on an iterator of
     futures, a Semaphore, or a fixed worker pool. If N is provably
     small (config keys, not rows), the row is fine.
MISLEADS the spawn is not provably inside THIS loop (fn-level
     co-occurrence of a loop and a spawn); spawn_blocking-in-loop counts
     too (same name prefix) and is usually the RIGHT call there; the
     loop's trip count is invisible.`},
	{`spawn-join-balance`, `module-level task accounting: spawns minus handle joins -- the fire-and-forget ledger`, "ANSWERS whether a module's concurrency is reclaimed. A large positive\n     detached balance means tasks nobody observes: panics nobody sees,\n     shutdown nobody waits for. A balanced or negative module reaps what\n     it sows. Module grain, like ffi-raw-balance's into_raw/from_raw\n     ledger -- per-handle ownership is not modelled.\nACT for every detached spawn decide ONCE who owns the handle: a\n     JoinSet, a results channel, or a documented `best effort, may be\n     lost` comment. Then the balance is a decision, not an accident.\nMISLEADS module-level: the join may live in the module that consumes\n     results and the balance is legitimate; slice::join / String-join\n     calls share the base name and inflate the join side; awaited via\n     select! on a JoinSet counts only when spelled join/join_next."},
	{`channel-op-in-loop`, `send/recv inside loops -- unbounded queue growth or a self-deadlock when the buffer fills`, `ANSWERS channel traffic inside loop bodies. send-per-iteration into an
     unbounded channel grows memory until the consumer catches up (tokio
     mpsc::unbounded's documented footgun); send into a BOUNDED channel
     whose recv runs later in the SAME loop deadlocks the moment the
     buffer fills.
ACT bound the channel and size the buffer to the known lag; batch sends;
     move recv to a dedicated task so producers decouple from consumers.
MISLEADS fn-level co-occurrence (channel ops AND a loop), not proven
     same-loop; a drain loop -- recv until disconnected -- is the correct
     shape and ranks identically; bounded vs unbounded is not modelled,
     so the two failure modes are not distinguished.`},
	{`deep-async-call-chain`, `async call chains 4+ hops deep -- every frame's state is embedded in the root's future`, `ANSWERS the giant-future problem: an async fn's future embeds the state
     of every future it awaits, so call depth multiplies the size of the
     allocation every spawned task pays. The async WG's future-size
     reports are full of stacks traced to chains exactly like these.
ACT break chains at 4+ hops: Box::pin the tail so it stops growing the
     root, spawn the tail as an independent task, or pass data instead
     of driving the callee inline.
MISLEADS static graph depth, not per-execution: a chain run once at
     startup costs nothing; trait-object calls are unresolved, so depth
     hiding behind dyn dispatch is invisible; capped at 8 hops by the
     walk itself, so 8 is the ceiling, not the truth.`},
	{`swallowed-error-below-pub-api`, `let _ = fallible() / .map_err(|_| ...) reachable from a pub API -- the caller gets Ok while it failed`, "ANSWERS the cross-frame half of clippy::let_underscore_must_use: the\n     per-fn lint sees the discard line, not the published API whose\n     contract now includes silent failure. A caller of the pub fn cannot\n     distinguish `done` from `failed quietly`.\nACT at hops=1 the fix is local: propagate or log. At hops>=3 the swallow\n     is effectively part of the API contract -- check callers before\n     changing it, and at minimum document the best-effort behavior.\nMISLEADS resolved edges only and 3 hops deep; `let _ =` on a non-fallible\n     value is a deliberate discard and counts anyway; a swallow in a\n     helper whose is_test flag never got set (a cfg(test) mod the parser\n     mis-attributed) pollutes the pub path."},
	{`exit-skipping-drop`, `process::exit / abort reachable from a pub API -- destructors do not run on the way out`, `ANSWERS where the process dies without unwinding. std::process::exit runs
     NO destructors: buffered writers lose their tail, lock files stay
     held, temp dirs stay. abort is harsher still. 0 hops = the pub fn
     itself calls it; higher hops = a helper a caller can trigger.
ACT return an error and let main decide; if exit is required, flush and
     drop explicitly first, and keep the call on a shutdown path callers
     can see in the signature.
MISLEADS hazard patterns are name-based (exit / process::exit / abort),
     so a wrapper named shutdown_now hides the call and libc::abort
     through a re-export is missed; a deliberate fail-fast at the very
     top of main is a legitimate row; reachability is resolved-edge
     only, capped at 4 hops.`},
	{`explicit-leak-surface`, `mem::forget, Box::leak and .leak() call sites -- memory intentionally never freed`, `ANSWERS the leak sites: forget destroys the value without running Drop,
     Box::leak/.leak() promote heap data to 'static. Intentional in a
     preallocated ring buffer or an interned string table; a leak in an
     error path that runs per request is a DoS vector with no OOM
     message to trace.
ACT scope the check by call frequency: a one-shot init leak is a
     decision, the same leak reachable per-call is not. Grep ManuallyDrop
     separately -- it is not a call and never appears here.
MISLEADS name-based on three spellings (mem::forget, Box::leak, bare
     .leak()); ManuallyDrop::new and mem::take-style ownership moves are
     invisible; a leak handed to a C caller via into_raw is the
     legitimate FFI row and counts.`},
	{`needless-unsafe-fn`, `unsafe fn with no unsafe op in its body -- callers write unsafe {} for nothing`, `ANSWERS unsafe fn whose body contains no unsafe block, transmute or raw
     conversion. The qualifier is a published contract: every caller must
     wrap it in unsafe and implicitly uphold whatever obligations it
     names. When the body needs none, the contract is a lie that spreads
     unsafe blocks across the codebase.
ACT drop the qualifier (breaking -- batch with the next major), or write
     the doc comment naming what callers must uphold anyway and keep it.
     On edition 2024 rustc flags the OPPOSITE (unsafe ops without a
     block), so a body-empty unsafe fn is stale, not conservative.
MISLEADS pre-2024, an unsafe fn CALLING other unsafe fns needs no block
     (unsafe_op_in_unsafe_fn), so on old editions a delegating unsafe fn
     is flagged yet is genuinely unsafe to call; unsafe ops hidden in
     macro expansions are invisible.`},
	{`gratuitous-unsafe-impl`, `unsafe impl Send/Sync/... on a type whose impl block shows no unsafe op at all`, "ANSWERS the manual promises with nothing visible behind them. clippy's\n    non_send_fields_in_send_ty (nursery) lints the FIELD view; this is\n    the impl view: unsafe impl whose methods contain no unsafe block,\n    raw pointer or transmute. Send/Sync auto-derive when every field is\n    -- a manual impl with nothing unsafe inside is usually either\n    redundant or hiding a non-Send field behind an alias.\nACT put a SAFETY comment naming the invariant, or delete the impl and\n    let auto-traits do the work. Re-verify after every field addition.\nMISLEADS the justification may live in a FIELD the parser cannot type\n    (a raw pointer behind `type Ptr = *mut u8` reads clean); generics\n    make auto-trait reasoning subtler than a syntactic scan; unsafe\n    impls of traits other than Send/Sync count too and are legitimate\n    more often."},
	{`macro-defined-unsafe`, `unsafe inside macro_rules! bodies -- re-expanded (and re-unreviewed) at every call site`, "ANSWERS unsafe code the unsafe_blocks table never sees: definitions whose\n    body contains `unsafe`. Each invocation re-expands it, so one\n    unaudited definition is unsafe multiplied by call_sites -- the\n    expansion is invisible to every other unsafe query in this file.\nACT audit the definition once; then either give the macro a SAFETY\n    comment like a block, or move the unsafe into a named fn where the\n    rest of this catalogue can see and rank it.\nMISLEADS counts the literal token `unsafe` in the definition text: a\n    comment containing the word counts, and expansions are never parsed,\n    so genuinely unsafe GENERATED code is invisible; invocation matching\n    is by bare macro name, so two same-named macros in different modules\n    merge their call-site counts."},
	{`mutual-recursion`, `indirect recursion cycles in the call graph (a->b->a) -- the stack-overflow paths is_recursive cannot see`, "ANSWERS call-graph cycles of length 2..6 through the RESOLVED edge table.\n    Self-recursion is the is_recursive column; these mutual cycles are\n    invisible to it and to every per-function tool, and each one is a\n    stack-overflow path whose depth is set by the input, not by a human.\nACT add a depth budget or rewrite as a worklist. If the recursion is\n    bounded by construction (a tree's depth), say so in a comment at the\n    top of the cycle -- the next reader is one `Visitor` pattern away\n    from reusing it on a graph.\nMISLEADS resolved edges only and cycle length capped at 6, so longer\n    cycles and anything reached through a trait object or macro are\n    missed; a cycle reachable only from dead code ranks the same as one\n    under the main entry point."},
	{`uncalled-pub-api`, `pub functions nothing in this tree calls -- what pub hides from rustc's dead-code lint`, "ANSWERS the over-exposed surface: pub fns with fan_in=0. rustc's\n    dead_code analysis STOPS at pub, so an accidental `pub` immunises a\n    private helper from the dead-code warning forever and forces every\n    refactor to preserve it.\nACT try pub(crate) for one release: if nothing breaks, the exposure was\n    accidental and the item re-enters dead-code analysis. For a library\n    with real external users, read is_trait_method and sloc first.\nMISLEADS this tree is not the world: a library's genuine external API is\n    ALL rows here, so judge against whether the crate has consumers;\n    trait-impl methods reached via dyn have no static edges and appear\n    wrongly (is_trait_method=1 is the tell); re-export chains and macro\n    callers are not modelled."},
	{`global-mutable-state`, `statics holding shared mutability -- static mut, Mutex/RwLock, atomics: one lock (or race) per process`, "ANSWERS file-level `static` items that carry mutable shared state. Every\n    caller in the process serialises behind the same lock, and\n    static mut is the unsynchronised version of the same problem. A\n    global lock is a contention ceiling no amount of internal sharding\n    fixes.\nACT prefer state owned by a struct and passed explicitly; reserve\n    globals for true singletons (config read once). For a global lock,\n    measure hold time before adding callers -- locking_fns_in_module is\n    the queue forming behind it.\nMISLEADS the type test is textual on the static's declaration (Mutex<,\n    RwLock<, Atomic*, or static mut), so a newtype wrapping a Mutex\n    reads clean and is missed; the locking-fn count couples ALL lock\n    users in the module to ALL its globals -- proven per-static use is\n    not modelled."},
	{`duplicate-dependency-versions`, `same crate declared at two different versions -- cargo-deny's duplicates check over the manifests`, "ANSWERS crates the workspace pulls at more than one version: two\n    compiles, two transitive trees, and trait impls that do not unify\n    across the boundary (a serde_json::Value from each copy is a\n    different type). cargo-deny calls these duplicates; `cargo tree -d`\n    shows the pullers.\nACT align on one version, or accept the pair deliberately during a\n    migration and write down when it ends. Semver-incompatible pairs are\n    the harmful ones; patch skew is usually harmless.\nMISLEADS reads only the manifests this run saw (root plus one level\n    down), so a version pair in deeper workspace members is missed;\n    entries without a version string count as one empty version; two\n    manifests agreeing on a version do not appear (correctly)."},
	{`needlessly-async-fn`, `async fn with no await and no async block -- clippy::unused_async, ranked by caller cost`, `ANSWERS signatures that promise suspension the body never does. Every
    caller wraps the call in a state machine that has exactly one
    state, and the fn cannot be called from sync code that never needed
    to care. fan_in ranks how many call sites pay for the ceremony.
ACT make it sync; or find the await the author forgot -- an async fn
    doing blocking I/O without await is ALSO a bug, and this query
    flags it from the other side (pair with blocking-io-in-async).
MISLEADS a fn that RETURNS another fn's future without awaiting counts
    here but is semantically async; trait-impl methods must match the
    trait's asyncness and cannot simply drop the keyword; fan_in is
    zero for unused fns, which sorts them last regardless of how wrong
    they are.`},
	{`allocation-loop-under-pub-api`, `clone/collect/format inside loops, reachable from a pub fn -- churn every caller pays`, `ANSWERS the allocation-churn signal promoted to a caller-facing property:
    per-iteration allocation reachable from a published API. The
    per-function lints (clone_in_loop et al.) see the line; only the
    graph says whose public contract now includes the cost, on inputs
    the API cannot bound.
ACT hoist the allocation, reserve with_capacity, or borrow instead of
    cloning. reached_from names the published function whose
    performance profile includes this loop.
MISLEADS 4 hops deep, resolved edges only; trip counts are invisible, so
    a 3-item loop ranks like a million-item one; an allocation
    amortised out of the loop by an author who knows the bound is
    counted in full (with_capacity is shown as counter-evidence).`},
	{`rc-in-public-signature`, `pub APIs taking or returning Rc/RefCell -- the signature infects every caller with single-threadedness`, "ANSWERS public functions whose parameter types carry Rc< or RefCell<.\n    The choice is contagious: a caller in another thread cannot call\n    the API at all, and every caller inherits runtime borrow checks.\n    The compiler reports it one crate too late -- this reports it at\n    the signature, where the fix is one type.\nACT take &T or Arc<T>; return owned data. If the API is genuinely\n    single-threaded by domain (GUI widgets, a game's main loop),\n    document that -- the row is then correct-but-accepted.\nMISLEADS parameter-type text match, so `Rc<dyn Trait>` matches but a\n    newtype wrapping an Rc reads clean; a generic named `R` does not\n    match even where it monomorphises to Rc; is_public is the keyword,\n    not effective export."},
	{`ptr-arg-surface`, `&mut Vec<T> / &mut String / &mut HashMap parameters (clippy::ptr_arg), ranked by callers to migrate`, `ANSWERS mutable references to whole collections. clippy::ptr_arg says it
    per-function; the graph adds the migration bill: fan_in is how many
    call sites change when the parameter becomes &mut [T] or &mut str.
    The widest params on the most-called fns are where the abstraction
    leaks hardest.
ACT take &mut [T], &mut str, or the smallest view that satisfies the
    body; if the callee only reads, take &. A callee that genuinely
    reallocates (Vec::reserve) needs &mut Vec and is the legitimate
    row.
MISLEADS parameter-type text match: a type alias over Vec reads clean
    and is missed; resizing callees are correct and counted; fan_in
    measures migration cost, not wrongness.`},
	{`test-only-callers`, `production functions whose entire caller set is test code -- dead in prod, kept alive by their tests`, "ANSWERS the graph fact no per-file tool can state: fan_in > 0, and every\n    single edge comes from a #[test] fn or a cfg(test) module. These\n    functions pass CI while nothing in production can reach them -- the\n    test suite is the only thing keeping them (and their bugs) on\n    life support.\nACT delete the fn with its test, or move it under #[cfg(test)]; if a\n    real call site is planned, gate the cleanup on that landing.\nMISLEADS `test` is the parser's flag: integration tests in tests/ are a\n    separate crate whose edges resolve by name -- they count as test\n    callers here, which is right, but a helper shared by prod code AND\n    tests correctly does NOT appear (from_tests < callers_total); a fn\n    called only via macro or dyn has no edges and is invisible."},
}
var metricsMeta = []catEntry{
	{`graph-blindspots`, `Read this first: where the call graph cannot see`, "ANSWERS how much of every other answer here is guesswork. Rust's blind\n     spot is trait-object dispatch: `Box<dyn T>` calling `.render()` has\n     no syntactic target, and neither does anything a macro expands to.\nACT external calls (std, core, crates.io) are out of scope BY DESIGN and\n     are not counted as blindness. Read pct_blind next to dyn_sites and\n     macro_calls: a module high in both is one this tool is guessing at.\nMISLEADS a resolved edge can still be wrong. A method call resolves by\n     name within the enclosing impl and then by unique name across the\n     tree, so two types with a method of the same name make one of the\n     two edges arbitrary. Macro bodies are counted as ONE call site each\n     however many calls they expand to, so macro-heavy crates look far\n     less connected than they are."},
	{`clone-churn-per-iteration`, `Clone and allocation inside loops, weighted by depth and fan-in`, "ANSWERS where a Rust program allocates for no reason: a `.clone()` to\n     satisfy the borrow checker, a `collect()` into a temporary, a\n     `format!` per row. The weight is depth times callers, because a\n     clone in a doubly-nested loop in a leaf forty things call is a\n     different object from the same line in a one-shot setup function.\nACT borrow instead of cloning; `Cow` where the clone is conditional;\n     hoist the allocation out and reuse the buffer; `with_capacity` when\n     the size is known.\nMISLEADS none of this is confirmed without a profile. `clone()` on a Copy\n     type is free and is counted here; so is `Arc::clone`, which is a\n     refcount bump, not a deep copy -- and this cannot tell them apart\n     because that needs types. Trip count is invisible: a loop bounded at\n     3 does not care."},
	{`dyn-with-one-impl`, `Trait objects for traits that have exactly one implementation`, "ANSWERS the free devirtualisation: `Box<dyn Trait>` costs a vtable\n     indirection, a heap allocation and an inlining barrier, and if the\n     trait has one implementor the abstraction buys nothing back.\nACT swap the concrete type in, or make the caller generic over the trait\n     so the call monomorphises -- UNLESS the trait exists for a test\n     double or a plugin boundary, which are the two good reasons.\nMISLEADS impl counting is syntactic: an implementor in another crate, one\n     produced by a blanket `impl<T> Trait for T`, or one generated by a\n     derive macro is not seen, so a count of 1 means 'look', never\n     'delete'. is_generic flags blanket impls, which make the count\n     meaningless on their own."},
	{`mono-blast-radius`, `Generic functions whose body gets copied once per instantiation`, "ANSWERS what makes a Rust build slow and a binary large: rustc emits a\n     fresh copy of every generic function per distinct type argument, so\n     body_bytes times instantiations is the code the linker has to chew\n     through and the icache has to hold.\nACT the standard fix is an inner non-generic function taking `&dyn` or a\n     concrete type, with a thin generic wrapper -- the generic surface\n     stays, the duplicated body does not. Sort by est_bloat.\nMISLEADS instantiations is a PROXY: the number of distinct MODULES that\n     call this function. rustc instantiates per distinct type-argument\n     tuple, which is a type-checking result no syntactic parser can\n     enumerate -- one module calling with six types counts as 1, and six\n     modules calling with the same type counts as 6. Both directions are\n     wrong; only the ranking is worth anything. Confirm with\n     `cargo llvm-lines` before doing surgery."},
	{`cfg-feature-nobody-builds`, `#[cfg(feature)] naming a feature Cargo.toml never declares`, "ANSWERS which conditional code no build in this workspace can compile.\n     A cfg on an undeclared feature is permanently false: it type-checks\n     against nothing, no test touches it, and it rots silently until\n     someone enables the feature and finds three years of drift.\nACT declare the feature in [features], or delete the block. Since Rust\n     1.80 `cargo check` warns about unexpected cfgs -- this finds the\n     same thing across a workspace and tells you how much code is behind\n     each one.\nMISLEADS the root manifest and every manifest ONE level below it are read,\n     which covers the usual workspace layout but not a nested one --\n     `crates/foo/bar/Cargo.toml` is invisible and its features will all\n     look undeclared. Features come from the manifest TEXT, not from\n     `cargo metadata`, so anything a build script adds is missed, and a\n     feature enabled only by a dependency's own `[features]` table is not\n     followed. Check the row against the manifest before deleting code."},
	{`alloc-churn-collect-and-format`, `collect() and format!() where an iterator or a writer would do`, "ANSWERS where the code allocates a whole collection or a whole String\n     only to consume it once. `collect::<Vec<_>>()` in the middle of a\n     chain materialises the entire sequence; `format!` in a loop\n     allocates per iteration.\nACT drop the intermediate collect and keep the iterator lazy. For\n     strings, write into one reused String with `write!` or push_str,\n     and reserve with_capacity when the size is known.\nMISLEADS a collect that is genuinely needed -- to sort, to borrow twice,\n     to escape a lifetime -- is not waste, and this cannot tell those\n     apart. Read `with_capacity` as evidence someone already thought."},
	{`dynamic-dispatch-cost`, `Box<dyn Trait> and &dyn parameters on the paths that run most`, "ANSWERS where the code pays for dynamic dispatch. Every call through a\n     trait object is an indirect jump the compiler cannot inline, and it\n     blocks the optimisations that would have followed inlining.\nACT if the set of implementations is closed, an enum with a match is\n     both faster and easier to exhaustively handle. If it is open but\n     small, generics monomorphise it away -- at the cost of code size,\n     which `mono-blast-radius` measures.\nMISLEADS dynamic dispatch is the correct choice for plugin boundaries\n     and for keeping compile times sane, and a Box<dyn Error> in a cold\n     error path costs nothing. Rank by fan_in, not by count."},
	{`hot-multipliers`, `Where one fix pays back many times: highest fan-in`, `ANSWERS which symbols the rest of the tree leans on hardest.
ACT a correctness or speed win in a high-fan-in leaf pays back once per
     caller. Read it next to sloc: a large fan_in on a tiny function is
     usually a name collision rather than a hot leaf.
MISLEADS fan_in counts STATIC call sites this parser could resolve, not
     runtime frequency, and test callers are included -- in most repos a
     test helper outranks production code. Scope with --module first.`},
	{`risk-ranked`, `Review order: if you can only read N symbols this week, which N`, `ANSWERS which code combines complexity with the operations this language
     punishes hardest.
ACT start at the top. The weights are this analyzer's own -- read
     --schema for the formula rather than assuming it matches another
     language's.
MISLEADS a heuristic, not a finding. Generated and vendored files are
     excluded by default, so the real top of the list may sit in code
     this filter hid.`},
	{`parse-coverage`, `What this run could not read`, `ANSWERS whether the numbers above cover the code you think they cover.
ACT a file with parsed=0 contributed nothing at all; one with errors
     contributed only the symbols around the damage. Check meta for
     grammar_note before concluding the code is broken -- several
     grammars here are a version behind their language.
MISLEADS a file can parse perfectly and still be misunderstood. This
     shows hard failures only, never wrong interpretations.`},
	{`box-dyn-overuse`, `Box<dyn> where generics could work (clippy/box_dyn)`, `ANSWERS where Box<dyn Trait> is used, which adds a heap allocation and
     vtable indirection. A generic <T: Trait> is monomorphized and has
     neither.
ACT use generics when the number of concrete types is small and known.
MISLEADS Box<dyn> for heterogeneous collections or plugin systems is correct.
     The graph counts the usage but not the design context.`},
	{`deep-nesting`, `Functions with excessive nesting depth (clippy/cognitive_complexity)`, `ANSWERS where a function has max_nesting > 4.
ACT extract nested blocks into named helper functions; use early returns.
MISLEADS a match with many arms is nesting=1 regardless of arm count.`},
	{`too-many-params`, `Functions with too many parameters (clippy/too_many_arguments)`, `ANSWERS where a function has more than 7 parameters.
ACT use a struct parameter, or split the function.
MISLEADS a function with many generic params counts them too.`},
	{`scattered-concerns`, `A function called from many different modules (shotgun surgery)`, `ANSWERS which functions are called from many distinct modules.
ACT consider splitting or stabilizing the contract.
MISLEADS a core trait method like Default::default is called from everywhere.`},
	{`unsafe-density`, `unsafe surface per module: blocks, ops, undocumented share, normalized per ksloc`, `ANSWERS how much of each module the compiler cannot check: unsafe blocks
    and operations, how much carries no SAFETY note, and ops per
    thousand SLOC so a 40-line module and a 4,000-line one compare.
ACT the top module is where a soundness review buys the most; route its
    rows through unsafe-under-pub-api to see how much is
    caller-reachable, and safety-doc-debt for the specific blocks.
MISLEADS sums only symbols the parser attributed -- unsafe inside macro
    expansions is invisible (see macro-defined-unsafe); ops-per-block
    counting makes one dense-but-tiny block look heavy; ksloc
    normalization dings small modules and macro-generated SLOC dilutes
    the density.`},
	{`async-blocking-ratio`, `async/blocking texture per module: what fraction of blocking I/O sits inside async fns`, `ANSWERS where latency incidents will come from: async fns, awaits,
    spawns, and blocking I/O split by whether it ran under an async fn
    (stalling an executor thread) or in plain sync code (perfectly
    fine). pct_blocking_in_async is the single number to watch.
ACT a module with async_fns>0 and blocking_in_async>0 goes straight to
    blocking-io-in-async for the call chains; a module with async_fns=0
    can ignore its own blocking_io column entirely.
MISLEADS per-symbol sums, not runtime frequencies: one cold startup
    path counts the same as a hot request path; blocking_in_async is
    literally blocking_io relocated by is_async_fn, so the two columns
    are not independent evidence; hold TIMES are invisible.`},
	{`panic-density`, `panic surface per module: unwraps, expects, panic macros, indexing -- total and per ksloc`, `ANSWERS which modules fail loudly and by which mechanism: the
    unwrap/expect/panic!-family/index counts and their density per
    thousand SLOC. Density says how much; panic-frontier says who can
    trigger it; this metric is the triage map between them.
ACT a high-density module with low fan-in is a contained risk; the
    inverse -- modest density on the module everything calls -- is the
    one to harden first. safe_fallbacks shows who already uses
    unwrap_or_else-style handling.
MISLEADS assert!/assert_eq! in production helpers count (they are
    panics) though test-flavored asserts legitimately litter non-test
    helper fns; ksloc normalization dings small modules; an unwrap on a
    compile-time-known value counts like one on user input.`},
	{`trait-coupling`, `how much code is welded to each trait: implementors plus generic bounds, the change-blanket rustdoc cannot sum`, `ANSWERS the blast radius of changing a trait: COUNT of impl blocks plus
    COUNT of generic functions bounding on it. trait-breadth owns the
    implementor half alone; the generic_users column is the half that
    hides in signatures and where-clauses and breaks at monomorphisation
    time, not impl time.
ACT the top rows are the traits to freeze, seal, or split first; a
    trait with many bounds but one impl is a de-facto concrete type
    wearing a costume -- consider inlining it.
MISLEADS name-based matching across the tree: two same-named traits in
    different modules merge into one row; dyn dispatch is NOT counted
    here (dyn-with-one-impl and dynamic-dispatch-cost own that half);
    bounds written via type aliases resolve to the alias, not the
    trait.`},
	{`await-risk-density`, `yield-point exposure per module: awaits, awaits in loops, guard-live sites, RefCell guards`, `ANSWERS the module-level exposure map for the await_holding family:
    where the yield points are, how many sit in loops, and how many
    have lock guards lexically alive. One row per module; the
    specific sites live in lock-held-across-await and
    refcell-across-await.
ACT a module with many awaits and zero guard-live rows is structurally
    clean -- audit it once and move on. guard_live_sites>0 routes to
    the per-site queries; explicit_drops is the author already fixing
    it.
MISLEADS lexical guard liveness over-reports (a deliberate
    tokio::sync::Mutex hold counts); awaits hidden in helpers make a
    module look cleaner than it is; pct_guarded is unstable on modules
    with a single await point.`},
	{`error-propagation-style`, `each module's error dialect: ? vs unwrap vs discard -- pct of fallible sites that propagate`, "ANSWERS the error-handling style a module actually speaks, as a leading\n    indicator: `?`-heavy modules declare their failure paths;\n    unwrap-heavy ones discover them in production. Style is not a defect\n    per site, but the pct_propagated ranking is where error-handling\n    hardening budgets go first.\nACT read the LOWEST pct_propagated rows first; a mixed dialect inside\n    one module means two authors or two eras -- standardize on the\n    thiserror/anyhow pattern the crate already chose.\nMISLEADS counts sites, not stakes: an unwrap on a proven-Some beats a\n    swallowed timeout; `?` inside macro expansions is invisible, so\n    macro-heavy modules undercount propagation; small modules swing the\n    percentage on one site."},
	{`task-structure`, `concurrency build-out per module: task spawns vs spawn_blocking vs raw threads vs joins vs channels`, `ANSWERS which modules create concurrent work and which reclaim it: the
    spawn / spawn_blocking / thread::spawn / join / channel-op ledger.
    A module that spawns without joins next to heavy channel traffic is
    running a private job system -- find out who supervises it.
ACT pair with spawn-join-balance for the detached ledger and
    spawned-task-panic for what dies silently; raw threads inside an
    async-heavy module is an architecture smell worth a design review.
MISLEADS sums per module with no cross-module pairing: the join may
    legitimately live in the consumer module; slice::join string calls
    inflate the join column (name collision); spawns spelled through a
    wrapper fn hide entirely.`},
	{`macro-opaque-bytes`, `how much of each module the parser counted but could not read: macro bytes vs module SLOC`, `ANSWERS the honesty metric for every other number in this catalogue:
    invocation body_bytes (what the expander hides) against module
    SLOC. A macro-heavy module's call graph is an approximation and
    this says by how much, in bytes.
ACT sample-read the top module's files before trusting a ranking that
    depends on it; a definition with defines_items=1 is generating
    symbols no query here can see.
MISLEADS body_bytes is the TOKEN TREE size, not the expansion size --
    expansions shrink or explode at compile time; trivial println!
    invocations count bytes too; module SLOC excludes the macro bytes
    themselves, so hidden_per_ksloc is approximate by construction.`},
	{`api-surface-bloat`, `exposure per module: pub symbol share and pub functions nothing internal calls`, `ANSWERS the surface area an attacker reads, a semver policy protects,
    and every refactor must preserve: pub share of function/method/
    type symbols, and the pub functions with zero internal callers --
    the trim list that rustc's dead-code lint cannot see past.
ACT pub_no_callers is the cut list (per-item detail in
    uncalled-pub-api); a module above ~60% public has no encapsulation
    -- consider an internal facade behind one re-export point.
MISLEADS zero internal callers includes the REAL external API of a
    library -- for a lib that is the product, not bloat; visibility is
    the keyword, so pub-in-a-private-module inflates exposure;
    pub_no_callers counts function/method kinds only while pub_symbols
    counts every kind shown.`},
	{`external-coupling`, `which external crates each module actually reaches -- the audit and upgrade surface`, `ANSWERS dependency risk by module: distinct external crate heads among
    use statements, how many use sites, and the wildcard share. When a
    RustSec advisory lands for crate X, this says which modules to
    re-verify before the CVE page finishes loading.
ACT the top module is the dependency risk hub -- pin its versions
    hardest and read its changelogs. Pair with manifest-vs-usage to
    drop what nothing uses, and duplicate-dependency-versions for
    version skew.
MISLEADS the crate head is the text before the first ::, so a
    re-exported path (use reexport::foo::X) counts under the wrong
    head; items a macro brings into scope carry no use and are
    invisible; module grain follows where the USE sits, not where the
    types flow.`},
}

type catEntry struct{ name, title, notes string }

func (g *Graph) finishDerived() {
	g0 = g
	n := len(g.SymName)
	g.At = make([]string, n)
	g.ModName = make([]string, n)
	fTest := make([]bool, len(g.Files)+1)
	fGen := make([]bool, len(g.Files)+1)
	fPath := make([]string, len(g.Files)+1)
	fMod := make([]string, len(g.Files)+1)
	for i := range g.Files {
		f := &g.Files[i]
		fTest[f.ID] = f.IsTest == 1
		fGen[f.ID] = f.IsGenerated == 1
		fPath[f.ID] = f.Path()
		if f.ModuleID >= 1 && int(f.ModuleID) <= len(g.Modules) {
			fMod[f.ID] = g.Modules[f.ModuleID-1].Name()
		}
	}
	for i := range n {
		fid := g.SymFile[i]
		g.At[i] = fPath[fid] + ":" + strconv.Itoa(int(g.SymLine[i]))
		g.ModName[i] = fMod[fid]
	}
	filePathByID = fPath
	sFileTest = make([]bool, n+1)
	sFileGen = make([]bool, n+1)
	sFilePath = make([]string, n+1)
	for i := range n {
		fid := g.SymFile[i]
		sFileTest[i+1] = fTest[fid]
		sFileGen[i+1] = fGen[fid]
		sFilePath[i+1] = fPath[fid]
	}
	nSym := n
	out := make([][]int32, nSym+1)
	for i := range g.Edges {
		e := &g.Edges[i]
		if e.IsSelf != 0 {
			continue
		}
		if e.Caller >= 1 && int(e.Caller) <= nSym {
			out[e.Caller] = append(out[e.Caller], e.Callee)
		}
	}
	sOut = out
	asyncBySym = map[int32][]int32{}
	for i := range g.AsyncPoints {
		a := &g.AsyncPoints[i]
		asyncBySym[a.SymID] = append(asyncBySym[a.SymID], int32(i))
	}
	unsafeBySym = map[int32][]int32{}
	for i := range g.UnsafeBlks {
		u := &g.UnsafeBlks[i]
		unsafeBySym[u.SymID] = append(unsafeBySym[u.SymID], int32(i))
	}
	paramBySym = map[int32][]int32{}
	for i := range g.Params {
		p := &g.Params[i]
		paramBySym[p.SymID] = append(paramBySym[p.SymID], int32(i))
	}
	childByParent = map[int32][]int32{}
	for i := range g.SymName {
		sid := int32(i + 1)
		if p := g.SymParent[i]; p > 0 {
			childByParent[p] = append(childByParent[p], sid)
		}
	}
	attrBySym = map[int32][]int32{}
	hazBySym = map[int32][]int32{}
	for i := range g.Hazards {
		h := &g.Hazards[i]
		hazBySym[h.SymID] = append(hazBySym[h.SymID], int32(i))
	}
	implsByTrait = map[string]int32{}
	for i := range g.Impls {
		if t := g.Impls[i].TraitName(); t != "" {
			implsByTrait[t]++
		}
	}
	for i := range g.Attributes {
		if g.Attributes[i].SymID > 0 {
			attrBySym[g.Attributes[i].SymID] =
				append(attrBySym[g.Attributes[i].SymID], int32(i))
		}
	}
}

var (
	asyncBySym    map[int32][]int32
	unsafeBySym   map[int32][]int32
	paramBySym    map[int32][]int32
	childByParent map[int32][]int32
	attrBySym     map[int32][]int32
	hazBySym      map[int32][]int32
	implsByTrait  map[string]int32
	sFileTest     []bool
	sFileGen      []bool
	sFilePath     []string
	filePathByID  []string
	sOut          [][]int32
)

const maxFileBytes = 4 * 1024 * 1024
const maxLineBytes = 1024 * 1024

var commonSkipDirs = map[string]bool{
	".git": true, ".hg": true, ".svn": true, ".jj": true, ".idea": true,
	".vscode": true, ".vs": true, ".claude": true, "node_modules": true,
	"bower_components": true, "vendor": true, "third_party": true,
	"thirdparty": true, "external": true, "externals": true, "deps": true,
	"Godeps": true, "_vendor": true, "__pycache__": true, ".mypy_cache": true,
	".pytest_cache": true, ".ruff_cache": true, ".tox": true, ".venv": true,
	"venv": true, "env": true, ".env": true, "virtualenv": true, "build": true,
	"_build": true, "dist": true, "out": true, "target": true, "bin": true,
	"obj": true, ".gradle": true, ".next": true, ".nuxt": true,
	".svelte-kit": true, ".parcel-cache": true, ".turbo": true, ".cache": true,
	"coverage": true, "htmlcov": true, ".nyc_output": true,
	"site-packages": true,
}
var (
	reTestPath = regexp.MustCompile(`(?i)(^|/)(tests?|test-d|spec|specs|__tests__|__snapshots__|testing|e2e|integration[-_]tests?|testdata|test_data|test-data|fixtures?)(/|$)`)
	reRustTest = regexp.MustCompile(`(^tests?\.rs$|_test\.rs$)`)
	reVendored = regexp.MustCompile(`(?i)(^|/)(vendor|third_party|thirdparty|external|node_modules|deps)(/|$)`)
	reGenName  = regexp.MustCompile(`(?i)(\.min\.|\.bundle\.|[-_.](gen|generated|pb|g)\.|_pb2|\.g\.dart$|\.designer\.|^zz_generated)`)
	reExample  = regexp.MustCompile(`(?i)(^|/)(examples?|samples?|demos?)(/|$)`)
	reTool     = regexp.MustCompile(`(?i)(^|/)(tools?|scripts?|cmd|bin)(/|$)`)
	reMarker   = regexp.MustCompile(`(?i)\b(TODO|FIXME|XXX|HACK|BUG|NOTE|WARNING|OPTIMIZE|REVIEW|DEPRECATED|SAFETY|PANIC|UNSAFE)\b[ \t]*[:\-(]`)
)
var generatedMarkers = []string{
	"@generated", "DO NOT EDIT", "Code generated by", "AUTO-GENERATED",
	"autogenerated", "This file was automatically generated",
	"Generated by the protocol buffer compiler", "@flow-generated",
}

type srcFile struct {
	id         int32
	moduleID   int32
	rel        string
	abspath    string
	lang       string
	isTest     bool
	isGen      bool
	isVendored bool
	data       []byte
	size       int32
}
type discovered struct {
	files    []srcFile
	mods     map[string]int32
	modOrder []string
	kinds    []string
}
type walkStats struct {
	big, special, escape, denied, walkErr int
}

func (d *discovered) moduleOfName(rel string) int32 {
	name := moduleOf(rel)
	if id, ok := d.mods[name]; ok {
		return id
	}
	kind := "source"
	switch {
	case reTestPath.MatchString(name):
		kind = "test"
	case reVendored.MatchString(name):
		kind = "vendor"
	case reExample.MatchString(name):
		kind = "example"
	case reTool.MatchString(name):
		kind = "tool"
	}
	id := int32(len(d.mods) + 1)
	d.mods[name] = id
	d.modOrder = append(d.modOrder, name)
	d.kinds = append(d.kinds, kind)
	return id
}
func isGenerated(name, head string) bool {
	if reGenName.MatchString(name) {
		return true
	}
	for _, m := range generatedMarkers {
		if strings.Contains(head, m) {
			return true
		}
	}
	return false
}
func discover(root string, g *Graph, quiet bool) (*discovered, walkStats) {
	d := &discovered{mods: map[string]int32{}}
	var st walkStats
	realRoot, err := filepath.EvalSymlinks(root)
	if err != nil {
		realRoot = root
	}
	type dirEntry struct {
		path  string
		files []string
		dirs  []string
	}
	readDir := func(p string) (*dirEntry, error) {
		ents, err := os.ReadDir(p)
		if err != nil {
			return nil, err
		}
		de := &dirEntry{path: p}
		for _, e := range ents {
			name := e.Name()
			if e.IsDir() {
				if commonSkipDirs[name] || strings.HasPrefix(name, ".") {
					continue
				}
				de.dirs = append(de.dirs, name)
			} else {
				de.files = append(de.files, name)
			}
		}
		sort.Strings(de.files)
		sort.Strings(de.dirs)
		return de, nil
	}
	stack := []string{root}
	for len(stack) > 0 {
		dir := stack[len(stack)-1]
		stack = stack[:len(stack)-1]
		de, err := readDir(dir)
		if err != nil {
			st.walkErr++
			continue
		}
		var childDirs []string
		for _, fn := range de.files {
			if !strings.HasSuffix(fn, ".rs") {
				continue
			}
			full := filepath.Join(dir, fn)
			rel, _ := filepath.Rel(root, full)
			rel = filepath.ToSlash(rel)
			fi, err := os.Lstat(full)
			if err != nil {
				continue
			}
			if !fi.Mode().IsRegular() {
				st.special++
				continue
			}
			rp, err := filepath.EvalSymlinks(full)
			if err != nil {
				continue
			}
			if rp != full && !strings.HasPrefix(rp, realRoot+string(os.PathSeparator)) {
				st.escape++
				continue
			}
			var data []byte
			tooBig := false
			if fi.Size() > maxFileBytes {
				st.big++
				tooBig = true
			} else {
				data, err = os.ReadFile(full)
				if err != nil {
					if os.IsPermission(err) {
						st.denied++
					}
					continue
				}
			}
			if !tooBig && len(data) > 0 && longestByteLine(data) > maxLineBytes {
				st.big++
				tooBig = true
			}
			fr := countFileLines(data)
			row := FileRow{
				ID:         int32(len(g.Files) + 1),
				path:       cgPut(rel),
				dir:        cgPut(cgDirname(rel)),
				base:       cgPut(fn),
				ext:        cgPut(".rs"),
				lang:       cgPut(langName),
				ModuleID:   d.moduleOfName(rel),
				Bytes:      int32(fi.Size()),
				Lines:      fr.lines,
				Sloc:       fr.sloc,
				Blank:      fr.blank,
				Comment:    fr.comment,
				Doc:        fr.doc,
				MaxLine:    fr.maxLen,
				IsTest:     boolT(reTestPath.MatchString(rel) || reRustTest.MatchString(fn)),
				IsVendored: boolT(reVendored.MatchString(rel)),
			}
			head := ""
			if len(data) > 2000 {
				head = string(data[:2000])
			} else {
				head = string(data)
			}
			row.IsGenerated = boolT(isGenerated(fn, head))
			if len(data) > 0 {
				sum := sha1.Sum(data)
				row.sha1 = cgPut(hex.EncodeToString(sum[:]))
			}
			parsed := !tooBig && len(data) > 0
			if !opts.includeTests && row.IsTest == 1 {
				parsed = false
			}
			if !opts.includeGenerated && row.IsGenerated == 1 {
				parsed = false
			}
			if !opts.includeVendored && row.IsVendored == 1 {
				parsed = false
			}
			row.Parsed = boolT(parsed)
			g.Files = append(g.Files, row)
			if parsed {
				d.files = append(d.files, srcFile{
					id: row.ID, moduleID: row.ModuleID, rel: rel, abspath: full,
					lang: langName, isTest: row.IsTest == 1,
					isGen: row.IsGenerated == 1, isVendored: row.IsVendored == 1,
					data: data, size: row.Bytes,
				})
			}
		}
		for _, v := range slices.Backward(de.dirs) {
			childDirs = append(childDirs, filepath.Join(dir, v))
		}
		stack = append(stack, childDirs...)
	}
	if !quiet {
		for _, s := range []struct {
			n   int
			why string
		}{
			{st.big, "too large or with a pathologically long line -- catalogued, not parsed"},
			{st.special, "not regular files (fifo, socket, device) -- skipped"},
			{st.escape, "symlinks pointing OUTSIDE the tree -- skipped"},
			{st.denied, "unreadable (permission denied)"},
			{st.walkErr, "director(ies) could not be listed"},
		} {
			if s.n > 0 {
				printfln("  %d %s", s.n, s.why)
			}
		}
	}
	return d, st
}

type fileCounts struct{ lines, sloc, blank, comment, doc, maxLen int32 }

func countFileLines(data []byte) fileCounts {
	var c fileCounts
	cgSplitLines(string(data), func(line string) {
		ll := int32(utf8.RuneCountInString(line))
		if ll > c.maxLen {
			c.maxLen = ll
		}
		t := cgStrip(line)
		if t == "" {
			c.blank++
			c.lines++
			return
		}
		c.sloc++
		c.lines++
		t3 := t
		if len([]rune(t3)) > 3 {
			t3 = clip(t3, 3)
		}
		switch t3 {
		case "//", "#", "/*", "*", "*/", `"""`, "'''", "--", ";;", "%":
			c.comment++
		}
	})
	return c
}
func longestByteLine(data []byte) int {
	longest, cur := 0, 0
	for _, b := range data {
		if b == '\n' {
			if cur > longest {
				longest = cur
			}
			cur = 0
			continue
		}
		cur++
	}
	if cur > longest {
		longest = cur
	}
	return longest
}
func cgDirname(rel string) string {
	i := strings.LastIndexByte(rel, '/')
	if i < 0 {
		return "."
	}
	return rel[:i]
}
func boolT(b bool) int32 {
	if b {
		return 1
	}
	return 0
}

var _ = fs.ModeDir

func (g *Graph) dump(w io.Writer) {
	bw := bufio.NewWriterSize(w, 1<<20)
	defer bw.Flush()
	for _, t := range []struct {
		name  string
		ncols int
		rows  []string
	}{
		{"async_points", 11, g.dumpAsync()},
		{"attributes", 6, g.dumpAttrs()},
		{"callsites", 3, g.dumpSites()},
		{"cfg_blocks", 8, g.dumpCfgs()},
		{"crate_features", 4, g.dumpFeats()},
		{"deps", 4, g.dumpDeps()},
		{"derives", 6, g.dumpDerives()},
		{"edges", 6, g.dumpEdges()},
		{"enum_members", 5, g.dumpEnums()},
		{"fields", 14, g.dumpFields()},
		{"files", 29, g.dumpFiles()},
		{"generic_bounds", 7, g.dumpBounds()},
		{"hazards", 5, g.dumpHazards()},
		{"impls", 11, g.dumpImpls()},
		{"imports", 13, g.dumpImports()},
		{"lifetimes", 7, g.dumpLives()},
		{"literals", 7, g.dumpLits()},
		{"locals", 11, nil},
		{"macros", 10, g.dumpMacros()},
		{"markers", 6, g.dumpMarkers()},
		{"meta", 2, g.dumpMeta()},
		{"modules", 10, g.dumpModules()},
		{"params", 13, g.dumpParams()},
		{"secret_candidates", 5, g.dumpSecrets()},
		{"symbols", 199, g.dumpSymbols()},
		{"sym_fts", 3, g.dumpSymFts()},
		{"traits", 13, g.dumpTraits()},
		{"unresolved_calls", 4, g.dumpUnresolved()},
		{"unsafe_blocks", 13, g.dumpUnsafes()},
	} {
		rows := t.rows
		sort.Strings(rows)
		bw.WriteString("T " + t.name + " " + strconv.Itoa(t.ncols) + " " +
			strconv.Itoa(len(rows)) + "\n")
		for _, r := range rows {
			bw.WriteString(r)
			bw.WriteByte('\n')
		}
		bw.WriteString("E " + t.name + "\n")
	}
}
func encInt(v int32) string     { return "i:" + strconv.Itoa(int(v)) }
func encFloat(v float64) string { return "f:" + cgReprFloat(v) }
func encText(s string) string {
	var b strings.Builder
	b.WriteString("s:")
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
			if c < 0x20 || c == 0x7f {
				const hex = "0123456789ABCDEF"
				b.WriteString(`\x`)
				b.WriteByte(hex[c>>4])
				b.WriteByte(hex[c&0xf])
			} else {
				b.WriteByte(c)
			}
		}
	}
	return b.String()
}
func encOptInt(v int32) string {
	if v < 0 {
		return `\N`
	}
	return encInt(v)
}
func row(cells ...string) string { return "R " + strings.Join(cells, " ") }
func (g *Graph) dumpSymbols() []string {
	out := make([]string, 0, len(g.SymName))
	for i := range g.SymName {
		sid := int32(i + 1)
		cells := make([]string, len(symCols))
		for j, f := range symField {
			switch f {
			case fID:
				cells[j] = encInt(sid)
			case fFile:
				cells[j] = encInt(g.SymFile[i])
			case fModule:
				cells[j] = encOptInt(g.SymModule[i])
			case fParent:
				cells[j] = encOptInt(g.SymParent[i])
			case fName:
				cells[j] = encText(g.SymName[i].Str())
			case fQual:
				cells[j] = encText(g.SymQual[i].Str())
			case fKind:
				cells[j] = encText(g.SymKind[i].Str())
			case fLineS:
				cells[j] = encInt(g.SymLine[i])
			case fLineE:
				cells[j] = encInt(g.SymLineEnd[i])
			case fNLines:
				cells[j] = encInt(g.SymNLines[i])
			case fByteLo:
				cells[j] = encInt(g.SymByteLo[i])
			case fByteHi:
				cells[j] = encInt(g.SymByteHi[i])
			case fSig:
				cells[j] = encText(g.SymSig[i].Str())
			case fRet:
				cells[j] = encText(g.SymRet[i].Str())
			case fVis:
				cells[j] = encText(g.SymVis[i].Str())
			case fImpl:
				cells[j] = encText(g.SymImpl[i].Str())
			default:
				cells[j] = encInt(g.mCol(i, f))
			}
		}
		out = append(out, row(cells...))
	}
	return out
}
func (g *Graph) dumpSymFts() []string {
	row := `R \N \N \N`
	out := make([]string, len(g.SymName))
	for i := range out {
		out[i] = row
	}
	return out
}
func (g *Graph) dumpFiles() []string {
	out := make([]string, 0, len(g.Files))
	for i := range g.Files {
		f := &g.Files[i]
		out = append(out, row(encInt(f.ID), encText(f.Path()), encText(f.Dir()),
			encText(f.Base()), encText(f.Ext()), encText(f.Lang()), encInt(f.ModuleID),
			encInt(f.Bytes), encInt(f.Lines), encInt(f.Sloc), encInt(f.Blank),
			encInt(f.Comment), encInt(f.Doc), encInt(f.MaxLine), encText(f.SHA1()),
			encInt(f.Parsed), encInt(f.IsTest), encInt(f.IsGenerated),
			encInt(f.IsVendored), encInt(f.NParseErrors), encInt(f.NMissingNodes),
			encFloat(f.ParseMs), encInt(f.NSymbols), encInt(f.NFunctions),
			encInt(f.NTypes), encInt(f.NImports), encInt(f.TotalCyclo),
			encInt(f.MaxCyclo), encInt(f.TotalRisk)))
	}
	return out
}
func (g *Graph) dumpModules() []string {
	out := make([]string, 0, len(g.Modules))
	for i := range g.Modules {
		m := &g.Modules[i]
		out = append(out, row(encInt(m.ID), encText(m.Name()), encText(m.Kind()),
			encInt(m.NFiles), encInt(m.NSymbols), encInt(m.NPublic), encInt(m.Sloc),
			encInt(m.FanIn), encInt(m.FanOut), encFloat(m.Instability)))
	}
	return out
}
func (g *Graph) dumpMeta() []string {
	out := make([]string, 0, len(g.Meta))
	for _, m := range g.Meta {
		if m.Key() == "sqlite" || m.Key() == "parser" {
			continue
		}
		out = append(out, row(encText(m.Key()), encText(m.Value())))
	}
	return out
}
func (g *Graph) dumpParams() []string {
	out := make([]string, 0, len(g.Params))
	for i := range g.Params {
		p := &g.Params[i]
		out = append(out, row(encInt(p.SymID), encInt(int32(p.Pos)), encText(p.Name()),
			encText(p.Type()), `\N`, encInt(0), encInt(0),
			encInt(0), encInt(0), encInt(0),
			encInt(0), encInt(int32(p.IsUntyped)), encInt(int32(p.TypeDepth))))
	}
	return out
}
func (g *Graph) dumpFields() []string {
	out := make([]string, 0, len(g.Fields))
	for i := range g.Fields {
		f := &g.Fields[i]
		out = append(out, row(encInt(f.SymID), encInt(f.Ordinal), encText(f.Name()),
			encText(f.Type()), encText(f.Visibility()), encInt(f.Line), encInt(f.IsStatic),
			encInt(f.IsConst), encInt(f.IsMutable), encInt(f.IsNullable),
			encInt(f.IsCollection), encInt(f.IsUntyped), encInt(f.HasDefault),
			encInt(f.TypeDepth)))
	}
	return out
}
func (g *Graph) dumpEnums() []string {
	out := make([]string, 0, len(g.EnumMembers))
	for i := range g.EnumMembers {
		e := &g.EnumMembers[i]
		v := encText(e.Value())
		if !e.HasValue {
			v = `\N`
		}
		out = append(out, row(encInt(e.SymID), encInt(e.Ordinal), encText(e.Name()),
			v, encInt(e.NFields)))
	}
	return out
}
func (g *Graph) dumpEdges() []string {
	out := make([]string, 0, len(g.Edges))
	for i := range g.Edges {
		e := &g.Edges[i]
		out = append(out, row(encInt(e.Caller), encInt(e.Callee), encInt(e.NCalls),
			encInt(e.SameFile), encInt(e.SameModule), encInt(e.IsSelf)))
	}
	return out
}
func (g *Graph) dumpSites() []string {
	out := make([]string, 0, len(g.Callsites))
	for i := range g.Callsites {
		s := &g.Callsites[i]
		out = append(out, row(encInt(s.Caller), encInt(s.Callee), encInt(s.Line)))
	}
	return out
}
func (g *Graph) dumpUnresolved() []string {
	out := make([]string, 0, len(g.Unresolved))
	for i := range g.Unresolved {
		u := &g.Unresolved[i]
		out = append(out, row(encInt(u.Caller), encText(u.Name()), encInt(int32(u.N)),
			encInt(int32(u.FirstLine))))
	}
	return out
}
func (g *Graph) dumpImports() []string {
	out := make([]string, 0, len(g.Imports))
	for i := range g.Imports {
		m := &g.Imports[i]
		al := encText(m.Alias())
		if !m.HasAlias {
			al = `\N`
		}
		out = append(out, row(encInt(m.ID), encInt(m.FileID), encText(m.Target()),
			encOptInt(m.TargetID), al, encText(m.Kind()), encInt(m.Line),
			encInt(m.IsExternal), encInt(m.IsRelative), encInt(m.IsWildcard),
			encInt(m.IsTypeOnly), encInt(m.IsDynamic), encInt(m.NNames)))
	}
	return out
}
func (g *Graph) dumpHazards() []string {
	out := make([]string, 0, len(g.Hazards))
	for i := range g.Hazards {
		h := &g.Hazards[i]
		out = append(out, row(encInt(h.SymID), encText(h.Pattern()), encText(h.Category()),
			encInt(h.N), encInt(h.FirstLine)))
	}
	return out
}
func (g *Graph) dumpAttrs() []string {
	out := make([]string, 0, len(g.Attributes))
	for i := range g.Attributes {
		a := &g.Attributes[i]
		out = append(out, row(encInt(a.ID), encOptInt(a.SymID), encInt(a.FileID),
			encText(a.Name()), encText(a.Args()), encInt(a.Line)))
	}
	return out
}
func (g *Graph) dumpLits() []string {
	out := make([]string, 0, len(g.Literals))
	for i := range g.Literals {
		l := &g.Literals[i]
		out = append(out, row(encInt(l.ID), encOptInt(l.SymID), encInt(l.FileID),
			encText(l.Kind()), encText(l.Value()), encInt(l.Line), encInt(l.IsMagic)))
	}
	return out
}
func (g *Graph) dumpMarkers() []string {
	out := make([]string, 0, len(g.Markers))
	for i := range g.Markers {
		m := &g.Markers[i]
		out = append(out, row(encInt(m.ID), encInt(m.FileID), encOptInt(m.SymID),
			encText(m.Kind()), encInt(m.Line), encText(m.Text())))
	}
	return out
}
func (g *Graph) dumpTraits() []string {
	out := make([]string, 0, len(g.Traits))
	for i := range g.Traits {
		t := &g.Traits[i]
		out = append(out, row(encInt(t.SymID), encInt(t.FileID), encText(t.Name()),
			encInt(t.NRequired), encInt(t.NProvided), encInt(t.NAssocTypes),
			encInt(t.NAssocConsts), encInt(t.NSupertraits), encInt(t.IsUnsafe),
			encInt(t.IsPublic), encInt(t.IsGeneric), encInt(t.HasAssocType),
			encText(t.Methods())))
	}
	return out
}
func (g *Graph) dumpImpls() []string {
	out := make([]string, 0, len(g.Impls))
	for i := range g.Impls {
		m := &g.Impls[i]
		out = append(out, row(encInt(m.ID), encInt(m.SymID), encInt(m.FileID),
			encText(m.TypeName()), encText(m.TraitName()), encInt(m.IsUnsafe),
			encInt(m.IsNegative), encInt(m.IsGeneric), encInt(m.NMethods),
			encInt(m.NUnsafeMethods), encInt(m.Line)))
	}
	return out
}
func (g *Graph) dumpUnsafes() []string {
	out := make([]string, 0, len(g.UnsafeBlks))
	for i := range g.UnsafeBlks {
		u := &g.UnsafeBlks[i]
		out = append(out, row(encInt(u.ID), encInt(u.SymID), encInt(u.FileID),
			encInt(u.Line), encInt(u.Sloc), encInt(u.NOps), encInt(u.NDeref),
			encInt(u.NRawCalls), encInt(u.NTransmute), encInt(u.NFromRaw),
			encInt(u.HasSafety), encInt(u.InUnsafeFn), encInt(u.InLoop)))
	}
	return out
}
func (g *Graph) dumpDerives() []string {
	out := make([]string, 0, len(g.Derives))
	for i := range g.Derives {
		d := &g.Derives[i]
		out = append(out, row(encInt(d.ID), encOptInt(d.SymID), encInt(d.FileID),
			encText(d.Name()), encInt(d.IsStd), encInt(d.Line)))
	}
	return out
}
func (g *Graph) dumpLives() []string {
	out := make([]string, 0, len(g.Lifetimes))
	for i := range g.Lifetimes {
		l := &g.Lifetimes[i]
		out = append(out, row(encInt(l.ID), encInt(l.SymID), encInt(l.FileID),
			encText(l.Name()), encText(l.Kind()), encInt(l.IsStatic), encInt(l.Line)))
	}
	return out
}
func (g *Graph) dumpBounds() []string {
	out := make([]string, 0, len(g.GenBounds))
	for i := range g.GenBounds {
		b := &g.GenBounds[i]
		out = append(out, row(encInt(b.ID), encInt(b.SymID), encText(b.Param()),
			encText(b.Bound()), encInt(b.InWhere), encInt(b.IsHrtb), encInt(b.Line)))
	}
	return out
}
func (g *Graph) dumpMacros() []string {
	out := make([]string, 0, len(g.Macros))
	for i := range g.Macros {
		m := &g.Macros[i]
		out = append(out, row(encInt(m.ID), encOptInt(m.SymID), encInt(m.FileID),
			encText(m.Name()), encText(m.Kind()), encInt(m.NRules), encInt(m.BodyBytes),
			encInt(m.DefinesItems), encInt(m.NUnsafe), encInt(m.Line)))
	}
	return out
}
func (g *Graph) dumpSecrets() []string {
	out := make([]string, 0, len(g.Secrets))
	for i := range g.Secrets {
		s := &g.Secrets[i]
		out = append(out, row(encInt(s.ID), encOptInt(s.SymID), encInt(s.FileID),
			encText(s.Value()), encInt(s.Line)))
	}
	return out
}
func (g *Graph) dumpCfgs() []string {
	out := make([]string, 0, len(g.CfgBlocks))
	for i := range g.CfgBlocks {
		c := &g.CfgBlocks[i]
		out = append(out, row(encInt(c.ID), encInt(c.FileID), encOptInt(c.SymID),
			encText(c.Expr()), encText(c.Feature()), encInt(c.IsTest),
			encInt(c.IsAttrOnly), encInt(c.Line)))
	}
	return out
}
func (g *Graph) dumpAsync() []string {
	out := make([]string, 0, len(g.AsyncPoints))
	for i := range g.AsyncPoints {
		a := &g.AsyncPoints[i]
		out = append(out, row(encInt(a.ID), encInt(a.SymID), encInt(a.FileID),
			encInt(a.Line), encInt(a.InLoop), encInt(a.LoopDepth),
			encInt(a.NGuardsLive), encText(a.Guards()), encInt(a.GuardDropped),
			encText(a.Expr()), encInt(a.HasRefcellGuard)))
	}
	return out
}
func (g *Graph) dumpDeps() []string {
	out := make([]string, 0, len(g.Deps))
	for i := range g.Deps {
		d := &g.Deps[i]
		out = append(out, row(encInt(d.ID), encText(d.Name()), encText(d.Version()),
			encInt(d.IsDev)))
	}
	return out
}
func (g *Graph) dumpFeats() []string {
	out := make([]string, 0, len(g.Feat))
	for i := range g.Feat {
		f := &g.Feat[i]
		out = append(out, row(encInt(f.ID), encText(f.Name()), encText(f.Enables()),
			encInt(f.IsDefault)))
	}
	return out
}

type scopeItem struct {
	n  tsNode
	sc scope
}
type scope struct {
	symID    int32
	qual     string
	typeName string
	typeID   int32
}

func (fp *fileParser) decodeFile(rec srcFile, res *fileResult, buf []byte) {
	clear(fp.implLike)
	clear(fp.traitIDs)
	fp.src = rec.data
	tree := fp.p.decodeCST(buf, rec.data)
	if tree == nil {
		panic(fmt.Sprintf("cli cst decode failed (%d bytes out)", len(buf)))
	}
	if opts.keepTrees {
		res.recs = append(res.recs[:0], tree.recs...)
	}
	fp.tree = tree
	defer func() {
		tree.free()
		fp.tree = nil
		fp.src = nil
	}()
	root := tree.root()
	if nHasError(root) {
		res.nErr, res.nMissing = fp.countErrors(root)
	}
	fp.parseImports(root, rec, res)
	fp.walkScope(root, rec, res)
	fp.emitModuleScope(root, rec, res)
	fp.parseFileExtra(root, rec, res)
}
func (fp *fileParser) countErrors(root tsNode) (int32, int32) {
	var errs, miss int32
	cur := tsWalk(root)
	defer cur.close()
	for {
		n := cur.node()
		if tsKindName(nSymbol(n)) == "ERROR" {
			errs++
		} else if nIsMissing(n) {
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
func (fp *fileParser) walkNodes(root tsNode, fn func(tsNode) bool) {
	cur := tsWalk(root)
	defer cur.close()
	for {
		n := cur.node()
		if fn(n) {
			return
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
func (fp *fileParser) walkScope(root tsNode, rec srcFile, res *fileResult) {
	stack := make([]scopeItem, 0, 32)
	stack = pushNamedKids(stack, root, scope{})
	for len(stack) > 0 {
		it := stack[len(stack)-1]
		stack = stack[:len(stack)-1]
		cur, sc := it.n, it.sc
		if kind, ok := funcKinds[tsKindName(nSymbol(cur))]; ok {
			if kind == kFunction {
				p := nParent(cur)
				if nValid(p) && kindIs(p, "declaration_list") {
					if gp := nParent(p); nValid(gp) &&
						(kindIs(gp, "impl_item") || kindIs(gp, "trait_item")) {
						kind = kMethod
					}
				}
			}
			sid := fp.emitFunction(cur, rec, res, sc, kind)
			nm := fp.nodeName(cur)
			if nm == "" {
				nm = "?"
			}
			inner := scope{sid, sc.qual + nm + ".", sc.typeName, sc.typeID}
			stack = fp.pushBody(stack, cur, inner)
			continue
		}
		if kind, ok := typeKinds[tsKindName(nSymbol(cur))]; ok {
			sid := fp.emitType(cur, rec, res, sc, kind)
			nm := fp.nodeName(cur)
			if nm == "" {
				nm = "?"
			}
			inner := scope{sid, sc.qual + nm + ".", nm, sid}
			stack = fp.pushBody(stack, cur, inner)
			continue
		}
		stack = pushNamedKids(stack, cur, sc)
	}
}

// pushNamedKids pushes the named children of n in reverse so the stack pops
// them in document order (the order the old slices.Backward(namedKids) loop
// produced), without allocating a child slice per visited node.
func pushNamedKids(stack []scopeItem, n tsNode, sc scope) []scopeItem {
	for i := int(nNamedChildCount(n)) - 1; i >= 0; i-- {
		stack = append(stack, scopeItem{nNamedChildAt(n, uint32(i)), sc})
	}
	return stack
}

func (fp *fileParser) pushBody(stack []scopeItem, cur tsNode, inner scope) []scopeItem {
	body := nField(cur, F.body)
	if !nValid(body) {
		body = cur
	}
	return pushNamedKids(stack, body, inner)
}
func (fp *fileParser) emitFunction(n tsNode, rec srcFile, res *fileResult,
	sc scope, kind string) int32 {
	name := fp.nodeName(n)
	if name == "" {
		name = "(anonymous)"
	}
	qual := sc.qual + name
	body := nField(n, F.body)
	if !nValid(body) {
		body = n
	}
	st := fp.measure(body, nil, true)
	sid := res.newSym()
	s := &res.syms[sid-1]
	s.file, s.module = rec.id, rec.moduleID
	s.parent = sc.symID
	s.name, s.qual, s.kind = name, qual, kind
	ls := int32(nStartRow(n)) + 1
	le := int32(nEndRow(n)) + 1
	s.lineS, s.lineE, s.nLines = ls, le, le-ls+1
	s.byteLo, s.byteHi = int32(nStartByte(n)), int32(nEndByte(n))
	s.sig = fp.signatureOf(n)
	s.ret = clip(fp.returnTypeOf(n), 200)
	s.vis = fp.visibilityOf(n)
	s.implType = ""
	s.typeName = sc.typeName
	s.qualBy = true
	s.setCounts(st.counts)
	s.setM(cCyclomatic, st.cyclomatic)
	s.setM(cCognitive, st.cognitive)
	s.setM(cMaxNesting, st.maxNesting)
	s.setM(cMaxLoopDepth, st.maxLoopDepth)
	s.setM(cNTokens, st.nTokens)
	s.setM(cNOperators, st.nOperators)
	s.setM(cNOperands, st.nOperands)
	s.setM(cNDistinctOperators, int32(len(st.ops)))
	s.setM(cNDistinctOperands, int32(len(st.operands)))
	s.setM(cSloc, fp.slocOf(n))
	s.setM(cBodyBytes, int32(nEndByte(body)-nStartByte(body)))
	s.setM(cIsGenerated, boolT(rec.isGen))
	fp.countParams(n, s)
	fp.functionFlags(n, s, sc)
	doc := fp.docLines(n)
	s.setM(cNDocLines, doc)
	s.setM(cHasDoc, boolT(doc > 0))
	fp.emitParams(n, rec, sid, res)
	for _, c := range st.calls {
		if c.dynamic || c.name == "" {
			continue
		}
		res.pendSid = append(res.pendSid, sid)
		res.pendLine = append(res.pendLine, c.line)
		res.pendName = append(res.pendName, fp.internStr(c.name))
		res.pendType = append(res.pendType, fp.internStr(sc.typeName))
	}
	fp.emitHazards(st, sid, rec, res)
	for _, v := range st.secrets {
		res.secrets = append(res.secrets, SecretRow{SymID: sid, FileID: rec.id,
			Line: v[1].(int32), value: res.put(v[0].(string))})
	}
	for _, l := range st.lits {
		res.lits = append(res.lits, LitRow{SymID: sid, FileID: rec.id,
			kind: res.put(l.kind), value: res.put(clip(l.value, 200)),
			Line: l.line, IsMagic: boolT(l.magic)})
	}
	fp.functionExtra(n, body, rec, res, sid, sc, st)
	return sid
}
func (fp *fileParser) countParams(n tsNode, s *symOut) {
	params := nField(n, F.params)
	if !nValid(params) {
		return
	}
	var np, opt int32
	for i := uint32(0); i < nNamedChildCount(params); i++ {
		c := nNamedChildAt(params, i)
		if commentNodes[tsKindName(nSymbol(c))] {
			continue
		}
		np++
		if strings.HasPrefix(tsKindName(nSymbol(c)), "optional") || nValid(nField(c, F.val)) {
			opt++
		}
	}
	s.setM(cNParams, np)
	s.setM(cNOptionalParams, opt)
}
func (fp *fileParser) emitParams(n tsNode, rec srcFile, sid int32, res *fileResult) {
	params := nField(n, F.params)
	if !nValid(params) {
		return
	}
	pos := int32(0)
	for i := uint32(0); i < nNamedChildCount(params); i++ {
		p := nNamedChildAt(params, i)
		if commentNodes[tsKindName(nSymbol(p))] {
			pos++
			continue
		}
		name := fp.nodeName(p)
		ptype := ""
		if t := nField(p, F.typ); nValid(t) {
			ptype = cgStrip(fp.text(t))
		}
		if name == "" {
			name = clip(cgStrip(fp.text(p)), 80)
		}
		ptype = clip(ptype, 200)
		res.params = append(res.params, ParamRow{
			SymID: sid, Pos: uint16(pos), name: res.put(clip(name, 120)),
			typ: res.put(ptype), IsUntyped: uint8(boolT(ptype == "")),
			TypeDepth: uint16(strings.Count(ptype, "<") + strings.Count(ptype, "[")),
		})
		pos++
	}
}
func (fp *fileParser) functionFlags(n tsNode, s *symOut, sc scope) {
	mods := ""
	for i := uint32(0); i < nNamedChildCount(n); i++ {
		c := nNamedChildAt(n, i)
		if kindIs(c, "function_modifiers") {
			mods = fp.text(c)
			break
		}
	}
	params := nField(n, F.params)
	ptxt, rtxt := "", ""
	if nValid(params) {
		ptxt = fp.text(params)
	}
	if r := nField(n, F.ret); nValid(r) {
		rtxt = fp.text(r)
	}
	tp := nField(n, F.tparams)
	var where tsNode
	for i := uint32(0); i < nNamedChildCount(n); i++ {
		c := nNamedChildAt(n, i)
		if kindIs(c, "where_clause") {
			where = c
			break
		}
	}
	var nGeneric, nBounds, nLife, nHrtb, nWhere int32
	for _, sub := range []tsNode{tp, where} {
		if !nValid(sub) {
			continue
		}
		fp.walkNodes(sub, func(c tsNode) bool {
			switch tsKindName(nSymbol(c)) {
			case "type_parameter", "const_parameter":
				nGeneric++
			case "trait_bounds":
				nBounds++
			case "lifetime", "lifetime_parameter":
				nLife++
			case "higher_ranked_trait_bound", "for_lifetimes":
				nHrtb++
			case "where_predicate":
				nWhere++
			}
			return false
		})
	}
	sigTypes := ptxt + " " + rtxt
	var nDyn, nImplTrait, nRaw int32
	for _, sub := range []tsNode{params, nField(n, F.ret)} {
		if !nValid(sub) {
			continue
		}
		fp.walkNodes(sub, func(c tsNode) bool {
			switch tsKindName(nSymbol(c)) {
			case "dynamic_type":
				nDyn++
			case "abstract_type":
				nImplTrait++
			case "pointer_type":
				nRaw++
			case "lifetime":
				nLife++
			}
			return false
		})
	}
	implType := ""
	if sc.typeID != 0 && fp.implLike[sc.typeID] {
		implType = sc.typeName
	}
	isTraitMethod := int32(boolT(fp.traitIDs[sc.typeID]))
	if isTraitMethod == 0 && sc.typeID != 0 && fp.implLike[sc.typeID] {
		isTraitMethod = boolT(fp.implHasTrait(n))
	}
	attrs := fp.attrNames(n)
	attrText := strings.Join(fp.attrArgs(n), " ")
	var isTest int32
	for _, a := range attrs {
		if reTestAttr.MatchString(a) {
			isTest = 1
		}
	}
	vis := fp.visibilityOf(n)
	inForeign := int32(0)
	if p := nParent(n); nValid(p) && kindIs(p, "declaration_list") {
		if gp := nParent(p); nValid(gp) && kindIs(gp, "foreign_mod_item") {
			inForeign = 1
		}
	}
	isStatic := int32(0)
	if nValid(params) {
		isStatic = 1
		for i := uint32(0); i < nNamedChildCount(params); i++ {
			if tsKindName(nSymbol(nNamedChildAt(params, i))) == "self_parameter" {
				isStatic = 0
				break
			}
		}
	}
	var allow, expect, inline, cfg int32
	for _, a := range attrs {
		switch {
		case a == "allow":
			allow++
		case a == "expect":
			expect++
		case strings.HasPrefix(a, "inline"):
			inline++
		case strings.HasPrefix(a, "cfg"):
			cfg++
		}
	}
	pub := boolT(vis == "public")
	s.implType = clip(implType, 120)
	s.setM(cIsPublic, pub)
	s.setM(cIsExported, pub)
	s.setM(cIsAsync, boolT(strings.Contains(mods, "async")))
	s.setM(cIsAsyncFn, boolT(strings.Contains(mods, "async")))
	s.setM(cIsUnsafeFn, boolT(strings.Contains(mods, "unsafe")))
	s.setM(cIsConstFn, boolT(strings.Contains(mods, "const")))
	s.setM(cIsExternFn, boolT(strings.Contains(mods, "extern") || inForeign == 1))
	s.setM(cIsAbstract, boolT(kindIs(n, "function_signature_item")))
	s.setM(cIsTest, isTest)
	var dep int32
	for _, a := range attrs {
		if a == "deprecated" {
			dep = 1
		}
	}
	s.setM(cIsDeprecated, dep)
	s.setM(cIsEntrypoint, boolT(s.name == "main"))
	s.setM(cIsStatic, isStatic)
	s.setM(cNGenericParams, nGeneric)
	s.setM(cNTraitBounds, nBounds)
	s.setM(cNWherePredicates, nWhere)
	s.setM(cNLifetimes, nLife)
	s.setM(cNHrtb, nHrtb)
	s.setM(cNDynParams, nDyn)
	s.setM(cNImplTrait, nImplTrait)
	s.setM(cNRawPtr, nRaw)
	l1, l2, l3 := lockCounts(sigTypes)
	s.setM(cNArcMutex, l1)
	s.setM(cNRcRefcell, l2)
	s.setM(cNWeakRefs, l3)
	s.setM(cNAllowAttrs, allow)
	s.setM(cNExpectAttrs, expect)
	s.setM(cNInlineAttrs, inline)
	s.setM(cNCfgBlocks, cfg)
	s.setM(cNCfgFeatures, int32(len(reCfgFeature.FindAllString(attrText, -1))))
	s.setM(cIsTraitMethod, isTraitMethod)
}
func countMatches(re *regexp.Regexp, s string) int { return cgCount(re, s) }

func lockCounts(s string) (int32, int32, int32) {
	if !strings.Contains(s, "<") {
		return 0, 0, 0
	}
	var arc, rc, weak int32
	if strings.Contains(s, "Arc") || strings.Contains(s, "Mutex") || strings.Contains(s, "RwLock") {
		arc = int32(cgCount(reSharedMut, s))
	}
	if strings.Contains(s, "Rc") {
		rc = int32(cgCount(reRcCell, s))
	}
	if strings.Contains(s, "Weak") {
		weak = int32(cgCount(reWeak, s))
	}
	return arc, rc, weak
}
func (fp *fileParser) functionExtra(n, body tsNode, rec srcFile, res *fileResult,
	sid int32, sc scope, st *bodyStats) {
	isUnsafeFn := int32(0)
	for i := uint32(0); i < nNamedChildCount(n); i++ {
		c := nNamedChildAt(n, i)
		if kindIs(c, "function_modifiers") && strings.Contains(fp.text(c), "unsafe") {
			isUnsafeFn = 1
			break
		}
	}
	fp.emitGenerics(n, rec, sid, res)
	fp.emitAttrRows(n, rec, sid, res)
	if isUnsafeFn == 1 {
		res.hazards = append(res.hazards, HazardRow{SymID: sid,
			pattern: res.put("unsafe fn"), category: res.put("unsafe"), N: 1,
			FirstLine: int32(nStartRow(n)) + 1})
	}
	if !nValid(body) {
		return
	}
	for _, b := range st.unsafeBlocks {
		res.hazards = append(res.hazards, HazardRow{SymID: sid,
			pattern: res.put("unsafe {"), category: res.put("unsafe"), N: 1,
			FirstLine: int32(nStartRow(b)) + 1})
		fp.emitUnsafeBlock(b, rec, res, sid, isUnsafeFn,
			fp.loopDepthOf(b, body))
	}
	for _, a := range st.awaits {
		fp.emitAwait(a, rec, res, sid, body)
	}
	for _, inv := range st.invocations {
		m := nField(inv, F.macro)
		if !nValid(m) {
			continue
		}
		var tt tsNode
		for i := uint32(0); i < nNamedChildCount(inv); i++ {
			if c := nNamedChildAt(inv, i); kindIs(c, "token_tree") {
				tt = c
			}
		}
		inner := ""
		if nValid(tt) {
			inner = fp.text(tt)
		}
		res.macros = append(res.macros, MacroRow{ID: 0, SymID: sid,
			FileID: rec.id, Line: int32(nStartRow(inv)) + 1,
			name: res.put(clip(fp.text(m), 120)), kind: res.put("invocation"),
			NRules:       0,
			BodyBytes:    int32(utf8.RuneCountInString(inner)),
			DefinesItems: boolT(cgMatch(reDefinesIt, inner)),
			NUnsafe:      int32(cgCount(reUnsafeTok, inner))})
	}
}
func (fp *fileParser) emitType(n tsNode, rec srcFile, res *fileResult, sc scope, kind string) int32 {
	name := fp.nodeName(n)
	if name == "" {
		name = "(anonymous)"
	}
	qual := sc.qual + name
	body := nField(n, F.body)
	if !nValid(body) {
		body = n
	}
	st := fp.measure(body, pruneById, false)
	sid := res.newSym()
	s := &res.syms[sid-1]
	s.file, s.module = rec.id, rec.moduleID
	s.parent = sc.symID
	s.name, s.qual, s.kind = name, qual, kind
	ls := int32(nStartRow(n)) + 1
	le := int32(nEndRow(n)) + 1
	s.lineS, s.lineE, s.nLines = ls, le, le-ls+1
	s.byteLo, s.byteHi = int32(nStartByte(n)), int32(nEndByte(n))
	s.sig = clip(cgStrip(clipStr(fp.text(n), "{")), 300)
	s.ret = ""
	s.vis = fp.visibilityOf(n)
	s.typeName = sc.typeName
	s.setCounts(st.counts)
	s.setM(cSloc, fp.slocOf(n))
	s.setM(cIsGenerated, boolT(rec.isGen))
	s.setM(cNTokens, st.nTokens)
	s.setM(cNOperators, st.nOperators)
	s.setM(cNOperands, st.nOperands)
	fp.typeFlags(n, s)
	doc := fp.docLines(n)
	s.setM(cNDocLines, doc)
	s.setM(cHasDoc, boolT(doc > 0))
	if kind == kImpl || kind == kTrait {
		fp.implLike[sid] = true
		if kind == kTrait {
			fp.traitIDs[sid] = true
		}
	}
	for _, c := range st.calls {
		if c.dynamic || c.name == "" {
			continue
		}
		res.pendSid = append(res.pendSid, sid)
		res.pendLine = append(res.pendLine, c.line)
		res.pendName = append(res.pendName, fp.internStr(c.name))
		res.pendType = append(res.pendType, fp.internStr(sc.typeName))
	}
	fp.emitHazards(st, sid, rec, res)
	fp.typeExtra(n, rec, res, sid, body)
	return sid
}
func clipStr(s, sep string) string {
	if before, _, ok := strings.Cut(s, sep); ok {
		return before
	}
	return s
}
func (fp *fileParser) typeFlags(n tsNode, s *symOut) {
	vis := fp.visibilityOf(n)
	txt := fp.text(n)
	head := clipStr(txt, "{")
	attrs := fp.attrNames(n)
	argList := fp.attrArgs(n)
	tp := nField(n, F.tparams)
	var nGeneric int32
	if nValid(tp) {
		fp.walkNodes(tp, func(c tsNode) bool {
			if kindIs(c, "type_parameter") || kindIs(c, "const_parameter") {
				nGeneric++
			}
			return false
		})
	}
	pub := boolT(vis == "public")
	s.setM(cIsPublic, pub)
	s.setM(cIsExported, pub)
	s.setM(cIsUnsafeFn, boolT(fp.hasAnon(n, "unsafe")))
	s.setM(cNGenericParams, nGeneric)
	statMut := int32(0)
	if kindIs(n, "static_item") {
		for i := uint32(0); i < nNamedChildCount(n); i++ {
			if tsKindName(nSymbol(nNamedChildAt(n, i))) == "mutable_specifier" {
				statMut = 1
			}
		}
	}
	s.setM(cNStaticMut, statMut)
	l1, l2, l3 := lockCounts(txt)
	s.setM(cNArcMutex, l1)
	s.setM(cNRcRefcell, l2)
	s.setM(cNWeakRefs, l3)
	s.setM(cNBoxDyn, int32(countOccurrences(head, "dyn ")))
	var allow, expect, cfg int32
	for _, a := range attrs {
		switch {
		case a == "allow":
			allow++
		case a == "expect":
			expect++
		case strings.HasPrefix(a, "cfg"):
			cfg++
		}
	}
	s.setM(cNAllowAttrs, allow)
	s.setM(cNExpectAttrs, expect)
	s.setM(cNCfgBlocks, cfg)
	s.setM(cNCfgFeatures, int32(len(reCfgFeature.FindAllString(strings.Join(argList, " "), -1))))
	isTest := int32(0)
	if kindIs(n, "mod_item") {
		for _, a := range argList {
			if strings.Contains(a, "cfg(test)") {
				isTest = 1
			}
		}
	}
	s.setM(cIsTest, isTest)
}
func countOccurrences(s, sub string) int { return strings.Count(s, sub) }
func (fp *fileParser) typeExtra(n tsNode, rec srcFile, res *fileResult, sid int32, body tsNode) {
	fp.emitGenerics(n, rec, sid, res)
	fp.emitAttrRows(n, rec, sid, res)
	line := int32(nStartRow(n)) + 1
	switch tsKindName(nSymbol(n)) {
	case "trait_item":
		var req, prov, at, ac int32
		var names []string
		if nValid(body) {
			for i := uint32(0); i < nNamedChildCount(body); i++ {
				c := nNamedChildAt(body, i)
				switch tsKindName(nSymbol(c)) {
				case "function_signature_item":
					req++
					names = append(names, fp.nodeName(c))
				case "function_item":
					prov++
					names = append(names, fp.nodeName(c))
				case "associated_type":
					at++
				case "const_item":
					ac++
				}
			}
		}
		var nSuper int32
		if b := nField(n, F.bounds); nValid(b) {
			fp.walkNodes(b, func(c tsNode) bool {
				if kindIs(c, "type_identifier") || kindIs(c, "generic_type") {
					nSuper++
				}
				return false
			})
		}
		res.traits = append(res.traits, TraitRow{
			SymID: sid, FileID: rec.id, name: res.put(clip(fp.nodeName(n), 120)),
			NRequired: req, NProvided: prov, NAssocTypes: at, NAssocConsts: ac,
			NSupertraits: nSuper, IsUnsafe: boolT(fp.hasAnon(n, "unsafe")),
			IsPublic:     boolT(fp.visibilityOf(n) == "public"),
			IsGeneric:    boolT(nValid(nField(n, F.tparams))),
			HasAssocType: boolT(at > 0), methods: res.put(clip(strings.Join(names, ","), 400)),
		})
	case "impl_item":
		tn, tr := "", ""
		if t := nField(n, F.typ); nValid(t) {
			tn = baseType(fp.text(t))
		}
		if t := nField(n, F.trait); nValid(t) {
			tr = baseType(fp.text(t))
		}
		var nm, num int32
		if nValid(body) {
			for i := uint32(0); i < nNamedChildCount(body); i++ {
				c := nNamedChildAt(body, i)
				if tsKindName(nSymbol(c)) != "function_item" && tsKindName(nSymbol(c)) != "function_signature_item" {
					continue
				}
				nm++
				for j := uint32(0); j < nNamedChildCount(c); j++ {
					k := nNamedChildAt(c, j)
					if kindIs(k, "function_modifiers") &&
						strings.Contains(fp.text(k), "unsafe") {
						num++
						break
					}
				}
			}
		}
		res.impls = append(res.impls, ImplRow{SymID: sid, FileID: rec.id,
			typeName: res.put(tn), traitName: res.put(tr),
			IsUnsafe: boolT(fp.hasAnon(n, "unsafe")), IsNegative: boolT(fp.hasAnon(n, "!")),
			IsGeneric: 0, NMethods: nm, NUnsafeMethods: num, Line: line})
		if nValid(nField(n, F.tparams)) {
			res.impls[len(res.impls)-1].IsGeneric = 1
		}
	case "macro_definition":
		var rules int32
		for i := uint32(0); i < nNamedChildCount(n); i++ {
			if tsKindName(nSymbol(nNamedChildAt(n, i))) == "macro_rule" {
				rules++
			}
		}
		txt := fp.text(n)
		res.macros = append(res.macros, MacroRow{ID: 0, SymID: sid,
			FileID: rec.id, Line: line, name: res.put(clip(fp.nodeName(n), 120)),
			kind: res.put("definition"), NRules: rules,
			BodyBytes:    int32(utf8.RuneCountInString(txt)),
			DefinesItems: boolT(cgMatch(reDefinesIt, txt)),
			NUnsafe:      int32(cgCount(reUnsafeTok, txt))})
	case "struct_item", "union_item":
		fp.emitFields(n, rec, res, sid)
	case "enum_item":
		if !nValid(body) {
			return
		}
		var i int32
		for j := uint32(0); j < nNamedChildCount(body); j++ {
			v := nNamedChildAt(body, j)
			if tsKindName(nSymbol(v)) != "enum_variant" {
				continue
			}
			vb := nField(v, F.body)
			nf := int32(0)
			if nValid(vb) {
				nf = int32(nNamedChildCount(vb))
			}
			res.enums = append(res.enums, EnumRow{SymID: sid, Ordinal: i,
				name: res.put(clip(fp.nodeName(v), 120)), value: cgStr{},
				HasValue: false, NFields: nf})
			i++
		}
	}
}
func (fp *fileParser) emitFields(n tsNode, rec srcFile, res *fileResult, sid int32) {
	body := nField(n, F.body)
	if !nValid(body) {
		return
	}
	i := int32(0)
	for j := uint32(0); j < nNamedChildCount(body); j++ {
		f := nNamedChildAt(body, j)
		if tsKindName(nSymbol(f)) != "field_declaration" {
			continue
		}
		nm := nField(f, F.name)
		ftype := ""
		if t := nField(f, F.typ); nValid(t) {
			ftype = fp.text(t)
		}
		vis := "private"
		for k := uint32(0); k < nNamedChildCount(f); k++ {
			if tsKindName(nSymbol(nNamedChildAt(f, k))) == "visibility_modifier" {
				vis = "public"
			}
		}
		name := "_"
		if nValid(nm) {
			name = fp.text(nm)
		}
		res.fields = append(res.fields, FieldRow{
			SymID: sid, Ordinal: i, name: res.put(clip(name, 120)),
			typ: res.put(clip(ftype, 200)), vis: res.put(vis),
			Line:         int32(nStartRow(f)) + 1,
			IsNullable:   boolT(strings.HasPrefix(ftype, "Option<")),
			IsCollection: boolT(hasAnyPrefix(ftype, "Vec<", "HashMap<", "BTreeMap<", "HashSet<", "VecDeque<", "[")),
			TypeDepth:    int32(strings.Count(ftype, "<") + strings.Count(ftype, "&")),
		})
		i++
	}
}
func hasAnyPrefix(s string, p ...string) bool {
	for _, x := range p {
		if strings.HasPrefix(s, x) {
			return true
		}
	}
	return false
}
func afterLast(s, sep string) string {
	if i := strings.LastIndex(s, sep); i >= 0 {
		return s[i+len(sep):]
	}
	return s
}
func lastSeg(s string) string { return afterLast(afterLast(s, "."), "::") }
func (fp *fileParser) measure(body tsNode, prune []bool, collect bool) *bodyStats {
	st := &fp.stats
	for i := range st.counts {
		st.counts[i] = 0
	}
	clear(st.ops)
	clear(st.operands)
	st.cyclomatic, st.cognitive, st.maxNesting, st.maxLoopDepth = 1, 0, 0, 0
	st.nTokens, st.nOperators, st.nOperands = 0, 0, 0
	st.calls = st.calls[:0]
	st.lits = st.lits[:0]
	st.secrets = st.secrets[:0]
	st.unsafeBlocks = st.unsafeBlocks[:0]
	st.awaits = st.awaits[:0]
	st.invocations = st.invocations[:0]
	src := fp.src
	cur := tsWalk(body)
	defer cur.close()
	depth := 0
	loopDepth := 0
	var nestStack, loopStack []int32
	nestStack = make([]int32, 0, 32)
	loopStack = make([]int32, 0, 16)
	for {
		node := cur.node()
		id := int(nSymbol(node))
		if id >= len(bitsById) {
			id = 0
		}
		bits := bitsById[id]
		for len(nestStack) > 0 && nestStack[len(nestStack)-1] >= int32(depth) {
			nestStack = nestStack[:len(nestStack)-1]
		}
		for len(loopStack) > 0 && loopStack[len(loopStack)-1] >= int32(depth) {
			loopStack = loopStack[:len(loopStack)-1]
			loopDepth--
			if loopDepth < 0 {
				loopDepth = 0
			}
		}
		if bits&bitCounter != 0 {
			if c := counterById[id]; c >= 0 {
				st.counts[c]++
			}
		}
		if bits == 0 {
			if nChildCount(node) == 0 {
				st.nTokens++
				st.nOperands++
				st.operands[clip(string(src[nStartByte(node):nEndByte(node)]), 40)] = true
			}
		} else {
			var isElif bool
			if bits&bitElif != 0 {
				isElif = fp.isElif(node)
			}
			if namedById[id] {
				if bits&bitNest != 0 && !isElif {
					nestStack = append(nestStack, int32(depth))
					if int32(len(nestStack)) > st.maxNesting {
						st.maxNesting = int32(len(nestStack))
					}
				}
				if bits&bitLoop != 0 {
					loopStack = append(loopStack, int32(depth))
					loopDepth++
					if int32(loopDepth) > st.maxLoopDepth {
						st.maxLoopDepth = int32(loopDepth)
					}
					st.cyclomatic++
					n := int32(len(nestStack))
					if n > 1 {
						st.cognitive += n
					} else {
						st.cognitive++
					}
					st.counts[cNLoops]++
				} else if bits&bitBranch != 0 {
					st.cyclomatic++
					n := int32(len(nestStack))
					if isElif {
						st.cognitive++
					} else if n > 1 {
						st.cognitive += n
					} else {
						st.cognitive++
					}
					st.counts[cNBranches]++
					if isElif {
						st.counts[cNElif]++
					}
					if loopDepth != 0 {
						st.counts[cBranchInLoop]++
					}
				}
				switch {
				case bits&bitCall != 0:
					fp.onCall(node, st, loopDepth, len(nestStack))
				case bits&bitOp != 0:
					st.nOperators++
					st.ops[kindName[id]] = true
				case bits&bitStr != 0:
					txt := fp.text(node)
					st.counts[cNStringLit]++
					st.operands[clip(txt, 40)] = true
					st.nOperands++
					fp.onString(node, txt, st, loopDepth)
				case bits&bitNum != 0:
					txt := cgStrip(fp.text(node))
					st.nOperands++
					st.operands[txt] = true
					if !magicStr[txt] && reNum.MatchString(txt) {
						st.counts[cNMagic]++
						st.lits = append(st.lits, litSite{"number", txt,
							int32(nStartRow(node)) + 1, true})
					}
					if strings.ContainsRune(txt, '.') ||
						strings.ContainsAny(strings.ToLower(txt), "e") {
						st.counts[cNFloatLit]++
					}
				case bits&bitCmt != 0:
					st.counts[cNCommentLines] += int32(nEndRow(node) -
						nStartRow(node) + 1)
				case nChildCount(node) == 0:
					st.nTokens++
					st.nOperands++
					st.operands[clip(string(src[nStartByte(node):nEndByte(node)]), 40)] = true
				}
				if bits&bitOnNode != 0 {
					fp.onNode(node, st, loopDepth, len(nestStack))
				}
				if collect {
					switch kindName[id] {
					case "unsafe_block":
						st.unsafeBlocks = append(st.unsafeBlocks, node)
					case "await_expression":
						st.awaits = append(st.awaits, node)
					case "macro_invocation":
						st.invocations = append(st.invocations, node)
					}
				}
			} else if nChildCount(node) == 0 {
				st.nTokens++
				st.nOperands++
				st.operands[clip(string(src[nStartByte(node):nEndByte(node)]), 40)] = true
			}
		}
		descend := prune == nil || !prune[id]
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
func isIfNode(n tsNode) bool {
	if !nValid(n) {
		return false
	}
	id := int(nSymbol(n))
	if id >= len(ifById) {
		return false
	}
	return ifById[id]
}
func (fp *fileParser) isElif(node tsNode) bool {
	par := nParent(node)
	if isIfNode(par) {
		alt := nField(par, F.alt)
		return nValid(alt) && tsNodeId(alt) == tsNodeId(node)
	}
	if !nValid(par) {
		return false
	}
	gp := nParent(par)
	if !isIfNode(gp) {
		return false
	}
	alt := nField(gp, F.alt)
	if !nValid(alt) || tsNodeId(alt) != tsNodeId(par) {
		return false
	}
	first := nNamedChildAt(par, 0)
	return nValid(first) && tsNodeId(first) == tsNodeId(node)
}
func (fp *fileParser) onCall(node tsNode, st *bodyStats, loopDepth, nest int) {
	line := int32(nStartRow(node)) + 1
	inLoop := loopDepth != 0
	st.counts[cNCalls]++
	if inLoop {
		st.counts[cCallInLoop]++
	}
	if kindIs(node, "macro_invocation") {
		m := nField(node, F.macro)
		if !nValid(m) {
			st.counts[cNDynamicCalls]++
			return
		}
		name := cgStrip(fp.text(m)) + "!"
		st.calls = append(st.calls, callSite{clip(name, 200), line, false})
		if name == "format!" {
			st.counts[cNFormatMacro]++
		} else if name == "panic!" || name == "unreachable!" ||
			name == "todo!" || name == "unimplemented!" {
			st.counts[cNPanicMacro]++
		}
		if inLoop {
			if c, ok := loopCallIdx[name]; ok {
				st.counts[c]++
			}
		}
		return
	}
	fn := nField(node, F.fn)
	if !nValid(fn) {
		st.counts[cNDynamicCalls]++
		st.calls = append(st.calls, callSite{"", line, true})
		return
	}
	name := cgStrip(fp.text(fn))
	b := lastSeg(name)
	if inLoop {
		if lockInLoopBases[b] {
			st.counts[cNLockInLoop]++
		}
		if toOwnedLoopBases[b] {
			st.counts[cNToOwnedInLoop]++
		}
		if iterLoopBases[b] {
			st.counts[cNIterInLoop]++
		}
		if pushLoopBases[b] {
			st.counts[cNPushInLoop]++
		}
		if ioLoopBases[b] {
			st.counts[cNIOInLoop]++
		}
		if b == "len" {
			st.counts[cNLenInLoop]++
		}
	}
	if safeFallbackBase[b] {
		st.counts[cNSafeFallback]++
	}
	if b == "block_on" {
		st.counts[cNBlockOn]++
	}
	if b == "sleep" && strings.Contains(name, "thread") {
		st.counts[cNThreadSleep]++
	}
	if borrowMutBases[b] {
		st.counts[cNBorrowMut]++
	}
	if unwrapErrBases[b] {
		st.counts[cNUnwrapErr]++
	}
	if uncheckedBases[b] {
		st.counts[cNUncheckedCall]++
	}
	if b == "spawn" && strings.Contains(name, "thread") {
		st.counts[cNThreadSpawn]++
	}
	if joinBases[b] {
		st.counts[cNJoinCalls]++
	}
	if kindIs(fn, "generic_function") {
		if inner := nField(fn, F.fn); nValid(inner) {
			name = cgStrip(fp.text(inner))
		}
	}
	dynamic := name == ""
	if !dynamic {
		r := []rune(name)[0]
		dynamic = !unicode.IsLetter(r) && r != '_'
	}
	st.calls = append(st.calls, callSite{clip(name, 200), line, dynamic})
	if dynamic {
		st.counts[cNDynamicCalls]++
	}
	base := lastSeg(name)
	if deserBase[base] {
		st.counts[cNDeserialize]++
	}
	for _, p := range zipPfx {
		if strings.HasPrefix(name, p) {
			st.counts[cNZipRead]++
			break
		}
	}
	if cols, ok := callBaseCols[base]; ok {
		for _, c := range cols {
			st.counts[c]++
		}
	}
	for _, p := range checkedPf {
		if strings.HasPrefix(base, p) {
			st.counts[cNCheckedArith]++
			break
		}
	}
	if iterAdapters[base] {
		st.counts[cNIterAdapters]++
	}
	if blockingIO[base] || blockingIO[name] {
		fp.blockingHit(st, inLoop)
	} else {
		segs := strings.Split(strings.ReplaceAll(name, ".", "::"), "::")
		if len(segs) >= 2 && blockingIO[strings.Join(segs[len(segs)-2:], "::")] {
			fp.blockingHit(st, inLoop)
		}
	}
	if inLoop {
		for _, p := range loopCallSet {
			needle := p[0].(string)
			if needle == base || strings.Contains(name, needle) {
				st.counts[p[1].(int)]++
			}
		}
	}
}
func (fp *fileParser) blockingHit(st *bodyStats, inLoop bool) {
	st.counts[cNBlockingIO]++
	if inLoop {
		st.counts[cIOInLoop]++
	}
}
func (fp *fileParser) onString(node tsNode, txt string, st *bodyStats, loopDepth int) {
	val := strings.Trim(txt, "\"'")
	if len([]rune(val)) >= 12 && !strings.Contains(val, " ") && reSecret.MatchString(val) {
		st.secrets = append(st.secrets, [2]any{clip(val, 200),
			int32(nStartRow(node)) + 1})
	}
	if cgMatch(reSQLLit, txt) {
		st.counts[cNSqlLiteral]++
		if loopDepth != 0 {
			st.counts[cQueryInLoop]++
		}
	}
}
func (fp *fileParser) onNode(node tsNode, st *bodyStats, loopDepth, nest int) {
	switch tsKindName(nSymbol(node)) {
	case "let_declaration":
		if nValid(nField(node, F.alt)) {
			st.counts[cNLetElse]++
			st.cyclomatic++
			if nest > 1 {
				st.cognitive += int32(nest)
			} else {
				st.cognitive++
			}
		}
		pat := nField(node, F.pat)
		val := nField(node, F.val)
		if nValid(pat) && nValid(val) {
			ptxt := cgStrip(fp.text(pat))
			if ptxt == "_" {
				switch tsKindName(nSymbol(val)) {
				case "call_expression", "method_invocation", "await_expression":
					st.counts[cNErrorSwallow]++
				}
			}
			if ptxt == "_" && strings.Contains(clip(fp.text(val), 200), "map_err") {
				st.counts[cNErrorSwallow]++
			}
		}
	case "binary_expression":
		o := fp.operatorKind(node)
		switch {
		case arithOps[o]:
			st.counts[cNArith]++
			if o == "<<" || o == ">>" {
				st.counts[cNShift]++
			}
		case cmpOps[o]:
			st.counts[cNCmp]++
		case bitOps[o]:
			st.counts[cNBitop]++
		case logicOps[o]:
			st.counts[cNLogical]++
			st.cyclomatic++
		}
	case "compound_assignment_expr":
		o := fp.operatorKind(node)
		if len(o) > 0 && arithOps[o[:len(o)-1]] {
			st.counts[cNArith]++
		}
	case "unary_expression":
		if nChildCount(node) > 0 && tsKindName(nSymbol(nChildAt(node, 0))) == "*" {
			st.counts[metricDeref]++
		}
	case "index_expression":
		for i := uint32(0); i < nNamedChildCount(node); i++ {
			if tsKindName(nSymbol(nNamedChildAt(node, i))) == "range_expression" {
				st.counts[cNSliceRange]++
				break
			}
		}
	case "scoped_identifier":
		if m := cgSubmatch1(reOrdering, fp.text(node)); m != nil {
			switch m[1] {
			case "Relaxed":
				st.counts[cNRelaxedOrdering]++
			case "SeqCst":
				st.counts[cNSeqcstOrdering]++
			}
		}
	case "await_expression":
		if loopDepth != 0 {
			st.counts[cAwaitInLoop]++
		}
	case "return_expression":
		st.counts[cNEarlyReturns]++
	case "match_arm":
		pat := nField(node, F.pat)
		if nValid(pat) && cgStrip(fp.text(pat)) == "_" {
			st.counts[cNCatchBroad]++
		}
	}
}
func (fp *fileParser) operatorKind(node tsNode) string {
	op := nField(node, F.op)
	if !nValid(op) {
		return ""
	}
	return tsKindName(nSymbol(op))
}
func (fp *fileParser) nodeName(n tsNode) string {
	if kindIs(n, "impl_item") {
		t := nField(n, F.typ)
		if !nValid(t) {
			return ""
		}
		return baseType(fp.text(t))
	}
	field := F.name
	if kindIs(n, "closure_expression") {
		field = 0
	}
	if field != 0 {
		if c := nField(n, field); nValid(c) {
			return cgStrip(fp.text(c))
		}
	}
	for i := uint32(0); i < nNamedChildCount(n); i++ {
		c := nNamedChildAt(n, i)
		if identNodes[tsKindName(nSymbol(c))] {
			return cgStrip(fp.text(c))
		}
	}
	return ""
}
func (fp *fileParser) visibilityOf(n tsNode) string {
	for i := uint32(0); i < nNamedChildCount(n); i++ {
		c := nNamedChildAt(n, i)
		if kindIs(c, "visibility_modifier") {
			t := cgStrip(fp.text(c))
			if t == "pub" {
				return "public"
			}
			return t
		}
	}
	return "private"
}
func baseType(text string) string {
	t := cgStrip(text)
	t = strings.TrimLeft(t, "&")
	t = reLEading.ReplaceAllString(t, "")
	t = cgStrip(t)
	if strings.HasPrefix(t, "mut ") {
		t = t[4:]
	}
	if i := strings.Index(t, "<"); i >= 0 {
		t = t[:i]
	}
	t = cgStrip(t)
	if strings.Contains(t, "::") {
		return afterLast(t, "::")
	}
	return t
}
func (fp *fileParser) hasAnon(n tsNode, token string) bool {
	for i := uint32(0); i < uint32(nChildCount(n)); i++ {
		c := nChildAt(n, i)
		if nIsNamed(c) {
			return false
		}
		if tsKindName(nSymbol(c)) == token {
			return true
		}
	}
	return false
}
func (fp *fileParser) implHasTrait(n tsNode) bool {
	p := nParent(n)
	if !nValid(p) || tsKindName(nSymbol(p)) != "declaration_list" {
		return false
	}
	gp := nParent(p)
	return nValid(gp) && kindIs(gp, "impl_item") && nValid(nField(gp, F.trait))
}
func (fp *fileParser) slocOf(n tsNode) int32 {
	seg := fp.src[nStartByte(n):nEndByte(n)]
	c := int32(0)
	cgSplitLines(string(seg), func(line string) {
		t := cgStrip(line)
		if t == "" {
			return
		}
		switch {
		case strings.HasPrefix(t, "//"), strings.HasPrefix(t, "#"),
			strings.HasPrefix(t, "/*"), strings.HasPrefix(t, "*"),
			strings.HasPrefix(t, `"""`), strings.HasPrefix(t, "'''"),
			strings.HasPrefix(t, "--"), strings.HasPrefix(t, "%"):
		default:
			c++
		}
	})
	return c
}
func (fp *fileParser) signatureOf(n tsNode) string {
	end := nEndByte(n)
	if b := nField(n, F.body); nValid(b) {
		end = nStartByte(b)
	}
	return clip(cgStrip(string(fp.src[nStartByte(n):end])), 400)
}
func (fp *fileParser) returnTypeOf(n tsNode) string {
	r := nField(n, F.ret)
	if !nValid(r) {
		return ""
	}
	return cgStrip(fp.text(r))
}
func (fp *fileParser) docLines(n tsNode) int32 {
	prev := nPrevSibling(n)
	for nValid(prev) && kindIs(prev, "attribute_item") {
		prev = nPrevSibling(prev)
	}
	var c int32
	for nValid(prev) && commentNodes[tsKindName(nSymbol(prev))] {
		txt := strings.TrimLeft(fp.text(prev), " \t\r\n\v\f")
		sp := nStartRow(prev)
		ep := nEndRow(prev)
		switch {
		case strings.HasPrefix(txt, "///"), strings.HasPrefix(txt, "/**"),
			strings.HasPrefix(txt, "//!"):
			c += int32(ep - sp + 1)
		case c == 0 && int32(ep)+1 >= int32(nStartRow(n)):
			c += int32(ep - sp + 1)
		default:
			return c
		}
		prev = nPrevSibling(prev)
	}
	return c
}
func (fp *fileParser) attrNames(n tsNode) []string {
	var out []string
	prev := nPrevSibling(n)
	for nValid(prev) && kindIs(prev, "attribute_item") {
		a := attrOf(prev)
		if nValid(a) {
			for i := uint32(0); i < nNamedChildCount(a); i++ {
				c := nNamedChildAt(a, i)
				if kindIs(c, "identifier") || kindIs(c, "scoped_identifier") {
					out = append(out, fp.text(c))
					break
				}
			}
		}
		prev = nPrevSibling(prev)
	}
	return out
}
func (fp *fileParser) attrArgs(n tsNode) []string {
	var out []string
	prev := nPrevSibling(n)
	for nValid(prev) && kindIs(prev, "attribute_item") {
		out = append(out, fp.text(prev))
		prev = nPrevSibling(prev)
	}
	return out
}
func attrOf(item tsNode) tsNode {
	for i := uint32(0); i < nNamedChildCount(item); i++ {
		c := nNamedChildAt(item, i)
		if kindIs(c, "attribute") {
			return c
		}
	}
	return tsNode{}
}
func (fp *fileParser) loopDepthOf(n, stop tsNode) int32 {
	d := int32(0)
	cur := nParent(n)
	for nValid(cur) && tsNodeId(cur) != tsNodeId(stop) {
		if isLoopKind(tsKindName(nSymbol(cur))) {
			d++
		}
		cur = nParent(cur)
	}
	return d
}

var loopKindSet = map[string]bool{"for_expression": true, "while_expression": true, "loop_expression": true}

func isLoopKind(k string) bool { return loopKindSet[k] }

var _ = utf8.RuneCountInString

const (
	cCognitive = iota
	cMaxNesting
	cNOperators
	cNOperands
	cNDistinctOperators
	cNDistinctOperands
	cNLoops
	cNBranches
	cNElif
	cNReturns
	cNEarlyReturns
	cNSwitch
	cNCases
	cNTernary
	cNLogical
	cNTry
	cNCatch
	cNCatchBroad
	cNCatchEmpty
	cNFinally
	cNThrow
	cNLabels
	cNGotos
	cMaxLoopDepth
	cCallInLoop
	cAllocInLoop
	cIOInLoop
	cAwaitInLoop
	cLockInLoop
	cConcatInLoop
	cRegexInLoop
	cQueryInLoop
	cBranchInLoop
	cNLocals
	cNAssign
	cNCompoundAssign
	cNIncdec
	cNCmp
	cNBitop
	cNShift
	cNArith
	cNStringLit
	cNRegexLit
	cNFloatLit
	cNMagic
	cNNullCheck
	cNSubscript
	cNMemberAccess
	cNLambda
	cNClosureCapture
	cNCalls
	cNUniqueCalls
	cNDynamicCalls
	cNUnresolvedCalls
	cFanIn
	cFanOut
	cNCallsites
	cIsRecursive
	cIsLeaf
	cIsRoot
	cNHazards
	cRiskScore
	cNParams
	cNOptionalParams
	cNGenericParams
	cNOverloads
	cArityRank
	cIsPublic
	cIsStatic
	cIsAsync
	cIsGenerator
	cIsAbstract
	cIsOverride
	cIsExported
	cIsTest
	cIsDeprecated
	cIsEntrypoint
	cIsGenerated
	cNCommentLines
	cNDocLines
	cHasDoc
	cMaintainability
	cNUnsafe
	cNPanic
	cNAlloc
	cNClone
	cNLock
	cNAtomic
	cNAsync
	cNIO
	cNFfi
	cNMem
	cNExec
	cNControl
	cNLetElse
	cNUnsafeBlocks
	cNUnsafeOps
	cNSafetyComments
	cIsUnsafeFn
	cNUnwrap
	cNExpect
	cNPanicMacro
	cNIndexExpr
	cNSliceRange
	cNQuestionMark
	cNBorrowCalls
	cNCloneInLoop
	cNToOwned
	cNCollect
	cNFormatMacro
	cNSqlLiteral
	cNDeserialize
	cNZipRead
	cNWithCapacity
	cNIterAdapters
	cNAwait
	cNAsyncBlocks
	cNLockAcquire
	cNLockAcrossAwait
	cNBlockingIO
	cNBlockingInAsync
	cNSpawn
	cNSpawnBlocking
	cNChannelOps
	cIsAsyncFn
	cNAtomicOps
	cNRelaxedOrdering
	cNSeqcstOrdering
	cNArcMutex
	cNRcRefcell
	cNWeakRefs
	cNBoxDyn
	cNDynParams
	cNImplTrait
	cNTraitBounds
	cNWherePredicates
	cNLifetimes
	cNHrtb
	cNTurbofish
	cNMonoInstantiations
	cNRawPtr
	cNTransmute
	cNExternCalls
	cNFromRaw
	cNIntoRaw
	cNStaticMut
	cIsExternFn
	cNDerives
	cNMacroInvocations
	cNAllowAttrs
	cNExpectAttrs
	cNInlineAttrs
	cNCfgBlocks
	cNCfgFeatures
	cNAsCasts
	cNCheckedArith
	cNArithUnchecked
	cNMatchArms
	cNLetChains
	cIsConstFn
	cNLockInLoop
	cNToOwnedInLoop
	cNSafeFallback
	cNErrorSwallow
	cNIterInLoop
	cNPushInLoop
	cNIOInLoop
	cNBlockOn
	cNThreadSleep
	cNLenInLoop
	cNBorrowMut
	cNUnwrapErr
	cNUncheckedCall
	cNExternalCalls
	cIsTraitMethod
	cNThreadSpawn
	cNSpawnInLoop
	cNJoinCalls
	metricDeref
	metricNarrow
)

const (
	cCyclomatic = metricNarrow + iota
	cNTokens
	cSloc
	cBodyBytes
	cHalsteadVolume
	metricCount
)

const metricWide = metricCount - metricNarrow

var metricNames = map[string]int{
	"n_params": cNParams, "n_optional_params": cNOptionalParams,
	"n_generic_params": cNGenericParams, "n_overloads": cNOverloads,
	"arity_rank": cArityRank, "is_public": cIsPublic, "is_static": cIsStatic,
	"is_async": cIsAsync, "is_generator": cIsGenerator, "is_abstract": cIsAbstract,
	"is_override": cIsOverride, "is_exported": cIsExported, "is_test": cIsTest,
	"is_deprecated": cIsDeprecated, "is_entrypoint": cIsEntrypoint,
	"is_generated": cIsGenerated, "sloc": cSloc, "body_bytes": cBodyBytes,
	"n_comment_lines": cNCommentLines, "n_doc_lines": cNDocLines, "has_doc": cHasDoc,
	"cyclomatic": cCyclomatic, "cognitive": cCognitive, "max_nesting": cMaxNesting,
	"n_tokens": cNTokens, "n_operators": cNOperators, "n_operands": cNOperands,
	"n_distinct_operators": cNDistinctOperators, "n_distinct_operands": cNDistinctOperands,
	"halstead_volume": cHalsteadVolume, "maintainability": cMaintainability,
	"n_loops": cNLoops, "n_branches": cNBranches, "n_returns": cNReturns,
	"n_early_returns": cNEarlyReturns, "n_switch": cNSwitch, "n_cases": cNCases,
	"n_ternary": cNTernary, "n_logical": cNLogical, "n_try": cNTry,
	"n_catch": cNCatch, "n_catch_broad": cNCatchBroad, "n_catch_empty": cNCatchEmpty,
	"n_finally": cNFinally, "n_throw": cNThrow, "n_labels": cNLabels,
	"n_gotos": cNGotos, "max_loop_depth": cMaxLoopDepth, "call_in_loop": cCallInLoop,
	"alloc_in_loop": cAllocInLoop, "io_in_loop": cIOInLoop, "await_in_loop": cAwaitInLoop,
	"lock_in_loop": cLockInLoop, "concat_in_loop": cConcatInLoop,
	"regex_in_loop": cRegexInLoop, "query_in_loop": cQueryInLoop,
	"branch_in_loop": cBranchInLoop, "n_locals": cNLocals, "n_assign": cNAssign,
	"n_compound_assign": cNCompoundAssign, "n_incdec": cNIncdec, "n_cmp": cNCmp,
	"n_bitop": cNBitop, "n_shift": cNShift, "n_arith": cNArith,
	"n_string_lit": cNStringLit, "n_regex_lit": cNRegexLit, "n_float_lit": cNFloatLit,
	"n_magic": cNMagic, "n_null_check": cNNullCheck, "n_subscript": cNSubscript,
	"n_member_access": cNMemberAccess, "n_lambda": cNLambda,
	"n_closure_capture": cNClosureCapture, "n_calls": cNCalls,
	"n_unique_calls": cNUniqueCalls, "n_dynamic_calls": cNDynamicCalls,
	"n_unresolved_calls": cNUnresolvedCalls, "fan_in": cFanIn, "fan_out": cFanOut,
	"n_callsites": cNCallsites, "is_recursive": cIsRecursive, "is_leaf": cIsLeaf,
	"is_root": cIsRoot, "n_hazards": cNHazards, "risk_score": cRiskScore,
	"n_unsafe": cNUnsafe, "n_panic": cNPanic, "n_alloc": cNAlloc, "n_clone": cNClone,
	"n_lock": cNLock, "n_atomic": cNAtomic, "n_async": cNAsync, "n_io": cNIO,
	"n_ffi": cNFfi, "n_mem": cNMem, "n_exec": cNExec, "n_control": cNControl,
	"n_let_else": cNLetElse, "n_unsafe_blocks": cNUnsafeBlocks,
	"n_unsafe_ops": cNUnsafeOps, "n_safety_comments": cNSafetyComments,
	"is_unsafe_fn": cIsUnsafeFn, "n_unwrap": cNUnwrap, "n_expect": cNExpect,
	"n_panic_macro": cNPanicMacro, "n_index_expr": cNIndexExpr,
	"n_slice_range": cNSliceRange, "n_question_mark": cNQuestionMark,
	"n_borrow_calls": cNBorrowCalls, "n_clone_in_loop": cNCloneInLoop,
	"n_to_owned": cNToOwned, "n_collect": cNCollect, "n_format_macro": cNFormatMacro,
	"n_sql_literal": cNSqlLiteral, "n_deserialize": cNDeserialize,
	"n_zip_read": cNZipRead, "n_with_capacity": cNWithCapacity,
	"n_iter_adapters": cNIterAdapters, "n_await": cNAwait,
	"n_async_blocks": cNAsyncBlocks, "n_lock_acquire": cNLockAcquire,
	"n_lock_across_await": cNLockAcrossAwait, "n_blocking_io": cNBlockingIO,
	"n_blocking_in_async": cNBlockingInAsync, "n_spawn": cNSpawn,
	"n_spawn_blocking": cNSpawnBlocking, "n_channel_ops": cNChannelOps,
	"is_async_fn": cIsAsyncFn, "n_atomic_ops": cNAtomicOps,
	"n_relaxed_ordering": cNRelaxedOrdering, "n_seqcst_ordering": cNSeqcstOrdering,
	"n_arc_mutex": cNArcMutex, "n_rc_refcell": cNRcRefcell, "n_weak_refs": cNWeakRefs,
	"n_box_dyn": cNBoxDyn, "n_dyn_params": cNDynParams, "n_impl_trait": cNImplTrait,
	"n_trait_bounds": cNTraitBounds, "n_where_predicates": cNWherePredicates,
	"n_lifetimes": cNLifetimes, "n_hrtb": cNHrtb, "n_turbofish": cNTurbofish,
	"n_mono_instantiations": cNMonoInstantiations, "n_raw_ptr": cNRawPtr,
	"n_transmute": cNTransmute, "n_extern_calls": cNExternCalls,
	"n_from_raw": cNFromRaw, "n_into_raw": cNIntoRaw, "n_static_mut": cNStaticMut,
	"is_extern_fn": cIsExternFn, "n_derives": cNDerives,
	"n_macro_invocations": cNMacroInvocations, "n_allow_attrs": cNAllowAttrs,
	"n_expect_attrs": cNExpectAttrs, "n_inline_attrs": cNInlineAttrs,
	"n_cfg_blocks": cNCfgBlocks, "n_cfg_features": cNCfgFeatures,
	"n_as_casts": cNAsCasts, "n_checked_arith": cNCheckedArith,
	"n_arith_unchecked": cNArithUnchecked, "n_match_arms": cNMatchArms,
	"n_let_chains": cNLetChains, "is_const_fn": cIsConstFn,
	"n_lock_in_loop": cNLockInLoop, "n_to_owned_in_loop": cNToOwnedInLoop,
	"n_safe_fallback": cNSafeFallback, "n_error_swallow": cNErrorSwallow,
	"n_iter_in_loop": cNIterInLoop, "n_push_in_loop": cNPushInLoop,
	"n_io_in_loop": cNIOInLoop, "n_block_on": cNBlockOn,
	"n_thread_sleep": cNThreadSleep, "n_len_in_loop": cNLenInLoop,
	"n_borrow_mut": cNBorrowMut, "n_unwrap_err": cNUnwrapErr,
	"n_unchecked_call": cNUncheckedCall, "n_elif": cNElif,
	"n_external_calls": cNExternalCalls, "is_trait_method": cIsTraitMethod,
	"n_thread_spawn": cNThreadSpawn, "n_spawn_in_loop": cNSpawnInLoop,
	"n_join_calls": cNJoinCalls,
}

const (
	fID = -(iota + 1)
	fFile
	fModule
	fParent
	fName
	fQual
	fKind
	fLineS
	fLineE
	fNLines
	fByteLo
	fByteHi
	fSig
	fRet
	fVis
	fImpl
)

var symCols = []string{
	"id", "file_id", "module_id", "parent_id", "name", "qual_name", "kind",
	"line_start", "line_end", "n_lines", "byte_start", "byte_end", "signature",
	"return_type", "visibility", "n_params", "n_optional_params",
	"n_generic_params", "n_overloads", "arity_rank", "is_public", "is_static",
	"is_async", "is_generator", "is_abstract", "is_override", "is_exported",
	"is_test", "is_deprecated", "is_entrypoint", "is_generated", "sloc",
	"body_bytes", "n_comment_lines", "n_doc_lines", "has_doc", "cyclomatic",
	"cognitive", "max_nesting", "n_tokens", "n_operators", "n_operands",
	"n_distinct_operators", "n_distinct_operands", "halstead_volume",
	"maintainability", "n_loops", "n_branches", "n_returns", "n_early_returns",
	"n_switch", "n_cases", "n_ternary", "n_logical", "n_try", "n_catch",
	"n_catch_broad", "n_catch_empty", "n_finally", "n_throw", "n_labels",
	"n_gotos", "max_loop_depth", "call_in_loop", "alloc_in_loop", "io_in_loop",
	"await_in_loop", "lock_in_loop", "concat_in_loop", "regex_in_loop",
	"query_in_loop", "branch_in_loop", "n_locals", "n_assign",
	"n_compound_assign", "n_incdec", "n_cmp", "n_bitop", "n_shift", "n_arith",
	"n_string_lit", "n_regex_lit", "n_float_lit", "n_magic", "n_null_check",
	"n_subscript", "n_member_access", "n_lambda", "n_closure_capture", "n_calls",
	"n_unique_calls", "n_dynamic_calls", "n_unresolved_calls", "fan_in",
	"fan_out", "n_callsites", "is_recursive", "is_leaf", "is_root", "n_hazards",
	"risk_score", "n_unsafe", "n_panic", "n_alloc", "n_clone", "n_lock",
	"n_atomic", "n_async", "n_io", "n_ffi", "n_mem", "n_exec", "n_control",
	"n_let_else", "n_unsafe_blocks", "n_unsafe_ops", "n_safety_comments",
	"is_unsafe_fn", "n_unwrap", "n_expect", "n_panic_macro", "n_index_expr",
	"n_slice_range", "n_question_mark", "n_borrow_calls", "n_clone_in_loop",
	"n_to_owned", "n_collect", "n_format_macro", "n_sql_literal", "n_deserialize",
	"n_zip_read", "n_with_capacity", "n_iter_adapters", "n_await",
	"n_async_blocks", "n_lock_acquire", "n_lock_across_await", "n_blocking_io",
	"n_blocking_in_async", "n_spawn", "n_spawn_blocking", "n_channel_ops",
	"is_async_fn", "n_atomic_ops", "n_relaxed_ordering", "n_seqcst_ordering",
	"n_arc_mutex", "n_rc_refcell", "n_weak_refs", "n_box_dyn", "n_dyn_params",
	"n_impl_trait", "n_trait_bounds", "n_where_predicates", "n_lifetimes",
	"n_hrtb", "n_turbofish", "n_mono_instantiations", "n_raw_ptr", "n_transmute",
	"n_extern_calls", "n_from_raw", "n_into_raw", "n_static_mut", "is_extern_fn",
	"n_derives", "n_macro_invocations", "n_allow_attrs", "n_expect_attrs",
	"n_inline_attrs", "n_cfg_blocks", "n_cfg_features", "n_as_casts",
	"n_checked_arith", "n_arith_unchecked", "n_match_arms", "n_let_chains",
	"is_const_fn", "n_lock_in_loop", "n_to_owned_in_loop", "n_safe_fallback",
	"n_error_swallow", "n_iter_in_loop", "n_push_in_loop", "n_io_in_loop",
	"n_block_on", "n_thread_sleep", "n_len_in_loop", "n_borrow_mut",
	"n_unwrap_err", "n_unchecked_call", "n_elif", "n_external_calls",
	"impl_type", "is_trait_method", "n_thread_spawn", "n_spawn_in_loop",
	"n_join_calls",
}
var symField = buildSymField()

func buildSymField() []int {
	out := make([]int, len(symCols))
	for i, name := range symCols {
		switch name {
		case "id":
			out[i] = fID
		case "file_id":
			out[i] = fFile
		case "module_id":
			out[i] = fModule
		case "parent_id":
			out[i] = fParent
		case "name":
			out[i] = fName
		case "qual_name":
			out[i] = fQual
		case "kind":
			out[i] = fKind
		case "line_start":
			out[i] = fLineS
		case "line_end":
			out[i] = fLineE
		case "n_lines":
			out[i] = fNLines
		case "byte_start":
			out[i] = fByteLo
		case "byte_end":
			out[i] = fByteHi
		case "signature":
			out[i] = fSig
		case "return_type":
			out[i] = fRet
		case "visibility":
			out[i] = fVis
		case "impl_type":
			out[i] = fImpl
		default:
			out[i] = metricNames[name]
		}
	}
	return out
}

type Graph struct {
	Files                             []FileRow
	Modules                           []ModuleRow
	Meta                              []MetaRow
	SymFile                           []int32
	SymModule                         []int32
	SymParent                         []int32
	SymName                           []cgStr
	SymQual                           []cgStr
	SymKind                           []cgStr
	SymLine                           []int32
	SymLineEnd                        []int32
	SymNLines                         []int32
	SymByteLo                         []int32
	SymByteHi                         []int32
	SymSig                            []cgStr
	SymRet                            []cgStr
	SymVis                            []cgStr
	SymImpl                           []cgStr
	M                                 [][]uint16
	MW                                [][]int32
	Params                            []ParamRow
	Fields                            []FieldRow
	EnumMembers                       []EnumRow
	Edges                             []EdgeRow
	Callsites                         []SiteRow
	Unresolved                        []UnresRow
	Imports                           []ImportRow
	Hazards                           []HazardRow
	Attributes                        []AttrRow
	Literals                          []LitRow
	Markers                           []MarkerRow
	Traits                            []TraitRow
	Impls                             []ImplRow
	UnsafeBlks                        []UnsafeRow
	Derives                           []DeriveRow
	Lifetimes                         []LifeRow
	GenBounds                         []BoundRow
	Macros                            []MacroRow
	Secrets                           []SecretRow
	CfgBlocks                         []CfgRow
	AsyncPoints                       []AsyncRow
	Deps                              []DepRow
	Feat                              []FeatRow
	At                                []string
	ModName                           []string
	pendSid                           []int32
	pendLine                          []int32
	pendName                          []string
	pendType                          []string
	byName                            map[string][]byNameEntry
	byQual                            map[string]int32
	symType                           []string
	nExternal, nResolved, nUnresolved int
	astTrees                          []*tsTree
}
type FileRow struct {
	ID                                               int32
	padA                                             uint32
	path, dir, base, ext, lang, sha1                 cgStr
	ModuleID                                         int32
	Bytes, Lines, Sloc, Blank, Comment, Doc, MaxLine int32
	Parsed, IsTest, IsGenerated, IsVendored          int32
	NParseErrors, NMissingNodes                      int32
	ParseMs                                          float64
	NSymbols, NFunctions, NTypes, NImports           int32
	TotalCyclo, MaxCyclo, TotalRisk                  int32
	padB                                             uint32
}

func (f *FileRow) Path() string { return f.path.Str() }
func (f *FileRow) Dir() string  { return f.dir.Str() }
func (f *FileRow) Base() string { return f.base.Str() }
func (f *FileRow) Ext() string  { return f.ext.Str() }
func (f *FileRow) Lang() string { return f.lang.Str() }
func (f *FileRow) SHA1() string { return f.sha1.Str() }

type ModuleRow struct {
	ID                                             int32
	padA                                           uint32
	name, kind                                     cgStr
	NFiles, NSymbols, NPublic, Sloc, FanIn, FanOut int32
	Instability                                    float64
}

func (m *ModuleRow) Name() string { return m.name.Str() }
func (m *ModuleRow) Kind() string { return m.kind.Str() }

type MetaRow struct {
	key   cgStr
	value cgStr
}

func (m *MetaRow) Key() string   { return m.key.Str() }
func (m *MetaRow) Value() string { return m.value.Str() }

type ParamRow struct {
	SymID     int32
	padA      uint32
	name, typ cgStr
	Pos       uint16
	TypeDepth uint16
	IsUntyped uint8
	padB      [3]uint8
}

func (p *ParamRow) Name() string { return p.name.Str() }
func (p *ParamRow) Type() string { return p.typ.Str() }

type FieldRow struct {
	SymID, Ordinal          int32
	name, typ, vis          cgStr
	Line                    int32
	IsStatic, IsConst       int32
	IsMutable, IsNullable   int32
	IsCollection, IsUntyped int32
	HasDefault, TypeDepth   int32
	padA                    uint32
}

func (f *FieldRow) Name() string       { return f.name.Str() }
func (f *FieldRow) Type() string       { return f.typ.Str() }
func (f *FieldRow) Visibility() string { return f.vis.Str() }

type EnumRow struct {
	SymID, Ordinal int32
	name, value    cgStr
	HasValue       bool
	padA           [3]uint8
	NFields        int32
}

func (e *EnumRow) Name() string  { return e.name.Str() }
func (e *EnumRow) Value() string { return e.value.Str() }

type EdgeRow struct{ Caller, Callee, NCalls, SameFile, SameModule, IsSelf int32 }
type SiteRow struct{ Caller, Callee, Line int32 }
type UnresRow struct {
	name      cgStr
	Caller    int32
	FirstLine uint16
	N         uint16
}

func (u *UnresRow) Name() string { return u.name.Str() }

type ImportRow struct {
	ID                                 int32
	FileID                             int32
	target, alias, kind                cgStr
	HasAlias                           bool
	padA                               [3]uint8
	TargetID                           int32
	Line                               int32
	IsExternal, IsRelative, IsWildcard int32
	IsTypeOnly, IsDynamic, NNames      int32
	padB                               [4]uint8
}

func (m *ImportRow) Target() string { return m.target.Str() }
func (m *ImportRow) Alias() string  { return m.alias.Str() }
func (m *ImportRow) Kind() string   { return m.kind.Str() }

type HazardRow struct {
	SymID             int32
	padA              uint32
	pattern, category cgStr
	N, FirstLine      int32
}

func (h *HazardRow) Pattern() string  { return h.pattern.Str() }
func (h *HazardRow) Category() string { return h.category.Str() }

type AttrRow struct {
	ID         int32
	SymID      int32
	FileID     int32
	padA       uint32
	name, args cgStr
	Line       int32
	padB       uint32
}

func (a *AttrRow) Name() string { return a.name.Str() }
func (a *AttrRow) Args() string { return a.args.Str() }

type LitRow struct {
	ID          int32
	SymID       int32
	FileID      int32
	padA        uint32
	kind, value cgStr
	Line        int32
	IsMagic     int32
}

func (l *LitRow) Kind() string  { return l.kind.Str() }
func (l *LitRow) Value() string { return l.value.Str() }

type MarkerRow struct {
	ID     int32
	FileID int32
	SymID  int32
	padA   uint32
	kind   cgStr
	text   cgStr
	Line   int32
	padB   uint32
}

func (m *MarkerRow) Kind() string { return m.kind.Str() }
func (m *MarkerRow) Text() string { return m.text.Str() }

type TraitRow struct {
	SymID, FileID                    int32
	name                             cgStr
	NRequired, NProvided             int32
	NAssocTypes, NAssocConsts        int32
	NSupertraits, IsUnsafe, IsPublic int32
	IsGeneric, HasAssocType          int32
	padA                             uint32
	methods                          cgStr
}

func (t *TraitRow) Name() string    { return t.name.Str() }
func (t *TraitRow) Methods() string { return t.methods.Str() }

type ImplRow struct {
	ID, SymID, FileID               int32
	padA                            uint32
	typeName, traitName             cgStr
	IsUnsafe, IsNegative, IsGeneric int32
	NMethods, NUnsafeMethods, Line  int32
}

func (m *ImplRow) TypeName() string  { return m.typeName.Str() }
func (m *ImplRow) TraitName() string { return m.traitName.Str() }

type UnsafeRow struct {
	ID, SymID, FileID, Line, Sloc int32
	NOps, NDeref, NRawCalls       int32
	NTransmute, NFromRaw          int32
	HasSafety, InUnsafeFn, InLoop int32
}
type DeriveRow struct {
	ID, SymID, FileID int32
	padA              uint32
	name              cgStr
	IsStd, Line       int32
}

func (d *DeriveRow) Name() string { return d.name.Str() }

type LifeRow struct {
	ID, SymID, FileID, Line int32
	name, kind              cgStr
	IsStatic                int32
	padA                    uint32
}

func (l *LifeRow) Name() string { return l.name.Str() }
func (l *LifeRow) Kind() string { return l.kind.Str() }

type BoundRow struct {
	ID, SymID, Line int32
	padA            uint32
	param, bound    cgStr
	InWhere, IsHrtb int32
}

func (b *BoundRow) Param() string { return b.param.Str() }
func (b *BoundRow) Bound() string { return b.bound.Str() }

type MacroRow struct {
	ID, SymID, FileID, Line         int32
	name, kind                      cgStr
	NRules, BodyBytes, DefinesItems int32
	NUnsafe                         int32
}

func (m *MacroRow) Name() string { return m.name.Str() }
func (m *MacroRow) Kind() string { return m.kind.Str() }

type SecretRow struct {
	ID, SymID, FileID, Line int32
	value                   cgStr
}

func (s *SecretRow) Value() string { return s.value.Str() }

type CfgRow struct {
	ID, FileID               int32
	SymID                    int32
	padA                     uint32
	expr, feature            cgStr
	IsTest, IsAttrOnly, Line int32
	padB                     uint32
}

func (c *CfgRow) Expr() string    { return c.expr.Str() }
func (c *CfgRow) Feature() string { return c.feature.Str() }

type AsyncRow struct {
	ID, SymID, FileID, Line   int32
	InLoop, LoopDepth         int32
	NGuardsLive, GuardDropped int32
	guards, expr              cgStr
	HasRefcellGuard           int32
	padA                      uint32
}

func (a *AsyncRow) Guards() string { return a.guards.Str() }
func (a *AsyncRow) Expr() string   { return a.expr.Str() }

type DepRow struct {
	ID      int32
	padA    uint32
	name    cgStr
	version cgStr
	IsDev   int32
	padB    uint32
}

func (d *DepRow) Name() string    { return d.name.Str() }
func (d *DepRow) Version() string { return d.version.Str() }

type FeatRow struct {
	ID        int32
	padA      uint32
	name      cgStr
	enables   cgStr
	IsDefault int32
	padB      uint32
}

func (f *FeatRow) Name() string    { return f.name.Str() }
func (f *FeatRow) Enables() string { return f.enables.Str() }

func (g *Graph) N() int { return len(g.SymName) }

const mBlockSyms = 8192

func (s *symOut) setCounts(src []int32) {
	for i, v := range src[:metricNarrow] {
		if v < 0 || v > 65535 {
			panic(sprintf("metric column %d value %d exceeds the 16-bit range", i, v))
		}
		s.m[i] = uint16(v)
	}
	copy(s.mw, src[metricNarrow:metricCount])
}
func (s *symOut) setM(col int, v int32) {
	if col >= metricNarrow {
		s.mw[col-metricNarrow] = v
		return
	}
	if v < 0 || v > 65535 {
		panic(sprintf("metric column %d value %d exceeds the 16-bit range", col, v))
	}
	s.m[col] = uint16(v)
}
func (g *Graph) mCol(i, col int) int32 {
	if col >= metricNarrow {
		return g.MW[i/mBlockSyms][(i%mBlockSyms)*metricWide+col-metricNarrow]
	}
	return int32(g.M[i/mBlockSyms][(i%mBlockSyms)*metricNarrow+col])
}
func (g *Graph) Mv(sid, col int32) int32 {
	if col >= metricNarrow {
		return g.MW[(int(sid)-1)/mBlockSyms][((int(sid)-1)%mBlockSyms)*metricWide+int(col)-metricNarrow]
	}
	return int32(g.M[(int(sid)-1)/mBlockSyms][((int(sid)-1)%mBlockSyms)*metricNarrow+int(col)])
}
func (g *Graph) Set(sid, col, v int32) {
	if col >= metricNarrow {
		g.MW[(int(sid)-1)/mBlockSyms][((int(sid)-1)%mBlockSyms)*metricWide+int(col)-metricNarrow] = v
		return
	}
	if v < 0 || v > 65535 {
		panic(sprintf("metric column %d value %d exceeds the 16-bit range", col, v))
	}
	g.M[(int(sid)-1)/mBlockSyms][((int(sid)-1)%mBlockSyms)*metricNarrow+int(col)] = uint16(v)
}
func (g *Graph) Bump(sid, col int32) {
	if col >= metricNarrow {
		g.MW[(int(sid)-1)/mBlockSyms][((int(sid)-1)%mBlockSyms)*metricWide+int(col)-metricNarrow]++
		return
	}
	p := &g.M[(int(sid)-1)/mBlockSyms][((int(sid)-1)%mBlockSyms)*metricNarrow+int(col)]
	if *p == 65535 {
		panic(sprintf("metric column %d overflows the 16-bit range", col))
	}
	*p++
}
func (g *Graph) SetMeta(k, v string) {
	for i := range g.Meta {
		if g.Meta[i].key.Str() == k {
			g.Meta[i].value = cgPut(v)
			return
		}
	}
	g.Meta = append(g.Meta, MetaRow{key: cgPut(k), value: cgPut(v)})
}

const (
	kFunction = "function"
	kMethod   = "method"
	kClosure  = "closure"
	kModule   = "module"
	kStruct   = "struct"
	kEnum     = "enum"
	kUnion    = "union"
	kTrait    = "trait"
	kImpl     = "impl"
	kType     = "type"
	kConst    = "const"
	kStatic   = "static"
	kMacro    = "macro"
)

var funcKinds = map[string]string{
	"function_item":           kFunction,
	"function_signature_item": kFunction,
	"closure_expression":      kClosure,
}
var typeKinds = map[string]string{
	"struct_item":      kStruct,
	"enum_item":        kEnum,
	"union_item":       kUnion,
	"trait_item":       kTrait,
	"impl_item":        kImpl,
	"type_item":        kType,
	"mod_item":         kModule,
	"const_item":       kConst,
	"static_item":      kStatic,
	"macro_definition": kMacro,
}

func isFnKind(k string) bool { return k == kFunction || k == kMethod || k == kClosure }
func moduleOf(rel string) string {
	parts := strings.Split(strings.ReplaceAll(rel, "\\", "/"), "/")
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
	return strings.Join(head, "/")
}

const (
	bitElif = 1 << iota
	bitNest
	bitLoop
	bitBranch
	bitCall
	bitOp
	bitStr
	bitNum
	bitCmt
	bitCounter
	bitOnNode
)

var (
	ifNodes      = []string{"if_expression"}
	loopNodes    = []string{"for_expression", "while_expression", "loop_expression"}
	branchNodes  = []string{"if_expression"}
	nestNodes    = []string{"if_expression", "for_expression", "while_expression", "loop_expression", "match_expression", "closure_expression", "unsafe_block", "async_block"}
	callNodes    = []string{"call_expression", "macro_invocation"}
	commentNodes = map[string]bool{"line_comment": true, "block_comment": true}
	onNodeTypes  = []string{"let_declaration", "binary_expression", "compound_assignment_expr", "unary_expression", "index_expression", "scoped_identifier", "await_expression", "generic_type", "return_expression", "match_arm"}
	stringNodes  = []string{"string_literal", "raw_string_literal", "char_literal"}
	numberNodes  = []string{"integer_literal", "float_literal"}
	operatorNode = []string{"binary_expression", "unary_expression", "assignment_expression", "compound_assignment_expr", "index_expression", "field_expression", "reference_expression", "type_cast_expression", "range_expression", "try_expression"}
	counterTable = map[string]string{
		"return_expression":        "n_returns",
		"match_expression":         "n_switch",
		"match_arm":                "n_match_arms",
		"closure_expression":       "n_lambda",
		"await_expression":         "n_await",
		"try_expression":           "n_question_mark",
		"unsafe_block":             "n_unsafe_blocks",
		"index_expression":         "n_index_expr",
		"field_expression":         "n_member_access",
		"type_cast_expression":     "n_as_casts",
		"macro_invocation":         "n_macro_invocations",
		"let_declaration":          "n_locals",
		"assignment_expression":    "n_assign",
		"compound_assignment_expr": "n_compound_assign",
		"generic_function":         "n_turbofish",
		"pointer_type":             "n_raw_ptr",
		"dynamic_type":             "n_box_dyn",
		"abstract_type":            "n_impl_trait",
		"lifetime":                 "n_lifetimes",
		"async_block":              "n_async_blocks",
		"try_block":                "n_try",
		"let_chain":                "n_let_chains",
	}
	loopCallCounters = map[string]string{
		"clone": "n_clone_in_loop", "to_owned": "n_clone_in_loop",
		"to_vec": "n_clone_in_loop", "to_string": "n_clone_in_loop",
		"spawn": "n_spawn_in_loop", "collect": "alloc_in_loop",
		"format!": "alloc_in_loop", "vec!": "alloc_in_loop",
		"push": "alloc_in_loop", "insert": "alloc_in_loop",
		"lock": "lock_in_loop", "borrow_mut": "lock_in_loop",
		"Regex::new": "regex_in_loop", "query": "query_in_loop",
		"execute": "query_in_loop",
	}
	identNodes = map[string]bool{"identifier": true, "type_identifier": true, "field_identifier": true}
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
)
var (
	kindBits    = map[string]uint32{}
	counterIdx  = map[string]int{}
	loopCallIdx = map[string]int{}
	loopCallSet = [][2]any{}
)

func init() {
	mark := func(types []string, b uint32) {
		for _, t := range types {
			kindBits[t] |= b
		}
	}
	mark(ifNodes, bitElif)
	mark(nestNodes, bitNest)
	mark(loopNodes, bitLoop)
	mark(branchNodes, bitBranch)
	mark(callNodes, bitCall)
	mark(operatorNode, bitOp)
	mark(stringNodes, bitStr)
	mark(numberNodes, bitNum)
	mark([]string{"line_comment", "block_comment"}, bitCmt)
	mark(onNodeTypes, bitOnNode)
	for t, m := range counterTable {
		counterIdx[t] = metricNames[m]
		kindBits[t] |= bitCounter
	}
	for k, m := range loopCallCounters {
		loopCallIdx[k] = metricNames[m]
		loopCallSet = append(loopCallSet, [2]any{k, metricNames[m]})
	}
}

type fields struct {
	body, name, typ, params, ret, alt, cond, fn, macro, trait, pat, val, op,
	arg, args, alias, bounds, left, path, targs, tparams uint16
}

var F fields
var (
	bitsById    []uint32
	counterById []int32
	pruneById   []bool
	ifById      []bool
	loopById    []bool
	opById      []bool
	namedById   []bool
	kindName    []string
)
var kindIDNames = []string{
	"ERROR", "attribute", "attribute_item", "block", "block_comment",
	"closure_expression", "const_parameter", "declaration_list",
	"foreign_mod_item", "function_modifiers", "function_signature_item",
	"generic_function", "generic_type", "identifier", "impl_item",
	"line_comment", "macro_invocation", "mod_item", "scoped_identifier",
	"static_item", "token_tree", "trait_item", "type_identifier",
	"type_parameter", "use_as_clause", "visibility_modifier", "where_clause",
}

func buildKindTables() {
	n := tsKindCount()
	bitsById = make([]uint32, n)
	counterById = make([]int32, n)
	pruneById = make([]bool, n)
	ifById = make([]bool, n)
	loopById = make([]bool, n)
	opById = make([]bool, n)
	namedById = make([]bool, n)
	kindName = make([]string, n)
	for id := range n {
		kindName[id] = tsKindName(uint16(id))
		namedById[id] = tsKindIsNamed(uint16(id))
	}
	pruneSet := map[string]bool{}
	for k := range pruneKinds {
		pruneSet[k] = true
	}
	ifSet := map[string]bool{}
	for _, k := range ifNodes {
		ifSet[k] = true
	}
	loopSet := map[string]bool{}
	for _, k := range loopNodes {
		loopSet[k] = true
	}
	opSet := map[string]bool{}
	for _, k := range operatorNode {
		opSet[k] = true
	}
	want := map[string]bool{}
	for _, k := range kindIDNames {
		want[k] = true
	}
	for id := range n {
		k := kindName[id]
		bitsById[id] |= kindBits[k]
		if m, ok := counterTable[k]; ok {
			counterById[id] = int32(metricNames[m])
		}
		pruneById[id] = pruneSet[k]
		ifById[id] = ifSet[k]
		loopById[id] = loopSet[k]
		opById[id] = opSet[k]
		if want[k] {
			kindIDs[k] = append(kindIDs[k], uint16(id))
		}
	}
}
func init() { initFields(); buildKindTables() }
func initFields() {
	get := tsFieldID
	F.body = get("body")
	F.name = get("name")
	F.typ = get("type")
	F.params = get("parameters")
	F.ret = get("return_type")
	F.alt = get("alternative")
	F.cond = get("condition")
	F.fn = get("function")
	F.macro = get("macro")
	F.trait = get("trait")
	F.pat = get("pattern")
	F.val = get("value")
	F.op = get("operator")
	F.arg = get("argument")
	F.args = get("arguments")
	F.alias = get("alias")
	F.bounds = get("bounds")
	F.left = get("left")
	F.path = get("path")
	F.targs = get("type_arguments")
	F.tparams = get("type_parameters")
}

var (
	hazardCalls = map[string]string{
		"unwrap": "panic", "expect": "panic", "unwrap_err": "panic",
		"expect_err": "panic", "unwrap_unchecked": "panic",
		"unwrap_or_default": "panic", "panic!": "panic", "unreachable!": "panic",
		"todo!": "panic", "unimplemented!": "panic", "assert!": "panic",
		"assert_eq!": "panic", "assert_ne!": "panic", "debug_assert!": "panic",
		"borrow": "panic", "borrow_mut": "panic", "abort": "panic",
		"clone": "clone", "cloned": "clone", "to_owned": "clone",
		"to_vec": "clone", "to_string": "clone", "into_owned": "clone",
		"clone_from": "clone", "deep_clone": "clone",
		"Vec::new": "alloc", "Vec::with_capacity": "alloc", "vec!": "alloc",
		"String::new": "alloc", "String::with_capacity": "alloc",
		"Box::new": "alloc", "Rc::new": "alloc", "Arc::new": "alloc",
		"collect": "alloc", "format!": "alloc", "extend": "alloc",
		"reserve": "alloc", "leak": "alloc", "into_boxed_slice": "alloc",
		"with_capacity": "alloc", "to_vec_in": "alloc",
		"lock": "lock", "try_lock": "lock", "read": "lock", "write": "lock",
		"RefCell::new": "lock", "Mutex::new": "lock", "RwLock::new": "lock",
		"Condvar::wait": "lock", "wait_timeout": "lock", "write_owned": "lock",
		"read_owned": "lock", "lock_owned": "lock",
		"load": "atomic", "store": "atomic", "compare_exchange": "atomic",
		"compare_exchange_weak": "atomic", "fetch_add": "atomic",
		"fetch_sub": "atomic", "fetch_update": "atomic", "fetch_or": "atomic",
		"swap": "atomic", "fence": "atomic", "compiler_fence": "atomic",
		"spawn": "async", "spawn_blocking": "async", "spawn_local": "async",
		"block_on": "async", "join!": "async", "try_join!": "async",
		"select!": "async", "Box::pin": "async", "send": "async", "recv": "async",
		"try_send": "async", "try_recv": "async", "blocking_send": "async",
		"blocking_recv": "async", "join_all": "async", "timeout": "async",
		"File::open": "io", "File::create": "io", "fs::read": "io",
		"fs::read_to_string": "io", "fs::write": "io", "fs::remove_file": "io",
		"fs::create_dir_all": "io", "fs::metadata": "io", "read_to_string": "io",
		"read_to_end": "io", "write_all": "io", "flush": "io",
		"thread::sleep": "io", "TcpStream::connect": "io", "TcpListener::bind": "io",
		"println!": "io", "eprintln!": "io", "print!": "io", "eprint!": "io",
		"stdin": "io", "read_line": "io", "BufReader::new": "io",
		"from_raw": "ffi", "into_raw": "ffi", "CStr::from_ptr": "ffi",
		"CString::from_raw": "ffi", "CString::into_raw": "ffi",
		"from_raw_parts": "ffi", "from_raw_parts_mut": "ffi",
		"NonNull::new_unchecked": "ffi", "as_ptr": "ffi", "as_mut_ptr": "ffi",
		"from_raw_fd": "ffi", "into_raw_fd": "ffi",
		"transmute": "mem", "transmute_copy": "mem", "mem::forget": "mem",
		"MaybeUninit::uninit": "mem", "assume_init": "mem", "ptr::read": "mem",
		"ptr::write": "mem", "copy_nonoverlapping": "mem", "set_len": "mem",
		"get_unchecked": "mem", "get_unchecked_mut": "mem",
		"Pin::new_unchecked": "mem", "Box::leak": "mem", "zeroed": "mem",
		"ptr::null_mut": "mem", "offset": "mem", "add": "mem",
		"Command::new": "exec", "process::exit": "exec", "exit": "exec",
		"Command::spawn": "exec", "status": "exec", "output": "exec",
		"catch_unwind": "control", "resume_unwind": "control",
		"set_hook": "control", "take_hook": "control",
	}
	blockingIO = setOf(`
File::open File::create fs::read fs::read_to_string fs::write fs::remove_file
fs::create_dir_all fs::metadata fs::read_dir read_to_string read_to_end
write_all thread::sleep TcpStream::connect TcpListener::bind read_line
recv_timeout join wait lock_blocking blocking_send blocking_recv`)
	iterAdapters = setOf(`
map filter filter_map flat_map flatten fold try_fold scan zip chain take skip
take_while skip_while step_by enumerate rev peekable inspect cloned copied
collect partition unzip windows chunks chunks_exact for_each any all find
find_map position count sum product min_by max_by min_by_key max_by_key
sort_by sort_by_key dedup retain`)
	stdRoots  = setOf("std core alloc proc_macro test")
	stdMacros = setOf(`
println eprintln print eprint format write writeln panic unreachable todo
unimplemented assert assert_eq assert_ne debug_assert debug_assert_eq
debug_assert_ne vec matches dbg include include_str include_bytes concat
stringify line file column module_path cfg env option_env compile_error
thread_local try_join join select tokio_test`)
	prelude = setOf(`
Some None Ok Err Box Vec String Option Result Rc Arc RefCell Cell Mutex RwLock
HashMap HashSet BTreeMap BTreeSet VecDeque Cow Default Clone Copy Drop From
Into TryFrom TryInto Iterator IntoIterator Send Sync Sized Fn FnMut FnOnce
drop print len is_empty iter into_iter next self Self true false`)
	arithOps         = setOf("+ - * / % << >>")
	cmpOps           = setOf("== != < > <= >=")
	bitOps           = setOf("& | ^")
	logicOps         = setOf("&& ||")
	checkedPf        = []string{"checked_", "wrapping_", "saturating_", "overflowing_", "unchecked_"}
	zipPfx           = []string{"ZipArchive::", "zip::"}
	deserBase        = setOf("from_str", "from_slice", "from_reader", "from_bytes")
	lockInLoopBases  = setOf("lock", "read", "write")
	toOwnedLoopBases = setOf("to_string", "to_owned", "to_vec")
	safeFallbackBase = setOf("unwrap_or_else", "unwrap_or_default", "ok_or_else")
	iterLoopBases    = setOf("iter", "into_iter", "chars", "bytes")
	pushLoopBases    = setOf("push", "insert", "extend")
	ioLoopBases      = setOf("read_to_string", "read_to_end", "write_all")
	borrowMutBases   = setOf("get_mut", "borrow_mut")
	unwrapErrBases   = setOf("expect_err", "unwrap_err")
	uncheckedBases   = setOf("from_utf8_unchecked", "get_unchecked", "get_unchecked_mut")
	joinBases        = setOf("join", "join_all", "try_join", "join_next", "try_join_all")
	stdDerives       = setOf("Debug Clone Copy PartialEq Eq PartialOrd Ord Hash Default")
)
var callBaseCols = map[string][]int{
	"unwrap": {cNUnwrap}, "expect": {cNExpect},
	"clone": {cNClone}, "cloned": {cNClone},
	"to_owned": {cNToOwned}, "to_vec": {cNToOwned}, "to_string": {cNToOwned},
	"collect": {cNCollect}, "with_capacity": {cNWithCapacity},
	"borrow": {cNBorrowCalls, cNLockAcquire}, "borrow_mut": {cNBorrowCalls, cNLockAcquire},
	"lock": {cNLockAcquire}, "try_lock": {cNLockAcquire},
	"read": {cNLockAcquire}, "write": {cNLockAcquire}, "lock_owned": {cNLockAcquire},
	"spawn":                 {cNSpawn},
	"spawn_blocking":        {cNSpawnBlocking},
	"block_in_place":        {cNSpawnBlocking},
	"send":                  {cNChannelOps},
	"recv":                  {cNChannelOps},
	"try_send":              {cNChannelOps},
	"try_recv":              {cNChannelOps},
	"blocking_send":         {cNChannelOps},
	"blocking_recv":         {cNChannelOps},
	"load":                  {cNAtomicOps},
	"store":                 {cNAtomicOps},
	"fetch_add":             {cNAtomicOps},
	"fetch_sub":             {cNAtomicOps},
	"fetch_update":          {cNAtomicOps},
	"fetch_or":              {cNAtomicOps},
	"compare_exchange":      {cNAtomicOps},
	"compare_exchange_weak": {cNAtomicOps},
	"fence":                 {cNAtomicOps},
	"transmute":             {cNTransmute},
	"transmute_copy":        {cNTransmute},
	"from_raw":              {cNFromRaw},
	"from_raw_parts":        {cNFromRaw},
	"from_raw_parts_mut":    {cNFromRaw},
	"from_raw_fd":           {cNFromRaw},
	"into_raw":              {cNIntoRaw},
	"into_raw_fd":           {cNIntoRaw},
}
var (
	reSharedMut  = regexp.MustCompile(`\b(?:Arc|Mutex|RwLock)\s*<\s*(?:Mutex|RwLock)\s*<`)
	reRcCell     = regexp.MustCompile(`\bRc\s*<\s*(?:RefCell|Cell)\s*<`)
	reWeak       = regexp.MustCompile(`\bWeak\s*<`)
	reGuard      = regexp.MustCompile(`\.\s*(lock|try_lock|read|write|borrow|borrow_mut|lock_owned|read_owned|write_owned)\s*\(`)
	reSafety     = regexp.MustCompile(`(?im)^\s*(?:/{2,}!?|/\*+|\*)\s*#*\s*SAFETY\b[:\-\s]`)
	reOrdering   = regexp.MustCompile(`\bOrdering::(Relaxed|Acquire|Release|AcqRel|SeqCst)\b`)
	reSQLLit     = regexp.MustCompile(`(?i)\b(SELECT\s|INSERT\s+INTO|UPDATE\s+\w|DELETE\s+FROM)\b`)
	reCfgFeature = regexp.MustCompile(`feature\s*=\s*"([^"]+)"`)
	reTestAttr   = regexp.MustCompile(`^(?:test|bench|.*::test|rstest|proptest|tokio::test|async_std::test|quickcheck)$`)
	reSecret     = regexp.MustCompile(`(?i)(api[_-]?key|apikey|secret|password|passwd|pwd|token|bearer|access[_-]?key|private[_-]?key|client[_-]?secret|auth[_-]?token|jwt|credential|smtp[_-]?pass|db[_-]?pass|sk_live|rk_live|pk_live|ghp_|xoxb-|AKIA)`)
	reNum        = regexp.MustCompile(`^[-+]?(?:0[xXbBoO][0-9a-fA-F_]+|[\d_]+(?:\.[\d_]*)?(?:[eE][-+]?\d+)?)[uUlLfFdD]*$`)
	reDefinesIt  = regexp.MustCompile(`\b(fn|struct|impl|enum|trait)\s`)
	reUnsafeTok  = regexp.MustCompile(`\bunsafe\b`)
	reIdentTok   = regexp.MustCompile(`[A-Za-z_][\p{L}\p{N}_:]*`)
	reLEading    = regexp.MustCompile(`^'[\p{L}\p{N}_]+\s*`)
)
var magicStr = func() map[string]bool {
	m := map[string]bool{}
	for _, v := range []string{"0", "1", "2", "-1", "10", "100", "1000", "8", "16",
		"32", "64", "128", "256", "512", "1024", "255", "65535", "4096", "24",
		"60", "365", "7", "12", "3", "4", "6", "0x0", "0x1", "0xff", "0xFF",
		"0.0", "1.0", ""} {
		m[v] = true
	}
	return m
}()

func setOf(parts ...string) map[string]bool {
	m := map[string]bool{}
	for _, s := range parts {
		for w := range strings.FieldsSeq(s) {
			m[w] = true
		}
	}
	return m
}

type symOut struct {
	file, module, parent int32
	name, qual, kind     string
	sig, ret, vis        string
	implType, typeName   string
	lineS, lineE, nLines int32
	byteLo, byteHi       int32
	qualBy               bool
	m                    []uint16
	mw                   []int32
}
type callSite struct {
	name    string
	line    int32
	dynamic bool
}
type litSite struct {
	kind  string
	value string
	line  int32
	magic bool
}
type bodyStats struct {
	counts       []int32
	cyclomatic   int32
	cognitive    int32
	maxNesting   int32
	maxLoopDepth int32
	nTokens      int32
	nOperators   int32
	nOperands    int32
	ops          map[string]bool
	operands     map[string]bool
	calls        []callSite
	lits         []litSite
	secrets      [][2]any
	unsafeBlocks []tsNode
	awaits       []tsNode
	invocations  []tsNode
}
type fileResult struct {
	idx          int
	rel          string
	err          bool
	nErr         int32
	nMissing     int32
	syms         []symOut
	params       []ParamRow
	fields       []FieldRow
	enums        []EnumRow
	imports      []ImportRow
	markers      []MarkerRow
	attrs        []AttrRow
	lits         []LitRow
	hazards      []HazardRow
	traits       []TraitRow
	impls        []ImplRow
	unsafes      []UnsafeRow
	derives      []DeriveRow
	lifes        []LifeRow
	bounds       []BoundRow
	macros       []MacroRow
	secrets      []SecretRow
	cfgs         []CfgRow
	asyncs       []AsyncRow
	pendSid      []int32
	pendLine     []int32
	pendName     []string
	pendType     []string
	recs         []tsRec
	nMarkerLines int32
	ar           []byte
	arIdx        map[string]cgStr
}

func (r *fileResult) put(s string) cgStr {
	if s == "" {
		return cgStr{}
	}
	if v, ok := r.arIdx[s]; ok {
		return v
	}
	off := uint64(len(r.ar))
	r.ar = append(r.ar, s...)
	v := cgStr{off, uint64(len(s))}
	if r.arIdx == nil {
		r.arIdx = make(map[string]cgStr, 256)
	}
	r.arIdx[s] = v
	return v
}

func cgStageRows[T any](dst *[]T, src []T, ar []byte, offs []uintptr) {
	for i := range src {
		r := src[i]
		for _, o := range offs {
			p := (*cgStr)(unsafe.Pointer(uintptr(unsafe.Pointer(&r)) + o))
			if p.Ln == 0 {
				continue
			}
			*p = cgPut(unsafe.String(&ar[p.Off], int(p.Ln)))
		}
		*dst = append(*dst, r)
	}
}

func (r *fileResult) reset(idx int, rel string) {
	r.idx, r.rel = idx, rel
	r.err = false
	r.nErr, r.nMissing, r.nMarkerLines = 0, 0, 0
	r.syms = r.syms[:0]
	r.params = r.params[:0]
	r.fields = r.fields[:0]
	r.enums = r.enums[:0]
	r.imports = r.imports[:0]
	r.markers = r.markers[:0]
	r.attrs = r.attrs[:0]
	r.lits = r.lits[:0]
	r.hazards = r.hazards[:0]
	r.traits = r.traits[:0]
	r.impls = r.impls[:0]
	r.unsafes = r.unsafes[:0]
	r.derives = r.derives[:0]
	r.lifes = r.lifes[:0]
	r.bounds = r.bounds[:0]
	r.macros = r.macros[:0]
	r.secrets = r.secrets[:0]
	r.cfgs = r.cfgs[:0]
	r.asyncs = r.asyncs[:0]
	r.pendSid = r.pendSid[:0]
	r.pendLine = r.pendLine[:0]
	r.pendName = r.pendName[:0]
	r.pendType = r.pendType[:0]
	r.recs = nil
	r.ar = r.ar[:0]
	clear(r.arIdx)
}
func (r *fileResult) newSym() int32 {
	r.syms = append(r.syms, symOut{m: make([]uint16, metricNarrow), mw: make([]int32, metricWide)})
	return int32(len(r.syms))
}

type fileParser struct {
	p         *tsParser
	tree      *tsTree
	src       []byte
	stats     bodyStats
	haz       map[string][2]string
	hasHaz    map[string]bool
	internMap map[string]string
	implLike  map[int32]bool
	traitIDs  map[int32]bool
}

func newFileParser() *fileParser {
	fp := &fileParser{
		p:         tsParserNew(),
		haz:       map[string][2]string{},
		hasHaz:    map[string]bool{},
		internMap: map[string]string{},
		implLike:  map[int32]bool{},
		traitIDs:  map[int32]bool{},
	}
	fp.stats.counts = make([]int32, metricCount+1)
	fp.stats.ops = map[string]bool{}
	fp.stats.operands = map[string]bool{}
	return fp
}
func (fp *fileParser) close() { fp.p.free() }
func (fp *fileParser) text(n tsNode) string {
	return string(fp.src[nStartByte(n):nEndByte(n)])
}
func (fp *fileParser) internStr(s string) string {
	if v, ok := fp.internMap[s]; ok {
		return v
	}
	fp.internMap[s] = s
	return s
}
func cgSplitLines(s string, fn func(line string)) {
	if s == "" {
		return
	}
	start := 0
	i := 0
	for i < len(s) {
		c := s[i]
		if c < utf8.RuneSelf {
			w := 1
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
				i += w
				start = i
				continue
			}
			i += w
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
func cgStrip(s string) string { return strings.TrimFunc(s, isPySpace) }
func isPySpace(r rune) bool {
	if unicode.IsSpace(r) {
		return true
	}
	return r >= 0x1c && r <= 0x1f
}
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
	if decpt <= -4 || decpt > 16 {
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
	} else if decpt <= 0 {
		b.WriteString("0.")
		for i := 0; i < -decpt; i++ {
			b.WriteByte('0')
		}
		b.WriteString(digits)
	} else if decpt >= len(digits) {
		b.WriteString(digits)
		for i := 0; i < decpt-len(digits); i++ {
			b.WriteByte('0')
		}
		b.WriteString(".0")
	} else {
		b.WriteString(digits[:decpt])
		b.WriteByte('.')
		b.WriteString(digits[decpt:])
	}
	return b.String()
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
func cgWordRune(r rune) bool {
	return r == '_' || unicode.IsLetter(r) || unicode.IsNumber(r)
}
func cgBoundaryBefore(s string, i int) bool {
	if i == 0 {
		return true
	}
	r, _ := utf8.DecodeLastRuneInString(s[:i])
	return r == utf8.RuneError || r < utf8.RuneSelf || !cgWordRune(r)
}
func cgBoundaryAfter(s string, i int) bool {
	if i >= len(s) {
		return true
	}
	r, _ := utf8.DecodeRuneInString(s[i:])
	return r == utf8.RuneError || r < utf8.RuneSelf || !cgWordRune(r)
}
func cgFindAll(re *regexp.Regexp, s string) [][]int {
	var out [][]int
	for pos := 0; pos <= len(s); {
		loc := re.FindStringIndex(s[pos:])
		if loc == nil {
			break
		}
		a, b := pos+loc[0], pos+loc[1]
		if cgBoundaryBefore(s, a) && cgBoundaryAfter(s, b) {
			out = append(out, []int{a, b})
		}
		if b == a {
			pos = a + 1
		} else {
			pos = b
		}
	}
	return out
}
func cgMatch(re *regexp.Regexp, s string) bool { return len(cgFindAll(re, s)) > 0 }
func cgCount(re *regexp.Regexp, s string) int  { return len(cgFindAll(re, s)) }
func cgSubmatch1(re *regexp.Regexp, s string) []string {
	for pos := 0; pos <= len(s); {
		loc := re.FindStringSubmatchIndex(s[pos:])
		if loc == nil {
			return nil
		}
		a, b := pos+loc[0], pos+loc[1]
		if cgBoundaryBefore(s, a) && cgBoundaryAfter(s, b) {
			out := []string{s[a:b]}
			if len(loc) >= 4 && loc[2] >= 0 {
				out = append(out, s[pos+loc[2]:pos+loc[3]])
			}
			return out
		}
		if b == a {
			pos = a + 1
		} else {
			pos = b
		}
	}
	return nil
}
func lowerASCII(r rune) rune {
	if r >= 'A' && r <= 'Z' {
		return r + 32
	}
	return r
}
func likeSubstr(s, pat string) bool {
	return likeMatch("%"+pat+"%", s)
}

var g0 *Graph

type rowRec struct {
	id int32
	x  int32
	c  []cell
	s  string
}
type tri struct{ root, sym, hops int32 }

func sortRows(rs []rowRec, less func(a, b *rowRec) bool) {
	sort.SliceStable(rs, func(i, j int) bool { return less(&rs[i], &rs[j]) })
}
func fill(r *result, rs []rowRec) {
	r.rows = make([][]cell, len(rs))
	for i := range rs {
		r.rows[i] = rs[i].c
	}
}
func (q *qctx) at(sid int32) string       { return q.g.At[sid-1] }
func (q *qctx) name(sid int32) string     { return q.g.SymName[sid-1].Str() }
func (q *qctx) impl(sid int32) string     { return q.g.SymImpl[sid-1].Str() }
func (q *qctx) mv(sid int32, c int) int32 { return q.g.Mv(sid, int32(c)) }
func (q *qctx) max1(v int32) int32 {
	if v < 1 {
		return 1
	}
	return v
}
func abs32(v int64) int64 {
	if v < 0 {
		return -v
	}
	return v
}
func (q *qctx) isKind(sid int32, kinds ...string) bool {
	k := q.g.SymKind[sid-1].Str()
	return slices.Contains(kinds, k)
}
func setMax(dst *int32, v int32) {
	if v > *dst {
		*dst = v
	}
}
func (q *qctx) simple(cols []string, gate func(sid int32) bool,
	row func(sid int32) []cell, order func(a, b *rowRec) bool) *result {
	r := &result{cols: cols}
	var rs []rowRec
	for sid := int32(1); sid <= int32(q.g.N()); sid++ {
		if !gate(sid) || !q.modOK(sid) {
			continue
		}
		rs = append(rs, rowRec{id: sid, c: row(sid)})
	}
	sortRows(rs, order)
	fill(r, rs)
	return r
}
func (q *qctx) reachPairs(depth int32, rootFn func(sid int32) bool,
	keep func(root, sym, hops int32) bool) []tri {
	return q.reach(depth, false, rootFn, keep)
}
func (q *qctx) reachPairsSelf(depth int32, rootFn func(sid int32) bool,
	keep func(root, sym, hops int32) bool) []tri {
	return q.reach(depth, true, rootFn, keep)
}
func (q *qctx) reach(depth int32, self bool, rootFn func(sid int32) bool,
	keep func(root, sym, hops int32) bool) []tri {
	g := q.g
	w := newReachWalk(g)
	w.includeSelf = self
	type key struct{ a, b int32 }
	dist := map[key]int32{}
	var keys []key
	for sid := int32(1); sid <= int32(g.N()); sid++ {
		if !rootFn(sid) {
			continue
		}
		w.each(sid, depth, func(s, d int32) {
			if !keep(sid, s, d) {
				return
			}
			k := key{sid, s}
			if old, ok := dist[k]; !ok || d < old {
				if !ok {
					keys = append(keys, k)
				}
				dist[k] = d
			}
		})
	}
	sort.SliceStable(keys, func(i, j int) bool {
		if keys[i].b != keys[j].b {
			return keys[i].b < keys[j].b
		}
		return keys[i].a < keys[j].a
	})
	out := make([]tri, len(keys))
	for i, k := range keys {
		out[i] = tri{k.a, k.b, dist[k]}
	}
	return out
}
func (q *qctx) fromReach(cols []string, ts []tri,
	row func(t tri) []cell, order func(a, b *rowRec) bool) *result {
	r := &result{cols: cols}
	rs := make([]rowRec, len(ts))
	for i, t := range ts {
		rs[i] = rowRec{id: t.sym, x: t.root, c: row(t)}
	}
	sortRows(rs, order)
	fill(r, rs)
	return r
}

type modGroup struct {
	id    int32
	cols  []int32
	nSyms int32
}

func (q *qctx) modGroups(cols []int, kinds []string, skipTest, skipGen bool) []*modGroup {
	g := q.g
	byMod := map[int32]*modGroup{}
	var order []int32
	for sid := int32(1); sid <= int32(g.N()); sid++ {
		if len(kinds) > 0 && !q.isKind(sid, kinds...) {
			continue
		}
		if skipTest && sFileTest[sid] {
			continue
		}
		if skipGen && sFileGen[sid] {
			continue
		}
		m := g.SymModule[sid-1]
		if m < 0 {
			continue
		}
		p, ok := byMod[m]
		if !ok {
			p = &modGroup{id: m, cols: make([]int32, len(cols))}
			byMod[m] = p
			order = append(order, m)
		}
		for i, c := range cols {
			p.cols[i] += q.mv(sid, c)
		}
		p.nSyms++
	}
	var out []*modGroup
	for _, m := range order {
		if !likeMatch(q.mod, g.Modules[m-1].Name()) {
			continue
		}
		out = append(out, byMod[m])
	}
	return out
}
func (g *Graph) modName(id int32) string {
	if id >= 1 && int(id) <= len(g.Modules) {
		return g.Modules[id-1].Name()
	}
	return ""
}
func fileModName(fid int32) string {
	g := g0
	if fid < 1 || int(fid) > len(g.Files) {
		return ""
	}
	return g.modName(g.Files[fid-1].ModuleID)
}

type cellKind uint8

const (
	kInt cellKind = iota
	kFloat
	kStr
	kNull
)

type cell struct {
	k cellKind
	i int64
	f float64
	s string
}

func ci(v int64) cell   { return cell{k: kInt, i: v} }
func ci32(v int32) cell { return cell{k: kInt, i: int64(v)} }
func cf(v float64) cell { return cell{k: kFloat, f: v} }
func cs(v string) cell  { return cell{k: kStr, s: v} }
func cnull() cell       { return cell{k: kNull} }

type result struct {
	cols []string
	rows [][]cell
}

func (r *result) add(vs ...cell) { r.rows = append(r.rows, vs) }

type query struct {
	name, title, notes string
	run                func(g *Graph, mod string, lim int) *result
}

func runQuery(g *Graph, q query, mod string, lim int) *result {
	r := q.run(g, mod, lim)
	if lim >= 0 && len(r.rows) > lim {
		r.rows = r.rows[:lim]
	}
	return r
}

type qctx struct {
	g   *Graph
	mod string
}

func (q *qctx) modOK(sid int32) bool { return likeMatch(q.mod, q.g.ModName[sid-1]) }
func groupConcatDistinct(vals []string) string {
	seen := map[string]bool{}
	out := vals[:0:0]
	for _, v := range vals {
		if v == "" || seen[v] {
			continue
		}
		seen[v] = true
		out = append(out, v)
	}
	return joinComma(out)
}
func groupConcatNull(vals []string) cell {
	if len(vals) == 0 {
		return cnull()
	}
	return cs(groupConcatDistinct(vals))
}
func groupConcatSorted(vals []string) string {
	seen := map[string]bool{}
	out := make([]string, 0, len(vals))
	for _, v := range vals {
		if v == "" || seen[v] {
			continue
		}
		seen[v] = true
		out = append(out, v)
	}
	sort.Strings(out)
	return joinComma(out)
}
func groupConcatSortedOrNull(vals []string) cell {
	if len(vals) == 0 {
		return cnull()
	}
	return cs(groupConcatSorted(vals))
}
func sqliteCastInt(f float64) int32 { return int32(f) }
func castOverNull(num, den int32) cell {
	if den == 0 {
		return cnull()
	}
	return ci32(sqliteCastInt(1000.0 * float64(num) / float64(den)))
}
func castPctOverNull(num, den int32) cell {
	if den == 0 {
		return cnull()
	}
	return ci32(sqliteCastInt(100.0 * float64(num) / float64(den)))
}
func joinComma(v []string) string {
	var out strings.Builder
	for i, s := range v {
		if i > 0 {
			out.WriteString(",")
		}
		out.WriteString(s)
	}
	return out.String()
}

type reachWalk struct {
	g           *Graph
	dist        []int32
	seen        []int32
	gen         int32
	vis         []int32
	best        []int32
	queue       []int32
	maxd        []int32
	nCallees    []int32
	seenSym     map[int32]bool
	reportRoot  bool
	includeSelf bool
	pairSeen    map[int64]struct{}
}

func newReachWalk(g *Graph) *reachWalk {
	n := int32(len(g.SymName))
	return &reachWalk{g: g, dist: make([]int32, n+1), seen: make([]int32, n+1),
		vis: make([]int32, n+1), best: make([]int32, n+1),
		maxd: make([]int32, n+1), nCallees: make([]int32, n+1),
		seenSym: map[int32]bool{}}
}
func (w *reachWalk) each(root int32, maxDepth int32, fn func(sym, depth int32)) {
	w.gen++
	gen := w.gen
	dist := w.dist
	seen := w.seen
	seen[root] = gen
	dist[root] = 0
	queue := w.queue[:0]
	queue = append(queue, root)
	for i := 0; i < len(queue); i++ {
		sym := queue[i]
		d := dist[sym]
		if sym != root || w.includeSelf {
			fn(sym, d)
		}
		if d >= maxDepth {
			continue
		}
		for _, c := range sOut[sym] {
			if c == root && w.reportRoot {
				fn(root, d+1)
				continue
			}
			if seen[c] == gen {
				continue
			}
			seen[c] = gen
			dist[c] = d + 1
			queue = append(queue, c)
		}
	}
	w.queue = queue
}
func (w *reachWalk) recordBest(sym, depth int32) {
	if v := depth + 1; w.best[sym] == 0 || v < w.best[sym] {
		w.best[sym] = v
	}
}
func (w *reachWalk) minBest(sym int32) int32 {
	if w.best[sym] == 0 {
		return -1
	}
	return w.best[sym] - 1
}
func (w *reachWalk) pairStats(root int32, maxDepth int32) (int32, int32) {
	if w.pairSeen == nil {
		w.pairSeen = map[int64]struct{}{}
	}
	clear(w.pairSeen)
	seenSym := map[int32]bool{}
	cur := []int32{root}
	w.pairSeen[int64(root)<<32] = struct{}{}
	seenSym[root] = true
	maxD, n := int32(0), int32(1)
	for d := int32(0); d < maxDepth && len(cur) > 0; d++ {
		var next []int32
		for _, sym := range cur {
			for _, c := range sOut[sym] {
				key := int64(c)<<32 | int64(d+1)
				if _, ok := w.pairSeen[key]; ok {
					continue
				}
				w.pairSeen[key] = struct{}{}
				if !seenSym[c] {
					seenSym[c] = true
					n++
				}
				next = append(next, c)
			}
		}
		if len(next) > 0 {
			maxD = d + 1
		}
		cur = next
	}
	return maxD, n
}

const maxCell = 72

func (c cell) str() string {
	switch c.k {
	case kNull:
		return "-"
	case kFloat:
		return fmt.Sprintf("%.2f", c.f)
	case kInt:
		return strconv.FormatInt(c.i, 10)
	default:
		return c.s
	}
}
func render(w io.Writer, r *result) {
	if len(r.rows) == 0 {
		fmt.Fprintln(w, " (no rows)")
		return
	}
	body := make([][]string, len(r.rows))
	for i, row := range r.rows {
		body[i] = make([]string, len(row))
		for j, c := range row {
			t := c.str()
			if n := utf8.RuneCountInString(t); n > maxCell {
				t = clip(t, maxCell-3) + "..."
			}
			body[i][j] = t
		}
	}
	widths := make([]int, len(r.cols))
	for j, name := range r.cols {
		w := utf8.RuneCountInString(name)
		for _, row := range body {
			if n := utf8.RuneCountInString(row[j]); n > w {
				w = n
			}
		}
		widths[j] = w
	}
	pad := func(s string, w int) string {
		n := w - utf8.RuneCountInString(s)
		if n <= 0 {
			return s
		}
		return s + strings.Repeat(" ", n)
	}
	fmt.Fprintln(w, " "+joinCols(r.cols, widths, pad))
	dashes := make([]string, len(widths))
	for i, wd := range widths {
		dashes[i] = strings.Repeat("-", wd)
	}
	fmt.Fprintln(w, " "+strings.Join(dashes, " "))
	for _, row := range body {
		padded := make([]string, len(row))
		for j, c := range row {
			padded[j] = pad(c, widths[j])
		}
		fmt.Fprintln(w, " "+strings.Join(padded, " "))
	}
}
func joinCols(cols []string, widths []int, pad func(string, int) string) string {
	out := make([]string, len(cols))
	for i, c := range cols {
		out[i] = pad(c, widths[i])
	}
	return strings.Join(out, " ")
}
func writeCSV(w io.Writer, r *result) {
	bw := bufio.NewWriter(w)
	defer bw.Flush()
	bw.WriteString(csvRow(toStrings(r.cols)))
	for _, row := range r.rows {
		bw.WriteString(csvRow(cellStrings(row)))
	}
}
func toStrings(v []string) []string { return v }
func cellStrings(row []cell) []string {
	out := make([]string, len(row))
	for i, c := range row {
		switch c.k {
		case kNull:
			out[i] = ""
		case kFloat:
			out[i] = cgReprFloat(c.f)
		case kInt:
			out[i] = strconv.FormatInt(c.i, 10)
		default:
			out[i] = c.s
		}
	}
	return out
}
func csvRow(cells []string) string {
	var b strings.Builder
	for i, c := range cells {
		if i > 0 {
			b.WriteByte(',')
		}
		b.WriteString(csvField(c))
	}
	b.WriteString("\r\n")
	return b.String()
}
func csvField(s string) string {
	if !strings.ContainsAny(s, ",\"\r\n") {
		return s
	}
	return "\"" + strings.ReplaceAll(s, "\"", "\"\"") + "\""
}
func writeJSON(w io.Writer, r *result) {
	bw := bufio.NewWriter(w)
	defer bw.Flush()
	if len(r.rows) == 0 {
		bw.WriteString("[]\n")
		return
	}
	bw.WriteString("[\n")
	for i, row := range r.rows {
		if i > 0 {
			bw.WriteString(",\n")
		}
		bw.WriteString("  {\n")
		for j, c := range row {
			if j > 0 {
				bw.WriteString(",\n")
			}
			bw.WriteString("    " + jsonStr(r.cols[j]) + ": " + jsonVal(c))
		}
		bw.WriteString("\n  }")
	}
	if len(r.rows) > 0 {
		bw.WriteString("\n")
	}
	bw.WriteString("]\n")
}
func jsonVal(c cell) string {
	switch c.k {
	case kNull:
		return "null"
	case kInt:
		return strconv.FormatInt(c.i, 10)
	case kFloat:
		if math.IsInf(c.f, 0) || math.IsNaN(c.f) {
			return `"` + cgReprFloat(c.f) + `"`
		}
		return cgReprFloat(c.f)
	default:
		return jsonStr(c.s)
	}
}
func jsonStr(s string) string {
	var b strings.Builder
	b.WriteByte('"')
	for _, r := range s {
		switch r {
		case '"':
			b.WriteString(`\"`)
		case '\\':
			b.WriteString(`\\`)
		case '\n':
			b.WriteString(`\n`)
		case '\r':
			b.WriteString(`\r`)
		case '\t':
			b.WriteString(`\t`)
		case '\b':
			b.WriteString(`\b`)
		case '\f':
			b.WriteString(`\f`)
		default:
			switch {
			case r < 0x20:
				b.WriteString(fmt.Sprintf(`\u%04x`, r))
			case r < 0x7f:
				b.WriteRune(r)
			case r <= 0xffff:
				b.WriteString(fmt.Sprintf(`\u%04x`, r))
			default:
				r -= 0x10000
				hi := 0xd800 + (r >> 10)
				lo := 0xdc00 + (r & 0x3ff)
				b.WriteString(fmt.Sprintf(`\u%04x\u%04x`, hi, lo))
			}
		}
	}
	b.WriteByte('"')
	return b.String()
}

var _ = os.Stdout

func report(w io.Writer, g *Graph) {
	meta := map[string]string{}
	for _, m := range g.Meta {
		meta[m.Key()] = m.Value()
	}
	line := func(k, v string) { fmt.Fprintf(w, " %-14s %s\n", k, v) }
	fmt.Fprintf(w, "\n%s\n", rep(78, '='))
	fmt.Fprintf(w, "OVERVIEW\n%s\n", rep(78, '-'))
	for _, k := range []string{"lang", "target", "parser", "root", "built_at"} {
		if v := meta[k]; v != "" {
			line(k, v)
		}
	}
	files := int32(len(g.Files))
	parsed, sloc := int32(0), int32(0)
	for i := range g.Files {
		if g.Files[i].Parsed == 1 {
			parsed++
			sloc += g.Files[i].Sloc
		}
	}
	line("files", fmt.Sprintf("%d catalogued, %d parsed, %d sloc", files, parsed, sloc))
	kinds := map[string]int32{}
	for i := range g.SymName {
		kinds[g.SymKind[i].Str()]++
	}
	type kv struct {
		k string
		v int32
	}
	var ks []kv
	for k, v := range kinds {
		ks = append(ks, kv{k, v})
	}
	sort.Slice(ks, func(i, j int) bool {
		if ks[i].v != ks[j].v {
			return ks[i].v > ks[j].v
		}
		return ks[i].k < ks[j].k
	})
	if len(ks) > 12 {
		ks = ks[:12]
	}
	var parts strings.Builder
	for i, e := range ks {
		if i > 0 {
			parts.WriteString(", ")
		}
		parts.WriteString(e.k + "=" + itoa(int(e.v)))
	}
	line("symbols", parts.String())
	var unres int32
	for i := range g.Unresolved {
		unres += int32(g.Unresolved[i].N)
	}
	line("call graph", fmt.Sprintf("%d edges, %d call sites, %d unresolved",
		len(g.Edges), len(g.Callsites), unres))
	fmt.Fprintf(w, "\n%s\n", rep(78, '='))
	fmt.Fprintf(w, "HOW MUCH OF THIS TO TRUST\n%s\n", rep(78, '-'))
	var errFiles, totCalls int32
	for i := range g.Files {
		if g.Files[i].NParseErrors > 0 {
			errFiles++
		}
	}
	for i := range g.SymName {
		totCalls += g.mCol(i, cNCalls)
	}
	if parsed == 0 {
		fmt.Fprintf(w, " NOTHING WAS PARSED. Every number below is zero because no file\n")
		fmt.Fprintf(w, " was read, not because this repository is empty or clean.\n")
	}
	fmt.Fprintf(w, " %-30s %d file(s)\n", "files with parse errors", errFiles)
	if totCalls != 0 {
		fmt.Fprintf(w, " %-30s %d of %d call sites (%d%%)\n",
			"calls we could NOT resolve", unres, totCalls, 100*unres/totCalls)
	} else {
		fmt.Fprintf(w, " %-30s no calls were recorded at all -- this is the absence of\n", "call resolution")
		fmt.Fprintf(w, " %-30s data, not a clean result\n", "")
	}
	fmt.Fprintf(w, " A high unresolved share means the call-graph queries below see less\n")
	fmt.Fprintf(w, " than they imply. `v_blindspot` lists exactly where.\n")
	q := &qctx{g: g, mod: "%"}
	mods := make([]int, 0, len(g.Modules))
	for i := range g.Modules {
		if g.Modules[i].NFiles > 0 {
			mods = append(mods, i)
		}
	}
	sort.Slice(mods, func(i, j int) bool {
		return g.Modules[mods[i]].Sloc > g.Modules[mods[j]].Sloc
	})
	if len(mods) > 12 {
		mods = mods[:12]
	}
	r1 := &result{cols: []string{"name", "files", "sloc", "syms", "instab"}}
	for _, i := range mods {
		m := &g.Modules[i]
		r1.add(cs(m.Name()), ci32(m.NFiles), ci32(m.Sloc), ci32(m.NSymbols),
			cf(m.Instability))
	}
	type symRow struct {
		sid int32
		v   int32
	}
	var byCyc, byFan []symRow
	for i := range g.SymName {
		sid := int32(i + 1)
		if !isFnKind(g.SymKind[i].Str()) {
			continue
		}
		byCyc = append(byCyc, symRow{sid, g.mCol(i, cCyclomatic)})
		byFan = append(byFan, symRow{sid, g.mCol(i, cFanIn)})
	}
	sort.SliceStable(byCyc, func(i, j int) bool { return byCyc[i].v > byCyc[j].v })
	sort.SliceStable(byFan, func(i, j int) bool { return byFan[i].v > byFan[j].v })
	if len(byCyc) > 12 {
		byCyc = byCyc[:12]
	}
	if len(byFan) > 12 {
		byFan = byFan[:12]
	}
	r2 := &result{cols: []string{"name", "sloc", "cyclo", "cog", "nest", "fan_in", "at"}}
	for _, e := range byCyc {
		sid := e.sid
		r2.add(cs(g.SymName[sid-1].Str()), ci32(q.mv(sid, cSloc)), ci32(q.mv(sid, cCyclomatic)),
			ci32(q.mv(sid, cCognitive)), ci32(q.mv(sid, cMaxNesting)), ci32(q.mv(sid, cFanIn)),
			cs(g.At[sid-1]))
	}
	r3 := &result{cols: []string{"name", "fan_in", "fan_out", "cyclo", "sloc", "at"}}
	for _, e := range byFan {
		sid := e.sid
		r3.add(cs(g.SymName[sid-1].Str()), ci32(q.mv(sid, cFanIn)), ci32(q.mv(sid, cFanOut)),
			ci32(q.mv(sid, cCyclomatic)), ci32(q.mv(sid, cSloc)), cs(g.At[sid-1]))
	}
	mk := map[string]int32{}
	for i := range g.Markers {
		mk[g.Markers[i].Kind()]++
	}
	var mks []kv
	for k, v := range mk {
		mks = append(mks, kv{k, v})
	}
	sort.Slice(mks, func(i, j int) bool {
		if mks[i].v != mks[j].v {
			return mks[i].v > mks[j].v
		}
		return mks[i].k < mks[j].k
	})
	r4 := &result{cols: []string{"kind", "n"}}
	for _, e := range mks {
		r4.add(cs(e.k), ci32(e.v))
	}
	for _, s := range []struct {
		label string
		r     *result
	}{
		{"BIGGEST MODULES", r1},
		{"HEAVIEST FUNCTIONS", r2},
		{"MOST DEPENDED ON", r3},
		{"MARKERS LEFT IN THE CODE", r4},
	} {
		fmt.Fprintf(w, "\n%s\n", rep(78, '='))
		fmt.Fprintf(w, "%s\n%s\n", s.label, rep(78, '-'))
		render(w, s.r)
	}
}
func rep(n int, c byte) string {
	b := make([]byte, n)
	for i := range b {
		b[i] = c
	}
	return string(b)
}

type byNameEntry struct {
	sid      int32
	file     int32
	module   int32
	typeName string
}

func mergeResult(g *Graph, res *fileResult) {
	base := int32(len(g.SymName))
	for i := range res.syms {
		s := &res.syms[i]
		sid := base + int32(i) + 1
		g.SymFile = append(g.SymFile, s.file)
		g.SymModule = append(g.SymModule, s.module)
		if s.parent > 0 {
			g.SymParent = append(g.SymParent, base+s.parent)
		} else {
			g.SymParent = append(g.SymParent, -1)
		}
		g.SymName = append(g.SymName, cgPut(s.name))
		g.SymQual = append(g.SymQual, cgPut(s.qual))
		g.SymKind = append(g.SymKind, cgPut(s.kind))
		g.SymLine = append(g.SymLine, s.lineS)
		g.SymLineEnd = append(g.SymLineEnd, s.lineE)
		g.SymNLines = append(g.SymNLines, s.nLines)
		g.SymByteLo = append(g.SymByteLo, s.byteLo)
		g.SymByteHi = append(g.SymByteHi, s.byteHi)
		g.SymSig = append(g.SymSig, cgPut(s.sig))
		g.SymRet = append(g.SymRet, cgPut(s.ret))
		g.SymVis = append(g.SymVis, cgPut(s.vis))
		g.SymImpl = append(g.SymImpl, cgPut(s.implType))
		for len(g.M) == 0 || cap(g.M[len(g.M)-1])-len(g.M[len(g.M)-1]) < metricNarrow {
			g.M = append(g.M, make([]uint16, 0, mBlockSyms*metricNarrow))
		}
		last := len(g.M) - 1
		g.M[last] = append(g.M[last], s.m...)
		for len(g.MW) == 0 || cap(g.MW[len(g.MW)-1])-len(g.MW[len(g.MW)-1]) < metricWide {
			g.MW = append(g.MW, make([]int32, 0, mBlockSyms*metricWide))
		}
		g.MW[len(g.MW)-1] = append(g.MW[len(g.MW)-1], s.mw...)
		if s.qualBy {
			g.byQual[res.rel+":"+s.qual] = sid
		}
		g.byQual[s.qual] = sid
		g.symType = append(g.symType, s.typeName)
		if s.name != "<module>" {
			e := byNameEntry{sid, s.file, s.module, s.typeName}
			if g.byName == nil {
				g.byName = map[string][]byNameEntry{}
			}
			g.byName[s.name] = append(g.byName[s.name], e)
		}
	}
	shift := func(v *int32) { *v += base }
	for i := range res.params {
		shift(&res.params[i].SymID)
	}
	cgStageRows(&g.Params, res.params, res.ar, paramStrOffs)
	for i := range res.fields {
		shift(&res.fields[i].SymID)
	}
	cgStageRows(&g.Fields, res.fields, res.ar, fieldStrOffs)
	for i := range res.enums {
		shift(&res.enums[i].SymID)
	}
	cgStageRows(&g.EnumMembers, res.enums, res.ar, enumStrOffs)
	for i := range res.imports {
		res.imports[i].ID = int32(len(g.Imports) + 1 + i)
	}
	cgStageRows(&g.Imports, res.imports, res.ar, importStrOffs)
	for i := range res.markers {
		res.markers[i].ID = int32(len(g.Markers) + 1 + i)
	}
	cgStageRows(&g.Markers, res.markers, res.ar, markStrOffs)
	for i := range res.attrs {
		res.attrs[i].ID = int32(len(g.Attributes) + 1 + i)
		if res.attrs[i].SymID > 0 {
			shift(&res.attrs[i].SymID)
		}
	}
	cgStageRows(&g.Attributes, res.attrs, res.ar, attrStrOffs)
	for i := range res.lits {
		res.lits[i].ID = int32(len(g.Literals) + 1 + i)
		if res.lits[i].SymID > 0 {
			shift(&res.lits[i].SymID)
		}
	}
	cgStageRows(&g.Literals, res.lits, res.ar, litStrOffs)
	type hazKey struct {
		sid int32
		pat cgStr
	}
	seenHaz := map[hazKey]int32{}
	for i := range res.hazards {
		h := &res.hazards[i]
		h.SymID += base
		if h.pattern.Ln != 0 {
			h.pattern = cgPut(unsafe.String(&res.ar[h.pattern.Off], int(h.pattern.Ln)))
		}
		if h.category.Ln != 0 {
			h.category = cgPut(unsafe.String(&res.ar[h.category.Off], int(h.category.Ln)))
		}
		k := hazKey{h.SymID, h.pattern}
		if at, ok := seenHaz[k]; ok {
			g.Hazards[at].N += h.N
			continue
		}
		seenHaz[k] = int32(len(g.Hazards))
		g.Hazards = append(g.Hazards, *h)
	}
	for i := range res.traits {
		shift(&res.traits[i].SymID)
	}
	cgStageRows(&g.Traits, res.traits, res.ar, traitStrOffs)
	for i := range res.impls {
		res.impls[i].ID = int32(len(g.Impls) + 1 + i)
		shift(&res.impls[i].SymID)
	}
	cgStageRows(&g.Impls, res.impls, res.ar, implStrOffs)
	for i := range res.unsafes {
		res.unsafes[i].ID = int32(len(g.UnsafeBlks) + 1 + i)
		shift(&res.unsafes[i].SymID)
	}
	cgStageRows(&g.UnsafeBlks, res.unsafes, res.ar, nil)
	for i := range res.derives {
		res.derives[i].ID = int32(len(g.Derives) + 1 + i)
		shift(&res.derives[i].SymID)
	}
	cgStageRows(&g.Derives, res.derives, res.ar, deriveStrOffs)
	for i := range res.lifes {
		res.lifes[i].ID = int32(len(g.Lifetimes) + 1 + i)
		shift(&res.lifes[i].SymID)
	}
	cgStageRows(&g.Lifetimes, res.lifes, res.ar, lifeStrOffs)
	for i := range res.bounds {
		res.bounds[i].ID = int32(len(g.GenBounds) + 1 + i)
		shift(&res.bounds[i].SymID)
	}
	cgStageRows(&g.GenBounds, res.bounds, res.ar, boundStrOffs)
	for i := range res.macros {
		res.macros[i].ID = int32(len(g.Macros) + 1 + i)
		shift(&res.macros[i].SymID)
	}
	cgStageRows(&g.Macros, res.macros, res.ar, macroStrOffs)
	for i := range res.secrets {
		res.secrets[i].ID = int32(len(g.Secrets) + 1 + i)
		shift(&res.secrets[i].SymID)
	}
	cgStageRows(&g.Secrets, res.secrets, res.ar, secretStrOffs)
	for i := range res.cfgs {
		res.cfgs[i].ID = int32(len(g.CfgBlocks) + 1 + i)
		if res.cfgs[i].SymID > 0 {
			shift(&res.cfgs[i].SymID)
		}
	}
	cgStageRows(&g.CfgBlocks, res.cfgs, res.ar, cfgStrOffs)
	for i := range res.asyncs {
		res.asyncs[i].ID = int32(len(g.AsyncPoints) + 1 + i)
		shift(&res.asyncs[i].SymID)
	}
	cgStageRows(&g.AsyncPoints, res.asyncs, res.ar, asyncStrOffs)
	for i := range res.pendSid {
		g.pendSid = append(g.pendSid, base+res.pendSid[i])
		g.pendLine = append(g.pendLine, res.pendLine[i])
		g.pendName = append(g.pendName, res.pendName[i])
		g.pendType = append(g.pendType, res.pendType[i])
	}
}
func hashStr(s string) int32 {
	var h int32 = 2166136261 & 0x7fffffff
	for i := 0; i < len(s); i++ {
		h ^= int32(s[i])
		h *= 16777619
	}
	return h
}

type resolver struct {
	unique     map[string]byNameEntry
	fileScope  map[int64]int32
	typeScope  map[string]int32
	symLoc     []int64
	byNameKeys map[string]bool
	haveLoc    []bool
}

func resolveCalls(g *Graph) {
	r := &resolver{
		unique:     map[string]byNameEntry{},
		fileScope:  map[int64]int32{},
		typeScope:  map[string]int32{},
		byNameKeys: map[string]bool{},
	}
	n := int32(len(g.SymName))
	r.symLoc = make([]int64, n+1)
	r.haveLoc = make([]bool, n+1)
	counts := map[string]int32{}
	for sid := int32(1); sid <= n; sid++ {
		nm := g.SymName[sid-1].Str()
		if nm == "<module>" {
			continue
		}
		counts[nm]++
	}
	first := map[string]byNameEntry{}
	for sid := int32(1); sid <= n; sid++ {
		nm := g.SymName[sid-1].Str()
		if nm == "<module>" {
			continue
		}
		e := byNameEntry{sid, g.SymFile[sid-1], g.SymModule[sid-1], g.symType[sid-1]}
		if !r.haveLoc[sid] {
			r.symLoc[sid] = int64(e.file)<<32 | int64(e.module)
			r.haveLoc[sid] = true
		}
		if _, ok := first[nm]; !ok {
			first[nm] = e
		}
		k := int64(uint32(e.file))<<32 | int64(uint32(hashStr(nm)))
		if _, ok := r.fileScope[k]; !ok {
			r.fileScope[k] = sid
		}
		if e.typeName != "" {
			tk := e.typeName + "\x00" + nm
			if _, ok := r.typeScope[tk]; !ok {
				r.typeScope[tk] = sid
			}
		}
	}
	for nm, c := range counts {
		if c == 1 {
			r.unique[nm] = first[nm]
		}
	}
	edges := map[uint64]*edgeAgg{}
	sites := map[siteKey]struct{}{}
	unres := map[uint64]*unresAgg{}
	extByCaller := map[int32]int32{}
	var nRes, nUnres, nExt int
	for i := range g.pendSid {
		raw := g.pendName[i]
		name := strings.TrimRight(cgStrip(raw), "!")
		if name == "" {
			continue
		}
		base := lastSeg(name)
		caller := g.pendSid[i]
		fid := g.SymFile[caller-1]
		ty := g.pendType[i]
		line := g.pendLine[i]
		target := int32(0)
		if ty != "" {
			target = r.typeScope[ty+"\x00"+base]
		}
		if target == 0 {
			target = g.byQual[name]
		}
		if target == 0 {
			target = r.fileScope[int64(uint32(fid))<<32|int64(uint32(hashStr(base)))]
		}
		if target == 0 {
			if e, ok := r.unique[base]; ok {
				target = e.sid
			}
		}
		if target == 0 {
			if isExternalName(name, base, g.byName) {
				extByCaller[caller]++
				nExt++
			} else {
				k := uint64(caller)<<32 | uint64(uint32(hashStr(clip(name, 160))))
				if a, ok := unres[k]; ok {
					a.n++
				} else {
					unres[k] = &unresAgg{caller, clip(name, 160), 1, line}
				}
				nUnres++
			}
			continue
		}
		loc := r.symLoc[target]
		key := uint64(caller)<<32 | uint64(target)
		a, ok := edges[key]
		if !ok {
			a = &edgeAgg{caller, target, 1,
				boolT(int32(loc>>32) == fid),
				boolT(int32(loc) == g.SymModule[caller-1]),
				boolT(caller == target)}
			edges[key] = a
		} else {
			a.n++
		}
		if line != 0 {
			sites[siteKey{caller, target, line}] = struct{}{}
		}
		nRes++
	}
	for _, a := range edges {
		g.Edges = append(g.Edges, EdgeRow{a.caller, a.callee, a.n, a.sameFile,
			a.sameModule, a.isSelf})
	}
	sort.Slice(g.Edges, func(i, j int) bool {
		if g.Edges[i].Caller != g.Edges[j].Caller {
			return g.Edges[i].Caller < g.Edges[j].Caller
		}
		return g.Edges[i].Callee < g.Edges[j].Callee
	})
	for k := range sites {
		g.Callsites = append(g.Callsites, SiteRow{k.caller, k.target, k.line})
	}
	sort.Slice(g.Callsites, func(i, j int) bool {
		a, b := &g.Callsites[i], &g.Callsites[j]
		if a.Caller != b.Caller {
			return a.Caller < b.Caller
		}
		if a.Callee != b.Callee {
			return a.Callee < b.Callee
		}
		return a.Line < b.Line
	})
	unresOrder := make([]*unresAgg, 0, len(unres))
	for _, a := range unres {
		unresOrder = append(unresOrder, a)
	}
	sort.Slice(unresOrder, func(i, j int) bool {
		if unresOrder[i].caller != unresOrder[j].caller {
			return unresOrder[i].caller < unresOrder[j].caller
		}
		return unresOrder[i].name < unresOrder[j].name
	})
	for _, a := range unresOrder {
		if a.n > 65535 {
			panic(sprintf("unresolved-call count %d for %q exceeds the 16-bit range", a.n, a.name))
		}
		g.Unresolved = append(g.Unresolved, UnresRow{name: cgPut(a.name),
			Caller: a.caller, FirstLine: uint16(a.line), N: uint16(a.n)})
	}
	sort.Slice(g.Unresolved, func(i, j int) bool {
		a, b := &g.Unresolved[i], &g.Unresolved[j]
		if a.Caller != b.Caller {
			return a.Caller < b.Caller
		}
		return a.name.Str() < b.name.Str()
	})
	for sid, v := range extByCaller {
		g.Set(sid, cNExternalCalls, v)
	}
	g.nResolved, g.nExternal, g.nUnresolved = nRes, nExt, nUnres
}

type edgeAgg struct {
	caller, callee               int32
	n                            int32
	sameFile, sameModule, isSelf int32
}
type unresAgg struct {
	caller int32
	name   string
	n      int32
	line   int32
}
type siteKey struct{ caller, target, line int32 }

func isExternalName(name, base string, byName map[string][]byNameEntry) bool {
	flat := strings.ReplaceAll(name, ".", "::")
	head, _, _ := strings.Cut(flat, "::")
	if stdRoots[head] || head == "crate" || head == "Self" {
		return true
	}
	if stdMacros[base] {
		if _, ok := byName[base]; !ok {
			return true
		}
	}
	return prelude[base] || prelude[head]
}

var importSuffixes = []string{"", ".py", ".pyi", ".ts", ".tsx", ".d.ts", ".mts",
	".cts", ".js", ".jsx", ".mjs", ".cjs", ".rb", ".php", ".go", ".rs", ".java"}
var importIndexes = []string{"__init__.py", "index.ts", "index.tsx", "index.js",
	"index.mjs", "mod.rs", "lib.rs"}

func resolveImportTargets(g *Graph) int {
	byPath := map[string]int32{}
	for i := range g.Files {
		norm := g.Files[i].Path()
		if _, ok := byPath[norm]; !ok {
			byPath[norm] = g.Files[i].ID
		}
		stem := norm
		if j := strings.LastIndex(stem, "."); j >= 0 {
			stem = stem[:j]
		}
		if _, ok := byPath[stem]; !ok {
			byPath[stem] = g.Files[i].ID
		}
	}
	look := func(cand string) int32 {
		cand = strings.Trim(cand, "/")
		if cand == "" {
			return 0
		}
		for _, suf := range importSuffixes {
			if h, ok := byPath[cand+suf]; ok {
				return h
			}
		}
		for _, idx := range importIndexes {
			if h, ok := byPath[cand+"/"+idx]; ok {
				return h
			}
		}
		return 0
	}
	pathOf := map[int32]string{}
	for i := range g.Files {
		pathOf[g.Files[i].ID] = g.Files[i].Path()
	}
	n := 0
	for i := range g.Imports {
		im := &g.Imports[i]
		if im.TargetID >= 0 {
			continue
		}
		t := strings.TrimSpace(strings.ReplaceAll(im.Target(), "\\", "/"))
		if t == "" {
			continue
		}
		here := cgDirname(pathOf[im.FileID])
		var hit int32
		if strings.HasPrefix(t, ".") {
			nUp := 0
			for nUp < len(t) && t[nUp] == '.' {
				nUp++
			}
			var rest string
			if strings.Contains(t, "/") {
				rest = strings.TrimLeft(t, "./")
			} else {
				rest = strings.ReplaceAll(t[nUp:], ".", "/")
			}
			base := here
			for k := 0; k < nUp-1; k++ {
				base = cgDirname(base)
				if base == "." {
					break
				}
			}
			if base != "" {
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
	return n
}
func sortedKeys(m map[string]bool) []string {
	out := make([]string, 0, len(m))
	for k := range m {
		out = append(out, k)
	}
	sort.Strings(out)
	return out
}

var _ = filepath.Join

func (fp *fileParser) emitGenerics(n tsNode, rec srcFile, sid int32, res *fileResult) {
	if tp := nField(n, F.tparams); nValid(tp) {
		for i := uint32(0); i < nNamedChildCount(tp); i++ {
			p := nNamedChildAt(tp, i)
			switch tsKindName(nSymbol(p)) {
			case "lifetime_parameter":
				nm := cgStrip(fp.text(p))
				res.lifes = append(res.lifes, LifeRow{SymID: sid, FileID: rec.id,
					Line: int32(nStartRow(p)) + 1, name: res.put(clip(nm, 60)),
					kind: res.put("param"), IsStatic: boolT(nm == "'static")})
			case "type_parameter", "const_parameter":
				pname := fp.nodeName(p)
				if pname == "" {
					pname = clip(fp.text(p), 40)
				}
				b := nField(p, F.bounds)
				if !nValid(b) {
					continue
				}
				for j := uint32(0); j < nNamedChildCount(b); j++ {
					bd := nNamedChildAt(b, j)
					res.bounds = append(res.bounds, BoundRow{SymID: sid,
						Line: int32(nStartRow(bd)) + 1, param: res.put(clip(pname, 80)),
						bound: res.put(clip(fp.text(bd), 160)), InWhere: 0,
						IsHrtb: boolT(isHrtb(tsKindName(nSymbol(bd))))})
				}
			}
		}
	}
	for i := uint32(0); i < nNamedChildCount(n); i++ {
		c := nNamedChildAt(n, i)
		if tsKindName(nSymbol(c)) != "where_clause" {
			continue
		}
		for j := uint32(0); j < nNamedChildCount(c); j++ {
			pred := nNamedChildAt(c, j)
			if tsKindName(nSymbol(pred)) != "where_predicate" {
				continue
			}
			lname := "?"
			if l := nField(pred, F.left); nValid(l) {
				lname = clip(fp.text(l), 80)
			}
			b := nField(pred, F.bounds)
			if !nValid(b) {
				continue
			}
			for k := uint32(0); k < nNamedChildCount(b); k++ {
				bd := nNamedChildAt(b, k)
				res.bounds = append(res.bounds, BoundRow{SymID: sid,
					Line: int32(nStartRow(bd)) + 1, param: res.put(lname),
					bound: res.put(clip(fp.text(bd), 160)), InWhere: 1,
					IsHrtb: boolT(isHrtb(tsKindName(nSymbol(bd))))})
			}
		}
	}
	for _, sub := range []tsNode{nField(n, F.params), nField(n, F.ret)} {
		if !nValid(sub) {
			continue
		}
		fp.walkNodes(sub, func(c tsNode) bool {
			if tsKindName(nSymbol(c)) != "lifetime" {
				return false
			}
			nm := cgStrip(fp.text(c))
			res.lifes = append(res.lifes, LifeRow{SymID: sid, FileID: rec.id,
				Line: int32(nStartRow(c)) + 1, name: res.put(clip(nm, 60)),
				kind: res.put("use"), IsStatic: boolT(nm == "'static")})
			return false
		})
	}
}
func isHrtb(k string) bool { return k == "higher_ranked_trait_bound" || k == "for_lifetimes" }
func (fp *fileParser) emitAttrRows(n tsNode, rec srcFile, sid int32, res *fileResult) {
	prev := nPrevSibling(n)
	for nValid(prev) && kindIs(prev, "attribute_item") {
		a := attrOf(prev)
		if nValid(a) {
			nm := ""
			for i := uint32(0); i < nNamedChildCount(a); i++ {
				c := nNamedChildAt(a, i)
				if kindIs(c, "identifier") || kindIs(c, "scoped_identifier") {
					nm = fp.text(c)
					break
				}
			}
			args := ""
			if an := nField(a, F.args); nValid(an) {
				args = fp.text(an)
			}
			line := int32(nStartRow(prev)) + 1
			res.attrs = append(res.attrs, AttrRow{SymID: sid, FileID: rec.id,
				name: res.put(clip(nm, 120)), args: res.put(clip(args, 300)), Line: line})
			switch nm {
			case "derive":
				for _, d := range reIdentTok.FindAllString(args, -1) {
					res.derives = append(res.derives, DeriveRow{SymID: sid,
						FileID: rec.id, name: res.put(clip(d, 80)),
						IsStd: boolT(stdDerives[d]), Line: line})
				}
			case "cfg", "cfg_attr":
				feat := ""
				if m := reCfgFeature.FindStringSubmatch(args); m != nil {
					feat = clip(m[1], 80)
				}
				res.cfgs = append(res.cfgs, CfgRow{FileID: rec.id, SymID: sid,
					expr: res.put(clip(args, 200)), feature: res.put(feat),
					IsTest:     boolT(strings.Contains(args, "test")),
					IsAttrOnly: boolT(nm == "cfg_attr"), Line: line})
			}
		}
		prev = nPrevSibling(prev)
	}
}
func (fp *fileParser) emitUnsafeBlock(n tsNode, rec srcFile, res *fileResult,
	sid, inUnsafeFn, depth int32) {
	var deref, rawCalls, trans, fromRaw int32
	fp.walkNodes(n, func(c tsNode) bool {
		switch tsKindName(nSymbol(c)) {
		case "unary_expression":
			if nChildCount(c) > 0 && tsKindName(nSymbol(nChildAt(c, 0))) == "*" {
				deref++
			}
		case "call_expression":
			fn := nField(c, F.fn)
			if !nValid(fn) {
				return false
			}
			if kindIs(fn, "generic_function") {
				if inner := nField(fn, F.fn); nValid(inner) {
					fn = inner
				} else {
					fn = tsNode{}
				}
				if !nValid(fn) {
					return false
				}
			}
			nm := fp.text(fn)
			base := lastSegOfPath(nm)
			switch {
			case base == "transmute" || base == "transmute_copy":
				trans++
			case strings.HasPrefix(base, "from_raw"):
				fromRaw++
			default:
				rawCalls++
			}
		}
		return false
	})
	sloc := int32(0)
	cgSplitLines(string(fp.src[nStartByte(n):nEndByte(n)]), func(l string) {
		if cgStrip(l) != "" {
			sloc++
		}
	})
	res.unsafes = append(res.unsafes, UnsafeRow{0, sid, rec.id,
		int32(nStartRow(n)) + 1, sloc,
		deref + rawCalls + trans + fromRaw, deref, rawCalls, trans, fromRaw,
		boolT(fp.hasSafetyComment(n)), inUnsafeFn, boolT(depth > 0)})
}
func lastSegOfPath(s string) string {
	return lastSeg(strings.ReplaceAll(s, ".", "::"))
}
func (fp *fileParser) hasSafetyComment(n tsNode) bool {
	cur := n
	for range 4 {
		prev := nPrevSibling(cur)
		for nValid(prev) && kindIs(prev, "attribute_item") {
			prev = nPrevSibling(prev)
		}
		if nValid(prev) {
			for k := 0; k < 20 && nValid(prev) &&
				(kindIs(prev, "line_comment") || kindIs(prev, "block_comment")); k++ {
				if reSafety.MatchString(string(fp.src[nStartByte(prev):nEndByte(prev)])) {
					return true
				}
				prev = nPrevSibling(prev)
			}
			return false
		}
		cur = nParent(cur)
		if !nValid(cur) {
			return false
		}
	}
	return false
}

var dropRes = map[string]*regexp.Regexp{}

func dropRe(name string) *regexp.Regexp {
	if r, ok := dropRes[name]; ok {
		return r
	}
	r := regexp.MustCompile(`\bdrop\s*\(\s*` + regexp.QuoteMeta(name) + `\s*\)`)
	dropRes[name] = r
	return r
}
func (fp *fileParser) emitAwait(n tsNode, rec srcFile, res *fileResult, sid int32, body tsNode) {
	var guards []string
	hasRef := int32(0)
	dropped := int32(0)
	stopID := uintptr(0)
	if fn := nParent(body); nValid(fn) {
		end := minI(int(nEndByte(fn)), int(nStartByte(fn))+600)
		if end >= int(nStartByte(fn)) {
			hasRef = boolT(cgMatch(reRefCell, string(fp.src[nStartByte(fn):end])))
		}
		stopID = tsNodeId(fn)
	}
	cur := nParent(n)
	for nValid(cur) && tsNodeId(cur) != stopID {
		if kindIs(cur, "block") {
			for i := uint32(0); i < nNamedChildCount(cur); i++ {
				c := nNamedChildAt(cur, i)
				if tsKindName(nSymbol(c)) != "let_declaration" || nStartByte(c) >= nStartByte(n) {
					continue
				}
				val := nField(c, F.val)
				if !nValid(val) || !reGuard.MatchString(fp.text(val)) {
					continue
				}
				gname := "_"
				if p := nField(c, F.pat); nValid(p) {
					gname = cgStrip(fp.text(p))
				}
				span := ""
				if nEndByte(c) < nStartByte(n) {
					span = string(fp.src[nEndByte(c):nStartByte(n)])
				}
				if dropRe(gname).MatchString(span) {
					dropped = 1
					continue
				}
				guards = append(guards, clip(gname, 40))
			}
		}
		cur = nParent(cur)
	}
	depth := fp.loopDepthOf(n, body)
	res.asyncs = append(res.asyncs, AsyncRow{SymID: sid, FileID: rec.id,
		Line: int32(nStartRow(n)) + 1, InLoop: boolT(depth > 0),
		LoopDepth: depth, NGuardsLive: int32(len(guards)),
		guards: res.put(clip(strings.Join(guards, ","), 200)), GuardDropped: dropped,
		expr:            res.put(clip(strings.ReplaceAll(fp.text(n), "\n", " "), 120)),
		HasRefcellGuard: hasRef})
}

var reRefCell = regexp.MustCompile(`\bRefCell\b`)

func minI(a, b int) int {
	if a < b {
		return a
	}
	return b
}
func (fp *fileParser) emitModuleScope(root tsNode, rec srcFile, res *fileResult) {
	st := fp.measure(root, pruneById, false)
	if len(st.calls) == 0 && st.nTokens < 8 {
		return
	}
	sid := res.newSym()
	s := &res.syms[sid-1]
	s.file, s.module = rec.id, rec.moduleID
	s.parent = 0
	s.name, s.qual, s.kind = "<module>", rec.rel, kModule
	ls := int32(nStartRow(root)) + 1
	le := int32(nEndRow(root)) + 1
	s.lineS, s.lineE, s.nLines = ls, le, le-ls+1
	s.byteLo, s.byteHi = int32(nStartByte(root)), int32(nEndByte(root))
	s.sig = clip("top-level statements of "+rec.rel, 400)
	s.vis = ""
	s.setCounts(st.counts)
	s.setM(cCyclomatic, st.cyclomatic)
	s.setM(cCognitive, st.cognitive)
	s.setM(cMaxNesting, st.maxNesting)
	s.setM(cMaxLoopDepth, st.maxLoopDepth)
	s.setM(cNTokens, st.nTokens)
	s.setM(cNOperators, st.nOperators)
	s.setM(cNOperands, st.nOperands)
	s.setM(cNDistinctOperators, int32(len(st.ops)))
	s.setM(cNDistinctOperands, int32(len(st.operands)))
	s.setM(cIsGenerated, boolT(rec.isGen))
	s.setM(cIsTest, boolT(rec.isTest))
	for _, c := range st.calls {
		if c.dynamic || c.name == "" {
			continue
		}
		res.pendSid = append(res.pendSid, sid)
		res.pendLine = append(res.pendLine, c.line)
		res.pendName = append(res.pendName, fp.internStr(c.name))
		res.pendType = append(res.pendType, "")
	}
	fp.emitHazards(st, sid, rec, res)
	for _, v := range st.secrets {
		res.secrets = append(res.secrets, SecretRow{SymID: sid, FileID: rec.id,
			Line: v[1].(int32), value: res.put(v[0].(string))})
	}
	for _, l := range st.lits {
		res.lits = append(res.lits, LitRow{SymID: sid, FileID: rec.id,
			kind: res.put(l.kind), value: res.put(clip(l.value, 200)),
			Line: l.line, IsMagic: boolT(l.magic)})
	}
}
func (fp *fileParser) emitHazards(st *bodyStats, sid int32, rec srcFile, res *fileResult) {
	type key struct {
		cat  string
		n    int32
		line int32
	}
	seen := map[string]*key{}
	var order []string
	for _, c := range st.calls {
		if c.name == "" {
			continue
		}
		pat, cat, ok := fp.hazardOf(c.name)
		if !ok {
			continue
		}
		if e, ok := seen[pat]; ok {
			e.n++
			continue
		}
		seen[pat] = &key{cat, 1, c.line}
		order = append(order, pat)
	}
	for _, pat := range order {
		e := seen[pat]
		res.hazards = append(res.hazards, HazardRow{SymID: sid,
			pattern: res.put(clip(pat, 120)), category: res.put(e.cat),
			N: e.n, FirstLine: e.line})
	}
}
func (fp *fileParser) hazardOf(callee string) (string, string, bool) {
	if h, ok := fp.haz[callee]; ok {
		return h[0], h[1], h[0] != ""
	}
	cat, ok := hazardCalls[callee]
	if ok {
		fp.haz[callee] = [2]string{callee, cat}
		return callee, cat, true
	}
	if strings.IndexByte(callee, '.') < 0 {
		baseStart, twoStart := 0, -1
		for i := 0; i < len(callee); i++ {
			if callee[i] == ':' {
				j := i
				for j < len(callee) && callee[j] == ':' {
					j++
				}
				i = j - 1
				twoStart = baseStart
				baseStart = j
			}
		}
		base := callee[baseStart:]
		if cat, ok := hazardCalls[base]; ok {
			h := [2]string{"*::" + base, cat}
			fp.haz[callee] = h
			return h[0], h[1], true
		}
		if twoStart >= 0 {
			two := callee[twoStart:]
			if cat, ok := hazardCalls[two]; ok {
				fp.haz[callee] = [2]string{two, cat}
				return two, cat, true
			}
		}
		fp.haz[callee] = [2]string{}
		return "", "", false
	}
	flat := strings.ReplaceAll(callee, ".", "::")
	parts := strings.Split(flat, "::")
	base := parts[len(parts)-1]
	if cat, ok := hazardCalls[base]; ok {
		h := [2]string{"*::" + base, cat}
		fp.haz[callee] = h
		return h[0], h[1], true
	}
	if len(parts) >= 2 {
		two := strings.Join(parts[len(parts)-2:], "::")
		if cat, ok := hazardCalls[two]; ok {
			fp.haz[callee] = [2]string{two, cat}
			return two, cat, true
		}
	}
	fp.haz[callee] = [2]string{}
	return "", "", false
}
func (fp *fileParser) parseImports(root tsNode, rec srcFile, res *fileResult) {
	for i := uint32(0); i < nNamedChildCount(root); i++ {
		n := nNamedChildAt(root, i)
		switch tsKindName(nSymbol(n)) {
		case "extern_crate_declaration":
			nm := "?"
			if c := nField(n, F.name); nValid(c) {
				nm = clip(fp.text(c), 300)
			}
			res.imports = append(res.imports, ImportRow{FileID: rec.id,
				target: res.put(nm), TargetID: -1, kind: res.put("extern crate"),
				Line: int32(nStartRow(n)) + 1, IsExternal: 1, NNames: 1})
			continue
		case "use_declaration":
		default:
			continue
		}
		arg := nField(n, F.arg)
		if !nValid(arg) {
			continue
		}
		target := strings.ReplaceAll(fp.text(arg), "\n", " ")
		head := strings.TrimSpace(clipStr(target, "::"))
		relative := head == "crate" || head == "self" || head == "super"
		external := int32(0)
		if !relative && !stdRoots[head] {
			external = 1
		}
		names := int32(1)
		if strings.Contains(target, "{") {
			names = int32(strings.Count(target, ",") + 1)
		}
		hasAlias := false
		alias := ""
		if kindIs(arg, "use_as_clause") {
			if a := nField(arg, F.alias); nValid(a) {
				alias, hasAlias = fp.text(a), true
			}
		}
		res.imports = append(res.imports, ImportRow{FileID: rec.id,
			target: res.put(clip(target, 300)), alias: res.put(alias),
			HasAlias: hasAlias, TargetID: -1, kind: res.put("use"),
			Line:       int32(nStartRow(n)) + 1,
			IsExternal: external, IsRelative: boolT(relative),
			IsWildcard: boolT(strings.Contains(target, "*")), NNames: names})
	}
}
func (fp *fileParser) parseFileExtra(root tsNode, rec srcFile, res *fileResult) {
	for i := uint32(0); i < nNamedChildCount(root); i++ {
		n := nNamedChildAt(root, i)
		if tsKindName(nSymbol(n)) != "inner_attribute_item" {
			continue
		}
		a := attrOf(n)
		if !nValid(a) {
			continue
		}
		nm := ""
		for j := uint32(0); j < nNamedChildCount(a); j++ {
			c := nNamedChildAt(a, j)
			if kindIs(c, "identifier") || kindIs(c, "scoped_identifier") {
				nm = fp.text(c)
				break
			}
		}
		args := ""
		if an := nField(a, F.args); nValid(an) {
			args = fp.text(an)
		}
		line := int32(nStartRow(n)) + 1
		res.attrs = append(res.attrs, AttrRow{SymID: -1, FileID: rec.id,
			name: res.put(clip(nm, 120)), args: res.put(clip(args, 300)), Line: line})
		if nm == "cfg" || nm == "cfg_attr" {
			feat := ""
			if m := reCfgFeature.FindStringSubmatch(args); m != nil {
				feat = clip(m[1], 80)
			}
			res.cfgs = append(res.cfgs, CfgRow{FileID: rec.id, SymID: -1,
				expr: res.put(clip(args, 200)), feature: res.put(feat),
				IsTest:     boolT(strings.Contains(args, "test")),
				IsAttrOnly: boolT(nm == "cfg_attr"), Line: line})
		}
	}
}

var (
	reEdition = regexp.MustCompile(`(?m)^\s*edition\s*=\s*"(\d+)"`)
	reMSRV    = regexp.MustCompile(`(?m)^\s*rust-version\s*=\s*"([^"]+)"`)
	reCrateNm = regexp.MustCompile(`(?m)^\s*name\s*=\s*"([^"]+)"`)
	reDepRow  = regexp.MustCompile(`(?m)^\s*([A-Za-z0-9_-]+)\s*=\s*(?:\{\s*version\s*=\s*"([^"]*)"|"([^"]*)")`)
	reFeatRow = regexp.MustCompile(`^\s*([A-Za-z0-9_\-]+)\s*=\s*\[(.*?)\]`)
	reOptDep  = regexp.MustCompile(`(?m)^\s*([A-Za-z0-9_\-]+)\s*=\s*\{[^}]*optional\s*=\s*true`)
)

type manifestState struct {
	edition, rustVersion, crateName string
	features                        map[string]bool
	feats                           []FeatRow
	deps                            []DepRow
}

func readManifests(root string, g *Graph) {
	ms := &manifestState{features: map[string]bool{}}
	var paths []string
	if isFile(root + "/Cargo.toml") {
		paths = append(paths, root+"/Cargo.toml")
	}
	ents, err := readDirNames(root)
	if err == nil {
		for _, e := range ents {
			sub := root + "/" + e + "/Cargo.toml"
			if isFile(sub) {
				paths = append(paths, sub)
			}
		}
	}
	if len(paths) == 0 {
		g.SetMeta("edition", "unknown (no Cargo.toml found)")
		return
	}
	for i, p := range paths {
		text := readText(p)
		if i == 0 || ms.edition == "" {
			if m := reEdition.FindStringSubmatch(text); m != nil {
				ms.edition = m[1]
			}
			if m := reMSRV.FindStringSubmatch(text); m != nil {
				ms.rustVersion = m[1]
			}
			if m := reCrateNm.FindStringSubmatch(text); m != nil && ms.crateName == "" {
				ms.crateName = m[1]
			}
		}
		readFeatures(text, ms)
		for _, sect := range []struct {
			name  string
			isDev int32
		}{{"dependencies", 0}, {"dev-dependencies", 1}} {
			for _, line := range tomlSection(text, sect.name) {
				for _, dm := range reDepRow.FindAllStringSubmatch(line, -1) {
					v := dm[2]
					if v == "" {
						v = dm[3]
					}
					ms.deps = append(ms.deps, DepRow{name: cgPut(clip(dm[1], 120)),
						version: cgPut(clip(v, 40)), IsDev: sect.isDev})
				}
			}
		}
	}
	crate := ms.crateName
	if crate == "" {
		crate = "?"
	}
	letChains := "NO -- rustc rejects `if let ... && ...` before edition 2024; " +
		"the grammar still parses it, so a non-zero n_let_chains here is code that does not build"
	if ms.edition == "2024" {
		letChains = "yes (edition 2024)"
	}
	declared := "(none)"
	if len(ms.features) > 0 {
		declared = strings.Join(sortedKeys(ms.features), ", ")
	}
	g.SetMeta("crate", crate)
	g.SetMeta("edition", orDefault(ms.edition, "2015 (unset)"))
	g.SetMeta("rust_version", orDefault(ms.rustVersion, "(no MSRV declared)"))
	g.SetMeta("let_chains", letChains)
	g.SetMeta("declared_features", declared)
	for i := range ms.feats {
		ms.feats[i].ID = int32(i + 1)
	}
	g.Feat = append(g.Feat, ms.feats...)
	for i := range ms.deps {
		ms.deps[i].ID = int32(len(g.Deps) + i + 1)
	}
	g.Deps = append(g.Deps, ms.deps...)
}
func orDefault(s, d string) string {
	if s == "" {
		return d
	}
	return s
}
func readFeatures(text string, ms *manifestState) {
	for _, line := range tomlSection(text, "features") {
		m := reFeatRow.FindStringSubmatch(line)
		if m == nil || ms.features[m[1]] {
			continue
		}
		name := m[1]
		ms.features[name] = true
		ms.feats = append(ms.feats, FeatRow{name: cgPut(name),
			enables: cgPut(clip(m[2], 300)), IsDefault: boolT(name == "default")})
	}
	for _, m := range reOptDep.FindAllStringSubmatch(text, -1) {
		if ms.features[m[1]] {
			continue
		}
		ms.features[m[1]] = true
		ms.feats = append(ms.feats, FeatRow{name: cgPut(m[1]),
			enables: cgPut("(optional dep)"), IsDefault: 0})
	}
}
func tomlSection(text, name string) []string {
	lines := strings.Split(text, "\n")
	var out []string
	in := false
	for _, l := range lines {
		t := strings.TrimRight(l, "\r")
		if strings.HasPrefix(t, "[") {
			if in {
				return out
			}
			in = t == "["+name+"]"
			continue
		}
		if in {
			out = append(out, t)
		}
	}
	return out
}

var markerNames = [...]string{"TODO", "FIXME", "XXX", "HACK", "BUG", "NOTE",
	"WARNING", "OPTIMIZE", "REVIEW", "DEPRECATED", "SAFETY", "PANIC", "UNSAFE"}

func markerKind(w []byte) int {
	for k := range markerNames {
		if markerEq(w, markerNames[k]) {
			return k
		}
	}
	return -1
}

func markerEq(w []byte, name string) bool {
	if len(w) != len(name) {
		return false
	}
	for i := 0; i < len(w); i++ {
		c := w[i]
		if c >= 'a' && c <= 'z' {
			c -= 32
		}
		if c != name[i] {
			return false
		}
	}
	return true
}

func isMarkerWordByte(c byte) bool {
	return c == '_' || (c >= '0' && c <= '9') ||
		(c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')
}

func scanMarkerFind(line []byte) (int, int, bool) {
	for i := 0; i < len(line); {
		if !isMarkerWordByte(line[i]) {
			i++
			continue
		}
		start := i
		for i < len(line) && isMarkerWordByte(line[i]) {
			i++
		}
		if markerKind(line[start:i]) < 0 {
			continue
		}
		j := i
		for j < len(line) && (line[j] == ' ' || line[j] == '\t') {
			j++
		}
		if j < len(line) {
			f := line[j]
			if f == ':' || f == '-' || f == '(' {
				return start, i, true
			}
		}
	}
	return 0, 0, false
}

func splitLinesBytes(data []byte, fn func(line []byte)) {
	if len(data) == 0 {
		return
	}
	start := 0
	i := 0
	for i < len(data) {
		c := data[i]
		if c < utf8.RuneSelf {
			if c == '\n' || c == '\v' || c == '\f' || c == '\r' ||
				c == 0x1c || c == 0x1d || c == 0x1e {
				fn(data[start:i])
				if c == '\r' && i+1 < len(data) && data[i+1] == '\n' {
					i++
				}
				i++
				start = i
				continue
			}
			i++
			continue
		}
		r, w := utf8.DecodeRune(data[i:])
		if r == 0x85 || r == 0x2028 || r == 0x2029 {
			fn(data[start:i])
			i += w
			start = i
			continue
		}
		i += w
	}
	if start < len(data) {
		fn(data[start:])
	}
}

func scanMarkers(rec srcFile, res *fileResult) {
	splitLinesBytes(rec.data, func(line []byte) {
		res.nMarkerLines++
		if !bytes.Contains(line, []byte("//")) && !bytes.Contains(line, mashtag) &&
			!bytes.Contains(line, []byte("*")) && !bytes.Contains(line, []byte("--")) {
			return
		}
		a, b, ok := scanMarkerFind(line)
		if !ok {
			return
		}
		ls := string(line)
		res.markers = append(res.markers, MarkerRow{FileID: rec.id, SymID: -1,
			kind: res.put(markerNames[markerKind(line[a:b])]),
			Line: res.nMarkerLines, text: res.put(clip(cgStrip(ls), 200))})
	})
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
	{name: "async_points",
		note: "an .await inside a function, with the guards live there",
		cols: []columnShape{
			{"id", "int", false},
			{"symbol_id", "int", false},
			{"file_id", "int", false},
			{"line", "int", false},
			{"in_loop", "int", false},
			{"loop_depth", "int", false},
			{"n_guards_live", "int", false},
			{"guards", "text", false},
			{"guard_dropped", "int", false},
			{"expr", "text", false},
			{"has_refcell_guard", "int", false},
		}},
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
	{name: "cfg_blocks",
		note: "a #[cfg(...)] attribute and the configuration it tests",
		cols: []columnShape{
			{"id", "int", false},
			{"file_id", "int", false},
			{"symbol_id", "int", true},
			{"expr", "text", false},
			{"feature", "text", false},
			{"is_test", "int", false},
			{"is_attr_only", "int", false},
			{"line", "int", false},
		}},
	{name: "crate_features",
		note: "features declared in the manifest and what they enable",
		cols: []columnShape{
			{"id", "int", false},
			{"name", "text", false},
			{"enables", "text", false},
			{"is_default", "int", false},
		}},
	{name: "deps",
		note: "dependencies declared in the manifest, against what is used",
		cols: []columnShape{
			{"id", "int", false},
			{"name", "text", false},
			{"version", "text", false},
			{"is_dev", "int", false},
		}},
	{name: "derives",
		note: "a derive macro and the traits it is asked to implement",
		cols: []columnShape{
			{"id", "int", false},
			{"symbol_id", "int", true},
			{"file_id", "int", false},
			{"name", "text", false},
			{"is_std", "int", false},
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
	{name: "generic_bounds",
		note: "a generic parameter and the bounds placed on it",
		cols: []columnShape{
			{"id", "int", false},
			{"symbol_id", "int", false},
			{"param", "text", false},
			{"bound", "text", false},
			{"in_where", "int", false},
			{"is_hrtb", "int", false},
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
	{name: "impls",
		note: "an inherent or trait impl block, and what it declares",
		cols: []columnShape{
			{"id", "int", false},
			{"symbol_id", "int", false},
			{"file_id", "int", false},
			{"type_name", "text", false},
			{"trait_name", "text", false},
			{"is_unsafe", "int", false},
			{"is_negative", "int", false},
			{"is_generic", "int", false},
			{"n_methods", "int", false},
			{"n_unsafe_methods", "int", false},
			{"line", "int", false},
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
	{name: "lifetimes",
		note: "a lifetime parameter and where it is constrained",
		cols: []columnShape{
			{"id", "int", false},
			{"symbol_id", "int", false},
			{"file_id", "int", false},
			{"name", "text", false},
			{"kind", "text", false},
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
	{name: "macros",
		note: "a macro invocation, and which definition it expands to",
		cols: []columnShape{
			{"id", "int", false},
			{"symbol_id", "int", true},
			{"file_id", "int", false},
			{"name", "text", false},
			{"kind", "text", false},
			{"n_rules", "int", false},
			{"body_bytes", "int", false},
			{"defines_items", "int", false},
			{"n_unsafe", "int", false},
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
			{"n_unsafe", "int", false},
			{"n_panic", "int", false},
			{"n_alloc", "int", false},
			{"n_clone", "int", false},
			{"n_lock", "int", false},
			{"n_atomic", "int", false},
			{"n_async", "int", false},
			{"n_io", "int", false},
			{"n_ffi", "int", false},
			{"n_mem", "int", false},
			{"n_exec", "int", false},
			{"n_control", "int", false},
			{"n_let_else", "int", false},
			{"n_unsafe_blocks", "int", false},
			{"n_unsafe_ops", "int", false},
			{"n_safety_comments", "int", false},
			{"is_unsafe_fn", "int", false},
			{"n_unwrap", "int", false},
			{"n_expect", "int", false},
			{"n_panic_macro", "int", false},
			{"n_index_expr", "int", false},
			{"n_slice_range", "int", false},
			{"n_question_mark", "int", false},
			{"n_borrow_calls", "int", false},
			{"n_clone_in_loop", "int", false},
			{"n_to_owned", "int", false},
			{"n_collect", "int", false},
			{"n_format_macro", "int", false},
			{"n_sql_literal", "int", false},
			{"n_deserialize", "int", false},
			{"n_zip_read", "int", false},
			{"n_with_capacity", "int", false},
			{"n_iter_adapters", "int", false},
			{"n_await", "int", false},
			{"n_async_blocks", "int", false},
			{"n_lock_acquire", "int", false},
			{"n_lock_across_await", "int", false},
			{"n_blocking_io", "int", false},
			{"n_blocking_in_async", "int", false},
			{"n_spawn", "int", false},
			{"n_spawn_blocking", "int", false},
			{"n_channel_ops", "int", false},
			{"is_async_fn", "int", false},
			{"n_atomic_ops", "int", false},
			{"n_relaxed_ordering", "int", false},
			{"n_seqcst_ordering", "int", false},
			{"n_arc_mutex", "int", false},
			{"n_rc_refcell", "int", false},
			{"n_weak_refs", "int", false},
			{"n_box_dyn", "int", false},
			{"n_dyn_params", "int", false},
			{"n_impl_trait", "int", false},
			{"n_trait_bounds", "int", false},
			{"n_where_predicates", "int", false},
			{"n_lifetimes", "int", false},
			{"n_hrtb", "int", false},
			{"n_turbofish", "int", false},
			{"n_mono_instantiations", "int", false},
			{"n_raw_ptr", "int", false},
			{"n_transmute", "int", false},
			{"n_extern_calls", "int", false},
			{"n_from_raw", "int", false},
			{"n_into_raw", "int", false},
			{"n_static_mut", "int", false},
			{"is_extern_fn", "int", false},
			{"n_derives", "int", false},
			{"n_macro_invocations", "int", false},
			{"n_allow_attrs", "int", false},
			{"n_expect_attrs", "int", false},
			{"n_inline_attrs", "int", false},
			{"n_cfg_blocks", "int", false},
			{"n_cfg_features", "int", false},
			{"n_as_casts", "int", false},
			{"n_checked_arith", "int", false},
			{"n_arith_unchecked", "int", false},
			{"n_match_arms", "int", false},
			{"n_let_chains", "int", false},
			{"is_const_fn", "int", false},
			{"n_lock_in_loop", "int", false},
			{"n_to_owned_in_loop", "int", false},
			{"n_safe_fallback", "int", false},
			{"n_error_swallow", "int", false},
			{"n_iter_in_loop", "int", false},
			{"n_push_in_loop", "int", false},
			{"n_io_in_loop", "int", false},
			{"n_block_on", "int", false},
			{"n_thread_sleep", "int", false},
			{"n_len_in_loop", "int", false},
			{"n_borrow_mut", "int", false},
			{"n_unwrap_err", "int", false},
			{"n_unchecked_call", "int", false},
			{"n_elif", "int", false},
			{"n_external_calls", "int", false},
			{"impl_type", "text", false},
			{"is_trait_method", "int", false},
			{"n_thread_spawn", "int", false},
			{"n_spawn_in_loop", "int", false},
			{"n_join_calls", "int", false},
		}},
	{name: "sym_fts",
		note: "a contentless full-text index over (name, qual_name, signature): every column reads back empty, and the four shadow b-tree tables beside it are not reproduced at all",
		cols: []columnShape{
			{"name", "any", true},
			{"qual_name", "any", true},
			{"signature", "any", true},
		}},
	{name: "traits",
		note: "a trait/interface declaration, and what implements it",
		cols: []columnShape{
			{"symbol_id", "int", false},
			{"file_id", "int", false},
			{"name", "text", false},
			{"n_required", "int", false},
			{"n_provided", "int", false},
			{"n_assoc_types", "int", false},
			{"n_assoc_consts", "int", false},
			{"n_supertraits", "int", false},
			{"is_unsafe", "int", false},
			{"is_public", "int", false},
			{"is_generic", "int", false},
			{"has_assoc_type", "int", false},
			{"methods", "text", false},
		}},
	{name: "unresolved_calls",
		note: "a call we saw but could not point at a definition",
		cols: []columnShape{
			{"caller_id", "int", false},
			{"name", "text", false},
			{"n", "int", false},
			{"first_line", "int", false},
		}},
	{name: "unsafe_blocks",
		note: "an unsafe block, and what it does inside one",
		cols: []columnShape{
			{"id", "int", false},
			{"symbol_id", "int", false},
			{"file_id", "int", false},
			{"line", "int", false},
			{"sloc", "int", false},
			{"n_ops", "int", false},
			{"n_deref", "int", false},
			{"n_raw_calls", "int", false},
			{"n_transmute", "int", false},
			{"n_from_raw", "int", false},
			{"has_safety_comment", "int", false},
			{"in_unsafe_fn", "int", false},
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
const (
	tsRuntimeVersion = "0.25.10"
	tsGrammarVersion = "0.24.2"
)
const parserBanner = "parser: tree-sitter " + tsRuntimeVersion +
	" + tree-sitter-rust " + tsGrammarVersion

var _ = time.Now

func sprintf(f string, a ...any) string { return fmt.Sprintf(f, a...) }
func itoa(i int) string                 { return strconv.Itoa(i) }
func printfln(f string, a ...any)       { fmt.Fprintf(os.Stdout, f+"\n", a...) }
func eprintln(s string)                 { fmt.Fprintln(os.Stderr, s) }
func isFile(p string) bool {
	fi, err := os.Stat(p)
	return err == nil && fi.Mode().IsRegular()
}
func readDirNames(p string) ([]string, error) {
	ents, err := os.ReadDir(p)
	if err != nil {
		return nil, err
	}
	out := make([]string, 0, len(ents))
	for _, e := range ents {
		out = append(out, e.Name())
	}
	sort.Strings(out)
	return out, nil
}
func readText(p string) string {
	b, err := os.ReadFile(p)
	if err != nil {
		return ""
	}
	return string(b)
}
func isAllDigits(s string) bool {
	for i := 0; i < len(s); i++ {
		if s[i] < '0' || s[i] > '9' {
			return false
		}
	}
	return len(s) > 0
}
func peakWatch() func() {
	if os.Getenv("CG_PEAKWATCH") == "" {
		return func() {}
	}
	at, _ := strconv.ParseUint(os.Getenv("CG_PEAKHEAPAT"), 10, 64)
	heapFile := os.Getenv("CG_PEAKHEAPFILE")
	heapDone := at == 0 || heapFile == ""
	mib := func(v uint64) string { return sprintf("%.1f", float64(v)/(1024*1024)) }
	var maxAlloc, maxInuse, maxSys uint64
	done := make(chan struct{})
	finished := make(chan struct{})
	go func() {
		defer close(finished)
		t := time.NewTicker(25 * time.Millisecond)
		defer t.Stop()
		for {
			select {
			case <-done:
				return
			case <-t.C:
				var m runtime.MemStats
				runtime.ReadMemStats(&m)
				if m.HeapAlloc > maxAlloc {
					maxAlloc = m.HeapAlloc
				}
				if m.HeapInuse > maxInuse {
					maxInuse = m.HeapInuse
				}
				if m.Sys > maxSys {
					maxSys = m.Sys
				}
				if !heapDone && m.HeapAlloc >= at*(1024*1024) {
					heapDone = true
					if f, err := os.Create(heapFile); err == nil {
						pprof.Lookup("heap").WriteTo(f, 0)
						f.Close()
						fmt.Fprintf(os.Stderr, "peakwatch: heap profile at %sMiB -> %s\n",
							mib(m.HeapAlloc), heapFile)
					}
				}
			}
		}
	}()
	return func() {
		close(done)
		<-finished
		fmt.Fprintf(os.Stderr, "peakwatch: HeapAlloc(max)=%sMiB HeapInuse(max)=%sMiB Sys(max)=%sMiB goroutines=%d\n",
			mib(maxAlloc), mib(maxInuse), mib(maxSys), runtime.NumGoroutine())
	}
}

const progName = "codegraph_rust"

type flagSpec struct {
	name    string
	hasArg  bool
	metavar string
}

var flagSpecs = []flagSpec{
	{"module", true, ""},
	{"limit", true, ""},
	{"list", false, ""},
	{"metrics", false, ""},
	{"schema", false, ""},
	{"report", false, ""},
	{"csv", true, "N"},
	{"json", true, "N"},
	{"save", true, "PATH"},
	{"save-ast", true, "PATH"},
	{"load-ast", true, "PATH"},
	{"dump", true, "PATH"},
	{"force", false, ""},
	{"deps", false, ""},
	{"install-deps", false, ""},
	{"include-generated", false, ""},
	{"include-vendored", false, ""},
	{"no-tests", false, ""},
	{"quiet", false, ""},
	{"version", false, ""},
	{"workers", true, "N"},
	{"cpuprofile", true, "PATH"},
	{"memprofile", true, "PATH"},
	{"blockprofile", true, "PATH"},
	{"mutexprofile", true, "PATH"},
	{"trace", true, "PATH"},
}

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
	hasSave          bool
	saveAST          string
	loadAST          string
	dump             string
	hasDump          bool
	force            bool
	deps             bool
	installDeps      bool
	includeGenerated bool
	includeVendored  bool
	noTests          bool
	quiet            bool
	version          bool
	workers          int
	cpuProf          string
	memProf          string
	blockProf        string
	mutexProf        string
	traceOut         string
}

func cgRepr(s string) string {
	if strings.Contains(s, "'") && !strings.Contains(s, "\"") {
		return "\"" + s + "\""
	}
	return "'" + s + "'"
}
func symlinkTarget(path string) string {
	if real, err := filepath.EvalSymlinks(path); err == nil {
		return real
	}
	abs, err := filepath.Abs(path)
	if err != nil {
		return path
	}
	dir, base := filepath.Split(abs)
	if base == "" {
		return abs
	}
	rd, err := filepath.EvalSymlinks(filepath.Clean(dir))
	if err != nil {
		rd = filepath.Clean(dir)
	}
	sep := string(filepath.Separator)
	target, err := os.Readlink(rd + sep + base)
	if err != nil {
		return rd + sep + base
	}
	if !filepath.IsAbs(target) {
		target = filepath.Join(rd, target)
	}
	return target
}
func usageErr(msg string) {
	if j := strings.Index(usageText, "\n\n"); j > 0 {
		fmt.Fprint(os.Stderr, usageText[:j+1])
	}
	fmt.Fprintf(os.Stderr, "%s: error: %s\n", progName, msg)
	os.Exit(2)
}
func parseArgs(argv []string) *cli {
	c := &cli{root: ".", module: "%", limit: -1, workers: 0}
	var positional []string
	find := func(name string) (flagSpec, bool) {
		for _, f := range flagSpecs {
			if f.name == name {
				return f, true
			}
		}
		var match *flagSpec
		for i := range flagSpecs {
			if strings.HasPrefix(flagSpecs[i].name, name) {
				if match != nil {
					return flagSpec{}, false
				}
				match = &flagSpecs[i]
			}
		}
		if match != nil {
			return *match, true
		}
		return flagSpec{}, false
	}
	set := func(f flagSpec, val string, hasVal bool) {
		switch f.name {
		case "module":
			c.module = val
		case "limit":
			n, err := strconv.Atoi(val)
			if err != nil {
				usageErr("argument --limit: invalid int value: " + cgRepr(val))
			}
			c.limit = n
		case "list":
			c.list = true
		case "metrics":
			c.metrics = true
		case "schema":
			c.schema = true
		case "report":
			c.report = true
		case "csv":
			n, err := strconv.Atoi(val)
			if err != nil {
				usageErr("argument --csv: invalid int value: " + cgRepr(val))
			}
			c.csv, c.hasCSV = n, true
		case "json":
			n, err := strconv.Atoi(val)
			if err != nil {
				usageErr("argument --json: invalid int value: " + cgRepr(val))
			}
			c.json, c.hasJSON = n, true
		case "save":
			c.save, c.hasSave = val, true
		case "save-ast":
			c.saveAST = val
		case "load-ast":
			c.loadAST = val
		case "dump":
			c.dump, c.hasDump = val, true
		case "force":
			c.force = true
		case "deps":
			c.deps = true
		case "install-deps":
			c.installDeps = true
		case "include-generated":
			c.includeGenerated = true
		case "include-vendored":
			c.includeVendored = true
		case "no-tests":
			c.noTests = true
		case "quiet":
			c.quiet = true
		case "version":
			c.version = true
		case "workers":
			n, err := strconv.Atoi(val)
			if err != nil {
				usageErr("argument --workers: invalid int value: " + cgRepr(val))
			}
			c.workers = n
		case "cpuprofile":
			c.cpuProf = val
		case "memprofile":
			c.memProf = val
		case "trace":
			c.traceOut = val
		case "blockprofile":
			c.blockProf = val
		case "mutexprofile":
			c.mutexProf = val
		}
		_ = hasVal
	}
	for i := 0; i < len(argv); i++ {
		a := argv[i]
		switch {
		case a == "--":
			positional = append(positional, argv[i+1:]...)
			i = len(argv)
		case a == "-h", a == "--help":
			fmt.Print(usageText)
			os.Exit(0)
		case strings.HasPrefix(a, "--"):
			name := a[2:]
			val := ""
			hasVal := false
			if j := strings.IndexByte(name, '='); j >= 0 {
				val, hasVal = name[j+1:], true
				name = name[:j]
			}
			f, ok := find(name)
			if !ok {
				usageErr("unrecognized arguments: " + a)
			}
			if f.hasArg && !hasVal {
				if i+1 >= len(argv) {
					usageErr("argument " + a + ": expected one argument")
				}
				i++
				val, hasVal = argv[i], true
			}
			set(f, val, hasVal)
		case len(a) > 1 && a[0] == '-':
			if isAllDigits(a[1:]) {
				positional = append(positional, a)
			} else {
				usageErr("unrecognized arguments: " + a)
			}
		default:
			positional = append(positional, a)
		}
	}
	if len(positional) > 0 {
		c.root = positional[0]
	}
	if len(positional) > 1 {
		for _, p := range positional[1:] {
			n, err := strconv.Atoi(p)
			if err != nil {
				usageErr("argument which: invalid int value: " + cgRepr(p))
			}
			c.which = append(c.which, n)
		}
	}
	return c
}

const usageText = `usage: codegraph_rust [-h] [--module MODULE] [--limit LIMIT] [--list]
                      [--metrics] [--schema] [--report] [--csv N]
                      [--json N] [--save PATH] [--save-ast PATH]
                      [--load-ast PATH] [--force] [--deps]
                      [--install-deps] [--include-generated]
                      [--include-vendored] [--no-tests] [--quiet] [--version]
                      [--dump PATH] [--workers N] [--cpuprofile PATH]
                      [--memprofile PATH] [--blockprofile PATH]
                      [--mutexprofile PATH] [--trace PATH]
                      [root] [which ...]

Parse a rust tree into an in-memory graph and query it in one shot. Target: Rust 1.97 (edition 2024)

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
  --dump PATH          write the canonical graph dump (verification hook)
  --workers N          accepted for compatibility; the reader runs one
                       tree-sitter child at a time, so N changes nothing
  --cpuprofile PATH    write a CPU profile
  --memprofile PATH    write a heap profile at exit
  --blockprofile PATH  write a block profile
  --mutexprofile PATH  write a mutex profile
  --trace PATH         write an execution trace

every run re-parses from source unless --load-ast hands it a saved AST state, so an answer can never describe code that has moved on
`

func cgPutU32(b []byte, o int, v uint32) { *(*uint32)(unsafe.Pointer(&b[o])) = v }
func cgPutU64(b []byte, o int, v uint64) { *(*uint64)(unsafe.Pointer(&b[o])) = v }

func cgGetU32(b []byte, o int) uint32 { return *(*uint32)(unsafe.Pointer(&b[o])) }
func cgGetU64(b []byte, o int) uint64 { return *(*uint64)(unsafe.Pointer(&b[o])) }

func main() {
	c := parseArgs(os.Args[1:])
	if c.version {
		fmt.Printf("%s  target=%s  schema=v%d  go=%s\n", progName, targetVersion, 1, runtime.Version())
		return
	}
	if c.installDeps {
		if !c.quiet {
			fmt.Println("all dependencies already present")
		}
		if c.deps {
			fmt.Println()
			describeDeps()
			return
		}
	} else if c.deps {
		describeDeps()
		return
	}
	if c.schema {
		fmt.Print(schemaNative())
		return
	}
	showMetrics = c.metrics
	qs := queries()
	if c.list {
		for i, q := range qs {
			fmt.Printf("%2d. %-26s %s\n", i+1, q.name, q.title)
		}
		return
	}
	if c.hasCSV || c.hasJSON {
		c.quiet = true
	}
	if c.saveAST != "" && c.loadAST != "" {
		fmt.Fprintln(os.Stderr, "--save-ast and --load-ast cannot be used together")
		os.Exit(2)
	}
	if c.loadAST == "" {
		fi, err := os.Stat(c.root)
		if err != nil || !fi.IsDir() {
			fmt.Fprintf(os.Stderr, "not a directory: %s\n", c.root)
			os.Exit(2)
		}
	}
	opts.quiet = c.quiet
	opts.includeTests = !c.noTests
	opts.includeGenerated = c.includeGenerated
	opts.includeVendored = c.includeVendored
	opts.workers = c.workers
	if opts.workers <= 0 {
		opts.workers = defaultParseWorkers
	}
	if v := os.Getenv("CG_GOGC"); v != "" {
		n, _ := strconv.Atoi(v)
		debug.SetGCPercent(n)
	} else {
		debug.SetGCPercent(30)
	}
	defer peakWatch()()
	if c.cpuProf != "" {
		f, _ := os.Create(c.cpuProf)
		pprof.StartCPUProfile(f)
		defer pprof.StopCPUProfile()
	}
	if c.traceOut != "" {
		f, _ := os.Create(c.traceOut)
		trace.Start(f)
		defer func() {
			trace.Stop()
			f.Close()
			fmt.Fprintf(os.Stderr, "goroutines at exit: %d\n", runtime.NumGoroutine())
		}()
	}
	if c.blockProf != "" {
		runtime.SetBlockProfileRate(1)
		defer func() {
			f, _ := os.Create(c.blockProf)
			pprof.Lookup("block").WriteTo(f, 0)
			f.Close()
		}()
	}
	if c.mutexProf != "" {
		runtime.SetMutexProfileFraction(1)
		defer func() {
			f, _ := os.Create(c.mutexProf)
			pprof.Lookup("mutex").WriteTo(f, 0)
			f.Close()
		}()
	}
	abs, _ := filepath.Abs(c.root)
	t0 := time.Now()
	var g *Graph
	var n int
	var err error
	if c.loadAST != "" {
		g, err = loadAST(c.loadAST)
		if err != nil {
			fmt.Fprintf(os.Stderr, "load-ast: %v\n", err)
			os.Exit(2)
		}
	} else {
		opts.keepTrees = c.saveAST != ""
		g = &Graph{}
		n, err = build(abs, g)
		if err != nil {
			fmt.Fprintln(os.Stderr, err)
			os.Exit(1)
		}
	}
	took := time.Since(t0)
	tIx := time.Now()
	g.finishDerived()
	if !c.quiet {
		printfln("  indexed in %.1fs", time.Since(tIx).Seconds())
	}
	if c.saveAST != "" {
		if _, serr := os.Lstat(c.saveAST); serr == nil && !c.force {
			fmt.Fprintf(os.Stderr, "refusing to overwrite %s (pass --force)\n", c.saveAST)
			os.Exit(2)
		}
		ts := time.Now()
		nb, werr := saveASTFile(g, c.saveAST)
		if werr != nil {
			fmt.Fprintf(os.Stderr, "save-ast: %v\n", werr)
			os.Exit(2)
		}
		if !c.quiet {
			eprintln(sprintf("ast state written to %s: %d bytes in %.1fs",
				c.saveAST, nb, time.Since(ts).Seconds()))
		}
	}
	if c.memProf != "" {
		f, _ := os.Create(c.memProf)
		pprof.Lookup("allocs").WriteTo(f, 0)
		f.Close()
	}
	if c.hasCSV || c.hasJSON {
		idx := c.csv - 1
		if c.hasJSON {
			idx = c.json - 1
		}
		if idx < 0 || idx >= len(qs) {
			fmt.Fprintf(os.Stderr, "no query %d\n", idx+1)
			os.Exit(2)
		}
		r := runQuery(g, qs[idx], c.module, c.limit)
		if c.hasCSV {
			writeCSV(os.Stdout, r)
		} else {
			writeJSON(os.Stdout, r)
		}
		return
	}
	out := bufio.NewWriter(os.Stdout)
	defer out.Flush()
	if !c.quiet {
		lim := "all"
		if c.limit >= 0 {
			lim = itoa(c.limit)
		}
		if c.loadAST != "" {
			fmt.Fprintf(out, "codegraph-%s: %d files loaded from AST in %.1fs module=%s limit=%s\n",
				langName, len(g.Files), took.Seconds(), c.module, lim)
		} else {
			fmt.Fprintf(out, "codegraph-%s: %d files parsed into memory in %.1fs module=%s limit=%s\n",
				langName, n, took.Seconds(), c.module, lim)
		}
	}
	if c.report {
		report(out, g)
	}
	sel := c.which
	if len(sel) == 0 {
		sel = make([]int, len(qs))
		for i := range qs {
			sel[i] = i + 1
		}
	}
	for _, k := range sel {
		if k < 1 || k > len(qs) {
			continue
		}
		q := qs[k-1]
		fmt.Fprintf(out, "\n%s\n", strings.Repeat("=", 78))
		fmt.Fprintf(out, "Q%d. %s -- %s\n", k, q.name, q.title)
		fmt.Fprintf(out, "%s\n", strings.Repeat("-", 78))
		for line := range strings.SplitSeq(q.notes, "\n") {
			fmt.Fprintf(out, " %s\n", line)
		}
		fmt.Fprintln(out)
		render(out, runQuery(g, q, c.module, c.limit))
	}
	out.Flush()
	if c.hasSave {
		if _, err := os.Lstat(c.save); err == nil && !c.force {
			msg := "\nrefusing to overwrite " + c.save + " (pass --force)"
			if li, lerr := os.Lstat(c.save); lerr == nil && li.Mode()&os.ModeSymlink != 0 {
				msg += " -- it is a symlink to " + symlinkTarget(c.save)
			}
			fmt.Fprintln(os.Stderr, msg)
		} else {
			if li, lerr := os.Lstat(c.save); lerr == nil && li.Mode()&os.ModeSymlink != 0 {
				os.Remove(c.save)
			}
			if err := saveGraph(g, c.save); err != nil {
				fmt.Fprintf(os.Stderr, "\ncould not write %s: %s\n", c.save, err)
			} else {
				fmt.Fprintf(out, "\n(graph also written to %s)\n", c.save)
			}
		}
	}
	if c.hasDump {
		f, err := os.Create(c.dump)
		if err != nil {
			fmt.Fprintf(os.Stderr, "could not write %s: %s\n", c.dump, err)
			os.Exit(2)
		}
		g.dump(f)
		f.Close()
	}
}
func describeDeps() {
	fmt.Println("dependencies for codegraph-rust:")
	for _, d := range []struct{ mod, ver string }{
		{"`tree-sitter` CLI on PATH (or $TREE_SITTER_BIN)", tsRuntimeVersion},
		{"tree-sitter-rust grammar registered with that CLI", "0.24.2"},
	} {
		fmt.Printf("  [ok     ] %-42s %-10s %s\n", d.mod, d.ver, "required")
	}
	fmt.Println("             spawned per file (`tree-sitter parse /dev/stdin --scope")
	fmt.Println("             source.rust --cst`). Nothing is linked in and there is no")
	fmt.Println("             C in this build, and there is no fallback path: a missing")
	fmt.Println("             CLI aborts at startup rather than emitting an empty graph,")
	fmt.Println("             which reads exactly like a clean repository.")
}
func saveGraph(g *Graph, path string) error {
	f, err := os.Create(path)
	if err != nil {
		return err
	}
	defer f.Close()
	bw := bufio.NewWriterSize(f, 1<<20)
	w := &dumpWriter{bw}
	w.line("#codegraph-rust 1")
	w.line("files %d", len(g.Files))
	for i := range g.Files {
		fl := &g.Files[i]
		w.line("f %d %s %d %d %d %d %d %d %d %d %s %d %d %d %d",
			fl.ID, encText(fl.Path()), fl.ModuleID, fl.Bytes, fl.Lines, fl.Sloc,
			fl.Blank, fl.Comment, fl.MaxLine, fl.NParseErrors, encText(fl.SHA1()),
			fl.Parsed, fl.IsTest, fl.IsGenerated, fl.IsVendored, fl.NMissingNodes)
	}
	w.line("modules %d", len(g.Modules))
	for i := range g.Modules {
		m := &g.Modules[i]
		w.line("m %d %s %s %d %d %d %d %d %d %s", m.ID, encText(m.Name()),
			encText(m.Kind()), m.NFiles, m.NSymbols, m.NPublic, m.Sloc, m.FanIn,
			m.FanOut, encFloat(m.Instability))
	}
	w.line("symbols %d", len(g.SymName))
	for i := range g.SymName {
		sid := int32(i + 1)
		cells := make([]string, 0, len(symCols))
		for _, f := range symField {
			switch f {
			case fID:
				cells = append(cells, encInt(sid))
			case fFile:
				cells = append(cells, encInt(g.SymFile[i]))
			case fModule:
				cells = append(cells, encInt(g.SymModule[i]))
			case fParent:
				cells = append(cells, encInt(g.SymParent[i]))
			case fName:
				cells = append(cells, encText(g.SymName[i].Str()))
			case fQual:
				cells = append(cells, encText(g.SymQual[i].Str()))
			case fKind:
				cells = append(cells, encText(g.SymKind[i].Str()))
			case fLineS:
				cells = append(cells, encInt(g.SymLine[i]))
			case fLineE:
				cells = append(cells, encInt(g.SymLineEnd[i]))
			case fNLines:
				cells = append(cells, encInt(g.SymNLines[i]))
			case fByteLo:
				cells = append(cells, encInt(g.SymByteLo[i]))
			case fByteHi:
				cells = append(cells, encInt(g.SymByteHi[i]))
			case fSig:
				cells = append(cells, encText(g.SymSig[i].Str()))
			case fRet:
				cells = append(cells, encText(g.SymRet[i].Str()))
			case fVis:
				cells = append(cells, encText(g.SymVis[i].Str()))
			case fImpl:
				cells = append(cells, encText(g.SymImpl[i].Str()))
			default:
				cells = append(cells, encInt(g.mCol(i, f)))
			}
		}
		w.line("s %s", strings.Join(cells, " "))
	}
	w.line("edges %d", len(g.Edges))
	for i := range g.Edges {
		e := &g.Edges[i]
		w.line("e %d %d %d %d %d %d", e.Caller, e.Callee, e.NCalls, e.SameFile,
			e.SameModule, e.IsSelf)
	}
	w.line("pending %d", len(g.pendSid))
	for i := range g.pendSid {
		w.line("p %d %d %s %s", g.pendSid[i], g.pendLine[i], encText(g.pendName[i]),
			encText(g.pendType[i]))
	}
	return bw.Flush()
}

type dumpWriter struct{ bw *bufio.Writer }

func (d *dumpWriter) line(f string, a ...any) {
	fmt.Fprintf(d.bw, f+"\n", a...)
}

var _ = sort.Strings

type cgStr struct{ Off, Ln uint64 }

const cgExtBase = uint64(1) << 62

var (
	cgArena  []byte
	cgExt    []byte
	cgIntern map[string]cgStr
	cgMu     sync.Mutex
)

func cgPut(s string) cgStr {
	if s == "" {
		return cgStr{}
	}
	cgMu.Lock()
	if v, ok := cgIntern[s]; ok {
		cgMu.Unlock()
		return v
	}
	off := uint64(len(cgArena))
	cgArena = append(cgArena, s...)
	v := cgStr{off, uint64(len(s))}
	if cgIntern == nil {
		cgIntern = make(map[string]cgStr, 1<<16)
	}
	cgIntern[unsafe.String(&cgArena[off], len(s))] = v
	cgMu.Unlock()
	return v
}

func cgPutExt(s string) cgStr {
	cgMu.Lock()
	off := cgExtBase + uint64(len(cgExt))
	cgExt = append(cgExt, s...)
	cgMu.Unlock()
	return cgStr{off, uint64(len(s))}
}

func (s cgStr) Str() string {
	if s.Ln == 0 {
		return ""
	}
	if s.Off >= cgExtBase {
		return unsafe.String(&cgExt[s.Off-cgExtBase], int(s.Ln))
	}
	return unsafe.String(&cgArena[s.Off], int(s.Ln))
}

const cgasMagic = "CGAS"

const (
	cgasVersion  = 3
	cgasHeaderSz = 32
	cgasSecSz    = 24
	cgasNSec     = 46
	cgasArenaLo  = 1 << 20
)

const (
	cgasSecStrings uint32 = 1 + iota
	cgasSecTrees
	cgasSecTreeDir
	cgasSecFiles
	cgasSecModules
	cgasSecMeta
	cgasSecSymFile
	cgasSecSymModule
	cgasSecSymParent
	cgasSecSymLine
	cgasSecSymLineEnd
	cgasSecSymNLines
	cgasSecSymByteLo
	cgasSecSymByteHi
	cgasSecSymName
	cgasSecSymQual
	cgasSecSymKind
	cgasSecSymSig
	cgasSecSymRet
	cgasSecSymVis
	cgasSecSymImpl
	cgasSecMetrics
	cgasSecParams
	cgasSecFields
	cgasSecEnums
	cgasSecEdges
	cgasSecSites
	cgasSecUnres
	cgasSecImports
	cgasSecHaz
	cgasSecAttrs
	cgasSecLits
	cgasSecMark
	cgasSecTraits
	cgasSecImpls
	cgasSecUnsafes
	cgasSecDerives
	cgasSecLifes
	cgasSecBounds
	cgasSecMacros
	cgasSecSecrets
	cgasSecCfgs
	cgasSecAsyncs
	cgasSecDeps
	cgasSecFeats
	cgasSecMetricWide
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
		unsafe.Offsetof(FileRow{}.path),
		unsafe.Offsetof(FileRow{}.dir),
		unsafe.Offsetof(FileRow{}.base),
		unsafe.Offsetof(FileRow{}.ext),
		unsafe.Offsetof(FileRow{}.lang),
		unsafe.Offsetof(FileRow{}.sha1),
	}
	moduleStrOffs = []uintptr{
		unsafe.Offsetof(ModuleRow{}.name),
		unsafe.Offsetof(ModuleRow{}.kind),
	}
	metaStrOffs = []uintptr{
		unsafe.Offsetof(MetaRow{}.key),
		unsafe.Offsetof(MetaRow{}.value),
	}
	paramStrOffs = []uintptr{
		unsafe.Offsetof(ParamRow{}.name),
		unsafe.Offsetof(ParamRow{}.typ),
	}
	fieldStrOffs = []uintptr{
		unsafe.Offsetof(FieldRow{}.name),
		unsafe.Offsetof(FieldRow{}.typ),
		unsafe.Offsetof(FieldRow{}.vis),
	}
	enumStrOffs = []uintptr{
		unsafe.Offsetof(EnumRow{}.name),
		unsafe.Offsetof(EnumRow{}.value),
	}
	unresStrOffs = []uintptr{
		unsafe.Offsetof(UnresRow{}.name),
	}
	importStrOffs = []uintptr{
		unsafe.Offsetof(ImportRow{}.target),
		unsafe.Offsetof(ImportRow{}.alias),
		unsafe.Offsetof(ImportRow{}.kind),
	}
	hazStrOffs = []uintptr{
		unsafe.Offsetof(HazardRow{}.pattern),
		unsafe.Offsetof(HazardRow{}.category),
	}
	attrStrOffs = []uintptr{
		unsafe.Offsetof(AttrRow{}.name),
		unsafe.Offsetof(AttrRow{}.args),
	}
	litStrOffs = []uintptr{
		unsafe.Offsetof(LitRow{}.kind),
		unsafe.Offsetof(LitRow{}.value),
	}
	markStrOffs = []uintptr{
		unsafe.Offsetof(MarkerRow{}.kind),
		unsafe.Offsetof(MarkerRow{}.text),
	}
	traitStrOffs = []uintptr{
		unsafe.Offsetof(TraitRow{}.name),
		unsafe.Offsetof(TraitRow{}.methods),
	}
	implStrOffs = []uintptr{
		unsafe.Offsetof(ImplRow{}.typeName),
		unsafe.Offsetof(ImplRow{}.traitName),
	}
	deriveStrOffs = []uintptr{
		unsafe.Offsetof(DeriveRow{}.name),
	}
	lifeStrOffs = []uintptr{
		unsafe.Offsetof(LifeRow{}.name),
		unsafe.Offsetof(LifeRow{}.kind),
	}
	boundStrOffs = []uintptr{
		unsafe.Offsetof(BoundRow{}.param),
		unsafe.Offsetof(BoundRow{}.bound),
	}
	macroStrOffs = []uintptr{
		unsafe.Offsetof(MacroRow{}.name),
		unsafe.Offsetof(MacroRow{}.kind),
	}
	secretStrOffs = []uintptr{
		unsafe.Offsetof(SecretRow{}.value),
	}
	cfgStrOffs = []uintptr{
		unsafe.Offsetof(CfgRow{}.expr),
		unsafe.Offsetof(CfgRow{}.feature),
	}
	asyncStrOffs = []uintptr{
		unsafe.Offsetof(AsyncRow{}.guards),
		unsafe.Offsetof(AsyncRow{}.expr),
	}
	depStrOffs = []uintptr{
		unsafe.Offsetof(DepRow{}.name),
		unsafe.Offsetof(DepRow{}.version),
	}
	featStrOffs = []uintptr{
		unsafe.Offsetof(FeatRow{}.name),
		unsafe.Offsetof(FeatRow{}.enables),
	}
	strColOffs = []uintptr{0}
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
	fail(unsafe.Sizeof(cgStr{}) == 16, "cgStr must be 16 bytes")
	fail(unsafe.Alignof(cgStr{}) == 8, "cgStr must be 8-aligned")
	fail(cgExtBase%8 == 0, "cgExtBase must stay 8-aligned")
	fail(unsafe.Sizeof(tsRec{}) == tsRecSize, "tsRec must be the 32-byte fixed stride")
	fail(unsafe.Sizeof(cgasHeader{}) == 32, "cgasHeader must be 32 bytes")
	fail(unsafe.Sizeof(cgasSec{}) == 24, "cgasSec must be 24 bytes")
	for _, t := range []reflect.Type{
		reflect.TypeOf(tsRec{}),
		reflect.TypeOf(cgStr{}),
		reflect.TypeOf(FileRow{}),
		reflect.TypeOf(ModuleRow{}),
		reflect.TypeOf(MetaRow{}),
		reflect.TypeOf(ParamRow{}),
		reflect.TypeOf(FieldRow{}),
		reflect.TypeOf(EnumRow{}),
		reflect.TypeOf(EdgeRow{}),
		reflect.TypeOf(SiteRow{}),
		reflect.TypeOf(UnresRow{}),
		reflect.TypeOf(ImportRow{}),
		reflect.TypeOf(HazardRow{}),
		reflect.TypeOf(AttrRow{}),
		reflect.TypeOf(LitRow{}),
		reflect.TypeOf(MarkerRow{}),
		reflect.TypeOf(TraitRow{}),
		reflect.TypeOf(ImplRow{}),
		reflect.TypeOf(UnsafeRow{}),
		reflect.TypeOf(DeriveRow{}),
		reflect.TypeOf(LifeRow{}),
		reflect.TypeOf(BoundRow{}),
		reflect.TypeOf(MacroRow{}),
		reflect.TypeOf(SecretRow{}),
		reflect.TypeOf(CfgRow{}),
		reflect.TypeOf(AsyncRow{}),
		reflect.TypeOf(DepRow{}),
		reflect.TypeOf(FeatRow{}),
		reflect.TypeOf(int32(0)),
		reflect.TypeOf(uint32(0)),
		reflect.TypeOf(uint16(0)),
	} {
		fail(!cgasHasRef(t), t.String()+" must be pointer-free")
	}
	for _, c := range []struct {
		offs []uintptr
		sz   uintptr
		what string
	}{
		{fileStrOffs, unsafe.Sizeof(FileRow{}), "files"},
		{moduleStrOffs, unsafe.Sizeof(ModuleRow{}), "modules"},
		{metaStrOffs, unsafe.Sizeof(MetaRow{}), "meta"},
		{paramStrOffs, unsafe.Sizeof(ParamRow{}), "params"},
		{fieldStrOffs, unsafe.Sizeof(FieldRow{}), "fields"},
		{enumStrOffs, unsafe.Sizeof(EnumRow{}), "enum members"},
		{unresStrOffs, unsafe.Sizeof(UnresRow{}), "unresolved calls"},
		{importStrOffs, unsafe.Sizeof(ImportRow{}), "imports"},
		{hazStrOffs, unsafe.Sizeof(HazardRow{}), "hazards"},
		{attrStrOffs, unsafe.Sizeof(AttrRow{}), "attributes"},
		{litStrOffs, unsafe.Sizeof(LitRow{}), "literals"},
		{markStrOffs, unsafe.Sizeof(MarkerRow{}), "markers"},
		{traitStrOffs, unsafe.Sizeof(TraitRow{}), "traits"},
		{implStrOffs, unsafe.Sizeof(ImplRow{}), "impls"},
		{deriveStrOffs, unsafe.Sizeof(DeriveRow{}), "derives"},
		{lifeStrOffs, unsafe.Sizeof(LifeRow{}), "lifetimes"},
		{boundStrOffs, unsafe.Sizeof(BoundRow{}), "generic bounds"},
		{macroStrOffs, unsafe.Sizeof(MacroRow{}), "macros"},
		{secretStrOffs, unsafe.Sizeof(SecretRow{}), "secret candidates"},
		{cfgStrOffs, unsafe.Sizeof(CfgRow{}), "cfg blocks"},
		{asyncStrOffs, unsafe.Sizeof(AsyncRow{}), "async points"},
		{depStrOffs, unsafe.Sizeof(DepRow{}), "deps"},
		{featStrOffs, unsafe.Sizeof(FeatRow{}), "crate features"},
		{strColOffs, unsafe.Sizeof(cgStr{}), "symbol string columns"},
	} {
		for _, o := range c.offs {
			fail(o+unsafe.Sizeof(cgStr{}) <= c.sz && o%8 == 0,
				c.what+" string field must be 8-aligned and inside the row")
		}
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

func cgasBytes[T any](rows []T) []byte {
	if len(rows) == 0 {
		return nil
	}
	return unsafe.Slice((*byte)(unsafe.Pointer(&rows[0])), len(rows)*int(unsafe.Sizeof(rows[0])))
}

func cgasDecodeRows[T any](mem []byte, off, ln uint64, what string) ([]T, error) {
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

func cgasCheckStrs[T any](rows []T, offs []uintptr, arenaLen uint64, what string) error {
	if len(rows) == 0 {
		return nil
	}
	n := int(unsafe.Sizeof(rows[0]))
	base := unsafe.Pointer(&rows[0])
	for _, f := range offs {
		if f+unsafe.Sizeof(cgStr{}) > uintptr(n) || f%8 != 0 {
			return fmt.Errorf("%s: string field offset %d is outside or misaligned for a %d-byte row",
				what, f, n)
		}
		for i := range rows {
			p := (*cgStr)(unsafe.Pointer(uintptr(base) + uintptr(i*n) + f))
			if p.Off > arenaLen || p.Ln > arenaLen-p.Off {
				return fmt.Errorf("%s: string reference (%d,%d) escapes the string arena (%d bytes)",
					what, p.Off, p.Ln, arenaLen)
			}
		}
	}
	return nil
}

func saveASTFile(g *Graph, path string) (int64, error) {
	cgasGuard()
	cgMu.Lock()
	arena := cgArena
	cgMu.Unlock()
	mWant := len(g.SymName) * metricNarrow
	mwWant := len(g.SymName) * metricWide
	metaRows := make([]MetaRow, 0, len(g.Meta))
	for _, m := range g.Meta {
		if m.Key() != "built_at" {
			metaRows = append(metaRows, m)
		}
	}
	body := make([][]byte, cgasNSec)
	body[cgasSecFiles-1] = cgasBytes(g.Files)
	body[cgasSecModules-1] = cgasBytes(g.Modules)
	body[cgasSecMeta-1] = cgasBytes(metaRows)
	body[cgasSecSymFile-1] = cgasBytes(g.SymFile)
	body[cgasSecSymModule-1] = cgasBytes(g.SymModule)
	body[cgasSecSymParent-1] = cgasBytes(g.SymParent)
	body[cgasSecSymLine-1] = cgasBytes(g.SymLine)
	body[cgasSecSymLineEnd-1] = cgasBytes(g.SymLineEnd)
	body[cgasSecSymNLines-1] = cgasBytes(g.SymNLines)
	body[cgasSecSymByteLo-1] = cgasBytes(g.SymByteLo)
	body[cgasSecSymByteHi-1] = cgasBytes(g.SymByteHi)
	body[cgasSecSymName-1] = cgasBytes(g.SymName)
	body[cgasSecSymQual-1] = cgasBytes(g.SymQual)
	body[cgasSecSymKind-1] = cgasBytes(g.SymKind)
	body[cgasSecSymSig-1] = cgasBytes(g.SymSig)
	body[cgasSecSymRet-1] = cgasBytes(g.SymRet)
	body[cgasSecSymVis-1] = cgasBytes(g.SymVis)
	body[cgasSecSymImpl-1] = cgasBytes(g.SymImpl)
	body[cgasSecParams-1] = cgasBytes(g.Params)
	body[cgasSecFields-1] = cgasBytes(g.Fields)
	body[cgasSecEnums-1] = cgasBytes(g.EnumMembers)
	body[cgasSecEdges-1] = cgasBytes(g.Edges)
	body[cgasSecSites-1] = cgasBytes(g.Callsites)
	body[cgasSecUnres-1] = cgasBytes(g.Unresolved)
	body[cgasSecImports-1] = cgasBytes(g.Imports)
	body[cgasSecHaz-1] = cgasBytes(g.Hazards)
	body[cgasSecAttrs-1] = cgasBytes(g.Attributes)
	body[cgasSecLits-1] = cgasBytes(g.Literals)
	body[cgasSecMark-1] = cgasBytes(g.Markers)
	body[cgasSecTraits-1] = cgasBytes(g.Traits)
	body[cgasSecImpls-1] = cgasBytes(g.Impls)
	body[cgasSecUnsafes-1] = cgasBytes(g.UnsafeBlks)
	body[cgasSecDerives-1] = cgasBytes(g.Derives)
	body[cgasSecLifes-1] = cgasBytes(g.Lifetimes)
	body[cgasSecBounds-1] = cgasBytes(g.GenBounds)
	body[cgasSecMacros-1] = cgasBytes(g.Macros)
	body[cgasSecSecrets-1] = cgasBytes(g.Secrets)
	body[cgasSecCfgs-1] = cgasBytes(g.CfgBlocks)
	body[cgasSecAsyncs-1] = cgasBytes(g.AsyncPoints)
	body[cgasSecDeps-1] = cgasBytes(g.Deps)
	body[cgasSecFeats-1] = cgasBytes(g.Feat)
	body[cgasSecStrings-1] = arena
	stride := uint64(tsRecSize)
	totalRecs := uint64(0)
	for i := range g.astTrees {
		if tr := g.astTrees[i]; tr != nil {
			totalRecs += uint64(len(tr.recs))
		}
	}
	tDir := make([]byte, 12+4*len(g.astTrees))
	cgPutU64(tDir[0:8], 0, stride)
	cgPutU32(tDir[8:12], 0, uint32(len(g.astTrees)))
	for i := range g.astTrees {
		n := uint32(0)
		if tr := g.astTrees[i]; tr != nil {
			n = uint32(len(tr.recs))
		}
		cgPutU32(tDir[12+4*i:], 0, n)
	}
	body[cgasSecTreeDir-1] = tDir
	dir := make([]cgasSec, cgasNSec)
	cur := uint64(cgasHeaderSz) + cgasNSec*cgasSecSz
	for i := range dir {
		cur = (cur + 7) &^ 7
		ln := uint64(len(body[i]))
		if i+1 == int(cgasSecTrees) {
			ln = totalRecs * stride
		} else if i+1 == int(cgasSecMetrics) {
			ln = uint64(mWant) * 2
		} else if i+1 == int(cgasSecMetricWide) {
			ln = uint64(mwWant) * 4
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
	cgPutU64(hdr[24:32], 0, uint64(len(arena)))
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
				if tr == nil || len(tr.recs) == 0 {
					continue
				}
				raw := unsafe.Slice((*byte)(unsafe.Pointer(&tr.recs[0])),
					len(tr.recs)*tsRecSize)
				if _, err := w.Write(raw); err != nil {
					return fail(err)
				}
			}
		} else if i+1 == int(cgasSecMetrics) {
			got := 0
			for bi := range g.M {
				blk := g.M[bi]
				if len(blk) == 0 {
					continue
				}
				if len(blk)%metricNarrow != 0 {
					return 0, fmt.Errorf("metric block %d holds %d ints, not a multiple of %d",
						bi, len(blk), metricNarrow)
				}
				raw := unsafe.Slice((*byte)(unsafe.Pointer(&blk[0])), len(blk)*2)
				if _, err := w.Write(raw); err != nil {
					return fail(err)
				}
				got += len(blk)
			}
			if got != mWant {
				return 0, fmt.Errorf("metric matrix holds %d ints, want %d", got, mWant)
			}
		} else if i+1 == int(cgasSecMetricWide) {
			got := 0
			for bi := range g.MW {
				blk := g.MW[bi]
				if len(blk) == 0 {
					continue
				}
				if len(blk)%metricWide != 0 {
					return 0, fmt.Errorf("wide metric block %d holds %d ints, not a multiple of %d",
						bi, len(blk), metricWide)
				}
				raw := unsafe.Slice((*byte)(unsafe.Pointer(&blk[0])), len(blk)*4)
				if _, err := w.Write(raw); err != nil {
					return fail(err)
				}
				got += len(blk)
			}
			if got != mwWant {
				return 0, fmt.Errorf("wide metric matrix holds %d ints, want %d", got, mwWant)
			}
		} else if len(body[i]) > 0 {
			if _, err := w.Write(body[i]); err != nil {
				return fail(err)
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
	arena := mem[ao : ao+al]
	dec := func(id uint32) (uint64, uint64) {
		return secs[id].Off, secs[id].Len
	}
	decErr := func(err error) (*Graph, error) {
		return nil, bad("%v", err)
	}
	var checks []func() error
	off, ln := dec(cgasSecFiles)
	files, err := cgasDecodeRows[FileRow](mem, off, ln, "files")
	if err != nil {
		return decErr(err)
	}
	checks = append(checks, func() error { return cgasCheckStrs(files, fileStrOffs, al, "files") })
	off, ln = dec(cgasSecModules)
	mods, err := cgasDecodeRows[ModuleRow](mem, off, ln, "modules")
	if err != nil {
		return decErr(err)
	}
	checks = append(checks, func() error { return cgasCheckStrs(mods, moduleStrOffs, al, "modules") })
	off, ln = dec(cgasSecMeta)
	meta, err := cgasDecodeRows[MetaRow](mem, off, ln, "meta")
	if err != nil {
		return decErr(err)
	}
	checks = append(checks, func() error { return cgasCheckStrs(meta, metaStrOffs, al, "meta") })
	off, ln = dec(cgasSecSymFile)
	symFile, err := cgasDecodeRows[int32](mem, off, ln, "symbol file column")
	if err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecSymModule)
	symModule, err := cgasDecodeRows[int32](mem, off, ln, "symbol module column")
	if err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecSymParent)
	symParent, err := cgasDecodeRows[int32](mem, off, ln, "symbol parent column")
	if err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecSymLine)
	symLine, err := cgasDecodeRows[int32](mem, off, ln, "symbol line column")
	if err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecSymLineEnd)
	symLineEnd, err := cgasDecodeRows[int32](mem, off, ln, "symbol line-end column")
	if err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecSymNLines)
	symNLines, err := cgasDecodeRows[int32](mem, off, ln, "symbol nlines column")
	if err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecSymByteLo)
	symByteLo, err := cgasDecodeRows[int32](mem, off, ln, "symbol byte-lo column")
	if err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecSymByteHi)
	symByteHi, err := cgasDecodeRows[int32](mem, off, ln, "symbol byte-hi column")
	if err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecSymName)
	symName, err := cgasDecodeRows[cgStr](mem, off, ln, "symbol name column")
	if err != nil {
		return decErr(err)
	}
	checks = append(checks, func() error { return cgasCheckStrs(symName, strColOffs, al, "symbol name column") })
	off, ln = dec(cgasSecSymQual)
	symQual, err := cgasDecodeRows[cgStr](mem, off, ln, "symbol qual column")
	if err != nil {
		return decErr(err)
	}
	checks = append(checks, func() error { return cgasCheckStrs(symQual, strColOffs, al, "symbol qual column") })
	off, ln = dec(cgasSecSymKind)
	symKind, err := cgasDecodeRows[cgStr](mem, off, ln, "symbol kind column")
	if err != nil {
		return decErr(err)
	}
	checks = append(checks, func() error { return cgasCheckStrs(symKind, strColOffs, al, "symbol kind column") })
	off, ln = dec(cgasSecSymSig)
	symSig, err := cgasDecodeRows[cgStr](mem, off, ln, "symbol sig column")
	if err != nil {
		return decErr(err)
	}
	checks = append(checks, func() error { return cgasCheckStrs(symSig, strColOffs, al, "symbol sig column") })
	off, ln = dec(cgasSecSymRet)
	symRet, err := cgasDecodeRows[cgStr](mem, off, ln, "symbol ret column")
	if err != nil {
		return decErr(err)
	}
	checks = append(checks, func() error { return cgasCheckStrs(symRet, strColOffs, al, "symbol ret column") })
	off, ln = dec(cgasSecSymVis)
	symVis, err := cgasDecodeRows[cgStr](mem, off, ln, "symbol vis column")
	if err != nil {
		return decErr(err)
	}
	checks = append(checks, func() error { return cgasCheckStrs(symVis, strColOffs, al, "symbol vis column") })
	off, ln = dec(cgasSecSymImpl)
	symImpl, err := cgasDecodeRows[cgStr](mem, off, ln, "symbol impl column")
	if err != nil {
		return decErr(err)
	}
	checks = append(checks, func() error { return cgasCheckStrs(symImpl, strColOffs, al, "symbol impl column") })
	n := len(symName)
	for _, c := range []struct {
		what string
		v    int
	}{
		{"file column", len(symFile)},
		{"module column", len(symModule)},
		{"parent column", len(symParent)},
		{"line column", len(symLine)},
		{"line-end column", len(symLineEnd)},
		{"nlines column", len(symNLines)},
		{"byte-lo column", len(symByteLo)},
		{"byte-hi column", len(symByteHi)},
		{"qual column", len(symQual)},
		{"kind column", len(symKind)},
		{"sig column", len(symSig)},
		{"ret column", len(symRet)},
		{"vis column", len(symVis)},
		{"impl column", len(symImpl)},
	} {
		if c.v != n {
			return nil, bad("symbol %s has %d rows, name column has %d", c.what, c.v, n)
		}
	}
	off, ln = dec(cgasSecMetrics)
	mFlat, err := cgasDecodeRows[uint16](mem, off, ln, "metric matrix")
	if err != nil {
		return decErr(err)
	}
	if len(mFlat) != n*metricNarrow {
		return nil, bad("metric matrix holds %d ints, want %d", len(mFlat), n*metricNarrow)
	}
	off, ln = dec(cgasSecMetricWide)
	mwFlat, err := cgasDecodeRows[int32](mem, off, ln, "wide metric matrix")
	if err != nil {
		return decErr(err)
	}
	if len(mwFlat) != n*metricWide {
		return nil, bad("wide metric matrix holds %d ints, want %d", len(mwFlat), n*metricWide)
	}
	off, ln = dec(cgasSecParams)
	params, err := cgasDecodeRows[ParamRow](mem, off, ln, "params")
	if err != nil {
		return decErr(err)
	}
	checks = append(checks, func() error { return cgasCheckStrs(params, paramStrOffs, al, "params") })
	off, ln = dec(cgasSecFields)
	fields, err := cgasDecodeRows[FieldRow](mem, off, ln, "fields")
	if err != nil {
		return decErr(err)
	}
	checks = append(checks, func() error { return cgasCheckStrs(fields, fieldStrOffs, al, "fields") })
	off, ln = dec(cgasSecEnums)
	enums, err := cgasDecodeRows[EnumRow](mem, off, ln, "enum members")
	if err != nil {
		return decErr(err)
	}
	checks = append(checks, func() error { return cgasCheckStrs(enums, enumStrOffs, al, "enum members") })
	off, ln = dec(cgasSecEdges)
	edges, err := cgasDecodeRows[EdgeRow](mem, off, ln, "edges")
	if err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecSites)
	sites, err := cgasDecodeRows[SiteRow](mem, off, ln, "call sites")
	if err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecUnres)
	unres, err := cgasDecodeRows[UnresRow](mem, off, ln, "unresolved calls")
	if err != nil {
		return decErr(err)
	}
	checks = append(checks, func() error { return cgasCheckStrs(unres, unresStrOffs, al, "unresolved calls") })
	off, ln = dec(cgasSecImports)
	imports, err := cgasDecodeRows[ImportRow](mem, off, ln, "imports")
	if err != nil {
		return decErr(err)
	}
	checks = append(checks, func() error { return cgasCheckStrs(imports, importStrOffs, al, "imports") })
	off, ln = dec(cgasSecHaz)
	haz, err := cgasDecodeRows[HazardRow](mem, off, ln, "hazards")
	if err != nil {
		return decErr(err)
	}
	checks = append(checks, func() error { return cgasCheckStrs(haz, hazStrOffs, al, "hazards") })
	off, ln = dec(cgasSecAttrs)
	attrs, err := cgasDecodeRows[AttrRow](mem, off, ln, "attributes")
	if err != nil {
		return decErr(err)
	}
	checks = append(checks, func() error { return cgasCheckStrs(attrs, attrStrOffs, al, "attributes") })
	off, ln = dec(cgasSecLits)
	lits, err := cgasDecodeRows[LitRow](mem, off, ln, "literals")
	if err != nil {
		return decErr(err)
	}
	checks = append(checks, func() error { return cgasCheckStrs(lits, litStrOffs, al, "literals") })
	off, ln = dec(cgasSecMark)
	mark, err := cgasDecodeRows[MarkerRow](mem, off, ln, "markers")
	if err != nil {
		return decErr(err)
	}
	checks = append(checks, func() error { return cgasCheckStrs(mark, markStrOffs, al, "markers") })
	off, ln = dec(cgasSecTraits)
	traits, err := cgasDecodeRows[TraitRow](mem, off, ln, "traits")
	if err != nil {
		return decErr(err)
	}
	checks = append(checks, func() error { return cgasCheckStrs(traits, traitStrOffs, al, "traits") })
	off, ln = dec(cgasSecImpls)
	impls, err := cgasDecodeRows[ImplRow](mem, off, ln, "impls")
	if err != nil {
		return decErr(err)
	}
	checks = append(checks, func() error { return cgasCheckStrs(impls, implStrOffs, al, "impls") })
	off, ln = dec(cgasSecUnsafes)
	unsafes, err := cgasDecodeRows[UnsafeRow](mem, off, ln, "unsafe blocks")
	if err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecDerives)
	derives, err := cgasDecodeRows[DeriveRow](mem, off, ln, "derives")
	if err != nil {
		return decErr(err)
	}
	checks = append(checks, func() error { return cgasCheckStrs(derives, deriveStrOffs, al, "derives") })
	off, ln = dec(cgasSecLifes)
	lifes, err := cgasDecodeRows[LifeRow](mem, off, ln, "lifetimes")
	if err != nil {
		return decErr(err)
	}
	checks = append(checks, func() error { return cgasCheckStrs(lifes, lifeStrOffs, al, "lifetimes") })
	off, ln = dec(cgasSecBounds)
	bounds, err := cgasDecodeRows[BoundRow](mem, off, ln, "generic bounds")
	if err != nil {
		return decErr(err)
	}
	checks = append(checks, func() error { return cgasCheckStrs(bounds, boundStrOffs, al, "generic bounds") })
	off, ln = dec(cgasSecMacros)
	macros, err := cgasDecodeRows[MacroRow](mem, off, ln, "macros")
	if err != nil {
		return decErr(err)
	}
	checks = append(checks, func() error { return cgasCheckStrs(macros, macroStrOffs, al, "macros") })
	off, ln = dec(cgasSecSecrets)
	secrets, err := cgasDecodeRows[SecretRow](mem, off, ln, "secret candidates")
	if err != nil {
		return decErr(err)
	}
	checks = append(checks, func() error { return cgasCheckStrs(secrets, secretStrOffs, al, "secret candidates") })
	off, ln = dec(cgasSecCfgs)
	cfgs, err := cgasDecodeRows[CfgRow](mem, off, ln, "cfg blocks")
	if err != nil {
		return decErr(err)
	}
	checks = append(checks, func() error { return cgasCheckStrs(cfgs, cfgStrOffs, al, "cfg blocks") })
	off, ln = dec(cgasSecAsyncs)
	asyncs, err := cgasDecodeRows[AsyncRow](mem, off, ln, "async points")
	if err != nil {
		return decErr(err)
	}
	checks = append(checks, func() error { return cgasCheckStrs(asyncs, asyncStrOffs, al, "async points") })
	off, ln = dec(cgasSecDeps)
	deps, err := cgasDecodeRows[DepRow](mem, off, ln, "deps")
	if err != nil {
		return decErr(err)
	}
	checks = append(checks, func() error { return cgasCheckStrs(deps, depStrOffs, al, "deps") })
	off, ln = dec(cgasSecFeats)
	feats, err := cgasDecodeRows[FeatRow](mem, off, ln, "crate features")
	if err != nil {
		return decErr(err)
	}
	checks = append(checks, func() error { return cgasCheckStrs(feats, featStrOffs, al, "crate features") })
	tOff, tLn := secs[cgasSecTrees].Off, secs[cgasSecTrees].Len
	dOff, dLn := secs[cgasSecTreeDir].Off, secs[cgasSecTreeDir].Len
	if dLn < 12 {
		return nil, bad("node record directory too small (%d bytes)", dLn)
	}
	dirBytes := unsafe.Slice((*byte)(unsafe.Pointer(uintptr(unsafe.Pointer(&mem[0]))+uintptr(dOff))), int(dLn))
	declStride := cgGetU64(dirBytes, 0)
	nTreeFiles := int(cgGetU32(dirBytes, 8))
	if declStride != tsRecSize {
		return nil, bad("node record stride %d, want %d", declStride, tsRecSize)
	}
	if nTreeFiles != len(files) {
		return nil, bad("node record directory covers %d files, graph has %d", nTreeFiles, len(files))
	}
	if int(dLn) < 12+4*nTreeFiles {
		return nil, bad("node record directory too small for %d files", nTreeFiles)
	}
	var counts []uint32
	if nTreeFiles > 0 {
		counts = unsafe.Slice((*uint32)(unsafe.Pointer(&dirBytes[12])), nTreeFiles)
	}
	if tLn%tsRecSize != 0 {
		return nil, bad("node record arena length %d is not a multiple of the record stride", tLn)
	}
	recsAll := unsafe.Slice((*tsRec)(unsafe.Pointer(uintptr(unsafe.Pointer(&mem[0]))+uintptr(tOff))), int(tLn/tsRecSize))
	astTrees := make([]*tsTree, nTreeFiles)
	base := 0
	for i := 0; i < nTreeFiles; i++ {
		cnt := int(counts[i])
		if base+cnt > len(recsAll) {
			return nil, bad("node record directory overruns the record arena")
		}
		if cnt > 0 {
			tr := &tsTree{recs: recsAll[base : base+cnt]}
			tr.index(&tsParser{})
			astTrees[i] = tr
		}
		base += cnt
	}
	if base != len(recsAll) {
		return nil, bad("node record arena has %d unused records", len(recsAll)-base)
	}
	if len(checks) > 0 {
		for _, c := range checks {
			if err := c(); err != nil {
				return decErr(err)
			}
		}
	}
	g := &Graph{}
	g.Files = files
	g.Modules = mods
	g.Meta = meta
	g.SymFile = symFile
	g.SymModule = symModule
	g.SymParent = symParent
	g.SymLine = symLine
	g.SymLineEnd = symLineEnd
	g.SymNLines = symNLines
	g.SymByteLo = symByteLo
	g.SymByteHi = symByteHi
	g.SymName = symName
	g.SymQual = symQual
	g.SymKind = symKind
	g.SymSig = symSig
	g.SymRet = symRet
	g.SymVis = symVis
	g.SymImpl = symImpl
	g.M = make([][]uint16, 0, len(mFlat)/(mBlockSyms*metricNarrow)+1)
	for o := 0; o < len(mFlat); o += mBlockSyms * metricNarrow {
		e := o + mBlockSyms*metricNarrow
		if e > len(mFlat) {
			e = len(mFlat)
		}
		g.M = append(g.M, mFlat[o:e])
	}
	g.MW = make([][]int32, 0, len(mwFlat)/(mBlockSyms*metricWide)+1)
	for o := 0; o < len(mwFlat); o += mBlockSyms * metricWide {
		e := o + mBlockSyms*metricWide
		if e > len(mwFlat) {
			e = len(mwFlat)
		}
		g.MW = append(g.MW, mwFlat[o:e])
	}
	g.Params = params
	g.Fields = fields
	g.EnumMembers = enums
	g.Edges = edges
	g.Callsites = sites
	g.Unresolved = unres
	g.Imports = imports
	g.Hazards = haz
	g.Attributes = attrs
	g.Literals = lits
	g.Markers = mark
	g.Traits = traits
	g.Impls = impls
	g.UnsafeBlks = unsafes
	g.Derives = derives
	g.Lifetimes = lifes
	g.GenBounds = bounds
	g.Macros = macros
	g.Secrets = secrets
	g.CfgBlocks = cfgs
	g.AsyncPoints = asyncs
	g.Deps = deps
	g.Feat = feats
	g.astTrees = astTrees
	cgMu.Lock()
	cgArena = arena
	cgExt = nil
	cgMu.Unlock()
	metaAll := make([]MetaRow, len(g.Meta)+1)
	copy(metaAll, g.Meta)
	metaAll[len(g.Meta)] = MetaRow{key: cgPutExt("built_at"),
		value: cgPutExt(time.Now().Format("2006-01-02T15:04:05"))}
	g.Meta = metaAll
	g.finishDerived()
	return g, nil
}
