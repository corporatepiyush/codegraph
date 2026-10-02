package main

import (
	"bufio"
	"bytes"
	"crypto/sha1"
	"encoding/hex"
	"encoding/json/jsontext"
	"flag"
	"fmt"
	"io"
	"io/fs"
	"math"
	"math/big"
	"os"
	"os/exec"
	"path/filepath"
	"reflect"
	"regexp"
	"runtime"
	"runtime/debug"
	"runtime/pprof"
	"slices"
	"sort"
	"strconv"
	"strings"
	"sync"
	"sync/atomic"
	"syscall"
	"time"
	"unicode"
	"unicode/utf8"
	"unsafe"
)

type jv struct {
	kind byte
	str  string
	b    bool
	keys []string
	vals []*jv
}

func (v *jv) get(key string) *jv {
	if v == nil || v.kind != 'o' {
		return nil
	}
	for i, k := range v.keys {
		if k == key {
			return v.vals[i]
		}
	}
	return nil
}

func parseJSONTree(path string) (*jv, error) {
	data, err := os.ReadFile(path)
	if err != nil {
		return nil, err
	}
	dec := jsontext.NewDecoder(bytes.NewReader(data))
	return readJV(dec)
}

func readJV(dec *jsontext.Decoder) (*jv, error) {
	tok, err := dec.ReadToken()
	if err != nil {
		return nil, err
	}
	switch tok.Kind() {
	case jsontext.KindBeginObject:
		obj := &jv{kind: 'o'}
		for {
			nt, err := dec.ReadToken()
			if err != nil {
				return nil, err
			}
			if nt.Kind() == jsontext.KindEndObject {
				break
			}

			name := nt.String()
			val, err := readJV(dec)
			if err != nil {
				return nil, err
			}
			obj.keys = append(obj.keys, name)
			obj.vals = append(obj.vals, val)
		}
		return obj, nil
	case jsontext.KindBeginArray:
		arr := &jv{kind: 'a'}
		for dec.PeekKind() != jsontext.KindEndArray {
			val, err := readJV(dec)
			if err != nil {
				return nil, err
			}
			arr.vals = append(arr.vals, val)
		}
		_, err = dec.ReadToken()
		return arr, err
	case jsontext.KindString:

		return &jv{kind: 's', str: tok.String()}, nil
	case jsontext.KindTrue, jsontext.KindFalse:
		return &jv{kind: 'b', b: tok.Kind() == jsontext.KindTrue}, nil
	case jsontext.KindNull:
		return &jv{kind: 'z'}, nil
	default:
		return &jv{kind: 'n', str: tok.String()}, nil
	}
}

type symRow struct {
	name string

	named, visible, supe bool
}

type tsTables struct {
	syms       []symRow
	fields     []string
	anonField  []uint16
	symNamed   []bool
	symVisible []bool
	symSuper   []bool
	symPublic  []uint16
	symNames   []string
	fieldNames []string
}

func buildKindTables(gd string) (*tsTables, error) {
	nodeTypes, err := parseJSONTree(filepath.Join(gd, "src", "node-types.json"))
	if err != nil {
		return nil, err
	}
	grammar, err := parseJSONTree(filepath.Join(gd, "src", "grammar.json"))
	if err != nil {
		return nil, err
	}

	out := &tsTables{}

	seenField := map[string]bool{}
	addField := func(name string) {
		if name != "" && !seenField[name] {
			seenField[name] = true
			out.fields = append(out.fields, name)
		}
	}

	type kfEntry struct {
		name     string
		anonOnly bool
	}
	kindFields := map[string][]kfEntry{}
	var order []string
	inOrder := map[string]bool{}
	typeOf := func(e *jv) string {
		if t := e.get("type"); t != nil && t.kind == 's' {
			return t.str
		}
		return ""
	}

	for _, e := range nodeTypes.vals {
		name := typeOf(e)
		if !inOrder[name] {
			inOrder[name] = true
			order = append(order, name)
		}
		kf := kindFields[name]
		fl := e.get("fields")
		if fl != nil && fl.kind == 'o' {
			for i, fname := range fl.keys {
				addField(fname)

				anonOnly := false
				if types := fl.vals[i].get("types"); types != nil && types.kind == 'a' && len(types.vals) > 0 {
					anonOnly = true
					for _, tv := range types.vals {
						named := true
						if nv := tv.get("named"); nv != nil && nv.kind == 'b' {
							named = nv.b
						}
						if named {
							anonOnly = false
						}
					}
				}
				idx := -1
				for j := range kf {
					if kf[j].name == fname {
						idx = j
						break
					}
				}
				if idx < 0 {
					kf = append(kf, kfEntry{name: fname, anonOnly: anonOnly})
				} else {
					kf[idx].anonOnly = kf[idx].anonOnly && anonOnly
				}
			}
		}
		kindFields[name] = kf
	}

	nested := map[string]bool{}
	for _, e := range nodeTypes.vals {
		stack := []*jv{e.get("fields"), e.get("children"), e.get("subtypes")}
		for len(stack) > 0 {
			obj := stack[len(stack)-1]
			stack = stack[:len(stack)-1]
			switch {
			case obj == nil:
			case obj.kind == 'o':
				t := obj.get("type")
				nm := obj.get("named")
				if t != nil && t.kind == 's' && nm != nil && nm.kind == 'b' {
					nested[t.str] = true
				}
				stack = append(stack, obj.vals...)
			case obj.kind == 'a':
				stack = append(stack, obj.vals...)
			}
		}
	}
	nestSorted := make([]string, 0, len(nested))
	for name := range nested {
		nestSorted = append(nestSorted, name)
	}
	sort.Strings(nestSorted)
	for _, name := range nestSorted {
		if _, ok := kindFields[name]; !ok {
			kindFields[name] = nil
			order = append(order, name)
		}
	}

	namedOf := map[string]bool{}
	haveNamed := map[string]bool{}
	for _, e := range nodeTypes.vals {
		name := typeOf(e)
		if !haveNamed[name] {
			haveNamed[name] = true
			named := true
			if nv := e.get("named"); nv != nil && nv.kind == 'b' {
				named = nv.b
			}
			namedOf[name] = named
		}
	}
	seen := map[string]bool{}
	for _, name := range order {
		seen[name] = true
		named := true
		if haveNamed[name] {
			named = namedOf[name]
		}
		out.syms = append(out.syms, symRow{name: name, named: named, visible: true})
	}
	if st := grammar.get("supertypes"); st != nil && st.kind == 'a' {
		for _, sv := range st.vals {
			if !seen[sv.str] {
				seen[sv.str] = true
				out.syms = append(out.syms, symRow{name: sv.str, named: true, supe: true})
			} else {
				for i := range out.syms {
					if out.syms[i].name == sv.str {
						out.syms[i].supe = true
					}
				}
			}
		}
	}
	out.syms = append(out.syms, symRow{name: "ERROR", named: true, visible: true})
	out.syms = append(out.syms, symRow{name: "\x00MISSING", named: true, visible: true})

	fidByID := map[string]uint16{}
	for i, f := range out.fields {
		fidByID[f] = uint16(i + 1)
	}
	for _, s := range out.syms {
		fid := uint16(0)
		for _, kf := range kindFields[s.name] {
			if kf.anonOnly {
				fid = fidByID[kf.name]
				break
			}
		}
		out.anonField = append(out.anonField, fid)
	}

	for _, s := range out.syms {
		out.symNamed = append(out.symNamed, s.named)
		out.symVisible = append(out.symVisible, s.visible)
		out.symSuper = append(out.symSuper, s.supe)
		out.symNames = append(out.symNames, s.name)
	}
	for i := range out.syms {
		out.symPublic = append(out.symPublic, uint16(i))
	}
	out.fieldNames = append([]string{""}, out.fields...)
	return out, nil
}

func grammarSourceDir() string {
	base := os.Getenv("TREE_SITTER_GRAMMARS")
	if base == "" {
		home, err := os.UserHomeDir()
		if err != nil {
			fmt.Fprintf(os.Stderr, "codegraph_python: cannot resolve home: %v\n", err)
			os.Exit(1)
		}
		base = filepath.Join(home, ".cache", "codegraph", "grammars")
	}
	return filepath.Join(base, "tree-sitter-python")
}

var kindTables = mustBuildKindTables()

func mustBuildKindTables() *tsTables {
	dir := grammarSourceDir()
	if _, err := os.Stat(filepath.Join(dir, "src", "node-types.json")); err != nil {
		fmt.Fprintf(os.Stderr, "codegraph_python: tree-sitter-python grammar sources not found at %s\n"+
			"  run: git clone --depth 1 --branch v0.25.0 https://github.com/tree-sitter/tree-sitter-python %s\n", dir, dir)
		os.Exit(1)
	}
	t, err := buildKindTables(dir)
	if err != nil {
		fmt.Fprintf(os.Stderr, "codegraph_python: %v\n", err)
		os.Exit(1)
	}
	return t
}

var (
	tsAbiVersion = 0
	tsSymCount   = len(kindTables.syms)
	tsFieldCount = len(kindTables.fields) + 1

	tsSymNamed   = kindTables.symNamed
	tsSymVisible = kindTables.symVisible
	tsSymSuper   = kindTables.symSuper
	tsSymPublic  = kindTables.symPublic
	tsSymNames   = kindTables.symNames
	tsFieldNames = kindTables.fieldNames
	tsAnonField  = kindTables.anonField
)

const tsScope = "source.python"

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
	bin    string
	env    []string
	outBuf []byte
	bigBuf []byte
}

func tsParserNew() *tsParser {
	bin := tsCLIBin()
	if _, err := os.Stat(bin); err != nil {
		panic("tree-sitter CLI not found at " + bin + " -- install it or point TREE_SITTER_BIN at it")
	}
	return &tsParser{bin: bin, env: append(os.Environ(), "NO_COLOR=1", "TERM=dumb")}
}

func (p *tsParser) free() {}

type tsTemp struct {
	dir   string
	paths []string
}

func newTSTemp() *tsTemp {
	d, err := os.MkdirTemp("", "cgpy-cst-")
	if err != nil {
		return &tsTemp{}
	}
	return &tsTemp{dir: d}
}

func (t *tsTemp) close() {
	if t.dir == "" {
		return
	}
	for _, p := range t.paths {
		os.Remove(p)
	}
	os.RemoveAll(t.dir)
}

func (t *tsTemp) stage(recs []*sourceFile) bool {
	if t.dir == "" {
		return false
	}
	for i, r := range recs {
		p := filepath.Join(t.dir, strconv.Itoa(i))
		if err := os.WriteFile(p, r.data, 0o600); err != nil {
			for _, q := range t.paths[:i] {
				os.Remove(q)
			}
			t.paths = t.paths[:0]
			return false
		}
		t.paths = append(t.paths, p)
	}
	return true
}

func (t *tsTemp) discard() {
	for _, p := range t.paths {
		os.Remove(p)
	}
	t.paths = t.paths[:0]
}

func (p *tsParser) startPaths(paths []string) (*os.File, func()) {
	args := make([]string, 0, len(paths)+7)
	args = append(args, "parse")
	args = append(args, paths...)
	args = append(args, "--scope", tsScope, "--cst", "--time")
	cmd := exec.Command(p.bin, args...)
	cmd.Env = p.env
	cmd.Stderr = nil
	outR, outW, err := os.Pipe()
	if err != nil {
		return nil, nil
	}
	cmd.Stdout = outW
	if serr := cmd.Start(); serr != nil {
		outR.Close()
		outW.Close()
		return nil, nil
	}
	outW.Close()
	return outR, func() {
		outR.Close()
		cmd.Wait()
	}
}

func isCSTMarker(line []byte, want string) bool {
	if len(line) == 0 || (line[0] >= '0' && line[0] <= '9') {
		return false
	}
	tab := bytes.IndexByte(line, '\t')
	if tab < 0 {
		return false
	}
	return string(bytes.TrimRight(line[:tab], " ")) == want
}

const cstBufRetain = 1 << 20

func (p *tsParser) grow(n int) {
	if cap(p.outBuf) >= n {
		return
	}
	if n > cstBufRetain {
		if cap(p.bigBuf) < n {
			p.bigBuf = make([]byte, n+n/2)
		}
		p.outBuf = p.bigBuf[:copy(p.bigBuf, p.outBuf)]
		return
	}
	c := 2 * cap(p.outBuf)
	if c < n {
		c = n
	}
	nb := make([]byte, len(p.outBuf), c)
	copy(nb, p.outBuf)
	p.outBuf = nb
}

func (p *tsParser) parse(src []byte) *tsTree {
	cmd := exec.Command(p.bin, "parse", "/dev/stdin", "--scope", tsScope, "--cst")
	cmd.Env = p.env
	cmd.Stderr = nil
	inR, inW, err := os.Pipe()
	if err != nil {
		return nil
	}
	outR, outW, err := os.Pipe()
	if err != nil {
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
	go func() {
		inW.Write(src)
		inW.Close()
	}()
	need := 24 * len(src)
	if need > 1<<20 {
		need = 1 << 20
	}
	if cap(p.outBuf) < need {
		p.outBuf = make([]byte, need+4096)
	}
	out := p.outBuf[:0]
	rerr := error(nil)
	for {
		n, e := outR.Read(out[len(out):cap(out)])
		out = out[:len(out)+n]
		if e != nil {
			rerr = e
			break
		}
		if len(out) == cap(out) {
			var rest []byte
			rest, rerr = io.ReadAll(outR)
			out = append(out, rest...)
			break
		}
	}
	werr := inW.Close()
	err = cmd.Wait()
	outR.Close()
	if err != nil && len(out) == 0 {
		return nil
	}
	if rerr != nil && rerr != io.EOF && len(out) == 0 {
		return nil
	}
	_ = werr
	t, derr := decodeCST(out, src)
	if derr != nil {
		panic(fmt.Sprintf("cli cst decode failed: %v", derr))
	}
	// Leave the scratch buffer empty. decodeCST has copied everything it
	// needs; a non-empty p.outBuf here would be scanned as already-buffered
	// CLI output by the next batch reader and silently mis-attribute blocks.
	p.outBuf = p.outBuf[:0]
	return t
}

type tsTree struct {
	recs []tsRec
}

func (t *tsTree) free() { t.recs = nil }

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

func sameNode(a, b tsNode) bool { return a.t == b.t && a.i == b.i }

func kindID(n tsNode) uint16 {
	if !hasNode(n) {
		return kNoNode
	}
	s := n.t.recs[n.i].sym
	if s == tsSymInvalid {
		return kErrID
	}
	if int(s) < len(kindIDCache.canon) {
		return kindIDCache.canon[s]
	}
	return s
}

func startByte(n tsNode) uint { return uint(n.t.recs[n.i].start) }
func endByte(n tsNode) uint {
	if !hasNode(n) {
		return 0
	}
	return uint(n.t.recs[n.i].end)
}
func startRow(n tsNode) int { return int(n.t.recs[n.i].srow) }
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

func nextNamedSibling(n tsNode) tsNode {
	if !hasNode(n) {
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

func langSymbolCount() int { return tsSymCount }

func langSymbolName(id uint16) string {
	if int(id) < len(tsSymNames) {
		return tsSymNames[id]
	}
	return ""
}

func symLookup(name string, named bool) uint16 {
	if len(name) <= 5 && "ERROR"[:len(name)] == name {
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

func firstChildN(n tsNode) tsNode {
	if !hasNode(n) || n.t.recs[n.i].subEnd == n.i+1 {
		return tsNode{}
	}
	return tsNode{t: n.t, i: n.i + 1}
}

func nextSiblingOf(n tsNode) tsNode {
	if !hasNode(n) {
		return tsNode{}
	}
	pi := n.t.recs[n.i].parent
	if pi < 0 {
		return tsNode{}
	}
	sib := n.t.recs[n.i].subEnd
	if sib >= n.t.recs[pi].subEnd {
		return tsNode{}
	}
	return tsNode{t: n.t, i: sib}
}

func callFunc(n tsNode) tsNode {
	fn := fieldNode(n, fFunction)
	switch kindID(fn) {
	case kListSplat, kDictSplat:
		return firstNamed(fn)
	}
	return fn
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

func decodeCST(out, src []byte) (*tsTree, error) {
	starts := make([]int, 1, bytes.Count(src, []byte{'\n'})+1)
	for i, b := range src {
		if b == '\n' {
			starts = append(starts, i+1)
		}
	}
	d := &cstDecoder{starts: starts, total: len(src)}

	recs := make([]tsRec, 0, bytes.Count(out, []byte{'\n'})+1)
	type frame struct {
		i   int32
		end uint32
	}
	var stack []frame

	nextFresh := uint16(len(tsSymByID) + 0x4000)
	freshIDs := make(map[string]uint16, 16)
	internB := func(b []byte) uint16 {
		if id, ok := tsSymByID[string(b)]; ok {
			return id
		}
		if id, ok := freshIDs[string(b)]; ok {
			return id
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
			par := stack[len(stack)-1].i
			recs[idx].parent = par

			if !named {
				if s := recs[par].sym; int(s) < len(tsAnonField) {
					if f := tsAnonField[s]; f != 0 {
						recs[idx].field = f
					}
				}
			}
		}
		stack = append(stack, frame{i: idx, end: end})
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

	for i := range recs {
		if int(recs[i].sym) >= len(tsAnonField) {
			continue
		}
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
	return &tsTree{recs: recs}, nil
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

func kindOf(name string) uint16 {
	cs, ok := kindIDCache.nameToID[name]
	if !ok {
		panic("tree-sitter-python has no node kind " + name)
	}
	return cs
}

var (
	kModule = kindOf("module")

	kFunctionDef   = kindOf("function_definition")
	kClassDef      = kindOf("class_definition")
	kDecoratedDef  = kindOf("decorated_definition")
	kDecorator     = kindOf("decorator")
	kBlock         = kindOf("block")
	kExprStmt      = kindOf("expression_statement")
	kAssignment    = kindOf("assignment")
	kAugAssignment = kindOf("augmented_assignment")
	kReturnStmt    = kindOf("return_statement")
	kDeleteStmt    = kindOf("delete_statement")
	kForStmt       = kindOf("for_statement")
	kWhileStmt     = kindOf("while_statement")
	kIfStmt        = kindOf("if_statement")
	kElifClause    = kindOf("elif_clause")
	kElseClause    = kindOf("else_clause")
	kWithStmt      = kindOf("with_statement")
	kWithClause    = kindOf("with_clause")
	kWithItem      = kindOf("with_item")
	kAsPattern     = kindOf("as_pattern")
	kAsPatternTgt  = kindOf("as_pattern_target")
	kTryStmt       = kindOf("try_statement")
	kExceptClause  = kindOf("except_clause")
	kFinallyClause = kindOf("finally_clause")
	kMatchStmt     = kindOf("match_statement")
	kCaseClause    = kindOf("case_clause")
	kRaiseStmt     = kindOf("raise_statement")
	kAssertStmt    = kindOf("assert_statement")
	kImportStmt    = kindOf("import_statement")
	kImportFrom    = kindOf("import_from_statement")
	kFutureImport  = kindOf("future_import_statement")
	kAliasedImport = kindOf("aliased_import")
	kDottedName    = kindOf("dotted_name")
	kRelativeImp   = kindOf("relative_import")
	kImportPrefix  = kindOf("import_prefix")
	kWildcardImp   = kindOf("wildcard_import")
	kGlobalStmt    = kindOf("global_statement")
	kNonlocalStmt  = kindOf("nonlocal_statement")
	kPassStmt      = kindOf("pass_statement")

	kIdentifier = kindOf("identifier")
	kAttribute  = kindOf("attribute")
	kSubscript  = kindOf("subscript")
	kSlice      = kindOf("slice")
	kCall       = kindOf("call")
	kArgList    = kindOf("argument_list")
	kKeywordArg = kindOf("keyword_argument")
	kListSplat  = kindOf("list_splat")
	kDictSplat  = kindOf("dictionary_splat")

	kBinaryOp  = kindOf("binary_operator")
	kUnaryOp   = kindOf("unary_operator")
	kNotOp     = kindOf("not_operator")
	kBoolOp    = kindOf("boolean_operator")
	kCompareOp = kindOf("comparison_operator")

	kCondExpr = kindOf("conditional_expression")
	kLambda   = kindOf("lambda")
	kLambdaPs = kindOf("lambda_parameters")
	kParams   = kindOf("parameters")

	kPosSeparator      = kindOf("positional_separator")
	kKwSeparator       = kindOf("keyword_separator")
	kStarParam         = kindOf("list_splat_pattern")
	kDStarParam        = kindOf("dictionary_splat_pattern")
	kTypedParam        = kindOf("typed_parameter")
	kDefaultParam      = kindOf("default_parameter")
	kTypedDefaultParam = kindOf("typed_default_parameter")

	kList         = kindOf("list")
	kTuple        = kindOf("tuple")
	kSet          = kindOf("set")
	kDictionary   = kindOf("dictionary")
	kPair         = kindOf("pair")
	kExprList     = kindOf("expression_list")
	kParenExpr    = kindOf("parenthesized_expression")
	kPatternList  = kindOf("pattern_list")
	kClassPattern = kindOf("class_pattern")

	kListComp = kindOf("list_comprehension")
	kSetComp  = kindOf("set_comprehension")
	kDictComp = kindOf("dictionary_comprehension")
	kGenExp   = kindOf("generator_expression")
	kForIn    = kindOf("for_in_clause")
	kIfClause = kindOf("if_clause")

	kYield         = kindOf("yield")
	kAwait         = kindOf("await")
	kNamedExpr     = kindOf("named_expression")
	kString        = kindOf("string")
	kStringStart   = kindOf("string_start")
	kStringContent = kindOf("string_content")
	kInterpolation = kindOf("interpolation")
	kFormatExpr    = kindOf("format_expression")
	kConcatString  = kindOf("concatenated_string")

	kInteger      = kindOf("integer")
	kFloat        = kindOf("float")
	kTrue         = kindOf("true")
	kFalse        = kindOf("false")
	kNone         = kindOf("none")
	kEllipsis     = kindOf("ellipsis")
	kComment      = kindOf("comment")
	kType         = kindOf("type")
	kTypeParam    = kindOf("type_parameter")
	kTypeAlias    = kindOf("type_alias_statement")
	kGenericType  = kindOf("generic_type")
	kUnionType    = kindOf("union_type")
	kTuplePattern = kindOf("tuple_pattern")
	kListPattern  = kindOf("list_pattern")

	kErrID  uint16 = 0xFFFE
	kNoNode uint16 = 0xFFFF
)

var (
	fName        = fieldID("name")
	fBody        = fieldID("body")
	fParameters  = fieldID("parameters")
	fReturnType  = fieldID("return_type")
	fTypeParams  = fieldID("type_parameters")
	fSuperclass  = fieldID("superclasses")
	fDefinition  = fieldID("definition")
	fLeft        = fieldID("left")
	fRight       = fieldID("right")
	fCondition   = fieldID("condition")
	fConsequence = fieldID("consequence")
	fValue       = fieldID("value")
	fType        = fieldID("type")
	fFunction    = fieldID("function")
	fArguments   = fieldID("arguments")
	fObject      = fieldID("object")
	fAttribute   = fieldID("attribute")
	fOperator    = fieldID("operator")
	fAlias       = fieldID("alias")
	fModuleName  = fieldID("module_name")
	fFormatSpec  = fieldID("format_specifier")
)

type kindTab struct {
	idToName []string
	canon    []uint16
	nameToID map[string]uint16
}

var kindIDCache = func() *kindTab {
	n := langSymbolCount()
	t := &kindTab{idToName: make([]string, n), canon: make([]uint16, n),
		nameToID: make(map[string]uint16, n)}
	for s := range n {
		id := uint16(s)
		nm := langSymbolName(id)
		t.idToName[s] = nm
		first, ok := t.nameToID[nm]
		if !ok {
			t.nameToID[nm] = id
			t.canon[s] = id
		} else {
			t.canon[s] = first
		}
	}

	t.nameToID["ERROR"] = kErrID
	return t
}()

func kindName(n tsNode) string {
	id := kindID(n)
	if id == kNoNode {
		return "<null>"
	}
	if int(id) < len(kindIDCache.idToName) {
		return kindIDCache.idToName[id]
	}
	return "?"
}

func nodeText(src []byte, n tsNode) string {
	if !hasNode(n) {
		return ""
	}
	s, e := startByte(n), endByte(n)
	if s > e || e > uint(len(src)) {
		return ""
	}
	return string(src[s:e])
}

func forEachNamed(n tsNode, fn func(tsNode)) {
	if !hasNode(n) {
		return
	}
	for c := firstChildN(n); hasNode(c); c = nextSiblingOf(c) {
		if isNamedN(c) && kindID(c) != kComment {
			fn(c)
		}
	}
}

func firstChildOfKind(n tsNode, k uint16) tsNode {
	var out tsNode
	forEachNamed(n, func(c tsNode) {
		if !hasNode(out) && kindID(c) == k {
			out = c
		}
	})
	return out
}

func childIsToken(n tsNode, i int, tok string, src []byte) bool {
	c := childAt(n, i)
	if !hasNode(c) || isNamedN(c) {
		return false
	}
	s, e := startByte(c), endByte(c)
	if e > uint(len(src)) || e-s != uint(len(tok)) {
		return false
	}
	return string(src[s:e]) == tok
}

func isAsync(n tsNode, src []byte) bool { return childIsToken(n, 0, "async", src) }

func eachNamedChild(n tsNode, fn func(tsNode)) {
	switch kindID(n) {
	case kDecoratedDef:
		if d := fieldNode(n, fDefinition); hasNode(d) {
			fn(d)
		}
		forEachNamed(n, func(c tsNode) {
			if kindID(c) == kDecorator {
				fn(c)
			}
		})
		return
	case kCondExpr:

		var kids []tsNode
		forEachNamed(n, func(c tsNode) { kids = append(kids, c) })
		if len(kids) == 3 {
			fn(kids[1])
			fn(kids[0])
			fn(kids[2])
			return
		}
		for _, c := range kids {
			fn(c)
		}
		return
	}
	forEachNamed(n, fn)
}

var skipDirs = map[string]bool{
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

	".eggs": true, "migrations": true,
}

var generatedMarkers = []string{
	"@generated", "DO NOT EDIT", "Code generated by", "AUTO-GENERATED",
	"autogenerated", "This file was automatically generated",
	"Generated by the protocol buffer compiler", "@flow-generated",
}

var generatedNameRE = regexp.MustCompile(`(?i)(\.min\.|\.bundle\.|[-_.](gen|generated|pb|g)\.|_pb2|\.g\.dart$|\.designer\.|^zz_generated)`)

var testPathRE = regexp.MustCompile(`(?i)(^|/)(tests?|test-d|spec|specs|__tests__|__snapshots__|testing|e2e|integration[-_]tests?|testdata|test_data|test-data|fixtures?)(/|$)`)

var testNameRE = regexp.MustCompile(`(^test_|_test\.py$|^conftest\.py$)`)

var vendorPathRE = regexp.MustCompile(`(?i)(^|/)(vendor|third_party|thirdparty|external|node_modules|deps)(/|$)`)

var exampleDirRE = regexp.MustCompile(`(?i)(^|/)(examples?|samples?|demos?)(/|$)`)
var toolDirRE = regexp.MustCompile(`(?i)(^|/)(tools?|scripts?|cmd|bin)(/|$)`)

var markerRE = regexp.MustCompile(`(?i)\b(TODO|FIXME|XXX|HACK|BUG|NOTE|WARNING|OPTIMIZE|REVIEW|DEPRECATED|SAFETY|PANIC|UNSAFE)\b[ \t]*[:\-(\[]`)

const cgSpace = `[\t\n\v\f\r\x1C-\x1F\p{Zs}]`

var noqaRE = regexp.MustCompile(`(?i)#` + cgSpace +
	`*(noqa|type:` + cgSpace + `*ignore|pragma:` + cgSpace + `*no` + cgSpace +
	`*cover|pyright:` + cgSpace + `*ignore)\b`)

var commentPrefixes = []string{"//", "#", "/*", "*", "*/", `"""`, "'''", "--", ";;", "%"}

const (
	maxFileBytes = 4 * 1024 * 1024
	maxLineBytes = 1024 * 1024
)

func moduleOf(rel string) string {
	parts := strings.Split(filepath.ToSlash(rel), "/")
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
	case testPathRE.MatchString(name):
		return "test"
	case vendorPathRE.MatchString(name):
		return "vendor"
	case exampleDirRE.MatchString(name):
		return "example"
	case toolDirRE.MatchString(name):
		return "tool"
	}
	return "source"
}

func isGeneratedFile(name, head string) bool {
	if generatedNameRE.MatchString(name) {
		return true
	}
	for _, m := range generatedMarkers {
		if strings.Contains(head, m) {
			return true
		}
	}
	return false
}

type sourceFile struct {
	fid     int32
	mid     int32
	rel     string
	abspath string
	text    string
	data    []byte
	sloc    int32
	isTest  bool
	isGen   bool
}

func (g *Graph) discover(root string, includeTests, includeGen, includeVendored, quiet bool) []*sourceFile {
	realRoot, err := filepath.EvalSymlinks(root)
	if err != nil {
		realRoot = root
	}
	var out []*sourceFile
	skipped := map[string]int{}
	var walk func(dir, rel string)
	walk = func(dir, rel string) {
		entries, err := os.ReadDir(dir)
		if err != nil {
			skipped["walk_errors"]++
			return
		}
		var dirs, files []string
		for _, e := range entries {
			n := e.Name()
			if e.IsDir() {
				if skipDirs[n] || strings.HasPrefix(n, ".") {
					continue
				}
				dirs = append(dirs, n)
				continue
			}
			files = append(files, n)
		}
		sort.Strings(dirs)
		sort.Strings(files)
		for _, n := range files {
			ext := filepath.Ext(n)
			if ext != ".py" && ext != ".pyi" && ext != ".pyw" {
				continue
			}
			full := filepath.Join(dir, n)
			r := n
			if rel != "" {
				r = rel + "/" + n
			}
			g.scanOne(full, r, &out, skipped, realRoot,
				includeTests, includeGen, includeVendored)
		}
		for _, n := range dirs {
			sub := n
			if rel != "" {
				sub = rel + "/" + n
			}
			walk(filepath.Join(dir, n), sub)
		}
	}
	walk(root, "")

	if !quiet {
		labels := [][2]string{
			{"big", "too large or with a pathologically long line -- catalogued, not parsed"},
			{"special", "not regular files (fifo, socket, device) -- skipped"},
			{"escape", "symlinks pointing OUTSIDE the tree -- skipped"},
			{"denied", "unreadable (permission denied)"},
			{"walk_errors", "director(ies) could not be listed"},
		}
		for _, l := range labels {
			if n := skipped[l[0]]; n > 0 {
				printfLn("  %d %s", n, l[1])
			}
		}
	}
	g.setMeta("files_skipped", sprintf(
		"big=%d special=%d escaping_symlink=%d denied=%d walk_errors=%d",
		skipped["big"], skipped["special"], skipped["escape"],
		skipped["denied"], skipped["walk_errors"]))
	return out
}

func (g *Graph) scanOne(full, rel string, out *[]*sourceFile, skipped map[string]int,
	realRoot string, includeTests, includeGen, includeVendored bool) {

	st, err := os.Lstat(full)
	if err != nil {
		return
	}
	if st.Mode()&os.ModeSymlink != 0 {
		st, err = os.Stat(full)
		if err != nil {
			return
		}
	}
	if !st.Mode().IsRegular() {
		skipped["special"]++
		return
	}
	if resolved, err := filepath.EvalSymlinks(full); err == nil {
		if resolved != full && !strings.HasPrefix(resolved, realRoot+string(filepath.Separator)) {
			skipped["escape"]++
			return
		}
	}
	tooBig := false
	var data []byte
	if st.Size() > maxFileBytes {
		skipped["big"]++
		tooBig = true
	} else {
		data, err = os.ReadFile(full)
		if err != nil {
			if os.IsPermission(err) {
				skipped["denied"]++
			}
			return
		}
	}
	text := ""
	if !tooBig {
		text = string(data)
	}
	if !tooBig && data != nil {
		if longestLine(data) > maxLineBytes {
			skipped["big"]++
			tooBig = true
		}
	}
	lines := splitLines(text)
	var blank, cmt, sloc, maxLen int32
	for _, l := range lines {
		if n := int32(cgStrLen(l)); n > maxLen {
			maxLen = n
		}
		if cgIsSpace(l) {
			blank++
			continue
		}
		if isCommentLine(cgLstrip(l)) {
			cmt++
		}
		sloc++
	}
	isTest := testPathRE.MatchString(rel) || testNameRE.MatchString(filepath.Base(rel))
	head := ""
	if len(text) > 2000 {
		head = text[:2000]
	} else {
		head = text
	}
	isGen := isGeneratedFile(filepath.Base(rel), head)
	isVend := vendorPathRE.MatchString(rel)
	mid := g.addModule(moduleOf(rel), moduleKind(moduleOf(rel)))
	fid := g.addFile(rel)
	sum := ""
	if len(data) > 0 {
		h := sha1.Sum(data)
		sum = hex.EncodeToString(h[:])
	}
	parse := !tooBig && text != "" &&
		(includeTests || !isTest) && (includeGen || !isGen) && (includeVendored || !isVend)
	f := &File{
		ID: fid, ModuleID: mid, Path: g.I(rel),
		Dir:      g.I(filepath.Dir(rel)),
		Basename: g.I(filepath.Base(rel)),
		Ext:      g.I(filepath.Ext(rel)),
		Bytes:    int32(st.Size()), Lines: int32(len(lines)), SLOC: sloc,
		BlankLines: blank, CommentLines: cmt, MaxLineLen: maxLen,
		SHA1: g.I(sum), Parsed: b2i(parse), IsTest: b2i(isTest),
		IsGenerated: b2i(isGen), IsVendored: b2i(isVend),
	}
	g.Files[fid-1] = *f
	if parse {
		*out = append(*out, &sourceFile{fid: fid, mid: mid, rel: rel, abspath: full,
			text: text, data: data, sloc: sloc, isTest: isTest, isGen: isGen})
	}
}

func b2i(b bool) int8 {
	if b {
		return 1
	}
	return 0
}

func isCommentLine(t string) bool {
	if len(t) > 3 {
		t = t[:3]
	}
	return slices.Contains(commentPrefixes, t)
}

func cgIsSpace(l string) bool {
	if l == "" {
		return true
	}
	for _, r := range l {
		if r == 0x1c || r == 0x1d || r == 0x1e || r == 0x1f {
			continue
		}
		if !unicode.IsSpace(r) {
			return false
		}
	}
	return true
}

func cgLstrip(l string) string {
	for len(l) > 0 {
		r, size := utf8.DecodeRuneInString(l)
		if r == 0x1c || r == 0x1d || r == 0x1e || r == 0x1f || unicode.IsSpace(r) {
			l = l[size:]
			continue
		}
		break
	}
	return l
}

func cgStrLen(s string) int {
	n := 0
	for i := 0; i < len(s); {
		b := s[i]
		if b < 0x80 {
			i++
			n++
			continue
		}
		var need int
		var lo, hi byte = 0x80, 0xbf
		switch {
		case b >= 0xc2 && b <= 0xdf:
			need = 1
		case b >= 0xe0 && b <= 0xef:
			need = 2
			if b == 0xe0 {
				lo = 0xa0
			} else if b == 0xed {
				hi = 0x9f
			}
		case b >= 0xf0 && b <= 0xf4:
			need = 3
			if b == 0xf0 {
				lo = 0x90
			} else if b == 0xf4 {
				hi = 0x8f
			}
		default:

			i++
			n++
			continue
		}
		j := i
		k := 0
		for k < need {
			j++
			if j >= len(s) {

				return n + 1
			}
			c := s[j]
			if k == 0 {
				if c < lo || c > hi {
					break
				}
			} else if c < 0x80 || c > 0xbf {
				break
			}
			k++
		}
		n++
		if k == need {
			i = j + 1
		} else {
			i = j
		}
	}
	return n
}

func longestLine(data []byte) int {
	longest, start := 0, 0
	for i := range data {
		if data[i] == '\n' {
			if i-start > longest {
				longest = i - start
			}
			start = i + 1
		}
	}
	if len(data)-start > longest {
		longest = len(data) - start
	}
	return longest
}

func splitLines(s string) []string {
	if s == "" {
		return nil
	}
	out := make([]string, 0, strings.Count(s, "\n")+1)
	start := 0
	for i := 0; i < len(s); {
		r, size := utf8.DecodeRuneInString(s[i:])
		if !isLineBreak(r) {
			i += size
			continue
		}
		out = append(out, s[start:i])
		i += size
		if r == '\r' && i < len(s) && s[i] == '\n' {
			i++
		}
		start = i
	}
	if start < len(s) {
		out = append(out, s[start:])
	}
	return out
}

func isLineBreak(r rune) bool {
	switch r {
	case '\n', '\r', '\v', '\f', 0x1c, 0x1d, 0x1e, 0x85, 0x2028, 0x2029:
		return true
	}
	return false
}

var _ = fs.WalkDir

func asciiFold(c byte) byte {
	if c >= 'A' && c <= 'Z' {
		return c + 32
	}
	return c
}

func isWordByte(c byte) bool {
	return c == '_' || (c >= '0' && c <= '9') || (c >= 'a' && c <= 'z') ||
		(c >= 'A' && c <= 'Z') || c >= 0x80
}

type matcher struct {
	words  []string
	first  [256]bool
	anySet bool
}

func newMatcher(words []string, anySet bool) *matcher {
	m := &matcher{words: words, anySet: anySet}
	for _, w := range words {
		if w == "" {
			continue
		}
		m.first[w[0]] = true
		m.first[asciiFold(w[0])] = true
	}
	return m
}

func matchAt(s string, i int, w string) bool {
	if i+len(w) > len(s) {
		return false
	}
	for k := 0; k < len(w); k++ {
		if asciiFold(s[i+k]) != w[k] {
			return false
		}
	}
	return true
}

func (m *matcher) match(s string) bool {
	if !m.anySet {

		for i := 0; i < len(s); i++ {
			if !m.first[asciiFold(s[i])] {
				continue
			}
			if i > 0 && isWordByte(s[i-1]) {
				continue
			}
			if !isWordByte(s[i]) {
				continue
			}
			for _, w := range m.words {
				if !matchAt(s, i, w) {
					continue
				}
				if i+len(w) < len(s) && isWordByte(s[i+len(w)]) {
					continue
				}
				return true
			}
		}
		return false
	}
	for i := 0; i < len(s); i++ {
		if !m.first[asciiFold(s[i])] {
			continue
		}
		for _, w := range m.words {
			if matchAt(s, i, w) {
				return true
			}
		}
	}
	return false
}

var sqlKeywordRE = newMatcher([]string{
	"select", "insert", "update", "delete", "create", "drop", "alter", "union",
}, false)

var sqlTails = map[string][][]string{
	"insert": {{"into"}},
	"delete": {{"from"}},
	"create": {{"table"}},
	"drop":   {{"table"}},
	"alter":  {{"table"}},
	"union":  {{"all", "select"}, {"select"}},
}

func sqlKeywordHit(s string) bool {
	for i := 0; i < len(s); i++ {
		c := s[i]
		if !sqlKeywordRE.first[asciiFold(c)] {
			continue
		}

		if i > 0 && isWordByte(s[i-1]) {
			continue
		}
		for _, w := range sqlKeywordRE.words {
			if !matchAt(s, i, w) {
				continue
			}

			j := i + len(w)
			if j < len(s) && isWordByte(s[j]) {
				continue
			}
			tails, ok := sqlTails[w]
			if !ok {

				return true
			}
			for _, alt := range tails {
				if sqlTailMatches(s, j, alt) {
					return true
				}
			}
		}
	}
	return false
}

func sqlTailMatches(s string, j int, alt []string) bool {
	k := j
	for _, w := range alt {
		for k < len(s) && isSQLSpace(s[k]) {
			k++
		}
		if k == j {
			return false
		}
		if !matchAt(s, k, w) {
			return false
		}
		k += len(w)
		j = k
	}
	return k >= len(s) || !isWordByte(s[k])
}

func isSQLSpace(c byte) bool {
	switch c {
	case ' ', '\t', '\n', '\r', '\f', '\v':
		return true
	}
	return false
}

var secretKeywords = newMatcher([]string{
	"api_key", "apikey", "api-key", "secret", "password", "passwd", "pwd",
	"token", "bearer", "access_key", "access-key", "private_key", "private-key",
	"client_secret", "client-secret", "auth_token", "auth-token", "jwt",
	"credential", "smtp_pass", "smtp-pass", "db_pass", "db-pass", "sk_live",
	"rk_live", "pk_live", "ghp_", "xoxb-", "akia",
}, true)

func secretKeywordHit(s string) bool { return secretKeywords.match(s) }

var _ = strings.EqualFold

func (g *Graph) extractParsed(pr parseResult) bool {
	rec, root, src, srcLines, err := pr.rec, pr.root, pr.src, pr.lines, pr.err
	if pr.tree != nil {
		if g.keepTrees && rec.fid >= 1 {
			kept := make([]tsRec, len(pr.tree.recs))
			copy(kept, pr.tree.recs)
			for int(rec.fid) > len(g.astTrees) {
				g.astTrees = append(g.astTrees, nil)
			}
			g.astTrees[rec.fid-1] = kept
		}
		defer pr.tree.free()
	}
	if err != nil {

		g.Files[rec.fid-1].ParseErrors++
		if !isSyntaxErr(err) {
			g.Files[rec.fid-1].Parsed = 0
			return false
		}
		g.markersOf(rec, srcLines)
		return false
	}
	g.Files[rec.fid-1].DocLines = int32(docstringLines(src, root))
	g.importsOf(root, src, rec)
	g.moduleVarsOf(root, src, rec)

	g.markersOf(rec, srcLines)
	g.walkScope(root, src, rec, srcLines, -1, "", nil, 0)
	g.moduleScope(root, src, rec, srcLines)
	return true
}

var parserPool = sync.Pool{New: func() any { return tsParserNew() }}

func getParser() *tsParser  { return parserPool.Get().(*tsParser) }
func putParser(p *tsParser) { parserPool.Put(p) }

// parseSourceP is the per-file stdin invocation, for one batch file at a time.
// The caller owns p, so a parallel worker reuses its own parser instead of
// churning through the pool.
func parseSourceP(p *tsParser, rec *sourceFile) (*tsTree, tsNode, []string, error) {
	lines := splitLines(rec.text)
	t := p.parse(rec.data)
	if t == nil {
		return nil, tsNode{}, lines, &parseErr{msg: "parse failed"}
	}
	root := t.root()
	if hasErr(root) {

		t.free()
		return nil, tsNode{}, lines, &parseErr{msg: "tree-sitter error node"}
	}
	return t, root, lines, nil
}

const batchSourceBytes = 4 << 20
const batchMaxFiles = 512

// CG_PIPELINE=1 prints a wall/reader/decoder/extract split so the reader side
// of the parse pipeline can be told apart from the graph-building side.
var cgPipeline = os.Getenv("CG_PIPELINE") != ""

var (
	pipeReadWait atomic.Int64
	pipeStage    atomic.Int64
	pipeDecode   atomic.Int64
	pipeExtract  atomic.Int64
)

// parseBatchDecode parses one contiguous batch with the caller's own parser
// and temp directory and returns exactly one parseResult per file, in file
// order, without touching the graph. A file whose CST block does not decode
// (and every file after it in the batch) falls back to a per-file stdin
// invocation, matching the serial reader's behaviour byte for byte.
//
// When sink is non-nil each result is handed over the moment it is decoded,
// so the serial reader extracts inline and never holds a batch of trees;
// otherwise the results are collected in file order for the reorder buffer.
func parseBatchDecode(p *tsParser, tmp *tsTemp, batch []*sourceFile,
	sink func(parseResult)) []parseResult {
	var items []parseResult
	emit := func(pr parseResult) {
		if sink != nil {
			sink(pr)
			return
		}
		items = append(items, pr)
	}
	var st time.Time
	if cgPipeline {
		st = time.Now()
	}
	okStage := tmp.stage(batch)
	if cgPipeline {
		pipeStage.Add(int64(time.Since(st)))
	}
	if !okStage {
		tmp.discard()
		appendPerFile(emit, p, batch, 0)
		return items
	}
	rd, done := p.startPaths(tmp.paths)
	if rd == nil {
		tmp.discard()
		appendPerFile(emit, p, batch, 0)
		return items
	}
	used := 0
	scan := 0
	readErr := false
	stop := false
	next := 0
	// The scan below treats everything in p.outBuf as this batch's CLI output;
	// any bytes left from a previous stdin invocation would be attributed to
	// the first file and the endByte clamp would hide the mismatch.
	p.outBuf = p.outBuf[:0]
	for !readErr && !stop {
		for scan < len(p.outBuf) {
			nl := bytes.IndexByte(p.outBuf[scan:], '\n')
			if nl < 0 {
				break
			}
			if next < len(batch) && isCSTMarker(p.outBuf[scan:scan+nl], tmp.paths[next]) {
				pr, ok := decodeBlock(p.outBuf[used:scan], batch[next])
				if !ok {
					stop = true
					break
				}
				emit(pr)
				batch[next].text, batch[next].data = "", nil
				next++
				used = scan + nl + 1
			}
			scan += nl + 1
		}
		if readErr || stop {
			break
		}
		if used > 0 {
			n := copy(p.outBuf, p.outBuf[used:scan])
			p.outBuf = p.outBuf[:n]
			scan -= used
			used = 0
		}
		if cap(p.outBuf)-len(p.outBuf) < 1<<16 {
			p.grow(len(p.outBuf) + (1 << 16))
		}
		var rs time.Time
		if cgPipeline {
			rs = time.Now()
		}
		k, err := rd.Read(p.outBuf[len(p.outBuf):cap(p.outBuf)])
		if cgPipeline {
			pipeReadWait.Add(int64(time.Since(rs)))
		}
		p.outBuf = p.outBuf[:len(p.outBuf)+k]
		if err != nil {
			readErr = true
		}
	}
	done()
	// Release the read buffer between batches. A worker farm multiplies any
	// retained big buffer by the worker count, and a single huge file (a 41k
	// line literal) grows it to tens of MB; the residency is not worth the
	// one realloc it saves on a later batch.
	if p.bigBuf != nil {
		p.bigBuf = nil
		p.outBuf = make([]byte, 0, cstBufRetain)
	} else {
		p.outBuf = p.outBuf[:0]
	}
	appendPerFile(emit, p, batch, next)
	tmp.discard()
	return items
}

// appendPerFile parses batch[from:] one file per CLI invocation and hands each
// result to emit. Every file must reach emit exactly once: a dropped result
// would drop every symbol in that file from the graph without a trace.
func appendPerFile(emit func(parseResult), p *tsParser, batch []*sourceFile, from int) {
	for i := from; i < len(batch); i++ {
		rec := batch[i]
		tree, root, lines, err := parseSourceP(p, rec)
		emit(parseResult{rec: rec, tree: tree, root: root,
			src: rec.data, lines: lines, err: err})
		rec.text, rec.data = "", nil
	}
}

func (g *Graph) parseSerial(recs []*sourceFile, quiet bool) (failed, syntax int) {
	n := len(recs)
	step := n / 20
	if step < 1 {
		step = 1
	}
	tmp := newTSTemp()
	defer tmp.close()
	p := getParser()
	defer putParser(p)
	for lo := 0; lo < n; {
		hi := lo
		sum := 0
		for hi < n && hi-lo < batchMaxFiles {
			sz := len(recs[hi].data)
			if hi > lo && sum+sz > batchSourceBytes {
				break
			}
			sum += sz
			hi++
		}
		parseBatchDecode(p, tmp, recs[lo:hi], func(pr parseResult) {
			if !g.extractTimed(pr) {
				if pr.err != nil && isSyntaxErr(pr.err) {
					syntax++
				} else {
					failed++
				}
			}
		})
		if !quiet && hi%step == 0 {
			printfLn("  ... %d/%d files", hi, n)
		}
		lo = hi
	}
	return failed, syntax
}

// decodeBlock turns one CST block into a parse result without touching the
// graph. Extraction happens later, in file order, on the consumer side; this
// separation is what lets the batch readers run in parallel.
func decodeBlock(blk []byte, rec *sourceFile) (parseResult, bool) {
	if cgPipeline {
		t0 := time.Now()
		defer func() { pipeDecode.Add(int64(time.Since(t0))) }()
	}
	t, derr := decodeCST(blk, rec.data)
	if derr != nil {
		return parseResult{}, false
	}
	if endByte(t.root()) != uint(len(rec.data)) {
		t.free()
		return parseResult{}, false
	}
	lines := splitLines(rec.text)
	if hasErr(t.root()) {
		t.free()
		return parseResult{rec: rec, lines: lines,
			err: &parseErr{msg: "tree-sitter error node"}}, true
	}
	return parseResult{rec: rec, tree: t, root: t.root(),
		src: rec.data, lines: lines}, true
}

// extractTimed is the single extraction entry point for both consumers.
func (g *Graph) extractTimed(pr parseResult) bool {
	if cgPipeline {
		t0 := time.Now()
		defer func() { pipeExtract.Add(int64(time.Since(t0))) }()
	}
	return g.extractParsed(pr)
}

// maxParseWorkers is the project-wide fan-out ceiling; more children than this
// stop paying for themselves on a typical 4-10 core laptop.
const maxParseWorkers = 8

func defaultParseWorkers() int {
	n := runtime.GOMAXPROCS(0)
	if n > maxParseWorkers {
		n = maxParseWorkers
	}
	if n < 1 {
		n = 1
	}
	return n
}

func (g *Graph) parseAndExtract(recs []*sourceFile, workers int, quiet bool) (failed, syntax int) {
	if workers < 1 {
		workers = 1
	}
	if workers == 1 || len(recs) == 0 {
		return g.parseSerial(recs, quiet)
	}
	if workers > len(recs) {
		workers = len(recs)
	}
	return g.parseParallel(recs, workers, quiet)
}

// Parallel batch sizes. Smaller than the serial reader's 4 MB/512 because more
// batches are what let the workers balance; the child startup (~10 ms) is
// amortised over hundreds of KB of source.
const (
	parBatchSourceBytes = 256 << 10
	parBatchMaxFiles    = 64
)

type parseBatchSpan struct{ lo, hi int }

func planParseBatches(recs []*sourceFile) []parseBatchSpan {
	var out []parseBatchSpan
	for lo := 0; lo < len(recs); {
		hi := lo
		sum := 0
		for hi < len(recs) && hi-lo < parBatchMaxFiles {
			sz := len(recs[hi].data)
			if hi > lo && sum+sz > parBatchSourceBytes {
				break
			}
			sum += sz
			hi++
		}
		out = append(out, parseBatchSpan{lo, hi})
		lo = hi
	}
	return out
}

type parseFarmResult struct {
	idx   int
	items []parseResult
}

// parseParallel runs the batch decode on N workers, each with its own CLI
// parser and staging directory, and extracts the results strictly in file
// order on this goroutine. Parse completion order therefore never reaches the
// graph: symbol ids and the dump are invariant under the worker count.
//
// A token is held from the start of a batch until that batch has been
// extracted in order, which bounds how many decoded CST buffers (and staged
// inputs) can be alive at once.
func (g *Graph) parseParallel(recs []*sourceFile, workers int, quiet bool) (failed, syntax int) {
	n := len(recs)
	batches := planParseBatches(recs)
	if len(batches) == 0 {
		return 0, 0
	}
	if workers > len(batches) {
		workers = len(batches)
	}
	step := n / 20
	if step < 1 {
		step = 1
	}

	// Batches are pulled in index order. That is what keeps the token protocol
	// deadlock-free: the batch the consumer is waiting for (emit) was always
	// pulled before any of the other in-flight batches, so one worker is
	// always making progress on it. A longest-processing-time order was tried
	// and deadlocks when emit's batch is scheduled after the tokens run out.
	var nextBatch atomic.Int64
	results := make(chan parseFarmResult, workers)
	tokens := make(chan struct{}, workers)
	var wg sync.WaitGroup
	for w := 0; w < workers; w++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			p := getParser()
			defer putParser(p)
			tmp := newTSTemp()
			defer tmp.close()
			for {
				bi := int(nextBatch.Add(1)) - 1
				if bi >= len(batches) {
					return
				}
				tokens <- struct{}{}
				sp := batches[bi]
				items := parseBatchDecode(p, tmp, recs[sp.lo:sp.hi], nil)
				results <- parseFarmResult{idx: bi, items: items}
			}
		}()
	}
	go func() {
		wg.Wait()
		close(results)
	}()

	pending := make(map[int][]parseResult, workers)
	emit := 0
	done := 0
	for res := range results {
		pending[res.idx] = res.items
		for {
			items, ok := pending[emit]
			if !ok {
				break
			}
			delete(pending, emit)
			if sp := batches[emit]; len(items) != sp.hi-sp.lo {

				panic(fmt.Sprintf("parse pipeline: batch %d produced %d results for %d files",
					emit, len(items), sp.hi-sp.lo))
			}
			emit++
			for i := range items {
				pr := &items[i]
				if !g.extractTimed(*pr) {
					if pr.err != nil && isSyntaxErr(pr.err) {
						syntax++
					} else {
						failed++
					}
				}
				done++
				if !quiet && done%step == 0 {
					printfLn("  ... %d/%d files", done, n)
				}
			}
			<-tokens
		}
	}
	if emit != len(batches) {

		panic(fmt.Sprintf("parse pipeline lost %d of %d batches", len(batches)-emit, len(batches)))
	}
	return failed, syntax
}

type parseResult struct {
	rec   *sourceFile
	tree  *tsTree
	root  tsNode
	src   []byte
	lines []string
	err   error
}

type parseErr struct {
	msg string
}

func (e *parseErr) Error() string { return "SyntaxError: " + e.msg }

func isSyntaxErr(err error) bool {
	switch err.(type) {
	case *parseErr:
		return true
	}
	return false
}

func (g *Graph) markersOf(rec *sourceFile, lines []string) {
	for i, line := range lines {
		hash := strings.ContainsRune(line, '#')
		if !(hash || strings.Contains(line, "//") || strings.ContainsRune(line, '*') ||
			strings.Contains(line, "--")) {
			continue
		}
		if m := markerRE.FindStringSubmatch(line); m != nil {
			g.Markers = append(g.Markers, Marker{
				ID: int32(len(g.Markers) + 1), FileID: rec.fid, SymbolID: -1,
				Kind: g.I(strings.ToUpper(m[1])), Line: int32(i + 1),
				Text: g.opt(truncStr(strings.TrimSpace(line), 200))})
		}
		if hash {
			if m := noqaRE.FindStringSubmatch(line); m != nil {
				g.Markers = append(g.Markers, Marker{
					ID: int32(len(g.Markers) + 1), FileID: rec.fid, SymbolID: -1,
					Kind: g.I(strings.ToUpper(m[1])), Line: int32(i + 1),
					Text: g.opt(truncStr(strings.TrimSpace(line), 200))})
			}
		}
	}
}

func (g *Graph) importsOf(tree tsNode, src []byte, rec *sourceFile) {
	alias := g.aliases[rec.fid]
	if alias == nil {
		alias = make(map[string]string, 8)
		g.aliases[rec.fid] = alias
	}
	type pending struct {
		fid                  int32
		target, asname, kind uint32
		line                 int32
		external, relative   int32
		wildcard, typeOnly   int32
		nNames               int32
	}
	var rows []pending
	hasIf := false

	walkNamedBFS(tree, src, func(n tsNode) {
		switch kindID(n) {
		case kIfStmt:
			hasIf = true
		case kImportStmt:
			forEachNamed(n, func(a tsNode) {
				name, asname := importAlias(src, a)
				local := asname
				if local == "" {
					local = firstSegment(name)
				}
				alias[local] = name
				rows = append(rows, pending{fid: rec.fid, target: g.I(name),
					asname: g.opt(asname), kind: g.I("import"), line: line1(n),
					external: b2i32(g.isExternalModule(name)),
					nNames:   1})
				if cat, ok := hazardImports[firstSegment(name)]; ok {
					g.recordImportHazard(rec.fid, firstSegment(name), cat, line1(n))
				}
			})
		case kImportFrom, kFutureImport:
			mod := ""
			rel := 0
			if kindID(n) == kFutureImport {

				mod = "__future__"
			} else if mn := fieldNode(n, fModuleName); hasNode(mn) {
				switch kindID(mn) {
				case kDottedName:
					mod = nodeText(src, mn)
				case kRelativeImp:
					forEachNamed(mn, func(c tsNode) {
						switch kindID(c) {
						case kImportPrefix:
							rel += strings.Count(nodeText(src, c), ".")
						case kDottedName:
							mod = nodeText(src, c)
						}
					})
				}
			} else {
				break
			}
			wildcard := int32(0)
			nNames := int32(0)
			modNode := fieldNode(n, fModuleName)
			forEachNamed(n, func(a tsNode) {
				if sameNode(a, modNode) {
					return
				}
				switch kindID(a) {
				case kDottedName, kAliasedImport, kWildcardImp:
				default:
					return
				}
				nNames++
				if kindID(a) == kWildcardImp {
					wildcard = 1
					return
				}
				name, asname := importAlias(src, a)
				local := asname
				if local == "" {
					local = name
				}
				if mod != "" {
					alias[local] = mod + "." + name
				} else {
					alias[local] = name
				}
			})
			ext := b2i32(rel == 0 && g.isExternalModule(mod))
			rows = append(rows, pending{
				fid: rec.fid, target: g.I(strings_Repeat(".", rel) + mod),
				kind: g.I("from"), line: line1(n), external: ext,
				relative: b2i32(rel > 0), wildcard: wildcard,
				typeOnly: b2i32(mod == "typing"),
				nNames:   nNames})
			if cat, ok := hazardImports[firstSegment(mod)]; ok {
				g.recordImportHazard(rec.fid, firstSegment(mod), cat, line1(n))
			}
		}
	})
	for _, r := range rows {
		if r.typeOnly == 1 {
			r.typeOnly = b2i32(hasIf)
		}
		g.Imports = append(g.Imports, Import{
			ID: int32(len(g.Imports) + 1), FileID: r.fid, Target: r.target,
			TargetID: -1, Alias: r.asname, Kind: r.kind, Line: r.line,
			IsExternal: r.external, IsRelative: r.relative,
			IsWildcard: r.wildcard, IsTypeOnly: r.typeOnly, NNames: r.nNames})
	}
}

func importAlias(src []byte, a tsNode) (string, string) {
	if kindID(a) == kDottedName {
		return nodeText(src, a), ""
	}
	if kindID(a) == kAliasedImport {
		name := ""
		forEachNamed(a, func(c tsNode) {
			if kindID(c) == kDottedName {
				name = nodeText(src, c)
			}
		})
		return name, nodeText(src, fieldNode(a, fAlias))
	}
	return "", ""
}

func (g *Graph) recordImportHazard(fid int32, root, cat string, line int32) {
	g.hazardImports = append(g.hazardImports, importHazard{fid: fid, root: root, cat: cat, line: line})
}

func firstSegment(s string) string {
	if before, _, ok := strings.Cut(s, "."); ok {
		return before
	}
	return s
}

func (g *Graph) isExternalModule(mod string) bool {
	if mod == "" {
		return false
	}
	head := firstSegment(mod)
	if g.cgHeads == nil {
		heads := make(map[string]bool, 256)
		segs := make(map[string]bool, 256)
		for p := range g.fileByPath {
			parts := strings.Split(p, "/")
			if len(parts) == 0 {
				continue
			}
			b := parts[len(parts)-1]
			if strings.HasSuffix(b, ".py") {
				for i := 0; i+3 <= len(b); i++ {
					if b[i:] == ".py" {
						continue
					}
					if strings.HasSuffix(b[i:], ".py") {
						heads[b[i:len(b)-3]] = true
					}
				}
			}
			for _, part := range parts[1:] {
				segs[part] = true
			}
		}
		g.cgHeads = heads
		g.segments = segs
	}
	return !g.cgHeads[head] && !g.segments[head]
}

func assignOf(st tsNode) tsNode {
	if kindID(st) != kExprStmt {
		return tsNode{}
	}
	inner := firstNamed(st)
	switch kindID(inner) {
	case kAssignment, kAugAssignment:
		return inner
	}
	return tsNode{}
}

func assignValue(n tsNode) tsNode {
	for hasNode(n) && kindID(n) == kAssignment {
		r := fieldNode(n, fRight)
		if kindID(r) != kAssignment {
			return r
		}
		n = r
	}
	return tsNode{}
}

func assignTargets(src []byte, n tsNode) []tsNode {
	var out []tsNode
	for hasNode(n) && kindID(n) == kAssignment {
		if l := fieldNode(n, fLeft); hasNode(l) {
			out = append(out, unwrapTarget(src, l))
		}
		n = fieldNode(n, fRight)
	}
	return out
}

func unwrapTarget(src []byte, n tsNode) tsNode {
	for hasNode(n) {
		switch kindID(n) {
		case kParenExpr:
			n = firstNamed(n)
		case kTuplePattern:
			if namedChildCount(n) != 1 || strings.Contains(nodeText(src, n), ",") {
				return n
			}
			n = firstNamed(n)
		default:
			return n
		}
	}
	return n
}

func (g *Graph) moduleVarsOf(tree tsNode, src []byte, rec *sourceFile) {
	forEachNamed(tree, func(st tsNode) {
		inner := assignOf(st)
		if !hasNode(inner) {
			return
		}
		switch kindID(inner) {
		case kAssignment:
			value := assignValue(inner)

			if !hasNode(value) {
				return
			}
			ann := ""
			if t := fieldNode(inner, fType); hasNode(t) {
				ann = typeText(src, t)
			}
			for _, tgt := range assignTargets(src, inner) {
				if kindID(tgt) != kIdentifier {
					continue
				}
				name := nodeText(src, tgt)
				if name == "__all__" {

					if hasNode(value) && (kindID(value) == kList || kindID(value) == kTuple) {
						g.captureAllExports(src, rec, value)
					}
					continue
				}
				g.moduleVarRow(src, rec, name, line1(inner), ann, value)
			}
		case kAugAssignment:

			left := fieldNode(inner, fLeft)
			if kindID(left) == kIdentifier && nodeText(src, left) == "__all__" &&
				opText(src, fieldNode(inner, fOperator)) == "+=" {
				value := fieldNode(inner, fRight)
				if hasNode(value) && (kindID(value) == kList || kindID(value) == kTuple) {
					g.captureAllExports(src, rec, value)
				}
			}
		}
	})
}

func (g *Graph) captureAllExports(src []byte, rec *sourceFile, value tsNode) {
	forEachNamed(value, func(e tsNode) {
		if kindID(e) == kString && !hasInterpolation(e) {
			if v, ok := cgStrVal(src, e); ok {
				g.AllExports = append(g.AllExports, AllExport{
					ID: int32(len(g.AllExports) + 1), FileID: rec.fid,
					Name: g.I(v), Line: line1(e)})
			}
		}
	})
}

func (g *Graph) moduleVarRow(src []byte, rec *sourceFile, name string, line int32,
	ann string, value tsNode) {
	value = unwrapAllParens(value)
	mutable := hasNode(value) && kindID(value) == kList || hasNode(value) &&
		(kindID(value) == kDictionary || kindID(value) == kSet)
	called := hasNode(value) && kindID(value) == kCall
	if called && mutableDefaultCalls[lastDot(dotted(src, fieldNode(value, fFunction)))] {
		mutable = true
	}
	g.ModuleVars = append(g.ModuleVars, ModuleVar{
		ID: int32(len(g.ModuleVars) + 1), FileID: rec.fid, ModuleID: rec.mid,
		Name: g.I(name), Line: line, Type: g.I(ann),
		IsConstant:         b2i32(name == strings.ToUpper(name) && isAllUpper(name)),
		IsMutableContainer: b2i32(mutable),
		IsPrivate:          b2i32(strings.HasPrefix(name, "_")),
		HasCallInit:        b2i32(called)})
}

func isAllUpper(s string) bool {
	cased := false
	for _, r := range s {
		if unicode.IsUpper(r) {
			cased = true
		} else if unicode.IsLower(r) || unicode.IsTitle(r) {
			return false
		}
	}
	return cased
}

func defOf(st tsNode) (def tsNode, decs []tsNode) {
	if kindID(st) == kDecoratedDef {
		d := fieldNode(st, fDefinition)
		forEachNamed(st, func(c tsNode) {
			if kindID(c) == kDecorator {
				decs = append(decs, c)
			}
		})
		return d, decs
	}
	switch kindID(st) {
	case kFunctionDef, kClassDef:
		return st, nil
	}
	return tsNode{}, nil
}

func scopeBlocks(n tsNode) []tsNode {
	var out []tsNode
	var add func(b tsNode)
	add = func(b tsNode) {
		forEachNamed(b, func(c tsNode) { out = append(out, c) })
	}

	arms := func(p tsNode) {
		forEachNamed(p, func(c tsNode) {
			switch kindID(c) {
			case kElifClause:
				add(fieldNode(c, fConsequence))
			case kElseClause:
				add(fieldNode(c, fBody))
			}
		})
	}
	switch kindID(n) {
	case kModule:
		forEachNamed(n, func(c tsNode) { out = append(out, c) })
	case kFunctionDef, kClassDef:
		add(fieldNode(n, fBody))
	case kIfStmt:
		add(fieldNode(n, fConsequence))
		arms(n)
	case kForStmt, kWhileStmt, kWithStmt:
		add(fieldNode(n, fBody))
		arms(n)
	case kTryStmt:
		add(fieldNode(n, fBody))
		forEachNamed(n, func(c tsNode) {
			switch kindID(c) {
			case kExceptClause:
				add(firstChildOfKind(c, kBlock))
			case kElseClause:
				add(fieldNode(c, fBody))
			case kFinallyClause:
				add(fieldNode(c, fBody))
			}
		})
	case kMatchStmt:
		var cases func(cn tsNode)
		cases = func(cn tsNode) {
			forEachNamed(cn, func(c tsNode) {
				switch kindID(c) {
				case kBlock:
					cases(c)
				case kCaseClause:
					add(fieldNode(c, fConsequence))
				}
			})
		}
		cases(n)
	case kElifClause:
		add(fieldNode(n, fConsequence))
		arms(n)
	case kElseClause, kFinallyClause:
		add(fieldNode(n, fBody))
	case kExceptClause:
		add(firstChildOfKind(n, kBlock))
	case kCaseClause:
		add(fieldNode(n, fConsequence))
	}
	return out
}

func compoundsRecurse(k uint16) bool {
	switch k {
	case kIfStmt, kForStmt, kWhileStmt, kWithStmt, kTryStmt, kMatchStmt,
		kElifClause, kElseClause, kFinallyClause, kExceptClause, kCaseClause:
		return true
	}
	return false
}

func (g *Graph) walkScope(n tsNode, src []byte, rec *sourceFile, srcLines []string,
	parentID int32, qualPrefix string, classStack []string, nest int32) {

	for _, child := range scopeBlocks(n) {
		def, decs := defOf(child)
		if !hasNode(def) {
			if compoundsRecurse(kindID(child)) {
				g.walkScope(child, src, rec, srcLines, parentID, qualPrefix, classStack, nest)
			}
			continue
		}
		switch kindID(def) {
		case kFunctionDef:
			sid := g.functionOf(def, decs, src, rec, srcLines, parentID, qualPrefix, classStack, nest)
			g.walkScope(def, src, rec, srcLines, sid, qualPrefix+funcName(src, def)+".", classStack, nest+1)
		case kClassDef:
			sid := g.classOf(def, decs, src, rec, srcLines, parentID, qualPrefix, nest)
			g.walkScope(def, src, rec, srcLines, sid, qualPrefix+nodeText(src, fieldNode(def, fName))+".",
				append(append([]string{}, classStack...), nodeText(src, fieldNode(def, fName))), nest+1)
		}
	}
}

func funcName(src []byte, def tsNode) string {
	return nodeText(src, fieldNode(def, fName))
}

func (g *Graph) moduleScope(tree tsNode, src []byte, rec *sourceFile, srcLines []string) {

	x := newMeasure(nil, true)
	x.src = src
	x.root = tree
	x.walk(tree)
	if len(x.calls) == 0 && len(x.m) == 0 {
		freeMeasure(x)
		return
	}
	end := int32(len(srcLines))
	if end == 0 {
		end = 1
	}
	docN := int32(docstringLines(src, tree))
	s := g.measureSymbol(x, 0)
	defer freeMeasure(x)
	s.Name = g.I("<module>")
	s.Kind = g.I("module")
	s.LineStart = 1
	s.LineEnd = end
	s.NLines = end
	s.ByteStart = 0
	s.ByteEnd = 0
	s.SLOC = rec.sloc
	s.IsGenerated = b2i32(rec.isGen)
	s.IsTest = b2i32(rec.isTest)
	s.HasDoc = b2i32(docN > 0)
	s.NDocLines = docN
	s.NCalls = x.m["n_calls"]
	s.NDynamicCalls = x.m["n_dynamic_calls"]
	s.IsEntrypoint = b2i32(isDunderMain(src, tree))

	s.QualName = g.I(rec.rel)
	s.Visibility = g.I("")
	sig := "top-level statements of " + rec.rel
	s.Signature = g.opt(truncStr(sig, 400))
	g.putSymbol(&s, rec)
	sid := s.ID
	g.hazardsAndCalls(x, sid, rec)
	g.dynamicSites(tree, src, sid, rec, true)
	for _, in := range x.inputs {
		g.InputSites = append(g.InputSites, UserInputSite{
			ID: int32(len(g.InputSites) + 1), SymbolID: sid, FileID: rec.fid,
			Var: g.I(in.varnm), Kind: g.I(in.kind), Line: in.line, InLoop: in.inLoop})
	}
	for _, sc := range x.secrets {
		g.Secrets = append(g.Secrets, SecretCandidate{
			ID: int32(len(g.Secrets) + 1), SymbolID: sid, FileID: rec.fid,
			Value: g.I(sc.value), Line: sc.line})
	}
	g.byQual[rec.rel+":<module>"] = sid
}

func isDunderMain(src []byte, tree tsNode) bool {
	found := false
	forEachNamed(tree, func(st tsNode) {
		if kindID(st) != kIfStmt || found {
			return
		}
		cond := fieldNode(st, fCondition)
		if kindID(cond) != kCompareOp {
			return
		}
		if c := firstNamed(cond); hasNode(c) && kindID(c) == kIdentifier &&
			nodeText(src, c) == "__name__" {
			found = true
		}
	})
	return found
}

func decoratorNames(src []byte, decs []tsNode) []string {
	var out []string
	for _, d := range decs {
		out = append(out, dotted(src, firstNamed(d)))
	}
	return out
}

func (g *Graph) functionOf(n tsNode, decs []tsNode, src []byte, rec *sourceFile,
	srcLines []string, parentID int32, qualPrefix string, classStack []string, nest int32) int32 {

	name := funcName(src, n)
	qual := qualPrefix + name
	isMethod := len(classStack) > 0 && parentID >= 0
	decsNames := decoratorNames(src, decs)
	decBase := map[string]bool{}
	for _, d := range decsNames {
		decBase[lastDot(d)] = true
	}
	anyDec := func(names ...string) bool {
		for _, nm := range names {
			if decBase[nm] {
				return true
			}
		}
		return false
	}

	anyDecSub := func(sub string) bool {
		for _, d := range decsNames {
			if strings.Contains(d, sub) {
				return true
			}
		}
		return false
	}

	x := newMeasure(classStack, false)
	x.src = src
	x.root = n

	measureRoot := n
	if p := parentNode(n); kindID(p) == kDecoratedDef {
		measureRoot = p
	}
	x.walk(measureRoot)

	lineEnd := stmtEndLine(n)
	if lineEnd == 0 {
		lineEnd = line1(n)
	}
	docN := int32(docstringLines(src, n))

	s := g.measureSymbol(x, int32(len(srcLines)))
	pa := paramAccountOf(fieldNode(n, fParameters))

	s.NParams = pa.nParams
	s.NOptionalParams = pa.nOptional

	s.IsPublic = b2i32(!strings.HasPrefix(name, "_"))
	s.IsAsync = b2i32(isAsync(n, src))
	s.IsGenerator = b2i32(x.m["n_yield"] > 0)
	s.IsAbstract = b2i32(anyDec("abstractmethod", "abstractproperty"))
	s.IsOverride = b2i32(decBase["override"])
	s.IsDeprecated = b2i32(decBase["deprecated"])
	s.IsTest = b2i32(strings.HasPrefix(name, "test_") ||
		anyDecSub("pytest"))
	s.IsEntrypoint = b2i32(dunderEntry[name])
	s.IsGenerated = b2i32(rec.isGen)
	s.SLOC = slocOf(srcLines, line1(n)-1, lineEnd)
	s.NCommentLines = commentLinesOf(srcLines, line1(n)-1, lineEnd)
	s.NDocLines = docN
	s.HasDoc = b2i32(docN > 0)
	s.Cyclomatic = x.cyclomatic
	s.Cognitive = x.cognitive
	s.MaxNesting = x.maxNesting
	s.MaxLoopDepth = x.maxLoopDepth
	s.NLocals = int32(len(x.storeNames))
	s.NDecorators = int32(len(decsNames))
	s.NDefaultArgs = pa.nDefaults
	s.NKwonlyArgs = pa.kwonly
	s.NPosonlyArgs = pa.posonly
	s.NStarArgs = b2i32(pa.vararg)
	s.NKwargs = b2i32(pa.kwarg)
	s.NAnnotatedParams = pa.annotated
	s.NUntypedParams = pa.nParams - pa.annotated - s.NStarArgs - s.NKwargs
	s.HasReturnType = b2i32(hasNode(fieldNode(n, fReturnType)))
	s.IsProperty = b2i32(anyDec("property", "cached_property"))
	s.IsClassmethod = b2i32(decBase["classmethod"])
	s.IsStaticmethod = b2i32(decBase["staticmethod"])
	s.IsDunder = b2i32(strings.HasPrefix(name, "__") && strings.HasSuffix(name, "__"))
	s.IsPrivate = b2i32(strings.HasPrefix(name, "_") && !strings.HasPrefix(name, "__"))
	s.IsOverload = b2i32(decBase["overload"])
	s.IsContextmanager = b2i32(anyDec("contextmanager", "asynccontextmanager"))
	s.IsCached = b2i32(anyDec("lru_cache", "cache", "cached_property", "memoize"))
	s.NestLevel = nest
	s.NDynamicCalls = x.m["n_dynamic_calls"]
	s.NCalls = x.m["n_calls"]

	s.Name = g.I(name)
	s.Kind = g.I("function")
	if isMethod {
		s.Kind = g.I("method")
	}
	s.LineStart = line1(n)
	s.LineEnd = lineEnd
	s.NLines = lineEnd - line1(n) + 1

	if parentID > 0 {
		s.ParentID = parentID
	}
	s.QualName = g.I(qual)
	if strings.HasPrefix(name, "_") {
		s.Visibility = g.I("private")
	} else {
		s.Visibility = g.I("public")
	}
	s.Signature = g.opt(signatureText(src, n, name))

	s.ReturnType = g.I(typeText(src, fieldNode(n, fReturnType)))
	g.putSymbol(&s, rec)
	sid := s.ID

	defer freeMeasure(x)

	g.paramsOf(sid, fieldNode(n, fParameters), rec, src)
	for i, d := range decs {
		g.Attributes = append(g.Attributes, Attribute{
			ID: int32(len(g.Attributes) + 1), SymbolID: sid, FileID: rec.fid,
			Name: g.opt(orDash(decsNames[i])), Args: g.opt(typeText(src, firstNamed(d))),
			Line: line1(d)})
	}
	g.handlersOf(measureRoot, src, sid)
	for _, c := range x.comps {
		g.Comprehens = append(g.Comprehens, Comprehension{
			ID: int32(len(g.Comprehens) + 1), SymbolID: sid, FileID: rec.fid,
			Kind: g.I(c.kind), Line: c.line, NGenerator: c.gens, NIfs: c.ifs,
			IsAsync: c.async})
	}
	g.hazardsAndCalls(x, sid, rec)
	g.dynamicSites(measureRoot, src, sid, rec, false)
	for _, l := range x.literals {
		g.Literals = append(g.Literals, Literal{
			ID: int32(len(g.Literals) + 1), SymbolID: sid, FileID: rec.fid,
			Kind: g.I(l.kind), Value: g.I(truncStr(l.value, 200)), Line: l.line,
			IsMagic: b2i32(l.magic)})
	}
	for _, in := range x.inputs {
		g.InputSites = append(g.InputSites, UserInputSite{
			ID: int32(len(g.InputSites) + 1), SymbolID: sid, FileID: rec.fid,
			Var: g.I(in.varnm), Kind: g.I(in.kind), Line: in.line, InLoop: in.inLoop})
	}
	for _, sc := range x.secrets {
		g.Secrets = append(g.Secrets, SecretCandidate{
			ID: int32(len(g.Secrets) + 1), SymbolID: sid, FileID: rec.fid,
			Value: g.I(sc.value), Line: sc.line})
	}
	class := ""
	if len(classStack) > 0 {
		class = classStack[len(classStack)-1]
	}
	g.byName[name] = append(g.byName[name], defSite{sid, rec.fid, rec.mid, class})
	g.byQual[rec.rel+":"+qual] = sid
	g.byQual[qual] = sid
	return sid
}

func orDash(s string) string {
	if s == "" {
		return "?"
	}
	return s
}

type paramAccount struct {
	posonly, normal, kwonly int32
	vararg, kwarg           bool
	nParams, nOptional      int32
	nDefaults, annotated    int32
}

type paramList struct {
	name      string
	ann       tsNode
	def       tsNode
	posonly   bool
	kwonly    bool
	variadic  uint8
	splatName string
}

func paramInfo(src []byte, ps tsNode) []paramList {
	var children []tsNode
	forEachNamed(ps, func(c tsNode) { children = append(children, c) })
	posSep, kwSep := -1, -1
	for i, c := range children {
		switch kindID(c) {
		case kPosSeparator:
			if posSep < 0 {
				posSep = i
			}
		case kKwSeparator:
			if kwSep < 0 {
				kwSep = i
			}
		}
	}
	var out []paramList
	for i, c := range children {

		splat := tsNode{}
		switch kindID(c) {
		case kStarParam, kDStarParam:
			splat = c
		default:
			if fn := firstNamed(c); kindID(fn) == kStarParam || kindID(fn) == kDStarParam {
				splat = fn
			}
		}
		if hasNode(splat) {
			e := paramList{ann: fieldNode(c, fType)}
			if kindID(splat) == kDStarParam {
				e.variadic = 2
			} else {
				e.variadic = 1

				if kwSep < 0 {
					kwSep = i
				}
			}
			e.splatName = nodeText(src, firstNamed(splat))
			out = append(out, e)
			continue
		}
		switch kindID(c) {
		case kPosSeparator, kKwSeparator:
			continue
		}
		e := paramList{}
		if posSep >= 0 && i < posSep {
			e.posonly = true
		}
		if kwSep >= 0 && i > kwSep {
			e.kwonly = true
		}
		nm := fieldNode(c, fName)
		if !hasNode(nm) {

			if fn := firstNamed(c); kindID(fn) == kIdentifier {
				nm = fn
			} else {
				nm = c
			}
		}
		e.name = nodeText(src, nm)
		e.ann = fieldNode(c, fType)
		e.def = fieldNode(c, fValue)
		out = append(out, e)
	}
	return out
}

func paramAccountOf(ps tsNode) paramAccount {
	var a paramAccount
	if !hasNode(ps) {
		return a
	}
	for _, e := range paramInfo(nil, ps) {
		switch e.variadic {
		case 1:
			a.vararg = true
			continue
		case 2:
			a.kwarg = true
			continue
		}
		switch {
		case e.posonly:
			a.posonly++
		case e.kwonly:
			a.kwonly++
		default:
			a.normal++
		}
		if hasNode(e.ann) {
			a.annotated++
		}
		if hasNode(e.def) {
			a.nOptional++
			if !e.kwonly {
				a.nDefaults++
			}
		}
	}
	a.nParams = a.posonly + a.normal + a.kwonly
	if a.vararg {
		a.nParams++
	}
	if a.kwarg {
		a.nParams++
	}
	return a
}

func (g *Graph) classOf(n tsNode, decs []tsNode, src []byte, rec *sourceFile,
	srcLines []string, parentID int32, qualPrefix string, nest int32) int32 {

	name := funcName(src, n)
	qual := qualPrefix + name
	var bases []string
	nBases := int32(0)
	if sup := fieldNode(n, fSuperclass); hasNode(sup) {
		forEachNamed(sup, func(b tsNode) {
			if kindID(b) == kKeywordArg {
				return
			}
			nBases++
			if d := dotted(src, b); d != "" {
				bases = append(bases, d)
			}
		})
	}
	baseStr := truncStr(strings.Join(bases, ","), 400)
	decsNames := decoratorNames(src, decs)
	decBase := map[string]bool{}
	for _, d := range decsNames {
		decBase[lastDot(d)] = true
	}
	lineEnd := stmtEndLine(n)
	if lineEnd == 0 {
		lineEnd = line1(n)
	}
	docN := int32(docstringLines(src, n))

	var methods []tsNode
	var classVars int32
	mnames := map[string]bool{}
	hasSlots := false
	for _, st := range scopeBlocks(n) {
		if def, _ := defOf(st); hasNode(def) && kindID(def) == kFunctionDef {
			methods = append(methods, def)
			mnames[funcName(src, def)] = true
		}
		if inner := assignOf(st); hasNode(inner) && kindID(inner) == kAssignment {
			classVars++
			for _, tgt := range assignTargets(src, inner) {
				if kindID(tgt) == kIdentifier && nodeText(src, tgt) == "__slots__" {
					hasSlots = true
				}
			}
		}
	}
	abstract := int32(0)
	for _, m := range methods {
		if p := parentNode(m); kindID(p) == kDecoratedDef {
			for _, d := range decoratorNames(src, decoratorList(p)) {
				if b := lastDot(d); b == "abstractmethod" || b == "abstractproperty" {
					abstract++
				}
			}
		}
	}
	dunder := int32(0)
	for nm := range mnames {
		if strings.HasPrefix(nm, "__") && strings.HasSuffix(nm, "__") {
			dunder++
		}
	}
	isEnum := false
	for _, b := range bases {
		if strings.Contains(b, "Enum") {
			isEnum = true
		}
	}
	isExc := false
	for _, b := range bases {
		if strings.HasSuffix(b, "Error") || strings.HasSuffix(b, "Exception") ||
			b == "Exception" || b == "BaseException" {
			isExc = true
		}
	}

	s := g.baseSymbol()
	s.Name = g.I(name)
	s.Kind = g.I("class")
	s.LineStart = line1(n)
	s.LineEnd = lineEnd
	s.NLines = lineEnd - line1(n) + 1

	if parentID > 0 {
		s.ParentID = parentID
	}
	s.QualName = g.I(qual)
	s.SLOC = slocOf(srcLines, line1(n)-1, lineEnd)
	s.NCommentLines = commentLinesOf(srcLines, line1(n)-1, lineEnd)
	s.NDocLines = docN
	s.HasDoc = b2i32(docN > 0)
	s.NDecorators = int32(len(decsNames))
	if tp := fieldNode(n, fTypeParams); hasNode(tp) {
		s.NGenericParams = int32(countOfKind(tp, kType))
	}
	if strings.HasPrefix(name, "_") {
		s.IsPublic = 0
		s.IsPrivate = 1
		s.Visibility = g.I("private")
	} else {
		s.IsPublic = 1
		s.Visibility = g.I("public")
	}
	s.IsAbstract = b2i32(abstract > 0 || strings.Contains(baseStr, "ABC"))
	s.IsDeprecated = b2i32(decBase["deprecated"])
	s.IsTest = b2i32(strings.HasPrefix(name, "Test"))
	s.IsGenerated = b2i32(rec.isGen)
	s.NestLevel = nest
	sig := truncStr("class "+name+"("+baseStr+")", 400)
	s.Signature = g.opt(sig)
	g.putSymbol(&s, rec)
	sid := s.ID

	for i, d := range decs {
		g.Attributes = append(g.Attributes, Attribute{
			ID: int32(len(g.Attributes) + 1), SymbolID: sid, FileID: rec.fid,
			Name: g.opt(orDash(decsNames[i])), Args: g.opt(typeText(src, firstNamed(d))),
			Line: line1(d)})
	}

	ordinal := int32(0)
	for _, st := range scopeBlocks(n) {
		inner := assignOf(st)
		if !hasNode(inner) {
			continue
		}
		switch kindID(inner) {
		case kAssignment:
			annotated := hasNode(fieldNode(inner, fType))
			value := assignValue(inner)
			for _, tgt := range assignTargets(src, inner) {
				if kindID(tgt) != kIdentifier {
					continue
				}
				tname := nodeText(src, tgt)
				if !annotated {
					if tname == "__slots__" {
						continue
					}

					mutable := int32(0)
					if hasNode(value) {
						switch kindID(value) {
						case kList, kDictionary, kSet:
							mutable = 1
						}
					}
					g.Fields = append(g.Fields, Field{
						SymbolID: sid, Ordinal: ordinal, Name: g.I(tname),
						Type: g.I(""), Visibility: g.I(""), Line: line1(inner),
						IsStatic: 1, IsMutable: mutable, IsColl: mutable,
						IsUntyped: 1, HasDefault: 1, TypeDepth: 0})
					ordinal++
				} else {
					ann := typeText(src, fieldNode(inner, fType))
					g.Fields = append(g.Fields, Field{
						SymbolID: sid, Ordinal: ordinal, Name: g.I(tname),
						Type: g.I(ann), Visibility: g.I(""), Line: line1(inner),
						IsStatic:   1,
						IsNullable: b2i32(strings.Contains(ann, "Optional") || strings.Contains(ann, "None")),
						IsColl:     b2i32(hasAnySub(ann, collectionTypes)),
						IsUntyped:  0, HasDefault: b2i32(hasNode(value)),
						TypeDepth: typeDepthOf(src, fieldNode(inner, fType))})
					ordinal++
				}
			}
		}
	}
	if isEnum {
		eo := int32(0)
		for _, st := range scopeBlocks(n) {
			inner := assignOf(st)
			if !hasNode(inner) || kindID(inner) != kAssignment {
				continue
			}
			for _, tgt := range assignTargets(src, inner) {
				if kindID(tgt) != kIdentifier {
					continue
				}
				g.EnumMembers = append(g.EnumMembers, EnumMember{
					SymbolID: sid, Ordinal: eo, Name: g.I(nodeText(src, tgt)),
					Value: g.opt(truncStr(typeText(src, assignValue(inner)), 80))})
				eo++
			}
		}
	}
	g.Classes = append(g.Classes, ClassInfo{
		SymbolID: sid, NBases: nBases, Bases: g.I(baseStr),
		NMethods: int32(len(methods)), NClassVars: classVars,
		NAbstractM: abstract, NDunder: dunder, HasSlots: b2i32(hasSlots),
		HasInit: b2i32(mnames["__init__"]), HasEq: b2i32(mnames["__eq__"]),
		HasHash:     b2i32(mnames["__hash__"]),
		IsDataclass: b2i32(decBase["dataclass"] || decBase["attrs"] || decBase["attr"]),
		IsABC:       b2i32(strings.Contains(baseStr, "ABC") || strings.Contains(baseStr, "ABCMeta")),
		IsEnum:      b2i32(isEnum), IsException: b2i32(isExc),
		IsProtocol:    b2i32(strings.Contains(baseStr, "Protocol")),
		IsNamedTuple:  b2i32(strings.Contains(baseStr, "NamedTuple") || strings.Contains(baseStr, "namedtuple")),
		IsTypedDict:   b2i32(strings.Contains(baseStr, "TypedDict")),
		IsPydantic:    b2i32(strings.Contains(baseStr, "BaseModel") || strings.Contains(strings.ToLower(baseStr), "pydantic")),
		IsDjangoModel: b2i32(strings.Contains(baseStr, "models.Model") || strings.HasSuffix(baseStr, "Model")),
		IsMetaclass:   b2i32(containsStr(bases, "type") || strings.Contains(baseStr, "ABCMeta"))})

	g.byName[name] = append(g.byName[name], defSite{sid, rec.fid, rec.mid, ""})
	return sid
}

func decoratorList(d tsNode) []tsNode {
	var out []tsNode
	forEachNamed(d, func(c tsNode) {
		if kindID(c) == kDecorator {
			out = append(out, c)
		}
	})
	return out
}

func containsStr(list []string, s string) bool {
	return slices.Contains(list, s)
}

func (g *Graph) baseSymbol() Symbol {
	return Symbol{ID: 0, FileID: -1, ModuleID: -1, ParentID: -1,
		Signature: g.Strings.Null(), ReturnType: g.I("")}
}

func (g *Graph) putSymbol(s *Symbol, rec *sourceFile) {
	s.ID = int32(len(g.Symbols) + 1)
	s.FileID = rec.fid
	s.ModuleID = rec.mid
	g.Symbols = append(g.Symbols, *s)
}

func (g *Graph) measureSymbol(x *measure, nlines int32) Symbol {
	s := g.baseSymbol()
	m := x.m
	s.Cyclomatic = x.cyclomatic
	s.Cognitive = x.cognitive
	s.MaxNesting = x.maxNesting
	s.MaxLoopDepth = x.maxLoopDepth

	fields := []struct {
		key string
		dst *int32
	}{
		{"n_loops", &s.NLoops}, {"n_branches", &s.NBranches},
		{"n_returns", &s.NReturns}, {"n_early_returns", &s.NEarlyReturns},
		{"n_switch", &s.NSwitch}, {"n_cases", &s.NCases},
		{"n_ternary", &s.NTernary}, {"n_logical", &s.NLogical},
		{"n_try", &s.NTry}, {"n_catch", &s.NCatch},
		{"n_catch_broad", &s.NCatchBroad}, {"n_catch_empty", &s.NCatchEmpty},
		{"n_finally", &s.NFinally}, {"n_throw", &s.NThrow},
		{"call_in_loop", &s.CallInLoop}, {"alloc_in_loop", &s.AllocInLoop},
		{"io_in_loop", &s.IOInLoop}, {"await_in_loop", &s.AwaitInLoop},
		{"lock_in_loop", &s.LockInLoop}, {"concat_in_loop", &s.ConcatInLoop},
		{"regex_in_loop", &s.RegexInLoop}, {"query_in_loop", &s.QueryInLoop},
		{"branch_in_loop", &s.BranchInLoop}, {"n_assign", &s.NAssign},
		{"n_compound_assign", &s.NCompoundAssign}, {"n_cmp", &s.NCmp},
		{"n_bitop", &s.NBitop}, {"n_shift", &s.NShift}, {"n_arith", &s.NArith},
		{"n_string_lit", &s.NStringLit}, {"n_float_lit", &s.NFloatLit},
		{"n_magic", &s.NMagic}, {"n_null_check", &s.NNullCheck},
		{"n_subscript", &s.NSubscript}, {"n_member_access", &s.NMemberAccess},
		{"n_lambda", &s.NLambda}, {"n_comprehension", &s.NComprehension},
		{"n_nested_comprehension", &s.NNestedComprehension},
		{"n_async_comprehension", &s.NAsyncComprehension},
		{"n_comp_generators", &s.NCompGenerators}, {"n_comp_ifs", &s.NCompIfs},
		{"n_genexp", &s.NGenexp}, {"n_yield", &s.NYield},
		{"n_yield_from", &s.NYieldFrom}, {"n_await", &s.NAwait},
		{"n_global_stmt", &s.NGlobalStmt}, {"n_nonlocal", &s.NNonlocal},
		{"n_bare_except", &s.NBareExcept}, {"n_catch_swallow", &s.NCatchSwallow},
		{"n_reraise", &s.NReraise}, {"n_with", &s.NWith},
		{"n_async_with", &s.NAsyncWith}, {"n_ctx_managers", &s.NCtxManagers},
		{"n_fstring", &s.NFstring}, {"n_isinstance", &s.NIsinstance},
		{"n_super", &s.NSuper}, {"n_walrus", &s.NWalrus},
		{"n_match", &s.NMatch}, {"n_assert", &s.NAssert},
		{"n_del", &s.NDel}, {"n_print", &s.NPrint}, {"n_open", &s.NOpen},
		{"n_self_attr", &s.NSelfAttr}, {"n_inner_function", &s.NInnerFunction},
		{"n_inner_class", &s.NInnerClass}, {"n_append_in_loop", &s.NAppendInLoop},
		{"len_in_loop", &s.LenInLoop}, {"append_in_loop", &s.AppendInLoop},
		{"try_in_loop", &s.TryInLoop}, {"n_range_len", &s.NRangeLen},
		{"n_try_in_loop", &s.NTryInLoop}, {"n_loop_else", &s.NLoopElse},
		{"n_regex_compile", &s.NRegexCompile}, {"n_regex_call", &s.NRegexCall},
		{"n_sql_literal", &s.NSqlLiteral}, {"n_sql_fstring", &s.NSqlFstring},
		{"n_sql_concat", &s.NSqlConcat}, {"n_sql_format", &s.NSqlFormat},
		{"n_shell_true", &s.NShellTrue}, {"n_annotated_assign", &s.NAnnotatedAssign},
		{"n_try_else", &s.NTryElse}, {"n_pickle_load", &s.NPickleLoad},
		{"n_yaml_load", &s.NYamlLoad}, {"n_weak_random", &s.NWeakRandom},
		{"n_weak_hash", &s.NWeakHash}, {"n_eval_exec", &s.NEvalExec},
		{"n_os_system", &s.NOSystem}, {"n_insecure_temp", &s.NInsecureTemp},
		{"n_sleep_in_loop", &s.NSleepInLoop}, {"n_dynamic_attr", &s.NDynamicAttr},
		{"n_dict_get_in_loop", &s.NDictGetInLoop},
		{"n_open_no_encoding", &s.NOpenNoEncoding},
		{"n_naive_datetime", &s.NDatetime},
		{"n_request_no_timeout", &s.NRequestNoTimeout},
		{"n_redirect", &s.NRedirect}, {"n_auth_call", &s.NAuthCall},
		{"n_fetch", &s.NFetch}, {"n_xxe_parser", &s.NXxeParser},
		{"n_dynamic_open", &s.NDynamicOpen}, {"n_upload_save", &s.NUploadSave},
		{"n_zip_read", &s.NZipRead}, {"n_log_call", &s.NLogCall},
		{"n_assert_in_loop", &s.NAssertInLoop}, {"n_subprocess", &s.NSubprocess},
		{"n_format_in_loop", &s.NFormatInLoop}, {"n_elif", &s.NElif},
		{"n_loop_closure", &s.NLoopClosure}, {"n_broad_raises", &s.NBroadRaises},
		{"n_autoescape_false", &s.NAutoescapeFalse},
		{"n_orm_query_in_loop", &s.NOrmQueryInLoop},
		{"n_commit_in_loop", &s.NCommitInLoop}, {"n_orm_write", &s.NOrmWrite},
		{"n_atomic", &s.NAtomic}, {"n_await_in_sync_with", &s.NAwaitInSyncWith},
		{"n_in_scan_loop", &s.NInScanLoop}, {"n_resource_return", &s.NResourceReturn},
		{"n_mark_safe", &s.NMarkSafe}, {"n_mass_assign", &s.NMassAssign},
		{"n_verify_false", &s.NVerifyFalse},
	}
	for _, f := range fields {
		*f.dst = m[f.key]
	}

	nOps := x.opCount(x.ops)
	nOperands := x.opCount(x.operands)
	s.NOperators = int32(nOps)
	s.NOperands = int32(nOperands)
	s.NDistinctOps = int32(len(x.ops))
	s.NDistinctOperand = int32(len(x.operands))
	s.NTokens = int32(nOps + nOperands)
	if s.NTokens > 0 {
		s.HalsteadVolume = halsteadVolume(nOps, nOperands,
			len(x.ops), len(x.operands))
	}
	_ = nlines
	return s
}

func halsteadVolume(nOps, nOperands, dOps, dOperands int) int64 {
	d := dOps + dOperands
	if d <= 1 {
		d = 2
	}
	return int64(nOps+nOperands) * int64(d)
}

func (x *measure) opCount(m map[string]int32) int {
	n := 0
	for _, v := range m {
		n += int(v)
	}
	return n
}

func slocOf(lines []string, start, end int32) int32 {
	var n int32
	for i := maxI32(0, start); i < minI32(end, int32(len(lines))); i++ {
		t := strings.TrimSpace(lines[i])
		if t != "" && !strings.HasPrefix(t, "#") {
			n++
		}
	}
	return n
}

func minI32(a, b int32) int32 {
	if a < b {
		return a
	}
	return b
}

func commentLinesOf(lines []string, start, end int32) int32 {
	var n int32
	for i := maxI32(0, start); i < minI32(end, int32(len(lines))); i++ {
		if strings.HasPrefix(strings.TrimSpace(lines[i]), "#") {
			n++
		}
	}
	return n
}

func signatureText(src []byte, n tsNode, name string) string {
	args := ""
	if ps := fieldNode(n, fParameters); hasNode(ps) {
		var parts []string
		forEachNamed(ps, func(c tsNode) {
			parts = append(parts, exprText(src, c))
		})
		args = "(" + strings.Join(parts, ", ") + ")"
	}
	if args == "" {
		args = "()"
	}
	pre := "def "
	if isAsync(n, src) {
		pre = "async def "
	}
	ret := typeText(src, fieldNode(n, fReturnType))
	s := pre + name + args
	if ret != "" {
		s += " -> " + ret
	}
	return truncStr(s, 400)
}

var collectionTypes = [...]string{"list", "List", "dict", "Dict", "set", "Set", "tuple"}

func hasAnySub(s string, subs [7]string) bool {
	for _, sub := range subs {
		if strings.Contains(s, sub) {
			return true
		}
	}
	return false
}

func typeText(src []byte, n tsNode) string {
	if !hasNode(n) {
		return ""
	}
	return truncStr(exprText(src, n), 120)
}

func typeDepthOf(src []byte, n tsNode) int32 {
	if !hasNode(n) {
		return 0
	}
	typeDepthSrc = src
	best := int32(0)
	walkSubtree(n, func(c tsNode) {
		if d := chainFrom(c); d > best {
			best = d
		}
	})
	if isBracketKind(skipTypeWrap(n)) {
		return best + 1
	}
	return best
}

func isBracketKind(n tsNode) bool {
	switch kindID(n) {
	case kSubscript, kGenericType:

		return !isSplatSpelling(n)
	}
	return false
}

func isSplatSpelling(n tsNode) bool {
	b := startByte(n)
	return int(b) < len(typeDepthSrc) && typeDepthSrc[b] == '*'
}

var typeDepthSrc []byte

func skipTypeWrap(n tsNode) tsNode {
	for hasNode(n) && kindID(n) == kType {
		n = firstNamed(n)
	}
	return n
}

func chainFrom(n tsNode) int32 {
	n = skipTypeWrap(n)
	if isSplatSpelling(n) {

		if strings.Contains(nodeText(typeDepthSrc, n), "[") {
			return 1
		}
		return 0
	}
	if !isBracketKind(n) {
		return 0
	}
	arg, single := bracketSingleArg(n)
	if single && isBracketKind(arg) {
		return 1 + chainFrom(arg)
	}
	return 1
}

func bracketSingleArg(n tsNode) (tsNode, bool) {
	var args []tsNode
	switch kindID(n) {
	case kGenericType:
		forEachNamed(n, func(c tsNode) {
			if kindID(c) != kTypeParam {
				return
			}
			forEachNamed(c, func(cc tsNode) {
				if kindID(cc) == kType {
					args = append(args, cc)
				}
			})
		})
	case kSubscript:
		val := fieldNode(n, fValue)
		forEachNamed(n, func(c tsNode) {
			if !sameNode(c, val) {
				args = append(args, c)
			}
		})
	}
	if len(args) != 1 {
		return tsNode{}, false
	}
	return skipTypeWrap(args[0]), true
}

func docstringLines(src []byte, n tsNode) int {
	switch kindID(n) {
	case kModule, kClassDef, kFunctionDef:
	default:
		return 0
	}
	var first tsNode
	for _, st := range scopeBlocks(n) {
		first = st
		break
	}
	if !hasNode(first) || kindID(first) != kExprStmt {
		return 0
	}
	v := docValue(src, first)
	if !hasNode(v) {
		return 0
	}
	if kindID(v) == kConcatString {

		fold := strings.Builder{}
		ok := true
		forEachNamed(v, func(c tsNode) {
			if !ok || kindID(c) != kString || hasInterpolation(c) || !strIsText(src, c) {
				if kindID(c) == kString {
					ok = false
				}
				return
			}
			s, good := cgStrVal(src, c)
			if !good {
				ok = false
				return
			}
			fold.WriteString(s)
		})
		if !ok {
			return 0
		}
		doc := fold.String()
		if doc == "" {
			return 0
		}
		return strings.Count(doc, "\n") + 1
	}
	if kindID(v) != kString || hasInterpolation(v) || !strIsText(src, v) {
		return 0
	}
	doc, ok := cgStrVal(src, v)
	if !ok || doc == "" {
		return 0
	}
	return strings.Count(doc, "\n") + 1
}

func docValue(src []byte, stmt tsNode) tsNode {
	var v tsNode
	for c := firstChildN(stmt); hasNode(c); c = nextSiblingOf(c) {
		if !isNamedN(c) {
			if nodeText(src, c) == "," {
				return tsNode{}
			}
			continue
		}
		if kindID(c) == kComment {
			continue
		}
		if hasNode(v) {

			return tsNode{}
		}
		v = c
	}
	for hasNode(v) && kindID(v) == kParenExpr {
		var inner tsNode
		for c := firstChildN(v); hasNode(c); c = nextSiblingOf(c) {
			if !isNamedN(c) || kindID(c) == kComment {
				continue
			}
			if hasNode(inner) {
				return tsNode{}
			}
			inner = c
		}
		v = inner
	}
	return v
}

func strIsText(src []byte, n tsNode) bool {
	for c := firstChildN(n); hasNode(c); c = nextSiblingOf(c) {
		if kindID(c) != kStringStart {
			continue
		}
		for _, r := range nodeText(src, c) {
			switch r {
			case 'f', 'F', 'b', 'B':
				return false
			}
			if r == '"' || r == '\'' {
				return true
			}
		}
	}
	return true
}

func (g *Graph) paramsOf(sid int32, ps tsNode, rec *sourceFile, src []byte) {
	if !hasNode(ps) {
		return
	}
	nMut := int32(0)
	pos := int32(0)

	var splats []*paramList
	list := paramInfo(src, ps)
	for i := range list {
		e := &list[i]
		if e.variadic != 0 {
			splats = append(splats, e)
			continue
		}
		ann := typeText(src, e.ann)
		if defIsMutable(src, unwrapParens(e.def)) {

			nMut++
		}
		g.Params = append(g.Params, Param{
			SymbolID: sid, Pos: pos, Name: g.I(e.name), Type: g.I(ann),
			DefaultValue: g.I(typeText(src, unwrapParens(e.def))), IsOptional: b2i32(hasNode(e.def)),
			IsMutable:  0,
			IsNullable: b2i32(strings.Contains(ann, "Optional") || strings.Contains(ann, "None")),
			IsGeneric:  b2i32(strings.Contains(ann, "TypeVar")),
			IsUntyped:  b2i32(!hasNode(e.ann)),
			TypeDepth:  typeDepthOf(src, e.ann)})
		pos++
	}
	for _, e := range splats {
		prefix := "*"
		if e.variadic == 2 {
			prefix = "**"
		}
		g.Params = append(g.Params, Param{
			SymbolID: sid, Pos: pos, Name: g.I(prefix + e.splatName),
			Type: g.I(typeText(src, e.ann)), DefaultValue: g.Strings.Null(),
			IsVariadic: 1, IsUntyped: b2i32(!hasNode(e.ann)),
			TypeDepth: typeDepthOf(src, e.ann)})
		pos++
	}
	if nMut > 0 {
		g.mutableDefaults = append(g.mutableDefaults,
			struct{ N, ID int32 }{nMut, sid})
	}
}

func unwrapParens(n tsNode) tsNode {
	if !hasNode(n) || kindID(n) != kParenExpr {
		return n
	}
	inner := firstNamed(n)
	switch kindID(inner) {
	case kCondExpr:
		return inner
	}
	return n
}

func unwrapAllParens(n tsNode) tsNode {
	for hasNode(n) && kindID(n) == kParenExpr {
		if inner, ok := soleNamed(n); ok {
			n = inner
		} else {
			break
		}
	}
	return n
}

func defIsMutable(src []byte, def tsNode) bool {
	if !hasNode(def) {
		return false
	}
	switch kindID(def) {
	case kList, kDictionary, kSet:
		return true
	case kCall:
		return mutableDefaultCalls[lastDot(dotted(src, fieldNode(def, fFunction)))]
	}
	return false
}

func (g *Graph) handlersOf(root tsNode, src []byte, sid int32) {
	var walk func(n tsNode, inLoop int32)
	walk = func(n tsNode, inLoop int32) {
		forEachNamed(n, func(c tsNode) {
			switch kindID(c) {
			case kExceptClause:
				types := exceptTypeOf(src, c)
				empty := int32(0)
				if body := firstChildOfKind(c, kBlock); hasNode(body) {
					if single, ok := singleStmt(body); ok {
						switch kindID(single) {
						case kPassStmt:
							empty = 1
						case kExprStmt:

							if v := firstNamed(single); hasNode(v) && isConstKind(v) &&
								childCount(single) == 2 {
								empty = 1
							}
						}
					}
				}
				reraise, log, raiseNoFrom := int32(0), int32(0), int32(0)
				hname := handlerNameOf(src, c)
				walkSubtree(c, func(y tsNode) {
					if kindID(y) == kRaiseStmt {
						reraise = 1

						if exc := raiseExc(y); hasNode(exc) && !hasNode(raiseCause(y)) {
							if kindID(exc) != kIdentifier || nodeText(src, exc) != hname {
								raiseNoFrom = 1
							}
						}
					}
					if kindID(y) == kCall && logLike(dotted(src, fieldNode(y, fFunction))) {
						log = 1
					}
				})
				bare := b2i32(!hasNode(fieldNode(c, fValue)))
				broad := int32(0)
				if bare == 1 {
					broad = 1
				} else if broadExceptions[types] {
					broad = 1
				}
				end := int32(endRow(c) + 1)
				if end == 0 {
					end = line1(c)
				}
				g.Handlers = append(g.Handlers, Handler{
					ID: int32(len(g.Handlers) + 1), SymbolID: sid, Line: line1(c),
					Types: g.I(truncStr(types, 200)), IsBare: bare, IsBroad: broad,
					IsEmpty: empty, HasReraise: reraise, HasLog: log,
					NBodyLines: end - line1(c), InLoop: inLoop,
					HasRaiseNoFrom: raiseNoFrom})

			case kForStmt, kWhileStmt:
				walk(c, 1)
			default:
				walk(c, inLoop)
			}
		})
	}
	walk(root, 0)
}

func exceptTypeOf(src []byte, c tsNode) string {
	tv := fieldNode(c, fValue)
	if !hasNode(tv) {
		return ""
	}
	t := tv
	if kindID(tv) == kAsPattern {
		t = firstNamed(tv)
	}
	if !hasNode(t) {
		return ""
	}
	if kindID(t) == kTuple {
		var parts []string
		forEachNamed(t, func(e tsNode) {
			parts = append(parts, dotted(src, e))
		})
		return strings.Join(parts, ",")
	}
	return dotted(src, t)
}

func handlerNameOf(src []byte, c tsNode) string {
	tv := fieldNode(c, fValue)
	if kindID(tv) == kAsPattern {
		if al := fieldNode(tv, fAlias); hasNode(al) {
			return nodeText(src, firstNamed(al))
		}
	}
	return ""
}

func raiseExc(n tsNode) tsNode { return firstNamed(n) }

func raiseCause(n tsNode) tsNode {
	var out []tsNode
	forEachNamed(n, func(c tsNode) { out = append(out, c) })
	if len(out) > 1 {
		return out[len(out)-1]
	}
	return tsNode{}
}

func logLike(name string) bool {
	l := strings.ToLower(name)
	for _, k := range []string{"log", "warn", "error", "print", "capture", "report"} {
		if strings.Contains(l, k) {
			return true
		}
	}
	return false
}

func (g *Graph) dynamicSites(root tsNode, src []byte, sid int32, rec *sourceFile, moduleLevel bool) {
	if moduleLevel {

		forEachNamed(root, func(st tsNode) {
			inner := assignOf(st)
			if !hasNode(inner) || kindID(inner) != kAssignment {
				return
			}

			if hasNode(fieldNode(inner, fType)) {
				return
			}
			for _, tgt := range assignTargets(src, inner) {
				if kindID(tgt) != kAttribute {
					continue
				}
				base := lastDot(dotted(src, fieldNode(tgt, fObject)))
				kind := "monkeypatch"
				if base == "settings" {
					kind = "settings-write"
				}
				g.APISites = append(g.APISites, APISite{
					ID: int32(len(g.APISites) + 1), SymbolID: sid, FileID: rec.fid,
					Kind: g.I(kind), Expr: g.I(truncStr(exprText(src, inner), 200)),
					Line: line1(inner)})
			}
		})
	}
	walkNamedBFS(root, src, func(c tsNode) {
		if kindID(c) != kCall {
			return
		}
		name := dotted(src, callFunc(c))
		base := ""
		if name != "" {
			base = lastDot(name)
		}
		kind := ""
		switch {
		case base == "eval" || base == "exec" || base == "compile":
			kind = base
		case base == "getattr" || base == "setattr" || base == "delattr":
			kind = "attr"
		case base == "__import__" || base == "import_module":
			kind = "import"
		case base == "globals" || base == "locals" || base == "vars":
			kind = "scope"
		case name == "":
			kind = "computed"
		}
		if kind != "" {
			pos, _ := callArgs(src, c)
			lit := b2i32(len(pos) > 0 && isConstKind(unwrapAllParens(pos[len(pos)-1])))
			expr := truncStr(exprText(src, c), 200)
			g.DynamicSites = append(g.DynamicSites, DynamicSite{
				ID: int32(len(g.DynamicSites) + 1), SymbolID: sid, FileID: rec.fid,
				Kind: g.I(kind), Expr: g.I(expr), Line: line1(c), IsLiteralArg: lit})
		}

		if moduleLevel {
			return
		}
		_, kws := callArgs(src, c)
		if base == "Thread" || strings.HasSuffix(name, ".Thread") {
			for _, kw := range kws {
				if kw.name == "target" && kindID(kw.value) == kIdentifier {
					g.APISites = append(g.APISites, APISite{
						ID: int32(len(g.APISites) + 1), SymbolID: sid, FileID: rec.fid,
						Kind: g.I("thread-target"), Expr: g.I(nodeText(src, kw.value)),
						Line: line1(c)})
				}
			}
		}
		switch base {
		case "Session", "sessionmaker", "scoped_session":
			g.APISites = append(g.APISites, APISite{
				ID: int32(len(g.APISites) + 1), SymbolID: sid, FileID: rec.fid,
				Kind: g.I("session"), Expr: g.I(truncStr(name, 200)), Line: line1(c)})
		case "render_template_string":
			pos, _ := callArgs(src, c)
			lit := b2i32(len(pos) > 0 && isConstKind(unwrapAllParens(pos[0])))
			g.APISites = append(g.APISites, APISite{
				ID: int32(len(g.APISites) + 1), SymbolID: sid, FileID: rec.fid,
				Kind: g.I("ssti"), Expr: g.I(truncStr(name, 200)), Line: line1(c),
				IsLiteralArg: lit})
		}
	})
}

type walkQi struct {
	t *tsTree
	i int32
	d int32
}

func walkNamedBFS(root tsNode, src []byte, fn func(tsNode)) {

	queue := make([]walkQi, 0, 4096)
	queue = append(queue, walkQi{root.t, root.i, 0})

	var push func(n tsNode, d int32)
	push = func(n tsNode, d int32) {
		switch kindID(n) {
		case kBlock, kParenExpr, kArgList, kType, kElseClause, kFinallyClause,
			kWithClause, kAsPattern, kPair, kConcatString:

			for c := firstChildN(n); hasNode(c); c = nextSiblingOf(c) {
				if isNamedN(c) && kindID(c) != kComment {
					push(c, d)
				}
			}
		case kDecoratedDef:

			if def := fieldNode(n, fDefinition); hasNode(def) {
				push(def, d)
			}
			for c := firstChildN(n); hasNode(c); c = nextSiblingOf(c) {
				if isNamedN(c) && kindID(c) == kDecorator {
					push(c, d+1)
				}
			}
		case kExprStmt:
			if a := assignOf(n); hasNode(a) {
				queue = append(queue, walkQi{a.t, a.i, d})
				return
			}
			queue = append(queue, walkQi{n.t, n.i, d})
		default:
			queue = append(queue, walkQi{n.t, n.i, d})
		}
	}

	head := 0
	for head < len(queue) {
		it := queue[head]
		head++
		in := tsNode{t: it.t, i: it.i}
		fn(in)
		d := it.d + 1

		if vals, ok := boolOpValues(src, in); ok {

			for _, c := range vals {
				push(c, d)
			}
			continue
		}
		switch {
		case kindID(in) == kIfStmt:

			var chain tsNode
			for c := firstChildN(in); hasNode(c); c = nextSiblingOf(c) {
				if !isNamedN(c) || kindID(c) == kComment {
					continue
				}
				switch kindID(c) {
				case kElifClause:
					if !hasNode(chain) {
						chain = c
					}
				case kElseClause:
				default:
					push(c, d)
				}
			}
			if hasNode(chain) {
				push(chain, d)
			} else if el := firstChildOfKind(in, kElseClause); hasNode(el) {
				push(el, d)
			}
		case kindID(in) == kElifClause:
			for c := firstChildN(in); hasNode(c); c = nextSiblingOf(c) {
				if isNamedN(c) && kindID(c) != kComment {
					push(c, d)
				}
			}

			if nx := nextNamedSibling(in); hasNode(nx) {
				switch kindID(nx) {
				case kElifClause, kElseClause:
					push(nx, d)
				}
			}
		default:
			switch kindID(in) {
			case kDecoratedDef:
				if def := fieldNode(in, fDefinition); hasNode(def) {
					push(def, d)
				}
				for c := firstChildN(in); hasNode(c); c = nextSiblingOf(c) {
					if isNamedN(c) && kindID(c) == kDecorator {
						push(c, d)
					}
				}
			case kCondExpr:
				var kids [3]tsNode
				nk := 0
				for c := firstChildN(in); hasNode(c); c = nextSiblingOf(c) {
					if !isNamedN(c) || kindID(c) == kComment {
						continue
					}
					if nk < len(kids) {
						kids[nk] = c
					}
					nk++
				}
				if nk == 3 {
					push(kids[1], d)
					push(kids[0], d)
					push(kids[2], d)
					break
				}
				for c := firstChildN(in); hasNode(c); c = nextSiblingOf(c) {
					if isNamedN(c) && kindID(c) != kComment {
						push(c, d)
					}
				}
			default:
				for c := firstChildN(in); hasNode(c); c = nextSiblingOf(c) {
					if isNamedN(c) && kindID(c) != kComment {
						push(c, d)
					}
				}
			}
		}
		if head == len(queue) {

			queue = queue[:0]
			head = 0
		}
	}
}

func boolOpValues(src []byte, n tsNode) ([]tsNode, bool) {
	if !hasNode(n) || kindID(n) != kBoolOp {
		return nil, false
	}
	switch nodeText(src, boolOpToken(n)) {
	case "and", "or":
	default:
		return nil, false
	}
	left := fieldNode(n, fLeft)
	right := fieldNode(n, fRight)
	ls, ok := boolOpValues(src, left)
	if !ok {
		ls = []tsNode{left}
	}
	return append(ls, right), true
}

func (g *Graph) hazardsAndCalls(x *measure, sid int32, rec *sourceFile) {
	alias := g.aliases[rec.fid]
	seen := map[string]*hazardSeen{}
	class := ""
	if len(x.classStack) > 0 {
		class = x.classStack[len(x.classStack)-1]
	}
	for _, c := range x.calls {
		if c.dynamic || c.name == "" {
			continue
		}
		resolved := c.name
		head := firstSegment(c.name)
		if t, ok := alias[head]; ok {
			resolved = t + c.name[len(head):]
		}
		cat, ok := hazardCalls[resolved]
		if !ok {
			cat, ok = hazardCalls[c.name]
		}
		if !ok {

			base := lastDot(c.name)
			if strings.Contains(c.name, ".") {
				if mcat, hit := hazardMethodSuffix[base]; hit {
					cat, resolved, ok = mcat, "*."+base, true
				}
			}
		}
		if ok && cat != "" {
			if e := seen[resolved]; e != nil {
				e.n++
			} else {
				seen[resolved] = &hazardSeen{cat: cat, n: 1, line: c.line}
			}
		}
		g.pendCaller = append(g.pendCaller, sid)
		g.pendFile = append(g.pendFile, rec.fid)
		g.pendModule = append(g.pendModule, rec.mid)
		g.pendName = append(g.pendName, c.name)
		g.pendLine = append(g.pendLine, c.line)
		g.pendClass = append(g.pendClass, class)
	}
	if n := x.m["n_shell_true"]; n > 0 {
		seen["shell=True"] = &hazardSeen{cat: "shell", n: n, line: 0}
	}
	patterns := make([]string, 0, len(seen))
	for pattern := range seen {
		patterns = append(patterns, pattern)
	}
	sort.Strings(patterns)
	for _, pattern := range patterns {
		e := seen[pattern]
		g.Hazards = append(g.Hazards, Hazard{
			SymbolID: sid, Pattern: g.I(truncStr(pattern, 120)),
			Category: g.I(e.cat), N: e.n, FirstLine: e.line})
	}
}

type hazardSeen struct {
	cat  string
	n    int32
	line int32
}

var _ = regexp.MustCompile
var _ = strconv.Itoa

func stmtEndLine(n tsNode) int32 {

	best := int32(0)
	for c := firstChildN(n); hasNode(c); c = nextSiblingOf(c) {
		if kindID(c) == kComment {
			continue
		}
		if e := stmtEndLine(c); e > best {
			best = e
		}
	}
	if best != 0 {
		return best
	}
	return int32(endRow(n) + 1)
}

func cgStrVal(src []byte, n tsNode) (string, bool) {
	if !hasNode(n) || kindID(n) != kString {
		return "", false
	}
	raw, isB := false, false
	val := strings.Builder{}
	for c := firstChildN(n); hasNode(c); c = nextSiblingOf(c) {
		switch kindID(c) {
		case kStringStart:
			p := nodeText(src, c)
			raw = strings.ContainsRune(p, 'r') || strings.ContainsRune(p, 'R')
			isB = strings.ContainsRune(p, 'b') || strings.ContainsRune(p, 'B')
		case kStringContent:
			val.WriteString(decodeStrEscapes(nodeText(src, c), raw, isB))
		case kInterpolation:
			return "", false
		}
	}
	return val.String(), true
}

func cgUnescape(s string, process bool) string {
	if !process {
		return s
	}
	return decodeStrEscapes(s, false, false)
}

func cgFStringBraces(s string) string {
	if !strings.Contains(s, "{{") && !strings.Contains(s, "}}") {
		return s
	}
	r := strings.ReplaceAll(s, "{{", "{")
	return strings.ReplaceAll(r, "}}", "}")
}

func cgIntVal(text string) (int64, string, bool) {
	t := strings.ReplaceAll(text, "_", "")
	neg := false
	if strings.HasPrefix(t, "-") {
		neg, t = true, t[1:]
	}
	base := 10
	switch {
	case strings.HasPrefix(t, "0x"), strings.HasPrefix(t, "0X"):
		base, t = 16, t[2:]
	case strings.HasPrefix(t, "0o"), strings.HasPrefix(t, "0O"):
		base, t = 8, t[2:]
	case strings.HasPrefix(t, "0b"), strings.HasPrefix(t, "0B"):
		base, t = 2, t[2:]
	}
	if t == "" {
		return 0, "", false
	}
	if v, err := strconv.ParseInt(t, base, 64); err == nil {
		if neg {
			v = -v
		}
		return v, "", true
	}

	bi := new(big.Int)
	if _, ok := bi.SetString(t, base); !ok {
		return 0, "", false
	}
	if neg {
		bi.Neg(bi)
	}
	return 0, bi.String(), true
}

func cgRepr(s string) string {
	q := byte('\'')
	if strings.ContainsRune(s, '\'') && !strings.ContainsRune(s, '"') {
		q = '"'
	}
	var b strings.Builder
	b.Grow(len(s) + 2)
	b.WriteByte(q)
	for _, r := range s {
		switch r {
		case rune(q):
			b.WriteByte('\\')
			b.WriteRune(r)
		case '\\':
			b.WriteString(`\\`)
		case '\n':
			b.WriteString(`\n`)
		case '\t':
			b.WriteString(`\t`)
		case '\r':
			b.WriteString(`\r`)
		default:
			if r < 0x20 || r == 0x7f {
				b.WriteString(`\x`)
				const hex = "0123456789abcdef"
				b.WriteByte(hex[r>>4])
				b.WriteByte(hex[r&0xf])
			} else {
				b.WriteRune(r)
			}
		}
	}
	b.WriteByte(q)
	return b.String()
}

func cgFloatText(text string) (body string, imag bool) {
	t := strings.ReplaceAll(text, "_", "")
	if strings.HasSuffix(t, "j") || strings.HasSuffix(t, "J") {
		return t[:len(t)-1], true
	}
	return t, false
}

func exprText(src []byte, n tsNode) string {
	if !hasNode(n) {
		return ""
	}
	if kindID(n) == kGenExp {

		var inner []leafTok
		forEachNamed(n, func(c tsNode) { collectLeaves(src, c, &inner) })
		return "(" + renderLeaves(src, n, inner) + ")"
	}
	var leaves []leafTok
	collectLeaves(src, n, &leaves)
	s := renderLeaves(src, n, leaves)
	if kindID(n) == kNamedExpr {

		return "(" + s + ")"
	}
	return s
}

func renderLeaves(src []byte, root tsNode, leaves []leafTok) string {
	var b strings.Builder
	prevEnd := startByte(root)
	prevTxt := ""
	prevNosp := false
	prevKind := kNoNode
	for i, lf := range leaves {

		s, e := startByte(lf.node), endByte(lf.node)
		ns, ne := s, e
		if lf.spanS != 0 {
			s = lf.spanS
		}
		if lf.spanE != 0 {
			e = lf.spanE
		}
		txt := lf.repr
		if txt == "" {
			txt = string(src[ns:ne])
		}
		if i > 0 && prevTxt == "," && !startsCloseBracket(txt) &&
			!lf.nosp && s == prevEnd {

			b.WriteByte(' ')
		}
		if i > 0 && prevKind == kInteger && strings.HasPrefix(txt, ".") &&
			!strings.HasPrefix(txt, "..") {

			b.WriteByte(' ')
		}
		if i > 0 && s == prevEnd && prevTxt == ":" && !lf.nosp &&
			!startsCloseBracket(txt) && !prevNosp {

			b.WriteByte(' ')
		}
		if i > 0 && s > prevEnd {
			gap := string(eraseComments(src, prevEnd, s))
			if startsCloseBracket(txt) {

				gap = strings.TrimRight(gap, " \t\r\n")
				gap = strings.TrimSuffix(gap, ",")
			}
			if isAllSpace([]byte(gap)) && len(gap) > 0 {

				if prevTxt == "," && !startsCloseBracket(txt) {

					b.WriteByte(' ')
				} else if !endsOpenBracket(prevTxt) && !startsCloseBracket(txt) &&
					txt != "," && txt != ":" && !prevNosp && !lf.nosp &&
					!tightDot(prevTxt, txt) && !tightOpen(prevTxt, txt) {
					b.WriteByte(' ')
				}
			} else if !isAllSpace([]byte(gap)) {
				b.WriteString(gap)
			}
		}
		b.WriteString(lf.pre)
		b.WriteString(txt)
		b.WriteString(lf.post)
		prevEnd = e
		prevTxt = txt
		prevNosp = lf.nosp
		prevKind = kindID(lf.node)
		if lf.post != "" {
			prevTxt = lf.post
		}
	}
	return b.String()
}

func endsOpenBracket(s string) bool {
	return len(s) > 0 && (s[len(s)-1] == '(' || s[len(s)-1] == '[' || s[len(s)-1] == '{')
}

func tightDot(prev, txt string) bool {
	if len(txt) == 0 || txt[0] != '.' || strings.HasPrefix(txt, "..") {
		return false
	}
	if len(prev) == 0 {
		return false
	}
	c := prev[len(prev)-1]
	return c == ')' || c == ']' || c == '\'' || c == '"' || c == '_' ||
		(c >= '0' && c <= '9') || (c >= 'a' && c <= 'z') ||
		(c >= 'A' && c <= 'Z')
}

func startsCloseBracket(s string) bool {
	return len(s) > 0 && (s[0] == ')' || s[0] == ']' || s[0] == '}')
}

type leafTok struct {
	node tsNode
	repr string
	nosp bool
	pre  string
	post string

	spanS, spanE uint
}

func collectLeaves(src []byte, n tsNode, out *[]leafTok) {
	k := kindID(n)
	if k == kComment {
		return
	}
	if k == kString {
		*out = append(*out, leafTok{node: n, repr: renderedString(src, n)})
		return
	}
	if k == kParenExpr {

		var kids []tsNode
		forEachNamed(n, func(c tsNode) { kids = append(kids, c) })
		if len(kids) == 1 {
			inner := kids[0]

			for kindID(inner) == kParenExpr {
				g, ok := soleNamed(inner)
				if !ok {
					break
				}
				inner = g
			}
			if kindID(inner) == kGenExp || kindID(inner) == kNamedExpr {

				*out = append(*out, leafTok{node: n, repr: exprText(src, inner)})
				return
			}
			if dropParens(src, n, inner) {

				collectDropped(src, n, inner, out)
				return
			}
		}
	}
	if k == kConcatString {

		allStr, anyBytes, hasF, fold := true, false, false, strings.Builder{}
		forEachNamed(n, func(c tsNode) {
			if kindID(c) != kString || hasInterpolation(c) {
				allStr = false
				return
			}
			if stringIsBytes(src, c) {
				anyBytes = true
			}
			if stringStartHas(src, c, 'f') || stringStartHas(src, c, 'F') {

				hasF = true
			}
			if v, ok := cgStrVal(src, c); ok {
				fold.WriteString(v)
			} else {
				allStr = false
			}
		})
		if allStr && !hasF && fold.Len() > 0 {
			if anyBytes {
				*out = append(*out, leafTok{node: n, repr: bytesRepr(fold.String())})
			} else {
				*out = append(*out, leafTok{node: n, repr: cgRepr(fold.String())})
			}
			return
		}

		if r, ok := fstringFold(src, n); ok {
			*out = append(*out, leafTok{node: n, repr: r})
			return
		}
		forEachNamed(n, func(c tsNode) {
			collectLeaves(src, c, out)
		})
		return
	}
	if k == kTuple || k == kTuplePattern {

		parent := parentNode(n)

		isForTarget := kindID(parent) == kForIn && sameNode(fieldNode(parent, fLeft), n)
		switch {
		case kindID(parent) == kSubscript || isForTarget:
			mark := len(*out)
			forEachNamed(n, func(c tsNode) { collectLeaves(src, c, out) })
			if len(*out) > mark {
				first := &(*out)[mark]
				last := &(*out)[len(*out)-1]
				first.spanS = startByte(n)
				last.spanE = endByte(n)
				if first.repr == "" && first == last {
					first.repr = string(src[startByte(first.node):endByte(first.node)])
				}
			}
			return
		}
	}
	if k == kArgList {

		var named []tsNode
		forEachNamed(n, func(c tsNode) { named = append(named, c) })
		if len(named) == 1 && kindID(named[0]) == kGenExp {
			var inner []leafTok
			forEachNamed(named[0], func(c tsNode) { collectLeaves(src, c, &inner) })

			*out = append(*out, leafTok{node: named[0],
				repr:  "((" + renderLeaves(src, named[0], inner) + "))",
				spanS: startByte(n), spanE: endByte(n)})
			return
		}
	}
	if k == kGenExp && kindID(parentNode(n)) == kCall &&
		!sameNode(fieldNode(parentNode(n), fFunction), n) {

		var inner []leafTok
		forEachNamed(n, func(c tsNode) { collectLeaves(src, c, &inner) })
		*out = append(*out, leafTok{node: n,
			repr: "((" + renderLeaves(src, n, inner) + "))"})
		return
	}
	cn := childCount(n)
	if cn == 0 {
		lt := leafTok{node: n}
		if k := kindID(n); k == kInteger || k == kFloat {

			lt.repr = renderedNumber(src, n)
		}
		*out = append(*out, lt)
		return
	}
	isSlice := kindID(n) == kSlice

	tightEq := kindID(n) == kDefaultParam || kindID(n) == kTypedDefaultParam ||
		kindID(n) == kKeywordArg
	for i, c := 0, firstChildN(n); hasNode(c); i, c = i+1, nextSiblingOf(c) {
		if kindID(c) == kComment {
			continue
		}
		if childCount(c) > 0 {

			if kOperand(src, n, c) {
				pk := operandKind(src, n, c)
				side := operandSide(src, n, c)
				cp := childPrec(src, n)
				ck := childPrec(src, c)
				if kindID(c) == kParenExpr {
					if inner, ok := soleNamed(c); ok && dropParens(src, c, inner) {
						collectDropped(src, c, inner, out)
						continue
					}

					collectLeaves(src, c, out)
					continue
				}
				if wrapOperand(pk, cp, side, ck) {
					mark := len(*out)
					collectLeaves(src, c, out)
					if len(*out) > mark {
						(*out)[mark].pre = "("
						(*out)[len(*out)-1].post = ")"
					}
					continue
				}
				collectLeaves(src, c, out)
				continue
			}
			collectLeaves(src, c, out)
			continue
		}
		if !isNamedN(c) {
			t := nodeText(src, c)
			if isTrailingComma(n, c, i, cn, src) {

				continue
			}
			if isSlice && t == ":" {

				*out = append(*out, leafTok{node: c, nosp: true})
				continue
			}
			if tightEq && t == "=" {
				*out = append(*out, leafTok{node: c, nosp: true})
				continue
			}
		}
		if k2 := kindID(c); k2 == kInteger || k2 == kFloat {

			*out = append(*out, leafTok{node: c, repr: renderedNumber(src, c)})
			continue
		}
		*out = append(*out, leafTok{node: c})
	}
}

func isTrailingComma(parent tsNode, c tsNode, i, cn int, src []byte) bool {
	if nodeText(src, c) != "," || i+1 >= cn {
		return false
	}
	for nxt := nextSiblingOf(c); hasNode(nxt); nxt = nextSiblingOf(nxt) {
		if kindID(nxt) == kComment {
			continue
		}
		t := nodeText(src, nxt)
		if t != ")" && t != "]" && t != "}" {
			return false
		}
		break
	}
	switch kindID(parent) {
	case kTuple, kSlice, kSubscript:

		named := 0
		forEachNamed(parent, func(tsNode) { named++ })
		if kindID(parent) == kSubscript {
			return named != 2
		}
		return named != 1
	}
	return true
}

const (
	precLambda = iota
	precTest
	precOr
	precAnd
	precNot
	precCompare
	precBitOr
	precBitXor
	precBitAnd
	precShift
	precArith
	precTerm
	precFactor
	precPower
	precAtom
)

func childPrec(src []byte, n tsNode) int {
	k := kindID(n)
	switch k {
	case kLambda, kNamedExpr:
		return precLambda
	case kCondExpr:
		return precTest
	case kBoolOp:
		if op := boolOpText(src, n); op == "and" {
			return precAnd
		}
		return precOr
	case kNotOp:
		return precNot
	case kCompareOp:
		return precCompare
	case kUnaryOp:
		return precFactor
	case kBinaryOp:
		return binOpPrec(operatorText(src, n))
	default:
		return precAtom
	}
}

func binOpPrec(op string) int {
	switch op {
	case "|":
		return precBitOr
	case "^":
		return precBitXor
	case "&":
		return precBitAnd
	case "<<", ">>":
		return precShift
	case "+", "-":
		return precArith
	case "*", "/", "//", "%", "@":
		return precTerm
	case "**":
		return precPower
	default:
		return precCompare
	}
}

func boolOpText(src []byte, n tsNode) string {
	return nodeText(src, boolOpToken(n))
}

func operatorText(src []byte, n tsNode) string {
	for c := firstChildN(n); hasNode(c); c = nextSiblingOf(c) {
		if !isNamedN(c) {
			t := nodeText(src, c)
			switch t {
			case "|", "^", "&", "<<", ">>", "+", "-", "*", "/", "//", "%",
				"@", "**", "==", "!=", "<", "<=", ">", ">=", "in", "is",
				"not", "and", "or", "~":
				return t
			}
			if t == "not" || t == "is" {

				return t
			}
		}
	}
	return ""
}

func kOperand(src []byte, n, c tsNode) bool {
	switch kindID(n) {
	case kBinaryOp, kCompareOp, kBoolOp, kUnaryOp, kNotOp, kCondExpr:
		return !isOperatorToken(src, c)
	}
	return false
}

func isOperatorToken(src []byte, c tsNode) bool {
	if isNamedN(c) {
		return false
	}
	switch nodeText(src, c) {
	case "|", "^", "&", "<<", ">>", "+", "-", "*", "/", "//", "%", "@",
		"**", "==", "!=", "<", "<=", ">", ">=", "in", "is", "not in",
		"is not", "and", "or", "not", "~", "if", "else":
		return true
	}
	return false
}

func soleNamed(paren tsNode) (tsNode, bool) {
	var inner tsNode
	for c := firstChildN(paren); hasNode(c); c = nextSiblingOf(c) {
		if !isNamedN(c) || kindID(c) == kComment {
			continue
		}
		if hasNode(inner) {
			return tsNode{}, false
		}
		inner = c
	}
	return inner, hasNode(inner)
}

func collectDropped(src []byte, paren, content tsNode, out *[]leafTok) {
	mark := len(*out)
	collectLeaves(src, content, out)
	if len(*out) > mark {

		first := &(*out)[mark]
		last := &(*out)[len(*out)-1]
		first.spanS = startByte(paren)
		if first.repr == "" {
			first.repr = string(src[startByte(first.node):endByte(first.node)])
		}
		last.spanE = endByte(paren)
		if len(*out) == mark+1 {
			last.spanS = startByte(paren)
		}
		if last.repr == "" && last != first {
			last.repr = string(src[startByte(last.node):endByte(last.node)])
		}
	}
}

func operandKind(src []byte, parent, child tsNode) uint16 {
	return kindID(parent)
}

func operandSide(src []byte, parent, child tsNode) int {
	switch kindID(parent) {
	case kBinaryOp, kCompareOp, kBoolOp:
		if sameNode(fieldNode(parent, fLeft), child) {
			return 0
		}
		return 1
	}
	return 1
}

func wrapOperand(pk uint16, parentPrec, side, child int) bool {
	if child >= precAtom {
		return false
	}
	switch pk {
	case kBinaryOp, kCompareOp:
		if side == 0 {
			if parentPrec == precPower {
				return child <= parentPrec
			}
			return child < parentPrec
		}
		if parentPrec == precCompare && child == precCompare {
			return true
		}
		return child <= parentPrec
	case kBoolOp:
		if side == 0 {
			return child < parentPrec
		}
		return child <= parentPrec+1
	case kUnaryOp:
		return child < precFactor
	case kNotOp:
		return child < precNot
	case kCondExpr:
		return child < precTest
	}
	return false
}

func dropParens(src []byte, paren tsNode, content tsNode) bool {
	parent := parentNode(paren)
	for hasNode(parent) && (kindID(parent) == kParenExpr || kindID(parent) == kType) {
		parent = parentNode(parent)
	}
	if !hasNode(parent) {
		return false
	}
	pk := kindID(parent)
	ck := childPrec(src, content)
	if contentKindIsAtomLike(content) && ck == precAtom {

		return true
	}
	switch kindID(content) {
	case kGenExp, kNamedExpr:
		return false
	case kTuple:

		pk := kindID(parentNode(paren))
		return pk == kSubscript || pk == kForIn
	}
	switch pk {
	case kAssignment, kReturnStmt, kArgList, kKeywordArg,
		kDefaultParam, kTypedDefaultParam, kExprStmt, kIfStmt, kWhileStmt,
		kAssertStmt, kList, kSet, kPair, kTypedParam:

		return true
	case kBinaryOp, kCompareOp, kBoolOp, kUnaryOp, kNotOp, kCondExpr:
		pp := childPrec(src, parent)
		side := operandSide(src, parent, paren)
		return !wrapOperand(pk, pp, side, ck)
	}
	return false
}

func contentKindIsAtomLike(content tsNode) bool {
	switch kindID(content) {
	case kString, kConcatString, kIdentifier, kAttribute, kCall, kDictionary, kSet,
		kList, kListComp, kSetComp, kDictComp, kTrue, kFalse, kNone,
		kInteger, kFloat:
		return true
	}
	return false
}

func renderedNumber(src []byte, n tsNode) string {
	t := nodeText(src, n)
	last := t[len(t)-1]
	if last == 'j' || last == 'J' {

		f, err := strconv.ParseFloat(strings.ReplaceAll(t[:len(t)-1], "_", ""), 64)
		if err == nil {
			return cgReprFloat(f) + "j"
		}
		return t
	}
	clean := strings.ReplaceAll(t, "_", "")
	if kindID(n) == kInteger {
		if v, ok := parseIntLiteral(clean, strings.ToLower(clean)); ok {
			return v
		}
		return t
	}
	f, err := strconv.ParseFloat(clean, 64)
	if err == nil || math.IsInf(f, 0) {

		if math.IsInf(f, 0) {
			if math.IsInf(f, -1) {
				return "-1e309"
			}
			return "1e309"
		}
		return cgReprFloat(f)
	}
	return t
}

func parseIntLiteral(clean, lower string) (string, bool) {
	base := 10
	digits := lower
	switch {
	case strings.HasPrefix(lower, "0x"):
		base, digits = 16, lower[2:]
	case strings.HasPrefix(lower, "0o"):
		base, digits = 8, lower[2:]
	case strings.HasPrefix(lower, "0b"):
		base, digits = 2, lower[2:]
	}
	if base == 10 {
		return clean, true
	}
	if v, err := strconv.ParseInt(digits, base, 64); err == nil {
		return strconv.FormatInt(v, 10), true
	}
	if big, ok := new(big.Int).SetString(digits, base); ok {
		return big.String(), true
	}
	return "", false
}

func renderedString(src []byte, n tsNode) string {
	text := nodeText(src, n)
	if !hasInterpolation(n) && !stringStartHas(src, n, 'f') && !stringStartHas(src, n, 'F') {
		raw := stringIsRaw(src, n)
		if !raw && stringIsBytes(src, n) {
			if v, ok := cgStrVal(src, n); ok {
				return bytesRepr(v)
			}
			return text
		}
		if v, ok := cgStrVal(src, n); ok {

			return cgRepr(v)
		}
		return text
	}

	return fstringText(src, n)
}

func fstringText(src []byte, n tsNode) string {
	start := firstChildOfKind(n, kStringStart)
	raw := false
	var prefix strings.Builder
	if hasNode(start) {

		for _, ch := range nodeText(src, start) {
			switch {
			case ch == '"' || ch == '\'':
			case ch == 'r' || ch == 'R':
				raw = true
			default:
				prefix.WriteString(string(unicode.ToLower(ch)))
			}
		}
	}
	var body strings.Builder
	forEachNamed(n, func(c tsNode) {
		switch kindID(c) {
		case kStringContent:

			decoded := decodeStrEscapes(nodeText(src, c), raw, false)
			body.WriteString(escapeFStringPart(decoded))
		case kInterpolation:
			body.WriteString(interpolationText(src, c))
		}
	})
	bodyStr := body.String()
	q := byte('\'')
	if strings.ContainsRune(bodyStr, '\'') && !strings.ContainsRune(bodyStr, '"') {
		q = '"'
	} else if strings.ContainsRune(bodyStr, '\'') {
		bodyStr = strings.ReplaceAll(bodyStr, "'", `\'`)
	}
	return prefix.String() + string(q) + bodyStr + string(q)
}

func escapeFStringPart(s string) string {
	var b strings.Builder
	for _, r := range s {
		switch r {
		case '\\':
			b.WriteString(`\\`)
		case '\n':
			b.WriteString(`\n`)
		case '\r':
			b.WriteString(`\r`)
		case '\t':
			b.WriteString(`\t`)
		default:
			b.WriteRune(r)
		}
	}
	return b.String()
}

func interpolationText(src []byte, n tsNode) string {
	expr := firstNamed(n)
	if !hasNode(expr) {
		return nodeText(src, n)
	}
	whole := nodeText(src, n)
	base := startByte(n)

	tail := whole[endByte(expr)-base:]
	e := nodeText(src, expr)
	if kindID(expr) == kCondExpr || kindID(expr) == kLambda {

		e = "(" + exprText(src, expr) + ")"
	}
	return "{" + e + tail
}

func stringIsRaw(src []byte, n tsNode) bool {
	st := firstChildOfKind(n, kStringStart)
	if !hasNode(st) {
		return false
	}
	p := nodeText(src, st)
	return strings.ContainsAny(p, "rR")
}

func eraseComments(src []byte, from, to uint) []byte {
	if !bytesContainByte(src[from:to], '#') {
		return src[from:to]
	}
	buf := make([]byte, to-from)
	copy(buf, src[from:to])
	i := 0
	for i < len(buf) {
		if buf[i] == '#' {
			j := i
			for j < len(buf) && buf[j] != '\n' {
				buf[j] = ' '
				j++
			}
			i = j
			continue
		}
		i++
	}
	return buf
}

func bytesContainByte(b []byte, c byte) bool {
	return slices.Contains(b, c)
}

func isAllSpace(b []byte) bool {
	for _, c := range b {
		switch c {
		case ' ', '\t', '\n', '\r', '\f', '\v', 0:
		default:
			return false
		}
	}
	return true
}

func stringIsBytes(src []byte, n tsNode) bool {
	st := firstChildOfKind(n, kStringStart)
	if !hasNode(st) {
		return false
	}
	return strings.ContainsAny(nodeText(src, st), "bB")
}

func fstringFold(src []byte, n tsNode) (string, bool) {
	anyF, bad := false, false
	type seg struct {
		lit  string
		expr string
	}
	var segs []seg
	lit := strings.Builder{}
	flush := func() {
		if lit.Len() > 0 {
			segs = append(segs, seg{lit: lit.String()})
			lit.Reset()
		}
	}
	forEachNamed(n, func(c tsNode) {
		if bad || kindID(c) != kString {
			return
		}
		if stringIsBytes(src, c) {

			bad = true
			return
		}
		raw := false
		for c2 := firstChildN(c); hasNode(c2); c2 = nextSiblingOf(c2) {
			switch kindID(c2) {
			case kStringStart:
				p := nodeText(src, c2)
				raw = strings.ContainsRune(p, 'r') || strings.ContainsRune(p, 'R')

				if strings.ContainsRune(p, 'f') || strings.ContainsRune(p, 'F') {
					anyF = true
				}
			case kStringContent:

				lit.WriteString(cgUnescape(nodeText(src, c2), !raw))
			case kInterpolation:
				flush()
				anyF = true
				segs = append(segs, seg{expr: interpolationText(src, c2)})
			}
		}
	})
	flush()
	if bad || !anyF {
		return "", false
	}

	only := strings.Builder{}
	for _, s := range segs {
		only.WriteString(s.lit)
		if s.expr != "" {
			only.WriteString(s.expr)
		}
	}
	q := byte('\'')
	if strings.ContainsRune(only.String(), '\'') && !strings.ContainsRune(only.String(), '"') {
		q = '"'
	}
	var b strings.Builder
	b.WriteString("f")
	b.WriteByte(q)
	for _, s := range segs {
		if s.expr != "" {
			b.WriteString(s.expr)
			continue
		}
		for _, r := range s.lit {
			switch r {
			case '\\':
				b.WriteString(`\\`)
			case '\n':
				b.WriteString(`\n`)
			case '\t':
				b.WriteString(`\t`)
			case '\r':
				b.WriteString(`\r`)
			case '{':
				b.WriteString(`{{`)
			case '}':
				b.WriteString(`}}`)
			case rune(q):
				b.WriteByte('\\')
				b.WriteRune(r)
			default:
				b.WriteRune(r)
			}
		}
	}
	b.WriteByte(q)
	return b.String(), true
}

func tightOpen(prev, txt string) bool {
	if txt == "" || (txt[0] != '(' && txt[0] != '[') || len(prev) == 0 {
		return false
	}
	c := prev[len(prev)-1]
	if c == '_' || (c >= '0' && c <= '9') || (c >= 'a' && c <= 'z') ||
		(c >= 'A' && c <= 'Z') {

		i := len(prev)
		for i > 0 {
			ch := prev[i-1]
			if ch == '_' || (ch >= '0' && ch <= '9') || (ch >= 'a' && ch <= 'z') ||
				(ch >= 'A' && ch <= 'Z') {
				i--
				continue
			}
			break
		}
		switch prev[i:] {
		case "and", "or", "not", "is", "in", "if", "else", "elif", "while",
			"for", "lambda", "await", "yield", "assert", "return", "del":
			return false
		}
		return true
	}
	return c == ')' || c == ']' || c == '}'
}

func stringStartHas(src []byte, n tsNode, r rune) bool {
	for c := firstChildN(n); hasNode(c); c = nextSiblingOf(c) {
		if kindID(c) == kStringStart {
			return strings.ContainsRune(nodeText(src, c), r)
		}
	}
	return false
}

func (g *Graph) resolveCalls() (resolved, external, unresolved int32) {

	symLoc := make(map[int32][2]int32, len(g.Symbols))
	for _, sites := range g.byName {
		for _, d := range sites {
			if _, ok := symLoc[d.sym]; !ok {
				symLoc[d.sym] = [2]int32{d.file, d.mod}
			}
		}
	}
	unique := make(map[string]defSite, len(g.byName))
	for nm, sites := range g.byName {
		if len(sites) == 1 {
			unique[nm] = sites[0]
		}
	}
	fileScope := make(map[int64]int32, len(g.byName)*2)
	for nm, sites := range g.byName {
		for _, d := range sites {
			k := int64(d.file)<<32 | int64(hashStr(nm))
			if _, ok := fileScope[k]; !ok {
				fileScope[k] = d.sym
			}
		}
	}

	type ek struct {
		caller, callee int32
		first, last    int32
	}
	type csKey struct{ caller, callee, line int32 }
	edges := make(map[ek]*edgeAgg, len(g.pendCaller))

	callsites := make(map[csKey]bool, len(g.pendCaller))
	unres := make(map[int64]*unresAgg, 256)
	extCount := map[int32]int32{}

	for i := range g.pendCaller {
		name := g.pendName[i]
		if name == "" {
			continue
		}
		caller := g.pendCaller[i]
		fid := g.pendFile[i]
		mid := g.pendModule[i]
		cls := g.pendClass[i]
		line := g.pendLine[i]
		head, tail, _ := strings.Cut(name, ".")
		base := lastDot(name)

		target, found := defSite{}, false
		if head == "self" && tail != "" && cls != "" {
			tb := lastDot(tail)
			for _, d := range g.byName[tb] {
				if d.class == cls {
					target, found = d, true
					break
				}
			}
		}
		if !found {
			if a, ok := g.aliases[fid]; ok {
				if t, ok := a[head]; ok {
					q := t
					if tail != "" {
						q = t + "." + tail
					}

					if sid, ok := g.byQual[q]; ok {
						target, found = defSite{sym: sid, file: fid, mod: mid}, true
					} else if k := strings.IndexByte(q, '.'); k > 0 {
						if sid, ok := g.byQual[q[k+1:]]; ok {
							target, found = defSite{sym: sid, file: fid, mod: mid}, true
						}
					}
				}
			}
		}
		if !found && !strings.Contains(name, ".") {
			if sid, ok := fileScope[int64(fid)<<32|int64(hashStr(name))]; ok {
				target, found = defSite{sym: sid, file: fid, mod: mid}, true
			}
		}
		if !found {
			if d, ok := unique[base]; ok {
				target, found = d, true
			}
		}
		if !found {

			if g.isExternalCall(name, head, fid) {
				extCount[caller]++
				external++
			} else {
				k := int64(caller)<<32 | int64(hashStr(name))
				if u := unres[k]; u == nil {
					unres[k] = &unresAgg{name: name, n: 1, line: line, caller: caller}
				} else {
					u.n++
				}
				unresolved++
			}
			continue
		}
		loc, hasLoc := symLoc[target.sym]
		key := ek{caller, target.sym, 0, 0}
		e := edges[key]
		if e == nil {
			e = &edgeAgg{}
			edges[key] = e
		}
		e.n++
		if hasLoc {
			if b2i32(loc[0] == fid) == 1 {
				e.sameFile = 1
			}
			if b2i32(loc[1] == mid) == 1 {
				e.sameModule = 1
			}
		}
		if b2i32(caller == target.sym) == 1 {
			e.isSelf = 1
		}
		callsites[csKey{caller, target.sym, line}] = true
		resolved++
	}
	for k, e := range edges {
		g.Edges = append(g.Edges, Edge{
			CallerID: k.caller, CalleeID: k.callee, NCalls: e.n,
			SameFile: e.sameFile, SameModule: e.sameModule, IsSelf: e.isSelf})
	}

	sortEdges(g.Edges)
	for k := range callsites {
		g.Callsites = append(g.Callsites, Callsite{
			CallerID: k.caller, CalleeID: k.callee, Line: k.line})
	}
	sortCallsites(g.Callsites)
	type unresRow struct {
		caller int32
		name   string
		n      int32
		line   int32
	}
	unresRows := make([]unresRow, 0, len(unres))
	for _, u := range unres {
		unresRows = append(unresRows, unresRow{caller: u.caller, name: truncStr(u.name, 160), n: u.n, line: u.line})
	}
	sort.Slice(unresRows, func(i, j int) bool {
		if unresRows[i].caller != unresRows[j].caller {
			return unresRows[i].caller < unresRows[j].caller
		}
		if unresRows[i].name != unresRows[j].name {
			return unresRows[i].name < unresRows[j].name
		}
		if unresRows[i].line != unresRows[j].line {
			return unresRows[i].line < unresRows[j].line
		}
		return unresRows[i].n < unresRows[j].n
	})
	for _, u := range unresRows {
		g.Unresolved = append(g.Unresolved, Unresolved{
			CallerID: u.caller, Name: g.I(u.name), N: u.n,
			FirstLine: u.line})
	}
	sortUnresolved(g.Unresolved)
	for sid, n := range extCount {
		g.Symbols[sid-1].NExternalCalls = n
	}
	return resolved, external, unresolved
}

type edgeAgg struct {
	n                    int32
	sameFile, sameModule int32
	isSelf               int32
}

type unresAgg struct {
	name   string
	n      int32
	line   int32
	caller int32
}

func hashStr(s string) uint32 {
	var h uint32 = 2166136261
	for i := 0; i < len(s); i++ {
		h ^= uint32(s[i])
		h *= 16777619
	}
	return h
}

func (g *Graph) isExternalCall(name, head string, fid int32) bool {
	if !strings.Contains(name, ".") && cgBuiltins[head] {
		return true
	}
	target := head
	if a, ok := g.aliases[fid]; ok {
		if t, ok := a[head]; ok {
			target = t
		}
	}
	if stdlibRoots[firstSegment(target)] {
		return true
	}

	if a, ok := g.aliases[fid]; ok {
		if _, imported := a[head]; imported {
			return g.isExternalModule(target)
		}
	}
	return false
}

func (g *Graph) resolveImports() int {

	byPath := make(map[string]int32, len(g.Files)*2)
	for fi := range g.Files {
		fp := g.S(g.Files[fi].Path)
		byPath[fp] = g.Files[fi].ID
		if di := strings.LastIndexByte(fp, '.'); di > 0 {
			if _, ok := byPath[fp[:di]]; !ok {
				byPath[fp[:di]] = g.Files[fi].ID
			}
		}
	}
	look := func(cand string) int32 {
		cand = strings.Trim(cand, "/")
		if cand == "" {
			return -1
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
		return -1
	}
	n := 0
	for i := range g.Imports {
		target := g.S(g.Imports[i].Target)
		if target == "" {
			continue
		}
		p := g.S(g.Files[g.Imports[i].FileID-1].Path)
		here := dirOf(p)
		var hit int32 = -1
		if strings.HasPrefix(target, ".") {

			nUp := int32(len(target) - len(strings.TrimLeft(target, ".")))
			rest := strings.ReplaceAll(target[nUp:], ".", "/")
			base := here
			for i := int32(0); i < nUp-1; i++ {
				base = dirOf(base)
			}
			if base != "" {
				hit = look(base + "/" + rest)
			} else {
				hit = look(rest)
			}
		} else {
			hit = look(strings.ReplaceAll(target, ".", "/"))
			if hit < 0 {
				hit = look(here + "/" + target)
			}
		}
		if hit >= 0 && hit != g.Imports[i].FileID {
			g.Imports[i].TargetID = hit
			n++
		}
	}
	return n
}

var importSuffixes = []string{"", ".py", ".pyi", ".ts", ".tsx", ".d.ts", ".mts",
	".cts", ".js", ".jsx", ".mjs", ".cjs", ".rb", ".php", ".go", ".rs", ".java"}

var importIndexes = []string{"__init__.py", "index.ts", "index.tsx", "index.js",
	"index.mjs", "mod.rs", "lib.rs"}

func dirOf(p string) string {
	if i := strings.LastIndexByte(p, '/'); i >= 0 {
		return p[:i]
	}
	return ""
}

func (g *Graph) materialise() {
	n := len(g.Symbols)
	fanOut := make([]int32, n+1)
	fanIn := make([]int32, n+1)
	callsites := make([]int32, n+1)
	recursive := make([]int32, n+1)
	for _, e := range g.Edges {
		if e.IsSelf == 1 {
			recursive[e.CallerID] = 1
		}
		if e.IsSelf == 0 {
			fanOut[e.CallerID]++
			fanIn[e.CalleeID]++
		}
	}
	uniqueCalls := make([]int32, n+1)
	for _, e := range g.Edges {
		uniqueCalls[e.CallerID]++
	}
	for _, c := range g.Callsites {
		callsites[c.CalleeID]++
	}
	unresolved := make([]int32, n+1)
	for _, u := range g.Unresolved {
		unresolved[u.CallerID] += u.N
	}

	hazTotal := make([]int32, n+1)
	hazCat := make(map[string][]int32, len(hazardCategories))
	for _, cat := range hazardCategories {
		hazCat[cat] = make([]int32, n+1)
	}
	for _, h := range g.Hazards {
		hazTotal[h.SymbolID] += h.N
		if c := g.S(h.Category); c != "" {
			if col, ok := hazCat[c]; ok {
				col[h.SymbolID] += h.N
			}
		}
	}
	for i := 1; i <= n; i++ {
		s := &g.Symbols[i-1]
		s.FanOut = fanOut[i]
		s.FanIn = fanIn[i]
		s.NCallsites = callsites[i]
		s.NUniqueCalls = uniqueCalls[i]
		s.IsRecursive = recursive[i]
		s.NUnresolvedCalls = unresolved[i]
		s.NHazards = hazTotal[i]
		s.IsLeaf = b2i32(fanOut[i] == 0)
		s.IsRoot = b2i32(fanIn[i] == 0)
		for _, cat := range hazardCategories {
			v := hazCat[cat][i]
			switch cat {
			case "exec":
				s.NExec = v
			case "deserialize":
				s.NDeserialize = v
			case "io":
				s.NIO = v
			case "net":
				s.NNet = v
			case "sql":
				s.NSql = v
			case "crypto":
				s.NCrypto = v
			case "reflect":
				s.NReflect = v
			case "concurrency":
				s.NConcurrency = v
			case "blocking":
				s.NBlocking = v
			case "resource":
				s.NResource = v
			case "shell":
				s.NShell = v
			}
		}
		if s.HalsteadVolume == 0 && s.NTokens > 0 {
			s.HalsteadVolume = halsteadVolume(int(s.NOperators), int(s.NOperands),
				int(s.NDistinctOps), int(s.NDistinctOperand))
		}

		if isFuncKind(g.S(s.Kind)) {
			sloc := 0.0
			if s.SLOC > 1 {
				sloc = float64(s.SLOC) / 20.0
			} else {
				sloc = 0.05
			}
			v := 171 - 0.23*float64(s.Cyclomatic) - 16.2*sloc
			if v < 0 {
				v = 0
			}
			s.Maintainability = int32(v)
		}
		s.RiskScore = riskScore(*s)
	}

	fSyms := make([]int32, len(g.Files)+1)
	fFuncs := make([]int32, len(g.Files)+1)
	fTypes := make([]int32, len(g.Files)+1)
	fCyclo := make([]int32, len(g.Files)+1)
	maxCyclo := make([]int32, len(g.Files)+1)
	fRisk := make([]int32, len(g.Files)+1)
	for i := range g.Symbols {
		s := &g.Symbols[i]
		if s.FileID < 1 || int(s.FileID) > len(g.Files) {
			continue
		}
		f := s.FileID
		fSyms[f]++
		switch g.S(s.Kind) {
		case "function", "method", "constructor", "closure":
			fFuncs[f]++
		case "class", "struct", "interface", "trait", "enum", "union", "record",
			"protocol", "type", "impl":
			fTypes[f]++
		}
		fCyclo[f] += s.Cyclomatic
		if s.Cyclomatic > maxCyclo[f] {
			maxCyclo[f] = s.Cyclomatic
		}
		fRisk[f] += s.RiskScore
	}
	for i := range g.Files {
		f := &g.Files[i]
		f.NSymbols = fSyms[f.ID]
		f.NFunctions = fFuncs[f.ID]
		f.NTypes = fTypes[f.ID]
		f.TotalCyclo = fCyclo[f.ID]
		f.MaxCyclo = maxCyclo[f.ID]

		_ = fRisk
		f.TotalRisk = 0
	}
	fImports := make([]int32, len(g.Files)+1)
	for _, im := range g.Imports {
		fImports[im.FileID]++
	}
	for i := range g.Files {
		g.Files[i].NImports = fImports[g.Files[i].ID]
	}

	mSyms := make([]int32, len(g.Modules)+1)
	mPublic := make([]int32, len(g.Modules)+1)
	for i := range g.Symbols {
		s := &g.Symbols[i]
		if s.ModuleID < 1 || int(s.ModuleID) > len(g.Modules) {
			continue
		}
		mSyms[s.ModuleID]++
		mPublic[s.ModuleID] += s.IsPublic
	}
	mFiles := make([]int32, len(g.Modules)+1)
	mSLOC := make([]int32, len(g.Modules)+1)
	for i := range g.Files {
		f := &g.Files[i]
		if f.ModuleID < 1 || int(f.ModuleID) > len(g.Modules) {
			continue
		}
		mFiles[f.ModuleID]++
		mSLOC[f.ModuleID] += f.SLOC
	}

	outSet := make([]map[int32]bool, len(g.Modules)+1)
	inSet := make([]map[int32]bool, len(g.Modules)+1)
	for i := range g.Modules {
		outSet[i+1] = map[int32]bool{}
		inSet[i+1] = map[int32]bool{}
	}
	for _, e := range g.Edges {
		if e.CallerID < 1 || e.CalleeID < 1 ||
			int(e.CallerID) > n || int(e.CalleeID) > n {
			continue
		}
		m1 := g.Symbols[e.CallerID-1].ModuleID
		m2 := g.Symbols[e.CalleeID-1].ModuleID
		if m1 < 1 || m2 < 1 || m1 == m2 {
			continue
		}
		outSet[m1][m2] = true
		inSet[m2][m1] = true
	}
	for i := range g.Modules {
		m := &g.Modules[i]
		m.NSymbols = mSyms[m.ID]
		m.NPublic = mPublic[m.ID]
		m.NFiles = mFiles[m.ID]
		m.SLOC = mSLOC[m.ID]
		m.FanOut = int32(len(outSet[m.ID]))
		m.FanIn = int32(len(inSet[m.ID]))
		if m.FanIn+m.FanOut == 0 {
			m.Instability = 0
		} else {
			m.Instability = float64(m.FanOut) / float64(m.FanIn+m.FanOut)
		}
	}

	kindSum := make(map[int32][3]int32)
	for i := range g.Symbols {
		s := &g.Symbols[i]
		if s.ParentID < 0 {
			continue
		}
		var a [3]int32
		if g.S(s.Kind) == "method" {
			a[0] = 1
		}
		if s.IsProperty == 1 {
			a[1] = 1
		}
		if s.IsDunder == 1 {
			a[2] = 1
		}
		kindSum[s.ParentID] = [3]int32{a[0] + kindSum[s.ParentID][0],
			a[1] + kindSum[s.ParentID][1], a[2] + kindSum[s.ParentID][2]}
	}
	for i := range g.Classes {
		if a, ok := kindSum[g.Classes[i].SymbolID]; ok {
			g.Classes[i].NMethods = a[0]
			g.Classes[i].NProperties = a[1]
			g.Classes[i].NDunder = a[2]
		}
	}
	for _, md := range g.mutableDefaults {
		if int(md.ID) >= 1 && int(md.ID) <= n {
			g.Symbols[md.ID-1].NMutableDefault = md.N
		}
	}

	g.buildAdjacency()
	g.buildIndex()

}

var hazardCategories = []string{"exec", "deserialize", "io", "net", "sql",
	"crypto", "reflect", "concurrency", "blocking", "resource", "shell"}

func isFuncKind(k string) bool {
	switch k {
	case "function", "method", "constructor", "closure":
		return true
	}
	return false
}

func riskScore(s Symbol) int32 {
	v := s.Cyclomatic*2 + s.Cognitive + s.MaxNesting*4 +
		s.NExec*30 + s.NDeserialize*25 + s.NShell*15 + s.NShellTrue*30 +
		s.NSqlFstring*30 + s.NSqlConcat*25 + s.NSqlFormat*25 +
		s.NReflect*3 + s.NNet*6 + s.NIO*4 + s.NCrypto*8 +
		s.NConcurrency*5 + s.NBlocking*4 +
		s.NBareExcept*10 + s.NCatchSwallow*8 + s.NMutableDefault*12 +
		s.AwaitInLoop*10 + s.QueryInLoop*15 + s.CallInLoop*2
	if s.IsRecursive == 1 {
		v += 15
	}
	if s.HasDoc == 0 && s.IsPublic == 1 {
		v += 5
	}
	return v
}

func (g *Graph) buildAdjacency() {
	n := len(g.Symbols)
	callerOff := make([]int32, n+2)
	calleeOff := make([]int32, n+2)
	for _, e := range g.Edges {
		if e.CallerID >= 0 && int(e.CallerID) <= n {
			callerOff[e.CallerID+1]++
		}
		if e.CalleeID >= 0 && int(e.CalleeID) <= n {
			calleeOff[e.CalleeID+1]++
		}
	}
	for i := 1; i < len(callerOff); i++ {
		callerOff[i] += callerOff[i-1]
	}
	for i := 1; i < len(calleeOff); i++ {
		calleeOff[i] += calleeOff[i-1]
	}
	callerAdj := make([]int32, len(g.Edges))
	calleeAdj := make([]int32, len(g.Edges))
	cf := make([]int32, n+1)
	df := make([]int32, n+1)
	copy(cf, callerOff[:n+1])
	copy(df, calleeOff[:n+1])
	for _, e := range g.Edges {
		if e.CallerID >= 0 && int(e.CallerID) <= n {
			callerAdj[cf[e.CallerID]] = e.CalleeID
			cf[e.CallerID]++
		}
		if e.CalleeID >= 0 && int(e.CalleeID) <= n {
			calleeAdj[df[e.CalleeID]] = e.CallerID
			df[e.CalleeID]++
		}
	}
	g.callerOff, g.callerAdj = callerOff, callerAdj
	g.calleeOff, g.calleeAdj = calleeOff, calleeAdj
}

func (g *Graph) callees(sid int32) []int32 {
	if int(sid)+1 >= len(g.callerOff) {
		return nil
	}
	return g.callerAdj[g.callerOff[sid]:g.callerOff[sid+1]]
}

func (g *Graph) callers(sid int32) []int32 {
	if int(sid)+1 >= len(g.calleeOff) {
		return nil
	}
	return g.calleeAdj[g.calleeOff[sid]:g.calleeOff[sid+1]]
}

func (g *Graph) setMeta(k, v string) {
	g.Meta = append(g.Meta, [2]uint32{g.I(k), g.I(v)})
}

func floatText(f float64) string {
	if math.IsNaN(f) {
		return "nan"
	}
	if math.IsInf(f, 1) {
		return "inf"
	}
	if math.IsInf(f, -1) {
		return "-inf"
	}
	neg := math.Signbit(f)
	if neg {
		f = -f
	}

	sci := strconv.FormatFloat(f, 'e', -1, 64)
	e := strings.IndexByte(sci, 'e')
	mant, exp := sci[:e], sci[e+1:]
	digits := strings.TrimRight(strings.Replace(mant, ".", "", 1), "0")
	if digits == "" {
		digits = "0"
	}
	n, _ := strconv.Atoi(exp)

	decpt := n + 1

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
		b.WriteByte('e')
		if decpt-1 < 0 {
			b.WriteByte('-')
		} else {
			b.WriteByte('+')
		}
		x := decpt - 1
		if x < 0 {
			x = -x
		}
		if x < 10 {
			b.WriteByte('0')
		}
		b.WriteString(strconv.Itoa(x))
		return b.String()
	}
	switch {
	case decpt <= 0:
		b.WriteString("0.")
		b.WriteString(strings.Repeat("0", -decpt))
		b.WriteString(digits)
	case decpt >= len(digits):
		b.WriteString(digits)
		b.WriteString(strings.Repeat("0", decpt-len(digits)))
		b.WriteString(".0")
	default:
		b.WriteString(digits[:decpt])
		b.WriteByte('.')
		b.WriteString(digits[decpt:])
	}
	return b.String()
}

var colKinds = map[string]string{
	"graph-blindspots":              "siiiiii",
	"risk-ranked":                   "siiiiiiiis",
	"hot-multipliers":               "siiiiiiss",
	"typing-holes":                  "siiiiiis",
	"god-functions":                 "siiiiiiiiis",
	"deep-nesting":                  "siiiiis",
	"nested-loops":                  "siiiiiis",
	"class-shape":                   "siiisiiiis",
	"slots-candidates":              "siiiiis",
	"module-coupling":               "ssiiiiiir",
	"undocumented-complexity":       "siiiiiis",
	"magic-numbers":                 "siiis",
	"markers":                       "ssissi",
	"parse-coverage":                "siiiiiii",
	"latent-risk-density":           "ssiiiiiiiiis",
	"too-many-locals":               "siiiiiis",
	"too-many-branches":             "siiiiiis",
	"too-many-return":               "siiiiis",
	"scattered-concerns":            "siiiiss",
	"line-too-long":                 "siiiis",
	"untyped-params":                "siiiiiis",
	"deep-nesting-excessive":        "siiiiiis",
	"god-class":                     "siniis",
	"import-surface":                "siiiiiiiis",
	"exception-posture":             "siiiiiiis",
	"resource-posture":              "siiiiiis",
	"concurrency-posture":           "siiiiiiis",
	"sql-construction":              "siiiiiiiis",
	"third-party-coupling":          "siiiiis",
	"recursive-hotspots":            "siiiiis",
	"registration-surface":          "siiss",
	"input-surface":                 "siiiis",
	"network-hygiene":               "siiiiis",
	"async-blocking":                "siiiiiis",
	"async-blocking-reachable":      "siiss",
	"await-in-loop":                 "siiiiis",
	"mutable-defaults":              "siiiiss",
	"untrusted-frontier":            "siiiiiis",
	"sql-built-by-hand":             "siiiiiis",
	"n-plus-one":                    "siiiiis",
	"loop-multiplied":               "siiiiiiiis",
	"quadratic-strings":             "siiiiis",
	"swallowed-errors":              "siiiiiiis",
	"reflection-opacity":            "siiiis",
	"decorator-roots":               "ssiiiis",
	"dead-code":                     "ssiiis",
	"untested":                      "siiiiis",
	"unbounded-caches":              "sssiis",
	"shared-mutable-state":          "ssisiii",
	"import-cycles":                 "ssii",
	"import-workarounds":            "sssiis",
	"resource-discipline":           "siiiiiis",
	"weak-crypto":                   "ssiiiis",
	"concurrency-surface":           "siiiiiis",
	"unsafe-decode-reachable":       "ssiiiiiiss",
	"bare-except":                   "siiiiiis",
	"pickle-deserialization":        "siiiis",
	"yaml-unsafe-load":              "siiiis",
	"subprocess-shell-injection":    "siiiiis",
	"eval-exec-injection":           "siiiis",
	"assert-in-production":          "siiiis",
	"global-statement":              "siiiiis",
	"open-without-with":             "siiiiiis",
	"datetime-naive":                "siiiis",
	"append-in-loop-perf":           "siiiiis",
	"decorator-depth":               "ssiiiis",
	"non-public-leak":               "ssissi",
	"wildcard-import-rank":          "siii",
	"all-reexports":                 "ssiii",
	"relative-import-depth":         "siii",
	"method-kind-mix":               "siiiiis",
	"request-without-timeout":       "ssii",
	"open-redirect-surface":         "siisis",
	"ssrf-fetch-surface":            "siiss",
	"hardcoded-secret-candidates":   "ssiis",
	"xxe-parser-surface":            "siis",
	"path-traversal-surface":        "siiss",
	"unchecked-upload-surface":      "siis",
	"zip-slip-surface":              "siis",
	"log-injection-surface":         "siisis",
	"unauthenticated-input-surface": "siss",
	"exception-in-loop":             "ssiii",
	"call-in-default-argument":      "ssssi",
	"name-shadowing":                "ssssi",
	"undocumented-export":           "ssiis",
	"closure-in-loop":               "siiiis",
	"raise-without-from":            "ssisi",
	"suppression-burden":            "siii",
	"broad-test-expectation":        "ssiii",
	"template-injection":            "ssiii",
	"orm-query-in-loop":             "siiiiis",
	"commit-in-loop":                "siiiis",
	"multi-write-no-atomic":         "siiis",
	"celery-task-sync-call":         "ssiis",
	"celery-task-reliability":       "ssis",
	"lock-across-await":             "siiiis",
	"thread-target-shared-state":    "ssiiis",
	"import-monkeypatch":            "ssis",
	"settings-mutation-import":      "ssis",
	"import-time-side-effects":      "siiiiiiis",
	"membership-scan-in-loop":       "siiiis",
	"resource-return-escape":        "siiis",
	"taint-frontier-input":          "siiiiiiis",
	"mark-safe-surface":             "siisis",
	"mass-assignment-surface":       "siisis",
	"ssti-surface":                  "ssiiis",
	"session-created-per-call":      "siis",
	"tls-verify-disabled":           "siis",
	"test-only-callers":             "siiiis",
	"mutable-class-attribute":       "sssis",
	"global-write-reachable":        "siiis",
	"prod-imports-test":             "ssiis",
	"dict-get-in-loop":              "siiiis",
	"format-in-loop":                "siiiis",
	"loop-else":                     "siiiis",
	"print-statement-shipping":      "siis",
	"insecure-tempfile":             "siis",
	"unused-public-api":             "ssiiis",
}

func cellFor(kind byte, s string) (string, bool) {
	switch kind {
	case 'r':

		f, err := strconv.ParseFloat(strings.TrimSpace(s), 64)
		if err != nil {
			return s, false
		}
		return floatText(f), false
	case 'n', 't':
		if s == "-" {
			return "", true
		}
	}
	return s, false
}

func csvQuote(f string) bool { return strings.ContainsAny(f, ",\"\r\n") }

func writeCSVRow(w *bufio.Writer, fields []string) {
	for i, f := range fields {
		if i > 0 {
			w.WriteByte(',')
		}

		if csvQuote(f) || (i == 0 && len(fields) == 1 && f == "") {
			w.WriteByte('"')
			w.WriteString(strings.ReplaceAll(f, `"`, `""`))
			w.WriteByte('"')
		} else {
			w.WriteString(f)
		}
	}
	w.WriteString("\r\n")
}

func writeCSV(w *bufio.Writer, r result, qname string) {
	writeCSVRow(w, r.cols)
	kinds := colKinds[qname]
	buf := make([]string, len(r.cols))
	for _, row := range r.rows {
		for i := range row {
			kind := byte('s')
			if i < len(kinds) {
				kind = kinds[i]
			}
			v, _ := cellFor(kind, row[i])
			buf[i] = v
		}
		writeCSVRow(w, buf[:len(row)])
	}
}

const hexDigits = "0123456789abcdef"

func writeJSONString(w *bufio.Writer, s string) {
	w.WriteByte('"')
	for _, r := range s {
		switch r {
		case '"':
			w.WriteString(`\"`)
			continue
		case '\\':
			w.WriteString(`\\`)
			continue
		case '\n':
			w.WriteString(`\n`)
			continue
		case '\r':
			w.WriteString(`\r`)
			continue
		case '\t':
			w.WriteString(`\t`)
			continue
		case '\b':
			w.WriteString(`\b`)
			continue
		case '\f':
			w.WriteString(`\f`)
			continue
		}
		if r >= 0x20 && r < 0x7f {
			w.WriteRune(r)
			continue
		}
		if r < 0x10000 {
			writeU16(w, uint16(r))
			continue
		}
		r -= 0x10000
		writeU16(w, uint16(0xd800+(r>>10)))
		writeU16(w, uint16(0xdc00+(r&0x3ff)))
	}
	w.WriteByte('"')
}

func writeU16(w *bufio.Writer, u uint16) {
	w.WriteString(`\u`)
	w.WriteByte(hexDigits[u>>12&0xf])
	w.WriteByte(hexDigits[u>>8&0xf])
	w.WriteByte(hexDigits[u>>4&0xf])
	w.WriteByte(hexDigits[u&0xf])
}

func writeJSONValue(w *bufio.Writer, kind byte, s string) {
	switch kind {
	case 'i', 'n':

		if kind == 'n' && s == "-" {
			w.WriteString("null")
			return
		}
		w.WriteString(s)
	case 'r':
		f, err := strconv.ParseFloat(strings.TrimSpace(s), 64)
		if err != nil {
			w.WriteString(s)
			return
		}
		w.WriteString(floatText(f))
	case 't':
		if s == "-" {
			w.WriteString("null")
			return
		}
		writeJSONString(w, s)
	default:
		writeJSONString(w, s)
	}
}

func writeJSON(w *bufio.Writer, r result, qname string) {
	kinds := colKinds[qname]
	if len(r.rows) == 0 {
		w.WriteString("[]\n")
		return
	}

	name := make([]int, 0, len(r.cols))
	src := make([]int, 0, len(r.cols))
	for i, c := range r.cols {
		found := -1
		for j, k := range name {
			if r.cols[k] == c {
				found = j
				break
			}
		}
		if found >= 0 {
			src[found] = i
			continue
		}
		name = append(name, i)
		src = append(src, i)
	}
	w.WriteString("[\n")
	for n, row := range r.rows {
		if n > 0 {
			w.WriteString(",\n")
		}
		w.WriteString("  {\n")
		for j, ci := range name {
			if j > 0 {
				w.WriteString(",\n")
			}
			kind := byte('s')
			if v := src[j]; v < len(kinds) {
				kind = kinds[v]
			}
			cell := ""
			if v := src[j]; v < len(row) {
				cell = row[v]
			}
			w.WriteString("    ")
			writeJSONString(w, r.cols[ci])
			w.WriteString(": ")
			writeJSONValue(w, kind, cell)
		}
		w.WriteString("\n  }")
	}
	w.WriteString("\n]\n")
}

type qNum struct {
	set bool
	n   int
}

func (q *qNum) String() string {
	if !q.set {
		return "N"
	}
	return strconv.Itoa(q.n)
}

func (q *qNum) Set(v string) error {
	n, err := strconv.Atoi(v)
	if err != nil {
		return err
	}
	q.n, q.set = n, true
	return nil
}

type Interner struct {
	buf  []byte
	off  []uint32
	lens []uint32
	idx  map[string]uint32
	null uint32
}

func NewInterner() *Interner {
	it := &Interner{idx: make(map[string]uint32, 1<<12)}
	it.null = it.intern("\x00null")
	return it
}

func (it *Interner) intern(s string) uint32 {
	if id, ok := it.idx[s]; ok {
		return id
	}
	id := uint32(len(it.lens))
	it.off = append(it.off, uint32(len(it.buf)))
	it.lens = append(it.lens, uint32(len(s)))
	it.buf = append(it.buf, s...)
	it.idx[s] = id
	return id
}

func (it *Interner) Get(id uint32) string {
	if id == it.null || id == 0 {
		return ""
	}
	return string(it.buf[it.off[id] : it.off[id]+it.lens[id]])
}

func (it *Interner) Intern(s string) uint32 { return it.intern(s) }

func (it *Interner) Lookup(s string) (uint32, bool) {
	id, ok := it.idx[s]
	return id, ok
}

func (it *Interner) IsNull(id uint32) bool { return id == it.null || id == 0 }

func (it *Interner) Null() uint32 { return it.null }

func (it *Interner) InternOptional(s string) uint32 {
	if s == "" {
		return it.null
	}
	return it.intern(s)
}

func (it *Interner) InternBool(b bool) uint32 {
	if b {
		return it.intern("1")
	}
	return it.intern("")
}

type File struct {
	ID           int32
	ModuleID     int32
	Path         uint32
	Dir          uint32
	Basename     uint32
	Ext          uint32
	Bytes        int32
	Lines        int32
	SLOC         int32
	BlankLines   int32
	CommentLines int32
	DocLines     int32
	MaxLineLen   int32
	SHA1         uint32
	Parsed       int8
	IsTest       int8
	IsGenerated  int8
	IsVendored   int8
	ParseErrors  int32
	MissingNodes int32
	ParseMS      float64
	NSymbols     int32
	NFunctions   int32
	NTypes       int32
	NImports     int32
	TotalCyclo   int32
	MaxCyclo     int32
	TotalRisk    int32
}

type Module struct {
	ID          int32
	Name        uint32
	Kind        uint32
	NFiles      int32
	NSymbols    int32
	NPublic     int32
	SLOC        int32
	FanIn       int32
	FanOut      int32
	Instability float64
}

type Symbol struct {
	ID       int32
	FileID   int32
	ModuleID int32
	ParentID int32

	Name       uint32
	QualName   uint32
	Kind       uint32
	LineStart  int32
	LineEnd    int32
	NLines     int32
	ByteStart  int32
	ByteEnd    int32
	Signature  uint32
	ReturnType uint32
	Visibility uint32

	NParams          int32
	NOptionalParams  int32
	NGenericParams   int32
	NOverloads       int32
	ArityRank        int32
	IsPublic         int32
	IsStatic         int32
	IsAsync          int32
	IsGenerator      int32
	IsAbstract       int32
	IsOverride       int32
	IsExported       int32
	IsTest           int32
	IsDeprecated     int32
	IsEntrypoint     int32
	IsGenerated      int32
	SLOC             int32
	BodyBytes        int32
	NCommentLines    int32
	NDocLines        int32
	HasDoc           int32
	Cyclomatic       int32
	Cognitive        int32
	MaxNesting       int32
	NTokens          int32
	NOperators       int32
	NOperands        int32
	NDistinctOps     int32
	NDistinctOperand int32
	HalsteadVolume   int64
	Maintainability  int32
	NLoops           int32
	NBranches        int32
	NReturns         int32
	NEarlyReturns    int32
	NSwitch          int32
	NCases           int32
	NTernary         int32
	NLogical         int32
	NTry             int32
	NCatch           int32
	NCatchBroad      int32
	NCatchEmpty      int32
	NFinally         int32
	NThrow           int32
	NLabels          int32
	NGotos           int32
	MaxLoopDepth     int32
	CallInLoop       int32
	AllocInLoop      int32
	IOInLoop         int32
	AwaitInLoop      int32
	LockInLoop       int32
	ConcatInLoop     int32
	RegexInLoop      int32
	QueryInLoop      int32
	BranchInLoop     int32
	NLocals          int32
	NAssign          int32
	NCompoundAssign  int32
	NIncdec          int32
	NCmp             int32
	NBitop           int32
	NShift           int32
	NArith           int32
	NStringLit       int32
	NRegexLit        int32
	NFloatLit        int32
	NMagic           int32
	NNullCheck       int32
	NSubscript       int32
	NMemberAccess    int32
	NLambda          int32
	NClosureCapture  int32
	NCalls           int32
	NUniqueCalls     int32
	NDynamicCalls    int32
	NUnresolvedCalls int32
	FanIn            int32
	FanOut           int32
	NCallsites       int32
	IsRecursive      int32
	IsLeaf           int32
	IsRoot           int32
	NHazards         int32
	RiskScore        int32
	NExec            int32
	NDeserialize     int32
	NIO              int32
	NNet             int32
	NSql             int32
	NCrypto          int32
	NReflect         int32
	NConcurrency     int32
	NBlocking        int32
	NResource        int32
	NShell           int32

	NDecorators          int32
	NComprehension       int32
	NNestedComprehension int32
	NAsyncComprehension  int32
	NCompGenerators      int32
	NCompIfs             int32
	NGenexp              int32
	NYield               int32
	NYieldFrom           int32
	NAwait               int32
	NGlobalStmt          int32
	NNonlocal            int32
	NBareExcept          int32
	NCatchSwallow        int32
	NReraise             int32
	NWith                int32
	NAsyncWith           int32
	NCtxManagers         int32
	NFstring             int32
	NIsinstance          int32
	NSuper               int32
	NWalrus              int32
	NMatch               int32
	NAssert              int32
	NDel                 int32
	NPrint               int32
	NOpen                int32
	NSelfAttr            int32
	NInnerFunction       int32
	NInnerClass          int32
	NMutableDefault      int32
	NStarArgs            int32
	NKwargs              int32
	NDefaultArgs         int32
	NKwonlyArgs          int32
	NPosonlyArgs         int32
	NAnnotatedParams     int32
	NUntypedParams       int32
	HasReturnType        int32
	NAppendInLoop        int32
	LenInLoop            int32
	AppendInLoop         int32
	TryInLoop            int32
	NRangeLen            int32
	NTryInLoop           int32
	NLoopElse            int32
	NRegexCompile        int32
	NRegexCall           int32
	NSqlLiteral          int32
	NSqlFstring          int32
	NSqlConcat           int32
	NSqlFormat           int32
	NShellTrue           int32
	NAnnotatedAssign     int32
	NTryElse             int32
	NPickleLoad          int32
	NYamlLoad            int32
	NWeakRandom          int32
	NWeakHash            int32
	NEvalExec            int32
	NOSystem             int32
	NInsecureTemp        int32
	NSleepInLoop         int32
	NDynamicAttr         int32
	NDictGetInLoop       int32
	NOpenNoEncoding      int32
	NDatetime            int32
	NRequestNoTimeout    int32
	NRedirect            int32
	NAuthCall            int32
	NFetch               int32
	NXxeParser           int32
	NDynamicOpen         int32
	NUploadSave          int32
	NZipRead             int32
	NLogCall             int32
	NAssertInLoop        int32
	NSubprocess          int32
	NFormatInLoop        int32
	NElif                int32
	NExternalCalls       int32
	NLoopClosure         int32
	NBroadRaises         int32
	NAutoescapeFalse     int32
	IsProperty           int32
	IsClassmethod        int32
	IsStaticmethod       int32
	IsDunder             int32
	IsPrivate            int32
	IsOverload           int32
	IsContextmanager     int32
	IsCached             int32
	NestLevel            int32
	NOrmQueryInLoop      int32
	NCommitInLoop        int32
	NOrmWrite            int32
	NAtomic              int32
	NAwaitInSyncWith     int32
	NInScanLoop          int32
	NResourceReturn      int32
	NMarkSafe            int32
	NMassAssign          int32
	NVerifyFalse         int32
}

type Param struct {
	SymbolID     int32
	Pos          int32
	Name         uint32
	Type         uint32
	DefaultValue uint32
	IsOptional   int32
	IsVariadic   int32
	IsRef        int32
	IsMutable    int32
	IsNullable   int32
	IsGeneric    int32
	IsUntyped    int32
	TypeDepth    int32
}

type Field struct {
	SymbolID   int32
	Ordinal    int32
	Name       uint32
	Type       uint32
	Visibility uint32
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

type Import struct {
	ID         int32
	FileID     int32
	Target     uint32
	TargetID   int32
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
	SymbolID  int32
	Pattern   uint32
	Category  uint32
	N         int32
	FirstLine int32
}

type Attribute struct {
	ID       int32
	SymbolID int32
	FileID   int32
	Name     uint32
	Args     uint32
	Line     int32
}

type Literal struct {
	ID       int32
	SymbolID int32
	FileID   int32
	Kind     uint32
	Value    uint32
	Line     int32
	IsMagic  int32
}

type EnumMember struct {
	SymbolID int32
	Ordinal  int32
	Name     uint32
	Value    uint32
	NFields  int32
}

type Marker struct {
	ID       int32
	FileID   int32
	SymbolID int32
	Kind     uint32
	Line     int32
	Text     uint32
}

type Handler struct {
	ID             int32
	SymbolID       int32
	Line           int32
	Types          uint32
	IsBare         int32
	IsBroad        int32
	IsEmpty        int32
	HasReraise     int32
	HasLog         int32
	NBodyLines     int32
	InLoop         int32
	HasRaiseNoFrom int32
}

type DynamicSite struct {
	ID           int32
	SymbolID     int32
	FileID       int32
	Kind         uint32
	Expr         uint32
	Line         int32
	IsLiteralArg int32
}

type Comprehension struct {
	ID         int32
	SymbolID   int32
	FileID     int32
	Kind       uint32
	Line       int32
	NGenerator int32
	NIfs       int32
	IsAsync    int32
	InLoop     int32
}

type ModuleVar struct {
	ID                 int32
	FileID             int32
	ModuleID           int32
	Name               uint32
	Line               int32
	Type               uint32
	IsConstant         int32
	IsMutableContainer int32
	IsPrivate          int32
	HasCallInit        int32
}

type AllExport struct {
	ID     int32
	FileID int32
	Name   uint32
	Line   int32
}

type UserInputSite struct {
	ID       int32
	SymbolID int32
	FileID   int32
	Var      uint32
	Kind     uint32
	Line     int32
	InLoop   int32
}

type SecretCandidate struct {
	ID       int32
	SymbolID int32
	FileID   int32
	Value    uint32
	Line     int32
}

type APISite struct {
	ID           int32
	SymbolID     int32
	FileID       int32
	Kind         uint32
	Expr         uint32
	Line         int32
	IsLiteralArg int32
}

type ClassInfo struct {
	SymbolID      int32
	NBases        int32
	Bases         uint32
	NMethods      int32
	NClassVars    int32
	NProperties   int32
	NAbstractM    int32
	NDunder       int32
	HasSlots      int32
	HasInit       int32
	HasEq         int32
	HasHash       int32
	IsDataclass   int32
	IsABC         int32
	IsEnum        int32
	IsException   int32
	IsProtocol    int32
	IsNamedTuple  int32
	IsTypedDict   int32
	IsPydantic    int32
	IsDjangoModel int32
	IsMetaclass   int32
}

type Edge struct {
	CallerID   int32
	CalleeID   int32
	NCalls     int32
	SameFile   int32
	SameModule int32
	IsSelf     int32
}

type Callsite struct {
	CallerID int32
	CalleeID int32
	Line     int32
}

type Unresolved struct {
	CallerID  int32
	Name      uint32
	N         int32
	FirstLine int32
}

type LocalVar struct {
	SymbolID   int32
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

type Graph struct {
	Strings *Interner

	Modules []Module
	Files   []File
	Symbols []Symbol

	Params       []Param
	Fields       []Field
	Locals       []LocalVar
	Imports      []Import
	Hazards      []Hazard
	Attributes   []Attribute
	Literals     []Literal
	EnumMembers  []EnumMember
	Markers      []Marker
	Handlers     []Handler
	DynamicSites []DynamicSite
	Comprehens   []Comprehension
	ModuleVars   []ModuleVar
	AllExports   []AllExport
	InputSites   []UserInputSite
	Secrets      []SecretCandidate
	APISites     []APISite
	Classes      []ClassInfo
	Edges        []Edge
	Callsites    []Callsite
	Unresolved   []Unresolved

	Meta [][2]uint32

	callerOff []int32
	callerAdj []int32
	calleeOff []int32
	calleeAdj []int32

	fileByPath map[string]int32

	aliases map[int32]map[string]string

	byName map[string][]defSite
	byQual map[string]int32

	pendCaller []int32
	pendFile   []int32
	pendModule []int32
	pendName   []string
	pendLine   []int32
	pendClass  []string

	mutableDefaults []struct{ N, ID int32 }

	cgHeads  map[string]bool
	segments map[string]bool

	hazardImports []importHazard

	ix *idx

	nameIdx map[string][]int32

	astTrees  [][]tsRec
	keepTrees bool
}

type importHazard struct {
	fid  int32
	root string
	cat  string
	line int32
}

type defSite struct {
	sym   int32
	file  int32
	mod   int32
	class string
}

func NewGraph() *Graph {
	return &Graph{
		Strings:    NewInterner(),
		fileByPath: make(map[string]int32, 256),
		aliases:    make(map[int32]map[string]string, 256),
		byName:     make(map[string][]defSite, 4096),
		byQual:     make(map[string]int32, 4096),
	}
}

func (g *Graph) S(id uint32) string { return g.Strings.Get(id) }
func (g *Graph) I(s string) uint32  { return g.Strings.Intern(s) }

func (g *Graph) opt(s string) uint32 {
	if s == "" {
		return g.Strings.Null()
	}
	return g.Strings.Intern(s)
}

func (g *Graph) addModule(name, kind string) int32 {
	for i := range g.Modules {
		if g.S(g.Modules[i].Name) == name {
			return g.Modules[i].ID
		}
	}
	id := int32(len(g.Modules) + 1)
	g.Modules = append(g.Modules, Module{ID: id, Name: g.I(name), Kind: g.I(kind)})
	return id
}

func (g *Graph) addFile(path string) int32 {
	id := int32(len(g.Files) + 1)
	g.Files = append(g.Files, File{ID: id, ModuleID: -1})
	g.fileByPath[path] = id
	return id
}

type measure struct {
	src []byte
	m   map[string]int32

	ops      map[string]int32
	operands map[string]int32

	depth        int32
	maxNesting   int32
	loopDepth    int32
	maxLoopDepth int32
	syncWith     int32
	tryDepth     int32
	cognitive    int32
	cyclomatic   int32

	calls    []callSite
	literals []litSite
	inputs   []inputSite
	secrets  []secretSite
	comps    []compSite

	awaitsInLoop int32
	classStack   []string
	storeNames   map[string]bool
	pruneDefs    bool

	root tsNode
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

type inputSite struct {
	line   int32
	varnm  string
	kind   string
	inLoop int32
}

type secretSite struct {
	value string
	line  int32
}

type compSite struct {
	kind  string
	line  int32
	gens  int32
	ifs   int32
	async int32
}

var measurePool = sync.Pool{New: func() any { return &measure{} }}

func newMeasure(classStack []string, pruneDefs bool) *measure {
	x := measurePool.Get().(*measure)
	if x.m == nil {
		x.m = make(map[string]int32, 64)
		x.ops = make(map[string]int32, 16)
		x.operands = make(map[string]int32, 16)
		x.storeNames = make(map[string]bool, 16)
	}
	x.cyclomatic = 1
	x.maxNesting, x.maxLoopDepth, x.syncWith, x.tryDepth, x.cognitive = 0, 0, 0, 0, 0
	x.depth, x.loopDepth = 0, 0
	x.awaitsInLoop = 0
	x.pruneDefs = pruneDefs
	x.classStack = classStack
	for k := range x.m {
		delete(x.m, k)
	}
	for k := range x.ops {
		delete(x.ops, k)
	}
	for k := range x.operands {
		delete(x.operands, k)
	}
	for k := range x.storeNames {
		delete(x.storeNames, k)
	}
	x.calls = x.calls[:0]
	x.literals = x.literals[:0]
	x.inputs = x.inputs[:0]
	x.secrets = x.secrets[:0]
	x.comps = x.comps[:0]
	return x
}

func freeMeasure(x *measure) {
	if os.Getenv("NOPOOL") == "" {
		measurePool.Put(x)
	}
}

func (x *measure) bump(k string)           { x.bumpN(k, 1) }
func (x *measure) bumpN(k string, n int32) { x.m[k] += n }

func line1(n tsNode) int32 { return int32(startRow(n) + 1) }

func (x *measure) walk(n tsNode) {
	if !hasNode(n) {
		return
	}
	k := kindID(n)

	if x.pruneDefs {
		switch k {
		case kFunctionDef, kClassDef, kDecoratedDef:
			return
		}
	}
	nested := false
	switch k {

	case kIfStmt, kForStmt, kWhileStmt, kWithStmt, kMatchStmt, kFunctionDef,
		kClassDef:
		nested = !sameNode(n, x.root) && !x.inElifPosition(n)
	case kTryStmt:
		nested = !sameNode(n, x.root) && !x.isTryStar(n)
	}
	loop := false
	switch k {
	case kForStmt, kWhileStmt:
		loop = true
	}
	if nested {
		x.depth++
		if x.depth > x.maxNesting {
			x.maxNesting = x.depth
		}
	}
	if loop {
		x.loopDepth++
		if x.loopDepth > x.maxLoopDepth {
			x.maxLoopDepth = x.loopDepth
		}
		x.cyclomatic++
		x.cognitive += maxI32(1, x.depth)
		x.bump("n_loops")
		if x.hasClause(n, kElseClause) {
			x.bump("n_loop_else")
		}
	}

	syncWith := k == kWithStmt && !isAsync(n, x.src)
	if syncWith {
		x.syncWith++
	}
	x.measureNode(n)

	eachNamedChild(n, func(c tsNode) { x.walk(c) })
	if syncWith {
		x.syncWith--
	}
	if loop {
		x.loopDepth--
	}
	if nested {
		x.depth--
	}
}

func (x *measure) hasClause(n tsNode, kind uint16) bool {
	found := false
	forEachNamed(n, func(c tsNode) {
		if kindID(c) == kind {
			found = true
		}
	})
	return found
}

func isAliasHead(n tsNode) bool {
	p := parentNode(n)
	if !hasNode(p) || kindID(p) != kType {
		return false
	}
	gp := parentNode(p)
	if !hasNode(gp) || kindID(gp) != kTypeAlias {
		return false
	}
	has := false
	forEachNamed(n, func(c tsNode) {
		if kindID(c) == kTypeParam {
			has = true
		}
	})
	return has
}

func (x *measure) inElifPosition(n tsNode) bool {
	if kindID(n) != kIfStmt {
		return false
	}
	blk := parentNode(n)
	if !hasNode(blk) || kindID(blk) != kBlock {
		return false
	}
	p := parentNode(blk)

	if !hasNode(p) || kindID(p) != kElseClause {
		return false
	}
	if kindID(parentNode(p)) != kIfStmt {
		return false
	}
	count := 0
	only := false
	forEachNamed(blk, func(c tsNode) {
		count++
		if sameNode(c, n) {
			only = true
		}
	})
	return count == 1 && only
}

func (x *measure) isTryStar(n tsNode) bool {
	exc := firstChildOfKind(n, kExceptClause)
	if !hasNode(exc) {
		return false
	}
	return childIsToken(exc, 1, "*", x.src)
}

func (x *measure) measureNode(n tsNode) {
	depth, loopDepth := x.depth, x.loopDepth
	k := kindID(n)
	switch k {
	case kString:

		if kindID(parentNode(n)) == kConcatString {
			return
		}
		x.stringConst(n)
	case kConcatString:
		x.stringConst(n)
	case kIdentifier:

		if !nameSlot(x.src, n) {
			x.operands[nodeText(x.src, n)]++
		}
	case kInteger:
		v, big, ok := cgIntVal(nodeText(x.src, n))
		if !ok {
			break
		}
		x.operands[trunc40(bigDec(v, big))]++
		if big == "" && magicOK[v] {
			break
		}
		x.bump("n_magic")
		x.literals = append(x.literals, litSite{kind: "number",
			value: bigDec(v, big), line: line1(n), magic: true})
	case kFloat:
		body, imag := cgFloatText(nodeText(x.src, n))
		if imag {
			if f, err := strconv.ParseFloat(body, 64); err == nil {
				x.operands[trunc40(reprImaginary(f))]++
			} else {
				x.operands[trunc40(body)]++
			}
			break
		}
		x.bump("n_float_lit")
		if f, err := strconv.ParseFloat(body, 64); err == nil {
			x.operands[trunc40(floatText(f))]++
		} else {
			x.operands[trunc40(body)]++
		}
	case kTrue:
		x.operands["True"]++
	case kFalse:
		x.operands["False"]++
	case kNone:
		x.operands["None"]++
	case kEllipsis:

		x.operands["Ellipsis"]++
	case kIfStmt, kCondExpr:
		x.cyclomatic++
		if x.inElifPosition(n) {

			x.cognitive++
			x.bump("n_elif")
		} else {
			x.cognitive += maxI32(1, depth)
		}
		x.bump("n_branches")
		if k == kCondExpr {
			x.bump("n_ternary")
		}
		if loopDepth > 0 {
			x.bump("branch_in_loop")
		}
	case kElifClause:

		x.cyclomatic++
		x.cognitive++
		x.bump("n_branches")
		x.bump("n_elif")
		if loopDepth > 0 {
			x.bump("branch_in_loop")
		}
	case kMatchStmt:
		x.bump("n_switch")
		nc := int32(countOfKind(n, kCaseClause))
		if body := fieldNode(n, fBody); hasNode(body) {

			nc += int32(countOfKind(body, kCaseClause))
		}
		x.bumpN("n_cases", nc)
		x.cyclomatic += nc
		x.bump("n_match")
	case kBoolOp:
		x.cyclomatic++
		x.bumpN("n_logical", 1)
	case kCompareOp:
		x.compare(n, loopDepth)
	case kReturnStmt:
		x.bump("n_returns")
		if depth > 0 {
			x.bump("n_early_returns")
		}
		if v := returnValue(x.src, n); hasNode(v) {
			escapes := false
			walkSubtree(v, func(c tsNode) {
				if escapes || kindID(c) != kCall {
					return
				}
				base := lastDot(dotted(x.src, fieldNode(c, fFunction)))
				if resourceReturns[base] {
					escapes = true
				}
			})
			if escapes {
				x.bump("n_resource_return")
			}
		}
	case kRaiseStmt:
		x.bump("n_throw")
		if !hasNode(firstNamed(n)) {
			x.bump("n_reraise")
		}
	case kTryStmt:
		x.bump("n_try")
		if x.hasClause(n, kFinallyClause) {
			x.bump("n_finally")
		}
		if x.hasClause(n, kElseClause) {
			x.bump("n_try_else")
		}
		if loopDepth > 0 {
			x.bump("try_in_loop")
		}
	case kExceptClause:
		x.except(n, depth)
	case kWithStmt:
		x.bump("n_with")
		x.bumpN("n_ctx_managers", int32(x.withItemCount(n)))
		if isAsync(n, x.src) {
			x.bump("n_async_with")
		}

		var storeItems func(cn tsNode)
		storeItems = func(cn tsNode) {
			forEachNamed(cn, func(c tsNode) {
				switch kindID(c) {
				case kWithItem:
					if ap := fieldNode(c, fValue); kindID(ap) == kAsPattern {
						x.addStore(fieldNode(ap, fAlias))
					}
				case kWithClause:
					storeItems(c)
				}
			})
		}
		storeItems(n)
	case kAssertStmt:
		x.bump("n_assert")
		x.cyclomatic++
	case kGlobalStmt:
		x.bumpN("n_global_stmt", int32(countOfKind(n, kIdentifier)))
	case kNonlocalStmt:
		x.bumpN("n_nonlocal", int32(countOfKind(n, kIdentifier)))
	case kAwait:
		x.bump("n_await")
		if loopDepth > 0 {
			x.bump("await_in_loop")
		}
		if x.syncWith > 0 {

			x.bump("n_await_in_sync_with")
		}
	case kYield:
		x.bump("n_yield")
		if hasTokenChild(x.src, n, "from") {
			x.bump("n_yield_from")
		}
	case kLambda:
		x.bump("n_lambda")
		if loopDepth > 0 {

			x.bump("n_loop_closure")
		}
	case kNamedExpr:
		x.bump("n_walrus")
		x.addStore(fieldNode(n, fName))
	case kDeleteStmt:
		x.bumpN("n_del", int32(deleteTargetCount(n)))
	case kListComp, kSetComp, kDictComp, kGenExp:
		x.comprehension(n)
	case kAssignment:

		if kindID(parentNode(n)) == kAssignment {
			break
		}
		x.bumpN("n_assign", int32(assignChainLen(n)))
		if hasNode(fieldNode(n, fType)) {
			x.bump("n_annotated_assign")
		}
		x.stringBuild(n)
		x.addStoresOfAssign(n)
	case kAugAssignment:
		x.bump("n_compound_assign")

		if opText(x.src, fieldNode(n, fOperator)) == "+=" && loopDepth > 0 {
			x.bump("concat_in_loop")
		}
		x.addStore(fieldNode(n, fLeft))
	case kSubscript, kGenericType:

		if k == kGenericType && isAliasHead(n) {

			break
		}
		x.bump("n_subscript")
	case kAttribute:
		x.attribute(n, loopDepth)
	case kBinaryOp:
		switch opText(x.src, fieldNode(n, fOperator)) {
		case "+", "-", "*", "/", "//", "%", "**", "@":
			x.bump("n_arith")
		case "&", "|", "^":
			x.bump("n_bitop")
		case "<<", ">>":
			x.bump("n_shift")
		}
	case kUnionType:

		x.bump("n_bitop")
	case kInterpolation:

		if hasNode(fieldNode(n, fFormatSpec)) {
			x.bump("n_fstring")
		}
	case kCall:
		x.call(n)
	case kClassDef:
		if !sameNode(n, x.root) {
			x.bump("n_inner_class")
		}
	case kFunctionDef:
		if !sameNode(n, x.root) {
			x.bump("n_inner_function")
			if loopDepth > 0 {
				x.bump("n_loop_closure")
			}
		}
	case kForIn:

		x.addStore(fieldNode(n, fLeft))
	case kForStmt:
		x.addStore(fieldNode(n, fLeft))
	}

	if opKey, ok := x.operatorKey(k, n); ok {
		x.ops[opKey]++
	}
}

func (x *measure) operatorKey(k uint16, n tsNode) (string, bool) {
	switch k {
	case kBinaryOp, kUnionType:

		return "BinOp", true
	case kUnaryOp, kNotOp:
		return "UnaryOp", true
	case kBoolOp:

		if p := parentNode(n); kindID(p) == kBoolOp &&
			nodeText(x.src, boolOpToken(p)) == nodeText(x.src, boolOpToken(n)) {
			return "", false
		}
		return "BoolOp", true
	case kCompareOp:
		return "Compare", true
	case kAugAssignment:
		return "AugAssign", true
	case kAssignment:

		if hasNode(fieldNode(n, fType)) {
			return "", false
		}

		if kindID(parentNode(n)) == kAssignment {
			return "", false
		}
		return "Assign", true
	case kSubscript, kGenericType:

		return "Subscript", true
	case kAttribute:
		return "Attribute", true
	case kCall:
		return "Call", true
	case kAwait:
		return "Await", true
	case kYield:
		if hasTokenChild(x.src, n, "from") {
			return "YieldFrom", true
		}
		return "Yield", true
	case kNamedExpr:
		return "NamedExpr", true
	case kListSplat:

		return "Starred", true
	case kStarParam:

		if isForTargetPattern(n) {
			return "Starred", true
		}
		return "", false
	case kSlice:
		return "Slice", true
	}
	return "", false
}

var patternKindIDs = func() map[uint16]bool {
	out := map[uint16]bool{}
	for _, nm := range []string{"class_pattern", "dict_pattern", "keyword_pattern",
		"list_pattern", "tuple_pattern", "splat_pattern",
		"case_pattern", "dotted_name"} {
		out[kindOf(nm)] = true
	}
	return out
}()

func nameSlot(src []byte, id tsNode) bool {
	p := parentNode(id)
	if !hasNode(p) {
		return false
	}
	pk := kindID(p)
	switch pk {
	case kAttribute:
		return sameNode(id, fieldNode(p, fAttribute))
	case kKeywordArg:
		return sameNode(id, fieldNode(p, fName))
	case kFunctionDef, kClassDef:
		return sameNode(id, fieldNode(p, fName))
	case kDottedName:

		gp := parentNode(p)
		if hasNode(gp) && kindID(gp) == kClassPattern {
			return false
		}
		return true
	case kParams, kLambdaPs, kGlobalStmt, kNonlocalStmt,
		kAliasedImport, kTypeParam:
		return true
	case kTypedParam, kDefaultParam, kTypedDefaultParam:

		if nm := fieldNode(p, fName); hasNode(nm) {
			return sameNode(id, nm)
		}

		return sameNode(id, firstNamed(p))
	case kStarParam, kDStarParam:

		return !isForTargetPattern(id)
	case kAsPattern:

		if !sameNode(id, fieldNode(p, fAlias)) {
			return false
		}
		gp := parentNode(p)
		return kindID(gp) != kWithItem
	case kAsPatternTgt:

		ap := parentNode(p)
		if !hasNode(ap) || kindID(ap) != kAsPattern {
			return true
		}
		return kindID(parentNode(ap)) != kWithItem
	case kTuplePattern, kListPattern, kPatternList:

		return !isForTargetPattern(id)
	}
	if patternKindIDs[pk] {
		return true
	}
	return false
}

func isForTargetPattern(id tsNode) bool {
	cur := parentNode(id)
	for hasNode(cur) {
		switch kindID(cur) {
		case kTuplePattern, kListPattern, kPatternList, kParenExpr,
			kStarParam, kDStarParam:

			cur = parentNode(cur)
		case kForStmt, kForIn, kAssignment:

			return true
		default:
			return false
		}
	}
	return false
}

func (x *measure) stringConst(n tsNode) {
	if kindID(n) == kString {
		x.oneString(n)
		return
	}

	type piece struct {
		text string
		line int32
		fld  bool
	}
	var pieces []piece
	anyF := false
	forEachNamed(n, func(c tsNode) {
		if kindID(c) != kString {
			return
		}
		if !x.isBytes(c) && !hasInterpolation(c) {
			if v, ok := cgStrVal(x.src, c); ok {
				pieces = append(pieces, piece{text: v, line: line1(c)})
			}
			return
		}
		if hasInterpolation(c) {
			anyF = true
			raw := x.rawString(c)
			forEachNamed(c, func(cc tsNode) {
				switch kindID(cc) {
				case kStringContent:
					txt := cgUnescape(nodeText(x.src, cc), !raw)
					pieces = append(pieces, piece{text: cgFStringBraces(txt), line: line1(cc)})
				case kInterpolation:
					pieces = append(pieces, piece{fld: true, line: line1(cc)})
					x.specConstants(cc)
				}
			})
			return
		}

		if v, ok := cgStrVal(x.src, c); ok {
			pieces = append(pieces, piece{text: "\x00bytes\x00" + v, line: line1(c)})
		}
	})
	if anyF {
		x.bump("n_fstring")
	} else if len(pieces) == 1 {
		x.strConstant(pieces[0].text, pieces[0].line)
		return
	}

	merge := strings.Builder{}
	mergeLine := int32(0)
	had := false
	flush := func() {
		if had {
			t := merge.String()
			if strings.HasPrefix(t, "\x00bytes\x00") {
				x.operands[trunc40(bytesRepr(t[8:]))]++
			} else {
				x.strConstant(t, mergeLine)
			}
			merge.Reset()
			had = false
		}
	}
	for _, pc := range pieces {
		if pc.fld {
			flush()
			continue
		}
		if !had {
			mergeLine = pc.line
			had = true
		}
		merge.WriteString(pc.text)
	}
	flush()
}

func (x *measure) oneString(n tsNode) {
	if x.isBytes(n) {

		if v, ok := cgStrVal(x.src, n); ok {
			x.operands[trunc40(bytesRepr(v))]++
		}
		return
	}
	if hasInterpolation(n) {
		x.bump("n_fstring")
		x.fstringSegments(n)
	} else if v, ok := cgStrVal(x.src, n); ok {
		x.strConstant(v, line1(n))
	}
}

func (x *measure) specConstants(interp tsNode) {
	fs := fieldNode(interp, fFormatSpec)
	if !hasNode(fs) {
		return
	}

	t := nodeText(x.src, fs)
	t = strings.TrimPrefix(t, ":")
	forEachNamed(fs, func(c tsNode) {
		if kindID(c) == kFormatExpr {
			s, e := startByte(c), endByte(c)
			if s <= e && e <= uint(len(x.src)) {
				span := string(x.src[s:e])
				t = strings.Replace(t, span, "", 1)
			}
		}
	})
	if t != "" {
		x.strConstant(t, line1(fs))
	}
}

func (x *measure) isBytes(n tsNode) bool {
	st := firstChildOfKind(n, kStringStart)
	if !hasNode(st) {
		return false
	}
	p := nodeText(x.src, st)
	return strings.ContainsRune(p, 'b') || strings.ContainsRune(p, 'B')
}

func hasInterpolation(n tsNode) bool { return hasNode(firstChildOfKind(n, kInterpolation)) }

func reprImaginary(f float64) string {
	s := floatText(f)
	if strings.HasSuffix(s, ".0") {
		return s[:len(s)-2] + "j"
	}
	return s + "j"
}

func (x *measure) fstringSegments(n tsNode) {
	raw := x.rawString(n)
	forEachNamed(n, func(c tsNode) {
		switch kindID(c) {
		case kStringContent:
			txt := cgUnescape(nodeText(x.src, c), !raw)
			x.strConstant(cgFStringBraces(txt), line1(c))
		case kInterpolation:

			x.specConstants(c)
		}
	})
}

func (x *measure) rawString(n tsNode) bool {
	st := firstChildOfKind(n, kStringStart)
	if !hasNode(st) {
		return false
	}
	p := nodeText(x.src, st)
	return strings.ContainsRune(p, 'r') || strings.ContainsRune(p, 'R')
}

func (x *measure) strConstant(v string, line int32) {
	x.bump("n_string_lit")

	if len(v) >= 6 && sqlKeywordHit(v) {
		x.bump("n_sql_literal")
		if x.loopDepth > 0 {
			x.bump("query_in_loop")
		}
	}
	x.operands[trunc40(cgRepr(v))]++
	if len(v) >= secretMinLen && !strings.Contains(v, " ") && secretKeywordHit(v) {
		x.secrets = append(x.secrets, secretSite{value: truncStr(v, 200), line: line})
	}
}

func bytesRepr(v string) string {
	q := byte('\'')
	if strings.IndexByte(v, '\'') >= 0 && strings.IndexByte(v, '"') < 0 {
		q = '"'
	}
	var b strings.Builder
	b.WriteByte('b')
	b.WriteByte(q)
	for i := 0; i < len(v); i++ {
		c := v[i]
		switch {
		case c == q || c == '\\':
			b.WriteByte('\\')
			b.WriteByte(c)
		case c == '\n':
			b.WriteString(`\n`)
		case c == '\t':
			b.WriteString(`\t`)
		case c == '\r':
			b.WriteString(`\r`)
		case c < 0x20 || c >= 0x7f:
			const hex = "0123456789abcdef"
			b.WriteString(`\x`)
			b.WriteByte(hex[c>>4])
			b.WriteByte(hex[c&0xf])
		default:
			b.WriteByte(c)
		}
	}
	b.WriteByte(q)
	return b.String()
}

func (x *measure) compare(n tsNode, loopDepth int32) {
	ops := 0
	inScan, noneCmp := false, false
	var operands []tsNode
	for c := firstChildN(n); hasNode(c); c = nextSiblingOf(c) {
		if isNamedN(c) {
			operands = append(operands, c)
			continue
		}
		ops++
		switch nodeText(x.src, c) {
		case "in", "not in":
			inScan = true
		case "is", "is not", "==", "!=":
			noneCmp = true
		}
	}
	x.bumpN("n_cmp", int32(ops))

	if loopDepth > 0 && inScan {

		constCmp := false
		for i, c := range operands {
			if i == 0 {
				continue
			}
			switch kindID(c) {
			case kIdentifier, kAttribute, kSubscript:
				constCmp = true
			}
		}
		if constCmp {
			x.bump("n_in_scan_loop")
		}
	}
	if noneCmp {
		for _, c := range operands {
			if kindID(c) == kNone {
				x.bump("n_null_check")
			}
		}
	}
}

func (x *measure) except(n tsNode, depth int32) {
	x.bump("n_catch")
	x.cyclomatic++
	x.cognitive += maxI32(1, depth)
	tv := fieldNode(n, fValue)
	typ := exceptTypeOf(x.src, n)
	if !hasNode(tv) {
		x.bump("n_bare_except")
		x.bump("n_catch_broad")
	} else if broadExceptions[typ] {
		x.bump("n_catch_broad")
	}
	body := firstChildOfKind(n, kBlock)
	if hasNode(body) {
		if single, ok := singleStmt(body); ok {
			switch kindID(single) {
			case kPassStmt:
				x.bump("n_catch_empty")
			default:
				if kindID(single) == kExprStmt && childCount(single) == 2 &&
					isConstKind(childAt(single, 1)) {
					x.bump("n_catch_empty")
				}
			}
		}
	}
	reraises := false
	walkSubtree(n, func(c tsNode) {
		if kindID(c) == kRaiseStmt || kindID(c) == kReturnStmt {
			reraises = true
		}
	})
	if !reraises {
		x.bump("n_catch_swallow")
	}
}

func singleStmt(body tsNode) (tsNode, bool) {
	first := tsNode{}
	seen := 0
	forEachNamed(body, func(c tsNode) {
		seen++
		if seen == 1 {
			first = c
		}
	})
	if seen == 1 {
		return first, true
	}
	return tsNode{}, false
}

func isConstKind(n tsNode) bool {
	switch kindID(n) {
	case kString:
		return !hasInterpolation(n)
	case kConcatString:
		constant := true
		forEachNamed(n, func(c tsNode) {
			if kindID(c) == kString && hasInterpolation(c) {
				constant = false
			}
		})
		return constant
	case kInteger, kFloat, kTrue, kFalse, kNone, kEllipsis:
		return true
	}
	return false
}

func (x *measure) comprehension(n tsNode) {
	x.bump("n_comprehension")
	gens := 0
	ifs := int32(0)
	anyAsync := false
	forEachNamed(n, func(c tsNode) {
		switch kindID(c) {
		case kForIn:
			gens++
			if isAsync(c, x.src) {
				anyAsync = true
				x.bump("n_async_comprehension")
			}
		case kIfClause:
			ifs++
		}
	})
	x.bumpN("n_comp_generators", int32(gens))
	if gens > 1 {
		x.bump("n_nested_comprehension")
	}
	x.bumpN("n_comp_ifs", ifs)
	var kind string
	switch kindID(n) {
	case kListComp:
		kind = "list"
	case kSetComp:
		kind = "set"
	case kDictComp:
		kind = "dict"
	case kGenExp:
		kind = "genexp"
		x.bump("n_genexp")
	}
	x.comps = append(x.comps, compSite{kind: kind, line: line1(n),
		gens: int32(gens), ifs: ifs, async: b2i32(anyAsync)})
}

func (x *measure) stringBuild(n tsNode) {
	if x.loopDepth == 0 {
		return
	}
	right := fieldNode(n, fRight)
	if kindID(right) != kBinaryOp || opText(x.src, fieldNode(right, fOperator)) != "+" {
		return
	}
	tgt := fieldNode(n, fLeft)
	if kindID(tgt) != kIdentifier {
		return
	}
	l := fieldNode(right, fLeft)
	if kindID(l) == kIdentifier && nodeText(x.src, l) == nodeText(x.src, tgt) {
		x.bump("concat_in_loop")
	}
}

func (x *measure) attribute(n tsNode, loopDepth int32) {
	x.bump("n_member_access")
	obj := fieldNode(n, fObject)
	attr := nodeText(x.src, fieldNode(n, fAttribute))
	if kindID(obj) == kIdentifier && nodeText(x.src, obj) == "self" {
		x.bump("n_self_attr")
	}
	kind, isInput := reqInputKinds[attr]
	if !isInput {
		return
	}
	var varnm string
	switch {
	case kindID(obj) == kIdentifier && nodeText(x.src, obj) == "request":
		varnm = "request." + attr
	case kindID(obj) == kAttribute &&
		nodeText(x.src, fieldNode(obj, fAttribute)) == "request" &&
		kindID(fieldNode(obj, fObject)) == kIdentifier &&
		nodeText(x.src, fieldNode(obj, fObject)) == "self":
		varnm = "self.request." + attr
	}
	if varnm != "" {
		x.inputs = append(x.inputs, inputSite{line: line1(n),
			varnm: truncStr(varnm, 120), kind: kind, inLoop: b2i32(loopDepth > 0)})
	}
}

func (x *measure) addStore(n tsNode) {
	if !hasNode(n) {
		return
	}
	switch kindID(n) {
	case kIdentifier:
		x.storeNames[nodeText(x.src, n)] = true
	case kExprList, kTuple, kList, kPatternList, kParenExpr,
		kTuplePattern, kListPattern, kAsPatternTgt, kStarParam, kDStarParam:

		forEachNamed(n, x.addStore)
	}
}

func (x *measure) addStoresOfAssign(n tsNode) {
	for hasNode(n) && kindID(n) == kAssignment {
		x.addStore(fieldNode(n, fLeft))
		n = fieldNode(n, fRight)
	}
}

func assignChainLen(n tsNode) int {
	c := 0
	for hasNode(n) && kindID(n) == kAssignment {
		c++
		n = fieldNode(n, fRight)
	}
	if c == 0 {
		return 1
	}
	return c
}

func deleteTargetCount(n tsNode) int {
	if lst := firstChildOfKind(n, kExprList); hasNode(lst) {
		c := 0
		forEachNamed(lst, func(tsNode) { c++ })
		return c
	}
	return 1
}

func walkSubtree(n tsNode, fn func(tsNode)) {
	if !hasNode(n) {
		return
	}
	fn(n)
	for c := firstChildN(n); hasNode(c); c = nextSiblingOf(c) {
		if isNamedN(c) && kindID(c) != kComment {
			walkSubtree(c, fn)
		}
	}
}

var pickleCalls = map[string]bool{
	"pickle.load": true, "pickle.loads": true, "cPickle.load": true,
	"cPickle.loads": true, "dill.load": true, "dill.loads": true,
	"shelve.open": true,
}

var yamlCalls = map[string]bool{
	"yaml.load": true, "yaml.unsafe_load": true, "yaml.full_load": true,
}

var noTimeoutCalls = map[string]bool{
	"requests.get": true, "requests.post": true, "requests.put": true,
	"requests.delete": true, "requests.patch": true, "requests.head": true,
	"requests.request": true, "urllib.request.urlopen": true,
}

var naiveDatetimeCalls = map[string]bool{
	"datetime.datetime.now": true, "datetime.now": true,
	"datetime.datetime.utcnow": true, "datetime.utcnow": true,
}

var subprocessCalls = map[string]bool{
	"subprocess.run": true, "subprocess.call": true,
	"subprocess.check_output": true, "subprocess.Popen": true,
	"subprocess.check_call": true,
}

func callArgs(src []byte, n tsNode) (pos []tsNode, kws []kwArg) {
	al := fieldNode(n, fArguments)
	if !hasNode(al) {
		return nil, nil
	}
	forEachNamed(al, func(c tsNode) {
		switch kindID(c) {
		case kKeywordArg:
			kws = append(kws, kwArg{
				name:  nodeText(src, fieldNode(c, fName)),
				value: fieldNode(c, fValue),
			})
		case kDictSplat:
			kws = append(kws, kwArg{value: firstNamed(c)})
		default:
			pos = append(pos, c)
		}
	})
	return pos, kws
}

type kwArg struct {
	name  string
	value tsNode
}

func (x *measure) call(n tsNode) {
	x.bump("n_calls")
	fn := callFunc(n)
	name := dotted(x.src, fn)
	line := line1(n)
	dynamic := name == ""

	pos, kws := callArgs(x.src, n)

	if x.loopDepth > 0 {
		x.bump("call_in_loop")
	}
	base := ""
	if name != "" {
		base = lastDot(name)
	} else if kindID(fn) == kAttribute {
		base = nodeText(x.src, fieldNode(fn, fAttribute))
	}
	if base == "save" {

		seen := strings.Contains(name, "files") || strings.Contains(name, "FILES")
		cur := fn
		for !seen && hasNode(cur) && (kindID(cur) == kAttribute || kindID(cur) == kSubscript) {
			if kindID(cur) == kAttribute {
				if a := nodeText(x.src, fieldNode(cur, fAttribute)); a == "files" || a == "FILES" {
					seen = true
				}
			}
			cur = fieldNode(cur, fObject)
		}
		if seen {
			x.bump("n_upload_save")
		}
	}
	if name == "" {
		x.bump("n_dynamic_calls")
		x.calls = append(x.calls, callSite{name: "", line: line, dynamic: true})
		return
	}
	lower := strings.ToLower(name)
	if base == "redirect" || base == "redirect_to" {
		x.bump("n_redirect")
	}
	if base == "urlopen" || hasPrefixAny(name, fetchPrefixes) {
		x.bump("n_fetch")
	}
	if hasPrefixAny(name, xxePrefixes) {
		x.bump("n_xxe_parser")
	}
	if base == "open" && len(pos) > 0 && !isConstKind(pos[0]) {
		x.bump("n_dynamic_open")
	}
	if strings.HasPrefix(name, zipPrefix) {
		x.bump("n_zip_read")
	}
	if logLevels[base] && (strings.Contains(name, "logging.") || strings.Contains(name, "logger")) {
		x.bump("n_log_call")
	}
	if containsAny(lower, authMarkers) {
		x.bump("n_auth_call")
	}
	if base == "raises" && strings.HasPrefix(name, "pytest.") && len(pos) > 0 &&
		kindID(pos[0]) == kIdentifier {
		id := nodeText(x.src, pos[0])
		if id == "Exception" || id == "BaseException" {
			x.bump("n_broad_raises")
		}
	}
	if base == "Environment" && strings.HasSuffix(name, "Environment") {
		for _, kw := range kws {
			if kw.name == "autoescape" && kindID(kw.value) == kFalse {
				x.bump("n_autoescape_false")
			}
		}
	}
	if (base == "append" || base == "extend" || base == "insert") && x.loopDepth > 0 {
		x.bump("append_in_loop")
	}
	switch {
	case base == "compile" && (strings.HasPrefix(name, "re.") || strings.HasPrefix(name, "regex.")):
		x.bump("n_regex_compile")
		if x.loopDepth > 0 {
			x.bump("regex_in_loop")
		}
	case strings.HasPrefix(name, "re.") || strings.HasPrefix(name, "regex."):
		x.bump("n_regex_call")
		if x.loopDepth > 0 {
			x.bump("regex_in_loop")
		}
	}
	if base == "isinstance" {
		x.bump("n_isinstance")
	}
	if base == "super" {
		x.bump("n_super")
	}
	if base == "len" && x.loopDepth > 0 {
		x.bump("len_in_loop")
	}
	if name == "range" && len(pos) > 0 {
		for _, a := range pos {
			if kindID(a) == kCall && dotted(x.src, fieldNode(a, fFunction)) == "len" {
				x.bump("n_range_len")
			}
		}
	}
	if base == "open" {
		x.bump("n_open")
	}
	if base == "print" {
		x.bump("n_print")
	}
	if pickleCalls[name] {
		x.bump("n_pickle_load")
	}
	if yamlCalls[name] {
		x.bump("n_yaml_load")
	}
	if strings.HasPrefix(name, "random.") && base != "SystemRandom" {
		x.bump("n_weak_random")
	}
	if name == "hashlib.md5" || name == "hashlib.sha1" || name == "md5.new" {
		x.bump("n_weak_hash")
	}
	if (base == "eval" || base == "exec" || base == "compile") &&
		!strings.HasPrefix(name, "re.") {
		x.bump("n_eval_exec")
	}
	if name == "os.system" || name == "os.popen" || name == "commands.getoutput" {
		x.bump("n_os_system")
	}
	if strings.HasPrefix(name, "tempfile.mktemp") {
		x.bump("n_insecure_temp")
	}
	if (name == "time.sleep" || name == "asyncio.sleep") && x.loopDepth > 0 {
		x.bump("n_sleep_in_loop")
	}
	if (base == "getattr" || base == "setattr" || base == "delattr" || base == "hasattr") &&
		len(pos) > 1 && !isConstKind(pos[1]) {
		x.bump("n_dynamic_attr")
	}
	if base == "get" && x.loopDepth > 0 {
		x.bump("n_dict_get_in_loop")
	}
	if base == "open" && !hasKeywordArg(kws, "encoding") {
		x.bump("n_open_no_encoding")
	}
	if naiveDatetimeCalls[name] && len(pos) == 0 && len(kws) == 0 {
		x.bump("n_naive_datetime")
	}
	if noTimeoutCalls[name] && !hasKeywordArg(kws, "timeout") {
		x.bump("n_request_no_timeout")
	}
	if (base == "assertEquals" || base == "assertEqual") && x.loopDepth > 0 {
		x.bump("n_assert_in_loop")
	}
	if subprocessCalls[name] {
		x.bump("n_subprocess")
	}
	if base == "format" && x.loopDepth > 0 {
		x.bump("n_format_in_loop")
	}
	if x.loopDepth > 0 {
		if cat, ok := hazardCalls[name]; ok {
			switch cat {
			case "io", "net", "sql":
				x.bump("io_in_loop")
			}
			if cat == "sql" {
				x.bump("query_in_loop")
			}
		}
	}
	if base == "acquire" && x.loopDepth > 0 {
		x.bump("lock_in_loop")
	}
	if strings.HasPrefix(name, "subprocess.") || name == "os.popen" {
		for _, kw := range kws {
			if kw.name == "shell" && kindID(kw.value) == kTrue {
				x.bump("n_shell_true")
			}
		}
	}
	if base == "execute" || base == "executemany" || base == "raw" || base == "extra" {
		if len(pos) > 0 {
			a := pos[0]
			switch kindID(a) {
			case kString:
				if hasInterpolation(a) {
					x.bump("n_sql_fstring")
				}
			case kBinaryOp:
				switch opText(x.src, fieldNode(a, fOperator)) {
				case "+", "%":
					x.bump("n_sql_concat")
				}
			case kCall:
				if strings.HasSuffix(dotted(x.src, callFunc(a)), ".format") {
					x.bump("n_sql_format")
				}
			}
		}
	}
	if x.loopDepth > 0 && strings.Contains(name, ".") && querysetReads[base] &&
		(base != "get" || strings.Contains(name, "objects")) {
		x.bump("n_orm_query_in_loop")
	}
	if x.loopDepth > 0 && base == "commit" {
		x.bump("n_commit_in_loop")
	}
	if strings.Contains(name, ".") && (ormWriteMethods[base] ||
		(ormWriteGated[base] && (strings.Contains(name, "objects") ||
			strings.Contains(name, "instance") || strings.HasPrefix(name, "self.")))) {
		x.bump("n_orm_write")
	}
	if base == "atomic" || strings.HasSuffix(name, ".atomic") {
		x.bump("n_atomic")
	}
	if name == "mark_safe" || strings.HasSuffix(name, ".mark_safe") {
		x.bump("n_mark_safe")
	}
	for _, kw := range kws {

		if kw.name == "" && hasNode(kw.value) {
			txt := dotted(x.src, kw.value)
			if txt == "" {
				txt = exprText(x.src, kw.value)
			}
			if strings.Contains(strings.ToLower(txt), "request") {
				x.bump("n_mass_assign")
				break
			}
		}
	}
	if (strings.HasPrefix(name, "requests.") || strings.HasPrefix(name, "httpx.")) &&
		hasKeywordFalseArg(kws, "verify") {
		x.bump("n_verify_false")
	}
	x.calls = append(x.calls, callSite{name: name, line: line, dynamic: dynamic})
}

func hasKeywordArg(kws []kwArg, name string) bool {
	for _, kw := range kws {
		if kw.name == name {
			return true
		}
	}
	return false
}

func hasKeywordFalseArg(kws []kwArg, name string) bool {
	for _, kw := range kws {
		if kw.name == name && kindID(kw.value) == kFalse {
			return true
		}
	}
	return false
}

func hasPrefixAny(s string, ps []string) bool {
	for _, p := range ps {
		if strings.HasPrefix(s, p) {
			return true
		}
	}
	return false
}

func containsAny(s string, ps []string) bool {
	for _, p := range ps {
		if strings.Contains(s, p) {
			return true
		}
	}
	return false
}

func truncStr(s string, n int) string {
	if utf8.RuneCountInString(s) <= n {
		return s
	}
	i, count := 0, 0
	for i < len(s) {
		if count == n {
			break
		}
		_, size := utf8.DecodeRuneInString(s[i:])
		i += size
		count++
	}
	return s[:i]
}

func trunc40(s string) string {
	if len(s) > 40 {
		return s[:40]
	}
	return s
}

func lastDot(s string) string {
	if i := strings.LastIndexByte(s, '.'); i >= 0 {
		return s[i+1:]
	}
	return s
}

func dotted(src []byte, n tsNode) string {

	for hasNode(n) && kindID(n) == kParenExpr {
		n = firstNamed(n)
	}
	switch kindID(n) {
	case kIdentifier:
		return nodeText(src, n)
	case kAttribute:
		base := dotted(src, fieldNode(n, fObject))
		if base == "" {
			return ""
		}
		return base + "." + nodeText(src, fieldNode(n, fAttribute))
	case kCall:
		return dotted(src, callFunc(n))
	}
	return ""
}

func opText(src []byte, n tsNode) string { return nodeText(src, n) }

func hasTokenChild(src []byte, n tsNode, tok string) bool {
	for c := firstChildN(n); hasNode(c); c = nextSiblingOf(c) {
		if !isNamedN(c) {
			s, e := startByte(c), endByte(c)
			if e <= uint(len(src)) && e-s == uint(len(tok)) && string(src[s:e]) == tok {
				return true
			}
		}
	}
	return false
}

func firstNamed(n tsNode) tsNode {
	var out tsNode
	forEachNamed(n, func(c tsNode) {
		if !hasNode(out) {
			out = c
		}
	})
	return out
}

func countOfKind(n tsNode, k uint16) int {
	c := 0
	forEachNamed(n, func(ch tsNode) {
		if kindID(ch) == k {
			c++
		}
	})
	return c
}

func returnValue(src []byte, n tsNode) tsNode { return firstNamed(n) }

func (x *measure) withItemCount(n tsNode) int {
	c := 0
	forEachNamed(n, func(ch tsNode) {
		switch kindID(ch) {
		case kWithItem:
			c++
		case kWithClause:
			c += countOfKind(ch, kWithItem)
		}
	})
	return c
}

func bigDec(v int64, big string) string {
	if big != "" {
		return big
	}
	return strconv.FormatInt(v, 10)
}

func boolOpToken(n tsNode) tsNode {
	for c := firstChildN(n); hasNode(c); c = nextSiblingOf(c) {
		if !isNamedN(c) {
			return c
		}
	}
	return tsNode{}
}

func strconvParseInt32(s string) (int32, error) {
	v, err := strconv.ParseInt(s, 10, 32)
	return int32(v), err
}

type question struct {
	name  string
	title string
	notes string
	run   func(g *Graph, mod string, limit int) result
}

type result struct {
	cols []string
	rows [][]string
}

const maxCell = 72

func cell(s string) string {
	if len(s) <= maxCell {
		return s
	}
	return s[:maxCell-3] + "..."
}

func renderRows(cols []string, rows [][]string) {
	if len(rows) == 0 {
		printfLn(" (no rows)")
		return
	}
	w := make([]int, len(cols))
	for i, c := range cols {
		w[i] = len(c)
	}
	body := make([][]string, len(rows))
	for i, r := range rows {
		body[i] = make([]string, len(cols))
		for j, c := range r {
			body[i][j] = cell(c)
			if len(body[i][j]) > w[j] {
				w[j] = len(body[i][j])
			}
		}
	}
	parts := make([]string, len(cols))
	for i, c := range cols {
		parts[i] = pad(c, w[i])
	}
	printfLn(" %s", strings.Join(parts, " "))
	dashes := make([]string, len(cols))
	for i := range cols {
		dashes[i] = strings.Repeat("-", w[i])
	}
	printfLn(" %s", strings.Join(dashes, " "))
	for _, r := range body {
		parts = parts[:0]
		for j, c := range r {
			parts = append(parts, pad(c, w[j]))
		}
		printfLn(" %s", strings.Join(parts, " "))
	}
}

func pad(s string, w int) string {
	if len(s) >= w {
		return s
	}
	return s + strings.Repeat(" ", w-len(s))
}

func (g *Graph) path(fid int32) string {
	if fid < 1 || int(fid) > len(g.Files) {
		return ""
	}
	return g.S(g.Files[fid-1].Path)
}

func itoa(v int32) string { return fmt.Sprintf("%d", v) }

func like(s, pattern string) bool {
	if pattern == "%" {
		return true
	}

	si, pi := 0, 0
	star, mark := -1, 0
	for si < len(s) {
		switch {
		case pi < len(pattern) && (pattern[pi] == '_' || pattern[pi] == s[si]):
			si++
			pi++
		case pi < len(pattern) && pattern[pi] == '%':
			star = pi
			mark = si
			pi++
		case star >= 0:
			pi = star + 1
			mark++
			si = mark
		default:
			return false
		}
	}
	for pi < len(pattern) && pattern[pi] == '%' {
		pi++
	}
	return pi == len(pattern)
}

func (g *Graph) inModule(sym Symbol, mod string) bool {
	if sym.ModuleID < 1 || int(sym.ModuleID) > len(g.Modules) {
		return like("", mod)
	}
	return like(g.S(g.Modules[sym.ModuleID-1].Name), mod)
}

func (g *Graph) allSyms() []int32 {
	out := make([]int32, len(g.Symbols))
	for i := range out {
		out[i] = int32(i + 1)
	}
	return out
}

func (g *Graph) fnSyms() []int32 {
	var out []int32
	for i := range g.Symbols {
		if isFuncKind(g.S(g.Symbols[i].Kind)) {
			out = append(out, int32(i+1))
		}
	}
	return out
}

func (g *Graph) fileOK(fid int32, wantTest bool) bool {
	if fid < 1 || int(fid) > len(g.Files) {
		return false
	}
	f := g.Files[fid-1]
	if f.IsGenerated == 1 || f.IsVendored == 1 {
		return false
	}
	if f.IsTest == 1 && !wantTest {
		return false
	}
	return true
}

func (g *Graph) resolvePendingHazards() {}

func atoi32(s string) (int32, error) { return strconvParseInt32(s) }

func run_append_in_loop_perf(g *Graph, mod string, limit int) result {
	return g.runSymQ(symQueries["append-in-loop-perf"], mod, limit)
}

func run_assert_in_production(g *Graph, mod string, limit int) result {
	return g.runSymQ(symQueries["assert-in-production"], mod, limit)
}

func run_bare_except(g *Graph, mod string, limit int) result {
	return g.runSymQ(symQueries["bare-except"], mod, limit)
}

func run_broad_test_expectation(g *Graph, mod string, limit int) result {
	return g.runSymQ(symQueries["broad-test-expectation"], mod, limit)
}

func run_closure_in_loop(g *Graph, mod string, limit int) result {
	return g.runSymQ(symQueries["closure-in-loop"], mod, limit)
}

func run_commit_in_loop(g *Graph, mod string, limit int) result {
	return g.runSymQ(symQueries["commit-in-loop"], mod, limit)
}

func run_concurrency_surface(g *Graph, mod string, limit int) result {
	return g.runSymQ(symQueries["concurrency-surface"], mod, limit)
}

func run_datetime_naive(g *Graph, mod string, limit int) result {
	return g.runSymQ(symQueries["datetime-naive"], mod, limit)
}

func run_deep_nesting(g *Graph, mod string, limit int) result {
	return g.runSymQ(symQueries["deep-nesting"], mod, limit)
}

func run_deep_nesting_excessive(g *Graph, mod string, limit int) result {
	return g.runSymQ(symQueries["deep-nesting-excessive"], mod, limit)
}

func run_dict_get_in_loop(g *Graph, mod string, limit int) result {
	return g.runSymQ(symQueries["dict-get-in-loop"], mod, limit)
}

func run_eval_exec_injection(g *Graph, mod string, limit int) result {
	return g.runSymQ(symQueries["eval-exec-injection"], mod, limit)
}

func run_format_in_loop(g *Graph, mod string, limit int) result {
	return g.runSymQ(symQueries["format-in-loop"], mod, limit)
}

func run_global_statement(g *Graph, mod string, limit int) result {
	return g.runSymQ(symQueries["global-statement"], mod, limit)
}

func run_god_functions(g *Graph, mod string, limit int) result {
	return g.runSymQ(symQueries["god-functions"], mod, limit)
}

func run_hot_multipliers(g *Graph, mod string, limit int) result {
	return g.runSymQ(symQueries["hot-multipliers"], mod, limit)
}

func run_insecure_tempfile(g *Graph, mod string, limit int) result {
	return g.runSymQ(symQueries["insecure-tempfile"], mod, limit)
}

func run_lock_across_await(g *Graph, mod string, limit int) result {
	return g.runSymQ(symQueries["lock-across-await"], mod, limit)
}

func run_loop_else(g *Graph, mod string, limit int) result {
	return g.runSymQ(symQueries["loop-else"], mod, limit)
}

func run_membership_scan_in_loop(g *Graph, mod string, limit int) result {
	return g.runSymQ(symQueries["membership-scan-in-loop"], mod, limit)
}

func run_nested_loops(g *Graph, mod string, limit int) result {
	return g.runSymQ(symQueries["nested-loops"], mod, limit)
}

func run_open_without_with(g *Graph, mod string, limit int) result {
	return g.runSymQ(symQueries["open-without-with"], mod, limit)
}

func run_orm_query_in_loop(g *Graph, mod string, limit int) result {
	return g.runSymQ(symQueries["orm-query-in-loop"], mod, limit)
}

func run_pickle_deserialization(g *Graph, mod string, limit int) result {
	return g.runSymQ(symQueries["pickle-deserialization"], mod, limit)
}

func run_print_statement_shipping(g *Graph, mod string, limit int) result {
	return g.runSymQ(symQueries["print-statement-shipping"], mod, limit)
}

func run_recursive_hotspots(g *Graph, mod string, limit int) result {
	return g.runSymQ(symQueries["recursive-hotspots"], mod, limit)
}

func run_request_without_timeout(g *Graph, mod string, limit int) result {
	return g.runSymQ(symQueries["request-without-timeout"], mod, limit)
}

func run_resource_discipline(g *Graph, mod string, limit int) result {
	return g.runSymQ(symQueries["resource-discipline"], mod, limit)
}

func run_resource_return_escape(g *Graph, mod string, limit int) result {
	return g.runSymQ(symQueries["resource-return-escape"], mod, limit)
}

func run_risk_ranked(g *Graph, mod string, limit int) result {
	return g.runSymQ(symQueries["risk-ranked"], mod, limit)
}

func run_subprocess_shell_injection(g *Graph, mod string, limit int) result {
	return g.runSymQ(symQueries["subprocess-shell-injection"], mod, limit)
}

func run_template_injection(g *Graph, mod string, limit int) result {
	return g.runSymQ(symQueries["template-injection"], mod, limit)
}

func run_tls_verify_disabled(g *Graph, mod string, limit int) result {
	return g.runSymQ(symQueries["tls-verify-disabled"], mod, limit)
}

func run_too_many_branches(g *Graph, mod string, limit int) result {
	return g.runSymQ(symQueries["too-many-branches"], mod, limit)
}

func run_too_many_locals(g *Graph, mod string, limit int) result {
	return g.runSymQ(symQueries["too-many-locals"], mod, limit)
}

func run_too_many_return(g *Graph, mod string, limit int) result {
	return g.runSymQ(symQueries["too-many-return"], mod, limit)
}

func run_typing_holes(g *Graph, mod string, limit int) result {
	return g.runSymQ(symQueries["typing-holes"], mod, limit)
}

func run_undocumented_complexity(g *Graph, mod string, limit int) result {
	return g.runSymQ(symQueries["undocumented-complexity"], mod, limit)
}

func run_undocumented_export(g *Graph, mod string, limit int) result {
	return g.runSymQ(symQueries["undocumented-export"], mod, limit)
}

func run_untyped_params(g *Graph, mod string, limit int) result {
	return g.runSymQ(symQueries["untyped-params"], mod, limit)
}

func run_unused_public_api(g *Graph, mod string, limit int) result {
	return g.runSymQ(symQueries["unused-public-api"], mod, limit)
}

func run_xxe_parser_surface(g *Graph, mod string, limit int) result {
	return g.runSymQ(symQueries["xxe-parser-surface"], mod, limit)
}

func run_yaml_unsafe_load(g *Graph, mod string, limit int) result {
	return g.runSymQ(symQueries["yaml-unsafe-load"], mod, limit)
}

func run_zip_slip_surface(g *Graph, mod string, limit int) result {
	return g.runSymQ(symQueries["zip-slip-surface"], mod, limit)
}

type pred func(g *Graph, s *Symbol) bool

type symQ struct {
	cols []string

	keep pred

	order func(g *Graph, s *Symbol) []oterm

	cells func(g *Graph, s *Symbol) []string
}

func (g *Graph) runSymQ(q symQ, mod string, limit int) result {
	r := result{cols: q.cols}
	rows := make([]qrow, 0, 64)
	for i := range g.Symbols {
		s := &g.Symbols[i]
		if !g.modOK(s, mod) || !q.keep(g, s) {
			continue
		}
		x := qrow{ord: s.ID, cells: q.cells(g, s)}
		if q.order != nil {
			x.order = q.order(g, s)
		}
		rows = append(rows, x)
	}
	qemit(&r, rows, limit)
	return r
}

func (g *Graph) modOK(s *Symbol, mod string) bool {
	if mod == "%" {
		return true
	}
	return dbLike(g.moduleName(s.ModuleID), mod)
}

func (g *Graph) notest(fid int32) bool {
	return fid >= 1 && int(fid) <= len(g.Files) && g.Files[fid-1].IsTest == 0
}
func (g *Graph) nogen(fid int32) bool {
	return fid >= 1 && int(fid) <= len(g.Files) && g.Files[fid-1].IsGenerated == 0
}
func (g *Graph) notestgen(fid int32) bool {
	return g.notest(fid) && g.nogen(fid)
}

func pAll(ps ...pred) pred {
	return func(g *Graph, s *Symbol) bool {
		for _, p := range ps {
			if !p(g, s) {
				return false
			}
		}
		return true
	}
}
func pGT(f func(*Symbol) int32, n int32) pred {
	return func(g *Graph, s *Symbol) bool { return f(s) > n }
}
func pGE(f func(*Symbol) int32, n int32) pred {
	return func(g *Graph, s *Symbol) bool { return f(s) >= n }
}
func pEQ(f func(*Symbol) int32, n int32) pred {
	return func(g *Graph, s *Symbol) bool { return f(s) == n }
}
func pIs0(f func(*Symbol) int32) pred {
	return func(g *Graph, s *Symbol) bool { return f(s) == 0 }
}
func pFile(f func(*Graph, int32) bool) pred {
	return func(g *Graph, s *Symbol) bool { return f(g, s.FileID) }
}
func pIsKind(ks ...string) pred {
	return func(g *Graph, s *Symbol) bool {
		k := g.S(s.Kind)
		return slices.Contains(ks, k)
	}
}

func cNOpen(s *Symbol) int32       { return s.NOpen }
func cNConc(s *Symbol) int32       { return s.NConcurrency }
func cNGlobal(s *Symbol) int32     { return s.NGlobalStmt }
func cNBare(s *Symbol) int32       { return s.NBareExcept }
func cNPickle(s *Symbol) int32     { return s.NPickleLoad }
func cNYaml(s *Symbol) int32       { return s.NYamlLoad }
func cNSub(s *Symbol) int32        { return s.NSubprocess }
func cNEval(s *Symbol) int32       { return s.NEvalExec }
func cNAssert(s *Symbol) int32     { return s.NAssert }
func cNAppend(s *Symbol) int32     { return s.AppendInLoop }
func cNReqTO(s *Symbol) int32      { return s.NRequestNoTimeout }
func cNXXE(s *Symbol) int32        { return s.NXxeParser }
func cNZip(s *Symbol) int32        { return s.NZipRead }
func cNLoopClos(s *Symbol) int32   { return s.NLoopClosure }
func cNBroadRaise(s *Symbol) int32 { return s.NBroadRaises }
func cNAutoesc(s *Symbol) int32    { return s.NAutoescapeFalse }
func cNOrmQ(s *Symbol) int32       { return s.NOrmQueryInLoop }
func cNCommit(s *Symbol) int32     { return s.NCommitInLoop }
func cNAwaitSync(s *Symbol) int32  { return s.NAwaitInSyncWith }
func cNScan(s *Symbol) int32       { return s.NInScanLoop }
func cNResRet(s *Symbol) int32     { return s.NResourceReturn }
func cNVerify(s *Symbol) int32     { return s.NVerifyFalse }
func cNDictGet(s *Symbol) int32    { return s.NDictGetInLoop }
func cNFmt(s *Symbol) int32        { return s.NFormatInLoop }
func cNLoopElse(s *Symbol) int32   { return s.NLoopElse }
func cNPrint(s *Symbol) int32      { return s.NPrint }
func cNInsecTemp(s *Symbol) int32  { return s.NInsecureTemp }
func cNUntyped(s *Symbol) int32    { return s.NUntypedParams }
func cNLoopDepth(s *Symbol) int32  { return s.MaxLoopDepth }
func cNesting(s *Symbol) int32     { return s.MaxNesting }
func cCyclo(s *Symbol) int32       { return s.Cyclomatic }
func cCog(s *Symbol) int32         { return s.Cognitive }
func cSLOC(s *Symbol) int32        { return s.SLOC }
func cFanIn(s *Symbol) int32       { return s.FanIn }
func cNLoops(s *Symbol) int32      { return s.NLoops }
func cNLocals(s *Symbol) int32     { return s.NLocals }
func cNReturns(s *Symbol) int32    { return s.NReturns }
func cNBranches(s *Symbol) int32   { return s.NBranches }
func cCallInLoop(s *Symbol) int32  { return s.CallInLoop }

func o1(a func(*Symbol) int32) func(*Graph, *Symbol) []oterm {
	return func(g *Graph, s *Symbol) []oterm { return []oterm{dsc(a(s))} }
}
func o2(a, b func(*Symbol) int32) func(*Graph, *Symbol) []oterm {
	return func(g *Graph, s *Symbol) []oterm { return []oterm{dsc(a(s)), dsc(b(s))} }
}

func atCell(g *Graph, s *Symbol) string { return at(g, *s) }

var symQueries = map[string]symQ{}

func regSym(name string, q symQ) { symQueries[name] = q }

func hasNoAttrLike(g *Graph, s *Symbol, pat string) bool {
	for _, a := range g.attrRows(s.ID) {
		if dbLike(g.S(a.Name), pat) {
			return false
		}
	}
	return true
}

func init() {

	regSym("resource-discipline", symQ{
		cols: cols_resource_discipline,
		keep: pAll(
			func(g *Graph, s *Symbol) bool { return s.NOpen+s.NResource > s.NCtxManagers },
			pGT(func(s *Symbol) int32 { return s.NOpen + s.NResource }, 0),
			pFile((*Graph).notest)),
		order: o1(func(s *Symbol) int32 { return s.NOpen + s.NResource - s.NCtxManagers }),
		cells: func(g *Graph, s *Symbol) []string {
			return []string{g.S(s.Name), cellInt(s.NOpen), cellInt(s.NResource),
				cellInt(s.NWith), cellInt(s.NCtxManagers), cellInt(s.NTry),
				cellInt(s.NFinally), atCell(g, s)}
		},
	})

	regSym("concurrency-surface", symQ{
		cols:  cols_concurrency_surface,
		keep:  pAll(pGT(cNConc, 0), pFile((*Graph).notest)),
		order: o2(cNConc, cNGlobal),
		cells: func(g *Graph, s *Symbol) []string {
			return []string{g.S(s.Name), cellInt(s.NConcurrency), cellInt(s.NGlobalStmt),
				cellInt(s.LockInLoop), cellInt(s.IsAsync), cellInt(s.NBlocking),
				cellInt(s.FanIn), atCell(g, s)}
		},
	})

	regSym("bare-except", symQ{
		cols:  cols_bare_except,
		keep:  pAll(pGT(cNBare, 0), pFile((*Graph).notest)),
		order: o2(cNBare, cFanIn),
		cells: func(g *Graph, s *Symbol) []string {
			return []string{g.S(s.Name), cellInt(s.NBareExcept), cellInt(s.NCatchSwallow),
				cellInt(s.NReraise), cellInt(s.NCatch), cellInt(s.FanIn),
				cellInt(s.Cyclomatic), atCell(g, s)}
		},
	})

	regSym("pickle-deserialization", symQ{
		cols:  cols_pickle_deserialization,
		keep:  pAll(pGT(cNPickle, 0), pFile((*Graph).notest)),
		order: o2(cFanIn, cNPickle),
		cells: func(g *Graph, s *Symbol) []string {
			return []string{g.S(s.Name), cellInt(s.NPickleLoad), cellInt(s.NEvalExec),
				cellInt(s.NYamlLoad), cellInt(s.FanIn), atCell(g, s)}
		},
	})

	regSym("yaml-unsafe-load", symQ{
		cols:  cols_yaml_unsafe_load,
		keep:  pAll(pGT(cNYaml, 0), pFile((*Graph).notest)),
		order: o2(cFanIn, cNYaml),
		cells: func(g *Graph, s *Symbol) []string {
			return []string{g.S(s.Name), cellInt(s.NYamlLoad), cellInt(s.NPickleLoad),
				cellInt(s.FanIn), cellInt(s.Cyclomatic), atCell(g, s)}
		},
	})

	regSym("subprocess-shell-injection", symQ{
		cols:  cols_subprocess_shell_injection,
		keep:  pAll(pGT(cNSub, 0), pFile((*Graph).notest)),
		order: o2(cFanIn, func(s *Symbol) int32 { return s.NShellTrue }),
		cells: func(g *Graph, s *Symbol) []string {
			return []string{g.S(s.Name), cellInt(s.NSubprocess), cellInt(s.NShellTrue),
				cellInt(s.NOSystem), cellInt(s.NEvalExec), cellInt(s.FanIn), atCell(g, s)}
		},
	})

	regSym("eval-exec-injection", symQ{
		cols:  cols_eval_exec_injection,
		keep:  pAll(pGT(cNEval, 0), pFile((*Graph).notest)),
		order: o2(cFanIn, cNEval),
		cells: func(g *Graph, s *Symbol) []string {
			return []string{g.S(s.Name), cellInt(s.NEvalExec), cellInt(s.NDynamicAttr),
				cellInt(s.NPickleLoad), cellInt(s.FanIn), atCell(g, s)}
		},
	})

	regSym("assert-in-production", symQ{
		cols:  cols_assert_in_production,
		keep:  pAll(pGT(cNAssert, 0), pFile((*Graph).notest)),
		order: o2(cFanIn, cNAssert),
		cells: func(g *Graph, s *Symbol) []string {
			return []string{g.S(s.Name), cellInt(s.NAssert), cellInt(s.NAssertInLoop),
				cellInt(s.FanIn), cellInt(s.Cyclomatic), atCell(g, s)}
		},
	})

	regSym("global-statement", symQ{
		cols:  cols_global_statement,
		keep:  pAll(pGT(cNGlobal, 0), pFile((*Graph).notest)),
		order: o2(cFanIn, cNGlobal),
		cells: func(g *Graph, s *Symbol) []string {
			return []string{g.S(s.Name), cellInt(s.NGlobalStmt), cellInt(s.NNonlocal),
				cellInt(s.NAssign), cellInt(s.FanIn), cellInt(s.Cyclomatic), atCell(g, s)}
		},
	})

	regSym("open-without-with", symQ{
		cols: cols_open_without_with,
		keep: pAll(pGT(cNOpen, 0), pIs0(func(s *Symbol) int32 { return s.NWith }),
			pFile((*Graph).notest)),
		order: o2(cFanIn, cNOpen),
		cells: func(g *Graph, s *Symbol) []string {
			return []string{g.S(s.Name), cellInt(s.NOpen), cellInt(s.NWith),
				cellInt(s.NTry), cellInt(s.NFinally), cellInt(s.FanIn),
				cellInt(s.Cyclomatic), atCell(g, s)}
		},
	})

	regSym("datetime-naive", symQ{
		cols: cols_datetime_naive,
		keep: pAll(pGT(func(s *Symbol) int32 { return s.NDatetime }, 0),
			pFile((*Graph).notest)),
		order: o2(cFanIn, func(s *Symbol) int32 { return s.NDatetime }),
		cells: func(g *Graph, s *Symbol) []string {
			return []string{g.S(s.Name), cellInt(s.NDatetime), cellInt(s.NOpenNoEncoding),
				cellInt(s.FanIn), cellInt(s.Cyclomatic), atCell(g, s)}
		},
	})

	regSym("append-in-loop-perf", symQ{
		cols:  cols_append_in_loop_perf,
		keep:  pAll(pGT(cNAppend, 0), pFile((*Graph).notest)),
		order: o2(cNAppend, cNLoops),
		cells: func(g *Graph, s *Symbol) []string {
			return []string{g.S(s.Name), cellInt(s.AppendInLoop), cellInt(s.NRangeLen),
				cellInt(s.NLoops), cellInt(s.Cyclomatic), cellInt(s.FanIn), atCell(g, s)}
		},
	})

	regSym("request-without-timeout", symQ{
		cols:  cols_request_without_timeout,
		keep:  pAll(pGT(cNReqTO, 0), pFile((*Graph).nogen)),
		order: o2(cFanIn, cNReqTO),
		cells: func(g *Graph, s *Symbol) []string {
			return []string{g.path(s.FileID), g.S(s.Name),
				cellInt(s.NRequestNoTimeout), cellInt(s.FanIn)}
		},
	})

	regSym("xxe-parser-surface", symQ{
		cols:  cols_xxe_parser_surface,
		keep:  pAll(pGT(cNXXE, 0), pFile((*Graph).notestgen)),
		order: o2(cNXXE, cSLOC),
		cells: func(g *Graph, s *Symbol) []string {
			return []string{g.S(s.Name), cellInt(s.NXxeParser), cellInt(s.SLOC), atCell(g, s)}
		},
	})

	regSym("zip-slip-surface", symQ{
		cols:  cols_zip_slip_surface,
		keep:  pAll(pGT(cNZip, 0), pFile((*Graph).notestgen)),
		order: o2(cFanIn, cNZip),
		cells: func(g *Graph, s *Symbol) []string {
			return []string{g.S(s.Name), cellInt(s.NZipRead), cellInt(s.FanIn), atCell(g, s)}
		},
	})

	regSym("undocumented-export", symQ{
		cols: cols_undocumented_export,
		keep: pAll(
			pEQ(func(s *Symbol) int32 { return s.IsPublic }, 1),
			pEQ(func(s *Symbol) int32 { return s.HasDoc }, 0),
			pGT(cFanIn, 0),
			pIsKind("function", "method", "class"),
			pFile((*Graph).notestgen)),
		order: func(g *Graph, s *Symbol) []oterm {
			return []oterm{dsc(cFanIn(s)), dsc(cSLOC(s)),
				ascI(s.FileID), ascT(g.S(s.Kind))}
		},
		cells: func(g *Graph, s *Symbol) []string {
			return []string{g.S(s.Name), g.S(s.Kind), cellInt(s.FanIn),
				cellInt(s.SLOC), atCell(g, s)}
		},
	})

	regSym("closure-in-loop", symQ{
		cols:  cols_closure_in_loop,
		keep:  pAll(pGT(cNLoopClos, 0), pFile((*Graph).notest)),
		order: o2(cNLoopClos, cFanIn),
		cells: func(g *Graph, s *Symbol) []string {
			return []string{g.S(s.Name), cellInt(s.NLoopClosure), cellInt(s.MaxLoopDepth),
				cellInt(s.NLambda), cellInt(s.FanIn), atCell(g, s)}
		},
	})

	regSym("broad-test-expectation", symQ{
		cols:  cols_broad_test_expectation,
		keep:  pAll(pGT(cNBroadRaise, 0), pFile((*Graph).notest)),
		order: o2(cNBroadRaise, cFanIn),
		cells: func(g *Graph, s *Symbol) []string {
			return []string{g.path(s.FileID), g.S(s.Name), cellInt(s.NBroadRaises),
				cellInt(s.NCalls), cellInt(s.FanIn)}
		},
	})

	regSym("template-injection", symQ{
		cols:  cols_template_injection,
		keep:  pAll(pGT(cNAutoesc, 0), pFile((*Graph).notest)),
		order: o2(cNAutoesc, cFanIn),
		cells: func(g *Graph, s *Symbol) []string {
			return []string{g.path(s.FileID), g.S(s.Name), cellInt(s.NAutoescapeFalse),
				cellInt(s.FanIn), cellInt(s.SLOC)}
		},
	})

	regSym("orm-query-in-loop", symQ{
		cols:  cols_orm_query_in_loop,
		keep:  pAll(pGT(cNOrmQ, 0), pFile((*Graph).notestgen)),
		order: o2(cNOrmQ, cFanIn),
		cells: func(g *Graph, s *Symbol) []string {
			return []string{g.S(s.Name), cellInt(s.NOrmQueryInLoop), cellInt(s.MaxLoopDepth),
				cellInt(s.NOrmWrite), cellInt(s.NSql), cellInt(s.FanIn), atCell(g, s)}
		},
	})

	regSym("commit-in-loop", symQ{
		cols:  cols_commit_in_loop,
		keep:  pAll(pGT(cNCommit, 0), pFile((*Graph).notestgen)),
		order: o2(cNCommit, cFanIn),
		cells: func(g *Graph, s *Symbol) []string {
			return []string{g.S(s.Name), cellInt(s.NCommitInLoop), cellInt(s.MaxLoopDepth),
				cellInt(s.NSql), cellInt(s.FanIn), atCell(g, s)}
		},
	})

	regSym("lock-across-await", symQ{
		cols: cols_lock_across_await,
		keep: pAll(
			pEQ(func(s *Symbol) int32 { return s.IsAsync }, 1),
			pGT(cNAwaitSync, 0),
			pFile((*Graph).notestgen)),
		order: o2(cNAwaitSync, cNConc),
		cells: func(g *Graph, s *Symbol) []string {
			return []string{g.S(s.Name), cellInt(s.NAwaitInSyncWith), cellInt(s.NConcurrency),
				cellInt(s.NAwait), cellInt(s.FanIn), atCell(g, s)}
		},
	})

	regSym("membership-scan-in-loop", symQ{
		cols:  cols_membership_scan_in_loop,
		keep:  pAll(pGT(cNScan, 0), pFile((*Graph).notestgen)),
		order: o2(cNScan, cFanIn),
		cells: func(g *Graph, s *Symbol) []string {
			return []string{g.S(s.Name), cellInt(s.NInScanLoop), cellInt(s.MaxLoopDepth),
				cellInt(s.NLoops), cellInt(s.FanIn), atCell(g, s)}
		},
	})

	regSym("resource-return-escape", symQ{
		cols:  cols_resource_return_escape,
		keep:  pAll(pGT(cNResRet, 0), pFile((*Graph).notestgen)),
		order: o2(cFanIn, cNResRet),
		cells: func(g *Graph, s *Symbol) []string {
			return []string{g.S(s.Name), cellInt(s.NResourceReturn), cellInt(s.NCtxManagers),
				cellInt(s.FanIn), atCell(g, s)}
		},
	})

	regSym("tls-verify-disabled", symQ{
		cols:  cols_tls_verify_disabled,
		keep:  pAll(pGT(cNVerify, 0), pFile((*Graph).notestgen)),
		order: o2(cNVerify, cFanIn),
		cells: func(g *Graph, s *Symbol) []string {
			return []string{g.S(s.Name), cellInt(s.NVerifyFalse), cellInt(s.FanIn), atCell(g, s)}
		},
	})

	regSym("dict-get-in-loop", symQ{
		cols:  cols_dict_get_in_loop,
		keep:  pAll(pGT(cNDictGet, 0), pFile((*Graph).notestgen)),
		order: o2(cNDictGet, cFanIn),
		cells: func(g *Graph, s *Symbol) []string {
			return []string{g.S(s.Name), cellInt(s.NDictGetInLoop), cellInt(s.MaxLoopDepth),
				cellInt(s.NLoops), cellInt(s.FanIn), atCell(g, s)}
		},
	})

	regSym("format-in-loop", symQ{
		cols:  cols_format_in_loop,
		keep:  pAll(pGT(cNFmt, 0), pFile((*Graph).notestgen)),
		order: o2(cNFmt, cFanIn),
		cells: func(g *Graph, s *Symbol) []string {
			return []string{g.S(s.Name), cellInt(s.NFormatInLoop), cellInt(s.MaxLoopDepth),
				cellInt(s.ConcatInLoop), cellInt(s.FanIn), atCell(g, s)}
		},
	})

	regSym("loop-else", symQ{
		cols:  cols_loop_else,
		keep:  pAll(pGT(cNLoopElse, 0), pFile((*Graph).notestgen)),
		order: o2(cNLoopElse, cFanIn),
		cells: func(g *Graph, s *Symbol) []string {
			return []string{g.S(s.Name), cellInt(s.NLoopElse), cellInt(s.NLoops),
				cellInt(s.Cyclomatic), cellInt(s.FanIn), atCell(g, s)}
		},
	})

	regSym("print-statement-shipping", symQ{
		cols: cols_print_statement_shipping,
		keep: pAll(pGT(cNPrint, 0),
			pEQ(func(s *Symbol) int32 { return s.IsPublic }, 1),
			pIsKind("function", "method"), pFile((*Graph).notestgen)),
		order: o2(cFanIn, cNPrint),
		cells: func(g *Graph, s *Symbol) []string {
			return []string{g.S(s.Name), cellInt(s.NPrint), cellInt(s.FanIn), atCell(g, s)}
		},
	})

	regSym("insecure-tempfile", symQ{
		cols:  cols_insecure_tempfile,
		keep:  pAll(pGT(cNInsecTemp, 0), pFile((*Graph).notest)),
		order: o2(cFanIn, cNInsecTemp),
		cells: func(g *Graph, s *Symbol) []string {
			return []string{g.S(s.Name), cellInt(s.NInsecureTemp), cellInt(s.FanIn), atCell(g, s)}
		},
	})

	regSym("unused-public-api", symQ{
		cols: cols_unused_public_api,
		keep: pAll(
			pEQ(cFanIn, 0),
			pEQ(func(s *Symbol) int32 { return s.IsPublic }, 1),
			pIsKind("function", "method"),
			pEQ(func(s *Symbol) int32 { return s.IsDunder }, 0),
			pEQ(func(s *Symbol) int32 { return s.IsEntrypoint }, 0),
			pEQ(func(s *Symbol) int32 { return s.IsOverride }, 0),
			pEQ(func(s *Symbol) int32 { return s.IsAbstract }, 0),
			pEQ(func(s *Symbol) int32 { return s.IsOverload }, 0),
			pEQ(func(s *Symbol) int32 { return s.IsTest }, 0),
			pFile((*Graph).notestgen),
			func(g *Graph, s *Symbol) bool { return len(g.attrRows(s.ID)) == 0 }),
		order: func(g *Graph, s *Symbol) []oterm {
			return []oterm{dsc(cSLOC(s)), ascI(s.FileID), ascT(g.S(s.Kind))}
		},
		cells: func(g *Graph, s *Symbol) []string {
			return []string{g.S(s.Name), g.S(s.Kind), cellInt(s.SLOC),
				cellInt(s.Cyclomatic), cellInt(s.NDocLines), atCell(g, s)}
		},
	})

	regSym("risk-ranked", symQ{
		cols: cols_risk_ranked,
		keep: pAll(pIsKind("function", "method"), pFile((*Graph).nogen)),
		order: func(g *Graph, s *Symbol) []oterm {
			return []oterm{dsc(s.RiskScore), ascI(s.FileID), ascT(g.S(s.Kind))}
		},
		cells: func(g *Graph, s *Symbol) []string {
			return []string{g.S(s.Name), cellInt(s.RiskScore), cellInt(s.Cyclomatic),
				cellInt(s.Cognitive), cellInt(s.MaxNesting),
				cellInt(s.NExec + s.NDeserialize),
				cellInt(s.NSqlFstring + s.NSqlConcat + s.NSqlFormat),
				cellInt(s.NShellTrue), cellInt(s.FanIn), atCell(g, s)}
		},
	})

	regSym("hot-multipliers", symQ{
		cols: cols_hot_multipliers,
		keep: pIsKind("function", "method"),
		order: func(g *Graph, s *Symbol) []oterm {
			return []oterm{dsc(cFanIn(s)), dsc(cCyclo(s)),
				ascT(g.path(s.FileID)), ascT(g.S(s.Kind))}
		},
		cells: func(g *Graph, s *Symbol) []string {
			return []string{g.S(s.Name), cellInt(s.FanIn), cellInt(s.NCallsites),
				cellInt(s.FanOut), cellInt(s.Cyclomatic), cellInt(s.SLOC),
				cellInt(s.HasDoc), g.moduleName(s.ModuleID), atCell(g, s)}
		},
	})

	regSym("typing-holes", symQ{
		cols: cols_typing_holes,
		keep: pAll(pIsKind("function", "method"),
			pEQ(func(s *Symbol) int32 { return s.IsPublic }, 1),
			pGT(cNUntyped, 0), pFile((*Graph).notestgen)),
		order: o2(cFanIn, cNUntyped),
		cells: func(g *Graph, s *Symbol) []string {
			pct, ok := castInt(100.0*float64(s.NAnnotatedParams)/float64(s.NParams), s.NParams != 0)
			return []string{g.S(s.Name), cellInt(s.NParams), cellInt(s.NUntypedParams),
				cellInt(s.HasReturnType), cellInt(s.FanIn), cellInt(s.IsPublic),
				cellOptInt(pct, ok), atCell(g, s)}
		},
	})

	regSym("god-functions", symQ{
		cols: cols_god_functions,
		keep: pAll(pIsKind("function", "method"), pFile((*Graph).nogen)),
		order: func(g *Graph, s *Symbol) []oterm {
			return []oterm{dsc(cCog(s)), ascI(s.FileID), ascT(g.S(s.Kind))}
		},
		cells: func(g *Graph, s *Symbol) []string {
			return []string{g.S(s.Name), cellInt(s.SLOC), cellInt(s.Cyclomatic),
				cellInt(s.Cognitive), cellInt(s.MaxNesting), cellInt(s.NElif),
				cellInt(s.NReturns), cellInt(s.NLocals), cellInt(s.NParams),
				cellInt(s.Maintainability), atCell(g, s)}
		},
	})

	regSym("deep-nesting", symQ{
		cols:  cols_deep_nesting,
		keep:  pAll(pGE(cNesting, 4), pFile((*Graph).nogen)),
		order: o2(cNesting, cCog),
		cells: func(g *Graph, s *Symbol) []string {
			return []string{g.S(s.Name), cellInt(s.MaxNesting), cellInt(s.MaxLoopDepth),
				cellInt(s.Cognitive), cellInt(s.SLOC), cellInt(s.NEarlyReturns), atCell(g, s)}
		},
	})

	regSym("nested-loops", symQ{
		cols:  cols_nested_loops,
		keep:  pAll(pGE(cNLoopDepth, 2), pFile((*Graph).nogen)),
		order: o2(cNLoopDepth, cCallInLoop),
		cells: func(g *Graph, s *Symbol) []string {
			return []string{g.S(s.Name), cellInt(s.MaxLoopDepth), cellInt(s.NLoops),
				cellInt(s.CallInLoop), cellInt(s.NSubscript), cellInt(s.SLOC),
				cellInt(s.FanIn), atCell(g, s)}
		},
	})

	regSym("undocumented-complexity", symQ{
		cols: cols_undocumented_complexity,
		keep: pAll(
			pEQ(func(s *Symbol) int32 { return s.HasDoc }, 0),
			pIsKind("function", "method"),
			pGE(cCyclo, 8),
			pFile((*Graph).notestgen),
			pEQ(func(s *Symbol) int32 { return s.IsDunder }, 0)),
		order: o2(cCyclo, cFanIn),
		cells: func(g *Graph, s *Symbol) []string {
			return []string{g.S(s.Name), cellInt(s.Cyclomatic), cellInt(s.Cognitive),
				cellInt(s.SLOC), cellInt(s.NParams), cellInt(s.FanIn),
				cellInt(s.IsPublic), atCell(g, s)}
		},
	})

	regSym("too-many-locals", symQ{
		cols:  cols_too_many_locals,
		keep:  pAll(pGT(cNLocals, 15), pIsKind("function", "method"), pFile((*Graph).notest)),
		order: o2(cNLocals, cCyclo),
		cells: func(g *Graph, s *Symbol) []string {
			return []string{g.S(s.Name), cellInt(s.NLocals), cellInt(s.NParams),
				cellInt(s.SLOC), cellInt(s.Cyclomatic), cellInt(s.MaxNesting),
				cellInt(s.FanIn), atCell(g, s)}
		},
	})

	regSym("too-many-branches", symQ{
		cols:  cols_too_many_branches,
		keep:  pAll(pGT(cNBranches, 12), pIsKind("function", "method"), pFile((*Graph).notest)),
		order: o2(cNBranches, cCyclo),
		cells: func(g *Graph, s *Symbol) []string {
			return []string{g.S(s.Name), cellInt(s.NBranches), cellInt(s.NSwitch),
				cellInt(s.NCases), cellInt(s.Cyclomatic), cellInt(s.SLOC),
				cellInt(s.FanIn), atCell(g, s)}
		},
	})

	regSym("too-many-return", symQ{
		cols:  cols_too_many_return,
		keep:  pAll(pGT(cNReturns, 6), pIsKind("function", "method"), pFile((*Graph).notest)),
		order: o2(cNReturns, cCyclo),
		cells: func(g *Graph, s *Symbol) []string {
			return []string{g.S(s.Name), cellInt(s.NReturns), cellInt(s.NEarlyReturns),
				cellInt(s.NFinally), cellInt(s.Cyclomatic), cellInt(s.FanIn), atCell(g, s)}
		},
	})

	regSym("untyped-params", symQ{
		cols: cols_untyped_params,
		keep: pAll(pGT(cNUntyped, 0),
			pEQ(func(s *Symbol) int32 { return s.IsPublic }, 1), pFile((*Graph).notest)),
		order: o2(cFanIn, cNUntyped),
		cells: func(g *Graph, s *Symbol) []string {
			return []string{g.S(s.Name), cellInt(s.NUntypedParams), cellInt(s.NAnnotatedParams),
				cellInt(s.NParams), cellInt(s.HasReturnType), cellInt(s.FanIn),
				cellInt(s.IsPublic), atCell(g, s)}
		},
	})

	regSym("deep-nesting-excessive", symQ{
		cols:  cols_deep_nesting_excessive,
		keep:  pAll(pGT(cNesting, 5), pIsKind("function", "method"), pFile((*Graph).notest)),
		order: o2(cNesting, cCyclo),
		cells: func(g *Graph, s *Symbol) []string {
			return []string{g.S(s.Name), cellInt(s.MaxNesting), cellInt(s.Cyclomatic),
				cellInt(s.Cognitive), cellInt(s.NLoops), cellInt(s.SLOC),
				cellInt(s.FanIn), atCell(g, s)}
		},
	})

	regSym("recursive-hotspots", symQ{
		cols: cols_recursive_hotspots,
		keep: pAll(
			pEQ(func(s *Symbol) int32 { return s.IsRecursive }, 1),
			pIsKind("function", "method"), pFile((*Graph).notestgen)),
		order: func(g *Graph, s *Symbol) []oterm {
			return []oterm{dsc(cCyclo(s)), dsc(cFanIn(s)),
				ascT(g.S(s.Kind)), ascT(g.S(s.Name))}
		},
		cells: func(g *Graph, s *Symbol) []string {
			return []string{g.S(s.Name), cellInt(s.Cyclomatic), cellInt(s.FanIn),
				cellInt(s.SLOC), cellInt(s.MaxLoopDepth), cellInt(s.NParams), atCell(g, s)}
		},
	})
}

func run_async_blocking(g *Graph, mod string, limit int) result {
	r := result{cols: cols_async_blocking}
	var ids []int32
	for _, id := range g.fnSyms() {
		s := g.sym(id)
		if s.IsAsync != 1 {
			continue
		}
		if s.NBlocking == 0 && s.NIO == 0 && s.NNet == 0 {
			continue
		}
		if !g.nogen(s.FileID) || !g.inModule(*s, mod) {
			continue
		}
		ids = append(ids, id)
	}

	sort.SliceStable(ids, func(i, j int) bool {
		a, b := g.sym(ids[i]), g.sym(ids[j])
		if a.NBlocking != b.NBlocking {
			return a.NBlocking > b.NBlocking
		}
		if a.NNet != b.NNet {
			return a.NNet > b.NNet
		}
		if g.S(a.Name) != g.S(b.Name) {
			return g.S(a.Name) < g.S(b.Name)
		}
		if a.FileID != b.FileID {
			return a.FileID < b.FileID
		}
		return ids[i] < ids[j]
	})
	for _, id := range ids {
		s := g.sym(id)
		r.rows = append(r.rows, []string{g.S(s.Name), num(s.NBlocking), num(s.NIO),
			num(s.NNet), num(s.NAwait), num(s.AwaitInLoop), num(s.FanIn), at(g, *s)})
	}
	truncate(r.rows, limit)
	return r
}

func run_async_blocking_reachable(g *Graph, mod string, limit int) result {
	r := result{cols: cols_async_blocking_reachable}
	var roots []int32
	for _, id := range g.fnSyms() {
		if g.sym(id).IsAsync == 1 {
			roots = append(roots, id)
		}
	}
	depth, parent := g.reach(roots, 4, true)
	type agg struct {
		count int32
		max   int32
		via   map[string]bool
	}
	m := map[int32]*agg{}
	for sym, d := range depth {
		if d == 0 {
			continue
		}
		s := g.sym(sym)
		if s.NBlocking == 0 {
			continue
		}

		root := int32(0)
		for cur := sym; ; {
			p, ok := parent[cur]
			if !ok {
				root = cur
				break
			}
			cur = p
		}
		rs := g.sym(root)
		if rs.IsAsync != 1 || !isFuncKind(g.S(rs.Kind)) {
			continue
		}
		if !g.nogen(rs.FileID) || !g.inModule(*rs, mod) {
			continue
		}
		a := m[root]
		if a == nil {
			a = &agg{via: map[string]bool{}}
			m[root] = a
		}
		a.count++
		if d > a.max {
			a.max = d
		}
		a.via[g.S(s.Name)] = true
	}
	var ids []int32
	for k := range m {
		ids = append(ids, k)
	}
	sort.Slice(ids, func(i, j int) bool {
		if m[ids[i]].count != m[ids[j]].count {
			return m[ids[i]].count > m[ids[j]].count
		}
		return g.S(g.Symbols[ids[i]-1].Name) < g.S(g.Symbols[ids[j]-1].Name)
	})
	for i, id := range ids {
		if limit >= 0 && i >= limit {
			break
		}
		s := g.sym(id)
		var via []string
		for k := range m[id].via {
			via = append(via, k)
		}
		sort.Strings(via)
		r.rows = append(r.rows, []string{g.S(s.Name), num(m[id].count),
			num(m[id].max), strings.Join(via, ","), at(g, *s)})
	}
	return r
}

func run_await_in_loop(g *Graph, mod string, limit int) result {
	r := result{cols: cols_await_in_loop}
	var rows []qrow
	for _, id := range g.fnSyms() {
		s := g.sym(id)
		if s.AwaitInLoop == 0 || !g.nogen(s.FileID) || !g.inModule(*s, mod) {
			continue
		}

		rows = append(rows, qrow{
			order: []oterm{dsc(s.AwaitInLoop), dsc(s.FanIn),
				ascT(g.S(s.Name)), ascI(s.FileID)},
			cells: []string{g.S(s.Name), num(s.AwaitInLoop), num(s.MaxLoopDepth),
				num(s.NAwait), num(s.NNet), num(s.FanIn), at(g, *s)},
			ord: id,
		})
	}
	r.cols = cols_await_in_loop
	qemit(&r, rows, limit)
	return r
}

func run_mutable_defaults(g *Graph, mod string, limit int) result {
	r := result{cols: cols_mutable_defaults}
	type def struct {
		keys  []int32
		cells []string
	}
	var rows []def
	for _, id := range g.fnSyms() {
		s := g.sym(id)
		if s.NMutableDefault == 0 || !g.nogen(s.FileID) || !g.inModule(*s, mod) {
			continue
		}
		var parts []string
		n := 0
		for _, p := range g.paramRows(id) {
			if p.DefaultValue == 0 {
				continue
			}

			parts = append(parts, g.S(p.Name)+"="+g.S(p.DefaultValue))
			n++
		}
		rows = append(rows, def{keys: []int32{s.FanIn, s.NMutableDefault},
			cells: []string{g.S(s.Name), num(s.NMutableDefault), num(s.FanIn),
				num(s.NParams), num(s.IsPublic), strings.Join(parts, ","), at(g, *s)}})
	}
	sort.SliceStable(rows, func(i, j int) bool {
		for k := range 2 {
			if rows[i].keys[k] != rows[j].keys[k] {
				return rows[i].keys[k] > rows[j].keys[k]
			}
		}
		return rows[i].cells[0] < rows[j].cells[0]
	})
	for i, x := range rows {
		if limit >= 0 && i >= limit {
			break
		}
		r.rows = append(r.rows, x.cells)
	}
	return r
}

func run_untrusted_frontier(g *Graph, mod string, limit int) result {
	r := result{cols: cols_untrusted_frontier}
	var roots []int32
	for i := range g.Symbols {
		s := &g.Symbols[i]

		if s.NExec+s.NDeserialize+s.NShellTrue == 0 {
			continue
		}
		if !g.fileOK(s.FileID, false) {
			continue
		}
		roots = append(roots, int32(i+1))
	}
	type agg struct{ hops, count int32 }
	m := make(map[int32]*agg, len(roots))
	callersOf := g.callerAdjacency()
	for _, root := range roots {

		minDepth := map[int32]int32{root: 0}
		frontier := []int32{root}
		for d := int32(1); d <= 5 && len(frontier) > 0; d++ {
			var next []int32
			for _, cur := range frontier {
				for _, e := range callersOf[cur] {
					if e.IsSelf == 1 {
						continue
					}
					if _, seen := minDepth[e.CallerID]; seen {
						continue
					}
					minDepth[e.CallerID] = d
					next = append(next, e.CallerID)
				}
			}
			frontier = next
		}
		e := m[root]
		if e == nil {
			e = &agg{hops: 1 << 30}
			m[root] = e
		}
		for sym, d := range minDepth {
			a := g.sym(sym)
			if a.IsPublic != 1 || !isFuncKind(g.S(a.Kind)) {
				continue
			}
			if d < e.hops {
				e.hops = d
			}
			e.count++
		}
	}
	var ids []int32
	for k, v := range m {
		if v.count > 0 {
			ids = append(ids, k)
		}
	}
	sort.Slice(ids, func(i, j int) bool {
		ai, aj := m[ids[i]], m[ids[j]]
		if ai.hops != aj.hops {
			return ai.hops < aj.hops
		}
		if ai.count != aj.count {
			return ai.count > aj.count
		}
		return ids[i] < ids[j]
	})
	for _, id := range ids {
		s := g.sym(id)
		if !g.fileOK(s.FileID, false) || !g.inModule(*s, mod) {
			continue
		}
		e := m[id]
		r.rows = append(r.rows, []string{g.S(s.Name), num(s.NExec),
			num(s.NDeserialize), num(s.NShell), num(s.NShellTrue),
			num(e.hops), num(e.count), at(g, *s)})
	}
	truncate(r.rows, limit)
	return r
}

func (g *Graph) callerAdjacency() map[int32][]Edge {
	out := make(map[int32][]Edge, len(g.Edges))
	for _, e := range g.Edges {
		out[e.CalleeID] = append(out[e.CalleeID], e)
	}
	return out
}
func run_sql_built_by_hand(g *Graph, mod string, limit int) result {
	r := result{cols: cols_sql_built_by_hand}
	var rows []row
	for _, id := range g.fnSyms() {
		s := g.sym(id)
		total := s.NSqlFstring + s.NSqlConcat + s.NSqlFormat
		if total == 0 {
			continue
		}
		f := g.Files[s.FileID-1]
		if f.IsTest == 1 || !g.inModule(*s, mod) {
			continue
		}
		rows = append(rows, row{id: id, keys: []int32{total, s.FanIn, -id},
			cells: []string{g.S(s.Name), num(s.NSqlFstring), num(s.NSqlConcat),
				num(s.NSqlFormat), num(s.NSql), num(s.FanIn), num(s.IsPublic), at(g, *s)}})
	}
	r.cols = cols_sql_built_by_hand
	g.emit(&r, rows, limit)
	return r
}

func run_n_plus_one(g *Graph, mod string, limit int) result {
	r := result{cols: cols_n_plus_one}
	var rows []row
	for _, id := range g.fnSyms() {
		s := g.sym(id)
		if g.Files[s.FileID-1].IsTest == 1 {
			continue
		}
		hit := (s.QueryInLoop > 0 && (s.NSql > 0 || s.IOInLoop > 0)) ||
			(s.NSql > 0 && s.MaxLoopDepth > 0)
		if !hit || !g.inModule(*s, mod) {
			continue
		}
		rows = append(rows, row{id: id, keys: []int32{s.QueryInLoop, s.MaxLoopDepth, -id},
			cells: []string{g.S(s.Name), num(s.QueryInLoop), num(s.MaxLoopDepth),
				num(s.NSql), num(s.IOInLoop), num(s.FanIn), at(g, *s)}})
	}
	r.cols = cols_n_plus_one
	g.emit(&r, rows, limit)
	return r
}

func run_loop_multiplied(g *Graph, mod string, limit int) result {
	r := result{cols: cols_loop_multiplied}
	var rows []row

	for _, id := range g.allSyms() {
		s := g.sym(id)

		if s.MaxLoopDepth == 0 || !g.fileOK(s.FileID, true) {
			continue
		}
		score := s.RegexInLoop*3 + s.ConcatInLoop*3 + s.LenInLoop + s.NRangeLen
		if score == 0 || !g.inModule(*s, mod) {
			continue
		}
		rows = append(rows, row{id: id, keys: []int32{score, -id},
			cells: []string{g.S(s.Name), num(s.MaxLoopDepth), num(s.CallInLoop),
				num(s.RegexInLoop), num(s.LenInLoop), num(s.NAppendInLoop),
				num(s.ConcatInLoop), num(s.NRangeLen), num(s.FanIn), at(g, *s)}})
	}
	r.cols = cols_loop_multiplied
	g.emit(&r, rows, limit)
	return r
}

func run_quadratic_strings(g *Graph, mod string, limit int) result {
	r := result{cols: cols_quadratic_strings}
	var rows []qrow
	for _, id := range g.allSyms() {
		s := g.sym(id)
		if s.ConcatInLoop == 0 || !g.inModule(*s, mod) {
			continue
		}

		rows = append(rows, qrow{
			order: []oterm{dsc(s.ConcatInLoop), dsc(s.MaxLoopDepth),
				ascT(g.path(s.FileID))},
			cells: []string{g.S(s.Name), num(s.ConcatInLoop), num(s.MaxLoopDepth),
				num(s.NStringLit), num(s.FanIn), num(s.SLOC), at(g, *s)},
			ord: id,
		})
	}
	r.cols = cols_quadratic_strings
	qemit(&r, rows, limit)
	return r
}

func run_swallowed_errors(g *Graph, mod string, limit int) result {
	r := result{cols: cols_swallowed_errors}
	type agg struct {
		handlers, bare, broad, empty, reraise, logged int32
	}
	m := map[int32]*agg{}
	for _, h := range g.Handlers {
		if h.IsBroad != 1 {
			continue
		}
		s := g.sym(h.SymbolID)
		if g.Files[s.FileID-1].IsTest == 1 || !g.inModule(*s, mod) {
			continue
		}
		a := m[h.SymbolID]
		if a == nil {
			a = &agg{}
			m[h.SymbolID] = a
		}
		a.handlers++
		a.bare += h.IsBare
		a.broad += h.IsBroad
		a.empty += h.IsEmpty
		a.reraise += h.HasReraise
		a.logged += h.HasLog
	}
	var rows []row
	for id, a := range m {
		if a.logged != 0 || a.reraise != 0 {
			continue
		}
		s := g.sym(id)
		rows = append(rows, row{id: id, keys: []int32{s.NIO + s.NNet + s.NSql, a.broad, -id},
			cells: []string{g.S(s.Name), num(a.handlers), num(a.bare), num(a.broad),
				num(a.empty), num(a.reraise), num(a.logged),
				num(s.NIO + s.NNet + s.NSql), at(g, *s)}})
	}
	r.cols = cols_swallowed_errors
	g.emit(&r, rows, limit)
	return r
}

func run_reflection_opacity(g *Graph, mod string, limit int) result {
	r := result{cols: cols_reflection_opacity}
	type agg struct {
		n, lit     int32
		fns, files map[int32]bool
		ex         []string
	}
	m := map[string]*agg{}
	for _, d := range g.DynamicSites {
		if !g.fileOK(d.FileID, false) {
			continue
		}
		s := g.sym(d.SymbolID)
		if !g.inModule(*s, mod) {
			continue
		}
		k := g.S(d.Kind)
		a := m[k]
		if a == nil {
			a = &agg{}
			m[k] = a
		}
		a.n++
		a.lit += d.IsLiteralArg

		if d.SymbolID >= 0 {
			if a.fns == nil {
				a.fns = map[int32]bool{}
			}
			a.fns[d.SymbolID] = true
		}
		if a.files == nil {
			a.files = map[int32]bool{}
		}
		a.files[d.FileID] = true

		if e := truncStr(g.S(d.Expr), 40); e != "" {
			a.ex = append(a.ex, e)
		}
	}
	var rows []groupedRow
	for k, a := range m {
		rows = append(rows, groupedRow{key: k, keys: []int32{a.n},
			cells: []string{k, num(a.n), num(a.lit), num(int32(len(a.fns))),
				num(int32(len(a.files))), joinDistinct(a.ex, ",")}})
	}
	r.cols = cols_reflection_opacity
	rankGroups(g, rows)
	emitGroups(&r, rows, limit)
	return r
}

func run_decorator_roots(g *Graph, mod string, limit int) result {
	r := result{cols: cols_decorator_roots}
	interesting := []string{"route", "task", "get", "post", "command", "handler",
		"register", "fixture", "receiver", "signal", "event", "subscribe", "hook"}
	var rows []row
	for _, id := range g.fnSyms() {
		s := g.sym(id)
		if s.FanIn != 0 || !g.inModule(*s, mod) {
			continue
		}

		names := g.attrsOf(id)
		order := make([]int, len(names))
		for k := range order {
			order[k] = k
		}
		sort.SliceStable(order, func(x, y int) bool {
			return names[order[x]] < names[order[y]]
		})
		for _, k := range order {
			a := names[k]
			hit := false
			for _, kk := range interesting {
				if strings.Contains(strings.ToLower(a), kk) {
					hit = true
					break
				}
			}
			if !hit {
				continue
			}
			rows = append(rows, row{id: id, keys: []int32{s.SLOC, -id},
				cells: []string{g.S(s.Name), a, num(s.FanIn), num(s.SLOC),
					num(s.Cyclomatic), num(s.IsAsync), at(g, *s)}})
		}
	}
	r.cols = cols_decorator_roots
	g.emit(&r, rows, limit)
	return r
}

func run_dead_code(g *Graph, mod string, limit int) result {
	r := result{cols: cols_dead_code}
	decorated := map[int32]bool{}
	for _, a := range g.Attributes {
		if a.SymbolID >= 0 {
			decorated[a.SymbolID] = true
		}
	}
	var rows []qrow
	for _, id := range g.fnSyms() {
		s := g.sym(id)
		if s.FanIn != 0 || s.IsPublic != 0 || s.IsTest != 0 || s.IsEntrypoint != 0 ||
			s.IsDunder != 0 || s.IsOverride != 0 || s.IsAbstract != 0 ||
			s.IsProperty != 0 || s.IsOverload != 0 {
			continue
		}
		if !g.fileOK(s.FileID, false) || !g.inModule(*s, mod) || decorated[id] {
			continue
		}
		rows = append(rows, qrow{
			order: []oterm{dsc(s.SLOC), ascI(s.FileID), ascT(g.S(s.Kind))},
			cells: []string{g.S(s.Name), g.S(s.Kind), num(s.SLOC), num(s.Cyclomatic),
				num(s.NExternalCalls), at(g, *s)},
			ord: id,
		})
	}
	r.cols = cols_dead_code
	qemit(&r, rows, limit)
	return r
}

func run_untested(g *Graph, mod string, limit int) result {
	r := result{cols: cols_untested}
	testReached := map[int32]bool{}
	for _, e := range g.Edges {
		cs := g.sym(e.CallerID)

		if g.Files[cs.FileID-1].IsTest == 1 || cs.IsTest == 1 {
			testReached[e.CalleeID] = true
		}
	}
	var rows []qrow
	for _, id := range g.fnSyms() {
		s := g.sym(id)

		if !g.fileOK(s.FileID, false) || !g.inModule(*s, mod) ||
			testReached[id] || s.IsTest == 1 || s.SLOC <= 5 {
			continue
		}

		rows = append(rows, qrow{
			order: []oterm{dsc(s.RiskScore), dsc(s.FanIn),
				ascI(s.FileID), ascT(g.S(s.Kind))},
			cells: []string{g.S(s.Name), num(s.FanIn), num(s.Cyclomatic),
				num(s.SLOC), num(s.RiskScore), num(s.IsPublic), at(g, *s)},
			ord: id,
		})
	}
	r.cols = cols_untested
	qemit(&r, rows, limit)
	return r
}

func truncate(rows [][]string, limit int) {
	if limit >= 0 && len(rows) > limit {
		rows = rows[:limit]
	}
}

func itoa32(v int32) string { return strconv.Itoa(int(v)) }

func run_unbounded_caches(g *Graph, mod string, limit int) result {
	r := result{cols: cols_unbounded_caches}
	var rows []qrow

	for i := range g.Symbols {
		s := &g.Symbols[i]
		if !g.notest(s.FileID) || !g.modOK(s, mod) {
			continue
		}
		for _, a := range g.attrRows(s.ID) {
			name := g.S(a.Name)
			if !dbLike(name, "%lru_cache%") && !dbLike(name, "%cache%") {
				continue
			}
			if dbLike(g.S(a.Args), "%maxsize%") {
				continue
			}
			rows = append(rows, qrow{
				order: []oterm{dsc(s.FanIn), ascI(0)},
				cells: []string{g.S(s.Name), "cache-decorator", name,
					cellInt(s.NParams), cellInt(s.FanIn), at(g, *s)},
				ord: a.ID,
			})
		}
	}

	for _, v := range g.ModuleVars {
		if v.IsMutableContainer != 1 || v.IsConstant != 0 || !g.notest(v.FileID) {
			continue
		}
		if mod != "%" && !dbLike(g.moduleName(v.ModuleID), mod) {
			continue
		}
		rows = append(rows, qrow{
			order: []oterm{dsc(0), ascI(1)},
			cells: []string{g.S(v.Name), "module-mutable", g.S(v.Type), "0", "0",
				g.path(v.FileID) + ":" + itoa(v.Line)},
			ord: v.ID,
		})
	}
	qemit(&r, rows, limit)
	return r
}

func run_shared_mutable_state(g *Graph, mod string, limit int) result {
	r := result{cols: cols_shared_mutable_state}

	type fileAgg struct{ fns, stmts int32 }
	byFile := make(map[int32]fileAgg, len(g.Files))
	for i := range g.Symbols {
		s := &g.Symbols[i]
		if s.NGlobalStmt <= 0 {
			continue
		}
		a := byFile[s.FileID]
		a.fns++
		a.stmts += s.NGlobalStmt
		byFile[s.FileID] = a
	}
	var rows []qrow
	for _, v := range g.ModuleVars {
		if v.IsMutableContainer != 1 || v.IsConstant != 0 || !g.notestgen(v.FileID) {
			continue
		}
		if mod != "%" && !dbLike(g.moduleName(v.ModuleID), mod) {
			continue
		}
		a := byFile[v.FileID]
		rows = append(rows, qrow{
			order: []oterm{dsc(a.stmts), dsc(a.fns)},
			cells: []string{g.S(v.Name), g.path(v.FileID), cellInt(v.Line), g.S(v.Type),
				cellInt(v.HasCallInit), cellInt(a.fns), cellInt(a.stmts)},
			ord: v.ID,
		})
	}
	qemit(&r, rows, limit)
	return r
}

func run_import_cycles(g *Graph, mod string, limit int) result {
	r := result{cols: cols_import_cycles}
	type pair struct{ a, b int32 }
	ab := map[pair]int32{}
	ba := map[pair]int32{}

	revSeen := map[pair]map[int32]bool{}
	for _, i1 := range g.Imports {
		if i1.TargetID < 1 || int(i1.TargetID) > len(g.Files) {
			continue
		}
		m1 := g.Files[i1.FileID-1].ModuleID
		m2 := g.Files[i1.TargetID-1].ModuleID
		if m1 < 1 || m2 < 1 || m1 >= m2 {
			continue
		}
		p := pair{m1, m2}

		back := 0
		seen := revSeen[p]
		if seen == nil {
			seen = map[int32]bool{}
			revSeen[p] = seen
		}
		for _, i2 := range g.importFor(i1.TargetID) {
			if i2.TargetID >= 1 && int(i2.TargetID) <= len(g.Files) &&
				g.Files[i2.TargetID-1].ModuleID == m1 {
				seen[i2.ID] = true
				back++
			}
		}
		if back == 0 {
			continue
		}
		ab[p]++
		ba[p] = int32(len(seen))
	}
	var rows []qrow
	pairs := make([]pair, 0, len(ab))
	for p := range ab {
		pairs = append(pairs, p)
	}
	sort.Slice(pairs, func(i, j int) bool {
		if pairs[i].a != pairs[j].a {
			return pairs[i].a < pairs[j].a
		}
		return pairs[i].b < pairs[j].b
	})
	for _, p := range pairs {
		fwd := ab[p]
		back := ba[p]
		if back == 0 {
			continue
		}
		an := g.moduleName(p.a)
		if mod != "%" && !dbLike(an, mod) {
			continue
		}
		rows = append(rows, qrow{
			order: []oterm{dsc(fwd + back)},
			cells: []string{an, g.moduleName(p.b), cellInt(fwd), cellInt(back)},
			ord:   p.a,
		})
	}
	qemit(&r, rows, limit)
	return r
}

func run_import_workarounds(g *Graph, mod string, limit int) result {
	r := result{cols: cols_import_workarounds}

	spans := make(map[int32][]int32, len(g.Files))
	for i := range g.Symbols {
		s := &g.Symbols[i]
		if !isFuncKind(g.S(s.Kind)) {
			continue
		}
		spans[s.FileID] = append(spans[s.FileID], s.ID)
	}
	for fid := range spans {
		ids := spans[fid]
		sort.Slice(ids, func(a, b int) bool {
			si, sj := g.Symbols[ids[a]-1], g.Symbols[ids[b]-1]
			if si.LineStart != sj.LineStart {
				return si.LineStart < sj.LineStart
			}
			return si.ID < sj.ID
		})
	}
	var rows []qrow
	for _, im := range g.Imports {
		f := g.Files[im.FileID-1]
		if f.IsGenerated != 0 {
			continue
		}
		if mod != "%" && !dbLike(g.moduleName(f.ModuleID), mod) {
			continue
		}
		ids := spans[im.FileID]

		for _, id := range ids {
			s := g.sym(id)
			if im.Line < s.LineStart {
				break
			}
			if im.Line > s.LineEnd {
				continue
			}
			rows = append(rows, qrow{
				order: []oterm{dsc(s.FanIn)},
				cells: []string{g.S(s.Name), g.S(im.Target), g.S(im.Kind),
					cellInt(s.FanIn), cellInt(im.Line), g.path(im.FileID) + ":" + itoa(im.Line)},
				ord: int32(len(rows)) + 1,
			})
		}
	}
	qemit(&r, rows, limit)
	return r
}

func run_weak_crypto(g *Graph, mod string, limit int) result {
	r := result{cols: cols_weak_crypto}
	var rows []qrow
	for i := range g.Hazards {
		h := &g.Hazards[i]
		if h.SymbolID < 1 || int(h.SymbolID) > len(g.Symbols) ||
			g.S(h.Category) != "crypto" {
			continue
		}
		s := g.sym(h.SymbolID)
		if !g.notest(s.FileID) || !g.modOK(s, mod) {
			continue
		}
		rows = append(rows, qrow{
			order: []oterm{dsc(s.FanIn), dsc(h.N)},
			cells: []string{g.S(s.Name), g.S(h.Pattern), cellInt(h.N), cellInt(h.FirstLine),
				cellInt(s.IsPublic), cellInt(s.FanIn),
				g.path(s.FileID) + ":" + itoa(h.FirstLine)},
			ord: s.ID,
		})
	}
	qemit(&r, rows, limit)
	return r
}

func run_unsafe_decode_reachable(g *Graph, mod string, limit int) result {
	r := result{cols: cols_unsafe_decode_reachable}
	var roots []int32
	for i := range g.Symbols {
		s := &g.Symbols[i]
		if s.NPickleLoad+s.NYamlLoad+s.NEvalExec > 0 && g.notest(s.FileID) {
			roots = append(roots, s.ID)
		}
	}
	type rp struct{ root, sym int32 }
	best := make(map[rp]int32, len(roots)*8)
	for _, root := range roots {
		depth := map[int32]int32{root: 0}
		queue := []int32{root}
		for i := 0; i < len(queue); i++ {
			cur := queue[i]
			if depth[cur] >= 4 {
				continue
			}
			for _, caller := range g.callers(cur) {
				if caller == cur {
					continue
				}
				if _, seen := depth[caller]; seen {
					continue
				}
				depth[caller] = depth[cur] + 1
				queue = append(queue, caller)
			}
		}
		for sym, d := range depth {
			best[rp{root, sym}] = d
		}
	}

	pairs := make([]rp, 0, len(best))
	for p := range best {
		pairs = append(pairs, p)
	}
	sort.Slice(pairs, func(i, j int) bool {
		if pairs[i].root != pairs[j].root {
			return pairs[i].root < pairs[j].root
		}
		return pairs[i].sym < pairs[j].sym
	})
	var rows []qrow
	for _, p := range pairs {
		d := best[p]
		src := g.sym(p.sym)
		if src.IsEntrypoint != 1 && src.IsPublic != 1 {
			continue
		}
		s := g.sym(p.root)
		if !g.notest(s.FileID) || !g.modOK(s, mod) {
			continue
		}

		rows = append(rows, qrow{
			order: []oterm{dsc(-d), dsc(s.NPickleLoad + s.NEvalExec), ascI(p.root)},
			cells: []string{g.S(s.Name), g.S(src.Name), cellInt(d),
				cellInt(s.NPickleLoad), cellInt(s.NYamlLoad), cellInt(s.NEvalExec),
				cellInt(s.NSubprocess), cellInt(s.FanIn), g.moduleName(s.ModuleID),
				at(g, *s)},
			ord: -p.sym,
		})
	}
	qemit(&r, rows, limit)
	return r
}

func run_decorator_depth(g *Graph, mod string, limit int) result {
	r := result{cols: cols_decorator_depth}
	var rows []qrow
	for i := range g.Symbols {
		s := &g.Symbols[i]
		if s.NDecorators < 3 || !g.notest(s.FileID) || !g.modOK(s, mod) {
			continue
		}
		rows = append(rows, qrow{
			order: []oterm{dsc(s.NDecorators), dsc(s.FanIn)},
			cells: []string{g.S(s.Name), g.S(s.Kind), cellInt(s.NDecorators),
				cellInt(int32(len(g.attrRows(s.ID)))), cellInt(s.SLOC),
				cellInt(s.FanIn), at(g, *s)},
			ord: s.ID,
		})
	}
	qemit(&r, rows, limit)
	return r
}

func run_non_public_leak(g *Graph, mod string, limit int) result {
	r := result{cols: cols_non_public_leak}
	var rows []qrow
	for calleeID := int32(1); calleeID <= int32(len(g.Symbols)); calleeID++ {
		cal := g.sym(calleeID)
		name := g.S(cal.Name)
		if instr(name, "_") != 1 || instr(name, "__") == 1 {
			continue
		}
		if mod != "%" && !dbLike(g.moduleName(cal.ModuleID), mod) {
			continue
		}
		defSet, callSet := newGC(), newGC()
		var nCalls int32
		any := false
		for _, edgeIdx := range g.incomingEdges(calleeID) {
			e := g.Edges[edgeIdx]
			call := g.sym(e.CallerID)
			if call.FileID == cal.FileID {
				continue
			}
			if g.Files[call.FileID-1].IsTest != 0 {
				continue
			}
			any = true
			defSet.add(g.path(cal.FileID))
			callSet.add(g.path(call.FileID))
			nCalls += e.NCalls
		}
		if !any {
			continue
		}
		rows = append(rows, qrow{
			order: []oterm{dsc(nCalls), dsc(cal.SLOC)},
			cells: []string{name, g.S(cal.Kind), cellInt(cal.SLOC),
				defSet.String(), callSet.String(), cellInt(nCalls)},
			ord: calleeID,
		})
	}
	qemit(&r, rows, limit)
	return r
}

func run_wildcard_import_rank(g *Graph, mod string, limit int) result {
	r := result{cols: cols_wildcard_import_rank}
	type gk struct{ n, exp int32 }
	agg := map[int32]*gk{}
	for _, im := range g.Imports {
		if im.IsWildcard != 1 || !g.notest(im.FileID) {
			continue
		}
		f := g.Files[im.FileID-1]
		if mod != "%" && !dbLike(g.moduleName(f.ModuleID), mod) {
			continue
		}
		a := agg[im.FileID]
		if a == nil {
			a = &gk{}
			agg[im.FileID] = a
		}
		a.n++
		a.exp = int32(len(g.exportFor(im.FileID)))
	}
	var rows []qrow
	for fid, a := range agg {
		f := g.Files[fid-1]
		rows = append(rows, qrow{
			order: []oterm{dsc(a.n), dsc(f.SLOC)},
			cells: []string{g.S(f.Path), cellInt(a.n), cellInt(a.exp), cellInt(f.SLOC)},
			ord:   fid,
		})
	}
	qemit(&r, rows, limit)
	return r
}

func run_all_reexports(g *Graph, mod string, limit int) result {
	r := result{cols: cols_all_reexports}

	type key struct {
		fid int32
		n   string
	}
	here := map[key]int32{}
	anywhere := map[string]int32{}
	for i := range g.Symbols {
		s := &g.Symbols[i]
		k := g.S(s.Kind)
		if k != "function" && k != "class" {
			continue
		}
		n := g.S(s.Name)
		anywhere[n]++
		here[key{s.FileID, n}]++
	}
	var rows []qrow
	for i := range g.AllExports {
		ae := &g.AllExports[i]
		f := g.Files[ae.FileID-1]
		if mod != "%" && !dbLike(g.moduleName(f.ModuleID), mod) {
			continue
		}
		nm := g.S(ae.Name)
		nHere := here[key{ae.FileID, nm}]
		if nHere != 0 {
			continue
		}
		rows = append(rows, qrow{
			order: []oterm{ascT(g.S(f.Path)), dsc(-ae.Line)},
			cells: []string{g.S(f.Path), nm, cellInt(ae.Line), cellInt(nHere),
				cellInt(anywhere[nm])},
			ord: ae.ID,
		})
	}
	qemit(&r, rows, limit)
	return r
}

func run_relative_import_depth(g *Graph, mod string, limit int) result {
	r := result{cols: cols_relative_import_depth}
	type gk struct {
		maxDepth, relative, deep int32
		hasMax                   bool
	}
	agg := map[int32]*gk{}
	for _, im := range g.Imports {
		if im.IsRelative != 1 || !g.notest(im.FileID) {
			continue
		}
		t := g.S(im.Target)
		d := int32(len(t) - len(ltrimDots(t)))
		if d < 1 {
			continue
		}
		f := g.Files[im.FileID-1]
		if mod != "%" && !dbLike(g.moduleName(f.ModuleID), mod) {
			continue
		}
		a := agg[im.FileID]
		if a == nil {
			a = &gk{}
			agg[im.FileID] = a
		}
		a.relative++
		if d >= 2 {
			a.deep++
		}
		if !a.hasMax || d > a.maxDepth {
			a.maxDepth, a.hasMax = d, true
		}
	}
	var rows []qrow
	for fid, a := range agg {
		rows = append(rows, qrow{
			order: []oterm{dsc(a.deep), dsc(a.maxDepth)},
			cells: []string{g.path(fid), cellInt(a.maxDepth), cellInt(a.relative),
				cellInt(a.deep)},
			ord: fid,
		})
	}
	qemit(&r, rows, limit)
	return r
}

func run_method_kind_mix(g *Graph, mod string, limit int) result {
	r := result{cols: cols_method_kind_mix}
	type gk struct {
		cm, sm, total, minLine int32
		has                    bool
	}
	agg := map[int32]*gk{}
	for i := range g.Symbols {
		s := &g.Symbols[i]
		if g.S(s.Kind) != "method" || s.ParentID < 1 || int(s.ParentID) > len(g.Symbols) {
			continue
		}
		pc := g.sym(s.ParentID)
		if g.S(pc.Kind) != "class" || !g.notest(pc.FileID) {
			continue
		}
		if mod != "%" && !dbLike(g.moduleName(pc.ModuleID), mod) {
			continue
		}
		a := agg[s.ParentID]
		if a == nil {
			a = &gk{}
			agg[s.ParentID] = a
		}
		a.cm += s.IsClassmethod
		a.sm += s.IsStaticmethod
		a.total++
		if !a.has || s.LineStart < a.minLine {
			a.minLine, a.has = s.LineStart, true
		}
	}
	var rows []qrow
	for pid, a := range agg {
		if a.cm+a.sm == 0 {
			continue
		}
		pc := g.sym(pid)
		pct, _ := castInt(100.0*float64(a.cm+a.sm)/float64(a.total), a.total != 0)
		rows = append(rows, qrow{
			order: []oterm{dsc(a.cm + a.sm), dsc(a.total)},
			cells: []string{g.S(pc.Name), cellInt(a.cm), cellInt(a.sm),
				cellInt(a.total - a.cm - a.sm), cellInt(a.total), cellInt(pct),
				g.path(pc.FileID) + ":" + itoa(a.minLine)},
			ord: pid,
		})
	}
	qemit(&r, rows, limit)
	return r
}

type inputSurface struct {
	cols  []string
	keep  pred
	order func(s *Symbol, nInputs int32) []oterm
	cells func(g *Graph, s *Symbol, nInputs int32, kinds string) []string

	onlyKind string
}

func (g *Graph) runInputSurface(q inputSurface, mod string, limit int) result {
	r := result{cols: q.cols}
	var rows []qrow
	for i := range g.Symbols {
		s := &g.Symbols[i]
		if !q.keep(g, s) || !g.notestgen(s.FileID) || !g.modOK(s, mod) {
			continue
		}
		ins := g.inputFor(s.ID)
		if len(ins) == 0 {
			continue
		}
		if q.onlyKind != "" {
			matched := int32(0)
			for _, u := range ins {
				if g.S(u.Kind) == q.onlyKind {
					matched++
				}
			}
			if matched == 0 {
				continue
			}
			ins = nil
			for _, u := range g.inputFor(s.ID) {
				if g.S(u.Kind) == q.onlyKind {
					ins = append(ins, u)
				}
			}
		}
		gc := newGC()
		for _, u := range ins {
			gc.add(g.S(u.Kind))
		}
		rows = append(rows, qrow{
			order: q.order(s, int32(len(ins))),
			cells: q.cells(g, s, int32(len(ins)), gc.String()),
			ord:   s.ID,
		})
	}
	qemit(&r, rows, limit)
	return r
}

func run_open_redirect_surface(g *Graph, mod string, limit int) result {
	return g.runInputSurface(inputSurface{
		cols:  cols_open_redirect_surface,
		keep:  pGT(func(s *Symbol) int32 { return s.NRedirect }, 0),
		order: func(s *Symbol, n int32) []oterm { return []oterm{dsc(s.FanIn), dsc(s.NRedirect)} },
		cells: func(g *Graph, s *Symbol, n int32, kinds string) []string {
			return []string{g.S(s.Name), cellInt(s.NRedirect), cellInt(n), kinds,
				cellInt(s.FanIn), at(g, *s)}
		},
	}, mod, limit)
}

func run_ssrf_fetch_surface(g *Graph, mod string, limit int) result {
	return g.runInputSurface(inputSurface{
		cols:  cols_ssrf_fetch_surface,
		keep:  pGT(func(s *Symbol) int32 { return s.NFetch }, 0),
		order: func(s *Symbol, n int32) []oterm { return []oterm{dsc(s.NFetch), dsc(n)} },
		cells: func(g *Graph, s *Symbol, n int32, kinds string) []string {
			return []string{g.S(s.Name), cellInt(s.NFetch), cellInt(n), kinds, at(g, *s)}
		},
	}, mod, limit)
}

func run_path_traversal_surface(g *Graph, mod string, limit int) result {
	return g.runInputSurface(inputSurface{
		cols:  cols_path_traversal_surface,
		keep:  pGT(func(s *Symbol) int32 { return s.NDynamicOpen }, 0),
		order: func(s *Symbol, n int32) []oterm { return []oterm{dsc(s.NDynamicOpen), dsc(n)} },
		cells: func(g *Graph, s *Symbol, n int32, kinds string) []string {
			return []string{g.S(s.Name), cellInt(s.NDynamicOpen), cellInt(n), kinds, at(g, *s)}
		},
	}, mod, limit)
}

func run_log_injection_surface(g *Graph, mod string, limit int) result {
	return g.runInputSurface(inputSurface{
		cols:  cols_log_injection_surface,
		keep:  pGT(func(s *Symbol) int32 { return s.NLogCall }, 0),
		order: func(s *Symbol, n int32) []oterm { return []oterm{dsc(s.NLogCall), dsc(n)} },
		cells: func(g *Graph, s *Symbol, n int32, kinds string) []string {
			return []string{g.S(s.Name), cellInt(s.NLogCall), cellInt(n), kinds,
				cellInt(s.FanIn), at(g, *s)}
		},
	}, mod, limit)
}

func run_mark_safe_surface(g *Graph, mod string, limit int) result {
	return g.runInputSurface(inputSurface{
		cols:  cols_mark_safe_surface,
		keep:  pGT(func(s *Symbol) int32 { return s.NMarkSafe }, 0),
		order: func(s *Symbol, n int32) []oterm { return []oterm{dsc(s.FanIn), dsc(s.NMarkSafe)} },
		cells: func(g *Graph, s *Symbol, n int32, kinds string) []string {
			return []string{g.S(s.Name), cellInt(s.NMarkSafe), cellInt(n), kinds,
				cellInt(s.FanIn), at(g, *s)}
		},
	}, mod, limit)
}

func run_mass_assignment_surface(g *Graph, mod string, limit int) result {
	return g.runInputSurface(inputSurface{
		cols:  cols_mass_assignment_surface,
		keep:  pGT(func(s *Symbol) int32 { return s.NMassAssign }, 0),
		order: func(s *Symbol, n int32) []oterm { return []oterm{dsc(s.NMassAssign), dsc(n)} },
		cells: func(g *Graph, s *Symbol, n int32, kinds string) []string {
			return []string{g.S(s.Name), cellInt(s.NMassAssign), cellInt(n), kinds,
				cellInt(s.FanIn), at(g, *s)}
		},
	}, mod, limit)
}

func run_unchecked_upload_surface(g *Graph, mod string, limit int) result {
	return g.runInputSurface(inputSurface{
		cols:     cols_unchecked_upload_surface,
		keep:     pGT(func(s *Symbol) int32 { return s.NUploadSave }, 0),
		order:    func(s *Symbol, n int32) []oterm { return []oterm{dsc(s.NUploadSave), dsc(n)} },
		onlyKind: "form",
		cells: func(g *Graph, s *Symbol, n int32, kinds string) []string {
			return []string{g.S(s.Name), cellInt(s.NUploadSave), cellInt(n), at(g, *s)}
		},
	}, mod, limit)
}

func run_unauthenticated_input_surface(g *Graph, mod string, limit int) result {
	r := result{cols: cols_unauthenticated_input_surface}
	var rows []qrow
	for i := range g.Symbols {
		s := &g.Symbols[i]
		if s.NAuthCall != 0 || !g.notestgen(s.FileID) || !g.modOK(s, mod) {
			continue
		}
		if !hasNoAttrLike(g, s, "%login_required%") || !hasNoAttrLike(g, s, "%permission_required%") {
			continue
		}
		ins := g.inputFor(s.ID)
		if len(ins) == 0 {
			continue
		}

		gc := newGC()
		sites := make([]int, len(ins))
		for k := range sites {
			sites[k] = k
		}
		sort.SliceStable(sites, func(a, b int) bool {
			return g.S(ins[sites[a]].Kind) < g.S(ins[sites[b]].Kind)
		})
		for _, k := range sites {
			gc.add(g.S(ins[k].Kind))
		}
		rows = append(rows, qrow{
			order: []oterm{dsc(int32(len(ins))), dsc(s.SLOC)},
			cells: []string{g.S(s.Name), cellInt(int32(len(ins))), gc.String(), at(g, *s)},
			ord:   s.ID,
		})
	}
	qemit(&r, rows, limit)
	return r
}

func run_hardcoded_secret_candidates(g *Graph, mod string, limit int) result {
	r := result{cols: cols_hardcoded_secret_candidates}
	var rows []qrow
	for i := range g.Secrets {
		sc := &g.Secrets[i]
		if sc.SymbolID < 1 || int(sc.SymbolID) > len(g.Symbols) {
			continue
		}
		s := g.sym(sc.SymbolID)
		if !g.notestgen(s.FileID) || !g.modOK(s, mod) {
			continue
		}
		v := g.S(sc.Value)
		if v != "" && v[0] == '/' {
			continue
		}
		if instr(v, "|") != 0 || instr(v, "%") != 0 {
			continue
		}
		rows = append(rows, qrow{
			order: []oterm{dsc(int32(len(v))), dsc(s.FanIn)},
			cells: []string{g.S(s.Name), v, cellInt(sc.Line), cellInt(s.FanIn),
				g.path(sc.FileID) + ":" + itoa(sc.Line)},
			ord: sc.ID,
		})
	}
	qemit(&r, rows, limit)
	return r
}

func run_exception_in_loop(g *Graph, mod string, limit int) result {
	r := result{cols: cols_exception_in_loop}
	type gk struct{ n, broad int32 }
	agg := map[int32]*gk{}
	for i := range g.Handlers {
		h := &g.Handlers[i]
		if h.InLoop != 1 || h.SymbolID < 1 || int(h.SymbolID) > len(g.Symbols) {
			continue
		}
		s := g.sym(h.SymbolID)
		if !g.nogen(s.FileID) || !g.modOK(s, mod) {
			continue
		}
		a := agg[h.SymbolID]
		if a == nil {
			a = &gk{}
			agg[h.SymbolID] = a
		}
		a.n++
		if h.IsBroad > a.broad {
			a.broad = h.IsBroad
		}
	}
	var rows []qrow
	for sid, a := range agg {
		s := g.sym(sid)
		rows = append(rows, qrow{
			order: []oterm{dsc(a.broad), dsc(s.FanIn)},
			cells: []string{g.path(s.FileID), g.S(s.Name), cellInt(a.n),
				cellInt(a.broad), cellInt(s.FanIn)},
			ord: sid,
		})
	}
	qemit(&r, rows, limit)
	return r
}

func run_call_in_default_argument(g *Graph, mod string, limit int) result {
	r := result{cols: cols_call_in_default_argument}
	var rows []qrow
	for i := range g.Params {
		p := &g.Params[i]
		if p.SymbolID < 1 || int(p.SymbolID) > len(g.Symbols) ||
			g.Strings.IsNull(p.DefaultValue) {
			continue
		}
		if instr(g.S(p.DefaultValue), "(") == 0 {
			continue
		}
		s := g.sym(p.SymbolID)
		if !g.nogen(s.FileID) || !g.modOK(s, mod) {
			continue
		}
		rows = append(rows, qrow{
			order: []oterm{dsc(s.FanIn)},
			cells: []string{g.path(s.FileID), g.S(s.Name), g.S(p.Name),
				g.cellText(p.DefaultValue), cellInt(s.FanIn)},
			ord: s.ID,
		})
	}
	qemit(&r, rows, limit)
	return r
}

func run_name_shadowing(g *Graph, mod string, limit int) result {
	r := result{cols: cols_name_shadowing}
	var rows []qrow

	for i := range g.Symbols {
		s := &g.Symbols[i]
		if !isFuncKind(g.S(s.Kind)) || !g.nogen(s.FileID) || !g.modOK(s, mod) {
			continue
		}
		p := g.path(s.FileID)
		for _, pr := range g.paramFor(s.ID) {
			if shadowBuiltins[g.S(pr.Name)] {
				rows = append(rows, qrow{
					order: []oterm{dsc(s.FanIn), ascT(g.S(pr.Name)), ascI(0)},
					cells: []string{p, g.S(s.Name), g.S(pr.Name), "param", cellInt(s.FanIn)},
					ord:   s.ID,
				})
			}
		}
	}
	for i := range g.Symbols {
		s := &g.Symbols[i]
		if !isFuncKind(g.S(s.Kind)) || !g.nogen(s.FileID) || !g.modOK(s, mod) {
			continue
		}
		p := g.path(s.FileID)
		for _, l := range g.localFor(s.ID) {
			if shadowBuiltins[g.S(l.Name)] {
				rows = append(rows, qrow{
					order: []oterm{dsc(s.FanIn), ascT(g.S(l.Name)), ascI(1)},
					cells: []string{p, g.S(s.Name), g.S(l.Name), "local", cellInt(s.FanIn)},
					ord:   s.ID,
				})
			}
		}
	}
	for _, mv := range g.ModuleVars {
		if !g.nogen(mv.FileID) {
			continue
		}
		if mod != "%" && !dbLike(g.moduleName(mv.ModuleID), mod) {
			continue
		}
		if shadowBuiltins[g.S(mv.Name)] {
			rows = append(rows, qrow{
				order: []oterm{dsc(0), ascT(g.S(mv.Name)), ascI(2)},
				cells: []string{g.path(mv.FileID), "<module>", g.S(mv.Name), "module_var", "0"},
				ord:   mv.ID,
			})
		}
	}
	qemit(&r, rows, limit)
	return r
}

var shadowBuiltins = func() map[string]bool {
	m := map[string]bool{}
	for _, n := range []string{
		"abs", "all", "any", "bool", "bytes", "dict", "dir", "enumerate",
		"filter", "float", "format", "frozenset", "hash", "hex", "id",
		"input", "int", "iter", "len", "list", "map", "max", "min",
		"next", "object", "oct", "open", "ord", "pow", "print", "range",
		"repr", "reversed", "round", "set", "slice", "sorted", "str",
		"sum", "tuple", "type", "vars", "zip",
	} {
		m[n] = true
	}
	return m
}()

func run_raise_without_from(g *Graph, mod string, limit int) result {
	r := result{cols: cols_raise_without_from}
	var rows []qrow
	for i := range g.Handlers {
		h := &g.Handlers[i]
		if h.HasRaiseNoFrom != 1 || h.SymbolID < 1 || int(h.SymbolID) > len(g.Symbols) {
			continue
		}
		s := g.sym(h.SymbolID)
		if !g.nogen(s.FileID) || !g.modOK(s, mod) {
			continue
		}

		rows = append(rows, qrow{
			order: []oterm{dsc(s.FanIn)},
			cells: []string{g.path(s.FileID), g.S(s.Name), cellInt(h.Line),
				g.S(h.Types), cellInt(s.FanIn)},
			ord: int32(i),
		})
	}
	qemit(&r, rows, limit)
	return r
}

func run_suppression_burden(g *Graph, mod string, limit int) result {
	r := result{cols: cols_suppression_burden}
	type gk struct{ sup, todo, all int32 }
	agg := map[int32]*gk{}
	for i := range g.Markers {
		mk := &g.Markers[i]
		if !g.nogen(mk.FileID) {
			continue
		}
		f := g.Files[mk.FileID-1]
		if mod != "%" && !dbLike(g.moduleName(f.ModuleID), mod) {
			continue
		}
		a := agg[mk.FileID]
		if a == nil {
			a = &gk{}
			agg[mk.FileID] = a
		}
		a.all++
		if suppressionKinds[g.S(mk.Kind)] {
			a.sup++
		} else {
			a.todo++
		}
	}
	var rows []qrow
	for fid, a := range agg {
		if a.sup == 0 || a.sup < a.todo {
			continue
		}
		rows = append(rows, qrow{
			order: []oterm{dsc(a.sup), dsc(a.todo)},
			cells: []string{g.path(fid), cellInt(a.sup), cellInt(a.todo), cellInt(a.all)},
			ord:   fid,
		})
	}
	qemit(&r, rows, limit)
	return r
}

var suppressionKinds = map[string]bool{
	"NOQA": true, "TYPE: IGNORE": true, "PRAGMA: NO COVER": true,
	"PYRIGHT: IGNORE": true,
}

func run_multi_write_no_atomic(g *Graph, mod string, limit int) result {
	r := result{cols: cols_multi_write_no_atomic}
	var rows []qrow
	for i := range g.Symbols {
		s := &g.Symbols[i]
		if s.NOrmWrite < 2 || s.NAtomic != 0 {
			continue
		}
		if !g.notestgen(s.FileID) || !g.modOK(s, mod) {
			continue
		}
		if !hasNoAttrLike(g, s, "%atomic%") {
			continue
		}
		rows = append(rows, qrow{
			order: []oterm{dsc(s.NOrmWrite), dsc(s.FanIn)},
			cells: []string{g.S(s.Name), cellInt(s.NOrmWrite), cellInt(s.NSql),
				cellInt(s.FanIn), at(g, *s)},
			ord: s.ID,
		})
	}
	qemit(&r, rows, limit)
	return r
}

func (g *Graph) taskDecorator(s *Symbol) (string, bool) {
	best := ""
	found := false
	for _, a := range g.attrRows(s.ID) {
		n := g.S(a.Name)
		if !dbLike(n, "%task%") {
			continue
		}
		if !found || n < best {
			best, found = n, true
		}
	}
	return best, found
}

func run_celery_task_sync_call(g *Graph, mod string, limit int) result {
	r := result{cols: cols_celery_task_sync_call}
	var rows []qrow
	for i := range g.Symbols {
		s := &g.Symbols[i]
		if s.FanIn <= 0 || !g.notestgen(s.FileID) || !g.modOK(s, mod) {
			continue
		}
		dec, ok := g.taskDecorator(s)
		if !ok {
			continue
		}
		rows = append(rows, qrow{
			order: []oterm{dsc(s.FanIn)},
			cells: []string{g.S(s.Name), dec, cellInt(s.FanIn), cellInt(s.NParams), at(g, *s)},
			ord:   s.ID,
		})
	}
	qemit(&r, rows, limit)
	return r
}

func run_celery_task_reliability(g *Graph, mod string, limit int) result {
	r := result{cols: cols_celery_task_reliability}
	var rows []qrow
	for i := range g.Symbols {
		s := &g.Symbols[i]
		if !g.notestgen(s.FileID) || !g.modOK(s, mod) {
			continue
		}
		dec, ok := g.taskDecorator(s)
		if !ok {
			continue
		}
		anyBare := false
		for _, a := range g.attrRows(s.ID) {
			if !dbLike(g.S(a.Name), "%task%") {
				continue
			}
			args := g.cellTextOr(a.Args, "")
			if !dbLike(args, "%acks_late%") && !dbLike(args, "%time_limit%") {
				anyBare = true
			}
		}
		if !anyBare {
			continue
		}
		rows = append(rows, qrow{
			order: []oterm{dsc(s.FanIn)},
			cells: []string{g.S(s.Name), dec, cellInt(s.FanIn), at(g, *s)},
			ord:   s.ID,
		})
	}
	qemit(&r, rows, limit)
	return r
}

func run_thread_target_shared_state(g *Graph, mod string, limit int) result {
	r := result{cols: cols_thread_target_shared_state}
	byName := g.funcsByName()
	type gkey struct {
		sid, line int32
		expr      string
	}
	agg := map[gkey]*struct{ defs, gw, conc int32 }{}
	for i := range g.APISites {
		d := &g.APISites[i]
		if g.S(d.Kind) != "thread-target" || !g.notest(d.FileID) {
			continue
		}
		s := g.sym(d.SymbolID)
		if mod != "%" && !dbLike(g.moduleName(s.ModuleID), mod) {
			continue
		}
		k := gkey{d.SymbolID, d.Line, g.S(d.Expr)}
		e := agg[k]
		if e == nil {
			e = &struct{ defs, gw, conc int32 }{}
			agg[k] = e
		}
		ids := byName[k.expr]
		e.defs = int32(len(ids))
		for _, id := range ids {
			t := g.sym(id)
			if t.NGlobalStmt > e.gw {
				e.gw = t.NGlobalStmt
			}
			if t.NConcurrency > e.conc {
				e.conc = t.NConcurrency
			}
		}
	}
	var rows []qrow
	for k, e := range agg {
		s := g.sym(k.sid)

		gwC, concC := cellInt(e.gw), cellInt(e.conc)
		if e.defs == 0 {
			gwC, concC = "-", "-"
		}
		rows = append(rows, qrow{
			order: []oterm{dsc(e.gw), dsc(e.conc)},
			cells: []string{g.S(s.Name), k.expr, cellInt(e.defs), gwC,
				concC, g.path(s.FileID) + ":" + itoa(k.line)},
			ord: k.sid,
		})
	}
	qemit(&r, rows, limit)
	return r
}

func (g *Graph) funcsByName() map[string][]int32 {
	if g.nameIdx != nil {
		return g.nameIdx
	}
	m := map[string][]int32{}
	for i := range g.Symbols {
		s := &g.Symbols[i]
		if !isFuncKind(g.S(s.Kind)) {
			continue
		}
		n := g.S(s.Name)
		m[n] = append(m[n], s.ID)
	}
	g.nameIdx = m
	return m
}

func (g *Graph) incomingEdges(sid int32) []int32 { return g.ix.edgeByCallee.get(sid) }

func run_apiSitesOfKind(g *Graph, mod string, limit int, kind string, cols []string) result {
	r := result{cols: cols}
	var rows []qrow
	for i := range g.APISites {
		d := &g.APISites[i]
		if g.S(d.Kind) != kind || !g.notestgen(d.FileID) {
			continue
		}
		f := g.Files[d.FileID-1]
		if mod != "%" && !dbLike(g.moduleName(f.ModuleID), mod) {
			continue
		}
		p := g.S(f.Path)
		rows = append(rows, qrow{
			order: []oterm{ascT(p), ascI(d.Line)},
			cells: []string{p, g.S(d.Expr), cellInt(d.Line), p + ":" + itoa(d.Line)},
			ord:   d.ID,
		})
	}
	qemit(&r, rows, limit)
	return r
}

func run_import_monkeypatch(g *Graph, mod string, limit int) result {
	return run_apiSitesOfKind(g, mod, limit, "monkeypatch", cols_import_monkeypatch)
}

func run_settings_mutation_import(g *Graph, mod string, limit int) result {
	return run_apiSitesOfKind(g, mod, limit, "settings-write", cols_settings_mutation_import)
}

func run_import_time_side_effects(g *Graph, mod string, limit int) result {
	r := result{cols: cols_import_time_side_effects}
	var rows []qrow
	for i := range g.Symbols {
		s := &g.Symbols[i]
		if g.S(s.Kind) != "module" {
			continue
		}
		work := s.NIO + s.NNet + s.NOpen + s.NExec + s.NShell + s.NSubprocess
		if work == 0 {
			continue
		}
		if !g.notestgen(s.FileID) || !g.modOK(s, mod) {
			continue
		}
		p := g.path(s.FileID)
		rows = append(rows, qrow{
			order: []oterm{dsc(work), dsc(s.NNet)},
			cells: []string{p, cellInt(s.NIO), cellInt(s.NNet), cellInt(s.NOpen),
				cellInt(s.NExec), cellInt(s.NShell), cellInt(s.NSubprocess),
				cellInt(work), p + ":1"},
			ord: s.ID,
		})
	}
	qemit(&r, rows, limit)
	return r
}

func run_taint_frontier_input(g *Graph, mod string, limit int) result {
	r := result{cols: cols_taint_frontier_input}
	var roots []int32
	seen := map[int32]bool{}
	for i := range g.InputSites {
		sid := g.InputSites[i].SymbolID
		if sid < 1 || int(sid) > len(g.Symbols) || seen[sid] {
			continue
		}
		seen[sid] = true
		roots = append(roots, sid)
	}

	type rp struct{ root, sym int32 }
	depth := make(map[rp]int32, len(roots)*8)
	var frontier []rp
	for _, root := range roots {
		depth[rp{root, root}] = 0
		frontier = append(frontier, rp{root, root})
	}
	for d := int32(1); d <= 4 && len(frontier) > 0; d++ {
		var next []rp
		for _, e := range frontier {
			for _, callee := range g.callees(e.sym) {
				if callee == e.sym {
					continue
				}
				k := rp{e.root, callee}
				if _, seen := depth[k]; seen {
					continue
				}
				depth[k] = d
				next = append(next, k)
			}
		}
		frontier = next
	}
	type agg struct {
		hops    int32
		readers map[int32]bool
	}
	m := map[int32]*agg{}
	for k, d := range depth {
		s := g.sym(k.sym)
		if s.NSubprocess+s.NShellTrue+s.NEvalExec+s.NPickleLoad+s.NMarkSafe == 0 {
			continue
		}
		if !g.notestgen(s.FileID) || !g.modOK(s, mod) {
			continue
		}
		a := m[k.sym]
		if a == nil {

			a = &agg{readers: map[int32]bool{}, hops: -1}
			m[k.sym] = a
		}
		a.readers[k.root] = true
		if a.hops < 0 || d < a.hops {
			a.hops = d
		}
	}
	var rows []qrow
	for sid, a := range m {
		s := g.sym(sid)
		rows = append(rows, qrow{
			order: []oterm{dsc(int32(len(a.readers))), dsc(-a.hops)},
			cells: []string{g.S(s.Name), cellInt(a.hops), cellInt(int32(len(a.readers))),
				cellInt(s.NSubprocess), cellInt(s.NShellTrue), cellInt(s.NEvalExec),
				cellInt(s.NPickleLoad), cellInt(s.NMarkSafe), at(g, *s)},
			ord: sid,
		})
	}
	qemit(&r, rows, limit)
	return r
}

func run_ssti_surface(g *Graph, mod string, limit int) result {
	r := result{cols: cols_ssti_surface}
	var rows []qrow
	for i := range g.APISites {
		d := &g.APISites[i]
		if g.S(d.Kind) != "ssti" || !g.notestgen(d.FileID) {
			continue
		}
		f := g.Files[d.FileID-1]
		if mod != "%" && !dbLike(g.moduleName(f.ModuleID), mod) {
			continue
		}
		s := g.sym(d.SymbolID)
		n := int32(len(g.inputFor(d.SymbolID)))
		rows = append(rows, qrow{
			order: []oterm{dsc(d.IsLiteralArg), dsc(n)},
			cells: []string{g.S(s.Name), g.S(d.Expr), cellInt(d.Line),
				cellInt(d.IsLiteralArg), cellInt(n),
				g.path(d.FileID) + ":" + itoa(d.Line)},
			ord: d.ID,
		})
	}
	qemit(&r, rows, limit)
	return r
}

func run_session_created_per_call(g *Graph, mod string, limit int) result {
	r := result{cols: cols_session_created_per_call}
	type gk struct {
		n, minLine int32
		has        bool
	}
	agg := map[int32]*gk{}
	for i := range g.APISites {
		d := &g.APISites[i]
		if g.S(d.Kind) != "session" || !g.notestgen(d.FileID) {
			continue
		}
		s := g.sym(d.SymbolID)
		if mod != "%" && !dbLike(g.moduleName(s.ModuleID), mod) {
			continue
		}
		a := agg[d.SymbolID]
		if a == nil {
			a = &gk{}
			agg[d.SymbolID] = a
		}
		a.n++
		if !a.has || d.Line < a.minLine {
			a.minLine, a.has = d.Line, true
		}
	}
	var rows []qrow
	for sid, a := range agg {
		s := g.sym(sid)
		rows = append(rows, qrow{
			order: []oterm{dsc(s.FanIn), dsc(a.n)},
			cells: []string{g.S(s.Name), cellInt(a.n), cellInt(s.FanIn),
				g.path(s.FileID) + ":" + itoa(a.minLine)},
			ord: sid,
		})
	}
	qemit(&r, rows, limit)
	return r
}

func run_test_only_callers(g *Graph, mod string, limit int) result {
	r := result{cols: cols_test_only_callers}
	fromTest := map[int32]bool{}
	fromProd := map[int32]bool{}
	for _, e := range g.Edges {
		caller := g.sym(e.CallerID)
		if g.Files[caller.FileID-1].IsTest == 1 || caller.IsTest == 1 {
			fromTest[e.CalleeID] = true
		} else {
			fromProd[e.CalleeID] = true
		}
	}
	var rows []qrow
	for i := range g.Symbols {
		s := &g.Symbols[i]
		if !isFuncKind(g.S(s.Kind)) || !g.notestgen(s.FileID) || !g.modOK(s, mod) {
			continue
		}
		if s.IsTest != 0 || s.FanIn <= 0 {
			continue
		}
		if !fromTest[s.ID] || fromProd[s.ID] {
			continue
		}
		rows = append(rows, qrow{
			order: []oterm{dsc(s.FanIn), dsc(s.Cyclomatic)},
			cells: []string{g.S(s.Name), cellInt(s.FanIn), cellInt(s.Cyclomatic),
				cellInt(s.SLOC), cellInt(s.IsPublic), at(g, *s)},
			ord: s.ID,
		})
	}
	qemit(&r, rows, limit)
	return r
}

func run_mutable_class_attribute(g *Graph, mod string, limit int) result {
	r := result{cols: cols_mutable_class_attribute}
	var rows []qrow
	for i := range g.Fields {
		fl := &g.Fields[i]
		if fl.SymbolID < 1 || int(fl.SymbolID) > len(g.Symbols) ||
			fl.IsStatic != 1 || fl.IsMutable != 1 {
			continue
		}
		if dbLike(g.S(fl.Type), "%ClassVar%") {
			continue
		}
		s := g.sym(fl.SymbolID)
		if g.S(s.Kind) != "class" || !g.notestgen(s.FileID) || !g.modOK(s, mod) {
			continue
		}
		n := int32(len(g.callsitesOf(s.ID)))
		if n == 0 {
			continue
		}
		rows = append(rows, qrow{
			order: []oterm{dsc(n)},
			cells: []string{g.S(s.Name), g.S(fl.Name), g.cellText(fl.Type), cellInt(n),
				g.path(s.FileID) + ":" + itoa(fl.Line)},
			ord: fl.SymbolID,
		})
	}
	qemit(&r, rows, limit)
	return r
}

func run_global_write_reachable(g *Graph, mod string, limit int) result {
	r := result{cols: cols_global_write_reachable}
	type rp struct{ root, sym int32 }
	depth := map[rp]int32{}
	var frontier []rp
	for i := range g.Symbols {
		s := &g.Symbols[i]
		if s.NGlobalStmt > 0 && isFuncKind(g.S(s.Kind)) {
			depth[rp{s.ID, s.ID}] = 0
			frontier = append(frontier, rp{s.ID, s.ID})
		}
	}
	for d := int32(1); d <= 4 && len(frontier) > 0; d++ {
		var next []rp
		for _, e := range frontier {
			for _, caller := range g.callers(e.sym) {
				if caller == e.sym {
					continue
				}
				k := rp{e.root, caller}
				if _, seen := depth[k]; seen {
					continue
				}
				depth[k] = d
				next = append(next, k)
			}
		}
		frontier = next
	}
	type agg struct {
		hops   int32
		public map[int32]bool
	}
	m := map[int32]*agg{}
	for k, d := range depth {
		w := g.sym(k.root)
		if !g.notestgen(w.FileID) || !g.modOK(w, mod) {
			continue
		}
		a := m[k.root]
		if a == nil {

			a = &agg{public: map[int32]bool{}, hops: -1}
			m[k.root] = a
		}
		if g.sym(k.sym).IsPublic == 1 {
			a.public[k.sym] = true
		}
		if a.hops < 0 || d < a.hops {
			a.hops = d
		}
	}
	var rows []qrow
	for root, a := range m {
		if len(a.public) == 0 {
			continue
		}
		w := g.sym(root)
		rows = append(rows, qrow{
			order: []oterm{dsc(int32(len(a.public))), dsc(w.NGlobalStmt)},
			cells: []string{g.S(w.Name), cellInt(w.NGlobalStmt), cellInt(a.hops),
				cellInt(int32(len(a.public))), at(g, *w)},
			ord: root,
		})
	}
	qemit(&r, rows, limit)
	return r
}

func run_prod_imports_test(g *Graph, mod string, limit int) result {
	r := result{cols: cols_prod_imports_test}
	var rows []qrow
	for i := range g.Imports {
		im := &g.Imports[i]
		if im.TargetID < 1 || int(im.TargetID) > len(g.Files) {
			continue
		}
		tf := g.Files[im.TargetID-1]
		if tf.IsTest != 1 || !g.notestgen(im.FileID) {
			continue
		}
		f := g.Files[im.FileID-1]
		if mod != "%" && !dbLike(g.moduleName(f.ModuleID), mod) {
			continue
		}
		rows = append(rows, qrow{
			order: []oterm{dsc(tf.NSymbols), ascT(g.S(f.Path))},
			cells: []string{g.S(f.Path), g.S(tf.Path), cellInt(im.Line),
				cellInt(tf.NSymbols), g.S(f.Path) + ":" + itoa(im.Line)},
			ord: im.ID,
		})
	}
	qemit(&r, rows, limit)
	return r
}

type csr struct {
	off []int32
	idx []int32
}

func buildCSR(nrec, nkeys int, key func(i int) int32) csr {
	counts := make([]int32, nkeys+2)
	for i := range nrec {
		k := key(i)
		if k < 0 || int(k) > nkeys {
			continue
		}
		counts[k+1]++
	}
	for i := 1; i < len(counts); i++ {
		counts[i] += counts[i-1]
	}
	idx := make([]int32, nrec)
	fill := make([]int32, nkeys+1)
	copy(fill, counts[:nkeys+1])
	for i := range nrec {
		k := key(i)
		if k < 0 || int(k) > nkeys {
			continue
		}
		idx[fill[k]] = int32(i)
		fill[k]++
	}
	return csr{off: counts, idx: idx}
}

func (c csr) get(k int32) []int32 {
	if k < 0 || int(k)+1 >= len(c.off) {
		return nil
	}
	return c.idx[c.off[k]:c.off[k+1]]
}

type idx struct {
	bySymbolAttr   csr
	bySymbolHaz    csr
	bySymbolHandle csr
	bySymbolParam  csr
	bySymbolInput  csr
	bySymbolAPI    csr
	bySymbolLit    csr
	bySymbolComp   csr
	bySymbolField  csr
	bySymbolLocal  csr
	bySymbolSecret csr
	bySymbolDyn    csr
	bySymbolClass  csr
	bySymbolEnum   csr
	byParent       csr
	byFileImport   csr
	byFileExport   csr
	byFileMarker   csr
	byCalleeSite   csr
	byCallerSite   csr
	edgeByCallee   csr
	byFileVar      csr
}

func (g *Graph) buildIndex() {
	n := len(g.Symbols)
	ix := &idx{}
	ix.bySymbolAttr = buildCSR(len(g.Attributes), n, func(i int) int32 { return g.Attributes[i].SymbolID })
	ix.bySymbolHaz = buildCSR(len(g.Hazards), n, func(i int) int32 { return g.Hazards[i].SymbolID })
	ix.bySymbolHandle = buildCSR(len(g.Handlers), n, func(i int) int32 { return g.Handlers[i].SymbolID })
	ix.bySymbolParam = buildCSR(len(g.Params), n, func(i int) int32 { return g.Params[i].SymbolID })
	ix.bySymbolInput = buildCSR(len(g.InputSites), n, func(i int) int32 { return g.InputSites[i].SymbolID })
	ix.bySymbolAPI = buildCSR(len(g.APISites), n, func(i int) int32 { return g.APISites[i].SymbolID })
	ix.bySymbolLit = buildCSR(len(g.Literals), n, func(i int) int32 { return g.Literals[i].SymbolID })
	ix.bySymbolComp = buildCSR(len(g.Comprehens), n, func(i int) int32 { return g.Comprehens[i].SymbolID })
	ix.bySymbolField = buildCSR(len(g.Fields), n, func(i int) int32 { return g.Fields[i].SymbolID })
	ix.bySymbolLocal = buildCSR(len(g.Locals), n, func(i int) int32 { return g.Locals[i].SymbolID })
	ix.bySymbolSecret = buildCSR(len(g.Secrets), n, func(i int) int32 { return g.Secrets[i].SymbolID })
	ix.bySymbolDyn = buildCSR(len(g.DynamicSites), n, func(i int) int32 { return g.DynamicSites[i].SymbolID })
	ix.bySymbolClass = buildCSR(len(g.Classes), n, func(i int) int32 { return g.Classes[i].SymbolID })
	ix.bySymbolEnum = buildCSR(len(g.EnumMembers), n, func(i int) int32 { return g.EnumMembers[i].SymbolID })
	ix.byParent = buildCSR(n, n, func(i int) int32 { return g.Symbols[i].ParentID })
	nf := len(g.Files)
	ix.byFileImport = buildCSR(len(g.Imports), nf, func(i int) int32 { return g.Imports[i].FileID })
	ix.byFileExport = buildCSR(len(g.AllExports), nf, func(i int) int32 { return g.AllExports[i].FileID })
	ix.byFileMarker = buildCSR(len(g.Markers), nf, func(i int) int32 { return g.Markers[i].FileID })
	ix.byFileVar = buildCSR(len(g.ModuleVars), nf, func(i int) int32 { return g.ModuleVars[i].FileID })
	ix.byCalleeSite = buildCSR(len(g.Callsites), n, func(i int) int32 { return g.Callsites[i].CalleeID })
	ix.byCallerSite = buildCSR(len(g.Callsites), n, func(i int) int32 { return g.Callsites[i].CallerID })
	ix.edgeByCallee = buildCSR(len(g.Edges), n, func(i int) int32 { return g.Edges[i].CalleeID })
	g.ix = ix
}

func (g *Graph) attrRows(sid int32) []Attribute {
	ix := g.ix.bySymbolAttr.get(sid)
	if len(ix) == 0 {
		return nil
	}
	out := make([]Attribute, len(ix))
	for i, k := range ix {
		out[i] = g.Attributes[k]
	}
	return out
}

func (g *Graph) paramFor(sid int32) []Param {
	ix := g.ix.bySymbolParam.get(sid)
	if len(ix) == 0 {
		return nil
	}
	out := make([]Param, len(ix))
	for i, k := range ix {
		out[i] = g.Params[k]
	}
	return out
}

func (g *Graph) inputFor(sid int32) []UserInputSite {
	ix := g.ix.bySymbolInput.get(sid)
	if len(ix) == 0 {
		return nil
	}
	out := make([]UserInputSite, len(ix))
	for i, k := range ix {
		out[i] = g.InputSites[k]
	}
	return out
}

func (g *Graph) localFor(sid int32) []LocalVar {
	ix := g.ix.bySymbolLocal.get(sid)
	if len(ix) == 0 {
		return nil
	}
	out := make([]LocalVar, len(ix))
	for i, k := range ix {
		out[i] = g.Locals[k]
	}
	return out
}

func (g *Graph) importFor(fid int32) []Import {
	ix := g.ix.byFileImport.get(fid)
	if len(ix) == 0 {
		return nil
	}
	out := make([]Import, len(ix))
	for i, k := range ix {
		out[i] = g.Imports[k]
	}
	return out
}

func (g *Graph) exportFor(fid int32) []AllExport {
	ix := g.ix.byFileExport.get(fid)
	if len(ix) == 0 {
		return nil
	}
	out := make([]AllExport, len(ix))
	for i, k := range ix {
		out[i] = g.AllExports[k]
	}
	return out
}

func (g *Graph) callsitesOf(sid int32) []Callsite {
	ix := g.ix.byCalleeSite.get(sid)
	if len(ix) == 0 {
		return nil
	}
	out := make([]Callsite, len(ix))
	for i, k := range ix {
		out[i] = g.Callsites[k]
	}
	return out
}

func dbLike(s, pattern string) bool { return like(s, pattern) }

func instr(hay, needle string) int {
	if needle == "" {
		return 1
	}
	i := indexOf(hay, needle)
	if i < 0 {
		return 0
	}
	return i + 1
}

func indexOf(hay, needle string) int {
	n := len(needle)
	if n == 0 {
		return 0
	}
	if n > len(hay) {
		return -1
	}
	for i := 0; i+n <= len(hay); i++ {
		if hay[i:i+n] == needle {
			return i
		}
	}
	return -1
}

func ltrimDots(s string) string {
	i := 0
	for i < len(s) && s[i] == '.' {
		i++
	}
	return s[i:]
}

type groupConcat struct {
	seen  map[string]bool
	parts []string
}

func newGC() *groupConcat { return &groupConcat{seen: map[string]bool{}} }

func (c *groupConcat) add(s string) {
	if c == nil || c.seen[s] {
		return
	}
	c.seen[s] = true
	c.parts = append(c.parts, s)
}

func (c *groupConcat) String() string {
	if c == nil {
		return ""
	}
	return joinStrings(c.parts, ",")
}

var cols_async_blocking = []string{"name", "blocking", "io", "net", "awaits", "awaits_in_loop", "fan_in", "at"}
var cols_async_blocking_reachable = []string{"async_fn", "blocking_callees", "max_hops", "via", "at"}
var cols_await_in_loop = []string{"name", "awaits_in_loop", "depth", "total_awaits", "net", "fan_in", "at"}
var cols_mutable_defaults = []string{"name", "mutable_defaults", "fan_in", "n_params", "public", "defaults", "at"}
var cols_untrusted_frontier = []string{"sink", "exec_", "unpickle", "shell", "shell_true", "hops_from_public", "reachable_from", "at"}
var cols_sql_built_by_hand = []string{"name", "fstring", "concat", "fmt", "sql_calls", "fan_in", "public", "at"}
var cols_n_plus_one = []string{"name", "queries_in_loop", "depth", "sql_calls", "io", "fan_in", "at"}
var cols_loop_multiplied = []string{"name", "depth", "calls", "regex", "len_calls", "appends", "concat", "range_len", "fan_in", "at"}
var cols_quadratic_strings = []string{"name", "concats", "depth", "literals", "fan_in", "sloc", "at"}
var cols_swallowed_errors = []string{"name", "handlers", "bare", "broad", "empty", "reraise", "logged", "risky_ops", "at"}
var cols_reflection_opacity = []string{"kind", "n", "literal_arg", "in_fns", "in_files", "examples"}
var cols_decorator_roots = []string{"name", "decorator", "fan_in", "sloc", "cyclo", "async_", "at"}
var cols_dead_code = []string{"name", "kind", "sloc", "cyclo", "ext_calls", "at"}
var cols_untested = []string{"name", "fan_in", "cyclo", "sloc", "risk", "public", "at"}
var cols_unbounded_caches = []string{"symbol", "kind", "detail", "key_arity", "fan_in", "at"}
var cols_shared_mutable_state = []string{"name", "path", "line", "type", "built_by_call", "fns_using_global", "global_stmts"}
var cols_import_cycles = []string{"module_a", "module_b", "a_imports_b", "b_imports_a"}
var cols_import_workarounds = []string{"inside_function", "imports_", "kind", "fan_in", "line", "at"}
var cols_resource_discipline = []string{"name", "opens", "resources", "with_blocks", "ctx_mgrs", "trys", "finallys", "at"}
var cols_weak_crypto = []string{"name", "pattern", "n", "first_line", "public", "fan_in", "at"}
var cols_concurrency_surface = []string{"name", "concurrency", "globals_", "locks_in_loop", "async_", "blocking", "fan_in", "at"}
var cols_unsafe_decode_reachable = []string{"name", "reached_from", "hops", "pickles", "yaml_loads", "evals", "subprocs", "fan_in", "module_", "at"}
var cols_bare_except = []string{"name", "bare_excepts", "swallowed", "reraises", "total_catches", "fan_in", "cyclo", "at"}
var cols_pickle_deserialization = []string{"name", "pickle_loads", "eval_execs", "yaml_loads", "fan_in", "at"}
var cols_yaml_unsafe_load = []string{"name", "yaml_loads", "pickle_loads", "fan_in", "cyclo", "at"}
var cols_subprocess_shell_injection = []string{"name", "subprocess_calls", "shell_true", "os_system", "eval_execs", "fan_in", "at"}
var cols_eval_exec_injection = []string{"name", "eval_execs", "dynamic_attrs", "pickle_loads", "fan_in", "at"}
var cols_assert_in_production = []string{"name", "asserts", "asserts_in_loop", "fan_in", "cyclo", "at"}
var cols_global_statement = []string{"name", "global_stmts", "nonlocal_stmts", "assignments", "fan_in", "cyclo", "at"}
var cols_open_without_with = []string{"name", "opens", "withs", "tries", "finallys", "fan_in", "cyclo", "at"}
var cols_datetime_naive = []string{"name", "naive_datetimes", "open_no_encoding", "fan_in", "cyclo", "at"}
var cols_append_in_loop_perf = []string{"name", "appends_in_loop", "range_lens", "loops", "cyclo", "fan_in", "at"}
var cols_decorator_depth = []string{"name", "kind", "decorators", "attr_rows", "sloc", "fan_in", "at"}
var cols_non_public_leak = []string{"callee_", "callee_kind", "sloc", "defined_in", "called_from", "n_calls"}
var cols_wildcard_import_rank = []string{"path", "wildcard_imports", "local_all_exports", "sloc"}
var cols_all_reexports = []string{"package_file", "exported_name", "line", "defined_here", "defined_anywhere"}
var cols_relative_import_depth = []string{"path", "max_depth", "relative_imports", "deep_imports"}
var cols_method_kind_mix = []string{"class_", "classmethods", "staticmethods", "instance_methods", "total_methods", "pct_staticish", "at_any"}
var cols_request_without_timeout = []string{"path", "name", "n_request_no_timeout", "fan_in"}
var cols_open_redirect_surface = []string{"name", "redirect_calls", "input_sites", "kinds", "fan_in", "at"}
var cols_ssrf_fetch_surface = []string{"name", "fetch_calls", "input_sites", "kinds", "at"}
var cols_hardcoded_secret_candidates = []string{"name", "candidate", "line", "fan_in", "at"}
var cols_xxe_parser_surface = []string{"name", "xml_parsers", "sloc", "at"}
var cols_path_traversal_surface = []string{"name", "open_sites", "input_sites", "kinds", "at"}
var cols_unchecked_upload_surface = []string{"name", "save_calls", "form_reads", "at"}
var cols_zip_slip_surface = []string{"name", "zip_access", "fan_in", "at"}
var cols_log_injection_surface = []string{"name", "log_calls", "input_sites", "kinds", "fan_in", "at"}
var cols_unauthenticated_input_surface = []string{"name", "input_sites", "kinds", "at"}
var cols_exception_in_loop = []string{"path", "name", "handlers_in_loops", "any_broad", "fan_in"}
var cols_call_in_default_argument = []string{"path", "name", "param", "default_value", "fan_in"}
var cols_name_shadowing = []string{"path", "fn", "shadowed", "where_", "fan_in"}
var cols_undocumented_export = []string{"name", "kind", "fan_in", "sloc", "at"}
var cols_closure_in_loop = []string{"name", "closures", "depth", "lambdas", "fan_in", "at"}
var cols_raise_without_from = []string{"path", "name", "line", "types", "fan_in"}
var cols_suppression_burden = []string{"path", "suppressions", "todos", "markers"}
var cols_broad_test_expectation = []string{"path", "name", "broad_raises", "n_calls", "fan_in"}
var cols_template_injection = []string{"path", "name", "unescaped_envs", "fan_in", "sloc"}
var cols_orm_query_in_loop = []string{"name", "orm_queries_in_loop", "depth", "orm_writes", "raw_sql", "fan_in", "at"}
var cols_commit_in_loop = []string{"name", "commits_in_loop", "depth", "sql_calls", "fan_in", "at"}
var cols_multi_write_no_atomic = []string{"name", "orm_writes", "raw_sql", "fan_in", "at"}
var cols_celery_task_sync_call = []string{"name", "task_decorator", "fan_in", "n_params", "at"}
var cols_celery_task_reliability = []string{"name", "task_decorator", "fan_in", "at"}
var cols_lock_across_await = []string{"name", "awaits_in_sync_with", "lock_sites", "awaits", "fan_in", "at"}
var cols_thread_target_shared_state = []string{"spawner", "target_fn", "defs", "target_global_writes", "target_concurrency", "at"}
var cols_import_monkeypatch = []string{"path", "expr", "line", "at"}
var cols_settings_mutation_import = []string{"path", "expr", "line", "at"}
var cols_import_time_side_effects = []string{"path", "io", "net", "opens", "execs", "shell", "subprocesses", "import_time_work", "at"}
var cols_membership_scan_in_loop = []string{"name", "membership_scans", "depth", "loops", "fan_in", "at"}
var cols_resource_return_escape = []string{"name", "escaped_handles", "ctx_managers", "fan_in", "at"}
var cols_taint_frontier_input = []string{"sink_fn", "hops", "input_readers", "subprocesses", "shell_true", "evals", "pickles", "mark_safe", "at"}
var cols_mark_safe_surface = []string{"name", "mark_safe_calls", "input_sites", "kinds", "fan_in", "at"}
var cols_mass_assignment_surface = []string{"name", "splat_sites", "input_sites", "kinds", "fan_in", "at"}
var cols_ssti_surface = []string{"name", "expr", "line", "is_literal_arg", "input_sites", "at"}
var cols_session_created_per_call = []string{"name", "session_builds", "fan_in", "at"}
var cols_tls_verify_disabled = []string{"name", "verify_disabled", "fan_in", "at"}
var cols_test_only_callers = []string{"name", "fan_in", "cyclo", "sloc", "public", "at"}
var cols_mutable_class_attribute = []string{"class_", "attribute", "type", "instantiations", "at"}
var cols_global_write_reachable = []string{"writer", "global_writes", "hops_from_public", "public_reach", "at"}
var cols_prod_imports_test = []string{"importer", "test_module", "line", "test_symbols", "at"}
var cols_dict_get_in_loop = []string{"name", "gets_in_loop", "depth", "loops", "fan_in", "at"}
var cols_format_in_loop = []string{"name", "formats_in_loop", "depth", "concats", "fan_in", "at"}
var cols_loop_else = []string{"name", "loop_elses", "loops", "cyclo", "fan_in", "at"}
var cols_print_statement_shipping = []string{"name", "prints", "fan_in", "at"}
var cols_insecure_tempfile = []string{"name", "insecure_temp_sites", "fan_in", "at"}
var cols_unused_public_api = []string{"name", "kind", "sloc", "cyclo", "n_doc_lines", "at"}
var cols_graph_blindspots = []string{"module", "fns", "calls", "unresolved", "computed", "reflect_sites", "pct_blind"}
var cols_risk_ranked = []string{"name", "risk", "cyclo", "cog", "nest", "danger", "sqlbuild", "shell", "fan_in", "at"}
var cols_hot_multipliers = []string{"name", "fan_in", "sites", "fan_out", "cyclo", "sloc", "doc", "module", "at"}
var cols_typing_holes = []string{"name", "n_params", "untyped", "ret_typed", "fan_in", "public", "pct", "at"}
var cols_god_functions = []string{"name", "sloc", "cyclo", "cog", "nest", "elifs", "returns", "locals_", "n_params", "maint", "at"}
var cols_deep_nesting = []string{"name", "nest", "loops", "cog", "sloc", "early_ret", "at"}
var cols_nested_loops = []string{"name", "depth", "loops", "calls", "subscripts", "sloc", "fan_in", "at"}
var cols_class_shape = []string{"name", "methods", "class_vars", "bases", "bases", "abstract", "slots", "dataclass_", "lines", "at"}
var cols_slots_candidates = []string{"class_", "attrs", "methods", "dataclass_", "built_in_loop", "fan_in", "at"}
var cols_module_coupling = []string{"name", "kind", "files", "sloc", "syms", "public", "fan_in", "fan_out", "instability"}
var cols_undocumented_complexity = []string{"name", "cyclo", "cog", "sloc", "n_params", "fan_in", "public", "at"}
var cols_magic_numbers = []string{"value", "uses", "files", "fns", "seen_in"}
var cols_markers = []string{"kind", "path", "line", "text", "in_fn", "fan_in"}
var cols_parse_coverage = []string{"path", "lines", "errors", "parsed", "generated", "vendored", "test", "bytes"}
var cols_latent_risk_density = []string{"name", "module_", "facts", "open_noenc", "naive_dt", "dyn_attr", "weak_hash", "no_timeout", "bare_except", "fan_in", "cyclo", "at"}
var cols_too_many_locals = []string{"name", "n_locals", "n_params", "sloc", "cyclo", "nesting", "fan_in", "at"}
var cols_too_many_branches = []string{"name", "branches", "switches", "cases", "cyclo", "sloc", "fan_in", "at"}
var cols_too_many_return = []string{"name", "returns", "early_returns", "finally_blocks", "cyclo", "fan_in", "at"}
var cols_scattered_concerns = []string{"name", "n_caller_modules", "fan_in", "cyclo", "sloc", "modules", "at"}
var cols_line_too_long = []string{"path", "max_line_len", "sloc", "lines", "n_symbols", "at"}
var cols_untyped_params = []string{"name", "untyped_params", "annotated_params", "n_params", "has_return_type", "fan_in", "is_public", "at"}
var cols_deep_nesting_excessive = []string{"name", "nesting", "cyclo", "cognitive", "loops", "sloc", "fan_in", "at"}
var cols_god_class = []string{"name", "n_methods", "total_cyclo", "fan_in", "sloc", "at"}
var cols_import_surface = []string{"module", "module_symbols", "io", "net", "opens", "execs", "shell", "subprocesses", "import_time_work", "at"}
var cols_exception_posture = []string{"module", "handler_rows", "broad", "bare", "empty", "in_loop", "body_lines", "pct_broad", "at"}
var cols_resource_posture = []string{"module", "functions", "opens", "resources", "ctx_managers", "with_blocks", "pct_open_unmanaged", "at"}
var cols_concurrency_posture = []string{"module", "functions", "spawn_lock_sites", "global_writes", "async_fns", "locks_in_loop", "mutable_module_vars", "shared_state_sites", "at"}
var cols_sql_construction = []string{"module", "functions", "sql_calls", "fstring", "concat", "fmt", "hand_built", "queries_in_loop", "pct_hand_built", "at"}
var cols_third_party_coupling = []string{"module", "import_rows", "external_rows", "external_roots", "relative_rows", "wildcard_rows", "at"}
var cols_recursive_hotspots = []string{"name", "cyclo", "fan_in", "sloc", "max_loop_depth", "n_params", "at"}
var cols_registration_surface = []string{"module", "registered_entry_points", "functions", "decorators", "at"}
var cols_input_surface = []string{"module", "input_reads", "functions", "fns_with_auth_checks", "pct_auth", "at"}
var cols_network_hygiene = []string{"module", "functions", "net_calls", "no_timeout_sites", "fetch_sites", "pct_no_timeout", "at"}

type modAcc struct {
	mid int32

	syms map[int32]bool

	sums map[int32]*int32

	at minStr

	mutableVars int32
}

var modVarCounts map[int32]int32

func setModVarCounts(m map[int32]int32) { modVarCounts = m }

func (g *Graph) newModAcc(mid int32) *modAcc {
	return &modAcc{mid: mid, syms: map[int32]bool{}, sums: map[int32]*int32{},
		mutableVars: modVarCounts[mid]}
}

func (a *modAcc) add(sid, field int32, v int32) {
	a.syms[sid] = true
	if p := a.sums[field]; p != nil {
		*p += v
	} else {
		n := v
		a.sums[field] = &n
	}
}

func (g *Graph) runModMetric(cols []string, mod string, limit int,
	keep pred,
	accum func(g *Graph, a *modAcc, s *Symbol, f *File),
	order func(a *modAcc) []oterm,
	cells func(g *Graph, a *modAcc) []string,
	emit func(g *Graph, a *modAcc) bool, tieDesc ...bool) result {

	r := result{cols: cols}
	groups := map[int32]*modAcc{}
	for i := range g.Symbols {
		s := &g.Symbols[i]
		if !keep(g, s) {
			continue
		}
		if s.ModuleID < 1 || int(s.ModuleID) > len(g.Modules) {
			continue
		}
		if !dbLike(g.moduleName(s.ModuleID), mod) {
			continue
		}
		a := groups[s.ModuleID]
		if a == nil {
			a = g.newModAcc(s.ModuleID)
			groups[s.ModuleID] = a
		}
		accum(g, a, s, &g.Files[s.FileID-1])
	}
	var rows []qrow
	for _, a := range groups {
		if !emit(g, a) {
			continue
		}

		ord := a.mid
		if len(tieDesc) > 0 && tieDesc[0] {
			ord = -a.mid
		}
		rows = append(rows, qrow{order: order(a), cells: cells(g, a), ord: ord})
	}
	qemit(&r, rows, limit)
	return r
}

const (
	fNIO = iota
	fNNet
	fNOpen
	fNExec
	fNShell
	fNSub
	fNConc
	fNGlobal
	fIsAsync
	fLockInLoop
	fNSql
	fNSqlFstring
	fNSqlConcat
	fNSqlFormat
	fQueryInLoop
	fNReqTO
	fNFetch
	fNCtx
	fNWith
	fNCyclo
	fNSLOC
	fNCalls
	fNNet2
)

func run_graph_blindspots(g *Graph, mod string, limit int) result {

	reflect := map[int32]int32{}
	for i := range g.DynamicSites {
		sid := g.DynamicSites[i].SymbolID
		if sid >= 1 && int(sid) <= len(g.Symbols) {
			reflect[g.Symbols[sid-1].ModuleID]++
		}
	}
	return g.runModMetric(cols_graph_blindspots, mod, limit,
		pIsKind("function", "method"),
		func(g *Graph, a *modAcc, s *Symbol, f *File) {
			a.add(s.ID, fNCalls, s.NCalls)
			a.add(s.ID, -1, s.NUnresolvedCalls)
			a.add(s.ID, -2, s.NDynamicCalls)
		},
		func(a *modAcc) []oterm { return []oterm{dsc(sumOf(a, -1))} },
		func(g *Graph, a *modAcc) []string {
			calls := sumOf(a, fNCalls)
			unres := sumOf(a, -1)
			pct, _ := castInt(100.0*float64(unres)/float64(calls), calls != 0)
			return []string{g.moduleName(a.mid), cellInt(int32(len(a.syms))),
				cellInt(calls), cellInt(unres), cellInt(sumOf(a, -2)),
				cellInt(reflect[a.mid]), cellInt(pct)}
		},
		func(g *Graph, a *modAcc) bool { return sumOf(a, fNCalls) > 0 },
	)
}

func sumOf(a *modAcc, field int32) int32 {
	if p := a.sums[field]; p != nil {
		return *p
	}
	return 0
}

func run_class_shape(g *Graph, mod string, limit int) result {
	r := result{cols: cols_class_shape}
	var rows []qrow
	for i := range g.Classes {
		c := &g.Classes[i]
		if c.SymbolID < 1 || int(c.SymbolID) > len(g.Symbols) {
			continue
		}
		s := g.sym(c.SymbolID)
		if !g.nogen(s.FileID) || !g.modOK(s, mod) {
			continue
		}
		rows = append(rows, qrow{
			order: []oterm{dsc(c.NMethods + c.NClassVars)},
			cells: []string{g.S(s.Name), cellInt(c.NMethods), cellInt(c.NClassVars),
				cellInt(c.NBases), g.S(c.Bases), cellInt(c.NAbstractM),
				cellInt(c.HasSlots), cellInt(c.IsDataclass), cellInt(s.NLines),
				at(g, *s)},
			ord: c.SymbolID,
		})
	}
	qemit(&r, rows, limit)
	return r
}

func run_slots_candidates(g *Graph, mod string, limit int) result {
	r := result{cols: cols_slots_candidates}
	var rows []qrow
	for i := range g.Classes {
		c := &g.Classes[i]
		if c.SymbolID < 1 || int(c.SymbolID) > len(g.Symbols) {
			continue
		}
		if c.HasSlots != 0 || c.IsEnum != 0 || c.IsException != 0 {
			continue
		}
		s := g.sym(c.SymbolID)
		if !g.nogen(s.FileID) || !g.modOK(s, mod) {
			continue
		}
		inLoop := int32(0)
		for _, cs := range g.callsitesOf(c.SymbolID) {
			if g.sym(cs.CallerID).MaxLoopDepth > 0 {
				inLoop++
			}
		}
		rows = append(rows, qrow{
			order: []oterm{dsc(inLoop), dsc(s.FanIn)},
			cells: []string{g.S(s.Name), cellInt(c.NClassVars), cellInt(c.NMethods),
				cellInt(c.IsDataclass), cellInt(inLoop), cellInt(s.FanIn), at(g, *s)},
			ord: c.SymbolID,
		})
	}
	qemit(&r, rows, limit)
	return r
}

func run_module_coupling(g *Graph, mod string, limit int) result {
	r := result{cols: cols_module_coupling}
	var rows []qrow
	for i := range g.Modules {
		m := &g.Modules[i]
		if m.NFiles <= 0 {
			continue
		}
		if !dbLike(g.S(m.Name), mod) {
			continue
		}
		rows = append(rows, qrow{
			order: []oterm{dsc(m.FanIn + m.FanOut)},
			cells: []string{g.S(m.Name), g.S(m.Kind), cellInt(m.NFiles), cellInt(m.SLOC),
				cellInt(m.NSymbols), cellInt(m.NPublic), cellInt(m.FanIn), cellInt(m.FanOut),
				cellFloat(round2(m.Instability))},
			ord: m.ID,
		})
	}
	qemit(&r, rows, limit)
	return r
}

func round2(v float64) float64 {
	scaled := v * 100
	if scaled >= 0 {
		return float64(int64(scaled+0.5)) / 100
	}
	return float64(int64(scaled-0.5)) / 100
}

func run_magic_numbers(g *Graph, mod string, limit int) result {
	r := result{cols: cols_magic_numbers}
	type gk struct {
		uses   int32
		files  map[int32]bool
		fns    map[int32]bool
		seenIn *groupConcat
		valID  uint32
	}
	agg := map[uint32]*gk{}
	for i := range g.Literals {
		l := &g.Literals[i]
		if l.IsMagic != 1 || !g.notestgen(l.FileID) {
			continue
		}
		f := g.Files[l.FileID-1]
		if mod != "%" && !dbLike(g.moduleName(f.ModuleID), mod) {
			continue
		}
		a := agg[l.Value]
		if a == nil {
			a = &gk{files: map[int32]bool{}, fns: map[int32]bool{}, seenIn: newGC(), valID: l.Value}
			agg[l.Value] = a
		}
		a.uses++
		a.files[l.FileID] = true
		a.fns[l.SymbolID] = true
		a.seenIn.add(g.S(f.Basename))
	}

	keys := make([]uint32, 0, len(agg))
	for k := range agg {
		keys = append(keys, k)
	}
	sort.Slice(keys, func(i, j int) bool {
		return g.S(agg[keys[i]].valID) < g.S(agg[keys[j]].valID)
	})
	var rows []qrow
	for _, k := range keys {
		a := agg[k]
		if len(a.files) <= 1 {
			continue
		}
		rows = append(rows, qrow{
			order: []oterm{dsc(a.uses)},
			cells: []string{g.S(a.valID), cellInt(a.uses), cellInt(int32(len(a.files))),
				cellInt(int32(len(a.fns))), a.seenIn.String()},
		})
	}
	qemit(&r, rows, limit)
	return r
}

func run_markers(g *Graph, mod string, limit int) result {
	r := result{cols: cols_markers}
	var rows []qrow
	var markerKinds = map[string]bool{
		"TODO": true, "FIXME": true, "HACK": true, "BUG": true,
		"XXX": true, "WARNING": true,
	}

	byFile := map[int32][]int32{}
	for i := range g.Symbols {
		s := &g.Symbols[i]
		if !isFuncKind(g.S(s.Kind)) {
			continue
		}
		byFile[s.FileID] = append(byFile[s.FileID], s.ID)
	}
	for i := range g.Markers {
		mk := &g.Markers[i]
		if !markerKinds[g.S(mk.Kind)] || !g.nogen(mk.FileID) {
			continue
		}
		f := g.Files[mk.FileID-1]
		if mod != "%" && !dbLike(g.moduleName(f.ModuleID), mod) {
			continue
		}

		sid := int32(0)
		for _, id := range byFile[mk.FileID] {
			s := g.sym(id)
			if mk.Line >= s.LineStart && mk.Line <= s.LineEnd {
				sid = id
				break
			}
		}
		name := "(module level)"
		fanIn := int32(0)
		if sid != 0 {
			name = g.S(g.sym(sid).Name)
			fanIn = g.sym(sid).FanIn
		}
		txt := g.S(mk.Text)
		if len(txt) > 60 {
			txt = txt[:60]
			txt = substrRunes(txt, 60)
		}
		rows = append(rows, qrow{
			order: []oterm{dsc(fanIn)},
			cells: []string{g.S(mk.Kind), g.S(f.Path), cellInt(mk.Line), txt,
				name, cellInt(fanIn)},
			ord: mk.ID,
		})
	}
	qemit(&r, rows, limit)
	return r
}

func substrRunes(s string, n int) string {
	cnt := 0
	for i := range s {
		if cnt == n {
			return s[:i]
		}
		cnt++
	}
	return s
}

func run_parse_coverage(g *Graph, mod string, limit int) result {
	r := result{cols: cols_parse_coverage}
	var rows []qrow
	for i := range g.Files {
		f := &g.Files[i]
		if f.ParseErrors <= 0 && f.Parsed != 0 {
			continue
		}
		if mod != "%" && !dbLike(g.moduleName(f.ModuleID), mod) {
			continue
		}
		rows = append(rows, qrow{
			order: []oterm{dsc(f.Lines)},
			cells: []string{g.S(f.Path), cellInt(f.Lines), cellInt(f.ParseErrors),
				cellInt(int32(f.Parsed)), cellInt(int32(f.IsGenerated)),
				cellInt(int32(f.IsVendored)), cellInt(int32(f.IsTest)), cellInt(f.Bytes)},
			ord: f.ID,
		})
	}
	qemit(&r, rows, limit)
	return r
}

func run_latent_risk_density(g *Graph, mod string, limit int) result {
	r := result{cols: cols_latent_risk_density}
	var rows []qrow
	for i := range g.Symbols {
		s := &g.Symbols[i]
		if !g.notest(s.FileID) || !g.modOK(s, mod) {
			continue
		}
		facts := int32(0)
		for _, v := range [...]int32{s.NOpenNoEncoding, s.NDatetime, s.NDynamicAttr,
			s.NWeakHash, s.NWeakRandom, s.NRequestNoTimeout, s.NSleepInLoop, s.NBareExcept} {
			if v > 0 {
				facts++
			}
		}
		if facts == 0 {
			continue
		}
		rows = append(rows, qrow{
			order: []oterm{dsc(facts), dsc(s.FanIn), dsc(s.Cyclomatic)},
			cells: []string{g.S(s.Name), g.moduleName(s.ModuleID), cellInt(facts),
				cellInt(s.NOpenNoEncoding), cellInt(s.NDatetime), cellInt(s.NDynamicAttr),
				cellInt(s.NWeakHash), cellInt(s.NRequestNoTimeout), cellInt(s.NBareExcept),
				cellInt(s.FanIn), cellInt(s.Cyclomatic), at(g, *s)},
			ord: s.ID,
		})
	}
	qemit(&r, rows, limit)
	return r
}

func run_scattered_concerns(g *Graph, mod string, limit int) result {
	r := result{cols: cols_scattered_concerns}
	type gk struct {
		mods map[int32]bool
		gc   *groupConcat
	}
	agg := map[int32]*gk{}
	for _, e := range g.Edges {
		if e.IsSelf != 0 {
			continue
		}
		if e.CalleeID < 1 || int(e.CalleeID) > len(g.Symbols) || e.CallerID < 1 ||
			int(e.CallerID) > len(g.Symbols) {
			continue
		}
		s := g.sym(e.CalleeID)
		if !isFuncKind(g.S(s.Kind)) || !g.notest(s.FileID) {
			continue
		}
		caller := g.sym(e.CallerID)
		mid := caller.ModuleID
		if mid < 1 {
			continue
		}
		if mod != "%" && !dbLike(g.moduleName(mid), mod) {
			continue
		}
		a := agg[e.CalleeID]
		if a == nil {
			a = &gk{mods: map[int32]bool{}, gc: newGC()}
			agg[e.CalleeID] = a
		}
		a.mods[mid] = true
		a.gc.add(g.moduleName(mid))
	}
	var rows []qrow
	for sid, a := range agg {
		if len(a.mods) <= 5 {
			continue
		}
		s := g.sym(sid)
		rows = append(rows, qrow{
			order: []oterm{dsc(int32(len(a.mods))), dsc(s.FanIn)},
			cells: []string{g.S(s.Name), cellInt(int32(len(a.mods))), cellInt(s.FanIn),
				cellInt(s.Cyclomatic), cellInt(s.SLOC), a.gc.String(), at(g, *s)},
			ord: sid,
		})
	}
	qemit(&r, rows, limit)
	return r
}

func run_line_too_long(g *Graph, mod string, limit int) result {
	r := result{cols: cols_line_too_long}
	var rows []qrow
	for i := range g.Files {
		f := &g.Files[i]
		if f.MaxLineLen <= 100 || !g.notestgen(f.ID) {
			continue
		}
		if mod != "%" && !dbLike(g.moduleName(f.ModuleID), mod) {
			continue
		}
		p := g.S(f.Path)
		rows = append(rows, qrow{
			order: []oterm{dsc(f.MaxLineLen)},
			cells: []string{p, cellInt(f.MaxLineLen), cellInt(f.SLOC), cellInt(f.Lines),
				cellInt(f.NSymbols), p + ":0"},
			ord: f.ID,
		})
	}
	qemit(&r, rows, limit)
	return r
}

func run_god_class(g *Graph, mod string, limit int) result {
	r := result{cols: cols_god_class}
	type gk struct {
		methods, cyclo int32
		hasCyclo       bool
	}
	agg := map[int32]*gk{}
	for i := range g.Symbols {
		s := &g.Symbols[i]
		if g.S(s.Kind) != "method" || s.ParentID < 1 || int(s.ParentID) > len(g.Symbols) {
			continue
		}
		a := agg[s.ParentID]
		if a == nil {
			a = &gk{}
			agg[s.ParentID] = a
		}
		a.methods++
		if !a.hasCyclo {
			a.cyclo, a.hasCyclo = s.Cyclomatic, true
		} else {
			a.cyclo += s.Cyclomatic
		}
	}
	var rows []qrow
	for i := range g.Symbols {
		s := &g.Symbols[i]
		if g.S(s.Kind) != "class" || !g.notest(s.FileID) || !g.modOK(s, mod) {
			continue
		}
		a := agg[s.ID]
		var n, cyclo int32
		cycloCell := "-"
		if a != nil {
			n, cyclo = a.methods, a.cyclo

			cycloCell = cellInt(cyclo)
		}
		rows = append(rows, qrow{

			order: []oterm{dsc(cyclo), ascT(g.S(s.Name))},
			cells: []string{g.S(s.Name), cellInt(n), cycloCell, cellInt(s.FanIn),
				cellInt(s.SLOC), at(g, *s)},
			ord: s.ID,
		})
	}
	qemit(&r, rows, limit)
	return r
}

func run_import_surface(g *Graph, mod string, limit int) result {
	return g.runModMetric(cols_import_surface, mod, limit,
		func(g *Graph, s *Symbol) bool {
			return g.S(s.Kind) == "module" && g.notestgen(s.FileID)
		},
		func(g *Graph, a *modAcc, s *Symbol, f *File) {
			a.add(s.ID, fNIO, s.NIO)
			a.add(s.ID, fNNet, s.NNet)
			a.add(s.ID, fNOpen, s.NOpen)
			a.add(s.ID, fNExec, s.NExec)
			a.add(s.ID, fNShell, s.NShell)
			a.add(s.ID, fNSub, s.NSubprocess)
			a.at.add(g.S(f.Path) + ":1")
		},
		func(a *modAcc) []oterm {
			return []oterm{dsc(sumOf(a, fNIO) + sumOf(a, fNNet) + sumOf(a, fNOpen) +
				sumOf(a, fNExec) + sumOf(a, fNShell) + sumOf(a, fNSub)), dsc(sumOf(a, fNNet))}
		},
		func(g *Graph, a *modAcc) []string {
			return []string{g.moduleName(a.mid), cellInt(int32(len(a.syms))),
				cellInt(sumOf(a, fNIO)), cellInt(sumOf(a, fNNet)), cellInt(sumOf(a, fNOpen)),
				cellInt(sumOf(a, fNExec)), cellInt(sumOf(a, fNShell)), cellInt(sumOf(a, fNSub)),
				cellInt(sumOf(a, fNIO) + sumOf(a, fNNet) + sumOf(a, fNOpen) +
					sumOf(a, fNExec) + sumOf(a, fNShell) + sumOf(a, fNSub)),
				a.at.String()}
		},
		func(g *Graph, a *modAcc) bool {
			return sumOf(a, fNIO)+sumOf(a, fNNet)+sumOf(a, fNOpen)+sumOf(a, fNExec)+
				sumOf(a, fNShell)+sumOf(a, fNSub) > 0
		},
	)
}

func run_exception_posture(g *Graph, mod string, limit int) result {
	r := result{cols: cols_exception_posture}
	type gk struct {
		rows, broad, bare, empty, inLoop, body int32
		at                                     minStr
	}
	agg := map[int32]*gk{}
	for i := range g.Handlers {
		h := &g.Handlers[i]
		if h.SymbolID < 1 || int(h.SymbolID) > len(g.Symbols) {
			continue
		}
		s := g.sym(h.SymbolID)
		if !g.notestgen(s.FileID) {
			continue
		}
		if s.ModuleID < 1 || int(s.ModuleID) > len(g.Modules) {
			continue
		}
		if !dbLike(g.moduleName(s.ModuleID), mod) {
			continue
		}
		a := agg[s.ModuleID]
		if a == nil {
			a = &gk{}
			agg[s.ModuleID] = a
		}
		a.rows++
		a.broad += h.IsBroad
		a.bare += h.IsBare
		a.empty += h.IsEmpty
		a.inLoop += h.InLoop
		a.body += h.NBodyLines
		a.at.addAt(g.path(s.FileID), h.Line)
	}
	var rows []qrow
	for mid, a := range agg {
		if a.rows == 0 {
			continue
		}
		pct, _ := castInt(100.0*float64(a.broad)/float64(a.rows), a.rows != 0)
		rows = append(rows, qrow{
			order: []oterm{dsc(a.rows), dsc(a.broad)},
			cells: []string{g.moduleName(mid), cellInt(a.rows), cellInt(a.broad),
				cellInt(a.bare), cellInt(a.empty), cellInt(a.inLoop), cellInt(a.body),
				cellInt(pct), a.at.String()},
			ord: mid,
		})
	}
	qemit(&r, rows, limit)
	return r
}

func run_resource_posture(g *Graph, mod string, limit int) result {
	return g.runModMetric(cols_resource_posture, mod, limit,
		func(g *Graph, s *Symbol) bool {
			return isFuncKind(g.S(s.Kind)) && g.notestgen(s.FileID)
		},
		func(g *Graph, a *modAcc, s *Symbol, f *File) {
			a.add(s.ID, fNOpen, s.NOpen)
			a.add(s.ID, -3, s.NResource)
			a.add(s.ID, fNCtx, s.NCtxManagers)
			a.add(s.ID, fNWith, s.NWith)
			a.at.addAt(g.S(f.Path), s.LineStart)
		},
		func(a *modAcc) []oterm {
			pct := pctUnmanaged(a)
			return []oterm{dsc(sumOf(a, fNOpen)), dsc(pct)}
		},
		func(g *Graph, a *modAcc) []string {
			return []string{g.moduleName(a.mid), cellInt(int32(len(a.syms))),
				cellInt(sumOf(a, fNOpen)), cellInt(sumOf(a, -3)), cellInt(sumOf(a, fNCtx)),
				cellInt(sumOf(a, fNWith)), cellInt(pctUnmanaged(a)), a.at.String()}
		},
		func(g *Graph, a *modAcc) bool { return sumOf(a, fNOpen) > 0 },
	)
}

func pctUnmanaged(a *modAcc) int32 {
	den := sumOf(a, fNOpen) + sumOf(a, fNCtx)
	pct, _ := castInt(100.0*float64(sumOf(a, fNOpen))/float64(den), den != 0)
	return pct
}

func run_concurrency_posture(g *Graph, mod string, limit int) result {

	mv := map[int32]int32{}
	for _, v := range g.ModuleVars {
		if v.IsMutableContainer != 1 || v.IsConstant != 0 || !g.notest(v.FileID) {
			continue
		}
		mv[v.ModuleID]++
	}
	setModVarCounts(mv)
	return g.runModMetric(cols_concurrency_posture, mod, limit,
		func(g *Graph, s *Symbol) bool {
			return isFuncKind(g.S(s.Kind)) && g.notestgen(s.FileID)
		},
		func(g *Graph, a *modAcc, s *Symbol, f *File) {
			a.add(s.ID, fNConc, s.NConcurrency)
			a.add(s.ID, fNGlobal, s.NGlobalStmt)
			a.add(s.ID, fIsAsync, s.IsAsync)
			a.add(s.ID, fLockInLoop, s.LockInLoop)
			a.at.addAt(g.S(f.Path), s.LineStart)
		},

		func(a *modAcc) []oterm { return []oterm{dsc(a.mutableVars + sharedSites(a))} },
		func(g *Graph, a *modAcc) []string {
			return []string{g.moduleName(a.mid), cellInt(int32(len(a.syms))),
				cellInt(sumOf(a, fNConc)), cellInt(sumOf(a, fNGlobal)),
				cellInt(sumOf(a, fIsAsync)), cellInt(sumOf(a, fLockInLoop)),
				cellInt(a.mutableVars), cellInt(a.mutableVars + sharedSites(a)),
				a.at.String()}
		},
		func(g *Graph, a *modAcc) bool { return a.mutableVars+sharedSites(a) > 0 },
		true,
	)
}

func sharedSites(a *modAcc) int32 {
	return sumOf(a, fNConc) + sumOf(a, fNGlobal)
}

func run_sql_construction(g *Graph, mod string, limit int) result {
	return g.runModMetric(cols_sql_construction, mod, limit,
		func(g *Graph, s *Symbol) bool {
			return isFuncKind(g.S(s.Kind)) && g.notestgen(s.FileID)
		},
		func(g *Graph, a *modAcc, s *Symbol, f *File) {
			a.add(s.ID, fNSql, s.NSql)
			a.add(s.ID, fNSqlFstring, s.NSqlFstring)
			a.add(s.ID, fNSqlConcat, s.NSqlConcat)
			a.add(s.ID, fNSqlFormat, s.NSqlFormat)
			a.add(s.ID, fQueryInLoop, s.QueryInLoop)
			a.at.addAt(g.S(f.Path), s.LineStart)
		},
		func(a *modAcc) []oterm { return []oterm{dsc(handBuilt(a)), dsc(sumOf(a, fQueryInLoop))} },
		func(g *Graph, a *modAcc) []string {
			return []string{g.moduleName(a.mid), cellInt(int32(len(a.syms))),
				cellInt(sumOf(a, fNSql)), cellInt(sumOf(a, fNSqlFstring)),
				cellInt(sumOf(a, fNSqlConcat)), cellInt(sumOf(a, fNSqlFormat)),
				cellInt(handBuilt(a)), cellInt(sumOf(a, fQueryInLoop)),
				cellInt(pctHandBuilt(a)), a.at.String()}
		},
		func(g *Graph, a *modAcc) bool { return handBuilt(a) > 0 },
	)
}

func handBuilt(a *modAcc) int32 {
	return sumOf(a, fNSqlFstring) + sumOf(a, fNSqlConcat) + sumOf(a, fNSqlFormat)
}

func pctHandBuilt(a *modAcc) int32 {
	den := sumOf(a, fNSql)
	if den == 0 {
		return 100
	}
	v := 100.0 * float64(handBuilt(a)) / float64(den)
	if v > 100 {
		v = 100
	}
	pct, _ := castInt(v, true)
	return pct
}

func run_third_party_coupling(g *Graph, mod string, limit int) result {
	r := result{cols: cols_third_party_coupling}
	type gk struct {
		rows, ext, rel, wild int32
		roots                map[string]bool
		at                   minStr
	}
	agg := map[int32]*gk{}
	for i := range g.Imports {
		im := &g.Imports[i]
		if !g.notestgen(im.FileID) {
			continue
		}
		f := g.Files[im.FileID-1]
		if f.ModuleID < 1 || int(f.ModuleID) > len(g.Modules) {
			continue
		}
		if !dbLike(g.moduleName(f.ModuleID), mod) {
			continue
		}
		a := agg[f.ModuleID]
		if a == nil {
			a = &gk{roots: map[string]bool{}}
			agg[f.ModuleID] = a
		}
		a.rows++
		a.ext += im.IsExternal
		a.rel += im.IsRelative
		a.wild += im.IsWildcard
		if im.IsExternal == 1 {

			t := g.S(im.Target)
			cut := len(t)
			if k := indexOf(t+"."[:1]+t[1:], "."); k >= 0 && k < cut {
				cut = k
			}
			a.roots[strings_ToLower(t[:cut])] = true
		}
		a.at.addAt(g.S(f.Path), im.Line)
	}
	var rows []qrow
	for mid, a := range agg {
		if len(a.roots) == 0 {
			continue
		}
		rows = append(rows, qrow{
			order: []oterm{dsc(int32(len(a.roots))), dsc(a.ext)},
			cells: []string{g.moduleName(mid), cellInt(a.rows), cellInt(a.ext),
				cellInt(int32(len(a.roots))), cellInt(a.rel), cellInt(a.wild),
				a.at.String()},
			ord: mid,
		})
	}
	qemit(&r, rows, limit)
	return r
}

func strings_ToLower(s string) string {
	b := []byte(s)
	for i := range b {
		if b[i] >= 'A' && b[i] <= 'Z' {
			b[i] += 32
		}
	}
	return string(b)
}

func run_registration_surface(g *Graph, mod string, limit int) result {
	r := result{cols: cols_registration_surface}
	pat := []string{"%route%", "%task%", "%receiver%", "%signal%", "%command%",
		"%listener%", "%subscribe%", "%event%", "%handler%", "%fixture%",
		"%connect%", "%hook%", "%register%"}
	type gk struct {
		attrs, fns int32
		names      *groupConcat
		at         minStr
		seen       map[int32]bool
	}
	agg := map[int32]*gk{}
	for i := range g.Attributes {
		a := &g.Attributes[i]
		if a.SymbolID < 1 || int(a.SymbolID) > len(g.Symbols) {
			continue
		}
		s := g.sym(a.SymbolID)
		if !g.notestgen(s.FileID) {
			continue
		}
		if s.ModuleID < 1 || int(s.ModuleID) > len(g.Modules) {
			continue
		}
		if !dbLike(g.moduleName(s.ModuleID), mod) {
			continue
		}
		n := g.S(a.Name)
		match := false
		for _, p := range pat {
			if dbLike(n, p) {
				match = true
				break
			}
		}
		if !match {
			continue
		}
		acc := agg[s.ModuleID]
		if acc == nil {
			acc = &gk{names: newGC(), seen: map[int32]bool{}}
			agg[s.ModuleID] = acc
		}
		acc.attrs++
		acc.names.add(n)

		if !acc.seen[s.ID] {
			acc.seen[s.ID] = true
			acc.fns++
			acc.at.addAt(g.path(s.FileID), s.LineStart)
		}
	}
	var rows []qrow
	for mid, a := range agg {
		rows = append(rows, qrow{
			order: []oterm{dsc(a.attrs)},
			cells: []string{g.moduleName(mid), cellInt(a.attrs), cellInt(a.fns),
				a.names.String(), a.at.String()},
			ord: -mid,
		})
	}
	qemit(&r, rows, limit)
	return r
}

func run_input_surface(g *Graph, mod string, limit int) result {
	r := result{cols: cols_input_surface}
	type gk struct {
		reads, fns, auth int32
	}
	agg := map[int32]*gk{}
	for i := range g.InputSites {
		u := &g.InputSites[i]
		if u.FileID < 1 || int(u.FileID) > len(g.Files) {
			continue
		}
		f := g.Files[u.FileID-1]
		if !g.notestgen(u.FileID) {
			continue
		}
		if f.ModuleID < 1 || int(f.ModuleID) > len(g.Modules) {
			continue
		}
		if !dbLike(g.moduleName(f.ModuleID), mod) {
			continue
		}
		a := agg[f.ModuleID]
		if a == nil {
			a = &gk{}
			agg[f.ModuleID] = a
		}
		a.reads++
	}

	authFns := map[int32]map[int32]bool{}
	for i := range g.Symbols {
		s := &g.Symbols[i]
		if !isFuncKind(g.S(s.Kind)) {
			continue
		}
		if s.ModuleID < 1 || int(s.ModuleID) > len(g.Modules) {
			continue
		}
		if !dbLike(g.moduleName(s.ModuleID), mod) {
			continue
		}
		a := agg[s.ModuleID]
		if a == nil {
			continue
		}
		if authFns[s.ModuleID] == nil {
			authFns[s.ModuleID] = map[int32]bool{}
		}
		if authFns[s.ModuleID][s.ID] {
			continue
		}
		authFns[s.ModuleID][s.ID] = true
		a.fns++
		if s.NAuthCall > 0 {
			a.auth++
		}
	}
	var rows []qrow
	for mid, a := range agg {
		if a.reads == 0 {
			continue
		}
		pct, _ := castInt(100.0*float64(a.auth)/float64(a.fns), a.fns != 0)
		rows = append(rows, qrow{
			order: []oterm{dsc(a.reads), dsc(-pct)},
			cells: []string{g.moduleName(mid), cellInt(a.reads), cellInt(a.fns),
				cellInt(a.auth), cellInt(pct), g.moduleName(mid) + ":1"},
			ord: mid,
		})
	}
	qemit(&r, rows, limit)
	return r
}

func run_network_hygiene(g *Graph, mod string, limit int) result {
	return g.runModMetric(cols_network_hygiene, mod, limit,
		func(g *Graph, s *Symbol) bool {
			return isFuncKind(g.S(s.Kind)) && g.notestgen(s.FileID)
		},
		func(g *Graph, a *modAcc, s *Symbol, f *File) {
			a.add(s.ID, fNNet, s.NNet)
			a.add(s.ID, fNReqTO, s.NRequestNoTimeout)
			a.add(s.ID, fNFetch, s.NFetch)
			a.at.addAt(g.S(f.Path), s.LineStart)
		},
		func(a *modAcc) []oterm {
			return []oterm{dsc(sumOf(a, fNReqTO)), dsc(sumOf(a, fNNet))}
		},
		func(g *Graph, a *modAcc) []string {
			return []string{g.moduleName(a.mid), cellInt(int32(len(a.syms))),
				cellInt(sumOf(a, fNNet)), cellInt(sumOf(a, fNReqTO)),
				cellInt(sumOf(a, fNFetch)), cellInt(pctNoTimeout(a)), a.at.String()}
		},
		func(g *Graph, a *modAcc) bool { return sumOf(a, fNReqTO) > 0 },
	)
}

func pctNoTimeout(a *modAcc) int32 {
	den := sumOf(a, fNNet)
	if den == 0 {
		return 0
	}
	v := 100.0 * float64(sumOf(a, fNReqTO)) / float64(den)
	if v > 100 {
		v = 100
	}
	pct, _ := castInt(v, true)
	return pct
}

type oterm struct {
	key int32
	txt string
	asc bool
	num bool
}

func dsc(v int32) oterm   { return oterm{key: v} }
func ascT(v string) oterm { return oterm{txt: v, asc: true} }
func ascI(v int32) oterm  { return oterm{key: v, asc: true, num: true} }

type qrow struct {
	order []oterm
	cells []string

	ord int32
}

func qlts(a, b *qrow) bool {
	for i := 0; i < len(a.order) && i < len(b.order); i++ {
		x, y := &a.order[i], &b.order[i]
		if x.asc && x.num {
			if x.key != y.key {
				return x.key < y.key
			}
			continue
		}
		if x.asc {
			if x.txt != y.txt {
				return x.txt < y.txt
			}
			continue
		}
		if x.key != y.key {
			return x.key > y.key
		}
	}

	return a.ord < b.ord
}

func qsort(rows []qrow) {
	if len(rows) < 2 {
		return
	}
	buf := make([]qrow, len(rows))
	src, dst := rows, buf
	inRows := true
	for width := 1; width < len(src); width *= 2 {
		for i := 0; i < len(src); i += 2 * width {
			qmerge(src, dst, i, min(i+width, len(src)), min(i+2*width, len(src)))
		}
		src, dst = dst, src
		inRows = !inRows
	}
	if !inRows {
		copy(rows, src)
	}
}

func qmerge(src, dst []qrow, lo, mid, hi int) {
	i, j, k := lo, mid, lo
	for i < mid && j < hi {
		if qlts(&src[j], &src[i]) {
			dst[k] = src[j]
			j++
		} else {
			dst[k] = src[i]
			i++
		}
		k++
	}
	for i < mid {
		dst[k] = src[i]
		i++
		k++
	}
	for j < hi {
		dst[k] = src[j]
		j++
		k++
	}
}

func qemit(r *result, rows []qrow, limit int) {
	qsort(rows)
	if limit >= 0 && len(rows) > limit {
		rows = rows[:limit]
	}
	for i := range rows {
		r.rows = append(r.rows, rows[i].cells)
	}
}

func cellInt(v int32) string { return itoa(v) }

func cellFloat(v float64) string { return sprintf("%.2f", v) }

func cellOptInt(v int32, ok bool) string {
	if !ok {
		return "-"
	}
	return itoa(v)
}

func (g *Graph) cellText(id uint32) string {
	if g.Strings.IsNull(id) {
		return "-"
	}
	return g.S(id)
}

func (g *Graph) cellTextOr(id uint32, def string) string {
	if g.Strings.IsNull(id) {
		return def
	}
	return g.S(id)
}

func castInt(v float64, valid bool) (int32, bool) {
	if !valid {
		return 0, false
	}
	return int32(int64(v)), true
}

func joinStrings(parts []string, sep string) string {
	switch len(parts) {
	case 0:
		return ""
	case 1:
		return parts[0]
	}
	n := len(sep) * (len(parts) - 1)
	for _, p := range parts {
		n += len(p)
	}
	b := make([]byte, 0, n)
	for i, p := range parts {
		if i > 0 {
			b = append(b, sep...)
		}
		b = append(b, p...)
	}
	return string(b)
}

type minStr struct {
	best string
	set  bool
}

func (m *minStr) add(s string) {
	if !m.set || s < m.best {
		m.best, m.set = s, true
	}
}

func (m *minStr) addAt(path string, line int32) { m.add(path + ":" + itoa(line)) }

func (m *minStr) String() string {
	if !m.set {
		return "-"
	}
	return m.best
}

func (g *Graph) sym(id int32) *Symbol { return &g.Symbols[id-1] }

func (g *Graph) reach(roots []int32, maxDepth int32, skipSelf bool) (map[int32]int32, map[int32]int32) {
	depth := make(map[int32]int32, len(roots)*4)
	parent := make(map[int32]int32, len(roots)*4)
	queue := make([]int32, 0, len(roots)*4)
	for _, r := range roots {
		if _, seen := depth[r]; seen {
			continue
		}
		depth[r] = 0
		queue = append(queue, r)
	}
	for i := 0; i < len(queue); i++ {
		cur := queue[i]
		d := depth[cur]
		if maxDepth > 0 && d >= maxDepth {
			continue
		}
		for _, c := range g.callees(cur) {
			if skipSelf && c == cur {
				continue
			}
			if _, seen := depth[c]; seen {
				continue
			}
			depth[c] = d + 1
			parent[c] = cur
			queue = append(queue, c)
		}
	}
	return depth, parent
}

type row struct {
	id    int32
	keys  []int32
	cells []string
}

func (g *Graph) rank(rows []row) {
	sort.SliceStable(rows, func(i, j int) bool {
		a, b := rows[i], rows[j]
		for k := 0; k < len(a.keys) && k < len(b.keys); k++ {
			if a.keys[k] != b.keys[k] {
				return a.keys[k] > b.keys[k]
			}
		}
		an, bn := g.S(g.Symbols[a.id-1].Name), g.S(g.Symbols[b.id-1].Name)
		if an != bn {
			return an > bn
		}
		return a.id < b.id
	})
}

func (g *Graph) emit(r *result, rows []row, limit int) {
	g.rank(rows)
	for i, x := range rows {
		if limit >= 0 && i >= limit {
			break
		}
		r.rows = append(r.rows, x.cells)
	}
	if r.cols == nil {
		r.cols = []string{}
	}
}

func at(g *Graph, s Symbol) string { return g.path(s.FileID) + ":" + strconv.Itoa(int(s.LineStart)) }

func num(v int32) string { return strconv.Itoa(int(v)) }

type groupedRow struct {
	key   string
	keys  []int32
	cells []string
}

func rankGroups(g *Graph, rows []groupedRow) {
	sort.SliceStable(rows, func(i, j int) bool {
		a, b := rows[i], rows[j]
		for k := 0; k < len(a.keys) && k < len(b.keys); k++ {
			if a.keys[k] != b.keys[k] {
				return a.keys[k] > b.keys[k]
			}
		}
		return a.key < b.key
	})
}

func emitGroups(r *result, rows []groupedRow, limit int) {
	for i, x := range rows {
		if limit >= 0 && i >= limit {
			break
		}
		r.rows = append(r.rows, x.cells)
	}
}

func (g *Graph) attrsOf(sid int32) []string {
	var out []string
	for _, a := range g.Attributes {
		if a.SymbolID == sid {
			out = append(out, g.S(a.Name))
		}
	}
	return out
}

func (g *Graph) paramRows(sid int32) []Param {
	var out []Param
	for _, p := range g.Params {
		if p.SymbolID == sid {
			out = append(out, p)
		}
	}
	return out
}

func (g *Graph) moduleName(mid int32) string {
	if mid < 1 || int(mid) > len(g.Modules) {
		return ""
	}
	return g.S(g.Modules[mid-1].Name)
}

func joinDistinct(parts []string, sep string) string {
	seen := map[string]bool{}
	var out []string
	for _, p := range parts {
		if p == "" || seen[p] {
			continue
		}
		seen[p] = true
		out = append(out, p)
	}
	return strings.Join(out, sep)
}

func (g *Graph) runQuestion(q question, mod string, limit int) result {
	if mod == "" {
		mod = "%"
	}
	if sq, ok := symQueries[q.name]; ok {
		return g.runSymQ(sq, mod, limit)
	}
	return q.run(g, mod, limit)
}

func tokenCount(s string) int {
	n := 0
	inTok := false
	var cur []rune
	for _, r := range s {
		if unicode.IsLetter(r) || unicode.IsDigit(r) {
			cur = append(cur, foldRune(r))
			inTok = true
			continue
		}
		if inTok {
			n++
			cur = cur[:0]
			inTok = false
		}
	}
	if inTok {
		n++
	}
	return n
}

var diacriticFolding = map[rune]rune{
	'À': 'A', 'Á': 'A', 'Â': 'A', 'Ã': 'A', 'Ä': 'A', 'Å': 'A', 'Æ': 'A',
	'Ç': 'C', 'È': 'E', 'É': 'E', 'Ê': 'E', 'Ë': 'E', 'Ì': 'I', 'Í': 'I',
	'Î': 'I', 'Ï': 'I', 'Ð': 'D', 'Ñ': 'N', 'Ò': 'O', 'Ó': 'O', 'Ô': 'O',
	'Õ': 'O', 'Ö': 'O', 'Ø': 'O', 'Ù': 'U', 'Ú': 'U', 'Û': 'U', 'Ü': 'U',
	'Ý': 'Y', 'Þ': 'P', 'ß': 's', 'à': 'a', 'á': 'a', 'â': 'a', 'ã': 'a',
	'ä': 'a', 'å': 'a', 'æ': 'a', 'ç': 'c', 'è': 'e', 'é': 'e', 'ê': 'e',
	'ë': 'e', 'ì': 'i', 'í': 'i', 'î': 'i', 'ï': 'i', 'ð': 'd', 'ñ': 'n',
	'ò': 'o', 'ó': 'o', 'ô': 'o', 'õ': 'o', 'ö': 'o', 'ø': 'o', 'ù': 'u',
	'ú': 'u', 'û': 'u', 'ü': 'u', 'ý': 'y', 'þ': 'p', 'ÿ': 'y',
}

func foldRune(r rune) rune {
	if f, ok := diacriticFolding[r]; ok {
		return f
	}

	if r >= 0x0300 && r <= 0x036F {
		return 0
	}
	if r < 128 {
		if r >= 'A' && r <= 'Z' {
			return r + 32
		}
		return r
	}
	return unicode.ToLower(r)
}

func (g *Graph) writeFTS(d *dumper) {

	ftsRows := make([][]field, 0, len(g.Symbols))
	nulls := []field{fNullV(), fNullV(), fNullV()}
	for range g.Symbols {
		ftsRows = append(ftsRows, nulls)
	}
	d.table("sym_fts", 3, ftsRows)
	d.table("sym_fts_config", 2, [][]field{{fStrV("version"), fIntV(4)}})

	docsize := make([][]field, 0, len(g.Symbols))
	for i := range g.Symbols {
		s := &g.Symbols[i]
		n1 := int64(tokenCount(g.S(s.Name)))
		n2 := int64(tokenCount(g.S(s.QualName)))
		n3 := int64(tokenCount(g.S(s.Signature)))
		blob := append(append(svarint(n1), svarint(n2)...), svarint(n3)...)
		docsize = append(docsize, []field{fIntV(s.ID), fBlob(blob)})
	}
	d.table("sym_fts_docsize", 2, docsize)
}

func svarint(v int64) []byte {
	if v < 0 {
		return svarintU(uint64(v))
	}
	return svarintU(uint64(v))
}

func svarintU(v uint64) []byte {
	if v>>56 != 0 {

		out := make([]byte, 9)
		for i := 8; i >= 1; i-- {
			out[i] = byte(v)
			v >>= 7
			out[i] |= 0x80
		}
		out[0] = byte(v)
		return out
	}
	var tmp [9]byte
	n := 0
	for {
		tmp[n] = byte(v & 0x7f)
		n++
		v >>= 7
		if v == 0 {
			break
		}
	}
	for i := 0; i < n-1; i++ {
		tmp[i] |= 0x80
	}
	out := make([]byte, n)
	for i := 0; i < n; i++ {
		out[i] = tmp[n-1-i]
	}
	return out
}

func fBlob(b []byte) field { return field{kind: 5, s: reprBytes(b)} }

func reprBytes(b []byte) string {
	sq, dq := 0, 0
	for _, c := range b {
		switch c {
		case '\'':
			sq++
		case '"':
			dq++
		}
	}
	quote := byte('"')
	if sq <= dq {
		quote = '\''
	}
	out := make([]byte, 0, len(b)*4+3)
	out = append(out, 'b', quote)
	const hexd = "0123456789abcdef"
	for _, c := range b {
		switch {
		case c == quote || c == '\\':
			out = append(out, '\\', c)
		case c == '\t':
			out = append(out, '\\', 't')
		case c == '\n':
			out = append(out, '\\', 'n')
		case c == '\r':
			out = append(out, '\\', 'r')
		case c >= 0x20 && c < 0x7F:
			out = append(out, c)
		default:
			out = append(out, '\\', 'x', hexd[c>>4], hexd[c&0xF])
		}
	}
	out = append(out, quote)
	return string(out)
}

func fn_i32_(g *Graph, v int32) field {
	if v < 0 {
		return fNullV()
	}
	return fIntV(v)
}

func fn_st_(g *Graph, id uint32) field {
	if g.Strings.IsNull(id) {
		return fNullV()
	}
	return fStrV(g.Strings.Get(id))
}

func (g *Graph) Write(out *bufio.Writer) {
	d := &dumper{w: out}
	d.table("meta", 2, g.fn_metaRows_())
	d.table("modules", 10, g.fn_moduleRows_())
	d.table("files", 29, g.fn_fileRows_())
	d.table("symbols", 215, g.fn_symbolRows_())
	d.table("params", 13, g.fn_paramRows_())
	d.table("fields", 14, g.fn_fieldRows_())
	d.table("locals", 11, nil)
	d.table("edges", 6, g.fn_edgeRows_())
	d.table("callsites", 3, g.fn_callsiteRows_())
	d.table("unresolved_calls", 4, g.fn_unresolvedRows_())
	d.table("imports", 13, g.fn_importRows_())
	d.table("hazards", 5, g.fn_hazardRows_())
	d.table("attributes", 6, g.fn_attributeRows_())
	d.table("literals", 7, g.fn_literalRows_())
	d.table("enum_members", 5, g.fn_enumRows_())
	d.table("markers", 6, g.fn_markerRows_())
	d.table("classes", 22, g.fn_classRows_())
	d.table("handlers", 12, g.fn_handlerRows_())
	d.table("dynamic_sites", 7, g.fn_dynamicRows_())
	d.table("comprehensions", 9, g.fn_compRows_())
	d.table("module_vars", 10, g.fn_moduleVarRows_())
	d.table("all_exports", 4, g.fn_allExportRows_())
	d.table("user_input_sites", 7, g.fn_inputRows_())
	d.table("secret_candidates", 5, g.fn_secretRows_())
	d.table("api_sites", 7, g.fn_apiRows_())
	g.writeFTS(d)
	d.flush()
}

func (g *Graph) fn_metaRows_() [][]field {
	rows := make([][]field, 0, len(g.Meta))
	for _, kv := range g.Meta {
		rows = append(rows, []field{fStrV(g.S(kv[0])), fStrV(g.S(kv[1]))})
	}
	return rows
}

func (g *Graph) fn_moduleRows_() [][]field {
	rows := make([][]field, 0, len(g.Modules))
	for _, m := range g.Modules {
		rows = append(rows, []field{
			fIntV(m.ID), fn_st_(g, m.Name), fn_st_(g, m.Kind), fIntV(m.NFiles),
			fIntV(m.NSymbols), fIntV(m.NPublic), fIntV(m.SLOC),
			fIntV(m.FanIn), fIntV(m.FanOut), fFloatV(m.Instability)})
	}
	return rows
}

func (g *Graph) fn_fileRows_() [][]field {
	rows := make([][]field, 0, len(g.Files))
	for _, f := range g.Files {
		rows = append(rows, []field{
			fIntV(f.ID), fn_st_(g, f.Path), fn_st_(g, f.Dir), fn_st_(g, f.Basename), fn_st_(g, f.Ext),
			fStrV("python"), fn_i32_(g, f.ModuleID), fIntV(f.Bytes), fIntV(f.Lines),
			fIntV(f.SLOC), fIntV(f.BlankLines), fIntV(f.CommentLines),
			fIntV(f.DocLines), fIntV(f.MaxLineLen), fn_st_(g, f.SHA1),
			fIntV(int32(f.Parsed)), fIntV(int32(f.IsTest)),
			fIntV(int32(f.IsGenerated)), fIntV(int32(f.IsVendored)),
			fIntV(f.ParseErrors), fIntV(f.MissingNodes), fFloatV(f.ParseMS),
			fIntV(f.NSymbols), fIntV(f.NFunctions), fIntV(f.NTypes),
			fIntV(f.NImports), fIntV(f.TotalCyclo), fIntV(f.MaxCyclo),
			fIntV(f.TotalRisk)})
	}
	return rows
}

func (g *Graph) fn_symbolRows_() [][]field {
	rows := make([][]field, 0, len(g.Symbols))
	for _, s := range g.Symbols {
		r := make([]field, 0, 215)
		r = append(r, fIntV(s.ID), fn_i32_(g, s.FileID), fn_i32_(g, s.ModuleID),
			fn_i32_(g, s.ParentID), fn_st_(g, s.Name), fn_st_(g, s.QualName), fn_st_(g, s.Kind),
			fIntV(s.LineStart), fIntV(s.LineEnd), fIntV(s.NLines),
			fIntV(s.ByteStart), fIntV(s.ByteEnd), fn_st_(g, s.Signature),
			fn_st_(g, s.ReturnType), fn_st_(g, s.Visibility),
			fIntV(s.NParams), fIntV(s.NOptionalParams), fIntV(s.NGenericParams),
			fIntV(s.NOverloads), fIntV(s.ArityRank),
			fIntV(s.IsPublic), fIntV(s.IsStatic), fIntV(s.IsAsync),
			fIntV(s.IsGenerator), fIntV(s.IsAbstract), fIntV(s.IsOverride),
			fIntV(s.IsExported), fIntV(s.IsTest), fIntV(s.IsDeprecated),
			fIntV(s.IsEntrypoint), fIntV(s.IsGenerated), fIntV(s.SLOC),
			fIntV(s.BodyBytes), fIntV(s.NCommentLines), fIntV(s.NDocLines),
			fIntV(s.HasDoc), fIntV(s.Cyclomatic), fIntV(s.Cognitive),
			fIntV(s.MaxNesting), fIntV(s.NTokens), fIntV(s.NOperators),
			fIntV(s.NOperands), fIntV(s.NDistinctOps), fIntV(s.NDistinctOperand),
			fInt64V(s.HalsteadVolume), fIntV(s.Maintainability),
			fIntV(s.NLoops), fIntV(s.NBranches), fIntV(s.NReturns),
			fIntV(s.NEarlyReturns), fIntV(s.NSwitch), fIntV(s.NCases),
			fIntV(s.NTernary), fIntV(s.NLogical), fIntV(s.NTry), fIntV(s.NCatch),
			fIntV(s.NCatchBroad), fIntV(s.NCatchEmpty), fIntV(s.NFinally),
			fIntV(s.NThrow), fIntV(s.NLabels), fIntV(s.NGotos),
			fIntV(s.MaxLoopDepth), fIntV(s.CallInLoop), fIntV(s.AllocInLoop),
			fIntV(s.IOInLoop), fIntV(s.AwaitInLoop), fIntV(s.LockInLoop),
			fIntV(s.ConcatInLoop), fIntV(s.RegexInLoop), fIntV(s.QueryInLoop),
			fIntV(s.BranchInLoop), fIntV(s.NLocals), fIntV(s.NAssign),
			fIntV(s.NCompoundAssign), fIntV(s.NIncdec), fIntV(s.NCmp),
			fIntV(s.NBitop), fIntV(s.NShift), fIntV(s.NArith), fIntV(s.NStringLit),
			fIntV(s.NRegexLit), fIntV(s.NFloatLit), fIntV(s.NMagic),
			fIntV(s.NNullCheck), fIntV(s.NSubscript), fIntV(s.NMemberAccess),
			fIntV(s.NLambda), fIntV(s.NClosureCapture), fIntV(s.NCalls),
			fIntV(s.NUniqueCalls), fIntV(s.NDynamicCalls),
			fIntV(s.NUnresolvedCalls), fIntV(s.FanIn), fIntV(s.FanOut),
			fIntV(s.NCallsites), fIntV(s.IsRecursive), fIntV(s.IsLeaf),
			fIntV(s.IsRoot), fIntV(s.NHazards), fIntV(s.RiskScore),
			fIntV(s.NExec), fIntV(s.NDeserialize), fIntV(s.NIO), fIntV(s.NNet),
			fIntV(s.NSql), fIntV(s.NCrypto), fIntV(s.NReflect),
			fIntV(s.NConcurrency), fIntV(s.NBlocking), fIntV(s.NResource),
			fIntV(s.NShell), fIntV(s.NDecorators), fIntV(s.NComprehension),
			fIntV(s.NNestedComprehension), fIntV(s.NAsyncComprehension),
			fIntV(s.NCompGenerators), fIntV(s.NCompIfs), fIntV(s.NGenexp),
			fIntV(s.NYield), fIntV(s.NYieldFrom), fIntV(s.NAwait),
			fIntV(s.NGlobalStmt), fIntV(s.NNonlocal), fIntV(s.NBareExcept),
			fIntV(s.NCatchSwallow), fIntV(s.NReraise), fIntV(s.NWith),
			fIntV(s.NAsyncWith), fIntV(s.NCtxManagers), fIntV(s.NFstring),
			fIntV(s.NIsinstance), fIntV(s.NSuper), fIntV(s.NWalrus),
			fIntV(s.NMatch), fIntV(s.NAssert), fIntV(s.NDel), fIntV(s.NPrint),
			fIntV(s.NOpen), fIntV(s.NSelfAttr), fIntV(s.NInnerFunction),
			fIntV(s.NInnerClass), fIntV(s.NMutableDefault), fIntV(s.NStarArgs),
			fIntV(s.NKwargs), fIntV(s.NDefaultArgs), fIntV(s.NKwonlyArgs),
			fIntV(s.NPosonlyArgs), fIntV(s.NAnnotatedParams),
			fIntV(s.NUntypedParams), fIntV(s.HasReturnType),
			fIntV(s.NAppendInLoop), fIntV(s.LenInLoop), fIntV(s.AppendInLoop),
			fIntV(s.TryInLoop), fIntV(s.NRangeLen), fIntV(s.NTryInLoop),
			fIntV(s.NLoopElse), fIntV(s.NRegexCompile), fIntV(s.NRegexCall),
			fIntV(s.NSqlLiteral), fIntV(s.NSqlFstring), fIntV(s.NSqlConcat),
			fIntV(s.NSqlFormat), fIntV(s.NShellTrue), fIntV(s.NAnnotatedAssign),
			fIntV(s.NTryElse), fIntV(s.NPickleLoad), fIntV(s.NYamlLoad),
			fIntV(s.NWeakRandom), fIntV(s.NWeakHash), fIntV(s.NEvalExec),
			fIntV(s.NOSystem), fIntV(s.NInsecureTemp), fIntV(s.NSleepInLoop),
			fIntV(s.NDynamicAttr), fIntV(s.NDictGetInLoop),
			fIntV(s.NOpenNoEncoding), fIntV(s.NDatetime),
			fIntV(s.NRequestNoTimeout), fIntV(s.NRedirect), fIntV(s.NAuthCall),
			fIntV(s.NFetch), fIntV(s.NXxeParser), fIntV(s.NDynamicOpen),
			fIntV(s.NUploadSave), fIntV(s.NZipRead), fIntV(s.NLogCall),
			fIntV(s.NAssertInLoop), fIntV(s.NSubprocess),
			fIntV(s.NFormatInLoop), fIntV(s.NElif), fIntV(s.NExternalCalls),
			fIntV(s.NLoopClosure), fIntV(s.NBroadRaises),
			fIntV(s.NAutoescapeFalse), fIntV(s.IsProperty), fIntV(s.IsClassmethod),
			fIntV(s.IsStaticmethod), fIntV(s.IsDunder), fIntV(s.IsPrivate),
			fIntV(s.IsOverload), fIntV(s.IsContextmanager), fIntV(s.IsCached),
			fIntV(s.NestLevel), fIntV(s.NOrmQueryInLoop), fIntV(s.NCommitInLoop),
			fIntV(s.NOrmWrite), fIntV(s.NAtomic), fIntV(s.NAwaitInSyncWith),
			fIntV(s.NInScanLoop), fIntV(s.NResourceReturn), fIntV(s.NMarkSafe),
			fIntV(s.NMassAssign), fIntV(s.NVerifyFalse))
		if len(r) != 215 {
			panic("symbol row has " + strconvItoa(len(r)) + " columns, want 215")
		}
		rows = append(rows, r)
	}
	return rows
}

func (g *Graph) fn_paramRows_() [][]field {
	rows := make([][]field, 0, len(g.Params))
	for _, p := range g.Params {
		rows = append(rows, []field{fIntV(p.SymbolID), fIntV(p.Pos), fn_st_(g, p.Name),
			fn_st_(g, p.Type), fn_st_(g, p.DefaultValue), fIntV(p.IsOptional),
			fIntV(p.IsVariadic), fIntV(p.IsRef), fIntV(p.IsMutable),
			fIntV(p.IsNullable), fIntV(p.IsGeneric), fIntV(p.IsUntyped),
			fIntV(p.TypeDepth)})
	}
	return rows
}

func (g *Graph) fn_fieldRows_() [][]field {
	rows := make([][]field, 0, len(g.Fields))
	for _, p := range g.Fields {
		rows = append(rows, []field{fIntV(p.SymbolID), fIntV(p.Ordinal),
			fn_st_(g, p.Name), fn_st_(g, p.Type), fn_st_(g, p.Visibility), fIntV(p.Line),
			fIntV(p.IsStatic), fIntV(p.IsConst), fIntV(p.IsMutable),
			fIntV(p.IsNullable), fIntV(p.IsColl), fIntV(p.IsUntyped),
			fIntV(p.HasDefault), fIntV(p.TypeDepth)})
	}
	return rows
}

func (g *Graph) fn_edgeRows_() [][]field {
	rows := make([][]field, 0, len(g.Edges))
	for _, e := range g.Edges {
		rows = append(rows, []field{fIntV(e.CallerID), fIntV(e.CalleeID),
			fIntV(e.NCalls), fIntV(e.SameFile), fIntV(e.SameModule), fIntV(e.IsSelf)})
	}
	return rows
}

func (g *Graph) fn_callsiteRows_() [][]field {
	rows := make([][]field, 0, len(g.Callsites))
	for _, c := range g.Callsites {
		rows = append(rows, []field{fIntV(c.CallerID), fIntV(c.CalleeID), fIntV(c.Line)})
	}
	return rows
}

func (g *Graph) fn_unresolvedRows_() [][]field {
	rows := make([][]field, 0, len(g.Unresolved))
	for _, u := range g.Unresolved {
		rows = append(rows, []field{fIntV(u.CallerID), fn_st_(g, u.Name),
			fIntV(u.N), fIntV(u.FirstLine)})
	}
	return rows
}

func (g *Graph) fn_importRows_() [][]field {
	rows := make([][]field, 0, len(g.Imports))
	for _, im := range g.Imports {
		rows = append(rows, []field{fIntV(im.ID), fIntV(im.FileID), fn_st_(g, im.Target),
			fn_i32_(g, im.TargetID), fn_st_(g, im.Alias), fn_st_(g, im.Kind), fIntV(im.Line),
			fIntV(im.IsExternal), fIntV(im.IsRelative), fIntV(im.IsWildcard),
			fIntV(im.IsTypeOnly), fIntV(im.IsDynamic), fIntV(im.NNames)})
	}
	return rows
}

func (g *Graph) fn_hazardRows_() [][]field {
	rows := make([][]field, 0, len(g.Hazards))
	for _, h := range g.Hazards {
		rows = append(rows, []field{fIntV(h.SymbolID), fn_st_(g, h.Pattern),
			fn_st_(g, h.Category), fIntV(h.N), fIntV(h.FirstLine)})
	}
	return rows
}

func (g *Graph) fn_attributeRows_() [][]field {
	rows := make([][]field, 0, len(g.Attributes))
	for _, a := range g.Attributes {
		rows = append(rows, []field{fIntV(a.ID), fn_i32_(g, a.SymbolID), fIntV(a.FileID),
			fn_st_(g, a.Name), fn_st_(g, a.Args), fIntV(a.Line)})
	}
	return rows
}

func (g *Graph) fn_literalRows_() [][]field {
	rows := make([][]field, 0, len(g.Literals))
	for _, l := range g.Literals {
		rows = append(rows, []field{fIntV(l.ID), fn_i32_(g, l.SymbolID), fIntV(l.FileID),
			fn_st_(g, l.Kind), fn_st_(g, l.Value), fIntV(l.Line), fIntV(l.IsMagic)})
	}
	return rows
}

func (g *Graph) fn_enumRows_() [][]field {
	rows := make([][]field, 0, len(g.EnumMembers))
	for _, e := range g.EnumMembers {
		rows = append(rows, []field{fIntV(e.SymbolID), fIntV(e.Ordinal),
			fn_st_(g, e.Name), fn_st_(g, e.Value), fIntV(e.NFields)})
	}
	return rows
}

func (g *Graph) fn_markerRows_() [][]field {
	rows := make([][]field, 0, len(g.Markers))
	for _, m := range g.Markers {
		rows = append(rows, []field{fIntV(m.ID), fIntV(m.FileID), fn_i32_(g, m.SymbolID),
			fn_st_(g, m.Kind), fIntV(m.Line), fn_st_(g, m.Text)})
	}
	return rows
}

func (g *Graph) fn_classRows_() [][]field {
	rows := make([][]field, 0, len(g.Classes))
	for _, c := range g.Classes {
		rows = append(rows, []field{fIntV(c.SymbolID), fIntV(c.NBases), fn_st_(g, c.Bases),
			fIntV(c.NMethods), fIntV(c.NClassVars), fIntV(c.NProperties),
			fIntV(c.NAbstractM), fIntV(c.NDunder), fIntV(c.HasSlots),
			fIntV(c.HasInit), fIntV(c.HasEq), fIntV(c.HasHash),
			fIntV(c.IsDataclass), fIntV(c.IsABC), fIntV(c.IsEnum),
			fIntV(c.IsException), fIntV(c.IsProtocol), fIntV(c.IsNamedTuple),
			fIntV(c.IsTypedDict), fIntV(c.IsPydantic), fIntV(c.IsDjangoModel),
			fIntV(c.IsMetaclass)})
	}
	return rows
}

func (g *Graph) fn_handlerRows_() [][]field {
	rows := make([][]field, 0, len(g.Handlers))
	for _, h := range g.Handlers {
		rows = append(rows, []field{fIntV(h.ID), fIntV(h.SymbolID), fIntV(h.Line),
			fn_st_(g, h.Types), fIntV(h.IsBare), fIntV(h.IsBroad), fIntV(h.IsEmpty),
			fIntV(h.HasReraise), fIntV(h.HasLog), fIntV(h.NBodyLines),
			fIntV(h.InLoop), fIntV(h.HasRaiseNoFrom)})
	}
	return rows
}

func (g *Graph) fn_dynamicRows_() [][]field {
	rows := make([][]field, 0, len(g.DynamicSites))
	for _, d := range g.DynamicSites {
		rows = append(rows, []field{fIntV(d.ID), fn_i32_(g, d.SymbolID), fIntV(d.FileID),
			fn_st_(g, d.Kind), fn_st_(g, d.Expr), fIntV(d.Line), fIntV(d.IsLiteralArg)})
	}
	return rows
}

func (g *Graph) fn_compRows_() [][]field {
	rows := make([][]field, 0, len(g.Comprehens))
	for _, c := range g.Comprehens {
		rows = append(rows, []field{fIntV(c.ID), fn_i32_(g, c.SymbolID), fIntV(c.FileID),
			fn_st_(g, c.Kind), fIntV(c.Line), fIntV(c.NGenerator), fIntV(c.NIfs),
			fIntV(c.IsAsync), fIntV(c.InLoop)})
	}
	return rows
}

func (g *Graph) fn_moduleVarRows_() [][]field {
	rows := make([][]field, 0, len(g.ModuleVars))
	for _, v := range g.ModuleVars {
		rows = append(rows, []field{fIntV(v.ID), fIntV(v.FileID), fn_i32_(g, v.ModuleID),
			fn_st_(g, v.Name), fIntV(v.Line), fn_st_(g, v.Type), fIntV(v.IsConstant),
			fIntV(v.IsMutableContainer), fIntV(v.IsPrivate), fIntV(v.HasCallInit)})
	}
	return rows
}

func (g *Graph) fn_allExportRows_() [][]field {
	rows := make([][]field, 0, len(g.AllExports))
	for _, a := range g.AllExports {
		rows = append(rows, []field{fIntV(a.ID), fIntV(a.FileID), fn_st_(g, a.Name), fIntV(a.Line)})
	}
	return rows
}

func (g *Graph) fn_inputRows_() [][]field {
	rows := make([][]field, 0, len(g.InputSites))
	for _, u := range g.InputSites {
		rows = append(rows, []field{fIntV(u.ID), fn_i32_(g, u.SymbolID), fIntV(u.FileID),
			fn_st_(g, u.Var), fn_st_(g, u.Kind), fIntV(u.Line), fIntV(u.InLoop)})
	}
	return rows
}

func (g *Graph) fn_secretRows_() [][]field {
	rows := make([][]field, 0, len(g.Secrets))
	for _, s := range g.Secrets {
		rows = append(rows, []field{fIntV(s.ID), fn_i32_(g, s.SymbolID), fIntV(s.FileID),
			fn_st_(g, s.Value), fIntV(s.Line)})
	}
	return rows
}

func (g *Graph) fn_apiRows_() [][]field {
	rows := make([][]field, 0, len(g.APISites))
	for _, a := range g.APISites {
		rows = append(rows, []field{fIntV(a.ID), fn_i32_(g, a.SymbolID), fIntV(a.FileID),
			fn_st_(g, a.Kind), fn_st_(g, a.Expr), fIntV(a.Line), fIntV(a.IsLiteralArg)})
	}
	return rows
}

func (g *Graph) report() {
	printfLn("\n%s", strings.Repeat("=", 78))
	printfLn("OVERVIEW")
	printfLn("%s", strings.Repeat("-", 78))
	meta := map[string]string{}
	for _, kv := range g.Meta {
		meta[g.S(kv[0])] = g.S(kv[1])
	}
	for _, k := range []string{"lang", "target", "parser", "root", "built_at"} {
		if v := meta[k]; v != "" {
			printfLn(" %-14s %s", k, v)
		}
	}
	files := len(g.Files)
	parsed := 0
	var sloc int32
	for i := range g.Files {
		if g.Files[i].Parsed == 1 {
			parsed++
			sloc += g.Files[i].SLOC
		}
	}
	printfLn(" %-14s %d catalogued, %d parsed, %d sloc", "files", files, parsed, sloc)
	byKind := map[string]int{}
	for i := range g.Symbols {
		byKind[g.S(g.Symbols[i].Kind)]++
	}
	var kinds []string
	for k := range byKind {
		kinds = append(kinds, k)
	}
	sortStringsDesc(kinds, byKind)
	var kb strings.Builder
	for i, k := range kinds {
		if i >= 12 {
			break
		}
		if i > 0 {
			kb.WriteString(", ")
		}
		kb.WriteString(k + "=" + itoa32(int32(byKind[k])))
	}
	printfLn(" %-14s %s", "symbols", kb.String())
	var unres int32
	for _, u := range g.Unresolved {
		unres += u.N
	}
	var calls int32
	for i := range g.Symbols {
		calls += g.Symbols[i].NCalls
	}
	printfLn(" %-14s %d edges, %d call sites, %d unresolved", "call graph",
		len(g.Edges), len(g.Callsites), unres)

	printfLn("\n%s", strings.Repeat("=", 78))
	printfLn("HOW MUCH OF THIS TO TRUST")
	printfLn("%s", strings.Repeat("-", 78))
	errFiles := 0
	for i := range g.Files {
		if g.Files[i].ParseErrors > 0 {
			errFiles++
		}
	}
	if parsed == 0 {
		printfLn(" NOTHING WAS PARSED. Every number below is zero because no file")
		printfLn(" was read, not because this repository is empty or clean.")
	}
	printfLn(" %-30s %d file(s)", "files with parse errors", errFiles)
	if calls > 0 {
		printfLn(" %-30s %d of %d call sites (%d%%)", "calls we could NOT resolve",
			unres, calls, 100*unres/calls)
	} else {
		printfLn(" %-30s no calls were recorded at all -- this is the absence of",
			"")
		printfLn(" %-30s data, not a clean result", "")
	}
	printfLn(" A high unresolved share means the call-graph queries below see less")
	printfLn(" than they imply. `v_blindspot` lists exactly where.")

	for _, sec := range g.reportSections() {
		printfLn("\n%s", strings.Repeat("=", 78))
		printfLn("%s", sec.title)
		printfLn("%s", strings.Repeat("-", 78))
		renderRows(sec.cols, sec.rows)
	}
}

func sortStringsDesc(keys []string, m map[string]int) {
	for i := 1; i < len(keys); i++ {
		for j := i; j > 0 && m[keys[j]] > m[keys[j-1]]; j-- {
			keys[j], keys[j-1] = keys[j-1], keys[j]
		}
	}
	for i := 1; i < len(keys); i++ {
		for j := i; j > 0 && m[keys[j]] == m[keys[j-1]] && keys[j] < keys[j-1]; j-- {
			keys[j], keys[j-1] = keys[j-1], keys[j]
		}
	}
}

type section struct {
	title string
	cols  []string
	rows  [][]string
}

func (g *Graph) reportSections() []section {
	var out []section

	var modRows [][]string
	for i := range g.Modules {
		mm := &g.Modules[i]
		if mm.NFiles == 0 {
			continue
		}

		modRows = append(modRows, []string{g.S(mm.Name), num(mm.NFiles),
			num(mm.SLOC), num(mm.NSymbols), sprintf("%.2f", mm.Instability)})
	}
	sortRowsDesc(modRows, 2)
	modRows = modRows[:minI(len(modRows), 12)]
	out = append(out, section{"BIGGEST MODULES",
		[]string{"name", "files", "sloc", "syms", "instab"}, modRows})

	fnKind := func(k string) bool {
		return k == "function" || k == "method" || k == "constructor" ||
			k == "closure"
	}
	type frow struct {
		cells []string
		id    int32
	}
	var fnRows []frow
	for i := range g.Symbols {
		s := &g.Symbols[i]
		if !fnKind(g.S(s.Kind)) {
			continue
		}
		fnRows = append(fnRows, frow{[]string{g.S(s.Name), num(s.SLOC), num(s.Cyclomatic),
			num(s.Cognitive), num(s.MaxNesting), num(s.FanIn), at(g, *s)}, s.ID})
	}
	sortF := func(rows []frow, col int) {
		for i := 1; i < len(rows); i++ {
			for j := i; j > 0; j-- {
				av, _ := atoi32(rows[j].cells[col])
				bv, _ := atoi32(rows[j-1].cells[col])
				if av < bv || (av == bv && rows[j].id > rows[j-1].id) {
					break
				}
				rows[j], rows[j-1] = rows[j-1], rows[j]
			}
		}
	}
	sortF(fnRows, 2)
	if len(fnRows) > 12 {
		fnRows = fnRows[:12]
	}
	fnCells := make([][]string, len(fnRows))
	for i, fr := range fnRows {
		fnCells[i] = fr.cells
	}
	out = append(out, section{"HEAVIEST FUNCTIONS",
		[]string{"name", "sloc", "cyclo", "cog", "nest", "fan_in", "at"}, fnCells})

	var depRows []frow
	for i := range g.Symbols {
		s := &g.Symbols[i]
		if !fnKind(g.S(s.Kind)) {
			continue
		}
		depRows = append(depRows, frow{[]string{g.S(s.Name), num(s.FanIn), num(s.FanOut),
			num(s.Cyclomatic), num(s.SLOC), at(g, *s)}, s.ID})
	}
	sortF(depRows, 1)
	if len(depRows) > 12 {
		depRows = depRows[:12]
	}
	depCells := make([][]string, len(depRows))
	for i, fr := range depRows {
		depCells[i] = fr.cells
	}
	out = append(out, section{"MOST DEPENDED ON",
		[]string{"name", "fan_in", "fan_out", "cyclo", "sloc", "at"}, depCells})

	counts := map[string]int{}
	for _, m := range g.Markers {
		counts[g.S(m.Kind)]++
	}
	var mk []string
	for k := range counts {
		mk = append(mk, k)
	}
	var mkRows [][]string
	for _, k := range mk {
		mkRows = append(mkRows, []string{k, itoa32(int32(counts[k]))})
	}
	sortRowsDesc(mkRows, 1)
	out = append(out, section{"MARKERS LEFT IN THE CODE",
		[]string{"kind", "n"}, mkRows})
	return out
}

func sortRowsDesc(rows [][]string, col int) {
	for i := 1; i < len(rows); i++ {
		for j := i; j > 0 && numGreater(rows[j][col], rows[j-1][col]); j-- {
			rows[j], rows[j-1] = rows[j-1], rows[j]
		}
	}
	for i := 1; i < len(rows); i++ {
		for j := i; j > 0 && rows[j][0] < rows[j-1][0] && rows[j][col] == rows[j-1][col]; j-- {
			rows[j], rows[j-1] = rows[j-1], rows[j]
		}
	}
}

func numGreater(a, b string) bool {
	ai, erra := atoi32(a)
	bi, errb := atoi32(b)
	if erra != nil || errb != nil {
		return a > b
	}
	return ai > bi
}

func minI(a, b int) int {
	if a < b {
		return a
	}
	return b
}

const (
	fNull = iota
	fInt
	fFloat
	fStr
)

type field struct {
	kind int
	i    int64
	f    float64
	s    string
}

func fNullV() field         { return field{kind: fNull} }
func fIntV(v int32) field   { return field{kind: fInt, i: int64(v)} }
func fInt64V(v int64) field { return field{kind: fInt, i: v} }
func fFloatV(v float64) field {
	return field{kind: fFloat, f: v}
}
func fStrV(s string) field {
	if s == "" {
		return field{kind: fStr, s: ""}
	}
	return field{kind: fStr, s: s}
}

func (f field) encode() string {
	var buf []byte
	return string(f.encodeTo(buf))
}

func (f field) encodeTo(buf []byte) []byte {
	switch f.kind {
	case fNull:
		return append(buf, `\N`...)
	case fInt:
		buf = append(buf, 'i', ':')
		return strconv.AppendInt(buf, f.i, 10)
	case fFloat:
		buf = append(buf, 'f', ':')
		return append(buf, cgReprFloat(f.f)...)
	default:
		buf = append(buf, 's', ':')
		return escapeDumpTo(buf, f.s)
	}
}

func escapeDump(s string) string {
	return string(escapeDumpTo(nil, s))
}

func escapeDumpTo(b []byte, s string) []byte {
	const hexd = "0123456789ABCDEF"
	for i := 0; i < len(s); i++ {
		c := s[i]
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
				b = append(b, '\\', 'x', hexd[c>>4], hexd[c&0xF])
			} else {
				b = append(b, c)
			}
		}
	}
	return b
}

func cgReprFloat(v float64) string {
	if math.IsNaN(v) {
		return "nan"
	}
	if math.IsInf(v, 1) {
		return "inf"
	}
	if math.IsInf(v, -1) {
		return "-inf"
	}
	if v == 0 {
		if math.Signbit(v) {
			return "-0.0"
		}
		return "0.0"
	}

	s := strconv.FormatFloat(v, 'e', -1, 64)
	i := strings.IndexByte(s, 'e')
	mant, expS := s[:i], s[i+1:]
	exp, _ := strconv.Atoi(expS)
	if exp >= 16 || exp < -4 {
		if len(expS) == 2 {
			expS = expS[:1] + "0" + expS[1:]
		}
		return mant + "e" + expS
	}
	neg := ""
	if mant[0] == '-' {
		neg = "-"
		mant = mant[1:]
	}
	digits := strings.Replace(mant, ".", "", 1)
	if exp >= 0 {
		if len(digits) > exp+1 {
			return neg + digits[:exp+1] + "." + digits[exp+1:]
		}
		return neg + digits + strings.Repeat("0", exp+1-len(digits)) + ".0"
	}
	return neg + "0." + strings.Repeat("0", -exp-1) + digits
}

type dumper struct {
	w      *bufio.Writer
	err    error
	blocks []dumpBlock
}

type dumpBlock struct {
	name  string
	lines []string
}

func (d *dumper) line(s string) {
	if d.err != nil {
		return
	}
	_, d.err = d.w.WriteString(s)
	if d.err == nil {
		d.err = d.w.WriteByte('\n')
	}
}

func (d *dumper) table(name string, ncols int, rows [][]field) {
	rowsOut := make([]string, 0, len(rows))
	var buf []byte
	for _, r := range rows {
		buf = buf[:0]
		for i := range r {
			if i > 0 {
				buf = append(buf, ' ')
			}
			buf = r[i].encodeTo(buf)
		}
		rowsOut = append(rowsOut, string(buf))
	}
	sort.Strings(rowsOut)
	blk := dumpBlock{name: name, lines: make([]string, 0, len(rowsOut)+2)}
	blk.lines = append(blk.lines,
		"T "+name+" "+strconv.Itoa(ncols)+" "+strconv.Itoa(len(rowsOut)))
	for _, r := range rowsOut {
		blk.lines = append(blk.lines, "R "+r)
	}
	blk.lines = append(blk.lines, "E "+name)
	d.blocks = append(d.blocks, blk)
}

func (d *dumper) flush() {
	sort.SliceStable(d.blocks, func(i, j int) bool {
		return d.blocks[i].name < d.blocks[j].name
	})
	for _, b := range d.blocks {
		for _, l := range b.lines {
			d.line(l)
		}
	}
	d.blocks = d.blocks[:0]
}

var Queries = []question{
	{
		name:  "async-blocking",
		title: "Blocking calls inside async functions -- the event loop stops here",
		notes: "ANSWERS which coroutines stall the whole loop instead of yielding.\nACT move the call to asyncio.to_thread / run_in_executor, or use the async\n     client. One blocking call in one coroutine stalls every other task.\nMISLEADS a blocking call during startup or in a CLI path is harmless. This\n     cannot tell setup code from request code -- check what calls it.",
		run:   run_async_blocking,
	},
	{
		name:  "async-blocking-reachable",
		title: "Blocking work reachable from an async caller, up to 4 hops away",
		notes: "ANSWERS which async entry points end up blocking through a chain of plain\n     helpers that individually look innocent.\nACT the fix belongs at the boundary: wrap the whole subtree in to_thread\n     rather than chasing each leaf.\nMISLEADS depth is capped at 4 and only resolved edges are walked, so this\n     is a floor. A path through getattr dispatch does not appear at all.",
		run:   run_async_blocking_reachable,
	},
	{
		name:  "await-in-loop",
		title: "Sequential awaits: requests issued one at a time that could overlap",
		notes: "ANSWERS where latency is the SUM of N round trips instead of the max.\nACT if the iterations are independent, collect the coroutines and hand\n     them to asyncio.gather or a TaskGroup. N x 50ms becomes 50ms.\nMISLEADS some loops MUST be sequential -- pagination, rate limits, or a\n     later iteration depending on an earlier result. Read before changing.",
		run:   run_await_in_loop,
	},
	{
		name:  "mutable-defaults",
		title: "Mutable default arguments, ranked by how many callers share the object",
		notes: "ANSWERS which functions accumulate state across unrelated calls.\nACT default to None and build the container inside. The default is created\n     ONCE at def time, so every caller that omits the argument mutates the\n     same list.\nMISLEADS a mutable default that is only ever read is harmless, and a few\n     are deliberate memo caches. fan_in is the multiplier on the damage.",
		run:   run_mutable_defaults,
	},
	{
		name:  "untrusted-frontier",
		title: "Dangerous sinks and how far they sit from a public entry point",
		notes: "ANSWERS which eval/exec/pickle/shell sites an outside caller can reach.\nACT a sink 1-2 hops from a public function is where to look first. Confirm\n     the argument cannot come from outside; if it can, that is the bug.\nMISLEADS reachability is not reachedness -- the path may be guarded by an\n     auth check this cannot see. Depth capped at 5; deeper paths are missed.",
		run:   run_untrusted_frontier,
	},
	{
		name:  "sql-built-by-hand",
		title: "Queries assembled with f-strings, concatenation or .format",
		notes: "ANSWERS where a query is built by string surgery instead of parameters.\nACT pass parameters to execute() instead. Every row here is a candidate\n     injection even if today's argument happens to be a constant.\nMISLEADS interpolating a table name you control is not injection. The\n     pattern cannot tell a literal from a request field -- read the site.",
		run:   run_sql_built_by_hand,
	},
	{
		name:  "n-plus-one",
		title: "Database work inside a loop: N queries where one would do",
		notes: "ANSWERS which functions issue a query per iteration.\nACT batch it -- one IN query, a join, or select_related/prefetch_related.\n     This is the single most common cause of a slow endpoint.\nMISLEADS query_in_loop is a REGEX over string literals: any string holding\n     the word SELECT, UPDATE or DELETE FROM counts, including error\n     messages and docstrings. Corroboration with sql_calls or io is now\n     required, but a row with sql_calls=0 is still worth reading twice.\n     Trip count is invisible either way.",
		run:   run_n_plus_one,
	},
	{
		name:  "loop-multiplied",
		title: "Work done per iteration that could be hoisted out",
		notes: "ANSWERS where a constant cost is being paid N times.\nACT re.compile once outside the loop; bind len() to a local; move the\n     invariant call above the loop. Cheap, mechanical, and compounding.\nMISLEADS the interpreter does not hoist any of this, so the cost is real --\n     but if the loop runs three times, saving it is worth nothing.",
		run:   run_loop_multiplied,
	},
	{
		name:  "quadratic-strings",
		title: "String built by += inside a loop -- quadratic in the result size",
		notes: "ANSWERS which functions cost O(n^2) to build a string that could be O(n).\nACT append to a list and ''.join it once at the end.\nMISLEADS CPython special-cases some in-place concatenation when the string\n     has one reference, so the worst case does not always bite. It bites\n     reliably once the string is also read inside the loop.",
		run:   run_quadratic_strings,
	},
	{
		name:  "swallowed-errors",
		title: "except blocks that catch everything and tell nobody",
		notes: "ANSWERS where failures disappear without a trace.\nACT catch the specific exception, or log with the traceback and re-raise.\n     A bare `except: pass` on an IO path hides outages for months.\nMISLEADS some swallowing is correct -- optional cleanup, best-effort cache\n     warming. The has_log column separates silence from mere breadth.",
		run:   run_swallowed_errors,
	},
	{
		name:  "reflection-opacity",
		title: "Runtime reflection: where static reading stops working",
		notes: "ANSWERS which code decides at run time what to call.\nACT these sites are why fan_in is a lower bound everywhere else. Where the\n     argument is a literal, the call could be written out and made visible.\nMISLEADS getattr with a literal name is perfectly readable; the is_literal\n     column separates those from the genuinely dynamic ones.",
		run:   run_reflection_opacity,
	},
	{
		name:  "decorator-roots",
		title: "Functions that look dead because a decorator registers them",
		notes: "ANSWERS which zero-fan-in functions are actually framework entry points.\nACT do NOT delete these. @app.route, @task, @pytest.fixture and friends\n     call the function from somewhere no source line references.\nMISLEADS the decorator list is heuristic. A custom registering decorator\n     this does not recognise still leaves its function looking dead in\n     `dead-code` below -- cross-check before removing anything.",
		run:   run_decorator_roots,
	},
	{
		name:  "dead-code",
		title: "Nothing in this tree calls these",
		notes: "ANSWERS what might be deletable.\nACT check `decorator-roots` first, then grep for the name as a string --\n     it may be reached by getattr or named in config. Then delete.\nMISLEADS the dominant cause of a wrong row is INHERITANCE, not dynamic\n     dispatch: a subclass override reached through a base-class reference\n     has no resolvable edge, and is_override fires on only 20 of\n     Django's 41k symbols -- any method whose name also exists on a\n     parent class is suspect. Beyond that, every dynamic\n     call in `reflection-opacity` is an edge that should have been here.\n     Public API meant for outside callers is excluded, but plugins are not.",
		run:   run_dead_code,
	},
	{
		name:  "untested",
		title: "Functions no test file reaches",
		notes: "ANSWERS what is shipping without a test that touches it.\nACT weigh by fan_in and risk -- an untested function 30 callers depend on\n     is a different problem from an untested one-liner.\nMISLEADS reachability from a test only proves a test EXECUTES it, not that\n     anything is asserted. And a test reaching it via getattr is invisible,\n     so this over-reports in metaprogramming-heavy code.",
		run:   run_untested,
	},
	{
		name:  "unbounded-caches",
		title: "@lru_cache / @cache with no maxsize, and module-level mutable state",
		notes: "ANSWERS which caches can grow without limit for the life of the process.\nACT give lru_cache a maxsize. A cache keyed on anything request-derived is\n     a memory leak with extra steps, and it also pins every key alive.\nMISLEADS a cache over a small fixed key space is fine unbounded. What\n     matters is whether the KEY comes from outside, which this cannot see.",
		run:   run_unbounded_caches,
	},
	{
		name:  "shared-mutable-state",
		title: "Module-level mutable state, and who writes to it",
		notes: "ANSWERS what is shared across every caller, thread and request.\nACT under free-threading this is a data race, not a style question. Move\n     it into an object, or guard it.\nMISLEADS a module-level dict used as a read-only lookup table is fine.\n     `global` statement count is the evidence of actual writes.",
		run:   run_shared_mutable_state,
	},
	{
		name:  "import-cycles",
		title: "Modules that import each other",
		notes: "ANSWERS which import pairs are mutually dependent.\nACT a cycle forces import-time ordering hacks and function-level imports.\n     Break it by moving the shared type to a third module.\nMISLEADS this compares module names two levels deep, so a cycle inside one\n     package is invisible. `import-workarounds` is the corroborating\n     evidence that a cycle is really being worked around.",
		run:   run_import_cycles,
	},
	{
		name:  "import-workarounds",
		title: "Imports hidden inside functions -- usually a cycle being dodged",
		notes: "ANSWERS where import-time coupling was too painful to leave at the top.\nACT each of these costs a dict lookup per call and hides a real dependency\n     from every tool that reads the import block. Fix the cycle instead.\nMISLEADS a function-level import is also the correct way to make a heavy\n     optional dependency lazy. Intent is not visible from the syntax.",
		run:   run_import_workarounds,
	},
	{
		name:  "resource-discipline",
		title: "Files, sockets and connections opened outside a with-block",
		notes: "ANSWERS where a handle depends on the garbage collector to be released.\nACT use `with`. CPython's refcounting usually saves you; PyPy and the\n     free-threaded build do not, and neither does an exception mid-function.\nMISLEADS a module-level file handle deliberately kept open for the process\n     lifetime is correct and appears here. n_with is the counter-evidence.",
		run:   run_resource_discipline,
	},
	{
		name:  "weak-crypto",
		title: "md5, sha1, and the random module used where secrets belongs",
		notes: "ANSWERS which code uses a hash or RNG unfit for a security purpose.\nACT `random` is a Mersenne Twister -- predictable from ~624 outputs. Use\n     `secrets` for anything a user should not be able to guess.\nMISLEADS md5 for a cache key or a file checksum is fine, and `random` for\n     sampling or jitter is fine. Purpose is not visible from the call.",
		run:   run_weak_crypto,
	},
	{
		name:  "concurrency-surface",
		title: "Everything that spawns, locks or shares, in one place",
		notes: "ANSWERS what the free-threaded build has to be correct about.\nACT read these together with `shared-mutable-state`. A thread target that\n     touches module-level state is a race the GIL used to hide.\nMISLEADS counting a Lock says nothing about whether it is the RIGHT lock,\n     or held long enough. This finds the surface, not the bugs on it.",
		run:   run_concurrency_surface,
	},
	{
		name:  "unsafe-decode-reachable",
		title: "pickle, yaml.load and eval, and how far they sit from something that takes input",
		notes: "ANSWERS which of bandit's deserialization findings actually matter here.\n     S301 and S506 fire on every pickle and every yaml.load in the tree,\n     including the ones only a build script reaches. The question they\n     cannot answer alone is whether attacker-controlled bytes get there.\nACT work down from hops=0. A pickle.load inside a request handler is\n     remote code execution; the same call in a management command run by\n     an operator is a design smell at worst. Replace with JSON, or sign\n     the payload and verify before decoding.\nMISLEADS reachability here is the CALL graph only, so a handler that\n     dispatches through a registry, a signal, or a Celery task name looks\n     unreachable and is not. hops is a lower bound on distance, never an\n     upper bound on safety, and bandit's own false-positive rate on S301\n     comes along unchanged -- a pickle of a constant is still counted.",
		run:   run_unsafe_decode_reachable,
	},
	{
		name:  "bare-except",
		title: "Bare except: clause without an exception type (bandit E722/pylint W0702)",
		notes: "ANSWERS where a bare except: catches every exception including\n     KeyboardInterrupt and SystemExit, making the program un-killable and\n     hiding real bugs.\nACT catch Exception or a specific exception type; never bare except.\nMISLEADS a bare except that immediately re-raises is correct but rare.",
		run:   run_bare_except,
	},
	{
		name:  "pickle-deserialization",
		title: "pickle.load or pickle.loads on untrusted input (bandit S301/S302)",
		notes: "ANSWERS where pickle deserialization is used, which can execute arbitrary\n     code during deserialization. A crafted pickle stream is an RCE vector.\nACT use json, or restrict with a custom Unpickler that whitelists classes.\nMISLEADS loading a trusted internal pickle is safe. The graph sees the call\n     but not the input source.",
		run:   run_pickle_deserialization,
	},
	{
		name:  "yaml-unsafe-load",
		title: "yaml.load without SafeLoader (bandit S506)",
		notes: "ANSWERS where yaml.load is called without specifying SafeLoader, which can\n     construct arbitrary Python objects from YAML tags.\nACT use yaml.safe_load or yaml.load(stream, Loader=yaml.SafeLoader).\nMISLEADS a yaml.load that explicitly passes SafeLoader is safe; the graph\n     counts the call but does not verify the Loader argument.",
		run:   run_yaml_unsafe_load,
	},
	{
		name:  "subprocess-shell-injection",
		title: "subprocess with shell=True (bandit S602/S603)",
		notes: "ANSWERS where subprocess is called with shell=True, which passes the\n     command through the shell, enabling command injection if any part is\n     user-controlled.\nACT use shell=False and pass args as a list.\nMISLEADS shell=True with a constant string is safe. n_shell_true counts\n     shell=True sites; the graph cannot see whether args are dynamic.",
		run:   run_subprocess_shell_injection,
	},
	{
		name:  "eval-exec-injection",
		title: "eval() or exec() on dynamic input (bandit S307/pylint W0122)",
		notes: "ANSWERS where eval() or exec() is called, which executes arbitrary Python.\n     If the input is user-controlled, this is an RCE.\nACT use ast.literal_eval for literal parsing; never eval user input.\nMISLEADS eval in a test or a REPL is correct. The graph sees the call but\n     not the input source.",
		run:   run_eval_exec_injection,
	},
	{
		name:  "assert-in-production",
		title: "assert used for validation in production code (bandit B101)",
		notes: "ANSWERS where assert is used for input validation in non-test code. Running\n     Python with -O strips all asserts, so the validation disappears.\nACT raise a ValueError or TypeError instead of asserting.\nMISLEADS assert in test files is correct. The is_test filter excludes tests.",
		run:   run_assert_in_production,
	},
	{
		name:  "global-statement",
		title: "global statement in a function (pylint W0603)",
		notes: "ANSWERS where a function uses the global keyword, creating hidden mutable\n     state that makes the function non-reentrant and hard to test.\nACT pass the value as a parameter and return the new value.\nMISLEADS a global for a module-level configuration that is set once at\n     startup is a known pattern.",
		run:   run_global_statement,
	},
	{
		name:  "open-without-with",
		title: "open() without a with statement (bandit/PSS)",
		notes: "ANSWERS where open() is called without a context manager, so the file may\n     not be closed if an exception occurs between open and close.\nACT use `with open(path) as f:`.\nMISLEADS open without with that is immediately followed by try/finally is\n     correct but verbose. The graph sees n_open vs n_with but not the\n     control flow between them.",
		run:   run_open_without_with,
	},
	{
		name:  "datetime-naive",
		title: "datetime without timezone (bandit DTZ003/DTZ005)",
		notes: "ANSWERS where datetime is used without timezone awareness, causing bugs\n     when comparing or storing timestamps across time zones.\nACT use timezone-aware datetimes: datetime.now(timezone.utc).\nMISLEADS a naive datetime for local display is sometimes correct. The graph\n     counts the pattern but not the context.",
		run:   run_datetime_naive,
	},
	{
		name:  "append-in-loop-perf",
		title: "List append inside a loop without pre-allocation (perf)",
		notes: "ANSWERS where list.append is called inside a loop, causing repeated\n     reallocations as the list grows. For large loops this is slow.\nACT use a list comprehension or pre-allocate with [None]*n.\nMISLEADS a loop that appends conditionally cannot be replaced with a\n     comprehension. append_in_loop is a site count, not a size estimate.",
		run:   run_append_in_loop_perf,
	},
	{
		name:  "decorator-depth",
		title: "Functions stacked with the most decorators",
		notes: "ANSWERS which definitions carry the deepest decorator chains. Each\n     stacked decorator adds a wrapper frame on every call and a layer of\n     indirection that breakpoints and tracebacks must cross -- and a\n     decorator conference (`@login_required @rate_limit @cache`) means\n     the real body is several wrappers deep.\nACT collapse chains of pure wrappers into one composite decorator, or\n     question whether the stacking is doing three jobs that belong in\n     three places.\nMISLEADS counts rows in the attributes table per symbol, so a decorator\n     applied via `functools.wraps`-style aliasing or `apply(fn)` is\n     invisible; stacked class decorators are counted the same as stacked\n     function decorators and the semantic weight differs.",
		run:   run_decorator_depth,
	},
	{
		name:  "non-public-leak",
		title: "Calls to _private symbols from outside their module",
		notes: "ANSWERS cross-module edges whose callee name starts with underscore --\n     the private-by-convention functions other modules reach into. Each\n     row is a coupling that the author did not declare and a rename\n     without a forwarding shim will break.\nACT export the function properly (drop the underscore or add a public\n     alias) or move the caller inside the module; a `_` name is a\n     maintenance contract, not a lock.\nMISLEADS same-file calls to _private symbols are NOT leaks (they are the\n     normal internal call pattern) and are excluded; `__name`\n     name-mangled attributes and dunder-named symbols are not reported.",
		run:   run_non_public_leak,
	},
	{
		name:  "wildcard-import-rank",
		title: "Files importing with `from x import *`",
		notes: "ANSWERS the star imports that flood the importing namespace with\n     unresolvable names: nothing can say what a later `foo()` resolves\n     to, and the module's `__all__` (where it exists) is the only\n     contract. One wildcard import makes the file's symbol table opaque.\nACT replace with explicit names, or constrain the source module with a\n     proper `__all__` and check it covers everything that is used.\nMISLEADS `is_wildcard` marks the import row; the names it brings in are\n     NOT added to the alias map (by design), so every use of an\n     imported-through-star name is either unresolved or resolved by\n     global-name luck. A `__all__`-less library star-imported this way\n     reads as zero hints.",
		run:   run_wildcard_import_rank,
	},
	{
		name:  "all-reexports",
		title: "Names in __all__ that are not defined in the same file",
		notes: "ANSWERS the package entry points `__all__` promises yet defines\n     elsewhere -- the re-export surface of an __init__.py. Each row is\n     a name that is importable-from-package but whose definition lives\n     elsewhere, which makes the package's API two edits deep.\nACT keep the list explicit and short; a `__all__` entry with no\n     definition AT ALL in the tree is a dangling promise.\nMISLEADS relies on the literal-list capture of `__all__ = [...]`;\n     computed `__all__` (sorted(), set operations) has no row here, and\n     a same-file definition counted as \"defined\" means the re-export\n     half is the missing one -- the query reports exactly that half.",
		run:   run_all_reexports,
	},
	{
		name:  "relative-import-depth",
		title: "Import chains climbing packages with leading dots",
		notes: "ANSWERS which files reach across package boundaries with `from ..x`\n     chains -- the dots count one per level climbed. Deep chains couple\n     the file to the layout above it, and moving either end silently\n     severs the link.\nACT replace depth >= 2 relative imports with an absolute import from a\n     shared root, or move the shared code closer to the consumer.\nMISLEADS depth is computed from the leading-dot count in the import\n     specifier; `from . import x` (depth one, same package) is counted\n     as a chain of depth 1, which is normal and reported only as data;\n     a module that imports itself or a missing sibling looks identical\n     here.",
		run:   run_relative_import_depth,
	},
	{
		name:  "method-kind-mix",
		title: "Class methods by kind: instance vs classmethod vs staticmethod",
		notes: "ANSWERS how each class mixes method kinds. A heavy classmethod/\n     staticmethod share signals factory-style design; an instance-method\n     majority is the plain OO shape. The mix column shows the split.\nACT a class whose methods are entirely static/class-wide is probably a\n     module hiding in a class -- consider a plain function module or\n     functools.singledispatch instead.\nMISLEADS relies on is_classmethod/is_staticmethod flags derived from\n     decorator names: `@classmethod`/`@staticmethod` spellings only, so\n     a decorator alias (e.g. `import classmethod as cm`) is invisible,\n     and inherited methods are not counted per subclass.",
		run:   run_method_kind_mix,
	},
	{
		name:  "request-without-timeout",
		title: "requests/urlopen calls with no timeout (bandit S113)",
		notes: "ANSWERS functions issuing requests.get/post or urllib urlopen calls with\n     no timeout: one stalled peer hangs the caller forever, and a\n     downstream outage becomes an upstream hang.\nACT pass a timeout; wrap in a deadline at the call site.\nMISLEADS deliberately infinite streams (SSE) read as violations; the\n     counter is per-function not per-site, so fan_in approximates blast\n     radius, not call count; a wrapper around requests that threads a\n     timeout internally is invisible to the name-based capture.",
		run:   run_request_without_timeout,
	},
	{
		name:  "open-redirect-surface",
		title: "redirect() calls in functions that read request input (OWASP G26)",
		notes: "ANSWERS functions that call flask/django redirect() AND read request\n     input (request.args / request.GET / cookies / headers) -- the shape\n     of an unvalidated redirect: return redirect(request.args.get(\"next\")).\nACT validate the target against an allowlist; never forward a\n     user-supplied URL.\nMISLEADS same-function co-occurrence is NOT data flow -- the input value\n     may never reach the redirect, and a constant redirect beside an\n     unrelated input read reads as a violation. The argument text is not\n     captured, so a fixed target cannot be told from an open one; the\n     redirect capture is the bare base name (redirect/redirect_to), so a\n     wrapper around redirect is invisible to it.",
		run:   run_open_redirect_surface,
	},
	{
		name:  "ssrf-fetch-surface",
		title: "Fetch calls in functions that read request input (OWASP G27)",
		notes: "ANSWERS functions that fetch a URL (requests/httpx/urllib) AND read\n     request input -- the shape of server-side request forgery:\n     requests.get(request.args.get(\"url\")).\nACT validate the URL scheme and host against an allowlist; never fetch a\n     user-supplied URL.\nMISLEADS same-function co-occurrence is NOT data flow -- the input value\n     may never reach the fetch, and a constant URL beside an unrelated\n     input read reads as a violation. The fetch capture is the dotted\n     name only: an aiohttp session's bare s.get(...) has no dotted name\n     and is invisible; a wrapper around requests is too.",
		run:   run_ssrf_fetch_surface,
	},
	{
		name:  "hardcoded-secret-candidates",
		title: "Credential-shaped string literals (OWASP G07)",
		notes: "ANSWERS string literals at least 12 chars long whose text names a\n     credential (password, token, api_key, secret, bearer, jwt, ...) --\n     the literal that a committed secret looks like.\nACT rotate and move to a secret manager; never commit the literal.\nMISLEADS a format string or test fixture containing the WORD token/pass\n     reads as a candidate (the filter is the literal's own text, not its\n     use); values over 200 chars are truncated at capture; a secret\n     built from parts or read from an env var is invisible here.\n     This is a candidate list, not a verdict.",
		run:   run_hardcoded_secret_candidates,
	},
	{
		name:  "xxe-parser-surface",
		title: "XML parser construction sites (OWASP G13)",
		notes: "ANSWERS functions that touch the stdlib XML parsers (xml.etree, lxml,\n     xml.dom, xml.sax) -- the surface where entity expansion is decided.\nACT use defusedxml, or disable DTD/entity expansion on the parser.\nMISLEADS the parser CONFIG is not modeled: a parser with entities\n     disabled ranks the same as one without. The capture is the dotted\n     module name, so from xml.etree import ElementTree and a bare\n     fromstring() are invisible. defusedxml is deliberately absent.",
		run:   run_xxe_parser_surface,
	},
	{
		name:  "path-traversal-surface",
		title: "open() with a non-literal path in input-reading functions (OWASP G12)",
		notes: "ANSWERS functions that call open() with a variable path AND read request\n     input -- the shape of path traversal: open(request.args.get(\"f\")).\nACT validate the resolved path stays under a configured root; use\n     Path.resolve() and a prefix check.\nMISLEADS same-function co-occurrence is NOT data flow -- the input value\n     may never reach open(), and a constant-open beside an unrelated\n     input read reads as a violation. The path is not analyzed: a\n     variable path is assumed suspicious, a literal is not.\n     Path(\"x\").read_text and os.path.join shapes are invisible to the\n     bare open() capture.",
		run:   run_path_traversal_surface,
	},
	{
		name:  "unchecked-upload-surface",
		title: "request.files save() with no visible size/type check (OWASP G28)",
		notes: "ANSWERS functions that save() an uploaded file (request.files[...]) --\n     the shape of an unchecked upload: request.files['f'].save(dst).\nACT check extension, MIME and size against an allowlist before saving;\n     store outside the web root.\nMISLEADS same-function co-occurrence is NOT data flow -- the check may\n     happen elsewhere in the function or be missing entirely; the graph\n     sees the save, not the validation. A .filename read without a save\n     is not flagged; a save on a non-request object whose receiver text\n     contains 'files' is a false positive.",
		run:   run_unchecked_upload_surface,
	},
	{
		name:  "zip-slip-surface",
		title: "zipfile access sites (OWASP G29)",
		notes: "ANSWERS functions that touch zipfile (ZipFile, extractall, namelist,\n     read) -- the surface where an entry name becomes a filesystem path.\nACT validate every entry name against a containment check before\n     extraction; reject ../ and absolute paths.\nMISLEADS the containment check is not modeled: a function that checks\n     each name before extractall ranks the same as one that does not.\n     The capture is the dotted zipfile. name, so a bare ZipFile import\n     alias is invisible.",
		run:   run_zip_slip_surface,
	},
	{
		name:  "log-injection-surface",
		title: "Logging calls in functions that read request input (OWASP G14)",
		notes: "ANSWERS functions that call a logging level method (logging.info,\n     logger.error, ...) AND read request input -- the shape of log\n     forging: logger.info(request.headers.get(\"User-Agent\")).\nACT sanitize newlines and control characters in log messages; never log\n     raw request input.\nMISLEADS same-function co-occurrence is NOT data flow -- the input value\n     may never reach the log call, and a constant message beside an\n     unrelated input read reads as a violation. The capture needs\n     'logging' or 'logger' in the dotted call name, so a bare\n     getLogger().info(...) chain and a different-named logger are\n     invisible.",
		run:   run_log_injection_surface,
	},
	{
		name:  "unauthenticated-input-surface",
		title: "Request input read with no auth call in the function (OWASP G01)",
		notes: "ANSWERS functions that read request input and contain NO auth-family\n     call (login_required, is_authenticated, current_user, session.get,\n     jwt, token) -- the surface where a request handler may be missing\n     its authorization check.\nACT add the auth/decorator check; verify the endpoint is in the\n     protected route group.\nMISLEADS auth may live on a DECORATOR, a base view class, or a\n     middleware -- decorators ARE visible (attributes table) and exclude\n     a symbol; a base-class or middleware check still reads as open. A\n     login or registration endpoint legitimately has no auth. The\n     markers are name-based substrings, so a helper wrapping the auth\n     call is invisible and counts as open.",
		run:   run_unauthenticated_input_surface,
	},
	{
		name:  "exception-in-loop",
		title: "try/except inside loop bodies (perflint PERF203)",
		notes: "ANSWERS handlers inside loop bodies: handler bookkeeping per iteration,\n     usually validation that belongs outside the loop.\nACT hoist the try, or prove the except is the loop's retry idiom.\nMISLEADS retry loops and break-on-success are the CORRECT form and will\n     rank here; is_broad + n_body_lines is the smell heuristic, not a\n     verdict; is_bare names the bare-except shape, which is a separate\n     (pre-existing) finding family.",
		run:   run_exception_in_loop,
	},
	{
		name:  "call-in-default-argument",
		title: "Defaults that are CALLS, evaluated once at def time (flake8-bugbear B008)",
		notes: "ANSWERS defaults that call a function: evaluated ONCE when the def runs\n     and shared by every caller. time.time() freezes at import; a\n     get_config() result is baked in; an object factory gives every call\n     the SAME instance.\nACT default None, compute inside the body.\nMISLEADS mutable-defaults owns []/{}/set(); this owns the call form. An\n     immutable-typed call default (e.g. `t=time.time()`) is benign in\n     practice but still shared, so it reads as a violation here.",
		run:   run_call_in_default_argument,
	},
	{
		name:  "name-shadowing",
		title: "Parameters, locals and module vars named after builtins",
		notes: "ANSWERS names that shadow a builtin -- `def f(len)`, `id = 5` at module\n     scope, a local named `type`. The shadow is invisible until the\n     shadowing name is removed or the builtin is called after the\n     assignment, and it blocks static checkers that follow the builtin.\nACT rename the parameter/local; a module var that shadows a builtin is\n     the worst form -- it taints every file that imports it.\nMISLEADS the builtin list is inline and conservative -- names that are\n     builtins on some platforms (e.g. `exec` always, `input` always) but\n     absent here are missed; shadowing a builtin you never call and\n     never re-export is harmless and still reported.",
		run:   run_name_shadowing,
	},
	{
		name:  "undocumented-export",
		title: "Public functions and classes with no docstring, by fan-in",
		notes: "ANSWERS the public API surface that says nothing about itself: no\n     docstring, no comment the analyzer can see, and callers inside the\n     tree to care about. The most-called undocumented symbol is where a\n     docstring pays off first.\nACT add a docstring; the row's fan_in is the number of callers who had\n     to read the code instead.\nMISLEADS Python has no is_exported signal, so is_public (not starting\n     with `_`) is the proxy and a module-private-ish public name slips\n     through; has_doc is a docstring/comment prefix scan, so a comment\n     above the def counts; dead symbols (fan_in 0) are excluded because\n     `dead-code` owns them.",
		run:   run_undocumented_export,
	},
	{
		name:  "closure-in-loop",
		title: "Lambdas and nested defs inside loop bodies (flake8-bugbear B023)",
		notes: "ANSWERS closures created inside loops: a lambda that references the\n     loop variable captures its FINAL value, so every call sees the\n     last iteration unless the value is bound early.\nACT bind the value as a default argument (`lambda x=x: ...`) or move\n     the closure creation out of the loop.\nMISLEADS the capture is positional (any lambda/def in a loop): a\n     closure that never references the loop variable is benign and\n     still counted; a def whose body ignores the loop var is the same;     list-comprehension closures are separate comprehension scopes and     are not counted.",
		run:   run_closure_in_loop,
	},
	{
		name:  "raise-without-from",
		title: "New exceptions raised from handlers without `from` (pylint W0707)",
		notes: "ANSWERS handlers that raise a NEW exception with no `from`: the\n     original exception's traceback is lost, so the root cause chain\n     breaks at exactly the translation layer where it matters most.\nACT add `from e` (or `from None` if the cause is deliberately hidden).\nMISLEADS a bare `raise` (re-raise) and `raise e` (the caught name)\n     preserve context and are correctly absent; `raise X() from None`\n     is a deliberate hiding and reads as clean; the flag is per-\n     handler, so a handler that raises WITH from elsewhere still\n     appears if any raise in it lacks the from.",
		run:   run_raise_without_from,
	},
	{
		name:  "suppression-burden",
		title: "Files drowning in # noqa / # type: ignore vs their TODO debt",
		notes: "ANSWERS files with more suppression directives than TODO markers: the\n     file has outgrown its linter. Suppressions without comments are\n     the audit gap -- someone silenced the check and moved on.\nACT fix or document the suppressed violations; a suppression with a\n     reason is half the problem solved.\nMISLEADS suppression text is not inspected beyond the directive kind:\n     `# noqa: F401` (scoped) counts the same as bare `# noqa`;\n     vendored or generated files are excluded by is_generated; the\n     ratio is per-file, so a small file with one noqa outranks a big\n     one with ten.",
		run:   run_suppression_burden,
	},
	{
		name:  "broad-test-expectation",
		title: "pytest.raises(Exception) -- a test that cannot fail (flake8-bugbear B017)",
		notes: "ANSWERS pytest.raises calls whose argument is the broad Exception or\n     BaseException: the test passes when ANY error is raised, which is\n     how a broken assertion hides for months.\nACT name the specific exception the code path is expected to raise.\nMISLEADS the capture is the literal first argument only: a variable\n     holding Exception (`exc = Exception`) or a tuple of exceptions\n     containing the broad ones is not distinguished; a test that\n     genuinely expects any failure (a fuzz-style guard) is the\n     legitimate row.",
		run:   run_broad_test_expectation,
	},
	{
		name:  "template-injection",
		title: "Jinja environments with autoescape disabled (bandit S701)",
		notes: "ANSWERS every Environment(autoescape=False): rendered user input is\n     emitted unescaped, which is stored/server XSS whenever the data\n     crosses to a browser.\nACT enable autoescape (it is the default in modern Jinja), or escape\n     at the sink with the template's own filter.\nMISLEADS text-matched on the keyword argument: `autoescape=False` set\n     via a variable or a wrapper around Environment is invisible;\n     a template used only for email (HTML escaping irrelevant) is the\n     legitimate row; `select_autoescape` policies are not read.",
		run:   run_template_injection,
	},
	{
		name:  "orm-query-in-loop",
		title: "Queryset reads inside a loop: the ORM N+1 (Django/SQLAlchemy perf docs)",
		notes: "ANSWERS where an ORM query fires per loop iteration -- .get/.filter/\n     .count on a manager or queryset inside a loop body. One query per\n     item is the classic N+1; the docs' fix is select_related or\n     prefetch_related, or one batched IN query before the loop.\nACT hoist the query out of the loop, batch it with an IN clause, or\n     eager-load the relation the body is walking.\nMISLEADS the capture is the method NAME, not the receiver type, so a\n     .count() on a list ranks beside a real queryset call; loop trip\n     count is invisible, and a get() over a two-element constant is a\n     true row that is not worth changing.",
		run:   run_orm_query_in_loop,
	},
	{
		name:  "commit-in-loop",
		title: ".commit() inside a loop: one transaction per item (SQLAlchemy session docs)",
		notes: "ANSWERS where the unit of work is a single row: a commit per iteration\n     commits N times, flushes N times, and leaves the batch half-applied\n     when the loop dies mid-way. The session docs' unit-of-work shape is\n     one transaction around the batch.\nACT open one transaction around the loop, or replace the per-row work\n     with a bulk insert/update.\nMISLEADS a deliberate commit-per-item as an incremental-progress\n     checkpoint (long ETL) is correct and ranks here; the counter sees\n     .commit() spelled on any receiver, including non-SQL objects with\n     a commit verb.",
		run:   run_commit_in_loop,
	},
	{
		name:  "multi-write-no-atomic",
		title: "Multiple ORM writes with no transaction.atomic in sight (Django transactions doc)",
		notes: "ANSWERS functions performing two or more ORM writes with no atomic block\n     or decorator: a failure between the writes leaves the datastore\n     half-mutated and every concurrent reader sees the intermediate\n     state.\nACT wrap the write sequence in `with transaction.atomic():` (or decorate\n     with @atomic) so the pair commits or rolls back together.\nMISLEADS the writes may target backends one atomic cannot cover, or sit\n     in a helper its caller already wraps -- this reads one body only;\n     any object with a save()/create() verb counts, so a non-ORM pair\n     of writes ranks the same.",
		run:   run_multi_write_no_atomic,
	},
	{
		name:  "celery-task-sync-call",
		title: "Celery task called as a plain function -- the queue is bypassed (Celery calling-tasks doc)",
		notes: "ANSWERS task-decorated functions that other in-tree code calls directly.\n     The calling-tasks doc is explicit: a direct call executes the task\n     in the CURRENT process and no message is sent -- retries, routing,\n     and ack semantics silently disappear.\nACT call task.delay() or task.apply_async() at the call site.\nMISLEADS fan_in counts RESOLVED call sites: `t.delay()` produces a name\n     the resolver cannot pin to the task, so queue use is invisible and\n     a row here can still be a false alarm; eager mode and Celery's own\n     test utilities call tasks synchronously on purpose.",
		run:   run_celery_task_sync_call,
	},
	{
		name:  "celery-task-reliability",
		title: "Task with no acks_late and no time limits (Celery task docs)",
		notes: "ANSWERS tasks whose decorator sets neither acks_late nor a time limit:\n     the default acks-early loses the task if the worker dies mid-run,\n     and an unbounded task can pin a worker slot forever.\nACT set time_limit/soft_time_limit on every task; add acks_late=True\n     only for tasks you have made idempotent.\nMISLEADS idempotency is not modelled -- acks_late on a non-idempotent\n     task is WORSE than the default; options inherited from a shared\n     base task class or app-level config are invisible to the decorator\n     text this reads.",
		run:   run_celery_task_reliability,
	},
	{
		name:  "lock-across-await",
		title: "Await while a sync with-block is open -- the lock is held across the suspension (clippy await_holding_lock analogue)",
		notes: "ANSWERS async functions that await inside a SYNCHRONOUS with-block: the\n     blocking context manager is not released by the await, so every\n     other task waiting on that lock (or file) stalls for the whole\n     suspension -- a self-inflicted event-loop deadlock candidate.\nACT use `async with` on an asyncio-compatible lock, or release before\n     awaiting; narrow the critical section so no await sits inside it.\nMISLEADS a sync with over a FILE or plain object that also awaits is\n     ordinary and safe -- only lock-like context managers are the\n     hazard, the row is per-FUNCTION not per with/await pair, and\n     n_concurrency is the corroborating signal, not proof.",
		run:   run_lock_across_await,
	},
	{
		name:  "thread-target-shared-state",
		title: "threading.Thread(target=...) aimed at code that writes shared state",
		notes: "ANSWERS spawn sites whose target function uses global/nonlocal writes:\n     under the free-threaded build that is a data race the GIL used to\n     hide, and even with a GIL the target's writes interleave with the\n     spawner in untracked order.\nACT pass state in explicitly and return results via a Queue or future;\n     guard genuinely shared objects with a lock and say which one.\nMISLEADS resolution of the bare target name picks EVERY same-name\n     function (the defs column shows the ambiguity) and a target that\n     only READS a module global is fine; started/joined/daemon state is\n     not modelled at all.",
		run:   run_thread_target_shared_state,
	},
	{
		name:  "import-monkeypatch",
		title: "Module-level attribute assignment: monkey-patching at import time",
		notes: "ANSWERS module-scope statements that assign into a dotted target (os.cwd\n     = spy, SomeClass.method = patch): the patch applies to every\n     importer in the process, in import order, before any caller or\n     test can opt out.\nACT move the patch behind a function, a fixture, or an explicit setup\n     call so the mutation has an owner and an order you can see.\nMISLEADS a compatibility shim under try/except ImportError is the\n     legitimate row; only literal `a.b = ...` targets are captured, so\n     patching via setattr is invisible, and a module assigning its OWN\n     name's attribute is not distinguished from reaching into another.",
		run:   run_import_monkeypatch,
	},
	{
		name:  "settings-mutation-import",
		title: "settings.* written at import time (Django settings docs)",
		notes: "ANSWERS module-scope writes like settings.DEBUG = True: Django reads\n     settings lazily at use time, so import-order decides whether the\n     mutation sticks -- an ordering no reader of this file can see.\nACT configure through settings modules or environment before Django\n     reads them; in tests use override_settings, never a module-level\n     write.\nMISLEADS only literal `...settings.<attr> =` targets are captured (an\n     alias, or getattr(settings, name, value), is invisible); a staging\n     or CI settings module that exists to mutate settings is the\n     legitimate row.",
		run:   run_settings_mutation_import,
	},
	{
		name:  "import-time-side-effects",
		title: "Work done at import time: I/O, network, subprocess or open() at module scope",
		notes: "ANSWERS modules that read files, touch the network, shell out or open a\n     handle as a side effect of being imported -- cold-start cost for\n     every consumer, and a failure there surfaces as a bare ImportError\n     far from the cause.\nACT defer to first use (lazy import or a getter), or make the startup\n     dependency explicit and fail loudly in one place.\nMISLEADS a constant table built from a small bundled file is a\n     legitimate row; the <module> symbol aggregates the whole top level\n     of the file, so one guarded or commented call ranks the module the\n     same as an unguarded one.",
		run:   run_import_time_side_effects,
	},
	{
		name:  "membership-scan-in-loop",
		title: "`x in container` inside a loop: O(n) scan per iteration (flake8-perf family)",
		notes: "ANSWERS membership tests against a variable container inside a loop\n     body: each test walks the container, so a loop over n items costs\n     O(n^2) whenever the container is a list.\nACT build a set (or dict) once before the loop and test membership on\n     that; hoist the container if it is rebuilt per iteration.\nMISLEADS the container's TYPE is not known: a membership test over a\n     set or frozenset is already O(1) and ranks identically, and `in`\n     over a small constant list is cheap in practice -- read the\n     container's construction before acting.",
		run:   run_membership_scan_in_loop,
	},
	{
		name:  "resource-return-escape",
		title: "open()/connect() result returned to the caller -- the handle escapes",
		notes: "ANSWERS functions that hand a freshly opened file, socket, session or\n     cursor to their caller with no context manager guarding it: every\n     caller now owns closing it, and one missed close leaks the handle\n     per call.\nACT return a path or a factory, or wrap in @contextmanager and yield\n     the handle inside a with-block so cleanup is the function's job.\nMISLEADS a function whose contract IS to hand back a handle for the\n     caller's `with` (an open_config() helper) is the legitimate row;\n     handles stored on self or globals instead of returned are\n     invisible, and the caller may close it diligently every time.",
		run:   run_resource_return_escape,
	},
	{
		name:  "taint-frontier-input",
		title: "Dangerous sinks reachable from request-input readers, with hop distance",
		notes: "ANSWERS which subprocess/shell/eval/pickle/mark_safe sinks sit within 4\n     resolved calls of a function that reads request input -- the\n     cross-function half of command injection, XSS and\n     deserialization, beyond same-function co-occurrence.\nACT start at hops=0 and walk outward; confirm the argument path carries\n     the input before treating a row as a finding.\nMISLEADS reachability is NOT data flow -- the input value may never\n     reach the sink's argument; depth is capped at 4 over RESOLVED\n     edges so getattr dispatch and framework routing hide paths (a\n     floor, never proof of safety); a validated sink beside an input\n     reader still ranks.",
		run:   run_taint_frontier_input,
	},
	{
		name:  "mark-safe-surface",
		title: "mark_safe() in functions that read request input (Django docs / Semgrep)",
		notes: "ANSWERS same-function co-occurrence of mark_safe (or a .mark_safe\n     method) with request-input reads -- the stored-XSS shape: the\n     string is declared HTML-trusted in the same body that reads\n     untrusted data.\nACT escape at the template boundary instead; if the HTML genuinely must\n     be trusted, sanitize it (bleach/nh3) and leave a comment saying\n     why the marking is safe.\nMISLEADS co-occurrence is NOT data flow -- the marked string may never\n     contain the input; mark_safe on a constant built beside an\n     unrelated request read ranks the same, and reachability from a\n     handler through helpers is covered by taint-frontier-input.",
		run:   run_mark_safe_surface,
	},
	{
		name:  "mass-assignment-surface",
		title: "**request.<form/json/args> splatted into a call (OWASP mass assignment)",
		notes: "ANSWERS calls that unpack a request-derived mapping into keyword\n     arguments -- Model(**request.form) or obj.update(**request.json):\n     every field the client sends becomes an attribute, including the\n     ones that were never meant to be client-settable (is_admin).\nACT bind fields explicitly, or route through a schema allowlist (Django\n     ModelForm.fields, marshmallow only=..., pydantic models).\nMISLEADS the capture is a ** keyword whose text mentions `request` -- a\n     pre-filtered dict named request_fields still ranks; a splat into\n     an allowlisting .update() is not distinguished from the raw model\n     constructor, and there is no data flow, only shape.",
		run:   run_mass_assignment_surface,
	},
	{
		name:  "ssti-surface",
		title: "render_template_string() calls: server-side template injection surface (CWE-1336)",
		notes: "ANSWERS templates constructed from runtime strings: a template argument\n     that is not a constant can carry user data into the Jinja compiler,\n     where {{ }} and {% %} become executable server-side -- full RCE\n     in the classic SSTI case.\nACT render a static template and pass data as context; never render a\n     string an outside party can influence.\nMISLEADS is_literal_arg=0 only means the argument is not a string\n     CONSTANT -- a template loaded from trusted config still ranks;\n     literal rows are included as near-misses for contrast; Markup/\n     render_template(**context) abuse is a different sink and is not\n     captured.",
		run:   run_ssti_surface,
	},
	{
		name:  "session-created-per-call",
		title: "Session()/sessionmaker() built inside functions (SQLAlchemy session-per-request)",
		notes: "ANSWERS functions that construct a Session themselves instead of\n     receiving the request-scoped one: N callers means N independent\n     transactions and identity maps, and objects cached in one session\n     go stale in another.\nACT create one session per request in framework setup and pass it down\n     (or use the scoped_session registry); scripts may keep one session\n     per unit of work deliberately.\nMISLEADS the capture is the constructor NAME, so a project wrapper\n     named Session is invisible while an unrelated class named Session\n     ranks; fan_in approximates how many call paths open their own\n     session, not how often it happens at runtime.",
		run:   run_session_created_per_call,
	},
	{
		name:  "tls-verify-disabled",
		title: "verify=False on an HTTP client call (bandit S501 / ruff S501)",
		notes: "ANSWERS requests/httpx calls with TLS certificate verification\n     explicitly disabled: the channel is encrypted but the peer is\n     unauthenticated, which is exactly the gap a MITM needs.\nACT remove verify=False; for a self-signed host, pin its CA with\n     verify=\"/path/to/ca.pem\" instead of turning verification off.\nMISLEADS test-suite calls are the legitimate rows (and is_test\n     excludes the test trees), but a staging-only default of False\n     still ranks; session-level or environment-driven verification\n     settings are invisible to the per-call capture.",
		run:   run_tls_verify_disabled,
	},
	{
		name:  "test-only-callers",
		title: "Production functions whose only callers are test files",
		notes: "ANSWERS functions every resolved caller of which lives in a test tree:\n     nothing in production reaches them, so they are either dead weight\n     shipping in the artifact or public API consumed outside the tree.\nACT grep external usage and docs before deleting; if internal-only,\n     delete or move beside its tests.\nMISLEADS resolution is name-based -- dynamic dispatch, decorators and\n     entry points have no resolved edges, so a genuinely-live function\n     can read as test-only (cross-check decorator-roots and dead-code);\n     a production caller reached only via getattr is invisible.",
		run:   run_test_only_callers,
	},
	{
		name:  "mutable-class-attribute",
		title: "Mutable class attribute without ClassVar -- shared by every instance (bugbear/RUF012)",
		notes: "ANSWERS class-level list/dict/set initializers that every instance\n     shares: one instance's .append is every instance's .append, and\n     the class object outlives them all -- cross-instance state by\n     accident.\nACT annotate with ClassVar if the sharing is deliberate, otherwise\n     initialize in __init__ so each instance gets its own.\nMISLEADS is_mutable is captured from the VALUE shape only (a literal\n     list/dict/set initializer), so an attribute assigned via a call is\n     invisible; deliberately shared registries are the legitimate rows\n     and instantiations only rank them, they do not prove mutation.",
		run:   run_mutable_class_attribute,
	},
	{
		name:  "global-write-reachable",
		title: "Global-variable writers reachable from public entry points",
		notes: "ANSWERS functions that execute global writes and how far they sit from a\n     public function: the write is not a local quirk but a step on a\n     path any caller can trigger -- and two callers can trigger it\n     concurrently.\nACT contain the state in an object or pass it through signatures; guard\n     what must stay global and name the lock in a comment.\nMISLEADS reachability walks RESOLVED edges only with depth capped at 4,\n     so getattr dispatch hides paths; a global set once as an idempotent\n     init guard is the legitimate row, and public_reach counts public\n     functions on the path, not call frequency.",
		run:   run_global_write_reachable,
	},
	{
		name:  "prod-imports-test",
		title: "Production code importing from the test tree",
		notes: "ANSWERS non-test files whose imports resolve into a test file: helpers\n     and fixtures leaked into the shipping import graph, and packaging\n     the tests out of the artifact will break the build.\nACT move the shared helper into a non-test module and import it from\n     both sides; keep tests importing production code, never the\n     reverse.\nMISLEADS resolution is path-based, so a same-named non-test module\n     elsewhere wins silently and a true hit can be missed; is_test is\n     name/pattern based (test_ prefix, tests directory), so a\n     prod-named file living under tests/ reads as a violation here.",
		run:   run_prod_imports_test,
	},
	{
		name:  "dict-get-in-loop",
		title: ".get() inside a loop body (ruff PERF family)",
		notes: "ANSWERS functions calling .get() inside loop bodies: when the same key\n     is probed every iteration, the lookup and its default construction\n     can be hoisted or folded into one merge before the loop.\nACT hoist the lookup, or restructure into a single dict merge /\n     setdefault pass ahead of the loop.\nMISLEADS probing a DIFFERENT key per iteration is the correct form and\n     dominates real code -- this counts sites, not repeated-key cost;\n     .get on non-dict receivers ranks identically because the receiver\n     type is not known.",
		run:   run_dict_get_in_loop,
	},
	{
		name:  "format-in-loop",
		title: ".format() inside a loop body (ruff PERF family)",
		notes: "ANSWERS str.format calls inside loop bodies: the template is re-parsed\n     and the result re-allocated on every iteration, which compounds\n     with the loop count and with quadratic-strings when the result\n     feeds a running total.\nACT hoist the template, use an f-string once per iteration only when\n     needed, or join the pieces once after the loop.\nMISLEADS formatting a DIFFERENT value per iteration is often the point\n     of the loop -- the site count says nothing about how hot the loop\n     is; a .format on a non-string receiver ranks identically.",
		run:   run_format_in_loop,
	},
	{
		name:  "loop-else",
		title: "for/while with an else clause (pylint W0120 shape)",
		notes: "ANSWERS loop-else constructs: the else runs when the loop ends without\n     break, a control path most readers do not know exists and most\n     reviewers misread on first pass.\nACT replace with a found-flag or an early return; keep the else only\n     where the no-break semantics are the point and say so in a\n     comment.\nMISLEADS this reads the SHAPE only: an else correctly paired with a\n     break (a search loop) is the legitimate form and cannot be\n     distinguished from an else nobody reasoned about, because break\n     placement is not captured.",
		run:   run_loop_else,
	},
	{
		name:  "print-statement-shipping",
		title: "print() in public non-test code",
		notes: "ANSWERS public functions that write to stdout outside tests: print\n     bypasses log levels, interleaves under concurrency, and in a WSGI\n     worker can crash on a closed stdout.\nACT switch to logging with a level, or guard deliberate CLI output\n     behind the argument parser's contract.\nMISLEADS a CLI tool whose contract IS stdout is the legitimate row and\n     this cannot tell it from debug residue; is_public-based filtering\n     means a private helper printing on behalf of a CLI still hides,\n     and fan_in ranks blast radius, not print frequency.",
		run:   run_print_statement_shipping,
	},
	{
		name:  "insecure-tempfile",
		title: "tempfile.mktemp -- predictable temp name (bandit S306)",
		notes: "ANSWERS insecure temp-FILE NAME generation: mktemp returns a path\n     another process can create first (a symlink attack), and whatever\n     appears there is opened with this process's rights.\nACT use NamedTemporaryFile, TemporaryDirectory or mkstemp -- name and\n     fd are allocated atomically; never mktemp then open.\nMISLEADS a mktemp call in a single-user build script is low risk but\n     ranks the same; only the mktemp family is captured, so\n     NamedTemporaryFile(delete=False) followed by a reopen (a real\n     race) is invisible.",
		run:   run_insecure_tempfile,
	},
	{
		name:  "unused-public-api",
		title: "Public functions nothing in the tree calls -- exported API nobody uses",
		notes: "ANSWERS public functions with zero resolved in-tree callers and no\n     decorator: dead code wearing a public name, or API consumed\n     outside the tree -- the ambiguity `dead-code` sidesteps by\n     excluding public symbols.\nACT check external consumers and docs first; if internal-only, delete\n     it or fold it into its only caller.\nMISLEADS entry points, getattr dispatch and __all__ re-exports have no\n     resolved edges -- cross-check decorator-roots and all-reexports\n     before deleting; a method invoked only through a base-class\n     reference also reads as unused here.",
		run:   run_unused_public_api,
	},
}

var Metrics = []question{
	{
		name:  "graph-blindspots",
		title: "Read this first: where the call graph cannot see",
		notes: "ANSWERS how much of every other answer here is guesswork.\nACT if a module is high on this list, treat its reachability results as a\n     lower bound. getattr and importlib dispatch are invisible to a reader.\nMISLEADS a resolved call can still be wrong -- name-based resolution picks\n     the unique definition of a name, and two classes with the same method\n     name are refused rather than guessed, landing here instead.",
		run:   run_graph_blindspots,
	},
	{
		name:  "risk-ranked",
		title: "Review order: if you can only read N functions this week, which N",
		notes: "ANSWERS which functions combine complexity with dangerous operations.\nACT start at the top. The score weights exec/deserialize/SQL-building far\n     above raw complexity, because a simple function that evals is worse\n     than a complicated one that does arithmetic.\nMISLEADS it is a heuristic, not a finding. A high score means 'look', not\n     'bug'. Generated and vendored files are excluded, so the real top of\n     the list may sit in code this filter hid.",
		run:   run_risk_ranked,
	},
	{
		name:  "hot-multipliers",
		title: "Where one fix pays back many times: highest fan-in",
		notes: "ANSWERS which functions the rest of the tree leans on hardest.\nACT a correctness or speed win in a high-fan-in leaf pays once per caller.\nMISLEADS fan_in counts STATIC call sites, not runtime frequency. Worse,\n     calls resolve by BARE NAME, so a method sharing a builtin name\n     absorbs every call site in the tree: Django's 12-line `super`\n     method collects all 1,285 super() calls and ranks second. A short\n     function with four-digit fan_in is a name collision, not a hot\n     leaf. Test callers are counted too.",
		run:   run_hot_multipliers,
	},
	{
		name:  "typing-holes",
		title: "Public API without type annotations, ranked by blast radius",
		notes: "ANSWERS which unannotated functions the most other code depends on.\nACT annotate high-fan-in functions first: every caller inherits the\n     uncertainty, so one signature fixes many call sites for a checker.\nMISLEADS an unannotated private helper is fine. This ranks by fan_in for\n     that reason, and counts `self`/`cls` as untyped, which they are.",
		run:   run_typing_holes,
	},
	{
		name:  "god-functions",
		title: "Functions doing too much, by every measure at once",
		notes: "ANSWERS which functions are hardest to hold in your head.\nACT split by responsibility, not by line count. The n_elif column tells\n     you whether it is a dispatch table (extract to a dict) or real nesting.\nMISLEADS a long flat dispatch is far easier to read than a short deeply\n     nested one. Sort by cognitive rather than sloc for that reason.",
		run:   run_god_functions,
	},
	{
		name:  "deep-nesting",
		title: "Nesting deep enough that the reader loses the thread",
		notes: "ANSWERS which functions need guard clauses.\nACT invert the condition and return early. Each level removed is a level\n     of context the next reader does not have to carry.\nMISLEADS elif chains are correctly NOT counted as nesting here -- a 30-arm\n     dispatch is flat. What is counted is genuine block nesting.",
		run:   run_deep_nesting,
	},
	{
		name:  "nested-loops",
		title: "Nested loops: where the input size decides whether this matters",
		notes: "ANSWERS which functions have quadratic or worse structure.\nACT depth 2 over a small collection is fine; depth 3 over anything\n     user-sized is a design question. Look for a dict that removes a level.\nMISLEADS depth is syntactic. Two loops over a 3-element constant is depth 2\n     and costs nothing. Collection size is invisible to a static reader.",
		run:   run_nested_loops,
	},
	{
		name:  "class-shape",
		title: "Classes carrying too much, and classes carrying nothing",
		notes: "ANSWERS which classes are god objects and which are anaemic wrappers.\nACT a class with 40 methods and 30 attributes is several classes. A class\n     with two attributes and no methods wants to be a dataclass or a tuple.\nMISLEADS inherited members are not counted -- only what this class declares.\n     A thin subclass of a fat base looks small here and is not.",
		run:   run_class_shape,
	},
	{
		name:  "slots-candidates",
		title: "Classes instantiated in a loop that carry no __slots__",
		notes: "ANSWERS where per-instance dict overhead is being paid at volume.\nACT __slots__ removes the instance __dict__ -- typically 30-40%% less\n     memory per object and faster attribute access.\nMISLEADS __slots__ breaks multiple inheritance, weakrefs and dynamic\n     attribute assignment. It is a change to the class contract, not a\n     free win, and only pays at thousands of instances.",
		run:   run_slots_candidates,
	},
	{
		name:  "module-coupling",
		title: "Which modules depend on which, and how unstable that makes them",
		notes: "ANSWERS which modules are hard to change because everything leans on them.\nACT instability near 0 with high fan_in means many depend on it and it\n     depends on little -- that is a good place for stable abstractions and\n     a bad place for volatile logic.\nMISLEADS instability is a ratio, so a module with one edge each way scores\n     0.5 and means nothing. Read it alongside n_files.",
		run:   run_module_coupling,
	},
	{
		name:  "undocumented-complexity",
		title: "The hardest functions, with nothing written down",
		notes: "ANSWERS where the next reader has to reconstruct intent from the code.\nACT one sentence on what it does and what it assumes. Prefer the public,\n     high-fan-in end of the list -- that is where the cost compounds.\nMISLEADS a docstring is not understanding. This finds absence, not quality,\n     and short obvious functions correctly do not need one.",
		run:   run_undocumented_complexity,
	},
	{
		name:  "magic-numbers",
		title: "Unexplained constants, and the ones repeated across files",
		notes: "ANSWERS which literals are load-bearing but unnamed.\nACT a number appearing in several files is a shared assumption with no\n     name. Name it once and import it, so changing it is one edit.\nMISLEADS obvious values (0, 1, powers of two, 100, 1000, time units) are\n     already filtered out. What is left still includes plenty of harmless\n     array indices.",
		run:   run_magic_numbers,
	},
	{
		name:  "markers",
		title: "TODO, FIXME, HACK and BUG, weighted by the code they sit in",
		notes: "ANSWERS which unfinished business sits in code that matters.\nACT a FIXME in a function 40 things depend on outranks a TODO in a script.\nMISLEADS marker age is invisible here -- git blame is the missing column.\n     Many of these were resolved years ago and the comment stayed.",
		run:   run_markers,
	},
	{
		name:  "parse-coverage",
		title: "What this run could not read",
		notes: "ANSWERS whether the numbers above cover the code you think they cover.\nACT a file listed here contributed nothing. If your interpreter is older\n     than the target's syntax, run this on that version instead.\nMISLEADS a file can parse perfectly and still be misunderstood. This shows\n     only hard failures, not wrong interpretations.",
		run:   run_parse_coverage,
	},
	{
		name:  "latent-risk-density",
		title: "Cheap linter facts that only matter together, ranked by who depends on them",
		notes: "ANSWERS which functions carry several small smells at once in code that\n     many things call. Each fact here is individually reported by ruff or\n     bandit and individually ignorable -- an open() without encoding, a\n     naive datetime, a getattr on a computed name, an md5. A function\n     with four of them that 200 callers reach is a different proposition.\nACT read `facts` as a count of DISTINCT smells, not severity. Start where\n     facts and fan_in are both high: that is where one careful rewrite\n     retires several warnings and the blast radius justifies the risk.\nMISLEADS this deliberately mixes security and correctness facts, so a\n     high score can be four harmless portability warnings. It ranks\n     ATTENTION, not danger -- read the columns, not the total. Encoding\n     and timezone defaults are also platform-dependent, so a codebase\n     that only ever runs in one container may have decided already.",
		run:   run_latent_risk_density,
	},
	{
		name:  "too-many-locals",
		title: "Function with too many local variables (pylint R0914)",
		notes: "ANSWERS where a function has more than 15 local variables, making it hard\n     to track state and reason about.\nACT extract a helper class or split the function.\nMISLEADS a data-processing function with many locals is sometimes the\n     clearest form.",
		run:   run_too_many_locals,
	},
	{
		name:  "too-many-branches",
		title: "Function with too many branches (pylint R0912)",
		notes: "ANSWERS where a function has more than 12 branches, making it hard to\n     verify all paths.\nACT use a dispatch table, polymorphism, or extract branches into helpers.\nMISLEADS a switch-like if/elif chain with many arms is branchy but linear.\n     cyclomatic is a better measure of actual complexity.",
		run:   run_too_many_branches,
	},
	{
		name:  "too-many-return",
		title: "Function with too many return statements (pylint R0911)",
		notes: "ANSWERS where a function has more than 6 return statements, making it hard\n     to verify all exit paths and resource cleanup.\nACT consolidate returns, or use a result variable with a single exit point.\nMISLEADS guard clauses (early returns) are good style; the count alone does\n     not distinguish guard returns from scattered mid-function returns.",
		run:   run_too_many_return,
	},
	{
		name:  "scattered-concerns",
		title: "A function called from many different modules (shotgun surgery)",
		notes: "ANSWERS which functions are called from many distinct modules, so any change\n     ripples widely.\nACT consider splitting the function or making the contract more stable.\nMISLEADS a utility like `log` or `config` is called from everywhere and is\n     intentionally stable.",
		run:   run_scattered_concerns,
	},
	{
		name:  "line-too-long",
		title: "Files with very long lines (pylint C0301)",
		notes: "ANSWERS which files have lines exceeding 100 characters, which hurts\n     readability and may break some tools.\nACT wrap long lines; the max_line_len column gives the worst line.\nMISLEADS generated or minified files have long lines by design. The\n     is_generated filter excludes those.",
		run:   run_line_too_long,
	},
	{
		name:  "untyped-params",
		title: "Functions with no type annotations (pylint/mypy)",
		notes: "ANSWERS where a function has parameters without type annotations, so the\n     contract is implicit and static analysis cannot check it.\nACT add type annotations to all parameters and the return type.\nMISLEADS a stub or protocol function may omit annotations intentionally.\n     n_untyped_params counts the untyped ones; n_annotated_params the typed.",
		run:   run_untyped_params,
	},
	{
		name:  "deep-nesting-excessive",
		title: "Functions with excessive nesting depth (pylint R1702)",
		notes: "ANSWERS where a function has max_nesting > 5, making it hard to read and\n     test. Each level multiplies the test matrix.\nACT extract nested blocks into named helper functions; use early returns.\nMISLEADS a deeply nested comprehension is a single expression, not\n     structural nesting. The column measures structural nesting.",
		run:   run_deep_nesting_excessive,
	},
	{
		name:  "god-class",
		title: "A class with too many methods and high complexity (pylint R0902)",
		notes: "ANSWERS which classes have too many methods and too much complexity.\nACT split the class along responsibility lines.\nMISLEADS a framework base class may be intentionally broad.",
		run:   run_god_class,
	},
	{
		name:  "import-surface",
		title: "Which modules do real work at import time, and what kind",
		notes: "ANSWERS the import-time bill per module: I/O, network, subprocess, exec\n     and file handles that run the moment the module is imported -- the\n    cold-start cost every consumer pays and a failure mode that\n     surfaces as a bare ImportError.\nACT read the top modules' top-level statements; move anything that can\n     wait behind a function or a lazy import.\nMISLEADS one deliberate constant-table build dominates its module's\n     score the same as ten stray calls, and the <module> symbol\n     aggregates everything top-level, so guarded one-time setup cannot\n     be told from an accident.",
		run:   run_import_surface,
	},
	{
		name:  "exception-posture",
		title: "How each module handles failure: handler volume and how broad it is",
		notes: "ANSWERS the shape of error handling per module -- how many except\n     clauses, how many are bare/broad/empty, how many sit in loops, and\n     what share of handlers swallow everything.\nACT a high pct_broad with low bare counts means catch-alls that should\n     be narrowed; bare counts mean handlers that eat KeyboardInterrupt.\nMISLEADS volume is not quality -- a module with one careful broad\n     handler around a plugin boundary reads fine here but scores like a\n     swamp; the counts say nothing about what the handlers DO.",
		run:   run_exception_posture,
	},
	{
		name:  "resource-posture",
		title: "Files and handles per module: how many opens vs how many context managers",
		notes: "ANSWERS the resource discipline per module -- total open()/resource\n     sites against with-blocks and context managers, with the share of\n     opens that no context manager balances.\nACT start with the modules where pct_open_unmanaged is high AND the\n     open count is high; that is where a leaked handle is live.\nMISLEADS opens and context managers are counted per function body, not\n     paired -- a with around something else reads as discipline, and a\n     try/finally close (correct) reads as unmanaged.",
		run:   run_resource_posture,
	},
	{
		name:  "concurrency-posture",
		title: "Shared-state writes per module: spawns, locks, globals and mutable module vars",
		notes: "ANSWERS where the free-threaded build has to be correct, aggregated per\n     module: thread/process/lock sites, global-statement writes, async\n     functions, and module-level mutable containers.\nACT read with shared-mutable-state: a module high on both global\n     writes and spawn sites is where a race ships first.\nMISLEADS sums say nothing about PROTECTION -- a module that locks\n     everything scores like one that locks nothing, and a module-level\n     read-only lookup table counts as mutable module state.",
		run:   run_concurrency_posture,
	},
	{
		name:  "sql-construction",
		title: "SQL usage per module: how much is built by string surgery",
		notes: "ANSWERS where raw SQL lives per module and what share of it is\n     assembled with f-strings, concatenation or .format -- the\n     injection-prone fraction of the module's database surface.\nACT parameterize the hand-built queries first in the top modules; a\n     high pct there is where an injection lands next.\nMISLEADS hand-built does not mean injectable -- interpolating a\n     constant or a table name you own is fine; the pct can read 100 on\n     a module with a single query, and reads of n_sql miss any query\n     routed through an ORM.",
		run:   run_sql_construction,
	},
	{
		name:  "third-party-coupling",
		title: "External dependency pull per module: distinct roots, wildcards, relative reach",
		notes: "ANSWERS how much of each module's import block is third-party, and how\n     many distinct external roots it pins -- the upgrade surface: one\n     breaking release per root lands here.\nACT consolidate the top module's roots behind one adapter module so a\n     major-version bump is a one-file change.\nMISLEADS root = text before the first dot of the import target, so one\n     vendor shipping two packages counts twice and a lazy in-function\n     import does not count at all; import COUNT says nothing about\n     usage depth.",
		run:   run_third_party_coupling,
	},
	{
		name:  "recursive-hotspots",
		title: "Functions that call themselves, by complexity and fan-in",
		notes: "ANSWERS where recursion lives and which recursive functions the most\n     code leans on -- a deep-enough input turns each of these into a\n     RecursionError (or a stack exhaustion on the free-threaded build).\nACT for high fan-in plus high cyclomatic, add an explicit depth budget\n     or convert to an explicit stack.\nMISLEADS is_recursive is a SELF-EDGE only -- mutual recursion (A calls\n     B calls A) is invisible, and a self-call guarded to depth 2 is\n     perfectly safe; input depth is unknowable statically.",
		run:   run_recursive_hotspots,
	},
	{
		name:  "registration-surface",
		title: "Framework-registered entry points per module: code invoked without a caller",
		notes: "ANSWERS where implicit invocation concentrates -- functions registered by\n     decorators (routes, tasks, signal receivers, click commands,\n     fixtures): code that runs with zero static callers, which every\n     reachability answer must treat as live.\nACT keep registrations in few modules; a registration hotspot is the\n    place a rename silently kills an endpoint.\nMISLEADS the decorator-name list is heuristic (task/route/receiver/...),\n     so a custom registering decorator is missed and a function named\n     in a decorator by coincidence is counted; a function can carry\n     several registering decorators and counts once per attribute row.",
		run:   run_registration_surface,
	},
	{
		name:  "input-surface",
		title: "Request-input reads per module, and how much of the module checks auth",
		notes: "ANSWERS the attack surface per module -- how many request-input sites it\n     reads (query/form/cookie/header/body) and what share of its\n     functions contain an auth-family call.\nACT read with unauthenticated-input-surface: a module with many input\n     reads and a low pct_auth is where a missing check is cheapest to\n     find.\nMISLEADS auth may live in middleware or a base class, which reads as a\n     low pct_auth; input SITES are attribute reads, not data flow, and\n     modules that parse input away from the `request` spelling (click,\n     argparse) are invisible.",
		run:   run_input_surface,
	},
	{
		name:  "network-hygiene",
		title: "Outbound calls per module: how many carry no timeout",
		notes: "ANSWERS the per-module split of outbound network calls: fetch sites,\n     total net calls, and the share issued with no timeout -- one\n     stalled peer per call site becomes a stuck worker per call.\nACT add timeouts in the top module first; wrap the rest in a deadline\n     at the boundary.\nMISLEADS counts sites, not call frequency -- one no-timeout call in a\n     retry loop outranks ten in one-shot paths here; session-level\n     default timeouts set in client setup are invisible, so a module\n     can rank high while every call inherits one.",
		run:   run_network_hygiene,
	},
}

var builtinNames = []string{
	"ArithmeticError",
	"AssertionError",
	"AttributeError",
	"BaseException",
	"BaseExceptionGroup",
	"BlockingIOError",
	"BrokenPipeError",
	"BufferError",
	"BytesWarning",
	"ChildProcessError",
	"ConnectionAbortedError",
	"ConnectionError",
	"ConnectionRefusedError",
	"ConnectionResetError",
	"DeprecationWarning",
	"EOFError",
	"Ellipsis",
	"EncodingWarning",
	"EnvironmentError",
	"Exception",
	"ExceptionGroup",
	"False",
	"FileExistsError",
	"FileNotFoundError",
	"FloatingPointError",
	"FutureWarning",
	"GeneratorExit",
	"IOError",
	"ImportError",
	"ImportWarning",
	"IndentationError",
	"IndexError",
	"InterruptedError",
	"IsADirectoryError",
	"KeyError",
	"KeyboardInterrupt",
	"LookupError",
	"MemoryError",
	"ModuleNotFoundError",
	"NameError",
	"None",
	"NotADirectoryError",
	"NotImplemented",
	"NotImplementedError",
	"OSError",
	"OverflowError",
	"PendingDeprecationWarning",
	"PermissionError",
	"ProcessLookupError",
	"PythonFinalizationError",
	"RecursionError",
	"ReferenceError",
	"ResourceWarning",
	"RuntimeError",
	"RuntimeWarning",
	"StopAsyncIteration",
	"StopIteration",
	"SyntaxError",
	"SyntaxWarning",
	"SystemError",
	"SystemExit",
	"TabError",
	"TimeoutError",
	"True",
	"TypeError",
	"UnboundLocalError",
	"UnicodeDecodeError",
	"UnicodeEncodeError",
	"UnicodeError",
	"UnicodeTranslateError",
	"UnicodeWarning",
	"UserWarning",
	"ValueError",
	"Warning",
	"ZeroDivisionError",
	"_IncompleteInputError",
	"__build_class__",
	"__debug__",
	"__doc__",
	"__import__",
	"__loader__",
	"__name__",
	"__package__",
	"__spec__",
	"abs",
	"aiter",
	"all",
	"anext",
	"any",
	"ascii",
	"bin",
	"bool",
	"breakpoint",
	"bytearray",
	"bytes",
	"callable",
	"chr",
	"classmethod",
	"compile",
	"complex",
	"copyright",
	"credits",
	"delattr",
	"dict",
	"dir",
	"divmod",
	"enumerate",
	"eval",
	"exec",
	"exit",
	"filter",
	"float",
	"format",
	"frozenset",
	"getattr",
	"globals",
	"hasattr",
	"hash",
	"help",
	"hex",
	"id",
	"input",
	"int",
	"isinstance",
	"issubclass",
	"iter",
	"len",
	"license",
	"list",
	"locals",
	"map",
	"max",
	"memoryview",
	"min",
	"next",
	"object",
	"oct",
	"open",
	"ord",
	"pow",
	"print",
	"property",
	"quit",
	"range",
	"repr",
	"reversed",
	"round",
	"set",
	"setattr",
	"slice",
	"sorted",
	"staticmethod",
	"str",
	"sum",
	"super",
	"tuple",
	"type",
	"vars",
	"zip",
}

var stdlibModuleNames = []string{
	"__future__",
	"_abc",
	"_aix_support",
	"_android_support",
	"_apple_support",
	"_ast",
	"_ast_unparse",
	"_asyncio",
	"_bisect",
	"_blake2",
	"_bz2",
	"_codecs",
	"_codecs_cn",
	"_codecs_hk",
	"_codecs_iso2022",
	"_codecs_jp",
	"_codecs_kr",
	"_codecs_tw",
	"_collections",
	"_collections_abc",
	"_colorize",
	"_compat_pickle",
	"_contextvars",
	"_csv",
	"_ctypes",
	"_curses",
	"_curses_panel",
	"_datetime",
	"_dbm",
	"_decimal",
	"_elementtree",
	"_frozen_importlib",
	"_frozen_importlib_external",
	"_functools",
	"_gdbm",
	"_hashlib",
	"_heapq",
	"_hmac",
	"_imp",
	"_interpchannels",
	"_interpqueues",
	"_interpreters",
	"_io",
	"_ios_support",
	"_json",
	"_locale",
	"_lsprof",
	"_lzma",
	"_markupbase",
	"_md5",
	"_multibytecodec",
	"_multiprocessing",
	"_opcode",
	"_opcode_metadata",
	"_operator",
	"_osx_support",
	"_overlapped",
	"_pickle",
	"_posixshmem",
	"_posixsubprocess",
	"_py_abc",
	"_py_warnings",
	"_pydatetime",
	"_pydecimal",
	"_pyio",
	"_pylong",
	"_pyrepl",
	"_queue",
	"_random",
	"_remote_debugging",
	"_scproxy",
	"_sha1",
	"_sha2",
	"_sha3",
	"_signal",
	"_sitebuiltins",
	"_socket",
	"_sqlite3",
	"_sre",
	"_ssl",
	"_stat",
	"_statistics",
	"_string",
	"_strptime",
	"_struct",
	"_suggestions",
	"_symtable",
	"_sysconfig",
	"_thread",
	"_threading_local",
	"_tkinter",
	"_tokenize",
	"_tracemalloc",
	"_types",
	"_typing",
	"_uuid",
	"_warnings",
	"_weakref",
	"_weakrefset",
	"_winapi",
	"_wmi",
	"_zoneinfo",
	"_zstd",
	"abc",
	"annotationlib",
	"antigravity",
	"argparse",
	"array",
	"ast",
	"asyncio",
	"atexit",
	"base64",
	"bdb",
	"binascii",
	"bisect",
	"builtins",
	"bz2",
	"cProfile",
	"calendar",
	"cmath",
	"cmd",
	"code",
	"codecs",
	"codeop",
	"collections",
	"colorsys",
	"compileall",
	"compression",
	"concurrent",
	"configparser",
	"contextlib",
	"contextvars",
	"copy",
	"copyreg",
	"csv",
	"ctypes",
	"curses",
	"dataclasses",
	"datetime",
	"dbm",
	"decimal",
	"difflib",
	"dis",
	"doctest",
	"email",
	"encodings",
	"ensurepip",
	"enum",
	"errno",
	"faulthandler",
	"fcntl",
	"filecmp",
	"fileinput",
	"fnmatch",
	"fractions",
	"ftplib",
	"functools",
	"gc",
	"genericpath",
	"getopt",
	"getpass",
	"gettext",
	"glob",
	"graphlib",
	"grp",
	"gzip",
	"hashlib",
	"heapq",
	"hmac",
	"html",
	"http",
	"idlelib",
	"imaplib",
	"importlib",
	"inspect",
	"io",
	"ipaddress",
	"itertools",
	"json",
	"keyword",
	"linecache",
	"locale",
	"logging",
	"lzma",
	"mailbox",
	"marshal",
	"math",
	"mimetypes",
	"mmap",
	"modulefinder",
	"msvcrt",
	"multiprocessing",
	"netrc",
	"nt",
	"ntpath",
	"nturl2path",
	"numbers",
	"opcode",
	"operator",
	"optparse",
	"os",
	"pathlib",
	"pdb",
	"pickle",
	"pickletools",
	"pkgutil",
	"platform",
	"plistlib",
	"poplib",
	"posix",
	"posixpath",
	"pprint",
	"profile",
	"pstats",
	"pty",
	"pwd",
	"py_compile",
	"pyclbr",
	"pydoc",
	"pydoc_data",
	"pyexpat",
	"queue",
	"quopri",
	"random",
	"re",
	"readline",
	"reprlib",
	"resource",
	"rlcompleter",
	"runpy",
	"sched",
	"secrets",
	"select",
	"selectors",
	"shelve",
	"shlex",
	"shutil",
	"signal",
	"site",
	"smtplib",
	"socket",
	"socketserver",
	"sqlite3",
	"sre_compile",
	"sre_constants",
	"sre_parse",
	"ssl",
	"stat",
	"statistics",
	"string",
	"stringprep",
	"struct",
	"subprocess",
	"symtable",
	"sys",
	"sysconfig",
	"syslog",
	"tabnanny",
	"tarfile",
	"tempfile",
	"termios",
	"textwrap",
	"this",
	"threading",
	"time",
	"timeit",
	"tkinter",
	"token",
	"tokenize",
	"tomllib",
	"trace",
	"traceback",
	"tracemalloc",
	"tty",
	"turtle",
	"turtledemo",
	"types",
	"typing",
	"unicodedata",
	"unittest",
	"urllib",
	"uuid",
	"venv",
	"warnings",
	"wave",
	"weakref",
	"webbrowser",
	"winreg",
	"winsound",
	"wsgiref",
	"xml",
	"xmlrpc",
	"zipapp",
	"zipfile",
	"zipimport",
	"zlib",
	"zoneinfo",
}

var hazardCalls = map[string]string{

	"eval": "exec", "exec": "exec", "compile": "exec", "execfile": "exec",
	"__import__": "exec",

	"pickle.load": "deserialize", "pickle.loads": "deserialize",
	"cPickle.load": "deserialize", "cPickle.loads": "deserialize",
	"dill.load": "deserialize", "dill.loads": "deserialize",
	"marshal.load": "deserialize", "marshal.loads": "deserialize",
	"shelve.open": "deserialize", "yaml.load": "deserialize",
	"yaml.unsafe_load": "deserialize", "yaml.full_load": "deserialize",
	"jsonpickle.decode": "deserialize", "torch.load": "deserialize",
	"joblib.load": "deserialize", "numpy.load": "deserialize",
	"np.load": "deserialize",

	"os.system": "shell", "os.popen": "shell", "os.spawnl": "shell",
	"os.spawnv": "shell", "os.execv": "shell", "os.execl": "shell",
	"commands.getoutput": "shell", "commands.getstatusoutput": "shell",
	"subprocess.run": "shell", "subprocess.call": "shell",
	"subprocess.Popen": "shell", "subprocess.check_call": "shell",
	"subprocess.check_output": "shell", "subprocess.getoutput": "shell",
	"pty.spawn": "shell",

	"open": "io", "os.remove": "io", "os.unlink": "io", "os.rmdir": "io",
	"os.rename": "io", "os.replace": "io", "shutil.rmtree": "io",
	"shutil.copy": "io", "shutil.move": "io", "os.chmod": "io",
	"os.chown": "io", "os.makedirs": "io", "os.walk": "io",
	"pathlib.Path.write_text": "io", "pathlib.Path.read_text": "io",
	"tempfile.mktemp": "io", "os.getcwd": "io", "os.listdir": "io",

	"socket.socket": "net", "socket.create_connection": "net",
	"requests.get": "net", "requests.post": "net", "requests.put": "net",
	"requests.delete": "net", "requests.request": "net",
	"urllib.request.urlopen": "net", "urlopen": "net",
	"httpx.get": "net", "httpx.post": "net", "httpx.request": "net",
	"aiohttp.request": "net", "http.client.HTTPConnection": "net",
	"ftplib.FTP": "net", "telnetlib.Telnet": "net", "smtplib.SMTP": "net",
	"paramiko.SSHClient": "net", "xmlrpc.client.ServerProxy": "net",

	"cursor.execute": "sql", "cursor.executemany": "sql",
	"connection.execute": "sql", "session.execute": "sql",
	"db.execute": "sql", "conn.execute": "sql",
	"sqlalchemy.text": "sql", "text": "sql",
	"objects.raw": "sql", "objects.extra": "sql",
	"django.db.connection.cursor": "sql",

	"hashlib.md5": "crypto", "hashlib.sha1": "crypto",
	"hashlib.new": "crypto", "md5.new": "crypto",
	"random.random": "crypto", "random.randint": "crypto",
	"random.choice": "crypto", "random.shuffle": "crypto",
	"random.randrange": "crypto", "random.seed": "crypto",
	"ssl._create_unverified_context": "crypto",
	"Crypto.Cipher.DES":              "crypto", "Crypto.Cipher.ARC4": "crypto",

	"getattr": "reflect", "setattr": "reflect", "delattr": "reflect",
	"hasattr": "reflect", "globals": "reflect", "locals": "reflect",
	"vars": "reflect", "dir": "reflect",
	"importlib.import_module": "reflect", "importlib.reload": "reflect",
	"inspect.getmembers": "reflect", "inspect.signature": "reflect",
	"type": "reflect", "super": "reflect",
	"operator.attrgetter": "reflect", "operator.methodcaller": "reflect",

	"threading.Thread": "concurrency", "threading.Lock": "concurrency",
	"threading.RLock": "concurrency", "threading.Event": "concurrency",
	"threading.local": "concurrency", "threading.Condition": "concurrency",
	"multiprocessing.Process": "concurrency", "multiprocessing.Pool": "concurrency",
	"concurrent.futures.ThreadPoolExecutor":  "concurrency",
	"concurrent.futures.ProcessPoolExecutor": "concurrency",
	"ThreadPoolExecutor":                     "concurrency", "ProcessPoolExecutor": "concurrency",
	"asyncio.create_task": "concurrency", "asyncio.gather": "concurrency",
	"asyncio.ensure_future": "concurrency", "asyncio.run": "concurrency",
	"asyncio.Lock": "concurrency", "asyncio.Semaphore": "concurrency",
	"asyncio.to_thread": "concurrency", "asyncio.wait_for": "concurrency",
	"asyncio.TaskGroup": "concurrency", "asyncio.shield": "concurrency",
	"queue.Queue": "concurrency", "os.fork": "concurrency",

	"time.sleep": "blocking", "os.wait": "blocking", "os.waitpid": "blocking",
	"input": "blocking", "select.select": "blocking",
	"subprocess.wait": "blocking", "lock.acquire": "blocking",
	"socket.recv": "blocking", "socket.accept": "blocking",

	"tempfile.NamedTemporaryFile": "resource", "tempfile.TemporaryFile": "resource",
	"sqlite3.connect": "resource", "psycopg2.connect": "resource",
	"pymysql.connect": "resource", "gzip.open": "resource",
	"zipfile.ZipFile": "resource", "tarfile.open": "resource",
	"mmap.mmap": "resource", "os.fdopen": "resource",
	"signal.signal": "resource", "atexit.register": "resource",
}

var hazardMethodSuffix = map[string]string{
	"execute": "sql", "executemany": "sql", "executescript": "sql",
	"raw": "sql", "read": "io", "write": "io", "readlines": "io",
	"acquire": "concurrency", "release": "concurrency",
	"join": "concurrency", "start": "concurrency",
	"recv": "net", "send": "net", "connect": "net",
}

var hazardImports = map[string]string{
	"pickle": "deserialize", "cPickle": "deserialize", "dill": "deserialize",
	"marshal": "deserialize", "shelve": "deserialize",
	"subprocess": "shell", "commands": "shell", "pty": "shell",
	"socket": "net", "requests": "net", "urllib": "net", "httpx": "net",
	"aiohttp": "net", "ftplib": "net", "telnetlib": "net", "paramiko": "net",
	"ctypes": "exec", "cffi": "exec",
	"threading": "concurrency", "multiprocessing": "concurrency",
	"asyncio": "concurrency", "concurrent": "concurrency",
}

var reqInputKinds = map[string]string{
	"args": "query", "GET": "query",
	"form": "form", "POST": "form", "files": "form", "FILES": "form",
	"cookies": "cookie", "COOKIES": "cookie",
	"headers":  "header",
	"get_json": "body",
}

var secretRE = mustCompile(`(?i)(api[_-]?key|apikey|secret|password|passwd|pwd|token|bearer|access[_-]?key|private[_-]?key|client[_-]?secret|auth[_-]?token|jwt|credential|smtp[_-]?pass|db[_-]?pass|sk_live|rk_live|pk_live|ghp_|xoxb-|AKIA)`)

const secretMinLen = 12

var logLevels = map[string]bool{
	"debug": true, "info": true, "warning": true, "warn": true,
	"error": true, "exception": true, "critical": true,
}

var authMarkers = []string{"login", "auth", "token", "jwt", "authenticate",
	"authorize", "current_user", "session.get"}

var fetchPrefixes = []string{"requests.", "httpx.", "http.client.", "aiohttp.",
	"urllib.request.urlopen", "urllib.urlopen"}

var xxePrefixes = []string{"xml.etree.", "lxml.", "xml.dom.", "xml.sax."}

const zipPrefix = "zipfile."

var querysetReads = map[string]bool{
	"get": true, "filter": true, "exclude": true, "all": true, "first": true,
	"last": true, "count": true, "exists": true, "iterator": true, "one": true,
	"scalar": true,
}

var ormWriteMethods = map[string]bool{
	"save": true, "create": true, "delete": true, "bulk_create": true,
	"bulk_update": true, "update_or_create": true, "get_or_create": true,
	"incr": true, "decr": true,
}

var ormWriteGated = map[string]bool{"update": true, "add": true, "set": true}

var resourceReturns = map[string]bool{
	"open": true, "urlopen": true, "connect": true, "NamedTemporaryFile": true,
	"TemporaryFile": true, "Session": true, "cursor": true, "mkstemp": true,
}

var mutableDefaultCalls = map[string]bool{
	"list": true, "dict": true, "set": true, "bytearray": true,
	"collections.deque": true, "defaultdict": true, "OrderedDict": true,
	"Counter": true,
}

var broadExceptions = map[string]bool{"Exception": true, "BaseException": true}

var dunderEntry = map[string]bool{
	"__main__": true, "main": true, "handler": true, "lambda_handler": true,
	"app": true,
}

var sqlTextRE = mustCompile(`(?i)\b(SELECT|INSERT\s+INTO|UPDATE|DELETE\s+FROM|CREATE\s+TABLE|DROP\s+TABLE|ALTER\s+TABLE|UNION\s+(?:ALL\s+)?SELECT)\b`)

var magicOK = map[int64]bool{
	0: true, 1: true, 2: true, -1: true, 10: true, 100: true, 1000: true,
	8: true, 16: true, 32: true, 64: true, 128: true, 256: true, 512: true,
	1024: true, 255: true, 65535: true, 4096: true, 24: true, 60: true,
	365: true, 7: true, 12: true, 3: true, 4: true, 6: true,
}

var cgBuiltins = func() map[string]bool {
	m := map[string]bool{}
	for _, n := range builtinNames {
		m[n] = true
	}
	for _, n := range []string{"self", "cls", "super", "print", "range", "len", "open"} {
		m[n] = true
	}
	return m
}()

var stdlibRoots = func() map[string]bool {
	m := map[string]bool{}
	for _, n := range stdlibModuleNames {
		m[n] = true
	}
	return m
}()

func sprintf(format string, a ...any) string { return fmt.Sprintf(format, a...) }

func decodeStrEscapes(s string, raw, isBytes bool) string {
	if raw {
		return s
	}
	if !strings.ContainsRune(s, '\\') {
		return s
	}
	var b strings.Builder
	b.Grow(len(s))
	for i := 0; i < len(s); i++ {
		c := s[i]
		if c != '\\' || i+1 >= len(s) {
			b.WriteByte(c)
			continue
		}
		i++
		switch s[i] {
		case '\n':

		case '\\':
			b.WriteByte('\\')
		case '\'':
			b.WriteByte('\'')
		case '"':
			b.WriteByte('"')
		case 'a':
			b.WriteByte(7)
		case 'b':
			b.WriteByte(8)
		case 'f':
			b.WriteByte(12)
		case 'n':
			b.WriteByte('\n')
		case 'r':
			b.WriteByte('\r')
		case 't':
			b.WriteByte('\t')
		case 'v':
			b.WriteByte(11)
		case '\r':
			if i+1 < len(s) && s[i+1] == '\n' {
				i++
			}
		case '0', '1', '2', '3', '4', '5', '6', '7':
			v := int(s[i] - '0')
			for k := 0; k < 2 && i+1 < len(s) && s[i+1] >= '0' && s[i+1] <= '7'; k++ {
				i++
				v = v*8 + int(s[i]-'0')
			}
			if isBytes {
				b.WriteByte(byte(v))
			} else {
				b.WriteRune(rune(v))
			}
		case 'x':
			if i+2 < len(s) && isHex(s[i+1]) && isHex(s[i+2]) {
				v := hexVal(s[i+1])<<4 | hexVal(s[i+2])
				if isBytes {
					b.WriteByte(byte(v))
				} else {
					b.WriteRune(rune(v))
				}
				i += 2
			} else {
				b.WriteByte('\\')
				b.WriteByte('x')
			}
		case 'N':

			if i+1 < len(s) && s[i+1] == '{' {
				j := i + 2
				for j < len(s) && s[j] != '}' {
					j++
				}
				if j < len(s) {
					b.WriteString(s[i-1 : j+1])
					i = j
					break
				}
			}
			b.WriteByte('\\')
			b.WriteByte('N')
		case 'u':
			if i+4 < len(s) && isHex(s[i+1]) && isHex(s[i+2]) && isHex(s[i+3]) && isHex(s[i+4]) {
				r := rune(hexVal(s[i+1])<<12 | hexVal(s[i+2])<<8 | hexVal(s[i+3])<<4 | hexVal(s[i+4]))
				b.WriteRune(r)
				i += 4
			} else {
				b.WriteByte('\\')
				b.WriteByte('u')
			}
		case 'U':
			if i+8 < len(s) {
				ok := true
				var r rune
				for k := 1; k <= 8; k++ {
					if !isHex(s[i+k]) {
						ok = false
						break
					}
					r = r<<4 | rune(hexVal(s[i+k]))
				}
				if ok {
					b.WriteRune(r)
					i += 8
					break
				}
			}
			b.WriteByte('\\')
			b.WriteByte('U')
		default:
			b.WriteByte('\\')
			b.WriteByte(s[i])
		}
	}
	return b.String()
}

func hexVal(c byte) int {
	switch {
	case c >= '0' && c <= '9':
		return int(c - '0')
	case c >= 'a' && c <= 'f':
		return int(c-'a') + 10
	case c >= 'A' && c <= 'F':
		return int(c-'A') + 10
	}
	return 0
}

func mustCompile(expr string) *regexp.Regexp { return regexp.MustCompile(expr) }

func b2i32(b bool) int32 {
	if b {
		return 1
	}
	return 0
}

func strings_Repeat(s string, n int) string { return strings.Repeat(s, n) }

func maxI32(a, b int32) int32 {
	if a > b {
		return a
	}
	return b
}

func isHex(c byte) bool {
	return (c >= '0' && c <= '9') || (c >= 'a' && c <= 'f') || (c >= 'A' && c <= 'F')
}

const target = "Python 3.15 (stdlib ast; grammar fallback for newer syntax)"
const schemaVersion = 1

var out = bufio.NewWriterSize(os.Stdout, 1<<16)

func printfLn(format string, a ...any) {
	fmt.Fprintf(out, format+"\n", a...)
}

func cgPutU32(b []byte, o int, v uint32) { *(*uint32)(unsafe.Pointer(&b[o])) = v }
func cgPutU64(b []byte, o int, v uint64) { *(*uint64)(unsafe.Pointer(&b[o])) = v }

func cgGetU32(b []byte, o int) uint32 { return *(*uint32)(unsafe.Pointer(&b[o])) }
func cgGetU64(b []byte, o int) uint64 { return *(*uint64)(unsafe.Pointer(&b[o])) }

func main() {

	if f := os.Getenv("CGPY_DEBUG_BFS"); f != "" {
		debugBFSOrder(f)
		return
	}
	os.Exit(run(os.Args[1:]))
}

func debugBFSOrder(path string) {
	src, err := os.ReadFile(path)
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(2)
	}
	p := tsParserNew()
	defer p.free()
	tr := p.parse(src)
	if tr == nil {
		os.Exit(3)
	}
	defer tr.free()
	root := tr.root()
	ls := []uint{0}
	for i, b := range src {
		if b == '\n' {
			ls = append(ls, uint(i+1))
		}
	}
	col := func(sb uint) int {
		lo, hi := 0, len(ls)-1
		for lo < hi {
			mid := (lo + hi + 1) / 2
			if ls[mid] <= sb {
				lo = mid
			} else {
				hi = mid - 1
			}
		}
		return int(sb - ls[lo])
	}
	first := true
	walkNamedBFS(root, src, func(c tsNode) {
		if kindName(c) == "call" {
			if !first {
				fmt.Print(",")
			}
			first = false
			fmt.Printf("%d:%d", line1(c), col(startByte(c)))
		}
	})
	fmt.Println()
}

func run(argv []string) int {
	fs := flag.NewFlagSet("codegraph-python", flag.ContinueOnError)
	fs.SetOutput(os.Stderr)
	var (
		list        = fs.Bool("list", false, "list the queries")
		metrics     = fs.Bool("metrics", false, "run/list the METRICS section")
		report      = fs.Bool("report", false, "narrative overview")
		dumpPath    = fs.String("dump", "", "write the canonical graph dump here")
		modLike     = fs.String("module", "%", "module-name LIKE filter")
		limit       = fs.Int("limit", -1, "rows per query; -1 is every row")
		quiet       = fs.Bool("quiet", false, "")
		version     = fs.Bool("version", false, "")
		noTests     = fs.Bool("no-tests", false, "skip test files")
		incGen      = fs.Bool("include-generated", false, "parse generated files too")
		incVend     = fs.Bool("include-vendored", false, "parse vendored trees too")
		only        = fs.String("only", "", "comma-separated question numbers or names")
		workersFlag = fs.Int("workers", defaultParseWorkers(), "parse workers; 1 is the serial reader, 0 means one per core")
		cpuProf     = fs.String("cpuprofile", "", "write a CPU profile here")
		memProf     = fs.String("memprofile", "", "write an alloc_space/inuse_space profile here")
		profMs      = fs.Int("profilems", 0, "milliseconds between heap samples (0 = default)")
		blockProf   = fs.String("blockprofile", "", "write a block profile here")
		mutexProf   = fs.String("mutexprofile", "", "write a mutex profile here")
		saveASTPath = fs.String("save-ast", "", "parse/build, then write the binary AST state to PATH")
		loadASTPath = fs.String("load-ast", "", "load a saved AST state instead of parsing")
		force       = fs.Bool("force", false, "overwrite an existing --save-ast state file")
	)
	var csvQ, jsonQ qNum
	fs.Var(&csvQ, "csv", "emit question N as CSV")
	fs.Var(&jsonQ, "json", "emit question N as JSON")
	fs.Usage = func() {
		fmt.Fprintf(os.Stderr, "usage: codegraph-python [flags] [tree] [question-number ...]\n")
		fmt.Fprintf(os.Stderr, "       [--save-ast PATH | --load-ast PATH] [--force]\n\n")
		fs.PrintDefaults()
	}

	var positional []string
	var flags []string
	for i := 0; i < len(argv); i++ {
		a := argv[i]
		if a == "--" {
			positional = append(positional, argv[i+1:]...)
			break
		}
		if len(a) > 1 && a[0] == '-' {
			flags = append(flags, a)

			if !strings.Contains(a, "=") && i+1 < len(argv) &&
				!strings.HasPrefix(argv[i+1], "-") && needsValue(a) {
				flags = append(flags, argv[i+1])
				i++
			}
			continue
		}
		positional = append(positional, a)
	}
	if err := fs.Parse(flags); err != nil {
		return 2
	}
	if *version {
		printfLn("codegraph-python  target=%s  schema=v%d  go=%s  cpus=%d",
			target, schemaVersion, runtime.Version(), runtime.NumCPU())
		out.Flush()
		return 0
	}
	cat := Queries
	if *metrics {
		cat = Metrics
	}
	if *list {
		for i, q := range cat {
			printfLn("%2d. %-26s %s", i+1, q.name, q.title)
		}
		out.Flush()
		return 0
	}
	args := positional
	root := "."
	var which []int
	if len(args) > 0 {
		root = args[0]
		for _, a := range args[1:] {
			n, err := strconv.Atoi(a)
			if err != nil {

				fs.Usage()
				fmt.Fprintf(os.Stderr, "codegraph-python: error: argument which: invalid int value: '%s'\n", a)
				out.Flush()
				return 2
			}
			which = append(which, n)
		}
	}
	if *only != "" {
		which = nil
		for part := range strings.SplitSeq(*only, ",") {
			part = strings.TrimSpace(part)
			if part == "" {
				continue
			}
			if n, err := strconv.Atoi(part); err == nil {
				which = append(which, n)
				continue
			}
			for i, q := range cat {
				if q.name == part {
					which = append(which, i+1)
				}
			}
		}
	}
	if *saveASTPath != "" && *loadASTPath != "" {
		fmt.Fprintln(os.Stderr, "--save-ast and --load-ast cannot be used together")
		out.Flush()
		return 2
	}
	if *loadASTPath == "" {
		st, err := os.Stat(root)
		if err != nil || !st.IsDir() {
			printfLn("not a directory: %s", root)
			out.Flush()
			return 2
		}
	}

	if csvQ.set || jsonQ.set {
		*quiet = true
	}

	// Keep the heap tight: the parse pipeline holds several decoded batches at
	// once and the default GOGC=100 lets peak RSS run ~30% above the serial
	// reader. 30 matches the sibling ports' default (CG_GOGC overrides).
	gogc := 30
	if v := os.Getenv("CG_GOGC"); v != "" {
		if n, err := strconv.Atoi(v); err == nil {
			gogc = n
		}
	}
	debug.SetGCPercent(gogc)

	if *cpuProf != "" {
		f, err := os.Create(*cpuProf)
		if err != nil {
			fmt.Fprintf(os.Stderr, "could not write %s: %v\n", *cpuProf, err)
			out.Flush()
			return 2
		}
		pprof.StartCPUProfile(f)
		defer func() { pprof.StopCPUProfile(); f.Close() }()
	}
	if *profMs > 0 {
		runtime.MemProfileRate = *profMs
	}
	t0 := time.Now()
	var g *Graph
	recs := []*sourceFile(nil)
	if *loadASTPath != "" {
		var lerr error
		g, lerr = loadAST(*loadASTPath)
		if lerr != nil {
			fmt.Fprintf(os.Stderr, "load-ast: %v\n", lerr)
			out.Flush()
			return 2
		}
	} else {
		g = NewGraph()
		recs = g.discover(root, !*noTests, *incGen, *incVend, *quiet)
		if !*quiet {
			printfLn("  %d python files discovered in %.1fs", len(recs), time.Since(t0).Seconds())
		}
		t1 := time.Now()

		workers := *workersFlag
		if workers <= 0 {
			workers = runtime.GOMAXPROCS(0)
		}
		g.keepTrees = *saveASTPath != ""

		nFailed, nSyntax := g.parseAndExtract(recs, workers, *quiet)
		if cgPipeline {
			fmt.Fprintf(os.Stderr, "pipeline: wall=%dms readerBusy=%dms stageBusy=%dms decoderBusy=%dms extractBusy=%dms\n",
				time.Since(t1)/1e6, pipeReadWait.Load()/1e6, pipeStage.Load()/1e6,
				pipeDecode.Load()/1e6, pipeExtract.Load()/1e6)
		}
		if nFailed > 0 {
			fmt.Fprintf(os.Stderr, "  WARNING: %d of %d file(s) FAILED to parse and contributed nothing.\n", nFailed, len(recs))
			fmt.Fprintf(os.Stderr, "           Re-run with CODEGRAPH_DEBUG=1 for the tracebacks.\n")
		}
		if nSyntax > 0 {
			fmt.Fprintf(os.Stderr, "  NOTE: %d file(s) had a syntax error; catalogued, not parsed.\n", nSyntax)
		}
		if !*quiet {
			suffix := ""
			if nFailed > 0 {
				suffix = fmt.Sprintf(" (%d file(s) failed)", nFailed)
			}
			printfLn("  %d symbols parsed in %.1fs%s", len(g.Symbols), time.Since(t1).Seconds(), suffix)
			if len(recs) > 0 && len(g.Symbols) == 0 {
				printfLn("  WARNING: %d file(s) were read and produced NO symbols. Every", len(recs))
				printfLn("           query below will be empty for that reason, not because the")
				printfLn("           code is clean. Check --report for parse errors.")
			}
		}
		t2 := time.Now()
		g.resolvePendingHazards()
		nRes, nExt, nUnres := g.resolveCalls()
		nImp := g.resolveImports()
		g.materialise()
		if !*quiet {
			printfLn("  call graph built in %.1fs", time.Since(t2).Seconds())
		}
		t3 := time.Now()
		g.fillMeta(root, int32(len(recs)), int32(nFailed), int32(nImp), nRes, nExt, nUnres)
		if !*quiet {
			printfLn("  aggregates materialized in %.1fs", time.Since(t3).Seconds())
			printfLn("  indexed in %.1fs", time.Since(t3).Seconds())
		}
	}

	if *saveASTPath != "" {
		if _, serr := os.Lstat(*saveASTPath); serr == nil && !*force {
			fmt.Fprintf(os.Stderr, "refusing to overwrite %s (pass --force)\n", *saveASTPath)
			out.Flush()
			return 2
		}
		ts := time.Now()
		nb, werr := saveASTFile(g, *saveASTPath)
		if werr != nil {
			fmt.Fprintf(os.Stderr, "save-ast: %v\n", werr)
			out.Flush()
			return 2
		}
		if !*quiet {
			printfLn("ast state written to %s: %d bytes in %.1fs", *saveASTPath, nb, time.Since(ts).Seconds())
		}
	}

	if *dumpPath != "" {
		f, err := os.Create(*dumpPath)
		if err != nil {
			fmt.Fprintf(os.Stderr, "could not write %s: %v\n", *dumpPath, err)
			out.Flush()
			return 2
		}
		w := bufio.NewWriterSize(f, 1<<20)
		g.Write(w)
		w.Flush()
		f.Close()
		if !*quiet {
			printfLn("\n(graph also written to %s)", *dumpPath)
		}
	}
	if csvQ.set || jsonQ.set {

		n := jsonQ.n
		if csvQ.set {
			n = csvQ.n
		}
		if n < 1 || n > len(cat) {
			fmt.Fprintf(os.Stderr, "no query %d\n", n)
			out.Flush()
			return 2
		}
		q := cat[n-1]
		res := g.runQuestion(q, *modLike, *limit)
		if csvQ.set {
			writeCSV(out, res, q.name)
		} else {
			writeJSON(out, res, q.name)
		}
		out.Flush()
		return 0
	}
	if !*quiet {
		took := time.Since(t0).Seconds()
		if *loadASTPath != "" {
			printfLn("codegraph-python: %d files loaded from AST in %.1fs module=%s limit=%s",
				len(g.Files), took, *modLike, limitText(*limit))
		} else {
			printfLn("codegraph-python: %d files parsed into memory in %.1fs module=%s limit=%s",
				len(recs), took, *modLike, limitText(*limit))
		}
	}
	if *report {
		g.report()
	}
	sel := which
	if len(sel) == 0 {
		for i := range cat {
			sel = append(sel, i+1)
		}
	}
	for _, k := range sel {
		if k < 1 || k > len(cat) {
			continue
		}
		q := cat[k-1]
		printfLn("\n%s", strings.Repeat("=", 78))
		printfLn("Q%d. %s -- %s", k, q.name, q.title)
		printfLn("%s", strings.Repeat("-", 78))
		for line := range strings.SplitSeq(q.notes, "\n") {
			printfLn(" %s", line)
		}
		printfLn("")
		res := g.runQuestion(q, *modLike, *limit)
		renderRows(res.cols, res.rows)
	}
	out.Flush()
	if *memProf != "" {
		f, err := os.Create(*memProf)
		if err != nil {
			fmt.Fprintf(os.Stderr, "could not write %s: %v\n", *memProf, err)
			return 2
		}

		runtime.GC()
		pprof.Lookup("allocs").WriteTo(f, 0)
		f.Close()
	}
	if *blockProf != "" {
		runtime.SetBlockProfileRate(1)
		f, _ := os.Create(*blockProf)
		pprof.Lookup("block").WriteTo(f, 0)
		f.Close()
	}
	if *mutexProf != "" {
		runtime.SetMutexProfileFraction(1)
		f, _ := os.Create(*mutexProf)
		pprof.Lookup("mutex").WriteTo(f, 0)
		f.Close()
	}
	return 0
}

func needsValue(a string) bool {
	switch strings.TrimLeft(a, "-") {
	case "module", "limit", "dump", "only", "workers", "cpuprofile", "memprofile",
		"profilems", "blockprofile", "mutexprofile", "csv", "json",
		"save-ast", "load-ast":
		return true
	}
	return false
}

func limitText(n int) string {
	if n < 0 {
		return "all"
	}
	return strconv.Itoa(n)
}

func (g *Graph) fillMeta(root string, nParsed, nFailed, nImp int32,
	resolved, external, unres int32) {
	abs, _ := filepath.Abs(root)
	g.setMeta("schema_version", strconv.Itoa(schemaVersion))
	g.setMeta("lang", "python")
	g.setMeta("target", target)
	g.setMeta("root", abs)
	g.setMeta("parse_mode", "go-tree-sitter")
	g.setMeta("parser", "tree-sitter-python grammar via the official tree-sitter CLI")
	g.setMeta("files_parsed", strconv.Itoa(int(nParsed)))
	g.setMeta("files_failed", strconv.Itoa(int(nFailed)))
	g.setMeta("imports_resolved", sprintf("%d of %d import rows point at a file in this tree",
		nImp, len(g.Imports)))
	scope := max(resolved+unres, 1)
	g.setMeta("calls_resolved", sprintf(
		"%d in-tree / %d external / %d unresolved (%d%% of in-scope calls resolved)",
		resolved, external, unres, 100*resolved/scope))
}

func sortEdges(e []Edge) {
	sort.Slice(e, func(i, j int) bool {
		if e[i].CallerID != e[j].CallerID {
			return e[i].CallerID < e[j].CallerID
		}
		return e[i].CalleeID < e[j].CalleeID
	})
}

func sortCallsites(c []Callsite) {
	sort.Slice(c, func(i, j int) bool {
		if c[i].CallerID != c[j].CallerID {
			return c[i].CallerID < c[j].CallerID
		}
		if c[i].CalleeID != c[j].CalleeID {
			return c[i].CalleeID < c[j].CalleeID
		}
		return c[i].Line < c[j].Line
	})
}

func sortUnresolved(u []Unresolved) {
	sort.Slice(u, func(i, j int) bool {
		if u[i].CallerID != u[j].CallerID {
			return u[i].CallerID < u[j].CallerID
		}
		return u[i].Name < u[j].Name
	})
}

func strconvItoa(n int) string { return strconv.Itoa(n) }

const cgasMagic = "CGAS"

const (
	cgasVersion    = 2
	cgasHeaderSz   = 32
	cgasSecSz      = 24
	cgasNSec       = 30
	cgasSymRowSz   = 462
	cgasParamRowSz = 27
)

const (
	cgasSecStrings uint32 = 1 + iota
	cgasSecTrees
	cgasSecTreeDir
	cgasSecMods
	cgasSecFiles
	cgasSecSyms
	cgasSecParams
	cgasSecFields
	cgasSecLocals
	cgasSecImports
	cgasSecHaz
	cgasSecAttrs
	cgasSecLits
	cgasSecEnums
	cgasSecMark
	cgasSecHandlers
	cgasSecDyn
	cgasSecComps
	cgasSecModVars
	cgasSecExports
	cgasSecInputs
	cgasSecSecrets
	cgasSecAPIs
	cgasSecClasses
	cgasSecEdges
	cgasSecSites
	cgasSecUnres
	cgasSecMeta
	cgasSecStrPos
	cgasSecStrLn
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

type cgasMetaRow [2]uint32

var (
	moduleStrOffs = []uintptr{
		unsafe.Offsetof(Module{}.Name),
		unsafe.Offsetof(Module{}.Kind),
	}
	fileStrOffs = []uintptr{
		unsafe.Offsetof(File{}.Path),
		unsafe.Offsetof(File{}.Dir),
		unsafe.Offsetof(File{}.Basename),
		unsafe.Offsetof(File{}.Ext),
		unsafe.Offsetof(File{}.SHA1),
	}
	symStrOffs = []uintptr{
		unsafe.Offsetof(Symbol{}.Name),
		unsafe.Offsetof(Symbol{}.QualName),
		unsafe.Offsetof(Symbol{}.Kind),
		unsafe.Offsetof(Symbol{}.Signature),
		unsafe.Offsetof(Symbol{}.ReturnType),
		unsafe.Offsetof(Symbol{}.Visibility),
	}
	paramStrOffs = []uintptr{
		unsafe.Offsetof(Param{}.Name),
		unsafe.Offsetof(Param{}.Type),
		unsafe.Offsetof(Param{}.DefaultValue),
	}
	fieldStrOffs = []uintptr{
		unsafe.Offsetof(Field{}.Name),
		unsafe.Offsetof(Field{}.Type),
		unsafe.Offsetof(Field{}.Visibility),
	}
	localStrOffs = []uintptr{
		unsafe.Offsetof(LocalVar{}.Name),
		unsafe.Offsetof(LocalVar{}.Type),
	}
	importStrOffs = []uintptr{
		unsafe.Offsetof(Import{}.Target),
		unsafe.Offsetof(Import{}.Alias),
		unsafe.Offsetof(Import{}.Kind),
	}
	hazardStrOffs = []uintptr{
		unsafe.Offsetof(Hazard{}.Pattern),
		unsafe.Offsetof(Hazard{}.Category),
	}
	attrStrOffs = []uintptr{
		unsafe.Offsetof(Attribute{}.Name),
		unsafe.Offsetof(Attribute{}.Args),
	}
	litStrOffs = []uintptr{
		unsafe.Offsetof(Literal{}.Kind),
		unsafe.Offsetof(Literal{}.Value),
	}
	enumStrOffs = []uintptr{
		unsafe.Offsetof(EnumMember{}.Name),
		unsafe.Offsetof(EnumMember{}.Value),
	}
	markerStrOffs = []uintptr{
		unsafe.Offsetof(Marker{}.Kind),
		unsafe.Offsetof(Marker{}.Text),
	}
	handlerStrOffs = []uintptr{
		unsafe.Offsetof(Handler{}.Types),
	}
	dynStrOffs = []uintptr{
		unsafe.Offsetof(DynamicSite{}.Kind),
		unsafe.Offsetof(DynamicSite{}.Expr),
	}
	compStrOffs = []uintptr{
		unsafe.Offsetof(Comprehension{}.Kind),
	}
	modVarStrOffs = []uintptr{
		unsafe.Offsetof(ModuleVar{}.Name),
		unsafe.Offsetof(ModuleVar{}.Type),
	}
	exportStrOffs = []uintptr{
		unsafe.Offsetof(AllExport{}.Name),
	}
	inputStrOffs = []uintptr{
		unsafe.Offsetof(UserInputSite{}.Var),
		unsafe.Offsetof(UserInputSite{}.Kind),
	}
	secretStrOffs = []uintptr{
		unsafe.Offsetof(SecretCandidate{}.Value),
	}
	apiStrOffs = []uintptr{
		unsafe.Offsetof(APISite{}.Kind),
		unsafe.Offsetof(APISite{}.Expr),
	}
	classStrOffs = []uintptr{
		unsafe.Offsetof(ClassInfo{}.Bases),
	}
	unresStrOffs = []uintptr{
		unsafe.Offsetof(Unresolved{}.Name),
	}
	metaStrOffs = []uintptr{0, 4}
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
	fail(unsafe.Sizeof(tsRec{}) == 32, "tsRec must be the 32-byte fixed stride")
	fail(unsafe.Sizeof(cgasMetaRow{}) == 8, "meta row must be two uint32 words")
	fail(unsafe.Sizeof(cgasSec{}) == 24, "section entry must be 24 bytes")
	fail(unsafe.Sizeof(cgasHeader{}) == 32, "header must be 32 bytes")
	for _, t := range []reflect.Type{
		reflect.TypeOf(tsRec{}),
		reflect.TypeOf(Module{}),
		reflect.TypeOf(File{}),
		reflect.TypeOf(Symbol{}),
		reflect.TypeOf(Param{}),
		reflect.TypeOf(Field{}),
		reflect.TypeOf(LocalVar{}),
		reflect.TypeOf(Import{}),
		reflect.TypeOf(Hazard{}),
		reflect.TypeOf(Attribute{}),
		reflect.TypeOf(Literal{}),
		reflect.TypeOf(EnumMember{}),
		reflect.TypeOf(Marker{}),
		reflect.TypeOf(Handler{}),
		reflect.TypeOf(DynamicSite{}),
		reflect.TypeOf(Comprehension{}),
		reflect.TypeOf(ModuleVar{}),
		reflect.TypeOf(AllExport{}),
		reflect.TypeOf(UserInputSite{}),
		reflect.TypeOf(SecretCandidate{}),
		reflect.TypeOf(APISite{}),
		reflect.TypeOf(ClassInfo{}),
		reflect.TypeOf(Edge{}),
		reflect.TypeOf(Callsite{}),
		reflect.TypeOf(Unresolved{}),
		reflect.TypeOf(cgasMetaRow{}),
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

func cgasRawBytes[T any](rows []T) []byte {
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

func cgPutU16b(b []byte, o int, v uint16) { b[o] = byte(v); b[o+1] = byte(v >> 8) }

func cgPutU32b(b []byte, o int, v uint32) {
	b[o] = byte(v)
	b[o+1] = byte(v >> 8)
	b[o+2] = byte(v >> 16)
	b[o+3] = byte(v >> 24)
}

func cgGetU16b(b []byte, o int) uint16 { return uint16(b[o]) | uint16(b[o+1])<<8 }

func cgGetU32b(b []byte, o int) uint32 {
	return uint32(b[o]) | uint32(b[o+1])<<8 | uint32(b[o+2])<<16 | uint32(b[o+3])<<24
}

func cgPutU64b(b []byte, o int, v uint64) {
	for i := 0; i < 8; i++ {
		b[o+i] = byte(v >> (8 * i))
	}
}

func cgGetU64b(b []byte, o int) uint64 {
	var v uint64
	for i := 0; i < 8; i++ {
		v |= uint64(b[o+i]) << (8 * i)
	}
	return v
}

func cgasStreamParams(w *bufio.Writer, rows []Param) error {
	const chunk = 4096
	scratch := make([]byte, chunk*cgasParamRowSz)
	for start := 0; start < len(rows); start += chunk {
		end := start + chunk
		if end > len(rows) {
			end = len(rows)
		}
		for i := start; i < end; i++ {
			p := &rows[i]
			o := (i - start) * cgasParamRowSz
			if p.Pos < 0 || p.Pos > 0xFFFF || p.TypeDepth < 0 || p.TypeDepth > 0xFFFF ||
				p.IsOptional < 0 || p.IsOptional > 0xFF || p.IsVariadic < 0 || p.IsVariadic > 0xFF ||
				p.IsRef < 0 || p.IsRef > 0xFF || p.IsMutable < 0 || p.IsMutable > 0xFF ||
				p.IsNullable < 0 || p.IsNullable > 0xFF || p.IsGeneric < 0 || p.IsGeneric > 0xFF ||
				p.IsUntyped < 0 || p.IsUntyped > 0xFF {
				return fmt.Errorf("params row %d: value exceeds the narrow state range", i)
			}
			cgPutU32b(scratch, o, uint32(p.SymbolID))
			cgPutU16b(scratch, o+4, uint16(p.Pos))
			cgPutU32b(scratch, o+6, p.Name)
			cgPutU32b(scratch, o+10, p.Type)
			cgPutU32b(scratch, o+14, p.DefaultValue)
			scratch[o+18] = byte(p.IsOptional)
			scratch[o+19] = byte(p.IsVariadic)
			scratch[o+20] = byte(p.IsRef)
			scratch[o+21] = byte(p.IsMutable)
			scratch[o+22] = byte(p.IsNullable)
			scratch[o+23] = byte(p.IsGeneric)
			scratch[o+24] = byte(p.IsUntyped)
			cgPutU16b(scratch, o+25, uint16(p.TypeDepth))
		}
		if _, err := w.Write(scratch[:(end-start)*cgasParamRowSz]); err != nil {
			return err
		}
	}
	return nil
}

func cgasDecodeParams(mem []byte, off, ln uint64) ([]Param, error) {
	if ln == 0 {
		return nil, nil
	}
	if ln%cgasParamRowSz != 0 {
		return nil, fmt.Errorf("params: section length %d is not a multiple of row size %d", ln, cgasParamRowSz)
	}
	if off < uint64(cgasHeaderSz) || off > uint64(len(mem)) || ln > uint64(len(mem))-off {
		return nil, fmt.Errorf("params: section lies outside the file")
	}
	rows := make([]Param, ln/cgasParamRowSz)
	for i := range rows {
		o := int(off) + i*cgasParamRowSz
		r := &rows[i]
		r.SymbolID = int32(cgGetU32b(mem, o))
		r.Pos = int32(cgGetU16b(mem, o+4))
		r.Name = cgGetU32b(mem, o+6)
		r.Type = cgGetU32b(mem, o+10)
		r.DefaultValue = cgGetU32b(mem, o+14)
		r.IsOptional = int32(mem[o+18])
		r.IsVariadic = int32(mem[o+19])
		r.IsRef = int32(mem[o+20])
		r.IsMutable = int32(mem[o+21])
		r.IsNullable = int32(mem[o+22])
		r.IsGeneric = int32(mem[o+23])
		r.IsUntyped = int32(mem[o+24])
		r.TypeDepth = int32(cgGetU16b(mem, o+25))
	}
	return rows, nil
}

func cgasStreamSyms(w *bufio.Writer, rows []Symbol) error {
	const chunk = 256
	scratch := make([]byte, chunk*cgasSymRowSz)
	overflow := -1
	u16 := func(v int32) uint16 {
		if overflow < 0 && (v < 0 || int64(v) > 0xFFFF) {
			overflow = int(v)
		}
		return uint16(v)
	}
	for start := 0; start < len(rows); start += chunk {
		end := start + chunk
		if end > len(rows) {
			end = len(rows)
		}
		for i := start; i < end; i++ {
			s := &rows[i]
			o := (i - start) * cgasSymRowSz
			cgPutU32b(scratch, o, uint32(s.ID))
			cgPutU32b(scratch, o+4, uint32(s.FileID))
			cgPutU32b(scratch, o+8, uint32(s.ModuleID))
			cgPutU32b(scratch, o+12, uint32(s.ParentID))
			cgPutU32b(scratch, o+16, s.Name)
			cgPutU32b(scratch, o+20, s.QualName)
			cgPutU32b(scratch, o+24, s.Kind)
			cgPutU16b(scratch, o+28, u16(s.LineStart))
			cgPutU16b(scratch, o+30, u16(s.LineEnd))
			cgPutU16b(scratch, o+32, u16(s.NLines))
			cgPutU32b(scratch, o+34, s.Signature)
			cgPutU32b(scratch, o+38, s.ReturnType)
			cgPutU32b(scratch, o+42, s.Visibility)
			cgPutU16b(scratch, o+46, u16(s.NParams))
			cgPutU16b(scratch, o+48, u16(s.NOptionalParams))
			cgPutU16b(scratch, o+50, u16(s.NGenericParams))
			cgPutU16b(scratch, o+52, u16(s.IsPublic))
			cgPutU16b(scratch, o+54, u16(s.IsStatic))
			cgPutU16b(scratch, o+56, u16(s.IsAsync))
			cgPutU16b(scratch, o+58, u16(s.IsGenerator))
			cgPutU16b(scratch, o+60, u16(s.IsAbstract))
			cgPutU16b(scratch, o+62, u16(s.IsOverride))
			cgPutU16b(scratch, o+64, u16(s.IsTest))
			cgPutU16b(scratch, o+66, u16(s.IsDeprecated))
			cgPutU16b(scratch, o+68, u16(s.IsEntrypoint))
			cgPutU16b(scratch, o+70, u16(s.IsGenerated))
			cgPutU16b(scratch, o+72, u16(s.SLOC))
			cgPutU16b(scratch, o+74, u16(s.NCommentLines))
			cgPutU16b(scratch, o+76, u16(s.NDocLines))
			cgPutU16b(scratch, o+78, u16(s.HasDoc))
			cgPutU16b(scratch, o+80, u16(s.Cyclomatic))
			cgPutU16b(scratch, o+82, u16(s.Cognitive))
			cgPutU16b(scratch, o+84, u16(s.MaxNesting))
			cgPutU32b(scratch, o+86, uint32(s.NTokens))
			cgPutU32b(scratch, o+90, uint32(s.NOperators))
			cgPutU32b(scratch, o+94, uint32(s.NOperands))
			cgPutU32b(scratch, o+98, uint32(s.NDistinctOps))
			cgPutU32b(scratch, o+102, uint32(s.NDistinctOperand))
			cgPutU32b(scratch, o+106, uint32(s.NStringLit))
			cgPutU32b(scratch, o+110, uint32(s.NRegexLit))
			cgPutU32b(scratch, o+114, uint32(s.NFloatLit))
			cgPutU32b(scratch, o+118, uint32(s.NMagic))
			cgPutU64b(scratch, o+122, uint64(s.HalsteadVolume))
			cgPutU16b(scratch, o+130, u16(s.Maintainability))
			cgPutU16b(scratch, o+132, u16(s.NLoops))
			cgPutU16b(scratch, o+134, u16(s.NBranches))
			cgPutU16b(scratch, o+136, u16(s.NReturns))
			cgPutU16b(scratch, o+138, u16(s.NEarlyReturns))
			cgPutU16b(scratch, o+140, u16(s.NSwitch))
			cgPutU16b(scratch, o+142, u16(s.NCases))
			cgPutU16b(scratch, o+144, u16(s.NTernary))
			cgPutU16b(scratch, o+146, u16(s.NLogical))
			cgPutU16b(scratch, o+148, u16(s.NTry))
			cgPutU16b(scratch, o+150, u16(s.NCatch))
			cgPutU16b(scratch, o+152, u16(s.NCatchBroad))
			cgPutU16b(scratch, o+154, u16(s.NCatchEmpty))
			cgPutU16b(scratch, o+156, u16(s.NFinally))
			cgPutU16b(scratch, o+158, u16(s.NThrow))
			cgPutU16b(scratch, o+160, u16(s.NLabels))
			cgPutU16b(scratch, o+162, u16(s.NGotos))
			cgPutU16b(scratch, o+164, u16(s.MaxLoopDepth))
			cgPutU16b(scratch, o+166, u16(s.CallInLoop))
			cgPutU16b(scratch, o+168, u16(s.AllocInLoop))
			cgPutU16b(scratch, o+170, u16(s.IOInLoop))
			cgPutU16b(scratch, o+172, u16(s.AwaitInLoop))
			cgPutU16b(scratch, o+174, u16(s.LockInLoop))
			cgPutU16b(scratch, o+176, u16(s.ConcatInLoop))
			cgPutU16b(scratch, o+178, u16(s.RegexInLoop))
			cgPutU16b(scratch, o+180, u16(s.QueryInLoop))
			cgPutU16b(scratch, o+182, u16(s.BranchInLoop))
			cgPutU16b(scratch, o+184, u16(s.NLocals))
			cgPutU16b(scratch, o+186, u16(s.NAssign))
			cgPutU16b(scratch, o+188, u16(s.NCompoundAssign))
			cgPutU16b(scratch, o+190, u16(s.NIncdec))
			cgPutU16b(scratch, o+192, u16(s.NCmp))
			cgPutU16b(scratch, o+194, u16(s.NBitop))
			cgPutU16b(scratch, o+196, u16(s.NShift))
			cgPutU16b(scratch, o+198, u16(s.NArith))
			cgPutU16b(scratch, o+200, u16(s.NNullCheck))
			cgPutU16b(scratch, o+202, u16(s.NSubscript))
			cgPutU16b(scratch, o+204, u16(s.NMemberAccess))
			cgPutU16b(scratch, o+206, u16(s.NLambda))
			cgPutU16b(scratch, o+208, u16(s.NClosureCapture))
			cgPutU16b(scratch, o+210, u16(s.NCalls))
			cgPutU16b(scratch, o+212, u16(s.NUniqueCalls))
			cgPutU16b(scratch, o+214, u16(s.NDynamicCalls))
			cgPutU16b(scratch, o+216, u16(s.NUnresolvedCalls))
			cgPutU16b(scratch, o+218, u16(s.FanIn))
			cgPutU16b(scratch, o+220, u16(s.FanOut))
			cgPutU16b(scratch, o+222, u16(s.NCallsites))
			cgPutU16b(scratch, o+224, u16(s.IsRecursive))
			cgPutU16b(scratch, o+226, u16(s.IsLeaf))
			cgPutU16b(scratch, o+228, u16(s.IsRoot))
			cgPutU16b(scratch, o+230, u16(s.NHazards))
			cgPutU16b(scratch, o+232, u16(s.RiskScore))
			cgPutU16b(scratch, o+234, u16(s.NExec))
			cgPutU16b(scratch, o+236, u16(s.NDeserialize))
			cgPutU16b(scratch, o+238, u16(s.NIO))
			cgPutU16b(scratch, o+240, u16(s.NNet))
			cgPutU16b(scratch, o+242, u16(s.NSql))
			cgPutU16b(scratch, o+244, u16(s.NCrypto))
			cgPutU16b(scratch, o+246, u16(s.NReflect))
			cgPutU16b(scratch, o+248, u16(s.NConcurrency))
			cgPutU16b(scratch, o+250, u16(s.NBlocking))
			cgPutU16b(scratch, o+252, u16(s.NResource))
			cgPutU16b(scratch, o+254, u16(s.NShell))
			cgPutU16b(scratch, o+256, u16(s.NDecorators))
			cgPutU16b(scratch, o+258, u16(s.NComprehension))
			cgPutU16b(scratch, o+260, u16(s.NNestedComprehension))
			cgPutU16b(scratch, o+262, u16(s.NAsyncComprehension))
			cgPutU16b(scratch, o+264, u16(s.NCompGenerators))
			cgPutU16b(scratch, o+266, u16(s.NCompIfs))
			cgPutU16b(scratch, o+268, u16(s.NGenexp))
			cgPutU16b(scratch, o+270, u16(s.NYield))
			cgPutU16b(scratch, o+272, u16(s.NYieldFrom))
			cgPutU16b(scratch, o+274, u16(s.NAwait))
			cgPutU16b(scratch, o+276, u16(s.NGlobalStmt))
			cgPutU16b(scratch, o+278, u16(s.NNonlocal))
			cgPutU16b(scratch, o+280, u16(s.NBareExcept))
			cgPutU16b(scratch, o+282, u16(s.NCatchSwallow))
			cgPutU16b(scratch, o+284, u16(s.NReraise))
			cgPutU16b(scratch, o+286, u16(s.NWith))
			cgPutU16b(scratch, o+288, u16(s.NAsyncWith))
			cgPutU16b(scratch, o+290, u16(s.NCtxManagers))
			cgPutU16b(scratch, o+292, u16(s.NFstring))
			cgPutU16b(scratch, o+294, u16(s.NIsinstance))
			cgPutU16b(scratch, o+296, u16(s.NSuper))
			cgPutU16b(scratch, o+298, u16(s.NWalrus))
			cgPutU16b(scratch, o+300, u16(s.NMatch))
			cgPutU16b(scratch, o+302, u16(s.NAssert))
			cgPutU16b(scratch, o+304, u16(s.NDel))
			cgPutU16b(scratch, o+306, u16(s.NPrint))
			cgPutU16b(scratch, o+308, u16(s.NOpen))
			cgPutU16b(scratch, o+310, u16(s.NSelfAttr))
			cgPutU16b(scratch, o+312, u16(s.NInnerFunction))
			cgPutU16b(scratch, o+314, u16(s.NInnerClass))
			cgPutU16b(scratch, o+316, u16(s.NMutableDefault))
			cgPutU16b(scratch, o+318, u16(s.NStarArgs))
			cgPutU16b(scratch, o+320, u16(s.NKwargs))
			cgPutU16b(scratch, o+322, u16(s.NDefaultArgs))
			cgPutU16b(scratch, o+324, u16(s.NKwonlyArgs))
			cgPutU16b(scratch, o+326, u16(s.NPosonlyArgs))
			cgPutU16b(scratch, o+328, u16(s.NAnnotatedParams))
			cgPutU16b(scratch, o+330, u16(s.NUntypedParams))
			cgPutU16b(scratch, o+332, u16(s.HasReturnType))
			cgPutU16b(scratch, o+334, u16(s.NAppendInLoop))
			cgPutU16b(scratch, o+336, u16(s.LenInLoop))
			cgPutU16b(scratch, o+338, u16(s.AppendInLoop))
			cgPutU16b(scratch, o+340, u16(s.TryInLoop))
			cgPutU16b(scratch, o+342, u16(s.NRangeLen))
			cgPutU16b(scratch, o+344, u16(s.NTryInLoop))
			cgPutU16b(scratch, o+346, u16(s.NLoopElse))
			cgPutU16b(scratch, o+348, u16(s.NRegexCompile))
			cgPutU16b(scratch, o+350, u16(s.NRegexCall))
			cgPutU16b(scratch, o+352, u16(s.NSqlLiteral))
			cgPutU16b(scratch, o+354, u16(s.NSqlFstring))
			cgPutU16b(scratch, o+356, u16(s.NSqlConcat))
			cgPutU16b(scratch, o+358, u16(s.NSqlFormat))
			cgPutU16b(scratch, o+360, u16(s.NShellTrue))
			cgPutU16b(scratch, o+362, u16(s.NAnnotatedAssign))
			cgPutU16b(scratch, o+364, u16(s.NTryElse))
			cgPutU16b(scratch, o+366, u16(s.NPickleLoad))
			cgPutU16b(scratch, o+368, u16(s.NYamlLoad))
			cgPutU16b(scratch, o+370, u16(s.NWeakRandom))
			cgPutU16b(scratch, o+372, u16(s.NWeakHash))
			cgPutU16b(scratch, o+374, u16(s.NEvalExec))
			cgPutU16b(scratch, o+376, u16(s.NOSystem))
			cgPutU16b(scratch, o+378, u16(s.NInsecureTemp))
			cgPutU16b(scratch, o+380, u16(s.NSleepInLoop))
			cgPutU16b(scratch, o+382, u16(s.NDynamicAttr))
			cgPutU16b(scratch, o+384, u16(s.NDictGetInLoop))
			cgPutU16b(scratch, o+386, u16(s.NOpenNoEncoding))
			cgPutU16b(scratch, o+388, u16(s.NDatetime))
			cgPutU16b(scratch, o+390, u16(s.NRequestNoTimeout))
			cgPutU16b(scratch, o+392, u16(s.NRedirect))
			cgPutU16b(scratch, o+394, u16(s.NAuthCall))
			cgPutU16b(scratch, o+396, u16(s.NFetch))
			cgPutU16b(scratch, o+398, u16(s.NXxeParser))
			cgPutU16b(scratch, o+400, u16(s.NDynamicOpen))
			cgPutU16b(scratch, o+402, u16(s.NUploadSave))
			cgPutU16b(scratch, o+404, u16(s.NZipRead))
			cgPutU16b(scratch, o+406, u16(s.NLogCall))
			cgPutU16b(scratch, o+408, u16(s.NAssertInLoop))
			cgPutU16b(scratch, o+410, u16(s.NSubprocess))
			cgPutU16b(scratch, o+412, u16(s.NFormatInLoop))
			cgPutU16b(scratch, o+414, u16(s.NElif))
			cgPutU16b(scratch, o+416, u16(s.NExternalCalls))
			cgPutU16b(scratch, o+418, u16(s.NLoopClosure))
			cgPutU16b(scratch, o+420, u16(s.NBroadRaises))
			cgPutU16b(scratch, o+422, u16(s.NAutoescapeFalse))
			cgPutU16b(scratch, o+424, u16(s.IsProperty))
			cgPutU16b(scratch, o+426, u16(s.IsClassmethod))
			cgPutU16b(scratch, o+428, u16(s.IsStaticmethod))
			cgPutU16b(scratch, o+430, u16(s.IsDunder))
			cgPutU16b(scratch, o+432, u16(s.IsPrivate))
			cgPutU16b(scratch, o+434, u16(s.IsOverload))
			cgPutU16b(scratch, o+436, u16(s.IsContextmanager))
			cgPutU16b(scratch, o+438, u16(s.IsCached))
			cgPutU16b(scratch, o+440, u16(s.NestLevel))
			cgPutU16b(scratch, o+442, u16(s.NOrmQueryInLoop))
			cgPutU16b(scratch, o+444, u16(s.NCommitInLoop))
			cgPutU16b(scratch, o+446, u16(s.NOrmWrite))
			cgPutU16b(scratch, o+448, u16(s.NAtomic))
			cgPutU16b(scratch, o+450, u16(s.NAwaitInSyncWith))
			cgPutU16b(scratch, o+452, u16(s.NInScanLoop))
			cgPutU16b(scratch, o+454, u16(s.NResourceReturn))
			cgPutU16b(scratch, o+456, u16(s.NMarkSafe))
			cgPutU16b(scratch, o+458, u16(s.NMassAssign))
			cgPutU16b(scratch, o+460, u16(s.NVerifyFalse))
		}
		if _, err := w.Write(scratch[:(end-start)*cgasSymRowSz]); err != nil {
			return err
		}
	}
	if overflow >= 0 {
		return fmt.Errorf("symbols: value %d exceeds the u16 state range", overflow)
	}
	return nil
}

func cgasDecodeSyms(mem []byte, off, ln uint64) ([]Symbol, error) {
	if ln == 0 {
		return nil, nil
	}
	if ln%cgasSymRowSz != 0 {
		return nil, fmt.Errorf("symbols: section length %d is not a multiple of row size %d", ln, cgasSymRowSz)
	}
	if off < uint64(cgasHeaderSz) || off > uint64(len(mem)) || ln > uint64(len(mem))-off {
		return nil, fmt.Errorf("symbols: section lies outside the file")
	}
	rows := make([]Symbol, ln/cgasSymRowSz)
	for i := range rows {
		o := int(off) + i*cgasSymRowSz
		r := &rows[i]
		r.ID = int32(cgGetU32b(mem, o))
		r.FileID = int32(cgGetU32b(mem, o+4))
		r.ModuleID = int32(cgGetU32b(mem, o+8))
		r.ParentID = int32(cgGetU32b(mem, o+12))
		r.Name = cgGetU32b(mem, o+16)
		r.QualName = cgGetU32b(mem, o+20)
		r.Kind = cgGetU32b(mem, o+24)
		r.LineStart = int32(cgGetU16b(mem, o+28))
		r.LineEnd = int32(cgGetU16b(mem, o+30))
		r.NLines = int32(cgGetU16b(mem, o+32))
		r.Signature = cgGetU32b(mem, o+34)
		r.ReturnType = cgGetU32b(mem, o+38)
		r.Visibility = cgGetU32b(mem, o+42)
		r.NParams = int32(cgGetU16b(mem, o+46))
		r.NOptionalParams = int32(cgGetU16b(mem, o+48))
		r.NGenericParams = int32(cgGetU16b(mem, o+50))
		r.IsPublic = int32(cgGetU16b(mem, o+52))
		r.IsStatic = int32(cgGetU16b(mem, o+54))
		r.IsAsync = int32(cgGetU16b(mem, o+56))
		r.IsGenerator = int32(cgGetU16b(mem, o+58))
		r.IsAbstract = int32(cgGetU16b(mem, o+60))
		r.IsOverride = int32(cgGetU16b(mem, o+62))
		r.IsTest = int32(cgGetU16b(mem, o+64))
		r.IsDeprecated = int32(cgGetU16b(mem, o+66))
		r.IsEntrypoint = int32(cgGetU16b(mem, o+68))
		r.IsGenerated = int32(cgGetU16b(mem, o+70))
		r.SLOC = int32(cgGetU16b(mem, o+72))
		r.NCommentLines = int32(cgGetU16b(mem, o+74))
		r.NDocLines = int32(cgGetU16b(mem, o+76))
		r.HasDoc = int32(cgGetU16b(mem, o+78))
		r.Cyclomatic = int32(cgGetU16b(mem, o+80))
		r.Cognitive = int32(cgGetU16b(mem, o+82))
		r.MaxNesting = int32(cgGetU16b(mem, o+84))
		r.NTokens = int32(cgGetU32b(mem, o+86))
		r.NOperators = int32(cgGetU32b(mem, o+90))
		r.NOperands = int32(cgGetU32b(mem, o+94))
		r.NDistinctOps = int32(cgGetU32b(mem, o+98))
		r.NDistinctOperand = int32(cgGetU32b(mem, o+102))
		r.NStringLit = int32(cgGetU32b(mem, o+106))
		r.NRegexLit = int32(cgGetU32b(mem, o+110))
		r.NFloatLit = int32(cgGetU32b(mem, o+114))
		r.NMagic = int32(cgGetU32b(mem, o+118))
		r.HalsteadVolume = int64(cgGetU64b(mem, o+122))
		r.Maintainability = int32(cgGetU16b(mem, o+130))
		r.NLoops = int32(cgGetU16b(mem, o+132))
		r.NBranches = int32(cgGetU16b(mem, o+134))
		r.NReturns = int32(cgGetU16b(mem, o+136))
		r.NEarlyReturns = int32(cgGetU16b(mem, o+138))
		r.NSwitch = int32(cgGetU16b(mem, o+140))
		r.NCases = int32(cgGetU16b(mem, o+142))
		r.NTernary = int32(cgGetU16b(mem, o+144))
		r.NLogical = int32(cgGetU16b(mem, o+146))
		r.NTry = int32(cgGetU16b(mem, o+148))
		r.NCatch = int32(cgGetU16b(mem, o+150))
		r.NCatchBroad = int32(cgGetU16b(mem, o+152))
		r.NCatchEmpty = int32(cgGetU16b(mem, o+154))
		r.NFinally = int32(cgGetU16b(mem, o+156))
		r.NThrow = int32(cgGetU16b(mem, o+158))
		r.NLabels = int32(cgGetU16b(mem, o+160))
		r.NGotos = int32(cgGetU16b(mem, o+162))
		r.MaxLoopDepth = int32(cgGetU16b(mem, o+164))
		r.CallInLoop = int32(cgGetU16b(mem, o+166))
		r.AllocInLoop = int32(cgGetU16b(mem, o+168))
		r.IOInLoop = int32(cgGetU16b(mem, o+170))
		r.AwaitInLoop = int32(cgGetU16b(mem, o+172))
		r.LockInLoop = int32(cgGetU16b(mem, o+174))
		r.ConcatInLoop = int32(cgGetU16b(mem, o+176))
		r.RegexInLoop = int32(cgGetU16b(mem, o+178))
		r.QueryInLoop = int32(cgGetU16b(mem, o+180))
		r.BranchInLoop = int32(cgGetU16b(mem, o+182))
		r.NLocals = int32(cgGetU16b(mem, o+184))
		r.NAssign = int32(cgGetU16b(mem, o+186))
		r.NCompoundAssign = int32(cgGetU16b(mem, o+188))
		r.NIncdec = int32(cgGetU16b(mem, o+190))
		r.NCmp = int32(cgGetU16b(mem, o+192))
		r.NBitop = int32(cgGetU16b(mem, o+194))
		r.NShift = int32(cgGetU16b(mem, o+196))
		r.NArith = int32(cgGetU16b(mem, o+198))
		r.NNullCheck = int32(cgGetU16b(mem, o+200))
		r.NSubscript = int32(cgGetU16b(mem, o+202))
		r.NMemberAccess = int32(cgGetU16b(mem, o+204))
		r.NLambda = int32(cgGetU16b(mem, o+206))
		r.NClosureCapture = int32(cgGetU16b(mem, o+208))
		r.NCalls = int32(cgGetU16b(mem, o+210))
		r.NUniqueCalls = int32(cgGetU16b(mem, o+212))
		r.NDynamicCalls = int32(cgGetU16b(mem, o+214))
		r.NUnresolvedCalls = int32(cgGetU16b(mem, o+216))
		r.FanIn = int32(cgGetU16b(mem, o+218))
		r.FanOut = int32(cgGetU16b(mem, o+220))
		r.NCallsites = int32(cgGetU16b(mem, o+222))
		r.IsRecursive = int32(cgGetU16b(mem, o+224))
		r.IsLeaf = int32(cgGetU16b(mem, o+226))
		r.IsRoot = int32(cgGetU16b(mem, o+228))
		r.NHazards = int32(cgGetU16b(mem, o+230))
		r.RiskScore = int32(cgGetU16b(mem, o+232))
		r.NExec = int32(cgGetU16b(mem, o+234))
		r.NDeserialize = int32(cgGetU16b(mem, o+236))
		r.NIO = int32(cgGetU16b(mem, o+238))
		r.NNet = int32(cgGetU16b(mem, o+240))
		r.NSql = int32(cgGetU16b(mem, o+242))
		r.NCrypto = int32(cgGetU16b(mem, o+244))
		r.NReflect = int32(cgGetU16b(mem, o+246))
		r.NConcurrency = int32(cgGetU16b(mem, o+248))
		r.NBlocking = int32(cgGetU16b(mem, o+250))
		r.NResource = int32(cgGetU16b(mem, o+252))
		r.NShell = int32(cgGetU16b(mem, o+254))
		r.NDecorators = int32(cgGetU16b(mem, o+256))
		r.NComprehension = int32(cgGetU16b(mem, o+258))
		r.NNestedComprehension = int32(cgGetU16b(mem, o+260))
		r.NAsyncComprehension = int32(cgGetU16b(mem, o+262))
		r.NCompGenerators = int32(cgGetU16b(mem, o+264))
		r.NCompIfs = int32(cgGetU16b(mem, o+266))
		r.NGenexp = int32(cgGetU16b(mem, o+268))
		r.NYield = int32(cgGetU16b(mem, o+270))
		r.NYieldFrom = int32(cgGetU16b(mem, o+272))
		r.NAwait = int32(cgGetU16b(mem, o+274))
		r.NGlobalStmt = int32(cgGetU16b(mem, o+276))
		r.NNonlocal = int32(cgGetU16b(mem, o+278))
		r.NBareExcept = int32(cgGetU16b(mem, o+280))
		r.NCatchSwallow = int32(cgGetU16b(mem, o+282))
		r.NReraise = int32(cgGetU16b(mem, o+284))
		r.NWith = int32(cgGetU16b(mem, o+286))
		r.NAsyncWith = int32(cgGetU16b(mem, o+288))
		r.NCtxManagers = int32(cgGetU16b(mem, o+290))
		r.NFstring = int32(cgGetU16b(mem, o+292))
		r.NIsinstance = int32(cgGetU16b(mem, o+294))
		r.NSuper = int32(cgGetU16b(mem, o+296))
		r.NWalrus = int32(cgGetU16b(mem, o+298))
		r.NMatch = int32(cgGetU16b(mem, o+300))
		r.NAssert = int32(cgGetU16b(mem, o+302))
		r.NDel = int32(cgGetU16b(mem, o+304))
		r.NPrint = int32(cgGetU16b(mem, o+306))
		r.NOpen = int32(cgGetU16b(mem, o+308))
		r.NSelfAttr = int32(cgGetU16b(mem, o+310))
		r.NInnerFunction = int32(cgGetU16b(mem, o+312))
		r.NInnerClass = int32(cgGetU16b(mem, o+314))
		r.NMutableDefault = int32(cgGetU16b(mem, o+316))
		r.NStarArgs = int32(cgGetU16b(mem, o+318))
		r.NKwargs = int32(cgGetU16b(mem, o+320))
		r.NDefaultArgs = int32(cgGetU16b(mem, o+322))
		r.NKwonlyArgs = int32(cgGetU16b(mem, o+324))
		r.NPosonlyArgs = int32(cgGetU16b(mem, o+326))
		r.NAnnotatedParams = int32(cgGetU16b(mem, o+328))
		r.NUntypedParams = int32(cgGetU16b(mem, o+330))
		r.HasReturnType = int32(cgGetU16b(mem, o+332))
		r.NAppendInLoop = int32(cgGetU16b(mem, o+334))
		r.LenInLoop = int32(cgGetU16b(mem, o+336))
		r.AppendInLoop = int32(cgGetU16b(mem, o+338))
		r.TryInLoop = int32(cgGetU16b(mem, o+340))
		r.NRangeLen = int32(cgGetU16b(mem, o+342))
		r.NTryInLoop = int32(cgGetU16b(mem, o+344))
		r.NLoopElse = int32(cgGetU16b(mem, o+346))
		r.NRegexCompile = int32(cgGetU16b(mem, o+348))
		r.NRegexCall = int32(cgGetU16b(mem, o+350))
		r.NSqlLiteral = int32(cgGetU16b(mem, o+352))
		r.NSqlFstring = int32(cgGetU16b(mem, o+354))
		r.NSqlConcat = int32(cgGetU16b(mem, o+356))
		r.NSqlFormat = int32(cgGetU16b(mem, o+358))
		r.NShellTrue = int32(cgGetU16b(mem, o+360))
		r.NAnnotatedAssign = int32(cgGetU16b(mem, o+362))
		r.NTryElse = int32(cgGetU16b(mem, o+364))
		r.NPickleLoad = int32(cgGetU16b(mem, o+366))
		r.NYamlLoad = int32(cgGetU16b(mem, o+368))
		r.NWeakRandom = int32(cgGetU16b(mem, o+370))
		r.NWeakHash = int32(cgGetU16b(mem, o+372))
		r.NEvalExec = int32(cgGetU16b(mem, o+374))
		r.NOSystem = int32(cgGetU16b(mem, o+376))
		r.NInsecureTemp = int32(cgGetU16b(mem, o+378))
		r.NSleepInLoop = int32(cgGetU16b(mem, o+380))
		r.NDynamicAttr = int32(cgGetU16b(mem, o+382))
		r.NDictGetInLoop = int32(cgGetU16b(mem, o+384))
		r.NOpenNoEncoding = int32(cgGetU16b(mem, o+386))
		r.NDatetime = int32(cgGetU16b(mem, o+388))
		r.NRequestNoTimeout = int32(cgGetU16b(mem, o+390))
		r.NRedirect = int32(cgGetU16b(mem, o+392))
		r.NAuthCall = int32(cgGetU16b(mem, o+394))
		r.NFetch = int32(cgGetU16b(mem, o+396))
		r.NXxeParser = int32(cgGetU16b(mem, o+398))
		r.NDynamicOpen = int32(cgGetU16b(mem, o+400))
		r.NUploadSave = int32(cgGetU16b(mem, o+402))
		r.NZipRead = int32(cgGetU16b(mem, o+404))
		r.NLogCall = int32(cgGetU16b(mem, o+406))
		r.NAssertInLoop = int32(cgGetU16b(mem, o+408))
		r.NSubprocess = int32(cgGetU16b(mem, o+410))
		r.NFormatInLoop = int32(cgGetU16b(mem, o+412))
		r.NElif = int32(cgGetU16b(mem, o+414))
		r.NExternalCalls = int32(cgGetU16b(mem, o+416))
		r.NLoopClosure = int32(cgGetU16b(mem, o+418))
		r.NBroadRaises = int32(cgGetU16b(mem, o+420))
		r.NAutoescapeFalse = int32(cgGetU16b(mem, o+422))
		r.IsProperty = int32(cgGetU16b(mem, o+424))
		r.IsClassmethod = int32(cgGetU16b(mem, o+426))
		r.IsStaticmethod = int32(cgGetU16b(mem, o+428))
		r.IsDunder = int32(cgGetU16b(mem, o+430))
		r.IsPrivate = int32(cgGetU16b(mem, o+432))
		r.IsOverload = int32(cgGetU16b(mem, o+434))
		r.IsContextmanager = int32(cgGetU16b(mem, o+436))
		r.IsCached = int32(cgGetU16b(mem, o+438))
		r.NestLevel = int32(cgGetU16b(mem, o+440))
		r.NOrmQueryInLoop = int32(cgGetU16b(mem, o+442))
		r.NCommitInLoop = int32(cgGetU16b(mem, o+444))
		r.NOrmWrite = int32(cgGetU16b(mem, o+446))
		r.NAtomic = int32(cgGetU16b(mem, o+448))
		r.NAwaitInSyncWith = int32(cgGetU16b(mem, o+450))
		r.NInScanLoop = int32(cgGetU16b(mem, o+452))
		r.NResourceReturn = int32(cgGetU16b(mem, o+454))
		r.NMarkSafe = int32(cgGetU16b(mem, o+456))
		r.NMassAssign = int32(cgGetU16b(mem, o+458))
		r.NVerifyFalse = int32(cgGetU16b(mem, o+460))
	}
	return rows, nil
}
func cgasCheckIDs[T any](rows []T, offs []uintptr, nStr uint32, what string) error {
	if len(rows) == 0 || len(offs) == 0 {
		return nil
	}
	size := unsafe.Sizeof(rows[0])
	base := unsafe.Pointer(&rows[0])
	for i := range rows {
		row := unsafe.Pointer(uintptr(base) + uintptr(i)*size)
		for _, o := range offs {
			id := *(*uint32)(unsafe.Pointer(uintptr(row) + o))
			if uint64(id) >= uint64(nStr) {
				return fmt.Errorf("%s: row %d references string %d of %d", what, i, id, nStr)
			}
		}
	}
	return nil
}

func saveASTFile(g *Graph, path string) (int64, error) {
	cgasGuard()
	arena := g.Strings.buf
	if len(arena) == 0 {
		arena = nil
	}
	body := make([][]byte, cgasNSec)
	body[cgasSecStrings-1] = arena
	body[cgasSecStrPos-1] = cgasRawBytes(g.Strings.off)
	body[cgasSecStrLn-1] = cgasRawBytes(g.Strings.lens)
	body[cgasSecMods-1] = cgasRawBytes(g.Modules)
	body[cgasSecFiles-1] = cgasRawBytes(g.Files)
	body[cgasSecFields-1] = cgasRawBytes(g.Fields)
	body[cgasSecLocals-1] = cgasRawBytes(g.Locals)
	body[cgasSecImports-1] = cgasRawBytes(g.Imports)
	body[cgasSecHaz-1] = cgasRawBytes(g.Hazards)
	body[cgasSecAttrs-1] = cgasRawBytes(g.Attributes)
	body[cgasSecLits-1] = cgasRawBytes(g.Literals)
	body[cgasSecEnums-1] = cgasRawBytes(g.EnumMembers)
	body[cgasSecMark-1] = cgasRawBytes(g.Markers)
	body[cgasSecHandlers-1] = cgasRawBytes(g.Handlers)
	body[cgasSecDyn-1] = cgasRawBytes(g.DynamicSites)
	body[cgasSecComps-1] = cgasRawBytes(g.Comprehens)
	body[cgasSecModVars-1] = cgasRawBytes(g.ModuleVars)
	body[cgasSecExports-1] = cgasRawBytes(g.AllExports)
	body[cgasSecInputs-1] = cgasRawBytes(g.InputSites)
	body[cgasSecSecrets-1] = cgasRawBytes(g.Secrets)
	body[cgasSecAPIs-1] = cgasRawBytes(g.APISites)
	body[cgasSecClasses-1] = cgasRawBytes(g.Classes)
	body[cgasSecEdges-1] = cgasRawBytes(g.Edges)
	body[cgasSecSites-1] = cgasRawBytes(g.Callsites)
	body[cgasSecUnres-1] = cgasRawBytes(g.Unresolved)
	body[cgasSecMeta-1] = cgasRawBytes(*(*[]cgasMetaRow)(unsafe.Pointer(&g.Meta)))

	stride := uint64(unsafe.Sizeof(tsRec{}))
	totalRecs := uint64(0)
	for i := range g.astTrees {
		totalRecs += uint64(len(g.astTrees[i]))
	}
	tDir := make([]byte, 12+4*len(g.astTrees))
	cgPutU64(tDir[0:8], 0, stride)
	cgPutU32(tDir[8:12], 0, uint32(len(g.astTrees)))
	for i := range g.astTrees {
		cgPutU32(tDir[12+4*i:], 0, uint32(len(g.astTrees[i])))
	}
	body[cgasSecTreeDir-1] = tDir

	dir := make([]cgasSec, cgasNSec)
	cur := uint64(cgasHeaderSz) + cgasNSec*cgasSecSz
	for i := range dir {
		cur = (cur + 7) &^ 7
		ln := uint64(len(body[i]))
		switch i + 1 {
		case int(cgasSecTrees):
			ln = totalRecs * stride
		case int(cgasSecSyms):
			ln = uint64(len(g.Symbols)) * cgasSymRowSz
		case int(cgasSecParams):
			ln = uint64(len(g.Params)) * cgasParamRowSz
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
	failW := func(err error) (int64, error) {
		f.Close()
		return 0, fmt.Errorf("write %s: %v", path, err)
	}
	failData := func(err error) (int64, error) {
		f.Close()
		os.Remove(path)
		return 0, fmt.Errorf("write %s: %v", path, err)
	}
	hdr := make([]byte, cgasHeaderSz)
	copy(hdr[0:4], cgasMagic)
	cgPutU32(hdr[4:8], 0, cgasVersion)
	cgPutU32(hdr[8:12], 0, cgasNSec)
	cgPutU64(hdr[16:24], 0, total)
	cgPutU64(hdr[24:32], 0, uint64(len(arena)))
	if _, err := w.Write(hdr); err != nil {
		return failW(err)
	}
	dirBuf := make([]byte, cgasNSec*cgasSecSz)
	for i := range dir {
		o := i * int(cgasSecSz)
		cgPutU32(dirBuf[o:], 0, dir[i].ID)
		cgPutU64(dirBuf[o+8:], 0, dir[i].Off)
		cgPutU64(dirBuf[o+16:], 0, dir[i].Len)
	}
	if _, err := w.Write(dirBuf); err != nil {
		return failW(err)
	}
	var zero [8]byte
	pos := uint64(cgasHeaderSz) + cgasNSec*cgasSecSz
	for i := range dir {
		if dir[i].Off > pos {
			if _, err := w.Write(zero[:dir[i].Off-pos]); err != nil {
				return failW(err)
			}
			pos = dir[i].Off
		}
		if i+1 == int(cgasSecTrees) {
			for _, tr := range g.astTrees {
				if len(tr) == 0 {
					continue
				}
				raw := unsafe.Slice((*byte)(unsafe.Pointer(&tr[0])), len(tr)*int(stride))
				if _, err := w.Write(raw); err != nil {
					return failW(err)
				}
			}
		} else if i+1 == int(cgasSecSyms) {
			if serr := cgasStreamSyms(w, g.Symbols); serr != nil {
				return failData(serr)
			}
		} else if i+1 == int(cgasSecParams) {
			if perr := cgasStreamParams(w, g.Params); perr != nil {
				return failData(perr)
			}
		} else if len(body[i]) > 0 {
			if _, err := w.Write(body[i]); err != nil {
				return failW(err)
			}
		}
		pos += dir[i].Len
	}
	if err := w.Flush(); err != nil {
		return failW(err)
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

	off, ln := dec(cgasSecStrPos)
	strPos, err := cgasDecodeRows[uint32](mem, off, ln, "interner offsets")
	if err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecStrLn)
	strLn, err := cgasDecodeRows[uint32](mem, off, ln, "interner lengths")
	if err != nil {
		return decErr(err)
	}
	if len(strPos) != len(strLn) {
		return nil, bad("interner offset/length counts differ (%d vs %d)", len(strPos), len(strLn))
	}
	for i := range strPos {
		if uint64(strPos[i]) > al || uint64(strLn[i]) > al-uint64(strPos[i]) {
			return nil, bad("interner string %d references (%d,%d) beyond the string arena (%d bytes)",
				i, strPos[i], strLn[i], al)
		}
	}
	if len(strPos) > 0 && (strLn[0] != 5 || arena[0] != 0 || string(arena[:5]) != "\x00null") {
		return nil, bad("interner entry 0 is not the null string")
	}
	nStr := uint32(len(strPos))

	off, ln = dec(cgasSecMods)
	mods, err := cgasDecodeRows[Module](mem, off, ln, "modules")
	if err != nil {
		return decErr(err)
	}
	if err := cgasCheckIDs(mods, moduleStrOffs, nStr, "modules"); err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecFiles)
	files, err := cgasDecodeRows[File](mem, off, ln, "files")
	if err != nil {
		return decErr(err)
	}
	if err := cgasCheckIDs(files, fileStrOffs, nStr, "files"); err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecSyms)
	syms, err := cgasDecodeSyms(mem, off, ln)
	if err != nil {
		return decErr(err)
	}
	if err := cgasCheckIDs(syms, symStrOffs, nStr, "symbols"); err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecParams)
	params, err := cgasDecodeParams(mem, off, ln)
	if err != nil {
		return decErr(err)
	}
	if err := cgasCheckIDs(params, paramStrOffs, nStr, "params"); err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecFields)
	fields, err := cgasDecodeRows[Field](mem, off, ln, "fields")
	if err != nil {
		return decErr(err)
	}
	if err := cgasCheckIDs(fields, fieldStrOffs, nStr, "fields"); err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecLocals)
	locals, err := cgasDecodeRows[LocalVar](mem, off, ln, "locals")
	if err != nil {
		return decErr(err)
	}
	if err := cgasCheckIDs(locals, localStrOffs, nStr, "locals"); err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecImports)
	imports, err := cgasDecodeRows[Import](mem, off, ln, "imports")
	if err != nil {
		return decErr(err)
	}
	if err := cgasCheckIDs(imports, importStrOffs, nStr, "imports"); err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecHaz)
	haz, err := cgasDecodeRows[Hazard](mem, off, ln, "hazards")
	if err != nil {
		return decErr(err)
	}
	if err := cgasCheckIDs(haz, hazardStrOffs, nStr, "hazards"); err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecAttrs)
	attrs, err := cgasDecodeRows[Attribute](mem, off, ln, "attributes")
	if err != nil {
		return decErr(err)
	}
	if err := cgasCheckIDs(attrs, attrStrOffs, nStr, "attributes"); err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecLits)
	lits, err := cgasDecodeRows[Literal](mem, off, ln, "literals")
	if err != nil {
		return decErr(err)
	}
	if err := cgasCheckIDs(lits, litStrOffs, nStr, "literals"); err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecEnums)
	enums, err := cgasDecodeRows[EnumMember](mem, off, ln, "enum members")
	if err != nil {
		return decErr(err)
	}
	if err := cgasCheckIDs(enums, enumStrOffs, nStr, "enum members"); err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecMark)
	mark, err := cgasDecodeRows[Marker](mem, off, ln, "markers")
	if err != nil {
		return decErr(err)
	}
	if err := cgasCheckIDs(mark, markerStrOffs, nStr, "markers"); err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecHandlers)
	handlers, err := cgasDecodeRows[Handler](mem, off, ln, "handlers")
	if err != nil {
		return decErr(err)
	}
	if err := cgasCheckIDs(handlers, handlerStrOffs, nStr, "handlers"); err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecDyn)
	dyn, err := cgasDecodeRows[DynamicSite](mem, off, ln, "dynamic sites")
	if err != nil {
		return decErr(err)
	}
	if err := cgasCheckIDs(dyn, dynStrOffs, nStr, "dynamic sites"); err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecComps)
	comps, err := cgasDecodeRows[Comprehension](mem, off, ln, "comprehensions")
	if err != nil {
		return decErr(err)
	}
	if err := cgasCheckIDs(comps, compStrOffs, nStr, "comprehensions"); err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecModVars)
	modVars, err := cgasDecodeRows[ModuleVar](mem, off, ln, "module vars")
	if err != nil {
		return decErr(err)
	}
	if err := cgasCheckIDs(modVars, modVarStrOffs, nStr, "module vars"); err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecExports)
	exports, err := cgasDecodeRows[AllExport](mem, off, ln, "all exports")
	if err != nil {
		return decErr(err)
	}
	if err := cgasCheckIDs(exports, exportStrOffs, nStr, "all exports"); err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecInputs)
	inputs, err := cgasDecodeRows[UserInputSite](mem, off, ln, "input sites")
	if err != nil {
		return decErr(err)
	}
	if err := cgasCheckIDs(inputs, inputStrOffs, nStr, "input sites"); err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecSecrets)
	secrets, err := cgasDecodeRows[SecretCandidate](mem, off, ln, "secret candidates")
	if err != nil {
		return decErr(err)
	}
	if err := cgasCheckIDs(secrets, secretStrOffs, nStr, "secret candidates"); err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecAPIs)
	apis, err := cgasDecodeRows[APISite](mem, off, ln, "api sites")
	if err != nil {
		return decErr(err)
	}
	if err := cgasCheckIDs(apis, apiStrOffs, nStr, "api sites"); err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecClasses)
	classes, err := cgasDecodeRows[ClassInfo](mem, off, ln, "classes")
	if err != nil {
		return decErr(err)
	}
	if err := cgasCheckIDs(classes, classStrOffs, nStr, "classes"); err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecEdges)
	edges, err := cgasDecodeRows[Edge](mem, off, ln, "edges")
	if err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecSites)
	sites, err := cgasDecodeRows[Callsite](mem, off, ln, "callsites")
	if err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecUnres)
	unres, err := cgasDecodeRows[Unresolved](mem, off, ln, "unresolved calls")
	if err != nil {
		return decErr(err)
	}
	if err := cgasCheckIDs(unres, unresStrOffs, nStr, "unresolved calls"); err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecMeta)
	meta, err := cgasDecodeRows[cgasMetaRow](mem, off, ln, "meta")
	if err != nil {
		return decErr(err)
	}
	if err := cgasCheckIDs(meta, metaStrOffs, nStr, "meta"); err != nil {
		return decErr(err)
	}

	tOff, tLn := secs[cgasSecTrees].Off, secs[cgasSecTrees].Len
	_, dLn := secs[cgasSecTreeDir].Off, secs[cgasSecTreeDir].Len
	if dLn < 12 {
		return nil, bad("node record directory too small (%d bytes)", dLn)
	}
	dBytes := mem[secs[cgasSecTreeDir].Off : secs[cgasSecTreeDir].Off+dLn]
	declStride := cgGetU64(dBytes, 0)
	nTreeFiles := int(cgGetU32(dBytes, 8))
	if declStride != uint64(unsafe.Sizeof(tsRec{})) {
		return nil, bad("node record stride %d, want %d", declStride, unsafe.Sizeof(tsRec{}))
	}
	if nTreeFiles != len(files) {
		return nil, bad("node record directory covers %d files, graph has %d", nTreeFiles, len(files))
	}
	if int(dLn) < 12+4*nTreeFiles {
		return nil, bad("node record directory too small for %d files", nTreeFiles)
	}
	var counts []uint32
	if nTreeFiles > 0 {
		counts = unsafe.Slice((*uint32)(unsafe.Pointer(&dBytes[12])), nTreeFiles)
	}
	if tLn%uint64(unsafe.Sizeof(tsRec{})) != 0 {
		return nil, bad("node record arena length %d is not a multiple of the record stride", tLn)
	}
	var recsAll []tsRec
	if tLn > 0 {
		recsAll = unsafe.Slice((*tsRec)(unsafe.Pointer(uintptr(unsafe.Pointer(&mem[0]))+uintptr(tOff))), int(tLn/uint64(unsafe.Sizeof(tsRec{}))))
	}
	astTrees := make([][]tsRec, nTreeFiles)
	base := 0
	for i := 0; i < nTreeFiles; i++ {
		cnt := int(counts[i])
		if base+cnt > len(recsAll) {
			return nil, bad("node record directory overruns the record arena")
		}
		if cnt > 0 {
			astTrees[i] = recsAll[base : base+cnt]
		}
		base += cnt
	}
	if base != len(recsAll) {
		return nil, bad("node record arena has %d unused records", len(recsAll)-base)
	}

	g := NewGraph()
	it := g.Strings
	it.buf = arena
	it.off = strPos
	it.lens = strLn
	it.null = 0
	it.idx = make(map[string]uint32, len(strPos))
	for i := range strPos {
		it.idx[string(it.buf[strPos[i]:strPos[i]+strLn[i]])] = uint32(i)
	}
	g.Modules = mods
	g.Files = files
	g.Symbols = syms
	g.Params = params
	g.Fields = fields
	g.Locals = locals
	g.Imports = imports
	g.Hazards = haz
	g.Attributes = attrs
	g.Literals = lits
	g.EnumMembers = enums
	g.Markers = mark
	g.Handlers = handlers
	g.DynamicSites = dyn
	g.Comprehens = comps
	g.ModuleVars = modVars
	g.AllExports = exports
	g.InputSites = inputs
	g.Secrets = secrets
	g.APISites = apis
	g.Classes = classes
	g.Edges = edges
	g.Callsites = sites
	g.Unresolved = unres
	g.Meta = make([][2]uint32, len(meta))
	for i, kv := range meta {
		g.Meta[i] = [2]uint32{kv[0], kv[1]}
	}
	for i := range g.Files {
		g.fileByPath[g.S(g.Files[i].Path)] = g.Files[i].ID
	}
	g.astTrees = astTrees
	g.buildAdjacency()
	g.buildIndex()
	return g, nil
}
