package main

import (
	"bufio"
	"bytes"
	"crypto/sha1"
	"encoding/csv"
	"encoding/hex"
	"encoding/json/jsontext"
	"encoding/json/v2"
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
	"slices"
	"sort"
	"strconv"
	"strings"
	"sync"
	"sync/atomic"
	"syscall"
	"time"
	"unicode/utf16"
	"unicode/utf8"
	"unsafe"
)

const tsGrammarTag = "v0.23.1"

var tsAbiVersion = 0

type kindTables struct {
	symCount, fieldCount   int
	named, visible, supers []bool
	public                 []uint16
	symNames, fieldNames   []string
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

func kindTableFatal(dir string, err error) {
	fmt.Fprintf(os.Stderr, "codegraph-ruby: grammar sources not usable at %s (%v)\n", dir, err)
	fmt.Fprintf(os.Stderr, "run: git clone --depth 1 --branch %s https://github.com/tree-sitter/tree-sitter-ruby %s\n",
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

func buildKindTables() kindTables {
	dir := filepath.Join(grammarBaseDir(), "tree-sitter-ruby")
	nodeTypesRaw, err := os.ReadFile(filepath.Join(dir, "src", "node-types.json"))
	if err != nil {
		kindTableFatal(dir, err)
	}
	grammarRaw, err := os.ReadFile(filepath.Join(dir, "src", "grammar.json"))
	if err != nil {
		kindTableFatal(dir, err)
	}

	nodeTypes, err := jsonArray(nodeTypesRaw)
	if err != nil {
		kindTableFatal(dir, err)
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
	for _, raw := range nodeTypes {
		keys, obj := jsonObject(raw)
		if obj == nil {
			continue
		}
		var name string
		named := true
		var fieldsRaw []byte
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
		if seen[name] {
			continue
		}
		seen[name] = true
		syms = append(syms, sym{name: name, named: named, visible: true})
		if len(fieldsRaw) > 0 {
			if fkeys, _ := jsonObject(fieldsRaw); fkeys != nil {
				for _, f := range fkeys {
					addField(f)
				}
			}
		}
	}

	var supertypes []string
	if _, gobj := jsonObject(grammarRaw); gobj != nil {
		if raw, ok := gobj["supertypes"]; ok {
			if err := json.Unmarshal(raw, &supertypes); err != nil {
				kindTableFatal(dir, err)
			}
		}
	}
	for _, name := range supertypes {
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

	t := kindTables{
		symCount:   len(syms),
		fieldCount: len(fields) + 1,
		named:      make([]bool, len(syms)),
		visible:    make([]bool, len(syms)),
		supers:     make([]bool, len(syms)),
		public:     make([]uint16, len(syms)),
		symNames:   make([]string, len(syms)),
		fieldNames: make([]string, len(fields)+1),
	}
	for i, s := range syms {
		t.named[i], t.visible[i], t.supers[i] = s.named, s.visible, s.super
		t.public[i] = uint16(i)
		t.symNames[i] = s.name
	}
	copy(t.fieldNames[1:], fields)
	return t
}

var kindT = buildKindTables()

var (
	tsSymCount   = kindT.symCount
	tsFieldCount = kindT.fieldCount
	tsSymNamed   = kindT.named
	tsSymVisible = kindT.visible
	tsSymSuper   = kindT.supers
	tsSymPublic  = kindT.public
	tsSymNames   = kindT.symNames
	tsFieldNames = kindT.fieldNames
)

var tableColumns = map[string]int{
	"ar_callbacks":      12,
	"ar_queries":        13,
	"attributes":        6,
	"blocks":            15,
	"callsites":         3,
	"edges":             6,
	"enum_members":      5,
	"fields":            14,
	"files":             29,
	"hazards":           5,
	"imports":           13,
	"literals":          7,
	"locals":            11,
	"markers":           6,
	"meta":              2,
	"metaprogram_sites": 12,
	"mixins":            9,
	"modules":           10,
	"monkey_patches":    9,
	"params":            13,
	"ruby_modules":      17,
	"secret_candidates": 5,
	"sym_fts":           3,
	"symbols":           223,
	"unresolved_calls":  4,
	"user_input_sites":  7,
}

func appendCellSep(dst []byte, more bool) []byte {
	if more {
		return append(dst, ' ')
	}
	return dst
}

const tsScope = "source.ruby"

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
	bin        string
	outBuf     []byte
	env        []string
	devNull    *os.File
	startsBuf  []int
	recsBuf    []tsRec
	stackBuf   []cstFrame
	unquoteBuf []byte
	freshIDs   map[string]uint16
}

type cstFrame struct {
	i   int32
	end uint32
}

func tsParserNew() *tsParser {
	bin := tsCLIBin()
	if _, err := os.Stat(bin); err != nil {
		panic("tree-sitter CLI not found at " + bin + " -- see setup.sh")
	}
	devNull, _ := os.OpenFile(os.DevNull, os.O_WRONLY, 0)
	return &tsParser{bin: bin, env: append(os.Environ(), "NO_COLOR=1", "TERM=dumb"),
		devNull: devNull}
}

func (p *tsParser) free() {}

func (p *tsParser) readAll(r io.Reader) []byte {
	buf := p.outBuf[:0]
	for {
		if len(buf) == cap(buf) {
			grow := cap(buf)
			if grow < 1<<16 {
				grow = 1 << 16
			}
			nb := make([]byte, len(buf), cap(buf)+grow)
			copy(nb, buf)
			buf = nb
		}
		n, err := r.Read(buf[len(buf):cap(buf)])
		buf = buf[:len(buf)+n]
		if err != nil {
			break
		}
	}
	p.outBuf = buf
	return buf
}

func (p *tsParser) parse(src []byte) *tsTree {
	cmd := exec.Command(p.bin, "parse", "/dev/stdin", "--scope", tsScope, "--cst")
	cmd.Env = p.env
	inr, inw, err := os.Pipe()
	if err != nil {
		return nil
	}
	outr, outw, err := os.Pipe()
	if err != nil {
		inr.Close()
		inw.Close()
		return nil
	}
	cmd.Stdin = inr
	cmd.Stdout = outw
	cmd.Stderr = p.devNull
	if serr := cmd.Start(); serr != nil {
		inr.Close()
		inw.Close()
		outr.Close()
		outw.Close()
		return nil
	}
	inr.Close()
	outw.Close()
	woff := 0
	for woff < len(src) {
		n, werr := inw.Write(src[woff:])
		woff += n
		if werr != nil {
			break
		}
	}
	inw.Close()
	out := p.readAll(outr)
	outr.Close()
	werr := cmd.Wait()
	if werr != nil && len(out) == 0 {
		return nil
	}
	t, derr := decodeCST(out, src, p)
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

func sameNode(a, b tsNode) bool { return a.t == b.t && a.i == b.i }

func kindID(n tsNode) uint16 {
	if !hasNode(n) {
		return tsSymInvalid
	}
	return n.t.recs[n.i].sym
}

func nodeKindName(n tsNode) string {
	s := kindID(n)
	if int(s) < nKinds {
		return kindNames[s]
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

func langAbiVersion() uint32 { return uint32(tsAbiVersion) }
func langVersion() uint32    { return uint32(tsAbiVersion) }

var kindNames = tsSymNames

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

func decodeCST(out, src []byte, p *tsParser) (*tsTree, error) {
	starts := p.startsBuf[:0]
	starts = append(starts, 0)
	for i := 0; i < len(src); i++ {
		if src[i] == '\n' {
			starts = append(starts, i+1)
		}
	}
	p.startsBuf = starts
	d := &cstDecoder{
		starts: starts,
		total:  len(src),
	}

	if n := bytes.Count(out, []byte{'\n'}) + 1; cap(p.recsBuf) < n {
		p.recsBuf = make([]tsRec, 0, n)
	}
	recs := p.recsBuf[:0]
	stack := p.stackBuf[:0]

	nextFresh := uint16(len(tsSymByID) + 0x4000)
	if p.freshIDs != nil {
		clear(p.freshIDs)
	}
	freshIDs := p.freshIDs
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
	unquoteBuf := p.unquoteBuf[:0]

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
		}
		stack = append(stack, cstFrame{i: idx, end: end})
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
	freshIDsMap := freshIDs
	if freshIDsMap == nil {
		freshIDsMap = map[string]uint16{}
	}
	p.freshIDs = freshIDsMap
	p.stackBuf = stack[:0]
	p.unquoteBuf = unquoteBuf[:0]
	p.recsBuf = recs
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

type kindTab struct {
	loops    []bool
	branches []bool
	nests    []bool
	calls    []bool
	ops      []bool
	strs     []bool
	nums     []bool
	cmts     []bool
	ifs      []bool
	xloops   []bool
	prune    []bool

	counter []uint8

	tk []uint16
}

var counterTypes = []string{
	"return", "yield", "block_argument", "do_block", "block", "lambda",
	"case", "case_match", "when", "in_clause", "conditional", "rescue",
	"rescue_modifier", "ensure", "retry", "instance_variable",
	"class_variable", "global_variable", "interpolation", "regex",
	"subshell", "assignment", "operator_assignment", "element_reference",
	"hash", "array", "string_array", "symbol_array", "heredoc_body",
	"alias", "undef", "super", "forward_argument", "forward_parameter",
	"uninterpreted", "scope_resolution",
	"identifier", "binary", "regex", "heredoc_body", "block_argument",
}

var kinds kindTab

var nKinds = langSymbolCount()

var (
	fName, fBody, fParams, fMethod, fReceiver, fArguments, fBlock tsFieldID
	fKey                                                          tsFieldID
	fObject, fSuperclass, fAlternative, fExceptions               tsFieldID
	fHandler, fLeft, fOperator, fValue                            tsFieldID
)

const noCounter = 0xFF

const (
	cReturns = iota
	cYield
	cBlockArgument
	cDoBlock
	cLambda
	cCase
	cCaseMatch
	cWhen
	cInClause
	cConditional
	cRescue
	cRescueModifier
	cEnsure
	cRetry
	cInstanceVariable
	cClassVariable
	cGlobalVariable
	cInterpolation
	cRegexLit
	cSubshell
	cAssign
	cOperatorAssignment
	cElementReference
	cHashLit
	cArrayLit
	cStringArray
	cSymbolArray
	cHeredocBody
	cAlias
	cUndef
	cSuper
	cForwardArgument
	cForwardParameter
	cUninterpreted
	cScopeResolution

	cQueryInLoop
	cIoInLoop
	cLockInLoop
	cRegexInLoop

	cSystemCall
	cRedirect
	cConstantize
	cHtmlSafe
	cRawSQL
	cWeakHash
	cWeakRandom
	cFetch
	cXxeParser
	cDynamicOpen
	cZipRead
	cLogCall
	cAuthCall
	cOpenCall
	cSleepCall
	cIncludeInLoop
	cEnumInLoop
	cCountInLoop
	cArWriteInLoop
	cSerializeInLoop
	cBlockGiven
	cRaise
	cFreeze
	cDupClone
	cProcNew
	cLambdaCall
	cThreadNew
	cMutex
	cRactor
	cThreadLocal
	cTimeout
	cPermit
	cPermitBang
	cSqlSanitized
	cToSym
	cRegexDyn
	cEnqueue
	cZonelessTime
	cConstMutate
	cThreadJoin
	cMetaprogramDispatch

	cRescueBare
	cRescueException
	cRescueEmpty
	cRescueReraise
	cSymbolToProc
	cClassLevelWrite

	cIterBlocks
	cCollectionLitInLoop
	cStrLitInLoop
	cClassLevelIvar
	cChainArrayAlloc
	cMapChain
	cTimesMap
	cRangeInclude
	cSaveIgnored
	cLegacyChain
	cEnqueueInLoop
	cMaxBlockDepth

	cLoopsBump
	cBranch
	cElif
	cBranchInLoop
	cStringLit
	cMagic
	cFloatLit
	cCommentLines
	cCallSite
	cCallInLoop
	cDynamicCall
	cMetaprogramTotal
	cMassAssignSink
	cSend
	cDefineMethod
	cMethodMissing
	cConstGet
	cInstanceEval
	cClassEval
	cInstanceVarGet
	cEval
	cMetaOther
	cArQuery
	cArTerminal
	cArWrite
	cSqlLiteral
	cSqlInterp
	cParamsRead
	nCounters
)

var counterNames = [nCounters]string{
	"n_returns", "n_yield", "n_block_pass", "n_blocks", "n_lambda", "n_switch",
	"n_switch", "n_cases", "n_cases", "n_ternary", "n_rescue", "n_rescue",
	"n_ensure", "n_retry", "n_instance_var", "n_class_var", "n_global_var",
	"n_string_interp", "n_regex_lit", "n_subshell", "n_assign",
	"n_compound_assign", "n_subscript", "n_hash_lit", "n_array_lit",
	"n_array_lit", "n_array_lit", "n_heredoc", "n_alias", "n_alias", "n_super",
	"n_forwarding", "n_forwarding", "n_end_data", "n_const_ref",
	"query_in_loop", "io_in_loop", "lock_in_loop", "regex_in_loop",
	"n_system_call", "n_redirect", "n_constantize", "n_html_safe", "n_raw_sql",
	"n_weak_hash", "n_weak_random", "n_fetch", "n_xxe_parser", "n_dynamic_open",
	"n_zip_read", "n_log_call", "n_auth_call", "n_open_call", "n_sleep_call",
	"n_include_in_loop", "n_enum_in_loop", "n_count_in_loop",
	"n_ar_write_in_loop", "n_serialize_in_loop", "n_block_given", "n_raise",
	"n_freeze", "n_dup_clone", "n_proc_new", "n_lambda", "n_thread_new",
	"n_mutex", "n_ractor", "n_thread_local", "n_timeout", "n_permit",
	"n_permit_bang", "n_sql_sanitized", "n_to_sym", "n_regex_dyn", "n_enqueue",
	"n_zoneless_time", "n_const_mutate", "n_thread_join",
	"n_metaprogram_dynamic",
	"n_rescue_bare", "n_rescue_exception", "n_rescue_empty",
	"n_rescue_reraise", "n_symbol_to_proc", "n_class_level_write",
	"n_iter_blocks", "n_collection_lit_in_loop", "n_str_lit_in_loop",
	"n_class_level_ivar", "n_chain_array_alloc", "n_map_chain", "n_times_map",
	"n_range_include", "n_save_ignored", "n_legacy_chain", "n_enqueue_in_loop",
	"max_block_depth",
	"n_loops", "n_branches", "n_elif", "branch_in_loop", "n_string_lit",
	"n_magic", "n_float_lit", "n_comment_lines",
	"n_calls", "call_in_loop", "n_dynamic_calls", "n_metaprogram_total",
	"n_mass_assign",
	"n_send", "n_define_method", "n_method_missing", "n_const_get",
	"n_instance_eval", "n_class_eval", "n_instance_var_get", "n_eval",
	"n_metaprogram_other",
	"n_ar_query", "n_ar_terminal", "n_ar_write",
	"n_sql_literal", "n_sql_interp", "n_params_read",
}

var counterIndex = func() map[string]uint8 {
	m := make(map[string]uint8, nCounters)
	for i, n := range counterNames {
		if _, dup := m[n]; !dup {
			m[n] = uint8(i)
		}
	}
	return m
}()

func counterOf(name string) uint8 {
	if i, ok := counterIndex[name]; ok {
		return i
	}
	panic("codegraph-ruby: metric counted but no column: " + name)
}

var (
	kindMethod      = uint16(0)
	kindSingl       = uint16(0)
	kindClass       = uint16(0)
	kindModule      = uint16(0)
	kindCall        = uint16(0)
	kindBlock       = uint16(0)
	kindDoBlock     = uint16(0)
	kindIdent       = uint16(0)
	kindConst       = uint16(0)
	kindScopeRs     = uint16(0)
	kindSetter      = uint16(0)
	kindOper        = uint16(0)
	kindStr         = uint16(0)
	kindHeredoc     = uint16(0)
	kindSubsh       = uint16(0)
	kindElemRef     = uint16(0)
	kindRescue      = uint16(0)
	kindRescMod     = uint16(0)
	kindBlockAr     = uint16(0)
	kindSingCls     = uint16(0)
	kindReturn      = uint16(0)
	kindBreak       = uint16(0)
	kindBin         = uint16(0)
	kindAssign      = uint16(0)
	kindOpAsgn      = uint16(0)
	kindRegex       = uint16(0)
	kindNilNode     = uint16(0)
	kindSym         = uint16(0)
	kindDelim       = uint16(0)
	kindHeredB      = uint16(0)
	kindSimSym      = uint16(0)
	kindArgList     = uint16(0)
	kindOptParam    = uint16(0)
	kindKwParam     = uint16(0)
	kindSplatP      = uint16(0)
	kindHSplatP     = uint16(0)
	kindFwdParam    = uint16(0)
	kindComment     = uint16(0)
	kindSelf        = uint16(0)
	kindRange       = uint16(0)
	kindParenStmt   = uint16(0)
	kindArray       = uint16(0)
	kindHash        = uint16(0)
	kindStrArray    = uint16(0)
	kindSymArray    = uint16(0)
	kindInterp      = uint16(0)
	kindInstanceVar = uint16(0)
	kindClassVar    = uint16(0)
	kindGlobalVar   = uint16(0)
	kindExprStmt    = uint16(0)
	kindBodyStmt    = uint16(0)
	kindDoNode      = uint16(0)
	kindThen        = uint16(0)
	kindPair        = uint16(0)
	kindYield       = uint16(0)
	kindReturnAnon  = uint16(0)
	kindBreakAnon   = uint16(0)
)

func init() {

	tsz := nKinds + 1
	kinds.loops = make([]bool, tsz)
	kinds.branches = make([]bool, tsz)
	kinds.nests = make([]bool, tsz)
	kinds.calls = make([]bool, tsz)
	kinds.ops = make([]bool, tsz)
	kinds.strs = make([]bool, tsz)
	kinds.nums = make([]bool, tsz)
	kinds.cmts = make([]bool, tsz)
	kinds.ifs = make([]bool, tsz)
	kinds.xloops = make([]bool, tsz)
	kinds.prune = make([]bool, tsz)
	kinds.counter = make([]uint8, tsz)
	kinds.tk = make([]uint16, tsz)
	for i := range kinds.counter {
		kinds.counter[i] = noCounter
		kinds.tk[i] = uint16(i)
	}
	for _, name := range counterTypes {
		named := symLookup(name, true)
		if int(named) < nKinds {
			kinds.tk[named] = named
		}
		anon := symLookup(name, false)
		if int(anon) < nKinds && langSymbolName(anon) == name {
			kinds.tk[anon] = named
		}
	}

	id := func(s string) uint16 { return symLookup(s, true) }
	mark := func(t *[]bool, names ...string) {
		for _, n := range names {
			k := id(n)
			if int(k) < nKinds {
				(*t)[k] = true
			}
		}
	}
	markC := func(names []string, c uint8) {
		for _, n := range names {
			k := id(n)
			if int(k) < nKinds {
				kinds.counter[k] = c
			}
		}
	}

	mark(&kinds.loops, "while", "until", "for", "while_modifier", "until_modifier")
	mark(&kinds.branches, "if", "elsif", "unless", "if_modifier", "unless_modifier",
		"when", "in_clause", "rescue", "conditional")
	mark(&kinds.nests, "if", "unless", "while", "until", "for", "case",
		"case_match", "do_block", "block", "begin", "lambda", "singleton_class")
	mark(&kinds.calls, "call")
	mark(&kinds.ops, "binary", "unary", "assignment", "operator_assignment",
		"element_reference", "conditional", "range", "scope_resolution",
		"splat_argument", "hash_splat_argument")
	mark(&kinds.strs, "string", "bare_string", "chained_string",
		"delimited_symbol", "heredoc_body")
	mark(&kinds.nums, "integer", "float", "rational", "complex")
	mark(&kinds.cmts, "comment")
	mark(&kinds.ifs, "if", "elsif", "unless")
	mark(&kinds.xloops, "do_block", "block")
	mark(&kinds.prune, "method", "singleton_method", "class", "module")

	markC([]string{"return"}, cReturns)
	markC([]string{"yield"}, cYield)
	markC([]string{"block_argument"}, cBlockArgument)
	markC([]string{"do_block", "block"}, cDoBlock)
	markC([]string{"lambda"}, cLambda)
	markC([]string{"case", "case_match"}, cCase)
	markC([]string{"when", "in_clause"}, cWhen)
	markC([]string{"conditional"}, cConditional)
	markC([]string{"rescue", "rescue_modifier"}, cRescue)
	markC([]string{"ensure"}, cEnsure)
	markC([]string{"retry"}, cRetry)
	markC([]string{"instance_variable"}, cInstanceVariable)
	markC([]string{"class_variable"}, cClassVariable)
	markC([]string{"global_variable"}, cGlobalVariable)
	markC([]string{"interpolation"}, cInterpolation)
	markC([]string{"regex"}, cRegexLit)
	markC([]string{"subshell"}, cSubshell)
	markC([]string{"assignment"}, cAssign)
	markC([]string{"operator_assignment"}, cOperatorAssignment)
	markC([]string{"element_reference"}, cElementReference)
	markC([]string{"hash"}, cHashLit)
	markC([]string{"array", "string_array", "symbol_array"}, cArrayLit)
	markC([]string{"heredoc_body"}, cHeredocBody)
	markC([]string{"alias", "undef"}, cAlias)
	markC([]string{"super"}, cSuper)
	markC([]string{"forward_argument", "forward_parameter"}, cForwardArgument)
	markC([]string{"uninterpreted"}, cUninterpreted)
	markC([]string{"scope_resolution"}, cScopeResolution)

	kindMethod = id("method")
	kindSingl = id("singleton_method")
	kindClass = id("class")
	kindModule = id("module")
	kindCall = id("call")
	kindBlock = id("block")
	kindDoBlock = id("do_block")
	kindIdent = id("identifier")
	kindConst = id("constant")
	kindScopeRs = id("scope_resolution")
	kindSetter = id("setter")
	kindOper = id("operator")
	kindStr = id("string")
	kindHeredoc = id("heredoc_body")
	kindSubsh = id("subshell")
	kindElemRef = id("element_reference")
	kindRescue = id("rescue")
	kindRescMod = id("rescue_modifier")
	kindBlockAr = id("block_argument")
	kindSingCls = id("singleton_class")
	kindReturn = id("return")
	kindBreak = id("break")
	kindBin = id("binary")
	kindAssign = id("assignment")
	kindOpAsgn = id("operator_assignment")
	kindRegex = id("regex")
	kindNilNode = id("nil")
	kindSym = id("simple_symbol")
	kindDelim = id("delimited_symbol")
	kindHeredB = id("heredoc_beginning")
	kindSimSym = id("simple_symbol")
	kindArgList = id("argument_list")
	kindOptParam = id("optional_parameter")
	kindKwParam = id("keyword_parameter")
	kindSplatP = id("splat_parameter")
	kindHSplatP = id("hash_splat_parameter")
	kindFwdParam = id("forward_parameter")
	kindComment = id("comment")
	kindSelf = id("self")
	kindRange = id("range")
	kindParenStmt = id("parenthesized_statements")
	kindArray = id("array")
	kindHash = id("hash")
	kindStrArray = id("string_array")
	kindSymArray = id("symbol_array")
	kindInterp = id("interpolation")
	kindInstanceVar = id("instance_variable")
	kindClassVar = id("class_variable")
	kindGlobalVar = id("global_variable")
	kindExprStmt = id("expression_statement")
	kindBodyStmt = id("body_statement")
	kindDoNode = id("do")
	kindThen = id("then")
	kindPair = id("pair")
	kindYield = id("yield")

	kindReturnAnon = symLookup("return", false)
	kindBreakAnon = symLookup("break", false)

	fName = fieldID("name")
	fBody = fieldID("body")
	fParams = fieldID("parameters")
	fMethod = fieldID("method")
	fReceiver = fieldID("receiver")
	fArguments = fieldID("arguments")
	fBlock = fieldID("block")
	fObject = fieldID("object")
	fSuperclass = fieldID("superclass")
	fAlternative = fieldID("alternative")
	fExceptions = fieldID("exceptions")
	fHandler = fieldID("handler")
	fLeft = fieldID("left")
	fOperator = fieldID("operator")
	fValue = fieldID("value")
	fKey = fieldID("key")
}

var setOp = map[string]bool{}

func init() { setOp["include?"] = true }

func tkOf(k uint16) uint16 {
	if int(k) < nKinds {
		return kinds.tk[k]
	}
	return uint16(nKinds)
}

func identKind(k uint16) bool {
	return k == kindIdent || k == kindConst || k == kindScopeRs ||
		k == kindSetter || k == kindOper
}

func simpleReceiver(k uint16) bool { return inSet(simpleReceivers, kindName(k)) }

func kindName(k uint16) string {
	if int(k) < nKinds {
		return kindNames[k]
	}
	if k == 0xFFFE {
		return "_ERROR"
	}
	if k == 0xFFFF {
		return "ERROR"
	}
	return ""
}

func textOf(src []byte, n tsNode) string {
	if !hasNode(n) {
		return ""
	}
	return string(src[startByte(n):endByte(n)])
}

func childField(n tsNode, f tsFieldID) tsNode {
	if !hasNode(n) || f == 0 {
		return tsNode{}
	}
	return fieldNode(n, f)
}

// forEachNamedChild visits n's named children in document order. It walks the
// record chain directly, which is O(k) for k children — namedChildAt restarts
// at the first child, so an index loop over them is O(k^2).
func forEachNamedChild(n tsNode, f func(tsNode)) {
	if !hasNode(n) {
		return
	}
	for c, end := n.i+1, n.t.recs[n.i].subEnd; c < end; c = n.t.recs[c].subEnd {
		if n.t.recs[c].flags&tsFlagNamed != 0 {
			f(tsNode{t: n.t, i: c})
		}
	}
}

// pushNamedChildren appends n's named children to stack in document order and
// reverses that segment, so the caller's LIFO pop visits them in document
// order — byte-for-byte the order the old reversed namedChildAt loop produced,
// at O(k) instead of O(k^2).
func pushNamedChildren(stack []walkItem, n tsNode, sc scope) []walkItem {
	if !hasNode(n) {
		return stack
	}
	start := len(stack)
	for c, end := n.i+1, n.t.recs[n.i].subEnd; c < end; c = n.t.recs[c].subEnd {
		if n.t.recs[c].flags&tsFlagNamed != 0 {
			stack = append(stack, walkItem{tsNode{t: n.t, i: c}, sc})
		}
	}
	for a, b := start, len(stack)-1; a < b; a, b = a+1, b-1 {
		stack[a], stack[b] = stack[b], stack[a]
	}
	return stack
}

func hasPrefixAny(s string, pfx ...string) bool {
	for _, p := range pfx {
		if strings.HasPrefix(s, p) {
			return true
		}
	}
	return false
}

func newSet(items ...string) map[string]bool {
	m := make(map[string]bool, len(items))
	for _, s := range items {
		m[s] = true
	}
	return m
}

func inSet(m map[string]bool, s string) bool { return m[s] }

var hazardCalls = map[string]string{
	"eval":                         "exec",
	"instance_eval":                "exec",
	"class_eval":                   "exec",
	"module_eval":                  "exec",
	"binding.eval":                 "exec",
	"Binding.eval":                 "exec",
	"system":                       "exec",
	"exec":                         "exec",
	"spawn":                        "exec",
	"syscall":                      "exec",
	"Process.spawn":                "exec",
	"Process.exec":                 "exec",
	"Process.fork":                 "exec",
	"Open3.capture2":               "exec",
	"Open3.capture2e":              "exec",
	"Open3.capture3":               "exec",
	"Open3.popen2":                 "exec",
	"Open3.popen2e":                "exec",
	"Open3.popen3":                 "exec",
	"Open3.pipeline":               "exec",
	"Kernel.system":                "exec",
	"Kernel.exec":                  "exec",
	"Kernel.spawn":                 "exec",
	"Kernel.open":                  "exec",
	"IO.popen":                     "exec",
	"PTY.spawn":                    "exec",
	"`backticks`":                  "exec",
	"%x{}":                         "exec",
	"send":                         "metaprogram",
	"public_send":                  "metaprogram",
	"__send__":                     "metaprogram",
	"define_method":                "metaprogram",
	"define_singleton_method":      "metaprogram",
	"method_missing":               "metaprogram",
	"respond_to_missing?":          "metaprogram",
	"const_get":                    "metaprogram",
	"const_set":                    "metaprogram",
	"const_missing":                "metaprogram",
	"constantize":                  "metaprogram",
	"safe_constantize":             "metaprogram",
	"instance_variable_get":        "metaprogram",
	"instance_variable_set":        "metaprogram",
	"class_variable_get":           "metaprogram",
	"class_variable_set":           "metaprogram",
	"instance_exec":                "metaprogram",
	"class_exec":                   "metaprogram",
	"method":                       "metaprogram",
	"alias_method":                 "metaprogram",
	"remove_method":                "metaprogram",
	"undef_method":                 "metaprogram",
	"prepend":                      "metaprogram",
	"extend":                       "metaprogram",
	"included_modules":             "metaprogram",
	"ancestors":                    "metaprogram",
	"define_attr_method":           "metaprogram",
	"attr_internal":                "metaprogram",
	"delegate_missing_to":          "metaprogram",
	"method_defined?":              "metaprogram",
	"singleton_class":              "metaprogram",
	"Object.const_get":             "metaprogram",
	"ObjectSpace.each_object":      "metaprogram",
	"Marshal.load":                 "deserialize",
	"Marshal.restore":              "deserialize",
	"YAML.load":                    "deserialize",
	"YAML.unsafe_load":             "deserialize",
	"YAML.load_file":               "deserialize",
	"YAML.unsafe_load_file":        "deserialize",
	"Psych.load":                   "deserialize",
	"Psych.unsafe_load":            "deserialize",
	"JSON.load":                    "deserialize",
	"Oj.load":                      "deserialize",
	"CSV.load":                     "deserialize",
	"Syck.load":                    "deserialize",
	"find_by_sql":                  "sql",
	"count_by_sql":                 "sql",
	"execute":                      "sql",
	"exec_query":                   "sql",
	"exec_update":                  "sql",
	"exec_delete":                  "sql",
	"select_all":                   "sql",
	"select_values":                "sql",
	"select_rows":                  "sql",
	"sanitize_sql":                 "sql",
	"sanitize_sql_array":           "sql",
	"sanitize_sql_for_conditions":  "sql",
	"quote":                        "sql",
	"connection.execute":           "sql",
	"where":                        "rails_query",
	"where!":                       "rails_query",
	"rewhere":                      "rails_query",
	"order":                        "rails_query",
	"reorder":                      "rails_query",
	"pluck":                        "rails_query",
	"joins":                        "rails_query",
	"left_joins":                   "rails_query",
	"includes":                     "rails_query",
	"preload":                      "rails_query",
	"eager_load":                   "rails_query",
	"references":                   "rails_query",
	"select":                       "alloc",
	"group":                        "rails_query",
	"having":                       "rails_query",
	"find_by":                      "rails_query",
	"find_each":                    "rails_query",
	"find_in_batches":              "rails_query",
	"in_batches":                   "rails_query",
	"update_all":                   "rails_query",
	"delete_all":                   "rails_query",
	"destroy_all":                  "rails_query",
	"upsert_all":                   "rails_query",
	"insert_all":                   "rails_query",
	"exists?":                      "rails_query",
	"lock":                         "rails_query",
	"distinct":                     "rails_query",
	"unscoped":                     "rails_query",
	"create":                       "mass_assign",
	"create!":                      "mass_assign",
	"update":                       "mass_assign",
	"update!":                      "mass_assign",
	"update_attributes":            "mass_assign",
	"update_attributes!":           "mass_assign",
	"update_attribute":             "mass_assign",
	"assign_attributes":            "mass_assign",
	"attributes=":                  "mass_assign",
	"permit":                       "mass_assign",
	"permit!":                      "mass_assign",
	"new":                          "mass_assign",
	"first_or_create":              "mass_assign",
	"find_or_create_by":            "mass_assign",
	"find_or_initialize_by":        "mass_assign",
	"File.open":                    "io",
	"File.read":                    "io",
	"File.write":                   "io",
	"File.readlines":               "io",
	"File.delete":                  "io",
	"File.unlink":                  "io",
	"File.rename":                  "io",
	"File.exist?":                  "io",
	"File.join":                    "io",
	"File.expand_path":             "io",
	"File.basename":                "io",
	"File.dirname":                 "io",
	"IO.read":                      "io",
	"IO.write":                     "io",
	"IO.readlines":                 "io",
	"IO.binread":                   "io",
	"IO.foreach":                   "io",
	"Dir.glob":                     "io",
	"Dir.entries":                  "io",
	"Dir.mkdir":                    "io",
	"Dir.chdir":                    "io",
	"Dir.[]":                       "io",
	"Dir.children":                 "io",
	"FileUtils.rm":                 "io",
	"FileUtils.rm_rf":              "io",
	"FileUtils.rm_f":               "io",
	"FileUtils.cp":                 "io",
	"FileUtils.cp_r":               "io",
	"FileUtils.mv":                 "io",
	"FileUtils.mkdir_p":            "io",
	"FileUtils.chmod":              "io",
	"FileUtils.touch":              "io",
	"FileUtils.ln_s":               "io",
	"Tempfile.new":                 "io",
	"Tempfile.create":              "io",
	"Pathname.new":                 "io",
	"StringIO.new":                 "io",
	"Net::HTTP.get":                "net",
	"Net::HTTP.post":               "net",
	"Net::HTTP.start":              "net",
	"Net::HTTP.new":                "net",
	"Net::HTTP.get_response":       "net",
	"Net::HTTP.post_form":          "net",
	"Net::FTP.open":                "net",
	"Net::SMTP.start":              "net",
	"URI.open":                     "net",
	"URI.parse":                    "net",
	"URI.join":                     "net",
	"open-uri":                     "net",
	"HTTParty.get":                 "net",
	"HTTParty.post":                "net",
	"Faraday.get":                  "net",
	"Faraday.post":                 "net",
	"Faraday.new":                  "net",
	"RestClient.get":               "net",
	"RestClient.post":              "net",
	"Excon.get":                    "net",
	"Typhoeus.get":                 "net",
	"Curl.get":                     "net",
	"Socket.new":                   "net",
	"TCPSocket.new":                "net",
	"TCPServer.new":                "net",
	"UDPSocket.new":                "net",
	"OpenURI.open_uri":             "net",
	"Digest::MD5.hexdigest":        "crypto",
	"Digest::MD5.digest":           "crypto",
	"Digest::MD5.new":              "crypto",
	"Digest::SHA1.hexdigest":       "crypto",
	"Digest::SHA1.digest":          "crypto",
	"Digest::SHA1.new":             "crypto",
	"OpenSSL::Digest::MD5":         "crypto",
	"OpenSSL::Digest::SHA1":        "crypto",
	"OpenSSL::Cipher.new":          "crypto",
	"OpenSSL::Cipher::Cipher.new":  "crypto",
	"rand":                         "crypto",
	"srand":                        "crypto",
	"Random.rand":                  "crypto",
	"Random.new":                   "crypto",
	"Kernel.rand":                  "crypto",
	"SecureRandom.hex":             "crypto",
	"SecureRandom.uuid":            "crypto",
	"SecureRandom.random_bytes":    "crypto",
	"SecureRandom.base64":          "crypto",
	"SecureRandom.urlsafe_base64":  "crypto",
	"SecureRandom.alphanumeric":    "crypto",
	"OpenSSL::HMAC.hexdigest":      "crypto",
	"Digest::SHA256.hexdigest":     "crypto",
	"BCrypt::Password.create":      "crypto",
	"Thread.new":                   "concurrency",
	"Thread.start":                 "concurrency",
	"Thread.fork":                  "concurrency",
	"Thread.current":               "concurrency",
	"Thread.kill":                  "concurrency",
	"Thread.exclusive":             "concurrency",
	"Mutex.new":                    "concurrency",
	"Monitor.new":                  "concurrency",
	"synchronize":                  "concurrency",
	"Queue.new":                    "concurrency",
	"SizedQueue.new":               "concurrency",
	"ConditionVariable.new":        "concurrency",
	"Ractor.new":                   "concurrency",
	"Ractor.yield":                 "concurrency",
	"Ractor::Port.new":             "concurrency",
	"Ractor.make_shareable":        "concurrency",
	"Fiber.new":                    "concurrency",
	"Fiber.yield":                  "concurrency",
	"Timeout.timeout":              "concurrency",
	"timeout":                      "concurrency",
	"Concurrent::Promise.execute":  "concurrency",
	"Concurrent::Future.execute":   "concurrency",
	"ThreadsWait.new":              "concurrency",
	"sleep":                        "concurrency",
	"map":                          "alloc",
	"collect":                      "alloc",
	"flat_map":                     "alloc",
	"filter":                       "alloc",
	"reject":                       "alloc",
	"sort_by":                      "alloc",
	"group_by":                     "alloc",
	"each_with_object":             "alloc",
	"uniq":                         "alloc",
	"flatten":                      "alloc",
	"compact":                      "alloc",
	"zip":                          "alloc",
	"to_a":                         "alloc",
	"dup":                          "alloc",
	"clone":                        "alloc",
	"deep_dup":                     "alloc",
	"Array.new":                    "alloc",
	"Hash.new":                     "alloc",
	"String.new":                   "alloc",
	"gsub":                         "alloc",
	"sub":                          "alloc",
	"split":                        "alloc",
	"join":                         "alloc",
	"format":                       "alloc",
	"sprintf":                      "alloc",
	"raise":                        "control",
	"fail":                         "control",
	"throw":                        "control",
	"catch":                        "control",
	"exit":                         "control",
	"exit!":                        "control",
	"abort":                        "control",
	"at_exit":                      "control",
	"retry":                        "control",
	"Process.exit":                 "control",
	"Kernel.exit":                  "control",
	"Kernel.abort":                 "control",
	"GC.start":                     "control",
	"ObjectSpace.define_finalizer": "control",
}

var hazardCategories = []string{"sql", "exec", "deserialize", "metaprogram", "io", "net", "crypto", "concurrency", "mass_assign", "rails_query", "alloc", "control"}

var iterMethods = newSet("each", "each_pair", "each_key", "each_value", "each_entry", "each_with_index", "each_with_object", "each_slice", "each_cons", "each_line", "each_char", "each_byte", "each_index", "each_object", "map", "map!", "collect", "collect!", "flat_map", "collect_concat", "select", "select!", "filter", "filter!", "filter_map", "reject", "reject!", "detect", "find", "find_all", "find_each", "find_in_batches", "in_batches", "partition", "group_by", "sort_by", "min_by", "max_by", "minmax_by", "sum", "reduce", "inject", "count", "tally", "chunk_while", "slice_when", "take_while", "drop_while", "times", "upto", "downto", "step", "cycle", "loop", "repeated_permutation", "permutation", "combination", "product", "zip", "bsearch", "delete_if", "keep_if", "all?", "any?", "none?", "one?", "each_batch", "traverse")

var iteratorMethods = newSet("each", "each_with_index", "each_with_object", "each_pair", "each_key", "each_value", "each_line", "each_char", "each_byte", "each_slice", "each_cons", "each_entry", "reverse_each", "map", "map!", "flat_map", "collect", "collect!", "select", "select!", "filter", "filter_map", "reject", "reject!", "find", "find_all", "detect", "find_index", "sort_by", "min_by", "max_by", "group_by", "partition", "chunk_while", "slice_when", "sum", "reduce", "inject", "count", "tally", "zip", "cycle", "times", "upto", "downto", "step", "loop", "all?", "any?", "none?", "one?", "take_while", "drop_while", "delete_if", "keep_if")

var arRelation = newSet("where", "rewhere", "not", "order", "reorder", "group", "having", "joins", "left_joins", "left_outer_joins", "includes", "preload", "eager_load", "references", "select", "distinct", "limit", "offset", "lock", "readonly", "unscope", "unscoped", "reselect", "regroup", "extending", "only", "except", "merge", "or", "and", "none", "from", "create_with")

var arTerminal = newSet("find", "find_by", "find_by!", "first", "first!", "last", "last!", "take", "take!", "pluck", "pick", "count", "sum", "average", "minimum", "maximum", "ids", "exists?", "any?", "many?", "none?", "empty?", "size", "to_a", "load", "find_each", "find_in_batches", "in_batches", "each_with_relation", "reload")

var arWrite = newSet("update_all", "delete_all", "destroy_all", "update_counters", "increment_counter", "decrement_counter", "touch_all", "insert_all", "insert_all!", "upsert_all")

var arRaw = newSet("find_by_sql", "count_by_sql", "execute", "exec_query", "exec_update", "exec_delete", "select_all", "select_one", "select_value", "select_values", "select_rows")

var massAssignSinks = newSet("new", "create", "create!", "update", "update!", "update_attributes", "update_attributes!", "assign_attributes", "attributes=", "first_or_create", "first_or_create!", "find_or_create_by", "find_or_create_by!", "find_or_initialize_by", "build")

var chainAlloc = newSet("map", "collect", "flat_map", "select", "filter", "reject", "sort", "sort_by", "uniq", "compact", "flatten", "reverse", "to_a", "entries", "zip", "take", "drop", "first", "last", "values_at", "group_by", "partition", "filter_map", "each_with_index", "each_slice", "each_cons", "chars", "lines", "bytes", "split")

var coreClasses = newSet("Object", "BasicObject", "Kernel", "Module", "Class", "Comparable", "Enumerable", "String", "Symbol", "Numeric", "Integer", "Float", "Rational", "Complex", "Array", "Hash", "Set", "Range", "Struct", "Proc", "Method", "UnboundMethod", "Binding", "Exception", "StandardError", "RuntimeError", "ArgumentError", "TypeError", "NameError", "NoMethodError", "IOError", "SystemExit", "NilClass", "TrueClass", "FalseClass", "Regexp", "MatchData", "Time", "Date", "DateTime", "Data", "IO", "File", "Dir", "Thread", "Mutex", "Queue", "ConditionVariable", "Fiber", "Ractor", "Process", "Signal", "ObjectSpace", "GC", "Math", "Random", "Marshal", "Enumerator", "Encoding")

var coreReceivers = newSet("File", "Dir", "IO", "Kernel", "Object", "Module", "Class", "Marshal", "YAML", "Psych", "JSON", "Oj", "CSV", "Net", "URI", "OpenURI", "HTTParty", "Faraday", "RestClient", "Excon", "Typhoeus", "Curl", "Socket", "TCPSocket", "TCPServer", "UDPSocket", "UNIXSocket", "Digest", "OpenSSL", "SecureRandom", "Base64", "Zlib", "Thread", "Mutex", "Monitor", "Queue", "SizedQueue", "ConditionVariable", "Fiber", "Ractor", "Process", "Signal", "ObjectSpace", "GC", "Math", "Random", "Time", "Date", "DateTime", "Timeout", "Tempfile", "Pathname", "StringIO", "FileUtils", "Etc", "Shellwords", "Open3", "PTY", "Struct", "Data", "Set", "Enumerator", "Comparable", "Enumerable", "Range", "Regexp", "Rails", "ActiveRecord", "ActiveSupport", "ActionController", "ActionView", "ActiveJob", "ActionMailer", "ActiveModel", "ActiveStorage", "ActionCable", "Arel", "I18n", "Logger", "Minitest", "RSpec", "Rack", "Sidekiq", "Redis", "Concurrent", "ENV", "ARGF", "ARGV", "STDOUT", "STDERR", "STDIN")

var coreMethods = newSet("new", "class", "inspect", "to_s", "to_str", "to_i", "to_f", "to_a", "to_h", "to_sym", "to_proc", "to_json", "freeze", "frozen?", "dup", "clone", "hash", "eql?", "equal?", "nil?", "is_a?", "kind_of?", "instance_of?", "respond_to?", "tap", "then", "yield_self", "itself", "display", "object_id", "puts", "print", "p", "pp", "warn", "raise", "fail", "loop", "lambda", "proc", "format", "sprintf", "gets", "require", "require_relative", "load", "autoload", "include", "extend", "prepend", "each", "map", "select", "reject", "find", "detect", "reduce", "inject", "size", "length", "count", "first", "last", "push", "pop", "shift", "unshift", "append", "concat", "join", "split", "strip", "chomp", "chop", "upcase", "downcase", "capitalize", "sub", "gsub", "match", "match?", "scan", "start_with?", "end_with?", "include?", "index", "slice", "empty?", "any?", "all?", "none?", "one?", "sum", "min", "max", "sort", "sort_by", "uniq", "compact", "flatten", "reverse", "zip", "group_by", "partition", "each_with_index", "each_with_object", "keys", "values", "merge", "fetch", "dig", "store", "delete", "key?", "has_key?", "value?", "has_value?", "call", "arity", "curry", "super", "block_given?", "binding", "caller", "attr_accessor", "attr_reader", "attr_writer", "private", "public", "protected", "module_function", "instance_variables", "methods", "send", "public_send", "respond_to_missing?")

var arCallbacks = newSet("before_validation", "after_validation", "before_save", "around_save", "after_save", "before_create", "around_create", "after_create", "before_update", "around_update", "after_update", "before_destroy", "around_destroy", "after_destroy", "after_commit", "after_rollback", "after_initialize", "after_find", "after_touch", "before_action", "after_action", "around_action", "before_filter", "after_filter", "skip_before_action", "prepend_before_action", "append_before_action")

var arAssociations = newSet("belongs_to", "has_one", "has_many", "has_and_belongs_to_many")

var simpleReceivers = newSet("constant", "scope_resolution", "identifier", "self", "instance_variable", "class_variable", "global_variable", "super")

var requireKinds = newSet("require", "require_relative", "require_dependency", "load", "autoload", "autoload_at", "gem")

var enqueueAPIs = newSet("perform_async", "perform_later", "perform_in", "perform_at", "perform_all_at", "enqueue", "enqueue_job", "deliver_later", "deliver_later!")

var constMutateAPIs = newSet("<<", "push", "append", "concat", "unshift", "shift", "pop", "delete_if", "clear", "merge!", "replace", "insert")

var metaprogramAPIs = map[string]string{
	"send":                    "n_send",
	"public_send":             "n_send",
	"__send__":                "n_send",
	"define_method":           "n_define_method",
	"define_singleton_method": "n_define_method",
	"method_missing":          "n_method_missing",
	"respond_to_missing?":     "n_method_missing",
	"const_missing":           "n_method_missing",
	"const_get":               "n_const_get",
	"const_set":               "n_const_get",
	"constantize":             "n_const_get",
	"safe_constantize":        "n_const_get",
	"qualified_const_get":     "n_const_get",
	"instance_eval":           "n_instance_eval",
	"instance_exec":           "n_instance_eval",
	"class_eval":              "n_class_eval",
	"module_eval":             "n_class_eval",
	"class_exec":              "n_class_eval",
	"instance_variable_get":   "n_instance_var_get",
	"instance_variable_set":   "n_instance_var_get",
	"class_variable_get":      "n_instance_var_get",
	"class_variable_set":      "n_instance_var_get",
	"eval":                    "n_eval",
	"binding.eval":            "n_eval",
	"alias_method":            "n_metaprogram_other",
	"remove_method":           "n_metaprogram_other",
	"undef_method":            "n_metaprogram_other",
	"method":                  "n_metaprogram_other",
	"delegate_missing_to":     "n_metaprogram_other",
	"attr_internal":           "n_metaprogram_other",
}

var attrMacros = map[string]string{
	"attr_accessor":          "n_attr_accessor",
	"attr_reader":            "n_attr_reader",
	"attr_writer":            "n_attr_writer",
	"attr":                   "n_attr_reader",
	"mattr_accessor":         "n_attr_accessor",
	"cattr_accessor":         "n_attr_accessor",
	"class_attribute":        "n_attr_accessor",
	"mattr_reader":           "n_attr_reader",
	"cattr_reader":           "n_attr_reader",
	"mattr_writer":           "n_attr_writer",
	"cattr_writer":           "n_attr_writer",
	"attr_internal_accessor": "n_attr_accessor",
	"thread_mattr_accessor":  "n_attr_accessor",
}

var mixinKinds = map[string]string{"include": "include", "extend": "extend", "prepend": "prepend"}

var reqIndexKinds = map[string]string{"params": "query", "cookies": "cookie"}

var reqMemberKinds = map[string]string{"headers": "header", "query_parameters": "query", "request_parameters": "body"}

var logLevels = newSet("debug", "info", "warn", "warning", "error", "fatal", "unknown")

var authMarkers = []string{"auth", "login", "signed_in", "logged_in", "current_user", "session", "jwt"}

var loopCallColumns = [][2]string{
	{"where", "query_in_loop"},
	{"find_by", "query_in_loop"},
	{"pluck", "query_in_loop"},
	{"count", "query_in_loop"},
	{"first", "query_in_loop"},
	{"execute", "query_in_loop"},
	{"File.open", "io_in_loop"},
	{"File.read", "io_in_loop"},
	{"synchronize", "lock_in_loop"},
	{"gsub", "regex_in_loop"},
	{"match", "regex_in_loop"},
	{"Regexp.new", "regex_in_loop"},
}

type symRow struct {
	Id                   int32
	FileId               int32
	ModuleId             int32
	ParentId             int32
	Name                 string
	QualName             string
	Kind                 string
	LineStart            int32
	LineEnd              int32
	NLines               int32
	ByteStart            int32
	ByteEnd              int32
	Signature            string
	ReturnType           string
	Visibility           string
	NParams              int32
	NOptionalParams      int32
	NGenericParams       int32
	NOverloads           int32
	ArityRank            int32
	IsPublic             int32
	IsStatic             int32
	IsAsync              int32
	IsGenerator          int32
	IsAbstract           int32
	IsOverride           int32
	IsExported           int32
	IsTest               int32
	IsDeprecated         int32
	IsEntrypoint         int32
	IsGenerated          int32
	Sloc                 int32
	BodyBytes            int32
	NCommentLines        int32
	NDocLines            int32
	HasDoc               int32
	Cyclomatic           int32
	Cognitive            int32
	MaxNesting           int32
	NTokens              int32
	NOperators           int32
	NOperands            int32
	NDistinctOperators   int32
	NDistinctOperands    int32
	HalsteadVolume       int64
	Maintainability      int32
	NLoops               int32
	NBranches            int32
	NReturns             int32
	NEarlyReturns        int32
	NSwitch              int32
	NCases               int32
	NTernary             int32
	NLogical             int32
	NTry                 int32
	NCatch               int32
	NCatchBroad          int32
	NCatchEmpty          int32
	NFinally             int32
	NThrow               int32
	NLabels              int32
	NGotos               int32
	MaxLoopDepth         int32
	CallInLoop           int32
	AllocInLoop          int32
	IoInLoop             int32
	AwaitInLoop          int32
	LockInLoop           int32
	ConcatInLoop         int32
	RegexInLoop          int32
	QueryInLoop          int32
	BranchInLoop         int32
	NLocals              int32
	NAssign              int32
	NCompoundAssign      int32
	NIncdec              int32
	NCmp                 int32
	NBitop               int32
	NShift               int32
	NArith               int32
	NStringLit           int32
	NRegexLit            int32
	NFloatLit            int32
	NMagic               int32
	NNullCheck           int32
	NSubscript           int32
	NMemberAccess        int32
	NLambda              int32
	NClosureCapture      int32
	NCalls               int32
	NUniqueCalls         int32
	NDynamicCalls        int32
	NUnresolvedCalls     int32
	FanIn                int32
	FanOut               int32
	NCallsites           int32
	IsRecursive          int32
	IsLeaf               int32
	IsRoot               int32
	NHazards             int32
	RiskScore            int32
	NSql                 int32
	NExec                int32
	NDeserialize         int32
	NMetaprogram         int32
	NIo                  int32
	NNet                 int32
	NCrypto              int32
	NConcurrency         int32
	NMassAssign          int32
	NRailsQuery          int32
	NAlloc               int32
	NControl             int32
	NSend                int32
	NDefineMethod        int32
	NMethodMissing       int32
	NConstGet            int32
	NInstanceEval        int32
	NClassEval           int32
	NInstanceVarGet      int32
	NEval                int32
	NMetaprogramOther    int32
	NMetaprogramTotal    int32
	NMetaprogramDynamic  int32
	NBlocks              int32
	NBlockPass           int32
	NBlockGiven          int32
	NYield               int32
	NProcNew             int32
	NSymbolToProc        int32
	NIterBlocks          int32
	MaxBlockDepth        int32
	NRescue              int32
	NRescueBare          int32
	NRescueException     int32
	NRescueEmpty         int32
	NRescueReraise       int32
	NRetry               int32
	NEnsure              int32
	NRaise               int32
	NClassVar            int32
	NInstanceVar         int32
	NGlobalVar           int32
	NClassLevelIvar      int32
	NClassLevelWrite     int32
	NAttrAccessor        int32
	NAttrReader          int32
	NAttrWriter          int32
	NArQuery             int32
	NArQueryInBlock      int32
	NArTerminal          int32
	NArWrite             int32
	NPermit              int32
	NPermitBang          int32
	NParamsRead          int32
	NSqlInterp           int32
	NSqlLiteral          int32
	NSqlSanitized        int32
	NStringInterp        int32
	NStrLitInLoop        int32
	NCollectionLitInLoop int32
	NChainArrayAlloc     int32
	NMapChain            int32
	NTimesMap            int32
	NRangeInclude        int32
	NFreeze              int32
	NDupClone            int32
	NHashLit             int32
	NArrayLit            int32
	NHeredoc             int32
	NSubshell            int32
	NMonkeyPatch         int32
	NMixins              int32
	NTimeout             int32
	NThreadNew           int32
	NMutex               int32
	NRactor              int32
	NThreadLocal         int32
	NAlias               int32
	NSuper               int32
	NForwarding          int32
	NEndData             int32
	NSystemCall          int32
	NConstantize         int32
	NHtmlSafe            int32
	NRawSql              int32
	NWeakHash            int32
	NWeakRandom          int32
	NRedirect            int32
	NAuthCall            int32
	NFetch               int32
	NXxeParser           int32
	NDynamicOpen         int32
	NZipRead             int32
	NLogCall             int32
	NOpenCall            int32
	NSleepCall           int32
	NIncludeInLoop       int32
	NEnumInLoop          int32
	NCountInLoop         int32
	NArWriteInLoop       int32
	NSerializeInLoop     int32
	NElif                int32
	NExternalCalls       int32
	NSaveIgnored         int32
	NLegacyChain         int32
	HasSig               int32
	NConstRef            int32
	NToSym               int32
	NRegexDyn            int32
	NEnqueue             int32
	NEnqueueInLoop       int32
	NZonelessTime        int32
	NConstMutate         int32
	NThreadJoin          int32
	HasFrozenLiteral     int32
	IsController         int32
	IsModel              int32
	IsJob                int32
	IsConcern            int32
	IsSingleton          int32
	IsEndless            int32
	IsThreadedEntry      int32
}

type Sym struct {
	Id                   int32
	FileId               int32
	ModuleId             int32
	ParentId             int32
	name                 cgStr
	qualName             cgStr
	kind                 cgStr
	LineStart            int32
	visibility           cgStr
	NParams              int32
	NOptionalParams      int32
	IsPublic             int32
	IsAbstract           int32
	IsTest               int32
	IsEntrypoint         int32
	IsGenerated          int32
	Sloc                 int32
	Cyclomatic           int32
	Cognitive            int32
	MaxNesting           int32
	NLoops               int32
	NBranches            int32
	NCases               int32
	MaxLoopDepth         int32
	CallInLoop           int32
	LockInLoop           int32
	RegexInLoop          int32
	QueryInLoop          int32
	NStringLit           int32
	NRegexLit            int32
	NLambda              int32
	NCalls               int32
	NUnresolvedCalls     int32
	FanIn                int32
	FanOut               int32
	NCallsites           int32
	IsRecursive          int32
	NHazards             int32
	RiskScore            int32
	NSql                 int32
	NExec                int32
	NIo                  int32
	NNet                 int32
	NMassAssign          int32
	NRailsQuery          int32
	NSend                int32
	NDefineMethod        int32
	NMethodMissing       int32
	NConstGet            int32
	NInstanceEval        int32
	NClassEval           int32
	NEval                int32
	NMetaprogramTotal    int32
	NMetaprogramDynamic  int32
	NBlocks              int32
	NBlockPass           int32
	NBlockGiven          int32
	NYield               int32
	NProcNew             int32
	NSymbolToProc        int32
	NIterBlocks          int32
	MaxBlockDepth        int32
	NRescue              int32
	NRescueBare          int32
	NRescueException     int32
	NRescueEmpty         int32
	NRescueReraise       int32
	NRetry               int32
	NEnsure              int32
	NRaise               int32
	NClassVar            int32
	NGlobalVar           int32
	NClassLevelIvar      int32
	NClassLevelWrite     int32
	NAttrAccessor        int32
	NAttrReader          int32
	NAttrWriter          int32
	NArQuery             int32
	NArQueryInBlock      int32
	NArWrite             int32
	NPermit              int32
	NPermitBang          int32
	NParamsRead          int32
	NSqlInterp           int32
	NSqlLiteral          int32
	NSqlSanitized        int32
	NStringInterp        int32
	NStrLitInLoop        int32
	NCollectionLitInLoop int32
	NChainArrayAlloc     int32
	NMapChain            int32
	NTimesMap            int32
	NRangeInclude        int32
	NFreeze              int32
	NDupClone            int32
	NHeredoc             int32
	NSubshell            int32
	NMonkeyPatch         int32
	NMixins              int32
	NTimeout             int32
	NThreadNew           int32
	NMutex               int32
	NRactor              int32
	NThreadLocal         int32
	NAlias               int32
	NSuper               int32
	NSystemCall          int32
	NConstantize         int32
	NHtmlSafe            int32
	NRawSql              int32
	NWeakHash            int32
	NWeakRandom          int32
	NRedirect            int32
	NAuthCall            int32
	NFetch               int32
	NXxeParser           int32
	NDynamicOpen         int32
	NZipRead             int32
	NLogCall             int32
	NOpenCall            int32
	NSleepCall           int32
	NEnumInLoop          int32
	NCountInLoop         int32
	NArWriteInLoop       int32
	NSerializeInLoop     int32
	NExternalCalls       int32
	NSaveIgnored         int32
	NLegacyChain         int32
	HasSig               int32
	NConstRef            int32
	NToSym               int32
	NRegexDyn            int32
	NEnqueue             int32
	NEnqueueInLoop       int32
	NZonelessTime        int32
	NConstMutate         int32
	NThreadJoin          int32
	HasFrozenLiteral     int32
	IsController         int32
	IsModel              int32
	IsJob                int32
	IsEndless            int32
	IsThreadedEntry      int32
}

func (s *Sym) Name() string       { return s.name.Str() }
func (s *Sym) QualName() string   { return s.qualName.Str() }
func (s *Sym) Kind() string       { return s.kind.Str() }
func (s *Sym) Visibility() string { return s.visibility.Str() }

type symCold struct {
	LineEnd            int16
	NLines             int16
	ByteStart          int16
	ByteEnd            int16
	IsStatic           int16
	IsGenerator        int16
	BodyBytes          int16
	NCommentLines      int16
	NDocLines          int16
	HasDoc             int16
	NTokens            int16
	NOperators         int16
	NOperands          int16
	NDistinctOperators int16
	NDistinctOperands  int16
	Maintainability    int16
	NReturns           int16
	NSwitch            int16
	NTernary           int16
	IoInLoop           int16
	BranchInLoop       int16
	NAssign            int16
	NCompoundAssign    int16
	NFloatLit          int16
	NMagic             int16
	NSubscript         int16
	NUniqueCalls       int16
	NDynamicCalls      int16
	IsLeaf             int16
	IsRoot             int16
	NDeserialize       int16
	NMetaprogram       int16
	NCrypto            int16
	NConcurrency       int16
	NAlloc             int16
	NControl           int16
	NInstanceVarGet    int16
	NMetaprogramOther  int16
	NInstanceVar       int16
	NArTerminal        int16
	NHashLit           int16
	NArrayLit          int16
	NForwarding        int16
	NEndData           int16
	NIncludeInLoop     int16
	NElif              int16
	IsConcern          int16
	IsSingleton        int16
}

type symColdWide struct {
	LineEnd            int32
	NLines             int32
	ByteStart          int32
	ByteEnd            int32
	IsStatic           int32
	IsGenerator        int32
	BodyBytes          int32
	NCommentLines      int32
	NDocLines          int32
	HasDoc             int32
	NTokens            int32
	NOperators         int32
	NOperands          int32
	NDistinctOperators int32
	NDistinctOperands  int32
	Maintainability    int32
	NReturns           int32
	NSwitch            int32
	NTernary           int32
	IoInLoop           int32
	BranchInLoop       int32
	NAssign            int32
	NCompoundAssign    int32
	NFloatLit          int32
	NMagic             int32
	NSubscript         int32
	NUniqueCalls       int32
	NDynamicCalls      int32
	IsLeaf             int32
	IsRoot             int32
	NDeserialize       int32
	NMetaprogram       int32
	NCrypto            int32
	NConcurrency       int32
	NAlloc             int32
	NControl           int32
	NInstanceVarGet    int32
	NMetaprogramOther  int32
	NInstanceVar       int32
	NArTerminal        int32
	NHashLit           int32
	NArrayLit          int32
	NForwarding        int32
	NEndData           int32
	NIncludeInLoop     int32
	NElif              int32
	IsConcern          int32
	IsSingleton        int32
}

type sigRef struct {
	blk, off, n int32
}

func narrow16(v int32) (int16, bool) {
	if v < 32768 && v > -32769 {
		return int16(v), true
	}
	return 0, false
}

func (b *builder) convertSym(r *symRow) (*Sym, symCold, sigRef, *symColdWide) {
	s := b.newSym()
	s.Id = r.Id
	s.FileId = r.FileId
	s.ModuleId = r.ModuleId
	s.ParentId = r.ParentId
	s.name = cgPut(r.Name)
	s.qualName = cgPut(r.QualName)
	s.kind = cgPut(r.Kind)
	s.LineStart = r.LineStart
	s.visibility = cgPut(r.Visibility)
	s.NParams = r.NParams
	s.NOptionalParams = r.NOptionalParams
	s.IsPublic = r.IsPublic
	s.IsAbstract = r.IsAbstract
	s.IsTest = r.IsTest
	s.IsEntrypoint = r.IsEntrypoint
	s.IsGenerated = r.IsGenerated
	s.Sloc = r.Sloc
	s.Cyclomatic = r.Cyclomatic
	s.Cognitive = r.Cognitive
	s.MaxNesting = r.MaxNesting
	s.NLoops = r.NLoops
	s.NBranches = r.NBranches
	s.NCases = r.NCases
	s.MaxLoopDepth = r.MaxLoopDepth
	s.CallInLoop = r.CallInLoop
	s.LockInLoop = r.LockInLoop
	s.RegexInLoop = r.RegexInLoop
	s.QueryInLoop = r.QueryInLoop
	s.NStringLit = r.NStringLit
	s.NRegexLit = r.NRegexLit
	s.NLambda = r.NLambda
	s.NCalls = r.NCalls
	s.NUnresolvedCalls = r.NUnresolvedCalls
	s.FanIn = r.FanIn
	s.FanOut = r.FanOut
	s.NCallsites = r.NCallsites
	s.IsRecursive = r.IsRecursive
	s.NHazards = r.NHazards
	s.RiskScore = r.RiskScore
	s.NSql = r.NSql
	s.NExec = r.NExec
	s.NIo = r.NIo
	s.NNet = r.NNet
	s.NMassAssign = r.NMassAssign
	s.NRailsQuery = r.NRailsQuery
	s.NSend = r.NSend
	s.NDefineMethod = r.NDefineMethod
	s.NMethodMissing = r.NMethodMissing
	s.NConstGet = r.NConstGet
	s.NInstanceEval = r.NInstanceEval
	s.NClassEval = r.NClassEval
	s.NEval = r.NEval
	s.NMetaprogramTotal = r.NMetaprogramTotal
	s.NMetaprogramDynamic = r.NMetaprogramDynamic
	s.NBlocks = r.NBlocks
	s.NBlockPass = r.NBlockPass
	s.NBlockGiven = r.NBlockGiven
	s.NYield = r.NYield
	s.NProcNew = r.NProcNew
	s.NSymbolToProc = r.NSymbolToProc
	s.NIterBlocks = r.NIterBlocks
	s.MaxBlockDepth = r.MaxBlockDepth
	s.NRescue = r.NRescue
	s.NRescueBare = r.NRescueBare
	s.NRescueException = r.NRescueException
	s.NRescueEmpty = r.NRescueEmpty
	s.NRescueReraise = r.NRescueReraise
	s.NRetry = r.NRetry
	s.NEnsure = r.NEnsure
	s.NRaise = r.NRaise
	s.NClassVar = r.NClassVar
	s.NGlobalVar = r.NGlobalVar
	s.NClassLevelIvar = r.NClassLevelIvar
	s.NClassLevelWrite = r.NClassLevelWrite
	s.NAttrAccessor = r.NAttrAccessor
	s.NAttrReader = r.NAttrReader
	s.NAttrWriter = r.NAttrWriter
	s.NArQuery = r.NArQuery
	s.NArQueryInBlock = r.NArQueryInBlock
	s.NArWrite = r.NArWrite
	s.NPermit = r.NPermit
	s.NPermitBang = r.NPermitBang
	s.NParamsRead = r.NParamsRead
	s.NSqlInterp = r.NSqlInterp
	s.NSqlLiteral = r.NSqlLiteral
	s.NSqlSanitized = r.NSqlSanitized
	s.NStringInterp = r.NStringInterp
	s.NStrLitInLoop = r.NStrLitInLoop
	s.NCollectionLitInLoop = r.NCollectionLitInLoop
	s.NChainArrayAlloc = r.NChainArrayAlloc
	s.NMapChain = r.NMapChain
	s.NTimesMap = r.NTimesMap
	s.NRangeInclude = r.NRangeInclude
	s.NFreeze = r.NFreeze
	s.NDupClone = r.NDupClone
	s.NHeredoc = r.NHeredoc
	s.NSubshell = r.NSubshell
	s.NMonkeyPatch = r.NMonkeyPatch
	s.NMixins = r.NMixins
	s.NTimeout = r.NTimeout
	s.NThreadNew = r.NThreadNew
	s.NMutex = r.NMutex
	s.NRactor = r.NRactor
	s.NThreadLocal = r.NThreadLocal
	s.NAlias = r.NAlias
	s.NSuper = r.NSuper
	s.NSystemCall = r.NSystemCall
	s.NConstantize = r.NConstantize
	s.NHtmlSafe = r.NHtmlSafe
	s.NRawSql = r.NRawSql
	s.NWeakHash = r.NWeakHash
	s.NWeakRandom = r.NWeakRandom
	s.NRedirect = r.NRedirect
	s.NAuthCall = r.NAuthCall
	s.NFetch = r.NFetch
	s.NXxeParser = r.NXxeParser
	s.NDynamicOpen = r.NDynamicOpen
	s.NZipRead = r.NZipRead
	s.NLogCall = r.NLogCall
	s.NOpenCall = r.NOpenCall
	s.NSleepCall = r.NSleepCall
	s.NEnumInLoop = r.NEnumInLoop
	s.NCountInLoop = r.NCountInLoop
	s.NArWriteInLoop = r.NArWriteInLoop
	s.NSerializeInLoop = r.NSerializeInLoop
	s.NExternalCalls = r.NExternalCalls
	s.NSaveIgnored = r.NSaveIgnored
	s.NLegacyChain = r.NLegacyChain
	s.HasSig = r.HasSig
	s.NConstRef = r.NConstRef
	s.NToSym = r.NToSym
	s.NRegexDyn = r.NRegexDyn
	s.NEnqueue = r.NEnqueue
	s.NEnqueueInLoop = r.NEnqueueInLoop
	s.NZonelessTime = r.NZonelessTime
	s.NConstMutate = r.NConstMutate
	s.NThreadJoin = r.NThreadJoin
	s.HasFrozenLiteral = r.HasFrozenLiteral
	s.IsController = r.IsController
	s.IsModel = r.IsModel
	s.IsJob = r.IsJob
	s.IsEndless = r.IsEndless
	s.IsThreadedEntry = r.IsThreadedEntry
	c := symCold{}
	ct := b.g.sigPut(r.Signature)
	var w *symColdWide
	b.g.halvPut(r.HalsteadVolume)
	if v, ok := narrow16(r.LineEnd); ok {
		c.LineEnd = v
	} else {
		if w == nil {
			w = &symColdWide{}
		}
		w.LineEnd = r.LineEnd
	}
	if v, ok := narrow16(r.NLines); ok {
		c.NLines = v
	} else {
		if w == nil {
			w = &symColdWide{}
		}
		w.NLines = r.NLines
	}
	if v, ok := narrow16(r.ByteStart); ok {
		c.ByteStart = v
	} else {
		if w == nil {
			w = &symColdWide{}
		}
		w.ByteStart = r.ByteStart
	}
	if v, ok := narrow16(r.ByteEnd); ok {
		c.ByteEnd = v
	} else {
		if w == nil {
			w = &symColdWide{}
		}
		w.ByteEnd = r.ByteEnd
	}
	if v, ok := narrow16(r.IsStatic); ok {
		c.IsStatic = v
	} else {
		if w == nil {
			w = &symColdWide{}
		}
		w.IsStatic = r.IsStatic
	}
	if v, ok := narrow16(r.IsGenerator); ok {
		c.IsGenerator = v
	} else {
		if w == nil {
			w = &symColdWide{}
		}
		w.IsGenerator = r.IsGenerator
	}
	if v, ok := narrow16(r.BodyBytes); ok {
		c.BodyBytes = v
	} else {
		if w == nil {
			w = &symColdWide{}
		}
		w.BodyBytes = r.BodyBytes
	}
	if v, ok := narrow16(r.NCommentLines); ok {
		c.NCommentLines = v
	} else {
		if w == nil {
			w = &symColdWide{}
		}
		w.NCommentLines = r.NCommentLines
	}
	if v, ok := narrow16(r.NDocLines); ok {
		c.NDocLines = v
	} else {
		if w == nil {
			w = &symColdWide{}
		}
		w.NDocLines = r.NDocLines
	}
	if v, ok := narrow16(r.HasDoc); ok {
		c.HasDoc = v
	} else {
		if w == nil {
			w = &symColdWide{}
		}
		w.HasDoc = r.HasDoc
	}
	if v, ok := narrow16(r.NTokens); ok {
		c.NTokens = v
	} else {
		if w == nil {
			w = &symColdWide{}
		}
		w.NTokens = r.NTokens
	}
	if v, ok := narrow16(r.NOperators); ok {
		c.NOperators = v
	} else {
		if w == nil {
			w = &symColdWide{}
		}
		w.NOperators = r.NOperators
	}
	if v, ok := narrow16(r.NOperands); ok {
		c.NOperands = v
	} else {
		if w == nil {
			w = &symColdWide{}
		}
		w.NOperands = r.NOperands
	}
	if v, ok := narrow16(r.NDistinctOperators); ok {
		c.NDistinctOperators = v
	} else {
		if w == nil {
			w = &symColdWide{}
		}
		w.NDistinctOperators = r.NDistinctOperators
	}
	if v, ok := narrow16(r.NDistinctOperands); ok {
		c.NDistinctOperands = v
	} else {
		if w == nil {
			w = &symColdWide{}
		}
		w.NDistinctOperands = r.NDistinctOperands
	}
	if v, ok := narrow16(r.Maintainability); ok {
		c.Maintainability = v
	} else {
		if w == nil {
			w = &symColdWide{}
		}
		w.Maintainability = r.Maintainability
	}
	if v, ok := narrow16(r.NReturns); ok {
		c.NReturns = v
	} else {
		if w == nil {
			w = &symColdWide{}
		}
		w.NReturns = r.NReturns
	}
	if v, ok := narrow16(r.NSwitch); ok {
		c.NSwitch = v
	} else {
		if w == nil {
			w = &symColdWide{}
		}
		w.NSwitch = r.NSwitch
	}
	if v, ok := narrow16(r.NTernary); ok {
		c.NTernary = v
	} else {
		if w == nil {
			w = &symColdWide{}
		}
		w.NTernary = r.NTernary
	}
	if v, ok := narrow16(r.IoInLoop); ok {
		c.IoInLoop = v
	} else {
		if w == nil {
			w = &symColdWide{}
		}
		w.IoInLoop = r.IoInLoop
	}
	if v, ok := narrow16(r.BranchInLoop); ok {
		c.BranchInLoop = v
	} else {
		if w == nil {
			w = &symColdWide{}
		}
		w.BranchInLoop = r.BranchInLoop
	}
	if v, ok := narrow16(r.NAssign); ok {
		c.NAssign = v
	} else {
		if w == nil {
			w = &symColdWide{}
		}
		w.NAssign = r.NAssign
	}
	if v, ok := narrow16(r.NCompoundAssign); ok {
		c.NCompoundAssign = v
	} else {
		if w == nil {
			w = &symColdWide{}
		}
		w.NCompoundAssign = r.NCompoundAssign
	}
	if v, ok := narrow16(r.NFloatLit); ok {
		c.NFloatLit = v
	} else {
		if w == nil {
			w = &symColdWide{}
		}
		w.NFloatLit = r.NFloatLit
	}
	if v, ok := narrow16(r.NMagic); ok {
		c.NMagic = v
	} else {
		if w == nil {
			w = &symColdWide{}
		}
		w.NMagic = r.NMagic
	}
	if v, ok := narrow16(r.NSubscript); ok {
		c.NSubscript = v
	} else {
		if w == nil {
			w = &symColdWide{}
		}
		w.NSubscript = r.NSubscript
	}
	if v, ok := narrow16(r.NUniqueCalls); ok {
		c.NUniqueCalls = v
	} else {
		if w == nil {
			w = &symColdWide{}
		}
		w.NUniqueCalls = r.NUniqueCalls
	}
	if v, ok := narrow16(r.NDynamicCalls); ok {
		c.NDynamicCalls = v
	} else {
		if w == nil {
			w = &symColdWide{}
		}
		w.NDynamicCalls = r.NDynamicCalls
	}
	if v, ok := narrow16(r.IsLeaf); ok {
		c.IsLeaf = v
	} else {
		if w == nil {
			w = &symColdWide{}
		}
		w.IsLeaf = r.IsLeaf
	}
	if v, ok := narrow16(r.IsRoot); ok {
		c.IsRoot = v
	} else {
		if w == nil {
			w = &symColdWide{}
		}
		w.IsRoot = r.IsRoot
	}
	if v, ok := narrow16(r.NDeserialize); ok {
		c.NDeserialize = v
	} else {
		if w == nil {
			w = &symColdWide{}
		}
		w.NDeserialize = r.NDeserialize
	}
	if v, ok := narrow16(r.NMetaprogram); ok {
		c.NMetaprogram = v
	} else {
		if w == nil {
			w = &symColdWide{}
		}
		w.NMetaprogram = r.NMetaprogram
	}
	if v, ok := narrow16(r.NCrypto); ok {
		c.NCrypto = v
	} else {
		if w == nil {
			w = &symColdWide{}
		}
		w.NCrypto = r.NCrypto
	}
	if v, ok := narrow16(r.NConcurrency); ok {
		c.NConcurrency = v
	} else {
		if w == nil {
			w = &symColdWide{}
		}
		w.NConcurrency = r.NConcurrency
	}
	if v, ok := narrow16(r.NAlloc); ok {
		c.NAlloc = v
	} else {
		if w == nil {
			w = &symColdWide{}
		}
		w.NAlloc = r.NAlloc
	}
	if v, ok := narrow16(r.NControl); ok {
		c.NControl = v
	} else {
		if w == nil {
			w = &symColdWide{}
		}
		w.NControl = r.NControl
	}
	if v, ok := narrow16(r.NInstanceVarGet); ok {
		c.NInstanceVarGet = v
	} else {
		if w == nil {
			w = &symColdWide{}
		}
		w.NInstanceVarGet = r.NInstanceVarGet
	}
	if v, ok := narrow16(r.NMetaprogramOther); ok {
		c.NMetaprogramOther = v
	} else {
		if w == nil {
			w = &symColdWide{}
		}
		w.NMetaprogramOther = r.NMetaprogramOther
	}
	if v, ok := narrow16(r.NInstanceVar); ok {
		c.NInstanceVar = v
	} else {
		if w == nil {
			w = &symColdWide{}
		}
		w.NInstanceVar = r.NInstanceVar
	}
	if v, ok := narrow16(r.NArTerminal); ok {
		c.NArTerminal = v
	} else {
		if w == nil {
			w = &symColdWide{}
		}
		w.NArTerminal = r.NArTerminal
	}
	if v, ok := narrow16(r.NHashLit); ok {
		c.NHashLit = v
	} else {
		if w == nil {
			w = &symColdWide{}
		}
		w.NHashLit = r.NHashLit
	}
	if v, ok := narrow16(r.NArrayLit); ok {
		c.NArrayLit = v
	} else {
		if w == nil {
			w = &symColdWide{}
		}
		w.NArrayLit = r.NArrayLit
	}
	if v, ok := narrow16(r.NForwarding); ok {
		c.NForwarding = v
	} else {
		if w == nil {
			w = &symColdWide{}
		}
		w.NForwarding = r.NForwarding
	}
	if v, ok := narrow16(r.NEndData); ok {
		c.NEndData = v
	} else {
		if w == nil {
			w = &symColdWide{}
		}
		w.NEndData = r.NEndData
	}
	if v, ok := narrow16(r.NIncludeInLoop); ok {
		c.NIncludeInLoop = v
	} else {
		if w == nil {
			w = &symColdWide{}
		}
		w.NIncludeInLoop = r.NIncludeInLoop
	}
	if v, ok := narrow16(r.NElif); ok {
		c.NElif = v
	} else {
		if w == nil {
			w = &symColdWide{}
		}
		w.NElif = r.NElif
	}
	if v, ok := narrow16(r.IsConcern); ok {
		c.IsConcern = v
	} else {
		if w == nil {
			w = &symColdWide{}
		}
		w.IsConcern = r.IsConcern
	}
	if v, ok := narrow16(r.IsSingleton); ok {
		c.IsSingleton = v
	} else {
		if w == nil {
			w = &symColdWide{}
		}
		w.IsSingleton = r.IsSingleton
	}
	return s, c, ct, w
}

func (g *Graph) appendSymCells(dst []byte, i int) []byte {
	s := g.Syms[i]
	c := g.cold[i]
	sg := g.sigRefs[i]
	w := g.coldWide[s.Id]
	first := true
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.Id)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.FileId)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.ModuleId)
	dst = appendCellSep(dst, !first)
	first = false
	if s.ParentId == 0 {
		dst = appendNullCell(dst)
	} else {
		dst = appendIntCell(dst, s.ParentId)
	}
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendStrCell(dst, s.Name())
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendStrCell(dst, s.QualName())
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendStrCell(dst, s.Kind())
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.LineStart)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendInt64Cell(dst, COLD64(c.LineEnd, w.LineEnd))
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendInt64Cell(dst, COLD64(c.NLines, w.NLines))
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendInt64Cell(dst, COLD64(c.ByteStart, w.ByteStart))
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendInt64Cell(dst, COLD64(c.ByteEnd, w.ByteEnd))
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendStrCell(dst, g.sigString(sg))
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendStrCell(dst, "")
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendStrCell(dst, s.Visibility())
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NParams)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NOptionalParams)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, 0)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, 0)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, 0)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.IsPublic)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendInt64Cell(dst, COLD64(c.IsStatic, w.IsStatic))
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, 0)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendInt64Cell(dst, COLD64(c.IsGenerator, w.IsGenerator))
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.IsAbstract)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, 0)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, 0)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.IsTest)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, 0)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.IsEntrypoint)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.IsGenerated)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.Sloc)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendInt64Cell(dst, COLD64(c.BodyBytes, w.BodyBytes))
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendInt64Cell(dst, COLD64(c.NCommentLines, w.NCommentLines))
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendInt64Cell(dst, COLD64(c.NDocLines, w.NDocLines))
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendInt64Cell(dst, COLD64(c.HasDoc, w.HasDoc))
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.Cyclomatic)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.Cognitive)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.MaxNesting)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendInt64Cell(dst, COLD64(c.NTokens, w.NTokens))
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendInt64Cell(dst, COLD64(c.NOperators, w.NOperators))
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendInt64Cell(dst, COLD64(c.NOperands, w.NOperands))
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendInt64Cell(dst, COLD64(c.NDistinctOperators, w.NDistinctOperators))
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendInt64Cell(dst, COLD64(c.NDistinctOperands, w.NDistinctOperands))
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendInt64Cell(dst, g.halv[i])
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendInt64Cell(dst, COLD64(c.Maintainability, w.Maintainability))
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NLoops)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NBranches)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendInt64Cell(dst, COLD64(c.NReturns, w.NReturns))
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, 0)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendInt64Cell(dst, COLD64(c.NSwitch, w.NSwitch))
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NCases)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendInt64Cell(dst, COLD64(c.NTernary, w.NTernary))
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, 0)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, 0)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, 0)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, 0)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, 0)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, 0)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, 0)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, 0)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, 0)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.MaxLoopDepth)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.CallInLoop)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, 0)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendInt64Cell(dst, COLD64(c.IoInLoop, w.IoInLoop))
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, 0)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.LockInLoop)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, 0)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.RegexInLoop)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.QueryInLoop)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendInt64Cell(dst, COLD64(c.BranchInLoop, w.BranchInLoop))
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, 0)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendInt64Cell(dst, COLD64(c.NAssign, w.NAssign))
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendInt64Cell(dst, COLD64(c.NCompoundAssign, w.NCompoundAssign))
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, 0)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, 0)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, 0)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, 0)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, 0)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NStringLit)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NRegexLit)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendInt64Cell(dst, COLD64(c.NFloatLit, w.NFloatLit))
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendInt64Cell(dst, COLD64(c.NMagic, w.NMagic))
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, 0)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendInt64Cell(dst, COLD64(c.NSubscript, w.NSubscript))
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, 0)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NLambda)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, 0)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NCalls)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendInt64Cell(dst, COLD64(c.NUniqueCalls, w.NUniqueCalls))
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendInt64Cell(dst, COLD64(c.NDynamicCalls, w.NDynamicCalls))
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NUnresolvedCalls)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.FanIn)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.FanOut)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NCallsites)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.IsRecursive)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendInt64Cell(dst, COLD64(c.IsLeaf, w.IsLeaf))
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendInt64Cell(dst, COLD64(c.IsRoot, w.IsRoot))
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NHazards)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.RiskScore)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NSql)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NExec)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendInt64Cell(dst, COLD64(c.NDeserialize, w.NDeserialize))
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendInt64Cell(dst, COLD64(c.NMetaprogram, w.NMetaprogram))
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NIo)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NNet)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendInt64Cell(dst, COLD64(c.NCrypto, w.NCrypto))
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendInt64Cell(dst, COLD64(c.NConcurrency, w.NConcurrency))
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NMassAssign)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NRailsQuery)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendInt64Cell(dst, COLD64(c.NAlloc, w.NAlloc))
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendInt64Cell(dst, COLD64(c.NControl, w.NControl))
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NSend)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NDefineMethod)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NMethodMissing)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NConstGet)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NInstanceEval)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NClassEval)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendInt64Cell(dst, COLD64(c.NInstanceVarGet, w.NInstanceVarGet))
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NEval)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendInt64Cell(dst, COLD64(c.NMetaprogramOther, w.NMetaprogramOther))
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NMetaprogramTotal)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NMetaprogramDynamic)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NBlocks)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NBlockPass)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NBlockGiven)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NYield)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NProcNew)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NSymbolToProc)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NIterBlocks)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.MaxBlockDepth)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NRescue)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NRescueBare)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NRescueException)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NRescueEmpty)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NRescueReraise)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NRetry)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NEnsure)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NRaise)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NClassVar)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendInt64Cell(dst, COLD64(c.NInstanceVar, w.NInstanceVar))
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NGlobalVar)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NClassLevelIvar)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NClassLevelWrite)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NAttrAccessor)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NAttrReader)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NAttrWriter)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NArQuery)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NArQueryInBlock)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendInt64Cell(dst, COLD64(c.NArTerminal, w.NArTerminal))
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NArWrite)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NPermit)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NPermitBang)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NParamsRead)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NSqlInterp)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NSqlLiteral)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NSqlSanitized)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NStringInterp)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NStrLitInLoop)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NCollectionLitInLoop)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NChainArrayAlloc)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NMapChain)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NTimesMap)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NRangeInclude)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NFreeze)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NDupClone)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendInt64Cell(dst, COLD64(c.NHashLit, w.NHashLit))
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendInt64Cell(dst, COLD64(c.NArrayLit, w.NArrayLit))
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NHeredoc)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NSubshell)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NMonkeyPatch)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NMixins)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NTimeout)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NThreadNew)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NMutex)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NRactor)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NThreadLocal)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NAlias)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NSuper)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendInt64Cell(dst, COLD64(c.NForwarding, w.NForwarding))
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendInt64Cell(dst, COLD64(c.NEndData, w.NEndData))
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NSystemCall)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NConstantize)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NHtmlSafe)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NRawSql)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NWeakHash)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NWeakRandom)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NRedirect)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NAuthCall)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NFetch)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NXxeParser)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NDynamicOpen)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NZipRead)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NLogCall)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NOpenCall)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NSleepCall)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendInt64Cell(dst, COLD64(c.NIncludeInLoop, w.NIncludeInLoop))
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NEnumInLoop)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NCountInLoop)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NArWriteInLoop)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NSerializeInLoop)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendInt64Cell(dst, COLD64(c.NElif, w.NElif))
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NExternalCalls)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NSaveIgnored)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NLegacyChain)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.HasSig)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NConstRef)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NToSym)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NRegexDyn)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NEnqueue)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NEnqueueInLoop)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NZonelessTime)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NConstMutate)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.NThreadJoin)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.HasFrozenLiteral)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.IsController)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.IsModel)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.IsJob)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendInt64Cell(dst, COLD64(c.IsConcern, w.IsConcern))
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendInt64Cell(dst, COLD64(c.IsSingleton, w.IsSingleton))
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.IsEndless)
	dst = appendCellSep(dst, !first)
	first = false
	dst = appendIntCell(dst, s.IsThreadedEntry)
	return dst
}

func COLD64(c int16, wide int32) int64 {
	if wide != 0 {
		return int64(wide)
	}
	return int64(c)
}

const sigBlockLen = 1 << 20

func (g *Graph) sigPut(s string) sigRef {
	if len(s) == 0 {
		return sigRef{blk: -1}
	}

	if g.sigBlk < 0 || g.sigBlk >= len(g.sigBases) || sigBlockLen-g.sigOff < len(s) {
		cgMu.Lock()
		g.sigBases = append(g.sigBases, uint64(len(cgArena)))
		cgArena = append(cgArena, make([]byte, sigBlockLen)...)
		cgArenaBase.Store(unsafe.SliceData(cgArena))
		cgMu.Unlock()
		g.sigBlk = len(g.sigBases) - 1
		g.sigOff = 0
	}
	base := g.sigBases[g.sigBlk] + uint64(g.sigOff)
	copy(cgArena[base:], s)
	ref := sigRef{blk: int32(g.sigBlk), off: int32(g.sigOff), n: int32(len(s))}
	g.sigOff += len(s)
	return ref
}

func (g *Graph) sigString(r sigRef) string {
	if r.blk < 0 {
		return ""
	}
	base := cgArenaBase.Load()
	if base == nil {
		return ""
	}
	return unsafe.String((*byte)(unsafe.Add(unsafe.Pointer(base),
		uintptr(g.sigBases[r.blk]+uint64(r.off)))), int(r.n))
}

func (g *Graph) halvPut(v int64) { g.halv = append(g.halv, v) }

func queryCatalogue() []*question {
	return []*question{
		{name: "n-plus-one", title: "An ActiveRecord query inside a block iterating a relation", notes: "ANSWERS the N+1 that Rails/FindEach, Rails/InverseOf and\n     Rails/WhereMissing each see one third of, and that no per-file cop\n     sees at all when the loop and the query live in different methods.\n     In Ruby the loop IS a block, so `users.each { |u| u.posts.count }`\n     has no `for` anywhere and a loop-node scan finds nothing.\nACT includes/preload/eager_load the association, or move the work into\n     one query. depth above 1 means a query nested two blocks deep, which\n     is N*M, not N.\nMISLEADS an iteration over a literal array of three symbols is not an N+1\n     and trip count is invisible here. `Rails/EagerLoading` does not\n     exist -- do not go looking for it. A query on a memoised relation\n     runs once and still appears.", run: runNamed("n-plus-one")},
		{name: "params-to-dynamic-dispatch", title: "Request parameters reaching send, constantize, eval or a backtick", notes: "ANSWERS Brakeman's Dangerous Send and Remote Code Execution shapes, but\n     across function boundaries: the controller that reads params and the\n     helper that calls send on it are usually not the same method.\n     Depth is bounded at 4 hops (see the WHERE clause below).\nACT an allowlist, always. `send(params[:action])` is remote method\n     invocation with the attacker choosing the method; constantize on\n     user input is remote class instantiation. A literal symbol argument\n     is safe and is shown so you can dismiss those rows fast.\nMISLEADS `from_params` is a textual test for the word `params` in the\n     argument, so a local named `params_hash` matches and a value laundered\n     through three assignments does not. Both directions of error are\n     present. Confirm each row by reading it.", run: runNamed("params-to-dynamic-dispatch")},
		{name: "monkey-patch-blast-radius", title: "Reopened core classes, ranked by how many call sites they could affect", notes: "ANSWERS the question a diff cannot: adding `def blank?` to String changes\n     the behaviour of every String in the process, including the ones in\n     gems you did not write. This ranks patches by how many call sites in\n     THIS tree use that method name at all.\nACT a refinement (`using`) scopes the change to one file. A helper module\n     scopes it to what includes it. Neither is a monkey patch. An operator\n     patch is the worst case -- `<=>` on Array changes sort everywhere.\nMISLEADS `could_collide` counts every symbol and call site sharing the\n     name, in this tree only. Gems are not scanned, so the true blast\n     radius is larger, and a patch that ADDS a method nobody else defines\n     is far safer than one that REDEFINES an existing core method --\n     which this cannot tell apart, because the core is not in the tree.\n     same_name_defs counts `def` only: methods generated by\n     attr_accessor, delegate or define_method exist at run time and have\n     no symbol, so the count is low by however many of those there are.\n     Only a top-level `class String` (or an explicit `class ::String`)\n     is treated as a reopening -- `class String` nested in a module is a\n     different class and is correctly excluded.", run: runNamed("monkey-patch-blast-radius")},
		{name: "string-churn-unfrozen", title: "String literals allocated per iteration, in files with no frozen magic comment", notes: "ANSWERS where the interpreter allocates a fresh String on every trip round\n     a loop. Ruby 3.4 made bare literals 'chilled' -- they warn when you\n     mutate them -- but frozen-by-default has still NOT landed in 4.0, so\n     without the magic comment each evaluation is a real allocation.\nACT add `# frozen_string_literal: true` to the top of the file. It is one\n     line, it is the single cheapest allocation win in Ruby, and\n     has_frozen tells you which files already have it.\nMISLEADS an interpolated string allocates whether or not the file is\n     frozen -- the magic comment cannot help `\"id=#{x}\"`, and interp\n     is broken out so you can see how much of the count it explains. A\n     string that is genuinely mutated afterwards MUST stay unfrozen.", run: runNamed("string-churn-unfrozen")},
		{name: "rescue-swallow", title: "Rescue bodies that discard the error, ranked by what they wrapped", notes: "ANSWERS which swallowed exceptions actually hide something. A bare\n     `rescue` catches StandardError; `rescue Exception` also catches\n     SignalException, NoMemoryError and Interrupt, so it eats Ctrl-C and\n     the OOM killer's warning shot. An empty body discards both.\nACT name the class you expect. If the method wraps a DB or HTTP call, a\n     silent rescue turns a timeout into a wrong answer that looks right,\n     which is the failure mode nobody notices for a quarter.\nMISLEADS `reraise` counts a raise anywhere in the handler body, so a\n     handler that logs and re-raises correctly still shows a rescue.\n     `rescue nil` on a parse you genuinely do not care about is fine and\n     appears here. Read the io/net/sql columns before acting.", run: runNamed("rescue-swallow")},
		{name: "class-state-under-threads", title: "Mutable class-level state reachable from something a thread runs", notes: "ANSWERS what rubocop-thread_safety's ten cops look for, raised to the call\n     graph. A `@@counter`, a class-level `@cache` or a `$global` is shared\n     by every thread in the process; Puma serves controller actions on\n     threads and every job backend runs perform on a worker, so those are\n     threaded entries whether or not the code says Thread.new.\n     Depth is bounded at 4 hops (see the WHERE clause below).\nACT make it immutable after boot, or put it behind a Mutex, or move it to\n     Thread.current / a request-scoped object. mutexes is the\n     counter-evidence column.\nMISLEADS state written once at class-definition time and only read\n     afterwards is safe and appears here -- this counts writes lexically,\n     not by when they run. Memoisation into a class ivar is the classic\n     benign-looking case that is in fact a race under load.", run: runNamed("class-state-under-threads")},
		{name: "timeout-blast-radius", title: "Timeout.timeout sites, ranked by what is running inside them", notes: "ANSWERS where the most dangerous API in the standard library is used.\n     Timeout.timeout raises in another thread at an arbitrary bytecode\n     boundary -- inside an ensure block, halfway through a Mutex handoff,\n     between a write and its flush. It is unsafe BY DESIGN, not by\n     misuse, and the damage scales with what was interrupted.\nACT use the library's own timeout: Net::HTTP#read_timeout, the driver's\n     statement_timeout, Redis's connect_timeout. Those unwind cleanly\n     because they know their own invariants.\nMISLEADS a Timeout around pure computation is comparatively harmless, and\n     this cannot see the timeout VALUE -- a 30-minute guard against a\n     hang is a different thing from a 100ms budget. db/http/io are the\n     columns that decide which one you are looking at.", run: runNamed("timeout-blast-radius")},
		{name: "mass-assignment", title: "params reaching new/create/update with no permit in sight", notes: "ANSWERS Brakeman's MassAssignment: a hash straight from the request handed\n     to a model writer sets whatever columns the attacker names, admin\n     flags included.\nACT strong parameters -- require(:model).permit(:only, :these). The\n     permit_bang column is the one with no false positives: `permit!`\n     permits EVERY parameter, so it is exactly as dangerous as no permit\n     at all while looking like it is doing something.\nMISLEADS `new` and `create` are counted as sinks whether or not the\n     argument came from params, so a row with params_reads = 0 is noise.\n     A permit in a private `xxx_params` method one frame away is not seen\n     as protecting this method -- check permit_nearby before acting.", run: runNamed("mass-assignment")},
		{name: "callback-cascade", title: "ActiveRecord callbacks that issue queries, and what they pull in behind them", notes: "ANSWERS why one `save` turns into eleven queries. A before_save that calls\n     a method that queries is invisible at the call site -- the caller\n     wrote `user.save` and got a transaction with a cascade inside it.\n     Depth is bounded at 3 hops (see the WHERE clause below), because\n     past three the answer stops being about the callback.\nACT move the work out of the callback and into an explicit service\n     object, or at minimum make it conditional. after_commit is the one\n     place where a query is defensible; before_* inside the transaction\n     is holding row locks while it waits.\nMISLEADS the edge from `before_save :normalize` to `def normalize` does\n     not exist in the tree -- a symbol is not a call -- so it is stitched\n     by name WITHIN THE FILE. A callback whose method is inherited from a\n     concern in another file has target_id NULL and is missing entirely.\n     Conditional callbacks may never run.", run: runNamed("callback-cascade")},
		{name: "mixin-method-collision", title: "Two modules included into one class, both defining the same method", notes: "ANSWERS which method actually wins. Ruby's method resolution order is\n     last-include-wins for `include`, and `prepend` jumps ahead of the\n     class's own definitions entirely -- so the answer depends on the\n     order of two lines that look unordered, and reordering them is a\n     behaviour change nobody reviews.\nACT if both are yours, rename one. If one is a gem's, prepend a module of\n     your own and call super explicitly so the chain is written down.\n     A collision where either side is `prepend` is the urgent one.\nMISLEADS only modules defined IN THIS TREE are compared, and only their\n     literal `def`s. A module that generates its methods with\n     attr_accessor, delegate or define_method contributes nothing here,\n     so a real collision between two such modules is invisible -- and\n     that is the common shape in a Concern. A collision with\n     ActiveSupport or with a gem is invisible for the same reason.\n     Matching is on the module's short name, so two different `Trackable`\n     modules in different namespaces are wrongly treated as one.", run: runNamed("mixin-method-collision")},
		{name: "sql-interpolation", title: "String interpolation inside where, order, pluck and friends", notes: "ANSWERS Brakeman's SQLInjection. `where(\"name = '#{params[:q]}'\")` is the\n     canonical Rails injection, and `order(params[:sort])` is the one\n     people forget -- ORDER BY is not parameterisable, so it needs an\n     allowlist rather than a bind.\nACT where(name: value) or where(\"name = ?\", value). For order, map the\n     user's string through a fixed hash of permitted columns.\nMISLEADS `sanitized` is a weak textual test for sanitize_sql or a bind\n     placeholder in the argument, so a genuinely safe call can show\n     sanitized = 0. Interpolation of a constant or of an integer that\n     never leaves the server is safe and appears here. from_params is the\n     column that separates the two.", run: runNamed("sql-interpolation")},
		{name: "per-iteration-cost", title: "Collection literals, Range#include? and chained array allocations in loops", notes: "ANSWERS the four rubocop-performance cops that only matter inside a loop:\n     CollectionLiteralInLoop (the array or hash is rebuilt every trip),\n     RangeInclude (include? walks the range, cover? compares two ends),\n     ChainArrayAllocation (each link in .map.select.map materialises a\n     whole new array), and TimesMap.\nACT hoist the literal to a frozen constant; swap include? for cover?;\n     collapse a chain with filter_map, each_with_object or lazy.\nMISLEADS every one of these is cheap on ten elements and only matters at\n     scale, and this cannot see collection size or trip count. Sort by\n     the score, then confirm with a benchmark before changing anything --\n     a chain rewritten as one pass is usually less readable and needs to\n     earn that.", run: runNamed("per-iteration-cost")},
		{name: "rescue-too-broad", title: "rescue Exception and bare rescue: catching what you were never meant to", notes: "ANSWERS where the error handling is wider than any error. Bare `rescue`\n     catches StandardError, which is usually intended -- but\n     `rescue Exception` also catches SignalException, Interrupt and\n     NoMemoryError, so it swallows Ctrl-C and turns an OOM into a\n     confusing retry loop.\nACT name the exceptions you can actually handle. If the goal is cleanup,\n     `ensure` runs without catching anything. If it is logging, re-raise\n     after logging -- `reraises` shows who already does.\nMISLEADS a top-level supervisor in a worker process legitimately catches\n     Exception so it can report before dying. Those are correct and rank\n     high here; check whether the body re-raises.", run: runNamed("rescue-too-broad")},
		{name: "threads-without-synchronisation", title: "Thread.new and Ractor next to mutable state, with no Mutex in sight", notes: "ANSWERS which concurrency is unguarded. MRI's GIL makes a data race\n     unlikely to corrupt an object, but it does NOT make check-then-act\n     atomic: two threads can both see nil and both build the thing.\n     On JRuby and TruffleRuby the GIL is not there at all.\nACT wrap the compound operation in a Mutex, or use a Queue, which is\n     already thread-safe. For memoisation prefer building eagerly at\n     boot over lazily under concurrency.\nMISLEADS a thread that only reads immutable data needs no mutex and is\n     listed here anyway. `class_writes` is the column that distinguishes\n     them -- shared MUTABLE state is the actual risk.", run: runNamed("threads-without-synchronisation")},
		{name: "eval-family-surface", title: "eval, instance_eval and class_eval: where the program rewrites itself", notes: "ANSWERS how much of this codebase is written at run time. `class_eval`\n     with a string builds methods no editor can jump to and no static\n     tool can see; `eval` on anything derived from input is remote code\n     execution.\nACT `define_method` with a block does everything `class_eval` with a\n     string does, keeps the lexical scope, and is visible to tooling.\n     Reserve string eval for genuine DSL compilation, and never let a\n     parameter reach it.\nMISLEADS Rails itself is built on this and the framework rows are\n     expected. What matters is eval in APPLICATION code, and eval whose\n     argument came from params -- see params-to-dynamic-dispatch.", run: runNamed("eval-family-surface")},
		{name: "shell-out-surface", title: "Backticks, system and exec, ranked by how close request data gets", notes: "ANSWERS where Ruby hands a string to a shell. Backticks and the\n     single-argument form of `system` go through /bin/sh, so a semicolon\n     anywhere in that string is a second command.\nACT use the multi-argument form -- `system(\"git\", \"log\", ref)` --\n     which execs directly and never involves a shell, so quoting stops\n     being a security question. Where a shell is genuinely required,\n     Shellwords.escape every interpolated value.\nMISLEADS this cannot see whether the argument is a literal. A backtick\n     running a fixed command is fine and ranks the same as one built by\n     interpolation -- `interpolations` is the column that separates them.", run: runNamed("shell-out-surface")},
		{name: "dead-code", title: "Nothing in this tree calls these", notes: "ANSWERS what might be deletable.\nACT grep the name as a STRING before deleting: a registry, a config file\n     or a reflective call keeps a symbol alive with no edge to show it.\nMISLEADS this is the query most likely to be wrong, and `graph-blindspots`\n     is the measure of by how much. Anything public is excluded because a\n     caller outside this tree cannot be seen at all; what is left is\n     private and unreferenced, which is a much weaker claim than dead.", run: runNamed("dead-code")},
		{name: "raw-sql-below-a-controller", title: "find_by_sql, execute or constantize reachable from a controller action", notes: "ANSWERS the ranking Brakeman cannot do. It reports every `find_by_sql`\n     and every `constantize` with a confidence level derived from the call\n     site alone. The graph adds the part that decides severity: whether a\n     controller action -- the code an HTTP request actually enters --\n     can reach it, and in how few hops.\nACT for `raw_sql`, move to a parameterised `where`. For `constantize`,\n     replace with an explicit allow-list hash; a `constantize` on request\n     data is remote code execution, not a lookup.\nMISLEADS reachability is not taint -- the SQL may be a frozen constant.\n     Depth stops at 4 hops. Rails resolves a great deal at runtime\n     (`send`, `method_missing`, concerns mixed in by string name), and\n     none of that produces an edge, so absence here proves nothing.", run: runNamed("raw-sql-below-a-controller")},
		{name: "write-per-iteration", title: "save, update or create called inside a loop, ranked by how many callers reach it", notes: "ANSWERS the write-side N+1 that RuboCop's Rails cops do not cover and\n     Bullet only catches at runtime on the read side. One `save` per\n     iteration is one INSERT, one transaction and one round trip per\n     iteration; a thousand-element collection is a thousand of each. The\n     read-side N+1 gets all the attention and this one is usually worse.\nACT use `insert_all` / `upsert_all`, or wrap the loop in a single\n     `transaction` block so the commits collapse. `enum_in_loop` next to a\n     write marks a nested iteration, which multiplies it again.\nMISLEADS a loop over two records is fine, and the bound is invisible here.\n     `save` on a non-ActiveRecord object -- a form object, a service --\n     reads identically and costs nothing. Callbacks that themselves write\n     are not counted, so the real number can be higher.", run: runNamed("write-per-iteration")},
		{name: "open-injection", title: "Kernel#open with user input (RuboCop Security/Open)", notes: "ANSWERS where Kernel#open is called, which for non-file URLs delegates to\n     open-uri, and for pipes can execute commands. open('|cmd') is RCE.\nACT use File.open for files, URI.open for URLs, never open on user input.\nMISLEADS open on a constant string is safe. The graph sees the call but\n     not the argument.", run: runNamed("open-injection")},
		{name: "send-injection", title: "send or __send__ with dynamic method name (RuboCop Security/Send)", notes: "ANSWERS where send is called with a dynamic method name, which can invoke\n     any method including private ones. If the name is user-controlled, this\n     is a metaprogramming injection.\nACT whitelist allowed method names; use public_send.\nMISLEADS send in a DSL or internal framework is a valid pattern. The graph\n     sees the call but not the argument source.", run: runNamed("send-injection")},
		{name: "constantize-injection", title: "constantize on user input (RuboCop Security/Const)", notes: "ANSWERS where constantize is called, which converts a string to a class\n     reference. If the string is user-controlled, an attacker can instantiate\n     any class in the runtime.\nACT use a whitelist hash mapping string names to class constants.\nMISLEADS constantize on an internal string is safe. The graph sees the call\n     but not the input source.", run: runNamed("constantize-injection")},
		{name: "string-concat-in-loop", title: "String += or << inside a loop (RuboCop Performance/Concat)", notes: "ANSWERS where strings are built with += or << inside a loop, which creates\n     a new string each iteration. Ruby strings are mutable but += reassigns.\nACT use << (in-place) or join an array.\nMISLEADS a loop with a small constant bound is fine. The column counts\n     sites, not allocations.", run: runNamed("string-concat-in-loop")},
		{name: "weak-hash", title: "MD5 or SHA1 used for hashing (RuboCop Security/WeakHash)", notes: "ANSWERS where a weak hash algorithm is used for security purposes.\nACT use SHA256 or stronger; for passwords use bcrypt/scrypt/argon2.\nMISLEADS MD5 for a non-security checksum is fine. The graph sees the call\n     but not the purpose.", run: runNamed("weak-hash")},
		{name: "html-safe-xss", title: "html_safe on user-controlled string (RuboCop Rails/OutputSafety)", notes: "ANSWERS where html_safe is called, which marks a string as safe for HTML\n     output, bypassing Rails' XSS protection. If the string contains user\n     input, this is an XSS vulnerability.\nACT use sanitize or content_tag; never html_safe on user input.\nMISLEADS html_safe on a constant or a sanitized string is correct. The\n     graph sees the call but not the string's source.", run: runNamed("html-safe-xss")},
		{name: "sql-injection-ar", title: "ActiveRecord where with string interpolation (RuboCop Rails/Skylight)", notes: "ANSWERS where ActiveRecord queries use string interpolation instead of\n     parameterized queries: where(\"x = #{y}\") instead of where(x: y).\nACT use the hash form: where(x: y) or parameterized: where('x = ?', y).\nMISLEADS interpolation of a constant is safe. n_sql_interp counts sites.\n     n_sql_sanitized says sanitize was called.", run: runNamed("sql-injection-ar")},
		{name: "eval-injection", title: "eval with user input (RuboCop Security/Eval)", notes: "ANSWERS where eval is called, which executes arbitrary Ruby. If the input\n     is user-controlled, this is RCE.\nACT use a parser, a DSL, or a whitelist; never eval user input.\nMISLEADS eval in a test or irb is correct. The graph sees the call but not\n     the input source.", run: runNamed("eval-injection")},
		{name: "mass-assignment-weak-params", title: "Mass assignment without strong params (RuboCop Rails/MassAssignment)", notes: "ANSWERS where params are passed directly to a model constructor or update,\n     allowing a user to set any attribute.\nACT use permit! or require(...).permit(...).\nMISLEADS n_permit > 0 means strong params ARE used; the risk is where\n     n_params_read > 0 AND n_permit = 0.", run: runNamed("mass-assignment-weak-params")},
		{name: "import-cycle", title: "Circular require dependencies (madge/circular)", notes: "ANSWERS which files form a require cycle.\nACT break the cycle by extracting shared code.\nMISLEADS cycles through test files are usually fine. Depth capped at 8.", run: runNamed("import-cycle")},
		{name: "thread-coupling", title: "Thread.new or Ractor.new coupling (RuboCop ThreadSafety)", notes: "ANSWERS where threads or ractors are spawned, which introduces concurrency.\n     Without proper synchronization, shared state can race.\nACT ensure shared state is synchronized (Mutex) or use message passing.\nMISLEADS a thread in a test or a background job framework is correct.\n     The graph sees the spawn but not the synchronization.", run: runNamed("thread-coupling")},
		{name: "monkey-patch-surface", title: "Class reopening or module inclusion that modifies existing classes (RuboCop)", notes: "ANSWERS where a class is reopened or a module is included/prepended into an\n     existing class, changing its behavior globally.\nACT prefer composition over monkey-patching; if patching, scope it narrowly.\nMISLEADS Rails and most Ruby frameworks monkey-patch extensively; the\n     pattern is idiomatic but risky for non-framework code.", run: runNamed("monkey-patch-surface")},
		{name: "ancestor-chain-depth", title: "Superclass depth per class: the monkey-patch resistance meter", notes: "ANSWERS how many superclass hops sit between each class and the root of\n     its inheritance tree. Deep ancestry is where a superclass change\n     ripples widest and where an include/extend mixin has the most\n     intervening method-lookup layers to cut through.\nACT prefer composition below ~4 levels; at minimum, the deep rows are\n     the ones to watch when an ancestor changes.\nMISLEADS walks the superclass TEXT column by exact name, so a\n     superclass spelled with a different constant path (`Foo::Bar` vs\n     `Bar` where Bar is a wrapper) breaks the chain at that hop; depth\n     is capped at 8 (the recursion bound) and includes/extend depth is\n     NOT counted -- only `class X < Y` ancestry, which matches the\n     compiler-enforced single-inheritance chain.", run: runNamed("ancestor-chain-depth")},
		{name: "yield-hubs", title: "Methods that hand control to a block via yield", notes: "ANSWERS which methods are callback processing hubs: every `yield`\n     passes control to whatever block the caller supplied, so a method\n     dense in yields is the funnel through which behavior is injected.\nACT a method yielding in a loop should be documented as a hook; each\n     yield is a contract point with the caller's block.\nMISLEADS counts yield KEYWORDS, not distinct block receivers; `yield`\n     inside a nested lambda in the same method still counts to the\n     method, and a method that yields through a helper (block.call in\n     another method) is hidden. block-vs-proc-cost covers the passing\n     side.", run: runNamed("yield-hubs")},
		{name: "attr-coupling", title: "Classes exposing state through attr_accessor/reader/writer", notes: "ANSWERS which classes publish read/write access to their instance\n     state via attribute macros -- the coupling surface that makes\n     internal fields public API. High writer counts mean mutation from\n     outside; high reader-only counts mean the class is more a data\n     holder than an object.\nACT every attr_accessor is an invitation to mutate from outside: prefer\n     attr_reader plus a method that changes state with intent.\nMISLEADS counts the macro DECLARATIONS (one per attribute), not the\n     generated method call sites; `attr` and `class_attribute` are\n     grouped with reader; a `mattr_`/`cattr_` variant is counted as an\n     accessor on the class rather than the instance.", run: runNamed("attr-coupling")},
		{name: "heavy-mixins", title: "Modules and concerns included by the most classes", notes: "ANSWERS which mixin surfaces spread across the widest class set -- the\n     gems and core modules every host pulls in, and the ones whose\n     method-name collisions hurt the most hosts at once.\nACT a mixin included by many classes is a coupling axis: changing its\n     methods changes every host. Keep it stable or split it.\nMISLEADS counts distinct HOSTS per mixin text, so the same mixin\n     spelled with and without a namespace prefix splits into two rows;\n     `include`/`extend`/`prepend` all count equally although the\n     method-lookup position differs.", run: runNamed("heavy-mixins")},
		{name: "super-overrides", title: "Methods that call super: the override surface", notes: "ANSWERS every method whose body reaches back to its ancestor via\n     `super` -- the precise list of behavioral overrides in this tree.\n     Each row is a place where the subclass extends, wraps or replaces\n     the superclass contract.\nACT an override with no super-call is a complete replacement; one with\n     super is a hook. Code review should treat the two differently.\nMISLEADS counts `super` keywords per method; `super` with explicit\n     arguments and bare `super` both count once, and a super written as\n     a delegated message (super.send(:x)) is not seen.", run: runNamed("super-overrides")},
		{name: "unused-private", title: "Private methods nothing in this class calls", notes: "ANSWERS private/protected methods with no resolved caller anywhere --\n     the internal helpers that nobody invokes. In Ruby, where method\n     calls through `send` and dynamic dispatch are idiomatic, this is a\n     candidate list rather than a proof of death.\nACT grep the method name as a string before deleting: a symbol call,\n     a DSL callback, or a `send(:method)` keeps it alive invisibly.\nMISLEADS visibility comes from the method's declared visibility; a\n     method called through send/instance_exec/define_method looks\n     uncalled here, and a private method called ON ITSELF inside the\n     class counts only if resolution followed the receiver.", run: runNamed("unused-private")},
		{name: "nested-iterators", title: "Methods iterating inside an iteration (reek NestedIterators)", notes: "ANSWERS methods with blocks at iteration depth >= 2: the accidental\n     O(n*m). Each nested level multiplies the work by the outer size.\nACT flatten, pluck, or push the inner query into SQL.\nMISLEADS matrix pipelines and group_by chains are legitimately nested;\n     depth counts blocks, not data size -- rank by queries_inside\n     first, because an inner AR query is the expensive half.", run: runNamed("nested-iterators")},
		{name: "feature-envy", title: "Methods whose calls mostly leave the object (reek FeatureEnvy)", notes: "ANSWERS methods whose foreign calls dominate self calls: the method\n     wants to move to the class it keeps calling. Each row is a\n     placement smell -- the data it works on lives elsewhere.\nACT move it to the envied class, or extract a value object.\nMISLEADS DSL receivers, delegation one-liners and AR association\n     proxies all read as envy; is_self is receiver-text based, so a\n     call through a local (`items.map`) counts as foreign even when\n     `items` is the method's own parameter -- which is the point for\n     params-heavy helpers but noise for pure functions.", run: runNamed("feature-envy")},
		{name: "debugger-surface", title: "binding.pry / debugger / byebug left in application code", notes: "ANSWERS the debugger entry points in non-test code: a binding.pry\n     shipped to production is an interactive session waiting for a\n     stdin, and byebug breaks under load in the same way.\nACT remove before shipping; gate the debugger behind an env flag if it\n     must survive in the tree.\nMISLEADS name-based on unresolved calls, so a wrapper around\n     binding.pry hides it; a debugger behind a development-only\n     constant is still reported (the row is the review list); test\n     files are excluded by is_test.", run: runNamed("debugger-surface")},
		{name: "unscoped-find-params", title: "find / find_by / where with params and no visible scope (brakeman)", notes: "ANSWERS AR lookups fed straight from params: unscoped find. Without an\n     explicit default scope or tenant filter, params[:id] from one\n     tenant can read another tenant's row.\nACT scope the query to the current account/tenant before the find, or\n     whitelist the param.\nMISLEADS from_params is an ARGUMENT-SHAPE flag: params[:id] inside a\n     method that is itself called with a scoped relation is invisible\n     (the flag looks at the literal argument, not data flow); a\n     controller that scopes first then finds is still reported if the\n     find call's own argument is params-derived.", run: runNamed("unscoped-find-params")},
		{name: "open-redirect-surface", title: "redirect_to calls in methods that read params/cookies (OWASP G26)", notes: "ANSWERS methods that call redirect_to AND read request input (params, cookies, request headers) -- the shape of an unvalidated redirect: redirect_to params[:next].\nACT validate the target against an allowlist; never forward a\n     user-supplied URL.\nMISLEADS same-function co-occurrence is NOT data flow -- the input value\n     may never reach the redirect, and a constant redirect beside an\n     unrelated params read reads as a violation. The argument text is not\n     captured, so a fixed target cannot be told from an open one. The\n     source capture is shape-based: a LOCAL variable named params or\n     cookies reads as request input (Rails' params cannot be shadowed,     but plain Ruby can).", run: runNamed("open-redirect-surface")},
		{name: "ssrf-fetch-surface", title: "HTTP client calls in methods that read params/cookies (OWASP G27)", notes: "ANSWERS methods that fetch a URL (Net::HTTP, HTTParty, Faraday,\n     RestClient, open-uri) AND read request input -- the shape of\n     server-side request forgery: Net::HTTP.get(URI(params[:url])).\nACT validate the URL scheme and host against an allowlist; never fetch a\n     user-supplied URL.\nMISLEADS same-function co-occurrence is NOT data flow -- the input value\n     may never reach the fetch, and a constant URL beside an unrelated\n     params read reads as a violation. The capture is the dotted\n     receiver: a client assigned to a variable (client = Net::HTTP.new)\n     and used via client.get is invisible; a wrapper around the client\n     is too.", run: runNamed("ssrf-fetch-surface")},
		{name: "hardcoded-secret-candidates", title: "Credential-shaped string literals (OWASP G07)", notes: "ANSWERS string literals at least 12 chars long whose text names a\n     credential (password, token, api_key, secret, bearer, jwt, ...) --\n     the literal that a committed secret looks like.\nACT rotate and move to a secret manager; never commit the literal.\nMISLEADS a format string or test fixture containing the WORD token/pass\n     reads as a candidate (the filter is the literal's own text, not its\n     use); values over 200 chars are truncated at capture; a secret\n     built from parts or read from an env var is invisible here.\n     This is a candidate list, not a verdict.", run: runNamed("hardcoded-secret-candidates")},
		{name: "xxe-parser-surface", title: "XML parser construction sites (OWASP G13)", notes: "ANSWERS methods that touch Nokogiri::XML or REXML -- the surface where\n     entity expansion is decided.\nACT use Nokogiri::XML::ParseOptions::NOENT off and reject DTDs; prefer\n     safe parsing configurations.\nMISLEADS the parser CONFIG is not modeled: a parser with entities\n     disabled ranks the same as one without. The capture is the dotted\n     receiver, so Nokogiri::XML::Document.parse assigned to a local and\n     called bare is invisible.", run: runNamed("xxe-parser-surface")},
		{name: "path-traversal-surface", title: "File.open/read with a non-literal path in input-reading methods (G12)", notes: "ANSWERS methods that call File.open/read with a variable path AND read\n     request input -- the shape of path traversal: File.read(params[:f]).\nACT validate the resolved path stays under a configured root; use\n     File.expand_path and a prefix check.\nMISLEADS same-function co-occurrence is NOT data flow -- the input value\n     may never reach the open, and a constant-open beside an unrelated\n     params read reads as a violation. The path is not analyzed: a\n     variable path is assumed suspicious, a literal is not; IO.read,\n     Pathname and rails' send_file shapes are invisible to the\n     File. capture.", run: runNamed("path-traversal-surface")},
		{name: "zip-slip-surface", title: "rubyzip access sites (OWASP G29)", notes: "ANSWERS methods that touch Zip::File and friends -- the surface where an\n     entry name becomes a filesystem path.\nACT validate every entry name against a containment check before\n     extraction; reject ../ and absolute paths.\nMISLEADS the containment check is not modeled: a method that checks each\n     name before extraction ranks the same as one that does not. The\n     capture is the dotted Zip:: receiver; a bare alias of the library\n     is invisible.", run: runNamed("zip-slip-surface")},
		{name: "log-injection-surface", title: "Logger calls in methods that read params/cookies (OWASP G14)", notes: "ANSWERS methods that call a logger level method (Rails.logger.info,\n     logger.error, ...) AND read request input -- the shape of log\n     forging: Rails.logger.info(params[:msg]).\nACT sanitize newlines and control characters in log messages; never log\n     raw request input.\nMISLEADS same-function co-occurrence is NOT data flow -- the input value\n     may never reach the log call, and a constant message beside an\n     unrelated params read reads as a violation. The capture needs the\n     word logger in the dotted call, so a differently-named logger is\n     invisible.", run: runNamed("log-injection-surface")},
		{name: "unauthenticated-input-surface", title: "Request input read with no auth call in the method (OWASP G01)", notes: "ANSWERS methods that read request input (params, cookies, request) and\n     contain NO auth-family call (authenticate_user!, current_user,\n     signed_in?, session) -- the surface where a controller action may\n     be missing its authorization check.\nACT add the before_action auth callback; verify the action is in the\n     protected route group.\nMISLEADS auth usually lives in a before_action or ApplicationController\n     -- this query sees the action body only, so a fully-protected\n     controller still ranks every action as open. A login or public\n     action legitimately has no auth. The markers are name-based\n     substrings, so a helper wrapping the auth call is invisible and\n     counts as open.", run: runNamed("unauthenticated-input-surface")},
		{name: "find-each-missed", title: "Model.all.each with a query inside the block", notes: "ANSWERS the accidental N+1 in its most mechanical form: iterate\n     EVERY row of a model, and run a query inside the loop.\nACT switch to find_each / find_in_batches; or preload and use the\n     association, which is one query.\nMISLEADS the block receiver is text (`User.all.each`); a variable\n     holding the collection reads as 'other' and is missed; n_queries\n     counts AR calls inside the block body, so a loop that does no\n     querying is excluded by the HAVING.", run: runNamed("find-each-missed")},
		{name: "unsafe-deserialization", title: "Marshal.load / YAML.load / Psych.load sites (brakeman UnsafeDeserialization)", notes: "ANSWERS the deserialization entry points that can turn attacker bytes\n     into object construction: Marshal.load on any untrusted input is\n     remote code execution, and YAML.load is the same in legacy Psych.\nACT feed untrusted bytes only to the safe forms: YAML.safe_load,\n     Psych.safe_load, Marshal never; JSON.load is listed but JSON\n     cannot construct objects.\nMISLEADS the capture is the deserialize hazard family, which includes\n     JSON.load and Oj.load -- rows whose payload cannot execute; the\n     data origin is NOT tracked, so a Marshal.load on a server-side\n     constant ranks the same as one on a cookie.", run: runNamed("unsafe-deserialization")},
		{name: "save-without-bang", title: "save (no bang) with the boolean result discarded (Rails/SaveBang)", notes: "ANSWERS save calls whose false-on-failure result is thrown away: the\n     failure is invisible to the caller, and in a callback the save can\n     silently not happen. rubocop-rails wants save! for this shape.\nACT use save! in callbacks and let the exception propagate, or handle\n     the false branch explicitly.\nMISLEADS the discard is positional (expression statement): a save whose\n     result feeds an if (`if record.save`) is correctly absent; save on\n     a bare receiver that is a method call (a relation) is excluded by\n     construction; validation-false is the common failure and is not\n     distinguished from an IO failure.", run: runNamed("save-without-bang")},
		{name: "legacy-enumerable-idioms", title: "select.first / map.flatten / reverse.each chains (fasterer)", notes: "ANSWERS the three chain pairs with a dedicated idiom: select{}.first is\n     find{}, map{}.flatten is flat_map{}, reverse.each is\n     reverse_each -- each saves an intermediate array or a pass.\nACT swap to the dedicated form; the change is mechanical.\nMISLEADS text-matched on the chain receiver: `xs.select(&:x).first`\n     matches, `ys.select(...)` with the call split across a local does\n     not; a select that is genuinely cheaper than find (all matches\n     needed elsewhere) still reads as a violation.", run: runNamed("legacy-enumerable-idioms")},
		{name: "param-clumps", title: "Three or more methods sharing the same parameter set (reek DataClump)", notes: "ANSWERS the parameter tuples repeated across methods: a DataClump is\n     the raw material of a missing value object. Each row names the\n     shared tuple and how many methods carry it.\nACT extract a value object (or a positional struct) and pass it once.\nMISLEADS the tuple is grouped as WRITTEN (parameter order matters):\n     two methods with the same params in different orders read as\n     different clumps; common framework params (request, response)\n     appear in every method of a class and dominate the list; a\n     one-off two-method pair is excluded by the HAVING.", run: runNamed("param-clumps")},
		{name: "typing-coverage", title: "Methods in sig-using classes that have no sig (sorbet adoption gaps)", notes: "ANSWERS public methods missing a sig{} in files where sorbet is in use:\n     the untyped gap. A class that typed one method proves the author\n     is adopting sorbet -- the untyped ones are the remainder.\nACT add sig{} to the method; if it is deliberately untyped (dynamic\n     dispatch), say so with a T.untyped comment.\nMISLEADS has_sig is the prev-sibling text: `sig` on the line before the\n     def; a sig separated by a comment or wrapped in a helper reads as\n     absent; files that never use sorbet are excluded by the EXISTS,\n     so the rows are the ADOPTION gaps, not a raw typing census.", run: runNamed("typing-coverage")},
		{name: "transaction-exit-statement", title: "return/break/throw inside a transaction or with_lock block (Rails/TransactionExitStatement)", notes: "ANSWERS where a transaction ends by falling off the method instead of by\n     committing or raising. On Rails 7.1 a `return` inside the block can\n     leave the transaction OPEN (active_record.commit_transaction_on_non_local_return);\n     on other versions it silently changes what was meant to be atomic.\n     `raise` rolls back and `next` commits -- neither is counted here.\nACT replace `return` with `next` (commit) or `raise` (rollback); a\n     `break` aimed at a loop nested in the block should be restructured,\n     not patched.\nMISLEADS a return/break/throw is attributed to EVERY enclosing block, so\n     a `return` inside `xs.each` inside `transaction` marks both rows --\n     the transaction one is the dangerous one. Custom transaction wrappers\n     configured in the cop (TransactionMethods) are invisible; only the\n     built-in names transaction and with_lock are matched.", run: runNamed("transaction-exit-statement")},
		{name: "validation-skip-reachable", title: "update_attribute / increment! / toggle! reachable from a params reader (Rails/SkipsModelValidations)", notes: "ANSWERS writes that bypass validations AND callbacks, reached through the\n     call graph from a method that reads request input -- the shape of\n     `update_attribute(:admin, true)` executed on attacker-controlled\n     rows. The per-call cop sees the call; only the graph sees that the\n     value path starts at params.\nACT replace with update!/update_columns-with-permitted-list, or validate\n     at the boundary. increment_counter on an unscoped id is the classic\n     vote/counter stuffing primitive.\nMISLEADS the sink match is on the unresolved call NAME with the receiver\n     stripped, so `foo.update_attribute` in a gem-wrapping module matches\n     too, and a local wrapper that renames the call hides it. Reachability\n     is not taint: the params read may never feed the write. Depth is\n     bounded at 4 hops.", run: runNamed("validation-skip-reachable")},
		{name: "action-filter-unresolved", title: "before_action etc. naming a method this tree cannot find (Rails/LexicallyScopedActionFilter)", notes: "ANSWERS action filters whose target method has NO definition in the same\n     file -- the filter silently does nothing, or resolves to whatever a\n     mixed-in concern happens to provide. The rubocop-rails cop checks\n     the lexically enclosing class; the graph checks the whole file, so\n     what survives here is strictly the unresolved remainder.\nACT read the concern chain: either the method moved and the filter is\n     dead, or it lives in a concern and deserves a comment naming it.\nMISLEADS a filter whose method is defined in a concern in ANOTHER file is\n     normal Rails and is reported here anyway -- the stitching is per\n     file, by name, and cannot see inheritance. String-named targets and\n     block filters are excluded.", run: runNamed("action-filter-unresolved")},
		{name: "abstract-method-unimplemented", title: "A module's abstract (NotImplementedError) method missing from an including host", notes: "ANSWERS interface drift: a module declares a method abstract -- body is a\n     bare `raise NotImplementedError` -- and a class includes the module\n     without defining it. The first caller hits the raise at run time,\n     which a test double or a sibling subclass silently papered over.\nACT implement the method in the host, or document the host as abstract\n    too; sorbet's `abstract!` is invisible to this parser and needs the\n    same check by hand.\nMISLEADS abstract is detected as a body that raises NotImplementedError,\n    so hand-rolled 'subclass must implement' raises that NAME a different\n    error are missed. The check is lexical: a host whose PARENT class\n    implements the method is still reported, and module short-name\n    matching can pair a host with a same-named module it does not\n    actually include.", run: runNamed("abstract-method-unimplemented")},
		{name: "method-missing-protocol", title: "method_missing without super, and what does not implement respond_to_missing?", notes: "ANSWERS the two halves of the method_missing contract, ranked together.\n     Without a `super` at the end, a NoMethodError that method_missing\n     cannot handle dies inside it and the REAL error (and its backtrace\n     origin) is lost. Without respond_to_missing?, everything that asks\n     respond_to? -- serializers, mock assertions, URI builders -- is lied\n     to about what the object answers.\nACT add `super` as the last line of method_missing; add\n    respond_to_missing? mirroring the names method_missing accepts.\nMISLEADS counts are per method_missing DEFINITION: a class hierarchy that\n    defines super once in the root still shows 0 for the subclass that\n    redefines it. respond_to_missing? is looked for among SIBLINGS of the\n    def only, so one inherited from an ancestor reads as missing.", run: runNamed("method-missing-protocol")},
		{name: "duplicate-method-in-class", title: "The same method defined twice in one class -- the second silently wins (Lint/DuplicateMethods)", notes: "ANSWERS redefinitions that overwrite without warning: a class reopened\n     further down the same file, a merge that kept both halves, a\n     generated block that collides with a hand-written def. Ruby raises\n     nothing; the FIRST definition is dead the moment the second loads,\n     and any tests aimed at it pass while production runs the other.\nACT delete or rename one definition; if the reopen is deliberate, move\n     the method to the winning file so there is only one.\nMISLEADS counts literal defs in the same class SUBTREE only: duplicates\n    across two files that reopen the class are invisible here (see\n    class-reopened-across-files for that), and methods generated by\n    attr_accessor or define_method collide with none of this because\n    they produce no symbol.", run: runNamed("duplicate-method-in-class")},
		{name: "class-reopened-across-files", title: "One class declared in several files: the split nobody reviews", notes: "ANSWERS classes and modules whose declarations are spread over more than\n     one file. Ruby makes reopening free, so a class can grow methods in\n     four places; every one of those places is a merge conflict, a load-\n     order dependency and a place a constant can be defined twice. The\n     per-file cop cannot see the spread; the import graph cannot see it\n     either, because reopening produces no require.\nACT if the split is a concern, make it a real module; if it is history,\n     collapse it into one file. Core-class reopenings here should be\n     cross-checked against monkey-patch-blast-radius.\nMISLEADS same short names in different namespaces are grouped together\n    (matching is on the declared name text, not the resolved constant),\n    and test-file declarations are excluded from the count, so a class\n    reopened only in its specs does not appear. Rails engines and\n    decorators do this deliberately and legitimately.", run: runNamed("class-reopened-across-files")},
		{name: "inherit-exception-base", title: "Exception subclass inheriting Exception/Object -- invisible to bare rescue (Lint/InheritException)", notes: "ANSWERS custom error classes whose parentage puts them OUTSIDE\n     StandardError: `class oops < Exception` is the cop's target, and\n     `< Object` for a raised thing means every bare `rescue` in the tree\n     -- which catches StandardError -- will let it fly past and take the\n     process down.\nACT inherit StandardError unless you have a specific reason not to; keep\n     Exception for the framework's own fatal classes.\nMISLEADS the row is the DECLARATION; whether the class is ever raised is\n    not checked (a never-raised subclass is harmless). The\n    same-file-rescue count is a proximity hint, not a call graph -- a\n    rescuer in another file is invisible, and `< Object` rows include\n    plain classes that are never raised at all.", run: runNamed("inherit-exception-base")},
		{name: "n-plus-one-reachable", title: "A query-in-a-loop method reachable from a controller action (CodeQL: Database query in a loop)", notes: "ANSWERS the cross-file N+1: the loop-and-query lives in a service or\n     model method, the controller action just calls it, and no per-file\n     cop can see the two halves together. Rows are (action, loop-query\n     method) pairs with the hop count.\nACT preload at the boundary (the action usually owns the initial\n     relation) or batch with find_each inside the callee.\nMISLEADS reachability is not execution: the action may call the loop on\n     a two-element collection, and the loop trip count is invisible.\n     Depth is bounded at 4 hops, and only PUBLIC controller methods are\n    roots, so a private helper that iterates under its own action is\n    counted from whichever action reaches it, not from its text.", run: runNamed("n-plus-one-reachable")},
		{name: "enqueue-in-loop", title: "Job enqueues inside an iteration -- the bulk-enqueue stampede (Sidekiq anti-pattern)", notes: "ANSWERS loops that enqueue one background job per element: ten thousand\n     rows means ten thousand jobs, ten thousand queue round trips and a\n     Sidekiq dashboard nobody can read. The enqueue and the loop usually\n     live in different files.\nACT batch the payload: one job that takes the id list (slice with\n     in_batches), or perform_all with a bulk-push adapter.\nMISLEADS a loop over three elements is fine and the bound is invisible\n    here; `deliver_later` inside an each over a tenant list is sometimes\n    exactly what the product wants. The in-loop test counts ENCLOSING\n    iteration blocks, so an enqueue under a bare `while` counts as an\n    enqueue but not as in-loop. The family match is on the NAME, not\n    the receiver, so a local object's own `enqueue` method counts.", run: runNamed("enqueue-in-loop")},
		{name: "mutex-held-across-io", title: "A Mutex taken in a method that also does network/disk/DB work", notes: "ANSWERS critical sections that span I/O: every other thread that wants\n     that Mutex waits for a socket, a disk seek or a DB round trip. Under\n     load this is the difference between p99 and a deadlock (the far end\n     calls back into us on another thread that wants the same lock).\nACT shrink the section: lock, copy the state, unlock, THEN do the I/O;\n     or use a Monitor + condition variable so the wait happens outside\n     the lock.\nMISLEADS same-method co-occurrence, not ordering: the I/O may run before\n    the lock is taken, or the Mutex may guard exactly that I/O on\n    purpose (a per-key lock around a cache fill is the defensible\n    shape). The n_mutex capture keys on Mutex.new/Monitor.new, so locks\n    from Concurrent::Semaphore or the GVL are invisible.", run: runNamed("mutex-held-across-io")},
		{name: "thread-new-without-join", title: "Thread.new with no join/value in the spawning method -- fire-and-forget failure modes", notes: "ANSWERS where threads are spawned and never waited on IN THE SAME METHOD.\n     An unjoined thread swallows its own exception (abort_on_exception is\n     off by default), outlives the request that started it, and keeps\n     every captured local alive. The spawn and the join are usually\n     separated on purpose -- which is exactly the bug this names.\nACT hold the thread and join it, or route the work through a job queue;\n    if it is a daemon by design, install a top-level exception handler\n    and say so in a comment.\nMISLEADS the counter-evidence is an ARGUMENTLESS join/value call in the\n    same method -- that shape is usually Thread#join, but an Array#join\n    with the default separator also counts, and a thread joined in a\n    DIFFERENT method still reads as fire-and-forget. Thread pools\n    (Concurrent, Sidekiq) never call join and are out of scope by\n    construction.", run: runNamed("thread-new-without-join")},
		{name: "thread-current-reachable", title: "Thread.current usage reachable from something that runs on a request/worker thread", notes: "ANSWERS where request-scoped state rides on Thread.current. Under Puma\n    the thread is REUSED by the next request: anything not reset at the\n    end leaks the previous request's user into this one. The classic\n    shape is Current attributes, request stores -- and hand-rolled\n    Thread.current[...] in a helper three hops from the action.\nACT set it in a around_action with an ensure that resets it; prefer an\n    explicit argument over thread storage in new code.\nMISLEADS Thread.current[:x] READS and WRITES are one counter, so the\n    consumer of a correctly-scoped store ranks like the leaker. Depth is\n    bounded at 4 hops and the roots are threaded entries (spawners,\n    controllers, jobs) -- a rake task using Thread.current safely does\n    not appear. Fibres change the scoping rules and are not modeled.", run: runNamed("thread-current-reachable")},
		{name: "constant-mutation", title: "Methods that mutate a constant receiver (CONST << x) -- shared mutable state", notes: "ANSWERS writes into process-global constants: `CACHE << item`,\n     `REGISTRY[key] = v` (via store), `CONFIG.merge!`. A constant is\n     only frozen by its own .freeze call, and even then the OBJECT it\n     names is shared by every thread and every request. Ranked by how\n    many callers reach the mutator.\nACT freeze the structure and replace mutation with a rebuild-and-rebind,\n    or move the state behind a Mutex / concurrent map.\nMISLEADS the receiver must be a CONSTANT node, so mutation through a\n    variable that aliases the constant is invisible, and `store`/\n    `update` on an immutable-looking constant is assumed mutating\n    without reading the argument. The constant's definition and its\n    freeze state are not checked -- this is the write side only.", run: runNamed("constant-mutation")},
		{name: "symbol-dos-surface", title: "to_sym / to_proc in a method that reads request input (brakeman SymbolDoS)", notes: "ANSWERS where request input can be interned: `params[:x].to_sym` puts an\n    unbounded number of permanent entries into the process symbol table\n    -- memory the GC cannot take back, on every Ruby before 3.x the\n    object-space DoS brakeman flags as SymbolDoS.\nACT keep request data a String; compare against a fixed set of symbols\n    (an allowlist hash), or use String#in? against frozen literals.\nMISLEADS same-method co-occurrence is not data flow: the to_sym may be\n    on a frozen literal beside an unrelated params read. The capture is\n    the METHOD NAME to_sym/to_proc -- interning that happens inside a\n    gem or via `String#capitalize!`-style C paths is invisible.", run: runNamed("symbol-dos-surface")},
		{name: "regex-dos-surface", title: "A regex built at run time (Regexp.new / interpolated literal) next to request input (brakeman RegexDoS)", notes: "ANSWERS the two ReDoS entry shapes: a regex COMPILED from a variable\n    (`Regexp.new(params[:re])`) and an interpolated literal\n    (/#{prefix}\\d+/) rebuilt per call. An attacker-chosen pattern is\n    worse than a slow one -- nested quantifiers on attacker TEXT is the\n    catastrophic-backtracking pair; attacker-chosen PATTERN is the\n    compiler as an oracle.\nACT anchor user text into \\A...\\z with Regexp.escape, never interpolate\n    raw input, and reuse a frozen constant for fixed patterns.\nMISLEADS same-method co-occurrence, not taint: the compiled regex may be\n    built from a frozen config constant while params feeds something\n    else on the same line range. The pattern TEXT is not analyzed, so a\n    harmless `#{col}` interpolation ranks like `(a+)+$`.", run: runNamed("regex-dos-surface")},
		{name: "html-safe-frontier", title: "html_safe / raw reachable, through the call graph, from a method that reads request input", notes: "ANSWERS the cross-function XSS frontier. html-safe-xss catches the mark\n    and the taint in one method; raw-sql-below-a-controller roots at\n    controllers. This roots at whatever READS params/cookies and walks\n    out to the method that marks a string safe -- the laundered shape:\n    the helper three calls deep that html_safe's a value built upstream.\nACT delete the html_safe and escape at the boundary; every one of these\n    rows is a place an attacker-supplied substring becomes markup.\nMISLEADS reachability is not taint: the html_safe may be applied to a\n    frozen template fragment and the params read may feed an unrelated\n    branch. Depth is bounded at 4 hops and dynamic dispatch (send,\n    method_missing) produces no edge, so the frontier is a floor.", run: runNamed("html-safe-frontier")},
		{name: "file-open-frontier", title: "File.open/read with a variable path, reachable from a params reader (brakeman FileAccess)", notes: "ANSWERS the path-traversal frontier across functions: same-function\n    File.read(params[:f]) is caught by path-traversal-surface; this one\n    catches the downloader that takes an id, calls into a storage\n    module, and THAT module opens a path built from its argument.\nACT resolve with File.expand_path and check the result still starts\n    with the configured root -- inside the OPENING method, not the\n    caller.\nMISLEADS reachability is not taint and the argument is not traced: the\n    variable path may be assembled from server-side config three hops\n    below the params read. send_file, IO.read and Pathname are not in\n    the File. capture, so those sinks are missed entirely.", run: runNamed("file-open-frontier")},
		{name: "sql-interp-reachable", title: "Interpolated-SQL query code reachable from a params reader (brakeman SQLInjection, graph frontier)", notes: "ANSWERS the injection frontier: the string-interpolated where/heredoc\n    lives in a model method, the params read lives in the controller,\n    and neither a per-site cop nor sql-interpolation's same-method view\n    can see the pair. This walks the call graph from readers of request\n    input to methods that build SQL with interpolation.\nACT move the value into a bind (`where(name: ?)`) or sanitize_sql --\n    in the SINK method, so every caller is safe at once.\nMISLEADS reachability is not taint: the interpolated term may be a\n    table name from a frozen constant. `is_sanitized` is a textual test\n    and can be 0 for genuinely bound queries. Depth is bounded at 4\n    hops; send/method_missing paths produce no edges, so this is a\n    floor, not a proof of safety elsewhere.", run: runNamed("sql-interp-reachable")},
		{name: "zoneless-time-surface", title: "Time.now / DateTime.now where a zoned time was meant (Rails/TimeZone)", notes: "ANSWERS wall-clock reads -- Time.now, DateTime.now -- which ignore\n    Time.zone. In an app that serves more than one timezone these are\n    the day-boundary bugs: the invoice dated yesterday, the coupon that\n    expires at the wrong midnight, the range query off by the server's\n    UTC offset.\nACT Time.current / Time.zone.now for wall-clock use; Date.current for\n    calendar days. Keep Time.now only where UTC-now is exactly what is\n    meant (monotonic budgets, token timestamps).\nMISLEADS Process.clock_gettime and Time.at are not counted, and a file\n    that genuinely works in UTC (jobs, batch sweeps) ranks the same as\n    a user-facing view. `now` on a variable receiver is invisible --\n    only the literal Time./DateTime. receiver shapes match.", run: runNamed("zoneless-time-surface")},
		{name: "lock-in-loop", title: "transaction / with_lock / synchronize taken inside an iteration", notes: "ANSWERS per-iteration locks and transactions: one BEGIN/COMMIT per row\n    (with_lock), one global Mutex hand-off per element (synchronize).\n    The loop multiplies the most expensive synchronization primitive in\n    the program by the trip count, and the trip count is never visible\n    in the file that contains the block.\nACT move the transaction/lock OUTSIDE the loop (one commit), or batch\n    the work so the loop disappears (insert_all).\nMISLEADS a lock taken in a loop over THREE items is correct and cheap;\n    the bound is invisible. `lock` as an AR relation method and Mutex\n    `synchronize` are name-matched, so a plain-Ruby object of yours with\n    a method of the same name reads as a lock. depth counts ENCLOSING\n    iteration blocks (a lock at depth 0 is outside every loop and is\n    excluded), not the loop trip count.", run: runNamed("lock-in-loop")},
		{name: "include-shadows-own-method", title: "An included module defines a method the host also defines -- the module silently wins", notes: "ANSWERS MRO accidents: `include` puts the module ABOVE the class in the\n    lookup chain, so when both define `process`, the class's own\n    definition -- the one with the tests and the comment history -- is\n    dead code from the moment the include loads. mixin-method-collision\n    compares two MODULES; this compares module against host.\nACT if the host's version should win, delete it (and call out the\n    module's contract); if the module's should win, delete the host's\n    and consider `prepend` only with an explicit super chain.\nMISLEADS the module match is on SHORT name, so two same-named modules\n    in different namespaces can produce a phantom row; generated\n    methods (attr_accessor, define_method) exist at run time and are\n    invisible here, so a real shadowing can be missed in both\n    directions.", run: runNamed("include-shadows-own-method")},
		{name: "nested-method-def", title: "A def inside a def (Lint/NestedMethodDefinition)", notes: "ANSWERS methods defined inside methods: the inner def is CREATED at each\n    outer call (a new closure object every time, and a method that no\n    profiler, graph or test-discovery tool attributes correctly). Usually\n    a leftover from converting a lambda, occasionally genuine metaprog.\nACT hoist the inner def to the class body, or make it an explicit\n    lambda/proc assigned to a local so the cost is visible.\nMISLEADS the graph records the inner def as a SIBLING-level method with\n    the outer as parent, so fan-in for it is approximate at best;\n    singleton methods inside methods are the legitimate\n    metaprogramming shape and appear here too.", run: runNamed("nested-method-def")},
		{name: "only-called-from-tests", title: "Production methods whose only callers are test files", notes: "ANSWERS the code the test suite keeps alive: every caller is in a test\n    file, so in production the method is unreferenced -- dead-code asks\n    for fan_in=0, which misses this because the tests provide edges.\n    debride's Rails whitelist problem in reverse: the tests are the\n    whitelist, and they are lying.\nACT confirm with a production grep before deleting; if the method is a\n    controller action or invoked by reflection (send, constantize), it\n    is a false positive by construction.\nMISLEADS dynamic dispatch produces no edge, so a genuinely-used method\n    reached only via send or method_missing reads as dead here; a\n    single non-test caller anywhere flips the row out of the result.\n    Callbacks and framework-invoked methods with no literal call site\n    have no edges at all and never appear in either direction.", run: runNamed("only-called-from-tests")},
		{name: "eql-without-hash", title: "A class defines == but no hash/eql? -- silently broken as a Hash key", notes: "ANSWERS the value-object contract gap: `==` defined, `hash` not. The\n    moment an instance goes into a Hash, a Set or uniq, Ruby keys on\n    identity-hash while comparing on your ==, so equal objects land in\n    different buckets and lookups MISS. CodeQL calls the cousin of this\n    CompoundHash; the plain missing-hash case is more common and worse.\nACT define hash alongside == (usually `[a, b].hash`), or inherit\n    Struct/Data which wires both for you.\nMISLEADS lexical: hash/eql? are looked for among the class's OWN def\n    children, so a hash inherited from a parent or generated by Struct\n    reads as missing; deconstruct_keys counts as keying because pattern\n    matching uses it, and a class that is never hashed still appears.", run: runNamed("eql-without-hash")},
		{name: "unguarded-recursion", title: "A recursive method with no conditional in its body", notes: "ANSWERS recursion with no visible base case: is_recursive comes from the\n    resolved call graph, and the body having zero branch and zero case\n    nodes means nothing in THIS method can stop it. Either the guard\n    lives in a callee (fine, but verify it), or the method is a stack\n    overflow and a SystemStackError in production waiting for its first\n    real input.\nACT add the base case here, or move the guard inline so the reader can\n    see the recursion terminate without opening the callee.\nMISLEADS is_recursive is name-resolution, so a recursive HELPER of the\n    same name in another class can mark an innocent method; a body that\n    terminates via exception, throw or a block's break has no branch\n", run: runNamed("unguarded-recursion")},
		{name: "regex-in-loop", title: "gsub / match / Regexp.new inside an iteration (regex recompilation and repeated backtracking)", notes: "ANSWERS per-iteration regex work: gsub and match re-scan on every trip,\n    Regexp.new re-COMPILES (cache miss every time, no /o trick for a\n    variable source), and the whole block re-runs per element of the\n    enclosing enumeration. rubocop-performance's ConstantRegexp covers\n    the constant-hoisting half; this adds the loop context and the\n    per-call recompilation the cop cannot see across methods.\nACT hoist the regex to a frozen constant; for gsub over one big string,\n    do it once OUTSIDE the loop; precompute the Regexp.new argument.\nMISLEADS cost is a static multiplier, not a benchmark: three matches in\n    a loop of ten is noise. match? versus match is not distinguished,\n    and a loop whose collection is empty at run time pays nothing.", run: runNamed("regex-in-loop")},
	}
}

func metricCatalogue() []*question {
	return []*question{
		{name: "graph-blindspots", title: "Read this first: Ruby's call graph is a lower bound, and here is by how much", notes: "ANSWERS how much of every other answer in this catalogue is guesswork.\n     In every other language this query is a footnote. In Ruby it is the\n     headline: send, public_send, define_method, method_missing,\n     const_get and constantize move dispatch out of the syntax tree\n     entirely, and class_eval on a heredoc defines methods in text this\n     parser never sees as code. None of that leaves an edge. Every\n     fan_in, every dead-code claim and every taint path below is a FLOOR.\nACT read pct_opaque before you act on any other query for that module. A\n     module over about 20 percent is one where 'nothing calls this' means\n     'no LITERAL call site exists' and nothing more. dynamic_meta is the\n     subset whose argument is not a literal symbol -- those are not even\n     resolvable in principle without running the program.\nMISLEADS the receiver is NOT typed -- `api` matches on the method name\n     alone, so first, size, to_a, empty? and any? on a plain Array or\n     Hash count as queries. A row whose model column is a local variable\n     or a CONSTANT is one of those.\n     this UNDER-counts twice over. Name-based resolution happily\n     resolves a call to `each` onto whichever single method named `each`\n     exists in the tree, which produces a confident edge that may be\n     wrong -- so `resolved` is not the same as `correct`. And external\n     calls are excluded from pct_opaque on purpose: File.read leaving the\n     tree is design, not blindness.", run: runNamed("graph-blindspots")},
		{name: "block-vs-proc-cost", title: "Block, proc and symbol-to-proc allocation on the methods called most", notes: "ANSWERS the per-call allocation a hot method pays for its own\n     conveniences. rubocop-performance names four of these:\n     RedundantBlockCall (block.call is slower than yield),\n     BlockGivenWithExplicitBlock (an explicit &block param allocates a\n     Proc just to ask whether one was passed), MethodObjectAsBlock, and\n     TimesMap.\nACT prefer yield over an explicit &block parameter; `&:sym` is faster\n     than `{ |x| x.sym }` and allocates less; a block passed with & to a\n     method that only yields is a Proc allocated for nothing.\nMISLEADS fan_in is static call sites, not call frequency, so a method\n     with fan_in 2 inside the hottest loop in the app outranks everything\n     here and does not appear. Nothing on this list is a finding without\n     a benchmark; it is a candidate list for one.", run: runNamed("block-vs-proc-cost")},
		{name: "frozen-literal-debt", title: "Files without frozen_string_literal, ranked by how much they allocate", notes: "ANSWERS which files pay for string allocation they could get for free.\n     Without the magic comment every literal allocates a new String each\n     time it is evaluated -- in a loop or a hot method that is pure GC\n     pressure, and Ruby's allocator does not return the pages to the OS.\nACT add `# frozen_string_literal: true` at the top of the file, then fix\n     whatever breaks -- anything that mutates a literal in place. The\n     files listed first are where the win is largest.\nMISLEADS the magic comment is per FILE, so this ranks files by the worst\n     method inside them. A file with one hot method and forty cold ones\n     scores as high as one that is hot throughout.", run: runNamed("frozen-literal-debt")},
		{name: "hot-multipliers", title: "Where one fix pays back many times: highest fan-in", notes: "ANSWERS which symbols the rest of the tree leans on hardest.\nACT a correctness or speed win in a high-fan-in leaf pays back once per\n     caller. Read it next to sloc: a large fan_in on a tiny function is\n     usually a name collision rather than a hot leaf.\nMISLEADS fan_in counts STATIC call sites this parser could resolve, not\n     runtime frequency, and test callers are included -- in most repos a\n     test helper outranks production code. Scope with --module first.", run: runNamed("hot-multipliers")},
		{name: "risk-ranked", title: "Review order: if you can only read N symbols this week, which N", notes: "ANSWERS which code combines complexity with the operations this language\n     punishes hardest.\nACT start at the top. The weights are this analyzer's own -- read\n     --schema for the formula rather than assuming it matches another\n     language's.\nMISLEADS a heuristic, not a finding. Generated and vendored files are\n     excluded by default, so the real top of the list may sit in code\n     this filter hid.", run: runNamed("risk-ranked")},
		{name: "parse-coverage", title: "What this run could not read", notes: "ANSWERS whether the numbers above cover the code you think they cover.\nACT a file with parsed=0 contributed nothing at all; one with errors\n     contributed only the symbols around the damage. Check meta for\n     grammar_note before concluding the code is broken -- several\n     grammars here are a version behind their language.\nMISLEADS a file can parse perfectly and still be misunderstood. This\n     shows hard failures only, never wrong interpretations.", run: runNamed("parse-coverage")},
		{name: "deep-nesting", title: "Functions with excessive nesting depth (RuboCop Style/NestedTernary)", notes: "ANSWERS where a function has max_nesting > 4, making it hard to read.\nACT extract nested blocks; use early returns or guard clauses.\nMISLEADS Ruby blocks are not structural nesting in the same way as if/while,\n     but the column counts both. A method with a single block is nesting=1.", run: runNamed("deep-nesting")},
		{name: "too-many-params", title: "Methods with too many parameters (RuboCop Metrics/ParameterLists)", notes: "ANSWERS where a method has more than 5 parameters.\nACT use an options hash or keyword arguments.\nMISLEADS a delegate or dispatcher may need many params by design.", run: runNamed("too-many-params")},
		{name: "scattered-concerns", title: "A method called from many different modules (shotgun surgery)", notes: "ANSWERS which methods are called from many distinct modules.\nACT consider splitting or stabilizing the contract.\nMISLEADS a core method like `new` or `to_s` is called from everywhere.", run: runNamed("scattered-concerns")},
		{name: "callback-load", title: "Lifecycle callbacks declared per class, and how many of them query", notes: "ANSWERS the ActiveRecord callback load a model carries: every\n    before_save/after_commit is code the framework runs inside or\n    around every write, so a class with twelve callbacks has a write\n    path nobody can read from `user.update(...)` alone. This is the\n    per-class rollup; callback-cascade ranks the ones that query.\nACT every row is a candidate for extraction: callbacks that send mail,\n    enqueue jobs or write OTHER models are the ones to move first.\nMISLEADS counts declared hooks, not executions -- conditionals\n    (if:/unless:) may never run, and hooks inherited from a concern\n    are attributed to the concern's file, not this class. Association\n    macros are excluded (association-fanout ranks those).", run: runNamed("callback-load")},
		{name: "association-fanout", title: "Associations declared per model -- the join surface every query can touch", notes: "ANSWERS how many belongs_to/has_many/has_and_belongs_to_many edges each\n    model declares. Association count is the raw material of the N+1\n    queries, the schema migrations and the serialization weight: a\n    model with fifteen associations is a hub every API version drags\n    around.\nACT the top rows are where eager-loading discipline (includes,\n    strict_loading) pays the most; check which associations are\n    actually serialized before pruning.\nMISLEADS counts declared macros, not loaded associations at run time,\n    and has_many :through expands to rows that list only what is\n    written. Association options (dependent:, inverse_of:) are not\n    parsed, so a well-audited hub and a neglected one rank the same.", run: runNamed("association-fanout")},
		{name: "mixin-fanout", title: "Hosts ranked by how many modules they mix in -- inclusion coupling per class", notes: "ANSWERS the receive side of Ruby's composition: how many modules each\n    class pulls into its ancestor chain (heavy-mixins ranks the\n    MODULES; this ranks the hosts). Every mixin is methods the host did\n    not write competing for its method table -- the more of them, the\n    less the class's own text tells you about its behavior.\nACT the top rows are the classes where 'find the def' answers nothing;\n    consolidate concerns or split the class before adding another\n    module.\nMISLEADS counts `include`/`extend`/`prepend` statements in the class's\n    own body only: mixins inherited from a superclass and transitively\n    included modules (include A where A includes B) are invisible, and\n    extend self-style internal use counts like a real dependency.", run: runNamed("mixin-fanout")},
		{name: "metaprogram-density", title: "Classes ranked by define_method/method_missing/eval sites per explicit def", notes: "ANSWERS how much of a class's real API is generated rather than\n    written. define_method loops, method_missing routers and\n    class_eval blocks produce methods with no def anywhere in the\n    file -- the density here predicts how far any static answer about\n    the class (fan-in, dead-code, signatures) is from the runtime\n    truth.\nACT read the top rows before trusting ANY static claim about the\n    class; consider replacing define_method loops with explicit defs\n    where the set is small and fixed.\nMISLEADS density over explicit defs UNDERSTATES classes that define\n    everything with zero defs (a pure define_method module divides by\n    its own meta count), and one legitimate DSL module at the top of a\n    namespace can outrank ten hand-written classes. pct_meta caps at\n    100 by construction.", run: runNamed("metaprogram-density")},
		{name: "delegate-density", title: "Classes ranked by ActiveSupport delegate statements vs their own defs", notes: "ANSWERS how much of a class's interface is forwarded elsewhere:\n    `delegate :name, :email, to: :user` is Law-of-Demeter debt made\n    explicit -- the class exists to route calls, and every new field on\n    the target is another line here. A high ratio means the class is a\n    façade; a high COUNT with a low ratio means delegation is leaking\n    into real logic.\nACT for façades above half-delegated, consider handing out the target\n    object instead of the wrapper -- callers get the same methods\n    without the maintenance.\nMISLEADS counts delegate CALLS, not forwarded names (one `delegate :a,\n    :b, :c` is one row), and delegate_missing_to counts once however\n    many methods it actually forwards. Delegation inside methods is\n    invisible; only class-body statements are captured.", run: runNamed("delegate-density")},
		{name: "attr-exposure", title: "Generated attribute accessors as a share of each class's public surface", notes: "ANSWERS the ratio lens on accessor exposure: attr-coupling ranks by raw\n    counts, this ranks by what SHARE of the class's callable surface is\n    machine-generated. A data holder with 30 accessors and 3 real\n    methods is a different design smell from a service with 2 accessors\n    and 40 methods -- same count, different class.\nACT the top rows are structs wearing object costumes: either promote\n    them to Data/Struct explicitly, or start hiding state behind\n    intent-revealing methods.\nMISLEADS accessors are macro DECLARATIONS (each generates reader AND\n    writer), so the share overstates small classes with one accessor;\n    cattr_/mattr_ variants count as accessors even though they attach\n    to the CLASS, and explicit method counts miss generated siblings,\n    so the denominator is the written surface only.", run: runNamed("attr-exposure")},
		{name: "class-variable-surface", title: "Class-level state per class: @@vars, class ivars and where they are written", notes: "ANSWERS the static surface of shared mutable state: class variables,\n    class-level instance variables (mattr_accessor, memoisation) and\n    the methods that WRITE them. class-state-under-threads ranks the\n    ones reachable from threaded entry points; this is the whole\n    inventory, including the batch scripts and boot code.\nACT anything with writes AND size belongs behind a Mutex, a\n    Concurrent::Map, or immutable rebuild-and-rebind.\nMISLEADS a write at BOOT that is read-only afterwards is safe and ranks\n    like a hot cache; @@class vars in a class hierarchy are SHARED down\n    the chain, which this cannot see, and ivars written only in\n    initialize of the class itself (rare) count like request-path\n    state. Reads without writes rank equally -- only write_sites\n    separates them.", run: runNamed("class-variable-surface")},
		{name: "class-weight", title: "Classes and modules ranked by total method load and lines (Metrics/ClassLength family)", notes: "ANSWERS the big classes: method count, class-method count and total\n    lines, with lines per method as the texture read. Size is the\n    strongest single predictor of where changes concentrate -- the\n    per-method metrics (risk-ranked, deep-nesting) cannot see a class\n    that is forty medium methods wide.\nACT split by responsibility: the mixins_ and callback columns in this\n    catalogue (mixin-fanout, callback-load) usually name the seam.\nMISLEADS line counts include comments and blanks, so a heavily\n    documented class outranks a dense one of the same logic; sloc per\n    method below ~5 usually means delegators and accessors, not\n    over-engineering, and modules that only hold constants (zero\n    defs) are excluded by the HAVING-style WHERE.", run: runNamed("class-weight")},
		{name: "constant-coupling", title: "Methods reaching across namespaces the most (Foo::Bar references + const_get)", notes: "ANSWERS namespace coupling at the call level: methods that reference\n    many namespaced constants (::-qualified, not bare Array) plus the\n    dynamic constant loads (const_get, constantize). Each reference is\n    a hard compile-time dependency on another namespace's internals --\n    the Ruby shape of the coupling metric.\nACT the top rows are where an interface (a class method, a value\n    object) would replace a web of direct references.\nMISLEADS counts REFERENCES, not distinct targets: ten uses of one\n    constant outrank ten different ones, and Ruby's own nested names\n    (Sinatra::Base in a Sinatra file) count like foreign coupling.\n    Bare constants (String, Hash) are excluded, which keeps stdlib\n    noise out but also hides genuine dependence on a top-level class\n    your file reopens or shadows.", run: runNamed("constant-coupling")},
		{name: "yield-spread", title: "Modules that hand control to caller blocks the most (block-yield fan-out)", notes: "ANSWERS which classes and modules are block-driven: how many of their\n    methods yield, how many checks block_given?, and how many callers\n    those yielding methods have. A module that yields everywhere is an\n    implicit interface -- its real contract is the block protocol, and\n    no signature shows it.\nACT for the top rows, document (or sig) the block protocol; consider\n    returning an Enumerator so callers can choose the style.\nMISLEADS aggregate per OWNING module: a module with one hot yielding\n    method ranks below one with ten cold ones, and blocks passed with\n    `&` (the other half of block-passing) are counted in\n    block-vs-proc-cost instead. yield inside a lambda is counted like\n    any other, though its return semantics differ, and modules whose\n    yielding methods are all test-only still rank (test files are\n    filtered, but the owners' yield counts are not).", run: runNamed("yield-spread")},
		{name: "enqueue-spread", title: "Job-enqueue calls per owning class -- who launches background work", notes: "ANSWERS which classes reach into background processing: perform_async,\n    perform_later, deliver_later and friends, rolled up per owner. The\n    enqueue call is a process boundary -- the arguments must serialize,\n    the timing is unknown, and the failure is invisible -- so the\n    classes that scatter them are where asynchronous behavior lives.\nACT pair every high row with its job class and check the argument is a\n    plain id, never an AR object (which is serialized at enqueue\n    time).\nMISLEADS the family match is on the METHOD NAME, so a local object\n    with an `enqueue` method counts like Sidekiq; enqueues inside\n    loops are the worse signal and have their own query\n    (enqueue-in-loop). Delivery wrappers (a mailer macro) count once\n    per call site, not per recipient, and Sidekiq's perform_async\n    arriving via method_missing is counted on the name with no\n    knowledge of which worker class it targeted.", run: runNamed("enqueue-spread")},
		{name: "dynamic-fanin", title: "Methods invoked through literal send(:name) sites -- the API the call graph cannot see", notes: "ANSWERS the invisible fan-in: methods whose name appears as a LITERAL\n    symbol argument to send/public_send somewhere in the tree. Every\n    one of those sites is a real caller that produces no edge, so the\n    method's static fan_in understates its use -- and dead-code and\n    only-called-from-tests will happily call it dead.\nACT before deleting or renaming any method on this list, grep for the\n    name as a SYMBOL; after renaming, update the send arguments too.\nMISLEADS name-matched across the whole tree: the send site may target\n    a DIFFERENT object's same-named method, and receivers are not\n    resolved. String-argument sends are excluded (they do not parse to\n    a literal symbol here), so a real dynamic caller using a string\n    name is missed, and define_method-generated methods of the same\n    name have no symbol and cannot appear as targets at all.", run: runNamed("dynamic-fanin")},
	}
}

func (x *xctx) scanClassMeta(n tsNode) {
	x.pendMeta = x.pendMeta[:0]
	x.pendAR = x.pendAR[:0]
	x.pendBlk = x.pendBlk[:0]
	body := childField(n, fBody)
	if !hasNode(body) {
		return
	}
	src := x.src
	stack := x.metaSt[:0]
	forEachNamedChild(body, func(c tsNode) { stack = append(stack, c) })
	for len(stack) > 0 {
		nd := stack[len(stack)-1]
		stack = stack[:len(stack)-1]
		switch kindID(nd) {
		case kindMethod, kindSingl, kindClass, kindModule:
			continue
		case kindCall:
			if mn := childField(nd, fMethod); hasNode(mn) {
				meth := textOf(src, mn)
				if col, ok := metaprogramAPIs[meth]; ok {
					setCount(&x.st, counterOf(col), x.stOf(col)+1)
					x.bump(cMetaprogramTotal)
				}
				x.callDetail(nd, meth, 0, true)
			}
		}
		forEachNamedChild(nd, func(c tsNode) { stack = append(stack, c) })
	}
	x.metaSt = stack[:0]
}

func (x *xctx) functionFlags(n tsNode, sc scope, vis, name string) {
	st := &x.st
	body := childField(n, fBody)
	singleton := b2i(kindID(n) == kindSingl || inSingletonClass(n))

	hasSig := int32(0)
	if prv := prevSibling(n); hasNode(prv) && kindID(prv) == kindCall {
		pt := cgStripLeft(textOf(x.src, prv))
		if strings.HasPrefix(pt, "sig") && !strings.HasPrefix(pt, "signature") {
			hasSig = 1
		}
	}
	st.IsPublic = b2i(vis == "public")
	st.IsStatic = singleton
	st.IsSingleton = singleton
	if hasNode(body) {
		t := kindName(kindID(body))
		if t != "body_statement" && t != "do" {
			st.IsEndless = 1
		}
	}
	st.IsTest = b2i(strings.HasPrefix(name, "test_") || strings.HasPrefix(name, "test ") ||
		x.rec.IsTest != 0)
	st.IsGenerator = 0
	st.IsEntrypoint = b2i(inSet(entrypointNames, name) ||
		(x.ctrl != 0 && vis == "public"))
	st.IsController = x.ctrl
	st.IsModel = x.model
	st.IsJob = x.job
	st.HasFrozenLiteral = x.frozen
	st.HasSig = hasSig
	st.IsAbstract = b2i(raisesNotImplemented(n, x.src))

	x.scanBody(n)
	st.IsGenerator = x.pendYld

	if name == "method_missing" || name == "respond_to_missing?" || name == "const_missing" {

		st.NMethodMissing = 1
		st.NMetaprogramTotal = 1
		x.pendMeta = append(x.pendMeta, wMetaSite{
			FileID: x.rec.ID, API: "def " + name, FromVar: 1,
			Line: int32(startRow(n) + 1)})
	}
}

var entrypointNames = map[string]bool{
	"perform": true, "perform_now": true, "call": true,
	"run": true, "execute": true, "main": true,
}

func (x *xctx) typeFlags(n tsNode, sc scope, name, short, head, supTxt string) {
	st := &x.st
	st.IsPublic = 1
	st.IsController = b2i(x.ctrl != 0 || strings.Contains(short, "Controller"))
	st.IsModel = x.model
	st.IsJob = x.job
	st.HasFrozenLiteral = x.frozen
	st.NMonkeyPatch = b2i(reopensCore(name, short, sc.qualPrefix))
	st.IsConcern = b2i(strings.Contains(head, "ActiveSupport::Concern"))
	st.IsAbstract = b2i(strings.Contains(head, "abstract_class"))

	x.zeroMetaprogramme()
	x.scanClassMeta(n)
}

func (x *xctx) zeroMetaprogramme() {
	s := &x.st
	s.NSend, s.NDefineMethod, s.NMethodMissing, s.NConstGet = 0, 0, 0, 0
	s.NInstanceEval, s.NClassEval, s.NInstanceVarGet, s.NEval = 0, 0, 0, 0
	s.NMetaprogramOther, s.NMetaprogramTotal = 0, 0
}

func reopensCore(name, short, qualPrefix string) bool {
	if !inSet(coreClasses, short) {
		return false
	}
	if strings.HasPrefix(name, "::") {
		return true
	}
	return qualPrefix == ""
}

func (x *xctx) typeExtra(n tsNode, sid int32, name, short, supTxt string, sc scope) {
	src := x.src
	body := childField(n, fBody)
	isCore := reopensCore(name, short, sc.qualPrefix)
	var st cbState
	for _, m := range x.pendMeta {
		m.SymID = sid
		m.FileID = x.rec.ID
		x.out.msites = append(x.out.msites, m)
	}
	for _, a := range x.pendAR {
		a.SymID = sid
		a.FileID = x.rec.ID
		x.out.arqs = append(x.out.arqs, a)
	}
	x.pendMeta = x.pendMeta[:0]
	x.pendAR = x.pendAR[:0]
	x.classBody(body, sid, short, isCore, &st, 0)
	x.out.rmods = append(x.out.rmods, wRubyModule{
		SymID: sid, FileID: x.rec.ID, Name: trunc(name, 200),
		IsModule:             b2i(kindID(n) == kindModule),
		IsConcern:            st.concern,
		HasIncludedBlock:     st.included,
		HasClassMethodsBlock: st.classMethods,
		Superclass:           trunc(supTxt, 120),
		NMixins:              st.mixins,
		NDefs:                st.defs,
		NClassDefs:           st.cdefs,
		NClassIvars:          st.ivars,
		NClassVars:           st.cvars,
		NGlobals:             st.globals,
		NDelegates:           st.delegates,
		ReopensCore:          b2i(isCore),
		Line:                 int32(startRow(n) + 1),
	})
	_ = src
}

func (x *xctx) classBody(body tsNode, sid int32, short string, isCore bool, st *cbState, inSingleton int32) {
	if !hasNode(body) {
		return
	}
	src := x.src
	forEachNamedChild(body, func(n tsNode) {
		switch kindID(n) {
		case kindMethod:
			st.defs++
			if inSingleton != 0 {
				st.cdefs++
			}
			if isCore {
				mn := childField(n, fName)
				mtxt := "?"
				isOp := false
				if hasNode(mn) {
					mtxt = textOf(src, mn)
					isOp = kindID(mn) == kindOper
				}
				x.out.mps = append(x.out.mps, wMonkeyPatch{
					SymID: sid, FileID: x.rec.ID, CoreClass: short,
					Method: trunc(mtxt, 80), Operator: b2i(isOp),
					Singleton: inSingleton, Line: int32(startRow(n) + 1)})
			}
			return
		case kindSingl:
			st.defs++
			st.cdefs++
			if isCore {
				mn := childField(n, fName)
				mtxt := "?"
				isOp := false
				if hasNode(mn) {
					mtxt = textOf(src, mn)
					isOp = kindID(mn) == kindOper
				}
				x.out.mps = append(x.out.mps, wMonkeyPatch{
					SymID: sid, FileID: x.rec.ID, CoreClass: short,
					Method: trunc(mtxt, 80), Operator: b2i(isOp), Singleton: 1,
					Line: int32(startRow(n) + 1)})
			}
			return
		case kindSingCls:
			x.classBody(childField(n, fBody), sid, short, isCore, st, 1)
			return
		case kindAssign, kindOpAsgn:
			if left := childField(n, fLeft); hasNode(left) {
				switch kindID(left) {
				case kindInstanceVar:
					st.ivars++
				case kindClassVar:
					st.cvars++
				case kindGlobalVar:
					st.globals++
				}
			}
			return
		}
		if kindID(n) != kindCall {
			return
		}
		mn := childField(n, fMethod)
		if !hasNode(mn) {
			return
		}
		meth := textOf(src, mn)
		args := childField(n, fArguments)
		blk := childField(n, fBlock)
		line := int32(startRow(n) + 1)

		switch {
		case hasNode(args) && mixinKinds[meth] != "":
			forEachNamedChild(args, func(a tsNode) {
				mx := cgStrip(textOf(src, a))
				if mx == "" || !isUpper(mx[0]) {
					return
				}
				st.mixins++
				if strings.HasSuffix(mx, "Concern") {
					st.concern = 1
				}
				shortMix := mx
				if j := strings.LastIndex(mx, "::"); j >= 0 {
					shortMix = mx[j+2:]
				}
				x.out.mixins = append(x.out.mixins, wMixin{
					HostID: sid, FileID: x.rec.ID, Host: short,
					Mixin: trunc(mx, 120), MixinShort: trunc(shortMix, 80),
					Kind: mixinKinds[meth], InSingleton: inSingleton, Line: line})
			})
		case attrMacros[meth] != "" && hasNode(args):

			col := attrMacros[meth]
			typ := col[2:]
			forEachNamedChild(args, func(a tsNode) {
				an := strings.Trim(cgStrip(textOf(src, a)), ":\"' ")
				if an == "" {
					return
				}
				st.attrs++
				x.out.fields = append(x.out.fields, wField{
					SymID: sid, Ord: st.attrs, Name: trunc(an, 120),
					Type: typ, Vis: "public", Line: line,
					Static: inSingleton, Mutable: 1, Untyped: 1,
				})
			})
		case meth == "delegate" || meth == "delegate_missing_to":

			st.delegates++
		case inSet(arCallbacks, meth) || inSet(arAssociations, meth):
			target := ""
			var cond int32
			if hasNode(args) {
				for i, m := 0, namedChildCount(args); i < m; i++ {
					a := namedChildAt(args, i)
					if (kindID(a) == kindSimSym || kindID(a) == kindDelim) && target == "" {

						target = strings.Trim(strings.TrimLeft(textOf(src, a), ":"), "\"'")
					} else if kindID(a) == kindPair {
						if k := childField(a, fKey); hasNode(k) {
							switch strings.TrimRight(textOf(src, k), ":") {
							case "if", "unless", "on":
								cond = 1
							}
						}
					}
				}
			}
			x.out.arcbs = append(x.out.arcbs, wARCallback{
				SymID: sid, FileID: x.rec.ID, Host: short, Hook: trunc(meth, 40),
				Method: trunc(target, 80), Conditional: cond, Block: b2i(hasNode(blk)),
				Association: b2i(inSet(arAssociations, meth)), Line: line})
		case inSet(bareBlockHooks, meth):
			if meth == "included" {
				st.included = 1
			} else if meth == "class_methods" {
				st.classMethods = 1
			}
			if hasNode(blk) {
				inner := int32(0)
				if meth == "class_methods" {
					inner = 1
				}
				x.classBody(childField(blk, fBody), sid, short, isCore, st, inner)
			}
		case inSet(visibilityWords, meth):
			if !hasNode(args) || namedChildCount(args) == 0 {
				x.vis = append(x.vis, visRange{line, int32(endRow(body) + 1), visWord(meth)})
			}
		}
	})

	forEachNamedChild(body, func(n tsNode) {
		if kindID(n) != kindIdent {
			return
		}
		txt := textOf(src, n)
		if inSet(visibilityWords, txt) {
			x.vis = append(x.vis, visRange{
				int32(startRow(n) + 1),
				int32(endRow(body) + 1), visWord(txt)})
		}
	})
}

var bareBlockHooks = map[string]bool{
	"included": true, "class_methods": true, "prepended": true,
	"extended": true, "included_do": true,
}

var visibilityWords = map[string]bool{
	"private": true, "protected": true, "public": true,
	"module_function": true, "private_class_method": true,
}

func visWord(m string) string {
	switch m {
	case "protected":
		return "protected"
	case "private", "module_function", "private_class_method":
		return "private"
	}
	return "public"
}

func init() {
	reg := func(name string, f func(*Graph, func(string) bool, int) *result) {
		questionRuns[name] = f
	}

	reg("n-plus-one", func(g *Graph, mod func(string) bool, lim int) *result {
		type key struct {
			sym        int32
			model, api string
		}
		type agg struct {
			s                 *Sym
			depth, forced, at int32
			n                 int32
			kind              string
		}
		groups := make(map[key]*agg, 512)
		var order []key
		for i := range g.ARQs {
			q := &g.ARQs[i]
			if q.LoopDepth <= 0 || !okFile(g, q.FileID, mod) {
				continue
			}
			if int(q.SymID) > len(g.Syms) || q.SymID == 0 {
				continue
			}
			s := g.Syms[q.SymID-1]
			if !mod(g.modNameOf(s.ModuleId)) {
				continue
			}
			k := key{q.SymID, q.Model(), q.API()}
			a := groups[k]
			if a == nil {
				a = &agg{s: s, at: q.Line, kind: q.BuildKind()}
				groups[k] = a
				order = append(order, k)
			}
			a.n++
			if q.LoopDepth > a.depth {
				a.depth = q.LoopDepth
			}
			if q.BuildKind() == "terminal" || q.BuildKind() == "raw_sql" {
				a.forced++
			}
			if q.Line < a.at {
				a.at = q.Line
			}
		}
		res := &result{cols: []string{"in_method", "module_", "model", "api",
			"build_kind", "depth", "queries", "iter_blocks", "block_depth",
			"forced", "ctrl", "fan_in", "at"}}
		sort.Slice(order, func(i, j int) bool {
			if order[i].sym != order[j].sym {
				return order[i].sym > order[j].sym
			}
			if order[i].model != order[j].model {
				return order[i].model > order[j].model
			}
			return order[i].api > order[j].api
		})
		for _, k := range order {
			a := groups[k]
			res.rows = append(res.rows, row{cs(a.s.Name()),
				cs(g.modNameOf(a.s.ModuleId)), cs(k.model), cs(k.api), cs(a.kind),
				ci32(a.depth), ci32(a.n), ci32(a.s.NIterBlocks),
				ci32(a.s.MaxBlockDepth), ci32(a.forced), ci32(a.s.IsController),
				ci32(a.s.FanIn), cs(g.at(a.s.FileId, a.at))})
		}
		return finish(res, func(a, b row) bool {
			return desc3(a[5].i, b[5].i, a[9].i, b[9].i, a[6].i, b[6].i)
		}, lim)
	})

	reg("params-to-dynamic-dispatch", func(g *Graph, mod func(string) bool, lim int) *result {
		var roots []int32
		for _, s := range g.Syms {
			if s.NParamsRead > 0 && s.Kind() == "method" {
				roots = append(roots, s.Id)
			}
		}
		sites := groupMeta(g)
		type key struct {
			src, sym int32
			api      string
		}
		groups := make(map[key]*sinkGroup, 256)
		for _, rp := range reachPairs(g, roots, 4) {
			for _, m := range sites[rp.Sym] {
				if m.Literal != 0 || !okFile(g, m.FileID, mod) {
					continue
				}
				s := g.Syms[rp.Sym-1]
				if !mod(g.modNameOf(s.ModuleId)) {
					continue
				}
				k := key{rp.Root, rp.Sym, m.API()}
				a := groups[k]
				if a == nil {
					a = &sinkGroup{}
					groups[k] = a
				}
				if !a.ok {
					a.ok, a.sum.hops, a.sum.at = true, rp.Hops, m.Line
				} else {
					a.sum.hops = mini(a.sum.hops, rp.Hops)
					a.sum.at = mini(a.sum.at, m.Line)
				}
				a.sum.par += m.FromParams
				a.sum.here += m.OnHeredoc
				a.sum.lit += m.Literal
			}
		}
		res := &result{cols: []string{"reads_params", "dispatches_in", "hops",
			"api", "argument", "literal_args", "param_args", "heredoc_args",
			"exec_calls", "backticks", "ctrl", "at"}}
		keys := sortedPairs2(groups)
		sort.Slice(keys, func(i, j int) bool {
			if keys[i].src != keys[j].src {
				return keys[i].src > keys[j].src
			}
			if keys[i].sym != keys[j].sym {
				return keys[i].sym < keys[j].sym
			}
			return keys[i].api > keys[j].api
		})
		for _, k := range keys {
			a := groups[k]
			s := g.Syms[k.sym-1]

			arg := cnull()
			for _, m := range sites[k.sym] {
				if m.API() == k.api {

					arg = cs(substr40(m.Arg()))
					break
				}
			}

			res.rows = append(res.rows, row{cs(g.Syms[k.src-1].Name()), cs(s.Name()),
				ci32(a.sum.hops), cs(k.api), arg, ci32(a.sum.lit), ci32(a.sum.par),
				ci32(a.sum.here), ci32(s.NExec), ci32(s.NSubshell),
				ci32(g.Syms[k.src-1].IsController), cs(g.at(s.FileId, a.sum.at))})
		}
		return finish(res, func(a, b row) bool {
			if a[6].i != b[6].i {
				return a[6].i > b[6].i
			}
			if a[2].i != b[2].i {
				return a[2].i < b[2].i
			}
			return a[8].i > b[8].i
		}, lim)
	})

	reg("monkey-patch-blast-radius", func(g *Graph, mod func(string) bool, lim int) *result {
		type key struct{ cc, method string }
		type agg struct {
			op, cls, sites, at, fid int32
		}
		groups := make(map[key]*agg, 64)
		var order []key
		for i := range g.MPs {
			p := &g.MPs[i]
			if !okFile(g, p.FileID, mod) {
				continue
			}
			k := key{p.CoreClass(), p.Method()}
			a := groups[k]
			if a == nil {
				a = &agg{at: p.Line, fid: p.FileID}
				groups[k] = a
				order = append(order, k)
			}
			a.sites++
			if p.Operator != 0 {
				a.op = 1
			}
			if p.Singleton != 0 {
				a.cls = 1
			}
			if p.Line < a.at {
				a.at, a.fid = p.Line, p.FileID
			}
		}

		byName := make(map[string]int32, 4096)
		for _, s := range g.Syms {
			if s.Kind() == "method" {
				byName[s.Name()]++
			}
		}
		sitesByName := make(map[string]int32, 4096)
		for i := range g.Sites {
			callee := g.Sites[i].Callee
			if callee > 0 && int(callee) <= len(g.Syms) {
				sitesByName[g.Syms[callee-1].Name()]++
			}
		}
		res := &result{cols: []string{"core_class", "method", "operator",
			"class_method", "patch_sites", "same_name_defs", "unresolved_uses",
			"resolved_uses", "could_collide", "at"}}
		for _, k := range order {
			a := groups[k]
			var unresDot, collide int32
			for i := range g.Unres {
				n := g.Unres[i].Name()

				if n == k.method || likeFold("%."+k.method, n) {
					unresDot++
				}
				if likeFold("%"+k.method, n) {
					collide++
				}
			}
			res.rows = append(res.rows, row{cs(k.cc), cs(k.method), ci32(a.op),
				ci32(a.cls), ci32(a.sites), ci32(byName[k.method]),
				ci32(unresDot), ci32(sitesByName[k.method]),
				ci32(byName[k.method] + collide), cs(g.at(a.fid, a.at))})
		}
		return finish(res, func(a, b row) bool {
			return desc2(a[8].i, b[8].i, a[2].i, b[2].i)
		}, lim)
	})

	reg("string-churn-unfrozen", symTable([]colDef{
		nameCol(), modCol(),
		num("has_frozen", func(s *Sym) int32 { return s.HasFrozenLiteral }),
		num("str_in_loop", func(s *Sym) int32 { return s.NStrLitInLoop }),
		num("interp", func(s *Sym) int32 { return s.NStringInterp }),
		num("strings", func(s *Sym) int32 { return s.NStringLit }),
		num("iter_blocks", func(s *Sym) int32 { return s.NIterBlocks }),
		num("block_depth", func(s *Sym) int32 { return s.MaxBlockDepth }),
		num("loop_depth", func(s *Sym) int32 { return s.MaxLoopDepth }),
		num("freezes", func(s *Sym) int32 { return s.NFreeze }),
		num("dups", func(s *Sym) int32 { return s.NDupClone }),
		num("fan_in", func(s *Sym) int32 { return s.FanIn }),
		{"churn", func(_ *Graph, s *Sym) cell {
			return ci32(s.NStrLitInLoop * (1 + s.MaxBlockDepth + s.MaxLoopDepth))
		}},
		atCol(),
	}, func(s *Sym) bool {
		return s.HasFrozenLiteral == 0 && s.NStrLitInLoop > 0
	}, func(a, b row) bool { return desc2(a[12].i, b[12].i, a[11].i, b[11].i) }))

	reg("rescue-swallow", symTable([]colDef{
		nameCol(), modCol(),
		num("rescues", func(s *Sym) int32 { return s.NRescue }),
		num("bare", func(s *Sym) int32 { return s.NRescueBare }),
		num("catches_exception", func(s *Sym) int32 { return s.NRescueException }),
		num("empty_", func(s *Sym) int32 { return s.NRescueEmpty }),
		num("reraises", func(s *Sym) int32 { return s.NRescueReraise }),
		num("retries", func(s *Sym) int32 { return s.NRetry }),
		num("ensures", func(s *Sym) int32 { return s.NEnsure }),
		num("raises", func(s *Sym) int32 { return s.NRaise }),
		num("db", func(s *Sym) int32 { return s.NSql + s.NRailsQuery }),
		num("http", func(s *Sym) int32 { return s.NNet }),
		num("io", func(s *Sym) int32 { return s.NIo }),
		num("ar_calls", func(s *Sym) int32 { return s.NArQuery }),
		num("fan_in", func(s *Sym) int32 { return s.FanIn }),
		{"severity", func(_ *Graph, s *Sym) cell {
			return ci32((s.NRescueEmpty*4 + s.NRescueException*3 + s.NRescueBare) *
				(1 + s.NSql + s.NNet + s.NRailsQuery))
		}},
		atCol(),
	}, func(s *Sym) bool {
		return s.NRescueBare+s.NRescueException+s.NRescueEmpty > 0 && s.NRescueReraise == 0
	}, func(a, b row) bool { return desc2(a[15].i, b[15].i, a[14].i, b[14].i) }))

	reg("class-state-under-threads", func(g *Graph, mod func(string) bool, lim int) *result {
		var roots []int32
		for _, s := range g.Syms {
			if s.IsThreadedEntry != 0 {
				roots = append(roots, s.Id)
			}
		}
		type key struct{ entry, sym int32 }
		type agg struct {
			hops, at, cv, gl, ci, wr, mu, tl int32
		}
		groups := make(map[key]*agg, 1024)
		for _, rp := range reachPairs(g, roots, 4) {
			{
				entry, sym, hops := rp.Root, rp.Sym, rp.Hops
				s := g.Syms[sym-1]
				if s.NClassVar+s.NGlobalVar+s.NClassLevelWrite == 0 ||
					!okFile(g, s.FileId, mod) {
					continue
				}
				k := key{entry, sym}
				a := groups[k]
				if a == nil {
					a = &agg{hops: hops, at: s.LineStart}
					groups[k] = a
				}
				if hops < a.hops {
					a.hops = hops
				}
				a.cv = maxi(a.cv, s.NClassVar)
				a.gl = maxi(a.gl, s.NGlobalVar)
				a.ci = maxi(a.ci, s.NClassLevelIvar)
				a.wr = maxi(a.wr, s.NClassLevelWrite)
				a.mu = maxi(a.mu, s.NMutex)
				a.tl = maxi(a.tl, s.NThreadLocal)
				a.at = mini(a.at, s.LineStart)
			}
		}
		res := &result{cols: []string{"threaded_entry", "touches_state", "hops",
			"class_vars", "globals", "class_ivars", "writes", "mutexes",
			"thread_locals", "spawns", "job", "ctrl", "at"}}
		for _, k := range sortedPairs2(groups) {
			a := groups[k]
			if a.mu != 0 {
				continue
			}
			e := g.Syms[k.entry-1]
			s := g.Syms[k.sym-1]
			res.rows = append(res.rows, row{cs(e.Name()), cs(s.Name()), ci32(a.hops),
				ci32(a.cv), ci32(a.gl), ci32(a.ci), ci32(a.wr), ci32(a.mu),
				ci32(a.tl), ci32(e.NThreadNew), ci32(e.IsJob),
				ci32(e.IsController), cs(g.at(s.FileId, a.at))})
		}
		return finish(res, func(a, b row) bool {
			if a[6].i != b[6].i {
				return a[6].i > b[6].i
			}
			if a[3].i != b[3].i {
				return a[3].i > b[3].i
			}
			return a[2].i < b[2].i
		}, lim)
	})

	reg("timeout-blast-radius", func(g *Graph, mod func(string) bool, lim int) *result {
		blk := groupBlocks(g)
		res := &result{cols: []string{"name", "module_", "timeouts", "db", "http",
			"io", "ensures", "mutexes", "spawns", "rescues", "ar_writes",
			"timeout_blocks", "fan_in", "blast", "at"}}
		for _, s := range g.Syms {
			if s.NTimeout == 0 || !okFile(g, s.FileId, mod) {
				continue
			}
			var tb int32
			for _, b := range blk[s.Id] {
				if b.Method() == "timeout" {
					tb++
				}
			}
			res.rows = append(res.rows, row{cs(s.Name()), cs(g.modNameOf(s.ModuleId)),
				ci32(s.NTimeout), ci32(s.NSql + s.NRailsQuery), ci32(s.NNet),
				ci32(s.NIo), ci32(s.NEnsure), ci32(s.NMutex), ci32(s.NThreadNew),
				ci32(s.NRescue), ci32(s.NArWrite), ci32(tb), ci32(s.FanIn),
				ci32(s.NTimeout * (1 + s.NSql + s.NNet*2 + s.NArWrite*3 +
					s.NEnsure*2 + s.NMutex*3)), symAt(g, s)})
		}
		return finish(res, func(a, b row) bool { return a[13].i > b[13].i }, lim)
	})

	reg("mass-assignment", func(g *Graph, mod func(string) bool, lim int) *result {
		permitsByFile := make(map[int32]int32, 256)
		for _, s := range g.Syms {
			if s.Kind() == "method" {
				permitsByFile[s.FileId] += s.NPermit
			}
		}
		res := &result{cols: []string{"name", "module_", "params_reads", "sinks",
			"permits", "permit_bang", "permit_nearby", "ar_writes", "ctrl",
			"public_", "fan_in", "at"}}
		for _, s := range g.Syms {
			if s.NMassAssign == 0 || (s.NPermit != 0 && s.NPermitBang == 0) ||
				s.NParamsRead == 0 || !okFile(g, s.FileId, mod) {
				continue
			}
			res.rows = append(res.rows, row{cs(s.Name()), cs(g.modNameOf(s.ModuleId)),
				ci32(s.NParamsRead), ci32(s.NMassAssign), ci32(s.NPermit),
				ci32(s.NPermitBang), ci32(permitsByFile[s.FileId]),
				ci32(s.NArWrite), ci32(s.IsController), ci32(s.IsPublic),
				ci32(s.FanIn), symAt(g, s)})
		}
		return finish(res, func(a, b row) bool {
			return desc3(a[5].i, b[5].i, a[2].i, b[2].i, a[3].i, b[3].i)
		}, lim)
	})

	reg("callback-cascade", func(g *Graph, mod func(string) bool, lim int) *result {
		by := calleeAdjacency(g)
		type agg struct {
			reach, methods, ar, writes, inBlk, http int32
		}
		aggs := make(map[int32]*agg, 256)
		for i := range g.ARCBs {
			c := &g.ARCBs[i]
			if !c.HasTargetID || !okFile(g, c.FileID, mod) {
				continue
			}
			a := aggs[c.ID]
			if a == nil {
				a = &agg{}
				aggs[c.ID] = a
			}
			seen := map[int32]bool{c.TargetID: true}
			a.methods++
			frontier := []int32{c.TargetID}
			for d := int32(0); d < 3 && len(frontier) > 0; d++ {
				var next []int32
				for _, s := range frontier {
					if d > a.reach {
						a.reach = d
					}
					if !seen[s] {
						seen[s] = true
						a.methods++
					}
					t := g.Syms[s-1]
					a.ar += t.NArQuery
					a.writes += t.NArWrite
					a.inBlk += t.NArQueryInBlock
					a.http += t.NNet
					for _, c2 := range by[s] {
						if !seen[c2] {
							next = append(next, c2)
						}
					}
				}
				frontier = next
			}
		}
		res := &result{cols: []string{"host", "hook", "method", "conditional",
			"assoc", "direct_query", "reach", "methods_pulled_in", "ar_calls",
			"writes", "queries_in_loops", "http_calls", "at"}}
		for i := range g.ARCBs {
			c := &g.ARCBs[i]
			a := aggs[c.ID]
			if a == nil || (a.ar == 0 && a.http == 0) {
				continue
			}
			res.rows = append(res.rows, row{cs(c.Host()), cs(c.Hook()), cs(c.Method()),
				ci32(c.Conditional), ci32(c.Association), ci32(c.IssuesQuery),
				ci32(a.reach), ci32(a.methods), ci32(a.ar), ci32(a.writes),
				ci32(a.inBlk), ci32(a.http), cs(g.at(c.FileID, c.Line))})
		}
		return finish(res, func(a, b row) bool {
			return desc3(a[10].i, b[10].i, a[8].i, b[8].i, a[6].i, b[6].i)
		}, lim)
	})

	reg("mixin-method-collision", func(g *Graph, mod func(string) bool, lim int) *result {

		modOf := make(map[int32]*Sym, 4096)
		for _, s := range g.Syms {
			if s.Kind() == "module" {
				modOf[s.Id] = s
			}
		}
		byModName := make(map[string]map[string][]int32, 256)
		for _, s := range g.Syms {
			if s.Kind() != "method" {
				continue
			}
			m := modOf[s.ParentId]
			if m == nil {
				continue
			}
			if byModName[m.Name()] == nil {
				byModName[m.Name()] = map[string][]int32{}
			}
			byModName[m.Name()][s.Name()] = append(byModName[m.Name()][s.Name()], s.Sloc)
		}
		mixByHost := make(map[int32][]*Mixin, 256)
		for i := range g.Mixins {
			mixByHost[g.Mixins[i].HostID] = append(mixByHost[g.Mixins[i].HostID], &g.Mixins[i])
		}
		res := &result{cols: []string{"host_class", "kind_a", "mixin_a",
			"kind_b", "mixin_b", "collides_on", "sloc_a", "sloc_b", "has_prepend",
			"line_a", "line_b", "wins_if_plain_include", "at"}}
		hosts := make([]int32, 0, len(mixByHost))
		for h := range mixByHost {
			hosts = append(hosts, h)
		}
		slices.Sort(hosts)
		for _, host := range hosts {
			if !okFile(g, g.Syms[host-1].FileId, mod) {
				continue
			}
			ms := mixByHost[host]
			for i := range ms {
				for j := i + 1; j < len(ms); j++ {

					a, b := ms[i], ms[j]
					if a.MixinShort() > b.MixinShort() {
						a, b = b, a
					}
					if a.MixinShort() == b.MixinShort() {
						continue
					}
					da, db := byModName[a.MixinShort()], byModName[b.MixinShort()]
					if da == nil || db == nil {
						continue
					}
					for meth, sas := range da {
						sbs, ok := db[meth]
						if !ok {
							continue
						}
						for _, sa := range sas {
							for _, sb := range sbs {
								hp := int32(0)
								if a.Kind() == "prepend" || b.Kind() == "prepend" {
									hp = 1
								}
								wins := a.MixinShort()
								if b.Line > a.Line {
									wins = b.MixinShort()
								}
								res.rows = append(res.rows, row{
									cs(g.Syms[host-1].Name()), cs(a.Kind()), cs(a.MixinShort()),
									cs(b.Kind()), cs(b.MixinShort()), cs(meth), ci32(sa),
									ci32(sb), ci32(hp), ci32(a.Line), ci32(b.Line),
									cs(wins), symAt(g, g.Syms[host-1])})
							}
						}
					}
				}
			}
		}
		return finish(res, func(a, b row) bool {
			return desc2(a[8].i, b[8].i, a[6].i, b[6].i)
		}, lim)
	})

	reg("sql-interpolation", func(g *Graph, mod func(string) bool, lim int) *result {
		res := &result{cols: []string{"model", "api", "build_kind", "in_method",
			"module_", "interp", "from_params", "sanitized", "string_arg",
			"chain", "in_loop", "sql_interp_lits", "sanitize_calls", "ctrl",
			"fan_in", "at"}}
		for i := range g.ARQs {
			q := &g.ARQs[i]
			if (q.HasInterpolation == 0 && q.FromParams == 0) || q.IsSanitized != 0 ||
				!okFile(g, q.FileID, mod) || q.SymID == 0 || int(q.SymID) > len(g.Syms) {
				continue
			}
			s := g.Syms[q.SymID-1]
			if !mod(g.modNameOf(s.ModuleId)) {
				continue
			}
			res.rows = append(res.rows, row{cs(q.Model()), cs(q.API()), cs(q.BuildKind()),
				cs(s.Name()), cs(g.modNameOf(s.ModuleId)), ci32(q.HasInterpolation),
				ci32(q.FromParams), ci32(q.IsSanitized), ci32(q.IsStringArg),
				ci32(q.Chain), ci32(q.LoopDepth), ci32(s.NSqlInterp),
				ci32(s.NSqlSanitized), ci32(s.IsController), ci32(s.FanIn),
				cs(g.at(q.FileID, q.Line))})
		}
		return finish(res, func(a, b row) bool {
			ra, rb := int64(0), int64(0)
			if a[2].s == "raw_sql" {
				ra = 1
			}
			if b[2].s == "raw_sql" {
				rb = 1
			}
			return desc3(a[6].i, b[6].i, ra, rb, a[5].i, b[5].i)
		}, lim)
	})

	reg("per-iteration-cost", symTable([]colDef{
		nameCol(), modCol(),
		num("lit_in_loop", func(s *Sym) int32 { return s.NCollectionLitInLoop }),
		num("chain_alloc", func(s *Sym) int32 { return s.NChainArrayAlloc }),
		num("map_chains", func(s *Sym) int32 { return s.NMapChain }),
		num("range_include", func(s *Sym) int32 { return s.NRangeInclude }),
		num("times_map", func(s *Sym) int32 { return s.NTimesMap }),
		num("str_in_loop", func(s *Sym) int32 { return s.NStrLitInLoop }),
		num("iter_blocks", func(s *Sym) int32 { return s.NIterBlocks }),
		num("block_depth", func(s *Sym) int32 { return s.MaxBlockDepth }),
		num("loop_depth", func(s *Sym) int32 { return s.MaxLoopDepth }),
		num("calls_in_loop", func(s *Sym) int32 { return s.CallInLoop }),
		num("frozen_", func(s *Sym) int32 { return s.HasFrozenLiteral }),
		num("fan_in", func(s *Sym) int32 { return s.FanIn }),
		{"cost", func(_ *Graph, s *Sym) cell {
			return ci32((s.NCollectionLitInLoop*4 + s.NChainArrayAlloc*3 +
				s.NRangeInclude*2 + s.NTimesMap*3 + s.NStrLitInLoop) *
				(1 + s.MaxBlockDepth + s.MaxLoopDepth))
		}},
		atCol(),
	}, func(s *Sym) bool {
		return s.NCollectionLitInLoop+s.NChainArrayAlloc+s.NRangeInclude+s.NTimesMap > 0
	}, func(a, b row) bool { return a[14].i > b[14].i }))

	reg("rescue-too-broad", symTable([]colDef{
		nameCol(), qualCol(),
		num("rescue_exception", func(s *Sym) int32 { return s.NRescueException }),
		num("bare", func(s *Sym) int32 { return s.NRescueBare }),
		num("empty_bodies", func(s *Sym) int32 { return s.NRescueEmpty }),
		num("reraises", func(s *Sym) int32 { return s.NRescueReraise }),
		num("ensures", func(s *Sym) int32 { return s.NEnsure }),
		num("retries", func(s *Sym) int32 { return s.NRetry }),
		num("fan_in", func(s *Sym) int32 { return s.FanIn }),
		atCol(),
	}, func(s *Sym) bool {
		return s.NRescueException > 0 || s.NRescueBare > 0
	}, func(a, b row) bool {
		return desc2(a[2].i, b[2].i, a[3].i-a[5].i, b[3].i-b[5].i)
	}))

	reg("threads-without-synchronisation", symTable([]colDef{
		nameCol(), qualCol(),
		num("threads", func(s *Sym) int32 { return s.NThreadNew }),
		num("ractors", func(s *Sym) int32 { return s.NRactor }),
		num("mutexes", func(s *Sym) int32 { return s.NMutex }),
		num("thread_locals", func(s *Sym) int32 { return s.NThreadLocal }),
		num("class_writes", func(s *Sym) int32 { return s.NClassLevelWrite }),
		num("globals", func(s *Sym) int32 { return s.NGlobalVar }),
		num("threaded_entry", func(s *Sym) int32 { return s.IsThreadedEntry }),
		num("fan_in", func(s *Sym) int32 { return s.FanIn }),
		atCol(),
	}, func(s *Sym) bool {
		return (s.NThreadNew > 0 || s.NRactor > 0) && s.NMutex == 0
	}, func(a, b row) bool {
		return desc2(a[6].i+a[7].i, b[6].i+b[7].i, a[2].i, b[2].i)
	}))

	reg("eval-family-surface", symTable([]colDef{
		nameCol(), qualCol(),
		num("evals", func(s *Sym) int32 { return s.NEval }),
		num("instance_evals", func(s *Sym) int32 { return s.NInstanceEval }),
		num("class_evals", func(s *Sym) int32 { return s.NClassEval }),
		num("define_methods", func(s *Sym) int32 { return s.NDefineMethod }),
		num("method_missing", func(s *Sym) int32 { return s.NMethodMissing }),
		num("sends", func(s *Sym) int32 { return s.NSend }),
		num("params_reads", func(s *Sym) int32 { return s.NParamsRead }),
		num("fan_in", func(s *Sym) int32 { return s.FanIn }),
		atCol(),
	}, func(s *Sym) bool {
		return s.NEval+s.NInstanceEval+s.NClassEval > 0
	}, func(a, b row) bool {
		return desc3(a[8].i, b[8].i, a[2].i, b[2].i, a[3].i+a[4].i, b[3].i+b[4].i)
	}))

	reg("shell-out-surface", symTable([]colDef{
		nameCol(), qualCol(),
		num("backticks", func(s *Sym) int32 { return s.NSubshell }),
		num("exec_calls", func(s *Sym) int32 { return s.NExec }),
		num("interpolations", func(s *Sym) int32 { return s.NStringInterp }),
		num("params_reads", func(s *Sym) int32 { return s.NParamsRead }),
		num("heredocs", func(s *Sym) int32 { return s.NHeredoc }),
		num("controller", func(s *Sym) int32 { return s.IsController }),
		num("job", func(s *Sym) int32 { return s.IsJob }),
		num("fan_in", func(s *Sym) int32 { return s.FanIn }),
		atCol(),
	}, func(s *Sym) bool {
		return s.NSubshell > 0 || s.NExec > 0
	}, func(a, b row) bool {
		return desc3(a[5].i, b[5].i, a[4].i, b[4].i, a[2].i+a[3].i, b[2].i+b[3].i)
	}))

	reg("dead-code", symTable([]colDef{
		nameCol(), kindCol(),
		num("sloc", func(s *Sym) int32 { return s.Sloc }),
		num("cyclo", func(s *Sym) int32 { return s.Cyclomatic }),
		num("ext_calls", func(s *Sym) int32 { return s.NExternalCalls }),
		atCol(),
	}, func(s *Sym) bool {
		if s.FanIn != 0 || s.IsPublic != 0 || s.IsTest != 0 || s.IsEntrypoint != 0 ||

			s.IsAbstract != 0 || !isCallableKind(s.Kind()) {
			return false
		}
		return s.Name() != "(anonymous)" && s.Name() != "<module>"
	}, func(a, b row) bool { return a[2].i > b[2].i }))

	reg("raw-sql-below-a-controller", func(g *Graph, mod func(string) bool, lim int) *result {
		var roots []int32
		for _, s := range g.Syms {
			if (s.IsController != 0 || s.IsEntrypoint != 0 || s.IsJob != 0) &&
				!g.fileIsTest(s.FileId) {
				roots = append(roots, s.Id)
			}
		}
		type key struct{ sym, entry int32 }
		hops := make(map[key]int32, 256)
		for _, rp := range reachPairs(g, roots, 4) {
			{
				root, sym, d := rp.Root, rp.Sym, rp.Hops
				s := g.Syms[sym-1]
				if d == 0 || (s.NRawSql == 0 && s.NConstantize == 0 &&
					s.NSystemCall == 0 && s.NHtmlSafe == 0) {
					continue
				}
				k := key{sym, root}
				if old, ok := hops[k]; !ok || d < old {
					hops[k] = d
				}
			}
		}
		res := &result{cols: []string{"name", "reached_from", "hops", "raw_sql",
			"constantize", "system_calls", "html_safe", "open_calls", "fan_in", "at"}}
		for _, k := range sortedPairs(hops) {
			h := hops[k]
			s := g.Syms[k.sym-1]
			if !okFile(g, s.FileId, mod) {
				continue
			}
			res.rows = append(res.rows, row{cs(s.Name()), cs(g.Syms[k.entry-1].Name()),
				ci32(h), ci32(s.NRawSql), ci32(s.NConstantize), ci32(s.NSystemCall),
				ci32(s.NHtmlSafe), ci32(s.NOpenCall), ci32(s.FanIn), symAt(g, s)})
		}
		return finish(res, func(a, b row) bool {
			if a[2].i != b[2].i {
				return a[2].i < b[2].i
			}
			return desc3(a[4].i, b[4].i, a[3].i, b[3].i, a[8].i, b[8].i)
		}, lim)
	})

	reg("write-per-iteration", func(g *Graph, mod func(string) bool, lim int) *result {
		callers := groupCallers(g)
		res := &result{cols: []string{"name", "writes_in_loop", "enum_in_loop",
			"count_in_loop", "serialize_in_loop", "loop_depth", "in_model",
			"in_job", "fan_in", "distinct_callers", "at"}}
		for _, s := range g.Syms {
			if s.NArWriteInLoop == 0 || !okFile(g, s.FileId, mod) {
				continue
			}
			res.rows = append(res.rows, row{cs(s.Name()), ci32(s.NArWriteInLoop),
				ci32(s.NEnumInLoop), ci32(s.NCountInLoop), ci32(s.NSerializeInLoop),
				ci32(s.MaxLoopDepth), ci32(s.IsModel), ci32(s.IsJob), ci32(s.FanIn),
				ci32(int32(len(callers[s.Id]))), symAt(g, s)})
		}
		return finish(res, func(a, b row) bool {
			return desc3(a[1].i, b[1].i, a[5].i, b[5].i, a[9].i, b[9].i)
		}, lim)
	})

	reg("open-injection", symTable([]colDef{
		nameCol(),
		num("open_calls", func(s *Sym) int32 { return s.NOpenCall }),
		num("system_calls", func(s *Sym) int32 { return s.NSystemCall }),
		num("eval_calls", func(s *Sym) int32 { return s.NEval }),
		num("fan_in", func(s *Sym) int32 { return s.FanIn }),
		atCol(),
	}, func(s *Sym) bool { return s.NOpenCall > 0 },
		func(a, b row) bool { return desc2(a[4].i, b[4].i, a[1].i, b[1].i) }))

	reg("send-injection", symTable([]colDef{
		nameCol(),
		num("send_calls", func(s *Sym) int32 { return s.NSend }),
		num("define_methods", func(s *Sym) int32 { return s.NDefineMethod }),
		num("method_missing", func(s *Sym) int32 { return s.NMethodMissing }),
		num("const_gets", func(s *Sym) int32 { return s.NConstGet }),
		num("metaprogram_total", func(s *Sym) int32 { return s.NMetaprogramTotal }),
		num("fan_in", func(s *Sym) int32 { return s.FanIn }),
		num("cyclo", func(s *Sym) int32 { return s.Cyclomatic }),
		atCol(),
	}, func(s *Sym) bool { return s.NSend > 0 },
		func(a, b row) bool { return desc2(a[6].i, b[6].i, a[1].i, b[1].i) }))

	reg("constantize-injection", symTable([]colDef{
		nameCol(),
		num("constantize_calls", func(s *Sym) int32 { return s.NConstantize }),
		num("const_gets", func(s *Sym) int32 { return s.NConstGet }),
		num("dynamic_metaprogram", func(s *Sym) int32 { return s.NMetaprogramDynamic }),
		num("fan_in", func(s *Sym) int32 { return s.FanIn }),
		atCol(),
	}, func(s *Sym) bool { return s.NConstantize > 0 },
		func(a, b row) bool { return desc2(a[4].i, b[4].i, a[1].i, b[1].i) }))

	reg("string-concat-in-loop", symTable([]colDef{
		nameCol(),
		num("str_lit_in_loop", func(s *Sym) int32 { return s.NStrLitInLoop }),
		num("string_interp", func(s *Sym) int32 { return s.NStringInterp }),

		num("concat_in_loop", func(s *Sym) int32 { return 0 }),
		num("loops", func(s *Sym) int32 { return s.NLoops }),
		num("cyclo", func(s *Sym) int32 { return s.Cyclomatic }),
		num("fan_in", func(s *Sym) int32 { return s.FanIn }),
		atCol(),
	}, func(s *Sym) bool { return false },
		func(a, b row) bool { return desc2(a[3].i, b[3].i, a[2].i, b[2].i) }))

	reg("weak-hash", symTable([]colDef{
		nameCol(),
		num("weak_hashs", func(s *Sym) int32 { return s.NWeakHash }),
		num("weak_randoms", func(s *Sym) int32 { return s.NWeakRandom }),
		num("fan_in", func(s *Sym) int32 { return s.FanIn }),
		atCol(),
	}, func(s *Sym) bool { return s.NWeakHash+s.NWeakRandom > 0 },
		func(a, b row) bool { return desc2(a[3].i, b[3].i, a[1].i+a[2].i, b[1].i+b[2].i) }))

	reg("html-safe-xss", symTable([]colDef{
		nameCol(),
		num("html_safe_calls", func(s *Sym) int32 { return s.NHtmlSafe }),
		num("raw_sql", func(s *Sym) int32 { return s.NRawSql }),
		num("params_reads", func(s *Sym) int32 { return s.NParamsRead }),
		num("fan_in", func(s *Sym) int32 { return s.FanIn }),
		atCol(),
	}, func(s *Sym) bool { return s.NHtmlSafe > 0 },
		func(a, b row) bool { return desc2(a[4].i, b[4].i, a[1].i, b[1].i) }))

	reg("sql-injection-ar", symTable([]colDef{
		nameCol(),
		num("sql_interp", func(s *Sym) int32 { return s.NSqlInterp }),
		num("sql_literal", func(s *Sym) int32 { return s.NSqlLiteral }),
		num("sql_sanitized", func(s *Sym) int32 { return s.NSqlSanitized }),
		num("ar_queries", func(s *Sym) int32 { return s.NArQuery }),
		num("fan_in", func(s *Sym) int32 { return s.FanIn }),
		atCol(),
	}, func(s *Sym) bool { return s.NSqlInterp > 0 },
		func(a, b row) bool { return desc2(a[5].i, b[5].i, a[1].i, b[1].i) }))

	reg("eval-injection", symTable([]colDef{
		nameCol(),
		num("eval_calls", func(s *Sym) int32 { return s.NEval }),
		num("send_calls", func(s *Sym) int32 { return s.NSend }),
		num("constantize_calls", func(s *Sym) int32 { return s.NConstantize }),
		num("fan_in", func(s *Sym) int32 { return s.FanIn }),
		atCol(),
	}, func(s *Sym) bool { return s.NEval > 0 },
		func(a, b row) bool { return desc2(a[4].i, b[4].i, a[1].i, b[1].i) }))

	reg("mass-assignment-weak-params", symTable([]colDef{
		nameCol(),
		num("params_reads", func(s *Sym) int32 { return s.NParamsRead }),
		num("permits", func(s *Sym) int32 { return s.NPermit }),
		num("permit_bangs", func(s *Sym) int32 { return s.NPermitBang }),
		num("mass_assigns", func(s *Sym) int32 { return s.NMassAssign }),
		num("fan_in", func(s *Sym) int32 { return s.FanIn }),
		atCol(),
	}, func(s *Sym) bool { return s.NMassAssign > 0 && s.NPermit == 0 },
		func(a, b row) bool { return desc2(a[5].i, b[5].i, a[4].i, b[4].i) }))

	reg("import-cycle", func(g *Graph, mod func(string) bool, lim int) *result {

		importsByFile := make(map[int32][]int32, 512)
		for i := range g.Imps {
			im := &g.Imps[i]
			if im.HasTargetID && im.External == 0 {
				importsByFile[im.FileID] = append(importsByFile[im.FileID], im.TargetID)
			}
		}
		res := &result{cols: []string{"path", "shortest_cycle", "at"}}
		for _, f := range g.Files {
			if f.IsTest != 0 || !mod(g.modNameOf(f.ModuleID)) {
				continue
			}
			best := int32(0)
			seen := map[int32]bool{f.ID: true}
			frontier := []int32{f.ID}
			for d := int32(1); d <= 8 && len(frontier) > 0 && best == 0; d++ {
				var next []int32
				for _, cur := range frontier {
					for _, t := range importsByFile[cur] {
						if t == f.ID {
							best = d
							break
						}
						if !seen[t] {
							seen[t] = true
							next = append(next, t)
						}
					}
					if best > 0 {
						break
					}
				}
				frontier = next
			}
			if best > 0 {
				res.rows = append(res.rows, row{cs(f.Path()), ci32(best),
					cs(f.Path() + ":0")})
			}
		}
		return finish(res, func(a, b row) bool { return a[1].i < b[1].i }, lim)
	})

	reg("thread-coupling", symTable([]colDef{
		nameCol(),
		num("thread_news", func(s *Sym) int32 { return s.NThreadNew }),
		num("ractor_news", func(s *Sym) int32 { return s.NRactor }),
		num("mutexes", func(s *Sym) int32 { return s.NMutex }),
		num("timeouts", func(s *Sym) int32 { return s.NTimeout }),
		num("fan_in", func(s *Sym) int32 { return s.FanIn }),
		num("cyclo", func(s *Sym) int32 { return s.Cyclomatic }),
		atCol(),
	}, func(s *Sym) bool { return s.NThreadNew+s.NRactor > 0 },
		func(a, b row) bool {
			return desc2(a[5].i, b[5].i, a[1].i+a[2].i, b[1].i+b[2].i)
		}))

	reg("monkey-patch-surface", symTable([]colDef{
		nameCol(),
		num("monkey_patches", func(s *Sym) int32 { return s.NMonkeyPatch }),
		num("mixins", func(s *Sym) int32 { return s.NMixins }),
		num("define_methods", func(s *Sym) int32 { return s.NDefineMethod }),
		num("method_missing", func(s *Sym) int32 { return s.NMethodMissing }),
		num("aliases", func(s *Sym) int32 { return s.NAlias }),
		num("fan_in", func(s *Sym) int32 { return s.FanIn }),
		atCol(),
	}, func(s *Sym) bool {
		return s.NMonkeyPatch+s.NMixins+s.NDefineMethod > 0
	}, func(a, b row) bool {
		return desc2(a[6].i, b[6].i, a[1].i+a[2].i, b[1].i+b[2].i)
	}))

	reg("ancestor-chain-depth", func(g *Graph, mod func(string) bool, lim int) *result {
		type link struct {
			klass, parent string
			depth         int32
		}
		byName := make(map[string][]*RubyModule, 256)
		present := make(map[string]bool, 256)
		for i := range g.RMods {
			r := &g.RMods[i]
			byName[r.Name()] = append(byName[r.Name()], r)
			if inMod(g, r.FileID, mod) {
				present[r.Name()] = true
			}
		}
		seen := make(map[link]bool, 1024)
		work := make([]link, 0, 512)
		for i := range g.RMods {
			if g.RMods[i].Superclass() != "" {
				work = append(work, link{g.RMods[i].Name(), g.RMods[i].Superclass(), 1})
			}
		}

		out := make(map[string]*[2]int32, 256)
		order := make([]string, 0, 256)
		for len(work) > 0 {
			l := work[len(work)-1]
			work = work[:len(work)-1]
			if seen[l] {
				continue
			}
			seen[l] = true
			a := out[l.klass]
			if a == nil {
				a = &[2]int32{}
				out[l.klass] = a
				order = append(order, l.klass)
			}
			if l.depth > a[0] {
				a[0] = l.depth
			}
			if l.depth > 0 {
				a[1]++
			}
			if l.depth >= 8 {
				continue
			}
			for _, m2 := range byName[l.parent] {
				if m2.Superclass() == "" || m2.Name() == l.klass {
					continue
				}
				work = append(work, link{l.klass, m2.Superclass(), l.depth + 1})
			}
		}

		parents := make(map[string]map[string]bool, 256)
		for l := range seen {
			if parents[l.klass] == nil {
				parents[l.klass] = map[string]bool{}
			}
			parents[l.klass][l.parent] = true
		}
		res := &result{cols: []string{"klass", "depth", "distinct_ancestors"}}
		sort.Strings(order)
		for _, k := range order {
			if !present[k] {
				continue
			}
			res.rows = append(res.rows, row{cs(k), ci32(out[k][0]),
				ci32(int32(len(parents[k])))})
		}
		return finish(res, func(a, b row) bool {
			return desc2(a[1].i, b[1].i, a[2].i, b[2].i)
		}, lim)
	})

	reg("yield-hubs", symTable([]colDef{
		nameCol(), kindCol(),
		num("yields", func(s *Sym) int32 { return s.NYield }),
		num("blocks", func(s *Sym) int32 { return s.NBlocks }),
		num("depth", func(s *Sym) int32 { return s.MaxLoopDepth }),
		num("fan_in", func(s *Sym) int32 { return s.FanIn }),
		num("n_calls", func(s *Sym) int32 { return s.NCalls }),
		num("sloc", func(s *Sym) int32 { return s.Sloc }),
		atCol(),
	}, func(s *Sym) bool { return s.NYield > 0 },
		func(a, b row) bool { return desc2(a[2].i, b[2].i, a[5].i, b[5].i) }))

	reg("attr-coupling", symTable([]colDef{
		nameCol(),
		num("accessors", func(s *Sym) int32 { return s.NAttrAccessor }),
		num("readers", func(s *Sym) int32 { return s.NAttrReader }),
		num("writers", func(s *Sym) int32 { return s.NAttrWriter }),
		{"total_attrs", func(_ *Graph, s *Sym) cell {
			return ci32(s.NAttrAccessor + s.NAttrReader + s.NAttrWriter)
		}},
		num("sloc", func(s *Sym) int32 { return s.Sloc }),
		num("fan_in", func(s *Sym) int32 { return s.FanIn }),
		atCol(),
	}, func(s *Sym) bool {
		return s.NAttrAccessor+s.NAttrReader+s.NAttrWriter > 0
	}, func(a, b row) bool { return desc2(a[4].i, b[4].i, a[6].i, b[6].i) }))

	reg("heavy-mixins", func(g *Graph, mod func(string) bool, lim int) *result {
		type agg struct {
			prep, ext map[string]bool
			hosts     map[string]bool
			via       map[string]bool
			at, fid   int32
		}
		groups := make(map[string]*agg, 256)
		for i := range g.Mixins {
			m := &g.Mixins[i]
			if !inMod(g, m.FileID, mod) {
				continue
			}
			a := groups[m.MixinShort()]
			if a == nil {
				a = &agg{via: map[string]bool{}, hosts: map[string]bool{},
					prep: map[string]bool{}, ext: map[string]bool{},
					at: m.Line, fid: m.FileID}
				groups[m.MixinShort()] = a
			}
			a.hosts[m.Host()] = true

			if m.Kind() == "prepend" {
				a.prep[m.Host()] = true
			}
			if m.Kind() == "extend" {
				a.ext[m.Host()] = true
			}
			a.via[m.Kind()] = true
			if m.Line < a.at {
				a.at, a.fid = m.Line, m.FileID
			}
		}
		res := &result{cols: []string{"mixin_", "hosts", "prepended_by",
			"extended_by", "via", "at_any"}}
		for _, name := range sortedKeys(groups) {
			a := groups[name]
			res.rows = append(res.rows, row{cs(name), ci32(int32(len(a.hosts))),
				ci32(int32(len(a.prep))), ci32(int32(len(a.ext))),
				joinKinds(a.via), cs(g.at(a.fid, a.at))})
		}
		return finish(res, func(a, b row) bool {
			return desc2(a[1].i, b[1].i, a[2].i, b[2].i)
		}, lim)
	})

	reg("super-overrides", symTable([]colDef{
		nameCol(),
		num("supers", func(s *Sym) int32 { return s.NSuper }),
		num("params", func(s *Sym) int32 { return s.NParams }),
		num("cyclo", func(s *Sym) int32 { return s.Cyclomatic }),
		num("fan_in", func(s *Sym) int32 { return s.FanIn }),
		atCol(),
	}, func(s *Sym) bool { return s.NSuper > 0 && s.Kind() == "method" },
		func(a, b row) bool { return desc2(a[1].i, b[1].i, a[4].i, b[4].i) }))

	reg("unused-private", symTable([]colDef{
		nameCol(),
		strc("visibility", func(s *Sym) string { return s.Visibility() }),
		num("calls", func(s *Sym) int32 { return s.NCalls }),
		num("cyclo", func(s *Sym) int32 { return s.Cyclomatic }),
		num("sloc", func(s *Sym) int32 { return s.Sloc }),
		atCol(),
	}, func(s *Sym) bool {
		return s.Kind() == "method" && s.IsPublic == 0 && s.FanIn == 0 &&
			(s.Visibility() == "private" || s.Visibility() == "protected")
	}, func(a, b row) bool { return a[4].i > b[4].i }))

	reg("nested-iterators", func(g *Graph, mod func(string) bool, lim int) *result {
		type agg struct {
			sym      *Sym
			n, depth int32
			queries  int32
		}
		groups := make(map[int32]*agg, 512)
		var order []int32
		for i := range g.Blks {
			b := &g.Blks[i]
			if b.IsIteration == 0 || b.Depth < 2 || g.fileIsGenerated(b.FileID) ||
				!okFile(g, b.FileID, mod) {
				continue
			}
			a := groups[b.SymID]
			if a == nil {
				a = &agg{sym: g.Syms[b.SymID-1]}
				groups[b.SymID] = a
				order = append(order, b.SymID)
			}
			a.n++
			if b.Depth > a.depth {
				a.depth = b.Depth
			}
			a.queries += b.NQueries
		}
		res := &result{cols: []string{"path", "name", "nested_iters", "max_depth",
			"queries_inside"}}
		for _, id := range order {
			a := groups[id]
			res.rows = append(res.rows, row{cs(g.Files[a.sym.FileId-1].Path()),
				cs(a.sym.Name()), ci32(a.n), ci32(a.depth), ci32(a.queries)})
		}
		return finish(res, func(a, b row) bool {
			return desc2(a[4].i, b[4].i, a[2].i, b[2].i)
		}, lim)
	})

	reg("feature-envy", func(g *Graph, mod func(string) bool, lim int) *result {
		type agg struct {
			sym           *Sym
			foreign, self int32
		}
		groups := make(map[int32]*agg, 4096)
		for i := range g.Edges {
			e := &g.Edges[i]
			a := groups[e.Caller]
			if a == nil {
				a = &agg{sym: g.Syms[e.Caller-1]}
				groups[e.Caller] = a
			}
			if e.Self == 0 {
				a.foreign += e.NCalls
			} else {
				a.self += e.NCalls
			}
		}
		res := &result{cols: []string{"name", "path", "foreign_calls", "self_calls"}}
		ids := sortedIDs(groups)
		for i := len(ids) - 1; i >= 0; i-- {
			a := groups[ids[i]]
			if !okFile(g, a.sym.FileId, mod) {
				continue
			}
			if a.foreign < 5 || a.foreign <= 2*a.self {
				continue
			}
			res.rows = append(res.rows, row{cs(a.sym.Name()),
				cs(g.Files[a.sym.FileId-1].Path()), ci32(a.foreign), ci32(a.self)})
		}
		return finish(res, func(a, b row) bool { return a[2].i > b[2].i }, lim)
	})

	reg("debugger-surface", func(g *Graph, mod func(string) bool, lim int) *result {
		want := map[string]bool{"binding.pry": true, "byebug": true,
			"debugger": true, "binding.irb": true}
		res := &result{cols: []string{"path", "name", "debugger", "n", "first_line",
			"fan_in"}}
		for i := range g.Unres {
			u := &g.Unres[i]
			if !want[u.Name()] || u.Caller == 0 || int(u.Caller) > len(g.Syms) {
				continue
			}
			s := g.Syms[u.Caller-1]
			if g.fileIsGenerated(s.FileId) || !okFile(g, s.FileId, mod) {
				continue
			}
			res.rows = append(res.rows, row{cs(g.Files[s.FileId-1].Path()),
				cs(s.Name()), cs(u.Name()), ci32(u.N), ci32(u.FirstLine),
				ci32(s.FanIn)})
		}
		return finish(res, func(a, b row) bool {
			return desc2(a[5].i, b[5].i, a[3].i, b[3].i)
		}, lim)
	})

	reg("unscoped-find-params", func(g *Graph, mod func(string) bool, lim int) *result {
		want := map[string]bool{"find": true, "find_by": true, "find_by!": true,
			"first": true, "last": true, "take": true, "where": true}
		res := &result{cols: []string{"path", "name", "model", "api", "build_kind", "line"}}
		for i := range g.ARQs {
			q := &g.ARQs[i]
			if q.FromParams == 0 || !want[q.API()] || q.SymID == 0 ||
				int(q.SymID) > len(g.Syms) || g.fileIsGenerated(q.FileID) ||
				!okFile(g, q.FileID, mod) {
				continue
			}
			s := g.Syms[q.SymID-1]
			if !mod(g.modNameOf(s.ModuleId)) {
				continue
			}
			res.rows = append(res.rows, row{cs(g.Files[q.FileID-1].Path()),
				cs(s.Name()), cs(q.Model()), cs(q.API()), cs(q.BuildKind()), ci32(q.Line)})
		}
		return finish(res, func(a, b row) bool {
			if a[3].s != b[3].s {
				return a[3].s < b[3].s
			}
			return a[5].i < b[5].i
		}, lim)
	})

	_ = strings.TrimSpace
}

func maxi(a, b int32) int32 {
	if a > b {
		return a
	}
	return b
}

func mini(a, b int32) int32 {
	if a < b {
		return a
	}
	return b
}

func joinSorted(m map[string]bool) string {
	out := make([]string, 0, len(m))
	for k := range m {
		out = append(out, k)
	}
	sort.Strings(out)
	return strings.Join(out, ",")
}

func init() {
	reg := func(name string, f func(*Graph, func(string) bool, int) *result) {
		questionRuns[name] = f
	}

	inputCoOccurrence := func(sink func(*Sym) int32, cols []string) func(*Graph, func(string) bool, int) *result {
		return func(g *Graph, mod func(string) bool, lim int) *result {
			ui := groupInpSites(g)
			res := &result{cols: append([]string{}, cols...)}
			for _, s := range g.Syms {
				if sink(s) == 0 || !okFile(g, s.FileId, mod) {
					continue
				}
				var n int32
				kinds := map[string]bool{}
				for _, u := range ui[s.Id] {
					n++
					kinds[u.Kind()] = true
				}
				if n == 0 {
					continue
				}
				r := row{cs(s.Name()), ci32(sink(s)), ci32(n), joinKinds(kinds), symAt(g, s)}
				res.rows = append(res.rows, r)
			}
			return finish(res, func(a, b row) bool {
				return desc2(a[len(a)-3].i, b[len(b)-3].i, a[1].i, b[1].i)
			}, lim)
		}
	}

	reg("open-redirect-surface", inputCoOccurrence(
		func(s *Sym) int32 { return s.NRedirect },
		[]string{"name", "redirect_calls", "input_sites", "kinds", "at"}))

	reg("ssrf-fetch-surface", inputCoOccurrence(
		func(s *Sym) int32 { return s.NFetch },
		[]string{"name", "fetch_calls", "input_sites", "kinds", "at"}))

	reg("path-traversal-surface", inputCoOccurrence(
		func(s *Sym) int32 { return s.NDynamicOpen },
		[]string{"name", "open_sites", "input_sites", "kinds", "at"}))

	reg("log-injection-surface", inputCoOccurrence(
		func(s *Sym) int32 { return s.NLogCall },
		[]string{"name", "log_calls", "input_sites", "kinds", "at"}))

	reg("hardcoded-secret-candidates", func(g *Graph, mod func(string) bool, lim int) *result {
		res := &result{cols: []string{"name", "candidate", "line", "at"}}
		for i := range g.Secs {
			s := &g.Secs[i]
			if g.fileIsGenerated(s.FileID) || !okFile(g, s.FileID, mod) ||
				s.SymID == 0 || int(s.SymID) > len(g.Syms) {
				continue
			}

			if strings.HasPrefix(s.Value(), "/") || strings.ContainsAny(s.Value(), "|%") {
				continue
			}
			res.rows = append(res.rows, row{cs(g.Syms[s.SymID-1].Name()),
				cs(s.Value()), ci32(s.Line), cs(g.at(s.FileID, s.Line))})
		}
		return finish(res, func(a, b row) bool {
			return int64(len(a[1].s)) > int64(len(b[1].s))
		}, lim)
	})

	reg("xxe-parser-surface", symTable([]colDef{
		nameCol(),
		num("xml_parsers", func(s *Sym) int32 { return s.NXxeParser }),
		num("sloc", func(s *Sym) int32 { return s.Sloc }),
		atCol(),
	}, func(s *Sym) bool { return s.NXxeParser > 0 },
		func(a, b row) bool { return desc2(a[1].i, b[1].i, a[2].i, b[2].i) }))

	reg("zip-slip-surface", symTable([]colDef{
		nameCol(),
		num("zip_access", func(s *Sym) int32 { return s.NZipRead }),
		num("sloc", func(s *Sym) int32 { return s.Sloc }),
		atCol(),
	}, func(s *Sym) bool { return s.NZipRead > 0 },
		func(a, b row) bool { return desc2(a[1].i, b[1].i, a[2].i, b[2].i) }))

	reg("unauthenticated-input-surface", func(g *Graph, mod func(string) bool, lim int) *result {
		ui := groupInpSites(g)
		type ent struct {
			s     *Sym
			n     int32
			kinds map[string]bool
		}
		var es []ent
		for _, s := range g.Syms {
			if s.NAuthCall != 0 || !okFile(g, s.FileId, mod) {
				continue
			}
			us := ui[s.Id]
			if len(us) == 0 {
				continue
			}
			kinds := make(map[string]bool, 4)
			for _, u := range us {
				kinds[u.Kind()] = true
			}
			es = append(es, ent{s: s, n: int32(len(us)), kinds: kinds})
		}
		sort.SliceStable(es, func(i, j int) bool {
			if es[i].n != es[j].n {
				return es[i].n > es[j].n
			}
			if es[i].s.Sloc != es[j].s.Sloc {
				return es[i].s.Sloc > es[j].s.Sloc
			}
			return es[i].s.Id < es[j].s.Id
		})
		res := &result{cols: []string{"name", "input_sites", "kinds", "at"}}
		for _, e := range es {
			res.rows = append(res.rows, row{cs(e.s.Name()), ci32(e.n),
				joinKinds(e.kinds), symAt(g, e.s)})
		}
		return finish(res, func(a, b row) bool { return false }, lim)
	})

	reg("find-each-missed", func(g *Graph, mod func(string) bool, lim int) *result {
		res := &result{cols: []string{"path", "name", "receiver", "line", "n_queries", "fan_in"}}
		for i := range g.Blks {
			b := &g.Blks[i]
			if b.IsIteration == 0 || !strings.Contains(b.Receiver(), ".all") ||
				b.NQueries == 0 || g.fileIsGenerated(b.FileID) ||
				!okFile(g, b.FileID, mod) || b.SymID == 0 || int(b.SymID) > len(g.Syms) {
				continue
			}
			s := g.Syms[b.SymID-1]
			if !mod(g.modNameOf(s.ModuleId)) {
				continue
			}
			res.rows = append(res.rows, row{cs(g.Files[b.FileID-1].Path()), cs(s.Name()),
				cs(b.Receiver()), ci32(b.Line), ci32(b.NQueries), ci32(s.FanIn)})
		}
		return finish(res, func(a, b row) bool { return desc2(a[4].i, b[4].i, a[5].i, b[5].i) }, lim)
	})

	reg("unsafe-deserialization", func(g *Graph, mod func(string) bool, lim int) *result {
		res := &result{cols: []string{"path", "name", "api", "sites", "first_line", "fan_in"}}
		var hs []*Hazard
		for i := range g.Haz {
			h := &g.Haz[i]
			if h.Category() != "deserialize" || h.SymID == 0 || int(h.SymID) > len(g.Syms) {
				continue
			}
			s := g.Syms[h.SymID-1]
			if g.fileIsGenerated(s.FileId) || !okFile(g, s.FileId, mod) {
				continue
			}
			hs = append(hs, h)
		}
		sort.Slice(hs, func(i, j int) bool {
			if hs[i].SymID != hs[j].SymID {
				return hs[i].SymID < hs[j].SymID
			}
			return hs[i].Pattern() < hs[j].Pattern()
		})
		for _, h := range hs {
			s := g.Syms[h.SymID-1]
			res.rows = append(res.rows, row{cs(g.Files[s.FileId-1].Path()), cs(s.Name()),
				cs(h.Pattern()), ci32(h.N), ci32(h.FirstLine), ci32(s.FanIn)})
		}
		return finish(res, func(a, b row) bool { return desc2(a[5].i, b[5].i, a[3].i, b[3].i) }, lim)
	})

	reg("save-without-bang", func(g *Graph, mod func(string) bool, lim int) *result {
		res := &result{cols: []string{"path", "name", "ignored_saves", "writes", "fan_in"}}
		for _, s := range g.Syms {
			if s.NSaveIgnored == 0 || !okFile(g, s.FileId, mod) {
				continue
			}
			res.rows = append(res.rows, row{cs(g.Files[s.FileId-1].Path()), cs(s.Name()),
				ci32(s.NSaveIgnored), ci32(s.NArWrite), ci32(s.FanIn)})
		}
		return finish(res, func(a, b row) bool { return desc2(a[2].i, b[2].i, a[4].i, b[4].i) }, lim)
	})

	reg("legacy-enumerable-idioms", func(g *Graph, mod func(string) bool, lim int) *result {
		res := &result{cols: []string{"path", "name", "legacy_chains", "queries", "fan_in"}}
		for _, s := range g.Syms {
			if s.NLegacyChain == 0 || !okFile(g, s.FileId, mod) {
				continue
			}
			res.rows = append(res.rows, row{cs(g.Files[s.FileId-1].Path()), cs(s.Name()),
				ci32(s.NLegacyChain), ci32(s.NArQuery), ci32(s.FanIn)})
		}
		return finish(res, func(a, b row) bool { return desc2(a[2].i, b[2].i, a[4].i, b[4].i) }, lim)
	})

	reg("param-clumps", func(g *Graph, mod func(string) bool, lim int) *result {

		bySym := make(map[int32][]string, 4096)
		for i := range g.Params {
			p := &g.Params[i]
			bySym[p.SymID] = append(bySym[p.SymID], p.Name())
		}
		type agg struct {
			n     int32
			files map[int32]bool
		}
		groups := make(map[string]*agg, 256)
		for i := range g.Syms {
			s := g.Syms[i]
			if s.Kind() != "method" || !okFile(g, s.FileId, mod) {
				continue
			}
			names := bySym[s.Id]
			if len(names) < 3 {
				continue
			}
			key := strings.Join(names, ",")
			a := groups[key]
			if a == nil {
				a = &agg{files: map[int32]bool{}}
				groups[key] = a
			}
			a.n++
			a.files[s.FileId] = true
		}
		res := &result{cols: []string{"names", "n_methods", "n_files"}}
		for _, key := range sortedKeys(groups) {
			a := groups[key]
			if a.n < 3 {
				continue
			}
			res.rows = append(res.rows, row{cs(key), ci32(a.n),
				ci32(int32(len(a.files)))})
		}
		return finish(res, func(a, b row) bool { return desc2(a[1].i, b[1].i, a[2].i, b[2].i) }, lim)
	})

	reg("typing-coverage", func(g *Graph, mod func(string) bool, lim int) *result {
		sigsInFile := make(map[int32]int32, 512)
		for _, s := range g.Syms {
			if s.Kind() == "method" && s.HasSig != 0 {
				sigsInFile[s.FileId]++
			}
		}
		res := &result{cols: []string{"path", "name", "sigs_in_file", "fan_in", "sloc"}}
		for _, s := range g.Syms {
			if s.Kind() != "method" || s.HasSig != 0 || s.IsPublic != 1 ||
				sigsInFile[s.FileId] == 0 || g.fileIsGenerated(s.FileId) ||
				!okFile(g, s.FileId, mod) {
				continue
			}
			res.rows = append(res.rows, row{cs(g.Files[s.FileId-1].Path()), cs(s.Name()),
				ci32(sigsInFile[s.FileId]), ci32(s.FanIn), ci32(s.Sloc)})
		}
		return finish(res, func(a, b row) bool { return desc2(a[2].i, b[2].i, a[4].i, b[4].i) }, lim)
	})

	reg("transaction-exit-statement", func(g *Graph, mod func(string) bool, lim int) *result {
		res := &result{cols: []string{"in_method", "module_", "block_api", "exits",
			"block_depth", "queries_in_block", "in_iterator", "body_sloc",
			"cyclo", "ar_writes", "fan_in", "at"}}
		for i := range g.Blks {
			b := &g.Blks[i]
			if (b.Method() != "transaction" && b.Method() != "with_lock") || b.NExits == 0 ||
				b.SymID == 0 || int(b.SymID) > len(g.Syms) || !okFile(g, b.FileID, mod) {
				continue
			}
			s := g.Syms[b.SymID-1]
			res.rows = append(res.rows, row{cs(s.Name()), cs(g.modNameOf(s.ModuleId)),
				cs(b.Method()), ci32(b.NExits), ci32(b.Depth), ci32(b.NQueries),
				ci32(b.IsIteration), ci32(b.BodySloc), ci32(s.Cyclomatic),
				ci32(s.NArWrite), ci32(s.FanIn), cs(g.at(b.FileID, b.Line))})
		}
		return finish(res, func(a, b row) bool {
			return desc3(a[3].i, b[3].i, a[10].i, b[10].i, a[5].i, b[5].i)
		}, lim)
	})

	reg("validation-skip-reachable", func(g *Graph, mod func(string) bool, lim int) *result {
		skips := map[string]bool{"update_attribute": true, "update_column": true,
			"update_columns": true, "increment!": true, "decrement!": true,
			"toggle!": true, "update_counters": true, "increment_counter": true,
			"decrement_counter": true}
		unres := groupUnres(g)
		var roots []int32
		for _, s := range g.Syms {
			if s.NParamsRead > 0 && s.Kind() == "method" {
				roots = append(roots, s.Id)
			}
		}
		type key struct{ src, sym int32 }
		groups := make(map[key]*sinkGroup, 256)
		for _, rp := range reachPairs(g, roots, 4) {
			apis := map[string]bool{}
			var sites int32
			for _, u := range unres[rp.Sym] {
				base := u.Name()
				if i := strings.IndexByte(base, '.'); i >= 0 {
					base = base[i+1:]
				}
				if skips[base] {
					apis[base] = true
					sites += u.N
				}
			}
			if len(apis) == 0 {
				continue
			}
			s := g.Syms[rp.Sym-1]
			if !okFile(g, s.FileId, mod) {
				continue
			}
			k := key{rp.Root, rp.Sym}
			a := groups[k]
			if a == nil {
				a = &sinkGroup{kind: joinSorted(apis)}
				groups[k] = a
			} else {
				a.kind = joinSorted(apis)
			}
			if !a.ok {
				a.ok, a.sum.hops = true, rp.Hops
			} else {
				a.sum.hops = mini(a.sum.hops, rp.Hops)
			}
			a.sum.sites += sites
		}
		res := &result{cols: []string{"reads_params", "skips_validations",
			"skipped_apis", "sites", "hops", "in_model", "fan_in", "at"}}
		for _, k := range sortedPairs2(groups) {
			a := groups[k]
			s := g.Syms[k.sym-1]
			res.rows = append(res.rows, row{cs(g.Syms[k.src-1].Name()), cs(s.Name()),
				cs(a.kind), ci32(a.sum.sites), ci32(a.sum.hops), ci32(s.IsModel),
				ci32(s.FanIn), symAt(g, s)})
		}
		return finish(res, func(a, b row) bool {
			if a[3].i != b[3].i {
				return a[3].i > b[3].i
			}
			if a[4].i != b[4].i {
				return a[4].i < b[4].i
			}
			return a[6].i > b[6].i
		}, lim)
	})

	reg("action-filter-unresolved", func(g *Graph, mod func(string) bool, lim int) *result {
		hooks := map[string]bool{"before_action": true, "after_action": true,
			"around_action": true, "prepend_before_action": true,
			"append_before_action": true, "prepend_around_action": true,
			"append_around_action": true, "before_filter": true,
			"after_filter": true, "around_filter": true}
		resolvedPerHost := make(map[string]int32, 256)
		for i := range g.ARCBs {
			if g.ARCBs[i].HasTargetID {
				resolvedPerHost[g.ARCBs[i].Host()]++
			}
		}
		res := &result{cols: []string{"host", "hook", "filter_target",
			"conditional", "resolved_siblings", "declared_in", "ctrl", "at"}}
		for i := range g.ARCBs {
			c := &g.ARCBs[i]
			if c.Method() == "" || c.HasTargetID || c.Block != 0 || !hooks[c.Hook()] ||
				c.SymID == 0 || int(c.SymID) > len(g.Syms) || !okFile(g, c.FileID, mod) {
				continue
			}
			s := g.Syms[c.SymID-1]
			res.rows = append(res.rows, row{cs(c.Host()), cs(c.Hook()), cs(c.Method()),
				ci32(c.Conditional), ci32(resolvedPerHost[c.Host()]), cs(s.Name()),
				ci32(s.IsController), cs(g.at(c.FileID, c.Line))})
		}
		return finish(res, func(a, b row) bool {
			ca, cb := int64(0), int64(0)
			if a[6].i != 0 {
				ca = 1
			}
			if b[6].i != 0 {
				cb = 1
			}
			if ca != cb {
				return ca > cb
			}
			if a[0].s != b[0].s {
				return a[0].s < b[0].s
			}
			return a[7].i < b[7].i
		}, lim)
	})

	reg("abstract-method-unimplemented", func(g *Graph, mod func(string) bool, lim int) *result {
		type abstract struct {
			meth string
			sloc int32
		}
		absMods := make(map[string][]abstract, 256)
		for _, s := range g.Syms {
			if s.Kind() != "method" || s.IsAbstract == 0 || s.ParentId == 0 {
				continue
			}
			m := g.Syms[s.ParentId-1]
			if m.Kind() != "module" && m.Kind() != "class" {
				continue
			}
			absMods[m.Name()] = append(absMods[m.Name()], abstract{s.Name(), s.Sloc})
		}
		ownNames := make(map[int32]map[string]bool, 1024)
		ownCount := make(map[int32]int32, 1024)
		for _, s := range g.Syms {
			if s.Kind() == "method" && s.ParentId != 0 {
				if ownNames[s.ParentId] == nil {
					ownNames[s.ParentId] = map[string]bool{}
				}
				ownNames[s.ParentId][s.Name()] = true
				ownCount[s.ParentId]++
			}
		}
		res := &result{cols: []string{"host", "mixed_in", "unimplemented",
			"mixin_kind", "stub_sloc", "own_methods", "at"}}
		type ent struct {
			row  row
			line int32
		}
		var es []ent
		for i := range g.Mixins {
			x := &g.Mixins[i]
			abs, ok := absMods[x.MixinShort()]
			if !ok || x.HostID == 0 || int(x.HostID) > len(g.Syms) {
				continue
			}
			h := g.Syms[x.HostID-1]
			if !okFile(g, h.FileId, mod) {
				continue
			}
			own := ownNames[x.HostID]

			for _, am := range abs {
				if own[am.meth] {
					continue
				}
				es = append(es, ent{row{cs(h.Name()), cs(x.MixinShort()),
					cs(am.meth), cs(x.Kind()), ci32(am.sloc),
					ci32(ownCount[x.HostID]), cs(g.at(x.FileID, x.Line))}, x.Line})
			}
		}
		sort.SliceStable(es, func(i, j int) bool {
			if es[i].row[4].i != es[j].row[4].i {
				return es[i].row[4].i > es[j].row[4].i
			}
			return es[i].line < es[j].line
		})
		for _, e := range es {
			res.rows = append(res.rows, e.row)
		}
		return finish(res, func(a, b row) bool { return false }, lim)
	})

	reg("method-missing-protocol", func(g *Graph, mod func(string) bool, lim int) *result {
		byParent := groupByParent(g)
		res := &result{cols: []string{"missing_def", "module_", "super_calls",
			"respond_to_defined", "send_calls", "cyclo", "sloc", "fan_in", "at"}}
		for _, s := range g.Syms {
			if s.Name() != "method_missing" || s.Kind() != "method" ||
				g.fileIsTest(s.FileId) || g.fileIsGenerated(s.FileId) ||
				!okFile(g, s.FileId, mod) {
				continue
			}
			var rt int32
			for _, sib := range byParent[s.ParentId] {
				if sib.Id == s.Id {
					continue
				}
				if sib.Name() == "respond_to_missing?" || sib.Name() == "respond_to?" {
					rt++
				}
			}
			res.rows = append(res.rows, row{cs(s.Name()), cs(g.modNameOf(s.ModuleId)),
				ci32(s.NSuper), ci32(rt), ci32(s.NSend), ci32(s.Cyclomatic),
				ci32(s.Sloc), ci32(s.FanIn), symAt(g, s)})
		}
		return finish(res, func(a, b row) bool {
			if a[2].i != b[2].i {
				return a[2].i < b[2].i
			}
			if a[3].i != b[3].i {
				return a[3].i < b[3].i
			}
			return a[7].i > b[7].i
		}, lim)
	})

	reg("duplicate-method-in-class", func(g *Graph, mod func(string) bool, lim int) *result {
		type key struct {
			par  int32
			name string
		}
		type agg struct {
			n, files, first, last int32
		}
		groups := make(map[key]*agg, 1024)
		seenFile := make(map[key]bool, 1024)
		for _, s := range g.Syms {
			if s.Kind() != "method" || s.ParentId == 0 || s.Name() == "(anonymous)" {
				continue
			}
			k := key{s.ParentId, s.Name()}
			a := groups[k]
			if a == nil {
				a = &agg{first: s.LineStart, last: s.LineStart}
				groups[k] = a
			}
			a.n++
			if !seenFile[k] {
				seenFile[k] = true
				a.files++
			}
			if s.LineStart < a.first {
				a.first = s.LineStart
			}
			if s.LineStart > a.last {
				a.last = s.LineStart
			}
		}
		res := &result{cols: []string{"owner", "method_", "n_defs", "n_files",
			"first_line", "last_line", "sloc", "fan_in", "at"}}
		for _, k := range sortedPairs2(groups) {
			a := groups[k]
			if a.n <= 1 {
				continue
			}
			h := g.Syms[k.par-1]
			if !okFile(g, h.FileId, mod) {
				continue
			}
			var o *Sym
			for _, s := range g.Syms {
				if s.ParentId == k.par && s.Name() == k.name && s.LineStart == a.first {
					o = s
					break
				}
			}
			sloc, fan := int32(0), int32(0)
			if o != nil {
				sloc, fan = o.Sloc, o.FanIn
			}
			res.rows = append(res.rows, row{cs(h.Name()), cs(k.name), ci32(a.n),
				ci32(a.files), ci32(a.first), ci32(a.last), ci32(sloc), ci32(fan),
				cs(g.at(h.FileId, a.first))})
		}
		return finish(res, func(a, b row) bool { return desc2(a[2].i, b[2].i, a[7].i, b[7].i) }, lim)
	})

	reg("class-reopened-across-files", func(g *Graph, mod func(string) bool, lim int) *result {
		type agg struct {
			n, files, defs, mixins, state, delegates, core, moduleDecls, at int32
			lastFile                                                        int32
		}
		groups := make(map[string]*agg, 1024)
		var order []string

		atFile := make(map[string]int32, 1024)
		atLine := make(map[string]int32, 1024)
		for i := range g.RMods {
			r := &g.RMods[i]

			if cur, ok := atLine[r.Name()]; !ok || r.Line < cur {
				atLine[r.Name()], atFile[r.Name()] = r.Line, r.FileID
			}
			if g.fileIsTest(r.FileID) || g.fileIsGenerated(r.FileID) {
				continue
			}
			a := groups[r.Name()]
			if a == nil {
				a = &agg{}
				groups[r.Name()] = a
				order = append(order, r.Name())
			}
			a.n++

			if r.FileID != a.lastFile {
				a.lastFile = r.FileID
				a.files++
			}
			a.defs += r.NDefs
			a.mixins += r.NMixins
			a.state += r.NClassVars + r.NClassIvars
			a.delegates += r.NDelegates
			a.core = maxi(a.core, r.ReopensCore)
			a.moduleDecls += r.IsModule
			if a.at == 0 || r.Line < a.at {
				a.at = r.Line
			}
		}
		res := &result{cols: []string{"name", "n_decls", "n_files", "total_defs",
			"total_mixins", "class_state", "total_delegates", "touches_core",
			"module_decls", "at"}}
		sort.Strings(order)
		for _, name := range order {
			a := groups[name]
			if a.files <= 1 {
				continue
			}

			fid := atFile[name]
			if !mod(g.modNameOf(g.Files[fid-1].ModuleID)) {
				continue
			}
			res.rows = append(res.rows, row{cs(name), ci32(a.n), ci32(a.files),
				ci32(a.defs), ci32(a.mixins), ci32(a.state), ci32(a.delegates),
				ci32(a.core), ci32(a.moduleDecls), cs(g.at(fid, a.at))})
		}
		return finish(res, func(a, b row) bool { return desc2(a[2].i, b[2].i, a[3].i, b[3].i) }, lim)
	})

	reg("inherit-exception-base", func(g *Graph, mod func(string) bool, lim int) *result {
		type agg struct {
			rescues, raises int32
		}
		byFile := make(map[int32]*agg, 512)
		for _, s := range g.Syms {
			if s.Kind() != "method" {
				continue
			}
			a := byFile[s.FileId]
			if a == nil {
				a = &agg{}
				byFile[s.FileId] = a
			}
			if s.NRescueException > 0 {
				a.rescues++
			}
			if s.NRaise > 0 {
				a.raises++
			}
		}
		res := &result{cols: []string{"exception_class", "inherits_from",
			"own_methods", "file_rescues_exception", "file_raises", "at"}}
		for i := range g.RMods {
			r := &g.RMods[i]
			if r.IsModule != 0 || (r.Superclass() != "Exception" &&
				r.Superclass() != "Object" && r.Superclass() != "BasicObject") {
				continue
			}
			if g.fileIsTest(r.FileID) || g.fileIsGenerated(r.FileID) ||
				!okFile(g, r.FileID, mod) {
				continue
			}
			a := byFile[r.FileID]
			res.rows = append(res.rows, row{cs(r.Name()), cs(r.Superclass()),
				ci32(r.NDefs), ci32(a.rescues), ci32(a.raises),
				cs(g.at(r.FileID, r.Line))})
		}
		return finish(res, func(a, b row) bool { return desc2(a[3].i, b[3].i, a[2].i, b[2].i) }, lim)
	})

	reg("n-plus-one-reachable", func(g *Graph, mod func(string) bool, lim int) *result {
		var roots []int32
		for _, s := range g.Syms {
			if s.IsController != 0 && s.IsPublic != 0 && s.Kind() == "method" &&
				!g.fileIsTest(s.FileId) {
				roots = append(roots, s.Id)
			}
		}
		type key struct{ entry, sym int32 }
		groups := make(map[key]*sinkGroup, 1024)
		for _, rp := range reachPairs(g, roots, 4) {
			if rp.Hops == 0 {
				continue
			}
			s := g.Syms[rp.Sym-1]
			if s.NArQueryInBlock == 0 && s.QueryInLoop == 0 {
				continue
			}
			if !okFile(g, s.FileId, mod) {
				continue
			}
			k := key{rp.Root, rp.Sym}
			a := groups[k]
			if a == nil {
				a = &sinkGroup{}
				groups[k] = a
			}
			if !a.ok {
				a.ok, a.sum.hops, a.sum.at = true, rp.Hops, s.LineStart
			} else {
				a.sum.hops = mini(a.sum.hops, rp.Hops)
				a.sum.at = mini(a.sum.at, s.LineStart)
			}
			a.sum.arInBlk = maxi(a.sum.arInBlk, s.NArQueryInBlock)
			a.sum.exec = maxi(a.sum.exec, s.QueryInLoop)
		}
		res := &result{cols: []string{"controller_action", "queries_in_loop",
			"hops", "ar_in_loops", "raw_in_loops", "writes_in_loops",
			"block_depth", "fan_in", "at"}}
		for _, k := range sortedPairs2(groups) {
			a := groups[k]
			s := g.Syms[k.sym-1]
			res.rows = append(res.rows, row{cs(g.Syms[k.entry-1].Name()), cs(s.Name()),
				ci32(a.sum.hops), ci32(a.sum.arInBlk), ci32(a.sum.exec),
				ci32(s.NArWriteInLoop), ci32(s.MaxBlockDepth), ci32(s.FanIn),
				cs(g.at(s.FileId, a.sum.at))})
		}
		return finish(res, func(a, b row) bool {
			if a[3].i != b[3].i {
				return a[3].i > b[3].i
			}
			if a[2].i != b[2].i {
				return a[2].i < b[2].i
			}
			return a[5].i > b[5].i
		}, lim)
	})

	reg("enqueue-in-loop", symTable([]colDef{
		strc("in_method", func(s *Sym) string { return s.Name() }), modCol(),
		num("enqueues_in_loop", func(s *Sym) int32 { return s.NEnqueueInLoop }),
		num("enqueues", func(s *Sym) int32 { return s.NEnqueue }),
		num("iter_blocks", func(s *Sym) int32 { return s.NIterBlocks }),
		num("block_depth", func(s *Sym) int32 { return s.MaxBlockDepth }),
		num("in_job", func(s *Sym) int32 { return s.IsJob }),
		num("fan_in", func(s *Sym) int32 { return s.FanIn }),
		atCol(),
	}, func(s *Sym) bool { return s.NEnqueueInLoop > 0 },
		func(a, b row) bool { return desc3(a[2].i, b[2].i, a[3].i, b[3].i, a[6].i, b[6].i) }))

	reg("mutex-held-across-io", symTable([]colDef{
		nameCol(), modCol(),
		num("mutexes", func(s *Sym) int32 { return s.NMutex }),
		num("io_", func(s *Sym) int32 { return s.NIo }),
		num("net_", func(s *Sym) int32 { return s.NNet }),
		num("db_", func(s *Sym) int32 { return s.NSql + s.NRailsQuery }),
		num("ar_calls", func(s *Sym) int32 { return s.NArQuery }),
		num("sleeps", func(s *Sym) int32 { return s.NSleepCall }),
		num("timeouts", func(s *Sym) int32 { return s.NTimeout }),
		num("lock_in_loop_", func(s *Sym) int32 { return s.LockInLoop }),
		num("fan_in", func(s *Sym) int32 { return s.FanIn }),
		atCol(),
	}, func(s *Sym) bool {
		return s.NMutex > 0 && s.NIo+s.NNet+s.NSql+s.NRailsQuery+s.NArQuery+s.NSleepCall > 0
	}, func(a, b row) bool {
		return desc2(a[3].i+a[4].i+a[5].i+a[6].i, b[3].i+b[4].i+b[5].i+b[6].i, a[10].i, b[10].i)
	}))

	reg("thread-new-without-join", symTable([]colDef{
		nameCol(), modCol(),
		num("threads_spawned", func(s *Sym) int32 { return s.NThreadNew }),
		num("ractors", func(s *Sym) int32 { return s.NRactor }),
		num("joins_seen", func(s *Sym) int32 { return s.NThreadJoin }),
		num("mutexes", func(s *Sym) int32 { return s.NMutex }),
		num("class_writes", func(s *Sym) int32 { return s.NClassLevelWrite }),
		num("fan_out", func(s *Sym) int32 { return s.FanOut }),
		num("fan_in", func(s *Sym) int32 { return s.FanIn }),
		atCol(),
	}, func(s *Sym) bool {
		return s.NThreadNew+s.NRactor > 0 && s.NThreadJoin == 0
	}, func(a, b row) bool { return desc2(a[2].i, b[2].i, a[8].i, b[8].i) }))

	reg("thread-current-reachable", func(g *Graph, mod func(string) bool, lim int) *result {
		var roots []int32
		for _, s := range g.Syms {
			if s.IsThreadedEntry != 0 {
				roots = append(roots, s.Id)
			}
		}
		type key struct{ entry, sym int32 }
		groups := make(map[key]*sinkGroup, 1024)
		for _, rp := range reachPairs(g, roots, 4) {
			s := g.Syms[rp.Sym-1]
			if s.NThreadLocal == 0 || !okFile(g, s.FileId, mod) {
				continue
			}
			k := key{rp.Root, rp.Sym}
			a := groups[k]
			if a == nil {
				a = &sinkGroup{}
				groups[k] = a
			}
			if !a.ok {
				a.ok, a.sum.hops, a.sum.at = true, rp.Hops, s.LineStart
			} else {
				a.sum.hops = mini(a.sum.hops, rp.Hops)
				a.sum.at = mini(a.sum.at, s.LineStart)
			}
			a.sum.open = maxi(a.sum.open, s.NThreadLocal)
		}
		res := &result{cols: []string{"threaded_entry", "uses_thread_current",
			"hops", "thread_local_sites", "spawns", "ctrl", "job", "at"}}
		for _, k := range sortedPairs2(groups) {
			a := groups[k]
			e := g.Syms[k.entry-1]
			s := g.Syms[k.sym-1]
			res.rows = append(res.rows, row{cs(e.Name()), cs(s.Name()), ci32(a.sum.hops),
				ci32(a.sum.open), ci32(e.NThreadNew), ci32(e.IsController),
				ci32(e.IsJob), cs(g.at(s.FileId, a.sum.at))})
		}
		return finish(res, func(a, b row) bool {
			if a[3].i != b[3].i {
				return a[3].i > b[3].i
			}
			return a[2].i < b[2].i
		}, lim)
	})

	reg("constant-mutation", symTable([]colDef{
		nameCol(), modCol(),
		num("mutations", func(s *Sym) int32 { return s.NConstMutate }),
		num("freezes", func(s *Sym) int32 { return s.NFreeze }),
		num("dynamic_gets", func(s *Sym) int32 { return s.NConstGet }),
		num("spawns", func(s *Sym) int32 { return s.NThreadNew }),
		num("fan_in", func(s *Sym) int32 { return s.FanIn }),
		atCol(),
	}, func(s *Sym) bool { return s.NConstMutate > 0 },
		func(a, b row) bool { return desc2(a[2].i, b[2].i, a[5].i, b[5].i) }))

	reg("symbol-dos-surface", func(g *Graph, mod func(string) bool, lim int) *result {
		ui := groupInpSites(g)
		res := &result{cols: []string{"name", "module_", "to_sym", "params_reads",
			"input_sites", "kinds", "ctrl", "fan_in", "at"}}
		for _, s := range g.Syms {
			if s.NToSym == 0 || s.NParamsRead == 0 || !okFile(g, s.FileId, mod) {
				continue
			}
			var n int32
			kinds := map[string]bool{}
			for _, u := range ui[s.Id] {
				n++
				kinds[u.Kind()] = true
			}
			res.rows = append(res.rows, row{cs(s.Name()), cs(g.modNameOf(s.ModuleId)),
				ci32(s.NToSym), ci32(s.NParamsRead), ci32(n), joinKinds(kinds),
				ci32(s.IsController), ci32(s.FanIn), symAt(g, s)})
		}
		return finish(res, func(a, b row) bool { return desc2(a[2].i, b[2].i, a[4].i, b[4].i) }, lim)
	})

	reg("regex-dos-surface", func(g *Graph, mod func(string) bool, lim int) *result {
		ui := groupInpSites(g)
		res := &result{cols: []string{"name", "module_", "dynamic_regex",
			"params_reads", "regex_in_loop_", "regex_lits", "input_sites",
			"ctrl", "fan_in", "at"}}
		for _, s := range g.Syms {
			if s.NRegexDyn == 0 || s.NParamsRead == 0 || !okFile(g, s.FileId, mod) {
				continue
			}
			n := int32(len(ui[s.Id]))
			res.rows = append(res.rows, row{cs(s.Name()), cs(g.modNameOf(s.ModuleId)),
				ci32(s.NRegexDyn), ci32(s.NParamsRead), ci32(s.RegexInLoop),
				ci32(s.NRegexLit), ci32(n), ci32(s.IsController), ci32(s.FanIn),
				symAt(g, s)})
		}
		return finish(res, func(a, b row) bool { return desc2(a[2].i, b[2].i, a[6].i, b[6].i) }, lim)
	})

	reg("html-safe-frontier", frontierQ(
		sinkSpec{"n_html_safe", func(s *Sym) int32 { return s.NHtmlSafe }},
		"reads_params", "marks_html_safe",
		[]string{"hops", "html_safe_calls", "ctrl", "fan_in"}))

	reg("file-open-frontier", frontierQ(
		sinkSpec{"n_dynamic_open", func(s *Sym) int32 { return s.NDynamicOpen }},
		"reads_params", "opens_path",
		[]string{"hops", "open_sites", "io_calls", "fan_in"}))

	reg("sql-interp-reachable", func(g *Graph, mod func(string) bool, lim int) *result {
		var roots []int32
		for _, s := range g.Syms {
			if s.NParamsRead > 0 && s.Kind() == "method" {
				roots = append(roots, s.Id)
			}
		}
		interp := make(map[int32]bool, 256)
		for i := range g.ARQs {
			if g.ARQs[i].HasInterpolation != 0 {
				interp[g.ARQs[i].SymID] = true
			}
		}
		type key struct{ src, sym int32 }
		groups := make(map[key]*sinkGroup, 256)
		for _, rp := range reachPairs(g, roots, 4) {
			s := g.Syms[rp.Sym-1]
			if s.NSqlInterp == 0 && !interp[rp.Sym] {
				continue
			}
			if !okFile(g, s.FileId, mod) {
				continue
			}
			k := key{rp.Root, rp.Sym}
			a := groups[k]
			if a == nil {
				a = &sinkGroup{}
				groups[k] = a
			}
			if !a.ok {
				a.ok, a.sum.hops, a.sum.at = true, rp.Hops, s.LineStart
			} else {
				a.sum.hops = mini(a.sum.hops, rp.Hops)
				a.sum.at = mini(a.sum.at, s.LineStart)
			}
			a.sum.sqlInterp = maxi(a.sum.sqlInterp, s.NSqlInterp)
			a.sum.sqlL = maxi(a.sum.sqlL, s.NSqlLiteral)
		}
		res := &result{cols: []string{"reads_params", "builds_sql", "hops",
			"interpolated_sql", "sql_literals", "sink_is_ctrl", "fan_in", "at"}}
		for _, k := range sortedPairs2(groups) {
			a := groups[k]
			s := g.Syms[k.sym-1]
			res.rows = append(res.rows, row{cs(g.Syms[k.src-1].Name()), cs(s.Name()),
				ci32(a.sum.hops), ci32(a.sum.sqlInterp), ci32(a.sum.sqlL),
				ci32(s.IsController), ci32(s.FanIn), cs(g.at(s.FileId, a.sum.at))})
		}
		return finish(res, func(a, b row) bool {
			return desc2(a[2].i, b[2].i, a[3].i, b[3].i)
		}, lim)
	})

	reg("zoneless-time-surface", symTable([]colDef{
		nameCol(), modCol(),
		num("now_calls", func(s *Sym) int32 { return s.NZonelessTime }),
		num("ctrl", func(s *Sym) int32 { return s.IsController }),
		num("in_job", func(s *Sym) int32 { return s.IsJob }),
		num("in_model", func(s *Sym) int32 { return s.IsModel }),
		num("fan_in", func(s *Sym) int32 { return s.FanIn }),
		atCol(),
	}, func(s *Sym) bool { return s.NZonelessTime > 0 },
		func(a, b row) bool { return desc2(a[2].i, b[2].i, a[6].i, b[6].i) }))

	reg("lock-in-loop", func(g *Graph, mod func(string) bool, lim int) *result {
		want := map[string]bool{"transaction": true, "with_lock": true,
			"synchronize": true, "lock": true}
		res := &result{cols: []string{"in_method", "module_", "lock_api",
			"block_depth", "queries_in_block", "exits", "body_sloc", "fan_in", "at"}}
		for i := range g.Blks {
			b := &g.Blks[i]
			if b.Depth == 0 || !want[b.Method()] || b.SymID == 0 ||
				int(b.SymID) > len(g.Syms) || !okFile(g, b.FileID, mod) {
				continue
			}
			s := g.Syms[b.SymID-1]
			res.rows = append(res.rows, row{cs(s.Name()), cs(g.modNameOf(s.ModuleId)),
				cs(b.Method()), ci32(b.Depth), ci32(b.NQueries), ci32(b.NExits),
				ci32(b.BodySloc), ci32(s.FanIn), cs(g.at(b.FileID, b.Line))})
		}
		return finish(res, func(a, b row) bool {
			return desc3(a[3].i, b[3].i, a[4].i, b[4].i, a[7].i, b[7].i)
		}, lim)
	})

	reg("include-shadows-own-method", func(g *Graph, mod func(string) bool, lim int) *result {
		modMethods := make(map[string]map[string][]int32, 256)
		for _, s := range g.Syms {
			if s.Kind() != "method" || s.ParentId == 0 {
				continue
			}
			p := g.Syms[s.ParentId-1]
			if p.Kind() != "module" {
				continue
			}
			if modMethods[p.Name()] == nil {
				modMethods[p.Name()] = map[string][]int32{}
			}
			modMethods[p.Name()][s.Name()] = append(modMethods[p.Name()][s.Name()], s.Sloc)
		}
		hostMethods := make(map[int32]map[string][2]int32, 1024)
		for _, s := range g.Syms {
			if s.Kind() != "method" || s.ParentId == 0 {
				continue
			}
			if hostMethods[s.ParentId] == nil {
				hostMethods[s.ParentId] = map[string][2]int32{}
			}
			hostMethods[s.ParentId][s.Name()] = [2]int32{s.Sloc, s.LineStart}
		}
		res := &result{cols: []string{"host_class", "mixin", "shadowed_method",
			"sloc_in_mixin", "sloc_in_host", "mixin_kind", "include_line", "at"}}
		for i := range g.Mixins {
			x := &g.Mixins[i]
			hm := hostMethods[x.HostID]
			if hm == nil || x.HostID == 0 || int(x.HostID) > len(g.Syms) {
				continue
			}
			h := g.Syms[x.HostID-1]
			if !okFile(g, h.FileId, mod) {
				continue
			}
			for _, meth := range sortedKeys(modMethods[x.MixinShort()]) {
				slocs := modMethods[x.MixinShort()][meth]
				hv, ok := hm[meth]
				if !ok {
					continue
				}
				for _, sloc := range slocs {
					res.rows = append(res.rows, row{cs(h.Name()), cs(x.MixinShort()),
						cs(meth), ci32(sloc), ci32(hv[0]), cs(x.Kind()), ci32(x.Line),
						cs(g.at(x.FileID, x.Line))})
				}
			}
		}
		return finish(res, func(a, b row) bool {
			if a[3].i != b[3].i {
				return a[3].i > b[3].i
			}
			return a[6].i < b[6].i
		}, lim)
	})

	reg("nested-method-def", symTableG([]colDef{
		strc("inner_def", func(s *Sym) string { return s.Name() }),
		{"outer_method", func(g *Graph, s *Sym) cell {
			if s.ParentId == 0 {
				return cnull()
			}
			return cs(g.Syms[s.ParentId-1].Name())
		}},
		modCol(),
		num("sloc", func(s *Sym) int32 { return s.Sloc }),
		num("cyclo", func(s *Sym) int32 { return s.Cyclomatic }),
		num("fan_in", func(s *Sym) int32 { return s.FanIn }),
		atCol(),
	}, keepNested, func(a, b row) bool { return desc2(a[3].i, b[3].i, a[5].i, b[5].i) }))

	reg("only-called-from-tests", func(g *Graph, mod func(string) bool, lim int) *result {
		prod := make(map[int32]int32, 4096)
		test := make(map[int32]int32, 4096)

		for i := range g.Edges {
			e := &g.Edges[i]
			c := g.Syms[e.Caller-1]
			if g.fileIsTest(c.FileId) || c.IsTest != 0 {
				test[e.Callee]++
			} else {
				prod[e.Callee]++
			}
		}
		res := &result{cols: []string{"name", "module_", "test_callers", "sloc",
			"cyclo", "static_fan_in", "at"}}
		for _, s := range g.Syms {
			t, ok := test[s.Id]
			if !ok || prod[s.Id] != 0 {
				continue
			}
			if s.Kind() != "method" && s.Kind() != "function" {
				continue
			}
			if !okFile(g, s.FileId, mod) {
				continue
			}
			res.rows = append(res.rows, row{cs(s.Name()), cs(g.modNameOf(s.ModuleId)),
				ci32(t), ci32(s.Sloc), ci32(s.Cyclomatic), ci32(s.FanIn), symAt(g, s)})
		}
		return finish(res, func(a, b row) bool { return desc2(a[2].i, b[2].i, a[3].i, b[3].i) }, lim)
	})

	reg("eql-without-hash", func(g *Graph, mod func(string) bool, lim int) *result {
		eqCount := make(map[int32]int32, 256)
		eqFirst := make(map[int32]int32, 256)
		keyed := make(map[int32]int32, 256)
		own := make(map[int32]int32, 1024)
		for _, s := range g.Syms {
			if s.Kind() != "method" {
				continue
			}
			if s.ParentId != 0 {
				own[s.ParentId]++
				switch s.Name() {
				case "hash", "eql?", "deconstruct_keys":
					keyed[s.ParentId]++
				}
			}
			if s.Name() == "==" && s.ParentId != 0 {
				eqCount[s.ParentId]++
				if _, ok := eqFirst[s.ParentId]; !ok {
					eqFirst[s.ParentId] = s.LineStart
				}
			}
		}
		res := &result{cols: []string{"owner", "module_", "n_eq_defs",
			"first_line", "keyed_siblings", "own_methods", "at"}}
		pars := make([]int32, 0, len(eqCount))
		for p := range eqCount {
			pars = append(pars, p)
		}
		slices.Sort(pars)
		for _, p := range pars {
			if keyed[p] != 0 {
				continue
			}
			h := g.Syms[p-1]
			if !okFile(g, h.FileId, mod) {
				continue
			}
			res.rows = append(res.rows, row{cs(h.Name()), cs(g.modNameOf(h.ModuleId)),
				ci32(eqCount[p]), ci32(eqFirst[p]), ci32(0), ci32(own[p]),
				cs(g.at(h.FileId, eqFirst[p]))})
		}
		return finish(res, func(a, b row) bool { return desc2(a[2].i, b[2].i, a[5].i, b[5].i) }, lim)
	})

	reg("unguarded-recursion", func(g *Graph, mod func(string) bool, lim int) *result {
		res := &result{cols: []string{"name", "module_", "cyclo", "branches",
			"cases", "calls_", "fan_in", "at"}}
		var ms []*Sym
		for _, s := range g.Syms {
			if s.IsRecursive != 0 && s.NBranches == 0 && s.NCases == 0 &&
				(s.Kind() == "method" || s.Kind() == "function") &&
				okFile(g, s.FileId, mod) {
				ms = append(ms, s)
			}
		}
		sort.SliceStable(ms, func(i, j int) bool {
			if ms[i].Kind() != ms[j].Kind() {
				return ms[i].Kind() < ms[j].Kind()
			}
			return ms[i].Name() < ms[j].Name()
		})
		for _, s := range ms {
			res.rows = append(res.rows, row{cs(s.Name()), cs(g.modNameOf(s.ModuleId)),
				ci32(s.Cyclomatic), ci32(s.NBranches), ci32(s.NCases), ci32(s.NCalls),
				ci32(s.FanIn), symAt(g, s)})
		}
		return finish(res, func(a, b row) bool { return desc2(a[2].i, b[2].i, a[6].i, b[6].i) }, lim)
	})

	reg("regex-in-loop", symTable([]colDef{
		nameCol(), modCol(),
		num("re_in_loop", func(s *Sym) int32 { return s.RegexInLoop }),
		num("dynamic_regex", func(s *Sym) int32 { return s.NRegexDyn }),
		num("regex_lits", func(s *Sym) int32 { return s.NRegexLit }),
		num("iter_blocks", func(s *Sym) int32 { return s.NIterBlocks }),
		num("block_depth", func(s *Sym) int32 { return s.MaxBlockDepth }),
		{"cost", func(_ *Graph, s *Sym) cell {
			return ci32(s.RegexInLoop*(1+s.MaxBlockDepth) + s.NRegexDyn*2)
		}},
		num("fan_in", func(s *Sym) int32 { return s.FanIn }),
		atCol(),
	}, func(s *Sym) bool { return s.RegexInLoop > 0 },
		func(a, b row) bool { return desc2(a[7].i, b[7].i, a[8].i, b[8].i) }))

	_ = strings.TrimSpace
}

type sinkSpec struct {
	name string
	test func(*Sym) int32
}

func frontierQ(sink sinkSpec, colA, colB string, extra []string) func(*Graph, func(string) bool, int) *result {
	return func(g *Graph, mod func(string) bool, lim int) *result {
		var roots []int32
		for _, s := range g.Syms {
			if s.NParamsRead > 0 && s.Kind() == "method" {
				roots = append(roots, s.Id)
			}
		}
		cols := []string{colA, colB}
		cols = append(cols, extra...)
		cols = append(cols, "at")
		type key struct{ src, sym int32 }
		groups := make(map[key]*sinkGroup, 256)
		for _, rp := range reachPairs(g, roots, 4) {
			s := g.Syms[rp.Sym-1]
			if sink.test(s) == 0 || !okFile(g, s.FileId, mod) {
				continue
			}
			k := key{rp.Root, rp.Sym}
			a := groups[k]
			if a == nil {
				a = &sinkGroup{}
				groups[k] = a
			}
			if !a.ok {
				a.ok, a.sum.hops, a.sum.at = true, rp.Hops, s.LineStart
			} else {
				a.sum.hops = mini(a.sum.hops, rp.Hops)
				a.sum.at = mini(a.sum.at, s.LineStart)
			}
			a.sum.sites += sink.test(s)
		}
		res := &result{cols: cols}
		for _, k := range sortedPairs2(groups) {
			a := groups[k]
			s := g.Syms[k.sym-1]
			r := row{cs(g.Syms[k.src-1].Name()), cs(s.Name()), ci32(a.sum.hops)}
			switch sink.name {
			case "n_html_safe":
				r = append(r, ci32(a.sum.sites), ci32(s.IsController), ci32(s.FanIn))
			case "n_dynamic_open":
				r = append(r, ci32(a.sum.sites), ci32(s.NIo), ci32(s.FanIn))
			}
			r = append(r, cs(g.at(s.FileId, a.sum.at)))
			res.rows = append(res.rows, r)
		}
		return finish(res, func(a, b row) bool {
			return desc2(a[2].i, b[2].i, a[3].i, b[3].i)
		}, lim)
	}
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
	{name: "ar_callbacks",
		note: "ActiveRecord callbacks declared on a model",
		cols: []columnShape{
			{"id", "int", false},
			{"symbol_id", "int", true},
			{"file_id", "int", false},
			{"host", "text", false},
			{"hook", "text", false},
			{"method", "text", false},
			{"is_conditional", "int", false},
			{"is_block", "int", false},
			{"is_association", "int", false},
			{"issues_query", "int", false},
			{"target_id", "int", true},
			{"line", "int", false},
		}},
	{name: "ar_queries",
		note: "query-builder chains: the method, the table, the conditions",
		cols: []columnShape{
			{"id", "int", false},
			{"symbol_id", "int", true},
			{"file_id", "int", false},
			{"model", "text", false},
			{"api", "text", false},
			{"build_kind", "text", false},
			{"has_interpolation", "int", false},
			{"is_sanitized", "int", false},
			{"from_params", "int", false},
			{"is_string_arg", "int", false},
			{"loop_depth", "int", false},
			{"chain_len", "int", false},
			{"line", "int", false},
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
	{name: "blocks",
		note: "a block literal: its parameters, and what it returns or raises",
		cols: []columnShape{
			{"id", "int", false},
			{"symbol_id", "int", true},
			{"file_id", "int", false},
			{"method", "text", false},
			{"receiver", "text", false},
			{"style", "text", false},
			{"is_iteration", "int", false},
			{"depth", "int", false},
			{"n_params", "int", false},
			{"body_sloc", "int", false},
			{"n_queries", "int", false},
			{"n_allocs", "int", false},
			{"captures_outer", "int", false},
			{"line", "int", false},
			{"n_exits", "int", false},
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
	{name: "metaprogram_sites",
		note: "a place where code is generated or rewritten at runtime",
		cols: []columnShape{
			{"id", "int", false},
			{"symbol_id", "int", true},
			{"file_id", "int", false},
			{"api", "text", false},
			{"arg", "text", false},
			{"is_literal", "int", false},
			{"from_params", "int", false},
			{"from_variable", "int", false},
			{"on_heredoc", "int", false},
			{"in_class_body", "int", false},
			{"loop_depth", "int", false},
			{"line", "int", false},
		}},
	{name: "mixins",
		note: "a module included in another, and what it brings with it",
		cols: []columnShape{
			{"id", "int", false},
			{"host_id", "int", true},
			{"file_id", "int", false},
			{"host", "text", false},
			{"mixin", "text", false},
			{"mixin_short", "text", false},
			{"kind", "text", false},
			{"in_singleton", "int", false},
			{"line", "int", false},
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
	{name: "monkey_patches",
		note: "a method redefined on a class it was not declared in",
		cols: []columnShape{
			{"id", "int", false},
			{"symbol_id", "int", true},
			{"method_id", "int", true},
			{"file_id", "int", false},
			{"core_class", "text", false},
			{"method", "text", false},
			{"is_operator", "int", false},
			{"is_singleton", "int", false},
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
	{name: "ruby_modules",
		note: "a module (a namespace that can be reopened and mixed in)",
		cols: []columnShape{
			{"symbol_id", "int", false},
			{"file_id", "int", false},
			{"name", "text", false},
			{"is_module", "int", false},
			{"is_concern", "int", false},
			{"has_included_block", "int", false},
			{"has_class_methods_block", "int", false},
			{"superclass", "text", false},
			{"n_mixins", "int", false},
			{"n_defs", "int", false},
			{"n_class_defs", "int", false},
			{"n_class_ivars", "int", false},
			{"n_class_vars", "int", false},
			{"n_globals", "int", false},
			{"n_delegates", "int", false},
			{"reopens_core", "int", false},
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
	{name: "sym_fts",
		note: "a contentless full-text index over (name, qual_name, signature): every column reads back empty, and the four shadow b-tree tables beside it are not reproduced at all",
		cols: []columnShape{
			{"name", "any", true},
			{"qual_name", "any", true},
			{"signature", "any", true},
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
			{"n_sql", "int", false},
			{"n_exec", "int", false},
			{"n_deserialize", "int", false},
			{"n_metaprogram", "int", false},
			{"n_io", "int", false},
			{"n_net", "int", false},
			{"n_crypto", "int", false},
			{"n_concurrency", "int", false},
			{"n_mass_assign", "int", false},
			{"n_rails_query", "int", false},
			{"n_alloc", "int", false},
			{"n_control", "int", false},
			{"n_send", "int", false},
			{"n_define_method", "int", false},
			{"n_method_missing", "int", false},
			{"n_const_get", "int", false},
			{"n_instance_eval", "int", false},
			{"n_class_eval", "int", false},
			{"n_instance_var_get", "int", false},
			{"n_eval", "int", false},
			{"n_metaprogram_other", "int", false},
			{"n_metaprogram_total", "int", false},
			{"n_metaprogram_dynamic", "int", false},
			{"n_blocks", "int", false},
			{"n_block_pass", "int", false},
			{"n_block_given", "int", false},
			{"n_yield", "int", false},
			{"n_proc_new", "int", false},
			{"n_symbol_to_proc", "int", false},
			{"n_iter_blocks", "int", false},
			{"max_block_depth", "int", false},
			{"n_rescue", "int", false},
			{"n_rescue_bare", "int", false},
			{"n_rescue_exception", "int", false},
			{"n_rescue_empty", "int", false},
			{"n_rescue_reraise", "int", false},
			{"n_retry", "int", false},
			{"n_ensure", "int", false},
			{"n_raise", "int", false},
			{"n_class_var", "int", false},
			{"n_instance_var", "int", false},
			{"n_global_var", "int", false},
			{"n_class_level_ivar", "int", false},
			{"n_class_level_write", "int", false},
			{"n_attr_accessor", "int", false},
			{"n_attr_reader", "int", false},
			{"n_attr_writer", "int", false},
			{"n_ar_query", "int", false},
			{"n_ar_query_in_block", "int", false},
			{"n_ar_terminal", "int", false},
			{"n_ar_write", "int", false},
			{"n_permit", "int", false},
			{"n_permit_bang", "int", false},
			{"n_params_read", "int", false},
			{"n_sql_interp", "int", false},
			{"n_sql_literal", "int", false},
			{"n_sql_sanitized", "int", false},
			{"n_string_interp", "int", false},
			{"n_str_lit_in_loop", "int", false},
			{"n_collection_lit_in_loop", "int", false},
			{"n_chain_array_alloc", "int", false},
			{"n_map_chain", "int", false},
			{"n_times_map", "int", false},
			{"n_range_include", "int", false},
			{"n_freeze", "int", false},
			{"n_dup_clone", "int", false},
			{"n_hash_lit", "int", false},
			{"n_array_lit", "int", false},
			{"n_heredoc", "int", false},
			{"n_subshell", "int", false},
			{"n_monkey_patch", "int", false},
			{"n_mixins", "int", false},
			{"n_timeout", "int", false},
			{"n_thread_new", "int", false},
			{"n_mutex", "int", false},
			{"n_ractor", "int", false},
			{"n_thread_local", "int", false},
			{"n_alias", "int", false},
			{"n_super", "int", false},
			{"n_forwarding", "int", false},
			{"n_end_data", "int", false},
			{"n_system_call", "int", false},
			{"n_constantize", "int", false},
			{"n_html_safe", "int", false},
			{"n_raw_sql", "int", false},
			{"n_weak_hash", "int", false},
			{"n_weak_random", "int", false},
			{"n_redirect", "int", false},
			{"n_auth_call", "int", false},
			{"n_fetch", "int", false},
			{"n_xxe_parser", "int", false},
			{"n_dynamic_open", "int", false},
			{"n_zip_read", "int", false},
			{"n_log_call", "int", false},
			{"n_open_call", "int", false},
			{"n_sleep_call", "int", false},
			{"n_include_in_loop", "int", false},
			{"n_enum_in_loop", "int", false},
			{"n_count_in_loop", "int", false},
			{"n_ar_write_in_loop", "int", false},
			{"n_serialize_in_loop", "int", false},
			{"n_elif", "int", false},
			{"n_external_calls", "int", false},
			{"n_save_ignored", "int", false},
			{"n_legacy_chain", "int", false},
			{"has_sig", "int", false},
			{"n_const_ref", "int", false},
			{"n_to_sym", "int", false},
			{"n_regex_dyn", "int", false},
			{"n_enqueue", "int", false},
			{"n_enqueue_in_loop", "int", false},
			{"n_zoneless_time", "int", false},
			{"n_const_mutate", "int", false},
			{"n_thread_join", "int", false},
			{"has_frozen_literal", "int", false},
			{"is_controller", "int", false},
			{"is_model", "int", false},
			{"is_job", "int", false},
			{"is_concern", "int", false},
			{"is_singleton", "int", false},
			{"is_endless", "int", false},
			{"is_threaded_entry", "int", false},
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

func checkSchema() error {
	for _, t := range graphShape {
		want, known := tableColumns[t.name]
		if !known {
			return fmt.Errorf("--schema: no row layout for table %s", t.name)
		}
		if got := len(t.cols); got != want {
			return fmt.Errorf("--schema: table %s has %d columns in the "+
				"description and %d in the row layout", t.name, got, want)
		}
	}
	for name := range tableColumns {
		if !describedTable(name) {
			return fmt.Errorf("--schema: table %s has a row layout but is "+
				"not described", name)
		}
	}
	return nil
}

func describedTable(name string) bool {
	for _, t := range graphShape {
		if t.name == name {
			return true
		}
	}
	return false
}

func printSchema() {
	if err := checkSchema(); err != nil {
		fmt.Println("codegraph-ruby: " + err.Error())
		return
	}
	fmt.Print(schemaNative())
}

func init() {
	reg := func(name string, f func(*Graph, func(string) bool, int) *result) {
		questionRuns[name] = f
	}

	reg("graph-blindspots", func(g *Graph, mod func(string) bool, lim int) *result {
		type agg struct {
			methods                            int32
			calls, ext, unres, meta, dyn, send int32
			define, missing, evals             int32
		}
		groups := make(map[int32]*agg, 128)
		for _, s := range g.Syms {
			if s.Kind() != "method" || s.ModuleId == 0 {
				continue
			}
			name := g.modNameOf(s.ModuleId)
			if !mod(name) {
				continue
			}
			a := groups[s.ModuleId]
			if a == nil {
				a = &agg{}
				groups[s.ModuleId] = a
			}
			a.methods++
			a.calls += s.NCalls
			a.ext += s.NExternalCalls
			a.unres += s.NUnresolvedCalls
			a.meta += s.NMetaprogramTotal
			a.dyn += s.NMetaprogramDynamic
			a.send += s.NSend
			a.define += s.NDefineMethod
			a.missing += s.NMethodMissing
			a.evals += s.NClassEval + s.NInstanceEval + s.NEval
		}
		res := &result{cols: []string{"module_", "methods_", "calls", "external",
			"unresolved", "meta", "dynamic_meta", "send_", "define_method",
			"method_missing", "evals", "pct_opaque"}}
		for _, id := range sortedIDs(groups) {
			a := groups[id]
			if a.calls == 0 {
				continue
			}
			pct := int32(0)
			if a.calls != 0 {
				pct = int32(100 * float64(a.unres+a.meta) / float64(a.calls))
			}
			res.rows = append(res.rows, row{cs(g.modNameOf(id)), ci32(a.methods),
				ci32(a.calls), ci32(a.ext), ci32(a.unres), ci32(a.meta),
				ci32(a.dyn), ci32(a.send), ci32(a.define), ci32(a.missing),
				ci32(a.evals), ci32(pct)})
		}
		return finish(res, func(a, b row) bool {
			return desc2(a[5].i+a[4].i, b[5].i+b[4].i, 0, 0)
		}, lim)
	})

	reg("block-vs-proc-cost", symTable([]colDef{
		nameCol(), modCol(),
		num("blocks_", func(s *Sym) int32 { return s.NBlocks }),
		num("iter_blocks", func(s *Sym) int32 { return s.NIterBlocks }),
		num("block_pass", func(s *Sym) int32 { return s.NBlockPass }),
		num("sym_to_proc", func(s *Sym) int32 { return s.NSymbolToProc }),
		num("block_given", func(s *Sym) int32 { return s.NBlockGiven }),
		num("yields", func(s *Sym) int32 { return s.NYield }),
		num("proc_new", func(s *Sym) int32 { return s.NProcNew }),
		num("lambdas", func(s *Sym) int32 { return s.NLambda }),
		num("times_map", func(s *Sym) int32 { return s.NTimesMap }),
		num("depth", func(s *Sym) int32 { return s.MaxBlockDepth }),
		num("fan_in", func(s *Sym) int32 { return s.FanIn }),
		num("sites", func(s *Sym) int32 { return s.NCallsites }),
		{"payoff", func(_ *Graph, s *Sym) cell {
			var v int32
			if s.NBlockGiven > 0 && s.NBlockPass > 0 {
				v = 4
			}
			fan := max(s.FanIn, 1)
			return ci32((s.NBlockPass*2 + s.NProcNew*3 + s.NLambda*2 +
				s.NTimesMap*3 + v) * fan)
		}},
		atCol(),
	}, func(s *Sym) bool {
		return s.NBlockPass+s.NProcNew+s.NLambda+s.NTimesMap > 0
	}, func(a, b row) bool { return a[14].i > b[14].i }))

	reg("frozen-literal-debt", symTable([]colDef{
		nameCol(), qualCol(),
		num("frozen_pragma", func(s *Sym) int32 { return s.HasFrozenLiteral }),
		num("str_lits_in_loop", func(s *Sym) int32 { return s.NStrLitInLoop }),
		num("interpolations", func(s *Sym) int32 { return s.NStringInterp }),
		num("dup_clone", func(s *Sym) int32 { return s.NDupClone }),
		num("freezes", func(s *Sym) int32 { return s.NFreeze }),
		num("depth", func(s *Sym) int32 { return s.MaxLoopDepth }),
		num("fan_in", func(s *Sym) int32 { return s.FanIn }),
		atCol(),
	}, func(s *Sym) bool {
		return s.HasFrozenLiteral == 0 && (s.NStrLitInLoop > 0 || s.NStringInterp > 2)
	}, func(a, b row) bool {
		return desc2(a[3].i*(1+a[8].i), b[3].i*(1+b[8].i), a[4].i, b[4].i)
	}))

	reg("hot-multipliers", symTableF([]colDef{
		nameCol(),
		num("fan_in", func(s *Sym) int32 { return s.FanIn }),
		num("sites", func(s *Sym) int32 { return s.NCallsites }),
		num("fan_out", func(s *Sym) int32 { return s.FanOut }),
		num("cyclo", func(s *Sym) int32 { return s.Cyclomatic }),
		num("sloc", func(s *Sym) int32 { return s.Sloc }),
		kindCol(), modCol(), atCol(),
	}, func(_ *Graph, s *Sym) bool { return s.FanIn > 0 }, inMod,
		func(a, b row) bool { return desc2(a[1].i, b[1].i, a[4].i, b[4].i) }))

	reg("risk-ranked", symTableF([]colDef{
		nameCol(),
		num("risk", func(s *Sym) int32 { return s.RiskScore }),
		num("cyclo", func(s *Sym) int32 { return s.Cyclomatic }),
		num("cog", func(s *Sym) int32 { return s.Cognitive }),
		num("nest", func(s *Sym) int32 { return s.MaxNesting }),
		num("hazards", func(s *Sym) int32 { return s.NHazards }),
		num("fan_in", func(s *Sym) int32 { return s.FanIn }),
		num("sloc", func(s *Sym) int32 { return s.Sloc }),
		atCol(),
	}, func(_ *Graph, s *Sym) bool { return s.RiskScore > 0 },
		func(g *Graph, fid int32, mod func(string) bool) bool {
			if fid <= 0 || int(fid) > len(g.Files) {
				return false
			}
			return !g.fileIsGenerated(fid) && mod(g.modNameOf(g.Files[fid-1].ModuleID))
		},
		func(a, b row) bool { return a[1].i > b[1].i }))

	reg("parse-coverage", func(g *Graph, mod func(string) bool, lim int) *result {
		res := &result{cols: []string{"path", "lines", "bytes", "error_nodes",
			"missing", "parsed", "generated", "test", "vendored"}}
		for _, f := range g.Files {
			if f.ParseErrors == 0 && f.Parsed != 0 {
				continue
			}
			if !mod(g.modNameOf(f.ModuleID)) {
				continue
			}
			res.rows = append(res.rows, row{cs(f.Path()), ci32(f.Lines), ci32(f.Bytes),
				ci32(f.ParseErrors), ci32(f.Missing), ci32(f.Parsed),
				ci32(f.IsGenerated), ci32(f.IsTest), ci32(f.IsVendored)})
		}
		return finish(res, func(a, b row) bool { return desc2(a[3].i, b[3].i, a[1].i, b[1].i) }, lim)
	})

	reg("deep-nesting", symTable([]colDef{
		nameCol(),
		num("nesting", func(s *Sym) int32 { return s.MaxNesting }),
		num("cyclo", func(s *Sym) int32 { return s.Cyclomatic }),
		num("cognitive", func(s *Sym) int32 { return s.Cognitive }),
		num("blocks", func(s *Sym) int32 { return s.NBlocks }),
		num("block_depth", func(s *Sym) int32 { return s.MaxBlockDepth }),
		num("sloc", func(s *Sym) int32 { return s.Sloc }),
		num("fan_in", func(s *Sym) int32 { return s.FanIn }),
		atCol(),
	}, func(s *Sym) bool {
		return s.MaxNesting > 4 && (s.Kind() == "method" || s.Kind() == "function")
	}, func(a, b row) bool { return desc2(a[1].i, b[1].i, a[2].i, b[2].i) }))

	reg("too-many-params", symTable([]colDef{
		nameCol(),
		num("n_params", func(s *Sym) int32 { return s.NParams }),
		num("n_optional_params", func(s *Sym) int32 { return s.NOptionalParams }),
		num("sloc", func(s *Sym) int32 { return s.Sloc }),
		num("cyclo", func(s *Sym) int32 { return s.Cyclomatic }),
		num("fan_in", func(s *Sym) int32 { return s.FanIn }),
		atCol(),
	}, func(s *Sym) bool {
		return s.NParams > 5 && (s.Kind() == "method" || s.Kind() == "function")
	}, func(a, b row) bool { return desc2(a[1].i, b[1].i, a[5].i, b[5].i) }))

	reg("scattered-concerns", func(g *Graph, mod func(string) bool, lim int) *result {
		type agg struct {
			mods  map[int32]bool
			names map[string]bool
			s     *Sym
		}
		groups := make(map[int32]*agg, 4096)
		for i := range g.Edges {
			e := &g.Edges[i]
			if e.Self != 0 || e.Callee == 0 || int(e.Callee) > len(g.Syms) {
				continue
			}
			c := g.Syms[e.Callee-1]
			if c.Kind() != "method" && c.Kind() != "function" {
				continue
			}
			a := groups[e.Callee]
			if a == nil {
				a = &agg{s: c, mods: map[int32]bool{}, names: map[string]bool{}}
				groups[e.Callee] = a
			}
			caller := g.Syms[e.Caller-1]
			a.mods[caller.ModuleId] = true
			if n := g.modNameOf(caller.ModuleId); n != "" {
				a.names[n] = true
			}
		}
		res := &result{cols: []string{"name", "n_caller_modules", "fan_in",
			"cyclo", "sloc", "modules", "at"}}
		for _, id := range sortedIDs(groups) {
			a := groups[id]
			if len(a.mods) <= 5 || !okFile(g, a.s.FileId, mod) {
				continue
			}
			res.rows = append(res.rows, row{cs(a.s.Name()), ci32(int32(len(a.mods))),
				ci32(a.s.FanIn), ci32(a.s.Cyclomatic), ci32(a.s.Sloc),
				cs(joinSorted(a.names)), symAt(g, a.s)})
		}
		return finish(res, func(a, b row) bool {
			return desc2(a[1].i, b[1].i, a[2].i, b[2].i)
		}, lim)
	})

	reg("callback-load", func(g *Graph, mod func(string) bool, lim int) *result {
		type agg struct {
			n, q, cond, block, unresolved int32
			at, fid                       int32
			names                         map[string]bool
		}
		groups := make(map[string]*agg, 256)
		for i := range g.ARCBs {
			c := &g.ARCBs[i]
			if !okFile(g, c.FileID, mod) {
				continue
			}
			a := groups[c.Host()]
			if a == nil {
				a = &agg{at: c.Line, fid: c.FileID, names: map[string]bool{}}
				groups[c.Host()] = a
			}
			a.names[c.Hook()] = true
			a.n++
			a.q += c.IssuesQuery
			a.cond += c.Conditional
			a.block += c.Block
			if !c.HasTargetID && c.Method() != "" && c.Block == 0 {
				a.unresolved++
			}
			if c.Line < a.at {
				a.at, a.fid = c.Line, c.FileID
			}
		}
		res := &result{cols: []string{"host", "callbacks", "query_callbacks",
			"conditional_hooks", "block_hooks", "unresolved_targets",
			"distinct_hooks", "at"}}
		for host, a := range groups {
			res.rows = append(res.rows, row{cs(host), ci32(a.n), ci32(a.q),
				ci32(a.cond), ci32(a.block), ci32(a.unresolved),
				ci32(int32(len(a.names))), cs(g.at(a.fid, a.at))})
		}
		return finish(res, func(a, b row) bool { return desc2(a[1].i, b[1].i, a[2].i, b[2].i) }, lim)
	})

	reg("association-fanout", func(g *Graph, mod func(string) bool, lim int) *result {
		mixinsByHost := make(map[int32]int32, 512)
		for i := range g.Mixins {
			if g.Mixins[i].HostID != 0 {
				mixinsByHost[g.Mixins[i].HostID]++
			}
		}
		type agg struct {
			host, sym string
			n, cond   int32
			at, fid   int32
		}
		groups := make(map[[2]string]*agg, 256)
		for i := range g.ARCBs {
			c := &g.ARCBs[i]
			if c.Association == 0 || !okFile(g, c.FileID, mod) {
				continue
			}
			k := [2]string{c.Host(), itoa(c.SymID)}
			a := groups[k]
			if a == nil {
				a = &agg{host: c.Host(), sym: itoa(c.SymID), at: c.Line, fid: c.FileID}
				groups[k] = a
			}
			a.n++
			a.cond += c.Conditional
			if c.Line < a.at {
				a.at, a.fid = c.Line, c.FileID
			}
		}
		res := &result{cols: []string{"host", "associations", "conditional",
			"mixins_included", "at"}}
		for _, a := range groups {
			var sid int32
			sid = atoi(a.sym)
			res.rows = append(res.rows, row{cs(a.host), ci32(a.n), ci32(a.cond),
				ci32(mixinsByHost[sid]), cs(g.at(a.fid, a.at))})
		}
		return finish(res, func(a, b row) bool { return desc2(a[1].i, b[1].i, a[3].i, b[3].i) }, lim)
	})

	reg("mixin-fanout", func(g *Graph, mod func(string) bool, lim int) *result {
		distinct := make(map[int32]map[string]bool, 512)
		for i := range g.Mixins {
			m := &g.Mixins[i]
			if distinct[m.HostID] == nil {
				distinct[m.HostID] = map[string]bool{}
			}
			distinct[m.HostID][m.MixinShort()] = true
		}
		singl := make(map[int32]int32, 512)
		for i := range g.Mixins {
			if g.Mixins[i].InSingleton != 0 {
				singl[g.Mixins[i].HostID]++
			}
		}
		res := &result{cols: []string{"host", "mixins_", "distinct_mixins",
			"singleton_mixins", "own_defs", "superclass", "at"}}
		for i := range g.RMods {
			r := &g.RMods[i]
			if r.NMixins == 0 || !okFile(g, r.FileID, mod) {
				continue
			}
			res.rows = append(res.rows, row{cs(r.Name()), ci32(r.NMixins),
				ci32(int32(len(distinct[r.SymID]))), ci32(singl[r.SymID]),
				ci32(r.NDefs), cs(r.Superclass()), cs(g.at(r.FileID, r.Line))})
		}
		return finish(res, func(a, b row) bool { return desc2(a[1].i, b[1].i, a[2].i, b[2].i) }, lim)
	})

	reg("metaprogram-density", func(g *Graph, mod func(string) bool, lim int) *result {
		byParent := groupByParent(g)
		res := &result{cols: []string{"owner", "module_", "explicit_defs",
			"define_method", "method_missing", "eval_family", "meta_total",
			"pct_meta", "at"}}
		for i := range g.RMods {
			r := &g.RMods[i]
			if !okFile(g, r.FileID, mod) {
				continue
			}
			var def, mm, ev, meta int32
			for _, s := range byParent[r.SymID] {
				if s.Kind() != "method" {
					continue
				}
				def += s.NDefineMethod
				mm += s.NMethodMissing
				ev += s.NClassEval + s.NInstanceEval + s.NEval
				meta += s.NMetaprogramTotal
			}
			if meta == 0 {
				continue
			}
			total := r.NDefs + meta
			pct := int32(0)
			if total != 0 {
				pct = int32(100 * float64(meta) / float64(total))
			}
			res.rows = append(res.rows, row{cs(r.Name()), cs(g.modNameOf(g.Files[r.FileID-1].ModuleID)),
				ci32(r.NDefs), ci32(def), ci32(mm), ci32(ev), ci32(meta), ci32(pct),
				cs(g.at(r.FileID, r.Line))})
		}
		return finish(res, func(a, b row) bool { return desc2(a[7].i, b[7].i, a[6].i, b[6].i) }, lim)
	})

	reg("delegate-density", func(g *Graph, mod func(string) bool, lim int) *result {
		res := &result{cols: []string{"host", "module_", "delegate_statements",
			"own_defs", "pct_delegated", "at"}}
		for i := range g.RMods {
			r := &g.RMods[i]
			if r.NDelegates == 0 || !okFile(g, r.FileID, mod) {
				continue
			}
			pct := int32(0)
			if tot := r.NDelegates + r.NDefs; tot != 0 {
				pct = int32(100 * float64(r.NDelegates) / float64(tot))
			}
			res.rows = append(res.rows, row{cs(r.Name()),
				cs(g.modNameOf(g.Files[r.FileID-1].ModuleID)), ci32(r.NDelegates),
				ci32(r.NDefs), ci32(pct), cs(g.at(r.FileID, r.Line))})
		}
		return finish(res, func(a, b row) bool { return desc2(a[2].i, b[2].i, a[4].i, b[4].i) }, lim)
	})

	reg("attr-exposure", func(g *Graph, mod func(string) bool, lim int) *result {
		methods := make(map[int32]int32, 4096)
		for _, s := range g.Syms {
			if s.Kind() == "method" && s.ParentId != 0 {
				methods[s.ParentId]++
			}
		}
		res := &result{cols: []string{"owner", "module_", "exposed_attrs",
			"explicit_methods", "pct_generated_api", "fan_in", "at"}}
		for _, s := range g.Syms {
			if s.Kind() != "class" && s.Kind() != "module" {
				continue
			}
			exposed := s.NAttrAccessor + s.NAttrReader + s.NAttrWriter
			if exposed == 0 || !okFile(g, s.FileId, mod) {
				continue
			}
			m := methods[s.Id]
			pct := int32(0)
			if tot := exposed + m; tot != 0 {
				pct = int32(100 * float64(exposed) / float64(tot))
			}
			res.rows = append(res.rows, row{cs(s.Name()), cs(g.modNameOf(s.ModuleId)),
				ci32(exposed), ci32(m), ci32(pct), ci32(s.FanIn), symAt(g, s)})
		}
		return finish(res, func(a, b row) bool { return desc2(a[4].i, b[4].i, a[2].i, b[2].i) }, lim)
	})

	reg("class-variable-surface", func(g *Graph, mod func(string) bool, lim int) *result {
		byParent := groupByParent(g)
		res := &result{cols: []string{"owner", "module_", "class_vars",
			"class_ivars", "write_sites", "class_var_uses", "surface", "at"}}
		for i := range g.RMods {
			r := &g.RMods[i]
			if !okFile(g, r.FileID, mod) {
				continue
			}
			var writes, uses int32
			for _, s := range byParent[r.SymID] {
				if s.Kind() != "method" {
					continue
				}
				writes += s.NClassLevelWrite
				uses += s.NClassVar
			}
			surface := r.NClassVars + r.NClassIvars + writes
			if surface == 0 {
				continue
			}
			res.rows = append(res.rows, row{cs(r.Name()),
				cs(g.modNameOf(g.Files[r.FileID-1].ModuleID)), ci32(r.NClassVars),
				ci32(r.NClassIvars), ci32(writes), ci32(uses), ci32(surface),
				cs(g.at(r.FileID, r.Line))})
		}
		return finish(res, func(a, b row) bool { return desc2(a[6].i, b[6].i, a[4].i, b[4].i) }, lim)
	})

	reg("class-weight", func(g *Graph, mod func(string) bool, lim int) *result {
		res := &result{cols: []string{"owner", "module_", "is_module_",
			"methods_", "class_methods_", "mixins_", "sloc", "cyclo",
			"sloc_per_method", "at"}}
		for i := range g.RMods {
			r := &g.RMods[i]
			if r.NDefs == 0 || !okFile(g, r.FileID, mod) {
				continue
			}
			cls := g.Syms[r.SymID-1]
			per := cls.Sloc
			if r.NDefs > 0 {
				per = cls.Sloc / r.NDefs
			}
			res.rows = append(res.rows, row{cs(r.Name()),
				cs(g.modNameOf(g.Files[r.FileID-1].ModuleID)), ci32(r.IsModule),
				ci32(r.NDefs), ci32(r.NClassDefs), ci32(r.NMixins), ci32(cls.Sloc),
				ci32(cls.Cyclomatic), ci32(per), cs(g.at(r.FileID, r.Line))})
		}
		return finish(res, func(a, b row) bool { return desc2(a[6].i, b[6].i, a[3].i, b[3].i) }, lim)
	})

	reg("constant-coupling", symTable([]colDef{
		strc("in_method", func(s *Sym) string { return s.Name() }), modCol(),
		num("const_refs", func(s *Sym) int32 { return s.NConstRef }),
		num("dynamic_gets", func(s *Sym) int32 { return s.NConstGet }),
		num("constantizes", func(s *Sym) int32 { return s.NConstantize }),
		num("fan_out", func(s *Sym) int32 { return s.FanOut }),
		num("fan_in", func(s *Sym) int32 { return s.FanIn }),
		atCol(),
	}, func(s *Sym) bool {
		return s.NConstRef+s.NConstGet > 3 && s.Kind() == "method"
	}, func(a, b row) bool { return desc2(a[2].i, b[2].i, a[3].i, b[3].i) }))

	reg("yield-spread", func(g *Graph, mod func(string) bool, lim int) *result {
		byParent := groupByParent(g)
		res := &result{cols: []string{"owner", "module_", "owner_kind",
			"yielding_methods", "yields", "block_given_checks", "callers", "at"}}
		for _, owner := range sortedIDs(byParent) {
			o := g.Syms[owner-1]
			if o.Kind() != "module" && o.Kind() != "class" {
				continue
			}
			if !okFile(g, o.FileId, mod) {
				continue
			}
			var n, yields, bg, callers, at int32
			for _, y := range byParent[owner] {
				if y.Kind() != "method" || y.NYield == 0 {
					continue
				}
				n++
				yields += y.NYield
				bg += y.NBlockGiven
				callers += y.FanIn
				if at == 0 || y.LineStart < at {
					at = y.LineStart
				}
			}
			if n == 0 {
				continue
			}
			res.rows = append(res.rows, row{cs(o.Name()), cs(g.modNameOf(o.ModuleId)),
				cs(o.Kind()), ci32(n), ci32(yields), ci32(bg), ci32(callers),
				cs(g.at(o.FileId, at))})
		}
		return finish(res, func(a, b row) bool { return desc2(a[4].i, b[4].i, a[6].i, b[6].i) }, lim)
	})

	reg("enqueue-spread", func(g *Graph, mod func(string) bool, lim int) *result {
		byParent := groupByParent(g)
		res := &result{cols: []string{"owner", "module_", "enqueues",
			"enqueue_methods", "enqueues_in_loops", "owner_is_job", "at"}}
		for i := range g.RMods {
			r := &g.RMods[i]
			if !okFile(g, r.FileID, mod) {
				continue
			}
			var enq, inLoop, methods int32
			for _, s := range byParent[r.SymID] {
				if s.NEnqueue == 0 {
					continue
				}
				methods++
				enq += s.NEnqueue
				inLoop += s.NEnqueueInLoop
			}
			if enq == 0 {
				continue
			}
			res.rows = append(res.rows, row{cs(r.Name()),
				cs(g.modNameOf(g.Files[r.FileID-1].ModuleID)), ci32(enq),
				ci32(methods), ci32(inLoop), ci32(g.Syms[r.SymID-1].IsJob),
				cs(g.at(r.FileID, r.Line))})
		}
		return finish(res, func(a, b row) bool { return desc2(a[2].i, b[2].i, a[4].i, b[4].i) }, lim)
	})

	reg("dynamic-fanin", func(g *Graph, mod func(string) bool, lim int) *result {
		want := map[string]bool{"send": true, "public_send": true, "__send__": true}
		callers := make(map[string]map[int32]bool, 256)
		for i := range g.MSites {
			m := &g.MSites[i]
			if !want[m.API()] || m.Literal != 1 || len(m.Arg()) < 2 || m.Arg()[0] != ':' {
				continue
			}
			meth := m.Arg()[1:]
			if callers[meth] == nil {
				callers[meth] = map[int32]bool{}
			}
			callers[meth][m.SymID] = true
		}
		res := &result{cols: []string{"invoked_dynamically", "module_",
			"send_callers", "public_", "static_fan_in", "at"}}
		names := make([]string, 0, len(callers))
		for n := range callers {
			names = append(names, n)
		}
		sort.Strings(names)
		for _, meth := range names {
			n := int32(len(callers[meth]))
			for _, s := range g.Syms {
				if s.Name() != meth || s.Kind() != "method" || !okFile(g, s.FileId, mod) {
					continue
				}
				res.rows = append(res.rows, row{cs(s.Name()), cs(g.modNameOf(s.ModuleId)),
					ci32(n), ci32(s.IsPublic), ci32(s.FanIn), symAt(g, s)})
			}
		}
		return finish(res, func(a, b row) bool { return desc2(a[2].i, b[2].i, a[4].i, b[4].i) }, lim)
	})

	_ = strings.TrimSpace
}

func itoa(v int32) string {
	if v == 0 {
		return "0"
	}
	neg := v < 0
	if neg {
		v = -v
	}
	var buf [12]byte
	i := len(buf)
	for v > 0 {
		i--
		buf[i] = byte('0' + v%10)
		v /= 10
	}
	if neg {
		i--
		buf[i] = '-'
	}
	return string(buf[i:])
}

func atoi(s string) int32 {
	var v int32
	for i := 0; i < len(s); i++ {
		if s[i] < '0' || s[i] > '9' {
			return 0
		}
		v = v*10 + int32(s[i]-'0')
	}
	return v
}

func joinKinds(m map[string]bool) cell {
	if len(m) == 0 {
		return cnull()
	}
	return cs(joinSorted(m))
}

func (b *builder) aggregate() {
	g := b.g
	n := len(g.Syms)
	if n == 0 {
		return
	}
	fanIn := make([]int32, n+1)
	fanOut := make([]int32, n+1)
	callsites := make([]int32, n+1)
	recursive := make([]bool, n+1)
	hazN := make([]int32, n+1)
	unresN := make([]int32, n+1)

	for i := range g.Edges {
		e := &g.Edges[i]
		if e.Self == 0 {
			fanOut[e.Caller]++
			fanIn[e.Callee]++
		} else {
			recursive[e.Caller] = true
		}
	}
	for i := range g.Sites {
		callsites[g.Sites[i].Callee]++
	}
	for i := range g.Unres {
		unresN[g.Unres[i].Caller] += g.Unres[i].N
	}
	for i := range g.Haz {
		hazN[g.Haz[i].SymID] += g.Haz[i].N
	}

	catIdx := make(map[string]int32, len(hazardCategories))
	for i, c := range hazardCategories {
		catIdx[c] = int32(i)
	}
	catSum := make([][]int32, len(hazardCategories))
	for i := range catSum {
		catSum[i] = make([]int32, n+1)
	}
	for i := range g.Haz {
		if ci, ok := catIdx[g.Haz[i].Category()]; ok {
			catSum[ci][g.Haz[i].SymID] += g.Haz[i].N
		}
	}
	setCat := func(s *Sym, c *symCold, id int32, ci int32, v int32) {
		switch ci {
		case 0:
			s.NSql = v
		case 1:
			s.NExec = v
		case 2:
			g.setCold16(id, &c.NDeserialize, wNDeserialize, v)
		case 3:
			g.setCold16(id, &c.NMetaprogram, wNMetaprogram, v)
		case 4:
			s.NIo = v
		case 5:
			s.NNet = v
		case 6:
			g.setCold16(id, &c.NCrypto, wNCrypto, v)
		case 7:
			g.setCold16(id, &c.NConcurrency, wNConcurrency, v)
		case 8:
			s.NMassAssign = v
		case 9:
			s.NRailsQuery = v
		case 10:
			g.setCold16(id, &c.NAlloc, wNAlloc, v)
		case 11:
			g.setCold16(id, &c.NControl, wNControl, v)
		}
	}

	blkQ := make([]int32, len(g.Blks))
	if len(g.Blks) > 0 && len(g.ARQs) > 0 {
		type qloc struct {
			sym, line int32
		}
		qs := make([]qloc, 0, len(g.ARQs))
		for i := range g.ARQs {
			qs = append(qs, qloc{g.ARQs[i].SymID, g.ARQs[i].Line})
		}
		sort.Slice(qs, func(a, b int) bool {
			if qs[a].sym != qs[b].sym {
				return qs[a].sym < qs[b].sym
			}
			return qs[a].line < qs[b].line
		})
		bySym := make(map[int32][]int32, 1024)
		for _, q := range qs {
			bySym[q.sym] = append(bySym[q.sym], q.line)
		}
		for i := range g.Blks {
			lines := bySym[g.Blks[i].SymID]
			if len(lines) == 0 {
				continue
			}
			lo := sort.Search(len(lines), func(j int) bool { return lines[j] >= g.Blks[i].Line })
			hi := sort.Search(len(lines), func(j int) bool { return lines[j] > g.Blks[i].Line+g.Blks[i].BodySloc })
			blkQ[i] = int32(hi - lo)
		}
	}
	for i := range g.Blks {
		g.Blks[i].NQueries = blkQ[i]
	}

	arqInBlock := make([]int32, n+1)
	for i := range g.ARQs {
		if g.ARQs[i].LoopDepth > 0 {
			arqInBlock[g.ARQs[i].SymID]++
		}
	}
	metaDyn := make([]int32, n+1)
	for i := range g.MSites {
		if g.MSites[i].Literal == 0 {
			metaDyn[g.MSites[i].SymID]++
		}
	}
	mixinN := make([]int32, n+1)
	for i := range g.Mixins {
		if g.Mixins[i].HostID != 0 {
			mixinN[g.Mixins[i].HostID]++
		}
	}
	attrAcc := make([]int32, n+1)
	attrRd := make([]int32, n+1)
	attrWr := make([]int32, n+1)
	for i := range g.Fields {
		f := &g.Fields[i]
		switch f.Type() {
		case "attr_accessor":
			attrAcc[f.SymID]++
		case "attr_reader":
			attrRd[f.SymID]++
		case "attr_writer":
			attrWr[f.SymID]++
		}
	}

	for i := range g.Syms {
		s := g.Syms[i]
		c := &g.cold[i]
		id := int(s.Id)
		s.FanOut = fanOut[id]
		s.FanIn = fanIn[id]
		s.NCallsites = callsites[id]
		if recursive[id] {
			s.IsRecursive = 1
		}
		s.NUnresolvedCalls = unresN[id]
		s.NHazards = hazN[id]
		c.IsLeaf = int16(b2i(s.FanOut == 0))
		c.IsRoot = int16(b2i(s.FanIn == 0))

		for ci := range hazardCategories {
			if v := catSum[ci][id]; v != 0 {
				setCat(s, c, int32(id), int32(ci), v)
			}
		}
		s.NArQueryInBlock = arqInBlock[id]
		s.NMetaprogramDynamic = metaDyn[id]
		s.NMixins = mixinN[id]
		s.NAttrAccessor = attrAcc[id]
		s.NAttrReader = attrRd[id]
		s.NAttrWriter = attrWr[id]
		if s.NThreadNew != 0 || s.NRactor != 0 || s.IsJob == 1 ||
			(s.IsController == 1 && s.IsPublic == 1 && s.Kind() == "method") {
			s.IsThreadedEntry = 1
		}
	}

	byFileName := make(map[fileNameKey]int32, 4096)
	for _, s := range g.Syms {
		if s.Kind() != "method" {
			continue
		}
		k := fileNameKey{s.FileId, s.Name()}
		if cur, ok := byFileName[k]; !ok || s.LineStart < cur {
			byFileName[k] = s.LineStart
		}
	}

	firstInFile := make(map[fileNameKey]int32, 4096)
	atLine := make(map[fileLineKey]int32, 4096)
	for _, s := range g.Syms {
		if s.Kind() != "method" {
			continue
		}
		k := fileNameKey{s.FileId, s.Name()}
		if _, ok := firstInFile[k]; !ok {
			firstInFile[k] = s.Id
		}
		kl := fileLineKey{s.FileId, s.Name(), s.LineStart}
		if _, ok := atLine[kl]; !ok {
			atLine[kl] = s.Id
		}
	}
	for i := range g.ARCBs {
		c := &g.ARCBs[i]
		if c.Method() == "" {
			continue
		}
		if t, ok := firstInFile[fileNameKey{c.FileID, c.Method()}]; ok {
			c.TargetID = t
			c.HasTargetID = true
		}
	}
	for i := range g.ARCBs {
		c := &g.ARCBs[i]
		if c.HasTargetID && int(c.TargetID) <= len(g.Syms) {
			t := g.Syms[c.TargetID-1]
			if t.NArQuery != 0 || t.NRailsQuery != 0 || t.NSql != 0 {
				c.IssuesQuery = 1
			}
		}
	}
	for i := range g.MPs {
		p := &g.MPs[i]
		if p.HasMethodID {
			continue
		}
		if t, ok := atLine[fileLineKey{p.FileID, p.Method(), p.Line}]; ok {
			p.MethodID = t
			p.HasMethodID = true
		}
	}

	uniq := make([]int32, n+1)
	for i := range g.Edges {
		uniq[g.Edges[i].Caller]++
	}
	for i := range g.Syms {
		s := g.Syms[i]
		c := &g.cold[i]

		w := g.coldWide[s.Id]
		g.setCold16(int32(s.Id), &c.NUniqueCalls, wNUniqueCalls, uniq[int(s.Id)])
		if COLD64(c.NTokens, w.NTokens) > 0 {
			d := COLD64(c.NDistinctOperators, w.NDistinctOperators) + COLD64(c.NDistinctOperands, w.NDistinctOperands)
			f := 2.0
			if d > 1 {
				f = 1.0 * float64(d)
			}
			g.halv[i] = int64(float64(COLD64(c.NOperators, w.NOperators)+COLD64(c.NOperands, w.NOperands)) * f)
		}
		switch s.Kind() {
		case "function", "method", "constructor", "closure":
			sl := 0.05
			if s.Sloc > 1 {
				sl = fmaBarrier(1.0 * float64(s.Sloc) / 20.0)
			}

			v := fmaBarrier(171-fmaBarrier(0.23*float64(s.Cyclomatic))) -
				fmaBarrier(16.2*sl)
			m := max(int32(math.Trunc(v)), 0)
			c.Maintainability = int16(m)
		}
		s.RiskScore = riskScore(s, c, w)
	}

	type fAgg struct{ syms, fns, types, cyclo, maxCyclo, risk int32 }
	fa := make([]fAgg, len(g.Files)+1)
	for _, s := range g.Syms {
		a := &fa[s.FileId]
		a.syms++
		switch s.Kind() {
		case "function", "method", "constructor", "closure":
			a.fns++
		case "class", "struct", "interface", "trait", "enum", "union",
			"record", "protocol", "type", "impl":
			a.types++
		}
		a.cyclo += s.Cyclomatic
		if s.Cyclomatic > a.maxCyclo {
			a.maxCyclo = s.Cyclomatic
		}
		a.risk += s.RiskScore
	}
	nImp := make([]int32, len(g.Files)+1)
	for i := range g.Imps {
		nImp[g.Imps[i].FileID]++
	}
	for _, f := range g.Files {
		a := fa[f.ID]
		f.NSymbols, f.NFunctions, f.NTypes = a.syms, a.fns, a.types
		f.TotalCyclo, f.MaxCyclo = a.cyclo, a.maxCyclo

		f.TotalRisk = 0
		f.NImports = nImp[f.ID]
	}

	type mAgg struct {
		syms, publics, files, sloc int32
	}
	ma := make([]mAgg, len(g.Mods)+1)
	for _, s := range g.Syms {
		if s.ModuleId == 0 {
			continue
		}
		a := &ma[s.ModuleId]
		a.syms++
		a.publics += s.IsPublic
	}
	for _, f := range g.Files {
		if f.ModuleID == 0 {
			continue
		}
		a := &ma[f.ModuleID]
		a.files++
		a.sloc += f.Sloc
	}
	inSet2 := make([]map[int32]bool, len(g.Mods)+1)
	outSet2 := make([]map[int32]bool, len(g.Mods)+1)
	for i := range g.Edges {
		e := &g.Edges[i]
		if e.Caller == e.Callee {
			continue
		}
		cs, ce := g.Syms[e.Caller-1], g.Syms[e.Callee-1]
		if cs.ModuleId == ce.ModuleId {
			continue
		}
		if int(cs.ModuleId) < len(inSet2) {
			if outSet2[cs.ModuleId] == nil {
				outSet2[cs.ModuleId] = map[int32]bool{}
			}
			outSet2[cs.ModuleId][ce.ModuleId] = true
		}
		if int(ce.ModuleId) < len(inSet2) {
			if inSet2[ce.ModuleId] == nil {
				inSet2[ce.ModuleId] = map[int32]bool{}
			}
			inSet2[ce.ModuleId][cs.ModuleId] = true
		}
	}
	for _, m := range g.Mods {
		a := ma[m.ID]
		m.NSymbols, m.NPublic, m.NFiles, m.Sloc = a.syms, a.publics, a.files, a.sloc
		if int(m.ID) < len(inSet2) {
			m.FanIn = int32(len(inSet2[m.ID]))
			m.FanOut = int32(len(outSet2[m.ID]))
		}
		if m.FanIn+m.FanOut != 0 {
			m.Instability = float64(m.FanOut) / float64(m.FanIn+m.FanOut)
		}
	}
}

func fmaBarrier(f float64) float64 { return f }

type fileNameKey struct {
	fid  int32
	name string
}

type fileLineKey struct {
	fid  int32
	name string
	line int32
}

const (
	wNDeserialize = iota
	wNMetaprogram
	wNCrypto
	wNConcurrency
	wNAlloc
	wNControl
	wNUniqueCalls
)

func (g *Graph) setCold16(id int32, dst *int16, fld int, v int32) {
	if x, ok := narrow16(v); ok {
		*dst = x
		return
	}
	w := g.coldWide[id]
	switch fld {
	case wNDeserialize:
		w.NDeserialize = v
	case wNMetaprogram:
		w.NMetaprogram = v
	case wNCrypto:
		w.NCrypto = v
	case wNConcurrency:
		w.NConcurrency = v
	case wNAlloc:
		w.NAlloc = v
	case wNControl:
		w.NControl = v
	case wNUniqueCalls:
		w.NUniqueCalls = v
	}
	g.coldWide[id] = w
}

func riskScore(s *Sym, c *symCold, w symColdWide) int32 {
	v := float64(s.Cyclomatic)*2 + float64(s.Cognitive) + float64(s.MaxNesting)*4 +
		float64(s.NEval)*30 + float64(s.NExec)*25 + float64(COLD64(c.NDeserialize, w.NDeserialize))*20 +
		float64(s.NMetaprogramDynamic)*10 + float64(s.NMetaprogramTotal)*3 +
		float64(s.NSqlInterp)*30 + float64(s.NPermitBang)*20
	if s.NParamsRead > 0 && s.NMassAssign > 0 && s.NPermit == 0 {
		v += 25
	}
	v += float64(s.NArQueryInBlock)*12 + float64(s.QueryInLoop)*10
	v += float64(s.NRescueBare)*6 + float64(s.NRescueException)*10 + float64(s.NRescueEmpty)*12
	v += float64(s.NMonkeyPatch)*8 + float64(s.NTimeout)*8
	v += float64(s.NClassLevelWrite)*10 + float64(s.NGlobalVar)*4
	v += float64(s.NThreadNew)*5 + float64(COLD64(c.NCrypto, w.NCrypto))*3
	if s.IsRecursive != 0 {
		v += 10
	}
	return int32(v)
}

func (b *builder) writeMeta() {
	g := b.g
	g.setMeta("schema_version", "1")
	g.setMeta("lang", "ruby")
	g.setMeta("target", "Ruby 4.0")
	abs, err := absPath(b.root)
	if err != nil {
		abs = b.root
	}
	g.setMeta("root", abs)
	g.setMeta("parse_mode", "tree-sitter")
	g.setMeta("parser", parserBanner())

	g.setMetaExt("built_at", time.Now().Format("2006-01-02T15:04:05"))
	g.setMeta("files_parsed", fmt.Sprint(b.nParsed))
	g.setMeta("files_failed", fmt.Sprint(b.nFailed))
	g.setMeta("files_skipped", fmt.Sprintf(
		"big=%d special=%d escaping_symlink=%d denied=%d walk_errors=%d",
		b.skipped.big, b.skipped.special, b.skipped.escape, b.skipped.denied,
		b.skipped.walkErr))
	if _, ok := findMeta(g, "ruby4_leading_operator_files"); !ok {
		g.setMeta("ruby4_leading_operator_files", "0")
	}
	sort.Slice(g.Meta, func(i, j int) bool { return g.Meta[i].K.Str() < g.Meta[j].K.Str() })
}

func findMeta(g *Graph, k string) (string, bool) {
	for i := range g.Meta {
		if g.Meta[i].K.Str() == k {
			return g.Meta[i].V.Str(), true
		}
	}
	return "", false
}

var _ = strings.TrimSpace

const (
	maxFileBytes = 4 * 1024 * 1024
	maxLineBytes = 1024 * 1024

	maxOperandSet = 1 << 15

	importQuoteChars = "\"'`:" + "`"
)

var (
	frozenRe  = regexp.MustCompile(`(?m)^#\s*frozen_string_literal:\s*true`)
	sqlRe     = regexp.MustCompile(`(?i)\b(SELECT\s|INSERT\s+INTO|UPDATE\s+\w|DELETE\s+FROM|FROM\s+\w+|WHERE\s|JOIN\s|ORDER\s+BY|GROUP\s+BY|HAVING\s|UNION\s|CREATE\s+TABLE|DROP\s+TABLE|ALTER\s+TABLE|TRUNCATE\s)`)
	secretRe  = regexp.MustCompile(`(?i)(api[_-]?key|apikey|secret|password|passwd|pwd|token|bearer|access[_-]?key|private[_-]?key|client[_-]?secret|auth[_-]?token|jwt|credential|smtp[_-]?pass|db[_-]?pass|sk_live|rk_live|pk_live|ghp_|xoxb-|AKIA)`)
	numRe     = regexp.MustCompile(`^[-+]?(?:0[xXbBoO][0-9a-fA-F_]+|[\d_]+(?:\.[\d_]*)?(?:[eE][-+]?\d+)?)[uUlLfFdD]*$`)
	ruby4Re   = regexp.MustCompile(`(?m)^\s*(?:&&|\|\||and\b|or\b)`)
	reraiseRe = regexp.MustCompile(`\b(raise|fail|throw)\b`)

	controllerRe = regexp.MustCompile(`<\s*(?:\w+::)*(?:ApplicationController|ActionController::(?:Base|API|Metal)|Devise::\w+Controller|InheritedResources::Base)\b`)
	modelRe      = regexp.MustCompile(`<\s*(?:\w+::)*(?:ApplicationRecord|ActiveRecord::Base|ActiveModel::Base)\b`)
	jobRe        = regexp.MustCompile(`(<\s*(?:\w+::)*(?:ApplicationJob|ActiveJob::Base)\b|\binclude\s+Sidekiq::(?:Worker|Job)\b|\binclude\s+Resque\b)`)
)

var magicNum = func() map[string]bool {
	m := map[string]bool{"0x0": true, "0x1": true, "0xff": true, "0xFF": true,
		"0.0": true, "1.0": true, "-1": true, "": true}
	for _, v := range []string{"0", "1", "2", "-1", "10", "100", "1000", "8",
		"16", "32", "64", "128", "256", "512", "1024", "255", "65535", "4096",
		"24", "60", "365", "7", "12", "3", "4", "6"} {
		m[v] = true
	}
	return m
}()

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

type inRec struct {
	text   string
	kind   string
	line   int32
	inLoop bool
}

type secRec struct {
	value string
	line  int32
}

type visRange struct {
	lo, hi int32
	vis    string
}

type fileOut struct {
	idx int32

	lines, sloc, blank, cmt, maxlen int32
	sha1                            string
	tooBig, denied                  bool
	parsed, isGen                   bool
	parseErrs, missing              int32

	syms   []symRow
	params []wParam
	fields []wField
	lits   []wLiteral
	marks  []wMarker
	imps   []wImport
	hazs   []wHazard
	rmods  []wRubyModule
	mixins []wMixin
	msites []wMetaSite
	blks   []wBlock
	arqs   []wARQuery
	arcbs  []wARCallback
	mps    []wMonkeyPatch
	uis    []wInputSite
	secs   []wSecret

	regNames []regName
	regQuals []regQual
	pend     []pendCall
	recs     []tsRec

	ruby4 bool
	fails bool
}

type wParam struct {
	SymID, Pos int32
	Name       string
	HasName    bool
	Type       string
	Default    string
	HasDefault bool
	Optional   int32
	Variadic   int32
	Ref        int32
	Mutable    int32
	Nullable   int32
	Generic    int32
	Untyped    int32
	TypeDepth  int32
}

type wField struct {
	SymID, Ord        int32
	Name, Type, Vis   string
	Line              int32
	Static, Const_    int32
	Mutable, Nullable int32
	Collection        int32
	Untyped           int32
	HasDefault        int32
	TypeDepth         int32
}

type wImport struct {
	ID, FileID  int32
	Target      string
	TargetID    int32
	HasTargetID bool
	Alias       string
	HasAlias    bool
	Kind        string
	Line        int32
	External    int32
	Relative    int32
	Wildcard    int32
	TypeOnly    int32
	Dynamic     int32
	NNames      int32
}

type wHazard struct {
	SymID     int32
	Pattern   string
	Category  string
	N         int32
	FirstLine int32
}

type wLiteral struct {
	ID, SymID int32
	FileID    int32
	Kind      string
	Value     string
	Line      int32
	Magic     int32
}

type wMarker struct {
	ID, FileID int32
	SymID      int32
	HasSym     bool
	Kind       string
	Line       int32
	Text       string
}

type wRubyModule struct {
	SymID, FileID           int32
	Name                    string
	IsModule                int32
	IsConcern               int32
	HasIncludedBlock        int32
	HasClassMethodsBlock    int32
	Superclass              string
	NMixins, NDefs          int32
	NClassDefs, NClassIvars int32
	NClassVars, NGlobals    int32
	NDelegates              int32
	ReopensCore             int32
	Line                    int32
}

type wMixin struct {
	ID, HostID       int32
	FileID           int32
	Host, Mixin      string
	MixinShort, Kind string
	InSingleton      int32
	Line             int32
}

type wMetaSite struct {
	ID, SymID   int32
	FileID      int32
	API, Arg    string
	Literal     int32
	FromParams  int32
	FromVar     int32
	OnHeredoc   int32
	InClassBody int32
	LoopDepth   int32
	Line        int32
}

type wBlock struct {
	ID, SymID     int32
	FileID        int32
	Method        string
	Receiver      string
	Style         string
	IsIteration   int32
	Depth         int32
	NParams       int32
	BodySloc      int32
	NQueries      int32
	NAllocs       int32
	CapturesOuter int32
	Line          int32
	NExits        int32
}

type wARQuery struct {
	ID, SymID        int32
	FileID           int32
	Model, API       string
	BuildKind        string
	HasInterpolation int32
	IsSanitized      int32
	FromParams       int32
	IsStringArg      int32
	LoopDepth, Chain int32
	Line             int32
}

type wARCallback struct {
	ID, SymID   int32
	FileID      int32
	Host, Hook  string
	Method      string
	Conditional int32
	Block       int32
	Association int32
	IssuesQuery int32
	TargetID    int32
	HasTargetID bool
	Line        int32
}

type wMonkeyPatch struct {
	ID, SymID   int32
	HasSym      bool
	MethodID    int32
	HasMethodID bool
	FileID      int32
	CoreClass   string
	Method      string
	Operator    int32
	Singleton   int32
	Line        int32
}

type wInputSite struct {
	ID, SymID int32
	FileID    int32
	Var       string
	Kind      string
	Line      int32
	InLoop    int32
}

type wSecret struct {
	ID, SymID int32
	FileID    int32
	Value     string
	Line      int32
}

type regName struct {
	name     string
	sid      int32
	fileID   int32
	typeName string
}

type regQual struct {
	qual string
	sid  int32
}

type pendCall struct {
	sid      int32
	line     int32
	name     string
	typeName string
}

type xctx struct {
	opt buildOpts
	src []byte
	rec *File
	rel string
	out *fileOut

	cur tsCursor

	ctrl, model, job int32
	frozen           int32
	vis              []visRange

	nextID int32

	st       symRow
	opStamp  []int32
	gen      int32
	opndGen  map[string]int32
	nOp      int32
	nOpnd    int32
	calls    []callRec
	lits     []litRec
	inputs   []inRec
	secrets  []secRec
	nestSt   []int32
	loopSt   []int32
	pendBlk  []wBlock
	pendMeta []wMetaSite
	pendAR   []wARQuery
	pendYld  int32

	blockD   []blockRow
	blkStack []int32
	exits    map[int32]int32
	iterSt   []int32
	scratch  []walkItem
	metaSt   []tsNode
}

type cbState struct {
	mixins, defs, cdefs, ivars, cvars, globals int32
	included, classMethods, concern, attrs     int32
	delegates                                  int32
}

type blockRow struct {
	enter                   int32
	method, receiver, style string
	isIter                  int32
	depth, nparams, sloc    int32
	line                    int32
}

func newXctx() *xctx {
	return &xctx{
		opStamp: make([]int32, 4096),
		opndGen: make(map[string]int32, 4096),
		exits:   make(map[int32]int32, 64),
	}
}

func cgStrip(s string) string {
	return strings.Trim(s, " \t\n\r\v\f\x1c\x1d\x1e\x1f\x85\xa0")
}

func splitLines(s string) []string {
	var out []string
	start := 0
	for i := 0; i < len(s); i++ {
		c := s[i]
		if c == '\n' {
			out = append(out, s[start:i])
			start = i + 1
			continue
		}
		if c < 0x80 {
			continue
		}
		r, sz := utf8.DecodeRuneInString(s[i:])
		if r == '\r' || r == '\v' || r == '\f' || r == 0x85 || r == 0x2028 || r == 0x2029 {
			out = append(out, s[start:i])
			if r == '\r' && i+1 < len(s) && s[i+1] == '\n' {
				i++
			}
			start = i + 1
			_ = sz
		}
	}
	if start < len(s) {
		out = append(out, s[start:])
	}
	return out
}

func trunc(s string, n int) string {
	if len(s) <= n {
		return s
	}
	i, c := 0, 0
	for i < len(s) {
		if c == n {
			return s[:i]
		}
		_, sz := utf8.DecodeRuneInString(s[i:])
		i += sz
		c++
	}
	return s
}

func isUpper(b byte) bool { return b >= 'A' && b <= 'Z' }

func (x *xctx) runFileWith(fo *fileOut, p *tsParser, fidx int32, f *File, full string) *fileOut {
	fo.idx = fidx
	x.out = fo
	x.rec = f
	x.rel = f.Path()
	x.nextID = 0
	x.vis = x.vis[:0]

	if len(x.opndGen) > maxOperandSet {
		x.opndGen = make(map[string]int32, 4096)
	}

	// x.src doubles as the reusable read buffer for this worker: the previous
	// file's extraction is finished, and no string extracted from it aliases
	// the bytes (textOf copies), so the buffer is dead.
	data, reuse, denied, tooBig := readCapped(full, maxFileBytes, maxLineBytes, x.src)
	x.src = reuse
	if denied {
		fo.denied = true
		fo.fails = true
		return fo
	}
	fo.tooBig = tooBig
	if data == nil {
		data = []byte{}
	}
	if len(data) == 0 {

		fo.sha1 = ""
	} else {
		sum := sha1.Sum(data)
		fo.sha1 = hex.EncodeToString(sum[:])
	}

	fo.lines, fo.sloc, fo.blank, fo.cmt, fo.maxlen = measureLines(data)
	if fo.tooBig || len(data) == 0 {
		return fo
	}

	head := data
	if len(head) > 2000 {
		head = head[:2000]
	}
	fo.isGen = isGeneratedFile(f.Base(), head)

	fo.parsed = (x.opt.includeTests || f.IsTest == 0) &&
		(x.opt.includeGenerated || !fo.isGen) &&
		(x.opt.includeVendored || f.IsVendored == 0)
	if !fo.parsed {
		return fo
	}

	x.src = data
	x.classifyRole(data)
	x.frozen = 0
	head800 := data
	if len(head800) > 800 {
		head800 = head800[:800]
	}
	if frozenRe.Match(head800) {
		x.frozen = 1
	}

	tree := p.parse(data)
	if tree == nil {

		return fo
	}
	if x.opt.keepTrees {
		fo.recs = append(fo.recs[:0], tree.recs...)
	}
	defer tree.free()
	root := tree.root()
	if hasErr(root) {
		var errs, miss int32
		countErrors(root, &errs, &miss)
		fo.nErr(root, errs, miss)
	}

	x.scanMarkers(data)
	x.parseImports(root)
	x.walkScope(root, 0, scope{})
	x.emitModuleScope(root)
	if hasErr(root) && ruby4Re.Match(data) {
		fo.ruby4 = true
	}
	return fo
}

func (fo *fileOut) nErr(root tsNode, errs, miss int32) {
	fo.parseErrs = errs
	fo.missing = miss
}

func forEachLine(b []byte, fn func([]byte)) {
	start := 0
	for i := 0; i < len(b); i++ {
		c := b[i]
		if c == '\n' {
			fn(b[start:i])
			start = i + 1
			continue
		}
		if c < 0x80 {
			continue
		}
		r, _ := utf8.DecodeRune(b[i:])
		if r != '\r' && r != '\v' && r != '\f' && r != 0x85 && r != 0x2028 && r != 0x2029 {
			continue
		}
		fn(b[start:i])
		if r == '\r' && i+1 < len(b) && b[i+1] == '\n' {
			i++
		}
		start = i + 1
	}
	if start < len(b) {
		fn(b[start:])
	}
}

func measureLines(b []byte) (lines, sloc, blank, cmt, maxlen int32) {
	forEachLine(b, func(line []byte) {
		lines++

		if n := int32(len(line)); n > maxlen {
			if r := int32(utf8.RuneCount(line)); r > maxlen {
				maxlen = r
			}
		}
		t := trimLeftBytes(line)
		if isBlank(t) {
			blank++
			return
		}
		sloc++
		if commentWindowBytes(t) {
			cmt++
		}
	})
	return
}

func isBlank(b []byte) bool {
	for _, c := range b {
		switch c {
		case ' ', '\t', '\n', '\r', '\v', '\f', 0x1c, 0x1d, 0x1e, 0x1f, 0x85, 0xa0:
		default:
			return false
		}
	}
	return true
}

func trimLeftBytes(b []byte) []byte {
	i := 0
	for ; i < len(b); i++ {
		switch b[i] {
		case ' ', '\t', '\n', '\r', '\v', '\f', 0x1c, 0x1d, 0x1e, 0x1f, 0x85, 0xa0:
		default:
			return b[i:]
		}
	}
	return b[i:]
}

func commentWindowBytes(b []byte) bool {

	var p [3]byte
	n := 0
	for i := 0; i < len(b) && n < 3; {
		_, sz := utf8.DecodeRune(b[i:])
		if sz == 0 {
			break
		}
		for j := 0; j < sz && n < 3; j++ {
			p[n] = b[i+j]
			n++
		}
		i += sz
	}
	head := string(p[:n])
	return slices.Contains(commentPrefixes, head)
}

func commentPrefixBytes(b []byte) bool {
	for _, pre := range commentPrefixes {
		if len(b) < len(pre) {
			continue
		}
		ok := true
		for i := 0; i < len(pre); i++ {
			if b[i] != pre[i] {
				ok = false
				break
			}
		}
		if ok {
			return true
		}
	}
	return false
}

func cgStripLeft(s string) string {
	return strings.TrimLeft(s, " \t\n\r\v\f\x1c\x1d\x1e\x1f\x85\xa0")
}

func countErrors(n tsNode, errs, miss *int32) {
	stack := []tsNode{n}
	for len(stack) > 0 {
		c := stack[len(stack)-1]
		stack = stack[:len(stack)-1]
		if nodeKindName(c) == "ERROR" {
			*errs++
		} else if isMissingN(c) {
			*miss++
		}
		// Walk the record chain; childAt(c, i) restarts at the first child.
		for cc, end := c.i+1, c.t.recs[c.i].subEnd; cc < end; cc = c.t.recs[cc].subEnd {
			stack = append(stack, tsNode{t: c.t, i: cc})
		}
	}
}

// readCapped reads path into buf, reusing its backing array (buf is owned by
// the calling worker's xctx and is dead once extraction of the file finishes:
// no extracted string aliases it). The (possibly regrown) buffer is returned
// as reuse so the caller can keep it for the next file.
func readCapped(path string, maxBytes, maxLine int64, buf []byte) (data, reuse []byte, denied, tooBig bool) {
	f, err := openFile(path)
	if err != nil {
		return nil, buf, true, false
	}
	defer f.Close()
	st, err := f.Stat()
	if err != nil {
		return nil, buf, true, false
	}
	if st.Size() > maxBytes {
		return nil, buf, false, true
	}
	buf = buf[:0]
	if cap(buf) < int(st.Size())+1 {
		buf = make([]byte, 0, int(st.Size())+1)
	}
	for {
		if len(buf) == cap(buf) {
			grow := cap(buf) / 2
			if grow < 4096 {
				grow = 4096
			}
			nb := make([]byte, len(buf), cap(buf)+grow)
			copy(nb, buf)
			buf = nb
		}
		n, err := f.Read(buf[len(buf):cap(buf)])
		buf = buf[:len(buf)+n]
		if err != nil {
			break
		}
	}
	if int64(len(buf)) > maxBytes {
		return buf, buf, false, true
	}

	longest := 0
	start := 0
	for i := 0; i < len(buf); i++ {
		if buf[i] == '\n' {
			if i-start > longest {
				longest = i - start
			}
			start = i + 1
		}
	}
	if len(buf)-start > longest {
		longest = len(buf) - start
	}
	if int64(longest) > maxLine {
		return buf, buf, false, true
	}
	return buf, buf, false, false
}

func (x *xctx) classifyRole(text []byte) {
	rel := x.rec.Path()
	x.ctrl, x.model, x.job = 0, 0, 0
	if strings.Contains(rel, "app/controllers/") || bytes.Contains(text, []byte("Controller")) ||
		bytes.Contains(text, []byte("InheritedResources::Base")) {
		if controllerRe.Match(text) {
			x.ctrl = 1
		}
	}
	if strings.Contains(rel, "app/models/") || bytes.Contains(text, []byte("Record")) ||
		bytes.Contains(text, []byte("ActiveModel::Base")) {
		if modelRe.Match(text) {
			x.model = 1
		}
	}
	if strings.Contains(rel, "app/jobs/") || strings.Contains(rel, "app/workers/") ||
		bytes.Contains(text, []byte("Job")) || bytes.Contains(text, []byte("Sidekiq")) ||
		bytes.Contains(text, []byte("Resque")) {
		if jobRe.Match(text) {
			x.job = 1
		}
	}
}

func (x *xctx) scanMarkers(data []byte) {
	if !hasMarkerWord(data) {
		return
	}
	line := int32(0)
	start := 0
	i := 0
	for i <= len(data) {
		if i == len(data) {
			if start < len(data) {
				line++
				x.addMarker(data[start:i], line)
			}
			break
		}
		c := data[i]
		if c == '\n' {
			line++
			x.addMarker(data[start:i], line)
			i++
			start = i
			continue
		}
		if c < 0x80 {
			i++
			continue
		}
		r, sz := utf8.DecodeRune(data[i:])
		if r == '\r' || r == '\v' || r == '\f' || r == 0x85 || r == 0x2028 || r == 0x2029 {
			line++
			x.addMarker(data[start:i], line)
			i += sz
			if r == '\r' && i < len(data) && data[i] == '\n' {
				i++
			}
			start = i
			continue
		}
		i += sz
	}
}

func (x *xctx) addMarker(l []byte, line int32) {
	for p := 0; p < len(l); p++ {
		if p > 0 && isWordByte(l[p-1]) {
			continue
		}
		w, ok := matchMarker(l, p, true)
		if !ok {
			continue
		}
		if !bytesContain(l, "//") && !bytesContain(l, "#") &&
			!bytesContain(l, "*") && !bytesContain(l, "--") {
			return
		}
		x.out.marks = append(x.out.marks, wMarker{
			Kind: strings.ToUpper(w),
			Line: line,
			Text: trunc(cgStrip(string(l)), 200),
		})
		return
	}
}

func hasMarkerWord(data []byte) bool {
	for p := 0; p < len(data); p++ {
		if !isWordByte(data[p]) {
			continue
		}
		if p > 0 && isWordByte(data[p-1]) {
			continue
		}
		if _, ok := matchMarker(data, p, false); ok {
			return true
		}
	}
	return false
}

func isWordByte(b byte) bool {
	return b >= 'a' && b <= 'z' || b >= 'A' && b <= 'Z' ||
		b >= '0' && b <= '9' || b == '_'
}

func foldByte(b byte) byte {
	if isUpper(b) {
		return b + 32
	}
	return b
}

var markerWords = []string{"TODO", "FIXME", "XXX", "HACK", "BUG", "NOTE",
	"WARNING", "OPTIMIZE", "REVIEW", "DEPRECATED", "SAFETY", "PANIC", "UNSAFE"}

var markerFirstByte = func() [256]bool {
	var m [256]bool
	for _, w := range markerWords {
		m[w[0]] = true
		m[w[0]+32] = true
	}
	return m
}()

func matchMarker(l []byte, p int, needSep bool) (string, bool) {
	if !markerFirstByte[l[p]] {
		return "", false
	}
	for _, w := range markerWords {
		if foldByte(l[p]) != foldByte(w[0]) {
			continue
		}
		e := p + len(w)
		if e > len(l) {
			continue
		}
		ok := true
		for k := 1; k < len(w); k++ {
			if foldByte(l[p+k]) != foldByte(w[k]) {
				ok = false
				break
			}
		}
		if !ok {
			continue
		}
		if e < len(l) && isWordByte(l[e]) {
			continue
		}
		if needSep {
			j := e
			for j < len(l) && (l[j] == ' ' || l[j] == '\t') {
				j++
			}
			if j >= len(l) || (l[j] != ':' && l[j] != '-' && l[j] != '(') {
				continue
			}
		}
		return string(l[p:e]), true
	}
	return "", false
}

func (x *xctx) parseImports(root tsNode) {
	src := x.src
	if !bytesContain(src, "require") && !bytesContain(src, "load") && !bytesContain(src, "gem") {
		return
	}
	x.cur.start(root)
	defer x.cur.done()
	first := true
	for {
		n := x.cur.node()
		if kindID(n) == kindCall {
			m := childField(n, fMethod)
			if hasNode(m) {
				kind := textOf(src, m)
				if inSet(requireKinds, kind) {
					args := childField(n, fArguments)
					if hasNode(args) && namedChildCount(args) > 0 {
						a0 := namedChildAt(args, 0)

						target := strings.Trim(textOf(src, a0), importQuoteChars)
						var ext, rel, dyn int32
						if kind == "require" || kind == "gem" {
							ext = 1
						}
						if kind == "require_relative" {
							rel = 1
						}
						if kind == "autoload" {
							dyn = 1
						}
						x.out.imps = append(x.out.imps, wImport{
							Target:   trunc(target, 300),
							Kind:     kind,
							Line:     int32(startRow(n) + 1),
							External: ext,
							Relative: rel,
							Dynamic:  dyn,
							NNames:   int32(namedChildCount(args)),
						})
					}
				}
			}
		}
		if first {
			first = false
		}
		if !advanceCursor(&x.cur) {
			break
		}
	}
}

func bytesContain(b []byte, s string) bool {
	return indexBytes(b, s) >= 0
}

func indexBytes(b []byte, s string) int {
	n := len(s)
	if n == 0 {
		return 0
	}
	c := s[0]
	for i := 0; i+n <= len(b); i++ {
		if b[i] == c && string(b[i:i+n]) == s {
			return i
		}
	}
	return -1
}

func advanceCursor(c *tsCursor) bool {
	if c.first() {
		return true
	}
	for !c.next() {
		if !c.up() {
			return false
		}
	}
	return true
}

var rubyExts = map[string]bool{
	".rb": true, ".rake": true, ".gemspec": true, ".ru": true,
	".jbuilder": true, ".arb": true,
}

var commonSkipDirs = newSet(
	".git", ".hg", ".svn", ".jj", ".idea", ".vscode", ".vs", ".claude",
	"node_modules", "bower_components", "vendor", "third_party", "thirdparty",
	"external", "externals", "deps", "Godeps", "_vendor",
	"__pycache__", ".mypy_cache", ".pytest_cache", ".ruff_cache", ".tox",
	".venv", "venv", "env", ".env", "virtualenv",
	"build", "_build", "dist", "out", "target", "bin", "obj", ".gradle",
	".next", ".nuxt", ".svelte-kit", ".parcel-cache", ".turbo", ".cache",
	"coverage", "htmlcov", ".nyc_output", "site-packages",
)

var rubySkipDirs = newSet(
	"vendor", "tmp", "log", "public", "db/migrate_backup",
	".bundle", "coverage", "node_modules",
)

var (
	testPathRe   = regexp.MustCompile(`(?i)(^|/)(tests?|test-d|spec|specs|__tests__|__snapshots__|testing|e2e|integration[-_]tests?|testdata|test_data|test-data|fixtures?)(/|$)`)
	rubyTestName = regexp.MustCompile(`(_spec\.rb$|_test\.rb$|^test_)`)
	vendorPathRe = regexp.MustCompile(`(?i)(^|/)(vendor|third_party|thirdparty|external|node_modules|deps)(/|$)`)
	genNameRe    = regexp.MustCompile(`(?i)(\.min\.|\.bundle\.|[-_.](gen|generated|pb|g)\.|_pb2|\.g\.dart$|\.designer\.|^zz_generated)`)
	exampleRe    = regexp.MustCompile(`(?i)(^|/)(examples?|samples?|demos?)(/|$)`)
	toolRe       = regexp.MustCompile(`(?i)(^|/)(tools?|scripts?|cmd|bin)(/|$)`)
)

var genMarkers = [][]byte{
	[]byte("@generated"), []byte("DO NOT EDIT"), []byte("Code generated by"),
	[]byte("AUTO-GENERATED"), []byte("autogenerated"),
	[]byte("This file was automatically generated"),
	[]byte("Generated by the protocol buffer compiler"),
	[]byte("@flow-generated"),
}

func isGeneratedFile(name string, head []byte) bool {
	if genNameRe.MatchString(name) {
		return true
	}
	for _, m := range genMarkers {
		if bytes.Contains(head, m) {
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
	return strings.Join(head, "/")
}

func moduleKind(name string) string {
	switch {
	case testPathRe.MatchString(name):
		return "test"
	case vendorPathRe.MatchString(name):
		return "vendor"
	case exampleRe.MatchString(name):
		return "example"
	case toolRe.MatchString(name):
		return "tool"
	}
	return "source"
}

func splitExt(fn string) (string, string) {
	i := strings.LastIndexByte(fn, '.')
	if i <= 0 {
		return fn, ""
	}
	return fn[:i], fn[i:]
}

type discovery struct {
	files     []*File
	skip      skipCounts
	realRoot  string
	modByName map[string]int32
}

type skipCounts struct{ big, special, escape, denied, walkErr int }

func openFile(p string) (*os.File, error) { return os.Open(p) }

func mustReal(p string) string {
	if r, err := filepath.EvalSymlinks(p); err == nil {
		return r
	}
	return p
}

func (d *discovery) walkAll(root string) { d.walk(root, root) }

func (d *discovery) walk(root, dir string) {
	ents, err := os.ReadDir(dir)
	if err != nil {
		d.skip.walkErr++
		return
	}
	var subs []string
	for _, e := range ents {
		name := e.Name()
		if e.IsDir() {
			if commonSkipDirs[name] || rubySkipDirs[name] || strings.HasPrefix(name, ".") {
				continue
			}
			if e.Type()&os.ModeSymlink != 0 {
				continue
			}
			subs = append(subs, name)
			continue
		}
		base, ext := splitExt(name)
		_ = base
		if !rubyExts[ext] {
			continue
		}
		full := filepath.Join(dir, name)
		st, err := os.Lstat(full)
		if err != nil {
			d.skip.denied++
			continue
		}
		if !st.Mode().IsRegular() {

			d.skip.special++
			continue
		}
		rel, err := filepath.Rel(root, full)
		if err != nil {
			continue
		}

		if real := mustReal(full); real != full && !strings.HasPrefix(real, d.realRoot+string(filepath.Separator)) {
			d.skip.escape++
			continue
		}
		isTest := bool(testPathRe.MatchString(rel)) || rubyTestName.MatchString(name)
		isVend := vendorPathRe.MatchString(rel)
		modName := moduleOf(rel)
		mid := d.modID(modName)
		id := int32(len(d.files) + 1)
		dirn := filepath.Dir(rel)
		if dirn == "." {
			dirn = "."
		}
		f := &File{}
		cgZeroRow(unsafe.Pointer(f), unsafe.Sizeof(*f))
		f.ID = id
		f.path = cgPut(rel)
		f.dir = cgPut(dirn)
		f.base = cgPut(name)
		f.ext = cgPut(ext)
		f.lang = cgPut("ruby")
		f.ModuleID = mid
		f.Bytes = int32(minI64(st.Size(), 1<<31-1))
		f.IsTest = b2i(isTest)
		f.IsVendored = b2i(isVend)
		d.files = append(d.files, f)
	}
	sort.Strings(subs)
	for _, s := range subs {
		d.walk(root, filepath.Join(dir, s))
	}
}

func (d *discovery) modID(name string) int32 {
	if id, ok := d.modByName[name]; ok {
		return id
	}
	d.modByName[name] = int32(len(d.modByName) + 1)
	return d.modByName[name]
}

func minI64(a int64, b int64) int64 {
	if a < b {
		return a
	}
	return b
}

type pair struct{ a, b int32 }

type nameKey struct {
	sid  int32
	name string
}

type resolver struct {
	g      *Graph
	unique map[string]int32
	fileSc map[pair]int32
	qual   map[string]int32
	loc    []int64
	extBy  map[int32]int32

	edgeIdx  map[pair]int32
	unresIdx map[nameKey]int32
	sites    []CallSite

	nExt, nRes, nUnres int32
}

func (b *builder) resolve() {
	g := b.g
	nPend := 0
	for _, c := range b.pendChunks {
		nPend += len(c)
	}
	r := &resolver{
		g:        g,
		unique:   make(map[string]int32, 1024),
		fileSc:   make(map[pair]int32, 8192),
		qual:     make(map[string]int32, 8192),
		extBy:    make(map[int32]int32, 1024),
		edgeIdx:  make(map[pair]int32, nPend),
		unresIdx: make(map[nameKey]int32, nPend/4+16),
		loc:      make([]int64, len(g.Syms)+1),
	}

	byName := make(map[string][]regName, 4096)
	for _, rn := range b.regNames {
		byName[rn.name] = append(byName[rn.name], rn)
	}
	for nm, lst := range byName {
		if len(lst) == 1 {
			r.unique[nm] = lst[0].sid
		}
		for _, c := range lst {
			k := pair{c.sid, c.fileID}
			if _, ok := r.fileSc[k]; !ok {
				r.fileSc[k] = c.sid
			}
		}
	}
	for _, rq := range b.regQuals {
		r.qual[rq.qual] = rq.sid
	}

	owner := make(map[int32]string, 4096)
	for _, rn := range b.regNames {
		if rn.typeName != "" {
			owner[rn.sid] = rn.typeName
		}
	}
	for _, s := range g.Syms {
		r.loc[s.Id] = int64(s.FileId)<<32 | int64(s.ModuleId)
	}
	typeTable := make(map[string]int32, 1024)
	for _, s := range g.Syms {
		ty := owner[s.Id]
		if ty == "" {
			continue
		}
		k := ty + "\x00" + s.Name()
		if _, ok := typeTable[k]; !ok {
			typeTable[k] = s.Id
		}
	}

	fileBySym := make([]int32, len(g.Syms)+1)
	for _, s := range g.Syms {
		fileBySym[s.Id] = s.FileId
	}
	fileTable := make(map[int64]int32, 8192)
	for nm, lst := range byName {
		for _, c := range lst {
			k := int64(c.fileID)<<32 | int64(hashStr(nm))
			if _, ok := fileTable[k]; !ok {
				fileTable[k] = c.sid
			}
		}
	}

	for ci := range b.pendChunks {
		chunk := b.pendChunks[ci]
		for i := range chunk {
			p := &chunk[i]
			name := normaliseCallee(p.name)
			if name == "" {
				continue
			}
			base := name
			if i := strings.LastIndexAny(name, ".:"); i >= 0 {
				base = name[i+1:]
			}
			var target int32
			if p.typeName != "" {
				target = typeTable[p.typeName+"\x00"+base]
			}
			if target == 0 {
				target = r.qual[name]
			}
			if target == 0 {
				target = fileTable[int64(fileBySym[p.sid])<<32|int64(hashStr(base))]
			}
			if target == 0 {
				target = r.unique[base]
			}
			if target == 0 {
				if isExternalName(name, base) {
					r.extBy[p.sid]++
					r.nExt++
				} else {
					nm := trunc(name, 160)
					k := nameKey{p.sid, nm}
					if i, ok := r.unresIdx[k]; ok {
						g.Unres[i].N++
					} else {
						r.unresIdx[k] = int32(len(g.Unres))
						g.Unres = append(g.Unres, Unresolved{})
						u := &g.Unres[len(g.Unres)-1]
						cgZeroRow(unsafe.Pointer(u), unsafe.Sizeof(*u))
						u.Caller = p.sid
						u.name = cgPut(nm)
						u.N = 1
						u.FirstLine = p.line
					}
					r.nUnres++
				}
				continue
			}
			k := pair{p.sid, target}
			if i, ok := r.edgeIdx[k]; ok {
				g.Edges[i].NCalls++
			} else {
				cl := r.loc[p.sid]
				tl := r.loc[target]
				r.edgeIdx[k] = int32(len(g.Edges))
				g.Edges = append(g.Edges, Edge{
					Caller: p.sid, Callee: target, NCalls: 1,
					SameFile:   b2i(cl>>32 == tl>>32),
					SameModule: b2i(uint32(cl) == uint32(tl)),
					Self:       b2i(p.sid == target),
				})
			}
			if p.line != 0 {
				r.sites = append(r.sites, CallSite{Caller: p.sid, Callee: target, Line: p.line})
			}
			r.nRes++
		}
	}
	for sid, v := range r.extBy {
		if int(sid) <= len(g.Syms) {
			g.Syms[sid-1].NExternalCalls = v
		}
	}

	sort.Slice(r.sites, func(i, j int) bool { return siteLess(r.sites[i], r.sites[j]) })
	for i, s := range r.sites {
		if i > 0 && r.sites[i-1] == s {
			continue
		}
		g.Sites = append(g.Sites, s)
	}
	g.setMeta("calls_resolved", fmt.Sprintf(
		"%d in-tree / %d external / %d unresolved (%d%% of in-scope resolved)",
		r.nRes, r.nExt, r.nUnres, 100*r.nRes/maxI32(1, r.nRes+r.nUnres)))
}

func siteLess(a, b CallSite) bool {
	if a.Caller != b.Caller {
		return a.Caller < b.Caller
	}
	if a.Callee != b.Callee {
		return a.Callee < b.Callee
	}
	return a.Line < b.Line
}

func maxI32(a, b int32) int32 {
	if a > b {
		return a
	}
	return b
}

func hashStr(s string) uint32 {
	var h uint32 = 2166136261
	for i := 0; i < len(s); i++ {
		h ^= uint32(s[i])
		h *= 16777619
	}
	return h
}

func normaliseCallee(raw string) string {
	n := cgStrip(raw)
	if strings.HasSuffix(n, ".new") {
		recv := n[:len(n)-4]
		last := recv
		if i := strings.LastIndex(recv, "::"); i >= 0 {
			last = recv[i+2:]
		}
		if i := strings.LastIndex(last, "."); i >= 0 {
			last = last[i+1:]
		}
		if len(last) > 0 && isUpper(last[0]) {
			return last
		}
	}
	return n
}

func isExternalName(name, base string) bool {
	head := name
	if i := strings.IndexAny(name, ".:"); i >= 0 {
		head = name[:i]
	}
	if inSet(coreReceivers, head) {
		return true
	}
	if inSet(coreMethods, base) && !strings.Contains(name, ".") {
		return true
	}
	if inSet(coreMethods, base) && head != "" && head[0] >= 'a' && head[0] <= 'z' {
		return true
	}
	if strings.HasPrefix(head, "@") || head == "self" {
		return false
	}
	return false
}

var importSuffixes = []string{"", ".py", ".pyi", ".ts", ".tsx", ".d.ts", ".mts",
	".cts", ".js", ".jsx", ".mjs", ".cjs", ".rb", ".php", ".go", ".rs", ".java"}
var importIndexes = []string{"__init__.py", "index.ts", "index.tsx", "index.js",
	"index.mjs", "mod.rs", "lib.rs"}

func (b *builder) resolveImports() {
	g := b.g
	byPath := make(map[string]int32, len(g.Files)*2)
	for _, f := range g.Files {
		norm := filepath.ToSlash(f.Path())
		byPath[norm] = f.ID
		if i := strings.LastIndexByte(norm, '.'); i > 0 {
			if _, ok := byPath[norm[:i]]; !ok {
				byPath[norm[:i]] = f.ID
			}
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
	var n int32
	for i := range g.Imps {
		im := &g.Imps[i]
		if im.TargetID != 0 || im.Target() == "" {
			continue
		}
		t := strings.Trim(filepath.ToSlash(im.Target()), "/")

		here := cgDirname(g.Files[im.FileID-1].Path())
		var hit int32
		if strings.HasPrefix(t, ".") {
			nUp := len(t) - len(strings.TrimLeft(t, "."))
			rest := t[nUp:]
			if strings.Contains(rest, "/") {
				rest = strings.TrimLeft(rest, "./")
			} else {
				rest = strings.ReplaceAll(rest, ".", "/")
			}
			base := here
			for k := 0; k < nUp-1 && k < 16; k++ {
				base = cgDirname(base)
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
			im.HasTargetID = true
			n++
		}
	}
	g.setMeta("imports_resolved", fmt.Sprintf(
		"%d of %d import rows point at a file in this tree", n, len(g.Imps)))
}

func cgDirname(p string) string {
	i := strings.LastIndexByte(p, '/')
	if i < 0 {
		return ""
	}
	if i == 0 {
		return "/"
	}
	return p[:i]
}

const secretMinLen = 12

var dynamicDispatch = map[string]bool{
	"send": true, "public_send": true, "__send__": true, "eval": true,
	"instance_eval": true, "class_eval": true, "module_eval": true,
	"instance_exec": true, "define_method": true, "const_get": true,
	"constantize": true, "safe_constantize": true, "method": true,
}

func (x *xctx) onCall(n tsNode, loopDepth int32) {
	x.bump(cCallSite)
	if loopDepth > 0 {
		x.bump(cCallInLoop)
	}
	m := childField(n, fMethod)
	if !hasNode(m) {
		x.bump(cDynamicCall)
		x.calls = append(x.calls, callRec{"", int32(startRow(n) + 1), true, loopDepth > 0})
		return
	}
	src := x.src
	meth := cgStrip(textOf(src, m))
	recv := childField(n, fReceiver)
	full := meth
	if hasNode(recv) {
		rt := kindID(recv)
		switch {
		case simpleReceiver(rt):
			full = trunc(cgStrip(textOf(src, recv)), 80) + "." + meth
		case rt == kindCall:
			if inner := childField(recv, fMethod); hasNode(inner) {
				full = trunc(cgStrip(textOf(src, inner)), 40) + "." + meth
			}
		case rt == kindStr:
			full = "String#" + meth
		}
	}
	line := int32(startRow(n) + 1)

	switch meth {
	case "system", "exec", "spawn", "syscall":
		x.bump(cSystemCall)
	case "redirect_to":
		x.bump(cRedirect)
	case "constantize", "safe_constantize":
		x.bump(cConstantize)
	case "html_safe", "raw":
		x.bump(cHtmlSafe)
	case "find_by_sql", "execute", "select_all", "select_values":
		x.bump(cRawSQL)
	case "md5", "sha1":
		x.bump(cWeakHash)
	case "rand", "srand":
		x.bump(cWeakRandom)
	}
	if hasPrefixAny(full, "Net::HTTP.", "HTTParty.", "Faraday.", "RestClient.", "OpenURI.") {
		x.bump(cFetch)
	}
	if hasPrefixAny(full, "Nokogiri.", "REXML::") {
		x.bump(cXxeParser)
	}
	if (meth == "open" || meth == "read" || meth == "binread") && strings.HasPrefix(full, "File.") {
		args := childField(n, fArguments)
		if hasNode(args) && namedChildCount(args) > 0 {
			first := namedChildAt(args, 0)
			if kindID(first) != kindStr {
				x.bump(cDynamicOpen)
			}
		}
	}
	if strings.HasPrefix(full, "Zip::") {
		x.bump(cZipRead)
	}
	if inSet(logLevels, meth) && strings.Contains(strings.ToLower(full), "logger") {
		x.bump(cLogCall)
	}

	low := strings.ToLower(full + " " + meth)
	authed := false
	for _, k := range authMarkers {
		if strings.Contains(low, k) {
			authed = true
			break
		}
	}
	if authed {
		x.bump(cAuthCall)
	} else {
		switch meth {
		case "open":
			x.bump(cOpenCall)
		case "sleep":
			x.bump(cSleepCall)
		}
	}
	if loopDepth > 0 {
		switch meth {
		case "include?":
			x.bump(cIncludeInLoop)
		case "map", "select", "reject", "each", "detect":
			x.bump(cEnumInLoop)
		case "count", "size", "length":
			x.bump(cCountInLoop)
		case "save", "save!", "update", "create", "destroy":
			x.bump(cArWriteInLoop)
		case "to_json", "to_yaml", "to_s":
			x.bump(cSerializeInLoop)
		}
	}

	if col, ok := metaprogramAPIs[meth]; ok {
		setCount(&x.st, counterOf(col), x.stOf(col)+1)
		x.bump(cMetaprogramTotal)
	} else if col, ok := metaprogramAPIs[full]; ok {
		setCount(&x.st, counterOf(col), x.stOf(col)+1)
		x.bump(cMetaprogramTotal)
	}

	switch {
	case meth == "block_given?":
		x.bump(cBlockGiven)
	case meth == "raise" || meth == "fail":
		x.bump(cRaise)
	case meth == "freeze":
		x.bump(cFreeze)
	case meth == "dup" || meth == "clone":
		x.bump(cDupClone)
	case full == "Proc.new":
		x.bump(cProcNew)
	case (meth == "lambda" || meth == "proc") && !hasNode(recv):
		x.bump(cLambdaCall)
	case full == "Thread.new" || full == "Thread.start":
		x.bump(cThreadNew)
	case full == "Mutex.new" || full == "Monitor.new":
		x.bump(cMutex)
	case strings.HasPrefix(full, "Ractor."):
		x.bump(cRactor)
	case full == "Thread.current":
		x.bump(cThreadLocal)
	case full == "Timeout.timeout" || (meth == "timeout" && !hasNode(recv)):
		x.bump(cTimeout)
	case meth == "permit":
		x.bump(cPermit)
	case meth == "permit!":
		x.bump(cPermit)
		x.bump(cPermitBang)
	case strings.HasPrefix(meth, "sanitize_sql"):
		x.bump(cSqlSanitized)
	}
	if inSet(massAssignSinks, meth) {
		x.bump(cMassAssignSink)
	}
	if inSet(arRelation, meth) || inSet(arTerminal, meth) || inSet(arWrite, meth) || inSet(arRaw, meth) {
		x.bump(cArQuery)
		if inSet(arTerminal, meth) {
			x.bump(cArTerminal)
		} else if inSet(arWrite, meth) {
			x.bump(cArWrite)
		}
	}

	if meth == "to_sym" || meth == "to_proc" {
		x.bump(cToSym)
	}
	if full == "Regexp.new" || full == "Regexp.compile" {
		x.bump(cRegexDyn)
	}
	if inSet(enqueueAPIs, meth) {
		x.bump(cEnqueue)
	}
	if full == "Time.now" || full == "DateTime.now" {
		x.bump(cZonelessTime)
	}
	if hasNode(recv) && (kindID(recv) == kindConst || kindID(recv) == kindScopeRs) &&
		inSet(constMutateAPIs, meth) {
		x.bump(cConstMutate)
	}
	if meth == "join" || meth == "value" || meth == "value!" {
		args := childField(n, fArguments)
		if !hasNode(args) || namedChildCount(args) == 0 {
			x.bump(cThreadJoin)
		}
	}

	dynamic := dynamicDispatch[meth]
	x.calls = append(x.calls, callRec{trunc(full, 200), line, dynamic, loopDepth > 0})
	if dynamic {
		x.bump(cDynamicCall)
	}
	if loopDepth > 0 {
		base := full
		if i := strings.LastIndex(full, "."); i >= 0 {
			base = full[i+1:]
		}
		for _, lc := range loopCallColumns {
			if lc[0] == base || lc[0] == full {
				x.bump(counterOf(lc[1]))
			}
		}
	}
}

func (x *xctx) stOf(col string) int32 {
	switch counterOf(col) {
	case cSend:
		return x.st.NSend
	case cDefineMethod:
		return x.st.NDefineMethod
	case cMethodMissing:
		return x.st.NMethodMissing
	case cConstGet:
		return x.st.NConstGet
	case cInstanceEval:
		return x.st.NInstanceEval
	case cClassEval:
		return x.st.NClassEval
	case cInstanceVarGet:
		return x.st.NInstanceVarGet
	case cEval:
		return x.st.NEval
	case cMetaOther:
		return x.st.NMetaprogramOther
	}
	panic("codegraph-ruby: metaprogram column outside the known set: " + col)
}

func (x *xctx) onString(n tsNode, text string, loopDepth int32) {

	val := strings.Trim(text, "\"'")
	if len(val) >= secretMinLen && !strings.Contains(val, " ") && secretRe.MatchString(val) {
		x.secrets = append(x.secrets, secRec{trunc(val, 200), int32(startRow(n) + 1)})
	}
	if !sqlRe.MatchString(text) {
		return
	}
	x.bump(cSqlLiteral)
	for i, m := 0, namedChildCount(n); i < m; i++ {
		if kindID(namedChildAt(n, i)) == kindInterp {
			x.bump(cSqlInterp)
			break
		}
	}
	if loopDepth > 0 {
		x.bump(cQueryInLoop)
	}
}

func (x *xctx) onNode(n tsNode, loopDepth int32) {
	src := x.src
	switch tkOf(kindID(n)) {
	case kindIdent:
		if endByte(n)-startByte(n) <= 6 {
			switch textOf(src, n) {
			case "params":
				x.bump(cParamsRead)
			case "raise", "fail":
				x.bump(cRaise)
			case "retry":
				x.bump(cRetry)
			}
		}
	case kindRescue:
		exc := childField(n, fExceptions)
		body := childField(n, fBody)
		if !hasNode(exc) {
			x.bump(cRescueBare)
		} else if strings.Contains(textOf(src, exc), "Exception") {
			x.bump(cRescueException)
		}
		if !hasNode(body) || namedChildCount(body) == 0 {
			x.bump(cRescueEmpty)
		} else if reraiseRe.MatchString(textOf(src, body)) {
			x.bump(cRescueReraise)
		}
	case kindRescMod:
		x.bump(cRescueBare)
		if h := childField(n, fHandler); hasNode(h) && kindID(h) == kindNilNode {
			x.bump(cRescueEmpty)
		}
	case kindBlockAr:
		if namedChildCount(n) > 0 {
			kk := kindID(namedChildAt(n, 0))
			if kk == kindSym || kk == kindDelim {
				x.bump(cSymbolToProc)
			}
		}
	case kindElemRef:
		obj := childField(n, fObject)
		if hasNode(obj) {
			o := textOf(src, obj)
			if o == "params" {
				x.bump(cParamsRead)
			}
			kind := reqIndexKinds[o]
			if kind == "" && strings.HasPrefix(o, "request.") {
				kind = reqMemberKinds[o[len("request."):]]
			}
			if kind != "" {
				x.inputs = append(x.inputs, inRec{
					trunc(textOf(src, n), 120), kind,
					int32(startRow(n) + 1), loopDepth > 0})
			}
		}
	case kindSubsh:
		x.calls = append(x.calls, callRec{"`backticks`", int32(startRow(n) + 1), true, loopDepth > 0})
	case kindHeredoc:
		txt := textOf(src, n)
		if sqlRe.MatchString(txt) {
			x.bump(cSqlLiteral)
			if strings.Contains(txt, "#{") {
				x.bump(cSqlInterp)
			}
		}
	case kindBin:

		left := childField(n, fLeft)
		op := childField(n, fOperator)
		if hasNode(left) && hasNode(op) &&
			(kindID(left) == kindConst || kindID(left) == kindScopeRs) &&
			cgStrip(textOf(src, op)) == "<<" {
			x.bump(cConstMutate)
		}
	case kindRegex:
		for i, m := 0, namedChildCount(n); i < m; i++ {
			if kindID(namedChildAt(n, i)) == kindInterp {
				x.bump(cRegexDyn)
				break
			}
		}
	case kindAssign, kindOpAsgn:
		if left := childField(n, fLeft); hasNode(left) {
			lt := kindID(left)
			if lt == kindClassVar || lt == kindGlobalVar {
				x.bump(cClassLevelWrite)
			}
		}
	}
}

func (x *xctx) scanBody(n tsNode) {
	x.pendBlk = x.pendBlk[:0]
	x.pendMeta = x.pendMeta[:0]
	x.pendAR = x.pendAR[:0]
	x.pendYld = 0

	if params := childField(n, fParams); hasNode(params) {
		x.cur.start(params)
		first := true
		for {
			c := x.cur.node()
			if kindID(c) == kindCall {
				if pm := childField(c, fMethod); hasNode(pm) && endByte(pm)-startByte(pm) == 12 {
					x.pendYld = 1
				}
			}
			if first {
				first = false
			}
			if !advanceCursor(&x.cur) {
				break
			}
		}
		x.cur.done()
	}

	body := childField(n, fBody)
	if !hasNode(body) {
		return
	}
	src := x.src
	singleton := kindID(n) == kindSingl || inSingletonClass(n)
	x.blockD = x.blockD[:0]
	for k := range x.exits {
		delete(x.exits, k)
	}
	x.iterSt = x.iterSt[:0]

	x.blkStack = x.blkStack[:0]
	x.cur.start(body)
	depth := int32(0)
	maxBlock := int32(0)
	first := true
	for {
		nd := x.cur.node()
		for len(x.iterSt) > 0 && x.iterSt[len(x.iterSt)-1] >= depth {
			x.iterSt = x.iterSt[:len(x.iterSt)-1]
		}
		for len(x.blkStack) > 0 && x.blockD[x.blkStack[len(x.blkStack)-1]].enter >= depth {
			x.blkStack = x.blkStack[:len(x.blkStack)-1]
		}
		idepth := int32(len(x.iterSt))

		switch kindID(nd) {
		case kindCall:
			if mn := childField(nd, fMethod); hasNode(mn) {
				meth := textOf(src, mn)
				if endByte(mn)-startByte(mn) == 12 {
					x.pendYld = 1
				}
				if meth == "throw" {
					for _, bi := range x.blkStack {
						x.exits[bi]++
					}
				}
				x.callDetail(nd, meth, idepth, singleton)
			}
		case kindDoBlock, kindBlock:
			meth, recv := "", ""
			if par := parentNode(nd); hasNode(par) && kindID(par) == kindCall {
				if mn := childField(par, fMethod); hasNode(mn) {
					meth = textOf(src, mn)
				}
				if rn := childField(par, fReceiver); hasNode(rn) {

					if simpleReceiver(kindID(rn)) || kindID(rn) == kindCall {
						recv = trunc(textOf(src, rn), 60)
					}
				}
			}
			isIter := inSet(iterMethods, meth)
			if isIter {
				x.iterSt = append(x.iterSt, depth)
				if int32(len(x.iterSt)) > maxBlock {
					maxBlock = int32(len(x.iterSt))
				}
				x.bump(cIterBlocks)
			}
			np := int32(0)
			if ps := childField(nd, fParams); hasNode(ps) {
				np = int32(namedChildCount(ps))
			}
			style := "brace"
			if kindID(nd) == kindDoBlock {
				style = "do_end"
			}
			d := int32(0)
			if isIter {
				d = 1
			}
			x.blockD = append(x.blockD, blockRow{
				enter:  depth,
				method: trunc(meth, 60), receiver: recv, style: style,
				isIter: b2i(isIter), depth: idepth + d, nparams: np,
				sloc: int32(endRow(nd) - startRow(nd) + 1),
				line: int32(startRow(nd) + 1),
			})
			x.blkStack = append(x.blkStack, int32(len(x.blockD)-1))
		case kindReturn, kindBreak, kindReturnAnon, kindBreakAnon:

			for _, bi := range x.blkStack {
				x.exits[bi]++
			}
		case kindYield:
			x.pendYld = 1
		case kindArray, kindHash, kindStrArray, kindSymArray:
			if idepth > 0 {
				x.bump(cCollectionLitInLoop)
			}
		case kindStr, kindHeredoc:

			if idepth > 0 {
				x.bump(cStrLitInLoop)
			}
		case kindInstanceVar:
			if singleton {
				x.bump(cClassLevelIvar)
			}
		}

		if first {
			first = false
		}
		if x.cur.first() {
			depth++
			continue
		}
		done := false
		for !x.cur.next() {
			if !x.cur.up() {
				done = true
				break
			}
			depth--
		}
		if done {
			for i, b := range x.blockD {
				x.pendBlk = append(x.pendBlk, wBlock{
					Method: b.method, Receiver: b.receiver, Style: b.style,
					IsIteration: b.isIter, Depth: b.depth, NParams: b.nparams,
					BodySloc: b.sloc, Line: b.line, NExits: x.exits[int32(i)],
				})
			}
			setCount(&x.st, cMaxBlockDepth, maxBlock)
			return
		}
	}
}

func b2i(b bool) int32 {
	if b {
		return 1
	}
	return 0
}

func (x *xctx) callDetail(n tsNode, meth string, idepth int32, singleton bool) {
	src := x.src
	recv := childField(n, fReceiver)
	args := childField(n, fArguments)
	line := int32(startRow(n) + 1)

	if inSet(chainAlloc, meth) && hasNode(recv) && kindID(recv) == kindCall {
		if inner := childField(recv, fMethod); hasNode(inner) {
			it := textOf(src, inner)
			if inSet(chainAlloc, it) {
				x.bump(cChainArrayAlloc)
				if meth == "map" || meth == "collect" || it == "map" || it == "collect" {
					x.bump(cMapChain)
				}
			}
			if (meth == "map" || meth == "collect") && it == "times" {
				x.bump(cTimesMap)
			}
		}
	}

	if meth == "include?" && hasNode(recv) {
		rt := kindID(recv)
		if rt == kindRange || (rt == kindParenStmt && hasChildKind(recv, kindRange)) {
			x.bump(cRangeInclude)
		}
	}

	if meth == "save" && (!hasNode(recv) || kindID(recv) != kindCall) {
		if par := parentNode(n); hasNode(par) {
			switch kindID(par) {
			case kindExprStmt, kindBodyStmt, kindDoNode, kindThen:
				x.bump(cSaveIgnored)
			}
		}
	}

	if (meth == "first" || meth == "flatten" || meth == "each") && hasNode(recv) {
		rt := trunc(textOf(src, recv), 120)
		if (meth == "first" && strings.Contains(rt, "select")) ||
			(meth == "flatten" && strings.Contains(rt, "map")) ||
			(meth == "each" && strings.Contains(rt, "reverse")) {
			x.bump(cLegacyChain)
		}
	}

	if _, ok := metaprogramAPIs[meth]; ok {
		arg, literal, fromParams, fromVar, heredoc := "", int32(0), int32(0), int32(0), int32(0)
		if hasNode(args) && namedChildCount(args) > 0 {
			a0 := namedChildAt(args, 0)
			atxt := textOf(src, a0)
			arg = trunc(atxt, 120)
			switch k := kindID(a0); {
			case k == kindSimSym || k == kindDelim:
				literal = 1
			case k == kindStr && !hasChildKind(a0, kindInterp):
				literal = 1
			case k == kindHeredB:
				heredoc = 1
			default:
				fromVar = 1
			}
			if strings.Contains(atxt, "params") {
				fromParams = 1
			}
		}
		x.pendMeta = append(x.pendMeta, wMetaSite{
			API: trunc(meth, 40), Arg: arg, Literal: literal,
			FromParams: fromParams, FromVar: fromVar, OnHeredoc: heredoc,
			InClassBody: b2i(singleton), LoopDepth: idepth, Line: line,
		})
	}

	kind := ""
	switch {
	case inSet(arRaw, meth):
		kind = "raw_sql"
	case inSet(arWrite, meth):
		kind = "write"
	case inSet(arTerminal, meth):
		kind = "terminal"
	case inSet(arRelation, meth):
		kind = "relation"
	}
	if kind != "" {
		model, chain := x.chainRoot(n)
		atxt := ""
		if hasNode(args) {
			atxt = textOf(src, args)
		}
		var strArg int32
		if hasNode(args) && namedChildCount(args) > 0 {
			k := kindID(namedChildAt(args, 0))
			if k == kindStr || k == kindHeredB {
				strArg = 1
			}
		}

		sanitized := int32(0)
		if strings.Contains(atxt, "sanitize_sql") || strings.Contains(atxt, "?") ||
			strings.IndexByte(atxt, ':') >= 0 && strings.IndexByte(atxt, ':') < 2 {
			sanitized = 1
		}
		x.pendAR = append(x.pendAR, wARQuery{
			Model: trunc(model, 80), API: trunc(meth, 40), BuildKind: kind,
			HasInterpolation: b2i(strings.Contains(atxt, "#{")),
			IsSanitized:      sanitized,
			FromParams:       b2i(strings.Contains(atxt, "params")),
			IsStringArg:      strArg,
			LoopDepth:        idepth, Chain: chain, Line: line,
		})
	}
	if idepth > 0 && inSet(enqueueAPIs, meth) {
		x.bump(cEnqueueInLoop)
	}
}

func (x *xctx) chainRoot(n tsNode) (string, int32) {
	cur := n
	chain := int32(0)
	for hasNode(cur) && chain < 12 {
		recv := childField(cur, fReceiver)
		if !hasNode(recv) {
			return "", chain
		}
		rt := kindID(recv)
		if rt == kindCall {
			cur = recv
			chain++
			continue
		}
		if rt == kindConst || rt == kindScopeRs || rt == kindIdent ||
			rt == kindInstanceVar || rt == kindSelf {
			return textOf(x.src, recv), chain
		}
		return "", chain
	}
	return "", chain
}

func hasChildKind(n tsNode, k uint16) bool {
	for i, m := 0, namedChildCount(n); i < m; i++ {
		if kindID(namedChildAt(n, i)) == k {
			return true
		}
	}
	return false
}

func inSingletonClass(n tsNode) bool {
	cur := parentNode(n)
	for hops := 0; hasNode(cur) && hops < 6; hops++ {
		switch kindID(cur) {
		case kindSingCls:
			return true
		case kindClass, kindModule, kindMethod:
			return false
		}
		cur = parentNode(cur)
	}
	return false
}

func (x *xctx) nodeName(n tsNode) string {
	if c := childField(n, fName); hasNode(c) {
		return cgStrip(textOf(x.src, c))
	}
	for i, m := 0, namedChildCount(n); i < m; i++ {
		c := namedChildAt(n, i)
		if identKind(kindID(c)) {
			return cgStrip(textOf(x.src, c))
		}
	}
	return ""
}

func (x *xctx) walkScope(root tsNode, fid int32, sc scope) {
	stack := x.scratch
	stack = stack[:0]
	stack = pushNamedChildren(stack, root, sc)
	x.scratch = stack[:0]
	for len(stack) > 0 {
		it := stack[len(stack)-1]
		stack = stack[:len(stack)-1]
		cur, s := it.n, it.sc
		k := kindID(cur)
		if k == kindMethod || k == kindSingl {
			sid := x.emitFunction(cur, s, "method")
			name := x.nodeName(cur)
			if name == "" {
				name = "?"
			}
			inner := scope{sid, s.qualPrefix + name + ".", s.typeName, s.typeID, s.depth + 1}
			body := childField(cur, fBody)
			if !hasNode(body) {
				body = cur
			}
			stack = pushNamedChildren(stack, body, inner)
			continue
		}
		if k == kindClass || k == kindModule {
			kindName := "class"
			if k == kindModule {
				kindName = "module"
			}
			sid := x.emitType(cur, s, kindName)
			name := x.nodeName(cur)
			if name == "" {
				name = "?"
			}
			inner := scope{sid, s.qualPrefix + name + ".", name, sid, s.depth + 1}
			body := childField(cur, fBody)
			if !hasNode(body) {
				body = cur
			}
			stack = pushNamedChildren(stack, body, inner)
			continue
		}
		stack = pushNamedChildren(stack, cur, s)
	}
	x.scratch = stack[:0]
}

func nNamed(n tsNode) int {
	if !hasNode(n) {
		return 0
	}
	return namedChildCount(n)
}

func (x *xctx) finish(n tsNode, name, kind, qual string, parentID int32,
	signature, visibility string) int32 {
	x.nextID++
	s := &x.st
	s.Id = x.nextID
	s.FileId = x.rec.ID
	s.ModuleId = x.rec.ModuleID
	s.ParentId = parentID
	s.Name = name
	s.QualName = trunc(qual, 400)
	s.Kind = kind
	s.LineStart = int32(startRow(n) + 1)
	s.LineEnd = int32(endRow(n) + 1)
	s.NLines = s.LineEnd - s.LineStart + 1
	s.ByteStart = int32(startByte(n))
	s.ByteEnd = int32(endByte(n))
	s.Signature = trunc(signature, 400)
	s.Visibility = visibility
	x.out.syms = append(x.out.syms, *s)
	return s.Id
}

func (x *xctx) emitFunction(n tsNode, sc scope, kind string) int32 {
	name := x.nodeName(n)
	if name == "" {
		name = "(anonymous)"
	}
	qual := sc.qualPrefix + name
	body := childField(n, fBody)
	if !hasNode(body) {
		body = n
	}
	x.resetStats()
	x.measure(body, false)
	st := &x.st
	st.NDistinctOperators, st.NDistinctOperands = x.nOp, x.nOpnd
	st.Sloc = x.slocOf(n)
	st.BodyBytes = int32(endByte(body) - startByte(body))
	st.IsGenerated = b2i(x.rec.IsGenerated != 0)
	x.countParams(n)
	vis := x.visibilityOf(n)
	x.functionFlags(n, sc, vis, name)
	doc := x.docLines(n)
	st.NDocLines = doc
	st.HasDoc = b2i(doc > 0)
	st.IsPublic = b2i(vis == "public")

	sid := x.finish(n, name, kind, qual, sc.symID, x.signatureOf(n), vis)
	x.emitParams(n, sid)
	for _, c := range x.calls {
		if c.dynamic || c.text == "" {
			continue
		}
		x.out.pend = append(x.out.pend, pendCall{sid, c.line, c.text, sc.typeName})
	}
	x.emitHazards(sid)
	x.emitInputSites(sid)
	x.emitLiterals(sid)
	for _, b := range x.pendBlk {
		x.out.blks = append(x.out.blks, wBlock{SymID: sid, FileID: x.rec.ID, Method: b.Method,
			Receiver: b.Receiver, Style: b.Style, IsIteration: b.IsIteration,
			Depth: b.Depth, NParams: b.NParams, BodySloc: b.BodySloc, Line: b.Line, NExits: b.NExits})
	}
	for _, m := range x.pendMeta {
		m.SymID = sid
		m.FileID = x.rec.ID
		x.out.msites = append(x.out.msites, m)
	}
	for _, a := range x.pendAR {
		a.SymID = sid
		a.FileID = x.rec.ID
		x.out.arqs = append(x.out.arqs, a)
	}
	x.pendBlk = x.pendBlk[:0]
	x.pendMeta = x.pendMeta[:0]
	x.pendAR = x.pendAR[:0]

	x.out.regNames = append(x.out.regNames, regName{name, sid, x.rec.ID, sc.typeName})
	x.out.regQuals = append(x.out.regQuals, regQual{qual, sid})
	x.out.regQuals = append(x.out.regQuals, regQual{x.rel + ":" + qual, sid})
	return sid
}

func (x *xctx) emitType(n tsNode, sc scope, kind string) int32 {
	name := x.nodeName(n)
	if name == "" {
		name = "(anonymous)"
	}
	qual := sc.qualPrefix + name

	body := childField(n, fBody)
	if !hasNode(body) {
		body = n
	}
	x.resetStats()
	x.measure(body, true)
	st := &x.st

	st.Cyclomatic, st.Cognitive, st.MaxNesting, st.MaxLoopDepth = 0, 0, 0, 0
	st.NDistinctOperators, st.NDistinctOperands = 0, 0
	st.Sloc = x.slocOf(n)
	st.IsGenerated = b2i(x.rec.IsGenerated != 0)

	short := name
	if i := strings.LastIndex(name, "::"); i >= 0 {
		short = name[i+2:]
	}
	sup := childField(n, fSuperclass)
	supTxt := ""
	if hasNode(sup) {
		supTxt = cgStrip(strings.TrimLeft(cgStrip(textOf(x.src, sup)), "< "))
	}
	head := x.headText(n, 2000)
	x.typeFlags(n, sc, name, short, head, supTxt)
	doc := x.docLines(n)
	st.NDocLines = doc
	st.HasDoc = b2i(doc > 0)
	st.IsPublic = 1

	cs := startByte(n)
	ce := endByte(n)
	limit := int(ce - cs)
	if i := indexBytes(x.src[cs:ce], "{"); i >= 0 && i < limit {
		limit = i
	}
	sig := trunc(cgStrip(string(x.src[cs:cs+uint(limit)])), 300)

	vis := x.visibilityOf(n)
	sid := x.finish(n, name, kind, qual, sc.symID, sig, vis)

	for _, c := range x.calls {
		if c.dynamic || c.text == "" {
			continue
		}
		x.out.pend = append(x.out.pend, pendCall{sid, c.line, c.text, sc.typeName})
	}
	x.emitHazards(sid)
	x.typeExtra(n, sid, name, short, supTxt, sc)
	x.out.regNames = append(x.out.regNames, regName{name, sid, x.rec.ID, sc.typeName})
	x.out.regQuals = append(x.out.regQuals, regQual{qual, sid})
	return sid
}

func (x *xctx) headText(n tsNode, limit int) string {
	s, e := startByte(n), endByte(n)
	if uint(limit) < e-s {
		e = s + uint(limit)
	}
	return string(x.src[s:e])
}

func (x *xctx) emitModuleScope(root tsNode) {
	x.resetStats()
	x.measure(root, true)
	if len(x.calls) == 0 && x.st.NTokens < 8 {
		return
	}
	st := &x.st
	st.NDistinctOperators, st.NDistinctOperands = x.nOp, x.nOpnd
	st.IsGenerated = b2i(x.rec.IsGenerated != 0)
	st.IsTest = b2i(x.rec.IsTest != 0)
	sid := x.finish(root, "<module>", "module", x.rel, 0,
		"top-level statements of "+x.rec.Path(), "")

	for _, c := range x.calls {
		if c.dynamic || c.text == "" {
			continue
		}
		x.out.pend = append(x.out.pend, pendCall{sid, c.line, c.text, ""})
	}
	x.emitHazards(sid)
	x.emitInputSites(sid)
	x.emitLiterals(sid)
}

func (x *xctx) countParams(n tsNode) {
	params := childField(n, fParams)
	if !hasNode(params) {
		return
	}
	kids := namedChildCount(params)
	var opt int32
	for i, m := 0, namedChildCount(params); i < m; i++ {
		c := namedChildAt(params, i)
		if kindID(c) == kindComment {
			kids--
			continue
		}
		if strings.HasPrefix(kindName(kindID(c)), "optional") ||
			hasNode(childField(c, fValue)) {
			opt++
		}
	}
	x.st.NParams = int32(kids)
	x.st.NOptionalParams = opt
}

func (x *xctx) emitParams(n tsNode, sid int32) {
	params := childField(n, fParams)
	if !hasNode(params) {
		return
	}
	src := x.src
	for pos, i := int32(0), 0; i < namedChildCount(params); i++ {
		p := namedChildAt(params, i)
		k := kindID(p)
		nm := childField(p, fName)
		name := ""
		if hasNode(nm) {
			name = cgStrip(textOf(src, nm))
		} else {
			name = cgStrip(textOf(src, p))
		}
		dv := childField(p, fValue)
		var def string
		hasDef := false
		if hasNode(dv) {
			def = trunc(textOf(src, dv), 120)
			hasDef = true
		}
		opt := int32(0)
		if (k == kindOptParam || k == kindKwParam) && hasNode(dv) {
			opt = 1
		}
		var variadic int32
		if k == kindSplatP || k == kindHSplatP || k == kindFwdParam {
			variadic = 1
		}
		nm2 := trunc(name, 120)
		if nm2 == "" {
			nm2 = "(anonymous)"
		}
		x.out.params = append(x.out.params, wParam{
			SymID: sid, Pos: pos, Name: nm2, HasName: hasNode(nm),
			Type: kindName(k), Default: def, HasDefault: hasDef,
			Optional: opt, Variadic: variadic, Untyped: 1,
		})
		pos++
	}
}

func (x *xctx) emitHazards(sid int32) {

	var order []string
	counts := map[string]int32{}
	cats := map[string]string{}
	lines := map[string]int32{}
	for _, c := range x.calls {
		if c.text == "" {
			continue
		}
		pat, cat, ok := hazardOf(c.text)
		if !ok {
			continue
		}
		pat = trunc(pat, 120)
		if _, seen := counts[pat]; !seen {
			order = append(order, pat)
			cats[pat] = cat
			lines[pat] = c.line
		}
		counts[pat]++
	}
	for _, p := range order {
		x.out.hazs = append(x.out.hazs, wHazard{
			SymID: sid, Pattern: p, Category: cats[p],
			N: counts[p], FirstLine: lines[p]})
	}
}

func hazardOf(callee string) (pattern, category string, ok bool) {
	if c, found := hazardCalls[callee]; found {
		return callee, c, true
	}
	base := callee
	if i := strings.LastIndex(callee, "."); i >= 0 {
		base = callee[i+1:]
	}
	if c, found := hazardCalls[base]; found {
		return "*." + base, c, true
	}
	head := callee
	if before, _, ok := strings.Cut(callee, "."); ok {
		head = before
	}
	if head == "Digest" || head == "OpenSSL" || strings.HasPrefix(callee, "Digest::") {
		base2 := callee
		if i := strings.LastIndex(callee, "."); i >= 0 {
			base2 = callee[:i]
		}
		return base2, "crypto", true
	}
	return "", "", false
}

func (x *xctx) emitInputSites(sid int32) {
	for _, in := range x.inputs {
		x.out.uis = append(x.out.uis, wInputSite{
			SymID: sid, FileID: x.rec.ID, Var: in.text, Kind: in.kind,
			Line: in.line, InLoop: b2i(in.inLoop)})
	}
	for _, s := range x.secrets {
		x.out.secs = append(x.out.secs, wSecret{
			SymID: sid, FileID: x.rec.ID, Value: s.value, Line: s.line})
	}
}

func (x *xctx) emitLiterals(sid int32) {
	for _, l := range x.lits {
		x.out.lits = append(x.out.lits, wLiteral{
			SymID: sid, FileID: x.rec.ID, Kind: l.kind,
			Value: trunc(l.value, 200), Line: l.line, Magic: b2i(l.magic)})
	}
}

var commentPrefixes = []string{
	"//", "#", "/*", "*", "*/",
	"\"\"\"",
	"'''",
	"--", ";;", "%",
}

func (x *xctx) slocOf(n tsNode) int32 {
	var c int32
	forEachLine(x.src[startByte(n):endByte(n)], func(line []byte) {
		t := trimLeftBytes(line)
		if !isBlank(t) && !commentPrefixBytes(t) {
			c++
		}
	})
	return c
}

func (x *xctx) signatureOf(n tsNode) string {
	end := endByte(n)
	if p := childField(n, fParams); hasNode(p) {
		end = endByte(p)
	} else if b := childField(n, fBody); hasNode(b) {
		end = startByte(b)
	}
	s := startByte(n)
	if end < s {
		end = s
	}
	return cgStrip(string(x.src[s:end]))
}

var docPrefixes = []string{"///", "/**", "##", `"""`, "'''", "#'", "--|"}

func (x *xctx) docLines(n tsNode) int32 {
	prev := prevSibling(n)
	var total int32
	for hasNode(prev) && kindID(prev) == kindComment {
		txt := cgStripLeft(textOf(x.src, prev))
		span := int32(endRow(prev) - startRow(prev) + 1)
		switch {
		case hasPrefixAny(txt, docPrefixes...):
			total += span
		case total == 0 && int32(endRow(prev))+1 >= int32(startRow(n)):
			total += span
		default:
			return total
		}
		prev = prevSibling(prev)
	}
	return total
}

func raisesNotImplemented(n tsNode, src []byte) bool {
	b := childField(n, fBody)
	if !hasNode(b) {
		return false
	}
	return indexBytes(src[startByte(b):endByte(b)], "NotImplementedError") >= 0
}

func (x *xctx) visibilityOf(n tsNode) string {
	if kindID(n) == kindSingl {
		return "public"
	}

	if par := parentNode(n); hasNode(par) && kindID(par) == kindArgList {
		if gp := parentNode(par); hasNode(gp) && kindID(gp) == kindCall {
			if m := childField(gp, fMethod); hasNode(m) {
				txt := textOf(x.src, m)
				if txt == "private" || txt == "protected" || txt == "private_class_method" {
					if txt == "protected" {
						return "protected"
					}
					return "private"
				}
			}
		}
	}
	line := int32(startRow(n) + 1)
	vis := "public"
	for _, v := range x.vis {
		if v.lo <= line && line <= v.hi {
			vis = v.vis
		}
	}
	return vis
}

func writeJSON(w io.Writer, res *result) {
	b := bufio.NewWriterSize(w, 1<<16)
	defer b.Flush()
	if len(res.rows) == 0 {
		b.WriteString("[]\n")
		return
	}
	b.WriteString("[\n")
	for ri, r := range res.rows {
		b.WriteString("  {\n")
		for i, name := range res.cols {
			b.WriteString("    ")
			jsonString(b, name)
			b.WriteString(": ")
			if i < len(r) {
				jsonCell(b, r[i])
			} else {
				b.WriteString("null")
			}
			if i+1 < len(res.cols) {
				b.WriteByte(',')
			}
			b.WriteByte('\n')
		}
		b.WriteString("  }")
		if ri+1 < len(res.rows) {
			b.WriteByte(',')
		}
		b.WriteByte('\n')
	}
	b.WriteString("]\n")
}

func jsonCell(b *bufio.Writer, c cell) {
	switch c.kind {
	case 'i':
		b.WriteString(strconv.FormatInt(c.i, 10))
	case 'n':
		b.WriteString("null")
	case 'f':
		b.WriteString(cgFloatRepr(c.f))
	default:
		jsonString(b, c.s)
	}
}

func jsonString(b *bufio.Writer, s string) {
	b.WriteByte('"')
	for i := 0; i < len(s); {
		c := s[i]
		if c < utf8.RuneSelf {
			switch c {
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
				if c < 0x20 {
					const hex = "0123456789abcdef"
					b.WriteString(`\u00`)
					b.WriteByte(hex[c>>4])
					b.WriteByte(hex[c&0xF])
				} else {
					b.WriteByte(c)
				}
			}
			i++
			continue
		}
		r, sz := utf8.DecodeRuneInString(s[i:])
		if r == utf8.RuneError && sz == 1 {

			b.WriteString(`�`)
			i++
			continue
		}
		if r > 0xFFFF {
			hi, lo := utf16.EncodeRune(r)
			writeU(b, hi)
			writeU(b, lo)
		} else {
			writeU(b, r)
		}
		i += sz
	}
	b.WriteByte('"')
}

func writeU(b *bufio.Writer, r rune) {
	const hex = "0123456789abcdef"
	b.WriteString(`\u`)
	b.WriteByte(hex[(r>>12)&0xF])
	b.WriteByte(hex[(r>>8)&0xF])
	b.WriteByte(hex[(r>>4)&0xF])
	b.WriteByte(hex[r&0xF])
}

func cgFloatRepr(f float64) string {
	switch {
	case math.IsNaN(f):
		return "NaN"
	case math.IsInf(f, 1):
		return "Infinity"
	case math.IsInf(f, -1):
		return "-Infinity"
	}

	abs := math.Abs(f)
	if abs != 0 && (abs < 1e-4 || abs >= 1e16) {
		s := strconv.FormatFloat(f, 'e', -1, 64)

		i := len(s) - 1
		for i > 0 && s[i] != 'e' {
			i--
		}
		if i > 0 && i+3 < len(s) && s[i+2] == '+' && len(s)-i-3 < 2 {
			s = s[:i+3] + "0" + s[i+3:]
		}
		return s
	}
	s := strconv.FormatFloat(f, 'f', -1, 64)
	if !strings.ContainsAny(s, ".eE") {
		s += ".0"
	}
	return s
}

func appendIntCell(dst []byte, v int32) []byte {
	dst = append(dst, 'i', ':')
	return strconv.AppendInt(dst, int64(v), 10)
}

func appendInt64Cell(dst []byte, v int64) []byte {
	dst = append(dst, 'i', ':')
	return strconv.AppendInt(dst, v, 10)
}

func appendFloatCell(dst []byte, v float64) []byte {
	dst = append(dst, 'f', ':')
	if math.IsInf(v, 1) {
		return append(dst, "inf"...)
	}
	if math.IsInf(v, -1) {
		return append(dst, "-inf"...)
	}
	if math.IsNaN(v) {
		return append(dst, "nan"...)
	}
	a := math.Abs(v)
	form := byte('f')
	if a != 0 && (a < 1e-4 || a >= 1e16) {
		form = 'e'
	}
	b := strconv.AppendFloat(nil, v, form, -1, 64)
	if form == 'e' {

		if i := bytesIndexByte(b, 'e'); i >= 0 && bytesIndexByte(b[:i], '.') < 0 {
			nb := make([]byte, 0, len(b)+1)
			nb = append(nb, b[:i]...)
			nb = append(nb, '.', '0')
			nb = append(nb, b[i:]...)
			b = nb
		}
	} else if bytesIndexByte(b, '.') < 0 {
		b = append(b, '.', '0')
	}
	return append(dst, b...)
}

func bytesIndexByte(b []byte, c byte) int {
	for i := range b {
		if b[i] == c {
			return i
		}
	}
	return -1
}

func appendStrCell(dst []byte, s string) []byte {
	dst = append(dst, 's', ':')
	for i := 0; i < len(s); i++ {
		c := s[i]
		switch c {
		case '\\':
			dst = append(dst, '\\', '\\')
		case '\n':
			dst = append(dst, '\\', 'n')
		case '\t':
			dst = append(dst, '\\', 't')
		case '\r':
			dst = append(dst, '\\', 'r')
		default:
			if c < 0x20 || c == 0x7F {
				const hex = "0123456789ABCDEF"
				dst = append(dst, '\\', 'x', hex[c>>4], hex[c&0xF])
			} else {
				dst = append(dst, c)
			}
		}
	}
	return dst
}

func appendNullCell(dst []byte) []byte { return append(dst, '\\', 'N') }

type tableWriter struct {
	w   *bufio.Writer
	buf []byte
}

func (g *Graph) dumpTo(path string) error {
	f, err := os.Create(path)
	if err != nil {
		return err
	}
	defer f.Close()
	w := bufio.NewWriterSize(f, 1<<20)
	defer w.Flush()

	t := &tableWriter{w: w}
	t.table("ar_callbacks", 12, func() [][]byte {
		rows := make([][]byte, len(g.ARCBs))
		for i := range g.ARCBs {
			c := &g.ARCBs[i]
			b := []byte("R ")
			b = appendIntCell(b, int32(i+1))
			b = append(b, ' ')
			b = appendIntCell(b, c.SymID)
			b = append(b, ' ')
			b = appendIntCell(b, c.FileID)
			b = append(b, ' ')
			b = appendStrCell(b, c.Host())
			b = append(b, ' ')
			b = appendStrCell(b, c.Hook())
			b = append(b, ' ')
			b = appendStrCell(b, c.Method())
			b = append(b, ' ')
			b = appendIntCell(b, c.Conditional)
			b = append(b, ' ')
			b = appendIntCell(b, c.Block)
			b = append(b, ' ')
			b = appendIntCell(b, c.Association)
			b = append(b, ' ')
			b = appendIntCell(b, c.IssuesQuery)
			b = append(b, ' ')
			b = appendSymOrNull(b, c.HasTargetID, c.TargetID)
			b = append(b, ' ')
			b = appendIntCell(b, c.Line)
			rows[i] = b
		}
		return rows
	})

	t.table("ar_queries", 13, func() [][]byte {
		rows := make([][]byte, len(g.ARQs))
		for i := range g.ARQs {
			a := &g.ARQs[i]
			b := []byte("R ")
			b = appendIntCell(b, int32(i+1))
			b = append(b, ' ')
			b = appendIntCell(b, a.SymID)
			b = append(b, ' ')
			b = appendIntCell(b, a.FileID)
			b = append(b, ' ')
			b = appendStrCell(b, a.Model())
			b = append(b, ' ')
			b = appendStrCell(b, a.API())
			b = append(b, ' ')
			b = appendStrCell(b, a.BuildKind())
			b = append(b, ' ')
			b = appendIntCell(b, a.HasInterpolation)
			b = append(b, ' ')
			b = appendIntCell(b, a.IsSanitized)
			b = append(b, ' ')
			b = appendIntCell(b, a.FromParams)
			b = append(b, ' ')
			b = appendIntCell(b, a.IsStringArg)
			b = append(b, ' ')
			b = appendIntCell(b, a.LoopDepth)
			b = append(b, ' ')
			b = appendIntCell(b, a.Chain)
			b = append(b, ' ')
			b = appendIntCell(b, a.Line)
			rows[i] = b
		}
		return rows
	})

	t.table("attributes", 6, func() [][]byte { return nil })

	t.table("blocks", 15, func() [][]byte {
		rows := make([][]byte, len(g.Blks))
		for i := range g.Blks {
			b := &g.Blks[i]
			c := []byte("R ")
			c = appendIntCell(c, int32(i+1))
			for _, v := range []int32{b.SymID, b.FileID} {
				c = append(c, ' ')
				c = appendIntCell(c, v)
			}
			for _, s := range []string{b.Method(), b.Receiver(), b.Style()} {
				c = append(c, ' ')
				c = appendStrCell(c, s)
			}
			for _, v := range []int32{b.IsIteration, b.Depth, b.NParams, b.BodySloc,
				b.NQueries, b.NAllocs, b.CapturesOuter, b.Line, b.NExits} {
				c = append(c, ' ')
				c = appendIntCell(c, v)
			}
			rows[i] = c
		}
		return rows
	})

	t.table("callsites", 3, func() [][]byte {
		rows := make([][]byte, len(g.Sites))
		for i := range g.Sites {
			s := &g.Sites[i]
			c := []byte("R ")
			c = appendIntCell(c, s.Caller)
			c = append(c, ' ')
			c = appendIntCell(c, s.Callee)
			c = append(c, ' ')
			c = appendIntCell(c, s.Line)
			rows[i] = c
		}
		return rows
	})

	t.table("edges", 6, func() [][]byte {
		rows := make([][]byte, len(g.Edges))
		for i := range g.Edges {
			e := &g.Edges[i]
			c := []byte("R ")
			c = appendIntCell(c, e.Caller)
			c = append(c, ' ')
			c = appendIntCell(c, e.Callee)
			c = append(c, ' ')
			c = appendIntCell(c, e.NCalls)
			c = append(c, ' ')
			c = appendIntCell(c, e.SameFile)
			c = append(c, ' ')
			c = appendIntCell(c, e.SameModule)
			c = append(c, ' ')
			c = appendIntCell(c, e.Self)
			rows[i] = c
		}
		return rows
	})

	t.table("enum_members", 5, func() [][]byte {
		rows := make([][]byte, len(g.Enums))
		for i := range g.Enums {
			e := &g.Enums[i]
			c := []byte("R ")
			c = appendIntCell(c, e.SymID)
			c = append(c, ' ')
			c = appendIntCell(c, e.Ord)
			c = append(c, ' ')
			c = appendStrCell(c, e.Name())
			c = append(c, ' ')
			if e.HasValue {
				c = appendStrCell(c, e.Value())
			} else {
				c = appendNullCell(c)
			}
			c = append(c, ' ')
			c = appendIntCell(c, e.NFields)
			rows[i] = c
		}
		return rows
	})

	t.table("fields", 14, func() [][]byte {
		rows := make([][]byte, len(g.Fields))
		for i := range g.Fields {
			f := &g.Fields[i]
			c := []byte("R ")
			c = appendIntCell(c, f.SymID)
			c = append(c, ' ')
			c = appendIntCell(c, f.Ord)
			c = append(c, ' ')
			c = appendStrCell(c, f.Name())
			c = append(c, ' ')
			c = appendStrCell(c, f.Type())
			c = append(c, ' ')
			c = appendStrCell(c, f.Vis())
			c = append(c, ' ')
			c = appendIntCell(c, f.Line)
			for _, v := range []int32{f.Static, f.Const_, f.Mutable, f.Nullable,
				f.Collection, f.Untyped, f.HasDefault, f.TypeDepth} {
				c = append(c, ' ')
				c = appendIntCell(c, v)
			}
			rows[i] = c
		}
		return rows
	})

	t.table("files", 29, func() [][]byte {
		rows := make([][]byte, len(g.Files))
		for i := range g.Files {
			f := g.Files[i]
			c := []byte("R ")
			c = appendIntCell(c, f.ID)
			for _, s := range []string{f.Path(), f.Dir(), f.Base(), f.Ext(), f.Lang()} {
				c = append(c, ' ')
				c = appendStrCell(c, s)
			}
			c = append(c, ' ')
			if f.ModuleID != 0 {
				c = appendIntCell(c, f.ModuleID)
			} else {
				c = appendNullCell(c)
			}
			for _, v := range []int32{f.Bytes, f.Lines, f.Sloc, f.Blank, f.Comment,
				0, f.MaxLine} {
				c = append(c, ' ')
				c = appendIntCell(c, v)
			}
			c = append(c, ' ')
			c = appendStrCell(c, f.Sha1())
			for _, v := range []int32{f.Parsed, f.IsTest, f.IsGenerated, f.IsVendored,
				f.ParseErrors, f.Missing} {
				c = append(c, ' ')
				c = appendIntCell(c, v)
			}
			c = append(c, ' ')
			c = appendFloatCell(c, f.ParseMs)
			for _, v := range []int32{f.NSymbols, f.NFunctions, f.NTypes, f.NImports,
				f.TotalCyclo, f.MaxCyclo, f.TotalRisk} {
				c = append(c, ' ')
				c = appendIntCell(c, v)
			}
			rows[i] = c
		}
		return rows
	})

	t.table("hazards", 5, func() [][]byte {
		rows := make([][]byte, len(g.Haz))
		for i := range g.Haz {
			h := &g.Haz[i]
			c := []byte("R ")
			c = appendIntCell(c, h.SymID)
			c = append(c, ' ')
			c = appendStrCell(c, h.Pattern())
			c = append(c, ' ')
			c = appendStrCell(c, h.Category())
			c = append(c, ' ')
			c = appendIntCell(c, h.N)
			c = append(c, ' ')
			c = appendIntCell(c, h.FirstLine)
			rows[i] = c
		}
		return rows
	})

	t.table("imports", 13, func() [][]byte {
		rows := make([][]byte, len(g.Imps))
		for i := range g.Imps {
			m := &g.Imps[i]
			c := []byte("R ")
			c = appendIntCell(c, int32(i+1))
			c = append(c, ' ')
			c = appendIntCell(c, m.FileID)
			c = append(c, ' ')
			c = appendStrCell(c, m.Target())
			c = append(c, ' ')
			c = appendSymOrNull(c, m.HasTargetID, m.TargetID)
			c = append(c, ' ')
			if m.HasAlias {
				c = appendStrCell(c, m.Alias())
			} else {
				c = appendNullCell(c)
			}
			c = append(c, ' ')
			c = appendStrCell(c, m.Kind())
			for _, v := range []int32{m.Line, m.External, m.Relative, m.Wildcard,
				m.TypeOnly, m.Dynamic, m.NNames} {
				c = append(c, ' ')
				c = appendIntCell(c, v)
			}
			rows[i] = c
		}
		return rows
	})

	t.table("literals", 7, func() [][]byte {
		rows := make([][]byte, len(g.Lits))
		for i := range g.Lits {
			l := &g.Lits[i]
			c := []byte("R ")
			c = appendIntCell(c, int32(i+1))
			c = append(c, ' ')
			c = appendIntCell(c, l.SymID)
			c = append(c, ' ')
			c = appendIntCell(c, l.FileID)
			c = append(c, ' ')
			c = appendStrCell(c, l.Kind())
			c = append(c, ' ')
			c = appendStrCell(c, l.Value())
			c = append(c, ' ')
			c = appendIntCell(c, l.Line)
			c = append(c, ' ')
			c = appendIntCell(c, l.Magic)
			rows[i] = c
		}
		return rows
	})

	t.table("locals", 11, func() [][]byte { return nil })

	t.table("markers", 6, func() [][]byte {
		rows := make([][]byte, len(g.Mark))
		for i := range g.Mark {
			m := &g.Mark[i]
			c := []byte("R ")
			c = appendIntCell(c, int32(i+1))
			c = append(c, ' ')
			c = appendIntCell(c, m.FileID)
			c = append(c, ' ')
			c = appendSymOrNull(c, m.HasSym, m.SymID)
			c = append(c, ' ')
			c = appendStrCell(c, m.Kind())
			c = append(c, ' ')
			c = appendIntCell(c, m.Line)
			c = append(c, ' ')
			if m.Text() == "" {
				c = appendNullCell(c)
			} else {
				c = appendStrCell(c, m.Text())
			}
			rows[i] = c
		}
		return rows
	})

	t.table("meta", 2, func() [][]byte {
		rows := make([][]byte, 0, len(g.Meta))
		for _, m := range g.Meta {
			c := []byte("R ")
			c = appendStrCell(c, m.K.Str())
			c = append(c, ' ')
			c = appendStrCell(c, m.V.Str())
			rows = append(rows, c)
		}
		return rows
	})

	t.table("metaprogram_sites", 12, func() [][]byte {
		rows := make([][]byte, len(g.MSites))
		for i := range g.MSites {
			m := &g.MSites[i]
			c := []byte("R ")
			c = appendIntCell(c, int32(i+1))
			c = append(c, ' ')
			c = appendIntCell(c, m.SymID)
			c = append(c, ' ')
			c = appendIntCell(c, m.FileID)
			c = append(c, ' ')
			c = appendStrCell(c, m.API())
			c = append(c, ' ')
			c = appendStrCell(c, m.Arg())
			for _, v := range []int32{m.Literal, m.FromParams, m.FromVar, m.OnHeredoc,
				m.InClassBody, m.LoopDepth, m.Line} {
				c = append(c, ' ')
				c = appendIntCell(c, v)
			}
			rows[i] = c
		}
		return rows
	})

	t.table("mixins", 9, func() [][]byte {
		rows := make([][]byte, len(g.Mixins))
		for i := range g.Mixins {
			m := &g.Mixins[i]
			c := []byte("R ")
			c = appendIntCell(c, int32(i+1))
			c = append(c, ' ')
			c = appendSymOrNull(c, m.HostID != 0, m.HostID)
			c = append(c, ' ')
			c = appendIntCell(c, m.FileID)
			c = append(c, ' ')
			c = appendStrCell(c, m.Host())
			c = append(c, ' ')
			c = appendStrCell(c, m.Mixin())
			c = append(c, ' ')
			c = appendStrCell(c, m.MixinShort())
			c = append(c, ' ')
			c = appendStrCell(c, m.Kind())
			c = append(c, ' ')
			c = appendIntCell(c, m.InSingleton)
			c = append(c, ' ')
			c = appendIntCell(c, m.Line)
			rows[i] = c
		}
		return rows
	})

	t.table("modules", 10, func() [][]byte {
		rows := make([][]byte, len(g.Mods))
		for i := range g.Mods {
			m := *g.Mods[i]
			c := []byte("R ")
			c = appendIntCell(c, m.ID)
			c = append(c, ' ')
			c = appendStrCell(c, m.Name())
			c = append(c, ' ')
			c = appendStrCell(c, m.Kind())
			for _, v := range []int32{m.NFiles, m.NSymbols, m.NPublic, m.Sloc,
				m.FanIn, m.FanOut} {
				c = append(c, ' ')
				c = appendIntCell(c, v)
			}
			c = append(c, ' ')
			c = appendFloatCell(c, m.Instability)
			rows[i] = c
		}
		return rows
	})

	t.table("monkey_patches", 9, func() [][]byte {
		rows := make([][]byte, len(g.MPs))
		for i := range g.MPs {
			m := &g.MPs[i]
			c := []byte("R ")
			c = appendIntCell(c, int32(i+1))
			c = append(c, ' ')
			c = appendIntCell(c, m.SymID)
			c = append(c, ' ')
			c = appendSymOrNull(c, m.HasMethodID, m.MethodID)
			c = append(c, ' ')
			c = appendIntCell(c, m.FileID)
			c = append(c, ' ')
			c = appendStrCell(c, m.CoreClass())
			c = append(c, ' ')
			c = appendStrCell(c, m.Method())
			c = append(c, ' ')
			c = appendIntCell(c, m.Operator)
			c = append(c, ' ')
			c = appendIntCell(c, m.Singleton)
			c = append(c, ' ')
			c = appendIntCell(c, m.Line)
			rows[i] = c
		}
		return rows
	})

	t.table("params", 13, func() [][]byte {
		rows := make([][]byte, len(g.Params))
		for i := range g.Params {
			p := &g.Params[i]
			c := []byte("R ")
			c = appendIntCell(c, p.SymID)
			c = append(c, ' ')
			c = appendIntCell(c, p.Pos)
			c = append(c, ' ')
			if p.HasName || p.Name() != "" {
				c = appendStrCell(c, p.Name())
			} else {
				c = appendNullCell(c)
			}
			c = append(c, ' ')
			c = appendStrCell(c, p.Type())
			c = append(c, ' ')
			if p.HasDefault {
				c = appendStrCell(c, p.Default())
			} else {
				c = appendNullCell(c)
			}
			for _, v := range []int32{p.Optional, p.Variadic, p.Ref, p.Mutable,
				p.Nullable, p.Generic, p.Untyped, p.TypeDepth} {
				c = append(c, ' ')
				c = appendIntCell(c, v)
			}
			rows[i] = c
		}
		return rows
	})

	t.table("ruby_modules", 17, func() [][]byte {
		rows := make([][]byte, len(g.RMods))
		for i := range g.RMods {
			r := &g.RMods[i]
			c := []byte("R ")
			c = appendIntCell(c, r.SymID)
			c = append(c, ' ')
			c = appendIntCell(c, r.FileID)
			c = append(c, ' ')
			c = appendStrCell(c, r.Name())
			for _, v := range []int32{r.IsModule, r.IsConcern, r.HasIncludedBlock,
				r.HasClassMethodsBlock} {
				c = append(c, ' ')
				c = appendIntCell(c, v)
			}
			c = append(c, ' ')
			c = appendStrCell(c, r.Superclass())
			for _, v := range []int32{r.NMixins, r.NDefs, r.NClassDefs, r.NClassIvars,
				r.NClassVars, r.NGlobals, r.NDelegates, r.ReopensCore, r.Line} {
				c = append(c, ' ')
				c = appendIntCell(c, v)
			}
			rows[i] = c
		}
		return rows
	})

	t.table("secret_candidates", 5, func() [][]byte {
		rows := make([][]byte, len(g.Secs))
		for i := range g.Secs {
			s := &g.Secs[i]
			c := []byte("R ")
			c = appendIntCell(c, int32(i+1))
			c = append(c, ' ')
			c = appendIntCell(c, s.SymID)
			c = append(c, ' ')
			c = appendIntCell(c, s.FileID)
			c = append(c, ' ')
			c = appendStrCell(c, s.Value())
			c = append(c, ' ')
			c = appendIntCell(c, s.Line)
			rows[i] = c
		}
		return rows
	})

	t.table("sym_fts", 3, func() [][]byte {
		rows := make([][]byte, len(g.Syms))
		row := []byte("R \\N \\N \\N")
		for i := range rows {
			rows[i] = row
		}
		return rows
	})

	t.table("symbols", 223, func() [][]byte {
		rows := make([][]byte, len(g.Syms))
		// Build each 223-cell row in one reused buffer, then copy it to an
		// exact-size slice: appending from nil re-grows the row ~10 times, and
		// a fixed 4 KB capacity over-allocates every short row.
		var scratch []byte
		for i := range g.Syms {
			scratch = scratch[:0]
			scratch = append(scratch, "R "...)
			scratch = g.appendSymCells(scratch, i)
			rows[i] = append([]byte(nil), scratch...)
		}
		return rows
	})

	t.table("unresolved_calls", 4, func() [][]byte {
		rows := make([][]byte, len(g.Unres))
		for i := range g.Unres {
			u := &g.Unres[i]
			c := []byte("R ")
			c = appendIntCell(c, u.Caller)
			c = append(c, ' ')
			c = appendStrCell(c, u.Name())
			c = append(c, ' ')
			c = appendIntCell(c, u.N)
			c = append(c, ' ')
			c = appendIntCell(c, u.FirstLine)
			rows[i] = c
		}
		return rows
	})

	t.table("user_input_sites", 7, func() [][]byte {
		rows := make([][]byte, len(g.UIs))
		for i := range g.UIs {
			u := &g.UIs[i]
			c := []byte("R ")
			c = appendIntCell(c, int32(i+1))
			c = append(c, ' ')
			c = appendIntCell(c, u.SymID)
			c = append(c, ' ')
			c = appendIntCell(c, u.FileID)
			c = append(c, ' ')
			c = appendStrCell(c, u.Var())
			c = append(c, ' ')
			c = appendStrCell(c, u.Kind())
			c = append(c, ' ')
			c = appendIntCell(c, u.Line)
			c = append(c, ' ')
			c = appendIntCell(c, u.InLoop)
			rows[i] = c
		}
		return rows
	})
	return nil
}

func appendSymOrNull(dst []byte, present bool, v int32) []byte {
	if !present {
		return appendNullCell(dst)
	}
	return appendIntCell(dst, v)
}

func (t *tableWriter) table(name string, ncols int, fill func() [][]byte) {
	rows := fill()
	// Byte order is string order; this is the same ordering the previous
	// string(rows[i]) < string(rows[j]) comparator produced, without the
	// reflect.Swapper that sort.Slice uses on a [][]byte.
	slices.SortFunc(rows, bytes.Compare)
	t.buf = t.buf[:0]
	t.buf = append(t.buf, 'T', ' ')
	t.buf = append(t.buf, name...)
	t.buf = append(t.buf, ' ')
	t.buf = strconv.AppendInt(t.buf, int64(ncols), 10)
	t.buf = append(t.buf, ' ')
	t.buf = strconv.AppendInt(t.buf, int64(len(rows)), 10)
	t.buf = append(t.buf, '\n')
	t.w.Write(t.buf)
	for _, r := range rows {
		t.w.Write(r)
		t.w.WriteByte('\n')
	}
	t.w.WriteString("E " + name + "\n")
}

var _ = fmt.Sprint
var _ = strings.TrimSpace

func (g *Graph) report() {
	out := bufio.NewWriter(os.Stdout)
	defer out.Flush()
	bar := strings.Repeat("=", 78)
	dash := strings.Repeat("-", 78)

	fmt.Fprintf(out, "\n%s\nOVERVIEW\n%s\n", bar, dash)
	meta := map[string]string{}
	for i := range g.Meta {
		meta[g.Meta[i].K.Str()] = g.Meta[i].V.Str()
	}
	for _, k := range []string{"lang", "target", "parser", "root", "built_at"} {
		if v, ok := meta[k]; ok && v != "" {
			fmt.Fprintf(out, " %-14s %s\n", k, v)
		}
	}
	parsed, sloc := 0, int64(0)
	for _, f := range g.Files {
		if f.Parsed != 0 {
			parsed++
			sloc += int64(f.Sloc)
		}
	}
	fmt.Fprintf(out, " %-14s %d catalogued, %d parsed, %d sloc\n",
		"files", len(g.Files), parsed, sloc)

	kinds := map[string]int{}
	for _, s := range g.Syms {
		kinds[s.Kind()]++
	}
	type kv struct {
		k string
		v int
	}
	ks := make([]kv, 0, len(kinds))
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
	parts := make([]string, len(ks))
	for i, e := range ks {
		parts[i] = fmt.Sprintf("%s=%d", e.k, e.v)
	}
	fmt.Fprintf(out, " %-14s %s\n", "symbols", strings.Join(parts, ", "))

	var unresN int64
	for _, u := range g.Unres {
		unresN += int64(u.N)
	}
	fmt.Fprintf(out, " %-14s %d edges, %d call sites, %d unresolved\n",
		"call graph", len(g.Edges), len(g.Sites), unresN)

	fmt.Fprintf(out, "\n%s\nHOW MUCH OF THIS TO TRUST\n%s\n", bar, dash)
	errFiles := 0
	for _, f := range g.Files {
		if f.ParseErrors > 0 {
			errFiles++
		}
	}
	var totCalls, unres int64
	for _, s := range g.Syms {
		totCalls += int64(s.NCalls)
	}
	unres = unresN
	if parsed == 0 {
		fmt.Fprintln(out, " NOTHING WAS PARSED. Every number below is zero because no file")
		fmt.Fprintln(out, " was read, not because this repository is empty or clean.")
	}
	fmt.Fprintf(out, " %-30s %d file(s)\n", "files with parse errors", errFiles)
	if totCalls > 0 {
		fmt.Fprintf(out, " %-30s %d of %d call sites (%d%%)\n",
			"calls we could NOT resolve", unres, totCalls, 100*unres/totCalls)
	} else {
		fmt.Fprintf(out, " %-30s no calls were recorded at all -- this is the absence of\n", "")
		fmt.Fprintf(out, " %-30s call resolution data, not a clean result\n", "")
	}
	fmt.Fprintln(out, " A high unresolved share means the call-graph queries below see less")
	fmt.Fprintln(out, " than they imply. `v_blindspot` lists exactly where.")

	section := func(label string, cols []string, rows []row) {
		fmt.Fprintf(out, "\n%s\n%s\n%s\n", bar, label, dash)
		render(out, &result{cols: cols, rows: rows})
	}

	mods := append([]*Module(nil), g.Mods...)
	sort.Slice(mods, func(i, j int) bool {
		if mods[i].Sloc != mods[j].Sloc {
			return mods[i].Sloc > mods[j].Sloc
		}
		return mods[i].ID < mods[j].ID
	})
	var mr []row
	for _, m := range mods {
		if m.NFiles == 0 {
			continue
		}
		if len(mr) >= 12 {
			break
		}
		mr = append(mr, row{cs(m.Name()), ci32(m.NFiles), ci32(m.Sloc),
			ci32(m.NSymbols), cs(fmt.Sprintf("%.2f", m.Instability))})
	}
	section("BIGGEST MODULES", []string{"name", "files", "sloc", "syms", "instab"}, mr)

	fn := g.callableSyms()
	sort.SliceStable(fn, func(i, j int) bool {
		if fn[i].Cyclomatic != fn[j].Cyclomatic {
			return fn[i].Cyclomatic > fn[j].Cyclomatic
		}
		return bySymID(fn[i], fn[j]) < 0
	})
	var hr []row
	for i, s := range fn {
		if i >= 12 {
			break
		}
		hr = append(hr, row{cs(s.Name()), ci32(s.Sloc), ci32(s.Cyclomatic),
			ci32(s.Cognitive), ci32(s.MaxNesting), ci32(s.FanIn), symAt(g, s)})
	}
	section("HEAVIEST FUNCTIONS",
		[]string{"name", "sloc", "cyclo", "cog", "nest", "fan_in", "at"}, hr)

	all := append([]*Sym(nil), g.Syms...)
	sort.SliceStable(all, func(i, j int) bool {
		if all[i].FanIn != all[j].FanIn {
			return all[i].FanIn > all[j].FanIn
		}
		return bySymID(all[i], all[j]) < 0
	})
	var dr []row
	for i, s := range all {
		if i >= 12 {
			break
		}
		dr = append(dr, row{cs(s.Name()), ci32(s.FanIn), ci32(s.FanOut),
			ci32(s.Cyclomatic), ci32(s.Sloc), symAt(g, s)})
	}
	section("MOST DEPENDED ON",
		[]string{"name", "fan_in", "fan_out", "cyclo", "sloc", "at"}, dr)

	mk := map[string]int{}
	for _, m := range g.Mark {
		mk[m.Kind()]++
	}
	type mkv struct {
		k string
		v int
	}
	var mks []mkv
	for k, v := range mk {
		mks = append(mks, mkv{k, v})
	}
	sort.Slice(mks, func(i, j int) bool {
		if mks[i].v != mks[j].v {
			return mks[i].v > mks[j].v
		}
		return mks[i].k < mks[j].k
	})
	var gr []row
	for _, e := range mks {
		gr = append(gr, row{cs(e.k), ci(e.v)})
	}
	section("MARKERS LEFT IN THE CODE", []string{"kind", "n"}, gr)
}

func (g *Graph) callableSyms() []*Sym {
	out := make([]*Sym, 0, len(g.Syms))
	for _, s := range g.Syms {
		if isCallableKind(s.Kind()) {
			out = append(out, s)
		}
	}
	return out
}

type cell struct {
	kind byte
	i    int64
	f    float64
	s    string
}

func ci(v int) cell     { return cell{kind: 'i', i: int64(v)} }
func ci32(v int32) cell { return cell{kind: 'i', i: int64(v)} }
func cs(v string) cell  { return cell{kind: 's', s: v} }
func cnull() cell       { return cell{kind: 'n'} }

func (c cell) String() string {
	switch c.kind {
	case 'i':
		return strconv.FormatInt(c.i, 10)
	case 'f':
		return fmt.Sprintf("%.2f", c.f)
	case 'n':
		return "-"
	}
	return c.s
}

func (c cell) csv() string {
	if c.kind == 'n' {
		return ""
	}
	return c.String()
}

type row []cell

func (r row) csvStrings() []string {
	out := make([]string, len(r))
	for i, c := range r {
		out[i] = c.csv()
	}
	return out
}

type result struct {
	cols []string
	rows []row
}

func finish(res *result, order func(a, b row) bool, limit int) *result {
	sort.SliceStable(res.rows, func(i, j int) bool { return order(res.rows[i], res.rows[j]) })
	if limit >= 0 && len(res.rows) > limit {
		res.rows = res.rows[:limit]
	}
	return res
}

type question struct {
	name  string
	title string
	notes string
	run   func(g *Graph, mod func(string) bool, lim int) *result
}

var (
	catQueries  []*question
	catMetrics  []*question
	catBuiltOne bool
)

func catalogue(metrics bool) []*question {
	if !catBuiltOne {
		catQueries, catMetrics = queryCatalogue(), metricCatalogue()
		catBuiltOne = true
	}
	if metrics {
		return catMetrics
	}
	return catQueries
}

func symAt(g *Graph, s *Sym) cell { return cs(g.at(s.FileId, s.LineStart)) }

func isCallableKind(k string) bool {
	switch k {
	case "function", "method", "closure", "constructor":
		return true
	}
	return false
}

func okFile(g *Graph, fid int32, mod func(string) bool) bool {
	if fid <= 0 || int(fid) > len(g.Files) {
		return false
	}
	f := g.Files[fid-1]
	return f.IsTest == 0 && f.IsGenerated == 0 && mod(g.modNameOf(f.ModuleID))
}

func inMod(g *Graph, fid int32, mod func(string) bool) bool {
	if fid <= 0 || int(fid) > len(g.Files) {
		return false
	}
	return mod(g.modNameOf(g.Files[fid-1].ModuleID))
}

func bySymID(a, b *Sym) int {
	if a.FileId != b.FileId {
		return int(a.FileId - b.FileId)
	}
	if a.LineStart != b.LineStart {
		return int(a.LineStart - b.LineStart)
	}
	return int(a.Id - b.Id)
}

type reachPair struct {
	Root, Sym int32
	Hops      int32
}

type reachWalk struct {
	byCaller map[int32][]int32
	depth    []int32
	stamp    []int32
	queue    []int32
	touched  []int32
}

func newReachWalk(g *Graph) *reachWalk {
	w := &reachWalk{
		byCaller: make(map[int32][]int32, 4096),
		depth:    make([]int32, len(g.Syms)+1),
		stamp:    make([]int32, len(g.Syms)+1),
		queue:    make([]int32, 0, 1024),
		touched:  make([]int32, 0, 1024),
	}
	for i := range g.Edges {
		e := &g.Edges[i]
		if e.Self != 0 {
			continue
		}
		w.byCaller[e.Caller] = append(w.byCaller[e.Caller], e.Callee)
	}
	return w
}

func reachPairs(g *Graph, roots []int32, maxDepth int32) []reachPair {
	w := newReachWalk(g)
	out := make([]reachPair, 0, len(roots)*16)
	var gen int32
	for _, r := range roots {
		gen++
		w.touched = w.touched[:0]
		w.depth[r], w.stamp[r] = 0, gen
		w.touched = append(w.touched, r)
		w.queue = append(w.queue[:0], r)
		for len(w.queue) > 0 {
			n := w.queue[0]
			w.queue = w.queue[1:]
			d := w.depth[n]
			if d >= maxDepth {
				continue
			}
			for _, c := range w.byCaller[n] {
				if w.stamp[c] == gen && w.depth[c] <= d+1 {
					continue
				}
				w.stamp[c] = gen
				w.depth[c] = d + 1
				w.touched = append(w.touched, c)
				w.queue = append(w.queue, c)
			}
		}
		slices.Sort(w.touched)
		for _, s := range w.touched {
			out = append(out, reachPair{r, s, w.depth[s]})
		}
	}
	return out
}

type sinkSum struct {
	hops, at, sites int32
	exec            int32
	par, here, lit  int32
	open            int32
	sqlInterp, sqlL int32
	arInBlk         int32
}

type sinkGroup struct {
	sum  sinkSum
	kind string
	ok   bool
}

func substr40(s string) string {
	if s == "" {
		return ""
	}
	if len(s) <= 40 {
		return s
	}
	return s[:40]
}

func keepNested(g *Graph, s *Sym) bool {
	return s.Kind() == "method" && s.ParentId != 0 && s.ParentId < int32(len(g.Syms)) &&
		g.Syms[s.ParentId-1].Kind() == "method"
}

func joinPadded(cells []string, widths []int) string {
	var b strings.Builder
	for j, c := range cells {
		if j > 0 {
			b.WriteByte(' ')
		}
		b.WriteString(c)
		if w := widths[j] - len(c); w > 0 {
			b.WriteString(strings.Repeat(" ", w))
		}
	}
	return b.String()
}

func joinDashes(widths []int) string {
	parts := make([]string, len(widths))
	for j, w := range widths {
		parts[j] = strings.Repeat("-", w)
	}
	return strings.Join(parts, " ")
}

func sortedIDs[V any](m map[int32]V) []int32 {
	out := make([]int32, 0, len(m))
	for k := range m {
		out = append(out, k)
	}
	slices.Sort(out)
	return out
}

func sortedKeys[V any](m map[string]V) []string {
	out := make([]string, 0, len(m))
	for k := range m {
		out = append(out, k)
	}
	sort.Strings(out)
	return out
}

func sortedPairs2[K comparable, V any](m map[K]V) []K {
	out := make([]K, 0, len(m))
	for k := range m {
		out = append(out, k)
	}
	sort.Slice(out, func(i, j int) bool { return lessKey(out[i], out[j]) })
	return out
}

func sortedPairs[K comparable, V any](m map[K]V) []K { return sortedPairs2(m) }

func lessKey(a, b any) bool {
	av, bv := reflect.ValueOf(a), reflect.ValueOf(b)
	for i := 0; i < av.NumField(); i++ {
		x, y := av.Field(i), bv.Field(i)
		switch x.Kind() {
		case reflect.Int32:
			if x.Int() != y.Int() {
				return x.Int() < y.Int()
			}
		case reflect.String:
			if x.String() != y.String() {
				return x.String() < y.String()
			}
		case reflect.Bool:
			if x.Bool() != y.Bool() {
				return !x.Bool()
			}
		}
	}
	return false
}

func runNamed(name string) func(*Graph, func(string) bool, int) *result {
	return func(g *Graph, mod func(string) bool, lim int) *result {
		if f, ok := questionRuns[name]; ok {
			return f(g, mod, lim)
		}
		panic("codegraph-ruby: question has no run function: " + name)
	}
}

var questionRuns = map[string]func(*Graph, func(string) bool, int) *result{}

const maxCell = 72

func cellText(v cell) string {
	t := v.String()
	if len(t) > maxCell {
		return t[:maxCell-3] + "..."
	}
	return t
}

func render(w *bufio.Writer, res *result) {
	if len(res.rows) == 0 {
		fmt.Fprintln(w, " (no rows)")
		return
	}
	nc := len(res.cols)
	widths := make([]int, nc)
	body := make([][]string, len(res.rows))
	for i, r := range res.rows {
		body[i] = make([]string, nc)
		for j := range nc {
			if j < len(r) {
				body[i][j] = cellText(r[j])
			}
		}
	}
	for j := range nc {
		widths[j] = len(res.cols[j])
		for _, r := range body {
			if len(r[j]) > widths[j] {
				widths[j] = len(r[j])
			}
		}
	}
	fmt.Fprintln(w, " "+joinPadded(res.cols, widths))
	fmt.Fprintln(w, " "+joinDashes(widths))
	for _, r := range body {
		fmt.Fprintln(w, " "+joinPadded(r, widths))
	}
}

type colDef struct {
	name string
	get  func(*Graph, *Sym) cell
}

func num(name string, get func(*Sym) int32) colDef {
	return colDef{name, func(_ *Graph, s *Sym) cell { return ci32(get(s)) }}
}

func strc(name string, get func(*Sym) string) colDef {
	return colDef{name, func(_ *Graph, s *Sym) cell { return cs(get(s)) }}
}

func atCol() colDef {
	return colDef{"at", func(g *Graph, s *Sym) cell { return symAt(g, s) }}
}

func modCol() colDef {
	return colDef{"module_", func(g *Graph, s *Sym) cell { return cs(g.modNameOf(s.ModuleId)) }}
}

func qualCol() colDef { return strc("qual", func(s *Sym) string { return s.QualName() }) }
func nameCol() colDef { return strc("name", func(s *Sym) string { return s.Name() }) }
func kindCol() colDef { return strc("kind", func(s *Sym) string { return s.Kind() }) }

func symTable(cols []colDef, keep func(*Sym) bool, order func(a, b row) bool) func(*Graph, func(string) bool, int) *result {
	return symTableF(cols, func(_ *Graph, s *Sym) bool { return keep(s) }, okFile, order)
}

func symTableG(cols []colDef, keep func(*Graph, *Sym) bool, order func(a, b row) bool) func(*Graph, func(string) bool, int) *result {
	return symTableF(cols, keep, okFile, order)
}

func symTableF(cols []colDef, keep func(*Graph, *Sym) bool, okFn func(*Graph, int32, func(string) bool) bool, order func(a, b row) bool) func(*Graph, func(string) bool, int) *result {
	return func(g *Graph, mod func(string) bool, lim int) *result {
		res := &result{cols: make([]string, len(cols))}
		for i, c := range cols {
			res.cols[i] = c.name
		}
		var matched []*Sym
		for _, s := range g.Syms {
			if keep(g, s) && okFn(g, s.FileId, mod) {
				matched = append(matched, s)
			}
		}
		sort.Slice(matched, func(i, j int) bool { return bySymID(matched[i], matched[j]) < 0 })
		buf := make(row, len(cols))
		for _, s := range matched {
			for i, c := range cols {
				buf[i] = c.get(g, s)
			}
			res.rows = append(res.rows, append(row(nil), buf...))
		}
		return finish(res, order, lim)
	}
}

func desc2(a, b, c, d int64) bool {
	if a != b {
		return a > b
	}
	return c > d
}

func desc3(a, b, c, d, e, f int64) bool {
	if a != b {
		return a > b
	}
	if c != d {
		return c > d
	}
	return e > f
}

func calleeAdjacency(g *Graph) map[int32][]int32 {
	m := make(map[int32][]int32, 4096)
	for i := range g.Edges {
		e := &g.Edges[i]
		if e.Self != 0 {
			continue
		}
		m[e.Caller] = append(m[e.Caller], e.Callee)
	}
	return m
}

func groupCallers(g *Graph) map[int32]map[int32]bool {
	m := make(map[int32]map[int32]bool, 1024)
	for i := range g.Edges {
		e := &g.Edges[i]
		if e.Self != 0 {
			continue
		}
		if m[e.Callee] == nil {
			m[e.Callee] = map[int32]bool{}
		}
		m[e.Callee][e.Caller] = true
	}
	return m
}

func groupByParent(g *Graph) map[int32][]*Sym {
	m := make(map[int32][]*Sym, 4096)
	for _, s := range g.Syms {
		if s.ParentId != 0 {
			m[s.ParentId] = append(m[s.ParentId], s)
		}
	}
	return m
}

func groupMeta(g *Graph) map[int32][]*MetaSite {
	m := make(map[int32][]*MetaSite, 4096)
	for i := range g.MSites {
		m[g.MSites[i].SymID] = append(m[g.MSites[i].SymID], &g.MSites[i])
	}
	return m
}

func groupUnres(g *Graph) map[int32][]*Unresolved {
	m := make(map[int32][]*Unresolved, 4096)
	for i := range g.Unres {
		m[g.Unres[i].Caller] = append(m[g.Unres[i].Caller], &g.Unres[i])
	}
	return m
}

func groupBlocks(g *Graph) map[int32][]*Block {
	m := make(map[int32][]*Block, 4096)
	for i := range g.Blks {
		m[g.Blks[i].SymID] = append(m[g.Blks[i].SymID], &g.Blks[i])
	}
	return m
}

func groupInpSites(g *Graph) map[int32][]*InputSite {
	m := make(map[int32][]*InputSite, 1024)
	for i := range g.UIs {
		m[g.UIs[i].SymID] = append(m[g.UIs[i].SymID], &g.UIs[i])
	}
	return m
}

type scope struct {
	symID      int32
	qualPrefix string
	typeName   string
	typeID     int32
	depth      int32
}

type walkItem struct {
	n  tsNode
	sc scope
}

func (x *xctx) resetStats() {

	x.st = symRow{Cyclomatic: 1}
	x.calls = x.calls[:0]
	x.lits = x.lits[:0]
	x.inputs = x.inputs[:0]
	x.secrets = x.secrets[:0]
	x.gen++
	x.nOp = 0
	x.nOpnd = 0
}

func (x *xctx) opDistinct(k uint16) {
	if int(k) >= len(x.opStamp) {
		return
	}
	if x.opStamp[k] == x.gen {
		return
	}
	x.opStamp[k] = x.gen
	x.nOp++
}

func (x *xctx) opndDistinct(s string) {
	if x.opndGen[s] == x.gen {
		return
	}
	x.opndGen[s] = x.gen
	x.nOpnd++
}

func (x *xctx) bump(c uint8) { bump(&x.st, c) }
func (x *xctx) bumpN(c uint8, n int32) {
	for range n {
		bump(&x.st, c)
	}
}

func (x *xctx) measure(body tsNode, prune bool) {
	src := x.src
	st := &x.st
	x.cur.start(body)
	defer x.cur.done()
	depth := int32(0)
	loopDepth := int32(0)
	x.nestSt = x.nestSt[:0]
	x.loopSt = x.loopSt[:0]

	for {
		n := x.cur.node()

		k := tkOf(kindID(n))
		kid := int(k)

		for len(x.nestSt) > 0 && x.nestSt[len(x.nestSt)-1] >= depth {
			x.nestSt = x.nestSt[:len(x.nestSt)-1]
		}
		for len(x.loopSt) > 0 && x.loopSt[len(x.loopSt)-1] >= depth {
			x.loopSt = x.loopSt[:len(x.loopSt)-1]
			if loopDepth > 0 {
				loopDepth--
			}
		}

		isElif := false
		if kinds.ifs[kid] {
			par := parentNode(n)
			if hasNode(par) {
				pk := int(tkOf(kindID(par)))
				if kinds.ifs[pk] {
					alt := childField(par, fAlternative)
					isElif = hasNode(alt) && sameNode(alt, n)
				} else {
					gp := parentNode(par)
					if hasNode(gp) && kinds.ifs[int(tkOf(kindID(gp)))] {
						alt := childField(gp, fAlternative)
						if hasNode(alt) && sameNode(alt, par) {
							first := namedChildAt(par, 0)
							isElif = hasNode(first) && sameNode(first, n)
						}
					}
				}
			}
		}

		named := false
		if kinds.nests[kid] || kinds.loops[kid] || kinds.branches[kid] || kinds.xloops[kid] {
			named = isNamedN(n)
		}
		if named && kinds.nests[kid] && !isElif {
			x.nestSt = append(x.nestSt, depth)
			if int32(len(x.nestSt)) > st.MaxNesting {
				st.MaxNesting = int32(len(x.nestSt))
			}
		}
		if named && (kinds.loops[kid] || (kinds.xloops[kid] && x.isExtraLoop(n))) {
			x.loopSt = append(x.loopSt, depth)
			loopDepth++
			if loopDepth > st.MaxLoopDepth {
				st.MaxLoopDepth = loopDepth
			}
			st.Cyclomatic++
			st.Cognitive += max32(1, int32(len(x.nestSt)))
			x.bump(cLoopsBump)
		} else if named && kinds.branches[kid] {
			st.Cyclomatic++
			if isElif {
				st.Cognitive++
			} else {
				st.Cognitive += max32(1, int32(len(x.nestSt)))
			}
			x.bump(cBranch)
			if isElif {
				x.bump(cElif)
			}
			if loopDepth > 0 {
				x.bump(cBranchInLoop)
			}
		}

		if kid < nKinds {
			if c := kinds.counter[kid]; c != noCounter {
				x.bump(c)
			}
		}

		switch {
		case kinds.calls[kid]:
			x.onCall(n, loopDepth)
		case kinds.ops[kid]:
			st.NOperators++
			x.opDistinct(k)
		case kinds.strs[kid]:
			txt := textOf(src, n)
			x.bump(cStringLit)
			x.opndDistinct(trunc(txt, 40))
			st.NOperands++
			x.onString(n, txt, loopDepth)
		case kinds.nums[kid]:
			txt := cgStrip(textOf(src, n))
			st.NOperands++
			x.opndDistinct(txt)
			if !magicNum[txt] && numRe.MatchString(txt) {
				x.bump(cMagic)
				x.lits = append(x.lits, litRec{"number", txt, int32(startRow(n) + 1), true})
			}
			if strings.ContainsAny(txt, ".") || strings.ContainsAny(strings.ToLower(txt), "e") {
				x.bump(cFloatLit)
			}
		case kinds.cmts[kid]:
			x.bumpN(cCommentLines, int32(endRow(n)-startRow(n)+1))
		case childCount(n) == 0:
			st.NTokens++
			st.NOperands++
			x.opndDistinct(trunc(textOf(src, n), 40))
		}

		x.onNode(n, loopDepth)

		descend := true
		if prune && kid < nKinds && kinds.prune[kid] {
			descend = false
		}
		if descend && x.cur.first() {
			depth++
			continue
		}
		done := false
		for !x.cur.next() {
			if !x.cur.up() {
				done = true
				break
			}
			depth--
		}
		if done {
			st.NTokens += st.NOperators
			return
		}
	}
}

func max32(a, b int32) int32 {
	if a > b {
		return a
	}
	return b
}

func (x *xctx) isExtraLoop(n tsNode) bool {
	call := parentNode(n)
	if !hasNode(call) || kindID(call) != kindCall {
		return false
	}
	m := childField(call, fMethod)
	if !hasNode(m) {
		return false
	}
	return inSet(iteratorMethods, textOf(x.src, m))
}

func bump(s *symRow, c uint8) {
	switch c {
	case cReturns:
		s.NReturns++
	case cYield:
		s.NYield++
	case cBlockArgument:
		s.NBlockPass++
	case cDoBlock:
		s.NBlocks++
	case cLambda:
		s.NLambda++
	case cCase:
		s.NSwitch++
	case cCaseMatch:
		s.NSwitch++
	case cWhen:
		s.NCases++
	case cInClause:
		s.NCases++
	case cConditional:
		s.NTernary++
	case cRescue:
		s.NRescue++
	case cRescueModifier:
		s.NRescue++
	case cEnsure:
		s.NEnsure++
	case cRetry:
		s.NRetry++
	case cInstanceVariable:
		s.NInstanceVar++
	case cClassVariable:
		s.NClassVar++
	case cGlobalVariable:
		s.NGlobalVar++
	case cInterpolation:
		s.NStringInterp++
	case cRegexLit:
		s.NRegexLit++
	case cSubshell:
		s.NSubshell++
	case cAssign:
		s.NAssign++
	case cOperatorAssignment:
		s.NCompoundAssign++
	case cElementReference:
		s.NSubscript++
	case cHashLit:
		s.NHashLit++
	case cArrayLit:
		s.NArrayLit++
	case cStringArray:
		s.NArrayLit++
	case cSymbolArray:
		s.NArrayLit++
	case cHeredocBody:
		s.NHeredoc++
	case cAlias:
		s.NAlias++
	case cUndef:
		s.NAlias++
	case cSuper:
		s.NSuper++
	case cForwardArgument:
		s.NForwarding++
	case cForwardParameter:
		s.NForwarding++
	case cUninterpreted:
		s.NEndData++
	case cScopeResolution:
		s.NConstRef++
	case cQueryInLoop:
		s.QueryInLoop++
	case cIoInLoop:
		s.IoInLoop++
	case cLockInLoop:
		s.LockInLoop++
	case cRegexInLoop:
		s.RegexInLoop++
	case cSystemCall:
		s.NSystemCall++
	case cRedirect:
		s.NRedirect++
	case cConstantize:
		s.NConstantize++
	case cHtmlSafe:
		s.NHtmlSafe++
	case cRawSQL:
		s.NRawSql++
	case cWeakHash:
		s.NWeakHash++
	case cWeakRandom:
		s.NWeakRandom++
	case cFetch:
		s.NFetch++
	case cXxeParser:
		s.NXxeParser++
	case cDynamicOpen:
		s.NDynamicOpen++
	case cZipRead:
		s.NZipRead++
	case cLogCall:
		s.NLogCall++
	case cAuthCall:
		s.NAuthCall++
	case cOpenCall:
		s.NOpenCall++
	case cSleepCall:
		s.NSleepCall++
	case cIncludeInLoop:
		s.NIncludeInLoop++
	case cEnumInLoop:
		s.NEnumInLoop++
	case cCountInLoop:
		s.NCountInLoop++
	case cArWriteInLoop:
		s.NArWriteInLoop++
	case cSerializeInLoop:
		s.NSerializeInLoop++
	case cBlockGiven:
		s.NBlockGiven++
	case cRaise:
		s.NRaise++
	case cFreeze:
		s.NFreeze++
	case cDupClone:
		s.NDupClone++
	case cProcNew:
		s.NProcNew++
	case cLambdaCall:
		s.NLambda++
	case cThreadNew:
		s.NThreadNew++
	case cMutex:
		s.NMutex++
	case cRactor:
		s.NRactor++
	case cThreadLocal:
		s.NThreadLocal++
	case cTimeout:
		s.NTimeout++
	case cPermit:
		s.NPermit++
	case cPermitBang:
		s.NPermitBang++
	case cSqlSanitized:
		s.NSqlSanitized++
	case cToSym:
		s.NToSym++
	case cRegexDyn:
		s.NRegexDyn++
	case cEnqueue:
		s.NEnqueue++
	case cZonelessTime:
		s.NZonelessTime++
	case cConstMutate:
		s.NConstMutate++
	case cThreadJoin:
		s.NThreadJoin++
	case cMetaprogramDispatch:
		s.NMetaprogramDynamic++
	case cRescueBare:
		s.NRescueBare++
	case cRescueException:
		s.NRescueException++
	case cRescueEmpty:
		s.NRescueEmpty++
	case cRescueReraise:
		s.NRescueReraise++
	case cSymbolToProc:
		s.NSymbolToProc++
	case cClassLevelWrite:
		s.NClassLevelWrite++
	case cIterBlocks:
		s.NIterBlocks++
	case cCollectionLitInLoop:
		s.NCollectionLitInLoop++
	case cStrLitInLoop:
		s.NStrLitInLoop++
	case cClassLevelIvar:
		s.NClassLevelIvar++
	case cChainArrayAlloc:
		s.NChainArrayAlloc++
	case cMapChain:
		s.NMapChain++
	case cTimesMap:
		s.NTimesMap++
	case cRangeInclude:
		s.NRangeInclude++
	case cSaveIgnored:
		s.NSaveIgnored++
	case cLegacyChain:
		s.NLegacyChain++
	case cEnqueueInLoop:
		s.NEnqueueInLoop++
	case cMaxBlockDepth:
		s.MaxBlockDepth++
	case cLoopsBump:
		s.NLoops++
	case cBranch:
		s.NBranches++
	case cElif:
		s.NElif++
	case cBranchInLoop:
		s.BranchInLoop++
	case cStringLit:
		s.NStringLit++
	case cMagic:
		s.NMagic++
	case cFloatLit:
		s.NFloatLit++
	case cCommentLines:
		s.NCommentLines++
	case cCallSite:
		s.NCalls++
	case cCallInLoop:
		s.CallInLoop++
	case cDynamicCall:
		s.NDynamicCalls++
	case cMetaprogramTotal:
		s.NMetaprogramTotal++
	case cMassAssignSink:
		s.NMassAssign++
	case cSend:
		s.NSend++
	case cDefineMethod:
		s.NDefineMethod++
	case cMethodMissing:
		s.NMethodMissing++
	case cConstGet:
		s.NConstGet++
	case cInstanceEval:
		s.NInstanceEval++
	case cClassEval:
		s.NClassEval++
	case cInstanceVarGet:
		s.NInstanceVarGet++
	case cEval:
		s.NEval++
	case cMetaOther:
		s.NMetaprogramOther++
	case cArQuery:
		s.NArQuery++
	case cArTerminal:
		s.NArTerminal++
	case cArWrite:
		s.NArWrite++
	case cSqlLiteral:
		s.NSqlLiteral++
	case cSqlInterp:
		s.NSqlInterp++
	case cParamsRead:
		s.NParamsRead++
	default:
		panic("codegraph-ruby: unknown counter column")
	}
}

func setCount(s *symRow, c uint8, v int32) {
	switch c {
	case cReturns:
		s.NReturns = v
	case cYield:
		s.NYield = v
	case cBlockArgument:
		s.NBlockPass = v
	case cDoBlock:
		s.NBlocks = v
	case cLambda:
		s.NLambda = v
	case cCase:
		s.NSwitch = v
	case cCaseMatch:
		s.NSwitch = v
	case cWhen:
		s.NCases = v
	case cInClause:
		s.NCases = v
	case cConditional:
		s.NTernary = v
	case cRescue:
		s.NRescue = v
	case cRescueModifier:
		s.NRescue = v
	case cEnsure:
		s.NEnsure = v
	case cRetry:
		s.NRetry = v
	case cInstanceVariable:
		s.NInstanceVar = v
	case cClassVariable:
		s.NClassVar = v
	case cGlobalVariable:
		s.NGlobalVar = v
	case cInterpolation:
		s.NStringInterp = v
	case cRegexLit:
		s.NRegexLit = v
	case cSubshell:
		s.NSubshell = v
	case cAssign:
		s.NAssign = v
	case cOperatorAssignment:
		s.NCompoundAssign = v
	case cElementReference:
		s.NSubscript = v
	case cHashLit:
		s.NHashLit = v
	case cArrayLit:
		s.NArrayLit = v
	case cStringArray:
		s.NArrayLit = v
	case cSymbolArray:
		s.NArrayLit = v
	case cHeredocBody:
		s.NHeredoc = v
	case cAlias:
		s.NAlias = v
	case cUndef:
		s.NAlias = v
	case cSuper:
		s.NSuper = v
	case cForwardArgument:
		s.NForwarding = v
	case cForwardParameter:
		s.NForwarding = v
	case cUninterpreted:
		s.NEndData = v
	case cScopeResolution:
		s.NConstRef = v
	case cQueryInLoop:
		s.QueryInLoop = v
	case cIoInLoop:
		s.IoInLoop = v
	case cLockInLoop:
		s.LockInLoop = v
	case cRegexInLoop:
		s.RegexInLoop = v
	case cSystemCall:
		s.NSystemCall = v
	case cRedirect:
		s.NRedirect = v
	case cConstantize:
		s.NConstantize = v
	case cHtmlSafe:
		s.NHtmlSafe = v
	case cRawSQL:
		s.NRawSql = v
	case cWeakHash:
		s.NWeakHash = v
	case cWeakRandom:
		s.NWeakRandom = v
	case cFetch:
		s.NFetch = v
	case cXxeParser:
		s.NXxeParser = v
	case cDynamicOpen:
		s.NDynamicOpen = v
	case cZipRead:
		s.NZipRead = v
	case cLogCall:
		s.NLogCall = v
	case cAuthCall:
		s.NAuthCall = v
	case cOpenCall:
		s.NOpenCall = v
	case cSleepCall:
		s.NSleepCall = v
	case cIncludeInLoop:
		s.NIncludeInLoop = v
	case cEnumInLoop:
		s.NEnumInLoop = v
	case cCountInLoop:
		s.NCountInLoop = v
	case cArWriteInLoop:
		s.NArWriteInLoop = v
	case cSerializeInLoop:
		s.NSerializeInLoop = v
	case cBlockGiven:
		s.NBlockGiven = v
	case cRaise:
		s.NRaise = v
	case cFreeze:
		s.NFreeze = v
	case cDupClone:
		s.NDupClone = v
	case cProcNew:
		s.NProcNew = v
	case cLambdaCall:
		s.NLambda = v
	case cThreadNew:
		s.NThreadNew = v
	case cMutex:
		s.NMutex = v
	case cRactor:
		s.NRactor = v
	case cThreadLocal:
		s.NThreadLocal = v
	case cTimeout:
		s.NTimeout = v
	case cPermit:
		s.NPermit = v
	case cPermitBang:
		s.NPermitBang = v
	case cSqlSanitized:
		s.NSqlSanitized = v
	case cToSym:
		s.NToSym = v
	case cRegexDyn:
		s.NRegexDyn = v
	case cEnqueue:
		s.NEnqueue = v
	case cZonelessTime:
		s.NZonelessTime = v
	case cConstMutate:
		s.NConstMutate = v
	case cThreadJoin:
		s.NThreadJoin = v
	case cMetaprogramDispatch:
		s.NMetaprogramDynamic = v
	case cRescueBare:
		s.NRescueBare = v
	case cRescueException:
		s.NRescueException = v
	case cRescueEmpty:
		s.NRescueEmpty = v
	case cRescueReraise:
		s.NRescueReraise = v
	case cSymbolToProc:
		s.NSymbolToProc = v
	case cClassLevelWrite:
		s.NClassLevelWrite = v
	case cIterBlocks:
		s.NIterBlocks = v
	case cCollectionLitInLoop:
		s.NCollectionLitInLoop = v
	case cStrLitInLoop:
		s.NStrLitInLoop = v
	case cClassLevelIvar:
		s.NClassLevelIvar = v
	case cChainArrayAlloc:
		s.NChainArrayAlloc = v
	case cMapChain:
		s.NMapChain = v
	case cTimesMap:
		s.NTimesMap = v
	case cRangeInclude:
		s.NRangeInclude = v
	case cSaveIgnored:
		s.NSaveIgnored = v
	case cLegacyChain:
		s.NLegacyChain = v
	case cEnqueueInLoop:
		s.NEnqueueInLoop = v
	case cMaxBlockDepth:
		s.MaxBlockDepth = v
	case cLoopsBump:
		s.NLoops = v
	case cBranch:
		s.NBranches = v
	case cElif:
		s.NElif = v
	case cBranchInLoop:
		s.BranchInLoop = v
	case cStringLit:
		s.NStringLit = v
	case cMagic:
		s.NMagic = v
	case cFloatLit:
		s.NFloatLit = v
	case cCommentLines:
		s.NCommentLines = v
	case cCallSite:
		s.NCalls = v
	case cCallInLoop:
		s.CallInLoop = v
	case cDynamicCall:
		s.NDynamicCalls = v
	case cMetaprogramTotal:
		s.NMetaprogramTotal = v
	case cMassAssignSink:
		s.NMassAssign = v
	case cSend:
		s.NSend = v
	case cDefineMethod:
		s.NDefineMethod = v
	case cMethodMissing:
		s.NMethodMissing = v
	case cConstGet:
		s.NConstGet = v
	case cInstanceEval:
		s.NInstanceEval = v
	case cClassEval:
		s.NClassEval = v
	case cInstanceVarGet:
		s.NInstanceVarGet = v
	case cEval:
		s.NEval = v
	case cMetaOther:
		s.NMetaprogramOther = v
	case cArQuery:
		s.NArQuery = v
	case cArTerminal:
		s.NArTerminal = v
	case cArWrite:
		s.NArWrite = v
	case cSqlLiteral:
		s.NSqlLiteral = v
	case cSqlInterp:
		s.NSqlInterp = v
	case cParamsRead:
		s.NParamsRead = v
	}
}

type interner struct {
	m map[string]string
}

func (in *interner) do(s string) string {
	if v, ok := in.m[s]; ok {
		return v
	}
	if in.m == nil {
		in.m = make(map[string]string, 4096)
	}
	in.m[s] = s
	return s
}

type cgStr struct{ Off, Ln uint64 }

const cgExtBase = uint64(1) << 62

var (
	cgArena []byte
	// cgArenaBase is the atomic read side of cgArena. The parse workers hold
	// cgStr values (file paths, names) and resolve them to strings while the
	// main goroutine is still interning new ones in linkOne; reading the
	// growable cgArena slice header there raced with append's reallocation.
	// Publishing the backing-array base through an atomic pointer means
	// readers never touch the mutable header, and a reallocation merely
	// leaves an old (still GC-reachable through the reader's string) array
	// behind. An in-place append never changes the base.
	cgArenaBase atomic.Pointer[byte]
	cgExt       []byte
	cgIntern    map[string]cgStr
	cgMu        sync.Mutex
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
	cgArenaBase.Store(unsafe.SliceData(cgArena))
	v := cgStr{off, uint64(len(s))}
	if cgIntern == nil {
		cgIntern = make(map[string]cgStr, 1<<16)
	}
	cgIntern[s] = v
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

var cgZero [4096]byte

func cgZeroRow(p unsafe.Pointer, n uintptr) {
	copy(unsafe.Slice((*byte)(p), n)[:n], cgZero[:n])
}

func (s cgStr) Str() string {
	if s.Ln == 0 {
		return ""
	}
	if s.Off >= cgExtBase {
		return unsafe.String(&cgExt[s.Off-cgExtBase], int(s.Ln))
	}
	base := cgArenaBase.Load()
	if base == nil {
		return ""
	}
	return unsafe.String((*byte)(unsafe.Add(unsafe.Pointer(base), uintptr(s.Off))), int(s.Ln))
}

type File struct {
	ID                                     int32
	path, dir, base, ext, lang             cgStr
	ModuleID                               int32
	Bytes, Lines, Sloc                     int32
	Blank, Comment, MaxLine                int32
	sha1                                   cgStr
	Parsed                                 int32
	IsTest, IsGenerated, IsVendored        int32
	ParseErrors, Missing                   int32
	ParseMs                                float64
	NSymbols, NFunctions, NTypes, NImports int32
	TotalCyclo, MaxCyclo, TotalRisk        int32
}

func (f *File) Path() string { return f.path.Str() }
func (f *File) Dir() string  { return f.dir.Str() }
func (f *File) Base() string { return f.base.Str() }
func (f *File) Ext() string  { return f.ext.Str() }
func (f *File) Lang() string { return f.lang.Str() }
func (f *File) Sha1() string { return f.sha1.Str() }

type Module struct {
	ID                              int32
	name, kind                      cgStr
	NFiles, NSymbols, NPublic, Sloc int32
	FanIn, FanOut                   int32
	Instability                     float64
}

func (m *Module) Name() string { return m.name.Str() }
func (m *Module) Kind() string { return m.kind.Str() }

type Param struct {
	SymID, Pos int32
	name       cgStr
	HasName    bool
	typ        cgStr
	def        cgStr
	HasDefault bool
	Optional   int32
	Variadic   int32
	Ref        int32
	Mutable    int32
	Nullable   int32
	Generic    int32
	Untyped    int32
	TypeDepth  int32
}

func (p *Param) Name() string    { return p.name.Str() }
func (p *Param) Type() string    { return p.typ.Str() }
func (p *Param) Default() string { return p.def.Str() }

type Field struct {
	SymID, Ord        int32
	name, typ, vis    cgStr
	Line              int32
	Static, Const_    int32
	Mutable, Nullable int32
	Collection        int32
	Untyped           int32
	HasDefault        int32
	TypeDepth         int32
}

func (f *Field) Name() string { return f.name.Str() }
func (f *Field) Type() string { return f.typ.Str() }
func (f *Field) Vis() string  { return f.vis.Str() }

type Edge struct {
	Caller, Callee int32
	NCalls         int32
	SameFile       int32
	SameModule     int32
	Self           int32
}

type CallSite struct{ Caller, Callee, Line int32 }

type Unresolved struct {
	Caller    int32
	name      cgStr
	N         int32
	FirstLine int32
}

func (u *Unresolved) Name() string { return u.name.Str() }

type Import struct {
	ID, FileID  int32
	target      cgStr
	TargetID    int32
	HasTargetID bool
	alias       cgStr
	HasAlias    bool
	kind        cgStr
	Line        int32
	External    int32
	Relative    int32
	Wildcard    int32
	TypeOnly    int32
	Dynamic     int32
	NNames      int32
}

func (i *Import) Target() string { return i.target.Str() }
func (i *Import) Alias() string  { return i.alias.Str() }
func (i *Import) Kind() string   { return i.kind.Str() }

type Hazard struct {
	SymID     int32
	pattern   cgStr
	category  cgStr
	N         int32
	FirstLine int32
}

func (h *Hazard) Pattern() string  { return h.pattern.Str() }
func (h *Hazard) Category() string { return h.category.Str() }

type Literal struct {
	ID, SymID int32
	FileID    int32
	kind      cgStr
	value     cgStr
	Line      int32
	Magic     int32
}

func (l *Literal) Kind() string  { return l.kind.Str() }
func (l *Literal) Value() string { return l.value.Str() }

type Marker struct {
	ID, FileID int32
	SymID      int32
	HasSym     bool
	kind       cgStr
	Line       int32
	text       cgStr
}

func (m *Marker) Kind() string { return m.kind.Str() }
func (m *Marker) Text() string { return m.text.Str() }

type EnumMember struct {
	SymID, Ord int32
	name       cgStr
	value      cgStr
	HasValue   bool
	NFields    int32
}

func (e *EnumMember) Name() string  { return e.name.Str() }
func (e *EnumMember) Value() string { return e.value.Str() }

type Local struct {
	SymID, Ord      int32
	name            cgStr
	typ             cgStr
	Line            int32
	Const_, Mutable int32
	Untyped         int32
	HasInit, InLoop int32
	ScopeDepth      int32
}

func (l *Local) Name() string { return l.name.Str() }
func (l *Local) Type() string { return l.typ.Str() }

type RubyModule struct {
	SymID, FileID           int32
	name                    cgStr
	IsModule                int32
	IsConcern               int32
	HasIncludedBlock        int32
	HasClassMethodsBlock    int32
	superclass              cgStr
	NMixins, NDefs          int32
	NClassDefs, NClassIvars int32
	NClassVars, NGlobals    int32
	NDelegates              int32
	ReopensCore             int32
	Line                    int32
}

func (r *RubyModule) Name() string       { return r.name.Str() }
func (r *RubyModule) Superclass() string { return r.superclass.Str() }

type Mixin struct {
	ID, HostID       int32
	FileID           int32
	host, mixin      cgStr
	mixinShort, kind cgStr
	InSingleton      int32
	Line             int32
}

func (m *Mixin) Host() string       { return m.host.Str() }
func (m *Mixin) Mixin() string      { return m.mixin.Str() }
func (m *Mixin) MixinShort() string { return m.mixinShort.Str() }
func (m *Mixin) Kind() string       { return m.kind.Str() }

type MetaSite struct {
	ID, SymID   int32
	FileID      int32
	api, arg    cgStr
	Literal     int32
	FromParams  int32
	FromVar     int32
	OnHeredoc   int32
	InClassBody int32
	LoopDepth   int32
	Line        int32
}

func (m *MetaSite) API() string { return m.api.Str() }
func (m *MetaSite) Arg() string { return m.arg.Str() }

type Block struct {
	ID, SymID     int32
	FileID        int32
	method        cgStr
	receiver      cgStr
	style         cgStr
	IsIteration   int32
	Depth         int32
	NParams       int32
	BodySloc      int32
	NQueries      int32
	NAllocs       int32
	CapturesOuter int32
	Line          int32
	NExits        int32
}

func (b *Block) Method() string   { return b.method.Str() }
func (b *Block) Receiver() string { return b.receiver.Str() }
func (b *Block) Style() string    { return b.style.Str() }

type ARQuery struct {
	ID, SymID        int32
	FileID           int32
	model, api       cgStr
	buildKind        cgStr
	HasInterpolation int32
	IsSanitized      int32
	FromParams       int32
	IsStringArg      int32
	LoopDepth, Chain int32
	Line             int32
}

func (a *ARQuery) Model() string     { return a.model.Str() }
func (a *ARQuery) API() string       { return a.api.Str() }
func (a *ARQuery) BuildKind() string { return a.buildKind.Str() }

type ARCallback struct {
	ID, SymID   int32
	FileID      int32
	host, hook  cgStr
	method      cgStr
	Conditional int32
	Block       int32
	Association int32
	IssuesQuery int32
	TargetID    int32
	HasTargetID bool
	Line        int32
}

func (c *ARCallback) Host() string   { return c.host.Str() }
func (c *ARCallback) Hook() string   { return c.hook.Str() }
func (c *ARCallback) Method() string { return c.method.Str() }

type MonkeyPatch struct {
	ID, SymID   int32
	HasSym      bool
	MethodID    int32
	HasMethodID bool
	FileID      int32
	coreClass   cgStr
	method      cgStr
	Operator    int32
	Singleton   int32
	Line        int32
}

func (m *MonkeyPatch) CoreClass() string { return m.coreClass.Str() }
func (m *MonkeyPatch) Method() string    { return m.method.Str() }

type InputSite struct {
	ID, SymID int32
	FileID    int32
	vr        cgStr
	kind      cgStr
	Line      int32
	InLoop    int32
}

func (u *InputSite) Var() string  { return u.vr.Str() }
func (u *InputSite) Kind() string { return u.kind.Str() }

type Secret struct {
	ID, SymID int32
	FileID    int32
	value     cgStr
	Line      int32
}

func (s *Secret) Value() string { return s.value.Str() }

type cgMetaRow struct{ K, V cgStr }

func (m *cgMetaRow) Key() string { return m.K.Str() }
func (m *cgMetaRow) Val() string { return m.V.Str() }

type Graph struct {
	Files    []*File
	Mods     []*Module
	Syms     []*Sym
	fileRows []File
	modRows  []Module
	symRows  []Sym
	cold     []symCold
	sigRefs  []sigRef
	coldWide map[int32]symColdWide
	halv     []int64
	sigBases []uint64
	sigBlk   int
	sigOff   int
	Params   []Param
	Fields   []Field
	Locals   []Local
	Edges    []Edge
	Sites    []CallSite
	Unres    []Unresolved
	Imps     []Import
	Haz      []Hazard
	Lits     []Literal
	Mark     []Marker
	Enums    []EnumMember

	RMods  []RubyModule
	Mixins []Mixin
	MSites []MetaSite
	Blks   []Block
	ARQs   []ARQuery
	ARCBs  []ARCallback
	MPs    []MonkeyPatch
	UIs    []InputSite
	Secs   []Secret

	Meta []cgMetaRow

	in interner

	byFile   map[int32][]int32
	byParent map[int32][]int32
	byKind   map[string][]int32
	modName  map[string]int32
	filePath map[string]int32

	astBlob  []byte
	astTrees []*tsTree
}

func newGraph() *Graph {
	return &Graph{
		in:       interner{},
		byFile:   map[int32][]int32{},
		byParent: map[int32][]int32{},
		byKind:   map[string][]int32{},
		modName:  map[string]int32{},
		filePath: map[string]int32{},
	}
}

func (g *Graph) setMetaExt(k, v string) {
	for i := range g.Meta {
		if g.Meta[i].K.Str() == k {
			g.Meta[i].V = cgPutExt(v)
			return
		}
	}
	g.Meta = append(g.Meta, cgMetaRow{K: cgPutExt(k), V: cgPutExt(v)})
}

func (g *Graph) setMeta(k, v string) {
	for i := range g.Meta {
		if g.Meta[i].K.Str() == k {
			g.Meta[i].V = cgPut(v)
			return
		}
	}
	g.Meta = append(g.Meta, cgMetaRow{K: cgPut(k), V: cgPut(v)})
}

func (g *Graph) index() {
	for _, s := range g.Syms {
		g.byFile[s.FileId] = append(g.byFile[s.FileId], s.Id)
		if s.ParentId != 0 {
			g.byParent[s.ParentId] = append(g.byParent[s.ParentId], s.Id)
		}
		g.byKind[s.Kind()] = append(g.byKind[s.Kind()], s.Id)
	}
	for _, m := range g.Mods {
		g.modName[m.Name()] = m.ID
	}
	for _, f := range g.Files {
		g.filePath[f.Path()] = f.ID
	}
}

func (g *Graph) mod(id int32) *Module {
	if id <= 0 || int(id) > len(g.Mods) {
		return nil
	}
	return g.Mods[id-1]
}

func (g *Graph) modNameOf(id int32) string {
	m := g.mod(id)
	if m == nil {
		return ""
	}
	return m.Name()
}

func (g *Graph) at(fid, line int32) string {
	if fid <= 0 || int(fid) > len(g.Files) {
		return ""
	}
	return g.Files[fid-1].Path() + ":" + strconv.Itoa(int(line))
}

func (g *Graph) fileIsTest(fid int32) bool {
	if fid <= 0 || int(fid) > len(g.Files) {
		return false
	}
	return g.Files[fid-1].IsTest != 0
}

func (g *Graph) fileIsGenerated(fid int32) bool {
	if fid <= 0 || int(fid) > len(g.Files) {
		return false
	}
	return g.Files[fid-1].IsGenerated != 0
}

func newParser() *tsParser { return tsParserNew() }

type buildOpts struct {
	includeTests     bool
	includeGenerated bool
	includeVendored  bool
	quiet            bool
	threads          int
	window           int
	budget           int64
	gcPercent        int
	keepTrees        bool
}

type builder struct {
	g       *Graph
	opts    buildOpts
	root    string
	disc    *discovery
	nParsed int
	nFailed int
	skipped skipCounts
	t0      time.Time

	budget  int64
	threads int

	fouts      chan *fileOut
	symBase    int32
	regNames   []regName
	regQuals   []regQual
	pendChunks [][]pendCall
	ruby4Files int32

	symBlocks   [][]Sym
	symBIX      int
	symBOFF     int
	symBlockCap int
	firstSymBlk int

	trees [][]tsRec
}

const symBlockLen = 2048

func (b *builder) newSym() *Sym {
	if b.symBlocks == nil {
		n := symBlockLen
		if b.firstSymBlk > 0 && b.firstSymBlk < n {
			n = b.firstSymBlk
		}
		b.symBlocks = append(b.symBlocks, make([]Sym, n))
		b.symBIX, b.symBOFF, b.symBlockCap = 0, 0, n
	} else if b.symBOFF == b.symBlockCap {
		b.symBlocks = append(b.symBlocks, make([]Sym, symBlockLen))
		b.symBIX = len(b.symBlocks) - 1
		b.symBOFF, b.symBlockCap = 0, symBlockLen
	}
	s := &b.symBlocks[b.symBIX][b.symBOFF]
	b.symBOFF++
	return s
}

func build(root string, opts buildOpts) (*Graph, int, error) {
	b := &builder{opts: opts, root: root, g: newGraph(), t0: time.Now(),
		budget: opts.budget, threads: opts.threads}
	b.fouts = make(chan *fileOut, b.threads*8)
	if !opts.quiet {
		fmt.Println("  " + parserBanner())
	}
	t0 := time.Now()
	b.disc = &discovery{realRoot: mustReal(root), modByName: map[string]int32{}}
	b.disc.walkAll(root)
	if b.opts.keepTrees {
		b.trees = make([][]tsRec, len(b.disc.files))
	}
	tDisc := time.Since(t0)
	if !opts.quiet {
		fmt.Printf("  %d ruby files discovered in %.1fs\n", len(b.disc.files), tDisc.Seconds())
	}

	restoreGC := tightenGC(opts.gcPercent)
	defer restoreGC()

	t1 := time.Now()
	b.initTables()

	slots := newByteWindow(b.budget)
	type done struct {
		idx int32
		fo  *fileOut
	}
	finished := make(chan done, b.threads)
	var (
		next int32
		mu   sync.Mutex
		wg   sync.WaitGroup
	)
	for w := 0; w < b.threads; w++ {
		wg.Go(func() {
			x := newXctx()
			x.opt = opts
			p := newParser()
			defer p.free()
			for {
				mu.Lock()
				i := int(next)
				if i < len(b.disc.files) {
					next++
				}
				mu.Unlock()
				if i >= len(b.disc.files) {
					return
				}
				want := int64(b.disc.files[i].Bytes) + minFileSlot
				slots.take(want)
				var fo *fileOut
				select {
				case fo = <-b.fouts:
				default:
					fo = new(fileOut)
				}
				fo = x.runFileWith(fo, p, int32(i), b.disc.files[i], b.full(i))
				slots.give(want)
				finished <- done{int32(i), fo}
			}
		})
	}
	closed := make(chan struct{})
	go func() { wg.Wait(); close(closed) }()

	pending := make(map[int32]*fileOut, b.threads*2)

	step := max(len(b.disc.files)/20, 1)
	progress := func(done int) {
		if !opts.quiet && done%step == 0 {
			fmt.Printf("  ... %d/%d files\n", done, len(b.disc.files))
		}
	}

	nextIdx := int32(0)
	nFiles := int32(len(b.disc.files))
	for nextIdx < nFiles {
		for {
			fo, ok := pending[nextIdx]
			if !ok {
				break
			}
			b.linkOne(int(nextIdx), fo)
			delete(pending, nextIdx)
			nextIdx++
			progress(int(nextIdx))
		}
		if nextIdx >= nFiles {
			break
		}
		select {
		case d := <-finished:
			pending[d.idx] = d.fo
		case <-closed:

			for draining := true; draining; {
				select {
				case d := <-finished:
					pending[d.idx] = d.fo
				default:
					draining = false
				}
			}
			if int32(len(pending)) != nFiles-nextIdx {

				fmt.Fprintf(os.Stderr,
					"  BUG: %d file results unaccounted for at link time"+
						" (file %d of %d); the graph is incomplete\n",
					nFiles-nextIdx-int32(len(pending)), nextIdx+1, nFiles)
			}
			for nextIdx < nFiles {
				fo, ok := pending[nextIdx]
				if !ok {
					break
				}
				b.linkOne(int(nextIdx), fo)
				delete(pending, nextIdx)
				nextIdx++
				progress(int(nextIdx))
			}
		}
	}
	b.finishCollect()
	nSyms := b.symCount()
	if !opts.quiet {
		fmt.Printf("  %d symbols parsed in %.1fs\n", nSyms, time.Since(t1).Seconds())
	}
	if b.nFailed > 0 && (b.nFailed > b.nParsed/100 || !opts.quiet) {
		fmt.Fprintf(os.Stderr,
			"  WARNING: %d of %d file(s) FAILED to parse and contributed nothing.\n"+
				"           Re-run with CODEGRAPH_DEBUG=1 for the tracebacks.\n",
			b.nFailed, b.nParsed)
	}
	if b.nParsed > 0 && b.symCount() == 0 {
		fmt.Fprintf(os.Stderr,
			"  WARNING: %d file(s) were read and produced NO symbols. Every\n"+
				"           query below will be empty for that reason, not because the\n"+
				"           code is clean. Check --report for parse errors.\n", b.nParsed)
	}
	t2 := time.Now()
	b.resolve()
	if !opts.quiet {
		fmt.Printf("  call graph built in %.1fs\n", time.Since(t2).Seconds())
	}
	b.resolveImports()
	b.manifests()

	t3 := time.Now()
	b.aggregate()
	if !opts.quiet {
		fmt.Printf("  aggregates materialized in %.1fs\n", time.Since(t3).Seconds())
	}
	b.writeMeta()
	t4 := time.Now()
	b.g.index()
	if b.opts.keepTrees {
		trees := make([]*tsTree, len(b.trees))
		for i := range b.trees {
			if len(b.trees[i]) > 0 {
				trees[i] = &tsTree{recs: b.trees[i]}
			}
		}
		b.g.astTrees = trees
	}
	if !opts.quiet {
		fmt.Printf("  indexed in %.1fs\n", time.Since(t4).Seconds())
	}
	return b.g, b.nParsed, nil
}

func (b *builder) symCount() int { return len(b.g.Syms) }

func (b *builder) full(i int) string {
	return filepath.Join(b.root, b.disc.files[i].Path())
}

func (b *builder) initTables() {
	g := b.g

	names := make([]string, 0, len(b.disc.modByName))
	for n := range b.disc.modByName {
		names = append(names, n)
	}
	sort.Slice(names, func(i, j int) bool {
		return b.disc.modByName[names[i]] < b.disc.modByName[names[j]]
	})
	g.modRows = make([]Module, len(names))
	g.Mods = make([]*Module, len(names))
	for i, n := range names {
		m := &g.modRows[i]
		cgZeroRow(unsafe.Pointer(m), unsafe.Sizeof(*m))
		m.ID = int32(i + 1)
		m.name = cgPut(n)
		m.kind = cgPut(moduleKind(n))
		g.Mods[i] = m
	}
	g.Files = make([]*File, len(b.disc.files))
	copy(g.Files, b.disc.files)

	var bytes int64
	for _, f := range b.disc.files {
		bytes += int64(f.Bytes)
	}
	est := int(bytes/500) + 64
	b.firstSymBlk = est
	g.Syms = make([]*Sym, 0, est)
	g.cold = make([]symCold, 0, est)
	g.sigRefs = make([]sigRef, 0, est)
	g.halv = make([]int64, 0, est)
	g.Edges = make([]Edge, 0, est/2)
	g.Params = make([]Param, 0, est)
}

func (b *builder) linkOne(i int, fo *fileOut) {
	g := b.g
	if b.opts.keepTrees {
		b.trees[fo.idx] = fo.recs
		fo.recs = nil
	}
	f := b.disc.files[i]
	f.Lines, f.Sloc, f.Blank, f.Comment, f.MaxLine = fo.lines, fo.sloc, fo.blank, fo.cmt, fo.maxlen
	f.sha1 = cgPut(fo.sha1)
	f.ParseErrors, f.Missing = fo.parseErrs, fo.missing
	f.IsGenerated = b2i(fo.isGen)
	f.Parsed = b2i(fo.parsed)
	if fo.denied {
		b.skipped.denied++
	}
	if fo.parsed {
		b.nParsed++
		if fo.fails {
			b.nFailed++
			f.Parsed = 0
		}
	}
	base := b.symBase
	for k := range fo.syms {
		r := &fo.syms[k]
		r.Id = base + r.Id
		if r.ParentId != 0 {
			r.ParentId += base
		}
		hs, c, ct, w := b.convertSym(r)
		g.Syms = append(g.Syms, hs)
		g.cold = append(g.cold, c)
		g.sigRefs = append(g.sigRefs, ct)
		if w != nil {
			if g.coldWide == nil {
				g.coldWide = map[int32]symColdWide{}
			}
			g.coldWide[hs.Id] = *w
		}
	}
	b.symBase = base + int32(len(fo.syms))
	b.rebaseFile(fo, base)
	for k := range fo.regNames {
		fo.regNames[k].sid += base
		b.regNames = append(b.regNames, fo.regNames[k])
	}
	for k := range fo.regQuals {
		b.regQuals = append(b.regQuals, regQual{fo.regQuals[k].qual, base + fo.regQuals[k].sid})
	}
	for k := range fo.pend {
		fo.pend[k].sid += base
		fo.pend[k].name = g.in.do(fo.pend[k].name)
		fo.pend[k].typeName = g.in.do(fo.pend[k].typeName)
	}
	// One exact-size chunk per file instead of growing one shared slice by
	// doubling: the worker recycles fo.pend, so the copy is required either
	// way, and chunk order (file order) is the order resolve consumes.
	if len(fo.pend) > 0 {
		chunk := make([]pendCall, len(fo.pend))
		copy(chunk, fo.pend)
		b.pendChunks = append(b.pendChunks, chunk)
	}
	b.ruby4Files += b2i(fo.ruby4)
	b.recycle(fo)
}

func (b *builder) recycle(fo *fileOut) {
	fo.lines, fo.sloc, fo.blank, fo.cmt, fo.maxlen = 0, 0, 0, 0, 0
	fo.sha1 = ""
	fo.tooBig, fo.denied = false, false
	fo.parsed, fo.isGen, fo.ruby4, fo.fails = false, false, false, false
	fo.parseErrs, fo.missing = 0, 0
	fo.syms = fo.syms[:0]
	fo.params = fo.params[:0]
	fo.fields = fo.fields[:0]
	fo.lits = fo.lits[:0]
	fo.marks = fo.marks[:0]
	fo.imps = fo.imps[:0]
	fo.hazs = fo.hazs[:0]
	fo.rmods = fo.rmods[:0]
	fo.mixins = fo.mixins[:0]
	fo.msites = fo.msites[:0]
	fo.blks = fo.blks[:0]
	fo.arqs = fo.arqs[:0]
	fo.arcbs = fo.arcbs[:0]
	fo.mps = fo.mps[:0]
	fo.uis = fo.uis[:0]
	fo.secs = fo.secs[:0]
	fo.regNames = fo.regNames[:0]
	fo.regQuals = fo.regQuals[:0]
	fo.pend = fo.pend[:0]
	fo.recs = fo.recs[:0]
	select {
	case b.fouts <- fo:
	default:
	}
}

func (b *builder) finishCollect() {
	g := b.g
	g.symRows = make([]Sym, len(g.Syms))
	for i, s := range g.Syms {
		g.symRows[i] = *s
		g.Syms[i] = &g.symRows[i]
	}
	g.fileRows = make([]File, len(b.disc.files))
	for i, f := range b.disc.files {
		g.fileRows[i] = *f
		g.Files[i] = &g.fileRows[i]
	}
	b.g.index()
}

func (b *builder) rebaseFile(fo *fileOut, base int32) {
	g := b.g
	fid := b.disc.files[fo.idx].ID
	fix := func(sid int32) int32 {
		if sid == 0 {
			return 0
		}
		return base + sid
	}
	for i := range fo.params {
		w := &fo.params[i]
		g.Params = append(g.Params, Param{})
		rw := &g.Params[len(g.Params)-1]
		cgZeroRow(unsafe.Pointer(rw), unsafe.Sizeof(*rw))
		p := &g.Params[len(g.Params)-1]
		p.SymID = fix(w.SymID)
		p.Pos = w.Pos
		p.name = cgPut(w.Name)
		p.HasName = w.HasName
		p.typ = cgPut(w.Type)
		p.def = cgPut(w.Default)
		p.HasDefault = w.HasDefault
		p.Optional = w.Optional
		p.Variadic = w.Variadic
		p.Ref = w.Ref
		p.Mutable = w.Mutable
		p.Nullable = w.Nullable
		p.Generic = w.Generic
		p.Untyped = w.Untyped
		p.TypeDepth = w.TypeDepth
	}
	for i := range fo.fields {
		w := &fo.fields[i]
		g.Fields = append(g.Fields, Field{})
		rw := &g.Fields[len(g.Fields)-1]
		cgZeroRow(unsafe.Pointer(rw), unsafe.Sizeof(*rw))
		f := &g.Fields[len(g.Fields)-1]
		f.SymID = fix(w.SymID)
		f.Ord = w.Ord
		f.name = cgPut(w.Name)
		f.typ = cgPut(w.Type)
		f.vis = cgPut(w.Vis)
		f.Line = w.Line
		f.Static = w.Static
		f.Const_ = w.Const_
		f.Mutable = w.Mutable
		f.Nullable = w.Nullable
		f.Collection = w.Collection
		f.Untyped = w.Untyped
		f.HasDefault = w.HasDefault
		f.TypeDepth = w.TypeDepth
	}
	for i := range fo.hazs {
		w := &fo.hazs[i]
		g.Haz = append(g.Haz, Hazard{})
		rw := &g.Haz[len(g.Haz)-1]
		cgZeroRow(unsafe.Pointer(rw), unsafe.Sizeof(*rw))
		h := &g.Haz[len(g.Haz)-1]
		h.SymID = fix(w.SymID)
		h.pattern = cgPut(w.Pattern)
		h.category = cgPut(w.Category)
		h.N = w.N
		h.FirstLine = w.FirstLine
	}
	for i := range fo.lits {
		w := &fo.lits[i]
		g.Lits = append(g.Lits, Literal{})
		rw := &g.Lits[len(g.Lits)-1]
		cgZeroRow(unsafe.Pointer(rw), unsafe.Sizeof(*rw))
		l := &g.Lits[len(g.Lits)-1]
		l.ID = int32(len(g.Lits) + 1)
		l.SymID = fix(w.SymID)
		l.FileID = fid
		l.kind = cgPut(w.Kind)
		l.value = cgPut(w.Value)
		l.Line = w.Line
		l.Magic = w.Magic
	}
	for i := range fo.marks {
		w := &fo.marks[i]
		g.Mark = append(g.Mark, Marker{})
		rw := &g.Mark[len(g.Mark)-1]
		cgZeroRow(unsafe.Pointer(rw), unsafe.Sizeof(*rw))
		m := &g.Mark[len(g.Mark)-1]
		m.ID = int32(len(g.Mark) + 1)
		m.FileID = fid
		m.SymID = w.SymID
		m.HasSym = w.HasSym
		m.kind = cgPut(w.Kind)
		m.Line = w.Line
		m.text = cgPut(w.Text)
	}
	for i := range fo.imps {
		w := &fo.imps[i]
		g.Imps = append(g.Imps, Import{})
		rw := &g.Imps[len(g.Imps)-1]
		cgZeroRow(unsafe.Pointer(rw), unsafe.Sizeof(*rw))
		im := &g.Imps[len(g.Imps)-1]
		im.ID = int32(len(g.Imps) + 1)
		im.FileID = fid
		im.target = cgPut(w.Target)
		im.TargetID = w.TargetID
		im.HasTargetID = w.HasTargetID
		im.alias = cgPut(w.Alias)
		im.HasAlias = w.HasAlias
		im.kind = cgPut(w.Kind)
		im.Line = w.Line
		im.External = w.External
		im.Relative = w.Relative
		im.Wildcard = w.Wildcard
		im.TypeOnly = w.TypeOnly
		im.Dynamic = w.Dynamic
		im.NNames = w.NNames
	}
	for i := range fo.rmods {
		w := &fo.rmods[i]
		g.RMods = append(g.RMods, RubyModule{})
		rw := &g.RMods[len(g.RMods)-1]
		cgZeroRow(unsafe.Pointer(rw), unsafe.Sizeof(*rw))
		r := &g.RMods[len(g.RMods)-1]
		r.SymID = fix(w.SymID)
		r.FileID = fid
		r.name = cgPut(w.Name)
		r.IsModule = w.IsModule
		r.IsConcern = w.IsConcern
		r.HasIncludedBlock = w.HasIncludedBlock
		r.HasClassMethodsBlock = w.HasClassMethodsBlock
		r.superclass = cgPut(w.Superclass)
		r.NMixins = w.NMixins
		r.NDefs = w.NDefs
		r.NClassDefs = w.NClassDefs
		r.NClassIvars = w.NClassIvars
		r.NClassVars = w.NClassVars
		r.NGlobals = w.NGlobals
		r.NDelegates = w.NDelegates
		r.ReopensCore = w.ReopensCore
		r.Line = w.Line
	}
	for i := range fo.mixins {
		w := &fo.mixins[i]
		g.Mixins = append(g.Mixins, Mixin{})
		rw := &g.Mixins[len(g.Mixins)-1]
		cgZeroRow(unsafe.Pointer(rw), unsafe.Sizeof(*rw))
		mx := &g.Mixins[len(g.Mixins)-1]
		mx.ID = int32(len(g.Mixins) + 1)
		mx.HostID = fix(w.HostID)
		mx.FileID = fid
		mx.host = cgPut(w.Host)
		mx.mixin = cgPut(w.Mixin)
		mx.mixinShort = cgPut(w.MixinShort)
		mx.kind = cgPut(w.Kind)
		mx.InSingleton = w.InSingleton
		mx.Line = w.Line
	}
	for i := range fo.msites {
		w := &fo.msites[i]
		g.MSites = append(g.MSites, MetaSite{})
		rw := &g.MSites[len(g.MSites)-1]
		cgZeroRow(unsafe.Pointer(rw), unsafe.Sizeof(*rw))
		m := &g.MSites[len(g.MSites)-1]
		m.ID = int32(len(g.MSites) + 1)
		m.SymID = fix(w.SymID)
		m.FileID = fid
		m.api = cgPut(w.API)
		m.arg = cgPut(w.Arg)
		m.Literal = w.Literal
		m.FromParams = w.FromParams
		m.FromVar = w.FromVar
		m.OnHeredoc = w.OnHeredoc
		m.InClassBody = w.InClassBody
		m.LoopDepth = w.LoopDepth
		m.Line = w.Line
	}
	for i := range fo.blks {
		w := &fo.blks[i]
		g.Blks = append(g.Blks, Block{})
		rw := &g.Blks[len(g.Blks)-1]
		cgZeroRow(unsafe.Pointer(rw), unsafe.Sizeof(*rw))
		bl := &g.Blks[len(g.Blks)-1]
		bl.ID = int32(len(g.Blks) + 1)
		bl.SymID = fix(w.SymID)
		bl.FileID = fid
		bl.method = cgPut(w.Method)
		bl.receiver = cgPut(w.Receiver)
		bl.style = cgPut(w.Style)
		bl.IsIteration = w.IsIteration
		bl.Depth = w.Depth
		bl.NParams = w.NParams
		bl.BodySloc = w.BodySloc
		bl.NQueries = w.NQueries
		bl.NAllocs = w.NAllocs
		bl.CapturesOuter = w.CapturesOuter
		bl.Line = w.Line
		bl.NExits = w.NExits
	}
	for i := range fo.arqs {
		w := &fo.arqs[i]
		g.ARQs = append(g.ARQs, ARQuery{})
		rw := &g.ARQs[len(g.ARQs)-1]
		cgZeroRow(unsafe.Pointer(rw), unsafe.Sizeof(*rw))
		a := &g.ARQs[len(g.ARQs)-1]
		a.ID = int32(len(g.ARQs) + 1)
		a.SymID = fix(w.SymID)
		a.FileID = fid
		a.model = cgPut(w.Model)
		a.api = cgPut(w.API)
		a.buildKind = cgPut(w.BuildKind)
		a.HasInterpolation = w.HasInterpolation
		a.IsSanitized = w.IsSanitized
		a.FromParams = w.FromParams
		a.IsStringArg = w.IsStringArg
		a.LoopDepth = w.LoopDepth
		a.Chain = w.Chain
		a.Line = w.Line
	}
	for i := range fo.arcbs {
		w := &fo.arcbs[i]
		g.ARCBs = append(g.ARCBs, ARCallback{})
		rw := &g.ARCBs[len(g.ARCBs)-1]
		cgZeroRow(unsafe.Pointer(rw), unsafe.Sizeof(*rw))
		cb := &g.ARCBs[len(g.ARCBs)-1]
		cb.ID = int32(len(g.ARCBs) + 1)
		cb.SymID = fix(w.SymID)
		cb.FileID = fid
		cb.host = cgPut(w.Host)
		cb.hook = cgPut(w.Hook)
		cb.method = cgPut(w.Method)
		cb.Conditional = w.Conditional
		cb.Block = w.Block
		cb.Association = w.Association
		cb.IssuesQuery = w.IssuesQuery
		cb.TargetID = w.TargetID
		cb.HasTargetID = w.HasTargetID
		cb.Line = w.Line
	}
	for i := range fo.mps {
		w := &fo.mps[i]
		g.MPs = append(g.MPs, MonkeyPatch{})
		rw := &g.MPs[len(g.MPs)-1]
		cgZeroRow(unsafe.Pointer(rw), unsafe.Sizeof(*rw))
		mp := &g.MPs[len(g.MPs)-1]
		mp.ID = int32(len(g.MPs) + 1)
		mp.SymID = fix(w.SymID)
		mp.HasSym = w.HasSym
		mp.MethodID = w.MethodID
		mp.HasMethodID = w.HasMethodID
		mp.FileID = fid
		mp.coreClass = cgPut(w.CoreClass)
		mp.method = cgPut(w.Method)
		mp.Operator = w.Operator
		mp.Singleton = w.Singleton
		mp.Line = w.Line
	}
	for i := range fo.uis {
		w := &fo.uis[i]
		g.UIs = append(g.UIs, InputSite{})
		rw := &g.UIs[len(g.UIs)-1]
		cgZeroRow(unsafe.Pointer(rw), unsafe.Sizeof(*rw))
		u := &g.UIs[len(g.UIs)-1]
		u.ID = int32(len(g.UIs) + 1)
		u.SymID = fix(w.SymID)
		u.FileID = fid
		u.vr = cgPut(w.Var)
		u.kind = cgPut(w.Kind)
		u.Line = w.Line
		u.InLoop = w.InLoop
	}
	for i := range fo.secs {
		w := &fo.secs[i]
		g.Secs = append(g.Secs, Secret{})
		rw := &g.Secs[len(g.Secs)-1]
		cgZeroRow(unsafe.Pointer(rw), unsafe.Sizeof(*rw))
		sc := &g.Secs[len(g.Secs)-1]
		sc.ID = int32(len(g.Secs) + 1)
		sc.SymID = fix(w.SymID)
		sc.FileID = fid
		sc.value = cgPut(w.Value)
		sc.Line = w.Line
	}
}

var (
	rubyVerFileRe = regexp.MustCompile(`(\d+\.\d+(?:\.\d+)?)`)
	railsLockRe   = regexp.MustCompile(`(?m)^\s+rails \((\d+\.\d+\.\d+)`)
	gemfileRe     = regexp.MustCompile(`ruby\s+["'](\d+\.\d+[.\d]*)`)
)

func (b *builder) manifests() {
	g := b.g
	rubyVer, railsVer := "", ""
	if txt, ok := readSmall(filepath.Join(b.root, ".ruby-version")); ok {
		if m := rubyVerFileRe.FindStringSubmatch(txt); m != nil {
			rubyVer = m[1]
		}
	}
	if txt, ok := readSmall(filepath.Join(b.root, "Gemfile.lock")); ok {
		if m := railsLockRe.FindStringSubmatch(txt); m != nil {
			railsVer = m[1]
		}
	}
	if rubyVer == "" {
		if txt, ok := readSmall(filepath.Join(b.root, "Gemfile")); ok {
			if m := gemfileRe.FindStringSubmatch(txt); m != nil {
				rubyVer = m[1]
			}
		}
	}
	if rubyVer == "" {
		rubyVer = "not declared"
	}
	if railsVer == "" {
		railsVer = "not a Rails app"
	}
	var heredocEvals int32
	for _, m := range g.MSites {
		if m.OnHeredoc != 0 {
			heredocEvals++
		}
	}
	g.setMeta("ruby_version", rubyVer)
	g.setMeta("rails_version", railsVer)
	g.setMeta("frozen_string_default",
		"NO -- literals are 'chilled' (warn on mutate) in files without "+
			"the magic comment; frozen-by-default has not landed in 4.0")
	g.setMeta("ruby_source_in_heredoc_evals", fmt.Sprint(heredocEvals))
}

func readSmall(p string) (string, bool) {
	st, err := os.Stat(p)
	if err != nil || !st.Mode().IsRegular() || st.Size() > 1<<22 {
		return "", false
	}
	b, err := os.ReadFile(p)
	if err != nil {
		return "", false
	}
	return string(b), true
}

func defaultThreads() int { return runtime.GOMAXPROCS(0) * 2 }

const defaultGCPercent = 15

func tightenGC(pct int) func() {
	if pct <= 0 {
		return func() {}
	}
	old := debug.SetGCPercent(pct)
	return func() { debug.SetGCPercent(old) }
}

const minFileSlot = 64 << 10

func defaultBudget() int64 { return 8 << 20 }

type byteWindow struct {
	mu     sync.Mutex
	cond   *sync.Cond
	budget int64
	free   int64
}

func newByteWindow(budget int64) *byteWindow {
	if budget < minFileSlot {
		budget = minFileSlot
	}
	w := &byteWindow{budget: budget, free: budget}
	w.cond = sync.NewCond(&w.mu)
	return w
}

func (w *byteWindow) take(n int64) {
	if n > w.budget {
		n = w.budget
	}
	w.mu.Lock()
	for w.free < n {
		w.cond.Wait()
	}
	w.free -= n
	w.mu.Unlock()
}

func (w *byteWindow) give(n int64) {
	if n > w.budget {
		n = w.budget
	}
	w.mu.Lock()
	w.free += n
	w.cond.Broadcast()
	w.mu.Unlock()
}

var _ = strings.TrimSpace

const schemaVersion = 1

func parserBanner() string {
	return fmt.Sprintf("parser: go-tree-sitter %s (tree-sitter C 0.25) + tree-sitter-ruby>=0.23 0.23.1 (ABI %d, language version %d)",
		goTreeSitterVersion, langAbiVersion(), langVersion())
}

const goTreeSitterVersion = "0.25.0"

func absPath(p string) (string, error) { return filepath.Abs(p) }

type options struct {
	root      string
	which     []int
	module    string
	limit     int
	list      bool
	metrics   bool
	schema    bool
	report    bool
	sql       string
	csv       int
	hasCSV    bool
	jsonOut   int
	hasJSON   bool
	save      string
	saveAST   string
	loadAST   string
	force     bool
	deps      bool
	install   bool
	incGen    bool
	incVend   bool
	noTests   bool
	quiet     bool
	version   bool
	dump      string
	threads   int
	window    int
	budgetMB  int
	gcPercent int
	cpuprof   string
	memprof   string
	profile   bool
}

const usage = `usage: codegraph_ruby [-h] [--module MODULE] [--limit LIMIT] [--list]
                      [--json N] [--save PATH] [--save-ast PATH] [--load-ast PATH]
                      [--force] [--deps]
                      [--include-generated] [--include-vendored] [--no-tests]
                      [--quiet] [--version] [--dump PATH] [--threads N]
                      [--window N] [--budget-mb N] [--gc-percent N]
                      [--cpuprofile PATH]
                      [--memprofile PATH]
                      [--profile]
                      [root] [which ...]

Parse a ruby tree into an in-memory graph and query it in one shot.
Target: Ruby 4.0

positional arguments:
  root       tree to parse (default: .)
  which      1-based question numbers

options:
  -h, --help            show this help message and exit
  --module MODULE       module-name LIKE filter (default: %)
  --limit LIMIT         rows per question; -1 (default) is every row
  --list                list the questions
  --metrics             run/list the METRICS section instead of QUERIES
  --schema              describe what this tool records
  --report              narrative overview
  --csv N               emit question N as CSV
  --json N              emit question N as JSON
  --save PATH           also write the graph to a file
  --save-ast PATH       parse/build, then write the binary AST state to PATH
  --load-ast PATH       load a saved AST state instead of parsing
  --force               allow --save to overwrite an existing file
  --deps                show dependencies and how to install them
  --include-generated   parse generated files too (off by default)
  --include-vendored    parse vendored trees too (off by default)
  --no-tests            skip test files
  --quiet               suppress progress output
  --version             show version and exit
  --dump PATH           write the canonical graph dump (verification hook)
  --threads N           parse N files at once (default: GOMAXPROCS)
  --window N            max files in flight (default: 4 x threads)
  --budget-mb N         max source bytes in flight (default: 8)
  --gc-percent N       collector target during extraction (default: 50)
  --cpuprofile PATH     write a CPU profile
  --memprofile PATH     write a heap profile
  --profile             run every question (plus a second pass) and report
                        wall time and peak heap
`

func parseArgs(argv []string) (*options, error) {
	o := &options{root: ".", module: "%", limit: -1, threads: -1, window: -1, budgetMB: -1, gcPercent: -1}
	var positional []string
	i := 0
	need := func(name string) (string, error) {
		if i+1 >= len(argv) {
			return "", fmt.Errorf("argument %s: expected one argument", name)
		}
		i++
		return argv[i], nil
	}
	for ; i < len(argv); i++ {
		a := argv[i]
		if a == "--" {

			positional = append(positional, argv[i+1:]...)
			break
		}

		if !strings.HasPrefix(a, "-") || a == "-" ||
			(len(a) > 1 && a[0] == '-' && isAllDigits(a[1:])) {
			positional = append(positional, a)
			continue
		}
		eq := func() (string, string, bool) {
			if j := strings.IndexByte(a, '='); j > 0 && strings.HasPrefix(a, "--") {
				return a[:j], a[j+1:], true
			}
			return a, "", false
		}
		name, inline, hasInline := eq()
		takeStr := func() (string, error) {
			if hasInline {
				return inline, nil
			}
			return need(name)
		}
		takeInt := func(dst *int) error {
			v, err := takeStr()
			if err != nil {
				return err
			}
			n, err := strconv.Atoi(v)
			if err != nil {
				return fmt.Errorf("argument %s: invalid int value: %q", name, v)
			}
			*dst = n
			return nil
		}
		switch name {
		case "-h", "--help":
			fmt.Print(usage)
			os.Exit(0)
		case "--module":
			v, err := takeStr()
			if err != nil {
				return nil, err
			}
			o.module = v
		case "--limit":
			if err := takeInt(&o.limit); err != nil {
				return nil, err
			}
		case "--list":
			o.list = true
		case "--metrics":
			o.metrics = true
		case "--schema":
			o.schema = true
		case "--report":
			o.report = true
		case "--csv":
			if err := takeInt(&o.csv); err != nil {
				return nil, err
			}
			o.hasCSV = true
		case "--json":
			if err := takeInt(&o.jsonOut); err != nil {
				return nil, err
			}
			o.hasJSON = true
		case "--save":
			v, err := takeStr()
			if err != nil {
				return nil, err
			}
			o.save = v
		case "--save-ast":
			v, err := takeStr()
			if err != nil {
				return nil, err
			}
			o.saveAST = v
		case "--load-ast":
			v, err := takeStr()
			if err != nil {
				return nil, err
			}
			o.loadAST = v
		case "--force":
			o.force = true
		case "--deps":
			o.deps = true
		case "--install-deps":
			o.install = true
		case "--include-generated":
			o.incGen = true
		case "--include-vendored":
			o.incVend = true
		case "--no-tests":
			o.noTests = true
		case "--quiet":
			o.quiet = true
		case "--version":
			o.version = true
		case "--dump":
			v, err := takeStr()
			if err != nil {
				return nil, err
			}
			o.dump = v
		case "--threads":
			if err := takeInt(&o.threads); err != nil {
				return nil, err
			}
		case "--window":
			if err := takeInt(&o.window); err != nil {
				return nil, err
			}
		case "--budget-mb":
			if err := takeInt(&o.budgetMB); err != nil {
				return nil, err
			}
		case "--gc-percent":
			if err := takeInt(&o.gcPercent); err != nil {
				return nil, err
			}
		case "--cpuprofile":
			v, err := takeStr()
			if err != nil {
				return nil, err
			}
			o.cpuprof = v
		case "--memprofile":
			v, err := takeStr()
			if err != nil {
				return nil, err
			}
			o.memprof = v
		case "--profile":
			o.profile = true
		default:
			return nil, fmt.Errorf("unrecognized arguments: %s", a)
		}
	}
	if len(positional) > 0 {
		o.root = positional[0]
		positional = positional[1:]
	}
	for _, p := range positional {
		n, err := strconv.Atoi(p)
		if err != nil {
			return nil, fmt.Errorf("argument which: invalid int value: %q", p)
		}
		o.which = append(o.which, n)
	}
	return o, nil
}

func cgPutU32(b []byte, o int, v uint32) { *(*uint32)(unsafe.Pointer(&b[o])) = v }
func cgPutU64(b []byte, o int, v uint64) { *(*uint64)(unsafe.Pointer(&b[o])) = v }

func cgGetU32(b []byte, o int) uint32 { return *(*uint32)(unsafe.Pointer(&b[o])) }
func cgGetU64(b []byte, o int) uint64 { return *(*uint64)(unsafe.Pointer(&b[o])) }

func main() {
	o, err := parseArgs(os.Args[1:])
	if err != nil {
		fmt.Fprintf(os.Stderr, "%s\n%s", err, usage)
		os.Exit(2)
	}
	os.Exit(run(o))
}

func run(o *options) int {
	if o.version {

		fmt.Printf("codegraph_ruby.py  target=Ruby 4.0  schema=v%d  go=%s  cpus=%d\n",
			schemaVersion, runtime.Version(), runtime.NumCPU())
		return 0
	}
	if o.install {

		if !o.quiet {
			fmt.Println("all dependencies already present")
		}
		if o.deps {
			fmt.Println()
			printDeps()
			return 0
		}
	} else if o.deps {
		printDeps()
		return 0
	}
	if o.schema {
		printSchema()
		return 0
	}
	if o.list {
		for i, q := range catalogue(o.metrics) {
			fmt.Printf("%2d. %-26s %s\n", i+1, q.name, q.title)
		}
		return 0
	}
	if o.hasCSV || o.hasJSON {
		o.quiet = true
	}
	if o.saveAST != "" && o.loadAST != "" {
		fmt.Fprintln(os.Stderr, "--save-ast and --load-ast cannot be used together")
		return 2
	}
	if o.loadAST == "" {
		st, serr := os.Stat(o.root)
		if serr != nil || !st.IsDir() {
			fmt.Fprintf(os.Stderr, "not a directory: %s\n", o.root)
			return 2
		}
	}
	var err error

	threads := o.threads
	if threads <= 0 {
		threads = defaultThreads()
	}
	window := o.window
	if window <= 0 {
		window = threads
	}
	budget := defaultBudget()
	if o.budgetMB > 0 {
		budget = int64(o.budgetMB) << 20
	}
	gcpct := defaultGCPercent
	if o.gcPercent >= 0 {
		gcpct = o.gcPercent
	}

	if o.cpuprof != "" {
		f, err := os.Create(o.cpuprof)
		if err != nil {
			fmt.Fprintln(os.Stderr, err)
			return 2
		}
		pprof.StartCPUProfile(f)
		defer func() { pprof.StopCPUProfile(); f.Close() }()
	}

	t0 := time.Now()
	var g *Graph
	var nParsed int
	if o.loadAST != "" {
		g, err = loadAST(o.loadAST)
		if err != nil {
			fmt.Fprintf(os.Stderr, "load-ast: %v\n", err)
			return 2
		}
	} else {
		g, nParsed, err = build(o.root, buildOpts{
			includeTests:     !o.noTests,
			includeGenerated: o.incGen,
			includeVendored:  o.incVend,
			quiet:            o.quiet,
			threads:          threads,
			window:           window,
			budget:           budget,
			gcPercent:        gcpct,
			keepTrees:        o.saveAST != "",
		})
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

		restoreDumpGC := tightenGC(gcpct)
		err := g.dumpTo(o.dump)
		restoreDumpGC()
		if err != nil {
			fmt.Fprintln(os.Stderr, err)
			return 2
		}
	}
	if o.memprof != "" {
		f, err := os.Create(o.memprof)
		if err != nil {
			fmt.Fprintln(os.Stderr, err)
			return 2
		}
		runtime.GC()
		pprof.WriteHeapProfile(f)
		f.Close()
	}
	if o.profile {
		runProfile(g, o, took)
		return 0
	}

	if o.hasCSV || o.hasJSON {
		idx := o.csv
		if o.hasJSON {
			idx = o.jsonOut
		}
		qs := catalogue(o.metrics)
		if idx < 1 || idx > len(qs) {
			fmt.Fprintf(os.Stderr, "no query %d\n", idx)
			return 2
		}
		q := qs[idx-1]
		res := q.run(g, sqlLike(o.module), o.limit)
		if o.hasCSV {
			w := csv.NewWriter(os.Stdout)

			w.UseCRLF = true
			w.Write(res.cols)
			for _, r := range res.rows {
				w.Write(r.csvStrings())
			}
			w.Flush()
		} else {
			writeJSON(os.Stdout, res)
		}
		return 0
	}

	if !o.quiet {
		if o.loadAST != "" {
			fmt.Printf("codegraph-ruby: %d files loaded from AST in %.1fs module=%s limit=%s\n",
				len(g.Files), took.Seconds(), o.module,
				map[bool]string{true: "all", false: strconv.Itoa(o.limit)}[o.limit < 0])
		} else {
			fmt.Printf("codegraph-ruby: %d files parsed into memory in %.1fs module=%s limit=%s\n",
				nParsed, took.Seconds(), o.module,
				map[bool]string{true: "all", false: strconv.Itoa(o.limit)}[o.limit < 0])
		}
	}
	if o.report {
		g.report()
	}

	qs := catalogue(o.metrics)
	sel := o.which
	if len(sel) == 0 {
		for i := range qs {
			sel = append(sel, i+1)
		}
	}
	out := bufio.NewWriterSize(os.Stdout, 1<<16)
	defer out.Flush()
	for _, k := range sel {
		if k < 1 || k > len(qs) {
			continue
		}
		q := qs[k-1]
		fmt.Fprintf(out, "\n%s\n", strings.Repeat("=", 78))
		fmt.Fprintf(out, "Q%d. %s -- %s\n", k, q.name, q.title)
		fmt.Fprintf(out, "%s\n", strings.Repeat("-", 78))
		for _, line := range splitNotes(q.notes) {
			fmt.Fprintf(out, " %s\n", line)
		}
		fmt.Fprintln(out)
		res := q.run(g, sqlLike(o.module), o.limit)
		render(out, res)
	}

	if o.save != "" {

		if _, err := os.Lstat(o.save); err == nil && !o.force {

			msg := "\nrefusing to overwrite " + o.save + " (pass --force)"
			if li, lerr := os.Lstat(o.save); lerr == nil && li.Mode()&os.ModeSymlink != 0 {
				real, _ := filepath.EvalSymlinks(o.save)
				msg += " -- it is a symlink to " + real
			}
			fmt.Fprintln(os.Stderr, msg)
			out.Flush()
		} else {
			if li, lerr := os.Lstat(o.save); lerr == nil && li.Mode()&os.ModeSymlink != 0 {
				os.Remove(o.save)
			}
			if err := g.dumpTo(o.save); err != nil {
				fmt.Fprintln(os.Stderr, "\ncould not write "+o.save+": "+err.Error())
			} else {
				fmt.Fprintf(out, "\n(graph also written to %s)\n", o.save)
			}
		}
	}
	return 0
}

func likeFold(pat, s string) bool {
	lead := strings.HasPrefix(pat, "%")
	if lead {
		pat = pat[1:]
	}
	trail := strings.HasSuffix(pat, "%")
	if trail {
		pat = pat[:len(pat)-1]
	}
	switch {
	case lead && trail:
		if len(pat) > len(s) {
			return false
		}
		for i := 0; i+len(pat) <= len(s); i++ {
			if foldSeq(pat, s[i:i+len(pat)]) {
				return true
			}
		}
		return false
	case lead:
		return len(pat) <= len(s) && foldSeq(pat, s[len(s)-len(pat):])
	case trail:
		return len(pat) <= len(s) && foldSeq(pat, s[:len(pat)])
	default:
		return len(pat) == len(s) && foldSeq(pat, s)
	}
}

func foldSeq(pat, s string) bool {
	for i := 0; i < len(pat); i++ {
		c := pat[i]
		if c == '_' {
			continue
		}
		a, b := c, s[i]
		if a >= 'A' && a <= 'Z' {
			a += 32
		}
		if b >= 'A' && b <= 'Z' {
			b += 32
		}
		if a != b {
			return false
		}
	}
	return true
}

func sqlLike(pattern string) func(string) bool {
	if pattern == "" || pattern == "%" {
		return func(string) bool { return true }
	}
	lead := strings.HasPrefix(pattern, "%")
	tail := strings.HasSuffix(pattern, "%") && len(pattern) > 1
	core := strings.Trim(pattern, "%")
	core = strings.ToLower(core)
	hasWild := strings.ContainsAny(core, "_%")
	if !hasWild && lead && tail {
		return func(s string) bool { return strings.Contains(strings.ToLower(s), core) }
	}
	return func(s string) bool { return likeFold(pattern, s) }
}

func splitNotes(s string) []string {
	s = strings.TrimSuffix(s, "\n")
	return strings.Split(s, "\n")
}

func isAllDigits(s string) bool {
	for i := 0; i < len(s); i++ {
		if s[i] < '0' || s[i] > '9' {
			return false
		}
	}
	return len(s) > 0
}

func printDeps() {
	fmt.Println("dependencies for codegraph-ruby:")
	dep("ok     ", "tree-sitter CLI", goTreeSitterVersion, "required",
		"on PATH (or $TREE_SITTER_BIN); one child process parses one file "+
			"via `tree-sitter parse /dev/stdin --scope source.ruby --cst`. "+
			"Nothing is linked in and there is no C in this build, so a missing "+
			"CLI aborts at startup rather than yielding an empty graph, which "+
			"reads exactly like a clean repository",
		"verified against "+goTreeSitterVersion+" (external CLI, spawned per file)")
	dep("ok     ", "tree-sitter-ruby grammar", rubyGrammarVersion, "required",
		"tree-sitter grammar for Ruby, registered with that CLI. Required: "+
			"without it this analyzer refuses to run rather than produce an "+
			"empty graph",
		"verified against "+rubyGrammarVersion+" (ABI 14 -- older than most "+
			"grammars here; the 0.25 runtime accepts 13-15 so it loads, but it "+
			"predates Ruby 4.0 leading-operator continuation lines)")
}

func dep(mark, pip, ver, tag, why, verified string) {
	fmt.Printf("  [%-7s] %-28s %-10s %s\n", mark, pip, ver, tag)
	fmt.Printf("             %s\n", why)
	fmt.Printf("             %s\n", verified)
}

const rubyGrammarVersion = "0.23.1"

func runProfile(g *Graph, o *options, build time.Duration) {
	qs := catalogue(o.metrics)
	out := bufio.NewWriter(os.Stdout)
	defer out.Flush()
	fmt.Fprintf(out, "build      %v  (%d symbols, %d edges, %d files)\n",
		build, len(g.Syms), len(g.Edges), len(g.Files))
	var m0, m1 runtime.MemStats
	runtime.ReadMemStats(&m0)
	for pass := range 2 {
		for i, q := range qs {
			t := time.Now()
			q.run(g, func(string) bool { return true }, -1)
			if pass == 1 {
				fmt.Fprintf(out, "%3d %-32s %v\n", i+1, q.name, time.Since(t))
			}
		}
	}
	runtime.ReadMemStats(&m1)
	fmt.Fprintf(out, "\nheap in use  %d MB after the second pass\n", m1.HeapInuse>>20)
	fmt.Fprintf(out, "total alloc  %d MB\n", m1.TotalAlloc>>20)
}

const cgasMagic = "CGAS"

const (
	cgasVersion  = 2
	cgasHeaderSz = 32
	cgasSecSz    = 24
	cgasNSec     = 33
)

const (
	cgasSecStrings uint32 = 1 + iota
	cgasSecTrees
	cgasSecTreeDir
	cgasSecFiles
	cgasSecMods
	cgasSecSyms
	cgasSecCold
	cgasSecSigRefs
	cgasSecCWKeys
	cgasSecCWVals
	cgasSecHalv
	cgasSecSigIdx
	cgasSecParams
	cgasSecFields
	cgasSecLocals
	cgasSecEdges
	cgasSecSites
	cgasSecUnres
	cgasSecImps
	cgasSecHaz
	cgasSecLits
	cgasSecMark
	cgasSecEnums
	cgasSecRMods
	cgasSecMixins
	cgasSecMSites
	cgasSecBlks
	cgasSecARQs
	cgasSecARCBs
	cgasSecMPs
	cgasSecUIs
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

type cgasSRef struct{ Off, Ln uint64 }

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
	fail(unsafe.Sizeof(cgStr{}) == 16, "cgStr must be the 16-byte {offset,length} pair")
	fail(unsafe.Sizeof(cgMetaRow{}) == 32, "cgMetaRow must be the 32-byte fixed stride")
	fail(unsafe.Offsetof(cgMetaRow{}.V) == 16, "cgMetaRow value must sit at byte 16")
	for _, t := range []reflect.Type{
		reflect.TypeOf(tsRec{}),
		reflect.TypeOf(symCold{}),
		reflect.TypeOf(symColdWide{}),
		reflect.TypeOf(sigRef{}),
		reflect.TypeOf(Edge{}),
		reflect.TypeOf(CallSite{}),
		reflect.TypeOf(cgasSRef{}),
		reflect.TypeOf(cgStr{}),
		reflect.TypeOf(cgMetaRow{}),
		reflect.TypeOf(File{}),
		reflect.TypeOf(Module{}),
		reflect.TypeOf(Sym{}),
		reflect.TypeOf(Param{}),
		reflect.TypeOf(Field{}),
		reflect.TypeOf(Local{}),
		reflect.TypeOf(Unresolved{}),
		reflect.TypeOf(Import{}),
		reflect.TypeOf(Hazard{}),
		reflect.TypeOf(Literal{}),
		reflect.TypeOf(Marker{}),
		reflect.TypeOf(EnumMember{}),
		reflect.TypeOf(RubyModule{}),
		reflect.TypeOf(Mixin{}),
		reflect.TypeOf(MetaSite{}),
		reflect.TypeOf(Block{}),
		reflect.TypeOf(ARQuery{}),
		reflect.TypeOf(ARCallback{}),
		reflect.TypeOf(MonkeyPatch{}),
		reflect.TypeOf(InputSite{}),
		reflect.TypeOf(Secret{}),
		reflect.TypeOf(int32(0)),
		reflect.TypeOf(int64(0)),
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

func cgasStrFields[T any]() []uintptr {
	var p *T
	switch any(p).(type) {
	case *File:
		return []uintptr{unsafe.Offsetof(File{}.path), unsafe.Offsetof(File{}.dir),
			unsafe.Offsetof(File{}.base), unsafe.Offsetof(File{}.ext),
			unsafe.Offsetof(File{}.lang), unsafe.Offsetof(File{}.sha1)}
	case *Module:
		return []uintptr{unsafe.Offsetof(Module{}.name), unsafe.Offsetof(Module{}.kind)}
	case *Sym:
		return []uintptr{unsafe.Offsetof(Sym{}.name), unsafe.Offsetof(Sym{}.qualName),
			unsafe.Offsetof(Sym{}.kind), unsafe.Offsetof(Sym{}.visibility)}
	case *Param:
		return []uintptr{unsafe.Offsetof(Param{}.name), unsafe.Offsetof(Param{}.typ),
			unsafe.Offsetof(Param{}.def)}
	case *Field:
		return []uintptr{unsafe.Offsetof(Field{}.name), unsafe.Offsetof(Field{}.typ),
			unsafe.Offsetof(Field{}.vis)}
	case *Local:
		return []uintptr{unsafe.Offsetof(Local{}.name), unsafe.Offsetof(Local{}.typ)}
	case *Unresolved:
		return []uintptr{unsafe.Offsetof(Unresolved{}.name)}
	case *Import:
		return []uintptr{unsafe.Offsetof(Import{}.target), unsafe.Offsetof(Import{}.alias),
			unsafe.Offsetof(Import{}.kind)}
	case *Hazard:
		return []uintptr{unsafe.Offsetof(Hazard{}.pattern), unsafe.Offsetof(Hazard{}.category)}
	case *Literal:
		return []uintptr{unsafe.Offsetof(Literal{}.kind), unsafe.Offsetof(Literal{}.value)}
	case *Marker:
		return []uintptr{unsafe.Offsetof(Marker{}.kind), unsafe.Offsetof(Marker{}.text)}
	case *EnumMember:
		return []uintptr{unsafe.Offsetof(EnumMember{}.name), unsafe.Offsetof(EnumMember{}.value)}
	case *RubyModule:
		return []uintptr{unsafe.Offsetof(RubyModule{}.name), unsafe.Offsetof(RubyModule{}.superclass)}
	case *Mixin:
		return []uintptr{unsafe.Offsetof(Mixin{}.host), unsafe.Offsetof(Mixin{}.mixin),
			unsafe.Offsetof(Mixin{}.mixinShort), unsafe.Offsetof(Mixin{}.kind)}
	case *MetaSite:
		return []uintptr{unsafe.Offsetof(MetaSite{}.api), unsafe.Offsetof(MetaSite{}.arg)}
	case *Block:
		return []uintptr{unsafe.Offsetof(Block{}.method), unsafe.Offsetof(Block{}.receiver),
			unsafe.Offsetof(Block{}.style)}
	case *ARQuery:
		return []uintptr{unsafe.Offsetof(ARQuery{}.model), unsafe.Offsetof(ARQuery{}.api),
			unsafe.Offsetof(ARQuery{}.buildKind)}
	case *ARCallback:
		return []uintptr{unsafe.Offsetof(ARCallback{}.host), unsafe.Offsetof(ARCallback{}.hook),
			unsafe.Offsetof(ARCallback{}.method)}
	case *MonkeyPatch:
		return []uintptr{unsafe.Offsetof(MonkeyPatch{}.coreClass), unsafe.Offsetof(MonkeyPatch{}.method)}
	case *InputSite:
		return []uintptr{unsafe.Offsetof(InputSite{}.vr), unsafe.Offsetof(InputSite{}.kind)}
	case *Secret:
		return []uintptr{unsafe.Offsetof(Secret{}.value)}
	case *cgMetaRow:
		return []uintptr{unsafe.Offsetof(cgMetaRow{}.K), unsafe.Offsetof(cgMetaRow{}.V)}
	}
	return nil
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

func cgasCheckStrRefs[T any](rows []T, arenaLen uint64, what string) error {
	if len(rows) == 0 {
		return nil
	}
	n := int(unsafe.Sizeof(rows[0]))
	base := unsafe.Pointer(&rows[0])
	for _, f := range cgasStrFields[T]() {
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
	arena := cgArena

	cwKeys := make([]int32, 0, len(g.coldWide))
	for id := range g.coldWide {
		cwKeys = append(cwKeys, id)
	}
	slices.Sort(cwKeys)
	cwVals := make([]symColdWide, len(cwKeys))
	for i, id := range cwKeys {
		cwVals[i] = g.coldWide[id]
	}

	sigIdx := make([]cgasSRef, len(g.sigBases))
	for i := range g.sigBases {
		n := uint64(sigBlockLen)
		if i == len(g.sigBases)-1 {
			n = uint64(g.sigOff)
		}
		sigIdx[i] = cgasSRef{g.sigBases[i], n}
	}

	metaRows := make([]cgMetaRow, 0, len(g.Meta))
	for i := range g.Meta {
		if g.Meta[i].K.Off < cgExtBase && g.Meta[i].K.Str() != "built_at" {
			metaRows = append(metaRows, g.Meta[i])
		}
	}

	body := make([][]byte, cgasNSec)
	body[cgasSecFiles-1] = cgasBytes(g.fileRows)
	body[cgasSecMods-1] = cgasBytes(g.modRows)
	body[cgasSecSyms-1] = cgasBytes(g.symRows)
	body[cgasSecCold-1] = cgasBytes(g.cold)
	body[cgasSecSigRefs-1] = cgasBytes(g.sigRefs)
	body[cgasSecCWKeys-1] = cgasBytes(cwKeys)
	body[cgasSecCWVals-1] = cgasBytes(cwVals)
	body[cgasSecHalv-1] = cgasBytes(g.halv)
	body[cgasSecSigIdx-1] = cgasBytes(sigIdx)
	body[cgasSecParams-1] = cgasBytes(g.Params)
	body[cgasSecFields-1] = cgasBytes(g.Fields)
	body[cgasSecLocals-1] = cgasBytes(g.Locals)
	body[cgasSecEdges-1] = cgasBytes(g.Edges)
	body[cgasSecSites-1] = cgasBytes(g.Sites)
	body[cgasSecUnres-1] = cgasBytes(g.Unres)
	body[cgasSecImps-1] = cgasBytes(g.Imps)
	body[cgasSecHaz-1] = cgasBytes(g.Haz)
	body[cgasSecLits-1] = cgasBytes(g.Lits)
	body[cgasSecMark-1] = cgasBytes(g.Mark)
	body[cgasSecEnums-1] = cgasBytes(g.Enums)
	body[cgasSecRMods-1] = cgasBytes(g.RMods)
	body[cgasSecMixins-1] = cgasBytes(g.Mixins)
	body[cgasSecMSites-1] = cgasBytes(g.MSites)
	body[cgasSecBlks-1] = cgasBytes(g.Blks)
	body[cgasSecARQs-1] = cgasBytes(g.ARQs)
	body[cgasSecARCBs-1] = cgasBytes(g.ARCBs)
	body[cgasSecMPs-1] = cgasBytes(g.MPs)
	body[cgasSecUIs-1] = cgasBytes(g.UIs)
	body[cgasSecSecs-1] = cgasBytes(g.Secs)
	body[cgasSecMeta-1] = cgasBytes(metaRows)
	body[cgasSecStrings-1] = arena

	stride := uint64(unsafe.Sizeof(tsRec{}))
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
					len(tr.recs)*int(unsafe.Sizeof(tsRec{})))
				if _, err := w.Write(raw); err != nil {
					return fail(err)
				}
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
	arena := mem[ao : ao+al : ao+al]
	dec := func(id uint32) (uint64, uint64) {
		return secs[id].Off, secs[id].Len
	}
	decErr := func(err error) (*Graph, error) {
		return nil, bad("%v", err)
	}

	off, ln := dec(cgasSecFiles)
	files, err := cgasDecodeRows[File](mem, off, ln, "files")
	if err != nil {
		return decErr(err)
	}
	if err := cgasCheckStrRefs(files, al, "files"); err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecMods)
	mods, err := cgasDecodeRows[Module](mem, off, ln, "modules")
	if err != nil {
		return decErr(err)
	}
	if err := cgasCheckStrRefs(mods, al, "modules"); err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecSyms)
	symRows, err := cgasDecodeRows[Sym](mem, off, ln, "symbols")
	if err != nil {
		return decErr(err)
	}
	if err := cgasCheckStrRefs(symRows, al, "symbols"); err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecCold)
	cold, err := cgasDecodeRows[symCold](mem, off, ln, "cold columns")
	if err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecSigRefs)
	sigRefs, err := cgasDecodeRows[sigRef](mem, off, ln, "signature refs")
	if err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecCWKeys)
	cwKeys, err := cgasDecodeRows[int32](mem, off, ln, "wide cold keys")
	if err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecCWVals)
	cwVals, err := cgasDecodeRows[symColdWide](mem, off, ln, "wide cold values")
	if err != nil {
		return decErr(err)
	}
	if len(cwKeys) != len(cwVals) {
		return nil, bad("wide cold key/value counts differ (%d vs %d)", len(cwKeys), len(cwVals))
	}
	off, ln = dec(cgasSecHalv)
	halv, err := cgasDecodeRows[int64](mem, off, ln, "halstead column")
	if err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecSigIdx)
	sigIdx, err := cgasDecodeRows[cgasSRef](mem, off, ln, "signature text index")
	if err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecParams)
	params, err := cgasDecodeRows[Param](mem, off, ln, "params")
	if err != nil {
		return decErr(err)
	}
	if err := cgasCheckStrRefs(params, al, "params"); err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecFields)
	fields, err := cgasDecodeRows[Field](mem, off, ln, "fields")
	if err != nil {
		return decErr(err)
	}
	if err := cgasCheckStrRefs(fields, al, "fields"); err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecLocals)
	locals, err := cgasDecodeRows[Local](mem, off, ln, "locals")
	if err != nil {
		return decErr(err)
	}
	if err := cgasCheckStrRefs(locals, al, "locals"); err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecEdges)
	edges, err := cgasDecodeRows[Edge](mem, off, ln, "edges")
	if err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecSites)
	sites, err := cgasDecodeRows[CallSite](mem, off, ln, "call sites")
	if err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecUnres)
	unres, err := cgasDecodeRows[Unresolved](mem, off, ln, "unresolved calls")
	if err != nil {
		return decErr(err)
	}
	if err := cgasCheckStrRefs(unres, al, "unresolved calls"); err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecImps)
	imps, err := cgasDecodeRows[Import](mem, off, ln, "imports")
	if err != nil {
		return decErr(err)
	}
	if err := cgasCheckStrRefs(imps, al, "imports"); err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecHaz)
	haz, err := cgasDecodeRows[Hazard](mem, off, ln, "hazards")
	if err != nil {
		return decErr(err)
	}
	if err := cgasCheckStrRefs(haz, al, "hazards"); err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecLits)
	lits, err := cgasDecodeRows[Literal](mem, off, ln, "literals")
	if err != nil {
		return decErr(err)
	}
	if err := cgasCheckStrRefs(lits, al, "literals"); err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecMark)
	mark, err := cgasDecodeRows[Marker](mem, off, ln, "markers")
	if err != nil {
		return decErr(err)
	}
	if err := cgasCheckStrRefs(mark, al, "markers"); err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecEnums)
	enums, err := cgasDecodeRows[EnumMember](mem, off, ln, "enum members")
	if err != nil {
		return decErr(err)
	}
	if err := cgasCheckStrRefs(enums, al, "enum members"); err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecRMods)
	rmods, err := cgasDecodeRows[RubyModule](mem, off, ln, "ruby modules")
	if err != nil {
		return decErr(err)
	}
	if err := cgasCheckStrRefs(rmods, al, "ruby modules"); err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecMixins)
	mixins, err := cgasDecodeRows[Mixin](mem, off, ln, "mixins")
	if err != nil {
		return decErr(err)
	}
	if err := cgasCheckStrRefs(mixins, al, "mixins"); err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecMSites)
	msites, err := cgasDecodeRows[MetaSite](mem, off, ln, "meta-programming sites")
	if err != nil {
		return decErr(err)
	}
	if err := cgasCheckStrRefs(msites, al, "meta-programming sites"); err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecBlks)
	blks, err := cgasDecodeRows[Block](mem, off, ln, "blocks")
	if err != nil {
		return decErr(err)
	}
	if err := cgasCheckStrRefs(blks, al, "blocks"); err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecARQs)
	arqs, err := cgasDecodeRows[ARQuery](mem, off, ln, "AR queries")
	if err != nil {
		return decErr(err)
	}
	if err := cgasCheckStrRefs(arqs, al, "AR queries"); err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecARCBs)
	arcbs, err := cgasDecodeRows[ARCallback](mem, off, ln, "AR callbacks")
	if err != nil {
		return decErr(err)
	}
	if err := cgasCheckStrRefs(arcbs, al, "AR callbacks"); err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecMPs)
	mps, err := cgasDecodeRows[MonkeyPatch](mem, off, ln, "monkey patches")
	if err != nil {
		return decErr(err)
	}
	if err := cgasCheckStrRefs(mps, al, "monkey patches"); err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecUIs)
	uis, err := cgasDecodeRows[InputSite](mem, off, ln, "input sites")
	if err != nil {
		return decErr(err)
	}
	if err := cgasCheckStrRefs(uis, al, "input sites"); err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecSecs)
	secRows, err := cgasDecodeRows[Secret](mem, off, ln, "secrets")
	if err != nil {
		return decErr(err)
	}
	if err := cgasCheckStrRefs(secRows, al, "secrets"); err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecMeta)
	metaSrc, err := cgasDecodeRows[cgMetaRow](mem, off, ln, "meta")
	if err != nil {
		return decErr(err)
	}
	if err := cgasCheckStrRefs(metaSrc, al, "meta"); err != nil {
		return decErr(err)
	}

	cgMu.Lock()
	cgArena = arena
	cgArenaBase.Store(unsafe.SliceData(cgArena))
	cgMu.Unlock()

	meta := make([]cgMetaRow, 0, len(metaSrc)+1)
	meta = append(meta, metaSrc...)
	meta = append(meta, cgMetaRow{K: cgPutExt("built_at"),
		V: cgPutExt(time.Now().Format("2006-01-02T15:04:05"))})
	sort.Slice(meta, func(i, j int) bool { return meta[i].K.Str() < meta[j].K.Str() })

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
	g := newGraph()
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

	g.fileRows = files
	g.Files = make([]*File, len(files))
	for i := range files {
		g.Files[i] = &files[i]
	}
	g.modRows = mods
	g.Mods = make([]*Module, len(mods))
	for i := range mods {
		g.Mods[i] = &mods[i]
	}
	g.symRows = symRows
	g.Syms = make([]*Sym, len(symRows))
	for i := range symRows {
		g.Syms[i] = &symRows[i]
	}
	if len(cold) != len(symRows) {
		return nil, bad("cold column count %d, want %d", len(cold), len(symRows))
	}
	if len(sigRefs) != len(symRows) {
		return nil, bad("signature ref count %d, want %d", len(sigRefs), len(symRows))
	}
	g.cold = cold
	g.sigRefs = sigRefs
	g.coldWide = make(map[int32]symColdWide, len(cwKeys))
	for i := range cwKeys {
		g.coldWide[cwKeys[i]] = cwVals[i]
	}
	g.halv = halv
	g.sigBases = make([]uint64, len(sigIdx))
	for i := range sigIdx {
		if sigIdx[i].Off > al || sigIdx[i].Ln > al-sigIdx[i].Off {
			return nil, bad("signature block %d escapes the string arena", i)
		}
		g.sigBases[i] = sigIdx[i].Off
	}
	if len(sigIdx) > 0 {
		g.sigBlk = len(sigIdx) - 1
		g.sigOff = int(sigIdx[len(sigIdx)-1].Ln)
	}
	g.Params = params
	g.Fields = fields
	g.Locals = locals
	g.Edges = edges
	g.Sites = sites
	g.Unres = unres
	g.Imps = imps
	g.Haz = haz
	g.Lits = lits
	g.Mark = mark
	g.Enums = enums
	g.RMods = rmods
	g.Mixins = mixins
	g.MSites = msites
	g.Blks = blks
	g.ARQs = arqs
	g.ARCBs = arcbs
	g.MPs = mps
	g.UIs = uis
	g.Secs = secRows
	g.Meta = meta
	g.astBlob = mem
	g.index()
	return g, nil
}
