package main

import (
	"bufio"
	"bytes"
	"crypto/sha1"
	"encoding/hex"
	"flag"
	"fmt"
	"go/ast"
	"go/parser"
	"go/scanner"
	"go/token"
	"io"
	"io/fs"
	"math"
	"math/big"
	"os"
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

const minFileSlot = 64 << 10

var parseByteBudget = int64(2 << 20)

func fileCharge(n int64) int64 {
	if n < minFileSlot {
		return minFileSlot
	}
	return n
}

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

var defaultParseWorkers = runtime.GOMAXPROCS(0)

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

func cellText(c cellVal) string {
	switch {
	case c.null:
		return ""
	case c.isS:
		return c.s
	case c.isF:
		return floatText(c.f)
	default:
		return strconv.FormatInt(c.i, 10)
	}
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

func capRows(r result) result {
	if r.lim >= 0 && len(r.rows) > r.lim {
		r.rows = r.rows[:r.lim]
	}
	return r
}

func writeCSV(w *bufio.Writer, r result) {
	r = capRows(r)
	writeCSVRow(w, r.cols)
	buf := make([]string, len(r.cols))
	for _, row := range r.rows {
		for i := range row {
			buf[i] = cellText(row[i])
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

func writeJSONValue(w *bufio.Writer, c cellVal) {
	switch {
	case c.null:
		w.WriteString("null")
	case c.isS:
		writeJSONString(w, c.s)
	case c.isF:
		w.WriteString(floatText(c.f))
	default:
		w.WriteString(strconv.FormatInt(c.i, 10))
	}
}

func writeJSON(w *bufio.Writer, r result) {
	r = capRows(r)
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
			w.WriteString("    ")
			writeJSONString(w, r.cols[ci])
			w.WriteString(": ")
			if v := src[j]; v < len(row) {
				writeJSONValue(w, row[v])
			} else {
				w.WriteString("null")
			}
		}
		w.WriteString("\n  }")
	}
	w.WriteString("\n]\n")
}

func runProbe(paths []string) int {
	w := bufio.NewWriter(os.Stdout)
	defer w.Flush()
	for _, p := range paths {
		src, err := os.ReadFile(p)
		if err != nil {
			fmt.Fprintln(w, "read:", err)
			continue
		}
		fset := token.NewFileSet()
		f, err := parser.ParseFile(fset, p, src, parser.ParseComments|parser.AllErrors)
		if err != nil && f == nil {
			fmt.Fprintln(w, "parse:", err)
			continue
		}
		tf := fset.File(f.Pos())
		off := func(pos token.Pos) int32 { return int32(tf.Offset(pos)) }
		_ = off
		t := buildTree(tf, src, f)
		printTree(w, t, t.root, 0, fNone)
	}
	return 0
}

func printTree(w *bufio.Writer, t *Tree, n int32, d int, f Slot) {
	nd := t.nodes[n]
	short := t.text(n)
	if len(short) > 30 {
		short = short[:30]
	}
	var esc strings.Builder
	for i := 0; i < len(short); i++ {
		if short[i] == '\n' {
			esc.WriteString("\\n")
		} else if short[i] == '\t' {
			esc.WriteString(" ")
		} else {
			esc.WriteString(string(short[i]))
		}
	}
	tag := ""
	if f != fNone {
		tag = fieldTag(f) + "="
	}

	name := nodeNames[nd.kind]
	if pureToken[nd.kind] || !nodeNamed[nd.kind] {
		name = "*"
	}
	if nd.kind == kOperator {

		inner := nd.first
		if inner != noNode && t.nodes[inner].next == noNode {
			short = t.text(inner)
		}
		name = "*"
	}
	lo, hi := nd.start, nd.end
	if nd.kind == kOperator && nd.first != noNode && t.nodes[nd.first].next == noNode {
		lo, hi = t.nodes[nd.first].start, t.nodes[nd.first].end
	}
	fmt.Fprintf(w, "%*s%s%s %d-%d |%s|\n", d*2, "", tag, name, lo, hi, esc.String())
	if nd.kind == kOperator {
		return
	}
	for c := nd.first; c != noNode; c = t.nodes[c].next {
		printTree(w, t, c, d+1, t.nodes[c].field)
	}
}

var fieldTagNames = map[Slot]string{
	fBody: "body", fParameters: "parameters", fResult: "result",
	fAlternative: "alternative", fFunction: "function", fArguments: "arguments",
	fType: "type", fName: "name", fReceiver: "receiver", fPath: "path",
	fLeft: "left", fRight: "right", fValue: "value", fOperand: "operand",
	fSelectorField: "field", fOperator: "operator", fConsequence: "consequence", fCondition: "condition",
	fInitializer: "initializer", fTypeParameters: "type_parameters",
	fElement: "element", fKey: "key", fIndex: "index", fInit: "init",
	fPost: "post", fChannel: "channel", fLabel: "label", fTag: "tag",
	fPackage: "package", fAlias: "alias", fTypeArgs: "type_arguments",
}

func fieldTag(f Slot) string { return fieldTagNames[f] }

func runWalk(paths []string) int {
	w := bufio.NewWriterSize(os.Stdout, 1<<20)
	defer w.Flush()
	for _, p := range paths {
		src, err := os.ReadFile(p)
		if err != nil {
			continue
		}
		fset := token.NewFileSet()
		f, err := parser.ParseFile(fset, p, src, parser.ParseComments|parser.AllErrors)
		if err != nil && f == nil {
			fmt.Fprintln(w, "PARSEFAIL", p)
			continue
		}
		tf := fset.File(f.Pos())
		t := buildTree(tf, src, f)
		fmt.Fprintf(w, "### %s\n", filepath.Base(p))
		walkOut(w, t, t.root, 0)
	}
	return 0
}

func walkOut(w *bufio.Writer, t *Tree, n int32, d int) {
	nd := t.nodes[n]
	if nd.kind == kOperator {

		if nd.first == noNode {
			fmt.Fprintf(os.Stderr, "empty operator at %d\n", nd.start)
			return
		}
		walkOut(w, t, nd.first, d)
		return
	}
	nc := int32(0)
	for c := nd.first; c != noNode; c = t.nodes[c].next {
		nc++
	}
	if nc == 0 {
		fmt.Fprintf(w, "%d L %d %x\n", d, nd.start, t.src[nd.start:nd.end])
	} else {
		fmt.Fprintf(w, "%d N %s\n", d, nodeNames[nd.kind])
	}
	for c := nd.first; c != noNode; c = t.nodes[c].next {
		walkOut(w, t, c, d+1)
	}
}

var phaseName atomic.Value

func markPhase(name string) {
	phaseName.Store(name)
	if p := os.Getenv("CG_HEAP_AT"); p != "" {
		heapAt(name)
	}
}

func peakWatch() {
	path := os.Getenv("CG_PEAK_TRACE")
	if path == "" {
		phaseName.Store("start")
		return
	}
	f, err := os.Create(path)
	if err != nil {
		return
	}
	phaseName.Store("start")
	var lastPeak uint64
	n := 0
	t0 := time.Now()
	go func() {
		for {
			var ms runtime.MemStats
			runtime.ReadMemStats(&ms)
			fmt.Fprintf(f, "t=%7.3f phase=%-14s heapInuse=%9.1fMiB heapAlloc=%9.1fMiB heapSys=%9.1fMiB sys=%9.1fMiB numGC=%d\n",
				time.Since(t0).Seconds(), phaseName.Load(),
				float64(ms.HeapInuse)/(1<<20), float64(ms.HeapAlloc)/(1<<20),
				float64(ms.HeapSys)/(1<<20), float64(ms.Sys)/(1<<20), ms.NumGC)
			if ms.HeapInuse > lastPeak+(32<<20) {
				lastPeak = ms.HeapInuse
				n++
				if pf, err := os.Create(fmt.Sprintf("%s.peak%03d", path, n)); err == nil {
					_ = pprof.Lookup("heap").WriteTo(pf, 0)
					pf.Close()
				}
			}
			time.Sleep(5 * time.Millisecond)
		}
	}()
}

func startCPU(f *os.File) { pprof.StartCPUProfile(f) }
func stopCPU()            { pprof.StopCPUProfile() }
func writeHeap(f *os.File) {
	runtime.GC()
	_ = pprof.WriteHeapProfile(f)
}

func heapAt(phase string) {
	p := os.Getenv("CG_HEAP_AT")
	if p == "" {
		return
	}
	f, err := os.Create(p + "." + phase)
	if err == nil {
		writeHeap(f)
		f.Close()
	}
}

func mutexBlockWatch() {
	if os.Getenv("CG_MUTEX") == "" {
		return
	}
	runtime.SetMutexProfileFraction(5)
	runtime.SetBlockProfileRate(1)
}

func writeMutexBlock() {
	p := os.Getenv("CG_MUTEX")
	if p == "" {
		return
	}
	if f, err := os.Create(p + ".mutex"); err == nil {
		_ = pprof.Lookup("mutex").WriteTo(f, 0)
		f.Close()
	}
	if f, err := os.Create(p + ".block"); err == nil {
		_ = pprof.Lookup("block").WriteTo(f, 0)
		f.Close()
	}
}

type scope struct {
	symID  int32
	qual   string
	typeNm string
	typeID int32
	depth  int32
}

type FileRec struct {
	FID    int32
	MID    int32
	Rel    string
	Abs    string
	Text   []byte
	Lang   string
	IsTest bool
	IsGen  bool
	IsVend bool
}

var funcKinds = map[NodeKind]string{
	kFuncDecl: "function", kMethodDecl: "method", kFuncLit: "closure",
}
var typeKinds = map[NodeKind]string{kTypeSpec: "type"}

func (x *extractor) nodeName(t *Tree, n int32) string {
	nd := t.nodes[n]
	if nd.field == fName || (nd.kind == kFuncLit) {

	}
	if nd.kind != kFuncLit {
		if c := t.child(n, fName); c != noNode {
			return strings.TrimSpace(t.text(c))
		}
	}
	for c := nd.first; c != noNode; c = t.nodes[c].next {
		k := t.nodes[c].kind
		if !nodeNamed[k] {
			continue
		}
		switch k {
		case kIdentifier, kFieldIdent, kTypeIdent, kPackageIdent:
			return strings.TrimSpace(t.text(c))
		}
	}
	return ""
}

func (x *extractor) walkScope(t *Tree, root int32, sc scope) {
	type item struct {
		n  int32
		sc scope
	}

	stack := make([]item, 0, 64)
	pushAll := func(n int32, sc scope) {
		var rev []int32
		for c := t.nodes[n].first; c != noNode; c = t.nodes[c].next {
			rev = append(rev, c)
		}
		for _, r := range slices.Backward(rev) {
			stack = append(stack, item{r, sc})
		}
	}
	pushAll(root, sc)
	for len(stack) > 0 {
		it := stack[len(stack)-1]
		stack = stack[:len(stack)-1]
		cur, s := it.n, it.sc
		if kind, ok := funcKinds[t.nodes[cur].kind]; ok {
			sid := x.emitFunction(t, cur, s, kind)
			nm := x.nodeName(t, cur)
			if nm == "" {
				nm = "?"
			}
			inner := scope{sid, s.qual + nm + ".", s.typeNm, s.typeID, s.depth + 1}
			body := t.child(cur, fBody)
			if body == noNode {
				body = cur
			}
			pushAll(body, inner)
			continue
		}
		if kind, ok := typeKinds[t.nodes[cur].kind]; ok {
			sid := x.emitType(t, cur, s, kind)
			nm := x.nodeName(t, cur)
			if nm == "" {
				nm = "?"
			}
			inner := scope{sid, s.qual + nm + ".", nm, sid, s.depth + 1}
			pushAll(cur, inner)
			continue
		}
		pushAll(cur, s)
	}
}

func isFuncOrType(k NodeKind) bool {
	if _, ok := funcKinds[k]; ok {
		return true
	}
	_, ok := typeKinds[k]
	return ok
}

func (x *extractor) emitFunction(t *Tree, n int32, sc scope, kind string) int32 {
	nm := x.nodeName(t, n)
	if nm == "" {
		nm = "(anonymous)"
	}
	body := t.child(n, fBody)
	if body == noNode {
		body = n
	}
	st := x.measure(t, body, nil)
	x.sid = -1
	m := &x.m
	*m = metric{}
	x.typeNm = sc.typeNm
	x.copyCounts(st)
	m.Cyclomatic = st.cyc
	m.Cognitive = st.cog
	m.MaxNesting = st.maxNest
	m.MaxLoopDepth = st.maxLoop
	m.NTokens = st.nTokens
	m.NOperators = st.nOper
	m.NOperands = st.nOperand
	m.NDistinctOperators = int32(len(st.operSet))
	m.NDistinctOperands = int32(len(st.operands))
	m.Sloc = x.slocOf(t, n)
	m.BodyBytes = t.nodes[body].end - t.nodes[body].start
	m.IsGenerated = boolInt(x.file.IsGen)
	x.countParams(t, n, m)
	x.functionFlags(t, n, m)
	doc := x.docstringLines(t, n)
	m.NDocLines = doc
	m.HasDoc = boolInt(doc > 0)
	sig := x.signatureOf(t, n)

	vis := "private"
	if nm != "" && unicode.IsUpper(firstRune(nm)) {
		vis = "public"
	}
	sid := x.insert(t, nm, kind, n, trunc(sc.qual+nm, 400), sc.symID, sig,
		x.returnTypeOf(t, n), vis)

	x.emitParams(t, n, sid)
	for _, c := range st.calls {
		if c.dynamic || c.name == nullStr {
			continue
		}
		x.g.pSid = append(x.g.pSid, sid)
		x.g.pFid = append(x.g.pFid, x.file.FID)
		x.g.pMid = append(x.g.pMid, x.file.MID)
		x.g.pLine = append(x.g.pLine, c.line)
		x.g.pName = append(x.g.pName, c.name)
		x.g.pType = append(x.g.pType, x.g.intern(sc.typeNm))
	}
	x.emitHazards(t, st, sid)
	x.emitSatellites(t, st, sid)
	return sid
}

func (x *extractor) emitType(t *Tree, n int32, sc scope, kind string) int32 {
	nm := x.nodeName(t, n)
	if nm == "" {
		nm = "(anonymous)"
	}
	m := &x.m

	st := x.measure(t, n, isFuncOrType)
	x.sid = -1
	*m = metric{}
	x.recvType = ""
	x.typeNm = sc.typeNm
	x.copyCounts(st)
	m.Sloc = x.slocOf(t, n)
	m.IsGenerated = boolInt(x.file.IsGen)
	m.NTokens = st.nTokens
	m.NOperators = st.nOper
	m.NOperands = st.nOperand
	m.IsPublic = boolInt(nm != "" && unicode.IsUpper(firstRune(nm)))
	doc := x.docstringLines(t, n)
	m.NDocLines = doc
	m.HasDoc = boolInt(doc > 0)

	vis := "private"
	if nm != "" && unicode.IsUpper(firstRune(nm)) {
		vis = "public"
	}
	sid := x.insert(t, nm, kind, n, sc.qual+nm, sc.symID,
		trunc(strings.TrimSpace(strings.SplitN(t.text(n), "{", 2)[0]), 300), "", vis)
	for _, c := range st.calls {
		if c.dynamic || c.name == nullStr {
			continue
		}
		x.g.pSid = append(x.g.pSid, sid)
		x.g.pFid = append(x.g.pFid, x.file.FID)
		x.g.pMid = append(x.g.pMid, x.file.MID)
		x.g.pLine = append(x.g.pLine, c.line)
		x.g.pName = append(x.g.pName, c.name)
		x.g.pType = append(x.g.pType, x.g.intern(sc.typeNm))
	}
	x.emitHazards(t, st, sid)
	x.typeSatellites(t, n, sid)
	return sid
}

func boolInt(b bool) int32 {
	if b {
		return 1
	}
	return 0
}

func (x *extractor) copyCounts(st *bodyStats) {
	for i, v := range st.counts {
		if v != 0 {
			x.symPut(metricNames[i], v)
		}
	}
}

func (x *extractor) symPut(name string, v int32) {
	i, ok := metricIndex[name]
	if !ok {
		return
	}
	x.bump(i, v)
}

func (x *extractor) bump(i int, v int32) {
	(*[256]int32)(unsafe.Pointer(&x.m))[i] += v
}

func (x *extractor) bumpGet(i int) int32 { return (*[256]int32)(unsafe.Pointer(&x.m))[i] }

func init() {
	if int(unsafe.Sizeof(metric{})) != 4*len(metricNames) || len(metricNames) > 256 {
		panic("metric struct and metricNames disagree")
	}
}

func (x *extractor) insert(t *Tree, name, kind string, n int32, qual string,
	parent int32, sig, ret, vis string) int32 {
	g := x.g
	nd := t.nodes[n]
	i := g.Sym.push()
	g.Sym.FileId[i] = x.file.FID
	g.Sym.ModuleId[i] = x.file.MID
	g.Sym.ParentId[i] = parent
	g.Sym.Name[i] = g.intern(name)
	g.Sym.QualName[i] = g.intern(qual)
	g.Sym.Kind[i] = g.intern(kind)
	g.Sym.LineStart[i] = nd.line + 1
	g.Sym.LineEnd[i] = nd.endLn + 1
	g.Sym.NLines[i] = nd.endLn - nd.line + 1
	g.Sym.ByteStart[i] = nd.start
	g.Sym.ByteEnd[i] = nd.end

	g.Sym.Signature[i] = g.intern(trunc(sig, 400))
	g.Sym.ReturnType[i] = g.intern(trunc(ret, 200))
	g.Sym.Visibility[i] = g.intern(vis)
	g.Sym.ReceiverType[i] = g.intern(x.recvType)
	for j := range metricNames {
		x.g.Sym.putIdx(i, j, x.bumpGet(j))
	}
	for len(x.g.symTypeName) <= i {
		x.g.symTypeName = append(x.g.symTypeName, "")
	}
	x.g.symTypeName[i] = x.typeNm
	x.g.byName[name] = append(x.g.byName[name], int32(i))
	return int32(i)
}

func firstRune(s string) rune {
	for _, r := range s {
		return r
	}
	return 0
}

func (x *extractor) countParams(t *Tree, n int32, m *metric) {
	p := t.child(n, fParameters)
	if p == noNode {
		return
	}
	kids := x.namedKids(t, p)

	kept := kids[:0]
	for _, c := range kids {
		if t.nodes[c].kind != kComment {
			kept = append(kept, c)
		}
	}
	kids = kept
	m.NParams = int32(len(kids))
	var opt int32
	for _, c := range kids {
		k := t.nodes[c].kind
		if k == kVariadicParamDecl {
			opt++
			continue
		}
		if t.child(c, fValue) != noNode {
			opt++
		}
	}

	_ = opt
}

func (x *extractor) emitParams(t *Tree, n int32, sid int32) {
	p := t.child(n, fParameters)
	if p == noNode {
		return
	}
	pos := int32(0)
	for c := t.nodes[p].first; c != noNode; c = t.nodes[c].next {
		if !nodeNamed[t.nodes[c].kind] || t.nodes[c].kind == kComment {
			continue
		}
		name := x.nodeName(t, c)
		tn := t.child(c, fType)
		ptype := ""
		if tn != noNode {
			ptype = strings.TrimSpace(t.text(tn))
		}
		if name == "" {
			name = trunc(strings.TrimSpace(t.text(c)), 80)
		}

		x.g.Params = append(x.g.Params, Param{
			sym: sid, Pos: pos, Name: x.g.intern(trunc(name, 120)), Typ: x.g.intern(trunc(ptype, 200)),
			Default: nullStr,
			Untyped: boolInt(ptype == ""),
			Depth:   int32(strings.Count(ptype, "<") + strings.Count(ptype, "[")),
		})
		x.g.paramsSym = append(x.g.paramsSym, sid)
		pos++
	}
}

func (x *extractor) functionFlags(t *Tree, n int32, m *metric) {
	nm := x.nodeName(t, n)
	sig := x.signatureOf(t, n)
	recv := t.child(n, fReceiver)
	recvType, recvPtr := "", int32(0)
	if recv != noNode {
		rtxt := t.text(recv)
		recvPtr = boolInt(strings.Contains(rtxt, "*"))
		if mm := reRecvType.FindStringSubmatch(strings.TrimSpace(rtxt)); mm != nil {
			recvType = mm[1]
		}
	}
	p := t.child(n, fParameters)
	ptxt := ""
	if p != noNode {
		ptxt = t.text(p)
	}
	res := t.child(n, fResult)
	rtxt := ""
	if res != noNode {
		rtxt = t.text(res)
	}
	m.IsPublic = boolInt(nm != "" && unicode.IsUpper(firstRune(nm)))
	m.IsTest = boolInt(strings.HasPrefix(nm, "Test") || strings.HasPrefix(nm, "Benchmark") ||
		strings.HasPrefix(nm, "Fuzz") || strings.HasPrefix(nm, "Example"))
	m.IsEntrypoint = boolInt(nm == "main" || nm == "init")
	m.IsInit = boolInt(nm == "init")
	m.IsHandler = boolInt(reHandlerSig.MatchString(sig))
	m.ReceiverIsPointer = recvPtr
	m.NCtxParams = int32(strings.Count(ptxt, "context.Context"))
	if strings.Contains(ptxt, "any") || strings.Contains(ptxt, "interface") {
		m.NAnyParams = int32(len(reAnyParam.FindAllString(ptxt, -1)))
	}
	m.NIfaceParams = int32(strings.Count(ptxt, "interface{") + strings.Count(ptxt, " any"))
	m.NIfaceReturns = boolInt((strings.Contains(rtxt, "any") ||
		strings.Contains(rtxt, "interface") || strings.Contains(rtxt, "error")) &&
		reIfaceReturn.MatchString(rtxt))
	m.NNamedResults = boolInt(strings.Contains(rtxt, "(") &&
		reNamedResults.MatchString(rtxt))
	m.NGenericParams = boolInt(t.child(n, fTypeParameters) != noNode)
	x.recvType = recvType

}

func (x *extractor) slocOf(t *Tree, n int32) int32 {
	nd := t.nodes[n]
	var c int32
	for i, ln := range t.lines {
		if i < int(nd.line) {
			continue
		}
		if i > int(nd.endLn) {
			break
		}
		lo := ln

		if i == int(nd.line) && nd.start > lo {
			lo = nd.start
		}
		var hi int32
		if i+1 < len(t.lines) {
			hi = t.lines[i+1]
		} else {
			hi = int32(len(t.src))
		}
		if i == int(nd.endLn) && nd.end < hi && nd.end > lo {
			hi = nd.end
		}
		s := strings.TrimSpace(string(t.src[lo:hi]))
		if s == "" || isCommentPrefix(s) {
			continue
		}
		c++
	}
	return c
}

var commentPrefixes = []string{"//", "#", "/*", "*", "*/", `"""`, "'''", "--", "%"}

func isCommentPrefix(s string) bool {
	for _, p := range commentPrefixes {
		if strings.HasPrefix(s, p) {
			return true
		}
	}
	return false
}

func (x *extractor) signatureOf(t *Tree, n int32) string {
	end := t.nodes[n].end
	if b := t.child(n, fBody); b != noNode {
		end = t.nodes[b].start
	}
	nd := t.nodes[n]
	return strings.TrimSpace(string(t.src[nd.start:end]))
}

func (x *extractor) returnTypeOf(t *Tree, n int32) string {
	r := t.child(n, fResult)
	if r == noNode {
		return ""
	}
	return strings.TrimSpace(t.text(r))
}

func (x *extractor) docstringLines(t *Tree, n int32) int32 {
	nd := t.nodes[n]

	prev := noNode
	if nd.parent != noNode {
		prev = t.prevSibling(nd.parent, n)
	}
	cnt := int32(0)
	for prev != noNode && t.nodes[prev].kind == kComment {
		pn := &t.nodes[prev]
		txt := strings.TrimLeft(t.text(prev), " \t")
		if hasDocPrefix(txt) {
			cnt += pn.endLn - pn.line + 1
		} else if cnt == 0 && pn.endLn+1 >= nd.line {
			cnt += pn.endLn - pn.line + 1
		} else {
			break
		}
		prev = t.prevSibling(pn.parent, prev)
	}
	return cnt
}

func hasDocPrefix(s string) bool {
	for _, p := range docPrefixes {
		if strings.HasPrefix(s, p) {
			return true
		}
	}
	return false
}

func (t *Tree) prevSibling(parent, n int32) int32 {
	if parent == noNode {
		return noNode
	}
	prev := noNode
	for c := t.nodes[parent].first; c != noNode; c = t.nodes[c].next {
		if c == n {
			return prev
		}
		prev = c
	}
	return noNode
}

type NodeKind uint16

const (
	kSourceFile NodeKind = iota
	kPackageClause
	kFuncDecl
	kMethodDecl
	kTypeDecl
	kImportDecl
	kConstDecl
	kVarDecl
	kTypeSpec
	kConstSpec
	kVarSpec
	kImportSpecList
	kConstSpecList
	kVarSpecList
	kTypeSpecList
	kImportSpec
	kBlock
	kStmtList
	kParamList
	kParamDecl
	kVariadicParamDecl
	kTypeParams
	kTypeParamDecl
	kTypeConstraint
	kTypeArgs
	kGenericType
	kFieldDeclList
	kFieldDecl
	kFuncLit
	kExprStmt
	kAssignStmt
	kShortVarDecl
	kIfStmt
	kForStmt
	kRangeClause
	kForClause
	kSwitchStmt
	kTypeSwitchStmt
	kTypeSwitchHeader
	kSelectStmt
	kCaseClauseExpr
	kCaseClauseType
	kCaseClauseComm
	kCaseDefault
	kReturnStmt
	kBreakStmt
	kContinueStmt
	kGotoStmt
	kFallthroughStmt
	kIncStmt
	kDecStmt
	kSendStmt
	kLabeledStmt
	kGoStmt
	kDeferStmt
	kEmptyStmt
	kExprList
	kArgList
	kLiteralValue
	kLiteralElement
	kKeyedElement
	kComment
	kIdentifier
	kFieldIdent
	kTypeIdent
	kPackageIdent
	kBlankIdent
	kDot
	kLabelName
	kTypeParamName
	kIntLit
	kFloatLit
	kImaginaryLit
	kRuneLit
	kCharLit
	kInterpStr
	kRawStr
	kTypeElem
	kMethodElem
	kNegatedType
	kArrayType
	kSliceType
	kStructType
	kFuncType
	kInterfaceType
	kMapType
	kChanType
	kPointerType
	kQualifiedType
	kParenthesized
	kSelector
	kIndexExpr
	kIndexListExpr
	kSliceExpr
	kTypeAssert
	kCallExpr
	kUnaryExpr
	kBinaryExpr
	kEllipsis
	kToken
	kTypeInstantiation
	kVariadicArgument
	kStringContent
	kImplicitArray
	kParenType
	kEmpty
	kEscapeSequence
	kTypeAlias
	kOperator
	kTypeConversion
	kReceiveStmt
	kCompositeLit
	kError
	kMissing
	nodeKindCount
)

var nodeNames = [nodeKindCount]string{
	kSourceFile:        "source_file",
	kPackageClause:     "package_clause",
	kImportSpecList:    "import_spec_list",
	kConstSpecList:     "const_spec_list",
	kVarSpecList:       "var_spec_list",
	kTypeSpecList:      "type_spec_list",
	kFuncDecl:          "function_declaration",
	kMethodDecl:        "method_declaration",
	kTypeDecl:          "type_declaration",
	kImportDecl:        "import_declaration",
	kConstDecl:         "const_declaration",
	kVarDecl:           "var_declaration",
	kTypeSpec:          "type_spec",
	kConstSpec:         "const_spec",
	kVarSpec:           "var_spec",
	kImportSpec:        "import_spec",
	kBlock:             "block",
	kStmtList:          "statement_list",
	kParamList:         "parameter_list",
	kParamDecl:         "parameter_declaration",
	kVariadicParamDecl: "variadic_parameter_declaration",
	kTypeParams:        "type_parameter_list",
	kTypeParamDecl:     "type_parameter_declaration",
	kTypeConstraint:    "type_constraint",
	kTypeArgs:          "type_arguments",
	kGenericType:       "generic_type",
	kFieldDeclList:     "field_declaration_list",
	kFieldDecl:         "field_declaration",
	kFuncLit:           "func_literal",
	kExprStmt:          "expression_statement",
	kAssignStmt:        "assignment_statement",
	kShortVarDecl:      "short_var_declaration",
	kIfStmt:            "if_statement",
	kForStmt:           "for_statement",
	kRangeClause:       "range_clause",
	kForClause:         "for_clause",
	kSwitchStmt:        "expression_switch_statement",
	kTypeSwitchStmt:    "type_switch_statement",
	kTypeSwitchHeader:  "type_switch_header",
	kSelectStmt:        "select_statement",
	kCaseClauseExpr:    "expression_case",
	kCaseClauseType:    "type_case",
	kCaseClauseComm:    "communication_case",
	kCaseDefault:       "default_case",
	kReturnStmt:        "return_statement",
	kBreakStmt:         "break_statement",
	kContinueStmt:      "continue_statement",
	kGotoStmt:          "goto_statement",
	kFallthroughStmt:   "fallthrough_statement",
	kIncStmt:           "inc_statement",
	kDecStmt:           "dec_statement",
	kSendStmt:          "send_statement",
	kLabeledStmt:       "labeled_statement",
	kGoStmt:            "go_statement",
	kDeferStmt:         "defer_statement",
	kEmptyStmt:         "empty_statement",
	kExprList:          "expression_list",
	kArgList:           "argument_list",
	kLiteralValue:      "literal_value",
	kLiteralElement:    "literal_element",
	kKeyedElement:      "keyed_element",
	kComment:           "comment",
	kIdentifier:        "identifier",
	kFieldIdent:        "field_identifier",
	kTypeIdent:         "type_identifier",
	kPackageIdent:      "package_identifier",
	kBlankIdent:        "blank_identifier",
	kDot:               "dot",
	kLabelName:         "label_name",
	kTypeParamName:     "type_parameter_name",
	kIntLit:            "int_literal",
	kFloatLit:          "float_literal",
	kImaginaryLit:      "imaginary_literal",
	kRuneLit:           "rune_literal",
	kCharLit:           "char_literal",
	kInterpStr:         "interpreted_string_literal",
	kRawStr:            "raw_string_literal",
	kTypeElem:          "type_elem",
	kMethodElem:        "method_elem",
	kNegatedType:       "negated_type",
	kArrayType:         "array_type",
	kSliceType:         "slice_type",
	kStructType:        "struct_type",
	kFuncType:          "function_type",
	kInterfaceType:     "interface_type",
	kMapType:           "map_type",
	kChanType:          "channel_type",
	kPointerType:       "pointer_type",
	kQualifiedType:     "qualified_type",
	kParenthesized:     "parenthesized_expression",
	kSelector:          "selector_expression",
	kIndexExpr:         "index_expression",
	kIndexListExpr:     "index_list_expression",
	kSliceExpr:         "slice_expression",
	kTypeAssert:        "type_assertion_expression",
	kCallExpr:          "call_expression",
	kUnaryExpr:         "unary_expression",
	kBinaryExpr:        "binary_expression",
	kEllipsis:          "ellipsis",
	kToken:             "token",
	kVariadicArgument:  "variadic_argument",
	kStringContent:     "interpreted_string_literal_content",
	kImplicitArray:     "implicit_length_array_type",
	kParenType:         "parenthesized_type",
	kEmpty:             "call_expression",
	kEscapeSequence:    "escape_sequence",
	kTypeAlias:         "type_alias",
	kOperator:          "operator",
	kTypeConversion:    "type_conversion_expression",
	kReceiveStmt:       "receive_statement",
	kCompositeLit:      "composite_literal",
	kError:             "ERROR",
	kMissing:           "MISSING",
}

var nodeNamed = func() [nodeKindCount]bool {
	var a [nodeKindCount]bool
	for i := range a {
		a[i] = true
	}

	a[kToken] = false
	return a
}()

var pureToken = [nodeKindCount]bool{
	kIdentifier: true, kFieldIdent: true, kTypeIdent: true,
	kPackageIdent: true, kBlankIdent: true, kLabelName: true,
	kIntLit: true, kFloatLit: true, kImaginaryLit: true, kRuneLit: true,
	kCharLit: true, kMissing: true, kComment: true, kToken: true,
}

type Slot uint8

const (
	fNone Slot = iota
	fBody
	fParameters
	fResult
	fAlternative
	fFunction
	fArguments
	fType
	fName
	fReceiver
	fPath
	fLeft
	fRight
	fValue
	fOperand
	fSelectorField
	fOperator
	fConsequence
	fCondition
	fInitializer
	fTypeParameters
	fElement
	fKey
	fIndex
	fInit
	fPost
	fChannel
	fPackage
	fAlias
	fTypeArgs
	fLabel
	fTag
)

type Node struct {
	kind   NodeKind
	field  Slot
	parent int32
	first  int32
	next   int32
	start  int32
	end    int32
	line   int32
	endLn  int32
}

const noNode = int32(-1)

type Token struct {
	off  int32
	end  int32
	line int32
	endL int32
	kind NodeKind
}

type Tree struct {
	nodes []Node

	tail  []int32
	toks  []Token
	src   []byte
	lines []int32
	root  int32

	nerr int32
}

func (t *Tree) text(n int32) string { return string(t.src[t.nodes[n].start:t.nodes[n].end]) }

func (t *Tree) child(n int32, f Slot) int32 {
	for c := t.nodes[n].first; c != noNode; c = t.nodes[c].next {
		if t.nodes[c].field == f {
			return c
		}
	}
	return noNode
}

func (t *Tree) nChild(n int32) int32 {
	var k int32
	for c := t.nodes[n].first; c != noNode; c = t.nodes[c].next {
		k++
	}
	return k
}

func (t *Tree) lineOf(off int32) int32 {
	lo, hi := 0, len(t.lines)-1
	for lo < hi {
		mid := (lo + hi + 1) / 2
		if t.lines[mid] <= off {
			lo = mid
		} else {
			hi = mid - 1
		}
	}
	return int32(lo)
}

var (
	isLoop    [nodeKindCount]bool
	isBranch  [nodeKindCount]bool
	isNest    [nodeKindCount]bool
	isCall    [nodeKindCount]bool
	isOper    [nodeKindCount]bool
	isString  [nodeKindCount]bool
	isNumber  [nodeKindCount]bool
	isComment [nodeKindCount]bool
	isIf      [nodeKindCount]bool
	counterOf [nodeKindCount]uint8
)

func mark(set *[nodeKindCount]bool, kinds ...NodeKind) {
	for _, k := range kinds {
		set[k] = true
	}
}

func init() {
	mark(&isLoop, kForStmt)
	initCounters()
}

func initCounters() {
	mark(&isLoop, kForStmt)
	mark(&isBranch, kIfStmt)
	mark(&isNest, kIfStmt, kForStmt, kSwitchStmt, kTypeSwitchStmt, kSelectStmt, kFuncLit)
	mark(&isCall, kCallExpr)
	mark(&isOper, kBinaryExpr, kUnaryExpr, kAssignStmt, kIncStmt, kDecStmt,
		kIndexExpr, kSelector, kSliceExpr, kTypeAssert)
	mark(&isString, kInterpStr, kRawStr)
	mark(&isNumber, kIntLit, kFloatLit, kImaginaryLit)
	mark(&isComment, kComment)
	mark(&isIf, kIfStmt)

	counters := map[NodeKind]string{
		kReturnStmt: "n_returns", kGoStmt: "n_goroutines",
		kDeferStmt: "n_defer", kSelectStmt: "n_select",
		kSwitchStmt: "n_switch", kTypeSwitchStmt: "n_type_switch",
		kCaseClauseExpr: "n_cases", kCaseClauseType: "n_cases",
		kCaseDefault: "n_select_default", kSendStmt: "n_chan_send",
		kChanType: "n_chan_type", kFuncLit: "n_lambda",
		kTypeAssert: "n_type_assert", kLabeledStmt: "n_labels",
		kGotoStmt: "n_gotos", kInterfaceType: "n_iface_literal",
		kCompositeLit: "n_composite_lit", kTypeParams: "n_generic_params",
		kStructType: "n_struct_literal", kAssignStmt: "n_assign",
		kShortVarDecl: "n_assign", kIncStmt: "n_incdec", kDecStmt: "n_incdec",
	}
	for k, name := range counters {
		if i, ok := metricIndex[name]; ok {
			counterOf[k] = uint8(i + 1)
		}
	}

	loops := map[string]string{
		"Sprintf": "n_sprintf_in_loop", "append": "n_append_in_loop",
		"MustCompile": "regex_in_loop", "Compile": "regex_in_loop",
		"Lock": "lock_in_loop", "QueryContext": "query_in_loop",
		"Query": "query_in_loop", "ExecContext": "query_in_loop",
		"WithTimeout": "n_ctx_in_loop", "WithDeadline": "n_ctx_in_loop",
		"WithCancel": "n_ctx_in_loop",
	}
	loopCallBase = make(map[string]int, len(loops))
	loopCallSub = make(map[string]int, len(loops))
	for name, col := range loops {
		i, ok := metricIndex[col]
		if !ok {
			continue
		}
		loopCallBase[name] = i
		loopCallSub[name] = i
	}
}

var loopCallBase, loopCallSub map[string]int

type bodyStats struct {
	counts    []int32
	cyc       int32
	cog       int32
	maxNest   int32
	maxLoop   int32
	nTokens   int32
	nOper     int32
	nOperand  int32
	operSet   map[NodeKind]bool
	operands  map[string]struct{}
	calls     []pendingCall
	literals  []pendingLit
	inputs    []pendingInput
	secrets   []pendingSecret
	extra     []pendingExtra
	wgOps     []pendingWg
	closeVars []string
	callText  int32
	callRaw   string
	namedKids []int32
	kids      []int32
}

type pendingCall struct {
	name    uint32
	line    int32
	dynamic bool
}

type pendingLit struct {
	kind  uint32
	value uint32
	line  int32
	magic bool
}

type pendingInput struct {
	vari   uint32
	kind   uint32
	line   int32
	inLoop bool
}

type pendingSecret struct {
	value uint32
	line  int32
}

type pendingExtra struct {
	kind  uint8
	node  int32
	depth int32
}

type pendingWg struct {
	vari   uint32
	op     uint32
	line   int32
	inGo   int32
	inLoop bool
}

func newBodyStats() *bodyStats {
	return &bodyStats{
		counts:   make([]int32, len(metricNames)),
		operSet:  make(map[NodeKind]bool, 16),
		operands: make(map[string]struct{}, 256),
	}
}

func (s *bodyStats) reset() {
	for i := range s.counts {
		s.counts[i] = 0
	}
	s.cyc, s.cog, s.maxNest, s.maxLoop = 1, 0, 0, 0
	s.nTokens, s.nOper, s.nOperand = 0, 0, 0
	clear(s.operSet)
	clear(s.operands)
	s.calls = s.calls[:0]
	s.literals = s.literals[:0]
	s.inputs = s.inputs[:0]
	s.secrets = s.secrets[:0]
	s.extra = s.extra[:0]
	s.wgOps = s.wgOps[:0]
	s.closeVars = s.closeVars[:0]
}

func (s *bodyStats) bump(i int) { s.counts[i]++ }

func (s *bodyStats) bumpName(name string) {
	if i, ok := metricIndex[name]; ok {
		s.counts[i]++
	}
}

func (x *extractor) measure(t *Tree, body int32, prune func(NodeKind) bool) *bodyStats {
	x.stats.reset()
	st := x.stats
	if body == noNode {
		body = t.root
	}
	var nestStack, loopStack []int32
	loopDepth := int32(0)
	depth := int32(0)
	n := body

	lo, hi := t.nodes[body].start, t.nodes[body].end
	for {
		nd := &t.nodes[n]
		if nd.start < lo || nd.start >= hi {
			st.nTokens += st.nOper
			return st
		}
		k := nd.kind
		for len(nestStack) > 0 && nestStack[len(nestStack)-1] >= depth {
			nestStack = nestStack[:len(nestStack)-1]
		}
		for len(loopStack) > 0 && loopStack[len(loopStack)-1] >= depth {
			loopStack = loopStack[:len(loopStack)-1]
			if loopDepth > 0 {
				loopDepth--
			}
		}
		named := nodeNamed[k]
		isElif := false
		if k == kIfStmt {
			isElif = x.isElseIf(t, n)
		}

		if named && isNest[k] && !isElif {
			nestStack = append(nestStack, depth)
			if int32(len(nestStack)) > st.maxNest {
				st.maxNest = int32(len(nestStack))
			}
		}
		if named && isLoop[k] {
			loopStack = append(loopStack, depth)
			loopDepth++
			if loopDepth > st.maxLoop {
				st.maxLoop = loopDepth
			}
			st.cyc++
			st.cog += max32(1, int32(len(nestStack)))
			st.bumpName("n_loops")
		} else if named && isBranch[k] {
			st.cyc++
			if isElif {
				st.cog++
			} else {
				st.cog += max32(1, int32(len(nestStack)))
			}
			st.bumpName("n_branches")
			if isElif {
				st.bumpName("n_elif")
			}
			if loopDepth > 0 {
				st.bumpName("branch_in_loop")
			}
		}
		if c := counterOf[k]; c != 0 {
			st.counts[c-1]++
		}
		switch {
		case isCall[k]:
			x.onCall(t, n, st, loopDepth, int32(len(nestStack)))
		case isOper[k]:
			st.nOper++
			st.operSet[k] = true
		case isString[k]:
			txt := t.text(n)
			st.bumpName("n_string_lit")
			st.operands[trunc(txt, 40)] = struct{}{}
			st.nOperand++
			x.onString(t, n, txt, st, loopDepth)
		case isNumber[k]:
			txt := strings.TrimSpace(t.text(n))
			st.operands[txt] = struct{}{}
			st.nOperand++
			magic := !magicStrings[txt] && numRe.MatchString(txt)
			if magic {
				st.bumpName("n_magic")
				st.literals = append(st.literals, pendingLit{kind: x.g.intern("number"), value: x.g.intern(txt), line: nd.line + 1, magic: true})
			}
			if strings.ContainsAny(txt, ".eE") {
				st.bumpName("n_float_lit")
			}
		case isComment[k]:
			st.counts[metricIndex["n_comment_lines"]] += nd.endLn - nd.line + 1
		case t.nChild(n) == 0:
			st.nTokens++
			st.nOperand++
			st.operands[trunc(t.text(n), 40)] = struct{}{}
		}
		x.onNode(t, n, st, loopDepth, int32(len(nestStack)))
		descend := prune == nil || !prune(k)
		if descend && nd.first != noNode {
			n = nd.first
			depth++
			continue
		}

		for {
			if t.nodes[n].next != noNode {
				n = t.nodes[n].next
				break
			}
			p := t.nodes[n].parent
			if p == noNode || n == body || p == body {
				st.nTokens += st.nOper
				return st
			}
			n = p
			depth--
		}
	}
}

func (x *extractor) isElseIf(t *Tree, n int32) bool {
	par := t.nodes[n].parent
	if par == noNode {
		return false
	}
	if t.nodes[par].kind == kIfStmt {
		alt := t.child(par, fAlternative)
		return alt != noNode && alt == n
	}
	gp := t.nodes[par].parent
	if gp == noNode || t.nodes[gp].kind != kIfStmt {
		return false
	}
	alt := t.child(gp, fAlternative)
	if alt != par {
		return false
	}
	first := t.nodes[par].first
	return first != noNode && first == n
}

func max32(a, b int32) int32 {
	if a > b {
		return a
	}
	return b
}

func trunc(s string, n int) string {
	if utf8.RuneCountInString(s) <= n {
		return s
	}
	c := 0
	for j := range s {
		if c == n {
			return s[:j]
		}
		c++
	}
	return s
}

var magicStrings = func() map[string]bool {
	m := map[string]bool{"": true, "0x0": true, "0x1": true, "0xff": true,
		"0xFF": true, "0.0": true, "1.0": true, "-1": true}
	for _, v := range []string{"0", "1", "2", "-1", "10", "100", "1000", "8", "16",
		"32", "64", "128", "256", "512", "1024", "255", "65535", "4096", "24", "60",
		"365", "7", "12", "3", "4", "6"} {
		m[v] = true
	}
	return m
}()

var numRe = regexp.MustCompile(`^[-+]?(?:0[xXbBoO][0-9a-fA-F_]+|[\d_]+(?:\.[\d_]*)?(?:[eE][-+]?\d+)?)[uUlLfFdD]*$`)

var (
	reErrNilCheck    = regexp.MustCompile(`\berr\s*!=\s*nil`)
	reReturnNil      = regexp.MustCompile(`\breturn\s+nil\b`)
	reReturnNilErr   = regexp.MustCompile(`\breturn\s+nil,\s*err\b`)
	reCommaErrAssign = regexp.MustCompile(`\b\w+\s*,\s*err\s*:=`)
	reBlankAssign    = regexp.MustCompile(`^\s*_\s*(?:,\s*_\s*)*[:=]`)
	reVarDecl        = regexp.MustCompile(`^\s*(\w+)\s*:=\s*`)
	reRangeCopy      = regexp.MustCompile(`^\s*\w+\s*,\s*\w+\s*:?=\s*range\b`)
	reSQL            = regexp.MustCompile(`(?i)\b(SELECT|INSERT\s+INTO|UPDATE|DELETE\s+FROM|CREATE\s+TABLE|DROP\s+TABLE|ALTER\s+TABLE)\b`)

	reRecvType     = regexp.MustCompile(`\*?([A-Za-z_]\w*)\s*(?:\[[^\]]*\])?\s*\)$`)
	reAnyParam     = regexp.MustCompile(`\b(?:any|interface\s*\{\s*\})\b`)
	reIfaceReturn  = regexp.MustCompile(`\b(?:any|interface\s*\{\s*\}|error)\b`)
	reNamedResults = regexp.MustCompile(`\(\s*\w+\s+\w`)
	reHandlerSig   = regexp.MustCompile(`http\.ResponseWriter|\*http\.Request|gin\.Context|echo\.Context|fiber\.Ctx|events\.APIGatewayProxyRequest|grpc\.ServerStream`)
	reGoBuild      = regexp.MustCompile(`(?m)^//go:build\s+(.+)$`)
	reGenerated    = regexp.MustCompile(`(?m)^// Code generated .* DO NOT EDIT\.$`)
	reWgOp         = regexp.MustCompile(`([A-Za-z_]\w*)\.(Add|Done|Wait)\(`)
	reArrayLen     = regexp.MustCompile(`^\[(\d+)\](.+)$`)
	reGomodGo      = regexp.MustCompile(`(?m)^go\s+(\d+)\.(\d+)`)
	reGomodModule  = regexp.MustCompile(`(?m)^module\s+(\S+)`)
	reGenName      = regexp.MustCompile(`(?i)(\.min\.|\.bundle\.|[-_.](gen|generated|pb|g)\.|_pb2|\.g\.dart$|\.designer\.|^zz_generated)`)
	reTestPath     = regexp.MustCompile(`(?i)(^|/)(tests?|test-d|spec|specs|__tests__|__snapshots__|testing|e2e|integration[-_]tests?|testdata|test_data|test-data|fixtures?)(/|$)`)
	reVendPath     = regexp.MustCompile(`(?i)(^|/)(vendor|third_party|thirdparty|external|node_modules|deps)(/|$)`)
	reTestNameGo   = regexp.MustCompile(`_test\.go$`)
)

var generatedMarkers = []string{
	"@generated", "DO NOT EDIT", "Code generated by", "AUTO-GENERATED",
	"autogenerated", "This file was automatically generated",
	"Generated by the protocol buffer compiler", "@flow-generated",
}

var docPrefixes = []string{"///", "/**", "##", `"""`, "'''", "#'", "--|"}

func atoi(s string) (int32, bool) {
	if s == "" {
		return 0, false
	}
	n := int32(0)
	for i := 0; i < len(s); i++ {
		if s[i] < '0' || s[i] > '9' {
			return 0, false
		}
		n = n*10 + int32(s[i]-'0')
	}
	return n, true
}

func lowerASCII(c byte) byte {
	if c >= 'A' && c <= 'Z' {
		return c + 32
	}
	return c
}

func isWordByte(c byte) bool {
	return c == '_' || c >= 'a' && c <= 'z' || c >= 'A' && c <= 'Z' || c >= '0' && c <= '9'
}

type foldSet struct{ by [256][]string }

func newFoldSet(lits ...string) *foldSet {
	f := &foldSet{}
	for _, l := range lits {
		c := lowerASCII(l[0])
		f.by[c] = append(f.by[c], l)
	}
	return f
}

func eqFold(s, lit string) bool {
	for i := 0; i < len(lit); i++ {
		if lowerASCII(s[i]) != lowerASCII(lit[i]) {
			return false
		}
	}
	return true
}

func (f *foldSet) has(s string) bool {
	for i := 0; i < len(s); i++ {
		for _, lit := range f.by[lowerASCII(s[i])] {
			if i+len(lit) <= len(s) && eqFold(s[i:i+len(lit)], lit) {
				return true
			}
		}
	}
	return false
}

var (
	authCalls = newFoldSet("auth", "login", "jwt", "session", "token")

	secrets = newFoldSet(
		"apikey", "api_key", "api-key",
		"secret", "password", "passwd", "pwd", "token", "bearer",
		"accesskey", "access_key", "access-key",
		"privatekey", "private_key", "private-key",
		"clientsecret", "client_secret", "client-secret",
		"authtoken", "auth_token", "auth-token",
		"jwt", "credential",
		"smtppass", "smtp_pass", "smtp-pass",
		"dbpass", "db_pass", "db-pass",
		"sk_live", "rk_live", "pk_live", "ghp_", "xoxb-", "akia")
)

func mayBeSQL(s string) bool {
	for i := 0; i+1 < len(s); i++ {
		switch lowerASCII(s[i]) {
		case 's':
			if lowerASCII(s[i+1]) == 'e' {
				return true
			}
		case 'i':
			if lowerASCII(s[i+1]) == 'n' {
				return true
			}
		case 'u':
			if lowerASCII(s[i+1]) == 'p' {
				return true
			}
		case 'd':
			if lowerASCII(s[i+1]) == 'e' {
				return true
			}
		case 'c':
			if lowerASCII(s[i+1]) == 'r' {
				return true
			}
		case 'a':
			if lowerASCII(s[i+1]) == 'l' {
				return true
			}
		}
		if lowerASCII(s[i]) == 'd' && lowerASCII(s[i+1]) == 'r' {
			return true
		}
	}
	return false
}

var markers = newFoldSet("TODO", "FIXME", "XXX", "HACK", "BUG", "NOTE",
	"WARNING", "OPTIMIZE", "REVIEW", "DEPRECATED", "SAFETY", "PANIC", "UNSAFE")

func findMarker(line string) (string, int, bool) {
	for i := 0; i < len(line); i++ {
		if isWordByte(line[i]) && i > 0 && isWordByte(line[i-1]) {

			continue
		}
		for _, lit := range markers.by[lowerASCII(line[i])] {
			if i+len(lit) > len(line) || !eqFold(line[i:i+len(lit)], lit) {
				continue
			}
			j := i + len(lit)
			if j < len(line) && isWordByte(line[j]) {
				continue
			}
			for j < len(line) && (line[j] == ' ' || line[j] == '\t') {
				j++
			}
			if j < len(line) && (line[j] == ':' || line[j] == '-' || line[j] == '(') {
				return line[i : i+len(lit)], i, true
			}
		}
	}
	return "", 0, false
}

func isIdent(s string) bool {
	if s == "" || (s[0] >= '0' && s[0] <= '9') {
		return false
	}
	for i := 0; i < len(s); i++ {
		if !isWordByte(s[i]) {
			return false
		}
	}
	return true
}

type extractor struct {
	g        *Graph
	stats    *bodyStats
	kids     []int32
	file     *FileRec
	tree     *Tree
	m        metric
	recvType string
	sid      int32
	typeNm   string
}

var requestReceivers = map[string]bool{"r": true, "req": true, "request": true}

var requestMethodKinds = map[string]string{
	"FormValue": "query", "PostFormValue": "form",
	"Cookie": "cookie", "MultipartReader": "form",
}

var requestFieldKinds = map[string]string{
	"Form": "form", "PostForm": "form", "Header": "header", "Body": "body",
}

var hazardCalls = map[string]string{
	"sync.WaitGroup": "goroutine", "errgroup.Group": "goroutine",
	"errgroup.WithContext": "goroutine", "singleflight.Do": "goroutine",
	"sync.Once": "goroutine", "OnceFunc": "goroutine", "OnceValue": "goroutine",
	"runtime.Gosched": "goroutine", "runtime.GOMAXPROCS": "goroutine",
	"runtime.LockOSThread": "goroutine", "runtime.Goexit": "goroutine",
	"runtime.NumGoroutine": "goroutine",
	"close":                "channel", "signal.Notify": "channel", "signal.Stop": "channel",
	"signal.NotifyContext": "channel",
	"recover":              "defer", "runtime.SetFinalizer": "defer",
	"sync.Mutex": "lock", "sync.RWMutex": "lock", "Lock": "lock",
	"Unlock": "lock", "RLock": "lock", "RUnlock": "lock", "TryLock": "lock",
	"sync.Map": "lock", "LoadOrStore": "lock", "sync.Cond": "lock",
	"sync.Pool":       "lock",
	"atomic.AddInt64": "atomic", "atomic.LoadInt64": "atomic",
	"atomic.StoreInt64": "atomic", "atomic.CompareAndSwapInt64": "atomic",
	"atomic.CompareAndSwapPointer": "atomic", "atomic.Value": "atomic",
	"atomic.Int64": "atomic", "atomic.Bool": "atomic", "atomic.Pointer": "atomic",
	"context.Background": "context", "context.TODO": "context",
	"context.WithCancel": "context", "context.WithTimeout": "context",
	"context.WithDeadline": "context", "context.WithValue": "context",
	"context.WithCancelCause": "context", "context.WithoutCancel": "context",
	"context.AfterFunc": "context",
	"os.Open":           "io", "os.Create": "io", "os.OpenFile": "io", "os.ReadFile": "io",
	"os.WriteFile": "io", "os.Remove": "io", "os.RemoveAll": "io",
	"os.MkdirAll": "io", "os.Stat": "io", "os.ReadDir": "io",
	"io.Copy": "io", "io.ReadAll": "io", "ioutil.ReadAll": "io",
	"ioutil.ReadFile": "io", "bufio.NewReader": "io", "bufio.NewWriter": "io",
	"bufio.NewScanner": "io", "filepath.Walk": "io", "filepath.WalkDir": "io",
	"filepath.Glob": "io", "os.CreateTemp": "io",
	"http.Get": "net", "http.Post": "net", "http.PostForm": "net",
	"http.NewRequest": "net", "http.NewRequestWithContext": "net",
	"http.ListenAndServe": "net", "http.ListenAndServeTLS": "net",
	"http.HandleFunc": "net", "http.Handle": "net", "http.Serve": "net",
	"net.Dial": "net", "net.DialTimeout": "net", "net.Listen": "net",
	"grpc.Dial": "net", "grpc.NewClient": "net",
	"httputil.NewSingleHostReverseProxy": "net",
	"sql.Open":                           "sql", "QueryContext": "sql", "QueryRowContext": "sql",
	"Query": "sql", "QueryRow": "sql", "Exec": "sql", "Prepare": "sql",
	"Begin": "sql", "Commit": "sql", "Rollback": "sql", "Scan": "sql",
	"ExecContext": "sql", "PrepareContext": "sql", "BeginTx": "sql",
	"gorm.Open": "sql", "Preload": "sql",
	"exec.Command": "exec", "exec.CommandContext": "exec",
	"exec.LookPath": "exec", "syscall.Exec": "exec", "syscall.Syscall": "exec",
	"os.Exit": "exec", "os.StartProcess": "exec",
	"unsafe.Pointer": "unsafe", "unsafe.Slice": "unsafe",
	"unsafe.String": "unsafe", "unsafe.Add": "unsafe",
	"unsafe.SliceData": "unsafe", "unsafe.StringData": "unsafe",
	"reflect.SliceHeader": "unsafe", "reflect.StringHeader": "unsafe",
	"reflect.TypeOf": "reflect", "reflect.ValueOf": "reflect",
	"reflect.New": "reflect", "reflect.DeepEqual": "reflect",
	"reflect.MakeSlice": "reflect", "json.Marshal": "reflect",
	"json.Unmarshal": "reflect", "json.NewDecoder": "reflect",
	"json.NewEncoder": "reflect", "yaml.Unmarshal": "reflect",
	"xml.Unmarshal": "reflect", "proto.Unmarshal": "reflect",
	"gob.NewDecoder": "reflect",
	"C.malloc":       "cgo", "C.free": "cgo", "C.CString": "cgo",
	"C.GoString": "cgo", "C.GoBytes": "cgo", "C.CBytes": "cgo",
	"cgo.NewHandle": "cgo", "runtime.KeepAlive": "cgo", "runtime.Pinner": "cgo",
	"make": "alloc", "new": "alloc", "append": "alloc",
	"bytes.NewBuffer": "alloc", "bytes.NewBufferString": "alloc",
	"strings.Builder": "alloc", "strings.Repeat": "alloc",
	"strings.Split": "alloc", "strings.Join": "alloc", "strings.Fields": "alloc",
	"strings.NewReplacer": "alloc", "fmt.Sprintf": "alloc",
	"fmt.Sprint": "alloc", "fmt.Sprintln": "alloc", "fmt.Errorf": "alloc",
	"strconv.Itoa": "alloc", "strconv.FormatInt": "alloc",
	"regexp.Compile": "alloc", "regexp.MustCompile": "alloc",
	"panic": "panic", "log.Fatal": "panic", "log.Fatalf": "panic",
	"log.Fatalln": "panic", "log.Panic": "panic", "log.Panicf": "panic",
	"template.Must": "panic",
	"time.Sleep":    "time", "time.After": "time", "time.Tick": "time",
	"time.NewTicker": "time", "time.NewTimer": "time", "time.AfterFunc": "time",
	"time.Now": "time", "time.Since": "time",
}

var (
	exitBases     = map[string]bool{"Fatal": true, "Fatalf": true, "Fatalln": true, "Exit": true}
	exitPkgs      = map[string]bool{"log": true, "os": true, "logrus": true, "klog": true}
	httpDefaults  = map[string]bool{"http.Get": true, "http.Post": true, "http.PostForm": true, "http.Head": true, "http.DefaultClient.Do": true}
	decodeBases   = map[string]bool{"Unmarshal": true, "NewDecoder": true}
	weakRandom    = map[string]bool{"rand.Int": true, "rand.Intn": true, "rand.Float64": true, "rand.Read": true, "rand.Int31": true, "rand.Int63": true}
	weakCrypto    = map[string]bool{"md5.New": true, "sha1.New": true, "md5.Sum": true, "sha1.Sum": true, "des.NewCipher": true, "rc4.NewCipher": true}
	decodeCalls   = map[string]bool{"json.Unmarshal": true, "json.NewDecoder": true, "yaml.Unmarshal": true, "gob.NewDecoder": true, "xml.Unmarshal": true}
	readAllCalls  = map[string]bool{"ioutil.ReadAll": true, "io.ReadAll": true}
	envCalls      = map[string]bool{"os.Getenv": true, "os.LookupEnv": true}
	unsafeCalls   = map[string]bool{"unsafe.Pointer": true, "unsafe.Sizeof": true, "unsafe.Slice": true, "unsafe.String": true}
	execCalls     = map[string]bool{"exec.Command": true, "exec.CommandContext": true, "syscall.Exec": true}
	reflectCalls  = map[string]bool{"reflect.ValueOf": true, "reflect.TypeOf": true, "reflect.DeepEqual": true}
	timerNewBases = map[string]bool{"NewTicker": true, "NewTimer": true}
	semaphoreBase = map[string]bool{"SetLimit": true, "Acquire": true, "TryAcquire": true}
	stdlibRoots   = map[string]bool{}
	builtins      = map[string]bool{}
)

func init() {
	for w := range strings.FieldsSeq(`archive bufio builtin bytes cmp compress container
context crypto database debug embed encoding errors expvar flag fmt go hash html
image index io iter log maps math mime net os path plugin reflect regexp runtime
slices sort strconv strings structs sync syscall testing text time unicode unsafe
unique weak`) {
		stdlibRoots[w] = true
	}
	for w := range strings.FieldsSeq(`append cap clear close complex copy delete imag
len make max min new panic print println real recover any bool byte comparable
complex64 complex128 error float32 float64 int int8 int16 int32 int64 rune string
uint uint8 uint16 uint32 uint64 uintptr true false iota nil`) {
		builtins[w] = true
	}
}

func (x *extractor) onCall(t *Tree, n int32, st *bodyStats, loopDepth, nest int32) {
	st.bumpName("n_calls")
	if loopDepth > 0 {
		st.bumpName("call_in_loop")
	}
	fn := t.child(n, fFunction)
	line1 := t.nodes[n].line + 1
	if fn == noNode {
		st.bumpName("n_dynamic_calls")
		st.calls = append(st.calls, pendingCall{name: nullStr, line: line1, dynamic: true})
		return
	}
	name := t.text(fn)
	st.callText = n
	st.callRaw = name
	name = strings.TrimSpace(name)
	base := lastDot(name)
	if head, ok := splitDot(name); ok && requestReceivers[head] {
		kind, isReq := requestMethodKinds[base]
		if strings.HasSuffix(name, ".URL.Query") {

			kind, isReq = "query", true
		}
		if isReq {
			st.inputs = append(st.inputs, pendingInput{
				vari: x.g.intern(trunc(t.text(n), 120)), kind: x.g.intern(kind),
				line: line1, inLoop: loopDepth > 0})
		}
	}
	if name == "http.Redirect" {
		st.bumpName("n_redirect")
	}
	if strings.HasPrefix(name, "json.") && decodeBases[base] || base == "Decode" {
		st.bumpName("n_deserialize")
	}
	if strings.HasPrefix(name, "os.Open") || strings.HasPrefix(name, "os.ReadFile") ||
		strings.HasPrefix(name, "os.WriteFile") || strings.HasPrefix(name, "os.Create") {
		if args := t.child(n, fArguments); args != noNode {

			c := noNode
			for k := t.nodes[args].first; k != noNode; k = t.nodes[k].next {
				if nodeNamed[t.nodes[k].kind] {
					c = k
					break
				}
			}
			if c != noNode {
				ct := t.nodes[c].kind
				if ct != kInterpStr && ct != kRawStr {
					st.bumpName("n_dynamic_open")
				}
			}
		}
	}
	if strings.HasPrefix(name, "zip.") {
		st.bumpName("n_zip_read")
	}
	if authCalls.has(name) {
		st.bumpName("n_auth_call")
	}
	if name == "context.Background" || name == "context.TODO" {
		st.bumpName("n_ctx_background_call")
	}
	if httpDefaults[name] {
		st.bumpName("n_http_default_client")
	}
	if head, ok := splitDot(name); ok && exitBases[base] && exitPkgs[head] {
		st.bumpName("n_exit_call")
	}
	if name == "time.After" && loopDepth > 0 {
		st.bumpName("n_time_after_in_loop")
	}
	if name == "time.Tick" {
		st.bumpName("n_time_tick_call")
	}
	if name == "fmt.Errorf" && !strings.Contains(t.text(n), "%w") {
		st.bumpName("n_errorf_no_wrap")
	}
	if weakRandom[name] {
		st.bumpName("n_weak_random")
	}
	if weakCrypto[name] {
		st.bumpName("n_weak_crypto")
	}
	if readAllCalls[name] && loopDepth > 0 {
		st.bumpName("n_readall_in_loop")
	}
	if envCalls[name] {
		st.bumpName("n_env_read")
	}
	if decodeCalls[name] {
		st.bumpName("n_decode_call")
	}
	if name == "sync.WaitGroup" || name == "wg.Add" || base == "Add" && strings.HasPrefix(name, "wg.") {
		st.bumpName("n_waitgroup_add")
	}
	if base == "Done" && !strings.HasPrefix(name, "ctx.") {
		st.bumpName("n_wg_done")
		if vari, ok := splitDot(name); ok && isIdent(vari) {
			st.wgOps = append(st.wgOps, pendingWg{vari: x.g.intern(vari), op: x.g.intern("Done"),
				line: line1, inGo: inGoroutine(t, n), inLoop: loopDepth > 0})
		}
	} else if base == "Add" && strings.Contains(name, ".") {
		if vari, ok := splitDot(name); ok && isIdent(vari) {
			st.wgOps = append(st.wgOps, pendingWg{vari: x.g.intern(vari), op: x.g.intern("Add"),
				line: line1, inGo: inGoroutine(t, n), inLoop: loopDepth > 0})
		}
	}
	if base == "Wait" {
		st.bumpName("n_wait_call")
		vari := ""
		if v, ok := splitDot(name); ok {
			vari = v
		}
		if isIdent(vari) {
			st.wgOps = append(st.wgOps, pendingWg{vari: x.g.intern(vari), op: x.g.intern("Wait"),
				line: line1, inGo: inGoroutine(t, n), inLoop: loopDepth > 0})
		}
	}
	if name == "time.Sleep" {
		st.bumpName("n_sleep")
	}
	if base == "Err" {
		st.bumpName("n_rows_err_check")
	}
	if name == "time.NewTicker" || name == "time.NewTimer" || name == "time.AfterFunc" || timerNewBases[base] {
		st.bumpName("n_timer_new")
	}
	if base == "Stop" {
		st.bumpName("n_timer_stop")
	}
	if semaphoreBase[base] {
		st.bumpName("n_semaphore")
	}
	if base == "cancel" {
		st.bumpName("n_cancel_called")
	}
	if base == "Lock" || base == "RLock" {
		st.bumpName("n_lock_call")
	}
	if base == "Unlock" || base == "RUnlock" {
		st.bumpName("n_unlock_call")
	}
	if base == "Close" {
		st.bumpName("n_close_call")
	}
	if reflectCalls[name] {
		st.bumpName("n_reflect_call")
	}
	if unsafeCalls[name] {
		st.bumpName("n_unsafe_call")
	}
	if execCalls[name] {
		st.bumpName("n_exec_call")
	}
	if (name == "filepath.Join" || name == "path.Join") && loopDepth > 0 {
		st.bumpName("n_pathjoin_in_loop")
	}
	dynamic := name == "" || !(isAlpha(name[0]) || name[0] == '_' || name[0] == '$')
	st.calls = append(st.calls, pendingCall{
		name: x.g.intern(trunc(name, 200)), line: line1, dynamic: dynamic})
	if dynamic {
		st.bumpName("n_dynamic_calls")
	}
	if loopDepth > 0 {
		if i, ok := loopCallBase[base]; ok {
			st.counts[i]++
		}
		for needle, i := range loopCallSub {
			if needle != base && strings.Contains(name, needle) {
				st.counts[i]++
			}
		}
	}
}

func isLoopvarRebind(txt string) bool {
	m := reVarDecl.FindStringSubmatch(txt)
	if m == nil {
		return false
	}
	rest := strings.TrimLeft(txt[len(m[0]):], " \t")
	if !strings.HasPrefix(rest, m[1]) {
		return false
	}

	if len(rest) > len(m[1]) {
		switch c := rest[len(m[1])]; {
		case c == '_', c >= 'a' && c <= 'z', c >= 'A' && c <= 'Z', c >= '0' && c <= '9':
			return false
		}
	}
	return true
}

func isAlpha(c byte) bool { return c >= 'a' && c <= 'z' || c >= 'A' && c <= 'Z' || c >= 0x80 }

func lastDot(s string) string {
	if i := strings.LastIndexByte(s, '.'); i >= 0 {
		return s[i+1:]
	}
	return s
}

func splitDot(s string) (string, bool) {
	if before, _, ok := strings.Cut(s, "."); ok {
		return before, true
	}
	return "", false
}

func inGoroutine(t *Tree, n int32) int32 {
	for p := t.nodes[n].parent; p != noNode; p = t.nodes[p].parent {
		switch t.nodes[p].kind {
		case kGoStmt:
			return 1
		case kFuncDecl, kMethodDecl, kFuncLit:
			return 0
		}
	}
	return 0
}

func (x *extractor) onString(t *Tree, n int32, text string, st *bodyStats, loopDepth int32) {
	val := strings.Trim(text, "\"'")
	if len(val) >= 12 && !strings.Contains(val, " ") && secrets.has(val) {
		st.secrets = append(st.secrets, pendingSecret{value: x.g.intern(trunc(val, 200)), line: t.nodes[n].line + 1})
	}
	if mayBeSQL(text) && reSQL.MatchString(text) {
		st.bumpName("n_sql_literal")
		if p := t.nodes[n].parent; p != noNode && t.nodes[p].kind == kBinaryExpr &&
			strings.Contains(trunc(t.text(p), 400), "+") {
			st.bumpName("n_sql_concat")
		}
		if loopDepth > 0 {
			st.bumpName("query_in_loop")
		}
	}
}

var onNodeKinds = func() [nodeKindCount]bool {
	var a [nodeKindCount]bool
	for _, k := range []NodeKind{kBinaryExpr, kUnaryExpr, kChanType, kCaseClauseComm,
		kIfStmt, kAssignStmt, kShortVarDecl, kReturnStmt, kCompositeLit, kCallExpr,
		kSelector, kTypeAssert, kRangeClause, kFieldDecl, kGoStmt, kDeferStmt} {
		a[k] = true
	}
	return a
}()

func (x *extractor) onNode(t *Tree, n int32, st *bodyStats, loopDepth, nest int32) {
	k := t.nodes[n].kind
	if !onNodeKinds[k] {
		return
	}
	switch k {
	case kBinaryExpr:
		op := t.child(n, fOperator)
		o := ""
		if op != noNode {
			o = t.text(op)
		}
		switch o {
		case "&&", "||":
			st.bumpName("n_logical")
			st.cyc++
		case "==", "!=", "<", ">", "<=", ">=":
			st.bumpName("n_cmp")
		case "&", "|", "^", "&^":
			st.bumpName("n_bitop")
		case "<<", ">>":
			st.bumpName("n_shift")
		case "+", "-", "*", "/", "%":
			st.bumpName("n_arith")
		}
	case kSelector:
		op := t.child(n, fOperand)
		fld := t.child(n, fSelectorField)
		if op == noNode || fld == noNode {
			return
		}
		o := strings.TrimSpace(t.text(op))
		f := strings.TrimSpace(t.text(fld))
		if !requestReceivers[o] {
			return
		}
		kind, ok := requestFieldKinds[f]
		if !ok {
			return
		}
		if f == "URL" {
			par := t.nodes[n].parent
			if par != noNode && t.nodes[par].kind == kCallExpr &&
				t.child(par, fFunction) == n {
				return
			}
		}
		st.inputs = append(st.inputs, pendingInput{
			vari: x.g.intern(trunc(t.text(n), 120)), kind: x.g.intern(kind),
			line: t.nodes[n].line + 1, inLoop: loopDepth > 0})
	case kCallExpr:
		txt := st.callRaw
		if st.callText != n {
			fn := t.child(n, fFunction)
			if fn == noNode {
				fn = n
			}
			txt = t.text(fn)
		}
		switch {
		case txt == "recover":
			st.bumpName("n_recover")
		case txt == "panic":
			st.bumpName("n_panics")
		case strings.HasPrefix(txt, "log.Fatal") || strings.HasPrefix(txt, "log.Panic"):
			st.bumpName("n_log_fatal")
		case txt == "close":
			st.bumpName("n_chan_close")
			if a := t.child(n, fArguments); a != noNode {
				if c := t.nodes[a].first; c != noNode {
					if cv := strings.TrimSpace(t.text(c)); cv != "" {
						st.closeVars = append(st.closeVars, trunc(cv, 80))
					}
				}
			}
		case txt == "make":
			a := t.child(n, fArguments)
			if a == noNode {
				return
			}
			kids := x.namedKids(t, a)
			atxt := t.text(a)
			switch {
			case strings.Contains(atxt, "chan") && len(kids) < 2:
				st.bumpName("n_chan_unbuffered")
			case strings.HasPrefix(atxt, "([]") && len(kids) < 3:
				st.bumpName("n_make_no_cap")
			}
			if strings.Contains(atxt, "chan") {
				st.extra = append(st.extra, pendingExtra{kind: 2, node: n})
			}
		case txt == "time.Tick":
			st.bumpName("n_time_tick")
		case strings.HasPrefix(txt, "context.Background") || strings.HasPrefix(txt, "context.TODO"):
			st.bumpName("n_ctx_background")
		case strings.HasPrefix(txt, "context.With"):
			st.bumpName("n_ctx_withcancel")
		case strings.HasSuffix(txt, ".Done"):
			st.bumpName("n_ctx_done")
		case strings.HasPrefix(txt, "fmt.Errorf"):
			if a := t.child(n, fArguments); a != noNode && strings.Contains(t.text(a), "%w") {
				st.bumpName("n_err_wrapped")
			}
		case strings.HasPrefix(txt, "unsafe."):
			st.bumpName("n_unsafe_ops")
		case strings.HasPrefix(txt, "C."):
			st.bumpName("n_cgo_calls")
		case strings.HasPrefix(txt, "reflect."):
			st.bumpName("n_reflect_ops")
		}
		if loopDepth > 0 && (strings.HasPrefix(txt, "string(") || strings.HasPrefix(txt, "[]byte")) {
			st.bumpName("n_conv_in_loop")
		}
	case kIfStmt:
		txt := trunc(t.text(n), 160)
		if strings.Contains(txt, "err") && reErrNilCheck.MatchString(txt) {
			st.bumpName("n_err_checks")
			if cons := t.child(n, fConsequence); cons != noNode {
				ctxt := trunc(t.text(cons), 200)
				if reReturnNil.MatchString(ctxt) && !reReturnNilErr.MatchString(ctxt) {
					st.bumpName("n_err_nil_return")
				}
			}
		}
		if strings.Contains(txt, "err") && reCommaErrAssign.MatchString(txt) {
			st.bumpName("n_err_shadowed")
		}
	case kAssignStmt, kShortVarDecl:
		txt := trunc(t.text(n), 200)
		if strings.Contains(txt, "_") && reBlankAssign.MatchString(txt) {
			st.bumpName("n_err_ignored")
		}
		if k == kShortVarDecl && isLoopvarRebind(txt) {
			st.bumpName("n_loopvar_rebind")
		}
	case kReturnStmt:

		if !t.hasNamed(n) {
			st.bumpName("n_naked_returns")
		} else if strings.Contains(strings.ToLower(t.text(n)), "err") {
			st.bumpName("n_err_returns")
		}
	case kUnaryExpr:

		if c := t.nodes[n].first; c != noNode && t.text(c) == "<-" {
			st.bumpName("n_chan_recv")
		}
	case kCompositeLit:
		ty := t.child(n, fType)
		if ty != noNode && strings.Contains(t.text(ty), "tls.Config") &&
			strings.Contains(trunc(t.text(n), 400), "InsecureSkipVerify") {
			st.bumpName("n_insecure_tls")
		}
	case kTypeAssert:
		p := t.nodes[n].parent
		if p == noNode {
			st.bumpName("n_type_assert_unchecked")
			return
		}
		switch t.nodes[p].kind {
		case kAssignStmt, kShortVarDecl, kExprList:
		default:
			st.bumpName("n_type_assert_unchecked")
		}
	case kFieldDecl:
		if strings.Contains(t.text(n), "`") {
			st.bumpName("n_struct_tags")
		}
	case kCaseClauseComm:
		txt := t.text(n)
		if strings.Contains(txt, "ctx.Done()") || strings.Contains(txt, ".Done()") {
			st.bumpName("n_select_ctx_done")
		}
	case kRangeClause:
		if loopDepth > 0 && reRangeCopy.MatchString(trunc(t.text(n), 120)) {
			st.bumpName("n_range_value_copy")
		}
	case kGoStmt:
		st.extra = append(st.extra, pendingExtra{kind: 0, node: n, depth: loopDepth})
	case kDeferStmt:
		st.extra = append(st.extra, pendingExtra{kind: 1, node: n, depth: loopDepth})
	}
}

func (t *Tree) hasNamed(n int32) bool {
	for c := t.nodes[n].first; c != noNode; c = t.nodes[c].next {
		if nodeNamed[t.nodes[c].kind] {
			return true
		}
	}
	return false
}

func (x *extractor) namedKids(t *Tree, n int32) []int32 {
	x.kids = x.kids[:0]
	for c := t.nodes[n].first; c != noNode; c = t.nodes[c].next {
		if nodeNamed[t.nodes[c].kind] {
			x.kids = append(x.kids, c)
		}
	}
	return x.kids
}

func (x *extractor) hazardOf(callee string) (string, string, bool) {
	if cat, ok := hazardCalls[callee]; ok {
		return callee, cat, true
	}
	if !strings.Contains(callee, ".") {
		return "", "", false
	}
	base := lastDot(callee)
	if cat, ok := hazardCalls[base]; ok {
		return "*." + base, cat, true
	}
	return "", "", false
}

func (x *extractor) isExternal(name, base string) bool {
	if builtins[base] && !strings.Contains(name, ".") {
		return true
	}
	head := name
	if i := strings.IndexByte(head, '.'); i >= 0 {
		head = head[:i]
	}

	r, _ := utf8.DecodeRuneInString(head)
	return stdlibRoots[head] || head == "C" ||
		(unicode.IsLower(r) && strings.Contains(name, ".") &&
			len(x.g.byName) > 0 && !x.hasName(head))
}

func (x *extractor) hasName(n string) bool { _, ok := x.g.byName[n]; return ok }

func estSize(tp string) int32 {
	tp = strings.TrimSpace(tp)
	if tp == "" {
		return 0
	}
	if strings.HasPrefix(tp, "*") || strings.HasPrefix(tp, "chan") ||
		strings.HasPrefix(tp, "func") || strings.HasPrefix(tp, "map[") {
		return 8
	}
	if strings.HasPrefix(tp, "[]") {
		return 24
	}
	if strings.HasPrefix(tp, "interface") || tp == "any" {
		return 16
	}
	if m := reArrayLen.FindStringSubmatch(tp); m != nil {
		if ln, ok := atoi(m[1]); ok {
			return ln * estSize(m[2])
		}
	}
	if w, ok := goSizes[tp]; ok {
		return w
	}
	return 8
}

var goSizes = map[string]int32{
	"bool": 1, "int8": 1, "uint8": 1, "byte": 1, "int16": 2, "uint16": 2,
	"int32": 4, "uint32": 4, "rune": 4, "float32": 4, "int": 8, "uint": 8,
	"int64": 8, "uint64": 8, "float64": 8, "uintptr": 8, "complex64": 8,
	"complex128": 16, "string": 16, "error": 16,
}

func (x *extractor) emitHazards(t *Tree, st *bodyStats, sid int32) {

	seen := make(map[string]int32, 8)
	for _, c := range st.calls {
		if c.name == nullStr {
			continue
		}
		nm := x.g.Str.get(c.name)
		pattern, cat, ok := x.hazardOf(nm)
		if !ok {
			continue
		}
		if _, dup := seen[pattern]; dup {
			x.bumpLastHazard(pattern, sid)
			continue
		}
		seen[pattern] = 1
		x.g.Hazards = append(x.g.Hazards, Hazard{
			SymbolID: sid, Pattern: x.g.intern(trunc(pattern, 120)),
			Category: x.g.intern(cat), N: 1, Line: c.line,
		})
	}
}

func (x *extractor) bumpLastHazard(pattern string, sid int32) {
	for i := len(x.g.Hazards) - 1; i >= 0; i-- {
		h := x.g.Hazards[i]
		if h.SymbolID != sid {
			return
		}
		if x.g.Str.get(h.Pattern) == pattern {
			x.g.Hazards[i].N++
			return
		}
	}
}

func (x *extractor) emitSatellites(t *Tree, st *bodyStats, sid int32) {
	g := x.g
	for _, w := range st.wgOps {
		g.WgSites = append(g.WgSites, WgSite{
			SymbolID: sid, FileID: x.file.FID, Line: w.line, Var: w.vari, Op: w.op,
			InGoroutine: w.inGo, InLoop: boolInt(w.inLoop),
		})
	}
	for _, e := range st.extra {
		switch e.kind {
		case 0:
			n := e.node

			inner := noNode
			for c := t.nodes[n].first; c != noNode; c = t.nodes[c].next {
				if nodeNamed[t.nodes[c].kind] {
					inner = c
					break
				}
			}
			target, closure, btxt := "", int32(0), ""
			if inner != noNode {
				if fn := t.child(inner, fFunction); fn != noNode {
					target = trunc(t.text(fn), 120)
					closure = boolInt(t.nodes[fn].kind == kFuncLit)
				}
				btxt = t.text(inner)
			}
			g.Goro = append(g.Goro, Goro{
				SymbolID: sid, FileID: x.file.FID, Line: t.nodes[n].line + 1,
				IsClosure: closure, Target: g.intern(target),
				HasCtx:     boolInt(strings.Contains(btxt, ".Done()") || strings.Contains(btxt, "ctx.")),
				HasRecover: boolInt(strings.Contains(btxt, "recover(")),
				HasWG: boolInt(strings.Contains(btxt, ".Done()") && strings.Contains(btxt, "wg.") ||
					strings.Contains(btxt, "wg.Done") || strings.Contains(btxt, "WaitGroup")),
				HasEG:    boolInt(strings.Contains(btxt, "errgroup") || strings.Contains(btxt, "g.Go(")),
				ChanExit: boolInt(strings.Contains(btxt, "<-")),
				InLoop:   boolInt(e.depth > 0), LoopDepth: e.depth,
				BodySloc: int32(strings.Count(btxt, "\n") + 1),
			})

			for _, mm := range reWgOp.FindAllStringSubmatch(btxt, -1) {
				if mm[1] == "ctx" {
					continue
				}
				g.WgSites = append(g.WgSites, WgSite{
					SymbolID: sid, FileID: x.file.FID, Line: t.nodes[n].line + 1,
					Var: g.intern(mm[1]), Op: g.intern(mm[2]), InGoroutine: 1,
					InLoop: boolInt(e.depth > 0),
				})
			}
		case 1:
			dtxt := trunc(t.text(e.node), 160)
			g.Defers = append(g.Defers, Defer{
				SymbolID: sid, Line: t.nodes[e.node].line + 1, Target: g.intern(trunc(dtxt, 120)),
				InLoop: boolInt(e.depth > 0), LoopDepth: e.depth,
				IsClose:  boolInt(strings.Contains(dtxt, ".Close()")),
				IsUnlock: boolInt(strings.Contains(dtxt, ".Unlock()") || strings.Contains(dtxt, ".RUnlock()")),
				IsDone:   boolInt(strings.Contains(dtxt, ".Done()")),
			})
		case 2:
			n := e.node
			a := t.child(n, fArguments)
			kids := x.namedKids(t, a)
			capacity := int32(0)
			if len(kids) > 1 {
				ct := strings.TrimSpace(t.text(kids[1]))
				if v, ok := atoi(ct); ok {
					capacity = v
				} else {
					capacity = -1
				}
			}
			nm := ""
			if p := t.nodes[n].parent; p != noNode {
				switch t.nodes[p].kind {
				case kAssignStmt, kShortVarDecl:
					if l := t.child(p, fLeft); l != noNode {
						nm = trunc(strings.TrimSpace(t.text(l)), 80)
					}
				}
			}
			elem := ""
			if len(kids) > 0 {
				elem = trunc(t.text(kids[0]), 80)
			}
			closed := int32(0)
			if nm != "" {
				if slices.Contains(st.closeVars, nm) {
					closed = 1
				}
			}
			g.Chans = append(g.Chans, Chan{
				SymbolID: sid, FileID: x.file.FID, Name: g.intern(nm), ElemType: g.intern(elem),
				Capacity: capacity, Line: t.nodes[n].line + 1, ClosedInFn: closed,
			})
		}
	}
	for _, in := range st.inputs {
		g.UInput = append(g.UInput, UInput{
			SymbolID: sid, FileID: x.file.FID, Var: in.vari, Kind: in.kind,
			Line: in.line, InLoop: boolInt(in.inLoop),
		})
	}
	for _, s := range st.secrets {
		g.Secret = append(g.Secret, Secret{SymbolID: sid, FileID: x.file.FID, Value: s.value, Line: s.line})
	}
	for _, l := range st.literals {
		g.Literals = append(g.Literals, Literal{
			SymbolID: sid, FileID: x.file.FID, Kind: l.kind, Value: l.value,
			Line: l.line, Magic: boolInt(l.magic),
		})
	}
}

func (x *extractor) typeSatellites(t *Tree, n int32, sid int32) {
	g := x.g
	nm := x.nodeName(t, n)
	ty := t.child(n, fType)
	if ty == noNode {
		return
	}
	switch t.nodes[ty].kind {
	case kInterfaceType:
		var nMeth, nEmb int32
		var names []string
		for c := t.nodes[ty].first; c != noNode; c = t.nodes[c].next {
			switch t.nodes[c].kind {
			case kMethodElem:
				nMeth++
				names = append(names, x.nodeName(t, c))
			case kTypeElem:
				nEmb++
			}
		}
		txt := t.text(ty)
		g.Iface = append(g.Iface, Iface{
			SymbolID: sid, NMethods: nMeth, NEmbedded: nEmb,

			Exported:   boolInt(nm != "" && unicode.IsUpper(firstRune(nm))),
			Constraint: boolInt(strings.Contains(txt, "|") || strings.Contains(txt, "~")),
			Methods:    g.intern(trunc(strings.Join(names, ","), 400)),
		})
	case kStructType:

		txt := t.text(ty)
		g.Structs = append(g.Structs, Struct{
			SymbolID: sid,
			HasMutex: boolInt(strings.Contains(txt, "sync.Mutex") || strings.Contains(txt, "sync.RWMutex")),
			HasCtx:   boolInt(strings.Contains(txt, "context.Context")),
		})
	}
}

const internerShardBits = 8

const internerShards = 1 << internerShardBits

type internShard struct {
	mu  sync.RWMutex
	buf []byte
	off []uint32
	ln  []uint32
	idx map[string]uint32

	strs  []string
	built bool
}

type Interner struct {
	shards [internerShards]internShard
	null   uint32
}

const nullStr = ^uint32(0)

func NewInterner() *Interner {
	it := &Interner{}
	for i := range it.shards {
		it.shards[i].idx = make(map[string]uint32, 64)
	}
	it.null = it.intern("\x00null")
	return it
}

func shardOf(s string) uint32 {

	var h uint32 = 2166136261
	for i := 0; i < len(s); i++ {
		h ^= uint32(s[i])
		h *= 16777619
	}
	return (h >> (32 - internerShardBits)) & (internerShards - 1)
}

func (it *Interner) intern(s string) uint32 {
	sh := shardOf(s)
	c := &it.shards[sh]
	c.mu.Lock()
	if id, ok := c.idx[s]; ok {
		c.mu.Unlock()
		return id
	}
	local := uint32(len(c.ln))
	if local >= 1<<(32-internerShardBits) {
		c.mu.Unlock()
		panic("interner: shard overflow")
	}
	c.off = append(c.off, uint32(len(c.buf)))
	c.ln = append(c.ln, uint32(len(s)))
	c.buf = append(c.buf, s...)
	id := sh<<(32-internerShardBits) | local
	c.idx[s] = id
	if c.built {
		c.strs = append(c.strs, s)
	}
	c.mu.Unlock()
	return id
}

func (it *Interner) buildStrings() {
	for i := range it.shards {
		c := &it.shards[i]
		c.mu.Lock()
		if !c.built {
			c.strs = make([]string, len(c.ln))
			for j := range c.ln {
				c.strs[j] = string(c.buf[c.off[j] : c.off[j]+c.ln[j]])
			}
			c.built = true
		}
		c.mu.Unlock()
	}
}

func (it *Interner) get(id uint32) string {
	if id == it.null {
		return ""
	}
	c := &it.shards[id>>(32-internerShardBits)]
	local := id & (1<<(32-internerShardBits) - 1)
	c.mu.RLock()
	var s string
	if c.built {
		s = c.strs[local]
	} else {
		s = string(c.buf[c.off[local] : c.off[local]+c.ln[local]])
	}
	c.mu.RUnlock()
	return s
}

func (it *Interner) lookup(s string) (uint32, bool) {
	c := &it.shards[shardOf(s)]
	c.mu.RLock()
	id, ok := c.idx[s]
	c.mu.RUnlock()
	return id, ok
}

type CSR[T any] struct {
	off []int32
	idx []int32
	val []T
}

func BuildCSR[T any](nkeys int32, keys []int32, out []T) CSR[T] {
	c := CSR[T]{off: make([]int32, nkeys+1)}
	for _, k := range keys {
		c.off[k+1]++
	}
	for i := range nkeys {
		c.off[i+1] += c.off[i]
	}
	c.idx = make([]int32, len(keys))
	c.val = make([]T, len(out))
	fill := make([]int32, nkeys)
	copy(fill, c.off[:nkeys])
	for i, k := range keys {
		at := fill[k]
		fill[k]++
		c.idx[at] = int32(i)
		c.val[at] = out[i]
	}
	return c
}

func (c CSR[T]) row(k int32) (int32, int32) { return c.off[k], c.off[k+1] }
func (c CSR[T]) count(k int32) int32        { return c.off[k+1] - c.off[k] }

type File struct {
	Path      string
	Dir       string
	Basename  string
	Ext       string
	ModuleID  int32
	Bytes     int32
	Lines     int32
	Sloc      int32
	Blank     int32
	Comment   int32
	DocLines  int32
	MaxLine   int32
	SHA1      string
	Parsed    int32
	IsTest    int32
	IsGen     int32
	IsVend    int32
	NParsErr  int32
	NMissing  int32
	ParseMS   float64
	NSymbols  int32
	NFuncs    int32
	NTypes    int32
	NImports  int32
	TotalCyc  int32
	MaxCyc    int32
	TotalRisk int32
}

type Module struct {
	Name    string
	Kind    string
	NFiles  int32
	NSyms   int32
	NPublic int32
	Sloc    int32
	FanIn   int32
	FanOut  int32
	Instab  float64
	Depth   int32
	NDirect int32
	NTrans  int32
	HasDep  bool
}

type Edge struct {
	Callee   int32
	NCalls   int32
	SameFile int32
	SameMod  int32
	IsSelf   int32
}

type CallGraph struct {
	Out CSR[Edge]
	In  CSR[Edge]

	scr reachScratch
}

type reachScratch struct {
	dist     []int32
	gen      []uint32
	cur      uint32
	frontier []int32
	next     []int32
}

type reachDist struct {
	d   []int32
	gen []uint32
	cur uint32
}

func (r reachDist) at(sym int32) int32 {
	if r.gen[sym] == r.cur {
		return r.d[sym]
	}
	return -1
}

func (cg *CallGraph) reach(root, maxDepth int32) reachDist {
	s := &cg.scr
	n := int32(len(cg.Out.off) - 1)
	if int32(len(s.dist)) != n {
		s.dist = make([]int32, n)
		s.gen = make([]uint32, n)
		s.frontier = make([]int32, 0, 64)
		s.next = make([]int32, 0, 64)
		s.cur = 0
	}
	s.cur++
	if s.cur == 0 {
		for i := range s.gen {
			s.gen[i] = 0
		}
		s.cur = 1
	}
	cur := s.cur
	dist, gen := s.dist, s.gen
	dist[root] = 0
	gen[root] = cur
	s.frontier = append(s.frontier[:0], root)
	frontier := s.frontier
	for d := int32(0); d < maxDepth && len(frontier) > 0; d++ {
		s.next = s.next[:0]
		for _, sym := range frontier {
			lo, hi := cg.Out.row(sym)
			for p := lo; p < hi; p++ {
				e := &cg.Out.val[p]
				if e.IsSelf != 0 {
					continue
				}
				c := e.Callee
				if gen[c] == cur {
					continue
				}
				gen[c] = cur
				dist[c] = d + 1
				s.next = append(s.next, c)
			}
		}
		frontier, s.next = s.next, frontier[:0]
	}
	s.frontier = frontier[:0]
	return reachDist{d: dist, gen: gen, cur: cur}
}

type Graph struct {
	Sym  Syms
	Str  *Interner
	File []File
	Mod  []Module

	Calls CallGraph

	Params   []Param
	Fields   []Field
	Hazards  []Hazard
	Imports  []Import
	Literals []Literal
	Markers  []Marker
	Goro     []Goro
	Defers   []Defer
	Chans    []Chan
	Iface    []Iface
	Structs  []Struct
	WgSites  []WgSite
	UInput   []UInput
	Secret   []Secret
	Impl     []Impl
	BuildTag []BuildTag
	ErrChain []ErrChain

	paramsCSR CSR[int32]
	fieldsCSR CSR[int32]
	hazCSR    CSR[int32]
	goroCSR   CSR[int32]
	deferCSR  CSR[int32]
	chanCSR   CSR[int32]
	ifaceCSR  CSR[int32]
	structCSR CSR[int32]
	wgCSR     CSR[int32]
	uinputCSR CSR[int32]
	secretCSR CSR[int32]
	litCSR    CSR[int32]
	markerCSR CSR[int32]
	implCSR   CSR[int32]
	unresCSR  CSR[int32]
	csCSR     CSR[int32]

	symTypeName []string
	byName      map[string][]int32
	tgtIdx      map[string][]int32
	fileOf      []int32
	modOf       []int32

	Meta map[string]string

	ParseMode string
	Parser    string
	SQLite    string

	pSid  []int32
	pFid  []int32
	pMid  []int32
	pLine []int32
	pName []uint32
	pType []uint32

	edgeList  []rawEdge
	unresList []Unres
	csList    []Callsite

	paramsSym []int32
	fieldsSym []int32

	nExternal  int32
	nResolved  int32
	nUnresolvd int32
	extByCall  map[int32]int32
	modAccs    map[int32]*modAcc

	astBlob []byte
}

func (g *Graph) intern(s string) uint32 { return g.Str.intern(s) }

func NewGraph() *Graph {
	return &Graph{
		Str:         NewInterner(),
		byName:      make(map[string][]int32, 1<<12),
		symTypeName: make([]string, 0, 1<<12),
		Meta:        make(map[string]string, 20),
		extByCall:   make(map[int32]int32),
	}
}

type Param struct {
	sym      int32
	Pos      int32
	Name     uint32
	Typ      uint32
	Default  uint32
	Opt      int32
	Variadic int32
	Ref      int32
	Mutable  int32
	Nullable int32
	Generic  int32
	Untyped  int32
	Depth    int32
}

type Field struct {
	Ordinal    int32
	Name       uint32
	Typ        uint32
	Visibility uint32
	Line       int32
	Static     int32
	Const      int32
	Mutable    int32
	Nullable   int32
	Collection int32
	Untyped    int32
	HasDefault int32
	Depth      int32
}

type Hazard struct {
	SymbolID int32
	Pattern  uint32
	Category uint32
	N        int32
	Line     int32
}

type Import struct {
	FileID   int32
	Target   uint32
	TargetID int32
	Alias    uint32
	Kind     uint32
	Line     int32
	External int32
	Relative int32
	Wildcard int32
	TypeOnly int32
	Dynamic  int32
	NNames   int32
}

type Literal struct {
	SymbolID int32
	FileID   int32
	Kind     uint32
	Value    uint32
	Line     int32
	Magic    int32
}

type Marker struct {
	FileID   int32
	SymbolID int32
	Kind     uint32
	Line     int32
	Text     uint32
}

type Goro struct {
	SymbolID   int32
	FileID     int32
	Line       int32
	IsClosure  int32
	Target     uint32
	HasCtx     int32
	HasRecover int32
	HasWG      int32
	HasEG      int32
	ChanExit   int32
	InLoop     int32
	LoopDepth  int32
	BodySloc   int32
}

type Defer struct {
	SymbolID  int32
	Line      int32
	Target    uint32
	InLoop    int32
	LoopDepth int32
	IsClose   int32
	IsUnlock  int32
	IsDone    int32
}

type Chan struct {
	SymbolID   int32
	FileID     int32
	Name       uint32
	ElemType   uint32
	Capacity   int32
	Line       int32
	ClosedInFn int32
}

type Iface struct {
	SymbolID   int32
	NMethods   int32
	NEmbedded  int32
	Exported   int32
	Constraint int32
	Methods    uint32
}

type Struct struct {
	SymbolID  int32
	NFields   int32
	NEmbedded int32
	NExported int32
	EstSize   int32
	EstPad    int32
	SizeExact int32
	HasMutex  int32
	HasCtx    int32
	NTagged   int32
}

type WgSite struct {
	SymbolID    int32
	FileID      int32
	Line        int32
	Var         uint32
	Op          uint32
	InGoroutine int32
	InLoop      int32
}

type UInput struct {
	SymbolID int32
	FileID   int32
	Var      uint32
	Kind     uint32
	Line     int32
	InLoop   int32
}

type Secret struct {
	SymbolID int32
	FileID   int32
	Value    uint32
	Line     int32
}

type Impl struct {
	TypeName     uint32
	InterfaceID  int32
	InterfaceNam uint32
	NMethods     int32
	InTest       int32
}

type BuildTag struct {
	FileID int32
	Expr   uint32
	Line   int32
}

type rawEdge struct {
	Caller, Callee   int32
	NCalls, SameFile int32
	SameMod, IsSelf  int32
}

type Unres struct {
	Caller int32
	Name   uint32
	N      int32
	Line   int32
}

type Callsite struct {
	Caller, Callee, Line int32
}

type ErrChain struct {
	SymbolID int32
	MaxDepth int32
}

func (g *Graph) buildCSRs() {
	n := int32(g.Sym.n)
	g.buildLoc()
	g.paramsCSR = csrByOwner(n, g.Params, func(i int) int32 { return g.paramsSym[i] })
	g.fieldsCSR = csrByOwner(n, g.Fields, func(i int) int32 { return g.fieldsSym[i] })
	g.hazCSR = csrByOwner(n, g.Hazards, func(i int) int32 { return g.Hazards[i].SymbolID })
	g.goroCSR = csrByOwner(n, g.Goro, func(i int) int32 { return g.Goro[i].SymbolID })
	g.deferCSR = csrByOwner(n, g.Defers, func(i int) int32 { return g.Defers[i].SymbolID })
	g.chanCSR = csrByOwner(n, g.Chans, func(i int) int32 { return g.Chans[i].SymbolID })
	g.ifaceCSR = csrByOwner(n, g.Iface, func(i int) int32 { return g.Iface[i].SymbolID })
	g.structCSR = csrByOwner(n, g.Structs, func(i int) int32 { return g.Structs[i].SymbolID })
	g.wgCSR = csrByOwner(n, g.WgSites, func(i int) int32 { return g.WgSites[i].SymbolID })
	g.uinputCSR = csrByOwner(n, g.UInput, func(i int) int32 { return g.UInput[i].SymbolID })
	g.secretCSR = csrByOwner(n, g.Secret, func(i int) int32 { return g.Secret[i].SymbolID })
	g.litCSR = csrByOwner(n, g.Literals, func(i int) int32 { return g.Literals[i].SymbolID })
	g.markerCSR = csrByOwner(n, g.Markers, func(i int) int32 { return g.Markers[i].SymbolID })
	g.implCSR = csrByOwner(n, g.Impl, func(i int) int32 { return g.Impl[i].InterfaceID })
	g.unresCSR = csrByOwner(n, g.unresList, func(i int) int32 { return g.unresList[i].Caller })
	g.csCSR = csrByOwner(n, g.csList, func(i int) int32 { return g.csList[i].Callee })

	m := len(g.edgeList)
	keys := make([]int32, m)
	vals := make([]Edge, m)
	for i, e := range g.edgeList {
		keys[i] = e.Caller
		vals[i] = Edge{Callee: e.Callee, NCalls: e.NCalls, SameFile: e.SameFile,
			SameMod: e.SameMod, IsSelf: e.IsSelf}
	}
	g.Calls.Out = BuildCSR(n, keys, vals)
	for i, e := range g.edgeList {
		keys[i] = e.Callee
		vals[i] = Edge{Callee: e.Caller, NCalls: e.NCalls, SameFile: e.SameFile,
			SameMod: e.SameMod, IsSelf: e.IsSelf}
	}
	g.Calls.In = BuildCSR(n, keys, vals)
}

func (g *Graph) buildLoc() {
	n := int32(g.Sym.n)
	g.fileOf = make([]int32, n)
	g.modOf = make([]int32, n)
	for i := 0; i < int(n); i++ {
		g.fileOf[i] = g.Sym.FileId[i]
		g.modOf[i] = g.Sym.ModuleId[i]
	}
}

func csrByOwner[T any](n int32, rows []T, owner func(int) int32) CSR[int32] {
	keys := make([]int32, len(rows))
	idx := make([]int32, len(rows))
	for i := range rows {
		o := owner(i)
		if o < 0 || o >= n {
			o = 0
		}
		keys[i] = o
		idx[i] = int32(i)
	}
	return BuildCSR(n, keys, idx)
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
	"site-packages": true, "testdata": true,
}

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
	if head[0] == "src" || head[0] == "lib" || head[0] == "source" ||
		head[0] == "internal" || head[0] == "pkg" || head[0] == "app" {
		if len(head) > 3 {
			head = head[:3]
		}
	} else if len(head) > 2 {
		head = head[:2]
	}
	if len(head) == 0 {
		return "(root)"
	}
	return strings.Join(head, "/")
}

var (
	reExampleMod = regexp.MustCompile(`(?i)(^|/)(examples?|samples?|demos?)(/|$)`)
	reToolMod    = regexp.MustCompile(`(?i)(^|/)(tools?|scripts?|cmd|bin)(/|$)`)
)

func moduleKind(name string) string {
	switch {
	case reTestPath.MatchString(name):
		return "test"
	case reVendPath.MatchString(name):
		return "vendor"
	case reExampleMod.MatchString(name):
		return "example"
	case reToolMod.MatchString(name):
		return "tool"
	}
	return "source"
}

func isGeneratedName(name, head string) bool {
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

type discoverStats struct {
	seen, big, special, escape, denied, walkErr int
}

func discover(g *Graph, root string, includeTests, includeGen, includeVend bool) ([]FileRec, discoverStats) {
	var st discoverStats
	modID := map[string]int32{}
	realRoot, _ := filepath.EvalSymlinks(root)
	var recs []FileRec
	var paths []string

	var walk func(dir string)
	walk = func(dir string) {
		ents, err := os.ReadDir(dir)
		if err != nil {
			st.walkErr++
			return
		}
		sort.Slice(ents, func(a, b int) bool { return ents[a].Name() < ents[b].Name() })
		var subdirs []string
		for _, e := range ents {
			name := e.Name()
			if !e.IsDir() {
				continue
			}
			if skipDirs[name] || strings.HasPrefix(name, ".") {
				continue
			}
			subdirs = append(subdirs, name)
		}
		for _, e := range ents {
			if e.IsDir() || filepath.Ext(e.Name()) != ".go" {
				continue
			}
			paths = append(paths, filepath.Join(dir, e.Name()))
		}
		for _, d := range subdirs {
			walk(filepath.Join(dir, d))
		}
	}
	walk(root)
	an := make([]discFile, len(paths))
	dc := &dirCache{m: map[string]string{}}
	aw := runtime.GOMAXPROCS(0)
	if aw > len(paths) {
		aw = len(paths)
	}
	if aw > 1 {
		var nextA atomic.Int64
		var awg sync.WaitGroup
		awg.Add(aw)
		for k := 0; k < aw; k++ {
			go func() {
				defer awg.Done()
				for {
					i := int(nextA.Add(1)) - 1
					if i >= len(paths) {
						return
					}
					discAnalyze(paths[i], root, realRoot, dc, &an[i])
				}
			}()
		}
		awg.Wait()
	} else {
		for i := range paths {
			discAnalyze(paths[i], root, realRoot, dc, &an[i])
		}
	}
	for i := range paths {
		d := &an[i]
		st.seen++
		switch d.kind {
		case discDenied:
			st.denied++
			continue
		case discSpecial:
			st.special++
			continue
		case discEscape:
			st.escape++
			continue
		case discBig:
			st.big++
		}
		mname := moduleOf(d.rel)
		mid, ok := modID[mname]
		if !ok {
			mid = int32(len(g.Mod))
			g.Mod = append(g.Mod, Module{Name: mname, Kind: moduleKind(mname)})
			modID[mname] = mid
		}
		parse := d.kind != discBig && len(d.text) != 0 &&
			(includeTests || !d.test) && (includeGen || !d.gen) && (includeVend || !d.vend)
		g.File = append(g.File, File{
			Path: d.rel, Dir: dirOf(d.rel), Basename: filepath.Base(d.rel), Ext: ".go",
			ModuleID: mid, Bytes: d.bytes, Lines: d.lines,
			Sloc: d.sloc, Blank: d.blank, Comment: d.cmt, MaxLine: d.maxLn, SHA1: d.sum,
			Parsed: boolInt(parse), IsTest: boolInt(d.test), IsGen: boolInt(d.gen),
			IsVend: boolInt(d.vend),
		})
		if parse {
			recs = append(recs, FileRec{
				FID: int32(len(g.File) - 1), MID: mid, Rel: d.rel, Abs: paths[i],
				Text: d.text, Lang: "go", IsTest: d.test, IsGen: d.gen, IsVend: d.vend,
			})
		}
	}
	return recs, st
}

const (
	discOK = iota
	discDenied
	discSpecial
	discEscape
	discBig
)

type discFile struct {
	rel   string
	text  []byte
	sum   string
	sloc  int32
	blank int32
	cmt   int32
	maxLn int32
	lines int32
	bytes int32
	kind  byte
	test  bool
	gen   bool
	vend  bool
}

type dirCache struct {
	mu sync.Mutex
	m  map[string]string
}

func (dc *dirCache) resolve(dir string) string {
	dc.mu.Lock()
	r, ok := dc.m[dir]
	dc.mu.Unlock()
	if ok {
		return r
	}
	r, _ = filepath.EvalSymlinks(dir)
	dc.mu.Lock()
	dc.m[dir] = r
	dc.mu.Unlock()
	return r
}

func discAnalyze(full, root, realRoot string, dc *dirCache, d *discFile) {
	rel, _ := filepath.Rel(root, full)
	d.rel = filepath.ToSlash(rel)
	info, err := os.Lstat(full)
	if err != nil {
		d.kind = discDenied
		return
	}
	var rp string
	if info.Mode()&fs.ModeSymlink != 0 {
		info, err = os.Stat(full)
		if err != nil {
			d.kind = discDenied
			return
		}
		if !info.Mode().IsRegular() {
			d.kind = discSpecial
			return
		}
		rp, _ = filepath.EvalSymlinks(full)
	} else {
		if !info.Mode().IsRegular() {
			d.kind = discSpecial
			return
		}
		rp = dc.resolve(filepath.Dir(full))
		if rp != "" {
			rp += string(filepath.Separator) + filepath.Base(full)
		}
	}
	if rp != full && realRoot != "" && !strings.HasPrefix(rp, realRoot+string(filepath.Separator)) {
		d.kind = discEscape
		return
	}
	var data []byte
	if info.Size() > maxFileBytes {
		d.kind = discBig
		return
	}
	data, err = os.ReadFile(full)
	if err != nil {
		d.kind = discDenied
		return
	}
	if len(data) > 0 {
		longest := 0
		cur := 0
		for _, c := range data {
			if c == '\n' {
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
		if longest > maxLineBytes {
			d.kind = discBig
			return
		}
	}
	text := unsafe.String(unsafe.SliceData(data), len(data))
	lines := splitLines(text)
	var sloc, blank, cmt, maxLine int32
	for _, l := range lines {
		if strings.TrimSpace(l) == "" {
			blank++
		} else {
			sloc++
			tp := strings.TrimLeftFunc(l, unicode.IsSpace)
			if len(tp) >= 3 {
				tp = tp[:3]
			}
			if slices.Contains(discoverCommentPrefixes, tp) {
				cmt++
			}
		}
		if n := int32(utf8.RuneCountInString(l)); n > maxLine {
			maxLine = n
		}
	}
	d.text = data
	d.bytes = int32(len(data))
	d.lines = int32(len(lines))
	d.sloc, d.blank, d.cmt, d.maxLn = sloc, blank, cmt, maxLine
	if len(data) > 0 {
		s := sha1.Sum(data)
		d.sum = hex.EncodeToString(s[:])
	}
	d.test = reTestPath.MatchString(d.rel) || reTestNameGo.MatchString(filepath.Base(d.rel))
	d.gen = isGeneratedName(filepath.Base(d.rel), text[:min(2000, len(text))])
	d.vend = reVendPath.MatchString(d.rel)
}

var discoverCommentPrefixes = []string{"//", "#", "/*", "*", "*/", `"""`, "'''", "--", ";;", "%"}

func splitLines(s string) []string {
	if s == "" {
		return nil
	}
	out := make([]string, 0, len(s)/24+8)
	start := 0
	for i, r := range s {
		switch r {
		case '\n', '\r', '\v', '\f', 0x1c, 0x1d, 0x1e, 0x85, 0x2028, 0x2029:
		default:
			continue
		}
		if i < start {
			continue
		}
		out = append(out, s[start:i])
		n := utf8.RuneLen(r)
		if r == '\r' && i+n < len(s) && s[i+n] == '\n' {
			n++
		}
		start = i + n
	}
	if start < len(s) {
		out = append(out, s[start:])
	}
	return out
}

func dirOf(rel string) string {
	if i := strings.LastIndexByte(rel, '/'); i >= 0 {
		return rel[:i]
	}
	return "."
}

func parseFile(g *Graph, rec FileRec) error {
	fset := token.NewFileSet()
	f, err := parser.ParseFile(fset, rec.Abs, rec.Text,
		parser.ParseComments|parser.AllErrors|parser.SkipObjectResolution)

	if el, ok := err.(scanner.ErrorList); ok && len(el) > 0 {
		g.File[rec.FID].NParsErr = int32(len(el))
	} else if err != nil && f != nil {
		g.File[rec.FID].NParsErr = 1
	}
	if err != nil && f == nil {
		return err
	}
	tf := tokenFileFor(fset, f, rec.Abs, len(rec.Text))
	t := buildTree(tf, rec.Text, f)
	st := statsPool.Get().(*bodyStats)
	st.reset()
	x := &extractor{g: g, file: &rec, tree: t, stats: st}
	x.scanMarkers()
	x.parseImports(t)
	x.walkScope(t, t.root, scope{symID: noNode})
	x.parseFileExtras(t, rec)
	statsPool.Put(st)
	return nil
}

var statsPool = sync.Pool{New: func() any { return newBodyStats() }}

func tokenFileFor(fset *token.FileSet, f *ast.File, name string, size int) *token.File {
	if tf := fset.File(f.Pos()); tf != nil {
		return tf
	}
	var tf *token.File
	ast.Inspect(f, func(n ast.Node) bool {
		if tf != nil || n == nil {
			return false
		}
		tf = fset.File(n.Pos())
		return tf == nil
	})
	if tf == nil {
		tf = fset.AddFile(name, fset.Base(), size)
	}
	return tf
}

const segFiles = 64

type segment struct {
	g *Graph

	idx     []int32
	symN    int32
	types   int32
	sat     [nSat]int32
	counted bool
}

type fileRange struct {
	seg            *segment
	symStart, symN int32
	typeStart      int32
	sat            [nSat][2]int32
}

func extractAll(g *Graph, recs []FileRec, w int) int {
	if w < 1 {
		w = 1
	}
	if w > len(recs) {
		w = len(recs)
	}
	if w <= 1 {
		nErr := 0
		for i := range recs {
			if err := parseFile(g, recs[i]); err != nil {
				nErr++
				g.File[recs[i].FID].Parsed = 0
			}
			recs[i].Text = nil
		}
		rebuildNameScopes(g)
		return nErr
	}

	pub := make([]fileRange, len(recs))
	ready := make([]chan struct{}, len(recs))
	for i := range ready {
		ready[i] = make(chan struct{})
	}
	var next atomic.Int64
	var nFailed atomic.Int32

	sem := newByteWindow(parseByteBudget)
	var wg sync.WaitGroup
	wg.Add(w)
	for k := 0; k < w; k++ {
		go func() {
			defer wg.Done()
			var seg *segment
			var nIn int32
			for {
				i := int(next.Add(1)) - 1
				if i >= len(recs) {
					break
				}
				if seg == nil {
					seg = &segment{g: newSink(g), idx: make([]int32, 0, segFiles)}
					reserveSyms(&seg.g.Sym, segFiles*12)
					nIn = 0
				}
				s := seg.g
				pre := satLens(s)
				preTypes := int32(len(s.symTypeName))
				before := int32(s.Sym.n)

				sz := fileCharge(int64(len(recs[i].Text)))
				sem.take(sz)
				if err := parseFile(s, recs[i]); err != nil {
					nFailed.Add(1)
					g.File[recs[i].FID].Parsed = 0
				}
				recs[i].Text = nil

				sem.give(sz)

				post := satLens(s)
				r := &pub[i]
				r.seg = seg
				r.symStart = before
				r.symN = int32(s.Sym.n) - before
				r.typeStart = preTypes
				for k := range nSat {
					r.sat[k] = [2]int32{pre[k], post[k] - pre[k]}
				}
				nIn++
				seg.idx = append(seg.idx, int32(i))
				if nIn >= segFiles {
					seal(seg, ready)
					seg, nIn = nil, 0
				}
			}

			if seg != nil {
				seal(seg, ready)
			}
		}()
	}

	var runSym, runTypes int32
	var runSat [nSat]int32
	for i := range recs {
		<-ready[i]
		r := &pub[i]
		sg := r.seg
		if !sg.counted {
			sg.counted = true
			runSym += sg.symN
			runTypes += sg.types
			for k := range nSat {
				runSat[k] += sg.sat[k]
			}
			reserveRoom(g, runSym, runTypes, runSat)
		}
		mergeRange(g, sg.g, *r)

		r.seg = nil
	}
	wg.Wait()
	rebuildNameScopes(g)
	return int(nFailed.Load())
}

func rebuildNameScopes(g *Graph) {
	byName := make(map[string][]int32, len(g.byName))
	for i := 0; i < g.Sym.n; i++ {
		name := g.Str.get(g.Sym.Name[i])
		byName[name] = append(byName[name], int32(i))
	}
	g.byName = byName
}

func seal(seg *segment, ready []chan struct{}) {
	seg.symN = int32(seg.g.Sym.n)
	seg.types = int32(len(seg.g.symTypeName))
	tot := satLens(seg.g)
	for k := range nSat {
		seg.sat[k] = tot[k]
	}
	for _, i := range seg.idx {
		close(ready[i])
	}
}

const nSat = 21

func reserveSyms(s *Syms, n int) {
	d := reflect.ValueOf(s).Elem()
	for _, f := range symSliceFields {
		fv := d.Field(f)
		if c := fv.Cap(); c < n {
			grown := reflect.MakeSlice(fv.Type(), fv.Len(), n)
			reflect.Copy(grown, fv)
			fv.Set(grown)
		}
	}
}

func reserveRoom(dst *Graph, symN, types int32, sat [nSat]int32) {
	d := reflect.ValueOf(&dst.Sym).Elem()
	for _, f := range symSliceFields {
		fv := d.Field(f)
		if c := fv.Cap(); c < int(symN) {
			grow := max(int(symN)+c/2, 64)
			grown := reflect.MakeSlice(fv.Type(), fv.Len(), grow)
			reflect.Copy(grown, fv)
			fv.Set(grown)
		}
	}
	reserveTo(&dst.Markers, sat[0])
	reserveTo(&dst.Imports, sat[1])
	reserveTo(&dst.BuildTag, sat[2])
	reserveTo(&dst.Hazards, sat[3])
	reserveTo(&dst.WgSites, sat[4])
	reserveTo(&dst.Goro, sat[5])
	reserveTo(&dst.Defers, sat[6])
	reserveTo(&dst.Chans, sat[7])
	reserveTo(&dst.UInput, sat[8])
	reserveTo(&dst.Secret, sat[9])
	reserveTo(&dst.Literals, sat[10])
	reserveTo(&dst.Iface, sat[11])
	reserveTo(&dst.Structs, sat[12])
	reserveTo(&dst.Params, sat[13])
	reserveTo(&dst.paramsSym, sat[14])
	reserveTo(&dst.pSid, sat[15])
	reserveTo(&dst.pFid, sat[15])
	reserveTo(&dst.pMid, sat[15])
	reserveTo(&dst.pLine, sat[15])
	reserveTo(&dst.pName, sat[15])
	reserveTo(&dst.pType, sat[15])
	reserveTo(&dst.symTypeName, types)
}

func reserveTo[T any](p *[]T, n int32) {
	if cap(*p) >= int(n) {
		return
	}
	grow := max(int(n)+cap(*p)/2, 64)
	grown := make([]T, len(*p), grow)
	copy(grown, *p)
	*p = grown
}

func satLens(g *Graph) [nSat]int32 {
	return [nSat]int32{
		int32(len(g.Markers)), int32(len(g.Imports)), int32(len(g.BuildTag)),
		int32(len(g.Hazards)), int32(len(g.WgSites)), int32(len(g.Goro)),
		int32(len(g.Defers)), int32(len(g.Chans)), int32(len(g.UInput)),
		int32(len(g.Secret)), int32(len(g.Literals)), int32(len(g.Iface)),
		int32(len(g.Structs)), int32(len(g.Params)), int32(len(g.paramsSym)),
		int32(len(g.pSid)), int32(len(g.pFid)), int32(len(g.pMid)),
		int32(len(g.pLine)), int32(len(g.pName)), int32(len(g.pType)),
	}
}

func newSink(g *Graph) *Graph {
	return &Graph{
		Str:    g.Str,
		File:   g.File,
		byName: make(map[string][]int32, 64),
	}
}

var symSliceFields = func() []int {
	t := reflect.TypeFor[Syms]()
	var out []int
	for i := 0; i < t.NumField(); i++ {
		if t.Field(i).Type.Kind() == reflect.Slice {
			out = append(out, i)
		}
	}
	return out
}()

func mergeRange(dst, src *Graph, r fileRange) {
	base := int32(dst.Sym.n)
	symEnd := base + r.symN

	shift := base - r.symStart

	d := reflect.ValueOf(&dst.Sym).Elem()
	o := reflect.ValueOf(&src.Sym).Elem()
	for _, f := range symSliceFields {
		fv := d.Field(f)
		part := o.Field(f).Slice(int(r.symStart), int(r.symEnd()))
		fv.Set(reflect.AppendSlice(fv, part))
	}
	dst.Sym.n = int(symEnd)
	for i := int(base); i < int(symEnd); i++ {
		if p := dst.Sym.ParentId[i]; p >= 0 {
			dst.Sym.ParentId[i] = p + shift
		}
	}

	dst.symTypeName = append(dst.symTypeName,
		src.symTypeName[r.typeStart:r.typeStart+r.symN]...)

	for i := range 13 {
		off, n := r.sat[i][0], r.sat[i][1]
		if n == 0 {
			continue
		}
		switch i {
		case 0:
			copySat(&dst.Markers, &src.Markers, off, n, shift, func(p *Marker, b int32) {
				if p.SymbolID >= 0 {
					p.SymbolID += b
				}
			})
		case 1:
			copySat(&dst.Imports, &src.Imports, off, n, 0, func(p *Import, _ int32) {})
		case 2:
			copySat(&dst.BuildTag, &src.BuildTag, off, n, 0, func(p *BuildTag, _ int32) {})
		case 3:
			copySat(&dst.Hazards, &src.Hazards, off, n, shift, func(p *Hazard, b int32) { p.SymbolID += b })
		case 4:
			copySat(&dst.WgSites, &src.WgSites, off, n, shift, func(p *WgSite, b int32) { p.SymbolID += b })
		case 5:
			copySat(&dst.Goro, &src.Goro, off, n, shift, func(p *Goro, b int32) { p.SymbolID += b })
		case 6:
			copySat(&dst.Defers, &src.Defers, off, n, shift, func(p *Defer, b int32) { p.SymbolID += b })
		case 7:
			copySat(&dst.Chans, &src.Chans, off, n, shift, func(p *Chan, b int32) { p.SymbolID += b })
		case 8:
			copySat(&dst.UInput, &src.UInput, off, n, shift, func(p *UInput, b int32) { p.SymbolID += b })
		case 9:
			copySat(&dst.Secret, &src.Secret, off, n, shift, func(p *Secret, b int32) { p.SymbolID += b })
		case 10:
			copySat(&dst.Literals, &src.Literals, off, n, shift, func(p *Literal, b int32) { p.SymbolID += b })
		case 11:
			copySat(&dst.Iface, &src.Iface, off, n, shift, func(p *Iface, b int32) { p.SymbolID += b })
		case 12:
			copySat(&dst.Structs, &src.Structs, off, n, shift, func(p *Struct, b int32) { p.SymbolID += b })
		}
	}

	for _, pl := range []struct {
		dstp  *[]int32
		srcp  *[]int32
		i     int
		shift bool
	}{
		{&dst.paramsSym, &src.paramsSym, 14, true}, {&dst.pSid, &src.pSid, 15, true},
		{&dst.pFid, &src.pFid, 16, false}, {&dst.pMid, &src.pMid, 17, false},
		{&dst.pLine, &src.pLine, 18, false},
	} {
		off, n := r.sat[pl.i][0], r.sat[pl.i][1]
		part := (*pl.srcp)[off : off+n]
		if pl.shift {
			shiftBy(part, shift)
		}
		*pl.dstp = append(*pl.dstp, part...)
	}
	for _, pl := range []struct {
		dstp *[]uint32
		srcp *[]uint32
		i    int
	}{{&dst.pName, &src.pName, 19}, {&dst.pType, &src.pType, 20}} {
		off, n := r.sat[pl.i][0], r.sat[pl.i][1]
		*pl.dstp = append(*pl.dstp, (*pl.srcp)[off:off+n]...)
	}

	copySat(&dst.Params, &src.Params, r.sat[13][0], r.sat[13][1], 0, func(p *Param, _ int32) {})
}

func (r fileRange) symEnd() int32 { return r.symStart + r.symN }

func shiftBy(ids []int32, base int32) {
	for i, v := range ids {
		ids[i] = v + base
	}
}

func copySat[T any](dst *[]T, src *[]T, off, n, base int32, fix func(*T, int32)) {
	part := (*src)[off : off+n]
	for i := range part {
		fix(&part[i], base)
	}
	*dst = append(*dst, part...)
}

var (
	slashSlash = []byte("//")
	hashSign   = []byte("#")
	starStar   = []byte("*")
	dashDash   = []byte("--")
	nlByte     = []byte("\n")
)

func (x *extractor) scanMarkers() {
	rec := x.file
	ln := 0
	lineNo := 0
	for i := 0; i <= len(rec.Text); i++ {
		if i != len(rec.Text) && rec.Text[i] != '\n' {
			continue
		}
		line := rec.Text[ln:i]
		ln = i + 1
		lineNo++
		if !bytes.Contains(line, slashSlash) && !bytes.Contains(line, hashSign) &&
			!bytes.Contains(line, starStar) && !bytes.Contains(line, dashDash) {
			continue
		}
		kind, _, ok := findMarker(string(line))
		if !ok {
			continue
		}
		x.g.Markers = append(x.g.Markers, Marker{
			FileID: rec.FID, SymbolID: noNode,
			Kind: x.g.intern(strings.ToUpper(kind)),
			Line: int32(lineNo),
			Text: x.g.intern(trunc(string(bytes.TrimSpace(line)), 200)),
		})
	}
}

func (x *extractor) parseImports(t *Tree) {

	var walk func(n int32)
	walk = func(n int32) {
		for c := t.nodes[n].first; c != noNode; c = t.nodes[c].next {
			x.collectImports(t, c)
			walk(c)
		}
	}
	for c := t.nodes[t.root].first; c != noNode; c = t.nodes[c].next {
		if t.nodes[c].kind == kImportDecl {
			for d := t.nodes[c].first; d != noNode; d = t.nodes[d].next {
				x.collectImports(t, d)
				walk(d)
			}
		}
	}

	if t.nerr > 0 {
		walk(t.root)
	}
}

func (x *extractor) collectImports(t *Tree, n int32) {
	if t.nodes[n].kind != kImportSpec {
		return
	}
	p := t.child(n, fPath)
	if p == noNode {
		return
	}
	target := strings.Trim(t.text(p), "`\"")
	alias := noNode
	aliasID := nullStr
	if a := t.child(n, fName); a != noNode {
		alias = a
		aliasID = x.g.intern(t.text(a))
	}

	head := target
	if i := strings.IndexByte(head, '/'); i >= 0 {
		head = head[:i]
	}
	ext := strings.Contains(head, ".") || !stdlibRoots[head]
	x.g.Imports = append(x.g.Imports, Import{
		FileID: x.file.FID, Target: x.g.intern(trunc(target, 300)), TargetID: -1,
		Alias: aliasID, Kind: x.g.intern("import"), Line: t.nodes[n].line + 1,
		External: boolInt(ext && strings.Contains(head, ".")),
		Wildcard: boolInt(alias != noNode && t.text(alias) == "."),
		NNames:   1,
	})
}

func (x *extractor) parseFileExtras(t *Tree, rec FileRec) {
	head := rec.Text
	if len(head) > 4000 {
		head = head[:4000]
	}
	for _, m := range reGoBuild.FindAllSubmatchIndex(head, -1) {
		x.g.BuildTag = append(x.g.BuildTag, BuildTag{
			FileID: rec.FID, Expr: x.g.intern(trunc(string(bytes.TrimSpace(head[m[2]:m[3]])), 200)),
			Line: int32(bytes.Count(head[:m[0]], nlByte) + 1),
		})
	}
	if reGenerated.Match(head) {
		x.g.File[rec.FID].IsGen = 1
	}
}

func resolveCalls(g *Graph) {
	g.buildLoc()
	byName := g.byName

	byQual := make(map[uint64]int32, g.Sym.n)
	fileScope := make(map[uint64]int32, g.Sym.n)
	typeScope := map[string]int32{}

	for i := 0; i < g.Sym.n; i++ {
		id := int32(i)
		nm := g.Str.get(g.Sym.Name[i])
		qual := g.Sym.QualName[i]
		byQual[uint64(qual)] = id
		byQual[uint64(uint32(g.fileOf[id]))<<32|uint64(qual)] = id
		fk := uint64(uint32(g.fileOf[id]))<<32 | uint64(g.Sym.Name[i])
		if _, ok := fileScope[fk]; !ok {
			fileScope[fk] = id
		}
		if tn := g.symTypeName[id]; tn != "" {
			k := tn + "\x00" + nm
			if _, ok := typeScope[k]; !ok {
				typeScope[k] = id
			}
		}
	}

	edgeIdx := map[int64]int32{}
	unresIdx := map[uint64]int32{}

	csSeen := map[[3]int32]bool{}

	for i := range g.pSid {
		sid := g.pSid[i]
		fid := g.pFid[i]
		mid := g.pMid[i]
		line := g.pLine[i]

		name := strings.TrimSpace(g.Str.get(g.pName[i]))
		ty := g.Str.get(g.pType[i])
		base := lastDot(name)

		target := int32(-1)
		if ty != "" {
			target = lookStr(typeScope, ty+"\x00"+base)
		}
		if target < 0 {
			if nameID, ok := g.Str.lookup(name); ok {
				target = lookU64(byQual, uint64(nameID))
			}
		}
		if target < 0 {
			if baseID, ok := g.Str.lookup(base); ok {
				target = lookU64(fileScope, uint64(uint32(fid))<<32|uint64(baseID))
			}
		}
		if target < 0 {
			if ids := byName[base]; len(ids) == 1 {
				target = ids[0]
			}
		}
		if target < 0 {
			if x0 := (&extractor{g: g}).isExternal(name, base); x0 {
				g.extByCall[sid]++
				g.nExternal++
			} else {
				un := g.intern(trunc(name, 160))
				k := uint64(uint32(sid))<<32 | uint64(un)
				if j, ok := unresIdx[k]; ok {
					g.unresList[j].N++
				} else {
					unresIdx[k] = int32(len(g.unresList))
					g.unresList = append(g.unresList, Unres{
						Caller: sid, Name: un, N: 1, Line: line,
					})
				}
				g.nUnresolvd++
			}
			continue
		}
		g.nResolved++

		cfid, cmid := g.fileOf[target], g.modOf[target]
		ek := pack2(sid, target)
		if j, ok := edgeIdx[ek]; ok {
			g.edgeList[j].NCalls++
		} else {
			edgeIdx[ek] = int32(len(g.edgeList))
			g.edgeList = append(g.edgeList, rawEdge{
				Caller: sid, Callee: target, NCalls: 1,
				SameFile: boolInt(cfid == fid), SameMod: boolInt(cmid == mid),
				IsSelf: boolInt(sid == target),
			})
		}
		if line != 0 {
			ck := [3]int32{sid, target, line}
			if !csSeen[ck] {
				csSeen[ck] = true
				g.csList = append(g.csList, Callsite{Caller: sid, Callee: target, Line: line})
			}
		}
	}

	sort.SliceStable(g.edgeList, func(a, b int) bool {
		x0, y0 := g.edgeList[a], g.edgeList[b]
		if x0.Caller != y0.Caller {
			return x0.Caller < y0.Caller
		}
		return x0.Callee < y0.Callee
	})
	sort.SliceStable(g.unresList, func(a, b int) bool {
		x0, y0 := g.unresList[a], g.unresList[b]
		if x0.Caller != y0.Caller {
			return x0.Caller < y0.Caller
		}
		return g.Str.get(x0.Name) < g.Str.get(y0.Name)
	})
	sort.SliceStable(g.csList, func(a, b int) bool {
		x0, y0 := g.csList[a], g.csList[b]
		if x0.Caller != y0.Caller {
			return x0.Caller < y0.Caller
		}
		if x0.Callee != y0.Callee {
			return x0.Callee < y0.Callee
		}
		return x0.Line < y0.Line
	})
}

func lookStr(m map[string]int32, k string) int32 {
	if v, ok := m[k]; ok {
		return v
	}
	return -1
}

func lookU64(m map[uint64]int32, k uint64) int32 {
	if v, ok := m[k]; ok {
		return v
	}
	return -1
}

func pack2(a, b int32) int64 { return int64(uint64(uint32(a))<<32 | uint64(uint32(b))) }

var hazardCats = []string{"goroutine", "channel", "defer", "lock", "atomic",
	"context", "io", "net", "sql", "exec", "unsafe", "reflect", "cgo", "alloc",
	"panic", "time"}

func materialize(g *Graph) {
	n := g.Sym.n
	s := &g.Sym

	for i := range n {
		id := int32(i)
		self := int32(0)
		for p := g.Calls.Out.off[id]; p < g.Calls.Out.off[id+1]; p++ {
			if g.Calls.Out.val[p].IsSelf != 0 {
				self++
			}
		}
		s.FanOut[i] = g.Calls.Out.count(id) - self
		s.FanIn[i] = g.Calls.In.count(id) - self
		s.NCallsites[i] = g.csCSR.count(id)
	}

	catIdx := map[string]int{}
	for i, c := range hazardCats {
		catIdx["n_"+c] = i
	}
	catCount := make([][]int32, len(hazardCats))
	for i := range catCount {
		catCount[i] = make([]int32, n)
	}
	for i, h := range g.Hazards {
		ci, ok := catIdx["n_"+g.Str.get(h.Category)]
		if ok {
			catCount[ci][h.SymbolID] += h.N
		}
		_ = i
	}
	for ci, c := range hazardCats {
		switch c {
		case "goroutine":
			for i, v := range catCount[ci] {
				if v != 0 {
					s.NGoroutine[i] = v
				}
			}
		case "channel":
			for i, v := range catCount[ci] {
				if v != 0 {
					s.NChannel[i] = v
				}
			}
		case "defer":
			for i, v := range catCount[ci] {
				if v != 0 {
					s.NDefer[i] = v
				}
			}
		case "lock":
			for i, v := range catCount[ci] {
				if v != 0 {
					s.NLock[i] = v
				}
			}
		case "atomic":
			for i, v := range catCount[ci] {
				if v != 0 {
					s.NAtomic[i] = v
				}
			}
		case "context":
			for i, v := range catCount[ci] {
				if v != 0 {
					s.NContext[i] = v
				}
			}
		case "io":
			for i, v := range catCount[ci] {
				if v != 0 {
					s.NIo[i] = v
				}
			}
		case "net":
			for i, v := range catCount[ci] {
				if v != 0 {
					s.NNet[i] = v
				}
			}
		case "sql":
			for i, v := range catCount[ci] {
				if v != 0 {
					s.NSql[i] = v
				}
			}
		case "exec":
			for i, v := range catCount[ci] {
				if v != 0 {
					s.NExec[i] = v
				}
			}
		case "unsafe":
			for i, v := range catCount[ci] {
				if v != 0 {
					s.NUnsafe[i] = v
				}
			}
		case "reflect":
			for i, v := range catCount[ci] {
				if v != 0 {
					s.NReflect[i] = v
				}
			}
		case "cgo":
			for i, v := range catCount[ci] {
				if v != 0 {
					s.NCgo[i] = v
				}
			}
		case "alloc":
			for i, v := range catCount[ci] {
				if v != 0 {
					s.NAlloc[i] = v
				}
			}
		case "panic":
			for i, v := range catCount[ci] {
				if v != 0 {
					s.NPanic[i] = v
				}
			}
		case "time":
			for i, v := range catCount[ci] {
				if v != 0 {
					s.NTime[i] = v
				}
			}
		}
	}

	nUnres := make([]int32, n)
	for _, u := range g.unresList {
		nUnres[u.Caller] += u.N
	}
	copy(s.NUnresolvedCalls, nUnres)
	totalHaz := make([]int32, n)
	for i := range g.Hazards {
		totalHaz[g.Hazards[i].SymbolID] += g.Hazards[i].N
	}
	copy(s.NHazards, totalHaz)
	nGoInLoop := make([]int32, n)
	for _, o := range g.Goro {
		if o.InLoop != 0 {
			nGoInLoop[o.SymbolID]++
		}
	}
	copy(s.NGoInLoop, nGoInLoop)
	nDeferInLoop := make([]int32, n)
	nDeferClose := make([]int32, n)
	for _, o := range g.Defers {
		if o.InLoop != 0 {
			nDeferInLoop[o.SymbolID]++
		}
		if o.IsClose != 0 {
			nDeferClose[o.SymbolID]++
		}
	}
	copy(s.NDeferInLoop, nDeferInLoop)
	copy(s.NDeferClose, nDeferClose)
	for sid, v := range g.extByCall {
		s.NExternalCalls[sid] = v
	}
	for _, e := range g.edgeList {
		if e.IsSelf != 0 {
			s.IsRecursive[e.Caller] = 1
		}
	}
	for i := range n {
		s.IsLeaf[i] = boolInt(s.FanOut[i] == 0)
		s.IsRoot[i] = boolInt(s.FanIn[i] == 0)
	}

	uniq := make([]int32, n)
	for i := range n {
		uniq[i] = g.Calls.Out.count(int32(i))
	}
	copy(s.NUniqueCalls, uniq)

	nsym := make([]int32, len(g.File))
	nfn := make([]int32, len(g.File))
	ntp := make([]int32, len(g.File))
	tcyc := make([]int32, len(g.File))
	mcyc := make([]int32, len(g.File))
	trisk := make([]int32, len(g.File))
	isType := map[string]bool{"class": true, "struct": true, "interface": true,
		"trait": true, "enum": true, "union": true, "record": true,
		"protocol": true, "type": true, "module": true, "impl": true}
	isFn := map[string]bool{"function": true, "method": true, "constructor": true, "closure": true}
	for i := range n {
		fid := s.FileId[i]
		nsym[fid]++
		k := g.Str.get(s.Kind[i])
		if isFn[k] {
			nfn[fid]++
		}
		if isType[k] {
			ntp[fid]++
		}
		tcyc[fid] += s.Cyclomatic[i]
		if s.Cyclomatic[i] > mcyc[fid] {
			mcyc[fid] = s.Cyclomatic[i]
		}
		trisk[fid] += s.RiskScore[i]
	}
	nimp := make([]int32, len(g.File))
	for _, im := range g.Imports {
		nimp[im.FileID]++
	}
	for i := range g.File {
		g.File[i].NSymbols = nsym[i]
		g.File[i].NFuncs = nfn[i]
		g.File[i].NTypes = ntp[i]
		g.File[i].TotalCyc = tcyc[i]
		g.File[i].MaxCyc = mcyc[i]
		g.File[i].NImports = nimp[i]
	}

	for i := range g.File {
		m := &g.Mod[g.File[i].ModuleID]
		m.NFiles++
		m.Sloc += g.File[i].Sloc
	}
	nsyms := make([]int32, len(g.Mod))
	npub := make([]int32, len(g.Mod))
	for i := range n {
		mid := s.ModuleId[i]
		if mid < 0 {
			continue
		}
		nsyms[mid]++
		if s.IsPublic[i] != 0 {
			npub[mid]++
		}
	}
	for i := range g.Mod {
		g.Mod[i].NSyms = nsyms[i]
		g.Mod[i].NPublic = npub[i]
	}

	fanOut := make(map[int32]map[int32]bool, len(g.Mod))
	fanIn := make(map[int32]map[int32]bool, len(g.Mod))
	for _, e := range g.edgeList {
		a, b := s.ModuleId[e.Caller], s.ModuleId[e.Callee]
		if a < 0 || b < 0 || a == b {
			continue
		}
		if fanOut[a] == nil {
			fanOut[a] = map[int32]bool{}
		}
		if fanIn[b] == nil {
			fanIn[b] = map[int32]bool{}
		}
		fanOut[a][b] = true
		fanIn[b][a] = true
	}
	for i := range g.Mod {
		g.Mod[i].FanOut = int32(len(fanOut[int32(i)]))
		g.Mod[i].FanIn = int32(len(fanIn[int32(i)]))
		if t := g.Mod[i].FanIn + g.Mod[i].FanOut; t != 0 {
			g.Mod[i].Instab = float64(g.Mod[i].FanOut) / float64(t)
		}
	}

	for i := range n {
		rs := s.Cyclomatic[i]*2 + s.Cognitive[i] + s.MaxNesting[i]*4 +
			s.NUnsafe[i]*12 + s.NCgo[i]*10 + s.NExec[i]*15 + s.NReflect[i]*2 +
			s.NErrIgnored[i]*8 + s.NErrShadowed[i]*10 +
			s.NGoroutines[i]*4 + s.NGoInLoop[i]*12 + s.NDeferInLoop[i]*10 +
			s.NCtxBackground[i]*6 + s.NPanics[i]*6 + s.NLogFatal[i]*8 +
			s.NSqlConcat[i]*25 + s.QueryInLoop[i]*15 + s.NTimeTick[i]*8 +
			s.LockInLoop[i]*8 + s.NTypeAssertUnchecked[i]*5
		if s.IsRecursive[i] != 0 {
			rs += 12
		}
		if s.IsHandler[i] == 1 && s.NCtxParams[i] == 0 {
			rs += 10
		}
		s.RiskScore[i] = rs
		if s.NTokens[i] > 0 {
			d := s.NDistinctOperators[i] + s.NDistinctOperands[i]
			bf := int32(2)
			if d > 1 {
				bf = d
			}
			s.HalsteadVolume[i] = (s.NOperators[i] + s.NOperands[i]) * bf
		}
		if k := g.Str.get(s.Kind[i]); isFn[k] {
			s.Maintainability[i] = maintainability(s.Cyclomatic[i], s.Sloc[i])
		}
	}

	for i := range g.File {
		g.File[i].TotalRisk = trisk[i]
	}
}

//go:noinline

func rnd64(v float64) float64 { return v }

func maintainability(cyclomatic, sloc int32) int32 {
	f := 0.05
	if sloc > 1 {
		f = float64(sloc) / 20.0
	}
	v := 171.0 - rnd64(0.23*float64(cyclomatic))
	w := rnd64(16.2 * f)
	v = rnd64(v) - w
	m := max(int32(rnd64(v)), 0)
	return m
}

func interfaceSatisfaction(g *Graph) {
	byType := map[string]map[string]bool{}
	typesByMethod := map[string]map[string]bool{}
	testTypes := map[string]bool{}
	for i := 0; i < g.Sym.n; i++ {
		if g.Str.get(g.Sym.Kind[i]) != "method" {
			continue
		}
		recv := g.Str.get(g.Sym.ReceiverType[i])
		if recv == "" {
			continue
		}
		nm := g.Str.get(g.Sym.Name[i])
		if byType[recv] == nil {
			byType[recv] = map[string]bool{}
		}
		byType[recv][nm] = true
		if typesByMethod[nm] == nil {
			typesByMethod[nm] = map[string]bool{}
		}
		typesByMethod[nm][recv] = true
		if g.Sym.FileId[i] < int32(len(g.File)) && g.File[g.Sym.FileId[i]].IsTest != 0 {
			testTypes[recv] = true
		}
	}
	for _, f := range g.Iface {
		if f.NMethods == 0 {
			continue
		}
		ms := g.Str.get(f.Methods)
		if ms == "" {
			continue
		}
		want := strings.Split(ms, ",")

		var cand map[string]bool
		for i, w := range want {
			m := typesByMethod[w]
			if m == nil {
				cand = nil
				break
			}
			if i == 0 {
				cand = make(map[string]bool, len(m))
				for t := range m {
					cand[t] = true
				}
				continue
			}
			for t := range cand {
				if !m[t] {
					delete(cand, t)
				}
			}
		}
		if cand == nil {
			continue
		}
		for t := range cand {
			ok := true
			for _, w := range want {
				if w == "" {
					continue
				}
				if !byType[t][w] {
					ok = false
					break
				}
			}
			if !ok {
				continue
			}
			g.Impl = append(g.Impl, Impl{
				TypeName: g.intern(t), InterfaceID: f.SymbolID,
				InterfaceNam: g.intern(g.Str.get(g.Sym.Name[f.SymbolID])),
				NMethods:     f.NMethods, InTest: boolInt(testTypes[t]),
			})
		}
	}
	sort.SliceStable(g.Impl, func(a, b int) bool {
		x0, y0 := g.Impl[a], g.Impl[b]
		if x0.InterfaceID != y0.InterfaceID {
			return x0.InterfaceID < y0.InterfaceID
		}
		return g.Str.get(x0.TypeName) < g.Str.get(y0.TypeName)
	})
}

const errChainCap = 32

func errorChainDepth(g *Graph) {
	err := make([]bool, g.Sym.n)
	any := false
	for i := 0; i < g.Sym.n; i++ {
		if g.Sym.NErrReturns[i] > 0 {
			err[i] = true
			any = true
		}
	}
	if !any {
		return
	}
	fwd := make([][]int32, g.Sym.n)
	for _, e := range g.edgeList {
		if err[e.Caller] && err[e.Callee] {
			fwd[e.Caller] = append(fwd[e.Caller], e.Callee)
		}
	}
	memo := make([]int32, g.Sym.n)
	done := make([]bool, g.Sym.n)
	onPath := make([]bool, g.Sym.n)
	var depth func(n int32) int32
	depth = func(n int32) int32 {
		if done[n] {
			return memo[n]
		}
		if onPath[n] {
			return errChainCap
		}
		onPath[n] = true
		best := int32(0)
		for _, nx := range fwd[n] {
			if d := depth(nx); d > best {
				best = d
			}
		}
		onPath[n] = false
		done[n] = true
		memo[n] = best + 1
		return memo[n]
	}

	onPath = make([]bool, g.Sym.n)
	for i := 0; i < g.Sym.n; i++ {
		if !err[i] {
			continue
		}
		g.ErrChain = append(g.ErrChain, ErrChain{SymbolID: int32(i), MaxDepth: depth(int32(i))})
	}
	sort.SliceStable(g.ErrChain, func(a, b int) bool { return g.ErrChain[a].SymbolID < g.ErrChain[b].SymbolID })
}

func moduleDepth(g *Graph) {
	deps := map[int32]map[int32]bool{}
	inDeg := map[int32]int32{}
	for _, im := range g.Imports {
		if im.TargetID < 0 {
			continue
		}
		a := g.File[im.FileID].ModuleID
		b := g.File[im.TargetID].ModuleID
		if a == b {
			continue
		}
		if deps[a] == nil {
			deps[a] = map[int32]bool{}
			if _, ok := inDeg[a]; !ok {
				inDeg[a] = 0
			}
		}
		if deps[b] == nil {
			deps[b] = map[int32]bool{}
			if _, ok := inDeg[b]; !ok {
				inDeg[b] = 0
			}
		}
		if !deps[a][b] {
			deps[a][b] = true
			inDeg[b]++
		}
	}
	if len(deps) == 0 {
		return
	}
	depth := map[int32]int32{}
	for m := range deps {
		depth[m] = 0
	}
	var q []int32
	for m, d := range inDeg {
		if d == 0 {
			q = append(q, m)
		}
	}
	slices.Sort(q)
	order := make([]int32, 0, len(deps))
	for len(q) > 0 {
		m := q[0]
		q = q[1:]
		order = append(order, m)
		for t := range deps[m] {
			inDeg[t]--
			if inDeg[t] == 0 {
				q = append(q, t)
			}
		}
	}
	for _, m := range order {
		for t := range deps[m] {
			if depth[t] < depth[m]+1 {
				depth[t] = depth[m] + 1
			}
		}
	}
	reach := map[int32]map[int32]bool{}
	for m := range deps {
		reach[m] = map[int32]bool{}
	}
	for _, m := range slices.Backward(order) {

		for t := range deps[m] {
			reach[t][m] = true
			for r := range reach[m] {
				reach[t][r] = true
			}
		}
	}
	for m := range deps {
		mm := &g.Mod[m]
		mm.HasDep = true
		mm.Depth = depth[m]
		mm.NDirect = int32(len(deps[m]))
		mm.NTrans = int32(len(reach[m]))
	}
}

func resolveImportTargets(g *Graph) {
	byPath := make(map[string]int32, len(g.File)*2)
	for i := range g.File {
		p := g.File[i].Path
		byPath[p] = int32(i)
		if j := strings.LastIndexByte(p, '.'); j > 0 {
			if _, ok := byPath[p[:j]]; !ok {
				byPath[p[:j]] = int32(i)
			}
		}
	}
	suffixes := []string{"", ".py", ".pyi", ".ts", ".tsx", ".d.ts", ".mts", ".cts",
		".js", ".jsx", ".mjs", ".cjs", ".rb", ".php", ".go", ".rs", ".java"}
	indexes := []string{"__init__.py", "index.ts", "index.tsx", "index.js",
		"index.mjs", "mod.rs", "lib.rs"}
	look := func(cand string) int32 {
		cand = strings.Trim(cand, "/")
		if cand == "" {
			return -1
		}
		for _, sfx := range suffixes {
			if h, ok := byPath[cand+sfx]; ok {
				return h
			}
		}
		for _, idx := range indexes {
			if h, ok := byPath[cand+"/"+idx]; ok {
				return h
			}
		}
		return -1
	}
	n := 0
	for i := range g.Imports {
		im := &g.Imports[i]
		if im.TargetID >= 0 {
			continue
		}
		t := strings.TrimSpace(g.Str.get(im.Target))
		if t == "" {
			continue
		}
		here := dirOf(g.File[im.FileID].Path)
		var hit int32 = -1
		if strings.HasPrefix(t, ".") {
			nUp := len(t) - len(strings.TrimLeft(t, "."))
			rest := t[nUp:]
			if !strings.Contains(t, "/") {
				rest = strings.ReplaceAll(rest, ".", "/")
			} else {
				rest = strings.TrimLeft(t, "./")
			}
			base := here
			for k := 0; k < nUp-1; k++ {
				base = dirOf(base)
			}
			if base != "." && base != "" {
				hit = look(base + "/" + rest)
			} else {
				hit = look(rest)
			}
		} else {
			hit = look(strings.ReplaceAll(t, ".", "/"))
			if hit < 0 {
				hit = look(here + "/" + t)
			}
		}
		if hit >= 0 && hit != im.FileID {
			im.TargetID = hit
			n++
		}
	}
	g.Meta["imports_resolved"] = fmt.Sprintf("%d of %d import rows point at a file in this tree", n, len(g.Imports))
}

var _ = ast.Print

func nowStamp() string { return time.Now().Format("2006-01-02T15:04:05") }

type builder struct {
	t    *Tree
	file *token.File
	ti   int
}

func buildTree(file *token.File, src []byte, f *ast.File) *Tree {
	t := &Tree{src: src}
	t.lines = lineStarts(src)
	t.toks = scanTokens(src)
	capN := len(t.toks)*2 + 64
	t.nodes = make([]Node, 0, capN)
	t.tail = make([]int32, 0, capN)
	b := &builder{t: t, file: file}
	root := b.node(kSourceFile, 0, int32(len(src)), fNone)

	kw := int32(0)
	for _, tk := range t.toks {
		if tk.kind != kComment {
			kw = tk.off
			break
		}
	}

	pe := kw
	if f.Name != nil {
		if e, ok := b.tryOff(f.Name.End()); ok {
			pe = e
		}
	}
	pc := b.node(kPackageClause, kw, pe, fNone)
	b.add(root, pc)
	for _, d := range f.Decls {
		b.add(root, b.decl(d))
	}
	b.linkLeaves(root)
	t.root = root
	return t
}

func scanTokens(src []byte) []Token {
	lines := lineStarts(src)
	curLine := int32(0)
	lineOf := func(off int32) int32 {
		for curLine > 0 && lines[curLine] > off {
			curLine--
		}
		for curLine+1 < int32(len(lines)) && lines[curLine+1] <= off {
			curLine++
		}
		return curLine
	}
	out := make([]Token, 0, len(src)/5+16)
	fset := token.NewFileSet()
	tf := fset.AddFile("", -1, len(src))
	var s scanner.Scanner
	s.Init(tf, src, func(token.Position, string) {}, scanner.ScanComments)
	put := func(off, end int32, k NodeKind) {
		out = append(out, Token{off: off, end: end, line: lineOf(off), endL: lineOf(end), kind: k})
	}
	for {
		pos, tok, lit := s.Scan()
		if tok == token.EOF {
			break
		}
		off := int32(tf.Offset(pos))
		end := off + int32(len(lit))
		if lit == "" {

			end = off + opLen(src, off)
		}
		if tok == token.SEMICOLON && lit == "\n" {
			continue
		}
		if tok == token.STRING {

			put(off, off+1, kToken)
			put(end-1, end, kToken)
			continue
		}
		k := kToken
		if tok == token.COMMENT {
			k = kComment
		}
		put(off, end, k)
	}
	return out
}

func opLen(src []byte, off int32) int32 {
	if off+3 <= int32(len(src)) {
		switch string(src[off : off+3]) {
		case "...", "<<=", ">>=", "&^=":
			return 3
		}
	}
	if off+2 <= int32(len(src)) {
		switch string(src[off : off+2]) {
		case ":=", "<<", ">>", "&^", "&&", "||", "<=", ">=", "==", "!=",
			"++", "--", "+=", "-=", "*=", "/=", "%=", "&=", "|=", "^=", "<-":
			return 2
		}
	}
	return 1
}

func lineStarts(src []byte) []int32 {
	ls := make([]int32, 1, len(src)/24+8)
	for i := range src {
		if src[i] == '\n' {
			ls = append(ls, int32(i+1))
		}
	}
	return ls
}

func (b *builder) node(k NodeKind, start, end int32, f Slot) int32 {
	t := b.t
	id := int32(len(t.nodes))
	t.nodes = append(t.nodes, Node{kind: k, field: f, parent: noNode,
		first: noNode, next: noNode, start: start, end: end})
	t.tail = append(t.tail, noNode)
	t.nodes[id].line = t.lineOf(start)
	t.nodes[id].endLn = t.lineOf(end)
	return id
}

func (b *builder) add(parent, child int32) {
	if child == noNode {
		return
	}
	t := b.t
	t.nodes[child].parent = parent
	last := t.tail[parent]
	if last == noNode {
		t.nodes[parent].first = child
	} else {
		t.nodes[last].next = child
	}
	t.nodes[child].next = noNode
	t.tail[parent] = child
}

func (b *builder) off(p token.Pos) int32 { return int32(b.file.Offset(p)) }

func (b *builder) tryOff(p token.Pos) (int32, bool) {
	if b.file == nil || p == token.NoPos || p < token.Pos(b.file.Base()) {
		return 0, false
	}
	return int32(b.file.Offset(p)), true
}

func (b *builder) span(n ast.Node) (int32, int32) { return b.off(n.Pos()), b.off(n.End()) }

func (b *builder) linkLeaves(n int32) {
	t := b.t
	ns, ne := t.nodes[n].start, t.nodes[n].end
	for b.ti < len(t.toks) && t.toks[b.ti].off < ns {
		b.ti++
	}
	var head, tail int32 = noNode, noNode
	push := func(c int32) {
		t.nodes[c].next = noNode
		t.nodes[c].parent = n
		if tail == noNode {
			head = c
		} else {
			t.nodes[tail].next = c
		}
		tail = c
	}
	c := t.nodes[n].first
	for b.ti < len(t.toks) && t.toks[b.ti].off < ne {
		tk := t.toks[b.ti]
		for c != noNode && t.nodes[c].end <= tk.off {
			nx := t.nodes[c].next
			push(c)
			c = nx
		}
		if c != noNode && t.nodes[c].start <= tk.off {

			if !pureToken[t.nodes[c].kind] {
				b.linkLeaves(c)
			} else if b.ti < len(t.toks) && t.toks[b.ti].off < t.nodes[c].end {
				b.ti++
			}
			nx := t.nodes[c].next
			push(c)
			c = nx
			continue
		}
		leaf := int32(len(t.nodes))
		t.nodes = append(t.nodes, Node{kind: tk.kind, first: noNode, next: noNode, parent: n,
			start: tk.off, end: tk.end, line: tk.line, endLn: tk.endL})
		t.tail = append(t.tail, noNode)
		push(leaf)
		b.ti++
	}
	for c != noNode {
		nx := t.nodes[c].next
		push(c)
		c = nx
	}
	t.nodes[n].first = head
	t.tail[n] = tail
}

func (b *builder) decl(d ast.Decl) int32 {
	switch d := d.(type) {
	case *ast.FuncDecl:
		return b.funcDecl(d)
	case *ast.GenDecl:
		return b.genDecl(d)
	}
	return noNode
}

func (b *builder) funcDecl(d *ast.FuncDecl) int32 {
	s, e := b.span(d)
	kind := kFuncDecl
	if d.Recv != nil && len(d.Recv.List) > 0 {
		kind = kMethodDecl
	}
	n := b.node(kind, s, e, fNone)
	if kind == kMethodDecl {
		b.add(n, b.paramList(d.Recv, fReceiver))
	}
	if d.Name != nil {
		ps, pe := b.span(d.Name)
		nk := kIdentifier
		if kind == kMethodDecl {
			nk = kFieldIdent
		}
		b.add(n, b.node(nk, ps, pe, fName))
	}
	if d.Type != nil && d.Type.TypeParams != nil {
		b.add(n, b.typeParams(d.Type.TypeParams))
	}
	if d.Type != nil && d.Type.Params != nil {
		b.add(n, b.paramList(d.Type.Params, fParameters))
	}
	if d.Type != nil && d.Type.Results != nil {
		b.add(n, b.resultList(d.Type.Results))
	}
	if d.Body != nil {
		b.add(n, b.block(d.Body, fBody))
	}
	return n
}

func (b *builder) genDecl(d *ast.GenDecl) int32 {
	s, e := b.span(d)
	var k NodeKind
	switch d.Tok {
	case token.IMPORT:
		k = kImportDecl
	case token.CONST:
		k = kConstDecl
	case token.TYPE:
		k = kTypeDecl
	default:
		k = kVarDecl
	}
	n := b.node(k, s, e, fNone)
	holder := n

	if d.Lparen.IsValid() && (k == kImportDecl || k == kVarDecl) {
		lk := kVarSpecList
		if k == kImportDecl {
			lk = kImportSpecList
		}
		lst := b.node(lk, b.off(d.Lparen), b.off(d.Rparen)+1, fNone)
		b.add(n, lst)
		holder = lst
	}
	for _, sp := range d.Specs {
		switch sp := sp.(type) {
		case *ast.ImportSpec:
			ps, pe := b.span(sp)
			in := b.node(kImportSpec, ps, pe, fNone)
			if sp.Name != nil {
				ns, ne := b.span(sp.Name)
				switch sp.Name.Name {
				case "_":
					b.add(in, b.node(kBlankIdent, ns, ne, fName))
				case ".":
					b.add(in, b.node(kDot, ns, ne, fName))
				default:
					b.add(in, b.node(kPackageIdent, ns, ne, fName))
				}
			}
			if sp.Path != nil {
				b.add(in, b.stringNode(sp.Path, fPath))
			}
			b.add(holder, in)
		case *ast.ValueSpec:
			nk := kVarSpec
			if d.Tok == token.CONST {
				nk = kConstSpec
			}
			ps, pe := b.span(sp)
			vs := b.node(nk, ps, pe, fNone)
			for _, nm := range sp.Names {
				xs, xe := b.span(nm)
				b.add(vs, b.node(kIdentifier, xs, xe, fName))
			}
			if sp.Type != nil {
				b.add(vs, b.typ(sp.Type, fType))
			}
			if len(sp.Values) > 0 {
				xs, _ := b.span(sp.Values[0])
				xe := b.off(sp.Values[len(sp.Values)-1].End())
				el := b.node(kExprList, xs, xe, fValue)
				for _, v := range sp.Values {
					b.add(el, b.expr(v))
				}
				b.add(vs, el)
			}
			b.add(holder, vs)
		case *ast.TypeSpec:
			ps, pe := b.span(sp)
			tk := kTypeSpec
			if sp.Assign.IsValid() {

				tk = kTypeAlias
			}
			ts := b.node(tk, ps, pe, fNone)
			if sp.Name != nil {
				xs, xe := b.span(sp.Name)
				b.add(ts, b.node(kTypeIdent, xs, xe, fName))
			}
			if sp.TypeParams != nil {
				b.add(ts, b.typeParams(sp.TypeParams))
			}
			if sp.Type != nil {
				b.add(ts, b.typ(sp.Type, fType))
			}
			b.add(holder, ts)
		}
	}
	return n
}

func (b *builder) typeParams(fl *ast.FieldList) int32 {
	s, e := b.span(fl)
	n := b.node(kTypeParams, s, e, fTypeParameters)
	for _, fld := range fl.List {
		fs, fe := b.span(fld)
		pd := b.node(kTypeParamDecl, fs, fe, fNone)
		if len(fld.Names) > 0 {
			xs, xe := b.span(fld.Names[0])
			b.add(pd, b.node(kIdentifier, xs, xe, fName))
		}
		if fld.Type != nil {
			ts, te := b.span(fld.Type)
			b.add(pd, b.node(kTypeConstraint, ts, te, fType))
		}
		b.add(n, pd)
	}
	return n
}

func (b *builder) paramList(fl *ast.FieldList, f Slot) int32 {
	s, e := b.span(fl)
	n := b.node(kParamList, s, e, f)
	for _, fld := range fl.List {
		k := kParamDecl
		if _, ok := fld.Type.(*ast.Ellipsis); ok {
			k = kVariadicParamDecl
		}

		if len(fld.Names) > paramNamesPerDecl {
			for _, nm := range fld.Names[:len(fld.Names)-paramNamesPerDecl] {
				xs, xe := b.span(nm)
				pd := b.node(kParamDecl, xs, xe, fNone)
				b.add(pd, b.node(kTypeIdent, xs, xe, fType))
				b.add(n, pd)
			}
			fld = &ast.Field{
				Names: fld.Names[len(fld.Names)-paramNamesPerDecl:],
				Type:  fld.Type,
			}
		}
		fs, fe := b.span(fld)
		pd := b.node(k, fs, fe, fNone)
		for _, nm := range fld.Names {
			xs, xe := b.span(nm)
			b.add(pd, b.node(kIdentifier, xs, xe, fName))
		}
		switch ft := fld.Type.(type) {
		case nil:
		case *ast.Ellipsis:
			b.add(pd, b.typ(ft.Elt, fType))
		default:
			b.add(pd, b.typ(ft, fType))
		}
		b.add(n, pd)
	}
	return n
}

const paramNamesPerDecl = 9

func (b *builder) resultList(fl *ast.FieldList) int32 {
	if fl == nil {
		return noNode
	}
	if !fl.Opening.IsValid() && len(fl.List) == 1 && len(fl.List[0].Names) == 0 {
		return b.typ(fl.List[0].Type, fResult)
	}
	return b.paramList(fl, fResult)
}

func (b *builder) typ(e ast.Expr, f Slot) int32 {
	if e == nil {
		return noNode
	}
	s, en := b.span(e)
	switch t := e.(type) {
	case *ast.Ident:
		return b.node(kTypeIdent, s, en, f)
	case *ast.SelectorExpr:
		n := b.node(kQualifiedType, s, en, f)
		if t.X != nil {
			xs, xe := b.span(t.X)
			b.add(n, b.node(kPackageIdent, xs, xe, fPackage))
		}
		if t.Sel != nil {
			xs, xe := b.span(t.Sel)
			b.add(n, b.node(kTypeIdent, xs, xe, fName))
		}
		return n
	case *ast.StarExpr:
		n := b.node(kPointerType, s, en, f)
		b.add(n, b.typ(t.X, fNone))
		return n
	case *ast.ArrayType:

		k := kSliceType
		if t.Len != nil {
			k = kArrayType
			if _, ok := t.Len.(*ast.Ellipsis); ok {

				k = kImplicitArray
			}
		}
		n := b.node(k, s, en, f)
		if t.Len != nil {
			if _, ok := t.Len.(*ast.Ellipsis); !ok {
				b.add(n, b.exprNode(t.Len, fIndex))
			}
		}
		b.add(n, b.typ(t.Elt, fElement))
		return n
	case *ast.StructType:
		n := b.node(kStructType, s, en, f)
		if t.Fields != nil {
			fs, fe := b.span(t.Fields)
			fl := b.node(kFieldDeclList, fs, fe, fNone)
			for _, fld := range t.Fields.List {
				xs, xe := b.span(fld)
				fd := b.node(kFieldDecl, xs, xe, fNone)
				for _, nm := range fld.Names {
					ns, ne := b.span(nm)
					b.add(fd, b.node(kFieldIdent, ns, ne, fName))
				}
				if fld.Type != nil {
					if st, ok := fld.Type.(*ast.StarExpr); ok && len(fld.Names) == 0 {

						b.add(fd, b.typ(st.X, fType))
					} else {
						b.add(fd, b.typ(fld.Type, fType))
					}
				}
				if fld.Tag != nil {
					if k := litKind(fld.Tag); k == kInterpStr || k == kRawStr {
						b.add(fd, b.stringNode(fld.Tag, fTag))
					} else {
						gs, ge := b.span(fld.Tag)
						b.add(fd, b.node(k, gs, ge, fTag))
					}
				}
				b.add(fl, fd)
			}
			b.add(n, fl)
		}
		return n
	case *ast.FuncType:
		n := b.node(kFuncType, s, en, f)
		if t.Params != nil {
			b.add(n, b.paramList(t.Params, fParameters))
		}
		b.add(n, b.resultList(t.Results))
		return n
	case *ast.InterfaceType:
		n := b.node(kInterfaceType, s, en, f)
		if t.Methods == nil {
			return n
		}
		for _, fld := range t.Methods.List {
			xs, xe := b.span(fld)
			if len(fld.Names) > 0 {
				me := b.node(kMethodElem, xs, xe, fNone)
				ns, ne := b.span(fld.Names[0])
				b.add(me, b.node(kFieldIdent, ns, ne, fName))
				if ft, ok := fld.Type.(*ast.FuncType); ok {
					b.add(me, b.paramList(ft.Params, fParameters))
					b.add(me, b.resultList(ft.Results))
				}
				b.add(n, me)
				continue
			}
			te := b.node(kTypeElem, xs, xe, fNone)
			b.addUnion(te, fld.Type)
			b.add(n, te)
		}
		return n
	case *ast.MapType:
		n := b.node(kMapType, s, en, f)
		b.add(n, b.typ(t.Key, fKey))
		b.add(n, b.typ(t.Value, fValue))
		return n
	case *ast.ChanType:
		n := b.node(kChanType, s, en, f)
		b.add(n, b.typ(t.Value, fValue))
		return n
	case *ast.UnaryExpr:
		if t.Op == token.TILDE {
			n := b.node(kNegatedType, s, en, f)
			b.add(n, b.typ(t.X, fNone))
			return n
		}
		n := b.node(kUnaryExpr, s, en, f)
		b.add(n, b.expr(t.X))
		return n
	case *ast.Ellipsis:
		return b.node(kEllipsis, s, en, f)
	case *ast.IndexExpr:
		return b.genericType(s, en, b.off(t.Lbrack), b.off(t.Rbrack)+1, f, t.X, []ast.Expr{t.Index})
	case *ast.IndexListExpr:
		return b.genericType(s, en, b.off(t.Lbrack), b.off(t.Rbrack)+1, f, t.X, t.Indices)
	case *ast.ParenExpr:

		n := b.node(kParenType, s, en, f)
		b.add(n, b.typ(t.X, fNone))
		return n
	default:
		return b.exprNode(e, f)
	}
}

func (b *builder) addUnion(parent int32, e ast.Expr) {
	if be, ok := e.(*ast.BinaryExpr); ok && be.Op == token.OR {
		b.addUnion(parent, be.X)
		b.addUnion(parent, be.Y)
		return
	}
	b.add(parent, b.typ(e, fNone))
}

func (b *builder) genericType(s, en, bs, be int32, f Slot, x ast.Expr, idx []ast.Expr) int32 {
	n := b.node(kGenericType, s, en, f)
	b.add(n, b.typ(x, fType))
	if len(idx) == 0 {
		return n
	}
	args := b.node(kTypeArgs, bs, be, fTypeArgs)
	for _, i := range idx {
		is, ie := b.span(i)
		te := b.node(kTypeElem, is, ie, fNone)
		b.add(te, b.typ(i, fNone))
		b.add(args, te)
	}
	b.add(n, args)
	return n
}

func isTypeArg(e ast.Expr) bool {
	if isTypeLiteral(e) {
		return true
	}
	switch t := e.(type) {
	case *ast.SelectorExpr:

		_, ok := t.X.(*ast.Ident)
		return ok
	case *ast.StarExpr:
		return isTypeArg(t.X)
	case *ast.ParenExpr:
		return isTypeArg(t.X)
	}
	return false
}

func readsAsIndex(e ast.Expr) bool {
	switch t := e.(type) {
	case *ast.Ident:
		return true
	case *ast.StarExpr:
		_, ok := t.X.(*ast.Ident)
		return ok
	}
	return false
}

func isTypeish(e ast.Expr) bool {
	if isTypeArg(e) {
		return true
	}
	switch t := e.(type) {
	case *ast.Ident:
		return true
	case *ast.StarExpr:
		return isTypeish(t.X)
	case *ast.ParenExpr:
		return isTypeish(t.X)
	}
	return false
}

func parenGeneric(e ast.Expr) bool {
	switch t := e.(type) {
	case *ast.IndexExpr, *ast.IndexListExpr:
		return true
	case *ast.StarExpr:
		return parenGeneric(t.X)
	case *ast.ParenExpr:
		return parenGeneric(t.X)
	}
	return false
}

func isTypeLiteral(e ast.Expr) bool {
	switch t := e.(type) {
	case *ast.ArrayType:
		return true
	case *ast.MapType, *ast.ChanType, *ast.StructType, *ast.InterfaceType,
		*ast.FuncType:
		return true
	case *ast.ParenExpr:
		return isTypeLiteral(t.X)
	case *ast.StarExpr:
		return isTypeLiteral(t.X)
	case *ast.Ellipsis:
		return t.Elt == nil
	}
	return false
}

func (b *builder) typeArgs(lb, rb token.Pos, idx ast.Expr) int32 {
	as := b.off(lb)
	ae := b.off(rb) + 1
	args := b.node(kTypeArgs, as, ae, fTypeArgs)
	is, ie := b.span(idx)
	te := b.node(kTypeElem, is, ie, fNone)
	b.add(te, b.typ(idx, fNone))
	b.add(args, te)
	return args
}

func (b *builder) genericCall(t *ast.CallExpr, base ast.Expr, lb, rb token.Pos,
	one ast.Expr, many []ast.Expr, f Slot) int32 {
	s, en := b.span(t)
	n := b.node(kCallExpr, s, en, f)
	typeish := isTypeish(one)
	if many != nil {
		typeish = len(many) > 0
		for _, m := range many {
			if !isTypeish(m) {
				typeish = false
			}
		}
	}
	if len(t.Args) == 1 && typeish {
		n = b.node(kTypeConversion, s, en, f)
		b.add(n, b.genericTypeNode(base, lb, rb, one, many, fType))
		b.add(n, b.elemNode(t.Args[0], false))
		return n
	}

	idxs := many
	if idxs == nil {
		idxs = []ast.Expr{one}
	}
	typeArg, anyBare := true, false
	for _, ix := range idxs {
		if !isTypeish(ix) {
			typeArg = false
		}
		if readsAsIndex(ix) {
			anyBare = true
		}
	}
	if len(idxs) < 2 && anyBare {
		typeArg = false
	}
	if typeArg {
		b.add(n, b.exprNode(base, fFunction))
		b.add(n, b.typeArgsList(lb, rb, one, many))
	} else {

		idx := b.node(kIndexExpr, s, en, fFunction)
		b.add(idx, b.exprNode(base, fNone))
		if many != nil {
			for _, m := range many {
				b.add(idx, b.exprNode(m, fIndex))
			}
		} else {
			b.add(idx, b.exprNode(one, fIndex))
		}
		b.t.nodes[idx].end = b.off(rb) + 1
		b.add(n, idx)
	}
	b.add(n, b.argList(t, false))
	return n
}

func (b *builder) typeInstantiation(s, en int32, f Slot, outer ast.Expr, _ []ast.Expr) (int32, bool) {
	type link struct {
		base    ast.Expr
		lb, rb  token.Pos
		indices []ast.Expr
	}
	var chain []link
	cur := outer
	for {
		switch t := cur.(type) {
		case *ast.IndexExpr:
			chain = append(chain, link{t.X, t.Lbrack, t.Rbrack, []ast.Expr{t.Index}})
			cur = t.X
		case *ast.IndexListExpr:
			chain = append(chain, link{t.X, t.Lbrack, t.Rbrack, t.Indices})
			cur = t.X
		default:
			cur = nil
		}
		if cur == nil {
			break
		}
	}
	if len(chain) < 2 {
		return 0, false
	}
	for _, l := range chain {
		if len(l.indices) == 0 {
			return 0, false
		}
		for _, ix := range l.indices {
			if !isTypeArg(ix) {
				return 0, false
			}
		}
	}

	inner := chain[len(chain)-1]
	switch base := inner.base.(type) {
	case *ast.Ident:
	case *ast.SelectorExpr:
		if _, ok := base.X.(*ast.Ident); !ok {
			return 0, false
		}
	default:
		return 0, false
	}
	n := b.node(kTypeInstantiation, s, en, f)
	xs, _ := b.span(inner.base)
	gt := b.node(kGenericType, xs, b.off(inner.rb)+1, fType)
	b.add(gt, b.typ(inner.base, fType))
	b.add(gt, b.typeArgsList(inner.lb, inner.rb, nil, inner.indices))
	b.add(n, gt)
	for i := len(chain) - 2; i >= 0; i-- {
		l := chain[i]
		is, ie := b.span(l.indices[0])
		te := b.node(kTypeElem, is, ie, fPackage)
		b.add(te, b.typ(l.indices[0], fNone))
		b.add(n, te)
	}
	return n, true
}

func (b *builder) genericTypeNode(base ast.Expr, lb, rb token.Pos, one ast.Expr, many []ast.Expr, f Slot) int32 {
	xs, _ := b.span(base)
	xe := b.off(rb) + 1
	if one != nil {
		if _, ie := b.span(one); ie > xe {
			xe = ie
		}
	}
	for _, m := range many {
		if _, ie := b.span(m); ie > xe {
			xe = ie
		}
	}
	gt := b.node(kGenericType, xs, xe, f)
	b.add(gt, b.typ(base, fType))
	b.add(gt, b.typeArgsList(lb, rb, one, many))
	return gt
}

func (b *builder) typeArgsList(lb, rb token.Pos, one ast.Expr, many []ast.Expr) int32 {
	as := b.off(lb)
	ae := b.off(rb) + 1
	args := b.node(kTypeArgs, as, ae, fTypeArgs)
	if many != nil {
		for _, m := range many {
			is, ie := b.span(m)
			te := b.node(kTypeElem, is, ie, fNone)
			b.add(te, b.typ(m, fNone))
			b.add(args, te)
		}
		return args
	}
	is, ie := b.span(one)
	te := b.node(kTypeElem, is, ie, fNone)
	b.add(te, b.typ(one, fNone))
	b.add(args, te)
	return args
}

func (b *builder) elemNode(a ast.Expr, typeArg bool) int32 {
	if typeArg {
		return b.typ(a, fNone)
	}
	if cl, ok := a.(*ast.CompositeLit); ok {
		return b.compositeLit(cl)
	}
	return b.exprNode(a, fNone)
}

func (b *builder) stringNode(lit *ast.BasicLit, f Slot) int32 {
	s, e := b.span(lit)
	n := b.node(litKind(lit), s, e, f)
	b.stringBody(n, lit)
	return n
}

func (b *builder) stringBody(n int32, lit *ast.BasicLit) {
	v := lit.Value
	lo := int32(1)
	hi := max(int32(len(v))-1, lo)
	base := b.off(lit.Pos())

	if len(v) == 0 {
		return
	}
	if v[0] == '`' {
		b.add(n, b.node(kStringContent, base+lo, base+hi, fNone))
		return
	}
	i := lo
	for i < hi {
		if v[i] == '\\' {

			if i > lo {
				b.add(n, b.node(kStringContent, base+lo, base+i, fNone))
			}
			k := i + 2
			if i+1 < hi {
				switch v[i+1] {
				case 'x':
					k = i + 4
				case 'u':
					k = i + 6
				case 'U':
					k = i + 10
				case '0', '1', '2', '3', '4', '5', '6', '7':
					k = i + 4
				}
			}
			if k > hi {
				k = hi
			}
			b.add(n, b.node(kEscapeSequence, base+i, base+k, fNone))
			lo = k
			i = k
			continue
		}
		i++
	}
	if lo < hi {
		b.add(n, b.node(kStringContent, base+lo, base+hi, fNone))
	}
}

func litKind(lit *ast.BasicLit) NodeKind {
	switch lit.Kind {
	case token.INT:
		return kIntLit
	case token.FLOAT:
		return kFloatLit
	case token.IMAG:
		return kImaginaryLit
	case token.CHAR:
		return kRuneLit
	case token.STRING:
		if len(lit.Value) > 0 && lit.Value[0] == '`' {
			return kRawStr
		}
		return kInterpStr
	}
	return kIdentifier
}

func (b *builder) expr(e ast.Expr) int32 { return b.exprNode(e, fNone) }

func (b *builder) exprNode(e ast.Expr, f Slot) int32 {
	if e == nil {
		return noNode
	}
	s, en := b.span(e)
	switch t := e.(type) {
	case *ast.Ident:
		return b.node(kIdentifier, s, en, f)
	case *ast.BasicLit:
		if k := litKind(t); k == kInterpStr || k == kRawStr {
			return b.stringNode(t, f)
		}
		return b.node(litKind(t), s, en, f)
	case *ast.CompositeLit:
		n := b.node(kCompositeLit, s, en, f)
		if t.Type != nil {
			b.add(n, b.typ(t.Type, fType))
		}
		b.add(n, b.literalValue(t, fBody))
		return n
	case *ast.FuncLit:
		n := b.node(kFuncLit, s, en, f)
		if t.Type.TypeParams != nil {
			b.add(n, b.typeParams(t.Type.TypeParams))
		}
		if t.Type.Params != nil {
			b.add(n, b.paramList(t.Type.Params, fParameters))
		}
		b.add(n, b.resultList(t.Type.Results))
		b.add(n, b.block(t.Body, fBody))
		return n
	case *ast.ParenExpr:
		n := b.node(kParenthesized, s, en, f)
		b.add(n, b.exprNode(t.X, fNone))
		return n
	case *ast.SelectorExpr:
		n := b.node(kSelector, s, en, f)
		b.add(n, b.exprNode(t.X, fOperand))
		if t.Sel != nil {
			ss, se := b.span(t.Sel)
			b.add(n, b.node(kFieldIdent, ss, se, fSelectorField))
		}
		return n
	case *ast.IndexExpr:

		if n2, ok := b.typeInstantiation(s, en, f, t, []ast.Expr{t.Index}); ok {
			return n2
		}
		n := b.node(kIndexExpr, s, en, f)
		b.add(n, b.exprNode(t.X, fOperand))
		b.add(n, b.exprNode(t.Index, fIndex))
		return n
	case *ast.IndexListExpr:
		if n2, ok := b.typeInstantiation(s, en, f, t, t.Indices); ok {
			return n2
		}
		n := b.node(kIndexListExpr, s, en, f)
		b.add(n, b.exprNode(t.X, fOperand))
		for _, i := range t.Indices {
			b.add(n, b.exprNode(i, fIndex))
		}
		return n
	case *ast.SliceExpr:
		n := b.node(kSliceExpr, s, en, f)
		b.add(n, b.exprNode(t.X, fOperand))
		if t.Low != nil {
			b.add(n, b.exprNode(t.Low, fIndex))
		}
		if t.High != nil {
			b.add(n, b.exprNode(t.High, fIndex))
		}
		if t.Max != nil {
			b.add(n, b.exprNode(t.Max, fNone))
		}
		return n
	case *ast.TypeAssertExpr:
		if t.Type == nil {

			return b.switchValue(t.X)
		}
		n := b.node(kTypeAssert, s, en, f)
		b.add(n, b.exprNode(t.X, fOperand))
		b.add(n, b.typ(t.Type, fType))
		return n
	case *ast.CallExpr:
		return b.callExpr(t, f)
	case *ast.StarExpr:

		if ce, ok := t.X.(*ast.CallExpr); ok && len(ce.Args) == 1 {
			if pe, ok2 := ce.Fun.(*ast.ParenExpr); ok2 &&
				(isTypeLiteral(pe.X) || parenGeneric(pe.X)) {
				conv := b.node(kTypeConversion, s, en, f)
				ptr := b.node(kPointerType, s, b.off(pe.Rparen)+1, fType)
				pt := b.node(kParenType, b.off(pe.Lparen), b.off(pe.Rparen)+1, fNone)
				b.add(pt, b.typ(pe.X, fNone))
				b.add(ptr, pt)
				b.add(conv, ptr)
				b.add(conv, b.elemNode(ce.Args[0], false))
				return conv
			}
		}
		n := b.node(kUnaryExpr, s, en, f)
		if op := b.opTok(s, b.off(t.X.Pos()), "*"); op != noNode {
			b.add(n, op)
		}
		b.add(n, b.exprNode(t.X, fOperand))
		return n
	case *ast.UnaryExpr:
		n := b.node(kUnaryExpr, s, en, f)
		if op := b.opTok(s, b.off(t.X.Pos()), t.Op.String()); op != noNode {
			b.add(n, op)
		}
		b.add(n, b.exprNode(t.X, fOperand))
		return n
	case *ast.BinaryExpr:
		n := b.node(kBinaryExpr, s, en, f)
		b.add(n, b.exprNode(t.X, fLeft))
		if op := b.opTok(b.off(t.X.End()), b.off(t.Y.Pos()), t.Op.String()); op != noNode {
			b.add(n, op)
		}
		b.add(n, b.exprNode(t.Y, fRight))
		return n
	case *ast.KeyValueExpr:
		n := b.node(kKeyedElement, s, en, f)
		b.add(n, b.exprNode(t.Key, fKey))
		b.add(n, b.exprNode(t.Value, fValue))
		return n
	case *ast.Ellipsis:

		lo := b.off(t.Ellipsis)
		hi := b.off(t.Ellipsis) + 3
		if t.Elt != nil {
			if ep := b.off(t.Elt.Pos()); ep < lo {
				lo = ep
			}
			if ee := b.off(t.Elt.End()); ee > hi {
				hi = ee
			}
		}
		n := b.node(kVariadicArgument, lo, hi, f)
		b.add(n, b.typ(t.Elt, fNone))
		return n
	case *ast.ChanType, *ast.MapType, *ast.ArrayType, *ast.StructType,
		*ast.InterfaceType, *ast.FuncType:

		return b.typ(e, f)
	default:
		return b.node(kError, s, en, f)
	}
}

func (b *builder) litOrExpr(e ast.Expr) int32 {
	if cl, ok := e.(*ast.CompositeLit); ok {
		if cl.Type == nil {
			return b.literalValue(cl, fNone)
		}
		return b.compositeLit(cl)
	}
	return b.exprNode(e, fNone)
}

func (b *builder) literalValue(t *ast.CompositeLit, f Slot) int32 {
	bs := b.off(t.Lbrace)
	be := b.off(t.Rbrace) + 1
	lv := b.node(kLiteralValue, bs, be, f)
	for _, el := range t.Elts {
		es, ee := b.span(el)
		le := b.node(kLiteralElement, es, ee, fNone)
		if kv, ok := el.(*ast.KeyValueExpr); ok {
			ke := b.node(kKeyedElement, es, ee, fNone)
			ks, _ := b.span(kv.Key)
			kel := b.node(kLiteralElement, ks, b.off(kv.Key.End()), fKey)
			b.add(kel, b.litOrExpr(kv.Key))
			b.add(ke, kel)
			vs, _ := b.span(kv.Value)
			vel := b.node(kLiteralElement, vs, ee, fValue)
			if inner, ok := kv.Value.(*ast.CompositeLit); ok && inner.Type == nil {
				b.add(vel, b.literalValue(inner, fNone))
			} else if cl, ok := kv.Value.(*ast.CompositeLit); ok {
				cn := b.node(kCompositeLit, vs, ee, fNone)
				b.add(cn, b.typ(cl.Type, fType))
				b.add(cn, b.literalValue(cl, fNone))
				b.add(vel, cn)
			} else {
				b.add(vel, b.litOrExpr(kv.Value))
			}
			b.add(ke, vel)
			b.add(lv, ke)
			continue
		} else if inner, ok := el.(*ast.CompositeLit); ok {

			if inner.Type == nil {
				b.add(le, b.literalValue(inner, fNone))
			} else {
				cn := b.node(kCompositeLit, es, ee, fNone)
				b.add(cn, b.typ(inner.Type, fType))
				b.add(cn, b.literalValue(inner, fNone))
				b.add(le, cn)
			}
		} else {
			b.add(le, b.exprNode(el, fNone))
		}
		b.add(lv, le)
	}
	return lv
}

func (b *builder) callExpr(t *ast.CallExpr, f Slot) int32 {
	s, en := b.span(t)
	n := b.node(kCallExpr, s, en, f)

	switch ix := t.Fun.(type) {
	case *ast.IndexExpr:
		return b.genericCall(t, ix.X, ix.Lbrack, ix.Rbrack, ix.Index, nil, f)
	case *ast.IndexListExpr:
		return b.genericCall(t, ix.X, ix.Lbrack, ix.Rbrack, nil, ix.Indices, f)
	}
	if t.Fun != nil {
		switch fn := t.Fun.(type) {
		case *ast.ParenExpr:

			if isTypeLiteral(fn.X) || (len(t.Args) == 1 && parenGeneric(fn.X)) {
				b.t.nodes[n].kind = kTypeConversion
				pt := b.node(kParenType, b.off(fn.Lparen), b.off(fn.Rparen)+1, fType)
				b.add(pt, b.typ(fn.X, fNone))
				b.add(n, pt)
			} else {
				b.add(n, b.exprNode(fn, fFunction))
			}
		case *ast.StarExpr:
			if fn.X == nil {
				b.add(n, b.typ(t.Fun, fFunction))
			} else {
				b.add(n, b.exprNode(t.Fun, fFunction))
			}
		case *ast.ArrayType, *ast.MapType, *ast.ChanType, *ast.StructType,
			*ast.InterfaceType, *ast.FuncType:

			b.t.nodes[n].kind = kTypeConversion
			b.add(n, b.typ(t.Fun, fType))
		default:
			b.add(n, b.exprNode(t.Fun, fFunction))
		}
	}
	if b.t.nodes[n].kind == kTypeConversion {

		if len(t.Args) > 0 {
			b.add(n, b.elemNode(t.Args[0], false))
		}
		return n
	}
	b.add(n, b.argList(t, false))
	return n
}

func (b *builder) argList(t *ast.CallExpr, typeArgs bool) int32 {
	if !t.Rparen.IsValid() {
		return noNode
	}
	if id, ok := t.Fun.(*ast.Ident); ok {
		typeArgs = id.Name == "new" || id.Name == "make"
	}
	al := b.node(kArgList, b.off(t.Lparen), b.off(t.Rparen)+1, fArguments)
	for i, a := range t.Args {
		if i > 0 {
			typeArgs = false
		}
		if i == len(t.Args)-1 && t.Ellipsis.IsValid() {

			lo := b.off(a.Pos())
			hi := b.off(t.Ellipsis) + 3
			va := b.node(kVariadicArgument, lo, hi, fNone)
			b.add(va, b.elemNode(a, typeArgs))
			b.add(al, va)
			continue
		}
		b.add(al, b.elemNode(a, typeArgs))
	}
	return al
}

func (b *builder) compositeLit(t *ast.CompositeLit) int32 {
	s, en := b.span(t)
	n := b.node(kCompositeLit, s, en, fNone)
	if t.Type != nil {
		b.add(n, b.typ(t.Type, fType))
	}
	b.add(n, b.literalValue(t, fBody))
	return n
}

func (b *builder) block(blk *ast.BlockStmt, f Slot) int32 {
	s, e := b.span(blk)
	n := b.node(kBlock, s, e, f)
	if len(blk.List) == 0 {
		return n
	}
	sl := b.node(kStmtList, b.off(blk.List[0].Pos()), b.off(blk.Rbrace), fNone)
	b.add(n, sl)
	for _, st := range blk.List {
		b.add(sl, b.stmt(st))
	}
	return n
}

func (b *builder) caseBody(cn int32, body []ast.Stmt) {
	if len(body) == 0 {
		return
	}
	sl := b.node(kStmtList, b.off(body[0].Pos()), b.off(body[len(body)-1].End())+1, fNone)
	b.add(cn, sl)
	for _, st := range body {
		b.add(sl, b.stmt(st))
	}
}

func (b *builder) stmt(st ast.Stmt) int32 {
	if st == nil {
		return noNode
	}
	s, e := b.span(st)
	switch t := st.(type) {
	case *ast.ExprStmt:
		n := b.node(kExprStmt, s, e, fNone)
		if cl, ok := t.X.(*ast.CompositeLit); ok {
			b.add(n, b.compositeLit(cl))
		} else {
			b.add(n, b.exprNode(t.X, fNone))
		}
		return n
	case *ast.AssignStmt:
		k := kAssignStmt
		if t.Tok == token.DEFINE {
			k = kShortVarDecl
		}
		return b.assign(t, k, s, e, fNone)
	case *ast.DeclStmt:
		if gd, ok := t.Decl.(*ast.GenDecl); ok {
			return b.genDecl(gd)
		}
		return noNode
	case *ast.BlockStmt:
		return b.block(t, fNone)
	case *ast.IfStmt:
		n := b.node(kIfStmt, s, e, fNone)
		if t.Init != nil {
			b.add(n, b.stmtField(t.Init, fInitializer))
		}
		if t.Cond != nil {
			b.add(n, b.exprNode(t.Cond, fCondition))
		}
		b.add(n, b.block(t.Body, fConsequence))
		if t.Else != nil {
			b.add(n, b.stmtField(t.Else, fAlternative))
		}
		return n
	case *ast.ForStmt:
		n := b.node(kForStmt, s, e, fNone)

		hdr := n
		if b.forHasClauses(s, b.off(t.Body.Pos())) {
			hs := b.off(t.Body.Pos())
			if t.Init != nil {
				hs = b.off(t.Init.Pos())
			} else if t.Cond != nil {
				hs = b.off(t.Cond.Pos())
			} else if t.Post != nil {
				hs = b.off(t.Post.Pos())
			}
			he := b.off(t.Body.Pos())
			hdr = b.node(kForClause, hs, he, fNone)
			b.add(n, hdr)
		}
		if t.Init != nil {
			b.add(hdr, b.stmtField(t.Init, fInit))
		}
		if t.Cond != nil {
			b.add(hdr, b.exprNode(t.Cond, fCondition))
		}
		if t.Post != nil {
			b.add(hdr, b.stmtField(t.Post, fPost))
		}
		b.add(n, b.block(t.Body, fBody))
		return n
	case *ast.RangeStmt:
		n := b.node(kForStmt, s, e, fNone)

		rs := b.off(t.Body.Pos())
		for i := s + 3; i < b.off(t.Body.Pos()); i++ {
			if !isSpaceByte(b.t.src[i]) {
				rs = i
				break
			}
		}
		re := b.off(t.Body.Pos())
		if t.Key != nil {
			rs = minInt(rs, b.off(t.Key.Pos()))
		}
		if t.X != nil {
			rs = minInt(rs, b.off(t.X.Pos()))
		}
		if t.X != nil {
			re = b.off(t.X.End())
		}
		rc := b.node(kRangeClause, rs, re, fNone)
		if t.Key != nil {
			ks, _ := b.span(t.Key)
			ke := b.off(t.Key.End())
			if t.Value != nil {
				ke = b.off(t.Value.End())
			}
			el := b.node(kExprList, ks, ke, fLeft)
			b.add(el, b.exprNode(t.Key, fNone))
			if t.Value != nil {
				b.add(el, b.exprNode(t.Value, fNone))
			}
			b.add(rc, el)
		}
		if t.X != nil {
			b.add(rc, b.exprNode(t.X, fRight))
		}
		b.t.nodes[rc].end = b.off(t.Body.Pos())
		b.add(n, rc)
		b.add(n, b.block(t.Body, fBody))
		return n
	case *ast.SwitchStmt:
		n := b.node(kSwitchStmt, s, e, fNone)
		if t.Init != nil {
			b.add(n, b.stmtField(t.Init, fInitializer))
		}
		if t.Tag != nil {
			b.add(n, b.exprNode(t.Tag, fValue))
		}
		b.clauses(n, t.Body, kCaseClauseExpr)
		return n
	case *ast.TypeSwitchStmt:
		n := b.node(kTypeSwitchStmt, s, e, fNone)
		if t.Init != nil {
			b.add(n, b.stmtField(t.Init, fInitializer))
		}
		switch as := t.Assign.(type) {
		case *ast.AssignStmt:

			if len(as.Lhs) > 0 {
				ls, _ := b.span(as.Lhs[0])
				le := b.off(as.Lhs[len(as.Lhs)-1].End())
				el := b.node(kExprList, ls, le, fAlias)
				for _, l := range as.Lhs {
					b.add(el, b.exprNode(l, fNone))
				}
				b.add(n, el)
			}
			for _, r := range as.Rhs {
				b.add(n, b.switchValue(r))
			}
		case *ast.ExprStmt:
			b.add(n, b.switchValue(as.X))
		}
		b.clauses(n, t.Body, kCaseClauseType)
		return n
	case *ast.SelectStmt:
		n := b.node(kSelectStmt, s, e, fNone)
		b.clauses(n, t.Body, kCaseClauseComm)
		return n
	case *ast.ReturnStmt:
		n := b.node(kReturnStmt, s, e, fNone)
		if len(t.Results) > 0 {
			rs, _ := b.span(t.Results[0])
			re := b.off(t.Results[len(t.Results)-1].End())
			el := b.node(kExprList, rs, re, fNone)
			for _, r := range t.Results {
				if cl, ok := r.(*ast.CompositeLit); ok {
					b.add(el, b.compositeLit(cl))
				} else {
					b.add(el, b.exprNode(r, fNone))
				}
			}
			b.add(n, el)
		}
		return n
	case *ast.BranchStmt:
		var k NodeKind
		switch t.Tok {
		case token.BREAK:
			k = kBreakStmt
		case token.CONTINUE:
			k = kContinueStmt
		case token.GOTO:
			k = kGotoStmt
		default:
			k = kFallthroughStmt
		}
		n := b.node(k, s, e, fNone)
		if t.Label != nil {
			ls, le := b.span(t.Label)
			b.add(n, b.node(kLabelName, ls, le, fNone))
		}
		return n
	case *ast.IncDecStmt:
		k := kIncStmt
		if t.Tok == token.DEC {
			k = kDecStmt
		}
		n := b.node(k, s, e, fNone)
		b.add(n, b.exprNode(t.X, fNone))
		return n
	case *ast.SendStmt:
		n := b.node(kSendStmt, s, e, fNone)
		b.add(n, b.exprNode(t.Chan, fChannel))
		b.add(n, b.exprNode(t.Value, fValue))
		return n
	case *ast.LabeledStmt:
		n := b.node(kLabeledStmt, s, e, fNone)
		ls, le := b.span(t.Label)
		b.add(n, b.node(kLabelName, ls, le, fLabel))
		b.add(n, b.stmtField(t.Stmt, fNone))
		return n
	case *ast.GoStmt:
		n := b.node(kGoStmt, s, e, fNone)
		b.add(n, b.exprNode(t.Call, fNone))
		return n
	case *ast.DeferStmt:
		n := b.node(kDeferStmt, s, e, fNone)
		b.add(n, b.exprNode(t.Call, fNone))
		return n
	case *ast.EmptyStmt:
		return b.node(kEmptyStmt, s, e, fNone)
	default:
		return b.node(kError, s, e, fNone)
	}
}

func (b *builder) stmtField(st ast.Stmt, f Slot) int32 {
	n := b.stmt(st)
	if n != noNode {
		b.t.nodes[n].field = f
	}
	return n
}

func (b *builder) assign(t *ast.AssignStmt, k NodeKind, s, e int32, f Slot) int32 {
	n := b.node(k, s, e, f)
	if len(t.Lhs) > 0 {
		ls, _ := b.span(t.Lhs[0])
		le := b.off(t.Lhs[len(t.Lhs)-1].End())
		el := b.node(kExprList, ls, le, fLeft)
		for _, l := range t.Lhs {
			b.add(el, b.exprNode(l, fNone))
		}
		b.add(n, el)
	}
	if len(t.Rhs) > 0 {
		if len(t.Lhs) > 0 && t.Tok != token.DEFINE {
			if op := b.opTok(b.off(t.Lhs[len(t.Lhs)-1].End()),
				b.off(t.Rhs[0].Pos()), t.Tok.String()); op != noNode {
				b.add(n, op)
			}
		}
		rs, _ := b.span(t.Rhs[0])
		re := b.off(t.Rhs[len(t.Rhs)-1].End())
		el := b.node(kExprList, rs, re, fRight)
		for _, r := range t.Rhs {
			if cl, ok := r.(*ast.CompositeLit); ok {
				b.add(el, b.compositeLit(cl))
			} else {
				b.add(el, b.exprNode(r, fNone))
			}
		}
		b.add(n, el)
	}
	return n
}

func (b *builder) opTok(lo, lim int32, text string) int32 {
	if text == "" {
		return noNode
	}
	src := b.t.src
	hi := int32(len(src))
	if lim <= 0 || lim > hi {
		lim = hi
	}
	n := int32(len(text))
	lo = b.skipGap(lo, lim)
	if lo+n <= lim && string(src[lo:lo+n]) == text {
		return b.node(kOperator, lo, lo+n, fOperator)
	}

	for i := lo; i+n <= lim; i++ {
		if src[i] == text[0] && string(src[i:i+n]) == text {
			return b.node(kOperator, i, i+n, fOperator)
		}
	}
	if lo+n > hi {
		lo = hi - n
		if lo < 0 {
			return noNode
		}
	}
	return b.node(kOperator, lo, lo+n, fOperator)
}

func (b *builder) skipGap(lo, lim int32) int32 {
	src := b.t.src
	for lo < lim {
		if isSpaceByte(src[lo]) {
			lo++
			continue
		}
		if lo+1 < lim && src[lo] == '/' && src[lo+1] == '*' {
			i := lo + 2
			for i+1 < lim && !(src[i] == '*' && src[i+1] == '/') {
				i++
			}
			if i+1 < lim {
				lo = i + 2
				continue
			}

			return lim
		}
		if lo+1 < lim && src[lo] == '/' && src[lo+1] == '/' {
			i := lo + 2
			for i < lim && src[i] != '\n' {
				i++
			}
			lo = i
			continue
		}
		break
	}
	return lo
}

func minInt(a, b int32) int32 {
	if a < b {
		return a
	}
	return b
}

func isSpaceByte(c byte) bool {
	return c == ' ' || c == '\t' || c == '\n' || c == '\r'
}

func (b *builder) switchValue(e ast.Expr) int32 {
	if ta, ok := e.(*ast.TypeAssertExpr); ok && ta.Type == nil {
		return b.exprNode(ta.X, fValue)
	}
	return b.exprNode(e, fValue)
}

func (b *builder) forHasClauses(from, bodyEnd int32) bool {
	_, _, n := b.forHeader(from, bodyEnd)
	return n >= 2
}

func (b *builder) forHeader(from, bodyEnd int32) (int32, int32, int) {
	hi := min(bodyEnd, int32(len(b.t.src)))
	lo, last, n := hi, hi, 0
	for i := from + 3; i < hi; i++ {
		if b.t.src[i] != ';' {
			continue
		}
		if n == 0 {
			lo = i
		}
		last = i
		n++
	}
	return lo, last + 1, n
}

func (b *builder) clauses(n int32, body *ast.BlockStmt, kind NodeKind) {
	if body == nil {
		return
	}
	for _, cs := range body.List {
		cs2, ce := b.span(cs)
		switch c := cs.(type) {
		case *ast.CaseClause:
			k := kind
			if len(c.List) == 0 {
				k = kCaseDefault
			}
			cn := b.node(k, cs2, ce, fNone)
			if kind == kCaseClauseType {
				for _, ex := range c.List {
					b.add(cn, b.typ(ex, fType))
				}
			} else if len(c.List) > 0 {

				el := b.node(kExprList, b.off(c.List[0].Pos()),
					b.off(c.List[len(c.List)-1].End()), fValue)
				for _, v := range c.List {
					b.add(el, b.exprNode(v, fNone))
				}
				b.add(cn, el)
			}
			b.caseBody(cn, c.Body)
			b.add(n, cn)
		case *ast.CommClause:
			k := kCaseClauseComm
			if c.Comm == nil {
				k = kCaseDefault
			}
			cn := b.node(k, cs2, ce, fNone)
			if c.Comm != nil {

				switch cs := c.Comm.(type) {
				case *ast.ExprStmt:
					if u, ok := cs.X.(*ast.UnaryExpr); ok && u.Op == token.ARROW {
						rs := b.node(kReceiveStmt, b.off(cs.Pos()), b.off(cs.End()), fNone)
						b.add(rs, b.exprNode(u, fNone))
						b.add(cn, rs)
					} else {
						b.add(cn, b.stmtField(cs, fNone))
					}
				case *ast.AssignStmt:
					rs := b.node(kReceiveStmt, b.off(cs.Pos()), b.off(cs.End()), fNone)
					ls, _ := b.span(cs.Lhs[0])
					le := b.off(cs.Lhs[len(cs.Lhs)-1].End())
					el := b.node(kExprList, ls, le, fNone)
					for _, l := range cs.Lhs {
						b.add(el, b.exprNode(l, fNone))
					}
					b.add(rs, el)
					for _, r := range cs.Rhs {
						b.add(rs, b.exprNode(r, fNone))
					}
					b.add(cn, rs)
				default:
					b.add(cn, b.stmtField(c.Comm, fNone))
				}
			}
			b.caseBody(cn, c.Body)
			b.add(n, cn)
		}
	}
}

func (g *Graph) hazardRows(pat, modPat string, lim int, cols []string, keep func(h *Hazard, s int32) bool, emit func(h *Hazard, s int32) []cellVal) result {
	return g.hazardRowsF(pat, modPat, lim, cols, false, true, keep, emit)
}

func (g *Graph) hazardRowsF(pat, modPat string, lim int, cols []string, exclTest, exclGen bool, keep func(h *Hazard, s int32) bool, emit func(h *Hazard, s int32) []cellVal) result {
	r := result{cols: cols, lim: lim}
	for i := range g.Hazards {
		h := &g.Hazards[i]
		if !patMatch(g.Str.get(h.Pattern), pat) {
			continue
		}
		sid := h.SymbolID
		s := &g.Sym
		if !likePat(modName(g, s.ModuleId[sid]), modPat) {
			continue
		}
		if s.FileId[sid] < int32(len(g.File)) {
			f := &g.File[s.FileId[sid]]
			if (exclGen && f.IsGen != 0) || (exclTest && f.IsTest != 0) {
				continue
			}
		}
		if keep != nil && !keep(h, sid) {
			continue
		}
		r.rows = append(r.rows, emit(h, sid))
	}
	return r
}

func patMatch(v, pat string) bool {
	switch pat {
	case "":
		return true
	case "*":
		return true
	}
	if len(pat) > 2 && pat[0] == '\'' && pat[len(pat)-1] == '\'' {
		pat = pat[1 : len(pat)-1]
	}
	first := true
	for p := range strings.SplitSeq(pat, ",") {
		p = strings.TrimSpace(p)
		if p == "" && first {
			continue
		}
		first = false
		if p == v {
			return true
		}
	}
	return false
}

func modName(g *Graph, i int32) string {
	if i < 0 || i >= int32(len(g.Mod)) {
		return ""
	}
	return g.Mod[i].Name
}

func (g *Graph) inputSites(sid int32) (int32, string) {
	lo, hi := g.uinputCSR.row(sid)
	seen := map[string]bool{}
	var kinds []string
	var n int32
	for p := lo; p < hi; p++ {
		n++
		k := g.Str.get(g.UInput[p].Kind)
		if k == "" || seen[k] {
			continue
		}
		seen[k] = true
		kinds = append(kinds, k)
	}
	return n, joinInOrder(kinds)
}

func qImportCycle(g *Graph, pat string, lim int) result {
	r := result{cols: []string{"path", "cycle_size", "shortest_cycle", "at"}, lim: lim}

	adj := make([][]int32, len(g.File))
	for _, im := range g.Imports {
		if im.TargetID < 0 || im.External != 0 {
			continue
		}
		adj[im.FileID] = append(adj[im.FileID], im.TargetID)
	}
	seen := make([]int32, len(g.File))

	for f := range g.File {
		if g.File[f].IsTest != 0 {
			continue
		}
		start := int32(f)
		seen[f] = -1
		frontier := []int32{start}
		seen[f] = 0
		var cycleSize int32
		var shortest int32
		seenSet := map[int32]bool{start: true}
		for d := int32(0); d < 8 && len(frontier) > 0; d++ {
			var next []int32
			for _, cur := range frontier {
				for _, t := range adj[cur] {
					if t == start {
						if shortest == 0 {
							shortest = d + 1
						}
						cycleSize++
						continue
					}
					if !seenSet[t] {
						seenSet[t] = true
						next = append(next, t)
					}
				}
			}
			frontier = next
		}
		if cycleSize > 0 && shortest > 0 {
			r.rows = append(r.rows, row(nil, cs(g.File[f].Path), ci(int64(cycleSize)),
				ci(int64(shortest)), cs(g.File[f].Path+":0")))
		}
	}
	_ = seen
	return sortRows(r, 2, 1)
}

func qStringConcatInLoop(g *Graph, pat string, lim int) result {
	return result{cols: []string{"name", "concat_in_loop", "n_loops", "string_lits",
		"cyclo", "fan_in", "at"}, lim: lim}
}

func qUnsafePointerArith(g *Graph, pat string, lim int) result {
	r := result{cols: []string{"name", "unsafe_ops", "unsafe_calls", "cgo_calls",
		"reflect_ops", "fan_in", "cyclo", "at"}, lim: lim}
	s := &g.Sym
	for _, i := range g.matchedSyms(pat) {
		if s.NUnsafeOps[i] == 0 && s.NUnsafeCall[i] == 0 {
			continue
		}
		r.rows = append(r.rows, row(nil, cs(g.name(i)), ci(int64(s.NUnsafeOps[i])),
			ci(int64(s.NUnsafeCall[i])), ci(int64(s.NCgoCalls[i])),
			ci(int64(s.NReflectOps[i])), ci(int64(s.FanIn[i])),
			ci(int64(s.Cyclomatic[i])), cs(g.at(i))))
	}
	return sortRows(r, 5, 1)
}

func reachQuery(g *Graph, pat string, lim int, cols []string, seed func(i int32) bool,
	hops int32, keep func(i int32) bool, emit func(i int32, d int32) []cellVal,
	keys ...int) result {
	r := result{cols: cols, lim: lim}
	dist := g.reachFrom(seed, hops)
	for i := 0; i < g.Sym.n; i++ {
		if dist[i] < 0 || !keep(int32(i)) {
			continue
		}
		if !g.modOK(int32(i), g.Sym.FileId[i], pat) {
			continue
		}
		r.rows = append(r.rows, emit(int32(i), dist[i]))
	}
	return sortRows(r, keys...)
}

func qLogFatalInHandler(g *Graph, pat string, lim int) result {
	s := &g.Sym
	return reachQuery(g, pat, lim,
		[]string{"name", "fatal_calls", "exit_calls", "hops_from_handler", "fan_in", "at"},
		func(i int32) bool { return s.IsHandler[i] == 1 }, 4,
		func(i int32) bool { return s.NLogFatal[i] > 0 || s.NExitCall[i] > 0 },
		func(i int32, d int32) []cellVal {
			return row(nil, cs(g.name(i)), ci(int64(s.NLogFatal[i])),
				ci(int64(s.NExitCall[i])), ci(int64(d)), ci(int64(s.FanIn[i])), cs(g.at(i)))
		}, 1, 2)
}

func qTimeAfterInLoop(g *Graph, pat string, lim int) result {
	r := result{cols: []string{"name", "time_after_in_loop", "loops", "selects",
		"ctx_done", "fan_in", "at"}, lim: lim}
	s := &g.Sym
	for _, i := range g.symRows(pat) {
		if s.NTimeAfterInLoop[i] == 0 {
			continue
		}
		r.rows = append(r.rows, row(nil, cs(g.name(i)), ci(int64(s.NTimeAfterInLoop[i])),
			ci(int64(s.NLoops[i])), ci(int64(s.NSelect[i])), ci(int64(s.NCtxDone[i])),
			ci(int64(s.FanIn[i])), cs(g.at(i))))
	}
	return sortRows(r, 1, 2)
}

func qReflectCallSurface(g *Graph, pat string, lim int) result {
	r := result{cols: []string{"name", "reflect_ops", "reflect_calls",
		"unsafe_ops", "type_asserts", "fan_in", "handler", "at"}, lim: lim}
	s := &g.Sym
	for _, i := range g.matchedSyms(pat) {
		if s.NReflectCall[i] == 0 {
			continue
		}
		r.rows = append(r.rows, row(nil, cs(g.name(i)), ci(int64(s.NReflectOps[i])),
			ci(int64(s.NReflectCall[i])), ci(int64(s.NUnsafeOps[i])),
			ci(int64(s.NTypeAssert[i])), ci(int64(s.FanIn[i])),
			ci(int64(s.IsHandler[i])), cs(g.at(i))))
	}
	return sortRows(r, 5, 2)
}

func qEnvReadInHandler(g *Graph, pat string, lim int) result {
	s := &g.Sym
	return reachQuery(g, pat, lim,
		[]string{"name", "env_reads", "hops_from_handler", "fan_in", "cyclo", "at"},
		func(i int32) bool { return s.IsHandler[i] == 1 }, 4,
		func(i int32) bool { return s.NEnvRead[i] > 0 },
		func(i int32, d int32) []cellVal {
			return row(nil, cs(g.name(i)), ci(int64(s.NEnvRead[i])), ci(int64(d)),
				ci(int64(s.FanIn[i])), ci(int64(s.Cyclomatic[i])), cs(g.at(i)))
		}, 1, 2)
}

func qSelectWithoutDefault(g *Graph, pat string, lim int) result {
	r := result{cols: []string{"name", "selects", "defaults", "ctx_done_cases",
		"chan_sends", "chan_recvs", "goroutines", "fan_in", "at"}, lim: lim}
	s := &g.Sym
	for _, i := range g.symRows(pat) {
		if s.NSelect[i] == 0 || s.NSelectDefault[i] != 0 {
			continue
		}
		r.rows = append(r.rows, row(nil, cs(g.name(i)), ci(int64(s.NSelect[i])),
			ci(int64(s.NSelectDefault[i])), ci(int64(s.NSelectCtxDone[i])),
			ci(int64(s.NChanSend[i])), ci(int64(s.NChanRecv[i])),
			ci(int64(s.NGoroutines[i])), ci(int64(s.FanIn[i])), cs(g.at(i))))
	}
	return sortRows(r, 1, 6)
}

func qReadallInLoop(g *Graph, pat string, lim int) result {
	r := result{cols: []string{"name", "readall_in_loop", "loops", "io_in_loop",
		"alloc_in_loop", "cyclo", "fan_in", "at"}, lim: lim}
	s := &g.Sym
	for _, i := range g.symRows(pat) {
		if s.NReadallInLoop[i] == 0 {
			continue
		}
		r.rows = append(r.rows, row(nil, cs(g.name(i)), ci(int64(s.NReadallInLoop[i])),
			ci(int64(s.NLoops[i])), ci(0), ci(0), ci(int64(s.Cyclomatic[i])),
			ci(int64(s.FanIn[i])), cs(g.at(i))))
	}
	return sortRows(r, 1, 3)
}

func qIfaceSatisfactionBreadth(g *Graph, pat string, lim int) result {
	r := result{cols: []string{"type_name", "contracts", "test_contracts",
		"methods_matched", "iface_names"}, lim: lim}
	type acc struct {
		contracts, methods int32
		ids                map[int32]bool
		names              map[string]bool
	}
	by := map[string]*acc{}
	var order []string

	nameOK := make(map[string]bool, 1024)
	for i := 0; i < g.Sym.n; i++ {
		nm := g.name(int32(i))
		if !nameOK[nm] {
			nameOK[nm] = likePat(modName(g, g.Sym.ModuleId[i]), pat)
		}
	}
	inMod := func(t string) bool {
		return nameOK[t]
	}
	for i := range g.Impl {
		im := &g.Impl[i]
		if im.InTest != 0 {
			continue
		}
		t := g.Str.get(im.TypeName)
		if !inMod(t) {
			continue
		}
		a := by[t]
		if a == nil {
			a = &acc{ids: map[int32]bool{}, names: map[string]bool{}}
			by[t] = a
			order = append(order, t)
		}

		if !a.ids[im.InterfaceID] {
			a.ids[im.InterfaceID] = true
			a.contracts++
		}
		a.names[g.Str.get(im.InterfaceNam)] = true
		a.methods += im.NMethods
	}

	for _, t := range order {
		a := by[t]
		r.rows = append(r.rows, row(nil, cs(t), ci(int64(a.contracts)),
			ci(0), ci(int64(a.methods)), ci(int64(len(a.names)))))
	}
	return sortMixed(r, []bool{false, false, true}, 1, 3, 0)
}

func qConcurrencyHotspots(g *Graph, pat string, lim int) result {
	r := result{cols: []string{"name", "receiver", "spawns", "sends", "recvs",
		"closes", "spawns_in_loop", "wg_adds", "mutexes", "sloc", "at"}, lim: lim}
	s := &g.Sym
	for _, i := range g.symRows(pat) {

		k := g.kind(i)
		if k != "function" && k != "method" {
			continue
		}
		if g.File[s.FileId[i]].IsTest != 0 {
			continue
		}
		if s.NGoroutines[i]+s.NChanSend[i]+s.NChanRecv[i] == 0 {
			continue
		}
		score := s.NGoroutines[i]*4 + s.NChanSend[i] + s.NChanRecv[i]
		r.rows = append(r.rows, row(nil, cs(g.name(i)), cs(g.recv(i)),
			ci(int64(s.NGoroutines[i])), ci(int64(s.NChanSend[i])),
			ci(int64(s.NChanRecv[i])), ci(int64(s.NChanClose[i])),
			ci(int64(s.NGoInLoop[i])), ci(int64(s.NWaitgroupAdd[i])),
			ci(int64(s.NLock[i])), ci(int64(s.Sloc[i])), cs(g.at(i))))
		_ = score
	}
	return sortRows(r, 0)
}

func qUnusedExported(g *Graph, pat string, lim int) result {
	r := result{cols: []string{"name", "receiver", "sloc", "cyclo",
		"ext_calls", "at"}, lim: lim}
	s := &g.Sym
	implType := map[string]bool{}
	for i := range g.Impl {
		implType[g.Str.get(g.Impl[i].TypeName)] = true
	}
	for _, i := range g.symRows(pat) {
		k := g.kind(i)
		if k != "function" && k != "method" {
			continue
		}
		if s.FanIn[i] != 0 || s.IsPublic[i] == 0 || s.IsTest[i] != 0 ||
			s.IsEntrypoint[i] != 0 || s.IsHandler[i] != 0 || s.IsGenerated[i] != 0 {
			continue
		}
		if g.name(i) == "(anonymous)" || implType[g.recv(i)] {
			continue
		}
		r.rows = append(r.rows, row(nil, cs(g.name(i)), cs(g.recv(i)),
			ci(int64(s.Sloc[i])), ci(int64(s.Cyclomatic[i])),
			ci(int64(s.NExternalCalls[i])), cs(g.at(i))))
	}
	return sortRows(r, 2)
}

func qReceiverPointerMix(g *Graph, pat string, lim int) result {
	r := result{cols: []string{"receiver", "ptr_methods", "value_methods",
		"total_methods", "pct_ptr", "sample_path"}, lim: lim}
	type acc struct {
		ptr, val int32
		path     string
	}
	by := map[string]*acc{}
	var order []string
	for _, i := range g.symRows(pat) {
		if g.kind(i) != "method" {
			continue
		}
		rv := g.recv(i)
		if rv == "" {
			continue
		}
		a := by[rv]
		if a == nil {
			a = &acc{}
			by[rv] = a
			order = append(order, rv)
		}
		if g.Sym.ReceiverIsPointer[i] != 0 {
			a.ptr++
		} else {
			a.val++
		}
		if p := g.File[g.Sym.FileId[i]].Path; a.path == "" || p > a.path {
			a.path = p
		}
	}
	sort.Strings(order)
	for _, rv := range order {
		a := by[rv]
		if a.ptr == 0 || a.val == 0 {
			continue
		}
		tot := a.ptr + a.val
		r.rows = append(r.rows, row(nil, cs(rv), ci(int64(a.ptr)), ci(int64(a.val)),
			ci(int64(tot)), ci(int64(100*a.ptr/tot)), cs(a.path)))
	}
	return sortRows(r, 3, 4)
}

func qAbstractionReach(g *Graph, pat string, lim int) result {
	r := result{cols: []string{"iface_id", "iface", "methods", "exported",
		"implementors", "test_implementors", "implemented_by", "at"}, lim: lim}
	type acc struct {
		all, tests int32
		names      []string
		seen       map[string]bool
	}
	by := map[int32]*acc{}
	var order []int32
	for i := range g.Impl {
		im := &g.Impl[i]
		a := by[im.InterfaceID]
		if a == nil {
			a = &acc{seen: map[string]bool{}}
			by[im.InterfaceID] = a
			order = append(order, im.InterfaceID)
		}

		a.all++
		if im.InTest != 0 {
			a.tests++
		}
		tn := g.Str.get(im.TypeName)
		if !a.seen[tn] {
			a.seen[tn] = true
			a.names = append(a.names, tn)
		}
	}
	slices.Sort(order)
	for _, iid := range order {
		a := by[iid]
		lo, hi := g.ifaceCSR.row(iid)
		if lo == hi {
			continue
		}
		f := &g.Iface[g.ifaceCSR.idx[lo]]
		if f.Constraint != 0 || f.NMethods == 0 {
			continue
		}
		sid := f.SymbolID
		if !g.modOK(sid, g.Sym.FileId[sid], pat) {
			continue
		}
		r.rows = append(r.rows, row(nil, ci(int64(sid+1)), cs(g.name(sid)),
			ci(int64(f.NMethods)), ci(int64(f.Exported)), ci(int64(a.all)),
			ci(int64(a.tests)), cs(joinDistinct(a.names)), cs(g.at(sid))))
	}
	return sortRows(r, 4, 2)
}

func qInternalPackageLeak(g *Graph, pat string, lim int) result {
	r := result{cols: []string{"imported", "alias", "importer_path",
		"import_file", "line", "external"}, lim: lim}
	for i := range g.Imports {
		im := &g.Imports[i]
		t := g.Str.get(im.Target)
		if !strings.Contains(t, "/internal/") || im.TargetID < 0 || im.External != 0 {
			continue
		}
		fid := im.FileID
		if !likePat(modName(g, g.File[fid].ModuleID), pat) {
			continue
		}
		alias := cnull
		if im.Alias != nullStr {
			alias = cs(g.Str.get(im.Alias))
		}
		r.rows = append(r.rows, row(nil, cs(t), alias,
			cs(g.File[fid].Path), cs(g.File[im.TargetID].Path),
			ci(int64(im.Line)), ci(int64(im.External))))
	}
	return sortRows(r, 2, 4)
}

func qModuleDependencyDepth(g *Graph, pat string, lim int) result {
	r := result{cols: []string{"package_", "chain_depth", "direct_imports",
		"transitive_deps", "n_fns"}, lim: lim}
	s := &g.Sym
	for i := range g.Mod {
		m := &g.Mod[i]
		if !m.HasDep || m.Depth == 0 || !likePat(m.Name, pat) {
			continue
		}
		var n int32
		for j := 0; j < s.n; j++ {
			if s.ModuleId[j] == int32(i) {
				k := g.kind(int32(j))
				if k == "function" || k == "method" {
					n++
				}
			}
		}
		r.rows = append(r.rows, row(nil, cs(m.Name), ci(int64(m.Depth)),
			ci(int64(m.NDirect)), ci(int64(m.NTrans)), ci(int64(n))))
	}
	return sortRows(r, 3, 2)
}

func qErrorFanOut(g *Graph, pat string, lim int) result {
	r := result{cols: []string{"name", "receiver", "max_depth", "err_returns",
		"checks", "ignored", "fan_in", "sloc", "at"}, lim: lim}
	s := &g.Sym
	for _, e := range g.ErrChain {
		sid := e.SymbolID
		if s.NErrReturns[sid] == 0 || !g.modOK(sid, s.FileId[sid], pat) {
			continue
		}
		r.rows = append(r.rows, row(nil, cs(g.name(sid)), cs(g.recv(sid)),
			ci(int64(e.MaxDepth)), ci(int64(s.NErrReturns[sid])),
			ci(int64(s.NErrChecks[sid])), ci(int64(s.NErrIgnored[sid])),
			ci(int64(s.FanIn[sid])), ci(int64(s.Sloc[sid])), cs(g.at(sid))))
	}
	return sortRows(r, 2, 6)
}

func qCommandExecSurface(g *Graph, pat string, lim int) result {
	r := g.hazardRows("exec.Command,exec.CommandContext,syscall.Exec", pat, lim,
		[]string{"path", "caller", "sink", "sites", "first_line", "fan_in"},
		nil, func(h *Hazard, sid int32) []cellVal {
			return row(nil, cs(g.File[g.Sym.FileId[sid]].Path), cs(g.name(sid)),
				cs(g.Str.get(h.Pattern)), ci(int64(h.N)), ci(int64(h.Line)),
				ci(int64(g.Sym.FanIn[sid])))
		})
	return sortMixed(r, []bool{false, false, true}, 5, 3, 2)
}

func qSensitiveLogSurface(g *Graph, pat string, lim int) result {
	r := g.hazardRowsF("log.Fatal,log.Fatalf,log.Fatalln,log.Panic,log.Panicf", pat, lim,
		[]string{"path", "caller", "sink", "sites", "env_reads"}, true, true,
		func(h *Hazard, sid int32) bool { return g.Sym.NEnvRead[sid] > 0 },
		func(h *Hazard, sid int32) []cellVal {
			return row(nil, cs(g.File[g.Sym.FileId[sid]].Path), cs(g.name(sid)),
				cs(g.Str.get(h.Pattern)), ci(int64(h.N)), ci(int64(g.Sym.NEnvRead[sid])))
		})
	return sortRows(r, 3, 4)
}

func qOpenRedirectSurface(g *Graph, pat string, lim int) result {
	r := result{cols: []string{"name", "redirect_calls", "input_sites",
		"kinds", "fan_in", "at"}, lim: lim}
	s := &g.Sym
	for _, i := range g.symRows(pat) {
		if s.NRedirect[i] == 0 || g.File[s.FileId[i]].IsGen != 0 {
			continue
		}
		n, kinds := g.inputSites(i)
		if n == 0 {
			continue
		}
		r.rows = append(r.rows, row(nil, cs(g.name(i)), ci(int64(s.NRedirect[i])),
			ci(int64(n)), cs(kinds), ci(int64(s.FanIn[i])), cs(g.at(i))))
	}
	return sortRows(r, 4, 1)
}

func qHardcodedSecrets(g *Graph, pat string, lim int) result {
	r := result{cols: []string{"name", "candidate", "line", "at"}, lim: lim}
	s := &g.Sym
	for i := range g.Secret {
		sc := &g.Secret[i]
		v := g.Str.get(sc.Value)
		if strings.HasPrefix(v, "/") || strings.ContainsAny(v, "|%") {
			continue
		}
		f := &g.File[sc.FileID]
		if f.IsTest != 0 || f.IsGen != 0 || !likePat(modName(g, s.ModuleId[sc.SymbolID]), pat) {
			continue
		}
		r.krow([]int64{int64(len(v))}, cs(g.name(sc.SymbolID)), cs(v),
			ci(int64(sc.Line)), cs(g.atRow(sc.FileID, sc.Line)))
	}

	return sortKeys(r, []bool{false})
}

func inputSurface(g *Graph, pat string, lim int, cols []string, metric string,
	wantBody bool) result {
	r := result{cols: cols, lim: lim}
	s := &g.Sym
	col := s.NDeserialize
	colName := metric
	for _, i := range g.symRows(pat) {
		if s.IsGenerated[i] != 0 {
			continue
		}
		if colName == "dynamic_open" {
			col = s.NDynamicOpen
		}
		if col[i] == 0 {
			continue
		}
		var n int32
		var kinds []string
		seen := map[string]bool{}
		lo, hi := g.uinputCSR.row(i)
		for p := lo; p < hi; p++ {
			u := &g.UInput[p]
			if wantBody && g.Str.get(u.Kind) != "body" {
				continue
			}
			n++
			if k := g.Str.get(u.Kind); !seen[k] {
				seen[k] = true
				kinds = append(kinds, k)
			}
		}
		if n == 0 {
			continue
		}
		switch metric {
		case "redirect":
			r.rows = append(r.rows, row(nil, cs(g.name(i)), ci(int64(col[i])),
				ci(int64(n)), cs(joinDistinct(kinds)), ci(int64(s.FanIn[i])), cs(g.at(i))))
		case "body":
			r.rows = append(r.rows, row(nil, cs(g.name(i)), ci(int64(col[i])),
				ci(int64(n)), cs(g.at(i))))
		default:
			r.rows = append(r.rows, row(nil, cs(g.name(i)), ci(int64(col[i])),
				ci(int64(n)), cs(joinDistinct(kinds)), cs(g.at(i))))
		}
	}
	switch metric {
	case "redirect":
		return sortRows(r, 4, 1)
	case "body":
		return sortRows(r, 1, 2)
	}
	return sortRows(r, 1, 2)
}

func qUntrustedDeserialization(g *Graph, pat string, lim int) result {
	return inputSurface(g, pat, lim, []string{"name", "decode_calls", "input_sites",
		"kinds", "at"}, "deserialize", false)
}

func qPathTraversalSurface(g *Graph, pat string, lim int) result {
	return inputSurface(g, pat, lim, []string{"name", "open_sites", "input_sites",
		"kinds", "at"}, "dynamic_open", false)
}

func qMassAssignmentSurface(g *Graph, pat string, lim int) result {
	return inputSurface(g, pat, lim, []string{"name", "decode_calls", "body_reads",
		"at"}, "body", true)
}

func qUnauthenticatedInput(g *Graph, pat string, lim int) result {
	r := result{cols: []string{"name", "input_sites", "kinds", "at"}, lim: lim}
	s := &g.Sym
	for _, i := range g.matchedSyms(pat) {
		if s.NAuthCall[i] != 0 || g.inGenFile(i) {
			continue
		}
		n, kinds := g.inputSites(i)
		if n == 0 {
			continue
		}
		r.krow([]int64{int64(n), int64(s.Sloc[i])}, cs(g.name(i)), ci(int64(n)),
			cs(kinds), cs(g.at(i)))
	}

	return sortKeys(r, []bool{false, false})
}

func qDeprecatedStdlib(g *Graph, pat string, lim int) result {
	rep := map[string]string{"ioutil.ReadAll": "io.ReadAll", "ioutil.ReadFile": "os.ReadFile"}
	r := result{cols: []string{"path", "caller", "pattern", "replacement", "n"},
		lim: lim}
	for i := range g.Hazards {
		h := &g.Hazards[i]
		p := g.Str.get(h.Pattern)
		repl, ok := rep[p]
		if !ok {
			continue
		}
		sid := h.SymbolID
		if g.File[g.Sym.FileId[sid]].IsGen != 0 ||
			!likePat(modName(g, g.Sym.ModuleId[sid]), pat) {
			continue
		}
		r.rows = append(r.rows, row(nil, cs(g.File[g.Sym.FileId[sid]].Path),
			cs(g.name(sid)), cs(p), cs(repl), ci(int64(h.N))))
	}
	return sortRows(r, 4)
}

func qDeferredCloseUnchecked(g *Graph, pat string, lim int) result {
	r := result{cols: []string{"path", "name", "target", "line", "fan_in"}, lim: lim}
	s := &g.Sym
	for i := range g.Defers {
		d := &g.Defers[i]
		if d.IsClose == 0 || d.InLoop != 0 {
			continue
		}
		sid := d.SymbolID
		if g.File[s.FileId[sid]].IsGen != 0 || !likePat(modName(g, s.ModuleId[sid]), pat) {
			continue
		}
		r.rows = append(r.rows, row(nil, cs(g.File[s.FileId[sid]].Path),
			cs(g.name(sid)), cs(g.Str.get(d.Target)), ci(int64(d.Line)),
			ci(int64(s.FanIn[sid]))))
	}
	return sortRows(r, 4)
}

func qHTTPRequestNoContext(g *Graph, pat string, lim int) result {
	r := g.hazardRows("http.NewRequest", pat, lim,
		[]string{"path", "caller", "sites", "first_line", "fan_in"}, nil,
		func(h *Hazard, sid int32) []cellVal {
			return row(nil, cs(g.File[g.Sym.FileId[sid]].Path), cs(g.name(sid)),
				ci(int64(h.N)), ci(int64(h.Line)), ci(int64(g.Sym.FanIn[sid])))
		})
	return sortRows(r, 4, 2)
}

func qFileReadSurface(g *Graph, pat string, lim int) result {
	r := g.hazardRows("os.ReadFile,os.Open,ioutil.ReadFile", pat, lim,
		[]string{"path", "caller", "api", "sites", "first_line", "fan_in"}, nil,
		func(h *Hazard, sid int32) []cellVal {
			return row(nil, cs(g.File[g.Sym.FileId[sid]].Path), cs(g.name(sid)),
				cs(g.Str.get(h.Pattern)), ci(int64(h.N)), ci(int64(h.Line)),
				ci(int64(g.Sym.FanIn[sid])))
		})
	return sortMixed(r, []bool{false, false, true}, 5, 3, 2)
}

func qSQLInjectionBuild(g *Graph, pat string, lim int) result {
	r := result{cols: []string{"name", "receiver", "concat_sql", "query_in_loop",
		"fan_in", "at"}, lim: lim}
	s := &g.Sym
	for _, i := range g.symRows(pat) {
		if s.NSqlConcat[i] == 0 {
			continue
		}
		r.rows = append(r.rows, row(nil, cs(g.name(i)), cs(g.recv(i)),
			ci(int64(s.NSqlConcat[i])), ci(int64(s.QueryInLoop[i])),
			ci(int64(s.FanIn[i])), cs(g.at(i))))
	}
	return sortRows(r, 2, 4)
}

func qContextBuiltInLoop(g *Graph, pat string, lim int) result {
	r := result{cols: []string{"name", "in_loop", "depth", "ctx_creations",
		"fan_in", "at"}, lim: lim}
	s := &g.Sym
	for _, i := range g.symRows(pat) {
		if s.NCtxInLoop[i] == 0 {
			continue
		}
		r.rows = append(r.rows, row(nil, cs(g.name(i)), ci(int64(s.NCtxInLoop[i])),
			ci(int64(s.MaxLoopDepth[i])), ci(int64(s.NCtxWithcancel[i])),
			ci(int64(s.FanIn[i])), cs(g.at(i))))
	}
	return sortRows(r, 1, 4)
}

func qNilErrorAfterCheck(g *Graph, pat string, lim int) result {
	r := result{cols: []string{"name", "receiver", "dropped", "checks",
		"err_returns", "fan_in", "at"}, lim: lim}
	s := &g.Sym
	for _, i := range g.symRows(pat) {
		if s.NErrNilReturn[i] == 0 {
			continue
		}
		r.rows = append(r.rows, row(nil, cs(g.name(i)), cs(g.recv(i)),
			ci(int64(s.NErrNilReturn[i])), ci(int64(s.NErrChecks[i])),
			ci(int64(s.NErrReturns[i])), ci(int64(s.FanIn[i])), cs(g.at(i))))
	}
	return sortRows(r, 2, 5)
}

func qLoopvarRebindDead(g *Graph, pat string, lim int) result {
	r := result{cols: []string{"name", "rebinds", "depth", "fan_in", "at"}, lim: lim}
	s := &g.Sym

	maj, minor := int32(0), int32(0)
	if v := g.Meta["go_version"]; v != "" {
		parts := strings.SplitN(v, ".", 3)
		maj, _ = atoi(parts[0])
		if len(parts) > 1 {
			minor, _ = atoi(parts[1])
		}
	}
	if maj*100+minor < 122 {
		return r
	}
	for _, i := range g.symRows(pat) {
		if s.NLoopvarRebind[i] == 0 {
			continue
		}
		r.rows = append(r.rows, row(nil, cs(g.name(i)), ci(int64(s.NLoopvarRebind[i])),
			ci(int64(s.MaxLoopDepth[i])), ci(int64(s.FanIn[i])), cs(g.at(i))))
	}
	return sortRows(r, 1, 3)
}

func qInsecureTLS(g *Graph, pat string, lim int) result {
	r := result{cols: []string{"name", "insecure_cfgs", "fan_in", "at"}, lim: lim}
	s := &g.Sym
	for _, i := range g.symRows(pat) {
		if s.NInsecureTls[i] == 0 {
			continue
		}
		r.rows = append(r.rows, row(nil, cs(g.name(i)), ci(int64(s.NInsecureTls[i])),
			ci(int64(s.FanIn[i])), cs(g.at(i))))
	}
	return sortRows(r, 1, 2)
}

type wgOps struct {
	adds, dones, waits int32
}

func (g *Graph) wgTally() (map[[2]int32]*wgOps, [][2]int32) {
	by := map[[2]int32]*wgOps{}
	var order [][2]int32
	for i := range g.WgSites {
		w := &g.WgSites[i]
		k := [2]int32{w.SymbolID, hash32(g.Str.get(w.Var))}
		a := by[k]
		if a == nil {
			a = &wgOps{}
			by[k] = a
			order = append(order, k)
		}
		switch g.Str.get(w.Op) {
		case "Add":
			a.adds++
		case "Done":
			a.dones++
		case "Wait":
			a.waits++
		}
	}
	return by, order
}

func hash32(s string) int32 {
	var h uint32 = 2166136261
	for i := 0; i < len(s); i++ {
		h ^= uint32(s[i])
		h *= 16777619
	}
	return int32(h & 0x3fffffff)
}

func (g *Graph) targetSyms(name string) []int32 {
	if name == "" {
		return nil
	}
	if g.tgtIdx == nil {
		idx := make(map[string][]int32, g.Sym.n/8)
		for i := 0; i < g.Sym.n; i++ {
			k := g.kind(int32(i))
			if k != "function" && k != "method" {
				continue
			}
			f := &g.File[g.Sym.FileId[i]]
			if f.IsTest != 0 || f.IsGen != 0 {
				continue
			}
			nm := g.name(int32(i))
			idx[nm] = append(idx[nm], int32(i))
		}
		g.tgtIdx = idx
	}
	return g.tgtIdx[name]
}

func qWaitgroupAddInsideGoroutine(g *Graph, pat string, lim int) result {
	r := result{cols: []string{"spawner", "at", "add_site", "adds", "fan_in"},
		lim: lim}
	type site struct {
		sym int32
		n   int32
	}
	closureAdds := map[int32]int32{}
	targetAdds := map[int32]int32{}
	for i := range g.WgSites {
		w := &g.WgSites[i]
		if g.Str.get(w.Op) != "Add" {
			continue
		}
		if w.InGoroutine != 0 {
			closureAdds[w.SymbolID]++
		} else {
			targetAdds[w.SymbolID]++
		}
	}
	for i := range g.Goro {
		o := &g.Goro[i]
		if o.HasWG == 0 || g.File[o.FileID].IsTest != 0 || g.File[o.FileID].IsGen != 0 {
			continue
		}
		if !likePat(modName(g, g.Sym.ModuleId[o.SymbolID]), pat) {
			continue
		}
		sp := o.SymbolID
		at := g.atRow(o.FileID, o.Line)
		if n := closureAdds[sp]; n > 0 {
			r.rows = append(r.rows, row(nil, cs(g.name(sp)), cs(at), cs("(closure)"),
				ci(int64(n)), ci(int64(g.Sym.FanIn[sp]))))
		}
		for _, t := range g.targetSyms(g.Str.get(o.Target)) {
			if n := targetAdds[t]; n > 0 {
				r.rows = append(r.rows, row(nil, cs(g.name(sp)), cs(at), cs(g.name(t)),
					ci(int64(n)), ci(int64(g.Sym.FanIn[sp]))))
			}
		}
	}
	_ = site{}
	return sortRows(r, 3, 4)
}

func qWaitgroupDoneMissing(g *Graph, pat string, lim int) result {
	r := result{cols: []string{"spawner", "at", "target_fn", "target_fan_in"}, lim: lim}

	dones := map[int32]bool{}
	for i := range g.WgSites {
		if g.Str.get(g.WgSites[i].Op) == "Done" {
			dones[g.WgSites[i].SymbolID] = true
		}
	}
	for i := range g.Defers {
		if g.Defers[i].IsDone != 0 {
			dones[g.Defers[i].SymbolID] = true
		}
	}
	for _, e := range g.edgeList {
		if dones[e.Callee] {
			dones[e.Caller] = true
		}
	}
	for i := range g.Goro {
		o := &g.Goro[i]
		if o.HasWG == 0 || g.Str.get(o.Target) == "" {
			continue
		}
		f := &g.File[o.FileID]
		if f.IsTest != 0 || f.IsGen != 0 ||
			!likePat(modName(g, g.Sym.ModuleId[o.SymbolID]), pat) {
			continue
		}
		for _, t := range g.targetSyms(g.Str.get(o.Target)) {
			if dones[t] {
				continue
			}
			r.rows = append(r.rows, row(nil, cs(g.name(o.SymbolID)),
				cs(g.atRow(o.FileID, o.Line)), cs(g.name(t)),
				ci(int64(g.Sym.FanIn[t]))))
		}
	}
	return sortRows(r, 3)
}

func qWaitgroupImbalance(g *Graph, pat string, lim int) result {
	r := result{cols: []string{"fn", "wg_var", "adds", "dones", "waits",
		"unbalanced", "fan_in", "at"}, lim: lim}
	by, order := g.wgTally()
	delegated := map[int32]bool{}
	for i := range g.Goro {
		if g.Goro[i].HasWG != 0 {
			delegated[g.Goro[i].SymbolID] = true
		}
	}
	wgVar := make(map[[2]int32]uint32, len(g.WgSites))
	for i := range g.WgSites {
		w := &g.WgSites[i]
		wgVar[[2]int32{w.SymbolID, hash32(g.Str.get(w.Var))}] = w.Var
	}
	for _, k := range order {
		a := by[k]
		if a.adds <= a.dones+a.waits || delegated[k[0]] {
			continue
		}
		sid := k[0]
		f := &g.File[g.Sym.FileId[sid]]
		if f.IsTest != 0 || f.IsGen != 0 || !likePat(modName(g, g.Sym.ModuleId[sid]), pat) {
			continue
		}

		r.rows = append(r.rows, row(nil, cs(g.name(sid)), cs(g.Str.get(wgVar[k])),
			ci(int64(a.adds)), ci(int64(a.dones)), ci(int64(a.waits)),
			ci(int64(a.adds-a.dones)), ci(int64(g.Sym.FanIn[sid])), cs(g.at(sid))))
	}
	return sortRows(r, 5, 6)
}

func qDoubleLockSameReceiver(g *Graph, pat string, lim int) result {
	r := result{cols: []string{"outer_fn", "recv", "inner_fn", "inner_line",
		"outer_locks", "inner_locks", "cyclo", "fan_in", "at"}, lim: lim}
	s := &g.Sym
	for _, mo := range g.symRows(pat) {
		if s.NLockCall[mo] == 0 || g.recv(mo) == "" || s.IsGenerated[mo] != 0 {
			continue
		}
		lo, hi := g.Calls.Out.row(mo)
		for p := lo; p < hi; p++ {
			mi := g.Calls.Out.val[p].Callee
			if mi == mo || s.NLockCall[mi] == 0 || g.recv(mi) != g.recv(mo) {
				continue
			}
			r.rows = append(r.rows, row(nil, cs(g.name(mo)), cs(g.recv(mo)),
				cs(g.name(mi)), ci(int64(s.LineStart[mi])),
				ci(int64(s.NLockCall[mo])), ci(int64(s.NLockCall[mi])),
				ci(int64(s.Cyclomatic[mo])), ci(int64(s.FanIn[mo])), cs(g.at(mo))))
		}
	}
	return sortRows(r, 4, 5, 7)
}

func qOSExitUnderCallTree(g *Graph, pat string, lim int) result {
	r := result{cols: []string{"exit_fn", "at", "n_exit_call", "n_log_fatal",
		"entry_reachable", "defers_skipped_near", "fan_in"}, lim: lim}
	s := &g.Sym
	dist := g.reachFrom(func(i int32) bool {
		return s.IsHandler[i] == 1 || s.IsEntrypoint[i] == 1
	}, 8)

	near := map[int32]int32{}
	for i := 0; i < s.n; i++ {
		if dist[i] < 0 {
			continue
		}
		lo, hi := g.Calls.In.row(int32(i))
		for p := lo; p < hi; p++ {
			near[g.Calls.In.val[p].Callee] += s.NDefer[i]
		}
	}
	for i := 0; i < s.n; i++ {
		if dist[i] < 0 || (s.NExitCall[i] == 0 && s.NLogFatal[i] == 0) {
			continue
		}

		if g.File[s.FileId[i]].IsTest != 0 || g.File[s.FileId[i]].IsGen != 0 {
			continue
		}
		if s.IsGenerated[i] != 0 || !likePat(modName(g, s.ModuleId[i]), pat) {
			continue
		}
		r.rows = append(r.rows, row(nil, cs(g.name(int32(i))), cs(g.at(int32(i))),
			ci(int64(s.NExitCall[i])), ci(int64(s.NLogFatal[i])), ci(1),
			ci(int64(near[int32(i)])), ci(int64(s.FanIn[i]))))
	}
	return sortRows(r, 4, 5, 6)
}

func qLockHeldAcrossIO(g *Graph, pat string, lim int) result {
	r := result{cols: []string{"lock_fn", "io_callees", "max_hops", "locks",
		"unlocks", "fan_in", "at"}, lim: lim}
	s := &g.Sym
	type acc struct {
		n, maxHops int32
		seen       map[int32]bool
	}
	for root := 0; root < s.n; root++ {
		if s.NLockCall[root] == 0 {
			continue
		}
		rf := &g.File[s.FileId[root]]
		if rf.IsTest != 0 || rf.IsGen != 0 {
			continue
		}
		a := &acc{seen: map[int32]bool{}}

		g.reachWithin(int32(root), 3, func(i int32, d int32) {
			if d == 0 {
				return
			}
			if s.NNet[i]+s.NSql[i]+s.NExec[i]+s.NIo[i] == 0 {
				return
			}
			if g.File[s.FileId[i]].IsTest != 0 {
				return
			}
			if !a.seen[i] {
				a.seen[i] = true
				a.n++
			}
			if d > a.maxHops {
				a.maxHops = d
			}
		})
		if a.n == 0 || !likePat(modName(g, g.Sym.ModuleId[root]), pat) {
			continue
		}
		r.rows = append(r.rows, row(nil, cs(g.name(int32(root))), ci(int64(a.n)),
			ci(int64(a.maxHops)), ci(int64(s.NLockCall[root])),
			ci(int64(s.NUnlockCall[root])), ci(int64(s.FanIn[root])),
			cs(g.at(int32(root)))))
	}
	return sortRows(r, 1, 2, 5)
}

func (g *Graph) reachWithin(root, maxHops int32, visit func(sym, depth int32)) {
	visit(root, 0)
	seen := map[int32]int32{}
	frontier := []int32{root}
	for d := int32(1); d <= maxHops && len(frontier) > 0; d++ {
		var next []int32
		for _, u := range frontier {
			lo, hi := g.Calls.Out.row(u)
			for p := lo; p < hi; p++ {
				e := &g.Calls.Out.val[p]
				if e.IsSelf != 0 {
					continue
				}
				c := e.Callee
				if seen[c] >= d {
					continue
				}
				seen[c] = d
				visit(c, d)
				next = append(next, c)
			}
		}
		frontier = next
	}
}

func qLockHeldAcrossDynamic(g *Graph, pat string, lim int) result {

	r := result{cols: []string{"lock_fn", "locks", "dyn_calls", "iface_params",
		"n_iface_returns", "cyclo", "fan_in", "at"}, lim: lim}
	s := &g.Sym
	for _, i := range g.symRows(pat) {
		if s.NLockCall[i] == 0 || s.NDynamicCalls[i] == 0 {
			continue
		}
		if s.NIfaceParams[i]+s.NIfaceReturns[i] == 0 || g.inGenFile(i) {
			continue
		}
		r.rows = append(r.rows, row(nil, cs(g.name(i)), ci(int64(s.NLockCall[i])),
			ci(int64(s.NDynamicCalls[i])), ci(int64(s.NIfaceParams[i])),
			ci(int64(s.NIfaceReturns[i])), ci(int64(s.Cyclomatic[i])),
			ci(int64(s.FanIn[i])), cs(g.at(i))))
	}
	return sortRows(r, 0)
}

var closerTypes = []string{"sql.Rows", "sql.Stmt", "sql.Tx", "http.Response",
	"io.ReadCloser", "io.Closer", "*os.File"}

func qResourceNeverClosed(g *Graph, pat string, lim int) result {
	r := result{cols: []string{"opener", "return_type", "opener_fan_in",
		"caller_never_closes", "defer_closes", "at"}, lim: lim}
	s := &g.Sym
	for i := 0; i < s.n; i++ {
		rt := g.Str.get(s.ReturnType[i])
		if rt == "" {
			continue
		}
		hit := false
		for _, t := range closerTypes {
			if strings.Contains(rt, t) {
				hit = true
				break
			}
		}
		if !hit {
			continue
		}
		f := &g.File[s.FileId[i]]
		if f.IsTest != 0 || f.IsGen != 0 {
			continue
		}
		lo, hi := g.Calls.In.row(int32(i))
		seen := map[int32]bool{}
		for p := lo; p < hi; p++ {
			c := g.Calls.In.val[p].Callee
			if seen[c] || s.NDeferClose[c] != 0 || s.NCloseCall[c] != 0 {
				continue
			}
			seen[c] = true
			cf := &g.File[s.FileId[c]]
			if cf.IsTest != 0 || cf.IsGen != 0 || !likePat(modName(g, s.ModuleId[c]), pat) {
				continue
			}
			r.rows = append(r.rows, row(nil, cs(g.name(int32(i))), cs(rt),
				ci(int64(s.FanIn[i])), cs(g.name(c)), ci(int64(s.NDeferClose[c])),
				cs(g.at(c))))
		}
	}
	return sortRows(r, 2, 4)
}

func qPanicSourceReachable(g *Graph, pat string, lim int) result {
	r := result{cols: []string{"panic_fn", "at", "sources", "fan_in"}, lim: lim}
	s := &g.Sym
	dist := g.reachFrom(func(i int32) bool {
		return s.IsHandler[i] == 1 || s.IsEntrypoint[i] == 1
	}, 8)

	guarded := map[int32]bool{}
	for i := 0; i < s.n; i++ {
		if s.NRecover[i] == 0 {
			continue
		}
		lo, hi := g.Calls.Out.row(int32(i))
		for p := lo; p < hi; p++ {
			guarded[g.Calls.Out.val[p].Callee] = true
		}
	}
	for i := 0; i < s.n; i++ {
		if dist[i] < 0 || guarded[int32(i)] {
			continue
		}
		if s.NPanic[i]+s.NTypeAssertUnchecked[i] == 0 {
			continue
		}
		if !g.modOK(int32(i), s.FileId[i], pat) || g.inGenFile(int32(i)) {
			continue
		}
		r.rows = append(r.rows, row(nil, cs(g.name(int32(i))), cs(g.at(int32(i))),
			ci(int64(s.NPanic[i]+s.NTypeAssertUnchecked[i])), ci(int64(s.FanIn[i]))))
	}
	return sortRows(r, 2, 3)
}

func spawnTargetQuery(g *Graph, pat string, lim int, cols []string, mode int) result {
	r := result{cols: cols, lim: lim}
	s := &g.Sym
	for i := range g.Goro {
		o := &g.Goro[i]
		f := &g.File[o.FileID]
		if f.IsTest != 0 || f.IsGen != 0 ||
			!likePat(modName(g, s.ModuleId[o.SymbolID]), pat) {
			continue
		}
		sp := o.SymbolID
		at := g.atRow(o.FileID, o.Line)
		switch mode {
		case 0:
			if o.HasRecover != 0 || s.NRecover[sp] == 0 || g.Str.get(o.Target) == "" {
				continue
			}
			for _, t := range g.targetSyms(g.Str.get(o.Target)) {
				src := s.NPanic[t] + s.NTypeAssertUnchecked[t]
				if src == 0 {
					continue
				}
				r.rows = append(r.rows, row(nil, cs(g.name(sp)), ci(int64(o.Line)),
					cs(at), ci(int64(s.NRecover[sp])), cs(g.name(t)), ci(int64(src)),
					ci(int64(s.FanIn[t]))))
			}
		case 1:
			if o.HasCtx != 0 || o.ChanExit != 0 || g.Str.get(o.Target) == "" {
				continue
			}
			for _, t := range g.targetSyms(g.Str.get(o.Target)) {
				if s.NSelect[t] == 0 || s.NSelectCtxDone[t] != 0 {
					continue
				}
				r.rows = append(r.rows, row(nil, cs(g.name(sp)), ci(int64(o.Line)),
					cs(at), cs(g.name(t)), ci(int64(s.NSelect[t])),
					ci(int64(s.NSelectDefault[t])), ci(int64(s.NChanRecv[t])),
					ci(int64(s.FanIn[t]))))
			}
		case 2:
			if o.InLoop == 0 || o.HasEG != 0 || s.NSemaphore[sp] != 0 {
				continue
			}
			r.rows = append(r.rows, row(nil, cs(g.name(sp)), ci(int64(o.Line)),
				cs(at), ci(int64(o.LoopDepth)), ci(int64(s.NGoroutines[sp])),
				ci(int64(s.FanIn[sp])), ci(int64(s.IsHandler[sp]))))
		case 3:
			if o.IsClosure == 0 || o.InLoop == 0 || s.NAssign[sp] == 0 {
				continue
			}
			r.rows = append(r.rows, row(nil, cs(g.name(sp)), ci(int64(o.Line)),
				cs(at), ci(int64(o.LoopDepth)), ci(int64(s.NAssign[sp])),
				ci(int64(0)), ci(int64(s.FanIn[sp]))))
		}
	}
	switch mode {
	case 0:
		return sortRows(r, 5, 6)
	case 1:
		return sortRows(r, 4, 7)
	case 2:
		return sortRows(r, 3, 6, 5)
	}
	return sortRows(r, 3, 6)
}

func qTickerTimerNeverStopped(g *Graph, pat string, lim int) result {
	r := result{cols: []string{"timer_fn", "timers", "stops", "sleeps",
		"spawns", "fan_in", "at"}, lim: lim}
	s := &g.Sym

	stoppers := map[int32]int32{}
	for i := 0; i < s.n; i++ {
		if s.NTimerStop[i] == 0 {
			continue
		}
		lo, hi := g.Calls.Out.row(int32(i))
		for p := lo; p < hi; p++ {
			stoppers[g.Calls.Out.val[p].Callee] += s.NTimerStop[i]
		}
	}
	for _, i := range g.symRows(pat) {
		if s.NTimerNew[i] == 0 || s.NTimerNew[i] <= s.NTimerStop[i] {
			continue
		}
		if s.IsGenerated[i] != 0 || stoppers[i] >= s.NTimerNew[i] {
			continue
		}
		r.rows = append(r.rows, row(nil, cs(g.name(i)), ci(int64(s.NTimerNew[i])),
			ci(int64(s.NTimerStop[i])), ci(int64(s.NSleep[i])),
			ci(int64(s.NGoroutines[i])), ci(int64(s.FanIn[i])), cs(g.at(i))))
	}
	return sortRows(r, 1, 5)
}

func qHTTPDefaultClientUnderHandler(g *Graph, pat string, lim int) result {
	s := &g.Sym
	return reachQuery(g, pat, lim,
		[]string{"default_client_fn", "sites", "n_net", "fan_in", "at"},
		func(i int32) bool { return s.IsHandler[i] == 1 }, 4,
		func(i int32) bool { return s.NHttpDefaultClient[i] > 0 && s.IsGenerated[i] == 0 },
		func(i int32, d int32) []cellVal {
			return row(nil, cs(g.name(i)), ci(int64(s.NHttpDefaultClient[i])),
				ci(int64(s.NNet[i])), ci(int64(s.FanIn[i])), cs(g.at(i)))
		}, 1, 4)
}

func qErrgroupWithoutWait(g *Graph, pat string, lim int) result {
	r := result{cols: []string{"group_owner", "group_sites", "own_waits",
		"fan_in", "at"}, lim: lim}
	s := &g.Sym
	waiters := map[int32]bool{}
	for i := 0; i < s.n; i++ {
		if s.NWaitCall[i] > 0 {
			waiters[int32(i)] = true
		}
	}
	for i := range g.WgSites {
		if g.Str.get(g.WgSites[i].Op) == "Wait" {
			waiters[g.WgSites[i].SymbolID] = true
		}
	}

	indirect := map[int32]bool{}
	for i := 0; i < s.n; i++ {
		if !waiters[int32(i)] {
			continue
		}
		lo, hi := g.Calls.Out.row(int32(i))
		for p := lo; p < hi; p++ {
			indirect[g.Calls.Out.val[p].Callee] = true
		}
	}
	sites := map[int32]int32{}
	for i := range g.Hazards {
		h := &g.Hazards[i]
		if !patMatch(g.Str.get(h.Pattern), "errgroup.Group,errgroup.WithContext") {
			continue
		}
		sites[h.SymbolID] += h.N
	}
	var ids []int32
	for k := range sites {
		ids = append(ids, k)
	}
	slices.Sort(ids)
	for _, id := range ids {
		if waiters[id] || indirect[id] {
			continue
		}
		if g.File[s.FileId[id]].IsTest != 0 || g.File[s.FileId[id]].IsGen != 0 {
			continue
		}
		if !likePat(modName(g, s.ModuleId[id]), pat) {
			continue
		}
		r.rows = append(r.rows, row(nil, cs(g.name(id)), ci(int64(sites[id])),
			ci(int64(s.NWaitCall[id])), ci(int64(s.FanIn[id])), cs(g.at(id))))
	}
	return sortRows(r, 1, 3)
}

func qChannelNeverClosed(g *Graph, pat string, lim int) result {
	r := result{cols: []string{"declared_in", "chan_var", "elem_type", "cap_",
		"sends", "recv_sites", "spawns", "fan_in", "at"}, lim: lim}
	s := &g.Sym
	for i := range g.Chans {
		c := &g.Chans[i]
		if c.ClosedInFn != 0 {
			continue
		}
		f := &g.File[c.FileID]
		if f.IsTest != 0 || f.IsGen != 0 {
			continue
		}
		sid := c.SymbolID
		recv := s.NChanRecv[sid] + s.NSelect[sid]
		if recv == 0 || !likePat(modName(g, s.ModuleId[sid]), pat) {
			continue
		}
		r.rows = append(r.rows, row(nil, cs(g.name(sid)), cs(g.Str.get(c.Name)),
			cs(g.Str.get(c.ElemType)), ci(int64(c.Capacity)),
			ci(int64(s.NChanSend[sid])), ci(int64(recv)),
			ci(int64(s.NGoroutines[sid])), ci(int64(s.FanIn[sid])),
			cs(g.atRow(c.FileID, c.Line))))
	}
	return sortRows(r, 5, 7)
}

func qSignalNotifyUnbuffered(g *Graph, pat string, lim int) result {
	r := result{cols: []string{"notify_fn", "notify_sites", "chan_var", "cap_",
		"fan_in", "at"}, lim: lim}
	s := &g.Sym
	for i := range g.Hazards {
		h := &g.Hazards[i]
		if g.Str.get(h.Pattern) != "signal.Notify" {
			continue
		}
		sid := h.SymbolID
		f := &g.File[s.FileId[sid]]
		if f.IsTest != 0 || !likePat(modName(g, s.ModuleId[sid]), pat) {
			continue
		}
		lo, hi := g.chanCSR.row(sid)
		for p := lo; p < hi; p++ {
			c := &g.Chans[p]
			if c.Capacity > 0 {
				continue
			}
			r.rows = append(r.rows, row(nil, cs(g.name(sid)), ci(int64(h.N)),
				cs(g.Str.get(c.Name)), ci(int64(c.Capacity)),
				ci(int64(s.FanIn[sid])), cs(g.atRow(c.FileID, c.Line))))
		}
	}
	return sortRows(r, 4, 1)
}

func qErrorChainDiscard(g *Graph, pat string, lim int) result {
	r := result{cols: []string{"chain_top", "max_depth", "fan_in",
		"discarding_caller", "ignored", "at"}, lim: lim}
	s := &g.Sym
	for _, e := range g.ErrChain {
		sid := e.SymbolID
		if e.MaxDepth < 3 {
			continue
		}
		sf := &g.File[s.FileId[sid]]
		if sf.IsTest != 0 || !likePat(modName(g, s.ModuleId[sid]), pat) {
			continue
		}
		lo, hi := g.Calls.In.row(sid)
		for p := lo; p < hi; p++ {
			d := g.Calls.In.val[p].Callee
			if s.NErrIgnored[d] == 0 {
				continue
			}
			df := &g.File[s.FileId[d]]
			if df.IsTest != 0 || df.IsGen != 0 {
				continue
			}
			r.rows = append(r.rows, row(nil, cs(g.name(sid)), ci(int64(e.MaxDepth)),
				ci(int64(s.FanIn[sid])), cs(g.name(d)), ci(int64(s.NErrIgnored[d])),
				cs(g.at(d))))
		}
	}
	return sortRows(r, 1, 2)
}

func qBoundaryBareError(g *Graph, pat string, lim int) result {
	r := result{cols: []string{"bare_wrapper", "ext_calls", "unresolved",
		"wrapped", "err_returns", "fan_in", "at"}, lim: lim}
	s := &g.Sym
	for i := 0; i < s.n; i++ {
		if s.NErrReturns[i] == 0 || s.NErrWrapped[i] != 0 {
			continue
		}
		if s.NExternalCalls[i]+s.NUnresolvedCalls[i] == 0 || s.FanIn[i] < 3 {
			continue
		}

		if !g.modOK(int32(i), s.FileId[i], pat) || g.inGenFile(int32(i)) {
			continue
		}
		r.rows = append(r.rows, row(nil, cs(g.name(int32(i))),
			ci(int64(s.NExternalCalls[i])), ci(int64(s.NUnresolvedCalls[i])),
			ci(int64(s.NErrWrapped[i])), ci(int64(s.NErrReturns[i])),
			ci(int64(s.FanIn[i])), cs(g.at(int32(i)))))
	}
	return sortRows(r, 5, 1)
}

func qInitSideEffects(g *Graph, pat string, lim int) result {
	r := result{cols: []string{"init_fn", "side_effects", "n_io", "n_net",
		"n_sql", "n_exec", "env_reads", "spawns", "exits", "package_",
		"import_fan_in", "at"}, lim: lim}
	s := &g.Sym
	for i := 0; i < s.n; i++ {
		if s.IsInit[i] == 0 {
			continue
		}
		if !g.modOK(int32(i), s.FileId[i], pat) {
			continue
		}
		se := s.NIo[i] + s.NNet[i] + s.NSql[i] + s.NExec[i] + s.NEnvRead[i] +
			s.NGoroutines[i] + s.NExitCall[i]
		if se == 0 {
			continue
		}
		if !likePat(modName(g, s.ModuleId[i]), pat) {
			continue
		}
		mid := s.ModuleId[i]
		var fan int32
		if mid >= 0 {
			fan = g.Mod[mid].FanIn
		}
		r.rows = append(r.rows, row(nil, cs(g.name(int32(i))), ci(int64(se)),
			ci(int64(s.NIo[i])), ci(int64(s.NNet[i])), ci(int64(s.NSql[i])),
			ci(int64(s.NExec[i])), ci(int64(s.NEnvRead[i])),
			ci(int64(s.NGoroutines[i])), ci(int64(s.NExitCall[i])),
			cs(modName(g, mid)), ci(int64(fan)), cs(g.at(int32(i)))))
	}
	return sortRows(r, 1, 10)
}

func qRowsErrNeverChecked(g *Graph, pat string, lim int) result {
	r := result{cols: []string{"query_fn", "n_sql", "fan_in", "at"}, lim: lim}
	s := &g.Sym
	checks := map[int32]bool{}
	for i := 0; i < s.n; i++ {
		if s.NRowsErrCheck[i] > 0 {
			checks[int32(i)] = true
		}
	}
	for i := 0; i < s.n; i++ {
		if s.NSql[i] == 0 || s.NRowsErrCheck[i] != 0 {
			continue
		}
		if !g.modOK(int32(i), s.FileId[i], pat) || g.inGenFile(int32(i)) {
			continue
		}

		lo, hi := g.csCSR.row(int32(i))
		guarded := false
		for p := lo; p < hi; p++ {
			if checks[g.csList[g.csCSR.idx[p]].Caller] {
				guarded = true
				break
			}
		}
		if guarded {
			continue
		}
		r.rows = append(r.rows, row(nil, cs(g.name(int32(i))), ci(int64(s.NSql[i])),
			ci(int64(s.FanIn[i])), cs(g.at(int32(i)))))
	}
	return sortRows(r, 1, 2)
}

func qSleepUnderRequestPath(g *Graph, pat string, lim int) result {
	s := &g.Sym
	return reachQuery(g, pat, lim,
		[]string{"sleeping_fn", "hops", "sleeps", "ctx_done_checks", "fan_in", "at"},
		func(i int32) bool { return s.IsHandler[i] == 1 }, 3,
		func(i int32) bool { return s.NSleep[i] > 0 && s.IsGenerated[i] == 0 },
		func(i int32, d int32) []cellVal {
			return row(nil, cs(g.name(i)), ci(int64(d)), ci(int64(s.NSleep[i])),
				ci(int64(s.NCtxDone[i])), ci(int64(s.FanIn[i])), cs(g.at(i)))
		}, 1, 4)
}

func qHandlerWithoutRequestContext(g *Graph, pat string, lim int) result {
	r := result{cols: []string{"handler", "ctx_params", "blocking_calls",
		"spawns", "fan_in", "at"}, lim: lim}
	s := &g.Sym
	for _, i := range g.matchedSyms(pat) {
		if s.IsHandler[i] == 0 || s.NCtxParams[i] != 0 || s.IsGenerated[i] != 0 {
			continue
		}
		if s.NNet[i]+s.NSql[i]+s.NGoroutines[i] == 0 {
			continue
		}
		r.rows = append(r.rows, row(nil, cs(g.name(i)), ci(int64(s.NCtxParams[i])),
			ci(int64(s.NNet[i]+s.NSql[i])), ci(int64(s.NGoroutines[i])),
			ci(int64(s.FanIn[i])), cs(g.at(i))))
	}
	return sortRows(r, 4)
}

func qContextInStruct(g *Graph, pat string, lim int) result {
	r := result{cols: []string{"type_", "n_fields", "methods", "package_",
		"import_fan_in", "at"}, lim: lim}
	s := &g.Sym
	methods := map[string]int32{}
	for i := 0; i < s.n; i++ {
		if g.kind(int32(i)) == "method" && g.recv(int32(i)) != "" {
			methods[g.recv(int32(i))]++
		}
	}
	for i := range g.Structs {
		st := &g.Structs[i]
		if st.HasCtx == 0 {
			continue
		}
		sid := st.SymbolID
		if g.File[s.FileId[sid]].IsTest != 0 || g.File[s.FileId[sid]].IsGen != 0 {
			continue
		}
		if !likePat(modName(g, s.ModuleId[sid]), pat) {
			continue
		}
		var fan int32
		if mid := s.ModuleId[sid]; mid >= 0 {
			fan = g.Mod[mid].FanIn
		}
		r.rows = append(r.rows, row(nil, cs(g.name(sid)), ci(int64(st.NFields)),
			ci(int64(methods[g.name(sid)])), cs(modName(g, s.ModuleId[sid])),
			ci(int64(fan)), cs(g.at(sid))))
	}
	return sortRows(r, 2, 4)
}

func qBlockingSyncFunction(g *Graph, pat string, lim int) result {
	r := result{cols: []string{"fn", "spawns", "blocking_calls", "fan_in",
		"is_handler", "at"}, lim: lim}
	s := &g.Sym
	for _, i := range g.matchedSyms(pat) {
		if s.NGoroutines[i] == 0 || s.NNet[i]+s.NSql[i] == 0 || s.FanIn[i] == 0 {
			continue
		}
		if s.IsGenerated[i] != 0 {
			continue
		}
		r.rows = append(r.rows, row(nil, cs(g.name(i)), ci(int64(s.NGoroutines[i])),
			ci(int64(s.NNet[i]+s.NSql[i])), ci(int64(s.FanIn[i])),
			ci(int64(s.IsHandler[i])), cs(g.at(i))))
	}
	return sortRows(r, 3)
}

func qZipSlip(g *Graph, pat string, lim int) result {
	r := result{cols: []string{"name", "zip_access", "sloc", "at"}, lim: lim}
	s := &g.Sym
	for _, i := range g.symRows(pat) {
		if s.NZipRead[i] == 0 || s.IsGenerated[i] != 0 {
			continue
		}
		r.rows = append(r.rows, row(nil, cs(g.name(i)), ci(int64(s.NZipRead[i])),
			ci(int64(s.Sloc[i])), cs(g.at(i))))
	}
	return sortRows(r, 1, 2)
}

func qRecoverWrongSide(g *Graph, pat string, lim int) result {
	return spawnTargetQuery(g, pat, lim,
		[]string{"spawn_fn", "go_line", "at", "recover_in_spawner", "target_fn",
			"panic_sites", "fan_in"}, 0)
}

func qSelectMissingCtxDone(g *Graph, pat string, lim int) result {
	return spawnTargetQuery(g, pat, lim,
		[]string{"spawn_fn", "go_line", "at", "target_fn", "selects",
			"default_cases", "recvs", "target_fan_in"}, 1)
}

func qUnboundedSpawnFanout(g *Graph, pat string, lim int) result {
	return spawnTargetQuery(g, pat, lim,
		[]string{"spawn_fn", "go_line", "at", "loop_depth", "spawns_in_fn",
			"fan_in", "is_handler"}, 2)
}

func qCapturedVarMutated(g *Graph, pat string, lim int) result {
	return spawnTargetQuery(g, pat, lim,
		[]string{"spawn_fn", "go_line", "at", "loop_depth", "assignments",
			"loopvar_caps", "fan_in"}, 3)
}

type question struct {
	name  string
	title string
	notes string
	run   func(g *Graph, modPat string, lim int) result
}

var allQueries = []question{
	{
		name:  "goroutine-leak-frontier",
		title: "Goroutines with no context, no WaitGroup and no errgroup",
		notes: "ANSWERS which goroutines have no way to be told to stop.\nACT every spawn needs a stop condition and a joiner. A spawn inside a loop\n     with neither is the top of the list: it fans out per element and\n     nothing ever collects it.\nMISLEADS a goroutine that exits because its input channel is closed by\n     someone else is correct and appears here -- has_chan_exit is the\n     counter-evidence. has_ctx is a lexical scan of the closure body, so a\n     context checked one frame deeper is missed.",
		run:   qGoroutineLeakFrontier,
	},
	{
		name:  "goroutine-under-handler",
		title: "Goroutines reachable from a request handler, up to 4 hops",
		notes: "ANSWERS which spawns outlive the request that created them.\nACT a goroutine started per request and never joined is how RSS grows all\n     week and nobody can say why. Give it the request context.\nMISLEADS depth is capped at 4 and only resolved edges are walked, so this\n     is a floor. A handler registered by a router this cannot see has no\n     is_handler flag and its whole subtree is missing.",
		run:   qGoroutineUnderHandler,
	},
	{
		name:  "ctx-propagation-break",
		title: "Where a live context stops being passed down",
		notes: "ANSWERS the exact function at which cancellation and deadlines are lost:\n     the caller has a ctx, the callee makes a fresh Background() instead.\nACT thread the caller's ctx through. A Background() below a handler means\n     that work cannot be cancelled when the client hangs up.\nMISLEADS a genuinely detached background worker is SUPPOSED to call\n     context.Background(). Check whether the row sits on a request path\n     before changing it.",
		run:   qCtxPropagationBreak,
	},
	{
		name:  "defer-lifetime",
		title: "defer inside a loop: cleanup that waits for the whole function",
		notes: "ANSWERS staticcheck SA9001 -- defers run at FUNCTION exit, not at the end\n     of the iteration, so a loop over 10,000 files holds 10,000 handles.\nACT wrap the loop body in a func(){...}() so the defer fires per iteration,\n     or close explicitly at the end of the body.\nMISLEADS a loop with a small constant bound holding a couple of handles is\n     harmless. The risk scales with trip count, which is invisible here.",
		run:   qDeferLifetime,
	},
	{
		name:  "resource-close-cross-layer",
		title: "Opens a body, rows or file and defers no Close",
		notes: "ANSWERS the cross-function version of bodyclose / sqlclosecheck: the open\n     and the Close live in different functions, so no per-file checker can\n     pair them.\nACT the function that opens should defer the Close, or return a closer and\n     say so in its name. callers_that_close is the evidence someone else\n     is already doing it.\nMISLEADS a constructor that deliberately returns an open resource is\n     correct and appears here. Check whether the return type is a Closer.",
		run:   qResourceCloseCrossLayer,
	},
	{
		name:  "unchecked-errors",
		title: "Discarded errors, weighted by how much of the tree calls the discarder",
		notes: "ANSWERS which errcheck findings actually matter: a swallowed error in a\n     leaf forty callers depend on is a different object from one in a\n     one-shot init.\nACT check it, or wrap with %w so errors.Is still works upstream.\nMISLEADS the blast column multiplies by MAX(fan_in,1), so a symbol with\n     NO known caller scores exactly as if it had one. Read fan_in=0\n     rows as 'unknown reach', never as 'reach of 1'.\n     `_ = f.Close()` on a read-only file is a deliberate discard and is\n     counted here. Shadow detection is textual, so an intentional inner\n     err is a false positive.",
		run:   qUncheckedErrors,
	},
	{
		name:  "channel-topology",
		title: "Unbuffered channels, and whether anything can receive",
		notes: "ANSWERS the two channel deadlock shapes: an unbuffered send with no ready\n     receiver, and a range-over-channel nobody closes. SA1017 is the\n     special case -- signal.Notify on an unbuffered channel DROPS signals.\nACT name the closer for every channel. An unbuffered send while holding a\n     lock is a deadlock waiting for load.\nMISLEADS a never-closed channel is fine if nothing ranges over it. A\n     capacity of -1 means the size is a variable and could be anything.",
		run:   qChannelTopology,
	},
	{
		name:  "lock-copied-by-value",
		title: "Types embedding a sync.Mutex passed by value",
		notes: "ANSWERS `go vet copylocks` raised to the call graph: a copied mutex\n     protects nothing, and the copy is silent.\nACT take the type by pointer everywhere, or add a noCopy field so vet\n     catches the next one.\nMISLEADS a struct copied before any goroutine exists -- config\n     construction, test fixtures -- is harmless. An embedded mutex inside\n     an embedded struct is missed by the has_mutex scan.",
		run:   qLockCopiedByValue,
	},
	{
		name:  "lock-over-crosspkg-call",
		title: "A mutex held while calling into another package",
		notes: "ANSWERS where your critical section's duration is somebody else's code --\n     the contention a profiler shows as time in Lock with no clue why.\nACT copy what you need out of the guarded state, unlock, then call out.\nMISLEADS same_module=0 is a package boundary, not a slowness proof. A\n     cross-package call to a pure helper costs nothing.",
		run:   qLockOverCrosspkgCall,
	},
	{
		name:  "n-plus-one",
		title: "A query function whose CALLER puts it in a loop",
		notes: "ANSWERS the N+1 no per-file linter can see, because the query and the loop\n     live in different functions.\nACT batch-fetch, join, or move the loop into the query.\nMISLEADS a loop with a small constant bound is not an N+1, and trip count\n     is invisible here.",
		run:   qNPlusOne,
	},
	{
		name:  "unsafe-cgo-frontier",
		title: "unsafe.Pointer and cgo reachable from a handler, up to 5 hops",
		notes: "ANSWERS the only places in a Go binary where memory unsafety is possible.\nACT these are the fuzzing targets. Every cgo call also costs a\n     goroutine-to-thread transition, so a cgo call in a hot path is a\n     performance finding as well as a safety one.\nMISLEADS unsafe.Sizeof and unsafe.Alignof are compile-time and completely\n     safe, yet counted in n_unsafe_ops. Read the hazard patterns, not the\n     total.",
		run:   qUnsafeCgoFrontier,
	},
	{
		name:  "package-state-concurrent",
		title: "Packages that spawn goroutines and hold unguarded package state",
		notes: "ANSWERS what the race detector would find if the right two goroutines ever\n     ran together.\nACT move the state behind a struct with a mutex, or make it immutable\n     after init.\nMISLEADS state written only in init() and read afterwards is safe. This\n     counts declarations plus goroutine presence in the same package, not\n     actual concurrent access.",
		run:   qPackageStateConcurrent,
	},
	{
		name:  "dead-code",
		title: "Nothing in this tree calls these",
		notes: "ANSWERS what might be deletable.\nACT exported identifiers are excluded because another module may use them.\n     What is left is unexported and unreferenced.\nMISLEADS an unexported function reached only through an interface method\n     value, or registered in a map of handlers, has no resolvable edge\n     and appears here wrongly -- and so does a method called on its own\n     receiver from another FILE in the same package, which resolution\n     does not always follow. grep the name before deleting anything.",
		run:   qDeadCode,
	},
	{
		name:  "defer-in-loop",
		title: "defer inside a loop: cleanup that piles up until the function returns",
		notes: "ANSWERS where deferred work does not run when the author thinks it does.\n     `defer` fires at FUNCTION exit, not at the end of the iteration --\n     so a defer f.Close() in a loop over ten thousand files holds ten\n     thousand descriptors open, and the loop hits the ulimit.\nACT move the body into its own function so the defer scopes to one\n     iteration, or close explicitly at the end of the loop and drop the\n     defer. `defer_close` shows which of these are closing something.\nMISLEADS a defer in a loop that runs a bounded handful of times is fine,\n     and this cannot see the trip count. The dangerous shape is a defer\n     over a range of unknown length -- check what the loop iterates.",
		run:   qDeferInLoop,
	},
	{
		name:  "context-not-propagated",
		title: "Functions that take a context and never pass it on",
		notes: "ANSWERS where cancellation stops travelling. A ctx parameter that is\n     accepted and then ignored means every call below it is\n     uncancellable: the request times out, the client disconnects, and\n     the work carries on burning a database connection.\nACT pass ctx to every call that accepts one, and use\n     `ctx.Done()` in any select that could block. A function creating\n     `context.Background()` deep in a call stack is almost always\n     severing a chain it should have continued.\nMISLEADS a leaf function doing pure computation takes ctx for interface\n     reasons and has nothing to pass it to -- that is correct and shows\n     up here. Rank by fan_out: severing a chain matters where work follows.",
		run:   qContextNotPropagated,
	},
	{
		name:  "error-handling-drift",
		title: "Ignored errors, shadowed errors, and errors compared instead of unwrapped",
		notes: "ANSWERS where Go's error convention has quietly broken down. An `_`\n     assignment discards a failure; a re-declared err inside an if\n     shadows the outer one so the outer stays nil; and `err == ErrFoo`\n     fails the moment anything in the chain wraps it with %w.\nACT check the error or comment why it cannot fail. Use `errors.Is` and\n     `errors.As` rather than == and type assertions, so wrapping stays\n     transparent. `err_wrapped` shows who is already doing it.\nMISLEADS a deliberately ignored error -- a Close on a read-only file, a\n     fmt.Fprintf to a buffer -- is idiomatic and counted here. The\n     column that carries real signal is shadowing, which is never intended.",
		run:   qErrorHandlingDrift,
	},
	{
		name:  "slice-growth-and-copies",
		title: "append in a loop with no capacity, and range copying whole structs",
		notes: "ANSWERS where a loop reallocates or copies more than it needs to.\n     `append` without `make([]T, 0, n)` regrows and copies repeatedly;\n     `for _, v := range structs` copies every element by value, which\n     for a large struct is a memcpy per iteration.\nACT preallocate with the known length. Range over the index, or use a\n     pointer element, when the struct is big. `Sprintf` in a loop is the\n     third form of the same problem -- build with a strings.Builder.\nMISLEADS a slice that grows a handful of times costs nothing, and Go's\n     growth is amortised. This is a ranking of where the pattern is\n     densest and hottest, not a list of defects.",
		run:   qSliceGrowthAndCopies,
	},
	{
		name:  "unchecked-type-assertions",
		title: "Type assertions without the comma-ok form, and interface{} at the boundary",
		notes: "ANSWERS which assertions panic instead of failing. `v := x.(T)` aborts\n     the goroutine when x is not a T; `v, ok := x.(T)` does not. In a\n     handler without recover, that is the request AND the process.\nACT use the comma-ok form and handle the false branch, or a type switch\n     with a default. Where the value came from JSON or a plugin, assume\n     it will eventually be the wrong shape, because it will.\nMISLEADS an assertion immediately after a type switch that already\n     proved the type is safe and counted here. `type_switch` in the same\n     row is the hint that the author did check.",
		run:   qUncheckedTypeAssertions,
	},
	{
		name:  "context-severed-by-caller",
		title: "context.Background() called from a function whose own caller had a real context",
		notes: "ANSWERS the question `containedctx` and `fatcontext` cannot: not whether\n     a fresh Background() exists, but whether one was NEEDED. A\n     Background() at main() is correct. The same call two frames below a\n     handler that was handed a ctx severs cancellation for everything\n     underneath -- the request is abandoned and the work carries on.\nACT thread the caller's ctx down instead of minting a new one. The\n     `caller` column names a function that already had one; if several\n     callers appear, the signature needs a ctx parameter.\nMISLEADS a Background() used to deliberately OUTLIVE the request -- a\n     fire-and-forget audit write, a cache warm -- is correct and looks\n     identical here. The tell is whether the result is awaited. This also\n     inherits containedctx's blind spot: a ctx stored in a struct field\n     rather than passed is invisible to both.",
		run:   qContextSeveredByCaller,
	},
	{
		name:  "lock-release-imbalance-reachable",
		title: "Functions that lock more than they unlock, weighted by what reaches them",
		notes: "ANSWERS which unbalanced locking can actually be hit. Counting Lock and\n     Unlock per function is trivial and staticcheck does it; the useful\n     question is whether an HTTP handler or a goroutine reaches the\n     imbalance, because an unreleased mutex there deadlocks the server\n     rather than one test.\nACT `defer mu.Unlock()` immediately after the Lock is the fix for almost\n     all of these. Where the imbalance is deliberate -- lock in one\n     method, unlock in another -- name the pair so the next reader knows.\nMISLEADS a deferred Unlock IS counted, so a correctly balanced function\n     shows equal numbers; what appears here is genuinely lopsided text.\n     But lock and unlock in different FUNCTIONS is a legitimate pattern\n     for a guard type and reads as an imbalance in both halves. Depth is\n     bounded at 4 hops, so a deeper caller is simply not seen.",
		run:   qLockImbalanceReachable,
	},
	{
		name:  "nil-context-deep",
		title: "context.Background() or context.TODO() deep in a call chain (containedctx)",
		notes: "ANSWERS where a function that is reachable from a request handler creates a\n     new root context instead of accepting one from its caller, severing\n     cancellation and deadline propagation.\nACT thread the caller's context through, or if a true root is intended\n     (background worker), document why. n_ctx_background is the count;\n     is_handler=1 or reachability from one says a real context existed.\nMISLEADS context.Background() in main() or init() is correct. Reachability\n     is capped at 4 hops, so a handler six calls away is missed.",
		run:   qNilContextDeep,
	},
	{
		name:  "error-not-wrapped",
		title: "errors created without %w wrapping (errorlint)",
		notes: "ANSWERS where fmt.Errorf or errors.New is used without %w, so callers\n     cannot errors.Is or errors.As the underlying cause.\nACT change fmt.Errorf('...: %v', err) to fmt.Errorf('...: %w', err).\n     n_errorf_no_wrap is the count; n_err_wrapped is the counter-evidence.\nMISLEADS not every error has a cause to wrap; a sentinel error from\n     errors.New is intentionally flat.",
		run:   qErrorNotWrapped,
	},
	{
		name:  "weak-random-security",
		title: "math/rand used where crypto/rand is needed (gosec G404)",
		notes: "ANSWERS where math/rand is used for security-sensitive randomness: tokens,\n     IDs, keys, shuffling. math/rand is deterministic and predictable.\nACT replace with crypto/rand or math/rand/v2 with a proper seed for\n     non-security uses; use crypto/rand for anything security-relevant.\nMISLEADS math/rand for simulation, testing, or jitter is correct. The\n     column is a count, not a judgement: whether this call is\n     security-sensitive depends on the call graph context.",
		run:   qWeakRandom,
	},
	{
		name:  "weak-crypto-security",
		title: "MD5, SHA1, DES, or RC4 used in cryptographic context (gosec G401-G405)",
		notes: "ANSWERS where a broken or deprecated crypto algorithm is used.\nACT replace MD5/SHA1 with SHA256 or stronger; replace DES/RC4 with AES.\nMISLEADS MD5 for a checksum or ETag is not a security failure. The graph\n     sees the call, not its purpose.",
		run:   qWeakCrypto,
	},
	{
		name:  "import-cycle",
		title: "Circular import dependencies (madge/deadcode)",
		notes: "ANSWERS which files form an import cycle, where A imports B and B imports A\n     (directly or transitively). Cycles cause init-order bugs and block\n     testability.\nACT break the cycle by extracting shared code into a third package, or\n     use dependency injection.\nMISLEADS cycles through test files are usually fine. Depth is capped at 8.",
		run:   qImportCycle,
	},
	{
		name:  "string-concat-in-loop",
		title: "String concatenation with += inside a loop (gocritic stringConcat)",
		notes: "ANSWERS where strings are built with += or + in a loop, producing O(n^2)\n     allocations because Go strings are immutable.\nACT use strings.Builder or a []byte then string(b).\nMISLEADS a loop with a small constant bound (e.g. 3 iterations) pays less\n     than a Builder allocation. concat_in_loop is a site count, not a\n     measurement of how many iterations actually ran.",
		run:   qStringConcatInLoop,
	},
	{
		name:  "unsafe-pointer-arith",
		title: "unsafe.Pointer arithmetic or conversion (gosec G103)",
		notes: "ANSWERS where unsafe.Pointer is used for arithmetic, type punning, or\n     pointer conversion, bypassing Go's type and memory safety.\nACT review each site; replace with a safe alternative (encoding/binary,\n     reflect, or a typed slice) where possible.\nMISLEADS cgo interop and performance-critical code may legitimately need\n     unsafe. The n_cgo_calls column tells whether this is a cgo boundary.",
		run:   qUnsafePointerArith,
	},
	{
		name:  "log-fatal-in-handler",
		title: "log.Fatal or os.Exit in a request handler (revive deep-exit)",
		notes: "ANSWERS where a function reachable from a request handler calls log.Fatal,\n     log.Panic, or os.Exit, terminating the entire process for one bad\n     request.\nACT return an error to the caller; let the top-level recover middleware\n     decide whether to exit.\nMISLEADS log.Fatal in main() or a startup path is correct. Reachability is\n     from is_handler=1, capped at 4 hops.",
		run:   qLogFatalInHandler,
	},
	{
		name:  "time-after-in-loop",
		title: "time.After in a loop leaks timers until they fire (performance)",
		notes: "ANSWERS where time.After is used inside a loop, creating a new timer each\n     iteration that is not garbage collected until it fires. In a tight\n     loop this is a memory leak.\nACT use time.NewTimer and Reset it, or use a select with a time.AfterFunc.\nMISLEADS a loop with a long sleep between iterations may not leak enough\n     to matter. n_time_after_in_loop is a count, not a measurement of\n     how many timers are live at once.",
		run:   qTimeAfterInLoop,
	},
	{
		name:  "reflect-call-surface",
		title: "reflect.Call or reflect.ValueOf on dynamic input (gosec G104)",
		notes: "ANSWERS where reflect is used to call methods dynamically, which bypasses\n     the type system and can be exploited if the input is attacker-controlled.\nACT prefer interfaces over reflect; if reflect is needed, validate the\n     input type before calling.\nMISLEADS reflect is correct for serialization, testing, and ORM frameworks.\n     The graph sees the call but not the input source.",
		run:   qReflectCallSurface,
	},
	{
		name:  "env-read-in-handler",
		title: "os.Getenv or os.LookupEnv in a request path (revive env-in-handler)",
		notes: "ANSWERS where environment variables are read inside a function reachable\n     from a request handler, so each request pays the env-lookup cost and\n     the value can change between requests without restart.\nACT read env vars at startup (init or main) and pass them through.\nMISLEADS a handler that reads env to decide a feature flag is a valid\n     pattern if the flag is expected to change at runtime.",
		run:   qEnvReadInHandler,
	},
	{
		name:  "select-without-default",
		title: "select without a default case (potential goroutine deadlock)",
		notes: "ANSWERS where a select statement has no default case, so the goroutine\n     blocks until one case is ready. In a hot path this can deadlock.\nACT add a default case or a timeout case (with context cancellation) if\n     blocking is not intended.\nMISLEADS a select that blocks on purpose (worker pool, pipeline) is correct.\n     n_select_default counts defaults; n_select_ctx_done counts context\n     cancellation cases.",
		run:   qSelectWithoutDefault,
	},
	{
		name:  "readall-in-loop",
		title: "io.ReadAll or ioutil.ReadAll inside a loop (performance)",
		notes: "ANSWERS where io.ReadAll is called inside a loop, reading an entire stream\n     into memory per iteration. For large streams this is an O(n*m) memory\n     pattern.\nACT read once before the loop, or stream with a bufio.Reader.\nMISLEADS a loop that reads small, bounded payloads (headers, config lines)\n     is fine. n_readall_in_loop counts sites, not bytes.",
		run:   qReadallInLoop,
	},
	{
		name:  "iface-satisfaction-breadth",
		title: "Structs that implicitly satisfy the most interfaces",
		notes: "ANSWERS which concrete types are the load-bearing implementations: a type\n     satisfying many interfaces is the one every swap-in replacement must\n     match, and the one whose method name changes break the most contracts.\nACT test the top rows against the interface list before renaming any\n     method; these are the types where a signature change is a broad API\n     break.\nMISLEADS satisfaction is method-NAME containment only (see the implements\n     post_build contract): a type is counted as satisfying an interface\n     even where signatures disagree, and only in-tree implementors exist.",
		run:   qIfaceSatisfactionBreadth,
	},
	{
		name:  "concurrency-hotspots",
		title: "Functions that spawn goroutines AND touch channels: contention hubs",
		notes: "ANSWERS the functions where concurrency is personally invented rather\n     than inherited: goroutine spawns plus channel sends/recvs in one body\n     are the primitive shapes the sync package exists to replace.\nACT check whether each channel has ONE sender and ONE receiver per\n     message (the safe shape); multiple senders need locks or per-channel\n     mutexes.\nMISLEADS a function that spawns goroutines that later touch channels is\n     invisible here (the edge points at the goroutine's closure, whose\n     symbol is separate). Counts are per-symbol, and spawns in a loop are\n     one spawn call regardless of trip count.",
		run:   qConcurrencyHotspots,
	},
	{
		name:  "unused-exported",
		title: "Exported symbols nothing in this tree references",
		notes: "ANSWERS the public API surface the repository itself never calls -- the\n     symbols released to the world but exercised only by external\n     consumers, if any.\nACT for a library, an exported-and-unused symbol is a candidate for a\n     deprecation note: the tree does not exercise it, so it is the most\n     likely to rot. For an application, it is a dead export.\nMISLEADS external consumers are not in this tree, so a genuinely public\n     API looks identical to a dead one; `dead-code` is the unexported\n     counterpart. Interface-implementing methods are excluded because\n     they are reached through the interface, not by name.",
		run:   qUnusedExported,
	},
	{
		name:  "receiver-pointer-mix",
		title: "Value vs pointer receivers per type: the allocation-copy axis",
		notes: "ANSWERS which types mix receiver styles, which is the complaint that\n     blows up when the struct grows: a value receiver copies the whole\n     struct on every call, and a type that mixes the two will not get a\n     consistent compiler error about it.\nACT pick ONE style per type -- pointer receivers for anything with a\n     slice/header inside, value receivers only for tiny immutable types.\nMISLEADS methods taking a POINTER-typed receiver alias could be misread;\n     the count is per declared receiver, not per call, so a hot value\n     receiver is not weightened by its call frequency here.",
		run:   qReceiverPointerMix,
	},
	{
		name:  "abstraction-reach",
		title: "Interfaces satisfied by the most distinct types",
		notes: "ANSWERS the interface contracts with the widest implementation base --\n     the seams that, if they change, every implementor (and every caller\n     through the interface) must change with them.\nACT these are the interfaces worth keeping stable and worth writing\n     conformance tests for: a change here is a change across the tree.\nMISLEADS counts in-tree implementors by method-name containment only; an\n     interface that stdlib or an external module satisfies is invisible.\n     `single-impl-interface` is the zero-end of this same ranking.",
		run:   qAbstractionReach,
	},
	{
		name:  "internal-package-leak",
		title: "Imports reaching into /internal/ from outside its root",
		notes: "ANSWERS import statements whose target contains an internal/ segment,\n     joined with the importer's own path, so the Go-rule check (only\n     code under the internal root may import it) is visible per row.\nACT for each row, decide whether the importer sits under the internal\n     root: if not, the import is a layering leak that a module boundary\n     will break later.\nMISLEADS the tree does not know the module root, so the query cannot\n     CONFIRM the leak -- it lists candidate rows and lets the path\n     comparison be done by eye. Stdlib internal/ packages are excluded\n     by is_external.",
		run:   qInternalPackageLeak,
	},
	{
		name:  "module-dependency-depth",
		title: "Longest import chain through each package",
		notes: "ANSWERS how deeply each package sits in the import DAG, and how many\n     distinct packages it transitively depends on -- the numbers that\n     describe whether a change here drags a long chain along.\nACT a package with max_depth>=5 or many transitive deps is a candidate\n     for dependency trimming; a leaf package (depth 0, few transitives)\n     is the safe place to put shared code.\nMISLEADS computed on RESOLVED in-tree imports only, so stdlib and\n     external modules terminate a chain rather than extending it; depth\n     is the longest single chain, not an average, and modules that share\n     no resolved edge with the tree are absent entirely.",
		run:   qModuleDependencyDepth,
	},
	{
		name:  "error-fan-out",
		title: "Error-returning functions ranked by how far a failure propagates",
		notes: "ANSWERS where an error raised deep down surfaces many frames above:\n     max_depth is the longest chain of error-returning callees reachable\n     (f -> g -> h where every hop returns error), so a row with depth 4\n     means the deepest leaf's failure is carried, unwrapped or not,\n     through four frames. These are the chains where %w discipline and\n     context (file, line, operation) are cheapest to add and most often\n     missing.\nACT audit the deepest chains first: each hop is a place an error either\n     gains context (%w), stays bare (fmt.Errorf without %w), or gets\n     dropped. `error-not-wrapped` and `error-handling-drift` rank the\n     same functions on the text signals; this ranks the chain itself.\nMISLEADS depth counts error-RETURNING hops only -- a callee that absorbs\n     the error (logs and returns nil) terminates the chain, which is the\n     containment this query is asking about, not a miss. Edges are\n     name-resolved, so an error passed through an interface or returned\n     by a closure is invisible and chains undercount. A chain through a\n     recursive cycle is reported at the cap of 32; the call graph is\n     walked in Python per root, O(V*(V+E)) on error-returning symbols\n     only.",
		run:   qErrorFanOut,
	},
	{
		name:  "command-exec-surface",
		title: "Where the process boundary is crossed (gosec G204)",
		notes: "ANSWERS the functions that reach exec.Command / exec.CommandContext /\n     syscall.Exec -- every place a string becomes a process.\nACT each row needs an allowlisted or constant command; a command built\n     from variables or input is a command-injection review item.\nMISLEADS arg literalness is NOT captured -- constant commands rank the\n     same as tainted ones; a wrapper around exec.Command is invisible\n     to name matching; the capture is the hazard map, so os.Exit and\n     syscall.Syscall (same category, different risk) are excluded by\n     the exact-name denylist on purpose.",
		run:   qCommandExecSurface,
	},
	{
		name:  "sensitive-log-surface",
		title: "Fatal/panic logging in functions that read environment (OWASP G21)",
		notes: "ANSWERS functions that reach the log.Fatal family AND read environment\n     variables -- the shape of a secret or credential finding its way\n     into a log line (log.Println(os.Getenv(\"TOKEN\"))).\nACT log the redacted value, or nothing; keep tokens out of every log\n     sink, not just the fatal ones.\nMISLEADS same-function co-occurrence is NOT data flow -- the env value\n     may never reach the log call. os.Getenv is environment, not user\n     input. Only the log.Fatal/Print family is hazard-captured;\n    logrus/klog/zap and plain log.Print are invisible to name matching,\n     and log.Fatal in main() or a startup path is correct.",
		run:   qSensitiveLogSurface,
	},
	{
		name:  "open-redirect-surface",
		title: "http.Redirect calls in handlers that read request input (OWASP G26)",
		notes: "ANSWERS functions that call http.Redirect AND read request input\n     (r.URL.Query / r.FormValue / r.Cookie / r.Form) -- the shape of an\n     unvalidated redirect: http.Redirect(w, r, r.URL.Query().Get(\"next\"), 302).\nACT validate the target against an allowlist; never forward a\n     user-supplied URL.\nMISLEADS same-function co-occurrence is NOT data flow -- the input value\n     may never reach the redirect, and a constant redirect beside an\n     unrelated input read reads as a violation. The argument text is not\n     captured, so a fixed target cannot be told from an open one; a\n     wrapper around http.Redirect is invisible to the exact-name capture;     a request flow through an alias (rr := r) is invisible to the\n     receiver set {r, req, request}.",
		run:   qOpenRedirectSurface,
	},
	{
		name:  "hardcoded-secret-candidates",
		title: "Credential-shaped string literals (OWASP G07)",
		notes: "ANSWERS string literals at least 12 chars long whose text names a\n     credential (password, token, api_key, secret, bearer, jwt, ...) --\n     the literal that a committed secret looks like.\nACT rotate and move to a secret manager; never commit the literal.\nMISLEADS a format string or test fixture containing the WORD token/pass\n     reads as a candidate (the filter is the literal's own text, not its\n     use); values over 200 chars are truncated at capture; a secret\n     built from parts or read from an env var is invisible here.\n     This is a candidate list, not a verdict.",
		run:   qHardcodedSecrets,
	},
	{
		name:  "untrusted-deserialization",
		title: "json decode sites in functions that read request input (OWASP G19)",
		notes: "ANSWERS functions that call json.Unmarshal / Decoder.Decode AND read\n     request input -- the shape of deserializing an untrusted payload:\n     json.NewDecoder(r.Body).Decode(&user).\nACT validate the payload schema and size before decoding; never decode\n     into an interface{} from an untrusted source.\nMISLEADS same-function co-occurrence is NOT data flow -- the decoded\n     value may not come from the request, and a constant decode beside\n     an unrelated input read reads as a violation. The Decode capture is\n     the bare base name, so encoding/json's Decode and a totally\n     different library's Decode are indistinguishable here.",
		run:   qUntrustedDeserialization,
	},
	{
		name:  "path-traversal-surface",
		title: "os.* with a non-literal path in input-reading functions (OWASP G12)",
		notes: "ANSWERS functions that call os.Open/ReadFile/WriteFile/Create with a\n     variable path AND read request input -- the shape of path\n     traversal: os.ReadFile(r.URL.Query().Get(\"f\")).\nACT validate the resolved path stays under a configured root; use\n     filepath.Clean and a prefix check.\nMISLEADS same-function co-occurrence is NOT data flow -- the input value\n     may never reach the open, and a constant-open beside an unrelated\n     input read reads as a violation. The path is not analyzed: a\n     variable path is assumed suspicious, a literal is not; a\n     wrapped-open helper is invisible to the os. capture.",
		run:   qPathTraversalSurface,
	},
	{
		name:  "zip-slip-surface",
		title: "archive/zip access sites (OWASP G29)",
		notes: "ANSWERS functions that touch archive/zip -- the surface where an entry\n     name becomes a filesystem path.\nACT validate every entry name against a containment check before\n     extraction; reject ../ and absolute paths.\nMISLEADS the containment check is not modeled: a function that checks\n     each name before extraction ranks the same as one that does not.\n     The capture is the dotted zip. name; a renamed zip helper is\n     invisible.",
		run:   qZipSlip,
	},
	{
		name:  "mass-assignment-surface",
		title: "Decode into request-body readers (OWASP G30)",
		notes: "ANSWERS functions that decode JSON in functions that read the request\n     BODY -- the shape of mass assignment: json.NewDecoder(r.Body)\n     .Decode(&user) maps every request field onto the struct.\nACT bind to a DTO with only the fields you accept; never decode a\n     request body into a persistent model.\nMISLEADS same-function co-occurrence is NOT data flow -- the decoded\n     source may not be the body, and a body read beside an unrelated\n     decode reads as a violation. Which struct fields the body can set\n     is not modeled; a schema-validated decode ranks the same as an\n     unchecked one.",
		run:   qMassAssignmentSurface,
	},
	{
		name:  "unauthenticated-input-surface",
		title: "Request input read with no auth call in the function (OWASP G01)",
		notes: "ANSWERS functions that read request input and contain NO auth-family\n     call (RequireAuth, CheckAuth, jwt, session, login) -- the surface\n     where a handler may be missing its authorization check.\nACT add the auth middleware call; verify the route is in the protected\n     group.\nMISLEADS auth usually lives in MIDDLEWARE, not the handler -- this\n     query sees the handler only, so a fully-protected mux still ranks\n     every handler as open. A login or public endpoint legitimately has\n     no auth. The markers are name-based substrings, so a wrapper\n     around the auth call is invisible and counts as open.",
		run:   qUnauthenticatedInput,
	},
	{
		name:  "deprecated-stdlib-calls",
		title: "Call sites of deprecated stdlib entry points (staticcheck SA1019)",
		notes: "ANSWERS where deprecated stdlib functions are still called, with the\n     replacement inline. The ioutil.* family moved to io/os in Go 1.16.\nACT swap to the replacement; each row is mechanical.\nMISLEADS the denylist ships inline and goes stale with each Go release;\n     ioutil.WriteFile/Discard/NopCloser and rand.Seed/rand.Read are NOT\n     hazard-captured and are absent here (rand.Read is contextual\n     anyway -- crypto/rand where security-relevant, math/rand/v2\n     elsewhere); a dotted alias (io.ReadAll) is unaffected.",
		run:   qDeprecatedStdlib,
	},
	{
		name:  "deferred-close-unchecked",
		title: "defer x.Close() whose error return vanishes (staticcheck SA5001)",
		notes: "ANSWERS defer sites where a Close()/Flush() error is silently dropped,\n     ranked by how much of the tree calls the deferrer: a write error\n     that surfaces at defer time is exactly the one nobody checks.\nACT join the close error into the named return, or accept the loss\n     deliberately (a comment is cheaper than a bug report).\nMISLEADS Close errors on read handles are benign; whether THIS Close\n     returns error is name-inferred, not type-checked; in-loop defers\n     belong to defer-lifetime and are excluded here.",
		run:   qDeferredCloseUnchecked,
	},
	{
		name:  "http-request-no-context",
		title: "http.NewRequest without a context (noctx territory)",
		notes: "ANSWERS functions that build requests with the context-less\n     http.NewRequest instead of http.NewRequestWithContext: the request\n     cannot be cancelled, and a slow peer hangs the caller forever.\nACT pass the caller's context (or context.Background() where none\n     exists) via NewRequestWithContext.\nMISLEADS a wrapper around NewRequest that threads ctx internally is\n     invisible to name matching; the plain form in a CLI one-shot is\n     the legitimate row; the http.Client without a Timeout is a\n     different (pre-existing) family and does not appear here.",
		run:   qHTTPRequestNoContext,
	},
	{
		name:  "file-read-surface",
		title: "os.ReadFile / os.Open call sites by fan-in",
		notes: "ANSWERS where whole-file reads and opens happen -- the functions most\n     likely to hit path-traversal (G304) or unbounded reads, ranked by\n     how much of the tree trusts them.\nACT for a read whose path is derived from input, validate the path;\n     for os.ReadFile of a remote/untrusted file, prefer a reader with\n     a size limit.\nMISLEADS path origin is NOT captured -- a constant path ranks the same\n     as one built from user input; os.Open without a follow-on read\n     still appears (it IS the open surface); handler-adjacency is\n     approximated by fan_in.",
		run:   qFileReadSurface,
	},
	{
		name:  "sql-injection-build",
		title: "SQL assembled by string concatenation (gosec G201/G202 territory)",
		notes: "ANSWERS functions that build SQL by concatenating string literals: the\n     value can only be injected if a variable reaches the concat, and\n     this is the review list for exactly that question, ranked by how\n     much of the tree trusts the builder.\nACT use placeholders (QueryContext with args), or parameterise the\n     identifier with a whitelist -- concatenation is never the fix.\nMISLEADS n_sql_concat counts SQL literal sites whose parent is a `+`\n     expression: a query assembled by Sprintf or passed in whole as a\n     variable is invisible here, and a concat of two constants (no\n     injection possible) reads the same as one mixing a variable.\n     `string-concat-in-loop` owns the generic allocation shape.",
		run:   qSQLInjectionBuild,
	},
	{
		name:  "context-built-in-loop",
		title: "context.WithTimeout / WithDeadline / WithCancel inside a loop",
		notes: "ANSWERS deadline/cancel contexts created per iteration: WithTimeout in\n     a loop leaks one timer per pass until the iteration ends, and\n     WithCancel recreated every iteration can never be the thing the\n     body waits on -- the loop restarts it.\nACT create the context once before the loop; per-iteration deadlines\n     belong to the work function, not the loop.\nMISLEADS the counter is base-name based: a method literally named\n     WithTimeout on a non-context type also matches; a context created\n     in a helper called from the loop is invisible; a short loop over\n     a fixed slice pays little -- this ranks review order.",
		run:   qContextBuiltInLoop,
	},
	{
		name:  "nil-error-after-check",
		title: "if err != nil { return nil }: the error is dropped at the check (nilerr)",
		notes: "ANSWERS functions whose error check leads straight to a nil return:\n     the error is detected and then discarded. Callers cannot tell\n     success from swallowed failure, and a nil error from a function\n     that just failed is the hardest-to-reproduce bug class in Go.\nACT return the error (`return nil, err` in the multi-value shape); a\n     deliberately ignored failure needs a comment saying why.\nMISLEADS the shape is text-matched on the if-consequence: `return 0, nil`\n     (a zero value plus nil error) is missed, and an if-block that\n     returns nil BEFORE checking a second condition is caught even when\n     the later return is honest -- read the row, do not trust it.",
		run:   qNilErrorAfterCheck,
	},
	{
		name:  "loopvar-rebind-dead",
		title: "`v := v` rebinds under go >= 1.22 (copyloopvar territory)",
		notes: "ANSWERS the dead rebind: `for _, v := range xs { v := v ... }`. Before\n     Go 1.22 the rebind captured a per-iteration copy; from 1.22 the\n     loop variable already is per-iteration, so the rebind is a no-op\n     that reads as if it does something.\nACT delete the rebind; the semantics are already what the rebind\n     pretended to provide.\nMISLEADS gated on the go directive from go.mod: below 1.22 the rebind\n     is REAL and the row would be a false positive, so nothing fires;\n     the go directive can be lower than the toolchain actually used;\n     the text shape is `name := name`, so an unrelated same-name\n     shadow in a loop body also matches.",
		run:   qLoopvarRebindDead,
	},
	{
		name:  "insecure-tls-config",
		title: "tls.Config with InsecureSkipVerify: true (gosec G402)",
		notes: "ANSWERS every tls.Config that disables certificate verification: the\n     connection accepts ANY certificate, which turns TLS into\n     obfuscated plaintext. One wrong flag in a config struct is the\n     whole class.\nACT use the default verification; if a test or internal service needs\n     a skip, pin the expected cert instead of disabling the check.\nMISLEADS text-matched on the composite literal: a config built\n     field-by-field (`c := tls.Config{}; c.InsecureSkipVerify = true`)\n     is missed, and a flag set from a variable (`= allowInsecure`)\n     reads as absent here.",
		run:   qInsecureTLS,
	},
	{
		name:  "waitgroup-add-inside-goroutine",
		title: "WaitGroup.Add runs inside the spawned goroutine, not before the spawn (SA2000)",
		notes: "ANSWERS which `go` statements race on their own WaitGroup: the Add that\n     must happen before Wait fires sits lexically inside the spawned\n     closure (or inside the named target function), so Wait can observe\n     a zero counter and return while goroutines are still appearing.\nACT hoist `wg.Add(1)` above the `go` line at the spawn site; add a\n     regression test that runs under -race.\nMISLEADS a target that deliberately re-adds (batch regrouping) is flagged;\n     Add sites are matched per receiver variable, so a second, unrelated\n     counter named like a WaitGroup rides along; a spawned closure that\n     calls Add one more frame down is missed (one hop only).",
		run:   qWaitgroupAddInsideGoroutine,
	},
	{
		name:  "wg-done-missing-in-target",
		title: "WaitGroup-guarded spawn whose target never calls Done: Wait blocks forever",
		notes: "ANSWERS spawns the spawner arms with a WaitGroup but whose target function\n     -- nor anything it calls one hop out -- ever balances the Add with a\n     Done. The first Wait on that counter never returns.\nACT put `defer wg.Done()` as the first statement of the target, or switch\n     the fan-out to an errgroup so Wait is structural.\nMISLEADS the target may signal completion through a done channel instead\n     of the WaitGroup (check has_chan_exit); a Done delegated two or more\n     hops below the target is missed; dead-code targets inflate the list.",
		run:   qWaitgroupDoneMissing,
	},
	{
		name:  "waitgroup-imbalance",
		title: "A function Adds a WaitGroup more often than it Done/Waits it, and spawns nothing",
		notes: "ANSWERS per-WaitGroup-variable balance inside one function: more Adds than\n     Dones and Waits combined, with no WaitGroup-carrying spawn that the\n     Done could have been delegated to -- the counter leaks upward and a\n     later Wait never fires.\nACT pair every Add with a `defer wg.Done()` in the same scope, or hand\n     the whole counter to one owner.\nMISLEADS the normal spawner shape (Add here, Done inside the spawned\n     function) is EXCLUDED only when the spawn is visible as\n     has_waitgroup; a Done two hops down, or reached through an interface,\n     still reads as a deficit; two WaitGroups sharing a variable name in\n     one function are merged.",
		run:   qWaitgroupImbalance,
	},
	{
		name:  "double-lock-same-receiver-path",
		title: "Locking method calls a sibling method on the same receiver that also locks",
		notes: "ANSWERS self-deadlock paths: sync.Mutex is not reentrant, so an edge from\n     a locking method to another locking method with the SAME receiver\n     type deadlocks the second time anyone takes the first path.\nACT split the inner method into a lock-free variant (fooLocked) and call\n     that from both entry points.\nMISLEADS the two methods may lock DIFFERENT mutex fields of one struct\n     (nesting different locks is legal); the call may sit after an\n     Unlock on every path, which line-level analysis cannot prove;\n     only the DIRECT edge is reported, so three-hop cycles stay hidden.",
		run:   qDoubleLockSameReceiver,
	},
	{
		name:  "os-exit-under-call-tree",
		title: "os.Exit/log.Fatal buried below an entry point, skipping every caller's defers",
		notes: "ANSWERS exit sites reachable from a handler or main: the process dies\n     there and the defers of EVERY frame above the exit never run --\n     flushes, unlocks and acks included. defers_skipped_near counts the\n     defers in the immediate callers this graph can see.\nACT return the error up to main; keep exactly one exit, in main.\nMISLEADS a legitimate exit in CLI setup reachable only from main is\n     normal; reachability caps at 8 hops, so a deeper path hides the row;\n     defers_skipped_near is one hop of callers, not the whole stack.",
		run:   qOSExitUnderCallTree,
	},
	{
		name:  "lock-held-across-io-transitive",
		title: "Critical section stays held across I/O two or three calls deep",
		notes: "ANSWERS functions that lock and whose transitively-called functions (up to\n     3 hops) do network, SQL, exec or file I/O: the lock is held for the\n     duration of someone else's syscall, and every contender queues.\nACT copy the guarded state out, unlock, then do the I/O; or move to\n     per-key locks.\nMISLEADS the I/O may sit behind an early release this line-ordered view\n     cannot see; the io callee may be a cold error path; deliberate\n     write-behind under a lock is a design choice, not a bug.",
		run:   qLockHeldAcrossIO,
	},
	{
		name:  "lock-held-across-dynamic-call",
		title: "Mutex held while calling through an interface: unknown code in the critical section",
		notes: "ANSWERS functions that both lock and perform dynamic (interface) calls,\n     weighted by interface-typed parameters: any implementer -- including\n     one that calls back into the locked type -- runs inside the lock.\nACT extract what you need under the lock, unlock, then invoke the\n     callback; or document the no-reentrancy invariant on the type.\nMISLEADS n_dynamic_calls counts innocent fmt.Stringer and error-interface\n     calls too; visitor-style callback-under-lock is a deliberate design;\n     whether the dispatched method actually touches this type is beyond\n     name-based dispatch resolution.",
		run:   qLockHeldAcrossDynamic,
	},
	{
		name:  "resource-returned-never-closed",
		title: "Caller of a Rows/Body/File-returning helper never closes it: ownership leak",
		notes: "ANSWERS call sites of helpers that RETURN sql.Rows, an http.Response, a\n     ReadCloser or a file, where the receiving caller neither defers a\n     Close nor calls one. The opener looks fine to a per-file linter; the\n     leak lives one frame up, across the call edge.\nACT `defer r.Close()` at each leaking call site, or wrap the resource in\n     the helper and return a cleanup func instead.\nMISLEADS the caller may pass the resource onward to a function that\n     closes it (ownership transfer beyond one hop); a shared\n     drainAndClose helper reads as never-closed; type matching is on the\n     return-type TEXT, so custom wrapper types are missed.",
		run:   qResourceNeverClosed,
	},
	{
		name:  "panic-source-reachable-from-entry",
		title: "panic or unchecked type-assert reachable from a handler/main with no recover guard",
		notes: "ANSWERS functions containing panic() or a forced type assertion that are\n     reachable from a request handler or entrypoint AND whose direct\n     callers all lack recover: one bad input kills the process.\nACT make the assertion comma-ok and return an error, or add a recover in\n     the request wrapper at the handler boundary.\nMISLEADS a recover ANYWHERE on a caller suppresses the row even if that\n     path is rarely taken; nil-map writes and index-out-of-range panics\n     carry no panic() call and stay invisible; reachability caps at 8\n     hops.",
		run:   qPanicSourceReachable,
	},
	{
		name:  "recover-wrong-side-of-spawn",
		title: "Spawner has the recover, goroutine body can panic: recover never fires for the child",
		notes: "ANSWERS spawn sites whose own function recovers but whose spawned target\n     contains panic() or unchecked type assertions and no recover of its\n     own: recover() only works inside the panicking goroutine, so the\n     guard the author wrote guards the wrong frame.\nACT make the first statement of the goroutine body\n     `defer func(){ if r := recover(); ... }()`.\nMISLEADS the target may be panic-free in practice (n_panic counts only\n     explicit panics and unchecked asserts); inline closure bodies are\n     counted in the spawner, not as a separate target; a target that\n     delegates into an existing safe runner is missed.",
		run:   qRecoverWrongSide,
	},
	{
		name:  "goroutine-select-missing-ctx-done",
		title: "Spawned goroutine selects but never observes cancellation: it outlives its producer",
		notes: "ANSWERS spawns that pass no context whose target runs a select with no\n     ctx.Done case: when the producer goes away the goroutine blocks in\n     that select forever -- the leak goleak trips over at shutdown.\nACT pass ctx into the target and add a `<-ctx.Done()` case, or close a\n     done channel the select already watches.\nMISLEADS the target may exit via a channel close the select DOES watch\n     (has_chan_exit is filtered, but a close one frame deeper is not\n     visible); a deliberately immortal daemon loop looks like a leak;\n     send-side selects guarded by default are fine without ctx.",
		run:   qSelectMissingCtxDone,
	},
	{
		name:  "ticker-timer-never-stopped",
		title: "time.NewTicker/NewTimer with no Stop on any nearby path (SA1015 family)",
		notes: "ANSWERS ticker and timer producers that create more tickers than they or\n     any of their callers Stop: each leaked Ticker holds a runtime timer\n     and its channel buffer forever.\nACT `defer t.Stop()` immediately after NewTicker/NewTimer; replace bare\n     long-lived time.Tick with a stopped ticker.\nMISLEADS a Stop two hops below the producer is invisible (one caller hop\n     is checked); one-shot timer use that outlives the request on purpose\n     is not a leak; the counts are per function, so two tickers with one\n     shared Stop still read as a deficit.",
		run:   qTickerTimerNeverStopped,
	},
	{
		name:  "unbounded-spawn-fanout",
		title: "Per-item `go` in a loop with no errgroup or semaphore: concurrency is unbounded",
		notes: "ANSWERS in-loop spawns with neither an errgroup nor any semaphore acquire\n     (SetLimit/Acquire/TryAcquire) in the spawning function, on handlers\n     and other high fan-in code: one request over 10,000 items is 10,000\n     goroutines and whatever they open.\nACT wrap with errgroup.SetLimit, a buffered-channel semaphore, or a fixed\n     worker pool.\nMISLEADS a loop over a tiny fixed set (config entries) is harmless; a\n     limiter acquired by a CALLER and passed in reads as absent; a\n     WaitGroup bounds TIME here, not CONCURRENCY, and is deliberately\n     not counted as bounding.",
		run:   qUnboundedSpawnFanout,
	},
	{
		name:  "http-default-client-under-handler",
		title: "Handler reaches http.Get/DefaultClient within 4 hops: a request can hang forever",
		notes: "ANSWERS functions using the timeout-less default client (http.Get, Post,\n     Head, DefaultClient.Do) that are reachable from a request handler\n     within 4 hops: the missing timeout belongs to the path, not to the\n     helper's own file.\nACT inject a client with explicit Timeout (and transport timeouts) at the\n     handler boundary; or thread ctx and use NewRequestWithContext.\nMISLEADS a ctx-aware call through the default client is cancellable\n     anyway; a custom client built in middleware is invisible; reachability\n     beyond 4 hops is truncated.",
		run:   qHTTPDefaultClientUnderHandler,
	},
	{
		name:  "errgroup-without-wait",
		title: "errgroup.Group created but neither the function nor its callers ever Wait",
		notes: "ANSWERS functions that construct an errgroup.Group / WithContext group but\n     call no Wait themselves -- and none of their callers do either: the\n     group's errors vanish and WithContext's cancel leaks the ctx.\nACT `defer g.Wait()` (and `defer cancel()`) in the scope that owns the\n     group.\nMISLEADS g.Go is a plain call, not a `go` statement, so the anchor is the\n     group CONSTRUCTION and a Wait invoked through an interface or a\n     helper is invisible; deliberate fire-and-forget groups with their\n     own done channel are misread; a group handed to another function to\n     be waited on there reads as never-awaited.",
		run:   qErrgroupWithoutWait,
	},
	{
		name:  "channel-never-closed",
		title: "A channel someone receives from is never closed in its owning function",
		notes: "ANSWERS channels whose owning function receives (or selects) but never\n     closes, and no other local evidence of a closer exists: every\n     `for range ch` consumer of this channel terminates only when the\n     producer happens to close it from another function.\nACT have the producer `defer close(ch)` after its send loop, or range in\n     a select loop that also watches ctx.Done().\nMISLEADS closed_in_fn is matched per close() ARGUMENT in the owning\n     function only -- a close in a helper, or of an aliased channel,\n     reads as never-closed; eternal event-bus channels are a legitimate\n     design; channels whose size is a variable carry capacity -1 and are\n     filtered to the never-closed side only.",
		run:   qChannelNeverClosed,
	},
	{
		name:  "signal-notify-unbuffered",
		title: "signal.Notify on an unbuffered channel drops signals (SA1017, go vet sigchanyzer)",
		notes: "ANSWERS signal.Notify call sites in functions that also declare an\n     unbuffered (or variable-sized) channel: the kernel deliverable is\n     dropped while nothing is receiving on the channel right then.\nACT declare the signal channel `make(chan os.Signal, 1)`.\nMISLEADS the pairing is by same-function presence, so the buffered\n     channel may live one frame away and be passed in; capacity -1 means\n     the size is a variable and could be fine; a Notify that never\n     expects a second signal is harmless.",
		run:   qSignalNotifyUnbuffered,
	},
	{
		name:  "error-chain-terminated-by-discard",
		title: "A 3+ deep error chain whose top caller discards errors (errcheck x error-fan-out)",
		notes: "ANSWERS deep error-propagation chains (max_depth >= 3) where the caller at\n     the chain head has discarded error returns: three frames of honest\n     plumbing feed a caller that throws the failure away.\nACT log-or-wrap at the top caller; if the error will never be handled,\n     delete the plumbing instead.\nMISLEADS n_err_ignored includes deliberate `_ = fmt.Fprintln`-style\n     ignores of non-error returns; the discarder may retry instead of\n     propagating; chain depth counts only hops where EVERY callee returns\n     error, so aborted branches are invisible.",
		run:   qErrorChainDiscard,
	},
	{
		name:  "boundary-bare-error",
		title: "High fan-in function passes errors through with zero added context (wrapcheck)",
		notes: "ANSWERS heavily-called functions that return errors from external or\n     unresolved calls without ever wrapping one: callers get `open file`\n     with no word of WHO was being read or why.\nACT add `fmt.Errorf(\"reading config: %w\", err)` once at the boundary --\n     every caller inherits the context.\nMISLEADS internal same-module pass-through is fine per wrapcheck's own\n     defaults; context added by a custom error type is invisible to the\n     counters; must-style helpers that deliberately return the raw error\n     are idiomatic.",
		run:   qBoundaryBareError,
	},
	{
		name:  "init-side-effects",
		title: "init() doing I/O, env reads, exec, exits or spawning goroutines (Uber: Avoid init())",
		notes: "ANSWERS init functions whose side effects run at process start -- file and\n     network I/O, SQL, exec, os.Getenv, os.Exit/log.Fatal, goroutines --\n     ranked by how many modules import the package: every importer\n     re-executes the failure.\nACT move to an explicit Start/Close owned object; make failure an error\n     that main decides about.\nMISLEADS embedding templates and registering database drivers in init is\n     idiomatic and intentional; var-initializer expressions doing the\n     same thing carry no is_init flag; import fan-in counts packages,\n     not runtime executions.",
		run:   qInitSideEffects,
	},
	{
		name:  "rows-err-never-checked",
		title: "SQL-querying function where neither it nor its callers ever check rows.Err (rowserrcheck)",
		notes: "ANSWERS functions that query and drain rows with no rows.Err() call in\n     them or in their direct callers: a connection drop mid-iteration\n     ends the loop looking like SUCCESS.\nACT `if err := rows.Err(); err != nil {...}` after each drain loop, or\n     return rows wrapped in a helper that checks.\nMISLEADS rows.Scan errors usually surface the same failure one iteration\n     earlier (not always: the last batch); the check may live in a drain\n     helper two hops away; n_sql counts Exec with no rows too.",
		run:   qRowsErrNeverChecked,
	},
	{
		name:  "sleep-under-request-path",
		title: "time.Sleep reachable from a request handler: every request pays the latency",
		notes: "ANSWERS functions containing time.Sleep that are reachable from a handler\n     within 3 hops, ranked by distance: the same sleep in a background\n     janitor is fine, on a request path it is a deadline violation.\nACT replace with a select on a ctx-aware timer, or move the work off the\n     request path entirely.\nMISLEADS tiny backoff sleeps inside retry loops can be intentional (check\n     ctx_done_checks on the row); poll-wait loops are sometimes the only\n     option against an external system; reachability caps at 3 hops.",
		run:   qSleepUnderRequestPath,
	},
	{
		name:  "captured-var-mutated-after-spawn",
		title: "Closure goroutine spawned in a loop while the spawner keeps assigning locals",
		notes: "ANSWERS closure spawns inside loops where the spawning function also does\n     ordinary assignments: the goroutine captures locals by reference\n     while the spawner's remaining statements mutate them -- the classic\n     data race the race detector sees only under load.\nACT pass the values as parameters to the goroutine\n     (`go func(v T){...}(v)`), or copy before the spawn.\nMISLEADS on go >= 1.22 loop variables are per-iteration (the plain local\n     capture race is still real); a WaitGroup join before the mutation\n     orders the accesses and is safe but invisible here; n_assign counts\n     assignments anywhere in the spawner, not specifically after the go\n     line.",
		run:   qCapturedVarMutated,
	},
	{
		name:  "handler-without-request-context",
		title: "Request handler takes no context and does network/SQL/spawn work in it",
		notes: "ANSWERS functions with a handler signature but no context.Context\n     parameter that still do net/sql calls or spawn goroutines: every\n     client disconnect, timeout and shutdown signal stops at that\n     signature.\nACT add ctx as the first parameter and thread it to the first blocking\n     call.\nMISLEADS handlers whose framework injects cancellation another way\n     (gin's own request-scoped context) are flagged wrongly; a handler\n     that only reads memory is fine without ctx; a ctx param alone does\n     not prove it is USED -- see ctx-propagation-break for that side.",
		run:   qHandlerWithoutRequestContext,
	},
	{
		name:  "context-in-struct",
		title: "context.Context stored in a struct field: every method inherits a stale ctx (containedctx)",
		notes: "ANSWERS struct types with a context.Context field, ranked by method count:\n     the context frozen at construction shadows the caller's deadline on\n     every method it guards, and the Go wiki's rule is that ctx travels\n     as the first parameter, never inside a struct.\nACT drop the field; pass ctx explicitly to the methods that block.\nMISLEADS long-lived request objects whose ctx is refreshed per request\n     look the same as the frozen kind; test fixtures with a ctx field are\n     harmless; a struct holding a ctx it only forwards at construction\n     time is a style call, not a bug.",
		run:   qContextInStruct,
	},
	{
		name:  "blocking-sync-function",
		title: "Function both spawns goroutines and blocks on net/sql: concurrency the caller cannot see (Google style)",
		notes: "ANSWERS functions that spawn goroutines AND do their own blocking network\n     or SQL calls, with callers: the Google style guide wants synchronous\n     functions and the CONCURRENCY decided by the caller -- this shape\n     hides goroutine lifecycles inside a call that looks like a function.\nACT split it: a synchronous core the caller wraps, or a documented async\n     API that returns a handle.\nMISLEADS an internal worker pool that fully joins before returning is\n     synchronous in effect and flagged anyway; the sql/net counters say\n     nothing about how long the calls block; a wrapper that merely\n     forwards to one blocking helper is usually fine.",
		run:   qBlockingSyncFunction,
	},
}

var allMetrics = []question{
	{
		name:  "graph-blindspots",
		title: "Read this first: where the call graph cannot see",
		notes: "ANSWERS how much of every other answer here is guesswork.\nACT external calls are out of scope by design (stdlib, modules) and are\n     NOT counted as blindness. Unresolved means we genuinely lost it --\n     usually an interface method with several implementations.\nMISLEADS a resolved edge can still be wrong: a call to an interface method\n     resolves to whichever single implementation exists, and if two exist\n     this refuses to guess and lands here instead.",
		run:   mGraphBlindspots,
	},
	{
		name:  "single-impl-interface",
		title: "Interfaces satisfied by exactly one type: abstraction over nothing",
		notes: "ANSWERS a design question no linter asks. One implementor means the\n     interface is a hypothetical seam, and it costs a dynamic dispatch and\n     a heap escape at every call.\nACT delete it and use the concrete type -- UNLESS it exists for a test\n     double, or it is declared in the CONSUMER package, which is the\n     idiomatic Go pattern and is correct.\nMISLEADS satisfaction is computed on method NAMES, not signatures, so a\n     type with Close() error matches an interface wanting Close() even\n     where the Go compiler would not. It also sees only types in THIS\n     tree, so an implementor in another module is invisible.",
		run:   mSingleImplInterface,
	},
	{
		name:  "heap-pressure-loops",
		title: "Sprintf, uncapped append and conversions inside loops",
		notes: "ANSWERS the ways a Go loop moves work to the heap: formatting, growing a\n     slice from zero capacity, string/[]byte copies, boxing into any.\nACT make([]T, 0, n) when you know n; strconv over Sprintf; take a concrete\n     type instead of any.\nMISLEADS none of this is confirmed without `go build -gcflags=-m`. The\n     compiler's escape analysis may already be stack-allocating the row\n     you are reading. This is a candidate list for a benchmark.",
		run:   mHeapPressureLoops,
	},
	{
		name:  "range-value-copy",
		title: "for _, v := range over big structs: a memcpy per element",
		notes: "ANSWERS the silent per-iteration copy that costs est_size bytes every time\n     round the loop.\nACT range over the index and take &s[i], or hold pointers. The win scales\n     with the struct size.\nMISLEADS est_size is a 64-bit model estimate. Go lays fields out in\n     DECLARATION order -- reordering is an open proposal, not a thing the\n     compiler does -- but it pads for alignment, and nothing here computes\n     the exact size, which is why size_exact is 0 on every row. Anything\n     under about 32 bytes copies for free.",
		run:   mRangeValueCopy,
	},
	{
		name:  "risk-ranked",
		title: "Review order: if you can only read N functions this week, which N",
		notes: "ANSWERS which functions combine complexity with dangerous operations.\nACT start at the top. The score weights unsafe, cgo, exec and SQL building\n     far above raw complexity.\nMISLEADS a heuristic, not a finding. Generated and vendored files are\n     excluded, so the real top of the list may be in code this hid.",
		run:   mRiskRanked,
	},
	{
		name:  "hot-multipliers",
		title: "Where one fix pays back many times: highest fan-in",
		notes: "ANSWERS which functions the rest of the tree leans on hardest.\nACT a win in a high-fan-in leaf pays once per caller.\nMISLEADS fan_in counts STATIC call sites, not runtime frequency.",
		run:   mHotMultipliers,
	},
	{
		name:  "god-functions",
		title: "Functions doing too much, by every measure at once",
		notes: "ANSWERS which functions are hardest to hold in your head.\nACT split by responsibility. n_elif tells you whether it is a flat\n     dispatch (extract a map) or real nesting (extract functions).\nMISLEADS a long flat dispatch reads far more easily than a short deeply\n     nested one, which is why this sorts by cognitive rather than sloc.",
		run:   mGodFunctions,
	},
	{
		name:  "module-coupling",
		title: "Which packages depend on which, and how unstable that makes them",
		notes: "ANSWERS which packages are hard to change because everything leans on them.\nACT instability near 0 with high fan_in is a good place for stable\n     abstractions and a bad place for volatile logic.\nMISLEADS instability is a ratio, so a package with one edge each way scores\n     0.5 and means nothing. Read it next to n_files.",
		run:   mModuleCoupling,
	},
	{
		name:  "markers",
		title: "TODO, FIXME, HACK and BUG, weighted by the code they sit in",
		notes: "ANSWERS which unfinished business sits where it matters.\nACT a FIXME in a function forty things depend on outranks a TODO in a CLI.\nMISLEADS marker age is invisible -- git blame is the missing column. Many\n     of these were resolved years ago and the comment stayed.",
		run:   mMarkers,
	},
	{
		name:  "parse-coverage",
		title: "What this run could not read",
		notes: "ANSWERS whether the numbers above cover the code you think they cover.\nACT a file here contributed nothing. Build-tagged files that do not apply\n     to this platform are the usual innocent explanation.\nMISLEADS a file can parse perfectly and still be misunderstood. This shows\n     hard failures only.",
		run:   mParseCoverage,
	},
	{
		name:  "wrapper-function",
		title: "Function that only calls one other function (gocritic wrapperFunc)",
		notes: "ANSWERS where a function body is a single call to another function, adding\n     no logic \u2014 a wrapper that exists only to rename or forward.\nACT inline the call or document why the indirection is needed (interface\n     conformance, deprecated alias, test seam).\nMISLEADS a wrapper that satisfies an interface or provides a test seam is\n     intentional. The graph sees n_calls=1 and n_unique_calls=1 but cannot\n     see whether the signature differs from the callee.",
		run:   mWrapperFunction,
	},
	{
		name:  "naked-return-complex",
		title: "Naked return in a function with high complexity (golint)",
		notes: "ANSWERS where a function uses naked returns (implicit return of named\n     results) and has enough complexity that the return value is hard to\n     trace, which is golint's naked-return warning.\nACT use explicit returns in functions with cyclomatic > 10 or > 50 SLOC.\nMISLEADS naked returns in short functions (defer cleanup, early-exit\n     patterns) are idiomatic and clear.",
		run:   mNakedReturnComplex,
	},
	{
		name:  "scattered-concerns",
		title: "A function called from many different modules (shotgun-surgery smell)",
		notes: "ANSWERS which functions are called from a high number of distinct modules,\n     so any change to them ripples across the codebase.\nACT consider splitting the function or making the contract more stable.\n     The modules column lists the dependents.\nMISLEADS a utility like log.Printf is called from everywhere and is\n     intentionally stable; high fan_in from many modules is the design.",
		run:   mScatteredConcerns,
	},
	{
		name:  "god-module",
		title: "A package with too many functions and high total complexity",
		notes: "ANSWERS which modules are god packages: too many functions, too much\n     complexity, too much coupling for one package.\nACT split the package along responsibility lines. The total_cyclo and\n     n_functions columns quantify the size.\nMISLEADS a large package may be a framework entrypoint that is intentionally\n     broad. The instability column (fan_in/(fan_in+fan_out)) tells whether\n     it is a leaf or a root.",
		run:   mGodModule,
	},
	{
		name:  "deep-call-chain",
		title: "Functions at the end of a very deep call chain (maintainability)",
		notes: "ANSWERS which functions are reachable only through a long call chain\n     (depth > 6), making them hard to test in isolation and hard to debug.\nACT flatten the call chain or provide a direct entrypoint for testing.\nMISLEADS depth is from any root (handler or entrypoint), capped at 8.\n     A function that is deep from one root but shallow from another shows\n     the minimum.",
		run:   mDeepCallChain,
	},
	{
		name:  "too-many-return-paths",
		title: "Functions with an excessive number of return paths (maintainability)",
		notes: "ANSWERS where a function has more than 10 return statements, making it\n     hard to verify all paths are covered and resources are cleaned up.\nACT consolidate early returns or use a result struct; ensure defers cover\n     every path.\nMISLEADS a dispatch function with one return per case is correct. The\n     n_early_returns column distinguishes guard clauses from scattered\n     returns.",
		run:   mTooManyReturnPaths,
	},
	{
		name:  "unused-params",
		title: "Parameters that are never read in the function body (unparam)",
		notes: "ANSWERS where a function has parameters that are likely unused, based on\n     the ratio of member accesses and subscripts to the parameter count.\n     An unused parameter is a maintenance burden and a signal that the\n     interface is wider than needed.\nACT remove the parameter if no caller passes a meaningful value, or rename\n     to _ to signal intentional unused.\nMISLEADS a parameter used only in a branch the graph cannot see (a rare\n     error path) will appear unused. This is a heuristic, not a proof.",
		run:   mUnusedParams,
	},
	{
		name:  "goroutine-fanout-density",
		title: "Goroutine pressure per package: spawns, in-loop share, per-ksloc density",
		notes: "ANSWERS which packages put the most goroutine pressure on the runtime: raw\n     spawn counts, the share spawned per-loop-iteration, and spawns per\n     thousand SLOC so small hot packages are not hidden by big calm ones.\nACT point goleak tests and lifetime review at the top packages first;\n     every in-loop spawn should have a limiter next to it.\nMISLEADS a few legitimate long-lived worker pools dominate raw counts;\n     density punishes small high-concurrency packages; test-driven spawn\n     counts are excluded here but often dominate real repos.",
		run:   mGoroutineFanoutDensity,
	},
	{
		name:  "cleanup-coverage",
		title: "Functions with real exits and I/O but not a single defer: the cleanup-deficit list",
		notes: "ANSWERS functions doing I/O, SQL or network work with error checks and\n     return paths but zero defers: every error path leaks whatever the\n     success path closes by hand.\nACT review the top offenders for a missing `defer x.Close()`; set a house\n     rule that any function opening a resource defers its Close.\nMISLEADS explicit Close before each return is a correct alternative this\n     counts as a deficit; n_defer includes deferred log/print that cleans\n     nothing (excluded here only by being zero); pure functions dilute\n     nothing because the WHERE already filters to I/O doers.",
		run:   mCleanupCoverage,
	},
	{
		name:  "open-close-ratio",
		title: "Close actions vs open sites per package: who owns the descriptors",
		notes: "ANSWERS the module-grain balance between resources opened (io+sql+net\n     sites) and closes performed (direct Close calls plus close-defers):\n     below ~0.8 the package is exporting cleanup work to its callers.\nACT audit ownership in the worst packages: either the opener defers the\n     Close, or the return type says who must.\nMISLEADS read-only opens (os.ReadFile) self-close and inflate the\n     deficit; opens and closes via wrapper helpers count on different\n     rows; the ratio says nothing about WHICH paths close, only how\n     many.",
		run:   mOpenCloseRatio,
	},
	{
		name:  "lock-balance",
		title: "Packages that Lock more than they Unlock, defers included",
		notes: "ANSWERS module-grain lock hygiene: Lock/RLock calls vs Unlock/RUnlock\n     calls, how many of the unlocks are defers, and the deficit rows\n     that lock strictly more than they release. The function-grain view\n     is lock-release-imbalance-reachable; this is the screening view.\nACT a deficit package gets a defer-unlock sweep: every Lock is followed\n     by `defer mu.Unlock()` or an explicit release on every path.\nMISLEADS TryLock failure paths, RWMutex mixing and channels-as-locks are\n     invisible; a balanced package can still deadlock via nested locking\n     (double-lock-same-receiver-path); deferred unlocks are counted\n     inside the unlock total, not added twice.",
		run:   mLockBalance,
	},
	{
		name:  "channel-balance",
		title: "Send/receive/close counts per package, and the unbuffered share",
		notes: "ANSWERS the module-grain channel texture: how much sending and receiving\n    happens, how often channels get closed, and what share of channel\n    types are unbuffered -- the screening view for the cross-function\n    channel pairing queries.\nACT packages with heavy sends and few closes feed channel-never-closed\n    review; mandate `make(chan T, 1)` over bare unbuffered where a\n    capacity of one is the intent (Uber: Channel Size is One or None).\nMISLEADS select statements count as both send and receive sites; buffered\n    channels absorb imbalance by design; real producer/consumer pairing\n    crosses packages, so the module grain can only screen, not prove.",
		run:   mChannelBalance,
	},
	{
		name:  "test-only-fanin",
		title: "Exported functions whose only callers are _test.go files: production-dead but alive-looking",
		notes: "ANSWERS exported functions with callers where every edge comes from a test\n    file: no production code path reaches them, but per-file lint and\n    dead-code reads both keep them alive.\nACT delete or unexport; or move the test to exercise the real production\n    entry path instead of the helper directly.\nMISLEADS public library APIs are legitimately caller-less in their own\n    repo (external importers are invisible); entry points and examples\n    are exempt by is_entrypoint/is_public semantics only partially;\n    reflection- and registration-based dispatch has no edges at all.",
		run:   mTestOnlyFanin,
	},
	{
		name:  "wrap-ratio",
		title: "%w-wrapping share per package, weighted by importers (errorlint / wrapcheck)",
		notes: "ANSWERS the module-grain error-wrapping hygiene: %w-wrapped constructions\n    vs verbatim fmt.Errorf sites, ranked with the package's import\n    fan-in, because a module that never wraps breaks errors.Is and\n    errors.As FOR EVERY caller of that module.\nACT mandate %w in the worst packages first; migrate opportunistically\n    upward from the lowest ratio.\nMISLEADS deliberate %v at trust boundaries (hiding internals from API\n    consumers) is correct and counted against you; custom error types\n    wrap without Errorf and are invisible; raw counts matter less than\n    the ratio, so a one-function lapse does not sink a package.",
		run:   mWrapRatio,
	},
	{
		name:  "wide-interface",
		title: "Interfaces with the most methods (interfacebloat): every implementer signs the whole contract",
		notes: "ANSWERS interfaces declaring many methods, with how often they appear as a\n    parameter type: a fat interface forces mocks to implement methods\n    their tests never call and makes the next implementation a chore.\nACT split along the calls actually made at each site (consumer-side\n    interfaces, one or two methods).\nMISLEADS a broad interface backed by one canonical implementation is\n    sometimes the honest shape (database/sql.DB-like handles); used_as_\n    param matches the interface name as a parameter-type suffix, so a\n    same-named unrelated type rides along; embedded interfaces inflate\n    the method count without new surface.",
		run:   mWideInterface,
	},
}

var symColNames = []string{
	"id",
	"file_id",
	"module_id",
	"parent_id",
	"name",
	"qual_name",
	"kind",
	"line_start",
	"line_end",
	"n_lines",
	"byte_start",
	"byte_end",
	"signature",
	"return_type",
	"visibility",
	"n_params",
	"n_optional_params",
	"n_generic_params",
	"n_overloads",
	"arity_rank",
	"is_public",
	"is_static",
	"is_async",
	"is_generator",
	"is_abstract",
	"is_override",
	"is_exported",
	"is_test",
	"is_deprecated",
	"is_entrypoint",
	"is_generated",
	"sloc",
	"body_bytes",
	"n_comment_lines",
	"n_doc_lines",
	"has_doc",
	"cyclomatic",
	"cognitive",
	"max_nesting",
	"n_tokens",
	"n_operators",
	"n_operands",
	"n_distinct_operators",
	"n_distinct_operands",
	"halstead_volume",
	"maintainability",
	"n_loops",
	"n_branches",
	"n_returns",
	"n_early_returns",
	"n_switch",
	"n_cases",
	"n_ternary",
	"n_logical",
	"n_try",
	"n_catch",
	"n_catch_broad",
	"n_catch_empty",
	"n_finally",
	"n_throw",
	"n_labels",
	"n_gotos",
	"max_loop_depth",
	"call_in_loop",
	"alloc_in_loop",
	"io_in_loop",
	"await_in_loop",
	"lock_in_loop",
	"concat_in_loop",
	"regex_in_loop",
	"query_in_loop",
	"branch_in_loop",
	"n_locals",
	"n_assign",
	"n_compound_assign",
	"n_incdec",
	"n_cmp",
	"n_bitop",
	"n_shift",
	"n_arith",
	"n_string_lit",
	"n_regex_lit",
	"n_float_lit",
	"n_magic",
	"n_null_check",
	"n_subscript",
	"n_member_access",
	"n_lambda",
	"n_closure_capture",
	"n_calls",
	"n_unique_calls",
	"n_dynamic_calls",
	"n_unresolved_calls",
	"fan_in",
	"fan_out",
	"n_callsites",
	"is_recursive",
	"is_leaf",
	"is_root",
	"n_hazards",
	"risk_score",
	"n_goroutine",
	"n_channel",
	"n_defer",
	"n_lock",
	"n_atomic",
	"n_context",
	"n_io",
	"n_net",
	"n_sql",
	"n_exec",
	"n_unsafe",
	"n_reflect",
	"n_cgo",
	"n_alloc",
	"n_panic",
	"n_time",
	"n_goroutines",
	"n_go_in_loop",
	"n_defer_in_loop",
	"n_defer_close",
	"n_recover",
	"n_chan_send",
	"n_chan_recv",
	"n_chan_close",
	"n_chan_type",
	"n_chan_unbuffered",
	"n_select",
	"n_select_default",
	"n_select_ctx_done",
	"n_type_switch",
	"n_type_assert",
	"n_type_assert_unchecked",
	"n_ctx_params",
	"n_ctx_background",
	"n_ctx_done",
	"n_ctx_passed",
	"n_ctx_withcancel",
	"n_cancel_called",
	"n_err_returns",
	"n_err_checks",
	"n_err_ignored",
	"n_err_shadowed",
	"n_err_wrapped",
	"n_naked_returns",
	"n_named_results",
	"n_any_params",
	"n_iface_params",
	"n_iface_returns",
	"n_iface_literal",
	"n_make_no_cap",
	"n_append_in_loop",
	"n_sprintf_in_loop",
	"n_conv_in_loop",
	"n_range_value_copy",
	"n_loopvar_capture",
	"n_composite_lit",
	"n_struct_literal",
	"n_unsafe_ops",
	"n_cgo_calls",
	"n_reflect_ops",
	"n_go_directives",
	"n_struct_tags",
	"n_panics",
	"n_log_fatal",
	"n_time_tick",
	"n_sql_concat",
	"n_lock_by_value_params",
	"n_nolint",
	"n_ctx_background_call",
	"n_http_default_client",
	"n_exit_call",
	"n_time_after_in_loop",
	"n_time_tick_call",
	"n_errorf_no_wrap",
	"n_weak_random",
	"n_weak_crypto",
	"n_readall_in_loop",
	"n_env_read",
	"n_redirect",
	"n_auth_call",
	"n_deserialize",
	"n_dynamic_open",
	"n_zip_read",
	"n_decode_call",
	"n_waitgroup_add",
	"n_lock_call",
	"n_unlock_call",
	"n_close_call",
	"n_reflect_call",
	"n_unsafe_call",
	"n_exec_call",
	"n_pathjoin_in_loop",
	"n_elif",
	"n_external_calls",
	"receiver_is_pointer",
	"receiver_type",
	"is_handler",
	"is_init",
	"n_ctx_in_loop",
	"n_err_nil_return",
	"n_loopvar_rebind",
	"n_insecure_tls",
	"n_wg_done",
	"n_wait_call",
	"n_sleep",
	"n_rows_err_check",
	"n_timer_new",
	"n_timer_stop",
	"n_semaphore",
}

type metric struct {
	NParams              int32
	NOptionalParams      int32
	NGenericParams       int32
	IsPublic             int32
	IsTest               int32
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
	NLoops               int32
	NBranches            int32
	NReturns             int32
	NEarlyReturns        int32
	NSwitch              int32
	NCases               int32
	NLogical             int32
	NLabels              int32
	NGotos               int32
	MaxLoopDepth         int32
	CallInLoop           int32
	LockInLoop           int32
	RegexInLoop          int32
	QueryInLoop          int32
	BranchInLoop         int32
	NAssign              int32
	NIncdec              int32
	NCmp                 int32
	NBitop               int32
	NShift               int32
	NArith               int32
	NStringLit           int32
	NFloatLit            int32
	NMagic               int32
	NSubscript           int32
	NMemberAccess        int32
	NLambda              int32
	NCalls               int32
	NDynamicCalls        int32
	NDefer               int32
	NGoroutines          int32
	NRecover             int32
	NChanSend            int32
	NChanRecv            int32
	NChanClose           int32
	NChanType            int32
	NChanUnbuffered      int32
	NSelect              int32
	NSelectDefault       int32
	NSelectCtxDone       int32
	NTypeSwitch          int32
	NTypeAssert          int32
	NTypeAssertUnchecked int32
	NCtxParams           int32
	NCtxBackground       int32
	NCtxDone             int32
	NCtxPassed           int32
	NCtxWithcancel       int32
	NCancelCalled        int32
	NErrReturns          int32
	NErrChecks           int32
	NErrIgnored          int32
	NErrShadowed         int32
	NErrWrapped          int32
	NNakedReturns        int32
	NNamedResults        int32
	NAnyParams           int32
	NIfaceParams         int32
	NIfaceReturns        int32
	NIfaceLiteral        int32
	NMakeNoCap           int32
	NAppendInLoop        int32
	NSprintfInLoop       int32
	NConvInLoop          int32
	NRangeValueCopy      int32
	NCompositeLit        int32
	NStructLiteral       int32
	NUnsafeOps           int32
	NCgoCalls            int32
	NReflectOps          int32
	NStructTags          int32
	NPanics              int32
	NLogFatal            int32
	NTimeTick            int32
	NSqlConcat           int32
	NCtxBackgroundCall   int32
	NHttpDefaultClient   int32
	NExitCall            int32
	NTimeAfterInLoop     int32
	NTimeTickCall        int32
	NErrorfNoWrap        int32
	NWeakRandom          int32
	NWeakCrypto          int32
	NReadallInLoop       int32
	NEnvRead             int32
	NRedirect            int32
	NAuthCall            int32
	NDeserialize         int32
	NDynamicOpen         int32
	NZipRead             int32
	NDecodeCall          int32
	NWaitgroupAdd        int32
	NLockCall            int32
	NUnlockCall          int32
	NCloseCall           int32
	NReflectCall         int32
	NUnsafeCall          int32
	NExecCall            int32
	NPathjoinInLoop      int32
	NElif                int32
	ReceiverIsPointer    int32
	IsHandler            int32
	IsInit               int32
	NCtxInLoop           int32
	NErrNilReturn        int32
	NLoopvarRebind       int32
	NInsecureTls         int32
	NWgDone              int32
	NWaitCall            int32
	NSleep               int32
	NRowsErrCheck        int32
	NTimerNew            int32
	NTimerStop           int32
	NSemaphore           int32
}

var metricNames = []string{
	"n_params",
	"n_optional_params",
	"n_generic_params",
	"is_public",
	"is_test",
	"is_entrypoint",
	"is_generated",
	"sloc",
	"body_bytes",
	"n_comment_lines",
	"n_doc_lines",
	"has_doc",
	"cyclomatic",
	"cognitive",
	"max_nesting",
	"n_tokens",
	"n_operators",
	"n_operands",
	"n_distinct_operators",
	"n_distinct_operands",
	"n_loops",
	"n_branches",
	"n_returns",
	"n_early_returns",
	"n_switch",
	"n_cases",
	"n_logical",
	"n_labels",
	"n_gotos",
	"max_loop_depth",
	"call_in_loop",
	"lock_in_loop",
	"regex_in_loop",
	"query_in_loop",
	"branch_in_loop",
	"n_assign",
	"n_incdec",
	"n_cmp",
	"n_bitop",
	"n_shift",
	"n_arith",
	"n_string_lit",
	"n_float_lit",
	"n_magic",
	"n_subscript",
	"n_member_access",
	"n_lambda",
	"n_calls",
	"n_dynamic_calls",
	"n_defer",
	"n_goroutines",
	"n_recover",
	"n_chan_send",
	"n_chan_recv",
	"n_chan_close",
	"n_chan_type",
	"n_chan_unbuffered",
	"n_select",
	"n_select_default",
	"n_select_ctx_done",
	"n_type_switch",
	"n_type_assert",
	"n_type_assert_unchecked",
	"n_ctx_params",
	"n_ctx_background",
	"n_ctx_done",
	"n_ctx_passed",
	"n_ctx_withcancel",
	"n_cancel_called",
	"n_err_returns",
	"n_err_checks",
	"n_err_ignored",
	"n_err_shadowed",
	"n_err_wrapped",
	"n_naked_returns",
	"n_named_results",
	"n_any_params",
	"n_iface_params",
	"n_iface_returns",
	"n_iface_literal",
	"n_make_no_cap",
	"n_append_in_loop",
	"n_sprintf_in_loop",
	"n_conv_in_loop",
	"n_range_value_copy",
	"n_composite_lit",
	"n_struct_literal",
	"n_unsafe_ops",
	"n_cgo_calls",
	"n_reflect_ops",
	"n_struct_tags",
	"n_panics",
	"n_log_fatal",
	"n_time_tick",
	"n_sql_concat",
	"n_ctx_background_call",
	"n_http_default_client",
	"n_exit_call",
	"n_time_after_in_loop",
	"n_time_tick_call",
	"n_errorf_no_wrap",
	"n_weak_random",
	"n_weak_crypto",
	"n_readall_in_loop",
	"n_env_read",
	"n_redirect",
	"n_auth_call",
	"n_deserialize",
	"n_dynamic_open",
	"n_zip_read",
	"n_decode_call",
	"n_waitgroup_add",
	"n_lock_call",
	"n_unlock_call",
	"n_close_call",
	"n_reflect_call",
	"n_unsafe_call",
	"n_exec_call",
	"n_pathjoin_in_loop",
	"n_elif",
	"receiver_is_pointer",
	"is_handler",
	"is_init",
	"n_ctx_in_loop",
	"n_err_nil_return",
	"n_loopvar_rebind",
	"n_insecure_tls",
	"n_wg_done",
	"n_wait_call",
	"n_sleep",
	"n_rows_err_check",
	"n_timer_new",
	"n_timer_stop",
	"n_semaphore",
}

var metricIndex = func() map[string]int {
	m := make(map[string]int, len(metricNames))
	for i, n := range metricNames {
		m[n] = i
	}
	return m
}()

type Syms struct {
	n                    int
	Id                   []int32
	FileId               []int32
	ModuleId             []int32
	ParentId             []int32
	Name                 []uint32
	QualName             []uint32
	Kind                 []uint32
	LineStart            []int32
	LineEnd              []int32
	NLines               []int32
	ByteStart            []int32
	ByteEnd              []int32
	Signature            []uint32
	ReturnType           []uint32
	Visibility           []uint32
	NParams              []int32
	NOptionalParams      []int32
	NGenericParams       []int32
	IsPublic             []int32
	IsTest               []int32
	IsEntrypoint         []int32
	IsGenerated          []int32
	Sloc                 []int32
	BodyBytes            []int32
	NCommentLines        []int32
	NDocLines            []int32
	HasDoc               []int32
	Cyclomatic           []int32
	Cognitive            []int32
	MaxNesting           []int32
	NTokens              []int32
	NOperators           []int32
	NOperands            []int32
	NDistinctOperators   []int32
	NDistinctOperands    []int32
	HalsteadVolume       []int32
	Maintainability      []int32
	NLoops               []int32
	NBranches            []int32
	NReturns             []int32
	NEarlyReturns        []int32
	NSwitch              []int32
	NCases               []int32
	NLogical             []int32
	NLabels              []int32
	NGotos               []int32
	MaxLoopDepth         []int32
	CallInLoop           []int32
	LockInLoop           []int32
	RegexInLoop          []int32
	QueryInLoop          []int32
	BranchInLoop         []int32
	NAssign              []int32
	NIncdec              []int32
	NCmp                 []int32
	NBitop               []int32
	NShift               []int32
	NArith               []int32
	NStringLit           []int32
	NFloatLit            []int32
	NMagic               []int32
	NSubscript           []int32
	NMemberAccess        []int32
	NLambda              []int32
	NCalls               []int32
	NUniqueCalls         []int32
	NDynamicCalls        []int32
	NUnresolvedCalls     []int32
	FanIn                []int32
	FanOut               []int32
	NCallsites           []int32
	IsRecursive          []int32
	IsLeaf               []int32
	IsRoot               []int32
	NHazards             []int32
	RiskScore            []int32
	NGoroutine           []int32
	NChannel             []int32
	NDefer               []int32
	NLock                []int32
	NAtomic              []int32
	NContext             []int32
	NIo                  []int32
	NNet                 []int32
	NSql                 []int32
	NExec                []int32
	NUnsafe              []int32
	NReflect             []int32
	NCgo                 []int32
	NAlloc               []int32
	NPanic               []int32
	NTime                []int32
	NGoroutines          []int32
	NGoInLoop            []int32
	NDeferInLoop         []int32
	NDeferClose          []int32
	NRecover             []int32
	NChanSend            []int32
	NChanRecv            []int32
	NChanClose           []int32
	NChanType            []int32
	NChanUnbuffered      []int32
	NSelect              []int32
	NSelectDefault       []int32
	NSelectCtxDone       []int32
	NTypeSwitch          []int32
	NTypeAssert          []int32
	NTypeAssertUnchecked []int32
	NCtxParams           []int32
	NCtxBackground       []int32
	NCtxDone             []int32
	NCtxPassed           []int32
	NCtxWithcancel       []int32
	NCancelCalled        []int32
	NErrReturns          []int32
	NErrChecks           []int32
	NErrIgnored          []int32
	NErrShadowed         []int32
	NErrWrapped          []int32
	NNakedReturns        []int32
	NNamedResults        []int32
	NAnyParams           []int32
	NIfaceParams         []int32
	NIfaceReturns        []int32
	NIfaceLiteral        []int32
	NMakeNoCap           []int32
	NAppendInLoop        []int32
	NSprintfInLoop       []int32
	NConvInLoop          []int32
	NRangeValueCopy      []int32
	NCompositeLit        []int32
	NStructLiteral       []int32
	NUnsafeOps           []int32
	NCgoCalls            []int32
	NReflectOps          []int32
	NStructTags          []int32
	NPanics              []int32
	NLogFatal            []int32
	NTimeTick            []int32
	NSqlConcat           []int32
	NCtxBackgroundCall   []int32
	NHttpDefaultClient   []int32
	NExitCall            []int32
	NTimeAfterInLoop     []int32
	NTimeTickCall        []int32
	NErrorfNoWrap        []int32
	NWeakRandom          []int32
	NWeakCrypto          []int32
	NReadallInLoop       []int32
	NEnvRead             []int32
	NRedirect            []int32
	NAuthCall            []int32
	NDeserialize         []int32
	NDynamicOpen         []int32
	NZipRead             []int32
	NDecodeCall          []int32
	NWaitgroupAdd        []int32
	NLockCall            []int32
	NUnlockCall          []int32
	NCloseCall           []int32
	NReflectCall         []int32
	NUnsafeCall          []int32
	NExecCall            []int32
	NPathjoinInLoop      []int32
	NElif                []int32
	NExternalCalls       []int32
	ReceiverIsPointer    []int32
	ReceiverType         []uint32
	IsHandler            []int32
	IsInit               []int32
	NCtxInLoop           []int32
	NErrNilReturn        []int32
	NLoopvarRebind       []int32
	NInsecureTls         []int32
	NWgDone              []int32
	NWaitCall            []int32
	NSleep               []int32
	NRowsErrCheck        []int32
	NTimerNew            []int32
	NTimerStop           []int32
	NSemaphore           []int32
}

func (s *Syms) push() int {
	i := s.n
	s.n = i + 1
	s.Id = append(s.Id, 0)
	s.FileId = append(s.FileId, 0)
	s.ModuleId = append(s.ModuleId, 0)
	s.ParentId = append(s.ParentId, 0)
	s.Name = append(s.Name, 0)
	s.QualName = append(s.QualName, 0)
	s.Kind = append(s.Kind, 0)
	s.LineStart = append(s.LineStart, 0)
	s.LineEnd = append(s.LineEnd, 0)
	s.NLines = append(s.NLines, 0)
	s.ByteStart = append(s.ByteStart, 0)
	s.ByteEnd = append(s.ByteEnd, 0)
	s.Signature = append(s.Signature, 0)
	s.ReturnType = append(s.ReturnType, 0)
	s.Visibility = append(s.Visibility, 0)
	s.NParams = append(s.NParams, 0)
	s.NOptionalParams = append(s.NOptionalParams, 0)
	s.NGenericParams = append(s.NGenericParams, 0)
	s.IsPublic = append(s.IsPublic, 0)
	s.IsTest = append(s.IsTest, 0)
	s.IsEntrypoint = append(s.IsEntrypoint, 0)
	s.IsGenerated = append(s.IsGenerated, 0)
	s.Sloc = append(s.Sloc, 0)
	s.BodyBytes = append(s.BodyBytes, 0)
	s.NCommentLines = append(s.NCommentLines, 0)
	s.NDocLines = append(s.NDocLines, 0)
	s.HasDoc = append(s.HasDoc, 0)
	s.Cyclomatic = append(s.Cyclomatic, 0)
	s.Cognitive = append(s.Cognitive, 0)
	s.MaxNesting = append(s.MaxNesting, 0)
	s.NTokens = append(s.NTokens, 0)
	s.NOperators = append(s.NOperators, 0)
	s.NOperands = append(s.NOperands, 0)
	s.NDistinctOperators = append(s.NDistinctOperators, 0)
	s.NDistinctOperands = append(s.NDistinctOperands, 0)
	s.HalsteadVolume = append(s.HalsteadVolume, 0)
	s.Maintainability = append(s.Maintainability, 0)
	s.NLoops = append(s.NLoops, 0)
	s.NBranches = append(s.NBranches, 0)
	s.NReturns = append(s.NReturns, 0)
	s.NEarlyReturns = append(s.NEarlyReturns, 0)
	s.NSwitch = append(s.NSwitch, 0)
	s.NCases = append(s.NCases, 0)
	s.NLogical = append(s.NLogical, 0)
	s.NLabels = append(s.NLabels, 0)
	s.NGotos = append(s.NGotos, 0)
	s.MaxLoopDepth = append(s.MaxLoopDepth, 0)
	s.CallInLoop = append(s.CallInLoop, 0)
	s.LockInLoop = append(s.LockInLoop, 0)
	s.RegexInLoop = append(s.RegexInLoop, 0)
	s.QueryInLoop = append(s.QueryInLoop, 0)
	s.BranchInLoop = append(s.BranchInLoop, 0)
	s.NAssign = append(s.NAssign, 0)
	s.NIncdec = append(s.NIncdec, 0)
	s.NCmp = append(s.NCmp, 0)
	s.NBitop = append(s.NBitop, 0)
	s.NShift = append(s.NShift, 0)
	s.NArith = append(s.NArith, 0)
	s.NStringLit = append(s.NStringLit, 0)
	s.NFloatLit = append(s.NFloatLit, 0)
	s.NMagic = append(s.NMagic, 0)
	s.NSubscript = append(s.NSubscript, 0)
	s.NMemberAccess = append(s.NMemberAccess, 0)
	s.NLambda = append(s.NLambda, 0)
	s.NCalls = append(s.NCalls, 0)
	s.NUniqueCalls = append(s.NUniqueCalls, 0)
	s.NDynamicCalls = append(s.NDynamicCalls, 0)
	s.NUnresolvedCalls = append(s.NUnresolvedCalls, 0)
	s.FanIn = append(s.FanIn, 0)
	s.FanOut = append(s.FanOut, 0)
	s.NCallsites = append(s.NCallsites, 0)
	s.IsRecursive = append(s.IsRecursive, 0)
	s.IsLeaf = append(s.IsLeaf, 0)
	s.IsRoot = append(s.IsRoot, 0)
	s.NHazards = append(s.NHazards, 0)
	s.RiskScore = append(s.RiskScore, 0)
	s.NGoroutine = append(s.NGoroutine, 0)
	s.NChannel = append(s.NChannel, 0)
	s.NDefer = append(s.NDefer, 0)
	s.NLock = append(s.NLock, 0)
	s.NAtomic = append(s.NAtomic, 0)
	s.NContext = append(s.NContext, 0)
	s.NIo = append(s.NIo, 0)
	s.NNet = append(s.NNet, 0)
	s.NSql = append(s.NSql, 0)
	s.NExec = append(s.NExec, 0)
	s.NUnsafe = append(s.NUnsafe, 0)
	s.NReflect = append(s.NReflect, 0)
	s.NCgo = append(s.NCgo, 0)
	s.NAlloc = append(s.NAlloc, 0)
	s.NPanic = append(s.NPanic, 0)
	s.NTime = append(s.NTime, 0)
	s.NGoroutines = append(s.NGoroutines, 0)
	s.NGoInLoop = append(s.NGoInLoop, 0)
	s.NDeferInLoop = append(s.NDeferInLoop, 0)
	s.NDeferClose = append(s.NDeferClose, 0)
	s.NRecover = append(s.NRecover, 0)
	s.NChanSend = append(s.NChanSend, 0)
	s.NChanRecv = append(s.NChanRecv, 0)
	s.NChanClose = append(s.NChanClose, 0)
	s.NChanType = append(s.NChanType, 0)
	s.NChanUnbuffered = append(s.NChanUnbuffered, 0)
	s.NSelect = append(s.NSelect, 0)
	s.NSelectDefault = append(s.NSelectDefault, 0)
	s.NSelectCtxDone = append(s.NSelectCtxDone, 0)
	s.NTypeSwitch = append(s.NTypeSwitch, 0)
	s.NTypeAssert = append(s.NTypeAssert, 0)
	s.NTypeAssertUnchecked = append(s.NTypeAssertUnchecked, 0)
	s.NCtxParams = append(s.NCtxParams, 0)
	s.NCtxBackground = append(s.NCtxBackground, 0)
	s.NCtxDone = append(s.NCtxDone, 0)
	s.NCtxPassed = append(s.NCtxPassed, 0)
	s.NCtxWithcancel = append(s.NCtxWithcancel, 0)
	s.NCancelCalled = append(s.NCancelCalled, 0)
	s.NErrReturns = append(s.NErrReturns, 0)
	s.NErrChecks = append(s.NErrChecks, 0)
	s.NErrIgnored = append(s.NErrIgnored, 0)
	s.NErrShadowed = append(s.NErrShadowed, 0)
	s.NErrWrapped = append(s.NErrWrapped, 0)
	s.NNakedReturns = append(s.NNakedReturns, 0)
	s.NNamedResults = append(s.NNamedResults, 0)
	s.NAnyParams = append(s.NAnyParams, 0)
	s.NIfaceParams = append(s.NIfaceParams, 0)
	s.NIfaceReturns = append(s.NIfaceReturns, 0)
	s.NIfaceLiteral = append(s.NIfaceLiteral, 0)
	s.NMakeNoCap = append(s.NMakeNoCap, 0)
	s.NAppendInLoop = append(s.NAppendInLoop, 0)
	s.NSprintfInLoop = append(s.NSprintfInLoop, 0)
	s.NConvInLoop = append(s.NConvInLoop, 0)
	s.NRangeValueCopy = append(s.NRangeValueCopy, 0)
	s.NCompositeLit = append(s.NCompositeLit, 0)
	s.NStructLiteral = append(s.NStructLiteral, 0)
	s.NUnsafeOps = append(s.NUnsafeOps, 0)
	s.NCgoCalls = append(s.NCgoCalls, 0)
	s.NReflectOps = append(s.NReflectOps, 0)
	s.NStructTags = append(s.NStructTags, 0)
	s.NPanics = append(s.NPanics, 0)
	s.NLogFatal = append(s.NLogFatal, 0)
	s.NTimeTick = append(s.NTimeTick, 0)
	s.NSqlConcat = append(s.NSqlConcat, 0)
	s.NCtxBackgroundCall = append(s.NCtxBackgroundCall, 0)
	s.NHttpDefaultClient = append(s.NHttpDefaultClient, 0)
	s.NExitCall = append(s.NExitCall, 0)
	s.NTimeAfterInLoop = append(s.NTimeAfterInLoop, 0)
	s.NTimeTickCall = append(s.NTimeTickCall, 0)
	s.NErrorfNoWrap = append(s.NErrorfNoWrap, 0)
	s.NWeakRandom = append(s.NWeakRandom, 0)
	s.NWeakCrypto = append(s.NWeakCrypto, 0)
	s.NReadallInLoop = append(s.NReadallInLoop, 0)
	s.NEnvRead = append(s.NEnvRead, 0)
	s.NRedirect = append(s.NRedirect, 0)
	s.NAuthCall = append(s.NAuthCall, 0)
	s.NDeserialize = append(s.NDeserialize, 0)
	s.NDynamicOpen = append(s.NDynamicOpen, 0)
	s.NZipRead = append(s.NZipRead, 0)
	s.NDecodeCall = append(s.NDecodeCall, 0)
	s.NWaitgroupAdd = append(s.NWaitgroupAdd, 0)
	s.NLockCall = append(s.NLockCall, 0)
	s.NUnlockCall = append(s.NUnlockCall, 0)
	s.NCloseCall = append(s.NCloseCall, 0)
	s.NReflectCall = append(s.NReflectCall, 0)
	s.NUnsafeCall = append(s.NUnsafeCall, 0)
	s.NExecCall = append(s.NExecCall, 0)
	s.NPathjoinInLoop = append(s.NPathjoinInLoop, 0)
	s.NElif = append(s.NElif, 0)
	s.NExternalCalls = append(s.NExternalCalls, 0)
	s.ReceiverIsPointer = append(s.ReceiverIsPointer, 0)
	s.ReceiverType = append(s.ReceiverType, 0)
	s.IsHandler = append(s.IsHandler, 0)
	s.IsInit = append(s.IsInit, 0)
	s.NCtxInLoop = append(s.NCtxInLoop, 0)
	s.NErrNilReturn = append(s.NErrNilReturn, 0)
	s.NLoopvarRebind = append(s.NLoopvarRebind, 0)
	s.NInsecureTls = append(s.NInsecureTls, 0)
	s.NWgDone = append(s.NWgDone, 0)
	s.NWaitCall = append(s.NWaitCall, 0)
	s.NSleep = append(s.NSleep, 0)
	s.NRowsErrCheck = append(s.NRowsErrCheck, 0)
	s.NTimerNew = append(s.NTimerNew, 0)
	s.NTimerStop = append(s.NTimerStop, 0)
	s.NSemaphore = append(s.NSemaphore, 0)
	return i
}

func (s *Syms) put(col string, v int32) {
	switch col {
	case "n_params":
		s.NParams[s.n-1] = v
	case "n_optional_params":
		s.NOptionalParams[s.n-1] = v
	case "n_generic_params":
		s.NGenericParams[s.n-1] = v
	case "is_public":
		s.IsPublic[s.n-1] = v
	case "is_test":
		s.IsTest[s.n-1] = v
	case "is_entrypoint":
		s.IsEntrypoint[s.n-1] = v
	case "is_generated":
		s.IsGenerated[s.n-1] = v
	case "sloc":
		s.Sloc[s.n-1] = v
	case "body_bytes":
		s.BodyBytes[s.n-1] = v
	case "n_comment_lines":
		s.NCommentLines[s.n-1] = v
	case "n_doc_lines":
		s.NDocLines[s.n-1] = v
	case "has_doc":
		s.HasDoc[s.n-1] = v
	case "cyclomatic":
		s.Cyclomatic[s.n-1] = v
	case "cognitive":
		s.Cognitive[s.n-1] = v
	case "max_nesting":
		s.MaxNesting[s.n-1] = v
	case "n_tokens":
		s.NTokens[s.n-1] = v
	case "n_operators":
		s.NOperators[s.n-1] = v
	case "n_operands":
		s.NOperands[s.n-1] = v
	case "n_distinct_operators":
		s.NDistinctOperators[s.n-1] = v
	case "n_distinct_operands":
		s.NDistinctOperands[s.n-1] = v
	case "n_loops":
		s.NLoops[s.n-1] = v
	case "n_branches":
		s.NBranches[s.n-1] = v
	case "n_returns":
		s.NReturns[s.n-1] = v
	case "n_early_returns":
		s.NEarlyReturns[s.n-1] = v
	case "n_switch":
		s.NSwitch[s.n-1] = v
	case "n_cases":
		s.NCases[s.n-1] = v
	case "n_logical":
		s.NLogical[s.n-1] = v
	case "n_labels":
		s.NLabels[s.n-1] = v
	case "n_gotos":
		s.NGotos[s.n-1] = v
	case "max_loop_depth":
		s.MaxLoopDepth[s.n-1] = v
	case "call_in_loop":
		s.CallInLoop[s.n-1] = v
	case "lock_in_loop":
		s.LockInLoop[s.n-1] = v
	case "regex_in_loop":
		s.RegexInLoop[s.n-1] = v
	case "query_in_loop":
		s.QueryInLoop[s.n-1] = v
	case "branch_in_loop":
		s.BranchInLoop[s.n-1] = v
	case "n_assign":
		s.NAssign[s.n-1] = v
	case "n_incdec":
		s.NIncdec[s.n-1] = v
	case "n_cmp":
		s.NCmp[s.n-1] = v
	case "n_bitop":
		s.NBitop[s.n-1] = v
	case "n_shift":
		s.NShift[s.n-1] = v
	case "n_arith":
		s.NArith[s.n-1] = v
	case "n_string_lit":
		s.NStringLit[s.n-1] = v
	case "n_float_lit":
		s.NFloatLit[s.n-1] = v
	case "n_magic":
		s.NMagic[s.n-1] = v
	case "n_subscript":
		s.NSubscript[s.n-1] = v
	case "n_member_access":
		s.NMemberAccess[s.n-1] = v
	case "n_lambda":
		s.NLambda[s.n-1] = v
	case "n_calls":
		s.NCalls[s.n-1] = v
	case "n_dynamic_calls":
		s.NDynamicCalls[s.n-1] = v
	case "n_defer":
		s.NDefer[s.n-1] = v
	case "n_goroutines":
		s.NGoroutines[s.n-1] = v
	case "n_recover":
		s.NRecover[s.n-1] = v
	case "n_chan_send":
		s.NChanSend[s.n-1] = v
	case "n_chan_recv":
		s.NChanRecv[s.n-1] = v
	case "n_chan_close":
		s.NChanClose[s.n-1] = v
	case "n_chan_type":
		s.NChanType[s.n-1] = v
	case "n_chan_unbuffered":
		s.NChanUnbuffered[s.n-1] = v
	case "n_select":
		s.NSelect[s.n-1] = v
	case "n_select_default":
		s.NSelectDefault[s.n-1] = v
	case "n_select_ctx_done":
		s.NSelectCtxDone[s.n-1] = v
	case "n_type_switch":
		s.NTypeSwitch[s.n-1] = v
	case "n_type_assert":
		s.NTypeAssert[s.n-1] = v
	case "n_type_assert_unchecked":
		s.NTypeAssertUnchecked[s.n-1] = v
	case "n_ctx_params":
		s.NCtxParams[s.n-1] = v
	case "n_ctx_background":
		s.NCtxBackground[s.n-1] = v
	case "n_ctx_done":
		s.NCtxDone[s.n-1] = v
	case "n_ctx_passed":
		s.NCtxPassed[s.n-1] = v
	case "n_ctx_withcancel":
		s.NCtxWithcancel[s.n-1] = v
	case "n_cancel_called":
		s.NCancelCalled[s.n-1] = v
	case "n_err_returns":
		s.NErrReturns[s.n-1] = v
	case "n_err_checks":
		s.NErrChecks[s.n-1] = v
	case "n_err_ignored":
		s.NErrIgnored[s.n-1] = v
	case "n_err_shadowed":
		s.NErrShadowed[s.n-1] = v
	case "n_err_wrapped":
		s.NErrWrapped[s.n-1] = v
	case "n_naked_returns":
		s.NNakedReturns[s.n-1] = v
	case "n_named_results":
		s.NNamedResults[s.n-1] = v
	case "n_any_params":
		s.NAnyParams[s.n-1] = v
	case "n_iface_params":
		s.NIfaceParams[s.n-1] = v
	case "n_iface_returns":
		s.NIfaceReturns[s.n-1] = v
	case "n_iface_literal":
		s.NIfaceLiteral[s.n-1] = v
	case "n_make_no_cap":
		s.NMakeNoCap[s.n-1] = v
	case "n_append_in_loop":
		s.NAppendInLoop[s.n-1] = v
	case "n_sprintf_in_loop":
		s.NSprintfInLoop[s.n-1] = v
	case "n_conv_in_loop":
		s.NConvInLoop[s.n-1] = v
	case "n_range_value_copy":
		s.NRangeValueCopy[s.n-1] = v
	case "n_composite_lit":
		s.NCompositeLit[s.n-1] = v
	case "n_struct_literal":
		s.NStructLiteral[s.n-1] = v
	case "n_unsafe_ops":
		s.NUnsafeOps[s.n-1] = v
	case "n_cgo_calls":
		s.NCgoCalls[s.n-1] = v
	case "n_reflect_ops":
		s.NReflectOps[s.n-1] = v
	case "n_struct_tags":
		s.NStructTags[s.n-1] = v
	case "n_panics":
		s.NPanics[s.n-1] = v
	case "n_log_fatal":
		s.NLogFatal[s.n-1] = v
	case "n_time_tick":
		s.NTimeTick[s.n-1] = v
	case "n_sql_concat":
		s.NSqlConcat[s.n-1] = v
	case "n_ctx_background_call":
		s.NCtxBackgroundCall[s.n-1] = v
	case "n_http_default_client":
		s.NHttpDefaultClient[s.n-1] = v
	case "n_exit_call":
		s.NExitCall[s.n-1] = v
	case "n_time_after_in_loop":
		s.NTimeAfterInLoop[s.n-1] = v
	case "n_time_tick_call":
		s.NTimeTickCall[s.n-1] = v
	case "n_errorf_no_wrap":
		s.NErrorfNoWrap[s.n-1] = v
	case "n_weak_random":
		s.NWeakRandom[s.n-1] = v
	case "n_weak_crypto":
		s.NWeakCrypto[s.n-1] = v
	case "n_readall_in_loop":
		s.NReadallInLoop[s.n-1] = v
	case "n_env_read":
		s.NEnvRead[s.n-1] = v
	case "n_redirect":
		s.NRedirect[s.n-1] = v
	case "n_auth_call":
		s.NAuthCall[s.n-1] = v
	case "n_deserialize":
		s.NDeserialize[s.n-1] = v
	case "n_dynamic_open":
		s.NDynamicOpen[s.n-1] = v
	case "n_zip_read":
		s.NZipRead[s.n-1] = v
	case "n_decode_call":
		s.NDecodeCall[s.n-1] = v
	case "n_waitgroup_add":
		s.NWaitgroupAdd[s.n-1] = v
	case "n_lock_call":
		s.NLockCall[s.n-1] = v
	case "n_unlock_call":
		s.NUnlockCall[s.n-1] = v
	case "n_close_call":
		s.NCloseCall[s.n-1] = v
	case "n_reflect_call":
		s.NReflectCall[s.n-1] = v
	case "n_unsafe_call":
		s.NUnsafeCall[s.n-1] = v
	case "n_exec_call":
		s.NExecCall[s.n-1] = v
	case "n_pathjoin_in_loop":
		s.NPathjoinInLoop[s.n-1] = v
	case "n_elif":
		s.NElif[s.n-1] = v
	case "receiver_is_pointer":
		s.ReceiverIsPointer[s.n-1] = v
	case "is_handler":
		s.IsHandler[s.n-1] = v
	case "is_init":
		s.IsInit[s.n-1] = v
	case "n_ctx_in_loop":
		s.NCtxInLoop[s.n-1] = v
	case "n_err_nil_return":
		s.NErrNilReturn[s.n-1] = v
	case "n_loopvar_rebind":
		s.NLoopvarRebind[s.n-1] = v
	case "n_insecure_tls":
		s.NInsecureTls[s.n-1] = v
	case "n_wg_done":
		s.NWgDone[s.n-1] = v
	case "n_wait_call":
		s.NWaitCall[s.n-1] = v
	case "n_sleep":
		s.NSleep[s.n-1] = v
	case "n_rows_err_check":
		s.NRowsErrCheck[s.n-1] = v
	case "n_timer_new":
		s.NTimerNew[s.n-1] = v
	case "n_timer_stop":
		s.NTimerStop[s.n-1] = v
	case "n_semaphore":
		s.NSemaphore[s.n-1] = v
	}
}

func (s *Syms) symDump(i int, g *Graph, b *[]byte) {
	*b = append(*b, 'R', ' ')
	putI(b, int64(i+1))
	putSep(b)
	if s.FileId[i] < 0 {
		putNull(b)
	} else {
		putI(b, int64(s.FileId[i])+1)
	}
	putSep(b)
	if s.ModuleId[i] < 0 {
		putNull(b)
	} else {
		putI(b, int64(s.ModuleId[i])+1)
	}
	putSep(b)
	if s.ParentId[i] < 0 {
		putNull(b)
	} else {
		putI(b, int64(s.ParentId[i])+1)
	}
	putSep(b)
	if s.Name[i] == nullStr {
		putNull(b)
	} else {
		putText(b, g.Str.get(s.Name[i]))
	}
	putSep(b)
	if s.QualName[i] == nullStr {
		putNull(b)
	} else {
		putText(b, g.Str.get(s.QualName[i]))
	}
	putSep(b)
	if s.Kind[i] == nullStr {
		putNull(b)
	} else {
		putText(b, g.Str.get(s.Kind[i]))
	}
	putSep(b)
	putI(b, int64(s.LineStart[i]))
	putSep(b)
	putI(b, int64(s.LineEnd[i]))
	putSep(b)
	putI(b, int64(s.NLines[i]))
	putSep(b)
	putI(b, int64(s.ByteStart[i]))
	putSep(b)
	putI(b, int64(s.ByteEnd[i]))
	putSep(b)
	if s.Signature[i] == nullStr {
		putNull(b)
	} else {
		putText(b, g.Str.get(s.Signature[i]))
	}
	putSep(b)
	if s.ReturnType[i] == nullStr {
		putNull(b)
	} else {
		putText(b, g.Str.get(s.ReturnType[i]))
	}
	putSep(b)
	if s.Visibility[i] == nullStr {
		putNull(b)
	} else {
		putText(b, g.Str.get(s.Visibility[i]))
	}
	putSep(b)
	putI(b, int64(s.NParams[i]))
	putSep(b)
	putI(b, int64(s.NOptionalParams[i]))
	putSep(b)
	putI(b, int64(s.NGenericParams[i]))
	putSep(b)
	putI(b, 0)
	putSep(b)
	putI(b, 0)
	putSep(b)
	putI(b, int64(s.IsPublic[i]))
	putSep(b)
	putI(b, 0)
	putSep(b)
	putI(b, 0)
	putSep(b)
	putI(b, 0)
	putSep(b)
	putI(b, 0)
	putSep(b)
	putI(b, 0)
	putSep(b)
	putI(b, 0)
	putSep(b)
	putI(b, int64(s.IsTest[i]))
	putSep(b)
	putI(b, 0)
	putSep(b)
	putI(b, int64(s.IsEntrypoint[i]))
	putSep(b)
	putI(b, int64(s.IsGenerated[i]))
	putSep(b)
	putI(b, int64(s.Sloc[i]))
	putSep(b)
	putI(b, int64(s.BodyBytes[i]))
	putSep(b)
	putI(b, int64(s.NCommentLines[i]))
	putSep(b)
	putI(b, int64(s.NDocLines[i]))
	putSep(b)
	putI(b, int64(s.HasDoc[i]))
	putSep(b)
	putI(b, int64(s.Cyclomatic[i]))
	putSep(b)
	putI(b, int64(s.Cognitive[i]))
	putSep(b)
	putI(b, int64(s.MaxNesting[i]))
	putSep(b)
	putI(b, int64(s.NTokens[i]))
	putSep(b)
	putI(b, int64(s.NOperators[i]))
	putSep(b)
	putI(b, int64(s.NOperands[i]))
	putSep(b)
	putI(b, int64(s.NDistinctOperators[i]))
	putSep(b)
	putI(b, int64(s.NDistinctOperands[i]))
	putSep(b)
	putI(b, int64(s.HalsteadVolume[i]))
	putSep(b)
	putI(b, int64(s.Maintainability[i]))
	putSep(b)
	putI(b, int64(s.NLoops[i]))
	putSep(b)
	putI(b, int64(s.NBranches[i]))
	putSep(b)
	putI(b, int64(s.NReturns[i]))
	putSep(b)
	putI(b, int64(s.NEarlyReturns[i]))
	putSep(b)
	putI(b, int64(s.NSwitch[i]))
	putSep(b)
	putI(b, int64(s.NCases[i]))
	putSep(b)
	putI(b, 0)
	putSep(b)
	putI(b, int64(s.NLogical[i]))
	putSep(b)
	putI(b, 0)
	putSep(b)
	putI(b, 0)
	putSep(b)
	putI(b, 0)
	putSep(b)
	putI(b, 0)
	putSep(b)
	putI(b, 0)
	putSep(b)
	putI(b, 0)
	putSep(b)
	putI(b, int64(s.NLabels[i]))
	putSep(b)
	putI(b, int64(s.NGotos[i]))
	putSep(b)
	putI(b, int64(s.MaxLoopDepth[i]))
	putSep(b)
	putI(b, int64(s.CallInLoop[i]))
	putSep(b)
	putI(b, 0)
	putSep(b)
	putI(b, 0)
	putSep(b)
	putI(b, 0)
	putSep(b)
	putI(b, int64(s.LockInLoop[i]))
	putSep(b)
	putI(b, 0)
	putSep(b)
	putI(b, int64(s.RegexInLoop[i]))
	putSep(b)
	putI(b, int64(s.QueryInLoop[i]))
	putSep(b)
	putI(b, int64(s.BranchInLoop[i]))
	putSep(b)
	putI(b, 0)
	putSep(b)
	putI(b, int64(s.NAssign[i]))
	putSep(b)
	putI(b, 0)
	putSep(b)
	putI(b, int64(s.NIncdec[i]))
	putSep(b)
	putI(b, int64(s.NCmp[i]))
	putSep(b)
	putI(b, int64(s.NBitop[i]))
	putSep(b)
	putI(b, int64(s.NShift[i]))
	putSep(b)
	putI(b, int64(s.NArith[i]))
	putSep(b)
	putI(b, int64(s.NStringLit[i]))
	putSep(b)
	putI(b, 0)
	putSep(b)
	putI(b, int64(s.NFloatLit[i]))
	putSep(b)
	putI(b, int64(s.NMagic[i]))
	putSep(b)
	putI(b, 0)
	putSep(b)
	putI(b, int64(s.NSubscript[i]))
	putSep(b)
	putI(b, int64(s.NMemberAccess[i]))
	putSep(b)
	putI(b, int64(s.NLambda[i]))
	putSep(b)
	putI(b, 0)
	putSep(b)
	putI(b, int64(s.NCalls[i]))
	putSep(b)
	putI(b, int64(s.NUniqueCalls[i]))
	putSep(b)
	putI(b, int64(s.NDynamicCalls[i]))
	putSep(b)
	putI(b, int64(s.NUnresolvedCalls[i]))
	putSep(b)
	putI(b, int64(s.FanIn[i]))
	putSep(b)
	putI(b, int64(s.FanOut[i]))
	putSep(b)
	putI(b, int64(s.NCallsites[i]))
	putSep(b)
	putI(b, int64(s.IsRecursive[i]))
	putSep(b)
	putI(b, int64(s.IsLeaf[i]))
	putSep(b)
	putI(b, int64(s.IsRoot[i]))
	putSep(b)
	putI(b, int64(s.NHazards[i]))
	putSep(b)
	putI(b, int64(s.RiskScore[i]))
	putSep(b)
	putI(b, int64(s.NGoroutine[i]))
	putSep(b)
	putI(b, int64(s.NChannel[i]))
	putSep(b)
	putI(b, int64(s.NDefer[i]))
	putSep(b)
	putI(b, int64(s.NLock[i]))
	putSep(b)
	putI(b, int64(s.NAtomic[i]))
	putSep(b)
	putI(b, int64(s.NContext[i]))
	putSep(b)
	putI(b, int64(s.NIo[i]))
	putSep(b)
	putI(b, int64(s.NNet[i]))
	putSep(b)
	putI(b, int64(s.NSql[i]))
	putSep(b)
	putI(b, int64(s.NExec[i]))
	putSep(b)
	putI(b, int64(s.NUnsafe[i]))
	putSep(b)
	putI(b, int64(s.NReflect[i]))
	putSep(b)
	putI(b, int64(s.NCgo[i]))
	putSep(b)
	putI(b, int64(s.NAlloc[i]))
	putSep(b)
	putI(b, int64(s.NPanic[i]))
	putSep(b)
	putI(b, int64(s.NTime[i]))
	putSep(b)
	putI(b, int64(s.NGoroutines[i]))
	putSep(b)
	putI(b, int64(s.NGoInLoop[i]))
	putSep(b)
	putI(b, int64(s.NDeferInLoop[i]))
	putSep(b)
	putI(b, int64(s.NDeferClose[i]))
	putSep(b)
	putI(b, int64(s.NRecover[i]))
	putSep(b)
	putI(b, int64(s.NChanSend[i]))
	putSep(b)
	putI(b, int64(s.NChanRecv[i]))
	putSep(b)
	putI(b, int64(s.NChanClose[i]))
	putSep(b)
	putI(b, int64(s.NChanType[i]))
	putSep(b)
	putI(b, int64(s.NChanUnbuffered[i]))
	putSep(b)
	putI(b, int64(s.NSelect[i]))
	putSep(b)
	putI(b, int64(s.NSelectDefault[i]))
	putSep(b)
	putI(b, int64(s.NSelectCtxDone[i]))
	putSep(b)
	putI(b, int64(s.NTypeSwitch[i]))
	putSep(b)
	putI(b, int64(s.NTypeAssert[i]))
	putSep(b)
	putI(b, int64(s.NTypeAssertUnchecked[i]))
	putSep(b)
	putI(b, int64(s.NCtxParams[i]))
	putSep(b)
	putI(b, int64(s.NCtxBackground[i]))
	putSep(b)
	putI(b, int64(s.NCtxDone[i]))
	putSep(b)
	putI(b, int64(s.NCtxPassed[i]))
	putSep(b)
	putI(b, int64(s.NCtxWithcancel[i]))
	putSep(b)
	putI(b, int64(s.NCancelCalled[i]))
	putSep(b)
	putI(b, int64(s.NErrReturns[i]))
	putSep(b)
	putI(b, int64(s.NErrChecks[i]))
	putSep(b)
	putI(b, int64(s.NErrIgnored[i]))
	putSep(b)
	putI(b, int64(s.NErrShadowed[i]))
	putSep(b)
	putI(b, int64(s.NErrWrapped[i]))
	putSep(b)
	putI(b, int64(s.NNakedReturns[i]))
	putSep(b)
	putI(b, int64(s.NNamedResults[i]))
	putSep(b)
	putI(b, int64(s.NAnyParams[i]))
	putSep(b)
	putI(b, int64(s.NIfaceParams[i]))
	putSep(b)
	putI(b, int64(s.NIfaceReturns[i]))
	putSep(b)
	putI(b, int64(s.NIfaceLiteral[i]))
	putSep(b)
	putI(b, int64(s.NMakeNoCap[i]))
	putSep(b)
	putI(b, int64(s.NAppendInLoop[i]))
	putSep(b)
	putI(b, int64(s.NSprintfInLoop[i]))
	putSep(b)
	putI(b, int64(s.NConvInLoop[i]))
	putSep(b)
	putI(b, int64(s.NRangeValueCopy[i]))
	putSep(b)
	putI(b, 0)
	putSep(b)
	putI(b, int64(s.NCompositeLit[i]))
	putSep(b)
	putI(b, int64(s.NStructLiteral[i]))
	putSep(b)
	putI(b, int64(s.NUnsafeOps[i]))
	putSep(b)
	putI(b, int64(s.NCgoCalls[i]))
	putSep(b)
	putI(b, int64(s.NReflectOps[i]))
	putSep(b)
	putI(b, 0)
	putSep(b)
	putI(b, int64(s.NStructTags[i]))
	putSep(b)
	putI(b, int64(s.NPanics[i]))
	putSep(b)
	putI(b, int64(s.NLogFatal[i]))
	putSep(b)
	putI(b, int64(s.NTimeTick[i]))
	putSep(b)
	putI(b, int64(s.NSqlConcat[i]))
	putSep(b)
	putI(b, 0)
	putSep(b)
	putI(b, 0)
	putSep(b)
	putI(b, int64(s.NCtxBackgroundCall[i]))
	putSep(b)
	putI(b, int64(s.NHttpDefaultClient[i]))
	putSep(b)
	putI(b, int64(s.NExitCall[i]))
	putSep(b)
	putI(b, int64(s.NTimeAfterInLoop[i]))
	putSep(b)
	putI(b, int64(s.NTimeTickCall[i]))
	putSep(b)
	putI(b, int64(s.NErrorfNoWrap[i]))
	putSep(b)
	putI(b, int64(s.NWeakRandom[i]))
	putSep(b)
	putI(b, int64(s.NWeakCrypto[i]))
	putSep(b)
	putI(b, int64(s.NReadallInLoop[i]))
	putSep(b)
	putI(b, int64(s.NEnvRead[i]))
	putSep(b)
	putI(b, int64(s.NRedirect[i]))
	putSep(b)
	putI(b, int64(s.NAuthCall[i]))
	putSep(b)
	putI(b, int64(s.NDeserialize[i]))
	putSep(b)
	putI(b, int64(s.NDynamicOpen[i]))
	putSep(b)
	putI(b, int64(s.NZipRead[i]))
	putSep(b)
	putI(b, int64(s.NDecodeCall[i]))
	putSep(b)
	putI(b, int64(s.NWaitgroupAdd[i]))
	putSep(b)
	putI(b, int64(s.NLockCall[i]))
	putSep(b)
	putI(b, int64(s.NUnlockCall[i]))
	putSep(b)
	putI(b, int64(s.NCloseCall[i]))
	putSep(b)
	putI(b, int64(s.NReflectCall[i]))
	putSep(b)
	putI(b, int64(s.NUnsafeCall[i]))
	putSep(b)
	putI(b, int64(s.NExecCall[i]))
	putSep(b)
	putI(b, int64(s.NPathjoinInLoop[i]))
	putSep(b)
	putI(b, int64(s.NElif[i]))
	putSep(b)
	putI(b, int64(s.NExternalCalls[i]))
	putSep(b)
	putI(b, int64(s.ReceiverIsPointer[i]))
	putSep(b)
	if s.ReceiverType[i] == nullStr {
		putNull(b)
	} else {
		putText(b, g.Str.get(s.ReceiverType[i]))
	}
	putSep(b)
	putI(b, int64(s.IsHandler[i]))
	putSep(b)
	putI(b, int64(s.IsInit[i]))
	putSep(b)
	putI(b, int64(s.NCtxInLoop[i]))
	putSep(b)
	putI(b, int64(s.NErrNilReturn[i]))
	putSep(b)
	putI(b, int64(s.NLoopvarRebind[i]))
	putSep(b)
	putI(b, int64(s.NInsecureTls[i]))
	putSep(b)
	putI(b, int64(s.NWgDone[i]))
	putSep(b)
	putI(b, int64(s.NWaitCall[i]))
	putSep(b)
	putI(b, int64(s.NSleep[i]))
	putSep(b)
	putI(b, int64(s.NRowsErrCheck[i]))
	putSep(b)
	putI(b, int64(s.NTimerNew[i]))
	putSep(b)
	putI(b, int64(s.NTimerStop[i]))
	putSep(b)
	putI(b, int64(s.NSemaphore[i]))
}
func (s *Syms) putIdx(i, j int, v int32) {
	switch j {
	case 0:
		s.NParams[i] = v
	case 1:
		s.NOptionalParams[i] = v
	case 2:
		s.NGenericParams[i] = v
	case 3:
		s.IsPublic[i] = v
	case 4:
		s.IsTest[i] = v
	case 5:
		s.IsEntrypoint[i] = v
	case 6:
		s.IsGenerated[i] = v
	case 7:
		s.Sloc[i] = v
	case 8:
		s.BodyBytes[i] = v
	case 9:
		s.NCommentLines[i] = v
	case 10:
		s.NDocLines[i] = v
	case 11:
		s.HasDoc[i] = v
	case 12:
		s.Cyclomatic[i] = v
	case 13:
		s.Cognitive[i] = v
	case 14:
		s.MaxNesting[i] = v
	case 15:
		s.NTokens[i] = v
	case 16:
		s.NOperators[i] = v
	case 17:
		s.NOperands[i] = v
	case 18:
		s.NDistinctOperators[i] = v
	case 19:
		s.NDistinctOperands[i] = v
	case 20:
		s.NLoops[i] = v
	case 21:
		s.NBranches[i] = v
	case 22:
		s.NReturns[i] = v
	case 23:
		s.NEarlyReturns[i] = v
	case 24:
		s.NSwitch[i] = v
	case 25:
		s.NCases[i] = v
	case 26:
		s.NLogical[i] = v
	case 27:
		s.NLabels[i] = v
	case 28:
		s.NGotos[i] = v
	case 29:
		s.MaxLoopDepth[i] = v
	case 30:
		s.CallInLoop[i] = v
	case 31:
		s.LockInLoop[i] = v
	case 32:
		s.RegexInLoop[i] = v
	case 33:
		s.QueryInLoop[i] = v
	case 34:
		s.BranchInLoop[i] = v
	case 35:
		s.NAssign[i] = v
	case 36:
		s.NIncdec[i] = v
	case 37:
		s.NCmp[i] = v
	case 38:
		s.NBitop[i] = v
	case 39:
		s.NShift[i] = v
	case 40:
		s.NArith[i] = v
	case 41:
		s.NStringLit[i] = v
	case 42:
		s.NFloatLit[i] = v
	case 43:
		s.NMagic[i] = v
	case 44:
		s.NSubscript[i] = v
	case 45:
		s.NMemberAccess[i] = v
	case 46:
		s.NLambda[i] = v
	case 47:
		s.NCalls[i] = v
	case 48:
		s.NDynamicCalls[i] = v
	case 49:
		s.NDefer[i] = v
	case 50:
		s.NGoroutines[i] = v
	case 51:
		s.NRecover[i] = v
	case 52:
		s.NChanSend[i] = v
	case 53:
		s.NChanRecv[i] = v
	case 54:
		s.NChanClose[i] = v
	case 55:
		s.NChanType[i] = v
	case 56:
		s.NChanUnbuffered[i] = v
	case 57:
		s.NSelect[i] = v
	case 58:
		s.NSelectDefault[i] = v
	case 59:
		s.NSelectCtxDone[i] = v
	case 60:
		s.NTypeSwitch[i] = v
	case 61:
		s.NTypeAssert[i] = v
	case 62:
		s.NTypeAssertUnchecked[i] = v
	case 63:
		s.NCtxParams[i] = v
	case 64:
		s.NCtxBackground[i] = v
	case 65:
		s.NCtxDone[i] = v
	case 66:
		s.NCtxPassed[i] = v
	case 67:
		s.NCtxWithcancel[i] = v
	case 68:
		s.NCancelCalled[i] = v
	case 69:
		s.NErrReturns[i] = v
	case 70:
		s.NErrChecks[i] = v
	case 71:
		s.NErrIgnored[i] = v
	case 72:
		s.NErrShadowed[i] = v
	case 73:
		s.NErrWrapped[i] = v
	case 74:
		s.NNakedReturns[i] = v
	case 75:
		s.NNamedResults[i] = v
	case 76:
		s.NAnyParams[i] = v
	case 77:
		s.NIfaceParams[i] = v
	case 78:
		s.NIfaceReturns[i] = v
	case 79:
		s.NIfaceLiteral[i] = v
	case 80:
		s.NMakeNoCap[i] = v
	case 81:
		s.NAppendInLoop[i] = v
	case 82:
		s.NSprintfInLoop[i] = v
	case 83:
		s.NConvInLoop[i] = v
	case 84:
		s.NRangeValueCopy[i] = v
	case 85:
		s.NCompositeLit[i] = v
	case 86:
		s.NStructLiteral[i] = v
	case 87:
		s.NUnsafeOps[i] = v
	case 88:
		s.NCgoCalls[i] = v
	case 89:
		s.NReflectOps[i] = v
	case 90:
		s.NStructTags[i] = v
	case 91:
		s.NPanics[i] = v
	case 92:
		s.NLogFatal[i] = v
	case 93:
		s.NTimeTick[i] = v
	case 94:
		s.NSqlConcat[i] = v
	case 95:
		s.NCtxBackgroundCall[i] = v
	case 96:
		s.NHttpDefaultClient[i] = v
	case 97:
		s.NExitCall[i] = v
	case 98:
		s.NTimeAfterInLoop[i] = v
	case 99:
		s.NTimeTickCall[i] = v
	case 100:
		s.NErrorfNoWrap[i] = v
	case 101:
		s.NWeakRandom[i] = v
	case 102:
		s.NWeakCrypto[i] = v
	case 103:
		s.NReadallInLoop[i] = v
	case 104:
		s.NEnvRead[i] = v
	case 105:
		s.NRedirect[i] = v
	case 106:
		s.NAuthCall[i] = v
	case 107:
		s.NDeserialize[i] = v
	case 108:
		s.NDynamicOpen[i] = v
	case 109:
		s.NZipRead[i] = v
	case 110:
		s.NDecodeCall[i] = v
	case 111:
		s.NWaitgroupAdd[i] = v
	case 112:
		s.NLockCall[i] = v
	case 113:
		s.NUnlockCall[i] = v
	case 114:
		s.NCloseCall[i] = v
	case 115:
		s.NReflectCall[i] = v
	case 116:
		s.NUnsafeCall[i] = v
	case 117:
		s.NExecCall[i] = v
	case 118:
		s.NPathjoinInLoop[i] = v
	case 119:
		s.NElif[i] = v
	case 120:
		s.ReceiverIsPointer[i] = v
	case 121:
		s.IsHandler[i] = v
	case 122:
		s.IsInit[i] = v
	case 123:
		s.NCtxInLoop[i] = v
	case 124:
		s.NErrNilReturn[i] = v
	case 125:
		s.NLoopvarRebind[i] = v
	case 126:
		s.NInsecureTls[i] = v
	case 127:
		s.NWgDone[i] = v
	case 128:
		s.NWaitCall[i] = v
	case 129:
		s.NSleep[i] = v
	case 130:
		s.NRowsErrCheck[i] = v
	case 131:
		s.NTimerNew[i] = v
	case 132:
		s.NTimerStop[i] = v
	case 133:
		s.NSemaphore[i] = v
	}
}

func sqlRound(x float64, n int) float64 {
	if math.IsNaN(x) || math.IsInf(x, 0) {
		return x
	}
	if n < 0 {
		n = -n
	}
	r := new(big.Rat).SetFloat64(x)
	if r == nil {
		return x
	}
	scale := new(big.Int).Exp(big.NewInt(10), big.NewInt(int64(n)), nil)
	asRat := new(big.Rat).SetInt(scale)
	r.Mul(r, asRat)
	q, rem := new(big.Int).QuoRem(r.Num(), r.Denom(), new(big.Int))

	if rem.Abs(rem); rem.Lsh(rem, 1).Cmp(r.Denom()) >= 0 {
		one := big.NewInt(1)
		if r.Sign() < 0 {
			q.Sub(q, one)
		} else {
			q.Add(q, one)
		}
	}
	out := new(big.Rat).SetInt(q)
	f, _ := out.Quo(out, asRat).Float64()
	return f
}

type modAcc struct {
	fns, calls, external, unresolved, reflect   int32
	spawns, inLoop, semaphores, underHandlers   int32
	locks, unlocks, sends, recvs, closes, unbuf int32
	chanTypes, opens, closeCalls                int32
	wrapped, unwrapped, atomics                 int32
	defersClose, defersUnlock, defersDone       int32
	cyclo, sloc                                 int32
	names                                       []string
}

func (g *Graph) modAcc(mid int32) *modAcc {
	if g.modAccs == nil {
		g.modAccs = make(map[int32]*modAcc, len(g.Mod))
	}
	a := g.modAccs[mid]
	if a == nil {
		a = &modAcc{}
		g.modAccs[mid] = a
	}
	return a
}

func (g *Graph) perModule(pat string, noTestGen bool, fold func(a *modAcc, i int32)) {
	for i := 0; i < g.Sym.n; i++ {
		k := g.kind(int32(i))
		if k != "function" && k != "method" {
			continue
		}
		fid := g.Sym.FileId[i]
		f := &g.File[fid]
		if noTestGen && (f.IsTest != 0 || f.IsGen != 0) {
			continue
		}
		if !likePat(modName(g, g.Sym.ModuleId[i]), pat) {
			continue
		}
		fold(g.modAcc(g.Sym.ModuleId[i]), int32(i))
	}
}

func (g *Graph) moduleIDs() []int32 {
	ids := make([]int32, len(g.Mod))
	for i := range ids {
		ids[i] = int32(i)
	}
	return ids
}

func mGraphBlindspots(g *Graph, pat string, lim int) result {
	r := result{cols: []string{"package_", "fns", "calls", "external",
		"unresolved", "reflect_", "pct_blind"}, lim: lim}
	g.perModule(pat, false, func(a *modAcc, i int32) {
		s := &g.Sym
		a.fns++
		a.calls += s.NCalls[i]
		a.external += s.NExternalCalls[i]
		a.unresolved += s.NUnresolvedCalls[i]
		a.reflect += s.NReflectOps[i]
	})
	for _, m := range g.moduleIDs() {
		a := g.modAccs[m]
		if a == nil || a.calls == 0 {
			continue
		}
		r.rows = append(r.rows, row(nil, cs(g.Mod[m].Name), ci(int64(a.fns)),
			ci(int64(a.calls)), ci(int64(a.external)), ci(int64(a.unresolved)),
			ci(int64(a.reflect)), ci(int64(100*a.unresolved/a.calls))))
	}
	return sortRows(r, 4)
}

func tailIdent(t string) string {
	end := len(t)
	for end > 0 && isIdentByte(t[end-1]) {
		end--
	}
	return t[end:]
}

func isIdentByte(c byte) bool {
	return c == '_' || c >= 'a' && c <= 'z' || c >= 'A' && c <= 'Z' || c >= '0' && c <= '9'
}

func (g *Graph) paramTailCounts() map[string]int32 {
	m := map[string]int32{}
	for i := range g.Params {
		m[tailIdent(g.Str.get(g.Params[i].Typ))]++
	}
	return m
}

func (g *Graph) ifaceImpls(id int32) (impls, tests int32, names []string) {
	seen := map[string]bool{}
	for i := range g.Impl {
		if g.Impl[i].InterfaceID != id {
			continue
		}
		n := g.Str.get(g.Impl[i].TypeName)
		if g.Impl[i].InTest != 0 {
			tests++
			continue
		}
		impls++
		if !seen[n] {
			seen[n] = true
			names = append(names, n)
		}
	}
	return
}

func mSingleImplInterface(g *Graph, pat string, lim int) result {
	r := result{cols: []string{"iface", "methods", "embedded", "exported",
		"type_constraint", "used_as_param", "impls", "test_impls",
		"implemented_by", "methods", "at"}, lim: lim}
	used := g.paramTailCounts()

	var total int32
	first := -1
	var firstIfc *Iface
	var firstSid int32
	for i := range g.Iface {
		ifc := &g.Iface[i]
		if ifc.Constraint != 0 || ifc.NMethods == 0 {
			continue
		}
		sid := ifc.SymbolID
		if g.File[g.Sym.FileId[sid]].IsTest != 0 || !likePat(modName(g, g.Sym.ModuleId[sid]), pat) {
			continue
		}
		impls, _, _ := g.ifaceImpls(sid)
		if impls != 1 {
			continue
		}
		if first < 0 {
			first, firstIfc, firstSid = i, ifc, sid
		}
		total += used[g.name(sid)]
	}
	if first < 0 {
		r.rows = append(r.rows, row(nil, cnull, cnull, cnull, cnull, cnull,
			ci(0), ci(0), ci(0), cnull, cnull, cnull))
		return r
	}
	impls, tests, names := g.ifaceImpls(firstSid)
	r.rows = append(r.rows, row(nil, cs(g.name(firstSid)),
		ci(int64(firstIfc.NMethods)), ci(int64(firstIfc.NEmbedded)),
		ci(int64(firstIfc.Exported)), ci(int64(firstIfc.Constraint)),
		ci(int64(total)), ci(int64(impls)), ci(int64(tests)),
		cs(joinDistinct(names)), cs(g.Str.get(firstIfc.Methods)), cs(g.at(firstSid))))
	return r
}

func mWideInterface(g *Graph, pat string, lim int) result {
	r := result{cols: []string{"iface", "methods", "embedded", "used_as_param",
		"impls", "at"}, lim: lim}
	used := g.paramTailCounts()
	for i := range g.Iface {
		ifc := &g.Iface[i]
		if ifc.Constraint != 0 || ifc.NMethods < 4 {
			continue
		}
		sid := ifc.SymbolID
		f := &g.File[g.Sym.FileId[sid]]
		if f.IsTest != 0 || f.IsGen != 0 || !likePat(modName(g, g.Sym.ModuleId[sid]), pat) {
			continue
		}
		impls, _, _ := g.ifaceImpls(sid)
		r.rows = append(r.rows, row(nil, cs(g.name(sid)), ci(int64(ifc.NMethods)),
			ci(int64(ifc.NEmbedded)), ci(int64(used[g.name(sid)])), ci(int64(impls)),
			cs(g.at(sid))))
	}
	return sortRows(r, 1, 3)
}

func mHeapPressureLoops(g *Graph, pat string, lim int) result {
	r := result{cols: []string{"name", "sprintf_loop", "append_loop",
		"make_no_cap", "conv_loop", "any_params", "iface_params", "depth",
		"fan_in", "heap_pressure", "at"}, lim: lim}
	s := &g.Sym

	for _, i := range g.matchedSyms(pat) {
		if s.MaxLoopDepth[i] == 0 {
			continue
		}
		if s.NSprintfInLoop[i]+s.NAppendInLoop[i]+s.NMakeNoCap[i]+
			s.NConvInLoop[i]+s.NAnyParams[i] == 0 {
			continue
		}
		hp := (s.NSprintfInLoop[i]*4 + s.NAppendInLoop[i]*2 + s.NMakeNoCap[i]*3 +
			s.NConvInLoop[i]*2 + s.NAnyParams[i]) * (1 + s.MaxLoopDepth[i])
		r.rows = append(r.rows, row(nil, cs(g.name(i)), ci(int64(s.NSprintfInLoop[i])),
			ci(int64(s.NAppendInLoop[i])), ci(int64(s.NMakeNoCap[i])),
			ci(int64(s.NConvInLoop[i])), ci(int64(s.NAnyParams[i])),
			ci(int64(s.NIfaceParams[i])), ci(int64(s.MaxLoopDepth[i])),
			ci(int64(s.FanIn[i])), ci(int64(hp)), cs(g.at(i))))
	}
	return sortRows(r, 9)
}

func mRangeValueCopy(g *Graph, pat string, lim int) result {
	r := result{cols: []string{"in_fn", "range_copies", "depth", "calls_in_loop",
		"fan_in", "sloc", "biggest_local_struct", "at"}, lim: lim}
	s := &g.Sym

	maxEst := map[int32]int32{}
	for i := range g.Structs {
		st := &g.Structs[i]
		mid := s.ModuleId[st.SymbolID]
		if cur, ok := maxEst[mid]; !ok || st.EstSize > cur {
			maxEst[mid] = st.EstSize
		}
	}
	for _, i := range g.matchedSyms(pat) {
		if s.NRangeValueCopy[i] == 0 {
			continue
		}
		big := cnull
		if mx, ok := maxEst[s.ModuleId[i]]; ok {
			big = ci(int64(mx))
		}
		r.rows = append(r.rows, row(nil, cs(g.name(i)), ci(int64(s.NRangeValueCopy[i])),
			ci(int64(s.MaxLoopDepth[i])), ci(int64(s.CallInLoop[i])),
			ci(int64(s.FanIn[i])), ci(int64(s.Sloc[i])),
			big, cs(g.at(i))))
	}
	return sortRows(r, 1, 2)
}

func mRiskRanked(g *Graph, pat string, lim int) result {
	r := result{cols: []string{"name", "risk", "cyclo", "cog", "nest",
		"unsafe_", "err_ign", "spawns", "fan_in", "at"}, lim: lim}
	s := &g.Sym
	for _, i := range g.fnSyms(pat, true) {
		if g.inGenFile(i) {
			continue
		}
		r.rows = append(r.rows, row(nil, cs(g.name(i)), ci(int64(s.RiskScore[i])),
			ci(int64(s.Cyclomatic[i])), ci(int64(s.Cognitive[i])),
			ci(int64(s.MaxNesting[i])), ci(int64(s.NUnsafe[i]+s.NCgo[i])),
			ci(int64(s.NErrIgnored[i])), ci(int64(s.NGoroutines[i])),
			ci(int64(s.FanIn[i])), cs(g.at(i))))
	}
	return sortRows(r, 1)
}

func mHotMultipliers(g *Graph, pat string, lim int) result {
	r := result{cols: []string{"name", "fan_in", "sites", "fan_out", "cyclo",
		"sloc", "doc", "recv", "package_", "at"}, lim: lim}
	s := &g.Sym
	for _, i := range g.fnSyms(pat, true) {
		r.rows = append(r.rows, row(nil, cs(g.name(i)), ci(int64(s.FanIn[i])),
			ci(int64(s.NCallsites[i])), ci(int64(s.FanOut[i])),
			ci(int64(s.Cyclomatic[i])), ci(int64(s.Sloc[i])), ci(int64(s.HasDoc[i])),
			cs(g.recv(i)), cs(modName(g, s.ModuleId[i])), cs(g.at(i))))
	}
	return sortRows(r, 1, 4)
}

func mGodFunctions(g *Graph, pat string, lim int) result {
	r := result{cols: []string{"name", "sloc", "cyclo", "cog", "nest", "elifs",
		"returns_", "naked", "n_params", "maint", "at"}, lim: lim}
	s := &g.Sym
	for _, i := range g.fnSyms(pat, true) {
		if g.inGenFile(i) {
			continue
		}
		r.rows = append(r.rows, row(nil, cs(g.name(i)), ci(int64(s.Sloc[i])),
			ci(int64(s.Cyclomatic[i])), ci(int64(s.Cognitive[i])),
			ci(int64(s.MaxNesting[i])), ci(int64(s.NElif[i])),
			ci(int64(s.NReturns[i])), ci(int64(s.NNakedReturns[i])),
			ci(int64(s.NParams[i])), ci(int64(s.Maintainability[i])), cs(g.at(i))))
	}
	return sortRows(r, 3)
}

func mModuleCoupling(g *Graph, pat string, lim int) result {
	r := result{cols: []string{"name", "kind", "files", "sloc", "syms",
		"exported", "fan_in", "fan_out", "instability"}, lim: lim}
	for i := range g.Mod {
		m := &g.Mod[i]
		if m.NFiles == 0 || !likePat(m.Name, pat) {
			continue
		}
		r.krow([]int64{int64(m.FanIn) + int64(m.FanOut)},
			cs(m.Name), cs(m.Kind), ci(int64(m.NFiles)),
			ci(int64(m.Sloc)), ci(int64(m.NSyms)), ci(int64(m.NPublic)),
			ci(int64(m.FanIn)), ci(int64(m.FanOut)), cf(sqlRound(m.Instab, 2)))
	}

	return sortKeys(r, []bool{false})
}

func mMarkers(g *Graph, pat string, lim int) result {
	r := result{cols: []string{"kind", "path", "line", "text", "in_fn",
		"fan_in"}, lim: lim}
	kindOK := map[string]bool{"TODO": true, "FIXME": true, "HACK": true,
		"BUG": true, "XXX": true, "WARNING": true}
	s := &g.Sym
	for i := range g.Markers {
		mk := &g.Markers[i]
		if !kindOK[g.Str.get(mk.Kind)] {
			continue
		}
		f := &g.File[mk.FileID]
		if f.IsGen != 0 || !likePat(modName(g, f.ModuleID), pat) {
			continue
		}

		best, bestLen := int32(-1), int32(1<<30)
		for j := 0; j < s.n; j++ {
			k := g.kind(int32(j))
			if k != "function" && k != "method" {
				continue
			}
			if s.FileId[j] != mk.FileID {
				continue
			}
			if mk.Line < s.LineStart[j] || mk.Line > s.LineEnd[j] {
				continue
			}
			if w := s.LineEnd[j] - s.LineStart[j]; w < bestLen {
				bestLen, best = w, int32(j)
			}
		}
		name, fan := "(package level)", int32(0)
		if best >= 0 {
			name, fan = g.name(best), s.FanIn[best]
		}
		txt := g.Str.get(mk.Text)

		txt = trunc(txt, 58)
		r.rows = append(r.rows, row(nil, cs(g.Str.get(mk.Kind)), cs(f.Path),
			ci(int64(mk.Line)), cs(txt), cs(name), ci(int64(fan))))
	}
	return sortRows(r, 5)
}

func mParseCoverage(g *Graph, pat string, lim int) result {
	r := result{cols: []string{"path", "lines", "errors", "missing", "parsed",
		"generated", "test", "build_tags"}, lim: lim}
	for i := range g.File {
		f := &g.File[i]
		if f.NParsErr == 0 && f.Parsed != 0 {
			continue
		}
		if !likePat(modName(g, f.ModuleID), pat) {
			continue
		}
		var tags []string
		for j := range g.BuildTag {
			if g.BuildTag[j].FileID == int32(i) {
				tags = append(tags, g.Str.get(g.BuildTag[j].Expr))
			}
		}
		var tb cellVal = cnull
		if len(tags) > 0 {
			tb = cs(joinDistinct(tags))
		}
		r.rows = append(r.rows, row(nil, cs(f.Path), ci(int64(f.Lines)),
			ci(int64(f.NParsErr)), ci(int64(f.NMissing)), ci(int64(f.Parsed)),
			ci(int64(f.IsGen)), ci(int64(f.IsTest)), tb))
	}
	return sortRows(r, 1)
}

func mWrapperFunction(g *Graph, pat string, lim int) result {
	r := result{cols: []string{"name", "n_calls", "unique_callees", "sloc",
		"n_params", "fan_in", "sole_callee", "at"}, lim: lim}
	s := &g.Sym
	for _, i := range g.fnTestedRows(pat, true) {
		if s.NCalls[i] != 1 || s.NUniqueCalls[i] != 1 || s.Sloc[i] > 3 ||
			s.IsRecursive[i] != 0 {
			continue
		}
		lo, hi := g.Calls.Out.row(i)
		sole := cnull
		for p := lo; p < hi; p++ {
			e := &g.Calls.Out.val[p]
			if e.IsSelf == 0 {
				sole = cs(g.name(e.Callee))
				break
			}
		}
		r.rows = append(r.rows, row(nil, cs(g.name(i)), ci(int64(s.NCalls[i])),
			ci(int64(s.NUniqueCalls[i])), ci(int64(s.Sloc[i])),
			ci(int64(s.NParams[i])), ci(int64(s.FanIn[i])), sole, cs(g.at(i))))
	}
	return sortRows(r, 5)
}

func mNakedReturnComplex(g *Graph, pat string, lim int) result {
	r := result{cols: []string{"name", "naked_returns", "named_results",
		"cyclo", "sloc", "nesting", "fan_in", "at"}, lim: lim}
	s := &g.Sym
	for _, i := range g.symRows(pat) {
		if s.NNakedReturns[i] == 0 || s.Cyclomatic[i] <= 10 {
			continue
		}
		r.rows = append(r.rows, row(nil, cs(g.name(i)), ci(int64(s.NNakedReturns[i])),
			ci(int64(s.NNamedResults[i])), ci(int64(s.Cyclomatic[i])),
			ci(int64(s.Sloc[i])), ci(int64(s.MaxNesting[i])),
			ci(int64(s.FanIn[i])), cs(g.at(i))))
	}
	return sortRows(r, 3, 1)
}

func mScatteredConcerns(g *Graph, pat string, lim int) result {
	r := result{cols: []string{"name", "n_caller_modules", "fan_in", "cyclo",
		"sloc", "modules", "at"}, lim: lim}
	s := &g.Sym
	type acc struct {
		n     int32
		mods  map[int32]bool
		names []string
	}
	by := map[int32]*acc{}
	for _, e := range g.edgeList {
		if e.IsSelf != 0 {
			continue
		}
		mid := s.ModuleId[e.Caller]
		if mid < 0 || !likePat(modName(g, mid), pat) {
			continue
		}
		a := by[e.Callee]
		if a == nil {
			a = &acc{mods: map[int32]bool{}}
			by[e.Callee] = a
		}
		if !a.mods[mid] {
			a.mods[mid] = true
			a.n++
			a.names = append(a.names, g.Mod[mid].Name)
		}
	}
	var ids []int32
	for k := range by {
		ids = append(ids, k)
	}
	slices.Sort(ids)
	for _, id := range ids {
		a := by[id]
		if a.n <= 5 {
			continue
		}
		k := g.kind(id)
		if k != "function" && k != "method" {
			continue
		}
		if g.File[s.FileId[id]].IsTest != 0 {
			continue
		}
		r.rows = append(r.rows, row(nil, cs(g.name(id)), ci(int64(a.n)),
			ci(int64(s.FanIn[id])), ci(int64(s.Cyclomatic[id])),
			ci(int64(s.Sloc[id])), cs(joinDistinct(a.names)), cs(g.at(id))))
	}
	return sortRows(r, 1, 2)
}

func mGodModule(g *Graph, pat string, lim int) result {
	r := result{cols: []string{"name", "n_files", "n_symbols", "n_public",
		"sloc", "fan_in", "fan_out", "instability", "total_cyclo",
		"n_functions"}, lim: lim}
	s := &g.Sym
	for i := range g.Mod {
		m := &g.Mod[i]
		if m.NSyms <= 50 || !likePat(m.Name, pat) {
			continue
		}
		var cyclo, n int32
		for j := 0; j < s.n; j++ {
			if s.ModuleId[j] != int32(i) {
				continue
			}
			k := g.kind(int32(j))
			if k == "function" || k == "method" {
				cyclo += s.Cyclomatic[j]
				n++
			}
		}
		r.rows = append(r.rows, row(nil, cs(m.Name), ci(int64(m.NFiles)),
			ci(int64(m.NSyms)), ci(int64(m.NPublic)), ci(int64(m.Sloc)),
			ci(int64(m.FanIn)), ci(int64(m.FanOut)), cf(m.Instab),
			ci(int64(cyclo)), ci(int64(n))))
	}
	return sortRows(r, 8)
}

func mDeepCallChain(g *Graph, pat string, lim int) result {
	r := result{cols: []string{"name", "min_depth", "n_entrypoints", "fan_in",
		"cyclo", "sloc", "at"}, lim: lim}
	s := &g.Sym
	dist := g.reachFrom(func(i int32) bool {
		return s.IsHandler[i] == 1 || s.IsEntrypoint[i] == 1
	}, 8)
	for i := 0; i < s.n; i++ {
		d := dist[i]
		if d <= 6 {
			continue
		}
		if g.File[s.FileId[i]].IsTest != 0 || !likePat(modName(g, s.ModuleId[i]), pat) {
			continue
		}
		r.rows = append(r.rows, row(nil, cs(g.name(int32(i))), ci(int64(d)),
			ci(int64(g.countRootsReaching(int32(i), 8))),
			ci(int64(s.FanIn[i])), ci(int64(s.Cyclomatic[i])),
			ci(int64(s.Sloc[i])), cs(g.at(int32(i)))))
	}
	return sortRows(r, 1, 3)
}

func (g *Graph) countRootsReaching(sym int32, maxHops int32) int32 {
	s := &g.Sym
	seen := make([]int32, s.n)
	mark := int32(1)
	seen[sym] = mark
	frontier := []int32{sym}
	var roots int32
	for d := int32(0); d < maxHops && len(frontier) > 0; d++ {
		var next []int32
		for _, u := range frontier {
			lo, hi := g.Calls.In.row(u)
			for p := lo; p < hi; p++ {
				c := g.Calls.In.val[p]
				if c.IsSelf != 0 || seen[c.Callee] == mark {
					continue
				}
				seen[c.Callee] = mark
				next = append(next, c.Callee)
			}
		}
		for _, u := range next {
			if s.IsHandler[u] == 1 || s.IsEntrypoint[u] == 1 {
				roots++
			}
		}
		frontier = next
	}
	return roots
}

func mTooManyReturnPaths(g *Graph, pat string, lim int) result {
	r := result{cols: []string{"name", "returns", "early_returns", "defers",
		"recovers", "cyclo", "sloc", "fan_in", "at"}, lim: lim}
	s := &g.Sym
	for _, i := range g.symRows(pat) {
		if s.NReturns[i] <= 10 {
			continue
		}
		r.rows = append(r.rows, row(nil, cs(g.name(i)), ci(int64(s.NReturns[i])),
			ci(int64(s.NEarlyReturns[i])), ci(int64(s.NDeferClose[i])),
			ci(int64(s.NRecover[i])), ci(int64(s.Cyclomatic[i])),
			ci(int64(s.Sloc[i])), ci(int64(s.FanIn[i])), cs(g.at(i))))
	}
	return sortRows(r, 1, 5)
}

func mUnusedParams(g *Graph, pat string, lim int) result {
	r := result{cols: []string{"name", "n_params", "n_optional_params",
		"member_access", "subscripts", "n_calls", "sloc", "fan_in", "at"},
		lim: lim}
	s := &g.Sym
	for _, i := range g.symRows(pat) {
		if s.NParams[i] <= 3 {
			continue
		}
		if s.NMemberAccess[i]+s.NSubscript[i] >= s.NParams[i] {
			continue
		}
		r.rows = append(r.rows, row(nil, cs(g.name(i)), ci(int64(s.NParams[i])),
			ci(int64(s.NOptionalParams[i])), ci(int64(s.NMemberAccess[i])),
			ci(int64(s.NSubscript[i])), ci(int64(s.NCalls[i])),
			ci(int64(s.Sloc[i])), ci(int64(s.FanIn[i])), cs(g.at(i))))
	}
	return sortRows(r, 1, 7)
}

func mGoroutineFanoutDensity(g *Graph, pat string, lim int) result {
	r := result{cols: []string{"package_", "sloc", "spawns", "in_loop_spawns",
		"pct_in_loop", "per_ksloc", "limiter_sites", "under_handlers"}, lim: lim}
	s := &g.Sym
	g.perModule(pat, true, func(a *modAcc, i int32) {
		a.spawns += s.NGoroutines[i]
		a.inLoop += s.NGoInLoop[i]
		a.semaphores += s.NSemaphore[i]
		if s.IsHandler[i] != 0 {
			a.underHandlers += s.NGoroutines[i]
		}
	})
	for _, m := range g.moduleIDs() {
		a := g.modAccs[m]
		if a == nil || a.spawns == 0 {
			continue
		}
		sloc := g.Mod[m].Sloc
		perK := cf(0)
		if sloc > 0 {
			perK = cf(sqlRound(float64(a.spawns)*1000.0/float64(sloc), 2))
		}
		pct := cf(0)
		if a.spawns > 0 {
			pct = cf(sqlRound(100.0*float64(a.inLoop)/float64(a.spawns), 1))
		}
		r.rows = append(r.rows, row(nil, cs(g.Mod[m].Name), ci(int64(sloc)),
			ci(int64(a.spawns)), ci(int64(a.inLoop)), pct, perK,
			ci(int64(a.semaphores)), ci(int64(a.underHandlers))))
	}
	return sortRows(r, 5)
}

func mCleanupCoverage(g *Graph, pat string, lim int) result {
	r := result{cols: []string{"name", "err_checks", "n_returns", "io_sites",
		"fan_in", "cleanup_ratio", "at"}, lim: lim}
	s := &g.Sym

	for _, i := range g.fnTestedRows(pat, true) {
		if s.NDefer[i] != 0 || g.inGenFile(i) {
			continue
		}
		io := s.NIo[i] + s.NSql[i] + s.NNet[i]
		if io == 0 || s.NErrChecks[i]+s.NReturns[i] < 3 {
			continue
		}
		ratio := cf(0)
		if s.NErrChecks[i]+s.NReturns[i] > 0 {

			ratio = cf(sqlRound(1.0*float64(s.NDefer[i])/
				float64(s.NErrChecks[i]+s.NReturns[i]), 2))
		}
		r.krow([]int64{int64(io) * int64(s.FanIn[i])},
			cs(g.name(i)), ci(int64(s.NErrChecks[i])),
			ci(int64(s.NReturns[i])), ci(int64(io)), ci(int64(s.FanIn[i])), ratio,
			cs(g.at(i)))
	}

	return sortKeys(r, []bool{false})
}

func mOpenCloseRatio(g *Graph, pat string, lim int) result {
	r := result{cols: []string{"package_", "open_sites", "close_actions",
		"ratio"}, lim: lim}
	s := &g.Sym
	g.perModule(pat, true, func(a *modAcc, i int32) {
		a.opens += s.NIo[i] + s.NSql[i] + s.NNet[i]
		a.closeCalls += s.NCloseCall[i]
	})
	g.defersByModule(pat, false, func(mid int32, isClose, isUnlock, isDone int32) {
		a := g.modAcc(mid)
		a.defersClose += isClose
		a.defersUnlock += isUnlock
		a.defersDone += isDone
	})
	for _, m := range g.moduleIDs() {
		a := g.modAccs[m]
		if a == nil || a.opens <= 5 {
			continue
		}
		closes := a.closeCalls + a.defersClose
		ratio := cf(0)
		if a.opens > 0 {

			ratio = cf(sqlRound(1.0*float64(a.closeCalls)/float64(a.opens), 2))
		}
		r.rows = append(r.rows, row(nil, cs(g.Mod[m].Name), ci(int64(a.opens)),
			ci(int64(closes)), ratio))
	}
	return sortMixed(r, []bool{false, true}, 1, 3)
}

func (g *Graph) defersByModule(pat string, filtered bool,
	fold func(mid, isClose, isUnlock, isDone int32)) {
	s := &g.Sym
	for i := range g.Defers {
		d := &g.Defers[i]
		f := &g.File[s.FileId[d.SymbolID]]
		if filtered && (f.IsTest != 0 || f.IsGen != 0 ||
			!likePat(modName(g, f.ModuleID), pat)) {
			continue
		}
		fold(f.ModuleID, d.IsClose, d.IsUnlock, d.IsDone)
	}
}

func mLockBalance(g *Graph, pat string, lim int) result {
	r := result{cols: []string{"package_", "locks", "unlocks", "unlock_defers",
		"deficit"}, lim: lim}
	s := &g.Sym
	g.perModule(pat, true, func(a *modAcc, i int32) {
		a.locks += s.NLockCall[i]
		a.unlocks += s.NUnlockCall[i]
	})
	g.defersByModule(pat, true, func(mid int32, isClose, isUnlock, isDone int32) {
		g.modAcc(mid).defersUnlock += isUnlock
	})
	for _, m := range g.moduleIDs() {
		a := g.modAccs[m]
		if a == nil || a.locks <= a.unlocks {
			continue
		}
		r.rows = append(r.rows, row(nil, cs(g.Mod[m].Name), ci(int64(a.locks)),
			ci(int64(a.unlocks)), ci(int64(a.defersUnlock)),
			ci(int64(a.locks-a.unlocks))))
	}
	return sortRows(r, 4)
}

func mChannelBalance(g *Graph, pat string, lim int) result {
	r := result{cols: []string{"package_", "sends", "recvs", "closes", "unbuf",
		"pct_unbuf"}, lim: lim}
	s := &g.Sym
	g.perModule(pat, true, func(a *modAcc, i int32) {
		a.sends += s.NChanSend[i]
		a.recvs += s.NChanRecv[i]
		a.closes += s.NChanClose[i]
		a.unbuf += s.NChanUnbuffered[i]
		a.chanTypes += s.NChanType[i]
	})
	for _, m := range g.moduleIDs() {
		a := g.modAccs[m]
		if a == nil || a.sends == 0 {
			continue
		}

		pct := cnull
		if a.chanTypes > 0 {
			pct = cf(sqlRound(100.0*float64(a.unbuf)/float64(a.chanTypes), 1))
		}
		r.rows = append(r.rows, row(nil, cs(g.Mod[m].Name), ci(int64(a.sends)),
			ci(int64(a.recvs)), ci(int64(a.closes)), ci(int64(a.unbuf)), pct))
	}
	return sortRows(r, 1, 4)
}

func mWrapRatio(g *Graph, pat string, lim int) result {
	r := result{cols: []string{"package_", "importers", "wrapped", "unwrapped",
		"pct_wrapped"}, lim: lim}
	s := &g.Sym
	g.perModule(pat, true, func(a *modAcc, i int32) {
		a.wrapped += s.NErrWrapped[i]
		a.unwrapped += s.NErrorfNoWrap[i]
	})
	for _, m := range g.moduleIDs() {
		a := g.modAccs[m]
		if a == nil || a.wrapped+a.unwrapped == 0 {
			continue
		}

		pct := cf(sqlRound(100.0*float64(a.wrapped)/
			float64(a.wrapped+a.unwrapped), 1))
		r.rows = append(r.rows, row(nil, cs(g.Mod[m].Name), ci(int64(g.Mod[m].FanIn)),
			ci(int64(a.wrapped)), ci(int64(a.unwrapped)), pct))
	}
	return sortMixed(r, []bool{false, true}, 1, 4)
}

func mTestOnlyFanin(g *Graph, pat string, lim int) result {
	r := result{cols: []string{"name", "qual_name", "sloc", "fan_in",
		"prod_callers", "test_callers", "at"}, lim: lim}
	s := &g.Sym
	prod := map[int32]int32{}
	test := map[int32]int32{}
	for _, e := range g.edgeList {
		f := &g.File[s.FileId[e.Caller]]
		if f.IsTest != 0 {
			test[e.Callee]++
		} else {
			prod[e.Callee]++
		}
	}
	for _, i := range g.symRows(pat) {
		if s.IsGenerated[i] != 0 || s.IsPublic[i] == 0 || s.FanIn[i] == 0 {
			continue
		}
		if prod[i] != 0 {
			continue
		}
		r.rows = append(r.rows, row(nil, cs(g.name(i)), cs(g.Str.get(s.QualName[i])),
			ci(int64(s.Sloc[i])), ci(int64(s.FanIn[i])), ci(int64(prod[i])),
			ci(int64(test[i])), cs(g.at(i))))
	}
	return sortRows(r, 2)
}

func (g *Graph) modOK(sym, fid int32, pat string) bool {
	if fid >= 0 && fid < int32(len(g.File)) && g.File[fid].IsTest != 0 {
		return false
	}
	mid := g.Sym.ModuleId[sym]
	if mid < 0 {
		return likePat("", pat)
	}
	return likePat(g.Mod[mid].Name, pat)
}

func likePat(s, pat string) bool {
	if pat == "%" || pat == "" {
		return true
	}
	if !strings.ContainsAny(pat, "%_") {
		return len(s) == len(pat) && likeMatch(s, pat)
	}
	return likeMatch(s, pat)
}

func likeEq(a, b byte) bool {
	if a == b {
		return true
	}
	if 'A' <= a && a <= 'Z' {
		a += 'a' - 'A'
	} else if 'a' <= a && a <= 'z' {
		a -= 'a' - 'A'
	}
	return a == b
}

func likeMatch(s, p string) bool {
	si, pi, star, mark := 0, 0, -1, 0
	for si < len(s) {
		switch {
		case pi < len(p) && (p[pi] == '_' || likeEq(p[pi], s[si])):
			si++
			pi++
		case pi < len(p) && p[pi] == '%':
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
	for pi < len(p) && p[pi] == '%' {
		pi++
	}
	return pi == len(p)
}

func (g *Graph) matchedSyms(pat string) []int32 {
	out := make([]int32, 0, g.Sym.n/2)
	for i := 0; i < g.Sym.n; i++ {
		if g.modOK(int32(i), g.Sym.FileId[i], pat) {
			out = append(out, int32(i))
		}
	}
	return out
}

func isFnKind(g *Graph, i int32, bare bool) bool {
	switch g.Str.get(g.Sym.Kind[i]) {
	case "function", "method":
		return true
	case "constructor", "closure":
		return !bare
	}
	return false
}

func (g *Graph) fnSyms(pat string, bare bool) []int32 {
	out := make([]int32, 0, g.Sym.n/4)
	for i := 0; i < g.Sym.n; i++ {
		if !isFnKind(g, int32(i), bare) {
			continue
		}
		mid := g.Sym.ModuleId[i]
		if mid < 0 {
			if !likePat("", pat) {
				continue
			}
		} else if !likePat(g.Mod[mid].Name, pat) {
			continue
		}
		out = append(out, int32(i))
	}
	return out
}

func (g *Graph) symRows(pat string) []int32 { return g.fnTestedRows(pat, false) }

func (g *Graph) fnTestedRows(pat string, bare bool) []int32 {
	out := make([]int32, 0, g.Sym.n/4)
	for i := 0; i < g.Sym.n; i++ {
		if !isFnKind(g, int32(i), bare) {
			continue
		}
		if !g.modOK(int32(i), g.Sym.FileId[i], pat) {
			continue
		}
		out = append(out, int32(i))
	}
	return out
}

func (g *Graph) inGenFile(sym int32) bool {
	fid := g.Sym.FileId[sym]
	return fid >= 0 && fid < int32(len(g.File)) && g.File[fid].IsGen != 0
}

func (g *Graph) at(sym int32) string { return g.atRow(g.Sym.FileId[sym], g.Sym.LineStart[sym]) }

func (g *Graph) atRow(fid, line int32) string {
	if fid < 0 || fid >= int32(len(g.File)) {
		return ""
	}
	return g.File[fid].Path + ":" + itoa(line)
}

func itoa(v int32) string {
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
		b[i] = byte('0' + v%10)
		v /= 10
	}
	if neg {
		i--
		b[i] = '-'
	}
	return string(b[i:])
}

func (g *Graph) name(i int32) string { return g.Str.get(g.Sym.Name[i]) }
func (g *Graph) kind(i int32) string { return g.Str.get(g.Sym.Kind[i]) }
func (g *Graph) recv(i int32) string { return g.Str.get(g.Sym.ReceiverType[i]) }

func row(cols []string, vals ...cellVal) []cellVal { return append([]cellVal{}, vals...) }

func qGoroutineLeakFrontier(g *Graph, pat string, lim int) result {
	r := result{cols: []string{"in_fn", "spawns", "in_loop", "depth", "with_ctx",
		"with_wg", "with_errgroup", "with_recover", "chan_exit", "handler",
		"ctx_params", "at"}, lim: lim}
	type acc struct {
		spawns, inLoop, depth, ctx, wg, eg, rec, exit, minLine int32
	}
	by := map[int32]*acc{}
	var order []int32
	for i := range g.Goro {
		o := &g.Goro[i]
		if !g.modOK(o.SymbolID, o.FileID, pat) {
			continue
		}
		a := by[o.SymbolID]
		if a == nil {
			a = &acc{}
			by[o.SymbolID] = a
			order = append(order, o.SymbolID)
		}
		a.spawns++
		a.inLoop += o.InLoop
		if o.LoopDepth > a.depth {
			a.depth = o.LoopDepth
		}
		a.ctx += o.HasCtx
		a.wg += o.HasWG
		a.eg += o.HasEG
		a.rec += o.HasRecover
		a.exit += o.ChanExit
		if a.minLine == 0 || o.Line < a.minLine {
			a.minLine = o.Line
		}
	}
	for _, sid := range order {
		a := by[sid]
		if a.ctx != 0 || a.wg != 0 || a.eg != 0 {
			continue
		}
		s := &g.Sym
		r.rows = append(r.rows, row(nil, cs(g.name(sid)), ci(int64(a.spawns)),
			ci(int64(a.inLoop)), ci(int64(a.depth)), ci(int64(a.ctx)),
			ci(int64(a.wg)), ci(int64(a.eg)), ci(int64(a.rec)), ci(int64(a.exit)),
			ci(int64(s.IsHandler[sid])), ci(int64(s.NCtxParams[sid])),
			cs(g.atRow(g.firstGoroFile(sid), a.minLine))))
	}
	return sortRows(r, 2, 1)
}

func (g *Graph) firstGoroFile(sid int32) int32 {
	lo, hi := g.goroCSR.row(sid)
	if lo == hi {
		return g.Sym.FileId[sid]
	}
	return g.Goro[lo].FileID
}

func qGoroutineUnderHandler(g *Graph, pat string, lim int) result {
	r := result{cols: []string{"handler", "spawns_in", "hops", "goroutines",
		"with_ctx", "in_loop", "at"}, lim: lim}
	type acc struct{ goro, ctx, inLoop, minLine int32 }
	by := map[[2]int32]*acc{}
	var order [][2]int32
	hops := map[[2]int32]int32{}
	var cand []int32
	var candLo, candHi []int32
	for sym := 0; sym < g.Sym.n; sym++ {
		lo, hi := g.goroCSR.row(int32(sym))
		if lo == hi {
			continue
		}
		if !g.modOK(int32(sym), g.Sym.FileId[sym], pat) {
			continue
		}
		cand = append(cand, int32(sym))
		candLo = append(candLo, lo)
		candHi = append(candHi, hi)
	}
	for h := 0; h < g.Sym.n; h++ {
		if g.Sym.IsHandler[h] == 0 {
			continue
		}
		dist := g.Calls.reach(int32(h), 4)
		for ci, sym := range cand {
			d := dist.at(sym)
			if d < 0 {
				continue
			}
			k := [2]int32{int32(h), sym}
			hops[k] = d
			for p := candLo[ci]; p < candHi[ci]; p++ {
				o := &g.Goro[p]
				a := by[k]
				if a == nil {
					a = &acc{}
					by[k] = a
					order = append(order, k)
				}
				a.goro++
				a.ctx += o.HasCtx
				a.inLoop += o.InLoop
				if a.minLine == 0 || o.Line < a.minLine {
					a.minLine = o.Line
				}
			}
		}
	}

	for _, k := range order {
		a := by[k]
		if a.ctx >= a.goro {
			continue
		}
		r.rows = append(r.rows, row(nil, cs(g.name(k[0])), cs(g.name(k[1])),
			ci(int64(hops[k])), ci(int64(a.goro)), ci(int64(a.ctx)),
			ci(int64(a.inLoop)), cs(g.atRow(g.firstGoroFile(k[1]), a.minLine))))
	}
	return sortRows(r, 2, 3)
}

func qCtxPropagationBreak(g *Graph, pat string, lim int) result {
	r := result{cols: []string{"caller", "callee", "caller_ctx", "callee_ctx",
		"makes_background", "io", "net_", "sql_", "uses_done", "fan_in", "at"},
		lim: lim}
	s := &g.Sym
	for _, e := range g.edgeList {
		cal, cle := e.Caller, e.Callee
		if s.NCtxParams[cal] == 0 {
			continue
		}
		bg := s.NCtxBackground[cle]
		other := s.NCtxParams[cle] == 0 && s.NIo[cle]+s.NNet[cle]+s.NSql[cle] > 0
		if bg == 0 && !other {
			continue
		}
		if !g.modOK(cle, s.FileId[cle], pat) {
			continue
		}
		r.krow([]int64{int64(s.NNet[cle])*3 + int64(s.NSql[cle])*3 +
			int64(s.NIo[cle]), int64(s.FanIn[cle])},
			cs(g.name(cal)), cs(g.name(cle)),
			ci(int64(s.NCtxParams[cal])), ci(int64(s.NCtxParams[cle])),
			ci(int64(bg)), ci(int64(s.NIo[cle])), ci(int64(s.NNet[cle])),
			ci(int64(s.NSql[cle])), ci(int64(s.NCtxDone[cle])),
			ci(int64(s.FanIn[cle])), cs(g.at(cle)))
	}
	return sortKeys(r, []bool{false, false})
}

func qDeferLifetime(g *Graph, pat string, lim int) result {
	r := result{cols: []string{"name", "defers", "in_loop", "depth",
		"closes", "unlocks", "loops", "fan_in", "targets", "at"}, lim: lim}
	s := &g.Sym
	type acc struct {
		n, closes, unlocks, maxDepth, minLine int32
		targets                               []string
		seen                                  map[string]bool
	}
	by := make(map[int32]*acc, 64)
	var order []int32
	for i := range g.Defers {
		d := &g.Defers[i]
		if d.InLoop == 0 || !g.modOK(d.SymbolID, s.FileId[d.SymbolID], pat) {
			continue
		}
		a := by[d.SymbolID]
		if a == nil {
			a = &acc{seen: map[string]bool{}}
			by[d.SymbolID] = a
			order = append(order, d.SymbolID)
		}
		a.n++
		a.closes += d.IsClose
		a.unlocks += d.IsUnlock
		if d.LoopDepth > a.maxDepth {
			a.maxDepth = d.LoopDepth
		}
		if a.minLine == 0 || d.Line < a.minLine {
			a.minLine = d.Line
		}
		t := g.Str.get(d.Target)
		t = trunc(t, 28)
		if !a.seen[t] {
			a.seen[t] = true
			a.targets = append(a.targets, t)
		}
	}
	for _, sid := range order {
		a := by[sid]
		r.rows = append(r.rows, row(nil, cs(g.name(sid)), ci(int64(a.n)),
			ci(int64(a.n)), ci(int64(a.maxDepth)), ci(int64(a.closes)),
			ci(int64(a.unlocks)), ci(int64(s.NLoops[sid])),
			ci(int64(s.FanIn[sid])), cs(joinDistinct(a.targets)),
			cs(g.atRow(s.FileId[sid], a.minLine))))
	}
	return sortRows(r, 2, 3)
}

func qDeferInLoop(g *Graph, pat string, lim int) result {
	r := result{cols: []string{"name", "receiver", "defer_in_loop",
		"defer_closes", "depth", "chan_closes", "io_ops", "fan_in", "at"},
		lim: lim}
	s := &g.Sym
	for _, i := range g.matchedSyms(pat) {
		n := s.NDeferInLoop[i]
		if n == 0 {
			continue
		}
		r.krow([]int64{int64(n) * (1 + int64(s.FanIn[i])), int64(s.MaxLoopDepth[i])},
			cs(g.name(i)), cs(g.recv(i)),
			ci(int64(n)), ci(int64(s.NDeferClose[i])),
			ci(int64(s.MaxLoopDepth[i])), ci(int64(s.NChanClose[i])),
			ci(int64(s.NIo[i])), ci(int64(s.FanIn[i])), cs(g.at(i)))
	}
	return sortKeys(r, []bool{false, false})
}

func joinInOrder(v []string) string {
	var out strings.Builder
	for i, s := range v {
		if i > 0 {
			out.WriteString(",")
		}
		out.WriteString(s)
	}
	return out.String()
}

func joinDistinct(v []string) string {
	sort.Strings(v)
	var out strings.Builder
	for i, s := range v {
		if i > 0 {
			out.WriteString(",")
		}
		out.WriteString(s)
	}
	return out.String()
}

func qResourceCloseCrossLayer(g *Graph, pat string, lim int) result {
	r := result{cols: []string{"name", "net_ops", "sql_ops", "io_ops",
		"defers", "defer_closes", "return_type", "callers_that_close",
		"ignored_errs", "fan_in", "at"}, lim: lim}
	s := &g.Sym

	closers := make(map[int32]int32, len(g.edgeList)/8)
	for _, e := range g.edgeList {
		if s.NDeferClose[e.Caller] > 0 {
			closers[e.Callee]++
		}
	}
	for _, i := range g.matchedSyms(pat) {
		net, sql, io := s.NNet[i], s.NSql[i], s.NIo[i]
		if net+sql+io == 0 || s.NDeferClose[i] != 0 {
			continue
		}
		n := closers[i]
		r.krow([]int64{int64(n), int64(net)*3 + int64(sql)*3 + int64(io)},
			cs(g.name(i)), ci(int64(net)),
			ci(int64(sql)), ci(int64(io)), ci(int64(s.NDefer[i])),
			ci(int64(s.NDeferClose[i])), cs(g.Str.get(s.ReturnType[i])),
			ci(int64(n)), ci(int64(s.NErrIgnored[i])), ci(int64(s.FanIn[i])),
			cs(g.at(i)))
	}

	return sortKeys(r, []bool{true, false})
}

func qUncheckedErrors(g *Graph, pat string, lim int) result {
	r := result{cols: []string{"name", "ignored", "shadowed", "checked",
		"wrapped", "err_returns", "naked", "named", "fan_in", "blast", "at"},
		lim: lim}
	s := &g.Sym
	for _, i := range g.matchedSyms(pat) {
		ig, sh := s.NErrIgnored[i], s.NErrShadowed[i]
		if ig+sh == 0 {
			continue
		}
		blast := ig * max32(s.FanIn[i], 1)
		r.rows = append(r.rows, row(nil, cs(g.name(i)), ci(int64(ig)),
			ci(int64(sh)), ci(int64(s.NErrChecks[i])), ci(int64(s.NErrWrapped[i])),
			ci(int64(s.NErrReturns[i])), ci(int64(s.NNakedReturns[i])),
			ci(int64(s.NNamedResults[i])), ci(int64(s.FanIn[i])),
			ci(int64(blast)), cs(g.at(i))))
	}
	return sortRows(r, 9, 2)
}

func qChannelTopology(g *Graph, pat string, lim int) result {
	r := result{cols: []string{"declared_in", "elem_type", "cap_", "sends",
		"recvs", "closes", "selects", "ctx_done_case", "locks_in_loop",
		"spawns", "at"}, lim: lim}
	s := &g.Sym
	for i := range g.Chans {
		c := &g.Chans[i]
		if c.Capacity != 0 || !g.modOK(c.SymbolID, c.FileID, pat) {
			continue
		}
		sid := c.SymbolID
		r.rows = append(r.rows, row(nil, cs(g.name(sid)), cs(g.Str.get(c.ElemType)),
			ci(int64(c.Capacity)), ci(int64(s.NChanSend[sid])),
			ci(int64(s.NChanRecv[sid])), ci(int64(s.NChanClose[sid])),
			ci(int64(s.NSelect[sid])), ci(int64(s.NSelectCtxDone[sid])),
			ci(int64(s.LockInLoop[sid])), ci(int64(s.NGoroutines[sid])),
			cs(g.atRow(c.FileID, c.Line))))
	}
	return sortRows(r, 3, 9)
}

func qLockCopiedByValue(g *Graph, pat string, lim int) result {
	r := result{cols: []string{"type_", "fields", "bytes_", "used_in", "pos",
		"param", "type", "spawns", "fan_in", "at"}, lim: lim}
	s := &g.Sym

	mx := map[string][]*Struct{}
	for i := range g.Structs {
		st := &g.Structs[i]
		if st.HasMutex != 0 && st.SymbolID >= 0 && st.SymbolID < int32(g.Sym.n) {
			n := g.name(st.SymbolID)
			mx[n] = append(mx[n], st)
		}
	}

	seen := map[[3]int32]bool{}
	for i := range g.Params {
		p := &g.Params[i]

		sid := g.paramsSym[i]
		t := g.Str.get(p.Typ)
		if strings.Contains(t, "*") {
			continue
		}
		var cands []string
		if _, ok := mx[t]; ok {
			cands = append(cands, t)
		}

		trimmed := strings.TrimRight(t, "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_")
		if strings.HasSuffix(trimmed, ".") {
			q := t[len(trimmed):]
			if _, ok := mx[q]; ok {
				cands = append(cands, q)
			}
		}
		if strings.HasPrefix(t, "[]") {
			if _, ok := mx[t[2:]]; ok {
				cands = append(cands, t[2:])
			}
		}
		for _, c := range cands {
			for _, st := range mx[c] {
				k := [3]int32{st.SymbolID, sid, p.Pos}
				if seen[k] {
					continue
				}
				seen[k] = true
				if !g.modOK(sid, s.FileId[sid], pat) {
					continue
				}
				r.rows = append(r.rows, row(nil, cs(c), ci(int64(st.NFields)),
					ci(int64(st.EstSize)), cs(g.name(sid)), ci(int64(p.Pos)),
					cs(g.Str.get(p.Name)), cs(t),
					ci(int64(s.NGoroutines[sid])), ci(int64(s.FanIn[sid])),
					cs(g.at(sid))))
			}
		}
	}

	return sortRows(r, 7, 8)
}

func qLockOverCrosspkgCall(g *Graph, pat string, lim int) result {
	r := result{cols: []string{"holder", "locks", "locks_in_loop",
		"cross_pkg_callees", "callee_io", "callee_sends", "callee_locks",
		"fan_in", "calls_out", "at"}, lim: lim}
	s := &g.Sym
	type acc struct {
		n, io, sends, locks int32
		names               []string
		seen                map[int32]bool
	}
	by := map[int32]*acc{}
	var order []int32
	for _, e := range g.edgeList {
		if e.SameMod != 0 {
			continue
		}
		if s.NLock[e.Caller] == 0 {
			continue
		}
		if !g.modOK(e.Caller, s.FileId[e.Caller], pat) {
			continue
		}
		a := by[e.Caller]
		if a == nil {
			a = &acc{seen: map[int32]bool{}}
			by[e.Caller] = a
			order = append(order, e.Caller)
		}
		c := e.Callee
		if !a.seen[c] {
			a.seen[c] = true
			a.n++

			a.names = append(a.names, g.name(c))
		}
		a.io += s.NIo[c] + s.NNet[c] + s.NSql[c]
		a.sends += s.NChanSend[c]
		if s.NLock[c] > a.locks {
			a.locks = s.NLock[c]
		}
	}
	for _, sid := range order {
		a := by[sid]
		if a.io == 0 && a.locks == 0 && a.sends == 0 {
			continue
		}
		r.rows = append(r.rows, row(nil, cs(g.name(sid)), ci(int64(s.NLock[sid])),
			ci(int64(s.LockInLoop[sid])), ci(int64(a.n)), ci(int64(a.io)),
			ci(int64(a.sends)), ci(int64(a.locks)), ci(int64(s.FanIn[sid])),
			cs(joinInOrder(a.names)), cs(g.at(sid))))
	}
	return sortRows(r, 4, 2)
}

func qNPlusOne(g *Graph, pat string, lim int) result {
	r := result{cols: []string{"caller", "loop_depth", "query_fn", "sql_ops",
		"own_loop", "edges", "caller_fan_in", "handler", "at"}, lim: lim}
	s := &g.Sym
	for _, e := range g.edgeList {
		cal, cle := e.Caller, e.Callee
		if s.NSql[cle] == 0 || s.MaxLoopDepth[cal] == 0 || s.CallInLoop[cal] == 0 {
			continue
		}
		if !g.modOK(cal, s.FileId[cal], pat) {
			continue
		}
		r.rows = append(r.rows, row(nil, cs(g.name(cal)),
			ci(int64(s.MaxLoopDepth[cal])), cs(g.name(cle)), ci(int64(s.NSql[cle])),
			ci(int64(s.QueryInLoop[cle])), ci(int64(e.NCalls)),
			ci(int64(s.FanIn[cal])), ci(int64(s.IsHandler[cal])), cs(g.at(cal))))
	}
	return sortRows(r, 2, 3)
}

func (g *Graph) reachFrom(seed func(i int32) bool, maxHops int32) []int32 {
	dist := make([]int32, g.Sym.n)
	for i := range dist {
		dist[i] = -1
	}
	var frontier []int32
	for i := 0; i < g.Sym.n; i++ {
		if seed(int32(i)) {
			dist[i] = 0
			frontier = append(frontier, int32(i))
		}
	}
	for d := int32(0); d < maxHops && len(frontier) > 0; d++ {
		var next []int32
		for _, sym := range frontier {
			lo, hi := g.Calls.Out.row(sym)
			for p := lo; p < hi; p++ {
				c := g.Calls.Out.val[p]
				if c.IsSelf != 0 {
					continue
				}
				if dist[c.Callee] < 0 {
					dist[c.Callee] = d + 1
					next = append(next, c.Callee)
				}
			}
		}
		frontier = next
	}
	return dist
}

func qUnsafeCgoFrontier(g *Graph, pat string, lim int) result {
	r := result{cols: []string{"name", "hops_from_handler", "unsafe_", "cgo",
		"reflect_", "directives", "panics", "fan_in", "at"}, lim: lim}
	s := &g.Sym
	dist := g.reachFrom(func(i int32) bool {
		return s.IsHandler[i] == 1 || s.IsEntrypoint[i] == 1
	}, 5)
	for i := 0; i < g.Sym.n; i++ {
		if dist[i] < 0 || s.NUnsafeOps[i]+s.NCgoCalls[i] == 0 {
			continue
		}
		if !g.modOK(int32(i), s.FileId[i], pat) {
			continue
		}
		r.rows = append(r.rows, row(nil, cs(g.name(int32(i))), ci(int64(dist[i])),
			ci(int64(s.NUnsafeOps[i])), ci(int64(s.NCgoCalls[i])),
			ci(int64(s.NReflectOps[i])), ci(int64(0)), ci(int64(s.NPanics[i])),
			ci(int64(s.FanIn[i])), cs(g.at(int32(i)))))
	}
	return sortRows(r, 1, 3)
}

func qPackageStateConcurrent(g *Graph, pat string, lim int) result {
	r := result{cols: []string{"package_", "spawns", "locks", "atomics",
		"tickers", "init_funcs", "fns", "sends"}, lim: lim}
	type acc struct{ spawns, locks, atomics, tickers, inits, fns, sends int32 }
	by := map[int32]*acc{}

	for _, i := range g.matchedSyms(pat) {
		mid := g.Sym.ModuleId[i]
		if mid < 0 {
			continue
		}
		a := by[mid]
		if a == nil {
			a = &acc{}
			by[mid] = a
		}
		s := &g.Sym
		a.spawns += s.NGoroutines[i]
		a.locks += s.NLock[i]
		a.atomics += s.NAtomic[i]
		a.tickers += s.NTimeTick[i]
		a.inits += s.IsInit[i]
		a.fns++
		a.sends += s.NChanSend[i]
	}
	var mids []int32
	for m := range by {
		mids = append(mids, m)
	}
	slices.Sort(mids)
	for _, m := range mids {
		a := by[m]
		if a.spawns == 0 || a.locks != 0 || a.atomics != 0 {
			continue
		}
		r.rows = append(r.rows, row(nil, cs(g.Mod[m].Name), ci(int64(a.spawns)),
			ci(int64(a.locks)), ci(int64(a.atomics)), ci(int64(a.tickers)),
			ci(int64(a.inits)), ci(int64(a.fns)), ci(int64(a.sends))))
	}
	return sortRows(r, 1)
}

func qDeadCode(g *Graph, pat string, lim int) result {
	r := result{cols: []string{"name", "kind", "sloc", "cyclo", "recv",
		"ext_calls", "at"}, lim: lim}
	s := &g.Sym
	for i := 0; i < g.Sym.n; i++ {
		k := g.kind(int32(i))
		if k != "function" && k != "method" {
			continue
		}
		if s.FanIn[i] != 0 || s.IsPublic[i] != 0 || s.IsTest[i] != 0 ||
			s.IsEntrypoint[i] != 0 || s.IsHandler[i] != 0 {
			continue
		}

		if g.File[s.FileId[i]].IsTest != 0 || g.File[s.FileId[i]].IsGen != 0 {
			continue
		}
		if s.IsGenerated[i] != 0 || g.name(int32(i)) == "(anonymous)" {
			continue
		}
		if !g.modOK(int32(i), s.FileId[i], pat) {
			continue
		}
		r.rows = append(r.rows, row(nil, cs(g.name(int32(i))), cs(k),
			ci(int64(s.Sloc[i])), ci(int64(s.Cyclomatic[i])), cs(g.recv(int32(i))),
			ci(int64(s.NExternalCalls[i])), cs(g.at(int32(i)))))
	}

	return sortRows(r, 2)
}

func qContextNotPropagated(g *Graph, pat string, lim int) result {
	r := result{cols: []string{"name", "receiver", "ctx_params", "ctx_passed",
		"ctx_background", "ctx_done", "with_cancel", "cancels", "goroutines",
		"fan_out", "at"}, lim: lim}
	s := &g.Sym
	for _, i := range g.symRows(pat) {
		if s.NCtxParams[i] == 0 || s.NCtxPassed[i] != 0 || s.FanOut[i] == 0 {
			continue
		}
		r.rows = append(r.rows, row(nil, cs(g.name(i)), cs(g.recv(i)),
			ci(int64(s.NCtxParams[i])), ci(int64(s.NCtxPassed[i])),
			ci(int64(s.NCtxBackground[i])), ci(int64(s.NCtxDone[i])),
			ci(int64(s.NCtxWithcancel[i])), ci(int64(s.NCancelCalled[i])),
			ci(int64(s.NGoroutines[i])), ci(int64(s.FanOut[i])), cs(g.at(i))))
	}
	return sortRows(r, 9, 8)
}

func qErrorHandlingDrift(g *Graph, pat string, lim int) result {
	r := result{cols: []string{"name", "receiver", "ignored", "shadowed",
		"checked", "wrapped", "returns_err", "naked_returns", "panics",
		"log_fatal", "fan_in", "at"}, lim: lim}
	s := &g.Sym
	for _, i := range g.matchedSyms(pat) {
		if s.NErrIgnored[i] == 0 && s.NErrShadowed[i] == 0 {
			continue
		}
		r.krow([]int64{int64(s.NErrShadowed[i]),
			int64(s.NErrIgnored[i]) * (1 + int64(s.FanIn[i]))},
			cs(g.name(i)), cs(g.recv(i)),
			ci(int64(s.NErrIgnored[i])), ci(int64(s.NErrShadowed[i])),
			ci(int64(s.NErrChecks[i])), ci(int64(s.NErrWrapped[i])),
			ci(int64(s.NErrReturns[i])), ci(int64(s.NNakedReturns[i])),
			ci(int64(s.NPanics[i])), ci(int64(s.NLogFatal[i])),
			ci(int64(s.FanIn[i])), cs(g.at(i)))
	}
	return sortKeys(r, []bool{false, false})
}

func qSliceGrowthAndCopies(g *Graph, pat string, lim int) result {
	r := result{cols: []string{"name", "receiver", "append_in_loop",
		"make_no_cap", "range_copies", "sprintf_in_loop", "conv_in_loop",
		"depth", "fan_in", "at"}, lim: lim}
	s := &g.Sym
	for _, i := range g.matchedSyms(pat) {
		if s.NAppendInLoop[i]+s.NSprintfInLoop[i]+s.NRangeValueCopy[i] == 0 {
			continue
		}
		score := (s.NAppendInLoop[i]*2 + s.NSprintfInLoop[i]*3 + s.NRangeValueCopy[i]) *
			(1 + s.FanIn[i])
		r.krow([]int64{int64(score)},
			cs(g.name(i)), cs(g.recv(i)),
			ci(int64(s.NAppendInLoop[i])), ci(int64(s.NMakeNoCap[i])),
			ci(int64(s.NRangeValueCopy[i])), ci(int64(s.NSprintfInLoop[i])),
			ci(int64(s.NConvInLoop[i])), ci(int64(s.MaxLoopDepth[i])),
			ci(int64(s.FanIn[i])), cs(g.at(i)))
	}
	return sortKeys(r, []bool{false})
}

func qUncheckedTypeAssertions(g *Graph, pat string, lim int) result {
	r := result{cols: []string{"name", "receiver", "unchecked_asserts",
		"asserts_total", "type_switches", "any_params", "iface_params",
		"recovers", "handler", "fan_in", "at"}, lim: lim}
	s := &g.Sym
	for _, i := range g.matchedSyms(pat) {
		if s.NTypeAssertUnchecked[i] == 0 {
			continue
		}
		r.rows = append(r.rows, row(nil, cs(g.name(i)), cs(g.recv(i)),
			ci(int64(s.NTypeAssertUnchecked[i])), ci(int64(s.NTypeAssert[i])),
			ci(int64(s.NTypeSwitch[i])), ci(int64(s.NAnyParams[i])),
			ci(int64(s.NIfaceParams[i])), ci(int64(s.NRecover[i])),
			ci(int64(s.IsHandler[i])), ci(int64(s.FanIn[i])), cs(g.at(i))))
	}
	return sortRows(r, 8, 2)
}

func qContextSeveredByCaller(g *Graph, pat string, lim int) result {
	r := result{cols: []string{"makes_background", "caller", "caller_had_ctx",
		"background_calls", "callee_ctx_params", "goroutines", "fan_in",
		"callers_with_ctx", "at"}, lim: lim}
	s := &g.Sym
	type acc struct{ n int32 }
	by := map[[2]int32]*acc{}
	var order [][2]int32
	for _, e := range g.edgeList {
		if s.NCtxBackgroundCall[e.Callee] == 0 || s.NCtxParams[e.Caller] == 0 ||
			s.NCtxParams[e.Callee] != 0 || e.IsSelf != 0 {
			continue
		}
		if !g.modOK(e.Callee, s.FileId[e.Callee], pat) {
			continue
		}
		k := [2]int32{e.Callee, e.Caller}
		if by[k] == nil {
			order = append(order, k)
		}
		by[k] = &acc{n: 1}
	}
	for _, k := range order {
		ce, cr := k[0], k[1]
		r.rows = append(r.rows, row(nil, cs(g.name(ce)), cs(g.name(cr)),
			ci(int64(s.NCtxParams[cr])), ci(int64(s.NCtxBackgroundCall[ce])),
			ci(int64(s.NCtxParams[ce])), ci(int64(s.NGoroutines[ce])),
			ci(int64(s.FanIn[ce])), ci(int64(1)), cs(g.at(ce))))
	}
	return sortRows(r, 7, 6, 5)
}

func qLockImbalanceReachable(g *Graph, pat string, lim int) result {
	r := result{cols: []string{"name", "receiver", "reached_from", "hops",
		"locks", "unlocks", "imbalance", "defers", "goroutines", "fan_in",
		"at"}, lim: lim}
	s := &g.Sym
	var cand []int32
	for sym := 0; sym < g.Sym.n; sym++ {
		if s.NLockCall[sym] <= s.NUnlockCall[sym] {
			continue
		}
		if !g.modOK(int32(sym), s.FileId[sym], pat) {
			continue
		}
		cand = append(cand, int32(sym))
	}
	for e := 0; e < g.Sym.n; e++ {
		if s.IsHandler[e] == 0 && s.NGoroutines[e] == 0 {
			continue
		}
		dist := g.Calls.reach(int32(e), 4)
		type acc struct {
			hops, defers, goroutines, minLine int32
		}
		by := map[int32]*acc{}
		var order []int32
		for _, sym := range cand {
			d := dist.at(sym)
			if d < 0 {
				continue
			}
			a := by[sym]
			if a == nil {
				a = &acc{}
				by[int32(sym)] = a
				order = append(order, int32(sym))
			}
			if a.hops == 0 || d < a.hops {
				a.hops = d
			}
			a.defers += s.NDeferClose[sym]
			a.goroutines += s.NGoroutines[sym]
		}
		for _, sym := range order {
			a := by[sym]
			r.rows = append(r.rows, row(nil, cs(g.name(sym)), cs(g.recv(sym)),
				cs(g.name(int32(e))), ci(int64(a.hops)),
				ci(int64(s.NLockCall[sym])), ci(int64(s.NUnlockCall[sym])),
				ci(int64(s.NLockCall[sym]-s.NUnlockCall[sym])),
				ci(int64(a.defers)), ci(int64(a.goroutines)),
				ci(int64(s.FanIn[sym])), cs(g.at(sym))))
		}
	}
	return sortRows(r, 3, 4)
}

func qNilContextDeep(g *Graph, pat string, lim int) result {
	r := result{cols: []string{"name", "bg_contexts", "with_cancel",
		"cancel_called", "hops_from_handler", "fan_in", "cyclo", "at"}, lim: lim}
	s := &g.Sym
	dist := g.reachFrom(func(i int32) bool { return s.IsHandler[i] == 1 }, 4)
	for i := 0; i < g.Sym.n; i++ {
		if dist[i] < 0 || s.NCtxBackground[i] == 0 {
			continue
		}
		if !g.modOK(int32(i), s.FileId[i], pat) {
			continue
		}
		r.rows = append(r.rows, row(nil, cs(g.name(int32(i))),
			ci(int64(s.NCtxBackground[i])), ci(int64(s.NCtxWithcancel[i])),
			ci(int64(s.NCancelCalled[i])), ci(int64(dist[i])),
			ci(int64(s.FanIn[i])), ci(int64(s.Cyclomatic[i])), cs(g.at(int32(i)))))
	}
	return sortRows(r, 4, 1)
}

func qErrorNotWrapped(g *Graph, pat string, lim int) result {
	r := result{cols: []string{"name", "unwrapped_errors", "wrapped_errors",
		"err_returns", "fan_in", "cyclo", "at"}, lim: lim}
	s := &g.Sym
	for _, i := range g.matchedSyms(pat) {
		if s.NErrorfNoWrap[i] == 0 {
			continue
		}
		r.rows = append(r.rows, row(nil, cs(g.name(i)),
			ci(int64(s.NErrorfNoWrap[i])), ci(int64(s.NErrWrapped[i])),
			ci(int64(s.NErrReturns[i])), ci(int64(s.FanIn[i])),
			ci(int64(s.Cyclomatic[i])), cs(g.at(i))))
	}
	return sortRows(r, 1, 4)
}

func qWeakRandom(g *Graph, pat string, lim int) result {
	r := result{cols: []string{"name", "weak_random_calls", "decode_calls",
		"exec_calls", "fan_in", "handler", "at"}, lim: lim}
	s := &g.Sym
	for _, i := range g.symRows(pat) {
		if s.NWeakRandom[i] == 0 {
			continue
		}
		r.rows = append(r.rows, row(nil, cs(g.name(i)), ci(int64(s.NWeakRandom[i])),
			ci(int64(s.NDecodeCall[i])), ci(int64(s.NExecCall[i])),
			ci(int64(s.FanIn[i])), ci(int64(s.IsHandler[i])), cs(g.at(i))))
	}
	return sortRows(r, 4, 1)
}

func qWeakCrypto(g *Graph, pat string, lim int) result {
	r := result{cols: []string{"name", "weak_crypto_calls", "decode_calls",
		"fan_in", "handler", "at"}, lim: lim}
	s := &g.Sym
	for _, i := range g.symRows(pat) {
		if s.NWeakCrypto[i] == 0 {
			continue
		}
		r.rows = append(r.rows, row(nil, cs(g.name(i)), ci(int64(s.NWeakCrypto[i])),
			ci(int64(s.NDecodeCall[i])), ci(int64(s.FanIn[i])),
			ci(int64(s.IsHandler[i])), cs(g.at(i))))
	}
	return sortRows(r, 3, 1)
}

func putSep(b *[]byte)        { *b = append(*b, ' ') }
func putNull(b *[]byte)       { *b = append(*b, `\N`...) }
func putI(b *[]byte, v int64) { *b = append(*b, 'i', ':'); *b = strconv.AppendInt(*b, v, 10) }

func fk(b *[]byte, v int32) {
	if v < 0 {
		putNull(b)
		return
	}
	putI(b, int64(v)+1)
}

func putF(b *[]byte, v float64) { *b = append(*b, 'f', ':'); *b = append(*b, pyFloat(v)...) }

func putText(b *[]byte, s string) {
	*b = append(*b, 's', ':')
	last := 0
	for i := 0; i < len(s); i++ {
		c := s[i]
		if c >= 0x20 && c != 0x7f && c != '\\' {
			continue
		}
		*b = append(*b, s[last:i]...)
		switch {
		case c == '\\':
			*b = append(*b, '\\', '\\')
		case c == '\n':
			*b = append(*b, '\\', 'n')
		case c == '\t':
			*b = append(*b, '\\', 't')
		case c == '\r':
			*b = append(*b, '\\', 'r')
		default:
			*b = append(*b, '\\', 'x')
			*b = append(*b, "0123456789ABCDEF"[c>>4], "0123456789ABCDEF"[c&0xf])
		}
		last = i + 1
	}
	*b = append(*b, s[last:]...)
}

func pyFloat(v float64) string {
	if math.IsInf(v, 1) {
		return "inf"
	}
	if math.IsInf(v, -1) {
		return "-inf"
	}
	if math.IsNaN(v) {
		return "nan"
	}
	s := strconv.FormatFloat(v, 'g', -1, 64)

	if !strings.ContainsAny(s, ".eEn") {
		s += ".0"
	}

	if i := strings.IndexAny(s, "eE"); i >= 0 {
		mant, exp := s[:i], s[i+1:]
		sign := ""
		if exp[0] == '+' || exp[0] == '-' {
			sign, exp = string(exp[0]), exp[1:]
		}
		for len(exp) > 1 && exp[0] == '0' {
			exp = exp[1:]
		}
		if len(exp) == 1 {
			exp = "0" + exp
		}
		return mant + "e" + sign + exp
	}
	return s
}

var dumpTables = []string{
	"attributes", "build_tags", "callsites", "channels", "defers", "edges", "enum_members",
	"error_chain_depth", "fields", "files", "goroutines", "hazards",
	"implements", "imports", "interfaces", "literals", "locals", "markers",
	"meta", "module_depth", "modules", "params", "secret_candidates", "structs",
	"sym_fts", "symbols", "unresolved_calls", "user_input_sites", "wg_sites",
}

var runtimeMeta = map[string]bool{
	"parse_mode": true, "parser": true, "sqlite": true,

	"parse_diagnostics": true,
}

type dumper struct {
	g         *Graph
	out       *bufio.Writer
	scr       []byte
	rows      []string
	chunks    [][]byte
	ci, co    int
	symShards [][]string
}

const dumpChunk = 1 << 20
const dumpShardMin = 1 << 14

func (d *dumper) addRow() {
	s := d.scr
	n := len(s)
	if d.ci >= len(d.chunks) || d.co+n > len(d.chunks[d.ci]) {
		if n > dumpChunk {
			d.chunks = append(d.chunks, append([]byte(nil), s...))
			d.ci, d.co = len(d.chunks)-1, n
		} else {
			d.chunks = append(d.chunks, make([]byte, dumpChunk))
			d.ci, d.co = len(d.chunks)-1, 0
		}
	}
	c := d.chunks[d.ci]
	copy(c[d.co:], s)
	if n == 0 {
		d.rows = append(d.rows, "")
		return
	}
	d.rows = append(d.rows, unsafe.String(unsafe.SliceData(c[d.co:d.co+n]), n))
	d.co += n
}

func shardSymbolRows(g *Graph, k int) [][]string {
	if k < 2 || g.Sym.n < dumpShardMin {
		return nil
	}
	if m := runtime.GOMAXPROCS(0); m < k {
		k = m
	}
	if k < 2 {
		return nil
	}
	parts := make([][]string, k)
	var wg sync.WaitGroup
	wg.Add(k)
	n := int64(g.Sym.n)
	for j := 0; j < k; j++ {
		go func(j int) {
			defer wg.Done()
			lo, hi := n*int64(j)/int64(k), n*int64(j+1)/int64(k)
			sd := &dumper{g: g, scr: make([]byte, 0, 4096)}
			for i := lo; i < hi; i++ {
				sd.scr = sd.scr[:0]
				g.Sym.symDump(int(i), g, &sd.scr)
				sd.addRow()
			}
			parts[j] = sd.rows
		}(j)
	}
	wg.Wait()
	return parts
}

func (g *Graph) dumpTo(w io.Writer) error {
	d := &dumper{g: g, out: bufio.NewWriterSize(w, 1<<20), scr: make([]byte, 0, 4096)}
	d.symShards = shardSymbolRows(g, len(dumpTables))
	for _, t := range dumpTables {
		d.table(t)
	}
	return d.out.Flush()
}

func writeDump(path string, g *Graph) error {
	f, err := os.OpenFile(path, os.O_WRONLY|os.O_CREATE|os.O_TRUNC, 0o644)
	if err != nil {
		return err
	}
	derr := g.dumpTo(f)
	if cerr := f.Close(); derr == nil {
		derr = cerr
	}
	return derr
}

func (d *dumper) table(name string) {
	d.rows = d.rows[:0]
	d.ci, d.co = 0, 0
	ncol, n := 0, 0
	g := d.g
	switch name {
	case "symbols":
		ncol = len(symColNames)
		n = d.g.Sym.n
		if d.symShards != nil {
			for _, sh := range d.symShards {
				d.rows = append(d.rows, sh...)
			}
			break
		}
		for i := 0; i < n; i++ {
			d.scr = d.scr[:0]
			d.g.Sym.symDump(i, d.g, &d.scr)
			d.addRow()
		}
	case "files":
		ncol = 29
		for i := range d.g.File {
			f := &d.g.File[i]
			d.scr = d.scr[:0]
			d.scr = append(d.scr, "R "...)
			putI(&d.scr, int64(i+1))
			putSep(&d.scr)
			putText(&d.scr, f.Path)
			putSep(&d.scr)
			putText(&d.scr, f.Dir)
			putSep(&d.scr)
			putText(&d.scr, f.Basename)
			putSep(&d.scr)
			putText(&d.scr, f.Ext)
			putSep(&d.scr)
			putText(&d.scr, "go")
			putSep(&d.scr)
			putI(&d.scr, int64(f.ModuleID+1))
			putSep(&d.scr)
			putI(&d.scr, int64(f.Bytes))
			putSep(&d.scr)
			putI(&d.scr, int64(f.Lines))
			putSep(&d.scr)
			putI(&d.scr, int64(f.Sloc))
			putSep(&d.scr)
			putI(&d.scr, int64(f.Blank))
			putSep(&d.scr)
			putI(&d.scr, int64(f.Comment))
			putSep(&d.scr)
			putI(&d.scr, int64(f.DocLines))
			putSep(&d.scr)
			putI(&d.scr, int64(f.MaxLine))
			putSep(&d.scr)
			putText(&d.scr, f.SHA1)
			putSep(&d.scr)
			putI(&d.scr, int64(f.Parsed))
			putSep(&d.scr)
			putI(&d.scr, int64(f.IsTest))
			putSep(&d.scr)
			putI(&d.scr, int64(f.IsGen))
			putSep(&d.scr)
			putI(&d.scr, int64(f.IsVend))
			putSep(&d.scr)
			putI(&d.scr, int64(f.NParsErr))
			putSep(&d.scr)
			putI(&d.scr, int64(f.NMissing))
			putSep(&d.scr)
			putF(&d.scr, f.ParseMS)
			putSep(&d.scr)
			putI(&d.scr, int64(f.NSymbols))
			putSep(&d.scr)
			putI(&d.scr, int64(f.NFuncs))
			putSep(&d.scr)
			putI(&d.scr, int64(f.NTypes))
			putSep(&d.scr)
			putI(&d.scr, int64(f.NImports))
			putSep(&d.scr)
			putI(&d.scr, int64(f.TotalCyc))
			putSep(&d.scr)
			putI(&d.scr, int64(f.MaxCyc))
			putSep(&d.scr)
			putI(&d.scr, int64(f.TotalRisk))
			d.addRow()
		}
	case "modules":
		ncol = 10
		for i := range d.g.Mod {
			m := &d.g.Mod[i]
			d.scr = d.scr[:0]
			d.scr = append(d.scr, "R "...)
			putI(&d.scr, int64(i+1))
			putSep(&d.scr)
			putText(&d.scr, m.Name)
			putSep(&d.scr)
			putText(&d.scr, m.Kind)
			putSep(&d.scr)
			putI(&d.scr, int64(m.NFiles))
			putSep(&d.scr)
			putI(&d.scr, int64(m.NSyms))
			putSep(&d.scr)
			putI(&d.scr, int64(m.NPublic))
			putSep(&d.scr)
			putI(&d.scr, int64(m.Sloc))
			putSep(&d.scr)
			putI(&d.scr, int64(m.FanIn))
			putSep(&d.scr)
			putI(&d.scr, int64(m.FanOut))
			putSep(&d.scr)
			putF(&d.scr, m.Instab)
			d.addRow()
		}
	case "meta":
		ncol = 2
		keys := make([]string, 0, len(d.g.Meta))
		for k := range d.g.Meta {
			if runtimeMeta[k] {
				continue
			}
			keys = append(keys, k)
		}
		sort.Strings(keys)
		for _, k := range keys {
			d.scr = d.scr[:0]
			d.scr = append(d.scr, "R "...)
			putText(&d.scr, k)
			putSep(&d.scr)
			putText(&d.scr, d.g.Meta[k])
			d.addRow()
		}
	case "module_depth":
		ncol = 4
		for i := range d.g.Mod {
			m := &d.g.Mod[i]
			if !m.HasDep {
				continue
			}
			d.rowI4(int64(i+1), int64(m.Depth), int64(m.NDirect), int64(m.NTrans))
		}
	case "sym_fts":

		ncol = 3
		for i := 0; i < d.g.Sym.n; i++ {
			d.rowI3(0, 0, 0)
			_ = i
			d.rows[len(d.rows)-1] = `R \N \N \N`
		}
	case "attributes", "locals", "enum_members":

		ncol = map[string]int{"attributes": 6, "locals": 11, "enum_members": 5}[name]
	case "error_chain_depth":
		ncol = 2
		for _, e := range d.g.ErrChain {
			d.rowI2(int64(e.SymbolID+1), int64(e.MaxDepth))
		}
	case "params":
		ncol = 13
		for i, p := range d.g.Params {
			s := g.paramsSym[i]
			d.scr = d.scr[:0]
			d.scr = append(d.scr, "R "...)
			fk(&d.scr, s)
			putSep(&d.scr)
			putI(&d.scr, int64(p.Pos))
			putSep(&d.scr)
			d.txt(p.Name)
			putSep(&d.scr)
			putText(&d.scr, d.g.Str.get(p.Typ))
			putSep(&d.scr)
			d.txt(p.Default)
			putSep(&d.scr)
			putI(&d.scr, int64(p.Opt))
			putSep(&d.scr)
			putI(&d.scr, int64(p.Variadic))
			putSep(&d.scr)
			putI(&d.scr, int64(p.Ref))
			putSep(&d.scr)
			putI(&d.scr, int64(p.Mutable))
			putSep(&d.scr)
			putI(&d.scr, int64(p.Nullable))
			putSep(&d.scr)
			putI(&d.scr, int64(p.Generic))
			putSep(&d.scr)
			putI(&d.scr, int64(p.Untyped))
			putSep(&d.scr)
			putI(&d.scr, int64(p.Depth))
			d.addRow()
		}
	case "fields":
		ncol = 14
		for i, f := range d.g.Fields {
			s := d.g.fieldsSym[i]
			d.scr = d.scr[:0]
			d.scr = append(d.scr, "R "...)
			fk(&d.scr, s)
			putSep(&d.scr)
			putI(&d.scr, int64(f.Ordinal))
			putSep(&d.scr)
			putText(&d.scr, d.g.Str.get(f.Name))
			putSep(&d.scr)
			putText(&d.scr, d.g.Str.get(f.Typ))
			putSep(&d.scr)
			putText(&d.scr, d.g.Str.get(f.Visibility))
			putSep(&d.scr)
			putI(&d.scr, int64(f.Line))
			putSep(&d.scr)
			putI(&d.scr, int64(f.Static))
			putSep(&d.scr)
			putI(&d.scr, int64(f.Const))
			putSep(&d.scr)
			putI(&d.scr, int64(f.Mutable))
			putSep(&d.scr)
			putI(&d.scr, int64(f.Nullable))
			putSep(&d.scr)
			putI(&d.scr, int64(f.Collection))
			putSep(&d.scr)
			putI(&d.scr, int64(f.Untyped))
			putSep(&d.scr)
			putI(&d.scr, int64(f.HasDefault))
			putSep(&d.scr)
			putI(&d.scr, int64(f.Depth))
			d.addRow()
		}
	case "edges":
		ncol = 6
		for _, e := range d.g.edgeList {
			d.scr = d.scr[:0]
			d.scr = append(d.scr, "R "...)
			fk(&d.scr, e.Caller)
			putSep(&d.scr)
			fk(&d.scr, e.Callee)
			putSep(&d.scr)
			putI(&d.scr, int64(e.NCalls))
			putSep(&d.scr)
			putI(&d.scr, int64(e.SameFile))
			putSep(&d.scr)
			putI(&d.scr, int64(e.SameMod))
			putSep(&d.scr)
			putI(&d.scr, int64(e.IsSelf))
			d.addRow()
		}
	case "callsites":
		ncol = 3
		for _, c := range d.g.csList {
			d.rowI3(int64(c.Caller+1), int64(c.Callee+1), int64(c.Line))
		}
	case "unresolved_calls":
		ncol = 4
		for _, u := range d.g.unresList {
			d.scr = d.scr[:0]
			d.scr = append(d.scr, "R "...)
			fk(&d.scr, u.Caller)
			putSep(&d.scr)
			putText(&d.scr, trunc(d.g.Str.get(u.Name), 160))
			putSep(&d.scr)
			putI(&d.scr, int64(u.N))
			putSep(&d.scr)
			putI(&d.scr, int64(u.Line))
			d.addRow()
		}
	case "imports":
		ncol = 13
		for i, im := range d.g.Imports {
			d.scr = d.scr[:0]
			d.scr = append(d.scr, "R "...)
			putI(&d.scr, int64(i+1))
			putSep(&d.scr)
			fk(&d.scr, im.FileID)
			putSep(&d.scr)
			putText(&d.scr, trunc(d.g.Str.get(im.Target), 300))
			putSep(&d.scr)
			fk(&d.scr, im.TargetID)
			putSep(&d.scr)
			d.txt(im.Alias)
			putSep(&d.scr)
			putText(&d.scr, d.g.Str.get(im.Kind))
			putSep(&d.scr)
			putI(&d.scr, int64(im.Line))
			putSep(&d.scr)
			putI(&d.scr, int64(im.External))
			putSep(&d.scr)
			putI(&d.scr, int64(im.Relative))
			putSep(&d.scr)
			putI(&d.scr, int64(im.Wildcard))
			putSep(&d.scr)
			putI(&d.scr, int64(im.TypeOnly))
			putSep(&d.scr)
			putI(&d.scr, int64(im.Dynamic))
			putSep(&d.scr)
			putI(&d.scr, int64(im.NNames))
			d.addRow()
		}
	case "hazards":
		ncol = 5
		for _, h := range d.g.Hazards {
			d.scr = d.scr[:0]
			d.scr = append(d.scr, "R "...)
			fk(&d.scr, h.SymbolID)
			putSep(&d.scr)
			putText(&d.scr, d.g.Str.get(h.Pattern))
			putSep(&d.scr)
			putText(&d.scr, d.g.Str.get(h.Category))
			putSep(&d.scr)
			putI(&d.scr, int64(h.N))
			putSep(&d.scr)
			putI(&d.scr, int64(h.Line))
			d.addRow()
		}
	case "literals":
		ncol = 7
		for i, l := range d.g.Literals {
			d.scr = d.scr[:0]
			d.scr = append(d.scr, "R "...)
			putI(&d.scr, int64(i+1))
			putSep(&d.scr)
			if l.SymbolID < 0 {
				putNull(&d.scr)
			} else {
				fk(&d.scr, l.SymbolID)
			}
			putSep(&d.scr)
			fk(&d.scr, l.FileID)
			putSep(&d.scr)
			putText(&d.scr, d.g.Str.get(l.Kind))
			putSep(&d.scr)
			putText(&d.scr, trunc(d.g.Str.get(l.Value), 200))
			putSep(&d.scr)
			putI(&d.scr, int64(l.Line))
			putSep(&d.scr)
			putI(&d.scr, int64(l.Magic))
			d.addRow()
		}
	case "markers":
		ncol = 6
		for i, mk := range d.g.Markers {
			d.scr = d.scr[:0]
			d.scr = append(d.scr, "R "...)
			putI(&d.scr, int64(i+1))
			putSep(&d.scr)
			fk(&d.scr, mk.FileID)
			putSep(&d.scr)
			putNull(&d.scr)
			putSep(&d.scr)
			putText(&d.scr, d.g.Str.get(mk.Kind))
			putSep(&d.scr)
			putI(&d.scr, int64(mk.Line))
			putSep(&d.scr)
			d.txt(mk.Text)
			d.addRow()
		}
	case "goroutines":
		ncol = 14
		for i, o := range d.g.Goro {
			d.scr = d.scr[:0]
			d.scr = append(d.scr, "R "...)
			putI(&d.scr, int64(i+1))
			putSep(&d.scr)
			fk(&d.scr, o.SymbolID)
			putSep(&d.scr)
			fk(&d.scr, o.FileID)
			putSep(&d.scr)
			putI(&d.scr, int64(o.Line))
			putSep(&d.scr)
			putI(&d.scr, int64(o.IsClosure))
			putSep(&d.scr)
			putText(&d.scr, d.g.Str.get(o.Target))
			putSep(&d.scr)
			putI(&d.scr, int64(o.HasCtx))
			putSep(&d.scr)
			putI(&d.scr, int64(o.HasRecover))
			putSep(&d.scr)
			putI(&d.scr, int64(o.HasWG))
			putSep(&d.scr)
			putI(&d.scr, int64(o.HasEG))
			putSep(&d.scr)
			putI(&d.scr, int64(o.ChanExit))
			putSep(&d.scr)
			putI(&d.scr, int64(o.InLoop))
			putSep(&d.scr)
			putI(&d.scr, int64(o.LoopDepth))
			putSep(&d.scr)
			putI(&d.scr, int64(o.BodySloc))
			d.addRow()
		}
	case "defers":
		ncol = 9
		for i, o := range d.g.Defers {
			d.scr = d.scr[:0]
			d.scr = append(d.scr, "R "...)
			putI(&d.scr, int64(i+1))
			putSep(&d.scr)
			fk(&d.scr, o.SymbolID)
			putSep(&d.scr)
			putI(&d.scr, int64(o.Line))
			putSep(&d.scr)
			putText(&d.scr, d.g.Str.get(o.Target))
			putSep(&d.scr)
			putI(&d.scr, int64(o.InLoop))
			putSep(&d.scr)
			putI(&d.scr, int64(o.LoopDepth))
			putSep(&d.scr)
			putI(&d.scr, int64(o.IsClose))
			putSep(&d.scr)
			putI(&d.scr, int64(o.IsUnlock))
			putSep(&d.scr)
			putI(&d.scr, int64(o.IsDone))
			d.addRow()
		}
	case "channels":
		ncol = 8
		for i, c := range d.g.Chans {
			d.scr = d.scr[:0]
			d.scr = append(d.scr, "R "...)
			putI(&d.scr, int64(i+1))
			putSep(&d.scr)
			fk(&d.scr, c.SymbolID)
			putSep(&d.scr)
			fk(&d.scr, c.FileID)
			putSep(&d.scr)
			putText(&d.scr, d.g.Str.get(c.Name))
			putSep(&d.scr)
			putText(&d.scr, d.g.Str.get(c.ElemType))
			putSep(&d.scr)
			putI(&d.scr, int64(c.Capacity))
			putSep(&d.scr)
			putI(&d.scr, int64(c.Line))
			putSep(&d.scr)
			putI(&d.scr, int64(c.ClosedInFn))
			d.addRow()
		}
	case "interfaces":
		ncol = 6
		for _, f := range d.g.Iface {
			d.scr = d.scr[:0]
			d.scr = append(d.scr, "R "...)
			fk(&d.scr, f.SymbolID)
			putSep(&d.scr)
			putI(&d.scr, int64(f.NMethods))
			putSep(&d.scr)
			putI(&d.scr, int64(f.NEmbedded))
			putSep(&d.scr)
			putI(&d.scr, int64(f.Exported))
			putSep(&d.scr)
			putI(&d.scr, int64(f.Constraint))
			putSep(&d.scr)
			putText(&d.scr, d.g.Str.get(f.Methods))
			d.addRow()
		}
	case "structs":
		ncol = 10
		for _, s := range d.g.Structs {
			d.scr = d.scr[:0]
			d.scr = append(d.scr, "R "...)
			fk(&d.scr, s.SymbolID)
			putSep(&d.scr)
			putI(&d.scr, int64(s.NFields))
			putSep(&d.scr)
			putI(&d.scr, int64(s.NEmbedded))
			putSep(&d.scr)
			putI(&d.scr, int64(s.NExported))
			putSep(&d.scr)
			putI(&d.scr, int64(s.EstSize))
			putSep(&d.scr)
			putI(&d.scr, int64(s.EstPad))
			putSep(&d.scr)
			putI(&d.scr, int64(s.SizeExact))
			putSep(&d.scr)
			putI(&d.scr, int64(s.HasMutex))
			putSep(&d.scr)
			putI(&d.scr, int64(s.HasCtx))
			putSep(&d.scr)
			putI(&d.scr, int64(s.NTagged))
			d.addRow()
		}
	case "implements":
		ncol = 5
		for _, im := range d.g.Impl {
			d.scr = d.scr[:0]
			d.scr = append(d.scr, "R "...)
			putText(&d.scr, d.g.Str.get(im.TypeName))
			putSep(&d.scr)
			fk(&d.scr, im.InterfaceID)
			putSep(&d.scr)
			putText(&d.scr, d.g.Str.get(im.InterfaceNam))
			putSep(&d.scr)
			putI(&d.scr, int64(im.NMethods))
			putSep(&d.scr)
			putI(&d.scr, int64(im.InTest))
			d.addRow()
		}
	case "build_tags":
		ncol = 4
		for i, bt := range d.g.BuildTag {
			d.scr = d.scr[:0]
			d.scr = append(d.scr, "R "...)
			putI(&d.scr, int64(i+1))
			putSep(&d.scr)
			fk(&d.scr, bt.FileID)
			putSep(&d.scr)
			putText(&d.scr, d.g.Str.get(bt.Expr))
			putSep(&d.scr)
			putI(&d.scr, int64(bt.Line))
			d.addRow()
		}
	case "user_input_sites":
		ncol = 7
		for i, u := range d.g.UInput {
			d.scr = d.scr[:0]
			d.scr = append(d.scr, "R "...)
			putI(&d.scr, int64(i+1))
			putSep(&d.scr)
			fk(&d.scr, u.SymbolID)
			putSep(&d.scr)
			fk(&d.scr, u.FileID)
			putSep(&d.scr)
			putText(&d.scr, d.g.Str.get(u.Var))
			putSep(&d.scr)
			putText(&d.scr, d.g.Str.get(u.Kind))
			putSep(&d.scr)
			putI(&d.scr, int64(u.Line))
			putSep(&d.scr)
			putI(&d.scr, int64(u.InLoop))
			d.addRow()
		}
	case "secret_candidates":
		ncol = 5
		for i, s := range d.g.Secret {
			d.scr = d.scr[:0]
			d.scr = append(d.scr, "R "...)
			putI(&d.scr, int64(i+1))
			putSep(&d.scr)
			fk(&d.scr, s.SymbolID)
			putSep(&d.scr)
			fk(&d.scr, s.FileID)
			putSep(&d.scr)
			putText(&d.scr, d.g.Str.get(s.Value))
			putSep(&d.scr)
			putI(&d.scr, int64(s.Line))
			d.addRow()
		}
	case "wg_sites":
		ncol = 8
		for i, w := range d.g.WgSites {
			d.scr = d.scr[:0]
			d.scr = append(d.scr, "R "...)
			putI(&d.scr, int64(i+1))
			putSep(&d.scr)
			fk(&d.scr, w.SymbolID)
			putSep(&d.scr)
			fk(&d.scr, w.FileID)
			putSep(&d.scr)
			putI(&d.scr, int64(w.Line))
			putSep(&d.scr)
			putText(&d.scr, d.g.Str.get(w.Var))
			putSep(&d.scr)
			putText(&d.scr, d.g.Str.get(w.Op))
			putSep(&d.scr)
			putI(&d.scr, int64(w.InGoroutine))
			putSep(&d.scr)
			putI(&d.scr, int64(w.InLoop))
			d.addRow()
		}
	}
	sort.Strings(d.rows)
	var num [32]byte
	hdr := append(num[:0], 'T', ' ')
	hdr = append(hdr, name...)
	hdr = append(hdr, ' ')
	hdr = strconv.AppendInt(hdr, int64(ncol), 10)
	hdr = append(hdr, ' ')
	hdr = strconv.AppendInt(hdr, int64(len(d.rows)), 10)
	hdr = append(hdr, '\n')
	d.out.Write(hdr)
	for _, r := range d.rows {
		d.out.WriteString(r)
		d.out.WriteByte('\n')
	}
	d.out.WriteString("E ")
	d.out.WriteString(name)
	d.out.WriteByte('\n')
}

func (d *dumper) txt(id uint32) {
	if id == nullStr {
		putNull(&d.scr)
		return
	}
	putText(&d.scr, d.g.Str.get(id))
}

func (d *dumper) rowI2(a, b int64) {
	d.scr = d.scr[:0]
	d.scr = append(d.scr, "R "...)
	putI(&d.scr, a)
	putSep(&d.scr)
	putI(&d.scr, b)
	d.addRow()
}

func (d *dumper) rowI3(a, b, c int64) {
	d.scr = d.scr[:0]
	d.scr = append(d.scr, "R "...)
	putI(&d.scr, a)
	putSep(&d.scr)
	putI(&d.scr, b)
	putSep(&d.scr)
	putI(&d.scr, c)
	d.addRow()
}

func (d *dumper) rowI4(a, b, c, e int64) {
	d.scr = d.scr[:0]
	d.scr = append(d.scr, "R "...)
	putI(&d.scr, a)
	putSep(&d.scr)
	putI(&d.scr, b)
	putSep(&d.scr)
	putI(&d.scr, c)
	putSep(&d.scr)
	putI(&d.scr, e)
	d.addRow()
}

const maxCell = 72

var parseWorkers = flag.Int("workers", 0,
	"parse workers; 0 (default) uses runtime.GOMAXPROCS (container-aware)")

var parseGC = flag.Int("parse-gc", 60,
	"GC percent during extraction; -1 leaves the runtime default")

type cellVal struct {
	null bool
	isF  bool
	isS  bool
	i    int64
	f    float64
	s    string
}

func ci(v int64) cellVal   { return cellVal{i: v} }
func cf(v float64) cellVal { return cellVal{isF: true, f: v} }
func cs(v string) cellVal  { return cellVal{isS: true, s: v} }

var cnull = cellVal{null: true}

type result struct {
	cols []string
	rows [][]cellVal

	kv  []int64
	nk  int
	lim int
}

func sortRows(r result, keys ...int) result { return sortOrder(r, false, keys...) }

func sortOrder(r result, asc bool, keys ...int) result {
	sort.SliceStable(r.rows, func(a, b int) bool {
		cmp := compareRow(r.rows[a], r.rows[b], keys)
		if asc {
			return cmp < 0
		}
		return cmp > 0
	})

	if r.lim >= 0 && len(r.rows) > r.lim {
		r.rows = r.rows[:r.lim]
	}
	return r
}

func compareRow(x, y []cellVal, keys []int) int {
	for _, k := range keys {
		a, b := x[k], y[k]
		if a.null != b.null {
			if a.null {
				return 1
			}
			return -1
		}
		if a.null {
			continue
		}
		if a.isF || b.isF {
			if a.f != b.f {
				if a.f < b.f {
					return -1
				}
				return 1
			}
			continue
		}
		if a.isS || b.isS {
			if a.s < b.s {
				return -1
			}
			if a.s > b.s {
				return 1
			}
			continue
		}
		if a.i != b.i {
			if a.i < b.i {
				return -1
			}
			return 1
		}
	}
	return 0
}

func sortMixed(r result, dirs []bool, keys ...int) result {
	sort.SliceStable(r.rows, func(a, b int) bool {
		for n, k := range keys {
			c := compareOne(r.rows[a][k], r.rows[b][k])
			if c == 0 {
				continue
			}
			if n < len(dirs) && dirs[n] {
				return c < 0
			}
			return c > 0
		}
		return false
	})
	if r.lim >= 0 && len(r.rows) > r.lim {
		r.rows = r.rows[:r.lim]
	}
	return r
}

func compareOne(a, b cellVal) int {
	if a.null != b.null {
		if a.null {
			return 1
		}
		return -1
	}
	if a.null {
		return 0
	}
	if a.isF || b.isF {
		switch {
		case a.f < b.f:
			return -1
		case a.f > b.f:
			return 1
		}
		return 0
	}
	if a.isS || b.isS {
		switch {
		case a.s < b.s:
			return -1
		case a.s > b.s:
			return 1
		}
		return 0
	}
	switch {
	case a.i < b.i:
		return -1
	case a.i > b.i:
		return 1
	}
	return 0
}

func (r *result) krow(keys []int64, cells ...cellVal) {
	r.rows = append(r.rows, cells)
	r.kv = append(r.kv, keys...)
	r.nk = len(keys)
}

func sortKeys(r result, dirs []bool) result {
	n, nk := len(r.rows), r.nk
	perm := make([]int32, n)
	for i := range perm {
		perm[i] = int32(i)
	}
	sort.SliceStable(perm, func(a, b int) bool {
		ka, kb := r.kv[int(perm[a])*nk:], r.kv[int(perm[b])*nk:]
		for i := range nk {
			if ka[i] == kb[i] {
				continue
			}
			if i < len(dirs) && dirs[i] {
				return ka[i] < kb[i]
			}
			return ka[i] > kb[i]
		}
		return false
	})
	rows := make([][]cellVal, n)
	kv := make([]int64, n*nk)
	for i, p := range perm {
		rows[i] = r.rows[p]
		copy(kv[i*nk:(i+1)*nk], r.kv[int(p)*nk:(int(p)+1)*nk])
	}
	r.rows, r.kv = rows, kv
	if r.lim >= 0 && len(r.rows) > r.lim {
		r.rows = r.rows[:r.lim]
	}
	return r
}

func runeLenB(b []byte) int {
	n := 0
	for i := 0; i < len(b); {
		if b[i] < 0x80 {
			i++
		} else {
			_, sz := utf8.DecodeRune(b[i:])
			i += sz
		}
		n++
	}
	return n
}

func runeCut(s string, max int) string {
	rs := []rune(s)
	if len(rs) <= max {
		return s
	}
	return string(rs[:max]) + "..."
}

func render(w *bufio.Writer, r result) {
	r = capRows(r)
	if len(r.rows) == 0 {
		fmt.Fprintln(w, " (no rows)")
		return
	}
	ncol := len(r.cols)
	widths := make([]int, ncol)
	for i, c := range r.cols {
		widths[i] = len([]rune(c))
	}
	cellBuf := make([]byte, 0, 96)
	fmtCell := func(v cellVal) []byte {
		cellBuf = cellBuf[:0]
		switch {
		case v.null:
			cellBuf = append(cellBuf, '-')
		case v.isS:
			cellBuf = append(cellBuf, v.s...)
		case v.isF:
			cellBuf = strconv.AppendFloat(cellBuf, v.f, 'f', 2, 64)
		default:
			cellBuf = strconv.AppendInt(cellBuf, v.i, 10)
		}
		return cellBuf
	}
	for _, row := range r.rows {
		for i, v := range row {
			b := fmtCell(v)
			n := runeLenB(b)
			if n > maxCell {
				n = maxCell
			}
			if n > widths[i] {
				widths[i] = n
			}
		}
	}
	line := make([]byte, 0, 256)
	emitCell := func(b []byte, i int) {
		line = append(line, b...)
		if pad := widths[i] - runeLenB(b); pad > 0 {
			line = appendPad(line, pad)
		}
	}
	emitRow := func(cells [][]byte) {
		line = line[:0]
		line = append(line, ' ')
		for i := range cells {
			if i > 0 {
				line = append(line, ' ')
			}
			emitCell(cells[i], i)
		}
		line = append(line, '\n')
		w.Write(line)
	}
	colCells := make([][]byte, ncol)
	for i, c := range r.cols {
		colCells[i] = []byte(c)
	}
	emitRow(colCells)
	dash := make([][]byte, ncol)
	for i := range dash {
		dash[i] = []byte(strings.Repeat("-", widths[i]))
	}
	emitRow(dash)
	for _, row := range r.rows {
		line = line[:0]
		line = append(line, ' ')
		for i, v := range row {
			if i > 0 {
				line = append(line, ' ')
			}
			b := fmtCell(v)
			if runeLenB(b) > maxCell {
				b = []byte(runeCut(string(b), maxCell-3))
			}
			line = append(line, b...)
			if pad := widths[i] - runeLenB(b); pad > 0 {
				line = appendPad(line, pad)
			}
		}
		line = append(line, '\n')
		w.Write(line)
	}
}

func appendPad(b []byte, n int) []byte {
	for i := 0; i < n; i++ {
		b = append(b, ' ')
	}
	return b
}

func pad(s string, w int) string {
	n := w - len([]rune(s))
	if n <= 0 {
		return s
	}
	return s + strings.Repeat(" ", n)
}

type numList struct{ nums []int }

func (s *numList) String() string { return "" }
func (s *numList) Set(v string) error {
	n := 0
	for _, c := range v {
		if c >= '0' && c <= '9' {
			n = n*10 + int(c-'0')
		}
	}
	s.nums = append(s.nums, n)
	return nil
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

func errFileCount(g *Graph) int {
	n := 0
	for i := range g.File {
		if g.File[i].NParsErr > 0 {
			n++
		}
	}
	return n
}

const oracleSchemaDDL = "\n" +
	"CREATE TABLE meta(\n" +
	"    key TEXT PRIMARY KEY,\n" +
	"    value TEXT NOT NULL\n" +
	") WITHOUT ROWID, STRICT;\n" +
	"\n" +
	"CREATE TABLE modules(\n" +
	"    id INTEGER PRIMARY KEY,\n" +
	"    name TEXT NOT NULL UNIQUE,\n" +
	"    kind TEXT NOT NULL DEFAULT 'source',\n" +
	"    n_files INT NOT NULL DEFAULT 0,\n" +
	"    n_symbols INT NOT NULL DEFAULT 0,\n" +
	"    n_public INT NOT NULL DEFAULT 0,\n" +
	"    sloc INT NOT NULL DEFAULT 0,\n" +
	"    fan_in INT NOT NULL DEFAULT 0,\n" +
	"    fan_out INT NOT NULL DEFAULT 0,\n" +
	"    instability REAL NOT NULL DEFAULT 0.0\n" +
	") STRICT;\n" +
	"\n" +
	"CREATE TABLE files(\n" +
	"    id INTEGER PRIMARY KEY,\n" +
	"    path TEXT NOT NULL UNIQUE,\n" +
	"    dir TEXT NOT NULL,\n" +
	"    basename TEXT NOT NULL,\n" +
	"    ext TEXT NOT NULL,\n" +
	"    lang TEXT NOT NULL,\n" +
	"    module_id INT REFERENCES modules(id),\n" +
	"    bytes INT NOT NULL,\n" +
	"    lines INT NOT NULL,\n" +
	"    sloc INT NOT NULL,\n" +
	"    blank_lines INT NOT NULL DEFAULT 0,\n" +
	"    comment_lines INT NOT NULL DEFAULT 0,\n" +
	"    doc_lines INT NOT NULL DEFAULT 0,\n" +
	"    max_line_len INT NOT NULL DEFAULT 0,\n" +
	"    sha1 TEXT NOT NULL,\n" +
	"    parsed INT NOT NULL DEFAULT 0,\n" +
	"    is_test INT NOT NULL DEFAULT 0,\n" +
	"    is_generated INT NOT NULL DEFAULT 0,\n" +
	"    is_vendored INT NOT NULL DEFAULT 0,\n" +
	"    n_parse_errors INT NOT NULL DEFAULT 0,\n" +
	"    n_missing_nodes INT NOT NULL DEFAULT 0,\n" +
	"    parse_ms REAL NOT NULL DEFAULT 0.0,\n" +
	"    n_symbols INT NOT NULL DEFAULT 0,\n" +
	"    n_functions INT NOT NULL DEFAULT 0,\n" +
	"    n_types INT NOT NULL DEFAULT 0,\n" +
	"    n_imports INT NOT NULL DEFAULT 0,\n" +
	"    total_cyclo INT NOT NULL DEFAULT 0,\n" +
	"    max_cyclo INT NOT NULL DEFAULT 0,\n" +
	"    total_risk INT NOT NULL DEFAULT 0\n" +
	") STRICT;\n" +
	"\n" +
	"CREATE TABLE symbols(\n" +
	"    id INTEGER PRIMARY KEY,\n" +
	"    file_id INT NOT NULL REFERENCES files(id),\n" +
	"    module_id INT REFERENCES modules(id),\n" +
	"    parent_id INT REFERENCES symbols(id),\n" +
	"    name TEXT NOT NULL,\n" +
	"    qual_name TEXT NOT NULL DEFAULT '',\n" +
	"    kind TEXT NOT NULL,\n" +
	"    line_start INT NOT NULL,\n" +
	"    line_end INT NOT NULL,\n" +
	"    n_lines INT NOT NULL DEFAULT 0,\n" +
	"    byte_start INT NOT NULL DEFAULT 0,\n" +
	"    byte_end INT NOT NULL DEFAULT 0,\n" +
	"    signature TEXT,\n" +
	"    return_type TEXT,\n" +
	"    visibility TEXT NOT NULL DEFAULT '',\n" +
	"\n" +
	"    -- shape\n" +
	"    n_params INT NOT NULL DEFAULT 0,\n" +
	"    n_optional_params INT NOT NULL DEFAULT 0,\n" +
	"    n_generic_params INT NOT NULL DEFAULT 0,\n" +
	"    n_overloads INT NOT NULL DEFAULT 0,\n" +
	"    arity_rank INT NOT NULL DEFAULT 0,\n" +
	"\n" +
	"    -- flags\n" +
	"    is_public INT NOT NULL DEFAULT 0,\n" +
	"    is_static INT NOT NULL DEFAULT 0,\n" +
	"    is_async INT NOT NULL DEFAULT 0,\n" +
	"    is_generator INT NOT NULL DEFAULT 0,\n" +
	"    is_abstract INT NOT NULL DEFAULT 0,\n" +
	"    is_override INT NOT NULL DEFAULT 0,\n" +
	"    is_exported INT NOT NULL DEFAULT 0,\n" +
	"    is_test INT NOT NULL DEFAULT 0,\n" +
	"    is_deprecated INT NOT NULL DEFAULT 0,\n" +
	"    is_entrypoint INT NOT NULL DEFAULT 0,\n" +
	"    is_generated INT NOT NULL DEFAULT 0,\n" +
	"\n" +
	"    -- size\n" +
	"    sloc INT NOT NULL DEFAULT 0,\n" +
	"    body_bytes INT NOT NULL DEFAULT 0,\n" +
	"    n_comment_lines INT NOT NULL DEFAULT 0,\n" +
	"    n_doc_lines INT NOT NULL DEFAULT 0,\n" +
	"    has_doc INT NOT NULL DEFAULT 0,\n" +
	"\n" +
	"    -- complexity\n" +
	"    cyclomatic INT NOT NULL DEFAULT 0,\n" +
	"    cognitive INT NOT NULL DEFAULT 0,\n" +
	"    max_nesting INT NOT NULL DEFAULT 0,\n" +
	"    n_tokens INT NOT NULL DEFAULT 0,\n" +
	"    n_operators INT NOT NULL DEFAULT 0,\n" +
	"    n_operands INT NOT NULL DEFAULT 0,\n" +
	"    n_distinct_operators INT NOT NULL DEFAULT 0,\n" +
	"    n_distinct_operands INT NOT NULL DEFAULT 0,\n" +
	"    halstead_volume INT NOT NULL DEFAULT 0,\n" +
	"    maintainability INT NOT NULL DEFAULT 0,\n" +
	"\n" +
	"    -- control flow\n" +
	"    n_loops INT NOT NULL DEFAULT 0,\n" +
	"    n_branches INT NOT NULL DEFAULT 0,\n" +
	"    n_returns INT NOT NULL DEFAULT 0,\n" +
	"    n_early_returns INT NOT NULL DEFAULT 0,\n" +
	"    n_switch INT NOT NULL DEFAULT 0,\n" +
	"    n_cases INT NOT NULL DEFAULT 0,\n" +
	"    n_ternary INT NOT NULL DEFAULT 0,\n" +
	"    n_logical INT NOT NULL DEFAULT 0,\n" +
	"    n_try INT NOT NULL DEFAULT 0,\n" +
	"    n_catch INT NOT NULL DEFAULT 0,\n" +
	"    n_catch_broad INT NOT NULL DEFAULT 0,\n" +
	"    n_catch_empty INT NOT NULL DEFAULT 0,\n" +
	"    n_finally INT NOT NULL DEFAULT 0,\n" +
	"    n_throw INT NOT NULL DEFAULT 0,\n" +
	"    n_labels INT NOT NULL DEFAULT 0,\n" +
	"    n_gotos INT NOT NULL DEFAULT 0,\n" +
	"\n" +
	"    -- what sits inside a loop\n" +
	"    max_loop_depth INT NOT NULL DEFAULT 0,\n" +
	"    call_in_loop INT NOT NULL DEFAULT 0,\n" +
	"    alloc_in_loop INT NOT NULL DEFAULT 0,\n" +
	"    io_in_loop INT NOT NULL DEFAULT 0,\n" +
	"    await_in_loop INT NOT NULL DEFAULT 0,\n" +
	"    lock_in_loop INT NOT NULL DEFAULT 0,\n" +
	"    concat_in_loop INT NOT NULL DEFAULT 0,\n" +
	"    regex_in_loop INT NOT NULL DEFAULT 0,\n" +
	"    query_in_loop INT NOT NULL DEFAULT 0,\n" +
	"    branch_in_loop INT NOT NULL DEFAULT 0,\n" +
	"\n" +
	"    -- data texture\n" +
	"    n_locals INT NOT NULL DEFAULT 0,\n" +
	"    n_assign INT NOT NULL DEFAULT 0,\n" +
	"    n_compound_assign INT NOT NULL DEFAULT 0,\n" +
	"    n_incdec INT NOT NULL DEFAULT 0,\n" +
	"    n_cmp INT NOT NULL DEFAULT 0,\n" +
	"    n_bitop INT NOT NULL DEFAULT 0,\n" +
	"    n_shift INT NOT NULL DEFAULT 0,\n" +
	"    n_arith INT NOT NULL DEFAULT 0,\n" +
	"    n_string_lit INT NOT NULL DEFAULT 0,\n" +
	"    n_regex_lit INT NOT NULL DEFAULT 0,\n" +
	"    n_float_lit INT NOT NULL DEFAULT 0,\n" +
	"    n_magic INT NOT NULL DEFAULT 0,\n" +
	"    n_null_check INT NOT NULL DEFAULT 0,\n" +
	"    n_subscript INT NOT NULL DEFAULT 0,\n" +
	"    n_member_access INT NOT NULL DEFAULT 0,\n" +
	"    n_lambda INT NOT NULL DEFAULT 0,\n" +
	"    n_closure_capture INT NOT NULL DEFAULT 0,\n" +
	"\n" +
	"    -- the call graph\n" +
	"    n_calls INT NOT NULL DEFAULT 0,\n" +
	"    n_unique_calls INT NOT NULL DEFAULT 0,\n" +
	"    n_dynamic_calls INT NOT NULL DEFAULT 0,\n" +
	"    n_unresolved_calls INT NOT NULL DEFAULT 0,\n" +
	"    fan_in INT NOT NULL DEFAULT 0,\n" +
	"    fan_out INT NOT NULL DEFAULT 0,\n" +
	"    n_callsites INT NOT NULL DEFAULT 0,\n" +
	"    is_recursive INT NOT NULL DEFAULT 0,\n" +
	"    is_leaf INT NOT NULL DEFAULT 0,\n" +
	"    is_root INT NOT NULL DEFAULT 0,\n" +
	"\n" +
	"    -- hazards\n" +
	"    n_hazards INT NOT NULL DEFAULT 0,\n" +
	"    risk_score INT NOT NULL DEFAULT 0\n" +
	"    ,\n" +
	"    n_goroutine INT NOT NULL DEFAULT 0,\n" +
	"    n_channel INT NOT NULL DEFAULT 0,\n" +
	"    n_defer INT NOT NULL DEFAULT 0,\n" +
	"    n_lock INT NOT NULL DEFAULT 0,\n" +
	"    n_atomic INT NOT NULL DEFAULT 0,\n" +
	"    n_context INT NOT NULL DEFAULT 0,\n" +
	"    n_io INT NOT NULL DEFAULT 0,\n" +
	"    n_net INT NOT NULL DEFAULT 0,\n" +
	"    n_sql INT NOT NULL DEFAULT 0,\n" +
	"    n_exec INT NOT NULL DEFAULT 0,\n" +
	"    n_unsafe INT NOT NULL DEFAULT 0,\n" +
	"    n_reflect INT NOT NULL DEFAULT 0,\n" +
	"    n_cgo INT NOT NULL DEFAULT 0,\n" +
	"    n_alloc INT NOT NULL DEFAULT 0,\n" +
	"    n_panic INT NOT NULL DEFAULT 0,\n" +
	"    n_time INT NOT NULL DEFAULT 0,\n" +
	"    n_goroutines INT NOT NULL DEFAULT 0,\n" +
	"    n_go_in_loop INT NOT NULL DEFAULT 0,\n" +
	"    n_defer_in_loop INT NOT NULL DEFAULT 0,\n" +
	"    n_defer_close INT NOT NULL DEFAULT 0,\n" +
	"    n_recover INT NOT NULL DEFAULT 0,\n" +
	"    n_chan_send INT NOT NULL DEFAULT 0,\n" +
	"    n_chan_recv INT NOT NULL DEFAULT 0,\n" +
	"    n_chan_close INT NOT NULL DEFAULT 0,\n" +
	"    n_chan_type INT NOT NULL DEFAULT 0,\n" +
	"    n_chan_unbuffered INT NOT NULL DEFAULT 0,\n" +
	"    n_select INT NOT NULL DEFAULT 0,\n" +
	"    n_select_default INT NOT NULL DEFAULT 0,\n" +
	"    n_select_ctx_done INT NOT NULL DEFAULT 0,\n" +
	"    n_type_switch INT NOT NULL DEFAULT 0,\n" +
	"    n_type_assert INT NOT NULL DEFAULT 0,\n" +
	"    n_type_assert_unchecked INT NOT NULL DEFAULT 0,\n" +
	"    n_ctx_params INT NOT NULL DEFAULT 0,\n" +
	"    n_ctx_background INT NOT NULL DEFAULT 0,\n" +
	"    n_ctx_done INT NOT NULL DEFAULT 0,\n" +
	"    n_ctx_passed INT NOT NULL DEFAULT 0,\n" +
	"    n_ctx_withcancel INT NOT NULL DEFAULT 0,\n" +
	"    n_cancel_called INT NOT NULL DEFAULT 0,\n" +
	"    n_err_returns INT NOT NULL DEFAULT 0,\n" +
	"    n_err_checks INT NOT NULL DEFAULT 0,\n" +
	"    n_err_ignored INT NOT NULL DEFAULT 0,\n" +
	"    n_err_shadowed INT NOT NULL DEFAULT 0,\n" +
	"    n_err_wrapped INT NOT NULL DEFAULT 0,\n" +
	"    n_naked_returns INT NOT NULL DEFAULT 0,\n" +
	"    n_named_results INT NOT NULL DEFAULT 0,\n" +
	"    n_any_params INT NOT NULL DEFAULT 0,\n" +
	"    n_iface_params INT NOT NULL DEFAULT 0,\n" +
	"    n_iface_returns INT NOT NULL DEFAULT 0,\n" +
	"    n_iface_literal INT NOT NULL DEFAULT 0,\n" +
	"    n_make_no_cap INT NOT NULL DEFAULT 0,\n" +
	"    n_append_in_loop INT NOT NULL DEFAULT 0,\n" +
	"    n_sprintf_in_loop INT NOT NULL DEFAULT 0,\n" +
	"    n_conv_in_loop INT NOT NULL DEFAULT 0,\n" +
	"    n_range_value_copy INT NOT NULL DEFAULT 0,\n" +
	"    n_loopvar_capture INT NOT NULL DEFAULT 0,\n" +
	"    n_composite_lit INT NOT NULL DEFAULT 0,\n" +
	"    n_struct_literal INT NOT NULL DEFAULT 0,\n" +
	"    n_unsafe_ops INT NOT NULL DEFAULT 0,\n" +
	"    n_cgo_calls INT NOT NULL DEFAULT 0,\n" +
	"    n_reflect_ops INT NOT NULL DEFAULT 0,\n" +
	"    n_go_directives INT NOT NULL DEFAULT 0,\n" +
	"    n_struct_tags INT NOT NULL DEFAULT 0,\n" +
	"    n_panics INT NOT NULL DEFAULT 0,\n" +
	"    n_log_fatal INT NOT NULL DEFAULT 0,\n" +
	"    n_time_tick INT NOT NULL DEFAULT 0,\n" +
	"    n_sql_concat INT NOT NULL DEFAULT 0,\n" +
	"    n_lock_by_value_params INT NOT NULL DEFAULT 0,\n" +
	"    n_nolint INT NOT NULL DEFAULT 0,\n" +
	"    n_ctx_background_call INT NOT NULL DEFAULT 0,\n" +
	"    n_http_default_client INT NOT NULL DEFAULT 0,\n" +
	"    n_exit_call INT NOT NULL DEFAULT 0,\n" +
	"    n_time_after_in_loop INT NOT NULL DEFAULT 0,\n" +
	"    n_time_tick_call INT NOT NULL DEFAULT 0,\n" +
	"    n_errorf_no_wrap INT NOT NULL DEFAULT 0,\n" +
	"    n_weak_random INT NOT NULL DEFAULT 0,\n" +
	"    n_weak_crypto INT NOT NULL DEFAULT 0,\n" +
	"    n_readall_in_loop INT NOT NULL DEFAULT 0,\n" +
	"    n_env_read INT NOT NULL DEFAULT 0,\n" +
	"    n_redirect INT NOT NULL DEFAULT 0,\n" +
	"    n_auth_call INT NOT NULL DEFAULT 0,\n" +
	"    n_deserialize INT NOT NULL DEFAULT 0,\n" +
	"    n_dynamic_open INT NOT NULL DEFAULT 0,\n" +
	"    n_zip_read INT NOT NULL DEFAULT 0,\n" +
	"    n_decode_call INT NOT NULL DEFAULT 0,\n" +
	"    n_waitgroup_add INT NOT NULL DEFAULT 0,\n" +
	"    n_lock_call INT NOT NULL DEFAULT 0,\n" +
	"    n_unlock_call INT NOT NULL DEFAULT 0,\n" +
	"    n_close_call INT NOT NULL DEFAULT 0,\n" +
	"    n_reflect_call INT NOT NULL DEFAULT 0,\n" +
	"    n_unsafe_call INT NOT NULL DEFAULT 0,\n" +
	"    n_exec_call INT NOT NULL DEFAULT 0,\n" +
	"    n_pathjoin_in_loop INT NOT NULL DEFAULT 0,\n" +
	"    n_elif INT NOT NULL DEFAULT 0,\n" +
	"    n_external_calls INT NOT NULL DEFAULT 0,\n" +
	"    receiver_is_pointer INT NOT NULL DEFAULT 0,\n" +
	"    receiver_type TEXT NOT NULL DEFAULT '',\n" +
	"    is_handler INT NOT NULL DEFAULT 0,\n" +
	"    is_init INT NOT NULL DEFAULT 0,\n" +
	"    n_ctx_in_loop INT NOT NULL DEFAULT 0,\n" +
	"    n_err_nil_return INT NOT NULL DEFAULT 0,\n" +
	"    n_loopvar_rebind INT NOT NULL DEFAULT 0,\n" +
	"    n_insecure_tls INT NOT NULL DEFAULT 0,\n" +
	"    n_wg_done INT NOT NULL DEFAULT 0,\n" +
	"    n_wait_call INT NOT NULL DEFAULT 0,\n" +
	"    n_sleep INT NOT NULL DEFAULT 0,\n" +
	"    n_rows_err_check INT NOT NULL DEFAULT 0,\n" +
	"    n_timer_new INT NOT NULL DEFAULT 0,\n" +
	"    n_timer_stop INT NOT NULL DEFAULT 0,\n" +
	"    n_semaphore INT NOT NULL DEFAULT 0\n" +
	") STRICT;\n" +
	"\n" +
	"CREATE TABLE params(\n" +
	"    symbol_id INT NOT NULL REFERENCES symbols(id),\n" +
	"    pos INT NOT NULL,\n" +
	"    name TEXT,\n" +
	"    type TEXT NOT NULL DEFAULT '',\n" +
	"    default_value TEXT,\n" +
	"    is_optional INT NOT NULL DEFAULT 0,\n" +
	"    is_variadic INT NOT NULL DEFAULT 0,\n" +
	"    is_ref INT NOT NULL DEFAULT 0,\n" +
	"    is_mutable INT NOT NULL DEFAULT 0,\n" +
	"    is_nullable INT NOT NULL DEFAULT 0,\n" +
	"    is_generic INT NOT NULL DEFAULT 0,\n" +
	"    is_untyped INT NOT NULL DEFAULT 0,\n" +
	"    type_depth INT NOT NULL DEFAULT 0,\n" +
	"    PRIMARY KEY(symbol_id, pos)\n" +
	") WITHOUT ROWID, STRICT;\n" +
	"\n" +
	"CREATE TABLE fields(\n" +
	"    symbol_id INT NOT NULL REFERENCES symbols(id),\n" +
	"    ordinal INT NOT NULL,\n" +
	"    name TEXT NOT NULL,\n" +
	"    type TEXT NOT NULL DEFAULT '',\n" +
	"    visibility TEXT NOT NULL DEFAULT '',\n" +
	"    line INT NOT NULL DEFAULT 0,\n" +
	"    is_static INT NOT NULL DEFAULT 0,\n" +
	"    is_const INT NOT NULL DEFAULT 0,\n" +
	"    is_mutable INT NOT NULL DEFAULT 0,\n" +
	"    is_nullable INT NOT NULL DEFAULT 0,\n" +
	"    is_collection INT NOT NULL DEFAULT 0,\n" +
	"    is_untyped INT NOT NULL DEFAULT 0,\n" +
	"    has_default INT NOT NULL DEFAULT 0,\n" +
	"    type_depth INT NOT NULL DEFAULT 0,\n" +
	"    PRIMARY KEY(symbol_id, ordinal)\n" +
	") WITHOUT ROWID, STRICT;\n" +
	"\n" +
	"CREATE TABLE locals(\n" +
	"    symbol_id INT NOT NULL REFERENCES symbols(id),\n" +
	"    ordinal INT NOT NULL,\n" +
	"    name TEXT NOT NULL,\n" +
	"    type TEXT NOT NULL DEFAULT '',\n" +
	"    line INT NOT NULL DEFAULT 0,\n" +
	"    is_const INT NOT NULL DEFAULT 0,\n" +
	"    is_mutable INT NOT NULL DEFAULT 0,\n" +
	"    is_untyped INT NOT NULL DEFAULT 0,\n" +
	"    has_init INT NOT NULL DEFAULT 0,\n" +
	"    in_loop INT NOT NULL DEFAULT 0,\n" +
	"    scope_depth INT NOT NULL DEFAULT 0,\n" +
	"    PRIMARY KEY(symbol_id, ordinal)\n" +
	") WITHOUT ROWID, STRICT;\n" +
	"\n" +
	"CREATE TABLE edges(\n" +
	"    caller_id INT NOT NULL REFERENCES symbols(id),\n" +
	"    callee_id INT NOT NULL REFERENCES symbols(id),\n" +
	"    n_calls INT NOT NULL DEFAULT 1,\n" +
	"    same_file INT NOT NULL DEFAULT 0,\n" +
	"    same_module INT NOT NULL DEFAULT 0,\n" +
	"    is_self INT NOT NULL DEFAULT 0,\n" +
	"    PRIMARY KEY(caller_id, callee_id)\n" +
	") WITHOUT ROWID, STRICT;\n" +
	"\n" +
	"CREATE TABLE callsites(\n" +
	"    caller_id INT NOT NULL REFERENCES symbols(id),\n" +
	"    callee_id INT NOT NULL REFERENCES symbols(id),\n" +
	"    line INT NOT NULL,\n" +
	"    PRIMARY KEY(caller_id, callee_id, line)\n" +
	") WITHOUT ROWID, STRICT;\n" +
	"\n" +
	"CREATE TABLE unresolved_calls(\n" +
	"    caller_id INT NOT NULL REFERENCES symbols(id),\n" +
	"    name TEXT NOT NULL,\n" +
	"    n INT NOT NULL DEFAULT 1,\n" +
	"    first_line INT NOT NULL DEFAULT 0,\n" +
	"    PRIMARY KEY(caller_id, name)\n" +
	") WITHOUT ROWID, STRICT;\n" +
	"\n" +
	"CREATE TABLE imports(\n" +
	"    id INTEGER PRIMARY KEY,\n" +
	"    file_id INT NOT NULL REFERENCES files(id),\n" +
	"    target TEXT NOT NULL,\n" +
	"    target_id INT REFERENCES files(id),\n" +
	"    alias TEXT,\n" +
	"    kind TEXT NOT NULL DEFAULT 'import',\n" +
	"    line INT NOT NULL DEFAULT 0,\n" +
	"    is_external INT NOT NULL DEFAULT 0,\n" +
	"    is_relative INT NOT NULL DEFAULT 0,\n" +
	"    is_wildcard INT NOT NULL DEFAULT 0,\n" +
	"    is_type_only INT NOT NULL DEFAULT 0,\n" +
	"    is_dynamic INT NOT NULL DEFAULT 0,\n" +
	"    n_names INT NOT NULL DEFAULT 0\n" +
	") STRICT;\n" +
	"\n" +
	"CREATE TABLE hazards(\n" +
	"    symbol_id INT NOT NULL REFERENCES symbols(id),\n" +
	"    pattern TEXT NOT NULL,\n" +
	"    category TEXT NOT NULL,\n" +
	"    n INT NOT NULL DEFAULT 1,\n" +
	"    first_line INT NOT NULL DEFAULT 0,\n" +
	"    PRIMARY KEY(symbol_id, pattern)\n" +
	") WITHOUT ROWID, STRICT;\n" +
	"\n" +
	"CREATE TABLE attributes(\n" +
	"    id INTEGER PRIMARY KEY,\n" +
	"    symbol_id INT REFERENCES symbols(id),\n" +
	"    file_id INT NOT NULL REFERENCES files(id),\n" +
	"    name TEXT NOT NULL,\n" +
	"    args TEXT,\n" +
	"    line INT NOT NULL DEFAULT 0\n" +
	") STRICT;\n" +
	"\n" +
	"CREATE TABLE literals(\n" +
	"    id INTEGER PRIMARY KEY,\n" +
	"    symbol_id INT REFERENCES symbols(id),\n" +
	"    file_id INT NOT NULL REFERENCES files(id),\n" +
	"    kind TEXT NOT NULL,\n" +
	"    value TEXT NOT NULL,\n" +
	"    line INT NOT NULL,\n" +
	"    is_magic INT NOT NULL DEFAULT 0\n" +
	") STRICT;\n" +
	"\n" +
	"CREATE TABLE enum_members(\n" +
	"    symbol_id INT NOT NULL REFERENCES symbols(id),\n" +
	"    ordinal INT NOT NULL,\n" +
	"    name TEXT NOT NULL,\n" +
	"    value TEXT,\n" +
	"    n_fields INT NOT NULL DEFAULT 0,\n" +
	"    PRIMARY KEY(symbol_id, ordinal)\n" +
	") WITHOUT ROWID, STRICT;\n" +
	"\n" +
	"CREATE TABLE markers(\n" +
	"    id INTEGER PRIMARY KEY,\n" +
	"    file_id INT NOT NULL REFERENCES files(id),\n" +
	"    symbol_id INT REFERENCES symbols(id),\n" +
	"    kind TEXT NOT NULL,\n" +
	"    line INT NOT NULL,\n" +
	"    text TEXT\n" +
	") STRICT;\n" +
	"\n" +
	"CREATE VIRTUAL TABLE sym_fts USING fts5(name, qual_name, signature, content='');\n" +
	"\n" +
	"\n" +
	"CREATE TABLE goroutines(\n" +
	"    id INTEGER PRIMARY KEY,\n" +
	"    symbol_id INT NOT NULL REFERENCES symbols(id),\n" +
	"    file_id INT NOT NULL REFERENCES files(id),\n" +
	"    line INT NOT NULL,\n" +
	"    is_closure INT NOT NULL DEFAULT 0,\n" +
	"    target TEXT NOT NULL DEFAULT '',\n" +
	"    has_ctx INT NOT NULL DEFAULT 0,\n" +
	"    has_recover INT NOT NULL DEFAULT 0,\n" +
	"    has_waitgroup INT NOT NULL DEFAULT 0,\n" +
	"    has_errgroup INT NOT NULL DEFAULT 0,\n" +
	"    has_chan_exit INT NOT NULL DEFAULT 0,\n" +
	"    in_loop INT NOT NULL DEFAULT 0,\n" +
	"    loop_depth INT NOT NULL DEFAULT 0,\n" +
	"    body_sloc INT NOT NULL DEFAULT 0\n" +
	") STRICT;\n" +
	"\n" +
	"CREATE TABLE defers(\n" +
	"    id INTEGER PRIMARY KEY,\n" +
	"    symbol_id INT NOT NULL REFERENCES symbols(id),\n" +
	"    line INT NOT NULL,\n" +
	"    target TEXT NOT NULL DEFAULT '',\n" +
	"    in_loop INT NOT NULL DEFAULT 0,\n" +
	"    loop_depth INT NOT NULL DEFAULT 0,\n" +
	"    is_close INT NOT NULL DEFAULT 0,\n" +
	"    is_unlock INT NOT NULL DEFAULT 0,\n" +
	"    is_done INT NOT NULL DEFAULT 0\n" +
	") STRICT;\n" +
	"\n" +
	"CREATE TABLE channels(\n" +
	"    id INTEGER PRIMARY KEY,\n" +
	"    symbol_id INT REFERENCES symbols(id),\n" +
	"    file_id INT NOT NULL REFERENCES files(id),\n" +
	"    name TEXT NOT NULL DEFAULT '',\n" +
	"    elem_type TEXT NOT NULL DEFAULT '',\n" +
	"    capacity INT NOT NULL DEFAULT 0,\n" +
	"    line INT NOT NULL,\n" +
	"    closed_in_fn INT NOT NULL DEFAULT 0\n" +
	") STRICT;\n" +
	"\n" +
	"CREATE TABLE interfaces(\n" +
	"    symbol_id INT NOT NULL PRIMARY KEY REFERENCES symbols(id),\n" +
	"    n_methods INT NOT NULL DEFAULT 0,\n" +
	"    n_embedded INT NOT NULL DEFAULT 0,\n" +
	"    is_exported INT NOT NULL DEFAULT 0,\n" +
	"    is_constraint INT NOT NULL DEFAULT 0,\n" +
	"    methods TEXT NOT NULL DEFAULT ''\n" +
	") WITHOUT ROWID, STRICT;\n" +
	"\n" +
	"CREATE TABLE structs(\n" +
	"    symbol_id INT NOT NULL PRIMARY KEY REFERENCES symbols(id),\n" +
	"    n_fields INT NOT NULL DEFAULT 0,\n" +
	"    n_embedded INT NOT NULL DEFAULT 0,\n" +
	"    n_exported_fields INT NOT NULL DEFAULT 0,\n" +
	"    est_size INT NOT NULL DEFAULT 0,\n" +
	"    est_padding INT NOT NULL DEFAULT 0,\n" +
	"    size_exact INT NOT NULL DEFAULT 0,\n" +
	"    has_mutex INT NOT NULL DEFAULT 0,\n" +
	"    has_ctx_field INT NOT NULL DEFAULT 0,\n" +
	"    n_tagged_fields INT NOT NULL DEFAULT 0\n" +
	") WITHOUT ROWID, STRICT;\n" +
	"\n" +
	"CREATE TABLE implements(\n" +
	"    type_name TEXT NOT NULL,\n" +
	"    interface_id INT NOT NULL REFERENCES symbols(id),\n" +
	"    interface_name TEXT NOT NULL,\n" +
	"    n_methods INT NOT NULL DEFAULT 0,\n" +
	"    in_test INT NOT NULL DEFAULT 0,\n" +
	"    PRIMARY KEY(type_name, interface_id)\n" +
	") WITHOUT ROWID, STRICT;\n" +
	"\n" +
	"CREATE TABLE build_tags(\n" +
	"     id INTEGER PRIMARY KEY,\n" +
	"     file_id INT NOT NULL REFERENCES files(id),\n" +
	"     expr TEXT NOT NULL,\n" +
	"     line INT NOT NULL\n" +
	" ) STRICT;\n" +
	" \n" +
	" -- Longest transitive import chain starting at each module, computed in\n" +
	" -- Python (the import graph is a DAG; SQL recursion would re-expand paths).\n" +
	" CREATE TABLE module_depth(\n" +
	"     module_id INT NOT NULL PRIMARY KEY REFERENCES modules(id),\n" +
	"     max_depth INT NOT NULL DEFAULT 0,\n" +
	"     n_direct_imports INT NOT NULL DEFAULT 0,\n" +
	"     n_transitive INT NOT NULL DEFAULT 0\n" +
	" ) WITHOUT ROWID, STRICT;\n" +
	" \n" +
	" -- Longest error-propagation chain starting at each error-returning\n" +
	" -- function, computed in Python: max_depth is the length of the longest\n" +
	" -- path f -> g -> h where every hop's callee RETURNS error. A function\n" +
	" -- whose callees absorb errors terminates a chain at depth 1. Only\n" +
	" -- symbols with n_err_returns > 0 appear.\n" +
	" CREATE TABLE error_chain_depth(\n" +
	"     symbol_id INT NOT NULL PRIMARY KEY REFERENCES symbols(id),\n" +
	"     max_depth INT NOT NULL DEFAULT 0\n" +
	" ) WITHOUT ROWID, STRICT;\n" +
	"\n" +
	" CREATE TABLE user_input_sites(\n" +
	"     id INTEGER PRIMARY KEY,\n" +
	"     symbol_id INT REFERENCES symbols(id),\n" +
	"     file_id INT NOT NULL REFERENCES files(id),\n" +
	"     var TEXT NOT NULL DEFAULT '',\n" +
	"     kind TEXT NOT NULL DEFAULT 'query',\n" +
	"     line INT NOT NULL,\n" +
	"     in_loop INT NOT NULL DEFAULT 0\n" +
	" ) STRICT;\n" +
	"\n" +
	" CREATE TABLE secret_candidates(\n" +
	"     id INTEGER PRIMARY KEY,\n" +
	"     symbol_id INT REFERENCES symbols(id),\n" +
	"     file_id INT NOT NULL REFERENCES files(id),\n" +
	"     value TEXT NOT NULL,\n" +
	"     line INT NOT NULL\n" +
	" ) STRICT;\n" +
	"\n" +
	" -- WaitGroup Add/Done/Wait call sites, per WaitGroup VARIABLE (staticcheck\n" +
	" -- SA2000 family). The Add usually lives in the spawner and the Done in the\n" +
	" -- spawned function, so pairing them is a cross-function fact no per-file\n" +
	" -- checker can see; in_goroutine marks sites lexically inside the `go` body.\n" +
	" CREATE TABLE wg_sites(\n" +
	"     id INTEGER PRIMARY KEY,\n" +
	"     symbol_id INT NOT NULL REFERENCES symbols(id),\n" +
	"     file_id INT NOT NULL REFERENCES files(id),\n" +
	"     line INT NOT NULL,\n" +
	"     var TEXT NOT NULL DEFAULT '',\n" +
	"     op TEXT NOT NULL,\n" +
	"     in_goroutine INT NOT NULL DEFAULT 0,\n" +
	"     in_loop INT NOT NULL DEFAULT 0\n" +
	" ) STRICT;\n" +
	" \n" +
	"\n" +
	"-- Every query in every catalogue filters `f.is_test=0`, and without this\n" +
	"-- SQLite built the index at run time, per query. Measured on go/kubernetes:\n" +
	"-- package-state-concurrent 2.73s -> 0.037s. `files` is small, so the index\n" +
	"-- costs almost nothing to carry.\n" +
	"CREATE INDEX idx_files_test ON files(is_test);\n" +
	"CREATE INDEX idx_files_gen ON files(is_generated);\n" +
	"CREATE INDEX idx_sym_name ON symbols(name);\n" +
	"CREATE INDEX idx_sym_qual ON symbols(qual_name);\n" +
	"CREATE INDEX idx_sym_file_line ON symbols(file_id, line_start);\n" +
	"CREATE INDEX idx_sym_module_kind ON symbols(module_id, kind);\n" +
	"CREATE INDEX idx_sym_parent ON symbols(parent_id) WHERE parent_id IS NOT NULL;\n" +
	"CREATE INDEX idx_sym_kind ON symbols(kind, name);\n" +
	"\n" +
	"CREATE INDEX idx_fn_fanin ON symbols(fan_in DESC, name, file_id, cyclomatic, sloc, fan_out) WHERE kind='function';\n" +
	"CREATE INDEX idx_fn_cyclo ON symbols(cyclomatic DESC, name, file_id, sloc, max_nesting, cognitive) WHERE kind='function';\n" +
	"CREATE INDEX idx_fn_cog ON symbols(cognitive DESC, name, file_id, cyclomatic, max_nesting) WHERE kind='function';\n" +
	"CREATE INDEX idx_fn_risk ON symbols(risk_score DESC, name, file_id, cyclomatic) WHERE kind='function';\n" +
	"CREATE INDEX idx_fn_sloc ON symbols(sloc DESC, name, file_id, cyclomatic) WHERE kind='function';\n" +
	"CREATE INDEX idx_fn_nest ON symbols(max_nesting DESC, name, file_id, cyclomatic) WHERE kind='function';\n" +
	"CREATE INDEX idx_fn_rec ON symbols(cyclomatic DESC, name, file_id) WHERE is_recursive=1;\n" +
	"CREATE INDEX idx_fn_leaf ON symbols(fan_in DESC, name, file_id) WHERE is_leaf=1;\n" +
	"CREATE INDEX idx_fn_public ON symbols(fan_in DESC, name, file_id) WHERE is_public=1;\n" +
	"CREATE INDEX idx_fn_loopdepth ON symbols(max_loop_depth DESC, name, file_id, sloc) WHERE max_loop_depth>1;\n" +
	"CREATE INDEX idx_fn_callinloop ON symbols(call_in_loop DESC, name, file_id) WHERE call_in_loop>0;\n" +
	"CREATE INDEX idx_fn_awaitloop ON symbols(await_in_loop DESC, name, file_id) WHERE await_in_loop>0;\n" +
	"CREATE INDEX idx_fn_allocloop ON symbols(alloc_in_loop DESC, name, file_id) WHERE alloc_in_loop>0;\n" +
	"CREATE INDEX idx_fn_ioloop ON symbols(io_in_loop DESC, name, file_id) WHERE io_in_loop>0;\n" +
	"CREATE INDEX idx_fn_queryloop ON symbols(query_in_loop DESC, name, file_id) WHERE query_in_loop>0;\n" +
	"CREATE INDEX idx_fn_dyn ON symbols(n_dynamic_calls DESC, name, file_id) WHERE n_dynamic_calls>0;\n" +
	"CREATE INDEX idx_fn_unres ON symbols(n_unresolved_calls DESC, name, file_id) WHERE n_unresolved_calls>0;\n" +
	"CREATE INDEX idx_fn_catch ON symbols(n_catch_broad DESC, name, file_id) WHERE n_catch_broad>0;\n" +
	"CREATE INDEX idx_fn_magic ON symbols(n_magic DESC, name, file_id) WHERE n_magic>0;\n" +
	"CREATE INDEX idx_fn_nodoc ON symbols(cyclomatic DESC, name, file_id) WHERE has_doc=0 AND kind='function';\n" +
	"CREATE INDEX idx_fn_async ON symbols(name, file_id) WHERE is_async=1;\n" +
	"CREATE INDEX idx_fn_untested ON symbols(fan_in DESC, name) WHERE is_test=0;\n" +
	"\n" +
	"CREATE INDEX idx_edge_callee ON edges(callee_id, caller_id);\n" +
	"CREATE INDEX idx_edge_xmod ON edges(caller_id) WHERE same_module=0;\n" +
	"CREATE INDEX idx_cs_callee ON callsites(callee_id, line);\n" +
	"CREATE INDEX idx_unres_name ON unresolved_calls(name, n DESC);\n" +
	"\n" +
	"CREATE INDEX idx_haz_cat ON hazards(category, n DESC);\n" +
	"CREATE INDEX idx_haz_pattern ON hazards(pattern, symbol_id);\n" +
	"\n" +
	"CREATE INDEX idx_imp_target ON imports(target);\n" +
	"CREATE INDEX idx_imp_file ON imports(file_id, target);\n" +
	"CREATE INDEX idx_imp_resolved ON imports(target_id) WHERE target_id IS NOT NULL;\n" +
	"CREATE INDEX idx_imp_external ON imports(target) WHERE is_external=1;\n" +
	"CREATE INDEX idx_imp_intra ON imports(file_id) WHERE is_external=0;\n" +
	"\n" +
	"CREATE INDEX idx_params_sym ON params(symbol_id, pos);\n" +
	"CREATE INDEX idx_params_type ON params(type);\n" +
	"CREATE INDEX idx_params_untyped ON params(symbol_id) WHERE is_untyped=1;\n" +
	"CREATE INDEX idx_fields_sym ON fields(symbol_id, ordinal);\n" +
	"CREATE INDEX idx_fields_type ON fields(type);\n" +
	"CREATE INDEX idx_locals_sym ON locals(symbol_id, ordinal);\n" +
	"CREATE INDEX idx_lit_val ON literals(value, file_id) WHERE is_magic=1;\n" +
	"CREATE INDEX idx_lit_sym ON literals(symbol_id, kind);\n" +
	"CREATE INDEX idx_attr_sym ON attributes(symbol_id, name);\n" +
	"CREATE INDEX idx_attr_name ON attributes(name);\n" +
	"CREATE INDEX idx_mark_kind ON markers(kind, file_id);\n" +
	"CREATE INDEX idx_enum_sym ON enum_members(symbol_id, ordinal);\n" +
	"\n" +
	"CREATE INDEX idx_files_module ON files(module_id, sloc DESC);\n" +
	"CREATE INDEX idx_files_lang ON files(lang, sloc DESC);\n" +
	"CREATE INDEX idx_files_err ON files(n_parse_errors DESC) WHERE n_parse_errors>0;\n" +
	"CREATE INDEX idx_files_risk ON files(total_risk DESC, path);\n" +
	"\n" +
	"\n" +
	"-- parse-coverage joins build_tags by file; the planner was building this.\n" +
	"CREATE INDEX idx_buildtags_file ON build_tags(file_id);\n" +
	"CREATE INDEX idx_gor_sym ON goroutines(symbol_id);\n" +
	"CREATE INDEX idx_gor_leak ON goroutines(symbol_id)\n" +
	"    WHERE has_ctx=0 AND has_waitgroup=0 AND has_errgroup=0;\n" +
	"CREATE INDEX idx_def_loop ON defers(symbol_id) WHERE in_loop=1;\n" +
	"CREATE INDEX idx_chan_unbuf ON channels(symbol_id) WHERE capacity=0;\n" +
	"CREATE INDEX idx_iface_exp ON interfaces(is_exported, n_methods);\n" +
	"CREATE INDEX idx_impl_iface ON implements(interface_id, in_test);\n" +
	"CREATE INDEX idx_struct_mutex ON structs(symbol_id) WHERE has_mutex=1;\n" +
	"CREATE INDEX idx_fn_handler ON symbols(name, file_id) WHERE is_handler=1;\n" +
	"CREATE INDEX idx_fn_ctxbg ON symbols(n_ctx_background DESC, name)\n" +
	"    WHERE n_ctx_background>0;\n" +
	"CREATE INDEX idx_fn_errign ON symbols(n_err_ignored DESC, name)\n" +
	"    WHERE n_err_ignored>0;\n" +
	"CREATE INDEX idx_errchain ON error_chain_depth(max_depth DESC)\n" +
	"    WHERE max_depth > 1;\n" +
	"CREATE INDEX idx_uinput_sym ON user_input_sites(symbol_id, kind);\n" +
	"CREATE INDEX idx_uinput_kind ON user_input_sites(kind, line) WHERE in_loop=1;\n" +
	"CREATE INDEX idx_secret_sym ON secret_candidates(symbol_id);\n" +
	"CREATE INDEX idx_wg_sym ON wg_sites(symbol_id, op);\n" +
	"\n" +
	"\n" +
	"CREATE VIEW v_fn AS\n" +
	"SELECT s.id, s.name, s.qual_name, f.path, m.name AS module, s.line_start,\n" +
	"    s.line_end, s.sloc, s.cyclomatic, s.cognitive, s.max_nesting,\n" +
	"    s.fan_in, s.fan_out, s.n_calls, s.n_unresolved_calls, s.is_recursive,\n" +
	"    s.is_public, s.is_async, s.is_test, s.has_doc, s.n_params,\n" +
	"    s.max_loop_depth, s.call_in_loop, s.n_hazards, s.risk_score,\n" +
	"    f.is_test AS in_test_file, f.is_generated AS in_generated_file,\n" +
	"    f.path || ':' || s.line_start AS at\n" +
	"FROM symbols s\n" +
	"JOIN files f ON f.id = s.file_id\n" +
	"LEFT JOIN modules m ON m.id = s.module_id\n" +
	"WHERE s.kind IN ('function','method','constructor','closure');\n" +
	"\n" +
	"CREATE VIEW v_type AS\n" +
	"SELECT s.id, s.name, s.qual_name, s.kind, f.path, m.name AS module,\n" +
	"    s.line_start, s.n_lines, s.is_public, s.visibility,\n" +
	"    (SELECT COUNT(*) FROM fields fl WHERE fl.symbol_id=s.id) AS n_fields,\n" +
	"    (SELECT COUNT(*) FROM symbols c WHERE c.parent_id=s.id) AS n_members,\n" +
	"    f.path || ':' || s.line_start AS at\n" +
	"FROM symbols s\n" +
	"JOIN files f ON f.id = s.file_id\n" +
	"LEFT JOIN modules m ON m.id = s.module_id\n" +
	"WHERE s.kind IN ('class','struct','interface','trait','enum','union','record',\n" +
	"                 'protocol','type','module','impl','object','mixin');\n" +
	"\n" +
	"CREATE VIEW v_hotspot AS\n" +
	"SELECT *, (cyclomatic*2 + cognitive + max_nesting*5 + call_in_loop*4\n" +
	"    + n_hazards*6 + fan_in) AS heat\n" +
	"FROM v_fn\n" +
	"WHERE in_generated_file = 0\n" +
	"ORDER BY heat DESC;\n" +
	"\n" +
	"CREATE VIEW v_blindspot AS\n" +
	"SELECT name, path, module, n_calls, n_unresolved_calls, fan_out,\n" +
	"    CAST(100.0 * n_unresolved_calls / NULLIF(n_calls,0) AS INT) AS pct_blind, at\n" +
	"FROM v_fn\n" +
	"WHERE n_unresolved_calls > 0\n" +
	"ORDER BY n_unresolved_calls DESC;\n" +
	"\n" +
	"CREATE VIEW v_untested AS\n" +
	"SELECT * FROM v_fn\n" +
	"WHERE in_test_file = 0 AND is_test = 0 AND in_generated_file = 0\n" +
	"  AND id NOT IN (\n" +
	"    SELECT e.callee_id FROM edges e\n" +
	"    JOIN symbols cs ON cs.id = e.caller_id\n" +
	"    JOIN files cf ON cf.id = cs.file_id\n" +
	"    WHERE cf.is_test = 1 OR cs.is_test = 1);\n" +
	"\n" +
	"\n" +
	"CREATE VIEW v_goroutine AS\n" +
	"SELECT g.id, s.name AS in_fn, s.qual_name, f.path, g.line, g.is_closure,\n" +
	"    g.has_ctx, g.has_recover, g.has_waitgroup, g.has_errgroup,\n" +
	"    g.in_loop, g.loop_depth, s.is_handler, s.n_ctx_params,\n" +
	"    f.path || ':' || g.line AS at\n" +
	"FROM goroutines g\n" +
	"JOIN symbols s ON s.id=g.symbol_id\n" +
	"JOIN files f ON f.id=g.file_id;\n" +
	"\n" +
	"CREATE VIEW v_iface_impls AS\n" +
	"SELECT i.symbol_id AS iface_id, s.name AS iface, i.n_methods,\n" +
	"    i.is_exported, i.is_constraint,\n" +
	"    (SELECT COUNT(*) FROM params p WHERE substr(p.type, -length(s.name)) = s.name\n" +
	"           AND (length(p.type) = length(s.name)\n" +
	"                OR instr('abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_', substr(p.type, -length(s.name)-1, 1)) = 0)) AS used_as_param\n" +
	"FROM interfaces i JOIN symbols s ON s.id=i.symbol_id;\n" +
	"\n"

func main() {
	peakWatch()
	mutexBlockWatch()
	var (
		which       numList
		module      = flag.String("module", "%", "module-name LIKE filter")
		limit       = flag.Int("limit", -1, "rows per query; -1 (default) is every row")
		list        = flag.Bool("list", false, "list the queries")
		metrics     = flag.Bool("metrics", false, "run/list the METRICS section instead of QUERIES")
		schemaF     = flag.Bool("schema", false, "dump the schema")
		report      = flag.Bool("report", false, "narrative overview")
		savePath    = flag.String("save", "", "also write the graph to a file")
		forceF      = flag.Bool("force", false, "allow --save to overwrite an existing file")
		saveASTPath = flag.String("save-ast", "", "parse/build, then write the binary graph state to PATH")
		loadASTPath = flag.String("load-ast", "", "load a saved graph state instead of parsing")
		installDeps = flag.Bool("install-deps", false, "install the missing dependencies, then continue")
		dumpPath    = flag.String("dump", "", "write the canonical graph dump to PATH")
		incGen      = flag.Bool("include-generated", false, "parse generated files too (off by default)")
		incVend     = flag.Bool("include-vendored", false, "parse vendored trees too (off by default)")
		noTests     = flag.Bool("no-tests", false, "skip test files")
		quiet       = flag.Bool("quiet", false, "suppress progress output")
		version     = flag.Bool("version", false, "print version and exit")
		deps        = flag.Bool("deps", false, "show dependencies and how to install them")
		cpuprofile  = flag.String("cpuprofile", "", "write a CPU profile to PATH")
		memprofile  = flag.String("memprofile", "", "write a heap profile to PATH")
		probe       = flag.Bool("probe-tree", false, "print the parse tree (development aid)")
		probeWalk   = flag.Bool("probe-walk", false, "print the measuring-pass walk order (development aid)")
	)
	flag.Var(&which, "query", "1-based query numbers (repeatable)")
	var csvQ, jsonQ qNum
	flag.Var(&csvQ, "csv", "emit query N as CSV")
	flag.Var(&jsonQ, "json", "emit query N as JSON")

	flag.CommandLine.Parse(reorderArgs(os.Args[1:], flag.CommandLine))
	if *probe {
		os.Exit(runProbe(flag.Args()))
	}
	if *probeWalk {
		os.Exit(runWalk(flag.Args()))
	}
	if *version {
		fmt.Printf("codegraph-go  target=Go 1.26  schema=v1  go=%s\n", runtime.Version())
		return
	}
	if *installDeps {
		if !*quiet {
			fmt.Println("all dependencies already present")
		}
		if *deps {
			fmt.Println()
			printDeps()
			return
		}
	} else if *deps {
		printDeps()
		return
	}
	if *schemaF {
		fmt.Print(oracleSchemaDDL)
		return
	}
	cat := allQueries
	if *metrics {
		cat = allMetrics
	}
	if *list {
		for i, q := range cat {
			fmt.Printf("%2d. %-26s %s\n", i+1, q.name, q.title)
		}
		return
	}

	if csvQ.set || jsonQ.set {
		*quiet = true
	}
	if *saveASTPath != "" && *loadASTPath != "" {
		fmt.Fprintln(os.Stderr, "--save-ast and --load-ast cannot be used together")
		os.Exit(2)
	}
	root := flag.Arg(0)
	if root == "" {
		root = "."
	}
	if *loadASTPath == "" {
		if fi, err := os.Stat(root); err != nil || !fi.IsDir() {
			fmt.Fprintf(os.Stderr, "not a directory: %s\n", root)
			os.Exit(2)
		}
	}
	if *cpuprofile != "" {
		f, err := os.Create(*cpuprofile)
		if err == nil {
			startCPU(f)
			defer stopCPU()
		}
	}
	t0 := time.Now()
	var g *Graph
	var nParsed int
	if *loadASTPath != "" {
		var lerr error
		g, lerr = loadAST(*loadASTPath)
		if lerr != nil {
			fmt.Fprintf(os.Stderr, "load-ast: %v\n", lerr)
			os.Exit(2)
		}
		nParsed = len(g.File)
		if v, ok := g.Meta["files_parsed"]; ok {
			if nv, aerr := strconv.Atoi(v); aerr == nil {
				nParsed = nv
			}
		}
	} else {
		g, nParsed = buildGraph(root, *noTests, *incGen, *incVend, *quiet)
	}
	took := time.Since(t0)
	if *saveASTPath != "" {
		if _, serr := os.Lstat(*saveASTPath); serr == nil && !*forceF {
			fmt.Fprintf(os.Stderr, "refusing to overwrite %s (pass --force)\n", *saveASTPath)
			os.Exit(2)
		}
		ts := time.Now()
		nb, werr := saveASTFile(g, *saveASTPath)
		if werr != nil {
			fmt.Fprintf(os.Stderr, "save-ast: %v\n", werr)
			os.Exit(2)
		}
		if !*quiet {
			fmt.Fprintf(os.Stderr, "ast state written to %s: %d bytes in %.1fs\n",
				*saveASTPath, nb, time.Since(ts).Seconds())
		}
	}
	if *dumpPath != "" {
		if err := writeDump(*dumpPath, g); err != nil {
			fmt.Fprintf(os.Stderr, "could not write %s: %s\n", *dumpPath, err)
			os.Exit(2)
		}
	}
	if *memprofile != "" {
		if f, err := os.Create(*memprofile); err == nil {
			writeHeap(f)
			f.Close()
		}
	}
	w := bufio.NewWriterSize(os.Stdout, 1<<16)
	defer w.Flush()
	if csvQ.set || jsonQ.set {

		n := jsonQ.n
		if csvQ.set {
			n = csvQ.n
		}
		if n < 1 || n > len(cat) {
			fmt.Fprintf(os.Stderr, "no query %d\n", n)
			os.Exit(2)
		}
		r := cat[n-1].run(g, *module, *limit)
		if csvQ.set {
			writeCSV(w, r)
		} else {
			writeJSON(w, r)
		}
		return
	}
	if !*quiet {
		if *loadASTPath != "" {
			fmt.Fprintf(w, "codegraph-go: %d files loaded from AST state in %.1fs module=%s limit=%s\n",
				nParsed, took.Seconds(), *module, limText(*limit))
		} else {
			fmt.Fprintf(w, "codegraph-go: %d files parsed into memory in %.1fs module=%s limit=%s\n",
				nParsed, took.Seconds(), *module, limText(*limit))
		}
	}
	if *report {
		renderReport(w, g)
	}
	sel := which.nums

	for _, a := range flag.Args()[min(1, flag.NArg()):] {
		if n, err := strconv.Atoi(a); err == nil {
			sel = append(sel, n)
		}
	}
	if len(sel) == 0 {
		sel = make([]int, len(cat))
		for i := range cat {
			sel[i] = i + 1
		}
	}
	for _, k := range sel {
		if k < 1 || k > len(cat) {
			continue
		}
		q := cat[k-1]
		markPhase(fmt.Sprintf("q%03d-%s", k, q.name))
		fmt.Fprintf(w, "\n%s\n", strings.Repeat("=", 78))
		fmt.Fprintf(w, "Q%d. %s -- %s\n", k, q.name, q.title)
		fmt.Fprintf(w, "%s\n", strings.Repeat("-", 78))
		for line := range strings.SplitSeq(q.notes, "\n") {
			fmt.Fprintf(w, " %s\n", line)
		}
		fmt.Fprintln(w)
		render(w, q.run(g, *module, *limit))
	}
	if *savePath != "" {
		if _, err := os.Lstat(*savePath); err == nil && !*forceF {
			msg := "\nrefusing to overwrite " + *savePath + " (pass --force)"
			if li, lerr := os.Lstat(*savePath); lerr == nil && li.Mode()&os.ModeSymlink != 0 {
				real, _ := filepath.EvalSymlinks(*savePath)
				if real == "" {
					if d, derr := filepath.EvalSymlinks(filepath.Dir(*savePath)); derr == nil {
						real = filepath.Join(d, filepath.Base(*savePath))
					}
				}
				msg += " -- it is a symlink to " + real
			}
			fmt.Fprintln(os.Stderr, msg)
			w.Flush()
			return
		}
		if li, lerr := os.Lstat(*savePath); lerr == nil && li.Mode()&os.ModeSymlink != 0 {
			os.Remove(*savePath)
		}
		if err := writeDump(*savePath, g); err != nil {
			fmt.Fprintln(os.Stderr, "\ncould not write "+*savePath+": "+err.Error())
		} else {
			fmt.Fprintf(w, "\n(graph also written to %s)\n", *savePath)
		}
	}
	heapAt("render")
	writeMutexBlock()
}

func printDeps() {
	fmt.Println("dependencies: none.")
	fmt.Println("The parser is the standard library's go/parser and go/scanner, so there")
	fmt.Println("is nothing to install and no grammar for a missing one to hide behind.")
}

func reorderArgs(args []string, fs *flag.FlagSet) []string {
	var flags, pos []string
	for i := 0; i < len(args); i++ {
		a := args[i]

		if len(a) > 1 && a[0] == '-' && !isNegNumber(a) {
			flags = append(flags, a)
			if i+1 < len(args) && !strings.Contains(a, "=") {
				name := strings.TrimLeft(a, "-")
				if f := fs.Lookup(name); f != nil {
					if bf, ok := f.Value.(interface{ IsBoolFlag() bool }); !ok || !bf.IsBoolFlag() {
						i++
						flags = append(flags, args[i])
					}
				}
			}
			continue
		}
		pos = append(pos, a)
	}
	return append(flags, pos...)
}

func isNegNumber(a string) bool {
	if len(a) < 2 || a[0] != '-' {
		return false
	}
	digits, dot := 0, false
	for _, c := range a[1:] {
		switch {
		case c >= '0' && c <= '9':
			digits++
		case c == '.' && !dot:
			dot = true
		default:
			return false
		}
	}
	if !dot {
		return digits >= 1
	}
	last := a[len(a)-1]
	return last >= '0' && last <= '9'
}

func limText(l int) string {
	if l < 0 {
		return "all"
	}
	return fmt.Sprintf("%d", l)
}

func buildGraph(root string, noTests, incGen, incVend, quiet bool) (*Graph, int) {
	g := NewGraph()
	abs, _ := filepath.Abs(root)
	g.ParseMode = "native-ast"
	g.Parser = "parser: go/parser + go/scanner " + runtime.Version()
	g.Meta["schema_version"] = "1"
	g.Meta["lang"] = "go"
	g.Meta["target"] = "Go 1.26"
	g.Meta["root"] = abs
	g.Meta["parse_mode"] = g.ParseMode
	g.Meta["parser"] = g.Parser
	g.Meta["sqlite"] = "n/a (no SQL)"

	recs, st := discover(g, root, !noTests, incGen, incVend)
	markPhase("discover")
	if !quiet {
		if st.big > 0 {
			fmt.Printf("  %d too large or with a pathologically long line -- catalogued, not parsed\n", st.big)
		}
		if st.special > 0 {
			fmt.Printf("  %d not regular files (fifo, socket, device) -- skipped\n", st.special)
		}
		if st.escape > 0 {
			fmt.Printf("  %d symlinks pointing OUTSIDE the tree -- skipped\n", st.escape)
		}
		if st.denied > 0 {
			fmt.Printf("  %d unreadable (permission denied)\n", st.denied)
		}
		if st.walkErr > 0 {
			fmt.Printf("  %d director(ies) could not be listed\n", st.walkErr)
		}
		fmt.Printf("  %d go files discovered\n", len(recs))
	}

	workers := *parseWorkers
	if workers <= 0 {
		workers = defaultParseWorkers
	}
	if *parseGC >= 0 {
		debug.SetGCPercent(*parseGC)
	}
	nErr := extractAll(g, recs, workers)
	markPhase("extracted")
	debug.SetGCPercent(100)
	g.Str.buildStrings()

	nParsed := len(recs)
	recs = nil
	g.Meta["files_parsed"] = fmt.Sprintf("%d", nParsed)
	g.Meta["files_failed"] = fmt.Sprintf("%d", nErr)

	g.Meta["parse_diagnostics"] = fmt.Sprintf(
		"n_parse_errors = go/parser syntax errors (%d files affected); "+
			"n_missing_nodes is always 0 -- it counts tree-sitter recovery nodes, "+
			"which go/parser does not produce",
		errFileCount(g))
	if !quiet {
		fmt.Printf("  %d symbols parsed\n", g.Sym.n)
	}
	if nErr > 0 {
		fmt.Fprintf(os.Stderr, "  WARNING: %d of %d file(s) FAILED to parse and contributed nothing.\n", nErr, nParsed)
	}

	loopvarFixed := true
	if data, err := os.ReadFile(filepath.Join(root, "go.mod")); err == nil {
		txt := string(data)
		if m := reGomodGo.FindStringSubmatch(txt); m != nil {
			maj, _ := atoi(m[1])
			min, _ := atoi(m[2])
			g.Meta["go_version"] = m[1] + "." + m[2]
			loopvarFixed = maj > 1 || (maj == 1 && min >= 22)
		}
		if m := reGomodModule.FindStringSubmatch(txt); m != nil {
			g.Meta["module"] = m[1]
		}
		if loopvarFixed {
			g.Meta["loopvar_per_iteration"] = "yes (go>=1.22)"
		} else {
			g.Meta["loopvar_per_iteration"] = "NO -- capture bugs are real in this module"
		}
	}

	resolveCalls(g)
	markPhase("resolve")
	g.Meta["calls_resolved"] = fmt.Sprintf("%d in-tree / %d external / %d unresolved (%d%% of in-scope resolved)",
		g.nResolved, g.nExternal, g.nUnresolvd,
		100*g.nResolved/maxI32(1, g.nResolved+g.nUnresolvd))
	resolveImportTargets(g)
	interfaceSatisfaction(g)
	moduleDepth(g)
	errorChainDepth(g)
	g.buildCSRs()
	markPhase("csr")
	materialize(g)
	markPhase("materialize")
	g.Meta["implements_pairs"] = fmt.Sprintf("%d", len(g.Impl))
	g.Meta["files_skipped"] = fmt.Sprintf("big=%d special=%d escaping_symlink=%d denied=%d walk_errors=%d",
		st.big, st.special, st.escape, st.denied, st.walkErr)
	return g, nParsed
}

func maxI32(a, b int32) int32 {
	if a > b {
		return a
	}
	return b
}

func renderReport(w *bufio.Writer, g *Graph) {
	g.Meta["built_at"] = nowStamp()
	fmt.Fprintf(w, "\n%s\n", strings.Repeat("=", 78))
	fmt.Fprintln(w, "OVERVIEW")
	fmt.Fprintln(w, strings.Repeat("-", 78))
	for _, k := range []string{"lang", "target", "parser", "root", "built_at"} {
		if g.Meta[k] != "" {
			fmt.Fprintf(w, " %-14s %s\n", k, g.Meta[k])
		}
	}
	files := len(g.File)
	parsed, sloc := 0, int32(0)
	for i := range g.File {
		if g.File[i].Parsed != 0 {
			parsed++
			sloc += g.File[i].Sloc
		}
	}
	fmt.Fprintf(w, " %-14s %d catalogued, %d parsed, %d sloc\n", "files", files, parsed, sloc)
	kindCount := map[string]int{}
	for i := 0; i < g.Sym.n; i++ {
		kindCount[g.Str.get(g.Sym.Kind[i])]++
	}
	type kc struct {
		k string
		n int
	}
	var ks []kc
	for k, v := range kindCount {
		ks = append(ks, kc{k, v})
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
	var kb strings.Builder
	for i, e := range ks {
		if i > 0 {
			kb.WriteString(", ")
		}
		fmt.Fprintf(&kb, "%s=%d", e.k, e.n)
	}
	fmt.Fprintf(w, " %-14s %s\n", "symbols", kb.String())
	var totCalls int32
	for i := 0; i < g.Sym.n; i++ {
		totCalls += g.Sym.NCalls[i]
	}
	fmt.Fprintf(w, " %-14s %d edges, %d call sites, %d unresolved\n", "call graph",
		len(g.edgeList), len(g.csList), g.nUnresolvd)

	fmt.Fprintf(w, "\n%s\n", strings.Repeat("=", 78))
	fmt.Fprintln(w, "HOW MUCH OF THIS TO TRUST")
	fmt.Fprintln(w, strings.Repeat("-", 78))
	errFiles := 0
	for i := range g.File {
		if g.File[i].NParsErr > 0 {
			errFiles++
		}
	}
	if parsed == 0 {
		fmt.Fprintln(w, " NOTHING WAS PARSED. Every number below is zero because no file")
		fmt.Fprintln(w, " was read, not because this repository is empty or clean.")
	}
	fmt.Fprintf(w, " %-30s %d file(s)\n", "files with parse errors", errFiles)

	fmt.Fprintln(w, " n_parse_errors is go/parser's own syntax-error count, not the")
	fmt.Fprintln(w, " reference's tree-sitter ERROR-node count; the two parsers")
	fmt.Fprintln(w, " disagree on files only one of them can read.")
	fmt.Fprintln(w, " n_missing_nodes is always 0 here: it counts tree-sitter")
	fmt.Fprintln(w, " recovery nodes, and go/parser has no equivalent. A zero in")
	fmt.Fprintln(w, " that column is not a clean bill of health.")
	if totCalls > 0 {
		fmt.Fprintf(w, " %-30s %d of %d call sites (%d%%)\n", "calls we could NOT resolve",
			g.nUnresolvd, totCalls, 100*g.nUnresolvd/totCalls)
	} else {
		fmt.Fprintf(w, " %-30s no calls were recorded at all -- this is the absence of\n", "")
		fmt.Fprintf(w, " %-30s call resolution\n", "")
		fmt.Fprintf(w, " %-30s data, not a clean result\n", "")
	}
	fmt.Fprintln(w, " A high unresolved share means the call-graph queries below see less")
	fmt.Fprintln(w, " than they imply. `v_blindspot` lists exactly where.")

	for _, sec := range reportSections(g) {
		fmt.Fprintf(w, "\n%s\n", strings.Repeat("=", 78))
		fmt.Fprintln(w, sec.title)
		fmt.Fprintln(w, strings.Repeat("-", 78))
		render(w, sec.r)
	}
}

const reportCap = 12

type reportSection struct {
	title string
	r     result
}

func reportSections(g *Graph) []reportSection {
	return []reportSection{
		{"BIGGEST MODULES", biggestModules(g)},
		{"HEAVIEST FUNCTIONS", heaviestFunctions(g)},
		{"MOST DEPENDED ON", mostDependedOn(g)},
		{"MARKERS LEFT IN THE CODE", markerCounts(g)},
	}
}

func biggestModules(g *Graph) result {
	r := result{cols: []string{"name", "files", "sloc", "syms", "instab"},
		lim: reportCap}
	for i := range g.Mod {
		m := &g.Mod[i]
		if m.NFiles == 0 {
			continue
		}
		r.rows = append(r.rows, []cellVal{cs(m.Name), ci(int64(m.NFiles)),
			ci(int64(m.Sloc)), ci(int64(m.NSyms)), cf(m.Instab)})
	}
	return sortRows(r, 2)
}

func heaviestFunctions(g *Graph) result {
	r := result{cols: []string{"name", "sloc", "cyclo", "cog", "nest", "fan_in", "at"},
		lim: reportCap}
	for _, i := range g.fnSyms("%", false) {
		r.rows = append(r.rows, []cellVal{cs(g.Str.get(g.Sym.Name[i])),
			ci(int64(g.Sym.Sloc[i])), ci(int64(g.Sym.Cyclomatic[i])),
			ci(int64(g.Sym.Cognitive[i])), ci(int64(g.Sym.MaxNesting[i])),
			ci(int64(g.Sym.FanIn[i])), cs(g.at(i))})
	}
	return sortRows(r, 2)
}

func mostDependedOn(g *Graph) result {
	r := result{cols: []string{"name", "fan_in", "fan_out", "cyclo", "sloc", "at"},
		lim: reportCap}
	for _, i := range g.fnSyms("%", false) {
		r.rows = append(r.rows, []cellVal{cs(g.Str.get(g.Sym.Name[i])),
			ci(int64(g.Sym.FanIn[i])), ci(int64(g.Sym.FanOut[i])),
			ci(int64(g.Sym.Cyclomatic[i])), ci(int64(g.Sym.Sloc[i])), cs(g.at(i))})
	}
	return sortRows(r, 1)
}

func markerCounts(g *Graph) result {
	cnt := map[string]int{}
	for _, m := range g.Markers {
		cnt[g.Str.get(m.Kind)]++
	}
	keys := make([]string, 0, len(cnt))
	for k := range cnt {
		keys = append(keys, k)
	}
	sort.Slice(keys, func(a, b int) bool {
		if cnt[keys[a]] != cnt[keys[b]] {
			return cnt[keys[a]] > cnt[keys[b]]
		}
		return keys[a] < keys[b]
	})
	r := result{cols: []string{"kind", "n"}}
	for _, k := range keys {
		r.rows = append(r.rows, []cellVal{cs(k), ci(int64(cnt[k]))})
	}
	return r
}

const cgasMagic = "CGAS"

const (
	cgasVersion  = 1
	cgasHeaderSz = 32
	cgasSecSz    = 24
	cgasNSec     = 33
)

const (
	cgasSecStrings uint32 = 1 + iota
	cgasSecSyms
	cgasSecFiles
	cgasSecMods
	cgasSecIDir
	cgasSecSPos
	cgasSecSLn
	cgasSecSBuf
	cgasSecParams
	cgasSecParamSym
	cgasSecFields
	cgasSecFieldSym
	cgasSecHazards
	cgasSecImports
	cgasSecLiterals
	cgasSecMarkers
	cgasSecGoro
	cgasSecDefers
	cgasSecChans
	cgasSecIfaces
	cgasSecStructs
	cgasSecWgSites
	cgasSecUInputs
	cgasSecSecrets
	cgasSecImpls
	cgasSecBuildTags
	cgasSecErrChain
	cgasSecEdges
	cgasSecUnres
	cgasSecSites
	cgasSecMeta
	cgasSecExtByCall
	cgasSecStats
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

type cgasMetaRow struct {
	K, V string
}

type cgasExtKV struct{ K, V int32 }

var fileStrOffs = []uintptr{
	unsafe.Offsetof(File{}.Path),
	unsafe.Offsetof(File{}.Dir),
	unsafe.Offsetof(File{}.Basename),
	unsafe.Offsetof(File{}.Ext),
	unsafe.Offsetof(File{}.SHA1),
}

var moduleStrOffs = []uintptr{
	unsafe.Offsetof(Module{}.Name),
	unsafe.Offsetof(Module{}.Kind),
}

var metaStrOffs = []uintptr{
	unsafe.Offsetof(cgasMetaRow{}.K),
	unsafe.Offsetof(cgasMetaRow{}.V),
}

func cgasUint32Offs[T any]() []uintptr {
	t := reflect.TypeFor[T]()
	var out []uintptr
	for i := 0; i < t.NumField(); i++ {
		if t.Field(i).Type.Kind() == reflect.Uint32 {
			out = append(out, t.Field(i).Offset)
		}
	}
	return out
}

var (
	paramIDOffs     = cgasUint32Offs[Param]()
	fieldIDOffs     = cgasUint32Offs[Field]()
	hazardIDOffs    = cgasUint32Offs[Hazard]()
	importIDOffs    = cgasUint32Offs[Import]()
	literalIDOffs   = cgasUint32Offs[Literal]()
	markerIDOffs    = cgasUint32Offs[Marker]()
	goroIDOffs      = cgasUint32Offs[Goro]()
	deferIDOffs     = cgasUint32Offs[Defer]()
	chanIDOffs      = cgasUint32Offs[Chan]()
	ifaceIDOffs     = cgasUint32Offs[Iface]()
	wgIDOffs        = cgasUint32Offs[WgSite]()
	uinputIDOffs    = cgasUint32Offs[UInput]()
	secretIDOffs    = cgasUint32Offs[Secret]()
	implIDOffs      = cgasUint32Offs[Impl]()
	buildTagIDOffs  = cgasUint32Offs[BuildTag]()
	unresIDOffs     = cgasUint32Offs[Unres]()
	cgasSymColKinds = func() []reflect.Kind {
		t := reflect.TypeFor[Syms]()
		out := make([]reflect.Kind, len(symSliceFields))
		for i, f := range symSliceFields {
			out[i] = t.Field(f).Type.Elem().Kind()
		}
		return out
	}()
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
	fail(unsafe.Sizeof("") == 16, "string must be 16 bytes")
	g := "cgas-layout-guard"
	h := *(*[2]uintptr)(unsafe.Pointer(&g))
	fail(h[1] == uintptr(len(g)) &&
		h[0] == uintptr(unsafe.Pointer(unsafe.StringData(g))), "string header word order")
	fail(unsafe.Sizeof(cgasHeader{}) == cgasHeaderSz, "cgasHeader must be 32 bytes")
	fail(unsafe.Sizeof(cgasSec{}) == cgasSecSz, "cgasSec must be 24 bytes")
	fail(unsafe.Sizeof(cgasSRef{}) == 16, "cgasSRef must overlay a string header")
	fail(unsafe.Sizeof(cgasMetaRow{}) == 32, "cgasMetaRow must be two string headers")
	for _, t := range []reflect.Type{
		reflect.TypeOf(Param{}),
		reflect.TypeOf(Field{}),
		reflect.TypeOf(Hazard{}),
		reflect.TypeOf(Import{}),
		reflect.TypeOf(Literal{}),
		reflect.TypeOf(Marker{}),
		reflect.TypeOf(Goro{}),
		reflect.TypeOf(Defer{}),
		reflect.TypeOf(Chan{}),
		reflect.TypeOf(Iface{}),
		reflect.TypeOf(Struct{}),
		reflect.TypeOf(WgSite{}),
		reflect.TypeOf(UInput{}),
		reflect.TypeOf(Secret{}),
		reflect.TypeOf(Impl{}),
		reflect.TypeOf(BuildTag{}),
		reflect.TypeOf(rawEdge{}),
		reflect.TypeOf(Unres{}),
		reflect.TypeOf(Callsite{}),
		reflect.TypeOf(ErrChain{}),
		reflect.TypeOf(cgasExtKV{}),
		reflect.TypeOf(cgasSRef{}),
		reflect.TypeOf(int32(0)),
		reflect.TypeOf(uint32(0)),
	} {
		fail(!cgasHasRef(t), t.String()+" must be pointer-free")
	}
	fail(len(cgasSymColKinds) == len(symSliceFields), "symbol column kinds table is stale")
	for _, k := range cgasSymColKinds {
		fail(k == reflect.Int32 || k == reflect.Uint32, "symbol columns must be []int32 or []uint32")
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

func cgPutU32(b []byte, o int, v uint32) { *(*uint32)(unsafe.Pointer(&b[o])) = v }
func cgPutU64(b []byte, o int, v uint64) { *(*uint64)(unsafe.Pointer(&b[o])) = v }

func cgGetU32(b []byte, o int) uint32 { return *(*uint32)(unsafe.Pointer(&b[o])) }
func cgGetU64(b []byte, o int) uint64 { return *(*uint64)(unsafe.Pointer(&b[o])) }

func cgasAlign8(v uint64) uint64 { return (v + 7) &^ 7 }

type cgasTab struct {
	it   *Interner
	tbl  [internerShards][]uint32
	src  [internerShards][]uint32
	offs [internerShards][]uint32
	lens [internerShards][]uint32
	cur  [internerShards]uint32
	nstr int
}

func cgasNewTab(it *Interner) *cgasTab {
	t := &cgasTab{it: it}
	for sh := 0; sh < internerShards; sh++ {
		n := len(it.shards[sh].ln)
		if n == 0 {
			continue
		}
		t.tbl[sh] = make([]uint32, n)
		for i := range t.tbl[sh] {
			t.tbl[sh][i] = nullStr
		}
	}
	return t
}

func (t *cgasTab) mapID(id uint32) uint32 {
	if id == nullStr {
		return id
	}
	sh := id >> (32 - internerShardBits)
	local := id & (1<<(32-internerShardBits) - 1)
	if int(local) >= len(t.tbl[sh]) {
		panic("cgas: interner id exceeds its shard")
	}
	if nid := t.tbl[sh][local]; nid != nullStr {
		return nid
	}
	c := &t.it.shards[sh]
	c.mu.RLock()
	l := c.ln[local]
	c.mu.RUnlock()
	nlocal := uint32(len(t.offs[sh]))
	if nlocal >= 1<<(32-internerShardBits)-1 {
		panic("cgas: string shard overflow")
	}
	nid := sh<<(32-internerShardBits) | nlocal
	t.tbl[sh][local] = nid
	t.src[sh] = append(t.src[sh], id)
	t.offs[sh] = append(t.offs[sh], t.cur[sh])
	t.lens[sh] = append(t.lens[sh], l)
	t.cur[sh] += l
	t.nstr++
	return nid
}

func (t *cgasTab) lookup(id uint32) uint32 {
	if id == nullStr {
		return id
	}
	sh := id >> (32 - internerShardBits)
	local := id & (1<<(32-internerShardBits) - 1)
	if int(local) >= len(t.tbl[sh]) {
		panic("cgas: interner id exceeds its shard")
	}
	nid := t.tbl[sh][local]
	if nid == nullStr {
		panic("cgas: string id was not planned for save")
	}
	return nid
}

func (t *cgasTab) idir() []byte {
	b := make([]byte, 4+16*internerShards)
	cgPutU32(b, 0, internerShards)
	for sh := range internerShards {
		cgPutU64(b, 4+16*sh, uint64(t.cur[sh]))
		cgPutU64(b, 4+16*sh+8, uint64(len(t.offs[sh])))
	}
	return b
}

func (t *cgasTab) bufBytes() uint64 {
	var n uint64
	for sh := range internerShards {
		n += uint64(t.cur[sh])
	}
	return n
}

func (t *cgasTab) writeOffs(w *bufio.Writer) error {
	for sh := range internerShards {
		c := t.offs[sh]
		if len(c) > 0 {
			if _, err := w.Write(unsafe.Slice((*byte)(unsafe.Pointer(&c[0])), len(c)*4)); err != nil {
				return err
			}
		}
	}
	return nil
}

func (t *cgasTab) writeLens(w *bufio.Writer) error {
	for sh := range internerShards {
		c := t.lens[sh]
		if len(c) > 0 {
			if _, err := w.Write(unsafe.Slice((*byte)(unsafe.Pointer(&c[0])), len(c)*4)); err != nil {
				return err
			}
		}
	}
	return nil
}

func (t *cgasTab) writeBufs(w *bufio.Writer) error {
	for sh := range internerShards {
		src := t.src[sh]
		if len(src) == 0 {
			continue
		}
		c := &t.it.shards[sh]
		c.mu.RLock()
		var werr error
		for _, old := range src {
			local := old & (1<<(32-internerShardBits) - 1)
			if _, err := w.Write(c.buf[c.off[local] : c.off[local]+c.ln[local]]); err != nil {
				werr = err
				break
			}
		}
		c.mu.RUnlock()
		if werr != nil {
			return werr
		}
	}
	return nil
}

func cgasRowSize[T any]() uint64 {
	return uint64(unsafe.Sizeof(*new(T)))
}

func cgasPlanIDRows[T any](rows []T, idOffs []uintptr, t *cgasTab) {
	if len(rows) == 0 || len(idOffs) == 0 {
		return
	}
	size := unsafe.Sizeof(rows[0])
	base := unsafe.Pointer(&rows[0])
	for i := 0; i < len(rows); i++ {
		row := unsafe.Pointer(uintptr(base) + uintptr(i)*size)
		for _, o := range idOffs {
			t.mapID(*(*uint32)(unsafe.Pointer(uintptr(row) + uintptr(o))))
		}
	}
}

func cgasPlanIDs(g *Graph, t *cgasTab) {
	sv := reflect.ValueOf(&g.Sym).Elem()
	for _, f := range symSliceFields {
		switch col := sv.Field(f).Interface().(type) {
		case []int32:
		case []uint32:
			for i := range col {
				t.mapID(col[i])
			}
		}
	}
	cgasPlanIDRows(g.Params, paramIDOffs, t)
	cgasPlanIDRows(g.Fields, fieldIDOffs, t)
	cgasPlanIDRows(g.Hazards, hazardIDOffs, t)
	cgasPlanIDRows(g.Imports, importIDOffs, t)
	cgasPlanIDRows(g.Literals, literalIDOffs, t)
	cgasPlanIDRows(g.Markers, markerIDOffs, t)
	cgasPlanIDRows(g.Goro, goroIDOffs, t)
	cgasPlanIDRows(g.Defers, deferIDOffs, t)
	cgasPlanIDRows(g.Chans, chanIDOffs, t)
	cgasPlanIDRows(g.Iface, ifaceIDOffs, t)
	cgasPlanIDRows(g.WgSites, wgIDOffs, t)
	cgasPlanIDRows(g.UInput, uinputIDOffs, t)
	cgasPlanIDRows(g.Secret, secretIDOffs, t)
	cgasPlanIDRows(g.Impl, implIDOffs, t)
	cgasPlanIDRows(g.BuildTag, buildTagIDOffs, t)
	cgasPlanIDRows(g.unresList, unresIDOffs, t)
}

func cgasArenaLen(g *Graph, metaKeys []string) uint64 {
	var n uint64
	for i := range g.File {
		n += uint64(len(g.File[i].Path)) + uint64(len(g.File[i].Dir)) + uint64(len(g.File[i].Basename)) + uint64(len(g.File[i].Ext)) + uint64(len(g.File[i].SHA1))
	}
	for i := range g.Mod {
		n += uint64(len(g.Mod[i].Name)) + uint64(len(g.Mod[i].Kind))
	}
	for _, k := range metaKeys {
		n += uint64(len(k)) + uint64(len(g.Meta[k]))
	}
	return n
}

func cgasWriteRows[T any](w *bufio.Writer, rows []T, patch func([]T, int)) error {
	if len(rows) == 0 {
		return nil
	}
	size := int(unsafe.Sizeof(rows[0]))
	if patch == nil {
		_, err := w.Write(unsafe.Slice((*byte)(unsafe.Pointer(&rows[0])), len(rows)*size))
		return err
	}
	const batch = 1 << 10
	sc := make([]T, min(batch, len(rows)))
	for start := 0; start < len(rows); start += batch {
		end := min(start+batch, len(rows))
		cur := sc[:end-start]
		copy(cur, rows[start:end])
		patch(cur, start)
		if _, err := w.Write(unsafe.Slice((*byte)(unsafe.Pointer(&cur[0])), len(cur)*size)); err != nil {
			return err
		}
	}
	return nil
}

func cgasPatchIDs[T any](t *cgasTab, offs []uintptr) func([]T, int) {
	return func(sc []T, _ int) {
		size := int(unsafe.Sizeof(sc[0]))
		b := unsafe.Slice((*byte)(unsafe.Pointer(&sc[0])), len(sc)*size)
		for i := range sc {
			row := b[i*size : (i+1)*size]
			for _, o := range offs {
				cgPutU32(row, int(o), t.lookup(cgGetU32(row, int(o))))
			}
		}
	}
}

func cgasPatchStrRow[T any](offs []uintptr, cur *uint64) func([]T, int) {
	return func(sc []T, _ int) {
		size := int(unsafe.Sizeof(sc[0]))
		b := unsafe.Slice((*byte)(unsafe.Pointer(&sc[0])), len(sc)*size)
		for i := range sc {
			row := b[i*size : (i+1)*size]
			for _, o := range offs {
				s := *(*string)(unsafe.Pointer(&row[o]))
				cgPutU64(row, int(o), *cur)
				*cur += uint64(len(s))
			}
		}
	}
}

func cgasPatchParams(t *cgasTab, syms []int32) func([]Param, int) {
	ids := cgasPatchIDs[Param](t, paramIDOffs)
	return func(sc []Param, base int) {
		for i := range sc {
			sc[i].sym = syms[base+i]
		}
		ids(sc, base)
	}
}

func cgasWriteArena(w *bufio.Writer, g *Graph, metaKeys []string, filesEnd, modsEnd *uint64) error {
	var cur uint64
	for i := range g.File {
		if _, err := w.WriteString(g.File[i].Path); err != nil {
			return err
		}
		cur += uint64(len(g.File[i].Path))
		if _, err := w.WriteString(g.File[i].Dir); err != nil {
			return err
		}
		cur += uint64(len(g.File[i].Dir))
		if _, err := w.WriteString(g.File[i].Basename); err != nil {
			return err
		}
		cur += uint64(len(g.File[i].Basename))
		if _, err := w.WriteString(g.File[i].Ext); err != nil {
			return err
		}
		cur += uint64(len(g.File[i].Ext))
		if _, err := w.WriteString(g.File[i].SHA1); err != nil {
			return err
		}
		cur += uint64(len(g.File[i].SHA1))
	}
	*filesEnd = cur
	for i := range g.Mod {
		if _, err := w.WriteString(g.Mod[i].Name); err != nil {
			return err
		}
		cur += uint64(len(g.Mod[i].Name))
		if _, err := w.WriteString(g.Mod[i].Kind); err != nil {
			return err
		}
		cur += uint64(len(g.Mod[i].Kind))
	}
	*modsEnd = cur
	for _, k := range metaKeys {
		if _, err := w.WriteString(k); err != nil {
			return err
		}
		if _, err := w.WriteString(g.Meta[k]); err != nil {
			return err
		}
	}
	return nil
}

func cgasWriteSymCols(w *bufio.Writer, g *Graph, t *cgasTab, dir []byte, pad int) error {
	if _, err := w.Write(dir); err != nil {
		return err
	}
	sv := reflect.ValueOf(&g.Sym).Elem()
	n := g.Sym.n
	var zero [8]byte
	for _, f := range symSliceFields {
		fv := sv.Field(f)
		var werr error
		switch col := fv.Interface().(type) {
		case []int32:
			if n > 0 {
				_, werr = w.Write(unsafe.Slice((*byte)(unsafe.Pointer(&col[0])), n*4))
			}
		case []uint32:
			const batch = 1 << 14
			sc := make([]uint32, min(batch, n))
			for start := 0; start < n && werr == nil; start += batch {
				end := min(start+batch, n)
				cur := sc[:end-start]
				copy(cur, col[start:end])
				for i := range cur {
					cur[i] = t.lookup(cur[i])
				}
				_, werr = w.Write(unsafe.Slice((*byte)(unsafe.Pointer(&cur[0])), len(cur)*4))
			}
		}
		if werr != nil {
			return werr
		}
		if pad > 0 {
			if _, err := w.Write(zero[:pad]); err != nil {
				return err
			}
		}
	}
	return nil
}

func cgasStatsBlock(g *Graph) []byte {
	b := make([]byte, 32)
	cgPutU32(b, 0, nullStr)
	cgPutU32(b, 4, internerShards)
	cgPutU64(b, 8, uint64(g.nExternal))
	cgPutU64(b, 16, uint64(g.nResolved))
	cgPutU64(b, 24, uint64(g.nUnresolvd))
	return b
}

func saveASTFile(g *Graph, path string) (int64, error) {
	cgasGuard()
	if len(g.paramsSym) != len(g.Params) {
		return 0, fmt.Errorf("params table holds %d rows but %d owner ids", len(g.Params), len(g.paramsSym))
	}
	if len(g.fieldsSym) != len(g.Fields) {
		return 0, fmt.Errorf("fields table holds %d rows but %d owner ids", len(g.Fields), len(g.fieldsSym))
	}
	n := g.Sym.n
	if n < 0 || uint64(n) >= 1<<31 {
		return 0, fmt.Errorf("symbol count %d is out of range", n)
	}
	sv := reflect.ValueOf(&g.Sym).Elem()
	for _, f := range symSliceFields {
		if sv.Field(f).Len() != n {
			return 0, fmt.Errorf("symbol column %d holds %d rows, want %d", f, sv.Field(f).Len(), n)
		}
	}
	pad := 0
	if n%2 != 0 {
		pad = 4
	}
	ncol := len(symSliceFields)
	symDir := make([]byte, 16+8*ncol)
	cgPutU64(symDir, 0, uint64(n))
	cgPutU32(symDir, 8, uint32(ncol))
	for k := range symSliceFields {
		cgPutU64(symDir, 16+8*k, uint64(4*n))
	}
	symSecLen := uint64(16+8*ncol) + uint64(ncol)*cgasAlign8(uint64(4*n))
	metaKeys := make([]string, 0, len(g.Meta))
	for k := range g.Meta {
		metaKeys = append(metaKeys, k)
	}
	sort.Strings(metaKeys)
	metaRows := make([]cgasMetaRow, len(metaKeys))
	for i, k := range metaKeys {
		metaRows[i] = cgasMetaRow{k, g.Meta[k]}
	}
	extKeys := make([]int32, 0, len(g.extByCall))
	for k := range g.extByCall {
		extKeys = append(extKeys, k)
	}
	sort.Slice(extKeys, func(a, b int) bool { return extKeys[a] < extKeys[b] })
	extRows := make([]cgasExtKV, len(extKeys))
	for i, k := range extKeys {
		extRows[i] = cgasExtKV{k, g.extByCall[k]}
	}
	t := cgasNewTab(g.Str)
	cgasPlanIDs(g, t)
	arenaLen := cgasArenaLen(g, metaKeys)

	dir := make([]cgasSec, cgasNSec)
	cur := uint64(cgasHeaderSz) + cgasNSec*cgasSecSz
	setSec := func(sec uint32, ln uint64) {
		cur = (cur + 7) &^ 7
		dir[sec-1] = cgasSec{sec, 0, cur, ln}
		cur += ln
	}
	setSec(cgasSecStrings, arenaLen)
	setSec(cgasSecSyms, symSecLen)
	setSec(cgasSecFiles, uint64(len(g.File))*cgasRowSize[File]())
	setSec(cgasSecMods, uint64(len(g.Mod))*cgasRowSize[Module]())
	setSec(cgasSecIDir, uint64(4+16*internerShards))
	setSec(cgasSecSPos, 4*uint64(t.nstr))
	setSec(cgasSecSLn, 4*uint64(t.nstr))
	setSec(cgasSecSBuf, t.bufBytes())
	setSec(cgasSecParams, uint64(len(g.Params))*cgasRowSize[Param]())
	setSec(cgasSecParamSym, uint64(len(g.paramsSym))*cgasRowSize[int32]())
	setSec(cgasSecFields, uint64(len(g.Fields))*cgasRowSize[Field]())
	setSec(cgasSecFieldSym, uint64(len(g.fieldsSym))*cgasRowSize[int32]())
	setSec(cgasSecHazards, uint64(len(g.Hazards))*cgasRowSize[Hazard]())
	setSec(cgasSecImports, uint64(len(g.Imports))*cgasRowSize[Import]())
	setSec(cgasSecLiterals, uint64(len(g.Literals))*cgasRowSize[Literal]())
	setSec(cgasSecMarkers, uint64(len(g.Markers))*cgasRowSize[Marker]())
	setSec(cgasSecGoro, uint64(len(g.Goro))*cgasRowSize[Goro]())
	setSec(cgasSecDefers, uint64(len(g.Defers))*cgasRowSize[Defer]())
	setSec(cgasSecChans, uint64(len(g.Chans))*cgasRowSize[Chan]())
	setSec(cgasSecIfaces, uint64(len(g.Iface))*cgasRowSize[Iface]())
	setSec(cgasSecStructs, uint64(len(g.Structs))*cgasRowSize[Struct]())
	setSec(cgasSecWgSites, uint64(len(g.WgSites))*cgasRowSize[WgSite]())
	setSec(cgasSecUInputs, uint64(len(g.UInput))*cgasRowSize[UInput]())
	setSec(cgasSecSecrets, uint64(len(g.Secret))*cgasRowSize[Secret]())
	setSec(cgasSecImpls, uint64(len(g.Impl))*cgasRowSize[Impl]())
	setSec(cgasSecBuildTags, uint64(len(g.BuildTag))*cgasRowSize[BuildTag]())
	setSec(cgasSecErrChain, uint64(len(g.ErrChain))*cgasRowSize[ErrChain]())
	setSec(cgasSecEdges, uint64(len(g.edgeList))*cgasRowSize[rawEdge]())
	setSec(cgasSecUnres, uint64(len(g.unresList))*cgasRowSize[Unres]())
	setSec(cgasSecSites, uint64(len(g.csList))*cgasRowSize[Callsite]())
	setSec(cgasSecMeta, uint64(len(metaRows))*cgasRowSize[cgasMetaRow]())
	setSec(cgasSecExtByCall, uint64(len(extRows))*cgasRowSize[cgasExtKV]())
	setSec(cgasSecStats, 32)
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
	cgPutU32(hdr, 4, cgasVersion)
	cgPutU32(hdr, 8, cgasNSec)
	cgPutU64(hdr, 16, total)
	cgPutU64(hdr, 24, arenaLen)
	if _, err := w.Write(hdr); err != nil {
		return fail(err)
	}
	dirBuf := make([]byte, cgasNSec*cgasSecSz)
	for i := range dir {
		o := i * int(cgasSecSz)
		cgPutU32(dirBuf, o, dir[i].ID)
		cgPutU64(dirBuf, o+8, dir[i].Off)
		cgPutU64(dirBuf, o+16, dir[i].Len)
	}
	if _, err := w.Write(dirBuf); err != nil {
		return fail(err)
	}
	var zero [8]byte
	pos := uint64(cgasHeaderSz) + cgasNSec*cgasSecSz
	fCur, mCur, metaCur := uint64(0), uint64(0), uint64(0)
	for i := range dir {
		if dir[i].Off > pos {
			if _, err := w.Write(zero[:dir[i].Off-pos]); err != nil {
				return fail(err)
			}
			pos = dir[i].Off
		}
		var werr error
		switch uint32(i + 1) {
		case cgasSecStrings:
			werr = cgasWriteArena(w, g, metaKeys, &fCur, &mCur)
		case cgasSecSyms:
			werr = cgasWriteSymCols(w, g, t, symDir, pad)
		case cgasSecFiles:
			fCur = 0
			werr = cgasWriteRows(w, g.File, cgasPatchStrRow[File](fileStrOffs, &fCur))
		case cgasSecMods:
			mCur = fCur
			werr = cgasWriteRows(w, g.Mod, cgasPatchStrRow[Module](moduleStrOffs, &mCur))
		case cgasSecIDir:
			_, werr = w.Write(t.idir())
		case cgasSecSPos:
			werr = t.writeOffs(w)
		case cgasSecSLn:
			werr = t.writeLens(w)
		case cgasSecSBuf:
			werr = t.writeBufs(w)
		case cgasSecParams:
			werr = cgasWriteRows(w, g.Params, cgasPatchParams(t, g.paramsSym))
		case cgasSecParamSym:
			werr = cgasWriteRows(w, g.paramsSym, nil)
		case cgasSecFields:
			werr = cgasWriteRows(w, g.Fields, cgasPatchIDs[Field](t, fieldIDOffs))
		case cgasSecFieldSym:
			werr = cgasWriteRows(w, g.fieldsSym, nil)
		case cgasSecHazards:
			werr = cgasWriteRows(w, g.Hazards, cgasPatchIDs[Hazard](t, hazardIDOffs))
		case cgasSecImports:
			werr = cgasWriteRows(w, g.Imports, cgasPatchIDs[Import](t, importIDOffs))
		case cgasSecLiterals:
			werr = cgasWriteRows(w, g.Literals, cgasPatchIDs[Literal](t, literalIDOffs))
		case cgasSecMarkers:
			werr = cgasWriteRows(w, g.Markers, cgasPatchIDs[Marker](t, markerIDOffs))
		case cgasSecGoro:
			werr = cgasWriteRows(w, g.Goro, cgasPatchIDs[Goro](t, goroIDOffs))
		case cgasSecDefers:
			werr = cgasWriteRows(w, g.Defers, cgasPatchIDs[Defer](t, deferIDOffs))
		case cgasSecChans:
			werr = cgasWriteRows(w, g.Chans, cgasPatchIDs[Chan](t, chanIDOffs))
		case cgasSecIfaces:
			werr = cgasWriteRows(w, g.Iface, cgasPatchIDs[Iface](t, ifaceIDOffs))
		case cgasSecStructs:
			werr = cgasWriteRows(w, g.Structs, nil)
		case cgasSecWgSites:
			werr = cgasWriteRows(w, g.WgSites, cgasPatchIDs[WgSite](t, wgIDOffs))
		case cgasSecUInputs:
			werr = cgasWriteRows(w, g.UInput, cgasPatchIDs[UInput](t, uinputIDOffs))
		case cgasSecSecrets:
			werr = cgasWriteRows(w, g.Secret, cgasPatchIDs[Secret](t, secretIDOffs))
		case cgasSecImpls:
			werr = cgasWriteRows(w, g.Impl, cgasPatchIDs[Impl](t, implIDOffs))
		case cgasSecBuildTags:
			werr = cgasWriteRows(w, g.BuildTag, cgasPatchIDs[BuildTag](t, buildTagIDOffs))
		case cgasSecErrChain:
			werr = cgasWriteRows(w, g.ErrChain, nil)
		case cgasSecEdges:
			werr = cgasWriteRows(w, g.edgeList, nil)
		case cgasSecUnres:
			werr = cgasWriteRows(w, g.unresList, cgasPatchIDs[Unres](t, unresIDOffs))
		case cgasSecSites:
			werr = cgasWriteRows(w, g.csList, nil)
		case cgasSecMeta:
			metaCur = mCur
			werr = cgasWriteRows(w, metaRows, cgasPatchStrRow[cgasMetaRow](metaStrOffs, &metaCur))
		case cgasSecExtByCall:
			werr = cgasWriteRows(w, extRows, nil)
		case cgasSecStats:
			_, werr = w.Write(cgasStatsBlock(g))
		}
		if werr != nil {
			return fail(werr)
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
func cgasCheckID(it *Interner, id uint32, what string) error {
	if id == nullStr {
		return nil
	}
	sh := id >> (32 - internerShardBits)
	if sh >= internerShards {
		return fmt.Errorf("%s: interner id %d names shard %d of %d", what, id, sh, internerShards)
	}
	if id&(1<<(32-internerShardBits)-1) >= uint32(len(it.shards[sh].ln)) {
		return fmt.Errorf("%s: interner id %d exceeds its shard", what, id)
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
		return nil, fmt.Errorf("%s: too small (%d bytes) to be a graph state file", path, st.Size())
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
		return nil, bad("bad magic %q, want %q -- not a graph state file", string(mem[0:4]), cgasMagic)
	}
	if v := cgGetU32(mem, 4); v != cgasVersion {
		return nil, bad("unsupported state format version %d, want %d", v, cgasVersion)
	}
	secCount := int(cgGetU32(mem, 8))
	total := cgGetU64(mem, 16)
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
	arenaLen := cgGetU64(mem, 24)
	if al != arenaLen {
		return nil, bad("string arena length %d, header says %d", al, arenaLen)
	}
	arena := mem[ao : ao+al]
	memPtr := &mem[0]
	dec := func(id uint32) (uint64, uint64) {
		return secs[id].Off, secs[id].Len
	}
	decErr := func(err error) (*Graph, error) {
		return nil, bad("%v", err)
	}

	g := NewGraph()
	g.astBlob = mem

	idirOff, idirLn := dec(cgasSecIDir)
	if idirLn < 4 {
		return nil, bad("interner directory too small (%d bytes)", idirLn)
	}
	nshard := cgGetU32(mem, int(idirOff))
	if nshard != internerShards {
		return nil, bad("interner shard count %d, want %d", nshard, internerShards)
	}
	if uint64(idirLn) < 4+16*uint64(nshard) {
		return nil, bad("interner directory truncated")
	}
	bufLens := make([]uint64, nshard)
	strCnts := make([]uint64, nshard)
	var totStr, totBuf uint64
	for sh := 0; sh < int(nshard); sh++ {
		bufLens[sh] = cgGetU64(mem, int(idirOff)+4+16*sh)
		strCnts[sh] = cgGetU64(mem, int(idirOff)+4+16*sh+8)
		totStr += strCnts[sh]
		totBuf += bufLens[sh]
	}
	po, pl := dec(cgasSecSPos)
	lo, ll := dec(cgasSecSLn)
	bo, bl := dec(cgasSecSBuf)
	if pl != 4*totStr {
		return nil, bad("interner offset table holds %d bytes, want %d", pl, 4*totStr)
	}
	if ll != 4*totStr {
		return nil, bad("interner length table holds %d bytes, want %d", ll, 4*totStr)
	}
	if bl != totBuf {
		return nil, bad("interner chunk table holds %d bytes, want %d", bl, totBuf)
	}
	if totStr >= 1<<31 {
		return nil, bad("interner holds %d strings, too many", totStr)
	}
	spos := unsafe.Slice((*uint32)(unsafe.Pointer(uintptr(unsafe.Pointer(memPtr))+uintptr(po))), int(totStr))
	sln := unsafe.Slice((*uint32)(unsafe.Pointer(uintptr(unsafe.Pointer(memPtr))+uintptr(lo))), int(totStr))
	sbuf := mem[bo : bo+bl]
	at, bat := 0, uint64(0)
	for sh := 0; sh < int(nshard); sh++ {
		c := &g.Str.shards[sh]
		ns, nb := int(strCnts[sh]), bufLens[sh]
		c.buf = sbuf[bat : bat+nb]
		c.off = spos[at : at+ns]
		c.ln = sln[at : at+ns]
		c.idx = make(map[string]uint32, ns)
		c.strs = make([]string, ns)
		for j := 0; j < ns; j++ {
			o, slen := c.off[j], c.ln[j]
			if uint64(o) > nb || uint64(slen) > nb-uint64(o) {
				return nil, bad("interner string %d/%d escapes its chunk", sh, j)
			}
			s := string(c.buf[o : o+slen])
			c.strs[j] = s
			c.idx[s] = uint32(sh)<<(32-internerShardBits) | uint32(j)
		}
		c.built = true
		at += ns
		bat += nb
	}
	g.Str.null = nullStr

	so, sl := dec(cgasSecSyms)
	if sl < 16 {
		return nil, bad("symbol column directory too small (%d bytes)", sl)
	}
	symN := cgGetU64(mem, int(so))
	symNCols := cgGetU32(mem, int(so)+8)
	if symNCols != uint32(len(symSliceFields)) {
		return nil, bad("symbol column count %d, want %d", symNCols, len(symSliceFields))
	}
	if symN >= 1<<31 {
		return nil, bad("symbol count %d is out of range", symN)
	}
	want := cgasAlign8(4 * symN)
	if expect := uint64(16+8*int(symNCols)) + uint64(symNCols)*want; expect != sl {
		return nil, bad("symbol section length %d, want %d", sl, expect)
	}
	sn := int(symN)
	sv := reflect.ValueOf(&g.Sym).Elem()
	base := so + 16
	for k := 0; k < int(symNCols); k++ {
		if L := cgGetU64(mem, int(base)+8*k); L != 4*symN {
			return nil, bad("symbol column %d holds %d bytes, want %d", k, L, 4*symN)
		}
	}
	p := base + 8*uint64(symNCols)
	for k, f := range symSliceFields {
		p = cgasAlign8(p)
		if sn > 0 {
			if p+4*symN > so+sl {
				return nil, bad("symbol column %d overruns its section", k)
			}
			cp := unsafe.Pointer(uintptr(unsafe.Pointer(memPtr)) + uintptr(p))
			if cgasSymColKinds[k] == reflect.Uint32 {
				ids := unsafe.Slice((*uint32)(cp), sn)
				for i := range ids {
					if err := cgasCheckID(g.Str, ids[i], "symbol column"); err != nil {
						return nil, bad("%v", err)
					}
				}
				sv.Field(f).Set(reflect.ValueOf(ids))
			} else {
				sv.Field(f).Set(reflect.ValueOf(unsafe.Slice((*int32)(cp), sn)))
			}
		}
		p += want
	}
	g.Sym.n = sn

	off, ln := dec(cgasSecFiles)
	files, err := cgasDecodeRows[File](mem, arena, off, ln, fileStrOffs, "files")
	if err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecMods)
	mods, err := cgasDecodeRows[Module](mem, arena, off, ln, moduleStrOffs, "modules")
	if err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecParams)
	params, err := cgasDecodeRows[Param](mem, arena, off, ln, nil, "params")
	if err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecParamSym)
	paramsSym, err := cgasDecodeRows[int32](mem, arena, off, ln, nil, "param owner ids")
	if err != nil {
		return decErr(err)
	}
	if len(paramsSym) != len(params) {
		return nil, bad("param owner id count %d, want %d", len(paramsSym), len(params))
	}
	off, ln = dec(cgasSecFields)
	fields, err := cgasDecodeRows[Field](mem, arena, off, ln, nil, "fields")
	if err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecFieldSym)
	fieldsSym, err := cgasDecodeRows[int32](mem, arena, off, ln, nil, "field owner ids")
	if err != nil {
		return decErr(err)
	}
	if len(fieldsSym) != len(fields) {
		return nil, bad("field owner id count %d, want %d", len(fieldsSym), len(fields))
	}
	off, ln = dec(cgasSecHazards)
	hazards, err := cgasDecodeRows[Hazard](mem, arena, off, ln, nil, "hazards")
	if err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecImports)
	imports, err := cgasDecodeRows[Import](mem, arena, off, ln, nil, "imports")
	if err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecLiterals)
	literals, err := cgasDecodeRows[Literal](mem, arena, off, ln, nil, "literals")
	if err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecMarkers)
	markers, err := cgasDecodeRows[Marker](mem, arena, off, ln, nil, "markers")
	if err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecGoro)
	goro, err := cgasDecodeRows[Goro](mem, arena, off, ln, nil, "goroutines")
	if err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecDefers)
	defers, err := cgasDecodeRows[Defer](mem, arena, off, ln, nil, "defers")
	if err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecChans)
	chans, err := cgasDecodeRows[Chan](mem, arena, off, ln, nil, "channels")
	if err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecIfaces)
	ifaces, err := cgasDecodeRows[Iface](mem, arena, off, ln, nil, "interfaces")
	if err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecStructs)
	structs, err := cgasDecodeRows[Struct](mem, arena, off, ln, nil, "structs")
	if err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecWgSites)
	wgSites, err := cgasDecodeRows[WgSite](mem, arena, off, ln, nil, "waitgroup sites")
	if err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecUInputs)
	uInputs, err := cgasDecodeRows[UInput](mem, arena, off, ln, nil, "user input sites")
	if err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecSecrets)
	secrets, err := cgasDecodeRows[Secret](mem, arena, off, ln, nil, "secret candidates")
	if err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecImpls)
	impls, err := cgasDecodeRows[Impl](mem, arena, off, ln, nil, "interface satisfactions")
	if err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecBuildTags)
	buildTags, err := cgasDecodeRows[BuildTag](mem, arena, off, ln, nil, "build tags")
	if err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecErrChain)
	errChains, err := cgasDecodeRows[ErrChain](mem, arena, off, ln, nil, "error chain depths")
	if err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecEdges)
	edges, err := cgasDecodeRows[rawEdge](mem, arena, off, ln, nil, "call-graph edges")
	if err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecUnres)
	unres, err := cgasDecodeRows[Unres](mem, arena, off, ln, nil, "unresolved calls")
	if err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecSites)
	sites, err := cgasDecodeRows[Callsite](mem, arena, off, ln, nil, "call sites")
	if err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecMeta)
	metaRows, err := cgasDecodeRows[cgasMetaRow](mem, arena, off, ln, metaStrOffs, "meta")
	if err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecExtByCall)
	extRows, err := cgasDecodeRows[cgasExtKV](mem, arena, off, ln, nil, "external call tally")
	if err != nil {
		return decErr(err)
	}
	so2, sl2 := dec(cgasSecStats)
	if sl2 != 32 {
		return nil, bad("stats block is %d bytes, want 32", sl2)
	}
	if cgGetU32(mem, int(so2)) != nullStr {
		return nil, bad("stats block carries an unexpected null id")
	}
	if cgGetU32(mem, int(so2)+4) != internerShards {
		return nil, bad("stats block carries an unexpected shard count")
	}
	g.nExternal = int32(cgGetU64(mem, int(so2)+8))
	g.nResolved = int32(cgGetU64(mem, int(so2)+16))
	g.nUnresolvd = int32(cgGetU64(mem, int(so2)+24))

	g.File = files
	g.Mod = mods
	g.Params = params
	g.paramsSym = paramsSym
	g.Fields = fields
	g.fieldsSym = fieldsSym
	g.Hazards = hazards
	g.Imports = imports
	g.Literals = literals
	g.Markers = markers
	g.Goro = goro
	g.Defers = defers
	g.Chans = chans
	g.Iface = ifaces
	g.Structs = structs
	g.WgSites = wgSites
	g.UInput = uInputs
	g.Secret = secrets
	g.Impl = impls
	g.BuildTag = buildTags
	g.ErrChain = errChains
	g.edgeList = edges
	g.unresList = unres
	g.csList = sites
	g.Meta = make(map[string]string, len(metaRows))
	for i := range metaRows {
		g.Meta[metaRows[i].K] = metaRows[i].V
	}
	g.extByCall = make(map[int32]int32, len(extRows))
	for i := range extRows {
		g.extByCall[extRows[i].K] = extRows[i].V
	}
	g.ParseMode = g.Meta["parse_mode"]
	g.Parser = g.Meta["parser"]
	g.SQLite = g.Meta["sqlite"]
	rebuildNameScopes(g)
	g.buildCSRs()
	return g, nil
}

func cgasDecodeRows[T any](mem, arena []byte, off, ln uint64, offs []uintptr, what string) ([]T, error) {
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
	rows := unsafe.Slice((*T)(base), int(ln/size))
	if len(offs) == 0 {
		return rows, nil
	}
	arenaLen := uint64(len(arena))
	var arenaPtr *byte
	if arenaLen > 0 {
		arenaPtr = &arena[0]
	} else {
		arenaPtr = &mem[0]
	}
	for i := range rows {
		row := unsafe.Pointer(uintptr(base) + uintptr(i)*uintptr(size))
		for _, o := range offs {
			p := (*cgasSRef)(unsafe.Pointer(uintptr(row) + o))
			if p.Off > arenaLen || p.Ln > arenaLen-p.Off {
				return nil, fmt.Errorf("%s: string reference (%d,%d) escapes the string arena (%d bytes)",
					what, p.Off, p.Ln, arenaLen)
			}
			*(*unsafe.Pointer)(unsafe.Pointer(p)) = unsafe.Pointer(uintptr(unsafe.Pointer(arenaPtr)) + uintptr(p.Off))
		}
	}
	return rows, nil
}
