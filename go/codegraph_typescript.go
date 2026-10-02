package main

import (
	"bufio"
	"bytes"
	"crypto/sha1"
	"encoding/json"
	"encoding/json/jsontext"
	"fmt"
	"io"
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
	"runtime/trace"
	"slices"
	"sort"
	"strconv"
	"strings"
	"sync"
	"syscall"
	"time"
	"unicode"
	"unicode/utf16"
	"unicode/utf8"
	"unsafe"
)

type kindTables struct {
	syms    []string
	fields  []string
	opField []uint16
}

type allKindTables struct {
	ts  kindTables
	tsx kindTables
}

var kindT = buildAllKindTables()

var (
	tsSymNames    = kindT.ts.syms
	tsFieldNames  = kindT.ts.fields
	tsSymOpField  = kindT.ts.opField
	tsxSymNames   = kindT.tsx.syms
	tsxFieldNames = kindT.tsx.fields
	tsxSymOpField = kindT.tsx.opField
)

const tsGrammarTag = "v0.23.2"

func tsGrammarRoot() string {
	base := os.Getenv("TREE_SITTER_GRAMMARS")
	if base == "" {
		home, err := os.UserHomeDir()
		if err != nil {
			kindTablesFatal("cannot resolve the home directory: %v", err)
		}
		base = filepath.Join(home, ".cache", "codegraph", "grammars")
	}
	return filepath.Join(base, "tree-sitter-typescript")
}

func kindTablesFatal(format string, args ...any) {
	fmt.Fprintf(os.Stderr, "codegraph_typescript: "+format+"\n", args...)
	fmt.Fprintf(os.Stderr, "fix: git clone --depth 1 --branch %s https://github.com/tree-sitter/tree-sitter-typescript\n"+
		"(into %s, or point TREE_SITTER_GRAMMARS at the checkout's parent)\n",
		tsGrammarTag, tsGrammarRoot())
	os.Exit(1)
}

func buildAllKindTables() allKindTables {
	root := tsGrammarRoot()
	for _, lang := range []string{"typescript", "tsx"} {
		st, err := os.Stat(filepath.Join(root, lang, "src", "node-types.json"))
		if err != nil || st.IsDir() {
			kindTablesFatal("grammar checkout missing: %s/%s/src/node-types.json not found",
				root, lang)
		}
	}
	return allKindTables{
		ts:  buildKindTable(filepath.Join(root, "typescript", "src")),
		tsx: buildKindTable(filepath.Join(root, "tsx", "src")),
	}
}

func readString(dec *jsontext.Decoder) (string, error) {
	tok, err := dec.ReadToken()
	if err != nil {
		return "", err
	}
	return tok.String(), nil
}

func mustRead(path, srcDir string) []byte {
	raw, err := os.ReadFile(path)
	if err != nil {
		kindTablesFatal("grammar checkout incomplete (%s/src): %v", srcDir, err)
	}
	return raw
}

func buildKindTable(srcDir string) kindTables {
	syms, fields, nodeFields := walkNodeTypes(
		mustRead(filepath.Join(srcDir, "node-types.json"), srcDir), srcDir)
	supertypes := walkSupertypes(
		mustRead(filepath.Join(srcDir, "grammar.json"), srcDir), srcDir)

	seen := make(map[string]bool, len(syms)+len(supertypes)+2)
	for _, name := range syms {
		seen[name] = true
	}
	for _, name := range supertypes {
		if !seen[name] {
			seen[name] = true
			syms = append(syms, name)
		}
	}
	syms = append(syms, "ERROR", "\x00MISSING")

	if syms[len(syms)-2] != "ERROR" {
		kindTablesFatal("internal: ERROR is not the second-to-last kind for %s", srcDir)
	}

	fieldID := make(map[string]uint16, len(fields))
	for i, name := range fields {
		fieldID[name] = uint16(i + 1)
	}
	opField := make([]uint16, len(syms))
	for i, n := range syms {
		for _, f := range nodeFields[n] {
			if f == "operator" {
				opField[i] = fieldID["operator"]
			}
		}
	}

	fields = append([]string{""}, fields...)
	return kindTables{syms: syms, fields: fields, opField: opField}
}

func walkNodeTypes(raw []byte, srcDir string) (syms, fields []string, nodeFields map[string][]string) {
	dec := jsontext.NewDecoder(bytes.NewReader(raw))
	if tok, err := dec.ReadToken(); err != nil || tok.Kind() != '[' {
		kindTablesFatal("cannot parse %s/node-types.json: want a top-level array", srcDir)
	}
	seenKinds := map[string]bool{}
	seenFields := map[string]bool{}
	nodeFields = make(map[string][]string, 256)
	for dec.PeekKind() == '{' {
		typ, entryFields := walkNodeTypeEntry(dec, srcDir)
		if typ == "" || seenKinds[typ] {
			continue
		}
		seenKinds[typ] = true
		syms = append(syms, typ)
		nodeFields[typ] = entryFields
		for _, f := range entryFields {
			if f != "" && !seenFields[f] {
				seenFields[f] = true
				fields = append(fields, f)
			}
		}
	}
	if _, err := dec.ReadToken(); err != nil {
		kindTablesFatal("cannot parse %s/node-types.json: %v", srcDir, err)
	}
	return syms, fields, nodeFields
}

func walkNodeTypeEntry(dec *jsontext.Decoder, srcDir string) (typ string, entryFields []string) {
	if tok, err := dec.ReadToken(); err != nil || tok.Kind() != '{' {
		kindTablesFatal("cannot parse %s/node-types.json: entry is not an object", srcDir)
	}
	for dec.PeekKind() != '}' {
		name, err := readString(dec)
		if err != nil {
			kindTablesFatal("cannot parse %s/node-types.json: %v", srcDir, err)
		}
		switch name {
		case "type":
			if typ, err = readString(dec); err != nil {
				kindTablesFatal("cannot parse %s/node-types.json: %v", srcDir, err)
			}
		case "fields":
			entryFields = walkFieldsObject(dec)
		default:
			if err := dec.SkipValue(); err != nil {
				kindTablesFatal("cannot parse %s/node-types.json: %v", srcDir, err)
			}
		}
	}
	if _, err := dec.ReadToken(); err != nil {
		kindTablesFatal("cannot parse %s/node-types.json: %v", srcDir, err)
	}
	return typ, entryFields
}

func walkFieldsObject(dec *jsontext.Decoder) []string {
	if dec.PeekKind() != '{' {
		dec.SkipValue()
		return nil
	}
	dec.ReadToken()
	var keys []string
	for dec.PeekKind() != '}' {
		name, err := readString(dec)
		if err != nil {
			return keys
		}
		keys = append(keys, name)
		dec.SkipValue()
	}
	dec.ReadToken()
	return keys
}

func walkSupertypes(raw []byte, srcDir string) []string {
	dec := jsontext.NewDecoder(bytes.NewReader(raw))
	if tok, err := dec.ReadToken(); err != nil || tok.Kind() != '{' {
		kindTablesFatal("cannot parse %s/grammar.json: want a top-level object", srcDir)
	}
	var supertypes []string
	for dec.PeekKind() != '}' {
		name, err := readString(dec)
		if err != nil {
			kindTablesFatal("cannot parse %s/grammar.json: %v", srcDir, err)
		}
		if name == "supertypes" && dec.PeekKind() == '[' {
			dec.ReadToken()
			supertypes = nil
			for dec.PeekKind() != ']' {
				s, err := readString(dec)
				if err != nil {
					kindTablesFatal("cannot parse %s/grammar.json: %v", srcDir, err)
				}
				supertypes = append(supertypes, s)
			}
			dec.ReadToken()
		} else {
			if err := dec.SkipValue(); err != nil {
				kindTablesFatal("cannot parse %s/grammar.json: %v", srcDir, err)
			}
		}
	}
	dec.ReadToken()
	return supertypes
}

func writeMeta(g *Graph, o *Options, bs *BuildStats, ntsx int) {
	abs, _ := absPath(o.Root)
	g.setMeta("schema_version", "1")
	g.setMeta("lang", langName)
	g.setMeta("target", targetName)
	g.setMeta("root", abs)
	g.setMeta("parse_mode", "tree-sitter")
	g.setMeta("files_parsed", itoa(bs.FilesParsed))
	g.setMeta("files_failed", itoa(bs.FilesFailed))
	g.setMeta("tsx_files", itoa(ntsx))
	g.setMeta("imports_resolved", g.metaOf("imports_resolved"))
	g.setMeta("calls_resolved", callsResolvedNote(bs))
}

func callsResolvedNote(bs *BuildStats) string {
	den := bs.Resolved + bs.Unresolved
	pct := 0
	if den > 0 {
		pct = 100 * bs.Resolved / den
	}
	return itoa(bs.Resolved) + " in-tree / " + itoa(bs.External) + " external / " +
		itoa(bs.Unresolved) + " unresolved (" + itoa(pct) + "% of in-scope resolved)"
}

func absPath(p string) (string, error) {
	if len(p) > 0 && p[0] == '/' {
		return p, nil
	}
	wd, err := os.Getwd()
	if err != nil {
		return p, err
	}
	return wd + "/" + p, nil
}

type Symbol struct {
	FileID    int32
	ModuleID  int32
	ParentID  int32
	padS1     [4]byte
	name      cgStr
	qualName  cgStr
	Kind      int8
	padS2     [7]byte
	vis       cgStr
	LineStart int32
	LineEnd   int32
	ByteStart int32
	ByteEnd   int32
	sig       cgStr
	retType   cgStr
	MOff      int32
	padS3     [4]byte
}

func (s *Symbol) Name() string     { return s.name.Str() }
func (s *Symbol) QualName() string { return s.qualName.Str() }
func (s *Symbol) Vis() string      { return s.vis.Str() }
func (s *Symbol) Sig() string      { return s.sig.Str() }
func (s *Symbol) RetType() string  { return s.retType.Str() }

type Module struct {
	name        cgStr
	kind        cgStr
	NFiles      int32
	NSymbols    int32
	NPublic     int32
	Sloc        int32
	FanIn       int32
	FanOut      int32
	Instability float64
}

func (m *Module) Name() string { return m.name.Str() }
func (m *Module) Kind() string { return m.kind.Str() }

type File struct {
	path      cgStr
	dir       cgStr
	base      cgStr
	ext       cgStr
	lang      cgStr
	ModuleID  int32
	Bytes     int32
	Lines     int32
	Sloc      int32
	Blank     int32
	Comment   int32
	DocLines  int32
	MaxLen    int32
	sha1      cgStr
	Parsed    bool
	IsTest    bool
	IsGen     bool
	IsVend    bool
	NErrs     int32
	NMissing  int32
	NSymbols  int32
	NFuncs    int32
	NTypes    int32
	NImports  int32
	TotalCyc  int32
	MaxCyc    int32
	TotalRisk int32
}

func (f *File) Path() string     { return f.path.Str() }
func (f *File) Dir() string      { return f.dir.Str() }
func (f *File) Basename() string { return f.base.Str() }
func (f *File) Ext() string      { return f.ext.Str() }
func (f *File) Lang() string     { return f.lang.Str() }
func (f *File) Sha1() string     { return f.sha1.Str() }

type Param struct {
	SymID   int32
	Pos     int32
	name    cgStr
	typ     cgStr
	IsUntyp bool
	padP    [3]byte
	Depth   int32
}

func (p *Param) Name() string { return p.name.Str() }
func (p *Param) Type() string { return p.typ.Str() }

type Field struct {
	SymID   int32
	Ordinal int32
	name    cgStr
	typ     cgStr
	Line    int32
	IsConst bool
	IsMut   bool
	IsNull  bool
	IsColl  bool
	IsUntyp bool
	padF    [3]byte
	Depth   int32
}

func (f *Field) Name() string { return f.name.Str() }
func (f *Field) Type() string { return f.typ.Str() }

type Edge struct {
	Caller, Callee             int32
	NCalls                     int32
	SameFile, SameModule, Self bool
	padE                       [1]byte
}

type Callsite struct {
	Caller, Callee, Line int32
}

type Unresolved struct {
	Caller    int32
	padN      [4]byte
	name      cgStr
	N         int32
	FirstLine int32
}

func (u *Unresolved) Name() string { return u.name.Str() }

type Import struct {
	FileID     int32
	padI1      [4]byte
	target     cgStr
	TargetID   int32
	padI2      [4]byte
	kind       cgStr
	Line       int32
	IsExternal bool
	IsRelative bool
	IsWildcard bool
	IsTypeOnly bool
	IsDynamic  bool
	padI3      [3]byte
	NNames     int32
}

func (m *Import) Target() string { return m.target.Str() }
func (m *Import) Kind() string   { return m.kind.Str() }

type Hazard struct {
	SymID     int32
	padH      [4]byte
	pattern   cgStr
	category  cgStr
	N         int32
	FirstLine int32
}

func (h *Hazard) Pattern() string  { return h.pattern.Str() }
func (h *Hazard) Category() string { return h.category.Str() }

type AttrRow struct {
	SymID  int32
	FileID int32
	name   cgStr
	args   cgStr
	Line   int32
	padA1  [4]byte
}

func (a *AttrRow) Name() string { return a.name.Str() }
func (a *AttrRow) Args() string { return a.args.Str() }

type Literal struct {
	SymID   int32
	FileID  int32
	kind    cgStr
	value   cgStr
	Line    int32
	IsMagic bool
	padL    [3]byte
}

func (l *Literal) Kind() string  { return l.kind.Str() }
func (l *Literal) Value() string { return l.value.Str() }

type EnumMember struct {
	SymID   int32
	Ordinal int32
	name    cgStr
	value   cgStr
	HasVal  bool
	padE    [7]byte
}

func (e *EnumMember) Name() string  { return e.name.Str() }
func (e *EnumMember) Value() string { return e.value.Str() }

type Marker struct {
	FileID int32
	SymID  int32
	kind   cgStr
	Line   int32
	padK   [4]byte
	text   cgStr
}

func (m *Marker) Kind() string { return m.kind.Str() }
func (m *Marker) Text() string { return m.text.Str() }

type MetaRow struct {
	K cgStr
	V cgStr
}

type TSExport struct {
	FileID     int32
	padX1      [4]byte
	name       cgStr
	kind       cgStr
	Line       int32
	IsDefault  bool
	IsReexport bool
	IsStar     bool
	IsTypeOnly bool
	source     cgStr
	HasSource  bool
	padX2      [7]byte
}

func (x *TSExport) Name() string   { return x.name.Str() }
func (x *TSExport) Kind() string   { return x.kind.Str() }
func (x *TSExport) Source() string { return x.source.Str() }

type Suppression struct {
	FileID    int32
	SymID     int32
	kind      cgStr
	Line      int32
	padP1     [4]byte
	reason    cgStr
	HasReason bool
	padP2     [7]byte
}

func (s *Suppression) Kind() string   { return s.kind.Str() }
func (s *Suppression) Reason() string { return s.reason.Str() }

type TSConfig struct {
	path        cgStr
	dir         cgStr
	extends     cgStr
	HasExtends  bool
	Strict      bool
	NoImplAny   bool
	NullChecks  bool
	UncheckedIx bool
	ExactOpt    bool
	Verbatim    bool
	Isolated    bool
	Erasable    bool
	padT1       [3]byte
	NStrict     int32
	target      cgStr
	module      cgStr
	resolution  cgStr
	removed     cgStr
	HasRemoved  bool
	padT2       [7]byte
	baseURL     cgStr
	HasBaseURL  bool
	padT3       [7]byte
	pathsJSON   cgStr
	HasPaths    bool
	padT4       [7]byte
}

func (c *TSConfig) Path() string       { return c.path.Str() }
func (c *TSConfig) Dir() string        { return c.dir.Str() }
func (c *TSConfig) Extends() string    { return c.extends.Str() }
func (c *TSConfig) Target() string     { return c.target.Str() }
func (c *TSConfig) Module() string     { return c.module.Str() }
func (c *TSConfig) Resolution() string { return c.resolution.Str() }
func (c *TSConfig) Removed() string    { return c.removed.Str() }
func (c *TSConfig) BaseURL() string    { return c.baseURL.Str() }
func (c *TSConfig) PathsJSON() string  { return c.pathsJSON.Str() }

type DepRow struct {
	name    cgStr
	version cgStr
	IsDev   bool
	padD    [7]byte
	dir     cgStr
}

func (d *DepRow) Name() string    { return d.name.Str() }
func (d *DepRow) Version() string { return d.version.Str() }
func (d *DepRow) Dir() string     { return d.dir.Str() }

type SigToken struct {
	SymID int32
	padG  [4]byte
	token cgStr
}

func (t *SigToken) Token() string { return t.token.Str() }

type TypeDef struct {
	SymID       int32
	NMembers    int32
	NOptional   int32
	NReadonly   int32
	NIndexSig   int32
	NCallSig    int32
	NExtends    int32
	padY        [4]byte
	extendsName cgStr
	NAnyMembers int32
	IsExported  bool
	IsAmbient   bool
	IsConstEnum bool
	padY2       [1]byte
}

func (t *TypeDef) ExtendsName() string { return t.extendsName.Str() }

type Listener struct {
	SymID   int32
	FileID  int32
	op      cgStr
	target  cgStr
	event   cgStr
	Line    int32
	InLoop  bool
	IsAsync bool
	padW    [2]byte
}

func (l *Listener) Op() string     { return l.op.Str() }
func (l *Listener) Target() string { return l.target.Str() }
func (l *Listener) Event() string  { return l.event.Str() }

type InputSite struct {
	SymID  int32
	FileID int32
	vr     cgStr
	kind   cgStr
	Line   int32
	InLoop bool
	padU   [3]byte
}

func (u *InputSite) Var() string  { return u.vr.Str() }
func (u *InputSite) Kind() string { return u.kind.Str() }

type Secret struct {
	SymID  int32
	FileID int32
	value  cgStr
	Line   int32
	padC   [4]byte
}

func (s *Secret) Value() string { return s.value.Str() }

type AwaitRow struct {
	SymID  int32
	FileID int32
	name   cgStr
	base   cgStr
	Line   int32
	padQ   [4]byte
}

func (a *AwaitRow) Name() string { return a.name.Str() }
func (a *AwaitRow) Base() string { return a.base.Str() }

type Graph struct {
	Symbols []Symbol
	Files   []File
	Modules []Module

	astTrees []*tsTree
	astBlob  []byte

	Params      []Param
	Fields      []Field
	Edges       []Edge
	Callsites   []Callsite
	Unresolved  []Unresolved
	Imports     []Import
	Hazards     []Hazard
	Attributes  []AttrRow
	Literals    []Literal
	EnumMembers []EnumMember
	Markers     []Marker
	TSExports   []TSExport
	Suppress    []Suppression
	TSConfigs   []TSConfig
	Deps        []DepRow
	SigTokens   []SigToken
	TypeDefs    []TypeDef
	Listeners   []Listener
	InputSites  []InputSite
	Secrets     []Secret
	Awaited     []AwaitRow
	Meta        []MetaRow

	mchunks [][]int32

	wide []wideMetric

	byName map[string][]nameCand
	byQual map[string]int32

	unresIdx map[callerNameKey]int32
	hazIdx   map[uint64]int32

	imported map[int32]map[string]bool

	pend pending

	extByCaller map[int32]int32

	adjCache  *adjacency
	scanCache map[scanOrder][]int32
	tokUse    map[string]tokenUse

	kindIdx map[string]int8
}

const metricChunkRows = 1 << 14

type wideMetric struct {
	id  int32
	col int
	val int64
}

func (g *Graph) metrics(id int32) []int32 {
	return g.mchunks[id/metricChunkRows][(id%metricChunkRows)*metricCount:]
}

func (g *Graph) mv(id int32, col int) int32 {
	return g.metrics(id)[col]
}

func pair(a, b int32) uint64 { return uint64(uint32(a))<<32 | uint64(uint32(b)) }

func patKey(s string) int32 { return int32(fnv1a(s)) }
func tokKey(s string) int32 { return int32(fnv1a(s)) }

func fnv1a(s string) uint32 {
	var h uint32 = 2166136261
	for i := 0; i < len(s); i++ {
		h ^= uint32(s[i])
		h *= 16777619
	}
	return h
}

func trip(a, b, c int32) uint64 {
	return uint64(uint32(a))<<42 | uint64(uint32(b))<<21 | uint64(uint32(c))
}

type cgStr struct{ Off, Ln uint64 }

var (
	cgArena  []byte
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
	cgIntern[s] = v
	cgMu.Unlock()
	return v
}

func (s cgStr) Str() string {
	if s.Ln == 0 {
		return ""
	}
	return unsafe.String(&cgArena[s.Off], int(s.Ln))
}

type cgSlab struct{}

func (s *cgSlab) put(v string) cgStr { return cgPut(v) }

func (s *cgSlab) view(r cgStr) string { return r.Str() }

func (s *cgSlab) reb(r cgStr) cgStr { return r }

type pending struct {
	Sid  []int32
	Fid  []int32
	Line []int32
	Name []string
	Type []string
}

func (p *pending) add(sid, fid, line int32, name, ty string) {
	p.Sid = append(p.Sid, sid)
	p.Fid = append(p.Fid, fid)
	p.Line = append(p.Line, line)
	p.Name = append(p.Name, name)
	p.Type = append(p.Type, ty)
}

var kindNames = []string{
	"function", "closure", "method", "class", "interface", "type", "enum", "module",
}

var kindLexRank = func() [8]int {
	ranks := [8]int{}
	names := append([]string(nil), kindNames...)
	sort.Strings(names)
	rankOf := map[string]int{}
	for i, n := range names {
		rankOf[n] = i
	}
	for i, n := range kindNames {
		ranks[i] = rankOf[n]
	}
	return ranks
}()

func sortSidsKindName(g *Graph, sids []int32) {
	sort.Slice(sids, func(x, y int) bool {
		a, b := &g.Symbols[sids[x]-1], &g.Symbols[sids[y]-1]
		if kindLexRank[a.Kind] != kindLexRank[b.Kind] {
			return kindLexRank[a.Kind] < kindLexRank[b.Kind]
		}
		if a.Name() != b.Name() {
			return a.Name() < b.Name()
		}
		return sids[x] < sids[y]
	})
}

const (
	kFunction = iota
	kClosure
	kMethod
	kClass
	kInterface
	kType
	kEnum
	kModule
)

var hazardCategories = []string{
	"unsound", "suppress", "sync_block", "exec", "proto_pollution", "redos",
	"listener", "timer", "cache", "io", "net", "dom", "storage", "crypto",
	"reflect",
}

const numHazCols = 15

var storedHazCols = [numHazCols]string{
	"unsound", "suppress", "sync_block", "exec", "proto_pollution", "redos",
	"listener", "timer", "cache", "io", "net", "dom", "storage", "crypto",
	"reflect",
}

const (
	mNParams = iota
	mNOptionalParams
	mNGenericParams
	mNOverloads
	mArityRank

	mIsPublic
	mIsStatic
	mIsAsync
	mIsGenerator
	mIsAbstract
	mIsOverride
	mIsExported
	mIsTest
	mIsDeprecated
	mIsEntrypoint
	mIsGenerated

	mSloc
	mBodyBytes
	mNCommentLines
	mNDocLines
	mHasDoc

	mCyclomatic
	mCognitive
	mMaxNesting
	mNTokens
	mNOperators
	mNOperands
	mNDistinctOperators
	mNDistinctOperands
	mHalsteadVolume
	mMaintainability

	mNLoops
	mNBranches
	mNReturns
	mNEarlyReturns
	mNSwitch
	mNCases
	mNTernary
	mNLogical
	mNTry
	mNCatch
	mNCatchBroad
	mNCatchEmpty
	mNFinally
	mNThrow
	mNLabels
	mNGotos

	mMaxLoopDepth
	mCallInLoop
	mAllocInLoop
	mIoInLoop
	mAwaitInLoop
	mLockInLoop
	mConcatInLoop
	mRegexInLoop
	mQueryInLoop
	mBranchInLoop

	mNLocals
	mNAssign
	mNCompoundAssign
	mNIncdec
	mNCmp
	mNBitop
	mNShift
	mNArith
	mNStringLit
	mNRegexLit
	mNFloatLit
	mNMagic
	mNNullCheck
	mNSubscript
	mNMemberAccess
	mNLambda
	mNClosureCapture

	mNCalls
	mNUniqueCalls
	mNDynamicCalls
	mNUnresolvedCalls
	mFanIn
	mFanOut
	mNCallsites
	mIsRecursive
	mIsLeaf
	mIsRoot

	mNHazards
	mRiskScore

	mCat0
)

const mLang0 = mCat0 + numHazCols

const (
	mNConstTypeParams = mLang0 + iota
	mNAnyParams
	mNAnyTotal
	mReturnsAny
	mNUnknownType
	mNAsAssertion
	mNAsAny
	mNAngleAssertion
	mNNonNull
	mNSatisfies
	mNTemplateSub
	mNSuppressions
	mNTsIgnore
	mNTsExpectError
	mNEslintDisable
	mNTypeArgs
	mNConditionalType
	mNMappedType
	mNTemplateType
	mNIndexSignature
	mNConditionalDepth
	mNInfer
	mNCallSig
	mNPropSig
	mNKeyof
	mNTypeofType
	mNUnionType
	mNUnionMembers
	mNIntersectionType
	mMaxTypeDepth
	mNAwait
	mNYield
	mNOptionalChain
	mNSpread
	mNDestructure
	mNStaticBlock
	mNDecorators
	mNThisRefs
	mNComputedMember
	mNPromiseAll
	mNThenChain
	mNFloatingPromise
	mNListenerAdd
	mNListenerRemove
	mNTimerSet
	mNTimerClear
	mNRegexRedos
	mNJsonParse
	mNInnerhtml
	mNProtoWrite
	mListenerInLoop
	mTimerInLoop
	mParseInLoop
	mDomInLoop
	mNChildProcess
	mNRedirect
	mNAuthCall
	mNFetch
	mNDynamicOpen
	mNUploadSave
	mNZipRead
	mNMassAssign
	mNLogCall
	mNConsoleLog
	mNFsSync
	mNArrayGrowInLoop
	mNSearchInLoop
	mNMathRandom
	mNJsonParseInLoop
	mNProcessExit
	mNThenInLoop
	mNAssignInLoop
	mNDisposeCall
	mNElif
	mNExternalCalls
	mIsDeclarationOnly
	mIsComponent
	mIsHook
	mIsHandler
	mNAsyncCallback
	mNAsyncExecutor
	mNSuperCalls
	mNPromiseAllInLoop
	mIsGetter
	mIsSetter
	metricCount
)

var metricCols = []string{
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
	"n_unsound",
	"n_suppress",
	"n_sync_block",
	"n_exec",
	"n_proto_pollution",
	"n_redos",
	"n_listener",
	"n_timer",
	"n_cache",
	"n_io",
	"n_net",
	"n_dom",
	"n_storage",
	"n_crypto",
	"n_reflect",
	"n_const_type_params",
	"n_any_params",
	"n_any_total",
	"returns_any",
	"n_unknown_type",
	"n_as_assertion",
	"n_as_any",
	"n_angle_assertion",
	"n_non_null",
	"n_satisfies",
	"n_template_sub",
	"n_suppressions",
	"n_ts_ignore",
	"n_ts_expect_error",
	"n_eslint_disable",
	"n_type_args",
	"n_conditional_type",
	"n_mapped_type",
	"n_template_type",
	"n_index_signature",
	"n_conditional_depth",
	"n_infer",
	"n_call_sig",
	"n_prop_sig",
	"n_keyof",
	"n_typeof_type",
	"n_union_type",
	"n_union_members",
	"n_intersection_type",
	"max_type_depth",
	"n_await",
	"n_yield",
	"n_optional_chain",
	"n_spread",
	"n_destructure",
	"n_static_block",
	"n_decorators",
	"n_this_refs",
	"n_computed_member",
	"n_promise_all",
	"n_then_chain",
	"n_floating_promise",
	"n_listener_add",
	"n_listener_remove",
	"n_timer_set",
	"n_timer_clear",
	"n_regex_redos",
	"n_json_parse",
	"n_innerhtml",
	"n_proto_write",
	"listener_in_loop",
	"timer_in_loop",
	"parse_in_loop",
	"dom_in_loop",
	"n_child_process",
	"n_redirect",
	"n_auth_call",
	"n_fetch",
	"n_dynamic_open",
	"n_upload_save",
	"n_zip_read",
	"n_mass_assign",
	"n_log_call",
	"n_console_log",
	"n_fs_sync",
	"n_array_grow_in_loop",
	"n_search_in_loop",
	"n_math_random",
	"n_json_parse_in_loop",
	"n_process_exit",
	"n_then_in_loop",
	"n_assign_in_loop",
	"n_dispose_call",
	"n_elif",
	"n_external_calls",
	"is_declaration_only",
	"is_component",
	"is_hook",
	"is_handler",
	"n_async_callback",
	"n_async_executor",
	"n_super_calls",
	"n_promise_all_in_loop",
	"is_getter",
	"is_setter",
}

func init() {
	if len(metricCols) != metricCount {
		panic("metric column table and index constants disagree: " +
			itoa(metricCount) + " vs " + itoa(len(metricCols)))
	}

	if got := metricCols[mCat0]; got != "n_unsound" {
		panic("hazard block starts at " + got)
	}
	if got := metricCols[mLang0]; got != "n_const_type_params" {
		panic("language block starts at " + got)
	}
	if got := metricCols[mIsGetter]; got != "is_getter" {
		panic("language block ends at " + got)
	}
}

func hazardMetric(cat string) int {
	for i, c := range storedHazCols {
		if c == cat {
			return mCat0 + i
		}
	}
	return -1
}

type tableDef struct {
	name  string
	ncols int
	rows  func() int
	key   func(i int) string

	emit func(w *lineWriter, i int)

	identical string
}

var g *Graph

func setGraph(x *Graph) { g = x }

func tables() []tableDef {
	return []tableDef{
		{name: "attributes", ncols: 6,
			rows: func() int { return len(g.Attributes) },
			key:  func(i int) string { return iEnc(i + 1) },
			emit: func(w *lineWriter, i int) {
				r := &g.Attributes[i]
				w.sid(i, iEnc(int(r.SymID)), iEnc(int(r.FileID)), tEnc(r.Name()),
					tEnc(r.Args()), iEnc(int(r.Line)))
			}},
		{name: "awaited_calls", ncols: 5,
			rows: func() int { return len(g.Awaited) },
			key: func(i int) string {
				r := &g.Awaited[i]
				return iEnc(int(r.SymID)) + " " + iEnc(int(r.FileID)) + " " +
					tEnc(r.Name()) + " " + tEnc(r.Base()) + " " + iEnc(int(r.Line))
			},
			emit: func(w *lineWriter, i int) {
				r := &g.Awaited[i]
				w.s(iEnc(int(r.SymID)), iEnc(int(r.FileID)), tEnc(r.Name()),
					tEnc(r.Base()), iEnc(int(r.Line)))
			}},
		{name: "callsites", ncols: 3,
			rows: func() int { return len(g.Callsites) },
			key: func(i int) string {
				r := &g.Callsites[i]
				return iEnc(int(r.Caller)) + " " + iEnc(int(r.Callee)) + " " + iEnc(int(r.Line))
			},
			emit: func(w *lineWriter, i int) {
				r := &g.Callsites[i]
				w.s(iEnc(int(r.Caller)), iEnc(int(r.Callee)), iEnc(int(r.Line)))
			}},
		{name: "deps", ncols: 5,
			rows: func() int { return len(g.Deps) },
			key:  func(i int) string { return iEnc(i + 1) },
			emit: func(w *lineWriter, i int) {
				r := &g.Deps[i]
				w.sid(i, tEnc(r.Name()), tEnc(r.Version()), bEnc(r.IsDev), tEnc(r.Dir()))
			}},
		{name: "edges", ncols: 6,
			rows: func() int { return len(g.Edges) },
			key: func(i int) string {
				r := &g.Edges[i]
				return iEnc(int(r.Caller)) + " " + iEnc(int(r.Callee))
			},
			emit: func(w *lineWriter, i int) {
				r := &g.Edges[i]
				w.s(iEnc(int(r.Caller)), iEnc(int(r.Callee)), iEnc(int(r.NCalls)),
					bEnc(r.SameFile), bEnc(r.SameModule), bEnc(r.Self))
			}},
		{name: "enum_members", ncols: 5,
			rows: func() int { return len(g.EnumMembers) },
			key: func(i int) string {
				r := &g.EnumMembers[i]
				return iEnc(int(r.SymID)) + " " + iEnc(int(r.Ordinal))
			},
			emit: func(w *lineWriter, i int) {
				r := &g.EnumMembers[i]
				w.s(iEnc(int(r.SymID)), iEnc(int(r.Ordinal)), tEnc(r.Name()),
					tEncOpt(r.Value(), r.HasVal), iEnc(0))
			}},
		{name: "fields", ncols: 14,
			rows: func() int { return len(g.Fields) },
			key: func(i int) string {
				r := &g.Fields[i]
				return iEnc(int(r.SymID)) + " " + iEnc(int(r.Ordinal))
			},
			emit: func(w *lineWriter, i int) {
				r := &g.Fields[i]
				w.s(iEnc(int(r.SymID)), iEnc(int(r.Ordinal)), tEnc(r.Name()),
					tEnc(r.Type()), tEnc(""), iEnc(int(r.Line)), iEnc(0),
					bEnc(r.IsConst), bEnc(r.IsMut), bEnc(r.IsNull), bEnc(r.IsColl),
					bEnc(r.IsUntyp), iEnc(0), iEnc(int(r.Depth)))
			}},
		{name: "files", ncols: 29,
			rows: func() int { return len(g.Files) },
			key:  func(i int) string { return iEnc(i + 1) },
			emit: func(w *lineWriter, i int) { emitFile(w, i, &g.Files[i]) }},
		{name: "hazards", ncols: 5,
			rows: func() int { return len(g.Hazards) },
			key: func(i int) string {
				r := &g.Hazards[i]
				return iEnc(int(r.SymID)) + " " + tEnc(r.Pattern())
			},
			emit: func(w *lineWriter, i int) {
				r := &g.Hazards[i]
				w.s(iEnc(int(r.SymID)), tEnc(r.Pattern()), tEnc(r.Category()),
					iEnc(int(r.N)), iEnc(int(r.FirstLine)))
			}},
		{name: "imports", ncols: 13,
			rows: func() int { return len(g.Imports) },
			key:  func(i int) string { return iEnc(i + 1) },
			emit: func(w *lineWriter, i int) {
				r := &g.Imports[i]
				w.sid(i, iEnc(int(r.FileID)), tEnc(r.Target()), iEncOpt(r.TargetID, r.TargetID >= 0),
					nullEnc, tEnc(r.Kind()), iEnc(int(r.Line)), bEnc(r.IsExternal),
					bEnc(r.IsRelative), bEnc(r.IsWildcard), bEnc(r.IsTypeOnly),
					bEnc(r.IsDynamic), iEnc(int(r.NNames)))
			}},
		{name: "listeners", ncols: 9,
			rows: func() int { return len(g.Listeners) },
			key:  func(i int) string { return iEnc(i + 1) },
			emit: func(w *lineWriter, i int) {
				r := &g.Listeners[i]
				w.sid(i, iEnc(int(r.SymID)), iEnc(int(r.FileID)), tEnc(r.Op()), tEnc(r.Target()),
					tEnc(r.Event()), iEnc(int(r.Line)), bEnc(r.InLoop), bEnc(r.IsAsync))
			}},
		{name: "literals", ncols: 7,
			rows: func() int { return len(g.Literals) },
			key:  func(i int) string { return iEnc(i + 1) },
			emit: func(w *lineWriter, i int) {
				r := &g.Literals[i]
				w.sid(i, iEnc(int(r.SymID)), iEnc(int(r.FileID)), tEnc(r.Kind()), tEnc(r.Value()),
					iEnc(int(r.Line)), bEnc(r.IsMagic))
			}},

		{name: "locals", ncols: 11, rows: func() int { return 0 },
			key: func(int) string { return "" }},
		{name: "markers", ncols: 6,
			rows: func() int { return len(g.Markers) },
			key:  func(i int) string { return iEnc(i + 1) },
			emit: func(w *lineWriter, i int) {
				r := &g.Markers[i]
				w.sid(i, iEnc(int(r.FileID)), iEncOpt(r.SymID, r.SymID >= 0),
					tEnc(r.Kind()), iEnc(int(r.Line)), tEnc(r.Text()))
			}},
		{name: "meta", ncols: 2,
			rows: func() int { return len(g.Meta) },
			key:  func(i int) string { return tEnc(g.Meta[i].K.Str()) },
			emit: func(w *lineWriter, i int) {
				w.s(tEnc(g.Meta[i].K.Str()), tEnc(g.Meta[i].V.Str()))
			}},
		{name: "modules", ncols: 10,
			rows: func() int { return len(g.Modules) },
			key:  func(i int) string { return iEnc(i + 1) },
			emit: func(w *lineWriter, i int) {
				r := &g.Modules[i]
				w.sid(i, tEnc(r.Name()), tEnc(r.Kind()), iEnc(int(r.NFiles)), iEnc(int(r.NSymbols)),
					iEnc(int(r.NPublic)), iEnc(int(r.Sloc)), iEnc(int(r.FanIn)),
					iEnc(int(r.FanOut)), fEnc(r.Instability))
			}},
		{name: "params", ncols: 13,
			rows: func() int { return len(g.Params) },
			key: func(i int) string {
				r := &g.Params[i]
				return iEnc(int(r.SymID)) + " " + iEnc(int(r.Pos))
			},
			emit: func(w *lineWriter, i int) {
				r := &g.Params[i]
				w.s(iEnc(int(r.SymID)), iEnc(int(r.Pos)), tEnc(r.Name()), tEnc(r.Type()),
					nullEnc, iEnc(0), iEnc(0), iEnc(0), iEnc(0), iEnc(0), iEnc(0),
					bEnc(r.IsUntyp), iEnc(int(r.Depth)))
			}},
		{name: "secret_candidates", ncols: 5,
			rows: func() int { return len(g.Secrets) },
			key:  func(i int) string { return iEnc(i + 1) },
			emit: func(w *lineWriter, i int) {
				r := &g.Secrets[i]
				w.sid(i, iEnc(int(r.SymID)), iEnc(int(r.FileID)), tEnc(r.Value()),
					iEnc(int(r.Line)))
			}},
		{name: "sig_tokens", ncols: 2,
			rows: func() int { return len(g.SigTokens) },
			key: func(i int) string {
				r := &g.SigTokens[i]
				return iEnc(int(r.SymID)) + " " + tEnc(r.Token())
			},
			emit: func(w *lineWriter, i int) {
				r := &g.SigTokens[i]
				w.s(iEnc(int(r.SymID)), tEnc(r.Token()))
			}},
		{name: "suppressions", ncols: 6,
			rows: func() int { return len(g.Suppress) },
			key:  func(i int) string { return iEnc(i + 1) },
			emit: func(w *lineWriter, i int) {
				r := &g.Suppress[i]
				w.sid(i, iEnc(int(r.FileID)), iEncOpt(r.SymID, r.SymID >= 0),
					tEnc(r.Kind()), iEnc(int(r.Line)), tEncOpt(r.Reason(), r.HasReason))
			}},

		{name: "sym_fts", ncols: 3,
			rows:      func() int { return len(g.Symbols) },
			key:       func(i int) string { return iEnc(i + 1) },
			identical: nullEnc + " " + nullEnc + " " + nullEnc},
		{name: "symbols", ncols: 15 + metricCount,
			rows: func() int { return len(g.Symbols) },
			key:  func(i int) string { return iEnc(i + 1) },
			emit: func(w *lineWriter, i int) { emitSymbol(w, g, i) }},
		{name: "ts_exports", ncols: 10,
			rows: func() int { return len(g.TSExports) },
			key:  func(i int) string { return iEnc(i + 1) },
			emit: func(w *lineWriter, i int) {
				r := &g.TSExports[i]
				w.sid(i, iEnc(int(r.FileID)), tEnc(r.Name()), tEnc(r.Kind()), iEnc(int(r.Line)),
					bEnc(r.IsDefault), bEnc(r.IsReexport), bEnc(r.IsStar),
					bEnc(r.IsTypeOnly), tEncOpt(r.Source(), r.HasSource))
			}},
		{name: "tsconfigs", ncols: 19,
			rows: func() int { return len(g.TSConfigs) },
			key:  func(i int) string { return iEnc(i + 1) },
			emit: func(w *lineWriter, i int) { emitTSConfig(w, i, &g.TSConfigs[i]) }},
		{name: "type_defs", ncols: 12,
			rows: func() int { return len(g.TypeDefs) },
			key:  func(i int) string { return iEnc(int(g.TypeDefs[i].SymID)) },
			emit: func(w *lineWriter, i int) {
				r := &g.TypeDefs[i]
				w.s(iEnc(int(r.SymID)), iEnc(int(r.NMembers)), iEnc(int(r.NOptional)),
					iEnc(int(r.NReadonly)), iEnc(int(r.NIndexSig)), iEnc(int(r.NCallSig)),
					iEnc(int(r.NExtends)), tEnc(r.ExtendsName()), iEnc(int(r.NAnyMembers)),
					bEnc(r.IsExported), bEnc(r.IsAmbient), bEnc(r.IsConstEnum))
			}},
		{name: "unresolved_calls", ncols: 4,
			rows: func() int { return len(g.Unresolved) },
			key: func(i int) string {
				r := &g.Unresolved[i]
				return iEnc(int(r.Caller)) + " " + tEnc(r.Name())
			},
			emit: func(w *lineWriter, i int) {
				r := &g.Unresolved[i]
				w.s(iEnc(int(r.Caller)), tEnc(r.Name()), iEnc(int(r.N)), iEnc(int(r.FirstLine)))
			}},
		{name: "user_input_sites", ncols: 7,
			rows: func() int { return len(g.InputSites) },
			key:  func(i int) string { return iEnc(i + 1) },
			emit: func(w *lineWriter, i int) {
				r := &g.InputSites[i]
				w.sid(i, iEnc(int(r.SymID)), iEnc(int(r.FileID)), tEnc(r.Var()),
					tEnc(r.Kind()), iEnc(int(r.Line)), bEnc(r.InLoop))
			}},
	}
}

func itoa(i int) string {
	if i == 0 {
		return "0"
	}
	neg := i < 0
	if neg {
		i = -i
	}
	var b [24]byte
	p := len(b)
	for i > 0 {
		p--
		b[p] = byte('0' + i%10)
		i /= 10
	}
	if neg {
		p--
		b[p] = '-'
	}
	return string(b[p:])
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
	{name: "awaited_calls",
		note: "a call that was awaited, and what it resolved to",
		cols: []columnShape{
			{"symbol_id", "int", false},
			{"file_id", "int", false},
			{"name", "text", false},
			{"base", "text", false},
			{"line", "int", false},
		}},
	{name: "callsites",
		note: "every distinct line a resolved call was seen on",
		cols: []columnShape{
			{"caller_id", "int", false},
			{"callee_id", "int", false},
			{"line", "int", false},
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
	{name: "listeners",
		note: "an event listener registration: target, event, handler",
		cols: []columnShape{
			{"id", "int", false},
			{"symbol_id", "int", false},
			{"file_id", "int", false},
			{"op", "text", false},
			{"target", "text", false},
			{"event", "text", false},
			{"line", "int", false},
			{"in_loop", "int", false},
			{"is_async", "int", false},
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
	{name: "sig_tokens",
		note: "the tokens of a rendered signature, for shape queries",
		cols: []columnShape{
			{"symbol_id", "int", false},
			{"token", "text", false},
		}},
	{name: "suppressions",
		note: "a lint suppression and what it silences",
		cols: []columnShape{
			{"id", "int", false},
			{"file_id", "int", false},
			{"symbol_id", "int", true},
			{"kind", "text", false},
			{"line", "int", false},
			{"reason", "text", true},
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
	{name: "ts_exports",
		note: "a re-export: the name, the source, and the kind",
		cols: []columnShape{
			{"id", "int", false},
			{"file_id", "int", false},
			{"name", "text", false},
			{"kind", "text", false},
			{"line", "int", false},
			{"is_default", "int", false},
			{"is_reexport", "int", false},
			{"is_star", "int", false},
			{"is_type_only", "int", false},
			{"source", "text", true},
		}},
	{name: "tsconfigs",
		note: "a tsconfig.json: the options it sets, resolved",
		cols: []columnShape{
			{"id", "int", false},
			{"path", "text", false},
			{"dir", "text", false},
			{"extends", "text", true},
			{"strict", "int", false},
			{"no_implicit_any", "int", false},
			{"strict_null_checks", "int", false},
			{"no_unchecked_indexed_access", "int", false},
			{"exact_optional", "int", false},
			{"verbatim_module_syntax", "int", false},
			{"isolated_modules", "int", false},
			{"erasable_syntax_only", "int", false},
			{"n_strict_flags", "int", false},
			{"target", "text", true},
			{"module", "text", true},
			{"module_resolution", "text", true},
			{"removed_option", "text", true},
			{"base_url", "text", true},
			{"paths_json", "text", true},
		}},
	{name: "type_defs",
		note: "a type or interface declaration and its members",
		cols: []columnShape{
			{"symbol_id", "int", false},
			{"n_members", "int", false},
			{"n_optional_members", "int", false},
			{"n_readonly_members", "int", false},
			{"n_index_signatures", "int", false},
			{"n_call_signatures", "int", false},
			{"n_extends", "int", false},
			{"extends_names", "text", false},
			{"n_any_members", "int", false},
			{"is_exported", "int", false},
			{"is_ambient", "int", false},
			{"is_const_enum", "int", false},
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

func symShape() []columnShape {
	out := make([]columnShape, 0, 15+metricCount)
	base := []columnShape{
		{"id", "int", false}, {"file_id", "int", false},
		{"module_id", "int", true}, {"parent_id", "int", true},
		{"name", "text", false}, {"qual_name", "text", false},
		{"kind", "text", false}, {"line_start", "int", false},
		{"line_end", "int", false}, {"n_lines", "int", false},
		{"byte_start", "int", false}, {"byte_end", "int", false},
		{"signature", "text", false}, {"return_type", "text", false},
		{"visibility", "text", false},
	}
	out = append(out, base...)
	for _, n := range metricCols {
		kind := "int"
		opt := false
		if n == "module_id" {
			opt = true
		}
		out = append(out, columnShape{n, kind, opt})
	}
	return out
}

var kindTable = []string{
	"",

	"function_declaration", "function_expression", "generator_function_declaration",
	"arrow_function", "method_definition", "method_signature", "function_signature",
	"abstract_method_signature",

	"class_declaration", "abstract_class_declaration", "interface_declaration",
	"type_alias_declaration", "enum_declaration", "internal_module", "module",

	"identifier", "property_identifier", "type_identifier",
	"private_property_identifier", "shorthand_property_identifier",

	"for_statement", "for_in_statement", "while_statement", "do_statement",
	"if_statement", "switch_statement", "try_statement", "class_body",

	"call_expression", "new_expression",

	"string", "template_string", "number", "regex", "comment",

	"binary_expression", "unary_expression", "assignment_expression",
	"augmented_assignment_expression", "update_expression", "subscript_expression",
	"member_expression", "ternary_expression", "as_expression", "satisfies_expression",
	"non_null_expression", "spread_element",

	"return_statement", "throw_statement", "catch_clause", "finally_clause",
	"switch_case", "await_expression", "yield_expression", "type_assertion",
	"optional_chain", "type_parameters", "type_arguments", "conditional_type",
	"mapped_type_clause", "template_literal_type", "index_signature", "union_type",
	"intersection_type", "object_pattern", "class_static_block", "decorator",
	"labeled_statement",

	"type_parameter", "infer_type", "index_type_query", "type_query",
	"property_signature", "predefined_type",

	"this", "template_substitution",

	"import_statement", "export_statement", "import_specifier", "export_specifier",
	"import_clause", "namespace_import",

	"variable_declarator", "public_field_definition", "field_definition", "pair",
	"lexical_declaration", "variable_declaration", "expression_statement",
	"accessibility_modifier", "override_modifier", "get", "set",
	"class_heritage", "extends_clause", "extends_type_clause", "implements_clause",
	"call_signature", "construct_signature", "ambient_declaration",
	"function", "ERROR",
}

const (
	cOther = iota
	cFunctionDeclaration
	cFunctionExpression
	cGeneratorFunctionDeclaration
	cArrowFunction
	cMethodDefinition
	cMethodSignature
	cFunctionSignature
	cAbstractMethodSignature
	cClassDeclaration
	cAbstractClassDeclaration
	cInterfaceDeclaration
	cTypeAliasDeclaration
	cEnumDeclaration
	cInternalModule
	cModule
	cIdentifier
	cPropertyIdentifier
	cTypeIdentifier
	cPrivatePropertyIdentifier
	cShorthandPropertyIdentifier
	cForStatement
	cForInStatement
	cWhileStatement
	cDoStatement
	cIfStatement
	cSwitchStatement
	cTryStatement
	cClassBody
	cCallExpression
	cNewExpression
	cString
	cTemplateString
	cNumber
	cRegex
	cComment
	cBinaryExpression
	cUnaryExpression
	cAssignmentExpression
	cAugmentedAssignmentExpression
	cUpdateExpression
	cSubscriptExpression
	cMemberExpression
	cTernaryExpression
	cAsExpression
	cSatisfiesExpression
	cNonNullExpression
	cSpreadElement
	cReturnStatement
	cThrowStatement
	cCatchClause
	cFinallyClause
	cSwitchCase
	cAwaitExpression
	cYieldExpression
	cTypeAssertion
	cOptionalChain
	cTypeParameters
	cTypeArguments
	cConditionalType
	cMappedTypeClause
	cTemplateLiteralType
	cIndexSignature
	cUnionType
	cIntersectionType
	cObjectPattern
	cClassStaticBlock
	cDecorator
	cLabeledStatement
	cTypeParameter
	cInferType
	cIndexTypeQuery
	cTypeQuery
	cPropertySignature
	cPredefinedType
	cThis
	cTemplateSubstitution
	cImportStatement
	cExportStatement
	cImportSpecifier
	cExportSpecifier
	cImportClause
	cNamespaceImport
	cVariableDeclarator
	cPublicFieldDefinition
	cFieldDefinition
	cPair
	cLexicalDeclaration
	cVariableDeclaration
	cExpressionStatement
	cAccessibilityModifier
	cOverrideModifier
	cGet
	cSet
	cClassHeritage
	cExtendsClause
	cExtendsTypeClause
	cImplementsClause
	cCallSignature
	cConstructSignature
	cAmbientDeclaration
	cFunctionExprKind
	cError
)

var codeOf = func() map[string]int16 {
	m := make(map[string]int16, len(kindTable))
	for i, s := range kindTable {
		if i == 0 {
			continue
		}
		m[s] = int16(i)
	}
	return m
}()

func init() {
	if len(kindTable) != 103 || cError != 102 {
		panic("kindTable and the code constants disagree: " + itoa(len(kindTable)))
	}
	for i, want := range map[int]string{
		cCallExpression: "call_expression", cNewExpression: "new_expression",
		cArrowFunction: "arrow_function", cIfStatement: "if_statement",
		cError: "ERROR", cFunctionExprKind: "function",
	} {
		if kindTable[i] != want {
			panic("kindTable[" + itoa(i) + "] is " + kindTable[i] + ", want " + want)
		}
	}
}

func code(name string) int16 {
	if c, ok := codeOf[name]; ok {
		return c
	}
	return cOther
}

type disp struct {
	funcKind  [512]int8
	typeKind  [512]int8
	isLoop    [512]bool
	isBranch  [512]bool
	isNest    [512]bool
	isCall    [512]bool
	isString  [512]bool
	isNumber  [512]bool
	isComment [512]bool
	isOper    [512]bool
	special   [512]bool
	counter   [512]int16
	onNode    [512]bool
	typeCnt   [512]int16
	symCode   []int16
}

const (
	fkNone = iota
	fkFunction
	fkClosure
	fkMethod
)

func buildDisp() *disp {
	d := &disp{}

	for i := range d.counter {
		d.counter[i] = -1
	}
	for i := range d.typeCnt {
		d.typeCnt[i] = -1
	}
	for name, k := range map[string]int8{
		"function_declaration":           fkFunction,
		"function_expression":            fkFunction,
		"generator_function_declaration": fkFunction,
		"arrow_function":                 fkClosure,
		"method_definition":              fkMethod,
		"method_signature":               fkMethod,
		"function_signature":             fkFunction,
		"abstract_method_signature":      fkMethod,
	} {
		d.funcKind[code(name)] = k
	}
	for name, k := range map[string]int8{
		"class_declaration":          kClass,
		"abstract_class_declaration": kClass,
		"interface_declaration":      kInterface,
		"type_alias_declaration":     kType,
		"enum_declaration":           kEnum,
		"internal_module":            kModule,
		"module":                     kModule,
	} {
		d.typeKind[code(name)] = k
	}
	for _, n := range []string{"for_statement", "for_in_statement", "while_statement", "do_statement"} {
		d.isLoop[code(n)] = true
	}
	d.isBranch[code("if_statement")] = true

	for _, n := range []string{"if_statement", "for_statement", "for_in_statement",
		"while_statement", "do_statement", "switch_statement", "try_statement",
		"arrow_function", "function_expression", "class_body"} {
		d.isNest[code(n)] = true
	}
	d.isCall[code("call_expression")] = true
	d.isCall[code("new_expression")] = true
	d.isString[code("string")] = true
	d.isString[code("template_string")] = true
	d.isNumber[code("number")] = true
	d.isComment[code("comment")] = true
	for _, n := range []string{"binary_expression", "unary_expression",
		"assignment_expression", "augmented_assignment_expression",
		"update_expression", "subscript_expression", "member_expression",
		"ternary_expression", "as_expression", "satisfies_expression",
		"non_null_expression", "spread_element"} {
		d.isOper[code(n)] = true
	}
	for i := range d.funcKind {
		d.special[i] = d.isCall[i] || d.isOper[i] || d.isString[i] ||
			d.isNumber[i] || d.isComment[i]
	}
	for name, col := range map[string]int{
		"return_statement":      mNReturns,
		"throw_statement":       mNThrow,
		"try_statement":         mNTry,
		"catch_clause":          mNCatch,
		"finally_clause":        mNFinally,
		"switch_statement":      mNSwitch,
		"switch_case":           mNCases,
		"ternary_expression":    mNTernary,
		"await_expression":      mNAwait,
		"yield_expression":      mNYield,
		"arrow_function":        mNLambda,
		"as_expression":         mNAsAssertion,
		"satisfies_expression":  mNSatisfies,
		"non_null_expression":   mNNonNull,
		"type_assertion":        mNAngleAssertion,
		"optional_chain":        mNOptionalChain,
		"spread_element":        mNSpread,
		"regex":                 mNRegexLit,
		"type_parameters":       mNGenericParams,
		"type_arguments":        mNTypeArgs,
		"conditional_type":      mNConditionalType,
		"mapped_type_clause":    mNMappedType,
		"template_literal_type": mNTemplateType,
		"index_signature":       mNIndexSignature,
		"union_type":            mNUnionType,
		"intersection_type":     mNIntersectionType,
		"object_pattern":        mNDestructure,
		"class_static_block":    mNStaticBlock,
		"decorator":             mNDecorators,
		"labeled_statement":     mNLabels,
	} {
		d.counter[code(name)] = int16(col)
	}
	for _, n := range []string{"call_expression", "member_expression",
		"binary_expression", "as_expression", "assignment_expression",
		"template_substitution", "await_expression", "this", "subscript_expression",
		"union_type", "comment", "regex"} {
		d.onNode[code(n)] = true
	}
	for name, col := range map[string]int{
		"conditional_type":      mNConditionalType,
		"mapped_type_clause":    mNMappedType,
		"template_literal_type": mNTemplateType,
		"index_signature":       mNIndexSignature,
		"intersection_type":     mNIntersectionType,
		"union_type":            mNUnionType,
		"type_parameter":        mNGenericParams,
		"type_arguments":        mNTypeArgs,
		"infer_type":            mNInfer,
		"index_type_query":      mNKeyof,
		"type_query":            mNTypeofType,
		"method_signature":      mNCallSig,
		"property_signature":    mNPropSig,
		"decorator":             mNDecorators,
	} {
		d.typeCnt[code(name)] = int16(col)
	}
	return d
}

func symbolCodes(l *langInfo) []int16 {
	out := make([]int16, 1<<16)
	for i := range 1 << 16 {
		if int(i) >= len(l.kindNames) {
			out[i] = cOther
			continue
		}

		out[i] = code(l.kindNames[i])
	}
	return out
}

func funcKindSymbol(k int8) int8 {
	switch k {
	case fkFunction:
		return kFunction
	case fkClosure:
		return kClosure
	case fkMethod:
		return kMethod
	}
	return kFunction
}

var defaultParseWorkers = runtime.GOMAXPROCS(0)

const (
	maxFileBytes = 4 * 1024 * 1024

	maxLineBytes = 1024 * 1024
)

var skipDirs = func() map[string]bool {
	names := []string{
		".git", ".hg", ".svn", ".jj", ".idea", ".vscode", ".vs", ".claude",
		"node_modules", "bower_components", "vendor", "third_party", "thirdparty",
		"external", "externals", "deps", "Godeps", "_vendor",
		"__pycache__", ".mypy_cache", ".pytest_cache", ".ruff_cache", ".tox",
		".venv", "venv", "env", ".env", "virtualenv",
		"build", "_build", "dist", "out", "target", "bin", "obj", ".gradle",
		".next", ".nuxt", ".svelte-kit", ".parcel-cache", ".turbo", ".cache",
		"coverage", "htmlcov", ".nyc_output", "site-packages",

		"lib", "types",
	}
	m := make(map[string]bool, len(names))
	for _, n := range names {
		m[n] = true
	}
	return m
}()

var langExts = map[string]bool{".ts": true, ".tsx": true, ".mts": true, ".cts": true}

var moduleRoots = map[string]bool{
	"src": true, "lib": true, "source": true, "internal": true, "pkg": true, "app": true,
}

func cgExt(name string) string {
	dot := strings.LastIndexByte(name, '.')
	if dot <= 0 {
		return ""
	}
	for i := range dot {
		if name[i] != '.' {
			return name[dot:]
		}
	}
	return ""
}

func moduleOf(rel string) string {
	parts := strings.Split(filepath.ToSlash(rel), "/")
	if len(parts) <= 1 {
		return "(root)"
	}
	head := parts[:len(parts)-1]
	if len(head) > 0 && moduleRoots[head[0]] {
		if len(head) > 3 {
			head = head[:3]
		}
	} else if len(head) > 2 {
		head = head[:2]
	}
	s := strings.Join(head, "/")
	if s == "" {
		return "(root)"
	}
	return s
}

var generatedMarkers = []string{
	"@generated", "DO NOT EDIT", "Code generated by", "AUTO-GENERATED",
	"autogenerated", "This file was automatically generated",
	"Generated by the protocol buffer compiler", "@flow-generated",
}

var testPathDirs = []string{
	"test", "tests", "test-d", "spec", "specs", "__tests__", "__snapshots__",
	"testing", "e2e", "integration-test", "integration-tests", "integration_test",
	"integration_tests", "testdata", "test_data", "test-data", "fixture", "fixtures",
}

var vendorPathDirs = []string{
	"vendor", "third_party", "thirdparty", "external", "node_modules", "deps",
}

func lowerASCII(s string) string {
	b := []byte(s)
	for i, c := range b {
		if c >= 'A' && c <= 'Z' {
			b[i] = c + 32
		}
	}
	return string(b)
}

func segMatches(parts []string, names []string) bool {
	for i := range parts {
		p := lowerASCII(parts[i])
		if slices.Contains(names, p) {
			return true
		}
	}
	return false
}

func isTestPath(rel string) bool   { return segMatches(strings.Split(rel, "/"), testPathDirs) }
func isVendorPath(rel string) bool { return segMatches(strings.Split(rel, "/"), vendorPathDirs) }

var tsTestSfx = []string{".test.", ".spec.", ".test-d.", "-test."}

func isTestName(base string) bool {
	l := lowerASCII(base)
	for _, s := range tsTestSfx {
		if strings.Contains(l, s) {
			return true
		}
	}
	return strings.HasPrefix(l, "test-")
}

var genNameSfx = []string{".min.", ".bundle.", "_pb2", ".designer."}

func isGeneratedName(name string) bool {
	l := lowerASCII(name)
	for _, s := range genNameSfx {
		if strings.Contains(l, s) {
			return true
		}
	}
	for _, g := range []string{"gen", "generated", "pb", "g"} {
		for _, sep := range []string{"-", "_", "."} {
			if strings.Contains(l, sep+g+".") {
				return true
			}
		}
	}
	if strings.HasSuffix(l, ".g.dart") {
		return true
	}
	return strings.HasPrefix(l, "zz_generated")
}

func isGeneratedHead(head string) bool {
	for _, m := range generatedMarkers {
		if strings.Contains(head, m) {
			return true
		}
	}
	return false
}

var exampleDirs = []string{"example", "examples", "sample", "samples", "demo", "demos"}
var toolDirs = []string{"tool", "tools", "script", "scripts", "cmd", "bin"}

func moduleKind(name string) string {
	parts := strings.Split(name, "/")
	switch {
	case segMatches(parts, testPathDirs):
		return "test"
	case segMatches(parts, vendorPathDirs):
		return "vendor"
	case segMatches(parts, exampleDirs):
		return "example"
	case segMatches(parts, toolDirs):
		return "tool"
	}
	return "source"
}

type pendingFile struct {
	rel      string
	full     string
	dir      string
	base     string
	ext      string
	moduleID int32
	size     int64
	isTest   bool
	isVend   bool
	fid      int32

	data     []byte
	sha      string
	tooBig   bool
	denied   bool
	isGen    bool
	nLines   int32
	nCode    int32
	nBlank   int32
	nComment int32
	maxLen   int32
	parsed   bool
}

type discoverStats struct {
	big      int
	special  int
	escaping int
	denied   int
	walkErr  int

	parsed int
}

type discoverer struct {
	g        *Graph
	root     string
	realRoot string
	modIdx   map[string]int32
	out      []pendingFile
	st       discoverStats
}

func (d *discoverer) walk(dir string) {
	ents, err := os.ReadDir(dir)
	if err != nil {
		if os.IsPermission(err) {
			d.st.denied++
		} else {
			d.st.walkErr++
		}
		return
	}
	var dirs, files []string
	for _, e := range ents {
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
	for _, fn := range files {
		if !langExts[cgExt(fn)] {
			continue
		}
		full := filepath.Join(dir, fn)
		rel, rerr := filepath.Rel(d.root, full)
		if rerr != nil {
			continue
		}
		rel = filepath.ToSlash(rel)
		if !utf8.ValidString(rel) {
			rel = cgDecode([]byte(rel))
		}
		fi, err := os.Stat(full)
		if err != nil {
			if os.IsPermission(err) {
				d.st.denied++
			}
			continue
		}
		if !fi.Mode().IsRegular() {

			d.st.special++
			continue
		}

		if rp, rerr2 := filepath.EvalSymlinks(full); rerr2 == nil {
			if rp != full && !strings.HasPrefix(rp, d.realRoot+string(filepath.Separator)) {
				d.st.escaping++
				continue
			}
		}
		mid := d.module(rel)
		dfn := filepath.ToSlash(filepath.Dir(rel))
		if dfn == "" || dfn == "." {
			dfn = "."
		}
		pf := pendingFile{
			rel: rel, full: full, dir: dfn, base: fn, ext: cgExt(fn),
			moduleID: mid, size: fi.Size(),
			isTest: isTestPath(rel) || isTestName(fn),
			isVend: isVendorPath(rel),
		}
		d.out = append(d.out, pf)
	}
	for _, sub := range dirs {
		d.walk(filepath.Join(dir, sub))
	}
}

func (d *discoverer) module(rel string) int32 {
	name := moduleOf(rel)
	if id, ok := d.modIdx[name]; ok {
		return id
	}
	id := int32(len(d.g.Modules) + 1)
	d.g.Modules = append(d.g.Modules, Module{name: cgPut(name), kind: cgPut(moduleKind(name))})
	d.modIdx[name] = id
	return id
}

func discover(g *Graph, root string, opts *Options) ([]pendingFile, discoverStats) {
	real, _ := filepath.EvalSymlinks(root)
	if real == "" {
		real = root
	}
	d := &discoverer{g: g, root: root, realRoot: real, modIdx: map[string]int32{}}
	d.walk(root)
	for i := range d.out {
		d.out[i].fid = int32(i + 1)
	}

	for i := range d.out {
		pf := &d.out[i]
		if pf.size > maxFileBytes {
			pf.tooBig = true
			d.st.big++
			pf.isGen = isGeneratedName(pf.base)
			pf.finishParsed(opts)
		}
	}
	return d.out, d.st
}

func scanBuffer(pf *pendingFile, data []byte, opts *Options) {
	h := sha1.New()
	var head []byte
	longestBytes, longestRunes := 0, 0
	curBytes, curRunes := 0, 0
	open := false

	allSpace := true
	started := false
	var first3 [3]byte
	nFirst := 0
	pendingCR := false

	skipPrefix := false
	{
		chunk := data
		n := len(chunk)
		if n > 0 {
			h.Write(chunk)
			if len(head) < 2000 {
				need := min(2000-len(head), len(chunk))
				head = append(head, chunk[:need]...)
			}

			from := 0
			if pendingCR {
				pendingCR = false
				if chunk[0] == '\n' {
					from = 1
				}
			}
			for i := from; i < n; {
				c := chunk[i]
				if c < 0x80 {
					i++
					curBytes++
					curRunes++
					open = true
					switch c {
					case '\n', '\r', '\v', '\f', 0x1c, 0x1d, 0x1e:
						curBytes--
						curRunes--
						pf.endLine(&curBytes, &curRunes, &longestBytes, &longestRunes,
							&open, allSpace, first3, nFirst, skipPrefix)
						allSpace, nFirst, started, skipPrefix = true, 0, false, false

						if c == '\r' {
							if i < n {
								if chunk[i] == '\n' {
									i++
								}
							} else {
								pendingCR = true
							}
						}
					default:

						if !started {
							if !isASCIISpace(c) {
								started = true
								allSpace = false
								first3[0] = c
								nFirst = 1
							}
						} else if nFirst < 3 {
							first3[nFirst] = c
							nFirst++
						}
					}
					continue
				}

				r, w := cgDecRune(chunk[i:])
				if w < 1 {
					w = 1
				}
				i += w

				if cgLineBreakRune(r) != 0 {
					pf.endLine(&curBytes, &curRunes, &longestBytes, &longestRunes,
						&open, allSpace, first3, nFirst, skipPrefix)
					allSpace, nFirst, started, skipPrefix = true, 0, false, false
					continue
				}
				curBytes += w
				curRunes++
				open = true
				if !started {

					if !cgSpaceRune(r) {
						started = true
						allSpace = false
						first3[0] = '?'
						nFirst = 1
						skipPrefix = true
					}
				} else if nFirst < 3 {
					nFirst++
				}
			}
		}
	}
	if open {
		pf.endLine(&curBytes, &curRunes, &longestBytes, &longestRunes,
			&open, allSpace, first3, nFirst, skipPrefix)
	}

	if pf.size == 0 {
		pf.sha = ""
	} else {
		pf.sha = hexEncode(h.Sum(nil))
	}
	pf.maxLen = int32(longestRunes)
	pf.isGen = isGeneratedName(pf.base) || isGeneratedHead(string(head))
	if longestBytes > maxLineBytes {
		pf.tooBig = true
	}
	pf.finishParsed(opts)
}

func (pf *pendingFile) endLine(cb, cr *int, lb, lr *int, open *bool,
	allSpace bool, first3 [3]byte, nFirst int, skipPrefix bool) {
	b, r := *cb, *cr
	*cb, *cr = 0, 0
	pf.nLines++
	if b > *lb {
		*lb = b
	}
	if r > *lr {
		*lr = r
	}
	*open = false
	if allSpace {
		pf.nBlank++
		return
	}
	pf.nCode++
	if skipPrefix {
		return
	}
	h := first3[:nFirst]
	for _, p := range commentLinePrefixes {
		if len(h) == len(p) && string(h) == p {
			pf.nComment++
			return
		}
	}
}

func isASCIISpace(c byte) bool {
	switch c {
	case ' ', '\t', '\n', '\v', '\f', '\r', 0x1c, 0x1d, 0x1e, 0x1f:
		return true
	}
	return false
}

func (pf *pendingFile) finishParsed(opts *Options) {
	pf.parsed = !pf.tooBig && pf.size > 0 &&
		(opts.IncludeTests || !pf.isTest) &&
		(opts.IncludeGenerated || !pf.isGen) &&
		(opts.IncludeVendored || !pf.isVend)
}

var commentLinePrefixes = []string{"//", "#", "/*", "*", "*/", "\"\"\"",
	"'''", "--", ";;", "%"}

var slocCommentPrefixes = []string{"//", "#", "/*", "*", "*/", `"""`, "'''", "--", "%"}

func slocLine(t string) bool {
	for _, p := range slocCommentPrefixes {
		if strings.HasPrefix(t, p) {
			return false
		}
	}
	return true
}

const hexDigits = "0123456789abcdef"

func hexEncode(b []byte) string {
	out := make([]byte, len(b)*2)
	for i, c := range b {
		out[i*2] = hexDigits[c>>4]
		out[i*2+1] = hexDigits[c&15]
	}
	return string(out)
}

func maxI32(a, b int32) int32 {
	if a > b {
		return a
	}
	return b
}

type Tree struct {
	cols tsCols
	n    int
	lang *langInfo

	rootHasErr bool
}

type langInfo struct {
	name      string
	kindNames []string
	fieldID   map[string]int
	disp      *disp
	errSym    uint16
}

func newLang(name string, symNames, fieldNames []string) *langInfo {
	kinds := make([]string, 1<<16)
	for i := range symNames {
		kinds[i] = symNames[i]
	}
	fields := make(map[string]int, 64)
	for f := 1; f < len(fieldNames); f++ {
		fields[fieldNames[f]] = f
	}
	return &langInfo{name: name, kindNames: kinds, fieldID: fields,
		errSym: uint16(len(symNames) - 2)}
}

func (l *langInfo) kind(sym uint16) string { return l.kindNames[sym] }

func (l *langInfo) field(name string) int { return l.fieldID[name] }

var (
	langTS  *langInfo
	langTSX *langInfo
)

var langsReady bool

func initLangs() {
	if langsReady {
		return
	}
	langsReady = true
	langTS = newLang("typescript", tsSymNames[:], tsFieldNames[:])
	langTSX = newLang("tsx", tsxSymNames[:], tsxFieldNames[:])
	langTS.disp = buildDisp()
	langTSX.disp = buildDisp()
	langTS.disp.symCode = symbolCodes(langTS)
	langTSX.disp.symCode = symbolCodes(langTSX)
	fieldsTS = resolveFields(langTS)
	fieldsTSX = resolveFields(langTSX)
}

func (t *Tree) len() int { return t.n }

func (t *Tree) sym(i int) uint16 { return t.cols.sym[i] }

func (t *Tree) kind(i int) string { return t.lang.kind(t.cols.sym[i]) }

func (t *Tree) codeAt(i int) int16 { return t.lang.disp.symCode[t.cols.sym[i]] }

func (t *Tree) start(i int) int { return int(t.cols.start[i]) }
func (t *Tree) end(i int) int   { return int(t.cols.end[i]) }
func (t *Tree) srow(i int) int  { return int(t.cols.srow[i]) }
func (t *Tree) erow(i int) int  { return int(t.cols.erow[i]) }
func (t *Tree) parent(i int) int {
	p := int(t.cols.parent[i])
	if p < 0 {
		return -1
	}
	return p
}
func (t *Tree) childCount(i int) int { return int(t.cols.nchild[i]) }
func (t *Tree) namedCount(i int) int { return int(t.cols.nnamed[i]) }

func (t *Tree) firstChild(i int) int { return int(t.cols.first[i]) }

func (t *Tree) nextSibling(i int) int { return int(t.cols.next[i]) }

func (t *Tree) namedChild(i, k int) int {
	for c := t.firstChild(i); c >= 0; c = t.nextSibling(c) {
		if t.cols.named[c] != 0 {
			if k == 0 {
				return c
			}
			k--
		}
	}
	return -1
}

func (t *Tree) prevSibling(i int) int {
	p := t.parent(i)
	if p < 0 {
		return -1
	}
	prev := -1
	for c := t.firstChild(p); c >= 0 && c != i; c = t.nextSibling(c) {
		prev = c
	}
	return prev
}

func (t *Tree) fieldChild(i, fid int) int {
	if fid == 0 {
		return -1
	}
	for c := t.firstChild(i); c >= 0; c = t.nextSibling(c) {
		if int(t.cols.field[c]) == fid {
			return c
		}
	}
	return -1
}

func (t *Tree) text(i int, s srcFile) string { return s.str(t.start(i), t.end(i)) }

func (t *Tree) textN(i int, s srcFile, n int) string {
	return s.strN(t.start(i), t.end(i), n)
}

func buildTree(ft *tsTree, useTSX bool) *Tree {
	if ft == nil || ft.failed {
		return &Tree{}
	}
	return &Tree{cols: ft.cols, n: len(ft.cols.sym), lang: langInfoOf(useTSX), rootHasErr: ft.rootHasErr}
}

func langInfoOf(tsx bool) *langInfo {
	if tsx {
		return langTSX
	}
	return langTS
}

const tsGrammarVersion = "cli-0.25.10+typescript-0.23.2"

type fieldIDs struct {
	body, parameters, returnType, name, left, key, value, defaultValue int
	typeF, alternative, function, constructor, arguments, property     int
	object, operator, index, declaration, source, alias, importClause  int
	typeParams                                                         int
}

var (
	fieldsTS  fieldIDs
	fieldsTSX fieldIDs
)

func resolveFields(l *langInfo) fieldIDs {
	f := fieldIDs{
		body: l.field("body"), parameters: l.field("parameters"),
		returnType: l.field("return_type"), name: l.field("name"),
		left: l.field("left"), key: l.field("key"), value: l.field("value"),
		typeParams:   l.field("type_parameters"),
		defaultValue: l.field("default_value"), typeF: l.field("type"),
		alternative: l.field("alternative"), function: l.field("function"),
		constructor: l.field("constructor"), arguments: l.field("arguments"),
		property: l.field("property"), object: l.field("object"),
		operator: l.field("operator"), index: l.field("index"),
		declaration: l.field("declaration"), source: l.field("source"),
		alias: l.field("alias"), importClause: l.field("import_clause"),
	}
	return f
}

func (t *Tree) f() fieldIDs {
	if t.lang == langTSX {
		return fieldsTSX
	}
	return fieldsTS
}

func (t *Tree) body(i int) int {
	c := t.fieldChild(i, t.f().body)
	if c < 0 {
		return i
	}
	return c
}

func (t *Tree) memberField(i, fid int) int {
	if c := t.fieldChild(i, fid); c >= 0 {
		return c
	}
	for c := t.firstChild(i); c >= 0; c = t.nextSibling(c) {
		if r := t.fieldChild(c, fid); r >= 0 {
			return r
		}
	}
	return -1
}

func isWordByte(c byte) bool {
	return c == '_' || (c >= '0' && c <= '9') || (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')
}

func isWordRune(r rune) bool {
	return r == '_' || (r >= '0' && r <= '9') || (r >= 'a' && r <= 'z') ||
		(r >= 'A' && r <= 'Z') || r > 127
}

func lowerByte(c byte) byte {
	if c >= 'A' && c <= 'Z' {
		return c + 32
	}
	return c
}

func eqFold(a, b byte) bool { return lowerByte(a) == lowerByte(b) }

var markerWords = []string{
	"TODO", "FIXME", "XXX", "HACK", "BUG", "NOTE", "WARNING", "OPTIMIZE",
	"REVIEW", "DEPRECATED", "SAFETY", "PANIC", "UNSAFE",
}

func matchMarker(line string) string {
	i, n := 0, len(line)
	for i < n {
		if !isWordByte(line[i]) {
			i++
			continue
		}
		start := i
		for i < n && isWordByte(line[i]) {
			i++
		}
		word := line[start:i]
		for _, w := range markerWords {
			if len(w) != len(word) || !eqFoldStr(word, w) {
				continue
			}
			j := i
			for j < n && (line[j] == ' ' || line[j] == '\t') {
				j++
			}
			if j < n && (line[j] == ':' || line[j] == '-' || line[j] == '(') {
				return w
			}
		}
	}
	return ""
}

func eqFoldStr(a, b string) bool {
	if len(a) != len(b) {
		return false
	}
	for i := 0; i < len(a); i++ {
		if !eqFold(a[i], b[i]) {
			return false
		}
	}
	return true
}

func markerLineGate(line string) bool {
	return strings.Contains(line, "//") || strings.Contains(line, "#") ||
		strings.Contains(line, "*") || strings.Contains(line, "--")
}

type suppressKind struct {
	group string
	kind  string
}

var suppressNeedles = []suppressKind{
	{"@ts-ignore", "ts-ignore"},
	{"@ts-expect-error", "ts-expect-error"},
	{"@ts-nocheck", "ts-nocheck"},
	{"eslint-disable-next-line", "eslint-disable"},
	{"eslint-disable", "eslint-disable"},
}

func matchSuppress(line string) (suppressKind, bool) {
	best := -1
	var hit suppressKind
	for _, n := range suppressNeedles {
		if idx := strings.Index(line, n.group); idx >= 0 && (best < 0 || idx < best) {
			best, hit = idx, n
		}
	}
	return hit, best >= 0
}

func countAny(s string) int {
	n := 0
	for i := 0; i+3 <= len(s); i++ {
		if s[i] != 'a' || s[i+1] != 'n' || s[i+2] != 'y' {
			continue
		}
		if i > 0 && isWordRune(rune(s[i-1])) {
			continue
		}
		if i+3 < len(s) && isWordRune(rune(s[i+3])) {
			continue
		}
		n++
		i += 2
	}
	return n
}

func hasAny(s string) bool {
	for i := 0; i+3 <= len(s); i++ {
		if s[i] != 'a' || s[i+1] != 'n' || s[i+2] != 'y' {
			continue
		}
		if i > 0 && isWordRune(rune(s[i-1])) {
			continue
		}
		if i+3 < len(s) && isWordRune(rune(s[i+3])) {
			continue
		}
		return true
	}
	return false
}

func hasAnyTail(s string) bool {
	if len(s) > 24 {
		s = s[len(s)-24:]
	}
	return hasAny(s)
}

func hasAnyWord(s string, words ...string) bool {
	for i := 0; i < len(s); i++ {
		if !isWordByte(s[i]) {
			continue
		}
		if i > 0 && isWordByte(s[i-1]) {
			continue
		}
		for _, w := range words {
			if i+len(w) <= len(s) && s[i:i+len(w)] == w {
				j := i + len(w)
				if j >= len(s) || !isWordByte(s[j]) {
					return true
				}
			}
		}
	}
	return false
}

func isHandlerShape(params string) bool {
	return hasAnyWord(params, "req", "request", "ctx", "event") &&
		hasAnyWord(params, "res", "response", "reply")
}

var secretNeedles = []string{
	"api_key", "api-key", "apikey", "secret", "password", "passwd", "pwd",
	"token", "bearer", "access_key", "access-key", "accesskey",
	"private_key", "private-key", "privatekey", "client_secret", "client-secret",
	"clientsecret", "auth_token", "auth-token", "authtoken", "jwt",
	"credential", "smtp_pass", "smtp-pass", "smtppass", "db_pass", "db-pass",
	"dbpass", "sk_live", "rk_live", "pk_live", "ghp_", "xoxb-", "akia",
}

var secretLower []string

func init() {
	secretLower = make([]string, len(secretNeedles))
	for i, n := range secretNeedles {
		secretLower[i] = strings.ToLower(n)
	}
}

func looksLikeSecret(s string) bool {
	l := strings.ToLower(s)
	for _, n := range secretLower {
		if strings.Contains(l, n) {
			return true
		}
	}
	return false
}

var redosShape = regexp.MustCompile(`\([^)]*[+*]\)[+*]|\[[^\]]*\][+*][+*]|\(\?:[^)]*[+*]\)[+*]`)

func isRedosShape(s string) bool { return redosShape.MatchString(s) }

var numLiteral = regexp.MustCompile(`^[-+]?(?:0[xXbBoO][0-9a-fA-F_]+|[\d_]+(?:\.[\d_]*)?(?:[eE][-+]?\d+)?)[uUlLfFdD]*$`)

func isNumberLiteral(s string) bool { return numLiteral.MatchString(s) }

var magicAllowed = map[string]bool{}

func init() {
	for _, v := range []string{"0", "1", "2", "-1", "10", "100", "1000", "8", "16",
		"32", "64", "128", "256", "512", "1024", "255", "65535", "4096", "24",
		"60", "365", "7", "12", "3", "4", "6",
		"0x0", "0x1", "0xff", "0xFF", "0.0", "1.0", "-1", ""} {
		magicAllowed[v] = true
	}
}

func isMagicNumber(txt string) bool {
	return !magicAllowed[txt] && isNumberLiteral(txt)
}

func sigTokenOK(c byte) bool {
	return c == '_' || c == '$' || (c >= '0' && c <= '9') ||
		(c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')
}

func sigTokenStart(c byte) bool {
	return c == '_' || c == '$' || (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')
}

func forEachSigToken(s string, fn func(tok string)) {
	i := 0
	for i < len(s) {
		if !sigTokenStart(s[i]) {
			i++
			continue
		}
		j := i
		for j < len(s) && sigTokenOK(s[j]) {
			j++
		}
		fn(s[i:j])
		i = j
	}
}

func typeDepth(s string) int {
	best, d := 0, 0
	for i := 0; i < len(s); i++ {
		switch s[i] {
		case '<':
			d++
			if d > best {
				best = d
			}
		case '>':
			if d > 0 {
				d--
			}
		}
	}
	return best
}

func cgSpaceByte(c byte) bool {
	switch c {
	case ' ', '\t', '\n', '\v', '\f', '\r', 0x1c, 0x1d, 0x1e, 0x1f:
		return true
	}
	return false
}

func cgSpaceRune(r rune) bool {
	switch r {
	case ' ', '\t', '\n', '\v', '\f', '\r', 0x1c, 0x1d, 0x1e, 0x1f,
		0x85, 0xa0, 0x1680, 0x2028, 0x2029, 0x202f, 0x205f, 0x3000:
		return true
	}
	return r >= 0x2000 && r <= 0x200a
}

func cgStripBytes(b []byte) []byte {
	i, j := 0, len(b)
	for i < j && cgSpaceByte(b[i]) {
		i++
	}
	for j > i && cgSpaceByte(b[j-1]) {
		j--
	}
	return b[i:j]
}

func cgStrip(s string) string { return strings.TrimFunc(s, cgSpaceRune) }

func cgLStrip(s string) string { return strings.TrimLeftFunc(s, cgSpaceRune) }

func cgLineBreakRune(r rune) int {
	switch r {
	case '\r':
		return 1
	case '\n', '\v', '\f', 0x1c, 0x1d, 0x1e, 0x85, 0x2028, 0x2029:
		return 1
	}
	return 0
}

func cgSplitLinesRunes(s string) []string {
	var out []string
	start := 0
	for i := 0; i < len(s); {
		r, w := utf8.DecodeRuneInString(s[i:])
		if cgLineBreakRune(r) == 0 {
			i += w
			continue
		}
		out = append(out, s[start:i])
		i += w
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

type srcFile struct {
	data  []byte
	ascii bool

	lossy bool
}

func newSrc(data []byte) srcFile {
	valid := utf8.Valid(data)
	return srcFile{data: data, ascii: valid && isASCII(data), lossy: !valid}
}

func cgDecRune(b []byte) (rune, int) {
	if len(b) == 0 {
		return 0, 0
	}
	c := b[0]
	if c < 0x80 {
		return rune(c), 1
	}
	var need int
	lo, hi := byte(0x80), byte(0xBF)
	switch {
	case c >= 0xC2 && c <= 0xDF:
		need = 1
	case c == 0xE0:
		need, lo = 2, 0xA0
	case c >= 0xE1 && c <= 0xEC:
		need = 2
	case c == 0xED:
		need, hi = 2, 0x9F
	case c >= 0xEE && c <= 0xEF:
		need = 2
	case c == 0xF0:
		need, lo = 3, 0x90
	case c >= 0xF1 && c <= 0xF3:
		need = 3
	case c == 0xF4:
		need, hi = 3, 0x8F
	default:
		return 0xFFFD, 1
	}
	got := 0
	for k := 0; k < need; k++ {
		j := 1 + k
		if j >= len(b) {
			break
		}
		t := b[j]
		if k == 0 {
			if t < lo || t > hi {
				break
			}
		} else if t < 0x80 || t > 0xBF {
			break
		}
		got = k + 1
	}
	if got == need {
		r, _ := utf8.DecodeRune(b[:1+need])
		return r, 1 + need
	}
	return 0xFFFD, 1 + got
}

func cgDecode(b []byte) string {
	if utf8.Valid(b) {
		return string(b)
	}
	var out strings.Builder
	out.Grow(len(b))
	for i := 0; i < len(b); {
		r, w := cgDecRune(b[i:])
		out.WriteRune(r)
		i += w
	}
	return out.String()
}

func isASCII(b []byte) bool {
	for _, c := range b {
		if c >= 0x80 {
			return false
		}
	}
	return true
}

func (s srcFile) str(a, b int) string {
	if s.lossy {
		return cgDecode(s.data[a:b])
	}
	return string(s.data[a:b])
}

func (s srcFile) strN(a, b, n int) string {
	if a >= b {
		return ""
	}
	if s.ascii {
		if b-a > n {
			b = a + n
		}
		return string(s.data[a:b])
	}
	t := s.data[a:b]
	if s.lossy {
		return cutStr(cgDecode(t), n)
	}
	if utf8.RuneCount(t) <= n {
		return string(t)
	}
	cut := 0
	for range n {
		_, w := utf8.DecodeRune(t[cut:])
		cut += w
	}
	return string(t[:cut])
}

func (s srcFile) strStripN(a, b, n int) string {
	if a >= b {
		return ""
	}
	if s.ascii {
		t := cgStripBytes(s.data[a:b])
		if len(t) > n {
			t = t[:n]
		}
		return string(t)
	}
	return cgStripN(string(s.data[a:b]), n)
}

func cgStripN(s string, n int) string {
	return cutStr(cgStrip(s), n)
}

func cutStr(s string, n int) string {
	if n <= 0 {
		return ""
	}
	if len(s) <= n {
		return s
	}
	i := 0
	for range n {
		if i >= len(s) {
			return s
		}
		_, w := utf8.DecodeRuneInString(s[i:])
		if w == 0 {
			return s
		}
		i += w
	}
	if i >= len(s) {
		return s
	}
	return s[:i]
}

func countStr(s, sub string) int {
	if sub == "" {
		return len([]rune(s)) + 1
	}
	return strings.Count(s, sub)
}

func trimSet(s, set string) string {
	return strings.Trim(s, set)
}

func lstripSet(s, set string) string { return strings.TrimLeft(s, set) }

func cgFloat(f float64) string {
	switch {
	case f != f:
		return "nan"
	case f > 1.7976931348623157e308:
		return "inf"
	case f < -1.7976931348623157e308:
		return "-inf"
	}
	neg := false
	if f < 0 || (f == 0 && strconv.FormatFloat(f, 'b', -1, 64)[0] == '-') {
		neg = true
		f = -f
	}
	if f == 0 {
		if neg {
			return "-0.0"
		}
		return "0.0"
	}

	sci := strconv.FormatFloat(f, 'e', -1, 64)
	epos := strings.IndexByte(sci, 'e')
	mant := sci[:epos]
	exp, _ := strconv.Atoi(sci[epos+1:])
	digits := strings.Replace(mant, ".", "", 1)

	digits = strings.TrimRight(digits, "0")
	if digits == "" {
		digits = "0"
	}
	decpt := exp + 1
	var out string
	if decpt <= -4 || decpt > 16 {
		var b strings.Builder
		b.WriteByte(digits[0])
		if len(digits) > 1 {
			b.WriteByte('.')
			b.WriteString(digits[1:])
		}
		b.WriteByte('e')
		e := decpt - 1
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
		out = b.String()
	} else if decpt <= 0 {
		out = "0." + strings.Repeat("0", -decpt) + digits
	} else if decpt >= len(digits) {
		out = digits + strings.Repeat("0", decpt-len(digits)) + ".0"
	} else {
		out = digits[:decpt] + "." + digits[decpt:]
	}
	if neg {
		return "-" + out
	}
	return out
}

func truncInt(f float64) int64 {
	if f < 0 {
		return -int64(-f)
	}
	return int64(f)
}

func ltrimSet(s, set string) string {
	i := 0
	for i < len(s) && strings.IndexByte(set, s[i]) >= 0 {
		i++
	}
	return s[i:]
}

func cgJSONDumps(v any) string {
	var b strings.Builder
	cgDumpValue(&b, v)
	return b.String()
}

func cgDumpValue(b *strings.Builder, v any) {
	switch t := v.(type) {
	case nil:
		b.WriteString("null")
	case bool:
		if t {
			b.WriteString("true")
		} else {
			b.WriteString("false")
		}
	case string:
		cgDumpString(b, t)
	case json.Number:
		b.WriteString(t.String())
	case float64:
		b.WriteString(cgFloatRepr(t))
	case []any:
		b.WriteByte('[')
		for i, e := range t {
			if i > 0 {
				b.WriteByte(',')
			}
			cgDumpValue(b, e)
		}
		b.WriteByte(']')
	case map[string]any:
		keys := make([]string, 0, len(t))
		for k := range t {
			keys = append(keys, k)
		}
		sort.Strings(keys)
		b.WriteByte('{')
		for i, k := range keys {
			if i > 0 {
				b.WriteByte(',')
			}
			cgDumpString(b, k)
			b.WriteByte(':')
			cgDumpValue(b, t[k])
		}
		b.WriteByte('}')
	default:
		b.WriteString("null")
	}
}

func cgDumpString(b *strings.Builder, s string) {
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
				b.WriteString(`\u00`)
				const hex = "0123456789abcdef"
				b.WriteByte(hex[byte(r)>>4])
				b.WriteByte(hex[byte(r)&0xF])
			case r < 0x7f:
				b.WriteRune(r)
			case r > 0xFFFF:
				hi, lo := utf16.EncodeRune(r)
				b.WriteString(`\u`)
				b.WriteByte(hexDigit(hi >> 8))
				b.WriteByte(hexDigit(hi))
				b.WriteByte(hexDigit(lo >> 8))
				b.WriteByte(hexDigit(lo))
			default:
				b.WriteString(`\u`)
				b.WriteByte(hexDigit(r >> 8))
				b.WriteByte(hexDigit(r))
			}
		}
	}
	b.WriteByte('"')
}

func hexDigit(c rune) byte {
	const hex = "0123456789abcdef"
	return hex[c&0xF]
}

func cgFloatRepr(f float64) string {
	if math.IsInf(f, 1) {
		return "Infinity"
	}
	if math.IsInf(f, -1) {
		return "-Infinity"
	}
	if math.IsNaN(f) {
		return "NaN"
	}

	s := strconv.FormatFloat(f, 'g', -1, 64)
	if s == "" {
		return "0.0"
	}
	if !strings.ContainsAny(s, ".eE") {
		s += ".0"
	}
	return s
}

func cgRepr(v any) string {
	switch t := v.(type) {
	case nil:
		return "None"
	case bool:
		if t {
			return "True"
		}
		return "False"
	case string:
		return cgStrRepr(t)
	case json.Number:
		return t.String()
	case float64:
		return cgFloatRepr(t)
	case []any:
		parts := make([]string, len(t))
		for i, e := range t {
			parts[i] = cgRepr(e)
		}
		return "[" + strings.Join(parts, ", ") + "]"
	case map[string]any:
		keys := make([]string, 0, len(t))
		for k := range t {
			keys = append(keys, k)
		}
		sort.Strings(keys)
		parts := make([]string, len(keys))
		for i, k := range keys {
			parts[i] = cgStrRepr(k) + ": " + cgRepr(t[k])
		}
		return "{" + strings.Join(parts, ", ") + "}"
	}
	return ""
}

func cgStrRepr(s string) string {
	quote := byte('\'')
	if strings.Contains(s, "'") && !strings.Contains(s, `"`) {
		quote = '"'
	}
	var b strings.Builder
	b.WriteByte(quote)
	for i := 0; i < len(s); {
		c := s[i]
		if c < utf8.RuneSelf {
			i++
			switch c {
			case '\\':
				b.WriteString(`\\`)
			case '\n':
				b.WriteString(`\n`)
			case '\r':
				b.WriteString(`\r`)
			case '\t':
				b.WriteString(`\t`)
			default:
				if c == quote {
					b.WriteByte('\\')
					b.WriteByte(c)
				} else if c < 0x20 || c == 0x7f {
					const hex = "0123456789abcdef"
					b.WriteString(`\x`)
					b.WriteByte(hex[c>>4])
					b.WriteByte(hex[c&0xF])
				} else {
					b.WriteByte(c)
				}
			}
			continue
		}
		r, sz := utf8.DecodeRuneInString(s[i:])
		if r == utf8.RuneError && sz == 1 {
			b.WriteString(`\x`)
			const hex = "0123456789abcdef"
			b.WriteByte(hex[c>>4])
			b.WriteByte(hex[c&0xF])
			i++
			continue
		}
		b.WriteString(s[i : i+sz])
		i += sz
	}
	b.WriteByte(quote)
	return b.String()
}

type queryDef struct {
	Name  string
	Title string
	Notes string
	Run   func(g *Graph, mod string, lim int) *table
}

var queries []queryDef
var metrics []queryDef

func likeMatch(pat, s string) bool {
	pi, si := 0, 0
	star, mark := -1, 0
	for si < len(s) {
		switch {
		case pi < len(pat) && (lowerByte(pat[pi]) == lowerByte(s[si]) || pat[pi] == '_'):
			pi++
			si++
		case pi < len(pat) && pat[pi] == '%':
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
	for pi < len(pat) && pat[pi] == '%' {
		pi++
	}
	return pi == len(pat)
}

func (g *Graph) modOK(mid int32, mod string) bool {
	if mod == "%" {
		return true
	}
	if mid <= 0 || int(mid) > len(g.Modules) {
		return likeMatch(mod, "")
	}
	return likeMatch(mod, g.Modules[mid-1].Name())
}

func (g *Graph) isCallKind(k int8) bool {
	return k == kFunction || k == kMethod || k == kClosure
}

func lim(t *table, n int) *table {
	if n >= 0 && len(t.rows) > n {
		t.rows = t.rows[:n]
	}
	return t
}

func sortRows(t *table, less func(a, b []cell) bool) {
	sort.SliceStable(t.rows, func(i, j int) bool { return less(t.rows[i], t.rows[j]) })
}

func gcDistinct(dst *[]string, seen map[string]bool, v string) {
	if seen[v] {
		return
	}
	seen[v] = true
	*dst = append(*dst, v)
}

func joinDistinct(v []string) string { return strings.Join(v, ",") }

type adjacency struct {
	outOff []int32
	outTo  []int32
	inOff  []int32
	inFrom []int32
}

func (g *Graph) adj() *adjacency {
	if g.adjCache != nil {
		return g.adjCache
	}
	n := int32(len(g.Symbols)) + 1
	a := &adjacency{outOff: make([]int32, n+2), inOff: make([]int32, n+2)}
	ne := int32(len(g.Edges))
	a.outTo = make([]int32, ne)
	a.inFrom = make([]int32, ne)
	for i := range g.Edges {
		e := &g.Edges[i]
		if e.Self {
			continue
		}
		a.outOff[e.Caller+1]++
		a.inOff[e.Callee+1]++
	}
	for i := int32(1); i <= n; i++ {
		a.outOff[i] += a.outOff[i-1]
		a.inOff[i] += a.inOff[i-1]
	}
	oc := append([]int32(nil), a.outOff...)
	ic := append([]int32(nil), a.inOff...)
	for i := range g.Edges {
		e := &g.Edges[i]
		if e.Self {
			continue
		}
		a.outTo[oc[e.Caller]] = e.Callee
		oc[e.Caller]++
		a.inFrom[ic[e.Callee]] = e.Caller
		ic[e.Callee]++
	}
	g.adjCache = a
	return a
}

func (g *Graph) bfsDepth(roots []int32, maxDepth int, test func(int32) bool) map[int32]int {
	a := g.adj()
	depth := make(map[int32]int, len(roots))
	frontier := make([]int32, 0, len(roots))
	for _, r := range roots {
		if _, ok := depth[r]; !ok {
			depth[r] = 0
			frontier = append(frontier, r)
		}
	}
	cur := frontier
	for d := 0; d < maxDepth && len(cur) > 0; d++ {
		var next []int32
		for _, u := range cur {
			for k := a.outOff[u]; k < a.outOff[u+1]; k++ {
				v := a.outTo[k]
				if _, ok := depth[v]; ok {
					continue
				}
				depth[v] = d + 1
				if test == nil || test(v) {
					next = append(next, v)
				}
			}
		}
		cur = next
	}
	return depth
}

func (g *Graph) entryRoots(isTest bool) []int32 {
	var roots []int32
	for i := range g.Symbols {
		s := &g.Symbols[i]
		m := g.metrics(int32(i + 1))
		if m[mIsExported] == 1 || m[mIsHandler] == 1 || m[mIsEntrypoint] == 1 {
			if !isTest && g.Files[s.FileID-1].IsTest {
				continue
			}
			roots = append(roots, int32(i+1))
		}
	}
	return roots
}

func init() {
	queries = append(buildQueries(), buildQueriesB()...)
	metrics = buildMetricsList()
	for i := range queries {
		queries[i].Title, queries[i].Notes = qTitles[i], qNotes[i]
	}
	for i := range metrics {
		metrics[i].Title, metrics[i].Notes = mTitles[i], mNotes[i]
	}
	if len(queries) != 80 || len(metrics) != 29 {
		panic("catalogue size changed: " + itoa(len(queries)) + " queries, " +
			itoa(len(metrics)) + " metrics")
	}
}

const (
	colAt   = -1
	colName = -2
	colQual = -3
	colKind = -4
	colRet  = -5
	colPar  = -6
	colLine = -7

	colScore = -8
)

type ordKey struct {
	col  int
	desc bool
}

type scanOrder struct {
	kind scanKind
	mcol int
}

type scanKind int

const (
	scanID scanKind = iota
	scanFileLine
	scanFileKind
	scanKindID
	scanIdxAsc
	scanIdxDesc
	scanPathLine
	scanPathKind
	scanNameFile
)

var kindTextRank = [8]int8{3, 1, 5, 0, 4, 7, 2, 6}

func kindRankLT(a, b int8) bool { return kindTextRank[a] < kindTextRank[b] }

func (g *Graph) scanIds(o scanOrder) []int32 {
	if g.scanCache == nil {
		g.scanCache = map[scanOrder][]int32{}
	}
	if v, ok := g.scanCache[o]; ok {
		return v
	}
	ids := make([]int32, len(g.Symbols))
	for i := range ids {
		ids[i] = int32(i + 1)
	}
	less := func(a, b int32) bool { return a < b }
	switch o.kind {
	case scanFileLine, scanPathLine:
		less = func(a, b int32) bool {
			sa, sb := &g.Symbols[a-1], &g.Symbols[b-1]
			if sa.FileID != sb.FileID {
				if o.kind == scanFileLine {
					return sa.FileID < sb.FileID
				}
				return g.Files[sa.FileID-1].Path() < g.Files[sb.FileID-1].Path()
			}
			if sa.LineStart != sb.LineStart {
				return sa.LineStart < sb.LineStart
			}
			return a < b
		}
	case scanFileKind, scanPathKind:
		less = func(a, b int32) bool {
			sa, sb := &g.Symbols[a-1], &g.Symbols[b-1]
			if sa.FileID != sb.FileID {
				if o.kind == scanFileKind {
					return sa.FileID < sb.FileID
				}
				return g.Files[sa.FileID-1].Path() < g.Files[sb.FileID-1].Path()
			}
			if sa.Kind != sb.Kind {
				return kindRankLT(sa.Kind, sb.Kind)
			}
			return a < b
		}
	case scanKindID:

		less = func(a, b int32) bool {
			sa, sb := &g.Symbols[a-1], &g.Symbols[b-1]
			if sa.Kind != sb.Kind {
				return kindRankLT(sa.Kind, sb.Kind)
			}
			if sa.Name() != sb.Name() {
				return sa.Name() < sb.Name()
			}
			return a < b
		}
	case scanNameFile:

		less = func(a, b int32) bool {
			sa, sb := &g.Symbols[a-1], &g.Symbols[b-1]
			if sa.Name() != sb.Name() {
				return sa.Name() < sb.Name()
			}
			if sa.FileID != sb.FileID {
				return sa.FileID < sb.FileID
			}
			return a < b
		}
	case scanIdxAsc, scanIdxDesc:

		less = func(a, b int32) bool {
			ma, mb := g.metrics(a)[o.mcol], g.metrics(b)[o.mcol]
			if ma != mb {
				if o.kind == scanIdxAsc {
					return ma < mb
				}
				return ma > mb
			}
			sa, sb := &g.Symbols[a-1], &g.Symbols[b-1]
			if sa.Name() != sb.Name() {
				return sa.Name() < sb.Name()
			}
			if sa.FileID != sb.FileID {
				return sa.FileID < sb.FileID
			}

			return a < b
		}
	}
	sort.Slice(ids, func(x, y int) bool { return less(ids[x], ids[y]) })
	g.scanCache[o] = ids
	return ids
}

func symQ(cols []string, proj []int, pred func([]int32) bool, order []ordKey,
	noTest, noGen bool, keep func(*Symbol) bool, scan ...scanOrder) func(*Graph, string, int) *table {
	so := scanOrder{}
	if len(scan) > 0 {
		so = scan[0]
	}
	return func(g *Graph, mod string, n int) *table {
		t := &table{cols: cols}
		row := make([]cell, len(proj))
		_ = 0
		for _, sid := range g.scanIds(so) {
			i := int(sid - 1)
			s := &g.Symbols[i]
			m := g.metrics(sid)
			if !pred(m) {
				continue
			}
			if keep != nil && !keep(s) {
				continue
			}
			f := &g.Files[s.FileID-1]
			if noTest && f.IsTest {
				continue
			}
			if noGen && f.IsGen {
				continue
			}
			if !g.modOK(s.ModuleID, mod) {
				continue
			}
			for j, p := range proj {
				switch p {
				case colAt:
					row[j] = cs(g.at(s))
				case colName:
					row[j] = cs(s.Name())
				case colQual:
					row[j] = cs(s.QualName())
				case colKind:
					row[j] = cs(kindNames[s.Kind])
				case colRet:
					row[j] = cs(s.RetType())
				default:
					row[j] = ci32(m[p])
				}
			}
			t.rows = append(t.rows, append([]cell(nil), row...))
		}
		sortRows(t, func(a, b []cell) bool {
			for _, k := range order {
				x, y := num(a[k.col]), num(b[k.col])
				if x == y {
					continue
				}
				if k.desc {
					return x > y
				}
				return x < y
			}
			return false
		})
		return lim(t, n)
	}
}

func symQ2(cols []string, proj []int, pred func([]int32) bool,
	score, score2 func([]int32) int, order []ordKey,
	noTest, noGen bool, keep func(*Symbol) bool, scan ...scanOrder) func(*Graph, string, int) *table {
	so := scanOrder{}
	if len(scan) > 0 {
		so = scan[0]
	}
	return func(g *Graph, mod string, n int) *table {
		t := &table{cols: cols}
		row := make([]cell, len(proj))
		scores := make([]int, 0, 256)
		scores2 := make([]int, 0, 256)
		for _, sid := range g.scanIds(so) {
			i := int(sid - 1)
			s := &g.Symbols[i]
			m := g.metrics(sid)
			if !pred(m) {
				continue
			}
			if keep != nil && !keep(s) {
				continue
			}
			f := &g.Files[s.FileID-1]
			if noTest && f.IsTest {
				continue
			}
			if noGen && f.IsGen {
				continue
			}
			if !g.modOK(s.ModuleID, mod) {
				continue
			}

			var sc, sc2 int
			if score != nil {
				sc = score(m)
			}
			if score2 != nil {
				sc2 = score2(m)
			}
			for j, p := range proj {
				switch p {
				case colAt:
					row[j] = cs(g.at(s))
				case colName:
					row[j] = cs(s.Name())
				case colQual:
					row[j] = cs(s.QualName())
				case colKind:
					row[j] = cs(kindNames[s.Kind])
				case colRet:
					row[j] = cs(s.RetType())
				case colPar:
					row[j] = g.parentCell(s)
				case colLine:
					row[j] = ci32(s.LineStart)
				case colScore:
					row[j] = ci32(int32(sc))
				default:
					row[j] = ci32(m[p])
				}
			}
			t.rows = append(t.rows, append([]cell(nil), row...))
			if score != nil {
				scores = append(scores, sc)
			}
			if score2 != nil {
				scores2 = append(scores2, sc2)
			}
		}

		idx := make([]int, len(t.rows))
		for i := range idx {
			idx[i] = i
		}
		sort.SliceStable(idx, func(a, b int) bool {
			ra, rb := idx[a], idx[b]
			if score != nil && scores[ra] != scores[rb] {
				return scores[ra] > scores[rb]
			}
			if score2 != nil && scores2[ra] != scores2[rb] {
				return scores2[ra] > scores2[rb]
			}
			A, B := t.rows[ra], t.rows[rb]
			for _, k := range order {
				x, y := num(A[k.col]), num(B[k.col])
				if x == y {
					continue
				}
				if k.desc {
					return x > y
				}
				return x < y
			}
			return false
		})
		rows := make([][]cell, len(t.rows))
		for i, j := range idx {
			rows[i] = t.rows[j]
		}
		t.rows = rows
		return lim(t, n)
	}
}

func scoreOf(a, b int) func([]int32) int {
	return func(m []int32) int { return int(m[a]) + int(m[b]) }
}

func oneOf(a int) func([]int32) int {
	return func(m []int32) int { return int(m[a]) }
}

func (g *Graph) parentCell(s *Symbol) cell {
	if s.ParentID <= 0 {
		return cnull()
	}
	return cs(g.Symbols[s.ParentID-1].Name())
}

func (g *Graph) parentName(s *Symbol) string {
	if s.ParentID <= 0 {
		return ""
	}
	return g.Symbols[s.ParentID-1].Name()
}

func lineOf(at string) int {
	k := lastIndexByte(at, ':')
	if k < 0 {
		return 0
	}
	v := 0
	for i := k + 1; i < len(at); i++ {
		if at[i] < '0' || at[i] > '9' {
			return 0
		}
		v = v*10 + int(at[i]-'0')
	}
	return v
}

func (g *Graph) at(s *Symbol) string {
	return g.Files[s.FileID-1].Path() + ":" + strconv.Itoa(int(s.LineStart))
}

func g_isCallKind(k int8) bool {
	return k == kFunction || k == kMethod || k == kClosure
}

func cs2(s string) cell { return cs(s) }

type tokenUse struct {
	first int32
	n     int32
}

func (g *Graph) sigTokenUse() map[string]tokenUse {
	if g.tokUse != nil {
		return g.tokUse
	}
	m := make(map[string]tokenUse, len(g.SigTokens))
	for i := range g.SigTokens {
		st := &g.SigTokens[i]
		e := m[st.Token()]
		if e.n == 0 {
			e.first = st.SymID
		}
		e.n++
		m[st.Token()] = e
	}
	g.tokUse = m
	return m
}

func maxi(a, b int32) int32 {
	if a > b {
		return a
	}
	return b
}

type enumValKey struct {
	sid   int32
	value string
}

func buildQueries() []queryDef {
	return []queryDef{
		{
			Name: "any-blast-radius",
			Run: func(g *Graph, mod string, n int) *table {
				t := &table{cols: []string{"name", "qual_name", "any_params", "returns_any",
					"any_total", "as_any", "bang", "fan_in", "exported", "blast", "at"}}
				for i := range g.Symbols {
					s := &g.Symbols[i]
					m := g.metrics(int32(i + 1))
					if m[mNAnyTotal] == 0 && m[mReturnsAny] == 0 {
						continue
					}
					f := &g.Files[s.FileID-1]
					if f.IsTest || f.IsGen || !g.modOK(s.ModuleID, mod) {
						continue
					}
					blast := (m[mNAnyTotal] + m[mReturnsAny]*4 + m[mNAsAny]*3) *
						maxi(m[mFanIn], 1)
					t.rows = append(t.rows, []cell{cs(s.Name()), cs(s.QualName()),
						ci32(m[mNAnyParams]), ci32(m[mReturnsAny]), ci32(m[mNAnyTotal]),
						ci32(m[mNAsAny]), ci32(m[mNNonNull]), ci32(m[mFanIn]),
						ci32(m[mIsExported]), ci(int(blast)), cs(g.at(s))})
				}
				sortRows(t, func(a, b []cell) bool { return num(a[9]) > num(b[9]) })
				return lim(t, n)
			},
		},
		{
			Name: "suppression-on-hot-code",
			Run: func(g *Graph, mod string, n int) *table {
				t := &table{cols: []string{"kind", "in_symbol", "fan_in", "cyclo",
					"exported", "reason", "at"}}
				for i := range g.Suppress {
					u := &g.Suppress[i]
					f := &g.Files[u.FileID-1]
					if f.IsTest || !g.modOK(f.ModuleID, mod) {
						continue
					}
					name, fan, cyc, exp := "(file level)", int32(0), int32(0), int32(0)
					if u.SymID > 0 {
						s := &g.Symbols[u.SymID-1]
						m := g.metrics(u.SymID)
						name, fan, cyc, exp = s.Name(), m[mFanIn], m[mCyclomatic], m[mIsExported]
					}
					reason := ""
					if u.HasReason {
						reason = cutStr(u.Reason(), 44)
					}
					t.rows = append(t.rows, []cell{cs(u.Kind()), cs(name), ci32(fan),
						ci32(cyc), ci32(exp), cs(reason),
						cs(f.Path() + ":" + strconv.Itoa(int(u.Line)))})
				}
				sortRows(t, func(a, b []cell) bool {
					if ta, tb := b2iStr(a[0].s, "ts-ignore"), b2iStr(b[0].s, "ts-ignore"); ta != tb {
						return ta > tb
					}
					return num(a[2]) > num(b[2])
				})
				return lim(t, n)
			},
		},
		{
			Name: "listener-leak",
			Run: func(g *Graph, mod string, n int) *table {
				type acc struct {
					adds, removes, inLoop, minLine int32
					events, targets                []string
					evSeen, tgSeen                 map[string]bool
				}
				accs := map[int32]*acc{}
				for i := range g.Listeners {
					l := &g.Listeners[i]
					a := accs[l.SymID]
					if a == nil {
						a = &acc{evSeen: map[string]bool{}, tgSeen: map[string]bool{},
							minLine: l.Line}
						accs[l.SymID] = a
					}
					if l.Op() == "add" {
						a.adds++
					} else {
						a.removes++
					}
					if l.InLoop {
						a.inLoop++
					}
					if l.Line < a.minLine {
						a.minLine = l.Line
					}
					gcDistinct(&a.events, a.evSeen, l.Event())
					gcDistinct(&a.targets, a.tgSeen, cutStr(l.Target(), 20))
				}

				classRem := map[int32]int32{}
				for i := range g.Listeners {
					l := &g.Listeners[i]
					if l.Op() != "remove" {
						continue
					}
					p := g.Symbols[l.SymID-1].ParentID
					if p > 0 {
						classRem[p]++
					}
				}
				t := &table{cols: []string{"name", "qual_name", "adds", "removes", "in_loop",
					"events", "targets", "removes_in_class", "fan_in", "at"}}

				sids := make([]int32, 0, len(accs))
				for id := range accs {
					sids = append(sids, id)
				}
				slices.Sort(sids)
				for _, id := range sids {
					a := accs[id]
					if a.adds <= a.removes {
						continue
					}
					s := &g.Symbols[id-1]
					m := g.metrics(id)
					f := &g.Files[s.FileID-1]
					if f.IsTest || !g.modOK(s.ModuleID, mod) {
						continue
					}
					t.rows = append(t.rows, []cell{cs(s.Name()), cs(s.QualName()),
						ci32(a.adds), ci32(a.removes), ci32(a.inLoop),
						cs(joinDistinct(a.events)), cs(joinDistinct(a.targets)),
						ci32(classRem[s.ParentID]), ci32(m[mFanIn]),
						cs(f.Path() + ":" + strconv.Itoa(int(a.minLine)))})
				}
				sortRows(t, func(a, b []cell) bool {
					if d := num(a[2]) - num(a[3]) - (num(b[2]) - num(b[3])); d != 0 {
						return d > 0
					}
					return num(a[4]) > num(b[4])
				})
				return lim(t, n)
			},
		},
		{
			Name: "timer-leak",
			Run: func(g *Graph, mod string, n int) *table {
				t := &table{cols: []string{"name", "timers_set", "timers_cleared", "in_loop",
					"captures", "handler", "component", "fan_in", "at"}}
				for i := range g.Symbols {
					s := &g.Symbols[i]
					m := g.metrics(int32(i + 1))
					if m[mNTimerSet] <= m[mNTimerClear] {
						continue
					}
					f := &g.Files[s.FileID-1]
					if f.IsTest || !g.modOK(s.ModuleID, mod) {
						continue
					}
					t.rows = append(t.rows, []cell{cs(s.Name()), ci32(m[mNTimerSet]),
						ci32(m[mNTimerClear]), ci32(m[mTimerInLoop]),
						ci32(m[mNClosureCapture]), ci32(m[mIsHandler]),
						ci32(m[mIsComponent]), ci32(m[mFanIn]), cs(g.at(s))})
				}
				sortRows(t, func(a, b []cell) bool {
					if d := num(a[1]) - num(a[2]) - (num(b[1]) - num(b[2])); d != 0 {
						return d > 0
					}
					return num(a[3]) > num(b[3])
				})
				return lim(t, n)
			},
		},
		{
			Name: "sync-under-handler",
			Run: func(g *Graph, mod string, n int) *table {

				var roots []int32
				for i := range g.Symbols {
					m := g.metrics(int32(i + 1))
					if m[mIsHandler] == 1 || m[mIsEntrypoint] == 1 {
						roots = append(roots, int32(i+1))
					}
				}
				depth := g.bfsDepth(roots, 4, nil)
				t := &table{cols: []string{"name", "hops", "sync_calls", "exec_", "io",
					"async_", "fan_in", "at"}}

				ids := make([]int32, 0, len(depth))
				for id := range depth {
					ids = append(ids, id)
				}
				slices.Sort(ids)
				for _, id := range ids {
					d := depth[id]
					s := &g.Symbols[id-1]
					m := g.metrics(id)
					if m[hazardMetric("sync_block")] == 0 {
						continue
					}
					f := &g.Files[s.FileID-1]
					if f.IsTest || !g.modOK(s.ModuleID, mod) {
						continue
					}
					t.rows = append(t.rows, []cell{cs(s.Name()), ci(d),
						ci32(m[hazardMetric("sync_block")]),
						ci32(m[hazardMetric("exec")]),
						ci32(m[hazardMetric("io")]),
						ci32(m[mIsAsync]), ci32(m[mFanIn]), cs(g.at(s))})
				}
				sortRows(t, func(a, b []cell) bool {
					if num(a[1]) != num(b[1]) {
						return num(a[1]) < num(b[1])
					}
					return num(a[2]) > num(b[2])
				})
				return lim(t, n)
			},
		},
		{
			Name: "await-in-loop",
			Run: symQ([]string{"name", "awaits_in_loop", "depth", "total_awaits",
				"promise_all", "net_", "fan_in", "at"},
				[]int{colName, mAwaitInLoop, mMaxLoopDepth, mNAwait, mNPromiseAll,
					hazardMetric("net"), mFanIn, colAt},
				func(m []int32) bool { return m[mAwaitInLoop] > 0 },
				[]ordKey{{1, true}, {2, true}},
				true, false, nil, scanOrder{kind: scanIdxDesc, mcol: mAwaitInLoop}),
		},
		{
			Name: "redos-reachable",
			Run: symQ([]string{"name", "suspicious_regexes", "total_regexes", "in_loop",
				"exported", "handler", "fan_in", "at"},
				[]int{colName, mNRegexRedos, mNRegexLit, mRegexInLoop, mIsExported,
					mIsHandler, mFanIn, colAt},
				func(m []int32) bool { return m[mNRegexRedos] > 0 },
				[]ordKey{{6, true}, {1, true}},
				true, false, nil),
		},
		{
			Name: "dom-sinks",
			Run: symQ([]string{"name", "innerhtml", "dom_ops", "json_parse", "any_params",
				"exported", "component", "fan_in", "at"},
				[]int{colName, mNInnerhtml, hazardMetric("dom"), mNJsonParse,
					mNAnyParams, mIsExported, mIsComponent, mFanIn, colAt},
				func(m []int32) bool {
					return m[mNInnerhtml] > 0 || m[hazardMetric("dom")] > 0
				},
				[]ordKey{{1, true}, {7, true}},
				true, false, nil),
		},
		{
			Name: "import-cycles",
			Run: func(g *Graph, mod string, n int) *table {

				t := &table{cols: []string{"file_a", "file_b", "a_type_only", "a_to_b",
					"b_to_a", "b_type_only"}}
				type pairAgg struct {
					a2b, typeA int32
				}
				agg := map[[2]int32]*pairAgg{}
				for i := range g.Imports {
					im := &g.Imports[i]
					if im.TargetID < 0 {
						continue
					}
					key := [2]int32{im.FileID, im.TargetID}
					p := agg[key]
					if p == nil {
						p = &pairAgg{}
						agg[key] = p
					}
					p.a2b++
					if im.IsTypeOnly {
						p.typeA++
					}
				}

				keys := make([][2]int32, 0, len(agg))
				for k := range agg {
					if k[0] >= k[1] {
						continue
					}
					rev := [2]int32{k[1], k[0]}
					if agg[rev] == nil {
						continue
					}
					f := &g.Files[k[0]-1]
					if !g.modOK(f.ModuleID, mod) {
						continue
					}
					keys = append(keys, k)
				}

				sort.Slice(keys, func(x, y int) bool {
					if keys[x][0] != keys[y][0] {
						return keys[x][0] < keys[y][0]
					}
					return keys[x][1] < keys[y][1]
				})
				for _, k := range keys {
					rev := [2]int32{k[1], k[0]}
					back := agg[rev]
					t.rows = append(t.rows, []cell{
						cs(g.Files[k[0]-1].Path()), cs(g.Files[k[1]-1].Path()),
						ci32(agg[k].typeA), ci32(agg[k].a2b), ci32(back.a2b), ci32(back.typeA)})
				}
				sortRows(t, func(a, b []cell) bool {
					return (num(a[3]) + num(a[4])) > (num(b[3]) + num(b[4]))
				})
				return lim(t, n)
			},
		},
		{
			Name: "assertion-density",
			Run: symQ2([]string{"name", "as_casts", "as_any", "bang", "angle_casts",
				"satisfies_", "any_", "suppressions", "fan_in", "exported", "at"},
				[]int{colName, mNAsAssertion, mNAsAny, mNNonNull, mNAngleAssertion,
					mNSatisfies, mNAnyTotal, mNSuppressions, mFanIn, mIsExported, colAt},
				func(m []int32) bool {
					return m[mNAsAssertion]+m[mNNonNull]+m[mNAngleAssertion] > 0
				},
				func(m []int32) int {
					return int(m[mNAsAny])*4 + int(m[mNAsAssertion]) + int(m[mNNonNull])
				}, nil, nil, true, false, nil, scanOrder{kind: scanFileLine}),
		},
		{
			Name: "assertion-escape-hatches",
			Run: symQ2([]string{"name", "qual", "as_any", "non_null", "angle_casts",
				"assertions", "satisfies_", "returns_any", "exported", "fan_in", "at"},
				[]int{colName, colQual, mNAsAny, mNNonNull, mNAngleAssertion,
					mNAsAssertion, mNSatisfies, mReturnsAny, mIsExported, mFanIn, colAt},
				func(m []int32) bool {
					return m[mNAsAny]+m[mNNonNull]+m[mNAngleAssertion] > 0
				},
				func(m []int32) int {
					return (int(m[mNAsAny])*3 + int(m[mNNonNull]) +
						int(m[mNAngleAssertion])) * (1 + int(m[mFanIn]))
				}, nil, nil, true, false, nil, scanOrder{kind: scanFileLine}),
		},
		{
			Name: "suppression-debt",
			Run: symQ2([]string{"name", "qual", "ts_ignore", "ts_expect_error", "eslint_disable",
				"total", "anys", "exported", "fan_in", "at"},
				[]int{colName, colQual, mNTsIgnore, mNTsExpectError, mNEslintDisable,
					mNSuppressions, mNAnyTotal, mIsExported, mFanIn, colAt},
				func(m []int32) bool {
					return m[mNTsIgnore]+m[mNTsExpectError]+m[mNEslintDisable] > 0
				},
				func(m []int32) int {
					return int(m[mNTsIgnore]) * (1 + int(m[mFanIn]))
				}, nil, []ordKey{{4, true}}, true, false, nil, scanOrder{kind: scanFileLine}),
		},
		{
			Name: "dead-code",
			Run: symQ([]string{"name", "kind", "sloc", "cyclo", "ext_calls", "at"},
				[]int{colName, colKind, mSloc, mCyclomatic, mNExternalCalls, colAt},
				func(m []int32) bool {
					return m[mFanIn] == 0 && m[mIsPublic] == 0 && m[mIsTest] == 0 &&
						m[mIsEntrypoint] == 0 && m[mIsOverride] == 0 && m[mIsAbstract] == 0
				},
				[]ordKey{{2, true}}, true, true,
				func(s *Symbol) bool {
					if !g_isCallKind(s.Kind) {
						return false
					}
					return s.Name() != "(anonymous)" && s.Name() != "<module>"
				}, scanOrder{kind: scanFileKind}),
		},
		{
			Name: "event-loop-block-below-entry",
			Run: func(g *Graph, mod string, n int) *table {

				want := func(id int32) bool {
					m := g.metrics(id)
					return m[mNFsSync] > 0 || m[mNSearchInLoop] > 0 || m[mNJsonParseInLoop] > 0
				}

				roots := g.entryRoots(false)
				a := g.adj()
				t := &table{cols: []string{"name", "reached_from", "hops", "sync_fs_calls",
					"search_in_loop", "json_parse_in_loop", "array_grow_in_loop",
					"callee_is_async", "fan_in", "at"}}
				type pair struct {
					sid, eid int32
					hops     int
				}
				pairs := map[uint64]*pair{}
				type layer struct{ id int32 }
				for _, r := range roots {
					cur := []layer{{r}}
					seen := map[uint64]struct{}{}
					for d := 0; d < 4 && len(cur) > 0; d++ {
						var next []layer
						for _, u := range cur {
							for k := a.outOff[u.id]; k < a.outOff[u.id+1]; k++ {
								v := a.outTo[k]
								pk := uint64(uint32(r))<<32 | uint64(uint32(v))
								if _, ok := seen[pk]; ok {
									continue
								}
								seen[pk] = struct{}{}
								next = append(next, layer{v})

								if v == r || !want(v) {
									continue
								}
								kk := uint64(uint32(v))<<32 | uint64(uint32(r))
								if _, ok := pairs[kk]; !ok {
									pairs[kk] = &pair{sid: v, eid: r, hops: d + 1}
								}
							}
						}
						cur = next
					}
				}

				pk := make([]uint64, 0, len(pairs))
				for k := range pairs {
					pk = append(pk, k)
				}
				slices.Sort(pk)
				for _, k := range pk {
					p := pairs[k]
					s := &g.Symbols[p.sid-1]
					m := g.metrics(p.sid)
					f := &g.Files[s.FileID-1]
					if f.IsTest || !g.modOK(s.ModuleID, mod) {
						continue
					}
					en := &g.Symbols[p.eid-1]
					t.rows = append(t.rows, []cell{cs(s.Name()), cs(en.Name()), ci(p.hops),
						ci32(m[mNFsSync]), ci32(m[mNSearchInLoop]),
						ci32(m[mNJsonParseInLoop]), ci32(m[mNArrayGrowInLoop]),
						ci32(m[mIsAsync]), ci32(m[mFanIn]), cs(g.at(s))})
				}
				sortRows(t, func(a, b []cell) bool {
					if num(a[3]) != num(b[3]) {
						return num(a[3]) > num(b[3])
					}
					if num(a[2]) != num(b[2]) {
						return num(a[2]) < num(b[2])
					}
					return num(a[8]) > num(b[8])
				})
				return lim(t, n)
			},
		},
		{
			Name: "listener-added-never-removed",
			Run: func(g *Graph, mod string, n int) *table {
				callers := map[int32]map[int32]bool{}
				for i := range g.Edges {
					e := &g.Edges[i]
					if e.Self {
						continue
					}
					m := callers[e.Callee]
					if m == nil {
						m = map[int32]bool{}
						callers[e.Callee] = m
					}
					m[e.Caller] = true
				}
				t := &table{cols: []string{"name", "adds", "removes", "dispose_calls",
					"adds_in_loop", "is_async", "fan_in", "distinct_callers", "at"}}
				for i := range g.Symbols {
					m := g.metrics(int32(i + 1))
					if m[mNListenerAdd] == 0 || m[mNListenerRemove] != 0 || m[mNDisposeCall] != 0 {
						continue
					}
					s := &g.Symbols[i]
					f := &g.Files[s.FileID-1]
					if f.IsTest || !g.modOK(s.ModuleID, mod) {
						continue
					}
					t.rows = append(t.rows, []cell{cs(s.Name()), ci32(m[mNListenerAdd]),
						ci32(m[mNListenerRemove]), ci32(m[mNDisposeCall]),
						ci32(m[mListenerInLoop]), ci32(m[mIsAsync]), ci32(m[mFanIn]),
						ci(len(callers[int32(i+1)])), cs(g.at(s))})
				}
				sortRows(t, func(a, b []cell) bool {
					if num(a[4]) != num(b[4]) {
						return num(a[4]) > num(b[4])
					}
					if num(a[1]) != num(b[1]) {
						return num(a[1]) > num(b[1])
					}
					return num(a[7]) > num(b[7])
				})
				return lim(t, n)
			},
		},
		{
			Name: "any-escape-hatch",
			Run: symQ([]string{"name", "any_count", "any_params", "returns_any", "as_any",
				"non_null_assertions", "fan_in", "is_exported", "at"},
				[]int{colName, mNAnyTotal, mNAnyParams, mReturnsAny, mNAsAny, mNNonNull,
					mFanIn, mIsExported, colAt},
				func(m []int32) bool { return m[mNAnyTotal] > 0 },
				[]ordKey{{1, true}, {6, true}},
				true, false, nil, scanOrder{kind: scanIdxDesc, mcol: mNAnyTotal}),
		},
		{
			Name: "ts-ignore",
			Run: symQ2([]string{"name", "ts_ignores", "ts_expect_errors", "eslint_disables",
				"total_suppressions", "fan_in", "cyclo", "at"},
				[]int{colName, mNTsIgnore, mNTsExpectError, mNEslintDisable, mNSuppressions,
					mFanIn, mCyclomatic, colAt},
				func(m []int32) bool { return m[mNTsIgnore]+m[mNTsExpectError] > 0 },
				oneOf(mFanIn), scoreOf(mNTsIgnore, mNTsExpectError), nil, true, false, nil),
		},
		{
			Name: "non-null-assertion",
			Run: symQ([]string{"name", "non_null_assertions", "optional_chains",
				"non_null_assertions", "fan_in", "cyclo", "at"},
				[]int{colName, mNNonNull, mNOptionalChain, mNNonNull, mFanIn, mCyclomatic, colAt},
				func(m []int32) bool { return m[mNNonNull] > 2 },
				[]ordKey{{1, true}, {4, true}},
				true, false, nil),
		},
		{
			Name: "unsafe-type-assertion",
			Run: symQ2([]string{"name", "as_assertions", "as_any", "angle_assertions",
				"satisfies", "fan_in", "cyclo", "at"},
				[]int{colName, mNAsAssertion, mNAsAny, mNAngleAssertion, mNSatisfies,
					mFanIn, mCyclomatic, colAt},
				func(m []int32) bool { return m[mNAsAssertion]+m[mNAngleAssertion] > 2 },
				oneOf(mFanIn), scoreOf(mNAsAssertion, mNAngleAssertion), nil, true, false, nil),
		},
		{
			Name: "floating-promise",
			Run: symQ([]string{"name", "floating_promises", "awaits", "then_chains",
				"promise_alls", "fan_in", "cyclo", "at"},
				[]int{colName, mNFloatingPromise, mNAwait, mNThenChain, mNPromiseAll,
					mFanIn, mCyclomatic, colAt},
				func(m []int32) bool { return m[mNFloatingPromise] > 0 },
				[]ordKey{{5, true}, {1, true}},
				true, false, nil, scanOrder{kind: scanFileLine}),
		},
		{
			Name: "async-in-loop",
			Run: symQ([]string{"name", "awaits_in_loop", "total_awaits", "loops",
				"promise_alls", "cyclo", "fan_in", "at"},
				[]int{colName, mAwaitInLoop, mNAwait, mNLoops, mNPromiseAll, mCyclomatic,
					mFanIn, colAt},
				func(m []int32) bool { return m[mAwaitInLoop] > 0 },
				[]ordKey{{1, true}, {3, true}},
				true, false, nil, scanOrder{kind: scanIdxDesc, mcol: mAwaitInLoop}),
		},
		{
			Name: "dom-xss-sink",
			Run: symQ([]string{"name", "innerhtml_uses", "json_parses", "fan_in",
				"is_handler", "at"},
				[]int{colName, mNInnerhtml, mNJsonParse, mFanIn, mIsHandler, colAt},
				func(m []int32) bool { return m[mNInnerhtml] > 0 },
				[]ordKey{{3, true}, {1, true}},
				true, false, nil),
		},
		{
			Name: "redos-surface",
			Run: symQ([]string{"name", "redos_patterns", "json_parses", "fan_in",
				"is_handler", "at"},
				[]int{colName, mNRegexRedos, mNJsonParse, mFanIn, mIsHandler, colAt},
				func(m []int32) bool { return m[mNRegexRedos] > 0 },
				[]ordKey{{3, true}, {1, true}},
				true, false, nil),
		},
		{
			Name: "process-exit-in-handler",
			Run: func(g *Graph, mod string, n int) *table {
				var roots []int32
				for i := range g.Symbols {
					if g.metrics(int32(i + 1))[mIsHandler] == 1 {
						roots = append(roots, int32(i+1))
					}
				}
				depth := g.bfsDepth(roots, 4, nil)
				t := &table{cols: []string{"name", "exit_calls", "hops_from_handler",
					"fan_in", "cyclo", "at"}}
				best := map[int32]int{}
				for id, d := range depth {
					m := g.metrics(id)
					if m[mNProcessExit] == 0 {
						continue
					}
					if b, ok := best[id]; ok && b <= d {
						continue
					}
					best[id] = d
				}
				for id, d := range best {
					s := &g.Symbols[id-1]
					m := g.metrics(id)
					f := &g.Files[s.FileID-1]
					if f.IsTest || !g.modOK(s.ModuleID, mod) {
						continue
					}
					t.rows = append(t.rows, []cell{cs(s.Name()), ci32(m[mNProcessExit]),
						ci(d), ci32(m[mFanIn]), ci32(m[mCyclomatic]), cs(g.at(s))})
				}
				sortRows(t, func(a, b []cell) bool {
					if num(a[2]) != num(b[2]) {
						return num(a[2]) < num(b[2])
					}
					return num(a[1]) > num(b[1])
				})
				return lim(t, n)
			},
		},
		{
			Name: "type-vs-value-space",
			Run: func(g *Graph, mod string, n int) *table {
				ty, val, tot, sloc := map[int32]int32{}, map[int32]int32{},
					map[int32]int32{}, map[int32]int32{}
				for i := range g.Symbols {
					s := &g.Symbols[i]
					f := &g.Files[s.FileID-1]
					switch s.Kind {
					case kInterface, kType, kEnum, kModule:
					case kClass, kFunction, kMethod, kClosure:
					default:
						continue
					}
					if f.IsTest || !g.modOK(s.ModuleID, mod) {
						continue
					}
					switch s.Kind {
					case kInterface, kType, kEnum, kModule:
						ty[s.FileID]++
					default:
						val[s.FileID]++
					}
					tot[s.FileID]++
					sloc[s.FileID] = f.Sloc
				}
				t := &table{cols: []string{"path", "type_space", "value_space", "total",
					"pct_type", "sloc"}}

				fids := make([]int32, 0, len(tot))
				for id := range tot {
					fids = append(fids, id)
				}
				slices.Sort(fids)
				for _, id := range fids {
					c := tot[id]
					pct := int64(100) * int64(ty[id]) / int64(c)
					t.rows = append(t.rows, []cell{cs(g.Files[id-1].Path()), ci32(ty[id]),
						ci32(val[id]), ci32(c), cl(pct), ci32(sloc[id])})
				}
				sortRows(t, func(a, b []cell) bool {
					if num(a[4]) != num(b[4]) {
						return num(a[4]) > num(b[4])
					}
					return num(a[1]) > num(b[1])
				})
				return lim(t, n)
			},
		},
		{
			Name: "orphan-types",
			Run: func(g *Graph, mod string, n int) *table {
				tokenUse := g.sigTokenUse()
				typeExports := map[string]int32{}
				for i := range g.TSExports {
					e := &g.TSExports[i]
					if e.IsTypeOnly {
						typeExports[e.Name()]++
					}
				}
				t := &table{cols: []string{"name", "kind", "n_members", "n_extends",
					"is_exported", "type_exports", "at"}}

				tds := make([]int, 0, len(g.TypeDefs))
				for i := range g.TypeDefs {
					tds = append(tds, i)
				}
				sort.Slice(tds, func(x, y int) bool {
					a, b := g.TypeDefs[tds[x]], g.TypeDefs[tds[y]]
					sa, sb := g.Symbols[a.SymID-1], g.Symbols[b.SymID-1]
					if sa.FileID != sb.FileID {
						return sa.FileID < sb.FileID
					}
					if kindLexRank[sa.Kind] != kindLexRank[sb.Kind] {
						return kindLexRank[sa.Kind] < kindLexRank[sb.Kind]
					}
					return a.SymID < b.SymID
				})
				for _, ti := range tds {
					td := &g.TypeDefs[ti]
					s := &g.Symbols[td.SymID-1]
					if s.Kind != kInterface && s.Kind != kType {
						continue
					}
					f := &g.Files[s.FileID-1]
					if f.IsTest || !g.modOK(s.ModuleID, mod) {
						continue
					}

					u := tokenUse[s.Name()]
					usedAny := u.n > 1 || (u.n == 1 && u.first != td.SymID)
					tex := typeExports[s.Name()]
					if usedAny || tex > 0 {
						continue
					}
					t.rows = append(t.rows, []cell{cs(s.Name()), cs(kindNames[s.Kind]),
						ci32(td.NMembers), ci32(td.NExtends), ci32(b2i(td.IsExported)),
						ci32(tex), cs(g.at(s))})
				}
				sortRows(t, func(a, b []cell) bool { return num(a[2]) > num(b[2]) })
				return lim(t, n)
			},
		},
		{
			Name: "path-alias-utilization",
			Run: func(g *Graph, mod string, n int) *table {
				aliasImp, relImp, totImp := map[string]int32{}, map[string]int32{}, map[string]int32{}
				for i := range g.Imports {
					im := &g.Imports[i]
					dir := g.Files[im.FileID-1].Dir()
					totImp[dir]++

					if len(im.Target()) >= 2 && im.Target()[0] == '@' &&
						strings.IndexByte(im.Target()[1:], '/') >= 0 {
						aliasImp[dir]++
					}
					if hasPrefix(im.Target(), "./") {
						relImp[dir]++
					}
				}
				t := &table{cols: []string{"project_dir", "base_url", "paths_json",
					"alias_imports", "rel_imports", "total_imports"}}
				for i := range g.TSConfigs {
					c := &g.TSConfigs[i]
					if c.PathsJSON() == "" || !likeMatch(mod, c.Dir()) {
						continue
					}

					pat := c.Dir() + "%"
					al, rl, tt := int32(0), int32(0), int32(0)
					for d, v := range totImp {
						if likeMatch(pat, d) {
							tt += v
						}
					}
					for d, v := range aliasImp {
						if likeMatch(pat, d) {
							al += v
						}
					}
					for d, v := range relImp {
						if likeMatch(pat, d) {
							rl += v
						}
					}
					bu := cnull()
					if c.HasBaseURL {
						bu = cs(c.BaseURL())
					}
					t.rows = append(t.rows, []cell{cs(c.Dir()), bu, cs(c.PathsJSON()),
						ci32(al), ci32(rl), ci32(tt)})
				}
				sortRows(t, func(a, b []cell) bool { return num(a[3]) > num(b[3]) })
				return lim(t, n)
			},
		},
		{
			Name: "ambient-augmentation",
			Run: func(g *Graph, mod string, n int) *table {
				t := &table{cols: []string{"name", "kind", "is_ambient", "n_members",
					"is_exported", "basename", "at"}}
				for i := range g.TypeDefs {
					td := &g.TypeDefs[i]
					if !td.IsAmbient {
						continue
					}
					s := &g.Symbols[td.SymID-1]
					if !g.modOK(s.ModuleID, mod) {
						continue
					}
					f := &g.Files[s.FileID-1]
					t.rows = append(t.rows, []cell{cs(s.Name()), cs(kindNames[s.Kind]),
						ci32(b2i(td.IsAmbient)), ci32(td.NMembers),
						ci32(b2i(td.IsExported)), cs(f.Basename()), cs(g.at(s))})
				}
				sortRows(t, func(a, b []cell) bool { return num(a[3]) > num(b[3]) })
				return lim(t, n)
			},
		},
		{
			Name: "iface-inherit-chain",
			Run: func(g *Graph, mod string, n int) *table {

				inheritedBy := map[string]int32{}
				for i := range g.TypeDefs {
					td := &g.TypeDefs[i]
					if td.ExtendsName() == "" {
						continue
					}
					seen := map[string]bool{}
					for _, part := range splitComma(td.ExtendsName()) {
						if seen[part] {
							continue
						}
						seen[part] = true
						inheritedBy[part]++
					}
				}
				t := &table{cols: []string{"name", "extends", "n_members", "extends_names",
					"idx_sigs", "inherited_by", "at"}}
				for i := range g.TypeDefs {
					td := &g.TypeDefs[i]
					if td.NExtends < 1 {
						continue
					}
					s := &g.Symbols[td.SymID-1]
					if !g.modOK(s.ModuleID, mod) {
						continue
					}
					t.rows = append(t.rows, []cell{cs(s.Name()), ci32(td.NExtends),
						ci32(td.NMembers), cs(td.ExtendsName()), ci32(td.NIndexSig),
						ci32(inheritedBy[s.Name()]), cs(g.at(s))})
				}
				sortRows(t, func(a, b []cell) bool {
					if num(a[5]) != num(b[5]) {
						return num(a[5]) > num(b[5])
					}
					return num(a[1]) > num(b[1])
				})
				return lim(t, n)
			},
		},
		{
			Name: "type-export-mismatch",
			Run: func(g *Graph, mod string, n int) *table {
				valueExports := map[int32]int32{}
				for i := range g.TSExports {
					if !g.TSExports[i].IsTypeOnly {
						valueExports[g.TSExports[i].FileID]++
					}
				}
				localValues := map[int32]int32{}
				for i := range g.Symbols {
					s := &g.Symbols[i]
					if s.Kind == kClass || s.Kind == kFunction || s.Kind == kMethod || s.Kind == kClosure {
						localValues[s.FileID]++
					}
				}

				type gkey struct {
					fid      int32
					reexport bool
				}
				groups := map[gkey]map[string]bool{}
				for i := range g.TSExports {
					e := &g.TSExports[i]
					if !e.IsTypeOnly {
						continue
					}
					f := &g.Files[e.FileID-1]
					if !g.modOK(f.ModuleID, mod) {
						continue
					}
					k := gkey{e.FileID, e.IsReexport}
					m := groups[k]
					if m == nil {
						m = map[string]bool{}
						groups[k] = m
					}
					m[e.Name()] = true
				}
				keys := make([]gkey, 0, len(groups))
				for k := range groups {
					if valueExports[k.fid] != 0 {
						continue
					}
					keys = append(keys, k)
				}

				sort.Slice(keys, func(x, y int) bool {
					if keys[x].fid != keys[y].fid {
						return keys[x].fid < keys[y].fid
					}
					return !keys[x].reexport && keys[y].reexport
				})
				t := &table{cols: []string{"module_", "type_exports", "local_values",
					"reexport", "value_exports"}}
				for _, k := range keys {
					t.rows = append(t.rows, []cell{cs(g.Files[k.fid-1].Path()),
						ci(len(groups[k])), ci32(localValues[k.fid]), cb(k.reexport),
						ci32(valueExports[k.fid])})
				}
				sortRows(t, func(a, b []cell) bool { return num(a[1]) > num(b[1]) })
				return lim(t, n)
			},
		},
		{
			Name: "dead-service-methods",
			Run: func(g *Graph, mod string, n int) *table {
				t := &table{cols: []string{"name", "class_", "sloc", "fan_in", "n_calls",
					"cyclo", "at"}}
				sids := make([]int32, 0, len(g.Symbols))
				for i := range g.Symbols {
					if g.Symbols[i].Kind == kMethod {
						sids = append(sids, int32(i+1))
					}
				}
				sortSidsKindName(g, sids)
				for _, sid := range sids {
					s := &g.Symbols[sid-1]
					m := g.metrics(sid)
					if m[mFanIn] != 0 {
						continue
					}
					f := &g.Files[s.FileID-1]
					if f.IsTest || f.IsGen || s.Name() == "constructor" {
						continue
					}
					if !g.modOK(s.ModuleID, mod) {
						continue
					}
					cls := cnull()
					if s.ParentID > 0 {
						cls = cs(g.Symbols[s.ParentID-1].Name())
					}
					t.rows = append(t.rows, []cell{cs(s.Name()), cls, ci32(m[mSloc]),
						ci32(m[mFanIn]), ci32(m[mNCalls]), ci32(m[mCyclomatic]), cs(g.at(s))})
				}
				sortRows(t, func(a, b []cell) bool { return num(a[2]) > num(b[2]) })
				return lim(t, n)
			},
		},
		{
			Name: "deprecated-usage",
			Run: func(g *Graph, mod string, n int) *table {
				callers := map[int32]map[int32]bool{}
				for i := range g.Edges {
					e := &g.Edges[i]
					m := callers[e.Callee]
					if m == nil {
						m = map[int32]bool{}
						callers[e.Callee] = m
					}
					m[e.Caller] = true
				}
				t := &table{cols: []string{"name", "path", "line_start", "n_callers"}}
				for i := range g.Symbols {
					s := &g.Symbols[i]
					m := g.metrics(int32(i + 1))
					if m[mIsDeprecated] == 0 {
						continue
					}
					f := &g.Files[s.FileID-1]
					if f.IsGen || !g.modOK(s.ModuleID, mod) {
						continue
					}

					if len(callers[int32(i+1)]) == 0 {
						continue
					}
					t.rows = append(t.rows, []cell{cs(s.Name()), cs(f.Path()),
						ci32(s.LineStart), ci(len(callers[int32(i+1)]))})
				}
				sortRows(t, func(a, b []cell) bool { return num(a[3]) > num(b[3]) })
				return lim(t, n)
			},
		},
		{
			Name: "duplicate-enum-values",
			Run: func(g *Graph, mod string, n int) *table {
				type grp struct {
					n       int32
					members []string
				}
				groups := map[enumValKey]*grp{}
				for i := range g.EnumMembers {
					em := &g.EnumMembers[i]
					if !em.HasVal {
						continue
					}
					k := enumValKey{em.SymID, em.Value()}
					gr := groups[k]
					if gr == nil {
						gr = &grp{}
						groups[k] = gr
					}
					gr.n++
					gr.members = append(gr.members, em.Name())
				}
				t := &table{cols: []string{"enum_name", "value", "n_members", "members", "path"}}

				keys := make([]enumValKey, 0, len(groups))
				for k := range groups {
					if groups[k].n > 1 {
						keys = append(keys, k)
					}
				}
				sort.Slice(keys, func(x, y int) bool {
					if keys[x].sid != keys[y].sid {
						return keys[x].sid < keys[y].sid
					}
					return keys[x].value < keys[y].value
				})
				for _, k := range keys {
					gr := groups[k]
					s := &g.Symbols[k.sid-1]
					f := &g.Files[s.FileID-1]
					if f.IsGen || !g.modOK(s.ModuleID, mod) {
						continue
					}
					t.rows = append(t.rows, []cell{cs(s.Name()), cs(k.value), ci32(gr.n),
						cs(joinComma(gr.members)), cs(f.Path())})
				}
				sortRows(t, func(a, b []cell) bool { return num(a[2]) > num(b[2]) })
				return lim(t, n)
			},
		},
		{
			Name: "mixed-enums",
			Run: func(g *Graph, mod string, n int) *table {
				strs := map[int32]int32{}
				nums := map[int32]int32{}
				tot := map[int32]int32{}
				for i := range g.EnumMembers {
					em := &g.EnumMembers[i]
					if !em.HasVal {
						continue
					}
					tot[em.SymID]++
					if em.Value() != "" && (em.Value()[0] == '\'' || em.Value()[0] == '"') {
						strs[em.SymID]++
					} else {
						nums[em.SymID]++
					}
				}
				t := &table{cols: []string{"enum_name", "path", "string_members",
					"numeric_members", "total_members"}}

				sids := make([]int32, 0, len(tot))
				for sid := range tot {
					if strs[sid] > 0 && nums[sid] > 0 {
						sids = append(sids, sid)
					}
				}
				slices.Sort(sids)
				for _, sid := range sids {
					s := &g.Symbols[sid-1]
					f := &g.Files[s.FileID-1]
					if f.IsGen || !g.modOK(s.ModuleID, mod) {
						continue
					}
					t.rows = append(t.rows, []cell{cs(s.Name()), cs(f.Path()),
						ci32(strs[sid]), ci32(nums[sid]), ci32(tot[sid])})
				}
				sortRows(t, func(a, b []cell) bool { return num(a[4]) > num(b[4]) })
				return lim(t, n)
			},
		},
		{
			Name: "type-import-misuse",
			Run: func(g *Graph, mod string, n int) *table {
				anyExport := map[int32]bool{}
				valueExport := map[int32]bool{}
				for i := range g.TSExports {
					e := &g.TSExports[i]
					anyExport[e.FileID] = true
					if !e.IsTypeOnly {
						valueExport[e.FileID] = true
					}
				}
				t := &table{cols: []string{"path", "target", "line", "n_names"}}
				for i := range g.Imports {
					im := &g.Imports[i]
					if im.IsTypeOnly || im.TargetID < 0 {
						continue
					}
					if !anyExport[im.TargetID] || valueExport[im.TargetID] {
						continue
					}
					f := &g.Files[im.FileID-1]
					if f.IsGen || !g.modOK(f.ModuleID, mod) {
						continue
					}
					t.rows = append(t.rows, []cell{cs(f.Path()), cs(im.Target()),
						ci32(im.Line), ci32(im.NNames)})
				}
				sortRows(t, func(a, b []cell) bool {
					if a[0].s != b[0].s {
						return a[0].s < b[0].s
					}
					return num(a[2]) < num(b[2])
				})
				return lim(t, n)
			},
		},
		{
			Name: "suppression-without-reason",
			Run: func(g *Graph, mod string, n int) *table {
				byFile := map[int32][]int32{}
				for i := range g.Symbols {
					s := &g.Symbols[i]
					if g.isCallKind(s.Kind) {
						byFile[s.FileID] = append(byFile[s.FileID], int32(i+1))
					}
				}
				for f := range byFile {
					ids := byFile[f]
					sort.SliceStable(ids, func(a, b int) bool {
						return g.Symbols[ids[a]-1].LineStart > g.Symbols[ids[b]-1].LineStart
					})
				}
				t := &table{cols: []string{"path", "kind", "line", "in_fn"}}
				for i := range g.Suppress {
					u := &g.Suppress[i]
					if u.HasReason && u.Reason() != "" {
						continue
					}
					f := &g.Files[u.FileID-1]
					if f.IsGen || !g.modOK(f.ModuleID, mod) {
						continue
					}
					inFn := cnull()
					for _, sid := range byFile[u.FileID] {
						s := &g.Symbols[sid-1]
						if u.Line >= s.LineStart && u.Line <= s.LineEnd {
							inFn = cs(s.Name())
							break
						}
					}
					t.rows = append(t.rows, []cell{cs(f.Path()), cs(u.Kind()),
						ci32(u.Line), inFn})
				}
				sortRows(t, func(a, b []cell) bool {
					if a[0].s != b[0].s {
						return a[0].s < b[0].s
					}
					return num(a[2]) < num(b[2])
				})
				return lim(t, n)
			},
		},
		{
			Name: "unused-dependencies",
			Run: func(g *Graph, mod string, n int) *table {
				used := make([]bool, len(g.Deps))
				byName := make(map[string][]int32, len(g.Deps)*2)
				for j := range g.Deps {
					d := g.Deps[j].Name()
					byName[d] = append(byName[d], int32(j))
				}
				for i := range g.Imports {
					tgt := g.Imports[i].Target()
					for {
						for _, j := range byName[tgt] {
							used[j] = true
						}
						k := strings.LastIndexByte(tgt, '/')
						if k < 0 {
							break
						}
						tgt = tgt[:k]
					}
				}
				t := &table{cols: []string{"name", "version", "is_dev", "package_dir", "used"}}
				for i := range g.Deps {
					d := &g.Deps[i]
					if used[i] {
						continue
					}
					t.rows = append(t.rows, []cell{cs(d.Name()), cs(d.Version()),
						cb(d.IsDev), cs(d.Dir()), ci(0)})
				}
				sortRows(t, func(a, b []cell) bool {
					if a[2].s != b[2].s {
						return a[2].s < b[2].s
					}
					return a[0].s < b[0].s
				})
				return lim(t, n)
			},
		},
		{
			Name: "any-interpolation",
			Run: symQ([]string{"name", "substitutions", "any_refs", "n_as_any", "fan_in", "at"},
				[]int{colName, mNTemplateSub, mNAnyTotal, mNAsAny, mFanIn, colAt},
				func(m []int32) bool { return m[mNTemplateSub] > 0 && m[mNAnyTotal] > 0 },
				[]ordKey{{1, true}, {2, true}},
				true, false, nil, scanOrder{kind: scanIdxAsc, mcol: mNAnyTotal}),
		},
		{
			Name: "mutability-blast",
			Run: func(g *Graph, mod string, n int) *table {
				t := &table{cols: []string{"name", "members", "readonly", "pct_readonly", "at"}}

				tds := make([]int, 0, len(g.TypeDefs))
				for i := range g.TypeDefs {
					tds = append(tds, i)
				}
				sort.Slice(tds, func(x, y int) bool {
					a, b := g.TypeDefs[tds[x]], g.TypeDefs[tds[y]]
					sa, sb := g.Symbols[a.SymID-1], g.Symbols[b.SymID-1]
					if sa.Kind != sb.Kind {
						return sa.Kind < sb.Kind
					}
					if sa.Name() != sb.Name() {
						return sa.Name() < sb.Name()
					}
					return a.SymID < b.SymID
				})
				for _, ti := range tds {
					td := &g.TypeDefs[ti]
					if td.NMembers <= 0 || td.NReadonly != 0 || !td.IsExported {
						continue
					}
					s := &g.Symbols[td.SymID-1]
					if s.Kind != kInterface {
						continue
					}
					f := &g.Files[s.FileID-1]
					if f.IsTest || !g.modOK(s.ModuleID, mod) {
						continue
					}
					t.rows = append(t.rows, []cell{cs(s.Name()), ci32(td.NMembers),
						ci32(td.NReadonly), ci(0), cs(g.at(s))})
				}
				sortRows(t, func(a, b []cell) bool { return num(a[1]) > num(b[1]) })
				return lim(t, n)
			},
		},
		{
			Name: "boundary-crossings",
			Run: func(g *Graph, mod string, n int) *table {
				inUI := func(d string) bool {
					d = "/" + d + "/"
					return containsStr(d, "/ui/") || containsStr(d, "/views/") ||
						containsStr(d, "/pages/")
				}
				inData := func(d string) bool {
					d = "/" + d + "/"
					return containsStr(d, "/api/") || containsStr(d, "/db/") ||
						containsStr(d, "/server/")
				}
				t := &table{cols: []string{"from_file", "to_file", "line", "target"}}
				for i := range g.Imports {
					im := &g.Imports[i]
					if im.TargetID < 0 || im.FileID == im.TargetID {
						continue
					}
					fc := &g.Files[im.FileID-1]
					ft := &g.Files[im.TargetID-1]
					if !inUI(fc.Dir()) || !inData(ft.Dir()) {
						continue
					}
					if !g.modOK(fc.ModuleID, mod) {
						continue
					}
					t.rows = append(t.rows, []cell{cs(fc.Path()), cs(ft.Path()),
						ci32(im.Line), cs(im.Target())})
				}
				sortRows(t, func(a, b []cell) bool {
					if a[0].s != b[0].s {
						return a[0].s < b[0].s
					}
					return num(a[2]) < num(b[2])
				})
				return lim(t, n)
			},
		},
	}
}

func b2iStr(s, want string) int {
	if s == want {
		return 1
	}
	return 0
}

func num(c cell) int {
	v := 0
	neg := false
	for i := 0; i < len(c.s); i++ {
		ch := c.s[i]
		if i == 0 && ch == '-' {
			neg = true
			continue
		}
		if ch < '0' || ch > '9' {
			return v
		}
		v = v*10 + int(ch-'0')
	}
	if neg {
		return -v
	}
	return v
}

func splitComma(s string) []string {
	var out []string
	start := 0
	for i := 0; i <= len(s); i++ {
		if i == len(s) || s[i] == ',' {
			out = append(out, s[start:i])
			start = i + 1
		}
	}
	return out
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

var _ = strconv.Itoa

func buildQueriesB() []queryDef {
	return []queryDef{
		{
			Name: "child-process-surface",
			Run: symQ2([]string{"name", "child_process_calls", "exec_calls", "fan_in",
				"sloc", "at"},
				[]int{colName, mNChildProcess, hazardMetric("exec"), mFanIn,
					mSloc, colAt},
				func(m []int32) bool { return m[mNChildProcess] > 0 },
				nil, nil, []ordKey{{3, true}, {1, true}},
				true, false, nil),
		},
		{
			Name: "open-redirect-surface",
			Run: inputCoOccur("open_redirect", mNRedirect, true,
				[]string{"name", "redirect_writes", "input_sites", "kinds", "fan_in", "at"},
				[]ordKey{{4, true}, {1, true}}),
		},
		{
			Name: "ssrf-fetch-surface",
			Run: inputCoOccur("ssrf", mNFetch, true,
				[]string{"name", "fetch_calls", "input_sites", "kinds", "at"},
				[]ordKey{{1, true}, {2, true}}),
		},
		{
			Name: "hardcoded-secret-candidates",
			Run: func(g *Graph, mod string, n int) *table {
				t := &table{cols: []string{"name", "candidate", "line", "at"}}
				for i := range g.Secrets {
					sc := &g.Secrets[i]
					if sc.SymID <= 0 {
						continue
					}
					f := &g.Files[sc.FileID-1]
					if f.IsTest || !g.modOK(f.ModuleID, mod) {
						continue
					}
					if hasPrefix(sc.Value(), "/") || containsStr(sc.Value(), "|") ||
						containsStr(sc.Value(), "%") {
						continue
					}
					s := &g.Symbols[sc.SymID-1]
					at := f.Path() + ":" + itoa(int(sc.Line))
					t.rows = append(t.rows, []cell{cs(s.Name()), cs(sc.Value()),
						ci32(sc.Line), cs(at)})
				}
				sortRows(t, func(a, b []cell) bool {
					return len(a[1].s) > len(b[1].s)
				})
				return lim(t, n)
			},
		},
		{
			Name: "path-traversal-surface",
			Run: inputCoOccur("path_traversal", mNDynamicOpen, true,
				[]string{"name", "open_sites", "input_sites", "kinds", "at"},
				[]ordKey{{1, true}, {2, true}}),
		},
		{
			Name: "unchecked-upload-surface",
			Run: inputCoOccur("upload", mNUploadSave, false,
				[]string{"name", "save_calls", "form_reads", "at"},
				[]ordKey{{1, true}, {2, true}}),
		},
		{
			Name: "zip-slip-surface",
			Run: symQ2([]string{"name", "zip_access", "sloc", "at"},
				[]int{colName, mNZipRead, mSloc, colAt},
				func(m []int32) bool { return m[mNZipRead] > 0 },
				nil, nil, []ordKey{{1, true}, {2, true}},
				true, false, nil),
		},
		{
			Name: "mass-assignment-surface",
			Run: inputCoOccur("mass_assignment", mNMassAssign, true,
				[]string{"name", "assigns", "input_sites", "kinds", "at"},
				[]ordKey{{1, true}, {2, true}}),
		},
		{
			Name: "log-injection-surface",
			Run: inputCoOccur("log_injection", mNLogCall, true,
				[]string{"name", "log_calls", "input_sites", "kinds", "at"},
				[]ordKey{{1, true}, {2, true}}),
		},
		{
			Name: "sensitive-log-surface",
			Run: inputCoOccur("sensitive_log", mNConsoleLog, true,
				[]string{"name", "console_calls", "input_sites", "kinds", "at"},
				[]ordKey{{1, true}, {2, true}}),
		},
		{
			Name: "unauthenticated-input-surface",
			Run: func(g *Graph, mod string, n int) *table {
				sites, kinds := g.inputSitesBySymbol()
				t := &table{cols: []string{"name", "input_sites", "kinds", "at"}}
				var slocs []int32
				for i := range g.Symbols {
					m := g.metrics(int32(i + 1))
					if m[mNAuthCall] != 0 {
						continue
					}
					ss := sites[int32(i+1)]
					if len(ss) == 0 {
						continue
					}
					s := &g.Symbols[i]
					f := &g.Files[s.FileID-1]
					if f.IsTest || !g.modOK(s.ModuleID, mod) {
						continue
					}

					seen := map[string]bool{}
					var kk []string
					for _, k := range kinds[int32(i+1)] {
						if !seen[k] {
							seen[k] = true
							kk = append(kk, k)
						}
					}
					sort.Strings(kk)
					t.rows = append(t.rows, []cell{cs(s.Name()), ci(len(ss)),
						cs(strings.Join(kk, ",")), cs(g.at(s))})
					slocs = append(slocs, m[mSloc])
				}

				type rw struct {
					row []cell
					slc int32
				}
				rws := make([]rw, len(t.rows))
				for i := range t.rows {
					rws[i] = rw{t.rows[i], slocs[i]}
				}
				sort.SliceStable(rws, func(x, y int) bool {
					if num(rws[x].row[1]) != num(rws[y].row[1]) {
						return num(rws[x].row[1]) > num(rws[y].row[1])
					}
					return rws[x].slc > rws[y].slc
				})
				for i := range rws {
					t.rows[i] = rws[i].row
				}
				return lim(t, n)
			},
		},
		{
			Name: "sync-caller-of-async",
			Run: func(g *Graph, mod string, n int) *table {
				t := &table{cols: []string{"async_callee", "caller_fn", "caller_is_async",
					"caller_awaits", "caller_returns", "callee_fan_in", "at"}}

				byCallee := map[int32][]int{}
				for j := range g.Callsites {
					c := g.Callsites[j].Callee
					byCallee[c] = append(byCallee[c], j)
				}
				calleeOrder := g.scanIds(scanOrder{kind: scanNameFile})
				var callerFan []int32
				for _, sid := range calleeOrder {
					ci := int(sid - 1)
					cm := g.metrics(sid)
					if cm[mIsAsync] == 0 {
						continue
					}
					callee := &g.Symbols[ci]
					mine := byCallee[sid]
					sort.SliceStable(mine, func(x, y int) bool {
						return g.Callsites[mine[x]].Line < g.Callsites[mine[y]].Line
					})
					for _, j := range mine {
						cs := &g.Callsites[j]
						caller := &g.Symbols[cs.Caller-1]
						cmm := g.metrics(cs.Caller)
						if cmm[mIsAsync] != 0 && cmm[mNAwait] != 0 {
							continue
						}
						f := &g.Files[caller.FileID-1]
						if f.IsTest || f.IsGen || !g.modOK(caller.ModuleID, mod) {
							continue
						}
						t.rows = append(t.rows, []cell{cs2(callee.Name()), cs2(caller.Name()),
							ci32(cmm[mIsAsync]), ci32(cmm[mNAwait]), ci32(cmm[mNReturns]),
							ci32(cm[mFanIn]),
							cs2(f.Path() + ":" + itoa(int(cs.Line)))})
						callerFan = append(callerFan, cmm[mFanIn])
					}
				}

				type rw struct {
					row []cell
					fan int32
				}
				rws := make([]rw, len(t.rows))
				for i := range t.rows {
					rws[i] = rw{t.rows[i], callerFan[i]}
				}
				sort.SliceStable(rws, func(x, y int) bool {
					if num(rws[x].row[5]) != num(rws[y].row[5]) {
						return num(rws[x].row[5]) > num(rws[y].row[5])
					}
					if rws[x].fan != rws[y].fan {
						return rws[x].fan > rws[y].fan
					}
					return lineOf(rws[x].row[6].s) < lineOf(rws[y].row[6].s)
				})
				for i := range rws {
					t.rows[i] = rws[i].row
				}
				return lim(t, n)
			},
		},
		{
			Name: "never-awaited-api",
			Run: func(g *Graph, mod string, n int) *table {

				callers := map[int32]int32{}
				nonAwait := map[int32]int32{}
				distinct := map[int32]map[int32]bool{}
				for i := range g.Callsites {
					cs := &g.Callsites[i]
					callers[cs.Callee]++
					cm := g.metrics(cs.Caller)
					if cm[mIsAsync] == 0 || cm[mNAwait] == 0 {
						nonAwait[cs.Callee]++
					}
					d := distinct[cs.Callee]
					if d == nil {
						d = map[int32]bool{}
						distinct[cs.Callee] = d
					}
					d[cs.Caller] = true
				}
				t := &table{cols: []string{"async_api", "callers", "non_awaiting_callers",
					"exported", "awaits", "fan_in", "at"}}
				for i := range g.Symbols {
					m := g.metrics(int32(i + 1))
					if m[mIsAsync] == 0 || m[mFanIn] == 0 {
						continue
					}
					id := int32(i + 1)
					c, na := int32(len(distinct[id])), nonAwait[id]
					if na != c {
						continue
					}
					s := &g.Symbols[i]
					f := &g.Files[s.FileID-1]
					if f.IsTest || f.IsGen || !g.modOK(s.ModuleID, mod) {
						continue
					}
					t.rows = append(t.rows, []cell{cs2(s.Name()), ci(int(c)), ci(int(na)),
						ci32(m[mIsExported]), ci32(m[mNAwait]), ci32(m[mFanIn]), cs2(g.at(s))})
				}
				sortRows(t, func(a, b []cell) bool {
					if num(a[1]) != num(b[1]) {
						return num(a[1]) > num(b[1])
					}
					return num(a[5]) > num(b[5])
				})
				return lim(t, n)
			},
		},
		{
			Name: "async-callback-argument",
			Run: symQ2([]string{"name", "async_arguments", "listener_adds", "timer_starts",
				"calls", "fan_in", "at"},
				[]int{colName, mNAsyncCallback, mNListenerAdd, mNTimerSet, mNCalls,
					mFanIn, colAt},
				func(m []int32) bool { return m[mNAsyncCallback] > 0 },
				nil, nil, []ordKey{{1, true}, {5, true}},
				true, true, nil, scanOrder{kind: scanFileLine}),
		},
		{
			Name: "async-event-listener",
			Run: func(g *Graph, mod string, n int) *table {
				t := &table{cols: []string{"registrar", "op", "event", "target", "in_loop",
					"is_add", "fan_in", "at"}}
				for i := range g.Listeners {
					l := &g.Listeners[i]
					if !l.IsAsync {
						continue
					}
					s := &g.Symbols[l.SymID-1]
					m := g.metrics(l.SymID)
					f := &g.Files[s.FileID-1]
					if f.IsTest || f.IsGen || !g.modOK(s.ModuleID, mod) {
						continue
					}
					t.rows = append(t.rows, []cell{cs2(s.Name()), cs2(l.Op()), cs2(l.Event()),
						cs2(l.Target()), cb(l.InLoop), cb(l.Op() == "add"), ci32(m[mFanIn]),
						cs2(f.Path() + ":" + itoa(int(l.Line)))})
				}
				sortRows(t, func(a, b []cell) bool {
					if a[5].s != b[5].s {
						return a[5].s == "i:1"
					}
					if num(a[6]) != num(b[6]) {
						return num(a[6]) > num(b[6])
					}
					return lineOf(a[len(a)-1].s) < lineOf(b[len(b)-1].s)
				})
				return lim(t, n)
			},
		},
		{
			Name: "async-promise-executor",
			Run: symQ2([]string{"name", "async_executors", "promise_alls", "awaits",
				"fan_in", "at"},
				[]int{colName, mNAsyncExecutor, mNPromiseAll, mNAwait, mFanIn, colAt},
				func(m []int32) bool { return m[mNAsyncExecutor] > 0 },
				nil, nil, []ordKey{{1, true}, {4, true}},
				true, true, nil),
		},
		{
			Name: "await-of-non-thenable",
			Run: func(g *Graph, mod string, n int) *table {
				byName := map[string][]int32{}
				for name, cands := range g.byName {
					for _, c := range cands {
						byName[name] = append(byName[name], c.sid)
					}
				}

				pick := func(base string) (int32, bool) {
					var best int32
					var bestKind string
					found := false
					for _, sid := range byName[base] {
						cs := &g.Symbols[sid-1]
						cm := g.metrics(sid)
						if !g_isCallKind(cs.Kind) || cm[mIsAsync] != 0 ||
							containsStr(cs.RetType(), "Promise") {
							continue
						}
						kd := kindNames[cs.Kind]
						if !found || kd < bestKind || (kd == bestKind && sid < best) {
							best, bestKind, found = sid, kd, true
						}
					}
					return best, found
				}
				type grp struct {
					pick    int32
					matches int
					line    int32
				}
				type gkey struct {
					sid, line int32
					base      string
				}
				groups := map[gkey]*grp{}
				for i := range g.Awaited {
					aw := &g.Awaited[i]
					var cands int
					for _, sid := range byName[aw.Base()] {
						s := &g.Symbols[sid-1]
						if !g_isCallKind(s.Kind) {
							continue
						}
						m := g.metrics(sid)
						if m[mIsAsync] != 0 || containsStr(s.RetType(), "Promise") {
							continue
						}
						cands++
					}
					if cands == 0 {
						continue
					}
					p, _ := pick(aw.Base())
					k := gkey{sid: aw.SymID, line: aw.Line, base: aw.Base()}
					gr := groups[k]
					if gr == nil {
						gr = &grp{pick: p, matches: cands, line: aw.Line}
						groups[k] = gr
					}
				}
				t := &table{cols: []string{"awaiting_fn", "awaited_callee", "declared_return",
					"severity", "matching_defs", "fan_in", "at"}}
				gk := make([]gkey, 0, len(groups))
				for k := range groups {
					gk = append(gk, k)
				}
				sort.Slice(gk, func(x, y int) bool {
					if gk[x].sid != gk[y].sid {
						return gk[x].sid < gk[y].sid
					}
					if gk[x].base != gk[y].base {
						return gk[x].base < gk[y].base
					}
					return gk[x].line < gk[y].line
				})

				for _, k := range slices.Backward(gk) {

					gr := groups[k]
					sid := k.sid
					s := &g.Symbols[sid-1]
					m := g.metrics(sid)
					f := &g.Files[s.FileID-1]
					if f.IsTest || f.IsGen || !g.modOK(s.ModuleID, mod) {
						continue
					}
					c := &g.Symbols[gr.pick-1]
					sev := 1
					if containsStr(c.RetType(), "void") {
						sev = 2
					}
					t.rows = append(t.rows, []cell{cs2(s.Name()),
						cs2(k.base), cs2(c.RetType()),
						ci(sev), ci(gr.matches), ci32(m[mFanIn]),
						cs2(f.Path() + ":" + itoa(int(gr.line)))})
				}
				sortRows(t, func(a, b []cell) bool {
					if num(a[3]) != num(b[3]) {
						return num(a[3]) > num(b[3])
					}
					if num(a[5]) != num(b[5]) {
						return num(a[5]) > num(b[5])
					}
					return lineOf(a[len(a)-1].s) < lineOf(b[len(b)-1].s)
				})
				return lim(t, n)
			},
		},
		{
			Name: "async-work-in-constructor",
			Run: func(g *Graph, mod string, n int) *table {
				type acc struct {
					callees map[int32]bool
					names   []string
					seen    map[string]bool
				}
				accs := map[int32]*acc{}
				for i := range g.Callsites {
					cs := &g.Callsites[i]
					ctor := &g.Symbols[cs.Caller-1]
					if ctor.Name() != "constructor" {
						continue
					}
					cm := g.metrics(cs.Callee)
					if cm[mIsAsync] == 0 {
						continue
					}
					f := &g.Files[ctor.FileID-1]
					if f.IsTest || f.IsGen || !g.modOK(ctor.ModuleID, mod) {
						continue
					}
					a := accs[cs.Caller]
					if a == nil {
						a = &acc{callees: map[int32]bool{}, seen: map[string]bool{}}
						accs[cs.Caller] = a
					}
					if !a.callees[cs.Callee] {
						a.callees[cs.Callee] = true
						nm := g.Symbols[cs.Callee-1].Name()
						if !a.seen[nm] {
							a.seen[nm] = true
							a.names = append(a.names, nm)
						}
					}
				}
				t := &table{cols: []string{"class_", "async_callees", "callees_called",
					"io", "net", "fan_in", "at"}}

				ctorIDs := make([]int32, 0, len(accs))
				for id := range accs {
					ctorIDs = append(ctorIDs, id)
				}
				slices.Sort(ctorIDs)
				for _, ctorID := range ctorIDs {
					a := accs[ctorID]
					ctor := &g.Symbols[ctorID-1]
					cm := g.metrics(ctorID)
					cls := cnull()
					if ctor.ParentID > 0 {
						cls = cs(g.Symbols[ctor.ParentID-1].Name())
					}
					t.rows = append(t.rows, []cell{cls, ci(len(a.callees)),
						cs2(joinComma(a.names)),
						ci32(cm[hazardMetric("io")]),
						ci32(cm[hazardMetric("net")]),
						ci32(cm[mFanIn]), cs2(g.at(ctor))})
				}
				sortRows(t, func(a, b []cell) bool {
					if num(a[1]) != num(b[1]) {
						return num(a[1]) > num(b[1])
					}
					return num(a[5]) > num(b[5])
				})
				return lim(t, n)
			},
		},
		{
			Name: "import-cycle-chain",
			Run: func(g *Graph, mod string, n int) *table {

				const maxDepth = 5
				type edge struct {
					to   int32
					line int32
				}
				adj := map[int32][]edge{}
				for i := range g.Imports {
					im := &g.Imports[i]
					if im.IsTypeOnly || im.TargetID < 0 {
						continue
					}
					adj[im.FileID] = append(adj[im.FileID], edge{im.TargetID, im.Line})
				}
				type walkState struct {
					a, b    int32
					depth   int
					path    string
					firstLn int32
				}
				var queue []walkState
				for i := range g.Imports {
					im := &g.Imports[i]
					if im.IsTypeOnly || im.TargetID < 0 {
						continue
					}
					queue = append(queue, walkState{a: im.FileID, b: im.TargetID,
						depth:   1,
						path:    g.Files[im.FileID-1].Path() + "|" + g.Files[im.TargetID-1].Path(),
						firstLn: im.Line})
				}
				type row struct {
					start   int32
					cycle   string
					hops    int
					firstLn int32
				}
				var rows []row
				for head := 0; head < len(queue); head++ {
					st := queue[head]
					if st.depth >= maxDepth {
						continue
					}
					for _, e := range adj[st.b] {
						nd := st.depth + 1
						tp := g.Files[e.to-1].Path()
						if e.to != st.a && containsStr(st.path+"|", tp+"|") {
							continue
						}
						if e.to == st.a {
							if nd >= 3 {
								rows = append(rows, row{start: st.a,
									cycle: st.path + "|" + tp, hops: nd,
									firstLn: st.firstLn})
							}

							queue = append(queue, walkState{a: st.a, b: e.to,
								depth: nd, path: st.path + "|" + tp,
								firstLn: st.firstLn})
							continue
						}
						queue = append(queue, walkState{a: st.a, b: e.to,
							depth: nd, path: st.path + "|" + tp,
							firstLn: st.firstLn})
					}
				}
				t := &table{cols: []string{"start_file", "cycle", "hops", "at"}}
				for _, r := range rows {
					f0 := &g.Files[r.start-1]
					if f0.IsTest || f0.IsGen || !g.modOK(f0.ModuleID, mod) {
						continue
					}
					t.rows = append(t.rows, []cell{cs2(f0.Path()), cs2(r.cycle),
						ci(r.hops), cs2(f0.Path() + ":" + itoa(int(r.firstLn)))})
				}
				sortRows(t, func(a, b []cell) bool {
					if num(a[2]) != num(b[2]) {
						return num(a[2]) < num(b[2])
					}
					return a[1].s < b[1].s
				})
				return lim(t, n)
			},
		},
		{
			Name: "unprotected-async-entry",
			Run: symQ2([]string{"name", "fan_in", "awaits", "calls", "exported",
				"handler", "at"},
				[]int{colName, mFanIn, mNAwait, mNCalls, mIsExported, mIsHandler, colAt},
				func(m []int32) bool {
					return m[mIsAsync] == 1 && m[mNAwait] > 0 && m[mNTry] == 0 &&
						m[mNCatch] == 0 && m[mNThenChain] == 0 && m[mFanIn] > 0
				},
				nil, nil, []ordKey{{1, true}, {2, true}},
				true, true, nil),
		},
		{
			Name: "unconsumed-disposables",
			Run: func(g *Graph, mod string, n int) *table {
				callers := map[int32]map[int32]bool{}
				for i := range g.Callsites {
					cs := &g.Callsites[i]
					d := callers[cs.Callee]
					if d == nil {
						d = map[int32]bool{}
						callers[cs.Callee] = d
					}
					d[cs.Caller] = true
				}
				t := &table{cols: []string{"factory", "return_type", "callers",
					"callers_never_dispose", "fan_in", "at"}}
				for i := range g.Symbols {
					s := &g.Symbols[i]
					if s.RetType() == "" || !containsStr(s.RetType(), "Disposable") {
						continue
					}
					m := g.metrics(int32(i + 1))
					if m[mFanIn] == 0 {
						continue
					}
					never := 0
					for cid := range callers[int32(i+1)] {
						if g.metrics(cid)[mNDisposeCall] == 0 {
							never++
						}
					}
					if never == 0 {
						continue
					}
					f := &g.Files[s.FileID-1]
					if f.IsTest || f.IsGen || !g.modOK(s.ModuleID, mod) {
						continue
					}
					t.rows = append(t.rows, []cell{cs2(s.Name()), cs2(s.RetType()),
						ci(len(callers[int32(i+1)])), ci(never), ci32(m[mFanIn]),
						cs2(g.at(s))})
				}
				sortRows(t, func(a, b []cell) bool {
					if num(a[3]) != num(b[3]) {
						return num(a[3]) > num(b[3])
					}
					return num(a[4]) > num(b[4])
				})
				return lim(t, n)
			},
		},
		{
			Name: "unvalidated-dto-into-io",
			Run: func(g *Graph, mod string, n int) *table {
				decorated := map[int32]bool{}
				for i := range g.Attributes {
					decorated[g.Attributes[i].SymID] = true
				}
				fields := map[int32]int32{}
				for i := range g.Fields {
					fields[g.Fields[i].SymID]++
				}
				t := &table{cols: []string{"consumer", "unvalidated_dto", "arg", "dto_fields",
					"io_calls", "handler", "fan_in", "at"}}

				paramsOf := map[int32][]int{}
				for i := range g.Params {
					if g.Params[i].Type() == "" {
						continue
					}
					paramsOf[g.Params[i].SymID] = append(paramsOf[g.Params[i].SymID], i)
				}
				for _, sid := range g.scanIds(scanOrder{kind: scanKindID}) {
					s := &g.Symbols[sid-1]
					if s.Kind != kFunction && s.Kind != kMethod {
						continue
					}
					sm := g.metrics(sid)
					io := sm[hazardMetric("io")] + sm[hazardMetric("net")] +
						sm[mNFetch]
					if io == 0 && sm[mIsHandler] == 0 {
						continue
					}
					f := &g.Files[s.FileID-1]
					if f.IsTest || f.IsGen || !g.modOK(s.ModuleID, mod) {
						continue
					}
					for _, pi := range paramsOf[sid] {
						p := &g.Params[pi]

						want := ltrimSet(p.Type(), ": ")
						for _, tid := range g.byName[want] {
							td := &g.Symbols[tid.sid-1]
							if td.Kind != kClass && td.Kind != kInterface {
								continue
							}
							if decorated[tid.sid] {
								continue
							}
							t.rows = append(t.rows, []cell{cs2(s.Name()), cs2(td.Name()),
								cs2(p.Name()), ci(int(fields[tid.sid])), ci(int(io)),
								ci32(sm[mIsHandler]), ci32(sm[mFanIn]), cs2(g.at(s))})
						}
					}
				}
				sortRows(t, func(a, b []cell) bool {
					av := num(a[6]) + num(a[4])
					bv := num(b[6]) + num(b[4])
					if av != bv {
						return av > bv
					}
					return num(a[3]) > num(b[3])
				})
				return lim(t, n)
			},
		},
		{
			Name: "singleton-request-state",
			Run: func(g *Graph, mod string, n int) *table {
				mut := map[int32]int32{}
				for i := range g.Fields {
					fl := &g.Fields[i]
					if fl.IsMut {
						mut[fl.SymID]++
					}
				}
				classInput := map[int32]int32{}
				for i := range g.InputSites {
					u := &g.InputSites[i]
					p := g.Symbols[u.SymID-1].ParentID
					if p > 0 {
						classInput[p]++
					}
				}
				t := &table{cols: []string{"class_", "mutable_fields", "input_reads_in_methods",
					"exported", "fan_in", "at"}}
				for i := range g.Symbols {
					s := &g.Symbols[i]
					if s.Kind != kClass {
						continue
					}
					nm, ir := mut[int32(i+1)], classInput[int32(i+1)]
					if nm == 0 || ir == 0 {
						continue
					}
					m := g.metrics(int32(i + 1))
					f := &g.Files[s.FileID-1]
					if f.IsTest || f.IsGen || !g.modOK(s.ModuleID, mod) {
						continue
					}
					t.rows = append(t.rows, []cell{cs2(s.Name()), ci32(nm), ci32(ir),
						ci32(m[mIsExported]), ci32(m[mFanIn]), cs2(g.at(s))})
				}
				sortRows(t, func(a, b []cell) bool {
					av := num(a[2]) * num(a[1])
					bv := num(b[2]) * num(b[1])
					if av != bv {
						return av > bv
					}
					return num(a[4]) > num(b[4])
				})
				return lim(t, n)
			},
		},
		{
			Name: "unsound-reachable",
			Run: func(g *Graph, mod string, n int) *table {
				roots := g.entryRoots(false)
				depth := g.bfsDepth(roots, 4, nil)
				t := &table{cols: []string{"name", "hops", "as_any", "bang", "suppressions",
					"anys", "fan_in", "at"}}

				ids := make([]int32, 0, len(depth))
				for id := range depth {
					ids = append(ids, id)
				}
				slices.Sort(ids)
				for _, id := range ids {
					d := depth[id]
					if d == 0 {
						continue
					}
					m := g.metrics(id)
					if m[mNAsAny] == 0 && m[mNNonNull] == 0 && m[mNSuppressions] == 0 {
						continue
					}
					s := &g.Symbols[id-1]
					f := &g.Files[s.FileID-1]
					if f.IsTest || f.IsGen || !g.modOK(s.ModuleID, mod) {
						continue
					}
					t.rows = append(t.rows, []cell{cs2(s.Name()), ci(d), ci32(m[mNAsAny]),
						ci32(m[mNNonNull]), ci32(m[mNSuppressions]), ci32(m[mNAnyTotal]),
						ci32(m[mFanIn]), cs2(g.at(s))})
				}
				sortRows(t, func(a, b []cell) bool {
					av := num(a[2])*3 + num(a[3]) + num(a[4])
					bv := num(b[2])*3 + num(b[3]) + num(b[4])
					if av != bv {
						return av > bv
					}
					return num(a[1]) < num(b[1])
				})
				return lim(t, n)
			},
		},
		{
			Name: "decorated-method-zero-caller",
			Run: func(g *Graph, mod string, n int) *table {
				type acc struct {
					names []string
					seen  map[string]bool
				}
				attrs := map[int32]*acc{}
				for i := range g.Attributes {
					a := &g.Attributes[i]
					ac := attrs[a.SymID]
					if ac == nil {
						ac = &acc{seen: map[string]bool{}}
						attrs[a.SymID] = ac
					}
					if !ac.seen[a.Name()] {
						ac.seen[a.Name()] = true
						ac.names = append(ac.names, a.Name())
					}
				}
				t := &table{cols: []string{"name", "class_", "n_decorators", "decorators",
					"static", "sloc", "fan_in", "at"}}

				ids := make([]int32, 0, len(attrs))
				for id := range attrs {
					ids = append(ids, id)
				}
				slices.Sort(ids)
				for _, id := range ids {
					ac := attrs[id]
					s := &g.Symbols[id-1]
					if s.Kind != kMethod {
						continue
					}
					m := g.metrics(id)
					if m[mFanIn] != 0 || m[mIsDeclarationOnly] != 0 {
						continue
					}
					f := &g.Files[s.FileID-1]
					if f.IsTest || f.IsGen || !g.modOK(s.ModuleID, mod) {
						continue
					}
					cls := cnull()
					if s.ParentID > 0 {
						cls = cs(g.Symbols[s.ParentID-1].Name())
					}
					t.rows = append(t.rows, []cell{cs2(s.Name()), cls,
						ci(len(ac.names)), cs2(joinComma(ac.names)),
						ci32(m[mIsStatic]), ci32(m[mSloc]), ci32(m[mFanIn]), cs2(g.at(s))})
				}
				sortRows(t, func(a, b []cell) bool {
					if num(a[5]) != num(b[5]) {
						return num(a[5]) > num(b[5])
					}
					return num(a[2]) > num(b[2])
				})
				return lim(t, n)
			},
		},
		{
			Name: "getter-setter-mismatch",
			Run: func(g *Graph, mod string, n int) *table {
				type classProp struct {
					parent int32
					name   string
				}
				type acc struct {
					get, set int32
					decls    int32
					fanIn    int32
					minLine  int32
				}
				groups := map[classProp]*acc{}

				for i := range g.Symbols {
					s := &g.Symbols[i]
					if s.ParentID <= 0 {
						continue
					}
					m := g.metrics(int32(i + 1))
					if s.Kind != kMethod || (m[mIsGetter] == 0 && m[mIsSetter] == 0) {
						continue
					}
					f := &g.Files[s.FileID-1]
					if f.IsTest || f.IsGen || !g.modOK(s.ModuleID, mod) {
						continue
					}
					k := classProp{s.ParentID, s.Name()}
					a := groups[k]
					if a == nil {
						a = &acc{minLine: s.LineStart}
						groups[k] = a
					}
					if m[mIsGetter] > a.get {
						a.get = 1
					}
					if m[mIsSetter] > a.set {
						a.set = 1
					}
					a.decls++
					if m[mFanIn] > a.fanIn {
						a.fanIn = m[mFanIn]
					}
					if s.LineStart < a.minLine {
						a.minLine = s.LineStart
					}
				}
				t := &table{cols: []string{"class_", "property", "has_getter", "has_setter",
					"declarations", "fan_in", "at"}}

				gks := make([]classProp, 0, len(groups))
				for k := range groups {
					gks = append(gks, k)
				}
				sort.Slice(gks, func(x, y int) bool {
					if gks[x].parent != gks[y].parent {
						return gks[x].parent < gks[y].parent
					}
					return gks[x].name < gks[y].name
				})

				for _, k := range slices.Backward(gks) {

					a := groups[k]
					if a.get == a.set {
						continue
					}
					parent, prop := k.parent, k.name
					cls := ""
					var fileID int32
					if parent > 0 {
						cls = g.Symbols[parent-1].Name()
						fileID = g.Symbols[parent-1].FileID
					}
					at := ""
					if fileID > 0 {
						at = g.Files[fileID-1].Path() + ":" + itoa(int(a.minLine))
					}
					t.rows = append(t.rows, []cell{cs2(cls), cs2(prop), ci32(a.get),
						ci32(a.set), ci32(a.decls), ci32(a.fanIn), cs2(at)})
				}
				sortRows(t, func(a, b []cell) bool {
					if num(a[4]) != num(b[4]) {
						return num(a[4]) > num(b[4])
					}
					return num(a[5]) > num(b[5])
				})
				return lim(t, n)
			},
		},
		{
			Name: "async-side-effect-getter",
			Run: symQ2([]string{"getter", "class_", "awaits", "io", "net", "fetches", "dom",
				"fan_in", "at"},
				[]int{colName, colPar, mNAwait, hazardMetric("io"),
					hazardMetric("net"), mNFetch, hazardMetric("dom"),
					mFanIn, colAt},
				func(m []int32) bool {
					return m[mIsGetter] == 1 &&
						(m[mNAwait]+m[hazardMetric("io")]+m[hazardMetric("net")]+
							m[mNFetch]+m[hazardMetric("dom")]) > 0
				},

				func(m []int32) int {
					return int(m[mNAwait])*3 + int(m[hazardMetric("io")]) +
						int(m[hazardMetric("net")]) + int(m[mNFetch]) +
						int(m[hazardMetric("dom")])
				},
				nil, []ordKey{{7, true}}, true, true, nil),
		},
		{
			Name: "async-without-await",
			Run: symQ2([]string{"name", "fan_in", "returns_", "then_chains", "exported", "at"},
				[]int{colName, mFanIn, mNReturns, mNThenChain, mIsExported, colAt},
				func(m []int32) bool {
					return m[mIsAsync] == 1 && m[mNAwait] == 0 && m[mNThenChain] == 0 &&
						m[mFanIn] > 0
				},
				nil, nil, []ordKey{{1, true}, {2, true}},
				true, true, nil),
		},
		{
			Name: "then-without-catch",
			Run: symQ2([]string{"name", "then_calls", "awaits", "catch_blocks", "fan_in", "at"},
				[]int{colName, mNThenChain, mNAwait, mNCatch, mFanIn, colAt},
				func(m []int32) bool { return m[mNThenChain] > 0 && m[mNCatch] == 0 },
				nil, nil, []ordKey{{1, true}, {4, true}},
				true, true, nil),
		},
		{
			Name: "discarded-promise-chain",
			Run: symQ2([]string{"name", "then_calls", "return_type", "fan_in", "exported", "at"},
				[]int{colName, mNThenChain, colRet, mFanIn, mIsExported, colAt},
				func(m []int32) bool {
					return m[mNThenChain] > 0 && m[mFanIn] > 0
				},
				nil, nil, []ordKey{{1, true}, {3, true}},
				true, true,

				func(s *Symbol) bool {
					return s.RetType() == "" || containsStr(s.RetType(), "void")
				}),
		},
		{
			Name: "handler-unguarded-await",
			Run: func(g *Graph, mod string, n int) *table {
				reads := map[int32]int32{}
				for i := range g.InputSites {
					reads[g.InputSites[i].SymID]++
				}
				t := &table{cols: []string{"name", "awaits", "catch_blocks", "input_reads",
					"fan_in", "at"}}
				for i := range g.Symbols {
					m := g.metrics(int32(i + 1))
					if m[mIsHandler] != 1 || m[mNAwait] == 0 || m[mNTry] != 0 {
						continue
					}
					s := &g.Symbols[i]
					f := &g.Files[s.FileID-1]
					if f.IsTest || f.IsGen || !g.modOK(s.ModuleID, mod) {
						continue
					}
					t.rows = append(t.rows, []cell{cs2(s.Name()), ci32(m[mNAwait]),
						ci32(m[mNCatch]), ci(int(reads[int32(i+1)])), ci32(m[mFanIn]), cs2(g.at(s))})
				}
				sortRows(t, func(a, b []cell) bool {
					if num(a[1]) != num(b[1]) {
						return num(a[1]) > num(b[1])
					}
					return num(a[3]) > num(b[3])
				})
				return lim(t, n)
			},
		},
		{
			Name: "timer-async-callback",
			Run: symQ2([]string{"name", "timers_started", "async_arguments", "timers_cleared",
				"timers_in_loop", "fan_in", "at"},
				[]int{colName, mNTimerSet, mNAsyncCallback, mNTimerClear, mTimerInLoop,
					mFanIn, colAt},
				func(m []int32) bool { return m[mNTimerSet] > 0 && m[mNAsyncCallback] > 0 },
				nil, nil, []ordKey{{1, true}, {2, true}},
				true, true, nil),
		},
		{
			Name: "override-without-super",

			Run: func(g *Graph, mod string, n int) *table {
				t := &table{cols: []string{"method", "class_", "class_fan_in", "sloc",
					"cyclo", "fan_in", "at"}}

				for i := range g.Symbols {
					s := &g.Symbols[i]
					m := g.metrics(int32(i + 1))
					if m[mIsOverride] != 1 || m[mNSuperCalls] != 0 || s.Kind != kMethod {
						continue
					}
					if s.ParentID <= 0 {
						continue
					}
					f := &g.Files[s.FileID-1]
					if f.IsTest || f.IsGen || !g.modOK(s.ModuleID, mod) {
						continue
					}
					var classFanIn int32
					if s.ParentID > 0 {
						classFanIn = g.metrics(s.ParentID)[mFanIn]
					}
					t.rows = append(t.rows, []cell{cs(s.Name()), cs(g.parentName(s)),
						ci32(classFanIn), ci32(m[mSloc]), ci32(m[mCyclomatic]),
						ci32(m[mFanIn]), cs(g.at(s))})
				}
				sortRows(t, func(a, b []cell) bool {
					if num(a[2]) != num(b[2]) {
						return num(a[2]) > num(b[2])
					}
					return num(a[3]) > num(b[3])
				})
				return lim(t, n)
			},
		},
		{
			Name: "service-dependency-cycle",
			Run: func(g *Graph, mod string, n int) *table {
				pairSet := map[uint64]bool{}
				for i := range g.Edges {
					e := &g.Edges[i]
					if e.Self {
						continue
					}
					ca := &g.Symbols[e.Caller-1]
					cb := &g.Symbols[e.Callee-1]
					if ca.ParentID <= 0 || cb.ParentID <= 0 || ca.ParentID == cb.ParentID {
						continue
					}
					pairSet[pair(ca.ParentID, cb.ParentID)] = true
				}
				t := &table{cols: []string{"class_a", "class_b", "coupled_pairs",
					"fan_in_a", "fan_in_b", "at"}}

				idx := make([]int, len(g.Edges))
				for i := range idx {
					idx[i] = i
				}
				sort.Slice(idx, func(x, y int) bool {
					if g.Edges[idx[x]].Callee != g.Edges[idx[y]].Callee {
						return g.Edges[idx[x]].Callee < g.Edges[idx[y]].Callee
					}
					return idx[x] < idx[y]
				})
				var keys []uint64
				for _, i := range idx {
					e := &g.Edges[i]
					if e.Self {
						continue
					}
					ca := &g.Symbols[e.Caller-1]
					cb := &g.Symbols[e.Callee-1]
					if ca.ParentID <= 0 || cb.ParentID <= 0 || ca.ParentID == cb.ParentID {
						continue
					}
					a, b := ca.ParentID, cb.ParentID
					if a >= b || !pairSet[pair(b, a)] {
						continue
					}
					k := pair(a, b)
					dup := slices.Contains(keys, k)
					if !dup {
						keys = append(keys, k)
					}
				}
				for _, k := range keys {
					a, b := int32(k>>32), int32(k&0xffffffff)
					sa := &g.Symbols[a-1]
					f := &g.Files[sa.FileID-1]
					if f.IsTest || f.IsGen || !g.modOK(sa.ModuleID, mod) {
						continue
					}
					sb := &g.Symbols[b-1]

					c := 0
					if pairSet[pair(a, b)] {
						c++
					}
					if pairSet[pair(b, a)] {
						c++
					}
					t.rows = append(t.rows, []cell{cs2(sa.Name()), cs2(sb.Name()), ci(c),
						ci32(g.metrics(a)[mFanIn]), ci32(g.metrics(b)[mFanIn]),
						cs2(g.at(sa))})
				}
				sortRows(t, func(a, b []cell) bool {
					if num(a[2]) != num(b[2]) {
						return num(a[2]) > num(b[2])
					}
					return num(a[3]) > num(b[3])
				})
				return lim(t, n)
			},
		},
		{
			Name: "mixed-await-styles",
			Run: symQ2([]string{"name", "awaits", "then_calls", "catch_blocks", "fan_in", "at"},
				[]int{colName, mNAwait, mNThenChain, mNCatch, mFanIn, colAt},
				func(m []int32) bool { return m[mNAwait] > 0 && m[mNThenChain] > 0 },

				scoreOf(mNAwait, mNThenChain), nil, []ordKey{{4, true}}, true, true, nil),
		},
		{
			Name: "async-void-api",
			Run: symQ2([]string{"name", "return_type", "awaits", "fan_in", "exported",
				"handler", "at"},
				[]int{colName, colRet, mNAwait, mFanIn, mIsExported, mIsHandler, colAt},
				func(m []int32) bool {
					return m[mIsAsync] == 1 && m[mFanIn] > 0
				},
				nil, nil, []ordKey{{3, true}, {2, true}},
				true, true,
				func(s *Symbol) bool { return containsStr(s.RetType(), "void") }),
		},
		{
			Name: "unbounded-concurrency",
			Run: symQ2([]string{"name", "all_in_loop", "total_promise_all", "awaits_in_loop",
				"async_arguments", "fan_in", "at"},
				[]int{colName, mNPromiseAllInLoop, mNPromiseAll, mAwaitInLoop,
					mNAsyncCallback, mFanIn, colAt},
				func(m []int32) bool { return m[mNPromiseAllInLoop] > 0 },
				nil, nil, []ordKey{{1, true}, {3, true}},
				true, true, nil),
		},
		{
			Name: "module-scope-io",
			Run: symQ2([]string{"module_init", "io", "net", "fetches", "sync_fs",
				"child_proc", "timers_started", "at"},
				[]int{colName, hazardMetric("io"), hazardMetric("net"),
					mNFetch, mNFsSync, mNChildProcess, mNTimerSet, colAt},
				func(m []int32) bool {
					return m[hazardMetric("io")]+m[hazardMetric("net")]+
						m[mNFetch]+m[mNFsSync]+m[mNChildProcess]+m[mNTimerSet] > 0
				},

				func(m []int32) int {
					return int(m[hazardMetric("io")]) + int(m[hazardMetric("net")]) +
						int(m[mNFetch]) + int(m[mNFsSync]) +
						int(m[mNChildProcess]) + int(m[mNTimerSet])
				},
				nil, nil, true, true,
				func(s *Symbol) bool { return s.Kind == kModule && s.Name() == "<module>" }),
		},
		{
			Name: "untyped-handler-input",
			Run: func(g *Graph, mod string, n int) *table {
				reads := map[int32]int32{}
				for i := range g.InputSites {
					reads[g.InputSites[i].SymID]++
				}
				t := &table{cols: []string{"name", "any_params", "input_reads", "handler",
					"fan_in", "at"}}
				for i := range g.Symbols {
					m := g.metrics(int32(i + 1))
					if m[mIsHandler] != 1 || m[mNAnyParams] == 0 {
						continue
					}
					s := &g.Symbols[i]
					if s.Kind != kFunction && s.Kind != kMethod {
						continue
					}
					f := &g.Files[s.FileID-1]
					if f.IsTest || f.IsGen || !g.modOK(s.ModuleID, mod) {
						continue
					}
					t.rows = append(t.rows, []cell{cs2(s.Name()), ci32(m[mNAnyParams]),
						ci(int(reads[int32(i+1)])), ci32(m[mIsHandler]), ci32(m[mFanIn]),
						cs2(g.at(s))})
				}
				sortRows(t, func(a, b []cell) bool {
					if num(a[1]) != num(b[1]) {
						return num(a[1]) > num(b[1])
					}
					return num(a[2]) > num(b[2])
				})
				return lim(t, n)
			},
		},
		{
			Name: "deep-then-chain",
			Run: symQ2([]string{"name", "then_calls", "awaits", "catch_blocks", "cog",
				"fan_in", "at"},
				[]int{colName, mNThenChain, mNAwait, mNCatch, mCognitive, mFanIn, colAt},
				func(m []int32) bool { return m[mNThenChain] >= 3 },
				nil, nil, []ordKey{{1, true}, {4, true}},
				true, true, nil),
		},
	}
}

func inputCoOccur(tag string, sinkCol int, useKinds bool, cols []string,
	order []ordKey) func(*Graph, string, int) *table {
	return func(g *Graph, mod string, n int) *table {
		type acc struct {
			n     int32
			kinds []string
			seen  map[string]bool
		}
		sites, kinds := g.inputSitesBySymbol()
		accs := map[int32]*acc{}
		for id, ss := range sites {
			a := accs[id]
			if a == nil {
				a = &acc{seen: map[string]bool{}}
				accs[id] = a
			}

			a.n = int32(len(ss))
			for _, k := range kinds[id] {
				if !a.seen[k] {
					a.seen[k] = true
					a.kinds = append(a.kinds, k)
				}
			}
		}
		t := &table{cols: cols}
		for i := range g.Symbols {
			id := int32(i + 1)
			a := accs[id]
			if a == nil {
				continue
			}
			m := g.metrics(id)
			if m[sinkCol] == 0 {
				continue
			}
			s := &g.Symbols[i]
			f := &g.Files[s.FileID-1]
			if f.IsTest || !g.modOK(s.ModuleID, mod) {
				continue
			}

			row := make([]cell, len(cols))
			for j, name := range cols {
				switch name {
				case "name":
					row[j] = cs2(s.Name())
				case "at":
					row[j] = cs2(g.at(s))
				case "fan_in":
					row[j] = ci32(m[mFanIn])
				case "kinds":
					row[j] = cs2(joinDistinct(a.kinds))
				case "input_sites", "form_reads":
					row[j] = ci(int(a.n))
				default:
					row[j] = ci32(m[sinkCol])
				}
			}
			t.rows = append(t.rows, row)
		}
		sortRows(t, func(a, b []cell) bool {
			for _, k := range order {
				x, y := num(a[k.col]), num(b[k.col])
				if x == y {
					continue
				}
				if k.desc {
					return x > y
				}
				return x < y
			}
			return false
		})
		return lim(t, n)
	}
}

func (g *Graph) inputSitesBySymbol() (map[int32][]int32, map[int32][]string) {
	sites := map[int32][]int32{}
	kinds := map[int32][]string{}
	for i := range g.InputSites {
		u := &g.InputSites[i]
		sites[u.SymID] = append(sites[u.SymID], int32(i+1))
		kinds[u.SymID] = append(kinds[u.SymID], u.Kind())
	}
	return sites, kinds
}

var _ = sort.Ints

var logLevels = map[string]bool{
	"debug": true, "info": true, "warn": true, "warning": true, "error": true,
	"fatal": true, "trace": true, "log": true,
}

var authMarkers = []string{"auth", "login", "jwt", "isauthenticated", "passport", "session"}

var loopCallCounters = []struct {
	needle string
	col    int16
}{
	{"addEventListener", mListenerInLoop},
	{"setTimeout", mTimerInLoop},
	{"setInterval", mTimerInLoop},
	{"JSON.parse", mParseInLoop},
	{"querySelector", mDomInLoop},
	{"querySelectorAll", mDomInLoop},
}

func (e *extractor) onCall(t *Tree, s srcFile, node int, m *meas, loopDepth int32) {
	m.bump(mNCalls)
	inLoop := loopDepth > 0
	if inLoop {
		m.bump(mCallInLoop)
	}
	f := t.f()
	args := t.fieldChild(node, f.arguments)

	asyncArgs := int32(0)
	if args >= 0 {
		for k := t.namedCount(args) - 1; k >= 0; k-- {
			a := t.namedChild(args, k)
			if isFnKind(t.codeAt(a)) && t.start(a)+5 <= len(s.data) &&
				string(s.data[t.start(a):t.start(a)+5]) == "async" {
				asyncArgs++
			}
		}
	}
	if asyncArgs > 0 {
		m.bumpN(mNAsyncCallback, asyncArgs)
		fn0 := t.fieldChild(node, f.function)
		if fn0 < 0 {
			fn0 = t.fieldChild(node, f.constructor)
		}
		if fn0 >= 0 && cgStrip(t.text(fn0, s)) == "Promise" {
			m.bump(mNAsyncExecutor)
		}
	}

	fn := t.fieldChild(node, f.function)
	line := int32(t.srow(node)) + 1
	if fn < 0 {
		m.bump(mNDynamicCalls)
		m.calls = append(m.calls, callRec{line: line, dynamic: true, inLoop: inLoop})
		return
	}
	name := s.strStripN(t.start(fn), t.end(fn), 1<<30)
	nl := lowerStr(name)
	b := afterLastDot(name)
	if name == "super" || hasPrefix(name, "super.") {
		m.bump(mNSuperCalls)
	}
	switch b {
	case "exec", "execSync", "spawnSync":
		if containsStr(name, "child_process") {
			m.bump(mNChildProcess)
		}
	case "fetch":
		m.bump(mNFetch)
	case "readFile", "readFileSync", "writeFile", "writeFileSync":
		if hasPrefix(name, "fs.") {
			if args >= 0 {
				if first := t.namedChild(args, 0); first >= 0 {
					if c := t.codeAt(first); c != cString && c != cTemplateString {
						m.bump(mNDynamicOpen)
					}
				}
			}
		}
	}
	if hasPrefix(name, "axios.") || hasPrefix(name, "got.") ||
		hasPrefix(name, "superagent.") || hasPrefix(name, "node-fetch") ||
		hasPrefix(name, "http.request") || hasPrefix(name, "https.request") {
		m.bump(mNFetch)
	}
	if (b == "writeFile" || b == "writeFileSync") && hasPrefix(name, "fs.") {
		if args >= 0 && t.namedCount(args) > 0 {
			for c := t.firstChild(args); c >= 0; c = t.nextSibling(c) {
				if t.cols.named[c] == 0 {
					continue
				}
				cc := t.codeAt(c)
				if cc != cMemberExpression && cc != cIdentifier {
					continue
				}
				a := cgStrip(t.text(c, s))
				if hasPrefix(a, "req.") || hasPrefix(a, "request.") || hasPrefix(a, "file") {
					m.bump(mNUploadSave)
					break
				}
			}
		}
	}
	if containsStr(nl, "unzip") ||
		(containsStr(nl, "zip") && (b == "extract" || b == "extractAll" ||
			b == "extractAllTo" || b == "extractFiles")) {
		m.bump(mNZipRead)
	}
	if b == "assign" && hasPrefix(name, "Object.") {
		m.bump(mNMassAssign)
	}
	if logLevels[b] && containsStr(nl, "logger") {
		m.bump(mNLogCall)
	}
	if hasPrefix(name, "console.") && logLevels[b] {
		m.bump(mNConsoleLog)
	}
	for _, k := range authMarkers {
		if containsStr(nl, k) {
			m.bump(mNAuthCall)
			break
		}
	}
	switch b {
	case "readFileSync", "writeFileSync", "existsSync":
		m.bump(mNFsSync)
	case "push", "concat", "unshift":
		if inLoop {
			m.bump(mNArrayGrowInLoop)
		}
	case "indexOf", "includes", "find":
		if inLoop {
			m.bump(mNSearchInLoop)
		}
	case "parse":
		if hasPrefix(name, "JSON") && inLoop {
			m.bump(mNJsonParseInLoop)
		}
	case "then":
		if inLoop {
			m.bump(mNThenInLoop)
		}
	case "assign":
		if hasPrefix(name, "Object") && inLoop {
			m.bump(mNAssignInLoop)
		}
	case "dispose", "unsubscribe", "removeEventListener":
		m.bump(mNDisposeCall)
	}
	if name == "Math.random" {
		m.bump(mNMathRandom)
	}
	if name == "process.exit" {
		m.bump(mNProcessExit)
	}

	r := firstRune(name)
	dynamic := name == "" || (!isAlphaRune(r) && r != '_' && r != '$')
	m.calls = append(m.calls, callRec{
		name: cutStr(name, 200), line: line, dynamic: dynamic, inLoop: inLoop,
	})
	if dynamic {
		m.bump(mNDynamicCalls)
	}
	if inLoop {
		for _, lc := range loopCallCounters {
			if lc.needle == b || containsStr(name, lc.needle) {
				m.bump(lc.col)
			}
		}
	}
}

func isFnKind(c int16) bool {
	return c == cArrowFunction || c == cFunctionExpression || c == cFunctionExprKind
}

func isAlphaRune(r rune) bool {
	return (r >= 'a' && r <= 'z') || (r >= 'A' && r <= 'Z') || r > 127
}

func firstRune(s string) rune {
	for _, r := range s {
		return r
	}
	return 0
}

const secretMinLen = 12

func (e *extractor) onString(t *Tree, s srcFile, node int, m *meas, loopDepth int32) {
	if t.codeAt(node) == cTemplateString {
		return
	}
	val := trimQuotes(cgStrip(t.text(node, s)))

	if charLenAtLeast(val, secretMinLen) && !containsStr(val, " ") && looksLikeSecret(val) {
		m.secrets = append(m.secrets, secretRec{value: cutStr(val, 200),
			line: int32(t.srow(node)) + 1})
	}
}

func charLenAtLeast(s string, n int) bool {
	if len(s) < n {
		return false
	}
	k := 0
	for range s {
		k++
		if k >= n {
			return true
		}
	}
	return k >= n
}

var userInputMembers = map[string]string{
	"query": "query", "body": "body", "headers": "header",
	"cookies": "cookie", "files": "form", "params": "path",
}

var promiseCombiners = map[string]bool{"all": true, "allSettled": true, "race": true}

var listenerAddBases = map[string]bool{
	"addEventListener": true, "addListener": true, "on": true,
	"subscribe": true, "observe": true, "once": true,
}
var listenerRemoveBases = map[string]bool{
	"removeEventListener": true, "removeListener": true, "off": true,
	"unsubscribe": true, "disconnect": true,
}
var timerSetBases = map[string]bool{
	"setTimeout": true, "setInterval": true, "setImmediate": true,
	"requestAnimationFrame": true,
}
var timerClearBases = map[string]bool{
	"clearTimeout": true, "clearInterval": true, "cancelAnimationFrame": true,
}

func (e *extractor) onNode(t *Tree, s srcFile, node int, m *meas, loopDepth int32, nest int) {
	f := t.f()
	line := int32(t.srow(node)) + 1
	inLoop := loopDepth > 0
	switch t.codeAt(node) {
	case cCallExpression:
		fn := t.fieldChild(node, f.function)
		if fn < 0 {
			return
		}
		name := t.text(fn, s)
		b := afterLastDot(name)
		op := ""
		if name == "JSON.parse" {
			m.bump(mNJsonParse)
		} else if promiseCombiners[b] && containsStr(name, "Promise") {
			m.bump(mNPromiseAll)
			if inLoop {
				m.bump(mNPromiseAllInLoop)
			}
		} else if b == "then" {
			m.bump(mNThenChain)
		} else if listenerAddBases[b] {
			m.bump(mNListenerAdd)
			op = "add"
		} else if listenerRemoveBases[b] {
			m.bump(mNListenerRemove)
			op = "remove"
		} else if timerSetBases[b] {
			m.bump(mNTimerSet)
		} else if timerClearBases[b] {
			m.bump(mNTimerClear)
		}

		if b == "then" || b == "catch" || b == "finally" {
			p := t.parent(node)
			if p >= 0 && t.codeAt(p) == cExpressionStatement {
				m.bump(mNFloatingPromise)
			}
		}
		if op != "" {
			ev := ""
			lisAsync := false
			if args := t.fieldChild(node, f.arguments); args >= 0 && t.namedCount(args) > 0 {
				fst := t.namedChild(args, 0)
				ev = cutStr(trimQuotes(cgStrip(t.text(fst, s))), 60)
				for c := t.firstChild(args); c >= 0; c = t.nextSibling(c) {
					if t.cols.named[c] == 0 {
						continue
					}
					if isFnKind(t.codeAt(c)) && t.start(c)+5 <= len(s.data) &&
						string(s.data[t.start(c):t.start(c)+5]) == "async" {
						lisAsync = true
						break
					}
				}
			}
			m.extras = append(m.extras, extraRow{

				kind: xListener, target: cutStr(beforeLastDot(name), 80), op: op,
				second: ev, flag: lisAsync, inLoop: inLoop, line: line,
			})
		}
	case cMemberExpression:
		prop := t.memberField(node, f.property)
		if prop < 0 {
			return
		}
		p := t.text(prop, s)
		if p == "innerHTML" || p == "outerHTML" {
			m.bump(mNInnerhtml)
		} else if p == "__proto__" || p == "constructor" || p == "prototype" {
			m.bump(mNProtoWrite)
		}
		obj := t.fieldChild(node, f.object)
		if obj < 0 {
			return
		}
		kind, ok := userInputMembers[p]
		if !ok {
			return
		}
		baseObj := t.text(obj, s)
		if baseObj != "req" && baseObj != "request" {
			return
		}
		v := t.textN(node, s, 120)
		if par := t.parent(node); par >= 0 && t.codeAt(par) == cMemberExpression {
			v = t.textN(par, s, 120)
		}
		m.extras = append(m.extras, extraRow{
			kind: xInput, name: v, second: kind, inLoop: inLoop, line: line,
		})
	case cBinaryExpression:
		opn := t.fieldChild(node, f.operator)
		o := ""
		if opn >= 0 {
			o = t.text(opn, s)
		}
		switch o {
		case "&&", "||", "??":
			m.bump(mNLogical)
			m.cyclomatic++
		case "==", "!=", "===", "!==", "<", ">", "<=", ">=":
			m.bump(mNCmp)
		case "&", "|", "^":
			m.bump(mNBitop)
		case "<<", ">>", ">>>":
			m.bump(mNShift)
		case "+", "-", "*", "/", "%", "**":
			m.bump(mNArith)
		}
	case cAsExpression:
		if hasAnyTail(t.text(node, s)) {
			m.bump(mNAsAny)
		}
	case cAssignmentExpression:
		left := t.fieldChild(node, f.left)
		if left < 0 || t.codeAt(left) != cMemberExpression {
			return
		}
		ob := t.fieldChild(left, f.object)
		pr := t.fieldChild(left, f.property)
		if ob < 0 || pr < 0 {
			return
		}
		ot, pt := t.text(ob, s), t.text(pr, s)
		if (ot == "location" && pt == "href") || (ot == "window" && pt == "location") {
			m.bump(mNRedirect)
		}
	case cTemplateSubstitution:
		m.bump(mNTemplateSub)
	case cAwaitExpression:
		if inLoop {
			m.bump(mAwaitInLoop)
		}
		if k0 := t.namedChild(node, 0); k0 >= 0 && t.codeAt(k0) == cCallExpression {
			if callee := t.fieldChild(k0, f.function); callee >= 0 {
				nm := cgStrip(t.text(callee, s))
				if nm != "" {
					m.extras = append(m.extras, extraRow{
						kind: xAwait, name: cutStr(nm, 160),
						second: cutStr(afterLastDot(nm), 120), line: line,
					})
				}
			}
		}
	case cThis:
		m.bump(mNThisRefs)
	case cSubscriptExpression:
		idx := t.fieldChild(node, f.index)
		if idx >= 0 {
			if c := t.codeAt(idx); c != cNumber && c != cString {
				m.bump(mNComputedMember)
			}
		}
	case cUnionType:
		m.bumpN(mNUnionMembers, int32(maxI32(0, int32(t.namedCount(node))-1)))
	case cComment:
		txt := t.text(node, s)
		if g, ok := matchSuppress(txt); ok {
			m.bump(mNSuppressions)

			if containsStr(g.group, "ts-ignore") {
				m.bump(mNTsIgnore)
			} else if containsStr(g.group, "ts-expect-error") {
				m.bump(mNTsExpectError)
			} else if containsStr(g.group, "eslint-disable") {
				m.bump(mNEslintDisable)
			}
		}
	case cRegex:
		if isRedosShape(t.text(node, s)) {
			m.bump(mNRegexRedos)
		}
	}
}

func beforeLastDot(s string) string {
	for i := len(s) - 1; i >= 0; i-- {
		if s[i] == '.' {
			return s[:i]
		}
	}
	return s
}

func lowerStr(s string) string {
	b := []byte(s)
	for i, c := range b {
		if c >= 'A' && c <= 'Z' {
			b[i] = c + 32
		}
	}
	return string(b)
}

func indexStr(s, sub string) int { return strings.Index(s, sub) }

type tframe struct {
	i, c int32
}

type fileOut struct {
	base  int32
	syms  []Symbol
	mvals []int32

	params      []Param
	fields      []Field
	literals    []Literal
	attributes  []AttrRow
	markers     []Marker
	imports     []Import
	hazards     []Hazard
	enumMembers []EnumMember
	typeDefs    []TypeDef
	listeners   []Listener
	inputSites  []InputSite
	secrets     []Secret
	awaited     []AwaitRow
	tsExports   []TSExport
	suppress    []Suppression

	pend pending

	nameRefs   []nameRef
	qualRefs   []qualRef
	importRefs []importRef

	nErrors  int32
	nMissing int32
	hasError bool
	langDecl bool

	scan scanOut

	tree *tsTree
	slab *cgSlab
}

type scanOut struct {
	sha                string
	lines, code        int32
	blank, comment     int32
	maxLen             int32
	isGen              bool
	parsed             bool
	tooBigLong, denied bool
}

type nameRef struct {
	name     string
	local    int32
	fid, mid int32
	typeName string
}

type qualRef struct {
	qual  string
	local int32
}

type importRef struct {
	name string
	bare bool
}

func (f *fileOut) reset() {
	f.base = 0
	f.syms = f.syms[:0]
	f.mvals = f.mvals[:0]
	f.params = f.params[:0]
	f.fields = f.fields[:0]
	f.literals = f.literals[:0]
	f.attributes = f.attributes[:0]
	f.markers = f.markers[:0]
	f.imports = f.imports[:0]
	f.hazards = f.hazards[:0]
	f.enumMembers = f.enumMembers[:0]
	f.typeDefs = f.typeDefs[:0]
	f.listeners = f.listeners[:0]
	f.inputSites = f.inputSites[:0]
	f.secrets = f.secrets[:0]
	f.awaited = f.awaited[:0]
	f.tsExports = f.tsExports[:0]
	f.suppress = f.suppress[:0]
	f.pend.Sid = f.pend.Sid[:0]
	f.pend.Fid = f.pend.Fid[:0]
	f.pend.Line = f.pend.Line[:0]
	f.pend.Name = f.pend.Name[:0]
	f.pend.Type = f.pend.Type[:0]
	f.nameRefs = f.nameRefs[:0]
	f.qualRefs = f.qualRefs[:0]
	f.importRefs = f.importRefs[:0]
	f.nErrors, f.nMissing, f.hasError, f.langDecl = 0, 0, false, false
	f.tree = nil
}

func (o *fileOut) reb(r cgStr) cgStr { return o.slab.reb(r) }

type scope struct {
	symID    int32
	qualPre  string
	typeName string
	typeID   int32
}

type extractor struct {
	slab   cgSlab
	m      *meas
	nameC  map[int32]string
	expC   map[int32]bool
	sink   *fileOut
	src    srcFile
	tree   *Tree
	fid    int32
	mid    int32
	rel    string
	pend   *pending
	frames []frame
	tstack []tframe
	kids   []int
}

func newExtractor() *extractor {
	return &extractor{
		m:     newMeas(),
		nameC: map[int32]string{},
		expC:  map[int32]bool{},
	}
}

func (e *extractor) intern(s string) string {
	return s
}

func (e *extractor) run(pf *pendingFile, out *fileOut, ft *tsTree) {
	e.sink = out
	out.slab = &e.slab
	e.fid = pf.fid
	e.mid = pf.moduleID
	e.rel = pf.rel
	useTSX := hasSuffix(pf.rel, ".tsx")
	e.tree = buildTree(ft, useTSX)
	for k := range e.nameC {
		delete(e.nameC, k)
	}
	for k := range e.expC {
		delete(e.expC, k)
	}
	e.pend = &out.pend
	runFile(e, pf)
}

func (e *extractor) noteImport(name, source string) {
	if name == "" {
		return
	}
	bare := !hasPrefix(source, ".") && !hasPrefix(source, "/")
	e.sink.importRefs = append(e.sink.importRefs, importRef{name: cgStrip(name), bare: bare})
}

func (e *extractor) parseImports(t *Tree, s srcFile, pf *pendingFile, o *fileOut) {
	f := t.f()
	for i := 0; i < t.len(); i++ {
		switch t.codeAt(i) {
		case cImportStatement:
			srcn := t.fieldChild(i, f.source)
			target := ""
			if srcn >= 0 {
				target = trimQuotes(t.text(srcn, s))
			}
			txt := t.text(i, s)
			nNames := e.importSpecifiers(t, s, i, target)
			typeOnly := hasPrefix(cgLStrip(txt), "import type") || containsStr(txt, "{ type ")
			o.imports = append(o.imports, Import{
				FileID: pf.fid, target: e.slab.put(cutStr(target, 300)), TargetID: -1,
				kind: e.slab.put("import"), Line: int32(t.srow(i)) + 1,
				IsExternal: !hasPrefix(target, "."), IsRelative: hasPrefix(target, "."),
				IsWildcard: containsStr(txt, "* as"), IsTypeOnly: typeOnly,
				NNames: nNames,
			})
		case cExportStatement:
			txt := t.text(i, s)
			srcn := t.fieldChild(i, f.source)
			hasSrc := srcn >= 0
			source := ""
			if hasSrc {
				source = trimQuotes(t.text(srcn, s))
			}
			isStar := containsStr(beforeFrom(txt), "*")
			isDefault := containsStr(cutStr(txt, 24), "default")

			decl := -1
			for c := t.firstChild(i); c >= 0; c = t.nextSibling(c) {
				if t.cols.named[c] == 0 {
					continue
				}
				switch t.codeAt(c) {
				case cInterfaceDeclaration, cTypeAliasDeclaration, cEnumDeclaration,
					cClassDeclaration, cFunctionDeclaration, cLexicalDeclaration:
					decl = c
				}
				if decl >= 0 {
					break
				}
			}
			typeOnly := hasPrefix(cgLStrip(txt), "export type") ||
				(decl >= 0 && (t.codeAt(decl) == cInterfaceDeclaration ||
					t.codeAt(decl) == cTypeAliasDeclaration))
			if hasSrc {
				o.imports = append(o.imports, Import{
					FileID: pf.fid, target: e.slab.put(cutStr(source, 300)), TargetID: -1,
					kind: e.slab.put("reexport"), Line: int32(t.srow(i)) + 1,
					IsExternal: !hasPrefix(source, "."), IsRelative: hasPrefix(source, "."),
					IsWildcard: isStar, IsTypeOnly: typeOnly, NNames: 1,
				})
			}
			var names []string
			collectSubtrees(t, i, cExportSpecifier, func(n int) {
				names = append(names, t.text(n, s))
			})
			if len(names) == 0 {
				nm := ""
				if decl >= 0 {
					nm = e.nodeName(t, s, decl)
				}
				names = []string{nm}
			}
			if names[0] == "" {
				nm := ""
				if decl >= 0 {
					nm = e.nodeName(t, s, decl)
				} else {
					nm = e.nodeName(t, s, i)
				}
				if nm == "" {
					if isDefault {
						nm = "default"
					} else {
						nm = "*"
					}
				}
				names = []string{nm}
			}
			kind := "named"
			if isStar {
				kind = "star"
			} else if isDefault {
				kind = "default"
			}
			if len(names) > 40 {
				names = names[:40]
			}
			for _, nm := range names {
				o.tsExports = append(o.tsExports, TSExport{
					FileID: pf.fid, name: e.slab.put(cutStr(cgStrip(nm), 120)),
					kind: e.slab.put(kind), Line: int32(t.srow(i)) + 1,
					IsDefault: isDefault, IsReexport: hasSrc, IsStar: isStar,
					IsTypeOnly: typeOnly, source: e.slab.put(source), HasSource: hasSrc,
				})
			}
		}
	}
}

func (e *extractor) importSpecifiers(t *Tree, s srcFile, node int, target string) int32 {
	f := t.f()
	var names []int
	collectSubtrees(t, node, cImportSpecifier, func(n int) { names = append(names, n) })
	for _, n := range names {
		got := t.fieldChild(n, f.alias)
		if got < 0 {
			got = t.fieldChild(n, f.name)
		}
		if got >= 0 {
			e.noteImport(t.text(got, s), target)
		}
	}
	clause := t.fieldChild(node, f.importClause)
	if clause < 0 {

		for c := t.firstChild(node); c >= 0; c = t.nextSibling(c) {
			if t.codeAt(c) == cImportClause {
				clause = c
				break
			}
		}
	}
	if clause >= 0 {
		for c := t.firstChild(clause); c >= 0; c = t.nextSibling(c) {
			if t.cols.named[c] == 0 {
				continue
			}
			switch t.codeAt(c) {
			case cIdentifier:
				e.noteImport(t.text(c, s), target)
			case cNamespaceImport:
				for k := t.firstChild(c); k >= 0; k = t.nextSibling(k) {
					if t.codeAt(k) == cIdentifier {
						e.noteImport(t.text(k, s), target)
					}
				}
			}
		}
	}
	if len(names) < 1 {
		return 1
	}
	return int32(len(names))
}

func collectSubtrees(t *Tree, root int, want int16, fn func(int)) {
	var kids []int
	stack := make([]int, 0, 64)

	for c := t.firstChild(root); c >= 0; c = t.nextSibling(c) {
		kids = append(kids, c)
	}
	for _, kid := range slices.Backward(kids) {
		stack = append(stack, kid)
	}
	kids = kids[:0]
	for len(stack) > 0 {
		n := stack[len(stack)-1]
		stack = stack[:len(stack)-1]
		if t.codeAt(n) == want {
			fn(n)
		}

		kids = kids[:0]
		for c := t.firstChild(n); c >= 0; c = t.nextSibling(c) {
			kids = append(kids, c)
		}
		for _, kid := range slices.Backward(kids) {
			stack = append(stack, kid)
		}
	}
}

func beforeFrom(s string) string {
	if before, _, ok := strings.Cut(s, "from"); ok {
		return before
	}
	return s
}

var strictFlags = []string{
	"strict", "noImplicitAny", "strictNullChecks", "strictFunctionTypes",
	"strictBindCallApply", "strictPropertyInitialization", "noImplicitThis",
	"useUnknownInCatchVariables", "alwaysStrict", "noUncheckedIndexedAccess",
	"exactOptionalPropertyTypes", "noImplicitOverride", "noImplicitReturns",
	"noFallthroughCasesInSwitch", "verbatimModuleSyntax", "isolatedModules",
	"erasableSyntaxOnly",
}

var removedByTS7 = [][2]string{
	{"baseUrl", "baseUrl (removed in TS 7 -- use relative paths)"},
	{"downlevelIteration", "downlevelIteration (removed in TS 7)"},
	{"importsNotUsedAsValues", "importsNotUsedAsValues (removed)"},
	{"preserveValueImports", "preserveValueImports (removed)"},
	{"suppressImplicitAnyIndexErrors", "suppressImplicitAnyIndexErrors"},
}

func parseManifests(g *Graph, root string) {

	var walk func(dir string)
	walk = func(dir string) {
		f, err := os.Open(dir)
		if err != nil {
			return
		}
		names, err := f.Readdirnames(-1)
		f.Close()
		if err != nil {
			return
		}
		var subs []string
		hasPkg := false
		for _, n := range names {
			st, err := os.Lstat(filepath.Join(dir, n))
			if err != nil {
				continue
			}
			if st.IsDir() {
				if n == "node_modules" || n == ".git" || n == "dist" || n == "out" {
					continue
				}
				subs = append(subs, n)
			} else {
				if strings.HasPrefix(n, "tsconfig") && strings.HasSuffix(n, ".json") {
					g.readTSConfig(g, root, dir, n)
				}
				if n == "package.json" {
					hasPkg = true
				}
			}
		}
		if hasPkg {
			g.readPackageJSON(g, root, dir)
		}
		for _, s := range subs {
			walk(filepath.Join(dir, s))
		}
	}
	walk(root)
}

func (g *Graph) readTSConfig(g2 *Graph, root, dir, name string) {
	raw, err := os.ReadFile(filepath.Join(dir, name))
	if err != nil {
		return
	}
	cfg := loadJSONC(raw)
	if cfg == nil {
		return
	}
	co, _ := cfg["compilerOptions"].(map[string]any)
	if co == nil {
		co = map[string]any{}
	}
	rel, _ := filepath.Rel(root, dir)
	rel = filepath.ToSlash(rel)
	if rel == "" {
		rel = "."
	}
	relFile, _ := filepath.Rel(root, filepath.Join(dir, name))
	relFile = filepath.ToSlash(relFile)
	mr := strOf(co["moduleResolution"])
	mod := strOf(co["module"])
	var removed []string
	for _, kv := range removedByTS7 {
		if _, ok := co[kv[0]]; ok {
			removed = append(removed, kv[1])
		}
	}
	switch lowerStr(mr) {
	case "classic", "node", "node10":
		removed = append(removed, "moduleResolution: "+mr+" (removed in TS 7)")
	}
	switch lowerStr(mod) {
	case "amd", "umd", "system", "none":
		removed = append(removed, "module: "+mod+" (removed in TS 7)")
	}
	if lowerStr(strOf(co["target"])) == "es5" {
		removed = append(removed, "target: es5 (removed in TS 7)")
	}
	var pathsJSON string
	if p, ok := co["paths"].(map[string]any); ok && len(p) > 0 {
		pathsJSON = cutStr(cgJSONDumps(p), 2000)
	}
	nStrict := int32(0)
	for _, f := range strictFlags {
		if v, ok := co[f].(bool); ok && v {
			nStrict++
		}
	}
	strict, _ := co["strict"].(bool)
	noAny, hasNoAny := co["noImplicitAny"].(bool)
	if !hasNoAny {
		noAny = strict
	}
	snc, hasSnc := co["strictNullChecks"].(bool)
	if !hasSnc {
		snc = strict
	}
	nuia, _ := co["noUncheckedIndexedAccess"].(bool)
	eo, _ := co["exactOptionalPropertyTypes"].(bool)
	vms, _ := co["verbatimModuleSyntax"].(bool)
	im, _ := co["isolatedModules"].(bool)
	eso, _ := co["erasableSyntaxOnly"].(bool)
	ext, hasExt := cfg["extends"]
	base, hasBase := co["baseUrl"]
	g2.TSConfigs = append(g2.TSConfigs, TSConfig{
		path: cgPut(relFile), dir: cgPut(rel),
		extends: cgPut(strOf(ext)), HasExtends: hasExt,
		Strict: strict, NoImplAny: noAny, NullChecks: snc, UncheckedIx: nuia,
		ExactOpt: eo, Verbatim: vms, Isolated: im, Erasable: eso, NStrict: nStrict,
		target: cgPut(strOf(co["target"])), module: cgPut(mod), resolution: cgPut(mr),
		removed: cgPut(strings.Join(removed, "; ")), HasRemoved: len(removed) > 0,
		baseURL: cgPut(strOf(base)), HasBaseURL: hasBase, pathsJSON: cgPut(pathsJSON),
		HasPaths: pathsJSON != "",
	})
}

func (g *Graph) readPackageJSON(g2 *Graph, root, dir string) {
	raw, err := os.ReadFile(filepath.Join(dir, "package.json"))
	if err != nil {
		return
	}
	var cfg map[string]json.RawMessage
	if err := json.Unmarshal(raw, &cfg); err != nil {
		return
	}
	rel, _ := filepath.Rel(root, dir)
	rel = filepath.ToSlash(rel)
	if rel == "" {
		rel = "."
	}

	for _, sect := range []struct {
		name  string
		isDev bool
	}{{"dependencies", false}, {"devDependencies", true}} {
		body, ok := cfg[sect.name]
		if !ok {
			continue
		}
		var keys []string
		var vals []json.RawMessage
		if !jsonObjectOrder(body, &keys, &vals) {
			continue
		}
		for i, k := range keys {
			g2.Deps = append(g2.Deps, DepRow{
				name: cgPut(cutStr(k, 120)), version: cgPut(cutStr(cgStrOfJSON(vals[i]), 40)),
				IsDev: sect.isDev, dir: cgPut(rel),
			})
		}
	}
}

func jsonObjectOrder(body []byte, keys *[]string, vals *[]json.RawMessage) bool {
	dec := json.NewDecoder(bytes.NewReader(body))
	tok, err := dec.Token()
	if err != nil {
		return false
	}
	if d, ok := tok.(json.Delim); !ok || d != '{' {
		return false
	}
	for dec.More() {
		kt, err := dec.Token()
		if err != nil {
			return false
		}
		k, ok := kt.(string)
		if !ok {
			return false
		}
		var v json.RawMessage
		if err := dec.Decode(&v); err != nil {
			return false
		}
		*keys = append(*keys, k)
		*vals = append(*vals, v)
	}
	return true
}

func cgStrOfJSON(raw json.RawMessage) string {
	if len(raw) == 0 {
		return ""
	}
	if raw[0] == '"' {
		var s string
		if json.Unmarshal(raw, &s) == nil {
			return s
		}
		return ""
	}
	dec := json.NewDecoder(bytes.NewReader(raw))
	dec.UseNumber()
	var v any
	if dec.Decode(&v) != nil {
		return ""
	}
	return cgRepr(v)
}

func strOf(v any) string {
	if v == nil {
		return ""
	}
	if s, ok := v.(string); ok {
		return s
	}
	return ""
}

func attachSuppressionSymbols(g *Graph) {
	byFile := make(map[int32][]int32, 256)
	for i := range g.Symbols {
		s := &g.Symbols[i]
		switch s.Kind {
		case kFunction, kMethod, kClosure:
			byFile[s.FileID] = append(byFile[s.FileID], int32(i+1))
		}
	}
	for f := range byFile {
		ids := byFile[f]

		sort.SliceStable(ids, func(a, b int) bool {
			sa, sb := &g.Symbols[ids[a]-1], &g.Symbols[ids[b]-1]
			if sa.LineStart != sb.LineStart {
				return sa.LineStart > sb.LineStart
			}
			return ids[a] < ids[b]
		})
	}
	for i := range g.Suppress {
		u := &g.Suppress[i]
		for _, sid := range byFile[u.FileID] {
			s := &g.Symbols[sid-1]
			if u.Line >= s.LineStart && u.Line <= s.LineEnd {
				u.SymID = sid
				break
			}
		}
	}
}

func buildSigTokens(g *Graph) {
	seen := make(map[uint64]struct{}, 1024)
	for i := range g.Symbols {
		sig := g.Symbols[i].Sig()
		if sig == "" {
			continue
		}
		if len(sig) > 4000 {
			sig = sig[:4000]
		}
		sid := int32(i + 1)
		forEachSigToken(sig, func(tok string) {
			k := pair(sid, tokKey(tok))
			if _, ok := seen[k]; ok {
				return
			}
			seen[k] = struct{}{}
			g.SigTokens = append(g.SigTokens, SigToken{SymID: sid, token: cgPut(tok)})
		})
	}
}

var importSuffixes = []string{
	"", ".py", ".pyi", ".ts", ".tsx", ".d.ts", ".mts", ".cts",
	".js", ".jsx", ".mjs", ".cjs", ".rb", ".php", ".go", ".rs", ".java",
}

var importIndexes = []string{
	"__init__.py", "index.ts", "index.tsx", "index.js", "index.mjs",
	"mod.rs", "lib.rs",
}

func resolveImportTargets(g *Graph) {
	byPath := make(map[string]int32, len(g.Files)*2)
	for i := range g.Files {
		norm := g.Files[i].Path()
		byPath[norm] = int32(i + 1)
		stem := norm
		if k := strings.LastIndexByte(norm, '.'); k > 0 {
			stem = norm[:k]
		}
		if _, ok := byPath[stem]; !ok {
			byPath[stem] = int32(i + 1)
		}
	}
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
	dirOf := func(p string) string {
		if k := strings.LastIndexByte(p, '/'); k >= 0 {
			return p[:k]
		}
		return ""
	}
	n := 0
	for i := range g.Imports {
		im := &g.Imports[i]
		if im.TargetID >= 0 {
			continue
		}
		target := im.Target()
		if target == "" {
			continue
		}
		here := dirOf(g.Files[im.FileID-1].Path())
		var hit int32
		if hasPrefix(target, ".") {
			nUp := 0
			for nUp < len(target) && target[nUp] == '.' {
				nUp++
			}
			rest := target[nUp:]
			if !strings.Contains(target, "/") {
				rest = strings.ReplaceAll(rest, ".", "/")
			} else {
				rest = strings.TrimLeft(target, "./")
			}
			base := here
			for k := 0; k < nUp-1; k++ {
				base = dirOf(base)
			}
			if base != "" {
				hit = look(base + "/" + rest)
			} else {
				hit = look(rest)
			}
		} else {
			hit = look(strings.ReplaceAll(target, ".", "/"))
			if hit == 0 {
				hit = look(here + "/" + target)
			}
		}
		if hit != 0 && hit != im.FileID {
			im.TargetID = hit
			n++
		}
	}
	g.setMeta("imports_resolved", itoa(n)+" of "+itoa(len(g.Imports))+
		" import rows point at a file in this tree")
}

func loadJSONC(raw []byte) map[string]any {
	var v map[string]any
	if json.Unmarshal(raw, &v) == nil {
		return v
	}
	text := stripJSONC(string(raw))
	if json.Unmarshal([]byte(text), &v) == nil {
		return v
	}
	return nil
}

func stripJSONC(raw string) string {
	out := make([]byte, 0, len(raw))
	inStr := false
	for i := 0; i < len(raw); {
		c := raw[i]
		if inStr {
			out = append(out, c)
			if c == '\\' && i+1 < len(raw) {
				out = append(out, raw[i+1])
				i += 2
				continue
			}
			if c == '"' {
				inStr = false
			}
			i++
			continue
		}
		if c == '"' {
			inStr = true
			out = append(out, c)
			i++
			continue
		}
		if c == '/' && i+1 < len(raw) && raw[i+1] == '/' {
			for i < len(raw) && raw[i] != '\n' {
				i++
			}
			continue
		}
		if c == '/' && i+1 < len(raw) && raw[i+1] == '*' {
			i += 2
			for i+1 < len(raw) && !(raw[i] == '*' && raw[i+1] == '/') {
				i++
			}
			i += 2
			continue
		}
		out = append(out, c)
		i++
	}
	return dropTrailingCommas(string(out))
}

func dropTrailingCommas(s string) string {
	b := []byte(s)
	w := 0
	inStr := false
	for i := 0; i < len(b); i++ {
		c := b[i]
		if inStr {
			if c == '\\' && i+1 < len(b) {
				b[w] = c
				w++
				i++
				c = b[i]
				b[w] = c
				w++
				continue
			}
			if c == '"' {
				inStr = false
			}
			b[w] = c
			w++
			continue
		}
		if c == '"' {
			inStr = true
			b[w] = c
			w++
			continue
		}
		if c == ',' {
			j := i + 1
			for j < len(b) && (b[j] == ' ' || b[j] == '\t' || b[j] == '\n' || b[j] == '\r') {
				j++
			}
			if j < len(b) && (b[j] == '}' || b[j] == ']') {
				continue
			}
		}
		b[w] = c
		w++
	}
	return string(b[:w])
}

func materialize(g *Graph) {
	n := int32(len(g.Symbols))

	fanOut := make([]int32, n+1)
	fanIn := make([]int32, n+1)
	for i := range g.Edges {
		e := &g.Edges[i]
		if e.Self {
			continue
		}
		fanOut[e.Caller]++
		fanIn[e.Callee]++
	}

	callsites := make([]int32, n+1)
	for i := range g.Callsites {
		callsites[g.Callsites[i].Callee]++
	}

	catTot := make([][]int32, len(storedHazCols))
	for i := range catTot {
		catTot[i] = make([]int32, n+1)
	}
	catIdx := map[string]int{}
	for i, c := range storedHazCols {
		catIdx[c] = i
	}
	hazTot := make([]int32, n+1)
	for i := range g.Hazards {
		h := &g.Hazards[i]
		if ci, ok := catIdx[h.Category()]; ok {
			catTot[ci][h.SymID] += h.N
		}
		hazTot[h.SymID] += h.N
	}

	unres := make([]int32, n+1)
	for i := range g.Unresolved {
		unres[g.Unresolved[i].Caller] += g.Unresolved[i].N
	}

	uniq := make([]int32, n+1)
	uniqCnt := make([]int32, n+1)
	hasUni := make([]bool, n+1)
	for i := range g.Edges {
		e := &g.Edges[i]
		uniq[e.Caller]++
		hasUni[e.Caller] = true
		if e.Self {
			uniqCnt[e.Caller] = 1
		}
	}

	supp := make([]int32, n+1)
	hasSupp := make([]bool, n+1)
	for i := range g.Suppress {
		if g.Suppress[i].SymID > 0 {
			supp[g.Suppress[i].SymID]++
			hasSupp[g.Suppress[i].SymID] = true
		}
	}

	la := make([]int32, n+1)
	lr := make([]int32, n+1)
	hasLis := make([]bool, n+1)
	for i := range g.Listeners {
		l := &g.Listeners[i]
		hasLis[l.SymID] = true
		if l.Op() == "add" {
			la[l.SymID]++
		} else if l.Op() == "remove" {
			lr[l.SymID]++
		}
	}

	extByCaller := g.extByCaller
	for i := int32(1); i <= n; i++ {
		m := g.metrics(i)
		m[mFanOut] = fanOut[i]
		m[mFanIn] = fanIn[i]
		m[mNCallsites] = callsites[i]
		if uniqCnt[i] != 0 {
			m[mIsRecursive] = 1
		}
		m[mNUnresolvedCalls] = unres[i]
		m[mNUniqueCalls] = uniq[i]
		for c := range len(storedHazCols) {
			m[mCat0+c] = catTot[c][i]
		}
		if v, ok := extByCaller[i]; ok {
			m[mNExternalCalls] = v
		}
		m[mNHazards] = hazTot[i]
		m[mIsLeaf] = b2i(fanOut[i] == 0)
		m[mIsRoot] = b2i(fanIn[i] == 0)
	}
	for i := int32(1); i <= n; i++ {
		m := g.metrics(i)
		if hasSupp[i] {
			m[mNSuppressions] = supp[i]
		}
		if hasLis[i] {
			m[mNListenerAdd] = la[i]
			m[mNListenerRemove] = lr[i]
		}
	}

	fsym := make([]int32, len(g.Files)+1)
	ffn := make([]int32, len(g.Files)+1)
	fty := make([]int32, len(g.Files)+1)
	fcyc := make([]int32, len(g.Files)+1)
	fmax := make([]int32, len(g.Files)+1)
	for i := range g.Symbols {
		s := &g.Symbols[i]
		m := g.metrics(int32(i + 1))
		f := s.FileID
		fsym[f]++
		switch s.Kind {
		case kFunction, kMethod, kClosure:
			ffn[f]++
		case kClass, kInterface, kType, kEnum:
			fty[f]++
		}
		fcyc[f] += m[mCyclomatic]
		if m[mCyclomatic] > fmax[f] {
			fmax[f] = m[mCyclomatic]
		}
	}
	fimp := make([]int32, len(g.Files)+1)
	for i := range g.Imports {
		fimp[g.Imports[i].FileID]++
	}
	for i := range g.Files {
		if fsym[g.Files[i].ModuleID] == 0 {

		}
		f := &g.Files[i]
		f.NSymbols = fsym[i+1]
		f.NFuncs = ffn[i+1]
		f.NTypes = fty[i+1]
		f.TotalCyc = fcyc[i+1]
		f.MaxCyc = fmax[i+1]
		f.NImports = fimp[i+1]
	}

	modSym := make([]int32, len(g.Modules)+1)
	modPub := make([]int32, len(g.Modules)+1)
	for i := range g.Symbols {
		s := &g.Symbols[i]
		m := g.metrics(int32(i + 1))
		modSym[s.ModuleID]++
		modPub[s.ModuleID] += m[mIsPublic]
	}
	modFiles := make([]int32, len(g.Modules)+1)
	modSloc := make([]int32, len(g.Modules)+1)
	for i := range g.Files {
		modFiles[g.Files[i].ModuleID]++
		modSloc[g.Files[i].ModuleID] += g.Files[i].Sloc
	}

	outSet := make([]map[int32]bool, len(g.Modules)+1)
	inSet := make([]map[int32]bool, len(g.Modules)+1)
	for i := range g.Edges {
		e := &g.Edges[i]
		c1 := &g.Symbols[e.Caller-1]
		c2 := &g.Symbols[e.Callee-1]
		if c1.ModuleID == c2.ModuleID {
			continue
		}
		if outSet[c1.ModuleID] == nil {
			outSet[c1.ModuleID] = map[int32]bool{}
		}
		outSet[c1.ModuleID][c2.ModuleID] = true
		if inSet[c2.ModuleID] == nil {
			inSet[c2.ModuleID] = map[int32]bool{}
		}
		inSet[c2.ModuleID][c1.ModuleID] = true
	}
	for i := range g.Modules {
		md := &g.Modules[i]
		id := int32(i + 1)
		md.NSymbols = modSym[id]
		md.NPublic = modPub[id]
		md.NFiles = modFiles[id]
		md.Sloc = modSloc[id]
		md.FanOut = int32(len(outSet[id]))
		md.FanIn = int32(len(inSet[id]))
		if md.FanIn+md.FanOut == 0 {
			md.Instability = 0.0
		} else {
			md.Instability = float64(md.FanOut) / float64(md.FanIn+md.FanOut)
		}
	}

	for i := int32(1); i <= n; i++ {
		m := g.metrics(i)
		if m[mNTokens] > 0 {
			dist := m[mNDistinctOperators] + m[mNDistinctOperands]
			df := 2.0
			if dist > 1 {
				df = float64(dist)
			}
			m[mHalsteadVolume] = int32(truncInt(float64(m[mNOperators]+m[mNOperands]) * df))
		}
		r := m[mCyclomatic]*2 + m[mCognitive] + m[mMaxNesting]*4 +
			m[mNAnyTotal]*3 + m[mReturnsAny]*10 + m[mNAsAny]*8 +
			m[mNNonNull]*2 + m[mNTsIgnore]*12 + m[mNTsExpectError]*4 +
			m[hazardMetric("exec")]*30 + m[hazardMetric("proto_pollution")]*20 +
			m[hazardMetric("dom")]*10 + m[hazardMetric("sync_block")]*12 +
			m[mNRegexRedos]*15 + m[hazardMetric("crypto")]*6 +
			m[hazardMetric("reflect")]*3 + m[mAwaitInLoop]*8 +
			m[mNFloatingPromise]*6
		if m[mNListenerAdd] > m[mNListenerRemove] {
			r += 12
		}
		if m[mIsRecursive] != 0 {
			r += 10
		}
		m[mRiskScore] = r
		if k := g.Symbols[i-1].Kind; k == kFunction || k == kMethod || k == kClosure {
			slocF := 0.05
			if m[mSloc] > 1 {
				slocF = float64(m[mSloc]) / 20.0
			}

			mv := max(int32(truncInt(171-fmul(0.23, float64(m[mCyclomatic]))-
				fmul(16.2, slocF))), 0)
			m[mMaintainability] = mv
		}
	}
}

//go:noinline
func fmul(a, b float64) float64 { return a * b }

type meas struct {
	vals    [metricCount]int32
	touched []int32

	cyclomatic         int32
	cognitive          int32
	maxNesting         int32
	maxLoopDepth       int32
	nTokens            int32
	nOperators         int32
	nOperands          int32
	nDistinctOperands  int32
	nDistinctOperators int32

	opSyms  []uint16
	opGen   uint32
	opGenV  []uint32
	operand map[string]uint32
	gen     uint32

	calls   []callRec
	lits    []litRec
	extras  []extraRow
	secrets []secretRec
}

type callRec struct {
	name    string
	line    int32
	dynamic bool
	inLoop  bool
}

type litRec struct {
	value string
	line  int32
}

type secretRec struct {
	value string
	line  int32
}

const (
	xListener = iota
	xInput
	xAwait
)

type extraRow struct {
	kind   int8
	name   string
	second string
	target string
	op     string
	flag   bool
	inLoop bool
	line   int32
}

func newMeas() *meas {
	return &meas{
		operand: make(map[string]uint32, 256),
		opGenV:  make([]uint32, 1<<16),
	}
}

func (m *meas) reset() {
	for _, c := range m.touched {
		m.vals[c] = 0
	}
	m.touched = m.touched[:0]

	m.cyclomatic, m.cognitive = 1, 0
	m.maxNesting, m.maxLoopDepth = 0, 0
	m.nTokens, m.nOperators, m.nOperands = 0, 0, 0
	m.nDistinctOperands, m.nDistinctOperators = 0, 0
	m.opSyms = m.opSyms[:0]
	m.opGen++
	if m.opGen == 0 {
		clear(m.opGenV)
		m.opGen = 1
	}
	if len(m.operand) > 1<<13 {
		m.operand = make(map[string]uint32, 256)
		m.gen = 1
	} else {
		m.gen++
	}
	m.calls = m.calls[:0]
	m.lits = m.lits[:0]
	m.extras = m.extras[:0]
	m.secrets = m.secrets[:0]
}

func (m *meas) bump(c int16) {
	if c < 0 {
		return
	}
	i := int(c)
	if m.vals[i] == 0 {
		m.touched = append(m.touched, int32(i))
	}
	m.vals[i]++
}

func (m *meas) bumpN(c int16, n int32) {
	if c < 0 || n == 0 {
		return
	}
	i := int(c)
	if m.vals[i] == 0 {
		m.touched = append(m.touched, int32(i))
	}
	m.vals[i] += n
}

func (m *meas) setv(c int, v int32) {
	if m.vals[c] == 0 {
		m.touched = append(m.touched, int32(c))
	}
	m.vals[c] = v
}

func (m *meas) addOperand(s string) {
	if m.operand[s] != m.gen {
		m.operand[s] = m.gen
		m.nDistinctOperands++
	}
}

func (m *meas) addOperator(sym uint16) {
	if m.opGenV[sym] != m.opGen {
		m.opGenV[sym] = m.opGen
		m.nDistinctOperators++
	}
}

func (e *extractor) measureBody(t *Tree, s srcFile, body int, prune bool) {
	m := e.m
	m.reset()
	d := t.lang.disp
	f := t.f()
	var nestStack, loopStack [256]int32
	ns, ls := 0, 0
	var loopDepth, depth int32

	i := body
	for {
		sym := t.cols.sym[i]
		c := d.symCode[sym]

		for ns > 0 && nestStack[ns-1] >= depth {
			ns--
		}
		for ls > 0 && loopStack[ls-1] >= depth {
			ls--
			if loopDepth > 0 {
				loopDepth--
			}
		}

		named := t.cols.named[i] != 0
		isElif := false
		if c == cIfStatement {
			p := t.parent(i)
			if p >= 0 {
				if d.symCode[t.cols.sym[p]] == cIfStatement {
					isElif = t.fieldChild(p, f.alternative) == i
				} else {
					gp := t.parent(p)
					if gp >= 0 && d.symCode[t.cols.sym[gp]] == cIfStatement {
						if t.fieldChild(gp, f.alternative) == p {
							isElif = t.namedChild(p, 0) == i
						}
					}
				}
			}
		}

		if named && d.isNest[c] && !isElif {
			nestStack[ns] = depth
			ns++
			if int32(ns) > m.maxNesting {
				m.maxNesting = int32(ns)
			}
		}
		if named && d.isLoop[c] {
			loopStack[ls] = depth
			ls++
			loopDepth++
			if loopDepth > m.maxLoopDepth {
				m.maxLoopDepth = loopDepth
			}
			m.cyclomatic++
			if int32(ns) < 1 {
				m.cognitive++
			} else {
				m.cognitive += int32(ns)
			}
			m.bump(mNLoops)
		} else if named && d.isBranch[c] {
			m.cyclomatic++
			if isElif {
				m.cognitive++
			} else if ns < 1 {
				m.cognitive++
			} else {
				m.cognitive += int32(ns)
			}
			if isElif {
				m.bump(mNElif)
			}
			m.bump(mNBranches)
			if loopDepth > 0 {
				m.bump(mBranchInLoop)
			}
		}

		m.bump(d.counter[c])

		if !d.special[c] {
			if t.childCount(i) == 0 {
				m.nTokens++
				m.nOperands++
				m.addOperand(t.textN(i, s, 40))
			}
		} else if d.isCall[c] {
			e.onCall(t, s, i, m, loopDepth)
		} else if d.isOper[c] {
			m.nOperators++
			m.addOperator(sym)
		} else if d.isString[c] {
			m.bump(mNStringLit)
			m.addOperand(t.textN(i, s, 40))
			m.nOperands++
			e.onString(t, s, i, m, loopDepth)
		} else if d.isNumber[c] {
			txt := cgStrip(t.text(i, s))
			m.nOperands++
			m.addOperand(txt)
			if isMagicNumber(txt) {
				m.bump(mNMagic)
				m.lits = append(m.lits, litRec{value: txt, line: int32(t.srow(i)) + 1})
			}
			if indexByteStr(txt, '.') >= 0 || hasExpMarker(txt) {
				m.bump(mNFloatLit)
			}
		} else if d.isComment[c] {
			m.bumpN(mNCommentLines, int32(t.erow(i))-int32(t.srow(i))+1)
		}

		if d.onNode[c] {
			e.onNode(t, s, i, m, loopDepth, ns)
		}

		descend := true
		if prune && isPrunable(d, c) {
			descend = false
		}
		if descend && t.childCount(i) > 0 {
			i = t.firstChild(i)
			depth++
			continue
		}

		for {
			if i == body {
				m.nTokens += m.nOperators
				return
			}
			if ns := t.nextSibling(i); ns >= 0 {
				i = ns
				break
			}
			p := t.parent(i)
			if p < 0 {
				m.nTokens += m.nOperators
				return
			}
			i = p
			depth--
		}
	}
}

func isPrunable(d *disp, c int16) bool {
	return d.funcKind[c] != fkNone || d.typeKind[c] != 0
}

func buildMetricsList() []queryDef {
	return []queryDef{
		{
			Name: "graph-blindspots",
			Run: func(g *Graph, mod string, n int) *table {
				t := &table{cols: []string{"module", "fns", "types", "calls", "external",
					"unresolved", "computed", "pct_blind"}}
				type agg struct {
					fns, types, calls, ext, unres, comp int32
				}
				per := map[int32]*agg{}
				var order []int32
				for i := range g.Symbols {
					s := &g.Symbols[i]
					m := g.metrics(int32(i + 1))
					if !g.modOK(s.ModuleID, mod) {
						continue
					}
					a := per[s.ModuleID]
					if a == nil {
						a = &agg{}
						per[s.ModuleID] = a
						order = append(order, s.ModuleID)
					}
					if g.isCallKind(s.Kind) {
						a.fns++
					}
					switch s.Kind {
					case kType, kInterface, kEnum:
						a.types++
					}
					a.calls += m[mNCalls]
					a.ext += m[mNExternalCalls]
					a.unres += m[mNUnresolvedCalls]
					a.comp += m[mNComputedMember]
				}

				sort.Slice(order, func(x, y int) bool { return order[x] > order[y] })
				for _, mid := range order {
					a := per[mid]
					if a.calls == 0 {
						continue
					}
					t.rows = append(t.rows, []cell{cs(g.moduleName(mid)), ci(int(a.fns)),
						ci(int(a.types)), ci32(a.calls), ci32(a.ext), ci32(a.unres),
						ci32(a.comp), ci(int(100 * a.unres / a.calls))})
				}
				sortRows(t, func(a, b []cell) bool { return num(a[5]) > num(b[5]) })
				return lim(t, n)
			},
		},
		{
			Name: "barrel-blast",
			Run: func(g *Graph, mod string, n int) *table {
				importers := map[int32]int32{}
				for i := range g.Imports {
					if g.Imports[i].TargetID > 0 {
						importers[g.Imports[i].TargetID]++
					}
				}
				named := map[int32]int32{}
				star := map[int32]int32{}
				srcs := map[int32][]string{}
				srcSeen := map[int32]map[string]bool{}
				for i := range g.TSExports {
					e := &g.TSExports[i]
					if !e.IsStar {
						named[e.FileID]++
						continue
					}
					star[e.FileID]++

					if !e.HasSource {
						continue
					}
					ss := srcSeen[e.FileID]
					if ss == nil {
						ss = map[string]bool{}
						srcSeen[e.FileID] = ss
					}
					v := cutStr(e.Source(), 26)
					if !ss[v] {
						ss[v] = true
						srcs[e.FileID] = append(srcs[e.FileID], v)
					}
				}
				t := &table{cols: []string{"barrel", "star_exports", "importers",
					"named_exports", "sloc", "reexports"}}

				fids := make([]int32, 0, len(star))
				for fid := range star {
					fids = append(fids, fid)
				}
				sort.Slice(fids, func(x, y int) bool { return fids[x] > fids[y] })
				for _, fid := range fids {
					c := star[fid]
					f := &g.Files[fid-1]
					if !g.modOK(f.ModuleID, mod) {
						continue
					}

					var re cell
					if v := joinDistinct(srcs[fid]); v != "" {
						re = cs(v)
					} else {
						re = cnull()
					}
					t.rows = append(t.rows, []cell{cs(f.Path()), ci32(c),
						ci32(importers[fid]), ci32(named[fid]), ci32(f.Sloc), re})
				}
				sortRows(t, func(a, b []cell) bool { return num(a[1]) > num(b[1]) })
				return lim(t, n)
			},
		},
		{
			Name: "strictness-map",
			Run: func(g *Graph, mod string, n int) *table {
				t := &table{cols: []string{"dir", "strict", "no_impl_any", "null_checks",
					"unchecked_index", "exact_optional", "verbatim", "erasable",
					"strict_flags", "target", "resolution", "removed_in_ts7"}}
				for i := range g.TSConfigs {
					c := &g.TSConfigs[i]
					if !likeMatch(mod, c.Dir()) {
						continue
					}
					rem := cnull()
					if c.HasRemoved {
						rem = cs(c.Removed())
					}
					t.rows = append(t.rows, []cell{cs(c.Dir()), cb(c.Strict),
						cb(c.NoImplAny), cb(c.NullChecks), cb(c.UncheckedIx),
						cb(c.ExactOpt), cb(c.Verbatim), cb(c.Erasable), ci32(c.NStrict),
						cs(c.Target()), cs(c.Resolution()), rem})
				}
				sortRows(t, func(a, b []cell) bool {
					ra, rb := a[11].s != "", b[11].s != ""
					if ra != rb {
						return ra
					}
					return num(a[8]) < num(b[8])
				})
				return lim(t, n)
			},
		},
		{
			Name: "type-depth-blowup",
			Run: symQ2([]string{"name", "kind", "depth", "conditionals", "cond_nesting",
				"mapped", "infers", "union_members", "template_types", "tparams",
				"fan_in", "at"},
				[]int{colName, colKind, mMaxTypeDepth, mNConditionalType,
					mNConditionalDepth, mNMappedType, mNInfer, mNUnionMembers,
					mNTemplateType, mNGenericParams, mFanIn, colAt},
				func(m []int32) bool {
					return m[mMaxTypeDepth] >= 3 || m[mNConditionalDepth] >= 2
				},
				nil, nil, []ordKey{{4, true}, {2, true}},

				false, false, nil, scanOrder{kind: scanPathLine}),
		},
		{
			Name: "weak-interfaces",
			Run: func(g *Graph, mod string, n int) *table {
				t := &table{cols: []string{"name", "kind", "members", "any_members",
					"index_sigs", "optional_", "readonly_", "extends_", "exported",
					"fan_in", "at"}}
				for i := range g.TypeDefs {
					td := &g.TypeDefs[i]
					if td.NAnyMembers == 0 && td.NIndexSig == 0 {
						continue
					}
					s := &g.Symbols[td.SymID-1]
					m := g.metrics(td.SymID)
					f := &g.Files[s.FileID-1]
					if f.IsTest || !g.modOK(s.ModuleID, mod) {
						continue
					}
					t.rows = append(t.rows, []cell{cs(s.Name()), cs(kindNames[s.Kind]),
						ci32(td.NMembers), ci32(td.NAnyMembers), ci32(td.NIndexSig),
						ci32(td.NOptional), ci32(td.NReadonly), ci32(td.NExtends),
						ci32(b2i(td.IsExported)), ci32(m[mFanIn]), cs(g.at(s))})
				}
				sortRows(t, func(a, b []cell) bool {
					av := num(a[3]) + num(a[4])
					bv := num(b[3]) + num(b[4])
					if av != bv {
						return av > bv
					}
					return num(a[9]) > num(b[9])
				})
				return lim(t, n)
			},
		},
		{
			Name: "dead-exports",
			Run: func(g *Graph, mod string, n int) *table {
				importers := map[int32]int32{}
				for i := range g.Imports {
					if g.Imports[i].TargetID > 0 {
						importers[g.Imports[i].TargetID]++
					}
				}

				type fnKey struct {
					fid  int32
					name string
				}
				matches := map[fnKey][]int32{}
				for i := range g.Symbols {
					s := &g.Symbols[i]
					k := fnKey{s.FileID, s.Name()}
					matches[k] = append(matches[k], int32(i+1))
				}
				t := &table{cols: []string{"export_", "kind", "path", "default_",
					"type_only", "file_importers", "fan_in", "sloc"}}

				for i := range g.TSExports {
					e := &g.TSExports[i]
					if e.IsStar || e.IsReexport {
						continue
					}
					f := &g.Files[e.FileID-1]
					if f.IsTest || f.IsGen || !g.modOK(f.ModuleID, mod) {
						continue
					}
					if importers[e.FileID] != 0 {
						continue
					}

					ms := matches[fnKey{e.FileID, e.Name()}]
					if len(ms) == 0 {
						t.rows = append(t.rows, []cell{cs(e.Name()), cs(e.Kind()), cs(f.Path()),
							cb(e.IsDefault), cb(e.IsTypeOnly), ci32(importers[e.FileID]),
							ci32(0), ci32(0)})
						continue
					}
					for _, sid := range ms {
						m := g.metrics(sid)
						if m[mFanIn] != 0 {
							continue
						}
						t.rows = append(t.rows, []cell{cs(e.Name()), cs(e.Kind()), cs(f.Path()),
							cb(e.IsDefault), cb(e.IsTypeOnly), ci32(importers[e.FileID]),
							ci32(0), ci32(m[mSloc])})
					}
				}
				sortRows(t, func(a, b []cell) bool { return num(a[7]) > num(b[7]) })
				return lim(t, n)
			},
		},
		{
			Name: "ts7-breaking",
			Run: func(g *Graph, mod string, n int) *table {
				enums := map[string]int32{}
				nsMods := map[string]int32{}
				for i := range g.Symbols {
					s := &g.Symbols[i]
					d := g.Files[s.FileID-1].Dir()
					if s.Kind == kEnum {
						enums[d]++
					}
					if s.Kind == kModule {
						nsMods[d]++
					}
				}
				countUnder := func(m map[string]int32, dir string) int32 {
					var c int32
					for d, v := range m {
						if d == dir || hasPrefix(d, dir) {
							c += v
						}
					}
					return c
				}
				t := &table{cols: []string{"dir", "breaks_in_ts7", "target", "module",
					"resolution", "erasable", "enums", "namespaces"}}
				for i := range g.TSConfigs {
					c := &g.TSConfigs[i]
					if !likeMatch(mod, c.Dir()) {
						continue
					}
					rem := cnull()
					if c.HasRemoved {
						rem = cs(c.Removed())
					}
					t.rows = append(t.rows, []cell{cs(c.Dir()), rem, cs(c.Target()),
						cs(c.Module()), cs(c.Resolution()), cb(c.Erasable),
						ci32(countUnder(enums, c.Dir())), ci32(countUnder(nsMods, c.Dir()))})
				}
				sortRows(t, func(a, b []cell) bool {
					ra, rb := a[1].s != "", b[1].s != ""
					return ra && !rb
				})
				return lim(t, n)
			},
		},
		{
			Name: "god-functions",
			Run: func(g *Graph, mod string, n int) *table {
				t := &table{cols: []string{"name", "sloc", "cyclo", "cog", "nest", "elifs",
					"returns_", "n_params", "any_", "maint", "at"}}

				sids := make([]int32, 0, len(g.Symbols))
				for _, sid := range g.scanIds(scanOrder{kind: scanFileKind}) {
					if g.isCallKind(g.Symbols[sid-1].Kind) {
						sids = append(sids, sid)
					}
				}
				sortSidsKindName(g, sids)
				for _, sid := range sids {
					s := &g.Symbols[sid-1]
					m := g.metrics(sid)
					f := &g.Files[s.FileID-1]
					if f.IsGen || !g.modOK(s.ModuleID, mod) {
						continue
					}
					t.rows = append(t.rows, []cell{cs(s.Name()), ci32(m[mSloc]),
						ci32(m[mCyclomatic]), ci32(m[mCognitive]), ci32(m[mMaxNesting]),
						ci32(m[mNElif]), ci32(m[mNReturns]), ci32(m[mNParams]),
						ci32(m[mNAnyTotal]), ci32(m[mMaintainability]), cs(g.at(s))})
				}
				sortRows(t, func(a, b []cell) bool { return num(a[3]) > num(b[3]) })
				return lim(t, n)
			},
		},
		{
			Name: "risk-ranked",
			Run: func(g *Graph, mod string, n int) *table {
				t := &table{cols: []string{"name", "risk", "cyclo", "cog", "any_", "as_any",
					"ts_ignore", "exec_", "sync_", "fan_in", "at"}}
				sids := make([]int32, 0, len(g.Symbols))
				for _, sid := range g.scanIds(scanOrder{kind: scanFileKind}) {
					if g.isCallKind(g.Symbols[sid-1].Kind) {
						sids = append(sids, sid)
					}
				}
				sortSidsKindName(g, sids)
				for _, sid := range sids {
					s := &g.Symbols[sid-1]
					m := g.metrics(sid)
					f := &g.Files[s.FileID-1]
					if f.IsGen || !g.modOK(s.ModuleID, mod) {
						continue
					}
					t.rows = append(t.rows, []cell{cs(s.Name()), ci32(m[mRiskScore]),
						ci32(m[mCyclomatic]), ci32(m[mCognitive]), ci32(m[mNAnyTotal]),
						ci32(m[mNAsAny]), ci32(m[mNTsIgnore]),
						ci32(m[hazardMetric("exec")]),
						ci32(m[hazardMetric("sync_block")]), ci32(m[mFanIn]),
						cs(g.at(s))})
				}
				sortRows(t, func(a, b []cell) bool { return num(a[1]) > num(b[1]) })
				return lim(t, n)
			},
		},
		{
			Name: "hot-multipliers",
			Run: func(g *Graph, mod string, n int) *table {
				t := &table{cols: []string{"name", "fan_in", "sites", "fan_out", "cyclo",
					"sloc", "doc", "exported", "returns_any", "at"}}

				sids := make([]int32, 0, len(g.Symbols))
				for _, sid := range g.scanIds(scanOrder{kind: scanPathKind}) {
					if g.isCallKind(g.Symbols[sid-1].Kind) {
						sids = append(sids, sid)
					}
				}
				sortSidsKindName(g, sids)
				for _, sid := range sids {
					s := &g.Symbols[sid-1]
					m := g.metrics(sid)
					if !g.modOK(s.ModuleID, mod) {
						continue
					}
					t.rows = append(t.rows, []cell{cs(s.Name()), ci32(m[mFanIn]),
						ci32(m[mNCallsites]), ci32(m[mFanOut]), ci32(m[mCyclomatic]),
						ci32(m[mSloc]), ci32(m[mHasDoc]), ci32(m[mIsExported]),
						ci32(m[mReturnsAny]), cs(g.at(s))})
				}
				sortRows(t, func(a, b []cell) bool {
					if num(a[1]) != num(b[1]) {
						return num(a[1]) > num(b[1])
					}
					return num(a[4]) > num(b[4])
				})
				return lim(t, n)
			},
		},
		{
			Name: "module-coupling",
			Run: func(g *Graph, mod string, n int) *table {
				t := &table{cols: []string{"name", "kind", "files", "sloc", "syms",
					"exported", "fan_in", "fan_out", "instability"}}
				for i := range g.Modules {
					m := &g.Modules[i]
					if m.NFiles == 0 || !likeMatch(mod, m.Name()) {
						continue
					}
					t.rows = append(t.rows, []cell{cs(m.Name()), cs(m.Kind()), ci32(m.NFiles),
						ci32(m.Sloc), ci32(m.NSymbols), ci32(m.NPublic), ci32(m.FanIn),
						ci32(m.FanOut), cf(roundTo(m.Instability, 2))})
				}
				sortRows(t, func(a, b []cell) bool {
					return (num(a[6]) + num(a[7])) > (num(b[6]) + num(b[7]))
				})
				return lim(t, n)
			},
		},
		{
			Name: "markers",
			Run: func(g *Graph, mod string, n int) *table {
				byFile := map[int32][]int32{}
				for i := range g.Symbols {
					s := &g.Symbols[i]
					if g.isCallKind(s.Kind) {
						byFile[s.FileID] = append(byFile[s.FileID], int32(i+1))
					}
				}

				for f := range byFile {
					ids := byFile[f]
					sort.SliceStable(ids, func(a, b int) bool {
						return g.Symbols[ids[a]-1].LineStart < g.Symbols[ids[b]-1].LineStart
					})
				}
				t := &table{cols: []string{"kind", "path", "line", "text", "in_fn", "fan_in"}}

				order := make([]int, 0, len(g.Markers))
				for i := range g.Markers {
					switch g.Markers[i].Kind() {
					case "TODO", "FIXME", "HACK", "BUG", "XXX", "WARNING":
					default:
						continue
					}
					order = append(order, i)
				}
				sort.SliceStable(order, func(x, y int) bool {
					a, b := &g.Markers[order[x]], &g.Markers[order[y]]
					if a.Kind() != b.Kind() {
						return a.Kind() < b.Kind()
					}
					if a.FileID != b.FileID {
						return a.FileID < b.FileID
					}
					return false
				})
				for _, mi := range order {
					k := &g.Markers[mi]
					f := &g.Files[k.FileID-1]
					if f.IsGen || !g.modOK(f.ModuleID, mod) {
						continue
					}
					name := "(module level)"
					var fan int32
					matched := false
					for _, sid := range byFile[k.FileID] {
						s := &g.Symbols[sid-1]
						if k.Line >= s.LineStart && k.Line <= s.LineEnd {
							t.rows = append(t.rows, []cell{cs(k.Kind()), cs(f.Path()), ci32(k.Line),
								cs(cutStr(k.Text(), 54)), cs(s.Name()),
								ci32(g.metrics(sid)[mFanIn])})
							matched = true
						}
					}
					if !matched {
						t.rows = append(t.rows, []cell{cs(k.Kind()), cs(f.Path()), ci32(k.Line),
							cs(cutStr(k.Text(), 54)), cs(name), ci32(fan)})
					}
				}
				sortRows(t, func(a, b []cell) bool { return num(a[5]) > num(b[5]) })
				return lim(t, n)
			},
		},
		{
			Name: "parse-coverage",
			Run: func(g *Graph, mod string, n int) *table {
				t := &table{cols: []string{"path", "lines", "error_nodes", "missing",
					"parsed", "generated", "test", "ext"}}
				for i := range g.Files {
					f := &g.Files[i]
					if f.NErrs == 0 && f.Parsed {
						continue
					}
					if !g.modOK(f.ModuleID, mod) {
						continue
					}
					t.rows = append(t.rows, []cell{cs(f.Path()), ci32(f.Lines),
						ci32(f.NErrs), ci32(f.NMissing), cb(f.Parsed), cb(f.IsGen),
						cb(f.IsTest), cs(f.Ext())})
				}
				sortRows(t, func(a, b []cell) bool { return num(a[2]) > num(b[2]) })
				return lim(t, n)
			},
		},
		{
			Name: "type-level-complexity",
			Run: symQ2([]string{"name", "qual", "type_depth", "cond_depth", "conds",
				"mapped", "infers", "templates", "union_members", "exported", "at"},
				[]int{colName, colQual, mMaxTypeDepth, mNConditionalDepth,
					mNConditionalType, mNMappedType, mNInfer, mNTemplateType,
					mNUnionMembers, mIsExported, colAt},
				func(m []int32) bool {
					return m[mMaxTypeDepth] > 2 || m[mNConditionalDepth] > 1
				},
				nil, nil, []ordKey{{3, true}, {2, true}, {6, true}},
				true, false, nil),
		},
		{
			Name: "index-signature-holes",
			Run: symQ2([]string{"name", "qual", "index_sigs", "unknowns", "anys", "keyofs",
				"prop_sigs", "call_sigs", "exported", "fan_in", "at"},
				[]int{colName, colQual, mNIndexSignature, mNUnknownType, mNAnyTotal,
					mNKeyof, mNPropSig, mNCallSig, mIsExported, mFanIn, colAt},
				func(m []int32) bool { return m[mNIndexSignature] > 0 },

				func(m []int32) int { return int(m[mIsExported]) },
				func(m []int32) int {
					return int(m[mNIndexSignature]) * (1 + int(m[mFanIn]))
				}, nil,
				true, false, nil, scanOrder{kind: scanFileLine}),
		},
		{
			Name: "declaration-vs-implementation",
			Run: symQ2([]string{"name", "qual", "declaration_only", "call_sigs", "prop_sigs",
				"type_args", "exported", "fan_in", "anys", "at"},
				[]int{colName, colQual, mIsDeclarationOnly, mNCallSig, mNPropSig,
					mNTypeArgs, mIsExported, mFanIn, mNAnyTotal, colAt},
				func(m []int32) bool { return m[mIsDeclarationOnly] == 1 },
				nil, nil, []ordKey{{6, true}, {8, true}, {7, true}},
				true, false, nil),
		},
		{
			Name: "deep-nesting-excessive",
			Run: symQ2([]string{"name", "nesting", "cyclo", "cognitive", "sloc", "fan_in", "at"},
				[]int{colName, mMaxNesting, mCyclomatic, mCognitive, mSloc, mFanIn, colAt},
				func(m []int32) bool { return m[mMaxNesting] > 4 },
				nil, nil, []ordKey{{1, true}, {2, true}},
				true, false, func(s *Symbol) bool {
					return s.Kind == kFunction || s.Kind == kMethod
				}, scanOrder{kind: scanFileKind}),
		},
		{
			Name: "too-many-params",
			Run: symQ2([]string{"name", "n_params", "n_optional_params", "destructured",
				"sloc", "cyclo", "fan_in", "at"},
				[]int{colName, mNParams, mNOptionalParams, mNDestructure, mSloc,
					mCyclomatic, mFanIn, colAt},
				func(m []int32) bool { return m[mNParams] > 4 },
				nil, nil, []ordKey{{1, true}, {6, true}},
				true, false, func(s *Symbol) bool {
					return s.Kind == kFunction || s.Kind == kMethod
				}, scanOrder{kind: scanFileKind}),
		},
		{
			Name: "scattered-concerns",
			Run: func(g *Graph, mod string, n int) *table {
				type acc struct {
					mods map[int32]bool
					list []string
					seen map[string]bool
				}
				accs := map[int32]*acc{}
				for i := range g.Edges {
					e := &g.Edges[i]
					if e.Self {
						continue
					}
					cm := g.Symbols[e.Caller-1].ModuleID
					a := accs[e.Callee]
					if a == nil {
						a = &acc{mods: map[int32]bool{}, seen: map[string]bool{}}
						accs[e.Callee] = a
					}
					if a.mods[cm] {
						continue
					}
					a.mods[cm] = true
					nm := g.moduleName(cm)
					if !a.seen[nm] {
						a.seen[nm] = true
						a.list = append(a.list, nm)
					}
				}
				t := &table{cols: []string{"name", "n_caller_modules", "fan_in", "cyclo",
					"sloc", "modules", "at"}}

				ids := make([]int32, 0, len(accs))
				for id := range accs {
					ids = append(ids, id)
				}
				slices.Sort(ids)
				for _, id := range ids {
					a := accs[id]
					if len(a.mods) <= 5 {
						continue
					}
					s := &g.Symbols[id-1]
					if s.Kind != kFunction && s.Kind != kMethod {
						continue
					}
					m := g.metrics(id)
					f := &g.Files[s.FileID-1]
					if f.IsTest || !g.modOK(s.ModuleID, mod) {
						continue
					}
					t.rows = append(t.rows, []cell{cs(s.Name()), ci(len(a.mods)),
						ci32(m[mFanIn]), ci32(m[mCyclomatic]), ci32(m[mSloc]),
						cs(joinDistinct(a.list)), cs(g.at(s))})
				}
				sortRows(t, func(a, b []cell) bool {
					if num(a[1]) != num(b[1]) {
						return num(a[1]) > num(b[1])
					}
					return num(a[2]) > num(b[2])
				})
				return lim(t, n)
			},
		},
		{
			Name: "async-surface",
			Run: func(g *Graph, mod string, n int) *table {
				type agg struct {
					fns, async, awaits, thens, alls, float, cbs, inLoop int32
				}
				per := map[int32]*agg{}
				for i := range g.Symbols {
					s := &g.Symbols[i]
					if !g.isCallKind(s.Kind) {
						continue
					}
					m := g.metrics(int32(i + 1))
					f := &g.Files[s.FileID-1]
					if f.IsTest || f.IsGen || !g.modOK(s.ModuleID, mod) {
						continue
					}
					a := per[s.ModuleID]
					if a == nil {
						a = &agg{}
						per[s.ModuleID] = a
					}
					a.fns++
					a.async += m[mIsAsync]
					a.awaits += m[mNAwait]
					a.thens += m[mNThenChain]
					a.alls += m[mNPromiseAll]
					a.float += m[mNFloatingPromise]
					a.cbs += m[mNAsyncCallback]
					a.inLoop += m[mAwaitInLoop]
				}
				t := &table{cols: []string{"module", "fns", "async_fns", "pct_async", "awaits",
					"then_chains", "promise_alls", "floating", "async_callback_args",
					"awaits_in_loop"}}

				mids := make([]int32, 0, len(per))
				for mid := range per {
					mids = append(mids, mid)
				}
				slices.Sort(mids)
				for _, mid := range mids {
					a := per[mid]
					if a.async == 0 {
						continue
					}
					t.rows = append(t.rows, []cell{cs(g.moduleName(mid)), ci(int(a.fns)),
						ci(int(a.async)), ci(int(100 * a.async / a.fns)), ci32(a.awaits),
						ci32(a.thens), ci32(a.alls), ci32(a.float), ci32(a.cbs),
						ci32(a.inLoop)})
				}
				sortRows(t, func(a, b []cell) bool {
					if num(a[2]) != num(b[2]) {
						return num(a[2]) > num(b[2])
					}
					return num(a[5]) > num(b[5])
				})
				return lim(t, n)
			},
		},
		{
			Name: "unsound-index",
			Run: func(g *Graph, mod string, n int) *table {
				type agg struct{ asAny, bang, supp, any, sloc int32 }
				per := map[int32]*agg{}
				for i := range g.Symbols {
					s := &g.Symbols[i]
					if !g.isCallKind(s.Kind) {
						continue
					}
					m := g.metrics(int32(i + 1))
					f := &g.Files[s.FileID-1]
					if f.IsTest || f.IsGen || !g.modOK(s.ModuleID, mod) {
						continue
					}
					a := per[s.ModuleID]
					if a == nil {
						a = &agg{}
						per[s.ModuleID] = a
					}
					a.asAny += m[mNAsAny]
					a.bang += m[mNNonNull]
					a.supp += m[mNSuppressions]
					a.any += m[mNAnyTotal]
					a.sloc += m[mSloc]
				}
				t := &table{cols: []string{"module", "as_any", "non_null_bang",
					"suppressions", "any_refs", "sloc", "unsound_per_kloc"}}

				mids := make([]int32, 0, len(per))
				for mid := range per {
					if per[mid].sloc != 0 {
						mids = append(mids, mid)
					}
				}
				sort.Slice(mids, func(x, y int) bool { return mids[x] > mids[y] })
				for _, mid := range mids {
					a := per[mid]
					v := 1000 * (int64(a.asAny)*3 + int64(a.bang) + int64(a.supp)*2 +
						int64(a.any)) / int64(a.sloc)
					if v == 0 {
						continue
					}
					t.rows = append(t.rows, []cell{cs(g.moduleName(mid)), ci32(a.asAny),
						ci32(a.bang), ci32(a.supp), ci32(a.any), ci32(a.sloc), cl(v)})
				}
				sortRows(t, func(a, b []cell) bool { return num(a[6]) > num(b[6]) })
				return lim(t, n)
			},
		},
		{
			Name: "attack-surface",
			Run: func(g *Graph, mod string, n int) *table {
				reads := map[int32]int32{}
				for i := range g.InputSites {
					s := &g.Symbols[g.InputSites[i].SymID-1]
					reads[s.ModuleID]++
				}
				type agg struct{ h, fetch, sync, child, cons, auth int32 }
				per := map[int32]*agg{}
				for i := range g.Symbols {
					s := &g.Symbols[i]
					if !g.isCallKind(s.Kind) {
						continue
					}
					m := g.metrics(int32(i + 1))
					f := &g.Files[s.FileID-1]
					if f.IsTest || f.IsGen || !g.modOK(s.ModuleID, mod) {
						continue
					}
					a := per[s.ModuleID]
					if a == nil {
						a = &agg{}
						per[s.ModuleID] = a
					}
					a.h += m[mIsHandler]
					a.fetch += m[mNFetch]
					a.sync += m[mNFsSync]
					a.child += m[mNChildProcess]
					a.cons += m[mNConsoleLog]
					a.auth += m[mNAuthCall]
				}
				t := &table{cols: []string{"module", "handlers", "input_reads", "fetches",
					"sync_fs_calls", "child_proc_calls", "console_calls", "auth_calls"}}

				mids := make([]int32, 0, len(per))
				for mid := range per {
					if per[mid].h != 0 || reads[mid] != 0 {
						mids = append(mids, mid)
					}
				}
				sort.Slice(mids, func(x, y int) bool { return mids[x] > mids[y] })
				for _, mid := range mids {
					a := per[mid]
					ir := reads[mid]
					t.rows = append(t.rows, []cell{cs(g.moduleName(mid)), ci32(a.h),
						ci32(ir), ci32(a.fetch), ci32(a.sync), ci32(a.child),
						ci32(a.cons), ci32(a.auth)})
				}
				sortRows(t, func(a, b []cell) bool {
					av := num(a[1])*2 + num(a[2])
					bv := num(b[1])*2 + num(b[2])
					return av > bv
				})
				return lim(t, n)
			},
		},
		{
			Name: "exposure-map",
			Run: func(g *Graph, mod string, n int) *table {

				const maxDepth = 6
				roots := g.entryRoots(false)
				a := g.adj()
				type acc struct {
					entries int32
					reach   int64
					maxR    int64
					sum     int64
				}
				per := map[int32]*acc{}
				for _, r := range roots {
					seen := map[int32]bool{r: true}
					count := int32(1)
					cur := []int32{r}
					for d := 0; d < maxDepth && len(cur) > 0; d++ {
						var next []int32
						for _, u := range cur {
							for k := a.outOff[u]; k < a.outOff[u+1]; k++ {
								v := a.outTo[k]
								if seen[v] {
									continue
								}
								seen[v] = true
								count++
								next = append(next, v)
							}
						}
						cur = next
					}
					mid := g.Symbols[r-1].ModuleID
					ac := per[mid]
					if ac == nil {
						ac = &acc{}
						per[mid] = ac
					}
					ac.entries++
					ac.reach += int64(count)
					ac.sum += int64(count)
					if int64(count) > ac.maxR {
						ac.maxR = int64(count)
					}
				}
				t := &table{cols: []string{"module", "entry_points", "symbols_reachable",
					"max_from_one_entry", "avg_from_entry"}}
				mids := make([]int32, 0, len(per))
				for mid := range per {
					mids = append(mids, mid)
				}

				sort.Slice(mids, func(x, y int) bool { return mids[x] > mids[y] })
				for _, mid := range mids {
					a2 := per[mid]
					if !g.modOK(mid, mod) {
						continue
					}
					avg := 0.0
					if a2.entries > 0 {
						avg = sqliteRound(float64(a2.sum)/float64(a2.entries), 1)
					}
					t.rows = append(t.rows, []cell{cs(g.moduleName(mid)), ci32(a2.entries),
						cl(a2.reach), cl(a2.maxR), cf(avg)})
				}
				sortRows(t, func(a, b []cell) bool { return num(a[2]) > num(b[2]) })
				return lim(t, n)
			},
		},
		{
			Name: "untested-risk",
			Run: func(g *Graph, mod string, n int) *table {
				fromTest := map[int32]bool{}
				for i := range g.Edges {
					e := &g.Edges[i]
					c := &g.Symbols[e.Caller-1]
					if g.Files[c.FileID-1].IsTest || g.metrics(e.Caller)[mIsTest] == 1 {
						fromTest[e.Callee] = true
					}
				}
				t := &table{cols: []string{"name", "risk", "fan_in", "cyclo", "anys",
					"exec_calls", "at"}}

				sids := make([]int32, 0, len(g.Symbols))
				for _, sid := range g.scanIds(scanOrder{kind: scanFileKind}) {
					if g.isCallKind(g.Symbols[sid-1].Kind) {
						sids = append(sids, sid)
					}
				}
				sortSidsKindName(g, sids)
				for _, sid := range sids {
					s := &g.Symbols[sid-1]
					m := g.metrics(sid)
					if m[mRiskScore] == 0 || m[mIsTest] == 1 {
						continue
					}
					f := &g.Files[s.FileID-1]
					if f.IsTest || f.IsGen || !g.modOK(s.ModuleID, mod) {
						continue
					}
					if fromTest[sid] {
						continue
					}
					t.rows = append(t.rows, []cell{cs(s.Name()), ci32(m[mRiskScore]),
						ci32(m[mFanIn]), ci32(m[mCyclomatic]), ci32(m[mNAnyTotal]),
						ci32(m[hazardMetric("exec")]), cs(g.at(s))})
				}
				sortRows(t, func(a, b []cell) bool { return num(a[1]) > num(b[1]) })
				return lim(t, n)
			},
		},
		{
			Name: "generic-hotspots",
			Run: symQ2([]string{"name", "kind", "tparams", "type_args", "call_sites",
				"instantiation_load", "conds", "fan_in", "at"},
				[]int{colName, colKind, mNGenericParams, mNTypeArgs, mNCallsites, colScore,
					mNConditionalType, mFanIn, colAt},
				func(m []int32) bool { return m[mNTypeArgs] > 0 || m[mNGenericParams] > 0 },
				func(m []int32) int {
					cs := max(m[mNCallsites], 1)
					return int(m[mNTypeArgs])*int(cs) + int(m[mNGenericParams])
				},
				nil, []ordKey{{3, true}}, true, false, nil, scanOrder{kind: scanFileLine}),
		},
		{
			Name: "handler-latency-budget",
			Run: symQ2([]string{"name", "awaits", "awaits_in_loop", "net_calls", "fetches",
				"sync_fs", "io", "serialized_ops", "fan_in", "at"},
				[]int{colName, mNAwait, mAwaitInLoop, hazardMetric("net"),
					mNFetch, mNFsSync, hazardMetric("io"), colScore, mFanIn, colAt},
				func(m []int32) bool {
					return m[mIsHandler] == 1 &&
						(m[mNAwait]+m[hazardMetric("net")]+m[mNFetch]+
							m[hazardMetric("io")]) > 0
				},
				func(m []int32) int {
					return int(m[mNAwait]) + int(m[mAwaitInLoop])*5 +
						int(m[hazardMetric("net")]) + int(m[mNFetch]) +
						int(m[hazardMetric("io")])
				},
				nil, nil, true, true, nil),
		},
		{
			Name: "heavy-constructors",
			Run: symQ2([]string{"constructor", "class_", "cyclo", "calls", "io", "net",
				"n_params", "sloc", "fan_in", "at"},
				[]int{colName, colPar, mCyclomatic, mNCalls, hazardMetric("io"),
					hazardMetric("net"), mNParams, mSloc, mFanIn, colAt},
				func(m []int32) bool {
					return m[mCyclomatic] > 3 || m[hazardMetric("io")] > 0 ||
						m[hazardMetric("net")] > 0 || m[mNCalls] > 5
				},
				func(m []int32) int {
					return int(m[mCyclomatic]) + int(m[hazardMetric("io")])*3 +
						int(m[hazardMetric("net")])*3 + int(m[mNCalls])
				},
				nil, nil, true, true, func(s *Symbol) bool {
					return s.Name() == "constructor" && s.Kind == kMethod
				}),
		},
		{
			Name: "framework-magic",
			Run: func(g *Graph, mod string, n int) *table {
				dec := map[int32]bool{}
				for i := range g.Attributes {
					dec[g.Attributes[i].SymID] = true
				}
				type acc struct{ methods, decorated, decZero int32 }
				per := map[int32]*acc{}
				for i := range g.Symbols {
					s := &g.Symbols[i]
					if s.Kind != kMethod {
						continue
					}
					f := &g.Files[s.FileID-1]
					if f.IsTest || f.IsGen || !g.modOK(s.ModuleID, mod) {
						continue
					}
					a := per[s.ModuleID]
					if a == nil {
						a = &acc{}
						per[s.ModuleID] = a
					}
					a.methods++
					if dec[int32(i+1)] {
						a.decorated++
						if g.metrics(int32(i + 1))[mFanIn] == 0 {
							a.decZero++
						}
					}
				}
				t := &table{cols: []string{"module", "methods", "decorated_methods",
					"decorated_zero_caller", "pct_decorated"}}

				mids := make([]int32, 0, len(per))
				for mid := range per {
					if per[mid].decorated != 0 {
						mids = append(mids, mid)
					}
				}
				sort.Slice(mids, func(x, y int) bool { return mids[x] > mids[y] })
				for _, mid := range mids {
					a := per[mid]
					t.rows = append(t.rows, []cell{cs(g.moduleName(mid)), ci32(a.methods),
						ci32(a.decorated), ci32(a.decZero),
						ci(int(100 * a.decorated / a.methods))})
				}
				sortRows(t, func(a, b []cell) bool { return num(a[2]) > num(b[2]) })
				return lim(t, n)
			},
		},
		{
			Name: "error-handling-map",
			Run: func(g *Graph, mod string, n int) *table {
				type acc struct{ throws, catches, broad, empty, tries, noTry int32 }
				per := map[int32]*acc{}
				for i := range g.Symbols {
					s := &g.Symbols[i]
					if !g.isCallKind(s.Kind) {
						continue
					}
					m := g.metrics(int32(i + 1))
					f := &g.Files[s.FileID-1]
					if f.IsTest || f.IsGen || !g.modOK(s.ModuleID, mod) {
						continue
					}
					a := per[s.ModuleID]
					if a == nil {
						a = &acc{}
						per[s.ModuleID] = a
					}
					a.throws += m[mNThrow]
					a.catches += m[mNCatch]
					a.broad += m[mNCatchBroad]
					a.empty += m[mNCatchEmpty]
					a.tries += m[mNTry]
					if m[mIsAsync] == 1 && m[mNAwait] > 0 && m[mNTry] == 0 {
						a.noTry++
					}
				}
				t := &table{cols: []string{"module", "throws", "catches", "broad_catches",
					"empty_catches", "try_blocks", "async_fns_no_try"}}

				mids := make([]int32, 0, len(per))
				for mid := range per {
					if per[mid].throws+per[mid].catches != 0 {
						mids = append(mids, mid)
					}
				}
				sort.Slice(mids, func(x, y int) bool { return mids[x] > mids[y] })
				for _, mid := range mids {
					a := per[mid]
					t.rows = append(t.rows, []cell{cs(g.moduleName(mid)), ci32(a.throws),
						ci32(a.catches), ci32(a.broad), ci32(a.empty), ci32(a.tries),
						ci32(a.noTry)})
				}
				sortRows(t, func(a, b []cell) bool {
					return (num(a[1]) + num(a[2])) > (num(b[1]) + num(b[2]))
				})
				return lim(t, n)
			},
		},
	}
}

func (g *Graph) moduleName(mid int32) string {
	if mid <= 0 || int(mid) > len(g.Modules) {
		return "(root)"
	}
	return g.Modules[mid-1].Name()
}

func sqliteRound(f float64, places int) float64 {
	if math.IsInf(f, 0) || math.IsNaN(f) {
		return f
	}
	bf := new(big.Float).SetFloat64(f)
	s := bf.Text('f', 800)
	neg := false
	if s[0] == '-' {
		neg = true
		s = s[1:]
	}
	dot := strings.IndexByte(s, '.')
	intPart, frac := s, ""
	if dot >= 0 {
		intPart, frac = s[:dot], s[dot+1:]
	}
	if len(frac) > places {
		keep := frac[:places]
		if frac[places] >= '5' {
			d := []byte(keep)
			i := len(d) - 1
			for ; i >= 0; i-- {
				if d[i] < '9' {
					d[i]++
					break
				}
				d[i] = '0'
			}
			if i < 0 {

				ip := []byte(intPart)
				j := len(ip) - 1
				for ; j >= 0; j-- {
					if ip[j] < '9' {
						ip[j]++
						break
					}
					ip[j] = '0'
				}
				if j < 0 {
					intPart = "1" + string(ip)
				} else {
					intPart = string(ip)
				}
				d = nil
			}
			keep = string(d)
		}
		frac = keep
	}
	for len(frac) < places {
		frac += "0"
	}
	out := intPart
	if places > 0 {
		out += "." + frac
	}
	if neg {
		out = "-" + out
	}
	v, err := strconv.ParseFloat(out, 64)
	if err != nil {
		return f
	}
	return v
}

func roundTo(f float64, places int) float64 {
	pow := 1.0
	for range places {
		pow *= 10
	}
	v := f * pow
	if v >= 0 {
		v = float64(int64(v + 0.5))
	} else {
		v = float64(int64(v - 0.5))
	}
	return v / pow
}

var qTitles = [80]string{
	"`any` weighted by how much code inherits the hole",
	"@ts-ignore and eslint-disable sitting on code many callers depend on",
	"Subscriptions added and never removed",
	"Timers started with no matching clear",
	"Blocking *Sync calls reachable from a request handler, up to 4 hops",
	"Sequential awaits that could have overlapped",
	"Regexes that can blow up, and how far they sit from an entry point",
	"innerHTML and friends, ranked by reachability from outside",
	"Files that import each other, and whether the cycle is type-only",
	"`as` and `!` clustered where types are weakest",
	"as any, non-null ! and angle-bracket casts: where the type system was told to be quiet",
	"@ts-ignore, @ts-expect-error and eslint-disable, and which are load-bearing",
	"Nothing in this tree calls these",
	"synchronous fs or a nested scan reachable from an exported or handler entry point",
	"a function that adds listeners and neither removes nor disposes them",
	"Functions using any type (eslint @typescript-eslint/no-explicit-any)",
	"@ts-ignore or @ts-expect-error suppressions (eslint)",
	"! non-null assertion (eslint @typescript-eslint/no-non-null-assertion)",
	"as assertion bypassing the type system (eslint @typescript-eslint/consistent-type-assertions)",
	"Promise not awaited or caught (eslint @typescript-eslint/no-floating-promises)",
	"await inside a loop (eslint @typescript-eslint/no-await-in-loop)",
	"innerHTML or dangerouslySetInnerHTML (eslint security)",
	"Regex that may cause catastrophic backtracking (eslint security/ReDoS)",
	"process.exit reachable from a handler (eslint no-process-exit)",
	"Type-space vs value-space weight ratio per file",
	"Interfaces and type aliases no runtime symbol references",
	"tsconfig path aliases declared vs alias imports used",
	"Files declaring global types and ambient modules",
	"Interfaces by extends breadth and chain depth",
	"Modules exporting type-only symbols without runtime values",
	"Class methods with zero resolved callers",
	"@deprecated symbols still being called (typescript-eslint no-deprecated)",
	"Enums where two members alias one runtime value",
	"Enums mixing numeric and string members",
	"Value imports of modules whose every export is type-only",
	"Bare @ts-ignore / @ts-expect-error with no reason",
	"package.json dependencies never imported (knip/machete territory)",
	"Template literals with any-typed substitutions",
	"Exported interfaces with no readonly members (prefer-readonly)",
	"ui/views/pages files importing api/db/server files",
	"child_process.exec / execSync / spawnSync sites (OWASP G10)",
	"location.href writes in handlers that read request input (OWASP G26)",
	"fetch/http calls in functions that read request input (OWASP G27)",
	"Credential-shaped string literals (OWASP G07)",
	"fs.* with a non-literal path in input-reading functions (OWASP G12)",
	"fs.writeFile fed from req.files with no visible check (OWASP G28)",
	"Archive extraction sites (OWASP G29)",
	"Object.assign in functions that read request input (OWASP G30)",
	"Logger calls in functions that read request input (OWASP G14)",
	"console.* calls in functions that read request input (OWASP G21)",
	"Request input read with no auth call in the function (OWASP G01)",
	"Call sites where a synchronous caller invokes an async function",
	"Async APIs every one of whose callers is unable or unlikely to await",
	"Async functions passed as arguments where void-returning are expected",
	"Event listeners registered with an async callback (rejections vanish)",
	"new Promise(async (resolve) => ...) -- the executor drops rejections",
	"Awaited calls whose callee is declared void or a plain value",
	"Constructors awaiting nothing but calling async work",
	"Value-import cycles of 3 to 5 files (the pairs query cannot see these)",
	"Async functions with awaits, no try/catch, no .catch, and callers",
	"Factories returning Disposable whose callers never call dispose",
	"Plain DTO classes (zero decorators) reaching IO-performing methods",
	"Classes with mutable fields whose methods read request input",
	"as any, ! and suppressions reachable from exported or handler entry points",
	"Decorator-registered methods with no resolved caller (framework or dead)",
	"Properties with a getter but no setter (or the reverse) in one class",
	"Getters that await or do IO -- properties that are secretly requests",
	"Async functions with no await, called by others (require-await at range)",
	"Functions building .then chains with no catch anywhere in the body",
	"Functions that build .then chains but return void to their callers",
	"Request handlers that await with no try/catch -- one throw is a 500",
	"Timers started with an async callback -- rejections no one can catch",
	"Override-marked methods that never call super (strict-override)",
	"Two classes whose members call each other (NestJS circular providers)",
	"Functions mixing await and .then in one flow",
	"Async functions declared : void -- callers cannot await the failure",
	"Promise.all inside a loop -- n x args concurrent operations",
	"Top-level statements doing IO -- import-time side effects",
	"Handlers taking untyped/any request params, ranked by input reads",
	"Promise chains 3+ .then calls deep in one function",
}

var qNotes = [80]string{
	"ANSWERS which `any` actually costs you. A count of `any` per file is\n     noise; an EXPORTED function returning `any` silently unchecks every\n     one of its callers, and that is what this ranks.\nACT fix the highest fan_in first -- one signature re-checks many call\n     sites. Prefer `unknown` plus a narrowing check over `any`.\nMISLEADS the blast column multiplies by MAX(fan_in,1), so a symbol with\n     NO known caller scores exactly as if it had one. Read fan_in=0\n     rows as 'unknown reach', never as 'reach of 1'.\n     `any` at a genuinely dynamic boundary -- JSON parsing, a plugin\n     API -- is the right answer and appears here. Test files are excluded,\n     so a mock typed `any` is NOT here. And a function typed `any` that\n     nothing calls costs nothing.",
	"ANSWERS where the type checker was switched off somewhere that matters.\nACT `@ts-expect-error` is strictly better than `@ts-ignore`: it FAILS when\n     the error goes away, so it cannot rot. Convert them, then fix the\n     high-fan_in ones.\nMISLEADS a suppression with a written reason next to a known upstream bug\n     is fine and appears here. The `reason` column is the evidence -- an\n     empty one is the signal, not the presence of the comment.",
	"ANSWERS the leak no JavaScript or TypeScript linter checks for. Across\n     ESLint, typescript-eslint, unicorn, Biome, oxlint and CodeQL there is\n     no rule for this; it is a genuine gap, not a duplicate.\nACT every add needs a matching remove on the same target, in a cleanup\n     path -- a React effect return, a `destroy`, or an AbortController\n     signal. A listener added inside a loop with no removal grows without\n     bound.\nMISLEADS the pairing is per FUNCTION, so an add in `mount` and a remove in\n     `unmount` looks unbalanced and is correct. Check the owning class\n     before acting; `target` is there to help you match them by hand.",
	"ANSWERS the other half of the leak nobody lints for. A `setInterval` with\n     no `clearInterval` runs until the process dies and keeps every\n     variable its callback closes over alive with it.\nACT store the handle and clear it in the teardown path.\nMISLEADS a `setTimeout` that fires once needs no clear and is counted\n     here. The dangerous one is `setInterval`, and a timer started inside\n     a loop or a request handler.",
	"ANSWERS which endpoint stops the whole event loop. Node is single\n     threaded per process: one `readFileSync` in one handler blocks every\n     other in-flight request, not just its own.\nACT use the promise API. `fs/promises`, `execFile`, `pbkdf2` -- every\n     *Sync has an async twin.\nMISLEADS a *Sync call at startup, in a CLI, or in a build script is\n     correct and often preferable. Only rows reachable from a handler are\n     the finding, which is what the hop count is for.",
	"ANSWERS where latency is the SUM of N round trips instead of the max.\nACT if the iterations are independent, build the promises and hand them\n     to Promise.all. N x 40ms becomes 40ms.\nMISLEADS some loops MUST be sequential -- pagination, rate limits, or a\n     later iteration depending on an earlier result. `promise_all` in the\n     same row means the author already knows the pattern.",
	"ANSWERS which regex a crafted input can hang the process with. A\n     quantifier inside a quantified group backtracks exponentially.\nACT rewrite to avoid nested quantifiers, or bound the input length before\n     matching. Node has no regex timeout.\nMISLEADS the pattern detector is shape-based and over-reports: many nested\n     quantifiers are provably linear because their branches cannot both\n     match. Confirm with a backtracking analyser before acting.",
	"ANSWERS where a string becomes markup the browser will execute.\nACT use textContent, or sanitise with a real sanitiser. Framework escape\n     hatches (dangerouslySetInnerHTML) are named that way for a reason.\nMISLEADS assigning a constant template to innerHTML is safe and appears\n     here. This finds the SINK; whether untrusted data reaches it needs a\n     taint analysis this does not do.",
	"ANSWERS which import pairs are mutually dependent.\nACT a VALUE cycle is a runtime hazard: one side sees a partly initialised\n     module. A TYPE-ONLY cycle is erased at compile time and is harmless.\n     Fix the value cycles; convert the rest to `import type`.\nMISLEADS this compares direct file-to-file edges only, so a three-hop\n     cycle is invisible and the count UNDERSTATES. Unresolved import\n     targets (bare package specifiers) are excluded entirely.",
	"ANSWERS where the code is telling the compiler to trust it. Each `as` and\n     each `!` is a place a runtime type error can no longer be caught.\nACT `as unknown as T` is a double assertion and always worth reading.\n     `!` on a value the checker thinks is nullable is either a missing\n     guard or a lie.\nMISLEADS an assertion after a hand-written type guard is correct and\n     appears here; `satisfies` is the safe alternative and is counted\n     separately as counter-evidence.",
	"ANSWERS where a type was asserted rather than proved. `x!` claims a\n     value is not null with no check; `as any` disables every check\n     downstream of it. Both move a failure from tsc to run time, and\n     `as any` additionally poisons inference for whatever it flows into.\nACT narrow instead of asserting -- an if, a type guard, or `satisfies`,\n     which checks without widening. Where an assertion is genuinely\n     needed at a boundary, assert to the specific type, never to any.\nMISLEADS a single `as any` in a well-fenced adapter is a deliberate,\n     correct trade. What this ranks is DENSITY on code others call --\n     the assertions that leak their looseness outwards.",
	"ANSWERS how much of the codebase compiles only because it was told to.\n     The difference matters: `@ts-expect-error` FAILS when the error goes\n     away, so it cleans itself up; `@ts-ignore` silently outlives the\n     problem it was hiding and then hides the next one.\nACT convert every `@ts-ignore` to `@ts-expect-error`. The ones that then\n     fail the build were suppressing nothing and can be deleted; the\n     rest now tell you when they become unnecessary.\nMISLEADS a suppression on a known upstream typing bug is the right call\n     and cannot be distinguished here from one hiding a real defect.\n     Density plus fan_in is the ranking, not the raw count.",
	"ANSWERS what might be deletable.\nACT grep the name as a STRING before deleting anything: a registry entry,\n     a config value or a reflective call keeps a symbol alive with no edge\n     to show for it.\nMISLEADS this is the query most likely to be wrong, and `graph-blindspots`\n     measures by how much. Public symbols are excluded because a caller\n     outside this tree cannot be seen at all, so what is left is private\n     and unreferenced -- a much weaker claim than dead.",
	"ANSWERS the question typescript-eslint answers per-file: no-sync,\n     no-await-in-loop and the perf rules each see one function. The graph\n     sees the path. A `readFileSync` in a helper is fine until an exported\n     API reaches it, at which point every consumer of that API inherits a\n     blocked event loop.\nACT for `sync_fs_calls`, move to the promise API. For `search_in_loop`,\n     hoist a Set. `reached_from` names the exported symbol whose latency\n     budget this spends.\nMISLEADS an exported symbol is not necessarily public API -- a barrel file\n     re-exports everything, so `is_exported` overcounts. Depth is bounded\n     at 4 hops, and a call through an interface method is only resolved\n     when the implementation is unambiguous.",
	"ANSWERS the leak no linter states as a rule because the pairing is a\n     convention, not a syntax: whatever calls addEventListener, `.on` or\n     `.subscribe` must eventually call the matching remove, or hand the\n     handle to something that will. A function with adds, zero removes and\n     zero dispose calls either delegates ownership or leaks -- and the\n     graph shows how many callers currently assume the former.\nACT return the disposable so the caller can own it, or register into a\n     DisposableStore. `listener_in_loop` marks the version that leaks once\n     per iteration rather than once per call.\nMISLEADS the correct case looks identical: a function that adds a listener\n     and returns the disposable is right, and the return value is not\n     modelled. A listener on an object that dies with the function is also\n     fine. Read this as an audit list, not a leak list.",
	"ANSWERS where the any type is used, which disables type checking. Each\n     site is a potential runtime bug that the compiler cannot catch.\nACT replace any with unknown (and narrow), or a specific type.\nMISLEADS any in a type declaration file (.d.ts) for JS interop is sometimes\n     needed. n_as_any counts `as any` assertions separately.",
	"ANSWERS where @ts-ignore or @ts-expect-error is used, which silences the\n     compiler. Each is a deferred type error.\nACT fix the underlying type error; @ts-expect-error is better than\n     @ts-ignore because it fails if the error disappears.\nMISLEADS suppression for a known library type bug is sometimes correct.\n     The graph counts suppressions but not their reasons.",
	"ANSWERS where the ! non-null assertion is used, which asserts a value is\n     non-null without checking. If the value is actually null/undefined,\n     this is a runtime TypeError.\nACT use optional chaining (?.) or nullish coalescing (??), or check.\nMISLEADS ! after a typeof check or a truthiness guard is redundant but safe.\n     The graph counts assertions but not preceding checks.",
	"ANSWERS where `as Type` is used to force a type assertion, which bypasses\n     the compiler's type checking. Each is a potential type mismatch.\nACT use a type guard (typeof, instanceof, in) or a properly typed constructor.\nMISLEADS `as` for narrowing after a check is correct. `as const` is safe.\n     n_as_any is the worst variant (as any).",
	"ANSWERS where a Promise is created but not awaited, caught, or returned.\n     Errors from floating promises are silently lost.\nACT await the promise, add .catch(), or explicitly void it.\nMISLEADS n_floating_promise only fires for statement-position .then/.catch/\n     .finally chains; the most common floating promise (a bare async call\n     or assignment that is discarded) is not counted. n_floating_promise\n     is a lower bound, not a complete count.",
	"ANSWERS where await is used inside a loop, serializing each iteration. For\n     independent operations, this is O(n) when it could be O(1) with\n     Promise.all.\nACT use Promise.all if iterations are independent; keep await if each\n     iteration depends on the previous.\nMISLEADS a loop that processes items sequentially by design (e.g. rate-limited\n     API calls) is correct.",
	"ANSWERS where innerHTML or dangerouslySetInnerHTML is used, which can inject\n     arbitrary HTML/JS if the value contains user input.\nACT use textContent, or sanitize with DOMPurify.\nMISLEADS innerHTML with a constant string is safe. The graph sees the call\n     but not the value's source.",
	"ANSWERS where regex patterns are used that may be vulnerable to ReDoS,\n     causing catastrophic backtracking on certain inputs.\nACT audit the regex pattern; avoid nested quantifiers like (a+)+.\nMISLEADS n_regex_redos counts patterns that match a heuristic; the actual\n     vulnerability depends on the pattern and the input.",
	"ANSWERS where process.exit is reachable from a request handler.\nACT throw an error; let the top-level handler decide.\nMISLEADS process.exit in main() is correct.",
	"ANSWERS the compile-time/runtime balance of every file: how many type\n     constructs (interface/type/enum) versus runtime constructs\n     (class/function) it declares. A type-dense file is a contract\n     surface; a value-dense one is behavior.\nACT a high type-ratio file is where a type-level change ripples most; a\n     low ratio with large exports is where a runtime behavior lives.\n     The ratio is advisory: categories are keyed by symbol kind, which\n     the parser classifies by construct, not by intent.\nMISLEADS a module of consts with types imported from elsewhere looks\n     value-heavy; an interface-only barrel looks type-heavy though its\n     runtime cost is nil. `declaration-vs-implementation` covers the\n     exported half of this question.",
	"ANSWERS the type-level constructs with no detected runtime use: no\n     symbol signature contains the type name, and no ts_exports row ties\n     it to a value. Each row is a candidate dead contract -- or a\n     deliberately exported API type consumed outside this tree.\nACT grep the type name as a string before deleting: an ambient module,\n     a mapped type over it, or generic instantiation can keep it alive\n     without any signature match here.\nMISLEADS the used-check is a precomputed token table (identifier tokens\n     of every signature, built at post_build): a name counts as used iff\n     it is a standalone token in some OTHER symbol's signature -- the\n     boundary-safe predicate, linear instead of the old quadratic GLOB\n     cross-product. A namespaced type (`ns.Foo`) whose simple name never\n     appears bare is reported even when used as `ns.Foo`; an exported\n     type consumed by an external package is invisible. This is a\n     candidate list, not a deletion list.",
	"ANSWERS per project dir how much the codebase leans on its own path\n     aliases (@app/*, @utils/*) versus raw relative imports. The\n     declared alias count is the config surface; the used count is the\n     practice.\nACT an alias declared but never used is config debt; heavy alias use\n     with no baseUrl is a bundle-configured redirect that stops working\n     the day the toolchain changes. The paths_json column records the\n     exact map.\nMISLEADS alias USE is counted as imports whose target starts with @*/\n     (the dominant convention); aliases without an @-prefix are missed,\n     and a relative import that reaches the same file is not\n     normalised to an alias-equivalent, so utilization is a floor.",
	"ANSWERS the files that augment the global environment: ambient\n     declarations (.d.ts with `declare`), global interfaces merged onto\n     existing ones, and `declare module` blocks. Each is a change to\n     the type environment visible project-wide.\nACT track these files as the ambient surface: a name collision or a\n     removed augmentation breaks every consumer, and no import chain\n     records the dependency.\nMISLEADS `is_ambient` comes from the `declare` keyword in the first 40\n     chars of the declaration block (the analyzer's documented\n     heuristic); `declare global` blocks augmenting an EXISTING global\n     are marked ambient but not distinguished from declarations that\n     introduce brand-new types.",
	"ANSWERS the interface contracts with the widest extends fan-out\n     (A extends B, C) and the deepest inherited chains -- the type\n     shapes whose supertype change ripples across every dependent\n     interface.\nACT an interface extending many others is a contract that inherits\n     every one of those responsibilities; splitting or merging it\n     changes the whole fan. `type-defs.n_extends` counts direct\n     parents only.\nMISLEADS extends_names is captured per declaration and matched\n     by name; a chain through re-exported or namespaced parents breaks\n     at the first unresolved hop, so chain depth is a floor.",
	"ANSWERS modules whose ts_exports declare type-only (interface/type)\n     names -- the contract-only modules with no runtime executable\n     surface. Two shapes get flagged: a type-only barrel (fine when\n     intentional) and a module exporting an interface the consumers\n     can never instantiate.\nACT for a contract module, keep the export list explicit and add a\n     README note; for a candidate dead module, grep whether any value\n     symbol imports it at all.\nMISLEADS is_type_only on ts_exports is per-export; a module with one\n     type export AND a value export is not flagged, and a type exported\n     without the `type` keyword reads as a value export to the parser\n     when the compiler would elide it.",
	"ANSWERS the service-layer (and every class) methods nothing in the\n     tree calls -- the API surface that is either about to be used by\n     a caller this analyzer cannot see, or genuinely dead.\nACT for each row, grep the method name including its class (`svc.\n     method`): a template string call or a dispatch table can hide it.\n     `dead-code` covers unexported functions; this covers the method-\n     on-a-class shape with the class context visible.\nMISLEADS resolution is by name; a method reached through an interface\n     satisfaction, a `Proxy`, or a decorator that rewrites the name is\n     invisible here, and exported class methods are excluded only when\n     the class itself is exported.",
	"ANSWERS @deprecated functions/methods with in-tree callers, ranked by\n     distinct callers: the migration list. Each row is a call site\n     family that will break (or at least lose its promise) when the\n     symbol is removed.\nACT migrate callers top-down; the deprecation message says where.\nMISLEADS is_deprecated comes from a @deprecated tag in the doc comment\n     immediately above the declaration -- a deprecation declared in a\n     type's interface but implemented in a class without the tag reads\n     as clean, and public-API deprecation is deliberate: the rows are\n     the migration list, not violations. Name-based edges may hit the\n     wrong overload.",
	"ANSWERS enums with two members equal to the same value: `==` between\n     members is true and a switch on the value hits the first member.\n     Rows name the members and the colliding value.\nACT rename or re-value one member; if intentional, comment it.\nMISLEADS computed members are excluded (n_fields > 0 / non-literal\n     value); intentional bitflag aliases are the dominant false\n     positive -- a flag set whose members share bits is NOT a bug.",
	"ANSWERS enums whose members are a mix of numbers and strings: the\n     runtime values have two types, comparisons and serialization\n     behave differently per member, and a switch written for one half\n     silently misses the other.\nACT split into two enums, or make every member one type.\nMISLEADS a member whose value is a computed expression (n_fields > 0)\n     is excluded because its type is unknown; a member with no value at\n     all auto-increments numerically and counts as numeric.",
	"ANSWERS value-space imports of modules that export nothing but types:\n     a dead runtime import, and a real compile error under\n     verbatimModuleSyntax, which elides nothing.\nACT switch to `import type`; confirm the module really has no values.\nMISLEADS re-export chains confuse target matching (the barrel's\n     exports are what counts, not the leaf's); side-effect-only modules\n     have no exports and are excluded by the EXISTS; per-NAME import\n     analysis needs a capture this query deliberately lacks.",
	"ANSWERS suppressions whose trailing comment is empty: nobody wrote why\n     the suppression is safe. The ts-expect-error form FAILS the build\n     when the error disappears, so a bare one is also a silent\n     invitation to leave it behind forever.\nACT add the reason (`// @ts-expect-error - <why>`); a suppression\n     without one cannot be audited.\nMISLEADS the reason is the text after the directive on the same line;\n     a reason on the NEXT line is not associated and reads as absent;\n     eslint-disable comments are counted in the same column.",
	"ANSWERS declared dependencies no import in the tree references: dead\n     weight in install time and lockfile surface, or a module used only\n     through a global/plugin the importer cannot see.\nACT remove the dependency, or import it where it is actually used; a\n     dependency used only by a build script or a global side effect\n     shows as unused here -- check before deleting.\nMISLEADS matching is target-basename: `import x from 'lodash/merge'`\n     counts as using lodash; a dependency used only via a package\n     internal (no import statement) reads as unused; devDependencies\n     used only by scripts (no source import) are the dominant\n     legitimate row.",
	"ANSWERS functions that interpolate into template literals while also\n     touching `any`: the ${x} family that restrict-template-expressions\n     rejects, because an any-typed value can smuggle anything into a\n     DOM sink or a URL. Co-occurrence, not data flow.\nACT type the interpolated value (unknown + narrowing beats any); if the\n     value is genuinely untyped, String(x) with a comment.\nMISLEADS n_template_sub counts ALL ${} sites and n_any_total all any\n     references in the body -- the join is per-function co-occurrence,\n     so a function with ${x} on a well-typed value plus an unrelated\n     any param reads as a violation; a `String(x)` interpolation is not\n     distinguished.",
	"ANSWERS the exported contracts whose members are all mutable: every\n     consumer can mutate the shape, so a change to any member ripples\n     as a behavioral change, not a type error. The biggest member\n     counts are the widest blast radii.\nACT mark members readonly; preferReadonly makes the compiler enforce\n     the discipline going forward.\nMISLEADS n_readonly_members counts members whose declaration line starts\n     with `readonly` -- an index signature or a type alias member is\n     not counted as readonly; a deliberately mutable DTO (form input,\n     draft state) is the legitimate row.",
	"ANSWERS the layer crossings in the conventional UI stack: a component\n     file importing a data-access module. The fix is the same as in\n     every layering rule -- route through an interface -- but the\n     directory convention is the cheapest detector there is.\nACT move the data access behind a hook/port, or accept the crossing\n     deliberately and say why in a comment.\nMISLEADS pure directory-name convention: a `pages/` dir that is not a\n     UI layer (e.g. a pagination module) misreads, and a `db/` helper\n     that is really a pure utility is flagged; a crossing through a\n     barrel (ui/ importing api/index) is matched on the barrel's dir.",
	"ANSWERS every function that crosses into a child process -- the places\n     a string becomes a command line.\nACT pass argument arrays (execFile/spawn args), never a shell string;\n     an allowlisted or constant command is the safe row.\nMISLEADS the capture is the qualified call text only: child_process.exec,\n     child_process.execSync, child_process.spawnSync. A destructured\n     `const {exec} = require('child_process')` call, and spawn/execFile/\n     fork (including child_process.spawn), are invisible to it. Argument\n     literalness is not captured -- a constant command ranks the same as\n     a tainted one.",
	"ANSWERS functions that assign location.href / window.location AND read\n     request input (req.query / req.params / req.headers) -- the shape of\n     a client-side open redirect: location.href = req.query.next.\nACT validate the target against an allowlist; never forward a\n     user-supplied URL.\nMISLEADS same-function co-occurrence is NOT data flow -- the input value\n     may never reach the assignment, and a constant redirect beside an\n     unrelated input read reads as a violation. The assignment target is\n     matched textually (location.href / window.location); location.assign\n     and location.replace calls are not captured; a wrapper around the\n     sink is invisible to it.",
	"ANSWERS functions that fetch a URL (fetch, axios, got, superagent, http.request) AND read request input -- the shape of server-side request forgery: fetch(req.query.url).\nACT validate the URL scheme and host against an allowlist; never fetch a\n     user-supplied URL.\nMISLEADS same-function co-occurrence is NOT data flow -- the input value\n     may never reach the fetch, and a constant URL beside an unrelated\n     input read reads as a violation. The capture is the dotted call\n     text: an http client assigned to a variable and used via c.get is\n     invisible; a wrapper around fetch is too.",
	"ANSWERS string literals at least 12 chars long whose text names a\n     credential (password, token, api_key, secret, bearer, jwt, ...) --\n     the literal that a committed secret looks like.\nACT rotate and move to a secret manager; never commit the literal.\nMISLEADS a format string or test fixture containing the WORD token/pass\n     reads as a candidate (the filter is the literal's own text, not its\n     use); values over 200 chars are truncated at capture; a secret\n     interpolated into a template string is invisible; a secret built\n     from parts or read from an env var is invisible here. This is a\n     candidate list, not a verdict.",
	"ANSWERS functions that call fs.readFile/writeFile with a variable path\n     AND read request input -- the shape of path traversal:\n     fs.readFile(req.query.f).\nACT validate the resolved path stays under a configured root; use\n     path.resolve and a prefix check.\nMISLEADS same-function co-occurrence is NOT data flow -- the input value\n     may never reach the read, and a constant-read beside an unrelated\n     input read reads as a violation. The path is not analyzed: a\n     variable path is assumed suspicious, a literal is not; a\n     destructured fs import is invisible to the fs. capture.",
	"ANSWERS functions that write a file whose data argument is req.files /\n     req.file -- the shape of an unchecked upload: fs.writeFile(dst,\n     req.files.f.data).\nACT check extension, MIME and size against an allowlist before saving;\n     store outside the web root.\nMISLEADS the writeFile data argument is matched textually -- an upload\n     assigned to a local before the write is invisible; multer\n     middleware configuration is not captured at all; the size/type\n     check is not modeled, so a checked write ranks the same as an\n     unchecked one.",
	"ANSWERS functions that touch archive libraries (unzipper, adm-zip,\n     jszip, yauzl) -- the surface where an entry name becomes a\n     filesystem path.\nACT validate every entry name against a containment check before\n     extraction; reject ../ and absolute paths.\nMISLEADS the containment check is not modeled: a function that checks\n     each name before extraction ranks the same as one that does not.\n     The capture needs zip/unzip in the call text, so a renamed\n     extraction helper is invisible.",
	"ANSWERS functions that call Object.assign AND read request input -- the\n     shape of mass assignment: Object.assign(user, req.body).\nACT whitelist the fields you accept; never assign a request body whole.\nMISLEADS same-function co-occurrence is NOT data flow -- the assigned\n     source may not be request input, and a constant object beside an\n     unrelated input read reads as a violation. The spread shape\n     {...req.body} is invisible to the Object.assign capture; a\n     per-field whitelist elsewhere in the function is not modeled.",
	"ANSWERS functions that call a logger level method (logger.info,\n     winston/pino) AND read request input -- the shape of log forging:\n     logger.info(req.headers['user-agent']).\nACT sanitize newlines and control characters in log messages; never log\n     raw request input.\nMISLEADS same-function co-occurrence is NOT data flow -- the input value\n     may never reach the log call, and a constant message beside an\n     unrelated input read reads as a violation. The capture needs the\n     word logger in the call text, so a differently-named logger is\n     invisible.",
	"ANSWERS functions that call console.log/info/warn/error AND read request\n     input -- the shape of request data (tokens, bodies) ending up in\n     stdout logs: console.log(req.headers.authorization).\nACT route through a structured logger with redaction; never console-log\n     raw request input.\nMISLEADS same-function co-occurrence is NOT data flow -- the input value\n     may never reach the console call, and a constant message beside an\n     unrelated input read reads as a violation. The capture is the\n     dotted console. call; a destructured console alias is invisible.",
	"ANSWERS functions that read request input and contain NO auth-family\n     call (passport, isAuthenticated, jwt, login) -- the surface where\n     a handler may be missing its authorization check.\nACT add the auth middleware call; verify the route is in the protected\n     group.\nMISLEADS auth usually lives in MIDDLEWARE or a router guard -- this\n     query sees the handler only, so a fully-protected app still ranks\n     every handler as open. A login or public endpoint legitimately has\n     no auth. The markers are name-based substrings, so a wrapper\n     around the auth call is invisible and counts as open.",
	"ANSWERS the transitive floating promise. typescript-eslint's\n     no-floating-promises sees one statement; the graph sees the chain:\n     a SYNC caller cannot await, so every promise it receives is floated,\n     returned, or dropped -- and its callers inherit the same three\n     choices one hop further out.\nACT await it, return it, or attach a .catch -- at whichever call site is\n     closest to the entry point. caller_awaits=0 rows inside an async fn\n     are the same defect one indentation in.\nMISLEADS `return asyncCall()` from a sync function is CORRECT and is\n     the dominant false positive here -- check caller_returns before\n     acting. Top-level (module-scope) rows are import-time side effects,\n     a different decision, not a dropped promise.",
	"ANSWERS which async functions have NO path to a await anywhere above\n     them: every caller is sync or never awaits itself. One rejection\n     from these becomes an unhandledRejection -- fatal on Node 15+.\nACT make the boundary explicit: return the promise, or document the\n     fire-and-forget contract with `void` and a .catch inside.\nMISLEADS a caller that returns the async call passes the duty upward\n     and still counts as non-awaiting here; name-based resolution may\n     also credit callers to the wrong same-named overload. Read with\n     sync-caller-of-async, which shows the individual sites.",
	"ANSWERS the cross-file half of no-misused-promises checksVoidReturn:\n     an async function handed to forEach, on, setTimeout or a factory\n     in ANOTHER file, where the signature says void. The promise is\n     dropped by construction -- the receiver never sees it.\nACT wrap the body, or give the parameter an explicit Promise-returning\n     type so the caller cannot pass async silently.\nMISLEADS counted per enclosing function, per async argument -- this\n     is co-occurrence, not the call edge: a `.map(async ...)` whose\n     results ARE consumed by Promise.all is correct and appears here.\n     The receiver's signature is not type-checked, only the shape seen.",
	"ANSWERS the registration sites no-misused-promises checksVoidReturn\n     names explicitly (event handlers): `.on('x', async (e) => ...)`.\n     A listener's return value is discarded by the emitter, so one\n     throw inside the callback is an unhandled rejection, not an error\n     path.\nACT catch inside the callback and route to the error channel, or emit\n     an 'error' event.\nMISLEADS `once` rows fire a bounded number of times, and a listener on\n     an object that dies with the request is a smaller blast radius than\n     a global emitter -- the target column tells you which. Adds only\n     are the finding; removes cannot be async here.",
	"ANSWERS the no-async-promise-executor defect in the wild: an async\n     executor means a thrown error becomes a REJECTED PROMISE nobody\n     holds, while the outer promise waits forever.\nACT make the executor synchronous; do the async work after, or wrap in\n     try/catch and call reject explicitly.\nMISLEADS ranked per enclosing function; a function with several\n     executors lists once. A wrapped executor whose body never throws\n     is a false positive this cannot distinguish.",
	"ANSWERS `await f()` where f is declared `: void` (typescript-eslint\n     no-confusing-void-expression / await-thenable territory) or a\n     plain value: the await either hides a missing Promise return type\n     or silently does nothing while claiming asynchrony to readers.\nACT fix the signature -- if f is really async, declare Promise<T>; if\n     it is really sync, drop the await.\nMISLEADS resolution is by callee BASE NAME, so a same-named thenable\n     method elsewhere clears the row entirely (names are matched\n     against ALL candidates and thenable ones are excluded first);\n     `await x` of a non-call value is not captured at all.",
	"ANSWERS constructors that kick off promises (loading, IO, network) at\n     instantiation: the caller gets a fully-typed object whose state is\n     still being filled in behind its back. SonarTS and the C# and\n     Swift guidelines all ban the shape; no TS linter sees it across\n     files.\nACT return an `async init()` or a static factory the caller awaits;\n     keep the constructor to assignments only.\nMISLEADS a constructor calling an async method it does NOT depend on\n     (fire-and-forget telemetry, deliberately void) reads the same as\n     one whose initialisation races its first use -- read what the ctor\n     does with the result, which this does not model.",
	"ANSWERS the longer cycles import-cycles misses by construction: a ->\n     b -> c -> a. At module load one file necessarily wins and the rest\n     read a partly-initialised import -- order-dependent, and it\n     flips with a seemingly harmless refactor.\nACT break at the weakest edge: move the shared constant/type to a leaf\n     module, or make the return edge `import type` (type-only cycles\n     are erased and harmless).\nMISLEADS depth is capped at 5 hops, so a 6-file cycle is invisible;\n     each cycle is listed once per ROTATION (a->b->c->a and b->c->a->b\n     are separate rows), so fix one edge, not N rows; unresolved\n     (bare-package) targets are excluded.",
	"ANSWERS the unhandled-rejection surface: every async function that\n     awaits, never catches (no try, no .then/.catch chain), and is\n     called by someone. Since Node 15 an unhandled rejection CRASHES\n     the process -- the caller inherits that, which is what fan_in\n     measures here.\nACT try/catch around the awaits, or make failure a returned\n     Result/Either so callers must handle it.\nMISLEADS a CALLER may wrap the call in its own try/catch -- this sees\n     the callee only, so a fully-guarded call still ranks; a top-level\n    `.catch` registration is not attributed to the callee either.",
	"ANSWERS the vscode/Playwright lifetime contract: a function whose\n     return type is a Disposable*, paired against each caller's body --\n     callers with zero dispose/unsubscribe/remove calls are holding a\n     resource with no owner.\nACT store into a DisposableStore, add to the component's cleanup\n     collection, or hand the handle to whoever outlives the value.\nMISLEADS the dispose may happen on a wrapper object the caller passes\n     the handle into (a store argument) and reads as missing here;\n     matching is by the factory's declared return type text, so a\n     union like `T | Disposable` counts and a bare `any` does not.",
	"ANSWERS the NestJS validation gap: a method whose parameter type is a\n     class carrying NO decorators at all -- no class-validator, no\n     @ApiProperty, nothing -- while the method does IO. Under a\n     ValidationPipe without `whitelist`/`forbidNonWhitelisted` (or with\n     no pipe), every field of that shape reaches the database as sent.\nACT decorate and validate the DTO, or `whitelist: true` the global\n     pipe; never persist a shape nobody constrained.\nMISLEADS 'no decorators' is the proxy for 'not validated': a DTO\n     validated by hand inside the method, or by an external schema\n     (zod), is undecorated and correct -- read the method before\n     acting. Interface-typed params match same-named interfaces only.",
	"ANSWERS the shared-instance state hazard behind NestJS injection\n     scopes: a class holding MUTABLE fields while its methods read\n     req.* is writing per-request data into memory every concurrent\n     request shares. A request-scoped provider injected into a\n     singleton has exactly this footprint.\nACT make the state a local, or scope the provider to the request; if\n     the field is a cache, make the write idempotent and say why.\nMISLEADS co-occurrence at class grain, not data flow: the mutable\n     field may be unrelated to the input read (a logger, a config\n     handle); an immutable-by-convention field declared without\n     readonly counts as mutable here.",
	"ANSWERS which unsound spots the graph actually REACHES: min hops from\n     an exported/handler entry to a function carrying `as any`, a\n     non-null `!`, or a suppression. assertion-density ranks the spots;\n     this ranks the paths -- a hole nobody can reach is a note, a hole\n     under the API is a defect.\nACT narrow the type at the highest-ranked row first: every hop is a\n     caller that trusted the lie.\nMISLEADS depth is bounded at 4 hops, so deeper paths are missed and\n     the hop count is a floor; reaching an unsound function is not\n     proof a bad VALUE flows in -- only that the door is on the path.",
	"ANSWERS the methods decorators register with a framework -- route\n     handlers, subscribers, cron jobs, CLI commands -- that NOTHING in\n     the tree calls. For NestJS/TypeGraphQL the framework is the\n     caller and the row is fine; the same shape with a misspelled\n     decorator or a moved route is a silently dead endpoint.\nACT verify the registration: does the route/subscription appear in the\n     running app? Then either fix the registration or delete the\n     method -- both outcomes are wins.\nMISLEADS zero RESOLVED callers is normal for framework-registered\n     code, so on a decorator-heavy repo this is an audit list, not a\n     defect list; decorators captured are only those sitting directly\n     on the method or its export wrapper.",
	"ANSWERS the accessor pairs typescript-eslint related-getter-setter-pairs\n     asks about: `get x()` without `set x()` in the same class means\n     assignment to .x is a silent TypeError in strict mode or a no-op --\n     a consumer writing obj.x = v compiles and does nothing.\nACT add the setter, or expose an explicit method so intent is visible;\n     readonly-intent belongs in the type, not the missing half.\nMISLEADS deliberate read-only accessors are the dominant row -- pair\n    it with how often the property is ASSIGNED elsewhere, which this\n    does not count; subclasses adding the missing half are not joined\n    (per-class grain only).",
	"ANSWERS accessors whose body awaits, hits the network, fs or DOM.\n     Property syntax promises a cheap field read; an async body hides\n     a request inside `obj.x` -- uncacheable, unawaitable, and\n     re-fired on every access (TC39 rejected async getters for\n     exactly this reason).\nACT make it a method (`getXAsync`) or cache the value; a getter must\n    be safe to read twice for free.\nMISLEADS a getter over a memoised field does IO-looking things once\n    and is fine; the counts are per body, so a thin getter delegating\n    to a heavy helper is invisible here.",
	"ANSWERS `async` signatures that never suspend: the function wraps its\n    result in a promise anyway, so EVERY caller's await is a real\n    microtask hop and `Promise.all` batching looks cheaper than it is.\n    Ranked by callers because that is who pays for the lie.\nACT drop the async keyword, or add the await that justifies it.\nMISLEADS async-on-interface-implementation is load bearing (removing\n    it changes the returned type for polymorphic callers) and reads as\n    a false positive here; a function that RETURNS a promise without\n    awaiting it is correct and also appears.",
	"ANSWERS the promise-chain style's unhandled-rejection twin: a body\n    with .then calls and no try/catch and no .catch -- the chain's\n    rejection path falls on the floor exactly where no-floating-promises\n    stops looking (the chain is not floating, just unguarded).\nACT end the chain with .catch, or migrate the flow to try/await/catch\n    so the error path is syntax rather than discipline.\nMISLEADS the .catch may be attached by a CALLER to the returned chain\n    -- correct, and counted here; a .finally-only chain reads the same\n    as a caught one to this query.",
	"ANSWERS chains whose RESULT dies in the function: .then(...) built,\n    function's return type void/none, callers waiting on nothing. The\n    no-confusing-void-expression family: whoever wrote the caller\n    cannot tell the work is asynchronous or failing.\nACT return the chain (Promise<T>), or void it explicitly at the call\n    site with a comment saying who owns the error.\nMISLEADS a deliberate fire-and-forget chain with an internal .catch is\n    a legitimate row; return types are the DECLARED annotation, so an\n    inferred-Promise function with no annotation reads as void.",
	"ANSWERS handlers (is_handler) that await INSIDE the handler with zero\n    try blocks: every rejection takes the framework's default error\n    path, leaking stack traces or killing the response. Ranked by\n    awaits -- each one is another failure mode.\nACT wrap the awaits, or mount an exception filter/error middleware so\n    the default path is deliberate; validate input before the first\n    await.\nMISLEADS a global error filter makes the raw shape SAFE (still\n    flagged); a handler delegating to an already-guarded service has\n    its awaits here while the try lives one hop away.",
	"ANSWERS setTimeout/setInterval given an async arrow: the timer owner\n    cannot observe the returned promise, so one rejection inside the\n    callback is an unhandledRejection (process-fatal on Node 15+) and\n    an interval fires it REPEATEDLY.\nACT .catch inside the callback; for intervals, add backoff and a\n    failure counter so a permanently-failing job is visible.\nMISLEADS per-function co-occurrence, not per-call: a function that\n    starts timers AND separately passes async arrows elsewhere reads\n    as one; a synchronous callback that merely awaits nowhere is not\n    counted (it has no async keyword).",
	"ANSWERS methods declared `override` whose body contains no super call\n    (typescript-eslint strict-override territory at cross-file range):\n    the author promised to extend the base behaviour -- either the\n    override silently REPLACES it (dropped teardown, dropped\n    validation) or the keyword is a lie.\nACT call super.method() at the right point, or drop the override\n    keyword if the contract is genuinely replaced.\nMISLEADS an override that is a full reimplementation is sometimes the\n    point (template-method hook) and is the dominant row on hook-heavy\n    bases; super calls routed through a wrapper are not counted.",
	"ANSWERS class-grain mutual dependency: methods of A call methods of B\n    AND methods of B call methods of A. This is the shape NestJS\n    documents as a circular provider dependency (fix with forwardRef\n    or, better, extract a third service) -- invisible to file-level\n    cycle queries when the classes share a file or import one-way.\nACT extract the shared responsibility into a third service both\n    depend on; events or an interface break the construction cycle.\nMISLEADS edges are name-resolved, so same-named methods on different\n    classes can forge or miss an edge; `new B()` inside A is a dynamic\n    call this parser does not attribute at all, so constructor-injection\n    cycles can hide; a 3-class cycle (A->B->C->A) is not reported.",
	"ANSWERS bodies using BOTH async styles: part of the flow is awaited,\n    part chained. The two error paths differ (.catch vs try/catch),\n    ordering is hard to see, and refactors routinely orphan one half --\n    the exact maintenance hazard the style guides warn about.\nACT convert the chain to try/await (or the reverse) so the whole flow\n    has one error path.\nMISLEADS a .then on a NON-promise (mapping an array) or a helper's\n    internal chain both count; the query sees style mixing, not a\n    broken data path -- read the body before judging.",
	"ANSWERS the async-void trap: a signature that says fire-and-forget on\n    an async body. Callers who trust the type write `doIt()` and every\n    rejection is unhandled; callers who await get void and a false\n    sense of sequencing -- the await ends when the FIRST await inside\n    suspends, not when the work completes.\nACT declare Promise<void> (or a Result) and let callers choose; keep\n    genuinely detached work behind an explicit `void doIt()` with a\n    .catch inside.\nMISLEADS event-handler-shaped methods (onClick(): void) that are async\n    by necessity in some frameworks are the dominant row; a `: void`\n    annotation that tsc itself would flag on an async fn means the\n    body may not actually be async -- check is_async semantics.",
	"ANSWERS the FutInVec shape: Promise.all (or race/allSettled) INSIDE a\n    loop body, so each iteration multiplies the fan-out -- n\n    iterations x k args concurrent sockets/queries, and one rejection\n    from any of them fails the iteration while the rest keep running.\nACT hoist the array out and call Promise.all ONCE over the mapped\n    promises; batch with p-limit/pool when n is genuinely large.\nMISLEADS loop_depth is textual: a Promise.all inside a callback that\n    runs once reads as in-loop, and an intentionally rate-limited\n    sequential loop the author already bounded looks the same as an\n    accident -- n_promise_all in the row tells you the total count.",
	"ANSWERS module-scope code that fetches, reads files, shells out or\n    starts timers at IMPORT time: every importer pays the latency on\n    its critical path, ordering between modules becomes load order,\n    and test imports trigger production side effects.\nACT move it behind an explicit init() the entry point calls; keep\n    module scope to constants and wiring.\nMISLEADS top-level event-listener REGISTRATION and DI container setup\n    look like IO families only when a call text matches, so a wiring\n    module can be flagged; the module symbol aggregates ALL top-level\n    statements in the file, not one line.",
	"ANSWERS handlers whose request object is `any`/untyped: every field\n    access compiles, so typos and attacker-controlled keys reach\n    runtime unchecked -- the DTO-validation gap at its widest. The\n    input_reads column is how much request surface actually flows\n    through.\nACT type the request (Express Request, FastifyRequest) or better a\n    validated DTO; then `noUncheckedIndexedAccess` does the rest.\nMISLEADS is_handler is a heuristic (req/res-ish parameter names), so\n    a non-HTTP function with any params can appear; a handler typed\n    `any` once and re-narrowed immediately still counts.",
	"ANSWERS long .then chains: each link is a scope boundary (no early\n    return, no breakpoint stepping), errors travel invisibly to the\n    tail, and intermediate results cannot be typed without generics --\n    the readability cliff SonarJS flags as cognitive complexity.\nACT convert to async/await with try/catch, or split each link into a\n    named function so the chain reads as a pipeline.\nMISLEADS count is per function, so a well-factored pipeline of\n    named links reads as deep as a copy-pasted chain; .then callbacks\n    that are pure synchronous transforms carry none of the risk and\n    are counted the same.",
}

var mTitles = [29]string{
	"Read this first: where the call graph cannot see",
	"Barrel files: how much gets pulled in per import",
	"Which directories opted out of which strict flags",
	"Types deep enough to slow the compiler down",
	"Interfaces and types carrying `any` or an index signature",
	"Exported and never imported anywhere in this tree",
	"Config and syntax TypeScript 7 no longer accepts",
	"Functions doing too much, by every measure at once",
	"Review order: if you can only read N functions this week, which N",
	"Where one fix pays back many times: highest fan-in",
	"Which modules depend on which, and how unstable that makes them",
	"TODO, FIXME, HACK and BUG, weighted by the code they sit in",
	"What this run could not read",
	"Conditional and mapped types deep enough to cost compile time",
	"Index signatures and unknown, where excess-property checking stops applying",
	"Ambient .d.ts declarations, and whether an implementation exists in this tree",
	"Functions with excessive nesting depth (eslint max-depth)",
	"Functions with too many parameters (eslint max-params)",
	"A function called from many different modules (shotgun surgery)",
	"Where the async frontier is: promise machinery per module",
	"Unsoundness per module: any, as-any, ! and suppressions per KLOC",
	"Entry surface per module: handlers, request reads, sinks, auth checks",
	"How much code hangs off each module's entry points (transitive, 6 hops)",
	"Highest-risk functions no test tree ever calls",
	"Generic instantiation load: type arguments times call sites",
	"Handlers by serialized IO: where request latency is spent",
	"Constructors doing branchy or IO work -- DI and testability debt",
	"How much of a module is decorator-registered (framework-owned) code",
	"Where errors are thrown, caught, swallowed -- module by module",
}

var mNotes = [29]string{
	"ANSWERS how much of every other answer here is guesswork.\nACT external calls leave the tree by design and are NOT blindness.\n     Unresolved means we lost it -- usually a method on a value whose type\n     only the type checker knows. This tool reads syntax, not types.\nMISLEADS a type-only module legitimately has almost no edges, and that is\n     not blindness either. Read `types` next to `fns` before judging.",
	"ANSWERS the build-time cost nobody measures. `export * from './x'` means\n     importing ONE symbol from the barrel makes the compiler and the\n     bundler load every module it re-exports, transitively.\nACT import from the defining module directly, or replace `export *` with\n     explicit named re-exports so tree-shaking can work.\nMISLEADS a barrel in a package's public entry point is deliberate API\n     design and is correct. The cost only bites on INTERNAL barrels that\n     the package's own modules import from.",
	"ANSWERS whether `strict: true` at the root actually holds everywhere.\nACT a nested tsconfig that extends the root and turns strictNullChecks\n     back off is where the null bugs live. `removed_option` flags settings\n     TypeScript 7 no longer accepts at all -- those are build breaks, not\n     style.\nMISLEADS this reads the config, not the code. A directory with strict off\n     and no `any` in it is fine; cross-reference with `any-blast-radius`.",
	"ANSWERS which declarations make `tsc` crawl. Conditional-type recursion\n     and deep generic instantiation are the documented cause of quadratic\n     compile time, and past a limit the compiler gives up entirely with\n     'type instantiation is excessively deep and possibly infinite'.\nACT flatten with a named intermediate type, or add an explicit depth\n     counter to bound the recursion.\nMISLEADS depth is a syntactic bracket count plus conditional nesting. It\n     is a proxy for instantiation cost, not a measurement of it. Only\n     `tsc --extendedDiagnostics` settles which type is actually slow.",
	"ANSWERS which shared shapes give up checking for everyone who uses them.\nACT an index signature (`[k: string]: any`) makes every property access\n     legal, including typos. Narrow it to a union of known keys, or use\n     Record with a concrete value type.\nMISLEADS an index signature is the correct model for a genuine dictionary\n     and for JSON-shaped data. The `n_members` column separates a real\n     interface with one escape hatch from a shape that is all escape.",
	"ANSWERS what the public surface carries that nothing here uses.\nACT if this is an application, delete it. If it is a library, this is\n     your published API and the query is telling you its size, not that\n     it is dead.\nMISLEADS THIS IS THE QUERY MOST LIKELY TO BE WRONG. A consumer outside\n     the tree, a barrel re-export, a dynamic import, or a string-keyed\n     registry all make an export live and invisible here. Check\n     `barrel-blast` and `graph-blindspots` before deleting anything.",
	"ANSWERS what will fail to build on an upgrade, before you attempt it.\nACT `baseUrl`, `moduleResolution: node10`, `module: amd|umd|system`,\n     `target: es5` and `downlevelIteration` are GONE in 7.0, not\n     deprecated. Fix these first; they are hard build breaks.\nMISLEADS this reads config only. `erasableSyntaxOnly` additionally bans\n     enums, runtime namespaces and parameter properties -- the enum and\n     namespace counts below tell you how much work that flag would be,\n     but it is opt-in and not required by 7.0 itself.",
	"ANSWERS which functions are hardest to hold in your head.\nACT split by responsibility. n_elif distinguishes a flat dispatch (extract\n     a lookup) from real nesting (extract functions).\nMISLEADS a long flat dispatch reads far more easily than a short deeply\n     nested one, which is why this sorts by cognitive, not sloc.",
	"ANSWERS which functions combine complexity with unsound typing and\n     dangerous operations.\nACT start at the top. The score weights eval, prototype pollution, `as\n     any` and @ts-ignore far above raw complexity.\nMISLEADS a heuristic, not a finding. Generated and vendored files are\n     excluded, so the real top of the list may be in code this hid.",
	"ANSWERS which functions the rest of the tree leans on hardest.\nACT a win in a high-fan-in leaf pays once per caller.\nMISLEADS fan_in counts STATIC call sites this parser could resolve, not\n     runtime frequency, and TypeScript resolution is name-based -- a\n     method on an interface-typed value is not attributed here.",
	"ANSWERS which modules are hard to change because everything leans on them.\nACT instability near 0 with high fan_in is a good place for stable\n     abstractions and a bad place for volatile logic.\nMISLEADS instability is a ratio, so a module with one edge each way scores\n     0.5 and means nothing. Read it next to n_files.",
	"ANSWERS which unfinished business sits where it matters.\nACT a FIXME in a function forty things depend on outranks a TODO in a\n     build script.\nMISLEADS marker age is invisible -- git blame is the missing column.",
	"ANSWERS whether the numbers above cover the code you think they cover.\nACT a file here contributed less than it should have.\nMISLEADS tree-sitter-typescript 0.23.2 was released 2024-11-11 and is\n     over a year behind the language. It does not accept `export type {X}\n     from './y'` in every position, and some `.d.ts` default-export forms\n     that tsc accepts. Errors here are usually the GRAMMAR being stale,\n     not the code being wrong -- check the file by hand before believing\n     it is broken.",
	"ANSWERS which types are programs. Deeply nested conditional types with\n     `infer` are evaluated by the compiler on every check, and past a\n     certain depth they dominate build time or hit the instantiation\n     limit outright -- the error nobody can read.\nACT flatten the conditional chain, or precompute the result as a named\n     type alias so it is instantiated once instead of at every use.\n     Measure with `tsc --diagnostics` before and after.\nMISLEADS depth is structural, not a cost model. A depth-6 type used\n     twice is free; a depth-3 type instantiated in a hot generic is not.\n     This finds candidates for the profiler, not verdicts.",
	"ANSWERS which types accept anything. An index signature makes every\n     property name legal, so a typo in a key is not a type error -- and\n     under `noUncheckedIndexedAccess` every read is silently possibly\n     undefined, which most codebases do not have switched on.\nACT use Record with a union of the known keys, or a Map when keys are\n     genuinely open. `unknown` is the right escape hatch where `any`\n     was reached for, because it forces narrowing at the point of use.\nMISLEADS an index signature on a genuine dictionary is exactly correct\n     and appears here. The rows worth reading are exported types where\n     callers will rely on the shape.",
	"ANSWERS which part of the public surface is a promise rather than code.\n     A `.d.ts` describes something the compiler will trust absolutely\n     and never verify -- if it drifts from the JavaScript it describes,\n     every caller type-checks against a fiction.\nACT generate declarations from the source with `declaration: true`\n     rather than hand-writing them. Where they must be hand-written --\n     describing a JS dependency -- pin the version they were written\n     against, because nothing else will catch the drift.\nMISLEADS a type-only package is ALL declarations by design and tops this\n     list correctly. fan_in of zero on a declaration means nothing in\n     THIS tree uses it, not that it is dead.",
	"ANSWERS where a function has max_nesting > 4.\nACT extract nested blocks; use early returns.\nMISLEADS TS structural nesting includes callbacks and conditionals.",
	"ANSWERS where a function has more than 4 parameters.\nACT use an options object or split the function.\nMISLEADS a destructured options parameter is one param semantically.",
	"ANSWERS which functions are called from many distinct modules.\nACT consider splitting or stabilizing the contract.\nMISLEADS a utility function is called from everywhere and is stable.",
	"ANSWERS which modules live on promises: async share, awaits, .then\n    chains, Promise.all sites, floating-promise counters and async\n    callback arguments -- the shape of a module's concurrency style\n    before reading a line of it.\nACT modules high on then_chains against the grain of the codebase are\n    migration candidates (async/await); high async_callbacks means\n    void-expecting receivers, cross-check async-callback-argument.\nMISLEADS counts are syntactic, so a module wrapping async helpers\n    without doing IO itself reads as async-heavy; modules with zero\n    async functions are excluded from the ranking entirely, not\n    shown as zero.",
	"ANSWERS where the type system has been switched off, normalized by\n    module size -- `any` counts alone punish big modules; per KLOC\n    ranks the DENSITY of escape hatches.\nACT a high unsound_per_kloc module is where strict-mode migration\n    pays first, and where runtime type validation (zod/valibot) is\n    most likely already missing.\nMISLEADS a module wrapping an untyped third-party API is unsound ON\n    PURPOSE at a boundary and still tops the list; declaration files\n    (.d.ts) with any are interop seams, and type-heavy modules have\n    tiny sloc so the ratio swings.",
	"ANSWERS which modules touch the outside world: request handlers,\n    req.* reads, fetch/fs/exec sinks, console logging, and how many\n    auth-family calls sit nearby -- the triage map for a security\n    review.\nACT review in order: high input_reads with low auth_calls is where a\n    missing guard costs most; cross-reference the OWASP surface\n    queries for the specific sinks.\nMISLEADS is_handler and input-site capture are name-heuristics\n    (req/res/request/ctx), so an SDK module with `ctx` params can\n    inflate the surface; auth middleware lives OUTSIDE these\n    functions, so auth_calls=0 does not mean unprotected.",
	"ANSWERS the blast radius of a signature change: per module, how many\n    entry points (exported/handlers) there are and how many symbols\n    are transitively reachable from them. A module with 5 entries and\n    900 reachable symbols breaks 900 call sites when an entry\n    contract moves.\nACT high reach with many entries is where an explicit internal API\n    (one exported facade, rest private) buys the most stability.\nMISLEADS depth is capped at 6 hops, so reach is a floor that\n    undercounts deep trees; entries include every exported symbol,\n    and barrel re-exports make library modules look enormous by\n    design.",
	"ANSWERS where the risk ranking and the test absence intersect: every\n    function with risk_score > 0 whose callers (transitively none)\n    include nothing from a test file -- the review list for 'has\n    anyone ever exercised this failure mode?'.\nACT write the test for the top rows first; risk here weights exec,\n    ts-ignore, as-any and blocking calls, which is exactly what a\n    regression test should pin.\nMISLEADS only DIRECT callers are checked -- a function called by an\n    untested helper that tests eventually reach still shows as\n    untested; exported library surface used outside the tree reads\n    the same as dead-untested.",
	"ANSWERS where the TS compiler does its busiest inference: functions\n    with many type parameters and many resolved call sites multiply\n    instantiations -- the TS performance handbook's first-order cost,\n    and the source of 'excessively deep' errors downstream.\nACT cap signature generics (concrete types or a base constraint);\n    measure with tsc --extendedDiagnostics before/after on the top\n    row.\nMISLEADS instantiation_load is call-site x declared-params, not the\n    compiler's real instantiation count (variance and conditional\n    types change that); n_type_args counts argument LISTS, so one\n    heavily-argued call equals many small ones.",
	"ANSWERS which handlers carry the most IO per request: awaits,\n    awaits-in-loop (x5 -- the sequential multiplier), network and fs\n    calls. The latency profile sync-under-handler draws for BLOCKING\n    calls, drawn here for the async ones that still cost users.\nACT the awaits_in_loop rows first: batching or caching there buys\n    real seconds; then coalesce independent awaits into Promise.all.\nMISLEADS counts are calls, not milliseconds -- one cached await and\n    one 3-second vendor call weigh the same; a handler delegating IO\n    to services shows only its direct calls, so read fan_out next to\n    the totals.",
	"ANSWERS constructors that branch, call out, or touch IO at\n    instantiation: every `new` in every test now needs the network,\n    and DI containers hide the cost until construction fails mid-app.\nACT assign fields and nothing else; move work to an init/factory the\n    composition root awaits, and take dependencies as parameters.\nMISLEADS field-initializer assignments count as calls at class grain\n    for some shapes, and a constructor over a pure config object can\n    pass the cyclomatic bar while doing nothing wrong; the n_io/n_net\n    columns are what make a row real.",
	"ANSWERS the share of methods whose behaviour is wired by decorators --\n    routes, injections, subscriptions, cron. High-share modules have\n    control flow that only exists at runtime: the call graph shows a\n    skeleton, the framework fills the rest, and renames/relocations\n    fail silently in string-keyed decorators.\nACT keep decorator-heavy modules THIN: the decorated method should\n    delegate to decorated-free services that stay unit-testable and\n    graph-visible.\nMISLEADS decorators captured are only those directly on the method\n    (or its export wrapper): a framework registered in a module's\n    config file shows nothing here; fan_in=0 on decorated methods is\n    EXPECTED, so the zero-caller column is an audit hint, not a\n    defect count.",
	"ANSWERS the error-flow landscape: throws vs catches per module, with\n    broad and empty catches called out, plus async functions awaiting\n    with no try at all. Cross-module reads matter: a module that\n    throws heavily and catches nothing is delegating the error path\n    to its callers -- deliberately or not.\nACT for top-throwing modules, check every caller catches; for\n    broad/empty catches, narrow or log-and-rethrow.\nMISLEADS throws include validation raises meant to be caught one\n    frame up (control flow by exception is idiomatic in some stacks);\n    caught counts are per function body, so a central error middleware\n    makes every other module look unguarded.",
}

type cell struct {
	s     string
	isStr bool
	null  bool
	isF   bool
	fv    float64
}

func cs(s string) cell  { return cell{s: s, isStr: true} }
func ci(v int) cell     { return cell{s: strconv.Itoa(v)} }
func ci32(v int32) cell { return cell{s: strconv.Itoa(int(v))} }
func cl(v int64) cell   { return cell{s: strconv.FormatInt(v, 10)} }

func cb(v bool) cell {
	if v {
		return ci(1)
	}
	return ci(0)
}

func cf(v float64) cell {
	return cell{s: fmt.Sprintf("%.2f", v), isF: true, fv: v}
}

func cnull() cell { return cell{null: true} }

func (c cell) repr() string {
	if c.null {
		return ""
	}
	if c.isF {
		return cgFloat(c.fv)
	}
	return c.s
}

func (c cell) text() string {
	if c.null {
		return "-"
	}
	return c.s
}

type table struct {
	cols []string
	rows [][]cell
}

const maxCell = 72

func dispLen(s string) int { return utf8.RuneCountInString(s) }

func cutRunes(s string, n int) string {
	if dispLen(s) <= n {
		return s
	}
	i := 0
	for range n {
		_, sz := utf8.DecodeRuneInString(s[i:])
		i += sz
	}
	return s[:i]
}

func render(w *bufio.Writer, t *table) {
	if len(t.rows) == 0 {
		fmt.Fprintln(w, " (no rows)")
		return
	}
	body := make([][]string, len(t.rows))
	dw := make([][]int, len(t.rows))
	for i, r := range t.rows {
		body[i] = make([]string, len(r))
		dw[i] = make([]int, len(r))
		for j, c := range r {
			s := c.text()
			if c.isStr && !utf8.ValidString(s) {
				s = cgDecode([]byte(s))
			}
			if dispLen(s) > maxCell {
				s = cutRunes(s, maxCell-3) + "..."
			}
			body[i][j] = s
			dw[i][j] = dispLen(s)
		}
	}
	widths := make([]int, len(t.cols))
	for i := range t.cols {
		widths[i] = dispLen(t.cols[i])
		for _, r := range dw {
			if r[i] > widths[i] {
				widths[i] = r[i]
			}
		}
	}
	var b strings.Builder
	b.WriteByte(' ')
	for i, cname := range t.cols {
		if i > 0 {
			b.WriteByte(' ')
		}
		b.WriteString(cname)
		b.WriteString(strings.Repeat(" ", widths[i]-dispLen(cname)))
	}
	b.WriteByte('\n')
	b.WriteByte(' ')
	for i := range t.cols {
		if i > 0 {
			b.WriteByte(' ')
		}
		b.WriteString(strings.Repeat("-", widths[i]))
	}
	b.WriteByte('\n')
	for ri, r := range body {
		b.WriteByte(' ')
		for i, v := range r {
			if i > 0 {
				b.WriteByte(' ')
			}
			b.WriteString(v)
			b.WriteString(strings.Repeat(" ", widths[i]-dw[ri][i]))
		}
		b.WriteByte('\n')
	}
	w.WriteString(b.String())
}

func csvField(c cell) string {
	if c.null {
		return ""
	}
	s := c.repr()
	need := strings.ContainsAny(s, ",\"\r\n")
	if !need {
		return s
	}
	var b strings.Builder
	b.WriteByte('"')
	for i := 0; i < len(s); i++ {
		if s[i] == '"' {
			b.WriteByte('"')
		}
		b.WriteByte(s[i])
	}
	b.WriteByte('"')
	return b.String()
}

func writeCSV(w *bufio.Writer, t *table) {
	var b strings.Builder
	for i, cname := range t.cols {
		if i > 0 {
			b.WriteByte(',')
		}
		b.WriteString(csvField(cs(cname)))
	}
	b.WriteString("\r\n")
	for _, r := range t.rows {
		for i, c := range r {
			if i > 0 {
				b.WriteByte(',')
			}
			b.WriteString(csvField(c))
		}
		b.WriteString("\r\n")
	}
	w.WriteString(b.String())
}

func jsonString(b *strings.Builder, s string) {
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
				fmt.Fprintf(b, "\\u%04x", r)
			} else if r < 0x7f {
				b.WriteRune(r)
			} else if r <= 0xffff {
				fmt.Fprintf(b, "\\u%04x", r)
			} else {
				r -= 0x10000
				fmt.Fprintf(b, "\\u%04x%04x", 0xd800+(r>>10), 0xdc00+(r&0x3ff))
			}
		}
	}
	b.WriteByte('"')
}

func writeJSON(w *bufio.Writer, t *table) {
	var b strings.Builder
	if len(t.rows) == 0 {
		b.WriteString("[]")
		w.WriteString(b.String() + "\n")
		return
	}
	b.WriteString("[\n")
	for ri, r := range t.rows {
		b.WriteString("  {\n")
		for ci, c := range r {
			b.WriteString("    ")
			jsonString(&b, t.cols[ci])
			b.WriteString(": ")
			switch {
			case c.null:
				b.WriteString("null")
			case c.isStr:
				jsonString(&b, c.s)
			case c.isF:
				b.WriteString(cgFloat(c.fv))
			default:
				b.WriteString(c.s)
			}
			if ci < len(r)-1 {
				b.WriteByte(',')
			}
			b.WriteByte('\n')
		}
		b.WriteString("  }")
		if ri < len(t.rows)-1 {
			b.WriteByte(',')
		}
		b.WriteByte('\n')
	}
	b.WriteString("]\n")
	w.WriteString(b.String())
}

func printReport(g *Graph) {
	o := bufio.NewWriter(os.Stdout)
	defer o.Flush()
	bar := strings.Repeat("=", 78)
	dash := strings.Repeat("-", 78)
	fmt.Fprintf(o, "\n%s\nOVERVIEW\n%s\n", bar, dash)
	for _, k := range []string{"lang", "target", "root"} {
		if v := g.metaOf(k); v != "" {
			fmt.Fprintf(o, " %-14s %s\n", k, v)
		}
	}
	fmt.Fprintf(o, " %-14s %d catalogued, %d parsed, %d sloc\n", "files",
		len(g.Files), g.countParsed(), g.totalSloc())
	fmt.Fprintf(o, " %-14s %s\n", "symbols", g.kindSummary())
	fmt.Fprintf(o, " %-14s %d edges, %d call sites, %d unresolved\n", "call graph",
		len(g.Edges), len(g.Callsites), g.totalUnresolved())

	fmt.Fprintf(o, "\n%s\nHOW MUCH OF THIS TO TRUST\n%s\n", bar, dash)
	errFiles := 0
	for i := range g.Files {
		if g.Files[i].NErrs > 0 {
			errFiles++
		}
	}
	if g.countParsed() == 0 {
		fmt.Fprintln(o, " NOTHING WAS PARSED. Every number below is zero because no file")
		fmt.Fprintln(o, " was read, not because this repository is empty or clean.")
	}
	fmt.Fprintf(o, " %-30s %d file(s)\n", "files with parse errors", errFiles)
	if tot := g.totalCalls(); tot > 0 {
		un := int64(g.totalUnresolved())
		fmt.Fprintf(o, " %-30s %d of %d call sites (%d%%)\n",
			"calls we could NOT resolve", un, tot, 100*un/tot)
	} else {
		fmt.Fprintf(o, " %-30s no calls were recorded at all -- this is the absence of\n", "")
		fmt.Fprintf(o, " %-30s call resolution data, not a clean result\n", "")
	}
	fmt.Fprintln(o, " A high unresolved share means the call-graph queries below see less")
	fmt.Fprintln(o, " than they imply. `v_blindspot` lists exactly where.")

	fmt.Fprintf(o, "\n%s\nBIGGEST MODULES\n%s\n", bar, dash)
	mods := make([]int, 0, len(g.Modules))
	for i := range g.Modules {
		if g.Modules[i].NFiles > 0 {
			mods = append(mods, i)
		}
	}
	sort.SliceStable(mods, func(a, b int) bool {
		return g.Modules[mods[a]].Sloc > g.Modules[mods[b]].Sloc
	})
	if len(mods) > 12 {
		mods = mods[:12]
	}
	mt := &table{cols: []string{"name", "files", "sloc", "syms", "instab"}}
	for _, i := range mods {
		m := &g.Modules[i]
		mt.rows = append(mt.rows, []cell{cs(m.Name()), ci32(m.NFiles), ci32(m.Sloc),
			ci32(m.NSymbols), cf(m.Instability)})
	}
	render(o, mt)

	fmt.Fprintf(o, "\n%s\nHEAVIEST FUNCTIONS\n%s\n", bar, dash)
	render(o, g.fnTable("cyclomatic", 12))
	fmt.Fprintf(o, "\n%s\nMOST DEPENDED ON\n%s\n", bar, dash)
	render(o, g.fnTable("fan_in", 12))
	fmt.Fprintf(o, "\n%s\nMARKERS LEFT IN THE CODE\n%s\n", bar, dash)
	kindCount := map[string]int{}
	for _, m := range g.Markers {
		kindCount[m.Kind()]++
	}
	kinds := make([]string, 0, len(kindCount))
	for k := range kindCount {
		kinds = append(kinds, k)
	}
	sort.Slice(kinds, func(a, b int) bool {
		if kindCount[kinds[a]] != kindCount[kinds[b]] {
			return kindCount[kinds[a]] > kindCount[kinds[b]]
		}
		return kinds[a] < kinds[b]
	})
	mk := &table{cols: []string{"kind", "n"}}
	for _, k := range kinds {
		mk.rows = append(mk.rows, []cell{cs(k), ci(kindCount[k])})
	}
	render(o, mk)
}

func (g *Graph) fnTable(key string, n int) *table {

	files := make([]int, len(g.Files))
	for i := range files {
		files[i] = i
	}
	sort.Slice(files, func(a, b int) bool {
		return g.Files[files[a]].Path() < g.Files[files[b]].Path()
	})
	rank := make([]int32, len(g.Files)+1)
	for pos, fi := range files {
		rank[fi+1] = int32(pos)
	}
	order := make([]int32, 0, len(g.Symbols))
	for i := range g.Symbols {
		k := g.Symbols[i].Kind
		if k == kFunction || k == kMethod || k == kClosure {
			order = append(order, int32(i+1))
		}
	}

	sort.SliceStable(order, func(a, b int) bool {
		sa, sb := &g.Symbols[order[a]-1], &g.Symbols[order[b]-1]
		if ra, rb := rank[sa.FileID], rank[sb.FileID]; ra != rb {
			return ra < rb
		}
		return kindNames[sa.Kind] < kindNames[sb.Kind]
	})
	col := mCyclomatic
	if key == "fan_in" {
		col = mFanIn
	}

	sort.SliceStable(order, func(a, b int) bool {
		return g.mv(order[a], col) > g.mv(order[b], col)
	})
	if len(order) > n {
		order = order[:n]
	}
	if key == "fan_in" {
		t := &table{cols: []string{"name", "fan_in", "fan_out", "cyclo", "sloc", "at"}}
		for _, id := range order {
			s := &g.Symbols[id-1]
			m := g.metrics(id)
			t.rows = append(t.rows, []cell{cs(s.Name()), ci32(m[mFanIn]), ci32(m[mFanOut]),
				ci32(m[mCyclomatic]), ci32(m[mSloc]), cs(g.at(s))})
		}
		return t
	}
	t := &table{cols: []string{"name", "sloc", "cyclo", "cog", "nest", "fan_in", "at"}}
	for _, id := range order {
		s := &g.Symbols[id-1]
		m := g.metrics(id)
		t.rows = append(t.rows, []cell{cs(s.Name()), ci32(m[mSloc]), ci32(m[mCyclomatic]),
			ci32(m[mCognitive]), ci32(m[mMaxNesting]), ci32(m[mFanIn]), cs(g.at(s))})
	}
	return t
}

func (g *Graph) metaOf(k string) string {
	for _, m := range g.Meta {
		if m.K.Str() == k {
			return m.V.Str()
		}
	}
	return ""
}

func (g *Graph) countParsed() int {
	n := 0
	for i := range g.Files {
		if g.Files[i].Parsed {
			n++
		}
	}
	return n
}

func (g *Graph) totalSloc() int64 {
	var t int64
	for i := range g.Files {
		if g.Files[i].Parsed {
			t += int64(g.Files[i].Sloc)
		}
	}
	return t
}

func (g *Graph) totalCalls() int64 {
	var t int64
	for i := range g.Symbols {
		t += int64(g.metrics(int32(i + 1))[mNCalls])
	}
	return t
}

func (g *Graph) totalUnresolved() int {
	t := 0
	for i := range g.Unresolved {
		t += int(g.Unresolved[i].N)
	}
	return t
}

func (g *Graph) kindSummary() string {
	cnt := map[string]int{}
	for i := range g.Symbols {
		cnt[kindNames[g.Symbols[i].Kind]]++
	}
	type kv struct {
		k string
		v int
	}
	all := make([]kv, 0, len(cnt))
	for k, v := range cnt {
		all = append(all, kv{k, v})
	}
	sort.Slice(all, func(a, b int) bool {
		if all[a].v != all[b].v {
			return all[a].v > all[b].v
		}
		return all[a].k < all[b].k
	})
	if len(all) > 12 {
		all = all[:12]
	}
	parts := make([]string, len(all))
	for i, e := range all {
		parts[i] = e.k + "=" + strconv.Itoa(e.v)
	}
	return strings.Join(parts, ", ")
}

type fileNameKey struct {
	fid  int32
	name string
}

type typeNameKey struct {
	ty   string
	name string
}

type callerNameKey struct {
	caller int32
	name   string
}

type nameCand struct {
	sid, fid int32
	ty       string
}

type resolveStats struct {
	resolved, unresolved, external int32
}

func (g *Graph) resolveCalls(p *pending, imported map[int32]map[string]bool) resolveStats {

	unique := make(map[string]int32, len(g.byName))
	for n, c := range g.byName {
		if len(c) == 1 {
			unique[n] = c[0].sid
		}
	}
	fileScope := make(map[fileNameKey]int32, len(g.byName)*2)
	typeScope := make(map[typeNameKey]int32, len(g.byName))

	symLoc := make(map[int32]uint64, len(g.Symbols))

	for name, cands := range g.byName {
		for _, c := range cands {
			if _, ok := symLoc[c.sid]; !ok {
				symLoc[c.sid] = uint64(uint32(c.fid))<<32 |
					uint64(uint32(g.Files[c.fid-1].ModuleID))
			}
			k := fileNameKey{c.fid, name}
			if _, ok := fileScope[k]; !ok {
				fileScope[k] = c.sid
			}
			if c.ty != "" {
				ks := typeNameKey{c.ty, name}
				if _, ok := typeScope[ks]; !ok {
					typeScope[ks] = c.sid
				}
			}
		}
	}

	var st resolveStats
	extByCaller := make(map[int32]int32, 1024)
	edgeIdx := make(map[uint64]int32, len(p.Sid))
	sites := make(map[uint64]struct{}, len(p.Sid)/2+16)

	for i := range p.Sid {
		name := cgStrip(p.Name[i])
		if name == "" {
			continue
		}
		base := afterLastDot(name)
		if k := lastIndexByte(base, ':'); k >= 0 {
			base = base[k+1:]
		}
		var target int32
		if ty := p.Type[i]; ty != "" {
			target = typeScope[typeNameKey{ty, base}]
		}
		if target == 0 {
			target = g.byQual[name]
		}
		callerFile := p.Fid[i]
		if target == 0 {
			target = fileScope[fileNameKey{callerFile, base}]
		}
		if target == 0 {
			target = unique[base]
		}
		if target == 0 {
			if g.isExternalName(name, base, callerFile, imported) {
				extByCaller[p.Sid[i]]++
				st.external++
			} else {

				short := cutStr(name, 160)
				k := callerNameKey{p.Sid[i], short}
				if ex, ok := g.unresIdx[k]; ok {
					g.Unresolved[ex].N++
				} else {
					g.unresIdx[k] = int32(len(g.Unresolved))
					g.Unresolved = append(g.Unresolved, Unresolved{
						Caller: p.Sid[i], name: cgPut(short), N: 1,
						FirstLine: p.Line[i],
					})
				}
				st.unresolved++
			}
			continue
		}
		loc := symLoc[target]
		calleeFile := int32(loc >> 32)
		calleeMod := int32(loc & 0xffffffff)
		callerMod := g.Files[callerFile-1].ModuleID
		caller := p.Sid[i]
		ek := pair(caller, target)
		if ex, ok := edgeIdx[ek]; ok {
			g.Edges[ex].NCalls++
		} else {
			edgeIdx[ek] = int32(len(g.Edges))
			g.Edges = append(g.Edges, Edge{
				Caller: caller, Callee: target, NCalls: 1,
				SameFile: calleeFile == callerFile, SameModule: calleeMod == callerMod,
				Self: caller == target,
			})
		}
		sites[trip(caller, target, p.Line[i])] = struct{}{}
		st.resolved++
	}
	g.Callsites = make([]Callsite, 0, len(sites))
	for k := range sites {
		g.Callsites = append(g.Callsites, Callsite{
			Caller: int32(k >> 42),
			Callee: int32((k >> 21) & 0x1fffff),
			Line:   int32(k & 0x1fffff),
		})
	}

	slices.SortFunc(g.Callsites, func(a, b Callsite) int {
		if a.Caller != b.Caller {
			return int(a.Caller) - int(b.Caller)
		}
		if a.Callee != b.Callee {
			return int(a.Callee) - int(b.Callee)
		}
		return int(a.Line) - int(b.Line)
	})
	g.extByCaller = extByCaller
	return st
}

func lastIndexByte(s string, b byte) int {
	for i := len(s) - 1; i >= 0; i-- {
		if s[i] == b {
			return i
		}
	}
	return -1
}

func (g *Graph) isExternalName(name, base string, fid int32, imported map[int32]map[string]bool) bool {
	head := name
	if k := indexByte(name, '.'); k >= 0 {
		head = name[:k]
	}
	if builtinGlobals[head] {
		return true
	}
	if indexByte(name, '.') < 0 && builtinGlobals[base] {
		return true
	}
	if m := imported[fid]; m != nil {
		if m[head] {
			return true
		}
		if m[base] {
			return true
		}
	}
	return false
}

func indexByte(s string, b byte) int {
	for i := 0; i < len(s); i++ {
		if s[i] == b {
			return i
		}
	}
	return -1
}

var builtinGlobals = func() map[string]bool {
	m := map[string]bool{}
	for s := range strings.FieldsSeq(`
Array Object String Number Boolean Symbol BigInt Math JSON Date RegExp Error
TypeError RangeError SyntaxError Promise Map Set WeakMap WeakSet Proxy Reflect
console process Buffer globalThis window document navigator localStorage
setTimeout setInterval clearTimeout clearInterval queueMicrotask structuredClone
fetch URL URLSearchParams TextEncoder TextDecoder AbortController Intl
parseInt parseFloat isNaN isFinite encodeURIComponent decodeURIComponent
require module exports __dirname __filename Function eval undefined NaN Infinity
`) {
		m[s] = true
	}
	return m
}()

func runFile(e *extractor, pf *pendingFile) {
	e.src = newSrc(pf.data)
	t := e.tree
	s := e.src
	o := e.sink

	if t.len() == 0 {
		return
	}

	if t.rootHasErr {
		o.hasError = true
		for i := 0; i < t.len(); i++ {
			if t.sym(i) == t.lang.errSym {
				o.nErrors++
			} else if t.cols.missing[i] != 0 {
				o.nMissing++
			}
		}
	}

	e.scanLines(s, o)
	e.parseImports(t, s, pf, o)
	e.walkScope(t, s, pf, o, scope{symID: -1})
	e.emitModuleScope(t, s, pf, o)

	if hasSuffix(pf.rel, ".d.ts") {
		o.langDecl = true
	}
}

func hasSuffix(s, suf string) bool {
	return len(s) >= len(suf) && s[len(s)-len(suf):] == suf
}

func (e *extractor) scanLines(s srcFile, o *fileOut) {
	n := 0
	if s.ascii {
		data := s.data
		start := 0
		for i := 0; i <= len(data); i++ {
			if i < len(data) {
				switch data[i] {
				case '\n', '\r', '\v', '\f', 0x1c, 0x1d, 0x1e:
				default:
					continue
				}
			}
			n++
			e.scanLine(string(data[start:i]), n, o)
			if i < len(data) && data[i] == '\r' && i+1 < len(data) && data[i+1] == '\n' {
				i++
			}
			start = i + 1
		}
		return
	}
	for i, l := range cgSplitLinesRunes(string(s.data)) {
		e.scanLine(l, i+1, o)
	}
}

func (e *extractor) scanLine(line string, n int, o *fileOut) {
	if markerLineGate(line) {
		if kw := matchMarker(line); kw != "" {
			o.markers = append(o.markers, Marker{
				SymID: -1, kind: e.slab.put(upperKW(kw)), Line: int32(n),
				text: e.slab.put(cutStr(cgStrip(line), 200)),
			})
		}
	}

	if !containsStr(line, "ts-") && !containsStr(line, "eslint") {
		return
	}
	g, ok := matchSuppress(line)
	if !ok {
		return
	}
	rest := line[strings.Index(line, g.group)+len(g.group):]
	reason := cutStr(trimSet(rest, " -:*/"), 160)
	o.suppress = append(o.suppress, Suppression{
		FileID: e.fid, SymID: -1, kind: e.slab.put(g.kind), Line: int32(n),
		reason: e.slab.put(reason), HasReason: reason != "",
	})
}

func upperKW(s string) string {
	b := []byte(s)
	for i, c := range b {
		if c >= 'a' && c <= 'z' {
			b[i] = c - 32
		}
	}
	return string(b)
}

type frame struct {
	c     int
	inner scope
}

func (e *extractor) walkScope(t *Tree, s srcFile, pf *pendingFile, o *fileOut, init scope) {
	d := t.lang.disp
	root := 0
	stack := e.frames[:0]
	stack = append(stack, frame{c: t.firstChild(root), inner: init})
	for len(stack) > 0 {
		fr := &stack[len(stack)-1]
		for fr.c >= 0 && t.cols.named[fr.c] == 0 {
			fr.c = t.nextSibling(fr.c)
		}
		if fr.c < 0 {
			stack = stack[:len(stack)-1]
			continue
		}
		cur := fr.c
		fr.c = t.nextSibling(fr.c)
		csc := fr.inner
		cc := t.codeAt(cur)
		if k := d.funcKind[cc]; k != fkNone {
			sid := e.emitFunction(t, s, pf, o, csc, cur, funcKindSymbol(k))

			name := e.nodeName(t, s, cur)
			if name == "" {
				name = "?"
			}
			inner := scope{symID: sid, qualPre: csc.qualPre + name + ".",
				typeName: csc.typeName}
			b := t.body(cur)
			stack = append(stack, frame{c: t.firstChild(b), inner: inner})
			continue
		}
		if k := d.typeKind[cc]; k != 0 {
			sid := e.emitType(t, s, pf, o, csc, cur, k)
			name := e.nodeName(t, s, cur)
			inner := scope{symID: sid, qualPre: csc.qualPre + name + ".",
				typeName: name, typeID: sid}
			b := t.body(cur)
			stack = append(stack, frame{c: t.firstChild(b), inner: inner})
			continue
		}
		stack = append(stack, frame{c: t.firstChild(cur), inner: csc})
	}
	e.frames = stack[:0]
}

func runQuery(g *Graph, q queryDef, mod string, lim int) *table {
	return q.Run(g, mod, lim)
}

const (
	tsRecBytes = 50

	tsLangTS  = 0
	tsLangTSX = 1
)

var tsScopes = [2]string{"source.ts", "source.tsx"}

type tsCols struct {
	sym, field                  []uint16
	start, end                  []uint32
	srow, scol, erow, ecol      []uint32
	parent, first, next, subEnd []int32
	nchild, nnamed              []uint16
	named, missing              []uint8
}

var tsColWidths = [...]uint64{2, 2, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 2, 2, 1, 1}

func tsColOffsets() [len(tsColWidths) + 1]int64 {
	var offs [len(tsColWidths) + 1]int64
	for i, w := range tsColWidths {
		offs[i+1] = offs[i] + int64(w)
	}
	return offs
}

func (c *tsCols) push(sym, field uint16, start, end, srow, scol, erow, ecol uint32,
	named, missing uint8) int32 {
	if sym > 65534 || field > 65534 {
		panic(fmt.Sprintf("codegraph_typescript: node id past the u16 record columns: sym=%d field=%d", sym, field))
	}
	i := int32(len(c.sym))
	c.sym = append(c.sym, sym)
	c.field = append(c.field, field)
	c.start = append(c.start, start)
	c.end = append(c.end, end)
	c.srow = append(c.srow, srow)
	c.scol = append(c.scol, scol)
	c.erow = append(c.erow, erow)
	c.ecol = append(c.ecol, ecol)
	c.parent = append(c.parent, -1)
	c.first = append(c.first, -1)
	c.next = append(c.next, -1)
	c.subEnd = append(c.subEnd, i+1)
	c.nchild = append(c.nchild, 0)
	c.nnamed = append(c.nnamed, 0)
	c.named = append(c.named, named)
	c.missing = append(c.missing, missing)
	return i
}

func (c *tsCols) trunc() tsCols {
	return tsCols{
		sym: c.sym[:0], field: c.field[:0],
		start: c.start[:0], end: c.end[:0],
		srow: c.srow[:0], scol: c.scol[:0], erow: c.erow[:0], ecol: c.ecol[:0],
		parent: c.parent[:0], first: c.first[:0], next: c.next[:0], subEnd: c.subEnd[:0],
		nchild: c.nchild[:0], nnamed: c.nnamed[:0],
		named: c.named[:0], missing: c.missing[:0],
	}
}

func (c *tsCols) win(base, n int) tsCols {
	return tsCols{
		sym: c.sym[base : base+n], field: c.field[base : base+n],
		start: c.start[base : base+n], end: c.end[base : base+n],
		srow: c.srow[base : base+n], scol: c.scol[base : base+n],
		erow: c.erow[base : base+n], ecol: c.ecol[base : base+n],
		parent: c.parent[base : base+n], first: c.first[base : base+n],
		next: c.next[base : base+n], subEnd: c.subEnd[base : base+n],
		nchild: c.nchild[base : base+n], nnamed: c.nnamed[base : base+n],
		named: c.named[base : base+n], missing: c.missing[base : base+n],
	}
}

func (c *tsCols) clone() tsCols {
	return tsCols{
		sym: slices.Clone(c.sym), field: slices.Clone(c.field),
		start: slices.Clone(c.start), end: slices.Clone(c.end),
		srow: slices.Clone(c.srow), scol: slices.Clone(c.scol),
		erow: slices.Clone(c.erow), ecol: slices.Clone(c.ecol),
		parent: slices.Clone(c.parent), first: slices.Clone(c.first),
		next: slices.Clone(c.next), subEnd: slices.Clone(c.subEnd),
		nchild: slices.Clone(c.nchild), nnamed: slices.Clone(c.nnamed),
		named: slices.Clone(c.named), missing: slices.Clone(c.missing),
	}
}

func (c *tsCols) colBytes(k, n int) []byte {
	if n <= 0 {
		return nil
	}
	switch k {
	case 0:
		return unsafe.Slice((*byte)(unsafe.Pointer(&c.sym[0])), n*2)
	case 1:
		return unsafe.Slice((*byte)(unsafe.Pointer(&c.field[0])), n*2)
	case 2:
		return unsafe.Slice((*byte)(unsafe.Pointer(&c.start[0])), n*4)
	case 3:
		return unsafe.Slice((*byte)(unsafe.Pointer(&c.end[0])), n*4)
	case 4:
		return unsafe.Slice((*byte)(unsafe.Pointer(&c.srow[0])), n*4)
	case 5:
		return unsafe.Slice((*byte)(unsafe.Pointer(&c.scol[0])), n*4)
	case 6:
		return unsafe.Slice((*byte)(unsafe.Pointer(&c.erow[0])), n*4)
	case 7:
		return unsafe.Slice((*byte)(unsafe.Pointer(&c.ecol[0])), n*4)
	case 8:
		return unsafe.Slice((*byte)(unsafe.Pointer(&c.parent[0])), n*4)
	case 9:
		return unsafe.Slice((*byte)(unsafe.Pointer(&c.first[0])), n*4)
	case 10:
		return unsafe.Slice((*byte)(unsafe.Pointer(&c.next[0])), n*4)
	case 11:
		return unsafe.Slice((*byte)(unsafe.Pointer(&c.subEnd[0])), n*4)
	case 12:
		return unsafe.Slice((*byte)(unsafe.Pointer(&c.nchild[0])), n*2)
	case 13:
		return unsafe.Slice((*byte)(unsafe.Pointer(&c.nnamed[0])), n*2)
	case 14:
		return unsafe.Slice((*byte)(unsafe.Pointer(&c.named[0])), n)
	case 15:
		return unsafe.Slice((*byte)(unsafe.Pointer(&c.missing[0])), n)
	}
	panic(fmt.Sprintf("codegraph_typescript: no such node column %d", k))
}

func tsColsFromMem(mem []byte, off, ln int64) (tsCols, error) {
	if ln%tsRecBytes != 0 {
		return tsCols{}, fmt.Errorf("node record arena length %d is not a multiple of the %d-byte record payload", ln, int64(tsRecBytes))
	}
	n := int(ln / tsRecBytes)
	root := uintptr(unsafe.Pointer(&mem[0])) + uintptr(off)
	offs := tsColOffsets()
	for k := range tsColWidths {
		if w := uintptr(tsColWidths[k]); w > 1 && (root+uintptr(offs[k])*uintptr(n))%w != 0 {
			return tsCols{}, fmt.Errorf("node column %d is not %d-byte aligned", k, int(w))
		}
	}
	at := func(k int) unsafe.Pointer {
		return unsafe.Pointer(uintptr(unsafe.Pointer(&mem[0])) + uintptr(off+offs[k]*int64(n)))
	}
	return tsCols{
		sym:     unsafe.Slice((*uint16)(at(0)), n),
		field:   unsafe.Slice((*uint16)(at(1)), n),
		start:   unsafe.Slice((*uint32)(at(2)), n),
		end:     unsafe.Slice((*uint32)(at(3)), n),
		srow:    unsafe.Slice((*uint32)(at(4)), n),
		scol:    unsafe.Slice((*uint32)(at(5)), n),
		erow:    unsafe.Slice((*uint32)(at(6)), n),
		ecol:    unsafe.Slice((*uint32)(at(7)), n),
		parent:  unsafe.Slice((*int32)(at(8)), n),
		first:   unsafe.Slice((*int32)(at(9)), n),
		next:    unsafe.Slice((*int32)(at(10)), n),
		subEnd:  unsafe.Slice((*int32)(at(11)), n),
		nchild:  unsafe.Slice((*uint16)(at(12)), n),
		nnamed:  unsafe.Slice((*uint16)(at(13)), n),
		named:   unsafe.Slice((*uint8)(at(14)), n),
		missing: unsafe.Slice((*uint8)(at(15)), n),
	}, nil
}

func init() {
	total := uint64(0)
	for _, w := range tsColWidths {
		total += w
	}
	if total != tsRecBytes || len(tsColWidths) != 16 {
		panic(fmt.Sprintf("node columns sum to %d bytes across %d columns, the fixed v2 payload is %d bytes across 16 columns",
			total, len(tsColWidths), tsRecBytes))
	}
}

func tsCLIBin() string {

	if b := os.Getenv("TREE_SITTER_BIN"); b != "" {
		return b
	}
	if home, err := os.UserHomeDir(); err == nil {
		if b := filepath.Join(home, ".cache", "codegraph", "bin", "tree-sitter"); fileExists(b) {
			return b
		}
	}
	if b, err := exec.LookPath("tree-sitter"); err == nil {
		return b
	}
	return "/opt/homebrew/bin/tree-sitter"
}

func fileExists(p string) bool {
	st, err := os.Stat(p)
	return err == nil && !st.IsDir()
}

type tsParser struct {
	bin     string
	cliEnv  []string
	devNull *os.File
}

func buildLineStarts(dst []int, src []byte) ([]int, int) {
	dst = append(dst[:0], 0)
	w, row, start := 1, 0, 0
	for i := 0; i < len(src); i++ {
		if src[i] != '\n' {
			continue
		}
		if w2 := ilog10(row) + ilog10(cstLossy(src[start:i])) + 1; w2 > w {
			w = w2
		}
		dst = append(dst, i+1)
		row++
		start = i + 1
	}
	if w2 := ilog10(row) + ilog10(cstLossy(src[start:])) + 1; w2 > w {
		w = w2
	}
	return dst, w
}

var cliConfigPath = sync.OnceValue(func() string {
	if p := os.Getenv("TREE_SITTER_CONFIG_PATH"); p != "" {
		return p
	}
	if dir := os.Getenv("XDG_CONFIG_HOME"); dir != "" {
		if _, err := os.Stat(filepath.Join(dir, "tree-sitter", "config.json")); err == nil {
			return filepath.Join(dir, "tree-sitter", "config.json")
		}
	}
	if home, err := os.UserHomeDir(); err == nil {
		p := filepath.Join(home, ".config", "tree-sitter", "config.json")
		if _, err := os.Stat(p); err == nil {
			return p
		}
	}
	return ""
})

func tsParserNew() *tsParser {
	bin := tsCLIBin()
	if _, err := os.Stat(bin); err != nil {
		panic("tree-sitter CLI not found at " + bin + " -- see setup.sh")
	}
	env := append(os.Environ(), "NO_COLOR=1", "TERM=dumb")
	devNull, err := os.OpenFile(os.DevNull, os.O_RDWR, 0)
	if err != nil {
		devNull = nil
	}
	p := &tsParser{bin: bin, cliEnv: env, devNull: devNull}
	p.checkDelimiter()
	return p
}

var tsDelimOnce sync.Once

func (p *tsParser) checkDelimiter() {
	tsDelimOnce.Do(func() {
		if p.probeDelimiter() {
			return
		}
		fmt.Fprintf(os.Stderr,
			"codegraph-typescript: the tree-sitter CLI at %s (%s) prints no blank line "+
				"between parsed trees, so batched parsing is unavailable and this run "+
				"spawns one child per file instead of one per 32.\n"+
				"  the per-tree blank line this port splits on is an undocumented "+
				"CLI-version contract: it holds in 0.25.10 and is absent in 0.27.0.\n"+
				"  the graph is NOT affected -- only the number of child processes is. "+
				"Pin TREE_SITTER_BIN to a 0.25.10 build to restore batching.\n",
			p.bin, p.cliVersion())
	})
}

func (p *tsParser) probeDelimiter() bool {
	d, err := os.MkdirTemp("", "cgts-probe-")
	if err != nil {
		return true
	}
	defer os.RemoveAll(d)
	a, b := filepath.Join(d, "0"), filepath.Join(d, "1")
	src := []byte("export const a: number = 1;\n")
	if os.WriteFile(a, src, 0o600) != nil || os.WriteFile(b, src, 0o600) != nil {
		return true
	}
	out, ok := p.parse(nil, []string{a, b}, tsLangTS)
	if !ok || len(out) == 0 {
		return true
	}
	n := 0
	for i := 1; i < len(out); i++ {
		if out[i] == '\n' && out[i-1] == '\n' {
			n++
		}
	}
	return n >= 2
}

func (p *tsParser) cliVersion() string {
	cmd := exec.Command(p.bin, "--version")
	cmd.Env = p.cliEnv
	cmd.Stderr = p.devNull
	v, err := cmd.Output()
	if err != nil {
		return "version unreadable"
	}
	if i := bytes.IndexByte(v, '\n'); i >= 0 {
		v = v[:i]
	}
	return string(bytes.TrimSpace(v))
}

func (p *tsParser) free() {
	if p.devNull != nil {
		p.devNull.Close()
		p.devNull = nil
	}
}

type tsStage struct {
	dir   string
	paths []string
}

func newTSStage() *tsStage {
	d, err := os.MkdirTemp("", "cgts-cst-")
	if err != nil {
		return &tsStage{}
	}
	return &tsStage{dir: d}
}

func (s *tsStage) clear() {
	for _, p := range s.paths {
		os.Remove(p)
	}
	s.paths = s.paths[:0]
}

func (s *tsStage) close() {
	if s.dir == "" {
		return
	}
	s.clear()
	os.Remove(s.dir)
}

func (s *tsStage) put(name, fallback string, data []byte) string {
	if s.dir == "" {
		return fallback
	}
	p := filepath.Join(s.dir, name)
	if err := os.WriteFile(p, data, 0o600); err != nil {
		return fallback
	}
	s.paths = append(s.paths, p)
	return p
}

func (p *tsParser) parse(dst []byte, paths []string, lang int) ([]byte, bool) {
	if len(paths) == 0 {
		return nil, false
	}
	args := make([]string, 0, 5+len(paths))
	args = append(args, "parse")
	args = append(args, paths...)
	args = append(args, "--scope", tsScopes[lang], "--cst")
	if cp := cliConfigPath(); cp != "" {
		args = append(args, "--config-path", cp)
	}
	cmd := exec.Command(p.bin, args...)
	cmd.Env = p.cliEnv
	cmd.Stderr = p.devNull

	stdoutR, stdoutW, err := os.Pipe()
	if err != nil {
		return nil, false
	}
	cmd.Stdout = stdoutW
	if serr := cmd.Start(); serr != nil {
		stdoutR.Close()
		stdoutW.Close()
		return nil, false
	}
	stdoutW.Close()

	want := 0
	for _, pth := range paths {
		if fi, serr := os.Stat(pth); serr == nil {
			want += int(fi.Size()) * 24
		}
	}
	b := dst[:0]
	if want < 1<<16 {
		want = 1 << 16
	}
	if cap(b) < want {
		b = make([]byte, 0, want)
	}

	var rerr error
	for {
		if len(b) == cap(b) {
			b = append(b, 0)[:len(b)]
		}
		var n int
		n, rerr = stdoutR.Read(b[len(b):cap(b)])
		b = b[:len(b)+n]
		if rerr != nil {
			break
		}
	}
	stdoutR.Close()
	out := b
	err = cmd.Wait()
	if childDied(err) {
		return nil, false
	}
	if rerr != nil && len(out) == 0 {
		return nil, false
	}
	if err != nil && len(out) == 0 {
		return nil, false
	}
	return out, true
}

func childDied(err error) bool {
	if err == nil {
		return false
	}
	ee, ok := err.(*exec.ExitError)
	if !ok {
		return true
	}
	if ws, ok := ee.Sys().(syscall.WaitStatus); ok && ws.Signaled() {
		return true
	}
	return ee.ExitCode() > 1
}

type tsTree struct {
	cols       tsCols
	n          int
	rootHasErr bool
	failed     bool
	lang       uint8
}

var tsInterners = sync.OnceValues(func() ([2]map[string]uint16, [2]map[string]uint16) {
	var syms [2]map[string]uint16
	var fields [2]map[string]uint16
	tables := [2]struct {
		names  []string
		fields []string
	}{
		{tsSymNames[:], tsFieldNames[:]},
		{tsxSymNames[:], tsxFieldNames[:]},
	}
	for li, t := range tables {
		syms[li] = make(map[string]uint16, len(t.names)+8)
		for s, name := range t.names {
			if _, dup := syms[li][name]; !dup {
				syms[li][name] = uint16(s)
			}
		}
		fields[li] = make(map[string]uint16, len(t.fields))
		for f := 1; f < len(t.fields); f++ {
			if _, dup := fields[li][t.fields[f]]; !dup {
				fields[li][t.fields[f]] = uint16(f)
			}
		}
	}
	return syms, fields
})

type cstFrame struct {
	i     int32
	end   uint32
	level int
}

type cstDecoder struct {
	starts  []int
	cols    tsCols
	stack   []cstFrame
	unquote []byte
	total   int
}

func decodeCST(d *cstDecoder, out, src []byte, lang int) (*tsTree, error) {
	d.total = len(src)
	var width int
	d.starts, width = buildLineStarts(d.starts, src)
	var opField []uint16
	if lang == tsLangTSX {
		opField = tsxSymOpField[:]
	} else {
		opField = tsSymOpField[:]
	}

	symByID, fieldByNameAll := tsInterners()
	nextFresh := uint16(0x4000)
	unquoteBuf := d.unquote[:0]

	if n := bytes.Count(out, []byte{'\n'}) + 1; cap(d.cols.sym) < n {
		d.cols = tsCols{
			sym: make([]uint16, 0, n), field: make([]uint16, 0, n),
			start: make([]uint32, 0, n), end: make([]uint32, 0, n),
			srow: make([]uint32, 0, n), scol: make([]uint32, 0, n),
			erow: make([]uint32, 0, n), ecol: make([]uint32, 0, n),
			parent: make([]int32, 0, n), first: make([]int32, 0, n),
			next: make([]int32, 0, n), subEnd: make([]int32, 0, n),
			nchild: make([]uint16, 0, n), nnamed: make([]uint16, 0, n),
			named: make([]uint8, 0, n), missing: make([]uint8, 0, n),
		}
	}
	cols := d.cols.trunc()
	stack := d.stack[:0]
	rootHasErr := false
	defer func() {
		if cap(cols.sym) > 1<<18 {
			d.cols = tsCols{}
		} else {
			d.cols = cols
		}
		if cap(stack) > 1<<15 {
			d.stack = nil
		} else {
			d.stack = stack[:0]
		}
		if cap(unquoteBuf) > 1<<18 {
			d.unquote = nil
		} else {
			d.unquote = unquoteBuf[:0]
		}
	}()

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
		depth := (len(rest) - len(trimmed) -
			cstRangePad(width, int(erow), int(ecol))) / 2
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
			named = false
			tok := bytes.TrimLeft(trimmed[len("MISSING: "):], " ")
			if len(tok) > 0 && tok[0] == '"' {
				kindB = unquoteBytes(tok, &unquoteBuf)
			} else {
				kindB, _ = kindToken(tok)
			}
		} else {

			if c := bytes.Index(trimmed, []byte(": ")); c > 0 {
				fname := trimmed[:c]
				if isFieldName(fname) {
					if f, ok := fieldByNameAll[lang][string(fname)]; ok {
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

		sym, ok := symByID[lang][string(kindB)]
		if !ok {
			if nextFresh > 65534 {
				panic(fmt.Sprintf("codegraph_typescript: fresh node kind id %d past the u16 sym column", nextFresh))
			}
			sym = nextFresh
			nextFresh++
		}

		start := d.offset(int(srow), int(scol))
		end := d.offset(int(erow), int(ecol))

		var nb, mb uint8
		if named {
			nb = 1
		}
		if missing {
			mb = 1
		}
		idx := cols.push(sym, field, start, end,
			uint32(srow), uint32(scol), uint32(erow), uint32(ecol), nb, mb)

		for len(stack) > 0 {
			top := stack[len(stack)-1]
			if top.end > start {
				break
			}
			if top.end == start && top.level < depth {
				break
			}
			cols.subEnd[top.i] = idx
			stack = stack[:len(stack)-1]
		}
		if len(stack) > 0 {
			p := stack[len(stack)-1].i
			cols.parent[idx] = p

			if nb == 0 && field == 0 {
				if op := opField[cols.sym[p]]; op != 0 {
					if op > 65534 {
						panic(fmt.Sprintf("codegraph_typescript: operator field id %d past the u16 field column", op))
					}
					cols.field[idx] = op
				}
			}
		}
		if idx == 0 {
			rootHasErr = hasErrMark || string(kindB) == "ERROR"
		}
		stack = append(stack, cstFrame{i: idx, end: end, level: depth})
	}

	for len(stack) > 0 {
		popped := stack[len(stack)-1]
		cols.subEnd[popped.i] = int32(len(cols.sym))
		stack = stack[:len(stack)-1]
	}
	if len(cols.sym) == 0 {
		return nil, fmt.Errorf("no nodes decoded (cli produced %d bytes)", len(out))
	}
	cols.parent[0] = -1

	n := int32(len(cols.sym))
	for i := n - 1; i >= 0; i-- {
		end := cols.subEnd[i]
		first := int32(i + 1)
		if end <= first {

			if i > 0 && cols.named[i] != 0 && cols.start[i] == cols.end[i] {
				cols.missing[i] = 1
			}
			continue
		}
		cols.first[i] = first
		var nc, nn uint16
		for c := first; c < end; {
			nx := cols.subEnd[c]
			if nx < end {
				cols.next[c] = nx
			} else {
				cols.next[c] = -1
			}
			nc++
			if cols.named[c] != 0 {
				nn++
			}
			c = nx
		}
		if nc > 65534 || nn > 65534 {
			panic(fmt.Sprintf("codegraph_typescript: node %d has %d children (%d named), past the u16 count columns", i, nc, nn))
		}
		cols.nchild[i] = nc
		cols.nnamed[i] = nn
	}
	return &tsTree{cols: cols, n: int(n), rootHasErr: rootHasErr, lang: uint8(lang)}, nil
}

func cstLossy(src []byte) int {
	n := 0
	for i := 0; i < len(src); {
		r, size := utf8.DecodeRune(src[i:])
		if r == utf8.RuneError && size == 1 {

			for i < len(src) {
				r2, s2 := utf8.DecodeRune(src[i:])
				if r2 == utf8.RuneError && s2 == 1 {
					i++
					continue
				}
				break
			}
			n += 3
			continue
		}
		i += size
		n += size
	}
	return n
}

func cstRangePad(width, row, col int) int {
	p := width - ilog10(row) - ilog10(col)
	if p < 1 {
		return 1
	}
	return p
}

func ilog10(n int) int {
	d := 0
	for n >= 10 {
		n /= 10
		d++
	}
	return d
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

var declaratorTypes = map[int16]bool{
	cVariableDeclarator: true, cPublicFieldDefinition: true, cFieldDefinition: true,
	cPair: true, cPropertySignature: true, cAssignmentExpression: true,
}

var climbForExport = map[int16]bool{
	cVariableDeclarator: true, cLexicalDeclaration: true, cVariableDeclaration: true,
	cExpressionStatement: true,
}

var climbForDoc = map[int16]bool{
	cExportStatement: true, cLexicalDeclaration: true, cVariableDeclaration: true,
	cExpressionStatement: true,
}

func (e *extractor) nodeName(t *Tree, s srcFile, node int) string {
	if v, ok := e.nameC[int32(node)]; ok {
		return v
	}
	cc := t.codeAt(node)
	var out string
	if cc == cArrowFunction || cc == cFunctionExpression {
		cur := t.parent(node)
		for hops := 0; cur >= 0 && hops < 4; hops++ {
			if declaratorTypes[t.codeAt(cur)] {
				f := t.f()
				for _, fid := range [3]int{f.name, f.left, f.key} {
					if g := t.fieldChild(cur, fid); g >= 0 {
						out = trimQuotes(s.strStripN(t.start(g), t.end(g), 1<<30))
						e.nameC[int32(node)] = out
						return out
					}
				}
			}
			if t.codeAt(cur) == cExportStatement {
				out = "default"
				e.nameC[int32(node)] = out
				return out
			}
			cur = t.parent(cur)
		}

		e.nameC[int32(node)] = ""
		return ""
	}
	f := t.f()
	if g := t.fieldChild(node, f.name); g >= 0 {
		out = s.strStripN(t.start(g), t.end(g), 1<<30)
		e.nameC[int32(node)] = out
		return out
	}
	for c := t.firstChild(node); c >= 0; c = t.nextSibling(c) {
		if t.cols.named[c] == 0 {
			continue
		}
		switch t.codeAt(c) {
		case cIdentifier, cPropertyIdentifier, cTypeIdentifier,
			cPrivatePropertyIdentifier, cShorthandPropertyIdentifier:
			out = s.strStripN(t.start(c), t.end(c), 1<<30)
			e.nameC[int32(node)] = out
			return out
		}
	}
	e.nameC[int32(node)] = ""
	return ""
}

func trimQuotes(s string) string { return trimSet(s, "\"'`") }

func (e *extractor) isExported(t *Tree, node int) bool {
	if v, ok := e.expC[int32(node)]; ok {
		return v
	}
	p := t.parent(node)
	for p >= 0 && climbForExport[t.codeAt(p)] {
		p = t.parent(p)
	}
	v := p >= 0 && t.codeAt(p) == cExportStatement
	e.expC[int32(node)] = v
	return v
}

func (e *extractor) visibilityOf(t *Tree, s srcFile, node int) string {
	for c := t.firstChild(node); c >= 0; c = t.nextSibling(c) {
		if t.codeAt(c) == cAccessibilityModifier {
			return s.strStripN(t.start(c), t.end(c), 1<<30)
		}
	}
	name := e.nodeName(t, s, node)
	if hasPrefix(name, "#") || hasPrefix(name, "_") {
		return "private"
	}
	if e.isExported(t, node) {
		return "public"
	}
	return ""
}

func (e *extractor) functionFlags(t *Tree, s srcFile, pf *pendingFile, node int, m *meas, sig string) {
	f := t.f()
	nConstTP := int32(0)
	if tps := t.fieldChild(node, f.typeParams); tps >= 0 {
		for c := t.firstChild(tps); c >= 0; c = t.nextSibling(c) {
			if t.cols.named[c] == 0 || t.codeAt(c) != cTypeParameter {
				continue
			}
			if t.start(c)+6 <= len(s.data) && string(s.data[t.start(c):t.start(c)+6]) == "const " {
				nConstTP++
			}
		}
	}
	m.setv(mNConstTypeParams, nConstTP)

	name := e.nodeName(t, s, node)
	if sig == "" {
		sig = e.signatureOf(t, s, node)
	}

	docSib := node
	for {
		p := t.parent(docSib)
		if p < 0 || !climbForDoc[t.codeAt(p)] {
			break
		}
		docSib = p
	}
	isDep := int32(0)
	for p := t.prevSibling(docSib); p >= 0 && t.codeAt(p) == cComment; p = t.prevSibling(p) {
		if containsStr(t.text(p, s), "@deprecated") {
			isDep = 1
			break
		}
	}
	m.setv(mIsDeprecated, isDep)

	ptxt := ""
	if p := t.fieldChild(node, f.parameters); p >= 0 {
		ptxt = t.text(p, s)
	}
	rtxt := ""
	if r := t.fieldChild(node, f.returnType); r >= 0 {
		rtxt = t.text(r, s)
	}
	bodyNode := t.fieldChild(node, f.body)
	exported := e.isExported(t, node)

	isGet, isSet, isOvr := int32(0), int32(0), int32(0)
	for c := t.firstChild(node); c >= 0; c = t.nextSibling(c) {
		switch t.codeAt(c) {
		case cGet:
			isGet = 1
		case cSet:
			isSet = 1
		case cOverrideModifier:
			isOvr = 1
		}
	}
	m.setv(mIsGetter, isGet)
	m.setv(mIsSetter, isSet)
	m.setv(mIsOverride, isOvr)

	btxt := ""
	if isUpperFirst(name) && bodyNode >= 0 {
		btxt = s.strN(t.start(bodyNode), t.end(bodyNode), 600)
	}
	head := headStr(sig, 40)
	m.setv(mIsPublic, b2i(exported || !hasPrefix(name, "_") && !(len(name) > 0 && name[0] == '#')))
	m.setv(mIsExported, b2i(exported))
	if containsStr(head, "async") {
		m.setv(mIsAsync, 1)
	}
	if indexByteStr(head, '*') >= 0 {
		m.setv(mIsGenerator, 1)
	}
	if t.codeAt(node) == cAbstractMethodSignature || containsStr(head, "abstract") {
		m.setv(mIsAbstract, 1)
	}
	if bodyNode < 0 {
		m.setv(mIsDeclarationOnly, 1)
	}
	if hasPrefix(name, "test") || hasPrefix(name, "it") || hasPrefix(name, "describe") {
		m.setv(mIsTest, 1)
	}
	if hasPrefix(name, "use") && runeLen(name) > 3 && isUpperRune(runeAt(name, 3)) {
		m.setv(mIsHook, 1)
	}
	if isUpperFirst(name) && (containsStr(btxt, "<") || containsAnyFoldStr(btxt, "jsx")) {
		m.setv(mIsComponent, 1)
	}
	if isHandlerShape(ptxt) {
		m.setv(mIsHandler, 1)
	}
	m.setv(mNAnyParams, int32(countAny(ptxt)))
	if hasAny(rtxt) {
		m.setv(mReturnsAny, 1)
	}
	m.setv(mNAnyTotal, int32(countAny(sig)))
	m.setv(mNUnknownType, int32(countStr(sig, "unknown")))
	m.setv(mMaxTypeDepth, int32(typeDepth(sig)))
}

func b2i(b bool) int32 {
	if b {
		return 1
	}
	return 0
}

func isUpperFirst(s string) bool {
	return len(s) > 0 && s[0] >= 'A' && s[0] <= 'Z'
}

func runeLen(s string) int {
	n := 0
	for range s {
		n++
	}
	return n
}

func runeAt(s string, i int) rune {
	n := 0
	for _, r := range s {
		if n == i {
			return r
		}
		n++
	}
	return 0
}

func isUpperRune(r rune) bool {
	if r < 128 {
		return r >= 'A' && r <= 'Z'
	}
	return unicode.IsUpper(r)
}

func indexByteStr(s string, b byte) int {
	for i := 0; i < len(s); i++ {
		if s[i] == b {
			return i
		}
	}
	return -1
}

func hasExpMarker(s string) bool {
	return indexByteStr(s, 'e') >= 0 || indexByteStr(s, 'E') >= 0
}

func headStr(s string, n int) string { return cutStr(s, n) }

func containsStr(s, sub string) bool { return indexStr(s, sub) >= 0 }

func containsAnyFoldStr(s, sub string) bool {
	l := lowerStr(s)
	return indexStr(l, lowerStr(sub)) >= 0
}

func (e *extractor) typeFlags(t *Tree, s srcFile, node int, m *meas, txt string) {
	d := t.lang.disp

	for _, col := range []int{mNConditionalType, mNMappedType, mNTemplateType,
		mNIndexSignature, mNGenericParams,
		mNTypeArgs, mNInfer, mNKeyof, mNCallSig, mNPropSig,
		mNUnionType, mNTypeofType, mNIntersectionType, mNDecorators,
		mNUnionMembers, mNAnyTotal} {
		m.setv(col, 0)
	}
	var maxDepth int32
	kids := e.kids[:0]
	stack := e.tstack[:0]
	stack = append(stack, tframe{int32(node), 0})
	for len(stack) > 0 {
		f := stack[len(stack)-1]
		stack = stack[:len(stack)-1]
		i := int(f.i)
		c := t.codeAt(i)

		if col := d.typeCnt[c]; col >= 0 {
			m.setv(int(col), m.vals[col]+1)
		}
		cd := f.c
		if c == cConditionalType {
			cd++
			if cd > maxDepth {
				maxDepth = cd
			}
		}
		switch c {
		case cUnionType:
			m.setv(mNUnionMembers, m.vals[mNUnionMembers]+
				int32(maxI32(0, int32(t.namedCount(i))-1)))
		case cPredefinedType:
			if t.text(i, s) == "any" {
				m.setv(mNAnyTotal, m.vals[mNAnyTotal]+1)
			}
		}
		kids = kids[:0]
		for k := t.firstChild(i); k >= 0; k = t.nextSibling(k) {
			kids = append(kids, k)
		}
		for _, kid := range slices.Backward(kids) {
			stack = append(stack, tframe{int32(kid), cd})
		}
	}
	e.tstack = stack[:0]
	e.kids = kids[:0]
	exported := e.isExported(t, node)
	m.setv(mIsPublic, b2i(exported))
	m.setv(mIsExported, b2i(exported))
	if t.codeAt(node) == cAbstractClassDeclaration {
		m.setv(mIsAbstract, 1)
	}
	td := int32(typeDepth(cutStr(txt, 4000)))
	if td > maxDepth {
		m.setv(mMaxTypeDepth, td)
	} else {
		m.setv(mMaxTypeDepth, maxDepth)
	}
	m.setv(mNConditionalDepth, maxDepth)
}

var heritageTypes = map[int16]bool{
	cExtendsClause: true, cClassHeritage: true, cExtendsTypeClause: true,
	cImplementsClause: true,
}

func (e *extractor) typeExtra(t *Tree, s srcFile, node int, sid int32, o *fileOut, txt string) {
	body := t.fieldChild(node, t.f().body)
	hasBody := body >= 0

	first := -1
	if hasBody {
		first = t.firstChild(body)
	}
	nOpt, nRO, nIdx, nCall, nAny, nMem := int32(0), int32(0), int32(0), int32(0), int32(0), int32(0)
	nExt := int32(0)
	extParts := make([]string, 0, 2)
	for c := t.firstChild(node); c >= 0; c = t.nextSibling(c) {
		if heritageTypes[t.codeAt(c)] {
			nExt++
			extParts = append(extParts, cgStrip(strings.ReplaceAll(
				strings.ReplaceAll(t.text(c, s), "extends", ""), "implements", "")))
		}
	}
	extNames := ""
	if len(extParts) > 0 {
		extNames = cutStr(strings.Join(extParts, ","), 300)
	}
	ord := int32(0)
	for c := first; c >= 0; c = t.nextSibling(c) {
		if t.cols.named[c] == 0 {
			continue
		}
		mtxt := t.text(c, s)
		head2, _, _ := cut3(mtxt, ":")
		if containsStr(head2, "?") {
			nOpt++
		}
		lstripped := cgLStrip(mtxt)
		if hasPrefix(lstripped, "readonly") {
			nRO++
		}
		cc := t.codeAt(c)
		if cc == cIndexSignature {
			nIdx++
		}
		if cc == cCallSignature || cc == cConstructSignature {
			nCall++
		}
		if hasAny(mtxt) {
			nAny++
		}
		mname := e.nodeName(t, s, c)
		if mname == "" {
			hh, _, _ := cut3(mtxt, ":")
			mname = cutStr(cgStrip(hh), 80)
		}
		mtype := ""
		if ta := t.fieldChild(c, t.f().typeF); ta >= 0 {
			mtype = lstripSet(t.text(ta, s), ": ")
		}
		mtHead := headStr(mtxt, 20)
		o.fields = append(o.fields, Field{
			SymID: sid, Ordinal: ord, name: e.slab.put(cutStr(mname, 120)),
			typ: e.slab.put(cutStr(mtype, 200)), Line: int32(t.srow(c)) + 1,
			IsConst: containsStr(mtHead, "readonly"),
			IsMut:   !containsStr(mtHead, "readonly") && cc != cMethodDefinition && cc != cMethodSignature,
			IsNull:  containsStr(head2, "?") || containsStr(mtype, "null") || containsStr(mtype, "undefined"),
			IsColl: hasPrefix(mtype, "Array") || hasPrefix(mtype, "Map") || hasPrefix(mtype, "Set") ||
				hasPrefix(mtype, "Record") || hasSuffixStr(mtype, "[]"),
			IsUntyp: mtype == "",
			Depth:   int32(typeDepth(mtype)),
		})
		ord++
		nMem++
	}
	ambient := containsStr(headStr(txt, 40), "declare")
	if !ambient {
		p := t.parent(node)
		ambient = p >= 0 && t.codeAt(p) == cAmbientDeclaration
	}
	o.typeDefs = append(o.typeDefs, TypeDef{
		SymID: sid, NMembers: nMem, NOptional: nOpt, NReadonly: nRO,
		NIndexSig: nIdx, NCallSig: nCall, NExtends: nExt, extendsName: e.slab.put(extNames),
		NAnyMembers: nAny, IsExported: e.isExported(t, node),
		IsAmbient: ambient, IsConstEnum: containsStr(headStr(txt, 40), "const enum"),
	})
	if t.codeAt(node) == cEnumDeclaration && hasBody {
		i := int32(0)
		for c := t.firstChild(body); c >= 0; c = t.nextSibling(c) {
			if t.cols.named[c] == 0 {
				continue
			}
			mtxt := t.text(c, s)
			nm, val, hasVal := cutAssign(mtxt)

			hasVal = hasVal && cgStrip(val) != ""
			o.enumMembers = append(o.enumMembers, EnumMember{
				SymID: sid, Ordinal: i, name: e.slab.put(cutStr(cgStrip(nm), 80)),
				value: e.slab.put(cutStr(cgStrip(val), 60)), HasVal: hasVal,
			})
			i++
		}
	}
}

func cut3(s, sep string) (string, string, bool) {
	for i := 0; i+len(sep) <= len(s); i++ {
		if s[i:i+len(sep)] == sep {
			return s[:i], s[i+len(sep):], true
		}
	}
	return s, "", false
}

func cutAssign(s string) (string, string, bool) {
	for i := 0; i < len(s); i++ {
		if s[i] == '=' {
			return s[:i], s[i+1:], true
		}
	}
	return s, "", false
}

func hasSuffixStr(s, suf string) bool {
	return len(s) >= len(suf) && s[len(s)-len(suf):] == suf
}

func (e *extractor) emitAttributes(t *Tree, s srcFile, pf *pendingFile, node int, sid int32, o *fileOut) {
	seen := map[int32]bool{}
	add := func(n int) {
		if seen[int32(n)] {
			return
		}
		seen[int32(n)] = true
		txt := t.text(n, s)

		nm := lstripSet(txt, "@")
		if i := indexByte(nm, '('); i >= 0 {
			nm = cgStrip(nm[:i])
		}
		o.attributes = append(o.attributes, AttrRow{
			SymID: sid, FileID: pf.fid, name: e.slab.put(cutStr(nm, 120)),
			args: e.slab.put(cutStr(txt, 200)), Line: int32(t.srow(n)) + 1,
		})
	}
	par := t.parent(node)
	if par >= 0 && t.codeAt(par) == cExportStatement {
		for c := t.firstChild(par); c >= 0; c = t.nextSibling(c) {
			if t.codeAt(c) == cDecorator {
				add(c)
			}
		}
	}
	if par >= 0 && t.codeAt(par) == cClassBody {
		for c := t.firstChild(par); c >= 0; c = t.nextSibling(c) {
			if t.codeAt(c) != cDecorator || t.end(c) > t.start(node) {
				continue
			}
			between := false
			for m := t.firstChild(par); m >= 0; m = t.nextSibling(m) {
				if m != node && t.cols.named[m] != 0 &&
					t.start(m) >= t.end(c) && t.end(m) <= t.start(node) {
					between = true
					break
				}
			}
			if !between {
				add(c)
			}
		}
	}
	for c := t.firstChild(node); c >= 0; c = t.nextSibling(c) {
		if t.codeAt(c) == cDecorator {
			add(c)
		}
	}
}

var hazardCalls = map[string]string{
	"readFileSync": "sync_block", "writeFileSync": "sync_block",
	"existsSync": "sync_block", "readdirSync": "sync_block",
	"statSync": "sync_block", "execSync": "sync_block",
	"spawnSync": "sync_block", "pbkdf2Sync": "sync_block",
	"scryptSync": "sync_block", "deflateSync": "sync_block",
	"gzipSync": "sync_block",
	"eval":     "exec", "Function": "exec", "vm.runInNewContext": "exec",
	"vm.runInThisContext": "exec", "child_process.exec": "exec",
	"child_process.execSync": "exec", "require": "exec",
	"merge": "proto_pollution", "deepMerge": "proto_pollution",
	"defaultsDeep": "proto_pollution", "mergeWith": "proto_pollution",
	"extend": "proto_pollution", "set": "proto_pollution",
	"setWith": "proto_pollution", "Object.assign": "proto_pollution",
	"addEventListener": "listener", "removeEventListener": "listener",
	"addListener": "listener", "removeListener": "listener",
	"on": "listener", "off": "listener", "once": "listener",
	"subscribe": "listener", "unsubscribe": "listener",
	"observe": "listener", "disconnect": "listener",
	"IntersectionObserver": "listener", "MutationObserver": "listener",
	"ResizeObserver": "listener", "AbortController": "listener",
	"setTimeout": "timer", "setInterval": "timer", "clearTimeout": "timer",
	"clearInterval": "timer", "requestAnimationFrame": "timer",
	"cancelAnimationFrame": "timer", "setImmediate": "timer",
	"Map": "cache", "Set": "cache", "WeakMap": "cache", "WeakSet": "cache",
	"WeakRef": "cache", "FinalizationRegistry": "cache",
	"readFile": "io", "writeFile": "io", "createReadStream": "io",
	"createWriteStream": "io", "pipeline": "io",
	"fetch": "net", "XMLHttpRequest": "net", "WebSocket": "net",
	"EventSource": "net", "axios": "net", "http.request": "net",
	"https.request": "net",
	"innerHTML":     "dom", "outerHTML": "dom", "insertAdjacentHTML": "dom",
	"document.write": "dom", "dangerouslySetInnerHTML": "dom",
	"execCommand":  "dom",
	"localStorage": "storage", "sessionStorage": "storage",
	"indexedDB":   "storage",
	"Math.random": "crypto", "createHash": "crypto",
	"Object.defineProperty": "reflect", "Proxy": "reflect",
	"Reflect.get": "reflect", "Reflect.set": "reflect",
	"Reflect.ownKeys": "reflect", "structuredClone": "reflect",
}

var hazardIdx = func() map[string]int32 {
	m := make(map[string]int32, len(hazardCategories))
	for i, c := range hazardCategories {
		m[c] = int32(i)
	}
	return m
}()

func (e *extractor) emitHazards(m *meas, sid int32, o *fileOut) {
	if len(m.calls) == 0 {
		return
	}
	type ent struct {
		cat  int32
		n    int32
		line int32
		pat  string
	}
	order := make([]string, 0, 8)
	seen := make(map[string]*ent, 8)
	for i := range m.calls {
		text := m.calls[i].name
		if text == "" {
			continue
		}
		cat, ok := hazardCalls[text]
		if !ok {
			base := afterLastDot(text)
			cat, ok = hazardCalls[base]
			if !ok {
				continue
			}
			text = "*." + base
		}
		p := cutStr(text, 120)
		en, ok2 := seen[p]
		if !ok2 {
			en = &ent{cat: hazardIdx[cat], n: 1, line: m.calls[i].line, pat: p}
			seen[p] = en
			order = append(order, p)
			continue
		}
		en.n++
	}
	for _, p := range order {
		en := seen[p]
		o.hazards = append(o.hazards, Hazard{
			SymID: sid, pattern: e.slab.put(p), category: e.slab.put(catName(en.cat)),
			N: en.n, FirstLine: en.line,
		})
	}
}

func catName(c int32) string {
	if c >= 0 && c < int32(len(hazardCategories)) {
		return hazardCategories[c]
	}
	return ""
}

func afterLastDot(s string) string {
	for i := len(s) - 1; i >= 0; i-- {
		if s[i] == '.' {
			return s[i+1:]
		}
	}
	return s
}

type Options struct {
	Root             string
	IncludeTests     bool
	IncludeGenerated bool
	IncludeVendored  bool
	Quiet            bool
	Workers          int
	KeepTrees        bool
}

type BuildStats struct {
	FilesDiscovered int
	FilesParsed     int
	FilesFailed     int
	Symbols         int
	Edges           int
	Callsites       int
	Unresolved      int
	External        int
	Resolved        int
	Discovered      time.Duration
	Parsed          time.Duration
	Resolved2       time.Duration
	Aggregated      time.Duration
	DiscoveredStats discoverStats
}

func newGraph() *Graph {
	g := &Graph{
		byName:   map[string][]nameCand{},
		byQual:   map[string]int32{},
		kindIdx:  map[string]int8{},
		unresIdx: map[callerNameKey]int32{},
		hazIdx:   map[uint64]int32{},
		imported: map[int32]map[string]bool{},
	}
	for i, k := range kindNames {
		g.kindIdx[k] = int8(i)
	}
	return g
}

func (g *Graph) setMeta(k, v string) {
	for i := range g.Meta {
		if g.Meta[i].K.Str() == k {
			g.Meta[i].V = cgPut(v)
			return
		}
	}
	g.Meta = append(g.Meta, MetaRow{K: cgPut(k), V: cgPut(v)})
}

func build(o *Options) (*Graph, *BuildStats, error) {
	initLangs()
	g := newGraph()

	setGraph(g)
	bs := &BuildStats{}

	t0 := time.Now()
	files, ds := discover(g, o.Root, o)
	bs.Discovered = time.Since(t0)
	bs.FilesDiscovered = len(files)
	bs.DiscoveredStats = ds

	for i := range files {
		g.Files = append(g.Files, File{
			path: cgPut(files[i].rel), dir: cgPut(files[i].dir),
			base: cgPut(files[i].base), ext: cgPut(files[i].ext), lang: cgPut("typescript"),
			ModuleID: files[i].moduleID, Bytes: int32(files[i].size),
			Parsed: files[i].parsed, IsTest: files[i].isTest,
			IsGen: files[i].isGen, IsVend: files[i].isVend,
		})
	}
	if !o.Quiet {
		fmt.Printf("  %d typescript files discovered in %.1fs\n", len(files),
			bs.Discovered.Seconds())
	}

	readable := make([]int, 0, len(files))
	for i := range files {
		if !files[i].tooBig {
			readable = append(readable, i)
		}
	}

	t1 := time.Now()
	var nsyms, nerrs, ntsx int
	nsyms, nerrs, ntsx = parseAll(g, files, readable, o, &ds)
	bs.Parsed = time.Since(t1)
	bs.FilesParsed = ds.parsed
	bs.FilesFailed = nerrs
	bs.Symbols = nsyms
	if !o.Quiet {
		fmt.Printf("  %d symbols parsed in %.1fs%s\n", nsyms, bs.Parsed.Seconds(),
			fmtSuffix(nerrs, " file(s) failed"))
	}
	g.setMeta("files_skipped", fmt.Sprintf(
		"big=%d special=%d escaping_symlink=%d denied=%d walk_errors=%d",
		ds.big, ds.special, ds.escaping, ds.denied, ds.walkErr))
	if bs.FilesParsed > 0 && nsyms == 0 {

		fmt.Fprintf(os.Stderr,
			"  WARNING: %d file(s) were read and produced NO symbols. Every\n"+
				"           query below will be empty for that reason, not\n"+
				"           because the code is clean. Check --report for parse errors.\n",
			bs.FilesParsed)
	}

	t3 := time.Now()
	st := g.resolveCalls(&g.pend, g.imported)
	bs.Resolved2 = time.Since(t3)
	bs.Resolved, bs.Unresolved, bs.External = int(st.resolved), int(st.unresolved), int(st.external)

	g.pend = pending{}
	g.imported = nil
	bs.Edges = len(g.Edges)
	bs.Callsites = len(g.Callsites)

	resolveImportTargets(g)
	parseManifests(g, o.Root)
	attachSuppressionSymbols(g)
	buildSigTokens(g)

	t2 := time.Now()
	materialize(g)
	bs.Aggregated = time.Since(t2)
	writeMeta(g, o, bs, ntsx)
	return g, bs, nil
}

func fmtSuffix(n int, s string) string {
	if n == 0 {
		return ""
	}
	return fmt.Sprintf(" (%d %s)", n, s)
}

const (
	tsBatchFiles = 32
	tsBatchBytes = 1 << 20
	tsQueueDepth = 6
)

type cstPart struct {
	fi   int
	off  int32
	ln   int32
	lang int
	has  bool
	pend bool
}

type cstItem struct {
	buf   []byte
	parts []cstPart
}

func tsLangOf(rel string) int {
	if hasSuffix(rel, ".tsx") {
		return tsLangTSX
	}
	return tsLangTS
}

func isCSTDigit(c byte) bool { return c >= '0' && c <= '9' }

func cutCST(buf []byte, dst []cstPart, lang, want int) []cstPart {
	dst = dst[:0]
	pos := 0
	for len(dst) < want {
		for pos < len(buf) {
			j := bytes.IndexByte(buf[pos:], '\n')
			if j < 0 {
				return nil
			}
			line := buf[pos : pos+j]
			if len(line) == 0 || !isCSTDigit(line[0]) {
				pos += j + 1
				continue
			}
			break
		}
		if pos >= len(buf) {
			return nil
		}
		start := pos
		for {
			j := bytes.IndexByte(buf[pos:], '\n')
			if j < 0 {
				return nil
			}
			if j == 0 {
				dst = append(dst, cstPart{off: int32(start),
					ln: int32(pos - start), lang: lang, has: true})
				pos++
				break
			}
			pos += j + 1
		}
	}
	for pos < len(buf) {
		j := bytes.IndexByte(buf[pos:], '\n')
		if j < 0 {
			break
		}
		line := buf[pos : pos+j]
		if len(line) > 0 && isCSTDigit(line[0]) {
			return nil
		}
		pos += j + 1
	}
	return dst
}

func grabBuf(free <-chan []byte) []byte {
	var buf []byte
	select {
	case buf = <-free:
	default:
	}
	if cap(buf) < 1<<16 {
		buf = make([]byte, 0, 1<<16)
	}
	return buf
}

func readAll(files []pendingFile, order []int, o *Options,
	items chan<- cstItem, free <-chan []byte, stat *pipeStat) {
	p := tsParserNew()
	defer p.free()
	stg := newTSStage()
	defer stg.close()

	t0 := time.Now()
	var busy, nchild, nbatch int64

	paths := make([]string, 0, tsBatchFiles)
	cuts := make([]cstPart, 0, tsBatchFiles)
	parts := make([]cstPart, 0, tsBatchFiles)
	one := make([]string, 1)

	for i := 0; i < len(order); {
		stg.clear()
		lang := tsLangOf(files[order[i]].rel)
		nw, nbytes := 1, files[order[i]].size
		for i+nw < len(order) && nw < tsBatchFiles && nbytes < tsBatchBytes {
			fi := order[i+nw]
			if tsLangOf(files[fi].rel) != lang {
				break
			}
			nbytes += files[fi].size
			nw++
		}

		paths = paths[:0]
		parts = parts[:0]
		for n := 0; n < nw; n++ {
			fi := order[i+n]
			pf := &files[fi]
			pf.data = nil
			pf.parsed = false
			pf.denied = false
			if d, err := os.ReadFile(pf.full); err != nil {
				if os.IsPermission(err) {
					pf.denied = true
				}
			} else {
				pf.data = d
				scanBuffer(pf, d, o)
			}
			if pf.parsed {
				paths = append(paths, stg.put(strconv.Itoa(fi), pf.full, pf.data))
				parts = append(parts, cstPart{fi: fi, lang: lang, pend: true})
			} else {
				parts = append(parts, cstPart{fi: fi, lang: lang})
			}
		}
		i += nw

		if len(paths) == 0 {
			items <- cstItem{parts: append([]cstPart(nil), parts...)}
			continue
		}

		buf := grabBuf(free)
		if len(paths) > 1 {
			bs := time.Now()
			out, ok := p.parse(buf[:0], paths, lang)
			busy += int64(time.Since(bs))
			nchild++
			if ok {
				cuts = cutCST(out, cuts, lang, len(paths))
				if len(cuts) == len(paths) {
					nbatch++
					k := 0
					for j := range parts {
						if !parts[j].pend {
							continue
						}
						parts[j].pend = false
						parts[j].off = cuts[k].off
						parts[j].ln = cuts[k].ln
						parts[j].has = true
						k++
					}
					items <- cstItem{buf: out,
						parts: append([]cstPart(nil), parts...)}
					continue
				}
				cuts = cuts[:0]
			}
		}

		k := 0
		for j := range parts {
			pt := parts[j]
			if !pt.pend {
				items <- cstItem{parts: []cstPart{pt}}
				continue
			}
			pf := &files[pt.fi]
			one[0] = paths[k]
			k++
			bs := time.Now()
			out, ok := p.parse(buf[:0], one, lang)
			busy += int64(time.Since(bs))
			nchild++
			if !ok {
				pf.parsed = false
				pf.data = nil
				items <- cstItem{parts: []cstPart{{fi: pt.fi, lang: lang}}}
				out = nil
			} else {
				items <- cstItem{buf: out, parts: []cstPart{{
					fi: pt.fi, off: 0, ln: int32(len(out)), lang: lang,
					has: true}}}
			}
			if out == nil {
				buf = grabBuf(free)
			} else {
				buf = out
			}
		}
	}
	close(items)
	stat.readerWall = int64(time.Since(t0))
	stat.readerBusy = busy
	stat.children = nchild
	stat.nbatch = nbatch
}

type pipeStat struct {
	readerWall, readerBusy int64
	decodeWall, decodeBusy int64
	children, batches      int64
	nbatch                 int64
}

func decodeAll(g *Graph, files []pendingFile, o *Options, ds *discoverStats,
	items <-chan cstItem, free chan<- []byte, stat *pipeStat,
	nsyms, nerrs, ntsx *int) {
	e := newExtractor()
	out := &fileOut{}
	var dec cstDecoder
	t0 := time.Now()
	var busy int64
	for it := range items {
		bs := time.Now()
		for _, pt := range it.parts {
			fi := pt.fi
			pf := &files[fi]
			out.reset()
			f := &g.Files[fi]
			f.sha1 = cgPut(pf.sha)
			f.Lines = pf.nLines
			f.Sloc = pf.nCode
			f.Blank = pf.nBlank
			f.Comment = pf.nComment
			f.MaxLen = pf.maxLen
			f.IsGen = pf.isGen
			f.Parsed = pf.parsed
			if pf.tooBig {
				ds.big++
			}
			if pf.denied {
				ds.denied++
			}
			if pf.parsed {
				ds.parsed++
				ft, err := decodeCST(&dec, it.buf[pt.off:pt.off+pt.ln], pf.data,
					pt.lang)
				if err != nil {
					ft = &tsTree{failed: true}
				}
				if runSafe(e, pf, out, ft) {
					*nerrs++
				}
				if o.KeepTrees && !ft.failed {
					out.tree = &tsTree{cols: ft.cols.clone(), n: ft.n,
						rootHasErr: ft.rootHasErr, lang: uint8(pt.lang)}
				}
			}
			if hasSuffix(pf.rel, ".tsx") {
				*ntsx++
			}
			appendFile(g, out, fi)
			if out.tree != nil {
				g.astTrees[fi] = out.tree
				out.tree = nil
			}
			*nsyms += len(out.syms)
			pf.data = nil
		}
		busy += int64(time.Since(bs))
		stat.batches++
		if cap(it.buf) <= 1<<26 {
			select {
			case free <- it.buf[:0]:
			default:
			}
		}
	}
	stat.decodeWall = int64(time.Since(t0))
	stat.decodeBusy = busy
}

func runSafe(e *extractor, pf *pendingFile, out *fileOut, ft *tsTree) (failed bool) {
	defer func() {
		if r := recover(); r != nil {
			failed = true
			out.reset()
			if os.Getenv("CODEGRAPH_DEBUG") != "" {
				fmt.Fprintf(os.Stderr, "  parse failed: %s: %v\n%s\n", pf.rel, r,
					string(debug.Stack()))
			}
		}
	}()
	e.run(pf, out, ft)
	return false
}

func parseAll(g *Graph, files []pendingFile, order []int, o *Options,
	ds *discoverStats) (nsyms, nerrs, ntsx int) {
	if len(order) == 0 {
		return 0, 0, 0
	}
	if o.KeepTrees {
		g.astTrees = make([]*tsTree, len(g.Files))
	}
	items := make(chan cstItem, tsQueueDepth)
	free := make(chan []byte, tsQueueDepth)
	var stat pipeStat
	var wg sync.WaitGroup
	wg.Go(func() { readAll(files, order, o, items, free, &stat) })
	wg.Go(func() { decodeAll(g, files, o, ds, items, free, &stat, &nsyms, &nerrs, &ntsx) })
	wg.Wait()
	if os.Getenv("CG_PIPELINE") != "" {
		wall := stat.readerWall
		if stat.decodeWall > wall {
			wall = stat.decodeWall
		}
		fmt.Fprintf(os.Stderr,
			"pipeline: files=%d children=%d batches=%d wall=%dms readerBusy=%dms "+
				"decodeBusy=%dms overlap=%.0f%%\n",
			len(order), stat.children, stat.nbatch, wall/1e6,
			stat.readerBusy/1e6, stat.decodeBusy/1e6,
			100*float64(stat.readerBusy+stat.decodeBusy)/float64(maxI64(wall, 1)))
	}
	return nsyms, nerrs, ntsx
}

func maxI64(a, b int64) int64 {
	if a > b {
		return a
	}
	return b
}

func appendFile(g *Graph, o *fileOut, fileIdx int) {

	fid := int32(fileIdx + 1)
	if len(o.syms) > 0 {
		fid = o.syms[0].FileID
	}
	base := int32(len(g.Symbols))
	o.base = base
	gid := func(local int32) int32 { return base + local + 1 }

	for i := range o.syms {
		s := &o.syms[i]
		if s.ParentID >= 0 {
			s.ParentID = gid(s.ParentID)
		}
		s.name = o.reb(s.name)
		s.qualName = o.reb(s.qualName)
		s.vis = o.reb(s.vis)
		s.sig = o.reb(s.sig)
		s.retType = o.reb(s.retType)
		g.Symbols = append(g.Symbols, *s)
	}
	if len(o.syms) == 0 {
		appendFileNoSymbols(g, o, fileIdx, fid)
		return
	}

	first := o.base + 1
	need := first + int32(len(o.syms))
	for int32(len(g.mchunks))*metricChunkRows < need {
		g.mchunks = append(g.mchunks, make([]int32, metricChunkRows*metricCount))
	}
	for i := range o.syms {

		copy(g.metrics(first+int32(i)), o.mvals[i*metricCount:(i+1)*metricCount])
	}

	for i := range o.params {
		o.params[i].SymID = gid(o.params[i].SymID)
		o.params[i].name = o.reb(o.params[i].name)
		o.params[i].typ = o.reb(o.params[i].typ)
		g.Params = append(g.Params, o.params[i])
	}
	for i := range o.fields {
		o.fields[i].SymID = gid(o.fields[i].SymID)
		o.fields[i].name = o.reb(o.fields[i].name)
		o.fields[i].typ = o.reb(o.fields[i].typ)
		g.Fields = append(g.Fields, o.fields[i])
	}
	for i := range o.literals {
		o.literals[i].SymID = gid(o.literals[i].SymID)
		o.literals[i].kind = o.reb(o.literals[i].kind)
		o.literals[i].value = o.reb(o.literals[i].value)
		g.Literals = append(g.Literals, o.literals[i])
	}
	for i := range o.attributes {
		o.attributes[i].SymID = gid(o.attributes[i].SymID)
		o.attributes[i].name = o.reb(o.attributes[i].name)
		o.attributes[i].args = o.reb(o.attributes[i].args)
		g.Attributes = append(g.Attributes, o.attributes[i])
	}
	for i := range o.markers {
		o.markers[i].FileID = fid
		o.markers[i].kind = o.reb(o.markers[i].kind)
		o.markers[i].text = o.reb(o.markers[i].text)
		g.Markers = append(g.Markers, o.markers[i])
	}
	for i := range o.imports {
		o.imports[i].FileID = fid
		o.imports[i].target = o.reb(o.imports[i].target)
		o.imports[i].kind = o.reb(o.imports[i].kind)
		g.Imports = append(g.Imports, o.imports[i])
	}
	for i := range o.hazards {
		o.hazards[i].SymID = gid(o.hazards[i].SymID)
		o.hazards[i].pattern = o.reb(o.hazards[i].pattern)
		o.hazards[i].category = o.reb(o.hazards[i].category)
		g.addHazard(&o.hazards[i])
	}
	for i := range o.enumMembers {
		o.enumMembers[i].SymID = gid(o.enumMembers[i].SymID)
		o.enumMembers[i].name = o.reb(o.enumMembers[i].name)
		o.enumMembers[i].value = o.reb(o.enumMembers[i].value)
		g.EnumMembers = append(g.EnumMembers, o.enumMembers[i])
	}

	for i := range o.tsExports {
		o.tsExports[i].FileID = fid
		o.tsExports[i].name = o.reb(o.tsExports[i].name)
		o.tsExports[i].kind = o.reb(o.tsExports[i].kind)
		o.tsExports[i].source = o.reb(o.tsExports[i].source)
		g.TSExports = append(g.TSExports, o.tsExports[i])
	}
	for i := range o.suppress {
		o.suppress[i].FileID = fid
		o.suppress[i].kind = o.reb(o.suppress[i].kind)
		o.suppress[i].reason = o.reb(o.suppress[i].reason)
		g.Suppress = append(g.Suppress, o.suppress[i])
	}
	for i := range o.typeDefs {
		o.typeDefs[i].SymID = gid(o.typeDefs[i].SymID)
		o.typeDefs[i].extendsName = o.reb(o.typeDefs[i].extendsName)
		g.TypeDefs = append(g.TypeDefs, o.typeDefs[i])
	}
	for i := range o.listeners {
		o.listeners[i].SymID = gid(o.listeners[i].SymID)
		o.listeners[i].FileID = fid
		o.listeners[i].op = o.reb(o.listeners[i].op)
		o.listeners[i].target = o.reb(o.listeners[i].target)
		o.listeners[i].event = o.reb(o.listeners[i].event)
		g.Listeners = append(g.Listeners, o.listeners[i])
	}
	for i := range o.inputSites {
		o.inputSites[i].SymID = gid(o.inputSites[i].SymID)
		o.inputSites[i].FileID = fid
		o.inputSites[i].vr = o.reb(o.inputSites[i].vr)
		o.inputSites[i].kind = o.reb(o.inputSites[i].kind)
		g.InputSites = append(g.InputSites, o.inputSites[i])
	}
	for i := range o.secrets {
		o.secrets[i].SymID = gid(o.secrets[i].SymID)
		o.secrets[i].FileID = fid
		o.secrets[i].value = o.reb(o.secrets[i].value)
		g.Secrets = append(g.Secrets, o.secrets[i])
	}
	for i := range o.awaited {
		o.awaited[i].SymID = gid(o.awaited[i].SymID)
		o.awaited[i].FileID = fid
		o.awaited[i].name = o.reb(o.awaited[i].name)
		o.awaited[i].base = o.reb(o.awaited[i].base)
		g.Awaited = append(g.Awaited, o.awaited[i])
	}
	for i := range o.nameRefs {
		r := &o.nameRefs[i]
		gs := gid(r.local)
		g.byName[r.name] = append(g.byName[r.name],
			nameCand{sid: gs, fid: r.fid, ty: r.typeName})
	}
	for i := range o.qualRefs {
		g.byQual[o.qualRefs[i].qual] = gid(o.qualRefs[i].local)
	}
	for i := range o.pend.Sid {
		g.pend.add(gid(o.pend.Sid[i]), o.pend.Fid[i], o.pend.Line[i],
			o.pend.Name[i], o.pend.Type[i])
	}
	if len(o.importRefs) > 0 {
		m := g.imported[fid]
		if m == nil {
			m = map[string]bool{}
			g.imported[fid] = m
		}
		for i := range o.importRefs {
			m[o.importRefs[i].name] = o.importRefs[i].bare
		}
	}

	if o.hasError {
		g.Files[fileIdx].NErrs = o.nErrors
		g.Files[fileIdx].NMissing = o.nMissing
	}
	if o.langDecl {

		g.Files[fileIdx].lang = cgPut("typescript-decl")
	}
}

func appendFileNoSymbols(g *Graph, o *fileOut, fileIdx int, fid int32) {
	for i := range o.markers {
		o.markers[i].FileID = fid
		o.markers[i].kind = o.reb(o.markers[i].kind)
		o.markers[i].text = o.reb(o.markers[i].text)
		g.Markers = append(g.Markers, o.markers[i])
	}
	for i := range o.imports {
		o.imports[i].FileID = fid
		o.imports[i].target = o.reb(o.imports[i].target)
		o.imports[i].kind = o.reb(o.imports[i].kind)
		g.Imports = append(g.Imports, o.imports[i])
	}
	for i := range o.suppress {
		o.suppress[i].FileID = fid
		o.suppress[i].kind = o.reb(o.suppress[i].kind)
		o.suppress[i].reason = o.reb(o.suppress[i].reason)
		g.Suppress = append(g.Suppress, o.suppress[i])
	}
	for i := range o.tsExports {
		o.tsExports[i].FileID = fid
		o.tsExports[i].name = o.reb(o.tsExports[i].name)
		o.tsExports[i].kind = o.reb(o.tsExports[i].kind)
		o.tsExports[i].source = o.reb(o.tsExports[i].source)
		g.TSExports = append(g.TSExports, o.tsExports[i])
	}
	if o.langDecl {
		g.Files[fileIdx].lang = cgPut("typescript-decl")
	}

	if o.hasError {
		g.Files[fileIdx].NErrs = o.nErrors
		g.Files[fileIdx].NMissing = o.nMissing
	}
}

func (g *Graph) addHazard(h *Hazard) {
	k := pair(h.SymID, patKey(h.Pattern()))
	if ex, ok := g.hazIdx[k]; ok {
		g.Hazards[ex].N += h.N
		return
	}
	g.hazIdx[k] = int32(len(g.Hazards))
	g.Hazards = append(g.Hazards, *h)
}

func defaultWorkers() int { return defaultParseWorkers }

func (e *extractor) newSymbol(o *fileOut, m *meas, name, qual string, kind int8,
	parent int32, ls, le, bs, be int32, sig, ret, vis string) int32 {
	id := int32(len(o.syms))
	o.syms = append(o.syms, Symbol{
		FileID: e.fid, ModuleID: e.mid, ParentID: parent,
		name: e.slab.put(name), qualName: e.slab.put(cutStr(qual, 400)), Kind: kind, vis: e.slab.put(vis),
		LineStart: ls, LineEnd: le, ByteStart: bs, ByteEnd: be,

		sig: e.slab.put(cutStr(sig, 400)), retType: e.slab.put(cutStr(ret, 200)),
	})
	base := len(o.mvals)
	need := base + metricCount
	if need > cap(o.mvals) {
		grown := make([]int32, need, need+metricCount*16)
		copy(grown, o.mvals)
		o.mvals = grown
	} else {
		o.mvals = o.mvals[:need]
		clear(o.mvals[base:need])
	}
	if m != nil {
		row := o.mvals[base:]
		for _, c := range m.touched {
			row[c] = m.vals[c]
		}
	}
	return id
}

func (e *extractor) emitFunction(t *Tree, s srcFile, pf *pendingFile, o *fileOut,
	sc scope, node int, kind int8) int32 {
	name := e.nodeName(t, s, node)
	if name == "" {
		name = "(anonymous)"
	}
	qual := sc.qualPre + name
	body := t.body(node)
	e.measureBody(t, s, body, false)
	m := e.m

	sig := e.signatureOf(t, s, node)

	m.setv(mCyclomatic, m.cyclomatic)
	m.setv(mCognitive, m.cognitive)
	m.setv(mMaxNesting, m.maxNesting)
	m.setv(mMaxLoopDepth, m.maxLoopDepth)
	m.setv(mNTokens, m.nTokens)
	m.setv(mNOperators, m.nOperators)
	m.setv(mNOperands, m.nOperands)
	m.setv(mNDistinctOperators, m.nDistinctOperators)
	m.setv(mNDistinctOperands, m.nDistinctOperands)
	m.setv(mSloc, e.slocOf(s, t.start(node), t.end(node)))
	m.setv(mBodyBytes, int32(t.end(body)-t.start(body)))
	m.setv(mIsGenerated, b2i(pf.isGen))
	e.countParams(t, s, node, m)
	e.functionFlags(t, s, pf, node, m, sig)
	doc := e.docstringLines(t, s, node)
	m.setv(mNDocLines, int32(doc))
	if doc > 0 {
		m.setv(mHasDoc, 1)
	}

	sid := e.newSymbol(o, m, name, qual, kind, sc.symID,
		int32(t.srow(node))+1, int32(t.erow(node))+1,
		int32(t.start(node)), int32(t.end(node)),
		sig, e.returnTypeOf(t, s, node), e.visibilityOf(t, s, node))

	e.emitParams(t, s, node, sid, o)
	e.emitAttributes(t, s, pf, node, sid, o)
	e.addPending(sid, pf.fid, m, sc.typeName, o)
	e.emitHazards(m, sid, o)
	e.emitSecrets(sid, pf, m, o)
	for _, l := range m.lits {
		o.literals = append(o.literals, Literal{
			SymID: sid, FileID: pf.fid, kind: e.slab.put("number"),
			value: e.slab.put(cutStr(l.value, 200)), Line: l.line, IsMagic: true,
		})
	}
	e.emitExtras(sid, pf, m, o)
	o.nameRefs = append(o.nameRefs, nameRef{name: e.intern(name), local: sid,
		fid: pf.fid, mid: pf.moduleID, typeName: sc.typeName})
	o.qualRefs = append(o.qualRefs, qualRef{qual: e.intern(qual), local: sid})
	return sid
}

func (e *extractor) addPending(sid int32, fid int32, m *meas, typeName string, o *fileOut) {
	p := &o.pend
	for i := range m.calls {
		c := &m.calls[i]
		if c.dynamic || c.name == "" {
			continue
		}
		p.add(sid, fid, c.line, c.name, typeName)
	}
}

func (e *extractor) emitExtras(sid int32, pf *pendingFile, m *meas, o *fileOut) {
	for _, r := range m.extras {
		switch r.kind {
		case xListener:
			o.listeners = append(o.listeners, Listener{
				SymID: sid, FileID: pf.fid, op: e.slab.put(r.op), target: e.slab.put(r.target),
				event: e.slab.put(r.second), Line: r.line, InLoop: r.inLoop, IsAsync: r.flag,
			})
		case xInput:
			o.inputSites = append(o.inputSites, InputSite{
				SymID: sid, FileID: pf.fid, vr: e.slab.put(r.name), kind: e.slab.put(r.second),
				Line: r.line, InLoop: r.inLoop,
			})
		case xAwait:
			o.awaited = append(o.awaited, AwaitRow{
				SymID: sid, FileID: pf.fid, name: e.slab.put(r.name), base: e.slab.put(r.second), Line: r.line,
			})
		}
	}
}

func (e *extractor) emitSecrets(sid int32, pf *pendingFile, m *meas, o *fileOut) {
	for _, sc := range m.secrets {
		o.secrets = append(o.secrets, Secret{
			SymID: sid, FileID: pf.fid, value: e.slab.put(sc.value), Line: sc.line,
		})
	}
}

func (e *extractor) emitType(t *Tree, s srcFile, pf *pendingFile, o *fileOut,
	sc scope, node int, kind int8) int32 {
	name := e.nodeName(t, s, node)
	if name == "" {
		name = "(anonymous)"
	}
	qual := sc.qualPre + name
	txt := t.text(node, s)

	body := t.body(node)
	e.measureBody(t, s, body, true)
	m := e.m

	m.setv(mSloc, e.slocOf(s, t.start(node), t.end(node)))
	m.setv(mIsGenerated, b2i(pf.isGen))
	m.setv(mNTokens, m.nTokens)
	m.setv(mNOperators, m.nOperators)
	m.setv(mNOperands, m.nOperands)
	e.typeFlags(t, s, node, m, txt)
	doc := e.docstringLines(t, s, node)
	m.setv(mNDocLines, int32(doc))
	if doc > 0 {
		m.setv(mHasDoc, 1)
	}

	sig := cutStr(cgStrip(beforeBrace(txt)), 300)
	sid := e.newSymbol(o, m, name, qual, kind, sc.symID,
		int32(t.srow(node))+1, int32(t.erow(node))+1,
		int32(t.start(node)), int32(t.end(node)),
		sig, "", e.visibilityOf(t, s, node))

	e.emitAttributes(t, s, pf, node, sid, o)
	e.addPending(sid, pf.fid, m, sc.typeName, o)
	e.emitHazards(m, sid, o)
	e.typeExtra(t, s, node, sid, o, txt)
	o.nameRefs = append(o.nameRefs, nameRef{name: e.intern(name), local: sid,
		fid: pf.fid, mid: pf.moduleID, typeName: sc.typeName})
	o.qualRefs = append(o.qualRefs, qualRef{qual: e.intern(qual), local: sid})
	return sid
}

func beforeBrace(txt string) string {
	for i := 0; i < len(txt); i++ {
		if txt[i] == '{' {
			return txt[:i]
		}
	}
	return txt
}

func (e *extractor) emitModuleScope(t *Tree, s srcFile, pf *pendingFile, o *fileOut) {
	e.measureBody(t, s, 0, true)
	m := e.m
	if len(m.calls) == 0 && m.nTokens < 8 {
		return
	}
	m.setv(mCyclomatic, m.cyclomatic)
	m.setv(mCognitive, m.cognitive)
	m.setv(mMaxNesting, m.maxNesting)
	m.setv(mMaxLoopDepth, m.maxLoopDepth)
	m.setv(mNTokens, m.nTokens)
	m.setv(mNOperators, m.nOperators)
	m.setv(mNOperands, m.nOperands)
	m.setv(mNDistinctOperators, m.nDistinctOperators)
	m.setv(mNDistinctOperands, m.nDistinctOperands)
	m.setv(mIsGenerated, b2i(pf.isGen))
	if pf.isTest {
		m.setv(mIsTest, 1)
	}
	sid := e.newSymbol(o, m, "<module>", pf.rel, kModule, -1,
		int32(t.srow(0))+1, int32(t.erow(0))+1,
		int32(t.start(0)), int32(t.end(0)),
		"top-level statements of "+pf.rel, "", "")
	e.addPending(sid, pf.fid, m, "", o)
	e.emitHazards(m, sid, o)
	e.emitSecrets(sid, pf, m, o)
	for _, l := range m.lits {
		o.literals = append(o.literals, Literal{
			SymID: sid, FileID: pf.fid, kind: e.slab.put("number"),
			value: e.slab.put(cutStr(l.value, 200)), Line: l.line, IsMagic: true,
		})
	}
}

func (e *extractor) countParams(t *Tree, s srcFile, node int, m *meas) {
	p := t.fieldChild(node, t.f().parameters)
	if p < 0 {
		return
	}
	kids, opt := 0, int32(0)
	for c := t.firstChild(p); c >= 0; c = t.nextSibling(c) {

		if t.cols.named[c] == 0 || t.codeAt(c) == cComment {
			continue
		}
		kids++
		if hasPrefix(t.kind(c), "optional") ||
			t.fieldChild(c, t.f().value) >= 0 ||
			t.fieldChild(c, t.f().defaultValue) >= 0 {
			opt++
		}
	}
	m.setv(mNParams, int32(kids))
	m.setv(mNOptionalParams, opt)
}

func hasPrefix(s, p string) bool { return len(s) >= len(p) && s[:len(p)] == p }

func (e *extractor) emitParams(t *Tree, s srcFile, node int, sid int32, o *fileOut) {
	p := t.fieldChild(node, t.f().parameters)
	if p < 0 {
		return
	}
	pos := int32(0)
	for c := t.firstChild(p); c >= 0; c = t.nextSibling(c) {
		if t.cols.named[c] == 0 {
			continue
		}

		if t.codeAt(c) == cComment {
			pos++
			continue
		}
		name := e.nodeName(t, s, c)
		ptype := ""
		if tn := t.fieldChild(c, t.f().typeF); tn >= 0 {
			ptype = s.strStripN(t.start(tn), t.end(tn), 1<<30)
		}
		if name == "" {
			name = s.strStripN(t.start(c), t.end(c), 80)
		}
		o.params = append(o.params, Param{

			SymID: sid, Pos: pos, name: e.slab.put(cutStr(name, 120)),
			typ:     e.slab.put(cutStr(ptype, 200)),
			IsUntyp: ptype == "",
			Depth:   int32(countStr(ptype, "<") + countStr(ptype, "[")),
		})
		pos++
	}
}

func (e *extractor) signatureOf(t *Tree, s srcFile, node int) string {
	end := t.end(node)
	if b := t.fieldChild(node, t.f().body); b >= 0 {
		end = t.start(b)
	}
	return s.strStripN(t.start(node), end, 1<<30)
}

func (e *extractor) returnTypeOf(t *Tree, s srcFile, node int) string {
	r := t.fieldChild(node, t.f().returnType)
	if r < 0 {
		return ""
	}
	return s.strStripN(t.start(r), t.end(r), 1<<30)
}

func (e *extractor) slocOf(s srcFile, a, b int) int32 {
	if a >= b || b > len(s.data) {
		return 0
	}
	seg := s.data[a:b]
	n := 0
	start := 0
	for i := 0; i <= len(seg); i++ {
		if i < len(seg) {
			if c := seg[i]; c != '\n' && c != '\r' && c != '\v' && c != '\f' &&
				c != 0x1c && c != 0x1d && c != 0x1e {
				continue
			}
		}
		line := seg[start:i]
		if s.ascii {
			t := cgStripBytes(line)
			if len(t) > 0 && slocLine(string(t)) {
				n++
			}
		} else {
			t := cgStrip(string(line))
			if t != "" && slocLine(t) {
				n++
			}
		}
		start = i + 1
		if i < len(seg) && seg[i] == '\r' && i+1 < len(seg) && seg[i+1] == '\n' {
			i++
		}
	}
	return int32(n)
}

var docPrefixes = []string{"///", "/**", "##", `"""`, "'''", "#'", "--|"}

func (e *extractor) docstringLines(t *Tree, s srcFile, node int) int32 {
	var n int32
	prev := t.prevSibling(node)
	for prev >= 0 {
		if t.codeAt(prev) != cComment {
			break
		}
		txt := s.str(t.start(prev), t.end(prev))
		if hasAnyPrefix(txt, docPrefixes) {
			n += int32(t.erow(prev) - t.srow(prev) + 1)
		} else if n == 0 && t.erow(prev)+1 >= t.srow(node) {
			n += int32(t.erow(prev) - t.srow(prev) + 1)
		} else {
			break
		}
		prev = t.prevSibling(prev)
	}
	return n
}

func hasAnyPrefix(s string, ps []string) bool {
	for _, p := range ps {
		if hasPrefix(s, p) {
			return true
		}
	}
	return false
}

const nullEnc = "\\N"

type lineWriter struct {
	w   *bufio.Writer
	buf []byte

	wide    []wideMetric
	widePos int
}

func (lw *lineWriter) wideAt(id int32, col int) (int64, bool) {
	for lw.widePos < len(lw.wide) && lw.wide[lw.widePos].id < id {
		lw.widePos++
	}
	if lw.widePos < len(lw.wide) {
		w := &lw.wide[lw.widePos]
		if w.id == id && w.col == col {
			return w.val, true
		}
	}
	return 0, false
}

func newLineWriter(w io.Writer) *lineWriter {
	return &lineWriter{w: bufio.NewWriterSize(w, 1<<20), buf: make([]byte, 0, 8192)}
}

func (lw *lineWriter) s(fields ...string) {
	lw.buf = append(lw.buf[:0], 'R', ' ')
	for i, f := range fields {
		if i > 0 {
			lw.buf = append(lw.buf, ' ')
		}
		lw.buf = append(lw.buf, f...)
	}
	lw.buf = append(lw.buf, '\n')
	lw.w.Write(lw.buf)
}

func (lw *lineWriter) sid(idx int, fields ...string) {
	lw.buf = append(lw.buf[:0], 'R', ' ', 'i', ':')
	lw.buf = strconv.AppendInt(lw.buf, int64(idx+1), 10)
	for _, f := range fields {
		lw.buf = append(lw.buf, ' ')
		lw.buf = append(lw.buf, f...)
	}
	lw.buf = append(lw.buf, '\n')
	lw.w.Write(lw.buf)
}

func iEnc(v int) string { return "i:" + strconv.Itoa(v) }

func iEncOpt(v int32, present bool) string {
	if !present {
		return nullEnc
	}
	return "i:" + strconv.Itoa(int(v))
}

func fEnc(f float64) string { return "f:" + cgFloat(f) }

func bEnc(b bool) string {
	if b {
		return "i:1"
	}
	return "i:0"
}

func tEncOpt(s string, present bool) string {
	if !present {
		return nullEnc
	}
	return tEnc(s)
}

const hexUpper = "0123456789ABCDEF"

func tEnc(s string) string {
	if !utf8.ValidString(s) {

		s = cgDecode([]byte(s))
	}
	plain := true
	for i := 0; i < len(s); i++ {
		c := s[i]
		if c == '\\' || c == '\n' || c == '\t' || c == '\r' || c < 0x20 || c == 0x7f {
			plain = false
			break
		}
	}
	if plain {
		b := make([]byte, len(s)+2)
		b[0] = 's'
		b[1] = ':'
		copy(b[2:], s)
		return string(b)
	}
	b := make([]byte, 0, len(s)+8)
	b = append(b, 's', ':')
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
			if c < 0x20 || c == 0x7f {
				b = append(b, '\\', 'x', hexUpper[c>>4], hexUpper[c&15])
			} else {
				b = append(b, c)
			}
		}
	}
	return string(b)
}

func emitFile(w *lineWriter, idx int, f *File) {
	w.buf = append(w.buf[:0], 'R', ' ', 'i', ':')
	w.buf = strconv.AppendInt(w.buf, int64(idx+1), 10)
	put := func(s string) {
		w.buf = append(w.buf, ' ')
		w.buf = append(w.buf, s...)
	}
	put(tEnc(f.Path()))
	put(tEnc(f.Dir()))
	put(tEnc(f.Basename()))
	put(tEnc(f.Ext()))
	put(tEnc(f.Lang()))
	put(iEnc(int(f.ModuleID)))
	put(iEnc(int(f.Bytes)))
	put(iEnc(int(f.Lines)))
	put(iEnc(int(f.Sloc)))
	put(iEnc(int(f.Blank)))
	put(iEnc(int(f.Comment)))
	put(iEnc(int(f.DocLines)))
	put(iEnc(int(f.MaxLen)))
	put(tEnc(f.Sha1()))
	put(bEnc(f.Parsed))
	put(bEnc(f.IsTest))
	put(bEnc(f.IsGen))
	put(bEnc(f.IsVend))
	put(iEnc(int(f.NErrs)))
	put(iEnc(int(f.NMissing)))
	put(fEnc(0))
	put(iEnc(int(f.NSymbols)))
	put(iEnc(int(f.NFuncs)))
	put(iEnc(int(f.NTypes)))
	put(iEnc(int(f.NImports)))
	put(iEnc(int(f.TotalCyc)))
	put(iEnc(int(f.MaxCyc)))
	put(iEnc(int(f.TotalRisk)))
	w.buf = append(w.buf, '\n')
	w.w.Write(w.buf)
}

func emitTSConfig(w *lineWriter, idx int, c *TSConfig) {
	w.sid(idx, tEnc(c.Path()), tEnc(c.Dir()),
		tEncOpt(c.Extends(), c.HasExtends), bEnc(c.Strict), bEnc(c.NoImplAny),
		bEnc(c.NullChecks), bEnc(c.UncheckedIx), bEnc(c.ExactOpt),
		bEnc(c.Verbatim), bEnc(c.Isolated), bEnc(c.Erasable),
		iEnc(int(c.NStrict)), tEnc(c.Target()), tEnc(c.Module()), tEnc(c.Resolution()),
		tEncOpt(c.Removed(), c.HasRemoved), tEncOpt(c.BaseURL(), c.HasBaseURL),
		tEncOpt(c.PathsJSON(), c.HasPaths))
}

func emitSymbol(w *lineWriter, g *Graph, idx int) {
	s := &g.Symbols[idx]
	m := g.metrics(int32(idx + 1))
	b := w.buf[:0]
	b = append(b, 'R', ' ', 'i', ':')
	b = strconv.AppendInt(b, int64(idx+1), 10)
	put := func(v string) {
		b = append(b, ' ')
		b = append(b, v...)
	}
	put(iEnc(int(s.FileID)))
	put(iEnc(int(s.ModuleID)))
	if s.ParentID < 0 {
		put(nullEnc)
	} else {
		put(iEnc(int(s.ParentID)))
	}
	put(tEnc(s.Name()))
	put(tEnc(s.QualName()))
	put(tEnc(kindNames[s.Kind]))
	put(iEnc(int(s.LineStart)))
	put(iEnc(int(s.LineEnd)))
	put(iEnc(int(s.LineEnd - s.LineStart + 1)))
	put(iEnc(int(s.ByteStart)))
	put(iEnc(int(s.ByteEnd)))
	put(tEnc(s.Sig()))
	put(tEnc(s.RetType()))
	put(tEnc(s.Vis()))
	id := int32(idx + 1)
	for i := range metricCount {
		b = append(b, ' ', 'i', ':')
		if v, ok := w.wideAt(id, i); ok {
			b = strconv.AppendInt(b, v, 10)
			continue
		}
		b = strconv.AppendInt(b, int64(m[i]), 10)
	}
	b = append(b, '\n')
	w.w.Write(b)
	w.buf = b[:0]
}

func dumpTo(g *Graph, w io.Writer) error {
	lw := newLineWriter(w)
	lw.wide = g.wide
	all := tables()
	order := make([]int, len(all))
	for i := range order {
		order[i] = i
	}
	sort.Slice(order, func(a, b int) bool { return all[order[a]].name < all[order[b]].name })
	for _, ti := range order {
		t := all[ti]
		n := t.rows()
		lw.w.WriteString("T " + t.name + " " + strconv.Itoa(t.ncols) + " " + strconv.Itoa(n) + "\n")
		if t.identical != "" {
			line := "R " + t.identical + "\n"
			for range n {
				lw.w.WriteString(line)
			}
		} else if n > 0 {
			keys := make([]string, n)
			for i := range n {
				keys[i] = t.key(i)
			}
			perm := make([]int32, n)
			for i := range perm {
				perm[i] = int32(i)
			}
			sort.Slice(perm, func(a, b int) bool { return keys[perm[a]] < keys[perm[b]] })
			for _, p := range perm {
				t.emit(lw, int(p))
			}
		}
		lw.w.WriteString("E " + t.name + "\n")
	}
	return lw.w.Flush()
}

func startProfiling(c *cli) func() {
	var closers []func()
	if c.cpuProfile != "" {
		f, err := os.Create(c.cpuProfile)
		if err != nil {
			fmt.Fprintf(os.Stderr, "cpuprofile: %v\n", err)
		} else {
			pprof.StartCPUProfile(f)
			closers = append(closers, func() {
				pprof.StopCPUProfile()
				f.Close()
				reportProfile(c.cpuProfile, "cpu")
			})
		}
	}
	if c.blockProfile != "" {
		runtime.SetBlockProfileRate(1)
		f, err := os.Create(c.blockProfile)
		if err != nil {
			fmt.Fprintf(os.Stderr, "blockprofile: %v\n", err)
		} else {
			closers = append(closers, func() {
				pprof.Lookup("block").WriteTo(f, 0)
				f.Close()
				runtime.SetBlockProfileRate(0)
				reportProfile(c.blockProfile, "block")
			})
		}
	}
	if c.mutexProfile != "" {
		runtime.SetMutexProfileFraction(1)
		f, err := os.Create(c.mutexProfile)
		if err != nil {
			fmt.Fprintf(os.Stderr, "mutexprofile: %v\n", err)
		} else {
			closers = append(closers, func() {
				pprof.Lookup("mutex").WriteTo(f, 0)
				f.Close()
				runtime.SetMutexProfileFraction(0)
				reportProfile(c.mutexProfile, "mutex")
			})
		}
	}
	if c.traceProfile != "" {
		f, err := os.Create(c.traceProfile)
		if err != nil {
			fmt.Fprintf(os.Stderr, "trace: %v\n", err)
		} else {
			if err := trace.Start(f); err != nil {
				fmt.Fprintf(os.Stderr, "trace: %v\n", err)
				f.Close()
			} else {
				closers = append(closers, func() {
					trace.Stop()
					fmt.Fprintf(os.Stderr, "goroutines at exit: %d\n",
						runtime.NumGoroutine())
					f.Close()
					reportProfile(c.traceProfile, "trace")
				})
			}
		}
	}
	return func() {
		for _, closer := range slices.Backward(closers) {
			closer()
		}
	}
}

func writeMemProfile(path string) {
	f, err := os.Create(path)
	if err != nil {
		fmt.Fprintf(os.Stderr, "memprofile: %v\n", err)
		return
	}
	defer f.Close()
	runtime.GC()
	if err := pprof.WriteHeapProfile(f); err != nil {
		fmt.Fprintf(os.Stderr, "memprofile: %v\n", err)
		return
	}
	reportProfile(path, "heap")
}

func reportProfile(path, kind string) {
	fi, err := os.Stat(path)
	if err != nil {
		return
	}
	if fi.Size() == 0 {
		fmt.Fprintf(os.Stderr,
			"profile %s: EMPTY -- %s profiling captured nothing, so treat any\n"+
				"  conclusion drawn from it as unmeasured rather than as a result.\n",
			path, kind)
		return
	}
	fmt.Fprintf(os.Stderr, "profile %s: %d bytes written\n", path, fi.Size())
}

const (
	langName   = "typescript"
	targetName = "TypeScript 7.0 (own parser; tsc has no public API before 7.1)"
	schemaVer  = 1
)

var usageText = `usage: codegraph-typescript [-h] [--module MODULE] [--limit LIMIT]
                          [--list] [--metrics] [--schema] [--report]
                          [--csv N] [--json N] [--save PATH] [--save-ast PATH]
                          [--load-ast PATH] [--force] [--deps]
                          [--install-deps] [--include-generated]
                          [--include-vendored] [--no-tests] [--quiet]
                          [--version] [--dump PATH] [--workers N]
                          [--cpuprofile PATH] [--memprofile PATH]
                          [--blockprofile PATH] [--mutexprofile PATH]
                          [--trace PATH]
                          [root] [which ...]

Parse a typescript tree into a graph and query it in one shot. Target: ` + targetName + `

every run re-parses from source; nothing is cached, so an answer can never
describe code that has moved on.  --save-ast PATH writes the parsed state
(trees, tables, strings) to a binary file after the run's parse; --load-ast
PATH restores that state instead of parsing, and answers from it.  The two
flags are mutually exclusive.
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

func main() {
	os.Exit(run(os.Args[1:]))
}

func run(argv []string) int {
	c, err := parseArgs(argv)
	if err != nil {
		fmt.Fprintf(os.Stderr, "%v\n", err)
		fmt.Fprint(os.Stderr, usageText)
		return 2
	}
	if c.version {
		fmt.Printf("codegraph_typescript  target=%s  schema=v%d  go=%s  "+
			"tree-sitter=%s\n", targetName, schemaVer,
			runtime.Version(), tsGrammarVersion)
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
	if c.save != "" {
		fmt.Fprintln(os.Stderr, "codegraph-typescript: --save writes a SQLite "+
			"database and this build has no SQL layer, so there is nothing to "+
			"save. Use --dump PATH to write the canonical table dump instead.")
		return 2
	}
	if c.loadAST == "" {
		if st, err := os.Stat(c.root); err != nil || !st.IsDir() {
			fmt.Fprintf(os.Stderr, "not a directory: %s\n", c.root)
			return 2
		}
	}

	gogc := 25
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
		Quiet: c.quiet, Workers: c.workers, KeepTrees: c.saveAST != "",
	}
	t0 := time.Now()
	var g *Graph
	var bs *BuildStats
	if c.loadAST != "" {
		profLoad := os.Getenv("CG_LOADALLOC") != ""
		var a0, m0 uint64
		if profLoad {
			a0, m0 = cgAllocSnap()
		}
		t1 := time.Now()
		g, err = loadAST(c.loadAST)
		if err != nil {
			fmt.Fprintf(os.Stderr, "load-ast: %v\n", err)
			return 2
		}
		if profLoad {
			a1, m1 := cgAllocSnap()
			fmt.Fprintf(os.Stderr, "load-alloc: total_bytes=%d mallocs=%d wall=%.3fs\n",
				a1-a0, m1-m0, time.Since(t1).Seconds())
		}
		if err != nil {
			fmt.Fprintf(os.Stderr, "load-ast: %v\n", err)
			return 2
		}
		setGraph(g)
		nParsed := 0
		for i := range g.Files {
			if g.Files[i].Parsed {
				nParsed++
			}
		}
		bs = &BuildStats{FilesParsed: nParsed}
	} else {
		g, bs, err = build(opts)
		if err != nil {
			fmt.Fprintf(os.Stderr, "%v\n", err)
			return 2
		}
	}
	if os.Getenv("CG_TREECHECK") != "" {
		cgTreeCheck(g)
	}
	took := time.Since(t0)

	if c.saveAST != "" {
		if _, serr := os.Lstat(c.saveAST); serr == nil && !c.force {
			fmt.Fprintf(os.Stderr, "refusing to overwrite %s (pass --force)\n", c.saveAST)
			return 2
		}
		ts := time.Now()
		profSave := os.Getenv("CG_SAVEALLOC") != ""
		var a0, m0 uint64
		if profSave {
			a0, m0 = cgAllocSnap()
		}
		nb, werr := saveASTFile(g, c.saveAST)
		if werr != nil {
			fmt.Fprintf(os.Stderr, "save-ast: %v\n", werr)
			return 2
		}
		sw := time.Since(ts)
		if profSave {
			a1, m1 := cgAllocSnap()
			fmt.Fprintf(os.Stderr, "save-alloc: total_bytes=%d mallocs=%d wall=%.3fs size=%d\n",
				a1-a0, m1-m0, sw.Seconds(), nb)
		}
		if !c.quiet {
			fmt.Fprintf(os.Stderr, "ast state written to %s: %d bytes in %.1fs\n",
				c.saveAST, nb, sw.Seconds())
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
	return 0
}

func parseArgs(argv []string) (*cli, error) {
	c := &cli{root: ".", module: "%", limit: -1, workers: defaultWorkers()}
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
	fmt.Println("codegraph-typescript dependencies")
	fmt.Println("  the official `tree-sitter` CLI binary on PATH (or $TREE_SITTER_BIN),")
	fmt.Println("  with the pinned tree-sitter-typescript checkout (v0.23.2, which")
	fmt.Println("  carries both the typescript and tsx grammars) registered under")
	fmt.Println("  ~/.config/tree-sitter/config.json -- `./setup.sh` checks all of")
	fmt.Println("  this and regenerates the kind tables. The CLI is spawned per file;")
	fmt.Println("  there is no C in this build, and the program refuses to run without")
	fmt.Println("  the CLI rather than emitting an empty graph -- an empty graph reads")
	fmt.Println("  exactly like a clean repository.")
}

const cgasMagic = "CGAS"

const (
	cgasVersion  = 3
	cgasHeaderSz = 32
	cgasSecSz    = 24
	cgasNSec     = 31
	cgasArenaLo  = 1 << 20
	cgasTreeTS   = 0
	cgasTreeTSX  = 1
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
	cgasSecEdges
	cgasSecCallsites
	cgasSecUnres
	cgasSecImps
	cgasSecHaz
	cgasSecAttrs
	cgasSecLits
	cgasSecEnums
	cgasSecMarks
	cgasSecExports
	cgasSecSuppress
	cgasSecTSConfigs
	cgasSecDeps
	cgasSecSigToks
	cgasSecTypeDefs
	cgasSecListeners
	cgasSecUISites
	cgasSecSecs
	cgasSecAwaited
	cgasSecMeta
	cgasSecMetrics
	cgasSecWide
	cgasSecByName
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

type cgasNameRow struct {
	name cgStr
	Sid  int32
	Fid  int32
	ty   cgStr
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
	fail(tsRecBytes == 50, "node record payload must be the 50-byte v2 columnar stride")
	ct := reflect.TypeOf(tsCols{})
	fail(ct.NumField() == len(tsColWidths), "node column count must match the stored widths table")
	for i := range tsColWidths {
		w := ct.Field(i).Type.Elem().Size()
		fail(uint64(w) == tsColWidths[i],
			fmt.Sprintf("node column %s is %d bytes, the format stores %d",
				ct.Field(i).Name, w, tsColWidths[i]))
	}
	sum := uint64(0)
	for _, w := range tsColWidths {
		sum += w
	}
	fail(sum == tsRecBytes, "node column widths must sum to the record payload")
	fail(unsafe.Sizeof(cgasSRef{}) == 16, "cgasSRef must overlay a string header")
	fail(unsafe.Sizeof(cgStr{}) == 16, "cgStr must be the 16-byte {offset,length} pair")
	fail(unsafe.Sizeof(wideMetric{}) == 24, "wideMetric must be the 24-byte fixed stride")
	fail(unsafe.Sizeof(cgasNameRow{}) == 40, "cgasNameRow must be the 40-byte fixed stride")
	pins := []struct {
		t    reflect.Type
		want int64
	}{
		{reflect.TypeOf(Symbol{}), 128},
		{reflect.TypeOf(Module{}), 64},
		{reflect.TypeOf(File{}), 168},
		{reflect.TypeOf(Param{}), 48},
		{reflect.TypeOf(Field{}), 56},
		{reflect.TypeOf(Edge{}), 16},
		{reflect.TypeOf(Callsite{}), 12},
		{reflect.TypeOf(Unresolved{}), 32},
		{reflect.TypeOf(Import{}), 64},
		{reflect.TypeOf(Hazard{}), 48},
		{reflect.TypeOf(AttrRow{}), 48},
		{reflect.TypeOf(Literal{}), 48},
		{reflect.TypeOf(EnumMember{}), 48},
		{reflect.TypeOf(Marker{}), 48},
		{reflect.TypeOf(MetaRow{}), 32},
		{reflect.TypeOf(TSExport{}), 72},
		{reflect.TypeOf(Suppression{}), 56},
		{reflect.TypeOf(TSConfig{}), 184},
		{reflect.TypeOf(DepRow{}), 56},
		{reflect.TypeOf(SigToken{}), 24},
		{reflect.TypeOf(TypeDef{}), 56},
		{reflect.TypeOf(Listener{}), 64},
		{reflect.TypeOf(InputSite{}), 48},
		{reflect.TypeOf(Secret{}), 32},
		{reflect.TypeOf(AwaitRow{}), 48},
		{reflect.TypeOf(cgasNameRow{}), 40},
	}
	for _, p := range pins {
		fail(uint64(p.t.Size()) == uint64(p.want),
			fmt.Sprintf("%s is %d bytes, the deterministic layout pins %d",
				p.t.String(), p.t.Size(), p.want))
		var cur int64
		for i := 0; i < p.t.NumField(); i++ {
			f := p.t.Field(i)
			fail(int64(f.Offset) == cur,
				fmt.Sprintf("%s has an unnamed %d-byte hole before field %s -- "+
					"add an explicit named pad field so appended rows stay deterministic",
					p.t.String(), int64(f.Offset)-cur, f.Name))
			cur += int64(f.Type.Size())
		}
		fail(cur == int64(p.t.Size()),
			fmt.Sprintf("%s tail padding is not covered by named fields", p.t.String()))
	}
	for _, t := range append([]reflect.Type{
		reflect.TypeOf(Edge{}),
		reflect.TypeOf(Callsite{}),
		reflect.TypeOf(wideMetric{}),
		reflect.TypeOf(cgasSRef{}),
		reflect.TypeOf(cgStr{}),
		reflect.TypeOf(cgasNameRow{}),
		reflect.TypeOf(int32(0)),
		reflect.TypeOf(int64(0)),
		reflect.TypeOf(uint32(0)),
	}, reflect.TypeOf(Symbol{}), reflect.TypeOf(File{}), reflect.TypeOf(Module{}),
		reflect.TypeOf(TSConfig{}), reflect.TypeOf(Listener{}), reflect.TypeOf(TypeDef{})) {
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
	case *Symbol:
		return []uintptr{unsafe.Offsetof(Symbol{}.name), unsafe.Offsetof(Symbol{}.qualName),
			unsafe.Offsetof(Symbol{}.vis), unsafe.Offsetof(Symbol{}.sig),
			unsafe.Offsetof(Symbol{}.retType)}
	case *Module:
		return []uintptr{unsafe.Offsetof(Module{}.name), unsafe.Offsetof(Module{}.kind)}
	case *File:
		return []uintptr{unsafe.Offsetof(File{}.path), unsafe.Offsetof(File{}.dir),
			unsafe.Offsetof(File{}.base), unsafe.Offsetof(File{}.ext),
			unsafe.Offsetof(File{}.lang), unsafe.Offsetof(File{}.sha1)}
	case *Param:
		return []uintptr{unsafe.Offsetof(Param{}.name), unsafe.Offsetof(Param{}.typ)}
	case *Field:
		return []uintptr{unsafe.Offsetof(Field{}.name), unsafe.Offsetof(Field{}.typ)}
	case *Unresolved:
		return []uintptr{unsafe.Offsetof(Unresolved{}.name)}
	case *Import:
		return []uintptr{unsafe.Offsetof(Import{}.target), unsafe.Offsetof(Import{}.kind)}
	case *Hazard:
		return []uintptr{unsafe.Offsetof(Hazard{}.pattern), unsafe.Offsetof(Hazard{}.category)}
	case *AttrRow:
		return []uintptr{unsafe.Offsetof(AttrRow{}.name), unsafe.Offsetof(AttrRow{}.args)}
	case *Literal:
		return []uintptr{unsafe.Offsetof(Literal{}.kind), unsafe.Offsetof(Literal{}.value)}
	case *EnumMember:
		return []uintptr{unsafe.Offsetof(EnumMember{}.name), unsafe.Offsetof(EnumMember{}.value)}
	case *Marker:
		return []uintptr{unsafe.Offsetof(Marker{}.kind), unsafe.Offsetof(Marker{}.text)}
	case *MetaRow:
		return []uintptr{unsafe.Offsetof(MetaRow{}.K), unsafe.Offsetof(MetaRow{}.V)}
	case *TSExport:
		return []uintptr{unsafe.Offsetof(TSExport{}.name), unsafe.Offsetof(TSExport{}.kind),
			unsafe.Offsetof(TSExport{}.source)}
	case *Suppression:
		return []uintptr{unsafe.Offsetof(Suppression{}.kind), unsafe.Offsetof(Suppression{}.reason)}
	case *TSConfig:
		return []uintptr{unsafe.Offsetof(TSConfig{}.path), unsafe.Offsetof(TSConfig{}.dir),
			unsafe.Offsetof(TSConfig{}.extends), unsafe.Offsetof(TSConfig{}.target),
			unsafe.Offsetof(TSConfig{}.module), unsafe.Offsetof(TSConfig{}.resolution),
			unsafe.Offsetof(TSConfig{}.removed), unsafe.Offsetof(TSConfig{}.baseURL),
			unsafe.Offsetof(TSConfig{}.pathsJSON)}
	case *DepRow:
		return []uintptr{unsafe.Offsetof(DepRow{}.name), unsafe.Offsetof(DepRow{}.version),
			unsafe.Offsetof(DepRow{}.dir)}
	case *SigToken:
		return []uintptr{unsafe.Offsetof(SigToken{}.token)}
	case *TypeDef:
		return []uintptr{unsafe.Offsetof(TypeDef{}.extendsName)}
	case *Listener:
		return []uintptr{unsafe.Offsetof(Listener{}.op), unsafe.Offsetof(Listener{}.target),
			unsafe.Offsetof(Listener{}.event)}
	case *InputSite:
		return []uintptr{unsafe.Offsetof(InputSite{}.vr), unsafe.Offsetof(InputSite{}.kind)}
	case *Secret:
		return []uintptr{unsafe.Offsetof(Secret{}.value)}
	case *AwaitRow:
		return []uintptr{unsafe.Offsetof(AwaitRow{}.name), unsafe.Offsetof(AwaitRow{}.base)}
	case *cgasNameRow:
		return []uintptr{unsafe.Offsetof(cgasNameRow{}.name), unsafe.Offsetof(cgasNameRow{}.ty)}
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

func cgAllocSnap() (uint64, uint64) {
	runtime.GC()
	var m runtime.MemStats
	runtime.ReadMemStats(&m)
	return m.TotalAlloc, m.Mallocs
}

func cgTreeCheck(g *Graph) {
	fnv := uint32(2166136261)
	fold := func(v uint64) {
		for i := 0; i < 8; i++ {
			fnv ^= uint32(byte(v >> (i * 8)))
			fnv *= 16777619
		}
	}
	nRecs := 0
	nTrees := 0
	sumVisits := uint64(0)
	for ti, tr := range g.astTrees {
		if tr == nil {
			continue
		}
		nTrees++
		n := tr.n
		nRecs += n
		c := &tr.cols
		for i := 0; i < n; i++ {
			fold(uint64(c.sym[i]))
			fold(uint64(c.field[i]))
			fold(uint64(c.start[i]))
			fold(uint64(c.end[i]))
			fold(uint64(c.srow[i]))
			fold(uint64(c.scol[i]))
			fold(uint64(c.erow[i]))
			fold(uint64(c.ecol[i]))
			fold(uint64(int32(c.parent[i])) & 0xffffffff)
			fold(uint64(int32(c.first[i])) & 0xffffffff)
			fold(uint64(int32(c.next[i])) & 0xffffffff)
			fold(uint64(int32(c.subEnd[i])) & 0xffffffff)
			fold(uint64(c.nchild[i]))
			fold(uint64(c.nnamed[i]))
			fold(uint64(c.named[i]))
			fold(uint64(c.missing[i]))
		}
		stack := make([]int32, 0, 256)
		seen := make([]uint8, n)
		visits := 0
		for i := 0; i < n; i++ {
			if c.parent[i] != -1 {
				p := int(c.parent[i])
				if p < 0 || p >= n || p == i {
					panic(fmt.Sprintf("treewalk: tree %d node %d has bad parent %d", ti, i, p))
				}
				continue
			}
			stack = append(stack[:0], int32(i))
			for len(stack) > 0 {
				x := stack[len(stack)-1]
				stack = stack[:len(stack)-1]
				if x < 0 || x >= int32(n) {
					panic(fmt.Sprintf("treewalk: tree %d link escapes to %d", ti, x))
				}
				if seen[x] == 1 {
					panic(fmt.Sprintf("treewalk: tree %d node %d reached twice", ti, x))
				}
				seen[x] = 1
				visits++
				kids := 0
				for y := c.first[x]; y >= 0; y = c.next[y] {
					if y >= int32(n) {
						panic(fmt.Sprintf("treewalk: tree %d next overrun at %d", ti, y))
					}
					if c.parent[y] != x {
						panic(fmt.Sprintf("treewalk: tree %d child %d of %d has parent %d",
							ti, y, x, c.parent[y]))
					}
					kids++
					if kids > int(c.nchild[x]) {
						panic(fmt.Sprintf("treewalk: tree %d node %d chain longer than nchild %d",
							ti, x, c.nchild[x]))
					}
					stack = append(stack, y)
				}
				if kids != int(c.nchild[x]) {
					panic(fmt.Sprintf("treewalk: tree %d node %d chain %d != nchild %d",
						ti, x, kids, c.nchild[x]))
				}
			}
		}
		if visits != n {
			panic(fmt.Sprintf("treewalk: tree %d visited %d of %d records", ti, visits, n))
		}
		sumVisits += uint64(visits)
	}
	fmt.Fprintf(os.Stderr, "treewalk: trees=%d records=%d visits=%d stride=%d fnv=%08x\n",
		nTrees, nRecs, sumVisits, tsRecBytes, fnv)
}

func saveASTFile(g *Graph, path string) (int64, error) {
	cgasGuard()
	arena := cgArena
	names := make([]string, 0, len(g.byName))
	for name := range g.byName {
		names = append(names, name)
	}
	sort.Strings(names)
	nameRows := make([]cgasNameRow, 0, len(names))
	for _, name := range names {
		for _, c := range g.byName[name] {
			nameRows = append(nameRows, cgasNameRow{name: cgPut(name), Sid: c.sid, Fid: c.fid, ty: cgPut(c.ty)})
		}
	}
	arena = cgArena
	nSyms := len(g.Symbols)
	nMetricBytes := nSyms * metricCount * 4
	body := make([][]byte, cgasNSec)
	body[cgasSecFiles-1] = cgasBytes(g.Files)
	body[cgasSecMods-1] = cgasBytes(g.Modules)
	body[cgasSecSyms-1] = cgasBytes(g.Symbols)
	body[cgasSecParams-1] = cgasBytes(g.Params)
	body[cgasSecFields-1] = cgasBytes(g.Fields)
	body[cgasSecEdges-1] = cgasBytes(g.Edges)
	body[cgasSecCallsites-1] = cgasBytes(g.Callsites)
	body[cgasSecUnres-1] = cgasBytes(g.Unresolved)
	body[cgasSecImps-1] = cgasBytes(g.Imports)
	body[cgasSecHaz-1] = cgasBytes(g.Hazards)
	body[cgasSecAttrs-1] = cgasBytes(g.Attributes)
	body[cgasSecLits-1] = cgasBytes(g.Literals)
	body[cgasSecEnums-1] = cgasBytes(g.EnumMembers)
	body[cgasSecMarks-1] = cgasBytes(g.Markers)
	body[cgasSecExports-1] = cgasBytes(g.TSExports)
	body[cgasSecSuppress-1] = cgasBytes(g.Suppress)
	body[cgasSecTSConfigs-1] = cgasBytes(g.TSConfigs)
	body[cgasSecDeps-1] = cgasBytes(g.Deps)
	body[cgasSecSigToks-1] = cgasBytes(g.SigTokens)
	body[cgasSecTypeDefs-1] = cgasBytes(g.TypeDefs)
	body[cgasSecListeners-1] = cgasBytes(g.Listeners)
	body[cgasSecUISites-1] = cgasBytes(g.InputSites)
	body[cgasSecSecs-1] = cgasBytes(g.Secrets)
	body[cgasSecAwaited-1] = cgasBytes(g.Awaited)
	body[cgasSecMeta-1] = cgasBytes(g.Meta)
	body[cgasSecWide-1] = cgasBytes(g.wide)
	body[cgasSecByName-1] = cgasBytes(nameRows)
	body[cgasSecStrings-1] = arena
	stride := uint64(tsRecBytes)
	totalRecs := uint64(0)
	for i := range g.astTrees {
		if tr := g.astTrees[i]; tr != nil {
			totalRecs += uint64(tr.n)
		}
	}
	tDir := make([]byte, 12+5*len(g.astTrees))
	cgPutU64(tDir[0:8], 0, stride)
	cgPutU32(tDir[8:12], 0, uint32(len(g.astTrees)))
	for i := range g.astTrees {
		n := uint32(0)
		fl := uint8(0)
		if tr := g.astTrees[i]; tr != nil {
			n = uint32(tr.n)
			fl = tr.lang & 1
			if tr.rootHasErr {
				fl |= 2
			}
		}
		cgPutU32(tDir[12+4*i:], 0, n)
		tDir[12+4*len(g.astTrees)+i] = fl
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
			ln = uint64(nMetricBytes)
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
			for k := range tsColWidths {
				for _, tr := range g.astTrees {
					if tr == nil || tr.n == 0 {
						continue
					}
					if _, err := w.Write(tr.cols.colBytes(k, tr.n)); err != nil {
						return failW(err)
					}
				}
			}
		} else if i+1 == int(cgasSecMetrics) {
			left := nSyms
			for ci, ch := range g.mchunks {
				if left <= 0 {
					break
				}
				take := metricChunkRows
				lo := 0
				if ci == 0 {
					take = metricChunkRows - 1
					lo = 1
				}
				if take > left {
					take = left
				}
				if _, err := w.Write(cgasBytes(ch[lo*metricCount : (lo+take)*metricCount])); err != nil {
					return failW(err)
				}
				left -= take
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
		return nil, bad("unsupported state format version %d, want %d -- v2 files carry Go-string rows patched at load and cannot be read by this offset-native build; re-parse with --save-ast --force", v, cgasVersion)
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
	cgMu.Lock()
	cgArena = arena
	cgMu.Unlock()
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
	syms, err := cgasDecodeRows[Symbol](mem, off, ln, "symbols")
	if err != nil {
		return decErr(err)
	}
	if err := cgasCheckStrRefs(syms, al, "symbols"); err != nil {
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
	off, ln = dec(cgasSecEdges)
	edges, err := cgasDecodeRows[Edge](mem, off, ln, "edges")
	if err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecCallsites)
	callsites, err := cgasDecodeRows[Callsite](mem, off, ln, "call sites")
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
	imports, err := cgasDecodeRows[Import](mem, off, ln, "imports")
	if err != nil {
		return decErr(err)
	}
	if err := cgasCheckStrRefs(imports, al, "imports"); err != nil {
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
	off, ln = dec(cgasSecAttrs)
	attrs, err := cgasDecodeRows[AttrRow](mem, off, ln, "attributes")
	if err != nil {
		return decErr(err)
	}
	if err := cgasCheckStrRefs(attrs, al, "attributes"); err != nil {
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
	off, ln = dec(cgasSecEnums)
	enums, err := cgasDecodeRows[EnumMember](mem, off, ln, "enum members")
	if err != nil {
		return decErr(err)
	}
	if err := cgasCheckStrRefs(enums, al, "enum members"); err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecMarks)
	marks, err := cgasDecodeRows[Marker](mem, off, ln, "markers")
	if err != nil {
		return decErr(err)
	}
	if err := cgasCheckStrRefs(marks, al, "markers"); err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecExports)
	exports, err := cgasDecodeRows[TSExport](mem, off, ln, "exports")
	if err != nil {
		return decErr(err)
	}
	if err := cgasCheckStrRefs(exports, al, "exports"); err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecSuppress)
	suppress, err := cgasDecodeRows[Suppression](mem, off, ln, "suppressions")
	if err != nil {
		return decErr(err)
	}
	if err := cgasCheckStrRefs(suppress, al, "suppressions"); err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecTSConfigs)
	tsconfigs, err := cgasDecodeRows[TSConfig](mem, off, ln, "tsconfig rows")
	if err != nil {
		return decErr(err)
	}
	if err := cgasCheckStrRefs(tsconfigs, al, "tsconfig rows"); err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecDeps)
	deps, err := cgasDecodeRows[DepRow](mem, off, ln, "dependencies")
	if err != nil {
		return decErr(err)
	}
	if err := cgasCheckStrRefs(deps, al, "dependencies"); err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecSigToks)
	sigToks, err := cgasDecodeRows[SigToken](mem, off, ln, "signature tokens")
	if err != nil {
		return decErr(err)
	}
	if err := cgasCheckStrRefs(sigToks, al, "signature tokens"); err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecTypeDefs)
	typeDefs, err := cgasDecodeRows[TypeDef](mem, off, ln, "type defs")
	if err != nil {
		return decErr(err)
	}
	if err := cgasCheckStrRefs(typeDefs, al, "type defs"); err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecListeners)
	listeners, err := cgasDecodeRows[Listener](mem, off, ln, "listeners")
	if err != nil {
		return decErr(err)
	}
	if err := cgasCheckStrRefs(listeners, al, "listeners"); err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecUISites)
	uis, err := cgasDecodeRows[InputSite](mem, off, ln, "input sites")
	if err != nil {
		return decErr(err)
	}
	if err := cgasCheckStrRefs(uis, al, "input sites"); err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecSecs)
	secs2, err := cgasDecodeRows[Secret](mem, off, ln, "secrets")
	if err != nil {
		return decErr(err)
	}
	if err := cgasCheckStrRefs(secs2, al, "secrets"); err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecAwaited)
	awaited, err := cgasDecodeRows[AwaitRow](mem, off, ln, "awaited rows")
	if err != nil {
		return decErr(err)
	}
	if err := cgasCheckStrRefs(awaited, al, "awaited rows"); err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecMeta)
	meta, err := cgasDecodeRows[MetaRow](mem, off, ln, "meta")
	if err != nil {
		return decErr(err)
	}
	if err := cgasCheckStrRefs(meta, al, "meta"); err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecMetrics)
	mflat, err := cgasDecodeRows[int32](mem, off, ln, "metric columns")
	if err != nil {
		return decErr(err)
	}
	if len(mflat) != len(syms)*metricCount {
		return nil, bad("metric column count %d, want %d", len(mflat), len(syms)*metricCount)
	}
	off, ln = dec(cgasSecWide)
	wide, err := cgasDecodeRows[wideMetric](mem, off, ln, "wide metrics")
	if err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecByName)
	nameRows, err := cgasDecodeRows[cgasNameRow](mem, off, ln, "name index")
	if err != nil {
		return decErr(err)
	}
	if err := cgasCheckStrRefs(nameRows, al, "name index"); err != nil {
		return decErr(err)
	}
	tOff, tLn := secs[cgasSecTrees].Off, secs[cgasSecTrees].Len
	dOff, dLn := secs[cgasSecTreeDir].Off, secs[cgasSecTreeDir].Len
	if dLn < 12 {
		return nil, bad("node record directory too small (%d bytes)", dLn)
	}
	dirBytes := mem[dOff : dOff+dLn]
	declBytes := cgGetU64(dirBytes, 0)
	nTreeFiles := int(cgGetU32(dirBytes, 8))
	if declBytes != tsRecBytes {
		return nil, bad("node record payload %d bytes per record, want %d", declBytes, int64(tsRecBytes))
	}
	if nTreeFiles != len(files) {
		return nil, bad("node record directory covers %d files, graph has %d", nTreeFiles, len(files))
	}
	if int(dLn) < 12+5*nTreeFiles {
		return nil, bad("node record directory too small for %d files", nTreeFiles)
	}
	counts := unsafe.Slice((*uint32)(unsafe.Pointer(&dirBytes[12])), nTreeFiles)
	flags := dirBytes[12+4*nTreeFiles:]
	colsAll, cerr := tsColsFromMem(mem, int64(tOff), int64(tLn))
	if cerr != nil {
		return nil, bad("%v", cerr)
	}
	g := newGraph()
	g.astBlob = mem
	g.Files = files
	g.Modules = mods
	g.Symbols = syms
	g.Params = params
	g.Fields = fields
	g.Edges = edges
	g.Callsites = callsites
	g.Unresolved = unres
	g.Imports = imports
	g.Hazards = haz
	g.Attributes = attrs
	g.Literals = lits
	g.EnumMembers = enums
	g.Markers = marks
	g.TSExports = exports
	g.Suppress = suppress
	g.TSConfigs = tsconfigs
	g.Deps = deps
	g.SigTokens = sigToks
	g.TypeDefs = typeDefs
	g.Listeners = listeners
	g.InputSites = uis
	g.Secrets = secs2
	g.Awaited = awaited
	g.Meta = meta
	g.wide = wide
	need := int32(len(g.Symbols)) + 1
	for int32(len(g.mchunks))*metricChunkRows < need {
		g.mchunks = append(g.mchunks, make([]int32, metricChunkRows*metricCount))
	}
	for i := 0; i < len(g.Symbols); i++ {
		copy(g.metrics(int32(i+1)), mflat[i*metricCount:(i+1)*metricCount])
	}
	for i := range nameRows {
		r := &nameRows[i]
		g.byName[r.name.Str()] = append(g.byName[r.name.Str()], nameCand{sid: r.Sid, fid: r.Fid, ty: r.ty.Str()})
	}
	g.astTrees = make([]*tsTree, nTreeFiles)
	nRecs := len(colsAll.sym)
	base := 0
	for i := 0; i < nTreeFiles; i++ {
		n := int(counts[i])
		if base+n > nRecs {
			return nil, bad("node record directory overruns the record arena")
		}
		if n > 0 {
			fl := flags[i]
			if fl&^uint8(3) != 0 {
				return nil, bad("tree %d carries unknown flags %#x", i, fl)
			}
			g.astTrees[i] = &tsTree{cols: colsAll.win(base, n), n: n,
				rootHasErr: fl&2 != 0, lang: fl & 1}
		}
		base += n
	}
	if base != nRecs {
		return nil, bad("node record arena has %d unused records", nRecs-base)
	}
	return g, nil
}
