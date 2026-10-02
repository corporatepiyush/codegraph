package main

import (
	"bufio"
	"bytes"
	"crypto/sha1"
	"encoding/csv"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"io"
	"io/fs"
	"maps"
	"math"
	"os"
	"path/filepath"
	"reflect"
	"runtime"
	"runtime/debug"
	"slices"
	"sort"
	"strconv"
	"strings"
	"sync"
	"sync/atomic"
	"syscall"
	"time"
	"unicode"
	"unsafe"
)

type arena struct {
	buf []byte
	off []int32
}

func (a *arena) add(s string) int32 {
	start := int32(len(a.buf))
	a.buf = append(a.buf, s...)
	a.off = append(a.off, int32(len(a.buf)))
	return start
}

func (a *arena) str(i int32) string {
	if i < 0 {
		return ""
	}
	end := a.off[i]
	start := int32(0)
	if i > 0 {
		start = a.off[i-1]
	}
	return string(a.buf[start:end])
}

type symArena struct{ arena }

type File struct {
	ID            int32
	pad1          uint32
	path, dir     cgStr
	basename, ext cgStr
	lang          cgStr
	ModuleID      int32
	Bytes         int32
	Lines         int32
	Sloc          int32
	BlankLines    int32
	CommentLines  int32
	DocLines      int32
	MaxLineLen    int32
	sha1          cgStr
	Parsed        int32
	IsTest        int32
	IsGenerated   int32
	IsVendored    int32
	NParseErrors  int32
	NMissingNodes int32
	ParseMs       float64

	NSymbols   int32
	NFunctions int32
	NTypes     int32
	NImports   int32
	TotalCyclo int32
	MaxCyclo   int32
	TotalRisk  int32
	pad2       uint32
}

func (f *File) Path() string     { return f.path.Str() }
func (f *File) Dir() string      { return f.dir.Str() }
func (f *File) Basename() string { return f.basename.Str() }
func (f *File) Ext() string      { return f.ext.Str() }
func (f *File) Lang() string     { return f.lang.Str() }
func (f *File) Sha1() string     { return f.sha1.Str() }

type Module struct {
	ID          int32
	pad1        uint32
	name, kind  cgStr
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

type symW struct {
	ID            int32
	FileID        int32
	ModuleID      int32
	Name          string
	QualName      string
	Kind          string
	LineStart     int32
	Signature     string
	ReturnType    string
	HasSignature  bool
	HasReturnType bool

	NParams int32

	IsPublic, IsStatic     int32
	IsAbstract, IsOverride int32
	IsTest, IsEntrypoint   int32
	IsGenerated            int32

	Sloc, NCommentLines, HasDoc int32

	Cyclomatic, Cognitive, MaxNesting     int32
	NTokens, NOperators, NOperands        int32
	NDistinctOperators, NDistinctOperands int32

	NLoops, NBranches, NReturns int32
	NSwitch, NCases             int32
	NLabels, NGotos             int32

	MaxLoopDepth, CallInLoop, AllocInLoop, IOInLoop int32
	LockInLoop, BranchInLoop                        int32

	NLocals, NCmp, NArith int32
	NShift                int32
	NFloatLit, NMagic     int32
	NNullCheck            int32

	NCalls, NDynamicCalls, NUnresolvedCalls int32
	FanIn, FanOut, NCallsites               int32
	IsRecursive                             int32

	RiskScore    int32
	NMemory      int32
	NAlloc       int32
	NIO          int32
	NStdio       int32
	NExec        int32
	NLibm        int32
	NInteger     int32
	NConcurrency int32
	NReentrancy  int32

	IsInline, IsVariadic               int32
	NPtrLocals, NDeref, NCast, NSizeof int32
	NIntrinsic, NAtomic, NRestrict     int32
	NLikely, NBuiltin                  int32

	rare int32
}

type Symbol struct {
	ID            int32
	FileID        int32
	ModuleID      int32
	name          cgStr
	qualName      cgStr
	kind          cgStr
	LineStart     int32
	signature     cgStr
	returnType    cgStr
	HasSignature  bool
	HasReturnType bool

	NParams int32

	IsPublic, IsStatic     int32
	IsAbstract, IsOverride int32
	IsTest, IsEntrypoint   int32
	IsGenerated            int32

	Sloc, NCommentLines, HasDoc int32

	Cyclomatic, Cognitive, MaxNesting     int32
	NTokens, NOperators, NOperands        int32
	NDistinctOperators, NDistinctOperands int32

	NLoops, NBranches, NReturns int32
	NSwitch, NCases             int32
	NLabels, NGotos             int32

	MaxLoopDepth, CallInLoop, AllocInLoop, IOInLoop int32
	LockInLoop, BranchInLoop                        int32

	NLocals, NCmp, NArith int32
	NShift                int32
	NFloatLit, NMagic     int32
	NNullCheck            int32

	NCalls, NDynamicCalls, NUnresolvedCalls int32
	FanIn, FanOut, NCallsites               int32
	IsRecursive                             int32

	RiskScore    int32
	NMemory      int32
	NAlloc       int32
	NIO          int32
	NStdio       int32
	NExec        int32
	NLibm        int32
	NInteger     int32
	NConcurrency int32
	NReentrancy  int32

	IsInline, IsVariadic               int32
	NPtrLocals, NDeref, NCast, NSizeof int32
	NIntrinsic, NAtomic, NRestrict     int32
	NLikely, NBuiltin                  int32

	rare int32
}

func (s *Symbol) Name() string       { return s.name.Str() }
func (s *Symbol) QualName() string   { return s.qualName.Str() }
func (s *Symbol) Kind() string       { return s.kind.Str() }
func (s *Symbol) Signature() string  { return s.signature.Str() }
func (s *Symbol) ReturnType() string { return s.returnType.Str() }

type symRare struct {
	SwitchInLoop, LibmInLoop, DivInLoop         int32
	StrlenInLoop                                int32
	RetNull, RetNeg, RetZero, RetVal, RetVoid   int32
	NFnptrCalls, NMacroCalls                    int32
	NExternalCalls                              int32
	NFree, NConstCast, NToctou                  int32
	NLockAcquire, NLockRelease                  int32
	NNarrowCast, NSignCmp, NVariadicFmt         int32
	NMemcpy, NAllocsite                         int32
	NGlobalWrite                                int32
	NErrno, NWeakRandom, NShiftVar              int32
	NReallocSelf, NVla, NGetenv                 int32
	NAssertSide                                 int32
	NFreeThenUse                                int32
	NEpoll, NUring, NKqueue, NEventWait         int32
	NEtReg, NOneshotReg, NWriteReady            int32
	NErrFlag, NRearm, NDereg, NEagain, NEintr   int32
	NUringRes, NUringRing, NUringBarrier        int32
	NUringSqpoll                                int32
	NNonblockSet, NEventCreate, NEventDestroy   int32
	NUringSqe, NUringSeen, NUringUdata          int32
	NUringLink, NUringStreamOps, NUringTeardown int32
	NEvTimeoutIndefinite, NEvTimeoutZero        int32
	NEvBatchOne, NKqTimer, NKqTimerZeroData     int32
	NKqReceipt                                  int32
	NRetNegCheck, NDomainGuard, NUcharCast      int32
	NErrnoZero, NEndptr, NVaEnd, NMapFailed     int32
	NMonotonicClock, NStackszArray              int32
	NPtrOvfCheck, NCallocTransposed, NVaArgArr  int32
}

type symDrop struct {
	BodyBytes                        int32
	HalsteadVolume, Maintainability  int32
	IsLeaf, IsRoot                   int32
	LineEnd, NLines, NDocLines       int32
	NEarlyReturns                    int32
	NControl, NHazards, NUniqueCalls int32
	NExternDeclCalls                 int32
	Visibility                       string
	NAddrof, NAllocsiteNoSizeof      int32
	NArrow, NAssign, NBitop          int32
	NCompoundAssign, NIncdec         int32
	NGlobalRead                      int32
	NLogical, NMemberAccess          int32
	NPtrParams, NStaticAssert        int32
	NStringLit, NSubscript           int32
	NTernary, NVolatile              int32
}

type symBuild struct {
	symW
	symRare
	symDrop
}

var zeroRare symRare

func (g *Graph) rv(s *Symbol) *symRare {
	if s.rare < 0 {
		return &zeroRare
	}
	return &g.rare[s.rare]
}

func (g *Graph) rw(i int) *symRare {
	s := g.Symbols[i]
	if s.rare < 0 {
		g.rare = append(g.rare, symRare{})
		s.rare = int32(len(g.rare)) - 1
	}
	return &g.rare[s.rare]
}

type paramW struct {
	SymbolID, Pos   int32
	Name            string
	HasName         bool
	Type            string
	DefaultValue    string
	HasDefaultValue bool
	IsOptional      int32
	IsVariadic      int32
	IsRef           int32
	IsMutable       int32
	IsNullable      int32
	IsGeneric       int32
	IsUntyped       int32
	TypeDepth       int32
}

type Param struct {
	SymbolID, Pos   int32
	name            cgStr
	HasName         bool
	pad1            [7]byte
	typ             cgStr
	def             cgStr
	HasDefaultValue bool
	pad2            [7]byte
	IsOptional      int32
	IsVariadic      int32
	IsRef           int32
	IsMutable       int32
	IsNullable      int32
	IsGeneric       int32
	IsUntyped       int32
	TypeDepth       int32
}

func (p *Param) Name() string    { return p.name.Str() }
func (p *Param) Type() string    { return p.typ.Str() }
func (p *Param) Default() string { return p.def.Str() }

type fieldW struct {
	SymbolID, Ordinal     int32
	Name, Type            string
	Visibility            string
	Line                  int32
	IsStatic, IsConst     int32
	IsMutable, IsNullable int32
	IsCollection          int32
	IsUntyped             int32
	HasDefault            int32
	TypeDepth             int32
}

type Field struct {
	SymbolID, Ordinal     int32
	name, typ, vis        cgStr
	Line                  int32
	pad1                  uint32
	IsStatic, IsConst     int32
	IsMutable, IsNullable int32
	IsCollection          int32
	IsUntyped             int32
	HasDefault            int32
	TypeDepth             int32
}

func (f *Field) Name() string { return f.name.Str() }
func (f *Field) Type() string { return f.typ.Str() }
func (f *Field) Vis() string  { return f.vis.Str() }

type localW struct {
	SymbolID, Ordinal  int32
	Name, Type         string
	Line               int32
	IsConst, IsMutable int32
	IsUntyped          int32
	HasInit, InLoop    int32
	ScopeDepth         int32
}

type Local struct {
	SymbolID, Ordinal  int32
	name, typ          cgStr
	Line               int32
	IsConst, IsMutable int32
	IsUntyped          int32
	HasInit, InLoop    int32
	ScopeDepth         int32
}

func (l *Local) Name() string { return l.name.Str() }
func (l *Local) Type() string { return l.typ.Str() }

type Edge struct {
	CallerID, CalleeID           int32
	NCalls, SameFile, SameModule int32
	IsSelf                       int32
}

type Callsite struct{ CallerID, CalleeID, Line int32 }

type Unresolved struct {
	CallerID  int32
	pad1      uint32
	name      cgStr
	N         int32
	FirstLine int32
}

func (u *Unresolved) Name() string { return u.name.Str() }

type Import struct {
	ID                     int32
	FileID                 int32
	target                 cgStr
	TargetID               int32
	HasTargetID            bool
	pad1                   uint32
	alias                  cgStr
	HasAlias               bool
	pad2                   [7]byte
	kind                   cgStr
	Line                   int32
	IsExternal, IsRelative int32
	IsWildcard, IsTypeOnly int32
	IsDynamic, NNames      int32
}

func (i *Import) Target() string { return i.target.Str() }
func (i *Import) Alias() string  { return i.alias.Str() }
func (i *Import) Kind() string   { return i.kind.Str() }

type Hazard struct {
	SymbolID  int32
	pad1      uint32
	pattern   cgStr
	category  cgStr
	N         int32
	FirstLine int32
}

func (h *Hazard) Pattern() string  { return h.pattern.Str() }
func (h *Hazard) Category() string { return h.category.Str() }

type Attribute struct {
	ID          int32
	SymbolID    int32
	HasSymbolID bool
	pad1        [7]byte
	FileID      int32
	pad2        uint32
	name        cgStr
	args        cgStr
	HasArgs     bool
	pad3        [7]byte
	Line        int32
	pad4        uint32
}

func (a *Attribute) Name() string { return a.name.Str() }
func (a *Attribute) Args() string { return a.args.Str() }

type Literal struct {
	ID       int32
	SymbolID int32
	HasSym   bool
	pad1     [7]byte
	FileID   int32
	pad2     uint32
	kind     cgStr
	value    cgStr
	Line     int32
	IsMagic  int32
}

func (l *Literal) Kind() string  { return l.kind.Str() }
func (l *Literal) Value() string { return l.value.Str() }

type EnumMember struct {
	SymbolID, Ordinal int32
	name              cgStr
	value             cgStr
	HasValue          bool
	pad1              [7]byte
	NFields           int32
	pad2              uint32
}

func (e *EnumMember) Name() string  { return e.name.Str() }
func (e *EnumMember) Value() string { return e.value.Str() }

type Marker struct {
	ID       int32
	FileID   int32
	SymbolID int32
	HasSym   bool
	pad1     uint32
	kind     cgStr
	Line     int32
	pad2     uint32
	text     cgStr
}

func (m *Marker) Kind() string { return m.kind.Str() }
func (m *Marker) Text() string { return m.text.Str() }

type LayoutRow struct {
	SymbolID, Ordinal  int32
	ByteOff, ByteSize  int32
	PadBefore, Exact   int32
	PtrDepth, ArrayLen int32
	IsFnptr, Depth     int32
	InUnion            int32
}

type StructSize struct {
	SymbolID, TotalSize, TailPad, TotalPad int32
	MaxAlign, Exact, NLines64              int32
}

type Declaration struct {
	ID     int32
	FileID int32
	name   cgStr
	Line   int32
	pad1   uint32
}

func (d *Declaration) Name() string { return d.name.Str() }

type AddrTaken struct {
	ID       int32
	SymbolID int32
	HasSym   bool
	pad1     [7]byte
	FileID   int32
	pad2     uint32
	name     cgStr
	Line     int32
	pad3     uint32
	kind     cgStr
}

func (a *AddrTaken) Name() string { return a.name.Str() }
func (a *AddrTaken) Kind() string { return a.kind.Str() }

type SecretCandidate struct {
	ID       int32
	SymbolID int32
	HasSym   bool
	pad1     [7]byte
	FileID   int32
	pad2     uint32
	value    cgStr
	Line     int32
	pad3     uint32
}

func (s *SecretCandidate) Value() string { return s.value.Str() }

type AllocSite struct {
	ID       int32
	SymbolID int32
	FileID   int32
	pad1     uint32
	fn       cgStr
	sizeExpr cgStr
	Line     int32
	pad2     uint32
}

func (a *AllocSite) Fn() string       { return a.fn.Str() }
func (a *AllocSite) SizeExpr() string { return a.sizeExpr.Str() }

type Memop struct {
	ID                int32
	SymbolID          int32
	FileID            int32
	pad1              uint32
	fn                cgStr
	dst, src, sizeArg cgStr
	sizeBuf, dstTail  cgStr
	Line              int32
	pad2              uint32
}

func (m *Memop) Fn() string      { return m.fn.Str() }
func (m *Memop) Dst() string     { return m.dst.Str() }
func (m *Memop) Src() string     { return m.src.Str() }
func (m *Memop) SizeArg() string { return m.sizeArg.Str() }
func (m *Memop) SizeBuf() string { return m.sizeBuf.Str() }
func (m *Memop) DstTail() string { return m.dstTail.Str() }

type Macro struct {
	SymbolID       int32
	IsFunctionlike int32
	NParams        int32
	pad1           uint32
	body           cgStr
	HasBody        bool
	pad2           [7]byte
	BodyLen        int32
	IsMultiline    int32
	NUses          int32
	pad3           uint32
}

func (m *Macro) Body() string { return m.body.Str() }

type Global struct {
	ID         int32
	FileID     int32
	ModuleID   int32
	pad1       uint32
	name       cgStr
	typ        cgStr
	Line       int32
	IsStatic   int32
	IsConst    int32
	IsVolatile int32
	IsAtomic   int32
	IsArray    int32
	PtrDepth   int32
	HasInit    int32
}

func (g *Global) Name() string { return g.name.Str() }
func (g *Global) Type() string { return g.typ.Str() }

type ConfigBlock struct {
	ID        int32
	FileID    int32
	directive cgStr
	expr      cgStr
	Line      int32
	IsConfig  int32
}

func (c *ConfigBlock) Directive() string { return c.directive.Str() }
func (c *ConfigBlock) Expr() string      { return c.expr.Str() }

type Reach struct {
	SymbolID, NTransitive, NTransitiveOut int32
}

type MakefileRule struct {
	ID     int32
	pad1   uint32
	path   cgStr
	rule   cgStr
	Line   int32
	NObjs  int32
	NSrcs  int32
	UsesAr int32
}

func (r *MakefileRule) Path() string { return r.path.Str() }
func (r *MakefileRule) Rule() string { return r.rule.Str() }

type LockRow struct {
	ID       int32
	SymbolID int32
	FileID   int32
	pad1     uint32
	name     cgStr
	Line     int32
	pad2     uint32
}

func (l *LockRow) Name() string { return l.name.Str() }

type EventOp struct {
	ID       int32
	SymbolID int32
	FileID   int32
	pad1     uint32
	family   cgStr
	fn       cgStr
	args     cgStr
	Line     int32
	pad2     uint32
}

func (e *EventOp) Family() string { return e.family.Str() }
func (e *EventOp) Fn() string     { return e.fn.Str() }
func (e *EventOp) Args() string   { return e.args.Str() }

type APIUse struct {
	ID       int32
	SymbolID int32
	FileID   int32
	pad1     uint32
	ns       cgStr
	fn       cgStr
	Line     int32
	pad2     uint32
}

func (a *APIUse) NS() string { return a.ns.Str() }
func (a *APIUse) Fn() string { return a.fn.Str() }

type IncludeCycle struct {
	ID           int32
	pad1         uint32
	aPath, bPath cgStr
	Length       int32
	pad2         uint32
	members      cgStr
}

func (c *IncludeCycle) APath() string   { return c.aPath.Str() }
func (c *IncludeCycle) BPath() string   { return c.bPath.Str() }
func (c *IncludeCycle) Members() string { return c.members.Str() }

type hazardW struct {
	SymbolID  int32
	Pattern   string
	Category  string
	N         int32
	FirstLine int32
}

type attrW struct {
	ID          int32
	SymbolID    int32
	HasSymbolID bool
	FileID      int32
	Name        string
	Args        string
	HasArgs     bool
	Line        int32
}

type importW struct {
	ID                     int32
	FileID                 int32
	Target                 string
	TargetID               int32
	HasTargetID            bool
	Alias                  string
	HasAlias               bool
	Kind                   string
	Line                   int32
	IsExternal, IsRelative int32
	IsWildcard, IsTypeOnly int32
	IsDynamic, NNames      int32
}

type literalW struct {
	ID       int32
	SymbolID int32
	HasSym   bool
	FileID   int32
	Kind     string
	Value    string
	Line     int32
	IsMagic  int32
}

type enumW struct {
	SymbolID, Ordinal int32
	Name              string
	Value             string
	HasValue          bool
	NFields           int32
}

type markerW struct {
	ID       int32
	FileID   int32
	SymbolID int32
	HasSym   bool
	Kind     string
	Line     int32
	Text     string
}

type declW struct {
	ID     int32
	FileID int32
	Name   string
	Line   int32
}

type addrW struct {
	ID       int32
	SymbolID int32
	HasSym   bool
	FileID   int32
	Name     string
	Line     int32
	Kind     string
}

type secretW struct {
	ID       int32
	SymbolID int32
	HasSym   bool
	FileID   int32
	Value    string
	Line     int32
}

type allocW struct {
	ID       int32
	SymbolID int32
	FileID   int32
	Fn       string
	SizeExpr string
	Line     int32
}

type memopW struct {
	ID                int32
	SymbolID          int32
	FileID            int32
	Fn                string
	Dst, Src, SizeArg string
	SizeBuf, DstTail  string
	Line              int32
}

type macroW struct {
	SymbolID       int32
	IsFunctionlike int32
	NParams        int32
	Body           string
	HasBody        bool
	BodyLen        int32
	IsMultiline    int32
	NUses          int32
}

type globalW struct {
	ID         int32
	FileID     int32
	ModuleID   int32
	Name       string
	Type       string
	Line       int32
	IsStatic   int32
	IsConst    int32
	IsVolatile int32
	IsAtomic   int32
	IsArray    int32
	PtrDepth   int32
	HasInit    int32
}

type cfgW struct {
	ID        int32
	FileID    int32
	Directive string
	Expr      string
	Line      int32
	IsConfig  int32
}

type lockW struct {
	ID       int32
	SymbolID int32
	FileID   int32
	Name     string
	Line     int32
}

type evopW struct {
	ID       int32
	SymbolID int32
	FileID   int32
	Family   string
	Fn       string
	Args     string
	Line     int32
}

type apiuseW struct {
	ID       int32
	SymbolID int32
	FileID   int32
	NS       string
	Fn       string
	Line     int32
}

type fileOut struct {
	symA                      *symBlock
	symLo, symN               int32
	rareN                     int32
	params                    []paramW
	fields                    []fieldW
	locals                    []localW
	literals                  []literalW
	markers                   []markerW
	attrs                     []attrW
	imports                   []importW
	hazards                   []hazardW
	enums                     []enumW
	layout                    []LayoutRow
	ssize                     []StructSize
	decls                     []declW
	addrs                     []addrW
	secrets                   []secretW
	allocs                    []allocW
	memops                    []memopW
	macros                    []macroW
	macroNames                []string
	globals                   []globalW
	cfgs                      []cfgW
	locks                     []lockW
	evops                     []evopW
	apiuses                   []apiuseW
	pendSID, pendFID, pendMID []int32
	pendName                  []string
	pendLine                  [][]int32
	globalNames               []string

	funcs []fnSite
}

const symChunk = 2048

type symBlock struct {
	chunks [][]symW

	rare []symRare
}

func newSymBlockN(n int) *symBlock {
	if n < 1 {
		n = 1
	}
	return &symBlock{chunks: [][]symW{make([]symW, 0, n)}}
}

func (a *symBlock) add(s *symW) {
	n := len(a.chunks)
	if n == 0 || len(a.chunks[n-1]) == cap(a.chunks[n-1]) {
		a.chunks = append(a.chunks, make([]symW, 0, symChunk))
		n++
	}
	a.chunks[n-1] = append(a.chunks[n-1], *s)
}

func (a *symBlock) addRare(r symRare) int32 {
	a.rare = append(a.rare, r)
	return int32(len(a.rare) - 1)
}

func (a *symBlock) count() int32 {
	t := int32(0)
	for _, c := range a.chunks {
		t += int32(len(c))
	}
	return t
}

func (a *symBlock) at(lo, n int32) []symW {
	if n == 0 {
		return nil
	}
	if len(a.chunks) == 1 && int(lo)+int(n) <= len(a.chunks[0]) {
		return a.chunks[0][lo : lo+n]
	}
	out := make([]symW, 0, n)
	for int32(len(out)) < n {
		p := lo + int32(len(out))
		off := int32(0)
		ci := 0
		for ci < len(a.chunks) && off+int32(len(a.chunks[ci])) <= p {
			off += int32(len(a.chunks[ci]))
			ci++
		}
		if ci >= len(a.chunks) {
			break
		}
		co := p - off
		take := min(int32(len(a.chunks[ci]))-co, n-int32(len(out)))
		out = append(out, a.chunks[ci][co:co+take]...)
	}
	return out
}

type fnSite struct {
	name string
	sid  int32
	fid  int32
	mid  int32
}

type Graph struct {
	Modules []Module
	Files   []File

	Symbols  []*Symbol
	symStore []Symbol

	rare           []symRare
	Params         []Param
	Fields         []Field
	Locals         []Local
	Literals       []Literal
	Markers        []Marker
	Attrs          []Attribute
	Imports        []Import
	Hazards        []Hazard
	EnumMem        []EnumMember
	Layout         []LayoutRow
	SSize          []StructSize
	Decls          []Declaration
	Addr           []AddrTaken
	Secrets        []SecretCandidate
	Allocs         []AllocSite
	Memops         []Memop
	Macros         []Macro
	Globals        []Global
	Cfgs           []ConfigBlock
	Reach          []Reach
	MkRules        []MakefileRule
	Locks          []LockRow
	EvOps          []EventOp
	APIUses        []APIUse
	apiByID        map[int32][]int32
	symsCache      []*Symbol
	symsCacheOrder string
	byNameCache    []*Symbol
	Cycles         []IncludeCycle
	Edges          []Edge
	Callsites      []Callsite
	Unres          []Unresolved

	Meta map[string]string

	byFile     map[int32][]int32
	byName     map[string][]int32
	fileByRel  map[string]int32
	fileByBase map[string]int32

	dumpW *bufio.Writer

	astBlob []byte
	trees   []cgTree

	EdgesN, MacroN, ExternN, DeclN, UnresN int32
	CallsTotal                             int32
	AddrPruned                             int32
	MakefilesRead                          int32
	FilesSkippedBig                        int32
	FilesSkippedSpecial                    int32
	FilesSkippedEscape                     int32
	FilesSkippedDenied                     int32
	WalkErrors                             int32
	FilesParsed                            int32
	FilesFailed                            int32
}

func itoa(v int) string { return strconv.Itoa(v) }

func realpath(p string) string {
	r, err := filepath.EvalSymlinks(p)
	if err != nil {
		return p
	}
	return r
}

func decodeReplace(data []byte) []byte {
	i := 0
	for i < len(data) {
		if data[i] < 0x80 {
			i++
			continue
		}
		n := utf8SeqLen(data[i])
		if n == 0 || i+n > len(data) || !validSeq(data[i:i+n]) {
			return decodeSlow(data)
		}
		i += n
	}
	return data
}

func utf8SeqLen(b byte) int {
	switch {
	case b&0xE0 == 0xC0:
		return 2
	case b&0xF0 == 0xE0:
		return 3
	case b&0xF8 == 0xF0:
		return 4
	}
	return 0
}

func validSeq(s []byte) bool {
	switch len(s) {
	case 2:
		return s[0] >= 0xC2 && s[1]&0xC0 == 0x80
	case 3:
		if s[1] < 0x80 {
			return false
		}
		if s[0] == 0xE0 {
			return s[1] >= 0xA0
		}
		if s[0] == 0xED {
			return s[1] <= 0x9F
		}
		return s[1]&0xC0 == 0x80 && s[2]&0xC0 == 0x80
	case 4:
		if s[0] == 0xF0 {
			return s[1] >= 0x90
		}
		if s[0] == 0xF4 {
			return s[1] <= 0x8F
		}
		return s[0] >= 0xF1 && s[0] <= 0xF3 &&
			s[1]&0xC0 == 0x80 && s[2]&0xC0 == 0x80 && s[3]&0xC0 == 0x80
	}
	return false
}

func decodeSlow(data []byte) []byte {
	out := make([]byte, 0, len(data)+16)
	for i := 0; i < len(data); {
		c := data[i]
		if c < 0x80 {
			out = append(out, c)
			i++
			continue
		}
		n := utf8SeqLen(c)
		if n > 0 && i+n <= len(data) && validSeq(data[i:i+n]) {
			out = append(out, data[i:i+n]...)
			i += n
			continue
		}

		j := i + 1
		for k := 1; k < n && j < len(data); k++ {
			if data[j]&0xC0 != 0x80 {
				break
			}
			if k == 1 && !leadSecondOK(c, data[j]) {
				break
			}
			j++
		}
		out = append(out, ef...)
		i = j
	}
	return out
}

func leadSecondOK(lead, b byte) bool {
	lo, hi := byte(0x80), byte(0xBF)
	switch lead {
	case 0xE0:
		lo = 0xA0
	case 0xED:
		hi = 0x9F
	case 0xF0:
		lo = 0x90
	case 0xF4:
		hi = 0x8F
	}
	return b >= lo && b <= hi
}

var ef = []byte{0xEF, 0xBF, 0xBD}

func runeLen(b []byte) int {
	n := len(b)
	for _, c := range b {
		if c&0xC0 == 0x80 {
			n--
		}
	}
	return n
}

func isIdentStart(c byte) bool {
	return c == '_' || (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')
}

func isIdentPart(c byte) bool {
	return isIdentStart(c) || (c >= '0' && c <= '9') || c >= 0x80
}

func isDigit(c byte) bool { return c >= '0' && c <= '9' }

func isWS(c byte) bool {
	switch c {
	case ' ', '\t', '\r', '\n', '\v', '\f':
		return true
	case 0x1c, 0x1d, 0x1e, 0x1f, 0x85, 0xa0:
		return true
	}
	return false
}

func isStripSpace(c byte) bool {
	switch c {
	case ' ', '\t', '\r', '\n', '\v', '\f', 0x1c, 0x1d, 0x1e, 0x1f, 0x85, 0xa0:
		return true
	}
	return false
}

func isHardWS(c byte) bool {
	return c == ' ' || c == '\t' || c == '\r' || c == '\n'
}

func lstripIdx(s string) int {
	i := 0
	for i < len(s) && (isHardWS(s[i]) || s[i] == '\v' || s[i] == '\f') {
		i++
	}
	return i
}

func trimSpace(s string) string {
	a := 0
	for a < len(s) && isStripSpace(s[a]) {
		a++
	}
	b := len(s)
	for b > a && isStripSpace(s[b-1]) {
		b--
	}
	return s[a:b]
}

func isSplitBound(b []byte, i int) bool {
	switch b[i] {
	case '\n', '\r', 0x0b, 0x0c, 0x1c, 0x1d, 0x1e:
		return true
	case 0xC2:
		return i+1 < len(b) && b[i+1] == 0x85
	case 0xE2:
		return i+2 < len(b) && b[i+1] == 0x80 && (b[i+2] == 0xA8 || b[i+2] == 0xA9)
	}
	return false
}
func skipBoundary(b []byte, i int) int {
	switch b[i] {
	case '\r':
		if i+1 < len(b) && b[i+1] == '\n' {
			return i + 2
		}
		return i + 1
	case 0xC2:
		return i + 2
	case 0xE2:
		return i + 3
	}
	return i + 1
}
func wordBefore(b []byte, i int) bool {
	return i > 0 && isWordByte(b[i-1])
}
func wordAfter(b []byte, i int) bool {
	return i < len(b) && isWordByte(b[i])
}
func sizeishName(w string) bool {
	switch w {
	case "len", "size", "count":
		return true
	}
	for _, suf := range [...]string{"len", "size", "cnt", "count"} {
		if len(w) > len(suf) && strings.HasSuffix(w, suf) {
			head := w[:len(w)-len(suf)]
			ok := true
			for i := 0; i < len(head); i++ {
				if !isIdentPart(head[i]) {
					ok = false
					break
				}
			}
			if ok {
				return true
			}
		}
	}
	if len(w) >= 3 && w[0] == 'n' && w[1] == '_' && w[2] >= 'a' && w[2] <= 'z' {
		return true
	}
	return false
}
func skipHTStr(s string, i int) int {
	for i < len(s) && isPySpace(s[i]) {
		i++
	}
	return i
}
func identEndStr(s string, i int) int {
	if i >= len(s) || !isIdentStart(s[i]) {
		return i
	}
	j := i + 1
	for j < len(s) && isIdentPart(s[j]) {
		j++
	}
	return j
}
func pathBase(p string) string {
	if i := strings.LastIndexByte(p, '/'); i >= 0 {
		return p[i+1:]
	}
	return p
}
func isPySpace(c byte) bool {
	switch c {
	case ' ', '\t', '\n', '\r', '\v', '\f':
		return true
	}
	return false
}

func isBlank(s string) bool {
	for i := 0; i < len(s); i++ {
		if !isStripSpace(s[i]) {
			return false
		}
	}
	return true
}

func splitBounds(b []byte) (int, []int32, int) {
	var starts []int32
	begin := 0
	i := 0
	last := 0
	for i < len(b) {
		var w int
		switch {
		case b[i] == '\n':
			w = 1
		case b[i] == '\r':
			w = 1
			if i+1 < len(b) && b[i+1] == '\n' {
				w = 2
			}
		case b[i] == 0x0b || b[i] == 0x0c || b[i] == 0x1c || b[i] == 0x1d ||
			b[i] == 0x1e:
			w = 1
		case b[i] == 0xC2 && i+1 < len(b) && b[i+1] == 0x85:
			w = 2
		case b[i] == 0xE2 && i+2 < len(b) && b[i+1] == 0x80 &&
			(b[i+2] == 0xA8 || b[i+2] == 0xA9):
			w = 3
		default:
			i++
			continue
		}
		starts = append(starts, int32(begin))
		begin = i + w
		last = i
		i += w
	}

	if begin < len(b) {
		starts = append(starts, int32(begin))
		return len(starts), starts, len(b)
	}
	if len(starts) == 0 {
		return 0, starts, 0
	}
	return len(starts), starts, last
}

func splitLines(text string) []string {
	b := []byte(text)
	n, starts, lastEnd := splitBounds(b)
	out := make([]string, 0, n)
	for i := range n {
		s := starts[i]
		e := int32(lastEnd)
		if i+1 < n {
			e = trimBreak(b, starts[i+1])
		}
		if e < s {
			e = s
		}
		out = append(out, text[s:e])
	}
	return out
}

func trimBreak(b []byte, at int32) int32 {
	j := int(at)
	if j > 0 && j-1 < len(b) && b[j-1] == '\n' {
		j--
		if j > 0 && b[j-1] == '\r' {
			j--
		}
		return int32(j)
	}
	if j >= 3 && b[j-3] == 0xE2 {
		return int32(j - 3)
	}
	if j >= 2 && b[j-2] == 0xC2 {
		return int32(j - 2)
	}
	if j > 0 {
		return int32(j - 1)
	}
	return int32(j)
}

func nlOffsets(b []byte) []int32 {
	offs := make([]int32, 0, len(b)/24+8)
	for i, c := range b {
		if c == '\n' {
			offs = append(offs, int32(i+1))
		}
	}
	return offs
}

func lineOf(offs []int32, pos int) int {
	lo, hi := 0, len(offs)
	for lo < hi {
		mid := int(uint(lo+hi) >> 1)
		if int(offs[mid]) <= pos {
			lo = mid + 1
		} else {
			hi = mid
		}
	}
	return lo + 1
}

func blankBuf(buf []byte, src []byte) []byte {
	out := buf
	if cap(out) < len(src) {
		out = make([]byte, len(src))
	} else {
		out = out[:len(src)]
	}
	copy(out, src)
	i := 0
	n := len(src)
	for i < n {
		switch {
		case src[i] == '/' && i+1 < n && src[i+1] == '*':
			j := indexFrom(src, "*/", i+2)
			end := n
			if j >= 0 {
				end = j + 2
			}
			blankSpan(out, src, i, end)
			i = end
		case src[i] == '/' && i+1 < n && src[i+1] == '/':
			j := indexByteFrom(src, '\n', i)
			end := n
			if j >= 0 {
				end = j
			}
			blankSpan(out, src, i, end)
			i = end
		case src[i] == '"' || src[i] == '\'':
			q := src[i]
			j := i + 1
			closed := -1
			for j < n {
				if src[j] == '\\' {
					j += 2
					continue
				}
				if src[j] == q {
					closed = j
					break
				}
				if src[j] == '\n' {
					break
				}
				j++
			}
			end := j
			if closed >= 0 {
				end = closed + 1
			} else {

				if end < n && src[end] == '\\' {
					end = n
				}
			}
			blankSpan(out, src, i, end)
			i = end
		default:
			i++
		}
	}
	return out
}

func blankSpan(out, src []byte, start, end int) {
	if end > len(out) {
		end = len(out)
	}
	for k := start; k < end; k++ {
		if src[k] != '\n' {
			out[k] = ' '
		}
	}
}

func indexFrom(b []byte, s string, from int) int {
	if from >= len(b) {
		return -1
	}
	i := bytes.Index(b[from:], []byte(s))
	if i < 0 {
		return -1
	}
	return from + i
}

func indexByteFrom(b []byte, c byte, from int) int {
	for i := from; i < len(b); i++ {
		if b[i] == c {
			return i
		}
	}
	return -1
}

func lastIndexByte(b []byte, c byte) int {
	for i, v := range slices.Backward(b) {
		if v == c {
			return i
		}
	}
	return -1
}

func lastIndexStr(b []byte, s string) int {
	if len(b) < len(s) {
		return -1
	}
	for i := len(b) - len(s); i >= 0; i-- {
		if string(b[i:i+len(s)]) == s {
			return i
		}
	}
	return -1
}

func sortStrings(s []string) { sort.Strings(s) }

func eachSplitLine(b []byte, fn func(lnNo int, seg []byte)) {
	n, start, i := 1, 0, 0
	for i < len(b) {
		if isSplitBound(b, i) {
			fn(n, b[start:i])
			i = skipBoundary(b, i)
			start = i
			n++
			continue
		}
		i++
	}
	if start < len(b) || n == 1 {
		fn(n, b[start:])
	}
}

func cgRepr(f float64) string {
	if math.IsInf(f, 1) {
		return "inf"
	}
	if math.IsInf(f, -1) {
		return "-inf"
	}
	if math.IsNaN(f) {
		return "nan"
	}
	neg := math.Signbit(f)
	if neg {
		f = -f
	}
	if f == 0 {
		if neg {
			return "-0.0"
		}
		return "0.0"
	}

	mant := strconv.FormatFloat(f, 'e', -1, 64)
	epos := strings.IndexByte(mant, 'e')
	digits := strings.Replace(mant[:epos], ".", "", 1)
	exp, _ := strconv.Atoi(mant[epos+1:])

	decpt := exp + 1
	var sb strings.Builder
	if neg {
		sb.WriteByte('-')
	}
	if decpt < -3 || decpt > 16 {
		sb.WriteByte(digits[0])
		if len(digits) > 1 {
			sb.WriteByte('.')
			sb.WriteString(digits[1:])
		}
		e := decpt - 1
		sb.WriteByte('e')
		if e < 0 {
			sb.WriteByte('-')
			e = -e
		} else {
			sb.WriteByte('+')
		}
		es := strconv.Itoa(e)
		if len(es) < 2 {
			es = "0" + es
		}
		sb.WriteString(es)
		return sb.String()
	}
	if decpt <= 0 {
		sb.WriteString("0.")
		for i := 0; i < -decpt; i++ {
			sb.WriteByte('0')
		}
		sb.WriteString(digits)
	} else if decpt >= len(digits) {
		sb.WriteString(digits)
		for i := 0; i < decpt-len(digits); i++ {
			sb.WriteByte('0')
		}
		sb.WriteString(".0")
	} else {
		sb.WriteString(digits[:decpt])
		sb.WriteByte('.')
		sb.WriteString(digits[decpt:])
	}
	return sb.String()
}

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

var cKeywords = map[string]bool{
	"_Atomic":        true,
	"_Bool":          true,
	"_Generic":       true,
	"_Static_assert": true,
	"__asm__":        true,
	"__attribute__":  true,
	"__extension__":  true,
	"__inline":       true,
	"__inline__":     true,
	"__restrict":     true,
	"__restrict__":   true,
	"__typeof__":     true,
	"__volatile__":   true,
	"alignas":        true,
	"alignof":        true,
	"and":            true,
	"asm":            true,
	"break":          true,
	"case":           true,
	"char":           true,
	"const":          true,
	"continue":       true,
	"default":        true,
	"defined":        true,
	"do":             true,
	"double":         true,
	"else":           true,
	"enum":           true,
	"extern":         true,
	"float":          true,
	"for":            true,
	"goto":           true,
	"if":             true,
	"inline":         true,
	"int":            true,
	"long":           true,
	"not":            true,
	"or":             true,
	"register":       true,
	"restrict":       true,
	"return":         true,
	"short":          true,
	"signed":         true,
	"sizeof":         true,
	"static":         true,
	"struct":         true,
	"switch":         true,
	"typedef":        true,
	"typeof":         true,
	"union":          true,
	"unsigned":       true,
	"void":           true,
	"volatile":       true,
	"while":          true,
}

func isKeywordBytes(b []byte) bool { return cKeywords[string(b)] }

var typeWords = map[string]bool{
	"_Atomic":  true,
	"const":    true,
	"enum":     true,
	"extern":   true,
	"inline":   true,
	"long":     true,
	"restrict": true,
	"short":    true,
	"signed":   true,
	"static":   true,
	"struct":   true,
	"union":    true,
	"unsigned": true,
	"volatile": true,
}

var hazardFuncs = map[string]string{
	"_exit":                          "control",
	"abort":                          "control",
	"accept":                         "io",
	"accept4":                        "io",
	"access":                         "io",
	"acos":                           "libm",
	"alarm":                          "control",
	"aligned_alloc":                  "alloc",
	"alloca":                         "memory",
	"asctime":                        "reentrancy",
	"asin":                           "libm",
	"asprintf":                       "memory",
	"assert":                         "control",
	"at_quick_exit":                  "control",
	"atan":                           "libm",
	"atan2":                          "libm",
	"atexit":                         "control",
	"atof":                           "integer",
	"atoi":                           "integer",
	"atol":                           "integer",
	"atoll":                          "integer",
	"atomic_compare_exchange_strong": "concurrency",
	"atomic_compare_exchange_weak":   "concurrency",
	"atomic_exchange":                "concurrency",
	"atomic_fetch_add":               "concurrency",
	"atomic_fetch_sub":               "concurrency",
	"atomic_load":                    "concurrency",
	"atomic_store":                   "concurrency",
	"atomic_thread_fence":            "concurrency",
	"basename":                       "reentrancy",
	"bcopy":                          "memory",
	"bind":                           "io",
	"bzero":                          "memory",
	"calloc":                         "alloc",
	"cbrt":                           "libm",
	"ceil":                           "libm",
	"cfree":                          "alloc",
	"chmod":                          "io",
	"chown":                          "io",
	"close":                          "io",
	"connect":                        "io",
	"cos":                            "libm",
	"crypt":                          "reentrancy",
	"ctime":                          "reentrancy",
	"dirname":                        "reentrancy",
	"dlclose":                        "exec",
	"dlmopen":                        "exec",
	"dlopen":                         "exec",
	"dlsym":                          "exec",
	"drand48":                        "reentrancy",
	"erf":                            "libm",
	"execl":                          "exec",
	"execle":                         "exec",
	"execlp":                         "exec",
	"execv":                          "exec",
	"execve":                         "exec",
	"execvp":                         "exec",
	"execvpe":                        "exec",
	"exit":                           "control",
	"exp":                            "libm",
	"expf":                           "libm",
	"faccessat":                      "io",
	"fchmod":                         "io",
	"fchown":                         "io",
	"fclose":                         "stdio",
	"fdatasync":                      "io",
	"fexecve":                        "exec",
	"fflush":                         "stdio",
	"fgetc":                          "stdio",
	"fgets":                          "stdio",
	"floor":                          "libm",
	"fmod":                           "libm",
	"fopen":                          "stdio",
	"fork":                           "exec",
	"fprintf":                        "stdio",
	"fputc":                          "stdio",
	"fputs":                          "stdio",
	"fread":                          "stdio",
	"free":                           "alloc",
	"freopen":                        "io",
	"fscanf":                         "memory",
	"fsync":                          "io",
	"ftruncate":                      "io",
	"fwrite":                         "stdio",
	"g_free":                         "alloc",
	"g_malloc":                       "alloc",
	"getaddrinfo":                    "io",
	"getcwd":                         "memory",
	"getenv":                         "reentrancy",
	"getgrgid":                       "reentrancy",
	"getgrnam":                       "reentrancy",
	"gethostbyaddr":                  "reentrancy",
	"gethostbyname":                  "io",
	"getpwnam":                       "reentrancy",
	"getpwuid":                       "reentrancy",
	"gets":                           "memory",
	"getwd":                          "memory",
	"gmtime":                         "reentrancy",
	"hypot":                          "libm",
	"inet_pton":                      "io",
	"initstate":                      "reentrancy",
	"kill":                           "control",
	"lgamma":                         "libm",
	"link":                           "io",
	"listen":                         "io",
	"localtime":                      "reentrancy",
	"log":                            "libm",
	"log10":                          "libm",
	"log2":                           "libm",
	"logf":                           "libm",
	"longjmp":                        "control",
	"lrand48":                        "reentrancy",
	"lseek":                          "io",
	"malloc":                         "alloc",
	"memalign":                       "alloc",
	"memccpy":                        "memory",
	"memchr":                         "memory",
	"memcmp":                         "memory",
	"memcpy":                         "memory",
	"memmove":                        "memory",
	"mempcpy":                        "memory",
	"memset":                         "memory",
	"mkdtemp":                        "io",
	"mkstemp":                        "io",
	"mktemp":                         "io",
	"mmap":                           "io",
	"mrand48":                        "reentrancy",
	"munmap":                         "io",
	"open":                           "io",
	"openat":                         "io",
	"opendir":                        "io",
	"pause":                          "control",
	"popen":                          "exec",
	"posix_memalign":                 "alloc",
	"posix_spawn":                    "exec",
	"posix_spawnp":                   "exec",
	"pow":                            "libm",
	"powf":                           "libm",
	"pread":                          "io",
	"printf":                         "stdio",
	"pthread_barrier_wait":           "concurrency",
	"pthread_cancel":                 "concurrency",
	"pthread_cond_broadcast":         "concurrency",
	"pthread_cond_signal":            "concurrency",
	"pthread_cond_wait":              "concurrency",
	"pthread_create":                 "concurrency",
	"pthread_detach":                 "concurrency",
	"pthread_join":                   "concurrency",
	"pthread_kill":                   "concurrency",
	"pthread_mutex_lock":             "concurrency",
	"pthread_mutex_trylock":          "concurrency",
	"pthread_mutex_unlock":           "concurrency",
	"pthread_rwlock_rdlock":          "concurrency",
	"pthread_rwlock_unlock":          "concurrency",
	"pthread_rwlock_wrlock":          "concurrency",
	"putchar":                        "stdio",
	"putenv":                         "reentrancy",
	"puts":                           "stdio",
	"pwrite":                         "io",
	"quick_exit":                     "control",
	"raise":                          "control",
	"rand":                           "reentrancy",
	"random":                         "reentrancy",
	"read":                           "io",
	"readdir":                        "io",
	"readlink":                       "io",
	"readv":                          "io",
	"realloc":                        "alloc",
	"reallocarray":                   "alloc",
	"reallocf":                       "alloc",
	"realpath":                       "memory",
	"recv":                           "io",
	"recvfrom":                       "io",
	"recvmsg":                        "io",
	"remove":                         "io",
	"rename":                         "io",
	"round":                          "libm",
	"scanf":                          "memory",
	"sched_yield":                    "concurrency",
	"sem_post":                       "concurrency",
	"sem_trywait":                    "concurrency",
	"sem_wait":                       "concurrency",
	"send":                           "io",
	"sendfile":                       "io",
	"sendmsg":                        "io",
	"sendto":                         "io",
	"setenv":                         "reentrancy",
	"setjmp":                         "control",
	"setlocale":                      "reentrancy",
	"sigaction":                      "control",
	"siglongjmp":                     "control",
	"signal":                         "control",
	"sigprocmask":                    "control",
	"sigsetjmp":                      "control",
	"sigsuspend":                     "control",
	"sin":                            "libm",
	"snprintf":                       "memory",
	"splice":                         "io",
	"sprintf":                        "memory",
	"sqrt":                           "libm",
	"sqrtf":                          "libm",
	"srand":                          "reentrancy",
	"srandom":                        "reentrancy",
	"sscanf":                         "memory",
	"stpcpy":                         "memory",
	"stpncpy":                        "memory",
	"strcat":                         "memory",
	"strchr":                         "memory",
	"strcmp":                         "memory",
	"strcpy":                         "memory",
	"strdup":                         "alloc",
	"strdupa":                        "alloc",
	"strerror":                       "reentrancy",
	"strlcat":                        "memory",
	"strlcpy":                        "memory",
	"strlen":                         "memory",
	"strncat":                        "memory",
	"strncmp":                        "memory",
	"strncpy":                        "memory",
	"strndup":                        "alloc",
	"strndupa":                       "alloc",
	"strnlen":                        "memory",
	"strrchr":                        "memory",
	"strsep":                         "memory",
	"strstr":                         "memory",
	"strtod":                         "integer",
	"strtof":                         "integer",
	"strtoimax":                      "integer",
	"strtok":                         "memory",
	"strtok_r":                       "memory",
	"strtol":                         "integer",
	"strtoll":                        "integer",
	"strtoul":                        "integer",
	"strtoull":                       "integer",
	"strtoumax":                      "integer",
	"swprintf":                       "memory",
	"symlink":                        "io",
	"syslog":                         "stdio",
	"system":                         "exec",
	"tan":                            "libm",
	"tempnam":                        "io",
	"tgamma":                         "libm",
	"tmpfile":                        "reentrancy",
	"tmpnam":                         "io",
	"trunc":                          "libm",
	"truncate":                       "io",
	"ttyname":                        "reentrancy",
	"umask":                          "io",
	"unlink":                         "io",
	"unlinkat":                       "io",
	"valloc":                         "alloc",
	"vasprintf":                      "memory",
	"vfork":                          "exec",
	"vfprintf":                       "stdio",
	"vfscanf":                        "memory",
	"vprintf":                        "stdio",
	"vsnprintf":                      "stdio",
	"vsprintf":                       "memory",
	"vsscanf":                        "memory",
	"wcscat":                         "memory",
	"wcscpy":                         "memory",
	"wcsncpy":                        "memory",
	"wordexp":                        "exec",
	"write":                          "io",
	"writev":                         "io",
	"xcalloc":                        "alloc",
	"xmalloc":                        "alloc",
	"xrealloc":                       "alloc",
	"xstrdup":                        "alloc",
}

var hazardCategories = [...]string{"memory", "alloc", "io", "stdio", "exec", "libm", "integer", "concurrency", "control", "reentrancy"}

var libcKnown = map[string]bool{
	"_exit":                          true,
	"abort":                          true,
	"abs":                            true,
	"accept":                         true,
	"accept4":                        true,
	"access":                         true,
	"acos":                           true,
	"acosh":                          true,
	"alarm":                          true,
	"aligned_alloc":                  true,
	"alignof":                        true,
	"alphasort":                      true,
	"arc4random":                     true,
	"asctime":                        true,
	"asctime_r":                      true,
	"asin":                           true,
	"asinh":                          true,
	"asprintf":                       true,
	"atan":                           true,
	"atan2":                          true,
	"atanh":                          true,
	"atexit":                         true,
	"atoi":                           true,
	"atol":                           true,
	"atoll":                          true,
	"atomic_compare_exchange_strong": true,
	"atomic_compare_exchange_weak":   true,
	"atomic_exchange":                true,
	"atomic_fetch_add":               true,
	"atomic_fetch_and":               true,
	"atomic_fetch_or":                true,
	"atomic_fetch_sub":               true,
	"atomic_fetch_xor":               true,
	"atomic_flag_test_and_set":       true,
	"atomic_init":                    true,
	"atomic_is_lock_free":            true,
	"atomic_load":                    true,
	"atomic_store":                   true,
	"atomic_thread_fence":            true,
	"backtrace":                      true,
	"backtrace_symbols":              true,
	"basename":                       true,
	"bcopy":                          true,
	"bind":                           true,
	"brk":                            true,
	"bsearch":                        true,
	"bzero":                          true,
	"calloc":                         true,
	"cbrt":                           true,
	"ceil":                           true,
	"chdir":                          true,
	"chmod":                          true,
	"chown":                          true,
	"clearerr":                       true,
	"clock":                          true,
	"clock_getres":                   true,
	"clock_gettime":                  true,
	"clock_settime":                  true,
	"close":                          true,
	"closedir":                       true,
	"closelog":                       true,
	"connect":                        true,
	"copysign":                       true,
	"cos":                            true,
	"cosh":                           true,
	"creat":                          true,
	"crypt":                          true,
	"ctime":                          true,
	"ctime_r":                        true,
	"daemon":                         true,
	"difftime":                       true,
	"dirname":                        true,
	"div":                            true,
	"dlclose":                        true,
	"dlerror":                        true,
	"dlopen":                         true,
	"dlsym":                          true,
	"dprintf":                        true,
	"dup":                            true,
	"dup2":                           true,
	"epoll_create":                   true,
	"epoll_create1":                  true,
	"epoll_ctl":                      true,
	"epoll_wait":                     true,
	"erf":                            true,
	"erfc":                           true,
	"execl":                          true,
	"execle":                         true,
	"execlp":                         true,
	"execv":                          true,
	"execve":                         true,
	"execvp":                         true,
	"execvpe":                        true,
	"exit":                           true,
	"exp":                            true,
	"exp2":                           true,
	"expf":                           true,
	"expm1":                          true,
	"fabs":                           true,
	"fabsf":                          true,
	"fchmod":                         true,
	"fchown":                         true,
	"fclose":                         true,
	"fcntl":                          true,
	"fdatasync":                      true,
	"fdim":                           true,
	"fdopen":                         true,
	"feof":                           true,
	"ferror":                         true,
	"fflush":                         true,
	"fgetc":                          true,
	"fgets":                          true,
	"fileno":                         true,
	"floor":                          true,
	"fmax":                           true,
	"fmin":                           true,
	"fmod":                           true,
	"fmodf":                          true,
	"fopen":                          true,
	"fork":                           true,
	"fprintf":                        true,
	"fputc":                          true,
	"fputs":                          true,
	"fread":                          true,
	"free":                           true,
	"freeaddrinfo":                   true,
	"freopen":                        true,
	"frexp":                          true,
	"fscanf":                         true,
	"fseek":                          true,
	"fseeko":                         true,
	"fstat":                          true,
	"fstatat":                        true,
	"fsync":                          true,
	"ftell":                          true,
	"ftello":                         true,
	"ftok":                           true,
	"ftruncate":                      true,
	"fwrite":                         true,
	"gai_strerror":                   true,
	"getaddrinfo":                    true,
	"getc":                           true,
	"getchar":                        true,
	"getcwd":                         true,
	"getegid":                        true,
	"getenv":                         true,
	"geteuid":                        true,
	"getgid":                         true,
	"getgrgid":                       true,
	"getgrnam":                       true,
	"gethostbyname":                  true,
	"gethostbyname_r":                true,
	"getnameinfo":                    true,
	"getopt":                         true,
	"getopt_long":                    true,
	"getpeername":                    true,
	"getpgid":                        true,
	"getpid":                         true,
	"getppid":                        true,
	"getpwnam":                       true,
	"getpwuid":                       true,
	"getrlimit":                      true,
	"getrusage":                      true,
	"gets":                           true,
	"getsockname":                    true,
	"getsockopt":                     true,
	"gettimeofday":                   true,
	"getuid":                         true,
	"glob":                           true,
	"globfree":                       true,
	"gmtime":                         true,
	"gmtime_r":                       true,
	"htonl":                          true,
	"htons":                          true,
	"hypot":                          true,
	"iconv":                          true,
	"iconv_close":                    true,
	"iconv_open":                     true,
	"inet_addr":                      true,
	"inet_ntoa":                      true,
	"inet_ntop":                      true,
	"inet_pton":                      true,
	"ioctl":                          true,
	"isalnum":                        true,
	"isalpha":                        true,
	"isatty":                         true,
	"isblank":                        true,
	"iscntrl":                        true,
	"isdigit":                        true,
	"isfinite":                       true,
	"isgraph":                        true,
	"isinf":                          true,
	"islower":                        true,
	"isnan":                          true,
	"isprint":                        true,
	"ispunct":                        true,
	"isspace":                        true,
	"isupper":                        true,
	"isxdigit":                       true,
	"kevent":                         true,
	"kill":                           true,
	"killpg":                         true,
	"kqueue":                         true,
	"labs":                           true,
	"ldexp":                          true,
	"ldiv":                           true,
	"lgamma":                         true,
	"link":                           true,
	"listen":                         true,
	"llabs":                          true,
	"lldiv":                          true,
	"llround":                        true,
	"localtime":                      true,
	"localtime_r":                    true,
	"log":                            true,
	"log10":                          true,
	"log1p":                          true,
	"log2":                           true,
	"logf":                           true,
	"longjmp":                        true,
	"lround":                         true,
	"lseek":                          true,
	"lstat":                          true,
	"madvise":                        true,
	"malloc":                         true,
	"mbstowcs":                       true,
	"memalign":                       true,
	"memchr":                         true,
	"memcmp":                         true,
	"memcpy":                         true,
	"memmove":                        true,
	"mempcpy":                        true,
	"memrchr":                        true,
	"memset":                         true,
	"mkdir":                          true,
	"mkdtemp":                        true,
	"mkstemp":                        true,
	"mktime":                         true,
	"mlock":                          true,
	"mmap":                           true,
	"modf":                           true,
	"mprotect":                       true,
	"msgget":                         true,
	"msgrcv":                         true,
	"msgsnd":                         true,
	"msync":                          true,
	"munlock":                        true,
	"munmap":                         true,
	"nan":                            true,
	"nanosleep":                      true,
	"nearbyint":                      true,
	"nice":                           true,
	"ntohl":                          true,
	"ntohs":                          true,
	"offsetof":                       true,
	"open":                           true,
	"openat":                         true,
	"opendir":                        true,
	"openlog":                        true,
	"pause":                          true,
	"pclose":                         true,
	"perror":                         true,
	"pipe":                           true,
	"pipe2":                          true,
	"poll":                           true,
	"popen":                          true,
	"posix_memalign":                 true,
	"posix_spawn":                    true,
	"posix_spawnp":                   true,
	"pow":                            true,
	"powf":                           true,
	"ppoll":                          true,
	"pread":                          true,
	"printf":                         true,
	"pselect":                        true,
	"pthread_atfork":                 true,
	"pthread_attr_destroy":           true,
	"pthread_attr_init":              true,
	"pthread_attr_setdetachstate":    true,
	"pthread_attr_setstacksize":      true,
	"pthread_cancel":                 true,
	"pthread_cond_broadcast":         true,
	"pthread_cond_destroy":           true,
	"pthread_cond_init":              true,
	"pthread_cond_signal":            true,
	"pthread_cond_timedwait":         true,
	"pthread_cond_wait":              true,
	"pthread_create":                 true,
	"pthread_detach":                 true,
	"pthread_equal":                  true,
	"pthread_exit":                   true,
	"pthread_getname_np":             true,
	"pthread_getspecific":            true,
	"pthread_join":                   true,
	"pthread_key_create":             true,
	"pthread_key_delete":             true,
	"pthread_kill":                   true,
	"pthread_mutex_destroy":          true,
	"pthread_mutex_init":             true,
	"pthread_mutex_lock":             true,
	"pthread_mutex_trylock":          true,
	"pthread_mutex_unlock":           true,
	"pthread_mutexattr_destroy":      true,
	"pthread_mutexattr_init":         true,
	"pthread_mutexattr_settype":      true,
	"pthread_once":                   true,
	"pthread_rwlock_destroy":         true,
	"pthread_rwlock_init":            true,
	"pthread_rwlock_rdlock":          true,
	"pthread_rwlock_tryrdlock":       true,
	"pthread_rwlock_trywrlock":       true,
	"pthread_rwlock_unlock":          true,
	"pthread_rwlock_wrlock":          true,
	"pthread_self":                   true,
	"pthread_setname_np":             true,
	"pthread_setspecific":            true,
	"putc":                           true,
	"putchar":                        true,
	"putenv":                         true,
	"puts":                           true,
	"pwrite":                         true,
	"qsort":                          true,
	"raise":                          true,
	"rand":                           true,
	"random":                         true,
	"read":                           true,
	"readdir":                        true,
	"readlink":                       true,
	"readv":                          true,
	"realloc":                        true,
	"reallocarray":                   true,
	"realpath":                       true,
	"recv":                           true,
	"recvfrom":                       true,
	"recvmsg":                        true,
	"remainder":                      true,
	"remove":                         true,
	"rename":                         true,
	"rewind":                         true,
	"rewinddir":                      true,
	"rint":                           true,
	"rmdir":                          true,
	"round":                          true,
	"sbrk":                           true,
	"scandir":                        true,
	"scanf":                          true,
	"sched_getaffinity":              true,
	"sched_setaffinity":              true,
	"sched_yield":                    true,
	"select":                         true,
	"sem_destroy":                    true,
	"sem_getvalue":                   true,
	"sem_init":                       true,
	"sem_post":                       true,
	"sem_trywait":                    true,
	"sem_wait":                       true,
	"semget":                         true,
	"semop":                          true,
	"send":                           true,
	"sendmsg":                        true,
	"sendto":                         true,
	"setbuf":                         true,
	"setegid":                        true,
	"setenv":                         true,
	"seteuid":                        true,
	"setgid":                         true,
	"setjmp":                         true,
	"setpgid":                        true,
	"setrlimit":                      true,
	"setsid":                         true,
	"setsockopt":                     true,
	"settimeofday":                   true,
	"setuid":                         true,
	"setvbuf":                        true,
	"shmat":                          true,
	"shmctl":                         true,
	"shmdt":                          true,
	"shmget":                         true,
	"shutdown":                       true,
	"sigaction":                      true,
	"sigaddset":                      true,
	"sigdelset":                      true,
	"sigemptyset":                    true,
	"sigfillset":                     true,
	"sigismember":                    true,
	"siglongjmp":                     true,
	"signal":                         true,
	"signbit":                        true,
	"sigprocmask":                    true,
	"sigsetjmp":                      true,
	"sigsuspend":                     true,
	"sigwait":                        true,
	"sin":                            true,
	"sinh":                           true,
	"sizeof":                         true,
	"sleep":                          true,
	"snprintf":                       true,
	"socket":                         true,
	"socketpair":                     true,
	"sprintf":                        true,
	"sqrt":                           true,
	"sqrtf":                          true,
	"sqrtl":                          true,
	"srand":                          true,
	"srandom":                        true,
	"sscanf":                         true,
	"stat":                           true,
	"strcasecmp":                     true,
	"strcasestr":                     true,
	"strcat":                         true,
	"strchr":                         true,
	"strcmp":                         true,
	"strcpy":                         true,
	"strcspn":                        true,
	"strdup":                         true,
	"strdupa":                        true,
	"strerror":                       true,
	"strerror_r":                     true,
	"strftime":                       true,
	"strlcat":                        true,
	"strlcpy":                        true,
	"strlen":                         true,
	"strncasecmp":                    true,
	"strncat":                        true,
	"strncmp":                        true,
	"strncpy":                        true,
	"strndup":                        true,
	"strnlen":                        true,
	"strpbrk":                        true,
	"strptime":                       true,
	"strrchr":                        true,
	"strsep":                         true,
	"strsignal":                      true,
	"strspn":                         true,
	"strstr":                         true,
	"strtod":                         true,
	"strtof":                         true,
	"strtok":                         true,
	"strtok_r":                       true,
	"strtol":                         true,
	"strtold":                        true,
	"strtoll":                        true,
	"strtoul":                        true,
	"strtoull":                       true,
	"symlink":                        true,
	"sync":                           true,
	"sysconf":                        true,
	"syslog":                         true,
	"system":                         true,
	"tan":                            true,
	"tanh":                           true,
	"tempnam":                        true,
	"tgamma":                         true,
	"time":                           true,
	"timegm":                         true,
	"tmpfile":                        true,
	"tmpnam":                         true,
	"tolower":                        true,
	"toupper":                        true,
	"trunc":                          true,
	"truncate":                       true,
	"ttyname":                        true,
	"umask":                          true,
	"uname":                          true,
	"ungetc":                         true,
	"unlink":                         true,
	"unlinkat":                       true,
	"unsetenv":                       true,
	"usleep":                         true,
	"va_arg":                         true,
	"va_copy":                        true,
	"va_end":                         true,
	"va_start":                       true,
	"valloc":                         true,
	"vasprintf":                      true,
	"vdprintf":                       true,
	"vfork":                          true,
	"vfprintf":                       true,
	"vprintf":                        true,
	"vsnprintf":                      true,
	"vsprintf":                       true,
	"vsscanf":                        true,
	"wait":                           true,
	"wait3":                          true,
	"wait4":                          true,
	"waitpid":                        true,
	"wcscpy":                         true,
	"wcslen":                         true,
	"wcstombs":                       true,
	"write":                          true,
	"writev":                         true,
}

var builtinPrefixes = [...]string{"__builtin_", "__atomic_", "__sync_", "__asan_", "__msan_", "__tsan_", "__c11_atomic_", "_InterlockedExchange"}

var funcToNS = map[string]string{
	"FD_CLR":                                 "sys/select.h",
	"FD_COPY":                                "sys/select.h",
	"FD_ISSET":                               "sys/select.h",
	"FD_SET":                                 "sys/select.h",
	"FD_ZERO":                                "sys/select.h",
	"F_DUPFD":                                "fcntl.h",
	"F_DUPFD_CLOEXEC":                        "fcntl.h",
	"F_GETFD":                                "fcntl.h",
	"F_GETFL":                                "fcntl.h",
	"F_GETLK":                                "fcntl.h",
	"F_RDLCK":                                "fcntl.h",
	"F_SETFD":                                "fcntl.h",
	"F_SETFL":                                "fcntl.h",
	"F_SETLK":                                "fcntl.h",
	"F_SETLKW":                               "fcntl.h",
	"F_UNLCK":                                "fcntl.h",
	"F_WRLCK":                                "fcntl.h",
	"O_CLOEXEC":                              "fcntl.h",
	"_Exit":                                  "stdlib.h",
	"__builtin_add_overflow":                 "__builtin_*",
	"__builtin_alloca":                       "__builtin_*",
	"__builtin_bswap16":                      "__builtin_*",
	"__builtin_bswap32":                      "__builtin_*",
	"__builtin_bswap64":                      "__builtin_*",
	"__builtin_choose_expr":                  "__builtin_*",
	"__builtin_clz":                          "__builtin_*",
	"__builtin_clzl":                         "__builtin_*",
	"__builtin_clzll":                        "__builtin_*",
	"__builtin_constant_p":                   "__builtin_*",
	"__builtin_counted_by_ref":               "__builtin_*",
	"__builtin_ctz":                          "__builtin_*",
	"__builtin_ctzl":                         "__builtin_*",
	"__builtin_ctzll":                        "__builtin_*",
	"__builtin_debugtrap":                    "__builtin_*",
	"__builtin_expect":                       "__builtin_*",
	"__builtin_extract_return_addr":          "__builtin_*",
	"__builtin_frame_address":                "__builtin_*",
	"__builtin_ia32_pause":                   "__builtin_*",
	"__builtin_memcmp":                       "__builtin_*",
	"__builtin_memcpy":                       "__builtin_*",
	"__builtin_memset":                       "__builtin_*",
	"__builtin_mul_overflow":                 "__builtin_*",
	"__builtin_offsetof":                     "__builtin_*",
	"__builtin_popcount":                     "__builtin_*",
	"__builtin_popcountl":                    "__builtin_*",
	"__builtin_popcountll":                   "__builtin_*",
	"__builtin_prefetch":                     "__builtin_*",
	"__builtin_return_address":               "__builtin_*",
	"__builtin_strcpy":                       "__builtin_*",
	"__builtin_strlen":                       "__builtin_*",
	"__builtin_sub_overflow":                 "__builtin_*",
	"__builtin_trap":                         "__builtin_*",
	"__builtin_types_compatible_p":           "__builtin_*",
	"__builtin_unreachable":                  "__builtin_*",
	"_exit":                                  "unistd.h",
	"_longjmp":                               "setjmp.h",
	"_setjmp":                                "setjmp.h",
	"_tolower":                               "ctype.h",
	"_toupper":                               "ctype.h",
	"a64l":                                   "stdlib.h",
	"abort":                                  "stdlib.h",
	"abs":                                    "stdlib.h",
	"accept":                                 "sys/socket.h",
	"accept4":                                "sys/socket.h",
	"access":                                 "unistd.h",
	"accessx_np":                             "unistd.h",
	"acct":                                   "unistd.h",
	"acos":                                   "math.h",
	"acosf":                                  "math.h",
	"acosh":                                  "math.h",
	"acoshf":                                 "math.h",
	"acoshl":                                 "math.h",
	"acosl":                                  "math.h",
	"add_profil":                             "unistd.h",
	"adjtime":                                "sys/time.h",
	"alarm":                                  "unistd.h",
	"aligned_alloc":                          "stdlib.h",
	"alloca":                                 "stdlib.h",
	"alphasort":                              "dirent.h",
	"arc4random":                             "stdlib.h",
	"arc4random_addrandom":                   "stdlib.h",
	"arc4random_buf":                         "stdlib.h",
	"arc4random_stir":                        "stdlib.h",
	"arc4random_uniform":                     "stdlib.h",
	"asctime":                                "time.h",
	"asctime_r":                              "time.h",
	"asin":                                   "math.h",
	"asinf":                                  "math.h",
	"asinh":                                  "math.h",
	"asinhf":                                 "math.h",
	"asinhl":                                 "math.h",
	"asinl":                                  "math.h",
	"asprintf":                               "stdio.h",
	"assert":                                 "assert.h",
	"at_quick_exit":                          "stdlib.h",
	"atan":                                   "math.h",
	"atan2":                                  "math.h",
	"atan2f":                                 "math.h",
	"atan2l":                                 "math.h",
	"atanf":                                  "math.h",
	"atanh":                                  "math.h",
	"atanhf":                                 "math.h",
	"atanhl":                                 "math.h",
	"atanl":                                  "math.h",
	"atexit":                                 "stdlib.h",
	"atexit_b":                               "stdlib.h",
	"atof":                                   "stdlib.h",
	"atoi":                                   "stdlib.h",
	"atol":                                   "stdlib.h",
	"atoll":                                  "stdlib.h",
	"bcmp":                                   "string.h",
	"bcopy":                                  "string.h",
	"bind":                                   "sys/socket.h",
	"brk":                                    "unistd.h",
	"bsd_signal":                             "signal.h",
	"bsearch":                                "stdlib.h",
	"bsearch_b":                              "stdlib.h",
	"btowc":                                  "wchar.h",
	"bzero":                                  "string.h",
	"calloc":                                 "stdlib.h",
	"cbrt":                                   "math.h",
	"cbrtf":                                  "math.h",
	"cbrtl":                                  "math.h",
	"ceil":                                   "math.h",
	"ceilf":                                  "math.h",
	"ceill":                                  "math.h",
	"cgetcap":                                "stdlib.h",
	"cgetclose":                              "stdlib.h",
	"cgetent":                                "stdlib.h",
	"cgetfirst":                              "stdlib.h",
	"cgetmatch":                              "stdlib.h",
	"cgetnext":                               "stdlib.h",
	"cgetnum":                                "stdlib.h",
	"cgetset":                                "stdlib.h",
	"cgetstr":                                "stdlib.h",
	"cgetustr":                               "stdlib.h",
	"chdir":                                  "unistd.h",
	"checkuseraccess":                        "fcntl.h",
	"chflags":                                "sys/stat.h",
	"chmod":                                  "sys/stat.h",
	"chmodx_np":                              "sys/stat.h",
	"chown":                                  "unistd.h",
	"chroot":                                 "unistd.h",
	"clearerr":                               "stdio.h",
	"clearerr_unlocked":                      "stdio.h",
	"clock":                                  "time.h",
	"clock_getres":                           "time.h",
	"clock_gettime":                          "time.h",
	"clock_gettime_nsec_np":                  "time.h",
	"clock_settime":                          "time.h",
	"close":                                  "unistd.h",
	"close_range":                            "unistd.h",
	"closedir":                               "dirent.h",
	"closefrom":                              "unistd.h",
	"closelog":                               "syslog.h",
	"confstr":                                "unistd.h",
	"connect":                                "sys/socket.h",
	"connectx":                               "sys/socket.h",
	"copysign":                               "math.h",
	"copysignf":                              "math.h",
	"copysignl":                              "math.h",
	"cos":                                    "math.h",
	"cosf":                                   "math.h",
	"cosh":                                   "math.h",
	"coshf":                                  "math.h",
	"coshl":                                  "math.h",
	"cosl":                                   "math.h",
	"creat":                                  "fcntl.h",
	"crypt":                                  "unistd.h",
	"ctermid_r":                              "stdio.h",
	"ctime":                                  "time.h",
	"ctime_r":                                "time.h",
	"daemon":                                 "stdlib.h",
	"devname":                                "stdlib.h",
	"devname_r":                              "stdlib.h",
	"difftime":                               "time.h",
	"digittoint":                             "ctype.h",
	"dirfd":                                  "dirent.h",
	"disconnectx":                            "sys/socket.h",
	"div":                                    "stdlib.h",
	"dladdr":                                 "dlfcn.h",
	"dlclose":                                "dlfcn.h",
	"dlerror":                                "dlfcn.h",
	"dlmopen":                                "dlfcn.h",
	"dlopen":                                 "dlfcn.h",
	"dlopen_preflight":                       "dlfcn.h",
	"dlsym":                                  "dlfcn.h",
	"dlvsym":                                 "dlfcn.h",
	"dprintf":                                "stdio.h",
	"drand48":                                "stdlib.h",
	"drem":                                   "math.h",
	"dup":                                    "unistd.h",
	"dup2":                                   "unistd.h",
	"dup3":                                   "unistd.h",
	"duplocale":                              "locale.h",
	"ecvt":                                   "stdlib.h",
	"elif":                                   "math.h",
	"encrypt":                                "unistd.h",
	"endusershell":                           "unistd.h",
	"erand48":                                "stdlib.h",
	"erf":                                    "math.h",
	"erfc":                                   "math.h",
	"erfcf":                                  "math.h",
	"erfcl":                                  "math.h",
	"erff":                                   "math.h",
	"erfl":                                   "math.h",
	"errno":                                  "errno.h",
	"exchangedata":                           "fcntl.h",
	"execl":                                  "unistd.h",
	"execle":                                 "unistd.h",
	"execlp":                                 "unistd.h",
	"execv":                                  "unistd.h",
	"execvP":                                 "unistd.h",
	"execve":                                 "unistd.h",
	"execveat":                               "unistd.h",
	"execvp":                                 "unistd.h",
	"execvpe":                                "unistd.h",
	"exit":                                   "stdlib.h",
	"exp":                                    "math.h",
	"exp2":                                   "math.h",
	"exp2f":                                  "math.h",
	"exp2l":                                  "math.h",
	"expf":                                   "math.h",
	"expl":                                   "math.h",
	"explicit_bzero":                         "string.h",
	"expm1":                                  "math.h",
	"expm1f":                                 "math.h",
	"expm1l":                                 "math.h",
	"fabs":                                   "math.h",
	"fabsf":                                  "math.h",
	"fabsl":                                  "math.h",
	"faccessat":                              "unistd.h",
	"fchdir":                                 "unistd.h",
	"fchflags":                               "sys/stat.h",
	"fchmod":                                 "sys/stat.h",
	"fchmodat":                               "sys/stat.h",
	"fchmodx_np":                             "sys/stat.h",
	"fchown":                                 "unistd.h",
	"fclose":                                 "stdio.h",
	"fcntl":                                  "fcntl.h",
	"fcntl_getpath":                          "fcntl.h",
	"fcntl_nosync":                           "fcntl.h",
	"fcvt":                                   "stdlib.h",
	"fdatasync":                              "unistd.h",
	"fdclosedir":                             "dirent.h",
	"fdim":                                   "math.h",
	"fdimf":                                  "math.h",
	"fdiml":                                  "math.h",
	"fdopen":                                 "stdio.h",
	"fdopendir":                              "dirent.h",
	"fdscandir":                              "dirent.h",
	"fdscandir_b":                            "dirent.h",
	"feof":                                   "stdio.h",
	"feof_unlocked":                          "stdio.h",
	"ferror":                                 "stdio.h",
	"ferror_unlocked":                        "stdio.h",
	"fexecve":                                "unistd.h",
	"fflagstostr":                            "unistd.h",
	"fflush":                                 "stdio.h",
	"ffs":                                    "string.h",
	"ffsctl":                                 "unistd.h",
	"ffsl":                                   "string.h",
	"ffsll":                                  "string.h",
	"fgetattrlist":                           "unistd.h",
	"fgetc":                                  "stdio.h",
	"fgetln":                                 "stdio.h",
	"fgetpos":                                "stdio.h",
	"fgets":                                  "stdio.h",
	"fgetwc":                                 "wchar.h",
	"fgetwln":                                "wchar.h",
	"fgetws":                                 "wchar.h",
	"fileno":                                 "stdio.h",
	"fileno_unlocked":                        "stdio.h",
	"finite":                                 "math.h",
	"flock":                                  "fcntl.h",
	"flockfile":                              "stdio.h",
	"floor":                                  "math.h",
	"floorf":                                 "math.h",
	"floorl":                                 "math.h",
	"fls":                                    "string.h",
	"flsl":                                   "string.h",
	"flsll":                                  "string.h",
	"fma":                                    "math.h",
	"fmaf":                                   "math.h",
	"fmal":                                   "math.h",
	"fmax":                                   "math.h",
	"fmaxf":                                  "math.h",
	"fmaxl":                                  "math.h",
	"fmemopen":                               "stdio.h",
	"fmin":                                   "math.h",
	"fminf":                                  "math.h",
	"fminl":                                  "math.h",
	"fmod":                                   "math.h",
	"fmodf":                                  "math.h",
	"fmodl":                                  "math.h",
	"fmtcheck":                               "stdio.h",
	"fopen":                                  "stdio.h",
	"fork":                                   "unistd.h",
	"format_arg":                             "stdio.h",
	"fpathconf":                              "unistd.h",
	"fpclassify":                             "math.h",
	"fpos_t":                                 "stdio.h",
	"fprintf":                                "stdio.h",
	"fpurge":                                 "stdio.h",
	"fputc":                                  "stdio.h",
	"fputs":                                  "stdio.h",
	"fputwc":                                 "wchar.h",
	"fputws":                                 "wchar.h",
	"fread":                                  "stdio.h",
	"free":                                   "stdlib.h",
	"free_aligned_sized":                     "stdlib.h",
	"free_sized":                             "stdlib.h",
	"freelocale":                             "locale.h",
	"freopen":                                "stdio.h",
	"frexp":                                  "math.h",
	"frexpf":                                 "math.h",
	"frexpl":                                 "math.h",
	"fropen":                                 "stdio.h",
	"fscanf":                                 "stdio.h",
	"fsctl":                                  "unistd.h",
	"fseek":                                  "stdio.h",
	"fseeko":                                 "stdio.h",
	"fsetattrlist":                           "unistd.h",
	"fsetpos":                                "stdio.h",
	"fstat":                                  "sys/stat.h",
	"fstat64":                                "sys/stat.h",
	"fstatat":                                "sys/stat.h",
	"fstatx64_np":                            "sys/stat.h",
	"fstatx_np":                              "sys/stat.h",
	"fsync":                                  "unistd.h",
	"fsync_volume_np":                        "unistd.h",
	"ftell":                                  "stdio.h",
	"ftello":                                 "stdio.h",
	"ftruncate":                              "unistd.h",
	"ftrylockfile":                           "stdio.h",
	"funlockfile":                            "stdio.h",
	"funopen":                                "stdio.h",
	"futimens":                               "fcntl.h",
	"futimes":                                "fcntl.h",
	"fwide":                                  "wchar.h",
	"fwopen":                                 "stdio.h",
	"fwprintf":                               "wchar.h",
	"fwrite":                                 "stdio.h",
	"fwscanf":                                "wchar.h",
	"gamma":                                  "math.h",
	"gcvt":                                   "stdlib.h",
	"getattrlist":                            "fcntl.h",
	"getattrlistat":                          "fcntl.h",
	"getbsize":                               "stdlib.h",
	"getc":                                   "stdio.h",
	"getc_unlocked":                          "stdio.h",
	"getchar":                                "stdio.h",
	"getchar_unlocked":                       "stdio.h",
	"getcwd":                                 "unistd.h",
	"getdate":                                "time.h",
	"getdelim":                               "stdio.h",
	"getdirentries":                          "dirent.h",
	"getdirentriesattr":                      "unistd.h",
	"getdomainname":                          "unistd.h",
	"getdtablesize":                          "unistd.h",
	"getegid":                                "unistd.h",
	"getenv":                                 "stdlib.h",
	"geteuid":                                "unistd.h",
	"getgid":                                 "unistd.h",
	"getgrouplist":                           "unistd.h",
	"getgroups":                              "unistd.h",
	"gethostid":                              "unistd.h",
	"gethostname":                            "unistd.h",
	"getiopolicy_np":                         "sys/resource.h",
	"getitimer":                              "sys/time.h",
	"getline":                                "stdio.h",
	"getloadavg":                             "stdlib.h",
	"getlogin":                               "unistd.h",
	"getlogin_r":                             "unistd.h",
	"getmode":                                "unistd.h",
	"getopt":                                 "getopt.h",
	"getopt_long":                            "getopt.h",
	"getopt_long_only":                       "getopt.h",
	"getpagesize":                            "unistd.h",
	"getpass":                                "unistd.h",
	"getpath_np":                             "fcntl.h",
	"getpeereid":                             "unistd.h",
	"getpeername":                            "sys/socket.h",
	"getpgid":                                "unistd.h",
	"getpgrp":                                "unistd.h",
	"getpid":                                 "unistd.h",
	"getppid":                                "unistd.h",
	"getpriority":                            "sys/resource.h",
	"getprogname":                            "stdlib.h",
	"getrlimit":                              "sys/resource.h",
	"getrusage":                              "sys/resource.h",
	"gets":                                   "stdio.h",
	"getsgroups_np":                          "unistd.h",
	"getsid":                                 "unistd.h",
	"getsockname":                            "sys/socket.h",
	"getsockopt":                             "sys/socket.h",
	"getsubopt":                              "stdlib.h",
	"gettimeofday":                           "sys/time.h",
	"getuid":                                 "unistd.h",
	"getusershell":                           "unistd.h",
	"getw":                                   "stdio.h",
	"getwc":                                  "wchar.h",
	"getwchar":                               "wchar.h",
	"getwd":                                  "unistd.h",
	"getwgroups_np":                          "unistd.h",
	"gmtime":                                 "time.h",
	"gmtime_r":                               "time.h",
	"grantpt":                                "stdlib.h",
	"heapsort":                               "stdlib.h",
	"heapsort_b":                             "stdlib.h",
	"hypot":                                  "math.h",
	"hypotf":                                 "math.h",
	"hypotl":                                 "math.h",
	"ilogb":                                  "math.h",
	"ilogbf":                                 "math.h",
	"ilogbl":                                 "math.h",
	"index":                                  "string.h",
	"initgroups":                             "unistd.h",
	"initstate":                              "stdlib.h",
	"iruserok":                               "unistd.h",
	"iruserok_sa":                            "unistd.h",
	"isalnum":                                "ctype.h",
	"isalpha":                                "ctype.h",
	"isascii":                                "ctype.h",
	"isatty":                                 "unistd.h",
	"isblank":                                "ctype.h",
	"iscntrl":                                "ctype.h",
	"isdigit":                                "ctype.h",
	"isfinite":                               "math.h",
	"isgraph":                                "ctype.h",
	"isgreater":                              "math.h",
	"isgreaterequal":                         "math.h",
	"ishexnumber":                            "ctype.h",
	"isideogram":                             "ctype.h",
	"isinf":                                  "math.h",
	"isless":                                 "math.h",
	"islessequal":                            "math.h",
	"islessgreater":                          "math.h",
	"islower":                                "ctype.h",
	"isnan":                                  "math.h",
	"isnormal":                               "math.h",
	"isnumber":                               "ctype.h",
	"isphonogram":                            "ctype.h",
	"isprint":                                "ctype.h",
	"ispunct":                                "ctype.h",
	"isrune":                                 "ctype.h",
	"issetugid":                              "unistd.h",
	"isspace":                                "ctype.h",
	"isspecial":                              "ctype.h",
	"isunordered":                            "math.h",
	"isupper":                                "ctype.h",
	"isxdigit":                               "ctype.h",
	"j0":                                     "math.h",
	"j1":                                     "math.h",
	"jn":                                     "math.h",
	"jrand48":                                "stdlib.h",
	"kdebug_signpost":                        "unistd.h",
	"kill":                                   "signal.h",
	"killpg":                                 "signal.h",
	"l64a":                                   "stdlib.h",
	"labs":                                   "stdlib.h",
	"lchflags":                               "sys/stat.h",
	"lchmod":                                 "sys/stat.h",
	"lchown":                                 "unistd.h",
	"lcong48":                                "stdlib.h",
	"ldexp":                                  "math.h",
	"ldexpf":                                 "math.h",
	"ldexpl":                                 "math.h",
	"ldiv":                                   "stdlib.h",
	"lgamma":                                 "math.h",
	"lgamma_r":                               "math.h",
	"lgammaf":                                "math.h",
	"lgammaf_r":                              "math.h",
	"lgammal":                                "math.h",
	"lgammal_r":                              "math.h",
	"link":                                   "unistd.h",
	"listen":                                 "sys/socket.h",
	"llabs":                                  "stdlib.h",
	"lldiv":                                  "stdlib.h",
	"llrint":                                 "math.h",
	"llrintf":                                "math.h",
	"llrintl":                                "math.h",
	"llround":                                "math.h",
	"llroundf":                               "math.h",
	"llroundl":                               "math.h",
	"localeconv":                             "locale.h",
	"localtime":                              "time.h",
	"localtime_r":                            "time.h",
	"lockf":                                  "unistd.h",
	"log":                                    "math.h",
	"log10":                                  "math.h",
	"log10f":                                 "math.h",
	"log10l":                                 "math.h",
	"log1p":                                  "math.h",
	"log1pf":                                 "math.h",
	"log1pl":                                 "math.h",
	"log2":                                   "math.h",
	"log2f":                                  "math.h",
	"log2l":                                  "math.h",
	"logb":                                   "math.h",
	"logbf":                                  "math.h",
	"logbl":                                  "math.h",
	"logf":                                   "math.h",
	"logl":                                   "math.h",
	"longjmp":                                "setjmp.h",
	"longjmperror":                           "setjmp.h",
	"lrand48":                                "stdlib.h",
	"lrint":                                  "math.h",
	"lrintf":                                 "math.h",
	"lrintl":                                 "math.h",
	"lround":                                 "math.h",
	"lroundf":                                "math.h",
	"lroundl":                                "math.h",
	"lseek":                                  "unistd.h",
	"lstat":                                  "sys/stat.h",
	"lstat64":                                "sys/stat.h",
	"lstatx64_np":                            "sys/stat.h",
	"lstatx_np":                              "sys/stat.h",
	"lutimes":                                "sys/time.h",
	"madvise":                                "sys/mman.h",
	"mallinfo":                               "stdlib.h",
	"mallinfo2":                              "stdlib.h",
	"malloc":                                 "stdlib.h",
	"mallopt":                                "stdlib.h",
	"math_errhandling":                       "math.h",
	"mblen":                                  "stdlib.h",
	"mbrlen":                                 "wchar.h",
	"mbrtowc":                                "wchar.h",
	"mbsinit":                                "wchar.h",
	"mbsnrtowcs":                             "wchar.h",
	"mbsrtowcs":                              "wchar.h",
	"mbstowcs":                               "stdlib.h",
	"mbtowc":                                 "stdlib.h",
	"memalign":                               "stdlib.h",
	"memalignment":                           "string.h",
	"memccpy":                                "string.h",
	"memchr":                                 "string.h",
	"memcmp":                                 "string.h",
	"memcpy":                                 "string.h",
	"memmem":                                 "string.h",
	"memmove":                                "string.h",
	"memset":                                 "string.h",
	"memset_explicit":                        "string.h",
	"memset_pattern16":                       "string.h",
	"memset_pattern4":                        "string.h",
	"memset_pattern8":                        "string.h",
	"memset_s":                               "string.h",
	"mergesort":                              "stdlib.h",
	"mergesort_b":                            "stdlib.h",
	"mincore":                                "sys/mman.h",
	"minherit":                               "sys/mman.h",
	"mkdir":                                  "sys/stat.h",
	"mkdirat":                                "sys/stat.h",
	"mkdirx_np":                              "sys/stat.h",
	"mkdtemp":                                "stdio.h",
	"mkdtempat_np":                           "unistd.h",
	"mkfifo":                                 "sys/stat.h",
	"mkfifoat":                               "sys/stat.h",
	"mkfifox_np":                             "sys/stat.h",
	"mknod":                                  "sys/stat.h",
	"mknodat":                                "sys/stat.h",
	"mkostemp":                               "unistd.h",
	"mkostemps":                              "unistd.h",
	"mkostempsat_np":                         "unistd.h",
	"mkpath_np":                              "unistd.h",
	"mkpathat_np":                            "unistd.h",
	"mkstemp":                                "stdio.h",
	"mkstemp_dprotected_np":                  "unistd.h",
	"mkstemps":                               "stdio.h",
	"mkstempsat_np":                          "unistd.h",
	"mktemp":                                 "stdlib.h",
	"mktime":                                 "time.h",
	"mlock":                                  "sys/mman.h",
	"mlockall":                               "sys/mman.h",
	"mmap":                                   "sys/mman.h",
	"modf":                                   "math.h",
	"modff":                                  "math.h",
	"modfl":                                  "math.h",
	"mprotect":                               "sys/mman.h",
	"mrand48":                                "stdlib.h",
	"msync":                                  "sys/mman.h",
	"munlock":                                "sys/mman.h",
	"munlockall":                             "sys/mman.h",
	"munmap":                                 "sys/mman.h",
	"nan":                                    "math.h",
	"nanf":                                   "math.h",
	"nanl":                                   "math.h",
	"nanosleep":                              "time.h",
	"nearbyint":                              "math.h",
	"nearbyintf":                             "math.h",
	"nearbyintl":                             "math.h",
	"newlocale":                              "locale.h",
	"nextafter":                              "math.h",
	"nextafterf":                             "math.h",
	"nextafterl":                             "math.h",
	"nexttoward":                             "math.h",
	"nexttowardf":                            "math.h",
	"nexttowardl":                            "math.h",
	"nfssvc":                                 "unistd.h",
	"nice":                                   "unistd.h",
	"nrand48":                                "stdlib.h",
	"open":                                   "fcntl.h",
	"open_memstream":                         "stdio.h",
	"open_wmemstream":                        "wchar.h",
	"openat":                                 "fcntl.h",
	"opendir":                                "dirent.h",
	"openlog":                                "syslog.h",
	"pathconf":                               "unistd.h",
	"pause":                                  "unistd.h",
	"pclose":                                 "stdio.h",
	"perror":                                 "errno.h",
	"pfctlinput":                             "sys/socket.h",
	"pipe":                                   "unistd.h",
	"pipe2":                                  "unistd.h",
	"poll":                                   "sys/select.h",
	"popen":                                  "stdio.h",
	"posix2time":                             "time.h",
	"posix_fadvise":                          "fcntl.h",
	"posix_fallocate":                        "fcntl.h",
	"posix_madvise":                          "sys/mman.h",
	"posix_memalign":                         "stdlib.h",
	"posix_openpt":                           "stdlib.h",
	"pow":                                    "math.h",
	"powf":                                   "math.h",
	"powl":                                   "math.h",
	"ppoll":                                  "sys/select.h",
	"pread":                                  "unistd.h",
	"preadv":                                 "sys/uio.h",
	"printf":                                 "stdio.h",
	"prlimit":                                "sys/resource.h",
	"process_vm_readv":                       "sys/uio.h",
	"process_vm_writev":                      "sys/uio.h",
	"profil":                                 "unistd.h",
	"program_invocation_name":                "errno.h",
	"pselect":                                "sys/select.h",
	"psignal":                                "signal.h",
	"psort":                                  "stdlib.h",
	"psort_b":                                "stdlib.h",
	"psort_r":                                "stdlib.h",
	"pthread_atfork":                         "pthread.h",
	"pthread_attr_destroy":                   "pthread.h",
	"pthread_attr_getdetachstate":            "pthread.h",
	"pthread_attr_getguardsize":              "pthread.h",
	"pthread_attr_getinheritsched":           "pthread.h",
	"pthread_attr_getschedparam":             "pthread.h",
	"pthread_attr_getschedpolicy":            "pthread.h",
	"pthread_attr_getscope":                  "pthread.h",
	"pthread_attr_getstack":                  "pthread.h",
	"pthread_attr_getstackaddr":              "pthread.h",
	"pthread_attr_getstacksize":              "pthread.h",
	"pthread_attr_init":                      "pthread.h",
	"pthread_attr_setdetachstate":            "pthread.h",
	"pthread_attr_setguardsize":              "pthread.h",
	"pthread_attr_setinheritsched":           "pthread.h",
	"pthread_attr_setschedparam":             "pthread.h",
	"pthread_attr_setschedpolicy":            "pthread.h",
	"pthread_attr_setscope":                  "pthread.h",
	"pthread_attr_setstack":                  "pthread.h",
	"pthread_attr_setstackaddr":              "pthread.h",
	"pthread_attr_setstacksize":              "pthread.h",
	"pthread_cancel":                         "pthread.h",
	"pthread_cleanup_pop":                    "pthread.h",
	"pthread_cleanup_push":                   "pthread.h",
	"pthread_cond_broadcast":                 "pthread.h",
	"pthread_cond_destroy":                   "pthread.h",
	"pthread_cond_init":                      "pthread.h",
	"pthread_cond_signal":                    "pthread.h",
	"pthread_cond_signal_thread_np":          "pthread.h",
	"pthread_cond_timedwait":                 "pthread.h",
	"pthread_cond_timedwait_relative_np":     "pthread.h",
	"pthread_cond_wait":                      "pthread.h",
	"pthread_condattr_destroy":               "pthread.h",
	"pthread_condattr_getpshared":            "pthread.h",
	"pthread_condattr_init":                  "pthread.h",
	"pthread_condattr_setpshared":            "pthread.h",
	"pthread_cpu_number_np":                  "pthread.h",
	"pthread_create":                         "pthread.h",
	"pthread_create_suspended_np":            "pthread.h",
	"pthread_detach":                         "pthread.h",
	"pthread_equal":                          "pthread.h",
	"pthread_exit":                           "pthread.h",
	"pthread_from_mach_thread_np":            "pthread.h",
	"pthread_get_stackaddr_np":               "pthread.h",
	"pthread_get_stacksize_np":               "pthread.h",
	"pthread_getconcurrency":                 "pthread.h",
	"pthread_getname_np":                     "pthread.h",
	"pthread_getschedparam":                  "pthread.h",
	"pthread_getspecific":                    "pthread.h",
	"pthread_getugid_np":                     "unistd.h",
	"pthread_is_threaded_np":                 "pthread.h",
	"pthread_jit_write_freeze_callbacks_np":  "pthread.h",
	"pthread_jit_write_protect_np":           "pthread.h",
	"pthread_jit_write_protect_supported_np": "pthread.h",
	"pthread_jit_write_with_callback_np":     "pthread.h",
	"pthread_join":                           "pthread.h",
	"pthread_key_create":                     "pthread.h",
	"pthread_key_delete":                     "pthread.h",
	"pthread_kill":                           "pthread.h",
	"pthread_mach_thread_np":                 "pthread.h",
	"pthread_main_np":                        "pthread.h",
	"pthread_mutex_destroy":                  "pthread.h",
	"pthread_mutex_getprioceiling":           "pthread.h",
	"pthread_mutex_init":                     "pthread.h",
	"pthread_mutex_lock":                     "pthread.h",
	"pthread_mutex_setprioceiling":           "pthread.h",
	"pthread_mutex_trylock":                  "pthread.h",
	"pthread_mutex_unlock":                   "pthread.h",
	"pthread_mutexattr_destroy":              "pthread.h",
	"pthread_mutexattr_getpolicy_np":         "pthread.h",
	"pthread_mutexattr_getprioceiling":       "pthread.h",
	"pthread_mutexattr_getprotocol":          "pthread.h",
	"pthread_mutexattr_getpshared":           "pthread.h",
	"pthread_mutexattr_gettype":              "pthread.h",
	"pthread_mutexattr_init":                 "pthread.h",
	"pthread_mutexattr_setpolicy_np":         "pthread.h",
	"pthread_mutexattr_setprioceiling":       "pthread.h",
	"pthread_mutexattr_setprotocol":          "pthread.h",
	"pthread_mutexattr_setpshared":           "pthread.h",
	"pthread_mutexattr_settype":              "pthread.h",
	"pthread_once":                           "pthread.h",
	"pthread_rwlock_destroy":                 "pthread.h",
	"pthread_rwlock_init":                    "pthread.h",
	"pthread_rwlock_rdlock":                  "pthread.h",
	"pthread_rwlock_tryrdlock":               "pthread.h",
	"pthread_rwlock_trywrlock":               "pthread.h",
	"pthread_rwlock_unlock":                  "pthread.h",
	"pthread_rwlock_wrlock":                  "pthread.h",
	"pthread_rwlockattr_destroy":             "pthread.h",
	"pthread_rwlockattr_getpshared":          "pthread.h",
	"pthread_rwlockattr_init":                "pthread.h",
	"pthread_rwlockattr_setpshared":          "pthread.h",
	"pthread_self":                           "pthread.h",
	"pthread_setcancelstate":                 "pthread.h",
	"pthread_setcanceltype":                  "pthread.h",
	"pthread_setconcurrency":                 "pthread.h",
	"pthread_setname_np":                     "pthread.h",
	"pthread_setschedparam":                  "pthread.h",
	"pthread_setspecific":                    "pthread.h",
	"pthread_setugid_np":                     "unistd.h",
	"pthread_sigmask":                        "pthread.h",
	"pthread_testcancel":                     "pthread.h",
	"pthread_threadid_np":                    "pthread.h",
	"pthread_yield_np":                       "pthread.h",
	"ptsname":                                "stdlib.h",
	"ptsname_r":                              "stdlib.h",
	"putc":                                   "stdio.h",
	"putc_unlocked":                          "stdio.h",
	"putchar":                                "stdio.h",
	"putchar_unlocked":                       "stdio.h",
	"putenv":                                 "stdlib.h",
	"puts":                                   "stdio.h",
	"putw":                                   "stdio.h",
	"putwc":                                  "wchar.h",
	"putwchar":                               "wchar.h",
	"pwrite":                                 "unistd.h",
	"pwritev":                                "sys/uio.h",
	"qsort":                                  "stdlib.h",
	"qsort_b":                                "stdlib.h",
	"qsort_r":                                "stdlib.h",
	"quick_exit":                             "stdlib.h",
	"radixsort":                              "stdlib.h",
	"raise":                                  "signal.h",
	"rand":                                   "stdlib.h",
	"rand_r":                                 "stdlib.h",
	"random":                                 "stdlib.h",
	"rcmd":                                   "unistd.h",
	"rcmd_af":                                "unistd.h",
	"read":                                   "unistd.h",
	"readdir":                                "dirent.h",
	"readdir_r":                              "dirent.h",
	"readlink":                               "unistd.h",
	"readv":                                  "sys/uio.h",
	"realloc":                                "stdlib.h",
	"reallocarray":                           "stdlib.h",
	"realpath":                               "stdlib.h",
	"reboot":                                 "unistd.h",
	"recv":                                   "sys/socket.h",
	"recvfrom":                               "sys/socket.h",
	"recvmmsg":                               "sys/socket.h",
	"recvmsg":                                "sys/socket.h",
	"remainder":                              "math.h",
	"remainderf":                             "math.h",
	"remainderl":                             "math.h",
	"remove":                                 "stdio.h",
	"remquo":                                 "math.h",
	"remquof":                                "math.h",
	"remquol":                                "math.h",
	"rename":                                 "stdio.h",
	"revoke":                                 "unistd.h",
	"rewind":                                 "stdio.h",
	"rewinddir":                              "dirent.h",
	"rindex":                                 "string.h",
	"rint":                                   "math.h",
	"rintf":                                  "math.h",
	"rintl":                                  "math.h",
	"rinttol":                                "math.h",
	"rmdir":                                  "unistd.h",
	"round":                                  "math.h",
	"roundf":                                 "math.h",
	"roundl":                                 "math.h",
	"roundtol":                               "math.h",
	"rpmatch":                                "stdlib.h",
	"rresvport":                              "unistd.h",
	"rresvport_af":                           "unistd.h",
	"ruserok":                                "unistd.h",
	"sbrk":                                   "unistd.h",
	"scalb":                                  "math.h",
	"scalbln":                                "math.h",
	"scalblnf":                               "math.h",
	"scalblnl":                               "math.h",
	"scalbn":                                 "math.h",
	"scalbnf":                                "math.h",
	"scalbnl":                                "math.h",
	"scandir":                                "dirent.h",
	"scandir_b":                              "dirent.h",
	"scandirat":                              "dirent.h",
	"scandirat_b":                            "dirent.h",
	"scanf":                                  "stdio.h",
	"searchfs":                               "unistd.h",
	"secure_getenv":                          "stdlib.h",
	"seed48":                                 "stdlib.h",
	"seekdir":                                "dirent.h",
	"select":                                 "sys/select.h",
	"send":                                   "sys/socket.h",
	"sendfile":                               "sys/socket.h",
	"sendmmsg":                               "sys/socket.h",
	"sendmsg":                                "sys/socket.h",
	"sendto":                                 "sys/socket.h",
	"setattrlist":                            "fcntl.h",
	"setattrlistat":                          "fcntl.h",
	"setbuf":                                 "stdio.h",
	"setbuffer":                              "stdio.h",
	"setdomainname":                          "unistd.h",
	"setegid":                                "unistd.h",
	"setenv":                                 "stdlib.h",
	"seteuid":                                "unistd.h",
	"setgid":                                 "unistd.h",
	"setgroups":                              "unistd.h",
	"sethostid":                              "unistd.h",
	"sethostname":                            "unistd.h",
	"setiopolicy_np":                         "sys/resource.h",
	"setitimer":                              "sys/time.h",
	"setjmp":                                 "setjmp.h",
	"setkey":                                 "stdlib.h",
	"setlinebuf":                             "stdio.h",
	"setlocale":                              "locale.h",
	"setlogin":                               "unistd.h",
	"setlogmask":                             "syslog.h",
	"setmode":                                "unistd.h",
	"setpgid":                                "unistd.h",
	"setpgrp":                                "unistd.h",
	"setpriority":                            "sys/resource.h",
	"setprogname":                            "stdlib.h",
	"setregid":                               "unistd.h",
	"setreuid":                               "unistd.h",
	"setrgid":                                "unistd.h",
	"setrlimit":                              "sys/resource.h",
	"setruid":                                "unistd.h",
	"setsgroups_np":                          "unistd.h",
	"setsid":                                 "unistd.h",
	"setsockopt":                             "sys/socket.h",
	"setstate":                               "stdlib.h",
	"settimeofday":                           "sys/time.h",
	"setuid":                                 "unistd.h",
	"setusershell":                           "unistd.h",
	"setvbuf":                                "stdio.h",
	"setwgroups_np":                          "unistd.h",
	"shm_open":                               "sys/mman.h",
	"shm_unlink":                             "sys/mman.h",
	"shutdown":                               "sys/socket.h",
	"sigaction":                              "signal.h",
	"sigaddset":                              "signal.h",
	"sigaltstack":                            "signal.h",
	"sigblock":                               "signal.h",
	"sigdelset":                              "signal.h",
	"sigemptyset":                            "signal.h",
	"sigfillset":                             "signal.h",
	"sighold":                                "signal.h",
	"sigignore":                              "signal.h",
	"siginterrupt":                           "signal.h",
	"sigismember":                            "signal.h",
	"siglongjmp":                             "setjmp.h",
	"signal":                                 "signal.h",
	"signbit":                                "math.h",
	"significand":                            "math.h",
	"sigpause":                               "signal.h",
	"sigpending":                             "signal.h",
	"sigprocmask":                            "signal.h",
	"sigrelse":                               "signal.h",
	"sigset":                                 "signal.h",
	"sigsetjmp":                              "setjmp.h",
	"sigsetmask":                             "signal.h",
	"sigsuspend":                             "signal.h",
	"sigtimedwait":                           "signal.h",
	"sigvec":                                 "signal.h",
	"sigwait":                                "signal.h",
	"sigwaitinfo":                            "signal.h",
	"sin":                                    "math.h",
	"sinf":                                   "math.h",
	"sinh":                                   "math.h",
	"sinhf":                                  "math.h",
	"sinhl":                                  "math.h",
	"sinl":                                   "math.h",
	"sleep":                                  "unistd.h",
	"snprintf":                               "stdio.h",
	"sockatmark":                             "sys/socket.h",
	"socket":                                 "sys/socket.h",
	"socketpair":                             "sys/socket.h",
	"sprintf":                                "stdio.h",
	"sqrt":                                   "math.h",
	"sqrtf":                                  "math.h",
	"sqrtl":                                  "math.h",
	"sradixsort":                             "stdlib.h",
	"srand":                                  "stdlib.h",
	"srand48":                                "stdlib.h",
	"sranddev":                               "stdlib.h",
	"srandom":                                "stdlib.h",
	"srandomdev":                             "stdlib.h",
	"sscanf":                                 "stdio.h",
	"stat":                                   "sys/stat.h",
	"stat64":                                 "sys/stat.h",
	"static_assert":                          "assert.h",
	"statx":                                  "sys/stat.h",
	"statx64_np":                             "sys/stat.h",
	"statx_np":                               "sys/stat.h",
	"stpcpy":                                 "string.h",
	"stpncpy":                                "string.h",
	"strcasecmp":                             "string.h",
	"strcasestr":                             "string.h",
	"strcat":                                 "string.h",
	"strchr":                                 "string.h",
	"strchrnul":                              "string.h",
	"strcmp":                                 "string.h",
	"strcoll":                                "string.h",
	"strcpy":                                 "string.h",
	"strcspn":                                "string.h",
	"strdup":                                 "string.h",
	"strerror":                               "errno.h",
	"strerror_r":                             "errno.h",
	"strftime":                               "time.h",
	"strlcat":                                "string.h",
	"strlcpy":                                "string.h",
	"strlen":                                 "string.h",
	"strmode":                                "string.h",
	"strncasecmp":                            "string.h",
	"strncat":                                "string.h",
	"strncmp":                                "string.h",
	"strncpy":                                "string.h",
	"strndup":                                "string.h",
	"strnlen":                                "string.h",
	"strnstr":                                "string.h",
	"strpbrk":                                "string.h",
	"strptime":                               "time.h",
	"strrchr":                                "string.h",
	"strsep":                                 "string.h",
	"strsignal":                              "string.h",
	"strsignal_r":                            "string.h",
	"strspn":                                 "string.h",
	"strstr":                                 "string.h",
	"strtod":                                 "stdlib.h",
	"strtof":                                 "stdlib.h",
	"strtofflags":                            "unistd.h",
	"strtoimax":                              "stdlib.h",
	"strtok":                                 "string.h",
	"strtok_r":                               "string.h",
	"strtol":                                 "stdlib.h",
	"strtold":                                "stdlib.h",
	"strtoll":                                "stdlib.h",
	"strtonum":                               "stdlib.h",
	"strtoq":                                 "stdlib.h",
	"strtoul":                                "stdlib.h",
	"strtoull":                               "stdlib.h",
	"strtoumax":                              "stdlib.h",
	"strtouq":                                "stdlib.h",
	"strxfrm":                                "string.h",
	"swab":                                   "string.h",
	"swapon":                                 "unistd.h",
	"swprintf":                               "wchar.h",
	"swscanf":                                "wchar.h",
	"symlink":                                "unistd.h",
	"sync":                                   "unistd.h",
	"sync_volume_np":                         "unistd.h",
	"syscall":                                "unistd.h",
	"sysconf":                                "unistd.h",
	"sysctl":                                 "sys/sysctl.h",
	"sysctlbyname":                           "sys/sysctl.h",
	"sysctlnametomib":                        "sys/sysctl.h",
	"syslog":                                 "syslog.h",
	"system":                                 "stdlib.h",
	"tan":                                    "math.h",
	"tanf":                                   "math.h",
	"tanh":                                   "math.h",
	"tanhf":                                  "math.h",
	"tanhl":                                  "math.h",
	"tanl":                                   "math.h",
	"tcgetpgrp":                              "unistd.h",
	"tcsetpgrp":                              "unistd.h",
	"telldir":                                "dirent.h",
	"tempnam":                                "stdio.h",
	"tgamma":                                 "math.h",
	"tgammaf":                                "math.h",
	"tgammal":                                "math.h",
	"time":                                   "time.h",
	"time2posix":                             "time.h",
	"timegm":                                 "time.h",
	"timelocal":                              "time.h",
	"timeradd":                               "sys/time.h",
	"timerclear":                             "sys/time.h",
	"timercmp":                               "sys/time.h",
	"timerisset":                             "sys/time.h",
	"timersub":                               "sys/time.h",
	"timespec_get":                           "time.h",
	"timespec_getres":                        "time.h",
	"timevalcmp":                             "sys/time.h",
	"timezone":                               "time.h",
	"timingsafe_bcmp":                        "string.h",
	"timingsafe_memcmp":                      "string.h",
	"tmpfile":                                "stdio.h",
	"tmpnam":                                 "stdio.h",
	"toascii":                                "ctype.h",
	"tolower":                                "ctype.h",
	"toupper":                                "ctype.h",
	"trunc":                                  "math.h",
	"truncate":                               "unistd.h",
	"truncf":                                 "math.h",
	"truncl":                                 "math.h",
	"ttyname":                                "unistd.h",
	"ttyname_r":                              "unistd.h",
	"ttyslot":                                "unistd.h",
	"tzset":                                  "time.h",
	"tzsetwall":                              "time.h",
	"ualarm":                                 "unistd.h",
	"umask":                                  "sys/stat.h",
	"umaskx_np":                              "sys/stat.h",
	"undelete":                               "unistd.h",
	"ungetc":                                 "stdio.h",
	"ungetwc":                                "wchar.h",
	"unlink":                                 "unistd.h",
	"unlinkat":                               "unistd.h",
	"unlockpt":                               "stdlib.h",
	"unsetenv":                               "stdlib.h",
	"unwhiteout":                             "unistd.h",
	"uselocale":                              "locale.h",
	"usleep":                                 "unistd.h",
	"utimensat":                              "fcntl.h",
	"utimes":                                 "fcntl.h",
	"va_arg":                                 "stdarg.h",
	"va_copy":                                "stdarg.h",
	"va_end":                                 "stdarg.h",
	"va_list":                                "stdarg.h",
	"va_start":                               "stdarg.h",
	"valloc":                                 "stdlib.h",
	"vasprintf":                              "stdio.h",
	"vdprintf":                               "stdio.h",
	"vfork":                                  "unistd.h",
	"vfprintf":                               "stdio.h",
	"vfscanf":                                "stdio.h",
	"vfwprintf":                              "wchar.h",
	"vfwscanf":                               "wchar.h",
	"vprintf":                                "stdio.h",
	"vscanf":                                 "stdio.h",
	"vsnprintf":                              "stdio.h",
	"vsprintf":                               "stdio.h",
	"vsscanf":                                "stdio.h",
	"vswprintf":                              "wchar.h",
	"vswscanf":                               "wchar.h",
	"vsyslog":                                "syslog.h",
	"vwprintf":                               "wchar.h",
	"vwscanf":                                "wchar.h",
	"wait":                                   "sys/wait.h",
	"wait3":                                  "sys/wait.h",
	"wait4":                                  "sys/wait.h",
	"waitid":                                 "sys/wait.h",
	"waitpid":                                "sys/wait.h",
	"wcpcpy":                                 "wchar.h",
	"wcpncpy":                                "wchar.h",
	"wcrtomb":                                "wchar.h",
	"wcscasecmp":                             "wchar.h",
	"wcscat":                                 "wchar.h",
	"wcschr":                                 "wchar.h",
	"wcscmp":                                 "wchar.h",
	"wcscoll":                                "wchar.h",
	"wcscpy":                                 "wchar.h",
	"wcscspn":                                "wchar.h",
	"wcsdup":                                 "wchar.h",
	"wcsftime":                               "wchar.h",
	"wcslcat":                                "wchar.h",
	"wcslcpy":                                "wchar.h",
	"wcslen":                                 "wchar.h",
	"wcsncasecmp":                            "wchar.h",
	"wcsncat":                                "wchar.h",
	"wcsncmp":                                "wchar.h",
	"wcsncpy":                                "wchar.h",
	"wcsnlen":                                "wchar.h",
	"wcsnrtombs":                             "wchar.h",
	"wcspbrk":                                "wchar.h",
	"wcsrchr":                                "wchar.h",
	"wcsrtombs":                              "wchar.h",
	"wcsspn":                                 "wchar.h",
	"wcsstr":                                 "wchar.h",
	"wcstod":                                 "wchar.h",
	"wcstof":                                 "wchar.h",
	"wcstok":                                 "wchar.h",
	"wcstol":                                 "wchar.h",
	"wcstold":                                "wchar.h",
	"wcstoll":                                "wchar.h",
	"wcstombs":                               "stdlib.h",
	"wcstoul":                                "wchar.h",
	"wcstoull":                               "wchar.h",
	"wcswidth":                               "wchar.h",
	"wcsxfrm":                                "wchar.h",
	"wctob":                                  "wchar.h",
	"wctomb":                                 "stdlib.h",
	"wcwidth":                                "wchar.h",
	"wmemchr":                                "wchar.h",
	"wmemcmp":                                "wchar.h",
	"wmemcpy":                                "wchar.h",
	"wmemmove":                               "wchar.h",
	"wmemset":                                "wchar.h",
	"wprintf":                                "wchar.h",
	"write":                                  "unistd.h",
	"writev":                                 "sys/uio.h",
	"wscanf":                                 "wchar.h",
	"y0":                                     "math.h",
	"y1":                                     "math.h",
	"yield":                                  "pthread.h",
	"yn":                                     "math.h",
}

var nsNames = [...]string{"__builtin_*", "assert.h", "ctype.h", "dirent.h", "dlfcn.h", "errno.h", "fcntl.h", "getopt.h", "locale.h", "math.h", "pthread.h", "setjmp.h", "signal.h", "stdarg.h", "stdio.h", "stdlib.h", "string.h", "sys/mman.h", "sys/resource.h", "sys/select.h", "sys/socket.h", "sys/stat.h", "sys/sysctl.h", "sys/time.h", "sys/uio.h", "sys/wait.h", "syslog.h", "time.h", "unistd.h", "wchar.h"}

var guardNS = map[string]map[string]bool{
	"calloc_sizeof_first": {"alloc": true, "stdlib.h": true},
	"domain":              {"math.h": true},
	"endptr":              {"stdlib.h": true},
	"errno_zero":          {"stdlib.h": true},
	"map_failed":          {"sys/mman.h": true},
	"monotonic":           {"sys/time.h": true, "time.h": true},
	"ptr_ovf_check":       {"stdio.h": true, "stdlib.h": true, "string.h": true, "unistd.h": true},
	"ret_neg":             {"dirent.h": true, "fcntl.h": true, "stdio.h": true, "sys/mman.h": true, "sys/select.h": true, "sys/socket.h": true, "sys/stat.h": true, "sys/uio.h": true, "sys/wait.h": true, "unistd.h": true},
	"stacksz_array":       {"pthread.h": true, "signal.h": true, "unistd.h": true},
	"uchar":               {"ctype.h": true},
	"va_arg_array":        {"stdarg.h": true},
	"va_end":              {"stdarg.h": true},
}

var guardNames = [...]string{"ret_neg", "domain", "uchar", "errno_zero", "endptr", "va_end", "map_failed", "monotonic", "stacksz_array", "ptr_ovf_check", "calloc_sizeof_first", "va_arg_array"}

var guardCol = map[string]string{"ret_neg": "n_ret_neg_check", "domain": "n_domain_guard", "uchar": "n_uchar_cast", "errno_zero": "n_errno_zero", "endptr": "n_endptr", "va_end": "n_va_end", "map_failed": "n_map_failed", "monotonic": "n_monotonic_clock", "stacksz_array": "n_stacksz_array", "ptr_ovf_check": "n_ptr_ovf_check", "calloc_sizeof_first": "n_calloc_transposed", "va_arg_array": "n_va_arg_array"}

var magicOK = map[int64]bool{-1: true, 0: true, 1: true, 2: true, 3: true, 4: true, 6: true, 7: true, 8: true, 10: true, 12: true, 16: true, 24: true, 32: true, 60: true, 64: true, 100: true, 128: true, 255: true, 256: true, 365: true, 512: true, 1000: true, 1024: true, 4096: true, 65535: true}

var lockGeneric = map[string]bool{"lck": true, "lock": true, "locks": true, "mutex": true, "sem": true, "spin": true, "spinlock": true}

var eventWaitFn = map[string]bool{"epoll_pwait": true, "epoll_pwait2": true, "epoll_wait": true, "io_uring_enter": true, "io_uring_peek_cqe": true, "io_uring_sqring_wait": true, "io_uring_submit_and_wait": true, "io_uring_wait_cqe": true, "io_uring_wait_cqes": true, "kevent": true}

var eventCreateFn = map[string]bool{"epoll_create": true, "epoll_create1": true, "io_uring_queue_init": true, "io_uring_queue_init_mem": true, "io_uring_queue_init_params": true, "io_uring_setup": true, "kqueue": true, "kqueue1": true, "kqueuex": true}

var typeSizeTable = map[string]int32{
	"_Bool":              1,
	"bool":               1,
	"char":               1,
	"double":             8,
	"float":              4,
	"gid_t":              4,
	"int":                4,
	"int16_t":            2,
	"int32_t":            4,
	"int64_t":            8,
	"int8_t":             1,
	"intptr_t":           8,
	"long":               8,
	"long double":        16,
	"long int":           8,
	"long long":          8,
	"mode_t":             4,
	"off_t":              8,
	"pid_t":              4,
	"pthread_t":          8,
	"ptrdiff_t":          8,
	"short":              2,
	"short int":          2,
	"signed char":        1,
	"size_t":             8,
	"ssize_t":            8,
	"time_t":             8,
	"uid_t":              4,
	"uint16_t":           2,
	"uint32_t":           4,
	"uint64_t":           8,
	"uint8_t":            1,
	"uintptr_t":          8,
	"unsigned":           4,
	"unsigned char":      1,
	"unsigned int":       4,
	"unsigned long":      8,
	"unsigned long int":  8,
	"unsigned long long": 8,
	"unsigned short":     2,
	"unsigned short int": 2,
}

var typeAlignTable = map[string]int32{"long double": 16}

const ptrSize = 8

var evTimeoutIdx = map[string]int{"epoll_pwait": 3, "epoll_pwait2": 3, "epoll_wait": 3, "kevent": 5}

var evBatchIdx = map[string]int{"epoll_pwait": 2, "epoll_pwait2": 2, "epoll_wait": 2, "kevent": 4}

var libcAllocNames = map[string]bool{"malloc": true, "calloc": true, "realloc": true, "free": true, "aligned_alloc": true, "posix_memalign": true, "memalign": true, "valloc": true, "reallocarray": true, "strdup": true, "strndup": true}

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
	{name: "addr_taken",
		note: "the address of a local taken and handed to something else",
		cols: []columnShape{
			{"id", "int", false},
			{"symbol_id", "int", true},
			{"file_id", "int", false},
			{"name", "text", false},
			{"line", "int", false},
			{"kind", "text", false},
		}},
	{name: "allocsites",
		note: "every allocation site, with the size the compiler saw",
		cols: []columnShape{
			{"id", "int", false},
			{"symbol_id", "int", false},
			{"file_id", "int", false},
			{"fn", "text", false},
			{"size_expr", "text", false},
			{"line", "int", false},
		}},
	{name: "apiuse",
		note: "standard-library entry points reached, and how often",
		cols: []columnShape{
			{"id", "int", false},
			{"symbol_id", "int", false},
			{"file_id", "int", false},
			{"ns", "text", false},
			{"fn", "text", false},
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
	{name: "callsites",
		note: "every distinct line a resolved call was seen on",
		cols: []columnShape{
			{"caller_id", "int", false},
			{"callee_id", "int", false},
			{"line", "int", false},
		}},
	{name: "config_blocks",
		note: "a #if/#ifdef/#else block and the condition on it",
		cols: []columnShape{
			{"id", "int", false},
			{"file_id", "int", false},
			{"directive", "text", false},
			{"expr", "text", false},
			{"line", "int", false},
			{"is_config", "int", false},
		}},
	{name: "declarations",
		note: "a declaration that is not a function: var, const, typedef",
		cols: []columnShape{
			{"id", "int", false},
			{"file_id", "int", false},
			{"name", "text", false},
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
	{name: "eventops",
		note: "event-loop registration: what was registered and where",
		cols: []columnShape{
			{"id", "int", false},
			{"symbol_id", "int", false},
			{"file_id", "int", false},
			{"family", "text", false},
			{"fn", "text", false},
			{"args", "text", false},
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
	{name: "globals",
		note: "a mutable global, and the threads that can see it",
		cols: []columnShape{
			{"id", "int", false},
			{"file_id", "int", false},
			{"module_id", "int", true},
			{"name", "text", false},
			{"type", "text", false},
			{"line", "int", false},
			{"is_static", "int", false},
			{"is_const", "int", false},
			{"is_volatile", "int", false},
			{"is_atomic", "int", false},
			{"is_array", "int", false},
			{"ptr_depth", "int", false},
			{"has_init", "int", false},
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
	{name: "include_cycles",
		note: "a cycle in the include graph",
		cols: []columnShape{
			{"id", "int", false},
			{"a_path", "text", false},
			{"b_path", "text", false},
			{"length", "int", false},
			{"members", "text", false},
		}},
	{name: "layout",
		note: "a struct or union layout: offsets, sizes, padding",
		cols: []columnShape{
			{"symbol_id", "int", false},
			{"ordinal", "int", false},
			{"byte_off", "int", false},
			{"byte_size", "int", false},
			{"pad_before", "int", false},
			{"exact", "int", false},
			{"ptr_depth", "int", false},
			{"array_len", "int", false},
			{"is_fnptr", "int", false},
			{"depth", "int", false},
			{"in_union", "int", false},
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
	{name: "locks",
		note: "a lock, and whether it is taken in a consistent order",
		cols: []columnShape{
			{"id", "int", false},
			{"symbol_id", "int", false},
			{"file_id", "int", false},
			{"name", "text", false},
			{"line", "int", false},
		}},
	{name: "macros",
		note: "a macro invocation, and which definition it expands to",
		cols: []columnShape{
			{"symbol_id", "int", false},
			{"is_functionlike", "int", false},
			{"n_params", "int", false},
			{"body", "text", true},
			{"body_len", "int", false},
			{"is_multiline", "int", false},
			{"n_uses", "int", false},
		}},
	{name: "makefile_rules",
		note: "a make target, its prerequisites, and its recipe",
		cols: []columnShape{
			{"id", "int", false},
			{"path", "text", false},
			{"rule", "text", false},
			{"line", "int", false},
			{"n_objs", "int", false},
			{"n_srcs", "int", false},
			{"uses_ar", "int", false},
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
	{name: "memops",
		note: "raw memory operations: allocation, copy, free, and overlap",
		cols: []columnShape{
			{"id", "int", false},
			{"symbol_id", "int", false},
			{"file_id", "int", false},
			{"fn", "text", false},
			{"dst", "text", false},
			{"src", "text", false},
			{"size_arg", "text", false},
			{"size_buf", "text", false},
			{"dst_tail", "text", false},
			{"line", "int", false},
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
	{name: "reach",
		note: "a symbol reachable from an entry point, and at what depth",
		cols: []columnShape{
			{"symbol_id", "int", false},
			{"n_transitive", "int", false},
			{"n_transitive_out", "int", false},
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
	{name: "struct_size",
		note: "the size and alignment of a declared struct",
		cols: []columnShape{
			{"symbol_id", "int", false},
			{"total_size", "int", false},
			{"tail_pad", "int", false},
			{"total_pad", "int", false},
			{"max_align", "int", false},
			{"exact", "int", false},
			{"n_lines_64", "int", false},
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
			{"byte_start", "int", false},
			{"byte_end", "int", false},
			{"signature", "text", true},
			{"return_type", "text", true},
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
			{"n_comment_lines", "int", false},
			{"has_doc", "int", false},
			{"cyclomatic", "int", false},
			{"cognitive", "int", false},
			{"max_nesting", "int", false},
			{"n_tokens", "int", false},
			{"n_operators", "int", false},
			{"n_operands", "int", false},
			{"n_distinct_operators", "int", false},
			{"n_distinct_operands", "int", false},
			{"n_loops", "int", false},
			{"n_branches", "int", false},
			{"n_returns", "int", false},
			{"n_switch", "int", false},
			{"n_cases", "int", false},
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
			{"n_cmp", "int", false},
			{"n_shift", "int", false},
			{"n_arith", "int", false},
			{"n_regex_lit", "int", false},
			{"n_float_lit", "int", false},
			{"n_magic", "int", false},
			{"n_null_check", "int", false},
			{"n_lambda", "int", false},
			{"n_closure_capture", "int", false},
			{"n_calls", "int", false},
			{"n_dynamic_calls", "int", false},
			{"n_unresolved_calls", "int", false},
			{"fan_in", "int", false},
			{"fan_out", "int", false},
			{"n_callsites", "int", false},
			{"is_recursive", "int", false},
			{"risk_score", "int", false},
			{"n_memory", "int", false},
			{"n_alloc", "int", false},
			{"n_io", "int", false},
			{"n_stdio", "int", false},
			{"n_exec", "int", false},
			{"n_libm", "int", false},
			{"n_integer", "int", false},
			{"n_concurrency", "int", false},
			{"n_reentrancy", "int", false},
			{"is_inline", "int", false},
			{"is_variadic", "int", false},
			{"n_ptr_locals", "int", false},
			{"n_deref", "int", false},
			{"n_cast", "int", false},
			{"n_sizeof", "int", false},
			{"n_intrinsic", "int", false},
			{"n_atomic", "int", false},
			{"n_restrict", "int", false},
			{"n_likely", "int", false},
			{"n_builtin", "int", false},
			{"switch_in_loop", "int", false},
			{"libm_in_loop", "int", false},
			{"div_in_loop", "int", false},
			{"strlen_in_loop", "int", false},
			{"ret_null", "int", false},
			{"ret_neg", "int", false},
			{"ret_zero", "int", false},
			{"ret_val", "int", false},
			{"ret_void", "int", false},
			{"n_fnptr_calls", "int", false},
			{"n_macro_calls", "int", false},
			{"n_external_calls", "int", false},
			{"n_free", "int", false},
			{"n_const_cast", "int", false},
			{"n_toctou", "int", false},
			{"n_lock_acquire", "int", false},
			{"n_lock_release", "int", false},
			{"n_narrow_cast", "int", false},
			{"n_sign_cmp", "int", false},
			{"n_variadic_fmt", "int", false},
			{"n_memcpy", "int", false},
			{"n_allocsite", "int", false},
			{"n_global_write", "int", false},
			{"n_errno", "int", false},
			{"n_weak_random", "int", false},
			{"n_shift_var", "int", false},
			{"n_realloc_self", "int", false},
			{"n_vla", "int", false},
			{"n_getenv", "int", false},
			{"n_assert_side", "int", false},
			{"n_free_then_use", "int", false},
			{"n_epoll", "int", false},
			{"n_uring", "int", false},
			{"n_kqueue", "int", false},
			{"n_event_wait", "int", false},
			{"n_et_reg", "int", false},
			{"n_oneshot_reg", "int", false},
			{"n_write_ready", "int", false},
			{"n_err_flag", "int", false},
			{"n_rearm", "int", false},
			{"n_dereg", "int", false},
			{"n_eagain", "int", false},
			{"n_eintr", "int", false},
			{"n_uring_res", "int", false},
			{"n_uring_ring", "int", false},
			{"n_uring_barrier", "int", false},
			{"n_uring_sqpoll", "int", false},
			{"n_nonblock_set", "int", false},
			{"n_event_create", "int", false},
			{"n_event_destroy", "int", false},
			{"n_uring_sqe", "int", false},
			{"n_uring_seen", "int", false},
			{"n_uring_udata", "int", false},
			{"n_uring_link", "int", false},
			{"n_uring_stream_ops", "int", false},
			{"n_uring_teardown", "int", false},
			{"n_ev_timeout_indefinite", "int", false},
			{"n_ev_timeout_zero", "int", false},
			{"n_ev_batch_one", "int", false},
			{"n_kq_timer", "int", false},
			{"n_kq_timer_zero_data", "int", false},
			{"n_kq_receipt", "int", false},
			{"n_ret_neg_check", "int", false},
			{"n_domain_guard", "int", false},
			{"n_uchar_cast", "int", false},
			{"n_errno_zero", "int", false},
			{"n_endptr", "int", false},
			{"n_va_end", "int", false},
			{"n_map_failed", "int", false},
			{"n_monotonic_clock", "int", false},
			{"n_stacksz_array", "int", false},
			{"n_ptr_ovf_check", "int", false},
			{"n_calloc_transposed", "int", false},
			{"n_va_arg_array", "int", false},
		}},
	{name: "unresolved_calls",
		note: "a call we saw but could not point at a definition",
		cols: []columnShape{
			{"caller_id", "int", false},
			{"name", "text", false},
			{"n", "int", false},
			{"first_line", "int", false},
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

var skipDirs = map[string]bool{
	".git": true, ".hg": true, ".svn": true, ".jj": true, ".idea": true,
	".vscode": true, ".vs": true, ".claude": true,
	"node_modules": true, "bower_components": true, "vendor": true,
	"third_party": true, "thirdparty": true, "external": true,
	"externals": true, "deps": true, "Godeps": true, "_vendor": true,
	"__pycache__": true, ".mypy_cache": true, ".pytest_cache": true,
	".ruff_cache": true, ".tox": true, ".venv": true, "venv": true,
	"env": true, ".env": true, "virtualenv": true,
	"build": true, "_build": true, "dist": true, "out": true, "target": true,
	"bin": true, "obj": true, ".gradle": true,
	".next": true, ".nuxt": true, ".svelte-kit": true, ".parcel-cache": true,
	".turbo": true, ".cache": true,
	"coverage": true, "htmlcov": true, ".nyc_output": true,
	"site-packages": true,

	"CMakeFiles": true, ".deps": true, ".libs": true, "autom4te.cache": true,
}

var cExts = map[string]bool{".c": true, ".h": true, ".inc": true, ".cc": true}

const (
	maxFileBytes = 4 * 1024 * 1024
	maxLineBytes = 1024 * 1024
)

var generatedMarkers = []string{
	"@generated", "DO NOT EDIT", "Code generated by", "AUTO-GENERATED",
	"autogenerated", "This file was automatically generated",
	"Generated by the protocol buffer compiler", "@flow-generated",
}

type discoverResult struct {
	files []File
	parse []int32
	mods  []Module
}

func moduleOf(rel string) string {
	parts := strings.Split(filepath.ToSlash(rel), "/")
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
	case matchPathSeg(name, "test", "tests", "test-d", "spec", "specs",
		"__tests__", "__snapshots__", "testing", "e2e", "integration-tests",
		"integration_tests", "testdata", "test_data", "test-data", "fixture",
		"fixtures"):
		return "test"
	case matchVendorPath(name):
		return "vendor"
	case matchDirWord(name, "example", "examples", "sample", "samples",
		"demo", "demos"):
		return "example"
	case matchDirWord(name, "tool", "tools", "script", "scripts", "cmd", "bin"):
		return "tool"
	}
	return "source"
}

func matchPathSeg(p string, words ...string) bool {
	lower := strings.ToLower(p)
	for seg := range strings.SplitSeq(lower, "/") {
		if slices.Contains(words, seg) {
			return true
		}
	}
	return false
}

func matchVendorPath(p string) bool {
	lower := strings.ToLower(p)
	for seg := range strings.SplitSeq(lower, "/") {
		switch seg {
		case "vendor", "third_party", "thirdparty", "external",
			"node_modules", "deps":
			return true
		}
	}
	return false
}

func matchDirWord(p string, words ...string) bool {
	lower := strings.ToLower(p)
	for seg := range strings.SplitSeq(lower, "/") {
		if slices.Contains(words, seg) {
			return true
		}
	}
	return false
}

func isGeneratedName(name string) bool {
	lower := strings.ToLower(name)
	for _, pat := range []string{".min.", ".bundle.", ".gen.", ".generated.",
		".pb.", ".g.", "_pb2", ".designer."} {
		if strings.Contains(lower, pat) {
			return true
		}
	}
	if strings.HasSuffix(lower, ".g.dart") {
		return true
	}
	if strings.HasPrefix(lower, "zz_generated") {
		return true
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

func cTestName(fn string) bool {
	if strings.HasPrefix(fn, "test_") || strings.HasPrefix(fn, "t_") {
		return true
	}
	return strings.HasSuffix(fn, "_test.c") || strings.HasSuffix(fn, "_test.h")
}

var cmtPrefixes = [...]string{"//", "#", "/*", "*", "*/", `"""`, "'''", "--", ";;", "%"}

func isCommentLine(line string) bool {
	s := strings.TrimLeft(line, " \t")
	if len(s) > 3 {
		s = s[:3]
	} else if len(s) < 3 {

		for _, p := range cmtPrefixes {
			if s == p {
				return len(strings.TrimSpace(line)) > 0
			}
		}
		return false
	}
	for _, p := range cmtPrefixes {
		if s == p {
			return len(strings.TrimSpace(line)) > 0
		}
	}
	return false
}

type walker struct {
	g        *Graph
	root     string
	modID    map[string]int32
	realRoot string
	res      discoverResult
	opts     runOpts
}

type runOpts struct {
	includeTests     bool
	includeGenerated bool
	includeVendored  bool
	quiet            bool
	keepAST          bool
}

func discover(root string, g *Graph, opts runOpts) []int32 {
	w := &walker{g: g, root: root, modID: map[string]int32{},
		realRoot: realpath(root), opts: opts}
	w.walk(root, false)
	for i := range w.res.files {
		f := &w.res.files[i]
		if f.Parsed == 1 {
			w.res.parse = append(w.res.parse, f.ID)
		}
	}
	g.Modules = w.res.mods
	g.Files = w.res.files
	return w.res.parse
}

func (w *walker) walk(dir string, viaLink bool) {
	ents, err := os.ReadDir(dir)
	if err != nil {
		w.g.WalkErrors++
		return
	}
	type ent struct {
		name  string
		isDir bool
		link  bool
	}
	files := make([]ent, 0, len(ents))
	dirs := make([]ent, 0, len(ents))
	for _, e := range ents {
		name := e.Name()
		switch {
		case e.Type()&fs.ModeSymlink != 0:
			st, err := os.Stat(filepath.Join(dir, name))
			if err != nil {
				continue
			}
			if st.IsDir() {

				dirs = append(dirs, ent{name, true, true})
				continue
			}
			files = append(files, ent{name, false, true})
		case e.IsDir():
			dirs = append(dirs, ent{name, true, false})
		default:
			files = append(files, ent{name, false, false})
		}
	}
	sort.Slice(files, func(i, j int) bool { return files[i].name < files[j].name })
	sort.Slice(dirs, func(i, j int) bool { return dirs[i].name < dirs[j].name })
	for _, e := range files {
		w.consider(filepath.Join(dir, e.name), e.name, viaLink || e.link)
	}
	for _, e := range dirs {

		if e.link || skipDirs[e.name] || strings.HasPrefix(e.name, ".") {
			continue
		}
		w.walk(filepath.Join(dir, e.name), viaLink)
	}
}

var source [][]byte

func (w *walker) consider(full, fn string, viaLink bool) {
	ext := filepath.Ext(fn)
	if !cExts[ext] {
		return
	}
	st, err := os.Stat(full)
	if err != nil {
		return
	}
	if !st.Mode().IsRegular() {
		w.g.FilesSkippedSpecial++
		return
	}

	if viaLink {
		if rp := realpath(full); rp != full {
			if !strings.HasPrefix(rp, w.realRoot+string(filepath.Separator)) {
				w.g.FilesSkippedEscape++
				return
			}
		}
	}
	var data []byte
	tooBig := false
	if st.Size() > maxFileBytes {
		w.g.FilesSkippedBig++
		tooBig = true
	} else {
		data, err = os.ReadFile(full)
		if err != nil {
			w.g.FilesSkippedDenied++
			return
		}
		if hasLongLine(data) {
			w.g.FilesSkippedBig++
			tooBig = true
		}
	}
	rel := filepath.ToSlash(mustRel(w.root, full))
	nLines, sloc, blank, cmt, maxLine := fileLineStatsBytes(data)
	head := data
	if len(head) > 2000 {
		head = head[:2000]
	}
	test := b2i(matchPathSeg(rel, "test", "tests", "test-d", "spec", "specs",
		"__tests__", "__snapshots__", "testing", "e2e", "integration-tests",
		"integration_tests", "testdata", "test_data", "test-data", "fixture",
		"fixtures") || cTestName(fn))
	gen := b2i(isGenerated(fn, string(head)))
	vend := b2i(matchVendorPath(rel))
	mid := w.module(rel)
	parse := b2i(!tooBig && len(data) != 0 &&
		(w.opts.includeTests || test == 0) &&
		(w.opts.includeGenerated || gen == 0) &&
		(w.opts.includeVendored || vend == 0))

	sum := ""
	if len(data) > 0 {
		h := sha1.Sum(data)
		sum = hex.EncodeToString(h[:])
	}
	id := int32(len(w.res.files) + 1)
	source = append(source, data)
	w.res.files = append(w.res.files, File{})
	fl := &w.res.files[len(w.res.files)-1]
	cgZeroRow(unsafe.Pointer(fl), unsafe.Sizeof(*fl))
	fl.ID = id
	fl.path = cgPut(rel)
	fl.dir = cgPut(pathDir(rel))
	fl.basename = cgPut(fn)
	fl.ext = cgPut(ext)
	fl.lang = cgPut("c")
	fl.ModuleID = mid
	fl.Bytes = int32(len(data))
	fl.Lines = int32(nLines)
	fl.Sloc = int32(sloc)
	fl.BlankLines = int32(blank)
	fl.CommentLines = int32(cmt)
	fl.MaxLineLen = int32(maxLine)
	fl.sha1 = cgPut(sum)
	fl.Parsed = parse
	fl.IsTest = test
	fl.IsGenerated = gen
	fl.IsVendored = vend
}

func mustRel(base, p string) string {
	r, err := filepath.Rel(base, p)
	if err != nil {
		return filepath.Base(p)
	}
	return r
}

func (w *walker) module(rel string) int32 {
	name := moduleOf(rel)
	if id, ok := w.modID[name]; ok {
		return id
	}
	id := int32(len(w.res.mods) + 1)
	w.res.mods = append(w.res.mods, Module{})
	mo := &w.res.mods[len(w.res.mods)-1]
	cgZeroRow(unsafe.Pointer(mo), unsafe.Sizeof(*mo))
	mo.ID = id
	mo.name = cgPut(name)
	mo.kind = cgPut(moduleKind(name))
	w.modID[name] = id
	return id
}

func hasLongLine(data []byte) bool {
	n := 0
	for _, c := range data {
		if c == '\n' {
			n = 0
			continue
		}
		n++
		if n > maxLineBytes {
			return true
		}
	}
	return false
}

func fileLineStatsBytes(b []byte) (n, sloc, blank, cmt, maxLen int) {
	add := func(seg []byte) {
		if len(trimSpaceBytes(seg)) != 0 {
			sloc++
		} else {
			blank++
		}
		if isCommentSeg(seg) {
			cmt++
		}
		if r := runeLen(seg); r > maxLen {
			maxLen = r
		}
		n++
	}

	start, i := 0, 0
	for i < len(b) {
		if isSplitBound(b, i) {
			add(b[start:i])
			i = skipBoundary(b, i)
			start = i
			continue
		}
		i++
	}
	if start < len(b) {
		add(b[start:])
	}
	return
}

func isCommentSeg(s []byte) bool {
	i := 0
	for i < len(s) && isStripSpace(s[i]) {
		i++
	}
	head := s[i:]
	if len(head) > 3 {
		head = head[:3]
	}
	for _, p := range cmtPrefixes {
		if string(head) == p {
			return len(trimSpaceBytes(s)) != 0
		}
	}
	return false
}

func pathDir(rel string) string {
	i := strings.LastIndexByte(rel, '/')
	if i < 0 {
		return "."
	}
	return rel[:i]
}

func b2i(b bool) int32 {
	if b {
		return 1
	}
	return 0
}

func identEnd(b []byte, i int) int {
	if i >= len(b) || !isIdentStart(b[i]) {
		return i
	}
	j := i + 1
	for j < len(b) && isIdentPart(b[j]) {
		j++
	}
	return j
}

func skipHardWS(b []byte, i int) int {
	for i < len(b) && isHardWS(b[i]) {
		i++
	}
	return i
}

func skipHT(b []byte, i int) int {
	for i < len(b) && (b[i] == ' ' || b[i] == '\t') {
		i++
	}
	return i
}

func isWordByte(c byte) bool { return isIdentPart(c) }

func wEnd(b []byte, i int) int {
	for i < len(b) && isWordByte(b[i]) {
		i++
	}
	return i
}

func countByte(b []byte, c byte) int {
	n := 0
	for _, x := range b {
		if x == c {
			n++
		}
	}
	return n
}

func countStr(b []byte, s string) int {
	if len(s) == 0 {
		return 0
	}
	return bytes.Count(b, []byte(s))
}

func hasStr(b []byte, s string) bool { return bytes.Contains(b, []byte(s)) }

func countCast(b []byte) int {
	n := 0
	for i := 0; i+1 < len(b); i++ {
		if b[i] != '(' {
			continue
		}
		j := skipHardWS(b, i+1)
		if j+5 < len(b) && string(b[j:j+5]) == "const" && isHardWS(b[j+5]) {
			j = skipHardWS(b, j+5)
		}
		e := identEnd(b, j)
		if e == j {
			continue
		}
		k := skipHardWS(b, e)
		star := 0
		for k < len(b) && b[k] == '*' {
			star++
			k++
		}
		if star == 0 {
			continue
		}
		k = skipHardWS(b, k)
		if k < len(b) && b[k] == ')' {
			n++
			i = k
		}
	}
	return n
}

var compoundOps = [...]string{"+=", "-=", "*=", "/=", "%=", "&=", "|=", "^=", "<<=", ">>="}

func skipLine(b []byte, i int) int {
	for i < len(b) && b[i] != '\n' {
		i++
	}
	return i + 1
}

func intrinsicName(w string) bool {
	lo := func(c byte) bool {
		return (c >= 'a' && c <= 'z') || (c >= '0' && c <= '9') || c == '_'
	}
	splitAt := func(from int) bool {
		for j := from; j+1 < len(w); j++ {
			if w[j] != '_' {
				continue
			}
			ok := true
			for k := from; k < j; k++ {
				if !lo(w[k]) {
					ok = false
					break
				}
			}
			if !ok {
				continue
			}
			for k := j + 1; k < len(w); k++ {
				if !lo(w[k]) {
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
	if len(w) < 3 {
		return false
	}
	if w[0] == 'v' {
		return splitAt(1)
	}
	if strings.HasPrefix(w, "_mm") {
		return splitAt(3)
	}
	if strings.HasPrefix(w, "sv") {
		return splitAt(2)
	}
	return false
}

func atLineStart(b []byte, i int) bool {
	if i == 0 {
		return true
	}
	c := b[i-1]
	return c == '\n' || c == '\r' || c == 0x0b || c == 0x0c || c == 0x1c ||
		c == 0x1d || c == 0x1e
}

var blankPool = sync.Pool{New: func() any { return new([]byte) }}

func trimSpaceBytes(s []byte) []byte {
	a := 0
	for a < len(s) && isStripSpace(s[a]) {
		a++
	}
	b := len(s)
	for b > a && isStripSpace(s[b-1]) {
		b--
	}
	return s[a:b]
}

func i32(v int) int32 { return int32(v) }

func countPtrCast(b []byte) int { return countCast(b) }

func countMulSizeof(b []byte) int {
	n := 0
	for i := 0; i < len(b); {
		if b[i] == '*' {
			j := skipHardWS(b, i+1)
			if isWordAt(b, j, "sizeof") {
				n++
				i = j + 6
				continue
			}
		}

		if isWordAt(b, i, "sizeof") && !wordAfter(b, i+6) {
			j := skipHardWS(b, i+6)
			if j < len(b) && b[j] == '(' {
				k := indexByteFrom(b, ')', j+1)
				if k >= 0 {
					k = skipHardWS(b, k+1)
					if k < len(b) && b[k] == '*' {
						n++
						i = k + 1
						continue
					}
				}
			}
		}
		i++
	}
	return n
}

var fixedBufTypes = []string{"unsigned char", "uint8_t", "int8_t", "char"}

func countFixedBuffer(b []byte) int {
	n := 0
	for i := 0; i < len(b); i++ {
		if !isIdentStart(b[i]) || wordBefore(b, i) {
			continue
		}
		e := identEnd(b, i)
		w := string(b[i:e])
		ok := false
		for _, t := range fixedBufTypes {
			if w == t || (t == "unsigned char" && w == "unsigned") {
				ok = true
			}
		}
		if !ok {
			continue
		}
		j := skipHardWS(b, e)
		k := identEnd(b, j)
		if k == j {
			continue
		}
		j = skipHardWS(b, k)
		if j >= len(b) || b[j] != '[' {
			continue
		}
		j = skipHT(b, j+1)
		st := j
		for j < len(b) && isDigit(b[j]) {
			j++
		}
		if j == st {
			continue
		}
		m := skipHT(b, j)
		if m < len(b) && b[m] == ']' {
			n++
			i = m
		}
	}
	return n
}

func countVLAPat(b []byte) int {
	n := 0
	for i := 0; i < len(b); i++ {
		if !isIdentStart(b[i]) || wordBefore(b, i) {
			continue
		}
		e := identEnd(b, i)
		w := string(b[i:e])
		switch w {
		case "char", "int", "uint8_t", "double", "float":
		default:
			continue
		}
		j := skipHardWS(b, e)
		k := identEnd(b, j)
		if k == j {
			continue
		}
		j = skipHardWS(b, k)
		if j >= len(b) || b[j] != '[' {
			continue
		}
		j = skipHT(b, j+1)
		if j >= len(b) || !(b[j] == '_' || (b[j] >= 'a' && b[j] <= 'z')) {
			continue
		}
		m := identEnd(b, j)
		m = skipHardWS(b, m)
		if m < len(b) && b[m] == ']' {
			n++
			i = m
		}
	}
	return n
}

func countSignedCmp(b []byte) int {
	n := 0
	for i := 0; i+3 <= len(b); i++ {
		if !isWordAt(b, i, "int") || wordBefore(b, i) || wordAfter(b, i+3) {
			continue
		}
		j := skipHardWS(b, i+3)
		k := wEnd(b, j)
		if k == j {
			continue
		}
		j = skipHardWS(b, k)
		if j >= len(b) || b[j] != '=' || (j+1 < len(b) && b[j+1] == '=') {
			continue
		}
		j = skipHardWS(b, j+1)
		k = wEnd(b, j)
		if k == j {
			continue
		}
		j = skipHardWS(b, k)
		if j >= len(b) || b[j] != '-' {
			continue
		}
		j = skipHardWS(b, j+1)
		k = wEnd(b, j)
		if k > j {
			n++
		}
	}
	return n
}

type memopHitUnused struct{}

func isLockShaped(name string) bool {
	low := asciiLower(name)
	if strings.Contains(low, "lock") || strings.Contains(low, "mutex") ||
		strings.HasSuffix(low, "_lck") || strings.HasPrefix(low, "sem") ||
		strings.Contains(low, "spin") {
		return true
	}
	return false
}

var narrowTypes = [...]string{"uint8_t", "int8_t", "uint16_t", "int16_t",
	"uint32_t", "int32_t"}

func countNarrowCasts(b []byte) int {
	n := 0
	for i := 0; i+1 < len(b); i++ {
		if b[i] != '(' {
			continue
		}
		j := skipHardWS(b, i+1)
		hit := false
		for _, t := range narrowTypes {
			if isWordAt(b, j, t) && !wordAfter(b, j+len(t)) {
				hit = true
				break
			}
		}
		if !hit {
			continue
		}
		j += 0
		for _, t := range narrowTypes {
			if isWordAt(b, j, t) {
				j += len(t)
				break
			}
		}
		j = skipHardWS(b, j)
		if j >= len(b) || b[j] != ')' {
			continue
		}
		j = skipHardWS(b, j+1)
		if j < len(b) && b[j] == '(' {
			j = skipHardWS(b, j+1)
		}
		if j < len(b) && (isIdentStart(b[j]) || b[j] == '&' || b[j] == '*') {
			n++
			i = j
		}
	}
	return n
}

type signCmpHit struct{ name string }

func cmpWidth(b []byte, i int) int {
	for _, op := range [...]string{"<=", ">=", "==", "!=", "<", ">"} {
		if isWordAt(b, i, op) {
			return len(op)
		}
	}
	return 0
}

func scanSignCmps(b []byte, fn func(signCmpHit)) {
	for i := 0; i < len(b); {
		if n, name := signCmpArm1(b, i); n > 0 {
			fn(signCmpHit{name: name})
			i += n
			continue
		}
		if n, name := signCmpArm2(b, i); n > 0 {
			fn(signCmpHit{name: name})
			i += n
			continue
		}
		i++
	}
}

func signCmpArm1(b []byte, i int) (int, string) {
	if !isIdentStart(b[i]) || wordBefore(b, i) {
		return 0, ""
	}
	w := b[i:identEnd(b, i)]
	if string(w) != "if" && string(w) != "while" && string(w) != "for" {
		return 0, ""
	}
	j := skipHardWS(b, i+len(w))
	if j >= len(b) || b[j] != '(' {
		return 0, ""
	}
	j = skipHardWS(b, j+1)
	if j < len(b) && b[j] == '!' {
		j = skipHardWS(b, j+1)
	}
	nameEnd := identEnd(b, j)
	if nameEnd == j {
		return 0, ""
	}
	name := string(b[j:nameEnd])
	k := skipHardWS(b, nameEnd)
	w2 := cmpWidth(b, k)
	if w2 == 0 {
		return 0, ""
	}
	k += w2
	k = skipHardWS(b, k)
	if isWordAt(b, k, "sizeof") && !wordAfter(b, k+6) {
		m := skipHardWS(b, k+6)
		if m < len(b) && b[m] == '(' {
			m = skipHardWS(b, m+1)
			q := skipHardWS(b, wEnd(b, m))
			if q < len(b) && b[q] == ')' {
				return q + 1 - i, name
			}
		}

		return k + 6 - i, name
	}
	if e := identEnd(b, k); e > k {
		return e - i, name
	}
	return 0, ""
}

func signCmpArm2(b []byte, i int) (int, string) {
	if !isIdentStart(b[i]) || wordBefore(b, i) {
		return 0, ""
	}
	e := identEnd(b, i)
	if !sizeishName(string(b[i:e])) || wordAfter(b, e) {
		return 0, ""
	}
	k := skipHardWS(b, e)
	w2 := cmpWidth(b, k)
	if w2 == 0 {
		return 0, ""
	}
	k = skipHardWS(b, k+w2)
	if e2 := identEnd(b, k); e2 > k {
		return e2 - i, string(b[i:e])
	}
	return 0, ""
}

func gRetNeg(b []byte) int {
	n := 0
	for i := 0; i < len(b); {
		if m := retNegArm(b, i); m > 0 {
			n++
			i += m
			continue
		}
		i++
	}
	return n
}

func retNegArm(b []byte, i int) int {
	switch b[i] {
	case '<':
		if i+1 < len(b) && b[i+1] == '=' {
			j := skipHardWS(b, i+2)
			if j+1 < len(b) && b[j] == '-' && b[j+1] == '1' {
				return j + 2 - i
			}
			return 0
		}
		j := skipHardWS(b, i+1)
		if j < len(b) && b[j] == '0' {
			return j + 1 - i
		}
	case '=', '!':
		if i+1 < len(b) && b[i+1] == '=' {
			j := skipHardWS(b, i+2)
			if j+1 < len(b) && b[j] == '-' && b[j+1] == '1' {
				return j + 2 - i
			}
		}
	case '-':
		if i > 0 && isWordByte(b[i-1]) {
			return 0
		}
		j := skipHardWS(b, i+1)
		if j < len(b) && b[j] == '1' {
			k := skipHardWS(b, j+1)
			if isWordAt(b, k, "==") || isWordAt(b, k, "!=") {
				return k + 2 - i
			}
		}
	}
	return 0
}

func gDomain(b []byte) int {
	n := 0
	for i := 0; i < len(b); {
		if m := domainArm(b, i); m > 0 {
			n++
			i += m
			continue
		}
		i++
	}
	return n
}

func domainArm(b []byte, i int) int {
	if isIdentStart(b[i]) && !wordBefore(b, i) {
		w := b[i:identEnd(b, i)]
		if string(w) == "if" || string(w) == "fabs" {
			j := skipHardWS(b, i+len(w))
			if j < len(b) && b[j] == '(' {
				return j + 1 - i
			}
		}
	}
	if isWordAt(b, i, "clamp") && !wordBefore(b, i) && !wordAfter(b, i+5) {
		return 5
	}
	if b[i] != '>' && b[i] != '<' {
		return 0
	}
	if i+1 < len(b) && b[i+1] == '=' {
		return 2
	}
	j := skipHardWS(b, i+1)
	if j >= len(b) {
		return 0
	}
	switch {
	case b[j] == '0':
		return j + 1 - i
	case b[j] == '1' && b[i] == '<':
		return j + 1 - i
	case b[j] == '-' && b[i] == '>' && j+1 < len(b) && b[j+1] == '1':
		return j + 2 - i
	}
	return 0
}

func gUchar(b []byte) int {
	n := 0
	for i := 0; i+1 < len(b); i++ {
		if b[i] != '(' {
			continue
		}
		j := skipHardWS(b, i+1)
		if !isWordAt(b, j, "unsigned") {
			continue
		}
		j = skipHardWS(b, j+8)
		if !isWordAt(b, j, "char") {
			continue
		}
		j = skipHardWS(b, j+4)
		if j < len(b) && b[j] == ')' {
			n++
			i = j
		}
	}
	return n
}

func gErrnoZero(b []byte) int {
	n := 0
	for i := 0; i+5 <= len(b); i++ {
		if !isWordAt(b, i, "errno") || wordBefore(b, i) || wordAfter(b, i+5) {
			continue
		}
		j := skipHardWS(b, i+5)
		if j < len(b) && b[j] == '=' && (j+1 >= len(b) || b[j+1] != '=') {
			k := skipHardWS(b, j+1)
			if k < len(b) && b[k] == '0' {
				n++
			}
		}
	}
	return n
}

func gEndptr(b []byte) int {
	n := 0
	for i := 0; i < len(b); {
		if isWordAt(b, i, "endptr") {
			n++
			i += 6
			continue
		}
		if b[i] == '&' {
			j := skipHardWS(b, i+1)
			k := wEnd(b, j)
			if k > j {
				k = skipHardWS(b, k)
				if k < len(b) && b[k] == ')' {
					k = skipHardWS(b, k+1)
					if k < len(b) && b[k] == ';' {
						n++
						i = k + 1
						continue
					}
				}
			}
		}
		i++
	}
	return n
}

func gVaEnd(b []byte) int { return countCall(b, "va_end") }

func gMapFailed(b []byte) int { return countWord(b, "MAP_FAILED") }

func gMonotonic(b []byte) int {
	return countWord(b, "CLOCK_MONOTONIC") + countWord(b, "CLOCK_MONOTONIC_RAW") +
		countWord(b, "CLOCK_BOOTTIME")
}

func gStackszArray(b []byte) int {
	n := 0
	for i := range b {
		if !isWordByte(b[i]) {
			continue
		}
		j := skipHardWS(b, identEnd(b, i))
		if j >= len(b) || b[j] != '[' {
			continue
		}
		k := skipHT(b, j+1)
		for _, w := range [...]string{"SIGSTKSZ", "MINSIGSTKSZ", "PTHREAD_STACK_MIN"} {
			if isWordAt(b, k, w) {
				m := skipHT(b, k+len(w))
				if m < len(b) && b[m] == ']' {
					n++
				}
			}
		}
	}
	return n
}

func gPtrOvf(b []byte) int {
	n := 0
	for i := range b {

		if !isWordByte(b[i]) || (i > 0 && isWordByte(b[i-1])) {
			continue
		}
		e := identEnd(b, i)
		name := string(b[i:e])
		j := skipHardWS(b, e)
		if j >= len(b) || b[j] != '+' {
			continue
		}
		j = skipHardWS(b, j+1)
		k := j
		for k < len(b) && isWordByte(b[k]) {
			k++
		}
		if k == j {
			continue
		}
		k = skipHardWS(b, k)
		if k >= len(b) || b[k] != '<' {
			continue
		}
		k = skipHardWS(b, k+1)
		if isWordAt(b, k, name) && !wordAfter(b, k+len(name)) {
			n++
		}
	}
	return n
}

func gCallocTransposed(b []byte) int {
	n := 0
	for i := 0; i+6 <= len(b); i++ {
		if !isWordAt(b, i, "calloc") || wordBefore(b, i) || wordAfter(b, i+6) {
			continue
		}
		j := skipHardWS(b, i+6)
		if j >= len(b) || b[j] != '(' {
			continue
		}
		j = skipHT(b, j+1)
		if isWordAt(b, j, "sizeof") {
			n++
		}
	}
	return n
}

func gVaArgArray(b []byte) int {
	n := 0
	for i := 0; i+6 <= len(b); i++ {
		if !isWordAt(b, i, "va_arg") || wordBefore(b, i) || wordAfter(b, i+6) {
			continue
		}
		j := skipHardWS(b, i+6)
		if j >= len(b) || b[j] != '(' {
			continue
		}
		region := indexByteFrom(b, ';', j+1)
		if region < 0 {
			region = len(b)
		}
		if region > len(b) {
			region = len(b)
		}
		for q := j + 1; q < region; q++ {
			if q+1 < region && b[q] == '(' {
				break
			}
			if b[q] == '[' {
				r := indexByteFrom(b, ']', q+1)
				if r > 0 && r < region {
					n++
				}
				break
			}
		}
	}
	return n
}

func countWord(b []byte, w string) int {
	n := 0
	for i := 0; i+len(w) <= len(b); i++ {
		if !isWordAt(b, i, w) {
			continue
		}
		if wordBefore(b, i) || wordAfter(b, i+len(w)) {
			continue
		}
		n++
		i += len(w) - 1
	}
	return n
}

type evFlags struct {
	etReg, oneshotReg, writeReady, errFlag, rearm, dereg int
	eagain, eintr, uringRes, uringSqpoll                 int
	nonblockSet, eventDestroy, uringSqe, uringSeen       int
	uringUdata, uringLink, uringStreamOps, uringTeardown int
	kqTimer, kqReceipt, uringRing, uringBarrier          int
}

func countFlagWords(b []byte, words ...string) int {
	n := 0
	for _, w := range words {
		n += countWord(b, w)
	}
	return n
}

func scanEvFlags(b []byte) evFlags {
	var f evFlags
	f.etReg = countFlagWords(b, "EPOLLET", "EV_CLEAR")
	f.oneshotReg = countFlagWords(b, "EPOLLONESHOT", "EV_ONESHOT", "EV_DISPATCH")
	f.writeReady = countFlagWords(b, "EPOLLOUT", "EVFILT_WRITE")
	f.errFlag = countFlagWords(b, "EPOLLERR", "EPOLLHUP", "EV_EOF", "EV_ERROR")
	f.rearm = countFlagWords(b, "EPOLL_CTL_MOD", "EV_ENABLE")
	f.dereg = countFlagWords(b, "EPOLL_CTL_DEL", "EV_DELETE", "EV_DISABLE")
	f.eagain = countFlagWords(b, "EAGAIN", "EWOULDBLOCK")
	f.eintr = countWord(b, "EINTR")
	f.uringSqpoll = countWord(b, "IORING_SETUP_SQPOLL")
	f.nonblockSet = countFlagWords(b, "O_NONBLOCK", "SOCK_NONBLOCK", "FIONBIO", "F_SETFL")
	f.uringSqe = countCall(b, "io_uring_get_sqe")
	f.uringSeen = countCall(b, "io_uring_cqe_seen") + countCall(b, "io_uring_cq_advance")
	f.uringUdata = scanUringUdata(b)
	f.uringLink = countWord(b, "IOSQE_IO_LINK")
	f.uringStreamOps = scanStreamOps(b)
	f.uringTeardown = countCall(b, "io_uring_queue_exit")
	f.kqTimer = countWord(b, "EVFILT_TIMER")
	f.kqReceipt = countWord(b, "EV_RECEIPT")
	f.eventDestroy = countCall(b, "close", "io_uring_queue_exit") +
		scanUnregister(b)
	f.uringRing = scanUringRing(b)
	f.uringBarrier = scanUringBarrier(b)
	f.uringRes = scanUringRes(b)
	return f
}

func scanUringRes(b []byte) int {
	n := 0
	for i := 0; i+3 <= len(b); i++ {
		if isWordAt(b, i, "res") && !wordBefore(b, i) && !wordAfter(b, i+3) {
			j := skipHardWS(b, i+3)
			if j < len(b) && b[j] == '<' {
				k := skipHardWS(b, j+1)
				if k < len(b) && b[k] == '0' {
					n++
				}
			}
			if i >= 2 && b[i-1] == '-' && b[i-2] == '>' {
				n++
			}
			if i >= 1 && b[i-1] == '.' {
				n++
			}
		}
	}
	return n
}

func scanUringUdata(b []byte) int {
	n := countCall2(b, "io_uring_sqe_set_data")
	for i := 0; i+9 <= len(b); i++ {
		if !isWordAt(b, i, "user_data") || wordBefore(b, i) || wordAfter(b, i+9) {
			continue
		}
		j := skipHardWS(b, i+9)
		if j < len(b) && b[j] == '=' && (j+1 >= len(b) || b[j+1] != '=') {
			k := skipHardWS(b, j+1)
			if k < len(b) && b[k] != ';' {
				n++
			}
		}
	}
	return n
}

func countCall2(b []byte, prefix string) int {
	n := 0
	for i := 0; i+len(prefix) <= len(b); i++ {
		if !isWordAt(b, i, prefix) || wordBefore(b, i) {
			continue
		}
		e := identEnd(b, i+len(prefix))
		j := skipHardWS(b, e)
		if j < len(b) && b[j] == '(' {
			n++
			i = e - 1
		}
	}
	return n
}

func scanStreamOps(b []byte) int {
	n := 0
	for i := 0; i+15 <= len(b); i++ {
		if !isWordAt(b, i, "io_uring_prep_") || wordBefore(b, i) {
			continue
		}
		p := i + 15
		for _, suf := range [...]string{"sendmsg", "sendzc", "send", "recvmsg",
			"recv", "send_zc"} {
			if !isWordAt(b, p, suf) {
				continue
			}
			e := p + len(suf)
			if wordAfter(b, e) {
				continue
			}
			j := skipHardWS(b, e)
			if j < len(b) && b[j] == '(' {
				n++
				i = e - 1
			}
			break
		}
	}
	return n
}

func scanUnregister(b []byte) int { return countCall2(b, "io_uring_unregister") }

func scanUringRing(b []byte) int {
	inClass := func(c byte) bool {
		return isWordByte(c) || c == '.' || c == '>' || c == '-'
	}
	n := 0
	i := 0
	for i < len(b) {
		if !isWordAt(b, i, "ring") {
			i++
			continue
		}

		st := i
		for st > 0 && isWordByte(b[st-1]) {
			st--
		}
		if st > 0 && !isWordAt(b, st, "") && b[st-1] == 0 {
			i++
			continue
		}
		_ = st

		rs := i
		for rs > 0 && inClass(b[rs-1]) && !isHardWS(b[rs-1]) {
			rs--
		}
		re := i + 4
		for re < len(b) && inClass(b[re]) && !isHardWS(b[re]) {
			re++
		}
		matched := false
		g := min(re-i-4, 16)
		for ; g >= 0; g-- {
			q := i + 4 + g
			if q+4 > re && q+4 > len(b) {
				continue
			}
			if !isWordAt(b, q, "head") && !isWordAt(b, q, "tail") {
				continue
			}
			if !wordAfter(b, q+4) {
				continue
			}
			if q == 0 || !isWordByte(b[q-1]) {
				n++
				matched = true
				i = q + 4 - 1
				break
			}
		}
		if !matched {
			i++
		}
	}
	return n
}

func scanUringBarrier(b []byte) int {
	n := 0
	for i := 0; i < len(b); i++ {
		if !isIdentStart(b[i]) || wordBefore(b, i) {
			continue
		}
		e := identEnd(b, i)
		hit := ""
		switch w := string(b[i:e]); {
		case w == "io_uring_smp_load_acquire", w == "io_uring_smp_store_release",
			w == "smp_load_acquire", w == "smp_store_release",
			w == "atomic_load_explicit", w == "atomic_store_explicit",
			w == "atomic_load", w == "atomic_store",
			w == "__atomic_load_n", w == "__atomic_store_n",
			w == "__atomic_load", w == "__atomic_store":
			hit = w
		}
		if hit == "" {
			continue
		}
		j := skipHardWS(b, e)
		if j < len(b) && b[j] == '(' {
			n++
			i = e - 1
		}
	}
	return n
}

func scanFirstArgCall(b []byte, names []string, fn func(name string)) {
	for i := range b {
		if !isIdentStart(b[i]) || wordBefore(b, i) {
			continue
		}
		e := identEnd(b, i)
		w := string(b[i:e])
		hit := slices.Contains(names, w)
		if !hit {
			continue
		}
		j := skipHardWS(b, e)
		if j >= len(b) || b[j] != '(' {
			continue
		}
		j = skipHardWS(b, j+1)
		k := identEnd(b, j)
		if k > j {
			fn(string(b[j:k]))
		}
	}
}

func countCall(b []byte, names ...string) int {
	n := 0
	for i := 0; i < len(b); i++ {
		if !isIdentStart(b[i]) || wordBefore(b, i) {
			continue
		}
		e := identEnd(b, i)
		w := string(b[i:e])
		if slices.Contains(names, w) {
			p := skipHardWS(b, e)
			if p < len(b) && b[p] == '(' {
				n++
				i = e - 1
			}
		}
	}
	return n
}

func countWeakRandom(b []byte) int {
	return countCall(b, "rand", "random", "srand", "srandom", "drand48",
		"lrand48", "mrand48")
}

func countShiftVar(b []byte) int {
	n := 0
	for i := 0; i+1 < len(b); i++ {
		if b[i] != '<' && b[i] != '>' || b[i] != b[i+1] {
			continue
		}
		j := skipHardWS(b, i+2)
		if j < len(b) && (b[j] == '(' || isIdentStart(b[j])) {
			n++
			i = j
		}
	}
	return n
}

func countReallocSelf(b []byte) int {
	n := 0
	for i := range b {
		if !isIdentStart(b[i]) || wordBefore(b, i) {
			continue
		}
		e := identEnd(b, i)
		name := string(b[i:e])
		j := skipHardWS(b, e)
		if j >= len(b) || b[j] != '=' || (j+1 < len(b) && b[j+1] == '=') {
			continue
		}
		j = skipHardWS(b, j+1)

		run := identEnd(b, j)
		ok := false
		for k := run; k >= j; k-- {
			if !isWordAt(b, k, "realloc") || wordAfter(b, k+7) {
				continue
			}
			p := skipHardWS(b, k+7)
			if p >= len(b) || b[p] != '(' {
				continue
			}
			p = skipHardWS(b, p+1)
			if !isWordAt(b, p, name) || wordAfter(b, p+len(name)) {
				continue
			}
			q := skipHardWS(b, p+len(name))
			if q < len(b) && b[q] == ',' {
				ok = true
				break
			}
		}
		if ok {
			n++
		}
	}
	return n
}

func countVLA(b []byte) int {
	n := 0
	for i := 0; i < len(b); i++ {
		if !isIdentStart(b[i]) || wordBefore(b, i) {
			continue
		}
		e := identEnd(b, i)
		w := string(b[i:e])
		ok := false
		switch w {
		case "char", "int", "double", "float", "short", "long", "unsigned":
			ok = true
		default:
			if (strings.HasPrefix(w, "uint") || strings.HasPrefix(w, "int")) &&
				strings.HasSuffix(w, "_t") && len(w) > 5 {
				ok = true
				for _, c := range w[4 : len(w)-2] {
					if !isDigit(byte(c)) {
						ok = false
					}
				}
			}
		}
		if !ok {
			continue
		}
		j := skipHardWS(b, e)
		k := identEnd(b, j)
		if k == j {
			continue
		}
		j = skipHardWS(b, k)
		if j >= len(b) || b[j] != '[' {
			continue
		}
		j = skipHardWS(b, j+1)
		if j >= len(b) || !isIdentStart(b[j]) {
			continue
		}
		m := identEnd(b, j)
		m = skipHardWS(b, m)
		if m < len(b) && b[m] == ']' {
			n++
			i = m
		}
	}
	return n
}

func countAssertSide(b []byte) int {
	n := 0
	alt := func(i int) bool {
		if isWordAt(b, i, "strcpy") || isWordAt(b, i, "memcpy") ||
			isWordAt(b, i, "malloc") || isWordAt(b, i, "printf") {
			return true
		}
		if i+1 < len(b) && b[i] == '=' && b[i+1] != '=' {
			return true
		}
		return i+1 < len(b) && ((b[i] == '+' && b[i+1] == '+') ||
			(b[i] == '-' && b[i+1] == '-'))
	}
	for i := 0; i+6 <= len(b); i++ {
		if !isWordAt(b, i, "assert") || wordBefore(b, i) || wordAfter(b, i+6) {
			continue
		}
		p := skipHardWS(b, i+6)
		if p >= len(b) || b[p] != '(' {
			continue
		}
		region := indexByteFrom(b, ';', p+1)
		if region < 0 {
			region = len(b)
		}
		found := -1
		for q := p + 1; q < region; q++ {
			if alt(q) {
				found = q
				break
			}
		}
		if found < 0 {
			continue
		}
		end := -1
		for q := region - 1; q > found; q-- {
			if b[q] == ')' {
				end = q
				break
			}
		}
		if end < 0 {
			continue
		}
		n++
		i = end
	}
	return n
}

type freeHit struct {
	name    string
	afterPl int
}

func scanFrees(b []byte, fn func(freeHit)) {
	for i := 0; i < len(b); i++ {
		if !isIdentStart(b[i]) || wordBefore(b, i) {
			continue
		}
		e := identEnd(b, i)
		hit := false
		for j := e; j >= i; j-- {
			if isWordAt(b, j, "free") && !wordAfter(b, j+4) {
				p := skipHardWS(b, j+4)
				if p < len(b) && b[p] == '(' {
					p = skipHardWS(b, p+1)
					q := identEnd(b, p)
					if q > p && q < len(b) && b[q] == ')' {
						fn(freeHit{name: string(b[p:q]), afterPl: q + 1})
						hit = true
					}
				}
				break
			}
		}
		if hit {
			i = e - 1
		}
	}
}

func derefAfter(tail []byte, name string) bool {
	for i := range tail {
		if isWordAt(tail, i, name) {
			if i == 0 || (tail[i-1] != '.' && !isWordByte(tail[i-1])) {
				j := skipHardWS(tail, i+len(name))
				if j < len(tail) && (tail[j] == '[' ||
					(tail[j] == '-' && j+1 < len(tail) && tail[j+1] == '>')) {
					return true
				}
			}
		}
		if tail[i] == '*' {
			j := skipHardWS(tail, i+1)
			if isWordAt(tail, j, name) {
				k := j + len(name)
				if !wordAfter(tail, k) {
					mm := skipHardWS(tail, k)
					if mm >= len(tail) || tail[mm] != '=' ||
						(mm+1 < len(tail) && tail[mm+1] == '=') {
						return true
					}
				}
			}
		}
	}
	return false
}

func eachLineStart(b []byte, fn func(start, j int) int) {
	for i := 0; i < len(b); {
		if !atLineStart(b, i) {
			i++
			continue
		}
		switch r := fn(i, skipHT(b, i)); {
		case r < 0:
			return
		case r > 0:
			i = r
		default:
			i = skipLine(b, i)
		}
	}
}

func isWordAt(b []byte, i int, s string) bool {
	return i+len(s) <= len(b) && string(b[i:i+len(s)]) == s
}

func squeezeStr(s []byte) string {
	var sb strings.Builder
	sb.Grow(len(s))
	sp := false
	for i := 0; i < len(s); i++ {
		c := s[i]
		if c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\v' ||
			c == '\f' || c == 0x1c || c == 0x1d || c == 0x1e {
			sp = true
			continue
		}
		if sp {
			sb.WriteByte(' ')
			sp = false
		}
		sb.WriteByte(c)
	}
	if sp {
		sb.WriteByte(' ')
	}
	return sb.String()
}

func isHexDigit(c byte) bool {
	return isDigit(c) || (c >= 'a' && c <= 'f') || (c >= 'A' && c <= 'F')
}

func asciiLower(s string) string {
	b := []byte(s)
	for i := range b {
		if b[i] >= 'A' && b[i] <= 'Z' {
			b[i] += 32
		}
	}
	return string(b)
}

func containsFold(hay, pat string) bool {
	if len(pat) == 0 || len(pat) > len(hay) {
		return false
	}
	for i := 0; i+len(pat) <= len(hay); i++ {
		ok := true
		for j := 0; j < len(pat); j++ {
			c := hay[i+j]
			if c >= 'A' && c <= 'Z' {
				c += 32
			}
			if c != pat[j] {
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

var secretPats = func() []string {
	return []string{
		"api_key", "api-key", "apikey", "secret", "password", "passwd", "pwd",
		"token", "bearer", "access_key", "access-key", "private_key",
		"private-key", "client_secret", "client-secret", "auth_token",
		"auth-token", "jwt", "credential", "smtp_pass", "smtp-pass", "db_pass",
		"db-pass", "sk_live", "rk_live", "pk_live", "ghp_", "xoxb-", "akia",
	}
}()

var allocNameRe = allocNameMatcher{}

type allocNameMatcher struct{}

func (allocNameMatcher) MatchString(s string) bool {
	low := asciiLower(s)
	for _, suf := range [...]string{"alloc", "free", "strdup", "memdup"} {
		if len(low) > len(suf) && low[len(low)-len(suf):] == suf {
			return true
		}
	}
	return false
}

var brackets = strings.NewReplacer("[", "", "]", "")

type extractor struct {
	g *Graph

	fnByName                              map[string][]int32
	fnByNameF                             map[string][]int32
	fnByNameM                             map[string][]int32
	macroSID                              map[string]int32
	declared                              map[string]bool
	byBasename                            map[string]int32
	nSym                                  int32
	edgeN, macroN, externN, declN, unresN int32
	callsTotal                            int32

	pendSID  []int32
	pendFID  []int32
	pendMID  []int32
	pendName []string
	pendLine [][]int32
}

func newExtractor(g *Graph) *extractor {
	return &extractor{
		g:          g,
		fnByName:   map[string][]int32{},
		fnByNameF:  map[string][]int32{},
		fnByNameM:  map[string][]int32{},
		macroSID:   map[string]int32{},
		declared:   map[string]bool{},
		byBasename: map[string]int32{},
	}
}

type fld struct {
	ordinal int32
	ftype   string
	fname   string
	ptr     int32
	alen    int32
	isFnptr int32
	depth   int32
	inUnion int32
	line    int32
}

func jtrunc(s string, n int) string {
	c := 0
	for i := range s {
		if c == n {
			return s[:i]
		}
		c++
	}
	return s
}

func maxi(a, b int) int {
	if a > b {
		return a
	}
	return b
}

func squeeze(s, cut string) string {
	s = strings.Trim(s, cut)

	var sb strings.Builder
	sb.Grow(len(s))
	sp := false
	for i := 0; i < len(s); i++ {
		c := s[i]
		if c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\v' ||
			c == '\f' || c == 0x1c || c == 0x1d || c == 0x1e {
			sp = true
			continue
		}
		if sp {
			sb.WriteByte(' ')
			sp = false
		}
		sb.WriteByte(c)
	}
	if sp {
		sb.WriteByte(' ')
	}
	return sb.String()
}

func typeSizeOf(ctype string, ptrDepth, arrayLen int32) (int32, int32, int32) {
	var base, align, exact int32
	if ptrDepth > 0 {
		base, align, exact = ptrSize, ptrSize, 1
	} else {
		t := ctype
		for _, w := range [...]string{"const", "volatile", "struct", "union",
			"enum", "_Atomic", "register"} {
			t = replaceWord(t, w, " ")
		}
		t = trimSpace(squeeze(t, ""))
		if v, ok := typeSizeTable[t]; ok {
			base = v
			if a, ok := typeAlignTable[t]; ok {
				align = a
			} else if base < 8 {
				align = base
			} else {
				align = 8
			}
			exact = 1
		}
	}
	if arrayLen > 0 && base != 0 {
		return base * arrayLen, align, exact
	}
	if arrayLen < 0 {
		return 0, align, 0
	}
	return base, align, exact
}

func replaceWord(s, w, rep string) string {
	var sb strings.Builder
	i := 0
	for i < len(s) {
		if isWordAt([]byte(s), i, w) && (i == 0 || !isIdentPart(s[i-1])) &&
			(i+len(w) >= len(s) || !isIdentPart(s[i+len(w)])) {
			sb.WriteString(rep)
			i += len(w)
			continue
		}
		sb.WriteByte(s[i])
		i++
	}
	return sb.String()
}

func layoutStruct(flds []fld, isUnion bool) ([][5]int32, int32, int32, int32, int32) {
	off := int32(0)
	maxAlign := int32(1)
	allExact := int32(1)
	out := make([][5]int32, 0, len(flds))
	for _, f := range flds {
		if f.depth != 0 || f.inUnion != 0 {
			out = append(out, [5]int32{f.ordinal, -1, 0, 0, 0})
			continue
		}
		sz, al, ex := typeSizeOf(f.ftype, f.ptr, f.alen)
		if ex == 0 {
			allExact = 0
		}
		if al == 0 {
			al = 1
		}
		if al > maxAlign {
			maxAlign = al
		}
		var pad int32
		if !isUnion {
			pad = (int32(-off)) % al
			if pad < 0 {
				pad += al
			}
		}
		thisOff := int32(0)
		if !isUnion {
			thisOff = off + pad
		}
		out = append(out, [5]int32{f.ordinal, thisOff, sz, pad, ex})
		if isUnion {
			if sz > off {
				off = sz
			}
		} else {
			off += pad + sz
		}
	}
	tail := int32(0)
	if maxAlign > 0 {
		tail = (int32(-off)) % maxAlign
		if tail < 0 {
			tail += maxAlign
		}
	}
	return out, off + tail, tail, allExact, maxAlign
}

func lineText(b []byte, nl []int32, n int) []byte {
	start := int32(0)
	if n > 1 {
		if n-2 >= len(nl) {
			return nil
		}
		start = nl[n-2]
	}
	end := int32(len(b))
	if n-1 < len(nl) {
		end = nl[n-1]
	}
	if end < start {
		return nil
	}
	return b[start:end]
}

func leadingComment(b []byte, nl []int32, lineStart int) (bool, int) {
	n := 0
	i := lineStart - 2
	for i >= 0 {
		s := trimSpaceBytes(lineText(b, nl, i+1))
		if len(s) == 0 && n == 0 {
			i--
			continue
		}
		if bytes.HasPrefix(s, []byte("/*")) || bytes.HasPrefix(s, []byte("*")) ||
			bytes.HasPrefix(s, []byte("*/")) || bytes.HasPrefix(s, []byte("//")) {
			n++
			i--
			continue
		}
		break
	}
	return n > 0, n
}

func eventFamily(fn string) string {
	switch {
	case strings.HasPrefix(fn, "epoll_"):
		return "epoll"
	case strings.HasPrefix(fn, "io_uring_"):
		return "io_uring"
	}
	return "kqueue"
}

func matchBraceClose(b []byte, openIdx int) int {
	d := 0
	for i := openIdx; i < len(b); i++ {
		switch b[i] {
		case '{':
			d++
		case '}':
			d--
			if d == 0 {
				return i
			}
		}
	}
	return -1
}

func isCompoundOp(s string) bool {
	for _, c := range compoundOps {
		if c == s {
			return true
		}
	}
	return false
}

func nsIntersects(used, want map[string]bool) bool {
	for k := range want {
		if used[k] {
			return true
		}
	}
	return false
}

func countGuard(g string, b []byte) int {
	switch g {
	case "ret_neg":
		return gRetNeg(b)
	case "domain":
		return gDomain(b)
	case "uchar":
		return gUchar(b)
	case "errno_zero":
		return gErrnoZero(b)
	case "endptr":
		return gEndptr(b)
	case "va_end":
		return gVaEnd(b)
	case "map_failed":
		return gMapFailed(b)
	case "monotonic":
		return gMonotonic(b)
	case "stacksz_array":
		return gStackszArray(b)
	case "ptr_ovf_check":
		return gPtrOvf(b)
	case "calloc_sizeof_first":
		return gCallocTransposed(b)
	case "va_arg_array":
		return gVaArgArray(b)
	}
	return 0
}

func sizeofArg(s string) (string, bool) {
	i := strings.Index(s, "sizeof")
	if i < 0 {
		return "", false
	}
	j := i + 6
	for j < len(s) && (s[j] == ' ' || s[j] == '\t' || s[j] == '\n' || s[j] == '\r') {
		j++
	}
	if j >= len(s) || s[j] != '(' {
		return "", false
	}
	k := j + 1
	for k < len(s) && (s[k] == ' ' || s[k] == '\t' || s[k] == '\n' || s[k] == '\r') {
		k++
	}
	e := k
	for e < len(s) && s[e] != ')' && s[e] != '\n' {
		e++
	}
	if e >= len(s) || s[e] != ')' {
		return "", false
	}
	return strings.TrimRight(s[k:e], " \t\r\n"), true
}

var typedSizeofWords = []string{"struct", "union", "enum"}

func typedSizeof(operand string) bool {
	for _, w := range typedSizeofWords {
		if strings.HasPrefix(operand, w+" ") {
			r := skipHTStr(operand, len(w))
			return r > len(w) && identEndStr(operand, r) > r
		}
	}
	for _, t := range [...]string{"uint8_t", "uint16_t", "uint32_t", "uint64_t",
		"int8_t", "int16_t", "int32_t", "int64_t"} {
		if strings.HasPrefix(operand, t) {
			return true
		}
	}
	for _, t := range [...]string{"char", "int", "long", "short", "float",
		"double", "size_t"} {
		if strings.HasPrefix(operand, t) {
			return true
		}
	}
	if strings.HasPrefix(operand, "unsigned") {
		r := skipHTStr(operand, 8)
		return r > 8 && identEndStr(operand, r) > r
	}
	return false
}

func trailingIdent(operand string) (string, bool) {
	e := len(operand)
	for e > 0 && (operand[e-1] == ' ' || operand[e-1] == '\t' ||
		operand[e-1] == '\n' || operand[e-1] == '\r') {
		e--
	}
	st := e
	for st > 0 && isIdentPart(operand[st-1]) {
		st--
	}
	if st == e {
		return "", false
	}
	return operand[st:e], true
}

func firstIdent(s string) (string, bool) {
	for i := 0; i < len(s); i++ {
		if isIdentStart(s[i]) {
			e := i + 1
			for e < len(s) && isIdentPart(s[e]) {
				e++
			}
			return s[i:e], true
		}
	}
	return "", false
}

func lastPathTail(dst string) string {
	parts := strings.Split(dst, "")
	_ = parts
	segs := strings.FieldsFunc(dst, func(r rune) bool { return false })
	_ = segs
	last := ""
	start := 0
	for i := 0; i <= len(dst); i++ {
		if i == len(dst) || isPathTailSep(dst[i]) {
			last = dst[start:i]
			start = i + 1
		}
	}
	t := trimSpace(last)
	if t == "" {
		return dst
	}
	return t
}

func isPathTailSep(c byte) bool {
	return c == '.' || c == '>' || c == '[' || c == ']'
}

func scanAttrs(sig string, fn func(args string)) {
	i := 0
	for {
		j := strings.Index(sig[i:], "__attribute__")
		if j < 0 {
			return
		}
		j += i
		k := j + 13
		for k < len(sig) && (sig[k] == ' ' || sig[k] == '\t' || sig[k] == '\n' || sig[k] == '\r') {
			k++
		}
		if k+2 > len(sig) || sig[k] != '(' || sig[k+1] != '(' {
			i = j + 1
			continue
		}
		k += 2
		e := k
		for e < len(sig) && sig[e] != ')' {
			e++
		}
		if e+1 >= len(sig) || sig[e+1] != ')' {
			i = j + 1
			continue
		}
		fn(sig[k:e])
		i = e + 2
	}
}

var magicOKCache sync.Map

func okMagic(tok string) bool {
	if v, ok := magicOKCache.Load(tok); ok {
		return v.(bool)
	}
	t := strings.TrimRight(tok, "uUlL")
	n, ok := cgInt0(t)
	r := ok && magicOK[n]
	magicOKCache.Store(tok, r)
	return r
}

func cgInt0(s string) (int64, bool) {
	neg := false
	if s != "" && (s[0] == '+' || s[0] == '-') {
		neg = s[0] == '-'
		s = s[1:]
	}
	if s == "" {
		return 0, false
	}
	base := 10
	body := s
	if s[0] == '0' && len(s) > 1 {
		switch {
		case s[1] == 'x' || s[1] == 'X':
			base, body = 16, s[2:]
		case s[1] == 'o' || s[1] == 'O':
			base, body = 8, s[2:]
		case s[1] == 'b' || s[1] == 'B':
			base, body = 2, s[2:]
		default:

			allZero := true
			for i := 0; i < len(s); i++ {
				if s[i] != '0' {
					allZero = false
					break
				}
			}
			if !allZero {
				return 0, false
			}
			return 0, true
		}
	}
	if body == "" {
		return 0, false
	}
	var u uint64
	ub := uint64(base)
	for i := 0; i < len(body); i++ {
		c := body[i]
		var d uint64
		switch {
		case c >= '0' && c <= '9':
			d = uint64(c - '0')
		case c >= 'a' && c <= 'f':
			d = uint64(c-'a') + 10
		case c >= 'A' && c <= 'F':
			d = uint64(c-'A') + 10
		default:
			return 0, false
		}
		if d >= ub {
			return 0, false
		}
		u = u*ub + d
		if u > (1 << 62) {
			return 0, false
		}
	}
	n := int64(u)
	if neg {
		n = -n
	}
	return n, true
}

func countCommentLines(body []byte) int32 {
	var n int32
	for i := 0; i < len(body); {
		st := i
		for i < len(body) && !isSplitBound(body, i) {
			i++
		}
		t := trimSpaceBytes(body[st:i])
		if bytes.HasPrefix(t, []byte("/*")) || bytes.HasPrefix(t, []byte("//")) ||
			bytes.HasPrefix(t, []byte("*")) {
			n++
		}
		if i < len(body) {
			i = skipBoundary(body, i)
		}
	}
	return n
}

func (g *Graph) tSymbols() [][]fval {
	out := make([][]fval, 0, len(g.Symbols))
	for i := range g.Symbols {
		out = append(out, g.symbolRow(g.Symbols[i]))
	}
	return out
}

func (g *Graph) symbolRow(s *Symbol) []fval {
	r := g.rv(s)
	return []fval{
		fI32(s.ID),
		fI32(s.FileID),
		fI32(s.ModuleID),
		fNull(),
		fStr(s.Name()),
		fStr(s.QualName()),
		fStr(s.Kind()),
		fI32(s.LineStart),
		fI32(0),
		fI32(0),
		fOptStr(s.Signature(), s.HasSignature),
		fOptStr(s.ReturnType(), s.HasReturnType),
		fI32(s.NParams),
		fI32(0),
		fI32(0),
		fI32(0),
		fI32(0),
		fI32(s.IsPublic),
		fI32(s.IsStatic),
		fI32(0),
		fI32(0),
		fI32(0),
		fI32(0),
		fI32(0),
		fI32(s.IsTest),
		fI32(0),
		fI32(s.IsEntrypoint),
		fI32(s.IsGenerated),
		fI32(s.Sloc),
		fI32(s.NCommentLines),
		fI32(s.HasDoc),
		fI32(s.Cyclomatic),
		fI32(s.Cognitive),
		fI32(s.MaxNesting),
		fI32(s.NTokens),
		fI32(s.NOperators),
		fI32(s.NOperands),
		fI32(s.NDistinctOperators),
		fI32(s.NDistinctOperands),
		fI32(s.NLoops),
		fI32(s.NBranches),
		fI32(s.NReturns),
		fI32(s.NSwitch),
		fI32(s.NCases),
		fI32(0),
		fI32(0),
		fI32(0),
		fI32(0),
		fI32(0),
		fI32(0),
		fI32(s.NLabels),
		fI32(s.NGotos),
		fI32(s.MaxLoopDepth),
		fI32(s.CallInLoop),
		fI32(s.AllocInLoop),
		fI32(s.IOInLoop),
		fI32(0),
		fI32(s.LockInLoop),
		fI32(0),
		fI32(0),
		fI32(0),
		fI32(s.BranchInLoop),
		fI32(s.NLocals),
		fI32(s.NCmp),
		fI32(s.NShift),
		fI32(s.NArith),
		fI32(0),
		fI32(s.NFloatLit),
		fI32(s.NMagic),
		fI32(s.NNullCheck),
		fI32(0),
		fI32(0),
		fI32(s.NCalls),
		fI32(s.NDynamicCalls),
		fI32(s.NUnresolvedCalls),
		fI32(s.FanIn),
		fI32(s.FanOut),
		fI32(s.NCallsites),
		fI32(s.IsRecursive),
		fI32(s.RiskScore),
		fI32(s.NMemory),
		fI32(s.NAlloc),
		fI32(s.NIO),
		fI32(s.NStdio),
		fI32(s.NExec),
		fI32(s.NLibm),
		fI32(s.NInteger),
		fI32(s.NConcurrency),
		fI32(s.NReentrancy),
		fI32(s.IsInline),
		fI32(s.IsVariadic),
		fI32(s.NPtrLocals),
		fI32(s.NDeref),
		fI32(s.NCast),
		fI32(s.NSizeof),
		fI32(s.NIntrinsic),
		fI32(s.NAtomic),
		fI32(s.NRestrict),
		fI32(s.NLikely),
		fI32(s.NBuiltin),
		fI32(r.SwitchInLoop),
		fI32(r.LibmInLoop),
		fI32(r.DivInLoop),
		fI32(r.StrlenInLoop),
		fI32(r.RetNull),
		fI32(r.RetNeg),
		fI32(r.RetZero),
		fI32(r.RetVal),
		fI32(r.RetVoid),
		fI32(r.NFnptrCalls),
		fI32(r.NMacroCalls),
		fI32(r.NExternalCalls),
		fI32(r.NFree),
		fI32(r.NConstCast),
		fI32(r.NToctou),
		fI32(r.NLockAcquire),
		fI32(r.NLockRelease),
		fI32(r.NNarrowCast),
		fI32(r.NSignCmp),
		fI32(r.NVariadicFmt),
		fI32(r.NMemcpy),
		fI32(r.NAllocsite),
		fI32(r.NGlobalWrite),
		fI32(r.NErrno),
		fI32(r.NWeakRandom),
		fI32(r.NShiftVar),
		fI32(r.NReallocSelf),
		fI32(r.NVla),
		fI32(r.NGetenv),
		fI32(r.NAssertSide),
		fI32(r.NFreeThenUse),
		fI32(r.NEpoll),
		fI32(r.NUring),
		fI32(r.NKqueue),
		fI32(r.NEventWait),
		fI32(r.NEtReg),
		fI32(r.NOneshotReg),
		fI32(r.NWriteReady),
		fI32(r.NErrFlag),
		fI32(r.NRearm),
		fI32(r.NDereg),
		fI32(r.NEagain),
		fI32(r.NEintr),
		fI32(r.NUringRes),
		fI32(r.NUringRing),
		fI32(r.NUringBarrier),
		fI32(r.NUringSqpoll),
		fI32(r.NNonblockSet),
		fI32(r.NEventCreate),
		fI32(r.NEventDestroy),
		fI32(r.NUringSqe),
		fI32(r.NUringSeen),
		fI32(r.NUringUdata),
		fI32(r.NUringLink),
		fI32(r.NUringStreamOps),
		fI32(r.NUringTeardown),
		fI32(r.NEvTimeoutIndefinite),
		fI32(r.NEvTimeoutZero),
		fI32(r.NEvBatchOne),
		fI32(r.NKqTimer),
		fI32(r.NKqTimerZeroData),
		fI32(r.NKqReceipt),
		fI32(r.NRetNegCheck),
		fI32(r.NDomainGuard),
		fI32(r.NUcharCast),
		fI32(r.NErrnoZero),
		fI32(r.NEndptr),
		fI32(r.NVaEnd),
		fI32(r.NMapFailed),
		fI32(r.NMonotonicClock),
		fI32(r.NStackszArray),
		fI32(r.NPtrOvfCheck),
		fI32(r.NCallocTransposed),
		fI32(r.NVaArgArr),
	}
}

func (g *Graph) tFTS() {

	rows := make([]string, len(g.Symbols))
	for i := range rows {
		rows[i] = `R \N \N \N`
	}
	sort.Strings(rows)
	fmt.Fprintf(g.dumpW, "T sym_fts 3 %d\n", len(rows))
	for _, r := range rows {
		g.dumpW.WriteString(r)
		g.dumpW.WriteByte('\n')
	}
	g.dumpW.WriteString("E sym_fts\n")
	g.dumpW.WriteString("T sym_fts_config 2 1\n")
	g.dumpW.WriteString(`R s:version i:4` + "\n")
	g.dumpW.WriteString("E sym_fts_config\n")

	lines := make([]string, 0, len(g.Symbols))
	for i := range g.Symbols {
		s := g.Symbols[i]
		blob := append(svarint(tokenCount(s.Name())), svarint(tokenCount(s.QualName()))...)
		blob = append(blob, svarint(tokenCount(s.Signature()))...)
		lines = append(lines, "R i:"+itoa(int(s.ID))+" s:"+escapeText(reprBytes(blob)))
	}
	sort.Strings(lines)
	fmt.Fprintf(g.dumpW, "T sym_fts_docsize 2 %d\n", len(lines))
	for _, l := range lines {
		g.dumpW.WriteString(l)
		g.dumpW.WriteByte('\n')
	}
	g.dumpW.WriteString("E sym_fts_docsize\n")
}

func tokenCount(s string) int {
	n := 0
	in := false
	for _, r := range s {
		if unicode.IsLetter(r) || unicode.IsDigit(r) {
			_ = foldRune(r)
			in = true
			continue
		}
		if in {
			n++
			in = false
		}
	}
	if in {
		n++
	}
	return n
}

func foldRune(r rune) rune {
	if r < 128 {
		if r >= 'A' && r <= 'Z' {
			return r + 32
		}
		return r
	}
	if d, ok := diacritics[r]; ok {
		return d
	}
	if r >= 0x0300 && r <= 0x036F {
		return 0
	}
	l := unicode.ToLower(r)
	return l
}

var diacritics = map[rune]rune{
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

func svarint(v int) []byte {
	var tmp [9]byte
	n := 0
	u := uint64(v)
	for {
		tmp[n] = byte(u & 0x7f)
		n++
		u >>= 7
		if u == 0 {
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

func reprBytes(b []byte) string {
	quote := byte('\'')
	hasSingle, hasDouble := false, false
	for _, c := range b {
		if c == '\'' {
			hasSingle = true
		}
		if c == '"' {
			hasDouble = true
		}
	}
	if hasSingle && !hasDouble {
		quote = '"'
	}
	var sb strings.Builder
	sb.WriteByte('b')
	sb.WriteByte(quote)
	for i, c := range b {
		if c >= 0x20 && c < 0x7F {
			if c == quote && i+1 < len(b) && b[i+1] == quote {
				sb.WriteByte('\\')
				sb.WriteByte(quote)
				continue
			}
			sb.WriteByte(c)
			continue
		}
		switch c {
		case '\t':
			sb.WriteString(`\t`)
		case '\n':
			sb.WriteString(`\n`)
		case '\r':
			sb.WriteString(`\r`)
		case '\\':
			sb.WriteString(`\\`)
		default:
			fmt.Fprintf(&sb, `\x%02x`, c)
		}
	}
	sb.WriteByte(quote)
	return sb.String()
}

var _ = bufio.NewWriter

func build(g *Graph, root string, opts runOpts, quiet bool) int {

	prevGC := debug.SetGCPercent(200)
	defer debug.SetGCPercent(prevGC)
	abs, _ := filepath.Abs(root)
	g.fileByRel = map[string]int32{}
	g.byName = map[string][]int32{}
	g.Meta = map[string]string{}

	if !quiet {
		fmt.Println("  parser: C23 lexer + hide-set preprocessor + recursive-descent parser (stdlib only)")
	}
	tDisc := time.Now()
	parseIDs := discover(abs, g, opts)
	for i := range g.Files {
		g.fileByRel[g.Files[i].Path()] = g.Files[i].ID
	}

	g.FilesParsed = int32(len(parseIDs))
	if !quiet {
		fmt.Printf("  %d c files discovered in %.1fs\n", len(parseIDs),
			time.Since(tDisc).Seconds())
	}

	ppSrcMu.Lock()
	ppSrcCache = map[string][]byte{}
	for i := range g.Files {
		if data := source[i]; len(data) > 0 {
			ppSrcCache[filepath.Join(abs, filepath.FromSlash(g.Files[i].Path()))] = data
		}
	}
	ppSrcMu.Unlock()
	for i := range source {
		source[i] = nil
	}

	e := newExtractor(g)
	t1 := time.Now()
	step := max(len(parseIDs)/20, 1)
	outs := e.runC23(abs, g, parseIDs, quiet, step, opts.keepAST)
	e.reserve(g, outs)
	for i, o := range outs {
		if o == nil {
			continue
		}
		e.merge(g, o)
		outs[i] = nil
		if !quiet && (i+1)%step == 0 {
			fmt.Printf("  ... %d/%d files\n", i+1, len(parseIDs))
		}
	}
	if !quiet {
		fmt.Printf("  %d symbols parsed in %.1fs\n", len(g.Symbols),
			time.Since(t1).Seconds())
	}

	t2 := time.Now()
	e.resolveCalls()
	if !quiet {
		fmt.Printf("  call graph built in %.1fs\n", time.Since(t2).Seconds())
	}

	collapseHazards(g)

	nres := e.resolveImportTargets(abs)
	nimp := 0
	for i := range g.Imports {
		if g.Imports[i].HasTargetID {
			nimp++
		}
	}
	g.Meta["imports_resolved"] = itoa(nimp) + " of " + itoa(len(g.Imports)) +
		" import rows point at a file in this tree (" + itoa(nres) +
		" resolved by path here)"
	parseManifests(abs, g)

	t3 := time.Now()
	e.materialize()
	if !quiet {
		fmt.Printf("  aggregates materialized in %.1fs\n", time.Since(t3).Seconds())
	}
	t4 := time.Now()
	e.postBuild()
	if !quiet {
		fmt.Printf("  indexed in %.1fs\n", time.Since(t4).Seconds())
	}

	g.Meta["schema_version"] = "2"
	g.Meta["lang"] = "c"
	g.Meta["target"] = target
	g.Meta["root"] = abs
	g.Meta["parse_mode"] = "c23-ast"
	g.Meta["parser"] = "C23 lexer + hide-set preprocessor + recursive-descent parser (stdlib only)"
	g.Meta["files_parsed"] = itoa(len(parseIDs))
	g.Meta["files_failed"] = itoa(int(g.FilesFailed))
	g.Meta["grammar_note"] = grammarNote
	g.Meta["layout_model"] = "LP64: pointer 8/8, long 8, int 4; sizes reported only where exact=1"
	g.Meta["files_skipped"] = "big=" + itoa(int(g.FilesSkippedBig)) +
		" special=" + itoa(int(g.FilesSkippedSpecial)) +
		" escaping_symlink=" + itoa(int(g.FilesSkippedEscape)) +
		" denied=" + itoa(int(g.FilesSkippedDenied)) +
		" walk_errors=" + itoa(int(g.WalkErrors))
	buildIndex(g)
	return len(parseIDs)
}

func collapseHazards(g *Graph) {
	idx := make(map[[2]any]int, len(g.Hazards))
	out := g.Hazards[:0]
	for _, h := range g.Hazards {
		k := [2]any{h.SymbolID, h.Pattern()}
		if j, ok := idx[k]; ok {
			out[j].N += h.N
			continue
		}
		idx[k] = len(out)
		out = append(out, h)
	}
	g.Hazards = out
}

const grammarNote = "no compiler frontend and no third-party package: C23 " +
	"(ISO/IEC 9899:2024) is analysed by a real preprocessor (hide-set macro " +
	"expansion, conditionals, include graph) and a recursive-descent parser " +
	"producing a pointer-free flat AST. Race-surface and guard counters keep " +
	"their text heuristics, fed exact AST body spans."

type edgeKey struct{ c, d int32 }

func (e *extractor) resolveCalls() {
	g := e.g
	edges := map[edgeKey]*Edge{}
	order := []edgeKey{}
	callSites := map[[3]int32]bool{}
	csOrder := [][3]int32{}
	unres := map[[2]any]*Unresolved{}
	unresOrder := [][2]any{}
	macroUses := map[int32]int32{}
	ext := map[int32]int32{}
	decl := map[int32]int32{}
	mac := map[int32]int32{}
	var allocHz []hazardW

	for i, name := range e.pendName {
		caller := e.pendSID[i]
		fid := e.pendFID[i]
		mid := e.pendMID[i]
		lines := e.pendLine[i]
		cnt := int32(len(lines))
		line := lines[0]
		if cands, ok := e.fnByName[name]; ok {
			ti := 0
			if len(cands) > 1 {
				for x, sfid := range e.fnByNameF[name] {
					if sfid == fid {
						ti = x
						break
					}
				}
			}
			target := cands[ti]
			tf := e.fnByNameF[name][ti]
			tm := e.fnByNameM[name][ti]
			for _, site := range lines {
				k := edgeKey{caller, target}
				ed, ok := edges[k]
				if !ok {
					ed = &Edge{CallerID: caller, CalleeID: target, NCalls: 1,
						SameFile: b2i(tf == fid), SameModule: b2i(tm == mid),
						IsSelf: b2i(caller == target)}
					edges[k] = ed
					order = append(order, k)
				} else {
					ed.NCalls++
				}
				ck := [3]int32{caller, target, site}
				if !callSites[ck] {
					callSites[ck] = true
					csOrder = append(csOrder, ck)
				}
			}
			e.edgeN += cnt
			if allocNameRe.MatchString(name) {
				allocHz = append(allocHz, hazardW{SymbolID: caller,
					Pattern: jtrunc(name, 80), Category: "alloc", N: cnt,
					FirstLine: line})
			}
			continue
		}
		if msid, ok := e.macroSID[name]; ok {
			mac[caller] += cnt
			macroUses[msid] += cnt
			e.macroN += cnt
			continue
		}
		if e.isExternal(name) {
			ext[caller] += cnt
			e.externN += cnt
			continue
		}
		if e.declared[name] {
			ext[caller] += cnt
			decl[caller] += cnt
			e.externN += cnt
			e.declN += cnt
			continue
		}
		nm := jtrunc(name, 160)
		k := [2]any{caller, nm}
		u, ok := unres[k]
		if !ok {
			u = &Unresolved{}
			cgZeroRow(unsafe.Pointer(u), unsafe.Sizeof(*u))
			u.CallerID = caller
			u.name = cgPut(nm)
			u.N = cnt
			u.FirstLine = line
			unres[k] = u
			unresOrder = append(unresOrder, k)
		} else {
			u.N += cnt
		}
		e.unresN += cnt
	}

	for _, h := range allocHz {
		g.Hazards = append(g.Hazards, Hazard{})
		hz := &g.Hazards[len(g.Hazards)-1]
		cgZeroRow(unsafe.Pointer(hz), unsafe.Sizeof(*hz))
		hz.SymbolID = h.SymbolID
		hz.pattern = cgPut(h.Pattern)
		hz.category = cgPut(h.Category)
		hz.N = h.N
		hz.FirstLine = h.FirstLine
	}
	for i := range g.Edges {
		_ = i
	}
	for _, k := range order {
		g.Edges = append(g.Edges, *edges[k])
	}
	for _, k := range csOrder {
		g.Callsites = append(g.Callsites, Callsite{k[0], k[1], k[2]})
	}
	for _, k := range unresOrder {
		g.Unres = append(g.Unres, *unres[k])
	}
	for _, sid := range sortedIDs(ext) {
		g.rw(int(sid - 1)).NExternalCalls += ext[sid]
	}
	for _, sid := range sortedIDs(mac) {
		g.rw(int(sid - 1)).NMacroCalls += mac[sid]
	}

	for i := range g.Macros {
		if n, ok := macroUses[g.Macros[i].SymbolID]; ok {
			g.Macros[i].NUses = n
		}
	}
	total := e.edgeN + e.macroN + e.externN + e.unresN
	pct := int32(0)
	if total > 0 {
		pct = 100 * (total - e.unresN) / total
	}
	den := max(total, 1)
	g.Meta["calls_resolved"] = itoa(int(e.edgeN)) + " in-tree / " +
		itoa(int(e.macroN)) + " via macro / " + itoa(int(e.externN)) +
		" external (" + itoa(int(e.declN)) +
		" of them declared-here-defined-elsewhere) / " +
		itoa(int(e.unresN)) + " unresolved -- " + itoa(int(pct)) + "% of " +
		itoa(int(den)) + " call sites accounted for"
}

func (e *extractor) isExternal(name string) bool {
	if libcKnown[name] {
		return true
	}
	for _, p := range builtinPrefixes {
		if strings.HasPrefix(name, p) {
			return true
		}
	}
	return intrinsicName(name)
}

func (e *extractor) resolveImportTargets(root string) int {
	g := e.g
	byPath := make(map[string]int32, len(g.Files)*2)
	for i := range g.Files {
		p := filepath.ToSlash(g.Files[i].Path())
		if _, ok := byPath[p]; !ok {
			byPath[p] = g.Files[i].ID
		}
		stem := p
		if j := strings.LastIndexByte(p, '.'); j > 0 {
			stem = p[:j]
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
		if v, ok := byPath[cand]; ok {
			return v
		}
		for _, idx := range importIndexes {
			if v, ok := byPath[cand+"/"+idx]; ok {
				return v
			}
		}
		return 0
	}
	n := 0
	for i := range g.Imports {
		im := &g.Imports[i]
		if im.HasTargetID {
			continue
		}
		target := im.Target()
		if target == "" {
			continue
		}
		here := pathDir(g.Files[im.FileID-1].Path())
		var hit int32
		t := target
		if strings.HasPrefix(t, ".") {
			nUp := len(t) - len(strings.TrimLeft(t, "."))
			rest := t
			if !strings.Contains(t, "/") {
				rest = strings.ReplaceAll(t[nUp:], ".", "/")
			} else {
				rest = strings.TrimLeft(t, "./")
			}
			base := here
			for k := 0; k < maxi(0, nUp-1); k++ {
				base = pathDir(base)
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
			im.TargetID, im.HasTargetID = hit, true
			n++
		}
	}
	return n
}

var importIndexes = []string{"__init__.py", "index.ts", "index.tsx",
	"index.js", "index.mjs", "mod.rs", "lib.rs"}

func parseManifests(root string, g *Graph) {
	bases := []string{root}
	ents, _ := os.ReadDir(root)
	names := make([]string, 0, len(ents))
	for _, e := range ents {
		names = append(names, e.Name())
	}
	sort.Strings(names)
	if len(names) > 64 {
		names = names[:64]
	}
	for _, d := range names {
		p := filepath.Join(root, d)
		if st, err := os.Stat(p); err == nil && st.IsDir() {
			bases = append(bases, p)
		}
	}
	seen := 0
	for _, base := range bases {
		for _, nm := range []string{"Makefile", "makefile", "GNUmakefile"} {
			p := filepath.Join(base, nm)
			st, err := os.Stat(p)
			if err != nil || !st.Mode().IsRegular() {
				continue
			}
			seen++
			rel, _ := filepath.Rel(root, p)
			rel = filepath.ToSlash(rel)
			data, err := os.ReadFile(p)
			if err != nil {
				break
			}
			cont, start := "", 0
			for lnNo0, ln := range splitLines(string(data)) {
				lnNo := lnNo0 + 1
				ln = strings.TrimRight(ln, "\r")
				if cont != "" {
					ln = cont + " " + strings.TrimLeft(ln, " \t")
					cont = ""
				}
				if strings.HasSuffix(ln, "\\") {
					cont = ln[:len(ln)-1]
					if start == 0 {
						start = lnNo
					}
					continue
				}
				if r := matchMakeRule(ln); r != "" {
					pre := ln[strings.Index(ln, ":")+1:]
					g.MkRules = append(g.MkRules, MakefileRule{})
					mr := &g.MkRules[len(g.MkRules)-1]
					cgZeroRow(unsafe.Pointer(mr), unsafe.Sizeof(*mr))
					mr.path = cgPut(rel)
					mr.rule = cgPut(r)
					mr.Line = int32(cmpOr(start, lnNo))
					mr.NObjs = int32(countMakeObj(pre))
					mr.NSrcs = int32(countMakeSrc(pre))
					mr.UsesAr = b2i(strings.Contains(pre, ".a"))
					start = 0
					continue
				}
				if v, val := matchMakeVar(ln); v != "" {
					objs := countMakeObj(val)
					srcs := countMakeSrc(val)
					if objs > 0 || srcs > 0 {
						g.MkRules = append(g.MkRules, MakefileRule{})
						mr := &g.MkRules[len(g.MkRules)-1]
						cgZeroRow(unsafe.Pointer(mr), unsafe.Sizeof(*mr))
						mr.path = cgPut(rel)
						mr.rule = cgPut(v + " =")
						mr.Line = int32(cmpOr(start, lnNo))
						mr.NObjs = int32(objs)
						mr.NSrcs = int32(srcs)
						mr.UsesAr = b2i(strings.Contains(val, ".a"))
					}
				}
				start = 0
			}
			break
		}
	}
	g.MakefilesRead = int32(seen)
	g.Meta["makefiles_read"] = itoa(seen)
}

func cmpOr(a, b int) int {
	if a != 0 {
		return a
	}
	return b
}

func makeClassish(c byte) bool {
	return c == '_' || c == '.' || c == '/' || c == '$' || c == '(' || c == ')' ||
		c == '{' || c == '}' || c == '-' || isWordByte(c)
}

func matchMakeRule(ln string) string {
	bb := []byte(ln)
	k := 0
	for k < len(bb) && isMakeNameByte(bb[k]) {
		k++
	}
	if k == 0 {
		return ""
	}
	m := k
	for m < len(bb) && (bb[m] == ' ' || bb[m] == '\t') {
		m++
	}
	if m >= len(bb) || bb[m] != ':' {
		return ""
	}
	if m+1 >= len(bb) || bb[m+1] == '=' {
		return ""
	}
	return ln[:k]
}

func isMakeNameByte(c byte) bool {
	return (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') ||
		(c >= '0' && c <= '9') || c == '_' || c == '.' || c == '/' ||
		c == '$' || c == '(' || c == ')' || c == '%' || c == '-'
}

func matchMakeVar(ln string) (string, string) {
	if ln == "" || !isIdentStart(ln[0]) {
		return "", ""
	}
	k := identEndStr(ln, 0)
	m := k
	for m < len(ln) && (ln[m] == ' ' || ln[m] == '\t') {
		m++
	}
	if m < len(ln) && (ln[m] == ':' || ln[m] == '+' || ln[m] == '?') {
		m++
	}
	if m >= len(ln) || ln[m] != '=' {
		return "", ""
	}
	m++
	for m < len(ln) && (ln[m] == ' ' || ln[m] == '\t') {
		m++
	}
	return ln[:k], ln[m:]
}

func countMakeObj(s string) int { return countMakeExt(s, 'o') }

func countMakeSrc(s string) int {
	n, _ := countMakeExt2(s, 'c')
	return n
}

func makeObjClass(c byte) bool {
	return isWordByte(c) || c == '/' || c == '$' || c == '(' || c == ')' ||
		c == '{' || c == '}' || c == '.' || c == '-'
}

func makeSrcClass(c byte) bool {
	return isWordByte(c) || c == '/' || c == '.' || c == '-'
}

func countMakeExt(s string, ext byte) int {
	n, _ := countMakeExt2(s, ext)
	return n
}

func countMakeExt2(s string, ext byte) (int, bool) {
	bb := []byte(s)
	inClass := makeObjClass
	if ext == 'c' {
		inClass = makeSrcClass
	}
	n := 0
	i := 0
	for i < len(bb) {
		if !inClass(bb[i]) {
			i++
			continue
		}
		greedy := i
		for greedy < len(bb) && inClass(bb[greedy]) {
			greedy++
		}
		found := -1
		for j := greedy - 1; j > i; j-- {
			if bb[j] != '.' || j+1 >= len(bb) || bb[j+1] != ext {
				continue
			}
			if j+2 < len(bb) && isWordByte(bb[j+2]) {
				continue
			}
			found = j
			break
		}
		if found < 0 {
			i = greedy
			continue
		}
		n++
		i = found + 2
	}
	return n, true
}

func (e *extractor) materialize() {
	g := e.g

	byCat := map[int32]map[string]int32{}
	for _, h := range g.Hazards {
		m := byCat[h.SymbolID]
		if m == nil {
			m = map[string]int32{}
			byCat[h.SymbolID] = m
		}
		m[h.Category()] += h.N
	}

	fanIn := map[int32]int32{}
	fanOut := map[int32]int32{}
	nsites := map[int32]int32{}
	selfCall := map[int32]bool{}
	for _, ed := range g.Edges {
		if ed.IsSelf == 0 {
			fanOut[ed.CallerID]++
			fanIn[ed.CalleeID]++
		} else {
			selfCall[ed.CallerID] = true
		}
	}
	for _, c := range g.Callsites {
		nsites[c.CalleeID]++
	}
	unresN := map[int32]int32{}
	for _, u := range g.Unres {
		unresN[u.CallerID] += u.N
	}
	hazN := map[int32]int32{}
	for _, h := range g.Hazards {
		hazN[h.SymbolID] += h.N
	}
	uniq := map[int32]int32{}
	for _, ed := range g.Edges {
		uniq[ed.CallerID]++
	}

	freeN := map[int32]int32{}
	allocN := map[int32]int32{}
	for _, h := range g.Hazards {
		if h.Category() != "alloc" {
			continue
		}
		if h.Pattern() == "free" || strings.HasSuffix(asciiLower(h.Pattern()), "free") {
			freeN[h.SymbolID] += h.N
		} else {
			allocN[h.SymbolID] += h.N
		}
	}
	for i := range g.Symbols {
		s := g.Symbols[i]
		s.FanOut = fanOut[s.ID]
		s.FanIn = fanIn[s.ID]
		s.NCallsites = nsites[s.ID]
		if selfCall[s.ID] {
			s.IsRecursive = 1
		}
		s.NUnresolvedCalls = unresN[s.ID]
		if m := byCat[s.ID]; m != nil {
			s.NMemory = m["memory"]
			s.NAlloc = m["alloc"]
			s.NIO = m["io"]
			s.NStdio = m["stdio"]
			s.NExec = m["exec"]
			s.NLibm = m["libm"]
			s.NInteger = m["integer"]
			s.NConcurrency = m["concurrency"]
			s.NReentrancy = m["reentrancy"]
		}
		g.rw(i).NFree = freeN[s.ID]
		s.NAlloc = allocN[s.ID]
	}

	for i := range g.Symbols {
		s := g.Symbols[i]
		r := s.Cyclomatic*2 + s.Cognitive + s.MaxNesting*5 +
			s.NMemory*10 + s.NIO*8 + s.NExec*15 + s.NInteger*1 +
			s.NAlloc*2 + s.NConcurrency*3
		if s.IsRecursive == 1 {
			r += 25
		}
		if s.NAlloc > 0 && g.rv(s).NFree == 0 {
			r += 10
		}
		s.RiskScore = r
	}

	type fileAgg struct {
		n, fn, ty, cyclo, maxc, risk int32
	}
	fagg := map[int32]*fileAgg{}
	for i := range g.Symbols {
		s := g.Symbols[i]
		a := fagg[s.FileID]
		if a == nil {
			a = &fileAgg{}
			fagg[s.FileID] = a
		}
		a.n++
		switch s.Kind() {
		case "function", "method", "constructor", "closure":
			a.fn++
		case "class", "struct", "interface", "trait", "enum", "union",
			"record", "protocol", "type", "impl":
			a.ty++
		}
		a.cyclo += s.Cyclomatic
		if s.Cyclomatic > a.maxc {
			a.maxc = s.Cyclomatic
		}
		a.risk += s.RiskScore
	}
	impN := map[int32]int32{}
	for _, im := range g.Imports {
		impN[im.FileID]++
	}
	for i := range g.Files {
		f := &g.Files[i]
		if a := fagg[f.ID]; a != nil {
			f.NSymbols, f.NFunctions, f.NTypes = a.n, a.fn, a.ty
			f.TotalCyclo, f.MaxCyclo, f.TotalRisk = a.cyclo, a.maxc, a.risk
		}
		f.NImports = impN[f.ID]
	}

	type modAgg struct{ n, p, files, sloc int32 }
	magg := map[int32]*modAgg{}
	for i := range g.Symbols {
		s := g.Symbols[i]
		if s.ModuleID == 0 {
			continue
		}
		m := magg[s.ModuleID]
		if m == nil {
			m = &modAgg{}
			magg[s.ModuleID] = m
		}
		m.n++
		m.p += s.IsPublic
	}
	for i := range g.Files {
		f := &g.Files[i]
		if f.ModuleID == 0 {
			continue
		}
		m := magg[f.ModuleID]
		if m == nil {
			m = &modAgg{}
			magg[f.ModuleID] = m
		}
		m.files++
		m.sloc += f.Sloc
	}

	mo, mi := map[int32]map[int32]bool{}, map[int32]map[int32]bool{}
	for _, ed := range g.Edges {
		if ed.CallerID < 1 || ed.CalleeID < 1 {
			continue
		}
		a := g.Symbols[ed.CallerID-1]
		b := g.Symbols[ed.CalleeID-1]
		if a.ModuleID == 0 || b.ModuleID == 0 || a.ModuleID == b.ModuleID {
			continue
		}
		if mo[a.ModuleID] == nil {
			mo[a.ModuleID] = map[int32]bool{}
		}
		mo[a.ModuleID][b.ModuleID] = true
		if mi[b.ModuleID] == nil {
			mi[b.ModuleID] = map[int32]bool{}
		}
		mi[b.ModuleID][a.ModuleID] = true
	}
	for i := range g.Modules {
		m := &g.Modules[i]
		if a := magg[m.ID]; a != nil {
			m.NSymbols, m.NPublic, m.NFiles, m.Sloc = a.n, a.p, a.files, a.sloc
		}
		m.FanOut = int32(len(mo[m.ID]))
		m.FanIn = int32(len(mi[m.ID]))
		if m.FanIn+m.FanOut != 0 {
			m.Instability = float64(m.FanOut) / float64(m.FanIn+m.FanOut)
		}
	}
}

func (e *extractor) reserve(g *Graph, outs []*fileOut) {
	var nSym, nPar, nFld, nLoc, nLit, nMk, nAt, nImp, nHaz, nEn int32
	var nLay, nSS, nDec, nAdd, nSec, nAlc, nMem, nMac, nGlb, nCfg int32
	var nLock, nEv, nAPI, nRare int32
	for _, o := range outs {
		if o == nil {
			continue
		}
		nSym += o.symN
		nRare += o.rareN
		nPar += int32(len(o.params))
		nFld += int32(len(o.fields))
		nLoc += int32(len(o.locals))
		nLit += int32(len(o.literals))
		nMk += int32(len(o.markers))
		nAt += int32(len(o.attrs))
		nImp += int32(len(o.imports))
		nHaz += int32(len(o.hazards))
		nEn += int32(len(o.enums))
		nLay += int32(len(o.layout))
		nSS += int32(len(o.ssize))
		nDec += int32(len(o.decls))
		nAdd += int32(len(o.addrs))
		nSec += int32(len(o.secrets))
		nAlc += int32(len(o.allocs))
		nMem += int32(len(o.memops))
		nMac += int32(len(o.macros))
		nGlb += int32(len(o.globals))
		nCfg += int32(len(o.cfgs))
		nLock += int32(len(o.locks))
		nEv += int32(len(o.evops))
		nAPI += int32(len(o.apiuses))
	}
	g.Symbols = make([]*Symbol, 0, nSym)
	g.symStore = make([]Symbol, 0, nSym)
	g.rare = make([]symRare, 0, nRare)
	g.Params = make([]Param, 0, nPar)
	g.Fields = make([]Field, 0, nFld)
	g.Locals = make([]Local, 0, nLoc)
	g.Literals = make([]Literal, 0, nLit)
	g.Markers = make([]Marker, 0, nMk)
	g.Attrs = make([]Attribute, 0, nAt)
	g.Imports = make([]Import, 0, nImp)
	g.Hazards = make([]Hazard, 0, nHaz)
	g.EnumMem = make([]EnumMember, 0, nEn)
	g.Layout = make([]LayoutRow, 0, nLay)
	g.SSize = make([]StructSize, 0, nSS)
	g.Decls = make([]Declaration, 0, nDec)
	g.Addr = make([]AddrTaken, 0, nAdd)
	g.Secrets = make([]SecretCandidate, 0, nSec)
	g.Allocs = make([]AllocSite, 0, nAlc)
	g.Memops = make([]Memop, 0, nMem)
	g.Macros = make([]Macro, 0, nMac)
	g.Globals = make([]Global, 0, nGlb)
	g.Cfgs = make([]ConfigBlock, 0, nCfg)
	g.Locks = make([]LockRow, 0, nLock)
	g.EvOps = make([]EventOp, 0, nEv)
	g.APIUses = make([]APIUse, 0, nAPI)
}

func (e *extractor) merge(g *Graph, o *fileOut) {
	base := int32(len(g.Symbols))
	syms := o.symA.at(o.symLo, o.symN)
	for i := range syms {
		w := &syms[i]
		g.symStore = append(g.symStore, Symbol{})
		d := &g.symStore[len(g.symStore)-1]
		cgZeroRow(unsafe.Pointer(d), unsafe.Sizeof(*d))
		d.ID = w.ID + base
		d.FileID = w.FileID
		d.ModuleID = w.ModuleID
		d.name = cgPut(w.Name)
		d.qualName = cgPut(w.QualName)
		d.kind = cgPut(w.Kind)
		d.LineStart = w.LineStart
		d.signature = cgPut(w.Signature)
		d.returnType = cgPut(w.ReturnType)
		d.HasSignature = w.HasSignature
		d.HasReturnType = w.HasReturnType
		d.NParams = w.NParams
		d.IsPublic = w.IsPublic
		d.IsStatic = w.IsStatic
		d.IsAbstract = w.IsAbstract
		d.IsOverride = w.IsOverride
		d.IsTest = w.IsTest
		d.IsEntrypoint = w.IsEntrypoint
		d.IsGenerated = w.IsGenerated
		d.Sloc = w.Sloc
		d.NCommentLines = w.NCommentLines
		d.HasDoc = w.HasDoc
		d.Cyclomatic = w.Cyclomatic
		d.Cognitive = w.Cognitive
		d.MaxNesting = w.MaxNesting
		d.NTokens = w.NTokens
		d.NOperators = w.NOperators
		d.NOperands = w.NOperands
		d.NDistinctOperators = w.NDistinctOperators
		d.NDistinctOperands = w.NDistinctOperands
		d.NLoops = w.NLoops
		d.NBranches = w.NBranches
		d.NReturns = w.NReturns
		d.NSwitch = w.NSwitch
		d.NCases = w.NCases
		d.NLabels = w.NLabels
		d.NGotos = w.NGotos
		d.MaxLoopDepth = w.MaxLoopDepth
		d.CallInLoop = w.CallInLoop
		d.AllocInLoop = w.AllocInLoop
		d.IOInLoop = w.IOInLoop
		d.LockInLoop = w.LockInLoop
		d.BranchInLoop = w.BranchInLoop
		d.NLocals = w.NLocals
		d.NCmp = w.NCmp
		d.NArith = w.NArith
		d.NShift = w.NShift
		d.NFloatLit = w.NFloatLit
		d.NMagic = w.NMagic
		d.NNullCheck = w.NNullCheck
		d.NCalls = w.NCalls
		d.NDynamicCalls = w.NDynamicCalls
		d.NUnresolvedCalls = w.NUnresolvedCalls
		d.FanIn = w.FanIn
		d.FanOut = w.FanOut
		d.NCallsites = w.NCallsites
		d.IsRecursive = w.IsRecursive
		d.RiskScore = w.RiskScore
		d.NMemory = w.NMemory
		d.NAlloc = w.NAlloc
		d.NIO = w.NIO
		d.NStdio = w.NStdio
		d.NExec = w.NExec
		d.NLibm = w.NLibm
		d.NInteger = w.NInteger
		d.NConcurrency = w.NConcurrency
		d.NReentrancy = w.NReentrancy
		d.IsInline = w.IsInline
		d.IsVariadic = w.IsVariadic
		d.NPtrLocals = w.NPtrLocals
		d.NDeref = w.NDeref
		d.NCast = w.NCast
		d.NSizeof = w.NSizeof
		d.NIntrinsic = w.NIntrinsic
		d.NAtomic = w.NAtomic
		d.NRestrict = w.NRestrict
		d.NLikely = w.NLikely
		d.NBuiltin = w.NBuiltin
		if old := w.rare; old >= 0 {
			g.rare = append(g.rare, o.symA.rare[old])
			d.rare = int32(len(g.rare) - 1)
		} else {
			d.rare = -1
		}
		g.Symbols = append(g.Symbols, d)
	}

	off := func(ids []int32) {
		for i := range ids {
			ids[i] += base
		}
	}
	for i := range o.params {
		o.params[i].SymbolID += base
	}
	for i := range o.fields {
		o.fields[i].SymbolID += base
	}
	for i := range o.locals {
		o.locals[i].SymbolID += base
	}
	for i := range o.literals {
		o.literals[i].ID = int32(len(g.Literals) + i + 1)
		o.literals[i].SymbolID += base
	}
	for i := range o.markers {
		o.markers[i].ID = int32(len(g.Markers) + i + 1)
	}
	for i := range o.attrs {
		o.attrs[i].ID = int32(len(g.Attrs) + i + 1)
		o.attrs[i].SymbolID += base
	}
	for i := range o.hazards {
		o.hazards[i].SymbolID += base
	}
	for i := range o.enums {
		o.enums[i].SymbolID += base
	}
	for i := range o.layout {
		o.layout[i].SymbolID += base
	}
	for i := range o.ssize {
		o.ssize[i].SymbolID += base
	}
	for i := range o.decls {
		o.decls[i].ID = int32(len(g.Decls) + i + 1)
	}
	for i := range o.addrs {
		o.addrs[i].ID = int32(len(g.Addr) + i + 1)
		if o.addrs[i].HasSym {
			o.addrs[i].SymbolID += base
		}
	}
	for i := range o.secrets {
		o.secrets[i].ID = int32(len(g.Secrets) + i + 1)
		o.secrets[i].SymbolID += base
	}
	for i := range o.allocs {
		o.allocs[i].ID = int32(len(g.Allocs) + i + 1)
		o.allocs[i].SymbolID += base
	}
	for i := range o.memops {
		o.memops[i].ID = int32(len(g.Memops) + i + 1)
		o.memops[i].SymbolID += base
	}
	for i := range o.macros {
		o.macros[i].SymbolID += base
	}
	for i := range o.locks {
		o.locks[i].ID = int32(len(g.Locks) + i + 1)
		o.locks[i].SymbolID += base
	}
	for i := range o.evops {
		o.evops[i].ID = int32(len(g.EvOps) + i + 1)
		o.evops[i].SymbolID += base
	}
	for i := range o.apiuses {
		o.apiuses[i].ID = int32(len(g.APIUses) + i + 1)
		o.apiuses[i].SymbolID += base
	}
	off(o.pendSID)
	e.pendSID = append(e.pendSID, o.pendSID...)
	e.pendFID = append(e.pendFID, o.pendFID...)
	e.pendMID = append(e.pendMID, o.pendMID...)
	e.pendName = append(e.pendName, o.pendName...)
	e.pendLine = append(e.pendLine, o.pendLine...)
	for i, m := range o.macros {
		if _, ok := e.macroSID[o.macroNames[i]]; !ok {
			e.macroSID[o.macroNames[i]] = m.SymbolID
		}
	}
	for _, d := range o.decls {
		e.declared[d.Name] = true
	}
	for _, fs := range o.funcs {
		e.fnByName[fs.name] = append(e.fnByName[fs.name], fs.sid+base)
		e.fnByNameF[fs.name] = append(e.fnByNameF[fs.name], fs.fid)
		e.fnByNameM[fs.name] = append(e.fnByNameM[fs.name], fs.mid)
	}

	for i := range o.params {
		w := &o.params[i]
		g.Params = append(g.Params, Param{})
		d := &g.Params[len(g.Params)-1]
		cgZeroRow(unsafe.Pointer(d), unsafe.Sizeof(*d))
		d.SymbolID = w.SymbolID
		d.Pos = w.Pos
		d.name = cgPut(w.Name)
		d.HasName = w.HasName
		d.typ = cgPut(w.Type)
		d.def = cgPut(w.DefaultValue)
		d.HasDefaultValue = w.HasDefaultValue
		d.IsOptional = w.IsOptional
		d.IsVariadic = w.IsVariadic
		d.IsRef = w.IsRef
		d.IsMutable = w.IsMutable
		d.IsNullable = w.IsNullable
		d.IsGeneric = w.IsGeneric
		d.IsUntyped = w.IsUntyped
		d.TypeDepth = w.TypeDepth
	}
	for i := range o.fields {
		w := &o.fields[i]
		g.Fields = append(g.Fields, Field{})
		d := &g.Fields[len(g.Fields)-1]
		cgZeroRow(unsafe.Pointer(d), unsafe.Sizeof(*d))
		d.SymbolID = w.SymbolID
		d.Ordinal = w.Ordinal
		d.name = cgPut(w.Name)
		d.typ = cgPut(w.Type)
		d.vis = cgPut(w.Visibility)
		d.Line = w.Line
		d.IsStatic = w.IsStatic
		d.IsConst = w.IsConst
		d.IsMutable = w.IsMutable
		d.IsNullable = w.IsNullable
		d.IsCollection = w.IsCollection
		d.IsUntyped = w.IsUntyped
		d.HasDefault = w.HasDefault
		d.TypeDepth = w.TypeDepth
	}
	for i := range o.locals {
		w := &o.locals[i]
		g.Locals = append(g.Locals, Local{})
		d := &g.Locals[len(g.Locals)-1]
		cgZeroRow(unsafe.Pointer(d), unsafe.Sizeof(*d))
		d.SymbolID = w.SymbolID
		d.Ordinal = w.Ordinal
		d.name = cgPut(w.Name)
		d.typ = cgPut(w.Type)
		d.Line = w.Line
		d.IsConst = w.IsConst
		d.IsMutable = w.IsMutable
		d.IsUntyped = w.IsUntyped
		d.HasInit = w.HasInit
		d.InLoop = w.InLoop
		d.ScopeDepth = w.ScopeDepth
	}
	for i := range o.literals {
		w := &o.literals[i]
		g.Literals = append(g.Literals, Literal{})
		d := &g.Literals[len(g.Literals)-1]
		cgZeroRow(unsafe.Pointer(d), unsafe.Sizeof(*d))
		d.ID = w.ID
		d.SymbolID = w.SymbolID
		d.HasSym = w.HasSym
		d.FileID = w.FileID
		d.kind = cgPut(w.Kind)
		d.value = cgPut(w.Value)
		d.Line = w.Line
		d.IsMagic = w.IsMagic
	}
	for i := range o.markers {
		w := &o.markers[i]
		g.Markers = append(g.Markers, Marker{})
		d := &g.Markers[len(g.Markers)-1]
		cgZeroRow(unsafe.Pointer(d), unsafe.Sizeof(*d))
		d.ID = w.ID
		d.FileID = w.FileID
		d.SymbolID = w.SymbolID
		d.HasSym = w.HasSym
		d.kind = cgPut(w.Kind)
		d.Line = w.Line
		d.text = cgPut(w.Text)
	}
	for i := range o.attrs {
		w := &o.attrs[i]
		g.Attrs = append(g.Attrs, Attribute{})
		d := &g.Attrs[len(g.Attrs)-1]
		cgZeroRow(unsafe.Pointer(d), unsafe.Sizeof(*d))
		d.ID = w.ID
		d.SymbolID = w.SymbolID
		d.HasSymbolID = w.HasSymbolID
		d.FileID = w.FileID
		d.name = cgPut(w.Name)
		d.args = cgPut(w.Args)
		d.HasArgs = w.HasArgs
		d.Line = w.Line
	}
	for i := range o.imports {
		w := &o.imports[i]
		g.Imports = append(g.Imports, Import{})
		d := &g.Imports[len(g.Imports)-1]
		cgZeroRow(unsafe.Pointer(d), unsafe.Sizeof(*d))
		d.ID = w.ID
		d.FileID = w.FileID
		d.target = cgPut(w.Target)
		d.TargetID = w.TargetID
		d.HasTargetID = w.HasTargetID
		d.alias = cgPut(w.Alias)
		d.HasAlias = w.HasAlias
		d.kind = cgPut(w.Kind)
		d.Line = w.Line
		d.IsExternal = w.IsExternal
		d.IsRelative = w.IsRelative
		d.IsWildcard = w.IsWildcard
		d.IsTypeOnly = w.IsTypeOnly
		d.IsDynamic = w.IsDynamic
		d.NNames = w.NNames
	}
	for i := range o.hazards {
		w := &o.hazards[i]
		g.Hazards = append(g.Hazards, Hazard{})
		d := &g.Hazards[len(g.Hazards)-1]
		cgZeroRow(unsafe.Pointer(d), unsafe.Sizeof(*d))
		d.SymbolID = w.SymbolID
		d.pattern = cgPut(w.Pattern)
		d.category = cgPut(w.Category)
		d.N = w.N
		d.FirstLine = w.FirstLine
	}
	for i := range o.enums {
		w := &o.enums[i]
		g.EnumMem = append(g.EnumMem, EnumMember{})
		d := &g.EnumMem[len(g.EnumMem)-1]
		cgZeroRow(unsafe.Pointer(d), unsafe.Sizeof(*d))
		d.SymbolID = w.SymbolID
		d.Ordinal = w.Ordinal
		d.name = cgPut(w.Name)
		d.value = cgPut(w.Value)
		d.HasValue = w.HasValue
		d.NFields = w.NFields
	}
	g.Layout = append(g.Layout, o.layout...)
	g.SSize = append(g.SSize, o.ssize...)
	for i := range o.decls {
		w := &o.decls[i]
		g.Decls = append(g.Decls, Declaration{})
		d := &g.Decls[len(g.Decls)-1]
		cgZeroRow(unsafe.Pointer(d), unsafe.Sizeof(*d))
		d.ID = w.ID
		d.FileID = w.FileID
		d.name = cgPut(w.Name)
		d.Line = w.Line
	}
	for i := range o.addrs {
		w := &o.addrs[i]
		g.Addr = append(g.Addr, AddrTaken{})
		d := &g.Addr[len(g.Addr)-1]
		cgZeroRow(unsafe.Pointer(d), unsafe.Sizeof(*d))
		d.ID = w.ID
		d.SymbolID = w.SymbolID
		d.HasSym = w.HasSym
		d.FileID = w.FileID
		d.name = cgPut(w.Name)
		d.Line = w.Line
		d.kind = cgPut(w.Kind)
	}
	for i := range o.secrets {
		w := &o.secrets[i]
		g.Secrets = append(g.Secrets, SecretCandidate{})
		d := &g.Secrets[len(g.Secrets)-1]
		cgZeroRow(unsafe.Pointer(d), unsafe.Sizeof(*d))
		d.ID = w.ID
		d.SymbolID = w.SymbolID
		d.HasSym = w.HasSym
		d.FileID = w.FileID
		d.value = cgPut(w.Value)
		d.Line = w.Line
	}
	for i := range o.allocs {
		w := &o.allocs[i]
		g.Allocs = append(g.Allocs, AllocSite{})
		d := &g.Allocs[len(g.Allocs)-1]
		cgZeroRow(unsafe.Pointer(d), unsafe.Sizeof(*d))
		d.ID = w.ID
		d.SymbolID = w.SymbolID
		d.FileID = w.FileID
		d.fn = cgPut(w.Fn)
		d.sizeExpr = cgPut(w.SizeExpr)
		d.Line = w.Line
	}
	for i := range o.memops {
		w := &o.memops[i]
		g.Memops = append(g.Memops, Memop{})
		d := &g.Memops[len(g.Memops)-1]
		cgZeroRow(unsafe.Pointer(d), unsafe.Sizeof(*d))
		d.ID = w.ID
		d.SymbolID = w.SymbolID
		d.FileID = w.FileID
		d.fn = cgPut(w.Fn)
		d.dst = cgPut(w.Dst)
		d.src = cgPut(w.Src)
		d.sizeArg = cgPut(w.SizeArg)
		d.sizeBuf = cgPut(w.SizeBuf)
		d.dstTail = cgPut(w.DstTail)
		d.Line = w.Line
	}
	for i := range o.macros {
		w := &o.macros[i]
		g.Macros = append(g.Macros, Macro{})
		d := &g.Macros[len(g.Macros)-1]
		cgZeroRow(unsafe.Pointer(d), unsafe.Sizeof(*d))
		d.SymbolID = w.SymbolID
		d.IsFunctionlike = w.IsFunctionlike
		d.NParams = w.NParams
		d.body = cgPut(w.Body)
		d.HasBody = w.HasBody
		d.BodyLen = w.BodyLen
		d.IsMultiline = w.IsMultiline
		d.NUses = w.NUses
	}
	for i := range o.globals {
		w := &o.globals[i]
		g.Globals = append(g.Globals, Global{})
		d := &g.Globals[len(g.Globals)-1]
		cgZeroRow(unsafe.Pointer(d), unsafe.Sizeof(*d))
		d.ID = w.ID
		d.FileID = w.FileID
		d.ModuleID = w.ModuleID
		d.name = cgPut(w.Name)
		d.typ = cgPut(w.Type)
		d.Line = w.Line
		d.IsStatic = w.IsStatic
		d.IsConst = w.IsConst
		d.IsVolatile = w.IsVolatile
		d.IsAtomic = w.IsAtomic
		d.IsArray = w.IsArray
		d.PtrDepth = w.PtrDepth
		d.HasInit = w.HasInit
	}
	for i := range o.cfgs {
		w := &o.cfgs[i]
		g.Cfgs = append(g.Cfgs, ConfigBlock{})
		d := &g.Cfgs[len(g.Cfgs)-1]
		cgZeroRow(unsafe.Pointer(d), unsafe.Sizeof(*d))
		d.ID = w.ID
		d.FileID = w.FileID
		d.directive = cgPut(w.Directive)
		d.expr = cgPut(w.Expr)
		d.Line = w.Line
		d.IsConfig = w.IsConfig
	}
	for i := range o.locks {
		w := &o.locks[i]
		g.Locks = append(g.Locks, LockRow{})
		d := &g.Locks[len(g.Locks)-1]
		cgZeroRow(unsafe.Pointer(d), unsafe.Sizeof(*d))
		d.ID = w.ID
		d.SymbolID = w.SymbolID
		d.FileID = w.FileID
		d.name = cgPut(w.Name)
		d.Line = w.Line
	}
	for i := range o.evops {
		w := &o.evops[i]
		g.EvOps = append(g.EvOps, EventOp{})
		d := &g.EvOps[len(g.EvOps)-1]
		cgZeroRow(unsafe.Pointer(d), unsafe.Sizeof(*d))
		d.ID = w.ID
		d.SymbolID = w.SymbolID
		d.FileID = w.FileID
		d.family = cgPut(w.Family)
		d.fn = cgPut(w.Fn)
		d.args = cgPut(w.Args)
		d.Line = w.Line
	}
	for i := range o.apiuses {
		w := &o.apiuses[i]
		g.APIUses = append(g.APIUses, APIUse{})
		d := &g.APIUses[len(g.APIUses)-1]
		cgZeroRow(unsafe.Pointer(d), unsafe.Sizeof(*d))
		d.ID = w.ID
		d.SymbolID = w.SymbolID
		d.FileID = w.FileID
		d.ns = cgPut(w.NS)
		d.fn = cgPut(w.Fn)
		d.Line = w.Line
	}
}

func (e *extractor) postBuild() {
	g := e.g
	fnNames := map[string]bool{}
	for i := range g.Symbols {
		if g.Symbols[i].Kind() == "function" {
			fnNames[g.Symbols[i].Name()] = true
		}
	}
	pruned := 0
	out := g.Addr[:0]
	for _, a := range g.Addr {
		if !a.HasSym && !fnNames[a.Name()] {
			pruned++
			continue
		}
		out = append(out, a)
	}
	g.Addr = out
	g.AddrPruned = int32(pruned)
	g.Meta["addr_taken_pruned"] = itoa(pruned) +
		" non-function file-scope references dropped"

	e.transitiveFan()
	e.includeCycles()
}

func (e *extractor) transitiveFan() {
	g := e.g
	n := int32(len(g.Symbols)) + 1
	type ek struct{ a, b int32 }
	edges := make([]ek, 0, len(g.Edges))
	has := make([]bool, n)
	for _, ed := range g.Edges {
		if ed.CallerID == ed.CalleeID {
			continue
		}
		edges = append(edges, ek{ed.CallerID, ed.CalleeID})
		has[ed.CallerID] = true
		has[ed.CalleeID] = true
	}
	if len(edges) == 0 {
		return
	}
	nodes := make([]int32, 0, n)
	for v := int32(1); v < n; v++ {
		if has[v] {
			nodes = append(nodes, v)
		}
	}
	start := make([]int32, n+1)
	for _, ed := range edges {
		start[ed.a+1]++
	}
	for v := int32(1); v < n; v++ {
		start[v+1] += start[v]
	}
	fill := make([]int32, n)
	copy(fill, start[:n])
	adj := make([]int32, len(edges))
	for _, ed := range edges {
		adj[fill[ed.a]] = ed.b
		fill[ed.a]++
	}
	index := make([]int32, n)
	low := make([]int32, n)
	onstk := make([]bool, n)
	compOf := make([]int32, n)
	for i := range index {
		index[i] = -1
		compOf[i] = -1
	}
	stk := make([]int32, 0, 128)
	comps := make([][]int32, 0, 64)
	var counter int32
	type frame struct {
		v int32
		w int32
	}
	for _, root := range nodes {
		if index[root] >= 0 {
			continue
		}
		index[root] = counter
		low[root] = counter
		counter++
		stk = append(stk, root)
		onstk[root] = true
		work := []frame{{root, 0}}
		for len(work) > 0 {
			top := &work[len(work)-1]
			v := top.v
			descended := false
			for top.w < start[v+1]-start[v] {
				w := adj[start[v]+top.w]
				top.w++
				if index[w] < 0 {
					index[w] = counter
					low[w] = counter
					counter++
					stk = append(stk, w)
					onstk[w] = true
					work = append(work, frame{w, 0})
					descended = true
					break
				}
				if onstk[w] && index[w] < low[v] {
					low[v] = index[w]
				}
			}
			if descended {
				continue
			}
			work = work[:len(work)-1]
			if len(work) > 0 {
				u := work[len(work)-1].v
				if low[v] < low[u] {
					low[u] = low[v]
				}
			}
			if low[v] == index[v] {
				comp := []int32{}
				for {
					w := stk[len(stk)-1]
					stk = stk[:len(stk)-1]
					onstk[w] = false
					comp = append(comp, w)
					if w == v {
						break
					}
				}
				comps = append(comps, comp)
			}
		}
	}
	for ci, c := range comps {
		for _, v := range c {
			compOf[v] = int32(ci)
		}
	}
	slot := make([]int32, n)
	for i, v := range nodes {
		slot[v] = int32(i)
	}
	nComp := len(comps)
	words := (len(nodes) + 63) / 64
	predE := make([][]int32, nComp)
	succE := make([][]int32, nComp)
	for _, ed := range edges {
		pc, cc := compOf[ed.a], compOf[ed.b]
		if pc == cc {
			continue
		}
		predE[cc] = append(predE[cc], pc)
		succE[pc] = append(succE[pc], cc)
	}
	preds := make([][]uint64, nComp)
	succs := make([][]uint64, nComp)
	setNode := func(bits []uint64, v int32) {
		s := slot[v]
		bits[s>>6] |= 1 << uint(s&63)
	}
	orInto := func(dst, src []uint64) {
		for i := range src {
			dst[i] |= src[i]
		}
	}
	for ci := nComp - 1; ci >= 0; ci-- {
		acc := make([]uint64, words)
		for _, p := range predE[ci] {
			orInto(acc, preds[p])
			for _, v := range comps[p] {
				setNode(acc, v)
			}
		}
		preds[ci] = acc
	}
	for ci := range nComp {
		acc := make([]uint64, words)
		for _, c2 := range succE[ci] {
			orInto(acc, succs[c2])
			for _, v := range comps[c2] {
				setNode(acc, v)
			}
		}
		succs[ci] = acc
	}
	for ci, comp := range comps {
		baseIn := int32(popcount(preds[ci]))
		baseOut := int32(popcount(succs[ci]))
		extra := int32(len(comp) - 1)
		if baseIn+baseOut+extra == 0 {
			continue
		}
		for _, v := range comp {
			e.g.Reach = append(e.g.Reach, Reach{SymbolID: v,
				NTransitive: baseIn + extra, NTransitiveOut: baseOut + extra})
		}
	}
}

func popcount(b []uint64) int {
	n := 0
	for _, w := range b {
		n += popcnt64(w)
	}
	return n
}

func popcnt64(x uint64) int {
	n := 0
	for x != 0 {
		x &= x - 1
		n++
	}
	return n
}

func (e *extractor) includeCycles() {
	g := e.g
	adj := map[int32]*pyset{}
	roots := []int32{}
	for i := range g.Imports {
		im := &g.Imports[i]
		if !im.HasTargetID || im.IsRelative != 1 || im.Kind() != "include" {
			continue
		}
		if g.Files[im.FileID-1].IsTest == 1 {
			continue
		}
		s := adj[im.FileID]
		if s == nil {
			s = newPyset()
			adj[im.FileID] = s
			roots = append(roots, im.FileID)
		}
		s.add(im.TargetID)
	}
	slices.Sort(roots)
	paths := make(map[int32]string, len(g.Files))
	for i := range g.Files {
		paths[g.Files[i].ID] = g.Files[i].Path()
	}
	seen := map[string]bool{}
	type row struct {
		a, b    string
		length  int
		members string
	}
	var rows []row
	for _, root := range roots {
		stack := [][2]any{}
		stack = append(stack, [2]any{root, []int32{root}})
		for len(stack) > 0 {
			top := stack[len(stack)-1]
			stack = stack[:len(stack)-1]
			node := top[0].(int32)
			path := top[1].([]int32)
			if s := adj[node]; s != nil {
				for _, nxt := range s.order() {
					if nxt == root && len(path) >= 2 {
						key := pathKey(path)
						if seen[key] {
							continue
						}
						seen[key] = true
						members := make([]string, 0, len(path))
						for _, f := range path {
							if p, ok := paths[f]; ok {
								members = append(members, p)
							} else {
								members = append(members, "?")
							}
						}
						rows = append(rows, row{members[0], members[len(members)-1],
							len(path), strings.Join(members, " -> ")})
					} else if !containsInt32(path, nxt) && len(path) < 8 {
						stack = append(stack, [2]any{nxt,
							append(append([]int32{}, path...), nxt)})
					}
				}
			}
			if len(rows) > 5000 {
				break
			}
		}
	}
	for _, r := range rows {
		g.Cycles = append(g.Cycles, IncludeCycle{})
		cy := &g.Cycles[len(g.Cycles)-1]
		cgZeroRow(unsafe.Pointer(cy), unsafe.Sizeof(*cy))
		cy.aPath = cgPut(r.a)
		cy.bPath = cgPut(r.b)
		cy.Length = int32(r.length)
		cy.members = cgPut(r.members)
	}
}

func pathKey(path []int32) string {
	cp := append([]int32{}, path...)
	slices.Sort(cp)
	return itoaArr(cp)
}

func itoaArr(v []int32) string {
	var sb strings.Builder
	for i, x := range v {
		if i > 0 {
			sb.WriteByte(',')
		}
		sb.WriteString(strconv.Itoa(int(x)))
	}
	return sb.String()
}

func containsInt32(s []int32, v int32) bool {
	return slices.Contains(s, v)
}

type pyset struct {
	table []int32
	mask  int
	fill  int
	used  int
}

func newPyset() *pyset {
	return &pyset{table: make([]int32, 8), mask: 7}
}

func psetCap(n int) int {
	t := 8
	for n > t/2 {
		t *= 4
	}
	return t
}

func (s *pyset) add(v int32) {
	if want := psetCap(s.used + 1); want > len(s.table) {
		s.resize(want, v)
		return
	}
	s.place(v)
	s.fill++
	s.used++
}

func (s *pyset) place(v int32) {
	mask := len(s.table) - 1
	i := int(uint32(v) & uint32(mask))
	for s.table[i] != 0 {
		i = (i + 1) & mask
	}
	s.table[i] = v
}

func (s *pyset) resize(newSize int, v int32) {
	nt := make([]int32, newSize)
	old := s.table
	s.table = nt
	s.place(v)
	for _, x := range old {
		if x != 0 {
			s.place(x)
		}
	}
	s.fill = s.used + 1
	s.used++
}

func (s *pyset) order() []int32 {
	out := make([]int32, 0, s.used)
	for _, v := range s.table {
		if v != 0 {
			out = append(out, v)
		}
	}
	return out
}

func buildIndex(g *Graph) {
	g.byFile = make(map[int32][]int32, len(g.Files))
	g.byName = make(map[string][]int32, len(g.Symbols))
	for i := range g.Symbols {
		s := g.Symbols[i]
		g.byFile[s.FileID] = append(g.byFile[s.FileID], s.ID)
		g.byName[s.Name()] = append(g.byName[s.Name()], s.ID)
	}
	g.fileByBase = make(map[string]int32, len(g.Files))
	for i := range g.Files {
		b := pathBase(g.Files[i].Path())
		if _, ok := g.fileByBase[b]; !ok {
			g.fileByBase[b] = g.Files[i].ID
		}
	}
}

func qQ1(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "io", "mem", "int_", "alloc", "cyclo", "fan_in", "at"}
	var rows [][]fval
	for _, s := range g.syms() {
		if s.NIO <= 0 || (s.NMemory <= 0 && s.NInteger <= 0) {
			continue
		}
		if !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		rows = append(rows, []fval{fStr(s.Name()), fI32(s.NIO), fI32(s.NMemory),
			fI32(s.NInteger), fI32(s.NAlloc), fI32(s.Cyclomatic), fI32(s.FanIn),
			fStr(g.at(s))})
	}
	orderBy(rows, dSum(2, 3), dI(1))
	return cols, limit(rows, p)
}

func qQ2(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "cyclo", "nest", "io", "locals", "fan_in", "sloc", "at"}
	var rows [][]fval
	for _, s := range g.syms() {
		if s.IsRecursive != 1 || s.Kind() != "function" {
			continue
		}
		if !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		rows = append(rows, []fval{fStr(s.Name()), fI32(s.Cyclomatic),
			fI32(s.MaxNesting), fI32(s.NIO), fI32(s.NLocals), fI32(s.FanIn),
			fI32(s.Sloc), fStr(g.at(s))})
	}
	orderBy(rows, dI(1), cmpS(0))
	return cols, limit(rows, p)
}

func qQ3(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "allocs", "frees", "fan_in", "returns_", "gotos",
		"labels", "at"}
	var rows [][]fval
	for _, s := range g.syms() {
		if s.NAlloc <= 0 || g.rv(s).NFree != 0 {
			continue
		}
		if !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		rows = append(rows, []fval{fStr(s.Name()), fI32(s.NAlloc), fI32(g.rv(s).NFree),
			fI32(s.FanIn), fI32(s.NReturns), fI32(s.NGotos), fI32(s.NLabels),
			fStr(g.at(s))})
	}
	orderBy(rows, dI(1), dI(3))
	return cols, limit(rows, p)
}

func qQ4(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"path", "libc", "project", "distinct_fns", "via"}
	type agg struct {
		libc, project int32
		pats          []string
	}
	byFile := map[int32]*agg{}
	var order []int32

	hs := g.hazardsByCatN("alloc")
	for _, hi := range hs {
		h := &g.Hazards[hi]
		sid := h.SymbolID
		if sid < 1 || int(sid) > len(g.Symbols) {
			continue
		}
		fid := g.Symbols[sid-1].FileID
		a := byFile[fid]
		if a == nil {
			a = &agg{}
			byFile[fid] = a
			order = append(order, fid)
		}
		if libcAllocNames[h.Pattern()] {
			a.libc += h.N
		} else {
			a.project += h.N
		}
		if !containsStr(a.pats, h.Pattern()) {
			a.pats = append(a.pats, h.Pattern())
		}
	}
	var rows [][]fval
	for _, fid := range order {
		a := byFile[fid]
		if a.libc <= 0 || a.project <= 0 {
			continue
		}
		if int(fid) > len(g.Files) {
			continue
		}
		f := &g.Files[fid-1]
		if !likeMatch(g.modName(f.ModuleID), p.mod) {
			continue
		}
		rows = append(rows, []fval{fStr(f.Path()), fI32(a.libc), fI32(a.project),
			fInt(len(a.pats)), fStr(groupConcat(a.pats))})
	}
	orderBy(rows, dSum(1, 2))
	return cols, limit(rows, p)
}

func qQ5(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "allocs", "depth", "frees", "calls", "fan_in", "at"}
	var rows [][]fval
	for _, s := range g.syms() {
		if s.AllocInLoop <= 0 || !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		rows = append(rows, []fval{fStr(s.Name()), fI32(s.AllocInLoop),
			fI32(s.MaxLoopDepth), fI32(g.rv(s).NFree), fI32(s.CallInLoop),
			fI32(s.FanIn), fStr(g.at(s))})
	}
	orderBy(rows, dI(1), dI(2))
	return cols, limit(rows, p)
}

func qQ6(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "allocs", "frees", "loops", "brs", "sloc", "fan_in", "at"}
	var rows [][]fval
	for _, s := range g.syms() {
		if s.Kind() != "function" || s.NAlloc <= 0 || g.rv(s).NFree <= 0 ||
			s.NLoops <= 0 || s.Sloc > 120 {
			continue
		}
		if !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		rows = append(rows, []fval{fStr(s.Name()), fI32(s.NAlloc), fI32(g.rv(s).NFree),
			fI32(s.NLoops), fI32(s.NBranches), fI32(s.Sloc), fI32(s.FanIn),
			fStr(g.at(s))})
	}
	orderBy(rows, dWeighted([][3]int32{{3, 3}, {1, 4}, {2, 1}}), cmpI(5), cmpS(0))
	return cols, limit(rows, p)
}

func qQ7(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name_", "type_", "ptr", "arr", "stat", "init", "module",
		"at", "mod_conc_fns"}
	modConc := map[int32]int32{}
	for i := range g.Symbols {
		if g.Symbols[i].NConcurrency > 0 {
			modConc[g.Symbols[i].ModuleID]++
		}
	}
	var rows [][]fval
	for i := range g.Globals {
		gl := &g.Globals[i]
		if gl.IsConst != 0 || gl.IsAtomic != 0 || gl.IsVolatile != 0 {
			continue
		}
		if gl.FileID < 1 || int(gl.FileID) > len(g.Files) {
			continue
		}
		f := &g.Files[gl.FileID-1]
		if f.IsTest != 0 {
			continue
		}
		if !likeMatch(g.modName(gl.ModuleID), p.mod) {
			continue
		}
		rows = append(rows, []fval{fStr(gl.Name()), fStr(gl.Type()), fI32(gl.PtrDepth),
			fI32(gl.IsArray), fI32(gl.IsStatic), fI32(gl.HasInit),
			fStr(g.modName(gl.ModuleID)),
			fStr(f.Path() + ":" + strconv.Itoa(int(gl.Line))),
			fI32(modConc[gl.ModuleID])})
	}
	orderBy(rows, dI(8), dI(2), cmpS(0))
	return cols, limit(rows, p)
}

func qQ8(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "sw", "depth", "calls", "cases", "sloc", "fan_in", "at"}
	var rows [][]fval
	for _, s := range g.syms() {
		if g.rv(s).SwitchInLoop <= 0 || !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		rows = append(rows, []fval{fStr(s.Name()), fI32(g.rv(s).SwitchInLoop),
			fI32(s.MaxLoopDepth), fI32(s.CallInLoop), fI32(s.NCases),
			fI32(s.Sloc), fI32(s.FanIn), fStr(g.at(s))})
	}
	orderBy(rows, dI(1), dI(3))
	return cols, limit(rows, p)
}

func qQ9(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "strlens", "depth", "loops", "fan_in", "at"}
	var rows [][]fval
	for _, s := range g.syms() {
		if g.rv(s).StrlenInLoop <= 0 || !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		rows = append(rows, []fval{fStr(s.Name()), fI32(g.rv(s).StrlenInLoop),
			fI32(s.MaxLoopDepth), fI32(s.NLoops), fI32(s.FanIn), fStr(g.at(s))})
	}
	orderBy(rows, dI(2), dI(1))
	return cols, limit(rows, p)
}

func qQ10(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "r_null", "r_neg", "r_0", "r_val", "r_void",
		"ret_type", "fan_in", "at"}
	var rows [][]fval
	for _, s := range g.syms() {
		if s.Kind() != "function" {
			continue
		}
		shapes := 0
		for _, v := range [][2]int32{{g.rv(s).RetNull, 0}, {g.rv(s).RetNeg, 0}, {g.rv(s).RetZero, 0}} {
			if v[0] > 0 {
				shapes++
			}
		}
		if shapes < 2 {
			continue
		}
		if !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		rows = append(rows, []fval{fStr(s.Name()), fI32(g.rv(s).RetNull), fI32(g.rv(s).RetNeg),
			fI32(g.rv(s).RetZero), fI32(g.rv(s).RetVal), fI32(g.rv(s).RetVoid),
			fOptStr(s.ReturnType(), s.HasReturnType), fI32(s.FanIn), fStr(g.at(s))})
	}
	orderBy(rows, dI(7), cmpS(0))
	return cols, limit(rows, p)
}

func qQ11(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "kind", "sloc", "cyclo", "ext_calls", "at"}
	var rows [][]fval
	for _, s := range g.syms() {
		if s.FanIn != 0 || s.IsPublic != 0 || s.IsTest != 0 ||
			s.IsEntrypoint != 0 || s.IsOverride != 0 || s.IsAbstract != 0 {
			continue
		}
		switch s.Kind() {
		case "function", "method", "closure":
		default:
			continue
		}
		if s.Name() == "(anonymous)" || s.Name() == "<module>" {
			continue
		}
		f := g.fileOf(s.ID)
		if f == nil || f.IsTest != 0 || f.IsGenerated != 0 {
			continue
		}
		if !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		rows = append(rows, []fval{fStr(s.Name()), fStr(s.Kind()), fI32(s.Sloc),
			fI32(s.Cyclomatic), fI32(g.rv(s).NExternalCalls), fStr(g.at(s))})
	}
	orderBy(rows, dI(2))
	return cols, limit(rows, p)
}

func qQ12(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "module", "n_patterns", "patterns", "reentrancy_calls",
		"concurrency_calls", "atomics", "fan_in", "cyclo", "at"}
	bySym := map[int32][]string{}
	for _, h := range g.Hazards {
		if h.Category() != "reentrancy" {
			continue
		}
		if !containsStr(bySym[h.SymbolID], h.Pattern()) {
			bySym[h.SymbolID] = append(bySym[h.SymbolID], h.Pattern())
		}
	}
	var rows [][]fval
	for _, s := range g.syms() {
		pats := bySym[s.ID]
		if len(pats) == 0 || s.NConcurrency <= 0 {
			continue
		}
		f := g.fileOf(s.ID)
		if f == nil || f.IsTest != 0 {
			continue
		}
		if !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		rows = append(rows, []fval{fStr(s.Name()), fStr(g.modName(s.ModuleID)),
			fInt(len(pats)), fStr(groupConcat(pats)), fI32(s.NReentrancy),
			fI32(s.NConcurrency), fI32(s.NAtomic), fI32(s.FanIn),
			fI32(s.Cyclomatic), fStr(g.at(s))})
	}
	orderBy(rows, dI(5), dI(2), dI(7))
	return cols, limit(rows, p)
}

var convFns = []string{"atoi", "atol", "atoll", "atof", "strtol", "strtoul",
	"strtoll", "strtoull", "strtod", "strtof", "strtoimax", "strtoumax"}

func qQ13(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "module", "n_conversions", "conversions",
		"conversion_calls", "io_calls", "stdio_calls", "memory_calls",
		"returns_value", "fan_in", "at"}
	bySym := map[int32][]string{}
	total := map[int32]int32{}
	for pi, h := range g.hazardsByPattern(convFns) {
		_ = pi
		if !containsStr(bySym[h.SymbolID], h.Pattern()) {
			bySym[h.SymbolID] = append(bySym[h.SymbolID], h.Pattern())
		}
		total[h.SymbolID] += h.N
	}
	var rows [][]fval
	for _, s := range g.syms() {
		if len(bySym[s.ID]) == 0 || (s.NIO <= 0 && s.NStdio <= 0) {
			continue
		}
		f := g.fileOf(s.ID)
		if f == nil || f.IsTest != 0 {
			continue
		}
		if !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		rows = append(rows, []fval{fStr(s.Name()), fStr(g.modName(s.ModuleID)),
			fInt(len(bySym[s.ID])), fStr(groupConcat(bySym[s.ID])),
			fI32(total[s.ID]), fI32(s.NIO), fI32(s.NStdio), fI32(s.NMemory),
			fI32(g.rv(s).RetVal), fI32(s.FanIn), fStr(g.at(s))})
	}
	orderBy(rows, dI(4), dI(5), dI(9))
	return cols, limit(rows, p)
}

var strcpyFns = []string{"sprintf", "strcpy", "strcat", "gets", "vsprintf",
	"scanf", "sscanf", "fscanf", "vfscanf", "vsscanf"}
var printfFns = []string{"printf", "fprintf", "sprintf", "snprintf", "vprintf",
	"vfprintf", "vsprintf", "vsnprintf", "syslog"}
var sigUnsafe = []string{"malloc", "calloc", "realloc", "free", "printf",
	"fprintf", "sprintf", "snprintf", "syslog", "fopen", "fclose", "fread",
	"fwrite", "strdup"}

func hazardsBy(g *Graph, cat string, pats []string) (map[int32][]string, map[int32]int32) {
	list := map[int32][]string{}
	total := map[int32]int32{}
	for _, h := range g.Hazards {
		if (cat != "" && h.Category() != cat) || !containsStr(pats, h.Pattern()) {
			continue
		}
		if !containsStr(list[h.SymbolID], h.Pattern()) {
			list[h.SymbolID] = append(list[h.SymbolID], h.Pattern())
		}
		total[h.SymbolID] += h.N
	}
	return list, total
}

func qQ14(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "n_patterns", "patterns", "dangerous_calls",
		"memory_calls", "io_calls", "fan_in", "cyclo", "at"}
	list, total := hazardsBy(g, "", strcpyFns)
	var rows [][]fval
	for _, s := range g.syms() {
		if len(list[s.ID]) == 0 {
			continue
		}
		f := g.fileOf(s.ID)
		if f == nil || f.IsTest != 0 {
			continue
		}
		if !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		rows = append(rows, []fval{fStr(s.Name()), fInt(len(list[s.ID])),
			fStr(groupConcat(list[s.ID])), fI32(total[s.ID]), fI32(s.NMemory),
			fI32(s.NIO), fI32(s.FanIn), fI32(s.Cyclomatic), fStr(g.at(s))})
	}
	orderBy(rows, dI(3), dI(6))
	return cols, limit(rows, p)
}

func qQ15(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "n_patterns", "patterns", "format_calls", "io_calls",
		"stdio_calls", "fan_in", "cyclo", "at"}
	list, total := hazardsBy(g, "", printfFns)
	for k := range list {
		sort.Strings(list[k])
	}
	var rows [][]fval
	for _, s := range g.syms() {
		if len(list[s.ID]) == 0 {
			continue
		}
		f := g.fileOf(s.ID)
		if f == nil || f.IsTest != 0 {
			continue
		}
		if !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		rows = append(rows, []fval{fStr(s.Name()), fInt(len(list[s.ID])),
			fStr(groupConcat(list[s.ID])), fI32(total[s.ID]), fI32(s.NIO),
			fI32(s.NStdio), fI32(s.FanIn), fI32(s.Cyclomatic), fStr(g.at(s))})
	}
	orderBy(rows, dI(3), dI(6))
	return cols, limit(rows, p)
}

func qQ16(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "allocs", "frees", "imbalance", "memory_ops",
		"fan_in", "cyclo", "returns", "at"}
	var rows [][]fval
	for _, s := range g.symsName() {
		if s.NAlloc <= 0 || g.rv(s).NFree != 0 {
			continue
		}
		f := g.fileOf(s.ID)
		if f == nil || f.IsTest != 0 {
			continue
		}
		if !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		rows = append(rows, []fval{fStr(s.Name()), fI32(s.NAlloc), fI32(g.rv(s).NFree),
			fI32(s.NAlloc - g.rv(s).NFree), fI32(s.NMemory), fI32(s.FanIn),
			fI32(s.Cyclomatic), fI32(s.NReturns), fStr(g.at(s))})
	}
	orderBy(rows, dI(1), dI(5))
	return cols, limit(rows, p)
}

func qQ17(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "allocs", "frees", "excess_frees", "return_paths",
		"cyclo", "fan_in", "at"}
	var rows [][]fval
	for _, s := range g.syms() {
		if g.rv(s).NFree <= s.NAlloc || g.rv(s).NFree <= 1 {
			continue
		}
		f := g.fileOf(s.ID)
		if f == nil || f.IsTest != 0 {
			continue
		}
		if !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		rows = append(rows, []fval{fStr(s.Name()), fI32(s.NAlloc), fI32(g.rv(s).NFree),
			fI32(g.rv(s).NFree - s.NAlloc), fI32(s.NReturns), fI32(s.Cyclomatic),
			fI32(s.FanIn), fStr(g.at(s))})
	}
	orderBy(rows, dI(3), dI(6))
	return cols, limit(rows, p)
}

func qQ18(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "memory_ops", "null_checks", "allocs", "cyclo",
		"fan_in", "at"}
	var rows [][]fval
	for _, s := range g.syms() {
		if s.NMemory <= 5 || s.NNullCheck != 0 {
			continue
		}
		f := g.fileOf(s.ID)
		if f == nil || f.IsTest != 0 {
			continue
		}
		if !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		rows = append(rows, []fval{fStr(s.Name()), fI32(s.NMemory),
			fI32(s.NNullCheck), fI32(s.NAlloc), fI32(s.Cyclomatic),
			fI32(s.FanIn), fStr(g.at(s))})
	}
	orderBy(rows, dI(1), dI(5))
	return cols, limit(rows, p)
}

func qQ19(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "arith_ops", "integer_ops", "comparisons", "loops",
		"cyclo", "fan_in", "at"}
	var rows [][]fval
	for _, s := range g.syms() {
		if s.NArith <= 20 {
			continue
		}
		f := g.fileOf(s.ID)
		if f == nil || f.IsTest != 0 {
			continue
		}
		if !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		rows = append(rows, []fval{fStr(s.Name()), fI32(s.NArith), fI32(s.NInteger),
			fI32(s.NCmp), fI32(s.NLoops), fI32(s.Cyclomatic), fI32(s.FanIn),
			fStr(g.at(s))})
	}
	orderBy(rows, dI(1), dI(6))
	return cols, limit(rows, p)
}

func qQ20(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "arith_ops", "div_in_loop", "comparisons",
		"null_checks", "cyclo", "fan_in", "at"}
	var rows [][]fval
	for _, s := range g.syms() {
		if s.NArith <= 0 || s.NCmp >= s.NArith {
			continue
		}
		f := g.fileOf(s.ID)
		if f == nil || f.IsTest != 0 {
			continue
		}
		if !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		rows = append(rows, []fval{fStr(s.Name()), fI32(s.NArith),
			fI32(g.rv(s).DivInLoop), fI32(s.NCmp), fI32(s.NNullCheck),
			fI32(s.Cyclomatic), fI32(s.FanIn), fStr(g.at(s))})
	}
	orderBy(rows, dI(1), dI(6))
	return cols, limit(rows, p)
}

func qQ21(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "switches", "cases", "cyclo", "fan_in", "at"}
	var rows [][]fval
	for _, s := range g.syms() {
		if s.NSwitch <= 0 {
			continue
		}
		f := g.fileOf(s.ID)
		if f == nil || f.IsTest != 0 {
			continue
		}
		if !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		rows = append(rows, []fval{fStr(s.Name()), fI32(s.NSwitch), fI32(s.NCases),
			fI32(s.Cyclomatic), fI32(s.FanIn), fStr(g.at(s))})
	}
	orderBy(rows, dI(1), dI(4))
	return cols, limit(rows, p)
}

func qQ22(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "concurrency_ops", "atomic_ops", "reentrancy_calls",
		"memory_ops", "fan_in", "cyclo", "at"}
	var rows [][]fval
	for _, s := range g.syms() {
		if s.NConcurrency <= 0 {
			continue
		}
		f := g.fileOf(s.ID)
		if f == nil || f.IsTest != 0 {
			continue
		}
		if !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		rows = append(rows, []fval{fStr(s.Name()), fI32(s.NConcurrency),
			fI32(s.NAtomic), fI32(s.NReentrancy), fI32(s.NMemory),
			fI32(s.FanIn), fI32(s.Cyclomatic), fStr(g.at(s))})
	}
	orderBy(rows, dI(1), dI(5))
	return cols, limit(rows, p)
}

func qQ23(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "n_unsafe_patterns", "unsafe_patterns", "io_calls",
		"memory_calls", "fan_in", "at"}
	list, _ := hazardsBy(g, "", sigUnsafe)
	var rows [][]fval
	for _, s := range g.syms() {
		if len(list[s.ID]) == 0 {
			continue
		}
		low := asciiLower(s.Name())
		if !strings.Contains(low, "sig") && !strings.Contains(low, "handler") &&
			!strings.Contains(low, "signal") {
			continue
		}
		f := g.fileOf(s.ID)
		if f == nil || f.IsTest != 0 {
			continue
		}
		if !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		rows = append(rows, []fval{fStr(s.Name()), fInt(len(list[s.ID])),
			fStr(groupConcat(list[s.ID])), fI32(s.NIO), fI32(s.NMemory),
			fI32(s.FanIn), fStr(g.at(s))})
	}
	orderBy(rows, dI(1), dI(5))
	return cols, limit(rows, p)
}

func qQ24(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "loops", "returns", "cyclo", "fan_in", "sloc", "at"}
	var rows [][]fval
	for _, s := range g.syms() {
		if s.NLoops <= 0 || s.NReturns != 0 || s.FanIn <= 0 || s.Kind() != "function" {
			continue
		}
		f := g.fileOf(s.ID)
		if f == nil || f.IsTest != 0 {
			continue
		}
		if !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		rows = append(rows, []fval{fStr(s.Name()), fI32(s.NLoops), fI32(s.NReturns),
			fI32(s.Cyclomatic), fI32(s.FanIn), fI32(s.Sloc), fStr(g.at(s))})
	}
	orderBy(rows, dI(1), dI(4), cmpS(0))
	return cols, limit(rows, p)
}

func qQ25(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "returns_value", "fan_in", "cyclo", "sloc", "at"}
	var rows [][]fval
	for _, s := range g.syms() {
		if g.rv(s).RetVal != 1 || s.FanIn <= 5 {
			continue
		}
		f := g.fileOf(s.ID)
		if f == nil || f.IsTest != 0 {
			continue
		}
		if !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		rows = append(rows, []fval{fStr(s.Name()), fI32(g.rv(s).RetVal), fI32(s.FanIn),
			fI32(s.Cyclomatic), fI32(s.Sloc), fStr(g.at(s))})
	}
	orderBy(rows, dI(2))
	return cols, limit(rows, p)
}

func qQ26(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "uses", "params", "body_len", "multiline", "at"}
	bySym := map[int32]*Macro{}
	for i := range g.Macros {
		bySym[g.Macros[i].SymbolID] = &g.Macros[i]
	}
	var rows [][]fval
	for _, s := range g.syms() {
		m, ok := bySym[s.ID]
		if !ok || m.IsFunctionlike != 1 || m.NUses <= 3 {
			continue
		}
		if !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		rows = append(rows, []fval{fStr(s.Name()), fI32(m.NUses), fI32(m.NParams),
			fI32(m.BodyLen), fI32(m.IsMultiline), fStr(g.at(s))})
	}
	orderBy(rows, dI(1))
	return cols, limit(rows, p)
}

func qQ27(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "fnptr_calls", "dyn_calls", "direct_calls",
		"fan_in", "sloc", "at"}
	var rows [][]fval
	for _, s := range g.syms() {
		if g.rv(s).NFnptrCalls+s.NDynamicCalls <= 0 || s.Kind() != "function" {
			continue
		}
		f := g.fileOf(s.ID)
		if f == nil || f.IsTest != 0 {
			continue
		}
		if !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		direct := maxI(0, s.NCalls-g.rv(s).NFnptrCalls-s.NDynamicCalls)
		rows = append(rows, []fval{fStr(s.Name()), fI32(g.rv(s).NFnptrCalls),
			fI32(s.NDynamicCalls), fI32(direct), fI32(s.FanIn), fI32(s.Sloc),
			fStr(g.at(s))})
	}
	orderBy(rows, dSum(1, 2), cmpS(0))
	return cols, limit(rows, p)
}

func qQ28(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"path", "user_headers", "sys_headers", "pct_user", "sloc"}
	type agg struct{ user, sys int32 }
	byFile := map[int32]*agg{}
	var order []int32
	for _, im := range g.Imports {
		if im.Kind() != "include" {
			continue
		}
		a := byFile[im.FileID]
		if a == nil {
			a = &agg{}
			byFile[im.FileID] = a
			order = append(order, im.FileID)
		}
		if im.IsRelative == 1 {
			a.user++
		} else {
			a.sys++
		}
	}
	var rows [][]fval
	for _, fid := range order {
		f := g.fileOf2(fid)
		if f == nil || !likeMatch(g.modName(f.ModuleID), p.mod) {
			continue
		}
		a := byFile[fid]
		rows = append(rows, []fval{fStr(f.Path()), fI32(a.user), fI32(a.sys),
			fI32(pct(int64(a.user), int64(a.user+a.sys))), fI32(f.Sloc)})
	}
	orderBy(rows, cmpI(3), dSum(1, 2))
	return cols, limit(rows, p)
}

func qQ29(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"fn_a", "fn_b", "at_a", "at_b", "a_calls_b", "b_calls_a"}
	type ek struct{ c, d int32 }
	n := map[ek]int32{}
	for _, e := range g.Edges {
		n[ek{e.CallerID, e.CalleeID}] = e.NCalls
	}
	var rows [][]fval
	for i := range g.Edges {
		a := &g.Edges[i]
		if a.CallerID >= a.CalleeID {
			continue
		}
		rev := n[ek{a.CalleeID, a.CallerID}]
		if rev == 0 {
			continue
		}
		sa := g.sym(a.CallerID)
		sb := g.sym(a.CalleeID)
		if sa == nil || sb == nil {
			continue
		}
		if !likeMatch(g.modName(sa.ModuleID), p.mod) {
			continue
		}
		rows = append(rows, []fval{fStr(sa.Name()), fStr(sb.Name()), fStr(g.at(sa)),
			fStr(g.at(sb)), fI32(a.NCalls), fI32(rev)})
	}
	orderBy(rows, dSum(4, 5))
	return cols, limit(rows, p)
}

func qQ30(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"path", "name", "type", "line", "has_init", "is_volatile",
		"is_atomic", "ptr_depth"}
	var rows [][]fval
	for i := range g.Globals {
		gl := &g.Globals[i]
		if gl.IsStatic != 0 || gl.IsConst != 0 {
			continue
		}
		if !likeMatch(g.modName(gl.ModuleID), p.mod) {
			continue
		}
		f := g.fileOf2(gl.FileID)
		if f == nil {
			continue
		}
		rows = append(rows, []fval{fStr(f.Path()), fStr(gl.Name()), fStr(gl.Type()),
			fI32(gl.Line), fI32(gl.HasInit), fI32(gl.IsVolatile),
			fI32(gl.IsAtomic), fI32(gl.PtrDepth)})
	}
	orderBy(rows, dI(6), dI(5), cmpS(0), cmpI(3))
	return cols, limit(rows, p)
}

func (g *Graph) fileOf2(id int32) *File {
	if id < 1 || int(id) > len(g.Files) {
		return nil
	}
	return &g.Files[id-1]
}

func qQ31(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"header", "sloc", "n_syms", "n_fns", "inbound_calls",
		"included_by"}
	nFns := map[int32]int32{}
	nSyms := map[int32]int32{}
	for _, s := range g.syms() {
		nSyms[s.FileID]++
		if s.Kind() == "function" {
			nFns[s.FileID]++
		}
	}
	inbound := map[int32]int32{}
	for _, e := range g.Edges {
		if s := g.sym(e.CalleeID); s != nil {
			inbound[s.FileID]++
		}
	}
	includedBy := map[int32]int32{}
	seenInc := map[[2]int32]bool{}
	for _, im := range g.Imports {
		if im.Kind() != "include" || !im.HasTargetID {
			continue
		}
		k := [2]int32{im.TargetID, im.FileID}
		if !seenInc[k] {
			seenInc[k] = true
			includedBy[im.TargetID]++
		}
	}
	var rows [][]fval
	for i := range g.Files {
		f := &g.Files[i]

		if includedBy[f.ID] == 0 || f.NSymbols <= 0 || nFns[f.ID] <= 0 ||
			inbound[f.ID] != 0 {
			continue
		}
		if !likeMatch(g.modName(f.ModuleID), p.mod) {
			continue
		}
		rows = append(rows, []fval{fStr(f.Path()), fI32(f.Sloc), fI32(nSyms[f.ID]),
			fI32(nFns[f.ID]), fI32(0), fI32(includedBy[f.ID])})
	}
	orderBy(rows, dI(5), dI(1))
	return cols, limit(rows, p)
}

func qQ32(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "transitive_callers", "fan_in", "n_calls", "sloc", "at"}
	var rows [][]fval
	for _, r := range g.Reach {
		s := g.sym(r.SymbolID)
		if s == nil || s.Kind() != "function" {
			continue
		}
		f := g.fileOf(s.ID)
		if f == nil || f.IsTest != 0 {
			continue
		}
		if !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		rows = append(rows, []fval{fStr(s.Name()), fI32(r.NTransitive),
			fI32(s.FanIn), fI32(s.NCalls), fI32(s.Sloc), fStr(g.at(s))})
	}
	orderBy(rows, dI(1), cmpS(0))
	return cols, limit(rows, p)
}

func qQ33(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "total_size", "tail_pad", "total_pad", "n_lines_64",
		"exact", "n_fields", "n_ptr_fields", "at"}
	nTop := map[int32]int32{}
	nPtr := map[int32]int32{}
	for _, l := range g.Layout {

		if l.Depth == 0 {
			nTop[l.SymbolID]++
		}
		if l.PtrDepth > 0 {
			nPtr[l.SymbolID]++
		}
	}
	var rows [][]fval
	for _, ss := range g.SSize {
		if ss.Exact != 1 || ss.TotalSize < 64 {
			continue
		}
		s := g.sym(ss.SymbolID)
		if s == nil {
			continue
		}
		if !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		rows = append(rows, []fval{fStr(s.Name()), fI32(ss.TotalSize),
			fI32(ss.TailPad), fI32(ss.TotalPad), fI32(ss.NLines64),
			fI32(ss.Exact), fI32(nTop[ss.SymbolID]), fI32(nPtr[ss.SymbolID]),
			fStr(g.at(s))})
	}
	orderBy(rows, dI(1), dI(3))
	return cols, limit(rows, p)
}

func qQ34(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"path", "extern_globals", "extern_calls", "total_calls",
		"pct_external"}
	eg := map[int32]int32{}
	for _, gl := range g.Globals {
		if gl.IsStatic == 0 && gl.IsConst == 0 {
			eg[gl.FileID]++
		}
	}
	ec := map[int32]int32{}
	tot := map[int32]int32{}
	nSym := map[int32]int32{}
	for _, s := range g.syms() {
		if s.Kind() != "function" {
			continue
		}
		ec[s.FileID] += g.rv(s).NExternalCalls
		tot[s.FileID] += s.NCalls
	}
	for i := range g.Symbols {
		nSym[g.Symbols[i].FileID]++
	}
	var rows [][]fval
	for i := range g.Files {
		f := &g.Files[i]
		if nSym[f.ID] == 0 || (ec[f.ID] == 0 && eg[f.ID] == 0) {
			continue
		}
		if !likeMatch(g.modName(f.ModuleID), p.mod) {
			continue
		}
		var pv fval = fNull()
		if tot[f.ID] != 0 {
			pv = fI32(pct(int64(ec[f.ID]), int64(tot[f.ID])))
		}
		rows = append(rows, []fval{fStr(f.Path()), fI32(eg[f.ID]), fI32(ec[f.ID]),
			fI32(tot[f.ID]), pv})
	}
	orderBy(rows, dI(2))
	return cols, limit(rows, p)
}

func qQ35(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "n_sigs", "n_files", "where_defined"}
	type grp struct {
		sigs  map[string]bool
		files map[int32]bool
		paths []string
		order []string
	}
	m := map[string]*grp{}
	var names []string
	for _, s := range g.symsName() {
		if s.Kind() != "function" || !s.HasSignature || s.Signature() == "" {
			continue
		}
		f := g.fileOf(s.ID)
		if f == nil || f.IsGenerated != 0 {
			continue
		}
		if !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		gp := m[s.Name()]
		if gp == nil {
			gp = &grp{sigs: map[string]bool{}, files: map[int32]bool{}}
			m[s.Name()] = gp
			names = append(names, s.Name())
		}
		gp.sigs[s.Signature()] = true
		if !gp.files[f.ID] {
			gp.files[f.ID] = true
			gp.paths = append(gp.paths, f.Path())
		}
	}
	var rows [][]fval
	for _, n := range names {
		gp := m[n]
		if len(gp.sigs) <= 1 {
			continue
		}
		rows = append(rows, []fval{fStr(n), fInt(len(gp.sigs)), fInt(len(gp.files)),
			fStr(groupConcat(gp.paths))})
	}
	orderBy(rows, dI(2), dI(1), cmpS(0))
	return cols, limit(rows, p)
}

func qQ36(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "path", "line_start", "fan_in", "n_caller_files"}
	callerFiles := map[int32]map[int32]bool{}
	for _, e := range g.Edges {
		cs := g.sym(e.CallerID)
		if cs == nil {
			continue
		}
		m := callerFiles[e.CalleeID]
		if m == nil {
			m = map[int32]bool{}
			callerFiles[e.CalleeID] = m
		}
		m[cs.FileID] = true
	}
	var rows [][]fval
	for _, s := range g.syms() {
		if s.Kind() != "function" || s.IsStatic != 0 {
			continue
		}
		f := g.fileOf(s.ID)
		if f == nil || f.IsGenerated != 0 {
			continue
		}
		if !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		n := int32(len(callerFiles[s.ID]))
		if s.FanIn <= 0 || n > 1 {
			continue
		}
		rows = append(rows, []fval{fStr(s.Name()), fStr(f.Path()),
			fI32(s.LineStart), fI32(s.FanIn), fI32(n)})
	}
	orderBy(rows, dI(3), cmpS(0))
	return cols, limit(rows, p)
}

var riskyApis = []string{"system", "popen", "execve", "execl", "execlp",
	"execvp", "execv", "fork", "posix_spawn", "posix_spawnp", "vfork", "wordexp",
	"dlopen", "dlmopen", "mktemp", "tmpnam", "tempnam", "access"}

func qQ37(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"path", "caller", "api", "category", "sites", "first_line",
		"fan_in"}
	var rows [][]fval
	for _, h := range g.Hazards {
		if !containsStr(riskyApis, h.Pattern()) {
			continue
		}
		s := g.sym(h.SymbolID)
		if s == nil {
			continue
		}
		f := g.fileOf(s.ID)
		if f == nil || f.IsGenerated != 0 {
			continue
		}
		if !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		rows = append(rows, []fval{fStr(f.Path()), fStr(s.Name()), fStr(h.Pattern()),
			fStr(h.Category()), fI32(h.N), fI32(h.FirstLine), fI32(s.FanIn)})
	}
	orderBy(rows, dI(6), dI(4))
	return cols, limit(rows, p)
}

func qQ38(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "candidate", "line", "at"}
	var rows [][]fval
	for _, sc := range g.Secrets {
		s := g.sym(sc.SymbolID)
		if s == nil {
			continue
		}
		f := g.fileOf(s.ID)
		if f == nil || f.IsTest != 0 || f.IsGenerated != 0 {
			continue
		}
		if !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		v := sc.Value()
		if strings.HasPrefix(v, "/") || strings.Contains(v, "|") ||
			strings.Contains(v, "%") {
			continue
		}
		rows = append(rows, []fval{fStr(s.Name()), fStr(v), fI32(sc.Line),
			fStr(f.Path() + ":" + strconv.Itoa(int(sc.Line)))})
	}
	orderBy(rows, dLenStr(1))
	return cols, limit(rows, p)
}

func qQ39(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"header", "partner", "length", "members"}
	var rows [][]fval
	byPath := map[string]int32{}
	for i := range g.Files {
		byPath[g.Files[i].Path()] = g.Files[i].ID
	}
	for _, c := range g.Cycles {
		fid, ok := byPath[c.APath()]
		if !ok {
			rows = append(rows, []fval{fStr(c.APath()), fStr(c.BPath()),
				fI32(c.Length), fStr(c.Members())})
			continue
		}
		f := &g.Files[fid-1]
		if !likeMatch(g.modName(f.ModuleID), p.mod) {
			continue
		}
		rows = append(rows, []fval{fStr(c.APath()), fStr(c.BPath()), fI32(c.Length),
			fStr(c.Members())})
	}
	orderBy(rows, cmpI(2), cmpS(0))
	return cols, limit(rows, p)
}

func qQ40(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "const_casts", "casts_total", "fan_in", "at"}
	var rows [][]fval
	for _, s := range g.syms() {
		if g.rv(s).NConstCast <= 0 {
			continue
		}
		f := g.fileOf(s.ID)
		if f == nil || f.IsTest != 0 {
			continue
		}
		if !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		rows = append(rows, []fval{fStr(s.Name()), fI32(g.rv(s).NConstCast),
			fI32(s.NCast), fI32(s.FanIn), fStr(g.at(s))})
	}
	orderBy(rows, dI(1), dI(3))
	return cols, limit(rows, p)
}

func qQ41(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "path", "line_start", "sloc", "addr_taken"}
	body := map[[2]any]int32{}
	byName := map[string]int32{}
	for _, a := range g.Addr {
		if !a.HasSym {
			continue
		}
		body[[2]any{a.Name(), a.FileID}]++
		byName[a.Name()] += 1
	}
	var rows [][]fval
	for _, s := range g.syms() {
		if s.Kind() != "function" || s.FanIn != 0 || s.IsTest != 0 {
			continue
		}
		f := g.fileOf(s.ID)
		if f == nil || !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		n := body[[2]any{s.Name(), f.ID}]
		if s.IsStatic == 0 {
			n = byName[s.Name()]
		}
		if n == 0 {
			continue
		}
		rows = append(rows, []fval{fStr(s.Name()), fStr(f.Path()), fI32(s.LineStart),
			fI32(s.Sloc), fI32(n)})
	}
	orderBy(rows, dI(4), dI(3), cmpS(0))
	return cols, limit(rows, p)
}

func qQ42(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "path", "line", "defined_count"}
	byName := map[string][]int32{}
	for _, s := range g.syms() {
		if s.Kind() != "function" {
			continue
		}
		byName[s.Name()] = append(byName[s.Name()], s.ID)
	}
	var rows [][]fval
	for _, d := range g.Decls {
		cnt := int32(0)
		for _, sid := range byName[d.Name()] {

			if sy := g.sym(sid); sy.IsStatic == 0 || sy.FileID == d.FileID {
				cnt++
			}
		}
		if cnt != 0 {
			continue
		}
		f := g.fileOf2(d.FileID)
		if f == nil || f.IsGenerated != 0 {
			continue
		}
		if !likeMatch(g.modName(f.ModuleID), p.mod) {
			continue
		}
		rows = append(rows, []fval{fStr(d.Name()), fStr(f.Path()), fI32(d.Line),
			fI32(0)})
	}
	orderBy(rows, cmpS(0), cmpS(1))
	return cols, limit(rows, p)
}

func qQ43(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "pairs", "io_calls", "fan_in", "at"}
	var rows [][]fval
	for _, s := range g.syms() {
		if g.rv(s).NToctou <= 0 {
			continue
		}
		f := g.fileOf(s.ID)
		if f == nil || f.IsTest != 0 {
			continue
		}
		if !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		rows = append(rows, []fval{fStr(s.Name()), fI32(g.rv(s).NToctou), fI32(s.NIO),
			fI32(s.FanIn), fStr(g.at(s))})
	}
	orderBy(rows, dI(1), dI(3))
	return cols, limit(rows, p)
}

func qQ44(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "acquires", "releases", "imbalance", "return_paths",
		"gotos", "fan_in", "cyclo", "at"}
	var rows [][]fval
	for _, s := range g.syms() {
		if s.Kind() != "function" || g.rv(s).NLockAcquire <= g.rv(s).NLockRelease {
			continue
		}
		f := g.fileOf(s.ID)
		if f == nil || f.IsTest != 0 {
			continue
		}
		if !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		rows = append(rows, []fval{fStr(s.Name()), fI32(g.rv(s).NLockAcquire),
			fI32(g.rv(s).NLockRelease), fI32(g.rv(s).NLockAcquire - g.rv(s).NLockRelease),
			fI32(s.NReturns), fI32(s.NGotos), fI32(s.FanIn),
			fI32(s.Cyclomatic), fStr(g.at(s))})
	}
	orderBy(rows, dI(3), dI(6), cmpS(0))
	return cols, limit(rows, p)
}

func qQ45(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "acquires", "io_calls", "mem_calls", "cyclo",
		"fan_in", "at"}
	var rows [][]fval
	for _, s := range g.syms() {
		if s.Kind() != "function" || g.rv(s).NLockAcquire <= 0 || s.NIO <= 0 {
			continue
		}
		f := g.fileOf(s.ID)
		if f == nil || f.IsTest != 0 {
			continue
		}
		if !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		rows = append(rows, []fval{fStr(s.Name()), fI32(g.rv(s).NLockAcquire), fI32(s.NIO),
			fI32(s.NMemory), fI32(s.Cyclomatic), fI32(s.FanIn), fStr(g.at(s))})
	}
	orderBy(rows, dI(2), dI(1), cmpS(0))
	return cols, limit(rows, p)
}

func qQ46(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"op", "dst", "src", "size_arg", "size_buf", "caller",
		"fan_in", "at"}
	want := []string{"memcpy", "memmove", "strncpy", "strncat", "snprintf"}
	var rows [][]fval
	for _, m := range g.Memops {
		if !containsStr(want, m.Fn()) || m.SizeBuf() == "" || m.SizeBuf() == m.DstTail() {
			continue
		}
		if strings.Contains(m.Src(), m.SizeBuf()) {
			continue
		}
		if strings.Contains(m.SizeArg(), "*") || strings.Contains(m.SizeArg(), "+") {
			continue
		}
		s := g.sym(m.SymbolID)
		if s == nil {
			continue
		}
		f := g.fileOf(s.ID)
		if f == nil || f.IsTest != 0 {
			continue
		}
		if !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		rows = append(rows, []fval{fStr(m.Fn()), fStr(m.Dst()), fStr(m.Src()),
			fStr(m.SizeArg()), fStr(m.SizeBuf()), fStr(s.Name()), fI32(s.FanIn),
			fStr(f.Path() + ":" + strconv.Itoa(int(m.Line)))})
	}
	orderBy(rows, dI(6), cmpLine(7), cmpS(0))
	return cols, limit(rows, p)
}

func qQ47(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"fn", "size_expr", "caller", "fan_in", "alloc_sites", "at"}
	var rows [][]fval
	for _, a := range g.Allocs {
		if strings.Contains(a.SizeExpr(), "sizeof") || a.SizeExpr() == "" {
			continue
		}
		s := g.sym(a.SymbolID)
		if s == nil {
			continue
		}
		f := g.fileOf(s.ID)
		if f == nil || f.IsTest != 0 {
			continue
		}
		if !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		rows = append(rows, []fval{fStr(a.Fn()), fStr(a.SizeExpr()), fStr(s.Name()),
			fI32(s.FanIn), fI32(g.rv(s).NAllocsite),
			fStr(f.Path() + ":" + strconv.Itoa(int(a.Line)))})
	}
	orderBy(rows, dI(3), cmpLine(5), cmpS(0))
	return cols, limit(rows, p)
}

func qQ48(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "writes", "module", "mutable_globals_here", "fan_in",
		"cyclo", "rank_in_module", "at"}
	mutable := map[int32]int32{}
	for _, gl := range g.Globals {
		if gl.IsConst == 0 {
			mutable[gl.FileID]++
		}
	}
	type w struct {
		id, mod int32
		writes  int32
	}

	var ws []w
	for _, s := range g.syms() {
		if s.Kind() != "function" || g.rv(s).NGlobalWrite <= 0 {
			continue
		}
		f := g.fileOf(s.ID)
		if f == nil || f.IsTest != 0 {
			continue
		}
		if !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		ws = append(ws, w{s.ID, s.ModuleID, g.rv(s).NGlobalWrite})
	}
	type wrow struct {
		id, mod, writes, fan int32
		name                 string
	}
	wr := make([]wrow, 0, len(ws))
	for _, x := range ws {
		fan, nm := int32(0), ""
		if sy := g.sym(x.id); sy != nil {
			fan, nm = sy.FanIn, sy.Name()
		}
		wr = append(wr, wrow{x.id, x.mod, x.writes, fan, nm})
	}
	sort.SliceStable(wr, func(a, b int) bool {
		if wr[a].writes != wr[b].writes {
			return wr[a].writes > wr[b].writes
		}
		if wr[a].name != wr[b].name {
			return wr[a].name > wr[b].name
		}
		return wr[a].id < wr[b].id
	})

	rank := map[int32]int32{}
	for mi := range g.Modules {
		part := make([]wrow, 0, 8)
		for _, x := range wr {
			if x.mod == g.Modules[mi].ID {
				part = append(part, x)
			}
		}
		sort.SliceStable(part, func(a, b int) bool {
			if part[a].writes != part[b].writes {
				return part[a].writes > part[b].writes
			}
			return part[a].fan > part[b].fan
		})
		n := int32(0)
		var pw, pf int32
		first := true
		for _, x := range part {
			if first || x.writes != pw || x.fan != pf {
				n++
				pw, pf, first = x.writes, x.fan, false
			}
			rank[x.id] = n
		}
	}
	var rows [][]fval
	for _, x := range wr {
		s := g.sym(x.id)
		if s == nil {
			continue
		}
		f := g.fileOf(s.ID)
		if f == nil {
			continue
		}
		rows = append(rows, []fval{fStr(s.Name()), fI32(x.writes),
			fStr(g.modName(s.ModuleID)), fI32(mutable[f.ID]), fI32(s.FanIn),
			fI32(s.Cyclomatic), fI32(rank[x.id]), fStr(g.at(s))})
	}
	orderBy(rows, dI(1), dI(4))
	return cols, limit(rows, p)
}

type qw struct {
	id, mod, writes, fan int32
}

func qQ49(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "narrow_casts", "arith_ops", "shifts", "io_calls",
		"fan_in", "at"}
	var rows [][]fval
	for _, s := range g.syms() {
		if s.Kind() != "function" || g.rv(s).NNarrowCast <= 0 {
			continue
		}
		if s.NArith <= 0 && s.NShift <= 0 && s.NIO <= 0 {
			continue
		}
		f := g.fileOf(s.ID)
		if f == nil || f.IsTest != 0 {
			continue
		}
		if !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		rows = append(rows, []fval{fStr(s.Name()), fI32(g.rv(s).NNarrowCast),
			fI32(s.NArith), fI32(s.NShift), fI32(s.NIO), fI32(s.FanIn),
			fStr(g.at(s))})
	}
	orderBy(rows, dI(1), dI(5), cmpS(0))
	return cols, limit(rows, p)
}

func qQ50(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "sign_cmps", "total_cmps", "n_params", "fan_in", "at"}
	var rows [][]fval
	for _, s := range g.syms() {
		if s.Kind() != "function" || g.rv(s).NSignCmp <= 0 {
			continue
		}
		f := g.fileOf(s.ID)
		if f == nil || f.IsTest != 0 {
			continue
		}
		if !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		rows = append(rows, []fval{fStr(s.Name()), fI32(g.rv(s).NSignCmp), fI32(s.NCmp),
			fI32(s.NParams), fI32(s.FanIn), fStr(g.at(s))})
	}
	orderBy(rows, dI(1), dI(4), cmpS(0))
	return cols, limit(rows, p)
}

func qQ51(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "fmt_calls", "stdio_calls", "fan_in", "via", "at"}
	want := []string{"vsnprintf", "vsprintf", "vfprintf", "vprintf", "syslog"}
	bySym := map[int32][]string{}
	for _, h := range g.Hazards {
		if containsStr(want, h.Pattern()) && !containsStr(bySym[h.SymbolID], h.Pattern()) {
			bySym[h.SymbolID] = append(bySym[h.SymbolID], h.Pattern())
		}
	}
	var rows [][]fval
	for _, s := range g.syms() {
		if s.Kind() != "function" || s.IsVariadic != 1 || g.rv(s).NVariadicFmt <= 0 {
			continue
		}
		f := g.fileOf(s.ID)
		if f == nil || f.IsTest != 0 {
			continue
		}
		if !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		var via fval = fNull()
		if l := bySym[s.ID]; len(l) > 0 {
			via = fStr(groupConcat(l))
		}
		rows = append(rows, []fval{fStr(s.Name()), fI32(g.rv(s).NVariadicFmt),
			fI32(s.NStdio), fI32(s.FanIn), via, fStr(g.at(s))})
	}
	orderBy(rows, dI(3), dI(1), cmpS(0))
	return cols, limit(rows, p)
}

func qQ52(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "table_refs", "plain_refs", "tables_in", "sloc",
		"cyclo", "at"}
	type ref struct {
		file int32
		kind string
	}
	refs := map[string][]ref{}

	bodyRefFiles := map[string][]int32{}
	for _, a := range g.Addr {
		if a.HasSym {
			bodyRefFiles[a.Name()] = append(bodyRefFiles[a.Name()], a.FileID)
			continue
		}
		refs[a.Name()] = append(refs[a.Name()], ref{a.FileID, a.Kind()})
	}
	vetoed := func(name string, fid, isStatic int32) bool {
		files := bodyRefFiles[name]
		if isStatic == 0 {
			return len(files) > 0
		}
		return slices.Contains(files, fid)
	}
	var rows [][]fval
	for _, s := range g.syms() {
		if s.Kind() != "function" || s.FanIn != 0 ||
			vetoed(s.Name(), s.FileID, s.IsStatic) {
			continue
		}
		rs := refs[s.Name()]
		n := int32(0)
		plain := int32(0)
		var names []string
		for _, r := range rs {
			if s.IsStatic == 0 || r.file == s.FileID {
				n++
				if r.kind == "ref" {
					plain++
				}
				if f := g.fileOf2(r.file); f != nil {
					names = append(names, f.Basename())
				}
			}
		}
		if n == 0 {
			continue
		}
		f := g.fileOf(s.ID)
		if f == nil || f.IsTest != 0 {
			continue
		}
		if !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		rows = append(rows, []fval{fStr(s.Name()), fI32(n), fI32(plain),
			fStr(groupConcat(distinctStrings(names))), fI32(s.Sloc),
			fI32(s.Cyclomatic), fStr(g.at(s))})
	}
	orderBy(rows, dI(1), dI(4), cmpS(0))
	return cols, limit(rows, p)
}

func qQ53(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "allocs", "frees", "return_paths", "branches",
		"gotos", "cyclo", "fan_in", "at"}
	var rows [][]fval
	for _, s := range g.syms() {
		if s.Kind() != "function" || g.rv(s).NAllocsite <= 0 || g.rv(s).NFree <= 0 ||
			s.NReturns < 3 || s.NReturns <= g.rv(s).NAllocsite {
			continue
		}
		f := g.fileOf(s.ID)
		if f == nil || f.IsTest != 0 {
			continue
		}
		if !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		rows = append(rows, []fval{fStr(s.Name()), fI32(g.rv(s).NAllocsite),
			fI32(g.rv(s).NFree), fI32(s.NReturns), fI32(s.NBranches), fI32(s.NGotos),
			fI32(s.Cyclomatic), fI32(s.FanIn), fStr(g.at(s))})
	}
	orderBy(rows, dI(3), dI(1), cmpS(0))
	return cols, limit(rows, p)
}

func qQ54(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "self_realloc", "allocs", "frees", "returns_",
		"fan_in", "at"}
	var rows [][]fval
	for _, s := range g.syms() {
		if g.rv(s).NReallocSelf <= 0 || !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		rows = append(rows, []fval{fStr(s.Name()), fI32(g.rv(s).NReallocSelf),
			fI32(s.NAlloc), fI32(g.rv(s).NFree), fI32(s.NReturns), fI32(s.FanIn),
			fStr(g.at(s))})
	}
	orderBy(rows, dI(1), dI(5))
	return cols, limit(rows, p)
}

func qQ55(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "fn", "size", "allocs", "fan_in", "at"}
	var rows [][]fval
	for _, a := range g.Allocs {
		if !strings.Contains(a.SizeExpr(), "strlen") ||
			strings.Contains(a.SizeExpr(), "+") {
			continue
		}
		s := g.sym(a.SymbolID)
		if s == nil || !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		f := g.fileOf(s.ID)
		if f == nil {
			continue
		}
		rows = append(rows, []fval{fStr(s.Name()), fStr(a.Fn()), fStr(a.SizeExpr()),
			fI32(s.NAlloc), fI32(s.FanIn),
			fStr(f.Path() + ":" + strconv.Itoa(int(a.Line)))})
	}
	orderBy(rows, dI(4), cmpS(0))
	return cols, limit(rows, p)
}

func qQ56(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "opens", "closes", "returns_", "gotos", "cyclo",
		"fan_in", "at"}
	openFns := []string{"open", "openat", "creat", "fopen", "fdopen", "opendir",
		"socket", "accept", "accept4", "mmap", "popen", "tmpfile"}
	closeFns := []string{"close", "fclose", "closedir", "munmap", "pclose", "shutdown"}
	o := map[int32]int32{}
	c := map[int32]int32{}
	for _, h := range g.Hazards {
		if h.Category() != "io" && h.Category() != "stdio" {
			continue
		}
		if containsStr(openFns, h.Pattern()) {
			o[h.SymbolID] += h.N
		}
		if containsStr(closeFns, h.Pattern()) {
			c[h.SymbolID] += h.N
		}
	}
	var rows [][]fval
	sids := make([]int32, 0, len(o))
	for sid := range o {
		sids = append(sids, sid)
	}
	slices.Sort(sids)
	for _, sid := range sids {
		if o[sid] <= c[sid] {
			continue
		}
		s := g.sym(sid)
		if s == nil || !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		rows = append(rows, []fval{fStr(s.Name()), fI32(o[sid]), fI32(c[sid]),
			fI32(s.NReturns), fI32(s.NGotos), fI32(s.Cyclomatic),
			fI32(s.FanIn), fStr(g.at(s))})
	}
	orderBy(rows, dWeighted([][3]int32{{1, 1}, {-1, 2}}), dI(6))
	return cols, limit(rows, p)
}

func qQ57(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "allocs", "null_checks", "returns_", "cyclo",
		"fan_in", "at"}
	var rows [][]fval
	for _, s := range g.syms() {
		if s.Kind() != "function" || s.NAlloc <= 0 || s.NNullCheck != 0 {
			continue
		}
		if !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		rows = append(rows, []fval{fStr(s.Name()), fI32(s.NAlloc),
			fI32(s.NNullCheck), fI32(s.NReturns), fI32(s.Cyclomatic),
			fI32(s.FanIn), fStr(g.at(s))})
	}
	orderBy(rows, dI(1), dI(5), cmpS(0))
	return cols, limit(rows, p)
}

func qQ58(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "vlas", "io", "mem", "int_", "nest", "fan_in",
		"rec", "at"}
	var rows [][]fval
	for _, s := range g.syms() {
		if g.rv(s).NVla <= 0 || (s.NIO <= 0 && s.NMemory <= 0 && s.IsRecursive != 1) {
			continue
		}
		if !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		rows = append(rows, []fval{fStr(s.Name()), fI32(g.rv(s).NVla), fI32(s.NIO),
			fI32(s.NMemory), fI32(s.NInteger), fI32(s.MaxNesting),
			fI32(s.FanIn), fI32(s.IsRecursive), fStr(g.at(s))})
	}
	orderBy(rows, dI(1), dI(2), dI(6))
	return cols, limit(rows, p)
}

func qQ59(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "uses", "frees", "sloc", "returns_", "fan_in", "at"}
	var rows [][]fval
	for _, s := range g.syms() {
		if g.rv(s).NFreeThenUse <= 0 || !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		rows = append(rows, []fval{fStr(s.Name()), fI32(g.rv(s).NFreeThenUse),
			fI32(g.rv(s).NFree), fI32(s.Sloc), fI32(s.NReturns), fI32(s.FanIn),
			fStr(g.at(s))})
	}
	orderBy(rows, dI(1), dI(5))
	return cols, limit(rows, p)
}

func qQ60(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "weak_rand", "io", "exec", "fan_in", "exported", "at"}
	var rows [][]fval
	for _, s := range g.syms() {
		if g.rv(s).NWeakRandom <= 0 || !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		rows = append(rows, []fval{fStr(s.Name()), fI32(g.rv(s).NWeakRandom),
			fI32(s.NIO), fI32(s.NExec), fI32(s.FanIn), fI32(s.IsPublic),
			fStr(g.at(s))})
	}
	orderBy(rows, dI(1), dI(4))
	return cols, limit(rows, p)
}

func qQ61(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "var_shifts", "casts", "io", "int_", "cyclo",
		"fan_in", "at"}
	var rows [][]fval
	for _, s := range g.symsName() {
		if g.rv(s).NShiftVar <= 0 || !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		rows = append(rows, []fval{fStr(s.Name()), fI32(g.rv(s).NShiftVar), fI32(s.NCast),
			fI32(s.NIO), fI32(s.NInteger), fI32(s.Cyclomatic), fI32(s.FanIn),
			fStr(g.at(s))})
	}
	orderBy(rows, dI(1), dI(3), dI(6))
	return cols, limit(rows, p)
}

func qQ62(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "errno_reads", "fallible_calls", "returns_", "cyclo",
		"fan_in", "at"}
	fallible := map[int32]int32{}
	for _, h := range g.Hazards {
		switch h.Category() {
		case "io", "stdio", "alloc", "memory":
			fallible[h.SymbolID] += h.N
		}
	}
	var rows [][]fval
	for _, s := range g.symsName() {
		if s.Kind() != "function" || g.rv(s).NErrno <= 0 {
			continue
		}
		f := g.fileOf(s.ID)
		if f == nil || f.IsTest != 0 {
			continue
		}
		if !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		rows = append(rows, []fval{fStr(s.Name()), fI32(g.rv(s).NErrno),
			fI32(fallible[s.ID]), fI32(s.NReturns), fI32(s.Cyclomatic),
			fI32(s.FanIn), fStr(g.at(s))})
	}
	orderBy(rows, dI(1), dI(2))
	return cols, limit(rows, p)
}

func qQ63(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "env_reads", "mem", "exec", "io", "fan_in", "at"}
	var rows [][]fval
	for _, s := range g.syms() {
		if g.rv(s).NGetenv <= 0 || !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		rows = append(rows, []fval{fStr(s.Name()), fI32(g.rv(s).NGetenv), fI32(s.NMemory),
			fI32(s.NExec), fI32(s.NIO), fI32(s.FanIn), fStr(g.at(s))})
	}
	orderBy(rows, dI(1), dI(3), dI(5))
	return cols, limit(rows, p)
}

func qQ64(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "bad_asserts", "sloc", "calls", "fan_in",
		"in_test_file", "at"}
	var rows [][]fval
	for _, s := range g.syms() {
		if g.rv(s).NAssertSide <= 0 {
			continue
		}
		f := g.fileOf(s.ID)
		if f == nil || f.IsTest != 0 {
			continue
		}
		if !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		rows = append(rows, []fval{fStr(s.Name()), fI32(g.rv(s).NAssertSide),
			fI32(s.Sloc), fI32(s.NCalls), fI32(s.FanIn), fI32(f.IsTest),
			fStr(g.at(s))})
	}
	orderBy(rows, dI(1), dI(4))
	return cols, limit(rows, p)
}

func qQ65(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"lock_a", "lock_b", "a_first_fns", "b_first_fns", "a_first",
		"b_first"}
	type pair struct{ lo, hi string }
	byPair := map[pair]*lockPair{}
	per := map[int32][]int32{}
	for i, l := range g.Locks {
		per[l.SymbolID] = append(per[l.SymbolID], int32(i))
	}
	sids := make([]int32, 0, len(per))
	for sid := range per {
		sids = append(sids, sid)
	}
	slices.Sort(sids)
	for _, sid := range sids {
		idxs := per[sid]
		for _, a := range idxs {
			for _, b := range idxs {
				if g.Locks[a].Name() == g.Locks[b].Name() ||
					g.Locks[a].Line >= g.Locks[b].Line {
					continue
				}
				lo, hi := g.Locks[a].Name(), g.Locks[b].Name()
				dirFirst := 0
				if hi < lo {
					lo, hi = hi, lo
					dirFirst = 1
				}
				k := pair{lo, hi}
				lp := byPair[k]
				if lp == nil {
					lp = newLockPair()
					byPair[k] = lp
				}
				nm := ""
				if s := g.sym(sid); s != nil {
					nm = s.Name()
				}
				if dirFirst == 0 {
					lp.aFns[sid] = true
					lp.aNames = appendDistinct(lp.aNames, nm)
				} else {
					lp.bFns[sid] = true
					lp.bNames = appendDistinct(lp.bNames, nm)
				}
			}
		}
	}
	keys := make([]pair, 0, len(byPair))
	for k := range byPair {
		keys = append(keys, k)
	}
	sort.Slice(keys, func(i, j int) bool {
		if keys[i].lo != keys[j].lo {
			return keys[i].lo < keys[j].lo
		}
		return keys[i].hi < keys[j].hi
	})
	var rows [][]fval
	for _, k := range keys {
		lp := byPair[k]
		af, bf := int32(len(lp.aFns)), int32(len(lp.bFns))
		if af == 0 || bf == 0 {
			continue
		}
		modOK := false
		for sid := range lp.aFns {
			if s := g.sym(sid); s != nil && likeMatch(g.modName(s.ModuleID), p.mod) {
				modOK = true
			}
		}
		for sid := range lp.bFns {
			if s := g.sym(sid); s != nil && likeMatch(g.modName(s.ModuleID), p.mod) {
				modOK = true
			}
		}
		if !modOK {
			continue
		}
		rows = append(rows, []fval{fStr(k.lo), fStr(k.hi), fI32(af), fI32(bf),
			fStr(groupConcat(lp.aNames)), fStr(groupConcat(lp.bNames))})
	}
	orderBy(rows, dSum(2, 3), dI(2))
	return cols, limit(rows, p)
}

type lockPair struct {
	aFns, bFns     map[int32]bool
	aNames, bNames []string
}

func newLockPair() *lockPair {
	return &lockPair{aFns: map[int32]bool{}, bFns: map[int32]bool{}}
}

func appendDistinct(l []string, s string) []string {
	if !containsStr(l, s) {
		return append(l, s)
	}
	return l
}

func qQ66(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"struct_name", "sharing_fields", "cache_line", "first_off",
		"last_off", "size", "pad", "conc_fns_in_module", "at"}
	modc := map[int32]int32{}
	for i := range g.Symbols {
		if g.Symbols[i].NConcurrency > 0 {
			modc[g.Symbols[i].ModuleID]++
		}
	}
	type grp struct {
		n, lo, hi int32
	}
	byKey := map[int64]*grp{}
	for _, l := range g.Layout {
		if l.InUnion != 0 || l.Depth != 0 || l.ByteOff < 0 || l.Exact != 1 {
			continue
		}
		k := int64(l.SymbolID)<<32 | int64(l.ByteOff/64)
		e := byKey[k]
		if e == nil {
			e = &grp{lo: l.ByteOff, hi: l.ByteOff}
			byKey[k] = e
		}
		e.n++
		if l.ByteOff < e.lo {
			e.lo = l.ByteOff
		}
		if l.ByteOff > e.hi {
			e.hi = l.ByteOff
		}
	}
	size := map[int32]int32{}
	pad := map[int32]int32{}
	for _, ss := range g.SSize {
		size[ss.SymbolID] = ss.TotalSize
		pad[ss.SymbolID] = ss.TotalPad
	}
	var keys []int64
	for k, v := range byKey {
		if v.n >= 2 {
			keys = append(keys, k)
		}
	}
	slices.Sort(keys)
	var rows [][]fval
	for _, k := range keys {
		sid := int32(k >> 32)
		s := g.sym(sid)
		if s == nil || !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		e := byKey[k]
		rows = append(rows, []fval{fStr(s.Name()), fI32(e.n), fI32(int32(k & 0xffffffff)),
			fI32(e.lo), fI32(e.hi), fI32(size[sid]), fI32(pad[sid]),
			fI32(modc[s.ModuleID]), fStr(g.at(s))})
	}
	orderBy(rows, dI(1), dI(7), dI(5))
	return cols, limit(rows, p)
}

func qQ67(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "fn", "dst", "size", "fan_in", "at"}
	var rows [][]fval
	for _, m := range g.Memops {
		if m.Fn() != "strncpy" && m.Fn() != "strncat" {
			continue
		}
		if !strings.Contains(m.SizeArg(), "sizeof") {
			continue
		}
		s := g.sym(m.SymbolID)
		if s == nil || !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		f := g.fileOf(s.ID)
		if f == nil {
			continue
		}
		rows = append(rows, []fval{fStr(s.Name()), fStr(m.Fn()), fStr(m.Dst()),
			fStr(m.SizeArg()), fI32(s.FanIn),
			fStr(f.Path() + ":" + strconv.Itoa(int(m.Line)))})
	}
	orderBy(rows, dI(4), cmpS(0))
	return cols, limit(rows, p)
}

func qQ68(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"struct_name", "size", "pad", "pct_pad", "copied_whole", "at"}
	copied := map[int32]bool{}
	for _, m := range g.Memops {
		if m.Fn() == "memcpy" || m.Fn() == "memmove" || m.Fn() == "memset" {
			copied[m.SymbolID] = true
		}
	}
	var rows [][]fval
	for _, ss := range g.SSize {
		if ss.TotalPad <= 0 || ss.Exact != 1 {
			continue
		}
		s := g.sym(ss.SymbolID)
		if s == nil || !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		cw := int32(0)
		if copied[ss.SymbolID] {
			cw = 1
		}
		rows = append(rows, []fval{fStr(s.Name()), fI32(ss.TotalSize),
			fI32(ss.TotalPad), fI32(pct(int64(ss.TotalPad), int64(ss.TotalSize))),
			fI32(cw), fStr(g.at(s))})
	}
	orderBy(rows, dI(2), dI(4), dI(1))
	return cols, limit(rows, p)
}

func qQ69(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "sloc", "cyclo", "calls", "only_file", "at"}
	taken := map[string]bool{}
	for _, a := range g.Addr {
		taken[a.Name()] = true
	}
	var rows [][]fval
	for _, s := range g.syms() {
		if s.Kind() != "function" || s.IsStatic != 1 || s.FanIn != 0 {
			continue
		}
		if taken[s.Name()] || !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		f := g.fileOf(s.ID)
		if f == nil {
			continue
		}
		rows = append(rows, []fval{fStr(s.Name()), fI32(s.Sloc), fI32(s.Cyclomatic),
			fI32(s.NCalls), fStr(f.Path()), fStr(g.at(s))})
	}
	orderBy(rows, dI(1), dI(2), cmpS(0))
	return cols, limit(rows, p)
}

func qQ70(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "fan_in", "sloc", "external", "at"}
	declared := map[string]bool{}
	for _, d := range g.Decls {
		declared[d.Name()] = true
	}
	var rows [][]fval
	for _, s := range g.syms() {
		if s.Kind() != "function" || s.IsStatic != 0 || s.IsInline != 0 {
			continue
		}
		f := g.fileOf(s.ID)
		if f == nil || f.Ext() != ".c" || declared[s.Name()] {
			continue
		}
		if !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		rows = append(rows, []fval{fStr(s.Name()), fI32(s.FanIn), fI32(s.Sloc),
			fI32(s.IsPublic), fStr(g.at(s))})
	}
	orderBy(rows, dI(1), dI(2), cmpS(0))
	return cols, limit(rows, p)
}

func qQ71(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"path", "sloc", "syms", "includes", "included_by"}
	inc := map[int32]int32{}
	incBy := map[int32]int32{}
	for _, im := range g.Imports {
		inc[im.FileID]++
		if im.HasTargetID {
			incBy[im.TargetID]++
		}
	}
	guarded := map[int32]bool{}
	for _, cb := range g.Cfgs {
		if cb.Directive() == "ifndef" && cb.Line <= 12 {
			guarded[cb.FileID] = true
		}
	}
	var rows [][]fval
	for i := range g.Files {
		f := &g.Files[i]
		if f.Ext() != ".h" || guarded[f.ID] {
			continue
		}
		if !likeMatch(g.modName(f.ModuleID), p.mod) {
			continue
		}
		rows = append(rows, []fval{fStr(f.Path()), fI32(f.Sloc), fI32(f.NSymbols),
			fI32(inc[f.ID]), fI32(incBy[f.ID])})
	}
	orderBy(rows, dI(4), dI(1))
	return cols, limit(rows, p)
}

func qQ72(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"from_module", "to_module", "hops_out", "hops_back",
		"out_edges", "back_edges"}
	medge := map[[2]int32]bool{}
	deg := map[int32]int32{}
	var direct [][2]int32
	for _, e := range g.Edges {
		a, b := g.sym(e.CallerID), g.sym(e.CalleeID)
		if a == nil || b == nil || a.ModuleID == 0 || b.ModuleID == 0 ||
			a.ModuleID == b.ModuleID {
			continue
		}
		k := [2]int32{a.ModuleID, b.ModuleID}
		if !medge[k] {
			medge[k] = true
			direct = append(direct, k)
			deg[a.ModuleID]++
		}
	}

	best := map[[2]int32]int32{}
	for k := range medge {
		best[k] = 1
	}

	cur := map[[2]int32]int32{}
	maps.Copy(cur, best)
	for depth := int32(2); depth <= 4; depth++ {
		next := map[[2]int32]int32{}
		for k, d := range cur {
			if d != depth-1 {
				continue
			}
			for _, e := range direct {
				if k[1] != e[0] {
					continue
				}
				nk := [2]int32{k[0], e[1]}
				if _, ok := best[nk]; !ok {
					next[nk] = depth
				}
			}
		}
		maps.Copy(best, next)
		cur = next
		if len(next) == 0 {
			break
		}
	}
	type pair struct{ a, b int32 }
	seen := map[pair]bool{}
	var keys []pair
	for k := range best {
		if k[0] < k[1] {
			pk := pair{k[0], k[1]}
			if !seen[pk] {
				seen[pk] = true
				keys = append(keys, pk)
			}
		}
	}
	sort.Slice(keys, func(i, j int) bool {
		if keys[i].a != keys[j].a {
			return keys[i].a < keys[j].a
		}
		return keys[i].b < keys[j].b
	})
	var rows [][]fval
	for _, k := range keys {
		out, ok1 := best[[2]int32{k.a, k.b}]
		back, ok2 := best[[2]int32{k.b, k.a}]
		if !ok1 || !ok2 {
			continue
		}
		if !likeMatch(g.modName(k.a), p.mod) {
			continue
		}
		rows = append(rows, []fval{fStr(g.modName(k.a)), fStr(g.modName(k.b)),
			fI32(out), fI32(back), fI32(deg[k.a]), fI32(deg[k.b])})
	}
	orderBy(rows, dSum(2, 3), dI(4))
	return cols, limit(rows, p)
}

func qQ73(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "dominant_prefix", "prefix_users", "fan_in", "sloc", "at"}
	counts := map[int32]map[string]int32{}
	prefix := map[int32]string{}
	for _, s := range g.syms() {
		if s.Kind() != "function" {
			continue
		}
		u := strings.IndexByte(s.Name(), '_')
		var pr string
		if u >= 1 {
			pr = s.Name()[:u+1]
		}
		if pr == "" {
			continue
		}
		m := counts[s.FileID]
		if m == nil {
			m = map[string]int32{}
			counts[s.FileID] = m
		}
		m[pr]++
	}
	for fid, m := range counts {

		best, bn := int32(0), ""
		for k, v := range m {
			if v > best || (v == best && k > bn) {
				best, bn = v, k
			}
		}
		prefix[fid] = bn
	}
	var rows [][]fval
	for _, s := range g.syms() {
		if s.Kind() != "function" {
			continue
		}
		u := strings.IndexByte(s.Name(), '_')
		if u < 1 {
			continue
		}
		pr := s.Name()[:u+1]
		dom := prefix[s.FileID]
		n := counts[s.FileID][dom]
		if pr == dom || n < 3 {
			continue
		}
		if !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		rows = append(rows, []fval{fStr(s.Name()), fStr(dom), fI32(n),
			fI32(s.FanIn), fI32(s.Sloc), fStr(g.at(s))})
	}
	orderBy(rows, dI(2), dI(3))
	return cols, limit(rows, p)
}

func qQ74(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "fan_in", "cyclo", "sloc", "module", "at"}
	untested := map[int32]bool{}
	for _, e := range g.Edges {
		cs := g.sym(e.CallerID)
		if cs == nil {
			continue
		}
		if f := g.fileOf(cs.ID); f != nil && f.IsTest == 1 {
			untested[e.CalleeID] = true
		}
		if cs.IsTest == 1 {
			untested[e.CalleeID] = true
		}
	}
	var rows [][]fval
	for _, s := range g.syms() {
		if s.Kind() != "function" || s.FanIn < 3 {
			continue
		}
		f := g.fileOf(s.ID)
		if f == nil || f.IsTest != 0 || s.IsTest != 0 || untested[s.ID] {
			continue
		}
		if !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		m := g.modName(s.ModuleID)
		if m == "" {
			m = "(none)"
		}
		rows = append(rows, []fval{fStr(s.Name()), fI32(s.FanIn),
			fI32(s.Cyclomatic), fI32(s.Sloc), fStr(m), fStr(g.at(s))})
	}
	orderBy(rows, dI(1), dI(2), cmpS(0))
	return cols, limit(rows, p)
}

func qQ75(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "io_calls", "depth", "loops", "calls", "fan_in", "at"}
	var rows [][]fval
	for _, s := range g.syms() {
		if s.IOInLoop <= 0 || !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		rows = append(rows, []fval{fStr(s.Name()), fI32(s.IOInLoop),
			fI32(s.MaxLoopDepth), fI32(s.NLoops), fI32(s.CallInLoop),
			fI32(s.FanIn), fStr(g.at(s))})
	}
	orderBy(rows, dI(1), dI(2))
	return cols, limit(rows, p)
}

func qQ76(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "lock_ops", "depth", "acquires", "releases",
		"fan_in", "at"}
	var rows [][]fval
	for _, s := range g.syms() {
		if s.LockInLoop <= 0 || !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		rows = append(rows, []fval{fStr(s.Name()), fI32(s.LockInLoop),
			fI32(s.MaxLoopDepth), fI32(g.rv(s).NLockAcquire), fI32(g.rv(s).NLockRelease),
			fI32(s.FanIn), fStr(g.at(s))})
	}
	orderBy(rows, dI(1), dI(2))
	return cols, limit(rows, p)
}

func qQ77(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "branches", "depth", "switches", "calls", "sloc",
		"fan_in", "at"}
	var rows [][]fval
	for _, s := range g.symsName() {
		if s.BranchInLoop <= 0 || s.MaxLoopDepth < 1 {
			continue
		}
		if !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		rows = append(rows, []fval{fStr(s.Name()), fI32(s.BranchInLoop),
			fI32(s.MaxLoopDepth), fI32(g.rv(s).SwitchInLoop), fI32(s.CallInLoop),
			fI32(s.Sloc), fI32(s.FanIn), fStr(g.at(s))})
	}
	orderBy(rows, dI(1), dI(2))
	return cols, limit(rows, p)
}

func simpleQ(cols []string, keep func(s *Symbol) bool, g *Graph, p params,
	fill func(s *Symbol) []fval, keys ...func(a, b []fval) int) ([]string, [][]fval) {
	var rows [][]fval
	for _, s := range g.syms() {
		if !keep(s) {
			continue
		}
		if !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		rows = append(rows, fill(s))
	}
	orderBy(rows, then(keys...), cmpS(0))
	return cols, limit(rows, p)
}

func qQ78(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "et_regs", "epoll_calls", "kqueue_calls",
		"eagain_checks", "loops", "cyclo", "fan_in", "at"}
	return simpleQ(cols, func(s *Symbol) bool { return g.rv(s).NEtReg > 0 && g.rv(s).NEagain == 0 },
		g, p, func(s *Symbol) []fval {
			return []fval{fStr(s.Name()), fI32(g.rv(s).NEtReg), fI32(g.rv(s).NEpoll),
				fI32(g.rv(s).NKqueue), fI32(g.rv(s).NEagain), fI32(s.NLoops),
				fI32(s.Cyclomatic), fI32(s.FanIn), fStr(g.at(s))}
		}, cmpI(1), cmpI(6))
}

func qQ79(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "waits", "epoll_calls", "uring_calls",
		"kqueue_calls", "eintr_checks", "loops", "cyclo", "fan_in", "at"}
	return simpleQ(cols, func(s *Symbol) bool { return g.rv(s).NEventWait > 0 && g.rv(s).NEintr == 0 },
		g, p, func(s *Symbol) []fval {
			return []fval{fStr(s.Name()), fI32(g.rv(s).NEventWait), fI32(g.rv(s).NEpoll),
				fI32(g.rv(s).NUring), fI32(g.rv(s).NKqueue), fI32(g.rv(s).NEintr), fI32(s.NLoops),
				fI32(s.Cyclomatic), fI32(s.FanIn), fStr(g.at(s))}
		}, cmpI(1), cmpI(7))
}

func qQ80(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "write_ready", "epoll_calls", "kqueue_calls",
		"deregistrations", "loops", "fan_in", "at"}
	return simpleQ(cols, func(s *Symbol) bool {
		return g.rv(s).NWriteReady > 0 && g.rv(s).NDereg == 0
	}, g, p, func(s *Symbol) []fval {
		return []fval{fStr(s.Name()), fI32(g.rv(s).NWriteReady), fI32(g.rv(s).NEpoll),
			fI32(g.rv(s).NKqueue), fI32(g.rv(s).NDereg), fI32(s.NLoops), fI32(s.FanIn),
			fStr(g.at(s))}
	}, dI(1), dI(6))
}

func qQ81(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "epoll_calls", "kqueue_calls", "err_flags", "waits",
		"cyclo", "fan_in", "at"}
	return simpleQ(cols, func(s *Symbol) bool {
		return (g.rv(s).NEpoll > 0 || g.rv(s).NKqueue > 0) && g.rv(s).NErrFlag == 0
	}, g, p, func(s *Symbol) []fval {
		return []fval{fStr(s.Name()), fI32(g.rv(s).NEpoll), fI32(g.rv(s).NKqueue),
			fI32(g.rv(s).NErrFlag), fI32(g.rv(s).NEventWait), fI32(s.Cyclomatic),
			fI32(s.FanIn), fStr(g.at(s))}
	}, func(a, b []fval) int { return -cmpI32(a[1].i+a[2].i, b[1].i+b[2].i) },
		dI(6))
}

func qQ82(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "oneshot_regs", "rearms", "epoll_calls",
		"kqueue_calls", "cyclo", "fan_in", "at"}
	return simpleQ(cols, func(s *Symbol) bool {
		return g.rv(s).NOneshotReg > 0 && g.rv(s).NRearm == 0
	}, g, p, func(s *Symbol) []fval {
		return []fval{fStr(s.Name()), fI32(g.rv(s).NOneshotReg), fI32(g.rv(s).NRearm),
			fI32(g.rv(s).NEpoll), fI32(g.rv(s).NKqueue), fI32(s.Cyclomatic), fI32(s.FanIn),
			fStr(g.at(s))}
	}, cmpI(1), cmpI(6))
}

func qQ83(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "uring_calls", "res_checks", "waits", "errno_reads",
		"cyclo", "fan_in", "at"}
	return simpleQ(cols, func(s *Symbol) bool { return g.rv(s).NUring > 0 && g.rv(s).NUringRes == 0 },
		g, p, func(s *Symbol) []fval {
			return []fval{fStr(s.Name()), fI32(g.rv(s).NUring), fI32(g.rv(s).NUringRes),
				fI32(g.rv(s).NEventWait), fI32(g.rv(s).NErrno), fI32(s.Cyclomatic),
				fI32(s.FanIn), fStr(g.at(s))}
		}, cmpI(1), cmpI(6))
}

func qQ84(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "uring_calls", "errno_reads", "res_checks", "cyclo",
		"fan_in", "at"}
	return simpleQ(cols, func(s *Symbol) bool { return g.rv(s).NUring > 0 && g.rv(s).NErrno > 0 },
		g, p, func(s *Symbol) []fval {
			return []fval{fStr(s.Name()), fI32(g.rv(s).NUring), fI32(g.rv(s).NErrno),
				fI32(g.rv(s).NUringRes), fI32(s.Cyclomatic), fI32(s.FanIn),
				fStr(g.at(s))}
		}, cmpI(1), cmpI(2))
}

func qQ85(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "uring_calls", "sqpoll_setups", "frees", "allocs",
		"cyclo", "at"}
	return simpleQ(cols, func(s *Symbol) bool {
		return g.rv(s).NUring > 0 && g.rv(s).NUringSqpoll > 0 && g.rv(s).NFree > 0
	}, g, p, func(s *Symbol) []fval {
		return []fval{fStr(s.Name()), fI32(g.rv(s).NUring), fI32(g.rv(s).NUringSqpoll),
			fI32(g.rv(s).NFree), fI32(s.NAlloc), fI32(s.Cyclomatic), fStr(g.at(s))}
	}, cmpI(2), cmpI(3))
}

func qQ86(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "ring_touches", "uring_calls", "barriers", "cyclo",
		"fan_in", "at"}
	return simpleQ(cols, func(s *Symbol) bool {
		return g.rv(s).NUringRing > 0 && g.rv(s).NUringBarrier == 0
	}, g, p, func(s *Symbol) []fval {
		return []fval{fStr(s.Name()), fI32(g.rv(s).NUringRing), fI32(g.rv(s).NUring),
			fI32(g.rv(s).NUringBarrier), fI32(s.Cyclomatic), fI32(s.FanIn),
			fStr(g.at(s))}
	}, cmpI(1), cmpI(5))
}

func qQ87(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "waits", "allocs", "allocs_in_loop", "loop_depth",
		"calls_in_loop", "cyclo", "fan_in", "at"}
	return simpleQ(cols, func(s *Symbol) bool { return g.rv(s).NEventWait > 0 && s.NAlloc > 0 },
		g, p, func(s *Symbol) []fval {
			return []fval{fStr(s.Name()), fI32(g.rv(s).NEventWait), fI32(s.NAlloc),
				fI32(s.AllocInLoop), fI32(s.MaxLoopDepth), fI32(s.CallInLoop),
				fI32(s.Cyclomatic), fI32(s.FanIn), fStr(g.at(s))}
		}, cmpI(2), cmpI(3))
}

func qQ88(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "indefinite", "zero_tmo", "waits", "epoll_calls",
		"kqueue_calls", "loops", "cyclo", "at"}
	return simpleQ(cols, func(s *Symbol) bool {
		return g.rv(s).NEvTimeoutIndefinite > 0 || g.rv(s).NEvTimeoutZero > 0
	}, g, p, func(s *Symbol) []fval {
		return []fval{fStr(s.Name()), fI32(g.rv(s).NEvTimeoutIndefinite),
			fI32(g.rv(s).NEvTimeoutZero), fI32(g.rv(s).NEventWait), fI32(g.rv(s).NEpoll),
			fI32(g.rv(s).NKqueue), fI32(s.NLoops), fI32(s.Cyclomatic), fStr(g.at(s))}
	}, func(a, b []fval) int {
		return -cmpI32(a[1].i+a[2].i, b[1].i+b[2].i)
	}, cmpI(7))
}

func qQ89(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "et_regs", "nonblock", "eagain_checks",
		"epoll_calls", "kqueue_calls", "cyclo", "fan_in", "at"}
	return simpleQ(cols, func(s *Symbol) bool { return g.rv(s).NEtReg > 0 && g.rv(s).NNonblockSet == 0 },
		g, p, func(s *Symbol) []fval {
			return []fval{fStr(s.Name()), fI32(g.rv(s).NEtReg), fI32(g.rv(s).NNonblockSet),
				fI32(g.rv(s).NEagain), fI32(g.rv(s).NEpoll), fI32(g.rv(s).NKqueue),
				fI32(s.Cyclomatic), fI32(s.FanIn), fStr(g.at(s))}
		}, cmpI(1), cmpI(6))
}

func qQ90(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "creates", "destroys", "epoll_calls", "uring_calls",
		"kqueue_calls", "returns_", "cyclo", "fan_in", "at"}
	return simpleQ(cols, func(s *Symbol) bool {
		return g.rv(s).NEventCreate > 0 && g.rv(s).NEventDestroy == 0
	}, g, p, func(s *Symbol) []fval {
		return []fval{fStr(s.Name()), fI32(g.rv(s).NEventCreate), fI32(g.rv(s).NEventDestroy),
			fI32(g.rv(s).NEpoll), fI32(g.rv(s).NUring), fI32(g.rv(s).NKqueue), fI32(s.NReturns),
			fI32(s.Cyclomatic), fI32(s.FanIn), fStr(g.at(s))}
	}, dI(1), dI(8))
}

func qQ91(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "sqe_gets", "null_checks", "uring_calls", "cyclo",
		"fan_in", "at"}
	return simpleQ(cols, func(s *Symbol) bool { return g.rv(s).NUringSqe > 0 && s.NNullCheck == 0 },
		g, p, func(s *Symbol) []fval {
			return []fval{fStr(s.Name()), fI32(g.rv(s).NUringSqe), fI32(s.NNullCheck),
				fI32(g.rv(s).NUring), fI32(s.Cyclomatic), fI32(s.FanIn), fStr(g.at(s))}
		}, cmpI(1), cmpI(5))
}

func qQ92(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "cqe_seen", "waits", "uring_calls", "sqe_gets",
		"cyclo", "fan_in", "at"}
	return simpleQ(cols, func(s *Symbol) bool {
		return g.rv(s).NUring > 0 && g.rv(s).NEventWait > 0 && g.rv(s).NUringSeen == 0
	}, g, p, func(s *Symbol) []fval {
		return []fval{fStr(s.Name()), fI32(g.rv(s).NUringSeen), fI32(g.rv(s).NEventWait),
			fI32(g.rv(s).NUring), fI32(g.rv(s).NUringSqe), fI32(s.Cyclomatic),
			fI32(s.FanIn), fStr(g.at(s))}
	}, cmpI(2), cmpI(3))
}

func qQ93(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "uncorrelated", "sqe_gets", "user_data_sets",
		"waits", "cyclo", "fan_in", "at"}
	return simpleQ(cols, func(s *Symbol) bool {
		return g.rv(s).NUringSqe >= 2 && g.rv(s).NUringSqe > g.rv(s).NUringUdata
	}, g, p, func(s *Symbol) []fval {
		return []fval{fStr(s.Name()), fI32(g.rv(s).NUringSqe - g.rv(s).NUringUdata),
			fI32(g.rv(s).NUringSqe), fI32(g.rv(s).NUringUdata), fI32(g.rv(s).NEventWait),
			fI32(s.Cyclomatic), fI32(s.FanIn), fStr(g.at(s))}
	}, cmpI(1), cmpI(2))
}

func qQ94(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "stream_ops", "linked", "sqe_gets", "loop_depth",
		"cyclo", "fan_in", "at"}
	return simpleQ(cols, func(s *Symbol) bool {
		return g.rv(s).NUringStreamOps > 0 && g.rv(s).NUringLink == 0
	}, g, p, func(s *Symbol) []fval {
		return []fval{fStr(s.Name()), fI32(g.rv(s).NUringStreamOps), fI32(g.rv(s).NUringLink),
			fI32(g.rv(s).NUringSqe), fI32(s.MaxLoopDepth), fI32(s.Cyclomatic),
			fI32(s.FanIn), fStr(g.at(s))}
	}, cmpI(1), cmpI(6))
}

func qQ95(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "ring_inits", "exits", "uring_calls", "any_release",
		"cyclo", "fan_in", "at"}
	return simpleQ(cols, func(s *Symbol) bool {
		return g.rv(s).NUring > 0 && g.rv(s).NEventCreate > 0 && g.rv(s).NUringTeardown == 0
	}, g, p, func(s *Symbol) []fval {
		return []fval{fStr(s.Name()), fI32(g.rv(s).NEventCreate), fI32(g.rv(s).NUringTeardown),
			fI32(g.rv(s).NUring), fI32(g.rv(s).NEventDestroy), fI32(s.Cyclomatic),
			fI32(s.FanIn), fStr(g.at(s))}
	}, cmpI(1), cmpI(2))
}

func qQ96(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "timers", "zero_data", "kqueue_calls", "cyclo",
		"fan_in", "at"}
	return simpleQ(cols, func(s *Symbol) bool { return g.rv(s).NKqTimerZeroData > 0 },
		g, p, func(s *Symbol) []fval {
			return []fval{fStr(s.Name()), fI32(g.rv(s).NKqTimer), fI32(g.rv(s).NKqTimerZeroData),
				fI32(g.rv(s).NKqueue), fI32(s.Cyclomatic), fI32(s.FanIn), fStr(g.at(s))}
		}, cmpI(2), cmpI(5))
}

func qQ97(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "receipt_batches", "err_flags", "kqueue_calls",
		"cyclo", "fan_in", "at"}
	return simpleQ(cols, func(s *Symbol) bool { return g.rv(s).NKqReceipt > 0 && g.rv(s).NErrFlag == 0 },
		g, p, func(s *Symbol) []fval {
			return []fval{fStr(s.Name()), fI32(g.rv(s).NKqReceipt), fI32(g.rv(s).NErrFlag),
				fI32(g.rv(s).NKqueue), fI32(s.Cyclomatic), fI32(s.FanIn), fStr(g.at(s))}
		}, cmpI(1), cmpI(5))
}

func qQ98(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "waits", "io_in_loop", "lock_in_loop", "calls_in_loop",
		"loop_depth", "cyclo", "fan_in", "at"}
	return simpleQ(cols, func(s *Symbol) bool {
		return g.rv(s).NEventWait > 0 && (s.IOInLoop > 0 || s.LockInLoop > 0)
	}, g, p, func(s *Symbol) []fval {
		return []fval{fStr(s.Name()), fI32(g.rv(s).NEventWait), fI32(s.IOInLoop),
			fI32(s.LockInLoop), fI32(s.CallInLoop), fI32(s.MaxLoopDepth),
			fI32(s.Cyclomatic), fI32(s.FanIn), fStr(g.at(s))}
	}, func(a, b []fval) int {
		return -cmpI32(a[2].i+a[3].i, b[2].i+b[3].i)
	}, cmpI(7))
}

func (g *Graph) apiUseIndex() map[int32][]int32 {
	if g.apiByID == nil {
		idx := make(map[int32][]int32, len(g.Symbols)/8+1)
		for i := range g.APIUses {
			id := g.APIUses[i].SymbolID
			idx[id] = append(idx[id], int32(i))
		}
		g.apiByID = idx
	}
	return g.apiByID
}

func hasAPIUse(g *Graph, sid int32, pred func(a *APIUse) bool) bool {
	if g.apiByID == nil {
		g.apiUseIndex()
	}
	for _, i := range g.apiByID[sid] {
		if pred(&g.APIUses[i]) {
			return true
		}
	}
	return false
}

func fnIs(names ...string) func(a *APIUse) bool {
	return func(a *APIUse) bool { return containsStr(names, a.Fn()) }
}

func apiQ(cols []string, fns []string, keep func(s *Symbol) bool, g *Graph, p params,
	fill func(s *Symbol) []fval, keys ...func(a, b []fval) int) ([]string, [][]fval) {
	var rows [][]fval
	for _, s := range g.syms() {
		if !keep(s) || !hasAPIUse(g, s.ID, fnIs(fns...)) {
			continue
		}
		if !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		rows = append(rows, fill(s))
	}
	orderBy(rows, then(keys...), cmpS(0))
	return cols, limit(rows, p)
}

func qQ99(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "sloc", "cyclo", "fan_in", "at"}
	return apiQ(cols, []string{"snprintf", "vsnprintf"},
		func(s *Symbol) bool { return g.rv(s).NRetNegCheck == 0 }, g, p,
		func(s *Symbol) []fval {
			return []fval{fStr(s.Name()), fI32(s.Sloc), fI32(s.Cyclomatic),
				fI32(s.FanIn), fStr(g.at(s))}
		}, func(a, b []fval) int { return -cmpI32(a[1].i, b[1].i) }, dI(3))
}

func qQ100(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "sloc", "cyclo", "fan_in", "at"}
	return apiQ(cols, []string{"fread", "fwrite", "fgets", "fscanf", "vfscanf",
		"fprintf", "fputs", "fputc"},
		func(s *Symbol) bool { return g.rv(s).NRetNegCheck == 0 && s.NNullCheck == 0 },
		g, p, func(s *Symbol) []fval {
			return []fval{fStr(s.Name()), fI32(s.Sloc), fI32(s.Cyclomatic),
				fI32(s.FanIn), fStr(g.at(s))}
		}, func(a, b []fval) int { return -cmpI32(a[1].i, b[1].i) }, dI(3))
}

func qQ101(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "errno_reads", "endptr_checks", "cyclo", "fan_in", "at"}
	return apiQ(cols, []string{"strtol", "strtoll", "strtoul", "strtoull",
		"strtod", "strtof", "strtold", "strtoimax", "strtoumax"},
		func(s *Symbol) bool { return !(g.rv(s).NErrnoZero > 0 && g.rv(s).NEndptr > 0) },
		g, p, func(s *Symbol) []fval {
			return []fval{fStr(s.Name()), fI32(g.rv(s).NErrno), fI32(g.rv(s).NEndptr),
				fI32(s.Cyclomatic), fI32(s.FanIn), fStr(g.at(s))}
		}, dI(3), dI(4))
}

func qQ102(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "cyclo", "params", "fan_in", "at"}
	return apiQ(cols, []string{"isalnum", "isalpha", "isblank", "iscntrl",
		"isdigit", "isgraph", "islower", "isprint", "ispunct", "isspace",
		"isupper", "isxdigit", "tolower", "toupper"},
		func(s *Symbol) bool { return g.rv(s).NUcharCast == 0 }, g, p,
		func(s *Symbol) []fval {
			return []fval{fStr(s.Name()), fI32(s.Cyclomatic), fI32(s.NParams),
				fI32(s.FanIn), fStr(g.at(s))}
		}, dI(3), dI(1))
}

func qQ103(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "loops", "cyclo", "fan_in", "at"}
	return apiQ(cols, []string{"nanosleep", "usleep", "sleep"},
		func(s *Symbol) bool { return g.rv(s).NEintr == 0 }, g, p,
		func(s *Symbol) []fval {
			return []fval{fStr(s.Name()), fI32(s.NLoops), fI32(s.Cyclomatic),
				fI32(s.FanIn), fStr(g.at(s))}
		}, dI(3), dI(2))
}

func qQ104(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "depth", "io_in_loop", "cyclo", "fan_in", "at"}
	return apiQ(cols, []string{"send", "sendto", "sendmsg", "write", "writev",
		"pwritev"}, func(s *Symbol) bool { return g.rv(s).NRetNegCheck == 0 }, g, p,
		func(s *Symbol) []fval {
			return []fval{fStr(s.Name()), fI32(s.MaxLoopDepth), fI32(s.IOInLoop),
				fI32(s.Cyclomatic), fI32(s.FanIn), fStr(g.at(s))}
		}, dI(4), dI(1))
}

func qQ105(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "returns_", "cyclo", "fan_in", "at"}
	return apiQ(cols, []string{"mmap"},
		func(s *Symbol) bool { return !hasAPIUse(g, s.ID, fnIs("munmap")) }, g, p,
		func(s *Symbol) []fval {
			return []fval{fStr(s.Name()), fI32(s.NReturns), fI32(s.Cyclomatic),
				fI32(s.FanIn), fStr(g.at(s))}
		}, dI(3), dI(2))
}

func qQ106(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "cyclo", "returns_", "fan_in", "at"}
	return apiQ(cols, []string{"waitpid", "wait", "waitid", "wait3", "wait4"},
		func(s *Symbol) bool { return g.rv(s).NRetNegCheck == 0 }, g, p,
		func(s *Symbol) []fval {
			return []fval{fStr(s.Name()), fI32(s.Cyclomatic), fI32(s.NReturns),
				fI32(s.FanIn), fStr(g.at(s))}
		}, cmpI(3), cmpI(1))
}

func qQ107(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "cyclo", "fan_in", "at"}
	return apiQ(cols, []string{"scanf", "fscanf", "sscanf", "vscanf", "vfscanf",
		"vsscanf"}, func(s *Symbol) bool { return g.rv(s).NRetNegCheck == 0 }, g, p,
		func(s *Symbol) []fval {
			return []fval{fStr(s.Name()), fI32(s.Cyclomatic), fI32(s.FanIn),
				fStr(g.at(s))}
		}, dI(2), dI(1))
}

func qQ108(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "depth", "cyclo", "fan_in", "at"}
	return apiQ(cols, []string{"sqrt", "log", "log10", "log2", "log1p", "logb",
		"asin", "acos", "atanh", "acosh", "tgamma", "lgamma", "pow"},
		func(s *Symbol) bool { return g.rv(s).NDomainGuard == 0 }, g, p,
		func(s *Symbol) []fval {
			return []fval{fStr(s.Name()), fI32(s.MaxLoopDepth),
				fI32(s.Cyclomatic), fI32(s.FanIn), fStr(g.at(s))}
		}, dI(3), dI(1))
}

func qQ109(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "cyclo", "conc_in_fn", "fan_in", "at"}
	return apiQ(cols, []string{"localtime", "gmtime", "ctime", "asctime"},
		func(s *Symbol) bool { return true }, g, p,
		func(s *Symbol) []fval {
			return []fval{fStr(s.Name()), fI32(s.Cyclomatic), fI32(s.NConcurrency),
				fI32(s.FanIn), fStr(g.at(s))}
		}, cmpI(3), cmpI(1))
}

func qQ110(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "cyclo", "fan_in", "at"}
	return apiQ(cols, []string{"signal"}, func(s *Symbol) bool {
		return !hasAPIUse(g, s.ID, fnIs("sigaction"))
	}, g, p, func(s *Symbol) []fval {
		return []fval{fStr(s.Name()), fI32(s.Cyclomatic), fI32(s.FanIn), fStr(g.at(s))}
	}, dI(2), dI(1))
}

func qQ111(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "cyclo", "fan_in", "at"}
	return apiQ(cols, []string{"mmap"},
		func(s *Symbol) bool { return g.rv(s).NMapFailed == 0 && s.NNullCheck == 0 },
		g, p, func(s *Symbol) []fval {
			return []fval{fStr(s.Name()), fI32(s.Cyclomatic), fI32(s.FanIn),
				fStr(g.at(s))}
		}, dI(2), dI(1))
}

func qQ112(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "depth", "cyclo", "fan_in", "at"}
	return apiQ(cols, []string{"accept", "accept4"},
		func(s *Symbol) bool { return g.rv(s).NNonblockSet == 0 }, g, p,
		func(s *Symbol) []fval {
			return []fval{fStr(s.Name()), fI32(s.MaxLoopDepth),
				fI32(s.Cyclomatic), fI32(s.FanIn), fStr(g.at(s))}
		}, cmpI(3), cmpI(1))
}

func qQ113(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "cyclo", "returns_", "fan_in", "at"}
	return apiQ(cols, []string{"va_start"},
		func(s *Symbol) bool { return g.rv(s).NVaEnd == 0 }, g, p,
		func(s *Symbol) []fval {
			return []fval{fStr(s.Name()), fI32(s.Cyclomatic), fI32(s.NReturns),
				fI32(s.FanIn), fStr(g.at(s))}
		}, cmpI(3), cmpI(1))
}

func qQ114(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "sized_arrays", "cyclo", "fan_in", "at"}
	return apiQ(cols, []string{}, func(s *Symbol) bool { return g.rv(s).NStackszArray > 0 },
		g, p, func(s *Symbol) []fval {
			return []fval{fStr(s.Name()), fI32(g.rv(s).NStackszArray),
				fI32(s.Cyclomatic), fI32(s.FanIn), fStr(g.at(s))}
		}, cmpI(1), cmpI(3))
}

func qQ114b(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "sized_arrays", "cyclo", "fan_in", "at"}
	var rows [][]fval
	for _, s := range g.syms() {
		if g.rv(s).NStackszArray <= 0 {
			continue
		}
		ok := false
		for j := range g.APIUses {
			a := &g.APIUses[j]
			if a.SymbolID == s.ID && (a.NS() == "signal.h" || a.NS() == "pthread.h") {
				ok = true
				break
			}
		}
		if !ok || !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		rows = append(rows, []fval{fStr(s.Name()), fI32(g.rv(s).NStackszArray),
			fI32(s.Cyclomatic), fI32(s.FanIn), fStr(g.at(s))})
	}
	orderBy(rows, dI(1), dI(3))
	return cols, limit(rows, p)
}

func qQ115(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "broken_checks", "cyclo", "fan_in", "at"}
	return apiQ(cols, []string{"memcpy", "memmove", "memset", "malloc", "realloc",
		"strlen", "strcpy"}, func(s *Symbol) bool { return g.rv(s).NPtrOvfCheck > 0 },
		g, p, func(s *Symbol) []fval {
			return []fval{fStr(s.Name()), fI32(g.rv(s).NPtrOvfCheck), fI32(s.Cyclomatic),
				fI32(s.FanIn), fStr(g.at(s))}
		}, cmpI(1), cmpI(3))
}

func qQ116(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "transposed", "cyclo", "fan_in", "at"}
	return apiQ(cols, []string{"calloc"},
		func(s *Symbol) bool { return g.rv(s).NCallocTransposed > 0 }, g, p,
		func(s *Symbol) []fval {
			return []fval{fStr(s.Name()), fI32(g.rv(s).NCallocTransposed),
				fI32(s.Cyclomatic), fI32(s.FanIn), fStr(g.at(s))}
		}, cmpI(1), cmpI(3))
}

func qQ117(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "array_va_args", "cyclo", "fan_in", "at"}
	return apiQ(cols, []string{"va_arg", "va_start"},
		func(s *Symbol) bool { return g.rv(s).NVaArgArr > 0 }, g, p,
		func(s *Symbol) []fval {
			return []fval{fStr(s.Name()), fI32(g.rv(s).NVaArgArr), fI32(s.Cyclomatic),
				fI32(s.FanIn), fStr(g.at(s))}
		}, cmpI(1), cmpI(3))
}

func qQ118(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "monotonic_uses", "cyclo", "depth", "fan_in", "at"}
	return apiQ(cols, []string{"gettimeofday", "time", "ftime", "clock"},
		func(s *Symbol) bool {
			return g.rv(s).NMonotonicClock == 0 &&
				!hasAPIUse(g, s.ID, fnIs("clock_gettime"))
		}, g, p, func(s *Symbol) []fval {
			return []fval{fStr(s.Name()), fI32(g.rv(s).NMonotonicClock),
				fI32(s.Cyclomatic), fI32(s.MaxLoopDepth), fI32(s.FanIn),
				fStr(g.at(s))}
		}, dI(4), dI(2))
}

func qQ119(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "size_one_waits", "waits", "epoll_calls",
		"kqueue_calls", "cyclo", "fan_in", "at"}
	return simpleQ(cols, func(s *Symbol) bool { return g.rv(s).NEvBatchOne > 0 },
		g, p, func(s *Symbol) []fval {
			return []fval{fStr(s.Name()), fI32(g.rv(s).NEvBatchOne), fI32(g.rv(s).NEventWait),
				fI32(g.rv(s).NEpoll), fI32(g.rv(s).NKqueue), fI32(s.Cyclomatic),
				fI32(s.FanIn), fStr(g.at(s))}
		}, cmpI(1), cmpI(6))
}

var _ = strconv.Itoa

type params struct {
	mod string
	lim int
}

func likeMatch(s, pat string) bool {
	if pat == "%" {
		return true
	}

	si, pi := 0, 0
	star, mark := -1, 0
	for si < len(s) {
		switch {
		case pi < len(pat) && (pat[pi] == '_' || pat[pi] == s[si]):
			si++
			pi++
		case pi < len(pat) && pat[pi] == '%':
			star = pi
			pi++
			mark = si
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

func (g *Graph) modName(id int32) string {
	if id <= 0 || int(id) > len(g.Modules) {
		return ""
	}
	return g.Modules[id-1].Name()
}

func (g *Graph) fileOf(symID int32) *File {
	if symID < 1 || int(symID) > len(g.Symbols) {
		return nil
	}
	fid := g.Symbols[symID-1].FileID
	if fid < 1 || int(fid) > len(g.Files) {
		return nil
	}
	return &g.Files[fid-1]
}

func (g *Graph) at(s *Symbol) string {
	f := g.fileOf(s.ID)
	if f == nil {
		return ""
	}
	return f.Path() + ":" + strconv.Itoa(int(s.LineStart))
}

func pct(a, b int64) int32 {
	if b == 0 {
		return 0
	}
	return int32(float64(a) * 100.0 / float64(b))
}

func minI(a, b int32) int32 {
	if a < b {
		return a
	}
	return b
}

func maxI(a, b int32) int32 {
	if a > b {
		return a
	}
	return b
}

func i32f(f float64) int32 { return int32(f) }

func limit(rows [][]fval, p params) [][]fval {
	if p.lim >= 0 && len(rows) > p.lim {
		return rows[:p.lim]
	}
	return rows
}

type rowSorter struct {
	rows [][]fval
	less func(i, j int) bool
}

func (r rowSorter) Len() int      { return len(r.rows) }
func (r rowSorter) Swap(i, j int) { r.rows[i], r.rows[j] = r.rows[j], r.rows[i] }
func (r rowSorter) Less(i, j int) bool {
	return r.less(i, j)
}

func sortRows(rows [][]fval, less func(i, j int) bool) {
	sort.SliceStable(rows, less)
}

func cmpI(col int) func(a, b []fval) int {
	return func(a, b []fval) int { return cmpI32(a[col].i, b[col].i) }
}

func cmpI32(a, b int64) int {
	switch {
	case a < b:
		return -1
	case a > b:
		return 1
	}
	return 0
}

func cmpLine(col int) func(a, b []fval) int {
	return func(a, b []fval) int {
		sa, sb := a[col].s, b[col].s
		ia, ib := strings.LastIndexByte(sa, ':'), strings.LastIndexByte(sb, ':')
		na, _ := strconv.Atoi(sa[ia+1:])
		nb, _ := strconv.Atoi(sb[ib+1:])
		return cmpI32(int64(na), int64(nb))
	}
}

func cmpS(col int) func(a, b []fval) int {
	return func(a, b []fval) int { return strings.Compare(a[col].s, b[col].s) }
}

func cmpF(col int) func(a, b []fval) int {
	return func(a, b []fval) int {
		switch {
		case a[col].f < b[col].f:
			return -1
		case a[col].f > b[col].f:
			return 1
		}
		return 0
	}
}

func then(cs ...func(a, b []fval) int) func(a, b []fval) int {
	return func(a, b []fval) int {
		for _, c := range cs {
			if v := c(a, b); v != 0 {
				return v
			}
		}
		return 0
	}
}

func orderBy(rows [][]fval, keys ...func(a, b []fval) int) {
	cmp := then(keys...)
	sort.SliceStable(rows, func(i, j int) bool { return cmp(rows[i], rows[j]) < 0 })
}

func groupConcat(vals []string) string { return strings.Join(vals, ",") }

func distinctStrings(in []string) []string {
	seen := map[string]bool{}
	out := make([]string, 0, len(in))
	for _, v := range in {
		if !seen[v] {
			seen[v] = true
			out = append(out, v)
		}
	}
	return out
}

func containsStr(list []string, s string) bool {
	return slices.Contains(list, s)
}

func isFnKind(k string) bool {
	return k == "function" || k == "method" || k == "constructor" || k == "closure"
}

func isTypeKind(k string) bool {
	switch k {
	case "class", "struct", "interface", "trait", "enum", "union", "record",
		"protocol", "type", "module", "impl", "object", "mixin":
		return true
	}
	return false
}

func (g *Graph) sym(id int32) *Symbol {
	if id < 1 || int(id) > len(g.Symbols) {
		return nil
	}
	return g.Symbols[id-1]
}

func dI(col int) func(a, b []fval) int {
	return func(a, b []fval) int { return cmpI32(b[col].i, a[col].i) }
}

func dSum(cols ...int) func(a, b []fval) int {
	return func(a, b []fval) int {
		sa, sb := int64(0), int64(0)
		for _, c := range cols {
			sa += a[c].i
			sb += b[c].i
		}
		return cmpI32(sb, sa)
	}
}

func dWeighted(w [][3]int32) func(a, b []fval) int {
	return func(a, b []fval) int {
		sa, sb := int64(0), int64(0)
		for _, x := range w {
			sa += int64(x[0]) * a[x[1]].i
			sb += int64(x[0]) * b[x[1]].i
		}
		return cmpI32(sb, sa)
	}
}

func dLenStr(col int) func(a, b []fval) int {
	return func(a, b []fval) int { return cmpI32(int64(len(b[col].s)), int64(len(a[col].s))) }
}

func (g *Graph) symsByName() []*Symbol { return g.scanByName() }

func (g *Graph) scanByName() []*Symbol {
	out := make([]*Symbol, 0, len(g.Symbols))
	for i := range g.Symbols {
		out = append(out, g.Symbols[i])
	}
	sort.SliceStable(out, func(a, b int) bool {
		if out[a].Name() != out[b].Name() {
			return out[a].Name() < out[b].Name()
		}
		return out[a].ID < out[b].ID
	})
	return out
}

func (g *Graph) symsByID() []*Symbol { return g.scanByID() }

func (g *Graph) scanByID() []*Symbol {
	out := make([]*Symbol, 0, len(g.Symbols))
	for i := range g.Symbols {
		out = append(out, g.Symbols[i])
	}
	return out
}

func (g *Graph) hazardsByCatN(cat string) []int32 {
	out := make([]int32, 0, 64)
	for i := range g.Hazards {
		if g.Hazards[i].Category() == cat {
			out = append(out, int32(i))
		}
	}
	sort.SliceStable(out, func(a, b int) bool {
		return g.Hazards[out[a]].N > g.Hazards[out[b]].N
	})
	return out
}

func (g *Graph) hazardsByPattern(pats []string) []*Hazard {
	sorted := append([]string{}, pats...)
	sort.Strings(sorted)
	var out []*Hazard
	for _, pat := range sorted {
		for i := range g.Hazards {
			if g.Hazards[i].Pattern() == pat {
				out = append(out, &g.Hazards[i])
			}
		}
	}
	return out
}

var scanOrder = "file"

func (g *Graph) syms() []*Symbol {
	if g.symsCache != nil && g.symsCacheOrder == scanOrder {
		return g.symsCache
	}
	out := g.symsUncached()
	g.symsCache, g.symsCacheOrder = out, scanOrder
	return out
}

func (g *Graph) symsUncached() []*Symbol {
	if scanOrder == "name" {
		return g.symsByName()
	}
	switch scanOrder {
	case "name":
		return g.symsByName()
	case "file":
		out := make([]*Symbol, 0, len(g.Symbols))
		for i := range g.Symbols {
			out = append(out, g.Symbols[i])
		}
		sort.SliceStable(out, func(a, b int) bool {
			fa, fb := g.fileOf2(out[a].FileID), g.fileOf2(out[b].FileID)
			if fa == nil || fb == nil {
				return out[a].ID < out[b].ID
			}
			if fa.Path() != fb.Path() {
				return fa.Path() < fb.Path()
			}
			if out[a].LineStart != out[b].LineStart {
				return out[a].LineStart < out[b].LineStart
			}
			return out[a].ID < out[b].ID
		})
		return out
	}
	return g.symsByID()
}

func (g *Graph) symsName() []*Symbol { return g.symsByName() }

func mM1(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"module", "fns", "fnptr", "via_macro", "external",
		"unresolved", "pct_unseen"}
	type agg struct {
		fns, fp, mac, ext, unr, calls int32
	}
	m := map[int32]*agg{}
	for _, s := range g.syms() {
		if s.Kind() != "function" {
			continue
		}
		a := m[s.ModuleID]
		if a == nil {
			a = &agg{}
			m[s.ModuleID] = a
		}
		a.fns++
		a.fp += g.rv(s).NFnptrCalls
		a.mac += g.rv(s).NMacroCalls
		a.ext += g.rv(s).NExternalCalls
		a.unr += s.NUnresolvedCalls
		a.calls += s.NCalls
	}
	var rows [][]fval
	for i := range g.Modules {
		mod := &g.Modules[i]
		if !likeMatch(mod.Name(), p.mod) {
			continue
		}
		a := m[mod.ID]
		if a == nil {
			continue
		}
		var pv fval = fNull()
		if a.calls != 0 {
			pv = fI32(pct(int64(a.fp+a.unr), int64(a.calls)))
		}
		rows = append(rows, []fval{fStr(mod.Name()), fI32(a.fns), fI32(a.fp),
			fI32(a.mac), fI32(a.ext), fI32(a.unr), pv})
	}
	orderBy(rows, dI(2), dI(5))
	return cols, limit(rows, p)
}

func mM2(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "fan_in", "sites", "cyclo", "sloc", "stat", "inl",
		"module", "at"}
	var rows [][]fval
	for _, s := range g.syms() {
		if s.Kind() != "function" || !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		rows = append(rows, []fval{fStr(s.Name()), fI32(s.FanIn), fI32(s.NCallsites),
			fI32(s.Cyclomatic), fI32(s.Sloc), fI32(s.IsStatic), fI32(s.IsInline),
			fOptStr(g.modName(s.ModuleID), s.ModuleID != 0), fStr(g.at(s))})
	}
	orderBy(rows, dI(1), dI(3), cmpS(0))
	return cols, limit(rows, p)
}

func mM3(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "risk", "cyclo", "cog", "nest", "mem", "io", "int_",
		"rec", "at"}
	var rows [][]fval
	for _, s := range g.syms() {
		if s.Kind() != "function" || !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		rows = append(rows, []fval{fStr(s.Name()), fI32(s.RiskScore),
			fI32(s.Cyclomatic), fI32(s.Cognitive), fI32(s.MaxNesting),
			fI32(s.NMemory), fI32(s.NIO), fI32(s.NInteger), fI32(s.IsRecursive),
			fStr(g.at(s))})
	}
	orderBy(rows, dI(1), cmpS(0))
	return cols, limit(rows, p)
}

func mM4(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "xalloc", "direct", "loops", "module", "at"}
	type ek struct{ c, d int32 }
	mult := map[ek]int32{}
	for _, c := range g.Callsites {
		mult[ek{c.CallerID, c.CalleeID}]++
	}
	direct := map[int32]int32{}
	for _, h := range g.Hazards {
		if h.Category() != "alloc" {
			continue
		}
		lp := strings.ToLower(h.Pattern())
		if h.Pattern() == "free" || strings.HasSuffix(lp, "free") {
			continue
		}
		direct[h.SymbolID] += h.N
	}
	levels := []map[int32]int32{direct}
	cur := direct
	for range 3 {
		next := map[int32]int32{}
		for k, v := range mult {
			if m, ok := cur[k.d]; ok && m != 0 {
				next[k.c] += v * m
			}
		}
		levels = append(levels, next)
		cur = next
	}
	total := map[int32]int32{}
	for _, lv := range levels {
		for k, v := range lv {
			total[k] += v
		}
	}
	var rows [][]fval
	for _, s := range g.syms() {
		if s.Kind() != "function" || !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		if total[s.ID] < 8 {
			continue
		}
		rows = append(rows, []fval{fStr(s.Name()), fI32(total[s.ID]),
			fI32(direct[s.ID]), fI32(s.NLoops),
			fOptStr(g.modName(s.ModuleID), s.ModuleID != 0), fStr(g.at(s))})
	}
	orderBy(rows, dI(1))
	return cols, limit(rows, p)
}

func mM5(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"from_module", "to_module", "edges", "calls", "distinct_targets"}
	type ek struct{ a, b int32 }
	type agg struct {
		calls, tgt int32
		t          map[int32]bool
		pairs      map[[2]int32]bool
	}
	m := map[ek]*agg{}
	for _, e := range g.Edges {
		if e.SameModule != 0 {
			continue
		}
		a, b := g.sym(e.CallerID), g.sym(e.CalleeID)
		if a == nil || b == nil {
			continue
		}
		k := ek{a.ModuleID, b.ModuleID}
		v := m[k]
		if v == nil {
			v = &agg{t: map[int32]bool{}, pairs: map[[2]int32]bool{}}
			m[k] = v
		}
		v.calls += e.NCalls
		if !v.t[e.CalleeID] {
			v.t[e.CalleeID] = true
			v.tgt++
		}
		v.pairs[[2]int32{e.CallerID, e.CalleeID}] = true
	}
	var keys []ek
	for k := range m {
		keys = append(keys, k)
	}
	sort.Slice(keys, func(i, j int) bool {
		if keys[i].a != keys[j].a {
			return keys[i].a < keys[j].a
		}
		return keys[i].b < keys[j].b
	})
	var rows [][]fval
	for _, k := range keys {
		if !likeMatch(g.modName(k.a), p.mod) {
			continue
		}
		v := m[k]
		rows = append(rows, []fval{fStr(g.modName(k.a)), fStr(g.modName(k.b)),
			fI32(int32(len(v.pairs))), fI32(v.calls), fI32(v.tgt)})
	}
	orderBy(rows, dI(2))
	return cols, limit(rows, p)
}

func mM6(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"header", "rebuilt_files", "sloc", "syms", "min_depth"}

	inc := map[int32][]int32{}
	for _, im := range g.Imports {
		if !im.HasTargetID {
			continue
		}
		inc[im.FileID] = append(inc[im.FileID], im.TargetID)
	}
	reach := map[int32]map[int32]int32{}
	for src, tgts := range inc {
		reach[src] = map[int32]int32{}

		for _, t := range tgts {
			reach[src][t] = 1
		}
	}
	frontier := inc
	for depth := int32(2); depth <= 4; depth++ {
		next := map[int32][]int32{}
		for src, hs := range frontier {
			for _, h := range hs {
				for _, t := range inc[h] {
					if t == src {
						continue
					}
					if _, ok := reach[src][t]; !ok {
						reach[src][t] = depth
						next[src] = append(next[src], t)
					}
				}
			}
		}
		if len(next) == 0 {
			break
		}
		frontier = next
	}
	_ = frontier
	count := map[int32]int32{}
	minD := map[int32]int32{}
	var order []int32
	for _, hs := range reach {
		for h, d := range hs {
			count[h]++
			if cur, ok := minD[h]; !ok || d < cur {
				minD[h] = d
			}
		}
	}
	seen := map[int32]bool{}
	for _, hs := range reach {
		for h := range hs {
			if !seen[h] {
				seen[h] = true
				order = append(order, h)
			}
		}
	}
	slices.Sort(order)
	var rows [][]fval
	for _, h := range order {
		f := g.fileOf2(h)
		if f == nil || !likeMatch(g.modName(f.ModuleID), p.mod) {
			continue
		}
		rows = append(rows, []fval{fStr(f.Path()), fI32(count[h]), fI32(f.Sloc),
			fI32(f.NSymbols), fI32(minD[h])})
	}
	orderBy(rows, dI(1), dI(2))
	return cols, limit(rows, p)
}

func mM7(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "depth", "loops", "calls", "divs", "libm", "brs",
		"sloc", "at"}
	var rows [][]fval
	for _, s := range g.syms() {
		if s.MaxLoopDepth <= 1 || !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		rows = append(rows, []fval{fStr(s.Name()), fI32(s.MaxLoopDepth),
			fI32(s.NLoops), fI32(s.CallInLoop), fI32(g.rv(s).DivInLoop),
			fI32(g.rv(s).LibmInLoop), fI32(s.BranchInLoop), fI32(s.Sloc), fStr(g.at(s))})
	}
	orderBy(rows, dI(1), dI(3))
	return cols, limit(rows, p)
}

func mM8(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "libm", "libm_in_loop", "loops", "depth", "sloc",
		"fan_in", "at"}
	var rows [][]fval
	for _, s := range g.syms() {
		if s.NLibm <= 0 || s.NLoops <= 0 {
			continue
		}
		if !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		rows = append(rows, []fval{fStr(s.Name()), fI32(s.NLibm),
			fI32(g.rv(s).LibmInLoop), fI32(s.NLoops), fI32(s.MaxLoopDepth),
			fI32(s.Sloc), fI32(s.FanIn), fStr(g.at(s))})
	}
	orderBy(rows, dI(2), dI(1))
	return cols, limit(rows, p)
}

func mM9(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "intrin", "hints", "restrict_", "builtins",
		"depth", "atomics", "at"}
	var rows [][]fval
	for _, s := range g.syms() {
		if s.NIntrinsic <= 0 && s.NLikely <= 0 {
			continue
		}
		if !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		rows = append(rows, []fval{fStr(s.Name()), fI32(s.NIntrinsic),
			fI32(s.NLikely), fI32(s.NRestrict), fI32(s.NBuiltin),
			fI32(s.MaxLoopDepth), fI32(s.NAtomic), fStr(g.at(s))})
	}
	orderBy(rows, dI(1), dI(2))
	return cols, limit(rows, p)
}

func mM10(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"struct_", "kind", "sz", "pad", "tail", "pct_waste",
		"lines64", "algn", "at"}
	var rows [][]fval
	for _, ss := range g.SSize {
		if ss.Exact != 1 || ss.TotalPad <= 0 {
			continue
		}
		s := g.sym(ss.SymbolID)
		if s == nil || !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		rows = append(rows, []fval{fStr(s.Name()), fStr(s.Kind()),
			fI32(ss.TotalSize), fI32(ss.TotalPad), fI32(ss.TailPad),
			fI32(pct(int64(ss.TotalPad), int64(ss.TotalSize))), fI32(ss.NLines64),
			fI32(ss.MaxAlign), fStr(g.at(s))})
	}
	orderBy(rows, dI(3))
	return cols, limit(rows, p)
}

func mM11(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"struct_", "sz", "pad", "lines64", "algn", "fields", "at"}
	nFields := map[int32]int32{}
	for _, l := range g.Layout {
		nFields[l.SymbolID]++
	}
	var rows [][]fval
	for _, ss := range g.SSize {
		if ss.Exact != 1 || ss.TotalSize < 65 || ss.TotalSize > 128 {
			continue
		}
		s := g.sym(ss.SymbolID)
		if s == nil || !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		rows = append(rows, []fval{fStr(s.Name()), fI32(ss.TotalSize),
			fI32(ss.TotalPad), fI32(ss.NLines64), fI32(ss.MaxAlign),
			fI32(nFields[ss.SymbolID]), fStr(g.at(s))})
	}
	orderBy(rows, cmpI(1))
	return cols, limit(rows, p)
}

func mM12(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"struct_", "fields", "ptrs", "fnptr", "arrays", "pct_ptr", "at"}
	type sh struct{ n, ptr, fnp, arr int32 }
	m := map[int32]*sh{}
	for _, l := range g.Layout {
		if l.InUnion != 0 || l.Depth != 0 {
			continue
		}
		s := g.sym(l.SymbolID)
		if s == nil || (s.Kind() != "struct" && s.Kind() != "union") {
			continue
		}
		e := m[l.SymbolID]
		if e == nil {
			e = &sh{}
			m[l.SymbolID] = e
		}
		e.n++
		if l.PtrDepth > 0 {
			e.ptr++
		}
		if l.IsFnptr == 1 {
			e.fnp++
		}
		if l.ArrayLen > 0 {
			e.arr++
		}
	}
	var rows [][]fval
	for _, s := range g.syms() {
		e := m[s.ID]
		if e == nil {
			continue
		}
		if e.n < 6 || float64(e.ptr)*100/float64(e.n) < 50 {
			continue
		}
		if !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		rows = append(rows, []fval{fStr(s.Name()), fI32(e.n), fI32(e.ptr),
			fI32(e.fnp), fI32(e.arr),
			fI32(pct(int64(e.ptr), int64(e.n))), fStr(g.at(s))})
	}
	orderBy(rows, dI(2))
	return cols, limit(rows, p)
}

func mM13(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "locals", "ptrs", "rec", "depth", "sloc",
		"params", "at"}
	var rows [][]fval
	for _, s := range g.syms() {
		if s.Kind() != "function" || s.NLocals <= 0 {
			continue
		}
		if !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		rows = append(rows, []fval{fStr(s.Name()), fI32(s.NLocals),
			fI32(s.NPtrLocals), fI32(s.IsRecursive), fI32(s.MaxLoopDepth),
			fI32(s.Sloc), fI32(s.NParams), fStr(g.at(s))})
	}
	orderBy(rows, dI(1), dI(3), cmpS(0))
	return cols, limit(rows, p)
}

func mM14(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "casts", "derefs", "shifts", "sizeofs", "mem", "io", "at"}
	var rows [][]fval
	for _, s := range g.syms() {
		if s.NCast <= 0 || !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		rows = append(rows, []fval{fStr(s.Name()), fI32(s.NCast), fI32(s.NDeref),
			fI32(s.NShift), fI32(s.NSizeof), fI32(s.NMemory), fI32(s.NIO),
			fStr(g.at(s))})
	}
	orderBy(rows, dI(1))
	return cols, limit(rows, p)
}

func macroQ(cols []string, pred func(m *Macro) bool, g *Graph, p params,
	fill func(s *Symbol, m *Macro) []fval,
	keys ...func(a, b []fval) int) ([]string, [][]fval) {
	bySym := make(map[int32]*Macro, len(g.Macros))
	for i := range g.Macros {
		bySym[g.Macros[i].SymbolID] = &g.Macros[i]
	}
	var rows [][]fval
	for _, s := range g.syms() {
		m := bySym[s.ID]
		if m == nil || !pred(m) {
			continue
		}
		if !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		rows = append(rows, fill(s, m))
	}
	orderBy(rows, then(keys...))
	return cols, limit(rows, p)
}

func mM15(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "uses", "params", "body_len", "multiline", "at"}
	return macroQ(cols, func(m *Macro) bool { return m.IsFunctionlike == 1 }, g, p,
		func(s *Symbol, m *Macro) []fval {
			return []fval{fStr(s.Name()), fI32(m.NUses), fI32(m.NParams),
				fI32(m.BodyLen), fI32(m.IsMultiline), fStr(g.at(s))}
		}, dI(1), func(a, b []fval) int { return -cmpI32(a[3].i, b[3].i) })
}

func mM16(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"expr", "sites", "files", "forms", "in_files"}
	type agg struct {
		sites  int32
		files  map[int32]bool
		forms  []string
		inFile []string
	}
	m := map[string]*agg{}
	var order []string
	for _, cb := range g.Cfgs {
		if cb.IsConfig != 1 {
			continue
		}
		a := m[cb.Expr()]
		if a == nil {
			a = &agg{files: map[int32]bool{}}
			m[cb.Expr()] = a
			order = append(order, cb.Expr())
		}
		a.sites++
		if !a.files[cb.FileID] {
			a.files[cb.FileID] = true
			if f := g.fileOf2(cb.FileID); f != nil && !containsStr(a.inFile, f.Basename()) {
				a.inFile = append(a.inFile, f.Basename())
			}
		}
		if !containsStr(a.forms, cb.Directive()) {
			a.forms = append(a.forms, cb.Directive())
		}
	}
	var rows [][]fval
	for _, e := range order {
		a := m[e]
		ok := false
		for fid := range a.files {
			if f := g.fileOf2(fid); f != nil && likeMatch(g.modName(f.ModuleID), p.mod) {
				ok = true
			}
		}
		if !ok {
			continue
		}
		rows = append(rows, []fval{fStr(e), fI32(a.sites), fI32(int32(len(a.files))),
			fStr(groupConcat(a.forms)), fStr(groupConcat(a.inFile))})
	}
	orderBy(rows, dI(1))
	return cols, limit(rows, p)
}

func mM17(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "small", "large", "defs", "files"}
	type grp struct {
		sloc   []int32
		files  []string
		fileID map[int32]bool
		defs   int32
	}
	m := map[string]*grp{}
	var order []string
	for _, s := range g.syms() {
		if s.Kind() != "function" {
			continue
		}
		f := g.fileOf(s.ID)
		if f == nil || f.IsTest != 0 {
			continue
		}
		mod := g.modName(s.ModuleID)
		if !likeMatch(mod, p.mod) {
			continue
		}
		if s.ModuleID >= 1 && int(s.ModuleID) <= len(g.Modules) {
			if k := g.Modules[s.ModuleID-1]; k.Kind() == "test" || k.Kind() == "tool" {
				continue
			}
		}
		if s.Name() == "main" || s.Name() == "LLVMFuzzerTestOneInput" ||
			s.Name() == "usage" || s.Name() == "help" {
			continue
		}
		gp := m[s.Name()]
		if gp == nil {
			gp = &grp{fileID: map[int32]bool{}}
			m[s.Name()] = gp
			order = append(order, s.Name())
		}
		gp.sloc = append(gp.sloc, s.Sloc)
		gp.defs++
		gp.fileID[f.ID] = true
		if !containsStr(gp.files, f.Basename()) {
			gp.files = append(gp.files, f.Basename())
		}
	}
	var rows [][]fval
	for _, n := range order {
		gp := m[n]
		lo, hi := int32(1<<30), int32(0)
		for _, v := range gp.sloc {
			if v < lo {
				lo = v
			}
			if v > hi {
				hi = v
			}
		}
		if gp.defs <= 1 || hi < 3*lo+3 {
			continue
		}
		if len(gp.files) == 1 && gp.files[0] == gp.files[0] {

		}
		if len(gp.fileID) >= 2 && minOf(gp.files) == maxOf(gp.files) {
			continue
		}
		rows = append(rows, []fval{fStr(n), fI32(lo), fI32(hi), fI32(gp.defs),
			fStr(groupConcat(distinctStrings(gp.files)))})
	}
	orderBy(rows, dWeighted([][3]int32{{1, 2}, {-1, 1}}))
	return cols, limit(rows, p)
}

func minOf(v []string) string {
	m := v[0]
	for _, x := range v {
		if x < m {
			m = x
		}
	}
	return m
}

func maxOf(v []string) string {
	m := v[0]
	for _, x := range v {
		if x > m {
			m = x
		}
	}
	return m
}

func mM18(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "fan_in", "sloc", "cyclo", "hidden", "at"}
	var rows [][]fval
	for _, s := range g.syms() {
		if s.Kind() != "function" || s.IsInline != 1 || s.IsStatic != 1 ||
			s.FanIn < 3 || s.Sloc < 4 {
			continue
		}
		if !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		rows = append(rows, []fval{fStr(s.Name()), fI32(s.FanIn), fI32(s.Sloc),
			fI32(s.Cyclomatic), fI32(s.FanIn * s.Sloc), fStr(g.at(s))})
	}
	orderBy(rows, dI(4), cmpS(0))
	return cols, limit(rows, p)
}

func mM19(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "cyclo", "sloc", "cmts", "doc", "nest", "fan_in", "at"}
	var rows [][]fval
	for _, s := range g.syms() {
		if s.Kind() != "function" || s.Cyclomatic < 20 ||
			s.NCommentLines*20 >= s.Sloc {
			continue
		}
		if !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		rows = append(rows, []fval{fStr(s.Name()), fI32(s.Cyclomatic),
			fI32(s.Sloc), fI32(s.NCommentLines), fI32(s.HasDoc),
			fI32(s.MaxNesting), fI32(s.FanIn), fStr(g.at(s))})
	}
	orderBy(rows, dI(1), cmpS(0))
	return cols, limit(rows, p)
}

func mM20(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"path", "rule", "objs", "srcs", "archives", "at_line"}
	var rows [][]fval
	for _, r := range g.MkRules {
		if r.NObjs+r.NSrcs < 2 {
			continue
		}
		rows = append(rows, []fval{fStr(r.Path()), fStr(r.Rule()), fI32(r.NObjs),
			fI32(r.NSrcs), fI32(r.UsesAr), fI32(r.Line)})
	}
	orderBy(rows, dSum(2, 3))
	return cols, limit(rows, p)
}

func mM21(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"module", "files", "parsed", "errors", "unclosed", "sloc",
		"fns", "includes", "ms"}
	type agg struct {
		files, parsed, errs, unc, sloc, fns, inc, ms int32
	}
	m := map[int32]*agg{}
	for i := range g.Files {
		f := &g.Files[i]
		a := m[f.ModuleID]
		if a == nil {
			a = &agg{}
			m[f.ModuleID] = a
		}
		a.files++
		a.parsed += f.Parsed
		a.errs += f.NParseErrors
		a.unc += f.NMissingNodes
		a.sloc += f.Sloc
		a.fns += f.NFunctions
		a.inc += f.NImports
		a.ms += int32(f.ParseMs + 0.5)
	}
	var rows [][]fval
	for i := range g.Modules {
		mod := &g.Modules[i]
		a := m[mod.ID]
		if a == nil || !likeMatch(mod.Name(), p.mod) {
			continue
		}
		rows = append(rows, []fval{fStr(mod.Name()), fI32(a.files), fI32(a.parsed),
			fI32(a.errs), fI32(a.unc), fI32(a.sloc), fI32(a.fns), fI32(a.inc),
			fI32(a.ms)})
	}
	orderBy(rows, dI(5))
	return cols, limit(rows, p)
}

func mM22(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "gotos", "labels", "cyclo", "sloc", "fan_in", "at"}
	var rows [][]fval
	for _, s := range g.syms() {
		if s.NGotos <= 3 {
			continue
		}
		f := g.fileOf(s.ID)
		if f == nil || f.IsTest != 0 {
			continue
		}
		if !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		rows = append(rows, []fval{fStr(s.Name()), fI32(s.NGotos), fI32(s.NLabels),
			fI32(s.Cyclomatic), fI32(s.Sloc), fI32(s.FanIn), fStr(g.at(s))})
	}
	orderBy(rows, dI(1), dI(3))
	return cols, limit(rows, p)
}

func mM23(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "nesting", "cyclo", "loops", "sloc", "fan_in", "at"}
	var rows [][]fval
	for _, s := range g.syms() {
		if s.MaxNesting <= 5 || s.Kind() != "function" {
			continue
		}
		f := g.fileOf(s.ID)
		if f == nil || f.IsTest != 0 {
			continue
		}
		if !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		rows = append(rows, []fval{fStr(s.Name()), fI32(s.MaxNesting),
			fI32(s.Cyclomatic), fI32(s.NLoops), fI32(s.Sloc), fI32(s.FanIn),
			fStr(g.at(s))})
	}
	orderBy(rows, dI(1), dI(2), cmpS(0))
	return cols, limit(rows, p)
}

func mM24(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "n_params", "sloc", "cyclo", "fan_in", "at"}
	var rows [][]fval
	for _, s := range g.syms() {
		if s.NParams <= 6 || s.Kind() != "function" {
			continue
		}
		f := g.fileOf(s.ID)
		if f == nil || f.IsTest != 0 {
			continue
		}
		if !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		rows = append(rows, []fval{fStr(s.Name()), fI32(s.NParams), fI32(s.Sloc),
			fI32(s.Cyclomatic), fI32(s.FanIn), fStr(g.at(s))})
	}
	orderBy(rows, dI(1), dI(4), cmpS(0))
	return cols, limit(rows, p)
}

func mM25(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "n_caller_modules", "fan_in", "cyclo", "sloc",
		"modules", "at"}
	var rows [][]fval
	for _, s := range g.syms() {
		if s.Kind() != "function" {
			continue
		}
		f := g.fileOf(s.ID)
		if f == nil || f.IsTest != 0 {
			continue
		}
		mods := map[int32]bool{}
		names := []string{}
		for _, e := range g.Edges {
			if e.CalleeID != s.ID || e.IsSelf != 0 {
				continue
			}
			cs := g.sym(e.CallerID)
			if cs == nil {
				continue
			}
			if !mods[cs.ModuleID] {
				mods[cs.ModuleID] = true
				if n := g.modName(cs.ModuleID); n != "" {
					names = append(names, n)
				}
			}
		}
		if len(mods) <= 5 {
			continue
		}
		if !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		rows = append(rows, []fval{fStr(s.Name()), fI32(int32(len(mods))),
			fI32(s.FanIn), fI32(s.Cyclomatic), fI32(s.Sloc),
			fStr(groupConcat(distinctStrings(names))), fStr(g.at(s))})
	}
	orderBy(rows, dI(1), dI(2), cmpS(0))
	return cols, limit(rows, p)
}

func mM26(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "magic_numbers", "float_literals", "cyclo", "sloc",
		"fan_in", "at"}
	var rows [][]fval
	for _, s := range g.syms() {
		if s.NMagic <= 10 || s.Kind() != "function" {
			continue
		}
		f := g.fileOf(s.ID)
		if f == nil || f.IsTest != 0 {
			continue
		}
		if !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		rows = append(rows, []fval{fStr(s.Name()), fI32(s.NMagic),
			fI32(s.NFloatLit), fI32(s.Cyclomatic), fI32(s.Sloc), fI32(s.FanIn),
			fStr(g.at(s))})
	}
	orderBy(rows, dI(1), dI(5), cmpS(0))
	return cols, limit(rows, p)
}

func mM27(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "reachable_fns", "transitive_callers", "fan_out",
		"cyclo", "module", "at"}
	var rows [][]fval
	for _, r := range g.Reach {
		s := g.sym(r.SymbolID)
		if s == nil || s.Kind() != "function" {
			continue
		}
		f := g.fileOf(s.ID)
		if f == nil || f.IsTest != 0 {
			continue
		}
		if !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		rows = append(rows, []fval{fStr(s.Name()), fI32(r.NTransitiveOut),
			fI32(r.NTransitive), fI32(s.FanOut), fI32(s.Cyclomatic),
			fOptStr(g.modName(s.ModuleID), s.ModuleID != 0), fStr(g.at(s))})
	}
	orderBy(rows, dI(1), cmpS(0))
	return cols, limit(rows, p)
}

func mM28(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"module", "mutable_globals", "static_ones", "writer_fns",
		"write_sites"}
	gs := map[int32]int32{}
	ss := map[int32]int32{}
	for _, gl := range g.Globals {
		if gl.IsConst != 0 {
			continue
		}
		f := g.fileOf2(gl.FileID)
		if f == nil || f.IsTest != 0 {
			continue
		}
		gs[f.ModuleID]++
		ss[f.ModuleID] += gl.IsStatic
	}
	wf := map[int32]int32{}
	ws := map[int32]int32{}
	for _, s := range g.syms() {
		if s.Kind() != "function" || g.rv(s).NGlobalWrite <= 0 {
			continue
		}
		f := g.fileOf(s.ID)
		if f == nil || f.IsTest != 0 {
			continue
		}
		wf[f.ModuleID]++
		ws[f.ModuleID] += g.rv(s).NGlobalWrite
	}
	var rows [][]fval
	for i := range g.Modules {
		mod := &g.Modules[i]
		if !likeMatch(mod.Name(), p.mod) {
			continue
		}
		if gs[mod.ID]+wf[mod.ID] <= 0 {
			continue
		}
		rows = append(rows, []fval{fStr(mod.Name()), fI32(gs[mod.ID]),
			fI32(ss[mod.ID]), fI32(wf[mod.ID]), fI32(ws[mod.ID])})
	}
	orderBy(rows, dI(1), dI(3))
	return cols, limit(rows, p)
}

func mM29(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "returns_", "fail_shapes", "null_checks", "gotos",
		"err_pct", "cyclo", "fan_in", "at"}
	var rows [][]fval
	for _, s := range g.syms() {
		if s.Kind() != "function" || s.NReturns < 4 {
			continue
		}
		if !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		shapes := g.rv(s).RetNull + g.rv(s).RetNeg + g.rv(s).RetZero
		var pv fval = fNull()
		if den := s.NReturns + s.NBranches; den != 0 {
			pv = fI32(pct(int64(shapes+s.NNullCheck), int64(den)))
		}
		rows = append(rows, []fval{fStr(s.Name()), fI32(s.NReturns), fI32(shapes),
			fI32(s.NNullCheck), fI32(s.NGotos), pv, fI32(s.Cyclomatic),
			fI32(s.FanIn), fStr(g.at(s))})
	}
	orderBy(rows, dI(5), dI(7), cmpS(0))
	return cols, limit(rows, p)
}

func numOrNeg(v fval) int64 {
	if v.kind == fkNull {
		return -1 << 40
	}
	return v.i
}

func mM30(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"fn", "sites", "with_sizeof", "raw_bytes", "callers",
		"pct_sizeof"}
	type agg struct {
		sites, with, raw int32
		callers          map[string]bool
	}
	m := map[string]*agg{}
	var order []string
	for _, a := range g.Allocs {
		s := g.sym(a.SymbolID)
		if s == nil || !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		e := m[a.Fn()]
		if e == nil {
			e = &agg{callers: map[string]bool{}}
			m[a.Fn()] = e
			order = append(order, a.Fn())
		}
		e.sites++
		if strings.Contains(a.SizeExpr(), "sizeof") {
			e.with++
		} else {
			e.raw++
		}
		e.callers[s.Name()] = true
	}
	var rows [][]fval
	for _, fn := range order {
		e := m[fn]
		pv := 0.0
		if e.sites != 0 {
			pv = math.Round(float64(e.with)*100/float64(e.sites)*10) / 10
		}
		rows = append(rows, []fval{fStr(fn), fI32(e.sites), fI32(e.with),
			fI32(e.raw), fI32(int32(len(e.callers))), fF(float64(pv))})
	}
	orderBy(rows, dI(1))
	return cols, limit(rows, p)
}

func mM31(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "copy_sites", "mem_ops_total", "loop_depth",
		"allocs_in_loop", "fan_in", "module", "at"}
	var rows [][]fval
	for _, s := range g.syms() {
		if s.Kind() != "function" || g.rv(s).NMemcpy < 3 {
			continue
		}
		if !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		rows = append(rows, []fval{fStr(s.Name()), fI32(g.rv(s).NMemcpy),
			fI32(s.NMemory), fI32(s.MaxLoopDepth), fI32(s.AllocInLoop),
			fI32(s.FanIn), fOptStr(g.modName(s.ModuleID), s.ModuleID != 0),
			fStr(g.at(s))})
	}
	orderBy(rows, dI(1), dI(5), cmpS(0))
	return cols, limit(rows, p)
}

func mM32(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "uses", "body_len", "expanded_bytes", "multiline",
		"params", "at"}
	return macroQ(cols, func(m *Macro) bool { return m.IsFunctionlike == 1 && m.NUses > 0 },
		g, p, func(s *Symbol, m *Macro) []fval {
			return []fval{fStr(s.Name()), fI32(m.NUses), fI32(m.BodyLen),
				fI32(m.NUses * m.BodyLen), fI32(m.IsMultiline), fI32(m.NParams),
				fStr(g.at(s))}
		}, dI(3))
}

func mM33(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"struct_", "sz", "pad", "ptr_fields", "fnptr_fields",
		"includers", "lines64", "at"}
	ptr := map[int32]int32{}
	fnp := map[int32]int32{}
	for _, l := range g.Layout {
		if l.PtrDepth > 0 && l.InUnion == 0 && l.Depth == 0 {
			ptr[l.SymbolID]++
		}
		if l.IsFnptr == 1 {
			fnp[l.SymbolID]++
		}
	}

	seenIn := map[int32]map[int32]bool{}
	for _, im := range g.Imports {
		if !im.HasTargetID {
			continue
		}
		if seenIn[im.TargetID] == nil {
			seenIn[im.TargetID] = map[int32]bool{}
		}
		seenIn[im.TargetID][im.FileID] = true
	}
	incl := make(map[int32]int32, len(seenIn))
	for t, set := range seenIn {
		incl[t] = int32(len(set))
	}
	var rows [][]fval
	for _, ss := range g.SSize {
		if ss.Exact != 1 {
			continue
		}
		s := g.sym(ss.SymbolID)
		if s == nil {
			continue
		}
		f := g.fileOf(s.ID)
		if f == nil || f.Ext() != ".h" {
			continue
		}
		if !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		rows = append(rows, []fval{fStr(s.Name()), fI32(ss.TotalSize),
			fI32(ss.TotalPad), fI32(ptr[ss.SymbolID]), fI32(fnp[ss.SymbolID]),
			fI32(incl[f.ID]), fI32(ss.NLines64), fStr(g.at(s))})
	}
	orderBy(rows, dI(5), dI(3), dI(1))
	return cols, limit(rows, p)
}

func mM34(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"path", "module", "n_markers", "todo", "fixme", "xxx",
		"hack", "bug", "unsafe", "deprecated", "sloc", "risk"}
	types := []string{"TODO", "FIXME", "XXX", "HACK", "BUG", "UNSAFE",
		"DEPRECATED"}
	type agg struct {
		n  int32
		by map[string]int32
	}
	m := map[int32]*agg{}
	for _, mk := range g.Markers {
		a := m[mk.FileID]
		if a == nil {
			a = &agg{by: map[string]int32{}}
			m[mk.FileID] = a
		}
		a.n++
		a.by[mk.Kind()]++
	}
	var rows [][]fval
	for i := range g.Files {
		f := &g.Files[i]
		a := m[f.ID]
		if a == nil {
			continue
		}
		if !likeMatch(g.modName(f.ModuleID), p.mod) {
			continue
		}
		mod := g.modName(f.ModuleID)
		if mod == "" {
			mod = "(none)"
		}
		row := []fval{fStr(f.Path()), fStr(mod), fI32(a.n)}
		for _, t := range types {
			row = append(row, fI32(a.by[t]))
		}
		row = append(row, fI32(f.Sloc), fI32(f.TotalRisk))
		rows = append(rows, row)
	}
	orderBy(rows, dI(2), dI(10))
	return cols, limit(rows, p)
}

func mM35(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"shape", "copies", "sloc", "cyclo", "params",
		"duplicated_sloc", "modules"}
	type grp struct {
		copies, sloc, cyc, params, dup int32
		mods                           map[int32]bool
	}
	m := map[string]*grp{}
	var order []string
	for _, s := range g.syms() {
		if s.Kind() != "function" || s.Sloc < 10 || s.Cyclomatic < 3 {
			continue
		}
		f := g.fileOf(s.ID)
		if f == nil || f.IsTest != 0 {
			continue
		}
		if !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		sig := strconv.Itoa(int(s.Sloc)) + "/" + strconv.Itoa(int(s.Cyclomatic)) +
			"/" + strconv.Itoa(int(s.NParams)) + "/" + strconv.Itoa(int(s.NCalls))
		gp := m[sig]
		if gp == nil {
			gp = &grp{mods: map[int32]bool{}}
			m[sig] = gp
			order = append(order, sig)
		}
		gp.copies++
		gp.sloc = s.Sloc
		gp.cyc = s.Cyclomatic
		gp.params = s.NParams
		gp.dup += s.Sloc
		gp.mods[s.ModuleID] = true
	}
	sort.Strings(order)
	var rows [][]fval
	for _, sig := range order {
		gp := m[sig]
		if gp.copies <= 1 {
			continue
		}
		var names []string
		for mid := range gp.mods {
			names = append(names, g.modName(mid))
		}

		sort.Strings(names)
		rows = append(rows, []fval{fStr(sig), fI32(gp.copies), fI32(gp.sloc),
			fI32(gp.cyc), fI32(gp.params), fI32(gp.dup),
			fStr(groupConcat(distinctStrings(names)))})
	}
	orderBy(rows, dI(5), dI(1))
	return cols, limit(rows, p)
}

func mM36(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "aliasing_pairs", "restrict_hints", "params",
		"cyclo", "depth", "fan_in", "at"}
	type grp struct {
		typ map[string]int32
		n   int32
	}
	m := map[int32]*grp{}
	for _, pr := range g.Params {
		if pr.IsRef != 1 || pr.Type() == "" {
			continue
		}
		gp := m[pr.SymbolID]
		if gp == nil {
			gp = &grp{typ: map[string]int32{}}
			m[pr.SymbolID] = gp
		}
		gp.typ[pr.Type()]++
		gp.n++
	}
	var rows [][]fval
	for _, s := range g.syms() {
		gp := m[s.ID]
		if gp == nil || s.Kind() != "function" || s.NRestrict != 0 {
			continue
		}
		f := g.fileOf(s.ID)
		if f == nil || f.IsTest != 0 {
			continue
		}
		if !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		pairs := int32(0)
		for _, c := range gp.typ {
			if c >= 2 {
				pairs += c
			}
		}
		if pairs == 0 {
			continue
		}
		rows = append(rows, []fval{fStr(s.Name()), fI32(pairs), fI32(s.NRestrict),
			fI32(s.NParams), fI32(s.Cyclomatic), fI32(s.MaxLoopDepth),
			fI32(s.FanIn), fStr(g.at(s))})
	}
	orderBy(rows, dI(1), dI(5), dI(6), cmpS(0))
	return cols, limit(rows, p)
}

func mM37(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"path", "module", "sloc", "fns", "types", "cyclo", "worst",
		"risk", "includes", "risk_per_100_sloc"}
	var rows [][]fval
	for i := range g.Files {
		f := &g.Files[i]
		if f.IsTest != 0 || f.Sloc <= 0 {
			continue
		}
		mod := g.modName(f.ModuleID)
		if !likeMatch(mod, p.mod) {
			continue
		}
		if mod == "" {
			mod = "(none)"
		}
		rows = append(rows, []fval{fStr(f.Path()), fStr(mod), fI32(f.Sloc),
			fI32(f.NFunctions), fI32(f.NTypes), fI32(f.TotalCyclo),
			fI32(f.MaxCyclo), fI32(f.TotalRisk), fI32(f.NImports),
			fI32(pct(int64(f.TotalRisk), int64(f.Sloc)))})
	}
	orderBy(rows, dI(7), dI(2))
	return cols, limit(rows, p)
}

func mM38(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "fan_in", "fan_out", "cyclo", "sloc", "documented",
		"params", "declared_in", "at"}
	inHeader := map[string]int32{}
	for _, d := range g.Decls {
		if f := g.fileOf2(d.FileID); f != nil && f.Ext() == ".h" {
			inHeader[d.Name()]++
		}
	}
	var rows [][]fval
	for _, s := range g.syms() {
		if s.Kind() != "function" || s.IsStatic != 0 || s.IsInline != 0 {
			continue
		}
		f := g.fileOf(s.ID)
		if f == nil || f.Ext() != ".c" || inHeader[s.Name()] == 0 {
			continue
		}
		if !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		nDecl := int32(0)
		for _, d := range g.Decls {
			if d.Name() == s.Name() {
				nDecl++
			}
		}
		rows = append(rows, []fval{fStr(s.Name()), fI32(s.FanIn), fI32(s.FanOut),
			fI32(s.Cyclomatic), fI32(s.Sloc), fI32(s.HasDoc), fI32(s.NParams),
			fI32(nDecl), fStr(g.at(s))})
	}
	orderBy(rows, dI(1), dI(4), cmpS(0))
	return cols, limit(rows, p)
}

func mM39(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "macro_params", "body_len", "uses", "multiline",
		"do_while", "at"}
	return macroQ(cols, func(m *Macro) bool { return m.IsFunctionlike == 1 }, g, p,
		func(s *Symbol, m *Macro) []fval {
			sp := strings.ReplaceAll(m.Body(), " ", "")
			dw := int32(0)
			if strings.Contains(sp, "do{") && strings.Contains(sp, "while(") {
				dw = 1
			}
			return []fval{fStr(s.Name()), fI32(m.NParams), fI32(m.BodyLen),
				fI32(m.NUses), fI32(m.IsMultiline), fI32(dw), fStr(g.at(s))}
		}, cmpI(3), func(a, b []fval) int { return -cmpI32(a[2].i, b[2].i) })
}

func mM40(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "locals", "uninitialised", "const_locals",
		"in_loop", "cyclo", "sloc", "at"}
	type agg struct {
		n, uninit, cst, loop int32
	}
	m := map[int32]*agg{}
	for _, l := range g.Locals {
		a := m[l.SymbolID]
		if a == nil {
			a = &agg{}
			m[l.SymbolID] = a
		}
		a.n++
		if l.HasInit == 0 {
			a.uninit++
		}
		a.cst += l.IsConst
		a.loop += l.InLoop
	}
	var rows [][]fval
	for _, s := range g.syms() {
		a := m[s.ID]
		if a == nil || s.Kind() != "function" {
			continue
		}
		f := g.fileOf(s.ID)
		if f == nil || f.IsTest != 0 {
			continue
		}
		if !likeMatch(g.modName(s.ModuleID), p.mod) || a.uninit < 3 {
			continue
		}
		rows = append(rows, []fval{fStr(s.Name()), fI32(a.n), fI32(a.uninit),
			fI32(a.cst), fI32(a.loop), fI32(s.Cyclomatic), fI32(s.Sloc),
			fStr(g.at(s))})
	}
	orderBy(rows, dI(2), dI(5), cmpS(0))
	return cols, limit(rows, p)
}

func mM41(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"lock_name", "held_by_fns", "acquire_sites", "n_files",
		"cyclo_under_lock", "worst_cyclo", "io_under_lock", "allocs_under_lock",
		"modules"}
	type agg struct {
		fns                   map[int32]bool
		fileSet               map[int32]bool
		sites                 int32
		cyc, worst, io, alloc int32
		mods                  []string
	}
	m := map[string]*agg{}
	var order []string
	for i, l := range g.Locks {
		s := g.sym(l.SymbolID)
		if s == nil || !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		a := m[l.Name()]
		if a == nil {
			a = &agg{fns: map[int32]bool{}, fileSet: map[int32]bool{}}
			m[l.Name()] = a
			order = append(order, l.Name())
		}
		_ = i
		a.sites++
		a.fns[s.ID] = true
		a.cyc += s.Cyclomatic
		if s.Cyclomatic > a.worst {
			a.worst = s.Cyclomatic
		}
		a.io += s.NIO
		a.alloc += s.NAlloc
		a.mods = appendDistinct(a.mods, g.modName(s.ModuleID))
		if f := g.fileOf(s.ID); f != nil {
			a.fileSet[f.ID] = true
		}
	}
	var rows [][]fval
	for _, n := range order {
		a := m[n]
		rows = append(rows, []fval{fStr(n), fI32(int32(len(a.fns))), fI32(a.sites),
			fI32(int32(len(a.fileSet))), fI32(a.cyc), fI32(a.worst), fI32(a.io), fI32(a.alloc),
			fStr(groupConcat(distinctStrings(a.mods)))})
	}
	orderBy(rows, dI(2), dI(4))
	return cols, limit(rows, p)
}

func mM42(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"typedef_name", "underlying", "at"}
	var rows [][]fval
	for _, s := range g.syms() {
		if s.Kind() != "typedef" || !s.HasReturnType {
			continue
		}
		rt := s.ReturnType()
		if !strings.Contains(rt, "*") && !strings.Contains(rt, "]") {
			continue
		}
		if !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		rows = append(rows, []fval{fStr(s.Name()), fStr(rt), fStr(g.at(s))})
	}
	orderBy(rows, cmpS(0))
	return cols, limit(rows, p)
}

func mM43(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"path", "n_static_inline", "sloc", "total_fan_in",
		"worst_fan_in", "cyclo", "times_included"}
	incl := map[int32]int32{}
	for _, im := range g.Imports {
		if im.HasTargetID {
			incl[im.TargetID]++
		}
	}
	type agg struct {
		n, sloc, fan, worst, cyc int32
	}
	m := map[int32]*agg{}
	for _, s := range g.syms() {
		if s.Kind() != "function" || s.IsStatic != 1 || s.IsInline != 1 {
			continue
		}
		f := g.fileOf(s.ID)
		if f == nil || f.Ext() != ".h" {
			continue
		}
		if !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		a := m[f.ID]
		if a == nil {
			a = &agg{}
			m[f.ID] = a
		}
		a.n++
		a.sloc += s.Sloc
		a.fan += s.FanIn
		if s.FanIn > a.worst {
			a.worst = s.FanIn
		}
		a.cyc += s.Cyclomatic
	}
	var rows [][]fval
	for _, fid := range sortedIDs(m) {
		a := m[fid]
		f := g.fileOf2(fid)
		rows = append(rows, []fval{fStr(f.Path()), fI32(a.n), fI32(a.sloc),
			fI32(a.fan), fI32(a.worst), fI32(a.cyc), fI32(incl[fid])})
	}
	orderBy(rows, dI(3), dI(1))
	return cols, limit(rows, p)
}

func sortedIDs[V any](m map[int32]V) []int32 {
	out := make([]int32, 0, len(m))
	for k := range m {
		out = append(out, k)
	}
	slices.Sort(out)
	return out
}

func mM44(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"module", "fns", "returns_null", "returns_neg",
		"returns_zero", "mixed", "pct_mixed"}
	type agg struct{ fns, nul, neg, zer, mixed int32 }
	m := map[int32]*agg{}
	for _, s := range g.syms() {
		if s.Kind() != "function" || s.NReturns == 0 {
			continue
		}
		f := g.fileOf(s.ID)
		if f == nil || f.IsTest != 0 {
			continue
		}
		if !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		a := m[f.ModuleID]
		if a == nil {
			a = &agg{}
			m[f.ModuleID] = a
		}
		a.fns++
		a.nul += b2i(g.rv(s).RetNull > 0)
		a.neg += b2i(g.rv(s).RetNeg > 0)
		a.zer += b2i(g.rv(s).RetZero > 0)
		shapes := 0
		for _, v := range [][2]int32{{g.rv(s).RetNull, 0}, {g.rv(s).RetNeg, 0}, {g.rv(s).RetZero, 0}} {
			if v[0] > 0 {
				shapes++
			}
		}
		a.mixed += b2i(shapes >= 2)
	}
	var rows [][]fval
	for _, mid := range sortedIDs(m) {
		a := m[mid]
		if a.fns < 8 {
			continue
		}
		rows = append(rows, []fval{fStr(g.modName(mid)), fI32(a.fns),
			fI32(a.nul), fI32(a.neg), fI32(a.zer), fI32(a.mixed),
			fI32(pct(int64(a.mixed), int64(a.fns)))})
	}
	orderBy(rows, dI(6), dI(1), cmpS(0))
	return cols, limit(rows, p)
}

func mM45(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"path", "module", "extern_decls", "also_in_a_header", "sloc"}
	hdrNames := map[string]bool{}
	for _, d := range g.Decls {
		if f := g.fileOf2(d.FileID); f != nil && f.Ext() == ".h" {
			hdrNames[d.Name()] = true
		}
	}
	srcN := map[int32]int32{}
	inhN := map[int32]int32{}
	seen := map[int32]map[string]bool{}
	for _, d := range g.Decls {
		f := g.fileOf2(d.FileID)
		if f == nil || f.Ext() != ".c" {
			continue
		}
		srcN[d.FileID]++
		if hdrNames[d.Name()] {
			if seen[d.FileID] == nil {
				seen[d.FileID] = map[string]bool{}
			}
			if !seen[d.FileID][d.Name()] {
				seen[d.FileID][d.Name()] = true
				inhN[d.FileID]++
			}
		}
	}
	var rows [][]fval
	for _, fid := range sortedIDs(srcN) {
		if srcN[fid] < 3 {
			continue
		}
		f := g.fileOf2(fid)
		mod := g.modName(f.ModuleID)
		if !likeMatch(mod, p.mod) {
			continue
		}
		if mod == "" {
			mod = "(none)"
		}
		rows = append(rows, []fval{fStr(f.Path()), fStr(mod), fI32(srcN[fid]),
			fI32(inhN[fid]), fI32(f.Sloc)})
	}
	orderBy(rows, dI(2), dI(4))
	return cols, limit(rows, p)
}

func mM46(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "module", "epoll", "uring", "kqueue", "waits", "et",
		"oneshot", "write_ready", "err_flags", "rearms", "deregs", "eagain",
		"eintr", "calls", "at"}
	bySym := map[int32][]string{}
	for i := range g.EvOps {
		e := &g.EvOps[i]
		if !containsStr(bySym[e.SymbolID], e.Fn()) {
			bySym[e.SymbolID] = append(bySym[e.SymbolID], e.Fn())
		}
	}
	var rows [][]fval
	for _, s := range g.syms() {
		if g.rv(s).NEpoll+g.rv(s).NUring+g.rv(s).NKqueue <= 0 {
			continue
		}
		mod := g.modName(s.ModuleID)
		if !likeMatch(mod, p.mod) {
			continue
		}
		if mod == "" {
			mod = "(none)"
		}
		var calls fval = fNull()
		if l := bySym[s.ID]; len(l) > 0 {
			calls = fStr(groupConcat(l))
		}
		rows = append(rows, []fval{fStr(s.Name()), fStr(mod), fI32(g.rv(s).NEpoll),
			fI32(g.rv(s).NUring), fI32(g.rv(s).NKqueue), fI32(g.rv(s).NEventWait), fI32(g.rv(s).NEtReg),
			fI32(g.rv(s).NOneshotReg), fI32(g.rv(s).NWriteReady), fI32(g.rv(s).NErrFlag),
			fI32(g.rv(s).NRearm), fI32(g.rv(s).NDereg), fI32(g.rv(s).NEagain), fI32(g.rv(s).NEintr),
			calls, fStr(g.at(s)), fI32(s.Cyclomatic)})
	}
	orderBy(rows, dSum(2, 3, 4), dI(len(cols)))
	for i, r := range rows {
		rows[i] = r[:len(cols)]
	}
	return cols, limit(rows, p)
}

func mM47(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"name", "waits", "cyclo", "cog", "nest", "loop_depth",
		"calls_in_loop", "io_in_loop", "branches_in_loop", "sloc", "fan_in", "at"}
	var rows [][]fval
	for _, s := range g.syms() {
		if g.rv(s).NEventWait <= 0 || !likeMatch(g.modName(s.ModuleID), p.mod) {
			continue
		}
		rows = append(rows, []fval{fStr(s.Name()), fI32(g.rv(s).NEventWait),
			fI32(s.Cyclomatic), fI32(s.Cognitive), fI32(s.MaxNesting),
			fI32(s.MaxLoopDepth), fI32(s.CallInLoop), fI32(s.IOInLoop),
			fI32(s.BranchInLoop), fI32(s.Sloc), fI32(s.FanIn), fStr(g.at(s))})
	}
	orderBy(rows, dI(2), dI(9))
	return cols, limit(rows, p)
}

func mM48(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"module", "fns", "epoll_fns", "uring_fns", "kqueue_fns",
		"wait_fns", "edge_triggered", "watches_errors", "handles_eintr",
		"sets_nonblocking", "eintr_blind", "et_unprepared", "leaks_instance",
		"api_calls"}
	type agg struct{ c [13]int32 }
	m := map[int32]*agg{}
	for _, s := range g.syms() {
		if g.rv(s).NEpoll+g.rv(s).NUring+g.rv(s).NKqueue <= 0 {
			continue
		}
		f := g.fileOf(s.ID)
		if f == nil {
			continue
		}
		a := m[f.ModuleID]
		if a == nil {
			a = &agg{}
			m[f.ModuleID] = a
		}
		a.c[0]++
		a.c[1] += b2i(g.rv(s).NEpoll > 0)
		a.c[2] += b2i(g.rv(s).NUring > 0)
		a.c[3] += b2i(g.rv(s).NKqueue > 0)
		a.c[4] += b2i(g.rv(s).NEventWait > 0)
		a.c[5] += b2i(g.rv(s).NEtReg > 0)
		a.c[6] += b2i(g.rv(s).NErrFlag > 0)
		a.c[7] += b2i(g.rv(s).NEintr > 0)
		a.c[8] += b2i(g.rv(s).NNonblockSet > 0)
		a.c[9] += b2i(g.rv(s).NEventWait > 0 && g.rv(s).NEintr == 0)
		a.c[10] += b2i(g.rv(s).NEtReg > 0 && g.rv(s).NNonblockSet == 0)
		a.c[11] += b2i(g.rv(s).NEventCreate > 0 && g.rv(s).NEventDestroy == 0)
		a.c[12] += g.rv(s).NEpoll + g.rv(s).NUring + g.rv(s).NKqueue
	}
	var rows [][]fval
	for _, mid := range sortedIDs(m) {
		a := m[mid]
		mod := g.modName(mid)
		if !likeMatch(mod, p.mod) {
			continue
		}
		if mod == "" {
			mod = "(none)"
		}
		row := []fval{fStr(mod)}
		for _, v := range a.c {
			row = append(row, fI32(v))
		}
		rows = append(rows, row)
	}
	orderBy(rows, dI(13), dI(1))
	return cols, limit(rows, p)
}

var retNegNS = []string{"stdio.h", "sys/socket.h", "sys/mman.h", "sys/wait.h",
	"sys/uio.h", "unistd.h", "fcntl.h", "dirent.h", "stdio.h"}

func mM49(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"module", "ns", "call_sites", "fns", "distinct_calls"}
	type agg struct {
		mod, ns string
		sites   int32
		fns     map[int32]bool
		calls   map[string]bool
	}
	type key struct {
		file int32
		ns   string
	}
	m := map[key]*agg{}
	var keys []key
	for _, a := range g.APIUses {
		f := g.fileOf2(a.FileID)
		if f == nil {
			continue
		}
		if !likeMatch(g.modName(f.ModuleID), p.mod) {
			continue
		}

		mod := g.modName(a.FileID)
		if !likeMatch(mod, p.mod) {
			continue
		}
		k := key{a.FileID, a.NS()}
		e := m[k]
		if e == nil {
			e = &agg{fns: map[int32]bool{}, calls: map[string]bool{}, mod: mod,
				ns: a.NS()}
			m[k] = e
			keys = append(keys, k)
		}
		e.sites++
		e.fns[a.SymbolID] = true
		e.calls[a.Fn()] = true
	}
	sort.Slice(keys, func(i, j int) bool {
		if keys[i].file != keys[j].file {
			return keys[i].file < keys[j].file
		}
		return keys[i].ns < keys[j].ns
	})
	var rows [][]fval
	for _, k := range keys {
		e := m[k]
		mod := e.mod
		if mod == "" {
			mod = "(none)"
		}
		rows = append(rows, []fval{fStr(mod),
			fStr(e.ns), fI32(e.sites), fI32(int32(len(e.fns))),
			fI32(int32(len(e.calls)))})
	}
	orderBy(rows, dI(2))
	return cols, limit(rows, p)
}

func mM50(g *Graph, p params) ([]string, [][]fval) {
	cols := []string{"module", "fns", "unchecked_returns", "unchecked_conversions",
		"ctype_ub", "varargs_unclosed", "mmap_unchecked", "api_call_sites"}
	type agg struct {
		mod                            string
		fns, ur, uc, cu, vu, mu, sites int32
	}

	m := map[int32]*agg{}
	order := make([]int32, 0, 64)
	for _, a := range g.APIUses {
		s := g.sym(a.SymbolID)
		if s == nil {
			continue
		}
		mod := g.modName(a.FileID)
		if !likeMatch(mod, p.mod) {
			continue
		}
		e := m[a.FileID]
		if e == nil {
			e = &agg{mod: mod}
			m[a.FileID] = e
			order = append(order, a.FileID)
		}
		e.sites++
		if containsStr(retNegNS, a.NS()) && g.rv(s).NRetNegCheck == 0 {
			e.ur++
		}
		switch a.Fn() {
		case "strtol", "strtoll", "strtoul", "strtoull", "strtod":
			if !(g.rv(s).NErrnoZero > 0 && g.rv(s).NEndptr > 0) {
				e.uc++
			}
		}
		if a.NS() == "ctype.h" && g.rv(s).NUcharCast == 0 {
			e.cu++
		}
		if a.NS() == "stdarg.h" && g.rv(s).NVaEnd == 0 {
			e.vu++
		}
		if a.NS() == "sys/mman.h" && g.rv(s).NMapFailed == 0 {
			e.mu++
		}
	}
	seen := map[int32]map[int32]bool{}
	for _, a := range g.APIUses {
		mod := g.modName(a.FileID)
		if !likeMatch(mod, p.mod) {
			continue
		}
		if seen[a.FileID] == nil {
			seen[a.FileID] = map[int32]bool{}
		}
		if !seen[a.FileID][a.SymbolID] {
			seen[a.FileID][a.SymbolID] = true
			m[a.FileID].fns++
		}
	}
	keys := sortedIDs(m)
	var rows [][]fval
	for _, fid := range keys {
		e := m[fid]
		mod := e.mod
		if mod == "" {
			mod = "(none)"
		}
		rows = append(rows, []fval{fStr(mod), fI32(e.fns), fI32(e.ur),
			fI32(e.uc), fI32(e.cu), fI32(e.vu), fI32(e.mu), fI32(e.sites)})
	}
	orderBy(rows, dI(7))
	return cols, limit(rows, p)
}

var queries = []qentry{
	{"untrusted-frontier", "Parses attacker bytes AND does pointer/size arithmetic", "ANSWERS the functions where a memory-safety bug is actually reachable.\nACT this is the CWE-190 shape: a length from the wire, a shift or a cast,\n     then a copy. Review these before anything else on the risk list.\nMISLEADS io counts RAW descriptor calls only; a function fed by a caller\n     that did the read is just as exposed and is invisible here.", qQ1},
	{"stack-exhaustion", "Self-recursive functions: unbounded input depth is a stack DoS", "ANSWERS where a deeply nested input can exhaust the C stack.\nACT every one of these needs a depth cap that is TESTED at the cap.\nMISLEADS DIRECT self-recursion only. Mutual recursion through two\n     functions, or through a function pointer, does not appear here.", qQ2},
	{"ownership-review", "Allocates but never frees in the same function", "ANSWERS where allocation ownership crosses a function boundary.\nACT each row must have a NAMED owner that frees it on EVERY path --\n     including the early returns and the goto-out ladder.\nMISLEADS this is a REVIEW list, not a leak list. Transferring ownership\n     to the caller is the normal C idiom and looks identical here.", qQ3},
	{"allocator-mixing", "Files that use libc malloc AND a project allocator", "ANSWERS which files split their memory across two accounting systems.\nACT pick ONE per file. A project allocator usually exists to track or cap\n     usage, and a libc allocation in the same file is invisible to it.\nMISLEADS a project allocator is recognised by NAME SHAPE (anything ending\n     in alloc/free/strdup), so an unconventionally named one is missed and\n     an unrelated `list_free` is counted. Also, mixing is sometimes right:\n     tracked buffers through the wrapper, private scratch through libc.", qQ4},
	{"alloc-per-iteration", "malloc/realloc inside a loop body", "ANSWERS which loops pay the allocator once per item.\nACT hoist the allocation, or reserve capacity before the loop.\nMISLEADS a realloc-grow loop is amortised O(1) and belongs here anyway;\n     the count is of SITES, and one site in a hot loop beats ten cold ones.", qQ5},
	{"bypass-tax", "Allocates BEFORE it knows the fast path applies", "ANSWERS which functions pay setup cost on inputs they then refuse.\nACT probe FIRST, allocate second. This is the classic bypass candidate.\nMISLEADS an allocation before a loop is usually just the output buffer,\n     which has to be allocated up front and is not a tax at all.", qQ6},
	{"race-surface", "Mutable, non-atomic, non-const file-scope state", "ANSWERS what two threads could be writing at the same time.\nACT every row needs a lock, an atomic, a thread-local, or a written proof\n     that only one thread ever touches it.\nMISLEADS it does not know which modules are threaded. The last column is\n     the only evidence offered: how many functions in the same module use\n     a concurrency primitive at all.", qQ7},
	{"per-element-dispatch", "A switch INSIDE a loop: type dispatch paid once per element", "ANSWERS where a loop re-decides the same thing on every iteration.\nACT hoist the switch out, or specialise the loop per case.\nMISLEADS a bytecode interpreter's dispatch loop is exactly this shape and\n     is correct by design. So is a state machine.", qQ8},
	{"loop-invariant-strlen", "strlen() inside a loop: accidental O(n^2)", "ANSWERS where a length is recomputed that cannot have changed.\nACT hoist it, or carry the length beside the string.\nMISLEADS a strlen over a SHORT string is a few cycles, and a loop whose\n     body mutates the string has to recompute it.", qQ9},
	{"error-shape-mix", "Functions that report failure in more than one shape", "ANSWERS where a caller can plausibly check the wrong thing.\nACT a function returning both NULL and -1 is one that callers get wrong\n     roughly half the time. Pick one convention per function and document\n     it in the header, where the caller is actually looking.\nMISLEADS returning 0 for success AND 0 as a legitimate value is the worst\n     case of all and is completely invisible here.", qQ10},
	{"dead-code", "Nothing in this tree calls these", "ANSWERS what might be deletable.\nACT grep the name as a STRING before deleting anything: a registry entry,\n     a config value or a reflective call keeps a symbol alive with no edge\n     to show for it.\nMISLEADS this is the query most likely to be wrong, and `graph-blindspots`\n     measures by how much. Public symbols are excluded because a caller\n     outside this tree cannot be seen at all, so what is left is private\n     and unreferenced -- a much weaker claim than dead.", qQ11},
	{"nonreentrant-under-threads", "a libc call with a shared static buffer, in a function that also touches threads", "ANSWERS CERT CON33-C and MSC24-C, which clang-tidy states as a per-call\n     rule and cppcheck barely states at all: `localtime`, `strerror`,\n     `getenv`, `basename` and friends return a pointer into one static\n     buffer. Single-threaded that is correct and cheap. In a function that\n     also creates threads or takes locks it is a data race that corrupts\n     the OTHER thread's result, silently, under load.\nACT use the _r form -- localtime_r, strerror_r, getpwnam_r -- or copy the\n     result before releasing the lock. `patterns` names exactly which\n     calls, so the fix is mechanical.\nMISLEADS a function that touches threads is not necessarily called from\n     more than one, and pthread_create in main() next to a getenv() at\n     startup is fine. This sees categories in the same body, not the\n     happens-before between them.", qQ12},
	{"unchecked-conversion-on-an-io-path", "atoi/strtol in a function that also reads input", "ANSWERS CERT ERR34-C, which flawfinder and clang-tidy report on every\n     `atoi` in the tree. `atoi(\"42\")` on a literal is fine. `atoi` on\n     bytes that just came off a socket or a file returns 0 for the string\n     \"0\" and for garbage alike, and sets no errno to distinguish them.\n     The graph supplies the missing half: whether the same function also\n     performs I/O.\nACT use strtol with an end pointer and check both `end` and `errno`, or\n     reject the input outright. `conversions` names the exact calls;\n     `returns_value` says whether the function can even report a failure\n     to its caller, and a 0 there means the error has nowhere to go.\nMISLEADS co-occurrence in one body is not dataflow -- a function may read\n     a file and separately parse a constant. A wrapper that validates\n     before calling this one makes the row correct and harmless, and that\n     wrapper is not visible in the row.", qQ13},
	{"buffer-overflow-surface", "sprintf/strcpy/strcat/gets without bounds (CERT STR31-C)", "ANSWERS where unbounded buffer operations are used: sprintf, strcpy,\n     strcat, gets. Each can write past the end of a buffer if the input\n     is larger than expected.\nACT use snprintf, strncpy (or strlcpy), strncat, fgets. Check return values.\nMISLEADS a sprintf on a buffer known to be large enough is safe, but the\n     graph cannot prove the buffer size.", qQ14},
	{"format-string-injection", "printf with non-literal format string (CERT STR30-C)", "ANSWERS where printf/fprintf/sprintf is called with a format string that is\n     not a string literal, enabling format string attacks if the string\n     contains user-controlled %s or %n.\nACT use printf('%s', user_string) not printf(user_string).\nMISLEADS a format string from a trusted constant array is safe. The graph\n     sees the call but not the argument source.", qQ15},
	{"memory-leak-surface", "malloc/calloc/realloc without matching free (CERT MEM31-C)", "ANSWERS where a function allocates memory but has no matching free, which\n     is a leak if the allocation outlives the function and is not stored.\nACT free the allocation before returning, or document ownership transfer.\nMISLEADS a function that allocates and returns the pointer to the caller is\n     not leaking; the caller is responsible. The graph sees alloc/free in\n     the same function, not across functions.", qQ16},
	{"double-free-surface", "free called more than once on same pointer (CERT MEM40-C)", "ANSWERS where a function has more free calls than alloc calls, which may\n     indicate a double-free if the same pointer is freed on multiple paths.\nACT track the pointer state; set to NULL after free and check before.\nMISLEADS a function that frees pointers allocated in other functions has\n     more frees than allocs by design. The imbalance is a signal, not proof.", qQ17},
	{"null-deref-surface", "Pointer dereference without null check (CERT ERR30-C)", "ANSWERS where a function dereferences pointers but has no null checks,\n     which means a NULL pointer will crash the program.\nACT check for NULL before dereferencing, especially after malloc/calloc.\nMISLEADS a pointer known to be non-null (from a trusted source) does not\n     need a check. The graph sees n_null_check but not which pointers.", qQ18},
	{"integer-overflow-surface", "Arithmetic without bounds checking (CERT INT32-C)", "ANSWERS where integer arithmetic is performed without overflow checking,\n     which is UB for signed integers and wraps for unsigned.\nACT use checked arithmetic (__builtin_add_overflow) or validate inputs.\nMISLEADS arithmetic on known-small constants is safe. The graph counts\n     arithmetic sites but not the operand ranges.", qQ19},
	{"division-by-zero-surface", "Division without zero check (CERT INT33-C)", "ANSWERS where division is performed but the function has no comparison\n     that could be a zero-check on the divisor.\nACT check for zero before dividing.\nMISLEADS a division by a constant is safe. The graph sees n_arith but\n     cannot distinguish division from other arithmetic.", qQ20},
	{"switch-no-default", "Switch without a default case (MISRA-C 16.4)", "ANSWERS where a switch statement has no default case, so unhandled values\n     fall through silently. MISRA-C requires a default in every switch.\nACT add a default case, even if it only asserts or does nothing.\nMISLEADS a switch over an exhaustive enum may not need a default, but a\n     future value will be silently ignored.", qQ21},
	{"race-condition-surface", "Shared static variable accessed from concurrent context (CERT CON33-C)", "ANSWERS where a function reads/writes a static variable and also touches\n     threads, locks, or atomics, indicating potential data races.\nACT protect the shared variable with a mutex, or use thread-local storage.\nMISLEADS a static variable set once at startup and only read afterward is\n     safe. The graph sees co-occurrence, not the happens-before relation.", qQ22},
	{"signal-handler-unsafe", "Unsafe function called inside a signal handler (CERT SIG30-C)", "ANSWERS where a function that may be called as a signal handler calls\n     non-async-signal-safe functions (malloc, printf, syslog).\nACT only call async-signal-safe functions inside signal handlers.\nMISLEADS relies on function name matching (contains 'sig' or 'handler'),\n     which is crude; a function registered via signal(2) at runtime with a\n     non-obvious name is not detected.", qQ23},
	{"infinite-loop", "Functions with loops but no return statements (CERT MSC53-C)", "ANSWERS where a function has loops but no return paths at all, which may\n     indicate an infinite loop with no exit condition.\nACT ensure there is a break, return, or condition that exits the loop.\nMISLEADS an event loop or a scheduler is intentionally infinite. The graph\n     sees n_loops and n_returns but not the exit condition. A function that\n     exits via a called function's longjmp is not captured.", qQ24},
	{"unused-return-value", "Function whose return value is ignored by callers (CERT EXP12-C)", "ANSWERS where a function returns a value but its callers do not check it,\n     so errors are silently lost. fan_in says how many call sites exist;\n     a high fan_in with no error-checking callers is a systemic problem.\nACT check the return value at every call site, or use a must-check attribute.\nMISLEADS a function that returns void has no return value to check. The\n     graph sees fan_in but not whether individual callers check the result.", qQ25},
	{"macro-side-effect", "Heavily-used function-like macro that may evaluate arguments twice (CERT PRE31-C)", "ANSWERS the function-like macros with the most use sites -- each use\n     passes its arguments through the macro body once PER REFERENCE in\n     that body, so an argument with side effects (i++, f()) is\n     evaluated however many times the body names it. `uses` is the\n     call-shaped reference count from call resolution.\nACT convert the top rows to static inline functions: identical\n     runtime cost, but types checked, breakpoints possible, and the\n     double-evaluation hazard gone.\nMISLEADS a macro that references each argument exactly once is safe\n     and lands here anyway (the body text is captured in macros.body\n     -- read it before acting); a macro used only as a non-call token\n     shows zero uses.", qQ26},
	{"vtable-risk", "Functions reached through function pointers or dynamic member calls", "ANSWERS where runtime target ambiguity is densest: the reads through\n     `ops->`-style members and `(*fp)()` calls that a static call graph\n     cannot resolve. Every one is a site whose callee is decided at runtime.\nACT audit the dispatch site: is the function-pointer slot ever written with\n     something other than the one obvious initializer? If so, the edge here\n     is a security boundary, not an abstraction.\nMISLEADS counts CALL SITES, not distinct targets, and the brace scanner\n     sees the `->`-shaped member call syntax only; a struct passed around\n     and invoked through a local alias (`ops->read` copied into a local\n     `fp`) shows up as the alias's direct call instead.", qQ27},
	{"header-scope-ratio", "User-header vs system-header include ratio per file", "ANSWERS which files lean almost entirely on system headers (<...>) and so\n     carry little project-local coupling -- and which pull in mostly user\n     headers (\"...\"), marking them as tightly coupled to the tree.\nACT a file at ~0%% user headers is often a portability shim; a file at\n     100%% user headers that is itself widely included deserves a look for\n     layering violations.\nMISLEADS a `<system>` include that RESOLVES inside the tree is counted as\n     user here (the analyzer treats project headers on the include path as\n     internal), so the ratio is about the include SPELLING, not about where\n     the file actually lives.", qQ28},
	{"recursion-loops", "Mutually recursive function pairs (a calls b, b calls a)", "ANSWERS the call pairs that can recurse unboundedly even though no single\n     function calls itself. Each row is a 2-cycle in the resolved edge set.\nACT add a depth cap or an iteration guard on the LOWER-LEVEL member of the\n     pair; the higher one is where the recursion is entered.\nMISLEADS finds direct 2-cycles only. Cycles of length >= 3 (a->b->c->a)\n     need a full SCC walk and do NOT appear; self-recursion is covered by\n     `stack-exhaustion`, not here. Edges are name-resolved, so two functions\n     that share one name are conflated.", qQ29},
	{"global-state-mutation", "Non-static, non-const globals: the state every translation unit shares", "ANSWERS the file-scope objects without internal linkage (no `static`), so\n     any translation unit that declares them extern can mutate them. Where\n     `race-surface` asks which mutable globals two THREADS could clobber\n     (it includes statics and singles out non-atomic ones), this asks\n     which globals merely EXIST as cross-TU seams -- the ones that make a\n     function untestable in isolation and a refactor a hunt through every\n     declaring file.\nACT make them static and route access through one setter, or move them\n     into a context struct passed explicitly.\nMISLEADS the brace scanner cannot see WHICH functions write the global,\n     only that it exists and is shared (`race-surface` is the same data\n     through a thread-race lens); `has_init` being 0 does not prove there\n     is no initializer (a forward-declared extern has none by\n     construction). Config-style `extern const` tables are correctly\n     excluded (is_const). The scanner records every file-scope declarator\n     including function parameters of that shape, so private locals and\n     pointer parameters can surface as rows; shared mutable file-scope\n     objects are the rows that matter.", qQ30},
	{"unreferenced-includes", "Headers included but none of their functions are ever called", "ANSWERS the #include lines whose target file's functions have zero\n     resolved callers anywhere in the tree -- the include-graph shape that\n     slows rebuilds without contributing edges.\nACT drop the include if the header only carried types you no longer use;\n     otherwise expect one of the covered-by-macro / config-gated cases.\nMISLEADS a header used ONLY for types, macros, or constants looks dead\n     here by construction (the scanner sees function calls only); a header\n     whose functions are CALLED THROUGH POINTERS is also invisible. This is\n     a candidate list, not a delete list.", qQ31},
	{"blast-radius", "Symbols with the largest transitive caller sets", "ANSWERS which functions, if changed, can disturb the most of the tree:\n     the count of DISTINCT functions that can reach this symbol through\n     resolved edges at any depth.\nACT treat the top rows as API changes requiring a caller sweep: every\n     row's callers are the blast zone. For a public entry point the number\n     is meaningless by design -- see MISLEADS.\nMISLEADS `n_transitive` counts callers THROUGH RESOLVED EDGES ONLY; a\n     symbol called dynamically (function pointer) or across a name\n     collision undercounts, and a widely-included header's inline helpers\n     are undercounted for the same reason. The pass is an SCC fold over\n     the whole graph (exact on the edges that exist); `call-chain-depth`\n     in METRICS is the same table read DOWNWARD.", qQ32},
	{"cross-file-struct-coupling", "Struct types that span translation units via layout surface", "ANSWERS the struct definitions whose shape (size, pointer fields, padding)\n     makes them load-bearing across files: a struct this large or this\n     pointer-heavy, defined once, is almost certainly passed between\n     translation units and is a compatibility surface.\nACT treat layout changes (field reorder, pointer widening) as ABI changes\n     for every included_by file; the pad columns show where the wasted\n     bytes are.\nMISLEADS the brace scanner cannot see WHERE a struct is instantiated; this\n     ranks by DEFINED shape, not by measured usage, so a huge struct that\n     never leaves its file appears here too. `exact=0` sizes (unknown field\n     types) are excluded rather than guessed.", qQ33},
	{"extern-linkage-density", "Translation units leaning on extern declarations", "ANSWERS where file boundaries are load-bearing on bare extern promises:\n     the count of extern-declared globals a file relies on, and the volume\n     of calls resolved only because a prototype declared the callee (no\n     definition in this unit).\nACT high extern + low definition density is where a symbol rename or a\n     signature change breaks the tree without the compiler naming every\n     victim; consider moving the shared declarations into a header.\nMISLEADS n_external_calls counts calls whose callee was declared but not\n     defined in the unit -- libc and POSIX calls dominate any realistic\n     file, so compare DENSITY across files, not the raw number.", qQ34},
	{"cross-tu-signature-drift", "One function name, two different definitions across TUs", "ANSWERS function names defined with >= 2 different signatures across\n     translation units: UB per C99 6.2.7 (MISRA 8.3). The linker picks\n     one definition and every caller of the other shape is miscompiled.\nACT pick one signature; rename or delete the other definition. The row\n     names every file involved.\nMISLEADS typedef-equivalent types compare different textually, so a\n     benign `int foo(int)` vs `int foo(int32_t)` pair is reported;\n     K&R definitions yield empty signature text and are excluded, and a\n     static fn in one file plus an extern fn of the same name in another\n     is NOT a link conflict yet still reads as drift here.", qQ35},
	{"linkage-scope-mismatch", "External-linkage functions whose callers all live in one TU", "ANSWERS non-static functions whose resolved callers all sit in one\n     translation unit: they should be static (MISRA 8.7, cppcheck). An\n     external-linkage symbol is a coupling surface for the whole\n     binary; a one-TU usage pattern says the author forgot the keyword.\nACT make it static; if fan_in is also 0, `dead-code` owns the deletion\n     question instead.\nMISLEADS name-based resolution undercounts callers, so a function used\n     from a second TU through a macro or a function pointer reads as\n     one-TU here; fnptr-dispatched users are invisible; a header inline\n     absorbed elsewhere never appears. When in doubt, the compiler's\n     own -Wmissing-prototypes is the tiebreaker.", qQ36},
	{"risky-process-apis", "Sites of dangerous process/temp APIs (CERT ENV33-C, flawfinder)", "ANSWERS reachable sites of the dangerous process and temp-file API set:\n     system/popen/exec for process boundaries, mktemp/tmpnam/tempnam for\n     race-prone temp files, access for TOCTOU-prone checks.\nACT replace mktemp with mkstemp; interrogate every system/popen -- each\n     is a command-injection review item when the argument is not a\n     constant; prefer execve with an explicit argv over execl/execvp\n     when the argument list is built at runtime.\nMISLEADS the capture is the call scanner, independent of resolution, so\n     libc calls that would otherwise classify as external still appear;\n     the denylist is the fixed set above -- rand/setenv are NOT captured\n     and are absent by design (their risk is caller-context, which this\n     query does not model); errno-checking callers are not distinguished.", qQ37},
	{"hardcoded-secret-candidates", "Credential-shaped string literals (OWASP G07)", "ANSWERS string literals at least 12 chars long whose text names a\n     credential (password, token, api_key, secret, bearer, jwt, ...) --\n     the literal that a committed secret looks like.\nACT rotate and move to a secret manager; never commit the literal.\nMISLEADS a format string or test fixture containing the WORD token/pass\n     reads as a candidate (the filter is the literal's own text, not its\n     use); values over 200 chars are truncated at capture; a secret\n     built from parts or read from an env var is invisible here. This\n     is a candidate list, not a verdict.", qQ38},
	{"include-cycles", "User headers that include each other, directly or via a chain", "ANSWERS user headers that include each other: the include graph is a\n     DAG in any well-formed project, so a cycle means the headers are\n     mutually dependent and the build order is an accident of include\n     guards.\nACT break the cycle with a forward declaration or by shrinking one\n     header; rows name both endpoints and the cycle length.\nMISLEADS include guards make cycles harmless at compile time, so this\n     is a maintainability smell, not a defect; the cycle set is\n     computed at BUILD time (bounded DFS, depth cap 8) into the\n     include_cycles table -- a recursive-CTE version of this query\n     enumerated paths rather than cycles and never finished on large\n     trees; is_relative=1 means user \"...\" includes, and a <...>\n     include that resolves in-tree is excluded from the walk.", qQ39},
	{"const-cast-away", "Casts that drop const from const-declared names (CERT EXP05-C)", "ANSWERS `(T*)name` casts applied to a name declared const: the\n     const-qualified promise is stripped by the cast, and any write\n     through the result is UB in the caller's face.\nACT remove the cast, or drop const from the declaration if the\n     function genuinely mutates (and say why).\nMISLEADS the const test is against the local/param declaration in the\n     SAME function: a const GLOBAL or a const from another translation\n     unit is invisible here; `(void*)` casts and casts of expressions\n     (not bare names) are not counted; a cast of a name that is NOT\n     const-declared reads clean by construction.", qQ40},
	{"fnptr-blindspot-callers", "Functions used only through &fn -- invisible to the call graph", "ANSWERS functions with fan_in 0 whose address is taken somewhere:\n     they ARE used, but every call goes through a function pointer, so\n     dead-code and every fan-in-based number understate them.\nACT read these as live API surface; a fnptr-dispatched function is a\n     plugin point or a table-driven dispatch entry.\nMISLEADS &fn text capture catches address-takes in function bodies; an\n     address taken in a struct initializer at file scope (the dominant\n     dispatch-table pattern) is NOT here -- dispatch-table-orphan owns\n     those rows, and dead-code must be read with both pages open.", qQ41},
	{"extern-symbol-asymmetry", "Declared in a prototype, never defined in the tree", "ANSWERS names with a prototype/extern declaration but no definition\n     anywhere in the tree: either the definition lives in a library\n     this run skipped (fine), or the symbol is promised but missing\n     (a link error waiting for the first caller).\nACT for each row decide: library boundary (ignore) or genuinely\n     missing (define or delete the prototype).\nMISLEADS a definition behind `#ifdef` that the scan excluded reads as\n     missing; static functions are excluded from the definition side\n     only when their name matches -- a same-named static in one file\n     does NOT satisfy an extern promise in another; libc prototypes in\n     system headers are not scanned (only this tree's files are).", qQ42},
	{"toctou-access-open", "access(X) then open(X) on the same variable (CERT POS01-C)", "ANSWERS functions that both access(X) and open(X) with the same\n     variable: the permission check and the use are two system calls,\n     and the file can be swapped between them. The window is the whole\n     race.\nACT open first, then fstat the descriptor; never trust access for\n     security decisions.\nMISLEADS same-function variable-name pairing, not data flow: access on\n     a path built from a different variable than the open is missed,\n     and access+open on a CONSTANT path (no race on most filesystems\n     in practice) reads the same as the race; `faccessat` with\n     AT_EACCESS is a different capture and is absent.", qQ43},
	{"lock-imbalance", "Acquires a lock more often than it releases it", "ANSWERS the functions where an early return or a goto-out ladder can\n     leave a mutex held: acquire sites outnumber release sites in one\n     body. The next caller to take that lock blocks forever -- and if\n     the lock is taken under load first, the hang looks like a load\n     problem, not a code problem.\nACT pair every acquire with a release on EVERY path, or move to\n     pthread_mutex_trylock with explicit unlock on the failure path.\nMISLEADS counts SITES, not paths: two acquires and two releases can\n     still leak (both releases behind the same `if`), and a function\n     whose contract is 'returns with the lock held' (an allocator's\n     arena lock, a lazy initializer) is correct and lands here anyway.\n     A release inside a called cleanup function is invisible.", qQ44},
	{"lock-under-io", "A lock is held across a call that can sleep or block I/O", "ANSWERS where a function both takes a lock and performs raw descriptor\n     I/O in the same body: read/write/recv/send/mmap while holding a\n     pthread mutex. Every other thread wanting that lock stalls for the\n     duration of the I/O -- the classic latency cliff under load, and\n     with a non-recursive mutex plus a nested acquisition, a deadlock.\nACT shrink the critical section: copy what is needed under the lock,\n     release, then do the I/O. If the I/O must be covered, document why\n     and bound it (timeout, O_NONBLOCK).\nMISLEADS co-occurrence in one body is not ordering: the I/O may run\n     strictly before the first acquire or after the last release, and\n     this cannot see which. Buffered stdio (fprintf) is excluded here\n     on purpose -- it lives in its own query family; a blocking call\n     reached THROUGH a callee while the lock is held is invisible.", qQ45},
	{"memcpy-sizeof-mismatch", "Copy whose size argument names neither dst nor src", "ANSWERS the copy sites where the SIZE expression dereferences a\n     buffer that is neither argument: memcpy(a, b, sizeof(c)) copies\n     by c's width -- CERT ARR38-C's shape when a, b and c have\n     different element sizes. `size_buf` is the identifier the size\n     expression references (from its sizeof), '' when it names none.\nACT read every row: the fix is a size naming THE DESTINATION, or an\n     explicit MIN of both. Prefer strlcpy / memcpy_s where available.\nMISLEADS textual, not semantic: sizeof(*dst) vs sizeof(struct x) can\n     be equal; copying into a larger dst is legal; a length VARIABLE\n     as size reads clean here but is exactly where an unchecked value\n     bites -- this query finds the WRONG-BUFFER sites, not every bad\n     copy. Argument capture stops at one paren level.", qQ46},
	{"alloc-without-sizeof", "malloc(n * k) with no sizeof in the size expression", "ANSWERS allocation sites whose size expression names no sizeof at all:\n     malloc(count * 4) hard-codes the element width, malloc(len) may be\n     confusing bytes with elements, and neither survives the element\n     type changing under it. Each row is the exact line to re-derive.\nACT write sizeof(*p) (or sizeof(T)) explicitly, and prefer calloc for\n     arrays so the overflow check is someone else's already-written bug\n     fix.\nMISLEADS a byte-oriented API (a raw network buffer, a string + 1) is\n     CORRECT without sizeof and will dominate this list in most trees;\n     a size expression built through a project macro (`s_malloc`,\n     `ALLOC_ARRAY`) hides its sizeof from this scan entirely.", qQ47},
	{"global-writer-concentration", "Functions that WRITE file-scope state, ranked by how much they touch", "ANSWERS which functions mutate shared file-scope objects, and which\n     globals are written from the most places. `race-surface` says a\n     global EXISTS and is mutable; this says WHO actually writes it --\n     the half that turns 'could race' into 'here is the commit that\n     must take the lock'.\nACT every writer of a hot global is a serialization point: batch the\n     writes, shard the state, or make the field atomic.\nMISLEADS same-file globals only -- writes through an extern declared\n     in a header are invisible, so cross-TU writers undercount; a\n     local variable shadowing a global name is counted as the global;\n     and `g->field = x` through a pointer parameter reads as a write\n     only when the base name matches a captured global.", qQ48},
	{"truncating-cast-flow", "Fixed-width narrowing casts on data that came from wide sources", "ANSWERS `(uint32_t)x`-style casts to a STRICTLY narrower fixed-width\n     type in functions that also do heavy arithmetic or I/O -- the\n     places where a 64-bit length, hash or offset silently becomes 32\n     bits. The wrap is not UB, which is exactly why nothing complains:\n     the value just comes back wrong on input above 4 GiB.\nACT before casting, range-check and reject; after casting, never use\n     the wide original again. Prefer size_t end-to-end.\nMISLEADS a cast to uint8_t for serialization into a wire format is\n     correct and common; the scan cannot know the value fits. Only\n     fixed-width targets are counted -- casts to int/long are\n     platform-dependent and deliberately absent.", qQ49},
	{"signed-size-compare", "Signed value compared against a size or sizeof result", "ANSWERS comparisons of the form `if (i < sizeof(b))` / `while (n <=\n     len)` where the left side is a signed local or parameter: the\n     comparison promotes the signed value to size_t, so -1 becomes\n     SIZE_MAX and the bounds check PASSES for the one input that must\n     fail it (CERT INT31-C).\nACT make the index size_t, or compare in the signed domain against a\n     checked cast of the size.\nMISLEADS the left operand being declared signed is necessary but not\n     sufficient: a value proven non-negative before the compare makes\n     the row harmless, and the scan sees declarations, not proofs.", qQ50},
	{"variadic-format-forwarder", "Variadic function forwarding to a vprintf-family call", "ANSWERS the wrappers that turn caller-supplied arguments into formatted\n     output: variadic definitions containing v?snprintf/v?printf/syslog.\n     Whether %n is reachable from outside depends ENTIRELY on whether\n     these forwarders pass through a caller-controlled format string --\n     they are the chokepoints worth auditing, because every other\n     printf-shaped call in the tree funnels through a handful of them.\nACT audit each: the format argument should be a literal or a fixed\n     table entry, never a parameter forwarded verbatim.\nMISLEADS a wrapper that hardcodes its own literal format ('%s') is safe\n     and indistinguishable here from one forwarding the caller's format\n     through; the format STRING itself is blanked during scanning (it is\n     a literal), so its content is not inspected.", qQ51},
	{"dispatch-table-orphan", "Referenced ONLY in file-scope initializers: live but zero fan-in", "ANSWERS functions kept alive exclusively by a dispatch-table entry at\n     file scope -- an initializer reference (`static cmd_t cmds[] =\n     {&get, &set}`) or a generated-table argument\n     (`MAKE_CMD(...,getCommand,...)`). No body contains the use, so\n     dead-code and every fan-in-based number read zero while the\n     function is very much alive: these are the plugin points of a\n     table-driven C program.\nACT treat as public API: renaming one breaks a TABLE, silently, at\n     runtime. Any signature change needs the table's owning module in\n     the review. `refs` says how many tables list it.\nMISLEADS the capture is textual (argument position, file scope, macro\n     bodies skipped), so a same-named DATA object referenced in an\n     initializer can attach to a function of that name after pruning;\n     a table entry spelled through a project macro's PARAMETER is not\n     seen (macro bodies are excluded on purpose); and a function whose\n     address is taken BOTH in a table and in a body appears here only\n     for its body-level rows.", qQ52},
	{"error-path-frees", "Allocations whose frees sit only behind error branches", "ANSWERS functions that allocate, free, and branch heavily: the shape\n    where the free list covers the error ladder but a NEW success-path\n    early return skips it. Unlike ownership-review (which flags 'no\n    free at all'), this finds the functions where a future edit is most\n    likely to introduce a leak, because the discipline exists but is\n    one return away from breaking. `allocs` counts direct\n    malloc/calloc/realloc/alloca sites; project wrappers are invisible\n    to it.\nACT when editing one of these, trace every new return against the free\n    ladder -- or convert to goto-cleanup, which makes skipping it\n    impossible.\nMISLEADS a heuristic by construction: alloc==free==1 with two branches\n    is usually fine; the ranking surfaces DENSITY of exits vs frees,\n    not an actual missing free. Transfers of ownership (returning the\n    buffer) look identical, and frees reached through a wrapper\n    function do not count, so a disciplined function using one can\n    read as frees=0 -- those land in ownership-review instead.", qQ53},
	{"realloc-idiom-risk", "p = realloc(p, n): the old block is lost on failure", "ANSWERS where a failed realloc leaks the buffer it was resizing.\nACT assign to a TEMPORARY: `tmp = realloc(p, n); if (!tmp) { /* p is still\n     valid */ } else p = tmp;`.\nMISLEADS matched textually on `x = realloc(x,`, so a realloc through a wrapper,\n     or one whose result lands in a different variable, is missed. A realloc to\n     a SMALLER size does not fail in practice, so some rows are noise.\n", qQ54},
	{"alloc-size-off-by-one", "An allocation sized from strlen() with no room for the terminator", "ANSWERS where the size expression is a string length and nothing adds one.\nACT MEM35-C: `strlen(s) + 1`, or use strdup, which cannot get this wrong.\nMISLEADS only sites whose size text contains `strlen` AND no `+` at all are\n     listed, so `strlen(s) + sizeof(hdr)` is excluded -- correctly, since that\n     may be a counted buffer. The size is TEXT, not a value: a length computed\n     two statements earlier is invisible here.\n", qQ55},
	{"resource-leak-surface", "Descriptors and FILEs opened on more paths than they are closed", "ANSWERS where an open outnumbers its close inside one function.\nACT FIO42-C: every open needs a close on EVERY path, including the error\n     returns and the goto-out ladder. Prefer one cleanup label.\nMISLEADS a function that opens and hands the descriptor to its caller is\n     correct and looks identical. Opens and closes reached through a wrapper\n     are not counted, and a resource closed by the caller reads as a leak.\n", qQ56},
	{"unchecked-alloc-result", "Allocates and never compares anything to NULL", "ANSWERS functions where no allocation result is checked at all.\nACT ERR33-C: on a 25k-function tree this list is long and mostly test code and\n     wrappers -- narrow it with --module and read the high fan_in rows first.\nMISLEADS `n_null_check` counts `== NULL` and `if (!x)` only. A check inside a\n     macro (`serverAssert(x)`), a helper, or an `assert(x)` is not seen, and a\n     wrapper that checks centrally makes every one of its callers look guilty.\n", qQ57},
	{"vla-from-input", "A variable-length array whose extent someone else chose", "ANSWERS stack allocations sized by a non-constant, worst where the length\n     arrives from I/O or from a string operation.\nACT ARR32-C: bound the length before the declaration, or heap-allocate. A VLA\n     has no failure mode -- it simply writes past the frame.\nMISLEADS the filter is `n_io>0 OR n_memory>0 OR recursive`, a PROXY for\n     \"the length may be attacker-influenced\", not evidence of it. A VLA sized\n     from a local constant is still listed if the function also does I/O.\n", qQ58},
	{"free-then-deref", "A name is freed and then dereferenced later in the same body", "ANSWERS the MEM30-C use-after-free shape that one function can contain.\nACT every row needs a read of the code: the dereference may sit on a path where\n     the pointer was reassigned, which is correct.\nMISLEADS textual and scope-limited. It cannot see that the two are on mutually\n     exclusive branches, or that the pointer was reassigned between them.\n     `p = malloc(...)` after a free is excluded; `*p = ...` is counted. A free\n     at the bottom of a loop that reallocates at the top is the common false\n     positive -- and the loop column is the only hint offered.\n", qQ59},
	{"weak-randomness", "rand() and friends where unpredictability might matter", "ANSWERS MSC30-C: the places a predictable generator is used.\nACT anything key-, token-, nonce-, or salt-related here is a finding.\n     Everything else -- shuffling test data, jitter, backoff -- is fine and is\n     still listed.\nMISLEADS presence, not reachability. Nothing here says the value is observable\n     by an attacker; the `io` and `exec` columns are the only evidence offered.\n", qQ60},
	{"shift-count-risk", "Shifts by an identifier rather than a literal", "ANSWERS INT34-C: shift counts the reader cannot check at the shift site.\nACT a count that can be negative, or >= the width of the promoted left operand,\n     is undefined. Clamp at the source, not at every shift.\nMISLEADS the great majority of these are correct bit-twiddling with a constant\n     named for readability. This ranks where to LOOK, and the count is of SITES,\n     not of bugs.\n", qQ61},
	{"errno-dependence", "Where the errno error channel is load bearing", "ANSWERS the functions whose error reporting depends on a global that any\n     intervening call can overwrite.\nACT ERR30-C: for each row, check that nothing runs between the failing call and\n     the errno read. Ranked by read count, because that is where a clobber hurts.\nMISLEADS it cannot tell a correct read from a stale one -- only that the code\n     consults errno at all. A function that reads errno correctly on every path\n     and one that reads it after three intervening printf calls look identical.\n", qQ62},
	{"env-trust-boundary", "getenv(): the process environment as an input", "ANSWERS every place the environment is read.\nACT the environment is attacker-controlled wherever the process was started by\n     a less trusted one. A length from getenv needs the same bounds treatment\n     as a length from a socket.\nMISLEADS presence only. A path from getenv used with an explicit length is fine;\n     one concatenated into a command or a path is not. The `exec` and `mem`\n     columns are the triage hint, not a verdict.\n", qQ63},
	{"assert-with-side-effect", "An assert() that does work, which NDEBUG deletes", "ANSWERS assertions whose removal would change behaviour.\nACT move the work out of the assert and assert on its RESULT. Under NDEBUG the\n     assert vanishes and so does whatever it did.\nMISLEADS the match is a shape (`=`, `++`, memcpy, malloc, printf inside the\n     parens), so `assert(x == y)` is excluded correctly but `assert(f(&x))` with\n     a read-only f is still counted. Test files are excluded; test helpers that\n     live in source files are not.\n", qQ64},
	{"lock-order-inversion", "Two locks taken in both orders by different functions", "ANSWERS the CON35-C / POS51-C deadlock shape.\nACT for each row decide whether the two functions can run at the same time.\n     If yes, this is a deadlock waiting on scheduling; if no, it is an invariant\n     someone should write down next to the lock.\nMISLEADS order is inferred from LINE NUMBER inside a function, not from control\n     flow: two acquires on one line, or one inside a conditional that actually\n     runs first, are ordered by text. Only lock-SHAPED identifiers are recorded,\n     so a lock held in a variable (`myLockAcquire(lock, ...)`) is invisible and\n     every ordering involving it is missed entirely.\n", qQ65},
	{"false-sharing-risk", "Two or more fields sharing one 64-byte cache line", "ANSWERS where independent writes to one struct will invalidate each other.\nACT only matters if different threads write different fields of one instance.\n     Aligning the hot field is the cheap fix; splitting the struct is the real\n     one.\nMISLEADS nothing here knows which fields are written by which thread. The\n     `conc_fns_in_module` column is the only evidence offered: how many\n     functions in the same module touch a concurrency primitive at all. Offsets\n     are LP64 and reported only where the layout was computed exactly.\n", qQ66},
	{"unterminated-strncpy", "strncpy/strncat sized with sizeof: no terminator guaranteed", "ANSWERS the STR31-C / STR32-C shape: a copy that fills the buffer exactly and\n     adds no NUL when the source is that long or longer.\nACT `strncpy(d, s, sizeof d - 1); d[sizeof d - 1] = '\\0';`, or use a function\n     that always terminates.\nMISLEADS matched on the SIZE ARGUMENT TEXT, so `strncpy(d, s, n)` with a runtime\n     n -- which can overrun for a different reason -- is absent. A size that is\n     provably shorter than the buffer is listed anyway.\n", qQ67},
	{"struct-padding-leak", "Structs with alignment holes that are copied or written whole", "ANSWERS DCL39-C: where padding bytes can be stored or transmitted.\nACT if the struct crosses a trust boundary -- to disk, to the wire, to another\n     process -- serialise it field by field, or pack and re-order it so there\n     are no holes.\nMISLEADS `copied_whole` counts memcpy-family sites in the same FILE as the\n     struct, not copies OF that struct: it is a proxy, not a data-flow fact.\n     Padding is computed only where every field's type could be sized, so a\n     struct containing an unknown typedef is absent rather than wrong. There\n     is no fan_in column: nothing calls a struct, so it would read 0 on\n     every row of every corpus -- the ranking is by pad bytes and copy\n     sites instead.\n", qQ68},
	{"dead-static", "static functions nothing calls and whose address is never taken", "ANSWERS unreachable code, with the stronger claim `static` allows.\nACT `static` means no other translation unit can reach it, so unlike dead-code\n     this is a candidate for deletion rather than for investigation.\nMISLEADS a static function reached through a function pointer assigned in a\n     macro or a generated table escapes the addr_taken test and appears here\n     while alive. Grep the name as a string before deleting anything.\n", qQ69},
	{"missing-prototype", "External functions defined in a .c with no prototype anywhere", "ANSWERS MISRA-C 8.2 / CERT DCL40-C: where callers get no signature check.\nACT add the prototype to the header that owns this module. Without one, every\n     caller in another translation unit is calling an implicitly-declared\n     function and an argument mismatch is silent.\nMISLEADS a prototype in a header this run did not parse -- vendored, generated,\n     or excluded -- is invisible, so those rows are wrong. It also does not\n     check that a prototype which DOES exist agrees with the definition.\n", qQ70},
	{"header-hygiene", "Headers with no inclusion guard", "ANSWERS headers that cannot safely be included twice.\nACT one line: `#ifndef FOO_H` / `#define FOO_H` ... `#endif`, or `#pragma once`.\nMISLEADS a guard is detected as an `#ifndef` in the first 12 lines, so a header\n     that uses ONLY `#pragma once` is reported as unguarded, which is wrong --\n     the preprocessor table does not record pragmas. Ranked by how many files\n     include it, since an unguarded header nobody includes twice harms nobody.\n", qQ71},
	{"module-cycles", "Module pairs that can each reach the other through calls", "ANSWERS the dependency cycles: seams that cannot be cut.\nACT a cycle means neither side can be built, tested, or reasoned about alone.\n     Break it by inverting one edge -- a callback, an interface header, an event.\nMISLEADS depth-bounded at 4 hops in each direction, so a longer return path\n     reads as no cycle. Modules are two path components, so a cycle WITHIN one\n     module is invisible here by construction.\n", qQ72},
	{"naming-coherence", "Functions that break their own file's dominant name prefix", "ANSWERS C's missing namespace, made visible.\nACT either the function is misplaced and belongs in the file that owns its\n     prefix, or the file is doing two jobs and should be split.\nMISLEADS the dominant prefix is simply the most common one in the file, so a\n     file with no dominant convention is skipped entirely (fewer than three\n     users) and a file with two legitimate conventions reports half of itself.\n     The prefix is the text before the first underscore.\n", qQ73},
	{"untested-surface", "Widely-called functions with no caller in any test file", "ANSWERS where a regression would ship.\nACT these are the highest-value test targets: high fan_in means a bug here\n     reaches far, and no test currently reaches it at all.\nMISLEADS \"reached by a test\" means a resolved call edge from a file this run\n     classified as a test. A test that drives the code through a socket, a\n     subprocess, or a function pointer produces no edge and reads as untested.\n", qQ74},
	{"io-in-loop", "A syscall inside a loop body: one per iteration", "ANSWERS where the syscall count scales with the data.\nACT batch it: readv/writev, a larger buffer, or hoist the call out of the loop.\nMISLEADS a loop over a handful of descriptors is correct and is listed. The\n     count is of call SITES in loop bodies, so one site in a hot loop beats ten\n     in a cold one -- which the ranking cannot see. `io_in_loop` has been\n     captured and indexed since the base schema and no query read it until now.\n", qQ75},
	{"lock-convoy", "A lock acquired inside a loop body", "ANSWERS where a lock is taken once per iteration instead of once per pass.\nACT hoist it, or take it around the batch. The cost is not the lock, it is the\n     queue behind it.\nMISLEADS a lock released at the end of each iteration may be REQUIRED -- a\n     per-item invariant, or a condvar wait. Loop depth is the triage hint:\n     depth 1 over a short loop is rarely the problem.\n", qQ76},
	{"branch-per-iteration", "Branches inside loop bodies, ranked by how many", "ANSWERS where the predictor re-decides on every iteration.\nACT only worth acting on where the branch is data-dependent. The switch and\n     call columns are the ones that usually are.\nMISLEADS this is the single most common shape in real code -- every loop has at\n     least one branch, including its own condition. It is a ranking of VOLUME,\n     not a finding, and a perfectly predicted branch costs almost nothing.\n", qQ77},
	{"et-without-drain", "Edge-triggered registration with no EAGAIN drain anywhere in the function", "ANSWERS the stall. epoll(7): with EPOLLET the caller \"must consider it ready\n     until the next (nonblocking) read/write yields EAGAIN\". Reading once and\n     moving on leaves the rest of the buffer in the kernel, and the next\n     epoll_wait() blocks forever -- the peer is waiting on a reply to bytes\n     this process has already been told about. EV_CLEAR is kqueue's spelling\n     of the same contract.\nACT loop until EAGAIN, or drop EPOLLET/EV_CLEAR and take level-triggered.\nMISLEADS the drain usually lives in a DIFFERENT function from the\n     registration -- a helper reads until EAGAIN and this ranks the registrar,\n     because that is the only place the flag is visible. Both counts are\n     per function and a project that centralises the drain will list every\n     registration site. It also cannot see that the descriptor is a datagram,\n     where one read really can consume everything.\n", qQ78},
	{"event-wait-eintr-blind", "A blocking wait whose return value is used without any EINTR handling", "ANSWERS where a delivered signal becomes a spin or a silent stall.\nACT epoll_wait(2), kevent(2) and io_uring_wait_cqe(3) all return -1 with\n     errno EINTR on any signal. Test for it and retry; do not fall through\n     into the loop with a negative count.\nMISLEADS the test is the presence of the token EINTR in the function -- a\n     retry in a shared wrapper does not make the caller clean, and a\n     `continue` on EINTR in a loop this function does not contain is\n     invisible. Conversely a function that names EINTR for an unrelated\n     syscall reads clean.\n", qQ79},
	{"write-ready-never-cleared", "Write-readiness registered and never withdrawn: a level-triggered busy loop", "ANSWERS the 100%-CPU-forever shape.\nACT EPOLLOUT and EVFILT_WRITE are level-triggered, so they are ready whenever\n     the socket can take a single byte -- which is nearly always. Register\n     them only when there is something queued, and remove them with\n     EPOLL_CTL_DEL / EV_DELETE the moment the queue drains.\nMISLEADS the deregistration may be in another function, and a project that\n     manages its write interest centrally will show every ADD site here.\n     EV_DELETE is also the normal teardown path, so a function that registers\n     and then tears down the whole connection counts as clean only if the\n     two are in the same body.\n", qQ80},
	{"event-error-flag-unhandled", "A poller that never looks at the error or hangup flags", "ANSWERS where disconnects and registration failures are silently dropped.\nACT epoll(7) delivers EPOLLERR and EPOLLHUP whether or not they were\n     requested, and kqueue(2) sets EV_EOF and EV_ERROR the same way. Test\n     them before the read/write flags, or a closed peer is reported as a\n     readable descriptor forever.\nMISLEADS the flags may be handled by a shared dispatcher rather than here,\n     which is the common and correct design; this ranks the functions that\n     own the mask, not the ones that get it right. A loop that only ever\n     watches timers or signals has no error flag to handle and still appears.\n", qQ81},
	{"oneshot-never-rearmed", "Delivered-once registration with no re-arm: the descriptor goes silent", "ANSWERS where a file descriptor stops reporting events permanently.\nACT EPOLLONESHOT disables the descriptor after one delivery and it stays\n     disabled until epoll_ctl(2) with EPOLL_CTL_MOD re-arms it -- ADD does\n     not re-arm, it only registers. EV_DISPATCH on kqueue needs EV_ENABLE.\n     Either re-arm or drop the flag.\nMISLEADS EPOLL_CTL_ADD is deliberately NOT counted as a re-arm, so a\n     register/delete/re-add cycle reads as unre-armed even though it works.\n     The re-arm is also usually in the I/O handler, not the registering\n     function.\n", qQ82},
	{"uring-res-unchecked", "CQEs consumed without ever testing res: io_uring errors are invisible", "ANSWERS where every I/O error becomes a successful zero-length operation.\nACT io_uring(7) is explicit: \"errno is never used for passing back error\n     information. Instead, res will contain ... -errno.\" Test `cqe->res < 0`\n     on every completion, including the ones from a batched submit.\nMISLEADS the test is a textual match for `res` in the function, so a helper\n     that checks it centrally leaves every caller listed. Multi-shot and\n     IORING_CQE_F_MORE completions need the check on each one, which this\n     cannot distinguish from a single check.\n", qQ83},
	{"uring-errno-confusion", "io_uring used together with errno: the wrong error channel", "ANSWERS a porting bug, and the most common one when synchronous I/O is\n     converted to io_uring.\nACT res carries the error. Reading errno after an io_uring operation reports\n     whatever the last unrelated call left behind -- and under SQPOLL there\n     may have been no syscall at all to set it.\nMISLEADS errno may be read here for a genuinely synchronous call in the same\n     function -- an open(), an mmap(), a malloc() failure. The columns show\n     both counts side by side precisely so that judgement is possible;\n     nothing here proves the errno belongs to the io_uring call.\n", qQ84},
	{"uring-sqpoll-free-race", "SQPOLL ring with a free in the same function: freed before completion", "ANSWERS a use-after-free that the kernel dereferences, not this process.\nACT io_uring(7): without SQPOLL a submitted pointer only has to stay valid\n     until io_uring_submit() returns; WITH IORING_SETUP_SQPOLL it \"must\n     remain valid until completion\". Hold the buffer until its CQE arrives,\n     or drop SQPOLL.\nMISLEADS the free may be of something entirely unrelated to the submission,\n     and a function that both submits and frees a scratch buffer is listed\n     regardless of whether the two are connected. The flag is captured from\n     the body, so a ring configured in another function and passed in is\n     invisible here. There is no fan_in column: SQPOLL setup with a free\n     in the same body is nearly always a test's main(), which has no\n     callers, so the number measured 0 on every row of every corpus.\n", qQ85},
	{"uring-ring-without-barrier", "Shared ring head or tail touched with no acquire/release barrier", "ANSWERS a data race on memory the kernel is writing at the same time.\nACT the head and tail are shared with the kernel and both sides write them,\n     so io_uring(7) requires an acquire on the way in and a release on the\n     way out. Use the io_uring_smp_load_acquire / io_uring_smp_store_release\n     helpers or their C11 equivalents; a plain read is not sufficient.\nMISLEADS the ring reference is matched by NAME SHAPE -- an identifier\n     containing `ring` followed within a short distance by `head` or `tail`\n     -- so a project's own ring that does not use the word, or a raw\n     integer index into the ring, is missed. liburing wraps all of this and\n     a ring accessed only through it is correctly absent.\n", qQ86},
	{"event-loop-alloc-per-event", "Allocation on the event path: one malloc per event", "ANSWERS where the allocator is on the hot path of the whole process.\nACT per-event allocations dominate a saturated loop. Use a pool, a slab, or\n     an object cache keyed by the descriptor; the allocation should not scale\n     with the event rate.\nMISLEADS the allocation may be a one-time setup that merely shares a body\n     with the wait, and the count is of SITES, not of events. A loop that\n     allocates only on connection establishment -- not per event -- looks\n     identical here.\n", qQ87},
	{"event-wait-no-timeout", "A wait primitive called with an indefinite or zero timeout", "ANSWERS which loops can never do periodic work, and which never sleep.\nACT two opposite bugs, both from the same argument. NULL or -1 blocks until\n     an event arrives, so the loop can never run a timer, check a shutdown\n     flag, or re-arm -- the usual fix is a bounded timeout plus a periodic\n     tick. 0 turns the wait into a poll, and a loop polling at 0 burns a\n     core to save microseconds of latency it usually does not need.\nMISLEADS an indefinite wait is CORRECT wherever the loop has nothing to do\n     between events -- postgres's WaitEventSetWaitBlock blocks forever\n     precisely because no timeout was requested. This ranks the property,\n     not the defect; read the fan_in column before acting. Only epoll_wait\n     and kevent are analysed: io_uring's wait calls end in an out-parameter\n     or a count, so \"the last argument is the timeout\" is not true there.\n     A kevent with nevents of 0 is a registration, not a wait, and is\n     skipped -- counting it was 2 of redis's first 3 rows. There is no\n     fan_in column: an event-loop poll function is almost always reached\n     through a dispatch-table pointer, so it has no callers and the number\n     measured 0 on every row of every corpus.\n", qQ88},
	{"et-without-nonblocking", "Edge-triggered registration on a descriptor never made non-blocking", "ANSWERS the other half of the edge-triggered contract.\nACT epoll(7): an EPOLLET application \"should use nonblocking file\n     descriptors to avoid having a blocking read or write starve a task that\n     is handling multiple file descriptors\". Set O_NONBLOCK (or accept with\n     SOCK_NONBLOCK) before registering.\nMISLEADS the flag is usually set somewhere ELSE -- at accept time, in the\n     listen socket, or by a shared helper -- so a correct loop is listed\n     whenever the descriptor was made non-blocking in a different function.\n     EAGAIN handling and a non-blocking descriptor are two separate halves:\n     et-without-drain ranks the first, this ranks the second, and a loop can\n     fail either one.\n", qQ89},
	{"event-fd-leak", "Creates a poller instance and never releases anything in the function", "ANSWERS where an epoll descriptor, a kqueue, or a ring is dropped.\nACT these are descriptors (and for io_uring, two shared mappings). close()\n     the epoll fd and the kqueue, and call io_uring_queue_exit() with any\n     registered buffers or files unregistered first -- on every error path,\n     not only the happy one.\nMISLEADS the release test is any close()/queue_exit()/unregister() call in\n     the same function, so a function that closes an unrelated descriptor\n     reads clean, and a constructor that hands the instance to its caller\n     -- which is the correct design -- is listed as a leak. Ownership\n     transfer is invisible here.\n", qQ90},
	{"uring-sqe-null", "io_uring_get_sqe() whose result is never checked for NULL", "ANSWERS the most common io_uring bug there is.\nACT io_uring_get_sqe() returns NULL when the submission queue is full. Keep\n     the queue drained, size it for the intended depth, and test the pointer\n     before filling it in -- otherwise a busy ring is a NULL dereference.\nMISLEADS the test is the function-wide count of `== NULL` and `if (!x)`, so\n     an unrelated NULL check anywhere in the function makes it read clean,\n     and a check inside a shared helper does not. Ranked by how many SQEs\n     the function takes, because that is how often it can be NULL.\n", qQ91},
	{"uring-cqe-never-seen", "Completions waited for but never returned to the kernel", "ANSWERS where the completion ring can fill and stall the program silently.\nACT every CQE has to be marked seen -- io_uring_cqe_seen(), or\n     io_uring_cq_advance() for a batch. Until it is, the slot stays occupied;\n     when the ring is full the kernel cannot post another completion and the\n     ring stops making progress with no error anywhere.\nMISLEADS a function that peeks rather than waits, or one that hands the CQE\n     to a helper that advances it, is listed. liburing's *_nr and\n     for_each_cqe helpers all advance in the caller, so this is usually a\n     true positive; the gap is a project's own wrapper.\n", qQ92},
	{"uring-user-data-unset", "More SQEs taken than user_data values set: completions cannot be correlated", "ANSWERS where a completion cannot be matched to the request it belongs to.\nACT io_uring(7) is explicit that completions arrive in ANY order and that\n     \"the most common method\" of matching them is the user_data field. Set\n     it on every SQE that shares a ring with another in-flight request, or\n     use liburing's io_uring_sqe_set_data().\nMISLEADS this only matters when more than one request is in flight at a\n     time, so the query requires at least 2 SQEs; a submit-one-wait-one loop\n     legitimately needs none. The comparison is of COUNTS, not of identity:\n     a function that sets user_data on one SQE and not on the other reads as\n     half-clean. liburing tests that reuse a single request are listed too.\n", qQ93},
	{"uring-link-ordering", "Stream sends or receives with no IOSQE_IO_LINK anywhere", "ANSWERS where two stream operations on one socket can be reordered.\nACT io_uring(7): \"it is generally unsafe to have more than one outstanding\n     send, or more than one outstanding receive ... on a given socket at a\n     time, as the kernel may reorder their execution.\" Link them with\n     IOSQE_IO_LINK, submit them in one batch, or wait between them.\nMISLEADS two sends of INDEPENDENT data -- a header and a separate response,\n     on different sockets -- are fine unlinked, and this cannot tell them\n     apart: it sees prep_send twice and no link flag. Datagram sockets are\n     unaffected by the ordering rule and are still listed.\n", qQ94},
	{"uring-teardown-incomplete", "A ring initialised in this function with no io_uring_queue_exit", "ANSWERS where a ring's descriptor and its two shared mappings are dropped.\nACT io_uring_queue_exit() releases the ring, the mappings and the\n     descriptor. Registered buffers and files must be unregistered first.\n     Put it on every exit path.\nMISLEADS a function that builds a ring and hands it to its caller is\n     correct and is listed -- ownership transfer is invisible to a\n     per-function count. Short-lived test and example code frequently lets\n     process exit do the cleanup, which is why this ranks high on trees\n     that are mostly tests.\n", qQ95},
	{"kevent-timer-zero", "EVFILT_TIMER registered with a data value of zero", "ANSWERS a timer that does not mean what it says.\nACT kqueue(2): \"Periodic timers with a specified timeout of 0 will be\n     silently adjusted to timeout after 1 of the time units specified by\n     the requested precision in fflags.\" At NOTE_NSECONDS that is a\n     one-nanosecond periodic timer -- the loop never sleeps and the process\n     pins a core. Pass the interval you meant, or use EV_ONESHOT.\nMISLEADS only EV_SET's data argument is inspected, so a timer whose value\n     is assigned afterwards (`kev.data = 0`) is missed, and a data of 0 that\n     is genuinely intended as \"one unit\" reads as a bug. NOTE_ABSTIME\n     timers are exempt in spirit but not in this test.\n", qQ96},
	{"kevent-batch-errors-ignored", "EV_RECEIPT bulk registration whose EV_ERROR events are never read", "ANSWERS where a failed registration is silent.\nACT kqueue(2): with EV_RECEIPT, \"EV_ERROR [is] always returned. When a\n     filter is successfully added the data field will be zero.\" The failures\n     arrive as EVENTS, not as a return value -- so iterate the eventlist and\n     test EV_ERROR on each, or drop EV_RECEIPT and check kevent()'s return.\nMISLEADS the EV_ERROR test may live in a shared dispatcher. This is the\n     rarest of the kqueue shapes and neither test corpus uses EV_RECEIPT at\n     all, so its only evidence is the fixture.\n", qQ97},
	{"blocking-call-in-event-loop", "A loop that waits, and also blocks on something else inside the loop", "ANSWERS where one slow descriptor stalls all the others.\nACT an event loop must block on exactly one thing: the wait primitive. A\n     synchronous read inside the body stalls every other descriptor for its\n     duration, and a lock taken in the body serialises every thread that\n     wants the same lock. Move the work off the loop, or make it\n     non-blocking and continue on the next event.\nMISLEADS the per-loop counters cover EVERY loop in the function, not only\n     the event loop, so a helper called from the loop that happens to lock\n     makes the whole function look blocking. Locking to update a shared\n     statistic is usually correct and cheap; the ranking cannot tell a\n     contended lock from an uncontended one.\n", qQ98},
	{"snprintf-truncation-ignored", "snprintf's return is never compared to anything", "ANSWERS where truncated output is silently accepted.\nACT snprintf returns the length it WOULD have written. Compare it against\n     the buffer size and treat `>= sizeof buf` as truncation. Otherwise\n     \"fit exactly\" and \"lost 400 bytes\" are the same result.\nMISLEADS the guard test is function-wide (`< 0`, `== -1`, `>= size`), so a\n     check for an unrelated call makes a row read clean. This is the single\n     largest rule in the pack by measured volume: 296 rows across the four\n     corpora, so triage by fan_in rather than reading top to bottom. GCC's\n     `-Wformat-truncation` catches some of these at compile time, but only\n     when the buffer size is known there.\n", qQ99},
	{"stdio-result-unchecked", "fread/fwrite/fscanf return values discarded", "ANSWERS where a short read, a failed write, or an unconverted field passes.\nACT fread returns a COUNT, not a success flag -- compare it to the count you\n     asked for. fscanf returns the number of conversions; check it equals the\n     number of specifiers, or the untouched variables hold garbage.\nMISLEADS function-wide guard test. A loop that checks nothing but writes\n     into a buffer it then validates another way is a false positive; there\n     is no way to see that from here.\n", qQ100},
	{"string-conversion-unchecked", "strtol-family result used without errno and end pointer", "ANSWERS where \"0\", \"not a number\" and \"overflow\" are indistinguishable.\nACT strtol fails three ways. Set `errno = 0` first, pass a real end pointer,\n     then check endptr != input AND errno != ERANGE. One without the other\n     is not a check.\nMISLEADS requires BOTH guards, so a function that clears errno but ignores\n     the end pointer is listed. `atoi` is worse still and is a separate\n     smell this query does not cover.\n", qQ101},
	{"ctype-signed-char-ub", "isalpha/toupper called on a plain char", "ANSWERS a latent undefined behaviour that is invisible until a byte >= 0x80.\nACT ctype functions are defined only for values representable as an unsigned\n     char, or EOF. Pass `(unsigned char)c`, or hold the byte in an `int`.\n     With a negative `char` the result is undefined -- typically a read\n     outside the table.\nMISLEADS the guard is `(unsigned char)` anywhere in the function, so a cast\n     used for an unrelated conversion makes a row read clean; and a char\n     that provably never goes negative (ASCII literals) is still listed.\n     ctype had ZERO coverage before this rule.\n", qQ102},
	{"sleep-eintr-unhandled", "nanosleep/usleep/sleep with no EINTR handling", "ANSWERS where a signal shortens a sleep and nobody notices.\nACT on -1/EINTR the remainder is undone. Retry with the remainder\n     (nanosleep writes it into the second argument) or the sleep is short.\nMISLEADS the test is the token EINTR anywhere in the function. Some sleeps\n     genuinely should be interruptible -- an alarm-driven timeout loop is\n     correct and is listed.\n", qQ103},
	{"socket-partial-write", "send/write return never compared: a short write truncates", "ANSWERS where a message can be silently truncated at the receiver.\nACT send/write return the number of bytes accepted, which is often less than\n     the length. Loop until everything is sent, or treat a short count as an\n     error, depending on the protocol.\nMISLEADS fires on any send/write in an unguarded function, including writes\n     to a blocking file where a short write genuinely cannot happen. It\n     cannot tell a socket from a file descriptor -- the two share write().\n", qQ104},
	{"mman-never-unmapped", "mmap with no munmap anywhere in the function", "ANSWERS where address space is acquired and never released.\nACT pair every mmap with munmap on every path. On a long-running daemon this\n     is a slow exhaustion rather than a crash.\nMISLEADS ownership transfer is invisible: a helper that returns the mapping\n     to its caller is correct and is listed. Short-lived processes that let\n     exit() clean up are listed too -- which is why liburing's tests rank\n     high here.\n", qQ105},
	{"wait-status-unchecked", "waitpid's status used without WIFEXITED/WIFSIGNALED", "ANSWERS where a signal death is reported as an exit code.\nACT the status word must be decoded first. WIFEXITED gates WEXITSTATUS;\n     WIFSIGNALED gates WTERMSIG. Reading it raw conflates the two.\nMISLEADS function-wide guard test; the macros may appear in a helper.\n", qQ106},
	{"scanf-unchecked", "scanf-family conversions never counted", "ANSWERS where malformed input silently yields uninitialised variables.\nACT scanf returns the number of successful conversions. Check it equals the\n     number of specifiers. Prefer fgets + strtol, which is checkable.\nMISLEADS function-wide guard test.\n", qQ107},
	{"math-domain-error", "sqrt/log/asin with no domain guard", "ANSWERS where a NaN is born and then propagates silently.\nACT sqrt of a negative, log of zero, asin outside [-1,1] are domain errors:\n     they return NaN and set errno. Clamp the argument or check the result\n     with isnan().\nMISLEADS the guard is any comparison or `if` in the function, which is a weak\n     proxy -- it cannot tell a clamp on THIS argument from an unrelated\n     branch. Only 7 rows across the corpora; gcc's -Wfloat-equal and clang's\n     -Wtautological-compare-ish checks do not cover this.\n", qQ108},
	{"time-not-threadsafe", "localtime/gmtime/ctime/asctime -- one static buffer", "ANSWERS where two threads can read each other's formatted time.\nACT these return a pointer to a single static object. Use the _r variants\n     (localtime_r, gmtime_r) or ctime_r, which fill a caller buffer.\nMISLEADS single-threaded programs are entirely unaffected and are listed.\n     The `conc_in_fn` column is the only evidence offered: whether the same\n     function touches a concurrency primitive at all.\n", qQ109},
	{"signal-deprecated-api", "signal() where sigaction() is available", "ANSWERS where handler semantics depend on the platform.\nACT signal() has implementation-defined behaviour on delivery -- SysV resets\n     the handler, BSD does not. sigaction() makes it explicit and is\n     portable.\nMISLEADS signal() is not wrong everywhere, only where the reset semantics\n     matter. A program that reinstalls its own handler is fine and listed.\n", qQ110},
	{"mman-result-unchecked", "mmap compared to NULL instead of MAP_FAILED", "ANSWERS a check that passes on failure.\nACT mmap fails with MAP_FAILED, which is (void *)-1 on most systems and NOT\n     NULL. A NULL check succeeds, and the caller then dereferences -1.\nMISLEADS the guard test looks for MAP_FAILED or a NULL check; a codebase\n     that correctly checks MAP_FAILED only via a macro is missed. Only 2\n     rows across the corpora -- rare, and worth finding precisely because\n     it is rare.\n", qQ111},
	{"socket-not-nonblocking", "accept() with no O_NONBLOCK anywhere", "ANSWERS where one slow peer can stall the loop that accepted it.\nACT an accepted socket starts blocking. Set O_NONBLOCK (or accept with\n     SOCK_NONBLOCK) before handing it to an event loop, or a read can block\n     every other descriptor.\nMISLEADS the guard is O_NONBLOCK/SOCK_NONBLOCK/F_SETFL anywhere in the\n     function, so a non-blocking set performed in a helper is missed and the\n     accepting function is listed.\n", qQ112},
	{"varargs-lifetime", "va_start with no va_end in the same function", "ANSWERS where a va_list is left in an undefined state.\nACT every va_start needs a matching va_end on every path -- including the\n     early returns. On some ABIs the frame is not cleaned up without it.\nMISLEADS only 2 rows across the corpora; this is a rare bug, kept because it\n     is cheap and unambiguous. A va_end reached through a macro is missed.\n", qQ113},
	{"signal-stack-size-constant", "Array sized with SIGSTKSZ / MINSIGSTKSZ / PTHREAD_STACK_MIN", "ANSWERS a mis-sized buffer that appeared when glibc changed underneath it.\nACT glibc 2.34 made these non-constant -- they are sysconf() calls now.\n     Query them at runtime (sysconf(_SC_SIGSTKSZ)) and allocate, or use a\n     constant of your own. A compile-time array gets a size that is no\n     longer tied to what the kernel wants.\nMISLEADS fires on NO corpus here. Only a problem on glibc >= 2.34; on musl\n     and older glibc these are still constants and the code is fine.\n", qQ114},
	{"pointer-overflow-check-broken", "`p + n < p` -- an overflow check the compiler deletes", "ANSWERS a check that looks defensive and is not one.\nACT pointer addition that overflows is undefined behaviour, so the compiler\n     folds `p + n < p` to false. Compare on integers:\n     `(uintptr_t)p + n < (uintptr_t)p`. Detect with\n     -fsanitize=pointer-overflow, which is opt-in -- hence this rule.\nMISLEADS the pattern is matched textually, so a genuine comparison of two\n     unrelated pointers that happen to share a name is listed. Fires on no\n     corpus here, and is kept precisely because the compiler silently\n     removes the check rather than warning about it.\n", qQ115},
	{"calloc-transposed-args", "calloc's arguments are the wrong way round", "ANSWERS an allocation that is the wrong size and looks deliberate.\nACT calloc(count, size). A sizeof in the FIRST argument means the two are\n     transposed: you asked for size*count elements of size bytes. GCC 14\n     catches this with -Wcalloc-transposed-args, which is opt-in.\nMISLEADS only the `calloc(sizeof(...)` spelling is detected; a named\n     constant first argument that is really a size is invisible. Harmless\n     when size == 1, which is common.\n", qQ116},
	{"varargs-array-type", "va_arg with an array type: undefined behaviour", "ANSWERS a construct that cannot work at all.\nACT va_arg's type must be a promoted type the ABI can pass. An array type\n     undergoes no promotion, so it never matches. Pass a pointer instead.\n     Clang 20 diagnoses this as -Wvarargs; GCC does not by default.\nMISLEADS fires on NO corpus in this tree -- it exists because the construct\n     is unambiguous UB and the compiler only catches it with an opt-in flag.\n", qQ117},
	{"time-elapsed-not-monotonic", "A wall clock read where an elapsed time may be measured", "ANSWERS where a clock adjustment, an NTP step or a DST change moves a timing.\nACT gettimeofday() and time() read the WALL clock, which steps backwards and\n     forwards. For elapsed time use clock_gettime(CLOCK_MONOTONIC), which\n     cannot go backwards. Keep the wall clock only for timestamps.\nMISLEADS this cannot tell measuring from timestamping -- and most wall-clock\n     reads are legitimate timestamps that are correctly excluded by the\n     `clock_gettime` test. A function that reads the clock to print a log\n     line is listed. The filter is any gettimeofday/time/ftime/clock call\n     with no CLOCK_MONOTONIC anywhere in the function, so the volume is high\n     (143 rows across the corpora) by design: triage by fan_in.\n", qQ118},
	{"event-wait-batch-one", "An event wait that can return exactly one event per syscall", "ANSWERS where the loop is syscall-bound instead of event-bound.\nACT pass a real array size. epoll_wait's maxevents of 1 -- or kevent's nevents\n     of 1 -- means one syscall per event, which throws away the entire reason\n     for using a poller instead of poll().\nMISLEADS a maxevents of 1 is sometimes deliberate: nginx uses it in a probe\n     that exists precisely to test one descriptor. Detected from the argument\n     list only, so a variable that happens to hold 1 is invisible.\n", qQ119},
}

var metricsCat = []qentry{
	{"graph-blindspots", "Read this first: where the call graph cannot see", "ANSWERS how much of every other answer below is a lower bound.\nACT fnptr is the real blindness -- a callback table, a vtable-by-hand, a\n     dispatch array. Reachability results for a module high on this list\n     are floors, not facts. `via_macro` and `external` are NOT blindness:\n     one is the preprocessor, the other is libc, and both are known.\nMISLEADS this matches on NAME and body size only -- it never checks that\n     the definitions sit behind a preprocessor conditional. Two\n     same-named static functions in unrelated translation units, or one\n     entry point implemented once per example module, look identical to\n     a real backend pair. Confirm with grep -n '#if' on both files.\n     fnptr also counts ordinary struct-member calls, and `unresolved`\n     includes names from headers of libraries this run never walked into.", mM1},
	{"hot-multipliers", "Where one fix multiplies: highest fan-in, ranked with complexity", "ANSWERS which functions the rest of the tree leans on hardest.\nACT a win in a high-fan-in leaf pays back once per caller.\nMISLEADS fan_in counts STATIC call sites, not dynamic frequency, and it\n     cannot see a caller that reaches this through a function pointer.", mM2},
	{"risk-ranked", "Security review order: complexity x hazard x recursion", "ANSWERS if you can only review N functions this week, which N.\nACT risk = 2*cyclo + cognitive + 5*nest + 10*memory + 8*io + 15*exec\n     + integer + 2*alloc + 3*concurrency + 25 if recursive\n     + 10 if it allocates and never frees.\nMISLEADS it is a heuristic for ORDERING, not a list of findings.", mM3},
	{"alloc-cost", "Allocations per call, TRANSITIVELY", "ANSWERS what one call to this function really costs the allocator.\nACT `direct` counts allocation written in the body; `xalloc` walks the\n     call graph and multiplies by static call sites.\nMISLEADS the multiplier is STATIC call sites, not trip count, and the\n     walk stops at depth 3 -- deeper allocation is not counted at all.\n     Cycles are double-counted (a self-recursive wrapper's own mass is\n     pushed back into it), so treat xalloc as an upper bound.", mM4},
	{"module-coupling", "Cross-module call edges: where a seam would actually cut", "ANSWERS how entangled the subsystems are.\nACT a heavy one-way edge is a real seam; a heavy pair is a cycle and the\n     two modules are one module that has not admitted it.\nMISLEADS counts DISTINCT caller/callee pairs, not runtime frequency, and\n     misses every edge that goes through a callback.", mM5},
	{"header-fanout", "Headers whose change rebuilds the most of the tree", "ANSWERS which header is the build's bottleneck, transitively.\nACT split the widely-included header, or move the hot declarations into a\n     narrow one. This is the cheapest build-time win in a C repo.\nMISLEADS include depth is not compile cost, and a header included by\n     everything but changed once a year costs nothing at all.", mM6},
	{"nested-loops", "Loop depth >= 2: the O(n^k) candidates, with their per-iteration cost", "ANSWERS where cost grows super-linearly in the input.\nACT check what bounds the INNER trip count. `divs` and `calls` are the\n     two per-iteration costs people forget; a divide is ~20-40 cycles and\n     a loop-invariant one should be a reciprocal multiply.\nMISLEADS depth counts LEXICAL nesting, not asymptotics: an inner loop\n     bounded by a constant is O(1).", mM7},
	{"vectorisation-blocked", "Loops that CANNOT vectorise: a libm call in the body", "ANSWERS which loops are categorically unvectorizable as written.\nACT a libm call in a loop body is a hard stop for the auto-vectoriser --\n     it cannot prove the call is pure or replace it with a vector form.\n     Use a vectorised math library, or a polynomial approximation.\nMISLEADS it does not know the loop is hot, and -ffast-math plus a vector\n     libm changes the answer entirely.", mM8},
	{"explicit-simd", "Hand-written intrinsics and branch hints", "ANSWERS where the code already commits to a specific ISA.\nACT every intrinsic site needs a scalar fallback that is BUILT in CI, not\n     merely present -- an unbuilt fallback is an unrun fallback.\nMISLEADS a high intrinsic count is not a fast function, and `likely` hints\n     are frequently wrong and never re-measured.", mM9},
	{"struct-padding", "Byte-accurate layout: bytes lost to alignment holes", "ANSWERS which structs waste memory on padding, and exactly how much.\nACT reorder fields largest-alignment-first. This is free: no algorithm\n     changes, no API changes, and it compounds across every instance.\nMISLEADS LP64 model, and exact=1 rows only -- a struct containing another\n     struct cannot be sized here and is simply absent from this list.", mM10},
	{"cache-line-crossers", "Structs just over a 64-byte cache line", "ANSWERS which hot objects need two cache lines where one would do.\nACT 65-128 bytes is the painful band: shrink below 64 and every access\n     halves its memory traffic. Removing the padding is often enough.\nMISLEADS a struct that is never hot does not care, and an object always\n     touched in full needs both lines anyway.", mM11},
	{"cache-hostile-layout", "Pointer-dense structs: each pointer field defeats the prefetcher", "ANSWERS which structures drag a whole cache line to reach one field, and\n     then send you somewhere else in memory to read it.\nACT candidates for splitting the hot fields into a parallel array (SoA).\nMISLEADS TOP-LEVEL fields only -- union arms are alternatives, not extra\n     fields -- and a node in a linked structure is pointer-dense by nature.", mM12},
	{"stack-pressure", "Functions with the most locals, and the most pointer locals", "ANSWERS which frames are large enough to matter.\nACT a big frame in a RECURSIVE function multiplies by depth, and that\n     product is what actually overflows the stack.\nMISLEADS counts DECLARATIONS, not simultaneous liveness -- the compiler\n     reuses slots -- and it cannot see arrays sized at run time.", mM13},
	{"cast-density", "Pointer casts: where the type system was overruled", "ANSWERS the places a wrong assumption becomes a memory bug.\nACT each cast is a claim the compiler cannot check. A cast next to I/O\n     and shifting is where attacker-controlled bytes become a pointer.\nMISLEADS the pattern counts some compound literals and some macro\n     parameter lists as casts.", mM14},
	{"macro-machinery", "Function-like macros, by how much work they do", "ANSWERS the code the call graph cannot see into at all.\nACT a heavily-used multi-line macro is a function that skipped review: no\n     type checking, no breakpoint, no stack frame, and its cost is\n     multiplied by every use site rather than shared.\nMISLEADS `uses` counts sites where the name was called and no function of\n     that name exists in the tree, so a macro shadowed by a real function\n     somewhere reads as unused.", mM15},
	{"config-gated", "Code behind a CONFIG_/HAVE_/USE_ flag", "ANSWERS which regions a plain build silently omits.\nACT build each flag in CI, or the code inside it is unrun and unreviewed\n     and will not compile the day someone needs it.\nMISLEADS lists DIRECTIVES, not region sizes: one #ifdef can gate a\n     thousand lines or a single semicolon.", mM16},
	{"backend-parity", "One name, two definitions: which #if-selected backend is the STUB", "ANSWERS where a compile-time alternative silently drops a feature.\nACT a body a fraction of its sibling's size is usually the stub, and the\n     platform that selects it is the platform the feature does not work on.\nMISLEADS a small body can be complete -- a one-line platform wrapper is\n     the whole implementation on that platform.", mM17},
	{"profiler-invisible", "static inline with real fan-in: zero self-time is not zero cost", "ANSWERS which functions a sampling profiler CANNOT attribute cost to.\nACT never conclude one of these is cold from a flat profile -- its time\n     is charged to whoever inlined it. `hidden` is fan_in * sloc, a rough\n     measure of how much code the inliner is duplicating.\nMISLEADS `static inline` is a request, not a guarantee, and a big one is\n     often refused.", mM18},
	{"undocumented-complexity", "Complex functions with almost no comments", "ANSWERS where the next reader has to reconstruct intent from the code,\n     and where that reconstruction costs the most.\nACT a useful comment carries a CONSTRAINT or a non-obvious fact -- why\n     the bound is 4096, which caller guarantees the pointer is non-NULL.\nMISLEADS comment COUNT is not comment quality, and a genuinely obvious\n     500-line switch needs no prose at all.", mM19},
	{"hand-linked-objects", "Build rules and object lists that enumerate their inputs by hand", "ANSWERS which link targets name their objects individually -- both in a\n     rule's prerequisites and in the OBJ= variable that feeds it, which is\n     where a C project usually keeps the list.\nACT these are the lists a NEW CALL from a shared source silently breaks:\n     the compile succeeds and the link fails naming a symbol nobody edited.\nMISLEADS a hand-written list is perfectly correct until a dependency\n     changes, so this is a fragility ranking, not a defect list. A probe\n     snippet in a configure check looks the same and matters not at all.", mM20},
	{"parse-coverage", "How much of the tree this run actually read", "ANSWERS whether any answer above is missing a chunk of the codebase.\nACT `errors` means braces or parentheses did not balance, so functions in\n     that file may be merged, truncated or missed entirely. `unclosed` is\n     an #if without an #endif. Both are worth reading before trusting a\n     ranking that says a module is small.\nMISLEADS a file with zero errors can still be mis-read: a macro that\n     opens a brace and another that closes it balances perfectly and\n     produces nonsense spans.", mM21},
	{"goto-spaghetti", "Functions with excessive goto usage (MISRA-C 15.1)", "ANSWERS where a function has more than 3 goto statements, making control\n     flow hard to follow and verify.\nACT restructure with structured control flow (if/else, while, break).\nMISLEADS goto for cleanup-on-error (the only acceptable use in Linux kernel\n     style) is correct but should be the only pattern.", mM22},
	{"deep-nesting", "Functions with excessive nesting depth (MISRA-C)", "ANSWERS where a function has max_nesting > 4, making it hard to verify.\nACT extract nested blocks into helper functions; use early returns.\nMISLEADS C's max_nesting is +1 vs tree-sitter languages because it counts\n     the function's own brace. Adjust thresholds accordingly.", mM23},
	{"too-many-params", "Functions with too many parameters (MISRA-C)", "ANSWERS where a function has more than 6 parameters.\nACT use a struct parameter.\nMISLEADS a variadic function has n_params that does not count the ellipsis.", mM24},
	{"scattered-concerns", "A function called from many different modules (shotgun surgery)", "ANSWERS which functions are called from many distinct modules.\nACT consider splitting or stabilizing the contract.\nMISLEADS a utility like memcpy or printf is called from everywhere.", mM25},
	{"magic-number", "Functions with many bare numeric literals (MISRA-C 7.4)", "ANSWERS where a function has many magic numbers — bare numeric literals\n     that are not 0 or 1 and have no named constant. Each is a\n     maintenance burden.\nACT extract magic numbers into named constants or enums.\nMISLEADS 0 and 1 are excluded by convention. Array indices and bit flags\n     are sometimes clearer as literals.", mM26},
	{"call-chain-depth", "Deepest resolved call chains: how far a change propagates downward", "ANSWERS the functions with the widest downward exposure -- the count\n     of DISTINCT functions each one can reach through resolved edges\n     at any depth (precomputed in `reach.n_transitive_out`). Where\n     blast-radius counts who can reach YOU (upward risk), this counts\n     what you can REACH: the failure modes, allocation behaviour and\n     locking you inherit every time you call down the stack.\nACT a wide fan under a request handler is where latency and error\n     handling get lost; flatten, or make each level's contract\n     explicit.\nMISLEADS breadth, not depth: a function calling 30 helpers outranks a\n     strict 12-level chain of 1-callee hops; calls through function\n     pointers end the walk and undercount; a cycle member inherits its\n     component's full reach.", mM27},
	{"global-state-map", "Which modules own mutable file-scope state, and who writes it", "ANSWERS the mutation map `race-surface` cannot draw: per module, the\n    count of mutable file-scope objects against the number of\n    functions that WRITE one of them in place. A module high on both\n    columns is stateful by design and is where 'just add a feature'\n    turns into 'understand six globals first'.\nACT the fix is architectural: group the globals into one context\n    struct passed explicitly, so ownership shows up in signatures.\nMISLEADS same-file references only (extern-through-header use is\n    invisible), and a write counted here can be an initializer run\n    once at startup -- volume of writes is not volume of races.", mM28},
	{"error-handling-density", "Where failure handling dominates the code", "ANSWERS the functions whose shape IS error handling: return paths vs\n    distinct failure shapes (NULL / negative / zero), null checks, and\n    gotos-to-cleanup. C has no stack unwinding, so this work is real\n    code with real branch cost -- and its absence is a defect while\n    its excess is unreadability. This metric measures the balance.\nACT a high ratio with FEW null checks is the dangerous corner:\n    failure-shaped but not checking allocations. Start there.\nMISLEADS ret_* counts are textual (`return NULL;` exactly); a returned\n    error ENUM or errno expression counts as ret_val, so a\n    consistently-error-coded module looks value-returning; goto here\n    includes non-cleanup uses.", mM29},
	{"alloc-site-inventory", "Every allocation site, grouped by size-expression shape", "ANSWERS the tree's actual allocation habits: raw byte counts vs\n    sizeof-multiplied element counts vs bare constants, per allocator.\n    The sizeof share is the single best proxy for allocation-safety\n    discipline, and it is comparable across projects.\nACT read the shape mix before trusting any single leak query: a tree\n    that allocates mostly through wrappers needs wrapper-level review,\n    not site-level.\nMISLEADS project allocator wrappers are invisible unless they call\n    malloc/calloc/realloc directly IN THE BODY (they usually do, which\n    is why the fn column matters); alloca rows are stack allocations\n    and do not leak -- they exhaust the stack instead.", mM30},
	{"copy-hotspots", "The heaviest memcpy-family users, with their copy-site inventory", "ANSWERS which functions move the most bytes-by-call-count: the\n    memcpy/memmove/strcpy/strcat/sprintf load ranked per function.\n    Copy count is the cheapest available proxy for memory-bandwidth\n    pressure, and these functions are also where a wrong length\n    argument does the most damage.\nACT for the top rows ask the only two questions that matter: could\n    this copy be a pointer swap, and is the length derived from input?\nMISLEADS call COUNT, not bytes moved -- one memcpy of 4 KB outranks\n    nothing here if the rest are 8-byte struct copies; copies inside\n    loops multiply beyond what the count shows (join nested-loops for\n    that).", mM31},
	{"macro-reach", "Macro definitions ranked by transitive use weight", "ANSWERS the preprocessor's real API surface: function-like macros\n    weighted by use sites AND by body size -- n_uses * body_len is the\n    amount of source the reader must simulate to understand one macro\n    call. macro-machinery ranks by uses alone; this adds the cost side.\nACT the top rows are conversion candidates: a static inline function\n    gives type checking and debuggability at identical runtime cost.\nMISLEADS n_uses counts CALL-SHAPED uses only (name followed by '(');\n    object-like macros used as constants show zero uses here, and a\n    macro shadowed by a same-named function anywhere in the tree\n    loses all its uses to that function.", mM32},
	{"struct-abi-surface", "Structs most exposed to layout change, weighted by field volatility", "ANSWERS the structs whose byte layout carries the most cross-file\n    weight: exact-sized, pointer-bearing, and defined in headers other\n    files include. Reordering ONE field of these changes offsets in\n    every consumer -- the ABI-compat question struct-padding answers\n    for waste, answered here for RISK.\nACT pin the hot ones with _Static_assert(sizeof(struct x) == N) so a\n    layout change fails the build instead of the customer.\nMISLEADS header-defined structs only (a .c-local struct cannot leak\n    its layout); usage is inferred from include edges, so a widely\n    included header whose struct nobody instantiates still tops the\n    list; exact=1 rows only.", mM33},
	{"marker-debt", "TODO/FIXME/XXX/HACK/BUG/UNSAFE comments, by file", "ANSWERS where the code says out loud that it is not finished.\nACT read the SAFETY and UNSAFE markers first: those are usually a real\n     invariant stated in prose because C cannot state it in types.\nMISLEADS a marker is a comment, not a defect, and NOTE dominates every real\n     codebase. The `markers` table has been populated since the base schema and\n     nothing read it until now, so no convention about it has been established.\n", mM34},
	{"clone-candidates", "Functions with an identical size-and-shape fingerprint", "ANSWERS where the same shape of code appears more than once.\nACT a fingerprint match is a place to LOOK, not proof of a copy. Read two rows\n     before extracting anything.\nMISLEADS the fingerprint is (sloc, cyclomatic, n_params, n_calls). Two entirely\n     different functions can share it, and a genuine copy that gained one\n     statement will not. `duplicated_sloc` is an upper bound on what could be\n     removed and is usually far larger than what should be.\n", mM35},
	{"aliasing-blocked", "Same-typed pointer parameters with no restrict anywhere", "ANSWERS where the compiler must assume two parameters overlap.\nACT add `restrict` where they genuinely cannot overlap and the reloads go away.\n     Verify first: CERT EXP43-C -- an incorrect restrict is undefined behaviour.\nMISLEADS \"same type\" is textual on the parameter type string, so two pointers\n     to different structs that happen to share a spelling get paired, while a\n     `void *` next to anything does not. Loop depth is the proxy for whether it\n     matters: without a loop there is nothing to reload.\n", mM36},
	{"file-hotspots", "Files ranked by total risk", "ANSWERS where to start when the answer has to be a file, not a function.\nACT `risk_per_100_sloc` normalises for size: a big file is not automatically a\n     bad one, but a small file with a high density is.\nMISLEADS risk is the C-weighted formula (memory, I/O, exec, recursion), so a\n     file full of careful string handling ranks high without being unsafe.\n", mM37},
	{"api-surface", "The tree's real public interface, ranked by dependents", "ANSWERS which functions are actually an API: defined in a .c, prototyped in a .h.\nACT these are the ones a signature change breaks across translation units, and\n     the ones that need a written contract. `documented=0` on a high fan_in row\n     is the shortest path to a better codebase.\nMISLEADS `declared_in` counts prototype rows anywhere in the tree, so a name\n     declared in several headers counts all of them. Inline functions in headers\n     are excluded by construction, which is where much of a modern C API lives.\n", mM38},
	{"macro-hygiene", "Function-like macros ranked by how much work they do", "ANSWERS the macros whose expansion is doing real work in this tree.\nACT a macro used a thousand times is a function that cannot be stepped into,\n     type-checked, or profiled. `do_while=0` on a multi-statement macro is the\n     one to fix first.\nMISLEADS `n_uses` counts calls resolved to this macro by NAME, so a macro\n     invoked from inside another macro is attributed to the outer one. do_while\n     is a substring test on the body, not a parse.\n", mM39},
	{"init-discipline", "Locals declared without an initialiser, by function", "ANSWERS the surface for EXP33-C: an uninitialised read.\nACT a local declared without an init is only a bug if it is READ before it is\n     written, which this cannot prove. Ranked by count so the largest surfaces\n     come first.\nMISLEADS the dominant false positive is a variable assigned on all paths\n     immediately after its declaration -- extremely common and entirely correct.\n", mM40},
	{"lock-scope", "Each lock, by how much code runs while it is held", "ANSWERS which lock is the actual contention point.\nACT a lock's cost is not how often it is acquired, it is how much work sits\n     underneath: cyclo_under_lock and io_under_lock are the columns that predict\n     stalls. Splitting a hot lock beats optimising what is under it.\nMISLEADS attributed per FUNCTION that acquires the lock, not per critical\n     section -- so everything in that function counts as \"under the lock\",\n     including code that runs before the acquire. Only lock-shaped identifier\n     names are recorded, so a lock held in a variable is invisible.\n", mM41},
	{"typedef-pointer-opacity", "Typedefs whose underlying type is a pointer or an array", "ANSWERS where the `*` is invisible at every use site.\nACT the reader cannot tell whether `Foo x` is one word or a thousand, whether\n     `x = y` aliases or copies, or whether `sizeof x` is the pointer or the\n     buffer. Naming it `FooPtr` is the cheap fix.\nMISLEADS matched on the presence of `*` or `[` in the declared type text, so a\n     typedef of a function pointer and a typedef of a struct that CONTAINS a\n     pointer are both listed; only the first is the readability problem.\n", mM42},
	{"static-inline-in-header", "static inline bodies living in a header", "ANSWERS code that is compiled once per including translation unit.\nACT `times_included` is the multiplier. These functions never appear in a\n     profile under their own name and their cost is paid once per includer.\nMISLEADS a header with none is absent from this list, not clean -- this is a\n     presence ranking. `total_fan_in` sums the fan_in of the inlines, so a\n     header with one heavily-used inline outranks one with thirty unused ones,\n     which is the right order for build time and the wrong one for review.\n", mM43},
	{"error-code-convention", "Modules that cannot agree how to report failure", "ANSWERS where a caller has to know the callee before it can check the result.\nACT pick one convention per module and write it down. `pct_mixed` is the share\n     of that module's functions that use more than one shape.\nMISLEADS computed over functions with at least one return, and the three shapes\n     are NULL, a negative literal and a zero literal. Returning 0 for success AND\n     0 as a legitimate value is the worst case of all and is invisible. Modules\n     with fewer than 8 functions are excluded.\n", mM44},
	{"extern-in-source", "extern declarations sitting in a .c instead of a header", "ANSWERS where a symbol's declaration is repeated per translation unit.\nACT move it to the header that owns the module, so the compiler can check every\n     declaration against every other one.\nMISLEADS `also_in_a_header` counts how many of this file's extern names ALSO\n     appear in some header anywhere -- not necessarily one this file includes. A\n     high number usually means the declaration is simply duplicated, which is\n     still the problem.\n", mM45},
	{"event-api-inventory", "Every function that touches epoll, io_uring or kqueue, with its flag profile", "ANSWERS which functions own the event loop, and what contract each one has\n     taken on -- edge or level, oneshot or not, errors watched or not.\nACT read this before any of the event-loop queries: it is the same columns\n     unfiltered, so a row here that no query flags is a loop that is probably\n     correct, and a row that several queries flag is where to start.\nMISLEADS all counts are per FUNCTION. A project with one central dispatcher\n     shows one row and looks simple; a project that inlines its loop shows\n     dozens and does not necessarily have more problems.\n", mM46},
	{"event-loop-hotspots", "The blocking wait loops, ranked by complexity", "ANSWERS which event loop is the one worth understanding.\nACT a loop's cost is not the wait, it is everything under it. The per-loop\n     columns -- calls, I/O and branches inside the loop body -- say whether\n     the loop is a dispatcher or accidentally a worker.\nMISLEADS 'loop' here means the function that calls the wait primitive, and\n     the loop-body metrics cover every loop in that function, not only the\n     event loop. Cyclomatic complexity ranks big dispatch switches highly,\n     which is often the correct shape for one.\n", mM47},
	{"event-api-coverage", "Per module: which of the three APIs, and how much of each contract is met", "ANSWERS where the event-loop code lives and how disciplined it is.\nACT the six right-hand columns are the same predicates the event-loop\n     queries use, counted instead of listed: eintr_blind, et_unprepared and\n     leaks_instance are the rows those queries would return, so this is the\n     denominator they lack.\nMISLEADS every count is per FUNCTION, so a project with one central\n     dispatcher shows a single dense row while a project that inlines its\n     loop shows many sparse ones with the same total defects. Modules are\n     two path components, so cross-directory loops are split.\n", mM48},
	{"api-namespace-inventory", "Which toolchain namespaces each file uses, and how heavily", "ANSWERS where the API surface of this codebase actually is.\nACT read this before any other rule in the pack: it is the denominator the\n     per-rule queries lack. A file leaning hard on string.h deserves the\n     string rules first.\nMISLEADS grouped per FILE, so a project with one central wrapper file shows\n     a single dense row while a project that calls libc everywhere shows many\n     sparse ones with the same total. Namespaces are assigned by first match\n     in sorted order, so a function declared by two headers is counted once.\n", mM49},
	{"api-discipline-score", "Per file: how much of the API surface is used without its guard", "ANSWERS which files are careless, not which individual calls are wrong.\nACT the five right-hand columns are the same predicates the per-rule queries\n     use, counted instead of listed. Rank by the column that matters for the\n     file's namespace mix.\nMISLEADS every count is per FUNCTION and every guard test is function-wide,\n     so a file with one careful helper and twenty careless callers scores\n     badly for the right reason and a file with one careful helper and no\n     callers scores perfectly for the wrong one. This is a triage ranking,\n     not a defect count.\n", mM50},
}

func report(g *Graph) {
	w := bufio.NewWriter(os.Stdout)
	defer w.Flush()
	var bar strings.Builder
	for range 78 {
		bar.WriteString("=")
	}
	var dash strings.Builder
	for range 78 {
		dash.WriteString("-")
	}
	fmt.Fprintf(w, "\n%s\nOVERVIEW\n%s\n", bar.String(), dash.String())
	for _, k := range []string{"lang", "target", "parser", "root"} {
		if v, ok := g.Meta[k]; ok && v != "" {
			fmt.Fprintf(w, " %-14s %s\n", k, v)
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
	fmt.Fprintf(w, " %-14s %d catalogued, %d parsed, %d sloc\n", "files",
		files, parsed, sloc)
	kindN := map[string]int{}
	for i := range g.Symbols {
		kindN[g.Symbols[i].Kind()]++
	}
	type kv struct {
		k string
		v int
	}
	var ks []kv
	for k, v := range kindN {
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
	parts := make([]string, 0, len(ks))
	for _, x := range ks {
		parts = append(parts, x.k+"="+strconv.Itoa(x.v))
	}
	fmt.Fprintf(w, " %-14s %s\n", "symbols", joinComma(parts))
	var unres int32
	for _, u := range g.Unres {
		unres += u.N
	}
	fmt.Fprintf(w, " %-14s %d edges, %d call sites, %d unresolved\n",
		"call graph", len(g.Edges), len(g.Callsites), unres)

	fmt.Fprintf(w, "\n%s\nHOW MUCH OF THIS TO TRUST\n%s\n", bar.String(), dash.String())

	errFiles := int32(0)
	totCalls := int32(0)
	for i := range g.Files {
		if g.Files[i].NParseErrors > 0 {
			errFiles++
		}
	}
	for i := range g.Symbols {
		totCalls += g.Symbols[i].NCalls
	}
	if parsed == 0 {
		fmt.Fprintln(w, " NOTHING WAS PARSED. Every number below is zero because no file")
		fmt.Fprintln(w, " was read, not because this repository is empty or clean.")
	}
	fmt.Fprintf(w, " %-30s %d file(s)\n", "files with parse errors", errFiles)
	if totCalls != 0 {
		fmt.Fprintf(w, " %-30s %d of %d call sites (%d%%)\n",
			"calls we could NOT resolve", unres, totCalls, int(100*unres/totCalls))
	} else {
		fmt.Fprintf(w, " %-30s no calls were recorded at all -- this is the absence of\n", "")
		fmt.Fprintf(w, " %-30s data, not a clean result\n", "")
	}
	fmt.Fprintln(w, " A high unresolved share means the call-graph queries below see less")
	fmt.Fprintln(w, " than they imply. `v_blindspot` lists exactly where.")

	fmt.Fprintf(w, "\n%s\nBIGGEST MODULES\n%s\n", bar.String(), dash.String())
	mods := make([]Module, 0, len(g.Modules))
	for _, m := range g.Modules {
		if m.NFiles > 0 {
			mods = append(mods, m)
		}
	}
	sort.Slice(mods, func(i, j int) bool {
		if mods[i].Sloc != mods[j].Sloc {
			return mods[i].Sloc > mods[j].Sloc
		}
		return mods[i].Name() < mods[j].Name()
	})
	if len(mods) > 12 {
		mods = mods[:12]
	}
	var mr [][]fval
	for _, m := range mods {
		mr = append(mr, []fval{fStr(m.Name()), fI32(m.NFiles), fI32(m.Sloc),
			fI32(m.NSymbols), fF(round2(m.Instability))})
	}
	render(w, mr, []string{"name", "files", "sloc", "syms", "instab"})

	fmt.Fprintf(w, "\n%s\nHEAVIEST FUNCTIONS\n%s\n", bar.String(), dash.String())
	render(w, heaviest(g), []string{"name", "sloc", "cyclo", "cog", "nest",
		"fan_in", "at"})

	fmt.Fprintf(w, "\n%s\nMOST DEPENDED ON\n%s\n", bar.String(), dash.String())
	render(w, mostDepended(g), []string{"name", "fan_in", "fan_out", "cyclo",
		"sloc", "at"})

	fmt.Fprintf(w, "\n%s\nMARKERS LEFT IN THE CODE\n%s\n", bar.String(), dash.String())
	mk := map[string]int{}
	for _, m := range g.Markers {
		mk[m.Kind()]++
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
	var mkr [][]fval
	for _, x := range mks {
		mkr = append(mkr, []fval{fStr(x.k), fInt(x.v)})
	}
	render(w, mkr, []string{"kind", "n"})
}

func round2(f float64) float64 {
	return float64(int64(f*100+copysign(0.5, f))) / 100
}

func copysign(v, s float64) float64 {
	if s < 0 {
		return -v
	}
	return v
}

func joinComma(p []string) string {
	var out strings.Builder
	for i, s := range p {
		if i > 0 {
			out.WriteString(", ")
		}
		out.WriteString(s)
	}
	return out.String()
}

func fnAt(g *Graph, s *Symbol) string {
	return g.Files[s.FileID-1].Path() + ":" + strconv.Itoa(int(s.LineStart))
}

func heaviest(g *Graph) [][]fval {
	var xs []*Symbol
	for i := range g.Symbols {
		s := g.Symbols[i]
		if s.Kind() == "function" || s.Kind() == "method" ||
			s.Kind() == "constructor" || s.Kind() == "closure" {
			xs = append(xs, s)
		}
	}
	sort.SliceStable(xs, func(i, j int) bool {
		return xs[i].Cyclomatic > xs[j].Cyclomatic
	})
	if len(xs) > 12 {
		xs = xs[:12]
	}
	var out [][]fval
	for _, s := range xs {
		out = append(out, []fval{fStr(s.Name()), fI32(s.Sloc), fI32(s.Cyclomatic),
			fI32(s.Cognitive), fI32(s.MaxNesting), fI32(s.FanIn), fStr(fnAt(g, s))})
	}
	return out
}

func mostDepended(g *Graph) [][]fval {
	var xs []*Symbol
	for i := range g.Symbols {
		s := g.Symbols[i]
		if s.Kind() == "function" || s.Kind() == "method" ||
			s.Kind() == "constructor" || s.Kind() == "closure" {
			xs = append(xs, s)
		}
	}
	sort.SliceStable(xs, func(i, j int) bool { return xs[i].FanIn > xs[j].FanIn })
	if len(xs) > 12 {
		xs = xs[:12]
	}
	var out [][]fval
	for _, s := range xs {
		out = append(out, []fval{fStr(s.Name()), fI32(s.FanIn), fI32(s.FanOut),
			fI32(s.Cyclomatic), fI32(s.Sloc), fStr(fnAt(g, s))})
	}
	return out
}

type fkind int

const (
	fkNull fkind = iota
	fkInt
	fkFloat
	fkStr
	fkBlob
)

type fval struct {
	kind fkind
	i    int64
	f    float64
	s    string
}

func fNull() fval        { return fval{kind: fkNull} }
func fInt(v int) fval    { return fval{kind: fkInt, i: int64(v)} }
func fI32(v int32) fval  { return fval{kind: fkInt, i: int64(v)} }
func fF(v float64) fval  { return fval{kind: fkFloat, f: v} }
func fStr(s string) fval { return fval{kind: fkStr, s: s} }
func fBool(v int32) fval { return fval{kind: fkInt, i: int64(v)} }
func fOptInt(v int32, ok bool) fval {
	if !ok {
		return fNull()
	}
	return fI32(v)
}
func fOptStr(v string, ok bool) fval {
	if !ok {
		return fNull()
	}
	return fStr(v)
}

func encodeField(v fval) string {
	switch v.kind {
	case fkNull:
		return `\N`
	case fkInt:
		return "i:" + strconv.FormatInt(v.i, 10)
	case fkFloat:
		return "f:" + cgFloat(v.f)
	default:
		return "s:" + escapeText(v.s)
	}
}

func escapeText(s string) string {
	var sb strings.Builder
	sb.Grow(len(s) + 2)
	for i := 0; i < len(s); i++ {
		c := s[i]
		switch c {
		case '\\':
			sb.WriteString(`\\`)
		case '\n':
			sb.WriteString(`\n`)
		case '\t':
			sb.WriteString(`\t`)
		case '\r':
			sb.WriteString(`\r`)
		default:
			if c < 0x20 || c == 0x7F {
				fmt.Fprintf(&sb, `\x%02X`, c)
			} else {
				sb.WriteByte(c)
			}
		}
	}
	return sb.String()
}

func cgFloat(f float64) string {
	if math.IsInf(f, 1) {
		return "inf"
	}
	if math.IsInf(f, -1) {
		return "-inf"
	}
	if math.IsNaN(f) {
		return "nan"
	}
	return cgRepr(f)
}

type dumper struct {
	w *bufio.Writer
}

func (d *dumper) table(name string, ncols int, rows [][]fval) {
	lines := make([]string, 0, len(rows))
	for _, r := range rows {
		parts := make([]string, len(r))
		for i, v := range r {
			parts[i] = encodeField(v)
		}
		lines = append(lines, "R "+strings.Join(parts, " "))
	}
	sort.Strings(lines)
	fmt.Fprintf(d.w, "T %s %d %d\n", name, ncols, len(lines))
	for _, l := range lines {
		d.w.WriteString(l)
		d.w.WriteByte('\n')
	}
	fmt.Fprintf(d.w, "E %s\n", name)
}

func (g *Graph) dump(w io.Writer) {
	d := &dumper{w: bufio.NewWriterSize(w, 1<<20)}
	g.dumpW = d.w

	d.table("addr_taken", 6, g.tAddrTaken())
	d.table("allocsites", 6, g.tAllocSites())
	d.table("apiuse", 6, g.tAPIUse())
	d.table("attributes", 6, g.tAttributes())
	d.table("callsites", 3, g.tCallsites())
	d.table("config_blocks", 6, g.tConfigBlocks())
	d.table("declarations", 4, g.tDeclarations())
	d.table("edges", 6, g.tEdges())
	d.table("enum_members", 5, g.tEnumMembers())
	d.table("eventops", 7, g.tEventOps())
	d.table("fields", 14, g.tFields())
	d.table("files", 29, g.tFiles())
	d.table("globals", 13, g.tGlobals())
	d.table("hazards", 5, g.tHazards())
	d.table("imports", 13, g.tImports())
	d.table("include_cycles", 5, g.tCycles())
	d.table("layout", 11, g.tLayout())
	d.table("literals", 7, g.tLiterals())
	d.table("locals", 11, g.tLocals())
	d.table("locks", 5, g.tLocks())
	d.table("macros", 7, g.tMacros())
	d.table("makefile_rules", 7, g.tMakefileRules())
	d.table("markers", 6, g.tMarkers())
	d.table("memops", 10, g.tMemops())
	d.table("meta", 2, g.tMeta())
	d.table("modules", 10, g.tModules())
	d.table("params", 13, g.tParams())
	d.table("reach", 3, g.tReach())
	d.table("secret_candidates", 5, g.tSecrets())
	d.table("struct_size", 7, g.tStructSize())
	g.tFTS()
	d.table("symbols", 174, g.tSymbols())
	d.table("unresolved_calls", 4, g.tUnresolved())
	d.w.Flush()
}

func (g *Graph) tAddrTaken() [][]fval {
	out := make([][]fval, 0, len(g.Addr))
	for _, a := range g.Addr {
		out = append(out, []fval{fI32(a.ID), fOptInt(a.SymbolID, a.HasSym),
			fI32(a.FileID), fStr(a.Name()), fI32(a.Line), fStr(a.Kind())})
	}
	return out
}

func (g *Graph) tAllocSites() [][]fval {
	out := make([][]fval, 0, len(g.Allocs))
	for i, a := range g.Allocs {
		out = append(out, []fval{fInt(i + 1), fI32(a.SymbolID), fI32(a.FileID),
			fStr(a.Fn()), fStr(a.SizeExpr()), fI32(a.Line)})
	}
	return out
}

func (g *Graph) tAPIUse() [][]fval {
	out := make([][]fval, 0, len(g.APIUses))
	for i, a := range g.APIUses {
		out = append(out, []fval{fInt(i + 1), fI32(a.SymbolID), fI32(a.FileID),
			fStr(a.NS()), fStr(a.Fn()), fI32(a.Line)})
	}
	return out
}

func (g *Graph) tAttributes() [][]fval {
	out := make([][]fval, 0, len(g.Attrs))
	for i, a := range g.Attrs {
		out = append(out, []fval{fInt(i + 1), fOptInt(a.SymbolID, a.HasSymbolID),
			fI32(a.FileID), fStr(a.Name()), fOptStr(a.Args(), a.HasArgs), fI32(a.Line)})
	}
	return out
}

func (g *Graph) tCallsites() [][]fval {
	out := make([][]fval, 0, len(g.Callsites))
	for _, c := range g.Callsites {
		out = append(out, []fval{fI32(c.CallerID), fI32(c.CalleeID), fI32(c.Line)})
	}
	return out
}

func (g *Graph) tConfigBlocks() [][]fval {
	out := make([][]fval, 0, len(g.Cfgs))
	for i, c := range g.Cfgs {
		out = append(out, []fval{fInt(i + 1), fI32(c.FileID), fStr(c.Directive()),
			fStr(c.Expr()), fI32(c.Line), fI32(c.IsConfig)})
	}
	return out
}

func (g *Graph) tDeclarations() [][]fval {
	out := make([][]fval, 0, len(g.Decls))
	for i, c := range g.Decls {
		out = append(out, []fval{fInt(i + 1), fI32(c.FileID), fStr(c.Name()), fI32(c.Line)})
	}
	return out
}

func (g *Graph) tEdges() [][]fval {
	out := make([][]fval, 0, len(g.Edges))
	for _, e := range g.Edges {
		out = append(out, []fval{fI32(e.CallerID), fI32(e.CalleeID), fI32(e.NCalls),
			fI32(e.SameFile), fI32(e.SameModule), fI32(e.IsSelf)})
	}
	return out
}

func (g *Graph) tEnumMembers() [][]fval {
	out := make([][]fval, 0, len(g.EnumMem))
	for _, e := range g.EnumMem {
		out = append(out, []fval{fI32(e.SymbolID), fI32(e.Ordinal), fStr(e.Name()),
			fOptStr(e.Value(), e.HasValue), fI32(e.NFields)})
	}
	return out
}

func (g *Graph) tEventOps() [][]fval {
	out := make([][]fval, 0, len(g.EvOps))
	for i, e := range g.EvOps {
		out = append(out, []fval{fInt(i + 1), fI32(e.SymbolID), fI32(e.FileID),
			fStr(e.Family()), fStr(e.Fn()), fStr(e.Args()), fI32(e.Line)})
	}
	return out
}

func (g *Graph) tFields() [][]fval {
	out := make([][]fval, 0, len(g.Fields))
	for _, f := range g.Fields {
		out = append(out, []fval{fI32(f.SymbolID), fI32(f.Ordinal), fStr(f.Name()),
			fStr(f.Type()), fStr(f.Vis()), fI32(f.Line), fI32(f.IsStatic),
			fI32(f.IsConst), fI32(f.IsMutable), fI32(f.IsNullable),
			fI32(f.IsCollection), fI32(f.IsUntyped), fI32(f.HasDefault),
			fI32(f.TypeDepth)})
	}
	return out
}

func (g *Graph) tFiles() [][]fval {
	out := make([][]fval, 0, len(g.Files))
	for _, f := range g.Files {
		out = append(out, []fval{fI32(f.ID), fStr(f.Path()), fStr(f.Dir()),
			fStr(f.Basename()), fStr(f.Ext()), fStr(f.Lang()), fI32(f.ModuleID),
			fI32(f.Bytes), fI32(f.Lines), fI32(f.Sloc), fI32(f.BlankLines),
			fI32(f.CommentLines), fI32(f.DocLines), fI32(f.MaxLineLen),
			fStr(f.Sha1()), fI32(f.Parsed), fI32(f.IsTest), fI32(f.IsGenerated),
			fI32(f.IsVendored), fI32(f.NParseErrors), fI32(f.NMissingNodes),
			fF(f.ParseMs), fI32(f.NSymbols), fI32(f.NFunctions), fI32(f.NTypes),
			fI32(f.NImports), fI32(f.TotalCyclo), fI32(f.MaxCyclo),
			fI32(f.TotalRisk)})
	}
	return out
}

func (g *Graph) tGlobals() [][]fval {
	out := make([][]fval, 0, len(g.Globals))
	for i, m := range g.Globals {
		out = append(out, []fval{fInt(i + 1), fI32(m.FileID), fI32(m.ModuleID),
			fStr(m.Name()), fStr(m.Type()), fI32(m.Line), fI32(m.IsStatic),
			fI32(m.IsConst), fI32(m.IsVolatile), fI32(m.IsAtomic),
			fI32(m.IsArray), fI32(m.PtrDepth), fI32(m.HasInit)})
	}
	return out
}

func (g *Graph) tHazards() [][]fval {
	out := make([][]fval, 0, len(g.Hazards))
	for _, h := range g.Hazards {
		out = append(out, []fval{fI32(h.SymbolID), fStr(h.Pattern()),
			fStr(h.Category()), fI32(h.N), fI32(h.FirstLine)})
	}
	return out
}

func (g *Graph) tImports() [][]fval {
	out := make([][]fval, 0, len(g.Imports))
	for i, im := range g.Imports {
		out = append(out, []fval{fInt(i + 1), fI32(im.FileID), fStr(im.Target()),
			fOptInt(im.TargetID, im.HasTargetID),
			fOptStr(im.Alias(), im.HasAlias), fStr(im.Kind()), fI32(im.Line),
			fI32(im.IsExternal), fI32(im.IsRelative), fI32(im.IsWildcard),
			fI32(im.IsTypeOnly), fI32(im.IsDynamic), fI32(im.NNames)})
	}
	return out
}

func (g *Graph) tCycles() [][]fval {
	out := make([][]fval, 0, len(g.Cycles))
	for i, c := range g.Cycles {
		out = append(out, []fval{fInt(i + 1), fStr(c.APath()), fStr(c.BPath()),
			fI32(c.Length), fStr(c.Members())})
	}
	return out
}

func (g *Graph) tLayout() [][]fval {
	out := make([][]fval, 0, len(g.Layout))
	for _, l := range g.Layout {
		out = append(out, []fval{fI32(l.SymbolID), fI32(l.Ordinal),
			fI32(l.ByteOff), fI32(l.ByteSize), fI32(l.PadBefore), fI32(l.Exact),
			fI32(l.PtrDepth), fI32(l.ArrayLen), fI32(l.IsFnptr), fI32(l.Depth),
			fI32(l.InUnion)})
	}
	return out
}

func (g *Graph) tLiterals() [][]fval {
	out := make([][]fval, 0, len(g.Literals))
	for i, l := range g.Literals {
		out = append(out, []fval{fInt(i + 1), fOptInt(l.SymbolID, l.HasSym),
			fI32(l.FileID), fStr(l.Kind()), fStr(l.Value()), fI32(l.Line),
			fI32(l.IsMagic)})
	}
	return out
}

func (g *Graph) tLocals() [][]fval {
	out := make([][]fval, 0, len(g.Locals))
	for _, l := range g.Locals {
		out = append(out, []fval{fI32(l.SymbolID), fI32(l.Ordinal), fStr(l.Name()),
			fStr(l.Type()), fI32(l.Line), fI32(l.IsConst), fI32(l.IsMutable),
			fI32(l.IsUntyped), fI32(l.HasInit), fI32(l.InLoop),
			fI32(l.ScopeDepth)})
	}
	return out
}

func (g *Graph) tLocks() [][]fval {
	out := make([][]fval, 0, len(g.Locks))
	for i, l := range g.Locks {
		out = append(out, []fval{fInt(i + 1), fI32(l.SymbolID), fI32(l.FileID),
			fStr(l.Name()), fI32(l.Line)})
	}
	return out
}

func (g *Graph) tMacros() [][]fval {
	out := make([][]fval, 0, len(g.Macros))
	for _, m := range g.Macros {
		out = append(out, []fval{fI32(m.SymbolID), fI32(m.IsFunctionlike),
			fI32(m.NParams), fOptStr(m.Body(), m.HasBody), fI32(m.BodyLen),
			fI32(m.IsMultiline), fI32(m.NUses)})
	}
	return out
}

func (g *Graph) tMakefileRules() [][]fval {
	out := make([][]fval, 0, len(g.MkRules))
	for i, m := range g.MkRules {
		out = append(out, []fval{fInt(i + 1), fStr(m.Path()), fStr(m.Rule()),
			fI32(m.Line), fI32(m.NObjs), fI32(m.NSrcs), fI32(m.UsesAr)})
	}
	return out
}

func (g *Graph) tMarkers() [][]fval {
	out := make([][]fval, 0, len(g.Markers))
	for i, m := range g.Markers {
		out = append(out, []fval{fInt(i + 1), fI32(m.FileID),
			fOptInt(m.SymbolID, m.HasSym), fStr(m.Kind()), fI32(m.Line), fStr(m.Text())})
	}
	return out
}

func (g *Graph) tMemops() [][]fval {
	out := make([][]fval, 0, len(g.Memops))
	for i, m := range g.Memops {
		out = append(out, []fval{fInt(i + 1), fI32(m.SymbolID), fI32(m.FileID),
			fStr(m.Fn()), fStr(m.Dst()), fStr(m.Src()), fStr(m.SizeArg()),
			fStr(m.SizeBuf()), fStr(m.DstTail()), fI32(m.Line)})
	}
	return out
}

var metaOrder = []string{"addr_taken_pruned", "calls_resolved", "files_failed",
	"files_parsed", "files_skipped", "grammar_note", "imports_resolved", "lang",
	"layout_model", "makefiles_read", "parse_mode", "parser", "root",
	"schema_version", "sqlite", "target"}

func (g *Graph) tMeta() [][]fval {
	out := make([][]fval, 0, len(metaOrder))
	for _, k := range metaOrder {
		v, ok := g.Meta[k]
		if !ok {
			continue
		}
		out = append(out, []fval{fStr(k), fStr(v)})
	}
	return out
}

func (g *Graph) tModules() [][]fval {
	out := make([][]fval, 0, len(g.Modules))
	for _, m := range g.Modules {
		out = append(out, []fval{fI32(m.ID), fStr(m.Name()), fStr(m.Kind()),
			fI32(m.NFiles), fI32(m.NSymbols), fI32(m.NPublic), fI32(m.Sloc),
			fI32(m.FanIn), fI32(m.FanOut), fF(m.Instability)})
	}
	return out
}

func (g *Graph) tParams() [][]fval {
	out := make([][]fval, 0, len(g.Params))
	for _, p := range g.Params {
		out = append(out, []fval{fI32(p.SymbolID), fI32(p.Pos),
			fOptStr(p.Name(), p.HasName), fStr(p.Type()),
			fOptStr(p.Default(), p.HasDefaultValue), fI32(p.IsOptional),
			fI32(p.IsVariadic), fI32(p.IsRef), fI32(p.IsMutable),
			fI32(p.IsNullable), fI32(p.IsGeneric), fI32(p.IsUntyped),
			fI32(p.TypeDepth)})
	}
	return out
}

func (g *Graph) tReach() [][]fval {
	out := make([][]fval, 0, len(g.Reach))
	for _, r := range g.Reach {
		out = append(out, []fval{fI32(r.SymbolID), fI32(r.NTransitive),
			fI32(r.NTransitiveOut)})
	}
	return out
}

func (g *Graph) tSecrets() [][]fval {
	out := make([][]fval, 0, len(g.Secrets))
	for i, s := range g.Secrets {
		out = append(out, []fval{fInt(i + 1), fOptInt(s.SymbolID, s.HasSym),
			fI32(s.FileID), fStr(s.Value()), fI32(s.Line)})
	}
	return out
}

func (g *Graph) tStructSize() [][]fval {
	out := make([][]fval, 0, len(g.SSize))
	for _, s := range g.SSize {
		out = append(out, []fval{fI32(s.SymbolID), fI32(s.TotalSize),
			fI32(s.TailPad), fI32(s.TotalPad), fI32(s.MaxAlign), fI32(s.Exact),
			fI32(s.NLines64)})
	}
	return out
}

func (g *Graph) tUnresolved() [][]fval {
	out := make([][]fval, 0, len(g.Unres))
	for _, u := range g.Unres {
		out = append(out, []fval{fI32(u.CallerID), fStr(u.Name()), fI32(u.N),
			fI32(u.FirstLine)})
	}
	return out
}

const target = "C23 (ISO/IEC 9899:2024) + GNU extensions tolerated (real preprocessor)"

type qentry struct {
	name  string
	title string
	notes string
	run   func(g *Graph, p params) (cols []string, rows [][]fval)
}

func main() {
	if v := os.Getenv("CGORD"); v != "" {
		scanOrder = v
	}

	args := os.Args[1:]
	for _, a := range args {
		if a == "-h" || a == "--help" {

			usage()
			return
		}
	}
	var positional []string
	flags := map[string]string{}
	boolFlags := map[string]bool{}
	for i := 0; i < len(args); i++ {
		a := args[i]
		if isNegNumber(a) || !strings.HasPrefix(a, "-") {
			positional = append(positional, a)
			continue
		}
		name := strings.TrimLeft(a, "-")
		val := ""
		if j := strings.IndexByte(name, '='); j >= 0 {
			val, name = name[j+1:], name[:j]
		} else if i+1 < len(args) && (!strings.HasPrefix(args[i+1], "-") ||
			isNegNumber(args[i+1])) && takesValue(name) {
			val = args[i+1]
			i++
		}
		if !knownFlag(name) {
			usage()
			fmt.Fprintf(os.Stderr, "codegraph_c: error: unrecognized arguments: %s\n", a)
			os.Exit(2)
		}
		if takesValue(name) {
			flags[name] = val
		} else {
			boolFlags[name] = true
		}
	}

	qv := map[string]bool{}
	for _, k := range []string{"list", "metrics", "report", "quiet", "no-tests",
		"include-generated", "include-vendored", "version", "deps", "force",
		"install-deps", "schema"} {
		if boolFlags[k] {
			qv[k] = true
		}
	}
	lim := -1
	if v, ok := flags["limit"]; ok {
		n, err := strconv.Atoi(v)
		if err != nil {
			invalidArg("--limit", v)
		}
		lim = n
	}
	modPat := "%"
	if v, ok := flags["module"]; ok {
		modPat = v
	}
	csvN, jsonN := -1, -1
	csvSet, jsonSet := false, false
	if v, ok := flags["csv"]; ok {
		csvSet = true
		n, err := strconv.Atoi(v)
		if err != nil {
			invalidArg("--csv", v)
		}
		csvN = n
	}
	if v, ok := flags["json"]; ok {
		jsonSet = true
		n, err := strconv.Atoi(v)
		if err != nil {
			invalidArg("--json", v)
		}
		jsonN = n
	}
	dumpPath := flags["dump"]
	savePath := flags["save"]
	saveAST := flags["save-ast"]
	loadASTPath := flags["load-ast"]
	if saveAST != "" && loadASTPath != "" {
		fmt.Fprintln(os.Stderr, "--save-ast and --load-ast cannot be used together")
		os.Exit(2)
	}

	if qv["version"] {
		fmt.Printf("codegraph_c  target=%s  schema=v2  go=%s\n", target, goVersion())
		return
	}
	if qv["deps"] || qv["install-deps"] {
		fmt.Println("dependencies for codegraph-c:")
		fmt.Println("  (none -- pure standard library)")
		return
	}
	if qv["schema"] {
		fmt.Print(schemaNative())
		return
	}

	cat := queries
	if qv["metrics"] {
		cat = metricsCat
	}
	if qv["list"] {
		for i, q := range cat {
			fmt.Printf("%2d. %-26s %s\n", i+1, q.name, q.title)
		}
		return
	}

	dir := "."
	if len(positional) > 0 {
		dir = positional[0]
	}
	var sel []int
	if len(positional) > 1 {
		for _, p := range positional[1:] {
			if n, err := strconv.Atoi(p); err == nil {
				sel = append(sel, n)
			}
		}
	}
	if loadASTPath == "" {
		if st, err := os.Stat(dir); err != nil || !st.IsDir() {
			fmt.Fprintf(os.Stderr, "not a directory: %s\n", dir)
			os.Exit(2)
		}
	}

	if csvSet || jsonSet {
		qv["quiet"] = true
	}
	quiet := qv["quiet"]

	var g *Graph
	t0 := time.Now()
	var n int
	if loadASTPath != "" {
		var err error
		g, err = loadAST(loadASTPath)
		if err != nil {
			fmt.Fprintf(os.Stderr, "load-ast: %v\n", err)
			os.Exit(2)
		}
		n = len(g.Files)
	} else {
		g = &Graph{}
		opts := runOpts{includeTests: !qv["no-tests"],
			includeGenerated: qv["include-generated"],
			includeVendored:  qv["include-vendored"], quiet: quiet,
			keepAST: saveAST != ""}
		n = build(g, dir, opts, quiet)
	}
	took := time.Since(t0)

	if saveAST != "" {
		if _, serr := os.Lstat(saveAST); serr == nil && !qv["force"] {
			fmt.Fprintf(os.Stderr, "refusing to overwrite %s (pass --force)\n", saveAST)
			os.Exit(2)
		}
		ts := time.Now()
		nb, werr := saveASTFile(g, saveAST)
		if werr != nil {
			fmt.Fprintf(os.Stderr, "save-ast: %v\n", werr)
			os.Exit(2)
		}
		if !quiet {
			fmt.Fprintf(os.Stderr, "ast state written to %s: %d bytes in %.1fs\n",
				saveAST, nb, time.Since(ts).Seconds())
		}
	}

	if dumpPath != "" {
		f, err := os.Create(dumpPath)
		if err != nil {
			fmt.Fprintf(os.Stderr, "could not write %s: %v\n", dumpPath, err)
			os.Exit(2)
		}
		bw := bufio.NewWriterSize(f, 1<<20)
		g.dump(bw)
		bw.Flush()
		f.Close()
	}

	p := params{mod: modPat, lim: lim}
	if csvSet || jsonSet {
		n2 := csvN
		if n2 < 0 {
			n2 = jsonN
		}

		if n2 < 1 || n2 > len(cat) {
			fmt.Fprintf(os.Stderr, "no query %d\n", n2)
			os.Exit(2)
		}
		cols, rows := cat[n2-1].run(g, p)
		if csvN >= 0 {
			w := csv.NewWriter(os.Stdout)

			w.UseCRLF = true
			w.Write(cols)
			for _, r := range rows {
				w.Write(fieldStrings(r))
			}
			w.Flush()
		} else {
			enc := json.NewEncoder(os.Stdout)
			enc.SetIndent("", "  ")
			enc.SetEscapeHTML(false)
			out := make([]orderedObj, 0, len(rows))
			for _, r := range rows {
				m := orderedObj{}
				for i, c := range cols {
					m = append(m, orderedKV{Key: c, Val: jsonValue(r[i])})
				}
				out = append(out, m)
			}
			enc.Encode(out)
		}
		return
	}

	if !quiet {
		limStr := "all"
		if lim >= 0 {
			limStr = itoa(lim)
		}
		if loadASTPath != "" {
			fmt.Printf("codegraph-c: %d files loaded from AST in %.1fs module=%s limit=%s\n",
				n, took.Seconds(), modPat, limStr)
		} else {
			fmt.Printf("codegraph-c: %d files parsed into memory in %.1fs module=%s limit=%s\n",
				n, took.Seconds(), modPat, limStr)
		}
	}
	if qv["report"] {
		report(g)
	}
	if len(sel) == 0 {
		for i := 1; i <= len(cat); i++ {
			sel = append(sel, i)
		}
	}
	w := bufio.NewWriterSize(os.Stdout, 1<<16)
	for _, k := range sel {
		if k < 1 || k > len(cat) {
			continue
		}
		q := cat[k-1]
		fmt.Fprintf(w, "\n%s\n", strings.Repeat("=", 78))
		fmt.Fprintf(w, "Q%d. %s -- %s\n", k, q.name, q.title)
		fmt.Fprintf(w, "%s\n", strings.Repeat("-", 78))
		for _, line := range splitNotes(q.notes) {
			fmt.Fprintf(w, " %s\n", line)
		}
		fmt.Fprintln(w)
		cols, rows := q.run(g, p)
		render(w, rows, cols)
	}
	w.Flush()
	saveGraph(g, savePath, qv["force"])
}

func symlinkReal(link string) string {
	tgt, err := os.Readlink(link)
	if err != nil {
		return link
	}
	if !filepath.IsAbs(tgt) {
		tgt = filepath.Join(filepath.Dir(link), tgt)
	}
	if r, err := filepath.EvalSymlinks(tgt); err == nil {
		return r
	}
	if r, err := filepath.EvalSymlinks(filepath.Dir(tgt)); err == nil {
		return filepath.Join(r, filepath.Base(tgt))
	}
	return tgt
}

func saveGraph(g *Graph, path string, force bool) {
	if path == "" {
		return
	}
	if fi, err := os.Lstat(path); err == nil {
		if fi.Mode()&os.ModeSymlink != 0 {
			if !force {
				fmt.Fprintf(os.Stderr,
					"refusing to overwrite %s (pass --force) -- it is a symlink to %s\n",
					path, symlinkReal(path))
				return
			}
			os.Remove(path)
		} else if !force {
			fmt.Fprintf(os.Stderr, "refusing to overwrite %s (pass --force)\n", path)
			return
		}
	}
	f, err := os.Create(path)
	if err != nil {
		fmt.Fprintf(os.Stderr, "could not write %s: %v\n", path, err)
		os.Exit(2)
	}
	bw := bufio.NewWriterSize(f, 1<<20)
	g.dump(bw)
	bw.Flush()
	f.Close()
	fmt.Printf("(graph also written to %s)\n", path)
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

type cgMetaRow struct{ K, V cgStr }

func (m *cgMetaRow) Key() string { return m.K.Str() }
func (m *cgMetaRow) Val() string { return m.V.Str() }

func (s cgStr) Str() string {
	if s.Ln == 0 {
		return ""
	}
	return unsafe.String(&cgArena[s.Off], int(s.Ln))
}

var cgZero [4096]byte

func cgZeroRow(p unsafe.Pointer, n uintptr) {
	copy(unsafe.Slice((*byte)(p), n)[:n], cgZero[:n])
}

func cgasBytes[T any](rows []T) []byte {
	if len(rows) == 0 {
		return nil
	}
	return unsafe.Slice((*byte)(unsafe.Pointer(&rows[0])), len(rows)*int(unsafe.Sizeof(rows[0])))
}

const cgasMagic = "CGAS"

const (
	cgasVersion  = 4
	cgasHeaderSz = 32
	cgasSecSz    = 24
	cgasNSec     = 36
	cgasArenaLo  = 1 << 20
)

const (
	cgasSecStrings uint32 = 1 + iota
	cgasSecFiles
	cgasSecMods
	cgasSecSyms
	cgasSecRare
	cgasSecParams
	cgasSecFields
	cgasSecLocals
	cgasSecLits
	cgasSecMark
	cgasSecAttrs
	cgasSecImps
	cgasSecHaz
	cgasSecEnums
	cgasSecLayout
	cgasSecSSize
	cgasSecDecls
	cgasSecAddr
	cgasSecSecrets
	cgasSecAllocs
	cgasSecMemops
	cgasSecMacros
	cgasSecGlobals
	cgasSecCfgs
	cgasSecReach
	cgasSecMkRules
	cgasSecLocks
	cgasSecEvOps
	cgasSecAPIUses
	cgasSecCycles
	cgasSecEdges
	cgasSecSites
	cgasSecUnres
	cgasSecMeta
	cgasSecCounters
	cgasSecTrees
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

type cgasCounters struct {
	FilesParsed, FilesFailed               int32
	EdgesN, MacroN, ExternN, DeclN, UnresN int32
	CallsTotal, AddrPruned, MakefilesRead  int32
	FilesSkippedBig, FilesSkippedSpecial   int32
	FilesSkippedEscape, FilesSkippedDenied int32
	WalkErrors, Pad                        int32
}

func cgasI16(v int32, what string) int16 {
	if v < -32768 || v > 32767 {
		panic("cgas: " + what + " = " + itoa(int(v)) + " exceeds int16 state width")
	}
	return int16(v)
}

func cgasFlag(v int32, what string) uint8 {
	if v < 0 || v > 1 {
		panic("cgas: " + what + " = " + itoa(int(v)) + " is not a 0/1 flag")
	}
	return uint8(v)
}

func cgasU8(v int32, what string) uint8 {
	if v < 0 || v > 255 {
		panic("cgas: " + what + " = " + itoa(int(v)) + " exceeds uint8 state width")
	}
	return uint8(v)
}

type cgasSymN struct {
	Name                                                                              cgStr
	QualName                                                                          cgStr
	Kind                                                                              cgStr
	Signature                                                                         cgStr
	ReturnType                                                                        cgStr
	ID, FileID, ModuleID, LineStart                                                   int32
	Sloc, NCommentLines, NTokens, NOperators                                          int32
	NOperands, Rare                                                                   int32
	NParams, Cyclomatic, Cognitive, MaxNesting, NDistinctOperators, NDistinctOperands int16
	NLoops, NBranches, NReturns, NSwitch, NCases, NLabels                             int16
	NGotos, MaxLoopDepth, CallInLoop, AllocInLoop, IOInLoop, LockInLoop               int16
	BranchInLoop, NLocals, NCmp, NArith, NShift, NFloatLit                            int16
	NMagic, NNullCheck, NCalls, NDynamicCalls, NUnresolvedCalls, FanIn                int16
	FanOut, NCallsites, RiskScore, NMemory, NAlloc, NIO                               int16
	NStdio, NExec, NLibm, NInteger, NConcurrency, NReentrancy                         int16
	NPtrLocals, NDeref, NCast, NSizeof, NIntrinsic, NAtomic                           int16
	NRestrict, NLikely, NBuiltin                                                      int16
	HasSignature, HasReturnType                                                       bool
	IsPublic, IsStatic, IsAbstract, IsOverride                                        uint8
	IsTest, IsEntrypoint, IsGenerated, HasDoc                                         uint8
	IsRecursive, IsInline, IsVariadic                                                 uint8
}

type cgasRareN struct {
	SwitchInLoop, LibmInLoop, DivInLoop, StrlenInLoop, RetNull, RetNeg                           int16
	RetZero, RetVal, RetVoid, NFnptrCalls, NMacroCalls, NExternalCalls                           int16
	NFree, NConstCast, NToctou, NLockAcquire, NLockRelease, NNarrowCast                          int16
	NSignCmp, NVariadicFmt, NMemcpy, NAllocsite, NGlobalWrite, NErrno                            int16
	NWeakRandom, NShiftVar, NReallocSelf, NVla, NGetenv, NAssertSide                             int16
	NFreeThenUse, NEpoll, NUring, NKqueue, NEventWait, NEtReg                                    int16
	NOneshotReg, NWriteReady, NErrFlag, NRearm, NDereg, NEagain                                  int16
	NEintr, NUringRes, NUringRing, NUringBarrier, NUringSqpoll, NNonblockSet                     int16
	NEventCreate, NEventDestroy, NUringSqe, NUringSeen, NUringUdata, NUringLink                  int16
	NUringStreamOps, NUringTeardown, NEvTimeoutIndefinite, NEvTimeoutZero, NEvBatchOne, NKqTimer int16
	NKqTimerZeroData, NKqReceipt, NRetNegCheck, NDomainGuard, NUcharCast, NErrnoZero             int16
	NEndptr, NVaEnd, NMapFailed, NMonotonicClock, NStackszArray, NPtrOvfCheck                    int16
	NCallocTransposed, NVaArgArr                                                                 int16
}

type cgasParamN struct {
	Name                                     cgStr
	Type                                     cgStr
	DefaultValue                             cgStr
	SymbolID                                 int32
	Pos, TypeDepth                           int16
	HasName, HasDefaultValue                 bool
	IsOptional, IsVariadic, IsRef, IsMutable uint8
	IsNullable, IsGeneric, IsUntyped         uint8
}

type cgasFieldN struct {
	Name                                     cgStr
	Type                                     cgStr
	Visibility                               cgStr
	SymbolID, Line                           int32
	Ordinal, TypeDepth                       int16
	IsStatic, IsConst, IsMutable, IsNullable uint8
	IsCollection, IsUntyped, HasDefault      uint8
}

type cgasLocalN struct {
	Name                                   cgStr
	Type                                   cgStr
	SymbolID, Line                         int32
	Ordinal                                int16
	IsConst, IsMutable, IsUntyped, HasInit uint8
	InLoop, ScopeDepth                     uint8
}

func cgasBoolOffs[T any]() []uintptr {
	t := reflect.TypeFor[T]()
	var out []uintptr
	for i := 0; i < t.NumField(); i++ {
		if t.Field(i).Type.Kind() == reflect.Bool {
			out = append(out, t.Field(i).Offset)
		}
	}
	return out
}

var (
	symNBoolOffs    = cgasBoolOffs[cgasSymN]()
	paramNBoolOffs  = cgasBoolOffs[cgasParamN]()
	importBoolOffs  = cgasBoolOffs[Import]()
	attrBoolOffs    = cgasBoolOffs[Attribute]()
	literalBoolOffs = cgasBoolOffs[Literal]()
	enumBoolOffs    = cgasBoolOffs[EnumMember]()
	addrBoolOffs    = cgasBoolOffs[AddrTaken]()
	secretBoolOffs  = cgasBoolOffs[SecretCandidate]()
	macroBoolOffs   = cgasBoolOffs[Macro]()
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
	fail(unsafe.Sizeof(cgStr{}) == 16, "cgStr must be the 16-byte {offset,length} pair")
	fail(unsafe.Sizeof(cgMetaRow{}) == 32, "cgMetaRow must be 32 bytes")
	fail(unsafe.Sizeof(cgasCounters{}) == 64, "cgasCounters must be 64 bytes")
	fail(unsafe.Sizeof(cgasSymN{}) == 240, "cgasSymN must be 240 bytes")
	fail(unsafe.Sizeof(cgasRareN{}) == 148, "cgasRareN must be 148 bytes")
	fail(unsafe.Sizeof(cgasParamN{}) == 72, "cgasParamN must be 72 bytes")
	fail(unsafe.Sizeof(cgasFieldN{}) == 72, "cgasFieldN must be 72 bytes")
	fail(unsafe.Sizeof(cgasLocalN{}) == 48, "cgasLocalN must be 48 bytes")
	fail(unsafe.Sizeof(cgasSymN{}) < unsafe.Sizeof(Symbol{}), "cgasSymN must narrow Symbol")
	fail(unsafe.Sizeof(cgasRareN{}) < unsafe.Sizeof(symRare{}), "cgasRareN must narrow symRare")
	fail(unsafe.Sizeof(cgasParamN{}) < unsafe.Sizeof(Param{}), "cgasParamN must narrow Param")
	fail(unsafe.Sizeof(cgasFieldN{}) < unsafe.Sizeof(Field{}), "cgasFieldN must narrow Field")
	fail(unsafe.Sizeof(cgasLocalN{}) < unsafe.Sizeof(Local{}), "cgasLocalN must narrow Local")
	for _, t := range []reflect.Type{
		reflect.TypeOf(File{}),
		reflect.TypeOf(Module{}),
		reflect.TypeOf(Symbol{}),
		reflect.TypeOf(symRare{}),
		reflect.TypeOf(Param{}),
		reflect.TypeOf(Field{}),
		reflect.TypeOf(Local{}),
		reflect.TypeOf(Literal{}),
		reflect.TypeOf(Marker{}),
		reflect.TypeOf(Attribute{}),
		reflect.TypeOf(Import{}),
		reflect.TypeOf(Hazard{}),
		reflect.TypeOf(EnumMember{}),
		reflect.TypeOf(LayoutRow{}),
		reflect.TypeOf(StructSize{}),
		reflect.TypeOf(Declaration{}),
		reflect.TypeOf(AddrTaken{}),
		reflect.TypeOf(SecretCandidate{}),
		reflect.TypeOf(AllocSite{}),
		reflect.TypeOf(Memop{}),
		reflect.TypeOf(Macro{}),
		reflect.TypeOf(Global{}),
		reflect.TypeOf(ConfigBlock{}),
		reflect.TypeOf(Reach{}),
		reflect.TypeOf(MakefileRule{}),
		reflect.TypeOf(LockRow{}),
		reflect.TypeOf(EventOp{}),
		reflect.TypeOf(APIUse{}),
		reflect.TypeOf(IncludeCycle{}),
		reflect.TypeOf(Edge{}),
		reflect.TypeOf(Callsite{}),
		reflect.TypeOf(Unresolved{}),
		reflect.TypeOf(cgasCounters{}),
		reflect.TypeOf(cgasSymN{}),
		reflect.TypeOf(cgasRareN{}),
		reflect.TypeOf(cgasParamN{}),
		reflect.TypeOf(cgasFieldN{}),
		reflect.TypeOf(cgasLocalN{}),
		reflect.TypeOf(int32(0)),
		reflect.TypeOf(uint32(0)),
	} {
		fail(!cgasHasGoRef(t), t.String()+" must be raw-castable")
	}
}

func cgasHasGoRef(t reflect.Type) bool {
	switch t.Kind() {
	case reflect.Pointer, reflect.Slice, reflect.Map,
		reflect.Chan, reflect.Func, reflect.Interface, reflect.UnsafePointer,
		reflect.Complex64, reflect.Complex128:
		return true
	case reflect.Array:
		return cgasHasGoRef(t.Elem())
	case reflect.Struct:
		for i := 0; i < t.NumField(); i++ {
			if cgasHasGoRef(t.Field(i).Type) {
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

func knownFlag(n string) bool {
	switch n {
	case "module", "limit", "csv", "json", "save", "dump", "save-ast", "load-ast":
		return true
	case "list", "metrics", "report", "quiet", "no-tests", "include-generated",
		"include-vendored", "version", "deps", "force", "install-deps",
		"schema", "help", "h":
		return true
	}
	return false
}

func invalidArg(flag, val string) {
	usage()
	fmt.Fprintf(os.Stderr, "codegraph_c: error: argument %s: invalid int value: '%s'\n", flag, val)
	os.Exit(2)
}

func takesValue(n string) bool {
	switch n {
	case "module", "limit", "csv", "json", "save", "dump", "save-ast", "load-ast":
		return true
	}
	return false
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

func usage() {
	fmt.Printf(`usage: codegraph_c [-h] [--module MODULE] [--limit LIMIT] [--list]
                      [--json N] [--save PATH] [--save-ast PATH] [--load-ast PATH]
                      [--force] [--deps]
                      [--install-deps] [--include-generated]
                      [--include-vendored] [--no-tests] [--quiet] [--version]
                      [root] [which ...]

Parse a c tree into an in-memory graph and query it in one shot. Target: %s
`, target)
}

func fieldStrings(r []fval) []string {
	out := make([]string, len(r))
	for i, v := range r {
		switch v.kind {
		case fkNull:
			out[i] = ""
		case fkInt:
			out[i] = strconv.FormatInt(v.i, 10)
		case fkFloat:
			out[i] = strconv.FormatFloat(v.f, 'g', -1, 64)
		default:
			out[i] = v.s
		}
	}
	return out
}

func jsonValue(v fval) any {
	switch v.kind {
	case fkNull:
		return nil
	case fkInt:
		return v.i
	case fkFloat:
		return v.f
	default:
		return cgJSONString(v.s)
	}
}

type orderedKV struct {
	Key string
	Val any
}

type orderedObj []orderedKV

func (o orderedObj) MarshalJSON() ([]byte, error) {
	var b []byte
	b = append(b, '{')
	for i, kv := range o {
		if i > 0 {
			b = append(b, ',')
		}
		k, err := json.Marshal(kv.Key)
		if err != nil {
			return nil, err
		}
		b = append(b, k...)
		b = append(b, ':')
		v, err := json.Marshal(kv.Val)
		if err != nil {
			return nil, err
		}
		b = append(b, v...)
	}
	b = append(b, '}')
	return b, nil
}

type cgJSONString string

func (s cgJSONString) MarshalJSON() ([]byte, error) {
	return []byte(cgJSONQuote(string(s))), nil
}

func cgJSONQuote(s string) string {
	var b strings.Builder
	b.Grow(len(s) + 2)
	b.WriteByte('"')
	for _, r := range s {
		switch r {
		case '"':
			b.WriteString(`\"`)
		case '\\':
			b.WriteString(`\\`)
		case '\b':
			b.WriteString(`\b`)
		case '\f':
			b.WriteString(`\f`)
		case '\n':
			b.WriteString(`\n`)
		case '\r':
			b.WriteString(`\r`)
		case '\t':
			b.WriteString(`\t`)
		default:
			if r < 0x20 {
				fmt.Fprintf(&b, `\u%04x`, r)
			} else if r < 0x80 {
				b.WriteByte(byte(r))
			} else if r <= 0xFFFF {
				fmt.Fprintf(&b, `\u%04x`, r)
			} else {
				r -= 0x10000
				fmt.Fprintf(&b, `\u%04x\u%04x`, 0xD800+(r>>10), 0xDC00+(r&0x3FF))
			}
		}
	}
	b.WriteByte('"')
	return b.String()
}

const maxCell = 72

func cell(v fval) string {
	var t string
	switch v.kind {
	case fkNull:
		return "-"
	case fkFloat:
		t = fmt.Sprintf("%.2f", v.f)
	case fkInt:
		t = strconv.FormatInt(v.i, 10)
	default:
		t = v.s
	}
	r := []rune(t)
	if len(r) <= maxCell {
		return t
	}
	return string(r[:maxCell-3]) + "..."
}

func render(w *bufio.Writer, rows [][]fval, cols []string) {
	if len(rows) == 0 {
		fmt.Fprintln(w, " (no rows)")
		return
	}
	body := make([][]string, len(rows))
	for i, r := range rows {
		body[i] = make([]string, len(r))
		for j, v := range r {
			body[i][j] = cell(v)
		}
	}
	widths := make([]int, len(cols))
	for i, c := range cols {
		widths[i] = len([]rune(c))
	}
	for _, r := range body {
		for i, c := range r {
			if n := len([]rune(c)); n > widths[i] {
				widths[i] = n
			}
		}
	}
	head := make([]string, len(cols))
	dash := make([]string, len(cols))
	for i, c := range cols {
		head[i] = pad(c, widths[i])
		dash[i] = strings.Repeat("-", widths[i])
	}
	fmt.Fprintf(w, " %s\n", strings.Join(head, " "))
	fmt.Fprintf(w, " %s\n", strings.Join(dash, " "))
	for _, r := range body {
		cells := make([]string, len(r))
		for i, c := range r {
			cells[i] = pad(c, widths[i])
		}
		fmt.Fprintf(w, " %s\n", strings.Join(cells, " "))
	}
}

func pad(s string, w int) string {
	n := w - len([]rune(s))
	if n <= 0 {
		return s
	}
	return s + strings.Repeat(" ", n)
}

func goVersion() string { return "go1.27" }

var _ = sort.Ints

func splitNotes(s string) []string {
	if s == "" {
		return nil
	}
	out := strings.Split(s, "\n")
	for len(out) > 0 && out[len(out)-1] == "" {
		out = out[:len(out)-1]
	}
	return out
}
func cgasCastRows[T any](mem []byte, off, ln uint64, what string) ([]T, error) {
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

func cgasStrFields[T any]() []uintptr {
	var p *T
	switch any(p).(type) {
	case *File:
		return []uintptr{unsafe.Offsetof(File{}.path), unsafe.Offsetof(File{}.dir),
			unsafe.Offsetof(File{}.basename), unsafe.Offsetof(File{}.ext),
			unsafe.Offsetof(File{}.lang), unsafe.Offsetof(File{}.sha1)}
	case *Module:
		return []uintptr{unsafe.Offsetof(Module{}.name), unsafe.Offsetof(Module{}.kind)}
	case *Symbol:
		return []uintptr{unsafe.Offsetof(Symbol{}.name), unsafe.Offsetof(Symbol{}.qualName),
			unsafe.Offsetof(Symbol{}.kind), unsafe.Offsetof(Symbol{}.signature),
			unsafe.Offsetof(Symbol{}.returnType)}
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
	case *Attribute:
		return []uintptr{unsafe.Offsetof(Attribute{}.name), unsafe.Offsetof(Attribute{}.args)}
	case *Literal:
		return []uintptr{unsafe.Offsetof(Literal{}.kind), unsafe.Offsetof(Literal{}.value)}
	case *EnumMember:
		return []uintptr{unsafe.Offsetof(EnumMember{}.name), unsafe.Offsetof(EnumMember{}.value)}
	case *Marker:
		return []uintptr{unsafe.Offsetof(Marker{}.kind), unsafe.Offsetof(Marker{}.text)}
	case *Declaration:
		return []uintptr{unsafe.Offsetof(Declaration{}.name)}
	case *AddrTaken:
		return []uintptr{unsafe.Offsetof(AddrTaken{}.name), unsafe.Offsetof(AddrTaken{}.kind)}
	case *SecretCandidate:
		return []uintptr{unsafe.Offsetof(SecretCandidate{}.value)}
	case *AllocSite:
		return []uintptr{unsafe.Offsetof(AllocSite{}.fn), unsafe.Offsetof(AllocSite{}.sizeExpr)}
	case *Memop:
		return []uintptr{unsafe.Offsetof(Memop{}.fn), unsafe.Offsetof(Memop{}.dst),
			unsafe.Offsetof(Memop{}.src), unsafe.Offsetof(Memop{}.sizeArg),
			unsafe.Offsetof(Memop{}.sizeBuf), unsafe.Offsetof(Memop{}.dstTail)}
	case *Macro:
		return []uintptr{unsafe.Offsetof(Macro{}.body)}
	case *Global:
		return []uintptr{unsafe.Offsetof(Global{}.name), unsafe.Offsetof(Global{}.typ)}
	case *ConfigBlock:
		return []uintptr{unsafe.Offsetof(ConfigBlock{}.directive), unsafe.Offsetof(ConfigBlock{}.expr)}
	case *MakefileRule:
		return []uintptr{unsafe.Offsetof(MakefileRule{}.path), unsafe.Offsetof(MakefileRule{}.rule)}
	case *LockRow:
		return []uintptr{unsafe.Offsetof(LockRow{}.name)}
	case *EventOp:
		return []uintptr{unsafe.Offsetof(EventOp{}.family), unsafe.Offsetof(EventOp{}.fn),
			unsafe.Offsetof(EventOp{}.args)}
	case *APIUse:
		return []uintptr{unsafe.Offsetof(APIUse{}.ns), unsafe.Offsetof(APIUse{}.fn)}
	case *IncludeCycle:
		return []uintptr{unsafe.Offsetof(IncludeCycle{}.aPath), unsafe.Offsetof(IncludeCycle{}.bPath),
			unsafe.Offsetof(IncludeCycle{}.members)}
	case *cgMetaRow:
		return []uintptr{unsafe.Offsetof(cgMetaRow{}.K), unsafe.Offsetof(cgMetaRow{}.V)}
	case *cgasSymN:
		return []uintptr{unsafe.Offsetof(cgasSymN{}.Name), unsafe.Offsetof(cgasSymN{}.QualName),
			unsafe.Offsetof(cgasSymN{}.Kind), unsafe.Offsetof(cgasSymN{}.Signature),
			unsafe.Offsetof(cgasSymN{}.ReturnType)}
	case *cgasParamN:
		return []uintptr{unsafe.Offsetof(cgasParamN{}.Name), unsafe.Offsetof(cgasParamN{}.Type),
			unsafe.Offsetof(cgasParamN{}.DefaultValue)}
	case *cgasFieldN:
		return []uintptr{unsafe.Offsetof(cgasFieldN{}.Name), unsafe.Offsetof(cgasFieldN{}.Type),
			unsafe.Offsetof(cgasFieldN{}.Visibility)}
	case *cgasLocalN:
		return []uintptr{unsafe.Offsetof(cgasLocalN{}.Name), unsafe.Offsetof(cgasLocalN{}.Type)}
	}
	return nil
}

func cgasCheckStrRefs[T any](rows []T, arenaLen uint64, what string) error {
	if len(rows) == 0 {
		return nil
	}
	n := int(unsafe.Sizeof(rows[0]))
	base := unsafe.Pointer(&rows[0])
	for _, f := range cgasStrFields[T]() {
		for i := range rows {
			q := (*cgStr)(unsafe.Pointer(uintptr(base) + uintptr(i*n) + f))
			if q.Off > arenaLen || q.Ln > arenaLen-q.Off {
				return fmt.Errorf("%s: string reference (%d,%d) escapes the string arena (%d bytes)",
					what, q.Off, q.Ln, arenaLen)
			}
		}
	}
	return nil
}

func cgasCheckBools[T any](rows []T, offs []uintptr, what string) error {
	if len(rows) == 0 || len(offs) == 0 {
		return nil
	}
	n := int(unsafe.Sizeof(rows[0]))
	base := unsafe.Pointer(&rows[0])
	for i := range rows {
		for _, o := range offs {
			if b := *(*byte)(unsafe.Pointer(uintptr(base) + uintptr(i*n) + o)); b > 1 {
				return fmt.Errorf("%s: row %d carries boolean byte %d", what, i, b)
			}
		}
	}
	return nil
}

func cgasWriteProj[S any, N any](w *bufio.Writer, rows []S, fill func(d *N, s *S)) error {
	if len(rows) == 0 {
		return nil
	}
	chunk := make([]N, min(len(rows), 512))
	for start := 0; start < len(rows); start += len(chunk) {
		n := min(len(chunk), len(rows)-start)
		for i := 0; i < n; i++ {
			cgZeroRow(unsafe.Pointer(&chunk[i]), unsafe.Sizeof(chunk[i]))
			fill(&chunk[i], &rows[start+i])
		}
		if _, err := w.Write(cgasBytes(chunk[:n])); err != nil {
			return err
		}
	}
	return nil
}

func cgasWriteFiles(w *bufio.Writer, rows []File) error {
	if len(rows) == 0 {
		return nil
	}
	chunk := make([]File, min(len(rows), 512))
	po := unsafe.Offsetof(File{}.ParseMs)
	for start := 0; start < len(rows); start += len(chunk) {
		end := min(start+len(chunk), len(rows))
		n := copy(chunk, rows[start:end])
		for i := 0; i < n; i++ {
			*(*float64)(unsafe.Pointer(uintptr(unsafe.Pointer(&chunk[i])) + po)) = 0
		}
		if _, err := w.Write(cgasBytes(chunk[:n])); err != nil {
			return err
		}
	}
	return nil
}

func cgasFillSymN(d *cgasSymN, s *Symbol) {
	d.ID = s.ID
	d.FileID = s.FileID
	d.ModuleID = s.ModuleID
	d.Name = s.name
	d.QualName = s.qualName
	d.Kind = s.kind
	d.LineStart = s.LineStart
	d.Signature = s.signature
	d.ReturnType = s.returnType
	d.HasSignature = s.HasSignature
	d.HasReturnType = s.HasReturnType
	d.NParams = cgasI16(s.NParams, "symbol NParams")
	d.IsPublic = cgasFlag(s.IsPublic, "symbol IsPublic")
	d.IsStatic = cgasFlag(s.IsStatic, "symbol IsStatic")
	d.IsAbstract = cgasFlag(s.IsAbstract, "symbol IsAbstract")
	d.IsOverride = cgasFlag(s.IsOverride, "symbol IsOverride")
	d.IsTest = cgasFlag(s.IsTest, "symbol IsTest")
	d.IsEntrypoint = cgasFlag(s.IsEntrypoint, "symbol IsEntrypoint")
	d.IsGenerated = cgasFlag(s.IsGenerated, "symbol IsGenerated")
	d.Sloc = s.Sloc
	d.NCommentLines = s.NCommentLines
	d.HasDoc = cgasFlag(s.HasDoc, "symbol HasDoc")
	d.Cyclomatic = cgasI16(s.Cyclomatic, "symbol Cyclomatic")
	d.Cognitive = cgasI16(s.Cognitive, "symbol Cognitive")
	d.MaxNesting = cgasI16(s.MaxNesting, "symbol MaxNesting")
	d.NTokens = s.NTokens
	d.NOperators = s.NOperators
	d.NOperands = s.NOperands
	d.NDistinctOperators = cgasI16(s.NDistinctOperators, "symbol NDistinctOperators")
	d.NDistinctOperands = cgasI16(s.NDistinctOperands, "symbol NDistinctOperands")
	d.NLoops = cgasI16(s.NLoops, "symbol NLoops")
	d.NBranches = cgasI16(s.NBranches, "symbol NBranches")
	d.NReturns = cgasI16(s.NReturns, "symbol NReturns")
	d.NSwitch = cgasI16(s.NSwitch, "symbol NSwitch")
	d.NCases = cgasI16(s.NCases, "symbol NCases")
	d.NLabels = cgasI16(s.NLabels, "symbol NLabels")
	d.NGotos = cgasI16(s.NGotos, "symbol NGotos")
	d.MaxLoopDepth = cgasI16(s.MaxLoopDepth, "symbol MaxLoopDepth")
	d.CallInLoop = cgasI16(s.CallInLoop, "symbol CallInLoop")
	d.AllocInLoop = cgasI16(s.AllocInLoop, "symbol AllocInLoop")
	d.IOInLoop = cgasI16(s.IOInLoop, "symbol IOInLoop")
	d.LockInLoop = cgasI16(s.LockInLoop, "symbol LockInLoop")
	d.BranchInLoop = cgasI16(s.BranchInLoop, "symbol BranchInLoop")
	d.NLocals = cgasI16(s.NLocals, "symbol NLocals")
	d.NCmp = cgasI16(s.NCmp, "symbol NCmp")
	d.NArith = cgasI16(s.NArith, "symbol NArith")
	d.NShift = cgasI16(s.NShift, "symbol NShift")
	d.NFloatLit = cgasI16(s.NFloatLit, "symbol NFloatLit")
	d.NMagic = cgasI16(s.NMagic, "symbol NMagic")
	d.NNullCheck = cgasI16(s.NNullCheck, "symbol NNullCheck")
	d.NCalls = cgasI16(s.NCalls, "symbol NCalls")
	d.NDynamicCalls = cgasI16(s.NDynamicCalls, "symbol NDynamicCalls")
	d.NUnresolvedCalls = cgasI16(s.NUnresolvedCalls, "symbol NUnresolvedCalls")
	d.FanIn = cgasI16(s.FanIn, "symbol FanIn")
	d.FanOut = cgasI16(s.FanOut, "symbol FanOut")
	d.NCallsites = cgasI16(s.NCallsites, "symbol NCallsites")
	d.IsRecursive = cgasFlag(s.IsRecursive, "symbol IsRecursive")
	d.RiskScore = cgasI16(s.RiskScore, "symbol RiskScore")
	d.NMemory = cgasI16(s.NMemory, "symbol NMemory")
	d.NAlloc = cgasI16(s.NAlloc, "symbol NAlloc")
	d.NIO = cgasI16(s.NIO, "symbol NIO")
	d.NStdio = cgasI16(s.NStdio, "symbol NStdio")
	d.NExec = cgasI16(s.NExec, "symbol NExec")
	d.NLibm = cgasI16(s.NLibm, "symbol NLibm")
	d.NInteger = cgasI16(s.NInteger, "symbol NInteger")
	d.NConcurrency = cgasI16(s.NConcurrency, "symbol NConcurrency")
	d.NReentrancy = cgasI16(s.NReentrancy, "symbol NReentrancy")
	d.IsInline = cgasFlag(s.IsInline, "symbol IsInline")
	d.IsVariadic = cgasFlag(s.IsVariadic, "symbol IsVariadic")
	d.NPtrLocals = cgasI16(s.NPtrLocals, "symbol NPtrLocals")
	d.NDeref = cgasI16(s.NDeref, "symbol NDeref")
	d.NCast = cgasI16(s.NCast, "symbol NCast")
	d.NSizeof = cgasI16(s.NSizeof, "symbol NSizeof")
	d.NIntrinsic = cgasI16(s.NIntrinsic, "symbol NIntrinsic")
	d.NAtomic = cgasI16(s.NAtomic, "symbol NAtomic")
	d.NRestrict = cgasI16(s.NRestrict, "symbol NRestrict")
	d.NLikely = cgasI16(s.NLikely, "symbol NLikely")
	d.NBuiltin = cgasI16(s.NBuiltin, "symbol NBuiltin")
	d.Rare = s.rare
}

func cgasFillRareN(d *cgasRareN, s *symRare) {
	d.SwitchInLoop = cgasI16(s.SwitchInLoop, "rare row SwitchInLoop")
	d.LibmInLoop = cgasI16(s.LibmInLoop, "rare row LibmInLoop")
	d.DivInLoop = cgasI16(s.DivInLoop, "rare row DivInLoop")
	d.StrlenInLoop = cgasI16(s.StrlenInLoop, "rare row StrlenInLoop")
	d.RetNull = cgasI16(s.RetNull, "rare row RetNull")
	d.RetNeg = cgasI16(s.RetNeg, "rare row RetNeg")
	d.RetZero = cgasI16(s.RetZero, "rare row RetZero")
	d.RetVal = cgasI16(s.RetVal, "rare row RetVal")
	d.RetVoid = cgasI16(s.RetVoid, "rare row RetVoid")
	d.NFnptrCalls = cgasI16(s.NFnptrCalls, "rare row NFnptrCalls")
	d.NMacroCalls = cgasI16(s.NMacroCalls, "rare row NMacroCalls")
	d.NExternalCalls = cgasI16(s.NExternalCalls, "rare row NExternalCalls")
	d.NFree = cgasI16(s.NFree, "rare row NFree")
	d.NConstCast = cgasI16(s.NConstCast, "rare row NConstCast")
	d.NToctou = cgasI16(s.NToctou, "rare row NToctou")
	d.NLockAcquire = cgasI16(s.NLockAcquire, "rare row NLockAcquire")
	d.NLockRelease = cgasI16(s.NLockRelease, "rare row NLockRelease")
	d.NNarrowCast = cgasI16(s.NNarrowCast, "rare row NNarrowCast")
	d.NSignCmp = cgasI16(s.NSignCmp, "rare row NSignCmp")
	d.NVariadicFmt = cgasI16(s.NVariadicFmt, "rare row NVariadicFmt")
	d.NMemcpy = cgasI16(s.NMemcpy, "rare row NMemcpy")
	d.NAllocsite = cgasI16(s.NAllocsite, "rare row NAllocsite")
	d.NGlobalWrite = cgasI16(s.NGlobalWrite, "rare row NGlobalWrite")
	d.NErrno = cgasI16(s.NErrno, "rare row NErrno")
	d.NWeakRandom = cgasI16(s.NWeakRandom, "rare row NWeakRandom")
	d.NShiftVar = cgasI16(s.NShiftVar, "rare row NShiftVar")
	d.NReallocSelf = cgasI16(s.NReallocSelf, "rare row NReallocSelf")
	d.NVla = cgasI16(s.NVla, "rare row NVla")
	d.NGetenv = cgasI16(s.NGetenv, "rare row NGetenv")
	d.NAssertSide = cgasI16(s.NAssertSide, "rare row NAssertSide")
	d.NFreeThenUse = cgasI16(s.NFreeThenUse, "rare row NFreeThenUse")
	d.NEpoll = cgasI16(s.NEpoll, "rare row NEpoll")
	d.NUring = cgasI16(s.NUring, "rare row NUring")
	d.NKqueue = cgasI16(s.NKqueue, "rare row NKqueue")
	d.NEventWait = cgasI16(s.NEventWait, "rare row NEventWait")
	d.NEtReg = cgasI16(s.NEtReg, "rare row NEtReg")
	d.NOneshotReg = cgasI16(s.NOneshotReg, "rare row NOneshotReg")
	d.NWriteReady = cgasI16(s.NWriteReady, "rare row NWriteReady")
	d.NErrFlag = cgasI16(s.NErrFlag, "rare row NErrFlag")
	d.NRearm = cgasI16(s.NRearm, "rare row NRearm")
	d.NDereg = cgasI16(s.NDereg, "rare row NDereg")
	d.NEagain = cgasI16(s.NEagain, "rare row NEagain")
	d.NEintr = cgasI16(s.NEintr, "rare row NEintr")
	d.NUringRes = cgasI16(s.NUringRes, "rare row NUringRes")
	d.NUringRing = cgasI16(s.NUringRing, "rare row NUringRing")
	d.NUringBarrier = cgasI16(s.NUringBarrier, "rare row NUringBarrier")
	d.NUringSqpoll = cgasI16(s.NUringSqpoll, "rare row NUringSqpoll")
	d.NNonblockSet = cgasI16(s.NNonblockSet, "rare row NNonblockSet")
	d.NEventCreate = cgasI16(s.NEventCreate, "rare row NEventCreate")
	d.NEventDestroy = cgasI16(s.NEventDestroy, "rare row NEventDestroy")
	d.NUringSqe = cgasI16(s.NUringSqe, "rare row NUringSqe")
	d.NUringSeen = cgasI16(s.NUringSeen, "rare row NUringSeen")
	d.NUringUdata = cgasI16(s.NUringUdata, "rare row NUringUdata")
	d.NUringLink = cgasI16(s.NUringLink, "rare row NUringLink")
	d.NUringStreamOps = cgasI16(s.NUringStreamOps, "rare row NUringStreamOps")
	d.NUringTeardown = cgasI16(s.NUringTeardown, "rare row NUringTeardown")
	d.NEvTimeoutIndefinite = cgasI16(s.NEvTimeoutIndefinite, "rare row NEvTimeoutIndefinite")
	d.NEvTimeoutZero = cgasI16(s.NEvTimeoutZero, "rare row NEvTimeoutZero")
	d.NEvBatchOne = cgasI16(s.NEvBatchOne, "rare row NEvBatchOne")
	d.NKqTimer = cgasI16(s.NKqTimer, "rare row NKqTimer")
	d.NKqTimerZeroData = cgasI16(s.NKqTimerZeroData, "rare row NKqTimerZeroData")
	d.NKqReceipt = cgasI16(s.NKqReceipt, "rare row NKqReceipt")
	d.NRetNegCheck = cgasI16(s.NRetNegCheck, "rare row NRetNegCheck")
	d.NDomainGuard = cgasI16(s.NDomainGuard, "rare row NDomainGuard")
	d.NUcharCast = cgasI16(s.NUcharCast, "rare row NUcharCast")
	d.NErrnoZero = cgasI16(s.NErrnoZero, "rare row NErrnoZero")
	d.NEndptr = cgasI16(s.NEndptr, "rare row NEndptr")
	d.NVaEnd = cgasI16(s.NVaEnd, "rare row NVaEnd")
	d.NMapFailed = cgasI16(s.NMapFailed, "rare row NMapFailed")
	d.NMonotonicClock = cgasI16(s.NMonotonicClock, "rare row NMonotonicClock")
	d.NStackszArray = cgasI16(s.NStackszArray, "rare row NStackszArray")
	d.NPtrOvfCheck = cgasI16(s.NPtrOvfCheck, "rare row NPtrOvfCheck")
	d.NCallocTransposed = cgasI16(s.NCallocTransposed, "rare row NCallocTransposed")
	d.NVaArgArr = cgasI16(s.NVaArgArr, "rare row NVaArgArr")
}

func cgasFillParamN(d *cgasParamN, s *Param) {
	d.SymbolID = s.SymbolID
	d.Pos = cgasI16(s.Pos, "param Pos")
	d.Name = s.name
	d.HasName = s.HasName
	d.Type = s.typ
	d.DefaultValue = s.def
	d.HasDefaultValue = s.HasDefaultValue
	d.IsOptional = cgasFlag(s.IsOptional, "param IsOptional")
	d.IsVariadic = cgasFlag(s.IsVariadic, "param IsVariadic")
	d.IsRef = cgasFlag(s.IsRef, "param IsRef")
	d.IsMutable = cgasFlag(s.IsMutable, "param IsMutable")
	d.IsNullable = cgasFlag(s.IsNullable, "param IsNullable")
	d.IsGeneric = cgasFlag(s.IsGeneric, "param IsGeneric")
	d.IsUntyped = cgasFlag(s.IsUntyped, "param IsUntyped")
	d.TypeDepth = cgasI16(s.TypeDepth, "param TypeDepth")
}

func cgasFillFieldN(d *cgasFieldN, s *Field) {
	d.SymbolID = s.SymbolID
	d.Ordinal = cgasI16(s.Ordinal, "field Ordinal")
	d.Name = s.name
	d.Type = s.typ
	d.Visibility = s.vis
	d.Line = s.Line
	d.IsStatic = cgasFlag(s.IsStatic, "field IsStatic")
	d.IsConst = cgasFlag(s.IsConst, "field IsConst")
	d.IsMutable = cgasFlag(s.IsMutable, "field IsMutable")
	d.IsNullable = cgasFlag(s.IsNullable, "field IsNullable")
	d.IsCollection = cgasFlag(s.IsCollection, "field IsCollection")
	d.IsUntyped = cgasFlag(s.IsUntyped, "field IsUntyped")
	d.HasDefault = cgasFlag(s.HasDefault, "field HasDefault")
	d.TypeDepth = cgasI16(s.TypeDepth, "field TypeDepth")
}

func cgasFillLocalN(d *cgasLocalN, s *Local) {
	d.SymbolID = s.SymbolID
	d.Ordinal = cgasI16(s.Ordinal, "local Ordinal")
	d.Name = s.name
	d.Type = s.typ
	d.Line = s.Line
	d.IsConst = cgasFlag(s.IsConst, "local IsConst")
	d.IsMutable = cgasFlag(s.IsMutable, "local IsMutable")
	d.IsUntyped = cgasFlag(s.IsUntyped, "local IsUntyped")
	d.HasInit = cgasFlag(s.HasInit, "local HasInit")
	d.InLoop = cgasFlag(s.InLoop, "local InLoop")
	d.ScopeDepth = cgasU8(s.ScopeDepth, "local ScopeDepth")
}

func saveASTFile(g *Graph, path string) (int64, error) {
	cgasGuard()
	mods := g.Modules
	metaKeys := make([]string, 0, len(g.Meta))
	for k := range g.Meta {
		metaKeys = append(metaKeys, k)
	}
	sort.Strings(metaKeys)
	metaRows := make([]cgMetaRow, len(metaKeys))
	for i, k := range metaKeys {
		metaRows[i].K = cgPut(k)
		metaRows[i].V = cgPut(g.Meta[k])
	}
	var ctr cgasCounters
	ctr.FilesParsed = g.FilesParsed
	ctr.FilesFailed = g.FilesFailed
	ctr.EdgesN = g.EdgesN
	ctr.MacroN = g.MacroN
	ctr.ExternN = g.ExternN
	ctr.DeclN = g.DeclN
	ctr.UnresN = g.UnresN
	ctr.CallsTotal = g.CallsTotal
	ctr.AddrPruned = g.AddrPruned
	ctr.MakefilesRead = g.MakefilesRead
	ctr.FilesSkippedBig = g.FilesSkippedBig
	ctr.FilesSkippedSpecial = g.FilesSkippedSpecial
	ctr.FilesSkippedEscape = g.FilesSkippedEscape
	ctr.FilesSkippedDenied = g.FilesSkippedDenied
	ctr.WalkErrors = g.WalkErrors
	body := make([][]byte, cgasNSec)
	body[cgasSecMods-1] = cgasBytes(mods)
	body[cgasSecLits-1] = cgasBytes(g.Literals)
	body[cgasSecMark-1] = cgasBytes(g.Markers)
	body[cgasSecAttrs-1] = cgasBytes(g.Attrs)
	body[cgasSecImps-1] = cgasBytes(g.Imports)
	body[cgasSecHaz-1] = cgasBytes(g.Hazards)
	body[cgasSecEnums-1] = cgasBytes(g.EnumMem)
	body[cgasSecLayout-1] = cgasBytes(g.Layout)
	body[cgasSecSSize-1] = cgasBytes(g.SSize)
	body[cgasSecDecls-1] = cgasBytes(g.Decls)
	body[cgasSecAddr-1] = cgasBytes(g.Addr)
	body[cgasSecSecrets-1] = cgasBytes(g.Secrets)
	body[cgasSecAllocs-1] = cgasBytes(g.Allocs)
	body[cgasSecMemops-1] = cgasBytes(g.Memops)
	body[cgasSecMacros-1] = cgasBytes(g.Macros)
	body[cgasSecGlobals-1] = cgasBytes(g.Globals)
	body[cgasSecCfgs-1] = cgasBytes(g.Cfgs)
	body[cgasSecReach-1] = cgasBytes(g.Reach)
	body[cgasSecMkRules-1] = cgasBytes(g.MkRules)
	body[cgasSecLocks-1] = cgasBytes(g.Locks)
	body[cgasSecEvOps-1] = cgasBytes(g.EvOps)
	body[cgasSecAPIUses-1] = cgasBytes(g.APIUses)
	body[cgasSecCycles-1] = cgasBytes(g.Cycles)
	body[cgasSecEdges-1] = cgasBytes(g.Edges)
	body[cgasSecSites-1] = cgasBytes(g.Callsites)
	body[cgasSecUnres-1] = cgasBytes(g.Unres)
	body[cgasSecMeta-1] = cgasBytes(metaRows)
	body[cgasSecCounters-1] = cgasBytes([]cgasCounters{ctr})
	body[cgasSecTrees-1] = cgTreesBlob(g)
	body[cgasSecStrings-1] = cgArena

	secLn := map[uint32]uint64{
		cgasSecFiles:  uint64(len(g.Files)) * uint64(unsafe.Sizeof(File{})),
		cgasSecSyms:   uint64(len(g.symStore)) * uint64(unsafe.Sizeof(cgasSymN{})),
		cgasSecRare:   uint64(len(g.rare)) * uint64(unsafe.Sizeof(cgasRareN{})),
		cgasSecParams: uint64(len(g.Params)) * uint64(unsafe.Sizeof(cgasParamN{})),
		cgasSecFields: uint64(len(g.Fields)) * uint64(unsafe.Sizeof(cgasFieldN{})),
		cgasSecLocals: uint64(len(g.Locals)) * uint64(unsafe.Sizeof(cgasLocalN{})),
	}
	dir := make([]cgasSec, cgasNSec)
	cur := uint64(cgasHeaderSz) + cgasNSec*cgasSecSz
	for i := range dir {
		cur = (cur + 7) &^ 7
		ln, ok := secLn[uint32(i+1)]
		if !ok {
			ln = uint64(len(body[i]))
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
	cgPutU32(hdr, 4, cgasVersion)
	cgPutU32(hdr, 8, cgasNSec)
	cgPutU64(hdr, 16, total)
	cgPutU64(hdr, 24, uint64(len(cgArena)))
	if _, err := w.Write(hdr); err != nil {
		return failW(err)
	}
	dirBuf := make([]byte, cgasNSec*cgasSecSz)
	for i := range dir {
		o := i * int(cgasSecSz)
		cgPutU32(dirBuf, o, dir[i].ID)
		cgPutU64(dirBuf, o+8, dir[i].Off)
		cgPutU64(dirBuf, o+16, dir[i].Len)
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
		var werr error
		switch uint32(i + 1) {
		case cgasSecFiles:
			werr = cgasWriteFiles(w, g.Files)
		case cgasSecSyms:
			werr = cgasWriteProj(w, g.symStore, cgasFillSymN)
		case cgasSecRare:
			werr = cgasWriteProj(w, g.rare, cgasFillRareN)
		case cgasSecParams:
			werr = cgasWriteProj(w, g.Params, cgasFillParamN)
		case cgasSecFields:
			werr = cgasWriteProj(w, g.Fields, cgasFillFieldN)
		case cgasSecLocals:
			werr = cgasWriteProj(w, g.Locals, cgasFillLocalN)
		default:
			if len(body[i]) > 0 {
				_, werr = w.Write(body[i])
			}
		}
		if werr != nil {
			return failW(werr)
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
		return nil, bad("unsupported state format version %d -- CGAS v1, v2 and v3 are retired, re-save with this build to produce v%d", v, cgasVersion)
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
	cgMu.Lock()
	cgArena = mem[ao : ao+al : ao+al]
	cgMu.Unlock()
	dec := func(id uint32) (uint64, uint64) {
		return secs[id].Off, secs[id].Len
	}
	decErr := func(err error) (*Graph, error) {
		return nil, bad("%v", err)
	}

	off, ln := dec(cgasSecFiles)
	files, err := cgasCastRows[File](mem, off, ln, "files")
	if err != nil {
		return decErr(err)
	}
	if err := cgasCheckStrRefs(files, al, "files"); err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecMods)
	mods, err := cgasCastRows[Module](mem, off, ln, "modules")
	if err != nil {
		return decErr(err)
	}
	if err := cgasCheckStrRefs(mods, al, "modules"); err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecSyms)
	symNRows, err := cgasCastRows[cgasSymN](mem, off, ln, "symbols")
	if err != nil {
		return decErr(err)
	}
	if err := cgasCheckStrRefs(symNRows, al, "symbols"); err != nil {
		return decErr(err)
	}
	if err := cgasCheckBools(symNRows, symNBoolOffs, "symbols"); err != nil {
		return decErr(err)
	}
	symRows := make([]Symbol, len(symNRows))
	for i := range symNRows {
		r := &symNRows[i]
		d := &symRows[i]
		d.ID = r.ID
		d.FileID = r.FileID
		d.ModuleID = r.ModuleID
		d.name = r.Name
		d.qualName = r.QualName
		d.kind = r.Kind
		d.LineStart = r.LineStart
		d.signature = r.Signature
		d.returnType = r.ReturnType
		d.HasSignature = r.HasSignature
		d.HasReturnType = r.HasReturnType
		d.NParams = int32(r.NParams)
		d.IsPublic = int32(r.IsPublic)
		d.IsStatic = int32(r.IsStatic)
		d.IsAbstract = int32(r.IsAbstract)
		d.IsOverride = int32(r.IsOverride)
		d.IsTest = int32(r.IsTest)
		d.IsEntrypoint = int32(r.IsEntrypoint)
		d.IsGenerated = int32(r.IsGenerated)
		d.Sloc = r.Sloc
		d.NCommentLines = r.NCommentLines
		d.HasDoc = int32(r.HasDoc)
		d.Cyclomatic = int32(r.Cyclomatic)
		d.Cognitive = int32(r.Cognitive)
		d.MaxNesting = int32(r.MaxNesting)
		d.NTokens = r.NTokens
		d.NOperators = r.NOperators
		d.NOperands = r.NOperands
		d.NDistinctOperators = int32(r.NDistinctOperators)
		d.NDistinctOperands = int32(r.NDistinctOperands)
		d.NLoops = int32(r.NLoops)
		d.NBranches = int32(r.NBranches)
		d.NReturns = int32(r.NReturns)
		d.NSwitch = int32(r.NSwitch)
		d.NCases = int32(r.NCases)
		d.NLabels = int32(r.NLabels)
		d.NGotos = int32(r.NGotos)
		d.MaxLoopDepth = int32(r.MaxLoopDepth)
		d.CallInLoop = int32(r.CallInLoop)
		d.AllocInLoop = int32(r.AllocInLoop)
		d.IOInLoop = int32(r.IOInLoop)
		d.LockInLoop = int32(r.LockInLoop)
		d.BranchInLoop = int32(r.BranchInLoop)
		d.NLocals = int32(r.NLocals)
		d.NCmp = int32(r.NCmp)
		d.NArith = int32(r.NArith)
		d.NShift = int32(r.NShift)
		d.NFloatLit = int32(r.NFloatLit)
		d.NMagic = int32(r.NMagic)
		d.NNullCheck = int32(r.NNullCheck)
		d.NCalls = int32(r.NCalls)
		d.NDynamicCalls = int32(r.NDynamicCalls)
		d.NUnresolvedCalls = int32(r.NUnresolvedCalls)
		d.FanIn = int32(r.FanIn)
		d.FanOut = int32(r.FanOut)
		d.NCallsites = int32(r.NCallsites)
		d.IsRecursive = int32(r.IsRecursive)
		d.RiskScore = int32(r.RiskScore)
		d.NMemory = int32(r.NMemory)
		d.NAlloc = int32(r.NAlloc)
		d.NIO = int32(r.NIO)
		d.NStdio = int32(r.NStdio)
		d.NExec = int32(r.NExec)
		d.NLibm = int32(r.NLibm)
		d.NInteger = int32(r.NInteger)
		d.NConcurrency = int32(r.NConcurrency)
		d.NReentrancy = int32(r.NReentrancy)
		d.IsInline = int32(r.IsInline)
		d.IsVariadic = int32(r.IsVariadic)
		d.NPtrLocals = int32(r.NPtrLocals)
		d.NDeref = int32(r.NDeref)
		d.NCast = int32(r.NCast)
		d.NSizeof = int32(r.NSizeof)
		d.NIntrinsic = int32(r.NIntrinsic)
		d.NAtomic = int32(r.NAtomic)
		d.NRestrict = int32(r.NRestrict)
		d.NLikely = int32(r.NLikely)
		d.NBuiltin = int32(r.NBuiltin)
		d.rare = r.Rare
	}
	off, ln = dec(cgasSecRare)
	rareNRows, err := cgasCastRows[cgasRareN](mem, off, ln, "rare columns")
	if err != nil {
		return decErr(err)
	}
	rare := make([]symRare, len(rareNRows))
	for i := range rareNRows {
		r := &rareNRows[i]
		d := &rare[i]
		d.SwitchInLoop = int32(r.SwitchInLoop)
		d.LibmInLoop = int32(r.LibmInLoop)
		d.DivInLoop = int32(r.DivInLoop)
		d.StrlenInLoop = int32(r.StrlenInLoop)
		d.RetNull = int32(r.RetNull)
		d.RetNeg = int32(r.RetNeg)
		d.RetZero = int32(r.RetZero)
		d.RetVal = int32(r.RetVal)
		d.RetVoid = int32(r.RetVoid)
		d.NFnptrCalls = int32(r.NFnptrCalls)
		d.NMacroCalls = int32(r.NMacroCalls)
		d.NExternalCalls = int32(r.NExternalCalls)
		d.NFree = int32(r.NFree)
		d.NConstCast = int32(r.NConstCast)
		d.NToctou = int32(r.NToctou)
		d.NLockAcquire = int32(r.NLockAcquire)
		d.NLockRelease = int32(r.NLockRelease)
		d.NNarrowCast = int32(r.NNarrowCast)
		d.NSignCmp = int32(r.NSignCmp)
		d.NVariadicFmt = int32(r.NVariadicFmt)
		d.NMemcpy = int32(r.NMemcpy)
		d.NAllocsite = int32(r.NAllocsite)
		d.NGlobalWrite = int32(r.NGlobalWrite)
		d.NErrno = int32(r.NErrno)
		d.NWeakRandom = int32(r.NWeakRandom)
		d.NShiftVar = int32(r.NShiftVar)
		d.NReallocSelf = int32(r.NReallocSelf)
		d.NVla = int32(r.NVla)
		d.NGetenv = int32(r.NGetenv)
		d.NAssertSide = int32(r.NAssertSide)
		d.NFreeThenUse = int32(r.NFreeThenUse)
		d.NEpoll = int32(r.NEpoll)
		d.NUring = int32(r.NUring)
		d.NKqueue = int32(r.NKqueue)
		d.NEventWait = int32(r.NEventWait)
		d.NEtReg = int32(r.NEtReg)
		d.NOneshotReg = int32(r.NOneshotReg)
		d.NWriteReady = int32(r.NWriteReady)
		d.NErrFlag = int32(r.NErrFlag)
		d.NRearm = int32(r.NRearm)
		d.NDereg = int32(r.NDereg)
		d.NEagain = int32(r.NEagain)
		d.NEintr = int32(r.NEintr)
		d.NUringRes = int32(r.NUringRes)
		d.NUringRing = int32(r.NUringRing)
		d.NUringBarrier = int32(r.NUringBarrier)
		d.NUringSqpoll = int32(r.NUringSqpoll)
		d.NNonblockSet = int32(r.NNonblockSet)
		d.NEventCreate = int32(r.NEventCreate)
		d.NEventDestroy = int32(r.NEventDestroy)
		d.NUringSqe = int32(r.NUringSqe)
		d.NUringSeen = int32(r.NUringSeen)
		d.NUringUdata = int32(r.NUringUdata)
		d.NUringLink = int32(r.NUringLink)
		d.NUringStreamOps = int32(r.NUringStreamOps)
		d.NUringTeardown = int32(r.NUringTeardown)
		d.NEvTimeoutIndefinite = int32(r.NEvTimeoutIndefinite)
		d.NEvTimeoutZero = int32(r.NEvTimeoutZero)
		d.NEvBatchOne = int32(r.NEvBatchOne)
		d.NKqTimer = int32(r.NKqTimer)
		d.NKqTimerZeroData = int32(r.NKqTimerZeroData)
		d.NKqReceipt = int32(r.NKqReceipt)
		d.NRetNegCheck = int32(r.NRetNegCheck)
		d.NDomainGuard = int32(r.NDomainGuard)
		d.NUcharCast = int32(r.NUcharCast)
		d.NErrnoZero = int32(r.NErrnoZero)
		d.NEndptr = int32(r.NEndptr)
		d.NVaEnd = int32(r.NVaEnd)
		d.NMapFailed = int32(r.NMapFailed)
		d.NMonotonicClock = int32(r.NMonotonicClock)
		d.NStackszArray = int32(r.NStackszArray)
		d.NPtrOvfCheck = int32(r.NPtrOvfCheck)
		d.NCallocTransposed = int32(r.NCallocTransposed)
		d.NVaArgArr = int32(r.NVaArgArr)
	}
	for i := range symRows {
		if r := symRows[i].rare; r >= int32(len(rare)) {
			return nil, bad("symbol %d names rare column %d of %d", symRows[i].ID, r, len(rare))
		}
	}
	off, ln = dec(cgasSecParams)
	paramNRows, err := cgasCastRows[cgasParamN](mem, off, ln, "params")
	if err != nil {
		return decErr(err)
	}
	if err := cgasCheckStrRefs(paramNRows, al, "params"); err != nil {
		return decErr(err)
	}
	if err := cgasCheckBools(paramNRows, paramNBoolOffs, "params"); err != nil {
		return decErr(err)
	}
	params := make([]Param, len(paramNRows))
	for i := range paramNRows {
		r := &paramNRows[i]
		d := &params[i]
		d.SymbolID = r.SymbolID
		d.Pos = int32(r.Pos)
		d.name = r.Name
		d.HasName = r.HasName
		d.typ = r.Type
		d.def = r.DefaultValue
		d.HasDefaultValue = r.HasDefaultValue
		d.IsOptional = int32(r.IsOptional)
		d.IsVariadic = int32(r.IsVariadic)
		d.IsRef = int32(r.IsRef)
		d.IsMutable = int32(r.IsMutable)
		d.IsNullable = int32(r.IsNullable)
		d.IsGeneric = int32(r.IsGeneric)
		d.IsUntyped = int32(r.IsUntyped)
		d.TypeDepth = int32(r.TypeDepth)
	}
	off, ln = dec(cgasSecFields)
	fieldNRows, err := cgasCastRows[cgasFieldN](mem, off, ln, "fields")
	if err != nil {
		return decErr(err)
	}
	if err := cgasCheckStrRefs(fieldNRows, al, "fields"); err != nil {
		return decErr(err)
	}
	fields := make([]Field, len(fieldNRows))
	for i := range fieldNRows {
		r := &fieldNRows[i]
		d := &fields[i]
		d.SymbolID = r.SymbolID
		d.Ordinal = int32(r.Ordinal)
		d.name = r.Name
		d.typ = r.Type
		d.vis = r.Visibility
		d.Line = r.Line
		d.IsStatic = int32(r.IsStatic)
		d.IsConst = int32(r.IsConst)
		d.IsMutable = int32(r.IsMutable)
		d.IsNullable = int32(r.IsNullable)
		d.IsCollection = int32(r.IsCollection)
		d.IsUntyped = int32(r.IsUntyped)
		d.HasDefault = int32(r.HasDefault)
		d.TypeDepth = int32(r.TypeDepth)
	}
	off, ln = dec(cgasSecLocals)
	localNRows, err := cgasCastRows[cgasLocalN](mem, off, ln, "locals")
	if err != nil {
		return decErr(err)
	}
	if err := cgasCheckStrRefs(localNRows, al, "locals"); err != nil {
		return decErr(err)
	}
	locals := make([]Local, len(localNRows))
	for i := range localNRows {
		r := &localNRows[i]
		d := &locals[i]
		d.SymbolID = r.SymbolID
		d.Ordinal = int32(r.Ordinal)
		d.name = r.Name
		d.typ = r.Type
		d.Line = r.Line
		d.IsConst = int32(r.IsConst)
		d.IsMutable = int32(r.IsMutable)
		d.IsUntyped = int32(r.IsUntyped)
		d.HasInit = int32(r.HasInit)
		d.InLoop = int32(r.InLoop)
		d.ScopeDepth = int32(r.ScopeDepth)
	}
	off, ln = dec(cgasSecLits)
	lits, err := cgasCastRows[Literal](mem, off, ln, "literals")
	if err != nil {
		return decErr(err)
	}
	if err := cgasCheckStrRefs(lits, al, "literals"); err != nil {
		return decErr(err)
	}
	if err := cgasCheckBools(lits, literalBoolOffs, "literals"); err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecMark)
	mark, err := cgasCastRows[Marker](mem, off, ln, "markers")
	if err != nil {
		return decErr(err)
	}
	if err := cgasCheckStrRefs(mark, al, "markers"); err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecAttrs)
	attrs, err := cgasCastRows[Attribute](mem, off, ln, "attributes")
	if err != nil {
		return decErr(err)
	}
	if err := cgasCheckStrRefs(attrs, al, "attributes"); err != nil {
		return decErr(err)
	}
	if err := cgasCheckBools(attrs, attrBoolOffs, "attributes"); err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecImps)
	imps, err := cgasCastRows[Import](mem, off, ln, "imports")
	if err != nil {
		return decErr(err)
	}
	if err := cgasCheckStrRefs(imps, al, "imports"); err != nil {
		return decErr(err)
	}
	if err := cgasCheckBools(imps, importBoolOffs, "imports"); err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecHaz)
	haz, err := cgasCastRows[Hazard](mem, off, ln, "hazards")
	if err != nil {
		return decErr(err)
	}
	if err := cgasCheckStrRefs(haz, al, "hazards"); err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecEnums)
	enums, err := cgasCastRows[EnumMember](mem, off, ln, "enum members")
	if err != nil {
		return decErr(err)
	}
	if err := cgasCheckStrRefs(enums, al, "enum members"); err != nil {
		return decErr(err)
	}
	if err := cgasCheckBools(enums, enumBoolOffs, "enum members"); err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecLayout)
	layout, err := cgasCastRows[LayoutRow](mem, off, ln, "layout rows")
	if err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecSSize)
	ssize, err := cgasCastRows[StructSize](mem, off, ln, "struct sizes")
	if err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecDecls)
	decls, err := cgasCastRows[Declaration](mem, off, ln, "declarations")
	if err != nil {
		return decErr(err)
	}
	if err := cgasCheckStrRefs(decls, al, "declarations"); err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecAddr)
	addr, err := cgasCastRows[AddrTaken](mem, off, ln, "addr-taken rows")
	if err != nil {
		return decErr(err)
	}
	if err := cgasCheckStrRefs(addr, al, "addr-taken rows"); err != nil {
		return decErr(err)
	}
	if err := cgasCheckBools(addr, addrBoolOffs, "addr-taken rows"); err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecSecrets)
	secrets, err := cgasCastRows[SecretCandidate](mem, off, ln, "secret candidates")
	if err != nil {
		return decErr(err)
	}
	if err := cgasCheckStrRefs(secrets, al, "secret candidates"); err != nil {
		return decErr(err)
	}
	if err := cgasCheckBools(secrets, secretBoolOffs, "secret candidates"); err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecAllocs)
	allocs, err := cgasCastRows[AllocSite](mem, off, ln, "allocation sites")
	if err != nil {
		return decErr(err)
	}
	if err := cgasCheckStrRefs(allocs, al, "allocation sites"); err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecMemops)
	memops, err := cgasCastRows[Memop](mem, off, ln, "memops")
	if err != nil {
		return decErr(err)
	}
	if err := cgasCheckStrRefs(memops, al, "memops"); err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecMacros)
	macros, err := cgasCastRows[Macro](mem, off, ln, "macros")
	if err != nil {
		return decErr(err)
	}
	if err := cgasCheckStrRefs(macros, al, "macros"); err != nil {
		return decErr(err)
	}
	if err := cgasCheckBools(macros, macroBoolOffs, "macros"); err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecGlobals)
	globals, err := cgasCastRows[Global](mem, off, ln, "globals")
	if err != nil {
		return decErr(err)
	}
	if err := cgasCheckStrRefs(globals, al, "globals"); err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecCfgs)
	cfgs, err := cgasCastRows[ConfigBlock](mem, off, ln, "config blocks")
	if err != nil {
		return decErr(err)
	}
	if err := cgasCheckStrRefs(cfgs, al, "config blocks"); err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecReach)
	reach, err := cgasCastRows[Reach](mem, off, ln, "reach rows")
	if err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecMkRules)
	mkRules, err := cgasCastRows[MakefileRule](mem, off, ln, "makefile rules")
	if err != nil {
		return decErr(err)
	}
	if err := cgasCheckStrRefs(mkRules, al, "makefile rules"); err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecLocks)
	locks, err := cgasCastRows[LockRow](mem, off, ln, "lock rows")
	if err != nil {
		return decErr(err)
	}
	if err := cgasCheckStrRefs(locks, al, "lock rows"); err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecEvOps)
	evOps, err := cgasCastRows[EventOp](mem, off, ln, "event ops")
	if err != nil {
		return decErr(err)
	}
	if err := cgasCheckStrRefs(evOps, al, "event ops"); err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecAPIUses)
	apiUses, err := cgasCastRows[APIUse](mem, off, ln, "api uses")
	if err != nil {
		return decErr(err)
	}
	if err := cgasCheckStrRefs(apiUses, al, "api uses"); err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecCycles)
	cycles, err := cgasCastRows[IncludeCycle](mem, off, ln, "include cycles")
	if err != nil {
		return decErr(err)
	}
	if err := cgasCheckStrRefs(cycles, al, "include cycles"); err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecEdges)
	edges, err := cgasCastRows[Edge](mem, off, ln, "call-graph edges")
	if err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecSites)
	sites, err := cgasCastRows[Callsite](mem, off, ln, "call sites")
	if err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecUnres)
	unres, err := cgasCastRows[Unresolved](mem, off, ln, "unresolved calls")
	if err != nil {
		return decErr(err)
	}
	if err := cgasCheckStrRefs(unres, al, "unresolved calls"); err != nil {
		return decErr(err)
	}
	off, ln = dec(cgasSecMeta)
	meta, err := cgasCastRows[cgMetaRow](mem, off, ln, "meta")
	if err != nil {
		return decErr(err)
	}
	if err := cgasCheckStrRefs(meta, al, "meta"); err != nil {
		return decErr(err)
	}
	cgMu.Lock()
	if cgIntern == nil {
		cgIntern = make(map[string]cgStr, len(meta)*2)
	}
	for i := range meta {
		cgIntern[meta[i].Key()] = meta[i].K
		cgIntern[meta[i].Val()] = meta[i].V
	}
	cgMu.Unlock()
	off, ln = dec(cgasSecCounters)
	ctrs, err := cgasCastRows[cgasCounters](mem, off, ln, "counters")
	if err != nil {
		return decErr(err)
	}
	if len(ctrs) != 1 {
		return nil, bad("counters section holds %d rows, want 1", len(ctrs))
	}

	g := &Graph{astBlob: mem}
	{
		to, tl := secs[cgasSecTrees].Off, secs[cgasSecTrees].Len
		if err := cgTreesParse(mem[to:to+tl:to+tl], g); err != nil {
			syscall.Munmap(mem)
			return nil, err
		}
	}
	g.Files = files
	g.Modules = mods
	g.symStore = symRows
	g.Symbols = make([]*Symbol, len(symRows))
	for i := range symRows {
		g.Symbols[i] = &g.symStore[i]
	}
	g.rare = rare
	g.Params = params
	g.Fields = fields
	g.Locals = locals
	g.Literals = lits
	g.Markers = mark
	g.Attrs = attrs
	g.Imports = imps
	g.Hazards = haz
	g.EnumMem = enums
	g.Layout = layout
	g.SSize = ssize
	g.Decls = decls
	g.Addr = addr
	g.Secrets = secrets
	g.Allocs = allocs
	g.Memops = memops
	g.Macros = macros
	g.Globals = globals
	g.Cfgs = cfgs
	g.Reach = reach
	g.MkRules = mkRules
	g.Locks = locks
	g.EvOps = evOps
	g.APIUses = apiUses
	g.Cycles = cycles
	g.Edges = edges
	g.Callsites = sites
	g.Unres = unres
	g.Meta = make(map[string]string, len(meta))
	for i := range meta {
		g.Meta[meta[i].Key()] = meta[i].Val()
	}
	g.FilesParsed = ctrs[0].FilesParsed
	g.FilesFailed = ctrs[0].FilesFailed
	g.EdgesN = ctrs[0].EdgesN
	g.MacroN = ctrs[0].MacroN
	g.ExternN = ctrs[0].ExternN
	g.DeclN = ctrs[0].DeclN
	g.UnresN = ctrs[0].UnresN
	g.CallsTotal = ctrs[0].CallsTotal
	g.AddrPruned = ctrs[0].AddrPruned
	g.MakefilesRead = ctrs[0].MakefilesRead
	g.FilesSkippedBig = ctrs[0].FilesSkippedBig
	g.FilesSkippedSpecial = ctrs[0].FilesSkippedSpecial
	g.FilesSkippedEscape = ctrs[0].FilesSkippedEscape
	g.FilesSkippedDenied = ctrs[0].FilesSkippedDenied
	g.WalkErrors = ctrs[0].WalkErrors
	g.fileByRel = make(map[string]int32, len(g.Files))
	for i := range g.Files {
		g.fileByRel[g.Files[i].Path()] = g.Files[i].ID
	}
	buildIndex(g)
	return g, nil
}

type FileRow struct {
	ID           int32   `json:"ID"`
	Path         string  `json:"Path"`
	Dir          string  `json:"Dir"`
	Basename     string  `json:"Basename"`
	Ext          string  `json:"Ext"`
	Lang         string  `json:"Lang"`
	ModuleID     int32   `json:"ModuleID"`
	Bytes        int32   `json:"Bytes"`
	Lines        int32   `json:"Lines"`
	Sloc         int32   `json:"Sloc"`
	BlankLines   int32   `json:"BlankLines"`
	CommentLines int32   `json:"CommentLines"`
	DocLines     int32   `json:"DocLines"`
	MaxLineLen   int32   `json:"MaxLineLen"`
	Sha1         string  `json:"Sha1"`
	Parsed       int32   `json:"Parsed"`
	IsTest       int32   `json:"IsTest"`
	IsGenerated  int32   `json:"IsGenerated"`
	IsVendored   int32   `json:"IsVendored"`
	NParseErrors int32   `json:"NParseErrors"`
	NMissing     int32   `json:"NMissingNodes"`
	ParseMs      float64 `json:"ParseMs"`

	NSymbols   int32 `json:"NSymbols"`
	NFunctions int32 `json:"NFunctions"`
	NTypes     int32 `json:"NTypes"`
	NImports   int32 `json:"NImports"`
	TotalCyclo int32 `json:"TotalCyclo"`
	MaxCyclo   int32 `json:"MaxCyclo"`
	TotalRisk  int32 `json:"TotalRisk"`
}

type ModuleRow struct {
	ID          int32   `json:"ID"`
	Name        string  `json:"Name"`
	Kind        string  `json:"Kind"`
	NFiles      int32   `json:"NFiles"`
	NSymbols    int32   `json:"NSymbols"`
	NPublic     int32   `json:"NPublic"`
	Sloc        int32   `json:"Sloc"`
	FanIn       int32   `json:"FanIn"`
	FanOut      int32   `json:"FanOut"`
	Instability float64 `json:"Instability"`
}

type SymbolRare struct {
	SwitchInLoop, LibmInLoop, DivInLoop         int32
	StrlenInLoop                                int32
	RetNull, RetNeg, RetZero, RetVal, RetVoid   int32
	NFnptrCalls, NMacroCalls                    int32
	NExternalCalls                              int32
	NFree, NConstCast, NToctou                  int32
	NLockAcquire, NLockRelease                  int32
	NNarrowCast, NSignCmp, NVariadicFmt         int32
	NMemcpy, NAllocsite                         int32
	NGlobalWrite                                int32
	NErrno, NWeakRandom, NShiftVar              int32
	NReallocSelf, NVla, NGetenv                 int32
	NAssertSide                                 int32
	NFreeThenUse                                int32
	NEpoll, NUring, NKqueue, NEventWait         int32
	NEtReg, NOneshotReg, NWriteReady            int32
	NErrFlag, NRearm, NDereg, NEagain, NEintr   int32
	NUringRes, NUringRing, NUringBarrier        int32
	NUringSqpoll                                int32
	NNonblockSet, NEventCreate, NEventDestroy   int32
	NUringSqe, NUringSeen, NUringUdata          int32
	NUringLink, NUringStreamOps, NUringTeardown int32
	NEvTimeoutIndefinite, NEvTimeoutZero        int32
	NEvBatchOne, NKqTimer, NKqTimerZeroData     int32
	NKqReceipt                                  int32
	NRetNegCheck, NDomainGuard, NUcharCast      int32
	NErrnoZero, NEndptr, NVaEnd, NMapFailed     int32
	NMonotonicClock, NStackszArray              int32
	NPtrOvfCheck, NCallocTransposed, NVaArgArr  int32
}

type SymbolRow struct {
	ID            int32
	FileID        int32
	ModuleID      int32
	Name          string
	QualName      string
	Kind          string
	LineStart     int32
	Signature     string
	ReturnType    string
	HasSignature  bool
	HasReturnType bool

	NParams int32

	IsPublic, IsStatic     int32
	IsAbstract, IsOverride int32
	IsTest, IsEntrypoint   int32
	IsGenerated            int32

	Sloc, NCommentLines, HasDoc int32

	Cyclomatic, Cognitive, MaxNesting     int32
	NTokens, NOperators, NOperands        int32
	NDistinctOperators, NDistinctOperands int32

	NLoops, NBranches, NReturns int32
	NSwitch, NCases             int32
	NLabels, NGotos             int32

	MaxLoopDepth, CallInLoop, AllocInLoop, IOInLoop int32
	LockInLoop, BranchInLoop                        int32

	NLocals, NCmp, NArith int32
	NShift                int32
	NFloatLit, NMagic     int32
	NNullCheck            int32

	NCalls, NDynamicCalls, NUnresolvedCalls int32
	FanIn, FanOut, NCallsites               int32
	IsRecursive                             int32

	RiskScore    int32
	NMemory      int32
	NAlloc       int32
	NIO          int32
	NStdio       int32
	NExec        int32
	NLibm        int32
	NInteger     int32
	NConcurrency int32
	NReentrancy  int32

	IsInline, IsVariadic               int32
	NPtrLocals, NDeref, NCast, NSizeof int32
	NIntrinsic, NAtomic, NRestrict     int32
	NLikely, NBuiltin                  int32

	LineEnd         int32
	NLines          int32
	Visibility      string
	NPtrParams      int32
	NAddrof         int32
	NArrow          int32
	NMemberAcc      int32
	NSubscript      int32
	NBitop          int32
	NStringLit      int32
	NBodyBytes      int32
	NTernary        int32
	NLogical        int32
	NVolatile       int32
	NStaticAssert   int32
	NAssign         int32
	NCompoundAssign int32
	NIncdec         int32

	SymbolRare
}

type ParamRow struct {
	SymbolID, Pos   int32
	Name            string
	HasName         bool
	Type            string
	DefaultValue    string
	HasDefaultValue bool
	IsOptional      int32
	IsVariadic      int32
	IsRef           int32
	IsMutable       int32
	IsNullable      int32
	IsGeneric       int32
	IsUntyped       int32
	TypeDepth       int32
}

type FieldRow struct {
	SymbolID, Ordinal     int32
	Name, Type            string
	Visibility            string
	Line                  int32
	IsStatic, IsConst     int32
	IsMutable, IsNullable int32
	IsCollection          int32
	IsUntyped             int32
	HasDefault            int32
	TypeDepth             int32
}

type LocalRow struct {
	SymbolID, Ordinal  int32
	Name, Type         string
	Line               int32
	IsConst, IsMutable int32
	IsUntyped          int32
	HasInit, InLoop    int32
	ScopeDepth         int32
}

type EdgeRow struct {
	CallerID, CalleeID           int32
	NCalls, SameFile, SameModule int32
	IsSelf                       int32
}

type CallsiteRow struct{ CallerID, CalleeID, Line int32 }

type UnresolvedRow struct {
	CallerID  int32
	Name      string
	N         int32
	FirstLine int32
}

type ImportRow struct {
	ID                     int32
	FileID                 int32
	Target                 string
	TargetID               int32
	HasTargetID            bool
	Alias                  string
	HasAlias               bool
	Kind                   string
	Line                   int32
	IsExternal, IsRelative int32
	IsWildcard, IsTypeOnly int32
	IsDynamic, NNames      int32
}

type HazardRow struct {
	SymbolID  int32
	Pattern   string
	Category  string
	N         int32
	FirstLine int32
}

type AttributeRow struct {
	ID          int32
	SymbolID    int32
	HasSymbolID bool
	FileID      int32
	Name        string
	Args        string
	HasArgs     bool
	Line        int32
}

type LiteralRow struct {
	ID       int32
	SymbolID int32
	HasSym   bool
	FileID   int32
	Kind     string
	Value    string
	Line     int32
	IsMagic  int32
}

type EnumMemberRow struct {
	SymbolID, Ordinal int32
	Name              string
	Value             string
	HasValue          bool
	NFields           int32
}

type MarkerRow struct {
	ID       int32
	FileID   int32
	SymbolID int32
	HasSym   bool
	Kind     string
	Line     int32
	Text     string
}

type LayoutRowR struct {
	SymbolID, Ordinal  int32
	ByteOff, ByteSize  int32
	PadBefore, Exact   int32
	PtrDepth, ArrayLen int32
	IsFnptr, Depth     int32
	InUnion            int32
}

type StructSizeRow struct {
	SymbolID, TotalSize, TailPad, TotalPad int32
	MaxAlign, Exact, NLines64              int32
}

type DeclarationRow struct {
	ID     int32
	FileID int32
	Name   string
	Line   int32
}

type AddrTakenRow struct {
	ID       int32
	SymbolID int32
	HasSym   bool
	FileID   int32
	Name     string
	Line     int32
	Kind     string
}

type SecretCandidateRow struct {
	ID       int32
	SymbolID int32
	HasSym   bool
	FileID   int32
	Value    string
	Line     int32
}

type AllocSiteRow struct {
	ID       int32
	SymbolID int32
	FileID   int32
	Fn       string
	SizeExpr string
	Line     int32
}

type MemopRow struct {
	ID               int32
	SymbolID         int32
	FileID           int32
	Fn               string
	Dst, Src         string
	SizeArg          string
	SizeBuf, DstTail string
	Line             int32
}

type MacroRow struct {
	SymbolID       int32
	IsFunctionlike int32
	NParams        int32
	Body           string
	HasBody        bool
	BodyLen        int32
	IsMultiline    int32
	NUses          int32
}

type GlobalRow struct {
	ID         int32
	FileID     int32
	ModuleID   int32
	Name       string
	Type       string
	Line       int32
	IsStatic   int32
	IsConst    int32
	IsVolatile int32
	IsAtomic   int32
	IsArray    int32
	PtrDepth   int32
	HasInit    int32
}

type ConfigBlockRow struct {
	ID        int32
	FileID    int32
	Directive string
	Expr      string
	Line      int32
	IsConfig  int32
}

type ReachRow struct {
	SymbolID, NTransitive, NTransitiveOut int32
}

type LockRowR struct {
	ID       int32
	SymbolID int32
	FileID   int32
	Name     string
	Line     int32
}

type EventOpRow struct {
	ID       int32
	SymbolID int32
	FileID   int32
	Family   string
	Fn       string
	Args     string
	Line     int32
}

type APIUseRow struct {
	ID       int32
	SymbolID int32
	FileID   int32
	NS       string
	Fn       string
	Line     int32
}

type IncludeCycleRow struct {
	ID      int32
	APath   string
	BPath   string
	Length  int32
	Members string
}

const (
	TIdent = iota
	TNumber
	TChar
	TStr
	TPunct
	THeader
	TEOF
	TNewline
)

type Tok struct {
	Text string
	Off  int32
	End  int32

	OrigOff int32
	Line    int32
	Col     int32
	SL      int32
	File    uint16
	Punct   uint8
	Kind    uint8

	WSBefore bool
}

var punctTable = []string{

	"%:%:",

	"<<=", ">>=", "...",

	"->", "++", "--", "<<", ">>", "<=", ">=", "==", "!=", "&&", "||",
	"*=", "/=", "%=", "+=", "-=", "&=", "^=", "|=", "##", "<:", ":>", "<%", "%>",
	"%:",

	"[", "]", "(", ")", "{", "}", ".", "&", "*", "+", "-", "~", "!",
	"/", "%", "<", ">", "^", "|", "?", ":", ";", "=", ",", "#",
}

var punctIndex = func() map[string]uint8 {
	m := make(map[string]uint8, len(punctTable))
	if len(punctTable) > 256 {
		panic("punct table exceeds uint8")
	}
	for i, p := range punctTable {
		m[p] = uint8(i)
	}
	return m
}()

var (
	PArrow   = mustPunct("->")
	PInc     = mustPunct("++")
	PDec     = mustPunct("--")
	PLsh     = mustPunct("<<")
	PRsh     = mustPunct(">>")
	PLe      = mustPunct("<=")
	PColon   = mustPunct(":")
	PSemi    = mustPunct(";")
	PEllip   = mustPunct("...")
	PLparen  = mustPunct("(")
	PRparen  = mustPunct(")")
	PLbrack  = mustPunct("[")
	PRbrack  = mustPunct("]")
	PLbrace  = mustPunct("{")
	PRbrace  = mustPunct("}")
	PTerse   = mustPunct("?")
	PLt      = mustPunct("<")
	PGt      = mustPunct(">")
	PAmp     = mustPunct("&")
	PAmpAmp  = mustPunct("&&")
	PStar    = mustPunct("*")
	PPlus    = mustPunct("+")
	PMinus   = mustPunct("-")
	PTilde   = mustPunct("~")
	PBang    = mustPunct("!")
	PSlash   = mustPunct("/")
	PMod     = mustPunct("%")
	PCaret   = mustPunct("^")
	PPipe    = mustPunct("|")
	PPipePip = mustPunct("||")
	PEq      = mustPunct("=")
	PDot     = mustPunct(".")
	PComma   = mustPunct(",")
	PHash    = mustPunct("#")
	PHashAt  = mustPunct("##")
)

func mustPunct(s string) uint8 {
	v, ok := punctIndex[s]
	if !ok {
		panic("bad punct " + s)
	}
	return v
}

func c23IsIdentStart(c byte) bool {
	return c == '_' || (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c >= 0x80
}

func c23IsIdentPart(c byte) bool {
	return c23IsIdentStart(c) || (c >= '0' && c <= '9')
}

var c23Keywords = map[string]bool{
	"alignas": true, "alignof": true, "asm": true, "auto": true, "bool": true,
	"break": true, "case": true, "char": true, "const": true, "constexpr": true,
	"continue": true, "default": true, "do": true, "double": true, "else": true,
	"enum": true, "extern": true, "false": true, "float": true, "for": true,
	"goto": true, "if": true, "inline": true, "int": true, "long": true,
	"nullptr": true, "register": true, "restrict": true, "return": true,
	"short": true, "signed": true, "sizeof": true, "static": true,
	"static_assert": true, "struct": true, "switch": true, "thread_local": true,
	"true": true, "typedef": true, "typeof": true, "typeof_unqual": true,
	"union": true, "unsigned": true, "void": true, "volatile": true,
	"while":    true,
	"_Alignas": true, "_Alignof": true, "_Atomic": true, "_BitInt": true,
	"_Bool": true, "_Complex": true, "_Decimal128": true, "_Decimal64": true,
	"_Decimal32": true, "_Generic": true, "_Imaginary": true, "_Noreturn": true,
	"_Static_assert": true, "_Thread_local": true,
	"__asm__": true, "__asm": true, "asm_": false,
	"__attribute__": true, "__attribute": true,
	"__const": true, "__const__": true, "__inline": true, "__inline__": true,
	"__restrict": true, "__restrict__": true, "__signed": true,
	"__signed__": true, "__volatile": true, "__volatile__": true,
	"__typeof": true, "__typeof__": true, "__typeof_unqual__": true,
	"__extension__": true, "__alignof": true, "__alignof__": true,
	"__thread": true, "__builtin_va_arg": true, "__builtin_offsetof": true,
	"__builtin_types_compatible_p": true, "__label__": true,
}

func isKeyword(s string) bool { return c23Keywords[s] }

var c23AttrNames = map[string]bool{
	"deprecated": true, "fallthrough": true, "maybe_unused": true,
	"nodiscard": true, "noreturn": true, "_Noreturn": true,
	"reproducible": true, "unsequenced": true,
}

func isC23AttrName(s string) bool { return c23AttrNames[s] }

func spliceSource(src []byte) (out []byte, origOf []int32, origLine []int32, lineStart []int32) {
	out = make([]byte, 0, len(src)+64)
	origOf = make([]int32, 0, len(src)+64)
	origLine = make([]int32, 0, len(src)+64)
	lineStart = append(lineStart, 0)
	ol, oo := int32(1), int32(0)
	i := 0
	n := len(src)
	push := func(c byte) {
		out = append(out, c)
		origOf = append(origOf, oo)
		origLine = append(origLine, ol)
	}
	for i < n {
		c := src[i]
		if c == '\\' && i+1 < n {

			if src[i+1] == '\n' {
				ol++
				oo += 2
				i += 2
				continue
			}
			if src[i+1] == '\r' {
				adv := 2
				if i+2 < n && src[i+2] == '\n' {
					adv = 3
				}
				ol++
				oo += int32(adv)
				i += adv
				continue
			}
		}
		switch {
		case c == '\n':
			push('\n')
			oo++
			i++
			lineStart = append(lineStart, int32(len(out)))
			ol++
		case c == '\r':
			push('\n')
			oo++
			i++
			if i < n && src[i] == '\n' {
				oo++
				i++
			}
			lineStart = append(lineStart, int32(len(out)))
			ol++
		default:
			push(c)
			oo++
			i++
		}
	}
	return out, origOf, origLine, lineStart
}

func stripBOM(b []byte) []byte {
	if len(b) >= 3 && b[0] == 0xEF && b[1] == 0xBB && b[2] == 0xBF {
		return b[3:]
	}
	return b
}

type lexErr struct {
	off  int32
	msg  string
	line int32
}

type lexer struct {
	src      []byte
	origOf   []int32
	origLine []int32
	lineStar []int32
	fileID   uint32
	pos      int32
	curLine  int32
	posLine  int32
	errs     *[]lexErr

	afterHash  bool
	includeCtx bool
}

func tokFileID(id uint32) uint16 {
	if id > maxFilesPerRun {
		panic("file id exceeds tok uint16")
	}
	return uint16(id)
}

func newLexer(src []byte, fileID uint32, errs *[]lexErr) *lexer {
	src = stripBOM(src)
	lineStar := make([]int32, 0, len(src)/24+8)
	lineStar = append(lineStar, 0)
	for i := 0; i < len(src); i++ {
		c := src[i]
		if c == '\r' || (c == '\\' && i+1 < len(src) &&
			(src[i+1] == '\n' || src[i+1] == '\r')) {
			b, origOf, origLine, ls := spliceSource(src)
			return &lexer{src: b, origOf: origOf, origLine: origLine,
				lineStar: ls, fileID: fileID, errs: errs}
		}
		if c == '\n' {
			lineStar = append(lineStar, int32(i+1))
		}
	}
	return &lexer{src: src, lineStar: lineStar, fileID: fileID, errs: errs}
}

func (lx *lexer) errf(off int32, msg string) {
	if lx.errs != nil && len(*lx.errs) < 4096 {
		*lx.errs = append(*lx.errs, lexErr{off: off, msg: msg, line: lx.lineAt(off)})
	}
}

func (lx *lexer) lineAt(off int32) int32 {
	if lx.origLine == nil {
		if int(off) >= len(lx.src) {
			off = int32(len(lx.src)) - 1
			if off < 0 {
				return 1
			}
		}
		lo, hi := 0, len(lx.lineStar)
		for lo < hi {
			mid := (lo + hi) / 2
			if lx.lineStar[mid] <= off {
				lo = mid + 1
			} else {
				hi = mid
			}
		}
		if lo < 1 {
			return 1
		}
		return int32(lo)
	}
	if int(off) < len(lx.origLine) {
		return lx.origLine[off]
	}
	if n := int32(len(lx.origLine)); n > 0 {
		return lx.origLine[n-1]
	}
	return 1
}

func (lx *lexer) posOf(off int32) (origOff, line, col int32) {
	if lx.origLine == nil {
		if int(off) >= len(lx.src) {
			off = int32(len(lx.src)) - 1
			if off < 0 {
				return 0, 1, 1
			}
		}
	} else if int(off) >= len(lx.origOf) {
		off = int32(len(lx.origOf)) - 1
		if off < 0 {
			return 0, 1, 1
		}
	}

	lineIdx := int(lx.posLine)
	if lineIdx >= len(lx.lineStar) || lx.lineStar[lineIdx] > off {
		lo, hi := 0, len(lx.lineStar)
		for lo < hi {
			mid := (lo + hi) / 2
			if lx.lineStar[mid] <= off {
				lo = mid + 1
			} else {
				hi = mid
			}
		}
		lineIdx = lo - 1
		if lineIdx < 0 {
			lineIdx = 0
		}
	} else {
		for lineIdx+1 < len(lx.lineStar) && lx.lineStar[lineIdx+1] <= off {
			lineIdx++
		}
	}
	lx.posLine = int32(lineIdx)
	if lx.origLine == nil {
		return off, int32(lineIdx + 1), off - lx.lineStar[lineIdx] + 1
	}
	return lx.origOf[off], lx.origLine[off], off - lx.lineStar[lineIdx] + 1
}

func (lx *lexer) at(off int32) byte {
	if int(off) >= len(lx.src) {
		return 0
	}
	return lx.src[off]
}

func (lx *lexer) eof() bool { return lx.pos >= int32(len(lx.src)) }

func (lx *lexer) skipWS() {
	for lx.pos < int32(len(lx.src)) {
		c := lx.src[lx.pos]
		if c == '\n' {
			return
		}
		if c == ' ' || c == '\t' || c == '\v' || c == '\f' || c == '\r' {
			lx.pos++
			continue
		}
		if c == '/' && lx.at(lx.pos+1) == '/' {
			for lx.pos < int32(len(lx.src)) && lx.src[lx.pos] != '\n' {
				lx.pos++
			}
			continue
		}
		if c == '/' && lx.at(lx.pos+1) == '*' {
			start := lx.pos
			lx.pos += 2
			closed := false
			for lx.pos < int32(len(lx.src)) {
				if lx.src[lx.pos] == '*' && lx.at(lx.pos+1) == '/' {
					lx.pos += 2
					closed = true
					break
				}
				lx.pos++
			}
			if !closed {
				lx.errf(start, "unterminated /* comment")
			}
			continue
		}
		return
	}
}

func (lx *lexer) next() Tok {
	p0 := lx.pos
	lx.skipWS()
	wsBefore := lx.pos > p0

	for int(lx.curLine+1) < len(lx.lineStar) && lx.lineStar[lx.curLine+1] <= lx.pos {
		lx.curLine++
	}
	if lx.pos >= int32(len(lx.src)) {
		_, l, co := lx.posOf(int32(len(lx.src)))
		return Tok{Kind: TEOF, Off: int32(len(lx.src)), End: int32(len(lx.src)),
			Line: l, Col: co, File: tokFileID(lx.fileID), WSBefore: wsBefore, SL: lx.curLine}
	}

	if lx.src[lx.pos] == '\n' {
		lx.pos++
		_, l, co := lx.posOf(lx.pos - 1)
		lx.afterHash = false
		lx.includeCtx = false
		return Tok{Kind: TNewline, Text: "\n", Off: lx.pos - 1, End: lx.pos,
			Line: l, Col: co, File: tokFileID(lx.fileID), WSBefore: wsBefore, SL: lx.curLine}
	}
	start := lx.pos
	c := lx.src[lx.pos]
	var t Tok
	t.File = tokFileID(lx.fileID)
	t.WSBefore = wsBefore
	switch {

	case c == '\'' || (c == 'L' && lx.at(lx.pos+1) == '\'') ||
		(c == 'u' && (lx.at(lx.pos+1) == '\'' || (lx.at(lx.pos+1) == '8' && lx.at(lx.pos+2) == '\''))) ||
		(c == 'U' && lx.at(lx.pos+1) == '\''):
		t.Kind = TChar
		lx.scanQuoted('\'')
		t.Text = string(lx.src[start:lx.pos])
	case c == '"' || (c == 'L' && lx.at(lx.pos+1) == '"') ||
		(c == 'u' && (lx.at(lx.pos+1) == '"' || (lx.at(lx.pos+1) == '8' && lx.at(lx.pos+2) == '"'))) ||
		(c == 'U' && lx.at(lx.pos+1) == '"'):
		t.Kind = TStr
		lx.scanQuoted('"')
		t.Text = string(lx.src[start:lx.pos])
	case c23IsIdentStart(c):
		t.Kind = TIdent
		lx.pos++
		for lx.pos < int32(len(lx.src)) {
			ch := lx.src[lx.pos]
			if c23IsIdentPart(ch) {
				lx.pos++
				continue
			}
			if ch == '\\' && (lx.at(lx.pos+1) == 'u' || lx.at(lx.pos+1) == 'U') {
				lx.pos += 2
				nd := 4
				if lx.at(lx.pos-1) == 'U' {
					nd = 8
				}
				for k := 0; k < nd && isHex(lx.at(lx.pos)); k++ {
					lx.pos++
				}
				continue
			}
			break
		}
		t.Text = string(lx.src[start:lx.pos])
	case isDigit(c) || (c == '.' && isDigit(lx.at(lx.pos+1))):
		t.Kind = TNumber
		lx.scanPPNumber()
		t.Text = string(lx.src[start:lx.pos])
	case lx.includeCtx && c == '<':
		t.Kind = THeader
		lx.pos++
		for lx.pos < int32(len(lx.src)) {
			ch := lx.src[lx.pos]
			if ch == '>' {
				lx.pos++
				break
			}
			if ch == '\n' {
				lx.errf(start, "unterminated header name")
				break
			}
			lx.pos++
		}
		t.Text = string(lx.src[start:lx.pos])
	default:

		t.Kind = TPunct
		best := uint8(0xFF)
		bestLen := 0
		for l := 4; l >= 1; l-- {
			if int(lx.pos)+l > len(lx.src) {
				continue
			}
			if code, ok := punctIndex[string(lx.src[lx.pos:int(lx.pos)+l])]; ok {
				best, bestLen = code, l
				break
			}
		}
		if bestLen == 0 {
			lx.errf(lx.pos, "stray byte in source")
			lx.pos++
			return lx.next()
		}
		lx.pos += int32(bestLen)
		t.Punct = normalizeDigraph(best, string(lx.src[lx.pos-int32(bestLen):lx.pos]))
		t.Text = string(lx.src[start:lx.pos])
	}
	t.Off = start
	t.End = lx.pos
	t.OrigOff, t.Line, t.Col = lx.posOf(start)
	t.SL = lx.curLine
	lx.updateIncludeCtx(t)
	return t
}

func (lx *lexer) updateIncludeCtx(t Tok) {
	if t.Kind == TPunct {
		if t.Punct == PHash {
			lx.afterHash = true
			return
		}
		if t.Punct == PRparen || t.Punct == PComma || t.Punct == PSemi {
			lx.includeCtx = false
			lx.afterHash = false
			return
		}
		return
	}
	if t.Kind == THeader {
		lx.includeCtx = false
		return
	}
	if t.Kind == TIdent {
		if lx.afterHash {
			switch t.Text {
			case "include", "include_next", "embed", "embed_next":
				lx.includeCtx = true
				lx.afterHash = false
				return
			}
			lx.afterHash = false
		}
		switch t.Text {
		case "__has_include", "__has_include_next", "__has_embed":
			lx.includeCtx = true
		}
	}
}

func (lx *lexer) skipComment() {

	if lx.at(lx.pos+1) == '/' {
		for lx.pos < int32(len(lx.src)) && lx.src[lx.pos] != '\n' {
			lx.pos++
		}
		return
	}
	lx.pos += 2
	for lx.pos < int32(len(lx.src)) {
		if lx.src[lx.pos] == '*' && lx.at(lx.pos+1) == '/' {
			lx.pos += 2
			return
		}
		lx.pos++
	}
}

func normalizeDigraph(code uint8, text string) uint8 {
	switch text {
	case "<:":
		return PLbrack
	case ":>":
		return PRbrack
	case "<%":
		return PLbrace
	case "%>":
		return PRbrace
	case "%:":
		return PHash
	case "%:%:":
		return PHashAt
	}
	return code
}

func isHex(c byte) bool {
	return isDigit(c) || (c >= 'a' && c <= 'f') || (c >= 'A' && c <= 'F')
}

func (lx *lexer) scanPPNumber() {
	lx.pos++
	for lx.pos < int32(len(lx.src)) {
		c := lx.src[lx.pos]
		if c23IsIdentPart(c) || c == '.' {

			if (c == 'e' || c == 'E' || c == 'p' || c == 'P') &&
				(lx.at(lx.pos+1) == '+' || lx.at(lx.pos+1) == '-') {
				lx.pos++
				if lx.pos < int32(len(lx.src)) {
					lx.pos++
				}
				continue
			}
			lx.pos++
			continue
		}
		if c == '\'' && c23IsIdentPart(lx.at(lx.pos+1)) {
			lx.pos++
			continue
		}
		break
	}
}

func (lx *lexer) scanQuoted(quote byte) {

	for lx.pos < int32(len(lx.src)) && lx.src[lx.pos] != quote {
		lx.pos++
	}
	if lx.pos >= int32(len(lx.src)) {
		lx.errf(lx.pos, "unterminated "+qname(quote))
		return
	}
	lx.pos++
	for lx.pos < int32(len(lx.src)) {
		c := lx.src[lx.pos]
		if c == '\\' {
			lx.pos += 2
			continue
		}
		if c == '\n' {
			lx.errf(lx.pos, "unterminated "+qname(quote))
			return
		}
		if c == quote {
			lx.pos++
			return
		}
		lx.pos++
	}
	lx.errf(lx.pos, "unterminated "+qname(quote))
}

func qname(q byte) string {
	if q == '\'' {
		return "char const"
	}
	return "string literal"
}

const (
	maxIncludeDepth = 100
	maxFilesPerRun  = 8000
	ppMaxFileBytes  = 32 << 20
	maxExpand       = 1 << 22
)

type ppMacro struct {
	Name       string
	IsFn       bool
	Params     []string
	IsVariadic bool
	VaName     string
	Body       []Tok
	Raw        string
	Line       int32
	FileID     uint32
	Uses       int32
}

type includeEdge struct {
	fromID   uint32
	target   string
	resolved string
	sys      bool
	line     int32
}

type pragmaRow struct {
	fileID uint32
	text   string
	line   int32
}

type cfgRow struct {
	fileID    uint32
	directive string
	expr      string
	line      int32
}

type fileTokSrc struct {
	path   string
	id     uint32
	raw    []byte
	toks   []Tok
	eofTok Tok
	pos    int
	once   bool
	active bool
}

type preprocessor struct {
	macros    map[string]*ppMacro
	allMacros []*ppMacro
	incDirs   []string
	root      string

	out  []Tok
	errs *[]lexErr

	files    []*fileTokSrc
	fileByID map[uint32]*fileTokSrc
	nfiles   int

	includes []includeEdge
	pragmas  []pragmaRow
	cfgs     []cfgRow

	cond    []condState
	onceSet map[string]bool
	onStack map[string]bool

	genFileID uint32

	lineDelta int64
	fileName  string

	depth   int
	stopped bool
	nExpand int
}

type condState struct {
	parentActive bool
	takenYet     bool
	activeNow    bool
	seenElse     bool
}

func newPP(root string, incDirs []string, errs *[]lexErr) *preprocessor {
	pp := &preprocessor{
		macros:   map[string]*ppMacro{},
		incDirs:  incDirs,
		root:     root,
		errs:     errs,
		fileByID: map[uint32]*fileTokSrc{},
		onceSet:  map[string]bool{},
		onStack:  map[string]bool{},
	}

	for _, d := range [][2]string{
		{"__STDC__", "1"}, {"__STDC_VERSION__", "202311L"},
		{"__STDC_HOSTED__", "1"}, {"__c23parser", "1"},
		{"__CHAR_BIT__", "8"}, {"__SIZEOF_LONG__", "8"}, {"__SIZEOF_PTRDIFF_T__", "8"},
		{"__SIZE_TYPE__", "unsigned long"}, {"__PTRDIFF_TYPE__", "long"},
		{"LITTLE_ENDIAN", "1234"}, {"BIG_ENDIAN", "4321"},
		{"BYTE_ORDER", "1234"}, {"__BYTE_ORDER", "1234"},
		{"__ORDER_LITTLE_ENDIAN__", "1234"}, {"__ORDER_BIG_ENDIAN__", "4321"},
		{"__ORDER_PDP_ENDIAN__", "3412"},
		{"__linux__", "1"}, {"linux", "1"}, {"__unix__", "1"}, {"__unix", "1"},
		{"__APPLE__", "1"}, {"__MACH__", "1"},
		{"__x86_64__", "1"}, {"__x86_64", "1"}, {"__amd64__", "1"}, {"__amd64", "1"},
		{"__LITTLE_ENDIAN__", "1"}, {"__ARM_ARCH", "8"},

		{"__has_include", "1"}, {"__has_include_next", "1"},
		{"__has_c_attribute", "0"}, {"__has_embed", "0"},
	} {

		pp.macros[d[0]] = &ppMacro{Name: d[0], Body: ppPredefBody(d[1]),
			Raw: d[1]}
	}
	return pp
}

func ppPredefBody(text string) []Tok {
	lex := newLexer([]byte(text), 0, nil)
	var out []Tok
	for i := 0; i < 64; i++ {
		t := lex.next()
		if t.Kind == TEOF {
			break
		}
		out = append(out, t)
	}
	return out
}

func (pp *preprocessor) errf(line int32, msg string) {
	if pp.errs != nil && len(*pp.errs) < 4096 {
		*pp.errs = append(*pp.errs, lexErr{off: 0, msg: msg, line: line})
	}
}

var ppSrcMu sync.RWMutex
var ppSrcCache = map[string][]byte{}

const tokBufMax = 131072

var tokBufPool = sync.Pool{}

func getTokBuf() []Tok {
	if v := tokBufPool.Get(); v != nil {
		return v.([]Tok)[:0]
	}
	return nil
}

func putTokBuf(b []Tok) {
	if c := cap(b); c >= 1024 && c <= tokBufMax {
		tokBufPool.Put(b[:0])
	}
}

func ppCachedRead(abs string) ([]byte, bool) {
	ppSrcMu.RLock()
	data, ok := ppSrcCache[abs]
	ppSrcMu.RUnlock()
	return data, ok
}

func (pp *preprocessor) loadFile(abs string) (*fileTokSrc, bool) {
	if pp.nfiles >= maxFilesPerRun {
		return nil, false
	}
	data, ok := ppCachedRead(abs)
	if !ok {
		fi, err := os.Stat(abs)
		if err != nil || fi.IsDir() || fi.Size() > ppMaxFileBytes {
			return nil, false
		}
		data, err = os.ReadFile(abs)
		if err != nil {
			return nil, false
		}
	}
	pp.nfiles++
	lex := newLexer(data, pp.genFileID+1, pp.errs)
	_ = data
	pp.genFileID++
	id := pp.genFileID
	src := &fileTokSrc{path: abs, id: id, raw: data}
	src.toks = make([]Tok, 0, len(data)/7+16)
	for {
		t := lex.next()
		src.toks = append(src.toks, t)
		if t.Kind == TEOF {
			src.eofTok = t
			break
		}
	}
	pp.files = append(pp.files, src)
	pp.fileByID[id] = src
	return src, true
}

func (pp *preprocessor) relFileName(abs string) string {
	if pp.root == "" {
		return abs
	}
	base := filepath.Dir(pp.root)
	if base == "" {
		return abs
	}
	if r, err := filepath.Rel(base, abs); err == nil && !strings.HasPrefix(r, "..") {
		return filepath.ToSlash(r)
	}
	return abs
}

func (pp *preprocessor) run(abs string) []Tok {
	pp.out = getTokBuf()
	pp.fileName = pp.relFileName(abs)
	if src, ok := pp.loadFile(abs); ok {
		pp.process(src, 1)
	}

	eof := Tok{Kind: TEOF, Text: "", File: tokFileID(pp.genFileID), Line: 1, Col: 1}
	if len(pp.files) > 0 {
		eof = pp.files[len(pp.files)-1].eofTok
	}
	pp.out = append(pp.out, eof)
	return pp.out
}

func (pp *preprocessor) process(src *fileTokSrc, depth int) {
	if src.active || pp.onceSet[src.path] || depth > maxIncludeDepth {
		return
	}
	src.active = true
	pp.onStack[src.path] = true

	savedName := pp.fileName
	pp.fileName = pp.relFileName(src.path)
	defer func() {
		src.active = false
		pp.onStack[src.path] = false
		src.toks = nil
		pp.fileName = savedName
	}()

	for src.pos < len(src.toks) {
		t := src.toks[src.pos]
		if t.Kind == TEOF {
			return
		}
		lineStart := src.pos
		lineEnd := src.pos
		for lineEnd < len(src.toks) && src.toks[lineEnd].Kind != TNewline &&
			src.toks[lineEnd].Kind != TEOF {
			lineEnd++
		}
		hadNL := lineEnd < len(src.toks) && src.toks[lineEnd].Kind == TNewline
		line := src.toks[lineStart:lineEnd]
		src.pos = lineEnd
		if hadNL {
			src.pos++
		}
		if len(line) == 0 {
			continue
		}
		if line[0].Kind == TPunct && line[0].Punct == PHash {
			pp.directive(src, line, line[0].Line, depth)
			if pp.stopped {
				return
			}
			continue
		}
		if !pp.condActive() {
			continue
		}
		if pp.lineMayExpand(line) {
			pp.out = append(pp.out, pp.expand(line)...)
		} else {
			pp.out = append(pp.out, line...)
		}
	}
}

func (pp *preprocessor) directive(src *fileTokSrc, line []Tok, dirLine int32, depth int) {
	if len(line) < 2 {
		return
	}
	name := line[1]
	if name.Kind != TIdent {
		pp.errf(name.Line, "bad directive name")
		return
	}
	rest := line[2:]
	dir := name.Text
	switch dir {
	case "define":
		pp.doDefine(src, line)
	case "undef":
		if len(rest) > 0 && rest[0].Kind == TIdent {
			if pp.condActive() {
				delete(pp.macros, rest[0].Text)
			}
		}
	case "include", "include_next":
		pp.doInclude(src, rest, dirLine, depth)
	case "if":
		expr := tokLineText(rest)
		val := int64(0)
		active := pp.condActive()
		if active {
			val = pp.evalCond(src, rest, dirLine)
		}
		pp.cfgs = append(pp.cfgs, cfgRow{src.id, "if", expr, dirLine})
		on := active && val != 0
		pp.cond = append(pp.cond, condState{parentActive: active,
			takenYet: on, activeNow: on})
	case "ifdef", "ifndef":
		val := false
		if pp.condActive() {
			def := false
			if len(rest) > 0 && rest[0].Kind == TIdent {
				_, def = pp.macros[rest[0].Text]
			}
			val = def
			if dir == "ifndef" {
				val = !def
			}
		}
		pp.cfgs = append(pp.cfgs, cfgRow{src.id, dir, tokLineText(rest), dirLine})
		on := pp.condActive() && val
		pp.cond = append(pp.cond, condState{parentActive: pp.condActive(),
			takenYet: on, activeNow: on})
	case "elif":
		expr := tokLineText(rest)
		if len(pp.cond) == 0 {
			pp.errf(dirLine, "#elif without #if")
			return
		}
		st := &pp.cond[len(pp.cond)-1]
		pp.cfgs = append(pp.cfgs, cfgRow{src.id, "elif", expr, dirLine})
		if st.seenElse {
			pp.errf(dirLine, "#elif after #else")
			return
		}
		st.activeNow = false
		if st.parentActive && !st.takenYet && pp.evalCond(src, rest, dirLine) != 0 {
			st.activeNow = true
			st.takenYet = true
		}
	case "elifdef", "elifndef":
		if len(pp.cond) == 0 {
			pp.errf(dirLine, "#"+dir+" without #if")
			return
		}
		st := &pp.cond[len(pp.cond)-1]
		pp.cfgs = append(pp.cfgs, cfgRow{src.id, dir, tokLineText(rest), dirLine})
		if st.seenElse {
			return
		}
		st.activeNow = false
		if st.parentActive && !st.takenYet {
			def := false
			if len(rest) > 0 && rest[0].Kind == TIdent {
				_, def = pp.macros[rest[0].Text]
			}
			if dir == "elifndef" {
				def = !def
			}
			st.activeNow = def
			st.takenYet = def
		}
	case "else":
		if len(pp.cond) == 0 {
			pp.errf(dirLine, "#else without #if")
			return
		}
		st := &pp.cond[len(pp.cond)-1]
		pp.cfgs = append(pp.cfgs, cfgRow{src.id, "else", "", dirLine})
		st.seenElse = true
		st.activeNow = st.parentActive && !st.takenYet
		st.takenYet = st.takenYet || st.activeNow
	case "endif":
		pp.cfgs = append(pp.cfgs, cfgRow{src.id, "endif", "", dirLine})
		if len(pp.cond) == 0 {
			pp.errf(dirLine, "#endif without #if")
			return
		}
		pp.cond = pp.cond[:len(pp.cond)-1]
	case "line":
		pp.doLine(src, rest, dirLine)
	case "error":

		if pp.condActive() {
			pp.errf(dirLine, "#error: "+tokLineText(rest))
		}
	case "warning":
		pp.pragmas = append(pp.pragmas, pragmaRow{src.id, "#warning " + tokLineText(rest), dirLine})
	case "pragma":
		if len(rest) > 0 && rest[0].Kind == TIdent && rest[0].Text == "once" {
			pp.onceSet[src.path] = true
			src.once = true
		}
		pp.pragmas = append(pp.pragmas, pragmaRow{src.id, "#pragma " + tokLineText(rest), dirLine})
	case "embed", "embed_next":

		pp.pragmas = append(pp.pragmas, pragmaRow{src.id, "#" + dir + " " + tokLineText(rest), dirLine})
	default:
		pp.errf(dirLine, "unknown directive #"+dir)
	}
}

func tokLineText(toks []Tok) string {
	var b strings.Builder
	for i, t := range toks {
		if i > 0 && t.WSBefore {
			b.WriteByte(' ')
		}
		b.WriteString(t.Text)
	}
	return b.String()
}

func (pp *preprocessor) condActive() bool {
	for i := range pp.cond {
		if !pp.cond[i].activeNow {
			return false
		}
	}
	return true
}

func (pp *preprocessor) condActiveOuter() bool {
	for i := 0; i < len(pp.cond)-1; i++ {
		if !pp.cond[i].activeNow {
			return false
		}
	}
	return true
}

func (pp *preprocessor) doDefine(src *fileTokSrc, line []Tok) {

	if len(line) < 3 || line[2].Kind != TIdent {
		pp.errf(line[0].Line, "malformed #define")
		return
	}
	nmTok := line[2]
	m := &ppMacro{Name: nmTok.Text, FileID: src.id, Line: nmTok.Line}
	i := 3
	if i < len(line) && line[i].Kind == TPunct && line[i].Punct == PLparen && !line[i].WSBefore {

		i++
		var params []string
		m.IsVariadic = false
		cur := strings.Builder{}
		depthP := 1
		for i < len(line) && depthP > 0 {
			t := line[i]
			switch {
			case t.Kind == TPunct && t.Punct == PLparen:
				depthP++
				cur.WriteByte('(')
			case t.Kind == TPunct && t.Punct == PRparen:
				depthP--
				if depthP == 0 {
					break
				}
				cur.WriteByte(')')
			case t.Kind == TPunct && t.Punct == PComma && depthP == 1:
				s := strings.TrimSpace(cur.String())
				if s != "" {
					params = append(params, s)
				}
				cur.Reset()
			case t.Kind == TPunct && t.Punct == PEllip && depthP == 1:
				m.IsVariadic = true
				if c := strings.TrimSpace(cur.String()); c != "" {
					m.VaName = c
				}
				cur.Reset()
			case t.Kind == TNewline:

			default:
				cur.WriteString(t.Text)
			}
			i++
		}
		if depthP != 0 {
			pp.errf(nmTok.Line, "unbalanced macro parameter list")
			return
		}
		if s := strings.TrimSpace(cur.String()); s != "" {
			params = append(params, s)
		}
		m.IsFn = true
		m.Params = params
		if m.IsVariadic && m.VaName == "" {
			m.VaName = "__VA_ARGS__"
		}
	}
	if i < len(line) {
		m.Body = append([]Tok(nil), line[i:]...)
	}
	m.Raw = tokLineText(line[3:])
	pp.allMacros = append(pp.allMacros, m)
	if pp.condActive() {
		pp.macros[m.Name] = m
	}
}

func (pp *preprocessor) doInclude(src *fileTokSrc, rest []Tok, dirLine int32, depth int) {
	if len(rest) == 0 {
		pp.errf(dirLine, "empty #include")
		return
	}
	tgt := ""
	sys := false
	switch {
	case rest[0].Kind == THeader:
		tgt = strings.TrimSuffix(strings.TrimPrefix(rest[0].Text, "<"), ">")
		sys = true
	case rest[0].Kind == TStr:
		tgt = dequote(rest[0].Text)
	default:
		ex := pp.expand(rest)
		if len(ex) > 0 {
			switch {
			case ex[0].Kind == THeader:
				tgt = strings.TrimSuffix(strings.TrimPrefix(ex[0].Text, "<"), ">")
				sys = true
			case ex[0].Kind == TStr:
				tgt = dequote(ex[0].Text)
			}
		}
	}
	if tgt == "" {
		pp.errf(dirLine, "malformed #include")
		return
	}
	resolved := pp.resolveInclude(src, tgt, sys)
	pp.includes = append(pp.includes, includeEdge{fromID: src.id, target: tgt,
		resolved: resolved, sys: sys, line: dirLine})
	if resolved == "" || !pp.condActive() {
		return
	}
	if pp.onceSet[resolved] || pp.onStack[resolved] {
		return
	}
	nxt, ok := pp.loadFile(resolved)
	if !ok {
		return
	}
	pp.process(nxt, depth+1)
}

func dequote(s string) string {
	s = strings.TrimPrefix(s, "u8")
	s = strings.TrimPrefix(s, "u")
	s = strings.TrimPrefix(s, "U")
	s = strings.TrimPrefix(s, "L")
	return strings.Trim(s, `"`)
}

type incCacheKey struct {
	root string
	dir  string
	tgt  string
	sys  bool
}

var (
	incCacheMu sync.RWMutex
	incCache   = map[incCacheKey]string{}

	statSeen sync.Map
)

func statIsFile(p string) bool {
	if v, ok := statSeen.Load(p); ok {
		return v.(bool)
	}
	fi, err := os.Stat(p)
	r := err == nil && !fi.IsDir()
	statSeen.Store(p, r)
	return r
}

func (pp *preprocessor) resolveInclude(src *fileTokSrc, tgt string, sys bool) string {
	key := incCacheKey{root: pp.root, tgt: tgt, sys: sys}
	if !sys {
		key.dir = filepath.Dir(src.path)
	}
	cacheable := len(pp.incDirs) == 0
	if cacheable {
		incCacheMu.RLock()
		hit, ok := incCache[key]
		incCacheMu.RUnlock()
		if ok {
			return hit
		}
	}
	cands := make([]string, 0, 4+len(pp.incDirs))
	if !sys {
		cands = append(cands, filepath.Join(key.dir, tgt))
	}
	for _, d := range pp.incDirs {
		cands = append(cands, filepath.Join(d, tgt))
	}
	if pp.root != "" {
		cands = append(cands, filepath.Join(pp.root, tgt))
	}
	res := ""
	for _, c := range cands {
		if statIsFile(c) {
			if rp, err2 := filepath.Abs(c); err2 == nil {
				res = rp
			} else {
				res = c
			}
			break
		}
	}
	if cacheable {
		incCacheMu.Lock()
		incCache[key] = res
		incCacheMu.Unlock()
	}
	return res
}

func (pp *preprocessor) doLine(src *fileTokSrc, rest []Tok, dirLine int32) {
	if len(rest) == 0 {
		return
	}
	ex := pp.expand(rest)
	if len(ex) == 0 {
		return
	}
	if v, ok := ppInt(ex[0].Text); ok {

		pp.lineDelta = v - int64(dirLine) - 1
	}
	if len(ex) > 2 && ex[1].Kind == TStr {
		pp.fileName = dequote(ex[1].Text)
	}
}

func ppInt(s string) (int64, bool) {
	v, err := strconv.ParseInt(stripNumSuffix(s), 0, 64)
	return v, err == nil
}

func stripNumSuffix(s string) string {

	i := len(s)
	for i > 0 {
		c := s[i-1]
		if c == 'u' || c == 'U' || c == 'l' || c == 'L' || c == 'z' || c == 'Z' || c == 'i' || c == 'I' {
			i--
			continue
		}
		break
	}
	return s[:i]
}

type expTok struct {
	t    Tok
	hide *hideSet
}

type hideSet struct {
	names map[string]bool
}

func (h *hideSet) has(n string) bool { return h != nil && h.names[n] }

func addHide(h *hideSet, name string) *hideSet {
	nh := &hideSet{names: map[string]bool{}}
	if h != nil {
		for k := range h.names {
			nh.names[k] = true
		}
	}
	nh.names[name] = true
	return nh
}

func (pp *preprocessor) lineMayExpand(in []Tok) bool {
	for i := range in {
		if in[i].Kind != TIdent {
			continue
		}
		tx := in[i].Text
		if tx == "__LINE__" || tx == "__FILE__" {
			return true
		}
		if _, ok := pp.macros[tx]; ok {
			return true
		}
	}
	return false
}

func (pp *preprocessor) expand(in []Tok) []Tok {
	work := make([]expTok, len(in))
	for i := range in {
		work[len(in)-1-i] = expTok{in[i], nil}
	}
	return pp.expandWork(work)
}

func (pp *preprocessor) expandETS(ets []expTok) []Tok {
	work := make([]expTok, 0, len(ets)+32)
	for i := len(ets) - 1; i >= 0; i-- {
		work = append(work, ets[i])
	}
	return pp.expandWork(work)
}

func (pp *preprocessor) expandWork(work []expTok) []Tok {
	out := make([]Tok, 0, cap(work))
	for len(work) > 0 {
		et := work[len(work)-1]
		work = work[:len(work)-1]
		t := et.t
		if t.Kind == TNewline || t.Kind == TEOF || t.Kind != TIdent || et.hide.has(t.Text) {
			out = append(out, t)
			continue
		}
		m := pp.macros[t.Text]
		if m == nil {
			if nt, ok := pp.nativeBuiltin(t); ok {
				out = append(out, nt)
				continue
			}
			out = append(out, t)
			continue
		}
		if pp.nExpand++; pp.nExpand > maxExpand {
			out = append(out, t)
			continue
		}
		if !m.IsFn {
			m.Uses++
			nh := addHide(et.hide, m.Name)
			sub := pp.subst(m, nil, nh, t)
			for k := len(sub) - 1; k >= 0; k-- {
				work = append(work, expTok{sub[k], nh})
			}
			continue
		}

		j := len(work) - 1
		for j >= 0 && work[j].t.Kind == TNewline {
			j--
		}
		if j < 0 || work[j].t.Kind != TPunct || work[j].t.Punct != PLparen {
			out = append(out, t)
			continue
		}
		args, rest, ok := pp.collectArgs(work[:j])
		if !ok {
			out = append(out, t)
			continue
		}
		work = rest
		m.Uses++
		nh := addHide(et.hide, m.Name)
		sub := pp.subst(m, args, nh, t)
		for k := len(sub) - 1; k >= 0; k-- {
			work = append(work, expTok{sub[k], nh})
		}
	}
	return out
}

func (pp *preprocessor) collectArgs(work []expTok) ([][]expTok, []expTok, bool) {
	var args [][]expTok
	cur := []expTok{}
	depth := 1
	i := len(work) - 1
	for i >= 0 {
		et := work[i]
		t := et.t
		i--
		if t.Kind == TEOF {
			return nil, work, false
		}
		if t.Kind == TPunct && t.Punct == PLparen {
			depth++
			cur = append(cur, et)
			continue
		}
		if t.Kind == TPunct && t.Punct == PRparen {
			depth--
			if depth == 0 {
				args = append(args, cur)
				return args, work[:i+1], true
			}
			cur = append(cur, et)
			continue
		}
		if t.Kind == TPunct && t.Punct == PComma && depth == 1 {
			args = append(args, cur)
			cur = []expTok{}
			continue
		}
		if t.Kind == TNewline {
			continue
		}
		cur = append(cur, et)
	}
	return nil, work, false
}

func (pp *preprocessor) subst(m *ppMacro, args [][]expTok, useHide *hideSet, use Tok) []Tok {
	body := m.Body
	out := make([]Tok, 0, len(body)+16)
	vaArgs := [][]expTok(nil)
	if m.IsVariadic && args != nil && len(args) > len(m.Params) {
		vaArgs = args[len(m.Params):]
		args = args[:len(m.Params)]
	}
	if m.IsVariadic && args != nil && len(args) < len(m.Params) {

		for len(args) < len(m.Params) {
			args = append(args, nil)
		}
	}
	for bi := 0; bi < len(body); bi++ {
		bt := body[bi]

		if bt.Kind == TPunct && bt.Punct == PHash && m.IsFn && bi+1 < len(body) {
			pt := body[bi+1]
			if pt.Kind == TIdent {
				if ai := paramIndex(m, pt.Text); ai >= 0 {
					out = append(out, stringize(argToks(args[ai]), use))
					bi++
					continue
				}
			}
		}

		if bt.Kind == TIdent && bt.Text == "__VA_OPT__" && m.IsVariadic &&
			bi+1 < len(body) && body[bi+1].Kind == TPunct && body[bi+1].Punct == PLparen {
			depth := 1
			k := bi + 2
			for k < len(body) && depth > 0 {
				if body[k].Kind == TPunct && body[k].Punct == PLparen {
					depth++
				} else if body[k].Kind == TPunct && body[k].Punct == PRparen {
					depth--
					if depth == 0 {
						break
					}
				}
				k++
			}
			inner := body[bi+2 : min(k, len(body))]
			empty := true
			for _, a := range vaArgs {
				if len(a) > 0 {
					empty = false
					break
				}
			}
			if !empty {
				innerM := &ppMacro{Name: "(va-opt)", Body: inner}
				out = append(out, pp.subst(innerM, args, useHide, use)...)
			}
			bi = k
			continue
		}

		if bt.Kind == TPunct && bt.Punct == PHashAt {
			var right []Tok
			if bi+1 < len(body) {
				nt := body[bi+1]
				right = nil
				if nt.Kind == TIdent {
					if ai := paramIndex(m, nt.Text); ai >= 0 {
						right = argToks(args[ai])
					} else if m.IsVariadic && nt.Text == m.VaName {
						right = joinVA(argTokss(vaArgs), use)
					}
				}
				if right == nil {
					right = []Tok{nt}
				}
				bi++
			}
			if len(out) > 0 && len(right) > 0 {
				l := out[len(out)-1]
				out[len(out)-1] = pasteTok(l, right[0], use)
				out = append(out, right[1:]...)
			} else if len(right) > 0 {
				out = append(out, right...)
			} else if len(out) == 0 {

			}
			continue
		}

		if bt.Kind == TIdent {
			if ai := paramIndex(m, bt.Text); ai >= 0 {
				out = append(out, pp.expandETS(args[ai])...)
				continue
			}
			if m.IsVariadic && bt.Text == m.VaName {
				out = append(out, joinVA(argTokss(vaArgs), use)...)
				continue
			}
		}
		out = append(out, bt)
	}

	for k := range out {
		o := out[k]
		o.File = use.File
		o.Off = use.Off
		o.End = use.End
		o.OrigOff = use.OrigOff
		o.Line = use.Line
		o.Col = use.Col
		o.SL = use.SL
		out[k] = o
	}
	return out
}

func argToks(a []expTok) []Tok {
	if len(a) == 0 {
		return nil
	}
	out := make([]Tok, len(a))
	for i, et := range a {
		out[i] = et.t
	}
	return out
}

func argTokss(aa [][]expTok) [][]Tok {
	out := make([][]Tok, len(aa))
	for i, a := range aa {
		out[i] = argToks(a)
	}
	return out
}

func joinVA(vaArgs [][]Tok, use Tok) []Tok {
	var joined []Tok
	for k, a := range vaArgs {
		if k > 0 {
			comma := use
			comma.Kind = TPunct
			comma.Punct = PComma
			comma.Text = ","
			joined = append(joined, comma)
		}
		joined = append(joined, a...)
	}
	return joined
}

func paramIndex(m *ppMacro, name string) int {
	for i, p := range m.Params {
		if p == name {
			return i
		}
	}
	return -1
}

func stringize(arg []Tok, use Tok) Tok {
	var b strings.Builder
	b.WriteByte('"')
	for i, t := range arg {
		if i > 0 && t.WSBefore {
			b.WriteByte(' ')
		}
		s := t.Text
		if t.Kind == TStr {
			s = strings.ReplaceAll(s, `\`, `\\`)
			s = strings.ReplaceAll(s, `"`, `\"`)
		} else if t.Kind == TChar {
			s = strings.ReplaceAll(s, `\`, `\\`)
		}
		b.WriteString(s)
	}
	b.WriteByte('"')
	tk := use
	tk.Kind = TStr
	tk.Text = b.String()
	tk.Punct = 0
	return tk
}

func pasteTok(l, r, use Tok) Tok {
	txt := l.Text + r.Text
	nk := uint8(TIdent)
	np := uint8(0)
	if txt == "" {

	} else if isDigit(txt[0]) || (txt[0] == '.' && len(txt) > 1 && isDigit(txt[1])) {
		nk = TNumber
	} else if c23IsIdentStart(txt[0]) {
		nk = TIdent
	} else if code, ok := punctIndex[txt]; ok {
		nk = TPunct
		np = code
	}
	tk := use
	tk.Kind = nk
	tk.Text = txt
	tk.Punct = np
	return tk
}

func (pp *preprocessor) nativeBuiltin(t Tok) (Tok, bool) {
	switch t.Text {
	case "__LINE__":
		nt := t
		nt.Kind = TNumber
		v := int64(t.Line) + pp.lineDelta
		if v < 1 {
			v = 1
		}
		nt.Text = strconv.FormatInt(v, 10)
		return nt, true
	case "__FILE__":
		nt := t
		nt.Kind = TStr
		nt.Text = strconv.Quote(pp.fileName)
		return nt, true
	}
	return t, false
}

func (pp *preprocessor) evalCond(src *fileTokSrc, toks []Tok, line int32) int64 {
	pre := pp.resolveCondOps(src, toks, line)
	ex := pp.expand(pre)
	v, ok := pp.evalExpr(ex, line)
	if !ok {
		pp.errf(line, "bad #if expression")
		return 0
	}
	return v
}

func (pp *preprocessor) resolveCondOps(src *fileTokSrc, toks []Tok, line int32) []Tok {
	out := make([]Tok, 0, len(toks))
	for i := 0; i < len(toks); i++ {
		t := toks[i]
		if t.Kind != TIdent {
			out = append(out, t)
			continue
		}
		switch t.Text {
		case "defined":
			name := ""
			j := i + 1
			if j < len(toks) && toks[j].Kind == TPunct && toks[j].Punct == PLparen {
				j++
				if j < len(toks) && toks[j].Kind == TIdent {
					name = toks[j].Text
					j++
				}
				if j < len(toks) && toks[j].Kind == TPunct && toks[j].Punct == PRparen {
					j++
				}
			} else if j < len(toks) && toks[j].Kind == TIdent {
				name = toks[j].Text
				j++
			}
			if name == "" {
				pp.errf(line, "bad defined()")
				return out
			}
			_, def := pp.macros[name]
			nt := t
			nt.Kind = TNumber
			nt.Text = btoa(def)
			out = append(out, nt)
			i = j - 1
			continue
		case "__has_include", "__has_include_next", "__has_embed":
			j := i + 1
			if !(j < len(toks) && toks[j].Kind == TPunct && toks[j].Punct == PLparen) {
				out = append(out, t)
				continue
			}

			depth := 1
			k := j + 1
			var inner []Tok
			for k < len(toks) && depth > 0 {
				if toks[k].Kind == TPunct && toks[k].Punct == PLparen {
					depth++
				} else if toks[k].Kind == TPunct && toks[k].Punct == PRparen {
					depth--
					if depth == 0 {
						break
					}
				}
				inner = append(inner, toks[k])
				k++
			}
			val := int64(0)
			if len(inner) > 0 {
				tgt := ""
				sys := false
				if inner[0].Kind == THeader {
					tgt = strings.TrimSuffix(strings.TrimPrefix(inner[0].Text, "<"), ">")
					sys = true
				} else if inner[0].Kind == TStr {
					tgt = dequote(inner[0].Text)
				} else {

					ex := pp.expand(inner)
					if len(ex) > 0 {
						if ex[0].Kind == THeader {
							tgt = strings.TrimSuffix(strings.TrimPrefix(ex[0].Text, "<"), ">")
							sys = true
						} else if ex[0].Kind == TStr {
							tgt = dequote(ex[0].Text)
						}
					}
				}
				if t.Text == "__has_c_attribute" {
					if len(inner) > 0 && inner[0].Kind == TIdent && isC23AttrName(inner[0].Text) {
						val = 202003
					}
				} else if t.Text == "__has_embed" {
					if r := pp.resolveInclude(src, tgt, sys); r != "" {
						val = 1
					}
				} else {
					if r := pp.resolveInclude(src, tgt, sys); r != "" {
						val = 1
					}
				}
			}
			nt := t
			nt.Kind = TNumber
			nt.Text = strconv.FormatInt(val, 10)
			out = append(out, nt)
			i = k
			continue
		default:
			out = append(out, t)
		}
	}
	return out
}

func btoa(b bool) string {
	if b {
		return "1"
	}
	return "0"
}

func (pp *preprocessor) evalExpr(toks []Tok, line int32) (int64, bool) {
	e := &ev{toks: toks, pp: pp, line: line}
	v := e.cond()
	if e.bad || e.pos < len(e.toks) && e.toks[e.pos].Kind != TEOF {

	}
	if e.bad {
		return 0, false
	}
	return v, true
}

type ev struct {
	toks []Tok
	pp   *preprocessor
	line int32
	pos  int
	bad  bool
}

func (e *ev) peek() Tok {
	if e.pos < len(e.toks) {
		return e.toks[e.pos]
	}
	return Tok{Kind: TEOF}
}

func (e *ev) acceptPunct(p uint8) bool {
	t := e.peek()
	if t.Kind == TPunct && t.Punct == p {
		e.pos++
		return true
	}
	return false
}

func (e *ev) cond() int64 {
	c := e.logor()
	if e.acceptPunct(PTerse) {
		a := e.cond()
		if e.acceptPunct(PColon) {
			b := e.cond()
			if c != 0 {
				return a
			}
			return b
		}
		e.bad = true
		return 0
	}
	return c
}

func (e *ev) binops(level int) int64 {

	return 0
}

func (e *ev) logor() int64 {
	v := e.logand()
	for {
		if e.acceptPunct(PPipePip) {
			r := e.logand()
			if v != 0 || r != 0 {
				v = 1
			} else {
				v = 0
			}
			continue
		}
		return v
	}
}

func (e *ev) logand() int64 {
	v := e.bitor()
	for {
		if e.acceptPunct(PAmpAmp) {
			r := e.bitor()
			if v != 0 && r != 0 {
				v = 1
			} else {
				v = 0
			}
			continue
		}
		return v
	}
}

func (e *ev) bitor() int64 {
	v := e.bitxor()
	for e.acceptPunct(PPipe) {
		v |= e.bitxor()
	}
	return v
}

func (e *ev) bitxor() int64 {
	v := e.bitand()
	for e.acceptPunct(PCaret) {
		v ^= e.bitand()
	}
	return v
}

func (e *ev) bitand() int64 {
	v := e.equality()
	for e.acceptPunct(PAmp) {
		v &= e.equality()
	}
	return v
}

func (e *ev) equality() int64 {
	v := e.relational()
	for {
		if e.acceptPunct(mustPunct("==")) {
			if v == e.relational() {
				v = 1
			} else {
				v = 0
			}
			continue
		}
		if e.acceptPunct(mustPunct("!=")) {
			if v != e.relational() {
				v = 1
			} else {
				v = 0
			}
			continue
		}
		return v
	}
}

func (e *ev) relational() int64 {
	v := e.shift()
	for {
		if e.acceptPunct(PLe) {
			if v <= e.shift() {
				v = 1
			} else {
				v = 0
			}
			continue
		}
		if e.acceptPunct(mustPunct(">=")) {
			if v >= e.shift() {
				v = 1
			} else {
				v = 0
			}
			continue
		}
		if e.acceptPunct(PLt) {
			if v < e.shift() {
				v = 1
			} else {
				v = 0
			}
			continue
		}
		if e.acceptPunct(PGt) {
			if v > e.shift() {
				v = 1
			} else {
				v = 0
			}
			continue
		}
		return v
	}
}

func (e *ev) shift() int64 {
	v := e.additive()
	for {
		if e.acceptPunct(PLsh) {
			v <<= uint64(e.additive())
			continue
		}
		if e.acceptPunct(PRsh) {
			v >>= uint64(e.additive())
			continue
		}
		return v
	}
}

func (e *ev) additive() int64 {
	v := e.mult()
	for {
		if e.acceptPunct(PPlus) {
			v += e.mult()
			continue
		}
		if e.acceptPunct(PMinus) {
			v -= e.mult()
			continue
		}
		return v
	}
}

func (e *ev) mult() int64 {
	v := e.unary()
	for {
		if e.acceptPunct(PStar) {
			v *= e.unary()
			continue
		}
		if e.acceptPunct(PSlash) {
			d := e.unary()
			if d == 0 {
				e.pp.errf(e.line, "division by zero in #if")
				e.bad = true
				return 0
			}
			v /= d
			continue
		}
		if e.acceptPunct(PMod) {
			d := e.unary()
			if d == 0 {
				e.pp.errf(e.line, "mod by zero in #if")
				e.bad = true
				return 0
			}
			v %= d
			continue
		}
		return v
	}
}

func (e *ev) unary() int64 {
	if e.acceptPunct(PBang) {
		if e.unary() != 0 {
			return 0
		}
		return 1
	}
	if e.acceptPunct(PTilde) {
		return ^e.unary()
	}
	if e.acceptPunct(PMinus) {
		return -e.unary()
	}
	if e.acceptPunct(PPlus) {
		return e.unary()
	}
	return e.primary()
}

func (e *ev) primary() int64 {
	t := e.peek()
	switch t.Kind {
	case TNumber:
		e.pos++
		if v, ok := parseCInt(t.Text); ok {
			return v
		}
		e.pp.errf(e.line, "bad number in #if: "+t.Text)
		e.bad = true
		return 0
	case TChar:
		e.pos++
		return charValue(t.Text)
	case TIdent:
		e.pos++
		switch t.Text {
		case "true":
			return 1
		case "false":
			return 0
		}
		return 0
	case TPunct:
		if t.Punct == PLparen {
			e.pos++
			v := e.cond()
			if !e.acceptPunct(PRparen) {
				e.bad = true
				return 0
			}
			return v
		}
	}
	e.bad = true
	return 0
}

func parseCInt(s string) (int64, bool) {
	s = strings.ReplaceAll(s, "'", "")
	s = stripNumSuffix(s)
	if s == "" {
		return 0, false
	}
	neg := false
	base := 10
	body := s
	if strings.HasPrefix(body, "+") {
		body = body[1:]
	} else if strings.HasPrefix(body, "-") {
		neg = true
		body = body[1:]
	}
	_ = base
	if strings.HasPrefix(body, "0x") || strings.HasPrefix(body, "0X") {
		base = 16
		body = body[2:]
	} else if strings.HasPrefix(body, "0b") || strings.HasPrefix(body, "0B") {
		base = 2
		body = body[2:]
	} else if len(body) > 1 && body[0] == '0' {
		base = 8
		body = body[1:]
	}
	var v int64
	for i := 0; i < len(body); i++ {
		var d int64
		c := body[i]
		switch {
		case c >= '0' && c <= '9':
			d = int64(c - '0')
		case c >= 'a' && c <= 'z':
			d = int64(c-'a') + 10
		case c >= 'A' && c <= 'Z':
			d = int64(c-'A') + 10
		default:
			return 0, false
		}
		if d >= int64(base) {
			return 0, false
		}
		v = v*int64(base) + d
	}
	if neg {
		v = -v
	}
	return v, true
}

func charValue(s string) int64 {
	if len(s) < 2 {
		return 0
	}

	if s[0] == '\'' {
		s = s[1:]
	} else if s[0] == 'u' && len(s) > 1 && s[1] == '8' {
		s = s[3:]
	} else if s[0] == 'u' || s[0] == 'U' || s[0] == 'L' {
		s = s[2:]
	}
	s = strings.TrimSuffix(s, "'")
	var v int64
	i := 0
	for i < len(s) {
		c, adv := readCharVal(s, i)
		v = v<<8 | (c & 0xFF)
		i += adv
	}
	return v
}

func readCharVal(s string, i int) (int64, int) {
	if s[i] == '\\' && i+1 < len(s) {
		switch s[i+1] {
		case 'n':
			return 10, 2
		case 't':
			return 9, 2
		case 'r':
			return 13, 2
		case 'a':
			return 7, 2
		case 'b':
			return 8, 2
		case 'f':
			return 12, 2
		case 'v':
			return 11, 2
		case '\\':
			return '\\', 2
		case '\'':
			return '\'', 2
		case '"':
			return '"', 2
		case '?':
			return '?', 2
		case 'e':
			return 27, 2
		case 'x':
			v := int64(0)
			j := i + 2
			for j < len(s) && isHex(s[j]) {
				v = v*16 + hexVal(s[j])
				j++
			}
			return v, j - i
		case 'u', 'U':
			nd := 4
			if s[i+1] == 'U' {
				nd = 8
			}
			v := int64(0)
			j := i + 2
			for k := 0; k < nd && j < len(s) && isHex(s[j]); k++ {
				v = v*16 + hexVal(s[j])
				j++
			}
			return v, j - i
		default:
			if s[i+1] >= '0' && s[i+1] <= '7' {
				v := int64(0)
				j := i + 1
				for k := 0; k < 3 && j < len(s) && s[j] >= '0' && s[j] <= '7'; k++ {
					v = v*8 + int64(s[j]-'0')
					j++
				}
				return v, j - i
			}
			return int64(s[i+1]), 2
		}
	}
	if s[i] < 0x80 {
		return int64(s[i]), 1
	}

	r := int64(s[i]) & 0x3F
	n := 1
	if s[i]&0xE0 == 0xC0 {
		n = 2
	} else if s[i]&0xF0 == 0xE0 {
		n = 3
	} else if s[i]&0xF8 == 0xF0 {
		n = 4
	}
	j := i + 1
	for k := 1; k < n && j < len(s); k++ {
		r = r<<6 | int64(s[j])&0x3F
		j++
	}
	return r, j - i
}

func hexVal(c byte) int64 {
	switch {
	case c >= '0' && c <= '9':
		return int64(c - '0')
	case c >= 'a' && c <= 'f':
		return int64(c-'a') + 10
	default:
		return int64(c-'A') + 10
	}
}

const (
	NBad = iota

	NTU
	NFuncDef
	NDecl
	NParam
	NKRDecl
	NStructSpec
	NUnionSpec
	NEnumSpec
	NField
	NEnumerator
	NTypeRef
	NStaticAssert

	NCompoundStmt
	NDeclStmt
	NExprStmt
	NIf
	NSwitch
	NCase
	NWhile
	NDo
	NFor
	NReturn
	NBreak
	NContinue
	NGoto
	NLabel
	NAsm

	NIdent
	NNumLit
	NCharLit
	NStrLit
	NBoolLit
	NNullPtr
	NCall
	NMember
	NIndex
	NPostfix
	NUnary
	NBinary
	NAssign
	NCond
	NComma
	NCast
	NSizeofT
	NSizeofE
	NAlignofT
	NGeneric
	NStmtExpr
	NParen
	NCompoundLit
	NVaArg
	NInitList
	NInitItem
)

const (
	FConst     = 1 << 0
	FVolatile  = 1 << 1
	FStatic    = 1 << 2
	FExtern    = 1 << 3
	FInline    = 1 << 4
	FAuto      = 1 << 5
	FRegister  = 1 << 6
	FThreadLoc = 1 << 7
	FConstexpr = 1 << 8
	FRestrict  = 1 << 9
	FAtomic    = 1 << 10
	FVariadic  = 1 << 11
	FNoreturn  = 1 << 12
	FKRStyle   = 1 << 13
	FHasInit   = 1 << 14
	FAttrHere  = 1 << 15
)

type Node struct {
	Kind       uint16
	Flags      uint16
	A, B, C, D uint32
	File       uint32
	Off, End   int32
	Line, Col  int32
}

type FuncDef struct {
	NameIdx      uint32
	SigIdx       uint32
	RetIdx       uint32
	Param0       uint32
	NParams      uint32
	Body         uint32
	LineEnd      int32
	Storage      uint16
	Variadic     bool
	KR           bool
	Attr0, NAttr uint32
}

type DeclNode struct {
	NameIdx  uint32
	TypeIdx  uint32
	Typename uint32
	Bitfield int32
	ArrayLen int32
	Ptr      int32
	Init     uint32
	Storage  uint16
	Kind     uint8
	Line     int32
}

type ParamD struct {
	NameIdx  uint32
	TypeIdx  uint32
	Ptr      int32
	ArrayLen int32
	Storage  uint16
	Variadic bool
	Unnamed  bool
	IsConst  bool
	Line     int32
}

type TagD struct {
	NameIdx       uint32
	Tag           string
	Child0        uint32
	NChild        uint32
	UnderlyingIdx uint32
	HasUnderlying bool
	Defined       bool
	Line          int32
	LineEnd       int32
}

type FieldD struct {
	NameIdx    uint32
	TypeIdx    uint32
	Ptr        int32
	PtrTypeIdx uint32
	ArrayLen   int32
	Bitfield   int32
	IsFnptr    bool
	Depth      int32
	IsConst    bool
	Line       int32
}

type EnumD struct {
	NameIdx  uint32
	ValueIdx uint32
	HasValue bool
	Line     int32
}

type TypeD struct {
	TextIdx  uint32
	Ptr      int32
	Array    bool
	ArrayLen int32
	IsFn     bool
}

type InitD struct {
	FieldIdx uint32
	Index    int64
	HasIndex bool
	IsList   bool
}

type GenericAssoc struct {
	TypeIdx   uint32
	IsDefault bool
	Expr      uint32
}

type AttrRec struct {
	Name string
	Args string
	Line int32

	Off, End int32
}

type FileAST struct {
	Names  []string
	nameIx map[string]uint32

	Nodes []Node

	Funcs  []FuncDef
	Decls  []DeclNode
	Params []ParamD
	Tags   []TagD
	Fields []FieldD
	Enums  []EnumD
	Types  []TypeD
	Inits  []InitD
	Assocs []GenericAssoc

	Attrs []AttrRec

	SrcOff, SrcEnd []uint32
}

func (fa *FileAST) intern(s string) uint32 {
	if fa.nameIx == nil {
		fa.nameIx = map[string]uint32{}
	}
	if ix, ok := fa.nameIx[s]; ok {
		return ix
	}
	fa.Names = append(fa.Names, s)
	ix := uint32(len(fa.Names))
	fa.nameIx[s] = ix
	return ix
}

func (fa *FileAST) name(ix uint32) string {
	if ix == 0 || int(ix) > len(fa.Names) {
		return ""
	}
	return fa.Names[ix-1]
}

func (fa *FileAST) addNode(n Node) uint32 {
	fa.Nodes = append(fa.Nodes, n)
	return uint32(len(fa.Nodes)) - 1
}

func (fa *FileAST) kids(i uint32) (uint32, uint32) {
	n := &fa.Nodes[i]
	return n.A, n.B
}

func (fa *FileAST) span(i uint32) (int32, int32) {
	return fa.Nodes[i].Off, fa.Nodes[i].End
}

type parseError struct {
	line int32
	file uint32
	msg  string
}

type scope struct {
	typedefs   map[string]bool
	tags       map[string]bool
	enumConsts map[string]bool
}

type parser struct {
	fa      *FileAST
	toks    []Tok
	pos     int
	errs    *[]parseError
	srcs    map[uint32][]byte
	fileID  uint32
	scopes  []*scope
	nErrors int
	stop    bool

	funcDepth int
	loopDepth int
	krMode    bool

	deferredTypedefs []defName
	deferredTags     []defName
	deferredConsts   []defName
}

type defName struct {
	name  string
	scope int
}

func newParser(fa *FileAST, toks []Tok, srcs map[uint32][]byte, fileID uint32, errs *[]parseError) *parser {
	p := &parser{fa: fa, toks: toks, srcs: srcs, fileID: fileID, errs: errs}
	p.pushScope()
	return p
}

func (p *parser) srcOf(t Tok) []byte {
	if b, ok := p.srcs[uint32(t.File)]; ok {
		return b
	}
	if len(p.srcs) == 1 {
		for _, b := range p.srcs {
			return b
		}
	}
	return nil
}

func (p *parser) pushScope() {
	p.scopes = append(p.scopes, &scope{typedefs: map[string]bool{},
		tags: map[string]bool{}, enumConsts: map[string]bool{}})
}

func (p *parser) popScope() {
	if len(p.scopes) > 1 {
		p.scopes = p.scopes[:len(p.scopes)-1]
	}
}

func (p *parser) cur() Tok {
	if p.pos < len(p.toks) {
		return p.toks[p.pos]
	}
	return p.toks[len(p.toks)-1]
}

func (p *parser) peek(n int) Tok {
	if p.pos+n < len(p.toks) {
		return p.toks[p.pos+n]
	}
	return p.toks[len(p.toks)-1]
}

func (p *parser) eof() bool { return p.cur().Kind == TEOF }

func (p *parser) advance() Tok {
	t := p.cur()
	if p.pos < len(p.toks)-1 {
		p.pos++
	}
	return t
}

func (p *parser) atPunct(code uint8) bool {
	t := p.cur()
	return t.Kind == TPunct && t.Punct == code
}

func (p *parser) atIdent(s string) bool {
	t := p.cur()
	return t.Kind == TIdent && t.Text == s
}

func (p *parser) acceptPunct(code uint8) bool {
	if p.atPunct(code) {
		p.advance()
		return true
	}
	return false
}

func (p *parser) acceptIdent(s string) bool {
	if p.atIdent(s) {
		p.advance()
		return true
	}
	return false
}

func (p *parser) errf(t Tok, msg string) {
	if p.errs != nil && len(*p.errs) < 4096 {
		*p.errs = append(*p.errs, parseError{line: t.Line, file: uint32(t.File), msg: msg})
	}
	p.nErrors++
}

func (p *parser) syncTo(t Tok, what string) {
	p.errf(t, "parse error near '"+t.Text+"' ("+what+"); syncing")
	depth := 0
	line := t.SL
	for !p.eof() {
		c := p.cur()
		if c.Kind == TPunct {
			switch c.Punct {
			case PLbrace:
				depth++
			case PRbrace:
				if depth == 0 {
					return
				}
				depth--
			case PSemi:
				if depth == 0 {
					p.advance()
					return
				}
			}
		}
		if c.SL > line && depth == 0 {
			return
		}
		p.advance()
	}
}

func (p *parser) expectPunct(code uint8, what string) bool {
	if p.acceptPunct(code) {
		return true
	}
	p.errf(p.cur(), "expected '"+punctTable[code]+"' "+what)
	return false
}

func (p *parser) closeParamList() {
	if p.acceptPunct(PRparen) {
		return
	}
	p.errf(p.cur(), "expected ')' to close parameter list; recovering")
	depth := 0
	for !p.eof() {
		t := p.cur()
		if t.Kind == TPunct {
			switch t.Punct {
			case PLparen, PLbrack:
				depth++
			case PRparen, PRbrack:
				if depth == 0 && t.Punct == PRparen {
					p.advance()
					return
				}
				if depth > 0 {
					depth--
				}
			case PLbrace, PSemi:
				if depth == 0 {
					return
				}
			}
		}
		p.advance()
	}
}

var sysTypedefs = map[string]bool{
	"size_t": true, "ssize_t": true, "ptrdiff_t": true, "intptr_t": true,
	"uintptr_t": true, "int8_t": true, "int16_t": true, "int32_t": true,
	"int64_t": true, "uint8_t": true, "uint16_t": true, "uint32_t": true,
	"uint64_t": true, "int_least8_t": true, "int_least16_t": true,
	"int_least32_t": true, "int_least64_t": true, "uint_least8_t": true,
	"uint_least16_t": true, "uint_least32_t": true, "uint_least64_t": true,
	"int_fast8_t": true, "int_fast16_t": true, "int_fast32_t": true,
	"int_fast64_t": true, "uint_fast8_t": true, "uint_fast16_t": true,
	"uint_fast32_t": true, "uint_fast64_t": true, "intmax_t": true,
	"uintmax_t": true, "off_t": true, "time_t": true, "clock_t": true,
	"pid_t": true, "uid_t": true, "gid_t": true, "ino_t": true, "dev_t": true,
	"mode_t": true, "nlink_t": true, "blkcnt_t": true, "blksize_t": true,
	"socklen_t": true, "sa_family_t": true, "in_addr_t": true,
	"in_port_t": true, "useconds_t": true, "suseconds_t": true,
	"key_t": true, "id_t": true, "va_list": true, "FILE": true, "DIR": true,
	"fpos_t": true, "sigset_t": true, "siginfo_t": true, "regex_t": true,
	"regoff_t": true, "pthread_t": true, "pthread_mutex_t": true,
	"pthread_rwlock_t": true, "pthread_cond_t": true, "pthread_key_t": true,
	"pthread_once_t": true, "pthread_attr_t": true, "pthread_spinlock_t": true,
	"socket_t": true, "nfds_t": true, "speed_t": true, "tcflag_t": true,
	"cc_t": true, "wchar_t": true, "wint_t": true, "wctype_t": true,
	"char16_t": true, "char32_t": true, "max_align_t": true, "div_t": true,
	"ldiv_t": true, "lldiv_t": true, "tm": true, "timespec": true,
	"timeval": true, "stat": true, "stat64": true, "dirent": true,
	"rlim_t": true, "rlimit": true, "rlimit64": true, "stack_t": true,
	"ucontext_t": true, "errno_t": true, "rsize_t": true,
}

func (p *parser) isTypedefName(s string) bool {
	if sysTypedefs[s] {
		return true
	}
	for i := len(p.scopes) - 1; i >= 0; i-- {
		if p.scopes[i].typedefs[s] {
			return true
		}
	}
	return false
}

func (p *parser) addTypedef(name string) {
	p.scopes[len(p.scopes)-1].typedefs[name] = true
}

func (p *parser) addTag(name string) {
	p.scopes[len(p.scopes)-1].tags[name] = true
}

func (p *parser) addEnumConst(name string) {
	p.scopes[len(p.scopes)-1].enumConsts[name] = true
}

type spanMark struct{ pos int }

const (
	BVoid = iota
	BBool
	BChar
	BShort
	BInt
	BLong
	BLongLong
	BFloat
	BDouble
	BSigned
	BUnsigned
	BDecimal32
	BDecimal64
	BDecimal128
	BTypedef
	BStruct
	BUnion
	BEnum
	BTypeof
	BBitInt
	BAuto
	BNone
)

type tspecs struct {
	words                                 []string
	base                                  string
	kind                                  int
	tag                                   string
	tagNode                               uint32
	typedef                               string
	isTypedef                             bool
	hasBase                               bool
	constq, volatileq, restrictq, atomicq bool
	alignas                               bool
	storage                               uint16
	saw                                   bool
}

func (ts *tspecs) baseText() string {
	var b strings.Builder
	if ts.constq {
		b.WriteString("const ")
	}
	if ts.volatileq {
		b.WriteString("volatile ")
	}
	if ts.restrictq {
		b.WriteString("restrict ")
	}
	if ts.atomicq {
		b.WriteString("_Atomic ")
	}
	b.WriteString(ts.base)
	return strings.TrimRight(b.String(), " ")
}

func (p *parser) recordAttr(name, args string, line int32, off, end int32) {
	p.fa.Attrs = append(p.fa.Attrs, AttrRec{Name: name, Args: args, Line: line,
		Off: off, End: end})
}

func (p *parser) skipBalanced() (string, int32, int32) {
	if !p.atPunct(PLparen) {
		return "", 0, 0
	}
	startTok := p.advance()
	depth := 1
	var b strings.Builder
	first := startTok.Off
	for !p.eof() && depth > 0 {
		t := p.cur()
		if t.Kind == TPunct {
			switch t.Punct {
			case PLparen:
				depth++
			case PRparen:
				depth--
				if depth == 0 {
					end := t.End
					p.advance()
					return b.String(), first, end
				}

				p.advance()
				continue
			}
		}
		if b.Len() > 0 || t.Kind != TPunct || t.Punct != PLparen {
			if b.Len() > 0 && t.WSBefore {
				b.WriteByte(' ')
			}
			b.WriteString(t.Text)
		}
		p.advance()
	}
	return b.String(), first, startTok.End
}

func (p *parser) parseAttributes() {
	for {
		t := p.cur()
		if t.Kind == TPunct && t.Punct == mustPunct("[") &&
			p.peek(1).Kind == TPunct && p.peek(1).Punct == mustPunct("[") {
			p.advance()
			p.advance()
			depth := 2
			var name, args strings.Builder
			gotName := false
			scoped := false
			for !p.eof() && depth > 0 {
				c := p.cur()
				if c.Kind == TPunct && c.Punct == mustPunct("[") {
					depth++
				} else if c.Kind == TPunct && c.Punct == mustPunct("]") {
					depth--
					p.advance()
					continue
				}
				if depth == 2 {
					if c.Kind == TIdent {
						if gotName && !scoped {
							if args.Len() > 0 && c.WSBefore {
								args.WriteByte(' ')
							}
							args.WriteString(c.Text)
						} else {
							name.WriteString(c.Text)
							gotName = true
							scoped = false
						}
					} else if c.Kind == TPunct {

						if c.Punct == PColon && gotName && args.Len() == 0 &&
							p.peek(1).Kind == TPunct && p.peek(1).Punct == PColon {
							name.WriteString("::")
							scoped = true
							p.advance()
							p.advance()
							continue
						}
						if args.Len() > 0 || gotName {
							args.WriteString(c.Text)
						}
					} else {
						args.WriteString(c.Text)
					}
				}
				p.advance()
			}

			if args.Len() > 0 {
				p.recordAttr(name.String(), args.String(), t.Line, t.Off, t.End)
			} else {
				p.recordAttr(name.String(), "", t.Line, t.Off, t.End)
			}
			continue
		}
		if t.Kind == TIdent && (t.Text == "__attribute__" || t.Text == "__attribute") {
			p.advance()
			args, off, end := p.skipBalanced()
			p.recordAttr("__attribute__", args, t.Line, off, end)
			continue
		}
		return
	}
}

func (p *parser) skipAsm() {

	for p.atIdent("asm") || p.atIdent("__asm__") || p.atIdent("__asm") ||
		p.atIdent("volatile") || p.atIdent("__volatile__") || p.atIdent("inline") ||
		p.atIdent("goto") {
		name := p.cur()
		p.advance()
		if p.atPunct(PLparen) {
			_, off, end := p.skipBalanced()
			p.recordAttr(name.Text, asmText(p.srcOf(name), off, end), name.Line, off, end)
		}
	}
}

func asmText(src []byte, off, end int32) string {
	if int(off) < len(src) && int(end) <= len(src) && off < end {
		return squeeze(string(src[off:end]), "")
	}
	return ""
}

func (p *parser) parseDeclSpecs() tspecs {
	var ts tspecs
	ts.kind = BNone
	for !p.eof() {
		t := p.cur()
		if t.Kind != TIdent && !(t.Kind == TPunct && (t.Punct == mustPunct("[") || t.Punct == mustPunct("]"))) {
			if t.Kind != TIdent {

				break
			}
		}
		if t.Kind != TIdent {
			break
		}
		switch t.Text {

		case "typedef":
			ts.storage |= 0
			ts.saw = true
			ts.typedef = "typedef"
			ts.isTypedef = true
			p.advance()
			continue
		case "extern":
			ts.storage |= FExtern
			ts.saw = true
			p.advance()
			continue
		case "static":
			ts.storage |= FStatic
			ts.saw = true
			p.advance()
			continue
		case "auto":
			ts.storage |= FAuto
			ts.saw = true
			ts.kind = BAuto
			ts.base = "auto"
			ts.hasBase = true
			p.advance()
			continue
		case "register":
			ts.storage |= FRegister
			ts.saw = true
			p.advance()
			continue
		case "thread_local", "_Thread_local", "__thread":
			ts.storage |= FThreadLoc
			ts.saw = true
			p.advance()
			continue
		case "constexpr":
			ts.storage |= FConstexpr
			ts.saw = true
			p.advance()
			continue

		case "inline", "__inline", "__inline__":
			ts.storage |= FInline
			ts.saw = true
			p.advance()
			continue
		case "_Noreturn", "noreturn":
			ts.storage |= FNoreturn
			ts.saw = true
			p.advance()
			continue

		case "const", "__const", "__const__":
			ts.constq = true
			ts.saw = true
			p.advance()
			continue
		case "volatile", "__volatile", "__volatile__":
			ts.volatileq = true
			ts.saw = true
			p.advance()
			continue
		case "restrict", "__restrict", "__restrict__":
			ts.restrictq = true
			ts.saw = true
			p.advance()
			continue
		case "_Atomic":

			if p.peek(1).Kind == TPunct && p.peek(1).Punct == PLparen {
				p.advance()
				p.advance()
				inner := p.parseTypeName()
				p.expectPunct(PRparen, "after _Atomic(")
				ts.base = "_Atomic(" + inner.text + ")"
				ts.kind = BTypeof
				ts.hasBase = true
				ts.saw = true
				continue
			}
			ts.atomicq = true
			ts.saw = true
			p.advance()
			continue
		case "alignas", "_Alignas":
			p.advance()
			p.skipBalanced()
			ts.alignas = true
			ts.saw = true
			continue
		case "__extension__":
			p.advance()
			continue
		case "__attribute__", "__attribute":
			p.advance()
			args, aoff, aend := p.skipBalanced()
			p.recordAttr("__attribute__", args, t.Line, aoff, aend)
			continue
		case "asm", "__asm", "__asm__":
			p.advance()
			p.skipBalanced()
			continue

		case "void":
			ts.words = append(ts.words, "void")
			ts.base = joinWords(ts.words)
			ts.kind = BVoid
			ts.hasBase = true
			ts.saw = true
			p.advance()
			continue
		case "_Bool", "bool":
			ts.words = append(ts.words, "_Bool")
			ts.base = joinWords(ts.words)
			ts.kind = BBool
			ts.hasBase = true
			ts.saw = true
			p.advance()
			continue
		case "char":
			ts.words = append(ts.words, "char")
			ts.base = joinWords(ts.words)
			ts.kind = BChar
			ts.hasBase = true
			ts.saw = true
			p.advance()
			continue
		case "short":
			ts.words = append(ts.words, "short")
			ts.base = joinWords(ts.words)
			ts.kind = BShort
			ts.hasBase = true
			ts.saw = true
			p.advance()
			continue
		case "int":
			ts.words = append(ts.words, "int")
			ts.base = joinWords(ts.words)
			if ts.kind == BNone {
				ts.kind = BInt
			}
			ts.hasBase = true
			ts.saw = true
			p.advance()
			continue
		case "long":
			if len(ts.words) > 0 && ts.words[len(ts.words)-1] == "long" {
				ts.words[len(ts.words)-1] = "long long"
				ts.kind = BLongLong
			} else {
				ts.words = append(ts.words, "long")
				ts.kind = BLong
			}
			ts.base = joinWords(ts.words)
			ts.hasBase = true
			ts.saw = true
			p.advance()
			continue
		case "float":
			ts.words = append(ts.words, "float")
			ts.base = joinWords(ts.words)
			ts.kind = BFloat
			ts.hasBase = true
			ts.saw = true
			p.advance()
			continue
		case "double":
			ts.words = append(ts.words, "double")
			ts.base = joinWords(ts.words)
			ts.kind = BDouble
			ts.hasBase = true
			ts.saw = true
			p.advance()
			continue
		case "signed", "__signed", "__signed__":
			ts.words = append(ts.words, "signed")
			ts.base = joinWords(ts.words)
			ts.saw = true
			p.advance()
			continue
		case "unsigned":
			ts.words = append(ts.words, "unsigned")
			ts.base = joinWords(ts.words)
			ts.kind = BSigned
			ts.hasBase = true
			ts.saw = true
			p.advance()
			continue
		case "_Decimal32":
			ts.base = "_Decimal32"
			ts.kind = BDecimal32
			ts.hasBase = true
			ts.saw = true
			p.advance()
			continue
		case "_Decimal64":
			ts.base = "_Decimal64"
			ts.kind = BDecimal64
			ts.hasBase = true
			ts.saw = true
			p.advance()
			continue
		case "_Decimal128":
			ts.base = "_Decimal128"
			ts.kind = BDecimal128
			ts.hasBase = true
			ts.saw = true
			p.advance()
			continue
		case "_Complex", "_Imaginary":
			ts.words = append(ts.words, t.Text)
			ts.base = joinWords(ts.words)
			ts.saw = true
			p.advance()
			continue
		case "_BitInt":
			p.advance()
			p.expectPunct(PLparen, "after _BitInt")
			var w strings.Builder
			for !p.eof() && !p.atPunct(PRparen) {
				w.WriteString(p.cur().Text)
				p.advance()
			}
			p.expectPunct(PRparen, "after _BitInt width")
			ts.base = "_BitInt(" + w.String() + ")"
			ts.kind = BBitInt
			ts.hasBase = true
			ts.saw = true
			continue
		case "typeof", "typeof_unqual", "__typeof", "__typeof__":
			unqual := t.Text != "typeof" && t.Text != "__typeof__" && t.Text != "__typeof"
			p.advance()
			p.expectPunct(PLparen, "after typeof")
			text := "typeof("
			if p.isTypeStart() {
				tn := p.parseTypeName()
				text += tn.text
				p.expectPunct(PRparen, "to close typeof(")
			} else {

				depth := 1
				var b strings.Builder
				for !p.eof() && depth > 0 {
					c := p.cur()
					if c.Kind == TPunct {
						if c.Punct == PLparen {
							depth++
						} else if c.Punct == PRparen {
							depth--
							if depth == 0 {
								p.advance()
								break
							}
						}
					}
					if b.Len() > 0 && c.WSBefore {
						b.WriteByte(' ')
					}
					b.WriteString(c.Text)
					p.advance()
				}
				text += b.String()
			}
			if unqual {
				text = strings.Replace(text, "typeof(", "typeof_unqual(", 1)
			}
			text += ")"
			ts.base = text
			ts.kind = BTypeof
			ts.hasBase = true
			ts.saw = true
			continue
		case "struct", "union", "enum":
			p.advance()
			node := p.parseTagSpec(t.Text)
			ts.tagNode = node
			ts.kind = map[string]int{"struct": BStruct, "union": BUnion, "enum": BEnum}[t.Text]
			td := p.fa.Tags[p.fa.Nodes[node].A-1]
			_ = td
			ts.base = t.Text
			if td.NameIdx != 0 {
				ts.base += " " + p.fa.name(td.NameIdx)
			}
			if td.HasUnderlying {
				ts.base += " : " + p.fa.name(td.UnderlyingIdx)
			}
			ts.tag = t.Text
			ts.hasBase = true
			ts.saw = true
			continue
		default:
			if p.isTypedefName(t.Text) {
				ts.base = t.Text
				ts.kind = BTypedef
				ts.typedef = t.Text
				ts.hasBase = true
				ts.saw = true
				p.advance()
				continue
			}

			if !ts.hasBase && p.unknownTypeFollows() {

				ts.words = append(ts.words, t.Text)
				ts.base = joinWords(ts.words)
				ts.kind = BTypedef
				ts.typedef = t.Text
				ts.hasBase = true
				ts.saw = true
				p.advance()
				continue
			}
			if ts.saw {
				return ts
			}
			return ts
		}
	}

	p.parseAttributes()
	return ts
}

func joinWords(ws []string) string {
	return strings.Join(ws, " ")
}

func (p *parser) unknownTypeFollows() bool {
	if p.krMode {
		return false
	}
	nx := p.peek(1)
	switch nx.Kind {
	case TIdent:
		switch nx.Text {
		case "__attribute__", "__attribute", "__asm__", "__asm", "asm",
			"__extension__":
			return false
		}

		switch nx.Text {
		case "const", "volatile", "restrict", "_Atomic", "struct", "union",
			"enum", "void", "char", "short", "int", "long", "float", "double",
			"signed", "unsigned", "_Bool", "bool", "_Complex", "_Imaginary",
			"typeof", "typeof_unqual", "_BitInt", "_Decimal32", "_Decimal64",
			"_Decimal128", "constexpr", "alignas", "_Alignas":
			return true
		}
		return !isKeyword(nx.Text)
	case TPunct:
		switch nx.Punct {
		case PStar, PLbrack, PSemi, PEq, PLparen:
			return true
		}
	}
	return false
}

func (p *parser) parseTagSpec(kind string) uint32 {
	kwTok := p.cur()
	p.parseAttributes()
	node := uint32(0)
	td := TagD{Tag: kind}
	if p.cur().Kind == TIdent {
		nm := p.advance()
		td.NameIdx = p.fa.intern(nm.Text)
		td.Line = int32(nm.Line)
	}

	if kind == "enum" && p.atPunct(PColon) {
		p.advance()
		tn := p.parseTypeName()
		td.UnderlyingIdx = p.fa.intern(tn.text)
		td.HasUnderlying = true
	}
	if p.atPunct(PLbrace) {
		ob := p.advance()
		td.Defined = true
		if td.Line == 0 {
			td.Line = int32(ob.Line)
		}

		child0 := uint32(len(p.fa.Nodes))
		if kind == "enum" {
			for !p.eof() && !p.atPunct(PRbrace) {
				p.parseAttributes()
				if p.atPunct(PRbrace) {
					break
				}
				if p.cur().Kind != TIdent {
					p.errf(p.cur(), "expected enumerator name")
					p.syncTo(p.cur(), "enumerator")
					if p.atPunct(PComma) {
						p.advance()
					}
					continue
				}
				nm := p.advance()
				ed := EnumD{NameIdx: p.fa.intern(nm.Text), Line: nm.Line}
				if p.acceptPunct(PEq) {
					vs, ve := p.exprSpan()
					if ve > vs {
						ed.HasValue = true
						ed.ValueIdx = p.fa.intern(rawText(p.srcOf(nm), vs, ve))
					}
				}
				en := Node{Kind: NEnumerator, File: uint32(nm.File), Line: nm.Line,
					Col: nm.Col, Off: nm.Off, End: nm.End}
				if ed.HasValue {
					en.Flags = 1
				}
				p.fa.Enums = append(p.fa.Enums, ed)
				en.A = uint32(len(p.fa.Enums))
				en.B = ed.ValueIdx
				p.addNode(en)
				p.addEnumConst(p.fa.name(ed.NameIdx))
				if !p.acceptPunct(PComma) {
					break
				}
			}
			p.expectPunct(PRbrace, "to close enum")
			p.parseAttributes()
			td.Child0 = child0
			td.NChild = uint32(len(p.fa.Nodes)) - child0
			endTok := p.cur()
			td.LineEnd = endTok.Line
		} else {
			for !p.eof() && !p.atPunct(PRbrace) {
				p.parseMember(kind)
			}
			p.expectPunct(PRbrace, "to close "+kind)
			p.parseAttributes()
			td.Child0 = child0
			td.NChild = uint32(len(p.fa.Nodes)) - child0
			endTok := p.cur()
			td.LineEnd = endTok.Line
		}
	} else {
		td.LineEnd = td.Line
	}
	p.fa.Tags = append(p.fa.Tags, td)
	idx := uint32(len(p.fa.Tags))
	k := uint16(NStructSpec)
	switch kind {
	case "union":
		k = NUnionSpec
	case "enum":
		k = NEnumSpec
	}
	n := Node{Kind: k, A: idx, Off: 0, End: 0}
	if td.Line != 0 {
		n.Line = td.Line
	}
	n.File = uint32(kwTok.File)
	node = p.addNode(n)
	if td.NameIdx != 0 {
		p.addTag(p.fa.name(td.NameIdx))
	}
	return node
}

func (p *parser) parseMember(kind string) {
	t := p.cur()
	if p.atPunct(PSemi) {
		p.advance()
		return
	}
	if p.atIdent("_Static_assert") || p.atIdent("static_assert") {
		p.parseStaticAssert()
		return
	}
	specs := p.parseDeclSpecs()
	if !specs.saw {
		p.errf(t, "bad member declaration")
		p.syncTo(t, "member")
		return
	}

	if p.atPunct(PSemi) && (specs.kind == BStruct || specs.kind == BUnion) {
		p.advance()
		fd := FieldD{TypeIdx: p.fa.intern(specs.baseText()), PtrTypeIdx: p.fa.intern(specs.baseText()),
			Depth: int32(p.scopeDepth()), Line: t.Line}
		p.fa.Fields = append(p.fa.Fields, fd)
		n := Node{Kind: NField, A: uint32(len(p.fa.Fields)), File: uint32(t.File),
			Off: t.Off, End: t.End, Line: t.Line, Col: t.Col}
		p.addNode(n)
		return
	}
	for {
		p.parseAttributes()
		d := p.declarator(&specs, false)
		p.parseAttributes()
		bf := int32(0)
		if p.acceptPunct(PColon) {
			_, ve := p.condExprSpan()
			if ve > 0 {
				bf = -1
			}
		}

		fd := FieldD{
			TypeIdx:    p.fa.intern(specs.baseText()),
			Ptr:        int32(d.ptr),
			PtrTypeIdx: p.fa.intern(specs.baseText() + d.ptrStars()),
			ArrayLen:   arrayLenI(d),
			Bitfield:   bf,
			IsFnptr:    d.fnptr,
			Depth:      int32(d.depth),
			IsConst:    specs.constq,
			Line:       int32(t.Line),
		}
		if d.name != "" {
			fd.NameIdx = p.fa.intern(d.name)
		}
		p.fa.Fields = append(p.fa.Fields, fd)
		n := Node{Kind: NField, A: uint32(len(p.fa.Fields)), File: uint32(t.File),
			Off: t.Off, End: t.End, Line: t.Line, Col: t.Col}
		p.addNode(n)
		if p.acceptPunct(PComma) {
			continue
		}
		p.expectPunct(PSemi, "after member")
		break
	}
}

func (p *parser) scopeDepth() int { return len(p.scopes) }

func arrayLenI(d dcl) int32 {
	if !d.isArray {
		return 0
	}
	if d.arrayConst {
		return int32(d.arrayLen)
	}
	return -1
}

func rawText(src []byte, off, end int32) string {
	if int(off) <= len(src) && int(end) <= len(src) && off <= end {
		return squeeze(string(src[off:end]), "")
	}
	return ""
}

func (p *parser) parseStaticAssert() {
	t := p.advance()
	p.expectPunct(PLparen, "after _Static_assert")
	n := Node{Kind: NStaticAssert, Off: t.Off, Line: t.Line, Col: t.Col}
	child0 := uint32(len(p.fa.Nodes))
	if !p.atPunct(PRparen) {
		p.assignment()
	}
	if p.acceptPunct(PComma) {
		if p.cur().Kind == TStr {
			p.advance()
		}
	}
	p.expectPunct(PRparen, "to close _Static_assert")
	p.expectPunct(PSemi, "after _Static_assert")
	n.A = child0
	n.B = uint32(len(p.fa.Nodes)) - child0
	n.End = p.cur().End
	p.addNode(n)
}

func (p *parser) exprSpan() (int32, int32) {
	p.assignment()
	return p.lastSpan()
}

func (p *parser) condExprSpan() (int32, int32) {
	p.assignment()
	return p.lastSpan()
}

func (p *parser) lastSpan() (int32, int32) {
	if len(p.fa.Nodes) == 0 {
		return 0, 0
	}
	n := p.fa.Nodes[len(p.fa.Nodes)-1]
	return n.Off, n.End
}

type paramT struct {
	name     string
	typ      string
	ptr      int
	arrayLen int32
	isConst  bool
	variadic bool
	unnamed  bool
	line     int32
}

type dcl struct {
	name       string
	nameTok    Tok
	hasName    bool
	ptr        int
	isArray    bool
	arrayLen   int64
	arrayConst bool
	isFn       bool
	fnptr      bool
	parenName  bool
	params     []paramT
	variadic   bool
	kr         bool
	krNames    []string
	depth      int
	constq     bool
	volatileq  bool
}

func (d *dcl) ptrStars() string {
	s := ""
	for i := 0; i < d.ptr; i++ {
		s += " *"
	}
	return s
}

func (p *parser) skipDecorationIdents(specs *tspecs) {
	if specs == nil || !specs.saw || p.krMode {
		return
	}

	baseIsDecoration := false
	if specs.kind == BTypedef && specs.hasBase && !isKeyword(specs.base) &&
		!p.isTypedefName(specs.base) && c23IsIdentStart(specs.base[0]) &&
		!strings.ContainsAny(specs.base, " *([;,") {
		baseIsDecoration = true
	}
	for {
		t := p.cur()
		if t.Kind != TIdent || isKeyword(t.Text) || p.isTypedefName(t.Text) {
			return
		}
		n1 := p.peek(1)
		if n1.Kind != TIdent || isKeyword(n1.Text) {
			return
		}
		n2 := p.peek(2)
		if n2.Kind != TPunct {
			return
		}
		switch n2.Punct {
		case PLparen:
		case PComma, PRparen:

			if !baseIsDecoration {
				return
			}
		default:
			return
		}
		p.advance()
	}
}

func (p *parser) declarator(specs *tspecs, abstract bool) dcl {
	d := dcl{}
	for {
		p.parseAttributes()
		if !p.acceptPunct(PStar) {
			break
		}
		d.ptr++
		for {
			t := p.cur()
			if t.Kind != TIdent {
				break
			}
			switch t.Text {
			case "const", "__const", "__const__":
				d.constq = true
			case "volatile", "__volatile", "__volatile__":
				d.volatileq = true
			case "restrict", "__restrict", "__restrict__":
			case "_Atomic":
			default:
				goto ptrDone
			}
			p.advance()
		}
	ptrDone:
	}
	p.skipDecorationIdents(specs)
	d = p.directDeclarator(d, abstract)
	p.parseAttributes()

	p.skipDeclaratorAsm()
	return d
}

func (p *parser) skipDeclaratorAsm() {
	for p.atIdent("__asm__") || p.atIdent("__asm") || p.atIdent("asm") {
		p.advance()
		p.skipBalanced()
	}
}

func (p *parser) directDeclarator(d dcl, abstract bool) dcl {
	t := p.cur()
	switch {
	case t.Kind == TIdent && !p.atPunct(0):

		if !isKeyword(t.Text) {
			d.name = t.Text
			d.nameTok = t
			d.hasName = true
			p.advance()
		}
	case t.Kind == TPunct && t.Punct == PLparen:

		nx := p.peek(1)
		if abstract && parenIsParamList(nx) {

			d = p.declaratorSuffix(d, abstract)
			return d
		}
		p.advance()
		d.depth++
		inner := p.declarator(nil, abstract)
		p.expectPunct(PRparen, "to close declarator")
		if inner.hasName {
			d.name = inner.name
			d.nameTok = inner.nameTok
			d.hasName = true
			d.parenName = true
		}
		d.ptr += inner.ptr
		d.depth += inner.depth
		d.constq = d.constq || inner.constq
	}
	d = p.declaratorSuffix(d, abstract)
	return d
}

func parenIsParamList(nx Tok) bool {
	if nx.Kind == TPunct && (nx.Punct == PRparen || nx.Punct == PEllip) {
		return true
	}
	if nx.Kind != TIdent {
		return false
	}
	switch nx.Text {
	case "const", "volatile", "restrict", "_Atomic", "void", "char", "short",
		"int", "long", "float", "double", "signed", "unsigned", "_Bool", "bool",
		"struct", "union", "enum", "typeof", "typeof_unqual", "_BitInt",
		"_Decimal32", "_Decimal64", "_Decimal128", "register", "inline":
		return true
	}
	return false
}

func (p *parser) declaratorSuffix(d dcl, abstract bool) dcl {
	for !p.eof() {
		t := p.cur()
		if t.Kind == TPunct && t.Punct == PLbrack {
			p.advance()
			d.isArray = true
			d.arrayConst = false
			d.arrayLen = 0

			if t2 := p.cur(); t2.Kind == TIdent && t2.Text == "static" {
				d.arrayConst = true
				p.advance()
			}
			for p.cur().Kind == TIdent {
				switch p.cur().Text {
				case "const", "volatile", "restrict", "__restrict", "__restrict__",
					"_Atomic", "static":
					d.arrayConst = d.arrayConst || p.cur().Text == "static"
					p.advance()
					continue
				}
				break
			}
			if p.atPunct(PStar) && p.peek(1).Kind == TPunct && p.peek(1).Punct == PRbrack {
				p.advance()
				d.arrayConst = false
				d.arrayLen = -1
			} else if !p.atPunct(PRbrack) {
				start := p.cur()
				p.assignment()
				end := p.prevEnd()
				if v, ok := constNumText(p.srcOf(start), start.Off, end); ok {
					d.arrayLen = v
					d.arrayConst = true
				} else {
					d.arrayLen = -1
				}
			}
			p.expectPunct(PRbrack, "to close array")
			continue
		}
		if t.Kind == TPunct && t.Punct == PLparen {
			p.advance()
			params, variadic, kr := p.paramList()
			d.isFn = true
			d.params = params
			d.variadic = variadic
			d.kr = kr
			if kr {
				for _, pt := range params {
					d.krNames = append(d.krNames, pt.name)
				}
			}
			d.fnptr = d.parenName && d.ptr > 0
			continue
		}
		return d
	}
	return d
}

func (p *parser) prevEnd() int32 {
	if p.pos > 0 {
		return p.toks[p.pos-1].End
	}
	return p.cur().End
}

func constNumText(src []byte, off, end int32) (int64, bool) {
	s := strings.TrimSpace(rawText(src, off, end))
	if s == "" {
		return 0, false
	}
	v, err := strconv.ParseInt(s, 0, 64)
	if err != nil {

		return 0, false
	}
	return v, true
}

func (p *parser) paramList() ([]paramT, bool, bool) {
	var params []paramT
	variadic := false
	if p.atPunct(PRparen) {
		p.advance()
		return nil, false, false
	}
	if p.atIdent("void") && p.peek(1).Kind == TPunct && p.peek(1).Punct == PRparen {
		p.advance()
		p.advance()
		return nil, false, false
	}
	kr := false
	for !p.eof() {
		p.parseAttributes()
		if p.acceptPunct(PEllip) {
			variadic = true
			p.closeParamList()
			return params, true, kr
		}
		t := p.cur()
		specs := p.parseDeclSpecs()
		if !specs.saw {

			if t.Kind == TIdent && !isKeyword(t.Text) {
				p.advance()
				kr = true
				params = append(params, paramT{name: t.Text, line: int32(t.Line)})
				if p.acceptPunct(PComma) {
					continue
				}
				p.closeParamList()
				return params, false, kr
			}
			p.errf(t, "expected parameter declaration")
			if p.atPunct(PRparen) {
				p.advance()
				return params, variadic, kr
			}
			if p.atPunct(PComma) {
				p.advance()
				continue
			}

			p.closeParamList()
			return params, variadic, kr
		}
		isVariadicArg := false
		if p.atPunct(PEllip) {
			isVariadicArg = true
		}
		d := p.declarator(&specs, true)
		if isVariadicArg {
			variadic = true
		}
		pt := paramT{
			typ:      specs.baseText() + d.ptrStars(),
			ptr:      d.ptr,
			arrayLen: arrayLenI(d),
			isConst:  specs.constq,
			variadic: variadic && d.name == "" && !d.hasName,
			unnamed:  !d.hasName,
			line:     int32(t.Line),
		}
		if pt.arrayLen != 0 {

		}
		if d.hasName {
			pt.name = d.name
		}
		if specs.typedef == "typedef" {

			specs.typedef = ""
		}
		params = append(params, pt)

		for p.cur().Kind == TIdent && !isKeyword(p.cur().Text) {
			nx := p.peek(1)
			if nx.Kind == TIdent && !isKeyword(nx.Text) {
				p.advance()
				continue
			}
			if nx.Kind == TPunct && nx.Punct == PLparen {
				p.advance()
				p.skipBalanced()
				continue
			}
			if nx.Kind == TPunct && (nx.Punct == PComma || nx.Punct == PRparen) {
				p.advance()
			}
			break
		}
		if p.acceptPunct(PComma) {
			continue
		}
		p.closeParamList()
		return params, variadic, kr
	}
	return params, variadic, kr
}

type tname struct {
	text    string
	ptr     int
	isFn    bool
	isArray bool
}

func (p *parser) parseTypeName() tname {
	specs := p.parseDeclSpecs()
	d := p.declarator(&specs, true)
	return tname{
		text:    specs.baseText() + d.ptrStars(),
		ptr:     d.ptr,
		isFn:    d.isFn,
		isArray: d.isArray,
	}
}

func (p *parser) parseTU() {

	mk := p.addNode(Node{Kind: NTU})
	p.fa.Nodes[mk].A = uint32(len(p.fa.Nodes))
	lastPos := -1
	reps := 0
	for !p.eof() {
		if p.pos == lastPos {
			reps++
			if reps > 4 {

				p.errf(p.cur(), "no progress; skipping token")
				p.advance()
				reps = 0
				continue
			}
		} else {
			reps = 0
			lastPos = p.pos
		}
		p.parseExternal()
		if len(p.fa.Nodes) > 4<<20 {
			p.errf(p.cur(), "node budget exceeded")
			return
		}
	}
	p.fa.Nodes[mk].B = uint32(len(p.fa.Nodes)) - p.fa.Nodes[mk].A
	if len(p.fa.Nodes) > 0 {
		p.fa.Nodes[mk].End = p.toks[len(p.toks)-1].End
	}
}

func (p *parser) parseExternal() {
	t := p.cur()
	switch {
	case p.atPunct(PSemi):
		p.advance()
		return
	case p.atPunct(PRbrace):
		p.errf(t, "unexpected '}' at file scope")
		p.advance()
		return
	case p.atIdent("__extension__"):
		p.advance()
		return
	case p.atIdent("asm") || p.atIdent("__asm__") || p.atIdent("__asm"):
		p.skipAsm()
		p.acceptPunct(PSemi)
		return
	case p.atIdent("_Static_assert") || p.atIdent("static_assert"):
		p.parseStaticAssert()
		return
	case p.atIdent("extern") && p.peek(1).Kind == TStr:

		p.advance()
		p.advance()
		if p.acceptPunct(PLbrace) {
			for !p.eof() && !p.atPunct(PRbrace) {
				p.parseExternal()
			}
			p.acceptPunct(PRbrace)
			return
		}
		p.parseExternal()
		return
	}
	p.parseAttributes()
	specs := p.parseDeclSpecs()
	p.parseAttributes()
	if !specs.saw {
		p.errf(t, "expected declaration")
		p.syncTo(t, "external declaration")
		return
	}
	if specs.isTypedef {
		d0 := p.declarator(&specs, false)
		if d0.isFn && (p.atPunct(PLbrace) || d0.kr) {
			p.parseFuncDef(specs, d0, t)
			return
		}
		p.parseDeclList(specs, d0, t, true)
		return
	}
	d := p.declarator(&specs, false)

	if d.isFn && !p.atPunct(PLbrace) && !p.atPunct(PSemi) && krShaped(d) {
		save := p.pos
		saveErrs := p.nErrors
		if p.errs != nil {
			saveErrs = len(*p.errs)
		}
		p.krMode = true
		d2 := p.declarator(&specs, false)
		p.krMode = false
		if d2.isFn && d2.kr {
			d = d2
		} else {
			p.pos = save
			p.nErrors = saveErrs
			if p.errs != nil {
				*p.errs = (*p.errs)[:min(saveErrs, len(*p.errs))]
			}
		}
	}
	if d.isFn && (p.atPunct(PLbrace) || d.kr) {
		p.parseFuncDef(specs, d, t)
		return
	}
	p.parseDeclList(specs, d, t, true)
}

func krShaped(d dcl) bool {
	if len(d.params) == 0 || d.variadic {
		return false
	}
	for _, pt := range d.params {
		if !pt.unnamed || pt.ptr > 0 || strings.Contains(pt.typ, " ") ||
			strings.Contains(pt.typ, "*") || strings.Contains(pt.typ, "(") {
			return false
		}
	}
	return true
}

func (p *parser) parseDeclList(specs tspecs, first dcl, t Tok, topLevel bool) []uint32 {
	var created []uint32
	d := first
	have := true
	for {
		if !have {
			p.parseAttributes()
			d = p.declarator(&specs, false)
			p.parseAttributes()
		}
		have = false
		nd := DeclNode{
			NameIdx:  0,
			TypeIdx:  p.fa.intern(specs.baseText() + d.ptrStars()),
			Ptr:      int32(d.ptr),
			ArrayLen: arrayLenI(d),
			Storage:  specs.storage,
			Line:     int32(t.Line),
		}
		if d.hasName {
			nd.NameIdx = p.fa.intern(d.name)
		}
		kind := uint8(0)
		switch {
		case specs.isTypedef:
			kind = 2
		case d.isFn && !d.fnptr:
			kind = 1
		}
		nd.Kind = kind
		if kind == 2 && d.hasName {
			p.addTypedef(d.name)
		}

		if p.acceptPunct(PEq) {
			nd.Init = p.initializer()
			nd.Storage |= FHasInit
		}
		p.fa.Decls = append(p.fa.Decls, nd)
		idxA := uint32(len(p.fa.Decls))
		n := Node{Kind: NDecl, A: idxA, Off: t.Off, End: t.End,
			Line: t.Line, Col: t.Col}
		if d.hasName {
			n.B = nd.NameIdx
		}
		if nd.Init != 0 {
			n.Flags |= FHasInit
		}
		n.File = uint32(t.File)
		created = append(created, p.addNode(n))
		if p.acceptPunct(PComma) {
			t = p.cur()
			continue
		}
		p.expectPunct(PSemi, "after declaration")
		break
	}
	return created
}

func (p *parser) parseFuncDef(specs tspecs, d dcl, t Tok) {

	if d.kr {
		for !p.eof() && !p.atPunct(PLbrace) {
			kt := p.cur()
			kspecs := p.parseDeclSpecs()
			if !kspecs.saw {
				p.errf(kt, "bad K&R declaration")
				p.advance()
				continue
			}
			have := false
			for {
				p.parseAttributes()
				kd := p.declarator(&kspecs, false)
				for i := range d.params {
					if d.params[i].name == kd.name {
						d.params[i].typ = kspecs.baseText() + kd.ptrStars()
						d.params[i].ptr = kd.ptr
						d.params[i].isConst = kspecs.constq
						d.params[i].unnamed = false
					}
				}
				have = true
				if !p.acceptPunct(PComma) {
					break
				}
			}
			_ = have
			p.expectPunct(PSemi, "after K&R declaration")
		}
	}
	ob := p.cur()
	p.funcDepth++
	p.pushScope()

	p0 := uint32(len(p.fa.Nodes))
	sig := funcSignature(specs, d)
	ret := specs.baseText() + d.ptrStars()
	for i := range d.params {
		pt := &d.params[i]
		pd := ParamD{
			TypeIdx:  p.fa.intern(pt.typ),
			Ptr:      int32(pt.ptr),
			ArrayLen: pt.arrayLen,
			Variadic: pt.variadic && i == len(d.params)-1 && d.variadic,
			Unnamed:  pt.unnamed,
			IsConst:  pt.isConst,
			Line:     pt.line,
		}
		if pt.name != "" {
			pd.NameIdx = p.fa.intern(pt.name)
		}
		p.fa.Params = append(p.fa.Params, pd)
		pn := Node{Kind: NParam, A: uint32(len(p.fa.Params)), Line: pt.line}
		p.addNode(pn)
		if pt.name != "" {
			p.addTypedefGuard(pt.name)
		}
	}
	fd := FuncDef{
		NameIdx:  p.fa.intern(d.name),
		SigIdx:   p.fa.intern(sig),
		RetIdx:   p.fa.intern(ret),
		Param0:   p0,
		NParams:  uint32(len(d.params)),
		LineEnd:  int32(ob.Line),
		Storage:  specs.storage,
		Variadic: d.variadic,
		KR:       d.kr,
	}
	body := p.block()
	p.popScope()
	p.funcDepth--
	fd.Body = body
	if body != 0 {
		fd.LineEnd = int32(p.fa.Nodes[body].Line)
	}
	p.fa.Funcs = append(p.fa.Funcs, fd)
	fn := Node{Kind: NFuncDef, A: uint32(len(p.fa.Funcs)), File: uint32(t.File),
		Off: t.Off, Line: t.Line, Col: t.Col}
	if body != 0 {
		fn.End = p.fa.Nodes[body].End
	} else {
		fn.End = t.End
	}
	p.addNode(fn)
}

func (p *parser) addTypedefGuard(name string) {

}

func funcSignature(specs tspecs, d dcl) string {
	var b strings.Builder
	if specs.storage&FStatic != 0 {
		b.WriteString("static ")
	}
	if specs.storage&FInline != 0 {
		b.WriteString("inline ")
	}
	if specs.storage&FExtern != 0 {
		b.WriteString("extern ")
	}
	b.WriteString(specs.baseText())
	b.WriteString(d.ptrStars())
	b.WriteString(" ")
	b.WriteString(d.name)
	b.WriteString("(")
	for i, pt := range d.params {
		if i > 0 {
			b.WriteString(", ")
		}
		if pt.typ == "" {
			b.WriteString(pt.name)
		} else if pt.unnamed {
			b.WriteString(pt.typ)
		} else {
			b.WriteString(pt.typ)
			b.WriteString(" ")
			b.WriteString(pt.name)
		}
	}
	if d.variadic {
		if len(d.params) > 0 {
			b.WriteString(", ")
		}
		b.WriteString("...")
	}
	b.WriteString(")")
	return b.String()
}

func (p *parser) block() uint32 {
	ob := p.advance()
	p.pushScope()
	mk := p.addNode(Node{Kind: NCompoundStmt, Off: ob.Off, End: ob.End,
		Line: ob.Line, Col: ob.Col})
	p.fa.Nodes[mk].A = uint32(len(p.fa.Nodes))
	for !p.atPunct(PRbrace) && !p.eof() {
		p.stmt()
	}
	p.fa.Nodes[mk].B = uint32(len(p.fa.Nodes)) - p.fa.Nodes[mk].A
	if p.acceptPunct(PRbrace) {
		p.fa.Nodes[mk].End = p.toks[p.pos-1].End
	}
	p.popScope()
	return mk
}

func (p *parser) isDeclStart() bool {
	t := p.cur()
	if t.Kind != TIdent {
		return false
	}
	switch t.Text {
	case "static", "extern", "register", "auto", "typedef", "const", "volatile",
		"restrict", "_Atomic", "struct", "union", "enum", "void", "char", "short",
		"int", "long", "float", "double", "signed", "unsigned", "_Bool", "bool",
		"_Complex", "_Imaginary", "typeof", "typeof_unqual", "_BitInt",
		"_Decimal32", "_Decimal64", "_Decimal128", "constexpr", "thread_local",
		"_Thread_local", "alignas", "_Alignas", "__extension__",
		"__attribute__", "__attribute", "__inline", "__inline__", "_Noreturn",
		"noreturn", "static_assert", "_Static_assert":
		return true
	}
	return p.isTypedefName(t.Text)
}

func (p *parser) stmt() uint32 {
	t := p.cur()
	if t.Kind == TPunct && t.Punct == mustPunct("[") {
		p.parseAttributes()
		t = p.cur()
	}
	switch {
	case p.atPunct(PLbrace):
		return p.block()
	case p.atPunct(PSemi):
		p.advance()
		return p.addNode(Node{Kind: NExprStmt, Off: t.Off, End: t.End,
			Line: t.Line, Col: t.Col})
	case p.atIdent("if"):
		return p.ifStmt()
	case p.atIdent("switch"):
		return p.switchStmt()
	case p.atIdent("while"):
		return p.whileStmt()
	case p.atIdent("do"):
		return p.doStmt()
	case p.atIdent("for"):
		return p.forStmt()
	case p.atIdent("return"):
		return p.returnStmt()
	case p.atIdent("break"):
		p.advance()
		p.expectPunct(PSemi, "after break")
		return p.addNode(Node{Kind: NBreak, Off: t.Off, End: t.End,
			Line: t.Line, Col: t.Col})
	case p.atIdent("continue"):
		p.advance()
		p.expectPunct(PSemi, "after continue")
		return p.addNode(Node{Kind: NContinue, Off: t.Off, End: t.End,
			Line: t.Line, Col: t.Col})
	case p.atIdent("goto"):
		p.advance()
		n := Node{Kind: NGoto, Off: t.Off, Line: t.Line, Col: t.Col}
		if p.acceptPunct(mustPunct("&&")) {
			if p.cur().Kind == TIdent {
				n.A = p.fa.intern(p.advance().Text)
			}
		} else if p.cur().Kind == TIdent {
			n.A = p.fa.intern(p.advance().Text)
		}
		p.expectPunct(PSemi, "after goto")
		n.End = p.prevEnd()
		return p.addNode(n)
	case p.atIdent("case"), p.atIdent("default"):
		return p.caseStmt()
	case p.atIdent("_Static_assert") || p.atIdent("static_assert"):
		p.parseStaticAssert()
		return uint32(len(p.fa.Nodes)) - 1
	case p.atIdent("asm") || p.atIdent("__asm__") || p.atIdent("__asm"):
		at := p.advance()
		p.skipAsm()
		p.acceptPunct(PSemi)
		return p.addNode(Node{Kind: NAsm, Off: at.Off, End: p.prevEnd(),
			Line: at.Line, Col: at.Col})
	case p.atIdent("__extension__"):
		p.advance()
		return p.stmt()
	case t.Kind == TIdent && p.peek(1).Kind == TPunct && p.peek(1).Punct == PColon &&
		!p.atIdent("default") && !p.atIdent("case"):

		p.advance()
		p.advance()
		mk := p.addNode(Node{Kind: NLabel, A: p.fa.intern(t.Text), Off: t.Off,
			Line: t.Line, Col: t.Col})
		body := p.stmt()
		p.fa.Nodes[mk].B = body
		p.fa.Nodes[mk].End = p.prevEnd()
		return mk
	case p.isDeclStart():
		if mk, ok := p.tryDeclStatement(); ok {
			return mk
		}
		fallthrough
	default:
		e0 := uint32(len(p.fa.Nodes))
		_ = e0
		mk := p.addNode(Node{Kind: NExprStmt})
		e := p.expr()
		p.fa.Nodes[mk].A = e
		p.expectPunct(PSemi, "after expression statement")
		p.fa.Nodes[mk].Off = t.Off
		p.fa.Nodes[mk].End = p.prevEnd()
		p.fa.Nodes[mk].Line = t.Line
		p.fa.Nodes[mk].Col = t.Col
		return mk
	}
}

func (p *parser) tryDeclStatement() (uint32, bool) {
	savePos := p.pos
	saveNodes := len(p.fa.Nodes)
	saveDecls := len(p.fa.Decls)
	saveParams := len(p.fa.Params)
	saveTags := len(p.fa.Tags)
	saveFields := len(p.fa.Fields)
	saveEnums := len(p.fa.Enums)
	saveTypes := len(p.fa.Types)
	saveInits := len(p.fa.Inits)
	saveErrs := p.nErrors
	t := p.cur()
	mk := p.addNode(Node{Kind: NDeclStmt, Off: t.Off, Line: t.Line,
		Col: t.Col})
	p.fa.Nodes[mk].A = uint32(len(p.fa.Nodes))
	p.parseAttributes()
	specs := p.parseDeclSpecs()
	if !specs.saw {
		p.rollbackDecl(savePos, saveNodes, saveDecls, saveParams, saveTags,
			saveFields, saveEnums, saveTypes, saveInits, saveErrs, mk)
		return 0, false
	}
	d0 := p.declarator(&specs, false)
	p.parseDeclList(specs, d0, t, false)
	if p.nErrors > saveErrs {
		p.rollbackDecl(savePos, saveNodes, saveDecls, saveParams, saveTags,
			saveFields, saveEnums, saveTypes, saveInits, saveErrs, mk)
		return 0, false
	}
	p.fa.Nodes[mk].B = uint32(len(p.fa.Nodes)) - p.fa.Nodes[mk].A
	p.fa.Nodes[mk].End = p.prevEnd()
	return mk, true
}

func (p *parser) rollbackDecl(savePos, nN, nD, nP, nT, nF, nE, nTy, nI, nEr int, mk uint32) {
	p.pos = savePos
	p.fa.Nodes = p.fa.Nodes[:nN]
	p.fa.Decls = p.fa.Decls[:nD]
	p.fa.Params = p.fa.Params[:nP]
	p.fa.Tags = p.fa.Tags[:nT]
	p.fa.Fields = p.fa.Fields[:nF]
	p.fa.Enums = p.fa.Enums[:nE]
	p.fa.Types = p.fa.Types[:nTy]
	p.fa.Inits = p.fa.Inits[:nI]
	if p.errs != nil {
		*p.errs = (*p.errs)[:min(nEr, len(*p.errs))]
	}
	_ = mk
	p.nErrors = nEr
}

func (p *parser) ifStmt() uint32 {
	t := p.advance()
	p.expectPunct(PLparen, "after if")
	c := p.expr()
	p.expectPunct(PRparen, "after if condition")
	th := p.stmt()
	el := uint32(0)
	if p.acceptIdent("else") {
		el = p.stmt()
	}
	return p.addNode(Node{Kind: NIf, A: c, B: th, C: el, Off: t.Off,
		End: p.prevEnd(), Line: t.Line, Col: t.Col})
}

func (p *parser) switchStmt() uint32 {
	t := p.advance()
	p.expectPunct(PLparen, "after switch")
	c := p.expr()
	p.expectPunct(PRparen, "after switch condition")
	b := p.stmt()
	return p.addNode(Node{Kind: NSwitch, A: c, B: b, Off: t.Off, End: p.prevEnd(),
		Line: t.Line, Col: t.Col})
}

func (p *parser) whileStmt() uint32 {
	t := p.advance()
	p.expectPunct(PLparen, "after while")
	c := p.expr()
	p.expectPunct(PRparen, "after while condition")
	p.loopDepth++
	b := p.stmt()
	p.loopDepth--
	return p.addNode(Node{Kind: NWhile, A: c, B: b, Off: t.Off, End: p.prevEnd(),
		Line: t.Line, Col: t.Col})
}

func (p *parser) doStmt() uint32 {
	t := p.advance()
	p.loopDepth++
	b := p.stmt()
	p.loopDepth--
	if p.acceptIdent("while") {
		p.expectPunct(PLparen, "after do while")
		c := p.expr()
		p.expectPunct(PRparen, "after do while")
		p.expectPunct(PSemi, "after do-while")
		return p.addNode(Node{Kind: NDo, A: b, B: c, Off: t.Off, End: p.prevEnd(),
			Line: t.Line, Col: t.Col})
	}
	return p.addNode(Node{Kind: NDo, A: b, Off: t.Off, End: p.prevEnd(),
		Line: t.Line, Col: t.Col})
}

func (p *parser) forStmt() uint32 {
	t := p.advance()
	p.expectPunct(PLparen, "after for")
	p.pushScope()
	mk := p.addNode(Node{Kind: NFor, Off: t.Off, Line: t.Line, Col: t.Col})
	init := uint32(0)
	if !p.atPunct(PSemi) {
		if p.isDeclStart() {
			if n, ok := p.tryDeclStatement(); ok {
				init = n
			}
		} else {
			ie := p.addNode(Node{Kind: NExprStmt})
			e := p.expr()
			p.fa.Nodes[ie].A = e
			p.expectPunct(PSemi, "after for-init")
			p.fa.Nodes[ie].End = p.prevEnd()
			init = ie
		}
	} else {
		p.advance()
	}
	cond := uint32(0)
	if !p.atPunct(PSemi) {
		cond = p.expr()
	}
	p.expectPunct(PSemi, "after for-cond")
	step := uint32(0)
	if !p.atPunct(PRparen) {
		step = p.expr()
	}
	p.expectPunct(PRparen, "after for-clauses")
	p.loopDepth++
	b := p.stmt()
	p.loopDepth--
	p.fa.Nodes[mk].A = init
	p.fa.Nodes[mk].B = cond
	p.fa.Nodes[mk].C = step
	p.fa.Nodes[mk].D = b
	p.fa.Nodes[mk].End = p.prevEnd()
	p.popScope()
	return mk
}

func (p *parser) returnStmt() uint32 {
	t := p.advance()
	n := Node{Kind: NReturn, Off: t.Off, Line: t.Line, Col: t.Col}
	if !p.atPunct(PSemi) {
		n.A = p.expr()
	}
	p.expectPunct(PSemi, "after return")
	n.End = p.prevEnd()
	return p.addNode(n)
}

func (p *parser) caseStmt() uint32 {
	t := p.advance()
	n := Node{Kind: NCase, Off: t.Off, Line: t.Line, Col: t.Col}
	if t.Text == "default" {
		p.expectPunct(PColon, "after default")
	} else {
		n.A = p.condExprNode()
		if p.acceptPunct(mustPunct("...")) {
			p.condExprNode()
		}
		p.expectPunct(PColon, "after case")
	}
	n.B = p.stmt()
	n.End = p.prevEnd()
	return p.addNode(n)
}

var binPrec = func() map[uint8]int {
	m := map[uint8]int{
		mustPunct("||"): 1, mustPunct("&&"): 2, mustPunct("|"): 3,
		mustPunct("^"): 4, mustPunct("&"): 5, mustPunct("=="): 6, mustPunct("!="): 6,
		mustPunct("<"): 7, mustPunct(">"): 7, mustPunct("<="): 7, mustPunct(">="): 7,
		mustPunct("<<"): 8, mustPunct(">>"): 8, mustPunct("+"): 9, mustPunct("-"): 9,
		mustPunct("*"): 10, mustPunct("/"): 10, mustPunct("%"): 10,
	}
	return m
}()

func isAssignOp(code uint8) bool {
	switch code {
	case PEq:
		return true
	}
	t := punctTable[code]
	if len(t) == 3 && (t == ">>=" || t == "<<=") {
		return true
	}
	return len(t) == 2 && t[1] == '=' && t[0] != '=' && t[0] != '!' && t[0] != '<' && t[0] != '>'
}

func (p *parser) expr() uint32 {
	l := p.assignment()
	for p.atPunct(PComma) {
		p.advance()
		r := p.assignment()
		l = p.addNode(Node{Kind: NComma, A: l, B: r, Off: p.fa.Nodes[l].Off,
			End: p.fa.Nodes[r].End, Line: p.fa.Nodes[l].Line, Col: p.fa.Nodes[l].Col})
	}
	return l
}

func (p *parser) assignment() uint32 {
	c := p.binary(1)
	if p.atPunct(PTerse) {
		p.advance()
		th := p.expr()
		p.expectPunct(PColon, "in ?:")
		el := p.assignment()
		return p.addNode(Node{Kind: NCond, A: c, B: th, C: el, Off: p.fa.Nodes[c].Off,
			End: p.fa.Nodes[el].End, Line: p.fa.Nodes[c].Line, Col: p.fa.Nodes[c].Col})
	}
	if t := p.cur(); t.Kind == TPunct && isAssignOp(t.Punct) {
		p.advance()
		r := p.assignment()
		return p.addNode(Node{Kind: NAssign, Flags: uint16(t.Punct), A: c, B: r,
			Off: p.fa.Nodes[c].Off, End: p.fa.Nodes[r].End,
			Line: p.fa.Nodes[c].Line, Col: p.fa.Nodes[c].Col})
	}
	return c
}

func (p *parser) binary(minPrec int) uint32 {
	l := p.unary()
	for {
		t := p.cur()
		if t.Kind != TPunct {
			return l
		}
		prec, ok := binPrec[t.Punct]
		if !ok || prec < minPrec {
			return l
		}
		p.advance()
		r := p.binary(prec + 1)
		n := Node{Kind: NBinary, Flags: uint16(t.Punct), A: l, B: r,
			Off: p.fa.Nodes[l].Off, End: p.fa.Nodes[r].End,
			Line: p.fa.Nodes[l].Line, Col: p.fa.Nodes[l].Col}
		l = p.addNode(n)
	}
}

func (p *parser) isTypeStart() bool {
	t := p.cur()
	if t.Kind != TIdent {
		return false
	}
	switch t.Text {
	case "const", "volatile", "restrict", "_Atomic", "struct", "union", "enum",
		"void", "char", "short", "int", "long", "float", "double", "signed",
		"unsigned", "_Bool", "bool", "_Complex", "_Imaginary", "typeof",
		"typeof_unqual", "_BitInt", "_Decimal32", "_Decimal64", "_Decimal128",
		"constexpr", "alignas", "_Alignas":
		return true
	}
	return p.isTypedefName(t.Text)
}

func (p *parser) unary() uint32 {
	t := p.cur()
	if t.Kind == TPunct {
		switch t.Punct {
		case PInc, PDec, PPlus, PMinus, PBang, PTilde:
			p.advance()
			o := p.unary()
			return p.addNode(Node{Kind: NUnary, Flags: uint16(t.Punct), A: o,
				Off: t.Off, End: p.fa.Nodes[o].End, Line: t.Line, Col: t.Col})
		case PStar:
			p.advance()
			o := p.unary()
			return p.addNode(Node{Kind: NUnary, Flags: uint16(PStar), A: o, Off: t.Off,
				End: p.fa.Nodes[o].End, Line: t.Line, Col: t.Col})
		case PAmp:
			p.advance()
			o := p.unary()
			return p.addNode(Node{Kind: NUnary, Flags: uint16(PAmp), A: o, Off: t.Off,
				End: p.fa.Nodes[o].End, Line: t.Line, Col: t.Col})
		case mustPunct("&&"):
			p.advance()
			if p.cur().Kind == TIdent {
				nm := p.advance()
				return p.addNode(Node{Kind: NIdent, A: p.fa.intern(nm.Text),
					Flags: 1, Off: t.Off, End: nm.End, Line: t.Line, Col: t.Col})
			}
		case PLparen:

			if p.peek(1).Kind != TEOF && p.isTypeStartAt(1) {
				save := p.pos
				p.advance()
				tn := p.parseTypeName()
				if p.acceptPunct(PRparen) {
					if p.atPunct(PLbrace) {
						il := p.initializer()
						return p.addNode(Node{Kind: NCompoundLit, A: p.addTypeD(tn), B: il,
							Off: t.Off, End: p.fa.Nodes[il].End, Line: t.Line, Col: t.Col})
					}
					o := p.unary()
					return p.addNode(Node{Kind: NCast, A: p.addTypeD(tn), B: o,
						Off: t.Off, End: p.fa.Nodes[o].End, Line: t.Line, Col: t.Col})
				}
				p.pos = save
			}
		}
	}
	if t.Kind == TIdent {
		switch t.Text {
		case "sizeof":
			p.advance()
			if p.atPunct(PLparen) && p.isTypeStartAt(1) {
				save := p.pos
				p.advance()
				tn := p.parseTypeName()
				if p.acceptPunct(PRparen) {
					return p.addNode(Node{Kind: NSizeofT, A: p.addTypeD(tn), Off: t.Off,
						End: p.prevEnd(), Line: t.Line, Col: t.Col})
				}
				p.pos = save
			}
			o := p.unary()
			return p.addNode(Node{Kind: NSizeofE, A: o, Off: t.Off,
				End: p.fa.Nodes[o].End, Line: t.Line, Col: t.Col})
		case "_Alignof", "alignof", "__alignof", "__alignof__":
			p.advance()
			p.expectPunct(PLparen, "after alignof")
			tn := p.parseTypeName()
			p.expectPunct(PRparen, "after alignof type")
			return p.addNode(Node{Kind: NAlignofT, A: p.addTypeD(tn), Off: t.Off,
				End: p.prevEnd(), Line: t.Line, Col: t.Col})
		case "__extension__":
			p.advance()
			return p.unary()
		case "_Generic":
			return p.genericSelection()
		case "__real", "__imag":
			p.advance()
			o := p.unary()
			return p.addNode(Node{Kind: NUnary, Flags: uint16(PStar), A: o, Off: t.Off,
				End: p.fa.Nodes[o].End, Line: t.Line, Col: t.Col})
		}
	}
	return p.postfix()
}

func (p *parser) isTypeStartAt(n int) bool {
	t := p.peek(n)
	if t.Kind != TIdent {
		return false
	}
	switch t.Text {
	case "const", "volatile", "restrict", "_Atomic", "struct", "union", "enum",
		"void", "char", "short", "int", "long", "float", "double", "signed",
		"unsigned", "_Bool", "bool", "_Complex", "_Imaginary", "typeof",
		"typeof_unqual", "_BitInt", "_Decimal32", "_Decimal64", "_Decimal128",
		"constexpr", "register":
		return true
	}
	return p.isTypedefName(t.Text)
}

func (p *parser) addTypeD(tn tname) uint32 {
	p.fa.Types = append(p.fa.Types, TypeD{
		TextIdx: p.fa.intern(tn.text), Ptr: int32(tn.ptr),
		Array: tn.isArray, IsFn: tn.isFn,
	})
	return uint32(len(p.fa.Types))
}

func (p *parser) genericSelection() uint32 {
	t := p.advance()
	p.expectPunct(PLparen, "after _Generic")
	ctrl := p.assignment()
	a0 := uint32(len(p.fa.Assocs))
	nAss := uint32(0)
	for p.acceptPunct(PComma) {
		asc := GenericAssoc{}
		if p.atIdent("default") {
			p.advance()
			asc.IsDefault = true
		} else {
			tn := p.parseTypeName()
			asc.TypeIdx = p.addTypeD(tn)
		}
		p.expectPunct(PColon, "in _Generic association")
		asc.Expr = p.assignment()
		p.fa.Assocs = append(p.fa.Assocs, asc)
		nAss++
	}
	p.expectPunct(PRparen, "to close _Generic")
	return p.addNode(Node{Kind: NGeneric, A: ctrl, B: a0, C: nAss, Off: t.Off,
		End: p.prevEnd(), Line: t.Line, Col: t.Col})
}

func (p *parser) postfix() uint32 {
	e := p.primary()
	for !p.eof() {
		t := p.cur()
		if t.Kind != TPunct {
			return e
		}
		switch t.Punct {
		case PLbrack:
			p.advance()
			ix := p.expr()
			p.expectPunct(PRbrack, "to close index")
			e = p.addNode(Node{Kind: NIndex, A: e, B: ix, Off: p.fa.Nodes[e].Off,
				End: p.prevEnd(), Line: p.fa.Nodes[e].Line, Col: p.fa.Nodes[e].Col})
		case PLparen:
			p.advance()
			a0 := uint32(len(p.fa.Nodes))
			nArgs := uint32(0)
			if !p.atPunct(PRparen) {
				for {
					p.assignment()
					nArgs++
					if !p.acceptPunct(PComma) {
						break
					}
				}
			}
			p.expectPunct(PRparen, "to close call args")
			e = p.addNode(Node{Kind: NCall, A: e, B: nArgs, C: a0,
				Off: p.fa.Nodes[e].Off, End: p.prevEnd(),
				Line: p.fa.Nodes[e].Line, Col: p.fa.Nodes[e].Col})
		case PDot, PArrow:
			p.advance()
			if p.cur().Kind != TIdent {
				p.errf(p.cur(), "expected member name")
				return e
			}
			nm := p.advance()
			e = p.addNode(Node{Kind: NMember, A: p.fa.intern(nm.Text), B: e,
				Flags: b2iu(t.Punct == PArrow), Off: p.fa.Nodes[e].Off, End: nm.End,
				Line: p.fa.Nodes[e].Line, Col: p.fa.Nodes[e].Col})
		case PInc, PDec:
			p.advance()
			e = p.addNode(Node{Kind: NPostfix, Flags: uint16(t.Punct), A: e,
				Off: p.fa.Nodes[e].Off, End: p.prevEnd(),
				Line: p.fa.Nodes[e].Line, Col: p.fa.Nodes[e].Col})
		default:
			return e
		}
	}
	return e
}

func b2iu(b bool) uint16 {
	if b {
		return 1
	}
	return 0
}

func (p *parser) primary() uint32 {
	t := p.cur()
	switch t.Kind {
	case TNumber:
		p.advance()
		return p.addNode(Node{Kind: NNumLit, A: p.fa.intern(t.Text), Off: t.Off,
			End: t.End, Line: t.Line, Col: t.Col})
	case TChar:
		p.advance()
		return p.addNode(Node{Kind: NCharLit, A: p.fa.intern(t.Text), Off: t.Off,
			End: t.End, Line: t.Line, Col: t.Col})
	case TStr:
		txt := t.Text
		end := t.End
		line := t.Line
		col := t.Col
		p.advance()
		for p.cur().Kind == TStr {
			nx := p.advance()
			txt += " " + nx.Text
			end = nx.End
		}
		return p.addNode(Node{Kind: NStrLit, A: p.fa.intern(txt), Off: t.Off,
			End: end, Line: line, Col: col})
	case TIdent:
		switch t.Text {
		case "true", "false":
			p.advance()
			fl := uint16(0)
			if t.Text == "true" {
				fl = 1
			}
			return p.addNode(Node{Kind: NBoolLit, Flags: fl, A: p.fa.intern(t.Text),
				Off: t.Off, End: t.End, Line: t.Line, Col: t.Col})
		case "nullptr":
			p.advance()
			return p.addNode(Node{Kind: NNullPtr, Off: t.Off, End: t.End,
				Line: t.Line, Col: t.Col})
		case "__builtin_va_arg":
			p.advance()
			p.expectPunct(PLparen, "after __builtin_va_arg")
			e := p.assignment()
			p.expectPunct(PComma, "in __builtin_va_arg")
			tn := p.parseTypeName()
			p.expectPunct(PRparen, "to close __builtin_va_arg")
			return p.addNode(Node{Kind: NVaArg, A: e, B: p.addTypeD(tn), Off: t.Off,
				End: p.prevEnd(), Line: t.Line, Col: t.Col})
		}
		p.advance()
		return p.addNode(Node{Kind: NIdent, A: p.fa.intern(t.Text), Off: t.Off,
			End: t.End, Line: t.Line, Col: t.Col})
	case TPunct:
		if t.Punct == PLparen {

			nx := p.peek(1)
			if nx.Kind == TPunct && nx.Punct == PLbrace {
				p.advance()
				p.advance()
				b := p.block()
				p.expectPunct(PRparen, "to close statement expression")
				return p.addNode(Node{Kind: NStmtExpr, A: b, Off: t.Off,
					End: p.prevEnd(), Line: t.Line, Col: t.Col})
			}
			if nx.Kind == TIdent && p.isTypedefName(nx.Text) {

			}
			p.advance()
			e := p.expr()
			p.expectPunct(PRparen, "to close parenthesis")
			return p.addNode(Node{Kind: NParen, A: e, Off: t.Off, End: p.prevEnd(),
				Line: t.Line, Col: t.Col})
		}
	}
	p.errf(t, "unexpected token '"+t.Text+"' in expression")

	p.advance()
	return p.addNode(Node{Kind: NBad, Off: t.Off, End: t.End,
		Line: t.Line, Col: t.Col})
}

func (p *parser) condExprNode() uint32 { return p.assignment() }

func (p *parser) addNode(n Node) uint32 {
	return p.fa.addNode(n)
}

func (p *parser) initializer() uint32 {
	if !p.atPunct(PLbrace) {
		return p.assignment()
	}
	ob := p.advance()
	mk := p.addNode(Node{Kind: NInitList, Off: ob.Off, End: ob.End,
		Line: ob.Line, Col: ob.Col})
	p.fa.Nodes[mk].A = uint32(len(p.fa.Nodes))
	for !p.eof() && !p.atPunct(PRbrace) {
		item := InitD{}
		desig := false
		for {
			if p.atPunct(PDot) {
				p.advance()
				if p.cur().Kind == TIdent {
					item.FieldIdx = p.fa.intern(p.advance().Text)
				} else {
					p.errf(p.cur(), "expected field designator name")
				}
				desig = true
				continue
			}
			if p.atPunct(PLbrack) {
				p.advance()
				p.assignment()
				if p.acceptPunct(mustPunct("...")) {
					p.assignment()
				}
				p.expectPunct(PRbrack, "to close index designator")
				item.HasIndex = true
				desig = true
				continue
			}
			break
		}
		if desig {
			p.expectPunct(PEq, "after designator")
		}
		val := p.initializer()
		item.IsList = p.fa.Nodes[val].Kind == NInitList
		p.fa.Inits = append(p.fa.Inits, item)
		n := Node{Kind: NInitItem, A: uint32(len(p.fa.Inits)), B: val}
		p.addNode(n)
		if !p.acceptPunct(PComma) {
			break
		}
	}
	p.expectPunct(PRbrace, "to close initializer list")
	p.fa.Nodes[mk].B = uint32(len(p.fa.Nodes)) - p.fa.Nodes[mk].A
	if p.pos > 0 {
		p.fa.Nodes[mk].End = p.toks[p.pos-1].End
	}
	return mk
}

type bodyWalk struct {
	cyclomatic, cognitive, maxNesting  int32
	nLoops, nBranches, nSwitch, nCases int32
	nLabels, nGotos, nReturns          int32
	nDeref, nCast, nSizeof             int32
	nArith, nCmp, nShift               int32
	nLogical, nTernary, nAssign        int32
	nCompoundAssign, nIncdec           int32
	nFloatLit, nMagic, nNullCheck      int32
	nPtrLocals, nVla                   int32
	nTokens, nOperators, nOperands     int32
	nDistOps, nDistOper                int32
	hasVolatile, hasRestrict           int32
	nStaticAssert, nAtomic, nIntrinsic int32
	nLikely, nBuiltin                  int32
	nGetenv, nErrno                    int32
	maxLoopDepth                       int32

	callInLoop, allocInLoop, libmInLoop       int32
	strlenInLoop, ioInLoop, lockInLoop        int32
	switchInLoop, branchInLoop, divInLoop     int32
	retNull, retNeg, retZero, retVal, retVoid int32
	nStringLit, nAddrof, nArrow, nDot         int32
	nSubscript, nBitop                        int32
	nGlobalWrite                              int32

	locals []LocalRow
	lits   []LiteralRow
	addrs  []AddrTakenRow
	calls  []callSiteRec

	opSeen, operSeen     map[string]bool
	visited              map[uint32]bool
	toctouChk, toctouOpn map[string]bool
	castIdents           []string
}

type derivedFile struct {
	file    FileRow
	symbols []SymbolRow

	funcSymByNode map[uint32]int32
	curFuncNode   uint32
	lastFuncNode  uint32
	globalFileID  int32
	params        []ParamRow
	fields        []FieldRow
	locals        []LocalRow
	lits          []LiteralRow
	markers       []MarkerRow
	attrs         []AttributeRow
	imports       []ImportRow
	hazards       []HazardRow
	enums         []EnumMemberRow
	layout        []LayoutRowR
	ssize         []StructSizeRow
	decls         []DeclarationRow
	addrs         []AddrTakenRow
	secrets       []SecretCandidateRow
	allocs        []AllocSiteRow
	memops        []MemopRow
	macros        []MacroRow
	globals       []GlobalRow
	cfgs          []ConfigBlockRow
	locks         []LockRowR
	evops         []EventOpRow
	apiuses       []APIUseRow

	pendNames  []string
	pendLines  [][]int32
	pendSym    []int32
	pendFile   []int32
	pendModule []int32

	fnNames   []string
	fnSyms    []int32
	fnFiles   []int32
	fnModules []int32

	declared  map[string]bool
	macroSID  map[string]int32
	macroName []string

	ast     *FileAST
	pp      *preprocessor
	incRows []includeEdge
	incSeen map[int32]bool
	fnSpans [][3]int32
	srcRaw  []byte
	blank   []byte
	nlRaw   []int32
	srcID   uint32
	relPath string
	isTestF int32
	isGenF  int32
	modID   int32
	glSet   map[string]bool
}

func (df *derivedFile) globalSet() map[string]bool {
	if df.glSet == nil {
		m := make(map[string]bool, len(df.globals)*2)
		for i := range df.globals {
			m[df.globals[i].Name] = true
		}
		df.glSet = m
	}
	return df.glSet
}

func newDerivedFile(fa *FileAST, pp *preprocessor, raw []byte, fileID uint32) *derivedFile {
	return &derivedFile{ast: fa, pp: pp, srcRaw: raw, srcID: fileID,
		incSeen:  map[int32]bool{},
		declared: map[string]bool{}, macroSID: map[string]int32{},
		funcSymByNode: map[uint32]int32{}}
}

func (df *derivedFile) internSym(s *SymbolRow) int32 {

	df.symbols = append(df.symbols, *s)
	return int32(len(df.symbols))
}

func (df *derivedFile) rawSpan(off, end int32, cap int) string {
	if off < 0 || end < off || int(end) > len(df.srcRaw) {
		return ""
	}
	return jtrunc(squeeze(string(df.srcRaw[off:end]), ""), cap)
}

func (df *derivedFile) derive() {
	fa := df.ast

	for ni := range fa.Nodes {
		n := &fa.Nodes[ni]
		if n.File != 0 && n.File != df.srcID {
			continue
		}
		switch n.Kind {
		case NStructSpec, NUnionSpec, NEnumSpec:
			td := &fa.Tags[n.A-1]
			if td.Defined {
				df.deriveTag(td)
			}
		case NDecl:
			d := &fa.Decls[n.A-1]
			if df.insideFunc(n.Off) {
				continue
			}
			switch d.Kind {
			case 2:
				df.deriveTypedef(d, n)
			case 1:
				df.derivePrototype(d, n)
			default:
				if d.NameIdx != 0 {
					df.deriveGlobal(d, n)
				}
			}
		case NFuncDef:
			fd := &fa.Funcs[n.A-1]
			df.curFuncNode = uint32(ni)
			df.deriveFunction(fd, n)
		}
	}

	for ni := range fa.Nodes {
		n := &fa.Nodes[ni]
		if n.Kind != NDecl || (n.File != 0 && n.File != df.srcID) {
			continue
		}
		d := &fa.Decls[n.A-1]
		if d.Init == 0 || df.insideFunc(n.Off) {
			continue
		}
		w := &bodyWalk{opSeen: map[string]bool{}, operSeen: map[string]bool{},
			visited: map[uint32]bool{}}
		df.walkStmt(w, d.Init, 1, 0)
		for i := range w.lits {
			l := w.lits[i]
			l.FileID = int32(df.srcID)
			l.ID = int32(len(df.lits) + 1)
			df.lits = append(df.lits, l)
		}
	}

	for _, m := range df.pp.allMacros {
		if m.FileID != df.srcID {
			continue
		}
		df.deriveMacro(m)
	}

	scanMarkersRaw(df.srcRaw, func(kind string, line int32, text string) {
		df.markers = append(df.markers, MarkerRow{FileID: int32(df.srcID),
			Kind: kind, Line: line, Text: text})
	})

	for _, c := range df.pp.cfgs {
		if c.fileID != df.srcID || c.directive == "endif" {
			continue
		}
		expr := jtrunc(strings.TrimSpace(c.expr), 160)
		isCfg := b2i(strings.Contains(expr, "CONFIG_") ||
			strings.Contains(expr, "HAVE_") || strings.Contains(expr, "USE_"))
		df.cfgs = append(df.cfgs, ConfigBlockRow{FileID: int32(df.srcID),
			Directive: c.directive, Expr: expr, Line: c.line, IsConfig: isCfg})
	}

	for _, inc := range df.pp.includes {
		if inc.fromID != df.srcID {
			continue
		}
		df.imports = append(df.imports, ImportRow{FileID: int32(df.srcID),
			Target: inc.target, Kind: "include", Line: inc.line,
			IsExternal: 1, NNames: 1, IsRelative: b2i(!inc.sys)})
		if _, ok := df.incSeen[inc.line]; !ok {
			df.incSeen[inc.line] = true
			df.incRows = append(df.incRows, inc)
		}
	}

	df.deriveAttrs()
}

func (df *derivedFile) funcSpans() [][3]int32 {
	if df.fnSpans == nil {
		spans := make([][3]int32, 0, 16)
		for ni := range df.ast.Nodes {
			n := &df.ast.Nodes[ni]
			if n.Kind == NFuncDef {
				spans = append(spans, [3]int32{n.Off, n.End, int32(ni)})
			}
		}
		df.fnSpans = spans
	}
	return df.fnSpans
}

func (df *derivedFile) insideFunc(off int32) bool {
	spans := df.funcSpans()
	for i := range spans {
		if off >= spans[i][0] && off < spans[i][1] {
			return true
		}
	}
	return false
}

func (df *derivedFile) deriveAttrs() {
	for i := range df.ast.Attrs {
		a := &df.ast.Attrs[i]
		row := AttributeRow{FileID: int32(df.srcID), Name: jtrunc(a.Name, 80),
			Args: jtrunc(a.Args, 200), HasArgs: a.Args != "", Line: a.Line}

		best := uint32(0)
		spans := df.funcSpans()
		for i := range spans {
			if a.Off >= spans[i][0] && a.Off < spans[i][1] {
				best = uint32(spans[i][2])
				break
			}
		}
		if sid, ok := df.funcSymByNode[best]; ok {
			row.HasSymbolID = true
			row.SymbolID = sid
		}
		df.attrs = append(df.attrs, row)
	}
}

func (df *derivedFile) deriveTag(td *TagD) {
	fa := df.ast
	name := fa.name(td.NameIdx)
	if name == "" {
		name = "(anon@" + strconv.Itoa(int(td.Line)) + ")"
	}
	kind := td.Tag
	sym := SymbolRow{FileID: int32(df.srcID), Name: name, QualName: name,
		Kind: kind, LineStart: td.Line, IsPublic: 1, HasReturnType: false,
		LineEnd: td.LineEnd, NLines: td.LineEnd - td.Line + 1}
	localsym := df.internSym(&sym)

	switch kind {
	case "struct", "union":
		isUnion := kind == "union"
		var flds []fld
		ord := int32(0)
		for ci := uint32(0); ci < td.NChild; ci++ {
			fn := &fa.Nodes[td.Child0+ci]
			if fn.Kind != NField {
				continue
			}
			fdp := &fa.Fields[fn.A-1]
			fname := fa.name(fdp.NameIdx)
			ftype := fa.name(fdp.PtrTypeIdx)
			df.fields = append(df.fields, FieldRow{SymbolID: localsym,
				Ordinal: ord, Name: jtrunc(fname, 80), Type: jtrunc(ftype, 160),
				Line: fdp.Line, IsConst: b2i(fdp.IsConst), IsMutable: b2i(!fdp.IsConst),
				IsNullable: b2i(fdp.Ptr > 0), IsCollection: b2i(fdp.ArrayLen != 0),
				TypeDepth: fdp.Ptr})
			flds = append(flds, fld{ordinal: ord, ftype: fa.name(fdp.TypeIdx),
				fname: fname, ptr: fdp.Ptr, alen: fdp.ArrayLen,
				isFnptr: b2i(fdp.IsFnptr), depth: 0, inUnion: 0, line: fdp.Line})
			ord++
		}
		lay, tot, tail, ex, mal := layoutStruct(flds, isUnion)
		tpad := tail
		for i := range lay {
			if i < len(flds) {
				tpad += lay[i][3]
			}
			df.layout = append(df.layout, LayoutRowR{SymbolID: localsym,
				Ordinal: lay[i][0], ByteOff: lay[i][1], ByteSize: lay[i][2],
				PadBefore: lay[i][3], Exact: lay[i][4], PtrDepth: flds[i].ptr,
				ArrayLen: flds[i].alen, IsFnptr: flds[i].isFnptr,
				Depth: flds[i].depth, InUnion: flds[i].inUnion})
		}
		lines64 := int32(0)
		if tot > 0 {
			lines64 = (tot + 63) / 64
		}
		df.ssize = append(df.ssize, StructSizeRow{SymbolID: localsym,
			TotalSize: tot, TailPad: tail, TotalPad: tpad, MaxAlign: mal,
			Exact: ex, NLines64: lines64})
	case "enum":
		ord := int32(0)
		for ci := uint32(0); ci < td.NChild; ci++ {
			en := &fa.Nodes[td.Child0+ci]
			if en.Kind != NEnumerator {
				continue
			}
			ed := &fa.Enums[en.A-1]
			em := EnumMemberRow{SymbolID: localsym, Ordinal: ord,
				Name: jtrunc(fa.name(ed.NameIdx), 80), HasValue: ed.HasValue,
				NFields: 0}
			ord++
			if ed.HasValue {
				em.Value = jtrunc(fa.name(ed.ValueIdx), 60)
			}
			df.enums = append(df.enums, em)
		}
	}
}

func (df *derivedFile) deriveTypedef(d *DeclNode, n *Node) {
	name := df.ast.name(d.NameIdx)
	if name == "" {
		return
	}
	ty := df.ast.name(d.TypeIdx)
	df.symbols = append(df.symbols, SymbolRow{FileID: int32(df.srcID),
		Name: name, QualName: name, Kind: "typedef", LineStart: n.Line,
		ReturnType: jtrunc(ty, 120), HasReturnType: true, IsPublic: 1,
		LineEnd: n.Line, NLines: 1})
}

func (df *derivedFile) derivePrototype(d *DeclNode, n *Node) {
	name := df.ast.name(d.NameIdx)
	if name == "" {
		return
	}
	df.declared[name] = true
	df.decls = append(df.decls, DeclarationRow{FileID: int32(df.srcID),
		Name: name, Line: n.Line})
}

func (df *derivedFile) deriveGlobal(d *DeclNode, n *Node) {
	name := df.ast.name(d.NameIdx)
	if name == "" {
		return
	}
	g := GlobalRow{FileID: int32(df.srcID), Name: name,
		Type:       jtrunc(squeeze(df.ast.name(d.TypeIdx), ""), 120),
		Line:       n.Line,
		IsStatic:   b2i(d.Storage&FStatic != 0),
		IsConst:    b2i(d.Storage&FConstexpr != 0 || strings.Contains(df.ast.name(d.TypeIdx), "const")),
		IsVolatile: b2i(strings.Contains(df.ast.name(d.TypeIdx), "volatile")),
		IsAtomic:   b2i(strings.Contains(df.ast.name(d.TypeIdx), "_Atomic")),
		IsArray:    b2i(d.ArrayLen != 0), PtrDepth: d.Ptr,
		HasInit: b2i(d.Init != 0)}
	df.globals = append(df.globals, g)
}

func (df *derivedFile) deriveMacro(m *ppMacro) {
	nParams := int32(0)
	for _, p := range m.Params {
		if strings.TrimSpace(p) != "" {
			nParams++
		}
	}
	sig := jtrunc("define "+m.Name+" "+m.Raw, 200)
	sym := SymbolRow{FileID: int32(df.srcID), Name: m.Name, QualName: m.Name,
		Kind: "macro", LineStart: m.Line, Signature: sig, HasSignature: true,
		LineEnd: m.Line, NLines: 1}
	sid := df.internSym(&sym)
	body := jtrunc(m.Raw, 500)
	ml := int32(len([]rune(m.Raw)))
	df.macroName = append(df.macroName, m.Name)
	if _, ok := df.macroSID[m.Name]; !ok {
		df.macroSID[m.Name] = sid
	}
	df.macros = append(df.macros, MacroRow{SymbolID: sid,
		IsFunctionlike: b2i(m.IsFn), NParams: nParams, Body: body,
		HasBody: true, BodyLen: ml,
		IsMultiline: b2i(strings.HasSuffix(strings.TrimRight(m.Raw, " \t\r\n"), "\\")),
		NUses:       m.Uses})
}

func magicFor(tok string) bool {
	v, err := strconv.ParseInt(stripNumSuffix(strings.ReplaceAll(tok, "'", "")), 0, 64)
	if err != nil {
		return false
	}
	return magicOK[v]
}

func isFloatTok(t string) bool {
	body := stripNumSuffix(strings.ReplaceAll(t, "'", ""))
	if len(body) > 1 && (body[0] == '0' && (body[1] == 'x' || body[1] == 'X')) {
		return strings.ContainsAny(body[2:], "pP.")
	}
	return strings.ContainsAny(body, ".eE")
}

func numKind(t string) string {
	body := strings.ToLower(t)
	if strings.HasPrefix(body, "0x") {
		return "hex"
	}
	if strings.HasPrefix(body, "0b") {
		return "bin"
	}
	if len(body) > 1 && body[0] == '0' && !isFloatTok(t) {
		return "oct"
	}
	if isFloatTok(t) {
		return "float"
	}
	return "int"
}

func (df *derivedFile) deriveFunction(fd *FuncDef, n *Node) {
	fa := df.ast
	df.lastFuncNode = df.curFuncNode
	name := fa.name(fd.NameIdx)
	sig := fa.name(fd.SigIdx)
	ret := fa.name(fd.RetIdx)

	qual := name
	if fd.Storage&FStatic != 0 {
		qual = df.relPath + ":" + name
	}
	sym := &SymbolRow{FileID: int32(df.srcID), Name: name,
		QualName: jtrunc(qual, 400), Kind: "function", LineStart: n.Line,
		Signature: jtrunc(sig, 400), HasSignature: true,
		ReturnType: jtrunc(ret, 120), HasReturnType: true,
		LineEnd: fd.LineEnd, NLines: fd.LineEnd - n.Line + 1,
		Visibility: "extern"}
	if fd.Storage&FStatic != 0 {
		sym.Visibility = "static"
	}
	sym.IsStatic = b2i(fd.Storage&FStatic != 0)
	sym.IsInline = b2i(fd.Storage&FInline != 0)
	sym.IsPublic = b2i(fd.Storage&FStatic == 0)
	sym.IsEntrypoint = b2i(name == "main" || name == "LLVMFuzzerTestOneInput")
	sym.IsVariadic = b2i(fd.Variadic)
	sym.NParams = int32(fd.NParams)
	sym.IsTest = df.isTestF
	sym.IsGenerated = df.isGenF

	w := &bodyWalk{opSeen: map[string]bool{}, operSeen: map[string]bool{},
		visited: map[uint32]bool{}, toctouChk: map[string]bool{},
		toctouOpn: map[string]bool{}}
	if fd.Body != 0 {
		df.walkStmt(w, fd.Body, 1, 0)
	}
	sym.Cyclomatic = w.cyclomatic + 1
	sym.Cognitive = w.cognitive
	sym.MaxNesting = w.maxNesting
	sym.NLoops = w.nLoops
	sym.NBranches = w.nBranches
	sym.NSwitch = w.nSwitch
	sym.NCases = w.nCases
	sym.NLabels = w.nLabels
	sym.NGotos = w.nGotos
	sym.NReturns = w.nReturns
	sym.NDeref = w.nDeref
	sym.NCast = w.nCast
	sym.NSizeof = w.nSizeof
	sym.NArith = w.nArith
	sym.NCmp = w.nCmp
	sym.NShift = w.nShift
	sym.NTernary = w.nTernary
	sym.NMagic = w.nMagic
	sym.NFloatLit = w.nFloatLit
	sym.NPtrLocals = w.nPtrLocals
	sym.MaxLoopDepth = w.maxLoopDepth
	sym.NStaticAssert = w.nStaticAssert
	sym.NVolatile = w.hasVolatile
	sym.NRestrict = w.hasRestrict
	sym.NIntrinsic = w.nIntrinsic
	sym.NAtomic = w.nAtomic
	sym.NLikely = w.nLikely
	sym.NBuiltin = w.nBuiltin
	sym.NGetenv = w.nGetenv
	sym.NErrno = w.nErrno
	sym.NVla = w.nVla
	sym.NOperators = w.nOperators
	sym.NOperands = w.nOperands
	sym.NTokens = w.nTokens
	sym.NDistinctOperators = w.nDistOps
	sym.NDistinctOperands = w.nDistOper
	sym.NAssign = w.nAssign
	sym.NCompoundAssign = w.nCompoundAssign
	sym.NIncdec = w.nIncdec
	sym.NLogical = w.nLogical
	sym.NAddrof = w.nAddrof
	sym.NArrow = w.nArrow
	sym.NMemberAcc = w.nArrow + w.nDot
	sym.NSubscript = w.nSubscript
	sym.NBitop = w.nBitop
	sym.NStringLit = w.nStringLit
	sym.NNullCheck = w.nNullCheck
	sym.CallInLoop = w.callInLoop
	sym.AllocInLoop = w.allocInLoop
	sym.IOInLoop = w.ioInLoop
	sym.LockInLoop = w.lockInLoop
	sym.BranchInLoop = w.branchInLoop
	r := &sym.SymbolRare
	r.SwitchInLoop = w.switchInLoop
	r.LibmInLoop = w.libmInLoop
	r.DivInLoop = w.divInLoop
	r.StrlenInLoop = w.strlenInLoop
	r.RetNull = w.retNull
	r.RetNeg = w.retNeg
	r.RetZero = w.retZero
	r.RetVal = w.retVal
	r.RetVoid = w.retVoid

	if fd.Body != 0 {
		b0, b1 := fa.Nodes[fd.Body].Off, fa.Nodes[fd.Body].End
		sym.Sloc = countSlocSpan(df.srcRaw, b0, b1)
	}

	nDyn := int32(0)
	for _, c := range w.calls {
		if c.isCall && c.fnptr {
			nDyn++
		}
	}
	sym.NCalls = int32(len(w.calls))
	sym.NDynamicCalls = nDyn
	sym.NFnptrCalls = nDyn
	sym.NCallsites = sym.NCalls

	sid := df.internSym(sym)
	df.funcSymByNode[df.lastFuncNode] = sid

	np := int32(0)
	for pi := uint32(0); pi < fd.NParams; pi++ {
		pn := &fa.Nodes[fd.Param0+pi]
		pd := &fa.Params[pn.A-1]
		pname := fa.name(pd.NameIdx)
		ptype := fa.name(pd.TypeIdx)
		if ptype == "" && pname == "void" {
			continue
		}
		if pname == "..." || pd.Variadic {
			pa := ParamRow{SymbolID: sid, Pos: np, IsVariadic: 1,
				IsMutable: 1, Type: "..."}
			df.params = append(df.params, pa)
			np++
			sym.IsVariadic = 1
			continue
		}
		pa := ParamRow{SymbolID: sid, Pos: np,
			Type:       jtrunc(ptype, 120),
			IsRef:      b2i(pd.Ptr > 0),
			IsMutable:  b2i(!pd.IsConst),
			IsNullable: b2i(pd.Ptr > 0),
			TypeDepth:  pd.Ptr}
		if pname != "" {
			pa.Name = jtrunc(pname, 80)
			pa.HasName = true
		}
		df.params = append(df.params, pa)
		if pd.Ptr > 0 {
			df.symbols[sid-1].NPtrParams++
		}
		np++
	}
	sym.NParams = np

	sym.NLocals = int32(len(w.locals))
	for i := range w.locals {
		w.locals[i].SymbolID = sid
		w.locals[i].Ordinal = int32(i)
		df.locals = append(df.locals, w.locals[i])
	}
	nLit := int32(0)
	for i := range w.lits {
		lk := w.lits[i].Kind
		if lk == "int" || lk == "hex" || lk == "oct" || lk == "bin" {
			if nLit >= 200 {
				continue
			}
			nLit++
		}
		w.lits[i].SymbolID = sid
		w.lits[i].HasSym = true
		w.lits[i].FileID = int32(df.srcID)
		w.lits[i].ID = int32(len(df.lits) + 1)
		df.lits = append(df.lits, w.lits[i])
	}
	for i := range w.addrs {
		w.addrs[i].SymbolID = sid
		w.addrs[i].HasSym = true
		w.addrs[i].FileID = int32(df.srcID)
		w.addrs[i].ID = int32(len(df.addrs) + 1)
		w.addrs[i].Kind = "addr"
		df.addrs = append(df.addrs, w.addrs[i])
	}

	extra := df.applyCallHeuristics(sid, w)
	sym.NMemcpy = extra.nMemcpy
	sym.NAlloc = extra.nAlloc
	sym.NAllocsite = extra.nAllocsite
	sym.NFree = extra.nFree
	sym.NLockAcquire = extra.nLockAcq
	sym.NLockRelease = extra.nLockRel
	sym.NEpoll = extra.nEpoll
	sym.NUring = extra.nUring
	sym.NKqueue = extra.nKqueue
	sym.NEventCreate = extra.nEventCreate
	sym.NEventWait = extra.nEventWait
	sym.NMemory = extra.nMemcpy + extra.nAlloc + extra.nFree
	r.NEvTimeoutIndefinite = extra.nTimeoutInf
	r.NEvTimeoutZero = extra.nTimeoutZero
	r.NEvBatchOne = extra.nBatchOne
	r.NKqTimerZeroData = extra.nKqTimerZero

	df.textHeuristics(sym, w, fd, n)

	byName := map[string][]int32{}
	var order []string
	for _, c := range w.calls {
		if !c.isCall || c.fnptr {
			continue
		}
		if byName[c.name] == nil {
			order = append(order, c.name)
		}
		byName[c.name] = append(byName[c.name], c.line)
	}
	for _, nm := range order {
		df.pendNames = append(df.pendNames, nm)
		df.pendLines = append(df.pendLines, byName[nm])
		df.pendSym = append(df.pendSym, sid)
		df.pendFile = append(df.pendFile, int32(df.srcID))
		df.pendModule = append(df.pendModule, df.modID)
	}
	df.fnNames = append(df.fnNames, name)
	df.fnSyms = append(df.fnSyms, sid)
	df.fnFiles = append(df.fnFiles, int32(df.srcID))
	df.fnModules = append(df.fnModules, df.modID)
}

func countSlocSpan(src []byte, off, end int32) int32 {
	if off < 0 || int(end) > len(src) || end < off {
		return 0
	}
	n := int32(0)
	seg := src[off:end]
	start := 0
	for i := 0; i <= len(seg); i++ {
		if i == len(seg) || seg[i] == '\n' {
			line := seg[start:i]
			for _, c := range line {
				if c != ' ' && c != '\t' && c != '\r' {
					n++
					break
				}
			}
			start = i + 1
		}
	}
	return n
}

func (df *derivedFile) textHeuristics(sym *SymbolRow, w *bodyWalk, fd *FuncDef, n *Node) {
	if fd.Body == 0 {
		return
	}
	fa := df.ast
	b0, b1 := fa.Nodes[fd.Body].Off, fa.Nodes[fd.Body].End
	if b0 < 0 || b1 > int32(len(df.srcRaw)) || b1 < b0 {
		return
	}
	rawBody := df.srcRaw[b0:b1]
	blankBody := rawBody
	if df.blank != nil && b1 <= int32(len(df.blank)) {
		blankBody = df.blank[b0:b1]
	}
	r := &sym.SymbolRare

	sym.NCommentLines = countCommentLines(rawBody)
	if df.nlRaw != nil {
		if doc, _ := leadingComment(df.srcRaw, df.nlRaw, int(n.Line)); doc {
			sym.HasDoc = 1
		}
	}
	sym.NBodyBytes = int32(runeLen(rawBody))

	if hasStr(blankBody, "8_t") || hasStr(blankBody, "16_t") || hasStr(blankBody, "32_t") {
		r.NNarrowCast = int32(countNarrowCasts(blankBody))
	}
	known := map[string]bool{}
	for i := range w.locals {
		known[w.locals[i].Name] = true
	}
	for pi := uint32(0); pi < fd.NParams; pi++ {
		pn := &fa.Nodes[fd.Param0+pi]
		pd := &fa.Params[pn.A-1]
		if nm := fa.name(pd.NameIdx); nm != "" {
			known[nm] = true
		}
	}
	nSignCmp := int32(0)
	scanSignCmps(blankBody, func(h signCmpHit) {
		if known[h.name] {
			nSignCmp++
		}
	})
	r.NSignCmp = nSignCmp
	if hasStr(blankBody, "rand") {
		r.NWeakRandom = int32(countWeakRandom(blankBody))
	}
	if hasStr(blankBody, "<<") || hasStr(blankBody, ">>") {
		r.NShiftVar = int32(countShiftVar(blankBody))
	}
	if hasStr(blankBody, "realloc") {
		r.NReallocSelf = int32(countReallocSelf(blankBody))
	}
	if hasStr(blankBody, "assert") {
		r.NAssertSide = int32(countAssertSide(blankBody))
	}
	if hasStr(blankBody, "free") {
		n := int32(0)
		scanFrees(blankBody, func(fh freeHit) {
			if fh.afterPl < len(blankBody) && derefAfter(blankBody[fh.afterPl:], fh.name) {
				n++
			}
		})
		r.NFreeThenUse = n
	}
	nCC := int32(0)
	for _, cn := range w.castIdents {
		if known[cn] {
			for i := range w.locals {
				if w.locals[i].Name == cn && w.locals[i].IsConst == 1 {
					nCC++
					break
				}
			}
			for pi := uint32(0); pi < fd.NParams; pi++ {
				pn := &fa.Nodes[fd.Param0+pi]
				pd := &fa.Params[pn.A-1]
				if fa.name(pd.NameIdx) == cn && pd.IsConst {
					nCC++
					break
				}
			}
		}
	}
	r.NConstCast = nCC
	r.NToctou = w.toctou()
	if fd.Variadic {
		nf := int32(0)
		for _, c := range w.calls {
			for _, p := range printfFns {
				if c.name == p {
					nf++
					break
				}
			}
		}
		r.NVariadicFmt = nf
	}

	nEv := 0
	for i := range df.evops {
		if df.evops[i].SymbolID == sym.ID {
			nEv++
		}
	}
	if nEv > 0 {
		fl := scanEvFlags(blankBody)
		r.NEtReg, r.NOneshotReg, r.NWriteReady = i32(fl.etReg), i32(fl.oneshotReg), i32(fl.writeReady)
		r.NErrFlag, r.NRearm, r.NDereg = i32(fl.errFlag), i32(fl.rearm), i32(fl.dereg)
		r.NEagain, r.NEintr = i32(fl.eagain), i32(fl.eintr)
		r.NUringRes, r.NUringSqpoll = i32(fl.uringRes), i32(fl.uringSqpoll)
		r.NNonblockSet, r.NEventDestroy = i32(fl.nonblockSet), i32(fl.eventDestroy)
		r.NUringSqe, r.NUringSeen, r.NUringUdata = i32(fl.uringSqe), i32(fl.uringSeen), i32(fl.uringUdata)
		r.NUringLink, r.NUringStreamOps = i32(fl.uringLink), i32(fl.uringStreamOps)
		r.NUringTeardown, r.NKqTimer, r.NKqReceipt = i32(fl.uringTeardown), i32(fl.kqTimer), i32(fl.kqReceipt)
		r.NUringRing, r.NUringBarrier = i32(fl.uringRing), i32(fl.uringBarrier)
	}

	{
		usedNS := map[string]bool{}
		for i := range df.apiuses {
			if df.apiuses[i].SymbolID == sym.ID {
				usedNS[df.apiuses[i].NS] = true
			}
		}
		if len(usedNS) > 0 {
			for _, gn := range guardNames {
				if !nsIntersects(usedNS, guardNS[gn]) {
					continue
				}
				v := int32(countGuard(gn, blankBody))
				switch gn {
				case "ret_neg":
					r.NRetNegCheck = v
				case "domain":
					r.NDomainGuard = v
				case "uchar":
					r.NUcharCast = v
				case "errno_zero":
					r.NErrnoZero = v
				case "endptr":
					r.NEndptr = v
				case "va_end":
					r.NVaEnd = v
				case "map_failed":
					r.NMapFailed = v
				case "monotonic":
					r.NMonotonicClock = v
				case "stacksz_array":
					r.NStackszArray = v
				case "ptr_ovf_check":
					r.NPtrOvfCheck = v
				case "calloc_sizeof_first":
					r.NCallocTransposed = v
				case "va_arg_array":
					r.NVaArgArr = v
				}
			}
		}
	}

	emitHz := func(pat, cat string, n int) {
		if n > 0 {
			df.hazards = append(df.hazards, HazardRow{SymbolID: sym.ID,
				Pattern: pat, Category: cat, N: int32(n)})
		}
	}
	emitHz("ptr_cast", "integer", countPtrCast(blankBody))
	if hasStr(blankBody, "<<") || hasStr(blankBody, ">>") {
		emitHz("shift", "integer", countStr(blankBody, "<<")+countStr(blankBody, ">>"))
	}
	if hasStr(blankBody, "sizeof") {
		emitHz("mul_sizeof", "integer", countMulSizeof(blankBody))
	}
	emitHz("fixed_buffer", "memory", countFixedBuffer(blankBody))
	emitHz("vla", "memory", countVLAPat(blankBody))
	emitHz("signed_cmp", "integer", countSignedCmp(blankBody))
}

type callSiteRec struct {
	name    string
	line    int32
	fnptr   bool
	isCall  bool
	node    uint32
	argsOff int32
	argsEnd int32
}

func (w *bodyWalk) noteOp(s string) {
	w.nOperators++
	if !w.opSeen[s] {
		w.opSeen[s] = true
		w.nDistOps++
	}
}

func (w *bodyWalk) noteOper(s string) {
	w.nOperands++
	if !w.operSeen[s] {
		w.operSeen[s] = true
		w.nDistOper++
	}
}

func (df *derivedFile) walkStmt(w *bodyWalk, idx uint32, scopeDepth int32, loopDepth int32) {
	fa := df.ast
	if idx == 0 || int(idx) >= len(fa.Nodes) {
		return
	}

	if w.visited[idx] {
		return
	}
	w.visited[idx] = true
	n := &fa.Nodes[idx]
	if scopeDepth > w.maxNesting {
		w.maxNesting = scopeDepth
	}
	if loopDepth > w.maxLoopDepth {
		w.maxLoopDepth = loopDepth
	}
	walkExpr := func(e uint32) { df.walkStmt(w, e, scopeDepth, loopDepth) }

	switch n.Kind {
	case NCompoundStmt:
		a, b := n.A, n.B
		for i := uint32(0); i < b; i++ {
			df.walkStmt(w, a+i, scopeDepth+1, loopDepth)
		}

	case NDeclStmt:
		a, b := n.A, n.B
		for i := uint32(0); i < b; i++ {
			c := &fa.Nodes[a+i]
			if c.Kind != NDecl {
				continue
			}
			d := &fa.Decls[c.A-1]
			typ := fa.name(d.TypeIdx)
			isConst := strings.Contains(typ, "const") || d.Storage&FConstexpr != 0
			lr := LocalRow{Line: c.Line,
				Name:       jtrunc(fa.name(d.NameIdx), 80),
				Type:       jtrunc(squeeze(typ, ""), 120),
				IsConst:    b2i(isConst),
				IsMutable:  b2i(!isConst),
				HasInit:    b2i(d.Init != 0),
				InLoop:     b2i(loopDepth > 0),
				ScopeDepth: b2i8(scopeDepth)}
			w.locals = append(w.locals, lr)
			if d.Ptr > 0 {
				w.nPtrLocals++
			}
			if d.ArrayLen == -1 {
				w.nVla++
			}
			if d.Init != 0 {
				df.walkStmt(w, d.Init, scopeDepth, loopDepth)
			}
		}

	case NExprStmt:
		if n.A != 0 {
			walkExpr(n.A)
		}

	case NIf:
		w.cyclomatic++
		w.nBranches++
		if loopDepth > 0 {
			w.branchInLoop++
		}
		if scopeDepth-1 > 1 {
			w.cognitive += scopeDepth - 1
		} else {
			w.cognitive++
		}
		w.noteOper("if")
		walkExpr(n.A)
		df.walkStmt(w, n.B, scopeDepth, loopDepth)
		if n.C != 0 {
			df.walkStmt(w, n.C, scopeDepth, loopDepth)
		}

	case NSwitch:
		w.nSwitch++
		w.nBranches++
		if loopDepth > 0 {
			w.switchInLoop++
		}
		if scopeDepth-1 > 1 {
			w.cognitive += scopeDepth - 1
		} else {
			w.cognitive++
		}
		w.noteOper("switch")
		walkExpr(n.A)
		df.walkStmt(w, n.B, scopeDepth, loopDepth)

	case NCase:
		if n.A != 0 {
			w.cyclomatic++
			w.nBranches++
			w.nCases++
			if loopDepth > 0 {
				w.branchInLoop++
			}
			w.noteOper("case")
			walkExpr(n.A)
		}
		df.walkStmt(w, n.B, scopeDepth, loopDepth)

	case NWhile:
		w.nLoops++
		w.cyclomatic++
		if scopeDepth-1 > 1 {
			w.cognitive += scopeDepth - 1
		} else {
			w.cognitive++
		}
		w.noteOper("while")
		walkExpr(n.A)
		df.walkStmt(w, n.B, scopeDepth, loopDepth+1)

	case NDo:
		w.nLoops++
		w.noteOper("do")
		df.walkStmt(w, n.A, scopeDepth, loopDepth+1)
		walkExpr(n.B)

	case NFor:
		w.nLoops++
		w.cyclomatic++
		if scopeDepth-1 > 1 {
			w.cognitive += scopeDepth - 1
		} else {
			w.cognitive++
		}
		w.noteOper("for")
		if n.A != 0 {
			df.walkStmt(w, n.A, scopeDepth, loopDepth)
		}
		if n.B != 0 {
			walkExpr(n.B)
		}
		if n.C != 0 {
			walkExpr(n.C)
		}
		df.walkStmt(w, n.D, scopeDepth, loopDepth+1)

	case NReturn:
		w.nReturns++
		w.noteOper("return")
		if n.A == 0 {
			w.retVoid++
		} else {
			switch df.retShape(n.A) {
			case 1:
				w.retNull++
			case 2:
				w.retNeg++
			case 3:
				w.retZero++
			default:
				w.retVal++
			}
		}
		if n.A != 0 {
			walkExpr(n.A)
		}

	case NGoto:
		w.nGotos++
		w.noteOper("goto")

	case NLabel:
		w.nLabels++
		if n.B != 0 {
			df.walkStmt(w, n.B, scopeDepth, loopDepth)
		}

	case NStaticAssert:
		w.nStaticAssert++

	case NAsm, NBreak, NContinue:

	case NBinary:
		op := punctTable[n.Flags&0xFF]
		w.noteOp(op)
		if n.Flags == uint16(PSlash) && loopDepth > 0 {
			w.divInLoop++
		}
		switch n.Flags {
		case uint16(PAmp), uint16(PPipe), uint16(PCaret), uint16(PLsh), uint16(PRsh):
			w.nBitop++
		}
		switch n.Flags {
		case uint16(PAmpAmp), uint16(PPipePip):
			w.cyclomatic++
			w.nLogical++
		case uint16(PPlus), uint16(PMinus), uint16(PStar), uint16(PSlash), uint16(PMod):
			w.nArith++
		case uint16(mustPunct("==")), uint16(mustPunct("!=")), uint16(PLt), uint16(PGt), uint16(PLe), uint16(mustPunct(">=")):
			w.nCmp++
		case uint16(PLsh), uint16(PRsh):
			w.nShift++
		}

		if n.Flags == uint16(mustPunct("==")) || n.Flags == uint16(mustPunct("!=")) {
			if df.isNullLit(n.A) || df.isNullLit(n.B) {
				w.nNullCheck++
			}
		}
		walkExpr(n.A)
		walkExpr(n.B)

	case NAssign:
		op := punctTable[n.Flags&0xFF]
		w.noteOp(op)
		if n.Flags == uint16(PEq) {
			w.nAssign++
		} else {
			w.nCompoundAssign++
		}

		switch n.Flags {
		case uint16(PAmpEq), uint16(PPipeEq), uint16(PCaretEq), uint16(PLshEq), uint16(PRshEq):
			w.nBitop++
		}
		if lhs := fa.Nodes[n.A]; lhs.Kind == NIdent {
			if df.isGlobalName(fa.name(lhs.A)) {
				w.nGlobalWrite++
				w.noteOper(fa.name(lhs.A))
			}
		}
		walkExpr(n.A)
		walkExpr(n.B)

	case NCond:
		w.nTernary++
		w.cyclomatic++
		w.noteOp("?")
		walkExpr(n.A)
		walkExpr(n.B)
		walkExpr(n.C)

	case NUnary:
		switch n.Flags {
		case uint16(PStar):
			w.nDeref++
			w.noteOp("*")
		case uint16(PInc), uint16(PDec):
			w.nIncdec++
			w.noteOp(punctTable[n.Flags])
		case uint16(PAmp):
			w.noteOp("&")
			if o := fa.Nodes[n.A]; o.Kind == NIdent {
				w.nAddrof++
				na := fa.name(o.A)
				if na != "" && !df.isFunctionName(na) {
					w.addrs = append(w.addrs, AddrTakenRow{Name: jtrunc(na, 80),
						Line: int32(fa.Nodes[n.A].Line)})
				}
			}
		case uint16(PTilde):
			w.nBitop++
		default:
			w.noteOp(punctTable[n.Flags&0xFF])
		}
		if n.A != 0 {
			walkExpr(n.A)
		}

	case NPostfix:
		w.nIncdec++
		w.noteOp(punctTable[n.Flags&0xFF])
		walkExpr(n.A)

	case NCall:
		callee := fa.Nodes[n.A]
		name := ""
		fnptr := false
		if callee.Kind == NIdent {
			name = fa.name(callee.A)
		} else {
			fnptr = true
		}
		argsOff, argsEnd := int32(0), int32(0)
		if n.B > 0 {
			first := &fa.Nodes[n.C]
			last := &fa.Nodes[n.C+n.B-1]
			argsOff, argsEnd = first.Off, last.End
		}
		w.calls = append(w.calls, callSiteRec{name: name, fnptr: fnptr,
			isCall: true, node: idx, argsOff: argsOff, argsEnd: argsEnd,
			line: int32(n.Line)})
		if loopDepth > 0 {
			w.callInLoop++
			switch name {
			case "malloc", "calloc", "realloc", "strdup", "strndup",
				"aligned_alloc", "reallocarray":
				w.allocInLoop++
			case "sqrt", "exp", "log", "log2", "log10", "pow", "sin", "cos",
				"tan", "atan", "atan2", "tgamma", "lgamma", "erf", "fmod",
				"cbrt", "hypot", "floor", "ceil", "round":
				w.libmInLoop++
			case "strlen", "strnlen":
				w.strlenInLoop++
			}
			switch hazardFuncs[name] {
			case "io":
				w.ioInLoop++
			case "concurrency":
				w.lockInLoop++
			}
		}
		if n.B > 0 {
			arg0 := &fa.Nodes[n.C]
			if arg0.Kind == NIdent {
				an := fa.name(arg0.A)
				switch name {
				case "access", "faccessat", "stat", "lstat":
					w.toctouChk[an] = true
				case "open", "openat", "fopen", "creat":
					w.toctouOpn[an] = true
				}
			}
		}
		if name == "getenv" || name == "secure_getenv" {
			w.nGetenv++
		}
		if isIntrinsicCall(name) {
			w.nIntrinsic++
		}
		if strings.HasPrefix(name, "__atomic_") || strings.HasPrefix(name, "__sync_") ||
			strings.HasPrefix(name, "__c11_atomic_") {
			w.nAtomic++
		}
		if name == "__builtin_expect" {
			w.nLikely++
		}
		if strings.HasPrefix(name, "__builtin_") {
			w.nBuiltin++
		}
		walkExpr(n.A)
		for i := uint32(0); i < n.B; i++ {
			walkExpr(n.C + i)
		}

	case NMember:
		if n.Flags&1 != 0 {
			w.nDeref++
			w.nArrow++
		} else {
			w.nDot++
		}
		w.noteOp(".")
		walkExpr(n.B)

	case NIndex:
		w.nSubscript++
		w.noteOp("[")
		walkExpr(n.A)
		walkExpr(n.B)

	case NCast:
		w.nCast++
		w.noteOp("cast")
		if n.B != 0 && fa.Nodes[n.B].Kind == NIdent {
			w.castIdents = append(w.castIdents, fa.name(fa.Nodes[n.B].A))
		}
		walkExpr(n.B)

	case NSizeofT, NAlignofT:
		w.nSizeof++
		w.noteOper("sizeof")

	case NSizeofE:
		w.nSizeof++
		w.noteOper("sizeof")
		walkExpr(n.A)

	case NVaArg:
		w.noteOper("__builtin_va_arg")
		walkExpr(n.A)

	case NIdent:
		nm := fa.name(n.A)
		if nm == "errno" {
			w.nErrno++
		}
		w.noteOper(nm)

	case NNumLit:
		tok := fa.name(n.A)
		w.noteOper(tok)
		kind := numKind(tok)
		magic := !magicFor(tok)
		if kind == "float" {
			w.nFloatLit++
			magic = true
		}
		if magic {
			w.nMagic++
		}
		w.lits = append(w.lits, LiteralRow{Kind: kind, Value: jtrunc(tok, 40),
			Line: int32(n.Line), IsMagic: b2i(magic)})

	case NCharLit:
		tok := fa.name(n.A)
		w.noteOper(tok)
		w.lits = append(w.lits, LiteralRow{Kind: "char", Value: jtrunc(tok, 40),
			Line: int32(n.Line)})

	case NStrLit:
		tok := fa.name(n.A)
		w.nStringLit++
		w.noteOper(tok)
		w.lits = append(w.lits, LiteralRow{Kind: "string",
			Value: jtrunc(dequoteLit(tok), 200), Line: int32(n.Line)})
		if secretShaped(dequoteLit(tok)) {
			w.lits = append(w.lits, LiteralRow{Kind: "_secret",
				Value: jtrunc(dequoteLit(tok), 200), Line: int32(n.Line)})
		}

	case NStmtExpr:
		if n.A != 0 {
			df.walkStmt(w, n.A, scopeDepth, loopDepth)
		}

	case NParen:
		w.noteOp("(")
		if n.A != 0 {
			walkExpr(n.A)
		}

	case NComma:
		w.noteOp(",")
		walkExpr(n.A)
		walkExpr(n.B)

	case NCompoundLit:
		walkExpr(n.B)

	case NGeneric:
		w.noteOper("_Generic")
		walkExpr(n.A)
		for i := uint32(0); i < n.C; i++ {
			asc := &fa.Assocs[n.B+i]
			if asc.Expr != 0 {
				walkExpr(asc.Expr)
			}
		}

	case NInitList:
		a, b := n.A, n.B
		for i := uint32(0); i < b; i++ {
			it := &fa.Nodes[a+i]
			if it.B != 0 {
				walkExpr(it.B)
			}
		}

	case NBad:

	}
}

func b2i8(v int32) int32 { return v }

func (df *derivedFile) isNullLit(idx uint32) bool {
	if idx == 0 {
		return false
	}
	nd := df.ast.Nodes[idx]
	if nd.Kind == NIdent {
		nm := df.ast.name(nd.A)
		return nm == "NULL" || nm == "nullptr"
	}
	if nd.Kind == NParen {
		return df.isNullLit(nd.A)
	}
	return false
}

func (df *derivedFile) isGlobalName(name string) bool {
	if len(df.globals) == 0 {
		return false
	}
	return df.globalSet()[name]
}

func (df *derivedFile) retShape(idx uint32) int {
	nd := df.ast.Nodes[idx]
	switch nd.Kind {
	case NIdent:
		nm := df.ast.name(nd.A)
		if nm == "NULL" || nm == "nullptr" {
			return 1
		}
	case NNullPtr:
		return 1
	case NParen:
		if nd.A != 0 {
			return df.retShape(nd.A)
		}
	case NUnary:
		if nd.Flags == uint16(PMinus) && nd.A != 0 {
			c := df.ast.Nodes[nd.A]
			if c.Kind == NNumLit {
				tx := df.ast.name(c.A)
				if len(tx) > 1 {
					digits := true
					for i := 1; i < len(tx); i++ {
						if tx[i] < '0' || tx[i] > '9' {
							digits = false
							break
						}
					}
					if digits {
						return 2
					}
				}
			}
		}
	case NNumLit:
		if df.ast.name(nd.A) == "0" {
			return 3
		}
	case NBoolLit:
		return 0
	}
	return 0
}

func (df *derivedFile) isFunctionName(name string) bool {
	for i := range df.fnNames {
		if df.fnNames[i] == name {
			return true
		}
	}
	return false
}

func dequoteLit(s string) string {
	s = strings.TrimPrefix(s, "u8")
	s = strings.TrimPrefix(s, "u")
	s = strings.TrimPrefix(s, "U")
	s = strings.TrimPrefix(s, "L")
	if len(s) >= 2 && s[0] == '"' {
		s = s[1 : len(s)-1]
	}
	return s
}

func splitTop(s string) []string {
	var out []string
	depth := 0
	start := 0
	for i := 0; i < len(s); i++ {
		switch s[i] {
		case '(', '[':
			depth++
		case ')', ']':
			depth--
		case ',':
			if depth == 0 {
				out = append(out, strings.TrimSpace(s[start:i]))
				start = i + 1
			}
		}
	}
	if strings.TrimSpace(s[start:]) != "" || len(out) > 0 {
		out = append(out, strings.TrimSpace(s[start:]))
	}
	return out
}

func (df *derivedFile) applyCallHeuristics(sid int32, w *bodyWalk) (extra symExtra) {
	type hazKey struct {
		pat, cat string
	}
	hazN := map[hazKey]int32{}
	hazFirst := map[hazKey]int32{}
	apiRows := 0
	for _, c := range w.calls {
		if !c.isCall {
			continue
		}
		argText := df.rawSpan(c.argsOff, c.argsEnd, 200)
		args := splitTop(argText)
		name := c.name

		if memopFnSet[name] {
			dst, src, sarg := memopArgs(name, args)
			sizeBuf := ""
			if op, ok := sizeofOperand(sarg); ok {
				if nm, ok2 := firstIdent(op); ok2 {
					sizeBuf = nm
				}
			} else if nm, ok2 := firstIdent(sarg); ok2 && sarg != "" && sarg[0] != '-' &&
				!(len(sarg) > 0 && sarg[0] >= '0' && sarg[0] <= '9') {
				sizeBuf = nm
			}
			dt := lastPathTail(dst)
			if dt == "" {
				dt = dst
			}
			df.memops = append(df.memops, MemopRow{ID: int32(len(df.memops) + 1),
				SymbolID: sid, FileID: int32(df.srcID), Fn: name,
				Dst: jtrunc(dst, 120), Src: jtrunc(src, 120),
				SizeArg: jtrunc(sarg, 120), SizeBuf: jtrunc(sizeBuf, 80),
				DstTail: jtrunc(dt, 80), Line: c.line})
			extra.nMemcpy++
		}

		if isAllocName(name) {
			if libcAllocNames[name] {
				extra.nAlloc++
			}
			if !c.fnptr {
				sz := jtrunc(squeeze(argText, ""), 150)
				df.allocs = append(df.allocs, AllocSiteRow{ID: int32(len(df.allocs) + 1),
					SymbolID: sid, FileID: int32(df.srcID), Fn: name,
					SizeExpr: sz, Line: c.line})
				extra.nAllocsite++
				if !strings.Contains(sz, "sizeof") {
					extra.nAllocNoSizeof++
				}
			}
		}
		if name == "free" && !c.fnptr {
			extra.nFree++
		}

		if isLockShaped(name) {
			if lockAcquireName(name) {
				extra.nLockAcq++
			}
			if lockReleaseName(name) {
				extra.nLockRel++
			}
			if len(args) > 0 {
				if nm, ok := firstIdent(args[len(args)-1]); ok {
					df.locks = append(df.locks, LockRowR{ID: int32(len(df.locks) + 1),
						SymbolID: sid, FileID: int32(df.srcID), Name: jtrunc(nm, 80),
						Line: c.line})
				}
			}
		}

		if isEventOp(name) {
			a := jtrunc(squeeze(argText, ""), 180)
			df.evops = append(df.evops, EventOpRow{ID: int32(len(df.evops) + 1),
				SymbolID: sid, FileID: int32(df.srcID), Family: eventFamily(name),
				Fn: name, Args: a, Line: c.line})
			switch {
			case strings.HasPrefix(name, "epoll_"):
				extra.nEpoll++
			case strings.HasPrefix(name, "io_uring_"):
				extra.nUring++
			default:
				extra.nKqueue++
			}
			if eventCreateFn[name] {
				extra.nEventCreate++
			}
			if eventWaitFn[name] {
				extra.nEventWait++
			}
			ti, hasT := evTimeoutIdx[name]
			if hasT {
				parts := splitTop(argText)
				bi := evBatchIdx[name]
				if len(parts) > bi && parts[bi] == "1" {
					extra.nBatchOne++
				}
				if len(parts) > ti && len(parts) > bi && parts[bi] != "0" {
					tmo := parts[ti]
					if tmo == "NULL" || tmo == "-1" {
						extra.nTimeoutInf++
					} else if tmo == "0" {
						extra.nTimeoutZero++
					}
				}
			} else if name == "EV_SET" {
				parts := splitTop(argText)
				if len(parts) > 5 && strings.Contains(parts[2], "EVFILT_TIMER") &&
					parts[5] == "0" {
					extra.nKqTimerZero++
				}
			}
		}

		if ns := funcToNS[name]; ns != "" && apiRows < 12 {
			df.apiuses = append(df.apiuses, APIUseRow{ID: int32(len(df.apiuses) + 1),
				SymbolID: sid, FileID: int32(df.srcID), NS: ns, Fn: name, Line: c.line})
			apiRows++
		}

		if cat := hazardFuncs[name]; cat != "" {
			k := hazKey{name, cat}
			if hazN[k] == 0 {
				hazFirst[k] = c.line
			}
			hazN[k]++
		}
	}

	for _, c := range w.calls {
		if !c.isCall {
			continue
		}
		k := hazKey{c.name, hazardFuncs[c.name]}
		if k.cat == "" || hazN[k] == 0 {
			continue
		}
		df.hazards = append(df.hazards, HazardRow{SymbolID: sid,
			Pattern: jtrunc(k.pat, 80), Category: k.cat, N: hazN[k],
			FirstLine: hazFirst[k]})
		hazN[k] = 0
	}

	for _, l := range w.lits {
		if l.Kind == "_secret" {
			df.secrets = append(df.secrets, SecretCandidateRow{ID: int32(len(df.secrets) + 1),
				SymbolID: sid, HasSym: true, FileID: int32(df.srcID),
				Value: l.Value, Line: l.Line})
		}
	}
	return
}

type symExtra struct {
	nMemcpy, nAlloc, nAllocsite, nAllocNoSizeof int32
	nFree, nLockAcq, nLockRel                   int32
	nEpoll, nUring, nKqueue                     int32
	nEventCreate, nEventWait                    int32
	nTimeoutInf, nTimeoutZero                   int32
	nBatchOne, nKqTimerZero                     int32
}

func (w *bodyWalk) toctou() int32 {
	n := int32(0)
	for k := range w.toctouChk {
		if w.toctouOpn[k] {
			n++
		}
	}
	return n
}

var memopFnSet = map[string]bool{"memcpy": true, "memmove": true, "strcpy": true,
	"strncpy": true, "strcat": true, "strncat": true, "memset": true,
	"sprintf": true, "snprintf": true}

func memopArgs(fn string, args []string) (dst, src, sizeArg string) {
	switch fn {
	case "memset":
		if len(args) > 0 {
			dst = args[0]
		}
		if len(args) > 2 {
			sizeArg = args[2]
		}
	case "snprintf", "sprintf":
		if len(args) > 0 {
			dst = args[0]
		}
		if len(args) > 1 {
			sizeArg = args[1]
		}
		if len(args) > 2 {
			src = args[2]
		}
	default:
		if len(args) > 0 {
			dst = args[0]
		}
		if len(args) > 1 {
			src = args[1]
		}
		if len(args) > 2 {
			sizeArg = args[2]
		}
	}
	return
}

func sizeofOperand(s string) (string, bool) {
	s = strings.TrimSpace(s)
	if !strings.HasPrefix(s, "sizeof") {
		return "", false
	}
	rest := strings.TrimSpace(s[6:])
	if strings.HasPrefix(rest, "(") {
		inner := strings.TrimSuffix(strings.TrimPrefix(rest, "("), ")")
		inner = strings.TrimSpace(inner)
		if strings.Contains(inner, "struct ") || strings.Contains(inner, "union ") ||
			strings.Contains(inner, "enum ") {
			return "", false
		}
		return inner, true
	}
	if rest == "" {
		return "", false
	}
	return rest, true
}

func lockAcquireName(name string) bool {
	low := strings.ToLower(name)
	if !strings.Contains(low, "lock") {
		if low == "sem_wait" || low == "sem_trywait" || low == "pthread_mutex_trylock" {
			return true
		}
		return false
	}
	return !strings.Contains(low, "unlock")
}

func lockReleaseName(name string) bool {
	low := strings.ToLower(name)
	return strings.Contains(low, "unlock")
}

func isEventOp(fn string) bool {
	if strings.HasPrefix(fn, "epoll_") || strings.HasPrefix(fn, "io_uring_") {
		return true
	}
	return eventWaitFn[fn] || eventCreateFn[fn] || fn == "kqueue" || fn == "EV_SET"
}

func isAllocName(name string) bool {
	if libcAllocNames[name] {
		return true
	}
	low := strings.ToLower(name)
	for _, suf := range [...]string{"alloc", "free", "strdup", "memdup"} {
		if len(low) > len(suf) && strings.HasSuffix(low, suf) {
			return true
		}
	}
	return false
}

func isIntrinsicCall(name string) bool {
	for _, p := range builtinPrefixes {
		if strings.HasPrefix(name, p) {
			return true
		}
	}
	return false
}

func secretShaped(s string) bool {
	if len(s) < 12 || strings.Contains(s, " ") {
		return false
	}
	low := strings.ToLower(s)
	for _, k := range [...]string{"passw", "secret", "api_key", "apikey",
		"token", "credential", "private_key", "auth_key", "access_key"} {
		if strings.Contains(low, k) {
			return true
		}
	}
	return false
}

var markerKinds = [...]string{"TODO", "FIXME", "XXX", "HACK", "BUG", "NOTE",
	"WARNING", "OPTIMIZE", "REVIEW", "DEPRECATED", "SAFETY", "PANIC", "UNSAFE"}

func scanMarkersRaw(src []byte, fn func(kind string, line int32, text string)) {
	ln := int32(1)
	start := 0
	for i := 0; i <= len(src); i++ {
		if i == len(src) || src[i] == '\n' {
			line := src[start:i]
			scanMarkerLine(line, ln, fn)
			ln++
			start = i + 1
		}
	}
}

func scanMarkerLine(line []byte, n int32, fn func(kind string, line int32, text string)) {

	sigil := false
	for i := 0; i+1 < len(line); i++ {
		if line[i] == '/' && line[i+1] == '/' {
			sigil = true
			break
		}
		if line[i] == '-' && line[i+1] == '-' {
			sigil = true
			break
		}
	}
	for _, c := range line {
		if c == '#' || c == '*' {
			sigil = true
			break
		}
	}
	if !sigil {
		return
	}
	textDone := false
	for p := 0; p < len(line); {
		if !c23IsIdentStart(line[p]) {
			p++
			continue
		}

		if p > 0 && c23IsIdentPart(line[p-1]) {
			p = identEndAt(line, p)
			continue
		}
		e := identEndAt(line, p)
		w := string(line[p:e])
		hit := ""
		for _, k := range markerKinds {
			if w == k {
				hit = k
				break
			}
		}
		if hit != "" {

			if e < len(line) && c23IsIdentPart(line[e]) {
				p = e
				continue
			}
			q := e
			for q < len(line) && (line[q] == ' ' || line[q] == '\t') {
				q++
			}
			if q < len(line) && (line[q] == ':' || line[q] == '-' || line[q] == '(') {
				if !textDone {
					fn(hit, n, jtrunc(strings.TrimSpace(string(line)), 200))
					textDone = true
				}
				return
			}
		}
		p = e
	}
}

func identEndAt(b []byte, i int) int {
	for i < len(b) && c23IsIdentPart(b[i]) {
		i++
	}
	return i
}

var (
	PAmpEq   = mustPunct("&=")
	PPipeEq  = mustPunct("|=")
	PCaretEq = mustPunct("^=")
	PLshEq   = mustPunct("<<=")
	PRshEq   = mustPunct(">>=")
)

type c23tu struct {
	root      int32
	fa        *FileAST
	pp        *preprocessor
	lexErrs   []lexErr
	perrs     []parseError
	claimed   []int32
	files     []*derivedFile
	ferrs     []int32
	fmissing  []int32
	redundant bool
}

type c23run struct {
	g         *Graph
	abs       string
	mu        sync.Mutex
	claim     map[string]int32
	turn      int32
	nPanics   int32
	paths     map[string]int32
	absID     map[string]int32
	quiet     bool
	keepTrees bool
}

func (e *extractor) runC23(abs string, g *Graph, parseIDs []int32, quiet bool, step int, keepTrees bool) []*fileOut {
	cr := &c23run{g: g, abs: abs, quiet: quiet, keepTrees: keepTrees,
		claim: map[string]int32{}, paths: map[string]int32{},
		absID: map[string]int32{}}
	for _, id := range parseIDs {
		f := &g.Files[id-1]
		cr.paths[filepath.Join(abs, filepath.FromSlash(f.Path()))] = id
	}
	for i := range g.Files {
		ap := filepath.Join(abs, filepath.FromSlash(g.Files[i].Path()))
		if _, ok := cr.absID[ap]; !ok {
			cr.absID[ap] = g.Files[i].ID
		}
	}
	tus := make([]*c23tu, len(parseIDs))
	workers := min(defaultParseWorkers, len(parseIDs))
	if workers < 1 {
		workers = 1
	}
	jobs := make(chan int)
	var wg sync.WaitGroup
	sem := newByteWindow(parseByteBudget)
	for k := 0; k < workers; k++ {
		wg.Go(func() {
			for i := range jobs {
				sz := fileCharge(int64(cr.g.Files[parseIDs[i]-1].Bytes))
				sem.take(sz)
				tu := cr.parseTU(int32(i), parseIDs[i])
				if tu != nil {
					cr.deriveTU(tu)
					if !cr.keepTrees {
						tu.fa = nil
					}
					tu.pp = nil
				}
				tus[i] = tu
				sem.give(sz)
			}
		})
	}
	go func() {
		for i := range parseIDs {
			jobs <- i
		}
		close(jobs)
	}()
	wg.Wait()

	ppSrcMu.Lock()
	ppSrcCache = map[string][]byte{}
	ppSrcMu.Unlock()

	var nFail int32
	outs := make([]*fileOut, len(g.Files))
	for a := range tus {
		tu := tus[a]
		if tu == nil {
			nFail++
			continue
		}
		if len(tu.files) == 0 && !tu.redundant {
			nFail++
		}
		for k, df := range tu.files {
			fid := df.file.ID
			fl := &g.Files[fid-1]
			fl.NParseErrors = tu.ferrs[k]
			fl.NMissingNodes = tu.fmissing[k]
			if outs[fid-1] == nil {
				outs[fid-1] = e.fileOutFrom(cr, df)
			}
		}
	}
	g.FilesFailed += nFail
	return outs
}

func (cr *c23run) parseTU(pos int32, fid int32) (tu *c23tu) {
	tu = &c23tu{root: fid}
	claiming := true
	defer func() {
		if r := recover(); r != nil {
			atomic.AddInt32(&cr.nPanics, 1)
			tu = &c23tu{root: fid}
		}
		if claiming {
			for atomic.LoadInt32(&cr.turn) != pos {
				time.Sleep(50 * time.Microsecond)
			}
			cr.mu.Lock()
			if tu.pp != nil {
				for _, src := range tu.pp.files {
					p := src.path
					if id, ok := cr.paths[p]; ok {
						if _, cdone := cr.claim[p]; !cdone {
							cr.claim[p] = fid
							tu.claimed = append(tu.claimed, id)
						} else if id == fid {
							tu.redundant = true
						}
					}
				}
			}
			cr.mu.Unlock()
			atomic.AddInt32(&cr.turn, 1)
			claiming = false
		}
	}()
	f := &cr.g.Files[fid-1]
	abs := filepath.Join(cr.abs, filepath.FromSlash(f.Path()))
	if _, ok := ppCachedRead(abs); !ok {
		claiming = false
		atomic.AddInt32(&cr.turn, 1)
		return nil
	}
	tu.fa = &FileAST{}
	tu.pp = newPP(abs, nil, &tu.lexErrs)
	toks := tu.pp.run(abs)
	srcs := map[uint32][]byte{}
	for id, fsrc := range tu.pp.fileByID {
		srcs[id] = fsrc.raw
	}
	p := newParser(tu.fa, toks, srcs, 0, &tu.perrs)
	p.parseTU()
	putTokBuf(toks)
	tu.pp.out = nil
	for _, fsrc := range tu.pp.fileByID {
		fsrc.toks = nil
	}
	return tu
}

func (cr *c23run) deriveTU(tu *c23tu) {
	tu.files = make([]*derivedFile, 0, len(tu.claimed))
	tu.ferrs = make([]int32, 0, len(tu.claimed))
	tu.fmissing = make([]int32, 0, len(tu.claimed))
	for _, fid := range tu.claimed {
		df, nerrs, nmiss := cr.deriveOne(tu, fid)
		if df != nil {
			tu.files = append(tu.files, df)
			tu.ferrs = append(tu.ferrs, nerrs)
			tu.fmissing = append(tu.fmissing, nmiss)
		}
	}
	if tu.fa != nil && cr.keepTrees {
		cr.mu.Lock()
		cr.g.trees = append(cr.g.trees, cgTree{root: tu.root, fa: tu.fa})
		cr.mu.Unlock()
	}
	if !cr.keepTrees {
		for _, df := range tu.files {
			df.ast = nil
			df.pp = nil
		}
	}
}

func (cr *c23run) deriveOne(tu *c23tu, fid int32) (df *derivedFile, nerrs int32, nmiss int32) {
	defer func() {
		if r := recover(); r != nil {
			atomic.AddInt32(&cr.nPanics, 1)
			df = nil
		}
	}()
	f := &cr.g.Files[fid-1]
	abs := filepath.Join(cr.abs, filepath.FromSlash(f.Path()))
	raw, ok := ppCachedRead(abs)
	if !ok {
		if d, err := os.ReadFile(abs); err == nil {
			raw = d
		} else {
			return nil, 0, 0
		}
	}
	var srcID uint32
	srcID = 1
	for _, fsrc := range tu.pp.files {
		if fsrc.path == abs {
			srcID = fsrc.id
			break
		}
	}
	bp := blankPool.Get().(*[]byte)
	blank := blankBuf(*bp, raw)
	nRaw := nlOffsets(raw)
	df = newDerivedFile(tu.fa, tu.pp, raw, srcID)
	df.blank = blank
	df.nlRaw = nRaw
	df.file = FileRow{ID: fid, Path: f.Path(), ModuleID: f.ModuleID}
	df.globalFileID = fid
	df.isTestF = f.IsTest
	df.isGenF = f.IsGenerated
	df.modID = f.ModuleID
	nErrs := 0
	if srcID == 1 {
		nErrs += len(tu.lexErrs)
	}
	for i := range tu.perrs {
		if tu.perrs[i].file == srcID {
			nErrs++
		}
	}
	df.file.NParseErrors = int32(nErrs)
	df.file.NMissing = int32(len(tu.pp.cond))
	df.derive()
	*bp = blank
	blankPool.Put(bp)
	return df, int32(nErrs), int32(len(tu.pp.cond))
}

func (e *extractor) fileOutFrom(cr *c23run, df *derivedFile) *fileOut {
	fo := &fileOut{symA: newSymBlockN(len(df.symbols))}
	block := fo.symA
	incCtx := map[int32]string{}
	sysCtx := map[int32]bool{}
	for _, inc := range df.incRows {
		if _, ok := incCtx[inc.line]; !ok {
			incCtx[inc.line] = inc.resolved
			sysCtx[inc.line] = inc.sys
		}
	}
	gfid := df.globalFileID
	for i := range df.symbols {
		s := &df.symbols[i]
		w := symW{ID: int32(i + 1), FileID: gfid, ModuleID: df.modID,
			Name: s.Name, QualName: s.QualName, Kind: s.Kind,
			LineStart: s.LineStart, Signature: s.Signature,
			ReturnType: s.ReturnType, HasSignature: s.HasSignature,
			HasReturnType: s.HasReturnType, NParams: s.NParams,
			IsPublic: s.IsPublic, IsStatic: s.IsStatic,
			IsAbstract: s.IsAbstract, IsOverride: s.IsOverride,
			IsTest: s.IsTest, IsEntrypoint: s.IsEntrypoint,
			IsGenerated: s.IsGenerated, Sloc: s.Sloc,
			NCommentLines: s.NCommentLines, HasDoc: s.HasDoc,
			Cyclomatic: s.Cyclomatic, Cognitive: s.Cognitive,
			MaxNesting: s.MaxNesting, NTokens: s.NTokens,
			NOperators: s.NOperators, NOperands: s.NOperands,
			NDistinctOperators: s.NDistinctOperators,
			NDistinctOperands:  s.NDistinctOperands,
			NLoops:             s.NLoops, NBranches: s.NBranches, NReturns: s.NReturns,
			NSwitch: s.NSwitch, NCases: s.NCases, NLabels: s.NLabels,
			NGotos: s.NGotos, MaxLoopDepth: s.MaxLoopDepth,
			CallInLoop: s.CallInLoop, AllocInLoop: s.AllocInLoop,
			IOInLoop: s.IOInLoop, LockInLoop: s.LockInLoop,
			BranchInLoop: s.BranchInLoop, NLocals: s.NLocals,
			NCmp: s.NCmp, NArith: s.NArith, NShift: s.NShift,
			NFloatLit: s.NFloatLit, NMagic: s.NMagic,
			NNullCheck: s.NNullCheck, NCalls: s.NCalls,
			NDynamicCalls:    s.NDynamicCalls,
			NUnresolvedCalls: s.NUnresolvedCalls, FanIn: s.FanIn,
			FanOut: s.FanOut, NCallsites: s.NCallsites,
			IsRecursive: s.IsRecursive, RiskScore: s.RiskScore,
			NMemory: s.NMemory, NAlloc: s.NAlloc, NIO: s.NIO,
			NStdio: s.NStdio, NExec: s.NExec, NLibm: s.NLibm,
			NInteger: s.NInteger, NConcurrency: s.NConcurrency,
			NReentrancy: s.NReentrancy, IsInline: s.IsInline,
			IsVariadic: s.IsVariadic, NPtrLocals: s.NPtrLocals,
			NDeref: s.NDeref, NCast: s.NCast, NSizeof: s.NSizeof,
			NIntrinsic: s.NIntrinsic, NAtomic: s.NAtomic,
			NRestrict: s.NRestrict, NLikely: s.NLikely, NBuiltin: s.NBuiltin}
		if fo.symN == 0 {
			fo.symLo = block.count()
		}
		r := rowRare(&s.SymbolRare)
		if r != (symRare{}) {
			w.rare = block.addRare(r)
			fo.rareN++
		} else {
			w.rare = -1
		}
		block.add(&w)
		fo.symN++
	}
	for i := range df.params {
		p := &df.params[i]
		fo.params = append(fo.params, paramW{SymbolID: p.SymbolID, Pos: p.Pos,
			Name: p.Name, HasName: p.HasName, Type: p.Type,
			IsVariadic: p.IsVariadic, IsRef: p.IsRef, IsMutable: p.IsMutable,
			IsNullable: p.IsNullable, TypeDepth: p.TypeDepth})
	}
	for i := range df.fields {
		p := &df.fields[i]
		fo.fields = append(fo.fields, fieldW{SymbolID: p.SymbolID,
			Ordinal: p.Ordinal, Name: p.Name, Type: p.Type,
			Visibility: p.Visibility, Line: p.Line, IsStatic: p.IsStatic,
			IsConst: p.IsConst, IsMutable: p.IsMutable,
			IsNullable: p.IsNullable, IsCollection: p.IsCollection,
			IsUntyped: p.IsUntyped, HasDefault: p.HasDefault,
			TypeDepth: p.TypeDepth})
	}
	for i := range df.locals {
		p := &df.locals[i]
		fo.locals = append(fo.locals, localW{SymbolID: p.SymbolID,
			Ordinal: p.Ordinal, Name: p.Name, Type: p.Type, Line: p.Line,
			IsConst: p.IsConst, IsMutable: p.IsMutable, IsUntyped: p.IsUntyped,
			HasInit: p.HasInit, InLoop: p.InLoop, ScopeDepth: p.ScopeDepth})
	}
	for i := range df.lits {
		p := &df.lits[i]
		fo.literals = append(fo.literals, literalW{ID: p.ID,
			SymbolID: p.SymbolID, HasSym: p.HasSym, FileID: gfid,
			Kind: p.Kind, Value: p.Value, Line: p.Line, IsMagic: p.IsMagic})
	}
	for i := range df.markers {
		p := &df.markers[i]
		fo.markers = append(fo.markers, markerW{ID: p.ID, FileID: gfid,
			SymbolID: p.SymbolID, HasSym: p.HasSym, Kind: p.Kind,
			Line: p.Line, Text: p.Text})
	}
	for i := range df.imports {
		p := &df.imports[i]
		im := importW{FileID: gfid, Target: p.Target, Kind: p.Kind,
			Line: p.Line, IsExternal: p.IsExternal, IsRelative: p.IsRelative,
			NNames: p.NNames}
		if resolved, ok := incCtx[p.Line]; ok && resolved != "" {
			if tid, ok2 := cr.absID[filepath.Clean(resolved)]; ok2 {
				im.TargetID, im.HasTargetID = tid, true
				im.IsExternal = 0
			}
		}
		fo.imports = append(fo.imports, im)
	}
	for i := range df.hazards {
		p := &df.hazards[i]
		fo.hazards = append(fo.hazards, hazardW{SymbolID: p.SymbolID,
			Pattern: p.Pattern, Category: p.Category, N: p.N,
			FirstLine: p.FirstLine})
	}
	for i := range df.enums {
		p := &df.enums[i]
		fo.enums = append(fo.enums, enumW{SymbolID: p.SymbolID,
			Ordinal: p.Ordinal, Name: p.Name, Value: p.Value,
			HasValue: p.HasValue, NFields: p.NFields})
	}
	for i := range df.layout {
		p := &df.layout[i]
		fo.layout = append(fo.layout, LayoutRow{SymbolID: p.SymbolID,
			Ordinal: p.Ordinal, ByteOff: p.ByteOff, ByteSize: p.ByteSize,
			PadBefore: p.PadBefore, Exact: p.Exact, PtrDepth: p.PtrDepth,
			ArrayLen: p.ArrayLen, IsFnptr: p.IsFnptr, Depth: p.Depth,
			InUnion: p.InUnion})
	}
	for i := range df.ssize {
		p := &df.ssize[i]
		fo.ssize = append(fo.ssize, StructSize{SymbolID: p.SymbolID,
			TotalSize: p.TotalSize, TailPad: p.TailPad, TotalPad: p.TotalPad,
			MaxAlign: p.MaxAlign, Exact: p.Exact, NLines64: p.NLines64})
	}
	for i := range df.decls {
		p := &df.decls[i]
		fo.decls = append(fo.decls, declW{ID: p.ID, FileID: gfid,
			Name: p.Name, Line: p.Line})
	}
	for i := range df.addrs {
		p := &df.addrs[i]
		fo.addrs = append(fo.addrs, addrW{ID: p.ID, SymbolID: p.SymbolID,
			HasSym: p.HasSym, FileID: gfid, Name: p.Name, Line: p.Line,
			Kind: p.Kind})
	}
	for i := range df.secrets {
		p := &df.secrets[i]
		fo.secrets = append(fo.secrets, secretW{ID: p.ID, SymbolID: p.SymbolID,
			HasSym: p.HasSym, FileID: gfid, Value: p.Value, Line: p.Line})
	}
	for i := range df.allocs {
		p := &df.allocs[i]
		fo.allocs = append(fo.allocs, allocW{ID: p.ID, SymbolID: p.SymbolID,
			FileID: gfid, Fn: p.Fn, SizeExpr: p.SizeExpr, Line: p.Line})
	}
	for i := range df.memops {
		p := &df.memops[i]
		fo.memops = append(fo.memops, memopW{ID: p.ID, SymbolID: p.SymbolID,
			FileID: gfid, Fn: p.Fn, Dst: p.Dst, Src: p.Src,
			SizeArg: p.SizeArg, SizeBuf: p.SizeBuf, DstTail: p.DstTail,
			Line: p.Line})
	}
	for i := range df.macros {
		p := &df.macros[i]
		fo.macros = append(fo.macros, macroW{SymbolID: p.SymbolID,
			IsFunctionlike: p.IsFunctionlike, NParams: p.NParams,
			Body: p.Body, HasBody: p.HasBody, BodyLen: p.BodyLen,
			IsMultiline: p.IsMultiline, NUses: p.NUses})
		fo.macroNames = append(fo.macroNames, df.macroName[i])
	}
	for i := range df.globals {
		p := &df.globals[i]
		fo.globals = append(fo.globals, globalW{ID: p.ID, FileID: gfid,
			ModuleID: df.modID, Name: p.Name, Type: p.Type, Line: p.Line,
			IsStatic: p.IsStatic, IsConst: p.IsConst, IsVolatile: p.IsVolatile,
			IsAtomic: p.IsAtomic, IsArray: p.IsArray, PtrDepth: p.PtrDepth,
			HasInit: p.HasInit})
	}
	for i := range df.cfgs {
		p := &df.cfgs[i]
		fo.cfgs = append(fo.cfgs, cfgW{ID: p.ID, FileID: gfid,
			Directive: p.Directive, Expr: p.Expr, Line: p.Line,
			IsConfig: p.IsConfig})
	}
	for i := range df.locks {
		p := &df.locks[i]
		fo.locks = append(fo.locks, lockW{ID: p.ID, SymbolID: p.SymbolID,
			FileID: gfid, Name: p.Name, Line: p.Line})
	}
	for i := range df.attrs {
		p := &df.attrs[i]
		fo.attrs = append(fo.attrs, attrW{ID: p.ID, SymbolID: p.SymbolID,
			HasSymbolID: p.HasSymbolID, FileID: gfid, Name: p.Name,
			Args: p.Args, HasArgs: p.HasArgs, Line: p.Line})
	}
	for i := range df.evops {
		p := &df.evops[i]
		fo.evops = append(fo.evops, evopW{ID: p.ID, SymbolID: p.SymbolID,
			FileID: gfid, Family: p.Family, Fn: p.Fn, Args: p.Args,
			Line: p.Line})
	}
	for i := range df.apiuses {
		p := &df.apiuses[i]
		fo.apiuses = append(fo.apiuses, apiuseW{ID: p.ID, SymbolID: p.SymbolID,
			FileID: gfid, NS: p.NS, Fn: p.Fn, Line: p.Line})
	}
	for i := range df.pendNames {
		fo.pendSID = append(fo.pendSID, df.pendSym[i])
		fo.pendFID = append(fo.pendFID, df.pendFile[i])
		fo.pendMID = append(fo.pendMID, df.pendModule[i])
		fo.pendName = append(fo.pendName, df.pendNames[i])
		fo.pendLine = append(fo.pendLine, df.pendLines[i])
	}
	for k, nm := range df.fnNames {
		fo.funcs = append(fo.funcs, fnSite{name: nm, sid: df.fnSyms[k],
			fid: df.fnFiles[k], mid: df.fnModules[k]})
	}
	return fo
}

func rowRare(s *SymbolRare) symRare {
	return symRare{
		SwitchInLoop:         s.SwitchInLoop,
		LibmInLoop:           s.LibmInLoop,
		DivInLoop:            s.DivInLoop,
		StrlenInLoop:         s.StrlenInLoop,
		RetNull:              s.RetNull,
		RetNeg:               s.RetNeg,
		RetZero:              s.RetZero,
		RetVal:               s.RetVal,
		RetVoid:              s.RetVoid,
		NFnptrCalls:          s.NFnptrCalls,
		NMacroCalls:          s.NMacroCalls,
		NExternalCalls:       s.NExternalCalls,
		NFree:                s.NFree,
		NConstCast:           s.NConstCast,
		NToctou:              s.NToctou,
		NLockAcquire:         s.NLockAcquire,
		NLockRelease:         s.NLockRelease,
		NNarrowCast:          s.NNarrowCast,
		NSignCmp:             s.NSignCmp,
		NVariadicFmt:         s.NVariadicFmt,
		NMemcpy:              s.NMemcpy,
		NAllocsite:           s.NAllocsite,
		NGlobalWrite:         s.NGlobalWrite,
		NErrno:               s.NErrno,
		NWeakRandom:          s.NWeakRandom,
		NShiftVar:            s.NShiftVar,
		NReallocSelf:         s.NReallocSelf,
		NVla:                 s.NVla,
		NGetenv:              s.NGetenv,
		NAssertSide:          s.NAssertSide,
		NFreeThenUse:         s.NFreeThenUse,
		NEpoll:               s.NEpoll,
		NUring:               s.NUring,
		NKqueue:              s.NKqueue,
		NEventWait:           s.NEventWait,
		NEtReg:               s.NEtReg,
		NOneshotReg:          s.NOneshotReg,
		NWriteReady:          s.NWriteReady,
		NErrFlag:             s.NErrFlag,
		NRearm:               s.NRearm,
		NDereg:               s.NDereg,
		NEagain:              s.NEagain,
		NEintr:               s.NEintr,
		NUringRes:            s.NUringRes,
		NUringRing:           s.NUringRing,
		NUringBarrier:        s.NUringBarrier,
		NUringSqpoll:         s.NUringSqpoll,
		NNonblockSet:         s.NNonblockSet,
		NEventCreate:         s.NEventCreate,
		NEventDestroy:        s.NEventDestroy,
		NUringSqe:            s.NUringSqe,
		NUringSeen:           s.NUringSeen,
		NUringUdata:          s.NUringUdata,
		NUringLink:           s.NUringLink,
		NUringStreamOps:      s.NUringStreamOps,
		NUringTeardown:       s.NUringTeardown,
		NEvTimeoutIndefinite: s.NEvTimeoutIndefinite,
		NEvTimeoutZero:       s.NEvTimeoutZero,
		NEvBatchOne:          s.NEvBatchOne,
		NKqTimer:             s.NKqTimer,
		NKqTimerZeroData:     s.NKqTimerZeroData,
		NKqReceipt:           s.NKqReceipt,
		NRetNegCheck:         s.NRetNegCheck,
		NDomainGuard:         s.NDomainGuard,
		NUcharCast:           s.NUcharCast,
		NErrnoZero:           s.NErrnoZero,
		NEndptr:              s.NEndptr,
		NVaEnd:               s.NVaEnd,
		NMapFailed:           s.NMapFailed,
		NMonotonicClock:      s.NMonotonicClock,
		NStackszArray:        s.NStackszArray,
		NPtrOvfCheck:         s.NPtrOvfCheck,
		NCallocTransposed:    s.NCallocTransposed,
		NVaArgArr:            s.NVaArgArr,
	}
}

type cgTree struct {
	root int32
	fa   *FileAST
}

type cgBlob struct {
	b []byte
}

func (w *cgBlob) u8(v uint8) { w.b = append(w.b, v) }
func (w *cgBlob) u32(v uint32) {
	w.b = append(w.b, byte(v), byte(v>>8), byte(v>>16), byte(v>>24))
}
func (w *cgBlob) i32(v int32) { w.u32(uint32(v)) }
func (w *cgBlob) i64(v int64) {
	w.u32(uint32(v))
	w.u32(uint32(v >> 32))
}
func (w *cgBlob) bl(v bool) uint8 {
	if v {
		return 1
	}
	return 0
}
func (w *cgBlob) str(s string) {
	w.u32(uint32(len(s)))
	w.b = append(w.b, s...)
}
func cgTag8(s string) uint8 {
	switch s {
	case "union":
		return 1
	case "enum":
		return 2
	}
	return 0
}
func cgUntag8(v uint8) string {
	switch v {
	case 1:
		return "union"
	case 2:
		return "enum"
	}
	return "struct"
}

func cgTreesBlob(g *Graph) []byte {
	w := &cgBlob{b: make([]byte, 0, 1<<20)}
	w.u32(uint32(len(g.trees)))
	for _, t := range g.trees {
		fa := t.fa
		w.i32(t.root)
		w.u32(uint32(len(fa.Names)))
		for _, nm := range fa.Names {
			w.str(nm)
		}
		w.u32(uint32(len(fa.Nodes)))
		for i := range fa.Nodes {
			n := &fa.Nodes[i]
			w.u32(uint32(n.Kind))
			w.u32(uint32(n.Flags))
			w.u32(n.A)
			w.u32(n.B)
			w.u32(n.C)
			w.u32(n.D)
			w.u32(n.File)
			w.i32(n.Off)
			w.i32(n.End)
			w.i32(n.Line)
			w.i32(n.Col)
		}
		w.u32(uint32(len(fa.Funcs)))
		for i := range fa.Funcs {
			f := &fa.Funcs[i]
			w.u32(f.NameIdx)
			w.u32(f.SigIdx)
			w.u32(f.RetIdx)
			w.u32(f.Param0)
			w.u32(f.NParams)
			w.u32(f.Body)
			w.i32(f.LineEnd)
			w.u32(uint32(f.Storage))
			w.u8(w.bl(f.Variadic))
			w.u8(w.bl(f.KR))
			w.u32(f.Attr0)
			w.u32(f.NAttr)
		}
		w.u32(uint32(len(fa.Decls)))
		for i := range fa.Decls {
			d := &fa.Decls[i]
			w.u32(d.NameIdx)
			w.u32(d.TypeIdx)
			w.u32(d.Typename)
			w.i32(d.Bitfield)
			w.i32(d.ArrayLen)
			w.i32(d.Ptr)
			w.u32(d.Init)
			w.u32(uint32(d.Storage))
			w.u8(d.Kind)
			w.i32(d.Line)
		}
		w.u32(uint32(len(fa.Params)))
		for i := range fa.Params {
			d := &fa.Params[i]
			w.u32(d.NameIdx)
			w.u32(d.TypeIdx)
			w.i32(d.Ptr)
			w.i32(d.ArrayLen)
			w.u32(uint32(d.Storage))
			w.u8(w.bl(d.Variadic))
			w.u8(w.bl(d.Unnamed))
			w.u8(w.bl(d.IsConst))
			w.i32(d.Line)
		}
		w.u32(uint32(len(fa.Tags)))
		for i := range fa.Tags {
			d := &fa.Tags[i]
			w.u32(d.NameIdx)
			w.u8(cgTag8(d.Tag))
			w.u32(d.Child0)
			w.u32(d.NChild)
			w.u32(d.UnderlyingIdx)
			w.u8(w.bl(d.HasUnderlying))
			w.u8(w.bl(d.Defined))
			w.i32(d.Line)
			w.i32(d.LineEnd)
		}
		w.u32(uint32(len(fa.Fields)))
		for i := range fa.Fields {
			d := &fa.Fields[i]
			w.u32(d.NameIdx)
			w.u32(d.TypeIdx)
			w.u32(d.PtrTypeIdx)
			w.i32(d.Ptr)
			w.i32(d.ArrayLen)
			w.i32(d.Bitfield)
			w.u8(w.bl(d.IsFnptr))
			w.u8(w.bl(d.IsConst))
			w.i32(d.Depth)
			w.i32(d.Line)
		}
		w.u32(uint32(len(fa.Enums)))
		for i := range fa.Enums {
			d := &fa.Enums[i]
			w.u32(d.NameIdx)
			w.u32(d.ValueIdx)
			w.u8(w.bl(d.HasValue))
			w.i32(d.Line)
		}
		w.u32(uint32(len(fa.Types)))
		for i := range fa.Types {
			d := &fa.Types[i]
			w.u32(d.TextIdx)
			w.i32(d.Ptr)
			w.u8(w.bl(d.Array))
			w.i32(d.ArrayLen)
			w.u8(w.bl(d.IsFn))
		}
		w.u32(uint32(len(fa.Inits)))
		for i := range fa.Inits {
			d := &fa.Inits[i]
			w.u32(d.FieldIdx)
			w.i64(d.Index)
			w.u8(w.bl(d.HasIndex))
			w.u8(w.bl(d.IsList))
		}
		w.u32(uint32(len(fa.Assocs)))
		for i := range fa.Assocs {
			d := &fa.Assocs[i]
			w.u32(d.TypeIdx)
			w.u8(w.bl(d.IsDefault))
			w.u32(d.Expr)
		}
		w.u32(uint32(len(fa.Attrs)))
		for i := range fa.Attrs {
			a := &fa.Attrs[i]
			w.str(a.Name)
			w.str(a.Args)
			w.i32(a.Line)
			w.i32(a.Off)
			w.i32(a.End)
		}
	}
	return w.b
}

func cgTreesParse(b []byte, g *Graph) error {
	r := &cgRd{b: b}
	if !r.u32ok() {
		return fmt.Errorf("trees: truncated header")
	}
	n := r.u32v()
	if n > 1<<20 {
		return fmt.Errorf("trees: implausible tree count %d", n)
	}
	for k := uint32(0); k < n; k++ {
		fa := &FileAST{}
		t := cgTree{fa: fa}
		var ok bool
		if t.root, ok = r.i32v(); !ok {
			return fmt.Errorf("trees: truncated root")
		}
		if !r.u32ok() {
			return fmt.Errorf("trees: truncated names")
		}
		nn := r.u32v()
		if nn > 1<<26 {
			return fmt.Errorf("trees: implausible name count %d", nn)
		}
		fa.Names = make([]string, 0, min(nn, 1<<20))
		for i := uint32(0); i < nn; i++ {
			s, ok := r.strv()
			if !ok {
				return fmt.Errorf("trees: truncated name")
			}
			fa.Names = append(fa.Names, s)
		}
		if fa.Nodes, ok = r.nodes(); !ok {
			return fmt.Errorf("trees: truncated nodes")
		}
		if fa.Funcs, ok = r.funcs(); !ok {
			return fmt.Errorf("trees: truncated funcs")
		}
		if fa.Decls, ok = r.decls(); !ok {
			return fmt.Errorf("trees: truncated decls")
		}
		if fa.Params, ok = r.params(); !ok {
			return fmt.Errorf("trees: truncated params")
		}
		if fa.Tags, ok = r.tags(); !ok {
			return fmt.Errorf("trees: truncated tags")
		}
		if fa.Fields, ok = r.fields(); !ok {
			return fmt.Errorf("trees: truncated fields")
		}
		if fa.Enums, ok = r.enums(); !ok {
			return fmt.Errorf("trees: truncated enums")
		}
		if fa.Types, ok = r.types(); !ok {
			return fmt.Errorf("trees: truncated types")
		}
		if fa.Inits, ok = r.inits(); !ok {
			return fmt.Errorf("trees: truncated inits")
		}
		if fa.Assocs, ok = r.assocs(); !ok {
			return fmt.Errorf("trees: truncated assocs")
		}
		if !r.u32ok() {
			return fmt.Errorf("trees: truncated attrs")
		}
		na := r.u32v()
		if na > 1<<24 {
			return fmt.Errorf("trees: implausible attr count %d", na)
		}
		for i := uint32(0); i < na; i++ {
			nm, ok1 := r.strv()
			ar, ok2 := r.strv()
			ln, ok3 := r.i32v()
			of, ok4 := r.i32v()
			en, ok5 := r.i32v()
			if !ok1 || !ok2 || !ok3 || !ok4 || !ok5 {
				return fmt.Errorf("trees: truncated attrs")
			}
			fa.Attrs = append(fa.Attrs, AttrRec{Name: nm, Args: ar, Line: ln, Off: of, End: en})
		}
		g.trees = append(g.trees, t)
	}
	return nil
}

type cgRd struct {
	b []byte
	p int
}

func (r *cgRd) need(n int) bool { return r.p+n <= len(r.b) }
func (r *cgRd) u32ok() bool     { return r.need(4) }
func (r *cgRd) u32v() uint32 {
	v := uint32(r.b[r.p]) | uint32(r.b[r.p+1])<<8 | uint32(r.b[r.p+2])<<16 | uint32(r.b[r.p+3])<<24
	r.p += 4
	return v
}
func (r *cgRd) i32v() (int32, bool) {
	if !r.need(4) {
		return 0, false
	}
	return int32(r.u32v()), true
}
func (r *cgRd) i64v() (int64, bool) {
	lo, ok1 := r.i32v()
	hi, ok2 := r.i32v()
	if !ok1 || !ok2 {
		return 0, false
	}
	return int64(uint64(uint32(hi))<<32 | uint64(uint32(lo))), true
}
func (r *cgRd) strv() (string, bool) {
	if !r.u32ok() {
		return "", false
	}
	n := r.u32v()
	if !r.need(int(n)) {
		return "", false
	}
	s := string(r.b[r.p : r.p+int(n)])
	r.p += int(n)
	return s, true
}
func (r *cgRd) u8v() (uint8, bool) {
	if !r.need(1) {
		return 0, false
	}
	v := r.b[r.p]
	r.p++
	return v, true
}
func (r *cgRd) blv(v uint8) bool { return v != 0 }

func (r *cgRd) nodes() ([]Node, bool) {
	if !r.u32ok() {
		return nil, false
	}
	n := r.u32v()
	if n > 1<<26 {
		return nil, false
	}
	out := make([]Node, 0, min(n, 1<<20))
	for i := uint32(0); i < n; i++ {
		if !r.need(44) {
			return nil, false
		}
		kind := uint16(r.u32v())
		flags := uint16(r.u32v())
		a := r.u32v()
		b := r.u32v()
		c := r.u32v()
		d := r.u32v()
		fl := r.u32v()
		off, _ := r.i32v()
		en, _ := r.i32v()
		ln, _ := r.i32v()
		col, _ := r.i32v()
		out = append(out, Node{Kind: kind, Flags: flags, A: a, B: b, C: c, D: d,
			File: fl, Off: off, End: en, Line: ln, Col: col})
	}
	return out, true
}
func (r *cgRd) funcs() ([]FuncDef, bool) {
	if !r.u32ok() {
		return nil, false
	}
	n := r.u32v()
	if n > 1<<24 {
		return nil, false
	}
	out := make([]FuncDef, 0, min(n, 1<<16))
	for i := uint32(0); i < n; i++ {
		if !r.need(42) {
			return nil, false
		}
		ni := r.u32v()
		si := r.u32v()
		ri := r.u32v()
		p0 := r.u32v()
		np := r.u32v()
		bd := r.u32v()
		le, _ := r.i32v()
		st := r.u32v()
		va, _ := r.u8v()
		kr, _ := r.u8v()
		a0 := r.u32v()
		an := r.u32v()
		out = append(out, FuncDef{NameIdx: ni, SigIdx: si, RetIdx: ri,
			Param0: p0, NParams: np, Body: bd, LineEnd: le, Storage: uint16(st),
			Variadic: r.blv(va), KR: r.blv(kr), Attr0: a0, NAttr: an})
	}
	return out, true
}
func (r *cgRd) decls() ([]DeclNode, bool) {
	if !r.u32ok() {
		return nil, false
	}
	n := r.u32v()
	if n > 1<<25 {
		return nil, false
	}
	out := make([]DeclNode, 0, min(n, 1<<18))
	for i := uint32(0); i < n; i++ {
		if !r.need(37) {
			return nil, false
		}
		ni := r.u32v()
		ti := r.u32v()
		ty := r.u32v()
		bf, _ := r.i32v()
		al, _ := r.i32v()
		pt, _ := r.i32v()
		in := r.u32v()
		st := r.u32v()
		kd, _ := r.u8v()
		ln, _ := r.i32v()
		out = append(out, DeclNode{NameIdx: ni, TypeIdx: ti, Typename: ty,
			Bitfield: bf, ArrayLen: al, Ptr: pt, Init: in, Storage: uint16(st),
			Kind: kd, Line: ln})
	}
	return out, true
}
func (r *cgRd) params() ([]ParamD, bool) {
	if !r.u32ok() {
		return nil, false
	}
	n := r.u32v()
	if n > 1<<25 {
		return nil, false
	}
	out := make([]ParamD, 0, min(n, 1<<18))
	for i := uint32(0); i < n; i++ {
		if !r.need(27) {
			return nil, false
		}
		ni := r.u32v()
		ti := r.u32v()
		pt, _ := r.i32v()
		al, _ := r.i32v()
		st := r.u32v()
		va, _ := r.u8v()
		un, _ := r.u8v()
		ic, _ := r.u8v()
		ln, _ := r.i32v()
		out = append(out, ParamD{NameIdx: ni, TypeIdx: ti, Ptr: pt,
			ArrayLen: al, Storage: uint16(st), Variadic: r.blv(va),
			Unnamed: r.blv(un), IsConst: r.blv(ic), Line: ln})
	}
	return out, true
}
func (r *cgRd) tags() ([]TagD, bool) {
	if !r.u32ok() {
		return nil, false
	}
	n := r.u32v()
	if n > 1<<24 {
		return nil, false
	}
	out := make([]TagD, 0, min(n, 1<<16))
	for i := uint32(0); i < n; i++ {
		if !r.need(27) {
			return nil, false
		}
		ni := r.u32v()
		tg, _ := r.u8v()
		c0 := r.u32v()
		nc := r.u32v()
		ui := r.u32v()
		hu, _ := r.u8v()
		df, _ := r.u8v()
		ln, _ := r.i32v()
		le, _ := r.i32v()
		out = append(out, TagD{NameIdx: ni, Tag: cgUntag8(tg), Child0: c0,
			NChild: nc, UnderlyingIdx: ui, HasUnderlying: r.blv(hu),
			Defined: r.blv(df), Line: ln, LineEnd: le})
	}
	return out, true
}
func (r *cgRd) fields() ([]FieldD, bool) {
	if !r.u32ok() {
		return nil, false
	}
	n := r.u32v()
	if n > 1<<25 {
		return nil, false
	}
	out := make([]FieldD, 0, min(n, 1<<18))
	for i := uint32(0); i < n; i++ {
		if !r.need(34) {
			return nil, false
		}
		ni := r.u32v()
		ti := r.u32v()
		pt := r.u32v()
		pd, _ := r.i32v()
		al, _ := r.i32v()
		bf, _ := r.i32v()
		fp, _ := r.u8v()
		ic, _ := r.u8v()
		dp, _ := r.i32v()
		ln, _ := r.i32v()
		out = append(out, FieldD{NameIdx: ni, TypeIdx: ti, PtrTypeIdx: pt,
			Ptr: pd, ArrayLen: al, Bitfield: bf, IsFnptr: r.blv(fp),
			IsConst: r.blv(ic), Depth: dp, Line: ln})
	}
	return out, true
}
func (r *cgRd) enums() ([]EnumD, bool) {
	if !r.u32ok() {
		return nil, false
	}
	n := r.u32v()
	if n > 1<<24 {
		return nil, false
	}
	out := make([]EnumD, 0, min(n, 1<<16))
	for i := uint32(0); i < n; i++ {
		if !r.need(13) {
			return nil, false
		}
		ni := r.u32v()
		vi := r.u32v()
		hv, _ := r.u8v()
		ln, _ := r.i32v()
		out = append(out, EnumD{NameIdx: ni, ValueIdx: vi, HasValue: r.blv(hv), Line: ln})
	}
	return out, true
}
func (r *cgRd) types() ([]TypeD, bool) {
	if !r.u32ok() {
		return nil, false
	}
	n := r.u32v()
	if n > 1<<25 {
		return nil, false
	}
	out := make([]TypeD, 0, min(n, 1<<18))
	for i := uint32(0); i < n; i++ {
		if !r.need(14) {
			return nil, false
		}
		ti := r.u32v()
		pt, _ := r.i32v()
		ar, _ := r.u8v()
		al, _ := r.i32v()
		fn, _ := r.u8v()
		out = append(out, TypeD{TextIdx: ti, Ptr: pt, Array: r.blv(ar),
			ArrayLen: al, IsFn: r.blv(fn)})
	}
	return out, true
}
func (r *cgRd) inits() ([]InitD, bool) {
	if !r.u32ok() {
		return nil, false
	}
	n := r.u32v()
	if n > 1<<25 {
		return nil, false
	}
	out := make([]InitD, 0, min(n, 1<<18))
	for i := uint32(0); i < n; i++ {
		if !r.need(14) {
			return nil, false
		}
		fi := r.u32v()
		ix, _ := r.i64v()
		hi, _ := r.u8v()
		il, _ := r.u8v()
		out = append(out, InitD{FieldIdx: fi, Index: ix, HasIndex: r.blv(hi), IsList: r.blv(il)})
	}
	return out, true
}
func (r *cgRd) assocs() ([]GenericAssoc, bool) {
	if !r.u32ok() {
		return nil, false
	}
	n := r.u32v()
	if n > 1<<25 {
		return nil, false
	}
	out := make([]GenericAssoc, 0, min(n, 1<<18))
	for i := uint32(0); i < n; i++ {
		if !r.need(9) {
			return nil, false
		}
		ti := r.u32v()
		df, _ := r.u8v()
		ex := r.u32v()
		out = append(out, GenericAssoc{TypeIdx: ti, IsDefault: r.blv(df), Expr: ex})
	}
	return out, true
}
