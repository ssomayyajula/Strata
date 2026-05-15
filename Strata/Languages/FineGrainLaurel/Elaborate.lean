/-
  Copyright Strata Contributors
  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.Languages.FineGrainLaurel.FineGrainLaurel
public import Strata.Languages.Laurel.Laurel
public import Strata.Languages.Laurel.HeapParameterizationConstants
public import Strata.Languages.Laurel.CoreDefinitionsForLaurel

/-!
# Pass 3: Elaboration

Elaboration transforms Laurel programs (impure CBV, effects implicit) into
Laurel programs where effects are explicit via calling conventions. The
theoretical foundation is **Fine-Grain Call-By-Value** (FGCBV) with graded
effects and bidirectional typing.

## Why FGCBV?

In plain CBV, every expression can have effects. You cannot tell by looking
at `f(x, g(y))` whether `g(y)` allocates, throws, or is pure. This matters
for verification because the calling convention depends on it: a pure call
returns a value directly; an effectful call returns through output parameters
(heap, error status).

FGCBV separates **values** (pure, duplicable) from **producers** (effectful,
sequenced). A producer must be explicitly sequenced — this makes the
elaborator syntax-directed. At every point, the structure of the term tells
you whether you are looking at a value or a producer.

## Bidirectional Typing

The elaborator has four mutually recursive functions:

- `synthValue`: value synthesis — literals, variables, pure calls, field access
- `checkValue`: value checking — synthesize then coerce (the ONE place subsumption lives)
- `synthExpr`: dispatches value vs producer (defunctionalized via `SynthResult`)
- `checkProducer`: producer checking — if, while, assign, block, exit, assert, etc.

Values synthesize their types bottom-up. Producers are checked against an
ambient grade and output type top-down. The mode discipline guarantees
deterministic choices at every point.

## Graded Effects

Each producer carries a grade from `{pure, proc, err, heap, heapErr}`. The
grade determines the calling convention (extra heap parameters, error outputs).
Grade inference proceeds by coinduction over the call graph: try each grade
from `pure` upward, the first that succeeds is the procedure's grade.

## Two Passes

1. **Grade inference** (coinductive fixpoint): for each user procedure, find
   the minimal grade at which elaboration succeeds.
2. **Term production**: elaborate each procedure at its inferred grade,
   project the FGCBV term back to Laurel statements.
-/

namespace Strata.FineGrainLaurel
open Strata.Laurel
public section

/-! ## Internal Types

Elaboration builds its own environment from `Laurel.Program` declarations.
Ideally call sites would carry callee signatures directly (no lookup needed),
but the Laurel AST uses string-named `StaticCall` nodes. -/

/-- Elaboration's internal function signature (built from Laurel.Procedure declarations). -/
structure FuncSig where
  /-- Procedure name (string, matching StaticCall callee names). -/
  name : String
  /-- Input parameters as (name, type) pairs. -/
  params : List (String × HighType)
  /-- Return type (first non-error output). -/
  returnType : HighType

instance : Inhabited FuncSig where
  default := { name := "", params := [], returnType := .TCore "Any" }

/-- What a name resolves to in Elaboration's type environment. -/
inductive NameInfo where
  /-- A callable procedure with its signature. -/
  | function (sig : FuncSig)
  /-- A variable binding with its type. -/
  | variable (ty : HighType)

instance : Inhabited NameInfo where
  default := .variable (.TCore "Any")

/-- The typing environment: maps names to their info and class names to field lists. -/
structure ElabTypeEnv where
  /-- All known names (procedures, variables, datatype constructors). -/
  names : Std.HashMap String NameInfo := {}
  /-- Class fields: class name -> list of (field name, field type). -/
  classFields : Std.HashMap String (List (String × HighType)) := {}
  deriving Inhabited

/-- Builds the type environment from a Laurel program's declarations. Scans all
    procedures (user + runtime) for signatures, all types for class fields. -/
def buildElabEnvFromProgram (program : Laurel.Program) (runtime : Laurel.Program := default) : ElabTypeEnv := Id.run do
  let mut names : Std.HashMap String NameInfo := {}
  let mut classFields : Std.HashMap String (List (String × HighType)) := {}
  for proc in program.staticProcedures ++ runtime.staticProcedures do
    let params := proc.inputs.map fun p => (p.name.text, p.type.val)
    let retTy := match proc.outputs.head? with
      | some o => o.type.val | none => HighType.TVoid
    names := names.insert proc.name.text (.function { name := proc.name.text, params, returnType := retTy })
  for td in program.types ++ runtime.types do
    match td with
    | .Composite ct =>
      let fields := ct.fields.map fun f => (f.name.text, f.type.val)
      classFields := classFields.insert ct.name.text fields
    | .Datatype dt =>
      for ctor in dt.constructors do
        let ctorParams := ctor.args.map fun p => (p.name.text, p.type.val)
        let retTy := HighType.UserDefined { text := dt.name.text, uniqueId := none }
        names := names.insert ctor.name.text (.function { name := ctor.name.text, params := ctorParams, returnType := retTy })
    | .Constrained _ => pure ()
  { names, classFields }

def mkLaurel (md : Imperative.MetaData Core.Expression) (e : StmtExpr) : StmtExprMd :=
  { val := e, md := md }
def mkHighTypeMd (md : Imperative.MetaData Core.Expression) (ty : HighType) : HighTypeMd :=
  { val := ty, md := md }

/-! ## The Grade Monoid

Grades classify which effects a producer performs. The monoid structure
ensures compositionality: sequencing two producers joins their grades.
The left residual `d \ e` ("what grade remains for the continuation after
a call at grade `d` within ambient grade `e`") drives grade inference —
if `d \ e` is undefined (d > e), elaboration fails and the grade is
pushed upward. -/

/-- The effect grade lattice: pure < proc < {err, heap} < heapErr. -/
inductive Grade where
  /-- No effects. Value-level `staticCall`, no extra params. -/
  | pure
  /-- Effectful but no error or heap. Outputs: `[result]`. -/
  | proc
  /-- May throw. Outputs: `[result, maybe_except]`. -/
  | err
  /-- Reads/writes heap. Inputs: `[$heap]`. Outputs: `[$heap, result]`. -/
  | heap
  /-- Heap + error. Inputs: `[$heap]`. Outputs: `[$heap, result, maybe_except]`. -/
  | heapErr
  deriving Inhabited, BEq, Repr

/-- Partial order on grades. `d.leq e` iff grade `d` is subsumed by `e`. -/
def Grade.leq : Grade → Grade → Bool
  | .pure, .pure => true | .pure, .proc => true | .pure, .err => true
  | .pure, .heap => true | .pure, .heapErr => true
  | .proc, .proc => true | .proc, .err => true | .proc, .heap => true | .proc, .heapErr => true
  | .err, .err => true | .err, .heapErr => true
  | .heap, .heap => true | .heap, .heapErr => true
  | .heapErr, .heapErr => true
  | _, _ => false

/-- Join (least upper bound) of two grades. Sequencing two producers joins their grades. -/
def Grade.join : Grade → Grade → Grade
  | .pure, e => e | e, .pure => e
  | .proc, .proc => .proc
  | .proc, .err => .err | .err, .proc => .err
  | .proc, .heap => .heap | .heap, .proc => .heap
  | .proc, .heapErr => .heapErr | .heapErr, .proc => .heapErr
  | .err, .err => .err
  | .err, .heap => .heapErr | .heap, .err => .heapErr
  | .err, .heapErr => .heapErr | .heapErr, .err => .heapErr
  | .heap, .heap => .heap
  | .heap, .heapErr => .heapErr | .heapErr, .heap => .heapErr
  | .heapErr, .heapErr => .heapErr

/-- Left residual: `d\e` = grade remaining for the continuation after a call
    at grade `d` within ambient grade `e`. Returns `none` if `d > e` (elaboration fails).
```
pure\e       = e
proc\proc    = pure     proc\err    = err      proc\heap   = heap     proc\heapErr = heapErr
err\err      = pure     err\heapErr = heap
heap\heap    = pure     heap\heapErr = err
heapErr\heapErr = pure
```
-/
def Grade.leftResidual : Grade → Grade → Option Grade
  | .pure, e => some e
  | .proc, .proc => some .pure | .proc, .err => some .err
  | .proc, .heap => some .heap | .proc, .heapErr => some .heapErr
  | .err, .err => some .pure | .err, .heapErr => some .heap
  | .heap, .heap => some .pure | .heap, .heapErr => some .err
  | .heapErr, .heapErr => some .pure
  | _, _ => none

/-! ## Type Erasure

Elaboration operates on `LowType` — the erased version of `HighType`.
User-defined types erase to `Composite` (they live on the heap). The
subtyping/coercion system operates on `LowType` values. -/

/-- The erased type system. User-defined types become `Composite` (heap-allocated).
    Subsumption and coercion operate on `LowType` values. -/
inductive LowType where
  /-- Machine integer. -/
  | TInt
  /-- Boolean. -/
  | TBool
  /-- String. -/
  | TString
  /-- 64-bit float. -/
  | TFloat64
  /-- Unit/void. -/
  | TVoid
  /-- Named core type (Any, Error, Heap, Composite, ListAny, DictStrAny, etc.). -/
  | TCore (name : String)
  deriving Inhabited, Repr, BEq

/-- Type erasure: HighType -> LowType. Primitives map directly, user-defined types
    become Composite, unknown/complex types become Any. -/
def eraseType : HighType → LowType
  | .TInt => .TInt | .TBool => .TBool | .TString => .TString
  | .TFloat64 => .TFloat64 | .TVoid => .TVoid | .TCore n => .TCore n
  | .UserDefined id => match id.text with
    | "Any" => .TCore "Any" | "Error" => .TCore "Error"
    | "ListAny" => .TCore "ListAny" | "DictStrAny" => .TCore "DictStrAny"
    | "Box" => .TCore "Box" | "Field" => .TCore "Field" | "TypeTag" => .TCore "TypeTag"
    | _ => .TCore "Composite"
  | .THeap => .TCore "Heap"
  | .TReal => .TCore "real" | .TTypedField _ => .TCore "Field"
  | .TSet _ | .TMap _ _ | .Applied _ _ | .Intersection _ | .Unknown => .TCore "Any"
  | .Pure _ => .TCore "Composite"

/-- Inverse of erasure (partial): lifts a LowType back to HighType for env extension. -/
def liftType : LowType → HighType
  | .TInt => .TInt | .TBool => .TBool | .TString => .TString
  | .TFloat64 => .TFloat64 | .TVoid => .TVoid | .TCore n => .TCore n

/-! ## FGL Terms

The intermediate representation between Laurel input and Laurel output.
Values are pure (can appear in any context). Producers are effectful
(must be sequenced). Every constructor carries source metadata so
provenance is preserved through elaboration. -/

abbrev Md := Imperative.MetaData Core.Expression

/-- A pure value in the FGCBV intermediate term. Can appear in any context.
    Every constructor carries source metadata for provenance. -/
inductive FGLValue where
  /-- Integer literal. -/
  | litInt (md : Md) (n : Int)
  /-- Boolean literal. -/
  | litBool (md : Md) (b : Bool)
  /-- String literal. -/
  | litString (md : Md) (s : String)
  /-- Variable reference. -/
  | var (md : Md) (name : String)
  /-- Coercion: int → Any. -/
  | fromInt (md : Md) (inner : FGLValue)
  /-- Coercion: string → Any. -/
  | fromStr (md : Md) (inner : FGLValue)
  /-- Coercion: bool → Any. -/
  | fromBool (md : Md) (inner : FGLValue)
  /-- Coercion: float → Any. -/
  | fromFloat (md : Md) (inner : FGLValue)
  /-- Coercion: Composite → Any. -/
  | fromComposite (md : Md) (inner : FGLValue)
  /-- Coercion: ListAny → Any. -/
  | fromListAny (md : Md) (inner : FGLValue)
  /-- Coercion: DictStrAny → Any. -/
  | fromDictStrAny (md : Md) (inner : FGLValue)
  /-- Coercion: None → Any. -/
  | fromNone (md : Md)
  /-- Field access (pre-heap-resolution). -/
  | fieldAccess (md : Md) (obj : FGLValue) (field : String)
  /-- Pure function call. -/
  | staticCall (md : Md) (name : String) (args : List FGLValue)
  deriving Inhabited

def FGLValue.getMd : FGLValue → Md
  | .litInt md _ | .litBool md _ | .litString md _ | .var md _
  | .fromInt md _ | .fromStr md _ | .fromBool md _ | .fromFloat md _
  | .fromComposite md _ | .fromListAny md _ | .fromDictStrAny md _ | .fromNone md
  | .fieldAccess md _ _ | .staticCall md _ _ => md

/-- An effectful producer in the FGCBV intermediate term. Must be sequenced.
    Each form carries a continuation (`body`/`after`) — the CPS structure
    makes projection to Laurel statements trivial. -/
inductive FGLProducer where
  /-- Return a value (terminal — no continuation). -/
  | produce (md : Md) (v : FGLValue)
  /-- Assign to an existing variable, then continue. -/
  | assign (md : Md) (target : FGLValue) (val : FGLValue) (body : FGLProducer)
  /-- Declare a local variable, then continue in extended scope. -/
  | varDecl (md : Md) (name : String) (ty : LowType) (init : Option FGLValue) (body : FGLProducer)
  /-- Conditional: check condition, branch, then continue after. -/
  | ifThenElse (md : Md) (cond : FGLValue) (thn : FGLProducer) (els : FGLProducer) (after : FGLProducer)
  /-- Loop: check condition, iterate body, then continue after. -/
  | whileLoop (md : Md) (cond : FGLValue) (body : FGLProducer) (after : FGLProducer)
  /-- Assert condition holds, then continue. -/
  | assert (md : Md) (cond : FGLValue) (body : FGLProducer)
  /-- Assume condition holds, then continue. -/
  | assume (md : Md) (cond : FGLValue) (body : FGLProducer)
  /-- Effectful call: bind outputs, then continue in extended scope. -/
  | procedureCall (md : Md) (callee : String) (args : List FGLValue)
      (outputs : List (String × LowType)) (body : FGLProducer)
  /-- Exit to enclosing labeled block (non-returning). -/
  | exit (md : Md) (label : String)
  /-- Labeled block: body may exit to label, then continue after. -/
  | labeledBlock (md : Md) (label : String) (body : FGLProducer) (after : FGLProducer)
  /-- Empty continuation (end of block). -/
  | unit
  deriving Inhabited

-- ═══════════════════════════════════════════════════════════════════════════════
-- Monad
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Reader environment for elaboration. Carries the type environment, program,
    runtime, inferred grades, and current procedure's input list (for hole args). -/
structure ElabEnv where
  /-- The typing context (names + class fields). -/
  typeEnv : ElabTypeEnv
  /-- The user program being elaborated. -/
  program : Laurel.Program
  /-- The runtime prelude (builtins, data structure operations). -/
  runtime : Laurel.Program := default
  /-- Inferred grades for all procedures. -/
  procGrades : Std.HashMap String Grade := {}
  /-- Current procedure's input params (used as hole arguments). -/
  procInputs : List (String × HighType) := []

/-- Mutable state for elaboration: fresh name counter, current heap variable name,
    and collectors for box constructors and holes used (emitted as declarations). -/
structure ElabState where
  /-- Counter for generating fresh variable names. -/
  freshCounter : Nat := 0
  /-- Current heap variable name (updated after each heap-writing call). -/
  heapVar : Option String := none
  /-- Box constructors used (emitted as datatype constructors in output). -/
  usedBoxConstructors : List (String × String × HighType) := []
  /-- Hole functions used (emitted as opaque procedure declarations in output). -/
  usedHoles : List (String × Bool × HighType) := []

abbrev ElabM := ReaderT ElabEnv (StateT ElabState Option)

private def freshVar (pfx : String := "tmp") : ElabM String := do
  let s ← get; set { s with freshCounter := s.freshCounter + 1 }; pure s!"{pfx}${s.freshCounter}"

-- ═══════════════════════════════════════════════════════════════════════════════
-- Box protocol (type-directed)
-- Architecture §"Heap Field Access"
-- ═══════════════════════════════════════════════════════════════════════════════

def boxConstructorName (ty : HighType) : String :=
  match ty with
  | .TInt => "BoxInt" | .TBool => "BoxBool" | .TFloat64 => "BoxFloat64"
  | .TReal => "BoxReal" | .TString => "BoxString"
  | .UserDefined _ => "BoxComposite"
  | .TCore "Any" => "BoxAny"
  | .TCore name => s!"Box..{name}"
  | _ => "BoxComposite"

def boxDestructorName (ty : HighType) : String :=
  match ty with
  | .TInt => "Box..intVal!" | .TBool => "Box..boolVal!" | .TFloat64 => "Box..float64Val!"
  | .TReal => "Box..realVal!" | .TString => "Box..stringVal!"
  | .UserDefined _ => "Box..compositeVal!"
  | .TCore "Any" => "Box..AnyVal!"
  | .TCore name => s!"Box..{name}Val!"
  | _ => "Box..compositeVal!"

def boxFieldName (ty : HighType) : String :=
  match ty with
  | .TInt => "intVal" | .TBool => "boolVal" | .TFloat64 => "float64Val"
  | .TReal => "realVal" | .TString => "stringVal"
  | .UserDefined _ => "compositeVal"
  | .TCore "Any" => "AnyVal"
  | .TCore name => s!"{name}Val"
  | _ => "compositeVal"

def boxFieldType (ty : HighType) : HighType :=
  match ty with
  | .UserDefined _ => .UserDefined (Identifier.mk "Composite" none)
  | other => other

def recordBoxUse (ty : HighType) : ElabM Unit := do
  let ctor := boxConstructorName ty
  let existing := (← get).usedBoxConstructors
  unless existing.any (fun (c, _, _) => c == ctor) do
    modify fun s => { s with usedBoxConstructors := s.usedBoxConstructors ++ [(ctor, boxDestructorName ty, ty)] }

/-- Reads a runtime procedure's grade structurally from its signature: does it
    have a Heap input? An Error output? The combination determines the grade.
    User procedure grades are inferred by coinduction, not read from signature. -/
def gradeFromSignature (proc : Laurel.Procedure) : Grade :=
  let hasError := proc.outputs.any fun o => eraseType o.type.val == .TCore "Error"
  let hasHeap := proc.inputs.any fun i => eraseType i.type.val == .TCore "Heap"
  match hasHeap, hasError with
  | true, true => .heapErr
  | true, false => .heap
  | false, true => .err
  | false, false => if proc.isFunctional then .pure else .proc

-- ═══════════════════════════════════════════════════════════════════════════════
-- Env helpers
-- ═══════════════════════════════════════════════════════════════════════════════

def lookupEnv (name : String) : ElabM (Option NameInfo) := do pure (← read).typeEnv.names[name]?
def extendEnv (name : String) (ty : HighType) (action : ElabM α) : ElabM α :=
  withReader (fun env => { env with typeEnv := { env.typeEnv with names := env.typeEnv.names.insert name (.variable ty) } }) action
def lookupFuncSig (name : String) : ElabM (Option FuncSig) := do
  match (← read).typeEnv.names[name]? with | some (.function sig) => pure (some sig) | _ => pure none
def lookupFieldType (className fieldName : String) : ElabM (Option HighType) := do
  match (← read).typeEnv.classFields[className]? with
  | some fields => pure (fields.find? (fun (n, _) => n == fieldName) |>.map (·.2))
  | none => pure none
def resolveFieldOwner (fieldName : String) : ElabM (Option String) := do
  for (className, fields) in (← read).typeEnv.classFields.toList do
    if fields.any (fun (n, _) => n == fieldName) then return some className
  pure none

/-! ## HOAS Smart Constructors

These construct effectful call nodes using higher-order abstract syntax:
the continuation is a Lean function from fresh output variables to the
body producer. This ensures output variables are always correctly scoped
(extended in the environment before the body is elaborated). -/

def mkEffectfulCall (md : Md) (callee : String) (args : List FGLValue)
    (outputSpecs : List (String × HighType))
    (body : List FGLValue → ElabM FGLProducer) : ElabM FGLProducer := do
  let mut names : List String := []
  let mut lowOutputs : List (String × LowType) := []
  for (pfx, ty) in outputSpecs do
    let n ← freshVar pfx
    names := names ++ [n]
    lowOutputs := lowOutputs ++ [(n, eraseType ty)]
  let vars := names.map (FGLValue.var md)
  let cont ← names.zip (outputSpecs.map (·.2)) |>.foldr
    (fun (n, ty) acc => extendEnv n ty acc) (body vars)
  pure (.procedureCall md callee args lowOutputs cont)

def mkVarDecl (md : Md) (name : String) (ty : LowType) (init : Option FGLValue)
    (body : FGLValue → ElabM FGLProducer) : ElabM FGLProducer := do
  let cont ← extendEnv name (liftType ty) (body (.var md name))
  pure (.varDecl md name ty init cont)

/-- Subgrading witness: `d ≤ e ↦ (pre, outs)`. Constructs a `procedureCall`
    with the correct calling convention based on grade.
```
d ≤ e ↦ (args_prepended, outputs_declared, resultIdx)

pure:     ([], [], —)                                  — value-level, no procedureCall
proc:     ([], [result:B], 0)
err:      ([], [result:B, except:Error], 0)
heap:     ([heap_var], [heap:Heap, result:B], 1)
heapErr:  ([heap_var], [heap:Heap, result:B, except:Error], 1)
```
-/
def mkGradedCall (md : Md) (callee : String) (args : List FGLValue)
    (declaredOutputs : List (String × HighType)) (callGrade : Grade)
    (body : FGLValue → ElabM FGLProducer) : ElabM FGLProducer := do
  let actualArgs ← if callGrade == .heap || callGrade == .heapErr then do
    let hv := (← get).heapVar
    let heapArg := match hv with | some h => FGLValue.var md h | none => FGLValue.var md "$heap"
    pure (heapArg :: args)
  else pure args
  mkEffectfulCall md callee actualArgs declaredOutputs fun outs => do
    if callGrade == .heap || callGrade == .heapErr then
      match outs[0]? with
      | some v => match v with | .var _ n => modify fun s => { s with heapVar := some n } | _ => pure ()
      | none => pure ()
    let resultVar := match callGrade with
      | .heap | .heapErr => outs[1]?
      | _ => outs[0]?
    match resultVar with
    | some rv => body rv
    | none => body (.fromNone md)

/-! ## Subsumption

A subtyping judgment `A <= B` has a witness: a coercion function. Upward
coercions (T <= Any) are value constructors (boxing). Downward coercions
(Any <= T) are pure function calls (unboxing). `applySubtype` is called
ONLY from `checkValue` — this is the bidirectional discipline. -/

/-- The result of a subsumption check: identity (types equal), a coercion witness
    (function to apply), or unrelated (no subtyping relationship). -/
inductive CoercionResult where
  /-- Types are equal — no coercion needed. -/
  | refl
  /-- Subtyping holds — apply this coercion function. -/
  | coerce (w : Md → FGLValue → FGLValue)
  /-- No subtyping relationship. -/
  | unrelated
  deriving Inhabited

/-- Subtyping judgment: `A ≤ B ↦ c`. Returns the coercion witness.
```
A ≤ A ↦ id  (reflexivity)

TInt ≤ Any ↦ fromInt          TBool ≤ Any ↦ fromBool
TString ≤ Any ↦ fromStr       TFloat64 ≤ Any ↦ fromFloat
Composite ≤ Any ↦ fromComposite
ListAny ≤ Any ↦ fromListAny   DictStrAny ≤ Any ↦ fromDictStrAny
TVoid ≤ Any ↦ fromNone

Any ≤ TBool ↦ Any_to_bool     Any ≤ TInt ↦ Any..as_int!
Any ≤ TString ↦ Any..as_string!
Any ≤ TFloat64 ↦ Any..as_float!
Any ≤ Composite ↦ Any..as_Composite!
```
-/
def subtype (actual expected : LowType) : CoercionResult :=
  if actual == expected then .refl else match actual, expected with
  | .TInt, .TCore "Any" => .coerce (fun md => .fromInt md)
  | .TBool, .TCore "Any" => .coerce (fun md => .fromBool md)
  | .TString, .TCore "Any" => .coerce (fun md => .fromStr md)
  | .TFloat64, .TCore "Any" => .coerce (fun md => .fromFloat md)
  | .TCore "Composite", .TCore "Any" => .coerce (fun md => .fromComposite md)
  | .TCore "ListAny", .TCore "Any" => .coerce (fun md => .fromListAny md)
  | .TCore "DictStrAny", .TCore "Any" => .coerce (fun md => .fromDictStrAny md)
  | .TVoid, .TCore "Any" => .coerce (fun md _ => .fromNone md)
  | .TCore "Any", .TBool => .coerce (fun md v => .staticCall md "Any_to_bool" [v])
  | .TCore "Any", .TInt => .coerce (fun md v => .staticCall md "Any..as_int!" [v])
  | .TCore "Any", .TString => .coerce (fun md v => .staticCall md "Any..as_string!" [v])
  | .TCore "Any", .TFloat64 => .coerce (fun md v => .staticCall md "Any..as_float!" [v])
  | .TCore "Any", .TCore "Composite" => .coerce (fun md v => .staticCall md "Any..as_Composite!" [v])
  | _, _ => .unrelated

/-- Apply the coercion witness for `actual <= expected` to a value. Identity if equal. -/
def applySubtype (val : FGLValue) (actual expected : LowType) : FGLValue :=
  match subtype actual expected with | .refl => val | .coerce c => c val.getMd val | .unrelated => val

-- ═══════════════════════════════════════════════════════════════════════════════
-- Defunctionalized producer synthesis result
-- Architecture §"Elaboration Structure"
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Defunctionalized result of expression synthesis. Either a pure value (can be
    used directly) or an effectful call (must be sequenced via the to-rule). -/
inductive SynthResult where
  /-- Pure: use this value directly. -/
  | value (val : FGLValue) (ty : LowType)
  /-- Effectful: must emit procedureCall to bind the result before use. -/
  | call (callee : String) (args : List FGLValue) (retTy : HighType) (grade : Grade)
  deriving Inhabited

/-! ## The Four Typing Functions

The mutual block below implements the four functions of bidirectional
elaboration:

- `synthValue` — Γ ⊢_v V ⇒ A (value synthesis)
- `checkValue` — Γ ⊢_v V ⇐ A (synth + subsume; THE one place coercions are inserted)
- `synthExpr` — dispatches to value or producer (defunctionalized via SynthResult)
- `checkProducer` — Γ ⊢_p M ⇐ A & e (producer checking: all statement constructs)

`checkArgsK` implements argument sequencing (ANF-lift effectful args).
`checkAssign` handles the assignment rule (field write, effectful RHS, etc.).
-/

mutual

/-- ⟦·⟧⇒ᵥ (literals):
```
D :: Γ ⊢ n : int   [lit]        ↦   ⟦D⟧⇒ᵥ :: ⟦Γ⟧ ⊢ litInt n ⇒ TInt   [litInt]
D :: Γ ⊢ b : bool  [lit]        ↦   ⟦D⟧⇒ᵥ :: ⟦Γ⟧ ⊢ litBool b ⇒ TBool   [litBool]
D :: Γ ⊢ s : string [lit]       ↦   ⟦D⟧⇒ᵥ :: ⟦Γ⟧ ⊢ litString s ⇒ TString   [litString]
```
-/
partial def synthValueLiteral (md : Md) : StmtExpr → Option (FGLValue × LowType)
  | .LiteralInt n => some (.litInt md n, .TInt)
  | .LiteralBool b => some (.litBool md b, .TBool)
  | .LiteralString s => some (.litString md s, .TString)
  | _ => none

/-- ⟦·⟧⇒ᵥ (variable):
```
D :: Γ ⊢ x : A   [var, (x:A) ∈ Γ]

    ↦

⟦D⟧⇒ᵥ :: ⟦Γ⟧ ⊢ var x ⇒ ⟦A⟧   [var, (x:⟦A⟧) ∈ ⟦Γ⟧]
```
-/
partial def synthValueVar (md : Md) (id : Laurel.Identifier) : ElabM (FGLValue × LowType) := do
  match (← lookupEnv id.text) with
  | some (.variable ty) => pure (.var md id.text, eraseType ty)
  | some (.function sig) => pure (.var md id.text, eraseType sig.returnType)
  | _ => pure (.var md id.text, .TCore "Any")

/-- ⟦·⟧⇒ᵥ (field access):
```
D :: Γ ⊢ obj.f : T   [fieldSelect]
└─ D_obj :: Γ ⊢ obj : C

    ↦    precondition: ($heap : Heap) ∈ ⟦Γ⟧

⟦D⟧⇒ᵥ :: ⟦Γ⟧ ⊢ functionCall unbox_T [functionCall readField [$heap, V_obj, $field.C.f]] ⇒ ⟦T⟧   [functionCall]
└─ ⟦Γ⟧ ⊢ functionCall readField [$heap, V_obj, $field.C.f] ⇐ Box   [subsumption]
   ├─ ⟦Γ⟧ ⊢ functionCall readField [$heap, V_obj, $field.C.f] ⇒ Box   [functionCall]
   │  ├─ ⟦Γ⟧ ⊢ $heap ⇐ Heap   [subsumption]
   │  │  ├─ ⟦Γ⟧ ⊢ $heap ⇒ Heap   [var]
   │  │  └─ Heap ≤ Heap ↦ id
   │  ├─ ⟦D_obj⟧⇐ᵥ :: ⟦Γ⟧ ⊢ V_obj ⇐ Composite   [subsumption]
   │  │  ├─ ⟦D_obj⟧⇒ᵥ :: ⟦Γ⟧ ⊢ V_obj ⇒ Composite   (since ⟦C⟧ = Composite for user-defined C)
   │  │  └─ Composite ≤ Composite ↦ id
   │  └─ ⟦Γ⟧ ⊢ functionCall $field.C.f [] ⇐ Field   [subsumption]
   │     ├─ ⟦Γ⟧ ⊢ functionCall $field.C.f [] ⇒ Field   [functionCall]
   │     └─ Field ≤ Field ↦ id
   └─ Box ≤ Box ↦ id
```
-/
partial def synthValueFieldSelect (md : Md) (obj : StmtExprMd) (field : Laurel.Identifier) : ElabM (FGLValue × LowType) := do
  let (ov, objTy) ← synthValue obj
  match (← get).heapVar with
  | some hv =>
    let owner ← resolveFieldOwner field.text
    let qualifiedName := match owner with | some cn => "$field." ++ cn ++ "." ++ field.text | none => "$field." ++ field.text
    let fieldTy ← match owner with
      | some cn => do let ft ← lookupFieldType cn field.text; pure (ft.getD (.TCore "Any"))
      | none => pure (.TCore "Any")
    recordBoxUse fieldTy
    let compositeObj := applySubtype ov objTy (.TCore "Composite")
    let read := FGLValue.staticCall md "readField" [.var md hv, compositeObj, .staticCall md qualifiedName []]
    pure (.staticCall md (boxDestructorName fieldTy) [read], eraseType fieldTy)
  | none => failure

/-- ⟦·⟧⇒ᵥ (pure call):
```
D :: Γ ⊢ f(e₁,…,eₙ) : B   [call, f : (Aᵢ) → B & pure]
└─ D_i :: Γ ⊢ eᵢ : Aᵢ  (for each i)

    ↦

⟦D⟧⇒ᵥ :: ⟦Γ⟧ ⊢ functionCall f [V₁,…,Vₙ] ⇒ ⟦B⟧   [functionCall]
└─ ⟦D_i⟧⇐ᵥ :: ⟦Γ⟧ ⊢ Vᵢ ⇐ ⟦Aᵢ⟧  (for each i)   [subsumption]
   ├─ ⟦D_i⟧⇒ᵥ :: ⟦Γ⟧ ⊢ Vᵢ ⇒ Bᵢ   (Bᵢ discovered by recursive synthValue)
   └─ Bᵢ ≤ ⟦Aᵢ⟧ ↦ cᵢ
```
-/
partial def synthValueStaticCall (md : Md) (callee : Laurel.Identifier) (args : List StmtExprMd) : ElabM (FGLValue × LowType) := do
  let g := (← read).procGrades[callee.text]?.getD .pure
  guard (g == .pure)
  let sig ← lookupFuncSig callee.text
  match sig with
  | some s =>
    let checkedArgs ← checkArgs args s.params
    pure (.staticCall md callee.text checkedArgs, eraseType s.returnType)
  | none =>
    let checkedArgs ← args.mapM fun arg => checkValue arg (.TCore "Any")
    pure (.staticCall md callee.text checkedArgs, .TCore "Any")

/-- ⟦·⟧⇒ᵥ (holes):
```
D :: Γ ⊢ ? : A   [hole]

    ↦

⟦D⟧⇒ᵥ :: ⟦Γ⟧ ⊢ functionCall hole_N [p₁,…,pₘ] ⇒ Any   [functionCall]
└─ ⟦Γ⟧ ⊢ pᵢ ⇐ Aᵢ  (for each procedure input pᵢ:Aᵢ)   [subsumption]
   ├─ ⟦Γ⟧ ⊢ pᵢ ⇒ Aᵢ   [var]
   └─ Aᵢ ≤ Aᵢ ↦ id

D :: Γ ⊢ ?? : A  [havoc]

    ↦

⟦D⟧⇒ᵥ :: ⟦Γ⟧ ⊢ functionCall havoc_N [] ⇒ Any   [functionCall]
(no premises — zero-arity)
```
Deterministic holes take all procedure inputs as arguments. Nondeterministic holes take none.
-/
partial def synthValueHole (md : Md) (deterministic : Bool) : ElabM (FGLValue × LowType) := do
  if deterministic then
    let hv ← freshVar "hole"
    let inputs := (← read).procInputs
    let args := inputs.map fun (name, _) => FGLValue.var md name
    modify fun s => { s with usedHoles := s.usedHoles ++ [(hv, true, .TCore "Any")] }
    pure (.staticCall md hv args, .TCore "Any")
  else
    let hv ← freshVar "havoc"
    modify fun s => { s with usedHoles := s.usedHoles ++ [(hv, false, .TCore "Any")] }
    pure (.staticCall md hv [], .TCore "Any")

/-- Value synthesis: dispatches to clause-specific helpers.
    Each helper implements one clause of ⟦·⟧⇒. -/
partial def synthValue (expr : StmtExprMd) : ElabM (FGLValue × LowType) := do
  let md := expr.md
  match expr.val with
  | .LiteralInt _ | .LiteralBool _ | .LiteralString _ =>
    match synthValueLiteral md expr.val with
    | some r => pure r
    | none => failure
  | .Identifier id => synthValueVar md id
  | .FieldSelect obj field => synthValueFieldSelect md obj field
  | .StaticCall callee args => synthValueStaticCall md callee args
  | .Hole deterministic _ => synthValueHole md deterministic
  | _ => failure

/-- Value checking: synthesize then coerce. This is the ONE place where
    subsumption (coercion insertion) happens. No other function calls `applySubtype`. -/
partial def checkValue (expr : StmtExprMd) (expected : HighType) : ElabM FGLValue := do
  let (val, actual) ← synthValue expr
  pure (applySubtype val actual (eraseType expected))

/-- Dispatches synthesis: if the callee's grade is pure, returns a value;
    if grade > pure, returns a `SynthResult.call` that the caller must sequence
    via the to-rule (procedureCall binding). -/
partial def synthExpr (expr : StmtExprMd) : ElabM SynthResult := do
  let md := expr.md
  match expr.val with
  | .StaticCall callee args =>
    let sig ← lookupFuncSig callee.text
    let g := (← read).procGrades[callee.text]?.getD .pure
    match sig with
    | some s =>
      let checkedArgs ← checkArgs args s.params
      if g == .pure then
        pure (.value (.staticCall md callee.text checkedArgs) (eraseType s.returnType))
      else
        pure (.call callee.text checkedArgs s.returnType g)
    | none =>
      let checkedArgs ← args.mapM fun arg => checkValue arg (.TCore "Any")
      if g == .pure then
        pure (.value (.staticCall md callee.text checkedArgs) (.TCore "Any"))
      else
        pure (.call callee.text checkedArgs (.TCore "Any") g)
  | _ =>
    let (val, ty) ← synthValue expr
    pure (.value val ty)

partial def checkArgs (args : List StmtExprMd) (params : List (String × HighType)) : ElabM (List FGLValue) := do
  let paramTypes := params.map (·.2)
  let rec go : List StmtExprMd → List HighType → ElabM (List FGLValue)
    | [], _ => pure []
    | arg :: rest, pty :: ptys => do
      let v ← checkValue arg pty
      let vs ← go rest ptys
      pure (v :: vs)
    | arg :: rest, [] => do
      let (v, _) ← synthValue arg
      let vs ← go rest []
      pure (v :: vs)
  go args paramTypes

-- Look up a proc's declared outputs, accounting for signature rewriting.
-- For user procs: grade determines rewritten outputs.
-- For runtime procs: outputs are as declared (never rewritten).
partial def lookupProcOutputs (callee : String) : ElabM (List (String × HighType)) := do
  let env ← read
  let g := env.procGrades[callee]?.getD .pure
  let findProc (procs : List Laurel.Procedure) : Option Laurel.Procedure :=
    procs.find? (fun p => p.name.text == callee)
  match findProc env.runtime.staticProcedures with
  | some proc => pure (proc.outputs.map fun o => (o.name.text, o.type.val))
  | none => match findProc env.program.staticProcedures with
    | some proc =>
      let resultOutputs := proc.outputs.filter fun o => eraseType o.type.val != .TCore "Error"
      let resultList := resultOutputs.map fun o => (o.name.text, o.type.val)
      match g with
      | .heap => pure ([("$heap", .THeap)] ++ resultList)
      | .heapErr => pure ([("$heap", .THeap)] ++ resultList ++ [("maybe_except", .TCore "Error")])
      | .err => pure (resultList ++ [("maybe_except", .TCore "Error")])
      | _ => pure (proc.outputs.map fun o => (o.name.text, o.type.val))
    | none => pure [("result", .TCore "Any")]

-- Dispatch smart constructor based on grade
-- Architecture §"Subgrading Witness"
private partial def dispatchCall (md : Md) (callee : String) (args : List FGLValue)
    (callGrade : Grade) (body : FGLValue → ElabM FGLProducer) : ElabM FGLProducer := do
  match callGrade with
  | .pure => body (FGLValue.staticCall md callee args)
  | _ => do
    let declaredOutputs ← lookupProcOutputs callee
    mkGradedCall md callee args declaredOutputs callGrade body

/-- Argument sequencing (ANF-lift): checks each argument. If an argument is a
    pure value, check it directly. If it's an effectful call (grade > pure),
    sequence it via procedureCall and use the result variable. Multiple effectful
    args nest left-to-right. -/
partial def checkArgsK (args : List StmtExprMd) (params : List (String × HighType))
    (grade : Grade) (cont : List FGLValue → ElabM FGLProducer) : ElabM FGLProducer := do
  let paramTypes := params.map (·.2)
  let rec go : List StmtExprMd → List HighType → List FGLValue → ElabM FGLProducer
    | [], _, acc => cont acc.reverse
    | arg :: rest, [], acc => do
      let result ← synthExpr arg
      match result with
      | .value val _ => go rest [] (val :: acc)
      | .call callee checkedArgs _retTy callGrade =>
        guard (Grade.leq callGrade grade)
        dispatchCall arg.md callee checkedArgs callGrade fun rv => go rest [] (rv :: acc)
    | arg :: rest, pty :: ptysRest, acc => do
      let result ← synthExpr arg
      match result with
      | .value val ty =>
        let coerced := applySubtype val ty (eraseType pty)
        go rest ptysRest (coerced :: acc)
      | .call callee checkedArgs retTy callGrade =>
        guard (Grade.leq callGrade grade)
        dispatchCall arg.md callee checkedArgs callGrade fun rv =>
          go rest ptysRest (applySubtype rv (eraseType retTy) (eraseType pty) :: acc)
  go args paramTypes []

/-- ⟦·⟧⇐ₚ (if):
```
D :: Γ ⊢ (if c then t else f); k : A   [if]
├─ D_c :: Γ ⊢ c : bool
├─ D_t :: Γ ⊢ t : A
├─ D_f :: Γ ⊢ f : A
└─ D_k :: Γ ⊢ k : A

    ↦

⟦D⟧⇐ₚ :: ⟦Γ⟧ ⊢ varDecl x_c bool M_c (ifThenElse x_c M_t M_f M_k) ⇐ ⟦A⟧ & d   [varDecl]
├─ ⟦D_c⟧⇐ₚ :: ⟦Γ⟧ ⊢ M_c ⇐ bool & d
└─ ⟦Γ⟧, x_c:bool ⊢ ifThenElse x_c M_t M_f M_k ⇐ ⟦A⟧ & d   [ifThenElse]
   ├─ ⟦Γ⟧, x_c:bool ⊢ x_c ⇐ bool   [subsumption]
   │  ├─ ⟦Γ⟧, x_c:bool ⊢ x_c ⇒ bool   [var]
   │  └─ bool ≤ bool ↦ id
   ├─ ⟦D_t⟧⇐ₚ :: ⟦Γ⟧, x_c:bool ⊢ M_t ⇐ ⟦A⟧ & d
   ├─ ⟦D_f⟧⇐ₚ :: ⟦Γ⟧, x_c:bool ⊢ M_f ⇐ ⟦A⟧ & d
   └─ ⟦D_k⟧⇐ₚ* :: ⟦Γ⟧, x_c:bool ⊢ M_k ⇐ ⟦A⟧ & d
```
-/
partial def checkProducerIf (md : Md) (cond thn : StmtExprMd) (els : Option StmtExprMd)
    (rest : List StmtExprMd) (retTy : HighType) (grade : Grade) : ElabM FGLProducer := do
  let cc ← checkValue cond .TBool
  let tp ← checkProducer thn [] retTy grade
  let ep ← match els with
    | some e => checkProducer e [] retTy grade
    | none => pure .unit
  let after ← checkProducers rest retTy grade
  pure (.ifThenElse md cc tp ep after)

/-- ⟦·⟧⇐ₚ (while):
```
D :: Γ ⊢ (while c do body); k : A   [while]
├─ D_c :: Γ ⊢ c : bool
├─ D_b :: Γ ⊢ body : A
└─ D_k :: Γ ⊢ k : A

    ↦

⟦D⟧⇐ₚ :: ⟦Γ⟧ ⊢ varDecl x_c bool M_c (whileLoop x_c M_b M_k) ⇐ ⟦A⟧ & d   [varDecl]
├─ ⟦D_c⟧⇐ₚ :: ⟦Γ⟧ ⊢ M_c ⇐ bool & d
└─ ⟦Γ⟧, x_c:bool ⊢ whileLoop x_c M_b M_k ⇐ ⟦A⟧ & d   [whileLoop]
   ├─ ⟦Γ⟧, x_c:bool ⊢ x_c ⇐ bool   [subsumption]
   │  ├─ ⟦Γ⟧, x_c:bool ⊢ x_c ⇒ bool   [var]
   │  └─ bool ≤ bool ↦ id
   ├─ ⟦D_b⟧⇐ₚ :: ⟦Γ⟧, x_c:bool ⊢ M_b ⇐ ⟦A⟧ & d
   └─ ⟦D_k⟧⇐ₚ* :: ⟦Γ⟧, x_c:bool ⊢ M_k ⇐ ⟦A⟧ & d
```
-/
partial def checkProducerWhile (md : Md) (cond body : StmtExprMd)
    (rest : List StmtExprMd) (retTy : HighType) (grade : Grade) : ElabM FGLProducer := do
  let cc ← checkValue cond .TBool
  let bp ← checkProducer body [] retTy grade
  let after ← checkProducers rest retTy grade
  pure (.whileLoop md cc bp after)

/-- ⟦·⟧⇐ₚ:
```
D_e :: Γ ⊢ e : A
─────────────────────
D :: Γ ⊢ (return e) : A

    ↦

⟦D_e⟧⇐ᵥ :: ⟦Γ⟧ ⊢ V_e ⇐ ⟦A⟧
─────────────────────────────────────
⟦D⟧⇐ₚ :: ⟦Γ⟧ ⊢ produce V_e ⇐ ⟦A⟧ & d
```
If e is effectful, the to-rule is applied first.
-/
partial def checkProducerReturn (md : Md) (valueOpt : Option StmtExprMd)
    (retTy : HighType) (grade : Grade) : ElabM FGLProducer := do
  match valueOpt with
  | some v =>
    let result ← synthExpr v
    match result with
    | .value val ty =>
      let coerced := applySubtype val ty (eraseType retTy)
      pure (.produce md coerced)
    | .call callee checkedArgs callRetTy callGrade =>
      guard (Grade.leq callGrade grade)
      dispatchCall md callee checkedArgs callGrade fun rv =>
        pure (.produce md (applySubtype rv (eraseType callRetTy) (eraseType retTy)))
  | none => pure (.produce md (.fromNone md))

/-- ⟦·⟧⇐ₚ (varDecl):
```
D :: Γ ⊢ (var x:T := e); k : A   [varDecl]
├─ D_e :: Γ ⊢ e : T
└─ D_k :: Γ, x:T ⊢ k : A

    ↦

⟦D⟧⇐ₚ :: ⟦Γ⟧ ⊢ varDecl x ⟦T⟧ M_e M_k ⇐ ⟦A⟧ & d   [varDecl]
├─ ⟦D_e⟧⇐ₚ :: ⟦Γ⟧ ⊢ M_e ⇐ ⟦T⟧ & d
└─ ⟦D_k⟧⇐ₚ* :: ⟦Γ⟧, x:⟦T⟧ ⊢ M_k ⇐ ⟦A⟧ & d
```
-/
partial def checkProducerVarDecl (md : Md) (nameId : Laurel.Identifier) (typeMd : HighTypeMd)
    (initOpt : Option StmtExprMd)
    (rest : List StmtExprMd) (retTy : HighType) (grade : Grade) : ElabM FGLProducer := do
  let ci ← match initOpt with
    | some ⟨.Hole false _, _⟩ => pure none
    | some ⟨.Hole true _, _⟩ => do let hv ← freshVar "hole"; pure (some (.staticCall md hv []))
    | some i => do let v ← checkValue i typeMd.val; pure (some v)
    | none => pure none
  mkVarDecl md nameId.text (eraseType typeMd.val) ci fun _ => checkProducers rest retTy grade

/-- ⟦·⟧⇐ₚ (assert):
```
D :: Γ ⊢ (assert c); k : A   [assert]
├─ D_c :: Γ ⊢ c : bool
└─ D_k :: Γ ⊢ k : A

    ↦

⟦D⟧⇐ₚ :: ⟦Γ⟧ ⊢ varDecl x_c bool M_c (assert x_c M_k) ⇐ ⟦A⟧ & d   [varDecl]
├─ ⟦D_c⟧⇐ₚ :: ⟦Γ⟧ ⊢ M_c ⇐ bool & d
└─ ⟦Γ⟧, x_c:bool ⊢ assert x_c M_k ⇐ ⟦A⟧ & d   [assert]
   ├─ ⟦Γ⟧, x_c:bool ⊢ x_c ⇐ bool   [subsumption]
   │  ├─ ⟦Γ⟧, x_c:bool ⊢ x_c ⇒ bool   [var]
   │  └─ bool ≤ bool ↦ id
   └─ ⟦D_k⟧⇐ₚ* :: ⟦Γ⟧, x_c:bool ⊢ M_k ⇐ ⟦A⟧ & d
```
-/
partial def checkProducerAssert (md : Md) (cond : StmtExprMd)
    (rest : List StmtExprMd) (retTy : HighType) (grade : Grade) : ElabM FGLProducer := do
  let cc ← checkValue cond .TBool
  let after ← checkProducers rest retTy grade
  pure (.assert md cc after)

/-- ⟦·⟧⇐ₚ (assume):
```
D :: Γ ⊢ (assume c); k : A   [assume]
├─ D_c :: Γ ⊢ c : bool
└─ D_k :: Γ ⊢ k : A

    ↦

⟦D⟧⇐ₚ :: ⟦Γ⟧ ⊢ varDecl x_c bool M_c (assume x_c M_k) ⇐ ⟦A⟧ & d   [varDecl]
├─ ⟦D_c⟧⇐ₚ :: ⟦Γ⟧ ⊢ M_c ⇐ bool & d
└─ ⟦Γ⟧, x_c:bool ⊢ assume x_c M_k ⇐ ⟦A⟧ & d   [assume]
   ├─ ⟦Γ⟧, x_c:bool ⊢ x_c ⇐ bool   [subsumption]
   │  ├─ ⟦Γ⟧, x_c:bool ⊢ x_c ⇒ bool   [var]
   │  └─ bool ≤ bool ↦ id
   └─ ⟦D_k⟧⇐ₚ* :: ⟦Γ⟧, x_c:bool ⊢ M_k ⇐ ⟦A⟧ & d
```
-/
partial def checkProducerAssume (md : Md) (cond : StmtExprMd)
    (rest : List StmtExprMd) (retTy : HighType) (grade : Grade) : ElabM FGLProducer := do
  let cc ← checkValue cond .TBool
  let after ← checkProducers rest retTy grade
  pure (.assume md cc after)

/-- ⟦·⟧⇐ₚ (call, grade(g) = d, ambient = e, d ≤ e):
```
D :: Γ ⊢ g(e₁,…,eₙ); k : A   [call]
├─ D_i :: Γ ⊢ eᵢ : Aᵢ  (for each i)
└─ D_k :: Γ ⊢ k : A

    ↦    let (pre, outs, r) = callingConvention(g, d)

⟦D⟧⇐ₚ :: ⟦Γ⟧ ⊢ varDecl x₁ ⟦A₁⟧ M₁ (… (varDecl xₙ ⟦Aₙ⟧ Mₙ (procedureCall g (pre ++ [x₁,…,xₙ]) outs M_k))) ⇐ ⟦A⟧ & e
├─ ⟦D₁⟧⇐ₚ :: ⟦Γ⟧ ⊢ M₁ ⇐ ⟦A₁⟧ & e   [varDecl]
│  └─ ⟦D₂⟧⇐ₚ :: ⟦Γ⟧, x₁:⟦A₁⟧ ⊢ M₂ ⇐ ⟦A₂⟧ & e   [varDecl]
│     └─ …   [varDecl]
│        └─ ⟦Γ⟧, x₁:⟦A₁⟧,…,xₙ:⟦Aₙ⟧ ⊢ procedureCall g (pre ++ [x₁,…,xₙ]) outs M_k ⇐ ⟦A⟧ & e   [producerSubsumption]
│           ├─ ⟦Γ⟧, x₁,…,xₙ ⊢ procedureCall g [x₁,…,xₙ] ⇒ ⟦B⟧ & d   [call]
│           │  └─ ⟦Γ⟧,… ⊢ xᵢ ⇐ ⟦Aᵢ⟧   [subsumption]
│           │     ├─ ⟦Γ⟧,… ⊢ xᵢ ⇒ ⟦Aᵢ⟧   [var]
│           │     └─ ⟦Aᵢ⟧ ≤ ⟦Aᵢ⟧ ↦ id
│           ├─ d ≤ e ↦ (pre, outs)
│           └─ ⟦D_k⟧⇐ₚ* :: ⟦Γ⟧, x₁,…,xₙ, outs ⊢ M_k ⇐ ⟦A⟧ & (d\e)
```
-/
partial def checkProducerStaticCall (md : Md) (callee : Laurel.Identifier) (args : List StmtExprMd)
    (rest : List StmtExprMd) (retTy : HighType) (grade : Grade) : ElabM FGLProducer := do
  let sig ← lookupFuncSig callee.text
  let params := match sig with | some s => s.params | none => []
  let callGrade := (← read).procGrades[callee.text]?.getD .pure
  guard (Grade.leq callGrade grade)
  checkArgsK args params grade fun checkedArgs => do
    match callGrade with
    | .pure => checkProducers rest retTy grade
    | _ => dispatchCall md callee.text checkedArgs callGrade fun _rv => checkProducers rest retTy grade

/-- ⟦·⟧⇐ₚ (block):
```
D :: Γ ⊢ {body}_l; k : A   [block]
├─ D_b :: Γ, l ⊢ body : A
└─ D_k :: Γ ⊢ k : A

    ↦

⟦D⟧⇐ₚ :: ⟦Γ⟧ ⊢ labeledBlock l M_b M_k ⇐ ⟦A⟧ & d   [labeledBlock]
├─ ⟦D_b⟧⇐ₚ :: ⟦Γ⟧, l ⊢ M_b ⇐ ⟦A⟧ & d
└─ ⟦D_k⟧⇐ₚ* :: ⟦Γ⟧ ⊢ M_k ⇐ ⟦A⟧ & d
```
Unlabeled blocks are flattened into the enclosing scope.
-/
partial def checkProducerBlock (md : Md) (stmts : List StmtExprMd) (label : Option String)
    (rest : List StmtExprMd) (retTy : HighType) (grade : Grade) : ElabM FGLProducer := do
  match label with
  | some l =>
    let blockProd ← checkProducers stmts retTy grade
    let after ← checkProducers rest retTy grade
    pure (.labeledBlock md l blockProd after)
  | none => checkProducers (stmts ++ rest) retTy grade

/-- ⟦·⟧⇐ₚ: dispatches on the Laurel statement form:
- `.IfThenElse` → `checkProducerIf`
- `.While` → `checkProducerWhile`
- `.Exit` → exit rule (inline)
- `.LocalVariable` → `checkProducerVarDecl`
- `.Assert` → `checkProducerAssert`
- `.Assume` → `checkProducerAssume`
- `.Assign` → `checkAssign`
- `.StaticCall` → `checkProducerStaticCall`
- `.Block` → `checkProducerBlock`
- `.Hole` → hole rule (inline)
-/
partial def checkProducer (stmt : StmtExprMd) (rest : List StmtExprMd) (retTy : HighType) (grade : Grade) : ElabM FGLProducer := do
  let md := stmt.md
  match stmt.val with
  | .IfThenElse cond thn els => checkProducerIf md cond thn els rest retTy grade
  | .While cond _invs _dec body => checkProducerWhile md cond body rest retTy grade
  | .Return valueOpt => checkProducerReturn md valueOpt retTy grade
  | .Exit target => pure (.exit md target)
  | .LocalVariable nameId typeMd initOpt => checkProducerVarDecl md nameId typeMd initOpt rest retTy grade
  | .Assert cond => checkProducerAssert md cond rest retTy grade
  | .Assume cond => checkProducerAssume md cond rest retTy grade
  | .Assign targets value => match targets with
    | [target] => checkAssign md target value rest retTy grade
    | _ => checkProducers rest retTy grade
  | .StaticCall callee args => checkProducerStaticCall md callee args rest retTy grade
  | .Block stmts label => checkProducerBlock md stmts label rest retTy grade
  | .New _ => failure
  | .Hole deterministic _ =>
    if deterministic then do
      let hv ← freshVar "hole"
      modify fun s => { s with usedHoles := s.usedHoles ++ [(hv, true, .TCore "Any")] }
      pure (.produce md (.staticCall md hv []))
    else
      do let hv ← freshVar "havoc"; mkVarDecl md hv (.TCore "Any") none fun _ => checkProducers rest retTy grade
  | _ => do let hv ← freshVar "unhandled"; mkVarDecl md hv (.TCore "Any") none fun _ => checkProducers rest retTy grade

-- checkProducers: elaborate remaining statements
partial def checkProducers (stmts : List StmtExprMd) (retTy : HighType) (grade : Grade) : ElabM FGLProducer := do
  match stmts with
  | [] => pure .unit
  | stmt :: rest => checkProducer stmt rest retTy grade

/-- ⟦·⟧⇐ₚ (field write):
```
D :: Γ ⊢ (obj.f := v); k : A   [fieldWrite]
├─ D_obj :: Γ ⊢ obj : C
├─ D_v :: Γ ⊢ v : fieldType(C,f)
└─ D_k :: Γ ⊢ k : A

    ↦

⟦D⟧⇐ₚ :: ⟦Γ⟧ ⊢ varDecl x_obj Composite M_obj (varDecl x_v ⟦fieldType(C,f)⟧ M_v (varDecl h' Heap M_update M_k)) ⇐ ⟦A⟧ & d   [varDecl]
├─ ⟦D_obj⟧⇐ₚ :: ⟦Γ⟧ ⊢ M_obj ⇐ Composite & d
└─ ⟦Γ⟧, x_obj:Composite ⊢ varDecl x_v ⟦fieldType(C,f)⟧ M_v (varDecl h' Heap M_update M_k) ⇐ ⟦A⟧ & d   [varDecl]
   ├─ ⟦D_v⟧⇐ₚ :: ⟦Γ⟧, x_obj ⊢ M_v ⇐ ⟦fieldType(C,f)⟧ & d
   └─ ⟦Γ⟧, x_obj, x_v ⊢ varDecl h' Heap M_update M_k ⇐ ⟦A⟧ & d   [varDecl]
      ├─ ⟦Γ⟧, x_obj, x_v ⊢ produce (functionCall updateField [$heap, x_obj, $field.C.f, functionCall box_T [x_v]]) ⇐ Heap & d   [produce]
      │  └─ ⟦Γ⟧, x_obj, x_v ⊢ functionCall updateField [$heap, x_obj, $field.C.f, functionCall box_T [x_v]] ⇐ Heap   [subsumption]
      │     ├─ ⟦Γ⟧, x_obj, x_v ⊢ functionCall updateField [$heap, x_obj, $field.C.f, functionCall box_T [x_v]] ⇒ Heap   [functionCall]
      │     │  ├─ ⟦Γ⟧, x_obj, x_v ⊢ $heap ⇐ Heap   [subsumption]
      │     │  │  ├─ ⟦Γ⟧, x_obj, x_v ⊢ $heap ⇒ Heap   [var]
      │     │  │  └─ Heap ≤ Heap ↦ id
      │     │  ├─ ⟦Γ⟧, x_obj, x_v ⊢ x_obj ⇐ Composite   [subsumption]
      │     │  │  ├─ ⟦Γ⟧, x_obj, x_v ⊢ x_obj ⇒ Composite   [var]
      │     │  │  └─ Composite ≤ Composite ↦ id
      │     │  ├─ ⟦Γ⟧, x_obj, x_v ⊢ functionCall $field.C.f [] ⇐ Field   [subsumption]
      │     │  │  ├─ ⟦Γ⟧, x_obj, x_v ⊢ functionCall $field.C.f [] ⇒ Field   [functionCall]
      │     │  │  └─ Field ≤ Field ↦ id
      │     │  └─ ⟦Γ⟧, x_obj, x_v ⊢ functionCall box_T [x_v] ⇐ Box   [subsumption]
      │     │     ├─ ⟦Γ⟧, x_obj, x_v ⊢ functionCall box_T [x_v] ⇒ Box   [functionCall]
      │     │     │  └─ ⟦Γ⟧, x_obj, x_v ⊢ x_v ⇐ ⟦fieldType(C,f)⟧   [subsumption]
      │     │     │     ├─ ⟦Γ⟧, x_obj, x_v ⊢ x_v ⇒ ⟦fieldType(C,f)⟧   [var]
      │     │     │     └─ ⟦fieldType(C,f)⟧ ≤ ⟦fieldType(C,f)⟧ ↦ id
      │     │     └─ Box ≤ Box ↦ id
      │     └─ Heap ≤ Heap ↦ id
      └─ ⟦D_k⟧⇐ₚ* :: ⟦Γ⟧, x_obj, x_v, h':Heap ⊢ M_k ⇐ ⟦A⟧ & d
```
-/
partial def checkAssignFieldWrite (md : Md) (obj : StmtExprMd) (field : Laurel.Identifier) (value : StmtExprMd)
    (rest : List StmtExprMd) (retTy : HighType) (grade : Grade) : ElabM FGLProducer := do
  guard (Grade.leq .heap grade)
  let (ov, objTy) ← synthValue obj
  match (← get).heapVar with
  | some hv =>
    let owner ← resolveFieldOwner field.text
    let qualifiedName := match owner with | some cn => "$field." ++ cn ++ "." ++ field.text | none => "$field." ++ field.text
    let fieldTy ← match owner with
      | some cn => do let ft ← lookupFieldType cn field.text; pure (ft.getD (.TCore "Any"))
      | none => pure (.TCore "Any")
    recordBoxUse fieldTy
    let cv ← checkValue value fieldTy
    let compositeObj := applySubtype ov objTy (.TCore "Composite")
    let boxed := FGLValue.staticCall md (boxConstructorName fieldTy) [cv]
    let newHeap := FGLValue.staticCall md "updateField" [.var md hv, compositeObj, .staticCall md qualifiedName [], boxed]
    let freshH ← freshVar "heap"
    modify fun s => { s with heapVar := some freshH }
    extendEnv freshH .THeap do
      let after ← checkProducers rest retTy grade
      pure (.varDecl md freshH (.TCore "Heap") (some newHeap) after)
  | none => failure

/-- ⟦·⟧⇐ₚ (effectful assignment):
```
D :: Γ ⊢ (x := g(e₁,…,eₙ)); k : A   [assign+call]
├─ D_i :: Γ ⊢ eᵢ : Aᵢ  (for each i)
└─ D_k :: Γ ⊢ k : A

    ↦    let (pre, outs, r) = callingConvention(g, d)

⟦D⟧⇐ₚ :: ⟦Γ⟧ ⊢ varDecl x₁ … (… (procedureCall g … outs (assign x c(x_r) M_k))) ⇐ ⟦A⟧ & e
├─ ⟦D₁⟧⇐ₚ :: ⟦Γ⟧ ⊢ M₁ ⇐ ⟦A₁⟧ & e   [varDecl]
│  └─ …   [varDecl]
│     └─ ⟦Γ⟧, x₁,…,xₙ ⊢ procedureCall g (pre ++ [x₁,…,xₙ]) outs (assign x c(x_r) M_k) ⇐ ⟦A⟧ & e   [producerSubsumption]
│        ├─ ⟦Γ⟧, x₁,…,xₙ ⊢ procedureCall g [x₁,…,xₙ] ⇒ ⟦B⟧ & d   [call]
│        ├─ d ≤ e ↦ (pre, outs)
│        └─ ⟦Γ⟧, x₁,…,xₙ, outs ⊢ assign x (produce c(x_r)) M_k ⇐ ⟦A⟧ & (d\e)   [assign]
│           ├─ ⟦Γ⟧,… ⊢ produce c(x_r) ⇐ ⟦Γ(x)⟧ & (d\e)   [produce]
│           │  └─ ⟦Γ⟧,… ⊢ c(x_r) ⇐ ⟦Γ(x)⟧   [subsumption]
│           │     ├─ ⟦Γ⟧,… ⊢ x_r ⇒ ⟦B⟧   [var]
│           │     └─ ⟦B⟧ ≤ ⟦Γ(x)⟧ ↦ c
│           └─ ⟦D_k⟧⇐ₚ* :: ⟦Γ⟧,… ⊢ M_k ⇐ ⟦A⟧ & (d\e)
```
where c coerces return type to ⟦Γ(x)⟧.
-/
partial def checkAssignStaticCall (md : Md) (tv : FGLValue) (targetTy : HighType) (needsDecl : Bool)
    (target : StmtExprMd) (callee : Laurel.Identifier) (args : List StmtExprMd)
    (rest : List StmtExprMd) (retTy : HighType) (grade : Grade) : ElabM FGLProducer := do
  let sig ← lookupFuncSig callee.text
  let retHty := match sig with | some s => s.returnType | none => .TCore "Any"
  let params := match sig with | some s => s.params | none => []
  let callGrade := (← read).procGrades[callee.text]?.getD .pure
  guard (Grade.leq callGrade grade)
  let assignOrDecl (val : FGLValue) : ElabM FGLProducer := do
    if needsDecl then
      let name := match target.val with | .Identifier id => id.text | _ => "_x"
      mkVarDecl md name (eraseType targetTy) (some val) fun _ => checkProducers rest retTy grade
    else do let after ← checkProducers rest retTy grade; pure (.assign md tv val after)
  checkArgsK args params grade fun checkedArgs => do
    match callGrade with
    | .pure =>
      let cv := FGLValue.staticCall md callee.text checkedArgs
      let coerced := applySubtype cv (eraseType retHty) (eraseType targetTy)
      assignOrDecl coerced
    | _ =>
      dispatchCall md callee.text checkedArgs callGrade fun rv => do
        let coerced := applySubtype rv (eraseType retHty) (eraseType targetTy)
        assignOrDecl coerced

/-- ⟦·⟧⇐ₚ (heap allocation):
```
D :: Γ ⊢ (x := new C); k : A   [assign+new]
└─ D_k :: Γ ⊢ k : A

    ↦

⟦D⟧⇐ₚ :: ⟦Γ⟧ ⊢ varDecl h' Heap (produce (functionCall increment [$heap])) (assign x (produce c(MkComposite(…))) M_k) ⇐ ⟦A⟧ & d   [varDecl]
├─ ⟦Γ⟧ ⊢ produce (functionCall increment [$heap]) ⇐ Heap & d   [produce]
│  └─ ⟦Γ⟧ ⊢ functionCall increment [$heap] ⇐ Heap   [subsumption]
│     ├─ ⟦Γ⟧ ⊢ functionCall increment [$heap] ⇒ Heap   [functionCall]
│     │  └─ ⟦Γ⟧ ⊢ $heap ⇐ Heap   [subsumption]
│     │     ├─ ⟦Γ⟧ ⊢ $heap ⇒ Heap   [var]
│     │     └─ Heap ≤ Heap ↦ id
│     └─ Heap ≤ Heap ↦ id
└─ ⟦Γ⟧, h':Heap ⊢ assign x (produce c(MkComposite(nextRef, C_TypeTag))) M_k ⇐ ⟦A⟧ & d   [assign]
   ├─ ⟦Γ⟧, h' ⊢ produce c(MkComposite(nextRef, C_TypeTag)) ⇐ ⟦Γ(x)⟧ & d   [produce]
   │  └─ ⟦Γ⟧, h' ⊢ c(MkComposite(Heap..nextReference!($heap), C_TypeTag)) ⇐ ⟦Γ(x)⟧   [subsumption]
   │     ├─ ⟦Γ⟧, h' ⊢ functionCall MkComposite [functionCall Heap..nextReference! [$heap], functionCall C_TypeTag []] ⇒ Composite   [functionCall]
   │     │  ├─ ⟦Γ⟧, h' ⊢ functionCall Heap..nextReference! [$heap] ⇐ int   [subsumption]
   │     │  │  ├─ ⟦Γ⟧, h' ⊢ functionCall Heap..nextReference! [$heap] ⇒ int   [functionCall]
   │     │  │  │  └─ ⟦Γ⟧, h' ⊢ $heap ⇐ Heap   [subsumption]
   │     │  │  │     ├─ ⟦Γ⟧, h' ⊢ $heap ⇒ Heap   [var]
   │     │  │  │     └─ Heap ≤ Heap ↦ id
   │     │  │  └─ int ≤ int ↦ id
   │     │  └─ ⟦Γ⟧, h' ⊢ functionCall C_TypeTag [] ⇐ TypeTag   [subsumption]
   │     │     ├─ ⟦Γ⟧, h' ⊢ functionCall C_TypeTag [] ⇒ TypeTag   [functionCall]
   │     │     └─ TypeTag ≤ TypeTag ↦ id
   │     └─ Composite ≤ ⟦Γ(x)⟧ ↦ c
   └─ ⟦D_k⟧⇐ₚ* :: ⟦Γ⟧, h', x:⟦Γ(x)⟧ ⊢ M_k ⇐ ⟦A⟧ & d
```
-/
partial def checkAssignNew (md : Md) (tv : FGLValue) (targetTy : HighType) (needsDecl : Bool)
    (target : StmtExprMd) (classId : Laurel.Identifier)
    (rest : List StmtExprMd) (retTy : HighType) (grade : Grade) : ElabM FGLProducer := do
  guard (Grade.leq .heap grade)
  match (← get).heapVar with
  | some hv =>
    let ref := FGLValue.staticCall md "Heap..nextReference!" [.var md hv]
    let newHeap := FGLValue.staticCall md "increment" [.var md hv]
    let obj := FGLValue.staticCall md "MkComposite" [ref, .staticCall md (classId.text ++ "_TypeTag") []]
    let coercedObj := applySubtype obj (.TCore "Composite") (eraseType targetTy)
    let freshH ← freshVar "heap"
    modify fun s => { s with heapVar := some freshH }
    extendEnv freshH .THeap do
      if needsDecl then
        let name := match target.val with | .Identifier id => id.text | _ => "_x"
        let cont ← extendEnv name (.UserDefined (Identifier.mk classId.text none)) (checkProducers rest retTy grade)
        pure (.varDecl md freshH (.TCore "Heap") (some newHeap) (.varDecl md name (eraseType targetTy) (some coercedObj) cont))
      else do
        let after ← checkProducers rest retTy grade
        pure (.varDecl md freshH (.TCore "Heap") (some newHeap) (.assign md tv coercedObj after))
  | none => failure

/-- ⟦·⟧⇐ₚ (assignment):
```
D :: Γ ⊢ (x := v); k : A   [assign]
├─ D_v :: Γ ⊢ v : B
└─ D_k :: Γ ⊢ k : A

    ↦

⟦D⟧⇐ₚ :: ⟦Γ⟧ ⊢ assign x M_v M_k ⇐ ⟦A⟧ & d   [assign]
├─ ⟦D_v⟧⇐ₚ :: ⟦Γ⟧ ⊢ M_v ⇐ ⟦Γ(x)⟧ & d
└─ ⟦D_k⟧⇐ₚ* :: ⟦Γ⟧ ⊢ M_k ⇐ ⟦A⟧ & d
```
-/
partial def checkAssignDefault (md : Md) (tv : FGLValue) (targetTy : HighType) (needsDecl : Bool)
    (target value : StmtExprMd)
    (rest : List StmtExprMd) (retTy : HighType) (grade : Grade) : ElabM FGLProducer := do
  let cv ← checkValue value targetTy
  if needsDecl then
    let name := match target.val with | .Identifier id => id.text | _ => "_x"
    mkVarDecl md name (eraseType targetTy) (some cv) fun _ => checkProducers rest retTy grade
  else do
    let after ← checkProducers rest retTy grade
    pure (.assign md tv cv after)

/-- Let-floating for assignments. Laurel's `x := e` has an arbitrary RHS that
    may be effectful. The translation let-floats: binds sub-expressions via
    `varDecl` until the RHS is in value form, then assigns. Dispatches on
    target form (field write) then RHS form (effectful call, new, hole, etc.). -/
partial def checkAssign (md : Md) (target value : StmtExprMd) (rest : List StmtExprMd) (retTy : HighType) (grade : Grade) : ElabM FGLProducer := do
  match target.val with
  | .FieldSelect obj field => checkAssignFieldWrite md obj field value rest retTy grade

  | _ =>
    let targetTy ← match target.val with
      | .Identifier id => match (← lookupEnv id.text) with | some (.variable t) => pure t | _ => pure (.TCore "Any")
      | _ => pure (.TCore "Any")
    let needsDecl ← match target.val with
      | .Identifier id => do match (← lookupEnv id.text) with | some _ => pure false | none => pure true
      | _ => pure false
    let (tv, _) ← synthValue target
    match value.val with
    | .IfThenElse cond thn els =>
      let assignThn : StmtExprMd := ⟨.Assign [target] thn, value.md⟩
      let assignEls : StmtExprMd := match els with
        | some e => ⟨.Assign [target] e, value.md⟩
        | none => ⟨.Block [] none, value.md⟩
      let desugared : StmtExprMd := ⟨.IfThenElse cond assignThn (some assignEls), value.md⟩
      checkProducer desugared rest retTy grade
    | .Block stmts _ =>
      match stmts.reverse with
      | last :: initRev =>
        let init := initRev.reverse
        let assignLast : StmtExprMd := ⟨.Assign [target] last, md⟩
        let desugared : StmtExprMd := ⟨.Block (init ++ [assignLast]) none, value.md⟩
        checkProducer desugared rest retTy grade
      | [] => checkProducers rest retTy grade
    | .Hole false _ =>
      if needsDecl then
        let name := match target.val with | .Identifier id => id.text | _ => "_havoc"
        mkVarDecl md name (eraseType targetTy) none fun _ => checkProducers rest retTy grade
      else
        do let hvName ← freshVar "havoc"; mkVarDecl md hvName (eraseType targetTy) none fun hv => do
          let after ← checkProducers rest retTy grade; pure (.assign md tv hv after)
    | .Hole true _ =>
      let hv ← freshVar "hole"
      modify fun s => { s with usedHoles := s.usedHoles ++ [(hv, true, targetTy)] }
      if needsDecl then
        let name := match target.val with | .Identifier id => id.text | _ => "_x"
        mkVarDecl md name (eraseType targetTy) (some (.staticCall md hv [])) fun _ => checkProducers rest retTy grade
      else do
        let after ← checkProducers rest retTy grade; pure (.assign md tv (.staticCall md hv []) after)
    | .New classId => checkAssignNew md tv targetTy needsDecl target classId rest retTy grade
    | .StaticCall callee args => checkAssignStaticCall md tv targetTy needsDecl target callee args rest retTy grade
    | .FieldSelect obj field =>
      guard (Grade.leq .heap grade)
      let (ov, objTy) ← synthValue obj
      match (← get).heapVar with
      | some hv =>
        let owner ← resolveFieldOwner field.text
        let qualifiedName := match owner with | some cn => "$field." ++ cn ++ "." ++ field.text | none => "$field." ++ field.text
        let fieldTy ← match owner with
          | some cn => do let ft ← lookupFieldType cn field.text; pure (ft.getD (.TCore "Any"))
          | none => pure (.TCore "Any")
        recordBoxUse fieldTy
        let compositeObj := applySubtype ov objTy (.TCore "Composite")
        let read := FGLValue.staticCall md "readField" [.var md hv, compositeObj, .staticCall md qualifiedName []]
        let unboxed := FGLValue.staticCall md (boxDestructorName fieldTy) [read]
        let coerced := applySubtype unboxed (eraseType fieldTy) (eraseType targetTy)
        if needsDecl then
          let name := match target.val with | .Identifier id => id.text | _ => "_x"
          mkVarDecl md name (eraseType targetTy) (some coerced) fun _ => checkProducers rest retTy grade
        else do let after ← checkProducers rest retTy grade; pure (.assign md tv coerced after)
      | none =>
        let fv := FGLValue.fieldAccess md ov field.text
        let after ← checkProducers rest retTy grade
        pure (.assign md tv fv after)
    | _ => checkAssignDefault md tv targetTy needsDecl target value rest retTy grade

end

/-! ## Grade Inference

Grade inference is coinductive over the call graph. For each procedure,
try elaboration at successively higher grades until one succeeds. When a
callee's grade exceeds the trial grade, the left residual is undefined,
elaboration fails (returns `none`), and the next grade is tried. The
finite lattice guarantees convergence. -/

/-- Try elaborating a procedure body at each grade in order. Returns the
    first grade that succeeds, or `heapErr` as fallback. -/
partial def tryGrades (callee : String) (env : ElabEnv) (body : StmtExprMd)
    (retTy : HighType) (grades : List Grade) : Option Grade :=
  match grades with
  | [] => some .heapErr
  | g :: rest =>
    let st : ElabState := {
      freshCounter := 0
      heapVar := if g == .heap || g == .heapErr then some "$heap" else none }
    let trialEnv := { env with procGrades := env.procGrades.insert callee g }
    match (checkProducer body [] retTy g).run trialEnv |>.run st with
    | some _ => some g
    | none => tryGrades callee env body retTy rest

/-! ## Projection

Maps FGL terms back to Laurel statements. The projection is trivial by
construction — the FGCBV structure uniquely determines the Laurel output.
`procedureCall` becomes declarations + assign + body. `varDecl` becomes
`LocalVariable`. Values map to their Laurel equivalents directly. -/

mutual
partial def projectValue : FGLValue → StmtExprMd
  | .litInt md n => mkLaurel md (.LiteralInt n)
  | .litBool md b => mkLaurel md (.LiteralBool b)
  | .litString md s => mkLaurel md (.LiteralString s)
  | .var md name => mkLaurel md (.Identifier (Identifier.mk name none))
  | .fromInt md v => mkLaurel md (.StaticCall (Identifier.mk "from_int" none) [projectValue v])
  | .fromStr md v => mkLaurel md (.StaticCall (Identifier.mk "from_str" none) [projectValue v])
  | .fromBool md v => mkLaurel md (.StaticCall (Identifier.mk "from_bool" none) [projectValue v])
  | .fromFloat md v => mkLaurel md (.StaticCall (Identifier.mk "from_float" none) [projectValue v])
  | .fromComposite md v => mkLaurel md (.StaticCall (Identifier.mk "from_Composite" none) [projectValue v])
  | .fromListAny md v => mkLaurel md (.StaticCall (Identifier.mk "from_ListAny" none) [projectValue v])
  | .fromDictStrAny md v => mkLaurel md (.StaticCall (Identifier.mk "from_DictStrAny" none) [projectValue v])
  | .fromNone md => mkLaurel md (.StaticCall (Identifier.mk "from_None" none) [])
  | .fieldAccess md obj f => mkLaurel md (.FieldSelect (projectValue obj) (Identifier.mk f none))
  | .staticCall md name args => mkLaurel md (.StaticCall (Identifier.mk name none) (args.map projectValue))

partial def projectProducer : FGLProducer → List StmtExprMd
  | .produce _md v => [projectValue v]
  | .assign md target val body => [mkLaurel md (.Assign [projectValue target] (projectValue val))] ++ projectProducer body
  | .varDecl md name ty init body => [mkLaurel md (.LocalVariable (Identifier.mk name none) (mkHighTypeMd md (liftType ty)) (init.map projectValue))] ++ projectProducer body
  | .ifThenElse md cond thn els after =>
    let elsProj := match els with
      | .unit => none
      | _ => some (mkLaurel md (.Block (projectProducer els) none))
    [mkLaurel md (.IfThenElse (projectValue cond) (mkLaurel md (.Block (projectProducer thn) none)) elsProj)] ++ projectProducer after
  | .whileLoop md cond body after => [mkLaurel md (.While (projectValue cond) [] none (mkLaurel md (.Block (projectProducer body) none)))] ++ projectProducer after
  | .assert md cond body => [mkLaurel md (.Assert (projectValue cond))] ++ projectProducer body
  | .assume md cond body => [mkLaurel md (.Assume (projectValue cond))] ++ projectProducer body
  | .procedureCall md callee args outputs body =>
    let call := mkLaurel md (.StaticCall (Identifier.mk callee none) (args.map projectValue))
    let decls := outputs.map fun (n, ty) => mkLaurel md (.LocalVariable (Identifier.mk n none) (mkHighTypeMd md (liftType ty)) (some (mkLaurel md (.Hole))))
    let targets := outputs.map fun (n, _) => mkLaurel md (.Identifier (Identifier.mk n none))
    decls ++ [mkLaurel md (.Assign targets call)] ++ projectProducer body
  | .exit md label => [mkLaurel md (.Exit label)]
  | .labeledBlock md label body after => [mkLaurel md (.Block (projectProducer body) (some label))] ++ projectProducer after
  | .unit => []
end

def projectBody (md : Md) (prod : FGLProducer) : StmtExprMd :=
  mkLaurel md (.Block (projectProducer prod) none)

/-! ## Entry Point

`fullElaborate` orchestrates both passes. Pass 1 iterates to a fixpoint on
grades. Pass 2 elaborates each procedure at its final grade and projects
back to Laurel. Also emits auxiliary datatypes (TypeTag, Composite, Field,
Box) and hole procedure declarations needed by the output program. -/

/-- Entry point: elaborates a Laurel program. Returns the elaborated program
    and a list of procedure names that failed to elaborate (emitted unchanged). -/
def fullElaborate (program : Laurel.Program) (runtime : Laurel.Program := default) (initialGrades : Std.HashMap String Grade := {}) : Except String (Laurel.Program × List String) := do
  let typeEnv := buildElabEnvFromProgram program runtime
  let baseEnv : ElabEnv := { typeEnv := typeEnv, program := program, runtime := runtime }

  -- PASS 1: Coinductive fixpoint iteration
  let mut knownGrades : Std.HashMap String Grade := initialGrades
  let mut changed := true
  while changed do
    changed := false
    for proc in program.staticProcedures do
      let bodyOpt := match proc.body with
        | .Transparent b => some b
        | .Opaque _ (some impl) _ => some impl
        | _ => none
      match bodyOpt with
      | some bodyExpr =>
        let extEnv := (proc.inputs ++ proc.outputs).foldl
          (fun (e : ElabTypeEnv) p => { e with names := e.names.insert p.name.text (.variable p.type.val) }) typeEnv
        let inputList := proc.inputs.map fun p => (p.name.text, p.type.val)
        let procEnv : ElabEnv := { baseEnv with typeEnv := extEnv, procGrades := knownGrades, procInputs := inputList }
        let retTy := match (proc.outputs.filter fun o => eraseType o.type.val != .TCore "Error").head? with
          | some o => o.type.val | none => .TCore "Any"
        match tryGrades proc.name.text procEnv bodyExpr retTy [.pure, .proc, .err, .heap, .heapErr] with
        | some g =>
          let g := if proc.outputs.length > 1 then Grade.join g .err else g
          if knownGrades[proc.name.text]? != some g then
            knownGrades := knownGrades.insert proc.name.text g
            changed := true
        | none => pure ()
      | none => pure ()

  -- PASS 2: Elaborate each proc with final grades
  let mut procs : List Laurel.Procedure := []
  let mut allBoxConstructors : List (String × String × HighType) := []
  let mut allHoles : List (String × Bool × List (String × HighType) × HighType) := []
  let mut elabFailures : List String := []
  for proc in program.staticProcedures do
    match proc.body with
    | .Transparent bodyExpr =>
      let extEnv := (proc.inputs ++ proc.outputs).foldl
        (fun (e : ElabTypeEnv) p => { e with names := e.names.insert p.name.text (.variable p.type.val) }) typeEnv
      let inputList := proc.inputs.map fun p => (p.name.text, p.type.val)
      let procEnv : ElabEnv := { baseEnv with typeEnv := extEnv, procGrades := knownGrades, procInputs := inputList }
      let g := knownGrades[proc.name.text]?.getD .pure
      let retTy := match (proc.outputs.filter fun o => eraseType o.type.val != .TCore "Error").head? with
        | some o => o.type.val | none => .TCore "Any"
      let st : ElabState := {
        freshCounter := 0
        heapVar := if g == .heap || g == .heapErr then some "$heap" else none }
      match (checkProducer bodyExpr [] retTy g).run procEnv |>.run st with
      | some (fgl, st') =>
        allBoxConstructors := allBoxConstructors ++ st'.usedBoxConstructors.filter
          (fun (c, _, _) => !allBoxConstructors.any (fun (c2, _, _) => c == c2))
        let newHoles := (st'.usedHoles.map fun (name, det, outTy) => (name, det, inputList, outTy)).filter
          (fun (n, _, _, _) => !allHoles.any (fun (n2, _, _, _) => n == n2))
        allHoles := allHoles ++ newHoles
        let projected := projectBody bodyExpr.md fgl
        let md := bodyExpr.md
        let heapInParam : Laurel.Parameter := { name := Identifier.mk "$heap_in" none, type := mkHighTypeMd md .THeap }
        let heapOutParam : Laurel.Parameter := { name := Identifier.mk "$heap" none, type := mkHighTypeMd md .THeap }
        let errOutParam : Laurel.Parameter := { name := Identifier.mk "maybe_except" none, type := mkHighTypeMd md (.TCore "Error") }
        let resultOutputs := proc.outputs.filter fun o => eraseType o.type.val != .TCore "Error"
        match g with
        | .heap =>
          let heapInit := mkLaurel md (.Assign [mkLaurel md (.Identifier (Identifier.mk "$heap" none))] (mkLaurel md (.Identifier (Identifier.mk "$heap_in" none))))
          let newBody := mkLaurel md (.Block ([heapInit] ++ (projectProducer fgl)) none)
          procs := procs ++ [{ proc with
            inputs := [heapInParam] ++ proc.inputs
            outputs := [heapOutParam] ++ resultOutputs
            body := .Transparent newBody }]
        | .heapErr =>
          let heapInit := mkLaurel md (.Assign [mkLaurel md (.Identifier (Identifier.mk "$heap" none))] (mkLaurel md (.Identifier (Identifier.mk "$heap_in" none))))
          let newBody := mkLaurel md (.Block ([heapInit] ++ (projectProducer fgl)) none)
          procs := procs ++ [{ proc with
            inputs := [heapInParam] ++ proc.inputs
            outputs := [heapOutParam] ++ resultOutputs ++ [errOutParam]
            body := .Transparent newBody }]
        | .err =>
          procs := procs ++ [{ proc with
            outputs := resultOutputs ++ [errOutParam]
            body := .Transparent projected }]
        | .proc | .pure =>
          procs := procs ++ [{ proc with body := .Transparent projected }]
      | none =>
        elabFailures := elabFailures ++ [proc.name.text]
        procs := procs ++ [proc]
    | _ => procs := procs ++ [proc]
  let hasHeap := knownGrades.toList.any fun (_, g) => g == .heap || g == .heapErr
  let compositeNames := typeEnv.classFields.toList.map (·.1)
  let typeTagDatatype : TypeDefinition := .Datatype {
    name := "TypeTag", typeArgs := [],
    constructors := compositeNames.map fun n => { name := Identifier.mk (n ++ "_TypeTag") none, args := [] } }
  let compositeType : TypeDefinition := .Datatype {
    name := "Composite", typeArgs := [],
    constructors := [{ name := Identifier.mk "MkComposite" none, args := [
      { name := Identifier.mk "ref" none, type := ⟨.TInt, #[]⟩ },
      { name := Identifier.mk "typeTag" none, type := ⟨.UserDefined "TypeTag", #[]⟩ }] }] }
  let fieldConstructors := typeEnv.classFields.toList.foldl (fun acc (className, fields) =>
    acc ++ fields.map fun (fieldName, _) =>
      { name := Identifier.mk ("$field." ++ className ++ "." ++ fieldName) none, args := [] : DatatypeConstructor }) []
  let fieldDatatype : TypeDefinition := .Datatype {
    name := "Field", typeArgs := [], constructors := fieldConstructors }
  let boxConstructors := allBoxConstructors.map fun (ctorName, _, ty) =>
    { name := Identifier.mk ctorName none, args := [
      { name := Identifier.mk (boxFieldName ty) none, type := ⟨boxFieldType ty, #[]⟩ }] : DatatypeConstructor }
  let boxDatatype : TypeDefinition := .Datatype {
    name := "Box", typeArgs := [], constructors := boxConstructors }
  let holeProcs := allHoles.map fun (name, deterministic, inputs, outTy) =>
    let params := inputs.map fun (pName, pType) =>
      ({ name := Identifier.mk pName none, type := ⟨pType, #[]⟩ } : Laurel.Parameter)
    let outputParam : Laurel.Parameter := { name := Identifier.mk "result" none, type := ⟨outTy, #[]⟩ }
    { name := Identifier.mk name none
      inputs := if deterministic then params else []
      outputs := [outputParam]
      preconditions := []
      determinism := if deterministic then .deterministic none else .nondeterministic
      decreases := none
      isFunctional := true
      body := .Opaque [] none []
      md := #[] : Laurel.Procedure }
  let result := if hasHeap then
    let heapTypesFiltered := heapConstants.types.filter fun td => match td with
      | .Datatype dt => dt.name.text != "Composite" && dt.name.text != "NotSupportedYet"
      | _ => true
    { program with
      staticProcedures := holeProcs ++ coreDefinitionsForLaurel.staticProcedures ++ heapConstants.staticProcedures ++ procs
      types := [fieldDatatype, boxDatatype, typeTagDatatype, compositeType] ++ heapTypesFiltered ++ coreDefinitionsForLaurel.types ++ program.types }
  else
    { program with
      staticProcedures := holeProcs ++ coreDefinitionsForLaurel.staticProcedures ++ procs
      types := [typeTagDatatype, compositeType] ++ coreDefinitionsForLaurel.types ++ program.types }
  pure (result, elabFailures)

end
end Strata.FineGrainLaurel

