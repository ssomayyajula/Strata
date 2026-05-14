/-
  Copyright Strata Contributors
  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.Languages.FineGrainLaurel.FineGrainLaurel
public import Strata.Languages.Laurel.Laurel
public import Strata.Languages.Laurel.HeapParameterizationConstants
public import Strata.Languages.Laurel.CoreDefinitionsForLaurel

namespace Strata.FineGrainLaurel
open Strata.Laurel
public section

-- ═══════════════════════════════════════════════════════════════════════════════
-- Internal types for Elaboration (derived from Laurel.Program, not from Resolution)
-- Tech debt: ideally call sites would carry callee signatures directly
-- ═══════════════════════════════════════════════════════════════════════════════

structure FuncSig where
  name : String
  params : List (String × HighType)
  returnType : HighType

instance : Inhabited FuncSig where
  default := { name := "", params := [], returnType := .TCore "Any" }

inductive NameInfo where
  | function (sig : FuncSig)
  | variable (ty : HighType)

instance : Inhabited NameInfo where
  default := .variable (.TCore "Any")

structure ElabTypeEnv where
  names : Std.HashMap String NameInfo := {}
  classFields : Std.HashMap String (List (String × HighType)) := {}
  deriving Inhabited

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

-- ═══════════════════════════════════════════════════════════════════════════════
-- Grade Monoid: {pure, proc, err, heap, heapErr}
-- Architecture §"The Grade Monoid"
-- ═══════════════════════════════════════════════════════════════════════════════

inductive Grade where | pure | proc | err | heap | heapErr deriving Inhabited, BEq, Repr

def Grade.leq : Grade → Grade → Bool
  | .pure, .pure => true | .pure, .proc => true | .pure, .err => true
  | .pure, .heap => true | .pure, .heapErr => true
  | .proc, .proc => true | .proc, .err => true | .proc, .heap => true | .proc, .heapErr => true
  | .err, .err => true | .err, .heapErr => true
  | .heap, .heap => true | .heap, .heapErr => true
  | .heapErr, .heapErr => true
  | _, _ => false

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

-- ═══════════════════════════════════════════════════════════════════════════════
-- Types: HighType → LowType erasure
-- Architecture §"Two Type Systems"
-- ═══════════════════════════════════════════════════════════════════════════════

inductive LowType where | TInt | TBool | TString | TFloat64 | TVoid | TCore (name : String)
  deriving Inhabited, Repr, BEq

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

def liftType : LowType → HighType
  | .TInt => .TInt | .TBool => .TBool | .TString => .TString
  | .TFloat64 => .TFloat64 | .TVoid => .TVoid | .TCore n => .TCore n

-- ═══════════════════════════════════════════════════════════════════════════════
-- FGL Terms — every constructor carries source metadata (correct by construction)
-- Architecture §"FGL Term Structure"
-- ═══════════════════════════════════════════════════════════════════════════════

abbrev Md := Imperative.MetaData Core.Expression

inductive FGLValue where
  | litInt (md : Md) (n : Int) | litBool (md : Md) (b : Bool) | litString (md : Md) (s : String)
  | var (md : Md) (name : String)
  | fromInt (md : Md) (inner : FGLValue) | fromStr (md : Md) (inner : FGLValue)
  | fromBool (md : Md) (inner : FGLValue) | fromFloat (md : Md) (inner : FGLValue)
  | fromComposite (md : Md) (inner : FGLValue) | fromListAny (md : Md) (inner : FGLValue)
  | fromDictStrAny (md : Md) (inner : FGLValue) | fromNone (md : Md)
  | fieldAccess (md : Md) (obj : FGLValue) (field : String)
  | staticCall (md : Md) (name : String) (args : List FGLValue)
  deriving Inhabited

def FGLValue.getMd : FGLValue → Md
  | .litInt md _ | .litBool md _ | .litString md _ | .var md _
  | .fromInt md _ | .fromStr md _ | .fromBool md _ | .fromFloat md _
  | .fromComposite md _ | .fromListAny md _ | .fromDictStrAny md _ | .fromNone md
  | .fieldAccess md _ _ | .staticCall md _ _ => md

inductive FGLProducer where
  | returnValue (md : Md) (v : FGLValue)
  | assign (md : Md) (target : FGLValue) (val : FGLValue) (body : FGLProducer)
  | varDecl (md : Md) (name : String) (ty : LowType) (init : Option FGLValue) (body : FGLProducer)
  | ifThenElse (md : Md) (cond : FGLValue) (thn : FGLProducer) (els : FGLProducer) (after : FGLProducer)
  | whileLoop (md : Md) (cond : FGLValue) (body : FGLProducer) (after : FGLProducer)
  | assert (md : Md) (cond : FGLValue) (body : FGLProducer)
  | assume (md : Md) (cond : FGLValue) (body : FGLProducer)
  | effectfulCall (md : Md) (callee : String) (args : List FGLValue)
      (outputs : List (String × LowType)) (body : FGLProducer)
  | exit (md : Md) (label : String)
  | labeledBlock (md : Md) (label : String) (body : FGLProducer) (after : FGLProducer)
  | unit
  deriving Inhabited

-- ═══════════════════════════════════════════════════════════════════════════════
-- Monad
-- ═══════════════════════════════════════════════════════════════════════════════

structure ElabEnv where
  typeEnv : ElabTypeEnv
  program : Laurel.Program
  runtime : Laurel.Program := default
  procGrades : Std.HashMap String Grade := {}
  procInputs : List (String × HighType) := []

structure ElabState where
  freshCounter : Nat := 0
  heapVar : Option String := none
  usedBoxConstructors : List (String × String × HighType) := []
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

-- ═══════════════════════════════════════════════════════════════════════════════
-- gradeFromSignature
-- Architecture §"User/Runtime Separation"
-- ═══════════════════════════════════════════════════════════════════════════════

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

-- ═══════════════════════════════════════════════════════════════════════════════
-- HOAS Smart Constructors
-- Architecture §"Subgrading Witness"
-- ═══════════════════════════════════════════════════════════════════════════════

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
  pure (.effectfulCall md callee args lowOutputs cont)

def mkVarDecl (md : Md) (name : String) (ty : LowType) (init : Option FGLValue)
    (body : FGLValue → ElabM FGLProducer) : ElabM FGLProducer := do
  let cont ← extendEnv name (liftType ty) (body (.var md name))
  pure (.varDecl md name ty init cont)

-- mkGradedCall: THE single call constructor for all grades > pure.
-- Grade determines whether to prepend heap. Outputs come from the proc's declaration.
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

-- ═══════════════════════════════════════════════════════════════════════════════
-- Subsumption
-- Architecture §"Subsumption Table"
-- ═══════════════════════════════════════════════════════════════════════════════

inductive CoercionResult where | refl | coerce (w : Md → FGLValue → FGLValue) | unrelated
  deriving Inhabited

def subsume (actual expected : LowType) : CoercionResult :=
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

def applySubsume (val : FGLValue) (actual expected : LowType) : FGLValue :=
  match subsume actual expected with | .refl => val | .coerce c => c val.getMd val | .unrelated => val

-- ═══════════════════════════════════════════════════════════════════════════════
-- Defunctionalized producer synthesis result
-- Architecture §"Elaboration Structure"
-- ═══════════════════════════════════════════════════════════════════════════════

inductive SynthResult where
  | value (val : FGLValue) (ty : LowType)
  | call (callee : String) (args : List FGLValue) (retTy : HighType) (grade : Grade)
  deriving Inhabited

-- ═══════════════════════════════════════════════════════════════════════════════
-- Typing Rules (mutual block)
-- Architecture §"Value Rules", §"Producer Synthesis", §"Producer Checking"
-- ═══════════════════════════════════════════════════════════════════════════════

mutual

-- Γ ⊢_v V ⇒ A (value synthesis)
-- Architecture: literals, variables, pure function calls (grade = 1)
partial def synthValue (expr : StmtExprMd) : ElabM (FGLValue × LowType) := do
  let md := expr.md
  match expr.val with
  | .LiteralInt n => pure (.litInt md n, .TInt)
  | .LiteralBool b => pure (.litBool md b, .TBool)
  | .LiteralString s => pure (.litString md s, .TString)
  | .Identifier id =>
    match (← lookupEnv id.text) with
    | some (.variable ty) => pure (.var md id.text, eraseType ty)
    | some (.function sig) => pure (.var md id.text, eraseType sig.returnType)
    | _ => pure (.var md id.text, .TCore "Any")
  | .FieldSelect obj field =>
    let (ov, objTy) ← synthValue obj
    match (← get).heapVar with
    | some hv =>
      let owner ← resolveFieldOwner field.text
      let qualifiedName := match owner with | some cn => "$field." ++ cn ++ "." ++ field.text | none => "$field." ++ field.text
      let fieldTy ← match owner with
        | some cn => do let ft ← lookupFieldType cn field.text; pure (ft.getD (.TCore "Any"))
        | none => pure (.TCore "Any")
      recordBoxUse fieldTy
      let compositeObj := applySubsume ov objTy (.TCore "Composite")
      let read := FGLValue.staticCall md "readField" [.var md hv, compositeObj, .staticCall md qualifiedName []]
      pure (.staticCall md (boxDestructorName fieldTy) [read], eraseType fieldTy)
    | none => failure
  | .StaticCall callee args =>
    -- Value rule: f(v₁,...,vₙ) ⇒ B requires grade(f) = 1 (pure)
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
  | .Hole deterministic _ => do
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
  | _ => failure

-- Γ ⊢_v V ⇐ A (value checking = synth + subsume)
partial def checkValue (expr : StmtExprMd) (expected : HighType) : ElabM FGLValue := do
  let (val, actual) ← synthValue expr
  pure (applySubsume val actual (eraseType expected))

-- synthExpr: value OR producer (defunctionalized)
-- If grade = pure → value. If grade > pure → call (needs binding via to-rule).
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

-- checkArgsK: to-rule applied at expression level (ANF-lift effectful args)
-- Architecture §"Block elaboration"
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
        let coerced := applySubsume val ty (eraseType pty)
        go rest ptysRest (coerced :: acc)
      | .call callee checkedArgs retTy callGrade =>
        guard (Grade.leq callGrade grade)
        dispatchCall arg.md callee checkedArgs callGrade fun rv =>
          go rest ptysRest (applySubsume rv (eraseType retTy) (eraseType pty) :: acc)
  go args paramTypes []

-- ═══════════════════════════════════════════════════════════════════════════════
-- checkProducer: THE main recursive function
-- Architecture §"Producer Checking", §"Assignment Rules"
-- ═══════════════════════════════════════════════════════════════════════════════

partial def checkProducer (stmt : StmtExprMd) (rest : List StmtExprMd) (retTy : HighType) (grade : Grade) : ElabM FGLProducer := do
  let md := stmt.md
  match stmt.val with

  -- if V then M else N: branches standalone, rest in after
  | .IfThenElse cond thn els =>
    let cc ← checkValue cond .TBool
    let tp ← checkProducer thn [] retTy grade
    let ep ← match els with
      | some e => checkProducer e [] retTy grade
      | none => pure .unit
    let after ← elabRest rest retTy grade
    pure (.ifThenElse md cc tp ep after)

  -- while V do M
  | .While cond _invs _dec body =>
    let cc ← checkValue cond .TBool
    let bp ← checkProducer body [] retTy grade
    let after ← elabRest rest retTy grade
    pure (.whileLoop md cc bp after)

  -- return V
  | .Return valueOpt =>
    match valueOpt with
    | some v =>
      let result ← synthExpr v
      match result with
      | .value val ty =>
        let coerced := applySubsume val ty (eraseType retTy)
        pure (.returnValue md coerced)
      | .call callee checkedArgs callRetTy callGrade =>
        guard (Grade.leq callGrade grade)
        dispatchCall md callee checkedArgs callGrade fun rv =>
          pure (.returnValue md (applySubsume rv (eraseType callRetTy) (eraseType retTy)))
    | none => pure (.returnValue md (.fromNone md))

  -- exit label
  | .Exit target => pure (.exit md target)

  -- var x:T := V; body
  | .LocalVariable nameId typeMd initOpt =>
    let ci ← match initOpt with
      | some ⟨.Hole false _, _⟩ => pure none
      | some ⟨.Hole true _, _⟩ => do let hv ← freshVar "hole"; pure (some (.staticCall md hv []))
      | some i => do let v ← checkValue i typeMd.val; pure (some v)
      | none => pure none
    mkVarDecl md nameId.text (eraseType typeMd.val) ci fun _ => elabRest rest retTy grade

  -- assert V
  | .Assert cond =>
    let cc ← checkValue cond .TBool
    let after ← elabRest rest retTy grade
    pure (.assert md cc after)

  -- assume V
  | .Assume cond =>
    let cc ← checkValue cond .TBool
    let after ← elabRest rest retTy grade
    pure (.assume md cc after)

  -- Assign [target] value — the to-rule for assignments
  | .Assign targets value => match targets with
    | [target] => checkAssign md target value rest retTy grade
    | _ => elabRest rest retTy grade

  -- StaticCall at statement level (effectful call, grade > 1)
  | .StaticCall callee args =>
    let sig ← lookupFuncSig callee.text
    let params := match sig with | some s => s.params | none => []
    let callGrade := (← read).procGrades[callee.text]?.getD .pure
    guard (Grade.leq callGrade grade)
    checkArgsK args params grade fun checkedArgs => do
      match callGrade with
      | .pure => elabRest rest retTy grade
      | _ => dispatchCall md callee.text checkedArgs callGrade fun _rv => elabRest rest retTy grade

  -- Block (labeled or unlabeled)
  | .Block stmts label =>
    match label with
    | some l =>
      let blockProd ← elabRest stmts retTy grade
      let after ← elabRest rest retTy grade
      pure (.labeledBlock md l blockProd after)
    | none => elabRest (stmts ++ rest) retTy grade

  -- Standalone New: elaboration failure (breaks producer synthesis inversion)
  | .New _ => failure

  | .Hole deterministic _ =>
    if deterministic then do
      let hv ← freshVar "hole"
      modify fun s => { s with usedHoles := s.usedHoles ++ [(hv, true, .TCore "Any")] }
      pure (.returnValue md (.staticCall md hv []))
    else
      do let hv ← freshVar "havoc"; mkVarDecl md hv (.TCore "Any") none fun _ => elabRest rest retTy grade

  -- Architecture §"Core Interface": must not fail. Emit havoc for unhandled.
  | _ => do let hv ← freshVar "unhandled"; mkVarDecl md hv (.TCore "Any") none fun _ => elabRest rest retTy grade

-- elabRest: elaborate remaining statements
partial def elabRest (stmts : List StmtExprMd) (retTy : HighType) (grade : Grade) : ElabM FGLProducer := do
  match stmts with
  | [] => pure .unit
  | stmt :: rest => checkProducer stmt rest retTy grade

-- ═══════════════════════════════════════════════════════════════════════════════
-- checkAssign: assignment handled uniformly via typing rules
-- Architecture §"Assignment Rules"
-- ═══════════════════════════════════════════════════════════════════════════════

partial def checkAssign (md : Md) (target value : StmtExprMd) (rest : List StmtExprMd) (retTy : HighType) (grade : Grade) : ElabM FGLProducer := do
  match target.val with
  -- Field write: obj.field := v (heap effect)
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
      let cv ← checkValue value fieldTy
      let compositeObj := applySubsume ov objTy (.TCore "Composite")
      let boxed := FGLValue.staticCall md (boxConstructorName fieldTy) [cv]
      let newHeap := FGLValue.staticCall md "updateField" [.var md hv, compositeObj, .staticCall md qualifiedName [], boxed]
      let freshH ← freshVar "heap"
      modify fun s => { s with heapVar := some freshH }
      extendEnv freshH .THeap do
        let after ← elabRest rest retTy grade
        pure (.varDecl md freshH (.TCore "Heap") (some newHeap) after)
    | none => failure

  | _ =>
    let targetTy ← match target.val with
      | .Identifier id => match (← lookupEnv id.text) with | some (.variable t) => pure t | _ => pure (.TCore "Any")
      | _ => pure (.TCore "Any")
    let needsDecl ← match target.val with
      | .Identifier id => do match (← lookupEnv id.text) with | some _ => pure false | none => pure true
      | _ => pure false
    let (tv, _) ← synthValue target
    match value.val with
    -- IfThenElse RHS (ternary): desugar to statement-level if
    | .IfThenElse cond thn els =>
      let assignThn : StmtExprMd := ⟨.Assign [target] thn, value.md⟩
      let assignEls : StmtExprMd := match els with
        | some e => ⟨.Assign [target] e, value.md⟩
        | none => ⟨.Block [] none, value.md⟩
      let desugared : StmtExprMd := ⟨.IfThenElse cond assignThn (some assignEls), value.md⟩
      checkProducer desugared rest retTy grade
    -- Block RHS (class instantiation): desugar
    | .Block stmts _ =>
      match stmts.reverse with
      | last :: initRev =>
        let init := initRev.reverse
        let assignLast : StmtExprMd := ⟨.Assign [target] last, md⟩
        let desugared : StmtExprMd := ⟨.Block (init ++ [assignLast]) none, value.md⟩
        checkProducer desugared rest retTy grade
      | [] => elabRest rest retTy grade
    -- Hole RHS
    | .Hole false _ =>
      if needsDecl then
        let name := match target.val with | .Identifier id => id.text | _ => "_havoc"
        mkVarDecl md name (eraseType targetTy) none fun _ => elabRest rest retTy grade
      else
        do let hvName ← freshVar "havoc"; mkVarDecl md hvName (eraseType targetTy) none fun hv => do
          let after ← elabRest rest retTy grade; pure (.assign md tv hv after)
    | .Hole true _ =>
      let hv ← freshVar "hole"
      -- TECH DEBT: holes should be a graded effect, not ad-hoc collection
      modify fun s => { s with usedHoles := s.usedHoles ++ [(hv, true, targetTy)] }
      if needsDecl then
        let name := match target.val with | .Identifier id => id.text | _ => "_x"
        mkVarDecl md name (eraseType targetTy) (some (.staticCall md hv [])) fun _ => elabRest rest retTy grade
      else do
        let after ← elabRest rest retTy grade; pure (.assign md tv (.staticCall md hv []) after)
    -- New RHS (heap effect + coercion)
    | .New classId =>
      guard (Grade.leq .heap grade)
      match (← get).heapVar with
      | some hv =>
        let ref := FGLValue.staticCall md "Heap..nextReference!" [.var md hv]
        let newHeap := FGLValue.staticCall md "increment" [.var md hv]
        let obj := FGLValue.staticCall md "MkComposite" [ref, .staticCall md (classId.text ++ "_TypeTag") []]
        let coercedObj := applySubsume obj (.TCore "Composite") (eraseType targetTy)
        let freshH ← freshVar "heap"
        modify fun s => { s with heapVar := some freshH }
        extendEnv freshH .THeap do
          if needsDecl then
            let name := match target.val with | .Identifier id => id.text | _ => "_x"
            let cont ← extendEnv name (.UserDefined (Identifier.mk classId.text none)) (elabRest rest retTy grade)
            pure (.varDecl md freshH (.TCore "Heap") (some newHeap) (.varDecl md name (eraseType targetTy) (some coercedObj) cont))
          else do
            let after ← elabRest rest retTy grade
            pure (.varDecl md freshH (.TCore "Heap") (some newHeap) (.assign md tv coercedObj after))
      | none => failure
    -- StaticCall RHS (to-rule: effectful call → bind → assign)
    | .StaticCall callee args =>
      let sig ← lookupFuncSig callee.text
      let retHty := match sig with | some s => s.returnType | none => .TCore "Any"
      let params := match sig with | some s => s.params | none => []
      let callGrade := (← read).procGrades[callee.text]?.getD .pure
      guard (Grade.leq callGrade grade)
      let assignOrDecl (val : FGLValue) : ElabM FGLProducer := do
        if needsDecl then
          let name := match target.val with | .Identifier id => id.text | _ => "_x"
          mkVarDecl md name (eraseType targetTy) (some val) fun _ => elabRest rest retTy grade
        else do let after ← elabRest rest retTy grade; pure (.assign md tv val after)
      checkArgsK args params grade fun checkedArgs => do
        match callGrade with
        | .pure =>
          let cv := FGLValue.staticCall md callee.text checkedArgs
          let coerced := applySubsume cv (eraseType retHty) (eraseType targetTy)
          assignOrDecl coerced
        | _ =>
          dispatchCall md callee.text checkedArgs callGrade fun rv => do
            let coerced := applySubsume rv (eraseType retHty) (eraseType targetTy)
            assignOrDecl coerced
    -- FieldSelect RHS (heap read)
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
        let compositeObj := applySubsume ov objTy (.TCore "Composite")
        let read := FGLValue.staticCall md "readField" [.var md hv, compositeObj, .staticCall md qualifiedName []]
        let unboxed := FGLValue.staticCall md (boxDestructorName fieldTy) [read]
        let coerced := applySubsume unboxed (eraseType fieldTy) (eraseType targetTy)
        if needsDecl then
          let name := match target.val with | .Identifier id => id.text | _ => "_x"
          mkVarDecl md name (eraseType targetTy) (some coerced) fun _ => elabRest rest retTy grade
        else do let after ← elabRest rest retTy grade; pure (.assign md tv coerced after)
      | none =>
        let fv := FGLValue.fieldAccess md ov field.text
        let after ← elabRest rest retTy grade
        pure (.assign md tv fv after)
    -- Default: checkValue on RHS
    | _ =>
      let cv ← checkValue value targetTy
      if needsDecl then
        let name := match target.val with | .Identifier id => id.text | _ => "_x"
        mkVarDecl md name (eraseType targetTy) (some cv) fun _ => elabRest rest retTy grade
      else do
        let after ← elabRest rest retTy grade
        pure (.assign md tv cv after)

end

-- ═══════════════════════════════════════════════════════════════════════════════
-- tryGrades: coinductive fixpoint helper
-- Architecture §"Grade Inference"
-- ═══════════════════════════════════════════════════════════════════════════════

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

-- ═══════════════════════════════════════════════════════════════════════════════
-- Projection
-- Architecture §"Projection"
-- ═══════════════════════════════════════════════════════════════════════════════

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
  | .returnValue _md v => [projectValue v]
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
  | .effectfulCall md callee args outputs body =>
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

-- ═══════════════════════════════════════════════════════════════════════════════
-- fullElaborate: entry point
-- Architecture §"fullElaborate structure"
-- ═══════════════════════════════════════════════════════════════════════════════

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

