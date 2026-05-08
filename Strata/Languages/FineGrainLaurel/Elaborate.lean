/-
  Copyright Strata Contributors
  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.Languages.FineGrainLaurel.FineGrainLaurel
public import Strata.Languages.Laurel.Laurel
public import Strata.Languages.Laurel.HeapParameterizationConstants
public import Strata.Languages.Laurel.CoreDefinitionsForLaurel
public import Strata.Languages.Python.NameResolution

namespace Strata.FineGrainLaurel
open Strata.Laurel
open Strata.Python.Resolution
public section

def mkLaurel (md : Imperative.MetaData Core.Expression) (e : StmtExpr) : StmtExprMd :=
  { val := e, md := md }
def mkHighTypeMd (md : Imperative.MetaData Core.Expression) (ty : HighType) : HighTypeMd :=
  { val := ty, md := md }

-- Grade Monoid

inductive Grade where | pure | err | heap | heapErr deriving Inhabited, BEq, Repr

def Grade.leq : Grade → Grade → Bool
  | .pure, _ => true
  | .err, .err => true | .err, .heapErr => true
  | .heap, .heap => true | .heap, .heapErr => true
  | .heapErr, .heapErr => true
  | _, _ => false

def Grade.join : Grade → Grade → Grade
  | .pure, e => e | e, .pure => e
  | .err, .heap => .heapErr | .heap, .err => .heapErr
  | .err, .err => .err | .heap, .heap => .heap
  | .heapErr, _ => .heapErr | _, .heapErr => .heapErr

-- Types

inductive LowType where | TInt | TBool | TString | TFloat64 | TVoid | TCore (name : String)
  deriving Inhabited, Repr, BEq

def eraseType : HighType → LowType
  | .TInt => .TInt | .TBool => .TBool | .TString => .TString
  | .TFloat64 => .TFloat64 | .TVoid => .TVoid | .TCore n => .TCore n
  | .UserDefined id => match id.text with
    | "Any" => .TCore "Any"
    | "Error" => .TCore "Error"
    | "ListAny" => .TCore "ListAny"
    | "DictStrAny" => .TCore "DictStrAny"
    | "Box" => .TCore "Box"
    | "Field" => .TCore "Field"
    | "TypeTag" => .TCore "TypeTag"
    | _ => .TCore "Composite"
  | .THeap => .TCore "Heap"
  | .TReal => .TCore "real" | .TTypedField _ => .TCore "Field"
  | .TSet _ | .TMap _ _ | .Applied _ _ | .Intersection _ | .Unknown => .TCore "Any"
  | .Pure _ => .TCore "Composite"

def liftType : LowType → HighType
  | .TInt => .TInt | .TBool => .TBool | .TString => .TString
  | .TFloat64 => .TFloat64 | .TVoid => .TVoid | .TCore n => .TCore n

-- FGL Terms — every constructor carries source metadata (correct by construction)

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

-- Monad

structure ElabEnv where
  typeEnv : TypeEnv
  program : Laurel.Program
  runtime : Laurel.Program := default
  procGrades : Std.HashMap String Grade := {}

structure ElabState where
  freshCounter : Nat := 0
  heapVar : Option String := none
  usedBoxConstructors : List (String × String × HighType) := []

abbrev ElabM := ReaderT ElabEnv (StateT ElabState Option)

private def freshVar (pfx : String := "tmp") : ElabM String := do
  let s ← get; set { s with freshCounter := s.freshCounter + 1 }; pure s!"{pfx}${s.freshCounter}"

-- Box protocol (type-directed)

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
  | .TCore "Any" => "Box..anyVal!"
  | .TCore name => s!"Box..{name}Val!"
  | _ => "Box..compositeVal!"

def boxFieldName (ty : HighType) : String :=
  match ty with
  | .TInt => "intVal" | .TBool => "boolVal" | .TFloat64 => "float64Val"
  | .TReal => "realVal" | .TString => "stringVal"
  | .UserDefined _ => "compositeVal"
  | .TCore "Any" => "anyVal"
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

-- Grade from procedure signature (structural: Error output → err, Heap param → heap)
def gradeFromSignature (proc : Laurel.Procedure) : Grade :=
  let hasError := proc.outputs.any fun o => eraseType o.type.val == .TCore "Error"
  let hasHeap := proc.inputs.any fun i => eraseType i.type.val == .TCore "Heap"
  match hasHeap, hasError with
  | true, true => .heapErr
  | true, false => .heap
  | false, true => .err
  | false, false => .pure

-- Env helpers

def lookupEnv (name : String) : ElabM (Option NameInfo) := do pure (← read).typeEnv.names[name]?
def extendEnv (name : String) (ty : HighType) (action : ElabM α) : ElabM α :=
  withReader (fun env => { env with typeEnv := { env.typeEnv with names := env.typeEnv.names.insert name (.variable ty) } }) action
def lookupFuncSig (name : String) : ElabM (Option FuncSig) := do
  match (← read).typeEnv.names[name]? with | some (.function sig) => pure (some sig) | _ => pure none
def lookupProcBody (name : String) : ElabM (Option StmtExprMd) := do
  let env ← read
  let findIn (procs : List Laurel.Procedure) : Option StmtExprMd :=
    match procs.find? (fun p => p.name.text == name) with
    | some proc => match proc.body with
      | .Transparent b => some b
      | .Opaque _ (some impl) _ => some impl
      | _ => none
    | none => none
  match findIn env.program.staticProcedures with
  | some b => pure (some b)
  | none =>
    pure none

def lookupFieldType (className fieldName : String) : ElabM (Option HighType) := do
  match (← read).typeEnv.classFields[className]? with
  | some fields => pure (fields.find? (fun (n, _) => n == fieldName) |>.map (·.2))
  | none => pure none

def resolveFieldOwner (fieldName : String) : ElabM (Option String) := do
  for (className, fields) in (← read).typeEnv.classFields.toList do
    if fields.any (fun (n, _) => n == fieldName) then return some className
  pure none

-- HOAS Smart Constructors — all take md from the source statement

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

def mkErrorCall (md : Md) (callee : String) (args : List FGLValue) (resultTy : HighType)
    (body : FGLValue → ElabM FGLProducer) : ElabM FGLProducer :=
  mkEffectfulCall md callee args [("result", resultTy), ("err", .TCore "Error")]
    fun outs => body outs[0]!

def mkHeapCall (md : Md) (callee : String) (args : List FGLValue) (resultTy : HighType)
    (body : FGLValue → ElabM FGLProducer) : ElabM FGLProducer := do
  let hv := (← get).heapVar
  let heapArg := match hv with | some h => FGLValue.var md h | none => FGLValue.var md "$heap"
  mkEffectfulCall md callee (heapArg :: args) [("heap", .THeap), ("result", resultTy)]
    fun outs => do
      match outs[0]! with | .var _ n => modify fun s => { s with heapVar := some n } | _ => pure ()
      body outs[1]!

def mkHeapErrorCall (md : Md) (callee : String) (args : List FGLValue) (resultTy : HighType)
    (body : FGLValue → ElabM FGLProducer) : ElabM FGLProducer := do
  let hv := (← get).heapVar
  let heapArg := match hv with | some h => FGLValue.var md h | none => FGLValue.var md "$heap"
  mkEffectfulCall md callee (heapArg :: args) [("heap", .THeap), ("result", resultTy), ("err", .TCore "Error")]
    fun outs => do
      match outs[0]! with | .var _ n => modify fun s => { s with heapVar := some n } | _ => pure ()
      body outs[1]!

-- Subsumption — coercions inherit md from the value being coerced

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

-- Defunctionalized producer synthesis result.
-- Describes what an expression produces WITHOUT needing the rest of the block.
inductive SynthResult where
  | value (val : FGLValue) (ty : LowType)
  | call (callee : String) (args : List FGLValue) (retTy : HighType) (grade : Grade)
  deriving Inhabited

-- Elaboration
-- checkProducer is THE entry point. It takes remaining statements as continuation.
-- Each FGL node threads the rest into its body field.

mutual

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
    let sig ← lookupFuncSig callee.text
    match sig with
    | some s =>
      let checkedArgs ← checkArgs args s.params
      pure (.staticCall md callee.text checkedArgs, eraseType s.returnType)
    | none =>
      let checkedArgs ← args.mapM fun arg => checkValue arg (.TCore "Any")
      pure (.staticCall md callee.text checkedArgs, .TCore "Any")
  | .Hole _ _ => pure (.var md "_hole", .TCore "Any")
  | _ => failure

partial def checkValue (expr : StmtExprMd) (expected : HighType) : ElabM FGLValue := do
  let (val, actual) ← synthValue expr
  pure (applySubsume val actual (eraseType expected))

-- synthExpr: synthesize an expression as value OR producer (defunctionalized)
-- Grade lookup is a pure HashMap read from the environment. No body evaluation.
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

-- checkArgsK: like checkArgs but with continuation — lifts effectful args via binding.
-- Uses synthExpr (defunctionalized) to determine if an arg is a value or producer.
partial def checkArgsK (args : List StmtExprMd) (params : List (String × HighType))
    (grade : Grade) (cont : List FGLValue → ElabM FGLProducer) : ElabM FGLProducer := do
  let paramTypes := params.map (·.2)
  let rec go : List StmtExprMd → List HighType → List FGLValue → ElabM FGLProducer
    | [], _, acc => cont acc.reverse
    | arg :: rest, [], acc => do
      let result ← synthExpr arg
      match result with
      | .value val _ => go rest [] (val :: acc)
      | .call callee checkedArgs retTy callGrade =>
        if !Grade.leq callGrade grade then failure
        else if callGrade == .err then
          mkErrorCall arg.md callee checkedArgs retTy fun rv => go rest [] (rv :: acc)
        else if callGrade == .heap then
          mkHeapCall arg.md callee checkedArgs retTy fun rv => go rest [] (rv :: acc)
        else if callGrade == .heapErr then
          mkHeapErrorCall arg.md callee checkedArgs retTy fun rv => go rest [] (rv :: acc)
        else go rest [] (FGLValue.staticCall arg.md callee checkedArgs :: acc)
    | arg :: rest, pty :: ptysRest, acc => do
      let result ← synthExpr arg
      match result with
      | .value val ty =>
        let coerced := applySubsume val ty (eraseType pty)
        go rest ptysRest (coerced :: acc)
      | .call callee checkedArgs retTy callGrade =>
        if !Grade.leq callGrade grade then failure
        else if callGrade == .err then
          mkErrorCall arg.md callee checkedArgs retTy fun rv =>
            go rest ptysRest (applySubsume rv (eraseType retTy) (eraseType pty) :: acc)
        else if callGrade == .heap then
          mkHeapCall arg.md callee checkedArgs retTy fun rv =>
            go rest ptysRest (applySubsume rv (eraseType retTy) (eraseType pty) :: acc)
        else if callGrade == .heapErr then
          mkHeapErrorCall arg.md callee checkedArgs retTy fun rv =>
            go rest ptysRest (applySubsume rv (eraseType retTy) (eraseType pty) :: acc)
        else do
          let val := FGLValue.staticCall arg.md callee checkedArgs
          go rest ptysRest (applySubsume val (eraseType retTy) (eraseType pty) :: acc)
  go args paramTypes []

-- checkProducer: the main recursive function.
-- `rest` is the remaining statements after this one (the continuation).
-- `grade` is the ambient grade (from the enclosing check context).
-- The function produces the FGL for `stmt; rest` nested together.
partial def checkProducer (stmt : StmtExprMd) (rest : List StmtExprMd) (grade : Grade) : ElabM FGLProducer := do
  let md := stmt.md
  match stmt.val with

  -- CHECK RULE: if V then M else N ⇐ A & e
  -- Both branches elaborate standalone. Rest goes in `after` (elaborated once).
  | .IfThenElse cond thn els =>
    let cc ← checkValue cond .TBool
    let tp ← checkProducer thn [] grade
    let ep ← match els with
      | some e => checkProducer e [] grade
      | none => pure .unit
    let after ← elabRest rest grade
    pure (.ifThenElse md cc tp ep after)

  -- SYNTH RULE: while V do M ⇒ TVoid & e
  | .While cond _invs _dec body =>
    let cc ← checkValue cond .TBool
    let bp ← checkProducer body [] grade
    let after ← elabRest rest grade
    pure (.whileLoop md cc bp after)

  -- CHECK RULE: return V ⇐ A & e
  | .Return valueOpt =>
    match valueOpt with
    | some v => let cv ← checkValue v (.TCore "Any"); pure (.returnValue md cv)
    | none => pure (.returnValue md (.fromNone md))

  -- SYNTH RULE: exit label ⇒ TVoid & 1
  | .Exit target => pure (.exit md target)

  -- CHECK RULE: var x:T := V; body ⇐ A & e
  | .LocalVariable nameId typeMd initOpt =>
    let ci ← match initOpt with
      | some ⟨.Hole false _, _⟩ => pure none
      | some ⟨.Hole true _, _⟩ => do let hv ← freshVar "hole"; pure (some (.staticCall md hv []))
      | some i => do let v ← checkValue i typeMd.val; pure (some v)
      | none => pure none
    mkVarDecl md nameId.text (eraseType typeMd.val) ci fun _ => elabRest rest grade

  -- SYNTH RULE: assert V ⇒ TVoid & 1
  | .Assert cond =>
    let cc ← checkValue cond .TBool
    let after ← elabRest rest grade
    pure (.assert md cc after)

  -- SYNTH RULE: assume V ⇒ TVoid & 1
  | .Assume cond =>
    let cc ← checkValue cond .TBool
    let after ← elabRest rest grade
    pure (.assume md cc after)

  -- SYNTH RULE: x := V ⇒ TVoid & 1
  | .Assign targets value => match targets with
    | [target] => elabAssign md target value rest grade
    | _ => elabRest rest grade

  -- SYNTH RULE: f(args) ⇒ B & d (effectful call, d > 1)
  | .StaticCall callee args => elabCall md callee args rest grade

  -- CHECK RULE: Block = sequence of statements
  -- Labeled blocks: Exit jumps to end of block, then rest continues.
  -- Thread `rest` OUTSIDE the block (not inside where Exit would skip it).
  | .Block stmts label =>
    match label with
    | some l =>
      let blockProd ← elabRest stmts grade
      let after ← elabRest rest grade
      pure (.labeledBlock md l blockProd after)
    | none => elabRest (stmts ++ rest) grade

  -- SYNTH RULE: new C ⇒ Composite & heap
  | .New classId =>
    guard (Grade.leq .heap grade)
    match (← get).heapVar with
    | some hv =>
      let ref := FGLValue.staticCall md "Heap..nextReference!" [.var md hv]
      let newHeap := FGLValue.staticCall md "increment" [.var md hv]
      let obj := FGLValue.staticCall md "MkComposite" [ref, .staticCall md (classId.text ++ "_TypeTag") []]
      let freshH ← freshVar "heap"
      modify fun s => { s with heapVar := some freshH }
      extendEnv freshH .THeap do
        let after ← elabRest rest grade
        pure (.varDecl md freshH (.TCore "Heap") (some newHeap) (.returnValue md obj))
    | none => failure

  | .Hole deterministic _ =>
    if deterministic then do
      let hv ← freshVar "hole"
      let after ← elabRest rest grade
      pure (.returnValue md (.staticCall md hv []))
    else
      mkVarDecl md "_havoc" (.TCore "Any") none fun _ => elabRest rest grade

  | _ => elabRest rest grade

-- elabRest: elaborate remaining statements (the continuation of the to-rule)
partial def elabRest (stmts : List StmtExprMd) (grade : Grade) : ElabM FGLProducer := do
  match stmts with
  | [] => pure .unit
  | stmt :: rest => checkProducer stmt rest grade

-- elabCall: StaticCall with grade lookup + checkArgsK (ANF-lifts effectful args)
partial def elabCall (md : Md) (callee : Identifier) (args : List StmtExprMd) (rest : List StmtExprMd) (grade : Grade) : ElabM FGLProducer := do
  let sig ← lookupFuncSig callee.text
  let params := match sig with | some s => s.params | none => []
  let retTy := match sig with | some s => s.returnType | none => .TCore "Any"
  let callGrade := (← read).procGrades[callee.text]?.getD .pure
  guard (Grade.leq callGrade grade)
  checkArgsK args params grade fun checkedArgs => do
    match callGrade with
    | .pure => elabRest rest grade
    | .err => mkErrorCall md callee.text checkedArgs retTy fun _rv => elabRest rest grade
    | .heap => mkHeapCall md callee.text checkedArgs retTy fun _rv => elabRest rest grade
    | .heapErr => mkHeapErrorCall md callee.text checkedArgs retTy fun _rv => elabRest rest grade

-- elabAssign: assignment with multiple sub-cases
partial def elabAssign (md : Md) (target value : StmtExprMd) (rest : List StmtExprMd) (grade : Grade) : ElabM FGLProducer := do
  match target.val with
  -- Field write: Assign [FieldSelect obj f] v → updateField
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
        let after ← elabRest rest grade
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
    | .IfThenElse cond thn els =>
      let assignThn : StmtExprMd := ⟨.Assign [target] thn, value.md⟩
      let assignEls : StmtExprMd := match els with
        | some e => ⟨.Assign [target] e, value.md⟩
        | none => ⟨.Block [] none, value.md⟩
      let desugared : StmtExprMd := ⟨.IfThenElse cond assignThn (some assignEls), value.md⟩
      checkProducer desugared rest grade
    | .Hole false _ =>
      if needsDecl then
        let name := match target.val with | .Identifier id => id.text | _ => "_havoc"
        mkVarDecl md name (eraseType targetTy) none fun _ => elabRest rest grade
      else
        mkVarDecl md "_havoc" (eraseType targetTy) none fun hv => do
          let after ← elabRest rest grade; pure (.assign md tv hv after)
    | .Hole true _ =>
      let hv ← freshVar "hole"
      if needsDecl then
        let name := match target.val with | .Identifier id => id.text | _ => "_x"
        mkVarDecl md name (eraseType targetTy) (some (.staticCall md hv [])) fun _ => elabRest rest grade
      else do
        let after ← elabRest rest grade; pure (.assign md tv (.staticCall md hv []) after)
    | .New classId =>
      guard (Grade.leq .heap grade)
      match (← get).heapVar with
      | some hv =>
        let ref := FGLValue.staticCall md "Heap..nextReference!" [.var md hv]
        let newHeap := FGLValue.staticCall md "increment" [.var md hv]
        let obj := FGLValue.staticCall md "MkComposite" [ref, .staticCall md (classId.text ++ "_TypeTag") []]
        let freshH ← freshVar "heap"
        modify fun s => { s with heapVar := some freshH }
        extendEnv freshH .THeap do
          let coercedObj := applySubsume obj (.TCore "Composite") (eraseType targetTy)
          if needsDecl then
            let name := match target.val with | .Identifier id => id.text | _ => "_x"
            let cont ← extendEnv name (.UserDefined (Identifier.mk classId.text none)) (elabRest rest grade)
            pure (.varDecl md freshH (.TCore "Heap") (some newHeap) (.varDecl md name (eraseType targetTy) (some coercedObj) cont))
          else do
            let after ← elabRest rest grade
            pure (.varDecl md freshH (.TCore "Heap") (some newHeap) (.assign md tv coercedObj after))
      | none => failure
    | .StaticCall callee args =>
      let sig ← lookupFuncSig callee.text
      let retHty := match sig with | some s => s.returnType | none => .TCore "Any"
      let params := match sig with | some s => s.params | none => []
      let callGrade := (← read).procGrades[callee.text]?.getD .pure
      guard (Grade.leq callGrade grade)
      let assignOrDecl (val : FGLValue) : ElabM FGLProducer := do
        if needsDecl then
          let name := match target.val with | .Identifier id => id.text | _ => "_x"
          mkVarDecl md name (eraseType targetTy) (some val) fun _ => elabRest rest grade
        else do let after ← elabRest rest grade; pure (.assign md tv val after)
      let doWithArgs (checkedArgs : List FGLValue) : ElabM FGLProducer := do
        match callGrade with
        | .pure =>
          let cv := FGLValue.staticCall md callee.text checkedArgs
          let coerced := applySubsume cv (eraseType retHty) (eraseType targetTy)
          assignOrDecl coerced
        | .err =>
          mkErrorCall md callee.text checkedArgs retHty fun rv => do
            let coerced := applySubsume rv (eraseType retHty) (eraseType targetTy)
            assignOrDecl coerced
        | .heap =>
          mkHeapCall md callee.text checkedArgs retHty fun rv => do
            let coerced := applySubsume rv (eraseType retHty) (eraseType targetTy)
            assignOrDecl coerced
        | .heapErr =>
          mkHeapErrorCall md callee.text checkedArgs retHty fun rv => do
            let coerced := applySubsume rv (eraseType retHty) (eraseType targetTy)
            assignOrDecl coerced
      checkArgsK args params grade doWithArgs
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
          mkVarDecl md name (eraseType targetTy) (some coerced) fun _ => elabRest rest grade
        else do let after ← elabRest rest grade; pure (.assign md tv coerced after)
      | none =>
        let fv := FGLValue.fieldAccess md ov field.text
        let after ← elabRest rest grade
        pure (.assign md tv fv after)
    | .Block stmts _ =>
      let assignLast : StmtExprMd := match stmts.reverse with
        | last :: initRev =>
          let init := initRev.reverse
          ⟨.Block (init ++ [⟨.Assign [target] last, md⟩]) none, value.md⟩
        | [] => ⟨.Block [] none, value.md⟩
      checkProducer assignLast rest grade
    | _ =>
      let cv ← checkValue value targetTy
      if needsDecl then
        let name := match target.val with | .Identifier id => id.text | _ => "_x"
        mkVarDecl md name (eraseType targetTy) (some cv) fun _ => elabRest rest grade
      else do
        let after ← elabRest rest grade
        pure (.assign md tv cv after)

end

-- tryGrades: try checkProducer at each grade, return smallest that succeeds.
-- Standalone (not in mutual block). Used by discoverGrades fixpoint.
partial def tryGrades (callee : String) (env : ElabEnv) (body : StmtExprMd)
    (grades : List Grade) : Option Grade :=
  match grades with
  | [] => some .heapErr
  | g :: rest =>
    let st : ElabState := {
      freshCounter := 0
      heapVar := if g == .heap || g == .heapErr then some "$heap" else none }
    let trialEnv := { env with procGrades := env.procGrades.insert callee g }
    match (checkProducer body [] g).run trialEnv |>.run st with
    | some _ => some g
    | none => tryGrades callee env body rest

-- Projection

mutual
partial def projectValue : FGLValue → StmtExprMd
  | .litInt md n => mkLaurel md (.LiteralInt n)
  | .litBool md b => mkLaurel md (.LiteralBool b)
  | .litString md s => mkLaurel md (.LiteralString s)
  | .var md "_hole" => mkLaurel md (.Hole)
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
  | .returnValue md v => [projectValue v]
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

-- fullElaborate: entry point

def fullElaborate (typeEnv : TypeEnv) (program : Laurel.Program) (runtime : Laurel.Program := default) (initialGrades : Std.HashMap String Grade := {}) : Except String (Laurel.Program × List String) := do
  let baseEnv : ElabEnv := { typeEnv := typeEnv, program := program, runtime := runtime }

  -- PASS 1: SYNTH — coinductive fixpoint iteration over call graph
  -- Iterate until grades stabilize. Convergence guaranteed (finite lattice, monotone).
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
          (fun e p => { e with names := e.names.insert p.name.text (.variable p.type.val) }) typeEnv
        let procEnv : ElabEnv := { baseEnv with typeEnv := extEnv, procGrades := knownGrades }
        match tryGrades proc.name.text procEnv bodyExpr [.pure, .err, .heap, .heapErr] with
        | some g =>
          let g := if proc.outputs.length > 1 then Grade.join g .err else g
          if knownGrades[proc.name.text]? != some g then
            knownGrades := knownGrades.insert proc.name.text g
            changed := true
        | none => pure ()
      | none => pure ()

  -- PASS 2: CHECK — elaborate each proc with all grades known
  let mut procs : List Laurel.Procedure := []
  let mut allBoxConstructors : List (String × String × HighType) := []
  let mut elabFailures : List String := []
  for proc in program.staticProcedures do
    match proc.body with
    | .Transparent bodyExpr =>
      let extEnv := (proc.inputs ++ proc.outputs).foldl
        (fun e p => { e with names := e.names.insert p.name.text (.variable p.type.val) }) typeEnv
      let procEnv : ElabEnv := { baseEnv with typeEnv := extEnv, procGrades := knownGrades }
      let g := knownGrades[proc.name.text]?.getD .pure
      let st : ElabState := {
        freshCounter := 0
        heapVar := if g == .heap || g == .heapErr then some "$heap" else none }
      match (checkProducer bodyExpr [] g).run procEnv |>.run st with
      | some (fgl, st') =>
        allBoxConstructors := allBoxConstructors ++ st'.usedBoxConstructors.filter
          (fun (c, _, _) => !allBoxConstructors.any (fun (c2, _, _) => c == c2))
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
        | .pure =>
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
  let result := if hasHeap then
    let heapTypesFiltered := heapConstants.types.filter fun td => match td with
      | .Datatype dt => dt.name.text != "Composite" && dt.name.text != "NotSupportedYet"
      | _ => true
    { program with
      staticProcedures := coreDefinitionsForLaurel.staticProcedures ++ heapConstants.staticProcedures ++ procs
      types := [fieldDatatype, boxDatatype, typeTagDatatype, compositeType] ++ heapTypesFiltered ++ coreDefinitionsForLaurel.types ++ program.types }
  else
    { program with
      staticProcedures := coreDefinitionsForLaurel.staticProcedures ++ procs
      types := [typeTagDatatype, compositeType] ++ coreDefinitionsForLaurel.types ++ program.types }
  pure (result, elabFailures)

end
end Strata.FineGrainLaurel
