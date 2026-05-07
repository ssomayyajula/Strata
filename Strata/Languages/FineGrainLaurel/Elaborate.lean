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
  | .UserDefined _ => .TCore "Composite" | .THeap => .TCore "Heap"
  | .TReal => .TCore "real" | .TTypedField _ => .TCore "Field"
  | .TSet _ | .TMap _ _ | .Applied _ _ | .Intersection _ | .Unknown => .TCore "Any"
  | .Pure _ => .TCore "Composite"

def liftType : LowType → HighType
  | .TInt => .TInt | .TBool => .TBool | .TString => .TString
  | .TFloat64 => .TFloat64 | .TVoid => .TVoid | .TCore n => .TCore n

-- FGL Terms

inductive FGLValue where
  | litInt (n : Int) | litBool (b : Bool) | litString (s : String) | var (name : String)
  | fromInt (inner : FGLValue) | fromStr (inner : FGLValue)
  | fromBool (inner : FGLValue) | fromFloat (inner : FGLValue)
  | fromComposite (inner : FGLValue) | fromListAny (inner : FGLValue)
  | fromDictStrAny (inner : FGLValue) | fromNone
  | fieldAccess (obj : FGLValue) (field : String)
  | staticCall (name : String) (args : List FGLValue)
  deriving Inhabited

inductive FGLProducer where
  | returnValue (v : FGLValue)
  | assign (target : FGLValue) (val : FGLValue) (body : FGLProducer)
  | varDecl (name : String) (ty : LowType) (init : Option FGLValue) (body : FGLProducer)
  | ifThenElse (cond : FGLValue) (thn : FGLProducer) (els : FGLProducer)
  | whileLoop (cond : FGLValue) (body : FGLProducer) (after : FGLProducer)
  | assert (cond : FGLValue) (body : FGLProducer)
  | assume (cond : FGLValue) (body : FGLProducer)
  | effectfulCall (callee : String) (args : List FGLValue)
      (outputs : List (String × LowType)) (body : FGLProducer)
  | exit (label : String)
  | labeledBlock (label : String) (body : FGLProducer)
  | unit
  deriving Inhabited

-- Monad

structure ElabEnv where
  typeEnv : TypeEnv
  program : Laurel.Program
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
  | .TCore name => s!"Box..{name}"
  | _ => "BoxComposite"

def boxDestructorName (ty : HighType) : String :=
  match ty with
  | .TInt => "Box..intVal!" | .TBool => "Box..boolVal!" | .TFloat64 => "Box..float64Val!"
  | .TReal => "Box..realVal!" | .TString => "Box..stringVal!"
  | .UserDefined _ => "Box..compositeVal!"
  | .TCore name => s!"Box..{name}Val!"
  | _ => "Box..compositeVal!"

def boxFieldName (ty : HighType) : String :=
  match ty with
  | .TInt => "intVal" | .TBool => "boolVal" | .TFloat64 => "float64Val"
  | .TReal => "realVal" | .TString => "stringVal"
  | .UserDefined _ => "compositeVal"
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

-- Env helpers

def lookupEnv (name : String) : ElabM (Option NameInfo) := do pure (← read).typeEnv.names[name]?
def extendEnv (name : String) (ty : HighType) (action : ElabM α) : ElabM α :=
  withReader (fun env => { env with typeEnv := { env.typeEnv with names := env.typeEnv.names.insert name (.variable ty) } }) action
def lookupFuncSig (name : String) : ElabM (Option FuncSig) := do
  match (← read).typeEnv.names[name]? with | some (.function sig) => pure (some sig) | _ => pure none
def lookupProcBody (name : String) : ElabM (Option StmtExprMd) := do
  match (← read).program.staticProcedures.find? (fun p => p.name.text == name) with
  | some proc => match proc.body with
    | .Transparent b => pure (some b)
    | .Opaque _ (some impl) _ => pure (some impl)
    | _ => pure none
  | none => pure none

def lookupFieldType (className fieldName : String) : ElabM (Option HighType) := do
  match (← read).typeEnv.classFields[className]? with
  | some fields => pure (fields.find? (fun (n, _) => n == fieldName) |>.map (·.2))
  | none => pure none

def resolveFieldOwner (fieldName : String) : ElabM (Option String) := do
  for (className, fields) in (← read).typeEnv.classFields.toList do
    if fields.any (fun (n, _) => n == fieldName) then return some className
  pure none

-- HOAS Smart Constructors

def mkEffectfulCall (callee : String) (args : List FGLValue)
    (outputSpecs : List (String × HighType))
    (body : List FGLValue → ElabM FGLProducer) : ElabM FGLProducer := do
  let mut names : List String := []
  let mut lowOutputs : List (String × LowType) := []
  for (pfx, ty) in outputSpecs do
    let n ← freshVar pfx
    names := names ++ [n]
    lowOutputs := lowOutputs ++ [(n, eraseType ty)]
  let vars := names.map FGLValue.var
  let cont ← names.zip (outputSpecs.map (·.2)) |>.foldr
    (fun (n, ty) acc => extendEnv n ty acc) (body vars)
  pure (.effectfulCall callee args lowOutputs cont)

def mkVarDecl (name : String) (ty : LowType) (init : Option FGLValue)
    (body : FGLValue → ElabM FGLProducer) : ElabM FGLProducer := do
  let cont ← extendEnv name (liftType ty) (body (.var name))
  pure (.varDecl name ty init cont)

def mkErrorCall (callee : String) (args : List FGLValue) (resultTy : HighType)
    (body : FGLValue → ElabM FGLProducer) : ElabM FGLProducer :=
  mkEffectfulCall callee args [("result", resultTy), ("err", .TCore "Error")]
    fun outs => body outs[0]!

def mkHeapCall (callee : String) (args : List FGLValue) (resultTy : HighType)
    (body : FGLValue → ElabM FGLProducer) : ElabM FGLProducer := do
  let hv := (← get).heapVar
  let heapArg := match hv with | some h => FGLValue.var h | none => FGLValue.var "$heap"
  mkEffectfulCall callee (heapArg :: args) [("heap", .THeap), ("result", resultTy)]
    fun outs => do
      match outs[0]! with | .var n => modify fun s => { s with heapVar := some n } | _ => pure ()
      body outs[1]!

def mkHeapErrorCall (callee : String) (args : List FGLValue) (resultTy : HighType)
    (body : FGLValue → ElabM FGLProducer) : ElabM FGLProducer := do
  let hv := (← get).heapVar
  let heapArg := match hv with | some h => FGLValue.var h | none => FGLValue.var "$heap"
  mkEffectfulCall callee (heapArg :: args) [("heap", .THeap), ("result", resultTy), ("err", .TCore "Error")]
    fun outs => do
      match outs[0]! with | .var n => modify fun s => { s with heapVar := some n } | _ => pure ()
      body outs[1]!

-- Subsumption

inductive CoercionResult where | refl | coerce (w : FGLValue → FGLValue) | unrelated
  deriving Inhabited

def subsume (actual expected : LowType) : CoercionResult :=
  if actual == expected then .refl else match actual, expected with
  | .TInt, .TCore "Any" => .coerce .fromInt
  | .TBool, .TCore "Any" => .coerce .fromBool
  | .TString, .TCore "Any" => .coerce .fromStr
  | .TFloat64, .TCore "Any" => .coerce .fromFloat
  | .TCore "Composite", .TCore "Any" => .coerce .fromComposite
  | .TCore "ListAny", .TCore "Any" => .coerce .fromListAny
  | .TCore "DictStrAny", .TCore "Any" => .coerce .fromDictStrAny
  | .TVoid, .TCore "Any" => .coerce (fun _ => .fromNone)
  | .TCore "Any", .TBool => .coerce (fun v => .staticCall "Any_to_bool" [v])
  | .TCore "Any", .TInt => .coerce (fun v => .staticCall "Any..as_int!" [v])
  | .TCore "Any", .TString => .coerce (fun v => .staticCall "Any..as_string!" [v])
  | .TCore "Any", .TFloat64 => .coerce (fun v => .staticCall "Any..as_float!" [v])
  | .TCore "Any", .TCore "Composite" => .coerce (fun v => .staticCall "Any..as_Composite!" [v])
  | _, _ => .unrelated

def applySubsume (val : FGLValue) (actual expected : LowType) : FGLValue :=
  match subsume actual expected with | .refl => val | .coerce c => c val | .unrelated => val

-- Elaboration
-- checkProducer is THE entry point. It takes remaining statements as continuation.
-- Each FGL node threads the rest into its body field.

mutual

partial def synthValue (expr : StmtExprMd) : ElabM (FGLValue × LowType) := do
  match expr.val with
  | .LiteralInt n => pure (.litInt n, .TInt)
  | .LiteralBool b => pure (.litBool b, .TBool)
  | .LiteralString s => pure (.litString s, .TString)
  | .Identifier id =>
    match (← lookupEnv id.text) with
    | some (.variable ty) => pure (.var id.text, eraseType ty)
    | some (.function sig) => pure (.var id.text, eraseType sig.returnType)
    | _ => pure (.var id.text, .TCore "Any")
  | .FieldSelect obj field =>
    let (ov, objTy) ← synthValue obj
    match (← get).heapVar with
    | some hv =>
      let owner ← resolveFieldOwner field.text
      let qualifiedName := match owner with | some cn => cn ++ "." ++ field.text | none => field.text
      let fieldTy ← match owner with
        | some cn => do let ft ← lookupFieldType cn field.text; pure (ft.getD (.TCore "Any"))
        | none => pure (.TCore "Any")
      recordBoxUse fieldTy
      let compositeObj := applySubsume ov objTy (.TCore "Composite")
      let read := FGLValue.staticCall "readField" [.var hv, compositeObj, .staticCall qualifiedName []]
      pure (.staticCall (boxDestructorName fieldTy) [read], eraseType fieldTy)
    | none => failure
  | .StaticCall callee args =>
    let sig ← lookupFuncSig callee.text
    match sig with
    | some s =>
      let g ← discoverGrade callee.text
      guard (g == .pure)
      let checkedArgs ← checkArgs args s.params
      pure (.staticCall callee.text checkedArgs, eraseType s.returnType)
    | none =>
      let checkedArgs ← args.mapM fun arg => checkValue arg (.TCore "Any")
      pure (.staticCall callee.text checkedArgs, .TCore "Any")
  | .Hole _ _ => pure (.var "_hole", .TCore "Any")
  | _ => failure

partial def checkValue (expr : StmtExprMd) (expected : HighType) : ElabM FGLValue := do
  let (val, actual) ← synthValue expr
  pure (applySubsume val actual (eraseType expected))

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

-- checkArgsK: like checkArgs but with continuation — lifts effectful args via binding
-- When an arg is an effectful StaticCall (grade > 1), binds it and passes the bound value.
partial def checkArgsK (args : List StmtExprMd) (params : List (String × HighType))
    (grade : Grade) (cont : List FGLValue → ElabM FGLProducer) : ElabM FGLProducer := do
  let paramTypes := params.map (·.2)
  let rec go : List StmtExprMd → List HighType → List FGLValue → ElabM FGLProducer
    | [], _, acc => cont acc.reverse
    | arg :: rest, ptys, acc => do
      let pty := match ptys with | p :: _ => p | [] => .TCore "Any"
      let ptysRest := match ptys with | _ :: ps => ps | [] => []
      match arg.val with
      | .StaticCall callee innerArgs =>
        let innerSig ← lookupFuncSig callee.text
        match innerSig with
        | some s =>
          let innerGrade ← discoverGrade callee.text
          let innerChecked ← checkArgs innerArgs s.params
          match innerGrade with
          | .pure =>
            let val := FGLValue.staticCall callee.text innerChecked
            let coerced := applySubsume val (eraseType s.returnType) (eraseType pty)
            go rest ptysRest (coerced :: acc)
          | .err => do
            guard (Grade.leq .err grade)
            mkErrorCall callee.text innerChecked s.returnType fun rv =>
              go rest ptysRest (applySubsume rv (eraseType s.returnType) (eraseType pty) :: acc)
          | .heap => do
            guard (Grade.leq .heap grade)
            mkHeapCall callee.text innerChecked s.returnType fun rv =>
              go rest ptysRest (applySubsume rv (eraseType s.returnType) (eraseType pty) :: acc)
          | .heapErr => do
            guard (Grade.leq .heapErr grade)
            mkHeapErrorCall callee.text innerChecked s.returnType fun rv =>
              go rest ptysRest (applySubsume rv (eraseType s.returnType) (eraseType pty) :: acc)
        | none => do
          -- No sig: runtime function, always pure
          let innerChecked ← innerArgs.mapM fun a => checkValue a (.TCore "Any")
          let val := FGLValue.staticCall callee.text innerChecked
          let coerced := applySubsume val (.TCore "Any") (eraseType pty)
          go rest ptysRest (coerced :: acc)
      | _ => do
        -- Non-StaticCall arg: regular value check
        let v ← checkValue arg pty
        go rest ptysRest (v :: acc)
  go args paramTypes []

-- checkProducer: the main recursive function.
-- `rest` is the remaining statements after this one (the continuation).
-- `grade` is the ambient grade (from the enclosing check context).
-- The function produces the FGL for `stmt; rest` nested together.
partial def checkProducer (stmt : StmtExprMd) (rest : List StmtExprMd) (grade : Grade) : ElabM FGLProducer := do
  match stmt.val with

  -- CHECK RULE: if V then M else N ⇐ A & e
  -- Both branches get the rest threaded in (duplicated).
  | .IfThenElse cond thn els =>
    let cc ← checkValue cond .TBool
    let tp ← checkProducer thn rest grade
    let ep ← match els with
      | some e => checkProducer e rest grade
      | none => elabRest rest grade
    pure (.ifThenElse cc tp ep)

  -- SYNTH RULE: while V do M ⇒ TVoid & e (body checked at same grade)
  | .While cond _invs _dec body =>
    let cc ← checkValue cond .TBool
    let bp ← checkProducer body [] grade
    let after ← elabRest rest grade
    pure (.whileLoop cc bp after)

  -- CHECK RULE: return V ⇐ A & e
  | .Return valueOpt =>
    match valueOpt with
    | some v => let cv ← checkValue v (.TCore "Any"); pure (.returnValue cv)
    | none => pure (.returnValue .fromNone)

  -- SYNTH RULE: exit label ⇒ TVoid & 1
  | .Exit target => pure (.exit target)

  -- CHECK RULE: var x:T := V; body ⇐ A & e
  | .LocalVariable nameId typeMd initOpt =>
    let ci ← match initOpt with
      | some ⟨.Hole false _, _⟩ => pure none
      | some ⟨.Hole true _, _⟩ => do let hv ← freshVar "hole"; pure (some (.staticCall hv []))
      | some i => do let v ← checkValue i typeMd.val; pure (some v)
      | none => pure none
    mkVarDecl nameId.text (eraseType typeMd.val) ci fun _ => elabRest rest grade

  -- SYNTH RULE: assert V ⇒ TVoid & 1
  | .Assert cond =>
    let cc ← checkValue cond .TBool
    let after ← elabRest rest grade
    pure (.assert cc after)

  -- SYNTH RULE: assume V ⇒ TVoid & 1
  | .Assume cond =>
    let cc ← checkValue cond .TBool
    let after ← elabRest rest grade
    pure (.assume cc after)

  -- SYNTH RULE: x := V ⇒ TVoid & 1
  | .Assign targets value => match targets with
    | [target] => elabAssign target value rest grade
    | _ => elabRest rest grade

  -- SYNTH RULE: f(args) ⇒ B & d (effectful call, d > 1)
  | .StaticCall callee args => elabCall callee args rest grade

  -- CHECK RULE: Block = sequence of statements
  | .Block stmts label =>
    let prod ← elabRest (stmts ++ rest) grade
    pure (match label with | some l => .labeledBlock l prod | none => prod)

  -- SYNTH RULE: new C ⇒ Composite & heap
  | .New classId =>
    guard (Grade.leq .heap grade)
    match (← get).heapVar with
    | some hv =>
      let ref := FGLValue.staticCall "Heap..nextReference!" [.var hv]
      let newHeap := FGLValue.staticCall "increment" [.var hv]
      let obj := FGLValue.staticCall "MkComposite" [ref, .staticCall (classId.text ++ "_TypeTag") []]
      let freshH ← freshVar "heap"
      modify fun s => { s with heapVar := some freshH }
      extendEnv freshH .THeap do
        let after ← elabRest rest grade
        pure (.varDecl freshH (.TCore "Heap") (some newHeap) (.returnValue obj))
    | none => failure

  | .Hole deterministic _ =>
    if deterministic then do
      let hv ← freshVar "hole"
      let after ← elabRest rest grade
      pure (.returnValue (.staticCall hv []))
    else
      mkVarDecl "_havoc" (.TCore "Any") none fun _ => elabRest rest grade

  | _ => elabRest rest grade

-- elabRest: elaborate remaining statements (the continuation of the to-rule)
partial def elabRest (stmts : List StmtExprMd) (grade : Grade) : ElabM FGLProducer := do
  match stmts with
  | [] => pure .unit
  | stmt :: rest => checkProducer stmt rest grade

-- elabCall: StaticCall with grade discovery + smart constructor dispatch
partial def elabCall (callee : Identifier) (args : List StmtExprMd) (rest : List StmtExprMd) (grade : Grade) : ElabM FGLProducer := do
  let sig ← lookupFuncSig callee.text
  let (checkedArgs, retTy) ← match sig with
    | some s => do let ca ← checkArgs args s.params; pure (ca, s.returnType)
    | none => do let ca ← args.mapM fun a => checkValue a (.TCore "Any"); pure (ca, .TCore "Any")
  let callGrade ← discoverGrade callee.text
  guard (Grade.leq callGrade grade)
  match callGrade with
  | .pure =>
    -- Pure call is a value — just continue
    elabRest rest grade
  | .err =>
    mkErrorCall callee.text checkedArgs retTy fun _rv => elabRest rest grade
  | .heap =>
    mkHeapCall callee.text checkedArgs retTy fun _rv => elabRest rest grade
  | .heapErr =>
    mkHeapErrorCall callee.text checkedArgs retTy fun _rv => elabRest rest grade

-- elabAssign: assignment with multiple sub-cases
partial def elabAssign (target value : StmtExprMd) (rest : List StmtExprMd) (grade : Grade) : ElabM FGLProducer := do
  match target.val with
  -- Field write: Assign [FieldSelect obj f] v → updateField
  | .FieldSelect obj field =>
    guard (Grade.leq .heap grade)
    let (ov, objTy) ← synthValue obj
    match (← get).heapVar with
    | some hv =>
      let owner ← resolveFieldOwner field.text
      let qualifiedName := match owner with | some cn => cn ++ "." ++ field.text | none => field.text
      let fieldTy ← match owner with
        | some cn => do let ft ← lookupFieldType cn field.text; pure (ft.getD (.TCore "Any"))
        | none => pure (.TCore "Any")
      recordBoxUse fieldTy
      let cv ← checkValue value fieldTy
      let compositeObj := applySubsume ov objTy (.TCore "Composite")
      let boxed := FGLValue.staticCall (boxConstructorName fieldTy) [cv]
      let newHeap := FGLValue.staticCall "updateField" [.var hv, compositeObj, .staticCall qualifiedName [], boxed]
      let freshH ← freshVar "heap"
      modify fun s => { s with heapVar := some freshH }
      extendEnv freshH .THeap do
        let after ← elabRest rest grade
        pure (.varDecl freshH (.TCore "Heap") (some newHeap) after)
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
    | .Hole false _ =>
      if needsDecl then
        let name := match target.val with | .Identifier id => id.text | _ => "_havoc"
        mkVarDecl name (eraseType targetTy) none fun _ => elabRest rest grade
      else
        mkVarDecl "_havoc" (eraseType targetTy) none fun hv => do
          let after ← elabRest rest grade; pure (.assign tv hv after)
    | .Hole true _ =>
      let hv ← freshVar "hole"
      if needsDecl then
        let name := match target.val with | .Identifier id => id.text | _ => "_x"
        mkVarDecl name (eraseType targetTy) (some (.staticCall hv [])) fun _ => elabRest rest grade
      else do
        let after ← elabRest rest grade; pure (.assign tv (.staticCall hv []) after)
    | .New classId =>
      guard (Grade.leq .heap grade)
      match (← get).heapVar with
      | some hv =>
        let ref := FGLValue.staticCall "Heap..nextReference!" [.var hv]
        let newHeap := FGLValue.staticCall "increment" [.var hv]
        let obj := FGLValue.staticCall "MkComposite" [ref, .staticCall (classId.text ++ "_TypeTag") []]
        let freshH ← freshVar "heap"
        modify fun s => { s with heapVar := some freshH }
        extendEnv freshH .THeap do
          if needsDecl then
            let name := match target.val with | .Identifier id => id.text | _ => "_x"
            let cont ← extendEnv name (.UserDefined (Identifier.mk classId.text none)) (elabRest rest grade)
            pure (.varDecl freshH (.TCore "Heap") (some newHeap) (.varDecl name (.TCore "Composite") (some obj) cont))
          else do
            let after ← elabRest rest grade
            pure (.varDecl freshH (.TCore "Heap") (some newHeap) (.assign tv obj after))
      | none => failure
    | .StaticCall callee args =>
      let sig ← lookupFuncSig callee.text
      let retHty := match sig with | some s => s.returnType | none => .TCore "Any"
      let params := match sig with | some s => s.params | none => []
      let callGrade ← discoverGrade callee.text
      guard (Grade.leq callGrade grade)
      let assignOrDecl (val : FGLValue) : ElabM FGLProducer := do
        if needsDecl then
          let name := match target.val with | .Identifier id => id.text | _ => "_x"
          mkVarDecl name (eraseType targetTy) (some val) fun _ => elabRest rest grade
        else do let after ← elabRest rest grade; pure (.assign tv val after)
      let doWithArgs (checkedArgs : List FGLValue) : ElabM FGLProducer := do
        match callGrade with
        | .pure =>
          let cv := FGLValue.staticCall callee.text checkedArgs
          let coerced := applySubsume cv (eraseType retHty) (eraseType targetTy)
          assignOrDecl coerced
        | .err =>
          mkErrorCall callee.text checkedArgs retHty fun rv => do
            let coerced := applySubsume rv (eraseType retHty) (eraseType targetTy)
            assignOrDecl coerced
        | .heap =>
          mkHeapCall callee.text checkedArgs retHty fun rv => do
            let coerced := applySubsume rv (eraseType retHty) (eraseType targetTy)
            assignOrDecl coerced
        | .heapErr =>
          mkHeapErrorCall callee.text checkedArgs retHty fun rv => do
            let coerced := applySubsume rv (eraseType retHty) (eraseType targetTy)
            assignOrDecl coerced
      -- Try checkArgs. If it fails, check if any arg is effectful and use checkArgsK.
      let env ← read; let st ← get
      let trySimple := match sig with
        | some s => (checkArgs args s.params).run env |>.run st
        | none => (args.mapM fun a => checkValue a (.TCore "Any")).run env |>.run st
      match trySimple with
      | some (checkedArgs, st') => set st'; doWithArgs checkedArgs
      | none =>
        -- checkArgs failed. Check if any arg is a known effectful call.
        let hasEffectfulArg := args.any fun a => match a.val with
          | .StaticCall c _ => match env.procGrades[c.text]? with | some g => g != .pure | _ => false
          | _ => false
        if hasEffectfulArg then
          checkArgsK args params grade doWithArgs
        else failure
    | .FieldSelect obj field =>
      guard (Grade.leq .heap grade)
      let (ov, objTy) ← synthValue obj
      match (← get).heapVar with
      | some hv =>
        let owner ← resolveFieldOwner field.text
        let qualifiedName := match owner with | some cn => cn ++ "." ++ field.text | none => field.text
        let fieldTy ← match owner with
          | some cn => do let ft ← lookupFieldType cn field.text; pure (ft.getD (.TCore "Any"))
          | none => pure (.TCore "Any")
        recordBoxUse fieldTy
        let compositeObj := applySubsume ov objTy (.TCore "Composite")
        let read := FGLValue.staticCall "readField" [.var hv, compositeObj, .staticCall qualifiedName []]
        let unboxed := FGLValue.staticCall (boxDestructorName fieldTy) [read]
        let coerced := applySubsume unboxed (eraseType fieldTy) (eraseType targetTy)
        if needsDecl then
          let name := match target.val with | .Identifier id => id.text | _ => "_x"
          mkVarDecl name (eraseType targetTy) (some coerced) fun _ => elabRest rest grade
        else do let after ← elabRest rest grade; pure (.assign tv coerced after)
      | none =>
        let fv := FGLValue.fieldAccess ov field.text
        let after ← elabRest rest grade
        pure (.assign tv fv after)
    | _ =>
      let cv ← checkValue value targetTy
      if needsDecl then
        let name := match target.val with | .Identifier id => id.text | _ => "_x"
        mkVarDecl name (eraseType targetTy) (some cv) fun _ => elabRest rest grade
      else do
        let after ← elabRest rest grade
        pure (.assign tv cv after)

-- discoverGrade: typing rules as oracle
-- Reads procGrades from the reader (no state mutation). Uses `local` for coinduction.
partial def discoverGrade (callee : String) : ElabM Grade := do
  match (← read).procGrades[callee]? with
  | some g => pure g
  | none =>
    let body ← lookupProcBody callee
    match body with
    | some bodyExpr =>
      let sig ← lookupFuncSig callee
      let retTy := match sig with | some s => eraseType s.returnType | none => .TCore "Any"
      let env ← read
      let paramEnv := match sig with
        | some s => s.params.foldl (fun e (n, t) =>
            { e with typeEnv := { e.typeEnv with names := e.typeEnv.names.insert n (.variable t) } }) env
        | none => env
      tryGrades callee paramEnv bodyExpr retTy [.pure, .err, .heap, .heapErr]
    | none => pure .pure

partial def tryGrades (callee : String) (env : ElabEnv) (body : StmtExprMd) (retTy : LowType) (grades : List Grade) : ElabM Grade := do
  match grades with
  | [] => pure .heapErr
  | g :: rest =>
    let st ← get
    let trialSt : ElabState := { st with
      freshCounter := 0
      heapVar := if g == .heap || g == .heapErr then some "$heap" else none }
    -- Use local to add coinductive sentinel: callee assumed at grade g
    let trialEnv := { env with procGrades := env.procGrades.insert callee g }
    match (checkProducer body [] g).run trialEnv |>.run trialSt with
    | some _ => pure g
    | none => tryGrades callee env body retTy rest

end

-- Projection

mutual
partial def projectValue (md : Imperative.MetaData Core.Expression) : FGLValue → StmtExprMd
  | .litInt n => mkLaurel md (.LiteralInt n)
  | .litBool b => mkLaurel md (.LiteralBool b)
  | .litString s => mkLaurel md (.LiteralString s)
  | .var "_hole" => mkLaurel md (.Hole)
  | .var name => mkLaurel md (.Identifier (Identifier.mk name none))
  | .fromInt v => mkLaurel md (.StaticCall (Identifier.mk "from_int" none) [projectValue md v])
  | .fromStr v => mkLaurel md (.StaticCall (Identifier.mk "from_str" none) [projectValue md v])
  | .fromBool v => mkLaurel md (.StaticCall (Identifier.mk "from_bool" none) [projectValue md v])
  | .fromFloat v => mkLaurel md (.StaticCall (Identifier.mk "from_float" none) [projectValue md v])
  | .fromComposite v => mkLaurel md (.StaticCall (Identifier.mk "from_Composite" none) [projectValue md v])
  | .fromListAny v => mkLaurel md (.StaticCall (Identifier.mk "from_ListAny" none) [projectValue md v])
  | .fromDictStrAny v => mkLaurel md (.StaticCall (Identifier.mk "from_DictStrAny" none) [projectValue md v])
  | .fromNone => mkLaurel md (.StaticCall (Identifier.mk "from_None" none) [])
  | .fieldAccess obj f => mkLaurel md (.FieldSelect (projectValue md obj) (Identifier.mk f none))
  | .staticCall name args => mkLaurel md (.StaticCall (Identifier.mk name none) (args.map (projectValue md)))

partial def projectProducer (md : Imperative.MetaData Core.Expression) : FGLProducer → List StmtExprMd
  | .returnValue v => [projectValue md v]
  | .assign target val body => [mkLaurel md (.Assign [projectValue md target] (projectValue md val))] ++ projectProducer md body
  | .varDecl name ty init body => [mkLaurel md (.LocalVariable (Identifier.mk name none) (mkHighTypeMd md (liftType ty)) (init.map (projectValue md)))] ++ projectProducer md body
  | .ifThenElse cond thn els => [mkLaurel md (.IfThenElse (projectValue md cond) (mkLaurel md (.Block (projectProducer md thn) none)) (some (mkLaurel md (.Block (projectProducer md els) none))))]
  | .whileLoop cond body after => [mkLaurel md (.While (projectValue md cond) [] none (mkLaurel md (.Block (projectProducer md body) none)))] ++ projectProducer md after
  | .assert cond body => [mkLaurel md (.Assert (projectValue md cond))] ++ projectProducer md body
  | .assume cond body => [mkLaurel md (.Assume (projectValue md cond))] ++ projectProducer md body
  | .effectfulCall callee args outputs body =>
    let call := mkLaurel md (.StaticCall (Identifier.mk callee none) (args.map (projectValue md)))
    let decls := outputs.map fun (n, ty) => mkLaurel md (.LocalVariable (Identifier.mk n none) (mkHighTypeMd md (liftType ty)) (some (mkLaurel md (.Hole))))
    let targets := outputs.map fun (n, _) => mkLaurel md (.Identifier (Identifier.mk n none))
    decls ++ [mkLaurel md (.Assign targets call)] ++ projectProducer md body
  | .exit label => [mkLaurel md (.Exit label)]
  | .labeledBlock label body => [mkLaurel md (.Block (projectProducer md body) (some label))]
  | .unit => []
end

def projectBody (md : Imperative.MetaData Core.Expression) (prod : FGLProducer) : StmtExprMd :=
  mkLaurel md (.Block (projectProducer md prod) none)

-- fullElaborate: entry point

def fullElaborate (typeEnv : TypeEnv) (program : Laurel.Program) : Except String Laurel.Program := do
  let baseEnv : ElabEnv := { typeEnv := typeEnv, program := program }
  let mut procs : List Laurel.Procedure := []
  let mut knownGrades : Std.HashMap String Grade := {}
  let mut allBoxConstructors : List (String × String × HighType) := []
  for proc in program.staticProcedures do
    match proc.body with
    | .Transparent bodyExpr =>
      let extEnv := (proc.inputs ++ proc.outputs).foldl
        (fun e p => { e with names := e.names.insert p.name.text (.variable p.type.val) }) typeEnv
      let procEnv : ElabEnv := { baseEnv with typeEnv := extEnv, procGrades := knownGrades }
      -- Discover grade by trying checkProducer at each level
      let grade := [Grade.pure, Grade.err, Grade.heap, Grade.heapErr].findSome? fun g =>
        let st : ElabState := {
          freshCounter := 0
          heapVar := if g == .heap || g == .heapErr then some "$heap" else none }
        let trialEnv := { procEnv with procGrades := knownGrades.insert proc.name.text g }
        match (checkProducer bodyExpr [] g).run trialEnv |>.run st with
        | some _ => some g
        | none => none
      match grade with
      | some g =>
        let g := if proc.outputs.length > 1 then Grade.join g .err else g
        knownGrades := knownGrades.insert proc.name.text g
        let st : ElabState := {
          freshCounter := 0
          heapVar := if g == .heap || g == .heapErr then some "$heap" else none }
        let elabEnv := { procEnv with procGrades := knownGrades }
        match (checkProducer bodyExpr [] g).run elabEnv |>.run st with
        | some (fgl, st') =>
          allBoxConstructors := allBoxConstructors ++ st'.usedBoxConstructors.filter
            (fun (c, _, _) => !allBoxConstructors.any (fun (c2, _, _) => c == c2))
          let projected := projectBody bodyExpr.md fgl
          if g == .heap || g == .heapErr then
            let heapInParam : Laurel.Parameter := { name := Identifier.mk "$heap_in" none, type := mkHighTypeMd bodyExpr.md .THeap }
            let heapOutParam : Laurel.Parameter := { name := Identifier.mk "$heap" none, type := mkHighTypeMd bodyExpr.md .THeap }
            let heapInit := mkLaurel bodyExpr.md (.Assign [mkLaurel bodyExpr.md (.Identifier (Identifier.mk "$heap" none))] (mkLaurel bodyExpr.md (.Identifier (Identifier.mk "$heap_in" none))))
            let newBody := mkLaurel bodyExpr.md (.Block ([heapInit] ++ (projectProducer bodyExpr.md fgl)) none)
            procs := procs ++ [{ proc with
              inputs := [heapInParam] ++ proc.inputs
              outputs := [heapOutParam] ++ proc.outputs
              body := .Transparent newBody }]
          else
            procs := procs ++ [{ proc with body := .Transparent projected }]
        | none => procs := procs ++ [proc]
      | none => procs := procs ++ [proc]
    | .Opaque _ (some impl) _ =>
      -- Opaque with implementation: discover grade but don't rewrite body
      let extEnv := (proc.inputs ++ proc.outputs).foldl
        (fun e p => { e with names := e.names.insert p.name.text (.variable p.type.val) }) typeEnv
      let procEnv : ElabEnv := { baseEnv with typeEnv := extEnv, procGrades := knownGrades }
      let grade := [Grade.pure, Grade.err, Grade.heap, Grade.heapErr].findSome? fun g =>
        let st : ElabState := {
          freshCounter := 0
          heapVar := if g == .heap || g == .heapErr then some "$heap" else none }
        let trialEnv := { procEnv with procGrades := knownGrades.insert proc.name.text g }
        match (checkProducer impl [] g).run trialEnv |>.run st with
        | some _ => some g
        | none => none
      match grade with
      | some g =>
        let g := if proc.outputs.length > 1 then Grade.join g .err else g
        knownGrades := knownGrades.insert proc.name.text g
      | none => pure ()
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
      { name := Identifier.mk (className ++ "." ++ fieldName) none, args := [] : DatatypeConstructor }) []
  let fieldDatatype : TypeDefinition := .Datatype {
    name := "Field", typeArgs := [], constructors := fieldConstructors }
  let boxConstructors := allBoxConstructors.map fun (ctorName, _, ty) =>
    { name := Identifier.mk ctorName none, args := [
      { name := Identifier.mk (boxFieldName ty) none, type := ⟨boxFieldType ty, #[]⟩ }] : DatatypeConstructor }
  let boxDatatype : TypeDefinition := .Datatype {
    name := "Box", typeArgs := [], constructors := boxConstructors }
  if hasHeap then
    let heapTypesFiltered := heapConstants.types.filter fun td => match td with
      | .Datatype dt => dt.name.text != "Composite" && dt.name.text != "NotSupportedYet"
      | _ => true
    pure { program with
      staticProcedures := coreDefinitionsForLaurel.staticProcedures ++ heapConstants.staticProcedures ++ procs
      types := [fieldDatatype, boxDatatype, typeTagDatatype, compositeType] ++ heapTypesFiltered ++ coreDefinitionsForLaurel.types ++ program.types }
  else
    pure { program with
      staticProcedures := coreDefinitionsForLaurel.staticProcedures ++ procs
      types := [typeTagDatatype, compositeType] ++ coreDefinitionsForLaurel.types ++ program.types }

end
end Strata.FineGrainLaurel
