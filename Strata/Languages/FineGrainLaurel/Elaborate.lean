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

-- Grade Monoid (residuated, partially-ordered, idempotent)

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

-- Left residual: d \ e = e when d ≤ e, none otherwise (idempotent monoid)
def Grade.residual (d e : Grade) : Option Grade :=
  if d.leq e then some e else none

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

-- Convention Witness (defunctionalized subgrading)

inductive ConventionWitness where
  | pureCall | errorCall | heapCall | heapErrorCall

def conventionOf : Grade → ConventionWitness
  | .pure => .pureCall | .err => .errorCall
  | .heap => .heapCall | .heapErr => .heapErrorCall

-- Monad

structure ElabEnv where
  typeEnv : TypeEnv
  program : Laurel.Program

structure ElabState where
  freshCounter : Nat := 0
  heapVar : Option String := none
  procGrades : Std.HashMap String Grade := {}
  usedBoxConstructors : List (String × String × HighType) := []  -- (ctorName, dtorName, fieldType)

abbrev ElabM := ReaderT ElabEnv (StateT ElabState Option)

private def freshVar (pfx : String := "tmp") : ElabM String := do
  let s ← get; set { s with freshCounter := s.freshCounter + 1 }; pure s!"{pfx}${s.freshCounter}"

def boxConstructorName (ty : HighType) : String :=
  match ty with
  | .TInt => "BoxInt" | .TBool => "BoxBool" | .TFloat64 => "BoxFloat64"
  | .TReal => "BoxReal" | .TString => "BoxString"
  | .UserDefined name => s!"BoxComposite"
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
  let dtor := boxDestructorName ty
  let existing := (← get).usedBoxConstructors
  unless existing.any (fun (c, _, _) => c == ctor) do
    modify fun s => { s with usedBoxConstructors := s.usedBoxConstructors ++ [(ctor, dtor, ty)] }

def lookupFieldType (className fieldName : String) : ElabM (Option HighType) := do
  match (← read).typeEnv.classFields[className]? with
  | some fields => pure (fields.find? (fun (n, _) => n == fieldName) |>.map (·.2))
  | none => pure none

def resolveFieldOwner (fieldName : String) : ElabM (Option String) := do
  let env := (← read).typeEnv
  for (className, fields) in env.classFields.toList do
    if fields.any (fun (n, _) => n == fieldName) then return some className
  pure none

def lookupEnv (name : String) : ElabM (Option NameInfo) := do pure (← read).typeEnv.names[name]?
def extendEnv (name : String) (ty : HighType) (action : ElabM α) : ElabM α :=
  withReader (fun env => { env with typeEnv := { env.typeEnv with names := env.typeEnv.names.insert name (.variable ty) } }) action
def lookupFuncSig (name : String) : ElabM (Option FuncSig) := do
  match (← read).typeEnv.names[name]? with | some (.function sig) => pure (some sig) | _ => pure none
def lookupProcBody (name : String) : ElabM (Option StmtExprMd) := do
  match (← read).program.staticProcedures.find? (fun p => p.name.text == name) with
  | some proc => match proc.body with | .Transparent b => pure (some b) | _ => pure none
  | none => pure none

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

-- Subsumption (type coercions — value-level, no grade contribution)

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
  -- Box unwrapping is type-directed, not a subsumption coercion (see §Heap Field Access)
  | _, _ => .unrelated

def applySubsume (val : FGLValue) (actual expected : LowType) : FGLValue :=
  match subsume actual expected with | .refl => val | .coerce c => c val | .unrelated => val

-- The nesting combinator type: takes the rest (monadic) and produces the nested FGL
abbrev NestComb := ElabM FGLProducer → ElabM FGLProducer

-- Elaboration (mutual block)

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
        | some cn => do
          let ft ← lookupFieldType cn field.text
          pure (ft.getD (.TCore "Any"))
        | none => pure (.TCore "Any")
      recordBoxUse fieldTy
      -- readField expects Composite — narrow from Any if needed
      let compositeObj := applySubsume ov objTy (.TCore "Composite")
      let read := FGLValue.staticCall "readField" [.var hv, compositeObj, .staticCall qualifiedName []]
      let dtor := boxDestructorName fieldTy
      pure (.staticCall dtor [read], eraseType fieldTy)
    | none => pure (.fieldAccess ov field.text, .TCore "Any")
  | .StaticCall callee args =>
    let sig ← lookupFuncSig callee.text
    match sig with
    | some s =>
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

partial def checkArgs (args : List StmtExprMd) (params : List (String × HighType)) : ElabM (List FGLValue) :=
  (args.zip (params.map (·.2))).mapM fun (arg, pty) => checkValue arg pty

-- synthProducer: returns (nesting combinator, result type, grade)
-- The combinator takes the rest of the block (monadic) and nests it into the body field.
partial def synthProducer (expr : StmtExprMd) : ElabM (NestComb × LowType × Grade) := do
  match expr.val with
  | .StaticCall callee args =>
    let sig ← lookupFuncSig callee.text
    match sig with
    | some s =>
      let checkedArgs ← checkArgs args s.params
      let grade ← discoverGrade callee.text
      let retTy := eraseType s.returnType
      match conventionOf grade with
      | .pureCall =>
        pure (fun restM => restM, retTy, .pure)
      | .errorCall =>
        pure (fun restM => mkErrorCall callee.text checkedArgs s.returnType fun _rv => restM, retTy, .err)
      | .heapCall =>
        pure (fun restM => mkHeapCall callee.text checkedArgs s.returnType fun _rv => restM, retTy, .heap)
      | .heapErrorCall =>
        pure (fun restM => mkHeapErrorCall callee.text checkedArgs s.returnType fun _rv => restM, retTy, .heapErr)
    | none =>
      let checkedArgs ← args.mapM fun arg => checkValue arg (.TCore "Any")
      let grade ← discoverGrade callee.text
      let retTy := LowType.TCore "Any"
      match conventionOf grade with
      | .pureCall =>
        pure (fun restM => restM, retTy, .pure)
      | .errorCall =>
        pure (fun restM => mkErrorCall callee.text checkedArgs (.TCore "Any") fun _rv => restM, retTy, .err)
      | .heapCall =>
        pure (fun restM => mkHeapCall callee.text checkedArgs (.TCore "Any") fun _rv => restM, retTy, .heap)
      | .heapErrorCall =>
        pure (fun restM => mkHeapErrorCall callee.text checkedArgs (.TCore "Any") fun _rv => restM, retTy, .heapErr)

  | .Assign targets value => match targets with
    | [target] =>
      -- Field write: Assign [FieldSelect obj field] value → heap update
      match target.val with
      | .FieldSelect obj field =>
        let (ov, objTy) ← synthValue obj
        pure (fun restM => do
          match (← get).heapVar with
          | some hv =>
            let owner ← resolveFieldOwner field.text
            let qualifiedName := match owner with | some cn => cn ++ "." ++ field.text | none => field.text
            let fieldTy ← match owner with
              | some cn => do let ft ← lookupFieldType cn field.text; pure (ft.getD (.TCore "Any"))
              | none => pure (.TCore "Any")
            recordBoxUse fieldTy
            let cv ← checkValue value fieldTy
            let ctor := boxConstructorName fieldTy
            let boxed := FGLValue.staticCall ctor [cv]
            let compositeObj := applySubsume ov objTy (.TCore "Composite")
            let newHeap := FGLValue.staticCall "updateField" [.var hv, compositeObj, .staticCall qualifiedName [], boxed]
            let freshH ← freshVar "heap"
            modify fun s => { s with heapVar := some freshH }
            extendEnv freshH .THeap (do
              let rest ← restM
              pure (.varDecl freshH (.TCore "Heap") (some newHeap) rest))
          | none => failure, .TVoid, .heap)
      | _ =>
      let targetTy ← match target.val with
        | .Identifier id => match (← lookupEnv id.text) with | some (.variable t) => pure t | _ => pure (.TCore "Any")
        | _ => pure (.TCore "Any")
      let (tv, _) ← synthValue target
      match value.val with
      | .Hole false _ =>
        pure (fun restM => mkVarDecl "_havoc" (eraseType targetTy) none fun hv => do
          let rest ← restM; pure (.assign tv hv rest), .TVoid, .pure)
      | .Hole true _ =>
        let hv ← freshVar "hole"
        let name := match target.val with | .Identifier id => id.text | _ => "_x"
        pure (fun restM => mkVarDecl name (eraseType targetTy) (some (.staticCall hv [])) fun _ => restM, .TVoid, .pure)
      | .New classId =>
        pure (fun restM => do
          match (← get).heapVar with
          | some hv =>
            let ref := FGLValue.staticCall "Heap..nextReference!" [.var hv]
            let newHeap := FGLValue.staticCall "increment" [.var hv]
            let obj := FGLValue.staticCall "MkComposite" [ref, .staticCall (classId.text ++ "_TypeTag") []]
            let freshH ← freshVar "heap"
            modify fun s => { s with heapVar := some freshH }
            extendEnv freshH .THeap (do
              let rest ← restM
              pure (.varDecl freshH (.TCore "Heap") (some newHeap) (.assign tv obj rest)))
          | none => failure, .TVoid, .heap)
      | .StaticCall callee args =>
        let sig ← lookupFuncSig callee.text
        match sig with
        | some s =>
          let checkedArgs ← checkArgs args s.params
          let grade ← discoverGrade callee.text
          match conventionOf grade with
          | .pureCall =>
            let cv := FGLValue.staticCall callee.text checkedArgs
            let coerced := applySubsume cv (eraseType s.returnType) (eraseType targetTy)
            pure (fun restM => do let rest ← restM; pure (.assign tv coerced rest), .TVoid, .pure)
          | .errorCall =>
            pure (fun restM => mkErrorCall callee.text checkedArgs s.returnType fun rv => do
              let coerced := applySubsume rv (eraseType s.returnType) (eraseType targetTy)
              let rest ← restM; pure (.assign tv coerced rest), .TVoid, .err)
          | .heapCall =>
            pure (fun restM => mkHeapCall callee.text checkedArgs s.returnType fun rv => do
              let coerced := applySubsume rv (eraseType s.returnType) (eraseType targetTy)
              let rest ← restM; pure (.assign tv coerced rest), .TVoid, .heap)
          | .heapErrorCall =>
            pure (fun restM => mkHeapErrorCall callee.text checkedArgs s.returnType fun rv => do
              let coerced := applySubsume rv (eraseType s.returnType) (eraseType targetTy)
              let rest ← restM; pure (.assign tv coerced rest), .TVoid, .heapErr)
        | none =>
          let checkedArgs ← args.mapM fun arg => checkValue arg (.TCore "Any")
          let grade ← discoverGrade callee.text
          match conventionOf grade with
          | .pureCall =>
            let cv := FGLValue.staticCall callee.text checkedArgs
            pure (fun restM => do let rest ← restM; pure (.assign tv cv rest), .TVoid, .pure)
          | .errorCall =>
            pure (fun restM => mkErrorCall callee.text checkedArgs (.TCore "Any") fun rv => do
              let rest ← restM; pure (.assign tv rv rest), .TVoid, .err)
          | .heapCall =>
            pure (fun restM => mkHeapCall callee.text checkedArgs (.TCore "Any") fun rv => do
              let rest ← restM; pure (.assign tv rv rest), .TVoid, .heap)
          | .heapErrorCall =>
            pure (fun restM => mkHeapErrorCall callee.text checkedArgs (.TCore "Any") fun rv => do
              let rest ← restM; pure (.assign tv rv rest), .TVoid, .heapErr)
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
          let dtor := boxDestructorName fieldTy
          let unboxed := FGLValue.staticCall dtor [read]
          let coerced := applySubsume unboxed (eraseType fieldTy) (eraseType targetTy)
          pure (fun restM => do let rest ← restM; pure (.assign tv coerced rest), .TVoid, .heap)
        | none =>
          let fv := FGLValue.fieldAccess ov field.text
          pure (fun restM => do let rest ← restM; pure (.assign tv fv rest), .TVoid, .pure)
      | _ =>
        let cv ← checkValue value targetTy
        pure (fun restM => do let rest ← restM; pure (.assign tv cv rest), .TVoid, .pure)
    | _ => pure (fun restM => restM, .TVoid, .pure)

  | .LocalVariable nameId typeMd initOpt =>
    let ci ← match initOpt with
      | some ⟨.Hole false _, _⟩ => pure none
      | some ⟨.Hole true _, _⟩ => do let hv ← freshVar "hole"; pure (some (.staticCall hv []))
      | some i => do let v ← checkValue i typeMd.val; pure (some v)
      | none => pure none
    pure (fun restM => mkVarDecl nameId.text (eraseType typeMd.val) ci fun _ => restM, .TVoid, .pure)

  | .Assert cond =>
    let cc ← checkValue cond .TBool
    pure (fun restM => do let rest ← restM; pure (.assert cc rest), .TVoid, .pure)

  | .Assume cond =>
    let cc ← checkValue cond .TBool
    pure (fun restM => do let rest ← restM; pure (.assume cc rest), .TVoid, .pure)

  | .While _ _ _ _ => failure  -- While is check-mode only (handled by elaborateBlock)

  | .IfThenElse _ _ _ => failure  -- IfThenElse is check-mode only (handled by elaborateBlock)

  | .Exit target =>
    pure (fun _restM => pure (.exit target), .TVoid, .pure)

  | .Return valueOpt =>
    pure (fun _restM => do
      let retTy := .TCore "Any"
      match valueOpt with
      | some v => let cv ← checkValue v retTy; pure (.returnValue cv)
      | none => pure (.returnValue .fromNone), .TVoid, .pure)

  | .Block stmts label =>
    pure (fun restM => do
      let g ← currentGrade
      let prod ← elaborateBlock stmts .TVoid g
      let rest ← restM
      pure (match label with | some l => .labeledBlock l prod | none => prod), .TVoid, .pure)

  | .New classId =>
    pure (fun restM => do
      match (← get).heapVar with
      | some hv =>
        let ref := FGLValue.staticCall "Heap..nextReference!" [.var hv]
        let newHeap := FGLValue.staticCall "increment" [.var hv]
        let obj := FGLValue.staticCall "MkComposite" [ref, .staticCall (classId.text ++ "_TypeTag") []]
        let freshH ← freshVar "heap"
        modify fun s => { s with heapVar := some freshH }
        extendEnv freshH .THeap (do
          let rest ← restM
          pure (.varDecl freshH (.TCore "Heap") (some newHeap) (.returnValue obj)))
      | none => failure, .TCore "Composite", .heap)

  | .Hole deterministic _ =>
    if deterministic then do
      let hv ← freshVar "hole"
      pure (fun restM => do let rest ← restM; pure (.returnValue (.staticCall hv [])), .TCore "Any", .pure)
    else
      pure (fun restM => mkVarDecl "_havoc" (.TCore "Any") none fun _hv => restM, .TCore "Any", .pure)

  | _ => pure (fun restM => restM, .TVoid, .pure)

-- checkProducer: check-mode rules (if, var-bind, return) + fallback to synth+subsumption
partial def checkProducer (expr : StmtExprMd) (expected : LowType) (grade : Grade) : ElabM FGLProducer := do
  match expr.val with
  | .IfThenElse cond thn els =>
    let cc ← checkValue cond .TBool
    let tp ← checkProducer thn expected grade
    let ep ← match els with | some e => checkProducer e expected grade | none => pure .unit
    pure (.ifThenElse cc tp ep)
  | .Return valueOpt =>
    match valueOpt with
    | some v => let cv ← checkValue v (liftType expected); pure (.returnValue cv)
    | none => pure (.returnValue .fromNone)
  | .Block stmts label =>
    let prod ← elaborateBlock stmts expected grade
    pure (match label with | some l => .labeledBlock l prod | none => prod)
  | _ =>
    elaborateBlock [expr] expected grade

-- elaborateBlock: sequence statements via nesting combinators + to-rule
partial def elaborateBlock (stmts : List StmtExprMd) (expected : LowType) (grade : Grade) : ElabM FGLProducer := do
  match stmts with
  | [] => pure .unit
  | [last] => match last.val with
    | .Return _ => checkProducer last expected grade
    | .Exit _ =>
      let (plug, _, _) ← synthProducer last
      plug (pure .unit)
    | _ =>
      let (plug, _, d) ← synthProducer last
      guard (Grade.leq d grade)
      plug (pure .unit)
  | stmt :: rest =>
    let (plug, _, d) ← synthProducer stmt
    guard (Grade.leq d grade)
    plug (elaborateBlock rest expected grade)

-- discoverGrade: typing rules as oracle (checkProducer at each grade)
partial def discoverGrade (callee : String) : ElabM Grade := do
  match (← get).procGrades[callee]? with
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
      let grade ← tryGrades paramEnv bodyExpr retTy [.pure, .err, .heap, .heapErr]
      modify fun s => { s with procGrades := s.procGrades.insert callee grade }
      pure grade
    | none => pure .pure

partial def tryGrades (env : ElabEnv) (body : StmtExprMd) (retTy : LowType) (grades : List Grade) : ElabM Grade := do
  match grades with
  | [] => pure .heapErr
  | g :: rest =>
    let st ← get
    let trialSt : ElabState := { st with
      heapVar := if g == .heap || g == .heapErr then some "$heap" else none }
    match (checkProducer body retTy g).run env |>.run trialSt with
    | some (_, st') =>
      -- Adopt discovered procGrades from successful trial
      modify fun s => { s with procGrades := st'.procGrades }
      pure g
    | none => tryGrades env body retTy rest

-- Helper: get the current grade from the check context (threaded via elaborateBlock)
-- We read the heapVar to infer the ambient grade
partial def currentGrade : ElabM Grade := do
  match (← get).heapVar with
  | some _ => pure .heapErr
  | none => pure .heapErr

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
  let env : ElabEnv := { typeEnv := typeEnv, program := program }
  let mut procs : List Laurel.Procedure := []
  let mut globalState : ElabState := {}
  for proc in program.staticProcedures do
    match proc.body with
    | .Transparent bodyExpr =>
      let extEnv := (proc.inputs ++ proc.outputs).foldl
        (fun e p => { e with names := e.names.insert p.name.text (.variable p.type.val) }) typeEnv
      let procEnv : ElabEnv := { env with typeEnv := extEnv }
      let retTy := match proc.outputs[0]? with | some o => eraseType o.type.val | none => .TCore "Any"
      -- Discover grade by trying checkProducer at each level
      let grade := [Grade.pure, Grade.err, Grade.heap, Grade.heapErr].findSome? fun g =>
        let st : ElabState := { globalState with
          freshCounter := 0
          heapVar := if g == .heap || g == .heapErr then some "$heap" else none }
        match (checkProducer bodyExpr retTy g).run procEnv |>.run st with
        | some _ => some g
        | none => none
      match grade with
      | some g =>
        dbg_trace s!"[elab] {proc.name.text} grade={repr g}"
        let st : ElabState := { globalState with
          freshCounter := 0
          heapVar := if g == .heap || g == .heapErr then some "$heap" else none }
        match (checkProducer bodyExpr retTy g).run procEnv |>.run st with
        | some (fgl, st') =>
          globalState := { globalState with
            procGrades := st'.procGrades
            usedBoxConstructors := globalState.usedBoxConstructors ++ st'.usedBoxConstructors.filter
              (fun (c, _, _) => !globalState.usedBoxConstructors.any (fun (c2, _, _) => c == c2)) }
          let projected := projectBody bodyExpr.md fgl
          -- If heap grade, add heap params
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
    | _ => procs := procs ++ [proc]
  let hasHeap := globalState.procGrades.toList.any fun (_, g) => g == .heap || g == .heapErr
  -- Collect composite class names from TypeEnv for TypeTag generation
  let compositeNames := typeEnv.classFields.toList.map (·.1)
  let typeTagDatatype : TypeDefinition := .Datatype {
    name := "TypeTag", typeArgs := [],
    constructors := compositeNames.map fun n => { name := Identifier.mk (n ++ "_TypeTag") none, args := [] } }
  let compositeType : TypeDefinition := .Datatype {
    name := "Composite", typeArgs := [],
    constructors := [{ name := Identifier.mk "MkComposite" none, args := [
      { name := Identifier.mk "ref" none, type := ⟨.TInt, #[]⟩ },
      { name := Identifier.mk "typeTag" none, type := ⟨.UserDefined "TypeTag", #[]⟩ }] }] }
  -- Generate Field datatype: one zero-arg constructor per class field (qualified: ClassName.fieldName)
  let fieldConstructors := typeEnv.classFields.toList.foldl (fun acc (className, fields) =>
    acc ++ fields.map fun (fieldName, _) =>
      { name := Identifier.mk (className ++ "." ++ fieldName) none, args := [] : DatatypeConstructor }) []
  let fieldDatatype : TypeDefinition := .Datatype {
    name := "Field", typeArgs := [], constructors := fieldConstructors }
  -- Generate Box datatype from used constructors
  let boxConstructors := globalState.usedBoxConstructors.map fun (ctorName, _, ty) =>
    { name := Identifier.mk ctorName none, args := [
      { name := Identifier.mk (boxFieldName ty) none, type := ⟨boxFieldType ty, #[]⟩ }] : DatatypeConstructor }
  let boxDatatype : TypeDefinition := .Datatype {
    name := "Box", typeArgs := [], constructors := boxConstructors }
  if hasHeap then
    -- Filter out Composite from heapConstants (we provide our own with typeTag)
    let heapTypesFiltered := heapConstants.types.filter fun td => match td with
      | .Datatype dt => dt.name.text != "Composite"
      | _ => true
    pure { program with
      staticProcedures := coreDefinitionsForLaurel.staticProcedures ++ heapConstants.staticProcedures ++ procs
      types := [fieldDatatype, boxDatatype, typeTagDatatype, compositeType] ++ heapTypesFiltered ++ program.types }
  else
    pure { program with
      staticProcedures := coreDefinitionsForLaurel.staticProcedures ++ procs
      types := [typeTagDatatype, compositeType] ++ program.types }

end
end Strata.FineGrainLaurel
