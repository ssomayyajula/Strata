/-
  Copyright Strata Contributors
  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.Languages.FineGrainLaurel.FineGrainLaurel
public import Strata.Languages.Laurel.Laurel
public import Strata.Languages.Laurel.HeapParameterizationConstants
public import Strata.Languages.Python.NameResolution

namespace Strata.FineGrainLaurel
open Strata.Laurel
open Strata.Python.Resolution
public section

def mkLaurel (md : Imperative.MetaData Core.Expression) (e : StmtExpr) : StmtExprMd :=
  { val := e, md := md }
def mkHighTypeMd (md : Imperative.MetaData Core.Expression) (ty : HighType) : HighTypeMd :=
  { val := ty, md := md }

-- Grade

inductive Grade where | pure | err | heap | heapErr deriving Inhabited, BEq, Repr

def Grade.mul : Grade → Grade → Grade
  | .pure, e => e | e, .pure => e
  | .err, .heap => .heapErr | .heap, .err => .heapErr
  | .err, .err => .err | .heap, .heap => .heap
  | .heapErr, _ => .heapErr | _, .heapErr => .heapErr

def Grade.residual : Grade → Grade → Option Grade
  | .pure, e => some e
  | .err, .err => some .pure | .err, .heapErr => some .heap
  | .heap, .heap => some .pure | .heap, .heapErr => some .err
  | .heapErr, .heapErr => some .pure
  | _, _ => none

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

-- Monad + State

structure ElabState where
  freshCounter : Nat := 0
  heapVar : Option String := none

abbrev ElabM := ReaderT TypeEnv (StateT ElabState Option)

private def freshVar (pfx : String := "tmp") : ElabM String := do
  let s ← get; set { s with freshCounter := s.freshCounter + 1 }; pure s!"{pfx}${s.freshCounter}"

def lookupEnv (name : String) : ElabM (Option NameInfo) := do pure (← read).names[name]?
def extendEnv (name : String) (ty : HighType) (action : ElabM α) : ElabM α :=
  withReader (fun env => { env with names := env.names.insert name (.variable ty) }) action
def lookupFuncSig (name : String) : ElabM (Option FuncSig) := do
  match (← read).names[name]? with | some (.function sig) => pure (some sig) | _ => pure none

-- HOAS Smart Constructors
-- These internally use heapVar from state + freshVar + extendEnv.
-- External code never touches raw variable names.

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
      -- Update heapVar to the fresh heap output (outs[0] is the new heap)
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
  | .TCore "Box", .TCore "Any" => .coerce (fun v => .staticCall "Box..AnyVal!" [v])
  | _, _ => .unrelated

def applySubsume (val : FGLValue) (actual expected : LowType) : FGLValue :=
  match subsume actual expected with | .refl => val | .coerce c => c val | .unrelated => val

-- Elaboration

mutual

partial def synthValue (expr : StmtExprMd) : ElabM (FGLValue × LowType) := do
  match expr.val with
  | .LiteralInt n => pure (.litInt n, .TInt)
  | .LiteralBool b => pure (.litBool b, .TBool)
  | .LiteralString s => pure (.litString s, .TString)
  | .Identifier id =>
    match (← lookupEnv id.text) with
    | some (.variable ty) => pure (.var id.text, eraseType ty)
    | some (.function sig) => pure (.var id.text, eraseType sig.effectType.resultType)
    | _ => pure (.var id.text, .TCore "Any")
  | .FieldSelect obj field =>
    let (ov, _) ← synthValue obj
    match (← get).heapVar with
    | some hv =>
      let read := FGLValue.staticCall "readField" [.var hv, ov, .staticCall field.text []]
      pure (.staticCall "Box..AnyVal!" [read], .TCore "Any")
    | none => pure (.fieldAccess ov field.text, .TCore "Any")
  | .StaticCall callee args =>
    let sig ← lookupFuncSig callee.text
    match sig with
    | some s =>
      let checkedArgs ← checkArgs args s.params
      pure (.staticCall callee.text checkedArgs, eraseType s.effectType.resultType)
    | none =>
      let checkedArgs ← args.mapM fun arg => checkValue arg (.TCore "Any")
      pure (.staticCall callee.text checkedArgs, .TCore "Any")
  | .New id => dbg_trace s!"[BUG] synthValue: New({id.text})"; failure
  | .Block _ _ => dbg_trace "[BUG] synthValue: Block"; failure
  | .Assign _ _ => dbg_trace "[BUG] synthValue: Assign"; failure
  | .IfThenElse _ _ _ => dbg_trace "[BUG] synthValue: IfThenElse"; failure
  | .Hole _ _ => pure (.var "_hole", .TCore "Any")
  | _ => dbg_trace "[BUG] synthValue: other"; failure

partial def checkValue (expr : StmtExprMd) (expected : HighType) : ElabM FGLValue := do
  let (val, actual) ← synthValue expr
  pure (applySubsume val actual (eraseType expected))

partial def checkArgs (args : List StmtExprMd) (params : List (String × HighType)) : ElabM (List FGLValue) :=
  (args.zip (params.map (·.2))).mapM fun (arg, pty) => checkValue arg pty

partial def synthProducer (expr : StmtExprMd) (cont : ElabM FGLProducer) : ElabM FGLProducer := do
  match expr.val with
  | .StaticCall callee args =>
    let sig ← lookupFuncSig callee.text
    match sig with
    | some s =>
      let checkedArgs ← checkArgs args s.params
      match s.effectType with
      | .pure _ =>
        let val := FGLValue.staticCall callee.text checkedArgs
        -- Pure call is a value, just continue
        cont
      | .error resultTy _ =>
        mkErrorCall callee.text checkedArgs resultTy fun _rv => cont
      | .stateful resultTy =>
        mkHeapCall callee.text checkedArgs resultTy fun _rv => cont
      | .statefulError resultTy _ =>
        mkHeapErrorCall callee.text checkedArgs resultTy fun _rv => cont
    | none => cont
  | .New classId =>
    match (← get).heapVar with
    | some hv =>
      let ref := FGLValue.staticCall "Heap..nextReference!" [.var hv]
      let newHeap := FGLValue.staticCall "increment" [.var hv]
      let obj := FGLValue.staticCall "MkComposite" [ref, .staticCall (classId.text ++ "_TypeTag") []]
      let freshH ← freshVar "heap"
      modify fun s => { s with heapVar := some freshH }
      let c ← extendEnv freshH .THeap cont
      pure (.assign (.var freshH) newHeap (.returnValue obj))
    | none => failure
  | .Assign targets value => match targets with
    | [target] =>
      let targetTy ← match target.val with
        | .Identifier id => match (← lookupEnv id.text) with | some (.variable t) => pure t | _ => pure (.TCore "Any")
        | _ => pure (.TCore "Any")
      let (tv, _) ← synthValue target
      match value.val with
      | .Hole false _ =>
        mkVarDecl "_havoc" (eraseType targetTy) none fun hv => do
          let c ← cont; pure (.assign tv hv c)
      | .Hole true _ => do
        let hv ← freshVar "hole"
        mkVarDecl (match target.val with | .Identifier id => id.text | _ => "_x") (eraseType targetTy) (some (.staticCall hv [])) fun _ => cont
      | _ =>
        let cr ← checkValue value targetTy
        let c ← cont
        pure (.assign tv cr c)
    | _ => cont
  | .LocalVariable nameId typeMd initOpt =>
    let ci ← match initOpt with
      | some ⟨.Hole false _, _⟩ => pure none
      | some ⟨.Hole true _, _⟩ => do let hv ← freshVar "hole"; pure (some (.staticCall hv []))
      | some i => do let v ← checkValue i typeMd.val; pure (some v)
      | none => pure none
    mkVarDecl nameId.text (eraseType typeMd.val) ci fun _ => cont
  | .Assert cond =>
    let cc ← checkValue cond .TBool
    let c ← cont
    pure (.assert cc c)
  | .Assume cond =>
    let cc ← checkValue cond .TBool
    let c ← cont
    pure (.assume cc c)
  | .While cond _invs _dec body =>
    let cc ← checkValue cond .TBool
    let bp ← checkProducer body .TVoid
    let c ← cont
    pure (.whileLoop cc bp c)
  | .Exit target => pure (.exit target)
  | .Return valueOpt =>
    let retTy := .TCore "Any"  -- TODO: pass from check context
    match valueOpt with
    | some v => let cv ← checkValue v retTy; pure (.returnValue cv)
    | none => pure (.returnValue .fromNone)
  | .IfThenElse cond thn els =>
    let cc ← checkValue cond .TBool
    let tp ← checkProducer thn .TVoid
    let ep ← match els with | some e => checkProducer e .TVoid | none => pure .unit
    let c ← cont
    pure (.ifThenElse cc tp ep)
  | .Block stmts label =>
    let prod ← elaborateBlock stmts cont
    pure (match label with | some l => .labeledBlock l prod | none => prod)
  | .Hole deterministic _ =>
    if deterministic then do
      let hv ← freshVar "hole"
      let c ← cont
      pure (.returnValue (.staticCall hv []))
    else
      mkVarDecl "_havoc" (.TCore "Any") none fun _hv => cont
  | _ => cont

partial def checkProducer (expr : StmtExprMd) (expected : LowType) : ElabM FGLProducer := do
  match expr.val with
  | .IfThenElse cond thn els =>
    let cc ← checkValue cond .TBool
    let tp ← checkProducer thn expected
    let ep ← match els with | some e => checkProducer e expected | none => pure .unit
    pure (.ifThenElse cc tp ep)
  | .Return valueOpt =>
    match valueOpt with
    | some v => let cv ← checkValue v (liftType expected); pure (.returnValue cv)
    | none => pure (.returnValue .fromNone)
  | .Block stmts label =>
    let prod ← elaborateBlock stmts (pure .unit)
    pure (match label with | some l => .labeledBlock l prod | none => prod)
  | _ =>
    synthProducer expr (pure .unit)

partial def elaborateBlock (stmts : List StmtExprMd) (terminal : ElabM FGLProducer) : ElabM FGLProducer := do
  match stmts with
  | [] => terminal
  | [last] => checkProducer last .TVoid
  | stmt :: rest =>
    synthProducer stmt (elaborateBlock rest terminal)

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

-- fullElaborate

def fullElaborate (typeEnv : TypeEnv) (program : Laurel.Program) : Except String Laurel.Program := do
  let mut procs : List Laurel.Procedure := []
  for proc in program.staticProcedures do
    match proc.body with
    | .Transparent bodyExpr =>
      let st : ElabState := { freshCounter := 0, heapVar := none }
      let extEnv := (proc.inputs ++ proc.outputs).foldl
        (fun env p => { env with names := env.names.insert p.name.text (.variable p.type.val) }) typeEnv
      match (checkProducer bodyExpr (.TCore "Any")).run extEnv |>.run st with
      | some (fgl, _) => procs := procs ++ [{ proc with body := .Transparent (projectBody bodyExpr.md fgl) }]
      | none => procs := procs ++ [proc]
    | _ => procs := procs ++ [proc]
  let compositeType : TypeDefinition := .Datatype { name := "Composite", typeArgs := [], constructors := [{ name := "MkComposite", args := [{ name := "ref", type := ⟨.TInt, #[]⟩ }] }] }
  pure { program with staticProcedures := procs, types := [compositeType] ++ program.types }

end
end Strata.FineGrainLaurel
