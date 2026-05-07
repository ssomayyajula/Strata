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

-- ═══════════════════════════════════════════════════════════════════════════
-- Type Systems (Architecture §"Two Type Systems")
-- HighType (Translation's output) → LowType (FGL's type system)
-- ═══════════════════════════════════════════════════════════════════════════

inductive LowType where
  | TInt | TBool | TString | TFloat64 | TVoid | TCore (name : String)
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

-- ═══════════════════════════════════════════════════════════════════════════
-- FGL Terms (Architecture §"Representation Decisions")
-- Value = inert, Producer = effectful. Lean types enforce separation.
-- ═══════════════════════════════════════════════════════════════════════════

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
  | callWithError (callee : String) (args : List FGLValue)
      (resultVar : String) (errorVar : String)
      (resultTy : LowType) (errorTy : LowType) (body : FGLProducer)
  | exit (label : String)
  | labeledBlock (label : String) (body : FGLProducer)
  | seq (first : FGLProducer) (second : FGLProducer)
  | unit
  deriving Inhabited

-- ═══════════════════════════════════════════════════════════════════════════
-- Monad (Architecture §"Monad carries context")
-- ═══════════════════════════════════════════════════════════════════════════

structure ElabState where
  freshCounter : Nat := 0
  currentProcReturnType : HighType := .TCore "Any"

abbrev ElabM := ReaderT TypeEnv (StateT ElabState Id)

private def freshVar (pfx : String := "tmp") : ElabM String := do
  let s ← get; set { s with freshCounter := s.freshCounter + 1 }; pure s!"{pfx}${s.freshCounter}"

def lookupEnv (name : String) : ElabM (Option NameInfo) := do pure (← read).names[name]?

def extendEnv (name : String) (ty : HighType) (action : ElabM α) : ElabM α :=
  withReader (fun env => { env with names := env.names.insert name (.variable ty) }) action

def lookupFuncSig (name : String) : ElabM (Option FuncSig) := do
  match (← read).names[name]? with | some (.function sig) => pure (some sig) | _ => pure none

-- ═══════════════════════════════════════════════════════════════════════════
-- HOAS Smart Constructors (Architecture §"Γ Extension at Binding Sites")
-- The ONLY way to create binding forms. Each extends Γ before calling closure.
-- ═══════════════════════════════════════════════════════════════════════════

def mkCallWithError (callee : String) (args : List FGLValue) (resultTy errTy : LowType)
    (body : FGLValue → FGLValue → ElabM FGLProducer) : ElabM FGLProducer := do
  let rv ← freshVar "result"
  let ev ← freshVar "err"
  let cont ← extendEnv rv (liftType resultTy) (extendEnv ev (.TCore "Error") (body (.var rv) (.var ev)))
  pure (.callWithError callee args rv ev resultTy errTy cont)

def mkVarDecl (name : String) (ty : LowType) (init : Option FGLValue)
    (body : FGLValue → ElabM FGLProducer) : ElabM FGLProducer := do
  let cont ← extendEnv name (liftType ty) (body (.var name))
  pure (.varDecl name ty init cont)

-- ═══════════════════════════════════════════════════════════════════════════
-- Subsumption (Architecture §"The Unified Subsumption Function")
-- One function, one table, three outcomes. Both upcast and narrowing produce VALUES.
-- ═══════════════════════════════════════════════════════════════════════════

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

-- ═══════════════════════════════════════════════════════════════════════════
-- Elaboration (Architecture §"The Typing Rules")
--
-- Entry: checkProducer (CHECK mode — type flows DOWN from context)
-- Synth: discovers types bottom-up at elimination forms
-- Check: uses annotations as expected types, inserts coercions via subsume
--
-- Evaluation order: Egger et al. 2014 effect-passing translation.
-- Left-to-right preserved by CPS structure of elaborateBlock.
-- ═══════════════════════════════════════════════════════════════════════════

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
  | .StaticCall callee args =>
    let sig ← lookupFuncSig callee.text
    match sig with
    | some s =>
      let checkedArgs ← checkArgs args s.params
      pure (.staticCall callee.text checkedArgs, eraseType s.effectType.resultType)
    | none =>
      let checkedArgs ← args.mapM fun arg => checkValue arg (.TCore "Any")
      pure (.staticCall callee.text checkedArgs, .TCore "Any")
  | .FieldSelect obj field =>
    let (ov, _) ← synthValue obj
    pure (.fieldAccess ov field.text, .TCore "Any")
  | .New classId =>
    pure (.staticCall "MkComposite" [.var "$heap_nextRef", .staticCall (classId.text ++ "_TypeTag") []], .TCore "Composite")
  | _ => pure (.var "_elab_unknown", .TCore "Any")

partial def checkValue (expr : StmtExprMd) (expected : HighType) : ElabM FGLValue := do
  let (val, actual) ← synthValue expr
  pure (applySubsume val actual (eraseType expected))

partial def checkArgs (args : List StmtExprMd) (params : List (String × HighType)) : ElabM (List FGLValue) := do
  let pairs := args.zip (params.map (·.2))
  pairs.mapM fun (arg, pty) => checkValue arg pty

partial def checkProducer (expr : StmtExprMd) (expected : LowType) : ElabM FGLProducer := do
  match expr.val with
  | .IfThenElse cond thn els =>
    let cc ← checkValue cond .TBool
    let tp ← checkProducer thn expected
    let ep ← match els with | some e => checkProducer e expected | none => pure .unit
    pure (.ifThenElse cc tp ep)
  | .Return valueOpt =>
    let retTy := (← get).currentProcReturnType
    match valueOpt with
    | some v => let cv ← checkValue v retTy; pure (.returnValue cv)
    | none => pure (.returnValue .fromNone)
  | .Block stmts label =>
    let prod ← elaborateBlock stmts expected
    pure (match label with | some l => .labeledBlock l prod | none => prod)
  | _ =>
    let (prod, _) ← synthProducer expr
    pure prod

partial def synthProducer (expr : StmtExprMd) : ElabM (FGLProducer × LowType) := do
  match expr.val with
  | .StaticCall callee args =>
    if callee.text == "PAnd" || callee.text == "POr" then
      shortCircuit callee.text args
    else
      let sig ← lookupFuncSig callee.text
      match sig with
      | some s => match s.effectType with
        | .pure _ =>
          let (val, ty) ← synthValue expr
          pure (.returnValue val, ty)
        | .error resultTy _ =>
          let checkedArgs ← checkArgs args s.params
          let prod ← mkCallWithError callee.text checkedArgs (eraseType resultTy) (.TCore "Error")
            fun rv _ev => pure (.returnValue rv)
          pure (prod, eraseType resultTy)
        | .stateful resultTy =>
          let checkedArgs ← checkArgs args s.params
          pure (.returnValue (.staticCall callee.text checkedArgs), eraseType resultTy)
        | .statefulError resultTy _ =>
          let checkedArgs ← checkArgs args s.params
          let prod ← mkCallWithError callee.text checkedArgs (eraseType resultTy) (.TCore "Error")
            fun rv _ev => pure (.returnValue rv)
          pure (prod, eraseType resultTy)
      | none =>
        let (val, ty) ← synthValue expr
        pure (.returnValue val, ty)
  | .Assign targets value => match targets with
    | [target] => elaborateAssign target value (pure .unit)
    | _ => pure (.unit, .TVoid)
  | .LocalVariable nameId typeMd initOpt =>
    let ci ← elaborateInit initOpt typeMd.val
    let prod ← mkVarDecl nameId.text (eraseType typeMd.val) ci fun _ => pure .unit
    pure (prod, .TVoid)
  | .While cond _invs _dec body =>
    let cc ← checkValue cond .TBool
    let bp ← checkProducer body .TVoid
    pure (.whileLoop cc bp .unit, .TVoid)
  | .Assert cond =>
    let cc ← checkValue cond .TBool
    pure (.assert cc .unit, .TVoid)
  | .Assume cond =>
    let cc ← checkValue cond .TBool
    pure (.assume cc .unit, .TVoid)
  | .Block stmts label =>
    let prod ← elaborateBlock stmts .TVoid
    pure (match label with | some l => (.labeledBlock l prod, .TVoid) | none => (prod, .TVoid))
  | .Exit target => pure (.exit target, .TVoid)
  | .Return valueOpt =>
    let retTy := (← get).currentProcReturnType
    match valueOpt with
    | some v => let cv ← checkValue v retTy; pure (.returnValue cv, eraseType retTy)
    | none => pure (.returnValue .fromNone, .TVoid)
  | .IfThenElse _ _ _ =>
    let p ← checkProducer expr .TVoid
    pure (p, .TVoid)
  | .FieldSelect _ _ =>
    let (v, t) ← synthValue expr
    pure (.returnValue v, t)
  | .New _ =>
    let (v, t) ← synthValue expr
    pure (.returnValue v, t)
  | .Hole deterministic _ =>
    if deterministic then do
      let hv ← freshVar "hole"
      pure (.returnValue (.staticCall hv []), .TCore "Any")
    else
      let prod ← mkVarDecl "_havoc" (.TCore "Any") none fun hv =>
        pure (.returnValue hv)
      pure (prod, .TCore "Any")
  | _ =>
    let (v, t) ← synthValue expr
    pure (.returnValue v, t)

partial def elaborateBlock (stmts : List StmtExprMd) (expected : LowType) : ElabM FGLProducer := do
  match stmts with
  | [] => pure .unit
  | [last] => checkProducer last expected
  | stmt :: rest =>
    elaborateStmt stmt (elaborateBlock rest expected)

partial def elaborateStmt (expr : StmtExprMd) (cont : ElabM FGLProducer) : ElabM FGLProducer := do
  match expr.val with
  | .StaticCall callee args =>
    if callee.text == "PAnd" || callee.text == "POr" then do
      let (p, _) ← shortCircuit callee.text args
      pure (.seq p (← cont))
    else
      let sig ← lookupFuncSig callee.text
      match sig with
      | some s => match s.effectType with
        | .pure _ =>
          pure (← cont)
        | .error resultTy _ =>
          let checkedArgs ← checkArgs args s.params
          mkCallWithError callee.text checkedArgs (eraseType resultTy) (.TCore "Error")
            fun _rv _ev => cont
        | .stateful _ =>
          let checkedArgs ← checkArgs args s.params
          pure (.seq (.returnValue (.staticCall callee.text checkedArgs)) (← cont))
        | .statefulError resultTy _ =>
          let checkedArgs ← checkArgs args s.params
          mkCallWithError callee.text checkedArgs (eraseType resultTy) (.TCore "Error")
            fun _rv _ev => cont
      | none => pure (← cont)
  | .Assign targets value => match targets with
    | [target] =>
      let (prod, _) ← elaborateAssign target value cont
      pure prod
    | _ => cont
  | .LocalVariable nameId typeMd initOpt =>
    let ci ← elaborateInit initOpt typeMd.val
    mkVarDecl nameId.text (eraseType typeMd.val) ci fun _ => cont
  | .While cond _invs _dec body =>
    let cc ← checkValue cond .TBool
    let bp ← checkProducer body .TVoid
    pure (.whileLoop cc bp (← cont))
  | .Assert cond =>
    let cc ← checkValue cond .TBool
    pure (.assert cc (← cont))
  | .Assume cond =>
    let cc ← checkValue cond .TBool
    pure (.assume cc (← cont))
  | .Block stmts label =>
    let inner ← elaborateBlock stmts .TVoid
    let c ← cont
    pure (match label with | some l => .seq (.labeledBlock l inner) c | none => .seq inner c)
  | .Exit target => pure (.exit target)
  | .Return valueOpt =>
    let retTy := (← get).currentProcReturnType
    match valueOpt with
    | some v => let cv ← checkValue v retTy; pure (.returnValue cv)
    | none => pure (.returnValue .fromNone)
  | .IfThenElse cond thn els =>
    let cc ← checkValue cond .TBool
    let tp ← checkProducer thn .TVoid
    let ep ← match els with | some e => checkProducer e .TVoid | none => pure .unit
    pure (.seq (.ifThenElse cc tp ep) (← cont))
  | .Hole deterministic _ =>
    if deterministic then do
      let hv ← freshVar "hole"
      pure (.seq (.returnValue (.staticCall hv [])) (← cont))
    else
      mkVarDecl "_havoc" (.TCore "Any") none fun _ => cont
  | _ => cont

partial def elaborateAssign (target value : StmtExprMd) (cont : ElabM FGLProducer) : ElabM (FGLProducer × LowType) := do
  let targetTy ← match target.val with
    | .Identifier id => match (← lookupEnv id.text) with | some (.variable t) => pure t | _ => pure (.TCore "Any")
    | _ => pure (.TCore "Any")
  let (tv, _) ← synthValue target
  match value.val with
  | .Hole false _ =>
    let prod ← mkVarDecl "_havoc" (eraseType targetTy) none fun hv => do
      pure (.assign tv hv (← cont))
    pure (prod, .TVoid)
  | .Hole true _ =>
    let hv ← freshVar "hole"
    let name := match target.val with | .Identifier id => id.text | _ => "_unknown"
    let prod ← mkVarDecl name (eraseType targetTy) (some (.staticCall hv [])) fun _ => cont
    pure (prod, .TVoid)
  | .StaticCall callee args =>
    let sig ← lookupFuncSig callee.text
    match sig with
    | some s => match s.effectType with
      | .error resultTy _ =>
        let checkedArgs ← checkArgs args s.params
        let prod ← mkCallWithError callee.text checkedArgs (eraseType resultTy) (.TCore "Error")
          fun rv _ev => do
            let coerced := applySubsume rv (eraseType resultTy) (eraseType targetTy)
            pure (.assign tv coerced (← cont))
        pure (prod, .TVoid)
      | .statefulError resultTy _ =>
        let checkedArgs ← checkArgs args s.params
        let prod ← mkCallWithError callee.text checkedArgs (eraseType resultTy) (.TCore "Error")
          fun rv _ev => do
            let coerced := applySubsume rv (eraseType resultTy) (eraseType targetTy)
            pure (.assign tv coerced (← cont))
        pure (prod, .TVoid)
      | _ =>
        let cr ← checkValue value targetTy
        pure (.assign tv cr (← cont), .TVoid)
    | none =>
      let cr ← checkValue value targetTy
      pure (.assign tv cr (← cont), .TVoid)
  | _ =>
    let cr ← checkValue value targetTy
    pure (.assign tv cr (← cont), .TVoid)

partial def elaborateInit (initOpt : Option StmtExprMd) (declTy : HighType) : ElabM (Option FGLValue) := do
  match initOpt with
  | some ⟨.Hole false _, _⟩ => pure none
  | some ⟨.Hole true _, _⟩ => do let hv ← freshVar "hole"; pure (some (.staticCall hv []))
  | some i => do let v ← checkValue i declTy; pure (some v)
  | none => pure none

partial def shortCircuit (op : String) (args : List StmtExprMd) : ElabM (FGLProducer × LowType) := do
  match args with
  | [a, b] =>
    let av ← checkValue a (.TCore "Any")
    let bv ← checkValue b (.TCore "Any")
    let cond := FGLValue.staticCall "Any_to_bool" [av]
    if op == "PAnd" then
      pure (.ifThenElse cond (.returnValue bv) (.returnValue av), .TCore "Any")
    else
      pure (.ifThenElse cond (.returnValue av) (.returnValue bv), .TCore "Any")
  | _ => pure (.unit, .TCore "Any")

end

-- ═══════════════════════════════════════════════════════════════════════════
-- Projection (Architecture §"Projection: Effect Calculus → Impure Language")
-- Trivial catamorphism. Forget polarity. No restructuring.
-- ═══════════════════════════════════════════════════════════════════════════

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
  | .assign target val body =>
    [mkLaurel md (.Assign [projectValue md target] (projectValue md val))] ++ projectProducer md body
  | .varDecl name ty init body =>
    let projInit := init.map (projectValue md)
    [mkLaurel md (.LocalVariable (Identifier.mk name none) (mkHighTypeMd md (liftType ty)) projInit)] ++ projectProducer md body
  | .ifThenElse cond thn els =>
    [mkLaurel md (.IfThenElse (projectValue md cond)
      (mkLaurel md (.Block (projectProducer md thn) none))
      (some (mkLaurel md (.Block (projectProducer md els) none))))]
  | .whileLoop cond body after =>
    [mkLaurel md (.While (projectValue md cond) [] none (mkLaurel md (.Block (projectProducer md body) none)))] ++ projectProducer md after
  | .assert cond body => [mkLaurel md (.Assert (projectValue md cond))] ++ projectProducer md body
  | .assume cond body => [mkLaurel md (.Assume (projectValue md cond))] ++ projectProducer md body
  | .callWithError callee args rv ev rTy _eTy body =>
    let call := mkLaurel md (.StaticCall (Identifier.mk callee none) (args.map (projectValue md)))
    let rvTarget := mkLaurel md (.Identifier (Identifier.mk rv none))
    let evTarget := mkLaurel md (.Identifier (Identifier.mk ev none))
    let rvDecl := mkLaurel md (.LocalVariable (Identifier.mk rv none) (mkHighTypeMd md (liftType rTy)) (some (mkLaurel md (.Hole))))
    let evDecl := mkLaurel md (.LocalVariable (Identifier.mk ev none) (mkHighTypeMd md (.TCore "Error")) (some (mkLaurel md (.Hole))))
    let multiAssign := mkLaurel md (.Assign [rvTarget, evTarget] call)
    [rvDecl, evDecl, multiAssign] ++ projectProducer md body
  | .exit label => [mkLaurel md (.Exit label)]
  | .labeledBlock label body => [mkLaurel md (.Block (projectProducer md body) (some label))]
  | .seq first second => projectProducer md first ++ projectProducer md second
  | .unit => []
end

-- ═══════════════════════════════════════════════════════════════════════════
-- Pipeline Entry (Architecture §"The Pipeline")
-- ═══════════════════════════════════════════════════════════════════════════

def projectBody (md : Imperative.MetaData Core.Expression) (prod : FGLProducer) : StmtExprMd :=
  mkLaurel md (.Block (projectProducer md prod) none)

def fullElaborate (typeEnv : TypeEnv) (program : Laurel.Program) : Except String Laurel.Program := do
  let mut procs : List Laurel.Procedure := []
  for proc in program.staticProcedures do
    match proc.body with
    | .Transparent bodyExpr =>
      let retTy : HighType := .TCore "Any"
      let st : ElabState := { freshCounter := 0, currentProcReturnType := retTy }
      let extEnv := (proc.inputs ++ proc.outputs).foldl
        (fun env p => { env with names := env.names.insert p.name.text (.variable p.type.val) }) typeEnv
      let (fgl, _) := (checkProducer bodyExpr (eraseType retTy)).run extEnv |>.run st
      procs := procs ++ [{ proc with body := .Transparent (projectBody bodyExpr.md fgl) }]
    | _ => procs := procs ++ [proc]
  let compositeType : TypeDefinition := .Datatype { name := "Composite", typeArgs := [], constructors := [{ name := "MkComposite", args := [{ name := "ref", type := ⟨.TInt, #[]⟩ }] }] }
  pure { program with staticProcedures := procs, types := [compositeType] ++ program.types }

end
end Strata.FineGrainLaurel
