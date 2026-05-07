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

-- Types

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
  | seq (first : FGLProducer) (second : FGLProducer)
  | unit
  deriving Inhabited

-- Monad (no heapVar — heap flows through function parameters)

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
    (fun (n, ty) acc => extendEnv n ty acc)
    (body vars)
  pure (.effectfulCall callee args lowOutputs cont)

def mkVarDecl (name : String) (ty : LowType) (init : Option FGLValue)
    (body : FGLValue → ElabM FGLProducer) : ElabM FGLProducer := do
  let cont ← extendEnv name (liftType ty) (body (.var name))
  pure (.varDecl name ty init cont)

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

-- Effectful call builder (DRY: one function for all effect types)
-- Takes the current heap (if any), builds args + outputs, calls mkEffectfulCall,
-- returns (producer, resultValue, newHeap)

def buildEffectfulCall (callee : String) (checkedArgs : List FGLValue)
    (effectType : EffectType) (heap : Option FGLValue)
    (k : FGLValue → Option FGLValue → ElabM FGLProducer) : ElabM FGLProducer := do
  let args := match heap with | some h => h :: checkedArgs | none => checkedArgs
  let heapOut := match heap with | some _ => [("heap", HighType.THeap)] | none => []
  let resultOut := [("result", effectType.resultType)]
  let errOut := match effectType with
    | .error _ e | .statefulError _ e => [("err", e)]
    | _ => []
  let outputs := heapOut ++ resultOut ++ errOut
  mkEffectfulCall callee args outputs fun outs =>
    let newHeap := if heap.isSome then some outs[0]! else none
    let resultIdx := if heap.isSome then 1 else 0
    k outs[resultIdx]! newHeap

-- Elaboration
-- The heap flows through function parameters: `heap : Option FGLValue`.
-- Each function that touches the heap receives it and produces a new one.
-- No mutable state. Pure threading through the CPS structure.

mutual

partial def synthValue (heap : Option FGLValue) (expr : StmtExprMd) : ElabM (FGLValue × LowType) := do
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
    let (ov, _) ← synthValue heap obj
    match heap with
    | some h =>
      let read := FGLValue.staticCall "readField" [h, ov, .staticCall field.text []]
      pure (.staticCall "Box..AnyVal!" [read], .TCore "Any")
    | none => pure (.fieldAccess ov field.text, .TCore "Any")
  | .StaticCall callee args =>
    let sig ← lookupFuncSig callee.text
    match sig with
    | some s => match s.effectType with
      | .pure ty =>
        let checkedArgs ← checkArgs heap args s.params
        pure (.staticCall callee.text checkedArgs, eraseType ty)
      | _ => pure (.var callee.text, .TCore "Any")
    | none =>
      let checkedArgs ← args.mapM fun arg => checkValue heap arg (.TCore "Any")
      pure (.staticCall callee.text checkedArgs, .TCore "Any")
  | _ => pure (.var "_unknown", .TCore "Any")

partial def checkValue (heap : Option FGLValue) (expr : StmtExprMd) (expected : HighType) : ElabM FGLValue := do
  let (val, actual) ← synthValue heap expr
  pure (applySubsume val actual (eraseType expected))

partial def checkArgs (heap : Option FGLValue) (args : List StmtExprMd) (params : List (String × HighType)) : ElabM (List FGLValue) :=
  (args.zip (params.map (·.2))).mapM fun (arg, pty) => checkValue heap arg pty

partial def checkProducer (heap : Option FGLValue) (expr : StmtExprMd) (expected : LowType) : ElabM FGLProducer := do
  match expr.val with
  | .IfThenElse cond thn els =>
    let cc ← checkValue heap cond .TBool
    let tp ← checkProducer heap thn expected
    let ep ← match els with | some e => checkProducer heap e expected | none => pure .unit
    pure (.ifThenElse cc tp ep)
  | .Return valueOpt =>
    let retTy := (← get).currentProcReturnType
    match valueOpt with
    | some v => let cv ← checkValue heap v retTy; pure (.returnValue cv)
    | none => pure (.returnValue .fromNone)
  | .Block stmts label =>
    let prod ← elaborateBlock heap stmts expected
    pure (match label with | some l => .labeledBlock l prod | none => prod)
  | _ =>
    let (prod, _) ← synthProducer heap expr
    pure prod

partial def synthProducer (heap : Option FGLValue) (expr : StmtExprMd) : ElabM (FGLProducer × LowType) := do
  match expr.val with
  | .StaticCall callee args =>
    if callee.text == "PAnd" || callee.text == "POr" then
      shortCircuit heap callee.text args
    else
      let sig ← lookupFuncSig callee.text
      match sig with
      | some s =>
        let checkedArgs ← checkArgs heap args s.params
        match s.effectType with
        | .pure _ =>
          let (val, ty) ← synthValue heap expr
          pure (.returnValue val, ty)
        | .error resultTy _ =>
          let prod ← buildEffectfulCall callee.text checkedArgs s.effectType none
            fun rv _newHeap => pure (.returnValue rv)
          pure (prod, eraseType resultTy)
        | .stateful resultTy =>
          let prod ← buildEffectfulCall callee.text checkedArgs s.effectType heap
            fun rv _newHeap => pure (.returnValue rv)
          pure (prod, eraseType resultTy)
        | .statefulError resultTy _ =>
          let prod ← buildEffectfulCall callee.text checkedArgs s.effectType heap
            fun rv _newHeap => pure (.returnValue rv)
          pure (prod, eraseType resultTy)
      | none =>
        let (val, ty) ← synthValue heap expr
        pure (.returnValue val, ty)
  | .New classId =>
    match heap with
    | some h =>
      let ref := FGLValue.staticCall "Heap..nextReference!" [h]
      let newHeap := FGLValue.staticCall "increment" [h]
      let obj := FGLValue.staticCall "MkComposite" [ref, .staticCall (classId.text ++ "_TypeTag") []]
      -- assign $heap := newHeap, then return obj
      pure (.assign (.var "$heap") newHeap (.returnValue obj), .TCore "Composite")
    | none =>
      let prod ← mkEffectfulCall (classId.text ++ "@new") []
        [("obj", .UserDefined (Identifier.mk classId.text none))]
        fun outs => pure (.returnValue outs[0]!)
      pure (prod, .TCore "Composite")
  | .Assign targets value => match targets with
    | [target] => elaborateAssign heap target value (pure .unit)
    | _ => pure (.unit, .TVoid)
  | .LocalVariable nameId typeMd initOpt =>
    let ci ← elaborateInit heap initOpt typeMd.val
    let prod ← mkVarDecl nameId.text (eraseType typeMd.val) ci fun _ => pure .unit
    pure (prod, .TVoid)
  | .While cond _invs _dec body =>
    let cc ← checkValue heap cond .TBool
    let bp ← checkProducer heap body .TVoid
    pure (.whileLoop cc bp .unit, .TVoid)
  | .Assert cond =>
    let cc ← checkValue heap cond .TBool
    pure (.assert cc .unit, .TVoid)
  | .Assume cond =>
    let cc ← checkValue heap cond .TBool
    pure (.assume cc .unit, .TVoid)
  | .Block stmts label =>
    let prod ← elaborateBlock heap stmts .TVoid
    pure (match label with | some l => (.labeledBlock l prod, .TVoid) | none => (prod, .TVoid))
  | .Exit target => pure (.exit target, .TVoid)
  | .Return valueOpt =>
    let retTy := (← get).currentProcReturnType
    match valueOpt with
    | some v => let cv ← checkValue heap v retTy; pure (.returnValue cv, eraseType retTy)
    | none => pure (.returnValue .fromNone, .TVoid)
  | .IfThenElse _ _ _ =>
    let p ← checkProducer heap expr .TVoid
    pure (p, .TVoid)
  | .FieldSelect _ _ =>
    let (v, t) ← synthValue heap expr
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
    let (v, t) ← synthValue heap expr
    pure (.returnValue v, t)

partial def elaborateBlock (heap : Option FGLValue) (stmts : List StmtExprMd) (expected : LowType) : ElabM FGLProducer := do
  match stmts with
  | [] => pure .unit
  | [last] => checkProducer heap last expected
  | stmt :: rest => elaborateStmt heap stmt (elaborateBlock heap rest expected)

partial def elaborateStmt (heap : Option FGLValue) (expr : StmtExprMd) (cont : ElabM FGLProducer) : ElabM FGLProducer := do
  match expr.val with
  | .StaticCall callee args =>
    if callee.text == "PAnd" || callee.text == "POr" then do
      let (p, _) ← shortCircuit heap callee.text args
      pure (.seq p (← cont))
    else
      let sig ← lookupFuncSig callee.text
      match sig with
      | some s =>
        let checkedArgs ← checkArgs heap args s.params
        match s.effectType with
        | .pure _ => cont
        | .error _ _ =>
          buildEffectfulCall callee.text checkedArgs s.effectType none
            fun _rv _newHeap => cont
        | .stateful _ =>
          buildEffectfulCall callee.text checkedArgs s.effectType heap
            fun _rv _newHeap => cont
        | .statefulError _ _ =>
          buildEffectfulCall callee.text checkedArgs s.effectType heap
            fun _rv _newHeap => cont
      | none => cont
  | .Assign targets value => match targets with
    | [target] =>
      let (prod, _) ← elaborateAssign heap target value cont
      pure prod
    | _ => cont
  | .LocalVariable nameId typeMd initOpt =>
    let ci ← elaborateInit heap initOpt typeMd.val
    mkVarDecl nameId.text (eraseType typeMd.val) ci fun _ => cont
  | .While cond _invs _dec body =>
    let cc ← checkValue heap cond .TBool
    let bp ← checkProducer heap body .TVoid
    pure (.whileLoop cc bp (← cont))
  | .Assert cond =>
    let cc ← checkValue heap cond .TBool
    pure (.assert cc (← cont))
  | .Assume cond =>
    let cc ← checkValue heap cond .TBool
    pure (.assume cc (← cont))
  | .Block stmts label =>
    let inner ← elaborateBlock heap stmts .TVoid
    let c ← cont
    pure (match label with | some l => .seq (.labeledBlock l inner) c | none => .seq inner c)
  | .Exit target => pure (.exit target)
  | .Return valueOpt =>
    let retTy := (← get).currentProcReturnType
    match valueOpt with
    | some v => let cv ← checkValue heap v retTy; pure (.returnValue cv)
    | none => pure (.returnValue .fromNone)
  | .IfThenElse cond thn els =>
    let cc ← checkValue heap cond .TBool
    let tp ← checkProducer heap thn .TVoid
    let ep ← match els with | some e => checkProducer heap e .TVoid | none => pure .unit
    pure (.seq (.ifThenElse cc tp ep) (← cont))
  | .Hole deterministic _ =>
    if deterministic then do
      let hv ← freshVar "hole"
      pure (.seq (.returnValue (.staticCall hv [])) (← cont))
    else
      mkVarDecl "_havoc" (.TCore "Any") none fun _ => cont
  | _ => cont

partial def elaborateAssign (heap : Option FGLValue) (target value : StmtExprMd) (cont : ElabM FGLProducer) : ElabM (FGLProducer × LowType) := do
  let targetTy ← match target.val with
    | .Identifier id => match (← lookupEnv id.text) with | some (.variable t) => pure t | _ => pure (.TCore "Any")
    | _ => pure (.TCore "Any")
  let (tv, _) ← synthValue heap target
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
  | .New classId =>
    match heap with
    | some h =>
      let ref := FGLValue.staticCall "Heap..nextReference!" [h]
      let newHeap := FGLValue.staticCall "increment" [h]
      let obj := FGLValue.staticCall "MkComposite" [ref, .staticCall (classId.text ++ "_TypeTag") []]
      let c ← cont
      pure (.assign (.var "$heap") newHeap (.assign tv obj c), .TVoid)
    | none =>
      let prod ← mkEffectfulCall (classId.text ++ "@new") []
        [("obj", .UserDefined (Identifier.mk classId.text none))]
        fun outs => do
          let coerced := applySubsume outs[0]! (.TCore "Composite") (eraseType targetTy)
          pure (.assign tv coerced (← cont))
      pure (prod, .TVoid)
  | .StaticCall callee args =>
    let sig ← lookupFuncSig callee.text
    match sig with
    | some s => match s.effectType with
      | .pure _ =>
        let cr ← checkValue heap value targetTy
        pure (.assign tv cr (← cont), .TVoid)
      | .error _ _ =>
        let checkedArgs ← checkArgs heap args s.params
        let prod ← buildEffectfulCall callee.text checkedArgs s.effectType none
          fun rv _newHeap => do
            let coerced := applySubsume rv (eraseType s.effectType.resultType) (eraseType targetTy)
            pure (.assign tv coerced (← cont))
        pure (prod, .TVoid)
      | .stateful _ =>
        let checkedArgs ← checkArgs heap args s.params
        let prod ← buildEffectfulCall callee.text checkedArgs s.effectType heap
          fun rv _newHeap => do
            let coerced := applySubsume rv (eraseType s.effectType.resultType) (eraseType targetTy)
            pure (.assign tv coerced (← cont))
        pure (prod, .TVoid)
      | .statefulError _ _ =>
        let checkedArgs ← checkArgs heap args s.params
        let prod ← buildEffectfulCall callee.text checkedArgs s.effectType heap
          fun rv _newHeap => do
            let coerced := applySubsume rv (eraseType s.effectType.resultType) (eraseType targetTy)
            pure (.assign tv coerced (← cont))
        pure (prod, .TVoid)
    | none =>
      let cr ← checkValue heap value targetTy
      pure (.assign tv cr (← cont), .TVoid)
  | _ =>
    let cr ← checkValue heap value targetTy
    pure (.assign tv cr (← cont), .TVoid)

partial def elaborateInit (heap : Option FGLValue) (initOpt : Option StmtExprMd) (declTy : HighType) : ElabM (Option FGLValue) := do
  match initOpt with
  | some ⟨.Hole false _, _⟩ => pure none
  | some ⟨.Hole true _, _⟩ => do let hv ← freshVar "hole"; pure (some (.staticCall hv []))
  | some i => do let v ← checkValue heap i declTy; pure (some v)
  | none => pure none

partial def shortCircuit (heap : Option FGLValue) (op : String) (args : List StmtExprMd) : ElabM (FGLProducer × LowType) := do
  match args with
  | [a, b] =>
    let av ← checkValue heap a (.TCore "Any")
    let bv ← checkValue heap b (.TCore "Any")
    let cond := FGLValue.staticCall "Any_to_bool" [av]
    if op == "PAnd" then
      pure (.ifThenElse cond (.returnValue bv) (.returnValue av), .TCore "Any")
    else
      pure (.ifThenElse cond (.returnValue av) (.returnValue bv), .TCore "Any")
  | _ => pure (.unit, .TCore "Any")

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
  | .effectfulCall callee args outputs body =>
    let call := mkLaurel md (.StaticCall (Identifier.mk callee none) (args.map (projectValue md)))
    let decls := outputs.map fun (n, ty) =>
      mkLaurel md (.LocalVariable (Identifier.mk n none) (mkHighTypeMd md (liftType ty)) (some (mkLaurel md (.Hole))))
    let targets := outputs.map fun (n, _) => mkLaurel md (.Identifier (Identifier.mk n none))
    let multiAssign := mkLaurel md (.Assign targets call)
    decls ++ [multiAssign] ++ projectProducer md body
  | .exit label => [mkLaurel md (.Exit label)]
  | .labeledBlock label body => [mkLaurel md (.Block (projectProducer md body) (some label))]
  | .seq first second => projectProducer md first ++ projectProducer md second
  | .unit => []
end

-- Pipeline Entry

def projectBody (md : Imperative.MetaData Core.Expression) (prod : FGLProducer) : StmtExprMd :=
  mkLaurel md (.Block (projectProducer md prod) none)

def fullElaborate (typeEnv : TypeEnv) (program : Laurel.Program) : Except String Laurel.Program := do
  let mut procs : List Laurel.Procedure := []
  for proc in program.staticProcedures do
    match proc.body with
    | .Transparent bodyExpr =>
      let retTy : HighType := .TCore "Any"
      let st : ElabState := { freshCounter := 0, currentProcReturnType := retTy }
      let baseEnv := (proc.inputs ++ proc.outputs).foldl
        (fun env p => { env with names := env.names.insert p.name.text (.variable p.type.val) }) typeEnv
      let heap := match typeEnv.names[proc.name.text]? with
        | some (.function sig) => match sig.effectType with
          | .stateful _ | .statefulError _ _ => some (FGLValue.var "$heap")
          | _ => none
        | _ => none
      match heap with
      | some h =>
        let extEnv := { baseEnv with names := baseEnv.names.insert "$heap_in" (.variable .THeap) |>.insert "$heap" (.variable .THeap) }
        let (fglRaw, _) := (checkProducer (some h) bodyExpr (eraseType retTy)).run extEnv |>.run st
        let fgl := FGLProducer.assign (.var "$heap") (.var "$heap_in") fglRaw
        let heapTy : HighTypeMd := ⟨.THeap, #[]⟩
        let heapIn : Laurel.Parameter := { name := Identifier.mk "$heap_in" none, type := heapTy }
        let heapOut : Laurel.Parameter := { name := Identifier.mk "$heap" none, type := heapTy }
        procs := procs ++ [{ proc with inputs := heapIn :: proc.inputs, outputs := heapOut :: proc.outputs, body := .Transparent (projectBody bodyExpr.md fgl) }]
      | none =>
        let (fgl, _) := (checkProducer none bodyExpr (eraseType retTy)).run baseEnv |>.run st
        procs := procs ++ [{ proc with body := .Transparent (projectBody bodyExpr.md fgl) }]
    | _ => procs := procs ++ [proc]
  let hasStateful := procs.any fun p => p.inputs.any fun i => i.name.text == "$heap_in"
  let compositeType : TypeDefinition := .Datatype { name := "Composite", typeArgs := [], constructors := [{ name := "MkComposite", args := [{ name := "ref", type := ⟨.TInt, #[]⟩ }] }] }
  match hasStateful with
  | true =>
    pure { program with
      staticProcedures := heapConstants.staticProcedures ++ procs,
      types := heapConstants.types ++ [compositeType] ++ program.types }
  | false =>
    pure { program with
      staticProcedures := procs,
      types := [compositeType] ++ program.types }

end
end Strata.FineGrainLaurel
