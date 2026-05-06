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

-- Smart constructors (the ONLY way to build AST nodes)

def mkLaurel (md : Imperative.MetaData Core.Expression) (e : StmtExpr) : StmtExprMd :=
  { val := e, md := md }

def mkHighTypeMd (md : Imperative.MetaData Core.Expression) (ty : HighType) : HighTypeMd :=
  { val := ty, md := md }

-- LowType (no UserDefined — erased to Composite)

inductive LowType where
  | TInt | TBool | TString | TFloat64 | TVoid
  | TCore (name : String)
  deriving Inhabited, Repr, BEq

def eraseType : HighType → LowType
  | .TInt => .TInt
  | .TBool => .TBool
  | .TString => .TString
  | .TFloat64 => .TFloat64
  | .TVoid => .TVoid
  | .TCore name => .TCore name
  | .UserDefined _ => .TCore "Composite"
  | .THeap => .TCore "Heap"
  | .TReal => .TCore "real"
  | .TTypedField _ => .TCore "Field"
  | .TSet _ => .TCore "Any"
  | .TMap _ _ => .TCore "Any"
  | .Applied _ _ => .TCore "Any"
  | .Pure _ => .TCore "Composite"
  | .Intersection _ => .TCore "Any"
  | .Unknown => .TCore "Any"

def liftType : LowType → HighType
  | .TInt => .TInt
  | .TBool => .TBool
  | .TString => .TString
  | .TFloat64 => .TFloat64
  | .TVoid => .TVoid
  | .TCore name => .TCore name

-- FGL Value (inert terms — pure calls, literals, variables, coercions)

inductive FGLValue where
  | litInt (n : Int)
  | litBool (b : Bool)
  | litString (s : String)
  | var (name : String)
  | fromInt (inner : FGLValue)
  | fromStr (inner : FGLValue)
  | fromBool (inner : FGLValue)
  | fromFloat (inner : FGLValue)
  | fromComposite (inner : FGLValue)
  | fromListAny (inner : FGLValue)
  | fromDictStrAny (inner : FGLValue)
  | fromNone
  | fieldAccess (obj : FGLValue) (field : String)
  | staticCall (name : String) (args : List FGLValue)
  deriving Inhabited

-- FGL Producer (effectful terms — only hasErrorOutput calls, control flow, mutation)

inductive FGLProducer where
  | returnValue (v : FGLValue)
  | assign (target : FGLValue) (val : FGLValue) (body : FGLProducer)
  | varDecl (name : String) (ty : LowType) (init : FGLValue) (body : FGLProducer)
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

-- Monad

structure ElabState where
  freshCounter : Nat := 0
  currentProcReturnType : HighType := .TCore "Any"

inductive ElabError where
  | typeError (msg : String)
  | unsupported (msg : String)
  deriving Repr, Inhabited

instance : ToString ElabError where
  toString
    | .typeError msg => s!"Elaboration type error: {msg}"
    | .unsupported msg => s!"Elaboration unsupported: {msg}"

abbrev ElabM := ReaderT TypeEnv (StateT ElabState (Except ElabError))

def freshVar (pfx : String := "tmp") : ElabM String := do
  let s ← get
  set { s with freshCounter := s.freshCounter + 1 }
  pure s!"{pfx}${s.freshCounter}"

def lookupEnv (name : String) : ElabM (Option NameInfo) := do
  pure (← read).names[name]?

def extendEnv (name : String) (ty : HighType) (action : ElabM α) : ElabM α :=
  withReader (fun env => { env with names := env.names.insert name (.variable ty) }) action

def lookupFuncSig (name : String) : ElabM (Option FuncSig) := do
  match (← read).names[name]? with
  | some (.function sig) => pure (some sig)
  | _ => pure none

-- Unified subsume: one function, three outcomes

inductive CoercionResult where
  | refl
  | coerce (witness : FGLValue → FGLValue)
  | unrelated
  deriving Inhabited

def subsume (actual expected : LowType) : CoercionResult :=
  if actual == expected then .refl
  else match actual, expected with
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

private def applySubsume (val : FGLValue) (actual expected : LowType) : FGLValue :=
  match subsume actual expected with
  | .refl => val
  | .coerce c => c val
  | .unrelated => val

-- Sequencing helper

private def sequenceProducers (first second : FGLProducer) : FGLProducer :=
  match first with
  | .unit => second
  | .assign target val .unit => .assign target val second
  | .varDecl name ty init .unit => .varDecl name ty init second
  | .assert cond .unit => .assert cond second
  | .assume cond .unit => .assume cond second
  | _ => .seq first second

-- The elaboration walk

mutual

-- Value synthesis: atoms + pure calls (hasErrorOutput=false)
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
  | .StaticCall callee args =>
    let sig ← lookupFuncSig callee.text
    if (match sig with | some s => s.hasErrorOutput | none => false) then
      throw (ElabError.unsupported "synthValue: effectful call")
    let paramTypes : List HighType := match sig with
      | some s => s.params.map (·.2)
      | none => args.map (fun _ => .TCore "Any")
    let checkedArgs ← (args.zip paramTypes).mapM fun (arg, paramTy) => checkValue arg paramTy
    let retTy := match sig with
      | some s => eraseType s.returnType
      | none => .TCore "Any"
    pure (.staticCall callee.text checkedArgs, retTy)
  | .FieldSelect obj field =>
    let (objVal, _) ← synthValue obj
    pure (.fieldAccess objVal field.text, .TCore "Any")
  | .New classId =>
    pure (.staticCall "MkComposite" [.var "$heap_nextRef", .staticCall (classId.text ++ "_TypeTag") []], .TCore "Composite")
  | _ => throw (ElabError.unsupported "synthValue: not a value form")

-- Value checking: subsumption (the only rule)
partial def checkValue (expr : StmtExprMd) (expected : HighType) : ElabM FGLValue := do
  let (val, actual) ← synthValue expr
  pure (applySubsume val actual (eraseType expected))

-- Producer synthesis
partial def synthProducer (expr : StmtExprMd) : ElabM (FGLProducer × LowType) := do
  match expr.val with
  -- Effectful StaticCall (hasErrorOutput=true) — TRUE let
  | .StaticCall callee args =>
    if callee.text == "PAnd" || callee.text == "POr" then
      shortCircuitDesugar callee.text args
    else
      let sig ← lookupFuncSig callee.text
      let isEffectful := match sig with | some s => s.hasErrorOutput | none => false
      if !isEffectful then
        -- Pure call: elaborate as value
        let (val, ty) ← synthValue expr
        pure (.returnValue val, ty)
      else
        let paramTypes : List HighType := match sig with
          | some s => s.params.map (·.2)
          | none => args.map (fun _ => .TCore "Any")
        let retTy := match sig with
          | some s => eraseType s.returnType
          | none => .TCore "Any"
        let checkedArgs ← (args.zip paramTypes).mapM fun (arg, paramTy) => checkValue arg paramTy
        let rv ← freshVar "result"
        let ev ← freshVar "err"
        pure (.callWithError callee.text checkedArgs rv ev retTy (.TCore "Error")
               (.returnValue (.var rv)), retTy)

  -- Assign: v ⇐ Γ(x)
  | .Assign targets value =>
    match targets with
    | [target] =>
      let targetTy ← match target.val with
        | .Identifier id =>
          match (← lookupEnv id.text) with
          | some (.variable t) => pure t
          | _ => pure (.TCore "Any")
        | _ => pure (.TCore "Any")
      let (targetVal, _) ← synthValue target
      let checkedRhs ← checkValue value targetTy
      pure (.assign targetVal checkedRhs .unit, .TVoid)
    | _ => pure (.unit, .TCore "Any")

  -- LocalVariable: v ⇐ T
  | .LocalVariable nameId typeMd initOpt =>
    let checkedInit ← match initOpt with
      | some init => checkValue init typeMd.val
      | none => pure (.var "_hole")
    pure (.varDecl nameId.text (eraseType typeMd.val) checkedInit .unit, eraseType typeMd.val)

  -- While: v ⇐ bool, M ⇐ TVoid
  | .While cond _invariants _decreases body =>
    let checkedCond ← checkValue cond (.TBool)
    let bodyProd ← checkProducer body .TVoid
    pure (.whileLoop checkedCond bodyProd .unit, .TVoid)

  -- Assert: v ⇐ bool
  | .Assert condition =>
    let checkedCond ← checkValue condition (.TBool)
    pure (.assert checkedCond .unit, .TVoid)

  -- Assume: v ⇐ bool
  | .Assume condition =>
    let checkedCond ← checkValue condition (.TBool)
    pure (.assume checkedCond .unit, .TVoid)

  -- Block
  | .Block stmts label =>
    let (prod, ty) ← elaborateBlock stmts
    match label with
    | some l => pure (.labeledBlock l prod, ty)
    | none => pure (prod, ty)

  -- Exit
  | .Exit target => pure (.exit target, .TVoid)

  -- Return: v ⇐ procReturnType
  | .Return valueOpt =>
    let retTy := (← get).currentProcReturnType
    match valueOpt with
    | some v =>
      let checkedVal ← checkValue v retTy
      pure (.returnValue checkedVal, eraseType retTy)
    | none => pure (.returnValue .fromNone, .TVoid)

  -- IfThenElse is a CHECKING form. At statement level, check against TVoid.
  | .IfThenElse _ _ _ =>
    let prod ← checkProducer expr .TVoid
    pure (prod, .TVoid)

  -- FieldSelect (value form)
  | .FieldSelect _ _ =>
    let (val, ty) ← synthValue expr
    pure (.returnValue val, ty)

  -- New (value form)
  | .New _ =>
    let (val, ty) ← synthValue expr
    pure (.returnValue val, ty)

  | .Hole _ _ => pure (.returnValue (.var "_hole"), .TCore "Any")
  | _ => pure (.returnValue (.var "_unsupported"), .TCore "Any")

-- Producer checking: structural rules
partial def checkProducer (expr : StmtExprMd) (expected : LowType) : ElabM FGLProducer := do
  match expr.val with
  -- if v then M else N ⇐ C: propagate C into branches
  | .IfThenElse cond thenBranch elseBranch =>
    let checkedCond ← checkValue cond (.TBool)
    let thenProd ← checkProducer thenBranch expected
    let elsProd ← match elseBranch with
      | some e => checkProducer e expected
      | none => pure .unit
    pure (.ifThenElse checkedCond thenProd elsProd)

  -- var x:T := v; body ⇐ C: propagate C into body
  | .LocalVariable nameId typeMd initOpt =>
    let checkedInit ← match initOpt with
      | some init => checkValue init typeMd.val
      | none => pure (.var "_hole")
    let body ← extendEnv nameId.text typeMd.val (checkProducer (mkLaurel #[] (.Block [] none)) expected)
    pure (.varDecl nameId.text (eraseType typeMd.val) checkedInit body)

  -- return v ⇐ procReturnType
  | .Return valueOpt =>
    let retTy := (← get).currentProcReturnType
    match valueOpt with
    | some v =>
      let checkedVal ← checkValue v retTy
      pure (.returnValue checkedVal)
    | none => pure (.returnValue .fromNone)

  -- Fallback: synth, then subsume
  | _ =>
    let (prod, actual) ← synthProducer expr
    match subsume actual expected with
    | .refl => pure prod
    | .coerce _ =>
      let tmpVar ← freshVar "tmp"
      pure (.seq prod (.returnValue (applySubsume (.var tmpVar) actual expected)))
    | .unrelated => pure prod

-- Short-circuit: PAnd/POr
partial def shortCircuitDesugar (op : String) (args : List StmtExprMd) : ElabM (FGLProducer × LowType) := do
  match args with
  | [a, b] =>
    let aVal ← checkValue a (.TCore "Any")
    let bVal ← checkValue b (.TCore "Any")
    let condVal : FGLValue := .staticCall "Any_to_bool" [aVal]
    if op == "PAnd" then
      pure (.ifThenElse condVal (.returnValue bVal) (.returnValue aVal), .TCore "Any")
    else
      pure (.ifThenElse condVal (.returnValue aVal) (.returnValue bVal), .TCore "Any")
  | _ =>
    let argVals ← args.mapM (fun a => checkValue a (.TCore "Any"))
    pure (.returnValue (.staticCall op argVals), .TCore "Any")

-- Block elaboration: sequence stmts, extend Γ at binding sites
partial def elaborateBlock (stmts : List StmtExprMd) : ElabM (FGLProducer × LowType) := do
  match stmts with
  | [] => pure (.unit, .TVoid)
  | [last] => synthProducer last
  | stmt :: rest =>
    let (firstProd, _) ← synthProducer stmt
    let elaborateRest := elaborateBlock rest
    let (restProd, restTy) ← match stmt.val with
      | .LocalVariable nameId typeMd _ => extendEnv nameId.text typeMd.val elaborateRest
      | _ => elaborateRest
    pure (sequenceProducers firstProd restProd, restTy)

end -- mutual

-- Projection: trivial cata

mutual

partial def projectValue (md : Imperative.MetaData Core.Expression) : FGLValue → StmtExprMd
  | .litInt n => mkLaurel md (.LiteralInt n)
  | .litBool b => mkLaurel md (.LiteralBool b)
  | .litString s => mkLaurel md (.LiteralString s)
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
  | .varDecl name _ty init body =>
    let initExpr := projectValue md init
    let decl := mkLaurel md (.LocalVariable (Identifier.mk name none) (mkHighTypeMd md (.TCore "Any")) (some initExpr))
    [decl] ++ projectProducer md body
  | .ifThenElse cond thn els =>
    let thnBlock := mkLaurel md (.Block (projectProducer md thn) none)
    let elsBlock := mkLaurel md (.Block (projectProducer md els) none)
    [mkLaurel md (.IfThenElse (projectValue md cond) thnBlock (some elsBlock))]
  | .whileLoop cond body after =>
    let bodyBlock := mkLaurel md (.Block (projectProducer md body) none)
    [mkLaurel md (.While (projectValue md cond) [] none bodyBlock)] ++ projectProducer md after
  | .assert cond body =>
    [mkLaurel md (.Assert (projectValue md cond))] ++ projectProducer md body
  | .assume cond body =>
    [mkLaurel md (.Assume (projectValue md cond))] ++ projectProducer md body
  | .callWithError callee args rv ev rTy _eTy body =>
    let callExpr := mkLaurel md (.StaticCall (Identifier.mk callee none) (args.map (projectValue md)))
    let rvDecl := mkLaurel md (.LocalVariable (Identifier.mk rv none) (mkHighTypeMd md (.TCore "Any")) (some callExpr))
    let evDecl := mkLaurel md (.LocalVariable (Identifier.mk ev none) (mkHighTypeMd md (liftType rTy)) (some (mkLaurel md (.StaticCall (Identifier.mk "NoError" none) []))))
    [rvDecl, evDecl] ++ projectProducer md body
  | .exit label => [mkLaurel md (.Exit label)]
  | .labeledBlock label body =>
    [mkLaurel md (.Block (projectProducer md body) (some label))]
  | .seq first second => projectProducer md first ++ projectProducer md second
  | .unit => []

end -- mutual (projection)

def projectBody (md : Imperative.MetaData Core.Expression) (prod : FGLProducer) : StmtExprMd :=
  mkLaurel md (.Block (projectProducer md prod) none)

-- Entry point

def fullElaborate (typeEnv : Strata.Python.Resolution.TypeEnv)
    (program : Strata.Laurel.Program) : Except String Strata.Laurel.Program := do
  let mut procs : List Strata.Laurel.Procedure := []
  for proc in program.staticProcedures do
    match proc.body with
    | .Transparent bodyExpr =>
      let retTy := match proc.outputs with
        | [p] => p.type.val
        | _ => .TCore "Any"
      let initState : ElabState := { freshCounter := 0, currentProcReturnType := retTy }
      match (synthProducer bodyExpr).run typeEnv |>.run initState with
      | .ok ((fglProd, _), _) =>
        let projected := projectBody bodyExpr.md fglProd
        procs := procs ++ [{ proc with body := .Transparent projected }]
      | .error _ =>
        procs := procs ++ [proc]
    | _ => procs := procs ++ [proc]
  pure { program with staticProcedures := procs }

end -- public section

end Strata.FineGrainLaurel
