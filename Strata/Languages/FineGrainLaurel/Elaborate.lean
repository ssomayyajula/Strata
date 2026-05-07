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
  | seq (first : FGLProducer) (second : FGLProducer)
  | unit
  deriving Inhabited

-- Monad

structure ElabState where
  freshCounter : Nat := 0

abbrev ElabM := ReaderT TypeEnv (StateT ElabState Option)

private def freshVar (pfx : String := "tmp") : ElabM String := do
  let s ← get; set { s with freshCounter := s.freshCounter + 1 }; pure s!"{pfx}${s.freshCounter}"

def lookupEnv (name : String) : ElabM (Option NameInfo) := do pure (← read).names[name]?
def extendEnv (name : String) (ty : HighType) (action : ElabM α) : ElabM α :=
  withReader (fun env => { env with names := env.names.insert name (.variable ty) }) action
def lookupFuncSig (name : String) : ElabM (Option FuncSig) := do
  match (← read).names[name]? with | some (.function sig) => pure (some sig) | _ => pure none

-- ElabResult: dependent on grade

@[expose] def ElabResult : Grade → Type
  | .pure => FGLProducer
  | .err => FGLProducer
  | .heap => FGLValue → ElabM FGLProducer
  | .heapErr => FGLValue → ElabM FGLProducer

-- HOAS

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

-- Subsumption (value-level coercions)

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

-- ElabResult helpers

def pureResult (g : Grade) : ElabM (ElabResult g) :=
  match g with
  | .pure => pure FGLProducer.unit
  | .err => pure FGLProducer.unit
  | .heap => pure (fun _ => pure FGLProducer.unit)
  | .heapErr => pure (fun _ => pure FGLProducer.unit)

def joinIfElse (g : Grade) (cond : FGLValue) (thn els : ElabResult g) : ElabResult g :=
  match g with
  | .pure => .ifThenElse cond thn els
  | .err => .ifThenElse cond thn els
  | .heap => fun h => do pure (.ifThenElse cond (← thn h) (← els h))
  | .heapErr => fun h => do pure (.ifThenElse cond (← thn h) (← els h))

def applyResult (d e : Grade) (result : ElabResult d) : ElabM (ElabResult e) :=
  match d, e with
  | .pure, .pure => pure result
  | .pure, .err => pure result
  | .pure, .heap => pure (fun _ => pure result)
  | .pure, .heapErr => pure (fun _ => pure result)
  | .err, .err => pure result
  | .err, .heapErr => pure (fun _ => pure result)
  | .heap, .heap => pure result
  | .heap, .heapErr => pure result
  | .heapErr, .heapErr => pure result
  | _, _ => failure

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
    pure (.fieldAccess ov field.text, .TCore "Any")
  | .StaticCall callee args =>
    let sig ← lookupFuncSig callee.text
    match sig with
    | some s =>
      let checkedArgs ← checkArgs args s.params
      pure (.staticCall callee.text checkedArgs, eraseType s.effectType.resultType)
    | none =>
      let checkedArgs ← args.mapM fun arg => checkValue arg (.TCore "Any")
      pure (.staticCall callee.text checkedArgs, .TCore "Any")
  | _ => pure (.var "_unknown", .TCore "Any")

partial def checkValue (expr : StmtExprMd) (expected : HighType) : ElabM FGLValue := do
  let (val, actual) ← synthValue expr
  pure (applySubsume val actual (eraseType expected))

partial def checkArgs (args : List StmtExprMd) (params : List (String × HighType)) : ElabM (List FGLValue) :=
  (args.zip (params.map (·.2))).mapM fun (arg, pty) => checkValue arg pty

partial def synthProducer (expr : StmtExprMd) : ElabM ((g : Grade) × LowType × ElabResult g) := do
  match expr.val with
  | .StaticCall callee args =>
    let sig ← lookupFuncSig callee.text
    match sig with
    | some s =>
      let checkedArgs ← checkArgs args s.params
      let retTy := eraseType s.effectType.resultType
      match s.effectType with
      | .pure _ =>
        let val := FGLValue.staticCall callee.text checkedArgs
        pure ⟨.pure, retTy, FGLProducer.returnValue val⟩
      | .error _ _ =>
        let prod ← mkEffectfulCall callee.text checkedArgs
          [("result", s.effectType.resultType), ("err", .TCore "Error")]
          fun outs => pure (.returnValue outs[0]!)
        pure ⟨.err, retTy, prod⟩
      | .stateful _ =>
        let closure : FGLValue → ElabM FGLProducer := fun heap =>
          mkEffectfulCall callee.text (heap :: checkedArgs)
            [("heap", .THeap), ("result", s.effectType.resultType)]
            fun outs => pure (.returnValue outs[1]!)
        pure ⟨.heap, retTy, closure⟩
      | .statefulError _ _ =>
        let closure : FGLValue → ElabM FGLProducer := fun heap =>
          mkEffectfulCall callee.text (heap :: checkedArgs)
            [("heap", .THeap), ("result", s.effectType.resultType), ("err", .TCore "Error")]
            fun outs => pure (.returnValue outs[1]!)
        pure ⟨.heapErr, retTy, closure⟩
    | none =>
      let (val, ty) ← synthValue expr
      pure ⟨.pure, ty, FGLProducer.returnValue val⟩
  | .New classId =>
    let closure : FGLValue → ElabM FGLProducer := fun heap => do
      let ref := FGLValue.staticCall "Heap..nextReference!" [heap]
      let newHeap := FGLValue.staticCall "increment" [heap]
      let obj := FGLValue.staticCall "MkComposite" [ref, .staticCall (classId.text ++ "_TypeTag") []]
      pure (.assign (.var "$heap") newHeap (.returnValue obj))
    pure ⟨.heap, .TCore "Composite", closure⟩
  | .Assign targets value => match targets with
    | [target] =>
      let targetTy ← match target.val with
        | .Identifier id => match (← lookupEnv id.text) with | some (.variable t) => pure t | _ => pure (.TCore "Any")
        | _ => pure (.TCore "Any")
      let (tv, _) ← synthValue target
      let cr ← checkValue value targetTy
      pure ⟨.pure, .TVoid, FGLProducer.assign tv cr .unit⟩
    | _ => pure ⟨.pure, .TVoid, FGLProducer.unit⟩
  | .LocalVariable nameId typeMd initOpt =>
    let ci ← match initOpt with
      | some ⟨.Hole false _, _⟩ => pure none
      | some ⟨.Hole true _, _⟩ => do let hv ← freshVar "hole"; pure (some (.staticCall hv []))
      | some i => do let v ← checkValue i typeMd.val; pure (some v)
      | none => pure none
    let prod ← mkVarDecl nameId.text (eraseType typeMd.val) ci fun _ => pure .unit
    pure ⟨.pure, .TVoid, prod⟩
  | .Assert cond => let cc ← checkValue cond .TBool; pure ⟨.pure, .TVoid, .assert cc .unit⟩
  | .Assume cond => let cc ← checkValue cond .TBool; pure ⟨.pure, .TVoid, .assume cc .unit⟩
  | .Exit target => pure ⟨.pure, .TVoid, .exit target⟩
  | .Block stmts label =>
    -- Synth a block: just check at heapErr (top grade, always works)
    let prod ← checkProducer (⟨.Block stmts label, expr.md⟩) .TVoid .heapErr
    pure ⟨.heapErr, .TVoid, prod⟩
  | _ =>
    let (v, t) ← synthValue expr
    pure ⟨.pure, t, FGLProducer.returnValue v⟩

partial def checkProducer (expr : StmtExprMd) (expected : LowType) (grade : Grade) : ElabM (ElabResult grade) := do
  match expr.val with
  | .IfThenElse cond thn els =>
    let cc ← checkValue cond .TBool
    let tp ← checkProducer thn expected grade
    let ep ← match els with | some e => checkProducer e expected grade | none => pureResult grade
    pure (joinIfElse grade cc tp ep)
  | .Return valueOpt =>
    match valueOpt with
    | some v => let cv ← checkValue v (liftType expected); pureResult grade
    | none => pureResult grade
  | .Block stmts label =>
    elaborateBlock stmts expected grade
  | _ =>
    -- Subsumption: synth, check grade admissible
    let ⟨d, _, result⟩ ← synthProducer expr
    applyResult d grade result

partial def elaborateBlock (stmts : List StmtExprMd) (expected : LowType) (grade : Grade) : ElabM (ElabResult grade) := do
  match stmts with
  | [] => pureResult grade
  | [last] => checkProducer last expected grade
  | stmt :: rest =>
    let ⟨d, _, result⟩ ← synthProducer stmt
    match Grade.residual d grade with
    | some restGrade => sorry -- TODO: sequence result with elaborateBlock rest
    | none => failure

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
  | .seq first second => projectProducer md first ++ projectProducer md second
  | .unit => []
end

def projectBody (md : Imperative.MetaData Core.Expression) (prod : FGLProducer) : StmtExprMd :=
  mkLaurel md (.Block (projectProducer md prod) none)

-- fullElaborate (stub for now — need to resolve sorry in elaborateBlock)

def fullElaborate (typeEnv : TypeEnv) (program : Laurel.Program) : Except String Laurel.Program := do
  pure program

end
end Strata.FineGrainLaurel
