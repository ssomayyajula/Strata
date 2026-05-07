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

-- 1. Grade

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

inductive ConventionWitness where | pureCall | errorCall | heapCall | heapErrorCall
  deriving Inhabited

def subgrade : Grade → Grade → Option ConventionWitness
  | .pure, _ => some .pureCall
  | .err, .err | .err, .heapErr => some .errorCall
  | .heap, .heap | .heap, .heapErr => some .heapCall
  | .heapErr, .heapErr => some .heapErrorCall
  | _, _ => none

-- 2. Types

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

-- 3. FGL Terms

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

-- 4. Monad (Option-based: check can fail for grade discovery)

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

def failElab : ElabM α := failure

-- 5. HOAS

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

def applyConvention (w : ConventionWitness) (callee : String) (args : List FGLValue)
    (heap : Option FGLValue) (resultTy : HighType)
    (k : FGLValue → Option FGLValue → ElabM FGLProducer) : ElabM FGLProducer :=
  match w with
  | .pureCall => k (.staticCall callee args) heap
  | .errorCall =>
    mkEffectfulCall callee args [("result", resultTy), ("err", .TCore "Error")]
      fun outs => k outs[0]! heap
  | .heapCall =>
    mkEffectfulCall callee (heap.get! :: args) [("heap", .THeap), ("result", resultTy)]
      fun outs => k outs[1]! (some outs[0]!)
  | .heapErrorCall =>
    mkEffectfulCall callee (heap.get! :: args) [("heap", .THeap), ("result", resultTy), ("err", .TCore "Error")]
      fun outs => k outs[1]! (some outs[0]!)

-- 6. Subsumption

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

-- 7-9. Elaboration

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
    | some s =>
      let checkedArgs ← checkArgs heap args s.params
      pure (.staticCall callee.text checkedArgs, eraseType s.effectType.resultType)
    | none =>
      let checkedArgs ← args.mapM fun arg => checkValue heap arg (.TCore "Any")
      pure (.staticCall callee.text checkedArgs, .TCore "Any")
  | _ => pure (.var "_unknown", .TCore "Any")

partial def checkValue (heap : Option FGLValue) (expr : StmtExprMd) (expected : HighType) : ElabM FGLValue := do
  let (val, actual) ← synthValue heap expr
  pure (applySubsume val actual (eraseType expected))

partial def checkArgs (heap : Option FGLValue) (args : List StmtExprMd) (params : List (String × HighType)) : ElabM (List FGLValue) :=
  (args.zip (params.map (·.2))).mapM fun (arg, pty) => checkValue heap arg pty

partial def synthProducer (heap : Option FGLValue) (expr : StmtExprMd) : ElabM (FGLProducer × LowType × Grade) := do
  match expr.val with
  | .StaticCall callee args =>
    let sig ← lookupFuncSig callee.text
    match sig with
    | some s =>
      let checkedArgs ← checkArgs heap args s.params
      -- For now: use effectType from Resolution as callee grade hint
      let calleeGrade := match s.effectType with
        | .pure _ => Grade.pure | .error _ _ => Grade.err
        | .stateful _ => Grade.heap | .statefulError _ _ => Grade.heapErr
      match subgrade calleeGrade calleeGrade with
      | some conv =>
        let prod ← applyConvention conv callee.text checkedArgs heap s.effectType.resultType
          fun rv newHeap => pure (.returnValue rv)
        pure (prod, eraseType s.effectType.resultType, calleeGrade)
      | none => failElab
    | none =>
      let (val, ty) ← synthValue heap expr
      pure (.returnValue val, ty, .pure)
  | .New _classId =>
    match heap with
    | some h =>
      let ref := FGLValue.staticCall "Heap..nextReference!" [h]
      let newHeap := FGLValue.staticCall "increment" [h]
      let obj := FGLValue.staticCall "MkComposite" [ref, .staticCall (_classId.text ++ "_TypeTag") []]
      pure (.assign (.var "$heap") newHeap (.returnValue obj), .TCore "Composite", .heap)
    | none => failElab  -- .New requires heap grade
  | .Assign targets value => match targets with
    | [target] =>
      let targetTy ← match target.val with
        | .Identifier id => match (← lookupEnv id.text) with | some (.variable t) => pure t | _ => pure (.TCore "Any")
        | _ => pure (.TCore "Any")
      let (tv, _) ← synthValue heap target
      let cr ← checkValue heap value targetTy
      pure (.assign tv cr .unit, .TVoid, .pure)
    | _ => pure (.unit, .TVoid, .pure)
  | .LocalVariable nameId typeMd initOpt =>
    let ci ← match initOpt with
      | some ⟨.Hole false _, _⟩ => pure none
      | some ⟨.Hole true _, _⟩ => do let hv ← freshVar "hole"; pure (some (.staticCall hv []))
      | some i => do let v ← checkValue heap i typeMd.val; pure (some v)
      | none => pure none
    let prod ← mkVarDecl nameId.text (eraseType typeMd.val) ci fun _ => pure .unit
    pure (prod, .TVoid, .pure)
  | .While cond _invs _dec body =>
    let cc ← checkValue heap cond .TBool
    let bp ← checkProducer heap body .TVoid .pure
    pure (.whileLoop cc bp .unit, .TVoid, .pure)
  | .Assert cond => let cc ← checkValue heap cond .TBool; pure (.assert cc .unit, .TVoid, .pure)
  | .Assume cond => let cc ← checkValue heap cond .TBool; pure (.assume cc .unit, .TVoid, .pure)
  | .Block stmts label =>
    let (prod, grade) ← elaborateBlock heap stmts .TVoid .pure
    pure (match label with | some l => (.labeledBlock l prod, .TVoid, grade) | none => (prod, .TVoid, grade))
  | .Exit target => pure (.exit target, .TVoid, .pure)
  | .Return valueOpt =>
    -- returnType comes from check context, not state. Use Any as fallback in synth.
    match valueOpt with
    | some v => let cv ← checkValue heap v (.TCore "Any"); pure (.returnValue cv, .TCore "Any", .pure)
    | none => pure (.returnValue .fromNone, .TVoid, .pure)
  | .IfThenElse cond thn els =>
    let cc ← checkValue heap cond .TBool
    let tp ← checkProducer heap thn .TVoid .pure
    let ep ← match els with | some e => checkProducer heap e .TVoid .pure | none => pure .unit
    pure (.ifThenElse cc tp ep, .TVoid, .pure)
  | .FieldSelect _ _ =>
    let (v, t) ← synthValue heap expr
    let grade := if heap.isSome then Grade.heap else Grade.pure
    pure (.returnValue v, t, grade)
  | .Hole deterministic _ =>
    if deterministic then do
      let hv ← freshVar "hole"; pure (.returnValue (.staticCall hv []), .TCore "Any", .pure)
    else do
      let prod ← mkVarDecl "_havoc" (.TCore "Any") none fun hv => pure (.returnValue hv)
      pure (prod, .TCore "Any", .pure)
  | _ => let (v, t) ← synthValue heap expr; pure (.returnValue v, t, .pure)

partial def checkProducer (heap : Option FGLValue) (expr : StmtExprMd) (expected : LowType) (grade : Grade) : ElabM FGLProducer := do
  match expr.val with
  | .IfThenElse cond thn els =>
    let cc ← checkValue heap cond .TBool
    let tp ← checkProducer heap thn expected grade
    let ep ← match els with | some e => checkProducer heap e expected grade | none => pure .unit
    pure (.ifThenElse cc tp ep)
  | .Return valueOpt =>
    match valueOpt with
    | some v => let cv ← checkValue heap v (liftType expected); pure (.returnValue cv)
    | none => pure (.returnValue .fromNone)
  | .Block stmts label =>
    let (prod, _) ← elaborateBlock heap stmts expected grade
    pure (match label with | some l => .labeledBlock l prod | none => prod)
  | _ =>
    -- Subsumption: synth then check grade
    let (prod, _, synthGrade) ← synthProducer heap expr
    -- Check: synthGrade ≤ grade (subgrading admissible — no new term)
    if Grade.residual synthGrade grade |>.isSome then pure prod
    else failElab

partial def elaborateBlock (heap : Option FGLValue) (stmts : List StmtExprMd) (expected : LowType) (grade : Grade) : ElabM (FGLProducer × Grade) := do
  match stmts with
  | [] => pure (.unit, .pure)
  | [last] =>
    let prod ← checkProducer heap last expected grade
    pure (prod, grade)
  | stmt :: rest =>
    let (stmtProd, _, stmtGrade) ← synthProducer heap stmt
    match Grade.residual stmtGrade grade with
    | some restGrade =>
      let (restProd, _) ← elaborateBlock heap rest expected restGrade
      pure (.seq stmtProd restProd, grade)
    | none => failElab

end

-- 10. Projection

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
    [mkLaurel md (.LocalVariable (Identifier.mk name none) (mkHighTypeMd md (liftType ty)) (init.map (projectValue md)))] ++ projectProducer md body
  | .ifThenElse cond thn els =>
    [mkLaurel md (.IfThenElse (projectValue md cond) (mkLaurel md (.Block (projectProducer md thn) none)) (some (mkLaurel md (.Block (projectProducer md els) none))))]
  | .whileLoop cond body after =>
    [mkLaurel md (.While (projectValue md cond) [] none (mkLaurel md (.Block (projectProducer md body) none)))] ++ projectProducer md after
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

-- 11. fullElaborate

private def tryGrades (env : TypeEnv) (heap : Option FGLValue) (body : StmtExprMd) (retTy : LowType) (grades : List Grade) : Option (FGLProducer × Grade) :=
  grades.findSome? fun g =>
    let st : ElabState := { freshCounter := 0 }
    match (checkProducer heap body retTy g).run env |>.run st with
    | some (prod, _) => some (prod, g)
    | none => none

def fullElaborate (typeEnv : TypeEnv) (program : Laurel.Program) : Except String Laurel.Program := do
  let mut procs : List Laurel.Procedure := []
  for proc in program.staticProcedures do
    match proc.body with
    | .Transparent bodyExpr =>
      let retTy : LowType := .TCore "Any"
      let baseEnv := (proc.inputs ++ proc.outputs).foldl
        (fun env p => { env with names := env.names.insert p.name.text (.variable p.type.val) }) typeEnv
      -- Try grades: pure first, then err, heap, heapErr
      let grades := [Grade.pure, Grade.err, Grade.heap, Grade.heapErr]
      -- First try without heap param
      match tryGrades baseEnv none bodyExpr retTy grades with
      | some (fgl, grade) =>
        match grade with
        | .heap | .heapErr =>
          -- Re-elaborate with heap
          let extEnv := { baseEnv with names := baseEnv.names.insert "$heap_in" (.variable .THeap) |>.insert "$heap" (.variable .THeap) }
          match tryGrades extEnv (some (.var "$heap")) bodyExpr retTy [grade] with
          | some (fglH, _) =>
            let fglFinal := FGLProducer.assign (.var "$heap") (.var "$heap_in") fglH
            let heapTy : HighTypeMd := ⟨.THeap, #[]⟩
            let heapIn : Laurel.Parameter := { name := Identifier.mk "$heap_in" none, type := heapTy }
            let heapOut : Laurel.Parameter := { name := Identifier.mk "$heap" none, type := heapTy }
            procs := procs ++ [{ proc with inputs := heapIn :: proc.inputs, outputs := heapOut :: proc.outputs, body := .Transparent (projectBody bodyExpr.md fglFinal) }]
          | none =>
            procs := procs ++ [{ proc with body := .Transparent (projectBody bodyExpr.md fgl) }]
        | _ =>
          procs := procs ++ [{ proc with body := .Transparent (projectBody bodyExpr.md fgl) }]
      | none =>
        -- Elaboration failed at all grades — pass through unchanged
        procs := procs ++ [proc]
    | _ => procs := procs ++ [proc]
  let hasHeap := procs.any fun p => p.inputs.any fun i => i.name.text == "$heap_in"
  let compositeType : TypeDefinition := .Datatype { name := "Composite", typeArgs := [], constructors := [{ name := "MkComposite", args := [{ name := "ref", type := ⟨.TInt, #[]⟩ }] }] }
  if hasHeap then
    pure { program with staticProcedures := heapConstants.staticProcedures ++ procs, types := heapConstants.types ++ [compositeType] ++ program.types }
  else
    pure { program with staticProcedures := procs, types := [compositeType] ++ program.types }

end
end Strata.FineGrainLaurel
