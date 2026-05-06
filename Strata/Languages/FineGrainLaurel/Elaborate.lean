/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.Languages.FineGrainLaurel.FineGrainLaurel
public import Strata.Languages.Laurel.Laurel
public import Strata.Languages.Python.NameResolution

/-! ## Elaboration: Laurel → FineGrainLaurel → Laurel (projected)

Per ARCHITECTURE.md §"Elaboration (Derivation Transformation)":
- Language-independent bidirectional typing (Dunfield & Krishnaswami 2021)
- Four functions: synthValue, checkValue, synthProducer, checkProducer
- Operations (local): coercions, exceptions, ANF, short-circuit
- Co-operations (global): heap threading via fixpoint propagation
- Metadata in reader context (reader = comonad, never dropped)
- Projection via splitProducer (bind reassociation, Peyton Jones et al. 1996)
-/

namespace Strata.FineGrainLaurel

open Strata.Laurel
open Strata.Python.Resolution

public section

/-! ## Types -/

/-- FGL Value (untyped representation for now — DDM generates the real type). -/
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

/-- FGL Producer (effectful terms). -/
inductive FGLProducer where
  | returnValue (v : FGLValue)
  | call (name : String) (args : List FGLValue)
  | letProd (var : String) (ty : HighType) (prod : FGLProducer) (body : FGLProducer)
  | letValue (var : String) (ty : HighType) (val : FGLValue) (body : FGLProducer)
  | assign (target : FGLValue) (val : FGLValue) (body : FGLProducer)
  | varDecl (name : String) (ty : HighType) (init : FGLValue) (body : FGLProducer)
  | ifThenElse (cond : FGLValue) (thn : FGLProducer) (els : FGLProducer)
  | whileLoop (cond : FGLValue) (body : FGLProducer) (after : FGLProducer)
  | assert (cond : FGLValue) (body : FGLProducer)
  | assume (cond : FGLValue) (body : FGLProducer)
  | callWithError (callee : String) (args : List FGLValue)
      (resultVar : String) (errorVar : String)
      (resultTy : HighType) (errorTy : HighType) (body : FGLProducer)
  | exit (label : String)
  | labeledBlock (label : String) (body : FGLProducer)
  | newObj (className : String) (resultVar : String) (ty : HighType) (body : FGLProducer)
  | seq (first : FGLProducer) (second : FGLProducer)
  | unit
  deriving Inhabited

/-! ## Elaboration Monad

Per ARCHITECTURE.md §"Metadata: Reader as Comonad":
Metadata lives in the reader. When elaboration descends into a subnode,
it updates currentMd. FGL types have no annotation parameter.
-/

/-- Elaboration context: Γ + current source metadata. -/
structure ElabContext where
  env : TypeEnv
  currentMd : Imperative.MetaData Core.Expression := #[]

/-- Elaboration state: fresh variable counter. -/
structure ElabState where
  freshCounter : Nat := 0

/-- Elaboration errors. -/
inductive ElabError where
  | typeError (msg : String)
  | unsupported (msg : String)
  deriving Repr, Inhabited

instance : ToString ElabError where
  toString
    | .typeError msg => s!"Elaboration type error: {msg}"
    | .unsupported msg => s!"Elaboration unsupported: {msg}"

abbrev ElabM := ReaderT ElabContext (StateT ElabState (Except ElabError))

/-- Generate a fresh variable name. -/
def freshVar (pfx : String := "tmp") : ElabM String := do
  let s ← get
  set { s with freshCounter := s.freshCounter + 1 }
  pure s!"{pfx}${s.freshCounter}"

/-- Look up a name in Γ. -/
def lookupEnv (name : String) : ElabM (Option NameInfo) := do
  pure (← read).env.names[name]?

/-- Get a function signature from Γ. -/
def lookupFuncSig (name : String) : ElabM (Option FuncSig) := do
  match (← read).env.names[name]? with
  | some (.function sig) => pure (some sig)
  | _ => pure none

/-! ## Subtyping and Narrowing (per ARCHITECTURE.md §"Coercion Table")

Two relations:
- A <: B (subtyping): value→value, infallible
- A ▷ B (narrowing): value→producer, fallible
-/

/-- Can we upcast A to B? Returns the coercion function name. -/
def canUpcast (actual expected : HighType) : Option (FGLValue → FGLValue) :=
  match actual, expected with
  | .TInt, .TCore "Any" => some FGLValue.fromInt
  | .TBool, .TCore "Any" => some FGLValue.fromBool
  | .TString, .TCore "Any" => some FGLValue.fromStr
  | .TFloat64, .TCore "Any" => some FGLValue.fromFloat
  | .UserDefined _, .TCore "Any" => some FGLValue.fromComposite
  | .TCore "ListAny", .TCore "Any" => some FGLValue.fromListAny
  | .TCore "DictStrAny", .TCore "Any" => some FGLValue.fromDictStrAny
  | .TVoid, .TCore "Any" => some (fun _ => FGLValue.fromNone)
  | _, _ => none

/-- Can we narrow A to B? Returns the downcast procedure name. -/
def canNarrow (actual expected : HighType) : Option String :=
  match actual, expected with
  | .TCore "Any", .TBool => some "Any_to_bool"
  | .TCore "Any", .TInt => some "Any..as_int!"
  | .TCore "Any", .TString => some "Any..as_string!"
  | .TCore "Any", .TFloat64 => some "Any..as_float!"
  | .TCore "Any", .UserDefined _ => some "Any..as_Composite!"
  | _, _ => none

/-- Are two types equal (no coercion needed)? -/
def typesEqual (a b : HighType) : Bool :=
  match a, b with
  | .TInt, .TInt => true
  | .TBool, .TBool => true
  | .TString, .TString => true
  | .TFloat64, .TFloat64 => true
  | .TVoid, .TVoid => true
  | .TCore n1, .TCore n2 => n1 == n2
  | .UserDefined id1, .UserDefined id2 => id1.text == id2.text
  | _, _ => false

/-! ## The Four Functions (Bidirectional Walk)

Per ARCHITECTURE.md §"The Bidirectional Recipe":
- synthValue: infer type of a value expression
- checkValue: check expression against expected type (insert upcast if needed)
- synthProducer: infer type of a producer expression
- checkProducer: check expression against expected type (insert downcast if needed)
-/

/-- Sequence two producers. Replaces .unit continuations with the next producer. -/
private def sequenceProducers (first second : FGLProducer) : FGLProducer :=
  match first with
  | .unit => second
  | .assign target val .unit => .assign target val second
  | .varDecl name ty init .unit => .varDecl name ty init second
  | .assert cond .unit => .assert cond second
  | .assume cond .unit => .assume cond second
  | _ => .seq first second

/-- Enter a subnode's metadata context. The reader comonad: extract md from the
    input node, make it available for projection output. -/
private def withNodeMd (node : StmtExprMd) (action : ElabM α) : ElabM α :=
  withReader (fun ctx => { ctx with currentMd := node.md }) action

mutual

/-- Synthesize a value: infer the type from the expression structure or Γ. -/
partial def synthValue (expr : StmtExprMd) : ElabM (FGLValue × HighType) := withNodeMd expr do
  match expr.val with
  | .LiteralInt n => pure (.litInt n, .TInt)
  | .LiteralBool b => pure (.litBool b, .TBool)
  | .LiteralString s => pure (.litString s, .TString)
  | .Identifier name =>
      let info ← lookupEnv name.text
      let ty := match info with
        | some (.variable t) => t
        | some (.function sig) => sig.returnType
        | _ => .TCore "Any"
      pure (.var name.text, ty)
  | .FieldSelect obj field =>
      let (objVal, _objTy) ← synthValue obj
      pure (.fieldAccess objVal field.text, .TCore "Any")
  | .StaticCall name args =>
      let sig ← lookupFuncSig name.text
      let argVals ← args.mapM fun arg => do
        let (v, _) ← synthValue arg
        pure v
      let retTy := match sig with
        | some s => s.returnType
        | none => .TCore "Any"
      pure (.staticCall name.text argVals, retTy)
  | _ =>
      pure (.var "_hole", .TCore "Any")

/-- Check a value against an expected type. Insert upcast if needed. -/
partial def checkValue (expr : StmtExprMd) (expected : HighType) : ElabM FGLValue := withNodeMd expr do
  let (val, actual) ← synthValue expr
  if typesEqual actual expected then
    pure val
  else
    match canUpcast actual expected with
    | some coerce => pure (coerce val)
    | none => pure val

/-- Synthesize a producer from a statement/expression.
    Handles calls (effectful), control flow, sequencing. -/
partial def synthProducer (expr : StmtExprMd) : ElabM (FGLProducer × HighType) := do
  match expr.val with
  | .StaticCall name args => do
      let sig ← lookupFuncSig name.text
      -- Check args against param types
      let checkedArgs ← match sig with
        | some s =>
            let pairs := List.zip args s.params
            pairs.mapM fun (arg, (_, paramTy)) => checkValue arg paramTy
        | none =>
            args.mapM fun arg => do let (v, _) ← synthValue arg; pure v
      let retTy := match sig with
        | some s => s.returnType
        | none => .TCore "Any"
      -- If callee has error output, emit prodCallWithError
      let hasError := match sig with
        | some s => s.hasErrorOutput
        | none => false
      if hasError then do
        let resultVar ← freshVar "result"
        let errorVar ← freshVar "err"
        pure (.callWithError name.text checkedArgs resultVar errorVar retTy
              (.TCore "Error") (.returnValue (.var resultVar)), retTy)
      else
        pure (.call name.text checkedArgs, retTy)
  | .Assign targets value => do
      match targets with
      | [target] => do
          -- Get target type
          let targetTy ← match target.val with
            | .Identifier name => do
                let info ← lookupEnv name.text
                pure (match info with
                  | some (.variable t) => t
                  | _ => .TCore "Any")
            | _ => pure (.TCore "Any")
          let (targetVal, _) ← synthValue target
          -- Check RHS against target type
          let checkedVal ← checkValue value targetTy
          pure (.assign targetVal checkedVal .unit, targetTy)
      | _ => pure (.unit, .TCore "Any")
  | .LocalVariable name typeMd initOpt => do
      let ty := typeMd.val
      let initVal ← match initOpt with
        | some init => checkValue init ty
        | none => pure (.var "_uninit")
      pure (.varDecl name.text ty initVal .unit, ty)
  | .IfThenElse cond thenBranch elseBranch => do
      -- Condition must be bool: check with narrowing
      let condVal ← checkValue cond .TBool
      let (thenProd, thenTy) ← synthProducer thenBranch
      let elsProd ← match elseBranch with
        | some els => do let (p, _) ← synthProducer els; pure p
        | none => pure .unit
      pure (.ifThenElse condVal thenProd elsProd, thenTy)
  | .While cond _invariants _variant body => do
      let condVal ← checkValue cond .TBool
      let (bodyProd, _) ← synthProducer body
      pure (.whileLoop condVal bodyProd .unit, .TVoid)
  | .Assert cond => do
      let condVal ← checkValue cond .TBool
      pure (.assert condVal .unit, .TVoid)
  | .Assume cond => do
      let condVal ← checkValue cond .TBool
      pure (.assume condVal .unit, .TVoid)
  | .Block stmts _label => do
      elaborateBlock stmts
  | .Exit label => do
      pure (.exit label, .TVoid)
  | .New classId => do
      let ty := HighType.UserDefined classId
      let tmpVar ← freshVar "obj"
      pure (.newObj classId.text tmpVar ty (.returnValue (.var tmpVar)), ty)
  | .Return value => do
      match value with
      | some v => do
          let (val, ty) ← synthValue v
          pure (.returnValue val, ty)
      | none => pure (.returnValue .fromNone, .TVoid)
  | _ => do
      -- Fallback: try as value, wrap in returnValue
      let (val, ty) ← synthValue expr
      pure (.returnValue val, ty)

/-- Check a producer against expected type. Insert narrowing if needed. -/
partial def checkProducer (expr : StmtExprMd) (expected : HighType) : ElabM FGLProducer := do
  let (prod, actual) ← synthProducer expr
  if typesEqual actual expected then
    pure prod
  else
    match canNarrow actual expected with
    | some narrowFn => do
        -- Bind the producer, then narrow the result
        let tmpVar ← freshVar "narrow"
        pure (.letProd tmpVar actual prod
              (.callWithError narrowFn [.var tmpVar] (tmpVar ++ "_ok") (tmpVar ++ "_err")
                expected (.TCore "Error") (.returnValue (.var (tmpVar ++ "_ok")))))
    | none =>
        pure prod

/-- Elaborate a block (list of statements) into a sequenced producer.
    Per ARCHITECTURE.md: blocks are nested lets (CBV → FGCBV embedding). -/
partial def elaborateBlock (stmts : List StmtExprMd) : ElabM (FGLProducer × HighType) := do
  match stmts with
  | [] => pure (.unit, .TVoid)
  | [last] => synthProducer last
  | stmt :: rest => do
      let (stmtProd, _stmtTy) ← synthProducer stmt
      let (restProd, restTy) ← elaborateBlock rest
      pure (sequenceProducers stmtProd restProd, restTy)

end -- mutual

/-! ## Projection: FGL → Laurel (per ARCHITECTURE.md §"Projection")

splitProducer implements bind reassociation (let-floating).
Flattens nested prodLetProd into sequential statements.
-/

/-- Project an FGLValue back to a Laurel StmtExprMd. -/
partial def projectValue (v : FGLValue) (md : Imperative.MetaData Core.Expression := #[])
    : StmtExprMd :=
  let mk e := ({ val := e, md := md } : StmtExprMd)
  match v with
  | .litInt n => mk (.LiteralInt n)
  | .litBool b => mk (.LiteralBool b)
  | .litString s => mk (.LiteralString s)
  | .var name => mk (.Identifier (Identifier.mk name none))
  | .fromInt inner => mk (.StaticCall (Identifier.mk "from_int" none) [projectValue inner md])
  | .fromStr inner => mk (.StaticCall (Identifier.mk "from_str" none) [projectValue inner md])
  | .fromBool inner => mk (.StaticCall (Identifier.mk "from_bool" none) [projectValue inner md])
  | .fromFloat inner => mk (.StaticCall (Identifier.mk "from_float" none) [projectValue inner md])
  | .fromComposite inner => mk (.StaticCall (Identifier.mk "from_Composite" none) [projectValue inner md])
  | .fromListAny inner => mk (.StaticCall (Identifier.mk "from_ListAny" none) [projectValue inner md])
  | .fromDictStrAny inner => mk (.StaticCall (Identifier.mk "from_DictStrAny" none) [projectValue inner md])
  | .fromNone => mk (.StaticCall (Identifier.mk "from_None" none) [])
  | .fieldAccess obj field => mk (.FieldSelect (projectValue obj md) (Identifier.mk field none))
  | .staticCall name args => mk (.StaticCall (Identifier.mk name none) (args.map (projectValue · md)))

mutual

/-- Split a producer into (prefix statements, terminal expression).
    This is the core of projection — bind reassociation / let-floating. -/
partial def splitProducer (prod : FGLProducer)
    (md : Imperative.MetaData Core.Expression := #[])
    : (List StmtExprMd) × StmtExprMd :=
  let mk e := ({ val := e, md := md } : StmtExprMd)
  match prod with
  | .returnValue v => ([], projectValue v md)
  | .call name args => ([], mk (.StaticCall (Identifier.mk name none) (args.map (projectValue · md))))
  | .letProd var ty inner body =>
      let (innerStmts, innerExpr) := splitProducer inner md
      let varDecl := mk (.LocalVariable (Identifier.mk var none) ({ val := ty, md := md } : HighTypeMd) (some innerExpr))
      let (bodyStmts, bodyExpr) := splitProducer body md
      (innerStmts ++ [varDecl] ++ bodyStmts, bodyExpr)
  | .letValue var ty val body =>
      let varDecl := mk (.LocalVariable (Identifier.mk var none) ({ val := ty, md := md } : HighTypeMd)
                          (some (projectValue val md)))
      let (bodyStmts, bodyExpr) := splitProducer body md
      ([varDecl] ++ bodyStmts, bodyExpr)
  | .assign target val body =>
      let assignStmt := mk (.Assign [projectValue target md] (projectValue val md))
      let (bodyStmts, bodyExpr) := splitProducer body md
      ([assignStmt] ++ bodyStmts, bodyExpr)
  | .varDecl name ty init body =>
      let decl := mk (.LocalVariable (Identifier.mk name none) ({ val := ty, md := md } : HighTypeMd)
                       (some (projectValue init md)))
      let (bodyStmts, bodyExpr) := splitProducer body md
      ([decl] ++ bodyStmts, bodyExpr)
  | .ifThenElse cond thn els =>
      let thnBlock := projectProducer thn md
      let elsBlock := projectProducer els md
      ([], mk (.IfThenElse (projectValue cond md) thnBlock (some elsBlock)))
  | .whileLoop cond body afterProd =>
      let bodyBlock := projectProducer body md
      let whileStmt := mk (.While (projectValue cond md) [] none bodyBlock)
      let (afterStmts, afterExpr) := splitProducer afterProd md
      ([whileStmt] ++ afterStmts, afterExpr)
  | .assert cond body =>
      let assertStmt := mk (.Assert (projectValue cond md))
      let (bodyStmts, bodyExpr) := splitProducer body md
      ([assertStmt] ++ bodyStmts, bodyExpr)
  | .assume cond body =>
      let assumeStmt := mk (.Assume (projectValue cond md))
      let (bodyStmts, bodyExpr) := splitProducer body md
      ([assumeStmt] ++ bodyStmts, bodyExpr)
  | .callWithError callee args resultVar errorVar resultTy errorTy body =>
      let callExpr := mk (.StaticCall (Identifier.mk callee none) (args.map (projectValue · md)))
      let resultDecl := mk (.LocalVariable (Identifier.mk resultVar none)
        ({ val := resultTy, md := md } : HighTypeMd) (some callExpr))
      let errorDecl := mk (.LocalVariable (Identifier.mk errorVar none)
        ({ val := errorTy, md := md } : HighTypeMd) (some (mk (.StaticCall (Identifier.mk "NoError" none) []))))
      let (bodyStmts, bodyExpr) := splitProducer body md
      ([resultDecl, errorDecl] ++ bodyStmts, bodyExpr)
  | .exit label => ([mk (.Exit label)], mk (.LiteralBool true))
  | .labeledBlock label body =>
      let bodyBlock := projectProducer body md
      ([mk (.Block [bodyBlock] (some label))], mk (.LiteralBool true))
  | .newObj className resultVar ty body =>
      let classId := Identifier.mk className none
      let newExpr := mk (.New classId)
      let decl := mk (.LocalVariable (Identifier.mk resultVar none) ({ val := ty, md := md } : HighTypeMd) (some newExpr))
      let (bodyStmts, bodyExpr) := splitProducer body md
      ([decl] ++ bodyStmts, bodyExpr)
  | .seq first second =>
      let (firstStmts, _) := splitProducer first md
      let (secondStmts, secondExpr) := splitProducer second md
      (firstStmts ++ secondStmts, secondExpr)
  | .unit => ([], mk (.LiteralBool true))

/-- Project a producer to a Laurel block (all statements, wrapped). -/
partial def projectProducer (prod : FGLProducer)
    (md : Imperative.MetaData Core.Expression := #[]) : StmtExprMd :=
  let (stmts, terminal) := splitProducer prod md
  let allStmts := if stmts.isEmpty then [terminal] else stmts ++ [terminal]
  { val := .Block allStmts none, md := md }

end -- mutual (splitProducer / projectProducer)

/-! ## Top-Level Elaboration

Elaborates each procedure body, then projects back to Laurel.
-/

/-- Elaborate a single procedure body. -/
def elaborateProcedure (env : TypeEnv) (proc : Laurel.Procedure) : Except ElabError Laurel.Procedure := do
  match proc.body with
  | .Transparent bodyExpr =>
    let ctx : ElabContext := { env := env, currentMd := bodyExpr.md }
    let initState : ElabState := { freshCounter := 0 }
    let ((fglProd, _ty), _finalState) ← (synthProducer bodyExpr).run ctx |>.run initState
    let projectedBody := projectProducer fglProd bodyExpr.md
    pure { proc with body := .Transparent projectedBody }
  | _ => pure proc

/-- Elaborate all procedures in a program. -/
def elaborateProgram (env : TypeEnv) (program : Laurel.Program)
    : Except ElabError Laurel.Program := do
  let mut procs : List Laurel.Procedure := []
  for proc in program.staticProcedures do
    let elaborated ← elaborateProcedure env proc
    procs := procs ++ [elaborated]
  pure { program with staticProcedures := procs }

/-- Entry point: fullElaborate (called by PySpecPipeline). -/
def fullElaborate (typeEnv : TypeEnv) (program : Laurel.Program)
    : Except String Laurel.Program :=
  match elaborateProgram typeEnv program with
  | .ok prog => .ok prog
  | .error e => .error (toString e)

end -- public section

end Strata.FineGrainLaurel
