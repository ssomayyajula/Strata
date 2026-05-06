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
- Metadata via smart constructors (ARCHITECTURE.md §"Metadata: Smart Constructors")
- Projection via splitProducer (bind reassociation, Peyton Jones et al. 1996)
-/

namespace Strata.FineGrainLaurel

open Strata.Laurel
open Strata.Python.Resolution

public section

/-! ## Task 1: Smart Constructors (ARCHITECTURE.md §"Metadata: Smart Constructors")

The ONLY way to build AST nodes. Never write `{ val := ..., md := ... }` directly
except inside these two definitions.
-/

/-- Smart constructor for Laurel StmtExprMd nodes.
    Per ARCHITECTURE.md: "You NEVER write `{ val := ..., md := ... }` directly." -/
def mkLaurel (md : Imperative.MetaData Core.Expression) (e : StmtExpr) : StmtExprMd :=
  { val := e, md := md }

/-- Smart constructor for HighTypeMd nodes. -/
def mkHighTypeMd (md : Imperative.MetaData Core.Expression) (ty : HighType) : HighTypeMd :=
  { val := ty, md := md }

/-! ## Task 2: FGLValue (ARCHITECTURE.md §"Representation Decisions: Separate Value and Producer Types")

Value category — inert terms: literals, variables, pure constructions.
Illegal states (producer in value position) are unrepresentable.
-/

/-- FGL Value: inert terms (literals, variables, fields, upcasts).
    Per ARCHITECTURE.md: "Positive types (values): int, bool, str, Any, Composite, ListAny, DictStrAny" -/
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

/-! ## Task 3: FGLProducer (ARCHITECTURE.md §"Representation Decisions: Separate Value and Producer Types")

Producer category — effectful terms: calls, let-bindings, control flow.
The only negative type: ↑A for any positive A (= a producer that yields A).
-/

/-- FGL Producer: effectful terms (calls, let-bindings, control flow, coercions).
    Per ARCHITECTURE.md: "A producer in value position *must* be explicitly sequenced via let-binding" -/
inductive FGLProducer where
  | returnValue (v : FGLValue)
  | call (name : String) (args : List FGLValue)
  | letProd (var : String) (ty : HighType) (prod : FGLProducer) (body : FGLProducer)
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

/-! ## Task 4: ElabM Monad + Helpers (IMPLEMENTATION_PLAN.md §"Phase 4" monad)

Per ARCHITECTURE.md §"Elaboration":
  abbrev ElabM := ReaderT TypeEnv (StateT ElabState (Except ElabError))
Γ in the reader (immutable). Fresh variable counter in the state.
-/

/-- Elaboration state: fresh variable counter + current procedure return type.
    `currentProcReturnType` is just another CHECK position — same subsumption
    mechanism as arg checking and assignment RHS checking (per IMPLEMENTATION_PLAN.md §Task 4). -/
structure ElabState where
  freshCounter : Nat := 0
  currentProcReturnType : HighType := .TCore "Any"

/-- Elaboration errors. -/
inductive ElabError where
  | typeError (msg : String)
  | unsupported (msg : String)
  deriving Repr, Inhabited

instance : ToString ElabError where
  toString
    | .typeError msg => s!"Elaboration type error: {msg}"
    | .unsupported msg => s!"Elaboration unsupported: {msg}"

/-- The elaboration monad. Γ (TypeEnv) in reader, fresh counter in state.
    Per ARCHITECTURE.md §"Monad carries context — ReaderT/StateT". -/
abbrev ElabM := ReaderT TypeEnv (StateT ElabState (Except ElabError))

/-- Generate a fresh variable name. Per ARCHITECTURE.md §"Freshness ensures soundness":
    Elaboration MUST use freshVar for all intermediate bindings. -/
def freshVar (pfx : String := "tmp") : ElabM String := do
  let s ← get
  set { s with freshCounter := s.freshCounter + 1 }
  pure s!"{pfx}${s.freshCounter}"

/-- Look up a name in Γ. -/
def lookupEnv (name : String) : ElabM (Option NameInfo) := do
  pure (← read).names[name]?

/-- Get a function signature from Γ. -/
def lookupFuncSig (name : String) : ElabM (Option FuncSig) := do
  match (← read).names[name]? with
  | some (.function sig) => pure (some sig)
  | _ => pure none

/-- Look up the type of a field on a class.
    Falls back to Any if the class or field is unknown. -/
def lookupFieldType (className field : String) : ElabM HighType := do
  let env ← read
  match env.classFields[className]? with
  | some fields =>
      match fields.find? (fun (n, _) => n == field) with
      | some (_, ty) => pure ty
      | none => pure (.TCore "Any")
  | none => pure (.TCore "Any")

/-! ## Task 5: Coercion Table (ARCHITECTURE.md §"The coercion table")

Two relations, determined by the types:
- A <: B (subtyping) → value-level upcast (infallible). `int <: Any` via valFromInt.
- A ▷ B (narrowing) → producer-level downcast (fallible). `Any ▷ bool` via Any_to_bool.
The type tells you which. You don't decide.
-/

/-- Can we upcast actual to expected? Returns the value-level coercion function.
    Per ARCHITECTURE.md §"Subtyping (value-level, infallible)":
    Γ ⊢_v e ⇒ A    A <: B  ⊢  Γ ⊢_v upcast(e) ⇐ B -/
def canUpcast (actual expected : HighType) : Option (FGLValue → FGLValue) :=
  match actual, expected with
  | .TInt, .TCore "Any" => some .fromInt
  | .TBool, .TCore "Any" => some .fromBool
  | .TString, .TCore "Any" => some .fromStr
  | .TFloat64, .TCore "Any" => some .fromFloat
  | .UserDefined _, .TCore "Any" => some .fromComposite
  | .TCore "ListAny", .TCore "Any" => some .fromListAny
  | .TCore "DictStrAny", .TCore "Any" => some .fromDictStrAny
  | .TVoid, .TCore "Any" => some (fun _ => .fromNone)
  | _, _ => none

/-- Can we narrow actual to expected? Returns the downcast procedure name.
    Per ARCHITECTURE.md §"Narrowing (producer-level, fallible)":
    Γ ⊢_v e ⇒ A    A ▷ B  ⊢  Γ ⊢_p narrow(e) : B -/
def canNarrow (actual expected : HighType) : Option String :=
  match actual, expected with
  | .TCore "Any", .TBool => some "Any_to_bool"
  | .TCore "Any", .TInt => some "Any..as_int!"
  | .TCore "Any", .TString => some "Any..as_string!"
  | .TCore "Any", .TFloat64 => some "Any..as_float!"
  | .TCore "Any", .UserDefined _ => some "Any..as_Composite!"
  | _, _ => none

/-- Are two types equal (no coercion needed)?
    Per ARCHITECTURE.md: "If actual = expected → no coercion" -/
def typesEqual (a b : HighType) : Bool :=
  match a, b with
  | .TInt, .TInt | .TBool, .TBool | .TString, .TString
  | .TFloat64, .TFloat64 | .TVoid, .TVoid => true
  | .TCore n1, .TCore n2 => n1 == n2
  | .UserDefined id1, .UserDefined id2 => id1.text == id2.text
  | _, _ => false

/-! ## sequenceProducers helper (IMPLEMENTATION_PLAN.md §"Task 13")

Replaces .unit continuations when sequencing statements in a block.
Put BEFORE the mutual block so that synthProducer/elaborateBlock can use it.
-/

/-- Sequence two producers: replaces .unit continuations in the first with the second.
    Per IMPLEMENTATION_PLAN.md §"Task 13": foldr over block stmts uses this. -/
private def sequenceProducers (first second : FGLProducer) : FGLProducer :=
  match first with
  | .unit => second
  | .assign target val .unit => .assign target val second
  | .varDecl name ty init .unit => .varDecl name ty init second
  | .assert cond .unit => .assert cond second
  | .assume cond .unit => .assume cond second
  | _ => .seq first second

/-! ## Tasks 6-8: synthValue + checkValue (ARCHITECTURE.md §"The Bidirectional Recipe")

Per ARCHITECTURE.md §"What SYNTHESIZES":
- Literals synthesize their literal type
- Identifier synthesizes Γ(x)
- FieldSelect synthesizes field type from classFields
- StaticCall synthesizes FuncSig.returnType
- New synthesizes UserDefined ClassName

Per ARCHITECTURE.md §"Subsumption (coercion insertion)":
- checkValue: synth, compare, coerce or error
- A <: B → upcast (value→value)
- A ▷ B → narrow (value→producer) — handled later in checkProducer
-/

mutual

/-- Synthesize a value and its type from a Laurel expression.
    Per ARCHITECTURE.md §"What SYNTHESIZES" — elimination forms produce known types. -/
partial def synthValue (expr : StmtExprMd) : ElabM (FGLValue × HighType) := do
  match expr.val with
  | .LiteralInt n => pure (.litInt n, .TInt)
  | .LiteralBool b => pure (.litBool b, .TBool)
  | .LiteralString s => pure (.litString s, .TString)
  | .Identifier id =>
    match (← lookupEnv id.text) with
    | some (.variable ty) => pure (.var id.text, ty)
    | some (.function sig) => pure (.var id.text, sig.returnType)
    | _ => pure (.var id.text, .TCore "Any")
  | .FieldSelect obj field =>
    let (objVal, objTy) ← synthValue obj
    match objTy with
    | .UserDefined className =>
      let fieldTy ← lookupFieldType className.text field.text
      pure (.fieldAccess objVal field.text, fieldTy)
    | _ => pure (.fieldAccess objVal field.text, .TCore "Any")
  | .StaticCall callee args =>
    let sig ← lookupFuncSig callee.text
    let retTy := match sig with
      | some s => s.returnType
      | none => .TCore "Any"
    let argVals ← args.mapM (fun a => do let (v, _) ← synthValue a; pure v)
    pure (.staticCall callee.text argVals, retTy)
  | .New classId =>
    pure (.var classId.text, .UserDefined classId)
  | _ => pure (.var "_hole", .TCore "Any")

/-- Check an expression against an expected type, inserting coercions as needed.
    Per ARCHITECTURE.md §"Subsumption (coercion insertion at CHECK boundaries)":
    synth(e) = A, expected = B, A ≠ B → insert upcast if A <: B. -/
partial def checkValue (expr : StmtExprMd) (expected : HighType) : ElabM FGLValue := do
  let (val, actual) ← synthValue expr
  if typesEqual actual expected then return val
  match canUpcast actual expected with
  | some coerce => return (coerce val)
  | none =>
    throw (ElabError.typeError s!"Cannot coerce {repr actual} to {repr expected}")

-- Tasks 9-13: synthProducer (ARCHITECTURE.md §"The Bidirectional Recipe")
-- Per ARCHITECTURE.md §"What CHECKS":
-- - Arg in f(arg) → checked against FuncSig.params[i]
-- - RHS of x := expr → checked against type of x
-- - RHS of var x: T := expr → checked against T
-- - return expr → checked against procedure return type
-- - Condition in assert/if/while → checked against bool (NARROWING if Any)

/-- Synthesize a producer and its type from a Laurel statement expression.
    Per ARCHITECTURE.md §"How Elaboration Works":
    - StaticCall: look up f in Γ, CHECK args, hasErrorOutput → callWithError
    - Assign: CHECK RHS against target type from Γ
    - LocalVariable: CHECK init against declared type
    - IfThenElse/While/Assert/Assume: NARROW condition (Any→bool via callWithError)
    - Block/Exit/New/Return: structural cases -/
partial def synthProducer (expr : StmtExprMd) : ElabM (FGLProducer × HighType) := do
  match expr.val with
  -- Task 9: StaticCall (CHECK args against FuncSig.params via checkValue)
  | .StaticCall callee args =>
    -- Task 15: PAnd/POr → short-circuit desugaring (ARCHITECTURE.md §"Short-Circuit Desugaring in FGL")
    if callee.text == "PAnd" || callee.text == "POr" then
      shortCircuitDesugar callee.text args
    else
      let sig ← lookupFuncSig callee.text
      let checkedArgs ← match sig with
        | some s =>
          let paramTypes := s.params.map (·.2)
          let pairs := args.zip paramTypes
          pairs.mapM (fun (arg, paramTy) => checkValue arg paramTy)
        | none => args.mapM (fun a => do let (v, _) ← synthValue a; pure v)
      let retTy := match sig with
        | some s => s.returnType
        | none => .TCore "Any"
      if (match sig with | some s => s.hasErrorOutput | none => false) then
        let rv ← freshVar "result"
        let ev ← freshVar "err"
        pure (.callWithError callee.text checkedArgs rv ev retTy (.TCore "Error")
               (.returnValue (.var rv)), retTy)
      else
        pure (.call callee.text checkedArgs, retTy)

  -- Task 10: Assign (CHECK RHS against target type from Γ)
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
      pure (.assign targetVal checkedRhs .unit, targetTy)
    | _ => pure (.unit, .TCore "Any")  -- multi-target: ARCHITECTURE GAP

  -- Task 11: LocalVariable (CHECK init against declared type)
  | .LocalVariable nameId typeMd initOpt =>
    let declTy := typeMd.val
    let initVal ← match initOpt with
      | some init => checkValue init declTy
      | none => pure (.var "_uninit")
    pure (.varDecl nameId.text declTy initVal .unit, declTy)

  -- Task 12: IfThenElse — condition is CHECK against bool via subsumption.
  -- No typesEqual dispatch. Coercion table decides.
  | .IfThenElse cond thenBranch elseBranch =>
    let (condVal, condTy) ← synthValue cond
    let (thenProd, thenTy) ← synthProducer thenBranch
    let elsProd ← match elseBranch with
      | some e => do let (p, _) ← synthProducer e; pure p
      | none => pure .unit
    -- Subsume condition to bool: try upcast, try narrow, else reflexivity
    match canUpcast condTy .TBool with
    | some coerce => pure (.ifThenElse (coerce condVal) thenProd elsProd, thenTy)
    | none => match canNarrow condTy .TBool with
      | some narrowFn =>
        let narrowVar ← freshVar "cond"
        pure (.callWithError narrowFn [condVal] narrowVar (narrowVar ++ "_err")
                  .TBool (.TCore "Error")
                  (.ifThenElse (.var narrowVar) thenProd elsProd), thenTy)
      | none => pure (.ifThenElse condVal thenProd elsProd, thenTy)  -- reflexivity

  -- Task 12: While — condition subsumed to bool, result = TVoid (synthesizes)
  | .While cond _invariants _decreases body =>
    let (condVal, condTy) ← synthValue cond
    let (bodyProd, _) ← synthProducer body
    match canUpcast condTy .TBool with
    | some coerce => pure (.whileLoop (coerce condVal) bodyProd .unit, .TVoid)
    | none => match canNarrow condTy .TBool with
      | some narrowFn =>
        let narrowVar ← freshVar "cond"
        pure (.callWithError narrowFn [condVal] narrowVar (narrowVar ++ "_err")
                  .TBool (.TCore "Error")
                  (.whileLoop (.var narrowVar) bodyProd .unit), .TVoid)
      | none => pure (.whileLoop condVal bodyProd .unit, .TVoid)

  -- Task 12: Assert — condition subsumed to bool, result = TVoid
  | .Assert condition =>
    let (condVal, condTy) ← synthValue condition
    match canUpcast condTy .TBool with
    | some coerce => pure (.assert (coerce condVal) .unit, .TVoid)
    | none => match canNarrow condTy .TBool with
      | some narrowFn =>
        let narrowVar ← freshVar "cond"
        pure (.callWithError narrowFn [condVal] narrowVar (narrowVar ++ "_err")
                  .TBool (.TCore "Error")
                  (.assert (.var narrowVar) .unit), .TVoid)
      | none => pure (.assert condVal .unit, .TVoid)

  -- Task 12: Assume — condition subsumed to bool, result = TVoid
  | .Assume condition =>
    let (condVal, condTy) ← synthValue condition
    match canUpcast condTy .TBool with
    | some coerce => pure (.assume (coerce condVal) .unit, .TVoid)
    | none => match canNarrow condTy .TBool with
      | some narrowFn =>
        let narrowVar ← freshVar "cond"
        pure (.callWithError narrowFn [condVal] narrowVar (narrowVar ++ "_err")
                  .TBool (.TCore "Error")
                  (.assume (.var narrowVar) .unit), .TVoid)
      | none => pure (.assume condVal .unit, .TVoid)

  -- Task 13: Block
  | .Block stmts label =>
    let (prod, ty) ← elaborateBlock stmts
    match label with
    | some l => pure (.labeledBlock l prod, ty)
    | none => pure (prod, ty)

  -- Task 13: Exit
  | .Exit target => pure (.exit target, .TVoid)

  -- Task 13: New
  | .New classId =>
    let objVar ← freshVar "obj"
    let ty := HighType.UserDefined classId
    pure (.newObj classId.text objVar ty (.returnValue (.var objVar)), ty)

  -- Task 13: Return
  | .Return valueOpt =>
    let retTy := (← get).currentProcReturnType
    match valueOpt with
    | some v =>
      let checkedVal ← checkValue v retTy
      pure (.returnValue checkedVal, retTy)
    | none => pure (.returnValue .fromNone, .TVoid)

  -- Fallback: synth as value, wrap in returnValue
  | _ =>
    let (v, t) ← synthValue expr
    pure (.returnValue v, t)

-- Task 14: checkProducer (ARCHITECTURE.md §"Narrowing")
-- Per ARCHITECTURE.md §"Subsumption":
-- - synthProducer to get (prod, actual)
-- - typesEqual → return prod
-- - canNarrow actual expected → letProd tmpVar actual prod (callWithError narrowFn ...)
-- - else → throw ElabError

/-- Check a producer against an expected type, inserting narrowing as needed.
    Per ARCHITECTURE.md §"Narrowing (A ▷ B)": bind producer, narrow result via fallible call. -/
partial def checkProducer (expr : StmtExprMd) (expected : HighType) : ElabM FGLProducer := do
  let (prod, actual) ← synthProducer expr
  if typesEqual actual expected then return prod
  match canNarrow actual expected with
  | some narrowFn =>
    let tmpVar ← freshVar "narrow"
    let resultVar ← freshVar "narrowed"
    pure (.letProd tmpVar actual prod
           (.callWithError narrowFn [.var tmpVar] resultVar (resultVar ++ "_err")
             expected (.TCore "Error") (.returnValue (.var resultVar))))
  | none =>
    throw (ElabError.typeError s!"Cannot narrow {repr actual} to {repr expected}")

-- Task 15: shortCircuitDesugar (ARCHITECTURE.md §"Short-Circuit Desugaring in FGL")
-- PAnd(a, b): Python semantics = return a if FALSY, else evaluate and return b
-- POr(a, b): Python semantics = return a if TRUTHY, else evaluate and return b
-- callWithError IS the binding for the narrowed bool (no extra letProd around it).

/-- Short-circuit desugaring for PAnd/POr.
    Per ARCHITECTURE.md §"Short-Circuit Desugaring in FGL":
    PAnd: `e to x. callWithError Any_to_bool [x] cond ... (if cond then elaborate b else returnValue x)`
    POr: `e to x. callWithError Any_to_bool [x] cond ... (if cond then returnValue x else elaborate b)` -/
partial def shortCircuitDesugar (op : String) (args : List StmtExprMd) : ElabM (FGLProducer × HighType) := do
  match args with
  | [a, b] =>
    let xVar ← freshVar "sc"
    let condVar ← freshVar "cond"
    let (aProd, _) ← synthProducer a
    let (bProd, _) ← synthProducer b
    if op == "PAnd" then
      -- PAnd: truthy → evaluate b, falsy → return a's value
      pure (.letProd xVar (.TCore "Any") aProd
        (.callWithError "Any_to_bool" [.var xVar] condVar (condVar ++ "_err")
          .TBool (.TCore "Error")
          (.ifThenElse (.var condVar)
            bProd
            (.returnValue (.var xVar)))),
        .TCore "Any")
    else
      -- POr: truthy → return a's value, falsy → evaluate b
      pure (.letProd xVar (.TCore "Any") aProd
        (.callWithError "Any_to_bool" [.var xVar] condVar (condVar ++ "_err")
          .TBool (.TCore "Error")
          (.ifThenElse (.var condVar)
            (.returnValue (.var xVar))
            bProd)),
        .TCore "Any")
  | _ =>
    -- Fallback: shouldn't happen (PAnd/POr always have exactly 2 args)
    let argVals ← args.mapM (fun a => do let (v, _) ← synthValue a; pure v)
    pure (.call op argVals, .TCore "Any")

-- Task 13: elaborateBlock (ARCHITECTURE.md §"Blocks as Nested Lets")
-- Per ARCHITECTURE.md §"Blocks as Nested Lets (CBV → FGCBV)":
-- foldr over stmts. Each elaborated via synthProducer, sequenced via sequenceProducers.

/-- Elaborate a block of statements into a single producer.
    Per ARCHITECTURE.md §"Blocks as Nested Lets (CBV → FGCBV)" — foldr, Levy §3.2. -/
partial def elaborateBlock (stmts : List StmtExprMd) : ElabM (FGLProducer × HighType) := do
  match stmts with
  | [] => pure (.unit, .TVoid)
  | [last] => synthProducer last
  | stmt :: rest =>
    let (firstProd, _) ← synthProducer stmt
    let (restProd, restTy) ← elaborateBlock rest
    pure (sequenceProducers firstProd restProd, restTy)

end -- mutual

/-! ## Tasks 16-17: projectValue + splitProducer + projectBody (mutually recursive)

Per ARCHITECTURE.md §"Projection (FineGrainLaurel → Laurel)":
- projectValue: FGLValue → StmtExprMd (one case per constructor)
- splitProducer: FGLProducer → (List StmtExprMd × StmtExprMd) (bind reassociation)
- projectBody: FGLProducer → StmtExprMd (split + wrap in Block)
ALL output via `mkLaurel md` (ARCHITECTURE.md §"Metadata: Smart Constructors").
-/

mutual

/-- Project an FGLValue to a Laurel StmtExprMd.
    Per ARCHITECTURE.md §"Projection" — forgetful functor, one case per constructor.
    All output via mkLaurel md (ARCHITECTURE.md §"Metadata: Smart Constructors"). -/
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

/-- Split a producer into (prefix statements, terminal expression).
    Per ARCHITECTURE.md §"Implementation: Projection as Bind Reassociation":
    THE monad law: `(m >>= f) >>= g = m >>= (λx. f x >>= g)`.
    The letProd case IS the monad law applied as a syntactic transformation. -/
partial def splitProducer (md : Imperative.MetaData Core.Expression) : FGLProducer → (List StmtExprMd × StmtExprMd)
  | .returnValue v => ([], projectValue md v)
  | .call name args =>
      ([], mkLaurel md (.StaticCall (Identifier.mk name none) (args.map (projectValue md))))
  | .letProd x ty inner body =>
      let (innerStmts, innerExpr) := splitProducer md inner
      let xDecl := mkLaurel md (.LocalVariable (Identifier.mk x none) (mkHighTypeMd md ty) (some innerExpr))
      let (bodyStmts, bodyExpr) := splitProducer md body
      (innerStmts ++ [xDecl] ++ bodyStmts, bodyExpr)
  | .assign target val body =>
      let stmt := mkLaurel md (.Assign [projectValue md target] (projectValue md val))
      let (bodyStmts, bodyExpr) := splitProducer md body
      ([stmt] ++ bodyStmts, bodyExpr)
  | .varDecl name ty init body =>
      let decl := mkLaurel md (.LocalVariable (Identifier.mk name none) (mkHighTypeMd md ty) (some (projectValue md init)))
      let (bodyStmts, bodyExpr) := splitProducer md body
      ([decl] ++ bodyStmts, bodyExpr)
  | .ifThenElse cond thn els =>
      ([], mkLaurel md (.IfThenElse (projectValue md cond) (projectBody md thn) (some (projectBody md els))))
  | .whileLoop cond body after =>
      let whileStmt := mkLaurel md (.While (projectValue md cond) [] none (projectBody md body))
      let (afterStmts, afterExpr) := splitProducer md after
      ([whileStmt] ++ afterStmts, afterExpr)
  | .assert cond body =>
      let stmt := mkLaurel md (.Assert (projectValue md cond))
      let (bodyStmts, bodyExpr) := splitProducer md body
      ([stmt] ++ bodyStmts, bodyExpr)
  | .assume cond body =>
      let stmt := mkLaurel md (.Assume (projectValue md cond))
      let (bodyStmts, bodyExpr) := splitProducer md body
      ([stmt] ++ bodyStmts, bodyExpr)
  | .callWithError callee args rv ev rTy eTy body =>
      let callExpr := mkLaurel md (.StaticCall (Identifier.mk callee none) (args.map (projectValue md)))
      let rvDecl := mkLaurel md (.LocalVariable (Identifier.mk rv none) (mkHighTypeMd md rTy) (some callExpr))
      let evDecl := mkLaurel md (.LocalVariable (Identifier.mk ev none) (mkHighTypeMd md eTy) (some (mkLaurel md (.StaticCall (Identifier.mk "NoError" none) []))))
      let (bodyStmts, bodyExpr) := splitProducer md body
      ([rvDecl, evDecl] ++ bodyStmts, bodyExpr)
  | .exit label => ([mkLaurel md (.Exit label)], mkLaurel md (.LiteralBool true))
  | .labeledBlock label body =>
      ([mkLaurel md (.Block [projectBody md body] (some label))], mkLaurel md (.LiteralBool true))
  | .newObj className rv ty body =>
      let newExpr := mkLaurel md (.New (Identifier.mk className none))
      let decl := mkLaurel md (.LocalVariable (Identifier.mk rv none) (mkHighTypeMd md ty) (some newExpr))
      let (bodyStmts, bodyExpr) := splitProducer md body
      ([decl] ++ bodyStmts, bodyExpr)
  | .seq first second =>
      let (fStmts, _) := splitProducer md first
      let (sStmts, sExpr) := splitProducer md second
      (fStmts ++ sStmts, sExpr)
  | .unit => ([], mkLaurel md (.LiteralBool true))

/-- Project a producer body to a Laurel Block.
    Per ARCHITECTURE.md §"Projection": projectBody calls splitProducer, wraps in Block. -/
partial def projectBody (md : Imperative.MetaData Core.Expression) (prod : FGLProducer) : StmtExprMd :=
  let (stmts, terminal) := splitProducer md prod
  mkLaurel md (.Block (stmts ++ [terminal]) none)

end -- mutual (projectValue, splitProducer, projectBody)

/-! ## Task 18: fullElaborate (IMPLEMENTATION_PLAN.md §"Task 18")

For each proc in program.staticProcedures:
- Match body as .Transparent bodyExpr
- Get returnType from proc.outputs[0].type.val (or .TCore "Any")
- Set ElabState { freshCounter := 0, currentProcReturnType := retTy }
- Run synthProducer bodyExpr with typeEnv in reader
- Project result via projectBody bodyExpr.md fglProd
- Rebuild proc with .Transparent projected
- On ElabError: catch and return the proc unchanged (graceful degradation)
-/

/-- Entry point: fullElaborate (called by PySpecPipeline).
    Per IMPLEMENTATION_PLAN.md §"Task 18": elaborate each proc body, project back to Laurel.
    currentProcReturnType from proc.outputs. Graceful degradation on ElabError. -/
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
        -- Graceful degradation: return proc unchanged on elaboration error
        procs := procs ++ [proc]
    | _ => procs := procs ++ [proc]
  pure { program with staticProcedures := procs }

end -- public section

end Strata.FineGrainLaurel
