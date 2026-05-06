/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.Languages.FineGrainLaurel.FineGrainLaurel
public import Strata.Languages.Laurel.Laurel
public import Strata.Languages.Laurel.HeapParameterizationConstants
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

/-! ## Task 22: LowType + eraseType (ARCHITECTURE.md §"Two Type Systems: HighType and LowType")

Per ARCHITECTURE.md: "Elaboration is a typed translation between two type systems
(Harper & Morrisett 1995, TIL). The source system has class identity. The target
system has a uniform heap representation."

UserDefined is UNREPRESENTABLE in LowType. If elaboration accidentally tries to emit
a UserDefined in FGL output, it's a Lean type error. The type system enforces the
erasure boundary.
-/

/-- LowType: FGL's type system (elaboration's output).
    Per ARCHITECTURE.md §"Two Type Systems": NO UserDefined. All class instances are Composite.
    UserDefined is unrepresentable — Lean enforces the erasure boundary. -/
inductive LowType where
  | TInt | TBool | TString | TFloat64 | TVoid
  | TCore (name : String)
  deriving Inhabited, Repr, BEq

/-- Type translation: HighType → LowType (total, deterministic).
    Per ARCHITECTURE.md §"The type translation (eraseType)":
    Every HighType maps to a LowType. UserDefined always becomes Composite. -/
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

/-- Equality on LowTypes (reflexivity axiom in the erased world).
    Per ARCHITECTURE.md §"MODE CORRECTNESS": Only used inside checkValue/checkProducer
    as the short-circuit (A <: A). -/
def lowTypesEqual (a b : LowType) : Bool :=
  match a, b with
  | .TInt, .TInt | .TBool, .TBool | .TString, .TString
  | .TFloat64, .TFloat64 | .TVoid, .TVoid => true
  | .TCore n1, .TCore n2 => n1 == n2
  | _, _ => false

/-- Lift a LowType back to HighType (for projection to Laurel which uses HighType).
    Per IMPLEMENTATION_PLAN.md §"Task 9 Note": Projection outputs Laurel nodes with
    HighType (for the LocalVariable type annotations). -/
def liftType : LowType → HighType
  | .TInt => .TInt
  | .TBool => .TBool
  | .TString => .TString
  | .TFloat64 => .TFloat64
  | .TVoid => .TVoid
  | .TCore name => .TCore name

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
  | letProd (var : String) (ty : LowType) (prod : FGLProducer) (body : FGLProducer)
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
  | newObj (className : String) (resultVar : String) (ty : LowType) (body : FGLProducer)
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

/-- Extend Γ with a variable binding. Used at binding sites (parameters, locals).
    This is how Γ grows as elaboration descends under binders — standard type theory. -/
def extendEnv (name : String) (ty : HighType) (action : ElabM α) : ElabM α := do
  withReader (fun env => { env with names := env.names.insert name (.variable ty) }) action

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
    Γ ⊢_v e ⇒ A    A <: B  ⊢  Γ ⊢_v upcast(e) ⇐ B
    Now operates on LowType (Task 25): UserDefined → Any becomes TCore "Composite" → Any
    because eraseType already converted it. -/
def canUpcast (actual expected : LowType) : Option (FGLValue → FGLValue) :=
  match actual, expected with
  | .TInt, .TCore "Any" => some .fromInt
  | .TBool, .TCore "Any" => some .fromBool
  | .TString, .TCore "Any" => some .fromStr
  | .TFloat64, .TCore "Any" => some .fromFloat
  | .TCore "Composite", .TCore "Any" => some .fromComposite
  | .TCore "ListAny", .TCore "Any" => some .fromListAny
  | .TCore "DictStrAny", .TCore "Any" => some .fromDictStrAny
  | .TVoid, .TCore "Any" => some (fun _ => .fromNone)
  | _, _ => none

/-- Can we narrow actual to expected? Returns the downcast procedure name.
    Per ARCHITECTURE.md §"Narrowing (producer-level, fallible)":
    Γ ⊢_v e ⇒ A    A ▷ B  ⊢  Γ ⊢_p narrow(e) : B
    Now operates on LowType (Task 25). -/
def canNarrow (actual expected : LowType) : Option String :=
  match actual, expected with
  | .TCore "Any", .TBool => some "Any_to_bool"
  | .TCore "Any", .TInt => some "Any..as_int!"
  | .TCore "Any", .TString => some "Any..as_string!"
  | .TCore "Any", .TFloat64 => some "Any..as_float!"
  | .TCore "Any", .TCore "Composite" => some "Any..as_Composite!"
  | _, _ => none

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

/-! ## The Mutual Block: CBV→FGCBV Embedding (ARCHITECTURE.md §"Elaboration = CBV→FGCBV Embedding")

Per ARCHITECTURE.md: "Elaboration IS the standard embedding of CBV (Laurel) into FGCBV
(FineGrainLaurel). This embedding is deterministic — no choices, no routing decisions.
Every CBV term has exactly one FGCBV translation."

Key properties:
- **Every subexpression is elaborated as a PRODUCER** (⟦e⟧ always produces a producer)
- **Every intermediate result is BOUND** (to x. = letProd)
- **Coercions applied to BOUND VALUES** (x₁, x₂, ... are values after binding)
- **synthValue only handles ATOMS** (literals, variables — things that ARE values)
- **No routing decision** — the embedding is uniform
-/

/-- Apply value-level upcast (subsumption short-circuit + coercion).
    Per ARCHITECTURE.md §"Subsumption": reflexivity short-circuit, then canUpcast.
    This is a PURE function — no monadic effects. Operates on bound values (atoms). -/
private def applyUpcast (val : FGLValue) (actual expected : LowType) : FGLValue :=
  if lowTypesEqual actual expected then val
  else match canUpcast actual expected with
    | some c => c val
    | none => val  -- no upcast available; narrowing handled at producer level

mutual

/-- Synthesize a value and its type. ONLY atoms (Identifier + Literals).
    Per ARCHITECTURE.md §"synthValue handles ONLY atoms": Identifier, Literal. Nothing else.
    Per IMPLEMENTATION_PLAN.md §"Task 6": synthValue handles ONLY: LiteralInt, LiteralBool,
    LiteralString, Identifier. NOTHING ELSE. -/
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
  | _ => throw (ElabError.unsupported "synthValue called on non-atom")

/-- Check an atom against an expected type, inserting value-level upcast.
    Per ARCHITECTURE.md §"Value checking (subsumption — the ONLY value checking rule)":
    Γ ⊢_v v ⇒ A, A <: B ~~> c ⊢ Γ ⊢_v c(v) ⇐ B
    ONLY called on atoms (bound variables, literals). The caller ensures this by
    binding compound expressions first via elaborateExpr + letProd. -/
partial def checkValue (expr : StmtExprMd) (expected : HighType) : ElabM FGLValue := do
  let (val, actual) ← synthValue expr
  let expectedLow := eraseType expected
  pure (applyUpcast val actual expectedLow)

/-- The CBV→FGCBV embedding entry point for any subexpression.
    Per ARCHITECTURE.md §"The embedding": ⟦e⟧ always produces a producer.
    - Atom → (.returnValue val, ty) — trivial binding (short-circuit)
    - Compound → delegates to synthProducer
    Per IMPLEMENTATION_PLAN.md §"Task 8": elaborateExpr is the UNIVERSAL entry point. -/
partial def elaborateExpr (expr : StmtExprMd) : ElabM (FGLProducer × LowType) := do
  match expr.val with
  | .LiteralInt _ | .LiteralBool _ | .LiteralString _ | .Identifier _ =>
    -- Atom: trivially a producer that returns the value
    let (val, ty) ← synthValue expr
    pure (.returnValue val, ty)
  | _ =>
    -- Compound: delegate to synthProducer
    synthProducer expr

/-- Synthesize a producer and its type.
    Per ARCHITECTURE.md §"Producer synthesis" rules:
    - f(v₁,...,vₙ): elaborate args as producers, bind each, coerce bound values, call
    - new Foo: heap allocation
    - x := v: elaborate RHS, bind, coerce to target type, assign
    - assert/assume v: elaborate condition, bind, narrow to bool
    - while v do M: elaborate condition, bind, narrow, loop body
    Per IMPLEMENTATION_PLAN.md §"Task 9": THE CBV→FGCBV embedding for function application. -/
partial def synthProducer (expr : StmtExprMd) : ElabM (FGLProducer × LowType) := do
  match expr.val with
  -- StaticCall: THE CBV→FGCBV embedding for application.
  -- ⟦f(a₁,...,aₙ)⟧ = ⟦a₁⟧ to x₁. ... ⟦aₙ⟧ to xₙ. f(coerce(x₁,T₁), ..., coerce(xₙ,Tₙ))
  | .StaticCall callee args =>
    -- PAnd/POr → short-circuit desugaring (ARCHITECTURE.md §"Short-Circuit Desugaring in FGL")
    if callee.text == "PAnd" || callee.text == "POr" then
      shortCircuitDesugar callee.text args
    else
      let sig ← lookupFuncSig callee.text
      let paramTypes : List LowType := match sig with
        | some s => s.params.map (fun (_, ty) => eraseType ty)
        | none => args.map (fun _ => LowType.TCore "Any")
      let retTy : LowType := match sig with
        | some s => eraseType s.returnType
        | none => .TCore "Any"
      -- Elaborate each arg as a producer, accumulate bindings
      let mut bindings : List (String × LowType × FGLProducer) := []
      let mut coercedArgs : List FGLValue := []
      for (arg, paramTy) in args.zip paramTypes do
        let (argProd, argTy) ← elaborateExpr arg
        let argVar ← freshVar "arg"
        bindings := bindings ++ [(argVar, argTy, argProd)]
        -- Coerce the BOUND value (atom .var argVar) against param type
        coercedArgs := coercedArgs ++ [applyUpcast (.var argVar) argTy paramTy]
      -- The call itself (with or without error output)
      let callProd ← if (match sig with | some s => s.hasErrorOutput | none => false) then do
        let rv ← freshVar "result"
        let ev ← freshVar "err"
        pure (.callWithError callee.text coercedArgs rv ev retTy (.TCore "Error")
               (.returnValue (.var rv)))
      else
        pure (.call callee.text coercedArgs)
      -- Wrap in letProd chain (right-fold: outermost binding first)
      let result := bindings.foldr (fun (name, ty, prod) acc => .letProd name ty prod acc) callProd
      pure (result, retTy)

  -- Assign: elaborate RHS as producer, bind, coerce bound value to target type, assign.
  -- Per ARCHITECTURE.md: v ⇐ Γ(x) ⊢ Γ ⊢_p (x := v) ⇒ TVoid
  | .Assign targets value =>
    match targets with
    | [target] =>
      let targetTy ← match target.val with
        | .Identifier id =>
          match (← lookupEnv id.text) with
          | some (.variable t) => pure (eraseType t)
          | _ => pure (.TCore "Any")
        | _ => pure (.TCore "Any")
      let (targetVal, _) ← synthValue target
      -- Elaborate RHS, bind, coerce the bound value
      let (rhsProd, rhsTy) ← elaborateExpr value
      let rhsVar ← freshVar "rhs"
      -- Per ARCHITECTURE.md: three cases at CHECK boundary
      if lowTypesEqual rhsTy targetTy then
        -- Reflexivity: no coercion
        pure (.letProd rhsVar rhsTy rhsProd
               (.assign targetVal (.var rhsVar) .unit), .TVoid)
      else match canUpcast rhsTy targetTy with
        | some coerce =>
          -- Upcast (value-level): e.g., int → Any via fromInt
          pure (.letProd rhsVar rhsTy rhsProd
                 (.assign targetVal (coerce (.var rhsVar)) .unit), .TVoid)
        | none => match canNarrow rhsTy targetTy with
          | some narrowFn =>
            -- Narrow (producer-level): e.g., Any → int via Any..as_int!
            let narrowedVar ← freshVar "narrowed"
            pure (.letProd rhsVar rhsTy rhsProd
                   (.callWithError narrowFn [.var rhsVar] narrowedVar (narrowedVar ++ "_err")
                     targetTy (.TCore "Error")
                     (.assign targetVal (.var narrowedVar) .unit)), .TVoid)
          | none =>
            -- No coercion: pass through (compatible types not in table)
            pure (.letProd rhsVar rhsTy rhsProd
                   (.assign targetVal (.var rhsVar) .unit), .TVoid)
    | _ => pure (.unit, .TCore "Any")  -- multi-target: ARCHITECTURE GAP

  -- LocalVariable: elaborate init as producer, bind, coerce to declared type.
  -- Per ARCHITECTURE.md: v ⇐ T, Γ,x:T ⊢_p body ⇐ C ⊢ Γ ⊢_p (var x:T := v; body) ⇐ C
  | .LocalVariable nameId typeMd initOpt =>
    let declTy := eraseType typeMd.val
    match initOpt with
    | some init =>
      let (initProd, initTy) ← elaborateExpr init
      let initVar ← freshVar "init"
      -- Per ARCHITECTURE.md: three cases at CHECK boundary
      if lowTypesEqual initTy declTy then
        -- Reflexivity: no coercion (e.g., int literal into int var)
        pure (.letProd initVar initTy initProd
               (.varDecl nameId.text declTy (.var initVar) .unit), declTy)
      else match canUpcast initTy declTy with
        | some coerce =>
          -- Upcast (value-level): e.g., int → Any
          pure (.letProd initVar initTy initProd
                 (.varDecl nameId.text declTy (coerce (.var initVar)) .unit), declTy)
        | none => match canNarrow initTy declTy with
          | some narrowFn =>
            -- Narrow (producer-level): e.g., Any → int
            let narrowedVar ← freshVar "narrowed"
            pure (.letProd initVar initTy initProd
                   (.callWithError narrowFn [.var initVar] narrowedVar (narrowedVar ++ "_err")
                     declTy (.TCore "Error")
                     (.varDecl nameId.text declTy (.var narrowedVar) .unit)), declTy)
          | none =>
            -- No coercion: pass through
            pure (.letProd initVar initTy initProd
                   (.varDecl nameId.text declTy (.var initVar) .unit), declTy)
    | none => pure (.varDecl nameId.text declTy (.var "_uninit") .unit, declTy)

  -- IfThenElse: elaborate condition as producer, bind, coerce/narrow to bool.
  -- Per ARCHITECTURE.md: v ⇐ bool, Γ ⊢_p M ⇐ C, Γ ⊢_p N ⇐ C
  | .IfThenElse cond thenBranch elseBranch =>
    let (condProd, condTy) ← elaborateExpr cond
    let condVar ← freshVar "cond"
    let (thenProd, thenTy) ← synthProducer thenBranch
    let elsProd ← match elseBranch with
      | some e => do let (p, _) ← synthProducer e; pure p
      | none => pure .unit
    -- Subsume bound condition value to bool
    if lowTypesEqual condTy .TBool then
      -- Already bool: use directly
      pure (.letProd condVar condTy condProd
             (.ifThenElse (.var condVar) thenProd elsProd), thenTy)
    else match canNarrow condTy .TBool with
      | some narrowFn =>
        -- Narrowing: produces a producer, need another bind to get Value(bool)
        let boolVar ← freshVar "boolCond"
        pure (.letProd condVar condTy condProd
               (.callWithError narrowFn [.var condVar] boolVar (boolVar ++ "_err")
                 .TBool (.TCore "Error")
                 (.ifThenElse (.var boolVar) thenProd elsProd)), thenTy)
      | none =>
        -- No narrowing found: try upcast (unlikely for bool), else use as-is
        let coerced := applyUpcast (.var condVar) condTy .TBool
        pure (.letProd condVar condTy condProd
               (.ifThenElse coerced thenProd elsProd), thenTy)

  -- While: elaborate condition, bind, narrow to bool, body synths TVoid.
  -- Per ARCHITECTURE.md: v ⇐ bool, Γ ⊢_p M ⇐ TVoid ⊢ Γ ⊢_p (while v do M) ⇒ TVoid
  | .While cond _invariants _decreases body =>
    let (condProd, condTy) ← elaborateExpr cond
    let condVar ← freshVar "cond"
    let (bodyProd, _) ← synthProducer body
    if lowTypesEqual condTy .TBool then
      pure (.letProd condVar condTy condProd
             (.whileLoop (.var condVar) bodyProd .unit), .TVoid)
    else match canNarrow condTy .TBool with
      | some narrowFn =>
        let boolVar ← freshVar "boolCond"
        pure (.letProd condVar condTy condProd
               (.callWithError narrowFn [.var condVar] boolVar (boolVar ++ "_err")
                 .TBool (.TCore "Error")
                 (.whileLoop (.var boolVar) bodyProd .unit)), .TVoid)
      | none =>
        let coerced := applyUpcast (.var condVar) condTy .TBool
        pure (.letProd condVar condTy condProd
               (.whileLoop coerced bodyProd .unit), .TVoid)

  -- Assert: elaborate condition, bind, narrow to bool.
  -- Per ARCHITECTURE.md: v ⇐ bool ⊢ Γ ⊢_p (assert v) ⇒ TVoid
  | .Assert condition =>
    let (condProd, condTy) ← elaborateExpr condition
    let condVar ← freshVar "cond"
    if lowTypesEqual condTy .TBool then
      pure (.letProd condVar condTy condProd
             (.assert (.var condVar) .unit), .TVoid)
    else match canNarrow condTy .TBool with
      | some narrowFn =>
        let boolVar ← freshVar "boolCond"
        pure (.letProd condVar condTy condProd
               (.callWithError narrowFn [.var condVar] boolVar (boolVar ++ "_err")
                 .TBool (.TCore "Error")
                 (.assert (.var boolVar) .unit)), .TVoid)
      | none =>
        let coerced := applyUpcast (.var condVar) condTy .TBool
        pure (.letProd condVar condTy condProd
               (.assert coerced .unit), .TVoid)

  -- Assume: elaborate condition, bind, narrow to bool.
  -- Per ARCHITECTURE.md: v ⇐ bool ⊢ Γ ⊢_p (assume v) ⇒ TVoid
  | .Assume condition =>
    let (condProd, condTy) ← elaborateExpr condition
    let condVar ← freshVar "cond"
    if lowTypesEqual condTy .TBool then
      pure (.letProd condVar condTy condProd
             (.assume (.var condVar) .unit), .TVoid)
    else match canNarrow condTy .TBool with
      | some narrowFn =>
        let boolVar ← freshVar "boolCond"
        pure (.letProd condVar condTy condProd
               (.callWithError narrowFn [.var condVar] boolVar (boolVar ++ "_err")
                 .TBool (.TCore "Error")
                 (.assume (.var boolVar) .unit)), .TVoid)
      | none =>
        let coerced := applyUpcast (.var condVar) condTy .TBool
        pure (.letProd condVar condTy condProd
               (.assume coerced .unit), .TVoid)

  -- Block: elaborate each statement, sequence via substitution of .unit continuations.
  | .Block stmts label =>
    let (prod, ty) ← elaborateBlock stmts
    match label with
    | some l => pure (.labeledBlock l prod, ty)
    | none => pure (prod, ty)

  -- Exit: terminal, no continuation.
  | .Exit target => pure (.exit target, .TVoid)

  -- New: heap allocation. Per ARCHITECTURE.md: Γ ⊢_p (new Foo) ⇒ Composite
  -- Per IMPLEMENTATION_PLAN.md §Task 26: New "Foo" → MkComposite(freshRef, Foo_TypeTag())
  | .New classId =>
    let refVar ← freshVar "ref"
    let objVar ← freshVar "obj"
    let prod := FGLProducer.letProd refVar .TInt (.call "Heap..nextReference!" [.var "$heap"])
      (.letProd objVar (.TCore "Composite")
        (.call "MkComposite" [.var refVar, .staticCall (classId.text ++ "_TypeTag") []])
        (.returnValue (.var objVar)))
    pure (prod, .TCore "Composite")

  -- Return: elaborate return value, bind, coerce to proc return type.
  -- Per ARCHITECTURE.md: v ⇐ procReturnType ⊢ Γ ⊢_p (return v) ⇐ procReturnType
  | .Return valueOpt =>
    let retTy := (← get).currentProcReturnType
    let retTyLow := eraseType retTy
    match valueOpt with
    | some v =>
      let (valProd, valTy) ← elaborateExpr v
      let valVar ← freshVar "ret"
      -- Per ARCHITECTURE.md: three cases at CHECK boundary
      if lowTypesEqual valTy retTyLow then
        -- Reflexivity
        pure (.letProd valVar valTy valProd
               (.returnValue (.var valVar)), retTyLow)
      else match canUpcast valTy retTyLow with
        | some coerce =>
          -- Upcast (value-level)
          pure (.letProd valVar valTy valProd
                 (.returnValue (coerce (.var valVar))), retTyLow)
        | none => match canNarrow valTy retTyLow with
          | some narrowFn =>
            -- Narrow (producer-level)
            let narrowedVar ← freshVar "narrowed"
            pure (.letProd valVar valTy valProd
                   (.callWithError narrowFn [.var valVar] narrowedVar (narrowedVar ++ "_err")
                     retTyLow (.TCore "Error")
                     (.returnValue (.var narrowedVar))), retTyLow)
          | none =>
            -- No coercion: pass through
            pure (.letProd valVar valTy valProd
                   (.returnValue (.var valVar)), retTyLow)
    | none => pure (.returnValue .fromNone, .TVoid)

  -- FieldSelect: producer (may read heap).
  -- Per ARCHITECTURE.md routing table: FieldSelect → PRODUCER (on heap) / VALUE (non-heap)
  | .FieldSelect obj field =>
    let (objProd, objTy) ← elaborateExpr obj
    let objVar ← freshVar "obj"
    if lowTypesEqual objTy (.TCore "Composite") then
      -- Heap field access: readField(heap, obj, field)
      let resultTy := LowType.TCore "Box"
      pure (.letProd objVar objTy objProd
             (.call "readField" [.var "$heap", .var objVar, .staticCall (field.text ++ "_Field") []]), resultTy)
    else
      -- Non-heap: treat as value-level field access
      let fieldTy ← match obj.val with
        | .Identifier id =>
          match (← lookupEnv id.text) with
          | some (.variable (.UserDefined className)) =>
            lookupFieldType className.text field.text
          | _ => pure (.TCore "Any")
        | _ => pure (.TCore "Any")
      pure (.letProd objVar objTy objProd
             (.returnValue (.fieldAccess (.var objVar) field.text)), eraseType fieldTy)

  -- Hole: unknown expression, pass through
  | .Hole _ _ => pure (.returnValue (.var "_hole"), .TCore "Any")

  -- Fallback for remaining forms: wrap in returnValue if possible
  | _ => pure (.returnValue (.var "_unsupported"), .TCore "Any")

/-- Check a producer against an expected type, inserting narrowing as needed.
    Per ARCHITECTURE.md producer checking rules + narrowing fallback:
    Γ ⊢_v v ⇒ A, A ▷ B ~~> n ⊢ Γ ⊢_p n(v) ⇐ B
    Per IMPLEMENTATION_PLAN.md §"Task 14". -/
partial def checkProducer (expr : StmtExprMd) (expected : LowType) : ElabM FGLProducer := do
  let (prod, actual) ← synthProducer expr
  if lowTypesEqual actual expected then return prod
  -- Bind the producer to get a value, then coerce
  let tmpVar ← freshVar "tmp"
  match canUpcast actual expected with
  | some coerce =>
    -- Upcast (value-level): bind then wrap
    pure (.letProd tmpVar actual prod (.returnValue (coerce (.var tmpVar))))
  | none => match canNarrow actual expected with
    | some narrowFn =>
      -- Narrow (producer-level): bind, then callWithError
      let resultVar ← freshVar "narrowed"
      pure (.letProd tmpVar actual prod
             (.callWithError narrowFn [.var tmpVar] resultVar (resultVar ++ "_err")
               expected (.TCore "Error") (.returnValue (.var resultVar))))
    | none =>
      -- No coercion available: return as-is (compatible types not in table)
      pure prod

/-- Short-circuit desugaring for PAnd/POr.
    Per ARCHITECTURE.md §"Short-Circuit Desugaring in FGL":
    PAnd: evaluate a, narrow to bool, if truthy → evaluate b, else return a's value
    POr: evaluate a, narrow to bool, if truthy → return a's value, else evaluate b
    Per IMPLEMENTATION_PLAN.md §"Task 15": exact FGL transcription. -/
partial def shortCircuitDesugar (op : String) (args : List StmtExprMd) : ElabM (FGLProducer × LowType) := do
  match args with
  | [a, b] =>
    let xVar ← freshVar "sc"
    let condVar ← freshVar "cond"
    let (aProd, aTy) ← elaborateExpr a
    let (bProd, _) ← elaborateExpr b
    -- Per ARCHITECTURE.md §"Short-Circuit Desugaring in FGL":
    -- The bound value xVar needs to be Any for Any_to_bool to apply.
    -- If aTy is not Any, upcast it before binding.
    let (bindProd, bindTy) :=
      if lowTypesEqual aTy (.TCore "Any") then (aProd, aTy)
      else match canUpcast aTy (.TCore "Any") with
        | some coerce =>
          -- Wrap: elaborate a, bind to tmp, upcast to Any
          let tmpProd := aProd
          -- We'll bind at aTy then upcast the bound var inside the letProd body.
          -- Actually simpler: just bind at the actual type and upcast in the Any_to_bool arg.
          (tmpProd, aTy)
        | none => (aProd, aTy)
    -- If aTy is already Any, use directly. Otherwise, upcast the bound value for Any_to_bool.
    let narrowArg : FGLValue :=
      if lowTypesEqual bindTy (.TCore "Any") then .var xVar
      else match canUpcast bindTy (.TCore "Any") with
        | some coerce => coerce (.var xVar)
        | none => .var xVar
    if op == "PAnd" then
      -- PAnd: truthy → evaluate b, falsy → return a's value
      pure (.letProd xVar bindTy bindProd
        (.callWithError "Any_to_bool" [narrowArg] condVar (condVar ++ "_err")
          .TBool (.TCore "Error")
          (.ifThenElse (.var condVar)
            bProd
            (.returnValue (.var xVar)))),
        .TCore "Any")
    else
      -- POr: truthy → return a's value, falsy → evaluate b
      pure (.letProd xVar bindTy bindProd
        (.callWithError "Any_to_bool" [narrowArg] condVar (condVar ++ "_err")
          .TBool (.TCore "Error")
          (.ifThenElse (.var condVar)
            (.returnValue (.var xVar))
            bProd)),
        .TCore "Any")
  | _ =>
    -- Fallback: shouldn't happen (PAnd/POr always have exactly 2 args)
    let argVals ← args.mapM (fun a => do let (v, _) ← synthValue a; pure v)
    pure (.call op argVals, .TCore "Any")

/-- Elaborate a block of statements into a single producer.
    Per ARCHITECTURE.md: blocks are sequenced via nested lets (CBV → FGCBV).
    Per IMPLEMENTATION_PLAN.md §"Task 13": foldr over stmts, sequenceProducers. -/
partial def elaborateBlock (stmts : List StmtExprMd) : ElabM (FGLProducer × LowType) := do
  match stmts with
  | [] => pure (.unit, .TVoid)
  | [last] => synthProducer last
  | stmt :: rest =>
    let (firstProd, _) ← synthProducer stmt
    -- Extend Γ at binding sites: LocalVariable introduces a name into scope for rest.
    -- This is standard type theory: Γ grows under binders.
    let elaborateRest := elaborateBlock rest
    let (restProd, restTy) ← match stmt.val with
      | .LocalVariable nameId typeMd _ =>
          extendEnv nameId.text typeMd.val elaborateRest
      | _ => elaborateRest
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
      let xDecl := mkLaurel md (.LocalVariable (Identifier.mk x none) (mkHighTypeMd md (liftType ty)) (some innerExpr))
      let (bodyStmts, bodyExpr) := splitProducer md body
      (innerStmts ++ [xDecl] ++ bodyStmts, bodyExpr)
  | .assign target val body =>
      let stmt := mkLaurel md (.Assign [projectValue md target] (projectValue md val))
      let (bodyStmts, bodyExpr) := splitProducer md body
      ([stmt] ++ bodyStmts, bodyExpr)
  | .varDecl name ty init body =>
      let decl := mkLaurel md (.LocalVariable (Identifier.mk name none) (mkHighTypeMd md (liftType ty)) (some (projectValue md init)))
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
      let rvDecl := mkLaurel md (.LocalVariable (Identifier.mk rv none) (mkHighTypeMd md (liftType rTy)) (some callExpr))
      let evDecl := mkLaurel md (.LocalVariable (Identifier.mk ev none) (mkHighTypeMd md (liftType eTy)) (some (mkLaurel md (.StaticCall (Identifier.mk "NoError" none) []))))
      let (bodyStmts, bodyExpr) := splitProducer md body
      ([rvDecl, evDecl] ++ bodyStmts, bodyExpr)
  | .exit label => ([mkLaurel md (.Exit label)], mkLaurel md (.LiteralBool true))
  | .labeledBlock label body =>
      ([mkLaurel md (.Block [projectBody md body] (some label))], mkLaurel md (.LiteralBool true))
  | .newObj className rv ty body =>
      let newExpr := mkLaurel md (.New (Identifier.mk className none))
      let decl := mkLaurel md (.LocalVariable (Identifier.mk rv none) (mkHighTypeMd md (liftType ty)) (some newExpr))
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

/-! ## Tasks 19-20: Heap Co-Operations (ARCHITECTURE.md §"Operations vs Co-Operations")

Per ARCHITECTURE.md: "Heap parameterization is precisely: turning heap operations
into co-operations in FineGrainLaurel — the heap is threaded as an explicit
parameter rather than being implicitly available."

Per IMPLEMENTATION_PLAN.md §Tasks 19-20:
- Phase 1: Analysis — collect reads/writes/callees per procedure
- Phase 2: Fixpoint propagation — transitive closure on call graph
- Phase 3: Signature rewriting — add Heap to inputs/outputs
- Type infrastructure — add Composite, Box, Field, Heap, TypeTag to program.types
-/

/-! ### Task 19: Heap Analysis (collect reads/writes/callees per procedure body)

Per IMPLEMENTATION_PLAN.md §Task 19:
- `.FieldSelect target _` → `readsHeap := true`
- `.New _` → `writesHeap := true`
- `.Assign [target] _` where `target.val` is `.FieldSelect _ _` → `writesHeap := true`
- `.StaticCall callee _` → record callee in `callees`

Reference: `HeapParameterization.lean` lines 48-80 does the same analysis.
-/

/-- Heap analysis result for a single procedure.
    Per IMPLEMENTATION_PLAN.md §Task 19. -/
structure HeapAnalysis where
  readsHeap : Bool := false
  writesHeap : Bool := false
  callees : List String := []

/-- Collect heap reads/writes/callees from a Laurel expression tree.
    Per IMPLEMENTATION_PLAN.md §Task 19 — walk procedure body collecting co-op evidence. -/
partial def collectHeapInfo (expr : StmtExprMd) : StateM HeapAnalysis Unit := do
  match expr.val with
  | .FieldSelect target _ =>
      modify fun s => { s with readsHeap := true }
      collectHeapInfo target
  | .New _ =>
      modify fun s => { s with writesHeap := true }
  | .StaticCall callee args =>
      modify fun s => { s with callees := callee.text :: s.callees }
      args.forM collectHeapInfo
  | .Assign targets value =>
      for target in targets do
        match target.val with
        | .FieldSelect _ _ => modify fun s => { s with writesHeap := true }
        | _ => pure ()
        collectHeapInfo target
      collectHeapInfo value
  | .IfThenElse c t e =>
      collectHeapInfo c
      collectHeapInfo t
      match e with | some x => collectHeapInfo x | none => pure ()
  | .Block stmts _ => stmts.forM collectHeapInfo
  | .LocalVariable _ _ initOpt =>
      match initOpt with | some x => collectHeapInfo x | none => pure ()
  | .While c _invs _ b =>
      collectHeapInfo c
      collectHeapInfo b
  | .Return v => match v with | some x => collectHeapInfo x | none => pure ()
  | .Assert c => collectHeapInfo c
  | .Assume c => collectHeapInfo c
  | _ => pure ()

/-- Analyze a single procedure for heap interactions.
    Per IMPLEMENTATION_PLAN.md §Task 19. -/
def analyzeHeap (proc : Strata.Laurel.Procedure) : HeapAnalysis :=
  match proc.body with
  | .Transparent bodyExpr => (collectHeapInfo bodyExpr).run {} |>.2
  | _ => {}

/-- Build heap analysis map for all procedures.
    Per IMPLEMENTATION_PLAN.md §Task 19. -/
def buildHeapAnalysis (procs : List Strata.Laurel.Procedure) : Std.HashMap String HeapAnalysis :=
  procs.foldl (fun acc proc =>
    acc.insert proc.name.text (analyzeHeap proc)) {}

/-! ### Task 20: Fixpoint Propagation + Signature Rewriting

Per IMPLEMENTATION_PLAN.md §Task 20:
- Phase 2a: Propagation via fixpoint on call graph
- Phase 2b: Signature rewriting (add Heap to inputs/outputs)
- Phase 2c: Call-site rewriting (prepend heap arg at call sites)
- Type infrastructure (add Composite, Box, Field, Heap, TypeTag to program.types)
-/

/-- Fixpoint propagation of heap reads/writes through the call graph.
    Per IMPLEMENTATION_PLAN.md §Task 20 Phase 2a:
    "If proc A calls proc B, and B reads/writes heap, then A reads/writes heap too."
    Uses fuel-bounded iteration. -/
def propagateHeapAnalysis (analysis : Std.HashMap String HeapAnalysis) : Std.HashMap String HeapAnalysis :=
  let fuel := analysis.size + 1
  let rec go (fuel : Nat) (current : Std.HashMap String HeapAnalysis) : Std.HashMap String HeapAnalysis :=
    match fuel with
    | 0 => current
    | fuel' + 1 =>
      let (next, changed) := current.fold (init := (current, false)) fun (acc, changed) procName info =>
        let (newReads, newWrites) := info.callees.foldl (fun (r, w) callee =>
          match current[callee]? with
          | some calleeInfo => (r || calleeInfo.readsHeap, w || calleeInfo.writesHeap)
          | none => (r, w)) (info.readsHeap, info.writesHeap)
        if newReads != info.readsHeap || newWrites != info.writesHeap then
          (acc.insert procName { info with readsHeap := newReads, writesHeap := newWrites }, true)
        else (acc, changed)
      if changed then go fuel' next else next
  go fuel analysis

/-- Rewrite a procedure's signature to add heap parameters.
    Per IMPLEMENTATION_PLAN.md §Task 20 Phase 2b:
    - writesHeap: add `$heap` to BOTH inputs AND outputs
    - readsHeap only: add `$heap` to inputs only -/
def rewriteProcSignature (proc : Strata.Laurel.Procedure) (info : HeapAnalysis) : Strata.Laurel.Procedure :=
  if info.writesHeap then
    let heapInParam : Strata.Laurel.Parameter := { name := "$heap_in", type := ⟨.THeap, #[]⟩ }
    let heapOutParam : Strata.Laurel.Parameter := { name := "$heap", type := ⟨.THeap, #[]⟩ }
    { proc with
      inputs := heapInParam :: proc.inputs
      outputs := heapOutParam :: proc.outputs }
  else if info.readsHeap then
    let heapParam : Strata.Laurel.Parameter := { name := "$heap", type := ⟨.THeap, #[]⟩ }
    { proc with inputs := heapParam :: proc.inputs }
  else proc

/-- Rewrite all procedure signatures based on heap analysis.
    Per IMPLEMENTATION_PLAN.md §Task 20 Phase 2b. -/
def rewriteSignatures (procs : List Strata.Laurel.Procedure)
    (analysis : Std.HashMap String HeapAnalysis) : List Strata.Laurel.Procedure :=
  procs.map fun proc =>
    match analysis[proc.name.text]? with
    | some info => rewriteProcSignature proc info
    | none => proc

/-- Add heap type infrastructure declarations to program.types.
    Per IMPLEMENTATION_PLAN.md §Task 20 "Type infrastructure declarations":
    Core needs Composite, Box, Field, Heap, TypeTag registered BEFORE it sees
    the prelude's `from_Composite` constructor on `Any`.

    Uses `heapConstants.types` (from HeapParameterizationConstants.lean) which provides:
    - Composite datatype: MkComposite(ref: int)
    - Heap datatype: MkHeap(data: Map Composite Map Field Box, nextReference: int)
    Plus minimal Field/Box/TypeTag datatypes for Core. -/
def addHeapTypeInfrastructure (program : Strata.Laurel.Program)
    (analysis : Std.HashMap String HeapAnalysis) : Strata.Laurel.Program :=
  -- Collect all field names from composite types in the program
  let fieldNames := program.types.foldl (fun acc td =>
    match td with
    | .Composite ct => acc ++ ct.fields.map (fun f => Identifier.mk (ct.name.text ++ "." ++ f.name.text) none)
    | _ => acc) ([] : List Identifier)
  -- Field datatype: enum of all qualified field names
  let fieldDatatype : Strata.Laurel.TypeDefinition :=
    .Datatype { name := "Field", typeArgs := [], constructors := fieldNames.map fun n => { name := n, args := [] } }
  -- TypeTag datatype: enum of all composite type names
  let typeTagNames := program.types.filterMap fun td =>
    match td with
    | .Composite ct => some ct.name
    | _ => none
  let typeTagDatatype : Strata.Laurel.TypeDefinition :=
    .Datatype { name := "TypeTag", typeArgs := [], constructors := typeTagNames.map fun n => { name := n, args := [] } }
  -- Box datatype: minimal set of constructors for field types that appear
  -- For now, include all primitive box constructors that the prelude/runtime may need
  let boxConstructors : List Strata.Laurel.DatatypeConstructor := [
    { name := "BoxInt", args := [{ name := "intVal", type := ⟨.TInt, #[]⟩ }] },
    { name := "BoxBool", args := [{ name := "boolVal", type := ⟨.TBool, #[]⟩ }] },
    { name := "BoxFloat64", args := [{ name := "float64Val", type := ⟨.TFloat64, #[]⟩ }] },
    { name := "BoxString", args := [{ name := "stringVal", type := ⟨.TString, #[]⟩ }] },
    { name := "BoxComposite", args := [{ name := "compositeVal", type := ⟨.UserDefined (Identifier.mk "Composite" none), #[]⟩ }] },
    { name := "BoxAny", args := [{ name := "anyVal", type := ⟨.TCore "Any", #[]⟩ }] }
  ]
  let boxDatatype : Strata.Laurel.TypeDefinition :=
    .Datatype { name := "Box", typeArgs := [], constructors := boxConstructors }
  -- heapConstants provides Composite + Heap + NotSupportedYet datatypes
  -- plus readField/updateField/increment procedures
  let heapTypeDefs := heapConstants.types
  let heapProcs := heapConstants.staticProcedures
  -- Rewrite heap procedures' signatures if they reference heap-touching procs
  let rewrittenProcs := rewriteSignatures program.staticProcedures analysis
  -- Type declarations ALWAYS added (prelude's Any references from_Composite).
  -- Heap procedures only when heap is used (otherwise Core chokes on the signatures).
  let hasHeapUsage := analysis.toList.any (fun (_, info) => info.readsHeap || info.writesHeap)
  let rewrittenProcs := rewriteSignatures program.staticProcedures analysis
  let finalProcs := if hasHeapUsage then heapProcs ++ rewrittenProcs else rewrittenProcs
  { program with
    types := heapTypeDefs ++ [fieldDatatype, boxDatatype, typeTagDatatype] ++ program.types
    staticProcedures := finalProcs
  }

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
    currentProcReturnType from proc.outputs. Graceful degradation on ElabError.

    Per IMPLEMENTATION_PLAN.md §Tasks 19-20 (integrated):
    1. Run elaboration (existing: synthProducer + project)
    2. Run heap analysis on the elaborated program
    3. Run fixpoint propagation
    4. Rewrite signatures for heap-touching procs
    5. Add type infrastructure declarations to program.types
    6. Return the final program -/
def fullElaborate (typeEnv : Strata.Python.Resolution.TypeEnv)
    (program : Strata.Laurel.Program) : Except String Strata.Laurel.Program := do
  -- Step 1: Elaborate each procedure body (bidirectional walk + projection)
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
  let elaboratedProgram := { program with staticProcedures := procs }
  -- Steps 2-3: Heap analysis + fixpoint propagation (IMPLEMENTATION_PLAN.md §Tasks 19-20)
  let heapAnalysisRaw := buildHeapAnalysis elaboratedProgram.staticProcedures
  let heapAnalysis := propagateHeapAnalysis heapAnalysisRaw
  -- Steps 4-5: Signature rewriting + type infrastructure (IMPLEMENTATION_PLAN.md §Task 20)
  let finalProgram := addHeapTypeInfrastructure elaboratedProgram heapAnalysis
  pure finalProgram

end -- public section

end Strata.FineGrainLaurel
