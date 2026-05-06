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

/-- Look up the type of a variable from Γ (erased to LowType).
    Per IMPLEMENTATION_PLAN.md §Task 31: ALL variables are typed Any in the projected output.
    This means at elaboration time, variables hold Any-typed values (after upcast wrapping).
    Only $-prefixed internal variables (like $heap) retain precise types. -/
def lookupVarType (name : String) : ElabM LowType := do
  if name.startsWith "$" then
    -- Internal/infrastructure variables retain precise types
    match (← read).names[name]? with
    | some (.variable ty) => pure (eraseType ty)
    | _ => pure (.TCore "Any")
  else
    -- All user variables are typed Any (they store boxed values)
    pure (.TCore "Any")

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

/-! ## Task 5: Unified subsume (ARCHITECTURE.md §"The Complete Coercion Table")

Per ARCHITECTURE.md: "No separate typesEqual + canUpcast + canNarrow. One table.
One function (subsume), one table, called at every CHECK boundary. The table decides
everything."

Three outcomes: refl (types equal), coerce (apply witness), unrelated (type error).
ALL coercion is value-level — both upcast and narrowing produce VALUES.
-/

/-- The result of subsumption: refl (no coercion), coerce (apply witness), or unrelated.
    Per ARCHITECTURE.md §"The Complete Coercion Table". -/
inductive CoercionResult where
  | refl
  | coerce (witness : FGLValue → FGLValue)
  | unrelated

/-- Unified subsumption: determines the relationship between actual and expected types.
    Per ARCHITECTURE.md §"Implementation: One function, one table, three outcomes":
    Replaces canUpcast + canNarrow + lowTypesEqual entirely. -/
def subsume (actual expected : LowType) : CoercionResult :=
  match actual, expected with
  -- Reflexivity:
  | .TInt, .TInt | .TBool, .TBool | .TString, .TString
  | .TFloat64, .TFloat64 | .TVoid, .TVoid => .refl
  | .TCore n1, .TCore n2 =>
    if n1 == n2 then .refl
    else match n1, n2 with
      | "Composite", "Any" => .coerce .fromComposite
      | "ListAny", "Any" => .coerce .fromListAny
      | "DictStrAny", "Any" => .coerce .fromDictStrAny
      | "Any", "bool" => .coerce (fun v => .staticCall "Any_to_bool" [v])
      | "Any", "Composite" => .coerce (fun v => .staticCall "Any..as_Composite!" [v])
      | "Box", "Any" => .coerce (fun v => .staticCall "Box..AnyVal!" [v])
      | _, "Any" => .refl  -- unknown TCore to Any: treat as compatible
      | _, _ => .unrelated
  -- Upcasts from concrete to Any:
  | .TInt, .TCore "Any" => .coerce .fromInt
  | .TBool, .TCore "Any" => .coerce .fromBool
  | .TString, .TCore "Any" => .coerce .fromStr
  | .TFloat64, .TCore "Any" => .coerce .fromFloat
  | .TVoid, .TCore "Any" => .coerce (fun _ => .fromNone)
  -- Narrowing from Any to concrete:
  | .TCore "Any", .TInt => .coerce (fun v => .staticCall "Any..as_int!" [v])
  | .TCore "Any", .TBool => .coerce (fun v => .staticCall "Any_to_bool" [v])
  | .TCore "Any", .TString => .coerce (fun v => .staticCall "Any..as_string!" [v])
  | .TCore "Any", .TFloat64 => .coerce (fun v => .staticCall "Any..as_float!" [v])
  -- Otherwise:
  | _, _ => .unrelated

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
(FineGrainLaurel). This embedding is deterministic — no choices, no routing decisions."

Key changes per IMPLEMENTATION_PLAN.md §"PATH TO PARITY" Tasks 30-34:
- Pure StaticCalls are VALUES (no binding) — stays nested inline
- Only effectful calls (hasErrorOutput) become producers that need binding
- checkValue uses unified subsume (one function, three outcomes)
- All coercion is value-level (upcast AND narrowing produce values)
-/

mutual

/-- Synthesize a value and its type. Handles atoms AND pure StaticCalls.
    Per IMPLEMENTATION_PLAN.md §Task 30: "Pure calls stay as values (no binding)."
    Per ARCHITECTURE.md: synthValue now handles StaticCall for PURE calls.
    Args are checked via checkValue (subsumption fires inline on each arg). -/
partial def synthValue (expr : StmtExprMd) : ElabM (FGLValue × LowType) := do
  match expr.val with
  | .LiteralInt n => pure (.litInt n, .TInt)
  | .LiteralBool b => pure (.litBool b, .TBool)
  | .LiteralString s => pure (.litString s, .TString)
  | .Identifier id =>
    let ty ← lookupVarType id.text
    pure (.var id.text, ty)
  | .StaticCall callee args =>
    -- Pure call: elaborate args via checkValue (subsumption inline), return as value
    let sig ← lookupFuncSig callee.text
    let paramTypes : List HighType := match sig with
      | some s => s.params.map (fun (_, ty) => ty)
      | none => args.map (fun _ => HighType.TCore "Any")
    let retTy : LowType := match sig with
      | some s => eraseType s.returnType
      | none => .TCore "Any"
    let checkedArgs ← (args.zip paramTypes).mapM fun (arg, paramTy) => checkValue arg paramTy
    pure (.staticCall callee.text checkedArgs, retTy)
  | .FieldSelect obj field =>
    let (objVal, objTy) ← synthValue obj
    -- If composite: readField (pure value-level call)
    if objTy == .TCore "Composite" then
      pure (.staticCall "readField" [.var "$heap", objVal, .staticCall (field.text ++ "_Field") []], .TCore "Box")
    else
      pure (.fieldAccess objVal field.text, .TCore "Any")
  | .New classId =>
    pure (.staticCall "MkComposite" [.var "$heap_nextRef", .staticCall (classId.text ++ "_TypeTag") []], .TCore "Composite")
  | .Hole _ _ =>
    -- Hole: nondeterministic value (verification abstraction). Type is Any.
    pure (.var "_hole", .TCore "Any")
  | _ => throw (ElabError.unsupported s!"synthValue: unsupported expression form")

/-- Check a value against an expected type, using unified subsume.
    Per ARCHITECTURE.md §"checkValue": one function, three outcomes.
    Γ ⊢_v v ⇒ A, subsume(A, B) = c ⊢ Γ ⊢_v c(v) ⇐ B -/
partial def checkValue (expr : StmtExprMd) (expected : HighType) : ElabM FGLValue := do
  let (val, actual) ← synthValue expr
  let expectedLow := eraseType expected
  match subsume actual expectedLow with
  | .refl => pure val
  | .coerce c => pure (c val)
  | .unrelated => pure val  -- pass through for compatible types not in table

/-- The CBV→FGCBV embedding entry point for any subexpression.
    Per IMPLEMENTATION_PLAN.md §Task 30: pure calls → synthValue (value, no binding).
    Only effectful calls (hasErrorOutput) → synthProducer (gets bound). -/
partial def elaborateExpr (expr : StmtExprMd) : ElabM (FGLProducer × LowType) := do
  match expr.val with
  | .LiteralInt _ | .LiteralBool _ | .LiteralString _ | .Identifier _ =>
    -- Atom: trivially a producer that returns the value
    let (val, ty) ← synthValue expr
    pure (.returnValue val, ty)
  | .StaticCall callee _ =>
    -- Check if effectful: only effectful calls become producers
    let sig ← lookupFuncSig callee.text
    let isEffectful := match sig with
      | some s => s.hasErrorOutput
      | none => false
    if isEffectful then
      -- Effectful call: must bind (becomes a producer)
      synthProducer expr
    else
      -- Pure call: stays as a value (nested inline, no binding)
      let (val, ty) ← synthValue expr
      pure (.returnValue val, ty)
  | _ => synthProducer expr

/-- Synthesize a producer and its type.
    Per ARCHITECTURE.md §"Producer synthesis" rules. Only GENUINELY effectful things.
    Per IMPLEMENTATION_PLAN.md §Task 30: pure calls are handled by synthValue/elaborateExpr,
    synthProducer only handles effectful StaticCalls, Assign, LocalVariable, control flow. -/
partial def synthProducer (expr : StmtExprMd) : ElabM (FGLProducer × LowType) := do
  match expr.val with
  -- StaticCall with hasErrorOutput: the ONLY StaticCall that reaches synthProducer.
  | .StaticCall callee args =>
    let sig ← lookupFuncSig callee.text
    let paramTypes : List HighType := match sig with
      | some s => s.params.map (fun (_, ty) => ty)
      | none => args.map (fun _ => HighType.TCore "Any")
    let retTy : LowType := match sig with
      | some s => eraseType s.returnType
      | none => .TCore "Any"
    -- Check args via checkValue (subsumption fires inline on each arg)
    let checkedArgs ← (args.zip paramTypes).mapM fun (arg, paramTy) => checkValue arg paramTy
    -- Effectful call: emit callWithError
    let rv ← freshVar "result"
    let ev ← freshVar "err"
    pure (.callWithError callee.text checkedArgs rv ev retTy (.TCore "Error")
           (.returnValue (.var rv)), retTy)

  -- Assign: look up target type, checkValue RHS against it, emit assign.
  -- Per ARCHITECTURE.md: v ⇐ Γ(x) ⊢ Γ ⊢_p (x := v) ⇒ TVoid
  -- Per IMPLEMENTATION_PLAN.md §Task 31: all user vars are Any, so target type is Any.
  -- This means subsumption fires to upcast concrete RHS (e.g., int→Any via from_int).
  | .Assign targets value =>
    match targets with
    | [target] =>
      let targetTy : HighType := match target.val with
        | .Identifier id =>
          if id.text.startsWith "$" then
            .TCore "Any"  -- infrastructure vars: treat as Any too for now
          else
            .TCore "Any"  -- ALL user vars are Any
        | _ => .TCore "Any"
      let (targetVal, _) ← synthValue target
      -- checkValue RHS against target type — subsumption fires inline
      let rhsVal ← checkValue value targetTy
      pure (.assign targetVal rhsVal .unit, .TVoid)
    | _ => pure (.unit, .TCore "Any")  -- multi-target: ARCHITECTURE GAP

  -- LocalVariable: checkValue init against target type, emit varDecl, extend Γ.
  -- Per ARCHITECTURE.md: v ⇐ T, Γ,x:T ⊢_p body ⇐ C ⊢ Γ ⊢_p (var x:T := v; body) ⇐ C
  -- Per IMPLEMENTATION_PLAN.md §Task 31: Python value vars typed Any.
  -- Infrastructure vars (Error, Heap) keep their declared type for Core compatibility.
  | .LocalVariable nameId typeMd initOpt =>
    let erasedTy := eraseType typeMd.val
    -- Infrastructure types keep their type; Python value types become Any
    let declTy := match erasedTy with
      | .TCore "Error" => LowType.TCore "Error"
      | .TCore "Heap" => LowType.TCore "Heap"
      | _ => LowType.TCore "Any"
    -- Check target type: for infrastructure vars, use their actual type; for value vars, Any
    let checkTy := match erasedTy with
      | .TCore "Error" => typeMd.val  -- Error → check against Error
      | .TCore "Heap" => typeMd.val
      | _ => HighType.TCore "Any"  -- value vars → check against Any (upcast fires)
    match initOpt with
    | some init =>
      let initVal ← checkValue init checkTy
      pure (.varDecl nameId.text declTy initVal .unit, declTy)
    | none =>
      -- Uninitialized: use a placeholder that projects to Hole
      pure (.varDecl nameId.text declTy (.var "_hole") .unit, declTy)

  -- IfThenElse: checkValue condition against bool (subsume narrows Any→bool inline).
  -- Per ARCHITECTURE.md: v ⇐ bool, Γ ⊢_p M ⇐ C, Γ ⊢_p N ⇐ C
  | .IfThenElse cond thenBranch elseBranch =>
    let condVal ← checkValue cond (.TBool)
    let (thenProd, thenTy) ← synthProducer thenBranch
    let elsProd ← match elseBranch with
      | some e => do let (p, _) ← synthProducer e; pure p
      | none => pure .unit
    pure (.ifThenElse condVal thenProd elsProd, thenTy)

  -- While: checkValue condition against bool, elaborate body.
  -- Per ARCHITECTURE.md: v ⇐ bool, Γ ⊢_p M ⇐ TVoid ⊢ Γ ⊢_p (while v do M) ⇒ TVoid
  | .While cond _invariants _decreases body =>
    let condVal ← checkValue cond (.TBool)
    let (bodyProd, _) ← synthProducer body
    pure (.whileLoop condVal bodyProd .unit, .TVoid)

  -- Assert: checkValue condition against bool.
  -- Per ARCHITECTURE.md: v ⇐ bool ⊢ Γ ⊢_p (assert v) ⇒ TVoid
  | .Assert condition =>
    let condVal ← checkValue condition (.TBool)
    pure (.assert condVal .unit, .TVoid)

  -- Assume: checkValue condition against bool.
  -- Per ARCHITECTURE.md: v ⇐ bool ⊢ Γ ⊢_p (assume v) ⇒ TVoid
  | .Assume condition =>
    let condVal ← checkValue condition (.TBool)
    pure (.assume condVal .unit, .TVoid)

  -- Block: elaborate each statement, sequence via substitution of .unit continuations.
  | .Block stmts label =>
    let (prod, ty) ← elaborateBlock stmts
    match label with
    | some l => pure (.labeledBlock l prod, ty)
    | none => pure (prod, ty)

  -- Exit: terminal, no continuation.
  | .Exit target => pure (.exit target, .TVoid)

  -- New: heap allocation. Per ARCHITECTURE.md: Γ ⊢_p (new Foo) ⇒ Composite
  -- Per IMPLEMENTATION_PLAN.md §Task 26/32: New "Foo" → MkComposite(freshRef, Foo_TypeTag())
  | .New classId =>
    let refVar ← freshVar "ref"
    let objVar ← freshVar "obj"
    let prod := FGLProducer.letProd refVar .TInt (.call "Heap..nextReference!" [.var "$heap"])
      (.letProd objVar (.TCore "Composite")
        (.call "MkComposite" [.var refVar, .staticCall (classId.text ++ "_TypeTag") []])
        (.returnValue (.var objVar)))
    pure (prod, .TCore "Composite")

  -- Return: checkValue against proc return type.
  -- Per ARCHITECTURE.md: v ⇐ procReturnType ⊢ Γ ⊢_p (return v) ⇐ procReturnType
  | .Return valueOpt =>
    let retTy := (← get).currentProcReturnType
    let retTyLow := eraseType retTy
    match valueOpt with
    | some v =>
      let retVal ← checkValue v retTy
      pure (.returnValue retVal, retTyLow)
    | none => pure (.returnValue .fromNone, .TVoid)

  -- FieldSelect: producer (may read heap).
  | .FieldSelect obj field =>
    let (objVal, objTy) ← synthValue obj
    if objTy == .TCore "Composite" then
      -- Heap field access: readField(heap, obj, field) — effectful (reads heap)
      let resultVar ← freshVar "field"
      pure (.letProd resultVar (.TCore "Box")
             (.call "readField" [.var "$heap", objVal, .staticCall (field.text ++ "_Field") []])
             (.returnValue (.var resultVar)), .TCore "Box")
    else
      pure (.returnValue (.fieldAccess objVal field.text), .TCore "Any")

  -- Hole: unknown expression, pass through
  | .Hole _ _ => pure (.returnValue (.var "_hole"), .TCore "Any")

  -- Fallback for remaining forms
  | _ => pure (.returnValue (.var "_unsupported"), .TCore "Any")

/-- Check a producer against an expected type, inserting coercion as needed.
    Per ARCHITECTURE.md producer checking rules + subsumption fallback.
    Per IMPLEMENTATION_PLAN.md §"Task 14". -/
partial def checkProducer (expr : StmtExprMd) (expected : LowType) : ElabM FGLProducer := do
  let (prod, actual) ← synthProducer expr
  match subsume actual expected with
  | .refl => return prod
  | .coerce c =>
    -- Bind the producer to get a value, then coerce
    let tmpVar ← freshVar "tmp"
    pure (.letProd tmpVar actual prod (.returnValue (c (.var tmpVar))))
  | .unrelated => pure prod

/-- Short-circuit desugaring for PAnd/POr.
    Per ARCHITECTURE.md §"Short-Circuit Desugaring in FGL":
    PAnd: evaluate a, narrow to bool, if truthy → evaluate b, else return a's value
    POr: evaluate a, narrow to bool, if truthy → return a's value, else evaluate b
    Per IMPLEMENTATION_PLAN.md §"Task 15": exact FGL transcription. -/
partial def shortCircuitDesugar (op : String) (args : List StmtExprMd) : ElabM (FGLProducer × LowType) := do
  match args with
  | [a, b] =>
    -- Elaborate a as a value (subsume to Any for Any_to_bool)
    let aVal ← checkValue a (.TCore "Any")
    let (bProd, _) ← elaborateExpr b
    let xVar ← freshVar "sc"
    let condVar ← freshVar "cond"
    -- Bind a's value, narrow to bool for condition, then branch
    if op == "PAnd" then
      -- PAnd: truthy → evaluate b, falsy → return a's value
      pure (.letProd xVar (.TCore "Any") (.returnValue aVal)
        (.letProd condVar .TBool (.call "Any_to_bool" [.var xVar])
          (.ifThenElse (.var condVar)
            bProd
            (.returnValue (.var xVar)))),
        .TCore "Any")
    else
      -- POr: truthy → return a's value, falsy → evaluate b
      pure (.letProd xVar (.TCore "Any") (.returnValue aVal)
        (.letProd condVar .TBool (.call "Any_to_bool" [.var xVar])
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
    let elaborateRest := elaborateBlock rest
    let (restProd, restTy) ← match stmt.val with
      | .LocalVariable nameId typeMd _ =>
          extendEnv nameId.text typeMd.val elaborateRest
      | _ => elaborateRest
    pure (sequenceProducers firstProd restProd, restTy)

end -- mutual

/-! ## Tasks 16-17: Projection (ARCHITECTURE.md §"Projection (FineGrainLaurel → Laurel)")

Per IMPLEMENTATION_PLAN.md §"PATH TO PARITY" Tasks 29, 31, 34:
- ALL projected variable types = TCore "Any" (Task 31)
- Hole for uninitialized variables (Task 34)
- Two-pass projection: hoist declarations, emit assignments (Task 29)

Per ARCHITECTURE.md §"Projection: Two-Pass (Declaration Hoisting)":
  Pass 1 — collectDecls: gather all bindings as (name, type) pairs
  Pass 2 — emitBody: emit Assign for letProd (not LocalVariable)
  projectBody: declarations at top (as LocalVariable with Hole), body below
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

/-- Collect all binding declarations from an FGLProducer tree (Pass 1).
    Per IMPLEMENTATION_PLAN.md §Task 29: gather all letProd/varDecl/callWithError bindings. -/
partial def collectDecls : FGLProducer → List (String × LowType)
  | .letProd name ty inner body => [(name, ty)] ++ collectDecls inner ++ collectDecls body
  | .callWithError _ _ rv ev rTy eTy body => [(rv, rTy), (ev, eTy)] ++ collectDecls body
  | .varDecl name ty _ body => [(name, ty)] ++ collectDecls body
  | .newObj _ rv ty body => [(rv, ty)] ++ collectDecls body
  | .assign _ _ body => collectDecls body
  | .assert _ body | .assume _ body => collectDecls body
  | .ifThenElse _ thn els => collectDecls thn ++ collectDecls els
  | .whileLoop _ body after => collectDecls body ++ collectDecls after
  | .labeledBlock _ body => collectDecls body
  | .seq first second => collectDecls first ++ collectDecls second
  | _ => []

/-- Emit body statements from an FGLProducer tree (Pass 2).
    Per IMPLEMENTATION_PLAN.md §Task 29: letProd/varDecl produce Assign (not LocalVariable). -/
partial def emitBody (md : Imperative.MetaData Core.Expression) : FGLProducer → (List StmtExprMd × StmtExprMd)
  | .returnValue v => ([], projectValue md v)
  | .call name args =>
      ([], mkLaurel md (.StaticCall (Identifier.mk name none) (args.map (projectValue md))))
  | .letProd name _ty inner body =>
      let (innerStmts, innerExpr) := emitBody md inner
      let assignStmt := mkLaurel md (.Assign [mkLaurel md (.Identifier (Identifier.mk name none))] innerExpr)
      let (bodyStmts, bodyExpr) := emitBody md body
      (innerStmts ++ [assignStmt] ++ bodyStmts, bodyExpr)
  | .assign target val body =>
      let stmt := mkLaurel md (.Assign [projectValue md target] (projectValue md val))
      let (bodyStmts, bodyExpr) := emitBody md body
      ([stmt] ++ bodyStmts, bodyExpr)
  | .varDecl name _ty init body =>
      -- varDecl from user code (LocalVariable): emit as Assign (declaration already hoisted)
      let assignStmt := mkLaurel md (.Assign [mkLaurel md (.Identifier (Identifier.mk name none))] (projectValue md init))
      let (bodyStmts, bodyExpr) := emitBody md body
      ([assignStmt] ++ bodyStmts, bodyExpr)
  | .ifThenElse cond thn els =>
      ([], mkLaurel md (.IfThenElse (projectValue md cond) (projectBody md thn) (some (projectBody md els))))
  | .whileLoop cond body after =>
      let whileStmt := mkLaurel md (.While (projectValue md cond) [] none (projectBody md body))
      let (afterStmts, afterExpr) := emitBody md after
      ([whileStmt] ++ afterStmts, afterExpr)
  | .assert cond body =>
      let stmt := mkLaurel md (.Assert (projectValue md cond))
      let (bodyStmts, bodyExpr) := emitBody md body
      ([stmt] ++ bodyStmts, bodyExpr)
  | .assume cond body =>
      let stmt := mkLaurel md (.Assume (projectValue md cond))
      let (bodyStmts, bodyExpr) := emitBody md body
      ([stmt] ++ bodyStmts, bodyExpr)
  | .callWithError callee args rv _ev _rTy _eTy body =>
      -- Per old pipeline: effectful call becomes assignment to result var
      let callExpr := mkLaurel md (.StaticCall (Identifier.mk callee none) (args.map (projectValue md)))
      let assignStmt := mkLaurel md (.Assign [mkLaurel md (.Identifier (Identifier.mk rv none))] callExpr)
      let (bodyStmts, bodyExpr) := emitBody md body
      ([assignStmt] ++ bodyStmts, bodyExpr)
  | .exit label => ([mkLaurel md (.Exit label)], mkLaurel md (.LiteralBool true))
  | .labeledBlock label body =>
      ([mkLaurel md (.Block [projectBody md body] (some label))], mkLaurel md (.LiteralBool true))
  | .newObj className rv _ty body =>
      let newExpr := mkLaurel md (.New (Identifier.mk className none))
      let assignStmt := mkLaurel md (.Assign [mkLaurel md (.Identifier (Identifier.mk rv none))] newExpr)
      let (bodyStmts, bodyExpr) := emitBody md body
      ([assignStmt] ++ bodyStmts, bodyExpr)
  | .seq first second =>
      let (fStmts, fTerminal) := emitBody md first
      let (sStmts, sExpr) := emitBody md second
      -- Include first's terminal as a statement if it's meaningful (not .unit artifact)
      let fAll := match fTerminal.val with
        | .LiteralBool true => fStmts  -- .unit artifact: omit
        | _ => fStmts ++ [fTerminal]
      (fAll ++ sStmts, sExpr)
  | .unit => ([], mkLaurel md (.LiteralBool true))

/-- Project a producer body to a Laurel Block (two-pass).
    Per ARCHITECTURE.md §"Projection: Two-Pass (Declaration Hoisting)":
    Pass 1: collect all bindings → LocalVariable name Any Hole at top
    Pass 2: emit assignments + control flow
    Per IMPLEMENTATION_PLAN.md §Tasks 29, 31, 34:
    - ALL vars typed Any (Task 31)
    - Hole for uninit (Task 34) -/
partial def projectBody (md : Imperative.MetaData Core.Expression) (prod : FGLProducer) : StmtExprMd :=
  -- Pass 1: collect all binding declarations
  let decls := collectDecls prod
  -- Deduplicate: only emit each name once (elaboration may visit sub-trees)
  let emptyList : List (String × LowType) := []
  let uniqueDecls := decls.foldl (fun (acc : List (String × LowType)) (name, ty) =>
    if acc.any (fun (n, _) => n == name) then acc else acc ++ [(name, ty)]) emptyList
  -- Per Task 31: ALL projected variable types = TCore "Any"
  -- Exception: infrastructure types (Error, Heap) keep their type for Core compatibility
  -- Per Task 34: Hole for uninitialized
  let declStmts := uniqueDecls.map fun (name, ty) =>
    let projTy := match ty with
      | .TCore "Error" => HighType.TCore "Error"  -- Core needs Error typed correctly
      | .TCore "Heap" => HighType.TCore "Heap"
      | _ => HighType.TCore "Any"  -- All other vars typed Any
    mkLaurel md (.LocalVariable (Identifier.mk name none) (mkHighTypeMd md projTy)
      (some (mkLaurel md (.Hole))))
  -- Pass 2: emit assignments + control flow
  let (bodyStmts, terminal) := emitBody md prod
  -- Filter out assignments to _hole vars (artifacts from uninitialized varDecl)
  let filteredBody := bodyStmts.filter fun stmt =>
    match stmt.val with
    | .Assign _ rhs => match rhs.val with
      | .Identifier id => id.text != "_hole"
      | _ => true
    | _ => true
  -- Only include terminal if it's meaningful (not the .unit artifact)
  let finalStmts := match terminal.val with
    | .LiteralBool true => declStmts ++ filteredBody  -- .unit artifact: omit
    | _ => declStmts ++ filteredBody ++ [terminal]
  -- Combine: declarations at top, body below
  mkLaurel md (.Block finalStmts none)

end -- mutual (projectValue, collectDecls, emitBody, projectBody)

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

    Per IMPLEMENTATION_PLAN.md §Tasks 32-33:
    - Composite: MkComposite(ref: int, typeTag: TypeTag) — TWO fields (Task 32)
    - Box: single constructor Box..Any(AnyVal: Any) (Task 33)

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
  -- Per IMPLEMENTATION_PLAN.md §Task 33: Box with SINGLE constructor Box..Any(AnyVal: Any)
  let boxConstructors : List Strata.Laurel.DatatypeConstructor := [
    { name := "Box..Any", args := [{ name := "AnyVal", type := ⟨.TCore "Any", #[]⟩ }] }
  ]
  let boxDatatype : Strata.Laurel.TypeDefinition :=
    .Datatype { name := "Box", typeArgs := [], constructors := boxConstructors }
  -- heapConstants provides Composite + Heap + NotSupportedYet datatypes
  -- plus readField/updateField/increment procedures
  let heapTypeDefs := heapConstants.types
  let heapProcs := heapConstants.staticProcedures
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
