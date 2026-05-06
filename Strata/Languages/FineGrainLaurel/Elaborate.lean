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

/-! ## Stub: fullElaborate (pass-through)

Pass-through stub so the build doesn't break while tasks 6+ are implemented.
Called by PySpecPipeline.lean. -/

/-- Entry point: fullElaborate (called by PySpecPipeline).
    Currently a pass-through stub — returns the input program unchanged. -/
def fullElaborate (_typeEnv : Strata.Python.Resolution.TypeEnv)
    (program : Strata.Laurel.Program) : Except String Strata.Laurel.Program :=
  pure program

end -- public section

end Strata.FineGrainLaurel
