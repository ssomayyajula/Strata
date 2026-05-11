# Python → Laurel Translation Architecture

---

## Overview

This pipeline translates Python source code into Laurel (our verification IL)
via a series of compositional passes. The key insight is **separation of
concerns**: Translation handles Python's surface syntax (scope, classes,
control flow) while Elaboration handles the semantic heavy lifting (effects,
coercions, heap threading). Neither pass knows about the other's job.

The elaboration pass is based on **Fine-Grain Call-By-Value** (FGCBV), a
type theory that separates *values* (pure, duplicable) from *producers*
(effectful, sequenced). In FGCBV, effects are made explicit through a
sequencing construct `M to x. N` ("run M, bind its result to x, continue
with N") rather than being implicit in evaluation order as in plain CBV.
This separation means the elaborator can reason precisely about which
subexpressions have effects and insert the correct calling conventions.

**Graded effects** refine this further: instead of a binary pure/effectful
distinction, each producer carries a *grade* from a monoid `{1, proc, err,
heap, heap·err}` that classifies exactly which effects it performs. The grade
determines the calling convention (extra heap parameters, error outputs)
and the grade monoid's algebraic structure ensures compositionality —
sequencing two producers joins their grades.

**Bidirectional typing** makes the elaborator syntax-directed (no
backtracking, no unification). Values *synthesize* their types (bottom-up);
producers are *checked* against an ambient grade (top-down). The mode
discipline guarantees that at every point in the algorithm, enough
information is available to make a deterministic choice.

## The Pipeline

```
Python AST + library stubs
  ↓ [Resolution: build Γ]
Γ : TypeEnv
  +
Python AST (user code)
  ↓ [Translation: fold over AST, type-directed via Γ]
e : Laurel.Program (impure CBV — precisely-typed, effects implicit)
  ↓ [Elaboration: impure CBV → Graded FGCBV, coinductive grade inference]
e' : GFGL.Program (Graded Fine-Grain Laurel — effects explicit via grades)
  ↓ [Projection: forget grading, trivial cata]
Laurel.Program (ready for Core)
  ↓ [Core translation]
Core
```

**Resolution** builds the typing environment Γ from Python source and
library stubs. It records function signatures, class fields, module
structure, and type annotations. It does NOT determine effects.

**Translation** is a deterministic fold over the Python AST. It desugars
Python's surface syntax (classes → constructors + init calls, for loops →
havoc + assume, context managers → enter/exit calls, etc.) into a flat
Laurel program. The output is precisely typed but effects are still
implicit — an effectful call looks the same as a pure one.

**Elaboration** takes this implicitly-effectful program and makes effects
explicit. It discovers each procedure's grade via coinduction on the call
graph, then elaborates each body: inserting coercions at type
boundaries, threading heap state, binding effectful subexpressions via
ANF-lifting, and rewriting procedure signatures to match the graded
calling convention. The output is a GFGL (Graded Fine-Grain Laurel) program.
GFGL is Laurel's AST enriched with graded effect information, based on the
theory of graded fine-grain call-by-value (McDermott 2025, building on
Levy 2003 and Gaboardi et al. 2016).

**Projection** forgets the grading — a trivial structural map from GFGL
back to Laurel syntax. The effect information is now encoded in the
procedure signatures and calling conventions, not in the type system.

---

## Engineering Principles

| Principle | Eliminates |
|---|---|
| Representation invariants | Runtime checks, dead branches |
| Proof-relevant elimination | Boolean blindness |
| Catamorphisms | Traversal choices |
| Correct by construction | Post-hoc rewrites |
| Separation of concerns | Decisions in wrong place |
| Monad carries context | Ad-hoc parameter passing |
| Types flow down | Bottom-up guessing |
| Illegal states unrepresentable | Undefined name references, invalid calls |
| No strings | Type-level resolution, not runtime checks |

### Illegal States Unrepresentable

**Resolution → Translation contract:** Translation CANNOT emit a `StaticCall`
to a name that is not in Γ. This is enforced representationally:

```lean
-- Resolution produces resolved names, not strings
structure ResolvedCall where
  sig : FuncSig            -- proof that the callee exists in Γ
  resolvedArgs : List StmtExprMd  -- args already matched to params

-- Translation's StaticCall takes a ResolvedCall, not an Identifier
-- If lookupName returns none → emit Hole (undefined = nondeterministic)
-- There is NO path that produces StaticCall with an unresolved name
```

This eliminates an entire class of bugs:
- Undefined function calls (→ Core "not found" errors)
- Arity mismatches (args checked against sig at construction time)
- Type-level module resolution failures silently producing garbage names

**No strings for types:** Types flow through the pipeline as `HighType`
values, never as strings. `extractTypeStr` + `pythonTypeToLaurel` is
ABOLISHED. Type annotations go directly from Python AST → `HighType`
via `Resolution.annotationToHighType`. Union types that can't be
represented → `.TCore "Any"` (handled in Resolution, not Translation).

**No boolean blindness in Resolution:** `NameInfo` is an inductive —
pattern matching on it gives you the data you need. There is no
`isResolved : String → Bool` followed by a separate lookup. The lookup
IS the check. `Option NameInfo` is the only interface.

---

## Resolution

**Input:** Python AST + stubs  
**Output:** `TypeEnv` (= Γ)

```lean
structure FuncSig where
  name : String
  params : List (String × HighType)
  defaults : List (Option StmtExprMd)
  returnType : HighType
  hasKwargs : Bool

structure TypeEnv where
  names : Std.HashMap String NameInfo
  classFields : Std.HashMap String (List (String × HighType))
  overloadTable : Std.HashMap String (Std.HashMap String String)
  builtinMap : Std.HashMap String String

inductive NameInfo where
  | class_ (name : String) (fields : List (String × HighType))
  | function (sig : FuncSig)
  | variable (ty : HighType)
  | module_ (fullName : String)
```

Resolution does NOT determine effects. Effects are inferred by elaboration.

**Contract with Translation:** Every name Translation wants to call MUST be
in `TypeEnv.names`. Translation looks up names via `Option NameInfo`. If the
lookup returns `none`, Translation emits `Hole` (nondeterministic havoc).
There is no code path that produces `StaticCall` for an unresolved name.

**No strings for types:** `annotationToHighType` goes directly from Python
annotation AST → `HighType`. Union types (`int | bool`, `Optional[X]`,
`List[X]`) that can't be precisely represented → `.TCore "Any"`. This
decision is made in Resolution, not in Translation.

---

## Translation

A catamorphism over the Python AST. One case per constructor. Deterministic.

**Does:** scope hoisting, object construction (.New + __init__), context managers,
for-loop abstraction (havoc + assume), loop labels, calling convention (kwargs +
defaults via Γ), module-level wrapping (__main__), mutable param copies,
error output declaration (`maybe_except: Error` in proc outputs — matches prelude
convention so the variable is in scope for try/except assignment).

**Does NOT:** cast insertion, literal wrapping, effect determination.

---

## Elaboration

Elaboration is the heart of the pipeline. It is NOT a term-to-term
transformation — it is the construction of a *GFGL typing derivation*
from a *Laurel typing derivation*. The input is a well-typed Laurel term
(implicitly effectful CBV); the output is a well-typed GFGL term (effects
explicit via grades in the term structure). The GFGL term is the proof
term of the typing derivation — it IS the derivation, not something
derived from it.

Concretely: the elaborator takes a Laurel program where effects are
implicit (an effectful call `f(x)` is syntactically identical to a pure
call `g(x)`) and constructs the GFGL derivation where effects are explicit
(effectful calls are sequenced via `effectfulCall` nodes that bind their
outputs, with grades witnessing the effect composition).

The theory behind this is **Fine-Grain Call-By-Value** (Levy 2003, Egger
et al. 2014). In FGCBV, the term language has two syntactic categories:

- **Values** (V): pure, duplicable, no effects. Literals, variables,
  pure function applications, coercions.
- **Producers** (M): effectful, sequenced. Statements, effectful calls,
  control flow.

The key construct is `M to x. N` — "evaluate producer M, bind its result
to x, then evaluate producer N." This is the fine-grain sequencing that
replaces implicit left-to-right evaluation. Our `effectfulCall` node is
exactly this construct specialized to procedure calls.

**Graded effects** (Gaboardi et al. 2016, Orchard et al. 2019) annotate
each producer with a grade from an effect monoid. Our monoid has five
elements: `pure` (no effects), `proc` (must be at statement level),
`err` (may raise exceptions), `heap` (reads/writes heap), and `heapErr`
(both). The grade tells us the calling convention: a `heap`-graded call
must receive the current heap and return a new one; an `err`-graded call
returns an extra error output; a `proc`-graded call is bound at statement
level with its declared outputs.

**Bidirectional typing** (Pierce & Turner 2000) makes the algorithm
syntax-directed. There are two modes:

- **Synthesis (⇒):** given a term, compute its type and grade.
- **Checking (⇐):** given a term and an expected type/grade, verify it fits.

The mode switch happens at subsumption: when we synthesize a type A but
need type B, we insert a coercion witness. When we synthesize grade d but
the ambient grade is e, we insert the appropriate calling convention.
Both witnesses are *proof-relevant* — they produce GFGL term structure,
not just boolean "yes/no."

### Two Type Systems

**HighType** (Translation's output): has `UserDefined "Foo"`.  
**LowType** (GFGL's type system): has only `Composite`.

```lean
def eraseType : HighType → LowType
  | .TInt => .TInt | .TBool => .TBool | .TString => .TString
  | .TFloat64 => .TFloat64 | .TVoid => .TVoid | .TCore n => .TCore n
  | .UserDefined id => match id.text with
    | "Any" => .TCore "Any" | "Error" => .TCore "Error"
    | "ListAny" => .TCore "ListAny" | "DictStrAny" => .TCore "DictStrAny"
    | "Box" => .TCore "Box" | "Field" => .TCore "Field" | "TypeTag" => .TCore "TypeTag"
    | _ => .TCore "Composite"
  | .THeap => .TCore "Heap"
  | .TReal => .TCore "real" | .TTypedField _ => .TCore "Field"
  | .TSet _ | .TMap _ _ | .Applied _ _ | .Intersection _ | .Unknown => .TCore "Any"
  | .Pure _ => .TCore "Composite"
```

Note: The Laurel parser produces `UserDefined "Any"` for the type name `Any`
in runtime program sources. `eraseType` must handle these — otherwise runtime
proc signatures get Composite where they should get Any, causing spurious coercions.

### The Grade Monoid (Residuated Partially-Ordered)

```
(E, ≤, 1, ·, \) where E = {1, proc, err, heap, heapErr}

Order:
  1 ≤ proc ≤ err ≤ heapErr
  1 ≤ proc ≤ heap ≤ heapErr

Multiplication:
  1 · e = e · 1 = e
  proc · proc = proc
  proc · err = err     err · proc = err
  proc · heap = heap   heap · proc = heap
  err · heap = heapErr   heap · err = heapErr
  e · e = e

Left residual (d \ e):
  1 \ e = e
  proc \ proc = 1     proc \ err = err     proc \ heap = heap   proc \ heapErr = heapErr
  err \ err = 1        err \ heapErr = heap
  heap \ heap = 1      heap \ heapErr = err
  heapErr \ heapErr = 1
```

**The `proc` grade:** Represents a computation that MUST be sequenced at
statement level but carries no specific effect (no error output, no heap
threading). Runtime procedures declared with `procedure` (not `function`)
that have no Error/Heap in their signature get grade `proc`. The calling
convention for `proc`: bind via `effectfulCall` with outputs matching
the procedure's declared outputs (typically `[result]`). No extra outputs
added.

`proc` exists because Laurel distinguishes `function` (can appear in
expressions, Core emits as `.op`) from `procedure` (must be at statement
level, Core emits as `.call`). A runtime procedure like `datetime_now()`
has no error or heap effects but CANNOT appear inside an expression —
it must be bound first.

### Laurel Type System (Source)

Laurel is an impure CBV language. One judgment:

```
Γ ⊢_L e : A
```

There is no distinction between expressions and statements — both are `StmtExpr`
and both carry type A. For expressions, A is their value type. For statement
sequences, A is the return type of the enclosing procedure (threaded through
the continuation).

```
─────────────────            ─────────────────            ─────────────────
Γ ⊢_L n : int               Γ ⊢_L b : bool              Γ ⊢_L s : string


(x : A) ∈ Γ
─────────────────
Γ ⊢_L x : A


f : (A₁,...,Aₙ) → B ∈ Γ    Γ ⊢_L e₁ : A₁  ...  Γ ⊢_L eₙ : Aₙ
──────────────────────────────────────────────────────────────────
Γ ⊢_L f(e₁,...,eₙ) : B


Γ ⊢_L e : C    fields(C,f) = T
────────────────────────────────
Γ ⊢_L e.f : T


C ∈ classes(Γ)
─────────────────
Γ ⊢_L new C : C


─────────────────            ─────────────────
Γ ⊢_L ?? : A  (nondet)      Γ ⊢_L ? : A  (det)


Γ ⊢_L e : Γ(x)    Γ ⊢_L rest : A
────────────────────────────────────
Γ ⊢_L (x := e); rest : A


Γ ⊢_L e : T    Γ,x:T ⊢_L rest : A
─────────────────────────────────────
Γ ⊢_L (var x:T := e); rest : A


Γ ⊢_L c : bool    Γ ⊢_L t : A    Γ ⊢_L f : A    Γ ⊢_L rest : A
──────────────────────────────────────────────────────────────────
Γ ⊢_L (if c then t else f); rest : A


Γ ⊢_L c : bool    Γ ⊢_L body : A    Γ ⊢_L rest : A
──────────────────────────────────────────────────────
Γ ⊢_L (while c do body); rest : A


Γ ⊢_L e : A
─────────────────────
Γ ⊢_L (return e) : A


─────────────────────
Γ ⊢_L (exit l) : A


Γ ⊢_L c : bool    Γ ⊢_L rest : A
───────────────────────────────────
Γ ⊢_L (assert c); rest : A


Γ ⊢_L c : bool    Γ ⊢_L rest : A
───────────────────────────────────
Γ ⊢_L (assume c); rest : A


Γ ⊢_L obj : C    Γ ⊢_L v : fieldType(C,f)    Γ ⊢_L rest : A
──────────────────────────────────────────────────────────────
Γ ⊢_L (obj.f := v); rest : A


Γ ⊢_L root : Any    Γ ⊢_L idx : Any    Γ ⊢_L v : Any    Γ ⊢_L rest : A
──────────────────────────────────────────────────────────────────────────
Γ ⊢_L (root[idx] := v); rest : A
```

Note: effects are invisible. `f(e₁,...,eₙ)` has the same typing rule regardless
of whether f is pure or effectful. The grade system exists only in GFGL.

### GFGL Type System (Target — Bidirectional, Graded)

GFGL has two sorts: **values** (pure, no effects) and **producers** (effectful,
sequenced, carry a grade). Typing is bidirectional.

The context Γ' carries:
- **Variables** `(x : A)` — looked up by value synthesis
- **Labels** `(l : A & e)` — looked up by producer synthesis

```
Γ' ⊢_v V ⇒ A           value synthesis
Γ' ⊢_v V ⇐ A           value checking
Γ' ⊢_p M ⇒ A & d       producer synthesis
Γ' ⊢_p M ⇐ A & e       producer checking
```

#### Value rules

```
─────────────────────────        ─────────────────────────        ─────────────────────────
Γ' ⊢_v litInt n ⇒ TInt          Γ' ⊢_v litBool b ⇒ TBool        Γ' ⊢_v litString s ⇒ TString


(x : A) ∈ Γ'
─────────────────────────
Γ' ⊢_v var x ⇒ A


f : (A₁,...,Aₙ) → B ∈ Γ'    Γ' ⊢_v V₁ ⇐ A₁  ...  Γ' ⊢_v Vₙ ⇐ Aₙ
───────────────────────────────────────────────────────────────────────
Γ' ⊢_v staticCall f [V₁,...,Vₙ] ⇒ B


Γ' ⊢_v V ⇒ A    subsume(A, B) = c
───────────────────────────────────
Γ' ⊢_v c(V) ⇐ B
```

#### Producer synthesis

```
(l : A & e) ∈ Γ'
─────────────────────────
Γ' ⊢_p exit l ⇒ A & e


f : (A₁,...,Aₙ) → B & d ∈ Γ'    Γ' ⊢_v V₁ ⇐ A₁  ...  Γ' ⊢_v Vₙ ⇐ Aₙ
──────────────────────────────────────────────────────────────────────────
Γ' ⊢_p f(V₁,...,Vₙ) ⇒ B & d
```

`exit l` synthesizes by looking up label `l` in the context (labels are
to producers what variables are to values).

#### Producer subsumption (mode switch ⇒ₚ to ⇐ₚ)

```
Γ' ⊢_p M ⇒ B & d    subsume(B, A) = c    Γ',x₁:T₁,...,xₖ:Tₖ ⊢_p M_k ⇐ A & (d\e)
──────────────────────────────────────────────────────────────────────────────────────
Γ',x₁:T₁,...,xₖ:Tₖ ⊢_p effectfulCall f [Vᵢ] [x₁:T₁,...,xₖ:Tₖ] (c(xⱼ); M_k) ⇐ A & e
```

The synthesized producer is bound via effectfulCall. Outputs come from
f's declared signature. Coercion c applied to the result in the continuation.
Continuation checked at residual `d\e`.

#### Producer checking rules

```
─────────────────────────
Γ' ⊢_p unit ⇐ A & e


Γ' ⊢_v V ⇐ A
──────────────────────────────────────
Γ' ⊢_p returnValue V ⇐ A & e


Γ' ⊢_v V ⇐ Γ'(x)    Γ' ⊢_p M_k ⇐ A & e
───────────────────────────────────────────
Γ' ⊢_p assign x V M_k ⇐ A & e


Γ' ⊢_v V ⇐ T    Γ',x:T ⊢_p M_k ⇐ A & e
───────────────────────────────────────────
Γ',x:T ⊢_p varDecl x T V M_k ⇐ A & e


Γ' ⊢_v V ⇐ bool    Γ' ⊢_p M_t ⇐ A & e    Γ' ⊢_p M_f ⇐ A & e    Γ' ⊢_p M_k ⇐ A & e
─────────────────────────────────────────────────────────────────────────────────────────
Γ' ⊢_p ifThenElse V M_t M_f M_k ⇐ A & e


Γ' ⊢_v V ⇐ bool    Γ' ⊢_p M_b ⇐ A & e    Γ' ⊢_p M_k ⇐ A & e
─────────────────────────────────────────────────────────────────
Γ' ⊢_p whileLoop V M_b M_k ⇐ A & e


Γ' ⊢_v V ⇐ bool    Γ' ⊢_p M_k ⇐ A & e
─────────────────────────────────────────
Γ' ⊢_p assert V M_k ⇐ A & e


Γ' ⊢_v V ⇐ bool    Γ' ⊢_p M_k ⇐ A & e
─────────────────────────────────────────
Γ' ⊢_p assume V M_k ⇐ A & e


Γ',l:(A & e) ⊢_p M_b ⇐ A & e    Γ' ⊢_p M_k ⇐ A & e
───────────────────────────────────────────────────────
Γ' ⊢_p labeledBlock l M_b M_k ⇐ A & e


f : (A₁,...,Aₙ) → [x₁:T₁,...,xₖ:Tₖ] & d ∈ Γ'
Γ' ⊢_v V₁ ⇐ A₁  ...  Γ' ⊢_v Vₙ ⇐ Aₙ
Γ',x₁:T₁,...,xₖ:Tₖ ⊢_p M_k ⇐ A & (d\e)
────────────────────────────────────────────────────────────────
Γ' ⊢_p effectfulCall f [V₁,...,Vₙ] [x₁:T₁,...,xₖ:Tₖ] M_k ⇐ A & e
```

Note: `labeledBlock l M_b M_k` binds label l in the context for M_b — so
`exit l` in the body can synthesize. M_k is checked in the outer context.

### Elaboration (⟦·⟧ : Laurel Derivations → GFGL Derivations)

Elaboration transforms Laurel typing derivations into GFGL typing derivations.
It is defined by four mutually recursive functions with an induced translation
on types (⟦A⟧ = eraseType(A)) and contexts (⟦Γ⟧ = { (x : ⟦A⟧) | (x:A) ∈ Γ }).

```
⟦·⟧⇒ᵥ : (Γ ⊢_L e : A) → ∃V. (⟦Γ⟧ ⊢_v V ⇒ ⟦A⟧)
⟦·⟧⇐ᵥ : (Γ ⊢_L e : A) → (B : LowType) → ∃V. (⟦Γ⟧ ⊢_v V ⇐ B)
⟦·⟧⇒ₚ : (Γ ⊢_L e : A) → ∃M,d. (⟦Γ⟧ ⊢_p M ⇒ ⟦A⟧ & d)
⟦·⟧⇐ₚ : (Γ ⊢_L S;rest : A) → (e : Grade) → ∃M. (⟦Γ⟧ ⊢_p M ⇐ ⟦A⟧ & e)
```

#### Phase 1: Grade inference (coinduction on the call graph)

Before any GFGL derivation is constructed, every procedure's grade must be
known. Grades are discovered by coinduction:

```
discoverGrades(program, Γ) → procGrades:
  1. Initialize: procGrades[f] := ⊥ (pure) for all user procs f
  2. For each proc f with body M and return type A:
       Try ⟦M⟧⇐ₚ at grade g for g ∈ [pure, proc, err, heap, heapErr]
       under the current procGrades assumption.
       Set procGrades[f] := smallest g that succeeds.
  3. If any grade changed, go to step 2.
  4. Stable (no changes). Return procGrades.
```

The translation functions are the oracle: ⟦M⟧⇐ₚ at grade g succeeds iff all
operations in M have grade ≤ g. It fails when the residual `d\e` is undefined
(a callee's grade exceeds the ambient grade).

Convergence is guaranteed: the grade lattice has 5 elements and grades only
increase. Mutual recursion works because the initial assumption (⊥) means
the first iteration may fail, bump the grade, and stabilize on the next round.

Runtime procedure grades are pre-computed from signatures (not by coinduction):

```
gradeFromSignature(proc) :=
  if proc has Error output and Heap input → heapErr
  if proc has Heap input → heap
  if proc has Error output → err
  if proc.isFunctional → pure
  else → proc
```

Runtime grades enter procGrades as initial values before coinduction begins.

#### Phase 2: Term production

After grade inference, all grades are known and stable. Term production
enters ⟦·⟧⇐ₚ on each user procedure body at the discovered grade:

```
⟦body⟧⇐ₚ at procGrades[f]  ::  ⟦Γ⟧,params ⊢_p M ⇐ ⟦returnType⟧ & e
```

During term production, grade lookup is a pure read (HashMap). No mutation.
No on-demand discovery. No boolean flags.

#### How the four functions call each other

⟦·⟧⇐ₚ is the main driver. For each Laurel statement, it:

1. Translates sub-expressions via ⟦·⟧⇐ᵥ (conditions → bool, values → target type)
2. Recursively translates the continuation via ⟦·⟧⇐ₚ
3. Assembles the GFGL producer checking derivation

For assignments and expression-statements, ⟦·⟧⇐ₚ first calls ⟦·⟧⇒ₚ on the
RHS to determine whether it's a value or effectful call:

- **Value (grade = pure):** ⟦·⟧⇐ᵥ checks it against the target type.
  The result is a GFGL value used directly.
- **Effectful call (grade > pure):** Producer subsumption fires — the call
  is bound via effectfulCall, extending the context with the callee's
  outputs. The continuation is checked at the residual grade `d\e`.

⟦·⟧⇐ᵥ = ⟦·⟧⇒ᵥ + subsumption. It synthesizes the value's type, then applies
the subsumption coercion if the synthesized type doesn't match the target.

The **to-rule** handles effectful arguments to pure calls: when ⟦·⟧⇒ₚ on
an argument yields grade > pure, the argument is ANF-lifted into an
effectfulCall binding BEFORE the outer call. Left-to-right, deterministic.
Each lift nests one effectfulCall and extends the context.

#### User/Runtime separation

The elaborator must know the types of ALL callees (to insert coercions) but
only elaborates USER procedure bodies (runtime is trusted).

```
ElabEnv:
  typeEnv : TypeEnv           -- ALL signatures (user + runtime + prelude)
  program : Laurel.Program    -- ONLY user procedures (bodies elaborated)
  runtime : Laurel.Program    -- ONLY runtime procedures (never elaborated)
  procGrades : HashMap        -- grades for ALL callees
```

Runtime procedure bodies are never inspected. Their grades are derived
from their signatures via gradeFromSignature.

#### Procedure signature rewriting

After a procedure's grade is discovered, its signature is rewritten to
match the calling convention:

- Grade `heap`/`heapErr` → add `$heap_in` input + `$heap` output
- Body prepended with `$heap := $heap_in`
- Callers already pass heap (determined by grade during term production)

#### Clauses of ⟦·⟧⇒ᵥ  (value synthesis)

```
D :: Γ ⊢_L n : int                   ↦    ⟦D⟧⇒ᵥ :: ⟦Γ⟧ ⊢_v litInt n ⇒ TInt

(x : A) ∈ Γ
─────────────────
D :: Γ ⊢_L x : A                     ↦    ⟦D⟧⇒ᵥ :: ⟦Γ⟧ ⊢_v var x ⇒ ⟦A⟧


D₁ :: Γ ⊢_L e₁ : A₁  ...  Dₙ :: Γ ⊢_L eₙ : Aₙ
──────────────────────────────────────────────────
D :: Γ ⊢_L f(e₁,...,eₙ) : B    where grade(f) = pure

        ↦

⟦D₁⟧⇐ᵥ :: ⟦Γ⟧ ⊢_v V₁ ⇐ ⟦A₁⟧  ...  ⟦Dₙ⟧⇐ᵥ :: ⟦Γ⟧ ⊢_v Vₙ ⇐ ⟦Aₙ⟧
────────────────────────────────────────────────────────────────────────
⟦D⟧⇒ᵥ :: ⟦Γ⟧ ⊢_v staticCall f [V₁,...,Vₙ] ⇒ ⟦B⟧


D_obj :: Γ ⊢_L e : C    fields(C,f) = T
────────────────────────────────────────
D :: Γ ⊢_L e.f : T

        ↦

⟦D_obj⟧⇐ᵥ :: ⟦Γ⟧ ⊢_v V_obj ⇐ Composite
──────────────────────────────────────────────────────────────────────
⟦D⟧⇒ᵥ :: ⟦Γ⟧ ⊢_v Box..tVal!(readField($heap, V_obj, $field.C.f)) ⇒ ⟦T⟧


D :: Γ ⊢_L ?? : A       ↦    ⟦D⟧⇒ᵥ :: ⟦Γ⟧,$havoc_N ⊢_v staticCall $havoc_N [] ⇒ Any
D :: Γ ⊢_L ?  : A       ↦    ⟦D⟧⇒ᵥ :: ⟦Γ⟧,$hole_N ⊢_v staticCall $hole_N [] ⇒ Any
```

#### ⟦·⟧⇐ᵥ  (value checking = ⟦·⟧⇒ᵥ + subsumption)

```
⟦D⟧⇒ᵥ :: ⟦Γ⟧ ⊢_v V ⇒ A    subsume(A, B) = c
────────────────────────────────────────────────
⟦D⟧⇐ᵥ :: ⟦Γ⟧ ⊢_v c(V) ⇐ B
```

The coercion c is proof-relevant — it becomes GFGL term structure
(`from_int`, `Any..as_Composite!`, etc.).

#### ⟦·⟧⇒ₚ  (producer synthesis)

```
D₁ :: Γ ⊢_L e₁ : A₁  ...  Dₙ :: Γ ⊢_L eₙ : Aₙ
──────────────────────────────────────────────────
D :: Γ ⊢_L f(e₁,...,eₙ) : B    where grade(f) = d > pure

        ↦

⟦D₁⟧⇐ᵥ :: ⟦Γ⟧ ⊢_v V₁ ⇐ ⟦A₁⟧  ...  ⟦Dₙ⟧⇐ᵥ :: ⟦Γ⟧ ⊢_v Vₙ ⇐ ⟦Aₙ⟧
────────────────────────────────────────────────────────────────────────
⟦D⟧⇒ₚ :: ⟦Γ⟧ ⊢_p f(V₁,...,Vₙ) ⇒ ⟦B⟧ & d
```

When grade(f) = pure, ⟦·⟧⇒ₚ delegates to ⟦·⟧⇒ᵥ (the expression is a value).

#### Producer subsumption (⟦·⟧⇒ₚ meets ⟦·⟧⇐ₚ)

When ⟦·⟧⇐ₚ encounters an expression with grade > pure, it uses ⟦·⟧⇒ₚ to
synthesize, then applies producer subsumption to construct the effectfulCall:

```
⟦D⟧⇒ₚ :: ⟦Γ⟧ ⊢_p f(Vᵢ) ⇒ ⟦B⟧ & d    K :: Γ ⊢_L rest : A
─────────────────────────────────────────────────────────────

        ↦

⟦K⟧⇐ₚ :: ⟦Γ⟧,x₁:T₁,...,xₖ:Tₖ ⊢_p M_k ⇐ ⟦A⟧ & (d\e)
────────────────────────────────────────────────────────────────────────────────
⟦Γ⟧,x₁:T₁,...,xₖ:Tₖ ⊢_p effectfulCall f [Vᵢ] [x₁:T₁,...,xₖ:Tₖ] M_k ⇐ ⟦A⟧ & e
```

Outputs [x₁:T₁,...,xₖ:Tₖ] from f's declared signature.
Continuation checked at residual grade `d\e`.

#### Clauses of ⟦·⟧⇐ₚ  (producer checking)

```
D_c :: Γ ⊢_L c : bool    D_t :: Γ ⊢_L t : A    D_f :: Γ ⊢_L f : A    K :: Γ ⊢_L rest : A
─────────────────────────────────────────────────────────────────────────────────────────────
D :: Γ ⊢_L (if c then t else f); rest : A

        ↦

⟦D_c⟧⇐ᵥ :: ⟦Γ⟧ ⊢_v V ⇐ bool    ⟦D_t⟧⇐ₚ :: ⟦Γ⟧ ⊢_p M_t ⇐ ⟦A⟧ & e    ⟦D_f⟧⇐ₚ :: ⟦Γ⟧ ⊢_p M_f ⇐ ⟦A⟧ & e    ⟦K⟧⇐ₚ :: ⟦Γ⟧ ⊢_p M_k ⇐ ⟦A⟧ & e
────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────
⟦D⟧⇐ₚ :: ⟦Γ⟧ ⊢_p ifThenElse V M_t M_f M_k ⇐ ⟦A⟧ & e


D_e :: Γ ⊢_L e : A
───────────────────
D :: Γ ⊢_L (return e) : A

        ↦

⟦D_e⟧⇐ᵥ :: ⟦Γ⟧ ⊢_v V ⇐ ⟦A⟧
─────────────────────────────────────────
⟦D⟧⇐ₚ :: ⟦Γ⟧ ⊢_p returnValue V ⇐ ⟦A⟧ & e


D_init :: Γ ⊢_L e : T    K :: Γ,x:T ⊢_L rest : A
───────────────────────────────────────────────────
D :: Γ ⊢_L (var x:T := e); rest : A

        ↦

⟦D_init⟧⇐ᵥ :: ⟦Γ⟧ ⊢_v V ⇐ ⟦T⟧    ⟦K⟧⇐ₚ :: ⟦Γ⟧,x:⟦T⟧ ⊢_p M_k ⇐ ⟦A⟧ & e
──────────────────────────────────────────────────────────────────────────────
⟦D⟧⇐ₚ :: ⟦Γ⟧,x:⟦T⟧ ⊢_p varDecl x ⟦T⟧ V M_k ⇐ ⟦A⟧ & e


D_c :: Γ ⊢_L c : bool    K :: Γ ⊢_L rest : A
──────────────────────────────────────────────
D :: Γ ⊢_L (assert c); rest : A

        ↦

⟦D_c⟧⇐ᵥ :: ⟦Γ⟧ ⊢_v V ⇐ bool    ⟦K⟧⇐ₚ :: ⟦Γ⟧ ⊢_p M_k ⇐ ⟦A⟧ & e
────────────────────────────────────────────────────────────────────────
⟦D⟧⇐ₚ :: ⟦Γ⟧ ⊢_p assert V M_k ⇐ ⟦A⟧ & e


D_e :: Γ ⊢_L e : B    K :: Γ ⊢_L rest : A
────────────────────────────────────────────
D :: Γ ⊢_L (x := e); rest : A

        ↦

If ⟦D_e⟧⇒ₚ is a value (grade = pure):

    ⟦D_e⟧⇐ᵥ :: ⟦Γ⟧ ⊢_v V ⇐ ⟦Γ(x)⟧    ⟦K⟧⇐ₚ :: ⟦Γ⟧ ⊢_p M_k ⇐ ⟦A⟧ & e
    ────────────────────────────────────────────────────────────────────────
    ⟦D⟧⇐ₚ :: ⟦Γ⟧ ⊢_p assign x V M_k ⇐ ⟦A⟧ & e

If ⟦D_e⟧⇒ₚ has grade d > pure:

    (producer subsumption: effectfulCall f [...] [outputs] (assign x (subsume(r, ⟦Γ(x)⟧)) ⟦K⟧⇐ₚ))


D_body :: Γ ⊢_L {s₁;...;sₙ} : A    K :: Γ ⊢_L rest : A
──────────────────────────────────────────────────────────
D :: Γ ⊢_L {s₁;...;sₙ}ₗ; rest : A    (labeled)

        ↦

⟦D_body⟧⇐ₚ :: ⟦Γ⟧,l:(⟦A⟧ & e) ⊢_p M_b ⇐ ⟦A⟧ & e    ⟦K⟧⇐ₚ :: ⟦Γ⟧ ⊢_p M_k ⇐ ⟦A⟧ & e
──────────────────────────────────────────────────────────────────────────────────────────
⟦D⟧⇐ₚ :: ⟦Γ⟧ ⊢_p labeledBlock l M_b M_k ⇐ ⟦A⟧ & e


D :: Γ ⊢_L (exit l) : A    (l : ⟦A⟧ & e) ∈ ⟦Γ⟧

        ↦

⟦D⟧⇐ₚ :: ⟦Γ⟧ ⊢_p exit l ⇐ ⟦A⟧ & e    (via producer synthesis: look up l)
```

The remaining clauses (while, assume, field write, subscript assignment,
new, ternary desugar, expression-as-statement) follow the same pattern:
sub-expressions via ⟦·⟧⇐ᵥ, continuation via ⟦·⟧⇐ₚ, assemble the GFGL
producer checking derivation.

#### Core interface requirements

The Laurel→Core translator imposes constraints on the elaborated output:

1. **function vs procedure:** `synthValue` only accepts grade = pure callees.
   Grade > pure forces the call through the producer path (statement level).

2. **Datatype constructors** (from_int, ListAny_cons, etc.) are expressions.
   The elaborator treats them as pure functions (they have FuncSigs in the prelude).

3. **Output arity:** effectfulCall outputs must match the callee's declared
   output count exactly.

4. **`__main__` metadata:** `__main__` must have sourceRangeToMd metadata
   so Core generates VCs from its assertions.

5. **No Holes in output:** Every Hole in the input is translated to a fresh
   function declaration ($havoc_N or $hole_N). These are added to the output
   program's function list.


## Projection

Trivial catamorphism. Forget grades. Map GFGL → Laurel:

- `effectfulCall md f args outputs body` → `[decl outputs; Assign [outputs] (StaticCall f args); body]`
- `assign md target val body` → `[Assign [target] val; body]`
- `varDecl md x ty init body` → `[LocalVariable x ty init; body]`
- Values map to their Laurel equivalents directly.

### Source Metadata (Correct by Construction)

Every GFGL constructor carries an `md : Md` field (= `Imperative.MetaData Core.Expression`)
from the source `StmtExprMd` that produced it. Projection extracts `md` structurally:

```lean
partial def projectValue : FGLValue → StmtExprMd
  | .litInt md n => mkLaurel md (.LiteralInt n)
  | .var md name => mkLaurel md (.Identifier ...)
  | .staticCall md name args => mkLaurel md (.StaticCall ...)
  ...

partial def projectProducer : FGLProducer → List StmtExprMd
  | .assert md cond body => [mkLaurel md (.Assert ...)] ++ projectProducer body
  ...
```

No `md` parameter to projection — it's impossible to use the wrong metadata
because each GFGL term carries its own. Coercions inserted by subsumption inherit
`md` from the value being coerced (via `val.getMd`).

---

## Translation Desugarings

| Python | Laurel |
|---|---|
| `x = expr` | `Assign [x] expr` |
| `a, b = rhs` | `tmp := rhs; a := Get(tmp,0); b := Get(tmp,1)` |
| `x += v` | `Assign [x] (PAdd x v)` |
| `x[i] = v` | `Assign [x] (Any_sets(ListAny_cons(i, ListAny_nil()), x, v))` |
| `x[i][j] = v` | `Assign [x] (Any_sets(ListAny_cons(i, ListAny_cons(j, ListAny_nil())), x, v))` |
| `x[start:stop]` | `Any_get(x, from_Slice(Any..as_int!(start), OptSome(Any..as_int!(stop))))` |
| `x[start:]` | `Any_get(x, from_Slice(Any..as_int!(start), OptNone()))` |
| `return e` | `LaurelResult := e; exit $body` |
| `Foo(args)` (class) | `Assign [tmp] (New Foo); Foo@__init__(tmp, args)` |
| `with mgr as v: body` | `v := Type@__enter__(mgr); body; Type@__exit__(mgr)` |
| `for x in iter: body` | `x := Hole; Assume(PIn(x, iter)); body` (labeled blocks for break/continue) |
| `[a, b, c]` | `from_ListAny(ListAny_cons(a, ListAny_cons(b, ListAny_cons(c, ListAny_nil()))))` |
| `{k: v}` | `from_DictStrAny(DictStrAny_cons(k, v, DictStrAny_empty()))` |
| `f"{expr}"` | `to_string_any(expr)` |
| `str(x)` | `to_string_any(x)` (via builtinMap) |

### Method FuncSigs

Method FuncSigs include `self` with type `UserDefined className`:
```
MyClass@__init__ : (self: MyClass, param1: T1, ...) → Any
```
Translation strips self from the FuncSig params when building the proc's
input list (to avoid duplicate self with the explicit selfParam it adds).

### __main__ Metadata

`__main__` MUST have `sourceRangeToMd filePath default` metadata so Core
classifies it as a user proc and generates VCs. Without it: vacuous passes.

### Constructor FuncSigs in Prelude

Datatype constructors used by Translation/Elaboration must have FuncSigs
in `preludeSignatures` so the elaborator can check args at correct types:
- `from_Slice : (int, OptionInt) → Any`
- `OptSome : (int) → OptionInt`
- `OptNone : () → OptionInt`
- `Any_sets : (ListAny, Any, Any) → Any`
- `BoxAny : (Any) → Box` (for Any-typed fields)

---

## Python Construct Coverage

Explicit accounting of what Translation handles, what it approximates,
and what it does not support.

**Fully handled (precise translation):**
- Literals (int, bool, str, None)
- Variables (identifiers, scope hoisting)
- Binary/comparison/boolean/unary operators (→ prelude StaticCalls)
- Function definitions (params, defaults, kwargs, return)
- Class definitions (fields, __init__, methods with self)
- Assignments (simple, augmented, annotated, tuple unpacking)
- Control flow (if/elif/else, while, for, break, continue)
- Return statements
- Assert/assume
- Try/except (labeled blocks + isError guards)
- Context managers (with/as)
- List/dict/tuple literals (→ ListAny_cons/DictStrAny_cons encoding)
- F-strings (→ to_string_any)
- Subscript read/write (→ Any_get/Any_sets)
- Slice notation (→ from_Slice)
- Module imports (→ qualified name resolution)
- Class instantiation (→ New + __init__)
- Method calls (→ qualified StaticCall with self)

**Approximated (Hole — sound but imprecise):**
- Unresolved names (not in Γ → nondeterministic Hole)
- Lambda expressions
- List/set/dict comprehensions
- Generator expressions
- Walrus operator (:=)
- Match statements
- Async constructs (async for, async with, await)
- Decorators
- Star expressions
- Float literals (represented as string — no real arithmetic)

**Not supported (Translation throws):**
- Chained comparisons (`a < b < c`)
- Multiple assignment targets (`x = y = 5`)

---

## Known Tech Debt

**Narrowing as pure function:** `Any_to_bool` etc. are modeled as pure (grade 1).
In Python, `__bool__` can have side effects. If needed later, narrowing becomes
grade > 1 and the coercion scheme changes.

**Instance procedures:** Methods emitted as top-level statics with `self` as first param.
`instanceProcedures` on CompositeType is empty.

**Prelude data encodings:** Lists/dicts are recursive ADTs (`ListAny_cons`/`DictStrAny_cons`).
Translation must emit these specific constructors.

---

## Current Status (2026-05-08)

### Parity with the Current Pipeline

The question is not "how many tests pass" but "are we replicating the current
pipeline's results?" On the 46 CI tests with expected outputs:

- **42/46 tests:** New pipeline replicates the current pipeline's result
  (same RESULT line — both pass, or both inconclusive)
- **3/46 tests:** Current pipeline passes, new pipeline is inconclusive
  (solver can't prove VCs that the current encoding allows — encoding quality
  gap in try/except and module-level code, not a correctness issue)
- **1/46 tests:** New pipeline passes where current was inconclusive
  (test_multiple_except: 8 real VCs proven — genuine improvement)

Zero crashes on the 46 CI tests. Two non-CI tests (`test_foo_client_folder`,
`test_invalid_client_type`) crash due to a missing runtime function
(`Any_type_to_Any` — the Python `type()` builtin is not yet in the prelude).
The current pipeline is verified intact and serves as the comparison baseline.

The 3 encoding gaps are in tests with nested try/except (`test_try_except_scoping`)
and module-level code that calls runtime procedures (`test_datetime`,
`test_dict_operations`). These produce correct but more complex VC structure
that the solver needs more time to handle.

### Key Implementation Decisions

- `annotationToHighType` handles Union/generic types directly (→ Any)
- Translation emits Hole for unresolved names (no undefined StaticCalls)
- `mkGradedCall` uses proc's declared outputs (no output arity mismatch)
- `proc` grade for runtime procedures (statement-level binding)
- `ifThenElse`/`labeledBlock` have `after` continuation (no VC blowup)
- `__main__` has metadata (VCs generated from module-level asserts)
- `gradeFromSignature` uses `isFunctional` (function vs procedure)

---

## Success Criteria

1. All 54 in-tree tests pass.
2. Translation is a fold — no post-hoc rewrites.
3. Elaboration is separate — translation emits no casts or grades.
4. Types from annotations — `Any` only when annotation absent.
5. One file per pass.
6. Implementation reads as transcription of the typing rules.

---

## Files

```
NameResolution.lean    -- Build Γ
Translation.lean       -- Fold over AST → Laurel
Elaborate.lean         -- Graded bidirectional elaboration
Pipeline.lean          -- Wire passes, CLI
```

---

## References

- **Levy** (2003). *Call-By-Push-Value.* Value/Producer.
- **Egger, Møgelberg, Staton** (2014). "Linear Usage of State." State-passing translation.
- **McDermott** (2025). "Grading call-by-push-value." Graded CBPV, implicit grading, coherence.
- **Dunfield & Krishnaswami** (2021). "Bidirectional Typing." Synth/check/subsumption.
- **Harper & Morrisett** (1995). "Compiling Polymorphism." Type-directed compilation.
