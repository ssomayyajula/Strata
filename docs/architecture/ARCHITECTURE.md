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

The context Γ' carries two kinds of bindings:
- **Variables** `(x : A)` — looked up by value synthesis
- **Labels** `(l : A & e)` — looked up by producer synthesis

Labels are to producers what variables are to values. A label `l : A & e` in
context means "there is a continuation at label l that accepts type A at grade e."

```
Γ' ⊢_v V ⇒ A           value synthesis (output: type A)
Γ' ⊢_v V ⇐ A           value checking (input: expected type A)
Γ' ⊢_p M ⇒ A & d       producer synthesis (output: type A, grade d)
Γ' ⊢_p M ⇐ A & e       producer checking (input: result type A, ambient grade e)
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

Labels are to producers what variables are to values:

```
(l : A & e) ∈ Γ'
─────────────────────────
Γ' ⊢_p exit l ⇒ A & e


(κ : A & e) ∈ Γ'
─────────────────────────
Γ' ⊢_p unit ⇒ A & e
```

`exit l` jumps to a named label. `unit` jumps to the implicit current
continuation κ. Both synthesize their type and grade from the context.

```
f : (A₁,...,Aₙ) → B & d ∈ Γ'    Γ' ⊢_v V₁ ⇐ A₁  ...  Γ' ⊢_v Vₙ ⇐ Aₙ
──────────────────────────────────────────────────────────────────────────
Γ' ⊢_p f(V₁,...,Vₙ) ⇒ B & d
```

#### Producer subsumption (mode switch ⇒ₚ to ⇐ₚ)

```
Γ' ⊢_p M ⇒ B & d    subsume(B, A) = c    Γ',x₁:T₁,...,xₖ:Tₖ ⊢_p M_k ⇐ A & (d\e)
──────────────────────────────────────────────────────────────────────────────────────
Γ',x₁:T₁,...,xₖ:Tₖ ⊢_p effectfulCall f [Vᵢ] [x₁:T₁,...,xₖ:Tₖ] (... c(xⱼ) ... M_k) ⇐ A & e
```

Analogous to value subsumption. The synthesized producer is bound via
effectfulCall. Outputs come from f's declared signature. Type coercion c
is applied in the continuation. Continuation checked at residual `d\e`.

#### Producer checking rules

```
Γ' ⊢_v V ⇐ A
──────────────────────────────────────
Γ' ⊢_p returnValue V ⇐ A & e


Γ' ⊢_v V ⇐ Γ'(x)    Γ' ⊢_p M_k ⇐ A & e
───────────────────────────────────────────
Γ' ⊢_p assign x V M_k ⇐ A & e


Γ' ⊢_v V ⇐ T    Γ',x:T ⊢_p M_k ⇐ A & e
───────────────────────────────────────────
Γ',x:T ⊢_p varDecl x T V M_k ⇐ A & e


Γ',κ:(A & e) ⊢_v V ⇐ bool    Γ',κ:(A & e) ⊢_p M_t ⇐ A & e    Γ',κ:(A & e) ⊢_p M_f ⇐ A & e    Γ' ⊢_p M_k ⇐ A & e
──────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────
Γ' ⊢_p ifThenElse V M_t M_f M_k ⇐ A & e


Γ',κ:(A & e) ⊢_v V ⇐ bool    Γ',κ:(A & e) ⊢_p M_b ⇐ A & e    Γ' ⊢_p M_k ⇐ A & e
──────────────────────────────────────────────────────────────────────────────────────
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

Note: `labeledBlock l M_b M_k` binds label `l` in the context for M_b —
so `exit l` inside the body can synthesize its type. `ifThenElse` and
`whileLoop` bind the implicit continuation κ in their branches/body —
so `unit` inside them can synthesize. M_k (the after-continuation) is
checked in the outer context without the label binding.

### Elaboration (⟦·⟧ : Laurel Derivations → GFGL Derivations)

Elaboration is defined by four mutually recursive functions on Laurel
typing derivations, producing derivations in the GFGL system above:

```
⟦·⟧⇒ᵥ : (D :: Γ ⊢_L e : A) → (⟦D⟧⇒ᵥ :: Γ' ⊢_v V ⇒ A')           value synthesis
⟦·⟧⇐ᵥ : (D :: Γ ⊢_L e : A, B) → (⟦D⟧⇐ᵥ :: Γ' ⊢_v V ⇐ B)         value checking
⟦·⟧⇒ₚ : (D :: Γ ⊢_L e : A) → SynthResult                            producer synthesis
⟦·⟧⇐ₚ : (D :: Γ ⊢_L S;rest : A, e) → (⟦D⟧⇐ₚ :: Γ' ⊢_p M ⇐ A & e) producer checking
```

The output of each function is a valid derivation in the GFGL system.
Mode correctness is auditable by checking that each output matches a
GFGL rule from the section above.

#### ⟦·⟧⇒ᵥ  (value synthesis)

```
D :: Γ ⊢_L n : int

        ↦

⟦D⟧⇒ᵥ :: Γ ⊢_v litInt n ⇒ TInt


(x : A) ∈ Γ
─────────────────
D :: Γ ⊢_L x : A

        ↦

⟦D⟧⇒ᵥ :: Γ ⊢_v var x ⇒ eraseType(A)


D₁ :: Γ ⊢_L e₁ : A₁  ...  Dₙ :: Γ ⊢_L eₙ : Aₙ
──────────────────────────────────────────────────
D :: Γ ⊢_L f(e₁,...,eₙ) : B    where grade(f) = pure

        ↦

⟦D₁⟧⇐ᵥ :: Γ' ⊢_v V₁ ⇐ A₁  ...  ⟦Dₙ⟧⇐ᵥ :: Γ' ⊢_v Vₙ ⇐ Aₙ
────────────────────────────────────────────────────────────────
⟦D⟧⇒ᵥ :: Γ' ⊢_v staticCall f [V₁,...,Vₙ] ⇒ eraseType(B)


D_obj :: Γ ⊢_L e : C    fields(C,f) = T
────────────────────────────────────────
D :: Γ ⊢_L e.f : T

        ↦

⟦D_obj⟧⇐ᵥ :: Γ' ⊢_v V_obj ⇐ Composite
──────────────────────────────────────────────────────────────────────
⟦D⟧⇒ᵥ :: Γ' ⊢_v Box..tVal!(readField($heap, V_obj, $field.C.f)) ⇒ eraseType(T)


D :: Γ ⊢_L ?? : A

        ↦

⟦D⟧⇒ᵥ :: Γ,$havoc_N ⊢_v staticCall $havoc_N [] ⇒ Any


D :: Γ ⊢_L ? : A

        ↦

⟦D⟧⇒ᵥ :: Γ,$hole_N ⊢_v staticCall $hole_N [] ⇒ Any
```

#### ⟦·⟧⇐ᵥ  (value checking = synthesis + subsumption)

```
⟦D⟧⇒ᵥ :: Γ' ⊢_v V ⇒ A    subsume(A, B) = c
─────────────────────────────────────────────
⟦D⟧⇐ᵥ :: Γ' ⊢_v c(V) ⇐ B
```

This is exactly the GFGL subsumption rule applied to the synthesized derivation.

#### ⟦·⟧⇒ₚ  (producer synthesis — defunctionalized)

```
inductive SynthResult where
  | value (V : FGLValue) (A : LowType)
  | call (callee args retTy : ...) (d : Grade)
```

```
D₁ :: Γ ⊢_L e₁ : A₁  ...  Dₙ :: Γ ⊢_L eₙ : Aₙ
──────────────────────────────────────────────────
D :: Γ ⊢_L f(e₁,...,eₙ) : B

If grade(f) = pure:    ⟦D⟧⇒ₚ = .value (⟦D⟧⇒ᵥ).V (⟦D⟧⇒ᵥ).A
If grade(f) = d > pure: ⟦D⟧⇒ₚ = .call f [⟦D₁⟧⇐ᵥ,...,⟦Dₙ⟧⇐ᵥ] (eraseType B) d
```

⟦·⟧⇒ₚ does NOT produce a derivation — it produces data that ⟦·⟧⇐ₚ uses
to construct the output derivation (via producer subsumption). This is
the defunctionalization: the grade determines the calling convention, but
the calling convention requires the ambient grade (from ⟦·⟧⇐ₚ's input)
to compute the residual.

#### Producer subsumption (⟦·⟧⇒ₚ meets ⟦·⟧⇐ₚ)

When ⟦·⟧⇒ₚ yields `.call f args B d` inside ⟦·⟧⇐ₚ at ambient grade e:

```
⟦D⟧⇒ₚ = .call f args B d    subgrade(d,e) = conv    K :: Γ ⊢_L rest : A
─────────────────────────────────────────────────────────────────────────

        ↦

⟦D₁⟧⇐ᵥ :: Γ' ⊢_v V₁ ⇐ A₁  ...  ⟦Dₙ⟧⇐ᵥ :: Γ' ⊢_v Vₙ ⇐ Aₙ    ⟦K⟧⇐ₚ :: Γ',x₁:T₁,...,xₖ:Tₖ ⊢_p M_k ⇐ A & (d\e)
─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────
Γ',x₁:T₁,...,xₖ:Tₖ ⊢_p effectfulCall f [V₁,...,Vₙ] [x₁:T₁,...,xₖ:Tₖ] M_k ⇐ A & e
```

The outputs [x₁:T₁,...,xₖ:Tₖ] come from f's declared signature.
The conv witness (procCall/errorCall/heapCall/heapErrorCall) determines
whether heap is prepended to args — but this is a property of f's
signature, not of the typing rule.

#### ⟦·⟧⇐ₚ  (producer checking)

```
D_c :: Γ ⊢_L c : bool    D_t :: Γ ⊢_L t : A    D_f :: Γ ⊢_L f : A    K :: Γ ⊢_L rest : A
─────────────────────────────────────────────────────────────────────────────────────────────
D :: Γ ⊢_L (if c then t else f); rest : A

        ↦

⟦D_c⟧⇐ᵥ :: Γ' ⊢_v V ⇐ bool    ⟦D_t⟧⇐ₚ :: Γ' ⊢_p M_t ⇐ A & e    ⟦D_f⟧⇐ₚ :: Γ' ⊢_p M_f ⇐ A & e    ⟦K⟧⇐ₚ :: Γ' ⊢_p M_k ⇐ A & e
──────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────
⟦D⟧⇐ₚ :: Γ' ⊢_p ifThenElse V M_t M_f M_k ⇐ A & e


D_c :: Γ ⊢_L c : bool    D_b :: Γ ⊢_L body : A    K :: Γ ⊢_L rest : A
────────────────────────────────────────────────────────────────────────
D :: Γ ⊢_L (while c do body); rest : A

        ↦

⟦D_c⟧⇐ᵥ :: Γ' ⊢_v V ⇐ bool    ⟦D_b⟧⇐ₚ :: Γ' ⊢_p M_b ⇐ A & e    ⟦K⟧⇐ₚ :: Γ' ⊢_p M_k ⇐ A & e
─────────────────────────────────────────────────────────────────────────────────────────────────────
⟦D⟧⇐ₚ :: Γ' ⊢_p whileLoop V M_b M_k ⇐ A & e


D_e :: Γ ⊢_L e : A
───────────────────
D :: Γ ⊢_L (return e) : A

        ↦

⟦D_e⟧⇐ᵥ :: Γ' ⊢_v V ⇐ eraseType(A)
─────────────────────────────────────────
⟦D⟧⇐ₚ :: Γ' ⊢_p returnValue V ⇐ A & e


D :: Γ ⊢_L (exit l) : A

        ↦

⟦D⟧⇐ₚ :: Γ ⊢_p exit l ⇐ A & e


D_init :: Γ ⊢_L e : T    K :: Γ,x:T ⊢_L rest : A
───────────────────────────────────────────────────
D :: Γ ⊢_L (var x:T := e); rest : A

        ↦

⟦D_init⟧⇐ᵥ :: Γ' ⊢_v V ⇐ eraseType(T)    ⟦K⟧⇐ₚ :: Γ',x:eraseType(T) ⊢_p M_k ⇐ A & e
──────────────────────────────────────────────────────────────────────────────────────────
⟦D⟧⇐ₚ :: Γ',x:eraseType(T) ⊢_p varDecl x (eraseType T) V M_k ⇐ A & e


D_c :: Γ ⊢_L c : bool    K :: Γ ⊢_L rest : A
──────────────────────────────────────────────
D :: Γ ⊢_L (assert c); rest : A

        ↦

⟦D_c⟧⇐ᵥ :: Γ' ⊢_v V ⇐ bool    ⟦K⟧⇐ₚ :: Γ' ⊢_p M_k ⇐ A & e
────────────────────────────────────────────────────────────────
⟦D⟧⇐ₚ :: Γ' ⊢_p assert V M_k ⇐ A & e


D_c :: Γ ⊢_L c : bool    K :: Γ ⊢_L rest : A
──────────────────────────────────────────────
D :: Γ ⊢_L (assume c); rest : A

        ↦

⟦D_c⟧⇐ᵥ :: Γ' ⊢_v V ⇐ bool    ⟦K⟧⇐ₚ :: Γ' ⊢_p M_k ⇐ A & e
────────────────────────────────────────────────────────────────
⟦D⟧⇐ₚ :: Γ' ⊢_p assume V M_k ⇐ A & e


D_body :: Γ ⊢_L {s₁;...;sₙ} : A    K :: Γ ⊢_L rest : A
──────────────────────────────────────────────────────────
D :: Γ ⊢_L {s₁;...;sₙ}ₗ; rest : A    (labeled)

        ↦

⟦D_body⟧⇐ₚ :: Γ' ⊢_p M_b ⇐ A & e    ⟦K⟧⇐ₚ :: Γ' ⊢_p M_k ⇐ A & e
──────────────────────────────────────────────────────────────────────
⟦D⟧⇐ₚ :: Γ' ⊢_p labeledBlock l M_b M_k ⇐ A & e


D₁ :: Γ ⊢_L e₁ : A₁  ...  Dₙ :: Γ ⊢_L eₙ : Aₙ    K :: Γ ⊢_L rest : A
──────────────────────────────────────────────────────────────────────────
D :: Γ ⊢_L f(e₁,...,eₙ); rest : A    where ⟦D⟧⇒ₚ = .call f args B d

        ↦

(producer subsumption — see above)


D_e :: Γ ⊢_L e : B    K :: Γ ⊢_L rest : A
────────────────────────────────────────────
D :: Γ ⊢_L (x := e); rest : A    where ⟦D_e⟧⇒ₚ = .value V T

        ↦

⟦D_e⟧⇐ᵥ :: Γ' ⊢_v V ⇐ eraseType(Γ(x))    ⟦K⟧⇐ₚ :: Γ' ⊢_p M_k ⇐ A & e
────────────────────────────────────────────────────────────────────────────
⟦D⟧⇐ₚ :: Γ' ⊢_p assign x V M_k ⇐ A & e


D_e :: Γ ⊢_L e : B    K :: Γ ⊢_L rest : A
────────────────────────────────────────────
D :: Γ ⊢_L (x := e); rest : A    where ⟦D_e⟧⇒ₚ = .call f args B d

        ↦

(producer subsumption with continuation: assign x (subsume(r, Γ(x))) ⟦K⟧⇐ₚ)


D_obj :: Γ ⊢_L obj : C    D_v :: Γ ⊢_L v : fieldType(C,f)    K :: Γ ⊢_L rest : A
────────────────────────────────────────────────────────────────────────────────────
D :: Γ ⊢_L (obj.f := v); rest : A    where heap ≤ e

        ↦

⟦D_obj⟧⇐ᵥ :: Γ' ⊢_v V_obj ⇐ Composite    ⟦D_v⟧⇐ᵥ :: Γ' ⊢_v V_val ⇐ fieldType    ⟦K⟧⇐ₚ :: Γ',$h:Heap ⊢_p M_k ⇐ A & e
──────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────
⟦D⟧⇐ₚ :: Γ',$h:Heap ⊢_p varDecl $h Heap (updateField($heap, V_obj, $field.C.f, BoxT(V_val))) M_k ⇐ A & e


D_r :: Γ ⊢_L root : Any    D_i :: Γ ⊢_L idx : Any    D_v :: Γ ⊢_L v : Any    K :: Γ ⊢_L rest : A
────────────────────────────────────────────────────────────────────────────────────────────────────
D :: Γ ⊢_L (root[idx] := v); rest : A

        ↦

⟦D_r⟧⇐ᵥ :: Γ' ⊢_v V_r ⇐ Any    ⟦D_i⟧⇐ᵥ :: Γ' ⊢_v V_i ⇐ Any    ⟦D_v⟧⇐ᵥ :: Γ' ⊢_v V_v ⇐ Any    ⟦K⟧⇐ₚ :: Γ' ⊢_p M_k ⇐ A & e
──────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────
⟦D⟧⇐ₚ :: Γ' ⊢_p assign root (staticCall Any_sets [V_i, V_r, V_v]) M_k ⇐ A & e


K :: Γ ⊢_L rest : A
─────────────────────────
D :: Γ ⊢_L ??; rest : A

        ↦

⟦K⟧⇐ₚ :: Γ',$hv:Any ⊢_p M_k ⇐ A & e
────────────────────────────────────────────────────
⟦D⟧⇐ₚ :: Γ',$hv:Any ⊢_p varDecl $hv Any none M_k ⇐ A & e


K :: Γ ⊢_L rest : A
───────────────────────────────────────
D :: Γ ⊢_L (x := new C); rest : A    where heap ≤ e

        ↦

⟦K⟧⇐ₚ :: Γ',$h:Heap ⊢_p M_k ⇐ A & e
────────────────────────────────────────────────────────────────────────────────────────
⟦D⟧⇐ₚ :: Γ',$h:Heap ⊢_p varDecl $h Heap (increment $heap) (assign x (MkComposite ...) M_k) ⇐ A & e


D_c :: Γ ⊢_L c : bool    D_a :: Γ ⊢_L a : B    D_b :: Γ ⊢_L b : B    K :: Γ ⊢_L rest : A
─────────────────────────────────────────────────────────────────────────────────────────────
D :: Γ ⊢_L (x := if c then a else b); rest : A

        ↦

⟦(if c then (x:=a) else (x:=b)); rest⟧⇐ₚ    [desugar, re-enter ⟦·⟧⇐ₚ]
```

#### The to-rule (ANF lifting effectful arguments)

When ⟦·⟧⇐ᵥ is invoked on an argument whose ⟦·⟧⇒ₚ yields `.call`:

```
Dᵢ :: Γ ⊢_L eᵢ : Aᵢ    where ⟦Dᵢ⟧⇒ₚ = .call gᵢ argsᵢ Bᵢ dᵢ

        ↦

⟦Dᵢ_args⟧⇐ᵥ :: ...    ⟦cont⟧⇐ₚ :: Γ',rᵢ:Bᵢ ⊢_p ... ⇐ A & (dᵢ\e)
──────────────────────────────────────────────────────────────────────
Γ',rᵢ:Bᵢ ⊢_p effectfulCall gᵢ argsᵢ [rᵢ:Bᵢ] ⟦cont⟧⇐ₚ ⇐ A & e
```

The bound variable rᵢ replaces eᵢ in the outer call's argument list.
Left-to-right. Each lift nests one effectfulCall around the continuation.

#### Value subsumption (mode switch ⇒ᵥ to ⇐ᵥ)

```
⟦D⟧⇒ᵥ :: Γ' ⊢_v V ⇒ A    subsume(A, B) = c
─────────────────────────────────────────────
⟦D⟧⇐ᵥ :: Γ' ⊢_v c(V) ⇐ B
```

The coercion c is proof-relevant — it becomes GFGL term structure.

### Subsumption Table (Type Coercions)

```lean
-- CoercionResult carries (Md → FGLValue → FGLValue) so coercions inherit
-- source metadata from the value being coerced.
inductive CoercionResult where | refl | coerce (w : Md → FGLValue → FGLValue) | unrelated

def subsume (actual expected : LowType) : CoercionResult :=
  if actual == expected then .refl else match actual, expected with
  | .TInt, .TCore "Any"         => .coerce (fun md => .fromInt md)
  | .TBool, .TCore "Any"        => .coerce (fun md => .fromBool md)
  | .TString, .TCore "Any"      => .coerce (fun md => .fromStr md)
  | .TFloat64, .TCore "Any"     => .coerce (fun md => .fromFloat md)
  | .TCore "Composite", .TCore "Any" => .coerce (fun md => .fromComposite md)
  | .TCore "ListAny", .TCore "Any"   => .coerce (fun md => .fromListAny md)
  | .TCore "DictStrAny", .TCore "Any" => .coerce (fun md => .fromDictStrAny md)
  | .TVoid, .TCore "Any"        => .coerce (fun md _ => .fromNone md)
  | .TCore "Any", .TBool        => .coerce (fun md v => .staticCall md "Any_to_bool" [v])
  | .TCore "Any", .TInt         => .coerce (fun md v => .staticCall md "Any..as_int!" [v])
  | .TCore "Any", .TString      => .coerce (fun md v => .staticCall md "Any..as_string!" [v])
  | .TCore "Any", .TFloat64     => .coerce (fun md v => .staticCall md "Any..as_float!" [v])
  | .TCore "Any", .TCore "Composite" => .coerce (fun md v => .staticCall md "Any..as_Composite!" [v])
  | _, _ => .unrelated

def applySubsume (val : FGLValue) (actual expected : LowType) : FGLValue :=
  match subsume actual expected with | .refl => val | .coerce c => c val.getMd val | .unrelated => val
```

### Coercion Table (validated against PythonRuntimeLaurelPart.lean)

**Subtyping (A <: B, infallible):**

| A | B | Witness | Source |
|---|---|---|---|
| int | Any | `from_int` | Prelude |
| bool | Any | `from_bool` | Prelude |
| str | Any | `from_str` | Prelude |
| real | Any | `from_float` | Prelude (note: `real` not `float64`) |
| Composite | Any | `from_Composite` | Prelude |
| ListAny | Any | `from_ListAny` | Prelude |
| DictStrAny | Any | `from_DictStrAny` | Prelude |
| TVoid | Any | `from_None` | Prelude |
| T | Box | `BoxT(val)` | Generated (type-directed: BoxInt, BoxBool, BoxComposite, ...) |

**Narrowing (A ▷ B, partial — precondition-guarded):**

| A | B | Witness | Source |
|---|---|---|---|
| Any | bool | `Any_to_bool` | Prelude (truthiness) |
| Any | int | `Any..as_int!` | DDM-generated |
| Any | str | `Any..as_string!` | DDM-generated |
| Any | real | `Any..as_float!` | DDM-generated |
| Any | Composite | `Any..as_Composite!` | DDM-generated |
| Any | ListAny | `Any..as_ListAny!` | DDM-generated |
| Any | DictStrAny | `Any..as_Dict!` | DDM-generated |
| Box | T | `Box..tVal!(box)` | Generated (type-directed: Box..intVal!, Box..boolVal!, ...) |

Both produce VALUES. Narrowing is partial (precondition-guarded).
No grade contribution — these are value-level operations.

### Composite and Any

`Any` is a tagged union. `Composite` is a heap reference (`MkComposite(ref: int, typeTag: TypeTag)`).
`Composite <: Any` via `from_Composite` (pointer-preserving injection).
`Any ▷ Composite` via `Any..as_Composite!`.

### Heap Field Access (Type-Directed Box Protocol)

The heap stores fields as `Box` values. `Box` is a sum type with one constructor
per primitive type used in fields:

```
datatype Box { BoxInt(intVal: int) | BoxBool(boolVal: bool) | BoxComposite(compositeVal: Composite) | ... }
```

Constructors and destructors are type-directed, selected by the field's declared
type from `classFields` in TypeEnv:

| Field type | Box constructor | Box destructor |
|---|---|---|
| int | `BoxInt(val)` | `Box..intVal!(box)` |
| bool | `BoxBool(val)` | `Box..boolVal!(box)` |
| float64 | `BoxFloat64(val)` | `Box..float64Val!(box)` |
| str | `BoxString(val)` | `Box..stringVal!(box)` |
| Composite | `BoxComposite(val)` | `Box..compositeVal!(box)` |
| UserDefined T | `Box..T(val)` | `Box..TVal!(box)` |
| TCore name | `Box..name(val)` | `Box..nameVal!(box)` |

Field read: `Box..tVal!(readField($heap, obj, ClassName.fieldName))` → value at field type
Field write: `$heap := updateField($heap, obj, ClassName.fieldName, BoxT(value))`

The qualified field name `ClassName.fieldName` is a zero-arg constructor of the
`Field` datatype. One constructor per declared field across all classes.

The `Box` datatype is generated with only the constructors actually used (tracked
during elaboration). The `Field` datatype is generated from all fields in
`classFields`.

### Subgrading Witness (Defunctionalized Calling Convention)

`subgrade(d, e)` returns a `ConventionWitness` when `d ≤ e`. The witness is
proof-relevant: it determines the GFGL term produced at the call site.

```lean
inductive ConventionWitness where
  | pureCall                -- grade 1: value-level, no binding
  | procCall                -- grade proc: bind with proc's declared outputs (statement-level)
  | errorCall               -- grade err: bind [result, error]
  | heapCall                -- grade heap: pass heap, bind [heap', result]
  | heapErrorCall           -- grade heap·err: pass heap, bind [heap', result, error]

def subgrade : Grade → Grade → Option ConventionWitness
  | .pure,    _        => some .pureCall
  | .proc,    .proc    => some .procCall
  | .proc,    .err     => some .procCall
  | .proc,    .heap    => some .procCall
  | .proc,    .heapErr => some .procCall
  | .err,     .err     => some .errorCall
  | .err,     .heapErr => some .errorCall
  | .heap,    .heap    => some .heapCall
  | .heap,    .heapErr => some .heapCall
  | .heapErr, .heapErr => some .heapErrorCall
  | _,        _        => none
```

**`procCall` convention:** `mkProcCall md callee args declaredOutputs body` —
binds the procedure's DECLARED outputs (read from Laurel.Procedure.outputs
or derived from the runtime program). No extra error/heap added. The outputs
are NOT determined by the grade alone — they come from the proc's signature.

ALL grades use declared outputs via `mkGradedCall`. The grade determines
only whether to prepend the heap argument. Outputs are never invented.

Examples:
- `print(msg: Any) returns ()` → 0 outputs → effectfulCall with [] → body receives no result
- `datetime_now() returns (ret: Any)` → 1 output → effectfulCall with [ret] → body receives ret

The call site must look up the proc's declared outputs to construct the
effectfulCall. This information comes from the runtime program's
`staticProcedures` list (for runtime procs) or from the user program's
proc definitions (for user procs after signature rewriting).

Application via smart constructors (read heapVar from state internally):

```lean
-- Smart constructors dispatch on the convention witness.
-- They take md from the source statement, read heapVar from ElabState,
-- prepend heap if needed, generate fresh output names (HOAS), extend Γ,
-- call body closure.

-- ALL graded call constructors use the proc's DECLARED outputs.
-- The grade determines only whether to prepend the heap argument.
-- Outputs are NEVER invented — they come from the proc's signature.

def mkGradedCall (md callee args declaredOutputs grade) (body : FGLValue → ElabM FGLProducer)
  -- grade pure: no binding (value level) — NOT a call constructor
  -- grade proc/err: effectfulCall callee args declaredOutputs body
  -- grade heap/heapErr: effectfulCall callee (heap::args) declaredOutputs body
  --   (prepend heap arg, declared outputs already include heap output)

def mkVarDecl (md name ty init) (body : FGLValue → ElabM FGLProducer)
```

### Elaboration Structure

**Textbook typing rules** (pure, no state mutation, no flags):

```lean
-- Value judgment: no grades
synthValue (expr) : ElabM (FGLValue × LowType)
checkValue (expr) (expected : HighType) : ElabM FGLValue

-- Producer synthesis: defunctionalized result (grade + enough to build GFGL)
inductive SynthResult where
  | value (val : FGLValue) (ty : LowType)         -- grade 1 (pure call or literal)
  | call (callee args retTy grade)                 -- grade > 1 (effectful call)

synthExpr (expr) : ElabM SynthResult

-- Producer checking: inputs grade, produces GFGL
checkProducer (stmt) (rest : List Stmt) (grade : Grade) : ElabM FGLProducer
```

**Block elaboration** (to-rule applied to statements and nested expressions):

For each statement in a block, `checkProducer` threads the rest as the
continuation. For nested expressions within a statement (e.g., effectful
call as argument to a pure call), `synthExpr` determines if the expression
is a value or producer. Producers are bound via the to-rule:

```
checkArgsK [arg₁, arg₂, ...] params grade cont:
  synthExpr arg₁ →
  | .value v ty   → cont (coerce v :: acc)
  | .call f a t d → mkSmartConstructor f a t d (fun rv → cont (coerce rv :: acc))
```

This is the to-rule applied at expression level: effectful subexpressions
are sequenced into let-bindings (ANF). The defunctionalized `SynthResult`
avoids closures — the grade is data, not a flag.

**Grade lookup during elaboration** is a pure HashMap read from the
environment (all grades pre-computed by coinduction). No body
evaluation during term production.

### Producer Subsumption (see §Subsumption above for the full rule)

The `conv` witness selects `mkGradedCall` with the appropriate grade:
- `pureCall` → no binding (value level)
- `procCall` → `mkGradedCall md callee args declaredOutputs .proc`
- `errorCall` → `mkGradedCall md callee args declaredOutputs .err`
- `heapCall` → `mkGradedCall md callee args declaredOutputs .heap`
- `heapErrorCall` → `mkGradedCall md callee args declaredOutputs .heapErr`

The `c` witness coerces `rv` inside the continuation (after binding).

### Heap Operations

| Source | Grade | Elaborated |
|---|---|---|
| `.New classId` | `heap` | `$heap := increment($heap); MkComposite(Heap..nextReference!($heap_prev), classId_TypeTag())` |
| `.FieldSelect obj field` | `heap` | `Box..tVal!(readField($heap, obj, ClassName.fieldName))` (t = field's declared type) |
| `Assign [FieldSelect obj f] v` | `heap` | `$heap := updateField($heap, obj, ClassName.fieldName, BoxT(v))` (T = field's declared type) |

### Procedure Entry Point

```
Γ, params ⊢_p body ⇐ returnType & e
─────────────────────────────────────
procedure f(params) → returnType & e
```

The procedure's grade `e` is discovered by trying grades [1, err, heap, heap·err]
on the body. The smallest grade at which `checkProducer` succeeds IS the grade.
`fullElaborate` does this for each procedure and rewrites its signature accordingly.

### Formal Rules → Implementation Mapping

| Formal | Implementation |
|---|---|
| `Γ ⊢_v V ⇒ A` | `synthValue expr : ElabM (FGLValue × LowType)` |
| `Γ ⊢_v V ⇐ A` | `checkValue expr expected : ElabM FGLValue` |
| `Γ ⊢_p M ⇒ A & d` | `synthExpr expr : ElabM SynthResult` (defunctionalized) |
| `Γ ⊢_p M ⇐ A & e` | `checkProducer stmt rest grade : ElabM FGLProducer` |
| `M to x. N ⇐ A & e` | `checkProducer` threads rest; `checkArgsK` lifts effectful args |
| `subsume(A, B)` | `subsume actual expected : CoercionResult` |
| `subgrade(d, e)` | `subgrade d e : Option ConventionWitness` → dispatches smart constructor |
| `d \ e` | `Grade.residual d e : Option Grade` |
| grade(f) | `procGrades[f]` (HashMap lookup from reader — pre-computed) |

**fullElaborate** structure:
1. `discoverGrades` — coinduction (calls typing rules, updates grades)
2. `checkProducer` on each body — term production (reads final grades, never mutates)

### Grade Inference: Coinduction on the Call Graph

Procedure grades are inferred by coinduction on the call graph — the
standard technique for typing mutually recursive definitions in functional
languages (cf. Hindley-Milner, abstract interpretation).

**Algorithm:**
```
discoverGrades(program, Γ) → procGrades:
  1. Initialize: procGrades[f] := ⊥ (pure) for all f
  2. For each proc f with body M:
       Try checkProducer M returnType g for g ∈ [pure, proc, err, heap, heapErr]
       under the current procGrades assumption.
       Set procGrades[f] := smallest g that succeeds.
  3. If any grade changed, go to step 2.
  4. Stable (no changes). Return procGrades.
```

The typing rules are the ORACLE: `checkProducer M retTy g` succeeds at
grade `g` iff the body's operations are all at grade ≤ g. The residual
`d \ e` fails (Option returns none) when a statement's grade `d` exceeds
the ambient grade `e`, causing the trial to fail.

**Separation of concerns:**
- The TYPING RULES (`synthValue`, `checkValue`, `checkProducer`) are
  textbook — pure transcriptions of the formal rules above. They read
  `procGrades` from the environment. They NEVER mutate grades. No boolean
  flags, no mode switching.
- The COINDUCTION (`discoverGrades`) is the only code that
  computes and updates grades. It calls the typing rules repeatedly
  with different grade assumptions until convergence.
- `fullElaborate` calls `discoverGrades` FIRST (all grades determined),
  then calls `checkProducer` on each body with the FINAL grades to
  produce GFGL terms.

**Coinduction:** Self-recursive and mutually recursive procedures work
because `procGrades` is initialized with an assumption (⊥). The typing
rules read this assumption during the trial. If the assumption was too
low, the trial fails, the grade is bumped, and the next round
succeeds. Convergence is guaranteed because the grade lattice is finite
(5 elements) and grades only increase.

**No on-demand discovery during elaboration.** By the time `checkProducer`
runs to produce GFGL terms (Pass 2), ALL grades are already known and
stable in the reader. `discoverGrade` is a simple HashMap lookup. No
body evaluation. No cascading. No boolean flags.

### Procedure Signature Rewriting

After a proc's grade is discovered:
- Grade `heap`/`heapErr` → add `$heap_in` input + `$heap` output
- Body prepended with `$heap := $heap_in`
- Callers already pass heap (smart constructors did this during elaboration)

### Resolution Does NOT Determine Effects

Resolution provides parameter types, return types, defaults, kwargs.
The elaborator discovers grades by coinduction on the call graph over
the call graph. There is no `EffectType` annotation from Resolution.
The grade IS the type — discovered by the same typing rules that check
everything else.

### User/Runtime Separation

**Principle:** The elaborator must know the types of ALL callees (to
insert coercions at call boundaries), but must only elaborate USER
procedure bodies (runtime is trusted).

This is representational, not boolean:

```
ElabEnv:
  typeEnv : TypeEnv           -- ALL signatures (user + runtime + prelude)
  program : Laurel.Program    -- ONLY user procedures (bodies elaborated)
  runtime : Laurel.Program    -- ONLY runtime procedures (never elaborated)
  procGrades : HashMap        -- grades for ALL callees
```

**TypeEnv** contains signatures for user-defined functions, prelude
primitives (PAdd, PGt, ...), AND runtime library procedures. Elaboration
uses these to type-check arguments at call boundaries. Without runtime
sigs, `checkArgsK` cannot insert coercions (e.g., int→Any for PAdd).

**Program** contains only user-defined procedure bodies. The coinduction
and Pass 2 elaboration walk ONLY `program.staticProcedures`.
Runtime procedure bodies are never inspected.

**Runtime grades** are derived structurally from procedure signatures via
`gradeFromSignature`:

```lean
def gradeFromSignature (proc : Laurel.Procedure) : Grade :=
  let hasError := proc.outputs.any fun o => eraseType o.type.val == .TCore "Error"
  let hasHeap := proc.inputs.any fun i => eraseType i.type.val == .TCore "Heap"
  match hasHeap, hasError with
  | true, true => .heapErr
  | true, false => .heap
  | false, true => .err
  | false, false => if proc.isFunctional then .pure else .proc
```

`isFunctional` distinguishes Laurel `function` (pure, can appear in
expressions) from `procedure` (must be at statement level). A runtime
procedure with no Error/Heap gets grade `proc` — ensuring it's ANF-lifted
to statement level rather than nested in expressions.

They enter `procGrades` as initial values before coinduction begins.
Uses `eraseType` (not string matching on type names) so it handles both
`TCore "Error"` and `UserDefined "Error"` from the Laurel parser uniformly.

This makes confusion impossible: you cannot accidentally elaborate a runtime
body (it's in `runtime`, not `program`). You cannot miss a coercion at a
runtime call boundary (the sig is in `typeEnv`).

### Holes

- Nondeterministic (`.Hole false`): `varDecl x T none body`
- Deterministic (`.Hole true`): `varDecl x T (some (staticCall "$hole_N" [])) body`

After elaboration, no Hole nodes remain.

### Core Interface Requirements

The Laurel→Core translator (`translateMinimal`) imposes constraints on the
elaborated output:

1. **`function` vs `procedure`:** Core distinguishes them. `function` declarations
   can appear in expressions (`.op`). `procedure` declarations MUST be at statement
   level (`.call`). The elaborator must NOT nest procedure calls inside expressions.
   This is enforced by the grade system: `synthValue` only accepts grade `pure`
   callees (functions). Grade > pure forces the call through the producer path
   which emits it at statement level.

2. **Datatype constructors** (from_int, ListAny_cons, etc.) are expressions — they're
   resolved by Core from the datatype definition. They do NOT need procedure entries.
   The elaborator treats them as pure functions (they have FuncSigs in the prelude).

3. **Output arity:** A `.call` statement's LHS targets must match the callee's
   declared output count exactly. `mkGradedCall` uses the proc's declared
   outputs for ALL grades. The grade only determines whether to prepend heap.
   The elaborator's signature rewriting must match what callers emit.

4. **`__main__` metadata:** `__main__` MUST have `sourceRangeToMd` metadata so Core
   classifies it as a user proc and generates VCs from its assertions. Without
   metadata, Core skips it → vacuous passes (unsound).

5. **Elaboration failure:** If elaboration fails on a proc body (returns `none`),
   the proc passes through unelaborated. If it has metadata, Core strict-checks it
   and may crash. Therefore: elaboration MUST NOT fail on any proc. If a construct
   is unhandled, emit a havoc (nondeterministic hole) rather than failing.

### GFGL Term Structure

```lean
inductive FGLProducer where
  | ifThenElse (md) (cond) (thn) (els) (after : FGLProducer)
  | labeledBlock (md) (label) (body) (after : FGLProducer)
  ...
```

Both `ifThenElse` and `labeledBlock` have an `after` field. This is the
continuation elaborated ONCE — preventing exponential duplication.

For `ifThenElse`: both branches elaborate standalone (rest = []).
`after` = elabRest(rest). Projection: `[if cond then {thn} else {els}] ++ after`.

For `labeledBlock`: the block body may contain `exit label` which jumps
to end of block. `after` continues after the block ends. Projection:
`[{label: body}] ++ after`.

---

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
