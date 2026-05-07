# Python → Laurel Translation Architecture (v2)

**Single source of truth for the refactored translation pipeline.**

---

## The Pipeline

```
Python AST + library stubs
  ↓ [Resolution: build Γ]
Γ : TypeEnv
  +
Python AST (user code)
  ↓ [Translation: fold over AST, type-directed via Γ]
e : Laurel.Program (impure CBV — precisely-typed, effects implicit)
  ↓ [Elaboration: impure CBV → Graded FGCBV]
e' : GFGL.Program (graded fine-grain Laurel — effects explicit via grades)
  ↓ [Projection: forget grading, trivial cata]
Laurel.Program (ready for Core)
  ↓ [Core translation]
Core
```

---

## Resolution (Building Γ)

**Input:** Python AST + stubs  
**Output:** TypeEnv (= Γ)

Resolution answers: "what is this name?" For each name, it records:
- Class, function, or variable
- Parameter names + types, defaults, return type
- Class fields

Resolution does NOT determine effects. Effects are inferred by elaboration.

```lean
structure FuncSig where
  name : String
  params : List (String × HighType)
  defaults : List (Option StmtExprMd)
  returnType : HighType
  hasKwargs : Bool

inductive NameInfo where
  | class_ (name : String) (fields : List (String × HighType))
  | function (sig : FuncSig)
  | variable (ty : HighType)
```

---

## Translation (Python AST → Laurel)

A fold over the Python AST. Each constructor maps to one Laurel construction.
Translation handles Python-specific desugarings (scope hoisting, object construction,
context managers, for-loop abstraction, calling convention normalization).

Translation does NOT insert coercions or determine effects.

---

## Elaboration (Impure CBV → Graded FGCBV)

### Overview

Elaboration is an action on derivations. Given a derivation `D : Γ ⊢_Laurel e : A`,
it produces `D' : Γ ⊢_GFGL e' : A & e` where `e` is the effect grade.

The target (GFGL) is a graded fine-grain call-by-value calculus in the sense of
McDermott (2025, "Grading call-by-push-value, explicitly and implicitly"). Grades
form an ordered monoid tracking effects. The grading is implicit: grades are a
PROPERTY of terms computed by the elaborator, not syntactic annotations.

### The Grade Monoid (Residuated)

```
(E, ≤, 1, ·, \) where E = {1, err, heap, heap·err}

Order:
  1 ≤ err ≤ heap·err
  1 ≤ heap ≤ heap·err

Multiplication:
  1 · e = e · 1 = e
  err · heap = heap · err = heap·err
  e · e = e  (idempotent)

Left residual (d \ e = largest e' such that d · e' ≤ e):
  1 \ e = e
  err \ err = 1
  err \ heap·err = heap
  heap \ heap = 1
  heap \ heap·err = err
  heap·err \ heap·err = 1
  d \ e = undefined when d ≰ e  (ill-typed: can't sequence a heap op in a pure context)
```

The residual makes the sequencing rule mode-correct: given input grade `e` and
synthesized prefix grade `d`, the continuation checks against `d \ e`.

### Types

**Value types:**
```
A, B ::= TInt | TBool | TString | TFloat64 | TVoid | TCore name | Composite
```

**Graded computation types:** A computation that returns type `A` with grade `e`:
```
A & e
```

### Judgments

```
Γ ⊢_v V ⇒ A                 (value synthesis)
Γ ⊢_v V ⇐ A                 (value checking)
Γ ⊢_p M ⇒ A & e             (producer synthesis — type AND grade both output)
Γ ⊢_p M ⇐ A & e             (producer checking — type AND grade both input)
```

Grade mode agrees with type mode.

### Value Rules (ungraded — values have no effects)

```
───────────────────────────
Γ ⊢_v n ⇒ int

(x : A) ∈ Γ
───────────────────────────
Γ ⊢_v x ⇒ A

f : (A₁,...,Aₙ) → B & 1        vᵢ ⇐ Aᵢ
──────────────────────────────────────────
Γ ⊢_v f(v₁,...,vₙ) ⇒ B                     (grade-1 call is a value)

Γ ⊢_v V ⇒ A    subsume(A, B) = c
──────────────────────────────────
Γ ⊢_v c(V) ⇐ B                             (subsumption — type coercion)
```

### Producer Rules

**Synthesis (type and grade both output):**

```
f : (A₁,...,Aₙ) → B & d    d > 1    vᵢ ⇐ Aᵢ
───────────────────────────────────────────────
Γ ⊢_p f(v₁,...,vₙ) ⇒ B & d                    (effectful call)

───────────────────────────
Γ ⊢_p (new C) ⇒ Composite & heap              (allocation)

Γ ⊢_v V ⇐ Γ(x)
───────────────────────────
Γ ⊢_p (x := V) ⇒ TVoid & 1                   (assignment to variable)

Γ ⊢_v V ⇐ bool
───────────────────────────
Γ ⊢_p (assert V) ⇒ TVoid & 1

Γ ⊢_v V ⇐ bool
───────────────────────────
Γ ⊢_p (assume V) ⇒ TVoid & 1

Γ ⊢_v V ⇐ bool    Γ ⊢_p M ⇐ TVoid & e
─────────────────────────────────────────
Γ ⊢_p (while V do M) ⇒ TVoid & e
```

**Checking (type and grade both input):**

```
Γ ⊢_v V ⇐ bool    Γ ⊢_p M ⇐ A & e    Γ ⊢_p N ⇐ A & e
──────────────────────────────────────────────────────────
Γ ⊢_p (if V then M else N) ⇐ A & e

Γ ⊢_v V ⇐ T    Γ, x:T ⊢_p body ⇐ A & e
──────────────────────────────────────────
Γ ⊢_p (var x:T := V; body) ⇐ A & e

Γ ⊢_p M ⇒ B & d    Γ, x:B ⊢_p N ⇐ A & (d \ e)
──────────────────────────────────────────────────
Γ ⊢_p (M to x. N) ⇐ A & e

Γ ⊢_v V ⇐ returnType
───────────────────────────
Γ ⊢_p (return V) ⇐ returnType & 1
```

**Subsumption (synth meets check — type coercion + subgrading):**

```
Γ ⊢_p M ⇒ A & d    A <: B    d ≤ e
─────────────────────────────────────
Γ ⊢_p M ⇐ B & e
```

Type coercion (`A <: B`) produces a value-level witness (`from_int`, etc.).
Subgrading (`d ≤ e`) is admissible — no syntax produced, the term is unchanged.
A less-effectful computation is always valid in a more-effectful context.

### Procedure Entry Point

```
Γ, x₁:A₁, ..., xₙ:Aₙ ⊢_p body ⇐ returnType & e
───────────────────────────────────────────────────
procedure f(x₁:A₁,...,xₙ:Aₙ) → returnType & e
```

The procedure body is CHECKED against `returnType & e`. But where does `e` come
from? It comes from the BODY ITSELF — elaboration first synthesizes the body's
grade, then uses subsumption to check it against the declared grade.

In practice: elaborate the body in SYNTH mode to discover its grade `d`. The
procedure's grade IS `d`. Callers read `d` from the effect map. If a caller
checks against a higher grade `e ≥ d`, subsumption handles it (admissible).

### Dependency Order

Callees must be elaborated before callers so that the callee's grade is available
at the call site. Procedures are processed in topological order of the call graph.

### The Calling Convention (Subgrading Coercion Made Manifest)

Although subgrading is admissible (no coercion syntax), it has an OBSERVABLE
EFFECT on the elaborated output: the STRUCTURE of the `effectfulCall` node.

The callee's grade determines what gets bound at the call site:

| Grade | Args | Outputs bound |
|-------|------|---------------|
| `1` | `[args]` | none (value call) |
| `err` | `[args]` | `[result, error]` |
| `heap` | `[heap, args]` | `[heap', result]` |
| `heap·err` | `[heap, args]` | `[heap', result, error]` |

This IS the proof-relevance of subgrading: the grade determines the shape of
the binding form. `mkEffectfulCall` takes the callee's grade and produces the
correctly-shaped `effectfulCall` node.

### Heap Threading

The heap variable flows through the HOAS closures:

```
mkEffectfulCall f [heap, args...]
  [("heap", THeap), ("result", resultTy)]
  fun [heap', rv] =>
    -- continuation has heap' in scope for the next operation
    mkEffectfulCall g [heap', args2...]
      [("heap", THeap), ("result", resultTy2)]
      fun [heap'', rv2] => ...
```

Each stateful call produces a NEW heap binding. The continuation receives it.
The next call uses it. No mutable state — pure CPS threading via HOAS.

### What Elaboration Does NOT Do

- No Python-specific logic (language-independent)
- No administrative let-bindings (grade-1 calls stay nested)
- No mutable state for heap tracking (HOAS closures thread it)
- No EffectType from Resolution (grades inferred from the walk)

---

## Projection (GFGL → Laurel)

Trivial catamorphism. Forget grades, map each GFGL constructor to Laurel.
The `effectfulCall` node projects to multi-output assignment (outputs determined
by the grade, which determined the output list during elaboration).

---

## References

- **Levy, P.B.** (2003). *Call-By-Push-Value.* — Value/Producer separation.
- **Egger, Møgelberg, Staton** (2014). "Linear Usage of State." — State-passing translation.
- **McDermott, D.** (2025). "Grading call-by-push-value, explicitly and implicitly." — Graded CBPV, implicit grading, coherence.
- **Dunfield & Krishnaswami** (2021). "Bidirectional Typing." — Synth/check discipline.
- **Moggi** (1991). "Notions of computation and monads." — Monadic effects.
- **Plotkin & Pretnar** (2009). "Handlers of Algebraic Effects." — Effect operations.
