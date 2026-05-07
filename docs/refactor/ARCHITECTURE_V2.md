# Python → Laurel Translation Architecture (v2)

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
  ↓ [Elaboration: impure CBV → Graded FGCBV, dependency order]
e' : GFGL.Program (graded fine-grain Laurel — effects explicit via grades)
  ↓ [Projection: forget grading, trivial cata]
Laurel.Program (ready for Core)
  ↓ [Core translation]
Core
```

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

---

## Translation

A catamorphism over the Python AST. One case per constructor. Deterministic.

**Does:** scope hoisting, object construction (.New + __init__), context managers,
for-loop abstraction (havoc + assume), loop labels, calling convention (kwargs +
defaults via Γ), module-level wrapping (__main__), mutable param copies.

**Does NOT:** cast insertion, literal wrapping, effect determination.

---

## Elaboration

### Two Type Systems

**HighType** (Translation's output): has `UserDefined "Foo"`.  
**LowType** (GFGL's type system): has only `Composite`.

```lean
def eraseType : HighType → LowType
  | .UserDefined _ => .TCore "Composite"
  | .TInt => .TInt | .TBool => .TBool | .TString => .TString
  | .TFloat64 => .TFloat64 | .TVoid => .TVoid | .TCore n => .TCore n
```

### The Grade Monoid (Residuated Partially-Ordered)

```
(E, ≤, 1, ·, \) where E = {1, err, heap, heap·err}

Order:
  1 ≤ err ≤ heap·err
  1 ≤ heap ≤ heap·err

Multiplication:
  1 · e = e · 1 = e
  err · heap = heap · err = heap·err
  e · e = e

Left residual (d \ e):
  1 \ e = e
  err \ err = 1        err \ heap·err = heap
  heap \ heap = 1      heap \ heap·err = err
  heap·err \ heap·err = 1
```

### Judgments

```
Γ ⊢_v V ⇒ A                 value synthesis (no grade)
Γ ⊢_v V ⇐ A                 value checking (no grade)
Γ ⊢_p M ⇒ A & e             producer synthesis (type + grade output)
Γ ⊢_p M ⇐ A & e             producer checking (type + grade input)
```

Grade mode agrees with type mode.

### Value Rules

```
───────────────
Γ ⊢_v n ⇒ int

(x : A) ∈ Γ
───────────────
Γ ⊢_v x ⇒ A

f : (A₁,...,Aₙ) → B & 1    vᵢ ⇐ Aᵢ
──────────────────────────────────────
Γ ⊢_v f(v₁,...,vₙ) ⇒ B

Γ ⊢_v V ⇒ A    subsume(A, B) = c
──────────────────────────────────
Γ ⊢_v c(V) ⇐ B
```

### Producer Synthesis

```
f : (A₁,...,Aₙ) → B & d    d > 1    vᵢ ⇐ Aᵢ
───────────────────────────────────────────────
Γ ⊢_p f(v₁,...,vₙ) ⇒ B & d

───────────────────────────
Γ ⊢_p (new C) ⇒ Composite & heap

Γ ⊢_v V ⇐ Γ(x)
───────────────────────────
Γ ⊢_p (x := V) ⇒ TVoid & 1

Γ ⊢_v V ⇐ bool
───────────────────────────
Γ ⊢_p (assert V) ⇒ TVoid & 1

Γ ⊢_v V ⇐ bool    Γ ⊢_p M ⇐ TVoid & e
─────────────────────────────────────────
Γ ⊢_p (while V do M) ⇒ TVoid & e
```

### Producer Checking

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

Γ ⊢_v V ⇐ A
───────────────────────────
Γ ⊢_p (return V) ⇐ A & e
```

### Subsumption

```
Γ ⊢_p M ⇒ A & d    A <: B    d ≤ e
─────────────────────────────────────
Γ ⊢_p M ⇐ B & e
```

Type coercion (`A <: B`) produces a witness. Subgrading (`d ≤ e`) is admissible.

### Subsumption Table (Type Coercions)

```lean
def subsume (actual expected : LowType) : CoercionResult :=
  if actual == expected then .refl else match actual, expected with
  | .TInt, .TCore "Any"         => .coerce .fromInt
  | .TBool, .TCore "Any"        => .coerce .fromBool
  | .TString, .TCore "Any"      => .coerce .fromStr
  | .TFloat64, .TCore "Any"     => .coerce .fromFloat
  | .TCore "Composite", .TCore "Any" => .coerce .fromComposite
  | .TCore "ListAny", .TCore "Any"   => .coerce .fromListAny
  | .TCore "DictStrAny", .TCore "Any" => .coerce .fromDictStrAny
  | .TVoid, .TCore "Any"        => .coerce (fun _ => .fromNone)
  | .TCore "Any", .TBool        => .coerce (fun v => .staticCall "Any_to_bool" [v])
  | .TCore "Any", .TInt         => .coerce (fun v => .staticCall "Any..as_int!" [v])
  | .TCore "Any", .TString      => .coerce (fun v => .staticCall "Any..as_string!" [v])
  | .TCore "Any", .TFloat64     => .coerce (fun v => .staticCall "Any..as_float!" [v])
  | .TCore "Any", .TCore "Composite" => .coerce (fun v => .staticCall "Any..as_Composite!" [v])
  | .TCore "Box", .TCore "Any"  => .coerce (fun v => .staticCall "Box..AnyVal!" [v])
  | _, _ => .unrelated
```

### Calling Convention (Grade → Binding Shape)

| Callee grade | Args | Outputs bound |
|---|---|---|
| `1` | `[args]` | none (value) |
| `err` | `[args]` | `[result, error]` |
| `heap` | `[heap, args]` | `[heap', result]` |
| `heap·err` | `[heap, args]` | `[heap', result, error]` |

### Heap Operations

| Source | Grade | Elaborated |
|---|---|---|
| `.New classId` | `heap` | `increment($heap)` → `MkComposite(ref, TypeTag)` |
| `.FieldSelect obj field` | `heap` | `Box..AnyVal!(readField($heap, obj, field))` |
| `Assign [FieldSelect obj f] v` | `heap` | `$heap := updateField($heap, obj, f, Box..Any(v))` |

### Dependency Order

Procedures elaborated in topological order of call graph. Callee's grade known
before caller's elaboration. Effect map: `procName → Grade`.

### Procedure Entry

Body synth'd to discover grade. That grade becomes the procedure's effect signature.
Callers read it from the effect map.

### Holes

- Nondeterministic (`.Hole false`): `varDecl x T none body`
- Deterministic (`.Hole true`): `varDecl x T (some (staticCall "$hole_N" [])) body`

After elaboration, no Hole nodes remain.

---

## Projection

Trivial catamorphism. Forget grades. Map GFGL → Laurel:

- `effectfulCall f args outputs body` → `[decl outputs; Assign [outputs] (StaticCall f args); body]`
- `assign target val body` → `[Assign [target] val; body]`
- `varDecl x ty init body` → `[LocalVariable x ty init; body]`
- Values map to their Laurel equivalents directly.

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
