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
  ↓ [Elaboration: impure CBV → Graded FGCBV, on-demand grade discovery]
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

f : (A₁,...,Aₙ) → B    grade(f) = 1    vᵢ ⇐ Aᵢ
──────────────────────────────────────────────────
Γ ⊢_v f(v₁,...,vₙ) ⇒ B

Γ ⊢_v V ⇒ A    subsume(A, B) = c
──────────────────────────────────
Γ ⊢_v c(V) ⇐ B
```

### Producer Synthesis

```
f : (A₁,...,Aₙ) → B    grade(f) = d (on-demand discovery)    d > 1    vᵢ ⇐ Aᵢ
────────────────────────────────────────────────────────────────────────────────
Γ ⊢_p f(v₁,...,vₙ) ⇒ B & d

───────────────────────────
Γ ⊢_p (new C) ⇒ Composite & heap

Γ ⊢_v V ⇐ Γ(x)
───────────────────────────
Γ ⊢_p (x := V) ⇒ TVoid & 1

Γ ⊢_v V ⇐ bool
───────────────────────────
Γ ⊢_p (assert V) ⇒ TVoid & 1

Γ ⊢_v V ⇐ bool    Γ ⊢_p M ⇐ TVoid & e    (e discovered by trying grades on M)
─────────────────────────────────────────────────────────────────────────────
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

Mode check for `M to x. N ⇐ A & e`:
- `A & e`: input (from check context)
- Synth M → get `B & d` (now `d` is known)
- Compute `d \ e` (residual — both `d` and `e` known, computable)
- Check N against `A & (d \ e)` (all inputs determined)

The residuated monoid makes this mode-correct: given the whole grade `e` and
the prefix grade `d`, the continuation grade `d \ e` is uniquely determined.

### Subsumption (synth meets check)

```
Γ ⊢_p M ⇒ A & d    subsume(A, B) = c    subgrade(d, e) = conv
────────────────────────────────────────────────────────────────
Γ ⊢_p conv(M, fun rv => return c(rv)) ⇐ B & e
```

The output term applies BOTH witnesses:
- `conv` wraps M in the correct binding form (effectfulCall with appropriate outputs)
- `c` coerces the bound result value inside the continuation
- `rv` is HOAS-bound (fresh name + extendEnv)

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
| Any | Box | `Box..Any` | Generated |

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
| Box | Any | `Box..AnyVal!` | DDM-generated (infallible) |

Both produce VALUES. Narrowing is partial (precondition-guarded).
No grade contribution — these are value-level operations.

### Composite and Any

`Any` is a tagged union. `Composite` is a heap reference (`MkComposite(ref: int)`).
`Composite <: Any` via `from_Composite` (pointer-preserving injection).
`Any ▷ Composite` via `Any..as_Composite!`.

Field access on Composite: `readField(heap, obj, field) → Box`, then `Box..AnyVal! → Any`,
then narrow `Any ▷ T`.

### Subgrading Witness (Defunctionalized Calling Convention)

`subgrade(d, e)` returns a `ConventionWitness` when `d ≤ e`. The witness is
proof-relevant: it determines the FGL term produced at the call site.

```lean
inductive ConventionWitness where
  | pureCall                -- grade 1: value-level, no binding
  | errorCall               -- grade err: bind [result, error]
  | heapCall                -- grade heap: pass heap, bind [heap', result]
  | heapErrorCall           -- grade heap·err: pass heap, bind [heap', result, error]

def subgrade : Grade → Grade → Option ConventionWitness
  | .pure,    _        => some .pureCall
  | .err,     .err     => some .errorCall
  | .err,     .heapErr => some .errorCall
  | .heap,    .heap    => some .heapCall
  | .heap,    .heapErr => some .heapCall
  | .heapErr, .heapErr => some .heapErrorCall
  | _,        _        => none
```

Application via smart constructors (read heapVar from state internally):

```lean
-- Smart constructors dispatch on the convention witness.
-- They read heapVar from ElabState, prepend heap if needed,
-- generate fresh output names (HOAS), extend Γ, call body closure.

def mkErrorCall (callee args resultTy) (body : FGLValue → ElabM FGLProducer)
def mkHeapCall (callee args resultTy) (body : FGLValue → ElabM FGLProducer)
def mkHeapErrorCall (callee args resultTy) (body : FGLValue → ElabM FGLProducer)
```

### CPS Elaboration

The elaborator is CPS: `synthProducer` takes a continuation and nests the
operation AROUND it. Every FGLProducer constructor has a `body` field — that
IS the continuation. There is no `.seq`.

```lean
partial def synthProducer (expr : StmtExprMd) (cont : ElabM FGLProducer) : ElabM FGLProducer
```

The smart constructors (§Subgrading Witness) plug the continuation into the
binding form. They handle all HOAS internally (fresh names, extendEnv, heapVar).

### Producer Subsumption (see §Subsumption above for the full rule)

The `conv` witness selects the smart constructor:
- `pureCall` → no binding
- `errorCall` → `mkErrorCall`
- `heapCall` → `mkHeapCall`
- `heapErrorCall` → `mkHeapErrorCall`

The `c` witness coerces `rv` inside the continuation (after binding).

### Heap Operations

| Source | Grade | Elaborated |
|---|---|---|
| `.New classId` | `heap` | `increment($heap)` → `MkComposite(ref, TypeTag)` |
| `.FieldSelect obj field` | `heap` | `Box..AnyVal!(readField($heap, obj, field))` |
| `Assign [FieldSelect obj f] v` | `heap` | `$heap := updateField($heap, obj, f, Box..Any(v))` |

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
| `Γ ⊢_p M ⇒ A & d` | `synthProducer expr cont : ElabM FGLProducer` (CPS — cont is rest of block) |
| `Γ ⊢_p M ⇐ A & e` | `checkProducer expr expected : ElabM FGLProducer` |
| `M to x. N ⇐ A & e` | `elaborateBlock [M, ...rest] cont` (M synth'd, rest is continuation) |
| `subsume(A, B)` | `subsume actual expected : CoercionResult` |
| `subgrade(d, e)` | `subgrade d e : Option ConventionWitness` → dispatches smart constructor |
| `d \ e` | `Grade.residual d e : Option Grade` |

The CPS transform: formal rules show `M to x. N` as a single check rule.
Implementation realizes this as `synthProducer M (elaborateBlock rest)` — the
continuation IS the rest of the block, passed as argument.

### On-Demand Callee Grade Discovery

When elaboration encounters `StaticCall f args`:
1. Look up f's grade in ElabState (same place as its type info)
2. If not yet known: find f's body, try `checkProducer body returnType g`
   for g ∈ [pure, err, heap, heapErr]. First success → f's grade. Store it.
3. Dispatch smart constructor based on discovered grade.

The grade is part of the procedure's TYPE — stored alongside its param types
and return type in the elaborator's state. Not a separate cache. When a callee
is elaborated on-demand, its grade joins the same structure as its other type
information. This is the same mechanism: type-checking discovers types AND
grades simultaneously.

### Procedure Signature Rewriting

After a proc's grade is discovered:
- Grade `heap`/`heapErr` → add `$heap_in` input + `$heap` output
- Body prepended with `$heap := $heap_in`
- Callers already pass heap (smart constructors did this during elaboration)

### Resolution Does NOT Determine Effects

Resolution provides parameter types, return types, defaults, kwargs.
The elaborator discovers grades on-demand by elaborating callee bodies.
There is no `EffectType` annotation from Resolution. The grade IS the
type — discovered by the same mechanism that checks everything else.

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

## Translation Desugarings

| Python | Laurel |
|---|---|
| `x = expr` | `Assign [x] expr` |
| `a, b = rhs` | `tmp := rhs; a := Get(tmp,0); b := Get(tmp,1)` |
| `x += v` | `Assign [x] (PAdd x v)` |
| `return e` | `LaurelResult := e; exit $body` |
| `Foo(args)` (class) | `tmp := New Foo; Foo@__init__(tmp, args); tmp` |
| `with mgr as v: body` | `v := Type@__enter__(mgr); body; Type@__exit__(mgr)` |
| `for x in iter: body` | `x := Hole; Assume(PIn(x, iter)); body` (labeled blocks for break/continue) |
| `[a, b, c]` | `from_ListAny(ListAny_cons(a, ListAny_cons(b, ListAny_cons(c, ListAny_nil()))))` |
| `{k: v}` | `from_DictStrAny(DictStrAny_cons(k, v, DictStrAny_empty()))` |
| `f"{expr}"` | `to_string_any(expr)` |
| `str(x)` | `to_string_any(x)` (via builtinMap) |

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
