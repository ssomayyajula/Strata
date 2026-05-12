# Python → Laurel Translation Architecture


## Overview

This pipeline translates Python source code into Laurel (our verification IL)
via a series of compositional passes. The key insight is **separation of
concerns**: Resolution handles scoping, Translation handles Python's surface
syntax (desugaring to Laurel), and Elaboration handles the semantic heavy
lifting (effects, coercions, heap threading). Each pass has a clear input
type, output type, and contract.

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

### Type signatures

```lean
def resolve   : Array (Python.stmt SourceRange) → Array (Python.stmt ResolvedAnn)
def translate : Array (Python.stmt ResolvedAnn) → Laurel.Program
def elaborate : Laurel.Program → Laurel.Program
```

### Diagram

```
Array (Python.stmt SourceRange)    (raw, unscoped)
  ↓ [Resolution: scope resolution, fold with growing context]
Array (Python.stmt ResolvedAnn)    (scoped, every node annotated with its meaning)
  ↓ [Translation: catamorphism over resolved AST]
Laurel.Program                     (impure CBV, effects implicit)
  ↓ [Elaboration: graded bidirectional typing, total]
Laurel.Program                     (effects explicit via calling conventions)
  ↓ [Core translation (existing, unchanged)]
Core
```

### What each pass does

**Resolution** is a fold over the Python AST that threads a growing context
as accumulator. Each declaration extends the context; each reference is
annotated with its resolution from the current context. The output is the
same AST with `ResolvedAnn` on every node — the scoping derivation for
the Python program.

**Translation** is a catamorphism over the resolved AST. It reads the
annotation on each node and emits the corresponding Laurel construct.
No name resolution — that was done by Resolution. At call sites,
Translation uses the FuncSig from the annotation to match args to params
(positional + kwargs → param order). If a node is `.unresolved`,
Translation emits `Hole`.

**Elaboration** takes the Laurel program and transforms it: inserting
coercions (governed by the subtyping table), threading heap state
(governed by grades), and binding effectful subexpressions at statement
level (governed by the to-rule). It is total — every Laurel construct
produces output. Grade inference is by coinduction on the call graph.

### Intermediate types

```lean
abbrev Identifier := String
abbrev PythonType := Python.expr SourceRange

structure FuncSig where
  params : List (Identifier × PythonType)
  defaults : List (Identifier × Python.expr SourceRange)
  returnType : PythonType
  locals : List (Identifier × PythonType)

inductive NameInfo where
  | class_ (name : Identifier) (fields : List (Identifier × PythonType))
  | function (sig : FuncSig)
  | variable (ty : PythonType)
  | module_ (name : Identifier)
  | unresolved

structure ResolvedAnn where
  sr : SourceRange
  info : NameInfo
```


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
to a name that is not in Γ. Enforced by the resolved AST representation:
call sites carry `.function sig` in their annotation. Unresolvable calls
carry `.unresolved` and Translation emits Hole. There is no constructor
that represents "StaticCall to an unresolved name."

This eliminates an entire class of bugs:
- Undefined function calls (→ Core "not found" errors)
- Arity mismatches (sig in annotation determines param count)
- Type-level module resolution failures silently producing garbage names

**Types are Python annotation expressions:** Types flow through Resolution
as `PythonType := Python.expr SourceRange` — the actual annotation from the
source. Translation maps them to `HighType` when emitting Laurel. No string
intermediate (`extractTypeStr` is abolished).

**No boolean blindness in Resolution:** `NameInfo` is an inductive —
pattern matching on it gives you the data you need. There is no
`isResolved : String → Bool` followed by a separate lookup. The annotation
IS the resolution.



## Resolution

```lean
def resolve : Array (Python.stmt SourceRange) → Array (Python.stmt ResolvedAnn)
```

**Input:** Raw Python AST (`Python.stmt SourceRange`).  
**Output:** Resolved Python AST (`Python.stmt ResolvedAnn`).

Resolution is a fold over the Python AST that threads a growing context
as accumulator. At the top level (module scope), each declaration extends
the context:

- `def f(...)` → extends context with `f : .function sig`
- `class C` → extends context with `C : .class_`, methods as `.function`
- `import M` → extends context with `M : .module_`
- `x : T = ...` → extends context with `x : .variable T`
- Python builtins (from stubs) → extend context with `.function sig`

At each reference (name use, call site, attribute access), the node is
annotated with the resolution from the current context. Unresolvable
references are annotated `.unresolved`.

Within a function body, the context is extended with:
- Parameters (from the function signature)
- Locals (Python's scoping rule: any assignment target anywhere in
  the body is function-local)

The output AST is the scoping derivation: every node carries proof of
what it refers to. Translation reads this directly — no lookups needed.

**Resolution does NOT:**
- Determine effects (Elaboration does that)
- Translate types to Laurel (Translation does that)

**Contract with Translation:** The resolved AST IS the interface. Every
call site carries `.function sig` or is `.unresolved` (→ Hole). Translation
cannot emit `StaticCall` for an unresolved name because unresolved nodes
don't carry a FuncSig — there's nothing to emit from.




## Translation

```lean
def translate : Array (Python.stmt ResolvedAnn) → Laurel.Program
```

A catamorphism over the resolved Python AST. One case per constructor.
Deterministic. No lookups — reads resolution from node annotations.

**Does:** desugar Python surface syntax into Laurel: object construction
(.New + __init__), context managers, for-loop abstraction (havoc + assume),
loop labels, module-level wrapping (__main__), mutable param copies,
error output declaration (`maybe_except: Error` in proc outputs), map
`PythonType` annotations to `HighType`.

**Does NOT:** scope resolution (Resolution did that), cast insertion,
literal wrapping, effect determination.

### Desugarings

| Python | Laurel |
|---|---|
| `x = expr` | `Assign [x] expr` |
| `a, b = rhs` | `tmp := rhs; a := Get(tmp,0); b := Get(tmp,1)` |
| `x += v` | `Assign [x] (PAdd x v)` |
| `x[i] = v` | `Assign [x] (Any_sets(ListAny_cons(i, ListAny_nil()), x, v))` |
| `x[start:stop]` | `Any_get(x, from_Slice(Any..as_int!(start), OptSome(Any..as_int!(stop))))` |
| `return e` | `LaurelResult := e; exit $body` |
| `Foo(args)` (class) | `Assign [tmp] (New Foo); Foo@__init__(tmp, args)` |
| `with mgr as v: body` | `v := Type@__enter__(mgr); body; Type@__exit__(mgr)` |
| `for x in iter: body` | `x := Hole; Assume(PIn(x, iter)); body` (labeled blocks for break/continue) |
| `[a, b, c]` | `from_ListAny(ListAny_cons(a, ListAny_cons(b, ListAny_cons(c, ListAny_nil()))))` |
| `{k: v}` | `from_DictStrAny(DictStrAny_cons(k, v, DictStrAny_empty()))` |
| `f"{expr}"` | `to_string_any(expr)` |



## Elaboration

Elaboration transforms Laurel typing derivations into GFGL typing derivations.

### Laurel Type System (Source)

Laurel is an impure CBV language. One judgment form. The context Γ carries
variable bindings `(x : A)` and label names `(l)` (untyped scope markers).

```
Γ ⊢_L e : A
```

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


Γ,l ⊢_L body : A    Γ ⊢_L rest : A
────────────────────────────────────────
Γ ⊢_L {body}ₗ; rest : A


l ∈ Γ
─────────────────────
Γ ⊢_L (exit l) : A


Γ ⊢_L e : A
─────────────────────
Γ ⊢_L (return e) : A


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

### The Grade Monoid

```
(E, ≤, 1, ·, \) where E = {pure, proc, err, heap, heapErr}

Order:
  pure ≤ proc ≤ err ≤ heapErr
  pure ≤ proc ≤ heap ≤ heapErr

Left residual (d \ e):
  pure \ e = e
  proc \ proc = pure    proc \ err = err    proc \ heap = heap    proc \ heapErr = heapErr
  err \ err = pure      err \ heapErr = heap
  heap \ heap = pure    heap \ heapErr = err
  heapErr \ heapErr = pure
```

### Elaboration's type translation (⟦·⟧ : HighType → LowType)

```lean
def ⟦·⟧ : HighType → LowType
  | .TInt => .TInt | .TBool => .TBool | .TString => .TString
  | .TFloat64 => .TFloat64 | .TVoid => .TVoid | .TCore n => .TCore n
  | .UserDefined id => match id.text with
    | "Any" => .TCore "Any" | "Error" => .TCore "Error"
    | "ListAny" => .TCore "ListAny" | "DictStrAny" => .TCore "DictStrAny"
    | _ => .TCore "Composite"
  | .THeap => .TCore "Heap"
  | _ => .TCore "Any"
```

(Implementation name: `eraseType`)

### GFGL Type System (Target — Bidirectional, Graded)

GFGL has two sorts: **values** (pure) and **producers** (effectful, graded).
Typing is bidirectional. The context Γ carries variable bindings `(x : A)`
and label names `(l)` (untyped scope markers, same as Laurel).

```
Γ ⊢_v V ⇒ A           value synthesis
Γ ⊢_v V ⇐ A           value checking
Γ ⊢_p M ⇒ A & d       producer synthesis
Γ ⊢_p M ⇐ A & e       producer checking
```

#### Value rules

```
─────────────────────────
Γ ⊢_v litInt n ⇒ TInt

(x : A) ∈ Γ
─────────────────────────
Γ ⊢_v var x ⇒ A

f : (A₁,...,Aₙ) → B ∈ Γ    Γ ⊢_v V₁ ⇐ A₁  ...  Γ ⊢_v Vₙ ⇐ Aₙ
───────────────────────────────────────────────────────────────────
Γ ⊢_v staticCall f [V₁,...,Vₙ] ⇒ B

Γ ⊢_v V ⇒ A    A ≤ B ↦ c
─────────────────────────────────
Γ ⊢_v c(V) ⇐ B
```

#### Producer synthesis

There is exactly one producer synthesis rule. By inversion, any synthesis
derivation gives you the callee, checked args, return type, and grade.

```
f : (A₁,...,Aₙ) → B & d ∈ Γ    Γ ⊢_v V₁ ⇐ A₁  ...  Γ ⊢_v Vₙ ⇐ Aₙ
──────────────────────────────────────────────────────────────────────────
Γ ⊢_p f(V₁,...,Vₙ) ⇒ B & d
```

#### Producer subsumption (mode switch ⇒ₚ to ⇐ₚ)

By inversion on the single synthesis rule, M = f(V₁,...,Vₙ) with known f,
args, return type B, and grade d. Producer subsumption binds the call's
outputs via effectfulCall and checks the continuation at the residual grade.
Let [x₁:T₁,...,xₖ:Tₖ] = outputs(f) and r = resultIdx(d):

```
Γ ⊢_p f(V₁,...,Vₙ) ⇒ B & d    B ≤ A ↦ c
Γ,x₁:T₁,...,xₖ:Tₖ ⊢_p K ⇐ A & (d\e)
────────────────────────────────────────────────────────────────────────────
Γ ⊢_p effectfulCall f [V₁,...,Vₙ] [x₁:T₁,...,xₖ:Tₖ] (c(xᵣ); K) ⇐ A & e
```

`xᵣ` is the result output (position r among the declared outputs).
c coerces it to the target type. K is checked at residual d\e.

#### Producer checking rules

```
─────────────────────────
Γ ⊢_p unit ⇐ A & e

l ∈ Γ
─────────────────────────
Γ ⊢_p exit l ⇐ A & e

Γ ⊢_v V ⇐ A
──────────────────────────────
Γ ⊢_p returnValue V ⇐ A & e

Γ ⊢_v V ⇐ Γ(x)    Γ ⊢_p K ⇐ A & e
──────────────────────────────────────
Γ ⊢_p assign x V K ⇐ A & e

Γ ⊢_v V ⇐ T    Γ,x:T ⊢_p K ⇐ A & e
──────────────────────────────────────
Γ ⊢_p varDecl x T V K ⇐ A & e

Γ ⊢_v V ⇐ bool    Γ ⊢_p M_t ⇐ A & e    Γ ⊢_p M_f ⇐ A & e    Γ ⊢_p K ⇐ A & e
─────────────────────────────────────────────────────────────────────────────────────
Γ ⊢_p ifThenElse V M_t M_f K ⇐ A & e

Γ ⊢_v V ⇐ bool    Γ ⊢_p M_b ⇐ A & e    Γ ⊢_p K ⇐ A & e
─────────────────────────────────────────────────────────────
Γ ⊢_p whileLoop V M_b K ⇐ A & e

Γ ⊢_v V ⇐ bool    Γ ⊢_p K ⇐ A & e
─────────────────────────────────────
Γ ⊢_p assert V K ⇐ A & e

Γ ⊢_v V ⇐ bool    Γ ⊢_p K ⇐ A & e
─────────────────────────────────────
Γ ⊢_p assume V K ⇐ A & e

Γ,l ⊢_p M_b ⇐ A & e    Γ ⊢_p K ⇐ A & e
───────────────────────────────────────────
Γ ⊢_p labeledBlock l M_b K ⇐ A & e
```

`labeledBlock`/`exit` form an intro/elim pair for label scope.
`exit l` is non-returning (checks at any A & e). `unit` terminates
the current continuation (control flows to the enclosing after-block).

### The Translation ⟦·⟧

#### Translation on contexts

```
⟦Γ⟧ = { (x : ⟦A⟧) | (x:A) ∈ Γ } ∪ { l | l ∈ Γ }
```

Each translation clause extends ⟦Γ⟧ with new bindings at erased types:
effectfulCall adds fresh output variables at ⟦Tᵢ⟧, varDecl adds the
declared name at ⟦T⟧. These extensions are visible in the recursive
call on continuation K.

#### The four functions

The translation is four mutually recursive functions.

Synthesis takes Γ and a raw expression, discovers A', and produces a
GFGL derivation at ⟦A'⟧. Value checking takes A : HighType and a Laurel
derivation at A, and produces a GFGL value checked at ⟦A⟧. Producer
checking additionally takes a grade e.

```
⟦·⟧⇒ᵥ : (Γ : Ctx) → (e : StmtExpr) → ∃(A' : HighType)(V : FGLValue). (Γ ⊢_L e : A') → (⟦Γ⟧ ⊢_v V ⇒ ⟦A'⟧)
⟦·⟧⇐ᵥ : (A : HighType) → (Γ ⊢_L e : A) → ∃V. (⟦Γ⟧ ⊢_v V ⇐ ⟦A⟧)
⟦·⟧⇒ₚ : (Γ : Ctx) → (e : StmtExpr) → ∃(A' : HighType)(M : FGLProducer)(d : Grade). (Γ ⊢_L e : A') → (⟦Γ⟧ ⊢_p M ⇒ ⟦A'⟧ & d)
⟦·⟧⇐ₚ : (A : HighType) → (e : Grade) → (Γ ⊢_L S;rest : A) → ∃M. (⟦Γ⟧ ⊢_p M ⇐ ⟦A⟧ & e)
```

⟦·⟧⇒ₚ has exactly one clause (call with grade > pure); inversion is trivial.

#### Grade inference

**Input** to elaboration: a Laurel.Program (typed procedures with bodies).  
**Output** of elaboration: a GFGL.Program (same procedures, graded, effect-explicit bodies).

Elaboration proceeds in two passes over the program's procedure list.

**Pass 1 — grade inference (coinduction over the call graph):**

Input: the Laurel program. Output: `procGrades : String → Grade`.

Runtime procedure grades are read structurally from the signature:
```lean
def gradeFromSignature (proc : Laurel.Procedure) : Grade :=
  let hasError := proc.outputs.any fun o => eraseType o.type.val == .TCore "Error"
  let hasHeap := proc.inputs.any fun i => eraseType i.type.val == .TCore "Heap"
  match hasHeap, hasError with
  | true, true => .heapErr | true, false => .heap
  | false, true => .err    | false, false => if proc.isFunctional then .pure else .proc
```

User procedure grades are inferred by coinduction: for each user procedure f,
attempt `⟦body(f)⟧⇐ₚ` at grade pure, then proc, then err, then heap, then
heapErr. The first grade where elaboration succeeds is f's grade. When a
callee's grade exceeds the trial grade, `d\e` is undefined and elaboration
fails — this is what drives the iteration upward. The process converges
because the grade lattice is finite and the grades are monotone.

**Pass 2 — term production:**

Input: the Laurel program + procGrades. Output: the GFGL program.

For each procedure, elaborate its body via ⟦body⟧⇐ₚ at the inferred grade.
Pass 1 guarantees this succeeds (the grade was chosen to make it succeed).

#### Entry point (per-procedure)

For procedure `f(p₁:T₁,...,pₘ:Tₘ) → R` with grade e = procGrades[f]:

```
grade(f) ∈ {heap, heapErr}:
  inputs  := [$heap_in : Heap] ++ params(f)
  outputs := [$heap : Heap] ++ resultOutputs(f) ++ (if err ≤ grade(f) then [maybe_except : Error] else [])
  body prefix: $heap := $heap_in

grade(f) = err:
  outputs := resultOutputs(f) ++ [maybe_except : Error]

grade(f) ∈ {pure, proc}:
  (no rewriting)
```

Elaboration begins (Γ extended with both inputs and outputs):
```
⟦Γ,p₁:T₁,...,pₘ:Tₘ,LaurelResult:R,maybe_except:Error ⊢_L B : R⟧⇐ₚ at grade e
```

#### Subgrading

A subgrading judgment `d ≤ e` has a *witness*: the calling convention
transformation applied at that call site. The witness determines what
arguments are passed, what outputs are declared, and which output
position holds the result.

```
d            args prepended    outputs(f)                         resultIdx   d\e
───────────────────────────────────────────────────────────────────────────────────────
pure         (none)            (none — value-level staticCall)    —           e
proc         (none)            [result : ⟦B⟧]                    0           proc\e
err          (none)            [result : ⟦B⟧, maybe_except : Error]  0       err\e
heap         [$heap]           [$heap : Heap, result : ⟦B⟧]      1           heap\e
heapErr      [$heap]           [$heap : Heap, result : ⟦B⟧, maybe_except : Error]  1  heapErr\e
```

`d\e` is defined iff `d ≤ e`. If not, elaboration fails (drives grade
inference upward). `$heap` is the current heap variable (initialized from
`$heap_in` at proc entry, updated to a fresh name by each effectfulCall
whose outputs include a Heap position).

#### Subtyping

A subtyping judgment `A ≤ B` has a *witness*: a coercion function
`c : FGLValue → FGLValue`. When `A = B`, c = id. Otherwise:

```
A ≤ B                    c(v)
─────────────────────────────────────────────────
TInt ≤ Any               fromInt(v)
TBool ≤ Any              fromBool(v)
TString ≤ Any            fromStr(v)
TFloat64 ≤ Any           fromFloat(v)
Composite ≤ Any          fromComposite(v)
ListAny ≤ Any            fromListAny(v)
DictStrAny ≤ Any         fromDictStrAny(v)
TVoid ≤ Any              fromNone
Any ≤ TBool              Any_to_bool(v)
Any ≤ TInt               Any..as_int!(v)
Any ≤ TString            Any..as_string!(v)
Any ≤ TFloat64           Any..as_float!(v)
Any ≤ Composite          Any..as_Composite!(v)
```

Upward (T ≤ Any): value constructors (boxing).
Downward (Any ≤ T): pure function calls (unboxing/narrowing).
If neither A ≤ B nor A = B: undefined.

#### Auxiliary definitions

```
outputs(g)    = declared outputs of g after signature rewriting
resultIdx(d)  = 0 if d ∈ {proc, err}; 1 if d ∈ {heap, heapErr}
$field.C.f    = zero-arity Field datatype constructor (one per class field)
boxCtor(T)    = boxConstructorName(T)  (e.g. BoxInt, BoxComposite, BoxAny)
```

#### Argument sequencing

The call clauses below use `⟦Dᵢ⟧⇐ᵥ` on each argument. This is only
valid when every argument synthesizes as a value (grade = pure). When
argument eᵢ has procGrades[callee(eᵢ)] > pure, it must be sequenced:

```
⟦Dᵢ⟧⇒ₚ :: ⟦Γ⟧ ⊢_p gᵢ(W₁,...,Wₘ) ⇒ Bᵢ & dᵢ    dᵢ ≤ e
⟦Γ⟧,y₁:T₁,...,yⱼ:Tⱼ ⊢_p ... ⇐ A & (dᵢ\e)
──────────────────────────────────────────────────────────────────────────
⟦Γ⟧ ⊢_p effectfulCall gᵢ [W₁,...,Wₘ] [y₁:T₁,...,yⱼ:Tⱼ] (... uses yᵣ as Vᵢ ...) ⇐ A & e
```

The result variable yᵣ (at resultIdx(dᵢ)) is then used in place of Vᵢ
in the outer call. Multiple effectful arguments nest left-to-right.
This turns the outer call from a value-level staticCall into a producer.


#### Clauses of ⟦·⟧⇒ᵥ

```
D :: Γ ⊢_L n : int       ↦    ⟦D⟧⇒ᵥ :: ⟦Γ⟧ ⊢_v litInt n ⇒ TInt
D :: Γ ⊢_L b : bool      ↦    ⟦D⟧⇒ᵥ :: ⟦Γ⟧ ⊢_v litBool b ⇒ TBool
D :: Γ ⊢_L s : string    ↦    ⟦D⟧⇒ᵥ :: ⟦Γ⟧ ⊢_v litString s ⇒ TString

(x : A) ∈ Γ
─────────────────
D :: Γ ⊢_L x : A                     ↦    ⟦D⟧⇒ᵥ :: ⟦Γ⟧ ⊢_v var x ⇒ ⟦A⟧


D₁ :: Γ ⊢_L e₁ : A₁  ...  Dₙ :: Γ ⊢_L eₙ : Aₙ
──────────────────────────────────────────────────
D :: Γ ⊢_L f(e₁,...,eₙ) : B    where procGrades[f] = pure

        ↦

⟦D₁⟧⇐ᵥ :: ⟦Γ⟧ ⊢_v V₁ ⇐ ⟦A₁⟧  ...  ⟦Dₙ⟧⇐ᵥ :: ⟦Γ⟧ ⊢_v Vₙ ⇐ ⟦Aₙ⟧
────────────────────────────────────────────────────────────────────────
⟦D⟧⇒ᵥ :: ⟦Γ⟧ ⊢_v staticCall f [V₁,...,Vₙ] ⇒ ⟦B⟧


D_obj :: Γ ⊢_L obj : C    fields(C,f) = T    ($heap : Heap) ∈ ⟦Γ⟧
───────────────────────────────────────────────────────────────────
D :: Γ ⊢_L obj.f : T

        ↦

⟦D_obj⟧⇐ᵥ :: ⟦Γ⟧ ⊢_v V_obj ⇐ Composite
──────────────────────────────────────────────────────────────────────────────────
⟦D⟧⇒ᵥ :: ⟦Γ⟧ ⊢_v staticCall (boxDestructor(T)) [staticCall readField [$heap, V_obj, $field.C.f]] ⇒ ⟦T⟧


D :: Γ ⊢_L ?? : A       ↦    ⟦D⟧⇒ᵥ :: ⟦Γ⟧ ⊢_v staticCall $havoc_N [] ⇒ Any
D :: Γ ⊢_L ?  : A       ↦    ⟦D⟧⇒ᵥ :: ⟦Γ⟧ ⊢_v staticCall $hole_N [] ⇒ Any
```

#### ⟦·⟧⇐ᵥ

```
⟦D⟧⇒ᵥ :: ⟦Γ⟧ ⊢_v V ⇒ B    B ≤ ⟦A⟧ ↦ c
──────────────────────────────────────────
⟦D⟧⇐ᵥ :: ⟦Γ⟧ ⊢_v c(V) ⇐ ⟦A⟧
```

A : HighType is the input. B : LowType is discovered by synthesis.

#### ⟦·⟧⇒ₚ

There is exactly one clause. procGrades[f] = pure implies ⟦·⟧⇒ₚ is
undefined (delegate to ⟦·⟧⇒ᵥ). Inversion on any producer synthesis
derivation immediately gives you f, the checked args, ⟦B⟧, and d.

```
D₁ :: Γ ⊢_L e₁ : A₁  ...  Dₙ :: Γ ⊢_L eₙ : Aₙ
──────────────────────────────────────────────────
D :: Γ ⊢_L f(e₁,...,eₙ) : B    where procGrades[f] = d > pure

        ↦

⟦D₁⟧⇐ᵥ :: ⟦Γ⟧ ⊢_v V₁ ⇐ ⟦A₁⟧  ...  ⟦Dₙ⟧⇐ᵥ :: ⟦Γ⟧ ⊢_v Vₙ ⇐ ⟦Aₙ⟧
──────────────────────────────────────────────────────────────────────
⟦D⟧⇒ₚ :: ⟦Γ⟧ ⊢_p f(V₁,...,Vₙ) ⇒ ⟦B⟧ & d
```

#### Producer subsumption in the translation


```
D₁ :: Γ ⊢_L e₁ : A₁  ...  Dₙ :: Γ ⊢_L eₙ : Aₙ    K :: Γ ⊢_L rest : A
──────────────────────────────────────────────────────────────────────────
D :: Γ ⊢_L g(e₁,...,eₙ); rest : A    where procGrades[g] = d > pure

        ↦    let [x₁:T₁,...,xₖ:Tₖ] = outputs(g)

⟦D₁⟧⇐ᵥ :: ⟦Γ⟧ ⊢_v V₁ ⇐ ⟦A₁⟧  ...  ⟦Dₙ⟧⇐ᵥ :: ⟦Γ⟧ ⊢_v Vₙ ⇐ ⟦Aₙ⟧
⟦K⟧⇐ₚ :: ⟦Γ⟧,x₁:T₁,...,xₖ:Tₖ ⊢_p M_k ⇐ ⟦A⟧ & (d\e)
────────────────────────────────────────────────────────────────────────────────────────────
⟦D⟧⇐ₚ :: ⟦Γ⟧ ⊢_p effectfulCall g [V₁,...,Vₙ] [x₁:T₁,...,xₖ:Tₖ] M_k ⇐ ⟦A⟧ & e
```

#### Clauses of ⟦·⟧⇐ₚ

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


D_e :: Γ ⊢_L e : B    K :: Γ ⊢_L rest : A    e is not a call to g with procGrades[g] > pure
──────────────────────────────────────────────────────────────────────────────────────────
D :: Γ ⊢_L (x := e); rest : A

        ↦

⟦D_e⟧⇐ᵥ :: ⟦Γ⟧ ⊢_v V ⇐ ⟦Γ(x)⟧    ⟦K⟧⇐ₚ :: ⟦Γ⟧ ⊢_p M_k ⇐ ⟦A⟧ & e
────────────────────────────────────────────────────────────────────────
⟦D⟧⇐ₚ :: ⟦Γ⟧ ⊢_p assign x V M_k ⇐ ⟦A⟧ & e


D₁ :: Γ ⊢_L e₁ : A₁  ...  Dₙ :: Γ ⊢_L eₙ : Aₙ    K :: Γ ⊢_L rest : A    procGrades[g] = d > pure
──────────────────────────────────────────────────────────────────────────────────────────────────────
D :: Γ ⊢_L (x := g(e₁,...,eₙ)); rest : A

        ↦    let [x₁:T₁,...,xₖ:Tₖ] = outputs(g), r = resultIdx(d)

⟦D₁⟧⇐ᵥ :: ⟦Γ⟧ ⊢_v V₁ ⇐ ⟦A₁⟧  ...  ⟦Dₙ⟧⇐ᵥ :: ⟦Γ⟧ ⊢_v Vₙ ⇐ ⟦Aₙ⟧
⟦K⟧⇐ₚ :: ⟦Γ⟧,x₁:T₁,...,xₖ:Tₖ ⊢_p M_k ⇐ ⟦A⟧ & (d\e)
──────────────────────────────────────────────────────────────────────────────────────────────────────
⟦D⟧⇐ₚ :: ⟦Γ⟧ ⊢_p effectfulCall g [V₁,...,Vₙ] [x₁:T₁,...,xₖ:Tₖ] (assign x c(xᵣ) M_k)    where ⟦B⟧ ≤ ⟦Γ(x)⟧ ↦ c ⇐ ⟦A⟧ & e


D_body :: Γ,l ⊢_L body : A    K :: Γ ⊢_L rest : A
───────────────────────────────────────────────────
D :: Γ ⊢_L {body}ₗ; rest : A

        ↦

⟦D_body⟧⇐ₚ :: ⟦Γ⟧,l ⊢_p M_b ⇐ ⟦A⟧ & e    ⟦K⟧⇐ₚ :: ⟦Γ⟧ ⊢_p M_k ⇐ ⟦A⟧ & e
────────────────────────────────────────────────────────────────────────────────
⟦D⟧⇐ₚ :: ⟦Γ⟧ ⊢_p labeledBlock l M_b M_k ⇐ ⟦A⟧ & e


l ∈ Γ
─────────────────────
D :: Γ ⊢_L (exit l) : A

        ↦

⟦D⟧⇐ₚ :: ⟦Γ⟧ ⊢_p exit l ⇐ ⟦A⟧ & e


D_c :: Γ ⊢_L c : bool    D_b :: Γ ⊢_L body : A    K :: Γ ⊢_L rest : A
────────────────────────────────────────────────────────────────────────
D :: Γ ⊢_L (while c do body); rest : A

        ↦

⟦D_c⟧⇐ᵥ :: ⟦Γ⟧ ⊢_v V ⇐ bool    ⟦D_b⟧⇐ₚ :: ⟦Γ⟧ ⊢_p M_b ⇐ ⟦A⟧ & e    ⟦K⟧⇐ₚ :: ⟦Γ⟧ ⊢_p M_k ⇐ ⟦A⟧ & e
───────────────────────────────────────────────────────────────────────────────────────────────────────────
⟦D⟧⇐ₚ :: ⟦Γ⟧ ⊢_p whileLoop V M_b M_k ⇐ ⟦A⟧ & e


D_c :: Γ ⊢_L c : bool    K :: Γ ⊢_L rest : A
──────────────────────────────────────────────
D :: Γ ⊢_L (assume c); rest : A

        ↦

⟦D_c⟧⇐ᵥ :: ⟦Γ⟧ ⊢_v V ⇐ bool    ⟦K⟧⇐ₚ :: ⟦Γ⟧ ⊢_p M_k ⇐ ⟦A⟧ & e
────────────────────────────────────────────────────────────────────────
⟦D⟧⇐ₚ :: ⟦Γ⟧ ⊢_p assume V M_k ⇐ ⟦A⟧ & e


D_obj :: Γ ⊢_L obj : C    D_v :: Γ ⊢_L v : fieldType(C,f)    K :: Γ ⊢_L rest : A
────────────────────────────────────────────────────────────────────────────────────
D :: Γ ⊢_L (obj.f := v); rest : A

        ↦

⟦D_obj⟧⇐ᵥ :: ⟦Γ⟧ ⊢_v V_obj ⇐ Composite    ⟦D_v⟧⇐ᵥ :: ⟦Γ⟧ ⊢_v V_val ⇐ ⟦fieldType(C,f)⟧    ⟦K⟧⇐ₚ :: ⟦Γ⟧,$h:Heap ⊢_p M_k ⇐ ⟦A⟧ & e
──────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────
⟦D⟧⇐ₚ :: ⟦Γ⟧,$h:Heap ⊢_p varDecl $h Heap (updateField($heap, V_obj, $field.C.f, boxCtor(fieldType(C,f))(V_val))) M_k ⇐ ⟦A⟧ & e


D_r :: Γ ⊢_L root : Any    D_i :: Γ ⊢_L idx : Any    D_v :: Γ ⊢_L v : Any    K :: Γ ⊢_L rest : A
────────────────────────────────────────────────────────────────────────────────────────────────────
D :: Γ ⊢_L (root[idx] := v); rest : A

        ↦

⟦D_r⟧⇐ᵥ :: ⟦Γ⟧ ⊢_v V_r ⇐ Any    ⟦D_i⟧⇐ᵥ :: ⟦Γ⟧ ⊢_v V_i ⇐ Any    ⟦D_v⟧⇐ᵥ :: ⟦Γ⟧ ⊢_v V_v ⇐ Any    ⟦K⟧⇐ₚ :: ⟦Γ⟧ ⊢_p M_k ⇐ ⟦A⟧ & e
────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────
⟦D⟧⇐ₚ :: ⟦Γ⟧ ⊢_p assign root (staticCall Any_sets [V_i, V_r, V_v]) M_k ⇐ ⟦A⟧ & e


K :: Γ ⊢_L rest : A
────────────────────
D :: Γ ⊢_L ??; rest : A

        ↦

⟦K⟧⇐ₚ :: ⟦Γ⟧,$hv:Any ⊢_p M_k ⇐ ⟦A⟧ & e
────────────────────────────────────────────
⟦D⟧⇐ₚ :: ⟦Γ⟧,$hv:Any ⊢_p varDecl $hv Any none M_k ⇐ ⟦A⟧ & e


D_e :: Γ ⊢_L e : B    K :: Γ ⊢_L rest : A    e is not a call to g with procGrades[g] > pure
─────────────────────────────────────────────────────────────────────────────────────────
D :: Γ ⊢_L e; rest : A

        ↦

⟦K⟧⇐ₚ :: ⟦Γ⟧ ⊢_p M_k ⇐ ⟦A⟧ & e
──────────────────────────────────
⟦D⟧⇐ₚ :: ⟦Γ⟧ ⊢_p M_k ⇐ ⟦A⟧ & e    (value discarded)


D₁ :: Γ ⊢_L e₁ : A₁  ...  Dₙ :: Γ ⊢_L eₙ : Aₙ    K :: Γ ⊢_L rest : A    procGrades[g] = d > pure
──────────────────────────────────────────────────────────────────────────────────────────────────────
D :: Γ ⊢_L g(e₁,...,eₙ); rest : A    (expression as statement)

        ↦    let [x₁:T₁,...,xₖ:Tₖ] = outputs(g)

⟦D₁⟧⇐ᵥ :: ⟦Γ⟧ ⊢_v V₁ ⇐ ⟦A₁⟧  ...  ⟦Dₙ⟧⇐ᵥ :: ⟦Γ⟧ ⊢_v Vₙ ⇐ ⟦Aₙ⟧
⟦K⟧⇐ₚ :: ⟦Γ⟧,x₁:T₁,...,xₖ:Tₖ ⊢_p M_k ⇐ ⟦A⟧ & (d\e)
────────────────────────────────────────────────────────────────────────────────────────────
⟦D⟧⇐ₚ :: ⟦Γ⟧ ⊢_p effectfulCall g [V₁,...,Vₙ] [x₁:T₁,...,xₖ:Tₖ] M_k ⇐ ⟦A⟧ & e
```



### Projection

Map FGLProducer back to Laurel statements.

- `effectfulCall f args outputs body` → `[decl outputs; Assign [outputs] (StaticCall f args); body]`
- `assign x V body` → `[Assign [x] V; body]`
- `varDecl x T V body` → `[LocalVariable x T V; body]`
- Values map to their Laurel equivalents directly.


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


## Known Tech Debt

**Narrowing as pure function:** `Any_to_bool` etc. are modeled as pure (grade 1).
In Python, `__bool__` can have side effects. If needed later, narrowing becomes
grade > 1 and the coercion scheme changes.

**Instance procedures:** Methods emitted as top-level statics with `self` as first param.
`instanceProcedures` on CompositeType is empty.

**Prelude data encodings:** Lists/dicts are recursive ADTs (`ListAny_cons`/`DictStrAny_cons`).
Translation must emit these specific constructors.

**Multi-output forces err grade:** Translation declares `maybe_except : Error` on every
procedure. The `outputs.length > 1` heuristic in grade inference therefore always fires,
joining every user proc's grade with err. Architecturally, grade should come purely from
coinduction. In practice, Translation's output format forces err as minimum.

**Hole declarations collected post-hoc:** Architecture says `$hole_N` must be in Γ for
the staticCall rule. Implementation emits the staticCall without the function in Γ (using
the unknown-callee fallback) and collects hole names for declaration in the output program
afterward — same pattern as box constructors.

**Entry point extends env with outputs:** `fullElaborate` extends Γ with both inputs AND
outputs (`LaurelResult`, `maybe_except`) before elaboration. Necessary because Translation
assigns to output variables. Architecture's entry point description only mentions params.


## Current Status (2026-05-12)

### Parity with the Current Pipeline

On the 54 in-tree CI tests (`diff_test.sh compare` using `pyAnalyzeV2`):

- **52/54 tests:** Same result category (pass/inconclusive) as old pipeline
- **2/54 tests:** internal_error (`test_foo_client_folder`, `test_invalid_client_type`)
  — missing runtime function + field resolution on non-class receivers
- **3/54 tests:** pass → inconclusive (encoding quality gaps)
- **1/54 tests:** inconclusive → pass (improvement)

### Architectural issues pending rewrite

The implementation has fundamental architectural violations requiring a
rewrite of all three passes (see plan):
- Resolution uses imperative loops, string-based builtinMap, no resolved AST
- Translation does name resolution and kwargs matching (should be Resolution's job)
- Elaboration uses Option monad with failure (should be total)

### Key Implementation Decisions

- `annotationToHighType` handles Union/generic types directly (→ Any)
- Translation emits Hole for unresolved names (no undefined StaticCalls)
- `mkGradedCall` uses proc's declared outputs (no output arity mismatch)
- `proc` grade for runtime procedures (statement-level binding)
- `ifThenElse`/`labeledBlock` have `after` continuation (no VC blowup)
- `__main__` has metadata (VCs generated from module-level asserts)
- `gradeFromSignature` uses `isFunctional` (function vs procedure)


## Success Criteria

1. All 54 in-tree tests pass.
2. Translation is a fold — no post-hoc rewrites.
3. Elaboration is separate — translation emits no casts or grades.
4. Types from annotations — `Any` only when annotation absent.
5. One file per pass.
6. Implementation reads as transcription of the typing rules.




## Files

```
NameResolution.lean    -- Scope resolution: Python AST → Resolved AST
Translation.lean       -- Catamorphism: Resolved AST → Laurel
Elaborate.lean         -- Graded bidirectional elaboration: Laurel → GFGL → Laurel
Pipeline.lean          -- Wire passes, CLI
```




## References

- **Levy** (2003). *Call-By-Push-Value.* Value/Producer, Jump-With-Argument.
- **Egger, Møgelberg, Staton** (2014). "Linear Usage of State."
- **McDermott** (2025). "Grading call-by-push-value."
- **Dunfield & Krishnaswami** (2021). "Bidirectional Typing."
