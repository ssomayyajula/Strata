# Python → Laurel Translation Architecture


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




## Translation

A catamorphism over the Python AST. One case per constructor. Deterministic.

**Does:** scope hoisting, object construction (.New + __init__), context managers,
for-loop abstraction (havoc + assume), loop labels, calling convention (kwargs +
defaults via Γ), module-level wrapping (__main__), mutable param copies,
error output declaration (`maybe_except: Error` in proc outputs).

**Does NOT:** cast insertion, literal wrapping, effect determination.

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

### eraseType

```lean
def eraseType : HighType → LowType
  | .TInt => .TInt | .TBool => .TBool | .TString => .TString
  | .TFloat64 => .TFloat64 | .TVoid => .TVoid | .TCore n => .TCore n
  | .UserDefined id => match id.text with
    | "Any" => .TCore "Any" | "Error" => .TCore "Error"
    | "ListAny" => .TCore "ListAny" | "DictStrAny" => .TCore "DictStrAny"
    | _ => .TCore "Composite"
  | .THeap => .TCore "Heap"
  | _ => .TCore "Any"
```

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

Γ ⊢_v V ⇒ A    subsume(A, B) = c
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
Γ ⊢_p f(V₁,...,Vₙ) ⇒ B & d    subsume(B, A) = c
Γ,x₁:T₁,...,xₖ:Tₖ ⊢_p K ⇐ A & (d\e)
────────────────────────────────────────────────────────────────────────────
Γ ⊢_p effectfulCall f [V₁,...,Vₙ] [x₁:T₁,...,xₖ:Tₖ] (c(xᵣ); K) ⇐ A & e
```

`xᵣ` is the result output (position r among the declared outputs).
c coerces it to the target type. K is checked at residual d\e.

The grade d determines the calling convention:

```
d = pure:                (no effectfulCall — handled by ⟦·⟧⇒ᵥ)
d ∈ {proc, err}:         effectfulCall f args outputs(f) K
d ∈ {heap, heapErr}:     effectfulCall f ($heap::args) outputs(f) K
```

`$heap` is the current heap variable (initialized from `$heap_in` at
proc entry for heap-graded procs, updated to fresh names by each
effectfulCall whose outputs include a Heap). `outputs(f)` comes from
f's declared signature after grade-based rewriting.

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

#### Types and contexts

```
⟦A⟧ = eraseType(A)
⟦Γ⟧ = { (x : ⟦A⟧) | (x:A) ∈ Γ } ∪ { l | l ∈ Γ }
```

The context translation ⟦Γ⟧ erases every type binding and preserves
labels. Each translation clause extends ⟦Γ⟧ with new bindings at
erased types: effectfulCall adds fresh output variables at ⟦Tᵢ⟧,
varDecl adds the declared name at ⟦T⟧. These extensions are visible
in the recursive call on continuation K.

#### The four functions

**Input:** a Laurel.Program (typed procedures with bodies).  
**Output:** a GFGL.Program (same procedures with graded, effect-explicit bodies).

The translation is four mutually recursive functions. Each takes a Laurel
typing derivation D — the context Γ, type A, and term structure are all
inherited from D. The only additional input is the ambient grade e for
⟦·⟧⇐ₚ (from the procedure's inferred grade, or the residual d\e after
an effectfulCall).

```
⟦·⟧⇒ᵥ : (D :: Γ ⊢_L e : A) → ∃V. (⟦Γ⟧ ⊢_v V ⇒ ⟦A⟧)
⟦·⟧⇐ᵥ = ⟦·⟧⇒ᵥ composed with subsumption (target ⟦T⟧ from enclosing derivation)
⟦·⟧⇒ₚ : (D :: Γ ⊢_L f(e₁,...,eₙ) : A) → ∃M. (⟦Γ⟧ ⊢_p M ⇒ ⟦A⟧ & procGrades[f])
⟦·⟧⇐ₚ : (D :: Γ ⊢_L S;rest : A) → (e : Grade) → ∃M. (⟦Γ⟧ ⊢_p M ⇐ ⟦A⟧ & e)
```

⟦·⟧⇐ᵥ is not an independent function — it synthesizes via ⟦·⟧⇒ᵥ then
applies `subsume(⟦A⟧, ⟦T⟧)` where T is the type the enclosing Laurel
derivation expects at that position (parameter type, assignment target type).

⟦·⟧⇒ₚ has exactly one clause (call with grade > pure); inversion is trivial.

#### Grade inference

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

Elaboration begins:
```
⟦Γ,p₁:⟦T₁⟧,...,pₘ:⟦Tₘ⟧ ⊢_L B : ⟦R⟧⟧⇐ₚ at grade e
```

#### Subgrading

Every call site checks `d ≤ e` (callee's grade ≤ ambient grade) before
emitting effectfulCall. This is the operational content of the residual:
`d\e` is defined iff `d ≤ e`. If it's not, elaboration fails.

The calling convention is determined by d:
```
d ∈ {proc, err}:         effectfulCall f args outputs(f) K
d ∈ {heap, heapErr}:     effectfulCall f ($heap::args) outputs(f) K
```

`$heap` is the current heap variable (initialized from `$heap_in` at
proc entry, updated to a fresh name by each effectfulCall whose outputs
include a Heap).

#### Auxiliary definitions

```
outputs(g)    = declared outputs of g after signature rewriting
resultIdx(d)  = 1 if d ∈ {proc, err}; 2 if d ∈ {heap, heapErr}
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
⟦D⟧⇒ᵥ :: ⟦Γ⟧ ⊢_v V ⇒ A    subsume(A, B) = c
────────────────────────────────────────────────
⟦D⟧⇐ᵥ :: ⟦Γ⟧ ⊢_v c(V) ⇐ B
```

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
⟦D⟧⇐ₚ :: ⟦Γ⟧ ⊢_p effectfulCall g [V₁,...,Vₙ] [x₁:T₁,...,xₖ:Tₖ] (assign x (subsume(xᵣ, ⟦Γ(x)⟧)) M_k) ⇐ ⟦A⟧ & e


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

### Subsumption Table

```lean
def subsume (actual expected : LowType) : CoercionResult :=
  if actual == expected then .refl else match actual, expected with
  | .TInt, .TCore "Any"              => .coerce (fun md => .fromInt md)
  | .TBool, .TCore "Any"             => .coerce (fun md => .fromBool md)
  | .TString, .TCore "Any"           => .coerce (fun md => .fromStr md)
  | .TFloat64, .TCore "Any"          => .coerce (fun md => .fromFloat md)
  | .TCore "Composite", .TCore "Any" => .coerce (fun md => .fromComposite md)
  | .TCore "ListAny", .TCore "Any"   => .coerce (fun md => .fromListAny md)
  | .TCore "DictStrAny", .TCore "Any"=> .coerce (fun md => .fromDictStrAny md)
  | .TVoid, .TCore "Any"             => .coerce (fun md _ => .fromNone md)
  | .TCore "Any", .TBool             => .coerce (fun md v => .staticCall md "Any_to_bool" [v])
  | .TCore "Any", .TInt              => .coerce (fun md v => .staticCall md "Any..as_int!" [v])
  | .TCore "Any", .TString           => .coerce (fun md v => .staticCall md "Any..as_string!" [v])
  | .TCore "Any", .TFloat64          => .coerce (fun md v => .staticCall md "Any..as_float!" [v])
  | .TCore "Any", .TCore "Composite" => .coerce (fun md v => .staticCall md "Any..as_Composite!" [v])
  | _, _ => .unrelated
```


## Projection

Trivial catamorphism. Forget grades. Map GFGL → Laurel:

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


## Success Criteria

1. All 54 in-tree tests pass.
2. Translation is a fold — no post-hoc rewrites.
3. Elaboration is separate — translation emits no casts or grades.
4. Types from annotations — `Any` only when annotation absent.
5. One file per pass.
6. Implementation reads as transcription of the typing rules.




## Files

```
NameResolution.lean    -- Build Γ
Translation.lean       -- Fold over AST → Laurel
Elaborate.lean         -- Graded bidirectional elaboration
Pipeline.lean          -- Wire passes, CLI
```




## References

- **Levy** (2003). *Call-By-Push-Value.* Value/Producer, Jump-With-Argument.
- **Egger, Møgelberg, Staton** (2014). "Linear Usage of State."
- **McDermott** (2025). "Grading call-by-push-value."
- **Dunfield & Krishnaswami** (2021). "Bidirectional Typing."
