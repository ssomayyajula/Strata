# Elaboration: Laurel → GFGL

---

## Purpose

This document specifies the Elaboration pass: the construction of a
**GFGL typing derivation** from a **Laurel typing derivation**.
Elaboration is a tree-to-tree map `⟦·⟧` defined by mutual recursion
on the Laurel derivation; its output derivation *is* the GFGL proof
term (term and typing derivation are one and the same object in
GFGL's bidirectional system).

The Translation pass that feeds this one (Python AST → Laurel AST)
is specified in the sibling file `TRANSLATION.md`. The pipeline's
prose overview is in `ARCHITECTURE.md`.

### The shape of this pass

```
  Laurel AST  ──── checked against Laurel typing rules ────▶  Laurel derivation D
                                                                    │
                                                                    │   Elaboration ⟦·⟧
                                                                    │   (derivation → derivation)
                                                                    ▼
                                                         GFGL derivation ⟦D⟧
```

- The Laurel AST coming out of Translation is checked against
  Laurel's rules to produce a derivation `D`. Elaboration's input is
  `D`, not the AST.
- Elaboration is defined by four mutually recursive functions,
  indexed by the two GFGL sorts (value / producer) and the two
  bidirectional modes (synthesis `⇒` / checking `⇐`).
- Side conditions that do not live in Laurel — procedure grades
  `procGrades[f]` and the ambient grade `e` — sit on the elaboration
  arrow, where they select which GFGL rule to build with.

### Prerequisite: grade inference

Procedure grades must be known before term production begins. Runtime
grades are read structurally from signatures via `gradeFromSignature`.
User grades are discovered by coinduction on the call graph: attempt
`⟦body⟧⇐ₚ` at increasing grades `[pure, proc, err, heap, heapErr]`
until one succeeds; the smallest succeeding grade is the procedure's
grade. The lattice has five elements, so the fixpoint converges in
at most five iterations.

"Success" here means all side conditions on the arrow are
satisfiable. In particular, the residual `d \ e` is undefined when a
callee's grade `d` exceeds the trial grade `e` — that is the signal
the coinduction uses to bump `e`.

### Notation

- `Γ` — Laurel context (variable bindings `(x : A)` and label
  bindings `(l : A)`).
- `Γ'` — GFGL context (variable bindings `(x : T)` and label
  bindings `(l : T & e)` — labels carry a grade).
- `⟦A⟧` — `eraseType(A)` from Laurel `HighType` to GFGL `LowType`.
  `⟦Γ⟧ = { (x : ⟦A⟧) | (x:A) ∈ Γ }` extended analogously on labels.
- `d`, `e`, `g` — grades from `{1, proc, err, heap, heapErr}`
  (`1 = pure`).
- `d \ e` — grade residual (left residuated on the monoid; see
  `ARCHITECTURE.md` §Grade Monoid).
- `⇒ᵥ` / `⇐ᵥ` — GFGL value synthesis / checking.
- `⇒ₚ` / `⇐ₚ` — GFGL producer synthesis / checking.
- `D`, `Dᵢ` — Laurel derivations; `⟦D⟧` — its elaboration.

### The judgments in play

| System       | Judgment                    | Reading                                                            |
|--------------|-----------------------------|--------------------------------------------------------------------|
| Laurel       | `Γ ⊢_L e : A`               | Laurel expression / statement list `e` has type `A`.               |
| GFGL value   | `Γ' ⊢_v V ⇒ A`              | GFGL value `V` synthesizes low type `A`.                           |
| GFGL value   | `Γ' ⊢_v V ⇐ A`              | GFGL value `V` checks against low type `A`.                        |
| GFGL producer| `Γ' ⊢_p M ⇒ A & d`          | GFGL producer `M` synthesizes return type `A` and grade `d`.       |
| GFGL producer| `Γ' ⊢_p M ⇐ A & e`          | GFGL producer `M` checks against return type `A` at ambient grade `e`. |
| Elaboration  | `⟦D⟧ = D'`                  | Laurel derivation `D` elaborates to GFGL derivation `D'`.          |

Laurel has a single judgment `Γ ⊢_L e : A` that is used both for
expressions (which carry a type) and for statement lists (whose type
is the return type of the enclosing procedure — statements at the
tail of a control-flow path terminate with `return e : A` or
`exit l : A`).

---

## Laurel Type System (Source)

Laurel is an impure CBV language. Effects are implicit; a call to an
effectful procedure is syntactically indistinguishable from a pure
call. One judgment: `Γ ⊢_L e : A`.

The context `Γ` carries variable bindings `(x : A)` and label bindings
`(l : A)`. Labels are bound by labeled blocks and consumed by `exit`.

```
─────────────────            ─────────────────            ─────────────────
Γ ⊢_L n : int                Γ ⊢_L b : bool               Γ ⊢_L s : string


(x : A) ∈ Γ
─────────────────
Γ ⊢_L x : A


f : (A₁,...,Aₙ) → B ∈ Γ       Γ ⊢_L e₁ : A₁   ...   Γ ⊢_L eₙ : Aₙ
──────────────────────────────────────────────────────────────────
Γ ⊢_L f(e₁,...,eₙ) : B


Γ ⊢_L e : C       fields(C, f) = T
──────────────────────────────────
Γ ⊢_L e.f : T


C ∈ classes(Γ)
─────────────────
Γ ⊢_L new C : C


─────────────────             ─────────────────
Γ ⊢_L ?? : A  (nondet)        Γ ⊢_L ? : A  (det)


Γ ⊢_L e : Γ(x)        Γ ⊢_L rest : A
─────────────────────────────────────
Γ ⊢_L (x := e); rest : A


Γ ⊢_L e : T       Γ, x:T ⊢_L rest : A
──────────────────────────────────────
Γ ⊢_L (var x:T := e); rest : A


Γ ⊢_L c : bool   Γ ⊢_L t : A   Γ ⊢_L f : A   Γ ⊢_L rest : A
─────────────────────────────────────────────────────────────
Γ ⊢_L (if c then t else f); rest : A


Γ ⊢_L c : bool   Γ ⊢_L body : A   Γ ⊢_L rest : A
───────────────────────────────────────────────────
Γ ⊢_L (while c do body); rest : A


Γ, l:A ⊢_L body : A       Γ ⊢_L rest : A
──────────────────────────────────────────
Γ ⊢_L {body}ₗ; rest : A


(l : A) ∈ Γ
───────────────────
Γ ⊢_L (exit l) : A


Γ ⊢_L e : A
─────────────────────
Γ ⊢_L (return e) : A


Γ ⊢_L c : bool       Γ ⊢_L rest : A
────────────────────────────────────
Γ ⊢_L (assert c); rest : A


Γ ⊢_L c : bool       Γ ⊢_L rest : A
────────────────────────────────────
Γ ⊢_L (assume c); rest : A


Γ ⊢_L obj : C     Γ ⊢_L v : fieldType(C, f)     Γ ⊢_L rest : A
────────────────────────────────────────────────────────────────
Γ ⊢_L (obj.f := v); rest : A


Γ ⊢_L root : Any   Γ ⊢_L idx : Any   Γ ⊢_L v : Any   Γ ⊢_L rest : A
─────────────────────────────────────────────────────────────────────
Γ ⊢_L (root[idx] := v); rest : A
```

Observations:

- Statement-list rules carry the procedure's return type `A`,
  propagated through the continuation `rest`. This is what lets
  `return e : A` and `exit l : A` tie off a control-flow path with
  the same `A`.
- `new C : C` is a value in Laurel. Heap threading only appears at
  elaboration time.
- There is no grade premise anywhere. Laurel does not know about
  effects.

---

## GFGL Type System (Target — Bidirectional, Graded)

GFGL has two sorts, **values** (pure) and **producers** (effectful,
graded). Typing is bidirectional. The context carries variable
bindings `(x : A)` and label bindings `(l : A & e)` — labels record
the grade at which they were bound.

```
Γ' ⊢_v V ⇒ A             value synthesis
Γ' ⊢_v V ⇐ A             value checking
Γ' ⊢_p M ⇒ A & d         producer synthesis
Γ' ⊢_p M ⇐ A & e         producer checking
```

### Value rules

```
─────────────────────────        ─────────────────────────        ──────────────────────────────
Γ' ⊢_v litInt n ⇒ TInt           Γ' ⊢_v litBool b ⇒ TBool          Γ' ⊢_v litString s ⇒ TString


(x : A) ∈ Γ'
─────────────────────────
Γ' ⊢_v var x ⇒ A


f : (A₁,...,Aₙ) → B ∈ Γ'       Γ' ⊢_v V₁ ⇐ A₁   ...   Γ' ⊢_v Vₙ ⇐ Aₙ
──────────────────────────────────────────────────────────────────────
Γ' ⊢_v staticCall f [V₁,...,Vₙ] ⇒ B


Γ' ⊢_v V ⇒ A      subsume(A, B) = c
───────────────────────────────────
Γ' ⊢_v c(V) ⇐ B                          (value mode switch)
```

### Producer synthesis

```
(l : A & e) ∈ Γ'
─────────────────────────
Γ' ⊢_p exit l ⇒ A & e


f : (A₁,...,Aₙ) → B & d ∈ Γ'    Γ' ⊢_v V₁ ⇐ A₁   ...   Γ' ⊢_v Vₙ ⇐ Aₙ
───────────────────────────────────────────────────────────────────────
Γ' ⊢_p f(V₁,...,Vₙ) ⇒ B & d
```

### Producer subsumption (mode switch ⇒ₚ to ⇐ₚ)

This is the single rule that binds a synthesized producer into the
checking context. All effectful calls enter the derivation through it.

```
Γ' ⊢_p M ⇒ B & d      subsume(B, A) = c
Γ', x₁:T₁,...,xₖ:Tₖ ⊢_p K ⇐ A & (d \ e)
────────────────────────────────────────────────────────────────────
Γ' ⊢_p effectfulCall M [x₁:T₁,...,xₖ:Tₖ] (c(xⱼ); K) ⇐ A & e
```

`M` synthesizes producer type `B & d`. Its outputs `[x₁:T₁,...,xₖ:Tₖ]`
(from the callee's declared signature) extend the context for the
continuation `K`, which is checked at the **residual grade** `d \ e`.
The coercion `c` is applied to the relevant output `xⱼ` inside `K`.

### Producer checking rules

```
─────────────────────────
Γ' ⊢_p unit ⇐ A & e


Γ' ⊢_v V ⇐ A
──────────────────────────────────────
Γ' ⊢_p returnValue V ⇐ A & e


Γ' ⊢_v V ⇐ Γ'(x)        Γ' ⊢_p K ⇐ A & e
─────────────────────────────────────────
Γ' ⊢_p assign x V K ⇐ A & e


Γ' ⊢_v V ⇐ T        Γ', x:T ⊢_p K ⇐ A & e
───────────────────────────────────────────
Γ', x:T ⊢_p varDecl x T V K ⇐ A & e


Γ' ⊢_v V ⇐ bool   Γ' ⊢_p M_t ⇐ A & e   Γ' ⊢_p M_f ⇐ A & e   Γ' ⊢_p K ⇐ A & e
──────────────────────────────────────────────────────────────────────────────
Γ' ⊢_p ifThenElse V M_t M_f K ⇐ A & e


Γ' ⊢_v V ⇐ bool    Γ' ⊢_p M_b ⇐ A & e    Γ' ⊢_p K ⇐ A & e
─────────────────────────────────────────────────────────────
Γ' ⊢_p whileLoop V M_b K ⇐ A & e


Γ' ⊢_v V ⇐ bool        Γ' ⊢_p K ⇐ A & e
────────────────────────────────────────
Γ' ⊢_p assert V K ⇐ A & e


Γ' ⊢_v V ⇐ bool        Γ' ⊢_p K ⇐ A & e
────────────────────────────────────────
Γ' ⊢_p assume V K ⇐ A & e


Γ', l:(A & e) ⊢_p M_b ⇐ A & e        Γ' ⊢_p K ⇐ A & e
───────────────────────────────────────────────────────
Γ' ⊢_p labeledBlock l M_b K ⇐ A & e


f : (A₁,...,Aₙ) → [x₁:T₁,...,xₖ:Tₖ] & d ∈ Γ'
Γ' ⊢_v V₁ ⇐ A₁   ...   Γ' ⊢_v Vₙ ⇐ Aₙ
Γ', x₁:T₁,...,xₖ:Tₖ ⊢_p K ⇐ A & (d \ e)
─────────────────────────────────────────────────────────────────
Γ' ⊢_p effectfulCall f [V₁,...,Vₙ] [x₁:T₁,...,xₖ:Tₖ] K ⇐ A & e
```

The final rule is the specialized form of producer subsumption where
`M = f(V₁,...,Vₙ)` is a direct call — the outputs are read from `f`'s
signature and no coercion witness is applied at the output.

---

## Elaboration (⟦·⟧: Laurel derivations → GFGL derivations)

Elaboration is defined by four mutually recursive functions. Types
and contexts are translated pointwise: `⟦A⟧ = eraseType(A)`, `⟦Γ⟧ = {
(x : ⟦A⟧) | (x:A) ∈ Γ } ∪ { (l : ⟦A⟧ & e) | (l:A) ∈ Γ, l bound at
ambient grade e }`.

```
⟦·⟧⇒ᵥ : (Γ ⊢_L e : A) → ∃V.    (⟦Γ⟧ ⊢_v V ⇒ ⟦A⟧)
⟦·⟧⇐ᵥ : (Γ ⊢_L e : A) → (B : LowType) → ∃V. (⟦Γ⟧ ⊢_v V ⇐ B)
⟦·⟧⇒ₚ : (Γ ⊢_L e : A) → ∃M,d.   (⟦Γ⟧ ⊢_p M ⇒ ⟦A⟧ & d)
⟦·⟧⇐ₚ : (Γ ⊢_L S;rest : A) → (e : Grade) → ∃M. (⟦Γ⟧ ⊢_p M ⇐ ⟦A⟧ & e)
```

All four read `procGrades[g]` for every callee `g`. Grade inference
(see §Prerequisite above) runs first and provides this map.

### How the functions interact

`⟦·⟧⇐ₚ` drives elaboration at ambient grade `e` — initially
`procGrades[f]` for the enclosing procedure, then `d \ e` inside the
continuation of each bound effectful call. For each statement:

- Sub-expressions are translated via `⟦·⟧⇐ᵥ` at their expected type.
- The continuation is translated via `⟦·⟧⇐ₚ` at the same ambient
  grade (or at `d \ e` if an effectful call is bound).
- For assignments, `⟦·⟧⇒ₚ` determines if the RHS is a value or a
  producer:
  - `procGrades[callee] = pure` → delegate to `⟦·⟧⇒ᵥ`, use its
    result as a value;
  - `procGrades[callee] = d > pure` → producer subsumption fires:
    `⟦·⟧⇒ₚ` produces a synthesis derivation, the GFGL producer
    subsumption rule binds it via `effectfulCall`, and the
    continuation is checked at `d \ e`.

**The to-rule.** When a pure call `f(e₁,...,eₙ)` has an argument `eᵢ`
whose callee has `procGrades[callee(eᵢ)] > pure`, that argument is
ANF-lifted into an `effectfulCall` binding before the outer call.
GFGL values cannot contain producers, so this lift is obligatory.
Arguments are processed left-to-right (CBV order).

### Clauses of `⟦·⟧⇒ᵥ`

```
─────────────────────────────────────────
D :: Γ ⊢_L n : int
        ↦   ⟦D⟧⇒ᵥ :: ⟦Γ⟧ ⊢_v litInt n ⇒ TInt

(and analogously for litBool, litString)


(x : A) ∈ Γ
────────────────────────
D :: Γ ⊢_L x : A
        ↦   ⟦D⟧⇒ᵥ :: ⟦Γ⟧ ⊢_v var x ⇒ ⟦A⟧


D₁ :: Γ ⊢_L e₁ : A₁   ...   Dₙ :: Γ ⊢_L eₙ : Aₙ
──────────────────────────────────────────────────
D :: Γ ⊢_L f(e₁,...,eₙ) : B       where procGrades[f] = pure

        ↦

⟦D₁⟧⇐ᵥ :: ⟦Γ⟧ ⊢_v V₁ ⇐ ⟦A₁⟧   ...   ⟦Dₙ⟧⇐ᵥ :: ⟦Γ⟧ ⊢_v Vₙ ⇐ ⟦Aₙ⟧
─────────────────────────────────────────────────────────────────────
⟦D⟧⇒ᵥ :: ⟦Γ⟧ ⊢_v staticCall f [V₁,...,Vₙ] ⇒ ⟦B⟧


D_obj :: Γ ⊢_L e : C       fields(C, f) = T
────────────────────────────────────────────
D :: Γ ⊢_L e.f : T

        ↦

⟦D_obj⟧⇐ᵥ :: ⟦Γ⟧ ⊢_v V_obj ⇐ Composite
───────────────────────────────────────────────────────────────────────
⟦D⟧⇒ᵥ :: ⟦Γ⟧ ⊢_v Box..tVal!(readField($heap, V_obj, $field.C.f)) ⇒ ⟦T⟧


D :: Γ ⊢_L ?? : A       ↦   ⟦D⟧⇒ᵥ :: ⟦Γ⟧, $havoc_N ⊢_v staticCall $havoc_N [] ⇒ Any
D :: Γ ⊢_L ? : A        ↦   ⟦D⟧⇒ᵥ :: ⟦Γ⟧, $hole_N  ⊢_v staticCall $hole_N  [] ⇒ Any
```

### `⟦·⟧⇐ᵥ` (single clause: value mode switch)

```
⟦D⟧⇒ᵥ :: ⟦Γ⟧ ⊢_v V ⇒ A       subsume(A, B) = c
──────────────────────────────────────────────
⟦D⟧⇐ᵥ :: ⟦Γ⟧ ⊢_v c(V) ⇐ B
```

When `subsume` returns `refl`, `c` is the identity and no coercion is
inserted. Otherwise `c` is proof-relevant GFGL term structure
(`from_int`, `Any..as_int!`, …) — see `ARCHITECTURE.md` §Coercion
Table.

### Clauses of `⟦·⟧⇒ₚ`

```
D₁ :: Γ ⊢_L e₁ : A₁   ...   Dₙ :: Γ ⊢_L eₙ : Aₙ
──────────────────────────────────────────────────
D :: Γ ⊢_L f(e₁,...,eₙ) : B       where procGrades[f] = d > pure

        ↦

⟦D₁⟧⇐ᵥ :: ⟦Γ⟧ ⊢_v V₁ ⇐ ⟦A₁⟧   ...   ⟦Dₙ⟧⇐ᵥ :: ⟦Γ⟧ ⊢_v Vₙ ⇐ ⟦Aₙ⟧
─────────────────────────────────────────────────────────────────────
⟦D⟧⇒ₚ :: ⟦Γ⟧ ⊢_p f(V₁,...,Vₙ) ⇒ ⟦B⟧ & d
```

When `procGrades[f] = pure`, `⟦·⟧⇒ₚ` delegates to `⟦·⟧⇒ᵥ`.

### Producer subsumption in the translation

When `⟦·⟧⇐ₚ` at ambient grade `e` encounters an expression whose head
is a call with `procGrades[g] = d > pure`, it calls `⟦·⟧⇒ₚ` to get
the synthesis derivation, then applies the GFGL producer subsumption
rule to bind it:

```
⟦D⟧⇒ₚ :: ⟦Γ⟧ ⊢_p g(V₁,...,Vₙ) ⇒ ⟦B⟧ & d        K :: Γ ⊢_L rest : A

        ↦

⟦K⟧⇐ₚ :: ⟦Γ⟧, x₁:T₁,...,xₖ:Tₖ ⊢_p M_k ⇐ ⟦A⟧ & (d \ e)
──────────────────────────────────────────────────────────────────────────────────────────
⟦Γ⟧, x₁:T₁,...,xₖ:Tₖ ⊢_p effectfulCall g [V₁,...,Vₙ] [x₁:T₁,...,xₖ:Tₖ] M_k ⇐ ⟦A⟧ & e
```

The callee `g` and arguments `V₁,...,Vₙ` are the same as in the
synthesis premise. The outputs `[x₁:T₁,...,xₖ:Tₖ]` are `g`'s declared
outputs read from its signature in `typeEnv`. The continuation `M_k`
is checked at the residual `d \ e`.

### Clauses of `⟦·⟧⇐ₚ`

All clauses below receive an ambient grade `e` (= `procGrades[f]` for
the enclosing procedure `f`, or `d \ e'` from an enclosing
`effectfulCall`).

```
D_c :: Γ ⊢_L c : bool    D_t :: Γ ⊢_L t : A    D_f :: Γ ⊢_L f : A    K :: Γ ⊢_L rest : A
──────────────────────────────────────────────────────────────────────────────────────────────
D :: Γ ⊢_L (if c then t else f); rest : A

        ↦

⟦D_c⟧⇐ᵥ :: ⟦Γ⟧ ⊢_v V ⇐ bool
⟦D_t⟧⇐ₚ :: ⟦Γ⟧ ⊢_p M_t ⇐ ⟦A⟧ & e       ⟦D_f⟧⇐ₚ :: ⟦Γ⟧ ⊢_p M_f ⇐ ⟦A⟧ & e
⟦K⟧⇐ₚ   :: ⟦Γ⟧ ⊢_p M_k ⇐ ⟦A⟧ & e
─────────────────────────────────────────────────────────────────────────
⟦D⟧⇐ₚ :: ⟦Γ⟧ ⊢_p ifThenElse V M_t M_f M_k ⇐ ⟦A⟧ & e


D_e :: Γ ⊢_L e : A
───────────────────────────
D :: Γ ⊢_L (return e) : A

        ↦

⟦D_e⟧⇐ᵥ :: ⟦Γ⟧ ⊢_v V ⇐ ⟦A⟧
───────────────────────────────────────
⟦D⟧⇐ₚ :: ⟦Γ⟧ ⊢_p returnValue V ⇐ ⟦A⟧ & e


D_init :: Γ ⊢_L e : T       K :: Γ, x:T ⊢_L rest : A
────────────────────────────────────────────────────
D :: Γ ⊢_L (var x:T := e); rest : A

        ↦

⟦D_init⟧⇐ᵥ :: ⟦Γ⟧ ⊢_v V ⇐ ⟦T⟧         ⟦K⟧⇐ₚ :: ⟦Γ⟧, x:⟦T⟧ ⊢_p M_k ⇐ ⟦A⟧ & e
────────────────────────────────────────────────────────────────────────────
⟦D⟧⇐ₚ :: ⟦Γ⟧, x:⟦T⟧ ⊢_p varDecl x ⟦T⟧ V M_k ⇐ ⟦A⟧ & e


D_c :: Γ ⊢_L c : bool       K :: Γ ⊢_L rest : A
─────────────────────────────────────────────────
D :: Γ ⊢_L (assert c); rest : A

        ↦

⟦D_c⟧⇐ᵥ :: ⟦Γ⟧ ⊢_v V ⇐ bool         ⟦K⟧⇐ₚ :: ⟦Γ⟧ ⊢_p M_k ⇐ ⟦A⟧ & e
────────────────────────────────────────────────────────────────────
⟦D⟧⇐ₚ :: ⟦Γ⟧ ⊢_p assert V M_k ⇐ ⟦A⟧ & e

(assume is analogous)


D_e :: Γ ⊢_L e : B        K :: Γ ⊢_L rest : A
──────────────────────────────────────────────
D :: Γ ⊢_L (x := e); rest : A

        ↦

If procGrades[callee(e)] = pure:

    ⟦D_e⟧⇐ᵥ :: ⟦Γ⟧ ⊢_v V ⇐ ⟦Γ(x)⟧        ⟦K⟧⇐ₚ :: ⟦Γ⟧ ⊢_p M_k ⇐ ⟦A⟧ & e
    ────────────────────────────────────────────────────────────────────
    ⟦D⟧⇐ₚ :: ⟦Γ⟧ ⊢_p assign x V M_k ⇐ ⟦A⟧ & e

If procGrades[callee(e)] = d > pure:

    producer subsumption fires: bind via effectfulCall, apply the
    result coercion c = subsume(B, Γ(x)), assign to x in the
    continuation, check K at d\e.


D_body :: Γ, l:A ⊢_L body : A       K :: Γ ⊢_L rest : A
─────────────────────────────────────────────────────────
D :: Γ ⊢_L {body}ₗ; rest : A

        ↦

⟦D_body⟧⇐ₚ :: ⟦Γ⟧, l:(⟦A⟧ & e) ⊢_p M_b ⇐ ⟦A⟧ & e    ⟦K⟧⇐ₚ :: ⟦Γ⟧ ⊢_p M_k ⇐ ⟦A⟧ & e
───────────────────────────────────────────────────────────────────────────────────
⟦D⟧⇐ₚ :: ⟦Γ⟧ ⊢_p labeledBlock l M_b M_k ⇐ ⟦A⟧ & e

    (the label binding l : A in Γ becomes l : ⟦A⟧ & e in ⟦Γ⟧;
     exit l then reads the grade from the label binding)


(l : A) ∈ Γ
────────────────────────
D :: Γ ⊢_L (exit l) : A

        ↦

⟦D⟧⇐ₚ :: ⟦Γ⟧ ⊢_p exit l ⇐ ⟦A⟧ & e

    (the producer synthesis rule for exit reads
     (l : ⟦A⟧ & e) from ⟦Γ⟧; ambient e matches the label's e)
```

The remaining clauses (`while`, `assume`, field write, subscript
assignment, `new`, expression-as-statement) follow the same
structure: sub-expressions through `⟦·⟧⇐ᵥ`, the continuation through
`⟦·⟧⇐ₚ` at the same ambient `e`, heap-touching operations gated on
`heap ≤ e` via producer subsumption on the heap-threading calls.

---

## Rule → Implementation Mapping

The Translation pass has its own mapping in `TRANSLATION.md`.

### Laurel type system (candidate-derivation checking)

The Laurel rules above are not implemented as an explicit pass. They
are the implicit typing discipline that Translation targets and
Elaboration relies on:

- Translation preserves the Laurel-AST invariants needed for each
  Laurel rule's side conditions (e.g. `f : … → B ∈ Γ` whenever a
  `StaticCall f …` is emitted — see the Illegal-States-Unrepresentable
  principle in `ARCHITECTURE.md`).
- Elaboration's dispatch on AST shape (`synthValue`, `synthExpr`,
  `checkProducer`) pattern-matches the same cases as the Laurel rules.

### Elaboration

The implementation is in `Strata/Languages/FineGrainLaurel/Elaborate.lean`.

| Formal object                      | Lean function                                  |
|------------------------------------|------------------------------------------------|
| `⟦·⟧⇒ᵥ : Γ ⊢_L e : A ↦ ⟦Γ⟧ ⊢_v V ⇒ ⟦A⟧` | `synthValue`                             |
| `⟦·⟧⇐ᵥ : Γ ⊢_L e : A ↦ ⟦Γ⟧ ⊢_v V ⇐ B`   | `checkValue`                             |
| `⟦·⟧⇒ₚ : Γ ⊢_L e : A ↦ ⟦Γ⟧ ⊢_p M ⇒ ⟦A⟧ & d` | `synthExpr` (defunctionalized `SynthResult`) |
| `⟦·⟧⇐ₚ : Γ ⊢_L S;rest : A ↦ ⟦Γ⟧ ⊢_p M ⇐ ⟦A⟧ & e` | `checkProducer` (threads `rest` as continuation) |
| value mode switch `subsume(A, B) = c`   | `subsume` + `applySubsume`               |
| producer subsumption (⇒ₚ → ⇐ₚ)         | `checkProducer` StaticCall/Assign branches via `mkGradedCall` |
| to-rule (effectful argument to pure call) | `checkArgsK`                          |
| grade lookup `procGrades[f]`           | reader read of `procGrades`              |
| grade residual `d \ e`                 | `Grade.residual d e`                     |
| grade inference (coinduction)          | `fullElaborate` + `discoverGrades` + `tryGrades` |
| runtime grade from signature           | `gradeFromSignature`                     |
| procedure signature rewriting (heap in/out) | inside `fullElaborate`              |

### Projection

Forgets the grading; trivial catamorphism `GFGL → Laurel`.

| Form                                     | Lean function        |
|------------------------------------------|----------------------|
| GFGL value → Laurel expression           | `projectValue`       |
| GFGL producer → Laurel statement list    | `projectProducer`    |
| Procedure body                           | `projectBody`        |

---

## References

- Levy, 2003. *Call-By-Push-Value.*
- Egger, Møgelberg, Staton, 2014. "Linear Usage of State."
- McDermott, 2025. "Grading call-by-push-value."
- Dunfield & Krishnaswami, 2021. "Bidirectional Typing."
- Gaboardi et al., 2016. "Combining Effects and Coeffects via Grading."
