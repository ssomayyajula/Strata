# Translation and Elaboration: Rules

---

## Purpose

This document gives a single, coherent presentation of the rules that
drive the two main passes of the pipeline:

- **Translation** — Python AST → Laurel AST (which, together with Γ,
  gives a *candidate* Laurel typing derivation; see below).
- **Elaboration** — Laurel typing derivation → GFGL typing derivation,
  defined by recursion on the Laurel derivation.

It is companion material to `ARCHITECTURE.md`. The prose overview and
engineering principles live there; the rules live here.

### The shape of the pipeline, precisely

```
  Python AST
     │
     │   Translation (tree-transforming fold)
     ▼
  Laurel AST  ──── checked against Laurel typing rules [L-*] ────▶  candidate Laurel derivation D
                                                                          │
                                                                          │   Elaboration ⟦·⟧
                                                                          │   (tree → tree, recursion on D)
                                                                          ▼
                                                              GFGL derivation ⟦D⟧
```

- **Translation** emits a Laurel AST. Every Laurel AST admits a
  *candidate* typing derivation under Laurel's own rules, but this
  derivation may be invalid (undefined names, bad types, effects where
  a value is expected). If the candidate is invalid the pipeline
  errors; if valid, we have a genuine Laurel derivation `D`.
- **Elaboration** is a partial map `⟦·⟧ : LaurelDeriv → GFGLDeriv`
  defined by recursion on the *Laurel derivation*, not on the
  AST. Side conditions (grades `G(f)`, ambient `g`, `subsume`,
  `subgrade`) live on the arrow, because they are elaboration-time
  facts consulted to choose which GFGL rule to build with. The sub-
  derivations of the input tree get elaborated to sub-derivations of
  the output tree.

This is what "tree → tree" means here: a Laurel derivation with root
rule `[L-X]` and sub-derivations `D₁,…,Dₖ` is mapped to a GFGL
derivation with root rule `[G-Y]` and sub-derivations `⟦D₁⟧,…,⟦Dₖ⟧`
(sometimes reordered or inserted under subsumption witnesses).

### Notation conventions

- `Γ` — typing environment from Resolution. Maps names to `NameInfo`.
  Laurel's typing judgments and elaboration's Γ are the same object.
- `G` — grade environment, `procGrades : name → Grade`. Built before
  elaboration by coinduction on the call graph. Read-only during rule
  application.
- `g`, `e`, `d` — grades from `{1, proc, err, heap, heapErr}`. The
  symbols `1` and `pure` are synonymous.
- `⇒` / `⇐` — bidirectional synthesis/checking modes on the GFGL side.
- `⌊A⌋ = eraseType(A)` — erasure from Laurel `HighType` to GFGL `LowType`.
- `A`, `B` — Laurel types; `T`, `U` — GFGL types.
- `V`, `W` — GFGL values; `M`, `N` — GFGL producers.
- `D`, `D'`, `Dᵢ` — Laurel derivations; `⟦D⟧` — its elaboration.
- `[L-X]` — Laurel typing rule. `[G-X]` — GFGL typing rule.
  `[E-X]` — elaboration clause mapping a Laurel rule to a GFGL rule.
- `[T-X]` — translation rule (Python → Laurel AST).

### The judgments in play

| System       | Judgment                       | Reading                                                       |
|--------------|--------------------------------|---------------------------------------------------------------|
| Translation  | `Γ ⊢ p ↦ e`                    | Python expression `p` translates to Laurel expression `e`.    |
| Translation  | `Γ ⊢ p ↦ ss`                   | Python statement `p` translates to Laurel statement list.     |
| Laurel       | `Γ ⊢_L e : A`                  | Laurel expression `e` has type `A`.                           |
| Laurel       | `Γ ⊢_L ss`                     | Laurel statement list is well-formed (in a body of type void).|
| GFGL         | `Γ ⊢_v V ⇒ T`                  | GFGL value `V` synthesizes low type `T`.                      |
| GFGL         | `Γ ⊢_v V ⇐ T`                  | GFGL value `V` checks against `T`.                            |
| GFGL         | `Γ; g ⊢_p M ⇐ void & g`        | GFGL producer `M` checks at ambient grade `g`.                |
| Elaboration  | `⟦D⟧ = D'`                     | Laurel derivation `D` elaborates to GFGL derivation `D'`.     |

Checking a producer is always "at void" — procedures communicate
results through declared outputs, not a return value in the FGCBV
sense. The grade `g` is the object of checking.

---

## Translation Rules (Python → Laurel AST)

Translation is a deterministic fold. The rules below cover the cases
that are more than a direct syntactic copy; trivial leaf cases
(literals, identifiers) are elided. The output is a Laurel AST, not
a derivation — the derivation is obtained by checking the AST against
Laurel's rules (§Laurel Type System, below).

### Expressions

```
                                                       [T-Lit]
──────────────────────────────
Γ ⊢ n : int   ↦   LiteralInt n

                                                       [T-BinOp]
Γ ⊢ p₁ ↦ e₁     Γ ⊢ p₂ ↦ e₂
──────────────────────────────────────────────
Γ ⊢ p₁ op p₂   ↦   StaticCall (opPrelude op) [e₁, e₂]


                                                       [T-CallResolved]
lookupName(f) = some (.function sig)     resolveKwargs(f, pos, kw) = args
Γ ⊢ pᵢ ↦ eᵢ
──────────────────────────────────────────────────────────────────────
Γ ⊢ f(p₁,…,pₙ, kw=…)   ↦   StaticCall f args


                                                       [T-CallUnresolved]
lookupName(f) = none
──────────────────────────────
Γ ⊢ f(…)   ↦   Hole      (nondeterministic — args discarded)


                                                       [T-MethodCall]
resolveMethodName(recv, m) = qualified
Γ ⊢ recv ↦ e_self       Γ ⊢ pᵢ ↦ eᵢ
──────────────────────────────────────────────
Γ ⊢ recv.m(p₁,…,pₙ)   ↦   StaticCall qualified [e_self, e₁,…,eₙ]


                                                       [T-FieldRead]
Γ ⊢ recv ↦ e_obj
──────────────────────────────
Γ ⊢ recv.f   ↦   FieldSelect e_obj f


                                                       [T-FString]
Γ ⊢ pᵢ ↦ eᵢ
─────────────────────────────────────────────────────────────
Γ ⊢ f"…{p₁}…{pₙ}…"   ↦   StaticCall to_string_any [concat …]


                                                       [T-ListLit]
Γ ⊢ pᵢ ↦ eᵢ
──────────────────────────────────────────────────────────────────
Γ ⊢ [p₁,…,pₙ]   ↦   from_ListAny (ListAny_cons e₁ … (ListAny_nil))


                                                       [T-DictLit]
Γ ⊢ kᵢ ↦ Kᵢ     Γ ⊢ vᵢ ↦ Vᵢ
──────────────────────────────────────────────────────────────────
Γ ⊢ {k₁:v₁,…}   ↦   from_DictStrAny (DictStrAny_cons K₁ V₁ … empty)


                                                       [T-Subscript]
Γ ⊢ x ↦ ex     Γ ⊢ i ↦ ei
──────────────────────────────
Γ ⊢ x[i]   ↦   Any_get(ex, ei)


                                                       [T-Slice]
Γ ⊢ start ↦ es     Γ ⊢ stop ↦ et
─────────────────────────────────────────────────────────────────────
Γ ⊢ x[start:stop]   ↦   Any_get(ex, from_Slice(Any..as_int!(es),
                                                OptSome(Any..as_int!(et))))
```

### Statements

```
                                                       [T-Assign]
Γ ⊢ p ↦ e
──────────────────────────────
Γ ⊢ (x = p)   ↦   [Assign [x] e]


                                                       [T-AugAssign]
Γ ⊢ p ↦ v
──────────────────────────────
Γ ⊢ (x += p)   ↦   [Assign [x] (PAdd x v)]


                                                       [T-TupleAssign]
Γ ⊢ rhs ↦ e    fresh tmp
─────────────────────────────────────────────────────
Γ ⊢ (a,b = rhs)   ↦   [tmp := e; a := Get(tmp,0); b := Get(tmp,1)]


                                                       [T-SubscriptAssign]
Γ ⊢ i ↦ ei     Γ ⊢ v ↦ ev
─────────────────────────────────────────────────────────────────
Γ ⊢ (x[i] = v)   ↦   [Assign [x] (Any_sets (cons ei nil) x ev)]


                                                       [T-Return]
Γ ⊢ p ↦ e
────────────────────────────────────────────────────
Γ ⊢ (return p)   ↦   [LaurelResult := e; exit $body]


                                                       [T-If]
Γ ⊢ cond ↦ ec     Γ ⊢ thn ↦ sst     Γ ⊢ els ↦ ssf
──────────────────────────────────────────────────────────
Γ ⊢ if cond: thn else: els   ↦   [if ec then sst else ssf]


                                                       [T-While]
Γ ⊢ cond ↦ ec     Γ ⊢ body ↦ ssb
──────────────────────────────────────────
Γ ⊢ while cond: body   ↦   [while ec do ssb]


                                                       [T-For]
fresh x        Γ ⊢ iter ↦ ei       Γ ⊢ body ↦ ssb     fresh $brk, $cont
────────────────────────────────────────────────────────────────────────
Γ ⊢ for x in iter: body   ↦   [label $brk {
                                 label $cont {
                                   x := Hole;
                                   Assume (PIn x ei);
                                   ssb
                                 }
                               }]


                                                       [T-Break]
currentBreakLabel() = $brk
──────────────────────────
Γ ⊢ break   ↦   [exit $brk]


                                                       [T-Continue]
currentContinueLabel() = $cont
──────────────────────────
Γ ⊢ continue   ↦   [exit $cont]


                                                       [T-With]
Γ ⊢ mgr ↦ em     T = varType(mgr)     Γ ⊢ body ↦ ssb
───────────────────────────────────────────────────────────────────
Γ ⊢ with mgr as v: body   ↦   [v := T@__enter__(em); ssb; T@__exit__(em)]


                                                       [T-TryExcept]
Γ ⊢ body ↦ ssb     Γ ⊢ handlerᵢ ↦ ssᵢ    fresh $try
────────────────────────────────────────────────────────────────────
Γ ⊢ try: body except Eᵢ: handlerᵢ
   ↦ [maybe_except : Error := default;
      label $try { ssb };
      if isError(maybe_except, Eᵢ) then ssᵢ else …]


                                                       [T-Assert]
Γ ⊢ cond ↦ ec
──────────────────────────────
Γ ⊢ assert cond   ↦   [Assert ec]


                                                       [T-NewObject]
Γ ⊢ Foo ↦ class C     Γ ⊢ pᵢ ↦ eᵢ     fresh tmp
───────────────────────────────────────────────────────────
Γ ⊢ Foo(p₁,…,pₙ)   (at position v = …)
   ↦ [Assign [tmp] (New C);
      StaticCall Foo@__init__ [tmp, e₁,…,eₙ];
      Assign [v] tmp]
```

### Module and Function Declarations

```
                                                       [T-FuncDef]
Γ ⊢ params : (pᵢ : Tᵢ)          Γ ⊢ body ↦ ssb
emit mutable param copies for pᵢ mutated in body
emit scope declarations for names declared in body
declare output `maybe_except : Error`
─────────────────────────────────────────────────────────
Γ ⊢ def f(params) → R: body
   ↦ procedure f (pᵢ : Tᵢ) → (LaurelResult : R, maybe_except : Error)
     { scopeDecls; paramCopies; ssb }


                                                       [T-ClassDef]
classFields(C) = (fᵢ : Tᵢ)     Γ ⊢ methodⱼ ↦ procⱼ
──────────────────────────────────────────────────────────────
Γ ⊢ class C: …
   ↦ (typedef C { compositeFields = fᵢ : Tᵢ }, [proc₁,…,procₘ])
       — methods emitted as top-level procs with `self : C` as first param


                                                       [T-Module]
collectNestedDefs(stmts) = nested     Γ ⊢ nested ↦ procs
Γ ⊢ topLevel(stmts) ↦ ssMain
───────────────────────────────────────────────────
Γ ⊢ stmts
   ↦ Program { staticProcedures = procs ++ [ __main__ { ssMain } ] }
       — __main__ MUST carry sourceRangeToMd metadata
```

---

## Laurel Type System

Laurel has two judgments:

- `Γ ⊢_L e : A` — the Laurel AST expression `e` has type `A`.
- `Γ ⊢_L ss` — the Laurel statement list `ss` is well-formed as a
  body (void-typed, i.e. it does not compute a value).

There are no grades in Laurel. Effects are implicit; a call to an
effectful procedure is syntactically indistinguishable from a call to
a pure function at this layer. What the candidate derivation records
is just "the names exist and the types match at the surface level".
Effect information is discovered later by elaboration.

### Expression rules

```
                                                        [L-LitInt]
──────────────────────
Γ ⊢_L LiteralInt n : int

                                                        [L-LitBool]
──────────────────────────
Γ ⊢_L LiteralBool b : bool

                                                        [L-LitStr]
───────────────────────────────
Γ ⊢_L LiteralString s : str

                                                        [L-Var]
Γ(x) = .variable A
──────────────────
Γ ⊢_L Identifier x : A


                                                        [L-Call]
Γ(f) = .function (FuncSig params=(Aᵢ) ret=B)
Dᵢ :: Γ ⊢_L eᵢ : Aᵢ                       (for i = 1..n)
──────────────────────────────────────────────
Γ ⊢_L StaticCall f [e₁,…,eₙ] : B


                                                        [L-Field]
D_obj :: Γ ⊢_L e_obj : C
classFields(C) includes (f : A)
────────────────────────────────
Γ ⊢_L FieldSelect e_obj f : A


                                                        [L-Hole]
──────────────────
Γ ⊢_L Hole : Any
```

`[L-Call]` does NOT distinguish effectful from pure — the side condition
is just "there is a FuncSig in Γ". Whether that function's grade is
pure, proc, err, heap, or heapErr is a separate fact determined by
elaboration.

### Statement rules

```
                                                        [L-Nil]
──────────────
Γ ⊢_L  (empty list)


                                                        [L-Assign]
Γ(x) = .variable A        D :: Γ ⊢_L e : A
D_k :: Γ ⊢_L ss
────────────────────────────────────────────
Γ ⊢_L  (Assign [x] e) :: ss


                                                        [L-VarDecl]
D_e :: Γ ⊢_L e : A         D_k :: Γ, x:A ⊢_L ss
──────────────────────────────────────────────────
Γ ⊢_L  (LocalVariable x A (some e)) :: ss


                                                        [L-VarDeclNoInit]
D_k :: Γ, x:A ⊢_L ss
────────────────────────────────────────────────
Γ ⊢_L  (LocalVariable x A none) :: ss


                                                        [L-Assert]
D_c :: Γ ⊢_L c : bool         D_k :: Γ ⊢_L ss
────────────────────────────────────────────────
Γ ⊢_L  (Assert c) :: ss


                                                        [L-If]
D_c :: Γ ⊢_L c : bool
D_t :: Γ ⊢_L sst        D_f :: Γ ⊢_L ssf      D_k :: Γ ⊢_L ss
───────────────────────────────────────────────────────────────
Γ ⊢_L  (If c sst ssf) :: ss


                                                        [L-While]
D_c :: Γ ⊢_L c : bool       D_b :: Γ ⊢_L ssb       D_k :: Γ ⊢_L ss
─────────────────────────────────────────────────────────────────
Γ ⊢_L  (While c ssb) :: ss


                                                        [L-Label]
D_b :: Γ ⊢_L ssb       D_k :: Γ ⊢_L ss
─────────────────────────────────────
Γ ⊢_L  (LabeledBlock L ssb) :: ss


                                                        [L-Exit]
────────────────────────────
Γ ⊢_L  (Exit L) :: ss


                                                        [L-Return]
D_e :: Γ ⊢_L e : returnType
──────────────────────────────────────────
Γ ⊢_L  (Return e) :: ss          (ss dead)


                                                        [L-CallStmt]
Γ(f) = .function (FuncSig params=(Aᵢ) ret=B)
Dᵢ :: Γ ⊢_L eᵢ : Aᵢ        D_k :: Γ ⊢_L ss
─────────────────────────────────────────────────
Γ ⊢_L  (StaticCall f [e₁,…,eₙ]) :: ss


                                                        [L-AssignCall]
Γ(f) = .function (FuncSig params=(Aᵢ) ret=B)
Γ(x) = .variable U          Dᵢ :: Γ ⊢_L eᵢ : Aᵢ
D_k :: Γ ⊢_L ss
─────────────────────────────────────────────────
Γ ⊢_L  (Assign [x] (StaticCall f [e₁,…,eₙ])) :: ss


                                                        [L-New]
Γ(x) = .variable (UserDefined C)        classFields(C) defined
D_k :: Γ ⊢_L ss
────────────────────────────────────────────────
Γ ⊢_L  (Assign [x] (New C)) :: ss


                                                        [L-FieldWrite]
D_obj :: Γ ⊢_L obj : C         classFields(C) includes (f : A)
D_v   :: Γ ⊢_L v : A           D_k :: Γ ⊢_L ss
─────────────────────────────────────────────────────────────
Γ ⊢_L  (Assign [FieldSelect obj f] v) :: ss
```

Observations:

- Laurel statement rules carry a continuation derivation `D_k`. A
  Laurel derivation of a statement list is literally a nested
  structure mirroring the list: each node is a rule
  application consuming the head statement and pointing to the tail
  derivation. Elaboration exploits this directly — `⟦D_k⟧` is where
  the continuation elaborates.
- `[L-Return]` and `[L-Exit]` have `ss` dead in the sense that control
  does not reach `ss`; we leave the premise `D_k :: … ⊢_L ss` absent
  here. Elaboration similarly ignores the rest.
- `[L-Call]` and `[L-CallStmt]` share a side condition (`f` is in Γ as
  a function with matching param types). There is no effect premise,
  which is the point: Laurel does not know about effects.

---

## Elaboration: `⟦·⟧ : LaurelDeriv → GFGLDeriv`

Elaboration is defined by recursion on the Laurel derivation. Each
clause says: given a Laurel derivation whose root is a specific
`[L-X]`, produce a GFGL derivation whose root is a specific `[G-Y]`,
using recursive calls to elaborate each sub-derivation. Side
conditions involving `G` (procedure grades) and `g` (ambient grade)
live on the elaboration arrow, not on the Laurel premise.

Each elaboration clause is presented in two parts, separated by the
elaboration arrow `⇝`:

```
 ⟦·⟧
  Input Laurel derivation              (by [L-X])
  ═══════════════════════ ⇝ with side conditions on G, g, subsume, subgrade
  Output GFGL derivation               (by [G-Y])
```

Sub-derivations on each side line up: the elaboration of each Laurel
premise is exactly the premise of the GFGL conclusion (possibly after
reordering / coercion insertion, noted inline).

### GFGL value derivations

#### [E-LitInt], [E-LitBool], [E-LitStr]

```
 ⟦·⟧
  ─────────────────────── [L-LitInt]
  Γ ⊢_L LiteralInt n : int
  ══════════════════════════ ⇝
  ────────────────────── [G-LitInt]
  Γ ⊢_v litInt n ⇒ TInt
```

(analogous for [L-LitBool]/[G-LitBool], [L-LitStr]/[G-LitStr])

#### [E-Var]

```
 ⟦·⟧
  Γ(x) = .variable A
  ──────────────────────── [L-Var]
  Γ ⊢_L Identifier x : A
  ══════════════════════════════ ⇝
  ────────────────────── [G-Var]
  Γ ⊢_v var x ⇒ ⌊A⌋
```

#### [E-PureCall]

```
 ⟦·⟧
  Γ(f) = .function (params=Aᵢ, ret=B)
  Dᵢ :: Γ ⊢_L eᵢ : Aᵢ
  ──────────────────────────────────── [L-Call]
  Γ ⊢_L StaticCall f [e₁,…,eₙ] : B
  ════════════════════════════════════ ⇝ requires G(f) = 1
  ⟦Dᵢ⟧ :: Γ ⊢_v Vᵢ ⇐ Aᵢ
  ───────────────────────────────────────── [G-PureCall]
  Γ ⊢_v staticCall f [V₁,…,Vₙ] ⇒ ⌊B⌋
```

Each `⟦Dᵢ⟧` is a recursive elaboration of the corresponding Laurel
sub-derivation `Dᵢ`, fed through the subsumption clause [E-Sub] below
to shift into checking mode. Applicability of [E-PureCall] **requires
`G(f) = 1`**; if the grade is higher, this [L-Call] derivation only
elaborates at statement position via [E-CallStmt] / [E-AssignCall].

#### [E-FieldRead]

```
 ⟦·⟧
  D_obj :: Γ ⊢_L e_obj : C
  classFields(C) includes (f : A)
  ────────────────────────────── [L-Field]
  Γ ⊢_L FieldSelect e_obj f : A
  ════════════════════════════════════ ⇝ let Bconstr = boxDestructor(A)
  ⟦D_obj⟧ :: Γ ⊢_v V_obj ⇒ T_obj       (then coerced to Composite)
  ────────────────────────────────────────────────────────────────────── [G-FieldRead]
  Γ ⊢_v Bconstr(readField($heap, sub(V_obj, Composite), C.f)) ⇒ ⌊A⌋
```

#### [E-Hole]

```
 ⟦·⟧
  ───────────────── [L-Hole]
  Γ ⊢_L Hole : Any
  ═══════════════════ ⇝ fresh $havoc_N or $hole_N (extends Γ)
  ──────────────────────── [G-HoleValue]
  Γ ⊢_v $havoc_N() ⇒ Any
```

#### [E-Sub] (mode switch)

Whenever a value derivation in synthesis mode is consumed in a
checking context, a subsumption witness is inserted. This is the only
"rule" that is not a direct Laurel→GFGL mapping — it is how
elaboration weaves the bidirectional check into GFGL.

```
 [E-Sub]
  ⟦D⟧ :: Γ ⊢_v V ⇒ T     subsume(T, ⌊A⌋) = c
  ──────────────────────────────────────────────
  Γ ⊢_v c(V) ⇐ A
```

`c = refl` ⇒ `c(V) = V`. Otherwise `c` is proof-relevant GFGL term
structure (`from_int`, `Any..as_int!`, …).

### GFGL producer derivations

Each Laurel statement rule has a head statement and a continuation
`ss`. Elaboration threads the continuation derivation directly: the
elaboration of `D_k :: Γ ⊢_L ss` is a GFGL derivation `⟦D_k⟧` that
occupies the `after`-slot (or body-slot) of the GFGL producer
constructor. No duplication.

All producer elaborations have the shape
`⟦D⟧ :: Γ; g ⊢_p M ⇐ void & g`.

#### [E-If]

```
 ⟦·⟧
  D_c :: Γ ⊢_L c : bool
  D_t :: Γ ⊢_L sst        D_f :: Γ ⊢_L ssf      D_k :: Γ ⊢_L ss
  ─────────────────────────────────────────────────────────────── [L-If]
  Γ ⊢_L (If c sst ssf) :: ss
  ═══════════════════════════════════════════════════════════════════ ⇝
  ⟦D_c⟧ :: Γ ⊢_v V ⇐ bool
  ⟦D_t⟧ :: Γ; g ⊢_p M_t ⇐ void & g    ⟦D_f⟧ :: Γ; g ⊢_p M_f ⇐ void & g
  ⟦D_k⟧ :: Γ; g ⊢_p M_k ⇐ void & g
  ─────────────────────────────────────────────────────────────────── [G-If]
  Γ; g ⊢_p ifThenElse V M_t M_f M_k ⇐ void & g
```

#### [E-While]

```
 ⟦·⟧
  D_c :: Γ ⊢_L c : bool
  D_b :: Γ ⊢_L ssb                D_k :: Γ ⊢_L ss
  ───────────────────────────────────────────────── [L-While]
  Γ ⊢_L (While c ssb) :: ss
  ═══════════════════════════════════════════════════════ ⇝
  ⟦D_c⟧ :: Γ ⊢_v V ⇐ bool
  ⟦D_b⟧ :: Γ; g ⊢_p M_b ⇐ void & g
  ⟦D_k⟧ :: Γ; g ⊢_p M_k ⇐ void & g
  ─────────────────────────────────────────── [G-While]
  Γ; g ⊢_p whileLoop V M_b M_k ⇐ void & g
```

#### [E-LabeledBlock], [E-Exit]

```
 ⟦·⟧
  D_b :: Γ ⊢_L ssb        D_k :: Γ ⊢_L ss
  ───────────────────────────────────────── [L-Label]
  Γ ⊢_L (LabeledBlock L ssb) :: ss
  ═════════════════════════════════════════════ ⇝
  ⟦D_b⟧ :: Γ; g ⊢_p M_b ⇐ void & g
  ⟦D_k⟧ :: Γ; g ⊢_p M_k ⇐ void & g
  ────────────────────────────────────────── [G-Label]
  Γ; g ⊢_p labeledBlock L M_b M_k ⇐ void & g


 ⟦·⟧
  ───────────────────────────── [L-Exit]
  Γ ⊢_L (Exit L) :: ss
  ═══════════════════════════════════ ⇝
  ──────────────────────── [G-Exit]
  Γ; g ⊢_p exit L ⇐ void & g
```

#### [E-Return]

```
 ⟦·⟧
  D_e :: Γ ⊢_L e : returnType
  ─────────────────────────────── [L-Return]
  Γ ⊢_L (Return e) :: ss
  ═══════════════════════════════════════ ⇝
  ⟦D_e⟧ :: Γ ⊢_v V ⇐ returnType
  ───────────────────────────────── [G-Return]
  Γ; g ⊢_p returnValue V ⇐ void & g
```

#### [E-Assert]

```
 ⟦·⟧
  D_c :: Γ ⊢_L c : bool        D_k :: Γ ⊢_L ss
  ───────────────────────────────────────────── [L-Assert]
  Γ ⊢_L (Assert c) :: ss
  ════════════════════════════════════════════════ ⇝
  ⟦D_c⟧ :: Γ ⊢_v V ⇐ bool       ⟦D_k⟧ :: Γ; g ⊢_p M_k ⇐ void & g
  ──────────────────────────────────────────────────────────────── [G-Assert]
  Γ; g ⊢_p assert V M_k ⇐ void & g
```

#### [E-VarDecl], [E-VarDeclNoInit]

```
 ⟦·⟧
  D_e :: Γ ⊢_L e : A        D_k :: Γ, x:A ⊢_L ss
  ───────────────────────────────────────────────── [L-VarDecl]
  Γ ⊢_L (LocalVariable x A (some e)) :: ss
  ═════════════════════════════════════════════════════ ⇝
  ⟦D_e⟧ :: Γ ⊢_v V ⇐ A        ⟦D_k⟧ :: Γ, x:⌊A⌋; g ⊢_p M_k ⇐ void & g
  ─────────────────────────────────────────────────────────────────── [G-VarDecl]
  Γ, x:⌊A⌋; g ⊢_p varDecl x ⌊A⌋ V M_k ⇐ void & g


 ⟦·⟧
  D_k :: Γ, x:A ⊢_L ss
  ───────────────────────────────────────────────── [L-VarDeclNoInit]
  Γ ⊢_L (LocalVariable x A none) :: ss
  ═════════════════════════════════════════════════════ ⇝
  ⟦D_k⟧ :: Γ, x:⌊A⌋; g ⊢_p M_k ⇐ void & g
  ─────────────────────────────────────────────────────────── [G-VarDecl]
  Γ, x:⌊A⌋; g ⊢_p varDecl x ⌊A⌋ none M_k ⇐ void & g
```

#### [E-AssignPure]

Applicable when the Laurel [L-Assign] derivation elaborates an
expression whose elaboration is a *value*, i.e. [E-PureCall] applies
(or `e` is a literal / identifier / field read). Concretely: this is
the branch where `synthExpr` returns `.value`.

```
 ⟦·⟧
  Γ(x) = .variable A      D_e :: Γ ⊢_L e : A
  D_k :: Γ ⊢_L ss
  ─────────────────────────────────────────── [L-Assign]
  Γ ⊢_L (Assign [x] e) :: ss
  ════════════════════════════════════════════════ ⇝ requires ⟦D_e⟧ is a value
  ⟦D_e⟧ :: Γ ⊢_v V ⇐ A       ⟦D_k⟧ :: Γ; g ⊢_p M_k ⇐ void & g
  ──────────────────────────────────────────────────────────── [G-Assign]
  Γ; g ⊢_p assign x V M_k ⇐ void & g
```

#### [E-CallStmt]

Statement-level effectful call (no assignment target). The elaboration
dispatches on `subgrade(d, g)` to pick the convention witness `conv`,
which in turn selects the GFGL rule variant.

```
 ⟦·⟧
  Γ(f) = .function (params=Aᵢ, ret=B)
  Dᵢ :: Γ ⊢_L eᵢ : Aᵢ           D_k :: Γ ⊢_L ss
  ────────────────────────────────────────────────── [L-CallStmt]
  Γ ⊢_L (StaticCall f [e₁,…,eₙ]) :: ss
  ══════════════════════════════════════════════════════ ⇝
      requires G(f) = d, d ≠ 1, subgrade(d, g) = some conv,
               outputs(f) = [y₁:C₁,…,yₖ:Cₖ]
  ⟦Dᵢ⟧ :: Γ ⊢_v Vᵢ ⇐ Aᵢ              (each Vᵢ possibly from [E-Lift])
  ⟦D_k⟧ :: Γ, y₁:⌊C₁⌋,…,yₖ:⌊Cₖ⌋; g ⊢_p M_k ⇐ void & g
  ────────────────────────────────────────────────────── [G-EffectfulCall[conv]]
  Γ; g ⊢_p effectfulCall[conv] f [Vᵢ] [yⱼ:⌊Cⱼ⌋] M_k ⇐ void & g
```

The convention witness `conv` determines whether `$heap` is prepended
to the argument list; outputs always come from `outputs(f)` (see
Invariant 2).

If any `eᵢ` is itself a [L-Call] with `G(·) > 1`, its sub-derivation
`Dᵢ` is not a value-position derivation — [E-PureCall] rejects it.
Such `Dᵢ` triggers [E-Lift], which inserts an extra `effectfulCall`
around everything that follows.

#### [E-AssignCall]

```
 ⟦·⟧
  Γ(f) = .function (params=Aᵢ, ret=B)       Γ(x) = .variable U
  Dᵢ :: Γ ⊢_L eᵢ : Aᵢ          D_k :: Γ ⊢_L ss
  ───────────────────────────────────────────────────────── [L-AssignCall]
  Γ ⊢_L (Assign [x] (StaticCall f [e₁,…,eₙ])) :: ss
  ═════════════════════════════════════════════════════════════ ⇝
      requires G(f) = d, d ≠ 1, subgrade(d, g) = some conv,
               outputs(f) = [r:B, …], subsume(B, ⌊U⌋) = c
  ⟦Dᵢ⟧ :: Γ ⊢_v Vᵢ ⇐ Aᵢ
  ⟦D_k⟧ :: Γ, r:⌊B⌋, …; g ⊢_p M_k ⇐ void & g
  ─────────────────────────────────────────────────────────────────── [G-EffectfulCallThenAssign]
  Γ; g ⊢_p effectfulCall[conv] f [Vᵢ] [r:⌊B⌋, …]
              (assign x c(r) M_k) ⇐ void & g
```

#### [E-Lift] (the FGCBV "to" rule, at argument position)

An argument derivation `Dⱼ :: Γ ⊢_L eⱼ : Aⱼ` whose elaboration would
require [E-PureCall] but whose callee has `G(·) > 1` cannot produce a
GFGL value. Elaboration instead expands the enclosing producer
derivation by inserting an `effectfulCall` that binds a fresh
variable, and elaborates the remainder under the extended Γ.

```
 [E-Lift]
   Consider an enclosing elaboration whose GFGL conclusion has the form
     Γ; g ⊢_p K(…Vⱼ…) ⇐ void & g
   where Vⱼ is needed as the j-th argument of an outer construct, but
   the Laurel sub-derivation Dⱼ has root [L-Call] with callee g′
   satisfying G(g′) = d₁ ≠ 1.

   Elaborate Dⱼ's arguments first:  ⟦Dⱼ,ᵢ⟧ :: Γ ⊢_v Wᵢ ⇐ A'ᵢ
   Let outputs(g′) = [r:B₁,…]; choose subgrade(d₁, g) = some conv₁.

   Then replace the enclosing elaboration's conclusion
     Γ; g ⊢_p K(…Vⱼ…) ⇐ void & g
   by
     Γ; g ⊢_p effectfulCall[conv₁] g′ [Wᵢ] [r:⌊B₁⌋,…] K(…r…) ⇐ void & g
   where the continuation K is re-elaborated under Γ, r:⌊B₁⌋, … with
   Vⱼ replaced by (the coercion of) `r`.
```

This is the one case where the shape of the GFGL derivation is *not*
a direct image of the Laurel derivation: the tree grows an extra
node. The extra node is how GFGL expresses "evaluate `g′(…)` first,
bind its result, then the outer operation". Laurel had no way to
express this explicitly (Laurel permitted nested calls syntactically);
GFGL insists on it.

Implementationally, [E-Lift] is `checkArgsK`.

#### [E-New]

```
 ⟦·⟧
  Γ(x) = .variable (UserDefined C)     D_k :: Γ ⊢_L ss
  ────────────────────────────────────────────────────── [L-New]
  Γ ⊢_L (Assign [x] (New C)) :: ss
  ══════════════════════════════════════════════════════════ ⇝ requires heap ≤ g
  ⟦D_k⟧ :: Γ, $h:Heap; g ⊢_p M_k ⇐ void & g
  ─────────────────────────────────────────────────────────────────────────────── [G-New]
  Γ, $h:Heap; g ⊢_p
      varDecl $h Heap (increment $heap)
        (assign x MkComposite(Heap..nextReference!($h), TypeTag_C) M_k)
      ⇐ void & g
```

Side condition `heap ≤ g` is the grade check on the elaboration arrow.
If it fails, the current attempt at grade `g` fails, and the
coinductive pass bumps `g`.

#### [E-FieldWrite]

```
 ⟦·⟧
  D_obj :: Γ ⊢_L obj : C           classFields(C) includes (f : A)
  D_v   :: Γ ⊢_L v : A             D_k :: Γ ⊢_L ss
  ──────────────────────────────────────────────────────────────── [L-FieldWrite]
  Γ ⊢_L (Assign [FieldSelect obj f] v) :: ss
  ════════════════════════════════════════════════════════════════════ ⇝
      requires heap ≤ g, let Bconstr = boxConstructor(A)
  ⟦D_obj⟧ :: Γ ⊢_v V_obj ⇐ Composite        ⟦D_v⟧ :: Γ ⊢_v V ⇐ A
  ⟦D_k⟧ :: Γ, $h:Heap; g ⊢_p M_k ⇐ void & g
  ─────────────────────────────────────────────────────────────────── [G-FieldWrite]
  Γ, $h:Heap; g ⊢_p
      varDecl $h Heap (updateField($heap, V_obj, C.f, Bconstr(V)))
        M_k
      ⇐ void & g
```

### Procedure entry

```
 [E-Proc]
  D_body :: Γ, params ⊢_L body
  ──────────────────────────────────────────── [L-Proc]
  procedure f(params) → returnType  { body }
  ═════════════════════════════════════════════ ⇝
      let g = discoverGrade(f)          (coinductive fixpoint, see below)
      ⟦D_body⟧ :: Γ, params; g ⊢_p M ⇐ void & g
  if g ∈ {heap, heapErr}, rewrite the signature:
    inputs      := $heap_in :: inputs
    outputs     := $heap :: outputs
    body        := $heap := $heap_in; M
```

`discoverGrade(f)` is defined by the fixed-point procedure in
ARCHITECTURE.md §Grade Inference: try grades `[pure, proc, err, heap,
heapErr]` and take the smallest `g` at which `⟦D_body⟧` exists. "Does
not exist" = some sub-clause's side condition failed (`subgrade`
returns `none`, `heap ≤ g` fails, etc.). Because the grade lattice is
finite and monotone, the fixpoint converges.

### Subsumption table (reference)

Reproduced from ARCHITECTURE.md for self-containment.

```lean
inductive CoercionResult where
  | refl
  | coerce (w : Md → FGLValue → FGLValue)
  | unrelated

def subsume (actual expected : LowType) : CoercionResult :=
  if actual == expected then .refl else match actual, expected with
  | .TInt, .TCore "Any"              => .coerce fromInt
  | .TBool, .TCore "Any"             => .coerce fromBool
  | .TString, .TCore "Any"           => .coerce fromStr
  | .TFloat64, .TCore "Any"          => .coerce fromFloat
  | .TCore "Composite", .TCore "Any" => .coerce fromComposite
  | .TCore "ListAny", .TCore "Any"   => .coerce fromListAny
  | .TCore "DictStrAny", .TCore "Any"=> .coerce fromDictStrAny
  | .TVoid, .TCore "Any"             => .coerce fromNone
  | .TCore "Any", .TBool             => .coerce (Any_to_bool)
  | .TCore "Any", .TInt              => .coerce (Any..as_int!)
  | .TCore "Any", .TString           => .coerce (Any..as_string!)
  | .TCore "Any", .TFloat64          => .coerce (Any..as_float!)
  | .TCore "Any", .TCore "Composite" => .coerce (Any..as_Composite!)
  | _, _                             => .unrelated
```

### Subgrade table (reference)

```lean
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

`subgrade` is the proof witness for `d ≤ g` in the call rules. A return
of `none` at grade `g` fails the current checking attempt, which is the
signal the coinductive pass uses to bump the grade.

---

## Rule → Implementation Mapping

### Translation

| Rule              | Lean function                                   | File                              |
|-------------------|-------------------------------------------------|-----------------------------------|
| [T-Lit], [T-BinOp]| `translateExpr` leaf cases                      | `Strata/Languages/Python/Translation.lean` |
| [T-CallResolved]  | `translateCall` → `resolveKwargs` + StaticCall  | same                              |
| [T-CallUnresolved]| `translateCall` no-sig branch → `.Hole`         | same                              |
| [T-MethodCall]    | `resolveMethodName` + `translateCall`           | same                              |
| [T-FieldRead]     | `translateExpr` (Attribute in expression pos.)  | same                              |
| [T-FString]       | `translateExpr` (JoinedStr case)                | same                              |
| [T-ListLit]       | `translateExpr` (List case)                     | same                              |
| [T-DictLit]       | `translateExpr` (Dict case)                     | same                              |
| [T-Subscript]     | `translateExpr` (Subscript case)                | same                              |
| [T-Slice]         | `translateExpr` + `from_Slice` constructor      | same                              |
| [T-Assign]        | `translateAssignSingle`                         | same                              |
| [T-AugAssign]     | `translateStmt` (AugAssign)                     | same                              |
| [T-TupleAssign]   | `unpackTargets`                                 | same                              |
| [T-SubscriptAssign] | `translateAssignSingle` (Subscript target)    | same                              |
| [T-Return]        | `translateStmt` (Return case)                   | same                              |
| [T-If]/[T-While]  | `translateStmt` (If/While cases)                | same                              |
| [T-For]           | `translateStmt` (For case) + `pushLoopLabel`    | same                              |
| [T-Break]/[T-Continue] | `currentBreakLabel` / `currentContinueLabel` | same                          |
| [T-With]          | `translateStmt` (With case)                     | same                              |
| [T-TryExcept]     | `translateTryExcept`                            | same                              |
| [T-Assert]        | `translateStmt` (Assert case)                   | same                              |
| [T-NewObject]     | `translateCall` (class-callee branch)           | same                              |
| [T-FuncDef]       | `translateFunction` + `emitScopeDeclarations` + `emitMutableParamCopies` | same |
| [T-ClassDef]      | `translateClass`                                | same                              |
| [T-Module]        | `translateModule` + `collectNestedDefs`         | same                              |

### Laurel type system (candidate-derivation checking)

The Laurel rules `[L-*]` are not implemented as an explicit pass in
Lean; they are the implicit typing discipline that Translation targets
and Elaboration relies on. They are realized by two facts:

- Translation preserves the Laurel-AST invariants needed for each
  `[L-X]`'s side conditions (e.g. `Γ(f) = .function sig` whenever a
  `StaticCall f …` is emitted — see the Illegal-States-Unrepresentable
  principle in ARCHITECTURE.md).
- Elaboration's dispatch on AST shape (`synthValue`, `synthExpr`,
  `checkProducer`) pattern-matches exactly the same cases as `[L-X]`.
  If an AST node does not match any `[L-X]`, elaboration falls through
  to a `Hole` emission (matching `[L-Hole]`).

### Elaboration

| Clause                 | Lean function                                     | File |
|------------------------|---------------------------------------------------|------|
| `Γ ⊢_v V ⇒ T`          | `synthValue`                                      | `Strata/Languages/FineGrainLaurel/Elaborate.lean` |
| `Γ ⊢_v V ⇐ T`          | `checkValue`                                      | same |
| `Γ; g ⊢_p M ⇐ void & g`| `checkProducer` (threads `ss` as continuation)    | same |
| [E-LitInt]/[E-LitBool]/[E-LitStr] | `synthValue` leaf cases                | same |
| [E-Var]                | `synthValue` (Identifier case)                    | same |
| [E-PureCall]           | `synthValue` / `synthExpr` (StaticCall pure branch) | same |
| [E-FieldRead]          | `synthValue` (FieldSelect case) + `boxDestructorName` | same |
| [E-Hole]               | `synthValue` (Hole case)                          | same |
| [E-Sub]                | `subsume` + `applySubsume`                        | same |
| [E-If]                 | `checkProducer` (If case)                         | same |
| [E-While]              | `checkProducer` (While case)                      | same |
| [E-LabeledBlock]/[E-Exit] | `checkProducer` (LabeledBlock / Exit cases)    | same |
| [E-Return]             | `checkProducer` (Return case)                     | same |
| [E-Assert]             | `checkProducer` (Assert case)                     | same |
| [E-VarDecl]/[E-VarDeclNoInit] | `checkProducer` (LocalVariable case) → `mkVarDecl` | same |
| [E-AssignPure]         | `checkAssign` (pure branch)                       | same |
| [E-CallStmt]           | `checkProducer` (StaticCall branch) → `mkGradedCall` | same |
| [E-AssignCall]         | `checkAssign` (call branch) → `mkGradedCall` + inner `assign` | same |
| [E-Lift]               | `checkArgsK`                                      | same |
| [E-New]                | `checkAssign` (New case)                          | same |
| [E-FieldWrite]         | `checkAssign` (FieldSelect target case)           | same |
| [E-Proc]               | `fullElaborate` + `discoverGrades` + `tryGrades`  | same |
| `subgrade(d, g)`       | `subgrade`                                        | same |
| `subsume(T, U)`        | `subsume`                                         | same |
| `G(f)` lookup          | reader read of `procGrades`                       | same |

### Projection

| Form                                     | Lean function                                  |
|------------------------------------------|-------------------------------------------------|
| GFGL value → Laurel expression           | `projectValue`                                  |
| GFGL producer → Laurel statement list    | `projectProducer`                               |
| Procedure body                           | `projectBody`                                   |

---

## Invariants Maintained by the Rules

1. **Elaboration is recursion on the Laurel derivation.** Every sub-
   derivation of the input appears (possibly coerced, possibly with an
   [E-Lift] node wrapped around the surrounding producer) as a sub-
   derivation of the output. No Laurel sub-derivation is dropped or
   duplicated (except that [E-Return]/[E-Exit] discard the dead
   continuation, which is sound because control cannot reach it).

2. **Outputs come from signatures, not grades.** Every rule that
   produces an `effectfulCall` gets its output list from `outputs(f)`
   — the callee's declared outputs — via `lookupProcOutputs`. The
   grade only decides whether `$heap` is prepended to the args.

3. **Laurel rules have no grade premises.** Grades appear only on the
   elaboration arrow, never inside a Laurel derivation. This is what
   makes the Laurel derivation "ill-typed in a benign way": it is
   missing the effect information that elaboration supplies.

4. **`Γ` grows only through binders.** Calls extend `Γ` with their
   output variables; `LocalVariable` extends with `x`; `New` extends
   with `$h`. No clause silently invents names without extending `Γ`.

5. **[E-Lift] is the only clause that does not preserve tree shape.**
   Every other clause maps `[L-X]` with sub-derivations `D₁,…,Dₖ`
   to `[G-Y]` with sub-derivations `⟦D₁⟧,…,⟦Dₖ⟧` in the same order.
   [E-Lift] inserts an extra `[G-EffectfulCall]` node. This is
   unavoidable: Laurel admits `f(g(x))` as a single expression when
   `g` is effectful; GFGL forces the nesting to be named.

---

## References

- Levy, 2003. *Call-By-Push-Value.*
- Egger, Møgelberg, Staton, 2014. "Linear Usage of State."
- McDermott, 2025. "Grading call-by-push-value."
- Dunfield & Krishnaswami, 2021. "Bidirectional Typing."
- Gaboardi et al., 2016. "Combining Effects and Coeffects via Grading."
