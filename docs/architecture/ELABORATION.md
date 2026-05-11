# Translation and Elaboration: Rules

---

## Purpose

This document gives a single, coherent presentation of the rules that
drive the two main passes of the pipeline:

- **Translation** — Python AST → Laurel AST.
- **Elaboration** — Laurel AST → GFGL derivation.

It is companion material to `ARCHITECTURE.md`. The prose overview and
engineering principles live there; the rules live here.

### Why a separate document

The previous presentation inside `ARCHITECTURE.md` framed elaboration as
a map `D :: Γ ⊢_L e : A  ↦  ⟦D⟧ :: Γ' ⊢_G …` — a translation on Laurel
typing derivations. This is not quite right:

- Laurel has no grades. Side conditions like `grade(f) = pure` or
  `grade(f) = d > pure, d ≤ e` are not part of any Laurel judgment;
  they consult `procGrades` from the environment and refer to the
  *output* ambient grade `e`.
- Several "Laurel" premises on the LHS are untypable as stated.
  The to-rule premise "argument `eᵢ` has grade `dᵢ > pure`" is not a
  Laurel judgment at all — Laurel's statement/expression split already
  forbids nesting effectful calls inside expressions. The Laurel AST
  that reaches elaboration is the *literal output of Translation*, not
  an arbitrary well-typed Laurel derivation.
- `(x := new C); rest : void` with the side condition `heap ≤ e` only
  makes sense once we know the GFGL ambient grade — again, not a
  Laurel-side fact.

The correct framing is: elaboration pattern-matches on the **Laurel
AST** (source, not a derivation), consults Γ and `procGrades`, and
produces a **GFGL typing derivation**. The Laurel AST is just syntax.
The only typing derivation is the one elaboration *builds*.

### Notation conventions

- `Γ` — typing environment from Resolution. Maps names to `NameInfo`.
- `G` — grade environment, `procGrades : name → Grade`. Built before
  elaboration by coinduction on the call graph. Read-only during rule
  application.
- `g`, `e`, `d` — grades from `{1, proc, err, heap, heapErr}`. The
  symbols `1` and `pure` are synonymous.
- `⇒` (synthesize) and `⇐` (check) — bidirectional modes.
- `⇝` — elaboration. Read `e ⇝ V ⇒ A` as "the Laurel expression `e`
  elaborates to GFGL value `V` synthesizing type `A`".
- `A`, `B` — Laurel `HighType`; `T`, `U` — GFGL `LowType`.
  `⌊A⌋ = eraseType(A)` is the erasure from `HighType` to `LowType`.
- `V`, `W` — GFGL values. `M`, `N` — GFGL producers.
- `s` — Laurel statement. `ss` — Laurel statement list (the
  continuation / "rest").
- Premises above the bar, conclusion below. Rule names in brackets.
  Rules that elaborate a piece of Laurel AST are **Elaboration**;
  rules that desugar a piece of Python AST are **Translation**.

### The two judgments of elaboration

| Form                        | Reading                                                                |
|-----------------------------|-------------------------------------------------------------------------|
| `Γ; G ⊢ e ⇝ V ⇒ T`          | The Laurel value-position expression `e` elaborates to GFGL value `V` synthesizing `T`. |
| `Γ; G ⊢ e ⇝ V ⇐ A`          | `e` elaborates to `V`, which fits expected type `A` (after coercion).  |
| `Γ; G; g ⊢ s ; ss ⇝ M ⇐ void & g` | The Laurel statement `s` followed by the continuation `ss`, checked at ambient grade `g`, elaborates to GFGL producer `M`. |

Checking a producer is always "at void" — procedures communicate
results through declared outputs, not a return value in the FGCBV
sense. The grade `g` is the object of checking.

### The single judgment of translation

Translation has no grades and no modes. One judgment:

| Form              | Reading                                                         |
|-------------------|------------------------------------------------------------------|
| `Γ ⊢ p ↦ e`       | The Python expression `p` translates to the Laurel expression `e`. |
| `Γ ⊢ p ↦ ss`      | The Python statement `p` translates to a Laurel statement list. |

`Γ` here is `TypeEnv`, the same structure Resolution builds. Translation
never reads grades.

---

## Translation Rules (Python → Laurel)

Translation is a deterministic fold. The rules below cover the cases
that are more than direct syntactic copy; trivial leaf cases (literals,
identifiers) are elided.

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
```

**Object construction** (class instantiation) is a statement-level
desugaring; see [T-NewObject] below.

```
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

## Elaboration Rules (Laurel AST → GFGL derivation)

The Laurel terms in premises are AST, *not* Laurel typing derivations.
Types come from Γ (Resolution). Grades come from `G` (coinduction output).

### Synthesis: `Γ; G ⊢ e ⇝ V ⇒ T`

```
                                             [E-LitInt]
──────────────────────────────────────
Γ; G ⊢ LiteralInt n   ⇝   litInt n ⇒ TInt

                                             [E-LitBool]
──────────────────────────────────────
Γ; G ⊢ LiteralBool b   ⇝   litBool b ⇒ TBool

                                             [E-LitStr]
──────────────────────────────────────
Γ; G ⊢ LiteralString s   ⇝   litStr s ⇒ TString


                                             [E-Var]
Γ(x) = A
──────────────────────────────────────
Γ; G ⊢ Identifier x   ⇝   var x ⇒ ⌊A⌋


                                             [E-PureCall]
Γ(f) = FuncSig(params=Aᵢ, returnType=B)     G(f) = 1
Γ; G ⊢ eᵢ ⇝ Vᵢ ⇐ Aᵢ
────────────────────────────────────────────────────────────────
Γ; G ⊢ StaticCall f [e₁,…,eₙ]   ⇝   staticCall f [V₁,…,Vₙ] ⇒ ⌊B⌋


                                             [E-FieldRead]
Γ; G ⊢ e_obj ⇝ V_obj ⇒ T_obj
fieldType(class, f) = A               Bconstr = boxDestructor(A)
─────────────────────────────────────────────────────────────────────────
Γ; G ⊢ FieldSelect e_obj f
      ⇝   Bconstr(readField($heap, sub(V_obj, Composite), ClassName.f)) ⇒ ⌊A⌋


                                             [E-HoleValue]
──────────────────────────────────────────
Γ; G ⊢ ??   ⇝   $havoc_N() ⇒ Any           (fresh $havoc_N; Γ extended)

                                             [E-HoleValue-Det]
──────────────────────────────────────────
Γ; G ⊢ ?    ⇝   $hole_N() ⇒ Any            (fresh $hole_N; Γ extended)
```

### Checking a value: `Γ; G ⊢ e ⇝ V ⇐ A`

One rule, the subsumption (mode-switch) rule:

```
                                             [E-Sub]
Γ; G ⊢ e ⇝ V ⇒ T       subsume(T, ⌊A⌋) = c
──────────────────────────────────────────────
Γ; G ⊢ e ⇝ c(V) ⇐ A
```

`subsume` is defined in §Subsumption Table below. When `c = refl`, the
result is just `V`; the coercion is proof-relevant and becomes GFGL term
structure (`from_int`, `Any..as_int!`, etc.).

### Producer checking: `Γ; G; g ⊢ s ; ss ⇝ M ⇐ void & g`

All producer rules take both the current statement `s` and the
continuation `ss` (the statements after `s` in the same block). This
is the standard FGCBV "continuation-passing" shape that threads the
rest of the block into the producer being built; the continuation is
elaborated exactly once.

#### Control-flow statements

```
                                             [E-If]
Γ; G ⊢ c ⇝ V ⇐ bool
Γ; G; g ⊢ thn ; [] ⇝ M_t     Γ; G; g ⊢ els ; [] ⇝ M_f
Γ; G; g ⊢ ss ⇝ M_k
───────────────────────────────────────────────────────────
Γ; G; g ⊢ (if c then thn else els) ; ss
         ⇝ ifThenElse V M_t M_f M_k


                                             [E-While]
Γ; G ⊢ c ⇝ V ⇐ bool
Γ; G; g ⊢ body ; [] ⇝ M_b
Γ; G; g ⊢ ss ⇝ M_k
───────────────────────────────────────────────────────────
Γ; G; g ⊢ (while c do body) ; ss
         ⇝ whileLoop V M_b M_k


                                             [E-LabeledBlock]
Γ; G; g ⊢ body ; [] ⇝ M_b
Γ; G; g ⊢ ss ⇝ M_k
───────────────────────────────────────────────────────────
Γ; G; g ⊢ (label L { body }) ; ss
         ⇝ labeledBlock L M_b M_k


                                             [E-Exit]
──────────────────────────────────────
Γ; G; g ⊢ (exit L) ; ss  ⇝  exit L


                                             [E-Return]
Γ; G ⊢ e ⇝ V ⇐ returnType
──────────────────────────────────────
Γ; G; g ⊢ (return e) ; ss  ⇝  returnValue V


                                             [E-Assert]
Γ; G ⊢ c ⇝ V ⇐ bool       Γ; G; g ⊢ ss ⇝ M_k
──────────────────────────────────────────────────
Γ; G; g ⊢ (assert c) ; ss  ⇝  assert V M_k
```

Note: `ss` is dead after `return` and after `exit`, so those rules
ignore it. This matches the source semantics and keeps the GFGL
derivation well-formed.

#### Variable declarations and pure assignments

```
                                             [E-VarDecl]
Γ; G ⊢ e ⇝ V ⇐ A           Γ, x:⌊A⌋; G; g ⊢ ss ⇝ M_k
─────────────────────────────────────────────────────────
Γ; G; g ⊢ (var x:A := e) ; ss
         ⇝ varDecl x ⌊A⌋ V M_k


                                             [E-VarDecl-Hole]
Γ, x:Any; G; g ⊢ ss ⇝ M_k
─────────────────────────────────────────
Γ; G; g ⊢ (var x := ??) ; ss
         ⇝ varDecl x Any none M_k


                                             [E-AssignPure]
Γ(x) = B        isPure(e)        Γ; G ⊢ e ⇝ V ⇐ B
Γ; G; g ⊢ ss ⇝ M_k
─────────────────────────────────────────────────────────
Γ; G; g ⊢ (Assign [x] e) ; ss  ⇝  assign x V M_k
```

`isPure(e)` ≡ the head of `e` is a literal, identifier, pure call, or
field read of a pure chain — i.e., `synthExpr(e)` returns a value, not a
call. When `e` is an effectful call, use [E-AssignCall] below.

#### Effectful calls (the producer path)

The key point: effectful calls never appear inside a value. Every call
with grade `d > 1` is pulled out to statement level by these rules.

```
                                             [E-Call]
Γ(f) = FuncSig(params=Aᵢ, returnType=B)     G(f) = d
subgrade(d, g) = conv        d ≠ 1
outputs(f) = [y₁:C₁, …, yₖ:Cₖ]
Γ; G ⊢ eᵢ ⇝ Vᵢ ⇐ Aᵢ          (lifted via [E-Lift] if any eᵢ has grade > 1)
Γ, y₁:C₁,…,yₖ:Cₖ; G; g ⊢ ss ⇝ M_k
────────────────────────────────────────────────────────────────────────
Γ; G; g ⊢ (StaticCall f [e₁,…,eₙ]) ; ss
         ⇝ mkGradedCall[conv] f [Vᵢ] [yⱼ:Cⱼ] M_k


                                             [E-AssignCall]
Γ(f) = FuncSig(params=Aᵢ, returnType=B)     G(f) = d ≠ 1
subgrade(d, g) = conv        Γ(x) = U
outputs(f) = [r:B, …]        Γ; G ⊢ eᵢ ⇝ Vᵢ ⇐ Aᵢ
subsume(B, U) = c            Γ, r:B, …; G; g ⊢ ss ⇝ M_k
────────────────────────────────────────────────────────────────────────
Γ; G; g ⊢ (Assign [x] (StaticCall f [e₁,…,eₙ])) ; ss
         ⇝ mkGradedCall[conv] f [Vᵢ] [r:B, …] (assign x c(r) M_k)
```

`mkGradedCall[conv]` dispatches on the `ConventionWitness` (§Subgrading
Witness in ARCHITECTURE.md):

| `conv`          | GFGL construct built                                                        |
|-----------------|-----------------------------------------------------------------------------|
| `pureCall`      | never produced here (handled by [E-PureCall])                                |
| `procCall`      | `effectfulCall f Vs outputs body`                                           |
| `errorCall`     | `effectfulCall f Vs outputs body`                                           |
| `heapCall`      | `effectfulCall f (heapVar :: Vs) outputs body` — outputs include heap       |
| `heapErrorCall` | `effectfulCall f (heapVar :: Vs) outputs body` — outputs include heap+err   |

The outputs `[yⱼ:Cⱼ]` come from the callee's declared signature
(prelude, runtime, or rewritten user signature), *not* from the grade.
This is the invariant that eliminates output-arity mismatches.

#### The to-rule (ANF lifting effectful arguments)

When an argument to a pure call has grade > 1, it is lifted to a
preceding `effectfulCall`. Applied left-to-right.

```
                                             [E-Lift]
Γ(g) = FuncSig(params=Aᵢ, returnType=B')        G(g) = d₁ > 1
outputs(g) = [r₁:B₁, …]
Γ; G ⊢ arg-expressions-before-eᵢ already elaborated as Wⱼ
Γ; G; g-ambient ⊢ continuation-after-binding-r₁ ⇝ M'
────────────────────────────────────────────────────────────────────────
inside the derivation of  Γ; G; g ⊢ (… f(…, g(…), …) …) ; ss ⇝ …
the subterm `g(…)` at argument position is replaced by a fresh `r₁`,
and the enclosing producer becomes
  effectfulCall g Ws [r₁:B₁,…] M'
```

Read: the Laurel AST from Translation cannot contain nested effectful
calls (Translation is syntax-directed and never produces them). [E-Lift]
is the elaboration rule that covers the case where an argument
expression is itself a `StaticCall` with grade > 1 — it is effectively
the producer path for a nested call. Implementationally this is
`checkArgsK`; textually it is the FGCBV "to" rule applied at argument
position.

#### New object (heap construction)

```
                                             [E-New]
heap ≤ g      C has TypeTag       fresh $h
Γ, $h:Heap; G; g ⊢ ss ⇝ M_k
───────────────────────────────────────────────────────────────────
Γ; G; g ⊢ (Assign [x] (New C)) ; ss
         ⇝ varDecl $h Heap (increment $heap)
             (assign x MkComposite(Heap..nextReference!($h), TypeTag_C)
                M_k)
```

The side condition `heap ≤ g` is the grade check: `New` contributes
`heap`, so the ambient grade must permit it. If it does not, the trial
fails at grade `g` and the coinduction bumps `g`.

#### Field write

```
                                             [E-FieldWrite]
fieldType(class, f) = A         Bconstr = boxConstructor(A)
heap ≤ g
Γ; G ⊢ obj ⇝ V_obj ⇐ Composite
Γ; G ⊢ v ⇝ V ⇐ A
Γ, $h:Heap; G; g ⊢ ss ⇝ M_k
─────────────────────────────────────────────────────────────────────
Γ; G; g ⊢ (Assign [FieldSelect obj f] v) ; ss
         ⇝ varDecl $h Heap (updateField($heap, V_obj, ClassName.f,
                                          Bconstr(V)))
             M_k
```

### Procedure entry

```
                                             [E-Proc]
discoverGrade(f) = g
Γ, params ⊢ body ; [] ⇝ M    at ambient g
───────────────────────────────────────────────
procedure f(params) → returnType
  rewritten with grade g:
    g = heap or heapErr ⇒ prepend $heap_in to inputs, $heap to outputs,
                           body prepended with $heap := $heap_in
```

`discoverGrade(f)` is the coinductive pass: try [pure, proc, err, heap,
heapErr] under the current `G` and take the smallest grade at which
checking `body` against it succeeds. See ARCHITECTURE.md §Grade
Inference for the fixpoint procedure.

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

### Elaboration

| Rule                   | Lean function                                     | File |
|------------------------|---------------------------------------------------|------|
| `Γ; G ⊢ e ⇝ V ⇒ T`     | `synthValue`                                      | `Strata/Languages/FineGrainLaurel/Elaborate.lean` |
| `Γ; G ⊢ e ⇝ V ⇐ A`     | `checkValue`                                      | same |
| `Γ; G; g ⊢ s ; ss ⇝ M` | `checkProducer` (threads `ss` as continuation)    | same |
| [E-LitInt]/[E-LitBool]/[E-LitStr] | `synthValue` leaf cases                | same |
| [E-Var]                | `synthValue` (Identifier case)                    | same |
| [E-PureCall]           | `synthValue` (StaticCall with pure callee) → built via `synthExpr` when at statement level | same |
| [E-FieldRead]          | `synthValue` (FieldSelect case) + `boxDestructorName` | same |
| [E-HoleValue]          | `synthValue` (Hole case) — emits `$havoc_N` / `$hole_N` | same |
| [E-Sub]                | `subsume` + `applySubsume`                        | same |
| [E-If]                 | `checkProducer` (If case)                         | same |
| [E-While]              | `checkProducer` (While case)                      | same |
| [E-LabeledBlock]/[E-Exit] | `checkProducer` (LabeledBlock / Exit cases)    | same |
| [E-Return]             | `checkProducer` (Return case)                     | same |
| [E-Assert]             | `checkProducer` (Assert case)                     | same |
| [E-VarDecl]            | `checkProducer` (LocalVariable case) → `mkVarDecl`| same |
| [E-VarDecl-Hole]       | `checkProducer` (LocalVariable with no init) + `mkVarDecl` | same |
| [E-AssignPure]         | `checkAssign` (pure branch)                       | same |
| [E-Call]               | `checkProducer` (StaticCall branch) → `mkGradedCall` | same |
| [E-AssignCall]         | `checkAssign` (call branch) → `mkGradedCall` + inner `assign` | same |
| [E-Lift]               | `checkArgsK`                                      | same |
| [E-New]                | `checkAssign` (New case)                          | same |
| [E-FieldWrite]         | `checkAssign` (FieldSelect target case)           | same |
| [E-Proc]               | `fullElaborate` + `discoverGrades` + `tryGrades`  | same |
| `subgrade(d, g)`       | `subgrade`                                        | same |
| `subsume(T, U)`        | `subsume`                                         | same |
| `G(f)` lookup          | reader read of `procGrades`                       | same |

### Projection (for completeness)

| Form                                     | Lean function                                  |
|------------------------------------------|-------------------------------------------------|
| GFGL value → Laurel expression           | `projectValue`                                  |
| GFGL producer → Laurel statement list    | `projectProducer`                               |
| Procedure body                           | `projectBody`                                   |

---

## Invariants Maintained by the Rules

1. **No hidden grades on the LHS of elaboration rules.** Every grade
   mentioned in a premise is either `G(f)` (lookup) or the ambient `g`
   that is *input* to the current check. This is the change from the
   previous presentation.

2. **Outputs come from signatures, not grades.** Every rule that
   produces an `effectfulCall` gets its output list from
   `outputs(f)` — the callee's declared outputs — via `lookupProcOutputs`.
   The grade only decides whether `$heap` is prepended to the args.

3. **Continuations are elaborated once.** Rules with a `ss` premise
   always put the elaborated continuation `M_k` in a single position
   in the conclusion (via the GFGL constructors' `after`/body field).
   No duplication of continuations between branches.

4. **Laurel is source, not derivation.** Rule LHSes mention Laurel
   *syntax* only. Nothing in the conclusion depends on a Laurel typing
   judgment; all well-typedness is on the GFGL side.

5. **`Γ` grows only through binders.** Calls extend `Γ` with their
   output variables; `var x := e` extends with `x`; `New` extends with
   `$h`. No rule silently invents names without extending `Γ`.

---

## References

- Levy, 2003. *Call-By-Push-Value.*
- Egger, Møgelberg, Staton, 2014. "Linear Usage of State."
- McDermott, 2025. "Grading call-by-push-value."
- Dunfield & Krishnaswami, 2021. "Bidirectional Typing."
- Gaboardi et al., 2016. "Combining Effects and Coeffects via Grading."
