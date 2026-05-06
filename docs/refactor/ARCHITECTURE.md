# Python → Laurel Translation Architecture

**Single source of truth for the refactored translation pipeline.**

---

## The Thesis

The architecture of this system is not a collection of engineering choices. It is the
unique consequence of one principle:

> **There is only one way to do it.**

Every type, every pass boundary, every structural decision exists to eliminate
implementation-level choices. If the implementor faces a decision — "should I emit
`.New` or `StaticCall`?", "should I insert a cast here?", "what type should this
variable get?" — that means our types or our methodology are wrong.

This principle comes from programming language theory and functional programming:

- **Representation invariants** eliminate invalid constructions (no runtime checks)
- **Proof-relevant elimination** eliminates boolean blindness (data carries evidence)
- **Catamorphisms** eliminate traversal choices (one case per constructor)
- **Bidirectional typing** eliminates cast-placement choices (the algorithm decides)
- **Monad-comonad interaction** eliminates metadata-loss scenarios (structural, not manual)

When these are applied correctly, the implementation reads like transcription — not
problem-solving. The pipeline below is the unique structure that satisfies all five.

---

## The Pipeline

The pipeline has the structure of a Logical-Framework-style induction — with
object-level and meta-level operations:

1. **Base case (Resolution):** Establish Γ — the typing context under which everything
   else is well-defined.
2. **Object-level induction (Translation):** Given Γ, construct the derivation `Γ ⊢ e : A`
   by structural fold over the Python AST. This is induction on the input term —
   each Python constructor maps to a Laurel typing rule application.
3. **Meta-level induction (Elaboration):** Given the derivation `Γ ⊢ e : A` constructed
   by Translation, produce a new derivation `Γ ⊢ e' : A` in a richer system
   (FineGrainLaurel) by induction on the structure of the *first derivation*. This
   is an action on derivations, not on terms — it transforms how the term is typed,
   inserting coercions where the object-level derivation uses subsumption implicitly.

The distinction: Translation builds a derivation (object-level). Elaboration
transforms that derivation into one in a more explicit system (meta-level). This is
the same relationship as between a typing judgment and a proof transformation in LF.

```
Python AST + library stubs (both .python.st.ion)
  ↓ [resolve: build Γ — one mechanism for user code and stubs]
Γ : TypeEnv
  +
Python AST (user code only)
  ↓ [translate: source-to-source fold, type-directed via Γ]
e : Laurel.Program (precisely-typed, no casts, no effects)
  ↓ [elaborate: derivation transformation, syntax-directed, language-independent]
e' : FineGrainLaurel.Program (Value/Producer types enforce polarity, all coercions + effects explicit)
  ↓ [project: mechanical mapping FGL → Laurel]
Laurel.Program (coercions/effects as Laurel nodes, ready for Core)
  ↓ [Core translation]
Core
```

The stratification is REPRESENTATIONAL: `Laurel.Program` and `FineGrainLaurel.Program`
are different Lean types. You cannot accidentally pass un-elaborated Laurel to Core —
the type system prevents it. FineGrainLaurel's separate `Value`/`Producer` inductives
make illegal states (producer in value position) unrepresentable at construction time.

---

## Resolution and Elaboration: One Logical Unit

Resolution and elaboration are not independent passes that happen to be adjacent.
Resolution is the **base case** — it establishes Γ. Translation is **object-level
induction** — it builds a derivation `Γ ⊢ e : A`. Elaboration is **meta-level
induction** — it transforms that derivation into one in a richer system.

- Resolution produces **Γ** (the typing context)
- Translation constructs **D : Γ ⊢_Laurel e : A** (a derivation in Laurel's type system)
- Elaboration transforms **D ↦ D' : Γ ⊢_FGL e' : A** (a derivation in FineGrainLaurel)

### Elaboration as Meta-Induction on Derivations

Elaboration operates on the *derivation* D, not on the term e directly. It proceeds
by induction on the structure of D (which, since D is syntax-directed, coincides with
the structure of e). At each step of D where Laurel's typing uses an implicit rule
(subsumption, effect masking), elaboration inserts the explicit witness in D'.

For example: D might contain a step where `e : int` is used at type `Any` via an
implicit subsumption rule. D' replaces that step with an explicit application of
`from_int`, making the coercion a visible node in the derivation tree.

In the sense of Winskel: the mapping D ↦ D' is **manifestly adequate**:
- **Compositional:** elaboration of a compound derivation is defined in terms of elaboration of its sub-derivations
- **Syntax-directed:** one transformation rule per Laurel typing rule, no backtracking
- **Adequate:** every Laurel derivation has a unique FineGrainLaurel elaboration
- **Type-preserving:** if D proves `e : A`, then D' proves `e' : A`

This dependency is reflected in code:

```lean
structure Elaborator where
  env : TypeEnv                    -- Γ, produced by resolution
  elaborate : Laurel.Program → Except ElabError FineGrainLaurel.Program

def mkElaborator (stmts : Array (Python.stmt SourceRange)) (pyspecs : ...) : Elaborator :=
  let env := buildTypeEnv stmts pyspecs    -- resolution (base case)
  { env, elaborate := elaborateWith env }  -- elaboration is only possible after
```

You can't *have* an `Elaborator` without having resolved. The type forces the dependency.

---

## Resolution (Building Γ)

**Input:** Python AST + PySpec files  
**Output:** `TypeEnv` (= Γ)

Resolution and PySpec loading are the same operation: given a name, produce its type
signature. They share one output type. This is not a coincidence — they both answer
the same question ("what is this name?"), so they must produce the same answer type.

```lean
structure FuncSig where
  name : String
  params : List (String × HighType)
  defaults : List (Option StmtExprMd)   -- default values for optional params
  returnType : HighType
  hasErrorOutput : Bool                 -- does this procedure have an Error output?
  hasKwargs : Bool                      -- does this accept **kwargs?

structure TypeEnv where
  names : Std.HashMap String NameInfo
  classFields : Std.HashMap String (List (String × HighType))
  overloadTable : Std.HashMap String (Std.HashMap String String)
    -- factory dispatch: funcName → (stringArg → className)
    -- e.g., "client" → {"iam" → "IAMClient", "s3" → "S3Client"}
  builtinMap : Std.HashMap String String
    -- Python builtins → Laurel names: "str" → "to_string_any", "len" → "Any_len_to_Any"

inductive NameInfo where
  | class_ (name : String) (fields : List (String × HighType))
  | function (sig : FuncSig)
  | variable (ty : HighType)
```

**What Γ must know** (so that translation and elaboration never guess):

| Question | Answered by |
|---|---|
| Is `Foo` a class or a function? | `NameInfo.class_` vs `NameInfo.function` |
| What are `Foo`'s fields? | `NameInfo.class_ _ fields` |
| What are `f`'s parameter types and defaults? | `FuncSig.params`, `FuncSig.defaults` |
| Does `f` have an error output? | `FuncSig.hasErrorOutput` |
| What does `boto3.client("iam")` resolve to? | `overloadTable["client"]["iam"]` → `"IAMClient"` |
| What does `str(x)` map to in Laurel? | `builtinMap["str"]` → `"to_string_any"` |
| What type is `obj` for `obj.method()` dispatch? | `NameInfo.variable ty` → use `ty` to qualify method |
| What does `self.field` resolve to? | `classFields[currentClass][field]` |

**Key property:** After resolution, every name in the program has an entry. Translation
and elaboration look up any name and get a complete type signature without guessing.
No guessing means no decisions. No decisions means one way to do it.

---

## Translation (Producing **e**)

**Input:** Python AST + Γ  
**Output:** Laurel (precisely-typed, no casts, no elaboration artifacts)

Translation is a **fold over the Python AST**. Each constructor maps to exactly one
Laurel construction. The mapping is determined by the AST node + the types from Γ.
There are no implementation-level decisions.

### Deterministic Mapping (expressions)

```
Python.Constant(5)              → Laurel.LiteralInt 5
Python.Constant("s")            → Laurel.LiteralString "s"
Python.Name("x")                → Laurel.Identifier "x"
Python.BinOp(left, Add, right)  → Laurel.StaticCall "PAdd" [left', right']
Python.Compare(l, Eq, r)        → Laurel.StaticCall "PEq" [l', r']
Python.BoolOp(And, [a, b])      → Laurel.StaticCall "PAnd" [a', b']
Python.UnaryOp(Not, x)          → Laurel.StaticCall "PNot" [x']
Python.Call("Foo", args)        → Laurel.New "Foo"             (Γ says Foo is a class)
Python.Call("f", args)          → Laurel.StaticCall "f" [args'] (Γ says f is a function)
Python.Call("str", args)        → Laurel.StaticCall "to_string_any" [args']  (Γ.builtinMap)
Python.Attribute(obj, "field")  → Laurel.FieldSelect obj' "field"
Python.Subscript(c, k)          → Laurel.StaticCall "Get" [c', k']
Python.List([a, b])             → from_ListAny(ListAny_cons(a', ListAny_cons(b', ListAny_nil())))
Python.Dict({k:v})              → from_DictStrAny(DictStrAny_cons(k', v', DictStrAny_empty()))
Python.IfExp(t, b, e)           → Laurel.IfThenElse t' b' e'
```

### Deterministic Desugarings (statements)

These are fixed patterns — one Python construct to a fixed sequence of Laurel nodes:

```
Python.AnnAssign(x, ty, val)    → Laurel.Assign [x'] val'  (scope hoisting pre-declared x)
Python.Assign([x], val)         → Laurel.Assign [x'] val'
Python.Assign([a,b], rhs)       → tmp := rhs; a := Get(tmp, 0); b := Get(tmp, 1)  (tuple unpacking)
Python.AugAssign(x, Add, v)     → Laurel.Assign [x'] (StaticCall "PAdd" [x', v'])
Python.Return(e)                → Laurel.Return e'
Python.Assert(e)                → Laurel.Assert e'
Python.If(t, b, e)              → Laurel.IfThenElse t' b' e'
Python.While(t, b)              → Block [...] (some breakLabel) wrapping While t' (Block [...] (some contLabel))
Python.Break                    → Laurel.Exit <currentBreakLabel>  (from loop label stack)
Python.Continue                 → Laurel.Exit <currentContinueLabel>
Python.Pass                     → Laurel.Block [] none

-- Object construction: Γ says Foo is a class → two-phase protocol
Python.Assign([x], Call("Foo", args))
  → x := New "Foo"; StaticCall "Foo@__init__" [x, args']

-- Context manager: qualified method calls via Γ's type info
Python.With(expr, var, body)
  → mgr := expr'; var := StaticCall "Type@__enter__" [mgr]; body'; StaticCall "Type@__exit__" [mgr]

-- For-loop: verification abstraction (havoc + assume), with labeled blocks
Python.For(x, iter, body)
  → Block [Assign [x'] Hole; Assume(PIn [x', iter']); body'] (some breakLabel)

-- __name__ injection at module level
(synthetic) → LocalVariable "__name__" str (LiteralString "__main__")
```

### What Translation Does NOT Do

- **No cast insertion.** No `from_int`, `from_str`, `Any_to_bool`. That's elaboration.
- **No literal wrapping.** `5` becomes `LiteralInt 5`, period.
- **No type inference.** Types come from annotations, top-down.
- **No polarity/ANF.** Translation naturally produces ANF by construction (expressions are pure, effects are statement-level).

### What Translation DOES Do (Python-Specific Desugarings)

- **Scope hoisting:** Pre-declares all function-local variables at body top (Python scoping).
- **Calling convention:** Normalizes kwargs to positional using Γ's FuncSig.
- **Mutable parameter copies:** `var x := $in_x` for method params.
- **Object construction:** `.New` + `__init__` two-phase protocol.
- **Context managers:** Qualified `Type@__enter__`/`Type@__exit__` calls.
- **For-loop abstraction:** Havoc + assume (verification modeling).
- **Loop labels:** Break/continue with labeled blocks (Translation-internal).

Translation is mechanical. It reads Γ and emits the unique corresponding Laurel.
If you find a decision point in translation, the design is wrong.

---

## Elaboration (Derivation Transformation: Laurel → FineGrainLaurel)

**Input:** Laurel term (potentially ill-typed in FGCBV's sense) + TypeEnv (= **Γ**)  
**Output:** FineGrainLaurel derivation (fully explicit: polarity, coercions, effects)

### The Unifying Principle

**Elaboration is language-independent.** It knows about Laurel's type system and
FineGrainLaurel's requirements — nothing about Python specifically. If we translate
Java→Laurel or JS→Laurel, the *same* elaboration pass works unchanged.

This is the litmus test for what belongs in elaboration vs. resolution/translation:
- "Does this depend on Python's semantics?" → Resolution or translation
- "Does this depend only on Laurel's type system?" → Elaboration

The method is bidirectional typing (Dunfield & Krishnaswami, ACM Computing Surveys 2021):

```
synth(expr) → (FGLExpr, Type)        -- bottom-up: what type does this have?
check(expr, expectedType) → FGLExpr  -- top-down: make it have this type
```

### The Bidirectional Recipe (Our Specific Instantiation)

FineGrainLaurel is implicitly polarized: it is FGCBV viewed as a fragment of CBPV
where the only computation type is `↑A` (a producer of value type A). This means:
- Positive types (values): int, bool, str, Any, Composite, ListAny, DictStrAny
- The only negative type: `↑A` for any positive A (= a producer that yields A)

The bidirectional discipline follows from this polarization, adapted to our system
where Python annotations drive the checking context:

**Elaboration = CBV→FGCBV Embedding (Levy 2003 §3.2)**

Elaboration IS the standard embedding of CBV (Laurel) into FGCBV (FineGrainLaurel).
This embedding is deterministic — no choices, no routing decisions. Every CBV term
has exactly one FGCBV translation.

**The embedding:**
```
⟦n⟧           = produce (litInt n)                    -- literal → value, wrapped in produce
⟦x⟧           = produce (var x)                      -- variable → value, wrapped in produce
⟦f(a₁,...,aₙ)⟧ = ⟦a₁⟧ to x₁. ... ⟦aₙ⟧ to xₙ.       -- evaluate args left-to-right
                  f(coerce(x₁,T₁), ..., coerce(xₙ,Tₙ)) to z.  -- call with coerced values
                  produce z                           -- result is a value
⟦x := e⟧     = ⟦e⟧ to tmp. assign x (coerce(tmp, Γ(x))) continuation
⟦let x:T = e in body⟧ = ⟦e⟧ to tmp. varDecl x T (coerce(tmp,T)) ⟦body⟧
⟦if c then a else b⟧  = ⟦c⟧ to cond. narrow(cond,bool) to b. if b then ⟦a⟧ else ⟦b⟧
```

Key properties:
- **Every subexpression is elaborated as a PRODUCER** (`⟦e⟧` always produces a producer)
- **Every intermediate result is BOUND** (`to x.` = letProd)
- **Coercions applied to BOUND VALUES** (x₁, x₂, ... are values after binding)
- **synthValue only handles ATOMS** (literals, variables — things that ARE values)
- **No routing decision** — the embedding is uniform

**Values vs Producers:**

| Laurel construct | In FGCBV | Why |
|---|---|---|
| `LiteralInt/Bool/String` | VALUE (atom) | Inert, no effects |
| `Identifier "x"` | VALUE (atom) | Variable reference, inert |
| `StaticCall "f" [args]` | PRODUCER | May throw, evaluates args |
| `New "Foo"` | PRODUCER | Heap allocation |
| `FieldSelect obj field` | PRODUCER (on heap) / VALUE (non-heap) | May read heap |
| `Assign/LocalVariable` | PRODUCER | Mutation/binding |
| `IfThenElse/While` | PRODUCER | Control flow |
| `Block` | PRODUCER | Sequencing (M to _. N to _. ...) |
| Everything else | PRODUCER | Effects or control |

**synthValue handles ONLY atoms:** Identifier, Literal. Nothing else.

**synthProducer handles EVERYTHING else.** It applies the embedding uniformly:
elaborate each sub-expression, bind result, apply coercions to bound values.

**checkValue only sees atoms.** Because every compound expression has already been
bound by the time a coercion check happens. The bound variable IS an atom.

**Projection is the LEFT INVERSE of the embedding.** It forgets the FGCBV structure
back into CBV. The chain of `letProd`s becomes a flat sequence of assignments.
`splitProducer` implements this via bind reassociation (monad law).

Round-trip:
```
Laurel (CBV) → [Embedding/Elaboration] → FGL (FGCBV) → [Projection/Forgetting] → Laurel (CBV)
```
What comes back has explicit coercions and bindings that weren't in the input.
That's the whole point — making implicit effects explicit.

**Γ extension at binding sites:**

Γ grows as elaboration descends under binders (standard type theory):
- Enter procedure → extend Γ with parameter names and types
- Process `LocalVariable x : T` → extend Γ with `x : T` for continuation
- Uses `withReader` on the reader monad. No mutable state. One Γ.

**The routing table (which function handles which):**

| Construct | Value or Producer? | Handled by | Why |
|---|---|---|---|
| `LiteralInt/Bool/String` | VALUE | synthValue | Inert, pure |
| `Identifier "x"` | VALUE | synthValue | Variable reference, pure |
| `FieldSelect obj field` | VALUE | synthValue | Pure projection |
| `StaticCall "f" [args]` | **PRODUCER** | **synthProducer** | May throw, coerces args |
| `New "ClassName"` | **PRODUCER** | **synthProducer** | Heap allocation |
| `Assign` | PRODUCER | synthProducer | Mutation |
| `LocalVariable` | PRODUCER | synthProducer | Binding introduction |
| `IfThenElse` | PRODUCER | synthProducer | Control flow |
| `While/Assert/Assume` | PRODUCER | synthProducer | Effect/control |
| `Block` | PRODUCER | synthProducer | Sequencing |
| `Exit/Return` | PRODUCER | synthProducer | Control flow |

**checkValue NEVER sees producers.** It only handles atoms (Identifier, Literal).
The caller (synthProducer) is responsible for binding producer results BEFORE
passing them to coercion. No `isProducer` dispatch. No routing in checkValue.

**Worked example:** `x := PAdd(a, b)` where `x: int`, PAdd: `(Any,Any)→Any`:
```
-- synthProducer for Assign [x] (StaticCall "PAdd" [a, b]):
⟦Identifier "a"⟧ to arg0.              -- elaborate arg a (atom → produce (var a))
⟦Identifier "b"⟧ to arg1.              -- elaborate arg b (atom → produce (var b))
-- arg0 has type int (from Γ), PAdd expects Any → coerce:
let coerced0 = fromInt(arg0)
let coerced1 = fromInt(arg1)
-- Call:
PAdd(coerced0, coerced1) to tmp.        -- bind call result (type Any)
-- Assign target x has type int → narrow Any→int:
Any..as_int!(tmp) to narrowed.          -- narrow (type int)
assign x narrowed                       -- assign the value
```

In FGL terms:
```
letProd "arg0" int (returnValue (var "a"))
 (letProd "arg1" int (returnValue (var "b"))
   (letProd "tmp" Any (call "PAdd" [fromInt (var "arg0"), fromInt (var "arg1")])
     (callWithError "Any..as_int!" [var "tmp"] "narrowed" "err" int Error
       (assign (var "x") (var "narrowed") continuation))))
```

Note: for atoms (Identifier "a"), `⟦a⟧ = produce (var a)` which is trivially bound.
In practice, we can SHORT-CIRCUIT atoms: if the expression is an atom, skip the
bind and use the value directly. This is an optimization, not a semantic change.
The embedding is still uniform — atoms just don't need a real letProd.

**The Rules:**

Value synthesis (atoms only):
```
───────────────        ─────────────────
Γ ⊢_v n ⇒ int         Γ ⊢_v x ⇒ Γ(x)
```

Value checking (subsumption — the ONLY value checking rule):
```
Γ ⊢_v v ⇒ A    A <: B ~~> c
─────────────────────────────
Γ ⊢_v c(v) ⇐ B
```

Producer synthesis:
```
vᵢ ⇐ paramTyᵢ                          v ⇐ Γ(x)
─────────────────────────────────        ─────────────────────────
Γ ⊢_p f(v₁,...,vₙ) ⇒ returnType(f)     Γ ⊢_p (x := v) ⇒ TVoid

─────────────────────────                v ⇐ bool
Γ ⊢_p (new Foo) ⇒ Composite             ─────────────────────────
                                         Γ ⊢_p (assert v) ⇒ TVoid

v ⇐ bool                                v ⇐ bool    Γ ⊢_p M ⇐ TVoid
─────────────────────────                ─────────────────────────────
Γ ⊢_p (assume v) ⇒ TVoid                Γ ⊢_p (while v do M) ⇒ TVoid
```

Producer checking:
```
v ⇐ bool    Γ ⊢_p M ⇐ C    Γ ⊢_p N ⇐ C
──────────────────────────────────────────
Γ ⊢_p (if v then M else N) ⇐ C

v ⇐ T    Γ,x:T ⊢_p body ⇐ C
──────────────────────────────
Γ ⊢_p (var x:T := v; body) ⇐ C

Γ ⊢_p M ⇒ A    Γ,x:A ⊢_p N ⇐ C
──────────────────────────────────
Γ ⊢_p (M to x. N) ⇐ C

v ⇐ procReturnType
───────────────────────────
Γ ⊢_p (return v) ⇐ procReturnType
```

Producer checking fallback (narrowing — when no other producer checking rule matches):
```
Γ ⊢_v v ⇒ A    A ▷ B ~~> n
─────────────────────────────
Γ ⊢_p n(v) ⇐ B
```
Narrowing is the producer checking FALLBACK (like subsumption is the value checking
fallback). It takes a VALUE, applies the narrowing witness `n`, produces a PRODUCER
that checks against expected type B. Both coercion rules operate on values — the
difference is what they produce (value vs producer).

**Mode correctness invariants:**
- Synth: output type determined by inputs (Γ, form, or fixed TVoid)
- Check: expected type is INPUT from context, never conjured
- No type equality anywhere — TVoid in while body is a CHECK (semantic constraint)
- `M to x. N`: M SYNTHS (learn A for binding), N CHECKS against C from context
- Subsumption is the FALLBACK (fires only when no other checking rule applies)

**Summary: which forms synthesize vs check:**

| Form | Synth/Check | Result type |
|---|---|---|
| `f(v₁,...,vₙ)` | Synth | returnType(f) from Γ |
| `new Foo` | Synth | Composite |
| `x := v` | Synth | TVoid |
| `assert v` / `assume v` | Synth | TVoid |
| `while v do M` | Synth | TVoid (body checks against TVoid) |
| `if v then M else N` | Check | C from context |
| `var x:T := v; body` | Check | C from context (flows into body) |
| `M to x. N` | Check | C from context (M synths, N checks) |
| `return v` | Check | procReturnType from context |

**Where coercions fire (subsumption at CHECK boundaries):**

Coercions fire when a synthesized value meets an expected type at a CHECK position.
Per the embedding, every subexpression is bound first (`⟦e⟧ to x.`), then `x` is
used at a CHECK position. The coercion wraps `x`:

| CHECK position | Expected type | Source |
|---|---|---|
| Arg `xᵢ` in `f(x₁,...,xₙ)` | paramTy from FuncSig | Γ |
| RHS `tmp` in `x := tmp` | Γ(x) | Extended Γ |
| Init `tmp` in `var x:T := tmp` | T | Annotation |
| Return value `tmp` in `return tmp` | procReturnType | Proc signature |
| Condition `tmp` in `if tmp ...` | bool | Semantics |

**MODE CORRECTNESS PRINCIPLE: No equality on HighTypes.**

All type comparisons in the elaboration walk MUST flow through:
- `canUpcast actual expected` → subtyping (A <: B, infallible, value-level)
- `canNarrow actual expected` → narrowing (A ▷ B, fallible, producer-level)

If you find yourself writing `typesEqual` or pattern matching on a specific type
in the elaboration walk, you are mode-incorrect. The only legitimate uses of
`typesEqual` are:
1. Inside `checkValue`/`checkProducer` BEFORE trying coercion (short-circuit: if
   types already agree, no coercion needed — this is the reflexivity axiom A <: A)
2. Nowhere else

Specifically NEVER:
- `if expectedType == .TVoid then ...` (TVoid constructs SYNTH, not CHECK)
- `if actualType == .TBool then ...` (the coercion table handles this)
- `match expectedType with | .TInt => ... | .TBool => ...` (that's dispatch on types)

The coercion table is the ONLY mechanism for relating types. If two types aren't
related by the table (neither `canUpcast` nor `canNarrow` produces a match), they
are UNRELATED — that's a type error, not a case to handle.

**The Python annotations ARE the checking context.** Translation preserved them as
precise types on LocalVariable declarations, procedure inputs/outputs. Elaboration
uses these as the CHECK targets. The coercions are "what the annotations demand":
- `var x: int := PAdd(a, b)` → PAdd returns Any, annotation says int → narrow `Any ▷ int`
- `def foo(x: int)` calling `foo(expr)` → check expr against int from sig

**Subsumption (coercion insertion):**

Subtyping and narrowing are CONSTRUCTIVE — they produce coercion witnesses:

```
-- Subtyping judgment produces a value-level coercion function:
A <: B ~~> c        where c : Value(A) → Value(B)
                    (e.g., int <: Any ~~> fromInt)

-- Narrowing judgment produces a producer-level coercion function:
A ▷ B ~~> n         where n : Value(A) → Producer(B)
                    (e.g., Any ▷ bool ~~> Any_to_bool)
```

The subsumption/narrowing rules APPLY these witnesses (both are CHECKING rules):

```
-- Value subsumption (applies upcast witness — value checking fallback):
Γ ⊢_v v ⇒ A    A <: B ~~> c
─────────────────────────────
Γ ⊢_v c(v) ⇐ B                  (value in, value out, B from context)

-- Narrowing (applies downcast witness — producer checking fallback):
Γ ⊢_v v ⇒ A    A ▷ B ~~> n
─────────────────────────────
Γ ⊢_p n(v) ⇐ B                  (value in, producer out, B from context)
```

Key: BOTH are checking rules (B is INPUT from context). BOTH take a VALUE as input.
The witness IS the coercion function/procedure. `canUpcast` returns the witness `c`.
`canNarrow` returns the witness `n`. The coercion table is the collection of all witnesses.

All coercion operates on VALUES. If you need to coerce a producer's result, BIND
it first (`M to x.`), then apply the witness to `x` (a value). Producer checking
has its own rules (if, var-bind, M-to-x, return) plus narrowing as fallback.

To use a narrowed result as a value (e.g., for an if-condition), bind the
narrowing producer: `n(v) to x. (use x as Value(B))`

**Implementation:** Subsumption is ONE function with three cases:
1. Reflexivity (A = A via table): no coercion (short-circuit)
2. Upcast (A <: B via canUpcast): wrap value, stay in value
3. Narrow (A ▷ B via canNarrow): emit producer, bind to get value back

No `typesEqual` dispatch in the walk. No pattern matching on types. The coercion
table decides everything. This function is called at every CHECK boundary.

**Critical: coercions go at the USE SITE (argument position, return position),
NOT at the definition site.** An `int` literal assigned to an `int` variable
needs no coercion. That same variable passed to `PAdd(v: Any)` gets `from_int`
at the call boundary.

Example:
```
var x: int;
x := 5;                              -- CHECK 5 <= int. int = int. No coercion.
prod := PAdd(x, y);                  -- CHECK x <= Any. int ≠ Any. Upcast: from_int(x).
assert Any_to_bool(PEq(prod, ...));  -- CHECK PEq(...) <= bool. Any ≠ bool. Narrow: Any_to_bool.
```

### Short-Circuit Desugaring in FGL

Short-circuit is the CBV→FGCBV embedding of `and`/`or`:

- CBV `or(e, f)`: evaluate e, if truthy return e, else evaluate f
  FGCBV: `e to x. if (truthy x) then produce x else f`
  
- CBV `and(e, f)`: evaluate e, if falsy return e, else evaluate f
  FGCBV: `e to x. if (truthy x) then f else produce x`

The correct FGL (Python's `and`/`or` return VALUES, not booleans):

```
-- PAnd(a, b) where a, b : Any, b is effectful
-- Python semantics: return a if FALSY, else evaluate and return b

prodLetProd "x" Any (elaborate a)              -- evaluate a, bind result to x
  (prodLetProd "cond" bool                     -- narrow x to bool for condition
    (prodCall "Any_to_bool" [valVar "x"])
    (prodIfThenElse (valVar "cond")            -- condition is Value(bool) ✓
      (elaborate b)                             -- truthy: evaluate b, return it (Any) ✓
      (prodReturnValue (valVar "x"))))          -- falsy: return a's value (Any) ✓
```

For `POr(a, b)`:
```
-- Python semantics: return a if TRUTHY, else evaluate and return b

prodLetProd "x" Any (elaborate a)
  (prodLetProd "cond" bool
    (prodCall "Any_to_bool" [valVar "x"])
    (prodIfThenElse (valVar "cond")
      (prodReturnValue (valVar "x"))            -- truthy: return a's value (Any) ✓
      (elaborate b)))                           -- falsy: evaluate b, return it (Any) ✓
```

Key properties:
- Condition is `Value(bool)` (narrowing bound via prodLetProd) ✓
- Both branches produce `Any` (same type) ✓
- Returns the VALUE not a boolean (Python semantics) ✓
- Second operand only evaluated when needed (short-circuit) ✓

---

### Elaboration Subsumes the Existing Lowering Passes

The existing `translateWithLaurel` runs 8 separate "lowering" passes that are all
instances of the same operation: making implicit structure explicit. They should
be unified into the single bidirectional elaboration walk:

| Existing pass | What it makes explicit | Bidirectional interpretation |
|---|---|---|
| `liftExpressionAssignments` | Sequencing (ANF) | FGCBV normal form: producers get let-bound |
| `desugarShortCircuit` | Evaluation order | FGCBV: all sequencing explicit |
| `eliminateReturns` | Control flow | FGCBV: normalize to expression form |
| `heapParameterization` | Heap state effect | Effect type: add Heap to T |
| `typeHierarchyTransform` | Runtime type tags | Type erasure: UserDefined→Composite (§"Two Type Systems") |
| `modifiesClausesTransform` | Frame conditions | Refinement type: heap-frame refinement |
| `constrainedTypeElim` | Type constraints | Refinement type: CHECK against refined type → emit requires/ensures |
| `eliminateHoles` | Nondeterminism | Effect type: nondeterminism as uninterpreted function |

These are all the same mechanism applied to three flavors of type:
- **Base types** (int, Any, bool) → coercions at boundaries
- **Effect types** (Heap, Error, nondeterminism) → effect parameters at boundaries
- **Refinement types** (constrained, modifies, type tags) → proof obligations at boundaries

The bidirectional algorithm handles all three: CHECK against the expected type, if the
actual type is weaker, insert the appropriate witness (coercion / effect param / proof
obligation).

**Why re-resolution goes away:** The existing passes re-run name resolution after each
step because they produce *terms* with dangling names (fresh variables, generated helpers).
Our elaboration produces *derivations* — each name introduction (`prodLetProd`,
`prodVarDecl`) binds the name structurally. Names are correct by construction. There is
nothing to re-resolve because the derivation tree IS the resolution.

### Operations vs Co-Operations (Bauer 2018)

Not all effects are the same. Following Bauer's algebraic effects framework
("What is algebraic about algebraic effects and handlers?", 2018):

- **Operations** are things the computation invokes — the environment handles them.
  (coercions, exceptions, let-bindings)
- **Co-operations** are things the environment provides — the computation threads them.
  (heap state, resource handles)

Heap parameterization is precisely: operations on heap (field read, field write, New)
in Laurel become **co-operations** in FineGrainLaurel — the heap is threaded as an
explicit parameter rather than being implicitly available. This is what "heap
parameterization" IS: turning heap operations into co-operations.

| Effect | Kind | What elaboration does | Scope |
|---|---|---|---|
| Coercions (from_int, Any_to_bool) | Operation | Insert call at boundary | Local |
| Exceptions (error output) | Operation | Insert prodCallWithError | Local |
| ANF (sequencing) | Operation | Insert let-binding | Local |
| Short-circuit (eval order) | Operation | Desugar to if-then-else | Local |
| **Heap (state)** | **Co-operation** | **Thread through signatures** | **Global** |

Operations are local: the bidirectional walk encounters a boundary, inserts a node,
moves on. Co-operations are globally propagated: the walk *discovers* that a procedure
touches state (locally), then the consequence (adding Heap to signatures) propagates
through the entire call graph.

**Both live in Elaboration.** The bidirectional walk handles both — the trigger is
local in both cases. The difference is what gets emitted:

- **Operations:** insert a node at the point
- **Co-operations:** mark the procedure as state-touching, propagate through callers

Implementation: elaboration has two sub-phases:
1. **Local walk** (bidirectional synth/check): inserts operations + discovers co-operations
2. **Global propagation** (fixpoint on call graph): threads Heap through marked procedures

This is analogous to type inference: constraints are collected locally, then solved globally.

---

### Composite and Any: The Pointer Injection

`Any` is a TAGGED UNION (sum type) of Python values. `Composite` is a heap reference
(`MkComposite(ref: int, typeTag: TypeTag)`). The relationship:

**`Composite` injects into `Any` via `from_Composite`** — a pointer-preserving injection.
The `Any` value holds the heap reference directly. No serialization, no deep copy.

```
datatype Any { ..., from_Composite (as_Composite: Composite), ... }
```

This means:
- `Composite <: Any` via `from_Composite` (subtyping: value→value, infallible)
- `Any ▷ Composite` via `Any..as_Composite!` (narrowing: value→producer, may throw TypeError)

**Why pointer-preserving is sound:**
- The `Composite` inside `Any` IS the heap reference (same `ref` integer, same `typeTag`)
- Mutations via `updateField(heap, obj, field, val)` are visible regardless of whether
  `obj` is typed `Composite` or unwrapped from `Any` — same pointer
- Identity preserved: two `from_Composite(x)` wrappings of the same `x` are equal
- No aliasing issues: there's still one object on the heap, one reference to it

**This resolves Issue #882** (Composite/Any unification failure) and the 4 competing
PRs (#727 Hole approach, #918 rename + pathways, #954 DynamicComposite, #1106 coerce
at call sites). The correct answer: `Composite` is just another concrete type that
injects into the `Any` sum, like `int` or `bool`.

---

**Nothing remains as cleanup.** Elaboration subsumes all lowering. `inferHoleTypes`
is subsumed by bidirectional synth (elaboration infers types at every node).
`filterPrelude` is a performance optimization — add it back only if Core can't
handle unused declarations. `validateDiamondFieldAccesses` is an error check that
should be a precondition on Resolution output, not a post-hoc pass.

---

### What Elaboration Does (Language-Independent)

#### Exceptions via the Exception Monad (Standard CBPV Treatment)

In FGCBV/CBPV, the effect monad for our system is `T(A) = Heap → ((A + E) × Heap)`.
A computation takes the current heap, may modify it, and produces either a value of
type A (success) or an error of type E (failure), along with the updated heap. This
combines the state monad (heap threading, co-operation) with the exception monad
(error sum, operation) in a single `T`. Standard treatment: Levy 2004 Ch.5, 
Plotkin & Pretnar 2009.

**The fundamental operations are:**
1. `prodCall "f" [args]` — call the procedure (returns `A + E` as a sum)
2. `prodLetProd result ty call body` — bind the result (monadic bind: `M to x. N`)
3. Case analysis on the sum — `if isError(result) then handle else continue`

There is no special "call with error" primitive. Every procedure call is a 
`prodCall`. If the procedure has error output (`hasErrorOutput = true`), its return
type is `A + E` (concretely: it returns both a result and an error value). The
caller binds and pattern-matches:

```
-- A function call that might throw:
prodLetProd "result" (A × Error)      -- bind the call result (a product of value + error)
  (prodCall "f" [args])               -- the call itself
  (prodIfThenElse                     -- case analysis on the error component
    (isError (snd result))            -- check if error
    <handle error>                    -- error path
    <continue with fst result>)       -- success path
```

**Key insight: a downcast IS a fallible call.** `Any_to_bool(x)` is just a procedure
call whose return type is `bool + TypeError`. It's not a separate mechanism — it's
the same `prodCall` + bind + case pattern:

```
-- A downcast (just a call that can fail):
prodLetProd "narrowed" bool
  (prodCall "Any_to_bool" [valVar "x"])    -- call (may throw TypeError)
  <continue with valVar "narrowed">        -- if it returns, the result is bool
```

**Smart constructor `prodCallWithError`:** For convenience, the FGL dialect defines
`prodCallWithError` as SUGAR that expands to the above pattern (call + bind both
result and error + case analysis). It is NOT a primitive — it's derived from
`prodCall` + `prodLetProd` + `prodIfThenElse`. The dialect keeps it for readability
of the projected output, but the THEORY is just the exception monad.

| Operation | Treatment | Primitive? |
|---|---|---|
| Infallible call | `prodCall "f" [args]` + `prodLetProd` | Yes (primitive) |
| Fallible call | `prodCall "f" [args]` + bind + case on error | Yes (composed from primitives) |
| Downcast (`Any ▷ T`) | `prodCall "Any_to_T" [val]` + bind + case | Yes (same as fallible call) |
| Upcast (`T <: Any`) | `valFromT(val)` | Yes (VALUE-level, no call needed) |
| `prodCallWithError` | Smart constructor = call + bind + case | No (sugar) |

There is no "cast insertion" vs "exception handling" distinction. There is only
**prodCallWithError** — the monadic bind for the effect monad T(A) = A × Error.
Some calls always succeed (upcasts). Some may fail (downcasts, user functions).
The structural form is identical.

#### Polarity Separation (ANF / Let-Binding)

| Pattern | Action |
|---|---|
| Producer in value position (`f() + g()`) | `let tmp1 = f() in let tmp2 = g() in tmp1 + tmp2` |
| Producer as argument (`h(f())`) | `let tmp = f() in h(tmp)` |

When `synth` encounters a producer where a value is expected, it introduces a
let-binding. This is a property of FineGrainLaurel's Value/Producer separation.

Note that `prodCallWithError` IS a let-binding — it sequences a producer and binds
its result. ANF and effect handling are not separate mechanisms; ANF is what
`prodCallWithError` does when there's no error to handle (the error branch is trivial).

#### How Elaboration Works

The bidirectional walk encounters each subexpression:

1. **Synth** a `StaticCall "f" [args]`:
   - Look up `f` in Γ
   - If `f.hasErrorOutput` or `f` is a downcast → emit `prodCallWithError`
   - If `f` is infallible → emit `prodLetProd` (simple ANF bind, error branch eliminated)
   - The result type comes from `FuncSig.returnType`

2. **Check** the result against the expected type:
   - If actual ≠ expected → the coercion itself is another `prodCallWithError`
   - Coercions compose: `let tmp = f() in let coerced = from_int(tmp) in ...`

Translation emits **plain calls**. It does NOT emit `isError` checks, multi-output
assignments, or coercions. Elaboration handles all of these uniformly via the single
`prodCallWithError` mechanism.

### What Resolution Handles (Python-Specific)

The following are all "what does this name/construct mean in Python?" questions.
They're resolved by building a richer Γ that makes translation deterministic.

#### Scope Resolution

Scope hoisting is a resolution problem — it answers "where does this variable live?"

| Question | Resolution answer |
|---|---|
| Variable `x` assigned inside `for` loop — where does it live? | Function scope (Python semantics). Γ records it. |
| Variable `e` from `except E as e:` — visible after? | Function scope. Γ records it. |
| Variable `x` assigned in both branches of `if` — one declaration or two? | One, at function scope. Γ records it. |

Resolution walks the function body, discovers all assigned names (Python's scoping
rule: assignment creates a function-local), and records them in Γ. Translation then
emits `LocalVariable` declarations at function top because Γ says they exist there.

#### Calling Convention

| Question | Resolution answer |
|---|---|
| What are `f`'s params in order? | `FuncSig.params` |
| Which params have defaults? | `FuncSig.defaults` |
| Does `f` accept `**kwargs`? | `FuncSig.hasKwargs` |

Translation emits calls with args in the order Γ's signature specifies. No runtime
reordering needed — Γ already normalized it.

#### Effect Signatures

| Question | Resolution answer |
|---|---|
| Does calling `f` produce an error output? | `FuncSig.hasErrorOutput` |
| What exception types can `f` raise? | Encoded in FuncSig (from PySpec) |

Translation emits plain calls. Elaboration inserts the error-handling protocol
(`prodCallWithError`) because Γ says the callee has an error output.

#### Mutability

| Question | Resolution answer |
|---|---|
| Is parameter `x` mutable? | All Python params are mutable → Γ marks it |
| Does `obj[k] = v` need functional update? | Γ says `obj` is a composite value type |

Translation emits the copy pattern (`var x := $in_x`) or functional update
(`obj = Any_sets(...)`) because Γ tells it what kind of thing it's dealing with.

#### Method and Builtin Resolution

| Question | Resolution answer |
|---|---|
| What does `obj.method()` resolve to? | `ReceiverType@method` (Γ knows obj's type) |
| What does `str(x)` mean? | `builtinMap["str"]` → `"to_string_any"` |
| What does `boto3.client("iam")` resolve to? | `overloadTable["client"]["iam"]` → `"IAMClient"` |
| What does `f"{composite}"` need? | Γ knows composite's fields → serialization determined |

#### Verification Modeling

| Question | Resolution answer |
|---|---|
| Is this a for-loop? | Γ/translation emits havoc+assume (fixed modeling choice) |
| Does `x: int \| str` need a precondition? | Γ records union type → translation emits Assume |
| Does return type need a postcondition? | Γ records return type → translation emits constraint |

### Key Property

**Elaboration is total on well-typed Laurel.** It cannot fail on well-formed input.
It is also **reusable** — Java→Laurel, JS→Laurel, or any other source language
produces Laurel that the same elaboration pass processes identically.

---

## Projection (FineGrainLaurel → Laurel)

### Categorical Background: FGCBV and CBV

FineGrainLaurel is to Laurel as FGCBV (Fine-Grain Call-By-Value) is to CBV
(Call-By-Value). This is a precise category-theoretic relationship, not an analogy.

**CBV** (Moggi 1991) models effectful computation via a monad T on a category C:
- Types are objects of C
- Values and computations live in the same syntactic category
- The monad T encapsulates effects: a computation of type A is a value of type TA
- Sequencing is monadic bind: `let x = M in N` where M : TA, N : TB (with x : A free)

In our system, **T encapsulates elaboration effects** — specifically:
- **Type coercions** (casting between Any and concrete types)
- **Exception propagation** (error outputs)
- **Partiality** (precondition violations, undefined behavior)

These are the effects that elaboration makes explicit. A "producer" is any term
that might cast, throw, or diverge. A "value" is inert — no effects possible.

The problem with CBV (= Laurel): values and producers are conflated syntactically.
The term `f(g(x))` hides sequencing — `g(x)` is a computation (it might throw, it
might need a cast on its result) whose result feeds into `f`, but the syntax doesn't
make the intermediate binding or error check explicit.

**FGCBV** (Levy 1999, 2004) refines CBV by separating the syntax:
- **Values** (type V): inert terms — variables, literals, pure constructions
- **Producers** (type TV): effectful terms — function calls (may throw), coercions (may fail), let-bindings, control flow
- A producer in value position *must* be explicitly sequenced via let-binding

The key operation is **let-binding** (monadic bind made syntactically explicit):
```
-- CBV / Laurel (implicit sequencing, implicit effects):
f(g(x))           -- g might throw, f might cast — all hidden

-- FGCBV / FineGrainLaurel (explicit sequencing, explicit effects):
let tmp = g(x) in   -- g is a producer: might throw → error check here
let result = f(tmp) in  -- f is a producer: might cast → coercion here
result
```

### Exception Handling: The Monadic Model

Exception handling in FineGrainLaurel is **monadic** — not an ad-hoc protocol of
sentinel variables and boolean checks. The FineGrainLaurel dialect already defines
the correct operator:

```
op prodCallWithError (callee: Ident, args: CommaSepBy Value,
                      resultVar: Ident, errorVar: Ident,
                      resultTy: LaurelType, errorTy: LaurelType,
                      body: Producer): Producer
  => "let [" resultVar ": " resultTy ", " errorVar ": " errorTy
     "] = " callee "(" args ") in " body;
```

This is the monadic bind for `T(A) = A + Error`:
- The callee produces either a result (type A) or an error (type Error)
- The `body` continuation has access to both `resultVar` and `errorVar`
- The `body` decides how to handle the error (propagate or catch)

**The flow:**
1. **Translation** emits a plain `StaticCall "f" [args]` — it doesn't know about errors
2. **Elaboration** sees that Γ says `f` has error output → transforms into:
   ```
   prodCallWithError "f" [args] result err A Error
     (if isError(err) then prodRaise(err) else <continue with result>)
   ```
3. **Projection** (DDM) flattens back to Laurel's multi-output assignment that Core expects:
   ```
   result, maybe_except := f(args)
   if isError(maybe_except) then ...
   ```

**The critical insight:** The ad-hoc `maybe_except` pattern in the old pipeline IS
the projection of the monadic bind. We were generating the *projected* form directly
instead of going through the proper intermediate. The difference:
- **Wrong:** Translation emits `result, maybe_except := f(args); if isError(...)` directly
- **Right:** Elaboration emits `prodCallWithError`, projection flattens it

This matters because:
- `prodCallWithError` is a **structural** construct that downstream passes can reason about
- The projected form is opaque imperative code that looks like any other if-statement
- FineGrainLaurel-level transformations (optimization, verification) can treat
  `prodCallWithError` as a single unit (it's the monadic bind), not three separate statements

### Prelude Alignment

The Laurel prelude defines:
- `Error` datatype: `NoError | TypeError | AttributeError | ...`
- `isError(e: Error) : bool`: test if exception occurred
- `exception(e: Error) : Any`: wrap exception in Any type

The prelude's `Error` with `NoError` as the success marker is the concrete
realization of the sum type `1 + TypeError + AttributeError + ...`. The monadic
T(A) for our system is `A × Error` (where Error may be `NoError`), which projects
to Laurel's multi-output convention: procedures return `(result: A, maybe_except: Error)`.

If we find ourselves encoding exceptions non-monadically (flag variables, manual
if-checks outside of the projection), something is wrong — we've left the Kleisli
category.

**Projection** (FGCBV → CBV) is the **forgetful functor** that erases the
Value/Producer distinction. Category-theoretically:
- FGCBV lives in the Kleisli category of the monad T
- CBV lives in the base category C (with T implicit)
- Projection is the canonical functor from Kleisli(T) → C that forgets the T-structure

In our system:
- **FineGrainLaurel** = FGCBV: separate `Value` and `Producer` categories, explicit let-bindings, explicit coercions
- **Laurel** = CBV: single `StmtExpr` type, sequencing implicit, effects implicit
- **Projection** = forgetful functor: erases polarity, keeps the inserted let-bindings and coercions as regular Laurel nodes

### Elaboration and Projection are Inverses

The round-trip:
```
Laurel (CBV) → [Elaboration = CBV→FGCBV embedding] → FGL → [Projection = FGCBV→CBV] → Laurel (CBV)
```

Projection is the LEFT INVERSE of elaboration. What comes back is the SAME
program but with explicit coercions and let-bindings that weren't in the input.
The embedding makes effects explicit. The forgetting flattens them back into
imperative sequential code. The net effect: coercions inserted, sequencing made
explicit, type errors caught.

### Why This Matters

1. **Elaboration targets FGCBV** because the CBV→FGCBV embedding is what forces
   every subexpression to be bound. Binding is where coercions are inserted.
   In CBV (Laurel), subexpressions are implicit — no place to insert coercions.

2. **Projection is total and meaning-preserving.** Every FGCBV term projects to a
   unique CBV term. The projection cannot fail and cannot change semantics — it only
   forgets the syntactic stratification. This is the category-theoretic guarantee.

3. **Illegal states in CBV become type errors in FGCBV.** A producer nested directly
   inside another producer (without let-binding) is a type error in FGCBV, though it's
   syntactically representable in CBV. The separate types make it unrepresentable.

### Implementation: Projection as Bind Reassociation

Projection views an FGCBV term as a CBV term. The key operation: nested
`prodLetProd` (monadic binds) become flat sequential statements. This is
monadic bind ASSOCIATIVITY:

```
-- FGCBV (nested lets — right-associated):
let x = (let y = N in K) in body

-- CBV (flat statements — left-associated):
y := N;
x := K;
body
```

The reassociation law: `let x = (let y = M in N) in K` = `let y = M in let x = N in K`

This is not an optimization — it's the DEFINITION of viewing FGCBV as CBV.
Every nested `prodLetProd` in the producer position of another `prodLetProd`
gets reassociated to the same level.

**The projection algorithm:**

Two functions — one extracts the "prefix bindings + terminal expression" from a
producer, the other flattens into a statement list:

```
-- Split a producer into (prefix statements, terminal expression)
-- The terminal is what the producer "produces" — the value that would be bound
-- by an enclosing `let x = M in ...`
splitProducer : FGL.Producer → (List Laurel.Stmt, Laurel.Expr)

splitProducer (prodReturnValue v)       = ([], projectValue v)
splitProducer (prodCall f args)         = ([], StaticCall f (args.map projectValue))
splitProducer (prodLetProd x ty M body) = let (mStmts, mExpr) := splitProducer M
                                          let xDecl := LocalVariable x ty (some mExpr)
                                          let (bodyStmts, bodyExpr) := splitProducer body
                                          (mStmts ++ [xDecl] ++ bodyStmts, bodyExpr)
splitProducer (prodAssign t v body)     = let assignStmt := Assign [projectValue t] (projectValue v)
                                          let (bodyStmts, bodyExpr) := splitProducer body
                                          ([assignStmt] ++ bodyStmts, bodyExpr)
splitProducer (prodIfThenElse c t e)    = ([], IfThenElse (projectValue c) (project t) (project e))
splitProducer (prodWhile c invs b aft)  = let whileStmt := While (projectValue c) invs (project b)
                                          let (afterStmts, afterExpr) := splitProducer aft
                                          ([whileStmt] ++ afterStmts, afterExpr)

-- For a procedure body (top level): just get all statements, ignore terminal
projectBody : FGL.Producer → Laurel.StmtExprMd
projectBody prod = let (stmts, _terminal) := splitProducer prod
                   Block stmts none
```

**Example — the reassociation in action:**

```
-- FGL (nested):
prodLetProd "assertCond" bool
  (prodLetProd "narrow" Any (prodCall "PAnd" [a, a]) (prodCall "Any_to_bool" [valVar "narrow"]))
  (prodAssert (valVar "assertCond") continuation)

-- splitProducer on the inner prodLetProd:
-- splitProducer (prodCall "PAnd" [a,a]) = ([], PAnd(a,a))
-- So: mStmts=[], mExpr=PAnd(a,a)
-- xDecl = LocalVariable "narrow" Any (some PAnd(a,a))
-- splitProducer (prodCall "Any_to_bool" [narrow]) = ([], Any_to_bool(narrow))
-- So: bodyStmts=[], bodyExpr=Any_to_bool(narrow)
-- Result: ([LocalVariable "narrow" Any (some PAnd(a,a))], Any_to_bool(narrow))

-- Now the outer prodLetProd:
-- (mStmts, mExpr) = ([LocalVariable "narrow" Any (some PAnd(a,a))], Any_to_bool(narrow))
-- xDecl = LocalVariable "assertCond" bool (some Any_to_bool(narrow))
-- Result includes: [LocalVariable "narrow" ..., LocalVariable "assertCond" ..., assert ...]

-- FLAT output:
var narrow: Any := PAnd(a, a);
var assertCond: bool := Any_to_bool(narrow);
assert assertCond;
```

**No heuristics. No filtering. No "expression vs statement position."**
Just the monad law `(m >>= f) >>= g = m >>= (λx. f x >>= g)` applied as a
syntactic transformation: split into prefix + terminal, thread through.

**Assumption: elaboration generates FRESH names for all bindings.**

Laurel has block scoping (a `LocalVariable` at the top of a `Block` is scoped
to that block). The flattening widens variable scope:

In the nested form:
```
let x = (let y = N in K) in body
```
`y` is scoped ONLY inside `(let y = N in K)` — not visible in `body`.

In the flattened form:
```
y := N;
x := K;
body;
```
`y` is now visible to `body` (same flat scope).

This is SAFE because:
1. Elaboration generates FRESH variable names for all intermediate bindings
   (`narrow$1`, `assertCond$2`, `arg$3`, etc. via `freshVar`)
2. Fresh names cannot clash with any user-defined or prelude names
3. Therefore scope widening cannot cause variable capture
4. Additionally, Translation already hoists user-defined locals to function
   top (Python's scoping rule), so user variables are already function-scoped

**Invariant to maintain:** Elaboration MUST use `freshVar` for all intermediate
bindings. If it ever reuses a name, the flattening becomes unsound.

---

## Representation Decisions

### FineGrainLaurel: Separate Value and Producer Types

```
category Value;    -- inert terms (literals, variables, fields)
category Producer; -- effectful terms (calls, let-bindings, control flow)
```

Illegal states are unrepresentable. You cannot put a Producer where a Value is
expected — Lean's type system rejects it at construction time. No runtime checks,
no predicates, no `by sorry`.

### Two Type Systems: HighType and LowType (Type-Directed Compilation)

Elaboration is a **typed translation between two type systems** (Harper & Morrisett
1995, TIL). The source system has class identity. The target system has a uniform
heap representation. The translation is coherent: every source typing derivation
maps to a unique target typing derivation.

**HighType** (Translation's output, Elaboration's input):
```lean
inductive HighType where
  | TInt | TBool | TString | TFloat64 | TVoid
  | TCore (name : String)       -- "Any", "Error", "ListAny", "DictStrAny", etc.
  | UserDefined (id : Identifier)  -- "Foo", "Bar" — distinct class identities
```

**LowType** (FGL's type system, Elaboration's output):
```lean
inductive LowType where
  | TInt | TBool | TString | TFloat64 | TVoid
  | TCore (name : String)       -- "Any", "Error", "Composite", "Heap", "ListAny", etc.
  -- NO UserDefined. All class instances are Composite.
```

`UserDefined` is **unrepresentable** in LowType. If elaboration accidentally tries
to emit a `UserDefined` in FGL output, it's a Lean type error. The type system
enforces the erasure boundary.

**The type translation (`eraseType`):**
```lean
def eraseType : HighType → LowType
  | .TInt => .TInt
  | .TBool => .TBool
  | .TString => .TString
  | .TFloat64 => .TFloat64
  | .TVoid => .TVoid
  | .TCore name => .TCore name
  | .UserDefined _ => .TCore "Composite"  -- ALL class instances → Composite
```

This is total (every HighType maps to a LowType) and deterministic (no choices).
The type tells you what to do. `UserDefined` always becomes `Composite`.

**How this affects elaboration:**

The bidirectional walk operates ACROSS the type boundary:
- Input: `StmtExprMd` with `HighType` annotations (from Translation)
- Output: `FGLValue`/`FGLProducer` with `LowType` (in FGL)
- `synthValue : StmtExprMd → ElabM (FGLValue × LowType)` — synthesizes a target type
- `checkValue : StmtExprMd → HighType → ElabM FGLValue` — expected type is in source system

The coercion table crosses the boundary:
```
canUpcast : HighType → HighType → Option (FGLValue → FGLValue)
```
When it sees `UserDefined _ → TCore "Any"`, it emits `from_Composite` — which is
correct because in the target, the value IS `Composite` (eraseType applied).

**How this affects term translation:**

When elaboration encounters terms whose meaning changes under erasure:
- `New "Foo"` → `MkComposite(freshRef, Foo_TypeTag())` (allocation in erased world)
- `var x : Foo` → type becomes `Composite` in FGL output
- `self : Foo` in method → `self : Composite`
- `FieldSelect obj field` → `readField(heap, obj, field)` (because obj is Composite)
- `Assign [FieldSelect obj field] val` → `updateField(heap, obj, field, BoxT(val))`

These are all determined by the type: seeing `UserDefined` in the source triggers
the erasure-aware elaboration. No boolean predicates. The type drives it.

**What remains in HighType for Resolution/Translation:**

Resolution needs `UserDefined "Foo"` to:
- Qualify methods: `Foo@method`
- Look up fields: `classFields["Foo"]`
- Distinguish classes from functions in Call resolution

Translation needs it to:
- Emit `New "Foo"` (not yet erased)
- Emit self-typed parameters
- Track variable types for method dispatch

After elaboration, `UserDefined` is gone. FGL and everything downstream (projection,
Core) only see `Composite`.

### Metadata: Smart Constructors (the ONLY way to build AST nodes)

Every AST node (`StmtExprMd` = `WithMetadata StmtExpr`) is constructed through a
smart constructor that takes the metadata and the inner value. You NEVER write
`{ val := ..., md := ... }` directly. The smart constructor makes forgetting
metadata impossible — you cannot construct a node without providing source location.

```lean
def mkLaurel (md : Imperative.MetaData Core.Expression) (e : StmtExpr) : StmtExprMd :=
  { val := e, md := md }
```

**Where does `md` come from?**
- For nodes that correspond to an input node: use the input node's `.md`
- For synthesized nodes (let-bindings, coercion calls): inherit `.md` from the
  input node that triggered the synthesis

This is the standard source-location pattern in every functional compiler.
Pattern match on `.val`, thread `.md` through the smart constructor on output.

**Translation** uses `mkExpr sr expr` (reads `sr` from the Python AST node).
**Elaboration** uses `mkLaurel md expr` (reads `md` from the input Laurel node).
**Projection** uses `mkLaurel md expr` (reads `md` from the FGL node being projected).

No polymorphic types. No reader-based threading. Just smart constructors.

### Translation Monad

```lean
abbrev TransM := ReaderT TypeEnv (StateT TransState (Except TransError))
```

Γ in the reader (immutable). Fresh names in the state. The monad carries everything —
no manual context threading.

---

## Engineering Principles

Each principle below is a consequence of "there is only one way to do it":

| # | Principle | Eliminates |
|---|---|---|
| 1 | **Representation invariants** — encode properties in types | Runtime checks, dead branches |
| 2 | **Proof-relevant elimination** — sum types carry evidence | Boolean blindness, re-derivation |
| 3 | **Catamorphisms** — one case per constructor | Traversal choices, interleaved walks |
| 4 | **Correct by construction** — no post-hoc rewrites | Fixup passes, tree-walking hacks |
| 5 | **Separation of concerns** — one responsibility per pass | Decisions in the wrong place |
| 6 | **Interaction law** — monad-comonad composition | Dropped metadata, manual threading |
| 7 | **Monad carries context** — ReaderT/StateT | Ad-hoc parameter passing |
| 8 | **Types flow down** — annotations, not inference | Bottom-up guessing in translation |

**Litmus test:** If you're writing an `if` statement in translation, something is wrong.
Either resolution should have settled it (strengthen Γ) or elaboration should handle
it (move it later). Translation is a fold — it pattern-matches on constructors, not
on properties.

---

## Files

```
NameResolution.lean              -- Build Γ from Python AST + PySpec + prelude
Translation.lean                 -- Fold over AST, produce e (one file, one fold)
Elaborate.lean                   -- Γ ⊢ e ⇒ e' (bidirectional, all semantic work)
FineGrainLaurel.dialect.st       -- DDM dialect (Value/Producer categories)
Pipeline.lean                    -- Wire passes together, CLI integration
```

---

## Library Stubs: Eliminating PySpec

### The Old Way (PySpec)

```
Python stubs (.py) → pySpecs tool → .pyspec.st.ion (binary) → ToLaurel.lean (675 lines) → Laurel
```

Four formats, three tools, two translation paths (one for user code, one for specs).

### The New Way (One Mechanism)

```
Python stubs (.py) → Python parser → .python.st.ion → buildTypeEnv → Γ_library
User code (.py)    → Python parser → .python.st.ion → buildTypeEnv → Γ_user
                                                       merge(Γ_library, Γ_user) → Γ
```

**Library stubs are Python. User code is Python. Resolution consumes Python.
There's only one mechanism.**

A stub file is a regular Python file with ClassDefs, FunctionDefs, type annotations,
and assert-based preconditions in method bodies. `buildTypeEnv` already handles
ClassDef → `NameInfo.class_`, FunctionDef → `NameInfo.function`. The only extension
needed: walk into stub method bodies to extract `assert` statements as `FuncSig`
preconditions.

### What Gets Eliminated

- `codegen.sh` / `pySpecs` generation tool
- `.pyspec.st.ion` binary format
- `Specs/ToLaurel.lean` (675 lines)
- `Specs/LoadSpecs.lean` (192 lines)
- `IdentifyOverloads.lean`
- The entire concept of "PySpec" as a separate pipeline

### The Pipeline

```
stub.python.st.ion  →  buildTypeEnv  →  Γ_library  (signatures + preconditions)
user.python.st.ion  →  buildTypeEnv  →  Γ_user     (signatures + user code structure)
                        merge(Γ_library, Γ_user)    →  Γ
                        translate(user AST, Γ)      →  e   (only user code gets translated)
                        elaborate(e, Γ)             →  e'
```

The distinction between "user code" and "library stubs" is just: we translate the
user's bodies but only take the stubs' signatures. `buildTypeEnv` does the same
thing for both — it never translates bodies, only records types.

### Preconditions from Stubs

Stub method bodies contain assert-based specifications:

```python
def request_spot_fleet(self, **kwargs: Unpack[RequestSpotFleetRequest]) -> None:
    assert len(kwargs["SpotFleetRequestConfig"]["LaunchSpecifications"]) >= 1
    assert len(kwargs["SpotFleetRequestConfig"]["LaunchSpecifications"]) <= 5
```

Resolution extracts these into `FuncSig.preconditions`:
```lean
structure FuncSig where
  ...
  preconditions : List (Python.expr SourceRange)  -- assert conditions from stub body
```

Translation emits them as `Assume` statements at call sites (verification modeling).

### Overload/Factory Dispatch from Stubs

Stubs define class structure. If `boto3.client` returns different types based on a
string argument, the stub file encodes this via `@overload`:

```python
@overload
def client(self, service_name: Literal["iam"]) -> IAMClient: ...
@overload
def client(self, service_name: Literal["s3"]) -> S3Client: ...
```

Resolution reads `@overload` + `Literal` annotations → populates `TypeEnv.overloadTable`:
```
"client" → {"iam" → "IAMClient", "s3" → "S3Client"}
```

No special dispatch mechanism. Just Resolution reading Python annotations.

### Types and Coercions: The Full Story

Core has NO subtyping. `int ≠ Any` — Hindley-Milner unification rejects them.
The prelude operations (`PAdd`, `PSub`, etc.) all take `Any` and return `Any`.

This is exactly what elaboration exists to handle:

1. Translation emits **precise types** from annotations: `procedure foo(x: int)`
2. Elaboration sees `PAdd` expects `Any`, `x` has `int` → inserts `from_int(x)`
3. Elaboration sees `PAdd` returns `Any`, result assigned to `y: int` → inserts `Any..as_int!(result)`
4. After elaboration, all boundaries are correctly bridged

The old pipeline achieved the same final state by collapsing everything to `Any`
upfront and wrapping literals in `from_int` during translation. That's the
*projected form* of what correct elaboration produces — but it conflates two passes
into one, violating separation of concerns.

**Elaboration must elaborate ALL calls uniformly** — prelude functions, user functions,
methods, casts. There is no `isPreludeFunc` gate. Every call site gets the same
bidirectional treatment: synth the argument types, check against the callee's param
types from Γ, insert coercions at mismatches.

---

### Performance: Load Only What's Needed

Resolution should only load stubs for services the user code actually imports.
This is an optimization internal to Resolution — the contract ("every name has an
entry in Γ") is unchanged. Implementation: scan user code `Import`/`ImportFrom`
nodes first, map to stub files, load only those.

Start with "load all referenced stubs." Optimize later if slow. Correctness first.

---

## Laurel Stratification (RESOLVED)

The stratification is representational: `Laurel.Program` and `FineGrainLaurel.Program`
are different Lean types (generated by DDM from separate dialect files). The type
system enforces the pipeline ordering:

- Translation produces `Laurel.Program` (you can't call elaboration without one)
- Elaboration takes `Laurel.Program`, produces `FineGrainLaurel.Program` (different type)
- Projection takes `FineGrainLaurel.Program`, produces `Laurel.Program` (for Core)

There are no "HighLaurel/MidLaurel/LowLaurel" implicit invariants. The invariants
ARE the types: FineGrainLaurel's `Value`/`Producer` separation makes illegal states
(producer in value position) unrepresentable at construction time.

After projection, the Laurel output goes directly to Core translation. No lowering
passes needed — elaboration already handled everything (coercions, heap threading,
type hierarchy, ANF). No cleanup passes either — bidirectional synth infers all types,
and projection produces complete output.

---

## Non-Goals

- **Untyped Python.** Missing annotations → `Any`. No inference.
- **Aliasing.** Documented assumption: no aliasing of composite values.
- **Laurel/Core changes.** Existing infrastructure unchanged.
- **Optimization.** Correctness first (except stub loading — see above).

### Break/Continue Labels (Translation-Internal)

Python's `break`/`continue` have no label — they implicitly reference the innermost
enclosing loop. Laurel's `Exit "label"` requires an explicit label string that matches
a `Block [...] (some "label")` node.

This is NOT a resolution problem (it's not a Python name, it's a Laurel artifact).
It's Translation-internal: the fold maintains a **loop label stack** in `TransState`:

```lean
structure TransState where
  ...
  loopLabels : List String := []  -- stack of enclosing loop labels
```

- Entering `For`/`While`: push a fresh label, emit `Block [...] (some label)`
- `Break`: emit `Exit <top_of_stack>`
- `Continue`: emit `Exit <continue_label>` (separate continue target within loop body)
- Exiting loop: pop

No resolution needed. The label is synthesized during the fold and never escapes
the function body. The monad carries it.

---

### Known Tech Debt: Instance Procedure Workaround

The existing `LaurelToCoreTranslator` does not fully support instance procedures on
composite types (it reports "Instance procedure on composite type not yet supported").
Since we don't change Laurel/Core infrastructure, Translation emits class methods as
**top-level static procedures** with `self` as an explicit first parameter:

```
-- Python: class Foo:
--           def bar(self, x): ...
--
-- Emitted Laurel:
composite Foo { ... }
procedure Foo@bar(self: Foo, x: Any) returns (LaurelResult: Any) { ... }
```

This matches what the old pipeline does and what Core can handle. The `instanceProcedures`
field on `CompositeType` is left empty — methods live as top-level procedures with
qualified names. This is tech debt: ideally Core would support instance procedures
directly, but that's outside our scope.

### Known Tech Debt: Prelude Data Type Encodings

The prelude defines Python's collection types as recursive algebraic datatypes in Laurel:

```
datatype ListAny { ListAny_nil, ListAny_cons(head: Any, tail: ListAny) }
datatype DictStrAny { DictStrAny_empty, DictStrAny_cons(key: string, val: Any, tail: DictStrAny) }
```

Translation must emit these specific constructors — not abstract operations like
`List_new` or `Dict_new` that don't exist as declared procedures. The mapping:

| Python | Laurel emission |
|---|---|
| `[a, b, c]` | `ListAny_cons(a, ListAny_cons(b, ListAny_cons(c, ListAny_nil())))` |
| `{k1: v1, k2: v2}` | `DictStrAny_cons(k1, v1, DictStrAny_cons(k2, v2, DictStrAny_empty()))` |
| `(a, b)` | Same as list (tuples are ListAny in this model) |
| `f"{expr}"` | `to_string_any(expr)` (prelude function, not `ToString`) |
| `str(x)` | `to_string_any(x)` (via `builtinMap`) |

This is the same pattern as instance procedures: we emit what the existing
infrastructure can handle rather than inventing abstractions it doesn't support.
Ideally, Laurel would have first-class list/dict types with native operations, but
that's outside our scope. We work with what Core knows.

---

## Success Criteria

1. All 54 in-tree tests pass verification (match or exceed old pipeline).
2. Translation is a fold — no post-hoc tree rewrites.
3. Elaboration is separate — translation emits no casts.
4. Types from annotations — nothing defaults to `Any` unless annotation is absent.
5. One file per pass. No fragmentation.
6. Implementation feels like transcription, not problem-solving.

---

## References

### Foundational

- **Moggi, E.** (1991). "Notions of computation and monads." *Information and Computation*, 93(1), 55–92.
  — The monadic model of effects. Our T encapsulates elaboration effects (casts, exceptions, partiality).

- **Levy, P.B.** (1999). "Call-by-push-value: A subsuming paradigm." *TLCA*.
  — Introduces CBPV which separates values from computations. FGCBV is the call-by-value restriction.

- **Levy, P.B.** (2004). *Call-By-Push-Value: A Functional/Imperative Synthesis.* Springer.
  — Full treatment. FineGrainLaurel's Value/Producer separation is this.

### Bidirectional Typing

- **Dunfield, J. & Krishnaswami, N.R.** (2021). "Bidirectional Typing." *ACM Computing Surveys*, 54(5), Article 98.
  — The survey. Our elaboration recipe (synth/check, subsumption at coercion boundaries) follows Section 4.

- **Dunfield, J. & Krishnaswami, N.R.** (2013). "Complete and Easy Bidirectional Typechecking for Higher-Rank Polymorphism." *ICFP*.
  — The specific algorithm. Our system is simpler (no polymorphism) but uses the same mode discipline.

### Gradual Typing (Any ↔ Concrete Boundaries)

- **Siek, J.G. & Taha, W.** (2006). "Gradual Typing for Functional Languages." *Scheme and Functional Programming Workshop*.
  — Introduces gradual typing. Our `Any` type and cast insertion at boundaries follows this model.

- **Siek, J.G. & Vachharajani, M.** (2008). "Gradual Typing with Unification-based Inference." *DLS*.
  — Bidirectional + gradual. Consistency replaces subtyping: `Any ~ T` for all `T`.

### Algebraic Effects and Handlers

- **Plotkin, G. & Pretnar, M.** (2009). "Handlers of Algebraic Effects." *ESOP*.
  — Algebraic effects with handlers. Our `prodCallWithError` is a specific handler for the exception effect.

- **Bauer, A.** (2018). "What is algebraic about algebraic effects and handlers?" *arXiv:1807.05923*.
  — Operations vs co-operations. Operations are invoked by computation (coercions, exceptions); co-operations are provided by the environment (heap state). Heap parameterization is precisely: turning heap operations into co-operations in FineGrainLaurel.

- **Ahman, D. & Uustalu, T.** (2019). "Decomposing Comonad Morphisms." *CALCO*.
  — Comodels for state effects. The heap as co-algebraic structure (state-passing arises from a comodel, not a model).

### Adequacy

- **Winskel, G.** (1993). *The Formal Semantics of Programming Languages.* MIT Press.
  — Manifest adequacy: compositional, syntax-directed correspondence between source and target derivations. Our elaboration (Laurel → FineGrainLaurel) should satisfy this.

### Nanopass / Compilation

- **Sarkar, D., Waddell, O. & Dybvig, R.K.** (2004). "A Nanopass Infrastructure for Compiler Education." *ICFP*.
  — The nanopass methodology. Each pass does one thing; representations between passes enforce invariants.

### Let-Floating / Projection

- **Peyton Jones, S., Partain, W. & Santos, A.** (1996). "Let-floating: moving bindings to give faster programs." *ICFP*.
  — Let float-out: inner bindings float to enclosing scope. Our FGCBV→CBV projection uses this (monadic bind associativity as let-floating). Soundness requires freshness of floated names.

### Metadata / Comonads

- **Uustalu, T. & Vene, V.** (2008). "Comonadic Notions of Computation." *ENTCS*, 203(5).
  — Comonads for structured computation. Our `WithMetadata` comonad and the monad-comonad interaction law draw from this.
