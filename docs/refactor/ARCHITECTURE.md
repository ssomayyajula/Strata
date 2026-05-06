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
e : Laurel.Program (impure CBV — precisely-typed, effects implicit)
  ↓ [elaborate: effect-passing translation — coercions, errors, heap made explicit]
e' : FineGrainLaurel.Program (enriched FGCBV — effects explicit)
  ↓ [project: effect calculus → impure language (trivial cata)]
Laurel.Program (effects re-implicit, coercions/bindings as Laurel nodes, ready for Core)
  ↓ [Core translation]
Core
```

The stratification is REPRESENTATIONAL: `Laurel.Program` and `FineGrainLaurel.Program`
are different Lean types. You cannot accidentally pass un-elaborated Laurel to Core —
the type system prevents it. FineGrainLaurel separates Values (pure expressions
including coercions) from Producers (effectful procedure calls, control flow, assignment).
Only procedures with `hasErrorOutput` produce true let-bindings.

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

## Elaboration (Effect-Passing Translation: Laurel → FineGrainLaurel)

**Input:** Laurel (impure CBV — effects implicit) + TypeEnv (= **Γ**)  
**Output:** FineGrainLaurel (enriched FGCBV — effects explicit)

### The Unifying Principle

**Laurel is an impure CBV language.** Effects (errors, heap state, coercions) are
implicit in the syntax. `f(x)` might throw, read the heap, or need a coercion —
you can't tell from the term alone.

**FineGrainLaurel is an effect calculus.** Each effect has an explicit implementation.
The effect structure is visible in the syntax.

**Elaboration is effect-passing translation:** it commits to an implementation
for each implicit effect, making them explicit in the target calculus. The target
is plain FGCBV (Levy 2003) — not enriched FGCBV. The only computation type is
`↑A` (producer of A). The methodology of translating impure CBV to FGCBV via
explicit effect passing follows Egger et al. 2014, but our target is simpler
(no linear computation types).

| Implicit in Laurel | Explicit in FGL | Mechanism |
|---|---|---|
| Error (procedure may throw) | Error-passing: `A × Error` | `prodCallWithError` (true let-binding) |
| Heap (field read/write, allocation) | State-passing: heap threaded as parameter | Signature rewriting + `readField`/`updateField` |
| Type mismatch at boundary | Partial function calls | `from_int(v)`, `Any_to_bool(v)` (inline values) |

Errors and heap are genuine effects made explicit via effect-passing translation.
Coercions are not effects — they're just value-level function calls inserted at
type boundaries by subsumption. They happen to be partial (narrowing has
preconditions), but they're bog-standard function application, not effect-passing.

**Elaboration is language-independent.** It knows about Laurel's type system and
FineGrainLaurel's requirements — nothing about Python specifically. If we translate
Java→Laurel or JS→Laurel, the *same* elaboration pass works unchanged.

This is the litmus test for what belongs in elaboration vs. resolution/translation:
- "Does this depend on Python's semantics?" → Resolution or translation
- "Does this depend only on Laurel's type system?" → Elaboration

### Two Type Systems (Type-Directed Compilation, Harper & Morrisett 1995)

Elaboration is a typed translation between two type systems:

**HighType** (Translation's output): Has `UserDefined "Foo"` — class identity.
**LowType** (FGL's type system): Has only `Composite` — uniform heap representation.
`UserDefined` is unrepresentable in LowType.

```lean
def eraseType : HighType → LowType
  | .UserDefined _ => .TCore "Composite"  -- ALL class instances → Composite
  | .TInt => .TInt  | .TBool => .TBool  | .TString => .TString
  | .TFloat64 => .TFloat64  | .TVoid => .TVoid  | .TCore n => .TCore n
```

### What is a Value vs a Producer?

In FGCBV, the distinction is about **elaboration effects**:

- **Values:** Pure expressions. No elaboration effects. Can be nested freely.
  Includes: literals, variables, pure function calls (no `hasErrorOutput`),
  coercions (both upcasts and narrowing — narrowing is partial but that's a
  verification concern, not a runtime control flow concern).

- **Producers:** Expressions with elaboration effects. Must be bound via `let`.
  Only: procedure calls with `hasErrorOutput = true` (produce error output),
  mutation (assignment), control flow (if, while, return, exit).

Pure function calls (arithmetic, coercions, field reads) are VALUES even though
they may be partial. Partiality is modeled via preconditions (`requires`), not
via error-value binding. The verifier handles it via SMT, not runtime branching.

### The Typing Rules

**Value synthesis (atoms + pure calls):**
```
───────────────        ─────────────────
Γ ⊢_v n ⇒ int         Γ ⊢_v x ⇒ Γ(x)

vᵢ ⇐ paramTyᵢ    f.hasErrorOutput = false
────────────────────────────────────────────
Γ ⊢_v f(v₁,...,vₙ) ⇒ returnType(f)              (pure call — stays nested)
```

**Value checking (subsumption — the ONLY value checking rule):**
```
Γ ⊢_v v ⇒ A    subsume(A, B) = coerce(c)
──────────────────────────────────────────
Γ ⊢_v c(v) ⇐ B
```

**Producer synthesis:**
```
vᵢ ⇐ paramTyᵢ    f.hasErrorOutput = true
──────────────────────────────────────────────
Γ ⊢_p f(v₁,...,vₙ) ⇒ returnType(f)              (effectful call — TRUE let)

─────────────────────────
Γ ⊢_p (new Foo) ⇒ Composite

v ⇐ Γ(x)
─────────────────────────
Γ ⊢_p (x := v) ⇒ TVoid

v ⇐ bool
─────────────────────────
Γ ⊢_p (assert v) ⇒ TVoid

v ⇐ bool
─────────────────────────
Γ ⊢_p (assume v) ⇒ TVoid

v ⇐ bool    Γ ⊢_p M ⇐ TVoid
─────────────────────────────
Γ ⊢_p (while v do M) ⇒ TVoid
```

**Producer checking:**
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

### The Unified Subsumption Function

One function, one table, three outcomes. No separate typesEqual/canUpcast/canNarrow:

```lean
inductive CoercionResult where
  | refl                                    -- A = A, no coercion
  | coerce (witness : FGLValue → FGLValue)  -- apply witness
  | unrelated                               -- type error

def subsume (actual expected : LowType) : CoercionResult :=
  match actual, expected with
  -- Reflexivity:
  | a, b => if a == b then .refl else
  -- Upcasts (infallible, value → value):
  | .TInt, .TCore "Any" => .coerce .fromInt
  | .TBool, .TCore "Any" => .coerce .fromBool
  | .TString, .TCore "Any" => .coerce .fromStr
  | .TFloat64, .TCore "Any" => .coerce .fromFloat
  | .TCore "Composite", .TCore "Any" => .coerce .fromComposite
  | .TCore "ListAny", .TCore "Any" => .coerce .fromListAny
  | .TCore "DictStrAny", .TCore "Any" => .coerce .fromDictStrAny
  | .TVoid, .TCore "Any" => .coerce (fun _ => .fromNone)
  | _, .TCore "Box" => .coerce (fun v => .staticCall "Box..Any" [upcastToAny v])
  -- Narrowing (partial, precondition-guarded, value → value):
  | .TCore "Any", .TBool => .coerce (fun v => .staticCall "Any_to_bool" [v])
  | .TCore "Any", .TInt => .coerce (fun v => .staticCall "Any..as_int!" [v])
  | .TCore "Any", .TString => .coerce (fun v => .staticCall "Any..as_string!" [v])
  | .TCore "Any", .TFloat64 => .coerce (fun v => .staticCall "Any..as_float!" [v])
  | .TCore "Any", .TCore "Composite" => .coerce (fun v => .staticCall "Any..as_Composite!" [v])
  | .TCore "Box", .TCore "Any" => .coerce (fun v => .staticCall "Box..AnyVal!" [v])
  -- Unrelated:
  | _, _ => .unrelated
```

Both upcast and narrowing produce VALUES. Narrowing is partial (precondition-guarded)
but that's a verification concern. No bindings introduced by coercion.

### Key Properties

- **Pure calls are values.** `PAdd(from_int(x), from_int(y))` is ONE nested value
  expression. No intermediate variables. Stays inline.
- **Only `hasErrorOutput` calls produce true lets.** These are the ONLY bindings
  that elaboration introduces (beyond user-written assignments/locals).
- **Narrowing is value-level.** `Any_to_bool(x)` is a value expression (partial
  function with precondition). Not a producer binding.
- **Projection is a trivial cata.** FGL maps directly to Laurel with no restructuring.
- **All coercion is value-level.** The `subsume` table decides everything.

### Coercion Table (validated against PythonRuntimeLaurelPart.lean)

**Subtyping (A <: B, infallible):**

| A | B | Witness | Source |
|---|---|---|---|
| int | Any | `from_int` | Prelude: `from_int (as_int : int)` on Any |
| bool | Any | `from_bool` | Prelude |
| str | Any | `from_str` | Prelude |
| real | Any | `from_float` | Prelude (note: `real` not `float64`) |
| Composite | Any | `from_Composite` | Prelude |
| ListAny | Any | `from_ListAny` | Prelude |
| DictStrAny | Any | `from_DictStrAny` | Prelude |
| TVoid | Any | `from_None` | Prelude |
| Any | Box | `Box..Any` | Generated (single Box constructor) |

**Narrowing (A ▷ B, partial/preconditioned):**

| A | B | Witness | Source |
|---|---|---|---|
| Any | bool | `Any_to_bool` | Prelude: explicit function (truthiness) |
| Any | int | `Any..as_int!` | DDM-generated partial accessor |
| Any | str | `Any..as_string!` | DDM-generated |
| Any | real | `Any..as_float!` | DDM-generated |
| Any | Composite | `Any..as_Composite!` | DDM-generated |
| Any | ListAny | `Any..as_ListAny!` | DDM-generated |
| Any | DictStrAny | `Any..as_Dict!` | DDM-generated |
| Box | Any | `Box..AnyVal!` | DDM-generated (infallible — single constructor) |

### Γ Extension at Binding Sites

Γ grows as elaboration descends under binders (standard type theory):
- Enter procedure → extend Γ with parameters
- Process `LocalVariable x : T` → extend Γ with `x : T` for continuation
- Uses `withReader` on the reader monad. No mutable state. One Γ.

### Heap (State-Passing Translation)

Heap is the state effect. The state-passing translation (Egger et al. 2014) makes
it explicit by threading the heap as a parameter:

- **Discovery:** Walk procedure bodies. FieldSelect on Composite, Assign to
  FieldSelect, New → mark procedure as heap-touching.
- **Propagation:** Fixpoint on call graph (transitive: if A calls heap-touching B,
  A is heap-touching too).
- **State-passing:** Add heap parameter to touching procedures. Calls to touching
  procedures pass and receive heap. Field accesses become `readField(heap, obj, field)` /
  `updateField(heap, obj, field, val)`.

This is the SAME operation as error-passing (`prodCallWithError`), just for a
different effect (state vs exceptions). Both are effect-passing translation:
- Error-passing: `f(args)` → `let [result, err] = f(args) in ...`
- State-passing: `f(args)` → `let (result, heap') = f(heap, args) in ...`

Field access: `readField(heap, obj, field)` is a VALUE (pure given explicit heap,
returns Box). To get concrete type: `Box → Any` via `Box..AnyVal!`, then
`Any → T` via narrowing witness.

### Metadata

Smart constructors: `mkLaurel md expr`. Process `.val`, keep `.md`. Synthesized
nodes inherit metadata from the input node that triggered them.

### Holes (Nondeterminism Effect)

Holes represent unknown/nondeterministic values. They are an elaboration effect —
elaboration translates them into forms Core can handle.

**Two kinds of Holes:**

- **Deterministic Hole** (`.Hole true`): "some fixed value of this type that we
  don't know." Used for unsupported constructs. Elaboration translates to a call
  to a freshly generated uninterpreted function (so SMT can reason about it).

- **Nondeterministic Hole** (`.Hole false`): "could be ANY value of this type."
  Used for for-loop havoc. Elaboration translates to a `LocalVariable` with no
  initializer (`none`), which Core emits as `.nondet` (havoced variable).

**Typing:**
- `Hole(some T)` synthesizes T (type stored in node)
- `Hole(none)` checks against context (takes whatever type is expected)

**After elaboration, no `.Hole` nodes remain in the output.** Core rejects them.
The effect-passing translation converts them:
- Deterministic → `StaticCall "$hole_N" [proc_inputs...]` (uninterpreted function)
- Nondeterministic → `LocalVariable freshVar ty none` (havoc)

This obsoletes both `inferHoleTypes` and `eliminateHoles` from the old pipeline.

### Heap (only when classes exist)

Heap type infrastructure (Composite, Field, Box, Heap, TypeTag) is ONLY added
to the program when classes/heap usage exists. For programs without classes,
no heap declarations are emitted — they would reference undefined types (Field,
Box) and break Core. `heapConstants.types` is NOT added unconditionally.

### What Elaboration Does NOT Do

- No Python-specific logic (language-independent)
- No administrative let-bindings (only true lets from hasErrorOutput + user code)
- No ANF transformation (pure calls stay nested)
- No type equality dispatch in the walk (subsume decides everything)

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
back into CBV. Since pure calls stay as values (no admin lets), projection is a
trivial catamorphism — map each FGL constructor to the corresponding Laurel constructor.

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

Narrowing (value → value, partial — precondition-guarded):
```
Γ ⊢_v v ⇒ A    A ▷ B ~~> n
─────────────────────────────
Γ ⊢_v n(v) ⇐ B
```
Narrowing is a VALUE checking rule (like subsumption). The witness `n` is a partial
function (e.g., `Any..as_int!` has precondition `Any..isfrom_int(v)`). Both upcast
and narrowing produce VALUES. The partiality is a verification concern — the verifier
emits a proof obligation, not a runtime error branch.

This means: ALL coercion is value-level. No coercion introduces bindings.
The ONLY producer form that introduces true bindings is `prodCallWithError`
(procedures with `hasErrorOutput = true`).

**Mode correctness invariants:**
- Synth: output type determined by inputs (Γ, form, or fixed TVoid)
- Check: expected type is INPUT from context, never conjured
- No type equality anywhere — TVoid in while body is a CHECK (semantic constraint)
- `M to x. N`: M SYNTHS (learn A for binding), N CHECKS against C from context
- Value subsumption + narrowing are the value checking FALLBACK
- The ONLY producer-level binding is `prodCallWithError` (hasErrorOutput procedures)
- All coercion (upcast AND narrowing) is value-level — no bindings introduced
- Partiality of narrowing is a verification concern, not an elaboration effect

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

**MODE CORRECTNESS PRINCIPLE: No type dispatch in the walk.**

All type comparisons flow through ONE function: `subsume(actual, expected)`.
It returns `refl`, `coerce witness`, or `unrelated`. No separate equality check.
No pattern matching on specific types in the elaboration walk.

Specifically NEVER:
- `if expectedType == .TVoid then ...` (TVoid constructs SYNTH, not CHECK)
- `if actualType == .TBool then ...` (the subsume table handles this)
- `match expectedType with | .TInt => ... | .TBool => ...` (that's type dispatch)

The `subsume` table is the ONLY mechanism for relating types. If `subsume` returns
`unrelated`, that's a type error — not a case to handle with ad-hoc logic.

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

The subsumption/narrowing rules APPLY these witnesses (both VALUE checking rules):

```
-- Value subsumption (upcast — infallible):
Γ ⊢_v v ⇒ A    A <: B ~~> c
─────────────────────────────
Γ ⊢_v c(v) ⇐ B                  (value in, value out)

-- Narrowing (downcast — partial, precondition-guarded):
Γ ⊢_v v ⇒ A    A ▷ B ~~> n
─────────────────────────────
Γ ⊢_v n(v) ⇐ B                  (value in, value out, may have precondition)
```

Key: BOTH are value checking rules. BOTH take a value and produce a value.
Narrowing is partial (the witness `n` may have a `requires` precondition) but
this is a VERIFICATION concern, not an elaboration concern. Elaboration inserts
the correct call; the verifier proves the precondition.

`subsume` returns `refl`, `coerce witness`, or `unrelated`.
The coercion table is the collection of all witnesses. ALL coercion is value-level.
No coercion introduces bindings.

All coercion operates on VALUES. If you need to coerce a producer's result, BIND
it first (`M to x.`), then apply the witness to `x` (a value). Producer checking
has its own rules (if, var-bind, M-to-x, return) plus narrowing as fallback.

Narrowing produces a VALUE directly: `n(v) : Value(B)`. No binding needed.
The result is used inline (e.g., `Any_to_bool(x)` as a condition expression).

### The Complete Coercion Table (validated against PythonRuntimeLaurelPart.lean)

**Subtyping (A <: B ~~> c : Value(A) → Value(B), infallible):**

| A | B | Witness `c` | Source |
|---|---|---|---|
| int | Any | `from_int` | Prelude: `from_int (as_int : int)` on Any |
| bool | Any | `from_bool` | Prelude: `from_bool (as_bool : bool)` on Any |
| str | Any | `from_str` | Prelude: `from_str (as_string : string)` on Any |
| real | Any | `from_float` | Prelude: `from_float (as_float : real)` on Any |
| Composite | Any | `from_Composite` | Prelude: `from_Composite (as_Composite: Composite)` on Any |
| ListAny | Any | `from_ListAny` | Prelude: `from_ListAny (as_ListAny : ListAny)` on Any |
| DictStrAny | Any | `from_DictStrAny` | Prelude: `from_DictStrAny (as_Dict: DictStrAny)` on Any |
| TVoid | Any | `from_None` | Prelude: `from_None ()` on Any |
| Any | Box | `Box..Any` | Generated: `Box..Any(AnyVal : Any)` — single Box constructor |

**Narrowing (A ▷ B ~~> n : Value(A) → Producer(B), fallible):**

| A | B | Witness `n` | Source |
|---|---|---|---|
| Any | bool | `Any_to_bool` | Prelude: explicit function (truthiness, not just unwrap) |
| Any | int | `Any..as_int!` | DDM-generated partial accessor |
| Any | str | `Any..as_string!` | DDM-generated partial accessor |
| Any | real | `Any..as_float!` | DDM-generated partial accessor (note: `real` not `float64`) |
| Any | Composite | `Any..as_Composite!` | DDM-generated partial accessor |
| Any | ListAny | `Any..as_ListAny!` | DDM-generated partial accessor |
| Any | DictStrAny | `Any..as_Dict!` | DDM-generated partial accessor |
| Box | Any | `Box..AnyVal!` | DDM-generated (infallible — single constructor, always succeeds) |

**Note on Box:** The old pipeline generates `Box` with a SINGLE constructor
`Box..Any(AnyVal: Any)`. All fields stored as `Any`. This means:
- Field write: `updateField(heap, obj, field, Box..Any(from_T(val)))` — upcast to Any, wrap in Box
- Field read: `Box..AnyVal!(readField(heap, obj, field))` → `Any`, then narrow `Any ▷ T`
- `Box..AnyVal!` is technically infallible (single constructor) — could be modeled as subtype

**Note on float:** The prelude uses `real` (not `float64`) for the float field on Any.
Our `HighType.TFloat64` maps to `real` in Core. The narrowing accessor is `Any..as_float!`.

**FieldSelect (on Composite objects):**
- `FieldSelect obj field` synthesizes type `Box` (value-level, pure given heap)
- Implementation: `readField(heap, obj, field)` — pure StaticCall returning `Box`
- To use the field value as type T: `Box..AnyVal!(readField(...))` then `Any ▷ T`
- This is two subsumption steps chained: `Box → Any → T`

**Coercions go at the USE SITE** (argument position, condition position, return),
NOT at the definition site. `var x: int := 5` → no coercion (int = int, reflexivity).
`PAdd(x, y)` where PAdd expects Any → `from_int(x)` at the call boundary.

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

### Effect-Passing: Local vs Global

All three effects are handled by the same methodology (effect-passing translation).
The difference is SCOPE — whether the effect can be resolved locally or requires
global program analysis:

| Effect | Scope | What elaboration does |
|---|---|---|
| Coercions | Local | Insert witness at CHECK boundary (inline) |
| Exceptions (error output) | Local | Insert `prodCallWithError` at call site |
| Heap (state) | **Global** | Discover locally, propagate through call graph, rewrite signatures |

Local effects are resolved during the bidirectional walk: encounter a boundary,
insert the appropriate node, move on.

The heap effect requires global analysis because it's TRANSITIVE: if procedure A
calls procedure B, and B touches the heap, then A must also receive a heap parameter
(even if A doesn't directly touch the heap). This requires a fixpoint computation
on the call graph AFTER the local walk.

Implementation: elaboration has two sub-phases:
1. **Local walk** (bidirectional synth/check): inserts coercions + error bindings,
   discovers heap-touching procedures
2. **Global propagation** (fixpoint on call graph): state-passing translation for heap

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
- `Any ▷ Composite` via `Any..as_Composite!` (narrowing: value→value, partial — precondition-guarded)

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
combines the state monad (heap threading via state-passing) with the exception monad
(error sum via error-passing) in a single `T`. Standard treatment: Levy 2004 Ch.5, 
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

### Projection: Effect Calculus → Impure Language (Trivial)

Going from an effect calculus (FGL) to an impure language (Laurel) is trivial —
the impure language already handles effects implicitly. Projection just forgets
the explicit effect structure and lets the impure semantics take over.

Concretely: forget the Value/Producer polarity distinction. Map each FGL
constructor to the corresponding Laurel constructor. No restructuring, no hoisting,
no collapsing — because elaboration didn't introduce administrative structure.
Only true lets (from hasErrorOutput + user code) appear in the output.

```
projectValue : FGLValue → StmtExprMd
  litInt n        → LiteralInt n
  litBool b       → LiteralBool b
  litString s     → LiteralString s
  var x           → Identifier x
  fromInt v       → StaticCall "from_int" [projectValue v]
  fromBool v      → StaticCall "from_bool" [projectValue v]
  ...
  staticCall f vs → StaticCall f (vs.map projectValue)
  fieldAccess o f → FieldSelect (projectValue o) f

projectProducer : FGLProducer → StmtExprMd
  -- True lets (from hasErrorOutput calls):
  callWithError f args rv ev rTy eTy body →
    Block [LocalVariable rv Any Hole; LocalVariable ev Error (StaticCall "NoError" []);
           Assign [rv, ev] (StaticCall f (args.map projectValue));
           projectProducer body]
  -- User assignments/locals:
  assign target val body → Block [Assign [projectValue target] (projectValue val);
                                   projectProducer body]
  varDecl x ty init body → Block [Assign [Identifier x] (projectValue init);
                                    projectProducer body]
  -- Control flow:
  ifThenElse c t e → IfThenElse (projectValue c) (projectProducer t) (projectProducer e)
  whileLoop c body after → Block [While (projectValue c) [] none (projectProducer body);
                                    projectProducer after]
  assert c body → Block [Assert (projectValue c); projectProducer body]
  assume c body → Block [Assume (projectValue c); projectProducer body]
  exit label → Exit label
  returnValue v → projectValue v  (terminal expression)
  ...
```

**Projected variable types use their actual LowType.** Precise types from elaboration
Projection uses `liftType` to convert LowType back to HighType for
variable declarations. No type erasure in projection.

**Uninitialized variables use `Hole`.** Core expects `<?>` for declarations without
a meaningful initial value.

### Why Projection is Trivial

Because elaboration doesn't introduce administrative lets. Pure calls stay nested
(they're values). Coercions are inline (they're value-level expressions). The ONLY
bindings are:
1. User-written `LocalVariable` declarations (from Translation's scope hoisting)
2. User-written `Assign` statements
3. `prodCallWithError` bindings (from hasErrorOutput procedures)

These map directly to Laurel's existing AST forms. No bind reassociation needed.
No let-floating. No two-pass hoisting.

### Exception Handling: prodCallWithError

The ONLY elaboration-introduced binding. When Γ says `f.hasErrorOutput = true`:
- Elaboration emits `prodCallWithError f [args] resultVar errorVar ...`
- Projection maps this to Laurel's multi-output assignment:
  ```
  resultVar, errorVar := f(args)
  if isError(errorVar) then ... else ...
  ```

This is the monadic bind for `T(A) = A × Error`. The projected form is Laurel's
convention for error-producing procedures.

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

The `subsume` function crosses the boundary: `checkValue` erases the expected
HighType via `eraseType` before calling `subsume(actual, expectedLow)`. When the
source type is `UserDefined _`, eraseType gives `TCore "Composite"`, and
`subsume(.TCore "Composite", .TCore "Any")` returns the `from_Composite` witness.

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

## Non-Goals

- **Untyped Python.** Missing annotations → `Any`. No inference.
- **Aliasing.** Documented assumption: no aliasing of composite values.
- **Laurel/Core changes.** Existing infrastructure unchanged.
- **Optimization.** Correctness first (except stub loading — see above).

---

### Known Tech Debt: Narrowing as Pure Function

Treating narrowing (downcasting) as a pure value-level function is a simplification.
In Python, casts can in general have effects — e.g., `__bool__` can execute arbitrary
code, `__int__` can have side effects. We model narrowing witnesses (`Any_to_bool`,
`Any..as_int!`, etc.) as partial functions with preconditions. The verifier checks the
precondition via SMT; Core doesn't branch on it at runtime.

If we later need to model cast effects (because a user's `__bool__` touches the heap
or throws), narrowing would need to become a producer with error handling. That changes
the entire coercion scheme: `subsume` would need to distinguish infallible (value)
from fallible (producer) coercions, and projection would need to emit bindings for
narrowing results. For now this is acceptable because:
1. The prelude's `Any_to_bool` is a pure function (defined without side effects)
2. The DDM accessors (`Any..as_int!`) are compiler-generated and pure
3. User-defined `__bool__`/`__int__` overrides would require PySpec stub support first

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

- **Egger, J., Møgelberg, R.E. & Simpson, A.** (2014). "The enriched effect calculus: syntax and semantics." *J. Logic and Computation*.
  — Effect-passing translation from impure CBV to FGCBV. Our elaboration follows this methodology (translate implicit effects to explicit effect calculus), though our target is plain FGCBV (no linear computation types).

### Adequacy

- **Winskel, G.** (1993). *The Formal Semantics of Programming Languages.* MIT Press.
  — Manifest adequacy: compositional, syntax-directed correspondence between source and target derivations. Our elaboration (Laurel → FineGrainLaurel) should satisfy this.

### Nanopass / Compilation

- **Sarkar, D., Waddell, O. & Dybvig, R.K.** (2004). "A Nanopass Infrastructure for Compiler Education." *ICFP*.
  — The nanopass methodology. Each pass does one thing; representations between passes enforce invariants.

### Compilation

- **Harper, R. & Morrisett, G.** (1995). "Compiling Polymorphism Using Intensional Type Analysis." *POPL*.
  — Type-directed compilation. Our elaboration translates between two type systems (HighType → LowType) guided by the types, following this methodology.

### Metadata / Comonads

- **Uustalu, T. & Vene, V.** (2008). "Comonadic Notions of Computation." *ENTCS*, 203(5).
  — Comonads for structured computation. Our `WithMetadata` comonad and the monad-comonad interaction law draw from this.
