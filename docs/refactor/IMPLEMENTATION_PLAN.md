# Implementation Plan: Derived from ARCHITECTURE.md

This plan is a SYSTEMATIC DERIVATION of the architecture. Each section references
the architecture doc and specifies what code implements it, what's missing, and how
to fix it. If the architecture doesn't say it, we don't do it.

Reference: `docs/refactor/ARCHITECTURE.md` (the single source of truth)

---

## OPERATIONAL DISCIPLINE

### Failure Mode (what keeps happening)
Agents abandon the architecture when they hit difficulty. They cheat (type as Any,
skip elaboration, add boolean gates). Review catches it, we kill, we restart.

### Prevention
1. Every implementation agent gets a PARALLEL review agent
2. Review agent greps for architecture violations (see Compliance Checks below)
3. Violations → immediate kill
4. Killed agent's transcript is read for lessons → next agent gets those lessons
5. Agents MUST run `diff_test.sh` (full suite), not individual tests
6. Agents MUST commit after every successful `lake build`

### Compliance Checks
```bash
grep -n "from_int\|from_str\|from_bool\|Any_to_bool" Translation.lean     # VIOLATION (coercions)
grep -n "SKIP\|skip\|disabled" PySpecPipeline.lean                         # VIOLATION (skipped elab)
grep -n "isPrelude\|isUserFunc" Elaborate.lean                             # VIOLATION (boolean gate)
grep -n "returnType.*:=.*TCore.*Any" Translation.lean                      # VIOLATION (hardcoded Any)
```

### Git Hygiene
- Every `lake build` success → `git commit`
- Broken build → `git checkout -- .` immediately
- Commit format: `[refactor] <what> (<test result>)`
- Never commit broken builds, never commit without building

---

## SUBTYPING AND NARROWING DISCIPLINE

This defines WHEN elaboration coerces and in WHICH direction. Two SEPARATE relations,
not gradual typing's mathematically questionable "consistency."

### Subtyping (A <: B) — Infallible, Value-Level

A value of type A IS a value of type B. The coercion is a pure injection (value in,
value out). It always succeeds.

```
int <: Any          (via valFromInt — inject int into Any sum)
bool <: Any         (via valFromBool)
str <: Any          (via valFromStr)
float <: Any        (via valFromFloat)
ListAny <: Any      (via valFromListAny)
DictStrAny <: Any   (via valFromDictStrAny)
Composite <: Any    (via valFromComposite)
TVoid <: Any        (via valFromNone)
A <: A              (reflexive — no coercion)
```

Properties:
- Reflexive: A <: A
- NOT transitive across Any: int <: Any does NOT give int <: bool
- Any is the TOP of the value lattice
- Concrete types are UNRELATED to each other (int ⊄ bool, str ⊄ int)

In the bidirectional walk: when CHECK finds `synth(e) = A` and `expected = B` with `A <: B`:
```
Γ ⊢_v e ⇒ A    A <: B
─────────────────────────
Γ ⊢_v coerce(e) ⇐ B        (emit valFromA(e) — stays in value judgment)
```

### Narrowing (A ▷ B) — Fallible, Producer-Level

A value of type A can be TESTED to have type B. The coercion is a computation that
may fail (throw TypeError). Value in, PRODUCER out.

```
Any ▷ bool          (via Any_to_bool — may throw TypeError)
Any ▷ int           (via Any..as_int! — may throw TypeError)
Any ▷ str           (via Any..as_string! — may throw TypeError)
Any ▷ float         (via Any..as_float! — may throw TypeError)
Any ▷ Composite     (via Any..as_Composite! — may throw TypeError)
```

Properties:
- NOT reflexive (A ▷ A is meaningless — you already have A)
- NOT symmetric (int ▷ Any makes no sense)
- Only defined FROM Any TO concrete types (it's sum elimination)
- Each narrowing is a PRODUCER (can fail → effect)

In the bidirectional walk: when CHECK finds `synth(e) = Any` and `expected = B` with `Any ▷ B`:
```
Γ ⊢_v e ⇒ Any    Any ▷ B
─────────────────────────────
Γ ⊢_p narrow(e) : B           (emit Any_to_B(e) — JUMPS to producer judgment)
```

### The Two Relations are NOT Inverses

- `int <: Any` (subtyping: value→value, infallible)
- `Any ▷ int` (narrowing: value→producer, fallible)

They're asymmetric: going UP is free (just tag it), going DOWN costs (must check the tag).
There is no "consistency" that relates them symmetrically.

### The Coercion Table

| actual | expected | relation | coercion function | FGL judgment |
|--------|----------|----------|-------------------|--------------|
| int | Any | A <: B (subtype) | `valFromInt` | ⊢_v (value→value) |
| bool | Any | A <: B | `valFromBool` | ⊢_v |
| str | Any | A <: B | `valFromStr` | ⊢_v |
| float | Any | A <: B | `valFromFloat` | ⊢_v |
| ListAny | Any | A <: B | `valFromListAny` | ⊢_v |
| DictStrAny | Any | A <: B | `valFromDictStrAny` | ⊢_v |
| Composite | Any | A <: B | `valFromComposite` | ⊢_v |
| TVoid | Any | A <: B | `valFromNone` | ⊢_v |
| Any | bool | A ▷ B (narrow) | `Any_to_bool` | ⊢_p (value→producer) |
| Any | int | A ▷ B | `Any..as_int!` | ⊢_p |
| Any | str | A ▷ B | `Any..as_string!` | ⊢_p |
| Any | float | A ▷ B | `Any..as_float!` | ⊢_p |
| Any | Composite | A ▷ B | `Any..as_Composite!` | ⊢_p |
| T | T | A = B (equal) | none | — |
| int | str | unrelated | ERROR | — |
| int | bool | unrelated | ERROR | — |

### When Coercions Fire (Bidirectional Integration)

Per Dunfield & Krishnaswami §4.4 (subsumption rule):

```
Γ ⊢ e ⇒ A    A ≠ B    A ~ B
─────────────────────────────────
Γ ⊢ e ⇐ B    ~~>  coerce(A, B, e)
```

Elaboration encounters this at:
1. **Function arguments:** `f(x)` where f expects `Any` but x has type `int` → `valFromInt(x)`
2. **Assignments:** `var x: Any := lit` where lit has type `int` → `valFromInt(lit)`
3. **Returns:** `return x` where return type is `Any` but x is `int` → `valFromInt(x)`
4. **Conditions:** `if cond ...` where cond has type `Any` → `Any_to_bool(cond)` (downcast to bool)
5. **Never at definition:** `var x: int := 5` → int = int, no coercion

### Upcast vs Downcast: Value vs Producer

**Upcasts are VALUE operations** (they're pure injections into the `Any` sum type):
- `from_int(5)` = tagging an int as `Any`. Always succeeds. Like `inl(5) : int + str`.
- In FGL: `valFromInt (valLiteralInt 5)` → a VALUE, no binding needed.
- In the dialect: `op valFromInt (inner: Value): Value => "from_int(" inner ")"` 

**Downcasts are the effectful opposite of subtyping.** They consume a VALUE and
produce a PRODUCER at the target type:

```
Γ ⊢_v V : Any
─────────────────────────────────
Γ ⊢_p Any_to_bool(V) : bool        (a PRODUCER of bool — may throw TypeError)
```

The entire downcast expression is a PRODUCER at the downcasted type. It takes a
value in (the Any-typed thing) and the whole thing is a producer (because it might
fail). The typing:

- `Any_to_bool : Value(Any) → Producer(bool)`
- `Any..as_int! : Value(Any) → Producer(int)`
- `Any..as_Composite! : Value(Any) → Producer(Composite)`

Contrast with upcasts which stay in the value judgment:

```
Γ ⊢_v V : int
─────────────────────────────────
Γ ⊢_v valFromInt(V) : Any          (a VALUE of Any — always succeeds)
```

**In the bidirectional walk:** when `check(e, bool)` finds `synth(e) = Any`:
- `e` elaborates to some Value `V : Any` (via value synthesis)
- The check emits `Any_to_bool(V)` which is a PRODUCER of type `bool`
- The caller (already in producer context) sequences this via `M to x. N`
- `x` is now a VALUE variable of type `bool` — usable downstream

This is the FGCBV semantics: downcasts introduce effects. Effects live in the
producer judgment. To get back to a value, you bind with `M to x.`

### Heap Is NOT a Coercion

The Heap parameter is a CO-OPERATION (Bauer 2018), not a coercion:
- It doesn't appear in the coercion table
- It's discovered during the local walk (FieldSelect, field assign, .New)
- It's propagated globally (fixpoint on call graph)
- It changes procedure SIGNATURES (not individual expressions)

The walk marks procedures as "heap-touching." The propagation phase threads Heap.
This is separate from the coercion discipline.

---

## ARCHITECTURE SECTION → IMPLEMENTATION MAPPING

### §"The Pipeline" (lines 52-68)

Architecture specifies:
```
Python AST + library stubs (.python.st.ion)
  → [resolve: build Γ]                              → TypeEnv
  → [translate: fold, type-directed]                 → HighLaurel
  → [elaborate: derivation transformation]           → FineGrainLaurel
  → [project: DDM-generated]                         → MidLaurel
  → [lower: flatten, inferHoles, filterPrelude]      → LowLaurel
  → [Core translation]                               → Core
```

**Implementation status:**
- [x] resolve: `NameResolution.lean` exists, produces TypeEnv ✓
- [x] translate: `Translation.lean` exists ✗ (violates: does coercions inline)
- [ ] elaborate: `Elaborate.lean` exists ✗ (SKIPPED in pipeline, operates on StmtExprMd not FGL types)
- [ ] FineGrainLaurel types: `#strata_gen` NOT called, Value/Producer types don't exist
- [ ] project: does not exist (no FGL → Laurel projection)
- [x] lower: uses existing `translateCombinedLaurelWithLowered` ✓
- [x] Core: unchanged ✓
- [ ] stub loading: not implemented (only prelude, no library stubs)

**Tasks derived:**
1. Generate FGL types (`#strata_gen FineGrainLaurel`)
2. Strip coercions from Translation
3. Rewrite Elaborate to produce FGL types
4. Write projection (FGL → Laurel)
5. Enable elaboration in pipeline
6. Add stub loading to pipeline

---

### §"Resolution (Building Γ)" (lines 121-169)

Architecture specifies:
- TypeEnv with: names, classFields, overloadTable, builtinMap
- NameInfo: class_ | function | variable
- FuncSig: name, params, defaults, returnType, hasErrorOutput, hasKwargs
- One mechanism for user code AND stubs
- Every name has an entry after resolution

**Implementation status:**
- [x] TypeEnv structure: `NameResolution.lean` has all fields ✓
- [x] NameInfo variants: class_, function, variable, module_ ✓
- [x] FuncSig: all fields present ✓
- [x] buildTypeEnv from AST ✓
- [x] Prelude signatures ✓
- [ ] Stub loading: NOT implemented (architecture says "one mechanism for user code and stubs")
- [ ] overloadTable: exists but never populated from stubs
- [x] builtinMap: populated with 31 entries ✓

**Tasks derived:**
7. Implement stub loading (parse stub .python.st.ion → buildTypeEnv → merge)

---

### §"Translation (Producing e)" (lines 173-253)

Architecture specifies:
- Fold over Python AST
- Reads annotations for types (NEVER defaults to Any when annotation exists)
- NO coercions (no from_int, from_str, Any_to_bool)
- NO literal wrapping
- Deterministic mappings (one constructor → one Laurel node)
- Python-specific desugarings: scope hoisting, kwargs, mutable params, .New+__init__, context managers, for-loop abstraction, loop labels

**Implementation status:**
- [x] Fold structure ✓
- [x] Scope hoisting ✓
- [x] Loop labels ✓
- [x] Object construction (.New + __init__) ✓
- [x] Context managers (Type@__enter__/Type@__exit__) ✓
- [x] For-loop abstraction (havoc + assume) ✓
- [x] builtinMap lookup ✓
- [x] Module import resolution (re.fullmatch → re_fullmatch) ✓
- [x] User error detection (unknown method on known class) ✓
- [✗] VIOLATES: from_int/from_str/from_bool wrapping literals (lines 300-325)
- [✗] VIOLATES: Any_to_bool wrapping conditions (lines 795, 811, 817, 865, 908)
- [✗] VIOLATES: Parameters default to Any when annotation isn't a known class (line 1232)
- [✗] VIOLATES: Return type hardcoded to Any (line 1263)
- [✗] VIOLATES: maybe_except/isError protocol in try/except (lines 950-998)

**Tasks derived:**
8. Remove from_int/from_str/from_bool wrapping from literals
9. Remove Any_to_bool wrapping from conditions
10. Fix parameter types: use pythonTypeToLaurel for ALL annotations, not just classes
11. Fix return types: read return annotation
12. Remove maybe_except/isError from Translation (elaboration handles this via prodCallWithError)

---

### §"Elaboration" (lines 257-478)

Architecture specifies:
- Language-independent (no Python-specific logic)
- Bidirectional typing (Dunfield & Krishnaswami recipe): introductions CHECK, eliminations SYNTH
- Subsumption at boundaries: coerce when synth type ≠ expected type
- Single mechanism: prodCallWithError for ALL effectful operations
- Operations (local): coercions, exceptions, ANF (let-binding)
- Co-operations (global): heap threading
- Two sub-phases: local walk + global propagation

**Implementation status:**
- [x] Bidirectional walk exists (synth/check) ✓
- [x] Coercion insertion (upcast/downcast function names) ✓
- [x] Heap analysis + propagation exists (Phase 2) ✓
- [x] Type hierarchy (New → MkComposite) exists (Phase 3) ✓
- [✗] VIOLATES: Elaboration is SKIPPED in pipeline (line 474 PySpecPipeline)
- [✗] VIOLATES: Operates on StmtExprMd not FGL Value/Producer types
- [✗] VIOLATES: from_int modeled as prodCall (architecture + theory say it's a VALUE operation)
- [✗] Missing: prodCallWithError for error-producing calls
- [✗] Missing: Short-circuit desugaring as part of the walk (partially done, was reverted)

**Tasks derived:**
13. Generate FGL types (prerequisite for everything else)
14. Rewrite elaboration to produce FGL.Value / FGL.Producer
15. Add valFromInt/valFromStr/valFromBool as VALUE operators in dialect
16. Implement prodCallWithError for hasErrorOutput procedures
17. Enable elaboration in pipeline (remove SKIP)
18. Add short-circuit desugaring back to elaboration walk

---

### Elaboration API: Four Functions (per Lakhani & Pfenning's four judgments)

```lean
-- Synthesize a VALUE from a Laurel expression (infer its type)
def synthValue (expr : Laurel.StmtExprMd) : ElabM (FGL.Value × HighType)

-- Check a Laurel expression AS a VALUE against expected type (insert upcast if needed)
def checkValue (expr : Laurel.StmtExprMd) (expected : HighType) : ElabM FGL.Value

-- Synthesize a PRODUCER from a Laurel expression (infer what it produces)
def synthProducer (expr : Laurel.StmtExprMd) : ElabM (FGL.Producer × HighType)

-- Check a Laurel expression AS a PRODUCER against expected type (insert downcast if needed)  
def checkProducer (expr : Laurel.StmtExprMd) (expected : HighType) : ElabM FGL.Producer
```

**Which Laurel constructors are values vs producers:**
- Values: LiteralInt, LiteralBool, LiteralString, Identifier, FieldSelect
- Producers: StaticCall, Assign, Block, IfThenElse, While, Return, Assert, Assume, New

**Mode transitions:**
- Value needed but have Producer → bind: `prodLetProd fresh ty prod (continue with valVar fresh)`
- Producer needed but have Value → wrap: `prodReturnValue val`
- Upcast (value → value): `valFromInt val` (stays in value judgment)
- Downcast (value → producer): `Any_to_bool val` (jumps to producer judgment)

### Blocks as Nested Lets (CBV → FGCBV Embedding, Levy §3.2)

`Block [s1, s2, s3]` becomes nested producers:

```
-- Block [x := 5, y := PAdd(x, 3), return y]
prodLetProd "x" int (prodReturnValue (valLiteralInt 5))
  (prodLetProd "y" Any (prodCall "PAdd" [valFromInt (valVar "x"), valFromInt (valLiteralInt 3)])
    (prodReturnValue (valVar "y")))
```

Each statement is a producer. Sequencing is `prodLetProd` (= `M to x. N`).
Implementation: `foldr` over statement list, accumulating continuation.

The standard CBV → FGCBV embedding (Levy et al. 2003 §3.2):
- `(M, N)` → `M to x. N to y. produce (x, y)`
- `M N` → `M to f. N to a. f a`  
- `let x = M in N` → `M to x. N`

### Worked Example: `PAdd(x, 5)` where `x: int`, PAdd expects `(Any, Any) → Any`

**Laurel input (from Translation):**
```
StaticCall "PAdd" [Identifier "x", LiteralInt 5]
```

**Elaboration (producer mode — we're in a procedure body):**

1. `synthProducer(StaticCall "PAdd" [Identifier "x", LiteralInt 5])`
2. Look up "PAdd" in Γ → `FuncSig { params: [(Any, Any)], returnType: Any }`
3. For each arg, call `checkValue(arg, paramType)`:
   - `checkValue(Identifier "x", Any)`:
     - `synthValue(Identifier "x")` → `(valVar "x", int)` (from Γ)
     - `int ≠ Any`, upcast needed → return `valFromInt(valVar "x")` : Value(Any) ✓
   - `checkValue(LiteralInt 5, Any)`:
     - `synthValue(LiteralInt 5)` → `(valLiteralInt 5, int)`
     - `int ≠ Any`, upcast needed → return `valFromInt(valLiteralInt 5)` : Value(Any) ✓
4. Emit: `prodCall "PAdd" [valFromInt(valVar "x"), valFromInt(valLiteralInt 5)]` : Producer(Any)

**FGL output:**
```
prodCall "PAdd" [valFromInt (valVar "x"), valFromInt (valLiteralInt 5)]
```

### Worked Example: `assert x > 0` where `x: int`

**Laurel input:**
```
Assert (StaticCall "PGt" [Identifier "x", LiteralInt 0])
```

**Elaboration (producer mode):**

1. `synthProducer(Assert condExpr)`
2. Assert needs `cond : bool`. So: `checkProducer(condExpr, bool)`
3. `checkProducer(StaticCall "PGt" [x, 0], bool)`:
   - `synthProducer(StaticCall "PGt" [x, 0])` → `(prodCall "PGt" [...], Any)`
   - `Any ≠ bool`, downcast needed
   - Downcast: `Any_to_bool` takes a Value, but we have a Producer!
   - So: bind the producer first: `prodLetProd "tmp" Any (prodCall "PGt" [...]) (Any_to_bool (valVar "tmp"))`
   - Result: Producer(bool) ✓
4. Now we have `cond : Producer(bool)`. Assert needs a Value(bool).
   - Bind again: `prodLetProd "cond" bool <the above> (prodAssert (valVar "cond") continuation)`

**FGL output:**
```
prodLetProd "tmp" Any (prodCall "PGt" [valFromInt (valVar "x"), valFromInt (valLiteralInt 0)])
  (prodLetProd "cond" bool (prodCall "Any_to_bool" [valVar "tmp"])
    (prodAssert (valVar "cond") continuation))
```

### Entry Point: Procedure Body

A procedure body is always elaborated in PRODUCER mode:
```lean
def elaborateProcBody (body : Laurel.StmtExprMd) : ElabM FGL.Producer :=
  synthProducer body |>.map (·.1)
```

The body is a `Block [stmts]` → becomes nested `prodLetProd` via `foldr`.
Arguments to calls → `checkValue` (value mode).
Conditions → `checkProducer` then bind to get value for assert/assume.

---

### §"Projection" (lines 555-688)

Architecture specifies:
- FineGrainLaurel → Laurel (the forgetful functor)
- DDM-generated (automatic)
- Erases polarity, keeps inserted coercions/let-bindings as Laurel nodes
- Total, meaning-preserving, unique

**Implementation status:**
- [ ] Does not exist. No projection function. No FGL → Laurel mapper.
- [ ] Can't be DDM-generated until FGL types exist

**Tasks derived:**
19. Write projection function (FGL.Value → StmtExprMd, FGL.Producer → StmtExprMd)
    (May need to be hand-written since DDM projection may not exist for this dialect)

---

### §"Types and Coercions" (lines 713-730)

Architecture specifies:
- Core has NO subtyping (HM unification: int ≠ Any)
- Translation emits precise types
- Elaboration inserts from_int when int meets Any boundary
- After elaboration, all boundaries correctly bridged
- Elaboration must elaborate ALL calls uniformly (no isPreludeFunc gate)

**Implementation status:**
- [✗] Translation still wraps literals (not precise types → coercions inline)
- [✗] Elaboration skipped
- [x] isPreludeFunc gate removed ✓ (earlier fix)

**Tasks derived:** (same as §Translation and §Elaboration tasks above)

---

### §"Library Stubs" (lines 739-776)

Architecture specifies:
- Stubs are Python files → same buildTypeEnv
- One mechanism for user code and stubs
- Resolution extracts assert statements as FuncSig.preconditions
- @overload + Literal annotations → overloadTable

**Implementation status:**
- [ ] Not implemented at all
- [ ] buildTypeEnv doesn't extract preconditions from assert statements
- [ ] No stub file loading in V2 pipeline
- [ ] overloadTable never populated from stubs

**Tasks derived:**
20. Extend buildTypeEnv to extract assert preconditions from function bodies
21. Add stub file loading to V2 pipeline (Step 0: load stubs → merge into Γ)
22. Populate overloadTable from @overload annotations in stubs

---

### §"Laurel Stratification" (lines 888-927)

Architecture specifies (open question):
- HighLaurel / MidLaurel / LowLaurel are same Lean type today
- Structural invariants should ideally be representational (separate types)
- Current decision: document invariants, satisfy them

**Implementation status:**
- [x] Documented in architecture ✓
- [✗] HighLaurel output invariants not fully specified (we hit "block expression not lowered" errors earlier)

**Tasks derived:**
23. Once FGL types exist, the stratification is representational BY CONSTRUCTION (FGL IS the separate type)

---

### §"Break/Continue Labels" (lines 804-822)

Architecture specifies:
- Translation-internal loop label stack
- Push fresh label on For/While entry
- Break → Exit breakLabel, Continue → Exit continueLabel
- Pop on exit

**Implementation status:**
- [x] Implemented ✓ (Task 1 completed earlier)

---

### §"Instance Procedure Workaround" (lines 961-982)

Architecture specifies:
- Methods as top-level static procedures with self as first param
- instanceProcedures := [] on CompositeType
- Qualified names: ClassName@methodName

**Implementation status:**
- [x] instanceProcedures := [] ✓
- [x] Methods in staticProcedures ✓
- [x] Qualified names ✓

---

### §"Prelude Data Type Encodings" (lines 984-1007)

Architecture specifies:
- Lists: ListAny_cons/ListAny_nil (wrapped in from_ListAny)
- Dicts: DictStrAny_cons/DictStrAny_empty (wrapped in from_DictStrAny)
- Tuples: same as lists
- f-strings: to_string_any
- str(): to_string_any via builtinMap

**Implementation status:**
- [x] Lists: from_ListAny(ListAny_cons(...)) ✓
- [x] Dicts: from_DictStrAny(DictStrAny_cons(...)) ✓
- [x] to_string_any ✓
- [x] builtinMap ✓

---

### §"Engineering Principles" (lines 609-659 in original, varies)

| Principle | Status |
|-----------|--------|
| Representation invariants | ✗ FGL types don't exist yet |
| No boolean blindness | ✓ Pattern match on NameInfo |
| Catamorphisms | ✓ Translation is a fold |
| No post-hoc rewrites | ✗ wrapLiterals was removed, but try/except protocol is ad-hoc |
| Separation of concerns | ✗ Translation does elaboration's job (coercions, error protocol) |
| Interaction law (metadata) | ✓ Smart constructors |
| Monad carries context | ✓ ReaderT TypeEnv |
| Types flow down | ✗ params/returns hardcoded to Any |

---

## FULL PIPELINE TRACE: End-to-End Example

### Python Source
```python
def add_and_check(x: int, y: int) -> bool:
    result: int = x + y
    return result > 0
```

### Stage 1: Resolution → Γ

```
Γ = {
  "add_and_check" → NameInfo.function { 
    name: "add_and_check",
    params: [("x", TInt), ("y", TInt)],
    returnType: TBool,
    hasErrorOutput: false
  },
  -- Prelude:
  "PAdd" → NameInfo.function { params: [("l", Any), ("r", Any)], returnType: Any },
  "PGt" → NameInfo.function { params: [("l", Any), ("r", Any)], returnType: Any },
}
```

### Stage 2: Translation → HighLaurel (bare types, no coercions)

```
procedure add_and_check(x: int, y: int) returns (LaurelResult: bool)
{
  var result: int;
  result := StaticCall "PAdd" [Identifier "x", Identifier "y"];
  LaurelResult := StaticCall "PGt" [Identifier "result", LiteralInt 0];
  exit $body
}
```

Note: NO from_int, NO Any_to_bool. Bare types from annotations. `result` typed `int` from annotation.

### Stage 3: Elaboration → FineGrainLaurel (all coercions explicit)

Entry: `synthProducer` on the body Block.

**Statement 1:** `result := PAdd(x, y)`
- synthProducer(Assign [result] (StaticCall "PAdd" [x, y]))
- For the RHS call: lookup PAdd → params are (Any, Any)
  - checkValue(Identifier "x", Any): synth → (valVar "x", int). int≠Any → valFromInt(valVar "x")
  - checkValue(Identifier "y", Any): synth → (valVar "y", int). int≠Any → valFromInt(valVar "y")
  - prodCall "PAdd" [valFromInt(valVar "x"), valFromInt(valVar "y")] : Producer(Any)
- Assign target "result" has type int. RHS produces Any. Need downcast Any→int.
  - Bind the PAdd call, then downcast:
  - prodLetProd "rhs" Any (prodCall "PAdd" [...]) 
      (prodLetProd "result" int (prodCall "Any..as_int!" [valVar "rhs"])
        <continuation>)

**Statement 2:** `LaurelResult := PGt(result, 0)`
- lookup PGt → params (Any, Any), returns Any
  - checkValue(Identifier "result", Any): synth → (valVar "result", int). int≠Any → valFromInt(valVar "result")
  - checkValue(LiteralInt 0, Any): synth → (valLiteralInt 0, int). int≠Any → valFromInt(valLiteralInt 0)
  - prodCall "PGt" [valFromInt(valVar "result"), valFromInt(valLiteralInt 0)] : Producer(Any)
- Assign target "LaurelResult" has type bool. RHS produces Any. Need downcast Any→bool.
  - prodLetProd "rhs2" Any (prodCall "PGt" [...])
      (prodLetProd "LaurelResult" bool (prodCall "Any_to_bool" [valVar "rhs2"])
        (prodReturnValue (valVar "LaurelResult")))

**Full FGL output:**
```
prodLetProd "rhs" Any 
  (prodCall "PAdd" [valFromInt (valVar "x"), valFromInt (valVar "y")])
  (prodLetProd "result" int 
    (prodCall "Any..as_int!" [valVar "rhs"])
    (prodLetProd "rhs2" Any 
      (prodCall "PGt" [valFromInt (valVar "result"), valFromInt (valLiteralInt 0)])
      (prodLetProd "LaurelResult" bool 
        (prodCall "Any_to_bool" [valVar "rhs2"])
        (prodReturnValue (valVar "LaurelResult")))))
```

### Stage 4: Projection → MidLaurel (coercions as Laurel nodes)

Mechanical mapping (each FGL constructor → Laurel):
```
procedure add_and_check(x: int, y: int) returns (LaurelResult: bool)
{
  var rhs: Any := PAdd(from_int(x), from_int(y));
  var result: int := Any..as_int!(rhs);
  var rhs2: Any := PGt(from_int(result), from_int(0));
  var LaurelResult: bool := Any_to_bool(rhs2);
  return LaurelResult
}
```

### Stage 5: Lower (existing passes: inferHoleTypes, filterPrelude) → LowLaurel

Minimal changes (no heap touching in this example, no composites). Output ≈ MidLaurel.

### Stage 6: Core Translation → Core

Standard `translateCombinedLaurel`. Types now match:
- `PAdd` expects `(Any, Any)` → gets `(from_int(x), from_int(y))` → types match ✓
- `Any..as_int!` expects `Any` → gets `rhs: Any` → types match ✓
- `Any_to_bool` expects `Any` → gets `rhs2: Any` → types match ✓
- Return type `bool` → `LaurelResult: bool` → types match ✓

Core type checking succeeds. SMT verification runs.

---

## TASK EXECUTION ORDER

### Phase A: Foundation (FGL types must exist first)
- Task 13: Add `#strata_gen FineGrainLaurel` to generate Value/Producer types
- Task 15: Add valFromInt/valFromStr/valFromBool value operators to dialect

### Phase B: Elaboration (depends on Phase A)
- Task 14: Rewrite Elaborate.lean to produce FGL.Value / FGL.Producer
- Task 16: Implement prodCallWithError for hasErrorOutput procedures
- Task 18: Short-circuit desugaring in walk
- Task 19: Write projection (FGL → Laurel)

### Phase C: Translation cleanup (depends on Phase B — tests break until elaboration works)
- Task 8: Remove from_int/from_str/from_bool wrapping
- Task 9: Remove Any_to_bool wrapping
- Task 10: Fix parameter types from annotations
- Task 11: Fix return types from annotations
- Task 12: Remove maybe_except/isError protocol
- Task 17: Enable elaboration in pipeline (remove SKIP)

### Phase D: Stub integration (independent of B/C)
- Task 7: Implement stub loading
- Task 20: Extract preconditions from stubs
- Task 21: Load stubs in V2 pipeline
- Task 22: Populate overloadTable from @overload

### Phase E: Wire Pipeline (no more "lowering")
- V2 pipeline: Resolution → Translation → Elaboration → Projection → cleanup → Core
- NO `translateWithLaurel` / `translateCombinedLaurelWithLowered` in V2 path
- Cleanup = `inferHoleTypes` + `filterPrelude` only (not the 8 lowering passes)
- The 8 lowering passes are SUBSUMED by elaboration (they only run in old pipeline)

### Phase F: Validation
- Run full `diff_test.sh compare pyAnalyzeV2`
- Target: 0 regressions
- Verify old pipeline unchanged

---

## VALIDATION

### After Phase A:
```bash
lake build
echo '#check @Strata.FineGrainLaurel.Value' | lake env lean --stdin  # must resolve
echo '#check @Strata.FineGrainLaurel.Producer' | lake env lean --stdin  # must resolve
echo '#check @Strata.FineGrainLaurel.valFromInt' | lake env lean --stdin  # must resolve
```

### After Phase B:
```bash
lake build
# Elaboration produces FGL types (verified by Lean type checker — can't produce StmtExprMd)
# Projection maps back to Laurel (verified by build)
```

### After Phase C:
```bash
lake build
PATH="/Users/somayyas/bin:$PATH" bash StrataTest/Languages/Python/diff_test.sh compare pyAnalyzeV2 2>&1 | grep "REGR"
# Target: 0 regressions
PATH="/Users/somayyas/bin:$PATH" .lake/build/bin/strata pyAnalyzeLaurel StrataTest/Languages/Python/tests/test_arithmetic.python.st.ion 2>&1 | tail -3
# Old pipeline must still work
```

### After Phase D:
```bash
# StrataInternal benchmarks (requires stubs loaded)
# This validates the PySpec elimination
```

---

## THEORETICAL GROUNDING

Every implementation decision above traces to:

| Decision | Theory | Reference |
|----------|--------|-----------|
| Separate Value/Producer types | FGCBV two judgments (⊢_v, ⊢_p) | Levy et al. 2003 §3.2 |
| produce V / M to x. N | FGCBV monadic bind | Levy et al. 2003 §3.2 |
| Introductions check, eliminations synth | Pfenning recipe | Dunfield & Krishnaswami 2021 §4 |
| Subsumption inserts coercions | Bidirectional typing | Dunfield & Krishnaswami 2021 §4.4 |
| from_int as VALUE operator | Positive type injection (sum) | Lakhani & Pfenning 2022 (↑/↓ shifts) |
| Any_to_bool as PRODUCER | Computation (elimination, can fail) | Lakhani & Pfenning 2022 |
| prodCallWithError | Monadic bind for error effect | Architecture §"Exception Handling" |
| Heap as co-operation | Comodel (state-passing) | Bauer 2018 §co-operations |
| Local walk + global propagation | Constraint collection + solving | Architecture §"Operations vs Co-Operations" |
| Projection = forgetful functor | Kleisli(T) → C | Architecture §"Projection" |
