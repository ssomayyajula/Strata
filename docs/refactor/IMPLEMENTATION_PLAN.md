# Implementation Plan: Python → Laurel (from scratch)

Derived entirely from ARCHITECTURE.md. This is a lab notebook (append-only).
New entries go at the top.

---

## The Build Order

The pipeline (ARCHITECTURE.md §"The Pipeline") is:

```
Resolution → Translation → Elaboration → Projection → Cleanup → Core
```

We implement BOTTOM-UP: start from what exists (Core), work backwards to
what we're building. Each phase has a SINGLE deliverable and a SINGLE
validation criterion.

### Phase 1: FGL Dialect (DONE — exists on branch)

**Deliverable:** `FineGrainLaurel.dialect.st` + `FineGrainLaurel.lean`

**Architecture section:** §"Representation Decisions: Separate Value and Producer Types"

**Validation:** `lake build` succeeds. `#check @Strata.FineGrainLaurel.Value` resolves.

**Status:** Complete. 213-line dialect with Value/Producer categories, all coercion
operators (valFromInt, valFromStr, valFromBool, valFromFloat, valFromComposite,
valFromListAny, valFromDictStrAny, valFromNone), prodCallWithError, prodExit,
prodLabeledBlock. DDM generates Lean types via `#strata_gen`.

---

### Phase 2: Resolution (NameResolution.lean)

**Deliverable:** `buildTypeEnv : Python.AST → TypeEnv`

**Architecture section:** §"Resolution (Building Γ)"

**What Γ must know (per architecture table):**
- Every module-level name classified: `NameInfo.class_` / `.function` / `.variable`
- FuncSig: name, params (with HighType), defaults, returnType, hasErrorOutput, hasKwargs
- classFields: class name → field list
- builtinMap: Python builtin name → Laurel name
- overloadTable: factory dispatch (string arg → class name)

**Implementation (from §"Resolution and Elaboration: One Logical Unit"):**
```lean
def buildTypeEnv (stmts : Array (Python.stmt SourceRange)) (pyspecs : ...) : TypeEnv
```

Walk the Python AST. For each:
- `FunctionDef` → `NameInfo.function (mkFuncSig ...)` reading param annotations via `pythonTypeToHighType`
- `ClassDef` → `NameInfo.class_` with fields from `__init__` annotations
- `AnnAssign` at module level → `NameInfo.variable ty`
- Prelude → hardcoded entries (31 builtins per existing code)

**Key constraints (per architecture):**
- Parameters get types FROM ANNOTATIONS, not defaulted to Any
- If annotation absent → `Any` (§"Non-Goals": Missing annotations → Any)
- returnType from return annotation
- hasErrorOutput from whether function body contains `raise` or calls something that does
- One mechanism for user code AND stubs (§"Library Stubs")

**Validation:** For a test file, `buildTypeEnv` produces a `TypeEnv` where every
referenced name has an entry. No "unknown function" errors downstream.

**Status:** Exists (840 lines). Needs audit: does it read ALL annotations correctly?
Does it produce HighType (not just string "Any")?

---

### Phase 3: Translation (Translation.lean)

**Deliverable:** `translateProgram : Python.AST → TypeEnv → Laurel.Program`

**Architecture section:** §"Translation (Producing e)"

**The fold:** One case per Python AST constructor. Reads Γ for type-directed decisions.
NO coercions. NO literal wrapping. Precise types from annotations.

**Deterministic mappings (from architecture §"Deterministic Mapping"):**

Expressions:
| Python | Laurel |
|--------|--------|
| `Constant(int n)` | `LiteralInt n` |
| `Constant(str s)` | `LiteralString s` |
| `Constant(bool b)` | `LiteralBool b` |
| `Name("x")` | `Identifier "x"` |
| `BinOp(l, Add, r)` | `StaticCall "PAdd" [l', r']` |
| `Compare(l, Eq, r)` | `StaticCall "PEq" [l', r']` |
| `BoolOp(And, [a,b])` | `StaticCall "PAnd" [a', b']` |
| `UnaryOp(Not, x)` | `StaticCall "PNot" [x']` |
| `Call("Foo", args)` where Γ(Foo) = class_ | `New "Foo"` |
| `Call("f", args)` where Γ(f) = function | `StaticCall "f" [args']` |
| `Call("str", args)` | `StaticCall "to_string_any" [args']` (via builtinMap) |
| `Attribute(obj, "field")` | `FieldSelect obj' "field"` |
| `Subscript(c, k)` | `StaticCall "Get" [c', k']` |
| `List([a,b])` | `from_ListAny(ListAny_cons(a', ListAny_cons(b', ListAny_nil())))` |
| `Dict({k:v})` | `from_DictStrAny(DictStrAny_cons(k', v', DictStrAny_empty()))` |
| `IfExp(t,b,e)` | `IfThenElse t' b' e'` |

Statements:
| Python | Laurel |
|--------|--------|
| `AnnAssign(x, ty, val)` | `Assign [x'] val'` (scope hoisting pre-declared x) |
| `Assign([x], val)` | `Assign [x'] val'` |
| `Assign([a,b], rhs)` | `tmp := rhs; a := Get(tmp, 0); b := Get(tmp, 1)` |
| `AugAssign(x, Add, v)` | `Assign [x'] (StaticCall "PAdd" [x', v'])` |
| `Return(e)` | `Return e'` |
| `Assert(e)` | `Assert e'` |
| `If(t, b, e)` | `IfThenElse t' b' e'` |
| `While(t, b)` | `Block [...] (some breakLabel)` wrapping `While t' body'` |
| `Break` | `Exit <currentBreakLabel>` |
| `Continue` | `Exit <currentContinueLabel>` |
| `Pass` | `Block [] none` |

**Python-specific desugarings (Translation-internal):**
1. Scope hoisting (pre-declare all function-local variables at body top)
2. Calling convention (normalize kwargs to positional using FuncSig)
3. Mutable parameter copies (`var x := $in_x`)
4. Object construction (`.New` + `__init__` two-phase protocol)
5. Context managers (`Type@__enter__`/`Type@__exit__` qualified calls)
6. For-loop abstraction (havoc + assume)
7. Loop labels (break/continue with labeled blocks, Translation-internal stack)
8. `__name__` injection at module level

**What Translation does NOT do (per architecture §"What Translation Does NOT Do"):**
- No `from_int`, `from_str`, `from_bool`, `Any_to_bool` — that's Elaboration
- No literal wrapping — `5` → `LiteralInt 5`, period
- No type inference — types from annotations, top-down
- No polarity/ANF — Translation naturally produces ANF by construction

**Monad:** `TransM := ReaderT TypeEnv (StateT TransState (Except TransError))`
- Γ in reader (immutable)
- Fresh names, loop label stack in state

**Metadata:** Interaction law (§"Metadata: Monad-Comonad Interaction Law"):
```lean
def translateM (wa : WithMetadata α) (f : α → TransM β) : TransM (WithMetadata β) := do
  let result ← f wa.val
  pure { val := result, md := wa.md }
```
Smart constructors (`mkExpr sr expr`) enforce metadata attachment.

**Validation (spec-driven):**
- Translation is a catamorphism (one case per constructor)?
- Emits NO coercions? `grep -n "from_int\|from_str\|from_bool\|Any_to_bool" Translation.lean` = empty
- Reads annotations for types (not default to Any)?
- Emits bare literals (not wrapped)?
- Each Python AST constructor has exactly one mapping?

**Status:** Exists (1402 lines). Previous version was correct (coercions stripped).
Needs audit against the full mapping table above.

---

### Phase 4: Elaboration (Elaborate.lean)

**Deliverable:** `elaborate : Laurel.Program → TypeEnv → FineGrainLaurel.Program`

**Architecture section:** §"Elaboration (Derivation Transformation: Laurel → FineGrainLaurel)"

**The method:** Bidirectional typing (Dunfield & Krishnaswami 2021).

**Four functions (per Lakhani & Pfenning's four judgments):**
```lean
def synthValue (expr : Laurel.StmtExprMd) : ElabM (FGL.Value × HighType)
def checkValue (expr : Laurel.StmtExprMd) (expected : HighType) : ElabM FGL.Value
def synthProducer (expr : Laurel.StmtExprMd) : ElabM (FGL.Producer × HighType)
def checkProducer (expr : Laurel.StmtExprMd) (expected : HighType) : ElabM FGL.Producer
```

**What synthesizes (type known from structure or Γ):**
| Construct | Synthesized type | Source |
|-----------|-----------------|--------|
| `Identifier "x"` | Γ(x) | Variable's declared type |
| `LiteralInt n` | int | Literal form |
| `LiteralBool b` | bool | Literal form |
| `LiteralString s` | str | Literal form |
| `StaticCall "f" [args]` | FuncSig.returnType | Γ's signature |
| `FieldSelect obj "field"` | field type from classFields | Γ's class def |
| `New "ClassName"` | UserDefined ClassName | Γ's class entry |

**What checks (expected type propagates inward):**
| Construct | Expected type | Source |
|-----------|--------------|--------|
| Arg in `f(arg)` | FuncSig.params[i] | Γ's signature |
| RHS of `x := expr` | type of x | Γ (from LocalVariable) |
| RHS of `var x: T := expr` | T | Annotation |
| `return expr` | procedure return type | Signature |
| Condition in assert/if/while | bool | Language semantics |
| Branches of if-then-else | enclosing expected type | Context |

**Subsumption (coercion insertion at CHECK boundaries):**
- synth(e) = A, expected = B, A ≠ B:
  - A <: B → upcast (value→value): `valFromX(e)` — stays in value judgment
  - A ▷ B → narrow (value→producer): `prodCall "Any_to_T" [e]` — jumps to producer
  - Neither → type error (should not happen on well-typed Translation output)

**The coercion table (from architecture):**
| actual | expected | relation | coercion | judgment |
|--------|----------|----------|----------|----------|
| int | Any | <: | valFromInt | value→value |
| bool | Any | <: | valFromBool | value→value |
| str | Any | <: | valFromStr | value→value |
| float | Any | <: | valFromFloat | value→value |
| ListAny | Any | <: | valFromListAny | value→value |
| DictStrAny | Any | <: | valFromDictStrAny | value→value |
| Composite | Any | <: | valFromComposite | value→value |
| TVoid | Any | <: | valFromNone | value→value |
| Any | bool | ▷ | Any_to_bool | value→producer |
| Any | int | ▷ | Any..as_int! | value→producer |
| Any | str | ▷ | Any..as_string! | value→producer |
| Any | float | ▷ | Any..as_float! | value→producer |
| Any | Composite | ▷ | Any..as_Composite! | value→producer |
| T | T | = | none | — |

**Short-circuit desugaring (§"Short-Circuit Desugaring in FGL"):**

PAnd(a, b): Python semantics = return a if FALSY, else evaluate and return b
```
prodLetProd "x" Any (elaborate a)
  (prodLetProd "cond" bool (prodCall "Any_to_bool" [valVar "x"])
    (prodIfThenElse (valVar "cond")
      (elaborate b)                      -- truthy: evaluate b
      (prodReturnValue (valVar "x"))))   -- falsy: return a
```

POr(a, b): Python semantics = return a if TRUTHY, else evaluate and return b
```
prodLetProd "x" Any (elaborate a)
  (prodLetProd "cond" bool (prodCall "Any_to_bool" [valVar "x"])
    (prodIfThenElse (valVar "cond")
      (prodReturnValue (valVar "x"))     -- truthy: return a
      (elaborate b)))                    -- falsy: evaluate b
```

**Exception handling (§"Exceptions via the Exception Monad"):**

T(A) = Heap → ((A + E) × Heap). Every call is `prodCall`. If the callee has
error output (`hasErrorOutput = true` in Γ), emit `prodCallWithError` (sugar =
call + bind + case on error). Downcasts are the same: `Any_to_bool` is a fallible
call. Same `prodCallWithError` pattern.

**Operations vs Co-operations (§"Operations vs Co-Operations"):**
- Operations (local): coercions, exceptions, ANF, short-circuit → insert at point
- Co-operations (global): heap → discover locally, propagate through call graph

Two sub-phases:
1. **Local walk** (bidirectional synth/check): inserts operations + discovers co-ops
2. **Global propagation** (fixpoint on call graph): threads Heap through marked procs

**Properties that must hold (language-independent):**
- No Python-specific logic in elaboration
- Total on well-typed Laurel input
- Same elaboration works for Java→Laurel, JS→Laurel

**Validation (spec-driven):**
- synthValue handles every Value-producing constructor?
- synthProducer handles every Producer-producing constructor?
- checkValue inserts valFromX at every A <: B boundary?
- checkProducer inserts narrowing at every A ▷ B boundary?
- Function args CHECKed against param types from Γ?
- Conditions CHECKed against bool?
- Assignment RHS CHECKed against variable's declared type?
- PAnd/POr desugar correctly (architecture-specified output)?
- hasErrorOutput → prodCallWithError?
- Downcasts → prodCallWithError (same pattern)?
- Heap procedures discovered and propagated?
- No `isEffectful`, no `isPreludeFunc`, no boolean blindness?

**Status:** Exists (2080 lines). Previous version had gaps (metadata, some edge cases).
Core logic was architecturally correct. Needs audit against validation questions above.

---

### Phase 5: Projection (in Elaborate.lean or separate file)

**Deliverable:** `project : FGL.Producer → Laurel.StmtExprMd`

**Architecture section:** §"Projection (FineGrainLaurel → Laurel)"

**The algorithm:** `splitProducer` implements bind reassociation (let-floating,
Peyton Jones et al. 1996).

```lean
splitProducer : FGL.Producer → (List Laurel.Stmt, Laurel.Expr)

splitProducer (prodReturnValue v)       = ([], projectValue v)
splitProducer (prodCall f args)         = ([], StaticCall f (args.map projectValue))
splitProducer (prodLetProd x ty M body) = let (mStmts, mExpr) := splitProducer M
                                          let xDecl := LocalVariable x ty (some mExpr)
                                          let (bodyStmts, bodyExpr) := splitProducer body
                                          (mStmts ++ [xDecl] ++ bodyStmts, bodyExpr)
splitProducer (prodIfThenElse c t e)    = ([], IfThenElse (projectValue c) (project t) (project e))
splitProducer (prodWhile c invs b aft)  = ([While ...] ++ afterStmts, afterExpr)
splitProducer (prodAssign t v body)     = ([Assign ...] ++ bodyStmts, bodyExpr)
```

**Soundness:** Scope widening is safe because elaboration generates FRESH names for
all intermediate bindings (freshVar). Fresh names cannot clash with user-defined names.

**projectValue:** Maps FGL.Value to Laurel.StmtExprMd:
- `valVar "x"` → `Identifier "x"`
- `valLiteralInt n` → `LiteralInt n`
- `valFromInt(v)` → `StaticCall "from_int" [projectValue v]`
- etc. (mechanical mapping, one case per Value constructor)

**Validation (spec-driven):**
- Does splitProducer flatten nested prodLetProd?
- Is terminal expression separated from prefix statements?
- Are fresh names used (no capture during scope widening)?
- Is the projection total (one case per FGL constructor)?

**Status:** Exists within Elaborate.lean. Needs audit.

---

### Phase 6: Pipeline Wiring (PySpecPipeline.lean)

**Deliverable:** V2 pipeline command that wires all passes together.

**Architecture section:** §"The Pipeline" (lines 52-68)

**The flow:**
```lean
def pyAnalyzeV2 (inputFile : String) (pyspecFiles : Array String) : IO Core.Program := do
  let ast ← readPython inputFile
  let pyspecResult ← readPySpecs pyspecFiles  -- temporary: old mechanism until stubs done
  let typeEnv := buildTypeEnv ast pyspecResult
  let laurel := translateProgram ast typeEnv
  let fgl := elaborate laurel typeEnv
  let projectedLaurel := project fgl
  let cleaned := inferHoleTypes (filterPrelude projectedLaurel)
  let core := translateToCore cleaned
  return core
```

**Cleanup (NOT lowering):** Only `inferHoleTypes` + `filterPrelude`. The 8 old
lowering passes (liftExpressionAssignments, desugarShortCircuit, eliminateReturns,
heapParameterization, typeHierarchyTransform, modifiesClausesTransform,
constrainedTypeElim, eliminateHoles) are ALL subsumed by elaboration.

**Validation:** `lake build` succeeds. Running the V2 command on test files produces
Core output. Old pipeline (`pyAnalyzeLaurel`) is unchanged.

**Status:** Exists (494 lines). The wiring logic works. Old pyspec mechanism retained
temporarily for stubs.

---

### Phase 7: Stub Integration (future)

**Deliverable:** Load library stubs as Python → buildTypeEnv → merge into Γ

**Architecture section:** §"Library Stubs: Eliminating PySpec"

**Not blocking Phase 2-6.** Current tests use pyspec. Stub integration eliminates
pyspec but doesn't change the pipeline's semantics.

---

## OPERATIONAL DISCIPLINE

### Rules

1. ARCHITECTURE.md answers WHAT and WHY. This plan answers HOW.
2. Every line of code traces to a specific section of ARCHITECTURE.md.
3. Plan before code. Write what you'll change, which file/lines, why (cite section).
4. Commit after every successful `lake build`.
5. Never commit broken builds.
6. `diff_test.sh` is a CONSEQUENCE check, not the validation target.
7. If stuck: write `-- ARCHITECTURE GAP: <description>` and stop.
8. No heuristics. No peephole optimizations. No "smart" handlers.
9. No boolean blindness (no `isEffectful`, no `isPreludeFunc`).
10. No coercions in Translation. No Python-specific logic in Elaboration.

### Compliance Checks (before every commit)

```bash
grep -n "from_int\|from_str\|from_bool\|Any_to_bool" Translation.lean | grep -v "^.*--"  # VIOLATION
grep -n "isPrelude\|isUserFunc\|isEffectful" Elaborate.lean                                # VIOLATION
grep -n "SKIP\|skip\|disabled" PySpecPipeline.lean                                         # VIOLATION
```

### Verification

```bash
lake build
PATH="/Users/somayyas/bin:$PATH" bash StrataTest/Languages/Python/diff_test.sh compare pyAnalyzeV2 2>&1 | grep "REGR\|BLOCKED"
```

### Validation is SPEC-DRIVEN

For each ARCHITECTURE.md section, does the code implement it?

§"Translation (Producing e)":
- Is Translation a catamorphism (one case per constructor)?
- Does it emit NO coercions?
- Does it read annotations for types?
- Does it emit bare literals?

§"The Bidirectional Recipe":
- Does synthValue handle every Value-producing Laurel constructor?
- Does synthProducer handle every Producer-producing Laurel constructor?
- Does checkValue insert valFromX at every A <: B boundary?
- Does checkProducer insert narrowing at every A ▷ B boundary?
- Are function args CHECKed against param types from Γ?
- Are conditions CHECKed against bool?
- Are assignment RHS CHECKed against variable's declared type?

§"Short-Circuit Desugaring in FGL":
- PAnd: `e to x. if (truthy x) then f else produce x`?
- POr: `e to x. if (truthy x) then produce x else f`?

§"Composite and Any":
- canUpcast fires for UserDefined → Any?
- insertFGLUpcast emits valFromComposite?
- from_Composite exists in prelude?

§"Projection as Bind Reassociation":
- splitProducer flattens nested prodLetProd?
- Fresh names (no capture)?

§"Operations vs Co-Operations":
- Heap-touching discovered locally?
- Propagated globally through call graph?

Test parity is a CONSEQUENCE of these holding. Not the target.

---

## WHAT EXISTS ON THIS BRANCH (reference only)

| File | Lines | Status |
|------|-------|--------|
| `FineGrainLaurel.dialect.st` | 213 | Phase 1 DONE |
| `FineGrainLaurel.lean` | — | Phase 1 DONE (DDM gen) |
| `NameResolution.lean` | 840 | Phase 2 reference |
| `Translation.lean` | 1402 | Phase 3 reference (coercions stripped) |
| `Elaborate.lean` | 2080 | Phase 4 reference (core logic correct, edge cases incomplete) |
| `PySpecPipeline.lean` | 494 | Phase 6 reference (wiring works) |
| `PythonRuntimeLaurelPart.lean` | — | Prelude (has from_Composite) |

This code is from the PREVIOUS attempt. It is REFERENCE, not the starting point.
We reuse what's architecturally correct. We rewrite what isn't.

---

## EXECUTION SEQUENCE

### Step 1: Audit existing code against architecture

For each file, check every validation question. Produce a gap list.
What's correct stays. What violates gets rewritten. No wholesale rewrites
unless the gap list shows systemic violation.

### Step 2: Fix gaps

In dependency order: Resolution → Translation → Elaboration → Projection → Pipeline.
Each fix is a single commit with `lake build` verification.

### Step 3: End-to-end validation

Run `diff_test.sh`. Any regressions → diagnose against architecture (which section
is violated?), not against "what makes the test pass."

---

## THEORETICAL GROUNDING

| Decision | Theory | Reference |
|----------|--------|-----------|
| Separate Value/Producer types | FGCBV two judgments (⊢_v, ⊢_p) | Levy et al. 2003 §3.2 |
| produce V / M to x. N | FGCBV monadic bind | Levy et al. 2003 §3.2 |
| Introductions check, eliminations synth | Pfenning recipe | Dunfield & Krishnaswami 2021 §4 |
| Subsumption inserts coercions | Bidirectional typing | Dunfield & Krishnaswami 2021 §4.4 |
| valFromInt as VALUE operator | Positive type injection (sum) | Lakhani & Pfenning 2022 |
| Any_to_bool as PRODUCER | Fallible elimination of sum type | Lakhani & Pfenning 2022 |
| prodCallWithError as SUGAR | Exception monad T(A) = A + E | Plotkin & Pretnar 2009 |
| T(A) = Heap → ((A+E) × Heap) | Combined state + exception monad | Levy 2004 Ch.5 |
| Heap as co-operation | Comodel (state-passing) | Bauer 2018 §co-operations |
| Local walk + global propagation | Constraint collection + solving | Standard |
| Projection = forgetful functor | Kleisli(T) → C | Category theory |
| Let-floating = bind associativity | Monad law | Peyton Jones et al. 1996 |
| Freshness ensures soundness | Scope widening under α-equivalence | Standard |
| Metadata via comonad interaction | Monad-comonad distributive law | Uustalu & Vene 2008 |
| from_Composite pointer-preserving | Sum type injection for heap refs | Architecture §"Composite and Any" |
