# Implementation Plan: Python → Laurel (from scratch)

Derived entirely from ARCHITECTURE.md. This is a lab notebook (append-only).
New entries go at the top.

---

## The Build Order

The pipeline (ARCHITECTURE.md §"The Pipeline") is:

```
Resolution → Translation → Elaboration → Projection → Core
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

For Translation: input Python nodes carry metadata. The fold extracts it and
attaches to the output Laurel nodes via smart constructors. Standard comonadic
extract + rebuild.

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

**Monad:**
```lean
abbrev ElabM := ReaderT TypeEnv (StateT ElabState (Except ElabError))
```

Γ in the reader (immutable). Fresh variable counter in the state.

**Metadata:** Smart constructors — the ONLY way to build AST nodes. Same pattern
as Translation's `mkExpr sr expr`. Every output node gets `md` from:
- The input node it corresponds to (use input's `.md`)
- Or the input node that caused its synthesis (inherited `.md`)

```lean
def mkLaurel (md : Imperative.MetaData Core.Expression) (e : StmtExpr) : StmtExprMd :=
  { val := e, md := md }
```

Never write `{ val := ..., md := ... }` directly. The smart constructor makes
forgetting metadata impossible.

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

**What checks (expected type flows in from context):**
| Construct | Expected type | Source |
|-----------|--------------|--------|
| Arg in `f(arg)` | FuncSig.params[i] | Γ's signature |
| RHS of `x := expr` | type of x | Γ (from LocalVariable) |
| RHS of `var x: T := expr` | T | Annotation |
| `return expr` | procedure return type | Signature |
| Condition in assert/if/while | bool | Language semantics |
| IfThenElse branches (in CHECK position) | enclosing expected type | Context |
| While body | TVoid | Statement |

**Statement forms that SYNTHESIZE TVoid (context adds nothing):**
- While, Assert, Assume, Exit, Assign → always TVoid, no CHECK needed

**Why this split (DRY):** All synthesizing constructs have the same coercion
pattern: "look up actual type, compare with expected, insert coercion if mismatch."
That IS checkValue/checkProducer. One function, one place. No repeated logic.

**MODE CORRECTNESS: No equality on HighTypes.** All type comparisons flow through
canUpcast (A <: B) or canNarrow (A ▷ B). `typesEqual` is ONLY used in
checkValue/checkProducer as the reflexivity short-circuit (A <: A). Never match
on specific types in the walk. Never `if ty == TVoid`. The coercion table is the
ONLY mechanism for relating types.

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
  let core := translateToCore projectedLaurel
  return core
```

**No cleanup passes.** The architecture pipeline is:
```
Resolution → Translation → Elaboration → Projection → Core translation
```
That's it. ALL old lowering passes (liftExpressionAssignments, desugarShortCircuit,
eliminateReturns, heapParameterization, typeHierarchyTransform,
modifiesClausesTransform, constrainedTypeElim, eliminateHoles, inferHoleTypes,
filterPrelude) are either subsumed by elaboration or irrelevant. Elaboration produces
a complete, correctly-typed FGL program. Projection maps it mechanically to Laurel.
Core translates that Laurel. Nothing in between.

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

## EXECUTION SEQUENCE (individual code changes)

All work happens in `Strata/Languages/FineGrainLaurel/Elaborate.lean`.
Each task: write the code, `lake build`, commit. Implementation agent + review agent.

### 0. Baseline

- [x] `lake build` passes with pass-through stub
- [x] Old pipeline (`pyAnalyzeLaurel`) has 0 regressions
- [x] Resolution produces precise types from annotations (commit ad8ff0b80)
- [x] Translation uses precise types from Γ (commit 5c3b0f00e)

### 1. Smart constructor: `mkLaurel`

**File:** Elaborate.lean  
**Code:**
```lean
def mkLaurel (md : Imperative.MetaData Core.Expression) (e : StmtExpr) : StmtExprMd :=
  { val := e, md := md }

def mkHighTypeMd (md : Imperative.MetaData Core.Expression) (ty : HighType) : HighTypeMd :=
  { val := ty, md := md }
```
**Why:** ARCHITECTURE.md §"Metadata: Smart Constructors" — the ONLY way to build nodes.

### 2. FGLValue inductive

**File:** Elaborate.lean  
**Code:**
```lean
inductive FGLValue where
  | litInt (n : Int)
  | litBool (b : Bool)
  | litString (s : String)
  | var (name : String)
  | fromInt (inner : FGLValue)
  | fromStr (inner : FGLValue)
  | fromBool (inner : FGLValue)
  | fromFloat (inner : FGLValue)
  | fromComposite (inner : FGLValue)
  | fromListAny (inner : FGLValue)
  | fromDictStrAny (inner : FGLValue)
  | fromNone
  | fieldAccess (obj : FGLValue) (field : String)
  | staticCall (name : String) (args : List FGLValue)
  deriving Inhabited
```
**Why:** ARCHITECTURE.md §"Representation Decisions" — Value category (inert terms).

### 3. FGLProducer inductive

**File:** Elaborate.lean  
**Code:**
```lean
inductive FGLProducer where
  | returnValue (v : FGLValue)
  | call (name : String) (args : List FGLValue)
  | letProd (var : String) (ty : HighType) (prod : FGLProducer) (body : FGLProducer)
  | assign (target : FGLValue) (val : FGLValue) (body : FGLProducer)
  | varDecl (name : String) (ty : HighType) (init : FGLValue) (body : FGLProducer)
  | ifThenElse (cond : FGLValue) (thn : FGLProducer) (els : FGLProducer)
  | whileLoop (cond : FGLValue) (body : FGLProducer) (after : FGLProducer)
  | assert (cond : FGLValue) (body : FGLProducer)
  | assume (cond : FGLValue) (body : FGLProducer)
  | callWithError (callee : String) (args : List FGLValue)
      (resultVar : String) (errorVar : String)
      (resultTy : HighType) (errorTy : HighType) (body : FGLProducer)
  | exit (label : String)
  | labeledBlock (label : String) (body : FGLProducer)
  | newObj (className : String) (resultVar : String) (ty : HighType) (body : FGLProducer)
  | seq (first : FGLProducer) (second : FGLProducer)
  | unit
  deriving Inhabited
```
**Why:** ARCHITECTURE.md §"Representation Decisions" — Producer category (effectful terms).

### 4. ElabM monad + helpers

**File:** Elaborate.lean  
**Code:**
```lean
structure ElabState where
  freshCounter : Nat := 0
  currentProcReturnType : HighType := .TCore "Any"  -- same CHECK mechanism as args/assign

inductive ElabError where
  | typeError (msg : String)
  | unsupported (msg : String)
  deriving Repr, Inhabited

abbrev ElabM := ReaderT TypeEnv (StateT ElabState (Except ElabError))

def freshVar (pfx : String := "tmp") : ElabM String := do
  let s ← get
  set { s with freshCounter := s.freshCounter + 1 }
  pure s!"{pfx}${s.freshCounter}"

def lookupEnv (name : String) : ElabM (Option NameInfo) := do
  pure (← read).names[name]?

def lookupFuncSig (name : String) : ElabM (Option FuncSig) := do
  match (← read).names[name]? with
  | some (.function sig) => pure (some sig)
  | _ => pure none

def lookupFieldType (className field : String) : ElabM HighType := do
  let env ← read
  match env.classFields[className]? with
  | some fields =>
      match fields.find? (fun (n, _) => n == field) with
      | some (_, ty) => pure ty
      | none => pure (.TCore "Any")
  | none => pure (.TCore "Any")
```
**Why:** IMPLEMENTATION_PLAN.md §"Phase 4" monad. `currentProcReturnType` is just another
CHECK position — same subsumption mechanism as arg checking and assignment RHS checking.
Expected type flows down, synth the expr, coerce at mismatch. Nothing special.

### 5. Coercion table: `canUpcast` + `canNarrow` + `typesEqual`

**File:** Elaborate.lean  
**Code:**
```lean
def canUpcast (actual expected : HighType) : Option (FGLValue → FGLValue) :=
  match actual, expected with
  | .TInt, .TCore "Any" => some .fromInt
  | .TBool, .TCore "Any" => some .fromBool
  | .TString, .TCore "Any" => some .fromStr
  | .TFloat64, .TCore "Any" => some .fromFloat
  | .UserDefined _, .TCore "Any" => some .fromComposite
  | .TCore "ListAny", .TCore "Any" => some .fromListAny
  | .TCore "DictStrAny", .TCore "Any" => some .fromDictStrAny
  | .TVoid, .TCore "Any" => some (fun _ => .fromNone)
  | _, _ => none

def canNarrow (actual expected : HighType) : Option String :=
  match actual, expected with
  | .TCore "Any", .TBool => some "Any_to_bool"
  | .TCore "Any", .TInt => some "Any..as_int!"
  | .TCore "Any", .TString => some "Any..as_string!"
  | .TCore "Any", .TFloat64 => some "Any..as_float!"
  | .TCore "Any", .UserDefined _ => some "Any..as_Composite!"
  | _, _ => none

def typesEqual (a b : HighType) : Bool :=
  match a, b with
  | .TInt, .TInt | .TBool, .TBool | .TString, .TString
  | .TFloat64, .TFloat64 | .TVoid, .TVoid => true
  | .TCore n1, .TCore n2 => n1 == n2
  | .UserDefined id1, .UserDefined id2 => id1.text == id2.text
  | _, _ => false
```
**Why:** ARCHITECTURE.md §"Coercion Table" — exact table transcribed.

**`typesEqual` is the reflexivity axiom (A <: A).** It is ONLY used inside the
subsumption function (checkValue/checkProducer) as a short-circuit: "types already
agree, no coercion needed." It must NEVER appear in the elaboration walk itself.
All type comparisons in the walk flow through canUpcast/canNarrow.

### 6. `synthValue`: literals + Identifier + FieldSelect

**File:** Elaborate.lean (inside mutual block)  
**Cases:**
```
.LiteralInt n       → (.litInt n, .TInt)
.LiteralBool b      → (.litBool b, .TBool)
.LiteralString s    → (.litString s, .TString)
.Identifier id      → lookup Γ(id.text):
                        .variable ty → (.var id.text, ty)
                        .function sig → (.var id.text, sig.returnType)
                        _ → (.var id.text, .TCore "Any")
.FieldSelect obj field → synthValue obj to get (objVal, objTy):
                        if objTy is UserDefined className →
                          lookupFieldType className field.text → fieldTy
                          (.fieldAccess objVal field.text, fieldTy)
                        else → (.fieldAccess objVal field.text, .TCore "Any")
```
**Why:** ARCHITECTURE.md §"What SYNTHESIZES" table, row by row.

### 7. `synthValue`: StaticCall + New

**File:** Elaborate.lean (inside mutual block)  
**Cases:**
```
.StaticCall callee args → lookup FuncSig from Γ(callee.text):
                          retTy = sig.returnType (or .TCore "Any" if unknown)
                          argVals = args.map (fun a => synthValue a |>.1)
                          (.staticCall callee.text argVals, retTy)
.New classId           → (.var classId.text, .UserDefined classId)
```
**Why:** ARCHITECTURE.md §"What SYNTHESIZES" — StaticCall synths return type from Γ.
Note: args are NOT checked here. Arg checking happens in synthProducer (producer context).

### 8. `checkValue`: synth → compare → coerce or error

**File:** Elaborate.lean (inside mutual block)  
**Logic:**
```
checkValue expr expected :=
  let (val, actual) ← synthValue expr
  if typesEqual actual expected then return val
  match canUpcast actual expected with
  | some coerce => return (coerce val)
  | none =>
    if typesEqual actual (.TCore "Any") && typesEqual expected (.TCore "Any") then return val
    throw (ElabError.typeError s!"Cannot coerce {actual} to {expected}")
```
**Why:** ARCHITECTURE.md §"Subsumption (coercion insertion)" — subsumption rule from
Dunfield & Krishnaswami §4.4. NOT silent drop — error on unrelated types.

### 9. `synthProducer`: StaticCall (CHECK args + hasErrorOutput)

**File:** Elaborate.lean (inside mutual block)  
**Logic:**
```
.StaticCall callee args →
  -- Special case: PAnd/POr → short-circuit (Task 14)
  if callee.text == "PAnd" || callee.text == "POr" then
    shortCircuitDesugar callee.text args
  else
    let sig ← lookupFuncSig callee.text
    let checkedArgs ← match sig with
      | some s => List.zip args s.params |>.mapM (fun (arg, (_, paramTy)) => checkValue arg paramTy)
      | none => args.mapM (fun a => synthValue a |>.map (·.1))
    let retTy := sig.map (·.returnType) |>.getD (.TCore "Any")
    if sig.map (·.hasErrorOutput) |>.getD false then
      let rv ← freshVar "result"
      let ev ← freshVar "err"
      return (.callWithError callee.text checkedArgs rv ev retTy (.TCore "Error") (.returnValue (.var rv)), retTy)
    else
      return (.call callee.text checkedArgs, retTy)
```
**Why:** ARCHITECTURE.md §"How Elaboration Works" point 1 — look up f in Γ, check args,
emit prodCallWithError if hasErrorOutput.

### 10. `synthProducer`: Assign

**File:** Elaborate.lean (inside mutual block)  
**Logic:**
```
.Assign targets value →
  match targets with
  | [target] =>
    let targetTy ← match target.val with
      | .Identifier id => lookupEnv id.text >>= fun
        | some (.variable t) => pure t
        | _ => pure (.TCore "Any")
      | _ => pure (.TCore "Any")
    let (targetVal, _) ← synthValue target
    let checkedRhs ← checkValue value targetTy
    return (.assign targetVal checkedRhs .unit, targetTy)
  | _ → (.unit, .TCore "Any")  -- multi-target: ARCHITECTURE GAP
```
**Why:** ARCHITECTURE.md §"What CHECKS" — "RHS of x := expr" checked against "type of x".

### 11. `synthProducer`: LocalVariable

**File:** Elaborate.lean (inside mutual block)  
**Logic:**
```
.LocalVariable nameId typeMd initOpt →
  let declTy := typeMd.val
  let initVal ← match initOpt with
    | some init => checkValue init declTy
    | none => pure (.var "_uninit")
  return (.varDecl nameId.text declTy initVal .unit, declTy)
```
**Why:** ARCHITECTURE.md §"What CHECKS" — "RHS of var x: T := expr" checked against T.

### 12. `synthProducer`: conditions (IfThenElse/While/Assert/Assume) — SUBSUMPTION

**File:** Elaborate.lean (inside mutual block)  
**Logic: Use subsumption function, NO type dispatch in the walk.**

The condition is a CHECK position (checked against bool). We use a single
`subsumeBool` helper that:
1. synthValue cond → (condVal, condTy)
2. canUpcast condTy .TBool → coerce (value→value) [nothing in table does this]
3. canNarrow condTy .TBool → emit callWithError, bind result to get Value(bool)
4. Reflexivity (condTy already bool via canUpcast .TBool .TBool = none, but
   we need a reflexivity check) → use condVal directly

The reflexivity check is the ONLY place where type comparison is legitimate
(A <: A, the short-circuit). Implemented as: if canUpcast returns none AND
canNarrow returns none AND it's not an error → types must already agree.

```
-- Helper: subsume a value to bool for condition positions.
-- Returns (condValue, Option wrapperProducer).
-- If narrowing needed: wrapperProducer wraps the if/while/assert in a callWithError.
subsumeToBool (cond : StmtExprMd) : ElabM (SubsumeResult) :=
  let (condVal, condTy) ← synthValue cond
  match canUpcast condTy .TBool with
  | some coerce => pure (.value (coerce condVal))  -- value-level, stays in value
  | none => match canNarrow condTy .TBool with
    | some narrowFn =>
      -- Producer-level: need to bind. Return info for caller to wrap.
      let narrowVar ← freshVar "cond"
      pure (.narrow condVal narrowFn narrowVar)
    | none => pure (.value condVal)  -- already bool (reflexivity)

-- IfThenElse uses subsumeToBool:
.IfThenElse cond thenBranch elseBranch →
  let result ← subsumeToBool cond
  let (thenProd, thenTy) ← synthProducer thenBranch
  let elsProd ← match elseBranch with
    | some e => (synthProducer e).map (·.1)
    | none => pure .unit
  match result with
  | .value boolVal =>
    return (.ifThenElse boolVal thenProd elsProd, thenTy)
  | .narrow condVal narrowFn narrowVar =>
    -- callWithError IS the binding. Body is the if.
    return (.callWithError narrowFn [condVal] narrowVar (narrowVar ++ "_err")
              .TBool (.TCore "Error")
              (.ifThenElse (.var narrowVar) thenProd elsProd), thenTy)
```
Same pattern for While (body synths, result = TVoid), Assert/Assume (result = TVoid).

**Why:** ARCHITECTURE.md §"MODE CORRECTNESS: No equality on HighTypes." All type
comparisons flow through canUpcast/canNarrow. The coercion table decides. No
`typesEqual condTy .TBool` dispatch. Subsumption is ONE function called at
CHECK boundaries. Narrowing gives a producer; bind it to get a value back for
the condition slot.

### 13. `synthProducer`: Block + Exit + New + Return

**File:** Elaborate.lean (inside mutual block)  
**Logic:**
```
.Block stmts label →
  let (prod, ty) ← elaborateBlock stmts
  match label with
  | some l => return (.labeledBlock l prod, ty)
  | none => return (prod, ty)

.Exit label → return (.exit label, .TVoid)

.New classId →
  let objVar ← freshVar "obj"
  let ty := HighType.UserDefined classId
  return (.newObj classId.text objVar ty (.returnValue (.var objVar)), ty)

.Return valueOpt →
  let retTy := (← get).currentProcReturnType
  match valueOpt with
  | some (.some_expr _ v) =>
    let checkedVal ← checkValue v retTy  -- same CHECK as args/assign: expected type flows down
    return (.returnValue checkedVal, retTy)
  | _ => return (.returnValue .fromNone, .TVoid)
```
`elaborateBlock`: foldr over stmts, each elaborated via synthProducer, sequenced
via `sequenceProducers` (replaces .unit continuations).

**Why:** ARCHITECTURE.md §"Blocks as Nested Lets (CBV → FGCBV)" — foldr, Levy §3.2.
Return is just another CHECK position in the bidirectional recipe (§"What CHECKS" table):
expected type from proc signature flows down, same subsumption as everywhere else.

### 14. `checkProducer`: synth → narrow

**File:** Elaborate.lean (inside mutual block)  
**Logic:**
```
checkProducer expr expected :=
  let (prod, actual) ← synthProducer expr
  if typesEqual actual expected then return prod
  match canNarrow actual expected with
  | some narrowFn =>
    let tmpVar ← freshVar "narrow"
    let resultVar ← freshVar "narrowed"
    return (.letProd tmpVar actual prod
             (.callWithError narrowFn [.var tmpVar] resultVar (resultVar ++ "_err")
               expected (.TCore "Error") (.returnValue (.var resultVar))))
  | none => throw (ElabError.typeError s!"Cannot narrow {actual} to {expected}")
```
**Why:** ARCHITECTURE.md §"Narrowing" — bind producer, narrow result via fallible call.

### 15. Short-circuit: PAnd/POr

**File:** Elaborate.lean  
**Logic (exact FGL from ARCHITECTURE.md §"Short-Circuit Desugaring in FGL"):**
```
shortCircuitDesugar "PAnd" [a, b] :=
  let xVar ← freshVar "sc"
  let condVar ← freshVar "cond"
  let (aProd, _) ← synthProducer a  -- elaborate first operand
  let (bProd, _) ← synthProducer b  -- elaborate second operand (lazy)
  -- Structure: bind a's result to xVar, then narrow xVar to bool, then branch.
  -- callWithError IS the binding for condVar (no extra letProd around it).
  return (.letProd xVar (.TCore "Any") aProd
    (.callWithError "Any_to_bool" [.var xVar] condVar (condVar ++ "_err")
      .TBool (.TCore "Error")
      (.ifThenElse (.var condVar)
        bProd                          -- truthy: evaluate b, return it
        (.returnValue (.var xVar)))),  -- falsy: return a's value
    .TCore "Any")

shortCircuitDesugar "POr" [a, b] :=
  let xVar ← freshVar "sc"
  let condVar ← freshVar "cond"
  let (aProd, _) ← synthProducer a
  let (bProd, _) ← synthProducer b
  return (.letProd xVar (.TCore "Any") aProd
    (.callWithError "Any_to_bool" [.var xVar] condVar (condVar ++ "_err")
      .TBool (.TCore "Error")
      (.ifThenElse (.var condVar)
        (.returnValue (.var xVar))     -- truthy: return a's value
        bProd)),                        -- falsy: evaluate b, return it
    .TCore "Any")
```
**Why:** ARCHITECTURE.md §"Short-Circuit Desugaring in FGL" — exact transcription.

### 16. `projectValue`: FGLValue → StmtExprMd

**File:** Elaborate.lean  
**Logic (one case per constructor, ALL via mkLaurel):**
```
projectValue (md : MetaData) : FGLValue → StmtExprMd
  | .litInt n => mkLaurel md (.LiteralInt n)
  | .litBool b => mkLaurel md (.LiteralBool b)
  | .litString s => mkLaurel md (.LiteralString s)
  | .var name => mkLaurel md (.Identifier (Identifier.mk name none))
  | .fromInt v => mkLaurel md (.StaticCall (Identifier.mk "from_int" none) [projectValue md v])
  | .fromStr v => mkLaurel md (.StaticCall (Identifier.mk "from_str" none) [projectValue md v])
  | .fromBool v => mkLaurel md (.StaticCall (Identifier.mk "from_bool" none) [projectValue md v])
  | .fromFloat v => mkLaurel md (.StaticCall (Identifier.mk "from_float" none) [projectValue md v])
  | .fromComposite v => mkLaurel md (.StaticCall (Identifier.mk "from_Composite" none) [projectValue md v])
  | .fromListAny v => mkLaurel md (.StaticCall (Identifier.mk "from_ListAny" none) [projectValue md v])
  | .fromDictStrAny v => mkLaurel md (.StaticCall (Identifier.mk "from_DictStrAny" none) [projectValue md v])
  | .fromNone => mkLaurel md (.StaticCall (Identifier.mk "from_None" none) [])
  | .fieldAccess obj f => mkLaurel md (.FieldSelect (projectValue md obj) (Identifier.mk f none))
  | .staticCall name args => mkLaurel md (.StaticCall (Identifier.mk name none) (args.map (projectValue md)))
```
**Why:** ARCHITECTURE.md §"Projection" — forgetful functor, one case per constructor.

### 17. `splitProducer`: bind reassociation

**File:** Elaborate.lean  
**Logic (THE monad law):**
```
splitProducer (md : MetaData) : FGLProducer → (List StmtExprMd × StmtExprMd)
  | .returnValue v => ([], projectValue md v)
  | .call name args =>
      ([], mkLaurel md (.StaticCall (Identifier.mk name none) (args.map (projectValue md))))
  | .letProd x ty inner body =>
      let (innerStmts, innerExpr) := splitProducer md inner
      let xDecl := mkLaurel md (.LocalVariable (Identifier.mk x none) (mkHighTypeMd md ty) (some innerExpr))
      let (bodyStmts, bodyExpr) := splitProducer md body
      (innerStmts ++ [xDecl] ++ bodyStmts, bodyExpr)
  | .assign target val body =>
      let stmt := mkLaurel md (.Assign [projectValue md target] (projectValue md val))
      let (bodyStmts, bodyExpr) := splitProducer md body
      ([stmt] ++ bodyStmts, bodyExpr)
  | .varDecl name ty init body =>
      let decl := mkLaurel md (.LocalVariable (Identifier.mk name none) (mkHighTypeMd md ty) (some (projectValue md init)))
      let (bodyStmts, bodyExpr) := splitProducer md body
      ([decl] ++ bodyStmts, bodyExpr)
  | .ifThenElse cond thn els =>
      ([], mkLaurel md (.IfThenElse (projectValue md cond) (projectBody md thn) (some (projectBody md els))))
  | .whileLoop cond body after =>
      let whileStmt := mkLaurel md (.While (projectValue md cond) [] none (projectBody md body))
      let (afterStmts, afterExpr) := splitProducer md after
      ([whileStmt] ++ afterStmts, afterExpr)
  | .assert cond body =>
      let stmt := mkLaurel md (.Assert (projectValue md cond))
      let (bodyStmts, bodyExpr) := splitProducer md body
      ([stmt] ++ bodyStmts, bodyExpr)
  | .assume cond body =>
      let stmt := mkLaurel md (.Assume (projectValue md cond))
      let (bodyStmts, bodyExpr) := splitProducer md body
      ([stmt] ++ bodyStmts, bodyExpr)
  | .callWithError callee args rv ev rTy eTy body =>
      let callExpr := mkLaurel md (.StaticCall (Identifier.mk callee none) (args.map (projectValue md)))
      let rvDecl := mkLaurel md (.LocalVariable (Identifier.mk rv none) (mkHighTypeMd md rTy) (some callExpr))
      let evDecl := mkLaurel md (.LocalVariable (Identifier.mk ev none) (mkHighTypeMd md eTy) (some (mkLaurel md (.StaticCall (Identifier.mk "NoError" none) []))))
      let (bodyStmts, bodyExpr) := splitProducer md body
      ([rvDecl, evDecl] ++ bodyStmts, bodyExpr)
  | .exit label => ([mkLaurel md (.Exit label)], mkLaurel md (.LiteralBool true))
  | .labeledBlock label body =>
      ([mkLaurel md (.Block [projectBody md body] (some label))], mkLaurel md (.LiteralBool true))
  | .newObj className rv ty body =>
      let newExpr := mkLaurel md (.New (Identifier.mk className none))
      let decl := mkLaurel md (.LocalVariable (Identifier.mk rv none) (mkHighTypeMd md ty) (some newExpr))
      let (bodyStmts, bodyExpr) := splitProducer md body
      ([decl] ++ bodyStmts, bodyExpr)
  | .seq first second =>
      let (fStmts, _) := splitProducer md first
      let (sStmts, sExpr) := splitProducer md second
      (fStmts ++ sStmts, sExpr)
  | .unit => ([], mkLaurel md (.LiteralBool true))
```
**Why:** ARCHITECTURE.md §"Implementation: Projection as Bind Reassociation" — exact
algorithm. The letProd case IS the monad law: `(m >>= f) >>= g = m >>= (λx. f x >>= g)`.

### 18. `projectBody` + `fullElaborate`

**File:** Elaborate.lean  
**Logic:**
```
projectBody (md : MetaData) (prod : FGLProducer) : StmtExprMd :=
  let (stmts, terminal) := splitProducer md prod
  mkLaurel md (.Block (stmts ++ [terminal]) none)

def fullElaborate (typeEnv : TypeEnv) (program : Laurel.Program) : Except String Laurel.Program := do
  let mut procs := []
  for proc in program.staticProcedures do
    match proc.body with
    | .Transparent bodyExpr =>
      let retTy := match proc.outputs with
        | [p] => p.type.val
        | _ => .TCore "Any"
      let initState : ElabState := { freshCounter := 0, currentProcReturnType := retTy }
      let ((fglProd, _), _) ← (synthProducer bodyExpr).run typeEnv |>.run initState
      let projected := projectBody bodyExpr.md fglProd
      procs := procs ++ [{ proc with body := .Transparent projected }]
    | _ => procs := procs ++ [proc]
  return { program with staticProcedures := procs }
```
**Why:** IMPLEMENTATION_PLAN.md §"Phase 6" — fullElaborate is the entry point.
Elaborates each proc body, projects back. `currentProcReturnType` from proc.outputs.

### SMOKE TEST RESULTS (2026-05-06, after tasks 1-18)

All test files that exist elaborate successfully:
- test_arithmetic: OK (1 proc)
- test_boolean_logic: OK (1 proc)
- test_break_continue: OK (4 procs)
- test_augmented_assign: OK (1 proc)
- test_class_decl: OK (2 procs)
- test_class_field_any/init/use: OK
- test_class_methods: OK (5 procs)
- test_with_void_enter: OK (4 procs)
- test_try_except: OK (2 procs)
- test_for_loop: OK (3 procs)

Zero elaboration failures. The Core error (`Undefined type 'Composite'`) is NOT
an elaboration issue — it's a pipeline wiring issue: the prelude declares
`from_Composite` on the `Any` datatype, but `Composite` (a heap infrastructure
type) isn't registered in `program.types`. The old pipeline's heap parameterization
pass adds these. Our Task 20 will do the same.

### 19. Heap co-op Phase 1: analysis (collect reads/writes/callees per procedure)

**File:** Elaborate.lean  
**Data:**
```lean
structure HeapAnalysis where
  readsHeap : Bool := false    -- FieldSelect on composite
  writesHeap : Bool := false   -- Assign to FieldSelect target, New
  callees : List String := []  -- StaticCall targets (for propagation)
```
**Logic:** Walk each procedure body BEFORE elaboration (or during). For each node:
- `.FieldSelect target _` where target type is UserDefined/Composite → `readsHeap := true`
- `.New _` → `writesHeap := true`
- `.Assign [target] _` where `target.val` is `.FieldSelect _ _` → `writesHeap := true`
- `.StaticCall callee _` → record callee in `callees`

Produce `Std.HashMap String HeapAnalysis` (proc name → analysis).

**Why:** ARCHITECTURE.md §"Operations vs Co-Operations" — local walk discovers co-ops.
Reference: `Strata/Languages/Laurel/HeapParameterization.lean` lines 48-80 does the
same analysis in the old pipeline (`collectExpr`).

### 20. Heap co-op Phase 2: fixpoint propagation + signature rewriting

**File:** Elaborate.lean  
**Phase 2a: Propagation.** Fixpoint on call graph:
```lean
def propagateHeap (analysis : Std.HashMap String HeapAnalysis) : Std.HashMap String HeapAnalysis :=
  -- Iterate until no changes:
  -- If proc A calls proc B, and B reads/writes heap, then A reads/writes heap too.
  loop:
    for (procName, info) in analysis:
      for callee in info.callees:
        match analysis[callee]? with
        | some calleeInfo =>
          if calleeInfo.readsHeap && !info.readsHeap → mark A as readsHeap, changed=true
          if calleeInfo.writesHeap && !info.writesHeap → mark A as writesHeap, changed=true
        | none => skip (external/prelude — check prelude sigs for heap)
    if changed: continue loop
    else: return analysis
```

**Phase 2b: Signature rewriting.** For each heap-touching procedure:
- If `writesHeap`: add `heap : Heap` to BOTH inputs AND outputs (inout)
- If `readsHeap` only: add `heap : Heap` to inputs only

**Phase 2c: Call-site rewriting.** For each call to a heap-touching procedure:
- If callee writes heap (inout): `heap, result := callee(heap, args...)`
  In FGL: `callWithError` with heap as first arg, heap as additional output
- If callee only reads heap: `result := callee(heap, args...)`
  In FGL: add `heap` to call args

**Phase 2d: Field access rewriting.**
- `.FieldSelect obj field` → `readField(heap, obj, field)` (StaticCall)
- `.Assign [.FieldSelect obj field] value` → `heap := updateField(heap, obj, field, BoxT(value))`
- `.New className` → `heap, obj := allocate(heap, className)` (heap gets new ref)

**Concrete types (from HeapParameterizationConstants.lean):**
- `Heap` = `TCore "Heap"` (datatype with `data: Map Composite (Map Field Box)`, `nextReference: int`)
- `Composite` = `TCore "Composite"` (type synonym for int — heap reference)
- `Field` = `TCore "Field"` (enum of all field names across all classes)
- `Box` = `TCore "Box"` (sum type: BoxInt, BoxBool, BoxFloat64, BoxComposite, BoxAny)
- `TypeTag` = `TCore "TypeTag"` (enum of class names for runtime type checks)

**Type infrastructure declarations.** fullElaborate must emit these datatypes in
`program.types` for Core to function:
- `Composite` composite type (just ref:int + typeTag:TypeTag)
- `Box` datatype with constructors per primitive
- `Field` enum datatype
- `Heap` datatype
- `TypeTag` enum datatype

**Why:** ARCHITECTURE.md §"Operations vs Co-Operations" — global propagation via fixpoint.
Reference: existing `HeapParameterization.lean` (400+ lines) does exactly this in the
old pipeline. We replicate its output but produce it from the elaboration framework
rather than as a separate pass.

### 22. Introduce LowType + eraseType (ARCHITECTURE.md §"Two Type Systems")

**File:** Elaborate.lean  
**Code:**
```lean
inductive LowType where
  | TInt | TBool | TString | TFloat64 | TVoid
  | TCore (name : String)  -- "Any", "Composite", "Heap", "Error", "ListAny", etc.
  deriving Inhabited, Repr

def eraseType : HighType → LowType
  | .TInt => .TInt
  | .TBool => .TBool
  | .TString => .TString
  | .TFloat64 => .TFloat64
  | .TVoid => .TVoid
  | .TCore name => .TCore name
  | .UserDefined _ => .TCore "Composite"
```
**Why:** Type-directed compilation (Harper & Morrisett 1995). FGL operates in the
erased world. UserDefined is unrepresentable in LowType. Lean enforces the boundary.

### 23. Update FGLProducer/FGLValue to use LowType

**File:** Elaborate.lean  
**Change:** Every `HighType` reference in FGLValue/FGLProducer constructors becomes `LowType`:
- `letProd (var : String) (ty : LowType) ...`
- `varDecl (name : String) (ty : LowType) ...`
- `callWithError ... (resultTy : LowType) (errorTy : LowType) ...`
- `newObj ... (ty : LowType) ...`

### 24. Update synthValue to return LowType

**File:** Elaborate.lean  
**Change:** `synthValue : StmtExprMd → ElabM (FGLValue × LowType)`
- LiteralInt → (.litInt n, .TInt)  [LowType.TInt]
- Identifier → lookupEnv, then `eraseType` the result
- FieldSelect → `eraseType` the field type
- StaticCall → `eraseType sig.returnType`
- New classId → (.var ..., .TCore "Composite")  [NOT UserDefined]

### 25. Update canUpcast/canNarrow to use erased types

**File:** Elaborate.lean  
**Change:** The CHECK boundary still takes HighType (from annotations) but compares
against LowType (from synth). Subsumption now crosses the boundary:
```lean
-- checkValue synthesizes a LowType, then compares against eraseType(expected)
def checkValue (expr : StmtExprMd) (expected : HighType) : ElabM FGLValue := do
  let (val, actual) ← synthValue expr  -- actual : LowType
  let expectedLow := eraseType expected
  if lowTypesEqual actual expectedLow then return val
  match canUpcast actual expectedLow with
  | some coerce => return (coerce val)
  | none => throw ...
```
canUpcast and canNarrow now operate on LowType × LowType (both sides erased).

### 26. Update New handling to emit MkComposite

**File:** Elaborate.lean  
**Change:** synthProducer for `.New classId`:
```
.New classId →
  let refVar ← freshVar "ref"
  let objVar ← freshVar "obj"
  -- Emit: ref := Heap..nextReference!(heap); heap := increment(heap);
  --       obj := MkComposite(ref, ClassName_TypeTag())
  pure (.letProd refVar (.TCore "int") (.call "Heap..nextReference!" [.var "$heap"])
    (.letProd objVar (.TCore "Composite") (.call "MkComposite" [.var refVar, .staticCall (classId.text ++ "_TypeTag") []])
      (.returnValue (.var objVar)))), .TCore "Composite")
```
This IS the type erasure for New: `New "Foo"` → `MkComposite(freshRef, Foo_TypeTag)`.

### 27. Update FieldSelect on Composite to emit readField

**File:** Elaborate.lean  
**Change:** synthValue for `.FieldSelect obj field` when objTy erases to Composite:
```
.FieldSelect obj field →
  let (objVal, objTy) ← synthValue obj
  if objTy == .TCore "Composite" then
    -- Heap field access: readField(heap, obj, field)
    pure (.staticCall "readField" [.var "$heap", objVal, .var (field.text ++ "_Field")], .TCore "Box")
  else
    pure (.fieldAccess objVal field.text, objTy)
```
And Assign to FieldSelect → updateField(heap, obj, field, BoxT(val)).

### 21. End-to-end validation

```bash
lake build
PATH="/Users/somayyas/bin:$PATH" bash StrataTest/Languages/Python/diff_test.sh compare pyAnalyzeV2
PATH="/Users/somayyas/bin:$PATH" bash StrataTest/Languages/Python/diff_test.sh compare pyAnalyzeLaurel
```
First: 0 regressions target. Second: must be unchanged (proves old pipeline untouched).
Any regression → diagnose against ARCHITECTURE.md, not "what makes test pass."

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
| HighType→LowType (type erasure) | Type-directed compilation | Harper & Morrisett 1995 (TIL) |
| UserDefined→Composite | Representation erasure (newtype unwrapping) | Standard compilation |
| Elaboration crosses type boundary | Typed translation between systems | Shao & Appel 1995 |
