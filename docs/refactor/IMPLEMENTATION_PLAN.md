# Implementation Plan: Graded FGCBV Elaboration

## Threat of Deletion

If any commit:
- Doesn't build
- Introduces regressions without fixing others
- Violates the architecture
- Uses boolean blindness
- Manipulates raw variables instead of HOAS
- Shoots from the hip without following this plan

Then EVERYTHING gets deleted and we start from scratch.

## Architecture Reference

All implementation follows ARCHITECTURE_V2.md. Key rules:

- Grade monoid: `{1, err, heap, heap·err}`, residuated
- Judgments: `Γ ⊢_v V ⇒/⇐ A` (values, no grade), `Γ ⊢_p M ⇒/⇐ A & e` (producers, graded)
- Value subsumption: `subsume(A, B) = c` → `c(V)`
- Producer subsumption: `subgrade(d, e) = conv` → `applyConvention(conv, M, fun outs => return c(rv))`
- Sequencing: `M to x. N ⇐ A & e` → synth M → `B & d`, check N → `A & (d \ e)`
- HOAS: `mkEffectfulCall` generates fresh names, extends Γ, calls closure
- No mutable state for heap. Heap flows through HOAS closures.
- Dependency order: elaborate callees before callers

## Contract: Translation → Elaboration

Translation guarantees:
- Args to calls are value forms (Literal, Identifier, FieldSelect, pure StaticCall)
- `.New` appears only in producer position
- Annotations give precise types on LocalVariable declarations
- No coercions, no effect annotations

## Contract: Elaboration → Projection → Core

Elaboration produces GFGL which projects to Laurel that Core accepts:
- No `.New` (elaborated into allocation sequence when heap grade)
- No `.FieldSelect` in expression position (elaborated into readField when heap grade)
- `effectfulCall` projects to `[decls; Assign [targets] (StaticCall f args); body]`
- Stateful procs get `$heap_in` input + `$heap` output

## Implementation Steps

### Step 1: Grade infrastructure

Add to Elaborate.lean (before the mutual block):

```lean
inductive Grade where | pure | err | heap | heapErr
  deriving Inhabited, BEq

def Grade.mul : Grade → Grade → Grade
def Grade.le : Grade → Grade → Bool
def Grade.residual : Grade → Grade → Grade  -- d \ e

inductive ConventionWitness where
  | pureCall | errorCall | heapCall | heapErrorCall

def subgrade : Grade → Grade → Option ConventionWitness
```

### Step 2: applyConvention

```lean
def applyConvention (w : ConventionWitness) (callee : String) (args : List FGLValue)
    (heap : Option FGLValue) (resultTy : LowType)
    (k : FGLValue → Option FGLValue → ElabM FGLProducer) : ElabM FGLProducer
```

- `k` receives `(resultValue, newHeap?)` — HOAS bound variables
- pureCall: `k (staticCall callee args) none`
- errorCall: `mkEffectfulCall callee args [...] fun outs => k outs[0]! none`
- heapCall: `mkEffectfulCall callee (heap::args) [...] fun outs => k outs[1]! (some outs[0]!)`
- heapErrorCall: `mkEffectfulCall callee (heap::args) [...] fun outs => k outs[1]! (some outs[0]!)`

### Step 3: Elaboration functions (signature change)

All elaboration functions take `heap : Option FGLValue` as parameter (the current
heap in scope). No mutable state. HOAS closures thread it.

```lean
synthValue (heap : Option FGLValue) (expr : StmtExprMd) : ElabM (FGLValue × LowType)
checkValue (heap : Option FGLValue) (expr : StmtExprMd) (expected : HighType) : ElabM FGLValue
synthProducer (heap : Option FGLValue) (expr : StmtExprMd) : ElabM (FGLProducer × LowType × Grade)
checkProducer (heap : Option FGLValue) (expr : StmtExprMd) (expected : LowType) (grade : Grade) : ElabM FGLProducer
```

Note: `synthProducer` now returns `Grade`. `checkProducer` takes `grade` as input.

### Step 4: synthProducer implementation

For each Laurel construct, produce (FGLProducer, LowType, Grade):

- `.StaticCall f args` where f has grade 1 → `(.returnValue val, ty, .pure)`
- `.StaticCall f args` where f has grade d → use `applyConvention(subgrade(d, ...), ...)`, return grade d
- `.New classId` → allocation sequence, grade `.heap`
- `.Assign [x] v` → `(.assign tv cv .unit, .TVoid, .pure)`
- `.Assert v` → grade `.pure`
- `.FieldSelect obj field` (with heap) → readField, grade `.heap`
- `.Block stmts` → elaborate block, grade = composition of all stmts

### Step 5: checkProducer implementation

- `if v then M else N ⇐ A & e` → check both branches against `A & e`
- `var x:T := v; body ⇐ A & e` → check body against `A & e`
- `M to x. N ⇐ A & e` → synth M → `B & d`, check N → `A & (d \ e)`
- `return v ⇐ A & e` → checkValue v A, grade 1, subgrading `1 ≤ e` (admissible)
- Fallback: synth + subsumption

### Step 6: elaborateBlock / elaborateStmt

`elaborateBlock` for a sequence [s₁, s₂, ..., sₙ]:
- Last statement: checkProducer against expected type and grade
- Earlier statements: synthProducer, grade accumulates

`elaborateStmt` (non-tail):
- Synth the statement → get grade d
- The continuation receives the new heap (if d includes heap)
- Grade residual computed for continuation's expected grade

### Step 7: fullElaborate (dependency order)

1. Build call graph (collect callees per proc)
2. Topological sort
3. Elaborate in order, building effect map: `procName → Grade`
4. For each proc:
   - Synth body → discover grade
   - If grade includes heap: add $heap_in/$heap params
   - Record grade in effect map
5. Assemble output program with heapConstants if any proc has heap grade

### Step 8: Validation

- `lake build` must pass
- `diff_test.sh compare pyAnalyzeV2` must not regress non-heap tests
- Heap tests should improve (ideally all 16 regressions fixed)

## Order of Execution

1. Write Grade + ConventionWitness + subgrade + applyConvention
2. Write synthProducer/checkProducer with Grade in signatures
3. Write elaborateBlock/elaborateStmt with grade accumulation
4. Write fullElaborate with dependency order + effect map
5. Build. Fix errors.
6. Test. Fix regressions.
7. Commit only when both build AND tests pass or improve.
