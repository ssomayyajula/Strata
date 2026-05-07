# Next Fixes: Non-Heap Regression Root Causes

## Issue 1: "Procedure X not found in program" (test_with_void_enter, test_loops)

**Symptom:** Core's CallElim says `from_bool` / `Any_get` not found as procedure.

**Root cause:** Projection emits `FGLValue.fromBool v` (a coercion) as a bare
`StaticCall "from_bool" [v]` in statement position. Core sees a StaticCall in
statement position and emits `Core.Statement.call` which looks up `from_bool`
as a PROCEDURE. But `from_bool` is a datatype CONSTRUCTOR (function), not a
procedure. It should only appear in expression position.

**Why it happens:** `FGLProducer.returnValue (.fromBool v)` projected into a
block produces `[StaticCall "from_bool" [v]]`. If this is the last statement,
Core's `translateExpr` handles it (since it's the block's "return value").
But if `.seq (.returnValue (.fromBool v)) continuation` is projected, it becomes
`[StaticCall "from_bool" [v], ...continuation...]`. The first element is now
a bare StaticCall in statement position — Core calls `translateStmt` on it which
dispatches to the procedure-call path.

**Fix:** The `.seq (.returnValue v) rest` case in projection is wrong. A
`returnValue` in non-tail position is dead code (the value is discarded). Either:
- (a) Don't emit it (skip returnValue in seq's first position), or
- (b) Assign it to a throwaway variable

The deeper fix: `elaborateStmt` for pure calls currently emits `cont` (drops the
call entirely). But for unknown functions, it also emits `cont`. If Translation
emits a bare function call as an expression statement (`.Expr _ value`), the
`synthStmt` → StaticCall → `.pure` case drops it. That's correct for PURE calls
(no side effects). But for the `| none =>` case (unknown function), it also drops
it — which is wrong if the function has effects we don't know about. However the
actual issue is that `.seq (.returnValue coercion) rest` appears in the projection
output, which means somewhere elaborateStmt IS emitting returnValue before cont.

**Actually the real cause:** Looking at `elaborateStmt` for `.StaticCall` with
`| .pure _ => cont` — this DROPS the call entirely. But what about the `PAnd`/`POr`
case? `shortCircuit` returns an `ifThenElse` with `returnValue` branches. Then
`elaborateStmt` does `.seq p (← cont)`. The `p` is an `.ifThenElse` with
`.returnValue (.fromBool v)` inside. When projected, the ifThenElse becomes a
statement, and its branches contain `from_bool(v)` which is fine as an expression
inside the if. So that's not the issue either.

**Need to trace:** Run test_with_void_enter, dump the FGL BEFORE projection, see
exactly which `.seq (.returnValue ...) ...` appears.

## Issue 2: "input length and args length mismatch" (test_function_def_calls, test_multi_function)

**Symptom:** CoreTransform rejects call because arg count != param count.

**Root cause:** `resolveKwargs` can't find the function in Γ at call time, so it
returns posArgs unchanged (without filling defaults). The function IS in Γ (buildTypeEnv
processes all top-level defs), but the lookup fails.

**Hypothesis:** The call might be going through a path where the function name doesn't
match what's in Γ. Or the `.Expr _ value` → `translateExpr` → `translateCall` → lookup
returns `| _ =>` (not found). Need to add a trace to confirm.

**Fix:** Once root cause is confirmed, ensure the lookup succeeds.

## Issue 3: "Cannot infer type" / "Type checking error" (test_procedure_in_assert, test_power)

**Symptom:** Core can't type-check because a user-defined function (e.g., `timedelta_func`)
isn't in the Core program's function table.

**Root cause:** User functions ARE in the Laurel program (Translation emitted them).
They go through `combinePySpecLaurel` which prepends runtime. They go through
`translateMinimal` → `resolve` → SemanticModel. But Core's type checker can't
find them.

**Hypothesis:** `resolve` builds a SemanticModel from the combined program. If the
user function doesn't get registered (maybe it's in an unreachable SCC, or has a
type error during resolution), Core won't see it.

**Fix:** Trace why the user function doesn't make it into the Core program.

## Implementation Plan

1. Fix Issue 1 (projection): ensure projection doesn't emit bare constructors/functions
   as statements. The fix is in how `.seq` with a `.returnValue` first projects.
2. Fix Issue 2 (defaults): trace the Γ lookup for `test_helper_procedure`, fix.
3. Fix Issue 3 (user functions): trace why user functions don't make it to Core.
4. Implement heap state-passing (the big one — 10 tests depend on this).

## Heap State-Passing Implementation Plan

Per Architecture §"Heap (State-Passing Translation)":

1. **Discovery:** Walk each procedure body post-elaboration. If it contains:
   - `.New` (allocation)
   - `.FieldSelect` on Composite (field read)
   - `.Assign` to FieldSelect (field write)
   Mark it as heap-touching.

2. **Propagation:** Build call graph. Fixpoint: if A calls heap-touching B, A is
   heap-touching too.

3. **State-passing rewrite:** For each heap-touching procedure:
   - Add `$heap: Heap` input parameter and `$heap: Heap` output parameter
   - Rewrite `.New classId` → `MkComposite($heap_nextRef, ClassName_TypeTag())`
     + increment heap ref counter
   - Rewrite `.FieldSelect obj field` → `readField($heap, obj, field)`
   - Rewrite `.Assign [FieldSelect obj field] val` → `updateField($heap, obj, field, Box..Any(from_T(val)))`
   - Rewrite calls to heap-touching procedures: pass $heap, receive updated $heap

4. **Type infrastructure:** Add Composite, Field, Box, Heap, TypeTag types to
   program.types ONLY when heap-touching procs exist.

This is a Laurel→Laurel pass that runs AFTER elaboration's projection and BEFORE
`translateMinimal` sends to Core. It replaces the old `typeHierarchyTransform` +
`heapParameterization` passes.
