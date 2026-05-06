# Implementation Plan (synced with ARCHITECTURE.md)

This document is APPEND-ONLY. New entries are added at the top. Previous entries
remain as a dated record of decisions, findings, and progress. Like a lab notebook.

---

## 2026-05-06 (after commit f52406a53 — methodology correction)

### Validation is SPEC-DRIVEN, not TEST-DRIVEN

Tests passing is a CONSEQUENCE of correctness, not a target. The validation 
methodology is: for each section of ARCHITECTURE.md, does the code implement it?

**The correct validation questions (per ARCHITECTURE.md sections):**

§"The Bidirectional Recipe":
- Does `synthValue` handle every Value-producing Laurel constructor?
- Does `synthProducer` handle every Producer-producing Laurel constructor?
- Does `checkValue` insert `valFromX` at every subtyping (A <: B) boundary?
- Does `checkProducer` insert narrowing at every (A ▷ B) boundary?
- Are function args CHECKed against param types from Γ?
- Are conditions CHECKed against bool?
- Are assignment RHS CHECKed against the variable's declared type?

§"Composite and Any: The Pointer Injection":
- Does `canUpcast` fire for UserDefined → Any?
- Does `insertFGLUpcast` emit `valFromComposite`?
- Does `canNarrow` fire for Any → UserDefined?
- Does the `from_Composite` constructor exist in the prelude?

§"Short-Circuit Desugaring in FGL":
- Does PAnd desugar to `e to x. if (truthy x) then f else produce x`?
- Does POr desugar to `e to x. if (truthy x) then produce x else f`?
- Do both branches produce the same type (Any)?

§"Implementation: Projection as Bind Reassociation":
- Does `splitProducer` flatten nested `prodLetProd`?
- Is the terminal expression separated from prefix statements?
- Are fresh names used (no capture during scope widening)?

§"Operations vs Co-Operations":
- Does elaboration discover heap-touching procedures (FieldSelect, field assign, New)?
- Does the global propagation thread Heap through marked procedures?
- Are `readField`/`updateField`/`increment` procedures produced?

§"Resolution (Building Γ)":
- Does buildTypeEnv classify every module-level name?
- Are function signatures complete (params, defaults, returnType, hasErrorOutput)?
- Are class fields recorded in classFields?

§"Translation (Producing e)":
- Is Translation a catamorphism (one case per constructor)?
- Does it emit NO coercions (no from_int, from_str, Any_to_bool)?
- Does it read annotations for types (not default to Any)?
- Does it emit bare literals (not wrapped)?

**Test parity is a CONSEQUENCE of getting these right.** If all the above hold and
tests still fail, either (a) the architecture has a gap, or (b) the test exercises
something outside our scope (stubs, PySpec features, etc.).

---

## 2026-05-06 (after commit 65bf8a608 — investigating remaining 9 crashes)

### Architectural Finding: `Any` Is Not the Top Type

**Discovery:** `Any` in the prelude is a TAGGED UNION (sum type) of specific value types:
`from_None | from_bool | from_int | from_float | from_str | from_DictStrAny | from_ListAny | from_ClassInstance | from_Slice | exception`

`Composite` (a heap reference = `MkComposite(ref: int, typeTag: TypeTag)`) is NOT a 
constructor of `Any`. There is no injection from `Composite` into `Any` in the current 
prelude. This means `Composite <: Any` does NOT hold in the existing type system.

This is the root cause of Issue #882 (13 tests) and the 4 competing PRs (#727, #918, 
#954, #1106) — they all attempt to bridge this gap with different approaches.

### Architectural Decision: Add `from_Composite` to `Any` (Option 1)

**Decision:** Add `from_Composite (as_Composite: Composite)` as a new constructor to the 
`Any` datatype in the prelude. This is:
- **Sound:** The heap reference is preserved (pointer-preserving injection). Mutations 
  through heap are still visible. No serialization, no aliasing issues.
- **Complete:** Gives a proper coercion path Composite → Any (subtyping) and 
  Any → Composite (narrowing via `Any..as_Composite!`).
- **Resolves all 4 competing PRs:** The coercion exists, is pointer-preserving, and 
  fits cleanly into the subtyping/narrowing discipline.

**Why this wasn't done before:** Requires changing the prelude `Any` datatype, which 
touches everything. But it's the theoretically correct answer: if `Any` models "any 
Python value" and Python values include class instances, `Any` MUST have a constructor 
for class instances-as-references.

### Implementation

1. Add to `PythonRuntimeLaurelPart.lean`, in the `Any` datatype:
   ```
   from_Composite (as_Composite: Composite),
   ```
   (After `from_Slice`, before `exception`)

2. DDM will auto-generate: `Any..isfrom_Composite`, `Any..as_Composite`, `Any..as_Composite!`

3. In `Elaborate.lean`, the subtyping relation already has `UserDefined <: Any` mapped to 
   `valFromComposite`. After heap parameterization transforms `UserDefined "ClassName"` to 
   `Composite`, the coercion function is `from_Composite`. Elaboration's `insertFGLUpcast` 
   for `UserDefined` / `Composite` → `Any` emits `valFromComposite`.

4. Narrowing: `Any ▷ Composite` via `Any..as_Composite!` (producer, may throw TypeError).

5. The `test_with_void_enter` regression (and likely some of the 8 inconclusive→crash tests) 
   will be fixed once this coercion path exists.

### What This Means for the Subtyping Relation

Updated coercion table:

| actual | expected | relation | coercion | FGL level |
|--------|----------|----------|----------|-----------|
| Composite | Any | A <: B | `from_Composite` | Value (pointer injection) |
| Any | Composite | A ▷ B | `Any..as_Composite!` | Producer (may throw) |

This is the SAME pattern as `int <: Any` via `from_int`. Composite is just another 
"concrete type" that injects into the `Any` sum.

---

## 2026-05-06 (after commit 5ad00fa5a — spec-driven audit)

### Audit Results: Elaborate.lean vs ARCHITECTURE.md

| Architecture Section | Verdict | Gap |
|---------------------|---------|-----|
| Bidirectional Recipe (checkValue inserts upcasts) | YES | — |
| Bidirectional Recipe (checkProducer inserts narrowing) | YES | — |
| Bidirectional Recipe (args CHECKed) | YES | — |
| Bidirectional Recipe (conditions CHECKed against bool) | YES | — |
| Bidirectional Recipe (assignment RHS CHECKed) | YES | — |
| Composite/Any (canUpcast, insertFGLUpcast, from_Composite) | YES | — |
| Short-circuit (PAnd/POr desugaring) | YES | Conditional on isEffectful (should be unconditional) |
| Projection (splitProducer, let-floating) | YES | — |
| Heap co-operations (discover, propagate, thread) | YES | — |
| prodCallWithError for hasErrorOutput | YES | — |
| **prodCallWithError for DOWNCASTS** | **NO** | Uses bare prodCall — architecture says casts are fallible |
| **Exit (break/continue)** | **NO** | Emits trivial value, control flow lost |
| **Multi-target assign (tuple unpacking)** | **NO** | Not implemented |
| Language-independent | YES | — |

### Gaps to Fix (per ARCHITECTURE.md)

1. **Downcasts must use `prodCallWithError`** (§"The Single Mechanism"): "a cast IS a
   fallible producer." `Any_to_bool` can throw TypeError. Must emit `prodCallWithError`
   not `prodCall`. This is an architecture VIOLATION, not tech debt.

2. **Short-circuit should be unconditional** (§"Short-Circuit Desugaring"): The architecture
   specifies PAnd/POr desugaring regardless of whether the operand is effectful. Pure operands
   should also desugar (Python's `and`/`or` return values, not booleans — always).

3. **Exit elaboration** (§"Break/Continue Labels"): Translation emits `Exit label`. Elaboration
   must preserve this in FGL. Currently emits trivial `prodReturnValue true` — wrong.

4. **Multi-target assign** (§"Translation: tuple unpacking"): Translation emits tuple
   unpacking as `tmp := rhs; a := Get(tmp, 0); b := Get(tmp, 1)`. Elaboration should
   handle this (each is a normal Assign). If it's not working, the issue is in how
   elaboration processes the Block containing these assignments.

5. **Dead code cleanup**: `unifiedElaborate` function has stale comment saying Phase 1
   is skipped. Remove or fix.

---

## 2026-05-06 (after commit 383da1e58)

**State:** 47/54 tests PASS (21 identical + 26 same-category-pass-different-output).
1 genuine regression (pass → internal_error). 8 tests crashed that were previously inconclusive.

### Test Breakdown

| Category | Count | Action needed |
|----------|-------|---------------|
| Pass (identical output) | 21 | None — verified correct |
| Pass (different output) | 26 | Audit: is V2 output semantically equivalent? |
| Pass → internal_error | 1 | Fix (test_with_void_enter — Composite/Any at heap boundary) |
| Inconclusive → internal_error | 8 | Fix (elaboration crashes where old pipeline produced inconclusive) |
| Inconclusive (both) | ~6 | Not our problem (old pipeline also fails) |

### Path to Parity

**Priority 1:** Fix 1 genuine regression (test_with_void_enter). Composite↔Any coercion
at heap boundary. `from_Composite` constructor DONE (commit 924f2700c). Elaboration's
`canUpcast`/`insertFGLUpcast` handles UserDefined→Any. Free `isSubtype` bypass removed
(commit 8fdc2cd6b). Remaining: find the specific boundary where coercion isn't being
inserted and fix the elaboration walk per ARCHITECTURE.md §"The Bidirectional Recipe".

**Priority 2:** Fix 8 inconclusive→crash tests. Elaboration gaps in complex cases
(multi-function, class methods, loops, with-statements).

**Priority 3:** Audit 26 different-output tests for semantic equivalence. If V2 proves
the same properties with different names, that's fine. If it misses bugs, that's a
correctness issue.

### Remaining Tech Debt

| Item | Status | Architecture reference |
|------|--------|----------------------|
| `from_Composite` prelude | ✅ DONE (commit 924f2700c) | §"Composite and Any: The Pointer Injection" |
| Free isSubtype bypass removed | ✅ DONE (commit 8fdc2cd6b) | §"Subtyping and Narrowing Discipline" |
| Coercion insertion at all Composite/Any boundaries | 🔄 IN PROGRESS | §"The Bidirectional Recipe" |
| Stub integration | ❌ Not started | §"Library Stubs: Eliminating PySpec" |
| Metadata in projection | ❌ Not started | §"Metadata: Monad-Comonad Interaction Law" |

---

## 2026-05-06 (after commit 17737b0d9 — removed old lowering passes)

**Finding:** Removing old lowering passes from V2 revealed that Core requires type
infrastructure (Composite, Box, Field, Heap, TypeTag datatypes + readField/updateField
procedures) that our elaboration wasn't producing.

**Decision:** Elaboration's Phase 2 (heap) and Phase 3 (type hierarchy) must produce
these type declarations in the output program. Fixed in commit f4239525e.

**Finding:** Core's type registry error "Type (arrow Composite ...) is not an instance
of a previously registered type" occurs because `program.types` in the elaborated output
didn't include the heap infrastructure datatypes.

---

## 2026-05-06 (after commit 88bb9af08 — projection flattening)

**Finding:** `prodLetProd` nested in the `prod` argument of another `prodLetProd` was
being projected as a Block-in-initializer (nested blocks). Core can't handle this.

**Decision:** Projection uses `splitProducer` which implements let-floating (Peyton Jones
et al. 1996) — monadic bind reassociation. `prodLetProd x ty M body` where M is itself
a `prodLetProd` gets flattened: M's bindings come first, then x gets M's terminal as
initializer, then body.

**Assumption documented:** Flattening widens scope. Safe because elaboration generates
fresh names (freshVar), preventing capture. Laurel has block scoping but freshness
makes widening sound.

---

## 2026-05-06 (after commit f77e021a2 — strip Translation + enable elaboration)

**Decision:** Translation stripped of ALL coercions (from_int, from_str, from_bool,
Any_to_bool). Elaboration enabled in pipeline (no longer skipped).

**Finding:** Short-circuit desugaring (PAnd/POr) needed type-aligned branches.
Architecture now specifies exact FGL output (commit b896ec248):
- AND: `e to x. if (truthy x) then f else produce x`
- OR: `e to x. if (truthy x) then produce x else f`

**Finding:** `from_ListAny`/`from_DictStrAny` are CONSTRUCTORS (per architecture table),
not coercions. They stay in Translation.

---

## 2026-05-06 (after commit 2d9455f44 — Phase B, elaboration with FGL types)

**Decision:** Elaboration produces `FineGrainLaurel.Value` and `FineGrainLaurel.Producer`
types (not `Laurel.StmtExprMd`). The types enforce polarity at the Lean level.

**Four elaboration functions:** synthValue, checkValue, synthProducer, checkProducer
(per Lakhani & Pfenning's four judgments for polarized bidirectional typing).

---

## 2026-05-06 (after commit 969a6680c — Phase A, FGL types generated)

**Decision:** Added `#strata_gen FineGrainLaurel` to generate Value/Producer inductive
types from the dialect file. Added value-level coercion operators (valFromInt, valFromStr,
etc.) to the dialect.

**Finding:** DDM's `#strata_gen` works with the `.st` text format (no need for `.st.ion`
binary compilation). Categories become separate inductive types. Operators become
constructors.

---

## Foundational Decisions (from architecture design sessions)

**Subtyping vs Narrowing:** Two separate relations.
- A <: B (subtyping): value→value, infallible. `int <: Any` via valFromInt.
- A ▷ B (narrowing): value→producer, fallible. `Any ▷ bool` via Any_to_bool.
Not gradual typing (mathematically questionable). Clean, asymmetric.

**Operations vs Co-operations (Bauer 2018):** Coercions/exceptions = operations (local
insertion by elaboration walk). Heap = co-operation (discovered locally, propagated
globally through call graph).

**Bidirectional recipe:** Python annotations drive checking mode. Things with known type
from Γ synthesize. Subsumption fires at CHECK boundaries when synth ≠ expected.

**FGCBV as CBPV fragment:** Only computation type is ↑A. Every Producer has type ↑A.
`produce V` = return. `M to x. N` = monadic bind. Function args must be Values.

**Projection = let-floating:** splitProducer implements bind associativity.
Freshness of elaboration names ensures soundness of scope widening.

---

## OPERATIONAL DISCIPLINE

- Architecture + Plan are God
- Every implementation agent gets parallel review agent
- Standard preamble (`.claude/agent-preamble.md`) for all agents
- Plan before code
- Commit after every successful build
- Kill on architecture violations
- Never ask the user implementation questions — the spec answers them
- This plan is APPEND-ONLY (lab notebook, not whiteboard)
