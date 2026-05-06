# Implementation Plan (synced with ARCHITECTURE.md)

This document is APPEND-ONLY. New entries are added at the top. Previous entries
remain as a dated record of decisions, findings, and progress. Like a lab notebook.

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
at heap boundary. Need `from_Composite` in prelude + elaboration's coerce function.

**Priority 2:** Fix 8 inconclusive→crash tests. Elaboration gaps in complex cases
(multi-function, class methods, loops, with-statements).

**Priority 3:** Audit 26 different-output tests for semantic equivalence. If V2 proves
the same properties with different names, that's fine. If it misses bugs, that's a
correctness issue.

### Remaining Tech Debt

| Item | Description | Architecture reference |
|------|-------------|----------------------|
| `from_Composite` prelude | Reverted — needs re-addition | §"Subtyping and Narrowing Discipline" |
| Stub integration | Library stubs not loaded | §"Library Stubs: Eliminating PySpec" |
| Metadata in projection | Some nodes get `#[]` metadata | §"Metadata: Monad-Comonad Interaction Law" |

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
