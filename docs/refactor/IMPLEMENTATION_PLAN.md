# Implementation Plan (synced with ARCHITECTURE.md)

**Last updated:** After commit 383da1e58 (fix 3/4 class regressions)

**Current state:** 47/54 tests PASS (21 identical + 26 same-category-pass-different-output).
1 genuine regression (pass → internal_error). 8 tests crashed that were previously inconclusive.

---

## CURRENT TEST BREAKDOWN

| Category | Count | Action needed |
|----------|-------|---------------|
| Pass (identical output) | 21 | None — verified correct |
| Pass (different output) | 26 | Audit: is V2 output semantically equivalent? |
| Pass → internal_error | 1 | Fix (test_with_void_enter — Composite/Any at heap boundary) |
| Inconclusive → internal_error | 8 | Fix (elaboration crashes where old pipeline produced inconclusive) |
| Inconclusive (both) | ~6 | Not our problem (old pipeline also fails) |

---

## PATH TO PARITY

### Priority 1: Fix the 1 genuine regression (test_with_void_enter)

This test passed on old pipeline but crashes on V2 with "Impossible to unify 
Composite with Any." This is the Composite↔Any coercion at a heap boundary —
the exact problem the architecture's `from_Composite` / subtyping discipline addresses.

**Fix:** Ensure elaboration inserts `valFromComposite` when a Composite-typed value
meets an Any context. The `from_Composite` prelude addition (which was reverted earlier)
needs to be re-added, and elaboration's coerce function needs the Composite→Any case.

### Priority 2: Fix the 8 inconclusive → internal_error tests

These tests DIDN'T pass on the old pipeline either (they were inconclusive) but at
least they didn't CRASH. Our V2 crashes on them. The crashes are elaboration gaps —
likely the same patterns as the type-checking errors we already fixed, but for more
complex cases (multi-function calls, class methods, loops, with-statements).

Tests: test_class_field_use, test_class_methods, test_class_with_methods, 
test_default_params, test_function_def_calls, test_loops, test_multi_function, 
test_with_statement

**Fix:** Diagnose each, fix elaboration gaps. Target: inconclusive (matching old 
pipeline) or better.

### Priority 3: Audit the 26 "different output" tests

These pass on both pipelines but produce different verification output. Differences
may be:
- Benign: different variable names (elaboration generates fresh `narrow$1` etc.)
- Benign: different assertion naming/ordering
- Concerning: different verification results (fewer/more VCs proved)
- Bad: V2 producing weaker verification (missed bugs)

**Action:** Compare a sample. If V2 finds the same bugs and proves the same properties
(just with different names), this is fine. If V2 misses something the old pipeline
catches, that's a correctness issue.

---

## REMAINING TECH DEBT

| Item | Description | Architecture reference |
|------|-------------|----------------------|
| `from_Composite` prelude | Reverted — needs re-addition | §"Subtyping and Narrowing Discipline" |
| Stub integration | Library stubs not loaded | §"Library Stubs: Eliminating PySpec" |
| Metadata in projection | Some nodes get `#[]` metadata | §"Metadata: Monad-Comonad Interaction Law" |

---

## OPERATIONAL DISCIPLINE (unchanged)

- Architecture + Plan are God
- Every implementation agent gets parallel review agent
- Standard preamble for all agents
- Plan before code
- Commit after every successful build
- Kill on architecture violations
- Never ask the user implementation questions — the spec answers them
