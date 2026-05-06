# Executive Summary: Agent-Driven Methodology for the Python→Laurel Refactor

## Why We're Doing This

The existing Python→Laurel translation pipeline (2100 lines) works but is unmaintainable,
unextensible, and fragile. It was built incrementally without a formal architecture, leading
to systemic problems that surface in every PR and review cycle.

### Problems with the Previous Implementation

**1. Correctness not enforced by types — bugs pass code review.**

PR #835 introduced a subtle bug in its first implementation pass because the Lean
types did not prevent generating incorrect Laurel output. The code compiled, tests
passed, but the semantic translation was wrong. The bug was only caught during manual
review — the type system offered no protection. This is symptomatic: `lake build`
verifies that Lean code is well-typed, not that the translation is semantically correct.

**2. Multiple PRs attacking the same problem from different angles.**

The Composite↔Any coercion issue has been approached from multiple PRs with different
assumptions about where the coercion belongs, whether it should be a Hole (unsound
approximation), a `from_Composite` injection, or handled by heap parameterization.
Without a formal subtyping/narrowing discipline specifying the exact relation and
where coercions are inserted, each PR makes a locally reasonable choice that may
conflict with other PRs' assumptions.

**3. Sequential bottleneck from implicit dependencies.**

PRs depend on each other's unstated assumptions. PR B assumes PR A's output has a
certain shape, but A's shape changes during review. This creates sequential
dependencies that prevent parallel work. A shared architecture with typed interfaces
between passes would make these dependencies explicit and allow independent development.

**4. Lowering passes mask elaboration bugs.**

The 8 lowering passes in `translateWithLaurel` (heap parameterization, type hierarchy,
short-circuit desugaring, ANF lifting, etc.) run after translation and silently fix up
structural issues in the output. This means Translation can produce subtly wrong Laurel
and the lowering passes compensate — until they don't, and the bug surfaces as a cryptic
Core type error far from the source.

**5. No differential testing baseline.**

There is no automated mechanism to verify that a change doesn't regress previously-passing
tests. The in-tree tests exercise the full pipeline (Python → SMT), making it impossible
to distinguish "translation bug" from "verification timeout" from "SMT solver quirk."

---

## The Solution: Agent-Driven Methodology

### Architecture as Single Source of Truth

A formally-grounded architecture document (`ARCHITECTURE.md`) defines:
- The exact pipeline: Resolution → Translation → Elaboration → Projection → Core
- The type-theoretic foundations: FGCBV (Levy 2003), bidirectional typing (Dunfield &
  Krishnaswami 2021), polarized subtyping (Lakhani & Pfenning 2022), algebraic effects
  (Bauer 2018)
- The subtyping/narrowing discipline: when and how coercions are inserted
- The engineering principles: representation invariants, no boolean blindness, catamorphisms,
  monad-comonad interaction

Every implementation decision traces to a specific section of this document. If it
doesn't, it's wrong.

### Implementation Plan Derived from Architecture

A separate implementation plan (`IMPLEMENTATION_PLAN.md`) maps each architecture section
to concrete code changes. It tracks:
- What's done, what's next, what's blocked
- The exact current state (which tests pass, which fail, why)
- Tech debt with architecture references
- Compliance checks (grep commands that detect violations)

### Agent-Driven Development with Formal Discipline

Implementation is driven by AI agents operating under strict constraints:

**Standard Preamble** (`AGENT_PREAMBLE.md`): Every agent reads this before writing code.
It mandates:

- Mechanical derivation from the spec (not problem-solving)
- No heuristics, no peephole optimizations, no boolean blindness
- Types determine the implementation (no choices)
- Plan before code
- Stop on gaps (don't invent workarounds)

**Parallel Review Agents**: Every implementation agent gets a parallel review agent that:

- Checks code compliance (grep-based violation detection)
- Reads the implementation agent's transcript for process compliance
- Reports violations immediately
- Recommends KILL if the agent deviates from architecture

**Kill Criteria**: Agents are immediately terminated if they:
- Add coercions to Translation (elaboration's job)
- Skip elaboration
- Add boolean gates (isPreludeFunc, isUserFunc)
- Type things as `Any` when annotations exist
- Add peephole optimizations or heuristics
- Fall back to "what the old pipeline does"

**Iterative Learning**: When an agent is killed, its transcript is read to identify
what it tried and where it failed. The next agent gets these lessons in its prompt.
Prevents the same failure from recurring.

### Correctness by Construction via FineGrainLaurel Types

The core technical innovation: FineGrainLaurel's `Value` and `Producer` types (generated
by DDM from a dialect file) make illegal states UNREPRESENTABLE at the Lean type level:

- You cannot put a Producer in value position (Lean type error)
- You cannot skip a coercion (the types don't unify without it)
- You cannot conflate effectful and pure subexpressions (different types)

This means: if the elaboration compiles, it's structurally correct. `lake build` IS
a meaningful correctness check because the types encode the invariants.

### Differential Testing Infrastructure

A proper testing script (`diff_test.sh`) captures the old pipeline's output as a
baseline and compares the new pipeline against it:
- SAME: identical output (no regression)
- IMPROVED: new pipeline succeeds where old failed
- REGRESSION: new pipeline fails where old succeeded (blocks)

This provides confidence that we're not introducing regressions — something the
previous PR-based workflow couldn't guarantee.

### Parallelization Enabled by Shared Architecture

With a written architecture:
- Multiple agents can work on different passes simultaneously (Resolution, Translation,
  Elaboration are independent given the interface types)
- Reviews are mechanical (check against architecture, not personal judgment)
- Assumptions are explicit and shared (not implicit in one person's head)
- PRs can be verified independently (each one either follows the architecture or doesn't)

---

## Results So Far

| Metric | Old Pipeline | New Pipeline (in progress) |
|--------|-------------|---------------------------|
| Architecture doc | None | 1100 lines, formally grounded |
| Separation of concerns | 1 monolithic function | 4 passes with typed interfaces |
| Type safety | None (same Lean type in/out) | FGL Value/Producer enforce polarity |
| Coercion correctness | Ad-hoc (from_int sprinkled everywhere) | Bidirectional typing (mechanically determined) |
| Heap handling | Separate ad-hoc pass | Co-operations in elaboration (Bauer 2018) |
| Regression detection | Manual review | Automated differential testing |
| Parallelizability | Blocked by shared mutable state | Independent passes, typed interfaces |
| Tests passing (V2) | N/A | 18/54 (4 remaining regressions from elaboration gaps) |

---

## What's Different This Time

The previous approach to improving the pipeline was: write code, review code, iterate.
This failed because:

- No shared definition of "correct"
- Reviews were judgment calls, not mechanical checks
- Contributors could disagree and both be "right" under their own assumptions

The new approach is: define correctness formally (architecture), derive implementation
mechanically (plan), verify compliance automatically (review agents), test differentially
(baseline comparison). The human's job is architectural decisions. The machine's job is
correct transcription.
