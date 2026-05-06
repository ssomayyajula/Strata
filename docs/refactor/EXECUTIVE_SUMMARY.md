# Executive Summary: Agent-Driven Methodology for the Python→Laurel Refactor

## Why We're Doing This

The existing Python→Laurel translation pipeline (2100 lines) works but is unmaintainable,
unextensible, and fragile. It was built incrementally without a formal architecture, leading
to systemic problems that surface in every PR and review cycle.

### Problems with the Previous Implementation

**1. Correctness not enforced by types — bugs pass compilation and tests.**

In PR #835 ("Laurel: Lift Procedure Calls in Asserts"), an agent-authored commit 
(`97bce95`) introduced a bug where `getLast` selected the ERROR output channel of a 
multi-output procedure instead of the primary return value. The generated code used 
`$c_1` (the error channel) where it should have used `$c_0` (the result). This compiled
cleanly and passed tests — both variables were valid at that program point with compatible
Lean types. The bug was caught only by human review of the generated Laurel output.

**Root cause:** The Lean types don't encode "which output variable is semantically correct."
`lake build` verifies Lean well-typedness, not semantic translation correctness.

**2. Multiple PRs attacking the same problem without a shared discipline.**

The Composite↔Any coercion problem (Issue #882: 13 failing tests) has spawned at least
4 PRs with incompatible approaches:

| PR | Approach | Status |
|----|----------|--------|
| #727 | Emit `Hole` (unconstrained value) — avoids crash, loses precision | Merged |
| #918 | Rename heap datatypes + coercion pathways | Draft (Git conflicts) |
| #954 | DynamicComposite wrapping + heap parameterization | Open (134 comments, architectural disagreement) |
| #1106 | Coerce args to Any at call sites | Open (defeats precondition model) |

PR #954's 134-comment thread reflects a fundamental architectural disagreement: one
approach extends `FieldSelect` with heap parameterization, the other uses opaque
`read`/`update` procedures. Neither can yield because there's no written architecture
to appeal to.

**Root cause:** No formal subtyping/narrowing discipline specifying when Composite↔Any
coercions fire, at what pipeline stage, and via what mechanism.

**3. Sequential bottleneck from architectural disagreements.**

- PR #753 (pipeline restructuring): 472 comments, 195 commits, ~2 months of iteration
- PR #475 (CoreSMT pipeline): open since Feb 2026, has Git conflicts
- PR #954: blocked on unresolved design disagreement for weeks

These aren't slow reviews — they're the absence of a shared architecture causing
repeated rework. Each iteration discovers a new unstated assumption that conflicts
with the reviewer's model.

**4. Lowering passes mask translation bugs and create ordering dependencies.**

PR #1011 (bot-authored, still Draft) exposes a pass-ordering bug: `HeapParameterization`
generates uninitialized local variables inside assertions that `LiftExpressionAssignments`
then fails to handle. The bug exists because:
- Translation produces structurally invalid Laurel
- Heap parameterization transforms it into a DIFFERENT structurally invalid form
- The expression lifter can't recover

Similarly, PR #727's `Hole` approach explicitly acknowledges masking: "Composite values
are replaced with Hole (unconstrained Any value) since Composite→Any coercion is not
yet modeled. This limits bug-finding ability."

**5. Agent contributions require expensive human oversight.**

The `keyboardDrummer-bot` has 55 PRs (12 open, 43 merged). While productive, agent
contributions consistently require human review to catch semantic correctness issues
(PR #835 being the clearest example). The cost: every agent PR must be manually
verified against an architecture that exists only in the reviewer's head.

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
