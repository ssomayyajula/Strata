# Executive Summary: Agent-Driven Methodology for the Python→Laurel Refactor

## Why We're Doing This

The existing Python→Laurel translation pipeline (2100 lines) works but is unmaintainable,
unextensible, and fragile. It was built incrementally without a formal architecture, leading
to systemic problems that surface in every PR and review cycle.

### Problems with the Previous Implementation

**1. No North Star for architecture or implementation.**

Reviews are fragile because there's no single source of truth defining what the code
SHOULD be. Reviewers check "does this compile" and "do tests pass" but can't verify
"does this follow the architecture" because no architecture exists. Each contributor
works off different assumptions about how the pipeline should be structured.

**2. Subtle bugs from differing assumptions.**

Without a shared architecture, contributors introduce bugs by making reasonable-looking
changes that violate unstated invariants. Example: PR #835's first pass introduced
issues because the author's mental model of the pipeline differed from the reviewer's.
Neither could appeal to a written spec to resolve the disagreement.

**3. Impossible to parallelize.**

PRs get stuck in review hell because:
- Changing assumptions for successive PRs (PR B depends on PR A's assumptions, which
  change during A's review)
- No way to verify PRs independently (each one implicitly depends on the whole system)
- Reviewers can't approve without understanding the entire context

**4. `lake build` is a low bar for correctness.**

The build passing gives no confidence that the translation is correct. The type system
(Lean 4) checks Lean-level types but NOT the semantic correctness of the translation.
A procedure can type-check in Lean while producing completely wrong Laurel output.
There's no mechanism for correctness by construction.

**5. No confidence against regressions.**

Every PR potentially introduces bugs because:
- No differential testing infrastructure
- No formal specification of what the output should look like
- "Tests pass" means the SMT solver didn't reject the output — not that the output is correct
- The translation pipeline conflates multiple concerns (coercion insertion, scope handling,
  error protocol, heap parameterization) in a single 2100-line function

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
