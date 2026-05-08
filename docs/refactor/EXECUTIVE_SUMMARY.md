# Executive Summary: Python→Laurel Pipeline Refactor

## Summary

The Python→Laurel translation pipeline is being replaced with a new architecture
that introduces a single, written specification governing how type coercions are
inserted, how effects are tracked, and what intermediate representations are valid.

The existing pipeline (2100 lines of translation + 8 lowering passes) has no such
specification. As a result, contributors operate under different mental models of
when coercions should fire, how effects compose, and what constitutes valid
intermediate output. This leads to:

- **Multiple competing PRs for the same bug** (4 open/merged PRs for Issue #882,
  each with a different coercion heuristic, none grounded in a shared rule)
- **Illegal states that compile and pass tests** (PR #835: wrong output variable
  selected, caught only by human review because the Lean types don't distinguish
  result from error outputs)
- **Pass-ordering bugs from implicit structural assumptions** (PR #1011: one
  lowering pass produces output another pass can't handle)
- **Blocked PRs from architectural disagreement** (PR #954: 100+ comments, still
  open, because there's no written rule to appeal to)

The new architecture addresses these by providing a single source of truth
(`ARCHITECTURE_V2.md`) that determines coercion insertion, effect classification,
and calling conventions. The implementation is a mechanical transcription of this
specification. When a question arises ("should this be Composite or Any?"), the
specification answers it — not a reviewer's mental model.

---

## Problems with the Current Pipeline

### 1. Type coercions have no governing rule

Core's type checker requires explicit coercions between `Composite` and `Any`.
The current pipeline inserts these ad-hoc in Translation, without a systematic
rule for when they're needed.

Issue #882 documents 13 failing tests from this. Four PRs have attempted fixes:

| PR | Approach | Outcome |
|----|----------|---------|
| #727 | Replace Composite values with Hole (unconstrained) | Merged; explicitly "limits bug-finding ability" |
| #918 | Rename heap datatypes + coercion pathways | Draft, abandoned (Git conflicts) |
| #954 | DynamicComposite + heap parameterization extension | 100+ comments, architectural disagreement, still open |
| #1106 | Coerce all args to Any at call sites | Open; reviewer notes it "defeats the type-wrapping discipline" |

Each PR proposes a different heuristic because there is no shared rule. The
current Translation doesn't have access to the type of each subexpression at
the point where it would need to insert a coercion — it handles syntax, not types.

The new pipeline separates these concerns: Translation handles syntax (producing
precisely-typed Laurel), and a separate Elaboration pass handles type-directed
coercion insertion. The Elaboration pass has a complete subsumption table that
determines exactly when `int → Any` (via `from_int`) or `Any → Composite` (via
`Any..as_Composite!`) is needed. This table is written in the specification and
implemented as a single function.

### 2. Lowering passes have implicit ordering dependencies

The current pipeline applies 8 Laurel→Laurel transformations between Translation
and Core:

1. `heapParameterization` 2. `typeHierarchyTransform` 3. `modifiesClausesTransform`
4. `inferHoleTypes` 5. `eliminateHoles` 6. `desugarShortCircuit`
7. `liftExpressionAssignments` 8. `constrainedTypeElim`

Each pass assumes specific structural properties of its input. When one pass
produces unexpected output, subsequent passes may crash or silently produce
incorrect results.

PR #1011 (Draft) documents a concrete instance: `heapParameterization` generates
uninitialized `LocalVariable` nodes inside assertion conditions, which
`liftExpressionAssignments` cannot handle. The fix requires understanding how
both passes interact — a property not documented anywhere.

The new pipeline eliminates all 8 passes. The Elaboration pass produces output
that Core can consume directly, because it makes effects explicit in the term
structure (values vs. producers, graded calling conventions). There is no
intermediate representation that requires further transformation.

### 3. The intermediate representation allows illegal states

PR #835 ("Lift Procedure Calls in Asserts") introduced a bug where `getLast`
selected a procedure's error output instead of its result (fixed in `001e735`).
The code compiled and tests passed because both output variables have the same
Lean type (`StmtExprMd`). The bug was caught only by manual review of generated
Laurel output.

This is a representation problem: the Lean types don't encode which output
variable is the result and which is the error channel. Any transformation that
reorders or selects outputs must be manually verified.

The new pipeline uses HOAS (Higher-Order Abstract Syntax) smart constructors that
bind output variables via closures. The continuation function receives only the
result variable as a parameter — the error output is not in scope and cannot be
referenced accidentally. This makes the bug class from PR #835 unrepresentable.

### 4. No shared specification means PRs become negotiations

PR #753 (pipeline restructuring) required 195 commits over ~1 month before merge.
PR #954 has been open for weeks with 100+ comments and unresolved disagreement
about whether field access should use heap parameterization or opaque read/update
procedures.

These are not slow reviews — they are the cost of having no written specification
to arbitrate. When the correct behavior is defined only in reviewers' heads,
every PR is a negotiation between implicit mental models.

The new architecture provides a 1000+ line specification that answers these
questions deterministically. "Should this field access use heap parameterization?"
is answered by the grade of the enclosing procedure (determined by coinductive
fixpoint) and the calling convention table (written in the spec).

### 5. Adding new Python constructs requires whole-pipeline reasoning

Supporting a new Python construct currently requires modifying Translation,
verifying that none of the 8 lowering passes interact badly with the new output,
and testing end-to-end (there is no intermediate correctness check).

In the new pipeline, adding a Python construct requires adding one case to
Translation (emit Laurel nodes) and, if the construct has non-trivial effects,
one typing rule to Elaboration. Both can be verified independently.

---

## The New Architecture

The replacement pipeline is governed by a formal specification
(`ARCHITECTURE_V2.md`, 1000+ lines) that defines:

- A **subsumption table** specifying all type coercions and when they fire
- A **grade monoid** `{pure, proc, err, heap, heapErr}` classifying effects
- **Calling conventions** derived from grades (which outputs to bind, whether to pass heap)
- **Typing rules** for every Laurel construct (bidirectional: synthesize types bottom-up, check top-down)
- **Engineering invariants** (illegal states unrepresentable, metadata by construction)

The pipeline has three passes:

```
Python AST + Γ → [Translation] → Laurel (effects implicit)
Laurel + Γ    → [Elaboration] → GFGL (effects explicit, coercions inserted)
GFGL          → [Projection]  → Laurel (ready for Core)
```

Translation handles Python's surface syntax. Elaboration handles types and effects.
They are independent: Translation does not insert coercions, Elaboration does not
handle Python-specific desugaring.

---

## Current Status (2026-05-08)

| Metric | Old Pipeline | New Pipeline |
|--------|-------------|-------------|
| CI test crashes | 0 | 0 |
| Tests passing | 28/54 | 29/54 (+1) |
| Lowering passes required | 8 | 0 |
| Written specification | None | 1000+ lines |
| Coercion rule | Ad-hoc (scattered across Translation) | Subsumption table (one function) |
| Adding a Python construct | Modify Translation + verify 8 pass interactions | Add Translation case + typing rule |

The old pipeline remains operational as a parallel path (`pyAnalyzeLaurel`) and
serves as the correctness baseline for differential testing.

Four tests remain where the old pipeline proves VCs that the new pipeline cannot
yet. These are solver-level encoding quality gaps (the new pipeline's encoding
of try/except generates more complex VC structure), not soundness issues.

---

## The Ask

Adopt the new pipeline (`pyAnalyzeV2`) as the path forward for the Python frontend.
The old pipeline continues to operate in parallel until the new pipeline achieves
feature parity on the Kiro benchmarks (52 annotated tests). The architecture
specification becomes the single source of truth for coercion, effect, and calling
convention questions — replacing ad-hoc judgment in PR reviews.
