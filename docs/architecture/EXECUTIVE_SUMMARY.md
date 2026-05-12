# Executive Summary: Architecture-Driven Python Front-End Development

## The Ask

The Python front-end has endemic tool errors that resist individual fixes.
This is not the fault of any particular set of contributors — the problem is
structural: without a written architecture, each fix generates code that
interacts unpredictably with 8 lowering passes, creating a positive feedback
loop where the pipeline's actual behavior diverges further from the intended
one with each change.

A written architecture (`ARCHITECTURE.md`, 1000+ lines) now exists that
specifies coercion insertion, effect classification, and calling conventions
— providing a single check on this divergence.

**Can we commit to developing the Python front-end against this architecture?
If so, what is the strategy for collaborative development driven by the spec?**

The architecture is designed to be the synchronization point between
contributors: code that follows the spec is correct by construction,
deviations are identifiable by inspection, and design disagreements are
resolvable by reference to the document rather than implicit mental models.

---

## Background

The existing pipeline (2100 lines of translation + 8 lowering passes) has no
written specification. Without an architectural check on the volume of code
generated for fixes, contributors necessarily operate under different mental
models of when coercions should fire, how effects compose, and what
constitutes valid intermediate output. This leads to:

- **Multiple competing PRs for the same bug** (4 open/merged PRs for Issue #882,
  each with a different coercion heuristic, none grounded in a shared rule)
- **Illegal states that compile and pass tests** (PR #835: wrong output variable
  selected, caught only by human review because the Lean types don't distinguish
  result from error outputs)
- **Pass-ordering bugs from implicit structural assumptions** (PR #1011: one
  lowering pass produces output another pass can't handle)
- **Blocked PRs from architectural disagreement** (PR #954: 100+ comments, still
  open, because there's no written rule to appeal to)
- **No explicit accounting of Python coverage** (which constructs are fully
  handled, which are approximated, and which silently produce incorrect output
  is implicit in 2100 lines of code — the new architecture documents this
  explicitly in §Python Construct Coverage)

### Benchmark results fluctuate without traceable cause

The internal benchmark suite runs nightly on mainline. Between May 4 and May 8,
nine runs produced the following time series:

| Date | Commit | Benchmarks | Correct | Regressions | Tool Errors |
|------|--------|-----------|---------|-------------|-------------|
| May 4 | b7d8600a | 398 | 181 | 9 | 161 |
| May 5 (a) | b30607ea | 398 | 162 | 28 | 166 |
| May 5 (b) | 5dccfcca | 398 | 163 | 27 | 166 |
| May 6 (a) | 055beafc | 398 | 163 | 27 | 166 |
| May 6 (b) | 5ea97fb6 | 414 | 169 | 33 | 166 |
| May 7 | 3c74daea | 414 | 169 | 33 | 166 |
| May 8 (a) | 76bca524 | 414 | 168 | 34 | 166 |
| May 8 (b) | 920195e5 | 414 | 169 | 33 | 166 |
| May 8 (c) | 5f5a7013 | 414 | 168 | 34 | 166 |

Two patterns are visible:

1. **Cliff between May 4 and May 5:** Correct dropped from 181 → 162 (−19),
   regressions jumped from 9 → 28 (+19), tool errors increased from 161 → 166
   (+5). Multiple PRs landed in this window. The regressions are almost entirely
   "Resolution failed: 'name' is not defined" — a name-resolution invariant was
   violated, but there is no written rule that would identify which PR broke it.

2. **Noise after May 6:** Correct oscillates between 168 and 169; regressions
   between 33 and 34. The ±1 is a single benchmark (`demo_glue_service` or
   `setup_cloudformation_delegated_admin`) non-deterministically timing out at
   the 40s budget. This is not a code change — it's solver variance.

The difficulty is not that things got worse — it's that we cannot explain WHY
the May 4→5 cliff happened. There is no specification to trace a regression
back to a violated invariant. When "Resolution failed: 'name' is not defined"
appears on 19 benchmarks after a field-access fix, the question "which
assumption did we break?" has no written answer to point to.

With a specification, every regression is traceable: either the implementation
deviated from the spec (implementation bug, fixable by re-reading the spec) or
the spec itself has a gap (architecture bug, fixable by extending the spec).
Without one, regressions require whole-pipeline debugging to attribute.

### Why this matters now: agentic development and review cost

Our development flow is increasingly agentic — code generation is cheap, but
reviewing the resulting volume of code is expensive. In this context, the absence
of a written architecture is not merely an inconvenience; it is the primary
bottleneck. Without a specification to review against, every generated PR requires
the reviewer to reconstruct the author's intent and verify it against an unwritten
mental model. This does not scale.

The long tail of stabilization in the current pipeline — where fixing one type coercion
bug introduces another, which requires a lowering pass fix, which breaks an
assumption in a third pass — has reduced our confidence in being able to deliver
front-end improvements in a predictable amount of time. The ping-ponging of bug
fixes (Issue #882 spawning 4 PRs over months, PR #954 blocked for weeks) is not
a staffing problem. It is the cost of having no synchronization point between
contributors' mental models.

The architecture specification serves as that synchronization point. It is the
single check and balance against runaway bug introduction: code that follows the
spec is correct by construction, and code that deviates from it is identifiable
by inspection rather than by waiting for downstream failures.

The new architecture addresses these by providing a single source of truth
(`ARCHITECTURE.md`) that determines coercion insertion, effect classification,
and calling conventions. The implementation is a mechanical transcription of this
specification. When a question arises ("should this be Composite or Any?"), the
specification answers it — not a reviewer's mental model.

---

## Problems with the Current Pipeline

### 1. Endemic internal errors (example: ad-hoc type coercion)

Internal errors and tool errors from type mismatches are endemic to the existing
pipeline. The Composite↔Any coercion problem is not an isolated issue — it is a
representative example of a broader pattern where the pipeline produces output
that Core's type checker rejects, because there is no specification governing
when type coercions should be inserted.

Core's type checker requires explicit coercions between `Composite` and `Any`.
The current pipeline inserts these ad-hoc in Translation, without a systematic
rule for when they're needed.

Issue #882 documents 13 failing tests from this class of error alone. Four PRs
have attempted fixes:

| PR | Approach | Outcome |
|----|----------|---------|
| #727 | Replace Composite values with Hole (unconstrained) | Merged; explicitly "limits bug-finding ability" |
| #918 | Add Composite→Any coercion for containers/comparisons + rename Box→$Box | Draft, abandoned (Git conflicts) |
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

### 3. No architectural discipline prevents incorrect transformations

PR #835 ("Lift Procedure Calls in Asserts") initially lifted assignments out of
assert conditions — which is semantically incorrect (assignments in asserts should
be rejected, not silently hoisted). Review caught this and the scope was narrowed
to lift only procedure calls. A secondary issue then emerged: for multi-output
procedures, the lifting logic selected the wrong output variable (the error channel
instead of the result), because both have the same Lean type (`StmtExprMd`).

Two problems are visible here:

1. **No rule specifying what can be lifted from asserts.** The pass had to be
   iteratively refined through review because there was no written specification
   of assert semantics to implement against. The initial over-lifting was a
   reasonable interpretation — it just happened to be wrong.

2. **Output variables are not distinguished by type.** The result and error
   outputs of a procedure call are both `StmtExprMd`. Any code that selects
   between them must be manually verified — the type system doesn't help.

The new pipeline addresses both: the architecture specifies exactly which
constructs are values (can appear in assert conditions) vs. producers (must be
bound at statement level). And the elaborator's smart constructors bind output
variables via closures — the continuation receives only the result, so the error
output is not in scope and cannot be accidentally referenced.

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
is answered by the grade of the enclosing procedure (determined by coinduction
on the call graph) and the calling convention table (written in the spec).

### 5. Adding new Python constructs requires whole-pipeline reasoning

Supporting a new Python construct currently requires modifying Translation,
verifying that none of the 8 lowering passes interact badly with the new output,
and testing end-to-end (there is no intermediate correctness check). For example,
adding `match` statement support would require verifying interactions with
`heapParameterization`, `liftExpressionAssignments`, and `constrainedTypeElim` —
none of which document their input assumptions.

In the new pipeline, adding a Python construct requires adding one case to
Translation (emit Laurel nodes) and, if the construct has non-trivial effects,
one typing rule to Elaboration. Both can be verified independently: Translation's
output must be well-formed Laurel (checkable by inspection), and Elaboration's
typing rules must be mode-correct (checkable against the bidirectional discipline).

This containment of blast radius is particularly important for validation of the
front-end, which is one of our team's key goals. With separated passes and
explicit intermediate invariants, we can validate each stage independently —
confirming that Translation produces correct desugaring, that Elaboration
preserves semantics, and that the composition is sound — rather than treating
the entire pipeline as an opaque function from Python to Core.

---

## Relationship to Existing Documentation Efforts

PRs #1136 ("Document the Python front-end") and #1144 ("Document the design of
Laurel") are open and add valuable narrative documentation. They describe WHAT the
pipeline does: the stages, data structures, naming conventions, supported constructs,
and general design rationale.

These documents serve a different purpose than the architecture specification
described here. They do not aim to specify:

- **When coercions fire.** PR #1136 documents the Any-boxing encoding (constructors
  like `from_int`, destructors like `Any..as_int!`) but does not specify the rule
  for when Translation should insert them. A contributor reading the doc still
  cannot determine whether a given expression needs wrapping without studying the
  existing code.

- **What constitutes valid intermediate output.** Neither doc specifies structural
  invariants that each pass's output must satisfy. Without these, pass-ordering
  bugs (PR #1011) remain possible — a pass can produce "valid Laurel" that the
  next pass cannot handle.

- **How to arbitrate design disagreements.** PR #954's 100+ comment thread exists
  because both approaches are consistent with a WHAT-level description. A
  specification that determines calling conventions from grades would resolve it:
  the grade lattice computes which approach is correct.

A related issue: the current pipeline's tech debt and Python construct coverage gaps
are not explicitly documented. It is currently difficult to give a straight answer
to the question "what does the Python front-end actually support?" without reading
2100 lines of translation code. Which constructs are fully handled, which are
approximated (e.g., Hole), and which silently produce incorrect output is implicit
in the implementation rather than stated anywhere.

The existing documentation efforts and this work are complementary. PRs #1136
and #1144 document the system as it is — essential for onboarding and debugging.
The architecture specification documents what the system should become, with enough
precision that implementation is mechanical and disagreements are resolvable by
reference to the spec.

---

## The Architecture

The specification (`ARCHITECTURE.md`) governs the front-end pipeline from
Python AST to Core. It is prescriptive — determining exactly when coercions
fire, how effects compose, and what calling conventions to use — so that
implementation is mechanical and disagreements are resolvable by reference.

### Pipeline

```
Python AST + library stubs
  ↓ [Resolution: build Γ — type environment with all signatures]
Γ : TypeEnv
  +
Python AST (user code)
  ↓ [Translation: fold over AST, type-directed via Γ]
e : Laurel.Program (impure CBV — precisely-typed, effects implicit)
  ↓ [Elaboration: graded bidirectional typing, coinduction on call graph]
e' : GFGL.Program (Graded Fine-Grain Laurel — effects explicit)
  ↓ [Projection: forget grading, trivial structural map]
Laurel.Program (ready for Core)
  ↓ [Core translation (existing, unchanged)]
Core
```

**Resolution** walks the Python AST and library stubs to build a unified type
environment where every name has a complete signature. After resolution,
Translation can look up any name and determine its parameter types, return
type, and defaults without guessing.

**Translation** is a deterministic fold over the Python AST — one case per
constructor. It desugars Python's surface syntax (classes → New + __init__,
for loops → havoc + assume, context managers → enter/exit, kwargs → positional
resolution via Γ) into flat Laurel. It does not insert coercions or determine
effects. If a name is not in Γ, it emits Hole (nondeterministic havoc) rather
than a call to an undefined function.

**Elaboration** constructs a GFGL (Graded Fine-Grain Laurel) typing derivation
from the Laurel program. It discovers each procedure's grade via coinduction
on the call graph, then elaborates each body: inserting
coercions at type boundaries (governed by the subsumption table), threading
heap state (governed by grades), and binding effectful subexpressions at
statement level via ANF-lifting (governed by the to-rule). The output term
IS the typing derivation — if it type-checks, it's semantically correct.

**Projection** is a trivial structural map that forgets the grading, producing
Laurel that Core's existing translator can consume. The effect information is
now encoded in procedure signatures and calling conventions rather than in
the type system.

Translation handles Python's surface syntax. Elaboration handles types and effects.
They are independent: Translation does not insert coercions, Elaboration does not
handle Python-specific desugaring.

---

## Traceability: Current Problems → Architecture Sections

Each problem identified above is addressed by a specific section of the
architecture specification. The table below provides traceability from
the evidence of the problem to the part of the spec that prevents it
from recurring. This is the key property of a prescriptive architecture:
every known failure mode maps to a rule that makes it unrepresentable or
mechanically detectable.

| Problem | Evidence | Architecture Section |
|---------|----------|---------------------|
| No rule for when coercions fire | Issue #882, PRs #727/#918/#954/#1106 | §Subtyping (witness table) |
| Pass-ordering bugs | PR #1011 | §Elaboration (single pass, no lowering) |
| Illegal states representable | PR #835 | §GFGL Type System (values vs producers) |
| Architectural disagreement | PR #954 (100+ comments) | §Grade Monoid, §Subgrading (witness table) |
| Whole-pipeline blast radius | Every new construct | §Translation (syntax), §Elaboration (semantics) |
| No specification to implement against | PRs #1136/#1144 document WHAT not WHEN/HOW | §The Translation ⟦·⟧, §Producer Checking Rules |
| Undocumented Python coverage | Implicit in 2100 lines | §Python Construct Coverage |
| Laurel function/procedure distinction not enforced | Runtime procs nested in expressions crash Core | §Grade Monoid (proc grade), §Producer Synthesis |

---

## Vignette: Diagnosing and Fixing a Bug Class via the Architecture

The new pipeline is not bug-free — but when bugs arise, the architecture
makes them diagnosable and fixable in a principled way. An example:

**The bug:** Runtime procedures like `datetime_now()` were being nested inside
expressions (e.g., `x := Any..as_Composite!(datetime_now())`). Core rejects
procedure calls in expression position, producing "0-ary op not found" errors.

**Diagnosis via the architecture:** The grade monoid `{pure, err, heap, heapErr}`
had no grade for "must be at statement level but has no specific effect." The
architecture's value rule requires `grade(f) = 1` for a call to appear in an
expression. But `datetime_now` was classified as `pure` (grade 1) because
`gradeFromSignature` only checked for Error/Heap — not whether the callee is
a Laurel `function` vs `procedure`.

**The fix:** Extend the grade monoid to `{pure, proc, err, heap, heapErr}`.
Update `gradeFromSignature` to check `isFunctional`. Update `synthValue` to
reject grade > pure. Update `mkGradedCall` to handle `proc`. Each change
traced directly to a section of the architecture — the grade lattice, the
value rule precondition, the calling convention table.

**Time to resolution:** One session. The architecture told us exactly what was
missing (a grade for non-functional procedures), where to add it (the monoid,
the signature function, the value rule), and how to verify the fix (grade trial
list, calling convention dispatch). Compare this to PR #954's 100+ comments
over weeks — same pipeline, same class of problem (calling convention confusion),
but no specification to guide the resolution.

The point is not that the new pipeline avoids bugs. It's that when bugs occur,
the architecture provides a framework for diagnosing root causes and verifying
fixes — rather than iterating through heuristics in PR review.

