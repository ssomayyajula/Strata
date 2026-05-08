# Executive Summary: Python→Laurel Pipeline Refactor

## The Case for a Rewrite

The existing Python→Laurel translation pipeline (2100 lines + 8 lowering passes)
works for the tests it was built against. But it has reached a point where adding
new features or fixing cross-cutting bugs requires disproportionate effort — not
because the code is poorly written, but because the architecture makes certain
classes of problems structurally unsolvable without a rewrite.

This document presents the evidence: specific PRs and issues where the current
architecture forced weeks of iteration, architectural disagreement, or incomplete
solutions. It then presents the replacement architecture and its current status.

---

## Evidence: Structural Problems in the Current Pipeline

### Problem 1: Type Coercions Are Unpredictable

**Issue #882:** 13 failing tests from Composite↔Any type mismatches.

**What happened:** Core's type checker rejects programs where `Composite` appears
where `Any` is expected (or vice versa). The old pipeline inserts coercions
(`from_Composite`, `Any..as_Composite!`) ad-hoc in Translation. But Translation
doesn't have a principled rule for WHEN to coerce — it's case-by-case pattern
matching scattered across 2100 lines.

**The attempted fixes:**

| PR | Approach | Outcome |
|----|----------|---------|
| #727 | Emit `Hole` (unconstrained value) — avoids crash, loses precision | Merged, but explicitly acknowledges "limits bug-finding ability" |
| #918 | Rename heap datatypes + coercion pathways | Draft, Git conflicts, abandoned |
| #954 | DynamicComposite wrapping + heap parameterization | 100+ comments, architectural disagreement, still open |
| #1106 | Coerce all args to Any at call sites | Open, defeats the precondition model entirely |

**Why it's structural:** Each PR proposes a different heuristic because there IS no
rule. The old pipeline does coercions inside Translation (which doesn't know types)
instead of in a separate type-directed pass (which does). You cannot fix this by
adding more cases to Translation — you need a separate elaboration pass that knows
the type of every subexpression and inserts coercions at type boundaries.

**What theory says:** Bidirectional typing (Dunfield & Krishnaswami 2021) provides
a deterministic algorithm: synthesize the expression's type, check it against the
expected type, insert the coercion witness at the subsumption boundary. One rule,
one location, zero guessing.

---

### Problem 2: Lowering Passes Create Ordering Dependencies

**PR #1011** (bot-authored, still Draft): `HeapParameterization` generates
uninitialized local variables inside assertions. `LiftExpressionAssignments`
can't handle this. The program is structurally invalid after one pass and a
different kind of structurally invalid after the next.

**The 8 lowering passes:**
1. `heapParameterization` — thread Heap through field-touching procedures
2. `typeHierarchyTransform` — adjust Composite types
3. `modifiesClausesTransform` — add modifies annotations
4. `inferHoleTypes` — fill in types for Hole nodes
5. `eliminateHoles` — remove Hole nodes
6. `desugarShortCircuit` — rewrite `&&`/`||`
7. `liftExpressionAssignments` — ANF-lift calls out of expressions
8. `constrainedTypeElim` — eliminate constrained types

Each pass assumes the output of the previous pass has specific structural
properties. When one pass produces unexpected output, the next one crashes or
silently produces wrong results. Debugging requires understanding the interaction
of ALL 8 passes.

**Why it's structural:** The passes exist because Translation produces output that
Core can't directly handle. Each pass fixes one thing Translation didn't do. But
the fixes interact. You cannot add a 9th pass to fix the interaction of passes 3
and 7 without potentially breaking the assumption of pass 8.

**What theory says:** Fine-Grain Call-By-Value (Levy 2003) separates values from
producers in the TERM STRUCTURE. If Translation produces well-typed FGCBV terms,
no lowering passes are needed — the output is already in a form Core can consume.
All 8 passes are subsumed by a single elaboration pass that produces correct
output by construction.

---

### Problem 3: Illegal States Are Representable

**PR #835** ("Laurel: Lift Procedure Calls in Asserts"): An agent-authored commit
(fixed in `001e735`) used `getLast` which selected the error output of a
multi-output procedure instead of the primary result.
The code compiled. The tests passed. Both variables were valid at that program point
with compatible Lean types. The bug was caught only by human review.

**Why it's structural:** The Lean types of `$c_0` and `$c_1` are both `StmtExprMd`.
There is no type-level distinction between "the result output" and "the error output."
Any refactoring that swaps them compiles cleanly. This is not a testing gap — it's
a representation gap. The types don't encode the invariant.

**What theory says:** HOAS (Higher-Order Abstract Syntax) smart constructors bind
output variables via closures. The continuation receives `rv` (the result) as a
function parameter — `$c_1` (the error output) literally doesn't exist in scope.
You cannot reference the wrong variable because the wrong variable isn't a term
you can construct.

---

### Problem 4: Architectural Disagreement Blocks Progress

**PR #753** (pipeline restructuring): 195 commits, ~1 month (Apr 3 → May 1, 2026).

**PR #954**: Blocked for weeks on whether field access should use heap
parameterization or opaque read/update procedures. Both approaches are defensible.
Neither can yield because there's no written architecture to appeal to.

**Why it's structural:** When the architecture exists only in reviewers' heads,
every PR is a negotiation between implicit mental models. The reviewer says "this
should be a Composite" and the author says "I think it should stay as Any." Neither
is wrong — they're operating under different unstated assumptions about when
coercions should fire.

**What theory says:** A written formal specification (graded FGCBV with bidirectional
typing) provides a single source of truth. "Should this be Composite or Any?" is
answered by: "What does `synthValue` produce? What does the context expect? The
subsumption table determines the coercion." No negotiation. No judgment calls.

---

### Problem 5: Every Python Construct Requires Whole-Pipeline Reasoning

Adding support for a new Python construct (e.g., `match` statements, walrus
operator, decorated functions) currently requires:
1. Adding Translation cases
2. Checking if any of the 8 lowering passes interact badly
3. Verifying Core handles the new output
4. Testing end-to-end (no intermediate checks possible)

The blast radius of any change is the entire pipeline. There's no way to verify
that Translation's output is correct in isolation — you can only test it after
all passes have run and Core has type-checked it.

**In the new pipeline:** Adding a Python construct means:
1. Add one case to Translation (emit Laurel)
2. Add one typing rule to Elaboration (if the construct has non-trivial effects)
3. Both are independently checkable: Translation's output must be well-formed
   Laurel, Elaboration's typing rules must be mode-correct

---

## The Replacement: Theory-Grounded Elaboration

### Architecture

A 1000+ line formal specification (`ARCHITECTURE_V2.md`) grounding every decision:

| What | How | Theory |
|------|-----|--------|
| When coercions fire | Subsumption at check boundaries | Bidirectional typing |
| Which effects a call has | Coinductive fixpoint over call graph | Graded monoid |
| How heap is threaded | Grade determines calling convention | State-passing translation |
| What's a value vs producer | FGCBV term structure | Levy's CBPV |
| What's representable | Metadata by construction, HOAS bindings | Correct by construction |

### Pipeline

```
Python AST → [Resolution] → Γ
Python AST + Γ → [Translation] → Laurel (effects implicit)
Laurel + Γ → [Elaboration] → GFGL (effects explicit, coercions inserted)
GFGL → [Projection] → Laurel (ready for Core)
```

Three passes. No lowering. Translation handles syntax. Elaboration handles
semantics. They don't know about each other's jobs.

### Current Status (2026-05-08)

- **Zero crashes** on all 46 CI tests (old pipeline also zero crashes)
- **29/54 tests pass** (old: 28/54) — +1 genuine improvement
- **4 encoding gaps** where old pipeline proves VCs the new one can't yet
  (solver quality, not soundness)
- **Old pipeline untouched** — both coexist, old serves as baseline
- **~2500 lines new code** (Resolution + Translation + Elaboration)

### Engineering Principles Enforced

| Principle | How |
|-----------|-----|
| Illegal states unrepresentable | Unresolved names → Hole (can't emit undefined StaticCall) |
| No boolean blindness | Pattern match on NameInfo, not `isResolved : Bool` |
| No strings for types | `annotationToHighType` from AST directly, Union → Any in Resolution |
| Metadata by construction | Every FGL term carries `md` from source (can't lose source locations) |
| Grade determines calling convention | `mkGradedCall` uses declared outputs (can't get arity wrong) |

---

## The Ask

Replace the old `PythonToLaurel.lean` + 8 lowering passes with the new
Resolution → Translation → Elaboration pipeline. The old pipeline continues
to exist as a parallel path (`pyAnalyzeLaurel`) until the new pipeline
(`pyAnalyzeV2`) achieves full feature parity on the 52 Kiro benchmarks.

The investment is already made (architecture + implementation exist). The
remaining work is encoding quality improvements to close the 4 solver gaps
and extending Translation to handle the full Python construct set needed by
the benchmarks.
