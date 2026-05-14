# Laurel Type Checker: Doc / Implementation Discrepancies

Tracks places where `docs/verso/LaurelDoc.lean` (the *Type checking* section) and
`Strata/Languages/Laurel/TypeCheck.lean` disagree, or where the doc itself is
internally inconsistent. Each entry is intentionally narrow: it states what the
doc says, what the implementation does (or could do), and a suggested
resolution. None of these are tracked as TODOs in the source — fixing them is a
documentation/policy decision, not a code change.

## 1. Roadmap item 2 contradicts the iteration-1 `≼`

**Doc — `LaurelDoc.lean:427-433`** says:

> *Composite subtyping.* `var x: Dog := new Cat` is silently accepted.
> […] The associated regression test lives as a "no diagnostic today" pin so
> that adding subtyping flips it from passing to correctly rejecting.

**Implementation.** `isAssignable` in `TypeCheck.lean:86-89` is *equality + cascade*
(`Unknown` either side, `TVoid` actual side). `UserDefined Cat` and `UserDefined
Dog` are unequal under `highEq`, so the case produces a `mismatch` diagnostic
*today*.

**Why the doc says otherwise.** The "silently accepted" claim was true under the
*stub* `isAssignable := true`. Now that the stub is gone, the roadmap's
description of the current behaviour is wrong, and the direction of the flip is
inverted: subtyping will move that case from *rejecting* to *correctly accepting
when `Cat extends Dog`*, not the other way round.

**Suggested fix.** Rewrite roadmap-2 to:

> Today every cross-type assignment between two distinct `UserDefined` names
> is rejected because `≼` is equality. Wiring `computeAncestors` into `≼` will
> let `var x: Dog := new Cat` pass when (and only when) `Cat` extends `Dog`,
> turning the regression test from passing-but-wrong to passing-and-correct.

## 2. T-InstCall's `receiverType ≼ self` is unenforceable in iteration 1

**Doc — `LaurelDoc.lean:336-341`.** The T-InstCall rule has the premise
`receiverType ≼ self` listed alongside the rest of iteration 1.

**Implementation.** With `≼` as equality, enforcing this premise rejects every
method call on a child instance of a parent-defined method (`a Cat calling
Animal.eat()`). Today `TypeCheck.lean:194-207` skips the check and leaves a
TODO referencing the roadmap; the doc gives no permission for this elision.

**Suggested fix.** Either:
- move the `receiverType ≼ self` premise into roadmap item 2 alongside
  composite subtyping, or
- explicitly note in the T-InstCall paragraph that the premise is degenerate
  (= equality) until subtyping lands and is therefore deferred.

## 3. Cascade rule: prose mentions `TVoid`, displayed rule does not

**Doc — `LaurelDoc.lean:399-412`.** Prose: "premises that demand a value type
are vacuously satisfied when the sub-expression is statement-shaped (`TVoid`)."
Displayed rule:

```
  one of σᵢ = Unknown
─────────────────────── (cascade)
  premise σᵢ ≼ τᵢ  ✓
```

The rule mentions only `Unknown`, not `TVoid`. The two specifications disagree
about what cascades.

**Implementation.** Follows the prose: `Unknown` cascades on either side
(`TypeCheck.lean:88`); `TVoid` cascades on the actual side only
(`TypeCheck.lean:88`, `HighType.isCascade` at `:99-101`).

**Suggested fix.** Update the displayed rule to:

```
  σᵢ = Unknown,  or  σᵢ = TVoid and the premise demands a value type
──────────────────────────────────────────────────────────────────── (cascade)
                       premise σᵢ ≼ τᵢ  ✓
```

so the formal rule and the prose say the same thing.

## 4. T-Assign is silent on the malformed-grammar case

**Doc — `LaurelDoc.lean:322-327, 344-347`.** The T-Assign rule covers the
well-formed shape (`|targets| = arity(valueType)`), but the doc never specifies
what happens when `targets.length > 1` and `value` is not a multi-output
`StaticCall`, e.g. `(x, y) := 5`.

**Grammar.** `Laurel.lean:271` states "Multiple targets are only allowed when
the value is a `StaticCall` to a procedure with multiple outputs", so this case
is grammatically malformed.

**Implementation.** `TypeCheck.lean:283-286` emits a generic `.other` diagnostic
("multi-target assignment requires a static-call RHS") for that case, but a
reader of the doc has no way to predict that.

**Suggested fix.** Add a side condition or a note under T-Assign:

> When `|targets| > 1`, `value` must syntactically be a `StaticCall`; otherwise
> the construct is malformed and a diagnostic is emitted.

## 5. Procedure-level rules omit preconditions, decreases, and reads

**Doc — `LaurelDoc.lean:385-397`.** Only T-FuncProc is listed as the
iteration-1 procedure-level rule.

**Implementation.** `TypeCheck.lean:362-381` carries no checks for `proc.preconditions`,
`proc.decreases`, or `proc.determinism`'s `reads` clause. Each of these has an
obvious type expectation: preconditions and reads are `TBool`-shaped, decreases
is `TInt`. A `TODO` referencing this used to live in the file (now removed
because the doc gives no anchor for it).

**Suggested fix.** Decide explicitly:
- *Either* add three rules — T-Pre (preconditions are `TBool`), T-Dec
  (`decreases : TInt`), T-Reads (the determinism reads expression has the
  right shape) — alongside T-FuncProc, *and* enforce them in `checkProcedure`,
- *or* add a roadmap item naming them as deferred so the omission is intentional.

## 6. T-AsType has no premise relating `target` and `τ`

**Doc — `LaurelDoc.lean:370-372, 382`.** "`AsType` synthesises its declared
target type (the cast itself is not soundness-checked at compile time)." The
rule literally types `target : _` and concludes `AsType target τ : τ`.

**Implementation.** Matches the rule literally (`TypeCheck.lean:321-323`):
recurse on `target`, return `τ`.

**Reader expectation.** A reader is likely to expect *some* compile-time check
preventing `(s : string) as Dog` — that is, a static-rejection clause for
"obviously incompatible" casts (e.g. between primitive types and user-defined
types). The doc's parenthetical "not soundness-checked" is easy to read as
"checked enough to reject `string as Dog`."

**Suggested fix.** Either narrow the prose to make the lack of any
target/`τ` relation explicit:

> `AsType` deliberately performs *no* relation check between `target`'s type
> and `τ`. `(s : string) as Dog` is accepted at compile time and the
> verifier discharges (or fails to discharge) the cast at proof time.

…or add a coarse pre-cast filter as a new rule (e.g. reject the cast when
`target`'s type and `τ` are both primitive but unequal).

---

## Reading order

These six items are listed roughly in decreasing order of "how likely a future
maintainer is to be tripped up by the discrepancy when extending the type
checker". Items 1, 2, and 3 directly contradict the implementation; items 4–6
are silences in the spec that the implementation has had to fill in unilaterally.
