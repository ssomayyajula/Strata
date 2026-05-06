# Standard Agent Preamble

You are implementing part of a formally-grounded compiler pipeline. Your code must
be mechanically derived from the specification. There is no room for creativity,
heuristics, or shortcuts.

## YOUR GOD

These two documents are your specification. There is no other specification:
1. `/Users/somayyas/workspace/StrataPythonBuildBackendWS/src/Strata/docs/refactor/ARCHITECTURE.md`
2. `/Users/somayyas/workspace/StrataPythonBuildBackendWS/src/Strata/docs/refactor/IMPLEMENTATION_PLAN.md`

Read BOTH completely before writing any code. Every line you write must trace back
to a specific section of these documents. If it doesn't, you're making something up.

## ABSOLUTE RULES

1. **The implementation is MECHANICALLY DERIVED from the spec.** You are transcribing,
   not problem-solving. If you find yourself making a choice, the spec is either
   incomplete (STOP and report) or you haven't read it carefully enough.

2. **No quick fixes.** If something doesn't work, the answer is in the architecture.
   Not in "what makes the test pass." Not in "what the old pipeline does."

3. **No if-statements on types.** Pattern match on the NameInfo/FGL constructors.
   Boolean blindness = immediate failure. If you write `if isX then ... else ...`
   you're wrong.

4. **FP best practices.** Catamorphisms (one case per constructor). No mutation
   outside the monad. No post-hoc tree rewrites. No filtering heuristics.

5. **No coercions in Translation.** If you see `from_int`, `from_str`, `from_bool`,
   `Any_to_bool` in Translation.lean, that's a violation. These belong in Elaboration.

6. **Elaboration produces FGL types.** Not StmtExprMd. If elaboration returns
   Laurel nodes directly, that's a violation.

7. **Projection is let-floating.** splitProducer(M) → (prefix stmts, terminal expr).
   No heuristics. No filtering. Pure monad associativity.

8. **Subtyping vs Narrowing.** Two separate relations:
   - A <: B → value-level upcast (infallible). `int <: Any` via valFromInt.
   - A ▷ B → producer-level downcast (fallible). `Any ▷ bool` via Any_to_bool.
   Never confuse them.

9. **COMMIT after every successful `lake build`.** Never commit broken builds.
   Format: `[refactor] <what> (<test result>)`

10. **If stuck: STOP.** Write `-- ARCHITECTURE GAP: <description>` and report.
    Do NOT invent a workaround. Do NOT fall back to the old pipeline.

## COMPLIANCE CHECKS (run before committing)

```bash
grep -n "from_int\|from_str\|from_bool\|Any_to_bool" Translation.lean | grep -v "^.*--"  # VIOLATION
grep -n "SKIP\|skip\|disabled" PySpecPipeline.lean                                         # VIOLATION
grep -n "isPrelude\|isUserFunc" Elaborate.lean                                             # VIOLATION
```

## VERIFICATION

```bash
lake build
PATH="/Users/somayyas/bin:$PATH" bash StrataTest/Languages/Python/diff_test.sh compare pyAnalyzeV2 2>&1 | grep "REGR\|BLOCKED"
PATH="/Users/somayyas/bin:$PATH" .lake/build/bin/strata pyAnalyzeLaurel StrataTest/Languages/Python/tests/test_arithmetic.python.st.ion 2>&1 | tail -3
```
