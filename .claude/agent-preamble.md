# Standard Agent Preamble

You are implementing part of a formally-grounded compiler pipeline. Your code must
be mechanically derived from the ARCHITECTURE.md and IMPLEMENTATION_PLAN.md. There 
is no room for creativity, heuristics, or shortcuts.

**EVERY message you write must reference the ARCHITECTURE.md and IMPLEMENTATION_PLAN.md.**
If you're not citing them, you're not following them. Cite the specific section that
justifies what you're doing.

## YOUR GOD

Two documents. Two questions. You cannot work without both.

- **ARCHITECTURE.md** answers WHAT and WHY (why is proof-relevant what).
  What are the types? What are the relations? What does each pass produce?
  Why this structure? Why this coercion? Why this boundary?

- **IMPLEMENTATION_PLAN.md** answers HOW.
  How do we get there from here? How is the code organized? How do we validate?

Paths:
1. `/Users/somayyas/workspace/StrataPythonBuildBackendWS/src/Strata/docs/refactor/ARCHITECTURE.md`
2. `/Users/somayyas/workspace/StrataPythonBuildBackendWS/src/Strata/docs/refactor/IMPLEMENTATION_PLAN.md`

Read BOTH completely before writing any code. Every line you write must trace back
to a specific section of these documents. If it doesn't, you're making something up.
If you can't answer "what/why does the ARCHITECTURE say?" AND "how does the PLAN say
to do it?" for what you're about to write — STOP.

## THERE IS ONLY ONE WAY TO DO IT

The types determine the implementation. The architecture determines the types.
You do NOT make choices. You do NOT ask questions. You TRANSCRIBE the spec into code.

If you find yourself:
- Choosing between two approaches → you haven't read the spec carefully enough
- Adding a "peephole optimization" → you're patching over a wrong implementation
- Writing an if-statement on a type string → you're doing boolean blindness
- Asking "should I use X or Y?" → the type already tells you which one

The FGL types enforce correctness:
- Procedure has error effect (hasErrorOutput) → MUST use `prodCallWithError`. No choice.
- Procedure has no error effect → MUST use `prodCall`. No choice.
- Expression is a value → MUST be `FGL.Value`. Can't put a Producer there.
- Expression is effectful → MUST be `FGL.Producer`. Can't pretend it's a Value.

## ABSOLUTE RULES

1. **MECHANICALLY DERIVED from the spec.** You are transcribing, not problem-solving.

2. **No quick fixes.** The answer is in the architecture. Not in "what makes the
   test pass." Not in "what the old pipeline does." Not in a peephole optimization.

3. **No if-statements on types.** Pattern match on NameInfo/FGL constructors.
   Boolean blindness = immediate failure.

4. **FP best practices.** Catamorphisms (one case per constructor). No mutation
   outside the monad. No post-hoc tree rewrites. No filtering heuristics.

5. **No coercions in Translation.** `from_int`, `from_str`, `from_bool`,
   `Any_to_bool` in Translation.lean = VIOLATION. These belong in Elaboration.

6. **Elaboration produces FGL types.** Not StmtExprMd. The types enforce polarity.

7. **Projection is let-floating.** splitProducer(M) → (prefix stmts, terminal expr).
   No heuristics. No filtering. Pure monad associativity (Peyton Jones et al. 1996).

8. **Subtyping vs Narrowing.** Two separate relations, determined by the types:
   - A <: B (subtyping) → value-level upcast (infallible). `int <: Any` via valFromInt.
   - A ▷ B (narrowing) → producer-level downcast (fallible). `Any ▷ bool` via Any_to_bool.
   The type tells you which. You don't decide.

9. **Error effect = prodCallWithError.** If `FuncSig.hasErrorOutput = true`, the
   call MUST be `prodCallWithError`. Not `prodCall`. Not a choice. The type says so.

10. **COMMIT after every successful `lake build`.** Never commit broken builds.

11. **If stuck: STOP.** Write `-- ARCHITECTURE GAP: <description>` and report.
    Do NOT invent a workaround. Do NOT fall back to the old pipeline.
    Do NOT add peephole optimizations. Do NOT "make the handler smarter."

## PROCESS: PLAN BEFORE CODE

Before writing ANY code change:
1. Write a PLAN: what you will change, which file/lines, why (cite architecture section)
2. The plan must be specific enough that a reviewer can verify it against the architecture
   WITHOUT seeing the code
3. Only after the plan is clear, execute it
4. If your plan requires heuristics, peephole optimizations, or "smart" handlers — your
   plan is WRONG. Go back to the architecture.

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
