# Implementation Plan (synced with ARCHITECTURE.md)

**Last updated:** After commit 88bb9af08 (principled projection flattening)

**Current state:** 19/54 tests pass, 6 genuine regressions (pass → internal_error)

---

## STATUS

| Phase | Status | Commit |
|-------|--------|--------|
| A: Generate FGL types | ✅ Done | 969a6680c |
| B: Rewrite Elaboration with FGL types | ✅ Done | 2d9455f44 |
| C: Strip Translation coercions + enable elaboration | ✅ Done | f77e021a2 |
| Elaboration gap fixes (local types, loops) | ✅ Done | 3864cbbf5 |
| Projection flattening (let-floating) | ✅ Done | 88bb9af08 |
| Remaining coercion gaps | 🔄 Next | — |
| Stub integration | ❌ Not started | — |
| Heap co-operations | ❌ Not started | — |

---

## REMAINING REGRESSIONS (6 tests)

All are "Type checking error: Impossible to unify X with Y" — missing narrowing coercions.

| Test | Error | Likely cause |
|------|-------|-------------|
| test_boolean_logic | Any vs bool | Narrowing not inserted for assert/condition |
| test_break_continue | Any vs bool | Same (while loop condition) |
| test_method_param_reassign | ? | Coercion gap at method boundary |
| test_optional_param_default | ? | Coercion gap at call with defaults |
| test_procedure_in_assert | ? | Coercion gap in assert condition |
| test_try_except_scoping | ? | Coercion gap in exception handling |

**Root cause:** The bidirectional walk's `checkProducer`/`checkValue` doesn't insert
narrowing coercions (`Any_to_bool`, `Any..as_int!`) in all required positions.

Per the ARCHITECTURE.md subtyping/narrowing discipline:
- Narrowing (A ▷ B): `Any ▷ bool` via `Any_to_bool` — value→producer, fallible
- Fires when CHECK finds `synth(e) = Any` and `expected = bool`

Per the bidirectional recipe (ARCHITECTURE.md §"The Bidirectional Recipe"):
- `assert expr`: CHECK expr against bool
- `while cond body`: CHECK cond against bool
- `if cond then/else`: CHECK cond against bool
- Function call args: CHECK each arg against param type from Γ

---

## NEXT TASK: Fix Narrowing Coercion Gaps

The elaboration walk must ensure that EVERY position requiring `bool` gets
`Any_to_bool` inserted when the expression synths as `Any`. Check:

1. `synthProducer` for `Assert` — does it `checkProducer cond .TBool`?
2. `synthProducer` for `While` — does it check the condition against bool?
3. `synthProducer` for `IfThenElse` — does it check the condition against bool?
4. `synthStaticCall` for function args — does it `checkValue arg paramType`?

If any of these are missing the check or the check doesn't trigger narrowing
correctly, that's the bug.

---

## OPERATIONAL DISCIPLINE

### Rules for All Agents
1. Read BOTH: `docs/refactor/ARCHITECTURE.md` AND `docs/refactor/IMPLEMENTATION_PLAN.md`
2. NO COMPROMISES. No coercions in Translation. No skipping elaboration. No boolean gates.
3. COMMIT after every successful `lake build`
4. Review agent runs in parallel
5. Kill on architecture violations

### Compliance Checks
```bash
grep -n "from_int\|from_str\|from_bool\|Any_to_bool" Translation.lean | grep -v "^.*--"  # VIOLATION
grep -n "SKIP\|skip\|disabled" PySpecPipeline.lean                                         # VIOLATION
grep -n "isPrelude\|isUserFunc" Elaborate.lean                                             # VIOLATION
```

### Git Hygiene
- Every `lake build` success → commit
- Commit format: `[refactor] <what> (<test result>)`
- Never commit broken builds

### Iterative Learning
- When an agent is killed: read its transcript, identify what it tried and where it failed
- Add learned constraints to next agent's prompt
- If genuine architecture gap found: escalate, don't hack

---

## THEORETICAL GROUNDING (see ARCHITECTURE.md for full details)

- **Subtyping (A <: B):** infallible, value→value. `int <: Any` via `valFromInt`.
- **Narrowing (A ▷ B):** fallible, value→producer. `Any ▷ bool` via `Any_to_bool`.
- **Projection:** let-floating (Peyton Jones et al. 1996). Bind associativity + freshness.
- **FGCBV:** Two judgments (⊢_v, ⊢_p). Function args are Values. Producers bound via `M to x. N`.
- **Bidirectional:** Introductions check, eliminations synth, subsumption at boundaries.
- **Operations vs co-operations (Bauer 2018):** Coercions/exceptions = operations (local).
  Heap = co-operation (global propagation).

---

## ARCHITECTURE COMPLIANCE CHECKLIST

Before ANY commit, verify:
- [ ] Translation has NO `from_int`/`from_str`/`from_bool`/`Any_to_bool` in code
- [ ] Elaboration is enabled (not skipped)
- [ ] No boolean gates (isPreludeFunc etc.)
- [ ] FGL types used in elaboration output (not StmtExprMd)
- [ ] Old pipeline (`pyAnalyzeLaurel`) still works
- [ ] `diff_test.sh compare pyAnalyzeV2` run, regressions counted
