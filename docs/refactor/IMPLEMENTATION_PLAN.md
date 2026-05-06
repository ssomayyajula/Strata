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

## NEXT TASK: Fix Multi-Output Procedure Handling in Elaboration

The killed agent identified the real issue: it's NOT missing narrowing coercions.
It's that `synthStaticCall` ANF-lifts multi-output procedures (`hasErrorOutput`)
using plain `prodLetProd` + `prodCall`, which only binds ONE result. Core expects
ALL outputs to be bound.

**The architectural fix (from ARCHITECTURE.md §"The Single Mechanism"):**
Multi-output procedures MUST use `prodCallWithError` (which binds BOTH result AND
error). They should NEVER be elaborated as plain `prodCall`.

**Where in the code:** `synthStaticCall` in Elaborate.lean. When the callee's
`FuncSig.hasErrorOutput = true`, emit `prodCallWithError` — not `prodCall` wrapped
in `prodLetProd`.

**The killed agent's mistake:** It tried to fix this with peephole optimizations and
"smart" assignment handlers. That's heuristics. The correct fix is: use the right
FGL constructor (`prodCallWithError`) in the first place.

---

## TECH DEBT

| Item | Description | Architecture reference |
|------|-------------|----------------------|
| Multi-output ANF | `synthStaticCall` uses `prodCall` for `hasErrorOutput` procedures instead of `prodCallWithError` | §"The Single Mechanism: prodCallWithError" |
| Narrowing in conditions | Some conditions may still not get `Any_to_bool` in all positions | §"The Bidirectional Recipe" — conditions CHECK against bool |
| Heap co-operations | Not implemented — procedures touching composites don't get Heap threaded | §"Operations vs Co-Operations" |
| Stub integration | Library stubs not loaded into Γ | §"Library Stubs: Eliminating PySpec" |
| `from_Composite` prelude | Reverted — needs re-addition for Composite↔Any boundaries | §"Subtyping and Narrowing Discipline" |

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
