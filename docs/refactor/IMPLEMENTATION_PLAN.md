# Implementation Plan: Python → Laurel

## Status: 35/54 non-regressing (19 regressions)

---

## Architectural Change: EffectType replaces hasErrorOutput

`FuncSig.hasErrorOutput: Bool` is boolean blindness. Replace with:

```lean
inductive EffectType where
  | pure (ty : HighType)
  | error (resultTy : HighType) (errTy : HighType)
  | stateful (resultTy : HighType)
  | statefulError (resultTy : HighType) (errTy : HighType)
```

Elaboration pattern-matches on `EffectType` — no boolean dispatch.
- `.pure ty` → synthValue (value-level call, stays nested)
- `.error resultTy errTy` → synthProducer (callWithError, true let)
- `.stateful resultTy` → synthProducer (heap threading)
- `.statefulError resultTy errTy` → synthProducer (both)

---

## Execution Tasks

### 1. Add EffectType to Resolution (NameResolution.lean)

- Add `EffectType` inductive
- Change `FuncSig`: remove `returnType + hasErrorOutput`, add `effectType : EffectType`
- Update `buildTypeEnv`: determine effect from function body (raise → .error, field access → .stateful)
- Update `preludeSignatures`: all prelude ops are `.pure (.TCore "Any")`
- `lake build`

### 2. Update Translation to use EffectType

- `resolveKwargs` reads `sig.effectType` for param info
- `translateFunction` determines effect for user procedures
- No boolean dispatch anywhere
- `lake build`

### 3. Update Elaboration to pattern-match on EffectType

- `synthValue` StaticCall: match `.pure ty` → value call
- `synthProducer` StaticCall: match `.error`/`.stateful`/`.statefulError` → producer
- Assign case: match RHS call's effect to determine if value or producer
- No `hasErrorOutput` anywhere
- `lake build`

### 4. Fix remaining type errors

- TVoid in Core (already fixed)
- Assign with effectful RHS (now handled by EffectType dispatch)
- test_power: NotSupportedYet issue
- test_procedure_in_assert: function type mismatch
- `lake build` + test

### 5. End-to-end validation

Target: 40+/54. Remaining will be heap (7) + PySpec (5).

---

## Remaining Regressions (19)

| Category | Count | Blocked by |
|----------|-------|-----------|
| Class/heap | 7 | Full heap implementation |
| PySpec stubs | 5 | Stub integration (out of scope) |
| TYPE_CHECK | 5 | EffectType fix (tasks 1-4) |
| PROC_NOT_FOUND | 2 | Pipeline wiring |
