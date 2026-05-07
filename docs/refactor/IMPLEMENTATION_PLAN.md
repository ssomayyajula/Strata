# Implementation Plan: Python → Laurel

## Status: 36/54 non-regressing (18 regressions)

---

## Next: HOAS Smart Constructors for Binding Hygiene

The current code has dangling variable references — `callWithError` introduces
`rv`/`ev` but subsequent code can reference them without Γ extension. This is
unsound. Fix: HOAS smart constructors.

### Task 1: Implement HOAS smart constructors

```lean
-- freshVar is PRIVATE to this module
private def freshVar (pfx : String) : ElabM String := ...

-- The ONLY way to create binding forms:
def mkCallWithError (callee : String) (args : List FGLValue) (resultTy errTy : LowType)
    (body : FGLValue → FGLValue → ElabM FGLProducer) : ElabM FGLProducer

def mkVarDecl (name : String) (ty : LowType) (init : Option FGLValue)
    (body : FGLValue → ElabM FGLProducer) : ElabM FGLProducer

def mkLetProd (ty : LowType) (prod : FGLProducer)
    (body : FGLValue → ElabM FGLProducer) : ElabM FGLProducer
```

Each extends Γ before calling the closure. `lake build`.

### Task 2: Rewrite elaboration to use HOAS constructors

- Assign effectful case: use `mkCallWithError` with closure for rest of block
- LocalVariable case: use `mkVarDecl` with closure for continuation
- `elaborateBlock`: threading uses closures, not `sequenceProducers`
- No direct `freshVar` calls in elaboration code
- `lake build`

### Task 3: End-to-end validation

Target: fix procedure_in_assert, method_param_reassign (dangling var bugs).
Run diff_test.sh. Target: 38+/54.

---

## Remaining Regressions After HOAS Fix

| Category | Count | Status |
|----------|-------|--------|
| Class/heap | 7 | Needs full heap implementation |
| PySpec stubs | 5 | Out of scope |
| PySpec arg mismatch | 3 | Out of scope |
| Pipeline (Any_get) | 1 | filterPrelude issue |
| Type errors (post-HOAS) | 2 | May be fixed by HOAS, otherwise diagnose |
