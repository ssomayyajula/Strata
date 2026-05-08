# Elaborator Rewrite Plan

## What changes

1. Remove `discoveryMode` from ElabState
2. Remove grade check from `synthValue` (values have no grades)
3. `synthExpr` returns `SynthResult` by looking up `procGrades` (pure read)
4. `discoverGrades` is a standalone fixpoint function
5. `fullElaborate` = discoverGrades + elaborate each body
6. `checkArgsK` is the default arg handler (uses synthExpr, applies to-rule)

## What stays the same

- FGLValue, FGLProducer types
- Grade monoid (leq, join, residual)
- LowType, eraseType, liftType
- Subsumption table
- Smart constructors (mkEffectfulCall, mkErrorCall, mkHeapCall, mkHeapErrorCall, mkVarDecl)
- HOAS (freshVar, extendEnv)
- Box protocol
- Projection
- Pipeline wiring (fullElaborate signature, type infrastructure generation)

## Implementation order

1. Write `discoverGrades` (fixpoint iteration, standalone)
2. Rewrite `synthValue` (remove grade check — values don't have grades)
3. Rewrite `synthExpr` (lookup procGrades, no body evaluation)
4. Rewrite `checkArgsK` to use synthExpr (the ONLY arg handler)
5. Remove old `checkArgs` (subsumed by checkArgsK)
6. Remove `discoverGrade` and `tryGrades` from mutual block
7. Remove `discoveryMode` from ElabState
8. Update `fullElaborate` to call discoverGrades then elaborate
9. Build + test
