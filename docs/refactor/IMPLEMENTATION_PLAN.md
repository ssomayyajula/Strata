# Implementation Plan

## Key Insight: ElabResult is dependent on Grade

```lean
def ElabResult (g : Grade) : Type :=
  match g with
  | .pure    => FGLProducer
  | .err     => FGLProducer
  | .heap    => FGLValue → ElabM FGLProducer
  | .heapErr => FGLValue → ElabM FGLProducer
```

- synthProducer returns: `(g : Grade) × LowType × ElabResult g`
- checkProducer takes grade as input, returns: `ElabResult g`
- Errors: output-only (effectfulCall with [rv, ev] built at synth time)
- Heap: closure waiting for heap value (applied at sequencing point)

## The Algorithm

1. Entry: `checkProducer body returnType grade` where grade is discovered on-demand
2. On-demand callee grade: at call site, elaborate callee body trying grades, store in Γ
3. Total: bidirectional algorithm never fails on well-typed Laurel
4. Failure ONLY during on-demand callee grade discovery (trying grades)
5. ElabState = { freshCounter } only
6. Return type flows DOWN via check mode (parameter, not state)
7. No heap parameter threading — heap lives inside closures

## The To-Rule (Sequencing)

```
M to x. N ⇐ A & e:
  1. Synth M → (d, B, result_d : ElabResult d)
  2. Apply result_d:
     - if d ∈ {pure, err}: result_d IS the FGLProducer (use directly)
     - if d ∈ {heap, heapErr}: result_d is closure, apply to current heap
  3. Bind the produced result in HOAS
  4. Compute d \ e (residual)
  5. Check N ⇐ A & (d \ e), passing new heap if d produced one
```

## Monad

```lean
abbrev ElabM := ReaderT TypeEnv (StateT ElabState Option)
-- Option for on-demand callee grade discovery (tryGrades can fail)
-- Main elaboration is total on well-typed input (never hits none)

structure ElabState where
  freshCounter : Nat := 0
```

## Synth vs Check Dispatch

SYNTH (produce type + grade + ElabResult):
- effectful call (grade from callee)
- .New (grade = heap)
- assign (grade = pure)
- assert/assume (grade = pure)
- while (grade from body)

CHECK (receive type + grade, return ElabResult):
- if/else (both branches check at same grade)
- var-bind (body checks at same grade)
- M to x. N (M synths, N checks at residual grade)
- return (check value against type, grade admissible)
- subsumption fallback (synth, then d ≤ e admissible)

## Implementation Order

1. Grade + ConventionWitness + residual
2. Types + FGL terms
3. ElabState + ElabM (Option-based)
4. HOAS (mkEffectfulCall, mkVarDecl)
5. Subsumption table
6. ElabResult type family
7. synthValue / checkValue
8. synthProducer (returns Sigma grade + ElabResult)
9. checkProducer (takes grade, returns ElabResult)
10. elaborateBlock (sequences with residual, applies closures)
11. On-demand callee grade discovery
12. fullElaborate + projection
13. Build + test
