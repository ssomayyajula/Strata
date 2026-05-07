# Implementation Plan

## Threat

If any commit violates the architecture, doesn't build, or regresses: delete everything.

## Architecture Summary

- Entry: `checkProducer body returnType grade`
- Grade discovered by trying `[pure, err, heap, heapErr]` until check succeeds
- Callee grades stored in Γ via on-demand elaboration
- `ElabState` = `{ freshCounter : Nat }`
- Heap flows as `Option FGLValue` parameter
- Producer subsumption: type coercion `c` + convention witness `conv`, applied via HOAS
- Sequencing: `M to x. N ⇐ A & e` → synth M → `d`, check N → `d \ e`
- All binding via HOAS (`mkEffectfulCall`, `mkVarDecl`)

## Data Types

```
Grade: pure | err | heap | heapErr
ConventionWitness: pureCall | errorCall | heapCall | heapErrorCall
LowType: TInt | TBool | TString | TFloat64 | TVoid | TCore name
FGLValue: litInt | litBool | litString | var | fromInt | fromStr | ... | staticCall
FGLProducer: returnValue | assign | varDecl | ifThenElse | whileLoop | assert |
             assume | effectfulCall | exit | labeledBlock | seq | unit
ElabState: { freshCounter : Nat }
ElabM: ReaderT TypeEnv (StateT ElabState Id)
```

## Functions

```
synthValue (heap) (expr) : ElabM (FGLValue × LowType)
checkValue (heap) (expr) (expected : HighType) : ElabM FGLValue
checkArgs (heap) (args) (params) : ElabM (List FGLValue)

synthProducer (heap) (expr) : ElabM (FGLProducer × LowType × Grade)
checkProducer (heap) (expr) (expected : LowType) (grade : Grade) : ElabM FGLProducer

elaborateBlock (heap) (stmts) (expected : LowType) (grade : Grade) : ElabM FGLProducer

lookupCalleeGrade (callee : String) : ElabM Grade
  -- On-demand: if not in Γ, elaborate callee body trying grades, store in Γ
```

## Entry Point: fullElaborate

```
for proc in program.staticProcedures:
  let grade := tryGrades proc.body [pure, err, heap, heapErr]
  let heap := if grade ∈ {heap, heapErr} then some (.var "$heap") else none
  let extEnv := Γ + proc params + (if heap: $heap_in, $heap)
  let fgl := checkProducer heap body returnType grade  (under extEnv)
  if heap: prepend $heap := $heap_in; add $heap_in/$heap params
  project fgl → Laurel
```

## tryGrades

```
tryGrades body [g₁, g₂, ...]:
  for g in grades:
    if checkProducer succeeds at grade g:
      return g
  return heapErr  -- top, always succeeds
```

"Succeeds" means: no residual failure (all `d \ e` computations return `some`).
Since `ElabM` is `Id`-based (no `Except`), failure = encountering an operation
whose grade exceeds the budget. Need to make check FALLIBLE for this.

## Making Check Fallible

Change monad: `ElabM := ReaderT TypeEnv (StateT ElabState (Option))` or similar.
Then when `Grade.residual d e = none`, the check fails (returns `none`).
`tryGrades` catches the failure and tries the next grade.

Alternative: keep `ElabM` as `Id`, add `canCheck` that returns `Bool` by scanning
the body. Simpler but less principled.

Decision: use `Option` monad. Check fails cleanly when grade is insufficient.

## Revised Monad

```
abbrev ElabM := ReaderT TypeEnv (StateT ElabState Option)
```

This means all elaboration functions return `Option`. `tryGrades` catches `none`.

## Order of Implementation

1. Grade + ConventionWitness + subgrade + residual (done in previous step)
2. LowType + eraseType + FGL terms
3. ElabState + ElabM (with Option)
4. HOAS constructors (mkEffectfulCall, mkVarDecl, applyConvention)
5. Subsumption table
6. synthValue / checkValue / checkArgs
7. synthProducer (handles .New, .FieldSelect, .StaticCall, etc.)
8. checkProducer (if, var-bind, to-rule with residual, return, subsumption fallback)
9. elaborateBlock (sequencing with grade accumulation via residual)
10. lookupCalleeGrade (on-demand elaboration, stores in Γ)
11. fullElaborate (tryGrades, heap params, projection, heapConstants)
12. Projection
13. Build + test
