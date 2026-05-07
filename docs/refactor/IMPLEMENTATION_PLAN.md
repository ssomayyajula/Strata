# Implementation Plan: Remove EffectType, Implement On-Demand Grade Discovery

## Threat

If any commit violates the architecture, doesn't build, or regresses: delete everything.
No `git add -A`. No `git add .`. Only named files.

## Overview

Remove `EffectType` from Resolution. The elaborator discovers grades on-demand
by elaborating callee bodies. Resolution provides only: name, params, defaults,
returnType, hasKwargs.

## Step 1: Change FuncSig (NameResolution.lean)

**Remove:**
```lean
inductive EffectType where
  | pure (ty : HighType)
  | error (resultTy : HighType) (errTy : HighType)
  | stateful (resultTy : HighType)
  | statefulError (resultTy : HighType) (errTy : HighType)

def EffectType.resultType : EffectType → HighType
```

**Change FuncSig:**
```lean
-- Before:
structure FuncSig where
  name : String
  params : List (String × HighType)
  defaults : List (Option StmtExprMd)
  effectType : EffectType
  hasKwargs : Bool

-- After:
structure FuncSig where
  name : String
  params : List (String × HighType)
  defaults : List (Option StmtExprMd)
  returnType : HighType
  hasKwargs : Bool
```

**Remove:** `detectEffectType`, `touchesHeap`, `detectErrorOutput`, all propagation
code in `buildTypeEnv` (the loop that marks functions stateful).

**Update:** `resolveFunctionDef` and `resolveClassDef` to use `returnType` directly.

**Update prelude signatures:** Replace `effectType := .pure (.TCore "Any")` with
`returnType := .TCore "Any"` for all entries in `preludeSignatures`.

**Update `withRuntimeProgram`:** Replace `effectType := EffectType.pure retTy` with
`returnType := retTy`.

## Step 2: Update Translation.lean

**One change:** Line 569:
```lean
-- Before:
| some (.function sig) => pure sig.effectType.resultType
-- After:
| some (.function sig) => pure sig.returnType
```

And any other `sig.effectType.resultType` → `sig.returnType`.

## Step 3: Update Elaborate.lean

**Remove:** All `match s.effectType with` dispatching.

**Add to ElabState:**
```lean
structure ElabState where
  freshCounter : Nat := 0
  heapVar : Option String := none
  gradeOf : Std.HashMap String Grade := {}   -- discovered callee grades
  program : Laurel.Program                    -- for on-demand body lookup
```

Wait — the architecture says grade is part of the procedure's TYPE, stored
alongside its type info. So `gradeOf` should be in ElabState. And `program`
is needed to find callee bodies for on-demand elaboration.

**Add `discoverCalleeGrade`:**
```lean
def discoverCalleeGrade (callee : String) : ElabM Grade := do
  -- Check if already discovered
  match (← get).gradeOf[callee]? with
  | some g => pure g
  | none =>
    -- Find body in program
    let proc := (← get).program.staticProcedures.find? (·.name.text == callee)
    match proc with
    | some p => match p.body with
      | .Transparent bodyExpr =>
        -- Try grades smallest to largest
        let grade := tryGrades bodyExpr [.pure, .err, .heap, .heapErr]
        modify fun s => { s with gradeOf := s.gradeOf.insert callee grade }
        pure grade
      | _ => pure .pure
    | none => pure .pure  -- unknown callee (prelude) treated as pure
```

**Replace effectType dispatch in synthProducer:**
```lean
-- Before:
match s.effectType with
| .pure _ => ...
| .error resultTy _ => mkErrorCall ...
| .stateful resultTy => mkHeapCall ...
| .statefulError resultTy _ => mkHeapErrorCall ...

-- After:
let grade ← discoverCalleeGrade callee.text
match grade with
| .pure => ... (value call, use synthValue)
| .err => mkErrorCall callee.text checkedArgs s.returnType fun rv => cont
| .heap => mkHeapCall callee.text checkedArgs s.returnType fun rv => cont
| .heapErr => mkHeapErrorCall callee.text checkedArgs s.returnType fun rv => cont
```

**Update fullElaborate:**
- Initialize `ElabState` with `program` field
- After elaborating all procs, read `gradeOf` to determine which need heap params
- Rewrite signatures for heap-grade procs

## Step 4: Build + Test

- `lake build` must pass
- Run `diff_test.sh compare pyAnalyzeV2`
- Must not regress from current 19 passing
- Heap tests may improve (on-demand discovery finds correct grades)

## Step 5: Commit

Only commit if build passes and tests don't regress. Commit only named files:
```
git add Strata/Languages/Python/NameResolution.lean
git add Strata/Languages/Python/Translation.lean
git add Strata/Languages/FineGrainLaurel/Elaborate.lean
```

## Execution Order

1. NameResolution: remove EffectType, add returnType, fix all usages
2. Translation: sig.returnType
3. Elaborate: add gradeOf + program to state, discoverCalleeGrade, remove effectType dispatch
4. Build
5. Test
6. Commit (named files only)
