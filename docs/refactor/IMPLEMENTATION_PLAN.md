# Implementation Plan: Python → Laurel

## Current Status

- **Translation:** Rewritten. Clean, recursive unpackTargets, single translateCall entry.
- **Elaboration:** Rewritten. Unified effectfulCall, HOAS, heap parameter threading.
- **Non-heap tests:** All pass (3 fixed: function_def_calls, multi_function, precondition_verification)
- **Heap tests:** 16 regressions. Elaboration has heap machinery but effect inference is wrong.
- **Root cause:** Resolution pre-computes EffectType (guessing). Elaboration should INFER effects.

## The Problem

Resolution guesses which procs are stateful by looking for `self.field` access and
`raise` statements. This is incomplete (misses transitive statefulness) and architecturally
wrong. Effects are an INFERENCE problem that belongs in elaboration.

## The Fix: Effect Inference in Dependency Order

Per the updated architecture, elaboration infers effects by processing procedures
in dependency order. No EffectType in Resolution. Elaboration discovers effects
bottom-up.

### Step 1: Remove EffectType from Resolution's role in elaboration

- `FuncSig` keeps `returnType : HighType` (needed for coercion checks)
- Remove `detectEffectType`, `detectErrorOutput`, `touchesHeap` from NameResolution
- Or: keep EffectType in Resolution as a HINT for Translation's calling convention,
  but elaboration ignores it and infers its own effect information

**Decision:** Keep EffectType in FuncSig for now (Translation uses it for the
`maybe_except` variable protocol). But elaboration does NOT read it. Elaboration
infers effects independently.

### Step 2: Build call graph in fullElaborate

For each procedure in the program, collect its callees (all `StaticCall` names
in its body). This gives us the call graph.

```lean
def buildCallGraph (procs : List Procedure) : Std.HashMap String (List String)
```

### Step 3: Topological sort

Process leaves first (procs that call no other user proc), then their callers.
For SCCs (mutual recursion), treat the whole group as one unit and conservatively
mark all as stateful if any member is.

```lean
def topoSort (graph : Std.HashMap String (List String)) : List (List String)
-- Returns SCCs in reverse topological order (leaves first)
```

### Step 4: Elaborate in dependency order with effect map

```lean
structure ElabResult where
  fgl : FGLProducer
  isStateful : Bool      -- did this proc's body touch heap?
  hasError : Bool        -- did this proc's body produce errors?

def fullElaborate (typeEnv : TypeEnv) (program : Laurel.Program) : Except String Laurel.Program := do
  let callGraph := buildCallGraph program.staticProcedures
  let order := topoSort callGraph
  let mut effectMap : Std.HashMap String ElabResult := {}
  for scc in order do
    for procName in scc do
      -- Elaborate proc, passing effectMap so it knows callees' effects
      let result := elaborateProc procName effectMap typeEnv program
      effectMap := effectMap.insert procName result
  -- Assemble final program with correct signatures
  ...
```

### Step 5: During elaboration, infer effects from the walk

When elaborating a proc's body:
- See `.New` → this proc is stateful. Introduce heap, thread it.
- See `.FieldSelect` → this proc is stateful.
- See `StaticCall f` where `effectMap[f].isStateful` → this proc is stateful.
- See `StaticCall f` where `effectMap[f].hasError` → thread error for this call.

The first time a stateful operation is encountered in a proc body, introduce
`$heap` as a local variable (or parameter if the proc itself needs to be stateful).

### Step 6: Signature rewriting

After elaboration, procs discovered to be stateful get `$heap_in` input and
`$heap` output added. Their callers (elaborated later in topo order) already
know this from the effect map.

---

## Validation

After implementation:
- All non-heap tests continue to pass
- Heap tests should pass (Core sees correct heap-parameterized output)
- No boolean blindness, no EffectType guessing in Resolution
- Effect inference is bottom-up, dependency-ordered, architecturally clean

## Test Categories

| Category | Count | Expected outcome |
|----------|-------|-----------------|
| Non-heap (arithmetic, control flow, etc.) | ~38 | PASS (already passing) |
| Class/heap (class_decl, field_init, etc.) | ~12 | PASS after effect inference |
| External (procedure_in_assert, power) | ~3 | PASS if user funcs resolved |
| Remaining (loops nested tuple) | ~1 | PASS after type fixes |
