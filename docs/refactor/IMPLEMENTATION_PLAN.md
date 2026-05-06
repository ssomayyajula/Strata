# Implementation Plan (synced with ARCHITECTURE.md)

**Last updated:** After commit 17737b0d9 (V2 skips old lowering passes)

**Current state:** V2 now runs WITHOUT old lowering passes. ALL tests fail.
This is architecturally correct — it exposes every gap in our elaboration.

---

## STATUS

| Phase | Status | Commit |
|-------|--------|--------|
| A: Generate FGL types | ✅ Done | 969a6680c |
| B: Rewrite Elaboration with FGL types | ✅ Done | 2d9455f44 |
| C: Strip Translation coercions + enable elaboration | ✅ Done | f77e021a2 |
| Elaboration gap fixes (local types, loops) | ✅ Done | 3864cbbf5 |
| Projection flattening (let-floating) | ✅ Done | 88bb9af08 |
| Short-circuit desugaring (architecture-specified) | ✅ Done | b896ec248 |
| prodCallWithError for hasErrorOutput | ✅ Done | a0ff15674 |
| E: Remove old lowering passes from V2 | ✅ Done | 17737b0d9 |
| **F: Core type infrastructure** | ❌ NEXT | — |
| G: Remaining elaboration gaps | ❌ Blocked by F | — |
| H: Stub integration | ❌ Not started | — |

---

## WHAT JUST HAPPENED

Removing the old lowering passes revealed: our elaboration produces Laurel that
Core cannot translate. The error:

```
Type (arrow Composite (arrow int string)) is not an instance of a previously registered type!
```

Core's type system has a REGISTRY of known types. The old `typeHierarchyTransform`
and `heapParameterization` passes registered these types (Composite, Box, Field, Heap,
TypeTag, etc.) as part of their transformation. Our elaboration doesn't register them.

Additionally: "BUG: metadata without a filerange" — projection emits nodes with
empty metadata, violating the interaction law.

---

## NEXT: Phase F — Core Type Infrastructure

### The Problem

Core's `resolve` builds a `SemanticModel` that knows all types. Core's translator
then looks up types in this model. If a type appears in a procedure signature but
isn't registered, Core rejects it.

The old passes registered types by:
1. `typeHierarchyTransform`: adds `TypeTag` datatype, `Composite` datatype with fields, `ancestorsPerType` constants
2. `heapParameterization`: adds `Box` datatype, `Field` datatype, `Heap` datatype, `readField`/`updateField`/`increment` procedures

Our elaboration Phase 2 (heap) and Phase 3 (type hierarchy) in Elaborate.lean
attempt to do this but apparently don't produce the right type registrations.

### What Needs to Happen

1. **Investigate:** What EXACTLY does Core's `resolve` need in the `Laurel.Program` to
   register Composite/Box/Field/Heap/TypeTag? Read the existing `typeHierarchyTransform`
   and `heapParameterization` to see what they ADD to the program's `types` field.

2. **Update architecture:** Add "type infrastructure generation" as a step in elaboration.
   It's not a separate pass — it's part of what elaboration produces (the datatypes that
   make the co-operations well-typed).

3. **Implement:** Make elaboration's Phase 2/3 produce the correct type declarations
   in the output `Laurel.Program.types` field.

4. **Fix metadata:** Projection must propagate metadata through `splitProducer`.
   The interaction law is non-negotiable.

### What to Study

```bash
# What does typeHierarchyTransform ADD to program.types?
grep -n "TypeTag\|Composite\|ancestors\|typeTag\|types :=" Strata/Languages/Laurel/TypeHierarchy.lean | head -20

# What does heapParameterization ADD to program.types?
grep -n "Box\|Field\|Heap\|types :=\|staticProcedures :=" Strata/Languages/Laurel/HeapParameterization.lean | head -20

# What does Core's resolve expect?
grep -n "register\|Known Types\|registered type" Strata/Languages/Core/ -r | head -10
```

---

## OPERATIONAL DISCIPLINE (unchanged)

### Rules
1. Read BOTH docs: ARCHITECTURE.md + this plan
2. Every implementation agent gets parallel review agent
3. Plan before code
4. Standard preamble (`.claude/agent-preamble.md`)
5. Commit after every successful build
6. NO heuristics, NO peephole optimizations, NO boolean blindness
7. If stuck: STOP and report

### Git State
- Branch: `ssomayyajula/python-fe-refactor`
- HEAD: `17737b0d9`
- Build: passes (500 jobs)
- Old pipeline: works (12 passed on test_arithmetic)
- V2 pipeline: ALL tests fail (expected — old passes removed, elaboration gaps exposed)

---

## THEORETICAL GROUNDING (unchanged, see ARCHITECTURE.md)

- Subtyping (A <: B): value-level, infallible
- Narrowing (A ▷ B): producer-level, fallible  
- Projection: let-floating (bind reassociation)
- FGCBV as CBPV fragment (only computation type is ↑A)
- Operations vs co-operations (Bauer 2018)
- Bidirectional recipe: annotations drive checking (Dunfield & Krishnaswami + Lakhani & Pfenning)
