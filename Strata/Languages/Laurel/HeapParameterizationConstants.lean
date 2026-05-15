/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DDM.Elab
public import Strata.DDM.AST
public import Strata.Languages.Laurel.Grammar.LaurelGrammar
public meta import Strata.Languages.Laurel.Grammar.LaurelGrammar
public import Strata.Languages.Laurel.Grammar.ConcreteToAbstractTreeTranslator

namespace Strata.Laurel

public section

/--
The heap model runtime interface. These are the types and functions that
elaboration relies on when translating field access, field write, and
heap allocation.

Types:
```
datatype Composite { MkComposite(ref: int) }
datatype Heap { MkHeap(data: Map Composite (Map Field Box), nextReference: int) }
datatype Field { ... }     (zero-arity constructors generated per class field)
datatype TypeTag { ... }   (zero-arity constructors generated per class)
datatype Box { ... }       (generated dynamically: BoxInt(intVal: int), BoxString(stringVal: string), etc.)
```

Functions (all pure, grade = pure):
```
readField     : (Heap, Composite, Field) → Box
updateField   : (Heap, Composite, Field, Box) → Heap
increment     : (Heap) → Heap
MkComposite   : (int) → Composite
MkHeap        : (Map …, int) → Heap
Heap..data!   : (Heap) → Map Composite (Map Field Box)
Heap..nextReference! : (Heap) → int
```

Datatype accessors/testers follow the DDM pattern:
```
$field.C.f       : () → Field      (zero-arity, one per class field)
C_TypeTag        : () → TypeTag    (zero-arity, one per class)
box_T            : (T) → Box       (e.g. BoxInt, BoxString, BoxComposite)
unbox_T          : (Box) → T       (e.g. Box..intVal!, Box..stringVal!)
```

Note: `Box` and `Field` constructors are generated dynamically by the
elaborator based on which field types and classes are actually used.
-/

private def laurelPreludeDDM :=
#strata
program Laurel;

// Composite: datatype with a reference (int)
datatype Composite { MkComposite(ref: int) }

datatype NotSupportedYet {}

// Heap: contains the data map and a nextReference for allocation
datatype Heap {
  MkHeap(data: Map Composite Map Field Box, nextReference: int)
}

// Read a field from the heap: readField(heap, obj, field) = Heap..data!(heap)[obj][field]
function readField(heap: Heap, obj: Composite, field: Field): Box {
  select(select(Heap..data!(heap), obj), field)
};

// Update a field in the heap
function updateField(heap: Heap, obj: Composite, field: Field, val: Box): Heap {
  MkHeap(
    update(Heap..data!(heap), obj,
      update(select(Heap..data!(heap), obj), field, val)),
    Heap..nextReference!(heap))
};

// Increment the heap allocation nextReference, returning a new heap
function increment(heap: Heap): Heap {
  MkHeap(Heap..data!(heap), Heap..nextReference!(heap) + 1)
};

#end

/-- The heap model runtime as a Laurel Program. Elaboration looks up
    these functions when translating field access, field write, and allocation.
```
readField     : (Heap, Composite, Field) → Box & pure
updateField   : (Heap, Composite, Field, Box) → Heap & pure
increment     : (Heap) → Heap & pure
MkComposite   : (int, TypeTag) → Composite & pure
Heap..nextReference! : (Heap) → int & pure
$field.C.f    : () → Field & pure   (generated per class field)
C_TypeTag     : () → TypeTag & pure (generated per class)
box_T         : (T) → Box & pure    (generated per field type used)
unbox_T       : (Box) → T & pure    (generated per field type used)
```
-/
def heapConstants : Program :=
  match Laurel.TransM.run none (Laurel.parseProgram laurelPreludeDDM) with
  | .ok program => program
  | .error e => dbg_trace s!"BUG: Laurel heap prelude parse error: {e}"; default

end -- public section

end Strata.Laurel
