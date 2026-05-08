# Status After Heap Threading Implementation

## Done
- Unified `effectfulCall` FGL constructor (one binding form for full monad)
- `mkEffectfulCall` HOAS constructor (extends Γ for all outputs)
- Projection handles `effectfulCall` → multi-output assign
- Resolution detects stateful methods (self.field → `.stateful`)
- fullElaborate adds $heap params for stateful procs
- .New emits allocation sequence when heapVar is set
- .FieldSelect emits readField when heapVar is set
- .stateful calls thread heap through

## Remaining Issues (heap tests still fail)

### 1. `_unknown` free variable in class tests
The two-phase class construction (New + __init__) produces:
- `tmp := New "ClassName"` → elaborated as MkComposite when heapVar set
- `target := tmp` → but tmp flows through elaboration as `_unknown`

Root cause: Translation emits `Block [tmpDecl, initCall, tmpRef]` for class
constructors. Elaboration's `synthValue` hits the Block case → falls to `| _ =>`
→ returns `_unknown`. Blocks aren't values.

Fix: The Block from class construction should go through `synthProducer`, not
`synthValue`. The assign case needs to handle block-valued RHS.

### 2. __init__ not detected as stateful
`__init__` bodies often don't access `self.field` directly (the CALLER does
`self.field := ...` or the allocation is at the call site). But __init__ receives
`self` and the caller expects heap threading.

Fix: All `__init__` methods should be marked `.stateful` unconditionally (they
always receive a freshly-allocated Composite).

### 3. Transitivity not implemented
If `main()` calls `Foo()` (class construction), main touches heap transitively.
But Resolution marks `main` as `.pure` because main's body doesn't directly
access `self.field`.

Fix: Resolution needs transitive propagation through the call graph, OR
the elaborator needs to propagate statefulness when it sees a call to a
stateful proc from a non-stateful context.
