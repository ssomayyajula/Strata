# Implementation Plan: Python → Laurel

Derived from ARCHITECTURE.md. Current state as of 2026-05-06.

---

## Status

**Resolution:** Done. `buildTypeEnv` produces precise types from annotations.
**Translation:** Done. Fold over AST, no coercions, precise types.
**Elaboration:** Needs rewrite to match final architecture.
**Projection:** Part of elaboration rewrite.
**Pipeline wiring:** Done (PySpecPipeline calls fullElaborate).
**End-to-end:** 0/54 tests pass (elaboration code reverted, needs clean rewrite).

---

## What We Know (from testing + diagnosis)

The old pipeline produces Laurel that Core accepts. It looks like:
```
var x: Core(Any) := <?>;
...
x := from_int(5);
prod := PMul(x, y);
assert Any_to_bool(PEq(prod, from_int(15)));
```

Properties:
- All variables typed `Any`
- Initialized with `Hole` (`<?>`)
- Coercions inline (`from_int(5)` in the assignment, not a separate variable)
- Pure calls nested (`PMul(x, y)` directly, `Any_to_bool(PEq(...))` directly)
- No intermediate variables from elaboration
- Only real bindings: user-declared vars + error-handling vars

---

## The Elaboration Algorithm (from ARCHITECTURE.md)

### Input/Output

- **Input:** Laurel program (from Translation) with HighType annotations
- **Output:** Laurel program with coercions inserted, all vars typed Any, ready for Core

### Core Concepts

1. **Two type systems:** HighType (with UserDefined) → LowType (with Composite only) via `eraseType`
2. **Unified subsume:** One function, three outcomes (refl/coerce/unrelated)
3. **Pure calls are values:** `hasErrorOutput = false` → stays nested, no binding
4. **Narrowing is value-level:** Partial function with precondition, not a producer
5. **Only true lets:** From `hasErrorOutput` procedures + user assignments/locals
6. **Projection is a cata:** Forget polarity, emit Laurel directly. All vars as Any, Hole for uninit.
7. **Γ extended at binding sites:** Parameters on entry, LocalVariable for continuation.

### The Typing Rules

**Value synthesis (atoms + pure calls):**
```
Γ ⊢_v n ⇒ int                                   (literal)
Γ ⊢_v x ⇒ Γ(x)                                  (variable lookup)
Γ ⊢_v f(v₁,...,vₙ) ⇒ returnType(f)              (pure call, f.hasErrorOutput = false)
     where each vᵢ ⇐ paramTyᵢ
```

**Value checking (subsumption — the only rule):**
```
Γ ⊢_v v ⇒ A    subsume(A, B) = coerce(c)
──────────────────────────────────────────
Γ ⊢_v c(v) ⇐ B
```

**Producer synthesis:**
```
Γ ⊢_p f(v₁,...,vₙ) ⇒ returnType(f)    (f.hasErrorOutput = true — TRUE LET)
Γ ⊢_p (new Foo) ⇒ Composite
Γ ⊢_p (x := v) ⇒ TVoid                 where v ⇐ Γ(x)
Γ ⊢_p (assert v) ⇒ TVoid               where v ⇐ bool
Γ ⊢_p (assume v) ⇒ TVoid               where v ⇐ bool
Γ ⊢_p (while v do M) ⇒ TVoid           where v ⇐ bool, M ⇐ TVoid
```

**Producer checking:**
```
Γ ⊢_p (if v then M else N) ⇐ C         where v ⇐ bool, M ⇐ C, N ⇐ C
Γ ⊢_p (var x:T := v; body) ⇐ C         where v ⇐ T, Γ,x:T ⊢_p body ⇐ C
Γ ⊢_p (M to x. N) ⇐ C                  where M ⇒ A, Γ,x:A ⊢_p N ⇐ C
Γ ⊢_p (return v) ⇐ procReturnType       where v ⇐ procReturnType
```

### The `subsume` Function

```lean
inductive CoercionResult where
  | refl
  | coerce (witness : FGLValue → FGLValue)
  | unrelated

def subsume (actual expected : LowType) : CoercionResult :=
  match actual, expected with
  | a, b => if a == b then .refl else
  -- Upcasts:
  | .TInt, .TCore "Any" => .coerce .fromInt
  | .TBool, .TCore "Any" => .coerce .fromBool
  | .TString, .TCore "Any" => .coerce .fromStr
  | .TFloat64, .TCore "Any" => .coerce .fromFloat
  | .TCore "Composite", .TCore "Any" => .coerce .fromComposite
  | .TCore "ListAny", .TCore "Any" => .coerce .fromListAny
  | .TCore "DictStrAny", .TCore "Any" => .coerce .fromDictStrAny
  | .TVoid, .TCore "Any" => .coerce (fun _ => .fromNone)
  -- Narrowing:
  | .TCore "Any", .TBool => .coerce (fun v => .staticCall "Any_to_bool" [v])
  | .TCore "Any", .TInt => .coerce (fun v => .staticCall "Any..as_int!" [v])
  | .TCore "Any", .TString => .coerce (fun v => .staticCall "Any..as_string!" [v])
  | .TCore "Any", .TFloat64 => .coerce (fun v => .staticCall "Any..as_float!" [v])
  | .TCore "Any", .TCore "Composite" => .coerce (fun v => .staticCall "Any..as_Composite!" [v])
  -- Box:
  | _, .TCore "Box" => .coerce (fun v => .staticCall "Box..Any" [upcastToAny v])
  | .TCore "Box", _ => .coerce (fun v => .staticCall "Box..AnyVal!" [v])
  -- Unrelated:
  | _, _ => .unrelated
```

### What `synthValue` Handles

Pure calls and atoms. The key insight: if `hasErrorOutput = false`, the call
is a value expression. Args are checked via `checkValue` (subsumption fires
inline on each arg). The whole thing stays nested — no intermediate variables.

```
synthValue expr := match expr.val with
  | .LiteralInt n => (.litInt n, .TInt)
  | .LiteralBool b => (.litBool b, .TBool)
  | .LiteralString s => (.litString s, .TString)
  | .Identifier id => (.var id.text, eraseType (Γ(id.text)))
  | .StaticCall callee args =>
      if callee.hasErrorOutput then DELEGATE TO synthProducer
      let checkedArgs := args.zip(params).map checkValue
      (.staticCall callee.text checkedArgs, eraseType returnType)
  | .FieldSelect obj field => (readField or fieldAccess depending on type)
  | .New classId => (.staticCall "MkComposite" [...], .TCore "Composite")
```

### What `synthProducer` Handles

Only genuinely effectful things: `hasErrorOutput` calls, assignment, control flow.

```
synthProducer expr := match expr.val with
  | .StaticCall callee args (hasErrorOutput = true) =>
      prodCallWithError callee (args checked) resultVar errorVar ...
  | .Assign [target] value =>
      let checkedRhs := checkValue value Γ(target)
      assign target checkedRhs
  | .LocalVariable name ty init =>
      let checkedInit := checkValue init ty
      varDecl name ty checkedInit; extend Γ
  | .IfThenElse cond thn els =>
      let checkedCond := checkValue cond bool
      ifThenElse checkedCond (elaborate thn) (elaborate els)
  | .While cond body =>
      let checkedCond := checkValue cond bool
      while checkedCond (elaborate body)
  | .Assert/Assume cond => ...checkValue cond bool...
  | .Block stmts => elaborateBlock stmts
  | .Exit/Return => ...
```

### Projection

Trivial cata. Map each FGL constructor to Laurel. Two-pass for procedure bodies:
- Pass 1: Collect all variable declarations (from user LocalVariables + prodCallWithError bindings)
- Pass 2: Emit assignments for initializers, control flow inline

All projected variable types = `TCore "Any"`. Uninitialized = `Hole`.

### Heap Infrastructure

Emit type declarations (Composite with typeTag, Box..Any, Field, Heap, TypeTag)
in `program.types`. Heap analysis + fixpoint propagation for signature rewriting.

---

## Execution Tasks

### Done (29/54 tests pass)

- [x] Unified subsume (CoercionResult, eraseType, LowType)
- [x] synthValue (atoms + pure calls), checkValue (subsume)
- [x] synthProducer, checkProducer (typing rules from architecture)
- [x] Projection (trivial cata, precise types, Hole → none)
- [x] fullElaborate (extend Γ with inputs+outputs)
- [x] Holes absorbed into Assign/LocalVariable rules
- [x] Translation: module-level code wrapped in __main__
- [x] Fix extractParams (args field, not posonlyargs)
- [x] Composite type declared (for prelude's from_Composite)

### Remaining (23 regressions)

**Default params / arg count mismatch (~3 tests: multi_function, default_params, optional_param_default)**

Resolution records params correctly now, but Translation's `resolveKwargs` fills
defaults with `from_None`. When a function has default params and is called with
fewer args, the arg count should match param count after defaults are filled.
The mismatch may be that Resolution's param count includes all params but the
call provides fewer (relying on defaults). Need to verify kwargs resolution works.

**Type checking errors in loops/control flow (~5 tests: break_continue, for_loop, loops, power, procedure_in_assert)**

Core type checking rejects our output. Need per-test diagnosis — likely issues
with how loop bodies or nested control flow interacts with precise types.
One known issue: for-loop havoc variables may need special handling after our
Hole changes.

**Class/heap tests (~10 tests: all class_*, with_*, composite_return)**

Full heap implementation not done. Need: Field/Box/TypeTag generation,
FieldSelect→readField, Assign FieldSelect→updateField, New→MkComposite with
typeTag, signature rewriting with heap param threading.

**test_method_param_reassign regression (1 test)**

Was passing, now fails after extractParams fix. The fix changed what params
Resolution reports for this test — needs investigation.

**PySpec/stub tests (~2 tests: foo_client_folder, invalid_client_type)**

These depend on PySpec stub loading which is out of scope (Phase 7).

### Next steps (priority order)

1. Diagnose type checking errors in non-class tests (break_continue, for_loop, power, procedure_in_assert) — these should be fixable without heap work
2. Fix default param / arg count mismatch
3. Investigate test_method_param_reassign regression
4. Full heap implementation (class tests)
5. End-to-end validation: target 40+/54

---

## Operational Discipline

1. ARCHITECTURE.md answers WHAT and WHY. This plan answers HOW.
2. Every line of code traces to a specific section of ARCHITECTURE.md.
3. Plan before code.
4. Commit after every successful `lake build`.
5. Never commit broken builds.
6. `diff_test.sh` is a CONSEQUENCE check, not the validation target.
7. Implementation agent + parallel review agent. No exceptions.
8. No type dispatch in the walk (subsume decides everything).
9. No coercions in Translation. No Python-specific logic in Elaboration.

### Compliance Checks

```bash
grep -n "from_int\|from_str\|from_bool\|Any_to_bool" Translation.lean | grep -v "^.*--"
grep -n "isPrelude\|isUserFunc\|isEffectful" Elaborate.lean
grep -n "canUpcast\|canNarrow\|typesEqual\|lowTypesEqual" Elaborate.lean | grep -v "^.*--"
```

---

## Theoretical Grounding

| Decision | Theory | Reference |
|----------|--------|-----------|
| Separate Value/Producer types | FGCBV (Levy 2003 §3.2) | Values inert, producers effectful |
| Pure calls as values | CBV semantics | Non-effectful calls don't need binding |
| Narrowing value-level | Partial functions | Preconditions, not runtime branching |
| Unified subsume | Bidirectional typing | One subsumption function |
| eraseType (HighType→LowType) | Type-directed compilation | Harper & Morrisett 1995 |
| Γ extended at binders | Standard type theory | Context grows under binders |
| Projection = cata | Forgetful functor | FGCBV → CBV |
| Heap as state-passing | Egger et al. 2014 | Discover locally, propagate globally |
| Metadata via smart constructors | Standard compiler practice | mkLaurel only |
