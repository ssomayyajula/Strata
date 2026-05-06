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

### 1. Write `subsume` + `CoercionResult` + `eraseType` + `LowType`

Replace canUpcast/canNarrow/lowTypesEqual with the unified function.
`lake build`.

### 2. Write `synthValue` (atoms + pure calls)

Handle: Literal, Identifier, StaticCall (pure only), FieldSelect, New.
Args checked via checkValue inline. No intermediate bindings.
`lake build`.

### 3. Write `checkValue`

Call synthValue, then `subsume`. Three outcomes handled.
`lake build`.

### 4. Write `synthProducer` (effectful calls + statements)

Handle: StaticCall (hasErrorOutput), Assign, LocalVariable, IfThenElse,
While, Assert, Assume, Block, Exit, Return.
Extend Γ at binding sites.
`lake build`.

### 5. Write `checkProducer`

Structural rules: if (propagate C), var-bind (propagate C), M-to-x, return.
Fallback: synth, bind, coerce bound value.
`lake build`.

### 6. Write projection (two-pass cata)

Pass 1: collect declarations. Pass 2: emit body. All vars Any. Hole for uninit.
`lake build`.

### 7. Write `fullElaborate` entry point

For each proc: extend Γ with params, elaborate body, project.
Heap analysis + infrastructure. `lake build`.

### 8. Fix heap infrastructure

Composite with typeTag. Box single constructor. Correct procedure names.
`lake build`.

### 9. End-to-end validation

`diff_test.sh compare pyAnalyzeV2`. Diagnose remaining failures against
architecture. Target: match or exceed 12/54 from earlier attempt.

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
