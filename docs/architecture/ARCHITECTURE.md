# Python → Laurel Translation Architecture


## Overview

This pipeline translates Python source code into Laurel (our verification IL)
via a series of compositional passes. The key insight is **separation of
concerns**: Resolution handles scoping, Translation handles Python's surface
syntax (desugaring to Laurel), and Elaboration handles the semantic heavy
lifting (effects, coercions, heap threading). Each pass has a clear input
type, output type, and contract.

The elaboration pass is based on **Fine-Grain Call-By-Value** (FGCBV), a
type theory that separates *values* (pure, duplicable) from *producers*
(effectful, sequenced). In FGCBV, effects are made explicit through a
sequencing construct `M to x. N` ("run M, bind its result to x, continue
with N") rather than being implicit in evaluation order as in plain CBV.
This separation means the elaborator can reason precisely about which
subexpressions have effects and insert the correct calling conventions.

**Graded effects** refine this further: instead of a binary pure/effectful
distinction, each producer carries a *grade* from a monoid `{1, proc, err,
heap, heap·err}` that classifies exactly which effects it performs. The grade
determines the calling convention (extra heap parameters, error outputs)
and the grade monoid's algebraic structure ensures compositionality —
sequencing two producers joins their grades.

**Bidirectional typing** makes the elaborator syntax-directed (no
backtracking, no unification). Values *synthesize* their types (bottom-up);
producers are *checked* against an ambient grade (top-down). The mode
discipline guarantees that at every point in the algorithm, enough
information is available to make a deterministic choice.

## The Pipeline

### Type signatures

```lean
def resolve   : Array (Python.stmt SourceRange) → ResolvedPythonProgram
def translate : ResolvedPythonProgram → Laurel.Program
def elaborate : Laurel.Program → Laurel.Program
```

### Diagram

```
Array (Python.stmt SourceRange)    (raw, unscoped)
  ↓ [Resolution: disambiguate, produce Laurel-ready identifiers]
ResolvedPythonProgram              (scoped, every node annotated with NodeInfo)
  ↓ [Translation: structural recursion, pattern match on NodeInfo]
Laurel.Program                     (impure CBV, effects implicit)
  ↓ [Elaboration: graded bidirectional typing, total]
Laurel.Program                     (effects explicit via calling conventions)
  ↓ [Core translation (existing, unchanged)]
Core
```

### What each pass does

**Resolution** is a fold over the Python AST that threads a growing context
as accumulator. Each declaration extends the context; each reference is
annotated with its resolution from the current context. The output is the
same AST with `ResolvedAnn` on every node — the scoping derivation for
the Python program.

**Translation** is a structural recursion over the resolved AST. It
pattern matches on `NodeInfo` and emits the corresponding Laurel construct.
No name resolution — that was done by Resolution. At call sites,
Translation uses the FuncSig from the annotation to match args to params
(positional + kwargs → param order). If a node is `.unresolved`,
Translation emits `Hole`.

**Elaboration** takes the Laurel program and transforms it: inserting
coercions (governed by the subtyping table), threading heap state
(governed by grades), and binding effectful subexpressions at statement
level (governed by the to-rule). It is total — every Laurel construct
produces output. Grade inference is by coinduction on the call graph.

### Intermediate types

**Phase distinction:** All Resolution types are purely Python-level. No
`Laurel.Identifier` is stored anywhere. Translation obtains Laurel
identifiers by calling accessor functions on the Python-level structures.
This makes the phase boundary explicit and prevents mixing.

```lean
abbrev PythonType := Python.expr SourceRange
abbrev PythonExpr := Python.expr SourceRange
abbrev ResolvedPythonExpr := Python.expr ResolvedAnn

structure PythonIdentifier where
  private mk ::
  private val : String
  deriving BEq, Hashable

-- Constructors (only ways to create a PythonIdentifier):
--   .fromAst    : Ann String SourceRange → PythonIdentifier  (from parsed AST node)
--   .fromImport : Ann String SourceRange → PythonIdentifier  (first component of dotted module)
--   .builtin    : String → PythonIdentifier                  (Python builtins: len, str, etc.)

-- Types are mutually recursive (ParamList stores ResolvedPythonExpr for defaults):
mutual

structure ParamList where
  required : List (PythonIdentifier × PythonType)
  optional : List (PythonIdentifier × PythonType × ResolvedPythonExpr)
  kwonly : List (PythonIdentifier × PythonType × Option ResolvedPythonExpr)

inductive FuncParams where
  | instance (receiver : PythonIdentifier) (params : ParamList)
  | static (params : ParamList)

structure FuncSig where
  name : PythonIdentifier
  className : Option PythonIdentifier
  params : FuncParams         -- private: accessed only via matchArgs/laurelDeclInputs
  returnType : PythonType
  locals : List (PythonIdentifier × PythonType)  -- private: accessed only via laurelLocals

inductive NodeInfo where
  | variable (name : PythonIdentifier)
  | funcCall (sig : FuncSig)
  | funcDecl (sig : FuncSig)
  | classNew (className : PythonIdentifier) (initSig : FuncSig)
  | classDecl (name : PythonIdentifier) (attributes : List (PythonIdentifier × PythonType)) (methods : List FuncSig)
  | attribute (name : PythonIdentifier)
  | withCtx (enterSig : FuncSig) (exitSig : FuncSig)
  | unresolved
  | irrelevant

structure ResolvedAnn where
  sr : SourceRange
  info : NodeInfo

end

structure ResolvedPythonProgram where
  stmts : Array (Python.stmt ResolvedAnn)
  moduleLocals : List (PythonIdentifier × PythonType)
```

**Accessor functions (Python → Laurel):** Translation calls these to obtain
`Laurel.Identifier` values on demand. They encode the naming conventions
(builtin mapping, method qualification) in one place.

```lean
def PythonIdentifier.toLaurel (id : PythonIdentifier) : Laurel.Identifier :=
  { text := id.val, uniqueId := none }

def FuncSig.laurelName (sig : FuncSig) : Laurel.Identifier :=
  match sig.className with
  | some cls => { text := s!"{cls.val}@{sig.name.val}", uniqueId := none }
  | none => { text := pythonNameToLaurel sig.name.val, uniqueId := none }

def FuncSig.laurelDeclInputs (sig : FuncSig) : List (Laurel.Identifier × PythonType)
  -- includes receiver for instance methods

def FuncSig.matchArgs [Monad m] (sig : FuncSig) (posArgs : List α)
    (kwargs : List (String × α)) (translateDefault : ResolvedPythonExpr → m α) : m (List α)
  -- zip-fold: positional → kwarg → default. Includes receiver slot for instance.

def FuncSig.laurelLocals (sig : FuncSig) : List (Laurel.Identifier × PythonType)
```

**`NodeInfo` complements:**
- `funcDecl` / `funcCall` — declaration and use site of a function
- `classDecl` / `classNew` — declaration and instantiation site of a class
- `withCtx` — `__enter__`/`__exit__` sigs on a with-item
- Operators (`+`, `==`, `not`) are `funcCall` — the sig carries the operator's
  runtime procedure name (with correct arity: 2 for binary, 1 for unary).
  Translation uses `matchArgs` uniformly.

**Design invariant:** Resolution stores only Python-level data. No
`Laurel.Identifier` appears in Resolution's types. Translation obtains
Laurel identifiers by calling accessor functions (`FuncSig.laurelName`,
`PythonIdentifier.toLaurel`, etc.) which encode naming conventions
(builtin mapping, method qualification) in one place. Translation never
fabricates identifiers from raw strings — it calls accessors on the
Python-level data that Resolution provided. This makes the phase boundary
explicit and naming conventions centralized.

**What Resolution disambiguates:** A Python `Name` node is syntactically
ambiguous — it could be a variable reference, a function callee, a class
reference, a type annotation, or a module. Resolution determines which it
is and attaches the appropriate `NodeInfo` variant with Laurel-ready data.
The process of disambiguation also produces auxiliary data (FuncSig, field
lists) that Translation needs to be mechanical.

**Internal vs output:** Resolution's internal `Ctx` tracks modules (for
resolving `module.func()` calls) and other intermediate state. This does
NOT appear in the output `NodeInfo`. Module Name nodes get `.irrelevant`
in the output — the Call node for `module.func()` gets `.call` with the
resolved callee.


## Engineering Principles

| Principle | Eliminates |
|---|---|
| Representation invariants | Runtime checks, dead branches |
| Proof-relevant elimination | Boolean blindness |
| Folds | Traversal choices |
| Correct by construction | Post-hoc rewrites |
| Separation of concerns | Decisions in wrong place |
| Monad carries context | Ad-hoc parameter passing |
| Types flow down | Bottom-up guessing |
| Illegal states unrepresentable | Undefined name references, invalid calls |
| No strings | Type-level resolution, not runtime checks |

### Illegal States Unrepresentable

**Resolution → Translation contract:** Translation CANNOT emit a `StaticCall`
to a name that Resolution did not verify. Enforced by the data: call sites
carry `.call callee sig` where `callee` is a `Laurel.Identifier` that
Resolution constructed. Translation pattern matches and forwards `callee`
directly. It cannot fabricate a callee name because it never constructs
`Laurel.Identifier` values — it only receives them from the annotation.

Unresolvable calls carry `.unresolved` and Translation emits Hole.

This eliminates an entire class of bugs:
- Undefined function calls (→ free variables in output)
- Ill-qualified method names (→ "get_x" instead of "Foo@get_x")
- Arity mismatches (sig in annotation determines param count)
- Stringly-typed name fabrication in Translation

**Types are Python annotation expressions:** Types flow through Resolution
as `PythonType := Python.expr SourceRange` — the actual annotation from the
source. Translation maps them to `HighType` when emitting Laurel. No string
intermediate (`extractTypeStr` is abolished).

**No boolean blindness:** `NodeInfo` is an inductive — pattern matching
on it gives you the data you need and determines Translation's action.
There is no `isResolved : String → Bool` followed by a separate lookup.
The annotation IS the resolution.



## Resolution

```lean
def resolve : Array (Python.stmt SourceRange) → ResolvedPythonProgram
```

**Input:** Raw Python AST (`Python.stmt SourceRange`).
**Output:** `ResolvedPythonProgram` — resolved stmts + module-level locals.

Resolution is a fold over the Python AST that threads a growing context
as accumulator. Its job is to **disambiguate** what each AST node means
and attach the result as a `NodeInfo` annotation. The process of
disambiguation produces Laurel-ready identifiers and auxiliary data
(FuncSig, field lists) that Translation uses mechanically.

At the top level (module scope), each declaration extends the context:

- `def f(...)` → extends context, annotates FunctionDef with `.funcDecl sig`
- `class C` → extends context with class + methods, annotates with `.classDecl`
- `import M` → extends context internally (module tracked in Ctx only)
- `x : T = ...` → extends context with variable

At each reference, Resolution annotates with the appropriate `NodeInfo`:

- Name use (variable) → `.variable name`
- Name use (function) → `.variable name` (same Python name — accessor maps to Laurel)
- Name use (class) → `.variable name` (classes are valid expressions)
- Name use (module) → `.irrelevant` (only meaningful as Call receiver)
- Call (function) → `.funcCall sig`
- Call (class) → `.classNew className initSig`
- Call (method) → `.funcCall sig` (sig has `className = some _` for qualification)
- Call (module function) → `.funcCall sig` (sig has bare name, accessor maps it)
- Attribute access → `.attribute name` (bare field name; Elaboration resolves based on synthesized receiver type)
- BinOp/Compare/UnaryOp → `.funcCall sig` (sig carries operator's Python name, accessor maps to runtime procedure)
- Unresolvable → `.unresolved`
- Non-reference (literal, keyword, etc.) → `.irrelevant`

**Attribute resolution:** Every `.Attribute` node gets a `ResolvedAnn` with
`.attribute name` where `name` is the bare Python field name. Translation
emits `FieldSelect obj name.toLaurel`. Elaboration synthesizes the receiver
type and branches:
- If receiver type is `Composite`: look up the field in `classFields`, emit
  `readField` with the qualified `$field.Class.field` constructor.
- If receiver type is `Any`: produce `Any` (havoc — field access on Any is
  unknowable).

When the Attribute is the callee of a Call, the Call node's annotation
carries `.funcCall` with the resolved method sig — the Attribute's own
`.attribute` annotation is irrelevant in that case (the Call subsumes it).

Within a function body, the context is extended with:
- Parameters (from the function signature). A parameter with no annotation
  does NOT override a more specific type already in the context (e.g. `self`
  typed by the enclosing class).
- Locals (Python's scoping rule: any assignment target anywhere in
  the body is function-local)

Within a class body, the context is extended with:
- `self` typed as the enclosing class (enables method resolution on `self`)
- All methods registered as `ClassName@method` (enables `self.method()` lookup)
- All fields and class-level annotations

This means the class body is resolved with a context where `self` has type
`ClassName`. When Resolution encounters `self.method()`, it looks up `self`
→ type `ClassName`, then looks up `ClassName@method` → resolves to `.call`.

**Method resolution on receivers:** The receiver of a method call
(`receiver.method()`) can be any expression. Resolution determines the
receiver's type using `typeOfExpr`:

- `.Name n` → look up `ctx[n]`, get the variable's type
- `.Attribute obj field` → recursively get type of `obj`, find that class
  in ctx, look up `field` in its field list, get the field's type

These two forms are called **spines**. Resolution chases spines to determine
receiver types. For any non-spine receiver (`.Call`, `.Subscript`, `.IfExp`,
etc.), Resolution emits `.unresolved`. This is tech debt — those forms
could be resolved by interpreting return types and generic type parameters,
but are not yet implemented.

Once `typeOfExpr` returns a type `.Name _ className _`, Resolution looks up
`ctx["{className}@{methodName}"]` to get the method's FuncSig.

**Resolution stores Python-level data only.** The builtin mapping
(`len` → `Any_len_to_Any`), method qualification
(`get_x` → `Account@get_x`), and module qualification
(`timedelta` → `datetime_timedelta`) are encoded in accessor functions
(`FuncSig.laurelName`, `PythonIdentifier.toLaurel`). Translation calls
these accessors — it never fabricates Laurel identifiers from strings
or applies naming conventions itself.

**Resolution does NOT:**
- Determine effects (Elaboration does that)
- Map PythonType → HighType (Translation does that)
- Emit Laurel constructs (Translation does that)

**Classes without explicit `__init__`:** Every Python class has `__init__`.
If not explicitly defined, it inherits `object.__init__` which takes no
arguments (just `self`). Resolution produces `.classNew cls init sig` where
`sig` has zero params (excluding `self`).

**`from foo import bar`:** If we have no information about `bar`, it is
registered as `CtxEntry.unresolved`. Names that reference it get
`.unresolved` and Translation emits Hole.

**Known incompleteness:** Match case pattern bindings are not yet extracted
as function locals. Requires walking `Python.pattern` inductive.

**Contract with Translation:** The resolved AST IS the interface.
Translation pattern matches on `NodeInfo` and uses the `Laurel.Identifier`
values directly. It never constructs identifiers from strings.



## Translation

```lean
def translate : ResolvedPythonProgram → Laurel.Program
```

A structural recursion over the resolved Python AST. Translation has
two modes of operation depending on the node:

**Reference nodes** (Name, Call, BinOp, Attribute, etc.): Translation
pattern matches on `ann.info : NodeInfo` and transcribes:
- `.variable name` → `Identifier name.toLaurel`
- `.funcCall sig` → `StaticCall sig.laurelName (matchArgs sig posArgs kwargs)`
- `.classNew className initSig` → `Assign [tmp] (New className.toLaurel); StaticCall initSig.laurelName (tmp :: args)`
- `.attribute name` → `FieldSelect (translateExpr obj) name.toLaurel`
- `.unresolved` → `Hole`
- `.irrelevant` → not reachable in expression position

For BinOp/UnaryOp/Compare/BoolOp, Translation reads `.funcCall sig` from
the annotation and uses the Python AST node structure to determine the
operand layout (binary, unary, etc.).

**Structural nodes** (literals, control flow, assignments): Translation
emits the corresponding Laurel construct directly:
- `LiteralInt`, `LiteralBool`, `LiteralString` (from constants)
- `Block`, `While`, `IfThenElse` (from control flow)
- `Assign`, `Exit`, `Assert`, `Assume` (from statements)
- `LocalVariable` (from `sig.locals` / `moduleLocals`)
- List/dict/tuple encoding — Translation uses runtime constants
  (defined once as `Laurel.Identifier` values from the runtime interface,
  NOT as string literals in Translation code)

**Declaration nodes** (FunctionDef, ClassDef): Translation reads
`.funcDecl sig` / `.classDecl name fields methods` and emits
`Procedure` / `CompositeType` using the sig data directly.

**Translation does NOT:**
- Fabricate `Laurel.Identifier` from raw strings (calls accessors instead)
- Apply naming conventions (accessors encode them)
- Resolve method calls or qualify names (Resolution did that)
- Insert casts or coercions (Elaboration does that)
- Determine effects (Elaboration does that)

**Translation DOES:**
- Map `PythonType` → `HighType` (for procedure input/output/local types)
- Desugar Python control flow to Laurel (loops → labeled blocks, etc.)
- Match args to params (using FuncSig from annotation)
- Emit scope declarations (`LocalVariable` from sig.locals / moduleLocals)
- Wrap module-level code in `__main__` procedure

### Desugarings

All identifiers in the Laurel column come from either:
- The `NodeInfo` annotation (operators, callees — Resolution produced them)
- Runtime constants (data structure constructors — extracted from runtime program)
- The `FuncSig` annotation (variable names, param names, locals)

Translation never fabricates these as string literals.

| Python | Laurel | Name source |
|---|---|---|
| `x = expr` | `Assign [x] expr` | `x` from `.variable id` |
| `a, b = rhs` | `tmp := rhs; a := Get(tmp,0); b := Get(tmp,1)` | `a`,`b` from annotation; `Get` = runtime constant |
| `x += v` | `Assign [x] (StaticCall op [x, v])` | `op` from `.operator callee` |
| `x[i] = v` | `Assign [x] (StaticCall Any_sets [...])` | `Any_sets` = runtime constant |
| `x[start:stop]` | `StaticCall Any_get [x, StaticCall from_Slice [...]]` | runtime constants |
| `obj.field` | `FieldSelect (translate obj) field` | `field` from `.attribute`; Elaboration qualifies based on receiver type |
| `return e` | `Assign [LaurelResult] e; Exit $body` | output var from sig; label is structural |
| `Foo(args)` (class) | `Assign [tmp] (New cls); StaticCall init (tmp :: args)` | `cls`, `init` from `.classNew` |
| `with mgr as v: body` | `v := StaticCall enter [mgr]; body; StaticCall exit [mgr]` | `enter`, `exit` from class method resolution |
| `for x in iter: body` | `x := Hole; Assume(StaticCall PIn [x, iter]); body` | `PIn` = runtime constant |
| `[a, b, c]` | `StaticCall from_ListAny [StaticCall ListAny_cons [...]]` | runtime constants |
| `{k: v}` | `StaticCall from_DictStrAny [StaticCall DictStrAny_cons [...]]` | runtime constants |
| `f"{expr}"` | `StaticCall to_string_any [expr]` | runtime constant |



## Elaboration

Elaboration transforms Laurel typing derivations into GFGL typing derivations.

### Laurel Type System (Source)

Laurel is an impure CBV language. One judgment form. The context Γ carries
variable bindings `(x : A)` and label names `(l)` (untyped scope markers).

```
Γ ⊢_L e : A
```

```
─────────────────            ─────────────────            ─────────────────
Γ ⊢_L n : int               Γ ⊢_L b : bool              Γ ⊢_L s : string


(x : A) ∈ Γ
─────────────────
Γ ⊢_L x : A


f : (A₁,...,Aₙ) → B ∈ Γ    Γ ⊢_L e₁ : A₁  ...  Γ ⊢_L eₙ : Aₙ
──────────────────────────────────────────────────────────────────
Γ ⊢_L f(e₁,...,eₙ) : B


Γ ⊢_L e : C    fields(C,f) = T
────────────────────────────────
Γ ⊢_L e.f : T


C ∈ classes(Γ)
─────────────────
Γ ⊢_L new C : C


─────────────────            ─────────────────
Γ ⊢_L ?? : A  (nondet)      Γ ⊢_L ? : A  (det)


Γ ⊢_L e : Γ(x)    Γ ⊢_L rest : A
────────────────────────────────────
Γ ⊢_L (x := e); rest : A


Γ ⊢_L e : T    Γ,x:T ⊢_L rest : A
─────────────────────────────────────
Γ ⊢_L (var x:T := e); rest : A


Γ ⊢_L c : bool    Γ ⊢_L t : A    Γ ⊢_L f : A    Γ ⊢_L rest : A
──────────────────────────────────────────────────────────────────
Γ ⊢_L (if c then t else f); rest : A


Γ ⊢_L c : bool    Γ ⊢_L body : A    Γ ⊢_L rest : A
──────────────────────────────────────────────────────
Γ ⊢_L (while c do body); rest : A


Γ,l ⊢_L body : A    Γ ⊢_L rest : A
────────────────────────────────────────
Γ ⊢_L {body}ₗ; rest : A


l ∈ Γ
─────────────────────
Γ ⊢_L (exit l) : A


Γ ⊢_L e : A
─────────────────────
Γ ⊢_L (return e) : A


Γ ⊢_L c : bool    Γ ⊢_L rest : A
───────────────────────────────────
Γ ⊢_L (assert c); rest : A


Γ ⊢_L c : bool    Γ ⊢_L rest : A
───────────────────────────────────
Γ ⊢_L (assume c); rest : A


Γ ⊢_L obj : C    Γ ⊢_L v : fieldType(C,f)    Γ ⊢_L rest : A
──────────────────────────────────────────────────────────────
Γ ⊢_L (obj.f := v); rest : A


Γ ⊢_L root : Any    Γ ⊢_L idx : Any    Γ ⊢_L v : Any    Γ ⊢_L rest : A
──────────────────────────────────────────────────────────────────────────
Γ ⊢_L (root[idx] := v); rest : A
```

### The Grade Monoid

```
(E, ≤, 1, ·, \) where E = {pure, proc, err, heap, heapErr}

Order:
  pure ≤ proc ≤ err ≤ heapErr
  pure ≤ proc ≤ heap ≤ heapErr

Left residual (d \ e):
  pure \ e = e
  proc \ proc = pure    proc \ err = err    proc \ heap = heap    proc \ heapErr = heapErr
  err \ err = pure      err \ heapErr = heap
  heap \ heap = pure    heap \ heapErr = err
  heapErr \ heapErr = pure
```

### Elaboration's type translation (⟦·⟧ : HighType → LowType)

```lean
def ⟦·⟧ : HighType → LowType
  | .TInt => .TInt | .TBool => .TBool | .TString => .TString
  | .TFloat64 => .TFloat64 | .TVoid => .TVoid | .TCore n => .TCore n
  | .UserDefined id => match id.text with
    | "Any" => .TCore "Any" | "Error" => .TCore "Error"
    | "ListAny" => .TCore "ListAny" | "DictStrAny" => .TCore "DictStrAny"
    | _ => .TCore "Composite"
  | .THeap => .TCore "Heap"
  | _ => .TCore "Any"
```

(Implementation name: `eraseType`)

### GFGL Type System (Target — Bidirectional, Graded)

GFGL has two sorts: **values** (pure) and **producers** (effectful, graded).
Typing is bidirectional. The context Γ carries variable bindings `(x : A)`
and label names `(l)` (untyped scope markers, same as Laurel).

```
Γ ⊢_v V ⇒ A           value synthesis
Γ ⊢_v V ⇐ A           value checking
Γ ⊢_p M ⇒ A & d       producer synthesis
Γ ⊢_p M ⇐ A & e       producer checking
```

#### Value rules

```
─────────────────────────
Γ ⊢_v litInt n ⇒ TInt

(x : A) ∈ Γ
─────────────────────────
Γ ⊢_v var x ⇒ A

f : (A₁,...,Aₙ) → B ∈ Γ    Γ ⊢_v V₁ ⇐ A₁  ...  Γ ⊢_v Vₙ ⇐ Aₙ
───────────────────────────────────────────────────────────────────
Γ ⊢_v staticCall f [V₁,...,Vₙ] ⇒ B

Γ ⊢_v V ⇒ A    A ≤ B ↦ c
─────────────────────────────────
Γ ⊢_v c(V) ⇐ B
```

#### Producer synthesis

There is exactly one producer synthesis rule. By inversion, any synthesis
derivation gives you the callee, checked args, return type, and grade.

```
f : (A₁,...,Aₙ) → B & d ∈ Γ    Γ ⊢_v V₁ ⇐ A₁  ...  Γ ⊢_v Vₙ ⇐ Aₙ
──────────────────────────────────────────────────────────────────────────
Γ ⊢_p f(V₁,...,Vₙ) ⇒ B & d
```

#### Producer subsumption (mode switch ⇒ₚ to ⇐ₚ)

By inversion on the single synthesis rule, M = f(V₁,...,Vₙ) with known f,
args, return type B, and grade d. Producer subsumption binds the call's
outputs via effectfulCall and checks the continuation at the residual grade.
Let [x₁:T₁,...,xₖ:Tₖ] = outputs(f) and r = resultIdx(d):

```
Γ ⊢_p f(V₁,...,Vₙ) ⇒ B & d    B ≤ A ↦ c
Γ,x₁:T₁,...,xₖ:Tₖ ⊢_p K ⇐ A & (d\e)
────────────────────────────────────────────────────────────────────────────
Γ ⊢_p effectfulCall f [V₁,...,Vₙ] [x₁:T₁,...,xₖ:Tₖ] (c(xᵣ); K) ⇐ A & e
```

`xᵣ` is the result output (position r among the declared outputs).
c coerces it to the target type. K is checked at residual d\e.

#### Producer checking rules

```
─────────────────────────
Γ ⊢_p unit ⇐ A & e

l ∈ Γ
─────────────────────────
Γ ⊢_p exit l ⇐ A & e

Γ ⊢_v V ⇐ A
──────────────────────────────
Γ ⊢_p returnValue V ⇐ A & e

Γ ⊢_v V ⇐ Γ(x)    Γ ⊢_p K ⇐ A & e
──────────────────────────────────────
Γ ⊢_p assign x V K ⇐ A & e

Γ ⊢_v V ⇐ T    Γ,x:T ⊢_p K ⇐ A & e
──────────────────────────────────────
Γ ⊢_p varDecl x T V K ⇐ A & e

Γ ⊢_v V ⇐ bool    Γ ⊢_p M_t ⇐ A & e    Γ ⊢_p M_f ⇐ A & e    Γ ⊢_p K ⇐ A & e
─────────────────────────────────────────────────────────────────────────────────────
Γ ⊢_p ifThenElse V M_t M_f K ⇐ A & e

Γ ⊢_v V ⇐ bool    Γ ⊢_p M_b ⇐ A & e    Γ ⊢_p K ⇐ A & e
─────────────────────────────────────────────────────────────
Γ ⊢_p whileLoop V M_b K ⇐ A & e

Γ ⊢_v V ⇐ bool    Γ ⊢_p K ⇐ A & e
─────────────────────────────────────
Γ ⊢_p assert V K ⇐ A & e

Γ ⊢_v V ⇐ bool    Γ ⊢_p K ⇐ A & e
─────────────────────────────────────
Γ ⊢_p assume V K ⇐ A & e

Γ,l ⊢_p M_b ⇐ A & e    Γ ⊢_p K ⇐ A & e
───────────────────────────────────────────
Γ ⊢_p labeledBlock l M_b K ⇐ A & e
```

`labeledBlock`/`exit` form an intro/elim pair for label scope.
`exit l` is non-returning (checks at any A & e). `unit` terminates
the current continuation (control flows to the enclosing after-block).

### The Translation ⟦·⟧

#### Translation on contexts

```
⟦Γ⟧ = { (x : ⟦A⟧) | (x:A) ∈ Γ } ∪ { l | l ∈ Γ }
```

Each translation clause extends ⟦Γ⟧ with new bindings at erased types:
effectfulCall adds fresh output variables at ⟦Tᵢ⟧, varDecl adds the
declared name at ⟦T⟧. These extensions are visible in the recursive
call on continuation K.

#### The four functions

The translation is four mutually recursive functions.

Synthesis takes Γ and a raw expression, discovers A', and produces a
GFGL derivation at ⟦A'⟧. Value checking takes A : HighType and a Laurel
derivation at A, and produces a GFGL value checked at ⟦A⟧. Producer
checking additionally takes a grade e.

```
⟦·⟧⇒ᵥ : (Γ : Ctx) → (e : StmtExpr) → ∃(A' : HighType)(V : FGLValue). (Γ ⊢_L e : A') → (⟦Γ⟧ ⊢_v V ⇒ ⟦A'⟧)
⟦·⟧⇐ᵥ : (A : HighType) → (Γ ⊢_L e : A) → ∃V. (⟦Γ⟧ ⊢_v V ⇐ ⟦A⟧)
⟦·⟧⇒ₚ : (Γ : Ctx) → (e : StmtExpr) → ∃(A' : HighType)(M : FGLProducer)(d : Grade). (Γ ⊢_L e : A') → (⟦Γ⟧ ⊢_p M ⇒ ⟦A'⟧ & d)
⟦·⟧⇐ₚ : (A : HighType) → (e : Grade) → (Γ ⊢_L S;rest : A) → ∃M. (⟦Γ⟧ ⊢_p M ⇐ ⟦A⟧ & e)
```

⟦·⟧⇒ₚ has exactly one clause (call with grade > pure); inversion is trivial.

#### Grade inference

**Input** to elaboration: a Laurel.Program (typed procedures with bodies).  
**Output** of elaboration: a GFGL.Program (same procedures, graded, effect-explicit bodies).

Elaboration proceeds in two passes over the program's procedure list.

**Pass 1 — grade inference (coinduction over the call graph):**

Input: the Laurel program. Output: `procGrades : String → Grade`.

Runtime procedure grades are read structurally from the signature:
```lean
def gradeFromSignature (proc : Laurel.Procedure) : Grade :=
  let hasError := proc.outputs.any fun o => eraseType o.type.val == .TCore "Error"
  let hasHeap := proc.inputs.any fun i => eraseType i.type.val == .TCore "Heap"
  match hasHeap, hasError with
  | true, true => .heapErr | true, false => .heap
  | false, true => .err    | false, false => if proc.isFunctional then .pure else .proc
```

User procedure grades are inferred by coinduction: for each user procedure f,
attempt `⟦body(f)⟧⇐ₚ` at grade pure, then proc, then err, then heap, then
heapErr. The first grade where elaboration succeeds is f's grade. When a
callee's grade exceeds the trial grade, `d\e` is undefined and elaboration
fails — this is what drives the iteration upward. The process converges
because the grade lattice is finite and the grades are monotone.

**Pass 2 — term production:**

Input: the Laurel program + procGrades. Output: the GFGL program.

For each procedure, elaborate its body via ⟦body⟧⇐ₚ at the inferred grade.
Pass 1 guarantees this succeeds (the grade was chosen to make it succeed).

#### Entry point (per-procedure)

For procedure `f(p₁:T₁,...,pₘ:Tₘ) → R` with grade e = procGrades[f]:

```
grade(f) ∈ {heap, heapErr}:
  inputs  := [$heap_in : Heap] ++ params(f)
  outputs := [$heap : Heap] ++ resultOutputs(f) ++ (if err ≤ grade(f) then [maybe_except : Error] else [])
  body prefix: $heap := $heap_in

grade(f) = err:
  outputs := resultOutputs(f) ++ [maybe_except : Error]

grade(f) ∈ {pure, proc}:
  (no rewriting)
```

Elaboration begins (Γ extended with both inputs and outputs):
```
⟦Γ,p₁:T₁,...,pₘ:Tₘ,LaurelResult:R,maybe_except:Error ⊢_L B : R⟧⇐ₚ at grade e
```

#### Subgrading

A subgrading judgment `d ≤ e` has a *witness*: the calling convention
transformation applied at that call site. The witness determines what
arguments are passed, what outputs are declared, and which output
position holds the result.

```
d            args prepended    outputs(f)                         resultIdx   d\e
───────────────────────────────────────────────────────────────────────────────────────
pure         (none)            (none — value-level staticCall)    —           e
proc         (none)            [result : ⟦B⟧]                    0           proc\e
err          (none)            [result : ⟦B⟧, maybe_except : Error]  0       err\e
heap         [$heap]           [$heap : Heap, result : ⟦B⟧]      1           heap\e
heapErr      [$heap]           [$heap : Heap, result : ⟦B⟧, maybe_except : Error]  1  heapErr\e
```

`d\e` is defined iff `d ≤ e`. If not, elaboration fails (drives grade
inference upward). `$heap` is the current heap variable (initialized from
`$heap_in` at proc entry, updated to a fresh name by each effectfulCall
whose outputs include a Heap position).

#### Subtyping

A subtyping judgment `A ≤ B` has a *witness*: a coercion function
`c : FGLValue → FGLValue`. When `A = B`, c = id. Otherwise:

```
A ≤ B                    c(v)
─────────────────────────────────────────────────
TInt ≤ Any               fromInt(v)
TBool ≤ Any              fromBool(v)
TString ≤ Any            fromStr(v)
TFloat64 ≤ Any           fromFloat(v)
Composite ≤ Any          fromComposite(v)
ListAny ≤ Any            fromListAny(v)
DictStrAny ≤ Any         fromDictStrAny(v)
TVoid ≤ Any              fromNone
Any ≤ TBool              Any_to_bool(v)
Any ≤ TInt               Any..as_int!(v)
Any ≤ TString            Any..as_string!(v)
Any ≤ TFloat64           Any..as_float!(v)
Any ≤ Composite          Any..as_Composite!(v)
```

Upward (T ≤ Any): value constructors (boxing).
Downward (Any ≤ T): pure function calls (unboxing/narrowing).
If neither A ≤ B nor A = B: undefined.

#### Auxiliary definitions

```
outputs(g)    = declared outputs of g after signature rewriting
resultIdx(d)  = 0 if d ∈ {proc, err}; 1 if d ∈ {heap, heapErr}
$field.C.f    = zero-arity Field datatype constructor (one per class field)
boxCtor(T)    = boxConstructorName(T)  (e.g. BoxInt, BoxComposite, BoxAny)
```

#### Argument sequencing

The call clauses below use `⟦Dᵢ⟧⇐ᵥ` on each argument. This is only
valid when every argument synthesizes as a value (grade = pure). When
argument eᵢ has procGrades[callee(eᵢ)] > pure, it must be sequenced:

```
⟦Dᵢ⟧⇒ₚ :: ⟦Γ⟧ ⊢_p gᵢ(W₁,...,Wₘ) ⇒ Bᵢ & dᵢ    dᵢ ≤ e
⟦Γ⟧,y₁:T₁,...,yⱼ:Tⱼ ⊢_p ... ⇐ A & (dᵢ\e)
──────────────────────────────────────────────────────────────────────────
⟦Γ⟧ ⊢_p effectfulCall gᵢ [W₁,...,Wₘ] [y₁:T₁,...,yⱼ:Tⱼ] (... uses yᵣ as Vᵢ ...) ⇐ A & e
```

The result variable yᵣ (at resultIdx(dᵢ)) is then used in place of Vᵢ
in the outer call. Multiple effectful arguments nest left-to-right.
This turns the outer call from a value-level staticCall into a producer.


#### Clauses of ⟦·⟧⇒ᵥ

```
D :: Γ ⊢_L n : int       ↦    ⟦D⟧⇒ᵥ :: ⟦Γ⟧ ⊢_v litInt n ⇒ TInt
D :: Γ ⊢_L b : bool      ↦    ⟦D⟧⇒ᵥ :: ⟦Γ⟧ ⊢_v litBool b ⇒ TBool
D :: Γ ⊢_L s : string    ↦    ⟦D⟧⇒ᵥ :: ⟦Γ⟧ ⊢_v litString s ⇒ TString

(x : A) ∈ Γ
─────────────────
D :: Γ ⊢_L x : A                     ↦    ⟦D⟧⇒ᵥ :: ⟦Γ⟧ ⊢_v var x ⇒ ⟦A⟧


D₁ :: Γ ⊢_L e₁ : A₁  ...  Dₙ :: Γ ⊢_L eₙ : Aₙ
──────────────────────────────────────────────────
D :: Γ ⊢_L f(e₁,...,eₙ) : B    where procGrades[f] = pure

        ↦

⟦D₁⟧⇐ᵥ :: ⟦Γ⟧ ⊢_v V₁ ⇐ ⟦A₁⟧  ...  ⟦Dₙ⟧⇐ᵥ :: ⟦Γ⟧ ⊢_v Vₙ ⇐ ⟦Aₙ⟧
────────────────────────────────────────────────────────────────────────
⟦D⟧⇒ᵥ :: ⟦Γ⟧ ⊢_v staticCall f [V₁,...,Vₙ] ⇒ ⟦B⟧


D_obj :: Γ ⊢_L obj : C    fields(C,f) = T    ($heap : Heap) ∈ ⟦Γ⟧
───────────────────────────────────────────────────────────────────
D :: Γ ⊢_L obj.f : T

        ↦

⟦D_obj⟧⇐ᵥ :: ⟦Γ⟧ ⊢_v V_obj ⇐ Composite
──────────────────────────────────────────────────────────────────────────────────
⟦D⟧⇒ᵥ :: ⟦Γ⟧ ⊢_v staticCall (boxDestructor(T)) [staticCall readField [$heap, V_obj, $field.C.f]] ⇒ ⟦T⟧


D :: Γ ⊢_L ?? : A       ↦    ⟦D⟧⇒ᵥ :: ⟦Γ⟧ ⊢_v staticCall $havoc_N [] ⇒ Any
D :: Γ ⊢_L ?  : A       ↦    ⟦D⟧⇒ᵥ :: ⟦Γ⟧ ⊢_v staticCall $hole_N [] ⇒ Any
```

#### ⟦·⟧⇐ᵥ

```
⟦D⟧⇒ᵥ :: ⟦Γ⟧ ⊢_v V ⇒ B    B ≤ ⟦A⟧ ↦ c
──────────────────────────────────────────
⟦D⟧⇐ᵥ :: ⟦Γ⟧ ⊢_v c(V) ⇐ ⟦A⟧
```

A : HighType is the input. B : LowType is discovered by synthesis.

#### ⟦·⟧⇒ₚ

There is exactly one clause. procGrades[f] = pure implies ⟦·⟧⇒ₚ is
undefined (delegate to ⟦·⟧⇒ᵥ). Inversion on any producer synthesis
derivation immediately gives you f, the checked args, ⟦B⟧, and d.

```
D₁ :: Γ ⊢_L e₁ : A₁  ...  Dₙ :: Γ ⊢_L eₙ : Aₙ
──────────────────────────────────────────────────
D :: Γ ⊢_L f(e₁,...,eₙ) : B    where procGrades[f] = d > pure

        ↦

⟦D₁⟧⇐ᵥ :: ⟦Γ⟧ ⊢_v V₁ ⇐ ⟦A₁⟧  ...  ⟦Dₙ⟧⇐ᵥ :: ⟦Γ⟧ ⊢_v Vₙ ⇐ ⟦Aₙ⟧
──────────────────────────────────────────────────────────────────────
⟦D⟧⇒ₚ :: ⟦Γ⟧ ⊢_p f(V₁,...,Vₙ) ⇒ ⟦B⟧ & d
```

#### Producer subsumption in the translation


```
D₁ :: Γ ⊢_L e₁ : A₁  ...  Dₙ :: Γ ⊢_L eₙ : Aₙ    K :: Γ ⊢_L rest : A
──────────────────────────────────────────────────────────────────────────
D :: Γ ⊢_L g(e₁,...,eₙ); rest : A    where procGrades[g] = d > pure

        ↦    let [x₁:T₁,...,xₖ:Tₖ] = outputs(g)

⟦D₁⟧⇐ᵥ :: ⟦Γ⟧ ⊢_v V₁ ⇐ ⟦A₁⟧  ...  ⟦Dₙ⟧⇐ᵥ :: ⟦Γ⟧ ⊢_v Vₙ ⇐ ⟦Aₙ⟧
⟦K⟧⇐ₚ :: ⟦Γ⟧,x₁:T₁,...,xₖ:Tₖ ⊢_p M_k ⇐ ⟦A⟧ & (d\e)
────────────────────────────────────────────────────────────────────────────────────────────
⟦D⟧⇐ₚ :: ⟦Γ⟧ ⊢_p effectfulCall g [V₁,...,Vₙ] [x₁:T₁,...,xₖ:Tₖ] M_k ⇐ ⟦A⟧ & e
```

#### Clauses of ⟦·⟧⇐ₚ

```
D_c :: Γ ⊢_L c : bool    D_t :: Γ ⊢_L t : A    D_f :: Γ ⊢_L f : A    K :: Γ ⊢_L rest : A
─────────────────────────────────────────────────────────────────────────────────────────────
D :: Γ ⊢_L (if c then t else f); rest : A

        ↦

⟦D_c⟧⇐ᵥ :: ⟦Γ⟧ ⊢_v V ⇐ bool    ⟦D_t⟧⇐ₚ :: ⟦Γ⟧ ⊢_p M_t ⇐ ⟦A⟧ & e    ⟦D_f⟧⇐ₚ :: ⟦Γ⟧ ⊢_p M_f ⇐ ⟦A⟧ & e    ⟦K⟧⇐ₚ :: ⟦Γ⟧ ⊢_p M_k ⇐ ⟦A⟧ & e
────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────
⟦D⟧⇐ₚ :: ⟦Γ⟧ ⊢_p ifThenElse V M_t M_f M_k ⇐ ⟦A⟧ & e


D_e :: Γ ⊢_L e : A
───────────────────
D :: Γ ⊢_L (return e) : A

        ↦

⟦D_e⟧⇐ᵥ :: ⟦Γ⟧ ⊢_v V ⇐ ⟦A⟧
─────────────────────────────────────────
⟦D⟧⇐ₚ :: ⟦Γ⟧ ⊢_p returnValue V ⇐ ⟦A⟧ & e


D_init :: Γ ⊢_L e : T    K :: Γ,x:T ⊢_L rest : A
───────────────────────────────────────────────────
D :: Γ ⊢_L (var x:T := e); rest : A

        ↦

⟦D_init⟧⇐ᵥ :: ⟦Γ⟧ ⊢_v V ⇐ ⟦T⟧    ⟦K⟧⇐ₚ :: ⟦Γ⟧,x:⟦T⟧ ⊢_p M_k ⇐ ⟦A⟧ & e
──────────────────────────────────────────────────────────────────────────────
⟦D⟧⇐ₚ :: ⟦Γ⟧,x:⟦T⟧ ⊢_p varDecl x ⟦T⟧ V M_k ⇐ ⟦A⟧ & e


D_c :: Γ ⊢_L c : bool    K :: Γ ⊢_L rest : A
──────────────────────────────────────────────
D :: Γ ⊢_L (assert c); rest : A

        ↦

⟦D_c⟧⇐ᵥ :: ⟦Γ⟧ ⊢_v V ⇐ bool    ⟦K⟧⇐ₚ :: ⟦Γ⟧ ⊢_p M_k ⇐ ⟦A⟧ & e
────────────────────────────────────────────────────────────────────────
⟦D⟧⇐ₚ :: ⟦Γ⟧ ⊢_p assert V M_k ⇐ ⟦A⟧ & e


D_e :: Γ ⊢_L e : B    K :: Γ ⊢_L rest : A    e is not a call to g with procGrades[g] > pure
──────────────────────────────────────────────────────────────────────────────────────────
D :: Γ ⊢_L (x := e); rest : A

        ↦

⟦D_e⟧⇐ᵥ :: ⟦Γ⟧ ⊢_v V ⇐ ⟦Γ(x)⟧    ⟦K⟧⇐ₚ :: ⟦Γ⟧ ⊢_p M_k ⇐ ⟦A⟧ & e
────────────────────────────────────────────────────────────────────────
⟦D⟧⇐ₚ :: ⟦Γ⟧ ⊢_p assign x V M_k ⇐ ⟦A⟧ & e


D₁ :: Γ ⊢_L e₁ : A₁  ...  Dₙ :: Γ ⊢_L eₙ : Aₙ    K :: Γ ⊢_L rest : A    procGrades[g] = d > pure
──────────────────────────────────────────────────────────────────────────────────────────────────────
D :: Γ ⊢_L (x := g(e₁,...,eₙ)); rest : A

        ↦    let [x₁:T₁,...,xₖ:Tₖ] = outputs(g), r = resultIdx(d)

⟦D₁⟧⇐ᵥ :: ⟦Γ⟧ ⊢_v V₁ ⇐ ⟦A₁⟧  ...  ⟦Dₙ⟧⇐ᵥ :: ⟦Γ⟧ ⊢_v Vₙ ⇐ ⟦Aₙ⟧
⟦K⟧⇐ₚ :: ⟦Γ⟧,x₁:T₁,...,xₖ:Tₖ ⊢_p M_k ⇐ ⟦A⟧ & (d\e)
──────────────────────────────────────────────────────────────────────────────────────────────────────
⟦D⟧⇐ₚ :: ⟦Γ⟧ ⊢_p effectfulCall g [V₁,...,Vₙ] [x₁:T₁,...,xₖ:Tₖ] (assign x c(xᵣ) M_k)    where ⟦B⟧ ≤ ⟦Γ(x)⟧ ↦ c ⇐ ⟦A⟧ & e


D_body :: Γ,l ⊢_L body : A    K :: Γ ⊢_L rest : A
───────────────────────────────────────────────────
D :: Γ ⊢_L {body}ₗ; rest : A

        ↦

⟦D_body⟧⇐ₚ :: ⟦Γ⟧,l ⊢_p M_b ⇐ ⟦A⟧ & e    ⟦K⟧⇐ₚ :: ⟦Γ⟧ ⊢_p M_k ⇐ ⟦A⟧ & e
────────────────────────────────────────────────────────────────────────────────
⟦D⟧⇐ₚ :: ⟦Γ⟧ ⊢_p labeledBlock l M_b M_k ⇐ ⟦A⟧ & e


l ∈ Γ
─────────────────────
D :: Γ ⊢_L (exit l) : A

        ↦

⟦D⟧⇐ₚ :: ⟦Γ⟧ ⊢_p exit l ⇐ ⟦A⟧ & e


D_c :: Γ ⊢_L c : bool    D_b :: Γ ⊢_L body : A    K :: Γ ⊢_L rest : A
────────────────────────────────────────────────────────────────────────
D :: Γ ⊢_L (while c do body); rest : A

        ↦

⟦D_c⟧⇐ᵥ :: ⟦Γ⟧ ⊢_v V ⇐ bool    ⟦D_b⟧⇐ₚ :: ⟦Γ⟧ ⊢_p M_b ⇐ ⟦A⟧ & e    ⟦K⟧⇐ₚ :: ⟦Γ⟧ ⊢_p M_k ⇐ ⟦A⟧ & e
───────────────────────────────────────────────────────────────────────────────────────────────────────────
⟦D⟧⇐ₚ :: ⟦Γ⟧ ⊢_p whileLoop V M_b M_k ⇐ ⟦A⟧ & e


D_c :: Γ ⊢_L c : bool    K :: Γ ⊢_L rest : A
──────────────────────────────────────────────
D :: Γ ⊢_L (assume c); rest : A

        ↦

⟦D_c⟧⇐ᵥ :: ⟦Γ⟧ ⊢_v V ⇐ bool    ⟦K⟧⇐ₚ :: ⟦Γ⟧ ⊢_p M_k ⇐ ⟦A⟧ & e
────────────────────────────────────────────────────────────────────────
⟦D⟧⇐ₚ :: ⟦Γ⟧ ⊢_p assume V M_k ⇐ ⟦A⟧ & e


D_obj :: Γ ⊢_L obj : C    D_v :: Γ ⊢_L v : fieldType(C,f)    K :: Γ ⊢_L rest : A
────────────────────────────────────────────────────────────────────────────────────
D :: Γ ⊢_L (obj.f := v); rest : A

        ↦

⟦D_obj⟧⇐ᵥ :: ⟦Γ⟧ ⊢_v V_obj ⇐ Composite    ⟦D_v⟧⇐ᵥ :: ⟦Γ⟧ ⊢_v V_val ⇐ ⟦fieldType(C,f)⟧    ⟦K⟧⇐ₚ :: ⟦Γ⟧,$h:Heap ⊢_p M_k ⇐ ⟦A⟧ & e
──────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────
⟦D⟧⇐ₚ :: ⟦Γ⟧,$h:Heap ⊢_p varDecl $h Heap (updateField($heap, V_obj, $field.C.f, boxCtor(fieldType(C,f))(V_val))) M_k ⇐ ⟦A⟧ & e


D_r :: Γ ⊢_L root : Any    D_i :: Γ ⊢_L idx : Any    D_v :: Γ ⊢_L v : Any    K :: Γ ⊢_L rest : A
────────────────────────────────────────────────────────────────────────────────────────────────────
D :: Γ ⊢_L (root[idx] := v); rest : A

        ↦

⟦D_r⟧⇐ᵥ :: ⟦Γ⟧ ⊢_v V_r ⇐ Any    ⟦D_i⟧⇐ᵥ :: ⟦Γ⟧ ⊢_v V_i ⇐ Any    ⟦D_v⟧⇐ᵥ :: ⟦Γ⟧ ⊢_v V_v ⇐ Any    ⟦K⟧⇐ₚ :: ⟦Γ⟧ ⊢_p M_k ⇐ ⟦A⟧ & e
────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────
⟦D⟧⇐ₚ :: ⟦Γ⟧ ⊢_p assign root (staticCall Any_sets [V_i, V_r, V_v]) M_k ⇐ ⟦A⟧ & e


K :: Γ ⊢_L rest : A
────────────────────
D :: Γ ⊢_L ??; rest : A

        ↦

⟦K⟧⇐ₚ :: ⟦Γ⟧,$hv:Any ⊢_p M_k ⇐ ⟦A⟧ & e
────────────────────────────────────────────
⟦D⟧⇐ₚ :: ⟦Γ⟧,$hv:Any ⊢_p varDecl $hv Any none M_k ⇐ ⟦A⟧ & e


D_e :: Γ ⊢_L e : B    K :: Γ ⊢_L rest : A    e is not a call to g with procGrades[g] > pure
─────────────────────────────────────────────────────────────────────────────────────────
D :: Γ ⊢_L e; rest : A

        ↦

⟦K⟧⇐ₚ :: ⟦Γ⟧ ⊢_p M_k ⇐ ⟦A⟧ & e
──────────────────────────────────
⟦D⟧⇐ₚ :: ⟦Γ⟧ ⊢_p M_k ⇐ ⟦A⟧ & e    (value discarded)


D₁ :: Γ ⊢_L e₁ : A₁  ...  Dₙ :: Γ ⊢_L eₙ : Aₙ    K :: Γ ⊢_L rest : A    procGrades[g] = d > pure
──────────────────────────────────────────────────────────────────────────────────────────────────────
D :: Γ ⊢_L g(e₁,...,eₙ); rest : A    (expression as statement)

        ↦    let [x₁:T₁,...,xₖ:Tₖ] = outputs(g)

⟦D₁⟧⇐ᵥ :: ⟦Γ⟧ ⊢_v V₁ ⇐ ⟦A₁⟧  ...  ⟦Dₙ⟧⇐ᵥ :: ⟦Γ⟧ ⊢_v Vₙ ⇐ ⟦Aₙ⟧
⟦K⟧⇐ₚ :: ⟦Γ⟧,x₁:T₁,...,xₖ:Tₖ ⊢_p M_k ⇐ ⟦A⟧ & (d\e)
────────────────────────────────────────────────────────────────────────────────────────────
⟦D⟧⇐ₚ :: ⟦Γ⟧ ⊢_p effectfulCall g [V₁,...,Vₙ] [x₁:T₁,...,xₖ:Tₖ] M_k ⇐ ⟦A⟧ & e
```



### Projection

Map FGLProducer back to Laurel statements.

- `effectfulCall f args outputs body` → `[decl outputs; Assign [outputs] (StaticCall f args); body]`
- `assign x V body` → `[Assign [x] V; body]`
- `varDecl x T V body` → `[LocalVariable x T V; body]`
- Values map to their Laurel equivalents directly.


## Python Construct Coverage

Explicit accounting of what Translation handles, what it approximates,
and what it does not support.

**Fully handled (precise translation):**
- Literals (int, bool, str, None)
- Variables (identifiers, scope hoisting)
- Binary/comparison/boolean/unary operators (→ prelude StaticCalls)
- Function definitions (params, defaults, kwargs, return)
- Class definitions (fields, __init__, methods with self)
- Assignments (simple, augmented, annotated, tuple unpacking)
- Control flow (if/elif/else, while, for, break, continue)
- Return statements
- Assert/assume
- Try/except (labeled blocks + isError guards)
- Context managers (with/as)
- List/dict/tuple literals (→ ListAny_cons/DictStrAny_cons encoding)
- F-strings (→ to_string_any)
- Subscript read/write (→ Any_get/Any_sets)
- Slice notation (→ from_Slice)
- Module imports (→ qualified name resolution)
- Class instantiation (→ New + __init__)
- Method calls (→ qualified StaticCall with self)

**Approximated (Hole — sound but imprecise):**
- Unresolved names (not in Γ → nondeterministic Hole)
- Lambda expressions
- List/set/dict comprehensions
- Generator expressions
- Walrus operator (:=)
- Match statements
- Async constructs (async for, async with, await)
- Decorators
- Star expressions
- Float literals (represented as string — no real arithmetic)

**Not supported (Translation throws):**
- Chained comparisons (`a < b < c`)
- Multiple assignment targets (`x = y = 5`)


## Known Tech Debt

**Narrowing as pure function:** `Any_to_bool` etc. are modeled as pure (grade 1).
In Python, `__bool__` can have side effects. If needed later, narrowing becomes
grade > 1 and the coercion scheme changes.

**Instance procedures:** Methods emitted as top-level statics with `self` as first param.
`instanceProcedures` on CompositeType is empty.

**Prelude data encodings:** Lists/dicts are recursive ADTs (`ListAny_cons`/`DictStrAny_cons`).
Translation emits these via runtime constants (resolved `Laurel.Identifier` values
extracted from the runtime program), not via string literals.

**Elaboration constructs internal lookup from program declarations:** The Laurel AST
does not carry callee signatures on call-site nodes (`StaticCall` uses string names).
Elaboration builds an internal signature map from `program.staticProcedures` at startup.
Ideally, call sites would carry their callee's signature directly (no lookup needed),
but this requires extending the Laurel AST or metadata system.

**Multi-output forces err grade:** Translation declares `maybe_except : Error` on every
procedure. The `outputs.length > 1` heuristic in grade inference therefore always fires,
joining every user proc's grade with err. Architecturally, grade should come purely from
coinduction. In practice, Translation's output format forces err as minimum.

**Hole declarations collected post-hoc:** Architecture says `$hole_N` must be in Γ for
the staticCall rule. Implementation emits the staticCall without the function in Γ (using
the unknown-callee fallback) and collects hole names for declaration in the output program
afterward — same pattern as box constructors.

**Entry point extends env with outputs:** `fullElaborate` extends Γ with both inputs AND
outputs (`LaurelResult`, `maybe_except`) before elaboration. Necessary because Translation
assigns to output variables. Architecture's entry point description only mentions params.


## Current Status (2026-05-14)

### Implementation status

**Resolution:** Complete for supported constructs. Phase distinction enforced:
all types are Python-level (`PythonIdentifier` newtype, `FuncSig` with
`FuncParams`/`ParamList`). Accessor functions produce Laurel identifiers.
Ctx keyed by `PythonIdentifier` (no fabricated string keys). Method
resolution via spine-based `typeOfExpr`. `with` statement resolves
`__enter__`/`__exit__` via `NodeInfo.withCtx`.

**Translation:** Writer monad (`TransM` = `BaseM` + statement output).
`tell` emits statements, `collect = lift ∘ runWriterT` captures them at
block boundaries. `translateExpr` returns `TransM StmtExprMd` — may emit
prefix statements (for `classNew` in expression position). Operators use
`matchArgs` (correct params in sig). No coercion insertion. No string
fabrication. Params get `$in_` prefix on inputs; body uses mutable locals
initialized from inputs.

**Elaboration:** Hole handling bug: `checkAssign` at line 674 generates
`hole$N` names but does NOT add them to `usedHoles`. The `synthValue`
handler (line 392) does add to `usedHoles`. This inconsistency causes
hole declarations to be missing from the output program when holes appear
in assignment value position.

### Remaining issues (4 test regressions)

1. **Imported class fields not resolved** (`test_foo_client_folder`,
   `test_invalid_client_type`): `from test_helper import ...` registers as
   `CtxEntry.unresolved`. Classes defined in imported modules have no fields
   in Resolution's ctx. Needs spec integration or cross-module resolution.

2. **Hole not collected in assign position** (`test_multiple_except`):
   Elaboration's `checkAssign` handler for `.Hole true` (line 674 in
   Elaborate.lean) generates `hole$N` via `freshVar` but does NOT add to
   `usedHoles`. The declaration is never emitted. Root cause: holes are
   handled ad-hoc across multiple code paths instead of as a systematic
   effect. Proper fix: treat nondeterminism as a graded effect with a
   monoidal element that collects hole nominals.

3. **Duplicate hole names across specs** (`test_procedure_in_assert`):
   Multi-spec pipeline runs Translation/Elaboration per spec with fresh
   counters. Multiple specs produce `havoc$0`. No `.py` source for this test.

4. **`test_foo_client_folder` / `test_invalid_client_type`**: These also
   fail due to `$field.__name__` — a Python dunder attribute on a type object
   that's accessed via imported code. Resolution doesn't model type objects.

### Key Implementation Decisions

- `pythonTypeToHighType` maps Union/generic types → `TCore "Any"`
- Translation emits Hole for unresolved names (no undefined StaticCalls)
- `FuncSig.matchArgs` is a zip-fold: positional first, then kwarg/default
- `instanceProcedures` on CompositeType is empty (methods as top-level statics)
- Writer monad: `tell` for statements, `collect` for block scoping
- `FuncParams.instance` separates receiver from other params
- Operator sigs have correct arity (2 for binary, 1 for unary)
- `PythonIdentifier.toLaurel` is identity; `FuncSig.laurelName` applies mapping
- Params: inputs named `$in_X`, body gets `LocalVariable X := $in_X`
- Loop labels use push/pop on state (should be reader monad — tech debt)
- FunctionDef/ClassDef NOT included in computeLocals (they're declarations)


## Success Criteria

1. All 54 in-tree tests pass.
2. Translation is a structural recursion on `NodeInfo` — no string fabrication.
3. Elaboration is separate — translation emits no casts or grades.
4. Types from annotations — `Any` only when annotation absent.
5. One file per pass.
6. Implementation reads as transcription of the typing rules.
7. Translation cannot produce ill-scoped names (enforced by data flow from Resolution).




## Files

```
Resolution.lean        -- Disambiguate + scope: Python AST → ResolvedPythonProgram
Translation.lean       -- Structural recursion: ResolvedPythonProgram → Laurel.Program
Elaborate.lean         -- Graded bidirectional elaboration: Laurel → GFGL → Laurel
PySpecPipeline.lean    -- Wire passes, CLI
```




## References

- **Levy** (2003). *Call-By-Push-Value.* Value/Producer, Jump-With-Argument.
- **Egger, Møgelberg, Staton** (2014). "Linear Usage of State."
- **McDermott** (2025). "Grading call-by-push-value."
- **Dunfield & Krishnaswami** (2021). "Bidirectional Typing."
