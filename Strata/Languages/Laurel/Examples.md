# Writing and Running Laurel — A Practical Guide

Each example below is annotated with the corresponding `HighType` / `StmtExpr` /
`TypeDefinition` constructors from `Laurel.lean`, so you can see how surface
syntax maps to the AST.

Annotation convention:
- `// ⟶ Xyz` marks the constructor the preceding construct builds
- `// :: T` gives the `HighType` of an expression / declaration

## Is there a .laurel file format?

Two options, both used in this repo:

- Standalone text files: `.lr.st` extension (found in `StrataTest/Languages/Laurel/tests/*.lr.st`)
- Raw strings inside Lean test files: the bulk of the examples in
  `StrataTest/Languages/Laurel/Examples/` use this form — you see a string
  literal `r"..."` with Laurel source inside, then a `#eval` that runs it
  through the pipeline

For writing normal Laurel, use `.lr.st`.

## The syntax, by concrete example

### A minimal program — assertion that should hold

```laurel
procedure main()                   // ⟶ Procedure { name, inputs=[], outputs=[] }
  opaque                           // ⟶ Body.Opaque
{                                  // ⟶ StmtExpr.Block
  var x: int := 5;                 // ⟶ Assign [Variable.Declare ⟨x, TInt⟩] (LiteralInt 5)
  var y: int := 3;                 //     int :: HighType.TInt
  var sum: int := x + y;           // RHS: PrimitiveOp .Add [Var (Local x), Var (Local y)]
  assert sum == 8                  // ⟶ StmtExpr.Assert (PrimitiveOp .Eq [...])
};
```

### Preconditions and postconditions

```laurel
procedure divide(x: int, y: int)   // inputs : List Parameter, each type :: TInt
  returns (r: int)                 // outputs: List Parameter
  requires y != 0                  // ⟶ preconditions : List Condition
  opaque                           // ⟶ Body.Opaque
  ensures r * y == x               // ⟶ postconditions inside Body.Opaque
{
  r := x / y                       // ⟶ Assign [Local r] (PrimitiveOp .Div [...])
};

procedure caller() opaque {
  var q: int := divide(10, 2);     // RHS ⟶ StmtExpr.StaticCall "divide" [...]
  assert q == 5;

  var bad: int := divide(10, 0)
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: precondition does not hold
};
```

### Functions (functional subset — no mutation, no loops)

```laurel
function square(x: int): int {     // ⟶ Procedure { isFunctional := true }
  x * x                            // body :: TInt (type of last stmt in Block)
};

function abs(x: int): int {
  if x >= 0 then x else -x         // ⟶ StmtExpr.IfThenElse (cond :: TBool) thenBr elseBr
};
```

### Composite types (class-like, reference semantics)

```laurel
composite Container {              // ⟶ TypeDefinition.Composite (CompositeType …)
  var intValue: int                // ⟶ Field { isMutable := true, type :: TInt }
  val label: string                // ⟶ Field { isMutable := false, type :: TString }
}

procedure use() opaque {
  var c: Container := new Container;  // RHS ⟶ StmtExpr.New "Container" :: UserDefined "Container"
  c#intValue := 42;                // ⟶ Assign [Variable.Field (Var (Local c)) "intValue"] (LiteralInt 42)
  assert c#intValue == 42          //      Var (Field (Var (Local c)) "intValue") :: TInt
};
```

### Inheritance

```laurel
composite Animal { var name: string }               // Composite.extending = []
composite Dog extends Animal { var breed: string }  // Composite.extending = ["Animal"]

procedure test(d: Dog) opaque {    // d :: UserDefined "Dog"
  assert d is Animal;              // ⟶ StmtExpr.IsType d (UserDefined "Animal") :: TBool
  var a: Animal := d as Animal     // ⟶ StmtExpr.AsType d (UserDefined "Animal") :: UserDefined "Animal"
};
```

### Datatypes

```laurel
datatype Color {                   // ⟶ TypeDefinition.Datatype (DatatypeDefinition …)
  Red(),                           // ⟶ DatatypeConstructor { name := "Red", args := [] }
  Green(),
  Blue()
}

procedure useColor(c: Color) opaque {        // c :: UserDefined "Color"
  if Color..isRed(c) then                    // "Color..isRed" ⟶ tester, returns TBool
    assert !Color..isBlue(c)                 // PrimitiveOp .Not [StaticCall "Color..isBlue" [c]]
};
```

### Constrained (refinement) types

```laurel
constrained nat = x: int where x >= 0 witness 0
//  ⟶ TypeDefinition.Constrained
//      ConstrainedType { name := "nat", base :: TInt,
//                        valueName := "x", constraint := x >= 0, witness := 0 }

constrained posnat = x: nat where x != 0 witness 1
//  base :: UserDefined "nat"   — nested constrained (flattened by ConstrainedTypeElim)

procedure takesNat(n: nat) opaque {    // n :: UserDefined "nat"
  assert n >= 0                        //   — body automatically gets `requires nat$constraint(n)` injected
};

procedure caller() opaque {
  takesNat(3);                         // ok
  takesNat(-1)
//^^^^^^^^^^^ error: precondition does not hold
};
```

### Loops with invariants

```laurel
procedure sumUpTo(n: int) returns (r: int)
  requires n >= 0
  opaque
  ensures r == (n * (n + 1)) / 2
{
  var i: int := 0;
  r := 0;
  while i < n                                       // ⟶ StmtExpr.While cond invs dec body
    invariant 0 <= i && i <= n                      //   invariants : List StmtExprMd
    invariant r == (i * (i + 1)) / 2                //   each invariant :: TBool
    decreases n - i                                 //   decreases   : Option StmtExprMd (termination measure)
  {                                                 //   body :: TVoid (it's a Block)
    i := i + 1;
    r := r + i
  }
};
```

### Quantifiers

```laurel
procedure test() opaque {
  var b: bool := forall(x: int) => x + 1 > x;   // ⟶ StmtExpr.Quantifier .Forall ⟨x, TInt⟩ none body
  assert b;                                      //     Quantifier :: TBool (always)

  var e: bool := exists(n: nat) => n == 42;      // ⟶ Quantifier .Exists ⟨n, UserDefined "nat"⟩ none body
  assert e                                       //     — nat$constraint(n) is injected into body
};
```

### Multiple return values

```laurel
procedure divmod(x: int, y: int) returns (q: int, r: int)
  requires y > 0
  opaque
  ensures x == q * y + r && 0 <= r && r < y;
// call type :: MultiValuedExpr [TInt, TInt]     — synthetic type used for arity checking

procedure use() opaque {
  assign var q: int, var r: int := divmod(10, 3);
  //  ⟶ Assign [Declare ⟨q, TInt⟩, Declare ⟨r, TInt⟩] (StaticCall "divmod" [LiteralInt 10, LiteralInt 3])
  //  — Resolution checks target-count (2) matches MultiValuedExpr arity (2)
  assert q == 3;
  assert r == 1
};
```

### Cheat-sheet: surface syntax ⟷ AST constructor

| Surface | `HighType` / `StmtExpr` |
|---|---|
| `int`, `bool`, `real`, `float64`, `string` | `TInt`, `TBool`, `TReal`, `TFloat64`, `TString` |
| `Foo` (user-defined name) | `UserDefined "Foo"` |
| `42` / `true` / `"s"` / `3.14` | `LiteralInt` / `LiteralBool` / `LiteralString` / `LiteralDecimal` |
| `x` (identifier) | `Var (Variable.Local …)` |
| `c#f` (field read) | `Var (Variable.Field target "f")` |
| `var x: T := e` | `Assign [Variable.Declare ⟨x, T⟩] e` |
| `x := e` | `Assign [Variable.Local x] e` |
| `c#f := e` | `Assign [Variable.Field target "f"] e` |
| `if c then a else b` | `IfThenElse cond thenBr (some elseBr)` |
| `while c inv … dec …  { … }` | `While cond invariants decreases body` |
| `return e` | `Return (some e)` |
| `{ … ; … }` | `Block stmts label` |
| `e1 + e2`, `==`, `&&`, `!`, ... | `PrimitiveOp op args` |
| `foo(a, b)` | `StaticCall "foo" [a, b]` |
| `obj..m(a)` | `InstanceCall obj "m" [a]` |
| `new Foo` | `New "Foo"` :: `UserDefined "Foo"` |
| `x is T` | `IsType x T` :: `TBool` |
| `x as T` | `AsType x T` :: `T` |
| `forall(x: T) => P` | `Quantifier .Forall ⟨x, T⟩ none P` :: `TBool` |
| `exists(x: T) => P` | `Quantifier .Exists ⟨x, T⟩ none P` :: `TBool` |
| `assert e` / `assume e` | `Assert ⟨e, summary?⟩` / `Assume e` |
| `old(e)` / `fresh(e)` | `Old e` / `Fresh e` |

| Surface | `TypeDefinition` |
|---|---|
| `composite Foo { … }` | `TypeDefinition.Composite (CompositeType …)` |
| `composite Foo extends Bar { … }` | `CompositeType.extending := ["Bar"]` |
| `constrained N = x: T where P witness w` | `TypeDefinition.Constrained (ConstrainedType …)` |
| `datatype D { C1(…), C2(…) }` | `TypeDefinition.Datatype (DatatypeDefinition …)` |
| `type Alias = T` | `TypeDefinition.Alias (TypeAlias …)` (eliminated early) |

### Key syntactic quirks worth remembering

- Top-level declarations end with `;` (even procedures)
- Statements inside a block are separated by `;`, but no trailing `;` before the closing brace
- Procedure bodies need `opaque` or `transparent`; functions don't
- Field access on composites uses `#`, not `.`
- Instance methods use `..`: `obj..method(args)`, tester `Color..isRed(c)`
- `var` declares a variable (optionally with `:= init`); `val` declares an immutable field on a composite
- `//  ^^^ error: ...` comments are test harness annotations — they assert that the tool reports that error at that position

## How to run a Laurel file

The strata executable (built from `StrataMain.lean`) has four Laurel subcommands:

```bash
# Parse-only — fast syntax check
strata laurelParse myfile.lr.st

# Parse + resolve + translate to Core + verify via SMT
strata laurelAnalyze myfile.lr.st

# Show the Core program that Laurel translates into
strata laurelToCore myfile.lr.st

# Read Laurel Ion from stdin (binary format)
strata laurelPrint < myfile.lr.st.ion
```

`laurelAnalyze` accepts the full verification-option set (`strata laurelAnalyze --help`): `--solver`, `--solver-timeout`, `--check-mode`, `--vc-directory`, `--no-solve`, `--sarif`, `--stop-on-first-error`, etc.

Typical local flow:

```bash
# Build the tool (from repo root)
lake build strata

# Run it
./.lake/build/bin/strata laurelAnalyze path/to/file.lr.st
```

Expected output on success:

```
==== RESULTS ====
<label>: ok verified
...
```

On failure, per-VC lines show which assertion couldn't be proved, with file locations.

## How to try one without the CLI — via the test harness

If you don't want to build, the fastest iteration loop is copying an existing example. In any `.lean` file under `StrataTest/Languages/Laurel/Examples/`:

```lean
import StrataTest.Util.TestDiagnostics
import StrataTest.Languages.Laurel.TestExamples

open StrataTest.Util
namespace Strata.Laurel

def program := r"
procedure foo() opaque {
  assert 1 + 1 == 2
};
"

#guard_msgs(drop info, error) in
#eval testInputWithOffset "Foo" program 14 processLaurelFile
```

Then `lake build <your.module>` (or open in Lean in VSCode) runs the pipeline and compares diagnostics against the `//  ^^^ error: ...` annotations inline in your program string.

## Where to browse more examples

Ordered roughly from simplest to most advanced:

- `Examples/Fundamentals/T1_AssertFalse.lean` — the basics
- `Examples/Fundamentals/T3_ControlFlow.lean` — if/while
- `Examples/Fundamentals/T5_ProcedureCalls.lean` — calls, return values
- `Examples/Fundamentals/T6_Preconditions.lean` — requires
- `Examples/Fundamentals/T8_Postconditions.lean` — ensures
- `Examples/Fundamentals/T10_ConstrainedTypes.lean` — refinement types
- `Examples/Fundamentals/T13_WhileLoops.lean` — invariants, decreases
- `Examples/Fundamentals/T14_Quantifiers.lean` — forall / exists
- `Examples/Objects/T1_MutableFields.lean` — composites, fields, aliasing
- `Examples/Objects/T2_ModifiesClauses.lean` — framing
- `Examples/Objects/T5_inheritance.lean` — extends, is, as
- `Examples/Objects/T6_Datatypes.lean` — algebraic datatypes

Each file is a self-contained working program, so you can copy-paste the `r"..."` contents into a `.lr.st` file and run `strata laurelAnalyze`.

## Suggested starter file

Save this as `hello.lr.st`:

```laurel
constrained nat = x: int where x >= 0 witness 0
// ⟶ TypeDefinition.Constrained (ConstrainedType …)

function factorial(n: nat): int    // n :: UserDefined "nat"; return :: TInt
  decreases n
{
  if n == 0 then 1 else n * factorial(n - 1)
  // IfThenElse (PrimitiveOp .Eq [...]) (LiteralInt 1) (PrimitiveOp .Mul [..., StaticCall "factorial" [...]])
};

procedure main() opaque {
  assert factorial(0) == 1;
  assert factorial(5) == 120
};
```

Then:

```bash
lake build strata
./.lake/build/bin/strata laurelAnalyze hello.lr.st
```

You should see two passed goals.
