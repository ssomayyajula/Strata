# Writing and Running Laurel — A Practical Guide

## Is there a .laurel file format?

Two options, both used in this repo:

- Standalone text files: `.lr.st` extension (found in `StrataTest/Languages/Laurel/tests/*.lr.st`)
- Raw strings inside Lean test files: the bulk of the examples in `StrataTest/Languages/Laurel/Examples/` use this form — you see a string literal `r"..."` with Laurel source inside, then a `#eval` that
runs it through the pipeline

For writing normal Laurel, use `.lr.st`.

## The syntax, by concrete example

A minimal program — assertion that should hold

```laurel
procedure main()
opaque
{
var x: int := 5;
var y: int := 3;
var sum: int := x + y;
assert sum == 8
};
```

### Preconditions and postconditions

```laurel
procedure divide(x: int, y: int) returns (r: int)
requires y != 0
opaque
ensures r * y == x
{
r := x / y
};
```

```laurel
procedure caller() opaque {
var q: int := divide(10, 2);
assert q == 5;
```

```laurel
var bad: int := divide(10, 0)
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: precondition does not hold
};
```

### Functions (functional subset — no mutation, no loops)

```laurel
function square(x: int): int {
x * x
};
```

```laurel
function abs(x: int): int {
if x >= 0 then x else -x
};
```

### Composite types (class-like, reference semantics)

```laurel
composite Container {
var intValue: int     // var = mutable
val label: string     // val = immutable (idiomatic form — see T4_ImmutableFields)
}
```

```laurel
procedure use() opaque {
var c: Container := new Container;
c#intValue := 42;           // # is field access/assign on composites
assert c#intValue == 42
};
```

### Inheritance

```laurel
composite Animal { var name: string }
composite Dog extends Animal { var breed: string }

procedure test(d: Dog) opaque {
assert d is Animal;         // runtime type test
var a: Animal := d as Animal
};
```

### Datatypes

```laurel
datatype Color {
Red(),
Green(),
Blue()
}

procedure useColor(c: Color) opaque {
if Color..isRed(c) then
  assert !Color..isBlue(c)
};
```

### Constrained (refinement) types

```laurel
constrained nat = x: int where x >= 0 witness 0
constrained posnat = x: nat where x != 0 witness 1

procedure takesNat(n: nat) opaque {
assert n >= 0             // free from the refinement
};

procedure caller() opaque {
takesNat(3);              // ok
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
while i < n
  invariant 0 <= i && i <= n
  invariant r == (i * (i + 1)) / 2
  decreases n - i
{
  i := i + 1;
  r := r + i
}
};
```

### Quantifiers

```laurel
procedure test() opaque {
var b: bool := forall(x: int) => x + 1 > x;
assert b;

var e: bool := exists(n: nat) => n == 42;
assert e
};
```

### Multiple return values

```laurel
procedure divmod(x: int, y: int) returns (q: int, r: int)
requires y > 0
opaque
ensures x == q * y + r && 0 <= r && r < y;

procedure use() opaque {
assign var q: int, var r: int := divmod(10, 3);
assert q == 3;
assert r == 1
};
```

### Key syntactic quirks worth remembering

- Top-level declarations end with `;` (even procedures)
- Statements inside a block are separated by `;`, but no trailing `;` before the closing brace
- Procedure bodies need `opaque` or `transparent`; functions don't
- Field access on composites uses `#`, not `.`
- Instance methods use `..: obj..method(args), tester Color..isRed(c)`
- `var` declares a variable (optionally with `:= init`); `val` declares an immutable field on a composite
-  `//  ^^^ error: ...` comments are test harness annotations — they assert that the tool reports that error at that position

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
==== RESULTS ====
<label>: ok verified
...

On failure, per-VC lines show which assertion couldn't be proved, with file locations.

## How to try one without the CLI — via the test harness

If you don't want to build, the fastest iteration loop is copying an existing example. In any `.lean` file under `StrataTest/Languages/Laurel/Examples/`:

```laurel
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

function factorial(n: nat): int
decreases n
{
if n == 0 then 1 else n * factorial(n - 1)
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
