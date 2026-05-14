/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import VersoManual

import Strata.Languages.Laurel.Laurel
import Strata.Languages.Laurel.LaurelTypes
import Strata.Languages.Laurel.LaurelToCoreTranslator
import Strata.Languages.Laurel.HeapParameterization
import Strata.Languages.Laurel.LiftImperativeExpressions
import Strata.Languages.Laurel.ModifiesClauses

open Strata.Laurel

-- This gets access to most of the manual genre
open Verso.Genre Manual

-- This gets access to Lean code that's in code blocks, elaborated in the same process and
-- environment as Verso
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "The Laurel Language" =>
%%%
shortTitle := "Laurel"
%%%

# Introduction

Laurel is an intermediate verification language designed to serve as a target for popular
garbage-collected languages that include imperative features, such as Java, Python, and
JavaScript. Laurel tries to include any features that are common to those three languages.

Laurel enables doing various forms of verification:
- Deductive verification
- (WIP) Model checking
- (WIP) Property based testing
- (WIP) Data-flow analysis

Here are some Laurel language features that are shared between the source languages:
- Statements such as loops and return statements
- Mutation of variables, including in expressions
- Reading and writing of fields of references
- Object oriented concepts such as inheritance, type checking, up and down casting and
  dynamic dispatch
- (WIP) Error handling via exceptions
- (WIP) Higher-order procedures and procedure types
- (WIP) Parametric polymorphism

On top of the above features, Laurel adds features that are useful specifically for verification:
- Assert and assume statements
- Loop invariants
- Pre and postconditions for procedures
- Modifies and reads clauses for procedures
- (WIP) Decreases clauses for procedures and loops
- (WIP) Immutable fields and constructors that support assigning to them
- (WIP) Constrained types
- (WIP) Type invariants
- Forall and exists expressions
- (WIP) Old and fresh expressions
- Unbounded integer and real types
- To be designed constructs for supporting proof writing

A peculiar choice of Laurel is that it does not require imperative code to be encapsulated
using a functional specification. A reason for this is that sometimes the imperative code is
as readable as the functional specification. For example:
```
procedure increment(counter: Counter)
  // In Laurel, this ensures clause can be left out
  ensures counter.value == old(counter.value) + 1
{
  counter.value := counter.value + 1;
};
```

## Implementation Choices

A design choice that impacts the implementation of Laurel is that statements and expressions
share a single implementation type, the StmtExpr. This reduces duplication for constructs
like conditionals and variable declarations. Each StmtExpr has a user facing type, which for
statement-like constructs could be void.

# Types

Laurel's type system includes primitive types, collection types, and user-defined types.

## Primitive Types

{docstring Strata.Laurel.HighType}

## User-Defined Types

User-defined types come in two categories: composite types and constrained types.

Composite types have fields and procedures, and may extend other composite types. Fields
declare whether they are mutable and specify their type.

{docstring Strata.Laurel.CompositeType}

{docstring Strata.Laurel.Field}

Constrained types are defined by a base type and a constraint over the values of the base
type. Algebraic datatypes can be encoded using composite and constrained types.

{docstring Strata.Laurel.ConstrainedType}

{docstring Strata.Laurel.TypeDefinition}

# Expressions and Statements

Laurel uses a unified `StmtExpr` type that contains both expression-like and statement-like
constructs. This avoids duplication of shared concepts such as conditionals and variable
declarations.

## Operations

{docstring Strata.Laurel.Operation}

## The StmtExpr Type

{docstring Strata.Laurel.StmtExpr}

## Metadata

All AST nodes can carry metadata via the `WithMetadata` wrapper.

{docstring Strata.Laurel.WithMetadata}

# Procedures

Procedures are the main unit of specification and verification in Laurel.

{docstring Strata.Laurel.Procedure}

{docstring Strata.Laurel.Parameter}

{docstring Strata.Laurel.Determinism}

{docstring Strata.Laurel.Body}

# Programs

A Laurel program consists of procedures, global variables, type definitions, and constants.

{docstring Strata.Laurel.Program}

# Type checking

Type checking runs as a standalone pass over a fully resolved Laurel `Program`,
between resolution and the translation pipeline. It consumes the `SemanticModel`
produced by resolution and emits a list of `DiagnosticModel`s; an empty list
means the program is well typed.

A standalone pass — rather than rules folded into `Resolution.lean` — keeps each
phase single-purpose: resolution decides *what name refers to what*, type
checking decides *whether the uses are well typed*. The same split is already
visible in `InferHoleTypes` and `validateDiamondFieldAccesses`, both of which
run post-resolution and consume `SemanticModel`.

## Architecture

The pass lives in `Strata.Languages.Laurel.TypeCheck` and exposes a single
entry point `typeCheck : SemanticModel → Program → Array DiagnosticModel`.
Internally it walks each `StmtExpr`, computes its type via
`LaurelTypes.computeExprType`, and checks the local shape constraints required
by the construct (e.g. an `if` condition must be `TBool`).

Reusable, monad-free type queries (`computeExprType`, future subtype/LUB
helpers) live in `LaurelTypes.lean` so other passes can share them. The
traversal, monadic state, and diagnostic emission live in `TypeCheck.lean`.

## Rules

The rules below are the *minimum* set the first iteration aims to enforce.
Each rule is local and synthesised from already-resolved types — no inference.

- **Branch conditions.** The condition of `IfThenElse`, `While`, `Assert`,
  and `Assume` must have type `TBool`.
- **Loop annotations.** `While` invariants must be `TBool`; the optional
  `decreases` measure must be `TInt`.
- **Primitive operators.** Each `PrimitiveOp` constrains its operands by
  category:
  - `And`, `Or`, `Not`, `Implies`, `AndThen`, `OrElse` require `TBool`
    operands.
  - `Neg`, `Add`, `Sub`, `Mul`, `Div`, `Mod`, `DivT`, `ModT`, `Lt`, `Leq`,
    `Gt`, `Geq` require numeric operands (`TInt`, `TReal`, `TFloat64`), with
    both operands of the same numeric type.
  - `StrConcat` requires `TString` operands.
  - `Eq`, `Neq` require operands with compatible types; the diagnostic for
    incompatible operands is symmetric (neither side is framed as "wrong").
- **Calls.** `StaticCall` and `InstanceCall` must match the callee's arity,
  and each argument's type must be assignable to the corresponding parameter
  type. For `InstanceCall`, the receiver fills the `self` slot and is checked
  separately.
- **Assignment.** `Assign targets value`: the count of targets must match the
  arity of `value` (1 for ordinary expressions, *n* for an *n*-output
  procedure call), and each target's declared type must accept the value's
  type.
- **Local variables.** A `LocalVariable` with an initialiser checks the
  initialiser's type against the declared type.
- **Returns.** A `Return` value's type must be assignable to the enclosing
  procedure's declared output type.
- **Quantifiers.** The body of `Forall` / `Exists` must be `TBool`.
- **Type tests.** `IsType` produces `TBool`; `AsType` produces the named
  type. No check is performed that the cast is sound at compile time.
- **Functional procedures.** A procedure marked `isFunctional` with a
  `Transparent` body has its body type checked against its declared output
  type.

`TVoid` and `Unknown` are *cascade suppressors*: when any operand of a check
has type `Unknown` no new diagnostic is emitted at the current level, and
checks that don't apply to statement-shaped expressions silently accept
`TVoid`. This keeps a single error from producing dozens of follow-on noise.

## Roadmap

Items deferred from the first iteration, in rough order of priority:

1. **Constrained types in boolean / numeric position.** Today any
   `UserDefined` is permissively accepted by the boolean and numeric checks;
   only `ConstrainedType` whose base is `TBool` (resp. numeric) should pass.
2. **Composite subtyping.** `var x: Dog := new Cat` is silently accepted.
   Wiring `computeAncestors` (already used by `validateDiamondFieldAccesses`)
   into the assignability check closes this gap. The associated regression
   test lives as a "no diagnostic today" pin so that adding subtyping flips
   it from passing to correctly rejecting.
3. **Generic type arguments.** `Applied`, `TSet`, `TMap` payload types are
   currently checked structurally without parameter substitution; extending
   to a substitution-aware check unlocks polymorphic procedures.
4. **Heap-relevant operations.** `New`, `Old`, `Fresh`, `ContractOf`,
   `Assigned` currently pass through with no extra checks beyond their
   children. Each has a small set of constraints (e.g. `Fresh` only on
   impure composite types) worth enforcing.
5. **Operator overload table.** Today numeric operators require homogenous
   operands; once Laurel grows mixed-numeric coercions an overload table
   replaces the per-operator `match`.

# Translation Pipeline

Laurel programs are verified by translating them to Strata Core and then invoking the Core
verification pipeline. The translation involves several passes, each transforming the Laurel
program before the final conversion to Core.

## Heap Parameterization

The heap parameterization pass transforms procedures that interact with the heap by adding
explicit heap parameters. The heap is modeled as `Map Composite (Map Field Box)`, where
`Box` is a tagged union with constructors for each primitive type.

Procedures that write the heap receive both an input and output heap parameter. Procedures
that only read the heap receive an input heap parameter. Field reads and writes are rewritten
to use `readField` and `updateField` functions.

## Modifies Clauses

The modifies clause transformation translates modifies clauses into additional ensures
clauses. The modifies clause of a procedure is translated into a quantified assertion that
states that objects not mentioned in the modifies clause have their field values preserved
between the input and output heap.

## Lifting Expression Assignments

The expression assignment lifting pass transforms assignments that appear in expression
contexts into preceding statements. This is necessary because Strata Core does not support
assignments within expressions.

## Translation to Core

The final translation converts Laurel types, expressions, statements, and procedures into
their Strata Core equivalents. Procedures with bodies that only have constructs supported by
Core expressions are translated to a Core function, while other procedures become Core
procedures.
