/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import VersoManual

import Strata.Languages.Laurel.Laurel
import Strata.Languages.Laurel.LaurelTypes
import Strata.Languages.Laurel.Resolution
import Strata.Languages.Laurel.TypeCheck
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

Type checking runs as a standalone pass over a fully resolved
{name Strata.Laurel.Program}`Program`, between resolution and the translation
pipeline. It consumes the {name Strata.Laurel.SemanticModel}`SemanticModel`
produced by resolution and emits a list of `DiagnosticModel`s; an empty list
means the program is well typed.

A standalone pass — rather than rules folded into
{name Strata.Laurel.resolve}`Resolution.lean` — keeps each phase
single-purpose: resolution decides *what name refers to what*, type checking
decides *whether the uses are well typed*. The same split is already visible
in {name Strata.Laurel.inferHoleTypes}`InferHoleTypes` and
{name Strata.Laurel.validateDiamondFieldAccesses}`validateDiamondFieldAccesses`,
both of which run post-resolution and consume
{name Strata.Laurel.SemanticModel}`SemanticModel`.

## Architecture

The pass lives in `Strata.Languages.Laurel.TypeCheck` and exposes a single
entry point {name Strata.Laurel.typeCheck}`typeCheck`:

{docstring Strata.Laurel.typeCheck}

Internally it walks each {name Strata.Laurel.StmtExpr}`StmtExpr`, computes
its type via {name Strata.Laurel.computeExprType}`computeExprType`, and
checks the local shape constraints required by the construct (e.g. an `if`
condition must be {name Strata.Laurel.HighType.TBool}`TBool`).

Reusable, monad-free type queries
({name Strata.Laurel.computeExprType}`computeExprType`, future subtype/LUB
helpers) live in `LaurelTypes.lean` so other passes can share them. The
traversal, monadic state, and diagnostic emission live in `TypeCheck.lean`.

The traversal threads {name Strata.Laurel.TypeCheckState}`TypeCheckState`,
which carries the resolution model, the output type of the procedure
currently being checked, and the diagnostics accumulated so far:

{docstring Strata.Laurel.TypeCheckState}

Errors are categorised up-front via {name Strata.Laurel.TypeError}`TypeError`
so that filtering and tests don't depend on message strings:

{docstring Strata.Laurel.TypeError}

## Rules

The rules below are the *minimum* set the first iteration aims to enforce.
Each rule is local and synthesised from already-resolved types — no inference.

The judgement `Γ ⊢ e : τ` reads "under semantic model `Γ`, expression `e` has
type `τ`". `Γ` carries the resolved scope produced by the resolution pass;
for the rules in this document, treat it as a partial map from
{name Strata.Laurel.Identifier}`Identifier` to
{name Strata.Laurel.HighType}`HighType`, with `Γ(x)` denoting the type bound
to `x`. The auxiliary judgement `τ₁ ≼ τ₂` reads "`τ₁` is assignable to
`τ₂`"; in the first iteration it is type equality, with the gaps captured in
the roadmap. The compatibility predicate `τ ~ τ'` used by symmetric
operators holds when either `τ ≼ τ'` or `τ' ≼ τ`.

### Literals and variables

Literals synthesise their canonical type, and variables look up their type in
the resolved scope.

```
─────────────────── (T-Int)        ─────────────────── (T-Bool)
  Γ ⊢ LiteralInt n : TInt            Γ ⊢ LiteralBool b : TBool

────────────────────────── (T-Str)    ──────────────────────────── (T-Dec)
  Γ ⊢ LiteralString s : TString         Γ ⊢ LiteralDecimal d : TReal


      Γ(x) = τ
─────────────────────── (T-Var)
  Γ ⊢ Identifier x : τ
```

### Control flow

{name Strata.Laurel.StmtExpr.IfThenElse}`IfThenElse` used as an expression
requires both branches to agree; used as a statement (no `else`) it produces
{name Strata.Laurel.HighType.TVoid}`TVoid`.
{name Strata.Laurel.StmtExpr.While}`While`,
{name Strata.Laurel.StmtExpr.Assert}`Assert`, and
{name Strata.Laurel.StmtExpr.Assume}`Assume` all demand a boolean condition;
loop invariants are also boolean and the optional `decreases` measure must
be {name Strata.Laurel.HighType.TInt}`TInt`.

```
  Γ ⊢ cond : TBool      Γ ⊢ thn : τ      Γ ⊢ els : τ
─────────────────────────────────────────────────────── (T-If)
        Γ ⊢ IfThenElse cond thn (some els) : τ


  Γ ⊢ cond : TBool      Γ ⊢ thn : τ
──────────────────────────────────────── (T-IfStmt)
  Γ ⊢ IfThenElse cond thn none : TVoid


  Γ ⊢ cond : TBool
  Γ ⊢ invᵢ : TBool   for each invariant invᵢ
  Γ ⊢ dec  : TInt    if dec is present
  Γ ⊢ body : _
─────────────────────────────────────────────── (T-While)
  Γ ⊢ While cond invs dec body : TVoid


  Γ ⊢ cond : TBool                       Γ ⊢ cond : TBool
─────────────────────────── (T-Assert)  ─────────────────────────── (T-Assume)
  Γ ⊢ Assert cond : TVoid                  Γ ⊢ Assume cond : TVoid
```

### Primitive operators

The {name Strata.Laurel.Operation}`Operation` cases partition into four
families. Logical operators (`And`, `Or`, `Implies`, `AndThen`, `OrElse`,
`Not`) take and return {name Strata.Laurel.HighType.TBool}`TBool`.
Arithmetic operators (`Add`, `Sub`, `Mul`, `Div`, `Mod`, `DivT`, `ModT`,
`Neg`) require homogenous numeric operands and return that same numeric
type — mixed forms like `TInt + TFloat64` are *rejected* in this iteration
(roadmap item 5). Comparisons (`Lt`, `Leq`, `Gt`, `Geq`) require homogenous
numeric operands and return `TBool`. `StrConcat` requires two
{name Strata.Laurel.HighType.TString}`TString` operands. Equality (`Eq`,
`Neq`) is symmetric: it accepts any two operands related by `~`, and the
diagnostic phrasing is correspondingly symmetric (neither side is framed as
"wrong").

`τ numeric` abbreviates `τ ∈ {`{name Strata.Laurel.HighType.TInt}`TInt`,
{name Strata.Laurel.HighType.TReal}`TReal`,
{name Strata.Laurel.HighType.TFloat64}`TFloat64` `}`.

```
  op ∈ {And, Or, Implies, AndThen, OrElse}      Γ ⊢ a : TBool      Γ ⊢ b : TBool
─────────────────────────────────────────────────────────────────────────────────── (T-OpBool₂)
                                Γ ⊢ PrimitiveOp op [a,b] : TBool


       Γ ⊢ a : TBool                                    Γ ⊢ a : τ      τ numeric
─────────────────────────── (T-Not)              ───────────────────────────────── (T-Neg)
  Γ ⊢ PrimitiveOp Not [a] : TBool                  Γ ⊢ PrimitiveOp Neg [a] : τ


  op ∈ {Add, Sub, Mul, Div, Mod, DivT, ModT}      Γ ⊢ a : τ      Γ ⊢ b : τ      τ numeric
──────────────────────────────────────────────────────────────────────────────────────────── (T-OpArith)
                                  Γ ⊢ PrimitiveOp op [a,b] : τ


  op ∈ {Lt, Leq, Gt, Geq}      Γ ⊢ a : τ      Γ ⊢ b : τ      τ numeric
─────────────────────────────────────────────────────────────────────────── (T-OpCmp)
                       Γ ⊢ PrimitiveOp op [a,b] : TBool


  Γ ⊢ a : TString      Γ ⊢ b : TString
─────────────────────────────────────────── (T-StrConcat)
  Γ ⊢ PrimitiveOp StrConcat [a,b] : TString


  op ∈ {Eq, Neq}      Γ ⊢ a : τ₁      Γ ⊢ b : τ₂      τ₁ ~ τ₂
────────────────────────────────────────────────────────────────── (T-OpEq)
                Γ ⊢ PrimitiveOp op [a,b] : TBool
```

### Calls and assignment

A {name Strata.Laurel.StmtExpr.StaticCall}`StaticCall`'s argument types must
each be assignable to the corresponding parameter type, and the call
synthesises the callee's return type.
{name Strata.Laurel.StmtExpr.InstanceCall}`InstanceCall` additionally
requires the receiver to fit the `self` slot.
{name Strata.Laurel.StmtExpr.Assign}`Assign` demands the LHS arity match the
RHS arity (1 for ordinary expressions, *n* for an *n*-output procedure
call), and each component must be assignable to its target. `arity(σ) = n`
for an *n*-tuple output, `1` otherwise; `σᵢ` is the *i*-th component of `σ`
when multi-valued, else `σ` itself.

```
  Γ(f) = (τ₁,…,τₙ) → τ      Γ ⊢ aᵢ : σᵢ      σᵢ ≼ τᵢ   for each i
─────────────────────────────────────────────────────────────────────── (T-Call)
                Γ ⊢ StaticCall f [a₁,…,aₙ] : τ


  Γ ⊢ recv : τ_recv      Γ.method(τ_recv, m) = (self, τ₁,…,τₙ) → τ
  Γ ⊢ aᵢ : σᵢ      σᵢ ≼ τᵢ   for each i      τ_recv ≼ self
──────────────────────────────────────────────────────────────────────── (T-InstCall)
              Γ ⊢ InstanceCall recv m [a₁,…,aₙ] : τ


  Γ ⊢ value : σ      |targets| = arity(σ)
  Γ ⊢ tᵢ : τᵢ        σᵢ ≼ τᵢ   for each target tᵢ
──────────────────────────────────────────────────── (T-Assign)
        Γ ⊢ Assign [t₁,…,tₖ] value : TVoid
```

### Variables and returns

A {name Strata.Laurel.StmtExpr.LocalVariable}`LocalVariable` with an
initialiser checks the initialiser against the declared type. A
{name Strata.Laurel.StmtExpr.Return}`Return` checks its value against the
enclosing procedure's declared output type, written `ret(proc)` — that's the
{name Strata.Laurel.TypeCheckState.currentOutputType}`currentOutputType`
field on the checker's state.

```
  Γ ⊢ init : σ      σ ≼ τ                                  Γ ⊢ value : σ      σ ≼ ret(proc)
─────────────────────────────────────── (T-LocalInit)    ───────────────────────────────────── (T-Return)
  Γ ⊢ LocalVariable x τ (some init) : TVoid                  Γ ⊢ Return (some value) : TVoid
```

### Quantifiers and type tests

{name Strata.Laurel.StmtExpr.Forall}`Forall` and
{name Strata.Laurel.StmtExpr.Exists}`Exists` extend the scope with the bound
variable and require a boolean body.
{name Strata.Laurel.StmtExpr.IsType}`IsType` always synthesises `TBool`;
{name Strata.Laurel.StmtExpr.AsType}`AsType` synthesises its declared target
type (the cast itself is not soundness-checked at compile time).

```
  Γ, x:τ ⊢ body : TBool                                      Γ, x:τ ⊢ body : TBool
─────────────────────────────────────── (T-Forall)         ─────────────────────────────────────── (T-Exists)
  Γ ⊢ Forall (x:τ) trigger body : TBool                      Γ ⊢ Exists (x:τ) trigger body : TBool


   Γ ⊢ target : _                                  Γ ⊢ target : _
──────────────────────────── (T-IsType)         ───────────────────────────── (T-AsType)
  Γ ⊢ IsType target τ : TBool                     Γ ⊢ AsType target τ : τ
```

### Procedure-level well-formedness

A functional {name Strata.Laurel.Procedure}`Procedure` whose
{name Strata.Laurel.Body}`Body` is `Transparent` has its body type checked
against the declared output type. This is the only procedure-level rule the
first iteration enforces; other body forms (`Opaque`, `Abstract`,
`External`) only have their sub-components checked.

```
  proc.isFunctional      proc.body = Transparent body      Γ ⊢ body : σ      σ ≼ ret(proc)
─────────────────────────────────────────────────────────────────────────────────────────── (T-FuncProc)
                                  ⊢ proc  ✓
```

### Cascade suppression

{name Strata.Laurel.HighType.Unknown}`Unknown` is the type resolution emits
when a name fails to resolve or a type cannot be determined; treating it as
compatible with everything keeps a single resolution error from producing
dozens of downstream type errors. Likewise, premises that demand a value
type are vacuously satisfied when the sub-expression is statement-shaped
({name Strata.Laurel.HighType.TVoid}`TVoid`). The contract is:

```
  one of σᵢ = Unknown
─────────────────────── (cascade)
  premise σᵢ ≼ τᵢ  ✓
```

Forgetting one of these wildcards in a future extension is the most common
way to break diagnostic quality without breaking correctness, so the
invariant is worth pinning with a regression test.

## Roadmap

Items deferred from the first iteration, in rough order of priority:

1. **Constrained types in boolean / numeric position.** Today any
   {name Strata.Laurel.HighType.UserDefined}`UserDefined` is permissively
   accepted by the boolean and numeric checks; only
   {name Strata.Laurel.ConstrainedType}`ConstrainedType` whose base is
   `TBool` (resp. numeric) should pass.
2. **Composite subtyping.** `var x: Dog := new Cat` is silently accepted.
   Wiring {name Strata.Laurel.computeAncestors}`computeAncestors` (already
   used by
   {name Strata.Laurel.validateDiamondFieldAccesses}`validateDiamondFieldAccesses`)
   into the assignability check closes this gap. The associated regression
   test lives as a "no diagnostic today" pin so that adding subtyping flips
   it from passing to correctly rejecting.
3. **Generic type arguments.**
   {name Strata.Laurel.HighType.Applied}`Applied`,
   {name Strata.Laurel.HighType.TSet}`TSet`,
   {name Strata.Laurel.HighType.TMap}`TMap` payload types are currently
   checked structurally without parameter substitution; extending to a
   substitution-aware check unlocks polymorphic procedures.
4. **Heap-relevant operations.**
   {name Strata.Laurel.StmtExpr.New}`New`,
   {name Strata.Laurel.StmtExpr.Old}`Old`,
   {name Strata.Laurel.StmtExpr.Fresh}`Fresh`,
   {name Strata.Laurel.StmtExpr.ContractOf}`ContractOf`,
   {name Strata.Laurel.StmtExpr.Assigned}`Assigned` currently pass through
   with no extra checks beyond their children. Each has a small set of
   constraints (e.g. `Fresh` only on impure composite types) worth
   enforcing.
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
