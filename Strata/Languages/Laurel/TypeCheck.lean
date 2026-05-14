/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.Laurel
public import Strata.Languages.Laurel.LaurelTypes
public import Strata.Languages.Laurel.Resolution

/-!
# Type Checking Pass

Standalone pass over a resolved Laurel `Program`. Walks the AST, computes the
type of each `StmtExpr` via `LaurelTypes.computeExprType`, and checks that each
context (assignment, call argument, branch condition, return value, …) receives
a type compatible with what the construct expects.

Input:  resolved `Program` + `SemanticModel` (from `Resolution`)
Output: `List DiagnosticModel` (empty on success).

Type *queries* live in `LaurelTypes.lean`; reusable type *relations* (subtype,
LUB, assignability) should be added there if a future pass needs them. This file
owns the traversal, the monadic state, and the diagnostic emission.
-/

namespace Strata.Laurel

public section

/-! ## Diagnostics -/

/-- Reasons type checking can fail. Categorising up-front makes it easier to
filter and test, and keeps message strings out of the traversal. -/
inductive TypeError where
  /-- Two types had to match (e.g. assignment, branch arms) and didn't. -/
  | mismatch (expected : HighType) (actual : HighType)
  /-- Wrong number of arguments to a callee. -/
  | arityMismatch (callee : Identifier) (expected actual : Nat)
  /-- A construct expected a specific type form (e.g. `TBool` for `if`). -/
  | expected (form : String) (actual : HighType)
  /-- Field access on a non-composite target. -/
  | notComposite (actual : HighType)
  /-- Generic catch-all while the checker is being filled in. -/
  | other (msg : String)
  deriving Repr

instance : Std.ToFormat TypeError where
  format
    | .mismatch e a        => f!"type mismatch: expected {e}, got {a}"
    | .arityMismatch c e a => f!"'{c}' expects {e} argument(s), got {a}"
    | .expected form a     => f!"expected {form}, got {a}"
    | .notComposite a      => f!"field access on non-composite type {a}"
    | .other m             => Std.Format.text m

/-! ## Monad -/

/-- State threaded through the checker. Mirrors `InferHoleState` in shape. -/
structure TypeCheckState where
  /-- Resolved semantic model produced by the resolution pass. -/
  model : SemanticModel
  /-- Output type of the procedure currently being checked. Used by `Return`. -/
  currentOutputType : HighTypeMd := ⟨.Unknown, #[]⟩
  /-- Diagnostics accumulated so far. -/
  errors : Array DiagnosticModel := #[]

@[expose] abbrev TypeCheckM := StateM TypeCheckState

private def emit (err : TypeError) (md : Imperative.MetaData Core.Expression) : TypeCheckM Unit := do
  let range := (Imperative.getFileRange md).getD FileRange.unknown
  modify fun s => { s with errors := s.errors.push (.withRange range s!"{Std.format err}") }

/-! ## Type relations

These helpers are intentionally tiny here; promote any of them to
`LaurelTypes.lean` if a second pass starts depending on them. -/

/-- Decide whether `actual` is assignable where `expected` is required.
TODO: implement properly (subtyping via `computeAncestors`, `Unknown`/`TCore`
leniency, etc.). -/
def isAssignable (model : SemanticModel) (expected actual : HighType) : Bool :=
  -- TODO: real subtype check
  let _ := model
  let _ := expected
  let _ := actual
  true

/-! ## Expression checking

The traversal mirrors `InferHoleTypes.inferExpr` and `Resolution.resolveStmtExpr`
so future maintainers can diff the three side-by-side. Each arm:
  1. recurses on sub-expressions,
  2. checks shape constraints local to that constructor,
  3. returns the type the *whole* expression has so the caller can use it.
-/

mutual

/-- Check an expression and return its type. Errors are accumulated in state. -/
partial def checkExpr (expr : StmtExprMd) : TypeCheckM HighTypeMd := do
  let model := (← get).model
  match expr with
  | WithMetadata.mk val md =>
  match val with
  -- Literals
  | .LiteralInt _ | .LiteralBool _ | .LiteralString _ | .LiteralDecimal _ =>
      pure (computeExprType model expr)
  -- References
  | .Identifier _ =>
      pure (computeExprType model expr)
  | .FieldSelect target _ =>
      -- TODO: verify target's type is composite, that field is reachable
      let _ ← checkExpr target
      pure (computeExprType model expr)
  | .PureFieldUpdate target _ newVal =>
      let _ ← checkExpr target
      let _ ← checkExpr newVal
      -- TODO: check newVal's type is assignable to the field's declared type
      pure (computeExprType model expr)
  -- Calls
  | .StaticCall _ args =>
      -- TODO: arity + per-arg assignability against `calleeParamTypes`
      let _ ← args.mapM checkExpr
      pure (computeExprType model expr)
  | .InstanceCall target _ args =>
      let _ ← checkExpr target
      let _ ← args.mapM checkExpr
      pure (computeExprType model expr)
  | .PrimitiveOp _ args =>
      -- TODO: per-operator type rules (Eq/Neq accept any matching pair,
      -- arithmetic ops require numeric operands, etc.)
      let _ ← args.mapM checkExpr
      pure (computeExprType model expr)
  -- Control flow / blocks
  | .IfThenElse cond thenBr elseBr =>
      let _ ← checkExpr cond
      -- TODO: assert cond is TBool
      let _ ← checkExpr thenBr
      match elseBr with
      | some e => let _ ← checkExpr e; pure ()
      | none => pure ()
      -- TODO: branches must agree (or use computeExprType's choice)
      pure (computeExprType model expr)
  | .Block stmts _ =>
      let _ ← stmts.mapM checkStmt
      pure (computeExprType model expr)
  -- Statement-shaped StmtExprs
  | .LocalVariable _ ty init =>
      match init with
      | some i =>
          let _ ← checkExpr i
          -- TODO: assert init's type is assignable to `ty`
          pure ()
      | none => pure ()
      pure ⟨.TVoid, md⟩
  | .Assign targets value =>
      let _ ← targets.mapM checkExpr
      let _ ← checkExpr value
      -- TODO: each target's type assignable from value (or, for multi-target,
      -- match against StaticCall outputs)
      pure ⟨.TVoid, md⟩
  | .While cond invs dec body =>
      let _ ← checkExpr cond
      -- TODO: cond must be TBool, invariants must be TBool, dec must be TInt
      let _ ← invs.mapM checkExpr
      match dec with
      | some d => let _ ← checkExpr d; pure ()
      | none => pure ()
      let _ ← checkExpr body
      pure ⟨.TVoid, md⟩
  | .Exit _ => pure ⟨.TVoid, md⟩
  | .Return v =>
      match v with
      | some e =>
          let _ ← checkExpr e
          -- TODO: assignable to (← get).currentOutputType
          pure ()
      | none => pure ()
      pure ⟨.TVoid, md⟩
  | .Assert cond | .Assume cond =>
      let _ ← checkExpr cond
      -- TODO: cond must be TBool
      pure ⟨.TVoid, md⟩
  -- Object / type
  | .New _ => pure (computeExprType model expr)
  | .This => pure (computeExprType model expr)
  | .ReferenceEquals lhs rhs =>
      let _ ← checkExpr lhs
      let _ ← checkExpr rhs
      pure ⟨.TBool, md⟩
  | .AsType target _ =>
      let _ ← checkExpr target
      pure (computeExprType model expr)
  | .IsType target _ =>
      let _ ← checkExpr target
      pure ⟨.TBool, md⟩
  -- Quantifiers
  | .Forall _ trigger body | .Exists _ trigger body =>
      match trigger with
      | some t => let _ ← checkExpr t; pure ()
      | none => pure ()
      let _ ← checkExpr body
      -- TODO: body must be TBool
      pure ⟨.TBool, md⟩
  -- Verification-only
  | .Assigned n => let _ ← checkExpr n; pure ⟨.TBool, md⟩
  | .Old v => checkExpr v
  | .Fresh v => let _ ← checkExpr v; pure ⟨.TBool, md⟩
  | .ProveBy v p =>
      let _ ← checkExpr p
      checkExpr v
  | .ContractOf _ f =>
      let _ ← checkExpr f
      pure (computeExprType model expr)
  -- Markers / holes
  | .Abstract | .All => pure (computeExprType model expr)
  | .Hole _ _ => pure (computeExprType model expr)

/-- Check a statement-shaped `StmtExpr`. The split between `checkExpr` and
`checkStmt` matches `InferHoleTypes`; today they're nearly identical, but
keeping them separate leaves room for context-specific rules (e.g. requiring
`Block` arms to be statements). -/
partial def checkStmt (stmt : StmtExprMd) : TypeCheckM Unit := do
  let _ ← checkExpr stmt
  pure ()

end

/-! ## Procedure / Program entry points -/

/-- Check a procedure body in the context of its declared output type. -/
def checkProcedure (proc : Procedure) : TypeCheckM Unit := do
  let outputType := match proc.outputs with
    | [single] => single.type
    | _ => ⟨.Unknown, #[]⟩
  modify fun s => { s with currentOutputType := outputType }
  -- TODO: check preconditions are TBool, decreases is TInt, determinism's reads
  match proc.body with
  | .Transparent body => checkStmt body
  | .Opaque postconds impl _ =>
      let _ ← postconds.mapM checkStmt
      match impl with
      | some i => checkStmt i
      | none => pure ()
  | .Abstract postconds => let _ ← postconds.mapM checkStmt; pure ()
  | .External => pure ()

/-- Run the type checker over a fully resolved program.
Returns the diagnostics; an empty array means the program type-checks. -/
def typeCheck (model : SemanticModel) (program : Program) : Array DiagnosticModel :=
  let init : TypeCheckState := { model := model }
  let (_, st) := (program.staticProcedures.mapM checkProcedure).run init
  -- TODO: also check constants' initializers, instance procedures on composite
  -- types, static fields' types, etc.
  st.errors

end -- public section

end Strata.Laurel
