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

/-! ## Type relations

These helpers are intentionally tiny here; promote any of them to
`LaurelTypes.lean` if a second pass starts depending on them. -/

/-- Whether `t` is one of the numeric base types. Roadmap item 1
(`ConstrainedType` over numeric base) and 5 (mixed-numeric coercions) widen
this; for now it is exactly `{TInt, TReal, TFloat64}`. -/
def HighType.isNumeric : HighType → Bool
  | .TInt | .TReal | .TFloat64 => true
  | _ => false

/-- The assignability judgement `actual ≼ expected` from the doc. First
iteration: equality, with `Unknown` (either side) and `TVoid` (actual side
only — premises demanding a value type are vacuously satisfied for
statement-shaped sub-expressions) acting as cascade wildcards. -/
def isAssignable (expected actual : HighType) : Bool :=
  match expected, actual with
  | .Unknown, _ | _, .Unknown | _, .TVoid => true
  | _, _ => highEq ⟨expected, default⟩ ⟨actual, default⟩

/-- Compatibility predicate `~` from the doc: assignable in either direction.
Used by symmetric operators (`Eq`, `Neq`). -/
def isCompatible (a b : HighType) : Bool :=
  isAssignable a b || isAssignable b a

/-- Whether a synthesised type should be treated as a wildcard (i.e. silently
satisfy any premise). `Unknown` propagates resolution errors; `TVoid`
propagates statement-shaped sub-expressions. -/
def HighType.isCascade : HighType → Bool
  | .Unknown | .TVoid => true
  | _ => false

private def emit (err : TypeError) (md : Imperative.MetaData Core.Expression) : TypeCheckM Unit := do
  let range := (Imperative.getFileRange md).getD FileRange.unknown
  modify fun s => { s with errors := s.errors.push (.withRange range s!"{Std.format err}") }

/-- Assert that `actual` is assignable where `expected` is required. -/
private def expectAssignable (expected actual : HighTypeMd)
    (md : Imperative.MetaData Core.Expression) : TypeCheckM Unit := do
  unless isAssignable expected.val actual.val do
    emit (.mismatch expected.val actual.val) md

/-- Assert that `actual` matches a *form* (e.g. `TBool`, `numeric`) described
by `pred`; the `form` string is only used for the diagnostic. Cascades on
`Unknown`/`TVoid`. -/
private def expectForm (pred : HighType → Bool) (form : String) (actual : HighTypeMd)
    (md : Imperative.MetaData Core.Expression) : TypeCheckM Unit := do
  unless actual.val.isCascade || pred actual.val do
    emit (.expected form actual.val) md

private def expectBool (actual : HighTypeMd)
    (md : Imperative.MetaData Core.Expression) : TypeCheckM Unit :=
  expectForm (· matches .TBool) "bool" actual md

private def expectNumeric (actual : HighTypeMd)
    (md : Imperative.MetaData Core.Expression) : TypeCheckM Unit :=
  expectForm HighType.isNumeric "numeric type" actual md

private def expectInt (actual : HighTypeMd)
    (md : Imperative.MetaData Core.Expression) : TypeCheckM Unit :=
  expectForm (· matches .TInt) "int" actual md

private def expectString (actual : HighTypeMd)
    (md : Imperative.MetaData Core.Expression) : TypeCheckM Unit :=
  expectForm (· matches .TString) "string" actual md

/-! ## Expression checking

The traversal mirrors `InferHoleTypes.inferExpr` and `Resolution.resolveStmtExpr`
so future maintainers can diff the three side-by-side. Each arm:
  1. recurses on sub-expressions,
  2. checks shape constraints local to that constructor,
  3. returns the type the *whole* expression has so the caller can use it.
-/

/-- Look up the parameter list of a callee resolved by `Resolution`. Returns
`none` when the callee is unresolved, function-typed, or otherwise not a
direct procedure/constructor — the caller should suppress arity/per-arg
checks in that case (cascade). -/
private def calleeParams (model : SemanticModel) (callee : Identifier) :
    Option (List Parameter) :=
  match model.get callee with
  | .staticProcedure proc => some proc.inputs
  | .instanceProcedure _ proc => some proc.inputs
  | .datatypeConstructor _ ctor => some ctor.args
  | _ => none

mutual

/-- Check an expression and return its type. Errors are accumulated in state. -/
partial def checkExpr (expr : StmtExprMd) : TypeCheckM HighTypeMd := do
  let model := (← get).model
  match expr with
  | WithMetadata.mk val md =>
  match val with
  -- Literals (T-Lit*)
  | .LiteralInt _ | .LiteralBool _ | .LiteralString _ | .LiteralDecimal _ =>
      pure (computeExprType model expr)
  -- References (T-Var)
  | .Identifier _ =>
      pure (computeExprType model expr)
  | .FieldSelect target _ =>
      -- TODO: verify field is reachable on target's composite type (roadmap).
      let _ ← checkExpr target
      pure (computeExprType model expr)
  | .PureFieldUpdate target _ newVal =>
      let _ ← checkExpr target
      let _ ← checkExpr newVal
      -- TODO: check newVal is assignable to the field's declared type (roadmap
      -- — needs the field-on-composite lookup that FieldSelect is also missing).
      pure (computeExprType model expr)
  -- Calls (T-Call / T-InstCall)
  | .StaticCall callee args =>
      let argTys ← args.mapM checkExpr
      match calleeParams model callee with
      | some params =>
          if params.length ≠ args.length then
            emit (.arityMismatch callee params.length args.length) md
          else
            for (param, argTy, arg) in params.zip (argTys.zip args) do
              expectAssignable param.type argTy arg.md
      | none => pure ()
      pure (computeExprType model expr)
  | .InstanceCall target callee args =>
      let _ ← checkExpr target
      let argTys ← args.mapM checkExpr
      -- TODO: receiver ≼ self (roadmap — instance-method receiver-type lookup
      -- doesn't have a single source of truth yet).
      match calleeParams model callee with
      | some params =>
          if params.length ≠ args.length then
            emit (.arityMismatch callee params.length args.length) md
          else
            for (param, argTy, arg) in params.zip (argTys.zip args) do
              expectAssignable param.type argTy arg.md
      | none => pure ()
      pure (computeExprType model expr)
  -- Primitive operators (T-OpBool₂ / T-Not / T-Neg / T-OpArith / T-OpCmp /
  -- T-StrConcat / T-OpEq).
  | .PrimitiveOp op args =>
      let argTys ← args.mapM checkExpr
      match op, args, argTys with
      | .And,  [a,b], [ta,tb] | .Or,      [a,b], [ta,tb]
      | .AndThen, [a,b], [ta,tb] | .OrElse, [a,b], [ta,tb]
      | .Implies, [a,b], [ta,tb] =>
          expectBool ta a.md; expectBool tb b.md
      | .Not, [a], [ta] => expectBool ta a.md
      | .Neg, [a], [ta] => expectNumeric ta a.md
      | .Add, [a,b], [ta,tb] | .Sub, [a,b], [ta,tb]
      | .Mul, [a,b], [ta,tb] | .Div, [a,b], [ta,tb]
      | .Mod, [a,b], [ta,tb] | .DivT, [a,b], [ta,tb] | .ModT, [a,b], [ta,tb] =>
          expectNumeric ta a.md
          expectAssignable ta tb b.md
      | .Lt, [a,b], [ta,tb] | .Leq, [a,b], [ta,tb]
      | .Gt, [a,b], [ta,tb] | .Geq, [a,b], [ta,tb] =>
          expectNumeric ta a.md
          expectAssignable ta tb b.md
      | .StrConcat, [a,b], [ta,tb] =>
          expectString ta a.md; expectString tb b.md
      | .Eq, [_,b], [ta,tb] | .Neq, [_,b], [ta,tb] =>
          -- Per doc T-OpEq: the diagnostic is symmetric — neither side is
          -- framed as "wrong" — so use `.other` rather than `mismatch`.
          unless ta.val.isCascade || tb.val.isCascade || isCompatible ta.val tb.val do
            emit (.other s!"incompatible operand types {Std.format ta.val} and {Std.format tb.val}") b.md
      | _, _, _ =>
          -- Wrong arity for the operator's family (or a future op without a
          -- rule yet); flag generically rather than silently passing.
          emit (.other s!"primitive operator {repr op} given {args.length} argument(s)") md
      pure (computeExprType model expr)
  -- Control flow / blocks
  | .IfThenElse cond thenBr elseBr =>
      let condTy ← checkExpr cond
      expectBool condTy cond.md  -- T-If, T-IfStmt
      let thenTy ← checkExpr thenBr
      match elseBr with
      | some e =>
          let elseTy ← checkExpr e
          -- T-If: branches must agree (compatible in either direction).
          unless thenTy.val.isCascade || elseTy.val.isCascade
              || isCompatible thenTy.val elseTy.val do
            emit (.mismatch thenTy.val elseTy.val) e.md
      | none => pure ()
      pure (computeExprType model expr)
  | .Block stmts _ =>
      let _ ← stmts.mapM checkStmt
      pure (computeExprType model expr)
  -- Statement-shaped StmtExprs
  | .LocalVariable _ ty init =>
      match init with
      | some i =>
          let initTy ← checkExpr i
          expectAssignable ty initTy i.md  -- T-LocalInit
      | none => pure ()
      pure ⟨.TVoid, md⟩
  | .Assign targets value =>
      let targetTys ← targets.mapM checkExpr
      let valueTy ← checkExpr value
      -- T-Assign: |targets| = arity(valueType). Multi-target assignment is
      -- only well-formed when `value` is a multi-output `StaticCall`; that's
      -- the only construct whose `arity` exceeds 1.
      match targets, value with
      | [_], _ =>
          expectAssignable targetTys[0]! valueTy value.md
      | _, ⟨.StaticCall callee _, _⟩ =>
          match model.get callee with
          | .staticProcedure proc =>
              if proc.outputs.length ≠ targets.length then
                emit (.arityMismatch callee proc.outputs.length targets.length) md
              else
                for (out, tgtTy, tgt) in proc.outputs.zip (targetTys.zip targets) do
                  expectAssignable tgtTy out.type tgt.md
          | _ =>
              -- Unresolved or non-procedure callee: cascade.
              pure ()
      | _, _ =>
          -- Multi-target with a non-`StaticCall` RHS — by Laurel's grammar
          -- the assignment itself is malformed; we still report it.
          emit (.other "multi-target assignment requires a static-call RHS") md
      pure ⟨.TVoid, md⟩
  | .While cond invs dec body =>
      let condTy ← checkExpr cond
      expectBool condTy cond.md  -- T-While: cond is TBool
      for inv in invs do
        let invTy ← checkExpr inv
        expectBool invTy inv.md  -- T-While: each invariant is TBool
      match dec with
      | some d =>
          let decTy ← checkExpr d
          expectInt decTy d.md  -- T-While: decreases is TInt
      | none => pure ()
      let _ ← checkExpr body
      pure ⟨.TVoid, md⟩
  | .Exit _ => pure ⟨.TVoid, md⟩
  | .Return v =>
      match v with
      | some e =>
          let retTy ← checkExpr e
          let expected := (← get).currentOutputType
          expectAssignable expected retTy e.md  -- T-Return
      | none => pure ()
      pure ⟨.TVoid, md⟩
  | .Assert cond | .Assume cond =>
      let condTy ← checkExpr cond
      expectBool condTy cond.md  -- T-Assert / T-Assume
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
  -- Quantifiers (T-Forall / T-Exists)
  | .Forall _ trigger body | .Exists _ trigger body =>
      match trigger with
      | some t => let _ ← checkExpr t; pure ()
      | none => pure ()
      let bodyTy ← checkExpr body
      expectBool bodyTy body.md
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
  match proc.body with
  | .Transparent body =>
      let bodyTy ← checkExpr body
      -- T-FuncProc: a functional procedure with a transparent body must
      -- synthesise a value assignable to its declared output type. Non-
      -- functional procedures use `Return` for that contract instead.
      if proc.isFunctional then
        expectAssignable outputType bodyTy body.md
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
