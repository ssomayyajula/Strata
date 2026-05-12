/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.Laurel
public import Strata.Languages.Python.PythonDialect
public import Strata.Languages.Python.Resolution
import Strata.DDM.Util.SourceRange

/-!
# Python Expression Translation (Type-Directed, Clean Implementation)

Clean implementation from first principles:
- Trust user annotations → concrete types
- Type-directed translation (straightforward mapping)
- Proper metadata preservation
- No ad-hoc wrapping in Any

## Critical Features Implemented
- Literals, variables
- Binary/unary/comparison/boolean operations
- Function calls (StaticCall to Laurel procedures)
- Attribute access (field selection)
- Subscript access (dict/list indexing)
- List/Dict/Tuple construction
- IfExp (ternary operator)
- F-strings (string concatenation)
-/

namespace Strata.Python.New

open Laurel

public section

/-! ## Error Types -/

inductive TransError where
  | unsupportedConstruct (msg : String) (ast : String)
  | internalError (msg : String)
  deriving Repr

/-! ## Translation Context -/

/-- Function/method signature for dispatch -/
structure FuncSig where
  name : String
  paramNames : List String
  deriving Inhabited

structure TransContext where
  filePath : String
  -- Type environment: variable name → type name
  typeEnv : Std.HashMap String String := {}
  -- Function signatures: qualified name → param names (for kwarg resolution)
  funcSigs : Std.HashMap String FuncSig := {}
  -- Resolution environment from nanopass: classifies names structurally
  resolvedEnv : ResolvedEnv := {}

/-! ## Smart Constructors -/

/-- Convert SourceRange to Laurel metadata -/
def sourceRangeToMetaData (filePath : String) (sr : SourceRange) : Imperative.MetaData Core.Expression :=
  let uri : Uri := .file filePath
  let fileRangeElt := ⟨ Imperative.MetaData.fileRange, .fileRange ⟨ uri, sr ⟩ ⟩
  #[fileRangeElt]

/-- Smart constructor: Create StmtExprMd with source location -/
def mkExpr (ctx : TransContext) (sr : SourceRange) (expr : StmtExpr) : StmtExprMd :=
  { val := expr, md := sourceRangeToMetaData ctx.filePath sr }

/-! ## Helper Functions -/

/-- Build list construction (simplified - direct representation) -/
def mkList (ctx : TransContext) (sr : SourceRange) (elements : List StmtExprMd) : StmtExprMd :=
  -- Lists as procedure call: List_new(elem1, elem2, ...)
  mkExpr ctx sr (.StaticCall "List_new" elements)

/-- Build dict construction (simplified - direct representation) -/
def mkDict (ctx : TransContext) (sr : SourceRange) (keys values : List StmtExprMd) : Except TransError StmtExprMd := do
  if keys.length != values.length then
    throw (.internalError "Dict keys/values length mismatch")
  -- Dict as procedure call: Dict_new(k1, v1, k2, v2, ...)
  let kvPairs := List.zip keys values
  let flatArgs := kvPairs.flatMap (fun (k, v) => [k, v])
  pure (mkExpr ctx sr (.StaticCall "Dict_new" flatArgs))

/-- Build tuple construction (simplified - direct representation) -/
def mkTuple (ctx : TransContext) (sr : SourceRange) (elements : List StmtExprMd) : StmtExprMd :=
  -- Tuples as procedure call: Tuple_new(elem1, elem2, ...)
  mkExpr ctx sr (.StaticCall "Tuple_new" elements)

/-! ## Keyword Argument Resolution -/

/-- Resolve keyword arguments against a function signature.
    With type annotations, we know parameter positions.
    Just append kwargs as positional args in signature order. -/
def resolveArgs (ctx : TransContext) (funcName : String)
    (posArgs : List StmtExprMd) (kwargs : List (String × StmtExprMd))
    : Except TransError (List StmtExprMd) := do
  if kwargs.isEmpty then
    pure posArgs
  else
    -- Look up signature to determine parameter order
    match ctx.funcSigs[funcName]? with
    | some sig =>
        -- Place kwargs in correct positions based on param names
        let numPos := posArgs.length
        let remainingParams := sig.paramNames.drop numPos
        let mut ordered := posArgs
        for paramName in remainingParams do
          match kwargs.find? (fun (name, _) => name == paramName) with
          | some (_, val) => ordered := ordered ++ [val]
          | none => pure ()  -- Optional param not provided
        pure ordered
    | none =>
        -- No signature known: just append kwargs in order
        pure (posArgs ++ kwargs.map (·.2))

/-! ## Core Translation -/

/-- Translate Python expression to Laurel StmtExpr.
    Clean implementation with proper metadata preservation.
-/
partial def translateExpr (ctx : TransContext) (e : Python.expr SourceRange)
    : Except TransError StmtExprMd := do
  match e with
  -- Literals
  | .Constant sr (.ConPos _ n) _ =>
      pure (mkExpr ctx sr (.LiteralInt n.val))
  | .Constant sr (.ConNeg _ n) _ =>
      pure (mkExpr ctx sr (.LiteralInt (-n.val)))
  | .Constant sr (.ConString _ s) _ =>
      pure (mkExpr ctx sr (.LiteralString s.val))
  | .Constant sr (.ConTrue _) _ =>
      pure (mkExpr ctx sr (.LiteralBool true))
  | .Constant sr (.ConFalse _) _ =>
      pure (mkExpr ctx sr (.LiteralBool false))
  | .Constant sr (.ConNone _) _ =>
      -- None as special constant (or could be Hole)
      pure (mkExpr ctx sr (.StaticCall "None" []))
  | .Constant sr (.ConBytes _ _) _ => pure (mkExpr ctx sr .Hole)
  | .Constant sr (.ConFloat _ f) _ =>
      -- Float: wrap in from_float prelude call with the string representation
      -- Model as StaticCall to from_float with the string value for later resolution
      pure (mkExpr ctx sr (.StaticCall "from_float" [mkExpr ctx sr (.LiteralString f.val)]))
  | .Constant sr (.ConComplex _ _ _) _ => pure (mkExpr ctx sr .Hole)
  | .Constant sr (.ConEllipsis _) _ => pure (mkExpr ctx sr .Hole)

  -- Variable references
  | .Name sr name _ =>
      pure (mkExpr ctx sr (.Identifier name.val))

  -- Binary operations
  | .BinOp sr left op right => do
      let leftExpr ← translateExpr ctx left
      let rightExpr ← translateExpr ctx right
      let preludeOp ← match op with
        | .Add _ => .ok "PAdd"
        | .Sub _ => .ok "PSub"
        | .Mult _ => .ok "PMul"
        | .Div _ => .ok "PDiv"
        | .FloorDiv _ => .ok "PFloorDiv"
        | .Mod _ => .ok "PMod"
        | .Pow _ => .ok "PPow"
        | .BitAnd _ => .ok "PBitAnd"
        | .BitOr _ => .ok "PBitOr"
        | .BitXor _ => .ok "PBitXor"
        | .LShift _ => .ok "PLShift"
        | .RShift _ => .ok "PRShift"
        | .MatMult _ => throw (.unsupportedConstruct "Matrix mult (@) not supported" "")
      pure (mkExpr ctx sr (.StaticCall preludeOp [leftExpr, rightExpr]))

  -- Comparison operations
  | .Compare sr left ops comparators => do
      if ops.val.size != 1 || comparators.val.size != 1 then
        throw (.unsupportedConstruct "Chained comparisons not supported" "")
      let leftExpr ← translateExpr ctx left
      let rightExpr ← translateExpr ctx comparators.val[0]!
      let preludeOp ← match ops.val[0]! with
        | .Eq _ => .ok "PEq"
        | .NotEq _ => .ok "PNEq"
        | .Lt _ => .ok "PLt"
        | .LtE _ => .ok "PLe"
        | .Gt _ => .ok "PGt"
        | .GtE _ => .ok "PGe"
        | .In _ => .ok "PIn"
        | .NotIn _ => .ok "PNotIn"
        | .Is _ => .ok "PIs"
        | .IsNot _ => .ok "PIsNot"
      pure (mkExpr ctx sr (.StaticCall preludeOp [leftExpr, rightExpr]))

  -- Boolean operations
  | .BoolOp sr op values => do
      if values.val.size < 2 then
        throw (.internalError "BoolOp must have at least 2 operands")
      let preludeOp ← match op with
        | .And _ => .ok "PAnd"
        | .Or _ => .ok "POr"
      -- Translate all operands
      let mut exprs : List StmtExprMd := []
      for val in values.val do
        let expr ← translateExpr ctx val
        exprs := exprs ++ [expr]
      -- Chain binary operations: a && b && c becomes (a && b) && c
      let mut result := exprs[0]!
      for i in [1:exprs.length] do
        result := mkExpr ctx sr (.StaticCall preludeOp [result, exprs[i]!])
      pure result

  -- Unary operations
  | .UnaryOp sr op operand => do
      let operandExpr ← translateExpr ctx operand
      let preludeOp ← match op with
        | .Not _ => .ok "PNot"
        | .USub _ => .ok "PNeg"
        | .UAdd _ => .ok "PPos"
        | .Invert _ => .ok "PInvert"
      pure (mkExpr ctx sr (.StaticCall preludeOp [operandExpr]))

  -- Function/Method Call: resolved via nanopass (no name classification here)
  | .Call sr func args kwargs => do
      -- Resolve call structurally via resolution environment
      let resolved := resolveCall ctx.resolvedEnv sr func args.val kwargs.val
      -- Exhaustive pattern match on resolved call — each branch determines Laurel node
      match resolved with
      | .classNew className callArgs _callKwargs => do
          -- Resolution determined this is a class: structurally emit .New
          -- Constructor args will be passed to __init__ separately
          let _translatedArgs ← callArgs.toList.mapM (translateExpr ctx)
          pure (mkExpr ctx sr (.New (Identifier.mk className none)))
      | .funcCall funcName callArgs callKwargs => do
          let posArgs ← callArgs.toList.mapM (translateExpr ctx)
          let kwargPairs ← callKwargs.toList.filterMapM (fun kw => do
            match kw with
            | .mk_keyword _ kwName kwExpr => do
                let val ← translateExpr ctx kwExpr
                match kwName.val with
                | some n => pure (some (n.val, val))
                | none => pure none)
          let allArgs ← resolveArgs ctx funcName posArgs kwargPairs
          pure (mkExpr ctx sr (.StaticCall funcName allArgs))
      | .methodCall receiver methodName callArgs callKwargs => do
          let objExpr ← translateExpr ctx receiver
          let posArgs ← callArgs.toList.mapM (translateExpr ctx)
          let kwargPairs ← callKwargs.toList.filterMapM (fun kw => do
            match kw with
            | .mk_keyword _ kwName kwExpr => do
                let val ← translateExpr ctx kwExpr
                match kwName.val with
                | some n => pure (some (n.val, val))
                | none => pure none)
          -- Qualify method name with receiver type
          let receiverType := match receiver with
            | .Name _ name _ => ctx.typeEnv[name.val]?.getD "Any"
            | _ => "Any"
          let qualifiedName := s!"{receiverType}@{methodName}"
          let allArgs ← resolveArgs ctx qualifiedName (objExpr :: posArgs) kwargPairs
          pure (mkExpr ctx sr (.StaticCall qualifiedName allArgs))

  -- Attribute access: obj.field
  | .Attribute sr obj attr _ => do
      let objExpr ← translateExpr ctx obj
      -- Direct field selection
      pure (mkExpr ctx sr (.FieldSelect objExpr attr.val))

  -- Subscript: dict[key] or list[i]
  | .Subscript sr container slice _ => do
      let containerExpr ← translateExpr ctx container
      let indexExpr ← match slice with
        | .Slice _ start stop step => do
            -- Slice notation: list[start:stop:step]
            -- For now, translate as call to Slice operation
            let startE ← match start.val with
              | some e => translateExpr ctx e
              | none => pure (mkExpr ctx sr (.LiteralInt 0))
            let stopE ← match stop.val with
              | some e => translateExpr ctx e
              | none => pure (mkExpr ctx sr (.LiteralInt (-1)))
            if step.val.isSome then
              throw (.unsupportedConstruct "Slice step not supported" "")
            pure (mkExpr ctx sr (.StaticCall "Slice_new" [startE, stopE]))
        | _ => translateExpr ctx slice
      -- Subscript as operation: Get(container, index)
      pure (mkExpr ctx sr (.StaticCall "Get" [containerExpr, indexExpr]))

  -- List literal: [1, 2, 3]
  | .List sr elts _ => do
      let elements ← elts.val.toList.mapM (translateExpr ctx)
      pure (mkList ctx sr elements)

  -- Tuple literal: (1, 2, 3)
  | .Tuple sr elts _ => do
      let elements ← elts.val.toList.mapM (translateExpr ctx)
      pure (mkTuple ctx sr elements)

  -- Dict literal: {'a': 1, 'b': 2}
  | .Dict sr keys vals => do
      let keyExprs ← keys.val.toList.mapM (fun optKey => match optKey with
        | .some_expr _ e => translateExpr ctx e
        | _ => throw (.unsupportedConstruct "Dict with None key" ""))
      let valExprs ← vals.val.toList.mapM (translateExpr ctx)
      mkDict ctx sr keyExprs valExprs

  -- IfExp: x if cond else y (ternary operator)
  | .IfExp sr test body orelse => do
      let testExpr ← translateExpr ctx test
      let bodyExpr ← translateExpr ctx body
      let elseExpr ← translateExpr ctx orelse
      pure (mkExpr ctx sr (.IfThenElse testExpr bodyExpr elseExpr))

  -- F-string: f"{x} is {y}"
  | .JoinedStr sr values => do
      if values.val.isEmpty then
        pure (mkExpr ctx sr (.LiteralString ""))
      else
        -- Translate each part and concatenate
        let parts ← values.val.toList.mapM (translateExpr ctx)
        -- Build concatenation via string operations
        let mut result := mkExpr ctx sr (.LiteralString "")
        for part in parts do
          result := mkExpr ctx sr (.StaticCall "StrConcat" [result, part])
        pure result

  -- F-string interpolation: {expr}
  | .FormattedValue sr value _ _ => do
      let valueExpr ← translateExpr ctx value
      -- Convert value to string
      pure (mkExpr ctx sr (.StaticCall "ToString" [valueExpr]))

  -- Lambda: lambda x: x + 1 (treat as Hole for now - needs closure support)
  | .Lambda sr .. => pure (mkExpr ctx sr .Hole)

  -- Everything else: Hole (preserve source location)
  | .Set sr .. => pure (mkExpr ctx sr .Hole)
  | .ListComp sr .. => pure (mkExpr ctx sr .Hole)
  | .SetComp sr .. => pure (mkExpr ctx sr .Hole)
  | .DictComp sr .. => pure (mkExpr ctx sr .Hole)
  | .GeneratorExp sr .. => pure (mkExpr ctx sr .Hole)
  | .NamedExpr sr .. => pure (mkExpr ctx sr .Hole)
  | .Slice sr .. => pure (mkExpr ctx sr .Hole)
  | .Starred sr .. => pure (mkExpr ctx sr .Hole)
  | .Await sr .. => pure (mkExpr ctx sr .Hole)
  | .Yield sr .. => pure (mkExpr ctx sr .Hole)
  | .YieldFrom sr .. => pure (mkExpr ctx sr .Hole)
  | .TemplateStr sr .. => pure (mkExpr ctx sr .Hole)
  | .Interpolation sr .. => pure (mkExpr ctx sr .Hole)

end -- public section
end Strata.Python.New
