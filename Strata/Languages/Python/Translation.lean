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
# Pass 2: Translation

Fold over the resolved Python AST. Reads annotations on each node,
emits corresponding Laurel constructs. No name resolution, no lookups.

Input:  ResolvedPythonProgram
Output: Laurel.Program
-/

namespace Strata.Python.Translation

open Strata.Laurel hiding Identifier
open Strata.Python.Resolution

public section

-- ═══════════════════════════════════════════════════════════════════════════════
-- Error
-- ═══════════════════════════════════════════════════════════════════════════════

inductive TransError where
  | unsupportedConstruct (msg : String)
  | internalError (msg : String)
  | userError (range : SourceRange) (msg : String)
  deriving Repr

instance : ToString TransError where
  toString
    | .unsupportedConstruct msg => s!"Translation: unsupported construct: {msg}"
    | .internalError msg => s!"Translation: internal error: {msg}"
    | .userError _range msg => s!"User code error: {msg}"

-- ═══════════════════════════════════════════════════════════════════════════════
-- Monad (State for fresh names only)
-- ═══════════════════════════════════════════════════════════════════════════════

structure TransState where
  freshCounter : Nat := 0
  filePath : System.FilePath := ""
  loopLabels : List (Laurel.Identifier × Laurel.Identifier) := []
  deriving Inhabited

abbrev TransM := StateT TransState (Except TransError)

-- ═══════════════════════════════════════════════════════════════════════════════
-- Smart Constructors
-- ═══════════════════════════════════════════════════════════════════════════════

private def sourceRangeToMd (filePath : System.FilePath) (sr : SourceRange) : Imperative.MetaData Core.Expression :=
  let uri : Uri := .file filePath.toString
  #[⟨ Imperative.MetaData.fileRange, .fileRange ⟨ uri, sr ⟩ ⟩]

def mkExpr (sr : SourceRange) (expr : StmtExpr) : TransM StmtExprMd := do
  pure { val := expr, md := sourceRangeToMd (← get).filePath sr }

private def defaultMd : Imperative.MetaData Core.Expression := #[]
def mkExprDefault (expr : StmtExpr) : StmtExprMd := { val := expr, md := defaultMd }
def mkTypeDefault (ty : HighType) : HighTypeMd := { val := ty, md := defaultMd }

def freshId (pfx : String) : TransM Laurel.Identifier := do
  let s ← get; set { s with freshCounter := s.freshCounter + 1 }
  pure (Laurel.Identifier.mk s!"{pfx}_{s.freshCounter}" none)

def pushLoopLabel (pfx : String) : TransM (Laurel.Identifier × Laurel.Identifier) := do
  let s ← get
  let bk := Laurel.Identifier.mk s!"{pfx}_break_{s.freshCounter}" none
  let ct := Laurel.Identifier.mk s!"{pfx}_continue_{s.freshCounter}" none
  set { s with freshCounter := s.freshCounter + 1, loopLabels := (bk, ct) :: s.loopLabels }
  pure (bk, ct)

def popLoopLabel : TransM Unit := modify fun s => { s with loopLabels := s.loopLabels.tail! }
def currentBreakLabel : TransM (Option Laurel.Identifier) := do return (← get).loopLabels.head?.map (·.1)
def currentContinueLabel : TransM (Option Laurel.Identifier) := do return (← get).loopLabels.head?.map (·.2)

-- ═══════════════════════════════════════════════════════════════════════════════
-- PythonType → HighType (architecture §Translation: "map PythonType annotations to HighType")
-- ═══════════════════════════════════════════════════════════════════════════════

def pythonTypeToHighType : PythonType → HighType
  | .Name _ n _ => match n.val with
    | "int" => .TInt
    | "bool" => .TBool
    | "str" => .TString
    | "float" => .TFloat64
    | "None" => .TVoid
    | "Any" => .TCore "Any"
    | name => .UserDefined { text := name, uniqueId := none }
  | .Constant _ (.ConNone _) _ => .TVoid
  | .BinOp _ _ (.BitOr _) _ => .TCore "Any"
  | .Subscript _ (.Name _ n _) _ _ => match n.val with
    | "Optional" | "Union" | "List" | "Dict" | "Tuple" | "Set" | "Type" => .TCore "Any"
    | other => .UserDefined { text := other, uniqueId := none }
  | _ => .TCore "Any"

-- ═══════════════════════════════════════════════════════════════════════════════
-- Python Name → Laurel Name (builtins only)
-- ═══════════════════════════════════════════════════════════════════════════════

def pythonNameToLaurel : String → String
  | "len" => "Any_len_to_Any"
  | "str" => "to_string_any"
  | "int" => "to_int_any"
  | "float" => "to_float_any"
  | "bool" => "Any_to_bool"
  | "abs" => "Any_abs_to_Any"
  | "print" => "print"
  | "repr" => "to_string_any"
  | "type" => "Any_type_to_Any"
  | "isinstance" => "Any_isinstance_to_bool"
  | "hasattr" => "Any_hasattr_to_bool"
  | "getattr" => "Any_getattr_to_Any"
  | "setattr" => "Any_setattr_to_Any"
  | "sorted" => "Any_sorted_to_Any"
  | "reversed" => "Any_reversed_to_Any"
  | "enumerate" => "Any_enumerate_to_Any"
  | "zip" => "Any_zip_to_Any"
  | "range" => "Any_range_to_Any"
  | "list" => "Any_list_to_Any"
  | "dict" => "Any_dict_to_Any"
  | "set" => "Any_set_to_Any"
  | "tuple" => "Any_tuple_to_Any"
  | "min" => "Any_min_to_Any"
  | "max" => "Any_max_to_Any"
  | "sum" => "Any_sum_to_Any"
  | "any" => "Any_any_to_bool"
  | "all" => "Any_all_to_bool"
  | "ord" => "Any_ord_to_Any"
  | "chr" => "Any_chr_to_Any"
  | "map" => "Any_map_to_Any"
  | "filter" => "Any_filter_to_Any"
  | "timedelta" => "timedelta_func"
  | other => other

-- ═══════════════════════════════════════════════════════════════════════════════
-- Module-level local collection (for __main__ scope declarations)
-- ═══════════════════════════════════════════════════════════════════════════════

private partial def extractResolvedTargetNames : Python.expr ResolvedAnn → List String
  | .Name _ n _ => [n.val]
  | .Tuple _ elems _ => elems.val.toList.flatMap extractResolvedTargetNames
  | .List _ elems _ => elems.val.toList.flatMap extractResolvedTargetNames
  | .Starred _ inner _ => extractResolvedTargetNames inner
  | _ => []

private partial def collectLocalsFromResolvedStmt (s : Python.stmt ResolvedAnn) : List String :=
  match s with
  | .Assign _ targets _ _ => targets.val.toList.flatMap extractResolvedTargetNames
  | .AnnAssign _ target _ _ _ => extractResolvedTargetNames target
  | .AugAssign _ target _ _ => extractResolvedTargetNames target
  | .For _ target _ body orelse _ =>
      extractResolvedTargetNames target ++
      body.val.toList.flatMap collectLocalsFromResolvedStmt ++
      orelse.val.toList.flatMap collectLocalsFromResolvedStmt
  | .AsyncFor _ target _ body orelse _ =>
      extractResolvedTargetNames target ++
      body.val.toList.flatMap collectLocalsFromResolvedStmt ++
      orelse.val.toList.flatMap collectLocalsFromResolvedStmt
  | .If _ _ body orelse =>
      body.val.toList.flatMap collectLocalsFromResolvedStmt ++
      orelse.val.toList.flatMap collectLocalsFromResolvedStmt
  | .While _ _ body orelse =>
      body.val.toList.flatMap collectLocalsFromResolvedStmt ++
      orelse.val.toList.flatMap collectLocalsFromResolvedStmt
  | .Try _ body handlers orelse finalbody =>
      body.val.toList.flatMap collectLocalsFromResolvedStmt ++
      handlers.val.toList.flatMap (fun h => match h with
        | .ExceptHandler _ _ _ hBody => hBody.val.toList.flatMap collectLocalsFromResolvedStmt) ++
      orelse.val.toList.flatMap collectLocalsFromResolvedStmt ++
      finalbody.val.toList.flatMap collectLocalsFromResolvedStmt
  | .TryStar _ body handlers orelse finalbody =>
      body.val.toList.flatMap collectLocalsFromResolvedStmt ++
      handlers.val.toList.flatMap (fun h => match h with
        | .ExceptHandler _ _ _ hBody => hBody.val.toList.flatMap collectLocalsFromResolvedStmt) ++
      orelse.val.toList.flatMap collectLocalsFromResolvedStmt ++
      finalbody.val.toList.flatMap collectLocalsFromResolvedStmt
  | .With _ _ body _ => body.val.toList.flatMap collectLocalsFromResolvedStmt
  | .AsyncWith _ _ body _ => body.val.toList.flatMap collectLocalsFromResolvedStmt
  | _ => []

private def collectModuleLocals (stmts : List (Python.stmt ResolvedAnn)) : List (String × Unit) :=
  let allNames := stmts.flatMap collectLocalsFromResolvedStmt
  let (_, result) := allNames.foldl (init := (({} : Std.HashSet String), ([] : List (String × Unit)))) fun acc name =>
    let (seen, result) := acc
    if seen.contains name then (seen, result)
    else (seen.insert name, result ++ [(name, ())])
  result

-- ═══════════════════════════════════════════════════════════════════════════════
-- Arg Matching (architecture: "uses FuncSig from annotation to match args to params")
-- ═══════════════════════════════════════════════════════════════════════════════

def matchArgs (sig : FuncSig) (posArgs : List StmtExprMd)
    (kwargs : List (String × StmtExprMd)) : List StmtExprMd :=
  let paramNames := sig.params.map (·.1)
  let numPos := posArgs.length
  let remainingParams := paramNames.drop numPos
  let kwargMatched := remainingParams.filterMap fun pName =>
    kwargs.find? (fun (k, _) => k == pName) |>.map (·.2)
  posArgs ++ kwargMatched

-- ═══════════════════════════════════════════════════════════════════════════════
-- The Fold
-- ═══════════════════════════════════════════════════════════════════════════════

mutual

-- ═══════════════════════════════════════════════════════════════════════════════
-- translateExpr: compositional, one StmtExprMd out
-- ═══════════════════════════════════════════════════════════════════════════════

partial def translateExpr (e : Python.expr ResolvedAnn) : TransM StmtExprMd := do
  let sr := e.ann.sr
  match e with
  | .Constant _ (.ConPos _ n) _ => mkExpr sr (.LiteralInt n.val)
  | .Constant _ (.ConNeg _ n) _ => mkExpr sr (.LiteralInt (-n.val))
  | .Constant _ (.ConString _ s) _ => mkExpr sr (.LiteralString s.val)
  | .Constant _ (.ConTrue _) _ => mkExpr sr (.LiteralBool true)
  | .Constant _ (.ConFalse _) _ => mkExpr sr (.LiteralBool false)
  | .Constant _ (.ConNone _) _ => mkExpr sr (.StaticCall "from_None" [])
  | .Constant _ (.ConFloat _ f) _ => mkExpr sr (.LiteralString f.val)
  | .Constant _ _ _ => mkExpr sr .Hole
  | .Name _ name _ => mkExpr sr (.Identifier name.val)
  | .BinOp _ left op right => do
      let l ← translateExpr left; let r ← translateExpr right
      let opName := match op with
        | .Add _ => "PAdd" | .Sub _ => "PSub" | .Mult _ => "PMul" | .Div _ => "PDiv"
        | .FloorDiv _ => "PFloorDiv" | .Mod _ => "PMod" | .Pow _ => "PPow"
        | .BitAnd _ => "PBitAnd" | .BitOr _ => "PBitOr" | .BitXor _ => "PBitXor"
        | .LShift _ => "PLShift" | .RShift _ => "PRShift" | .MatMult _ => "PMatMul"
      mkExpr sr (.StaticCall opName [l, r])
  | .Compare _ left ops comparators => do
      if ops.val.size != 1 || comparators.val.size != 1 then
        throw (.unsupportedConstruct "Chained comparisons")
      let l ← translateExpr left; let r ← translateExpr comparators.val[0]!
      let opName := match ops.val[0]! with
        | .Eq _ => "PEq" | .NotEq _ => "PNEq" | .Lt _ => "PLt" | .LtE _ => "PLe"
        | .Gt _ => "PGt" | .GtE _ => "PGe" | .In _ => "PIn" | .NotIn _ => "PNotIn"
        | .Is _ => "PIs" | .IsNot _ => "PIsNot"
      mkExpr sr (.StaticCall opName [l, r])
  | .BoolOp _ op values => do
      if values.val.size < 2 then throw (.internalError "BoolOp requires at least 2 operands")
      let opName := match op with | .And _ => "PAnd" | .Or _ => "POr"
      let exprs ← values.val.toList.mapM translateExpr
      let mut result := exprs[0]!
      for i in [1:exprs.length] do result ← mkExpr sr (.StaticCall opName [result, exprs[i]!])
      pure result
  | .UnaryOp _ op operand => do
      let inner ← translateExpr operand
      let opName := match op with
        | .Not _ => "PNot" | .USub _ => "PNeg" | .UAdd _ => "PPos" | .Invert _ => "PInvert"
      mkExpr sr (.StaticCall opName [inner])
  | .Call ann func args kwargs => translateCallExpr sr ann func args kwargs
  | .Attribute _ obj attr _ => do
      mkExpr sr (.FieldSelect (← translateExpr obj) attr.val)
  | .Subscript _ container slice _ => do
      let c ← translateExpr container
      let idx ← match slice with
        | .Slice _ start stop _ => do
          let s ← match start.val with
            | some e => mkExpr sr (.StaticCall "Any..as_int!" [← translateExpr e])
            | none => mkExpr sr (.LiteralInt 0)
          let e ← match stop.val with
            | some e => mkExpr sr (.StaticCall "OptSome" [← mkExpr sr (.StaticCall "Any..as_int!" [← translateExpr e])])
            | none => mkExpr sr (.StaticCall "OptNone" [])
          mkExpr sr (.StaticCall "from_Slice" [s, e])
        | _ => translateExpr slice
      mkExpr sr (.StaticCall "Any_get" [c, idx])
  | .List _ elts _ => do
      let es ← elts.val.toList.mapM translateExpr
      let nil ← mkExpr sr (.StaticCall "ListAny_nil" [])
      let cons ← es.foldrM (fun e acc => mkExpr sr (.StaticCall "ListAny_cons" [e, acc])) nil
      mkExpr sr (.StaticCall "from_ListAny" [cons])
  | .Tuple _ elts _ => do
      let es ← elts.val.toList.mapM translateExpr
      let nil ← mkExpr sr (.StaticCall "ListAny_nil" [])
      let cons ← es.foldrM (fun e acc => mkExpr sr (.StaticCall "ListAny_cons" [e, acc])) nil
      mkExpr sr (.StaticCall "from_ListAny" [cons])
  | .Dict _ keys vals => do
      let ks ← keys.val.toList.mapM (fun k => match k with
        | .some_expr _ e => translateExpr e | .missing_expr _ => mkExpr sr .Hole)
      let vs ← vals.val.toList.mapM translateExpr
      let empty ← mkExpr sr (.StaticCall "DictStrAny_empty" [])
      let cons ← (List.zip ks vs).foldrM (fun (k, v) acc =>
        mkExpr sr (.StaticCall "DictStrAny_cons" [k, v, acc])) empty
      mkExpr sr (.StaticCall "from_DictStrAny" [cons])
  | .IfExp _ test body orelse => do
      mkExpr sr (.IfThenElse (← translateExpr test) (← translateExpr body) (some (← translateExpr orelse)))
  | .JoinedStr _ values => do
      if values.val.isEmpty then mkExpr sr (.LiteralString "")
      else do
        let parts ← values.val.toList.mapM translateExpr
        let mut result ← mkExpr sr (.LiteralString "")
        for p in parts do result ← mkExpr sr (.StaticCall "PAdd" [result, p])
        pure result
  | .FormattedValue _ value _ _ => do
      mkExpr sr (.StaticCall "to_string_any" [← translateExpr value])
  | .Lambda _ _ _ => mkExpr sr .Hole
  | .Set _ _ => mkExpr sr .Hole
  | .ListComp _ _ _ => mkExpr sr .Hole
  | .SetComp _ _ _ => mkExpr sr .Hole
  | .DictComp _ _ _ _ => mkExpr sr .Hole
  | .GeneratorExp _ _ _ => mkExpr sr .Hole
  | .NamedExpr _ _ _ => mkExpr sr .Hole
  | .Slice _ _ _ _ => mkExpr sr .Hole
  | .Starred _ _ _ => mkExpr sr .Hole
  | .Await _ _ => mkExpr sr .Hole
  | .Yield _ _ => mkExpr sr .Hole
  | .YieldFrom _ _ => mkExpr sr .Hole
  | .TemplateStr _ _ => mkExpr sr .Hole
  | .Interpolation _ _ _ _ _ => mkExpr sr .Hole

where
  ann (e : Python.expr ResolvedAnn) : ResolvedAnn := match e with
    | .Name a .. => a | .Constant a .. => a | .BinOp a .. => a | .Compare a .. => a
    | .BoolOp a .. => a | .UnaryOp a .. => a | .Call a .. => a | .Attribute a .. => a
    | .Subscript a .. => a | .List a .. => a | .Tuple a .. => a | .Dict a .. => a
    | .Set a .. => a | .IfExp a .. => a | .JoinedStr a .. => a | .FormattedValue a .. => a
    | .Lambda a .. => a | .ListComp a .. => a | .SetComp a .. => a | .DictComp a .. => a
    | .GeneratorExp a .. => a | .NamedExpr a .. => a | .Slice a .. => a | .Starred a .. => a
    | .Await a .. => a | .Yield a .. => a | .YieldFrom a .. => a | .TemplateStr a .. => a
    | .Interpolation a .. => a

-- ═══════════════════════════════════════════════════════════════════════════════
-- translateCallExpr: isolated helper for call compositionality
-- Reads annotation. .function → StaticCall. .class_ → New. .unresolved → Hole.
-- ═══════════════════════════════════════════════════════════════════════════════

partial def translateCallExpr (sr : SourceRange) (callAnn : ResolvedAnn)
    (func : Python.expr ResolvedAnn)
    (args : Ann (Array (Python.expr ResolvedAnn)) ResolvedAnn)
    (kwargs : Ann (Array (Python.keyword ResolvedAnn)) ResolvedAnn) : TransM StmtExprMd := do
  let posArgs ← args.val.toList.mapM translateExpr
  let kwargPairs ← kwargs.val.toList.filterMapM fun kw => match kw with
    | .mk_keyword _ kwName kwExpr => do
      let val ← translateExpr kwExpr
      match kwName.val with | some n => pure (some (n.val, val)) | none => pure none
  match callAnn.info with
  | .function sig =>
      let calleeName := match func with
        | .Name _ n _ => pythonNameToLaurel n.val
        | .Attribute _ _ attr _ => attr.val
        | _ => "__indirect_call__"
      let matched := matchArgs sig posArgs kwargPairs
      mkExpr sr (.StaticCall calleeName matched)
  | .class_ className _ =>
      mkExpr sr (.New (Laurel.Identifier.mk className none))
  | _ => mkExpr sr (.Hole (deterministic := false))

-- ═══════════════════════════════════════════════════════════════════════════════
-- translateAssign: helper for assignment desugaring
-- Handles: simple, subscript write, tuple unpack, class instantiation
-- ═══════════════════════════════════════════════════════════════════════════════

partial def translateAssign (sr : SourceRange)
    (target : Python.expr ResolvedAnn) (value : Python.expr ResolvedAnn) : TransM (List StmtExprMd) := do
  match target with
  | .Tuple _ elts _ => do
      let rhsExpr ← translateExpr value
      let tmp ← freshId "unpack"
      let tmpDecl ← mkExpr sr (.LocalVariable tmp.text (mkTypeDefault (.TCore "Any")) (some rhsExpr))
      let tmpRef ← mkExpr sr (.Identifier tmp.text)
      pure ([tmpDecl] ++ (← unpackTargets sr elts.val.toList tmpRef))
  | .Subscript .. => do
      let (root, indices) ← collectSubscriptChain target
      let rootExpr ← translateExpr root
      let mut idxList ← mkExpr sr (.StaticCall "ListAny_nil" [])
      for idx in indices.reverse do
        let idxExpr ← match idx with
          | .Slice _ start stop _ => do
            let s' ← match start.val with
              | some e => mkExpr sr (.StaticCall "Any..as_int!" [← translateExpr e])
              | none => mkExpr sr (.LiteralInt 0)
            let e' ← match stop.val with
              | some e => mkExpr sr (.StaticCall "OptSome" [← mkExpr sr (.StaticCall "Any..as_int!" [← translateExpr e])])
              | none => mkExpr sr (.StaticCall "OptNone" [])
            mkExpr sr (.StaticCall "from_Slice" [s', e'])
          | _ => translateExpr idx
        idxList ← mkExpr sr (.StaticCall "ListAny_cons" [idxExpr, idxList])
      let rhs ← translateExpr value
      let setsCall ← mkExpr sr (.StaticCall "Any_sets" [idxList, rootExpr, rhs])
      pure [← mkExpr sr (.Assign [rootExpr] setsCall)]
  | _ =>
      match value with
      | .Call ann (.Name _ calleeName _) callArgs callKwargs =>
        match ann.info with
        | .class_ className _ => do
            let targetExpr ← translateExpr target
            let classId := Laurel.Identifier.mk className none
            let assignNew ← mkExpr sr (.Assign [targetExpr] (← mkExpr sr (.New classId)))
            let posArgs ← callArgs.val.toList.mapM translateExpr
            let kwargPairs ← callKwargs.val.toList.filterMapM fun kw => match kw with
              | .mk_keyword _ kwName kwExpr => do
                let val ← translateExpr kwExpr
                match kwName.val with | some n => pure (some (n.val, val)) | none => pure none
            let initName := s!"{className}@__init__"
            let initCall ← mkExpr sr (.StaticCall initName (targetExpr :: posArgs))
            pure [assignNew, initCall]
        | _ => do
            pure [← mkExpr sr (.Assign [← translateExpr target] (← translateExpr value))]
      | _ => do
          pure [← mkExpr sr (.Assign [← translateExpr target] (← translateExpr value))]

partial def unpackTargets (sr : SourceRange) (elts : List (Python.expr ResolvedAnn))
    (sourceRef : StmtExprMd) : TransM (List StmtExprMd) := do
  let mut stmts : List StmtExprMd := []
  let mut idx : Int := 0
  for elt in elts do
    let getExpr ← mkExpr sr (.StaticCall "Any_get" [sourceRef, ← mkExpr sr (.LiteralInt idx)])
    match elt with
    | .Tuple _ innerElts _ => do
      let innerTmp ← freshId "unpack"
      let innerRef ← mkExpr sr (.Identifier innerTmp.text)
      let innerDecl ← mkExpr sr (.LocalVariable innerTmp.text (mkTypeDefault (.TCore "Any")) (some getExpr))
      stmts := stmts ++ [innerDecl]
      stmts := stmts ++ (← unpackTargets sr innerElts.val.toList innerRef)
    | _ => do
      let tgt ← translateExpr elt
      stmts := stmts ++ [← mkExpr sr (.Assign [tgt] getExpr)]
    idx := idx + 1
  pure stmts

partial def collectSubscriptChain (expr : Python.expr ResolvedAnn) : TransM (Python.expr ResolvedAnn × List (Python.expr ResolvedAnn)) := do
  match expr with
  | .Subscript _ container slice _ =>
    let (root, innerIndices) ← collectSubscriptChain container
    pure (root, innerIndices ++ [slice])
  | other => pure (other, [])

-- ═══════════════════════════════════════════════════════════════════════════════
-- translateStmt: one case per constructor
-- ═══════════════════════════════════════════════════════════════════════════════

partial def translateStmtList (stmts : List (Python.stmt ResolvedAnn)) : TransM (List StmtExprMd) := do
  let mut result : List StmtExprMd := []
  for stmt in stmts do result := result ++ (← translateStmt stmt)
  return result

partial def translateStmt (s : Python.stmt ResolvedAnn) : TransM (List StmtExprMd) := do
  let sr := s.ann.sr
  match s with
  | .Assign _ targets value _ => do
      if targets.val.size != 1 then throw (.unsupportedConstruct "Multiple assignment targets")
      translateAssign sr targets.val[0]! value

  | .AnnAssign _ target _annotation value _ => do
      match value.val with
      | some val => translateAssign sr target val
      | none => pure []

  | .AugAssign _ target op value => do
      let t ← translateExpr target; let v ← translateExpr value
      let opName := match op with
        | .Add _ => "PAdd" | .Sub _ => "PSub" | .Mult _ => "PMul" | .Div _ => "PDiv"
        | .FloorDiv _ => "PFloorDiv" | .Mod _ => "PMod" | .Pow _ => "PPow"
        | .BitAnd _ => "PBitAnd" | .BitOr _ => "PBitOr" | .BitXor _ => "PBitXor"
        | .LShift _ => "PLShift" | .RShift _ => "PRShift" | .MatMult _ => "PMatMul"
      pure [← mkExpr sr (.Assign [t] (← mkExpr sr (.StaticCall opName [t, v])))]

  | .If _ test body orelse => do
      let cond ← translateExpr test
      let thn ← mkExpr sr (.Block (← translateStmtList body.val.toList) none)
      let els ← if orelse.val.isEmpty then pure none
        else pure (some (← mkExpr sr (.Block (← translateStmtList orelse.val.toList) none)))
      pure [← mkExpr sr (.IfThenElse cond thn els)]

  | .While _ test body _ => do
      let (bk, ct) ← pushLoopLabel "loop"
      let cond ← translateExpr test
      let inner ← mkExpr sr (.Block (← translateStmtList body.val.toList) (some ct.text))
      let outer ← mkExpr sr (.Block [← mkExpr sr (.While cond [] none inner)] (some bk.text))
      popLoopLabel; pure [outer]

  | .For _ target iter body _ _ => do
      let (bk, ct) ← pushLoopLabel "for"
      let iterExpr ← translateExpr iter
      let bodyStmts ← translateStmtList body.val.toList
      let (havocStmts, assumeTarget) ← match target with
        | .Tuple _ elts _ => do
          let tmp ← freshId "for_iter"
          let tmpRef ← mkExpr sr (.Identifier tmp.text)
          let havoc ← mkExpr sr (.Assign [tmpRef] (← mkExpr sr (.Hole (deterministic := false))))
          let unpacks ← unpackTargets sr elts.val.toList tmpRef
          pure ([havoc] ++ unpacks, tmpRef)
        | _ => do
          let tgt ← translateExpr target
          let havoc ← mkExpr sr (.Assign [tgt] (← mkExpr sr (.Hole (deterministic := false))))
          pure ([havoc], tgt)
      let assume ← mkExpr sr (.Assume (← mkExpr sr (.StaticCall "PIn" [assumeTarget, iterExpr])))
      let inner ← mkExpr sr (.Block (havocStmts ++ [assume] ++ bodyStmts) (some ct.text))
      let outer ← mkExpr sr (.Block [inner] (some bk.text))
      popLoopLabel; pure [outer]

  | .Return _ value => do
      match value.val with
      | some expr => do
        let e ← translateExpr expr
        pure [← mkExpr sr (.Assign [← mkExpr sr (.Identifier "LaurelResult")] e), ← mkExpr sr (.Exit "$body")]
      | none => pure [← mkExpr sr (.Exit "$body")]

  | .Assert _ test _ => pure [← mkExpr sr (.Assert (← translateExpr test))]
  | .Expr _ (.Constant _ (.ConString _ _) _) => pure []
  | .Expr _ value => pure [← translateExpr value]
  | .Pass _ => pure []
  | .Break _ => do pure [← mkExpr sr (.Exit ((← currentBreakLabel).map (·.text) |>.getD "break"))]
  | .Continue _ => do pure [← mkExpr sr (.Exit ((← currentContinueLabel).map (·.text) |>.getD "continue"))]

  | .Try _ body handlers _ _ => translateTryExcept sr body handlers
  | .TryStar _ body handlers _ _ => translateTryExcept sr body handlers

  | .With _ items body _ => do
      let mut pre : List StmtExprMd := []
      let mut post : List StmtExprMd := []
      for item in items.val do
        match item with
        | .mk_withitem _ ctxExpr optVars => do
          let ctxVal ← translateExpr ctxExpr
          let enter ← mkExpr sr (.Hole (deterministic := false))
          let exit ← mkExpr sr (.Hole (deterministic := false))
          match optVars.val with
          | some varExpr => pre := pre ++ [← mkExpr sr (.Assign [← translateExpr varExpr] enter)]
          | none => pre := pre ++ [enter]
          post := post ++ [exit]
          let _ := ctxVal
      pure (pre ++ (← translateStmtList body.val.toList) ++ post)

  | .Raise _ exc _ => do
      match exc.val with
      | some excExpr => do
        let errorExpr ← match excExpr with
          | .Call _ (.Name _ excName _) excArgs _ => do
            let ctor := match excName.val with
              | "TypeError" => "TypeError" | "AttributeError" => "AttributeError"
              | "AssertionError" => "AssertionError" | "IndexError" => "IndexError"
              | _ => "UnimplementedError"
            let msg ← if excArgs.val.size > 0 then translateExpr excArgs.val[0]!
              else mkExpr sr (.LiteralString "")
            mkExpr sr (.StaticCall ctor [msg])
          | _ => mkExpr sr (.StaticCall "UnimplementedError" [← translateExpr excExpr])
        pure [← mkExpr sr (.Assign [← mkExpr sr (.Identifier "maybe_except")] errorExpr)]
      | none =>
        pure [← mkExpr sr (.Assign [← mkExpr sr (.Identifier "maybe_except")]
          (← mkExpr sr (.StaticCall "UnimplementedError" [mkExprDefault (.LiteralString "re-raise")])))]

  | .Import _ _ => pure []
  | .ImportFrom _ _ _ _ => pure []
  | .Global _ _ => pure []
  | .Nonlocal _ _ => pure []
  | .Delete _ _ => pure []
  | .AsyncFor _ _ _ _ _ _ => pure [← mkExpr sr .Hole]
  | .AsyncWith _ _ _ _ => pure [← mkExpr sr .Hole]
  | .Match _ _ _ => pure [← mkExpr sr .Hole]
  | .TypeAlias _ _ _ _ => pure []
  | .FunctionDef _ _ _ _ _ _ _ _ => pure []
  | .AsyncFunctionDef _ _ _ _ _ _ _ _ => pure []
  | .ClassDef _ _ _ _ _ _ _ => pure []

where
  ann (s : Python.stmt ResolvedAnn) : ResolvedAnn := match s with
    | .FunctionDef a .. => a | .AsyncFunctionDef a .. => a | .ClassDef a .. => a
    | .Return a .. => a | .Delete a .. => a | .Assign a .. => a | .AugAssign a .. => a
    | .AnnAssign a .. => a | .For a .. => a | .AsyncFor a .. => a | .While a .. => a
    | .If a .. => a | .With a .. => a | .AsyncWith a .. => a | .Raise a .. => a
    | .Try a .. => a | .TryStar a .. => a | .Assert a .. => a | .Import a .. => a
    | .ImportFrom a .. => a | .Global a .. => a | .Nonlocal a .. => a | .Expr a .. => a
    | .Pass a => { sr := a.sr, info := .none } | .Break a => { sr := a.sr, info := .none }
    | .Continue a => { sr := a.sr, info := .none } | .Match a .. => a | .TypeAlias a .. => a

-- ═══════════════════════════════════════════════════════════════════════════════
-- translateTryExcept: labeled blocks + isError guards
-- ═══════════════════════════════════════════════════════════════════════════════

partial def translateTryExcept (sr : SourceRange)
    (body : Ann (Array (Python.stmt ResolvedAnn)) ResolvedAnn)
    (handlers : Ann (Array (Python.excepthandler ResolvedAnn)) ResolvedAnn) : TransM (List StmtExprMd) := do
  let tryLabel := s!"try_end_{sr.start.byteIdx}"
  let catchersLabel := s!"exception_handlers_{sr.start.byteIdx}"
  let bodyStmts ← translateStmtList body.val.toList
  let mut withChecks : List StmtExprMd := []
  for stmt in bodyStmts do
    withChecks := withChecks ++ [stmt]
    let ref ← mkExpr sr (.Identifier "maybe_except")
    let check ← mkExpr sr (.StaticCall "isError" [ref])
    withChecks := withChecks ++ [← mkExpr sr (.IfThenElse check (← mkExpr sr (.Exit catchersLabel)) none)]
  let exitTry ← mkExpr sr (.Exit tryLabel)
  let catchers ← mkExpr sr (.Block (withChecks ++ [exitTry]) (some catchersLabel))
  let mut handlerStmts : List StmtExprMd := []
  for handler in handlers.val do
    match handler with
    | .ExceptHandler _ _ _ handlerBody =>
      handlerStmts := handlerStmts ++ (← translateStmtList handlerBody.val.toList)
  pure [← mkExpr sr (.Block ([catchers] ++ handlerStmts) (some tryLabel))]

-- ═══════════════════════════════════════════════════════════════════════════════
-- translateFunction: reads FuncSig from annotation
-- ═══════════════════════════════════════════════════════════════════════════════

partial def translateFunction (funcAnn : ResolvedAnn) (procName : String)
    (sig : FuncSig) (body : Array (Python.stmt ResolvedAnn)) : TransM Procedure := do
  let sr := funcAnn.sr
  let inputs : List Laurel.Parameter := sig.params.map fun (pName, pTy) =>
    { name := Laurel.Identifier.mk pName none, type := mkTypeDefault (pythonTypeToHighType pTy) }
  let outputs : List Laurel.Parameter :=
    [{ name := Laurel.Identifier.mk "LaurelResult" none, type := mkTypeDefault (pythonTypeToHighType sig.returnType) },
     { name := Laurel.Identifier.mk "maybe_except" none, type := mkTypeDefault (.TCore "Error") }]
  let localDecls := sig.locals.map fun (lName, lTy) =>
    mkExprDefault (.LocalVariable (Laurel.Identifier.mk lName none) (mkTypeDefault (pythonTypeToHighType lTy)) none)
  let bodyStmts ← translateStmtList body.toList
  let bodyBlock ← mkExpr sr (.Block (localDecls ++ bodyStmts) none)
  let md := sourceRangeToMd (← get).filePath sr
  pure {
    name := Laurel.Identifier.mk procName none
    inputs := inputs
    outputs := outputs
    preconditions := []
    determinism := .deterministic none
    decreases := none
    isFunctional := false
    body := .Transparent bodyBlock
    md := md
  }

-- ═══════════════════════════════════════════════════════════════════════════════
-- translateClass: reads .class_ from annotation
-- ═══════════════════════════════════════════════════════════════════════════════

partial def translateClass (className : String)
    (fields : List (Resolution.Identifier × PythonType))
    (body : Array (Python.stmt ResolvedAnn)) : TransM (TypeDefinition × List Procedure) := do
  let laurelFields := fields.map fun (fName, fTy) =>
    ({ name := Laurel.Identifier.mk fName none, isMutable := true, type := mkTypeDefault (pythonTypeToHighType fTy) } : Field)
  let mut methods : List Procedure := []
  for stmt in body do
    match stmt with
    | .FunctionDef ann fname _ fbody _ _ _ _ =>
      match ann.info with
      | .function sig =>
        let proc ← translateFunction ann s!"{className}@{fname.val}" sig fbody.val
        methods := methods ++ [proc]
      | _ => pure ()
    | .AsyncFunctionDef ann fname _ fbody _ _ _ _ =>
      match ann.info with
      | .function sig =>
        let proc ← translateFunction ann s!"{className}@{fname.val}" sig fbody.val
        methods := methods ++ [proc]
      | _ => pure ()
    | _ => pure ()
  let ct : CompositeType := { name := Laurel.Identifier.mk className none, extending := [], fields := laurelFields, instanceProcedures := [] }
  pure (.Composite ct, methods)

-- ═══════════════════════════════════════════════════════════════════════════════
-- translateModule: top-level fold
-- ═══════════════════════════════════════════════════════════════════════════════

partial def translateModule (stmts : ResolvedPythonProgram) : TransM Laurel.Program := do
  let mut procedures : List Procedure := []
  let mut types : List TypeDefinition := []
  let mut otherStmts : List (Python.stmt ResolvedAnn) := []
  for stmt in stmts do
    match stmt with
    | .FunctionDef ann name _ body _ _ _ _ =>
      match ann.info with
      | .function sig =>
        let proc ← translateFunction ann name.val sig body.val
        procedures := procedures ++ [proc]
      | _ => pure ()
    | .AsyncFunctionDef ann name _ body _ _ _ _ =>
      match ann.info with
      | .function sig =>
        let proc ← translateFunction ann name.val sig body.val
        procedures := procedures ++ [proc]
      | _ => pure ()
    | .ClassDef ann _name _ _ body _ _ =>
      match ann.info with
      | .class_ className fields =>
        let (td, ms) ← translateClass className fields body.val
        types := types ++ [td]
        procedures := procedures ++ ms
      | _ => pure ()
    | _ => otherStmts := otherStmts ++ [stmt]
  if !otherStmts.isEmpty then
    let sr : SourceRange := default
    let nameDecl ← mkExpr sr (.LocalVariable "__name__" (mkTypeDefault .TString) (some (mkExprDefault (.LiteralString "__main__"))))
    let moduleLocals := collectModuleLocals otherStmts
    let localDecls := moduleLocals.map fun (lName, _) =>
      mkExprDefault (.LocalVariable (Laurel.Identifier.mk lName none) (mkTypeDefault (.TCore "Any")) none)
    let bodyStmts ← translateStmtList otherStmts
    let bodyBlock ← mkExpr sr (.Block ([nameDecl] ++ localDecls ++ bodyStmts) none)
    let mainOutputs : List Laurel.Parameter :=
      [{ name := Laurel.Identifier.mk "LaurelResult" none, type := mkTypeDefault (.TCore "Any") },
       { name := Laurel.Identifier.mk "maybe_except" none, type := mkTypeDefault (.TCore "Error") }]
    let mainMd := sourceRangeToMd (← get).filePath sr
    let mainProc : Procedure := { name := Laurel.Identifier.mk "__main__" none, inputs := [], outputs := mainOutputs, preconditions := [], determinism := .deterministic none, decreases := none, isFunctional := false, body := .Transparent bodyBlock, md := mainMd }
    procedures := procedures ++ [mainProc]
  return { staticProcedures := procedures, staticFields := [], types, constants := [] }

end -- mutual

-- ═══════════════════════════════════════════════════════════════════════════════
-- Runner
-- ═══════════════════════════════════════════════════════════════════════════════

def runTranslation (stmts : ResolvedPythonProgram)
    (filePath : String := "")
    : Except TransError (Laurel.Program × TransState) :=
  (translateModule stmts).run { filePath := filePath }

end -- public section
end Strata.Python.Translation
