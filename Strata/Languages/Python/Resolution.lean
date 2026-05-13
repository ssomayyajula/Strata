/-
  Copyright Strata Contributors
  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.Laurel
public import Strata.Languages.Python.PythonDialect
import Strata.DDM.Util.SourceRange

/-!
# Pass 1: Name Resolution

Fold over the Python AST that threads a growing context as accumulator.
Each declaration extends the context; each reference is annotated with
its resolution from the current context.

Input:  PythonProgram
Output: ResolvedPythonProgram

The output AST is the scoping derivation for the Python program —
every node carries proof of what it refers to.
-/

namespace Strata.Python.Resolution

open Strata.Laurel

public section

-- ═══════════════════════════════════════════════════════════════════════════════
-- Core Types
-- ═══════════════════════════════════════════════════════════════════════════════

abbrev PythonExpr := Python.expr SourceRange
abbrev PythonStmt := Python.stmt SourceRange
abbrev PythonProgram := Array PythonStmt
abbrev PythonType := PythonExpr
structure PythonIdentifier where
  private mk ::
  val : String
  deriving BEq, Hashable, Inhabited, Repr

def PythonIdentifier.fromAst (n : Ann String SourceRange) : PythonIdentifier :=
  ⟨n.val⟩

def PythonIdentifier.fromImport (modName : Ann String SourceRange) : PythonIdentifier :=
  match modName.val.splitOn "." with
  | first :: _ => ⟨first⟩
  | [] => ⟨modName.val⟩

def PythonIdentifier.builtin (name : String) : PythonIdentifier :=
  ⟨name⟩

structure FuncSig where
  name : Laurel.Identifier
  params : List (Laurel.Identifier × PythonType)
  defaults : List (Laurel.Identifier × PythonExpr)
  returnType : PythonType
  locals : List (Laurel.Identifier × PythonType)
  deriving Inhabited

inductive NodeInfo where
  | variable (id : Laurel.Identifier)
  | call (callee : Laurel.Identifier) (sig : FuncSig)
  | classNew (cls : Laurel.Identifier) (init : Laurel.Identifier) (sig : FuncSig)
  | operator (callee : Laurel.Identifier)
  | fieldAccess (field : Laurel.Identifier)
  | funcDecl (sig : FuncSig)
  | classDecl (name : Laurel.Identifier) (fields : List (Laurel.Identifier × PythonType)) (methods : List FuncSig)
  | unresolved
  | irrelevant
  deriving Inhabited

structure ResolvedAnn where
  sr : SourceRange
  info : NodeInfo
  deriving Inhabited

instance : Inhabited ResolvedAnn where
  default := { sr := .none, info := .irrelevant }

abbrev ResolvedPythonStmt := Python.stmt ResolvedAnn
abbrev ResolvedPythonExpr := Python.expr ResolvedAnn

structure ResolvedPythonProgram where
  stmts : Array ResolvedPythonStmt
  moduleLocals : List (Laurel.Identifier × PythonType)

-- ═══════════════════════════════════════════════════════════════════════════════
-- Internal Context (Resolution's working state — not exposed to Translation)
-- ═══════════════════════════════════════════════════════════════════════════════

inductive CtxEntry where
  | function (sig : FuncSig)
  | class_ (name : PythonIdentifier) (fields : List (PythonIdentifier × PythonType)) (methods : List (PythonIdentifier × FuncSig))
  | variable (ty : PythonType)
  | module_ (name : PythonIdentifier)
  | unresolved
  deriving Inhabited

abbrev Ctx := Std.HashMap PythonIdentifier CtxEntry

private def mkLaurelId (name : String) : Laurel.Identifier :=
  { text := name, uniqueId := none }

-- ═══════════════════════════════════════════════════════════════════════════════
-- Annotation Extraction
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Extract a PythonType from an optional annotation. No annotation defaults to Any. -/
def annotationToPythonType (ann : Option PythonExpr) : PythonType :=
  match ann with
  | some expr => expr
  | none => .Name SourceRange.none ⟨SourceRange.none, "Any"⟩ (.Load SourceRange.none)

-- ═══════════════════════════════════════════════════════════════════════════════
-- Function Locals (Python scoping: assignment anywhere in body → function-local)
-- ═══════════════════════════════════════════════════════════════════════════════

mutual
partial def collectWalrusFromComprehensions (comps : List (Python.comprehension SourceRange)) : List PythonIdentifier :=
  comps.flatMap fun comp =>
    match comp with
    | .mk_comprehension _ _target iter ifs _isAsync =>
        collectWalrusNames iter ++ ifs.val.toList.flatMap collectWalrusNames

partial def collectNamesFromTarget (target : PythonExpr) : List PythonIdentifier :=
  match target with
  | .Name _ n _ => [PythonIdentifier.fromAst n]
  | .Tuple _ elems _ => elems.val.toList.flatMap collectNamesFromTarget
  | .List _ elems _ => elems.val.toList.flatMap collectNamesFromTarget
  | .Starred _ inner _ => collectNamesFromTarget inner
  | .Subscript _ _ _ _ => []
  | .Attribute _ _ _ _ => []
  | e => collectWalrusNames e

partial def collectWalrusNames (expr : PythonExpr) : List PythonIdentifier :=
  match expr with
  | .NamedExpr _ target _ => collectNamesFromTarget target
  | .BinOp _ left _ right => collectWalrusNames left ++ collectWalrusNames right
  | .BoolOp _ _ operands => operands.val.toList.flatMap collectWalrusNames
  | .UnaryOp _ _ operand => collectWalrusNames operand
  | .Compare _ left _ comparators => collectWalrusNames left ++ comparators.val.toList.flatMap collectWalrusNames
  | .Call _ func args kwargs =>
      collectWalrusNames func ++ args.val.toList.flatMap collectWalrusNames ++
      kwargs.val.toList.flatMap fun kw => match kw with | .mk_keyword _ _ val => collectWalrusNames val
  | .IfExp _ test body orelse => collectWalrusNames test ++ collectWalrusNames body ++ collectWalrusNames orelse
  | .Dict _ keys vals => keys.val.toList.flatMap (fun k => match k with | .some_expr _ e => collectWalrusNames e | .missing_expr _ => []) ++ vals.val.toList.flatMap collectWalrusNames
  | .Set _ elts => elts.val.toList.flatMap collectWalrusNames
  | .ListComp _ elt generators => collectWalrusNames elt ++ collectWalrusFromComprehensions generators.val.toList
  | .SetComp _ elt generators => collectWalrusNames elt ++ collectWalrusFromComprehensions generators.val.toList
  | .DictComp _ key value generators => collectWalrusNames key ++ collectWalrusNames value ++ collectWalrusFromComprehensions generators.val.toList
  | .GeneratorExp _ elt generators => collectWalrusNames elt ++ collectWalrusFromComprehensions generators.val.toList
  | .Await _ inner => collectWalrusNames inner
  | .Yield _ valOpt => match valOpt.val with | some v => collectWalrusNames v | none => []
  | .YieldFrom _ inner => collectWalrusNames inner
  | .FormattedValue _ value _ _ => collectWalrusNames value
  | .JoinedStr _ values => values.val.toList.flatMap collectWalrusNames
  | .Subscript _ obj slice _ => collectWalrusNames obj ++ collectWalrusNames slice
  | .Attribute _ obj _ _ => collectWalrusNames obj
  | .Starred _ inner _ => collectWalrusNames inner
  | .Tuple _ elems _ => elems.val.toList.flatMap collectWalrusNames
  | .List _ elems _ => elems.val.toList.flatMap collectWalrusNames
  | .Slice _ start stop step =>
      (match start.val with | some e => collectWalrusNames e | none => []) ++
      (match stop.val with | some e => collectWalrusNames e | none => []) ++
      (match step.val with | some e => collectWalrusNames e | none => [])
  | .Name _ _ _ => []
  | .Constant _ _ _ => []
  | .Lambda _ _ _ => []
  | .TemplateStr _ _ => []
  | .Interpolation _ _ _ _ _ => []
end

partial def collectLocalsFromStmt (s : PythonStmt) : List (PythonIdentifier × PythonType) :=
  match s with
  | .Assign _ targets value _ =>
      let targetNames := targets.val.toList.flatMap fun target =>
        (collectNamesFromTarget target).map fun n => (n, annotationToPythonType none)
      let rhsWalrus := (collectWalrusNames value).map fun n => (n, annotationToPythonType none)
      targetNames ++ rhsWalrus
  | .AnnAssign _ target annotation valueOpt _ =>
      let targetNames := (collectNamesFromTarget target).map fun n => (n, annotation)
      let rhsWalrus := match valueOpt.val with
        | some v => (collectWalrusNames v).map fun n => (n, annotationToPythonType none)
        | none => []
      targetNames ++ rhsWalrus
  | .AugAssign _ target _ value =>
      let targetNames := (collectNamesFromTarget target).map fun n => (n, annotationToPythonType none)
      let rhsWalrus := (collectWalrusNames value).map fun n => (n, annotationToPythonType none)
      targetNames ++ rhsWalrus
  | .If _ test bodyStmts elseStmts =>
      (collectWalrusNames test).map (fun n => (n, annotationToPythonType none)) ++
      bodyStmts.val.toList.flatMap collectLocalsFromStmt ++
      elseStmts.val.toList.flatMap collectLocalsFromStmt
  | .For _ target iter bodyStmts orelse _ =>
      let targetNames := (collectNamesFromTarget target).map fun n => (n, annotationToPythonType none)
      let iterWalrus := (collectWalrusNames iter).map fun n => (n, annotationToPythonType none)
      targetNames ++ iterWalrus ++
      bodyStmts.val.toList.flatMap collectLocalsFromStmt ++
      orelse.val.toList.flatMap collectLocalsFromStmt
  | .While _ cond bodyStmts orelse =>
      (collectWalrusNames cond).map (fun n => (n, annotationToPythonType none)) ++
      bodyStmts.val.toList.flatMap collectLocalsFromStmt ++
      orelse.val.toList.flatMap collectLocalsFromStmt
  | .Try _ bodyStmts handlers orelse finalbody =>
      let handlerLocals := handlers.val.toList.flatMap fun h =>
        match h with
        | .ExceptHandler _ _ maybeName handlerBody =>
            let errorVar := match maybeName.val with
              | some n => [(PythonIdentifier.fromAst n, annotationToPythonType none)]
              | none => []
            errorVar ++ handlerBody.val.toList.flatMap collectLocalsFromStmt
      bodyStmts.val.toList.flatMap collectLocalsFromStmt ++
      handlerLocals ++
      orelse.val.toList.flatMap collectLocalsFromStmt ++
      finalbody.val.toList.flatMap collectLocalsFromStmt
  | .TryStar _ bodyStmts handlers orelse finalbody =>
      let handlerLocals := handlers.val.toList.flatMap fun h =>
        match h with
        | .ExceptHandler _ _ maybeName handlerBody =>
            let errorVar := match maybeName.val with
              | some n => [(PythonIdentifier.fromAst n, annotationToPythonType none)]
              | none => []
            errorVar ++ handlerBody.val.toList.flatMap collectLocalsFromStmt
      bodyStmts.val.toList.flatMap collectLocalsFromStmt ++
      handlerLocals ++
      orelse.val.toList.flatMap collectLocalsFromStmt ++
      finalbody.val.toList.flatMap collectLocalsFromStmt
  | .With _ items bodyStmts _ =>
      let itemLocals := items.val.toList.flatMap fun item =>
        match item with
        | .mk_withitem _ ctxExpr optVars =>
            let ctxWalrus := (collectWalrusNames ctxExpr).map fun n => (n, annotationToPythonType none)
            let varNames := match optVars.val with
              | some varExpr => (collectNamesFromTarget varExpr).map fun n => (n, annotationToPythonType none)
              | none => []
            ctxWalrus ++ varNames
      itemLocals ++ bodyStmts.val.toList.flatMap collectLocalsFromStmt
  | .AsyncWith _ items bodyStmts _ =>
      let itemLocals := items.val.toList.flatMap fun item =>
        match item with
        | .mk_withitem _ ctxExpr optVars =>
            let ctxWalrus := (collectWalrusNames ctxExpr).map fun n => (n, annotationToPythonType none)
            let varNames := match optVars.val with
              | some varExpr => (collectNamesFromTarget varExpr).map fun n => (n, annotationToPythonType none)
              | none => []
            ctxWalrus ++ varNames
      itemLocals ++ bodyStmts.val.toList.flatMap collectLocalsFromStmt
  | .AsyncFor _ target iter bodyStmts orelse _ =>
      let targetNames := (collectNamesFromTarget target).map fun n => (n, annotationToPythonType none)
      let iterWalrus := (collectWalrusNames iter).map fun n => (n, annotationToPythonType none)
      targetNames ++ iterWalrus ++
      bodyStmts.val.toList.flatMap collectLocalsFromStmt ++
      orelse.val.toList.flatMap collectLocalsFromStmt
  | .Match _ subject cases =>
      let subjectW := (collectWalrusNames subject).map fun n => (n, annotationToPythonType none)
      let caseLocals := cases.val.toList.flatMap fun c =>
        match c with
        | .mk_match_case _ _pattern guardOpt caseBody =>
            -- TODO: extract pattern bindings from _pattern (requires walking Python.pattern)
            let guardW := match guardOpt.val with
              | some g => (collectWalrusNames g).map fun n => (n, annotationToPythonType none)
              | none => []
            guardW ++ caseBody.val.toList.flatMap collectLocalsFromStmt
      subjectW ++ caseLocals
  | .FunctionDef _ name _ _ _ _ _ _ => [(PythonIdentifier.fromAst name, annotationToPythonType none)]
  | .AsyncFunctionDef _ name _ _ _ _ _ _ => [(PythonIdentifier.fromAst name, annotationToPythonType none)]
  | .ClassDef _ name _ _ _ _ _ => [(PythonIdentifier.fromAst name, annotationToPythonType none)]
  | .Return _ valOpt =>
      match valOpt.val with
      | some v => (collectWalrusNames v).map (fun n => (n, annotationToPythonType none))
      | none => []
  | .Delete _ targets =>
      targets.val.toList.flatMap fun t => (collectWalrusNames t).map fun n => (n, annotationToPythonType none)
  | .Raise _ excOpt causeOpt =>
      let excW := match excOpt.val with | some e => collectWalrusNames e | none => []
      let causeW := match causeOpt.val with | some e => collectWalrusNames e | none => []
      (excW ++ causeW).map fun n => (n, annotationToPythonType none)
  | .Assert _ test msgOpt =>
      let testW := collectWalrusNames test
      let msgW := match msgOpt.val with | some e => collectWalrusNames e | none => []
      (testW ++ msgW).map fun n => (n, annotationToPythonType none)
  | .Pass _ => []
  | .Break _ => []
  | .Continue _ => []
  | .Import _ aliases =>
      aliases.val.toList.filterMap fun alias =>
        match alias with
        | .mk_alias _ modName asName =>
            let id := match asName.val with
              | some aliasName => PythonIdentifier.fromAst aliasName
              | none => PythonIdentifier.fromImport modName
            some (id, annotationToPythonType none)
  | .ImportFrom _ _ imports _ =>
      imports.val.toList.filterMap fun imp =>
        match imp with
        | .mk_alias _ impName asName =>
            let id := match asName.val with
              | some aliasName => PythonIdentifier.fromAst aliasName
              | none => PythonIdentifier.fromAst impName
            some (id, annotationToPythonType none)
  | .Global _ _ => []
  | .Nonlocal _ _ => []
  | .Expr _ value =>
      (collectWalrusNames value).map (fun n => (n, annotationToPythonType none))
  | .TypeAlias _ nameExpr _ _ =>
      (collectNamesFromTarget nameExpr).map fun n => (n, annotationToPythonType none)

partial def collectGlobalNonlocalNames (s : PythonStmt) : List PythonIdentifier :=
  match s with
  | .Global _ names => names.val.toList.map PythonIdentifier.fromAst
  | .Nonlocal _ names => names.val.toList.map PythonIdentifier.fromAst
  | .If _ _ body orelse =>
      body.val.toList.flatMap collectGlobalNonlocalNames ++
      orelse.val.toList.flatMap collectGlobalNonlocalNames
  | .For _ _ _ body orelse _ =>
      body.val.toList.flatMap collectGlobalNonlocalNames ++
      orelse.val.toList.flatMap collectGlobalNonlocalNames
  | .AsyncFor _ _ _ body orelse _ =>
      body.val.toList.flatMap collectGlobalNonlocalNames ++
      orelse.val.toList.flatMap collectGlobalNonlocalNames
  | .While _ _ body orelse =>
      body.val.toList.flatMap collectGlobalNonlocalNames ++
      orelse.val.toList.flatMap collectGlobalNonlocalNames
  | .Try _ body handlers orelse finalbody =>
      body.val.toList.flatMap collectGlobalNonlocalNames ++
      handlers.val.toList.flatMap (fun h => match h with
        | .ExceptHandler _ _ _ hBody => hBody.val.toList.flatMap collectGlobalNonlocalNames) ++
      orelse.val.toList.flatMap collectGlobalNonlocalNames ++
      finalbody.val.toList.flatMap collectGlobalNonlocalNames
  | .TryStar _ body handlers orelse finalbody =>
      body.val.toList.flatMap collectGlobalNonlocalNames ++
      handlers.val.toList.flatMap (fun h => match h with
        | .ExceptHandler _ _ _ hBody => hBody.val.toList.flatMap collectGlobalNonlocalNames) ++
      orelse.val.toList.flatMap collectGlobalNonlocalNames ++
      finalbody.val.toList.flatMap collectGlobalNonlocalNames
  | .With _ _ body _ => body.val.toList.flatMap collectGlobalNonlocalNames
  | .AsyncWith _ _ body _ => body.val.toList.flatMap collectGlobalNonlocalNames
  | .Match _ _ cases =>
      cases.val.toList.flatMap fun c => match c with
        | .mk_match_case _ _ _ caseBody => caseBody.val.toList.flatMap collectGlobalNonlocalNames
  | _ => []

def computeLocals (body : PythonProgram) (paramNames : List PythonIdentifier)
    : List (PythonIdentifier × PythonType) :=
  let allPairs := body.toList.flatMap collectLocalsFromStmt
  let globalNonlocal := body.toList.flatMap collectGlobalNonlocalNames
  let excluded : Std.HashSet PythonIdentifier := (paramNames ++ globalNonlocal).foldl (fun s n => s.insert n) {}
  let (_, result) := allPairs.foldl (init := (excluded, ([] : List (PythonIdentifier × PythonType)))) fun acc pair =>
    let (seen, result) := acc
    let (name, ty) := pair
    if seen.contains name then (seen, result)
    else (seen.insert name, result ++ [(name, ty)])
  result

-- ═══════════════════════════════════════════════════════════════════════════════
-- Extract FuncSig from a Python FunctionDef
-- ═══════════════════════════════════════════════════════════════════════════════

private def argToParam (arg : Python.arg SourceRange) : PythonIdentifier × PythonType :=
  match arg with
  | .mk_arg _ argName annotation _ => (PythonIdentifier.fromAst argName, annotationToPythonType annotation.val)

def extractParams (args : Python.arguments SourceRange) : List (PythonIdentifier × PythonType) :=
  match args with
  | .mk_arguments _ posonlyargs argList _vararg kwonlyargs _ _kwarg _ =>
      posonlyargs.val.toList.map argToParam ++
      argList.val.toList.map argToParam ++
      kwonlyargs.val.toList.map argToParam

private def extractAllParamNames (args : Python.arguments SourceRange) : List PythonIdentifier :=
  match args with
  | .mk_arguments _ posonlyargs argList vararg kwonlyargs _ kwarg _ =>
      let names := (posonlyargs.val.toList ++ argList.val.toList ++ kwonlyargs.val.toList).map fun arg =>
        match arg with | .mk_arg _ argName _ _ => PythonIdentifier.fromAst argName
      let vaName := match vararg.val with | some (.mk_arg _ n _ _) => [PythonIdentifier.fromAst n] | none => []
      let kwName := match kwarg.val with | some (.mk_arg _ n _ _) => [PythonIdentifier.fromAst n] | none => []
      names ++ vaName ++ kwName

private def extractVarargKwarg (args : Python.arguments SourceRange) : List (PythonIdentifier × PythonType) :=
  match args with
  | .mk_arguments _ _ _ vararg _ _ kwarg _ =>
      let va := match vararg.val with | some a => [argToParam a] | none => []
      let kw := match kwarg.val with | some a => [argToParam a] | none => []
      va ++ kw

def extractDefaults (args : Python.arguments SourceRange) : List (PythonIdentifier × PythonExpr) :=
  match args with
  | .mk_arguments _ posonlyargs argList _ kwonlyargs kwDefaults _ defaults =>
      let posAndRegular := posonlyargs.val.toList ++ argList.val.toList
      let paramNames := posAndRegular.map fun arg =>
        match arg with | .mk_arg _ argName _ _ => PythonIdentifier.fromAst argName
      let paramCount := paramNames.length
      let defaultCount := defaults.val.size
      let requiredCount := paramCount - defaultCount
      let defaultParams := paramNames.drop requiredCount
      let posDefaults := defaultParams.zip (defaults.val.toList)
      let kwNames := kwonlyargs.val.toList.map fun arg =>
        match arg with | .mk_arg _ argName _ _ => PythonIdentifier.fromAst argName
      let kwDefaultPairs := kwNames.zip (kwDefaults.val.toList) |>.filterMap fun (name, optExpr) =>
        match optExpr with
        | .some_expr _ e => some (name, e)
        | .missing_expr _ => none
      posDefaults ++ kwDefaultPairs

def extractReturnType (returns : Ann (Option PythonExpr) SourceRange) : PythonType :=
  annotationToPythonType returns.val

def extractFuncSig (name : String) (args : Python.arguments SourceRange)
    (returns : Ann (Option PythonExpr) SourceRange)
    (body : PythonProgram) : FuncSig :=
  let params := extractParams args
  let defaults := extractDefaults args
  let retTy := extractReturnType returns
  let allParamNames := extractAllParamNames args
  let locals := computeLocals body allParamNames
  { name := mkLaurelId name
    params := params.map fun (n, ty) => (mkLaurelId n.val, ty)
    defaults := defaults.map fun (n, e) => (mkLaurelId n.val, e)
    returnType := retTy
    locals := locals.map fun (n, ty) => (mkLaurelId n.val, ty) }

-- ═══════════════════════════════════════════════════════════════════════════════
-- Python Name → Laurel Name (builtin mapping, applied when minting identifiers)
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

def operatorToLaurel : Python.operator SourceRange → String
  | .Add _ => "PAdd" | .Sub _ => "PSub" | .Mult _ => "PMul" | .Div _ => "PDiv"
  | .FloorDiv _ => "PFloorDiv" | .Mod _ => "PMod" | .Pow _ => "PPow"
  | .BitAnd _ => "PBitAnd" | .BitOr _ => "PBitOr" | .BitXor _ => "PBitXor"
  | .LShift _ => "PLShift" | .RShift _ => "PRShift" | .MatMult _ => "PMatMul"

def cmpopToLaurel : Python.cmpop SourceRange → String
  | .Eq _ => "PEq" | .NotEq _ => "PNEq" | .Lt _ => "PLt" | .LtE _ => "PLe"
  | .Gt _ => "PGt" | .GtE _ => "PGe" | .In _ => "PIn" | .NotIn _ => "PNotIn"
  | .Is _ => "PIs" | .IsNot _ => "PIsNot"

def unaryopToLaurel : Python.unaryop SourceRange → String
  | .Not _ => "PNot" | .USub _ => "PNeg" | .UAdd _ => "PPos" | .Invert _ => "PInvert"

def boolopToLaurel : Python.boolop SourceRange → String
  | .And _ => "PAnd" | .Or _ => "POr"

-- ═══════════════════════════════════════════════════════════════════════════════
-- Initial Context: Python Builtins
-- ═══════════════════════════════════════════════════════════════════════════════

private def anyType : PythonType := .Name SourceRange.none ⟨SourceRange.none, "Any"⟩ (.Load SourceRange.none)
private def intType : PythonType := .Name SourceRange.none ⟨SourceRange.none, "int"⟩ (.Load SourceRange.none)
private def strType : PythonType := .Name SourceRange.none ⟨SourceRange.none, "str"⟩ (.Load SourceRange.none)
private def boolType : PythonType := .Name SourceRange.none ⟨SourceRange.none, "bool"⟩ (.Load SourceRange.none)

private def mkBuiltinSig (pythonName : String) (params : List (String × PythonType)) (retTy : PythonType) : FuncSig :=
  { name := mkLaurelId (pythonNameToLaurel pythonName)
    params := params.map fun (n, ty) => (mkLaurelId n, ty)
    defaults := [], returnType := retTy, locals := [] }

def builtinContext : Ctx :=
  let entries : List (PythonIdentifier × CtxEntry) := [
    (.builtin "len", .function (mkBuiltinSig "len" [("obj", anyType)] intType)),
    (.builtin "str", .function (mkBuiltinSig "str" [("obj", anyType)] strType)),
    (.builtin "int", .function (mkBuiltinSig "int" [("obj", anyType)] intType)),
    (.builtin "float", .function (mkBuiltinSig "float" [("obj", anyType)] anyType)),
    (.builtin "bool", .function (mkBuiltinSig "bool" [("obj", anyType)] boolType)),
    (.builtin "print", .function (mkBuiltinSig "print" [("obj", anyType)] anyType)),
    (.builtin "repr", .function (mkBuiltinSig "repr" [("obj", anyType)] strType)),
    (.builtin "type", .function (mkBuiltinSig "type" [("obj", anyType)] anyType)),
    (.builtin "isinstance", .function (mkBuiltinSig "isinstance" [("obj", anyType), ("cls", anyType)] boolType)),
    (.builtin "hasattr", .function (mkBuiltinSig "hasattr" [("obj", anyType), ("name", strType)] boolType)),
    (.builtin "getattr", .function (mkBuiltinSig "getattr" [("obj", anyType), ("name", strType)] anyType)),
    (.builtin "setattr", .function (mkBuiltinSig "setattr" [("obj", anyType), ("name", strType), ("value", anyType)] anyType)),
    (.builtin "sorted", .function (mkBuiltinSig "sorted" [("iterable", anyType)] anyType)),
    (.builtin "reversed", .function (mkBuiltinSig "reversed" [("seq", anyType)] anyType)),
    (.builtin "enumerate", .function (mkBuiltinSig "enumerate" [("iterable", anyType)] anyType)),
    (.builtin "zip", .function (mkBuiltinSig "zip" [("a", anyType), ("b", anyType)] anyType)),
    (.builtin "range", .function (mkBuiltinSig "range" [("stop", anyType)] anyType)),
    (.builtin "list", .function (mkBuiltinSig "list" [("iterable", anyType)] anyType)),
    (.builtin "dict", .function (mkBuiltinSig "dict" [("iterable", anyType)] anyType)),
    (.builtin "set", .function (mkBuiltinSig "set" [("iterable", anyType)] anyType)),
    (.builtin "tuple", .function (mkBuiltinSig "tuple" [("iterable", anyType)] anyType)),
    (.builtin "min", .function (mkBuiltinSig "min" [("a", anyType), ("b", anyType)] anyType)),
    (.builtin "max", .function (mkBuiltinSig "max" [("a", anyType), ("b", anyType)] anyType)),
    (.builtin "sum", .function (mkBuiltinSig "sum" [("iterable", anyType)] anyType)),
    (.builtin "any", .function (mkBuiltinSig "any" [("iterable", anyType)] boolType)),
    (.builtin "all", .function (mkBuiltinSig "all" [("iterable", anyType)] boolType)),
    (.builtin "abs", .function (mkBuiltinSig "abs" [("x", anyType)] anyType)),
    (.builtin "ord", .function (mkBuiltinSig "ord" [("c", strType)] intType)),
    (.builtin "chr", .function (mkBuiltinSig "chr" [("i", intType)] strType)),
    (.builtin "map", .function (mkBuiltinSig "map" [("func", anyType), ("iterable", anyType)] anyType)),
    (.builtin "filter", .function (mkBuiltinSig "filter" [("func", anyType), ("iterable", anyType)] anyType))
  ]
  entries.foldl (fun ctx (name, info) => ctx.insert name info) {}

-- ═══════════════════════════════════════════════════════════════════════════════
-- Spine type resolution (chases .Name and .Attribute chains)
-- ═══════════════════════════════════════════════════════════════════════════════

def typeOfExpr (ctx : Ctx) : PythonExpr → Option PythonType
  | .Name _ n _ => match ctx[PythonIdentifier.fromAst n]? with
    | some (.variable ty) => some ty
    | some (.function _) => none
    | some (.class_ _ _ _) => none
    | some (.module_ _) => none
    | some .unresolved => none
    | none => none
  | .Attribute _ obj fieldName _ =>
    match typeOfExpr ctx obj with
    | some (.Name _ className _) => match ctx[PythonIdentifier.fromAst className]? with
      | some (.class_ _ fields _) =>
        fields.find? (fun (fName, _) => fName == PythonIdentifier.fromAst fieldName) |>.map (·.2)
      | _ => none
    | _ => none
  | _ => none

private def isAnyType (ty : PythonType) : Bool :=
  match ty with
  | .Name _ n _ => n.val == "Any"
  | _ => false

private def insertParamIfMoreSpecific (c : Ctx) (n : PythonIdentifier) (ty : PythonType) : Ctx :=
  if isAnyType ty then
    match c[n]? with
    | some _ => c
    | none => c.insert n (CtxEntry.variable ty)
  else
    c.insert n (CtxEntry.variable ty)

private def resolveFunctionBody (ctx : Ctx) (args : Python.arguments SourceRange) (body : PythonProgram) : Ctx :=
  let params := extractParams args
  let varargKwarg := extractVarargKwarg args
  let allParamNames := extractAllParamNames args
  let locals := computeLocals body allParamNames
  let bodyCtx := params.foldl (fun c (n, ty) => insertParamIfMoreSpecific c n ty) ctx
  let bodyCtx := varargKwarg.foldl (fun c (n, ty) => insertParamIfMoreSpecific c n ty) bodyCtx
  locals.foldl (fun c (n, ty) => c.insert n (CtxEntry.variable ty)) bodyCtx

private def resolveMethodCall (ctx : Ctx) (receiver : PythonExpr) (methodName : Ann String SourceRange) : NodeInfo :=
  let methId := PythonIdentifier.fromAst methodName
  match typeOfExpr ctx receiver with
  | some (.Name _ className _) =>
    let classId := PythonIdentifier.fromAst className
    match ctx[classId]? with
    | some (.class_ _ _ methods) =>
      match methods.find? (fun (mName, _) => mName == methId) with
      | some (_, sig) => .call sig.name sig
      | none => .unresolved
    | _ => .unresolved
  | _ => match receiver with
    | .Name _ rName _ =>
      let rId := PythonIdentifier.fromAst rName
      match ctx[rId]? with
      | some (.module_ _modName) => .unresolved
      | _ => .unresolved
    | _ => .unresolved

-- ═══════════════════════════════════════════════════════════════════════════════
-- AST Annotation Mapping (f : SourceRange → ResolvedAnn through the tree)
-- ═══════════════════════════════════════════════════════════════════════════════

private def mapAnnVal (f : α → β) (a : Ann T α) : Ann T β := ⟨f a.ann, a.val⟩
private def mapAnnOpt (f : α → β) (mapT : T₁ → T₂) (a : Ann (Option T₁) α) : Ann (Option T₂) β :=
  ⟨f a.ann, a.val.map mapT⟩
private def mapAnnArr (f : α → β) (mapT : T₁ → T₂) (a : Ann (Array T₁) α) : Ann (Array T₂) β :=
  ⟨f a.ann, a.val.map mapT⟩

-- ═══════════════════════════════════════════════════════════════════════════════
-- The Fold: resolve
--
-- Threads Ctx as accumulator. Declarations extend it. References look up from it.
-- Non-reference nodes get .none. Reference nodes get their lookup result.
-- ═══════════════════════════════════════════════════════════════════════════════

mutual
partial def resolveExprCtx (f : SourceRange → ResolvedAnn) : Python.expr_context SourceRange → Python.expr_context ResolvedAnn
  | .Load a => .Load (f a) | .Store a => .Store (f a) | .Del a => .Del (f a)

partial def resolveConstant (f : SourceRange → ResolvedAnn) : Python.constant SourceRange → Python.constant ResolvedAnn
  | .ConTrue a => .ConTrue (f a) | .ConFalse a => .ConFalse (f a)
  | .ConPos a n => .ConPos (f a) (mapAnnVal f n) | .ConNeg a n => .ConNeg (f a) (mapAnnVal f n)
  | .ConString a s => .ConString (f a) (mapAnnVal f s) | .ConFloat a s => .ConFloat (f a) (mapAnnVal f s)
  | .ConComplex a r i => .ConComplex (f a) (mapAnnVal f r) (mapAnnVal f i)
  | .ConNone a => .ConNone (f a) | .ConEllipsis a => .ConEllipsis (f a)
  | .ConBytes a b => .ConBytes (f a) (mapAnnVal f b)

partial def resolveInt (f : SourceRange → ResolvedAnn) : Python.int SourceRange → Python.int ResolvedAnn
  | .IntPos a n => .IntPos (f a) (mapAnnVal f n) | .IntNeg a n => .IntNeg (f a) (mapAnnVal f n)

partial def resolveOperator (f : SourceRange → ResolvedAnn) : Python.operator SourceRange → Python.operator ResolvedAnn
  | .Add a => .Add (f a) | .Sub a => .Sub (f a) | .Mult a => .Mult (f a) | .Div a => .Div (f a)
  | .FloorDiv a => .FloorDiv (f a) | .Mod a => .Mod (f a) | .Pow a => .Pow (f a)
  | .BitAnd a => .BitAnd (f a) | .BitOr a => .BitOr (f a) | .BitXor a => .BitXor (f a)
  | .LShift a => .LShift (f a) | .RShift a => .RShift (f a) | .MatMult a => .MatMult (f a)

partial def resolveBoolop (f : SourceRange → ResolvedAnn) : Python.boolop SourceRange → Python.boolop ResolvedAnn
  | .And a => .And (f a) | .Or a => .Or (f a)

partial def resolveUnaryop (f : SourceRange → ResolvedAnn) : Python.unaryop SourceRange → Python.unaryop ResolvedAnn
  | .Not a => .Not (f a) | .USub a => .USub (f a) | .UAdd a => .UAdd (f a) | .Invert a => .Invert (f a)

partial def resolveCmpop (f : SourceRange → ResolvedAnn) : Python.cmpop SourceRange → Python.cmpop ResolvedAnn
  | .Eq a => .Eq (f a) | .NotEq a => .NotEq (f a) | .Lt a => .Lt (f a) | .LtE a => .LtE (f a)
  | .Gt a => .Gt (f a) | .GtE a => .GtE (f a) | .Is a => .Is (f a) | .IsNot a => .IsNot (f a)
  | .In a => .In (f a) | .NotIn a => .NotIn (f a)

partial def resolveOptExpr (ctx : Ctx) (f : SourceRange → ResolvedAnn) : Python.opt_expr SourceRange → Python.opt_expr ResolvedAnn
  | .some_expr a e => .some_expr (f a) (resolveExpr ctx f e)
  | .missing_expr a => .missing_expr (f a)

partial def resolveKeyword (ctx : Ctx) (f : SourceRange → ResolvedAnn) : Python.keyword SourceRange → Python.keyword ResolvedAnn
  | .mk_keyword a arg val => .mk_keyword (f a) (mapAnnOpt f (mapAnnVal f) arg) (resolveExpr ctx f val)

partial def resolveArg (ctx : Ctx) (f : SourceRange → ResolvedAnn) : Python.arg SourceRange → Python.arg ResolvedAnn
  | .mk_arg a name ann tc => .mk_arg (f a) (mapAnnVal f name) (mapAnnOpt f (resolveExpr ctx f) ann) (mapAnnOpt f (mapAnnVal f) tc)

partial def resolveArguments (ctx : Ctx) (f : SourceRange → ResolvedAnn) : Python.arguments SourceRange → Python.arguments ResolvedAnn
  | .mk_arguments a posonlyargs args vararg kwonlyargs kwDefaults kwarg defaults =>
      .mk_arguments (f a)
        (mapAnnArr f (resolveArg ctx f) posonlyargs)
        (mapAnnArr f (resolveArg ctx f) args)
        (mapAnnOpt f (resolveArg ctx f) vararg)
        (mapAnnArr f (resolveArg ctx f) kwonlyargs)
        (mapAnnArr f (resolveOptExpr ctx f) kwDefaults)
        (mapAnnOpt f (resolveArg ctx f) kwarg)
        (mapAnnArr f (resolveExpr ctx f) defaults)

partial def resolveComprehension (ctx : Ctx) (f : SourceRange → ResolvedAnn) (comp : Python.comprehension SourceRange) : Ctx × Python.comprehension ResolvedAnn :=
  match comp with
  | .mk_comprehension a target iter ifs isAsync =>
      let targetNames := collectNamesFromTarget target
      let compCtx := targetNames.foldl (fun c n => c.insert n (CtxEntry.variable (annotationToPythonType Option.none))) ctx
      (compCtx, .mk_comprehension (f a) (resolveExpr compCtx f target) (resolveExpr ctx f iter)
        (mapAnnArr f (resolveExpr compCtx f) ifs) (resolveInt f isAsync))

partial def resolveComprehensions (ctx : Ctx) (f : SourceRange → ResolvedAnn) (comps : List (Python.comprehension SourceRange)) : Ctx × List (Python.comprehension ResolvedAnn) :=
  comps.foldl (init := (ctx, ([] : List (Python.comprehension ResolvedAnn)))) fun acc comp =>
    let (c, resolved) := acc
    let (c', r) := resolveComprehension c f comp
    (c', resolved ++ [r])

partial def resolveTypeParam (ctx : Ctx) (f : SourceRange → ResolvedAnn) : Python.type_param SourceRange → Python.type_param ResolvedAnn
  | .TypeVar a name bound def_ => .TypeVar (f a) (mapAnnVal f name)
      (mapAnnOpt f (resolveExpr ctx f) bound) (mapAnnOpt f (resolveExpr ctx f) def_)
  | .TypeVarTuple a name def_ => .TypeVarTuple (f a) (mapAnnVal f name) (mapAnnOpt f (resolveExpr ctx f) def_)
  | .ParamSpec a name def_ => .ParamSpec (f a) (mapAnnVal f name) (mapAnnOpt f (resolveExpr ctx f) def_)

partial def resolveExpr (ctx : Ctx) (f : SourceRange → ResolvedAnn) (e : PythonExpr) : ResolvedPythonExpr :=
  match e with
  | .Name a n ectx =>
      let nId := PythonIdentifier.fromAst n
      let info := match ctx[nId]? with
        | some (.function sig) => .variable sig.name
        | some (.class_ cId _ _) => .variable (mkLaurelId cId.val)
        | some (.variable _) => .variable (mkLaurelId n.val)
        | some (.module_ _) => .irrelevant
        | some .unresolved => .unresolved
        | none => .unresolved
      .Name { sr := a, info } (mapAnnVal f n) (resolveExprCtx f ectx)
  | .Call a func args kwargs =>
      let callInfo : NodeInfo := match func with
        | .Name _ n _ =>
          let nId := PythonIdentifier.fromAst n
          match ctx[nId]? with
          | some (.function sig) => .call sig.name sig
          | some (.class_ cId _ methods) =>
              let initId := PythonIdentifier.fromAst ⟨SourceRange.none, "__init__"⟩
              let initSig := methods.find? (fun (mName, _) => mName == initId)
              let initLaurelName := mkLaurelId s!"{cId.val}@__init__"
              match initSig with
              | some (_, sig) => .classNew (mkLaurelId cId.val) sig.name sig
              | none =>
                let emptySig : FuncSig := { name := initLaurelName, params := [], defaults := [], returnType := anyType, locals := [] }
                .classNew (mkLaurelId cId.val) initLaurelName emptySig
          | _ => .unresolved
        | .Attribute _ receiver methodName _ =>
            resolveMethodCall ctx receiver methodName
        | _ => .unresolved
      .Call { sr := a, info := callInfo } (resolveExpr ctx f func)
        (mapAnnArr f (resolveExpr ctx f) args)
        (mapAnnArr f (resolveKeyword ctx f) kwargs)
  | .Attribute a obj attr ectx =>
      .Attribute { sr := a, info := .fieldAccess (mkLaurelId attr.val) } (resolveExpr ctx f obj) (mapAnnVal f attr) (resolveExprCtx f ectx)
  | .Constant a c tc => .Constant (f a) (resolveConstant f c) (mapAnnOpt f (mapAnnVal f) tc)
  | .BinOp a left op right =>
      .BinOp { sr := a, info := .operator (mkLaurelId (operatorToLaurel op)) } (resolveExpr ctx f left) (resolveOperator f op) (resolveExpr ctx f right)
  | .BoolOp a op operands =>
      .BoolOp { sr := a, info := .operator (mkLaurelId (boolopToLaurel op)) } (resolveBoolop f op) (mapAnnArr f (resolveExpr ctx f) operands)
  | .UnaryOp a op operand =>
      .UnaryOp { sr := a, info := .operator (mkLaurelId (unaryopToLaurel op)) } (resolveUnaryop f op) (resolveExpr ctx f operand)
  | .Compare a left ops comps =>
      let opName := match ops.val[0]? with | some op => cmpopToLaurel op | none => "PEq"
      .Compare { sr := a, info := .operator (mkLaurelId opName) } (resolveExpr ctx f left) (mapAnnArr f (resolveCmpop f) ops) (mapAnnArr f (resolveExpr ctx f) comps)
  | .IfExp a test body orelse => .IfExp (f a) (resolveExpr ctx f test) (resolveExpr ctx f body) (resolveExpr ctx f orelse)
  | .Dict a keys vals => .Dict (f a) (mapAnnArr f (resolveOptExpr ctx f) keys) (mapAnnArr f (resolveExpr ctx f) vals)
  | .Set a elts => .Set (f a) (mapAnnArr f (resolveExpr ctx f) elts)
  | .ListComp a elt gens =>
      let (compCtx, resolvedGens) := resolveComprehensions ctx f gens.val.toList
      .ListComp (f a) (resolveExpr compCtx f elt) ⟨f gens.ann, resolvedGens.toArray⟩
  | .SetComp a elt gens =>
      let (compCtx, resolvedGens) := resolveComprehensions ctx f gens.val.toList
      .SetComp (f a) (resolveExpr compCtx f elt) ⟨f gens.ann, resolvedGens.toArray⟩
  | .DictComp a key val gens =>
      let (compCtx, resolvedGens) := resolveComprehensions ctx f gens.val.toList
      .DictComp (f a) (resolveExpr compCtx f key) (resolveExpr compCtx f val) ⟨f gens.ann, resolvedGens.toArray⟩
  | .GeneratorExp a elt gens =>
      let (compCtx, resolvedGens) := resolveComprehensions ctx f gens.val.toList
      .GeneratorExp (f a) (resolveExpr compCtx f elt) ⟨f gens.ann, resolvedGens.toArray⟩
  | .Await a inner => .Await (f a) (resolveExpr ctx f inner)
  | .Yield a valOpt => .Yield (f a) (mapAnnOpt f (resolveExpr ctx f) valOpt)
  | .YieldFrom a inner => .YieldFrom (f a) (resolveExpr ctx f inner)
  | .FormattedValue a value conv fmt => .FormattedValue (f a) (resolveExpr ctx f value) (resolveInt f conv) (mapAnnOpt f (resolveExpr ctx f) fmt)
  | .JoinedStr a values => .JoinedStr (f a) (mapAnnArr f (resolveExpr ctx f) values)
  | .Subscript a obj slice ectx => .Subscript (f a) (resolveExpr ctx f obj) (resolveExpr ctx f slice) (resolveExprCtx f ectx)
  | .Starred a inner ectx => .Starred (f a) (resolveExpr ctx f inner) (resolveExprCtx f ectx)
  | .Tuple a elts ectx => .Tuple (f a) (mapAnnArr f (resolveExpr ctx f) elts) (resolveExprCtx f ectx)
  | .List a elts ectx => .List (f a) (mapAnnArr f (resolveExpr ctx f) elts) (resolveExprCtx f ectx)
  | .NamedExpr a target value => .NamedExpr (f a) (resolveExpr ctx f target) (resolveExpr ctx f value)
  | .Lambda a args body =>
      let lambdaParams := extractParams args
      let lambdaCtx := lambdaParams.foldl (fun c (n, ty) => c.insert n (CtxEntry.variable ty)) ctx
      .Lambda (f a) (resolveArguments lambdaCtx f args) (resolveExpr lambdaCtx f body)
  | .Slice a start stop step => .Slice (f a) (mapAnnOpt f (resolveExpr ctx f) start) (mapAnnOpt f (resolveExpr ctx f) stop) (mapAnnOpt f (resolveExpr ctx f) step)
  | .TemplateStr a parts => .TemplateStr (f a) (mapAnnArr f (resolveExpr ctx f) parts)
  | .Interpolation a value conv fmtSpec fmt => .Interpolation (f a) (resolveExpr ctx f value) (resolveConstant f conv) (resolveInt f fmtSpec) (mapAnnOpt f (resolveExpr ctx f) fmt)

partial def resolveAlias (f : SourceRange → ResolvedAnn) : Python.alias SourceRange → Python.alias ResolvedAnn
  | .mk_alias a name asname => .mk_alias (f a) (mapAnnVal f name) (mapAnnOpt f (mapAnnVal f) asname)

partial def resolveWithitem (ctx : Ctx) (f : SourceRange → ResolvedAnn) : Python.withitem SourceRange → Python.withitem ResolvedAnn
  | .mk_withitem a ctxExpr optVars => .mk_withitem (f a) (resolveExpr ctx f ctxExpr) (mapAnnOpt f (resolveExpr ctx f) optVars)

partial def resolveExcepthandler (ctx : Ctx) (f : SourceRange → ResolvedAnn) : Python.excepthandler SourceRange → Python.excepthandler ResolvedAnn
  | .ExceptHandler a ty name body =>
      let handlerCtx := match name.val with
        | some n => ctx.insert (PythonIdentifier.fromAst n) (CtxEntry.variable (annotationToPythonType Option.none))
        | none => ctx
      .ExceptHandler (f a) (mapAnnOpt f (resolveExpr ctx f) ty) (mapAnnOpt f (mapAnnVal f) name) ⟨f body.ann, resolveBlock handlerCtx f body.val⟩

partial def resolveMatchCase (ctx : Ctx) (f : SourceRange → ResolvedAnn) : Python.match_case SourceRange → Python.match_case ResolvedAnn
  | .mk_match_case a pat guard body => .mk_match_case (f a) (sorry) (mapAnnOpt f (resolveExpr ctx f) guard) ⟨f body.ann, resolveBlock ctx f body.val⟩

partial def resolveBlock (ctx : Ctx) (f : SourceRange → ResolvedAnn) (stmts : Array PythonStmt) : Array ResolvedPythonStmt :=
  let (_, resolved) := stmts.foldl (init := (ctx, (#[] : Array ResolvedPythonStmt))) fun acc stmt =>
    let (c, arr) := acc
    let (c', r) := resolveStmt c f stmt
    (c', arr.push r)
  resolved

partial def resolveFuncDef (ctx : Ctx) (f : SourceRange → ResolvedAnn)
    (sig : FuncSig)
    (a : SourceRange) (name : Ann String SourceRange) (args : Python.arguments SourceRange)
    (body : Ann PythonProgram SourceRange) (decorators : Ann (Array PythonExpr) SourceRange)
    (returns : Ann (Option PythonExpr) SourceRange) (tc : Ann (Option (Ann String SourceRange)) SourceRange)
    (typeParams : Ann (Array (Python.type_param SourceRange)) SourceRange) :=
  let ctx' := ctx.insert (PythonIdentifier.fromAst name) (.function sig)
  let bodyCtx := resolveFunctionBody ctx' args body.val
  let ann : ResolvedAnn := { sr := a, info := .funcDecl sig }
  let rBody : Ann (Array ResolvedPythonStmt) ResolvedAnn := ⟨f body.ann, resolveBlock bodyCtx f body.val⟩
  (ctx', ann, mapAnnVal f name, resolveArguments bodyCtx f args, rBody,
    mapAnnArr f (resolveExpr ctx' f) decorators,
    mapAnnOpt f (resolveExpr ctx' f) returns,
    mapAnnOpt f (mapAnnVal f) tc,
    mapAnnArr f (resolveTypeParam ctx' f) typeParams)

partial def resolveStmt (ctx : Ctx) (f : SourceRange → ResolvedAnn) (s : PythonStmt) : Ctx × ResolvedPythonStmt :=
  match s with
  | .FunctionDef a name args body decorators returns tc typeParams =>
      let nameId := PythonIdentifier.fromAst name
      let sig := match ctx[nameId]? with
        | some (.function existingSig) => existingSig
        | _ => extractFuncSig name.val args returns body.val
      let (ctx', ann, rName, rArgs, rBody, rDecs, rRets, rTc, rTps) :=
        resolveFuncDef ctx f sig a name args body decorators returns tc typeParams
      (ctx', .FunctionDef ann rName rArgs rBody rDecs rRets rTc rTps)
  | .AsyncFunctionDef a name args body decorators returns tc typeParams =>
      let nameId := PythonIdentifier.fromAst name
      let sig := match ctx[nameId]? with
        | some (.function existingSig) => existingSig
        | _ => extractFuncSig name.val args returns body.val
      let (ctx', ann, rName, rArgs, rBody, rDecs, rRets, rTc, rTps) :=
        resolveFuncDef ctx f sig a name args body decorators returns tc typeParams
      (ctx', .AsyncFunctionDef ann rName rArgs rBody rDecs rRets rTc rTps)
  | .ClassDef a name bases keywords body decorators typeParams =>
      let classId := PythonIdentifier.fromAst name
      let classType : PythonType := .Name SourceRange.none ⟨SourceRange.none, name.val⟩ (.Load SourceRange.none)
      let fields := body.val.toList.filterMap fun s => match s with
        | .AnnAssign _ (.Name _ n _) annotation _ _ => some (PythonIdentifier.fromAst n, annotation)
        | _ => Option.none
      let methods := body.val.toList.filterMap fun s => match s with
        | .FunctionDef _ mName mArgs ⟨_, mBody⟩ _ mReturns _ _ =>
            let mId := PythonIdentifier.fromAst mName
            some (mId, extractFuncSig s!"{name.val}@{mName.val}" mArgs mReturns mBody)
        | .AsyncFunctionDef _ mName mArgs ⟨_, mBody⟩ _ mReturns _ _ =>
            let mId := PythonIdentifier.fromAst mName
            some (mId, extractFuncSig s!"{name.val}@{mName.val}" mArgs mReturns mBody)
        | _ => Option.none
      let ctx' := ctx.insert classId (CtxEntry.class_ classId fields methods)
      let classCtx := ctx'.insert (PythonIdentifier.fromAst ⟨SourceRange.none, "self"⟩) (CtxEntry.variable classType)
      let classCtx := methods.foldl (fun c (mId, mSig) => c.insert mId (CtxEntry.function mSig)) classCtx
      let laurelFields := fields.map fun (fId, fTy) => (mkLaurelId fId.val, fTy)
      let methodSigs := methods.map (·.2)
      (ctx', .ClassDef { sr := a, info := .classDecl (mkLaurelId name.val) laurelFields methodSigs } (mapAnnVal f name)
        (mapAnnArr f (resolveExpr ctx' f) bases)
        (mapAnnArr f (resolveKeyword ctx' f) keywords)
        ⟨f body.ann, resolveBlock classCtx f body.val⟩
        (mapAnnArr f (resolveExpr ctx' f) decorators)
        (mapAnnArr f (resolveTypeParam ctx' f) typeParams))
  | .Import a aliases =>
      let ctx' := aliases.val.foldl (fun c alias => match alias with
        | .mk_alias _ modName asName =>
            let registeredId := match asName.val with
              | some aliasName => PythonIdentifier.fromAst aliasName
              | none => PythonIdentifier.fromImport modName
            c.insert registeredId (CtxEntry.module_ (PythonIdentifier.fromAst modName))) ctx
      (ctx', .Import (f a) (mapAnnArr f (resolveAlias f) aliases))
  | .ImportFrom a modName imports level =>
      let ctx' := imports.val.foldl (fun c imp => match imp with
        | .mk_alias _ impName asName =>
            let registeredId := match asName.val with
              | some aliasName => PythonIdentifier.fromAst aliasName
              | none => PythonIdentifier.fromAst impName
            c.insert registeredId CtxEntry.unresolved) ctx
      (ctx', .ImportFrom (f a) (mapAnnOpt f (mapAnnVal f) modName) (mapAnnArr f (resolveAlias f) imports) (mapAnnOpt f (resolveInt f) level))
  | .Assign a targets value tc =>
      let newNames := targets.val.toList.flatMap collectNamesFromTarget
      let ctx' := newNames.foldl (fun c n => c.insert n (CtxEntry.variable (annotationToPythonType Option.none))) ctx
      (ctx', .Assign (f a) (mapAnnArr f (resolveExpr ctx f) targets) (resolveExpr ctx f value) (mapAnnOpt f (mapAnnVal f) tc))
  | .AnnAssign a target ann value simple =>
      let newNames := collectNamesFromTarget target
      let ctx' := newNames.foldl (fun c n => c.insert n (CtxEntry.variable ann)) ctx
      (ctx', .AnnAssign (f a) (resolveExpr ctx f target) (resolveExpr ctx f ann) (mapAnnOpt f (resolveExpr ctx f) value) (resolveInt f simple))
  | .AugAssign a target op value =>
      (ctx, .AugAssign { sr := a, info := .operator (mkLaurelId (operatorToLaurel op)) } (resolveExpr ctx f target) (resolveOperator f op) (resolveExpr ctx f value))
  | .If a test body orelse =>
      (ctx, .If (f a) (resolveExpr ctx f test) ⟨f body.ann, resolveBlock ctx f body.val⟩ ⟨f orelse.ann, resolveBlock ctx f orelse.val⟩)
  | .For a target iter body orelse tc =>
      (ctx, .For (f a) (resolveExpr ctx f target) (resolveExpr ctx f iter) ⟨f body.ann, resolveBlock ctx f body.val⟩ ⟨f orelse.ann, resolveBlock ctx f orelse.val⟩ (mapAnnOpt f (mapAnnVal f) tc))
  | .AsyncFor a target iter body orelse tc =>
      (ctx, .AsyncFor (f a) (resolveExpr ctx f target) (resolveExpr ctx f iter) ⟨f body.ann, resolveBlock ctx f body.val⟩ ⟨f orelse.ann, resolveBlock ctx f orelse.val⟩ (mapAnnOpt f (mapAnnVal f) tc))
  | .While a test body orelse =>
      (ctx, .While (f a) (resolveExpr ctx f test) ⟨f body.ann, resolveBlock ctx f body.val⟩ ⟨f orelse.ann, resolveBlock ctx f orelse.val⟩)
  | .Try a body handlers orelse finalbody =>
      (ctx, .Try (f a) ⟨f body.ann, resolveBlock ctx f body.val⟩ (mapAnnArr f (resolveExcepthandler ctx f) handlers) ⟨f orelse.ann, resolveBlock ctx f orelse.val⟩ ⟨f finalbody.ann, resolveBlock ctx f finalbody.val⟩)
  | .TryStar a body handlers orelse finalbody =>
      (ctx, .TryStar (f a) ⟨f body.ann, resolveBlock ctx f body.val⟩ (mapAnnArr f (resolveExcepthandler ctx f) handlers) ⟨f orelse.ann, resolveBlock ctx f orelse.val⟩ ⟨f finalbody.ann, resolveBlock ctx f finalbody.val⟩)
  | .With a items body tc =>
      (ctx, .With (f a) (mapAnnArr f (resolveWithitem ctx f) items) ⟨f body.ann, resolveBlock ctx f body.val⟩ (mapAnnOpt f (mapAnnVal f) tc))
  | .AsyncWith a items body tc =>
      (ctx, .AsyncWith (f a) (mapAnnArr f (resolveWithitem ctx f) items) ⟨f body.ann, resolveBlock ctx f body.val⟩ (mapAnnOpt f (mapAnnVal f) tc))
  | .Return a value => (ctx, .Return (f a) (mapAnnOpt f (resolveExpr ctx f) value))
  | .Delete a targets => (ctx, .Delete (f a) (mapAnnArr f (resolveExpr ctx f) targets))
  | .Raise a exc cause => (ctx, .Raise (f a) (mapAnnOpt f (resolveExpr ctx f) exc) (mapAnnOpt f (resolveExpr ctx f) cause))
  | .Assert a test msg => (ctx, .Assert (f a) (resolveExpr ctx f test) (mapAnnOpt f (resolveExpr ctx f) msg))
  | .Expr a value => (ctx, .Expr (f a) (resolveExpr ctx f value))
  | .Pass a => (ctx, .Pass (f a))
  | .Break a => (ctx, .Break (f a))
  | .Continue a => (ctx, .Continue (f a))
  | .Global a names => (ctx, .Global (f a) (mapAnnArr f (mapAnnVal f) names))
  | .Nonlocal a names => (ctx, .Nonlocal (f a) (mapAnnArr f (mapAnnVal f) names))
  | .Match a subject cases => (ctx, .Match (f a) (resolveExpr ctx f subject) (mapAnnArr f (resolveMatchCase ctx f) cases))
  | .TypeAlias a name typeParams value =>
      (ctx, .TypeAlias (f a) (resolveExpr ctx f name) (mapAnnArr f (resolveTypeParam ctx f) typeParams) (resolveExpr ctx f value))
end

def resolve (stmts : PythonProgram) : ResolvedPythonProgram :=
  let f : SourceRange → ResolvedAnn := fun sr => { sr, info := .irrelevant }
  let moduleLocals := computeLocals stmts []
  let initCtx := moduleLocals.foldl (fun c (n, ty) => c.insert n (CtxEntry.variable ty)) builtinContext
  let (_, resolved) := stmts.foldl (init := (initCtx, (#[] : Array ResolvedPythonStmt))) fun acc stmt =>
    let (ctx, arr) := acc
    let (ctx', resolved) := resolveStmt ctx f stmt
    (ctx', arr.push resolved)
  { stmts := resolved, moduleLocals := moduleLocals.map fun (n, ty) => (mkLaurelId n.val, ty) }

end -- public section
end Strata.Python.Resolution
