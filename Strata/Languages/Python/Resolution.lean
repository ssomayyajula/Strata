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

abbrev Identifier := String
abbrev PythonExpr := Python.expr SourceRange
abbrev PythonStmt := Python.stmt SourceRange
abbrev PythonProgram := Array PythonStmt
abbrev PythonType := PythonExpr

structure FuncSig where
  params : List (Identifier × PythonType)
  defaults : List (Identifier × PythonExpr)
  returnType : PythonType
  locals : List (Identifier × PythonType)
  deriving Inhabited

inductive NameInfo where
  | class_ (name : Identifier) (fields : List (Identifier × PythonType))
  | function (sig : FuncSig)
  | variable (ty : PythonType)
  | module_ (name : Identifier)
  | unresolved
  | none
  deriving Inhabited

structure ResolvedAnn where
  sr : SourceRange
  info : NameInfo
  deriving Inhabited

instance : Inhabited ResolvedAnn where
  default := { sr := .none, info := .none }

abbrev ResolvedPythonStmt := Python.stmt ResolvedAnn
abbrev ResolvedPythonExpr := Python.expr ResolvedAnn
abbrev ResolvedPythonProgram := Array ResolvedPythonStmt

-- ═══════════════════════════════════════════════════════════════════════════════
-- Context
-- ═══════════════════════════════════════════════════════════════════════════════

abbrev Ctx := Std.HashMap Identifier NameInfo

-- ═══════════════════════════════════════════════════════════════════════════════
-- Annotation Helpers
-- ═══════════════════════════════════════════════════════════════════════════════

def mkAnn (sr : SourceRange) (info : NameInfo) : ResolvedAnn :=
  { sr, info }

def unresolvedAnn (sr : SourceRange) : ResolvedAnn :=
  { sr, info := .unresolved }

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
partial def collectWalrusFromComprehensions (comps : List (Python.comprehension SourceRange)) : List Identifier :=
  comps.flatMap fun comp =>
    match comp with
    | .mk_comprehension _ _target iter ifs _isAsync =>
        collectWalrusNames iter ++ ifs.val.toList.flatMap collectWalrusNames

partial def collectNamesFromTarget (target : PythonExpr) : List Identifier :=
  match target with
  | .Name _ n _ => [n.val]
  | .Tuple _ elems _ => elems.val.toList.flatMap collectNamesFromTarget
  | .List _ elems _ => elems.val.toList.flatMap collectNamesFromTarget
  | .Starred _ inner _ => collectNamesFromTarget inner
  | .Subscript _ _ _ _ => []
  | .Attribute _ _ _ _ => []
  | other => collectWalrusNames other

partial def collectWalrusNames (expr : PythonExpr) : List Identifier :=
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

partial def collectLocalsFromStmt (s : PythonStmt) : List (Identifier × PythonType) :=
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
              | some n => [(n.val, annotationToPythonType none)]
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
              | some n => [(n.val, annotationToPythonType none)]
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
  | .FunctionDef _ name _ _ _ _ _ _ => [(name.val, annotationToPythonType none)]
  | .AsyncFunctionDef _ name _ _ _ _ _ _ => [(name.val, annotationToPythonType none)]
  | .ClassDef _ name _ _ _ _ _ => [(name.val, annotationToPythonType none)]
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
            let name := match asName.val with
              | some aliasName => aliasName.val
              | none => match modName.val.splitOn "." with
                | first :: _ => first
                | [] => modName.val
            some (name, annotationToPythonType none)
  | .ImportFrom _ _ imports _ =>
      imports.val.toList.filterMap fun imp =>
        match imp with
        | .mk_alias _ impName asName =>
            let name := match asName.val with
              | some aliasName => aliasName.val
              | none => impName.val
            some (name, annotationToPythonType none)
  | .Global _ _ => []
  | .Nonlocal _ _ => []
  | .Expr _ value =>
      (collectWalrusNames value).map (fun n => (n, annotationToPythonType none))
  | .TypeAlias _ nameExpr _ _ =>
      (collectNamesFromTarget nameExpr).map fun n => (n, annotationToPythonType none)

def computeLocals (body : PythonProgram) (paramNames : List Identifier)
    : List (Identifier × PythonType) :=
  let allPairs := body.toList.flatMap collectLocalsFromStmt
  let paramSet : Std.HashSet Identifier := paramNames.foldl (fun s n => s.insert n) {}
  let (_, result) := allPairs.foldl (init := (paramSet, ([] : List (Identifier × PythonType)))) fun acc pair =>
    let (seen, result) := acc
    let (name, ty) := pair
    if seen.contains name then (seen, result)
    else (seen.insert name, result ++ [(name, ty)])
  result

-- ═══════════════════════════════════════════════════════════════════════════════
-- Extract FuncSig from a Python FunctionDef
-- ═══════════════════════════════════════════════════════════════════════════════

def extractParams (args : Python.arguments SourceRange) : List (Identifier × PythonType) :=
  match args with
  | .mk_arguments _ _ argList _ _ _ _ _ =>
      argList.val.toList.map fun arg =>
        match arg with
        | .mk_arg _ argName annotation _ =>
            (argName.val, annotationToPythonType annotation.val)

def extractDefaults (args : Python.arguments SourceRange) : List (Identifier × PythonExpr) :=
  match args with
  | .mk_arguments _ _ argList _ _ _ _ defaults =>
      let params := argList.val.toList.map fun arg =>
        match arg with | .mk_arg _ argName _ _ => argName.val
      let paramCount := params.length
      let defaultCount := defaults.val.size
      let requiredCount := paramCount - defaultCount
      let defaultParams := params.drop requiredCount
      defaultParams.zip (defaults.val.toList)

def extractReturnType (returns : Ann (Option PythonExpr) SourceRange) : PythonType :=
  annotationToPythonType returns.val

def extractFuncSig (args : Python.arguments SourceRange)
    (returns : Ann (Option PythonExpr) SourceRange)
    (body : PythonProgram) : FuncSig :=
  let params := extractParams args
  let defaults := extractDefaults args
  let retTy := extractReturnType returns
  let paramNames := params.map (·.1)
  let locals := computeLocals body paramNames
  { params, defaults, returnType := retTy, locals }

-- ═══════════════════════════════════════════════════════════════════════════════
-- Initial Context: Python Builtins
-- ═══════════════════════════════════════════════════════════════════════════════

private def anyType : PythonType := .Name SourceRange.none ⟨SourceRange.none, "Any"⟩ (.Load SourceRange.none)
private def intType : PythonType := .Name SourceRange.none ⟨SourceRange.none, "int"⟩ (.Load SourceRange.none)
private def strType : PythonType := .Name SourceRange.none ⟨SourceRange.none, "str"⟩ (.Load SourceRange.none)
private def boolType : PythonType := .Name SourceRange.none ⟨SourceRange.none, "bool"⟩ (.Load SourceRange.none)

private def mkBuiltinSig (params : List (Identifier × PythonType)) (retTy : PythonType) : FuncSig :=
  { params, defaults := [], returnType := retTy, locals := [] }

def builtinContext : Ctx :=
  let entries : List (Identifier × NameInfo) := [
    ("len", .function (mkBuiltinSig [("obj", anyType)] intType)),
    ("str", .function (mkBuiltinSig [("obj", anyType)] strType)),
    ("int", .function (mkBuiltinSig [("obj", anyType)] intType)),
    ("float", .function (mkBuiltinSig [("obj", anyType)] anyType)),
    ("bool", .function (mkBuiltinSig [("obj", anyType)] boolType)),
    ("print", .function (mkBuiltinSig [("obj", anyType)] anyType)),
    ("repr", .function (mkBuiltinSig [("obj", anyType)] strType)),
    ("type", .function (mkBuiltinSig [("obj", anyType)] anyType)),
    ("isinstance", .function (mkBuiltinSig [("obj", anyType), ("cls", anyType)] boolType)),
    ("hasattr", .function (mkBuiltinSig [("obj", anyType), ("name", strType)] boolType)),
    ("getattr", .function (mkBuiltinSig [("obj", anyType), ("name", strType)] anyType)),
    ("setattr", .function (mkBuiltinSig [("obj", anyType), ("name", strType), ("value", anyType)] anyType)),
    ("sorted", .function (mkBuiltinSig [("iterable", anyType)] anyType)),
    ("reversed", .function (mkBuiltinSig [("seq", anyType)] anyType)),
    ("enumerate", .function (mkBuiltinSig [("iterable", anyType)] anyType)),
    ("zip", .function (mkBuiltinSig [("a", anyType), ("b", anyType)] anyType)),
    ("range", .function (mkBuiltinSig [("stop", anyType)] anyType)),
    ("list", .function (mkBuiltinSig [("iterable", anyType)] anyType)),
    ("dict", .function (mkBuiltinSig [("iterable", anyType)] anyType)),
    ("set", .function (mkBuiltinSig [("iterable", anyType)] anyType)),
    ("tuple", .function (mkBuiltinSig [("iterable", anyType)] anyType)),
    ("min", .function (mkBuiltinSig [("a", anyType), ("b", anyType)] anyType)),
    ("max", .function (mkBuiltinSig [("a", anyType), ("b", anyType)] anyType)),
    ("sum", .function (mkBuiltinSig [("iterable", anyType)] anyType)),
    ("any", .function (mkBuiltinSig [("iterable", anyType)] boolType)),
    ("all", .function (mkBuiltinSig [("iterable", anyType)] boolType)),
    ("abs", .function (mkBuiltinSig [("x", anyType)] anyType)),
    ("ord", .function (mkBuiltinSig [("c", strType)] intType)),
    ("chr", .function (mkBuiltinSig [("i", intType)] strType)),
    ("map", .function (mkBuiltinSig [("func", anyType), ("iterable", anyType)] anyType)),
    ("filter", .function (mkBuiltinSig [("func", anyType), ("iterable", anyType)] anyType))
  ]
  entries.foldl (fun ctx (name, info) => ctx.insert name info) {}

-- ═══════════════════════════════════════════════════════════════════════════════
-- The Fold: resolve
--
-- Threads Ctx as accumulator. Declarations extend it. References look up from it.
-- Produces the resolved AST where every node carries its NameInfo.
-- ═══════════════════════════════════════════════════════════════════════════════

-- ═══════════════════════════════════════════════════════════════════════════════
-- The Fold: resolve
--
-- Threads Ctx as accumulator. Declarations extend it. References look up from it.
-- Produces the resolved AST where every node carries its NameInfo.
-- ═══════════════════════════════════════════════════════════════════════════════

private def ann0 : ResolvedAnn := { sr := .none, info := .none }

def resolve (stmts : PythonProgram) : ResolvedPythonProgram :=
  sorry

end -- public section
end Strata.Python.Resolution
