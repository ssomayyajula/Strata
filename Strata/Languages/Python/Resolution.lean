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
  deriving Inhabited

structure ResolvedAnn where
  sr : SourceRange
  info : NameInfo
  deriving Inhabited

instance : Inhabited ResolvedAnn where
  default := { sr := .none, info := .unresolved }

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

partial def collectLocalsFromExpr (target : PythonExpr) : List Identifier :=
  match target with
  | .Name _ n _ => [n.val]
  | .Tuple _ elems _ => elems.val.toList.flatMap collectLocalsFromExpr
  | .List _ elems _ => elems.val.toList.flatMap collectLocalsFromExpr
  | .Starred _ inner _ => collectLocalsFromExpr inner
  | .Subscript _ _ _ _ => []
  | .Attribute _ _ _ _ => []
  | .Constant _ _ _ => []
  | .BinOp _ _ _ _ => []
  | .BoolOp _ _ _ => []
  | .UnaryOp _ _ _ => []
  | .Compare _ _ _ _ => []
  | .Call _ _ _ _ => []
  | .IfExp _ _ _ _ => []
  | .Dict _ _ _ => []
  | .Set _ _ => []
  | .ListComp _ _ _ => []
  | .SetComp _ _ _ => []
  | .DictComp _ _ _ _ => []
  | .GeneratorExp _ _ _ => []
  | .Await _ _ => []
  | .Yield _ _ => []
  | .YieldFrom _ _ => []
  | .FormattedValue _ _ _ _ => []
  | .JoinedStr _ _ => []
  | .Lambda _ _ _ => []
  | .NamedExpr _ _ _ => []
  | .Slice _ _ _ _ => []
  | .TemplateStr _ _ => []
  | .Interpolation _ _ _ _ _ => []

partial def collectLocalsFromStmt (s : PythonStmt) : List (Identifier × PythonType) :=
  match s with
  | .Assign _ targets _ _ =>
      targets.val.toList.flatMap fun target =>
        (collectLocalsFromExpr target).map fun n => (n, annotationToPythonType none)
  | .AnnAssign _ target annotation _ _ =>
      (collectLocalsFromExpr target).map fun n => (n, annotation)
  | .AugAssign _ target _ _ =>
      (collectLocalsFromExpr target).map fun n => (n, annotationToPythonType none)
  | .If _ _ bodyStmts elseStmts =>
      bodyStmts.val.toList.flatMap collectLocalsFromStmt ++
      elseStmts.val.toList.flatMap collectLocalsFromStmt
  | .For _ target _ bodyStmts _ _ =>
      let targetNames := (collectLocalsFromExpr target).map fun n => (n, annotationToPythonType none)
      targetNames ++ bodyStmts.val.toList.flatMap collectLocalsFromStmt
  | .While _ _ bodyStmts _ =>
      bodyStmts.val.toList.flatMap collectLocalsFromStmt
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
      let itemVars := items.val.toList.flatMap fun item =>
        match item with
        | .mk_withitem _ _ optVars =>
            match optVars.val with
            | some varExpr => (collectLocalsFromExpr varExpr).map fun n => (n, annotationToPythonType none)
            | none => []
      itemVars ++ bodyStmts.val.toList.flatMap collectLocalsFromStmt
  | .AsyncWith _ items bodyStmts _ =>
      let itemVars := items.val.toList.flatMap fun item =>
        match item with
        | .mk_withitem _ _ optVars =>
            match optVars.val with
            | some varExpr => (collectLocalsFromExpr varExpr).map fun n => (n, annotationToPythonType none)
            | none => []
      itemVars ++ bodyStmts.val.toList.flatMap collectLocalsFromStmt
  | .AsyncFor _ target _ bodyStmts _ _ =>
      let targetNames := (collectLocalsFromExpr target).map fun n => (n, annotationToPythonType none)
      targetNames ++ bodyStmts.val.toList.flatMap collectLocalsFromStmt
  | .Match _ _ cases =>
      cases.val.toList.flatMap fun c =>
        match c with
        | .mk_match_case _ _ _ caseBody => caseBody.val.toList.flatMap collectLocalsFromStmt
  | .FunctionDef _ name _ _ _ _ _ _ => [(name.val, annotationToPythonType none)]
  | .AsyncFunctionDef _ name _ _ _ _ _ _ => [(name.val, annotationToPythonType none)]
  | .ClassDef _ name _ _ _ _ _ => [(name.val, annotationToPythonType none)]
  | .Return _ _ => []
  | .Delete _ _ => []
  | .Raise _ _ _ => []
  | .Assert _ _ _ => []
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
  | .Expr _ _ => []
  | .TypeAlias _ nameExpr _ _ =>
      match nameExpr with
      | .Name _ n _ => [(n.val, annotationToPythonType none)]
      | _ => []

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
-- ═══════════════════════════════════════════════════════════════════════════════

-- TODO: implement the full fold
-- Stub: annotates all nodes with .unresolved
def resolve (stmts : PythonProgram) : ResolvedPythonProgram :=
  stmts.map fun _stmt => sorry

end -- public section
end Strata.Python.Resolution
