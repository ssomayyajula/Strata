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

partial def resolveComprehension (ctx : Ctx) (f : SourceRange → ResolvedAnn) : Python.comprehension SourceRange → Python.comprehension ResolvedAnn
  | .mk_comprehension a target iter ifs isAsync =>
      .mk_comprehension (f a) (resolveExpr ctx f target) (resolveExpr ctx f iter)
        (mapAnnArr f (resolveExpr ctx f) ifs) (resolveInt f isAsync)

partial def resolveTypeParam (ctx : Ctx) (f : SourceRange → ResolvedAnn) : Python.type_param SourceRange → Python.type_param ResolvedAnn
  | .TypeVar a name bound def_ => .TypeVar (f a) (mapAnnVal f name)
      (mapAnnOpt f (resolveExpr ctx f) bound) (mapAnnOpt f (resolveExpr ctx f) def_)
  | .TypeVarTuple a name def_ => .TypeVarTuple (f a) (mapAnnVal f name) (mapAnnOpt f (resolveExpr ctx f) def_)
  | .ParamSpec a name def_ => .ParamSpec (f a) (mapAnnVal f name) (mapAnnOpt f (resolveExpr ctx f) def_)

partial def resolveExpr (ctx : Ctx) (f : SourceRange → ResolvedAnn) (e : PythonExpr) : ResolvedPythonExpr :=
  match e with
  | .Name a n ectx =>
      let info := ctx[n.val]?.getD .unresolved
      .Name { sr := a, info } (mapAnnVal f n) (resolveExprCtx f ectx)
  | .Call a func args kwargs =>
      let callInfo := match func with
        | .Name _ n _ => ctx[n.val]?.getD .unresolved
        | .Attribute _ _ attr _ => ctx[attr.val]?.getD .unresolved
        | _ => .none
      .Call { sr := a, info := callInfo } (resolveExpr ctx f func)
        (mapAnnArr f (resolveExpr ctx f) args)
        (mapAnnArr f (resolveKeyword ctx f) kwargs)
  | .Attribute a obj attr ectx =>
      .Attribute (f a) (resolveExpr ctx f obj) (mapAnnVal f attr) (resolveExprCtx f ectx)
  | .Constant a c tc => .Constant (f a) (resolveConstant f c) (mapAnnOpt f (mapAnnVal f) tc)
  | .BinOp a left op right => .BinOp (f a) (resolveExpr ctx f left) (resolveOperator f op) (resolveExpr ctx f right)
  | .BoolOp a op operands => .BoolOp (f a) (resolveBoolop f op) (mapAnnArr f (resolveExpr ctx f) operands)
  | .UnaryOp a op operand => .UnaryOp (f a) (resolveUnaryop f op) (resolveExpr ctx f operand)
  | .Compare a left ops comps => .Compare (f a) (resolveExpr ctx f left) (mapAnnArr f (resolveCmpop f) ops) (mapAnnArr f (resolveExpr ctx f) comps)
  | .IfExp a test body orelse => .IfExp (f a) (resolveExpr ctx f test) (resolveExpr ctx f body) (resolveExpr ctx f orelse)
  | .Dict a keys vals => .Dict (f a) (mapAnnArr f (resolveOptExpr ctx f) keys) (mapAnnArr f (resolveExpr ctx f) vals)
  | .Set a elts => .Set (f a) (mapAnnArr f (resolveExpr ctx f) elts)
  | .ListComp a elt gens => .ListComp (f a) (resolveExpr ctx f elt) (mapAnnArr f (resolveComprehension ctx f) gens)
  | .SetComp a elt gens => .SetComp (f a) (resolveExpr ctx f elt) (mapAnnArr f (resolveComprehension ctx f) gens)
  | .DictComp a key val gens => .DictComp (f a) (resolveExpr ctx f key) (resolveExpr ctx f val) (mapAnnArr f (resolveComprehension ctx f) gens)
  | .GeneratorExp a elt gens => .GeneratorExp (f a) (resolveExpr ctx f elt) (mapAnnArr f (resolveComprehension ctx f) gens)
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
  | .Lambda a args body => .Lambda (f a) (resolveArguments ctx f args) (resolveExpr ctx f body)
  | .Slice a start stop step => .Slice (f a) (mapAnnOpt f (resolveExpr ctx f) start) (mapAnnOpt f (resolveExpr ctx f) stop) (mapAnnOpt f (resolveExpr ctx f) step)
  | .TemplateStr a parts => .TemplateStr (f a) (mapAnnArr f (resolveExpr ctx f) parts)
  | .Interpolation a value conv fmtSpec fmt => .Interpolation (f a) (resolveExpr ctx f value) (resolveConstant f conv) (resolveInt f fmtSpec) (mapAnnOpt f (resolveExpr ctx f) fmt)

partial def resolveAlias (f : SourceRange → ResolvedAnn) : Python.alias SourceRange → Python.alias ResolvedAnn
  | .mk_alias a name asname => .mk_alias (f a) (mapAnnVal f name) (mapAnnOpt f (mapAnnVal f) asname)

partial def resolveWithitem (ctx : Ctx) (f : SourceRange → ResolvedAnn) : Python.withitem SourceRange → Python.withitem ResolvedAnn
  | .mk_withitem a ctxExpr optVars => .mk_withitem (f a) (resolveExpr ctx f ctxExpr) (mapAnnOpt f (resolveExpr ctx f) optVars)

partial def resolveExcepthandler (ctx : Ctx) (f : SourceRange → ResolvedAnn) : Python.excepthandler SourceRange → Python.excepthandler ResolvedAnn
  | .ExceptHandler a ty name body => .ExceptHandler (f a) (mapAnnOpt f (resolveExpr ctx f) ty) (mapAnnOpt f (mapAnnVal f) name) (mapAnnArr f (resolveStmt ctx f ·  |>.2) body)

partial def resolveMatchCase (ctx : Ctx) (f : SourceRange → ResolvedAnn) : Python.match_case SourceRange → Python.match_case ResolvedAnn
  | .mk_match_case a pat guard body => .mk_match_case (f a) (sorry) (mapAnnOpt f (resolveExpr ctx f) guard) (mapAnnArr f (resolveStmt ctx f · |>.2) body)

partial def resolveStmt (ctx : Ctx) (f : SourceRange → ResolvedAnn) (s : PythonStmt) : Ctx × ResolvedPythonStmt :=
  match s with
  | .FunctionDef a name args body decorators returns tc typeParams =>
      let sig := extractFuncSig args returns body.val
      let ctx' := ctx.insert name.val (.function sig)
      let info : NameInfo := .function sig
      (ctx', .FunctionDef { sr := a, info } (mapAnnVal f name) (resolveArguments ctx' f args)
        (mapAnnArr f (resolveStmt ctx' f · |>.2) body)
        (mapAnnArr f (resolveExpr ctx' f) decorators)
        (mapAnnOpt f (resolveExpr ctx' f) returns)
        (mapAnnOpt f (mapAnnVal f) tc)
        (mapAnnArr f (resolveTypeParam ctx' f) typeParams))
  | .AsyncFunctionDef a name args body decorators returns tc typeParams =>
      let sig := extractFuncSig args returns body.val
      let ctx' := ctx.insert name.val (.function sig)
      let info : NameInfo := .function sig
      (ctx', .AsyncFunctionDef { sr := a, info } (mapAnnVal f name) (resolveArguments ctx' f args)
        (mapAnnArr f (resolveStmt ctx' f · |>.2) body)
        (mapAnnArr f (resolveExpr ctx' f) decorators)
        (mapAnnOpt f (resolveExpr ctx' f) returns)
        (mapAnnOpt f (mapAnnVal f) tc)
        (mapAnnArr f (resolveTypeParam ctx' f) typeParams))
  | .ClassDef a name bases keywords body decorators typeParams =>
      let fields := body.val.toList.filterMap fun s => match s with
        | .AnnAssign _ (.Name _ n _) annotation _ _ => some (n.val, annotation)
        | _ => Option.none
      let ctx' := ctx.insert name.val (.class_ name.val fields)
      (ctx', .ClassDef { sr := a, info := .class_ name.val fields } (mapAnnVal f name)
        (mapAnnArr f (resolveExpr ctx' f) bases)
        (mapAnnArr f (resolveKeyword ctx' f) keywords)
        (mapAnnArr f (resolveStmt ctx' f · |>.2) body)
        (mapAnnArr f (resolveExpr ctx' f) decorators)
        (mapAnnArr f (resolveTypeParam ctx' f) typeParams))
  | .Import a aliases =>
      let ctx' := aliases.val.foldl (fun c alias => match alias with
        | .mk_alias _ modName asName =>
            let registeredName := match asName.val with
              | some aliasName => aliasName.val
              | none => match modName.val.splitOn "." with
                | first :: _ => first | [] => modName.val
            c.insert registeredName (.module_ modName.val)) ctx
      (ctx', .Import (f a) (mapAnnArr f (resolveAlias f) aliases))
  | .ImportFrom a modName imports level =>
      let ctx' := imports.val.foldl (fun c imp => match imp with
        | .mk_alias _ impName asName =>
            let registeredName := match asName.val with
              | some aliasName => aliasName.val | none => impName.val
            c.insert registeredName .unresolved) ctx
      (ctx', .ImportFrom (f a) (mapAnnOpt f (mapAnnVal f) modName) (mapAnnArr f (resolveAlias f) imports) (mapAnnOpt f (resolveInt f) level))
  | .Assign a targets value tc =>
      let newNames := targets.val.toList.flatMap collectNamesFromTarget
      let ctx' := newNames.foldl (fun c n => c.insert n (.variable (annotationToPythonType Option.none))) ctx
      (ctx', .Assign (f a) (mapAnnArr f (resolveExpr ctx f) targets) (resolveExpr ctx f value) (mapAnnOpt f (mapAnnVal f) tc))
  | .AnnAssign a target ann value simple =>
      let newNames := collectNamesFromTarget target
      let ctx' := newNames.foldl (fun c n => c.insert n (.variable ann)) ctx
      (ctx', .AnnAssign (f a) (resolveExpr ctx f target) (resolveExpr ctx f ann) (mapAnnOpt f (resolveExpr ctx f) value) (resolveInt f simple))
  | .AugAssign a target op value =>
      (ctx, .AugAssign (f a) (resolveExpr ctx f target) (resolveOperator f op) (resolveExpr ctx f value))
  | .If a test body orelse =>
      (ctx, .If (f a) (resolveExpr ctx f test) (mapAnnArr f (resolveStmt ctx f · |>.2) body) (mapAnnArr f (resolveStmt ctx f · |>.2) orelse))
  | .For a target iter body orelse tc =>
      (ctx, .For (f a) (resolveExpr ctx f target) (resolveExpr ctx f iter) (mapAnnArr f (resolveStmt ctx f · |>.2) body) (mapAnnArr f (resolveStmt ctx f · |>.2) orelse) (mapAnnOpt f (mapAnnVal f) tc))
  | .AsyncFor a target iter body orelse tc =>
      (ctx, .AsyncFor (f a) (resolveExpr ctx f target) (resolveExpr ctx f iter) (mapAnnArr f (resolveStmt ctx f · |>.2) body) (mapAnnArr f (resolveStmt ctx f · |>.2) orelse) (mapAnnOpt f (mapAnnVal f) tc))
  | .While a test body orelse =>
      (ctx, .While (f a) (resolveExpr ctx f test) (mapAnnArr f (resolveStmt ctx f · |>.2) body) (mapAnnArr f (resolveStmt ctx f · |>.2) orelse))
  | .Try a body handlers orelse finalbody =>
      (ctx, .Try (f a) (mapAnnArr f (resolveStmt ctx f · |>.2) body) (mapAnnArr f (resolveExcepthandler ctx f) handlers) (mapAnnArr f (resolveStmt ctx f · |>.2) orelse) (mapAnnArr f (resolveStmt ctx f · |>.2) finalbody))
  | .TryStar a body handlers orelse finalbody =>
      (ctx, .TryStar (f a) (mapAnnArr f (resolveStmt ctx f · |>.2) body) (mapAnnArr f (resolveExcepthandler ctx f) handlers) (mapAnnArr f (resolveStmt ctx f · |>.2) orelse) (mapAnnArr f (resolveStmt ctx f · |>.2) finalbody))
  | .With a items body tc =>
      (ctx, .With (f a) (mapAnnArr f (resolveWithitem ctx f) items) (mapAnnArr f (resolveStmt ctx f · |>.2) body) (mapAnnOpt f (mapAnnVal f) tc))
  | .AsyncWith a items body tc =>
      (ctx, .AsyncWith (f a) (mapAnnArr f (resolveWithitem ctx f) items) (mapAnnArr f (resolveStmt ctx f · |>.2) body) (mapAnnOpt f (mapAnnVal f) tc))
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
  let f : SourceRange → ResolvedAnn := fun sr => { sr, info := .none }
  let (_, resolved) := stmts.foldl (init := (builtinContext, (#[] : ResolvedPythonProgram))) fun acc stmt =>
    let (ctx, arr) := acc
    let (ctx', resolved) := resolveStmt ctx f stmt
    (ctx', arr.push resolved)
  resolved

end -- public section
end Strata.Python.Resolution
