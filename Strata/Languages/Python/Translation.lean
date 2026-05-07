/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.Laurel
public import Strata.Languages.Python.PythonDialect
public import Strata.Languages.Python.NameResolution
import Strata.DDM.Util.SourceRange

namespace Strata.Python.Translation

open Laurel
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
-- State + Monad
-- ═══════════════════════════════════════════════════════════════════════════════

structure TransState where
  freshCounter : Nat := 0
  filePath : String := ""
  loopLabels : List (String × String) := []
  variableTypes : Std.HashMap String String := {}
  deriving Inhabited

abbrev TransM := ReaderT Resolution.TypeEnv (StateT TransState (Except TransError))

-- ═══════════════════════════════════════════════════════════════════════════════
-- Smart Constructors
-- ═══════════════════════════════════════════════════════════════════════════════

private def sourceRangeToMd (filePath : String) (sr : SourceRange) : Imperative.MetaData Core.Expression :=
  let uri : Uri := .file filePath
  #[⟨ Imperative.MetaData.fileRange, .fileRange ⟨ uri, sr ⟩ ⟩]

def mkExpr (sr : SourceRange) (expr : StmtExpr) : TransM StmtExprMd := do
  let filePath := (← get).filePath
  pure { val := expr, md := sourceRangeToMd filePath sr }

def mkTypeMd (sr : SourceRange) (ty : HighType) : TransM HighTypeMd := do
  let filePath := (← get).filePath
  pure { val := ty, md := sourceRangeToMd filePath sr }

private def defaultMd : Imperative.MetaData Core.Expression := #[]

def mkExprDefault (expr : StmtExpr) : StmtExprMd :=
  { val := expr, md := defaultMd }

def mkTypeDefault (ty : HighType) : HighTypeMd :=
  { val := ty, md := defaultMd }

-- ═══════════════════════════════════════════════════════════════════════════════
-- Type Annotations
-- ═══════════════════════════════════════════════════════════════════════════════

def pythonTypeToLaurel (typeStr : String) : HighType :=
  match typeStr with
  | "int" => .TInt | "bool" => .TBool | "str" => .TString
  | "float" => .TFloat64 | "None" => .TVoid | "Any" => .TCore "Any"
  | other => .UserDefined (Identifier.mk other none)

partial def extractTypeStr (e : Python.expr SourceRange) : String :=
  match e with
  | .Name _ n _ => n.val
  | .Constant _ (.ConString _ s) _ => s.val
  | .Subscript _ val slice _ => s!"{extractTypeStr val}[{extractTypeStr slice}]"
  | .Attribute _ val attr _ => s!"{extractTypeStr val}.{attr.val}"
  | .Tuple _ elts _ => String.intercalate ", " (elts.val.toList.map extractTypeStr)
  | .BinOp _ left _ right => s!"{extractTypeStr left} | {extractTypeStr right}"
  | _ => "Any"

-- ═══════════════════════════════════════════════════════════════════════════════
-- Monad Helpers
-- ═══════════════════════════════════════════════════════════════════════════════

def freshVar (pfx : String := "tmp") : TransM String := do
  let s ← get; set { s with freshCounter := s.freshCounter + 1 }; return s!"{pfx}_{s.freshCounter}"

def pushLoopLabel (pfx : String) : TransM (String × String) := do
  let s ← get
  let breakLabel := s!"{pfx}_break_{s.freshCounter}"
  let continueLabel := s!"{pfx}_continue_{s.freshCounter}"
  set { s with freshCounter := s.freshCounter + 1, loopLabels := (breakLabel, continueLabel) :: s.loopLabels }
  return (breakLabel, continueLabel)

def popLoopLabel : TransM Unit := modify fun s => { s with loopLabels := s.loopLabels.tail! }

def currentBreakLabel : TransM (Option String) := do return (← get).loopLabels.head?.map (·.1)
def currentContinueLabel : TransM (Option String) := do return (← get).loopLabels.head?.map (·.2)

def lookupName (name : String) : TransM (Option NameInfo) := do return (← read).names[name]?
def lookupBuiltin (name : String) : TransM (Option String) := do return (← read).builtinMap[name]?
def lookupClassFields (className : String) : TransM (List (String × HighType)) := do
  return (← read).classFields[className]?.getD []

def recordVariableType (varName className : String) : TransM Unit :=
  modify fun s => { s with variableTypes := s.variableTypes.insert varName className }
def lookupVariableType (varName : String) : TransM (Option String) := do
  return (← get).variableTypes[varName]?

-- ═══════════════════════════════════════════════════════════════════════════════
-- Kwargs + Defaults
-- ═══════════════════════════════════════════════════════════════════════════════

def translateKwargs (kwargs : Array (Python.keyword SourceRange)) (translateE : Python.expr SourceRange → TransM StmtExprMd) : TransM (List (String × StmtExprMd)) := do
  kwargs.toList.filterMapM fun kw => match kw with
    | .mk_keyword _ kwName kwExpr => do
      let val ← translateE kwExpr
      match kwName.val with | some n => pure (some (n.val, val)) | none => pure none

def resolveKwargs (funcName : String) (posArgs : List StmtExprMd)
    (kwargs : List (String × StmtExprMd)) : TransM (List StmtExprMd) := do
  let env ← read
  match env.names[funcName]? with
  | some (.function sig) =>
      let numPos := posArgs.length
      let totalParams := sig.params.length
      if kwargs.isEmpty && numPos >= totalParams then return posArgs
      let remainingParams := sig.params.drop numPos
      let remainingDefaults := sig.defaults.drop numPos
      let mut ordered := posArgs
      let mut idx := 0
      for (paramName, _) in remainingParams do
        match kwargs.find? (fun (name, _) => name == paramName) with
        | some (_, val) => ordered := ordered ++ [val]
        | none =>
            let hasDefault := match remainingDefaults[idx]? with
              | some (some _) => true | _ => false
            if hasDefault then
              ordered := ordered ++ [mkExprDefault (.StaticCall "from_None" [])]
        idx := idx + 1
      return ordered
  | _ =>
      if kwargs.isEmpty then return posArgs
      return posArgs ++ kwargs.map (·.2)

-- ═══════════════════════════════════════════════════════════════════════════════
-- The Fold
-- ═══════════════════════════════════════════════════════════════════════════════

mutual

partial def translateExpr (e : Python.expr SourceRange) : TransM StmtExprMd := do
  match e with
  | .Constant sr (.ConPos _ n) _ => mkExpr sr (.LiteralInt n.val)
  | .Constant sr (.ConNeg _ n) _ => mkExpr sr (.LiteralInt (-n.val))
  | .Constant sr (.ConString _ s) _ => mkExpr sr (.LiteralString s.val)
  | .Constant sr (.ConTrue _) _ => mkExpr sr (.LiteralBool true)
  | .Constant sr (.ConFalse _) _ => mkExpr sr (.LiteralBool false)
  | .Constant sr (.ConNone _) _ => mkExpr sr (.StaticCall "from_None" [])
  | .Constant sr (.ConFloat _ f) _ => mkExpr sr (.LiteralString f.val)
  | .Constant sr (.ConBytes _ _) _ => mkExpr sr .Hole
  | .Constant sr (.ConComplex _ _ _) _ => mkExpr sr .Hole
  | .Constant sr (.ConEllipsis _) _ => mkExpr sr .Hole
  | .Name sr name _ => mkExpr sr (.Identifier name.val)
  | .BinOp sr left op right => do
      let l ← translateExpr left; let r ← translateExpr right
      let opName := match op with
        | .Add _ => "PAdd" | .Sub _ => "PSub" | .Mult _ => "PMul" | .Div _ => "PDiv"
        | .FloorDiv _ => "PFloorDiv" | .Mod _ => "PMod" | .Pow _ => "PPow"
        | .BitAnd _ => "PBitAnd" | .BitOr _ => "PBitOr" | .BitXor _ => "PBitXor"
        | .LShift _ => "PLShift" | .RShift _ => "PRShift" | .MatMult _ => "PMatMul"
      mkExpr sr (.StaticCall opName [l, r])
  | .Compare sr left ops comparators => do
      if ops.val.size != 1 || comparators.val.size != 1 then
        throw (.unsupportedConstruct "Chained comparisons")
      let l ← translateExpr left; let r ← translateExpr comparators.val[0]!
      let opName := match ops.val[0]! with
        | .Eq _ => "PEq" | .NotEq _ => "PNEq" | .Lt _ => "PLt" | .LtE _ => "PLe"
        | .Gt _ => "PGt" | .GtE _ => "PGe" | .In _ => "PIn" | .NotIn _ => "PNotIn"
        | .Is _ => "PIs" | .IsNot _ => "PIsNot"
      mkExpr sr (.StaticCall opName [l, r])
  | .BoolOp sr op values => do
      if values.val.size < 2 then throw (.internalError "BoolOp requires at least 2 operands")
      let opName := match op with | .And _ => "PAnd" | .Or _ => "POr"
      let mut exprs ← values.val.toList.mapM translateExpr
      let mut result := exprs[0]!
      for i in [1:exprs.length] do
        result ← mkExpr sr (.StaticCall opName [result, exprs[i]!])
      pure result
  | .UnaryOp sr op operand => do
      let e ← translateExpr operand
      let opName := match op with | .Not _ => "PNot" | .USub _ => "PNeg" | .UAdd _ => "PPos" | .Invert _ => "PInvert"
      mkExpr sr (.StaticCall opName [e])
  | .Call sr func args kwargs => translateCall sr func args kwargs
  | .Attribute sr obj attr _ => do
      let objExpr ← translateExpr obj
      mkExpr sr (.FieldSelect objExpr attr.val)
  | .Subscript sr container slice _ => do
      let containerExpr ← translateExpr container
      let indexExpr ← match slice with
        | .Slice sr' start stop _step => do
            let startE ← match start.val with | some e => translateExpr e | none => mkExpr sr' (.LiteralInt 0)
            let stopE ← match stop.val with | some e => translateExpr e | none => mkExpr sr' (.LiteralInt (-1))
            mkExpr sr' (.StaticCall "from_Slice" [startE, stopE])
        | _ => translateExpr slice
      mkExpr sr (.StaticCall "Any_get" [containerExpr, indexExpr])
  | .List sr elts _ => do
      let elements ← elts.val.toList.mapM translateExpr
      let nil ← mkExpr sr (.StaticCall "ListAny_nil" [])
      let consList ← elements.foldrM (fun elem acc => mkExpr sr (.StaticCall "ListAny_cons" [elem, acc])) nil
      mkExpr sr (.StaticCall "from_ListAny" [consList])
  | .Tuple sr elts _ => do
      let elements ← elts.val.toList.mapM translateExpr
      let nil ← mkExpr sr (.StaticCall "ListAny_nil" [])
      let consList ← elements.foldrM (fun elem acc => mkExpr sr (.StaticCall "ListAny_cons" [elem, acc])) nil
      mkExpr sr (.StaticCall "from_ListAny" [consList])
  | .Dict sr keys vals => do
      let keyExprs ← keys.val.toList.mapM (fun k => match k with
        | .some_expr _ e => translateExpr e | .missing_expr sr' => mkExpr sr' .Hole)
      let valExprs ← vals.val.toList.mapM translateExpr
      let empty ← mkExpr sr (.StaticCall "DictStrAny_empty" [])
      let consChain ← (List.zip keyExprs valExprs).foldrM (fun (k, v) acc => mkExpr sr (.StaticCall "DictStrAny_cons" [k, v, acc])) empty
      mkExpr sr (.StaticCall "from_DictStrAny" [consChain])
  | .IfExp sr test body orelse => do
      let t ← translateExpr test; let b ← translateExpr body; let e ← translateExpr orelse
      mkExpr sr (.IfThenElse t b (some e))
  | .JoinedStr sr values => do
      if values.val.isEmpty then mkExpr sr (.LiteralString "")
      else do
        let parts ← values.val.toList.mapM translateExpr
        let mut result ← mkExpr sr (.LiteralString "")
        for part in parts do result ← mkExpr sr (.StaticCall "PAdd" [result, part])
        pure result
  | .FormattedValue sr value _ _ => do
      let v ← translateExpr value; mkExpr sr (.StaticCall "to_string_any" [v])
  | .Lambda sr .. => mkExpr sr .Hole
  | .Set sr .. => mkExpr sr .Hole
  | .ListComp sr .. => mkExpr sr .Hole
  | .SetComp sr .. => mkExpr sr .Hole
  | .DictComp sr .. => mkExpr sr .Hole
  | .GeneratorExp sr .. => mkExpr sr .Hole
  | .NamedExpr sr .. => mkExpr sr .Hole
  | .Slice sr .. => mkExpr sr .Hole
  | .Starred sr .. => mkExpr sr .Hole
  | .Await sr .. => mkExpr sr .Hole
  | .Yield sr .. => mkExpr sr .Hole
  | .YieldFrom sr .. => mkExpr sr .Hole
  | .TemplateStr sr .. => mkExpr sr .Hole
  | .Interpolation sr .. => mkExpr sr .Hole

-- ═══════════════════════════════════════════════════════════════════════════════
-- translateCall: THE single entry point for all call resolution.
-- ═══════════════════════════════════════════════════════════════════════════════

partial def translateCall (sr : SourceRange) (func : Python.expr SourceRange)
    (args : Ann (Array (Python.expr SourceRange)) SourceRange)
    (kwargs : Ann (Array (Python.keyword SourceRange)) SourceRange) : TransM StmtExprMd := do
  let posArgs ← args.val.toList.mapM translateExpr
  let kwargPairs ← translateKwargs kwargs.val translateExpr
  match func with
  | .Attribute _ receiver methodName _ =>
    let isModule ← match receiver with
      | .Name _ rName _ => do match (← lookupName rName.val) with | some (.module_ _) => pure true | _ => pure false
      | _ => pure false
    if isModule then
      let moduleName := match receiver with | .Name _ rName _ => rName.val | _ => "unknown"
      let funcName := s!"{moduleName}_{methodName.val}"
      let allArgs ← resolveKwargs funcName posArgs kwargPairs
      mkExpr sr (.StaticCall funcName allArgs)
    else
      let objExpr ← translateExpr receiver
      let qualifiedName ← resolveMethodName receiver methodName.val sr
      let allArgs ← resolveKwargs qualifiedName (objExpr :: posArgs) kwargPairs
      mkExpr sr (.StaticCall qualifiedName allArgs)
  | .Name _ calleeName _ =>
    let builtin ← lookupBuiltin calleeName.val
    match builtin with
    | some laurelName =>
      let allArgs ← resolveKwargs laurelName posArgs kwargPairs
      mkExpr sr (.StaticCall laurelName allArgs)
    | none =>
      let info ← lookupName calleeName.val
      match info with
      | some (.class_ className _) =>
        -- Object construction: New + __init__ (Architecture §"Object construction")
        let tmpName ← freshVar "new"
        let classId := Identifier.mk className none
        let newExpr ← mkExpr sr (.New classId)
        let tmpDecl ← mkExpr sr (.LocalVariable tmpName (mkTypeDefault (.UserDefined classId)) (some newExpr))
        let tmpRef ← mkExpr sr (.Identifier tmpName)
        let initName := s!"{className}@__init__"
        let allInitArgs ← resolveKwargs initName (tmpRef :: posArgs) kwargPairs
        let initCall ← mkExpr sr (.StaticCall initName allInitArgs)
        mkExpr sr (.Block [tmpDecl, initCall, tmpRef] none)
      | some (.function sig) =>
        let allArgs ← resolveKwargs sig.name posArgs kwargPairs
        mkExpr sr (.StaticCall sig.name allArgs)
      | _ =>
        let allArgs ← resolveKwargs calleeName.val posArgs kwargPairs
        mkExpr sr (.StaticCall calleeName.val allArgs)
  | _ => mkExpr sr (.StaticCall "call" posArgs)

partial def resolveMethodName (receiver : Python.expr SourceRange) (methodName : String) (sr : SourceRange) : TransM String := do
  match receiver with
  | .Name _ rName _ =>
    let info ← lookupName rName.val
    let classNameOpt ← match info with
      | some (.variable (.UserDefined id)) => pure (some id.text)
      | _ => lookupVariableType rName.val
    match classNameOpt with
    | some className =>
      let qName := s!"{className}@{methodName}"
      let methodInfo ← lookupName qName
      match methodInfo with
      | some _ => pure qName
      | none =>
        let initInfo ← lookupName s!"{className}@__init__"
        let classInfo ← lookupName className
        if initInfo.isSome || classInfo.isSome then throw (.userError sr s!"Unknown method '{methodName}'")
        else pure methodName
    | none => pure methodName
  | _ => pure methodName

-- ═══════════════════════════════════════════════════════════════════════════════
-- Statement Translation
-- ═══════════════════════════════════════════════════════════════════════════════

partial def translateStmt (s : Python.stmt SourceRange) : TransM (List StmtExprMd) := do
  let sr := s.ann
  match s with
  | .Assign _ targets value _ => do
    if targets.val.size == 1 then
      let target := targets.val[0]!
      match target with
      | .Tuple _ elts _ => translateTupleUnpack sr elts.val.toList value
      | _ => translateAssignSingle sr target value
    else throw (.unsupportedConstruct "Multiple assignment targets")

  | .AnnAssign _ target annotation value _ => do
    match target with
    | .Name _ varName _ =>
      let annType := extractTypeStr annotation
      match (← lookupName annType) with
      | some (.class_ className _) => recordVariableType varName.val className
      | _ => pure ()
    | _ => pure ()
    match value.val with
    | some val => translateAssignSingle sr target val
    | none => pure []

  | .AugAssign _ target op value => do
    let targetExpr ← translateExpr target; let valueExpr ← translateExpr value
    let opName := match op with
      | .Add _ => "PAdd" | .Sub _ => "PSub" | .Mult _ => "PMul" | .Div _ => "PDiv"
      | .FloorDiv _ => "PFloorDiv" | .Mod _ => "PMod" | .Pow _ => "PPow"
      | .BitAnd _ => "PBitAnd" | .BitOr _ => "PBitOr" | .BitXor _ => "PBitXor"
      | .LShift _ => "PLShift" | .RShift _ => "PRShift" | .MatMult _ => "PMatMul"
    let rhs ← mkExpr sr (.StaticCall opName [targetExpr, valueExpr])
    let assign ← mkExpr sr (.Assign [targetExpr] rhs)
    pure [assign]

  | .If _ test body orelse => do
    let condExpr ← translateExpr test
    let bodyStmts ← translateStmtList body.val.toList
    let bodyBlock ← mkExpr sr (.Block bodyStmts none)
    let elseBlock ← if orelse.val.isEmpty then pure none
      else do let es ← translateStmtList orelse.val.toList; pure (some (← mkExpr sr (.Block es none)))
    let ifExpr ← mkExpr sr (.IfThenElse condExpr bodyBlock elseBlock)
    pure [ifExpr]

  | .While _ test body _orelse => do
    let (breakLabel, continueLabel) ← pushLoopLabel "loop"
    let condExpr ← translateExpr test
    let bodyStmts ← translateStmtList body.val.toList
    let continueBlock ← mkExpr sr (.Block bodyStmts (some continueLabel))
    let whileExpr ← mkExpr sr (.While condExpr [] none continueBlock)
    let breakBlock ← mkExpr sr (.Block [whileExpr] (some breakLabel))
    popLoopLabel; pure [breakBlock]

  | .For _ target iter body _orelse _ => do
    let (breakLabel, continueLabel) ← pushLoopLabel "for"
    let iterExpr ← translateExpr iter
    let bodyStmts ← translateStmtList body.val.toList
    let (havocStmts, assumeTarget) ← match target with
      | .Tuple _ elts _ => do
        let tmpName ← freshVar "for_unpack"
        let holeExpr ← mkExpr sr (.Hole (deterministic := false))
        let tmpRef ← mkExpr sr (.Identifier tmpName)
        let tmpAssign ← mkExpr sr (.Assign [tmpRef] holeExpr)
        let mut assigns : List StmtExprMd := [tmpAssign]
        let mut idx : Int := 0
        for elt in elts.val.toList do
          let tgtExpr ← translateExpr elt
          let idxLit ← mkExpr sr (.LiteralInt idx)
          let getExpr ← mkExpr sr (.StaticCall "Any_get" [tmpRef, idxLit])
          assigns := assigns ++ [← mkExpr sr (.Assign [tgtExpr] getExpr)]
          idx := idx + 1
        pure (assigns, tmpRef)
      | _ => do
        let targetExpr ← translateExpr target
        let holeExpr ← mkExpr sr (.Hole (deterministic := false))
        let havoc ← mkExpr sr (.Assign [targetExpr] holeExpr)
        pure ([havoc], targetExpr)
    let inExpr ← mkExpr sr (.StaticCall "PIn" [assumeTarget, iterExpr])
    let assume ← mkExpr sr (.Assume inExpr)
    let continueBlock ← mkExpr sr (.Block (havocStmts ++ [assume] ++ bodyStmts) (some continueLabel))
    let breakBlock ← mkExpr sr (.Block [continueBlock] (some breakLabel))
    popLoopLabel; pure [breakBlock]

  | .Return _ value => do
    match value.val with
    | some expr => do
      let e ← translateExpr expr
      let laurelResult ← mkExpr sr (.Identifier "LaurelResult")
      let assign ← mkExpr sr (.Assign [laurelResult] e)
      let exit ← mkExpr sr (.Exit "$body")
      pure [assign, exit]
    | none => do let exit ← mkExpr sr (.Exit "$body"); pure [exit]

  | .Assert _ test _msg => do
    let condExpr ← translateExpr test
    let assertExpr ← mkExpr sr (.Assert condExpr)
    pure [assertExpr]

  | .Expr _ value => do let expr ← translateExpr value; pure [expr]
  | .Pass _ => pure []

  | .Break _ => do
    match (← currentBreakLabel) with
    | some l => do let e ← mkExpr sr (.Exit l); pure [e]
    | none => do let e ← mkExpr sr (.Exit "break"); pure [e]

  | .Continue _ => do
    match (← currentContinueLabel) with
    | some l => do let e ← mkExpr sr (.Exit l); pure [e]
    | none => do let e ← mkExpr sr (.Exit "continue"); pure [e]

  | .Try _ body handlers _orelse _finalbody => translateTryExcept sr body handlers
  | .TryStar _ body handlers _orelse _finalbody => translateTryExcept sr body handlers

  | .With _ items body _ => do
    let mut preamble : List StmtExprMd := []
    let mut cleanup : List StmtExprMd := []
    for item in items.val do
      match item with
      | .mk_withitem _ ctxExpr optVars => do
        let ctxVal ← translateExpr ctxExpr
        let mgrType ← match ctxExpr with
          | .Name _ rName _ => do
            match (← lookupVariableType rName.val) with
            | some cn => pure cn
            | none => match (← lookupName rName.val) with
              | some (.variable (.UserDefined id)) => pure id.text
              | _ => pure "Any"
          | _ => pure "Any"
        let enterName := if mgrType == "Any" then "__enter__" else s!"{mgrType}@__enter__"
        let exitName := if mgrType == "Any" then "__exit__" else s!"{mgrType}@__exit__"
        let enterCall ← if mgrType == "Any" then mkExpr sr .Hole else mkExpr sr (.StaticCall enterName [ctxVal])
        let exitCall ← if mgrType == "Any" then mkExpr sr .Hole else mkExpr sr (.StaticCall exitName [ctxVal])
        match optVars.val with
        | some varExpr => do
          let varTarget ← translateExpr varExpr
          preamble := preamble ++ [← mkExpr sr (.Assign [varTarget] enterCall)]
        | none => preamble := preamble ++ [enterCall]
        cleanup := cleanup ++ [exitCall]
    let bodyStmts ← translateStmtList body.val.toList
    pure (preamble ++ bodyStmts ++ cleanup)

  | .Raise _ exc _ => do
    match exc.val with
    | some excExpr => do
      let errorExpr ← match excExpr with
        | .Call _ (.Name _ excName _) excArgs _ => do
          let errorCtor := match excName.val with
            | "TypeError" => "TypeError" | "AttributeError" => "AttributeError"
            | "AssertionError" => "AssertionError" | "IndexError" => "IndexError"
            | _ => "UnimplementedError"
          let msgArg ← if excArgs.val.size > 0 then translateExpr excArgs.val[0]!
            else mkExpr sr (.LiteralString "")
          mkExpr sr (.StaticCall errorCtor [msgArg])
        | _ => do let e ← translateExpr excExpr; mkExpr sr (.StaticCall "UnimplementedError" [e])
      let maybeExcRef ← mkExpr sr (.Identifier "maybe_except")
      let assign ← mkExpr sr (.Assign [maybeExcRef] errorExpr)
      pure [assign]
    | none => do
      let errExpr ← mkExpr sr (.StaticCall "UnimplementedError" [mkExprDefault (.LiteralString "re-raise")])
      let ref ← mkExpr sr (.Identifier "maybe_except")
      pure [← mkExpr sr (.Assign [ref] errExpr)]

  | .Import _ _ => pure []
  | .ImportFrom _ _ _ _ => pure []
  | .Delete _ _ => do pure [← mkExpr sr .Hole]
  | .Global _ _ => pure []
  | .Nonlocal _ _ => pure []
  | .ClassDef .. => pure [← mkExpr sr .Hole]
  | .FunctionDef .. => pure [← mkExpr sr .Hole]
  | .Match _ .. => pure [← mkExpr sr .Hole]
  | .AsyncFor _ .. => pure [← mkExpr sr .Hole]
  | .AsyncWith _ .. => pure [← mkExpr sr .Hole]
  | .AsyncFunctionDef _ .. => pure [← mkExpr sr .Hole]
  | .TypeAlias _ .. => pure [← mkExpr sr .Hole]

-- ═══════════════════════════════════════════════════════════════════════════════
-- Assign helpers
-- ═══════════════════════════════════════════════════════════════════════════════

partial def translateAssignSingle (sr : SourceRange) (target : Python.expr SourceRange) (value : Python.expr SourceRange) : TransM (List StmtExprMd) := do
  -- Check if RHS is a class constructor → two-phase desugaring
  match value with
  | .Call _ (.Name _ calleeName _) callArgs callKwargs => do
    let info ← lookupName calleeName.val
    match info with
    | some (.class_ className _) => do
      match target with
      | .Name _ varName _ => recordVariableType varName.val className
      | _ => pure ()
      let targetExpr ← translateExpr target
      let classId := Identifier.mk className none
      let newExpr ← mkExpr sr (.New classId)
      let assignNew ← mkExpr sr (.Assign [targetExpr] newExpr)
      let posArgs ← callArgs.val.toList.mapM translateExpr
      let kwargPairs ← translateKwargs callKwargs.val translateExpr
      let initName := s!"{className}@__init__"
      let allInitArgs ← resolveKwargs initName (targetExpr :: posArgs) kwargPairs
      let initCall ← mkExpr sr (.StaticCall initName allInitArgs)
      pure [assignNew, initCall]
    | _ => do
      let targetExpr ← translateExpr target
      let valueExpr ← translateExpr value
      pure [← mkExpr sr (.Assign [targetExpr] valueExpr)]
  | _ => do
    let targetExpr ← translateExpr target
    let valueExpr ← translateExpr value
    pure [← mkExpr sr (.Assign [targetExpr] valueExpr)]

partial def translateTupleUnpack (sr : SourceRange) (elts : List (Python.expr SourceRange)) (value : Python.expr SourceRange) : TransM (List StmtExprMd) := do
  let rhsExpr ← translateExpr value
  let tmpName ← freshVar "unpack"
  let tmpDecl ← mkExpr sr (.LocalVariable tmpName (mkTypeDefault (.TCore "Any")) (some rhsExpr))
  let tmpRef ← mkExpr sr (.Identifier tmpName)
  let mut assigns : List StmtExprMd := [tmpDecl]
  let mut idx : Int := 0
  for elt in elts do
    let tgtExpr ← translateExpr elt
    let idxExpr ← mkExpr sr (.LiteralInt idx)
    let getExpr ← mkExpr sr (.StaticCall "Any_get" [tmpRef, idxExpr])
    assigns := assigns ++ [← mkExpr sr (.Assign [tgtExpr] getExpr)]
    idx := idx + 1
  pure assigns

partial def translateTryExcept (sr : SourceRange)
    (body : Ann (Array (Python.stmt SourceRange)) SourceRange)
    (handlers : Ann (Array (Python.excepthandler SourceRange)) SourceRange) : TransM (List StmtExprMd) := do
  let tryLabel := s!"try_end_{sr.start.byteIdx}"
  let catchersLabel := s!"exception_handlers_{sr.start.byteIdx}"
  let bodyStmts ← translateStmtList body.val.toList
  let mut bodyStmtsWithChecks : List StmtExprMd := []
  for stmt in bodyStmts do
    bodyStmtsWithChecks := bodyStmtsWithChecks ++ [stmt]
    let maybeExcRef ← mkExpr sr (.Identifier "maybe_except")
    let isException ← mkExpr sr (.StaticCall "isError" [maybeExcRef])
    let exitToHandler ← mkExpr sr (.Exit catchersLabel)
    let errorCheck ← mkExpr sr (.IfThenElse isException exitToHandler none)
    bodyStmtsWithChecks := bodyStmtsWithChecks ++ [errorCheck]
  let exitTry ← mkExpr sr (.Exit tryLabel)
  let catchersBlock ← mkExpr sr (.Block (bodyStmtsWithChecks ++ [exitTry]) (some catchersLabel))
  let mut handlerStmts : List StmtExprMd := []
  for handler in handlers.val do
    match handler with
    | .ExceptHandler _ _ _excName handlerBody => do
      handlerStmts := handlerStmts ++ (← translateStmtList handlerBody.val.toList)
  let tryBlock ← mkExpr sr (.Block ([catchersBlock] ++ handlerStmts) (some tryLabel))
  pure [tryBlock]

partial def translateStmtList (stmts : List (Python.stmt SourceRange)) : TransM (List StmtExprMd) := do
  let mut result : List StmtExprMd := []
  for stmt in stmts do result := result ++ (← translateStmt stmt)
  return result

-- ═══════════════════════════════════════════════════════════════════════════════
-- Function/Class/Module Translation
-- ═══════════════════════════════════════════════════════════════════════════════

partial def emitScopeDeclarations (sr : SourceRange)
    (body : Array (Python.stmt SourceRange)) (paramNames : List String) : TransM (List StmtExprMd) := do
  let typedLocals := Resolution.TypeEnv.getFunctionLocals body paramNames
  let env ← read
  let mut decls : List StmtExprMd := []
  for (varName, varType) in typedLocals do
    let actualType := match varType with
      | .TCore "Any" =>
        let annType := body.toList.findSome? fun stmt => match stmt with
          | .AnnAssign _ (.Name _ n _) ann _ _ =>
            if n.val == varName then
              match env.names[extractTypeStr ann]? with
              | some (.class_ className _) => some (HighType.UserDefined (Identifier.mk className none))
              | _ => none
            else none
          | _ => none
        annType.getD varType
      | _ => varType
    decls := decls ++ [← mkExpr sr (.LocalVariable (Identifier.mk varName none) (mkTypeDefault actualType) none)]
  pure decls

partial def emitMutableParamCopies (sr : SourceRange)
    (params : List (String × HighType)) : TransM (List StmtExprMd) := do
  let mut copies : List StmtExprMd := []
  for (pName, pType) in params do
    let inRef ← mkExpr sr (.Identifier s!"$in_{pName}")
    copies := copies ++ [← mkExpr sr (.LocalVariable pName (mkTypeDefault pType) (some inRef))]
  pure copies

partial def translateFunction (s : Python.stmt SourceRange)
    (isMethod : Bool := false) (className : Option String := none) : TransM (Option Procedure) := do
  match s with
  | .FunctionDef sr name args body _decorators _returns _typeComment _ => do
    let procName := match className with | some cn => s!"{cn}@{name.val}" | none => name.val
    let allParams ← do
      match (← lookupName procName) with
      | some (.function sig) =>
        pure (sig.params.map fun (pName, pType) =>
          ({ name := Identifier.mk pName none, type := mkTypeDefault pType } : Parameter))
      | _ => match args with
        | .mk_arguments _ _ argList _ _ _ _ _ =>
          argList.val.toList.mapM fun arg => match arg with
            | .mk_arg _ argName annotation _ =>
              let ty := match annotation.val with | some e => pythonTypeToLaurel (extractTypeStr e) | none => .TCore "Any"
              pure ({ name := Identifier.mk argName.val none, type := mkTypeDefault ty } : Parameter)
    let (inputs, paramCopies) ← if isMethod then do
      let selfType := match className with
        | some cn => HighType.UserDefined (Identifier.mk cn none) | none => .TCore "Any"
      let selfParam : Parameter := { name := Identifier.mk "self" none, type := mkTypeDefault selfType }
      let otherParams := if allParams.length > 0 then allParams.tail! else []
      let renamedParams := otherParams.map (fun p => { p with name := Identifier.mk s!"$in_{p.name.text}" none })
      let copies ← emitMutableParamCopies sr (otherParams.map (fun p => (p.name.text, p.type.val)))
      pure (selfParam :: renamedParams, copies)
    else pure (allParams, [])
    let returnType ← match (← lookupName procName) with
      | some (.function sig) => pure sig.effectType.resultType | _ => pure (.TCore "Any")
    let outputs : List Parameter := [{ name := Identifier.mk "LaurelResult" none, type := mkTypeDefault returnType }]
    let inputNames := inputs.map (·.name.text)
    let originalParamNames := allParams.map (·.name.text)
    let scopeDecls ← emitScopeDeclarations sr body.val (inputNames ++ originalParamNames)
    let noErrorInit ← mkExpr sr (.StaticCall "NoError" [])
    let maybeExceptDecl ← mkExpr sr (.LocalVariable "maybe_except" (mkTypeDefault (.TCore "Error")) (some noErrorInit))
    let bodyStmts ← translateStmtList body.val.toList
    let allStmts := paramCopies ++ scopeDecls ++ [maybeExceptDecl] ++ bodyStmts
    let bodyBlock ← mkExpr sr (.Block allStmts none)
    let filePath := (← get).filePath
    pure (some {
      name := Identifier.mk procName none, inputs, outputs,
      preconditions := [], determinism := .deterministic none,
      decreases := none, isFunctional := false,
      body := .Transparent bodyBlock, md := sourceRangeToMd filePath sr })
  | _ => pure none

partial def extractFields (body : Array (Python.stmt SourceRange)) : TransM (List Field) := do
  let mut fields : List Field := []
  for stmt in body do
    match stmt with
    | .AnnAssign _ (.Name _ fieldName _) _ _ _ =>
      fields := fields ++ [{ name := Identifier.mk fieldName.val none, type := mkTypeDefault (.TCore "Any"), isMutable := true }]
    | _ => pure ()
  return fields

partial def translateClass (s : Python.stmt SourceRange) : TransM (Option (TypeDefinition × List Procedure)) := do
  match s with
  | .ClassDef _ className _bases _ ⟨_, body⟩ _ _ => do
    let classNameStr := className.val
    let envFields ← lookupClassFields classNameStr
    let fields := envFields.map fun (fName, fType) =>
      { name := Identifier.mk fName none, type := mkTypeDefault fType, isMutable := true : Field }
    let mut methods : List Procedure := []
    for stmt in body do
      if let .FunctionDef .. := stmt then
        if let some proc ← translateFunction stmt (isMethod := true) (className := some classNameStr) then
          methods := methods ++ [proc]
    let compositeType : CompositeType := {
      name := Identifier.mk classNameStr none, extending := [],
      fields, instanceProcedures := [] }
    pure (some (.Composite compositeType, methods))
  | _ => pure none

partial def translateModule (stmts : Array (Python.stmt SourceRange)) : TransM Laurel.Program := do
  let mut procedures : List Procedure := []
  let mut types : List TypeDefinition := []
  let mut otherStmts : List (Python.stmt SourceRange) := []
  for stmt in stmts do
    match stmt with
    | .FunctionDef .. => if let some proc ← translateFunction stmt then procedures := procedures ++ [proc]
    | .ClassDef .. => if let some (td, ms) ← translateClass stmt then types := types ++ [td]; procedures := procedures ++ ms
    | _ => otherStmts := otherStmts ++ [stmt]
  if !otherStmts.isEmpty then
    let sr : SourceRange := default
    let nameDecl ← mkExpr sr (.LocalVariable "__name__" (mkTypeDefault .TString) (some (mkExprDefault (.LiteralString "__main__"))))
    let bodyStmts ← translateStmtList otherStmts
    let scopeDecls ← emitScopeDeclarations sr otherStmts.toArray []
    let noErrorInit ← mkExpr sr (.StaticCall "NoError" [])
    let maybeExceptDecl ← mkExpr sr (.LocalVariable "maybe_except" (mkTypeDefault (.TCore "Error")) (some noErrorInit))
    let allStmts := [nameDecl] ++ scopeDecls ++ [maybeExceptDecl] ++ bodyStmts
    let bodyBlock ← mkExpr sr (.Block allStmts none)
    let mainProc : Procedure := { name := Identifier.mk "__main__" none, inputs := [], outputs := [], preconditions := [], determinism := .deterministic none, decreases := none, isFunctional := false, body := .Transparent bodyBlock, md := #[] }
    procedures := procedures ++ [mainProc]
  return { staticProcedures := procedures, staticFields := [], types, constants := [] }

end -- mutual

-- ═══════════════════════════════════════════════════════════════════════════════
-- Runner
-- ═══════════════════════════════════════════════════════════════════════════════

def runTranslation (stmts : Array (Python.stmt SourceRange))
    (env : Resolution.TypeEnv := {}) (filePath : String := "")
    : Except TransError (Laurel.Program × TransState) :=
  (translateModule stmts).run env |>.run { filePath := filePath }

def runTranslationWithBase (stmts : Array (Python.stmt SourceRange))
    (baseEnv : Strata.Python.Resolution.TypeEnv := {}) (filePath : String := "")
    : Except TransError (Laurel.Program × TransState) :=
  runTranslation stmts baseEnv filePath

end -- public section
end Strata.Python.Translation
