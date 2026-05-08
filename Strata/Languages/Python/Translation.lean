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

-- Error

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

-- State + Monad

structure TransState where
  freshCounter : Nat := 0
  filePath : String := ""
  loopLabels : List (String × String) := []
  variableTypes : Std.HashMap String String := {}
  deriving Inhabited

abbrev TransM := ReaderT Resolution.TypeEnv (StateT TransState (Except TransError))

-- Smart Constructors

private def sourceRangeToMd (filePath : String) (sr : SourceRange) : Imperative.MetaData Core.Expression :=
  let uri : Uri := .file filePath
  #[⟨ Imperative.MetaData.fileRange, .fileRange ⟨ uri, sr ⟩ ⟩]

def mkExpr (sr : SourceRange) (expr : StmtExpr) : TransM StmtExprMd := do
  pure { val := expr, md := sourceRangeToMd (← get).filePath sr }

private def defaultMd : Imperative.MetaData Core.Expression := #[]
def mkExprDefault (expr : StmtExpr) : StmtExprMd := { val := expr, md := defaultMd }
def mkTypeDefault (ty : HighType) : HighTypeMd := { val := ty, md := defaultMd }

-- Type Annotations

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

-- Monad Helpers

def freshVar (pfx : String := "tmp") : TransM String := do
  let s ← get; set { s with freshCounter := s.freshCounter + 1 }; return s!"{pfx}_{s.freshCounter}"

def pushLoopLabel (pfx : String) : TransM (String × String) := do
  let s ← get
  let bk := s!"{pfx}_break_{s.freshCounter}"; let ct := s!"{pfx}_continue_{s.freshCounter}"
  set { s with freshCounter := s.freshCounter + 1, loopLabels := (bk, ct) :: s.loopLabels }
  return (bk, ct)

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

-- Kwargs + Defaults

def translateKwargs (kwargs : Array (Python.keyword SourceRange))
    (translateE : Python.expr SourceRange → TransM StmtExprMd) : TransM (List (String × StmtExprMd)) :=
  kwargs.toList.filterMapM fun kw => match kw with
    | .mk_keyword _ kwName kwExpr => do
      let val ← translateE kwExpr
      match kwName.val with | some n => pure (some (n.val, val)) | none => pure none

def resolveKwargs (funcName : String) (posArgs : List StmtExprMd)
    (kwargs : List (String × StmtExprMd)) : TransM (List StmtExprMd) := do
  match (← read).names[funcName]? with
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

-- The Fold

mutual

-- ═══════════════════════════════════════════════════════════════════════════════
-- Expression Translation
-- ═══════════════════════════════════════════════════════════════════════════════

partial def translateExpr (e : Python.expr SourceRange) : TransM StmtExprMd := do
  match e with
  | .Constant sr (.ConPos _ n) _ => mkExpr sr (.LiteralInt n.val)
  | .Constant sr (.ConNeg _ n) _ => mkExpr sr (.LiteralInt (-n.val))
  | .Constant sr (.ConString _ s) _ => mkExpr sr (.LiteralString s.val)
  | .Constant sr (.ConTrue _) _ => mkExpr sr (.LiteralBool true)
  | .Constant sr (.ConFalse _) _ => mkExpr sr (.LiteralBool false)
  | .Constant sr (.ConNone _) _ => mkExpr sr (.StaticCall "from_None" [])
  | .Constant sr (.ConFloat _ f) _ => mkExpr sr (.LiteralString f.val)
  | .Constant sr _ _ => mkExpr sr .Hole
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
      let exprs ← values.val.toList.mapM translateExpr
      let mut result := exprs[0]!
      for i in [1:exprs.length] do result ← mkExpr sr (.StaticCall opName [result, exprs[i]!])
      pure result
  | .UnaryOp sr op operand => do
      let e ← translateExpr operand
      let opName := match op with | .Not _ => "PNot" | .USub _ => "PNeg" | .UAdd _ => "PPos" | .Invert _ => "PInvert"
      mkExpr sr (.StaticCall opName [e])
  | .Call sr func args kwargs => translateCall sr func args kwargs
  | .Attribute sr obj attr _ => do
      mkExpr sr (.FieldSelect (← translateExpr obj) attr.val)
  | .Subscript sr container slice _ => do
      let c ← translateExpr container
      let idx ← match slice with
        | .Slice sr' start stop _ => do
          let s ← match start.val with
            | some e => mkExpr sr' (.StaticCall "Any..as_int!" [← translateExpr e])
            | none => mkExpr sr' (.LiteralInt 0)
          let e ← match stop.val with
            | some e => mkExpr sr' (.StaticCall "OptSome" [← mkExpr sr' (.StaticCall "Any..as_int!" [← translateExpr e])])
            | none => mkExpr sr' (.StaticCall "OptNone" [])
          mkExpr sr' (.StaticCall "from_Slice" [s, e])
        | _ => translateExpr slice
      mkExpr sr (.StaticCall "Any_get" [c, idx])
  | .List sr elts _ => do
      let es ← elts.val.toList.mapM translateExpr
      let nil ← mkExpr sr (.StaticCall "ListAny_nil" [])
      let cons ← es.foldrM (fun e acc => mkExpr sr (.StaticCall "ListAny_cons" [e, acc])) nil
      mkExpr sr (.StaticCall "from_ListAny" [cons])
  | .Tuple sr elts _ => do
      let es ← elts.val.toList.mapM translateExpr
      let nil ← mkExpr sr (.StaticCall "ListAny_nil" [])
      let cons ← es.foldrM (fun e acc => mkExpr sr (.StaticCall "ListAny_cons" [e, acc])) nil
      mkExpr sr (.StaticCall "from_ListAny" [cons])
  | .Dict sr keys vals => do
      let ks ← keys.val.toList.mapM (fun k => match k with
        | .some_expr _ e => translateExpr e | .missing_expr sr' => mkExpr sr' .Hole)
      let vs ← vals.val.toList.mapM translateExpr
      let empty ← mkExpr sr (.StaticCall "DictStrAny_empty" [])
      let cons ← (List.zip ks vs).foldrM (fun (k, v) acc =>
        mkExpr sr (.StaticCall "DictStrAny_cons" [k, v, acc])) empty
      mkExpr sr (.StaticCall "from_DictStrAny" [cons])
  | .IfExp sr test body orelse => do
      mkExpr sr (.IfThenElse (← translateExpr test) (← translateExpr body) (some (← translateExpr orelse)))
  | .JoinedStr sr values => do
      if values.val.isEmpty then mkExpr sr (.LiteralString "")
      else do
        let parts ← values.val.toList.mapM translateExpr
        let mut result ← mkExpr sr (.LiteralString "")
        for p in parts do result ← mkExpr sr (.StaticCall "PAdd" [result, p])
        pure result
  | .FormattedValue sr value _ _ => do mkExpr sr (.StaticCall "to_string_any" [← translateExpr value])
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
-- Call Resolution (single entry point)
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
      let resolvedArgs ← resolveKwargs qualifiedName posArgs kwargPairs
      mkExpr sr (.StaticCall qualifiedName (objExpr :: resolvedArgs))
  | .Name _ calleeName _ =>
    match (← lookupBuiltin calleeName.val) with
    | some laurelName =>
      mkExpr sr (.StaticCall laurelName (← resolveKwargs laurelName posArgs kwargPairs))
    | none => match (← lookupName calleeName.val) with
      | some (.class_ className _) =>
        let tmpName ← freshVar "new"
        let classId := Identifier.mk className none
        let newExpr ← mkExpr sr (.New classId)
        let tmpDecl ← mkExpr sr (.LocalVariable tmpName (mkTypeDefault (.UserDefined classId)) (some newExpr))
        let tmpRef ← mkExpr sr (.Identifier tmpName)
        let initName := s!"{className}@__init__"
        let initCall ← mkExpr sr (.StaticCall initName (tmpRef :: (← resolveKwargs initName posArgs kwargPairs)))
        mkExpr sr (.Block [tmpDecl, initCall, tmpRef] none)
      | some (.function sig) =>
        mkExpr sr (.StaticCall sig.name (← resolveKwargs sig.name posArgs kwargPairs))
      | _ =>
        mkExpr sr (.StaticCall calleeName.val (← resolveKwargs calleeName.val posArgs kwargPairs))
  | _ => mkExpr sr (.StaticCall "call" posArgs)

partial def resolveMethodName (receiver : Python.expr SourceRange) (methodName : String) (sr : SourceRange) : TransM String := do
  match receiver with
  | .Name _ rName _ =>
    let classNameOpt ← match (← lookupName rName.val) with
      | some (.variable (.UserDefined id)) => pure (some id.text)
      | _ => lookupVariableType rName.val
    match classNameOpt with
    | some className =>
      let qName := s!"{className}@{methodName}"
      match (← lookupName qName) with
      | some _ => pure qName
      | none =>
        if (← lookupName s!"{className}@__init__").isSome || (← lookupName className).isSome then
          throw (.userError sr s!"Unknown method '{methodName}'")
        else pure methodName
    | none => pure methodName
  | _ => pure methodName

-- ═══════════════════════════════════════════════════════════════════════════════
-- Unpack: recursive tuple destructuring (arbitrary depth)
-- ═══════════════════════════════════════════════════════════════════════════════

partial def unpackTargets (sr : SourceRange) (elts : List (Python.expr SourceRange))
    (sourceRef : StmtExprMd) : TransM (List StmtExprMd) := do
  let mut stmts : List StmtExprMd := []
  let mut idx : Int := 0
  for elt in elts do
    let getExpr ← mkExpr sr (.StaticCall "Any_get" [sourceRef, ← mkExpr sr (.LiteralInt idx)])
    match elt with
    | .Tuple _ innerElts _ => do
      let innerTmp ← freshVar "unpack"
      let innerRef ← mkExpr sr (.Identifier innerTmp)
      let innerDecl ← mkExpr sr (.LocalVariable innerTmp (mkTypeDefault (.TCore "Any")) (some getExpr))
      stmts := stmts ++ [innerDecl]
      stmts := stmts ++ (← unpackTargets sr innerElts.val.toList innerRef)
    | _ => do
      let tgt ← translateExpr elt
      stmts := stmts ++ [← mkExpr sr (.Assign [tgt] getExpr)]
    idx := idx + 1
  pure stmts

-- ═══════════════════════════════════════════════════════════════════════════════
-- Statement Translation
-- ═══════════════════════════════════════════════════════════════════════════════

partial def translateStmt (s : Python.stmt SourceRange) : TransM (List StmtExprMd) := do
  let sr := s.ann
  match s with
  | .Assign _ targets value _ => do
    if targets.val.size != 1 then throw (.unsupportedConstruct "Multiple assignment targets")
    let target := targets.val[0]!
    match target with
    | .Tuple _ elts _ => do
      let rhsExpr ← translateExpr value
      let tmp ← freshVar "unpack"
      let tmpDecl ← mkExpr sr (.LocalVariable tmp (mkTypeDefault (.TCore "Any")) (some rhsExpr))
      let tmpRef ← mkExpr sr (.Identifier tmp)
      pure ([tmpDecl] ++ (← unpackTargets sr elts.val.toList tmpRef))
    | _ => translateAssignSingle sr target value

  | .AnnAssign _ target annotation value _ => do
    match target with
    | .Name _ varName _ =>
      match (← lookupName (extractTypeStr annotation)) with
      | some (.class_ className _) => recordVariableType varName.val className
      | _ => pure ()
    | _ => pure ()
    match value.val with
    | some val => translateAssignSingle sr target val
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
    let inner ← mkExpr sr (.Block (← translateStmtList body.val.toList) (some ct))
    let outer ← mkExpr sr (.Block [← mkExpr sr (.While cond [] none inner)] (some bk))
    popLoopLabel; pure [outer]

  | .For _ target iter body _ _ => do
    let (bk, ct) ← pushLoopLabel "for"
    let iterExpr ← translateExpr iter
    let bodyStmts ← translateStmtList body.val.toList
    let (havocStmts, assumeTarget) ← match target with
      | .Tuple _ elts _ => do
        let tmp ← freshVar "for_iter"
        let tmpRef ← mkExpr sr (.Identifier tmp)
        let havoc ← mkExpr sr (.Assign [tmpRef] (← mkExpr sr (.Hole (deterministic := false))))
        let unpacks ← unpackTargets sr elts.val.toList tmpRef
        pure ([havoc] ++ unpacks, tmpRef)
      | _ => do
        let tgt ← translateExpr target
        let havoc ← mkExpr sr (.Assign [tgt] (← mkExpr sr (.Hole (deterministic := false))))
        pure ([havoc], tgt)
    let assume ← mkExpr sr (.Assume (← mkExpr sr (.StaticCall "PIn" [assumeTarget, iterExpr])))
    let inner ← mkExpr sr (.Block (havocStmts ++ [assume] ++ bodyStmts) (some ct))
    let outer ← mkExpr sr (.Block [inner] (some bk))
    popLoopLabel; pure [outer]

  | .Return _ value => do
    match value.val with
    | some expr => do
      let e ← translateExpr expr
      pure [← mkExpr sr (.Assign [← mkExpr sr (.Identifier "LaurelResult")] e), ← mkExpr sr (.Exit "$body")]
    | none => pure [← mkExpr sr (.Exit "$body")]

  | .Assert _ test _ => pure [← mkExpr sr (.Assert (← translateExpr test))]
  | .Expr _ value => pure [← translateExpr value]
  | .Pass _ => pure []
  | .Break _ => do pure [← mkExpr sr (.Exit ((← currentBreakLabel).getD "break"))]
  | .Continue _ => do pure [← mkExpr sr (.Exit ((← currentContinueLabel).getD "continue"))]

  | .Try _ body handlers _ _ => translateTryExcept sr body handlers
  | .TryStar _ body handlers _ _ => translateTryExcept sr body handlers

  | .With _ items body _ => do
    let mut pre : List StmtExprMd := []
    let mut post : List StmtExprMd := []
    for item in items.val do
      match item with
      | .mk_withitem _ ctxExpr optVars => do
        let ctxVal ← translateExpr ctxExpr
        let mgrType ← match ctxExpr with
          | .Name _ rName _ => do
            match (← lookupVariableType rName.val) with
            | some cn => pure cn
            | none => match (← lookupName rName.val) with
              | some (.variable (.UserDefined id)) => pure id.text | _ => pure "Any"
          | _ => pure "Any"
        let enter ← if mgrType == "Any" then mkExpr sr .Hole
          else mkExpr sr (.StaticCall s!"{mgrType}@__enter__" [ctxVal])
        let exit ← if mgrType == "Any" then mkExpr sr .Hole
          else mkExpr sr (.StaticCall s!"{mgrType}@__exit__" [ctxVal])
        match optVars.val with
        | some varExpr => pre := pre ++ [← mkExpr sr (.Assign [← translateExpr varExpr] enter)]
        | none => pre := pre ++ [enter]
        post := post ++ [exit]
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
  | .Delete _ _ => pure [← mkExpr sr .Hole]
  | .ClassDef .. => pure [← mkExpr sr .Hole]
  | .FunctionDef .. => pure [← mkExpr sr .Hole]
  | .Match _ .. => pure [← mkExpr sr .Hole]
  | .AsyncFor _ .. => pure [← mkExpr sr .Hole]
  | .AsyncWith _ .. => pure [← mkExpr sr .Hole]
  | .AsyncFunctionDef _ .. => pure [← mkExpr sr .Hole]
  | .TypeAlias _ .. => pure [← mkExpr sr .Hole]

-- ═══════════════════════════════════════════════════════════════════════════════
-- Helpers
-- ═══════════════════════════════════════════════════════════════════════════════

private partial def collectSubscriptChain (expr : Python.expr SourceRange) : TransM (Python.expr SourceRange × List (Python.expr SourceRange)) := do
  match expr with
  | .Subscript _ container slice _ =>
    let (root, innerIndices) ← collectSubscriptChain container
    pure (root, innerIndices ++ [slice])
  | other => pure (other, [])

partial def translateAssignSingle (sr : SourceRange) (target value : Python.expr SourceRange) : TransM (List StmtExprMd) := do
  match target with
  | .Subscript .. => do
    let (root, indices) ← collectSubscriptChain target
    let rootExpr ← translateExpr root
    let mut idxList ← mkExpr sr (.StaticCall "ListAny_nil" [])
    for idx in indices.reverse do
      let idxExpr ← match idx with
        | .Slice sr' start stop _ => do
          let s ← match start.val with
            | some e => mkExpr sr' (.StaticCall "Any..as_int!" [← translateExpr e])
            | none => mkExpr sr' (.LiteralInt 0)
          let e ← match stop.val with
            | some e => mkExpr sr' (.StaticCall "OptSome" [← mkExpr sr' (.StaticCall "Any..as_int!" [← translateExpr e])])
            | none => mkExpr sr' (.StaticCall "OptNone" [])
          mkExpr sr' (.StaticCall "from_Slice" [s, e])
        | _ => translateExpr idx
      idxList ← mkExpr sr (.StaticCall "ListAny_cons" [idxExpr, idxList])
    let rhs ← translateExpr value
    let setsCall ← mkExpr sr (.StaticCall "Any_sets" [idxList, rootExpr, rhs])
    pure [← mkExpr sr (.Assign [rootExpr] setsCall)]
  | _ =>
  match value with
  | .Call _ (.Name _ calleeName _) callArgs callKwargs => do
    match (← lookupName calleeName.val) with
    | some (.class_ className _) => do
      match target with
      | .Name _ varName _ => recordVariableType varName.val className
      | _ => pure ()
      let targetExpr ← translateExpr target
      let classId := Identifier.mk className none
      let assignNew ← mkExpr sr (.Assign [targetExpr] (← mkExpr sr (.New classId)))
      let posArgs ← callArgs.val.toList.mapM translateExpr
      let kwargPairs ← translateKwargs callKwargs.val translateExpr
      let initName := s!"{className}@__init__"
      let initCall ← mkExpr sr (.StaticCall initName (targetExpr :: (← resolveKwargs initName posArgs kwargPairs)))
      pure [assignNew, initCall]
    | _ => do
      pure [← mkExpr sr (.Assign [← translateExpr target] (← translateExpr value))]
  | _ => do
    pure [← mkExpr sr (.Assign [← translateExpr target] (← translateExpr value))]

partial def translateTryExcept (sr : SourceRange)
    (body : Ann (Array (Python.stmt SourceRange)) SourceRange)
    (handlers : Ann (Array (Python.excepthandler SourceRange)) SourceRange) : TransM (List StmtExprMd) := do
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

partial def translateStmtList (stmts : List (Python.stmt SourceRange)) : TransM (List StmtExprMd) := do
  let mut result : List StmtExprMd := []
  for stmt in stmts do result := result ++ (← translateStmt stmt)
  return result

-- ═══════════════════════════════════════════════════════════════════════════════
-- Function / Class / Module
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
  params.mapM fun (pName, pType) => do
    mkExpr sr (.LocalVariable pName (mkTypeDefault pType) (some (← mkExpr sr (.Identifier s!"$in_{pName}"))))

partial def translateFunction (s : Python.stmt SourceRange)
    (isMethod : Bool := false) (className : Option String := none) : TransM (Option Procedure) := do
  match s with
  | .FunctionDef sr name args body _ _returns _ _ => do
    let procName := match className with | some cn => s!"{cn}@{name.val}" | none => name.val
    let (allParams, selfAlreadyStripped) ← match (← lookupName procName) with
      | some (.function sig) =>
        pure (sig.params.map fun (pName, pType) =>
          ({ name := Identifier.mk pName none, type := mkTypeDefault pType } : Parameter), isMethod)
      | _ => match args with
        | .mk_arguments _ _ argList _ _ _ _ _ => do
          let ps ← argList.val.toList.mapM fun arg => match arg with
            | .mk_arg _ argName annotation _ =>
              let ty := match annotation.val with | some e => pythonTypeToLaurel (extractTypeStr e) | none => .TCore "Any"
              pure ({ name := Identifier.mk argName.val none, type := mkTypeDefault ty } : Parameter)
          pure (ps, false)
    let (inputs, paramCopies) ← if isMethod then do
      let selfType := match className with
        | some cn => HighType.UserDefined (Identifier.mk cn none) | none => .TCore "Any"
      let selfParam : Parameter := { name := Identifier.mk "self" none, type := mkTypeDefault selfType }
      let otherParams := if selfAlreadyStripped then allParams
        else if allParams.length > 0 then allParams.tail! else []
      let renamedParams := otherParams.map fun p => { p with name := Identifier.mk s!"$in_{p.name.text}" none }
      let copies ← emitMutableParamCopies sr (otherParams.map fun p => (p.name.text, p.type.val))
      pure (selfParam :: renamedParams, copies)
    else pure (allParams, [])
    let returnType ← match (← lookupName procName) with
      | some (.function sig) => pure sig.returnType | _ => pure (.TCore "Any")
    let outputs := [({ name := Identifier.mk "LaurelResult" none, type := mkTypeDefault returnType } : Parameter),
                     ({ name := Identifier.mk "maybe_except" none, type := mkTypeDefault (.TCore "Error") } : Parameter)]
    let inputNames := inputs.map (·.name.text)
    let originalParamNames := allParams.map (·.name.text)
    let scopeDecls ← emitScopeDeclarations sr body.val (inputNames ++ originalParamNames)
    let bodyStmts ← translateStmtList body.val.toList
    let bodyBlock ← mkExpr sr (.Block (paramCopies ++ scopeDecls ++ bodyStmts) none)
    let md := sourceRangeToMd (← get).filePath sr
    pure (some { name := Identifier.mk procName none, inputs := inputs, outputs := outputs, preconditions := [], determinism := .deterministic none, decreases := none, isFunctional := false, body := .Transparent bodyBlock, md := md })
  | _ => pure none

partial def translateClass (s : Python.stmt SourceRange) : TransM (Option (TypeDefinition × List Procedure)) := do
  match s with
  | .ClassDef _ className _ _ ⟨_, body⟩ _ _ => do
    let classNameStr := className.val
    let envFields ← lookupClassFields classNameStr
    let fields := envFields.map fun (fName, fType) =>
      ({ name := Identifier.mk fName none, type := mkTypeDefault fType, isMutable := true } : Field)
    let mut methods : List Procedure := []
    for stmt in body do
      if let .FunctionDef .. := stmt then
        if let some proc ← translateFunction stmt (isMethod := true) (className := some classNameStr) then
          methods := methods ++ [proc]
    let ct : CompositeType := { name := Identifier.mk classNameStr none, extending := [], fields := fields, instanceProcedures := [] }
    pure (some (.Composite ct, methods))
  | _ => pure none

partial def collectNestedDefs (stmts : List (Python.stmt SourceRange)) : List (Python.stmt SourceRange) :=
  stmts.flatMap fun stmt => match stmt with
    | .FunctionDef .. => [stmt]
    | .ClassDef .. => [stmt]
    | .If _ _ body orelse => collectNestedDefs body.val.toList ++ collectNestedDefs orelse.val.toList
    | _ => []

partial def translateModule (stmts : Array (Python.stmt SourceRange)) : TransM Laurel.Program := do
  let mut procedures : List Procedure := []
  let mut types : List TypeDefinition := []
  let mut otherStmts : List (Python.stmt SourceRange) := []
  for stmt in stmts do
    match stmt with
    | .FunctionDef .. => if let some proc ← translateFunction stmt then procedures := procedures ++ [proc]
    | .ClassDef .. => if let some (td, ms) ← translateClass stmt then types := types ++ [td]; procedures := procedures ++ ms
    | _ => otherStmts := otherStmts ++ [stmt]
  for nested in collectNestedDefs otherStmts do
    match nested with
    | .FunctionDef .. => if let some proc ← translateFunction nested then procedures := procedures ++ [proc]
    | .ClassDef .. => if let some (td, ms) ← translateClass nested then types := types ++ [td]; procedures := procedures ++ ms
    | _ => pure ()
  if !otherStmts.isEmpty then
    let sr : SourceRange := default
    let nameDecl ← mkExpr sr (.LocalVariable "__name__" (mkTypeDefault .TString) (some (mkExprDefault (.LiteralString "__main__"))))
    let scopeDecls ← emitScopeDeclarations sr otherStmts.toArray []
    let bodyStmts ← translateStmtList otherStmts
    let bodyBlock ← mkExpr sr (.Block ([nameDecl] ++ scopeDecls ++ bodyStmts) none)
    let mainOutputs := [({ name := Identifier.mk "LaurelResult" none, type := mkTypeDefault (.TCore "Any") } : Parameter),
                         ({ name := Identifier.mk "maybe_except" none, type := mkTypeDefault (.TCore "Error") } : Parameter)]
    let mainMd := sourceRangeToMd (← get).filePath sr
    let mainProc : Procedure := { name := Identifier.mk "__main__" none, inputs := [], outputs := mainOutputs, preconditions := [], determinism := .deterministic none, decreases := none, isFunctional := false, body := .Transparent bodyBlock, md := mainMd }
    procedures := procedures ++ [mainProc]
  return { staticProcedures := procedures, staticFields := [], types, constants := [] }

end -- mutual

-- Runner

def runTranslation (stmts : Array (Python.stmt SourceRange))
    (env : Resolution.TypeEnv := {}) (filePath : String := "")
    : Except TransError (Laurel.Program × TransState) :=
  (translateModule stmts).run env |>.run { filePath }

def runTranslationWithBase (stmts : Array (Python.stmt SourceRange))
    (baseEnv : Strata.Python.Resolution.TypeEnv := {}) (filePath : String := "")
    : Except TransError (Laurel.Program × TransState) :=
  runTranslation stmts baseEnv filePath

end
end Strata.Python.Translation
