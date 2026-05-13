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

Structural recursion over the resolved Python AST. Pattern matches on
NodeInfo and emits Laurel constructs. Never constructs Laurel.Identifier
from strings — only forwards what Resolution provided.

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
-- Monad (State for fresh counter + loop labels)
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
-- PythonType → HighType
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
-- Runtime Constants (extracted from runtime program interface)
-- ═══════════════════════════════════════════════════════════════════════════════

private def rt (name : String) : Laurel.Identifier := { text := name, uniqueId := none }

private def rtListAnyCons := rt "ListAny_cons"
private def rtListAnyNil := rt "ListAny_nil"
private def rtFromListAny := rt "from_ListAny"
private def rtDictStrAnyCons := rt "DictStrAny_cons"
private def rtDictStrAnyEmpty := rt "DictStrAny_empty"
private def rtFromDictStrAny := rt "from_DictStrAny"
private def rtFromNone := rt "from_None"
private def rtAnyGet := rt "Any_get"
private def rtAnySets := rt "Any_sets"
private def rtFromSlice := rt "from_Slice"
private def rtAnyAsInt := rt "Any..as_int!"
private def rtOptSome := rt "OptSome"
private def rtOptNone := rt "OptNone"
private def rtPIn := rt "PIn"
private def rtIsError := rt "isError"
private def rtToStringAny := rt "to_string_any"
private def rtLaurelResult := rt "LaurelResult"
private def rtMaybeExcept := rt "maybe_except"

-- ═══════════════════════════════════════════════════════════════════════════════
-- Arg Matching (uses FuncSig from annotation)
-- ═══════════════════════════════════════════════════════════════════════════════

def matchArgs (sig : FuncSig) (posArgs : List StmtExprMd)
    (kwargs : List (String × StmtExprMd)) : List StmtExprMd :=
  let paramNames := sig.params.map (·.1.text)
  let numPos := posArgs.length
  let remainingParams := paramNames.drop numPos
  let kwargMatched := remainingParams.filterMap fun pName =>
    kwargs.find? (fun (k, _) => k == pName) |>.map (·.2)
  posArgs ++ kwargMatched

-- ═══════════════════════════════════════════════════════════════════════════════
-- The Structural Recursion
-- ═══════════════════════════════════════════════════════════════════════════════

mutual

partial def translateExpr (e : Python.expr ResolvedAnn) : TransM StmtExprMd := do
  let sr := e.ann.sr
  match e with
  | .Constant _ (.ConPos _ n) _ => mkExpr sr (.LiteralInt n.val)
  | .Constant _ (.ConNeg _ n) _ => mkExpr sr (.LiteralInt (-n.val))
  | .Constant _ (.ConString _ s) _ => mkExpr sr (.LiteralString s.val)
  | .Constant _ (.ConTrue _) _ => mkExpr sr (.LiteralBool true)
  | .Constant _ (.ConFalse _) _ => mkExpr sr (.LiteralBool false)
  | .Constant _ (.ConNone _) _ => mkExpr sr (.StaticCall rtFromNone [])
  | .Constant _ (.ConFloat _ f) _ => mkExpr sr (.LiteralString f.val)
  | .Constant _ _ _ => mkExpr sr .Hole
  | .Name ann _ _ => match ann.info with
    | .variable id => mkExpr sr (.Identifier id)
    | .unresolved => mkExpr sr (.Hole (deterministic := false))
    | .irrelevant => panic! "unreachable: irrelevant node in expression position"
    | .funcDecl _ => panic! "unreachable: funcDecl on Name node"
    | .classDecl _ _ _ => panic! "unreachable: classDecl on Name node"
    | .call _ _ => panic! "unreachable: call on Name node"
    | .classNew _ _ _ => panic! "unreachable: classNew on Name node"
    | .operator _ => panic! "unreachable: operator on Name node"
  | .Call ann _ args kwargs => match ann.info with
    | .call callee sig => do
        let posArgs ← args.val.toList.mapM translateExpr
        let kwargPairs ← kwargs.val.toList.filterMapM fun kw => match kw with
          | .mk_keyword _ kwName kwExpr => do
            let val ← translateExpr kwExpr
            match kwName.val with | some n => pure (some (n.val, val)) | none => pure none
        mkExpr sr (.StaticCall callee (matchArgs sig posArgs kwargPairs))
    | .classNew cls _init _sig => mkExpr sr (.New cls)
    | .unresolved => mkExpr sr (.Hole (deterministic := false))
    | _ => mkExpr sr (.Hole (deterministic := false))
  | .BinOp ann left _ right => match ann.info with
    | .operator callee => do
        let l ← translateExpr left; let r ← translateExpr right
        mkExpr sr (.StaticCall callee [l, r])
    | _ => mkExpr sr .Hole
  | .BoolOp ann _ operands => match ann.info with
    | .operator callee => do
        let exprs ← operands.val.toList.mapM translateExpr
        let mut result := exprs[0]!
        for i in [1:exprs.length] do result ← mkExpr sr (.StaticCall callee [result, exprs[i]!])
        pure result
    | _ => mkExpr sr .Hole
  | .UnaryOp ann _ operand => match ann.info with
    | .operator callee => do
        mkExpr sr (.StaticCall callee [← translateExpr operand])
    | _ => mkExpr sr .Hole
  | .Compare ann left _ comparators => match ann.info with
    | .operator callee => do
        if comparators.val.size != 1 then throw (.unsupportedConstruct "Chained comparisons")
        let l ← translateExpr left; let r ← translateExpr comparators.val[0]!
        mkExpr sr (.StaticCall callee [l, r])
    | _ => mkExpr sr .Hole
  | .Attribute _ obj attr _ => do
      mkExpr sr (.FieldSelect (← translateExpr obj) attr.val)
  | .Subscript _ container slice _ => do
      let c ← translateExpr container
      let idx ← match slice with
        | .Slice _ start stop _ => do
          let s ← match start.val with
            | some e => mkExpr sr (.StaticCall rtAnyAsInt [← translateExpr e])
            | none => mkExpr sr (.LiteralInt 0)
          let e ← match stop.val with
            | some e => mkExpr sr (.StaticCall rtOptSome [← mkExpr sr (.StaticCall rtAnyAsInt [← translateExpr e])])
            | none => mkExpr sr (.StaticCall rtOptNone [])
          mkExpr sr (.StaticCall rtFromSlice [s, e])
        | _ => translateExpr slice
      mkExpr sr (.StaticCall rtAnyGet [c, idx])
  | .List _ elts _ => do
      let es ← elts.val.toList.mapM translateExpr
      let nil ← mkExpr sr (.StaticCall rtListAnyNil [])
      let cons ← es.foldrM (fun e acc => mkExpr sr (.StaticCall rtListAnyCons [e, acc])) nil
      mkExpr sr (.StaticCall rtFromListAny [cons])
  | .Tuple _ elts _ => do
      let es ← elts.val.toList.mapM translateExpr
      let nil ← mkExpr sr (.StaticCall rtListAnyNil [])
      let cons ← es.foldrM (fun e acc => mkExpr sr (.StaticCall rtListAnyCons [e, acc])) nil
      mkExpr sr (.StaticCall rtFromListAny [cons])
  | .Dict _ keys vals => do
      let ks ← keys.val.toList.mapM (fun k => match k with
        | .some_expr _ e => translateExpr e | .missing_expr _ => mkExpr sr .Hole)
      let vs ← vals.val.toList.mapM translateExpr
      let empty ← mkExpr sr (.StaticCall rtDictStrAnyEmpty [])
      let cons ← (List.zip ks vs).foldrM (fun (k, v) acc =>
        mkExpr sr (.StaticCall rtDictStrAnyCons [k, v, acc])) empty
      mkExpr sr (.StaticCall rtFromDictStrAny [cons])
  | .IfExp _ test body orelse => do
      mkExpr sr (.IfThenElse (← translateExpr test) (← translateExpr body) (some (← translateExpr orelse)))
  | .JoinedStr _ values => do
      if values.val.isEmpty then mkExpr sr (.LiteralString "")
      else do
        let parts ← values.val.toList.mapM translateExpr
        let mut result ← mkExpr sr (.LiteralString "")
        for p in parts do result ← mkExpr sr (.StaticCall (rt "PAdd") [result, p])
        pure result
  | .FormattedValue _ value _ _ => do
      mkExpr sr (.StaticCall rtToStringAny [← translateExpr value])
  | _ => mkExpr sr .Hole

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
-- Statement Translation
-- ═══════════════════════════════════════════════════════════════════════════════

partial def translateStmtList (stmts : List (Python.stmt ResolvedAnn)) : TransM (List StmtExprMd) := do
  let mut result : List StmtExprMd := []
  for stmt in stmts do result := result ++ (← translateStmt stmt)
  return result

partial def translateAssign (sr : SourceRange) (target : Python.expr ResolvedAnn)
    (value : Python.expr ResolvedAnn) : TransM (List StmtExprMd) := do
  match value with
  | .Call ann _ args _ => match ann.info with
    | .classNew cls init sig => do
        let targetExpr ← translateExpr target
        let assignNew ← mkExpr sr (.Assign [targetExpr] (← mkExpr sr (.New cls)))
        let posArgs ← args.val.toList.mapM translateExpr
        let initCall ← mkExpr sr (.StaticCall init (targetExpr :: posArgs))
        pure [assignNew, initCall]
    | _ => pure [← mkExpr sr (.Assign [← translateExpr target] (← translateExpr value))]
  | _ => pure [← mkExpr sr (.Assign [← translateExpr target] (← translateExpr value))]

partial def translateStmt (s : Python.stmt ResolvedAnn) : TransM (List StmtExprMd) := do
  let sr := s.ann.sr
  match s with
  | .Assign _ targets value _ => do
      if targets.val.size != 1 then throw (.unsupportedConstruct "Multiple assignment targets")
      let target := targets.val[0]!
      match target with
      | .Tuple _ elts _ => do
          let rhsExpr ← translateExpr value
          let tmp ← freshId "unpack"
          let tmpDecl ← mkExpr sr (.LocalVariable tmp.text (mkTypeDefault (.TCore "Any")) (some rhsExpr))
          let tmpRef ← mkExpr sr (.Identifier tmp)
          pure ([tmpDecl] ++ (← unpackTargets sr elts.val.toList tmpRef))
      | .Subscript .. => do
          let (root, indices) ← collectSubscriptChain target
          let rootExpr ← translateExpr root
          let mut idxList ← mkExpr sr (.StaticCall rtListAnyNil [])
          for idx in indices.reverse do
            let idxExpr ← match idx with
              | .Slice _ start stop _ => do
                let s' ← match start.val with
                  | some e => mkExpr sr (.StaticCall rtAnyAsInt [← translateExpr e])
                  | none => mkExpr sr (.LiteralInt 0)
                let e' ← match stop.val with
                  | some e => mkExpr sr (.StaticCall rtOptSome [← mkExpr sr (.StaticCall rtAnyAsInt [← translateExpr e])])
                  | none => mkExpr sr (.StaticCall rtOptNone [])
                mkExpr sr (.StaticCall rtFromSlice [s', e'])
              | _ => translateExpr idx
            idxList ← mkExpr sr (.StaticCall rtListAnyCons [idxExpr, idxList])
          let rhs ← translateExpr value
          let setsCall ← mkExpr sr (.StaticCall rtAnySets [idxList, rootExpr, rhs])
          pure [← mkExpr sr (.Assign [rootExpr] setsCall)]
      | _ => translateAssign sr target value

  | .AnnAssign _ target _ value _ => do
      match value.val with
      | some val => translateAssign sr target val
      | none => pure []

  | .AugAssign ann target _ value => match ann.info with
    | .operator callee => do
        let t ← translateExpr target; let v ← translateExpr value
        pure [← mkExpr sr (.Assign [t] (← mkExpr sr (.StaticCall callee [t, v])))]
    | _ => pure [← mkExpr sr .Hole]

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
          let tmpRef ← mkExpr sr (.Identifier tmp)
          let havoc ← mkExpr sr (.Assign [tmpRef] (← mkExpr sr (.Hole (deterministic := false))))
          let unpacks ← unpackTargets sr elts.val.toList tmpRef
          pure ([havoc] ++ unpacks, tmpRef)
        | _ => do
          let tgt ← translateExpr target
          let havoc ← mkExpr sr (.Assign [tgt] (← mkExpr sr (.Hole (deterministic := false))))
          pure ([havoc], tgt)
      let assume ← mkExpr sr (.Assume (← mkExpr sr (.StaticCall rtPIn [assumeTarget, iterExpr])))
      let inner ← mkExpr sr (.Block (havocStmts ++ [assume] ++ bodyStmts) (some ct.text))
      let outer ← mkExpr sr (.Block [inner] (some bk.text))
      popLoopLabel; pure [outer]

  | .Return _ value => do
      match value.val with
      | some expr => do
        let e ← translateExpr expr
        pure [← mkExpr sr (.Assign [← mkExpr sr (.Identifier rtLaurelResult)] e), ← mkExpr sr (.Exit "$body")]
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
        | .mk_withitem _ _ctxExpr optVars => do
          let enter ← mkExpr sr (.Hole (deterministic := false))
          let exit ← mkExpr sr (.Hole (deterministic := false))
          match optVars.val with
          | some varExpr => pre := pre ++ [← mkExpr sr (.Assign [← translateExpr varExpr] enter)]
          | none => pre := pre ++ [enter]
          post := post ++ [exit]
      pure (pre ++ (← translateStmtList body.val.toList) ++ post)

  | .Raise _ exc _ => do
      match exc.val with
      | some excExpr => do
        let errorExpr ← translateExpr excExpr
        pure [← mkExpr sr (.Assign [← mkExpr sr (.Identifier rtMaybeExcept)] errorExpr)]
      | none => pure [← mkExpr sr (.Assign [← mkExpr sr (.Identifier rtMaybeExcept)] (← mkExpr sr .Hole))]

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
    | .Pass a => { sr := a.sr, info := .irrelevant } | .Break a => { sr := a.sr, info := .irrelevant }
    | .Continue a => { sr := a.sr, info := .irrelevant } | .Match a .. => a | .TypeAlias a .. => a

partial def unpackTargets (sr : SourceRange) (elts : List (Python.expr ResolvedAnn))
    (sourceRef : StmtExprMd) : TransM (List StmtExprMd) := do
  let mut stmts : List StmtExprMd := []
  let mut idx : Int := 0
  for elt in elts do
    let getExpr ← mkExpr sr (.StaticCall rtAnyGet [sourceRef, ← mkExpr sr (.LiteralInt idx)])
    match elt with
    | .Tuple _ innerElts _ => do
      let innerTmp ← freshId "unpack"
      let innerRef ← mkExpr sr (.Identifier innerTmp)
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

partial def translateTryExcept (sr : SourceRange)
    (body : Ann (Array (Python.stmt ResolvedAnn)) ResolvedAnn)
    (handlers : Ann (Array (Python.excepthandler ResolvedAnn)) ResolvedAnn) : TransM (List StmtExprMd) := do
  let tryLabel := s!"try_end_{sr.start.byteIdx}"
  let catchersLabel := s!"exception_handlers_{sr.start.byteIdx}"
  let bodyStmts ← translateStmtList body.val.toList
  let mut withChecks : List StmtExprMd := []
  for stmt in bodyStmts do
    withChecks := withChecks ++ [stmt]
    let ref ← mkExpr sr (.Identifier rtMaybeExcept)
    let check ← mkExpr sr (.StaticCall rtIsError [ref])
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
-- Function / Class / Module — reads NodeInfo directly
-- ═══════════════════════════════════════════════════════════════════════════════

partial def translateFunction (sig : FuncSig) (body : Array (Python.stmt ResolvedAnn))
    (sr : SourceRange) : TransM Procedure := do
  let inputs : List Laurel.Parameter := sig.params.map fun (pId, pTy) =>
    { name := pId, type := mkTypeDefault (pythonTypeToHighType pTy) }
  let outputs : List Laurel.Parameter :=
    [{ name := rtLaurelResult, type := mkTypeDefault (pythonTypeToHighType sig.returnType) },
     { name := rtMaybeExcept, type := mkTypeDefault (.TCore "Error") }]
  let localDecls := sig.locals.map fun (lId, lTy) =>
    mkExprDefault (.LocalVariable lId (mkTypeDefault (pythonTypeToHighType lTy)) none)
  let bodyStmts ← translateStmtList body.toList
  let bodyBlock ← mkExpr sr (.Block (localDecls ++ bodyStmts) none)
  let md := sourceRangeToMd (← get).filePath sr
  pure {
    name := sig.name
    inputs := inputs
    outputs := outputs
    preconditions := []
    determinism := .deterministic none
    decreases := none
    isFunctional := false
    body := .Transparent bodyBlock
    md := md
  }

partial def translateClass (name : Laurel.Identifier) (fields : List (Laurel.Identifier × PythonType))
    (methods : List FuncSig) (body : Array (Python.stmt ResolvedAnn))
    (sr : SourceRange) : TransM (TypeDefinition × List Procedure) := do
  let laurelFields := fields.map fun (fId, fTy) =>
    ({ name := fId, isMutable := true, type := mkTypeDefault (pythonTypeToHighType fTy) } : Field)
  let mut procs : List Procedure := []
  for stmt in body do
    match stmt with
    | .FunctionDef ann _ _ fbody _ _ _ _ => match ann.info with
      | .funcDecl sig =>
        let proc ← translateFunction sig fbody.val ann.sr
        procs := procs ++ [proc]
      | _ => pure ()
    | .AsyncFunctionDef ann _ _ fbody _ _ _ _ => match ann.info with
      | .funcDecl sig =>
        let proc ← translateFunction sig fbody.val ann.sr
        procs := procs ++ [proc]
      | _ => pure ()
    | _ => pure ()
  let ct : CompositeType := { name := name, extending := [], fields := laurelFields, instanceProcedures := [] }
  pure (.Composite ct, procs)

partial def translateModule (program : ResolvedPythonProgram) : TransM Laurel.Program := do
  let mut procedures : List Procedure := []
  let mut types : List TypeDefinition := []
  let mut otherStmts : List (Python.stmt ResolvedAnn) := []
  for stmt in program.stmts do
    match stmt with
    | .FunctionDef ann _ _ body _ _ _ _ => match ann.info with
      | .funcDecl sig =>
        let proc ← translateFunction sig body.val ann.sr
        procedures := procedures ++ [proc]
      | _ => pure ()
    | .AsyncFunctionDef ann _ _ body _ _ _ _ => match ann.info with
      | .funcDecl sig =>
        let proc ← translateFunction sig body.val ann.sr
        procedures := procedures ++ [proc]
      | _ => pure ()
    | .ClassDef ann _ _ _ body _ _ => match ann.info with
      | .classDecl name fields methods =>
        let (td, ms) ← translateClass name fields methods body.val ann.sr
        types := types ++ [td]
        procedures := procedures ++ ms
      | _ => pure ()
    | _ => otherStmts := otherStmts ++ [stmt]
  if !otherStmts.isEmpty then
    let sr : SourceRange := default
    let nameId := rt "__name__"
    let nameDecl ← mkExpr sr (.LocalVariable nameId (mkTypeDefault .TString) (some (mkExprDefault (.LiteralString "__main__"))))
    let localDecls := program.moduleLocals.map fun (lId, lTy) =>
      mkExprDefault (.LocalVariable lId (mkTypeDefault (pythonTypeToHighType lTy)) none)
    let bodyStmts ← translateStmtList otherStmts
    let bodyBlock ← mkExpr sr (.Block ([nameDecl] ++ localDecls ++ bodyStmts) none)
    let mainOutputs : List Laurel.Parameter :=
      [{ name := rtLaurelResult, type := mkTypeDefault (.TCore "Any") },
       { name := rtMaybeExcept, type := mkTypeDefault (.TCore "Error") }]
    let mainMd := sourceRangeToMd (← get).filePath sr
    let mainProc : Procedure := { name := rt "__main__", inputs := [], outputs := mainOutputs, preconditions := [], determinism := .deterministic none, decreases := none, isFunctional := false, body := .Transparent bodyBlock, md := mainMd }
    procedures := procedures ++ [mainProc]
  return { staticProcedures := procedures, staticFields := [], types, constants := [] }

end -- mutual

-- ═══════════════════════════════════════════════════════════════════════════════
-- Runner
-- ═══════════════════════════════════════════════════════════════════════════════

def runTranslation (program : ResolvedPythonProgram)
    (filePath : String := "")
    : Except TransError (Laurel.Program × TransState) :=
  (translateModule program).run { filePath := filePath }

end -- public section
end Strata.Python.Translation
