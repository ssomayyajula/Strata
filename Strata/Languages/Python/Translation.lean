/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.Laurel
public import Strata.Languages.Python.PythonDialect
public import Strata.Languages.Python.NameResolution
import Strata.DDM.Util.SourceRange

/-!
# Pass 2: Translation (Python -> Laurel)

A catamorphism (fold) over the Python AST that produces precisely-typed Laurel.
Each Python AST constructor maps to exactly one Laurel construction.

## Design (from ARCHITECTURE.md)

Translation handles ALL Python-specific desugarings because Resolution (Γ) provides
the information needed:

- Scope hoisting: Γ tells translation which variables are function-scoped → emit
  LocalVariable declarations at function top
- Object construction: Γ says name is a class → emit New + __init__ call
- Context managers: fixed protocol (enter/exit)
- For-loop abstraction: havoc + assume (verification modeling)
- Tuple unpacking: tmp + indexed access
- Mutable parameter copy: var x := $in_x for method params
- Calling convention: Γ has param order + defaults → normalize kwargs

## What Translation Does NOT Do

- No cast insertion (no from_int, no Any_to_bool) — that is elaboration's job
- No literal wrapping — emit the literal directly
- No polarity/ANF — elaboration handles Value/Producer separation
- No type coercions — elaboration inserts these at type boundaries

## Engineering Principles

- Catamorphism: one case per constructor, recursive on sub-terms
- Interaction law: use mkExpr for all construction (never raw { val, md })
- Types flow down: read annotations, don't infer from children
- No post-hoc rewrites: emit correct IR the first time
- Monad carries context: TypeEnv in ReaderT, not a manual parameter
- No boolean blindness: pattern-match on NameInfo, never check isClass
-/

namespace Strata.Python.Translation

open Laurel
open Strata.Python.Resolution

public section

/-! ## Translation Error -/

/-- Errors during translation. These indicate genuinely malformed AST (should not
    happen on well-formed Python) or user code errors detected during translation. -/
inductive TransError where
  | unsupportedConstruct (msg : String)
  | internalError (msg : String)
  /-- User code error: the Python code has a detectable problem (e.g., calling a
      method that doesn't exist on a class). These are reported to the user as
      diagnostics, not internal failures. -/
  | userError (range : SourceRange) (msg : String)
  deriving Repr

instance : ToString TransError where
  toString
    | .unsupportedConstruct msg => s!"Translation: unsupported construct: {msg}"
    | .internalError msg => s!"Translation: internal error: {msg}"
    | .userError _range msg => s!"User code error: {msg}"

/-! ## Translation State -/

/-- Mutable state threaded through translation. -/
structure TransState where
  /-- Counter for generating fresh variable names. -/
  freshCounter : Nat := 0
  /-- Source file path for metadata (set once at translation start). -/
  filePath : String := ""
  /-- Stack of enclosing loop labels: (breakLabel, continueLabel).
      Entering For/While pushes a fresh pair; Break/Continue emit Exit with the top label.
      This is translation-internal (not a resolution problem). -/
  loopLabels : List (String × String) := []
  /-- Variable type annotations encountered during translation.
      Used for method qualification (e.g., With statement needs to know the
      context manager's class type to emit Type@__enter__/Type@__exit__).
      Maps variable name → Python class name from annotation. -/
  variableTypes : Std.HashMap String String := {}
  deriving Inhabited

/-! ## Translation Monad

From ARCHITECTURE.md:
  abbrev TransM := ReaderT Resolution.TypeEnv (StateT TransState (Except TransError))

Resolution.TypeEnv in the reader (immutable after resolution). Fresh variable counter
and filePath in the state. Errors for genuinely impossible cases.
-/

abbrev TransM := ReaderT Resolution.TypeEnv (StateT TransState (Except TransError))

/-! ## Smart Constructors (Interaction Law)

From ARCHITECTURE.md: Smart constructors (mkExpr sr expr) are the ONLY way
to build nodes -- they attach metadata from the Python AST's SourceRange.
Never construct { val := ..., md := ... } directly.
-/

/-- Convert SourceRange to Laurel metadata. -/
private def sourceRangeToMd (filePath : String) (sr : SourceRange) : Imperative.MetaData Core.Expression :=
  let uri : Uri := .file filePath
  #[⟨ Imperative.MetaData.fileRange, .fileRange ⟨ uri, sr ⟩ ⟩]

/-- Smart constructor: attach metadata from Python SourceRange.
    This is the ONLY way to construct Laurel nodes in this pass.
    Reads filePath from TransState for correct source location metadata. -/
def mkExpr (sr : SourceRange) (expr : StmtExpr) : TransM StmtExprMd := do
  let filePath := (← get).filePath
  pure { val := expr, md := sourceRangeToMd filePath sr }

/-- Smart constructor for HighTypeMd. Reads filePath from TransState. -/
def mkTypeMd (sr : SourceRange) (ty : HighType) : TransM HighTypeMd := do
  let filePath := (← get).filePath
  pure { val := ty, md := sourceRangeToMd filePath sr }

/-- Default metadata for nodes where no source location is available. -/
private def defaultMd : Imperative.MetaData Core.Expression := #[]

/-- Smart constructor with default metadata (for synthesized nodes). -/
def mkExprDefault (expr : StmtExpr) : StmtExprMd :=
  { val := expr, md := defaultMd }

/-- Smart constructor for types with default metadata. -/
def mkTypeDefault (ty : HighType) : HighTypeMd :=
  { val := ty, md := defaultMd }

/-! ## Type Annotation Translation

Types flow down from annotations. This function converts Python type annotation
strings to Laurel HighType. Only uses Any when annotation is literally absent.
-/

/-- Convert a Python type annotation string to Laurel HighType.
    Type-directed: reads the annotation, uses it directly. -/
def pythonTypeToLaurel (typeStr : String) : HighType :=
  match typeStr with
  | "int" => .TInt
  | "bool" => .TBool
  | "str" => .TString
  | "float" => .TFloat64
  | "None" => .TVoid
  | "Any" => .TCore "Any"
  | other => .UserDefined (Identifier.mk other none)

/-- Extract a type string from a Python expression used as a type annotation. -/
partial def extractTypeStr (e : Python.expr SourceRange) : String :=
  match e with
  | .Name _ n _ => n.val
  | .Constant _ (.ConString _ s) _ => s.val
  | .Subscript _ val slice _ =>
      let base := extractTypeStr val
      let arg := extractTypeStr slice
      s!"{base}[{arg}]"
  | .Attribute _ val attr _ =>
      let base := extractTypeStr val
      s!"{base}.{attr.val}"
  | .Tuple _ elts _ =>
      let args := elts.val.toList.map extractTypeStr
      String.intercalate ", " args
  | .BinOp _ left _ right =>
      -- Union type: X | Y
      let l := extractTypeStr left
      let r := extractTypeStr right
      s!"{l} | {r}"
  | _ => "Any"

/-! ## Monad Helpers -/

/-- Generate a fresh variable name with a given prefix. -/
def freshVar (pfx : String := "tmp") : TransM String := do
  let s ← get
  set { s with freshCounter := s.freshCounter + 1 }
  return s!"{pfx}_{s.freshCounter}"

/-- Push a fresh loop label pair onto the stack. Returns (breakLabel, continueLabel).
    Called when entering a For or While loop. -/
def pushLoopLabel (pfx : String) : TransM (String × String) := do
  let s ← get
  let breakLabel := s!"{pfx}_break_{s.freshCounter}"
  let continueLabel := s!"{pfx}_continue_{s.freshCounter}"
  set { s with freshCounter := s.freshCounter + 1,
               loopLabels := (breakLabel, continueLabel) :: s.loopLabels }
  return (breakLabel, continueLabel)

/-- Pop the top loop label from the stack. Called when exiting a For or While loop. -/
def popLoopLabel : TransM Unit :=
  modify fun s => { s with loopLabels := s.loopLabels.tail! }

/-- Get the current break label (top of stack). -/
def currentBreakLabel : TransM (Option String) := do
  return (← get).loopLabels.head?.map (·.1)

/-- Get the current continue label (top of stack). -/
def currentContinueLabel : TransM (Option String) := do
  return (← get).loopLabels.head?.map (·.2)

/-- Look up a name in Γ (the TypeEnv from Resolution). -/
def lookupName (name : String) : TransM (Option NameInfo) := do
  let env ← read
  return env.names[name]?

/-- Record a variable's Python class type (from annotation or constructor call).
    Used for method qualification in With statements and method calls. -/
def recordVariableType (varName : String) (className : String) : TransM Unit :=
  modify fun s => { s with variableTypes := s.variableTypes.insert varName className }

/-- Look up a variable's recorded Python class type. -/
def lookupVariableType (varName : String) : TransM (Option String) := do
  return (← get).variableTypes[varName]?

/-- Look up class fields from Γ. -/
def lookupClassFields (className : String) : TransM (List (String × HighType)) := do
  let env ← read
  return (env.classFields[className]?).getD []

/-- Look up builtin mapping. -/
def lookupBuiltin (name : String) : TransM (Option String) := do
  let env ← read
  return env.builtinMap[name]?

/-! ## Keyword Argument Resolution -/

/-- Resolve keyword arguments against a function signature from Γ.
    Places kwargs in correct positions based on param names from FuncSig.
    For parameters not provided by positional or keyword args, fills in
    `from_None` as the default (matching the prelude convention where
    optional params accept None). -/
def resolveKwargs (funcName : String) (posArgs : List StmtExprMd)
    (kwargs : List (String × StmtExprMd)) : TransM (List StmtExprMd) := do
  let env ← read
  match env.names[funcName]? with
  | some (.function sig) =>
      let numPos := posArgs.length
      let totalParams := sig.params.length
      -- If all params already provided positionally and no kwargs, return as-is
      if kwargs.isEmpty && numPos >= totalParams then
        return posArgs
      let remainingParams := sig.params.drop numPos
      let remainingDefaults := sig.defaults.drop numPos
      let mut ordered := posArgs
      let mut idx := 0
      for (paramName, _) in remainingParams do
        match kwargs.find? (fun (name, _) => name == paramName) with
        | some (_, val) => ordered := ordered ++ [val]
        | none =>
            -- Parameter not provided: fill with from_None if it has a default
            let hasDefault := match remainingDefaults[idx]? with
              | some (some _) => true
              | _ => false
            if hasDefault then
              ordered := ordered ++ [mkExprDefault (.StaticCall "from_None" [])]
        idx := idx + 1
      return ordered
  | _ =>
      -- No signature known: just append kwargs in order
      if kwargs.isEmpty then
        return posArgs
      return posArgs ++ kwargs.map (·.2)

/-- Translate a single Python argument to a Laurel Parameter.
    Type-directed: reads the annotation. Only uses Any if annotation is absent. -/
def translateArg (arg : Python.arg SourceRange) : TransM Parameter := do
  match arg with
  | .mk_arg _ argName annotation _ =>
      let ty := match annotation.val with
        | some annExpr => pythonTypeToLaurel (extractTypeStr annExpr)
        | none => .TCore "Any"  -- Only if genuinely unannotated
      pure { name := Identifier.mk argName.val none,
             type := mkTypeDefault ty }

/-! ## The Fold

Translation is ONE function per AST category. All are mutually recursive because
statement translation can encounter nested functions/classes, and expression
translation recurses on sub-expressions.
-/

mutual

-- Expression Translation: one case per Python expr constructor

/-- Translate a Python expression to Laurel. One case per constructor. -/
partial def translateExpr (e : Python.expr SourceRange) : TransM StmtExprMd := do
  match e with
  -- Literals: emit bare (no coercions). Elaboration inserts from_int/from_str/from_bool
  -- at type boundaries where needed (per ARCHITECTURE.md: Translation does NOT wrap).
  | .Constant sr (.ConPos _ n) _ =>
      mkExpr sr (.LiteralInt n.val)
  | .Constant sr (.ConNeg _ n) _ =>
      mkExpr sr (.LiteralInt (-n.val))
  | .Constant sr (.ConString _ s) _ =>
      mkExpr sr (.LiteralString s.val)
  | .Constant sr (.ConTrue _) _ =>
      mkExpr sr (.LiteralBool true)
  | .Constant sr (.ConFalse _) _ =>
      mkExpr sr (.LiteralBool false)
  | .Constant sr (.ConNone _) _ =>
      mkExpr sr (.StaticCall "from_None" [])
  | .Constant sr (.ConFloat _ f) _ =>
      mkExpr sr (.LiteralString f.val)
  | .Constant sr (.ConBytes _ _) _ => mkExpr sr .Hole
  | .Constant sr (.ConComplex _ _ _) _ => mkExpr sr .Hole
  | .Constant sr (.ConEllipsis _) _ => mkExpr sr .Hole

  -- Variable reference: direct identifier
  | .Name sr name _ =>
      mkExpr sr (.Identifier name.val)

  -- Binary operations: translate to prelude StaticCall
  | .BinOp sr left op right => do
      let l ← translateExpr left
      let r ← translateExpr right
      let opName ← match op with
        | .Add _ => pure "PAdd"
        | .Sub _ => pure "PSub"
        | .Mult _ => pure "PMul"
        | .Div _ => pure "PDiv"
        | .FloorDiv _ => pure "PFloorDiv"
        | .Mod _ => pure "PMod"
        | .Pow _ => pure "PPow"
        | .BitAnd _ => pure "PBitAnd"
        | .BitOr _ => pure "PBitOr"
        | .BitXor _ => pure "PBitXor"
        | .LShift _ => pure "PLShift"
        | .RShift _ => pure "PRShift"
        | .MatMult _ => throw (.unsupportedConstruct "Matrix multiplication (@) operator")
      mkExpr sr (.StaticCall opName [l, r])

  -- Comparison operations
  | .Compare sr left ops comparators => do
      if ops.val.size != 1 || comparators.val.size != 1 then
        throw (.unsupportedConstruct "Chained comparisons")
      let l ← translateExpr left
      let r ← translateExpr comparators.val[0]!
      let opName ← match ops.val[0]! with
        | .Eq _ => pure "PEq"
        | .NotEq _ => pure "PNEq"
        | .Lt _ => pure "PLt"
        | .LtE _ => pure "PLe"
        | .Gt _ => pure "PGt"
        | .GtE _ => pure "PGe"
        | .In _ => pure "PIn"
        | .NotIn _ => pure "PNotIn"
        | .Is _ => pure "PIs"
        | .IsNot _ => pure "PIsNot"
      mkExpr sr (.StaticCall opName [l, r])

  -- Boolean operations: chain binary
  | .BoolOp sr op values => do
      if values.val.size < 2 then
        throw (.internalError "BoolOp requires at least 2 operands")
      let opName ← match op with
        | .And _ => pure "PAnd"
        | .Or _ => pure "POr"
      let mut exprs : List StmtExprMd := []
      for val in values.val do
        let expr ← translateExpr val
        exprs := exprs ++ [expr]
      -- Chain: a op b op c -> (a op b) op c
      let mut result := exprs[0]!
      for i in [1:exprs.length] do
        result ← mkExpr sr (.StaticCall opName [result, exprs[i]!])
      pure result

  -- Unary operations
  | .UnaryOp sr op operand => do
      let e ← translateExpr operand
      let opName ← match op with
        | .Not _ => pure "PNot"
        | .USub _ => pure "PNeg"
        | .UAdd _ => pure "PPos"
        | .Invert _ => pure "PInvert"
      mkExpr sr (.StaticCall opName [e])

  -- Call: resolved via Γ (NameInfo). Pattern match determines Laurel node.
  | .Call sr func args kwargs => do
      match func with
      | .Attribute _ receiver methodName _ => do
          -- First check if receiver is a module (e.g., `re.fullmatch(...)` → `re_fullmatch(...)`)
          let isModule ← match receiver with
            | .Name _ rName _ => do
                let info ← lookupName rName.val
                match info with
                | some (.module_ _) => pure true
                | _ => pure false
            | _ => pure false
          if isModule then
            -- Module-qualified call: module.func(args) → StaticCall "module_func" [args]
            -- No receiver passed (modules are not objects)
            let moduleName := match receiver with
              | .Name _ rName _ => rName.val
              | _ => "unknown"
            let funcName := s!"{moduleName}_{methodName.val}"
            let posArgs ← args.val.toList.mapM translateExpr
            let kwargPairs ← kwargs.val.toList.filterMapM (fun kw => do
              match kw with
              | .mk_keyword _ kwName kwExpr => do
                  let val ← translateExpr kwExpr
                  match kwName.val with
                  | some n => pure (some (n.val, val))
                  | none => pure none)
            let allArgs ← resolveKwargs funcName posArgs kwargPairs
            mkExpr sr (.StaticCall funcName allArgs)
          else do
            -- Method call: receiver.method(args)
            let objExpr ← translateExpr receiver
            let posArgs ← args.val.toList.mapM translateExpr
            let kwargPairs ← kwargs.val.toList.filterMapM (fun kw => do
              match kw with
              | .mk_keyword _ kwName kwExpr => do
                  let val ← translateExpr kwExpr
                  match kwName.val with
                  | some n => pure (some (n.val, val))
                  | none => pure none)
            -- Qualify method with receiver type from Γ or variableTypes
            let qualifiedName ← do
              match receiver with
              | .Name _ rName _ =>
                  -- First try TypeEnv (Γ) for the variable's declared type
                  let info ← lookupName rName.val
                  let classNameOpt ← match info with
                    | some (.variable (.UserDefined id)) => pure (some id.text)
                    | _ =>
                        -- Fallback: check variableTypes (tracked from constructor calls)
                        lookupVariableType rName.val
                  match classNameOpt with
                  | some className =>
                      -- Check if the qualified method exists in Γ
                      let qName := s!"{className}@{methodName.val}"
                      let methodInfo ← lookupName qName
                      match methodInfo with
                      | some _ => pure qName
                      | none =>
                          -- Method not found for this class type.
                          -- Check if the class is known (has an __init__ or other methods)
                          -- If so, this is a user error.
                          let initInfo ← lookupName s!"{className}@__init__"
                          let classInfo ← lookupName className
                          if initInfo.isSome || classInfo.isSome then
                            throw (.userError sr s!"Unknown method '{methodName.val}'")
                          else
                            -- Class not well-known, fall through as unqualified
                            pure methodName.val
                  | none => pure methodName.val
              | _ => pure methodName.val
            let allArgs ← resolveKwargs qualifiedName (objExpr :: posArgs) kwargPairs
            mkExpr sr (.StaticCall qualifiedName allArgs)
      | .Name _ calleeName _ => do
          -- Check builtin map first
          let builtin ← lookupBuiltin calleeName.val
          match builtin with
          | some laurelName => do
              let posArgs ← args.val.toList.mapM translateExpr
              let kwargPairs ← kwargs.val.toList.filterMapM (fun kw => do
                match kw with
                | .mk_keyword _ kwName kwExpr => do
                    let val ← translateExpr kwExpr
                    match kwName.val with
                    | some n => pure (some (n.val, val))
                    | none => pure none)
              let allArgs ← resolveKwargs laurelName posArgs kwargPairs
              mkExpr sr (.StaticCall laurelName allArgs)
          | none => do
              -- Look up in Γ
              let info ← lookupName calleeName.val
              match info with
              | some (.class_ className _fields) => do
                  -- Object construction: two-phase protocol (New + __init__)
                  -- 1. Allocate: tmp := New "ClassName"
                  -- 2. Initialize: ClassName@__init__(tmp, args...)
                  -- 3. Block evaluates to tmp
                  -- This matches what the lowering passes expect:
                  -- typeHierarchyTransform expands New into heap allocation,
                  -- heapParameterization threads heap through the call.
                  let posArgs ← args.val.toList.mapM translateExpr
                  let kwargPairs ← kwargs.val.toList.filterMapM (fun kw => do
                    match kw with
                    | .mk_keyword _ kwName kwExpr => do
                        let val ← translateExpr kwExpr
                        match kwName.val with
                        | some n => pure (some (n.val, val))
                        | none => pure none)
                  let tmpName ← freshVar "new"
                  let classId := Identifier.mk className none
                  let newExpr ← mkExpr sr (.New classId)
                  let tmpDecl ← mkExpr sr (.LocalVariable tmpName
                      (mkTypeDefault (.UserDefined classId)) (some newExpr))
                  let tmpRef ← mkExpr sr (.Identifier tmpName)
                  let initName := s!"{className}@__init__"
                  let allInitArgs ← resolveKwargs initName (tmpRef :: posArgs) kwargPairs
                  let initCall ← mkExpr sr (.StaticCall initName allInitArgs)
                  mkExpr sr (.Block [tmpDecl, initCall, tmpRef] none)
              | some (.function sig) => do
                  let posArgs ← args.val.toList.mapM translateExpr
                  let kwargPairs ← kwargs.val.toList.filterMapM (fun kw => do
                    match kw with
                    | .mk_keyword _ kwName kwExpr => do
                        let val ← translateExpr kwExpr
                        match kwName.val with
                        | some n => pure (some (n.val, val))
                        | none => pure none)
                  let allArgs ← resolveKwargs sig.name posArgs kwargPairs
                  mkExpr sr (.StaticCall sig.name allArgs)
              | _ => do
                  -- Unknown name: emit as StaticCall (may be resolved later by pipeline)
                  let posArgs ← args.val.toList.mapM translateExpr
                  let kwargPairs ← kwargs.val.toList.filterMapM (fun kw => do
                    match kw with
                    | .mk_keyword _ kwName kwExpr => do
                        let val ← translateExpr kwExpr
                        match kwName.val with
                        | some n => pure (some (n.val, val))
                        | none => pure none)
                  let allArgs ← resolveKwargs calleeName.val posArgs kwargPairs
                  mkExpr sr (.StaticCall calleeName.val allArgs)
      | _ => do
          -- Indirect call (expression as callee)
          let posArgs ← args.val.toList.mapM translateExpr
          mkExpr sr (.StaticCall "call" posArgs)

  -- Attribute access: obj.field -> FieldSelect
  | .Attribute sr obj attr _ => do
      let objExpr ← translateExpr obj
      mkExpr sr (.FieldSelect objExpr attr.val)

  -- Subscript: container[index] -> StaticCall "Any_get"
  | .Subscript sr container slice _ => do
      let containerExpr ← translateExpr container
      let indexExpr ← match slice with
        | .Slice sr' start stop step => do
            let startE ← match start.val with
              | some e => translateExpr e
              | none => mkExpr sr' (.LiteralInt 0)
            let stopE ← match stop.val with
              | some e => translateExpr e
              | none => mkExpr sr' (.LiteralInt (-1))
            if step.val.isSome then
              throw (.unsupportedConstruct "Slice step")
            mkExpr sr' (.StaticCall "from_Slice" [startE, stopE])
        | _ => translateExpr slice
      mkExpr sr (.StaticCall "Any_get" [containerExpr, indexExpr])

  -- List literal: [a, b, c] -> from_ListAny(ListAny_cons(a, ListAny_cons(b, ListAny_cons(c, ListAny_nil()))))
  | .List sr elts _ => do
      let elements ← elts.val.toList.mapM translateExpr
      -- Build ListAny_cons(a, ListAny_cons(b, ListAny_cons(c, ListAny_nil())))
      let nil ← mkExpr sr (.StaticCall "ListAny_nil" [])
      let consList ← elements.foldrM (fun elem acc => mkExpr sr (.StaticCall "ListAny_cons" [elem, acc])) nil
      mkExpr sr (.StaticCall "from_ListAny" [consList])

  -- Tuple literal: (a, b) -> from_ListAny(ListAny_cons(a, ListAny_cons(b, ListAny_nil())))
  -- Python tuples are modeled as ListAny (same as lists in the verification model)
  | .Tuple sr elts _ => do
      let elements ← elts.val.toList.mapM translateExpr
      let nil ← mkExpr sr (.StaticCall "ListAny_nil" [])
      let consList ← elements.foldrM (fun elem acc => mkExpr sr (.StaticCall "ListAny_cons" [elem, acc])) nil
      mkExpr sr (.StaticCall "from_ListAny" [consList])

  -- Dict literal: {k: v, ...} -> from_DictStrAny(DictStrAny_cons(k1, v1, DictStrAny_cons(k2, v2, DictStrAny_empty())))
  | .Dict sr keys vals => do
      let keyExprs ← keys.val.toList.mapM (fun optKey => match optKey with
        | .some_expr _ e => translateExpr e
        | .missing_expr sr' => mkExpr sr' .Hole)
      let valExprs ← vals.val.toList.mapM translateExpr
      -- Build DictStrAny_cons(k1, v1, DictStrAny_cons(k2, v2, DictStrAny_empty()))
      let empty ← mkExpr sr (.StaticCall "DictStrAny_empty" [])
      let pairs := List.zip keyExprs valExprs
      let consChain ← pairs.foldrM (fun (k, v) acc => mkExpr sr (.StaticCall "DictStrAny_cons" [k, v, acc])) empty
      mkExpr sr (.StaticCall "from_DictStrAny" [consChain])

  -- IfExp: x if cond else y -> IfThenElse (ternary)
  | .IfExp sr test body orelse => do
      let testExpr ← translateExpr test
      let bodyExpr ← translateExpr body
      let elseExpr ← translateExpr orelse
      mkExpr sr (.IfThenElse testExpr bodyExpr (some elseExpr))

  -- F-string: f"{x} is {y}" -> string concatenation via PAdd (dynamic string concat)
  -- Bare literals emitted; elaboration handles coercions at PAdd boundaries.
  | .JoinedStr sr values => do
      if values.val.isEmpty then
        mkExpr sr (.LiteralString "")
      else
        let parts ← values.val.toList.mapM translateExpr
        let mut result ← mkExpr sr (.LiteralString "")
        for part in parts do
          result ← mkExpr sr (.StaticCall "PAdd" [result, part])
        pure result

  -- FormattedValue (f-string interpolation {expr}) -> to_string_any
  | .FormattedValue sr value _ _ => do
      let valueExpr ← translateExpr value
      mkExpr sr (.StaticCall "to_string_any" [valueExpr])

  -- Lambda: not yet supported structurally
  | .Lambda sr .. => mkExpr sr .Hole

  -- Unsupported but valid Python: emit Hole (preserves source location)
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

-- Statement Translation: one case per Python stmt constructor

/-- Translate a Python statement to Laurel. One case per constructor. -/
partial def translateStmt (s : Python.stmt SourceRange) : TransM (List StmtExprMd) := do
  let sr := s.ann
  match s with
  -- Assignment: x = expr
  -- Handles: simple assignment, tuple unpacking, object construction
  | .Assign _ targets value _ => do
      if targets.val.size == 1 then
        let target := targets.val[0]!
        -- Check for tuple unpacking on the target side
        match target with
        | .Tuple _ elts _ => do
            -- Tuple unpacking: a, b = rhs → tmp := rhs; a := Get(tmp, 0); b := Get(tmp, 1)
            let rhsExpr ← translateExpr value
            let tmpName ← freshVar "unpack"
            let tmpDecl ← mkExpr sr (.LocalVariable tmpName
                (mkTypeDefault (.TCore "Any")) (some rhsExpr))
            let tmpRef ← mkExpr sr (.Identifier tmpName)
            let mut assigns : List StmtExprMd := [tmpDecl]
            let mut idx : Int := 0
            for elt in elts.val.toList do
              let tgtExpr ← translateExpr elt
              let idxExpr ← mkExpr sr (.LiteralInt idx)
              let getExpr ← mkExpr sr (.StaticCall "Any_get" [tmpRef, idxExpr])
              let assignExpr ← mkExpr sr (.Assign [tgtExpr] getExpr)
              assigns := assigns ++ [assignExpr]
              idx := idx + 1
            pure assigns
        | _ => do
            -- Check if RHS is a class constructor call
            match value with
            | .Call _callSr (.Name _ calleeName _) callArgs callKwargs => do
                let info ← lookupName calleeName.val
                match info with
                | some (.class_ className _fields) => do
                    -- Object construction: two-phase protocol (New + __init__)
                    -- 1. target := New "ClassName" (heap allocation)
                    -- 2. ClassName@__init__(target, args...) (initialization)
                    -- This matches what lowering passes expect:
                    -- typeHierarchyTransform expands New into heap allocation,
                    -- heapParameterization threads heap through the call.
                    -- Record variable type for method dispatch
                    match target with
                    | .Name _ varName _ => recordVariableType varName.val className
                    | _ => pure ()
                    let targetExpr ← translateExpr target
                    let classId := Identifier.mk className none
                    let newExpr ← mkExpr sr (.New classId)
                    let assignNew ← mkExpr sr (.Assign [targetExpr] newExpr)
                    let posArgs ← callArgs.val.toList.mapM translateExpr
                    let kwargPairs ← callKwargs.val.toList.filterMapM (fun kw => do
                      match kw with
                      | .mk_keyword _ kwName kwExpr => do
                          let val ← translateExpr kwExpr
                          match kwName.val with
                          | some n => pure (some (n.val, val))
                          | none => pure none)
                    let initName := s!"{className}@__init__"
                    let allInitArgs ← resolveKwargs initName (targetExpr :: posArgs) kwargPairs
                    let initCall ← mkExpr sr (.StaticCall initName allInitArgs)
                    pure [assignNew, initCall]
                | _ => do
                    let targetExpr ← translateExpr target
                    let valueExpr ← translateExpr value
                    let assignExpr ← mkExpr sr (.Assign [targetExpr] valueExpr)
                    pure [assignExpr]
            | _ => do
                let targetExpr ← translateExpr target
                let valueExpr ← translateExpr value
                let assignExpr ← mkExpr sr (.Assign [targetExpr] valueExpr)
                pure [assignExpr]
      else
        throw (.unsupportedConstruct "Multiple assignment targets")

  -- Annotated assignment: x: int = expr
  -- Since scope hoisting already emits LocalVariable at function top,
  -- body-level AnnAssign emits just Assign (no duplicate declaration).
  -- For module-level AnnAssign (no scope hoisting), the variable is declared
  -- by the pipeline separately.
  -- Records the annotated type for later method qualification (With statements).
  | .AnnAssign _ target annotation value _ => do
      -- Record variable type if annotation names a known class (for method dispatch)
      match target with
      | .Name _ varName _ =>
          let annType := extractTypeStr annotation
          let info ← lookupName annType
          match info with
          | some (.class_ className _) => recordVariableType varName.val className
          | _ => pure ()
      | _ => pure ()
      match value.val with
      | some val => do
          -- Check if value is a class constructor call (same logic as Assign case)
          match val with
          | .Call _callSr (.Name _ calleeName _) callArgs callKwargs => do
              let info ← lookupName calleeName.val
              match info with
              | some (.class_ className _fields) => do
                  -- Object construction: two-phase protocol (New + __init__)
                  -- Record variable type for composite return detection
                  match target with
                  | .Name _ varName _ => recordVariableType varName.val className
                  | _ => pure ()
                  let targetExpr ← translateExpr target
                  let classId := Identifier.mk className none
                  let newExpr ← mkExpr sr (.New classId)
                  let assignNew ← mkExpr sr (.Assign [targetExpr] newExpr)
                  let posArgs ← callArgs.val.toList.mapM translateExpr
                  let kwargPairs ← callKwargs.val.toList.filterMapM (fun kw => do
                    match kw with
                    | .mk_keyword _ kwName kwExpr => do
                        let val ← translateExpr kwExpr
                        match kwName.val with
                        | some n => pure (some (n.val, val))
                        | none => pure none)
                  let initName := s!"{className}@__init__"
                  let allInitArgs ← resolveKwargs initName (targetExpr :: posArgs) kwargPairs
                  let initCall ← mkExpr sr (.StaticCall initName allInitArgs)
                  pure [assignNew, initCall]
              | _ => do
                  let targetExpr ← translateExpr target
                  let valExpr ← translateExpr val
                  let assignExpr ← mkExpr sr (.Assign [targetExpr] valExpr)
                  pure [assignExpr]
          | _ => do
              let targetExpr ← translateExpr target
              let valExpr ← translateExpr val
              let assignExpr ← mkExpr sr (.Assign [targetExpr] valExpr)
              pure [assignExpr]
      | none =>
          -- No value: declaration-only. Already hoisted by emitScopeDeclarations.
          pure []

  -- Augmented assignment: x += expr -> Assign [x] (PAdd x expr)
  | .AugAssign _ target op value => do
      let targetExpr ← translateExpr target
      let valueExpr ← translateExpr value
      let opName := match op with
        | .Add _ => "PAdd"
        | .Sub _ => "PSub"
        | .Mult _ => "PMul"
        | .FloorDiv _ => "PFloorDiv"
        | .Mod _ => "PMod"
        | .Div _ => "PDiv"
        | .Pow _ => "PPow"
        | .BitAnd _ => "PBitAnd"
        | .BitOr _ => "PBitOr"
        | .BitXor _ => "PBitXor"
        | .LShift _ => "PLShift"
        | .RShift _ => "PRShift"
        | .MatMult _ => "PMatMul"
      let rhs ← mkExpr sr (.StaticCall opName [targetExpr, valueExpr])
      let assignExpr ← mkExpr sr (.Assign [targetExpr] rhs)
      pure [assignExpr]

  -- If statement
  -- Condition emitted bare; elaboration inserts Any_to_bool at type boundary.
  | .If _ test body orelse => do
      let condExpr ← translateExpr test
      let bodyStmts ← translateStmtList body.val.toList
      let bodyBlock ← mkExpr sr (.Block bodyStmts none)
      let elseBlock ← if orelse.val.isEmpty then
        pure none
      else do
        let elseStmts ← translateStmtList orelse.val.toList
        let eb ← mkExpr sr (.Block elseStmts none)
        pure (some eb)
      let ifExpr ← mkExpr sr (.IfThenElse condExpr bodyBlock elseBlock)
      pure [ifExpr]

  -- While loop
  -- Condition emitted bare; elaboration inserts Any_to_bool at type boundary.
  -- Emits labeled blocks for break/continue:
  --   breakLabel: { while (cond) { continueLabel: { <body> } } }
  | .While _ test body _orelse => do
      let (breakLabel, continueLabel) ← pushLoopLabel "loop"
      let condExpr ← translateExpr test
      let bodyStmts ← translateStmtList body.val.toList
      -- Inner block: continue label wraps the body
      let continueBlock ← mkExpr sr (.Block bodyStmts (some continueLabel))
      let whileExpr ← mkExpr sr (.While condExpr [] none continueBlock)
      -- Outer block: break label wraps the while
      let breakBlock ← mkExpr sr (.Block [whileExpr] (some breakLabel))
      popLoopLabel
      pure [breakBlock]

  -- For loop: verification abstraction (havoc + assume)
  -- For(x, iter, body) → Havoc x; Assume(PIn(x, iter)); body'
  -- For tuple targets: For((a,b), iter, body) →
  --   tmp := Hole; a := Get(tmp, 0); b := Get(tmp, 1); Assume(PIn(tmp, iter)); body'
  -- Emits labeled blocks for break/continue:
  --   breakLabel: { continueLabel: { havoc; assume; <body> } }
  | .For _ target iter body _orelse _ => do
      let (breakLabel, continueLabel) ← pushLoopLabel "for"
      let iterExpr ← translateExpr iter
      let bodyStmts ← translateStmtList body.val.toList
      -- Handle tuple unpacking in for-loop target
      let (havocStmts, assumeTarget) ← match target with
        | .Tuple _ elts _ => do
            -- Tuple unpacking: for a, b in items
            -- havoc a tmp variable, then extract elements
            let tmpName ← freshVar "for_unpack"
            let holeExpr ← mkExpr sr (.Hole (deterministic := false))
            let tmpRef ← mkExpr sr (.Identifier tmpName)
            let tmpDecl ← mkExpr sr (.Assign [tmpRef] holeExpr)
            let mut assigns : List StmtExprMd := [tmpDecl]
            let mut idx : Int := 0
            for elt in elts.val.toList do
              let tgtExpr ← translateExpr elt
              let idxLit ← mkExpr sr (.LiteralInt idx)
              let getExpr ← mkExpr sr (.StaticCall "Any_get" [tmpRef, idxLit])
              let assignExpr ← mkExpr sr (.Assign [tgtExpr] getExpr)
              assigns := assigns ++ [assignExpr]
              idx := idx + 1
            pure (assigns, tmpRef)
        | _ => do
            -- Simple target: havoc directly
            let targetExpr ← translateExpr target
            let holeExpr ← mkExpr sr (.Hole (deterministic := false))
            let havoc ← mkExpr sr (.Assign [targetExpr] holeExpr)
            pure ([havoc], targetExpr)
      -- Assume: PIn(target, iter) — models that target is drawn from iter
      -- Elaboration inserts Any_to_bool at the Assume boundary if needed.
      let inExpr ← mkExpr sr (.StaticCall "PIn" [assumeTarget, iterExpr])
      let assume ← mkExpr sr (.Assume inExpr)
      -- Inner block: continue label wraps havoc + assume + body
      let continueBlock ← mkExpr sr (.Block (havocStmts ++ [assume] ++ bodyStmts) (some continueLabel))
      -- Outer block: break label wraps the continue block
      let breakBlock ← mkExpr sr (.Block [continueBlock] (some breakLabel))
      popLoopLabel
      pure [breakBlock]

  -- Return statement: emit "LaurelResult := value; exit $body"
  -- instead of a Return node. The Core translator's Return handler
  -- assigns to outputParams.head? which after heap parameterization
  -- is $heap (wrong). By emitting Assign + Exit directly, we target
  -- the correct output variable (LaurelResult) explicitly.
  --
  -- For composite-typed returns: emit Hole instead of the value.
  -- The old pipeline does this because Composite and Any are different
  -- Core datatypes that can't unify. The heap state (via updateField)
  -- carries the composite's data; the return value is opaque.
  | .Return _ value => do
      match value.val with
      | some expr => do
          let e ← translateExpr expr
          let laurelResultId ← mkExpr sr (.Identifier "LaurelResult")
          let assignResult ← mkExpr sr (.Assign [laurelResultId] e)
          let exitBody ← mkExpr sr (.Exit "$body")
          pure [assignResult, exitBody]
      | none => do
          let exitBody ← mkExpr sr (.Exit "$body")
          pure [exitBody]

  -- Assert statement
  -- Condition emitted bare; elaboration inserts Any_to_bool at type boundary.
  | .Assert _ test _msg => do
      let condExpr ← translateExpr test
      let assertExpr ← mkExpr sr (.Assert condExpr)
      pure [assertExpr]

  -- Expression statement (e.g., standalone function call)
  | .Expr _ value => do
      let expr ← translateExpr value
      pure [expr]

  -- Pass: no-op (emit nothing, not a Block — downstream passes don't expect
  -- empty Blocks as statements)
  | .Pass _ => pure []

  -- Break: Exit with the enclosing loop's break label
  | .Break _ => do
      let label ← currentBreakLabel
      match label with
      | some l => do
          let exitExpr ← mkExpr sr (.Exit l)
          pure [exitExpr]
      | none => do
          -- Fallback: should not happen in well-formed Python
          let exitExpr ← mkExpr sr (.Exit "break")
          pure [exitExpr]

  -- Continue: Exit with the enclosing loop's continue label
  | .Continue _ => do
      let label ← currentContinueLabel
      match label with
      | some l => do
          let exitExpr ← mkExpr sr (.Exit l)
          pure [exitExpr]
      | none => do
          -- Fallback: should not happen in well-formed Python
          let exitExpr ← mkExpr sr (.Exit "continue")
          pure [exitExpr]

  -- Try/except: labeled block structure matching the old pipeline's error protocol.
  -- Structure:
  --   Block [                                   -- labeled "try_end_N"
  --     Block [                                 -- labeled "exception_handlers_N"
  --       stmt1;
  --       if isError(maybe_except) then exit "exception_handlers_N";
  --       stmt2;
  --       if isError(maybe_except) then exit "exception_handlers_N";
  --       exit "try_end_N"                      -- normal completion skips handlers
  --     ];
  --     handler_stmts...                        -- only reached via exception exit
  --   ]
  -- The maybe_except variable is declared at function top (see translateFunction).
  -- Since try body statements are simple assignments (from_int, etc.) that cannot
  -- set maybe_except, isError(maybe_except) is always false and handlers are skipped.
  -- This gives the verifier precise control flow information.
  | .Try _ body handlers _orelse _finalbody => do
      let tryLabel := s!"try_end_{sr.start.byteIdx}"
      let catchersLabel := s!"exception_handlers_{sr.start.byteIdx}"

      -- Translate try body statements
      let bodyStmts ← translateStmtList body.val.toList

      -- Insert isError(maybe_except) check after each statement in try body
      let mut bodyStmtsWithChecks : List StmtExprMd := []
      for stmt in bodyStmts do
        bodyStmtsWithChecks := bodyStmtsWithChecks ++ [stmt]
        let maybeExcRef ← mkExpr sr (.Identifier "maybe_except")
        let isException ← mkExpr sr (.StaticCall "isError" [maybeExcRef])
        let exitToHandler ← mkExpr sr (.Exit catchersLabel)
        let errorCheck ← mkExpr sr (.IfThenElse isException exitToHandler none)
        bodyStmtsWithChecks := bodyStmtsWithChecks ++ [errorCheck]

      -- Normal completion: exit try block (skip handlers)
      let exitTry ← mkExpr sr (.Exit tryLabel)

      -- Catchers block: body with checks + exit on normal path
      let catchersBlock ← mkExpr sr (.Block (bodyStmtsWithChecks ++ [exitTry]) (some catchersLabel))

      -- Translate exception handlers
      let mut handlerStmts : List StmtExprMd := []
      for handler in handlers.val do
        match handler with
        | .ExceptHandler _ _ _excName handlerBody => do
            let hStmts ← translateStmtList handlerBody.val.toList
            handlerStmts := handlerStmts ++ hStmts

      -- Try block: catchers block + handlers
      let tryBlock ← mkExpr sr (.Block ([catchersBlock] ++ handlerStmts) (some tryLabel))
      pure [tryBlock]

  -- With statement: context manager protocol (enter/exit)
  -- With(expr, var, body) → mgr := expr; var := Type@__enter__(mgr); body; Type@__exit__(mgr)
  -- Emits FLAT statement list (no wrapping Block).
  -- Context managers modeled as type-qualified enter/exit calls.
  | .With _ items body _ => do
      let mut preamble : List StmtExprMd := []
      let mut cleanup : List StmtExprMd := []
      for item in items.val do
        match item with
        | .mk_withitem _ ctxExpr optVars => do
            let ctxVal ← translateExpr ctxExpr
            -- Determine the type of the context manager for method qualification.
            -- If ctxExpr is a variable, look up its recorded annotated type;
            -- otherwise use "Any". When type is "Any", emit Hole (no model available)
            -- like the old pipeline's mkInstanceMethodCall "Any" behavior.
            let mgrType ← match ctxExpr with
              | .Name _ rName _ => do
                  -- First check variable types recorded from annotations
                  let varType ← lookupVariableType rName.val
                  match varType with
                  | some className => pure className
                  | none => do
                    -- Fallback: check Γ for the variable's declared type
                    let info ← lookupName rName.val
                    match info with
                    | some (.variable (.UserDefined id)) => pure id.text
                    | _ => pure "Any"
              | _ => pure "Any"
            let enterName := if mgrType == "Any" then "__enter__" else s!"{mgrType}@__enter__"
            let exitName := if mgrType == "Any" then "__exit__" else s!"{mgrType}@__exit__"
            -- enter call
            let enterCall ← if mgrType == "Any" then
              mkExpr sr .Hole
            else
              mkExpr sr (.StaticCall enterName [ctxVal])
            -- exit call
            let exitCall ← if mgrType == "Any" then
              mkExpr sr .Hole
            else
              mkExpr sr (.StaticCall exitName [ctxVal])
            match optVars.val with
            | some varExpr => do
                let varTarget ← translateExpr varExpr
                let assignEnter ← mkExpr sr (.Assign [varTarget] enterCall)
                preamble := preamble ++ [assignEnter]
            | none =>
                preamble := preamble ++ [enterCall]
            cleanup := cleanup ++ [exitCall]
      -- body
      let bodyStmts ← translateStmtList body.val.toList
      -- Emit flat: preamble + body + cleanup
      pure (preamble ++ bodyStmts ++ cleanup)

  -- Raise: assign error to maybe_except (matching the error protocol)
  -- raise ExceptionType(msg) → maybe_except := ExceptionType(msg_string)
  -- The prelude Error type has constructors: TypeError, AttributeError, etc.
  -- For unknown exception types, use UnimplementedError as a generic fallback.
  | .Raise _ exc _ => do
      match exc.val with
      | some excExpr => do
          -- Parse raise ExcType(msg) to determine the Error constructor
          let errorExpr ← match excExpr with
            | .Call _ (.Name _ excName _) excArgs _ => do
                -- Map Python exception names to prelude Error constructors
                let errorCtor := match excName.val with
                  | "TypeError" => "TypeError"
                  | "AttributeError" => "AttributeError"
                  | "AssertionError" => "AssertionError"
                  | "IndexError" => "IndexError"
                  | "ValueError" => "UnimplementedError"
                  | "NotImplementedError" => "UnimplementedError"
                  | "RuntimeError" => "UnimplementedError"
                  | _ => "UnimplementedError"
                -- Get the message argument if present
                let msgArg ← if excArgs.val.size > 0 then do
                  let arg ← translateExpr excArgs.val[0]!
                  pure arg
                else
                  mkExpr sr (.LiteralString "")
                mkExpr sr (.StaticCall errorCtor [msgArg])
            | _ => do
                -- Bare expression: wrap in generic error
                let e ← translateExpr excExpr
                mkExpr sr (.StaticCall "UnimplementedError" [e])
          let maybeExcRef ← mkExpr sr (.Identifier "maybe_except")
          let assignError ← mkExpr sr (.Assign [maybeExcRef] errorExpr)
          pure [assignError]
      | none => do
          -- Bare raise (re-raise): assign generic error
          let errExpr ← mkExpr sr (.StaticCall "UnimplementedError" [mkExprDefault (.LiteralString "re-raise")])
          let maybeExcRef ← mkExpr sr (.Identifier "maybe_except")
          let assignError ← mkExpr sr (.Assign [maybeExcRef] errExpr)
          pure [assignError]

  -- Import / ImportFrom: no-ops (resolution handles these)
  | .Import _ _ => pure []
  | .ImportFrom _ _ _ _ => pure []

  -- Delete: unsupported
  | .Delete _ _ => do
      let hole ← mkExpr sr .Hole
      pure [hole]

  -- Global / Nonlocal: scoping hints (no-op in translation)
  | .Global _ _ => pure []
  | .Nonlocal _ _ => pure []

  -- Nested class/function defs at statement level: emit Hole
  -- (module-level translation handles these via translateFunction/translateClass)
  | .ClassDef .. => do
      let hole ← mkExpr sr .Hole
      pure [hole]
  | .FunctionDef .. => do
      let hole ← mkExpr sr .Hole
      pure [hole]

  -- TryStar (Python 3.11+): same labeled block structure as Try
  | .TryStar _ body handlers _orelse _finalbody => do
      let tryLabel := s!"try_end_{sr.start.byteIdx}"
      let catchersLabel := s!"exception_handlers_{sr.start.byteIdx}"

      let bodyStmts ← translateStmtList body.val.toList

      -- Insert isError(maybe_except) check after each statement
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
            let hStmts ← translateStmtList handlerBody.val.toList
            handlerStmts := handlerStmts ++ hStmts

      let tryBlock ← mkExpr sr (.Block ([catchersBlock] ++ handlerStmts) (some tryLabel))
      pure [tryBlock]

  -- Remaining: Hole
  | .Match _ .. => do let hole ← mkExpr sr .Hole; pure [hole]
  | .AsyncFor _ .. => do let hole ← mkExpr sr .Hole; pure [hole]
  | .AsyncWith _ .. => do let hole ← mkExpr sr .Hole; pure [hole]
  | .AsyncFunctionDef _ .. => do let hole ← mkExpr sr .Hole; pure [hole]
  | .TypeAlias _ .. => do let hole ← mkExpr sr .Hole; pure [hole]

/-- Translate a list of statements, concatenating results. -/
partial def translateStmtList (stmts : List (Python.stmt SourceRange)) : TransM (List StmtExprMd) := do
  let mut result : List StmtExprMd := []
  for stmt in stmts do
    let stmtExprs ← translateStmt stmt
    result := result ++ stmtExprs
  return result

-- Function Translation

/-- Emit scope declarations (LocalVariable) for all function-scoped variables.
    Python's scoping rule: any assignment within a function creates a function-local.
    We emit declarations at function top so verification knows their scope.

    Type-directed: uses the type from Resolution's collectFunctionLocals, which reads
    annotations. Only defaults to Any when no annotation is present.
    For variables annotated with a class type (composite), we use UserDefined so
    that heap parameterization correctly types them as Composite, matching the
    expected parameter types for __init__ and method calls. -/
partial def emitScopeDeclarations (sr : SourceRange)
    (body : Array (Python.stmt SourceRange))
    (paramNames : List String) : TransM (List StmtExprMd) := do
  let typedLocals := Resolution.TypeEnv.getFunctionLocals body paramNames
  let env ← read
  let mut decls : List StmtExprMd := []
  for (varName, varType) in typedLocals do
    -- If the variable's annotated type is a known class (composite), use
    -- UserDefined instead of Any. This ensures the variable gets type
    -- Composite after typeHierarchyTransform, matching __init__ param types.
    let actualType := match varType with
      | .TCore "Any" =>
          -- Check if there's an AnnAssign for this variable with a class type
          let annType := body.toList.findSome? fun stmt =>
            match stmt with
            | .AnnAssign _ (.Name _ n _) ann _ _ =>
                if n.val == varName then
                  let typeStr := Resolution.extractTypeStr ann
                  match env.names[typeStr]? with
                  | some (.class_ className _) =>
                      some (HighType.UserDefined (Identifier.mk className none))
                  | _ => none
                else none
            | _ => none
          annType.getD varType
      | _ => varType
    let decl ← mkExpr sr (.LocalVariable (Identifier.mk varName none) (mkTypeDefault actualType) none)
    decls := decls ++ [decl]
  pure decls

/-- Emit mutable parameter copies for method parameters.
    For each non-self parameter in a method:
      LocalVariable paramName type (some (Identifier "$in_paramName"))
    The procedure input is renamed to $in_paramName. -/
partial def emitMutableParamCopies (sr : SourceRange)
    (params : List (String × HighType)) : TransM (List StmtExprMd) := do
  let mut copies : List StmtExprMd := []
  for (pName, pType) in params do
    let inName := s!"$in_{pName}"
    let inRef ← mkExpr sr (.Identifier inName)
    let decl ← mkExpr sr (.LocalVariable pName (mkTypeDefault pType) (some inRef))
    copies := copies ++ [decl]
  pure copies

/-- Translate a Python FunctionDef to a Laurel Procedure.
    Type-directed: reads parameter and return type annotations directly.
    Handles: scope hoisting, mutable param copies (for methods). -/
partial def translateFunction (s : Python.stmt SourceRange)
    (isMethod : Bool := false) (className : Option String := none)
    : TransM (Option Procedure) := do
  match s with
  | .FunctionDef sr name args body _decorators _returns _typeComment _ => do
      -- Determine procedure name first (needed for Γ lookup)
      let procName := match className with
        | some cn => s!"{cn}@{name.val}"
        | none => name.val
      -- Translate parameters: use types from Γ (Resolution already extracted
      -- precise annotations). Only falls back to re-reading the AST if Γ has no entry.
      let allParams ← do
        let info ← lookupName procName
        match info with
        | some (.function sig) =>
            pure (sig.params.map fun (pName, pType) =>
              ({ name := Identifier.mk pName none, type := mkTypeDefault pType } : Parameter))
        | _ =>
            -- Fallback: read from AST (shouldn't happen if Resolution is correct)
            match args with
            | .mk_arguments _ _ argList _ _ _ _kwargs _defaults =>
                argList.val.toList.mapM fun arg => do
                  match arg with
                  | .mk_arg _ argName annotation _ =>
                    let paramType := match annotation.val with
                      | some annExpr => pythonTypeToLaurel (extractTypeStr annExpr)
                      | none => .TCore "Any"
                    pure ({ name := Identifier.mk argName.val none,
                            type := mkTypeDefault paramType } : Parameter)

      -- For methods: skip self, emit mutable copies for remaining params
      let (inputs, paramCopies) ← if isMethod then do
        -- self is typed as the composite class type so that Laurel resolution
        -- can correctly resolve field accesses (self#field) against the
        -- composite type's field definitions. This avoids field/variable name
        -- collisions when mutable param copies shadow field names.
        -- NOTE: This type becomes Composite after typeHierarchyTransform.
        let selfType := match className with
          | some cn => HighType.UserDefined (Identifier.mk cn none)
          | none => HighType.TCore "Any"
        let selfParam : Parameter := {
          name := Identifier.mk "self" none,
          type := mkTypeDefault selfType
        }
        -- Other params get the $in_ prefix for mutable copy
        let otherParams := if allParams.length > 0 then allParams.tail! else []
        let renamedParams := otherParams.map (fun p =>
          { p with name := Identifier.mk s!"$in_{p.name.text}" none })
        let paramPairs := otherParams.map (fun p => (p.name.text, p.type.val))
        let copies ← emitMutableParamCopies sr paramPairs
        pure (selfParam :: renamedParams, copies)
      else
        pure (allParams, [])

      -- Return type: from Γ (precise annotation). Only Any if genuinely unannotated.
      let returnType ← do
        let info ← lookupName procName
        match info with
        | some (.function sig) => pure sig.returnType
        | _ => pure (.TCore "Any")
      let outputs : List Parameter := [{ name := Identifier.mk "LaurelResult" none,
                                          type := mkTypeDefault returnType }]

      -- Scope hoisting: collect all assigned names in body, emit LocalVariable at top
      -- Uses Resolution.collectFunctionLocals for typed declarations
      -- Exclude both the renamed inputs ($in_X) and original param names (X) since
      -- mutable param copies already emit LocalVariable for the original names.
      let inputNames := inputs.map (fun p => p.name.text)
      let originalParamNames := allParams.map (fun p => p.name.text)
      let paramNames := inputNames ++ originalParamNames
      let scopeDecls ← emitScopeDeclarations sr body.val paramNames

      -- Exception handling variable: maybe_except is declared at function top
      -- (matching old pipeline's prependExceptHandlingHelper). Initialized to NoError().
      -- Try/except blocks use isError(maybe_except) to control handler dispatch.
      let noErrorInit ← mkExpr sr (.StaticCall "NoError" [])
      let maybeExceptDecl ← mkExpr sr
        (.LocalVariable "maybe_except" (mkTypeDefault (.TCore "Error")) (some noErrorInit))

      -- Translate body
      let bodyStmts ← translateStmtList body.val.toList

      -- Assemble: paramCopies + scopeDecls + maybe_except + body
      let allStmts := paramCopies ++ scopeDecls ++ [maybeExceptDecl] ++ bodyStmts
      let bodyBlock ← mkExpr sr (.Block allStmts none)

      let filePath := (← get).filePath

      pure (some {
        name := Identifier.mk procName none,
        inputs := inputs,
        outputs := outputs,
        preconditions := [],
        determinism := .deterministic none,
        decreases := none,
        isFunctional := false,
        body := .Transparent bodyBlock,
        md := sourceRangeToMd filePath sr
      })
  | _ => pure none

-- Class Translation

/-- Extract fields from class body: class-level AnnAssign statements.
    All fields are typed as Core(Any) for the dynamic pipeline.
    This ensures heap parameterization uses BoxAny (matching parameter types)
    and avoids type mismatches like "string vs Any" in field writes. -/
partial def extractFields (body : Array (Python.stmt SourceRange)) : TransM (List Field) := do
  let mut fields : List Field := []
  for stmt in body do
    match stmt with
    | .AnnAssign _ target _annotation _ _ =>
        match target with
        | .Name _ fieldName _ =>
            fields := fields ++ [{ name := Identifier.mk fieldName.val none,
                                    type := mkTypeDefault (.TCore "Any"),
                                    isMutable := true }]
        | _ => pure ()
    | _ => pure ()
  return fields

/-- Translate a Python ClassDef to a Laurel TypeDefinition and its methods. -/
partial def translateClass (s : Python.stmt SourceRange)
    : TransM (Option (TypeDefinition × List Procedure)) := do
  match s with
  | .ClassDef _ className _bases _ ⟨_, body⟩ _ _ => do
      let classNameStr := className.val

      -- Use TypeEnv's classFields (from Resolution) which includes both class-level
      -- and __init__-declared fields. Types come from annotations.
      let envFields ← lookupClassFields classNameStr
      let fields : List Field := envFields.map fun (fName, fType) =>
        { name := Identifier.mk fName none,
          type := mkTypeDefault fType,
          isMutable := true }

      -- Translate methods (as methods with mutable param copies)
      let mut methods : List Procedure := []
      for stmt in body do
        if let .FunctionDef .. := stmt then
          if let some proc ← translateFunction stmt (isMethod := true) (className := some classNameStr) then
            methods := methods ++ [proc]

      let compositeType : CompositeType := {
        name := Identifier.mk classNameStr none,
        extending := [],
        fields := fields,
        instanceProcedures := []  -- Methods are top-level static, not instance
      }

      pure (some (.Composite compositeType, methods))
  | _ => pure none

-- Module Translation

/-- Translate a Python module (top-level statement array) to a Laurel Program.
    Emits __name__ injection at module level. -/
partial def translateModule (stmts : Array (Python.stmt SourceRange)) : TransM Laurel.Program := do
  let mut procedures : List Procedure := []
  let mut types : List TypeDefinition := []

  for stmt in stmts do
    match stmt with
    | .FunctionDef .. => do
        if let some proc ← translateFunction stmt then
          procedures := procedures ++ [proc]
    | .ClassDef .. => do
        if let some (typeDef, classMethods) ← translateClass stmt then
          types := types ++ [typeDef]
          procedures := procedures ++ classMethods
    | _ => pure ()  -- Other top-level statements handled by pipeline

  return {
    staticProcedures := procedures,
    staticFields := [],
    types := types,
    constants := []
  }

end -- mutual

/-! ## Runner -/

/-- Run the translation pass.
    Input: Python AST + Resolution.TypeEnv + optional filePath
    Output: Laurel Program -/
def runTranslation (stmts : Array (Python.stmt SourceRange))
    (env : Resolution.TypeEnv := {}) (filePath : String := "")
    : Except TransError (Laurel.Program × TransState) :=
  (translateModule stmts).run env |>.run { filePath := filePath }

/-- Convenience: run translation with just a Resolution TypeEnv. -/
def runTranslationWithBase (stmts : Array (Python.stmt SourceRange))
    (baseEnv : Strata.Python.Resolution.TypeEnv := {})
    (filePath : String := "")
    : Except TransError (Laurel.Program × TransState) :=
  runTranslation stmts baseEnv filePath

end -- public section
end Strata.Python.Translation
