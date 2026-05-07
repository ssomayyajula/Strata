/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.Laurel
public import Strata.Languages.Python.PythonDialect

/-!
# Pass 1: Name Resolution

Walks the Python AST (top-level statements) and builds a unified type environment
(`TypeEnv`) where every name has a `NameInfo` entry.

## Design

Resolution and PySpec loading are the same operation — they produce the same output
type (`TypeEnv`). After resolution, every name that appears in the program has an
entry. Translation can look up any name and get a complete type signature without
guessing.

## Python Scoping

- Module-level: all top-level definitions visible everywhere
- Function-level: locals are function-scoped (not block-scoped)
- Class body: `self.field` resolved via class field list

## No Boolean Blindness

Consumers pattern-match on `NameInfo` variants directly. Each variant carries
everything needed — no boolean-returning query functions.

## What Γ Must Know (from ARCHITECTURE.md)

| Question | Answered by |
|---|---|
| Is `Foo` a class or a function? | `NameInfo.class_` vs `NameInfo.function` |
| What are `Foo`'s fields? | `NameInfo.class_ _ fields` |
| What are `f`'s parameter types and defaults? | `FuncSig.params`, `FuncSig.defaults` |
| What effects does `f` have? | `FuncSig.effectType` (pattern match) |
| What does `boto3.client("iam")` resolve to? | `overloadTable["client"]["iam"]` → `"IAMClient"` |
| What does `str(x)` map to in Laurel? | `builtinMap["str"]` → `"to_string_any"` |
| What type is `obj` for `obj.method()` dispatch? | `NameInfo.variable ty` → use `ty` to qualify method |
| What does `self.field` resolve to? | `classFields[currentClass][field]` |
-/

namespace Strata.Python.Resolution

open Strata.Laurel

public section

/-! ## Core Types -/

/-- Effect type: encodes what effects a function/procedure has.
    Pattern match on this — no boolean flags. -/
inductive EffectType where
  | pure (ty : HighType)
  | error (resultTy : HighType) (errTy : HighType)
  | stateful (resultTy : HighType)
  | statefulError (resultTy : HighType) (errTy : HighType)

/-- Extract the result type from an EffectType. -/
def EffectType.resultType : EffectType → HighType
  | .pure ty => ty
  | .error resultTy _ => resultTy
  | .stateful resultTy => resultTy
  | .statefulError resultTy _ => resultTy

structure FuncSig where
  name : String
  params : List (String × HighType)
  defaults : List (Option StmtExprMd)
  effectType : EffectType
  hasKwargs : Bool

instance : Inhabited FuncSig where
  default := { name := "", params := [], defaults := [], effectType := .pure (.TCore "Any"), hasKwargs := false }

/-- Classification of a name after resolution.
    Each variant is proof-relevant: it carries the data that translation needs
    to emit the correct Laurel node without further queries. -/
inductive NameInfo where
  /-- A class definition: carries field list for constructor emission -/
  | class_ (name : String) (fields : List (String × HighType))
  /-- A function or procedure: carries full signature -/
  | function (sig : FuncSig)
  /-- A variable binding: carries its type -/
  | variable (ty : HighType)
  /-- A module import: `import re` records "re" as a module.
      Translation uses this to translate `re.fullmatch(...)` → `re_fullmatch(...)`. -/
  | module_ (name : String)

instance : Inhabited NameInfo where
  default := .variable (.TCore "Any")

/-- The unified type environment produced by resolution.
    After this pass, every name in the program has an entry here.

    From ARCHITECTURE.md: "After resolution, every name in the program has an entry.
    Translation and elaboration look up any name and get a complete type signature
    without guessing." -/
structure TypeEnv where
  /-- What kind of thing is this name? -/
  names : Std.HashMap String NameInfo := {}
  /-- What are the fields of this class? (Redundant with NameInfo.class_ for
      fast field-level lookup by class name.) -/
  classFields : Std.HashMap String (List (String × HighType)) := {}
  /-- Factory dispatch: funcName → (stringArg → className).
      e.g., "client" → {"iam" → "IAMClient", "s3" → "S3Client"} -/
  overloadTable : Std.HashMap String (Std.HashMap String String) := {}
  /-- Python builtins → Laurel names.
      e.g., "str" → "to_string_any", "len" → "Any_len_to_Any" -/
  builtinMap : Std.HashMap String String := {}
  deriving Inhabited

/-! ## Type Extraction from Python Annotations -/

/-- Extract a type string from a Python type annotation expression.
    Handles Name, None constant, Subscript (generics), and Attribute forms. -/
def extractTypeStr : Python.expr SourceRange → String
  | .Name _ n _ => n.val
  | .Constant _ (.ConNone _) _ => "None"
  | .Subscript _ base slice _ =>
      let baseName := extractTypeStr base
      let argName := extractTypeStr slice
      s!"{baseName}[{argName}]"
  | .Attribute _ value attr _ =>
      let baseName := extractTypeStr value
      s!"{baseName}.{attr.val}"
  | _ => "Any"

/-- Convert a Python type string to a Laurel HighType.
    This is the canonical mapping used by both AST resolution and PySpec loading. -/
def pythonTypeToHighType : String → HighType
  | "int" => .TInt
  | "bool" => .TBool
  | "str" => .TString
  | "float" => .TFloat64
  | "None" => .TVoid
  | "Any" => .TCore "Any"
  | name => .UserDefined { text := name, uniqueId := none }

/-- Extract a HighType from a Python annotation expression.
    Composes extractTypeStr with pythonTypeToHighType. -/
def annotationToHighType (annotation : Python.expr SourceRange) : HighType :=
  pythonTypeToHighType (extractTypeStr annotation)

/-- Extract a HighType from an optional Python annotation expression.
    If no annotation is present, defaults to `Any`. -/
def optAnnotationToHighType : Option (Python.expr SourceRange) → HighType
  | some ann => annotationToHighType ann
  | none => .TCore "Any"

/-! ## Scope Resolution (Per-Function)

Python scoping rule: any assignment target in any branch/loop/try within a function
body is function-scoped. Resolution walks the function body to discover all assigned
names. Translation then emits `LocalVariable` declarations at function top.

From ARCHITECTURE.md:
"Resolution walks the function body, discovers all assigned names (Python's scoping
rule: assignment creates a function-local), and records them in Γ. Translation then
emits `LocalVariable` declarations at function top because Γ says they exist there."
-/

/-- Extract variable names from an assignment target expression.
    Handles simple names, tuples, and lists (for unpacking). -/
private partial def extractAssignTargetNames : Python.expr SourceRange → List String
  | .Name _ n _ => [n.val]
  | .Tuple _ elems _ => elems.val.toList.flatMap extractAssignTargetNames
  | .List _ elems _ => elems.val.toList.flatMap extractAssignTargetNames
  | .Starred _ inner _ => extractAssignTargetNames inner
  | _ => []  -- Attribute/Subscript targets don't create new locals

/-- Recursively collect assigned names from a single statement.
    Walks into if/for/while/try/with/match bodies (Python scope = function scope). -/
private partial def collectFromStmt (s : Python.stmt SourceRange) : List (String × HighType) :=
  match s with
  | .Assign _ targets _value _ =>
      targets.val.toList.flatMap fun target =>
        (extractAssignTargetNames target).map fun n => (n, .TCore "Any")
  | .AnnAssign _ target annotation _value _ =>
      let names := extractAssignTargetNames target
      let ty := annotationToHighType annotation
      names.map fun n => (n, ty)
  | .AugAssign _ target _ _ =>
      (extractAssignTargetNames target).map fun n => (n, .TCore "Any")
  | .If _ _ bodyStmts elseStmts =>
      bodyStmts.val.toList.flatMap collectFromStmt ++
      elseStmts.val.toList.flatMap collectFromStmt
  | .For _ target _ bodyStmts _orelse _ =>
      let targetNames := (extractAssignTargetNames target).map fun n => (n, .TCore "Any")
      targetNames ++ bodyStmts.val.toList.flatMap collectFromStmt
  | .AsyncFor _ target _ bodyStmts _orelse _ =>
      let targetNames := (extractAssignTargetNames target).map fun n => (n, .TCore "Any")
      targetNames ++ bodyStmts.val.toList.flatMap collectFromStmt
  | .While _ _ bodyStmts _orelse =>
      bodyStmts.val.toList.flatMap collectFromStmt
  | .Try _ bodyStmts handlers orelse finalbody =>
      let handlerPairs := handlers.val.toList.flatMap fun h =>
        match h with
        | .ExceptHandler _ _ maybeName handlerBody =>
            let errorVar := match maybeName.val with
              | some n => [(n.val, .UserDefined { text := "PythonError", uniqueId := none })]
              | none => []
            errorVar ++ handlerBody.val.toList.flatMap collectFromStmt
      bodyStmts.val.toList.flatMap collectFromStmt ++
      handlerPairs ++
      orelse.val.toList.flatMap collectFromStmt ++
      finalbody.val.toList.flatMap collectFromStmt
  | .TryStar _ bodyStmts handlers orelse finalbody =>
      let handlerPairs := handlers.val.toList.flatMap fun h =>
        match h with
        | .ExceptHandler _ _ maybeName handlerBody =>
            let errorVar := match maybeName.val with
              | some n => [(n.val, .UserDefined { text := "PythonError", uniqueId := none })]
              | none => []
            errorVar ++ handlerBody.val.toList.flatMap collectFromStmt
      bodyStmts.val.toList.flatMap collectFromStmt ++
      handlerPairs ++
      orelse.val.toList.flatMap collectFromStmt ++
      finalbody.val.toList.flatMap collectFromStmt
  | .With _ items bodyStmts _ =>
      let itemVars := items.val.toList.flatMap fun item =>
        match item with
        | .mk_withitem _ _ optVars =>
            match optVars.val with
            | some varExpr => (extractAssignTargetNames varExpr).map fun n => (n, .TCore "Any")
            | none => []
      itemVars ++ bodyStmts.val.toList.flatMap collectFromStmt
  | .AsyncWith _ items bodyStmts _ =>
      let itemVars := items.val.toList.flatMap fun item =>
        match item with
        | .mk_withitem _ _ optVars =>
            match optVars.val with
            | some varExpr => (extractAssignTargetNames varExpr).map fun n => (n, .TCore "Any")
            | none => []
      itemVars ++ bodyStmts.val.toList.flatMap collectFromStmt
  | .Match _ _ cases =>
      cases.val.toList.flatMap fun c =>
        match c with
        | .mk_match_case _ _ _ caseBody => caseBody.val.toList.flatMap collectFromStmt
  | _ => []

/-- Collect ALL assigned variable names within a function body (Python scoping rule).

    Walks recursively into if/for/while/try/with/match bodies. Returns a list of
    `(varName, type)` pairs. Types come from annotations when available, otherwise `Any`.

    Excludes parameter names (passed in `paramNames`) since those are already declared.

    From ARCHITECTURE.md:
    "Variable `x` assigned inside `for` loop — where does it live? Function scope."
    "Variable `e` from `except E as e:` — visible after? Function scope."
    "Variable `x` assigned in both branches of `if` — one declaration or two? One, at function scope." -/
def collectFunctionLocals (body : Array (Python.stmt SourceRange)) (paramNames : List String)
    : List (String × HighType) := Id.run do
  -- Collect all (name, type) pairs, then deduplicate by name
  let allPairs := body.toList.flatMap collectFromStmt
  -- Deduplicate: keep first occurrence, exclude param names
  let mut seen : Std.HashSet String := {}
  for p in paramNames do
    seen := seen.insert p
  let mut result : List (String × HighType) := []
  for (name, ty) in allPairs do
    if !seen.contains name then
      seen := seen.insert name
      result := result ++ [(name, ty)]
  return result

/-! ## Building TypeEnv from Python AST -/

/-- Extract parameters from a Python arguments node.
    Returns (paramName, paramType) pairs. -/
private def extractParams (args : Python.arguments SourceRange) : List (String × HighType) :=
  match args with
  | .mk_arguments _ _posonlyargs argList _vararg _kwonly _kwDefaults _kwarg _defaults =>
      argList.val.toList.map fun arg =>
        match arg with
        | .mk_arg _ argName annotation _ =>
            let ty := match annotation.val with
              | some annExpr => annotationToHighType annExpr
              | none => .TCore "Any"
            (argName.val, ty)

/-- Extract whether the arguments have **kwargs. -/
private def hasKwargsArg (args : Python.arguments SourceRange) : Bool :=
  match args with
  | .mk_arguments _ _ _ _ _ _ kwarg _ =>
      kwarg.val.isSome

/-- Extract defaults aligned to params list.
    Python convention: defaults are right-aligned to the params list.
    Returns a list of `Option StmtExprMd` of same length as params,
    where `none` = required and `some placeholder` = has a default.
    At resolution time, we don't translate the default expressions yet —
    we only record THAT a default exists (as a Hole placeholder). -/
private def extractDefaults (args : Python.arguments SourceRange) : List (Option StmtExprMd) :=
  match args with
  | .mk_arguments _ _posonlyargs argList _ _ _ _ defaults =>
      let paramCount := argList.val.size
      let defaultCount := defaults.val.size
      let requiredCount := paramCount - defaultCount
      -- First `requiredCount` params have no default
      let nones := (List.range requiredCount).map fun _ => (none : Option StmtExprMd)
      -- Remaining params have defaults (represented as Hole placeholders since we
      -- haven't translated to Laurel yet)
      let somes := (List.range defaultCount).map fun _ =>
        (some (⟨StmtExpr.Hole, #[]⟩ : StmtExprMd))
      nones ++ somes

/-- Extract the return type from an optional Python annotation. -/
private def extractReturnType (returns : Ann (Option (Python.expr SourceRange)) SourceRange)
    : HighType :=
  match returns.val with
  | some retExpr => annotationToHighType retExpr
  | none => .TCore "Any"

/-- Detect whether a function body contains a raise statement or has exception handler patterns
    that indicate it may produce an error output.
    This is a heuristic — PySpec data provides the definitive answer. -/
private def detectErrorOutput (body : Array (Python.stmt SourceRange)) : Bool :=
  body.any fun s =>
    match s with
    | .Raise _ _ _ => true
    | _ => false

/-- Process a top-level FunctionDef and produce a NameInfo.function entry. -/
private def resolveFunctionDef (name : Ann String SourceRange)
    (args : Python.arguments SourceRange)
    (body : Ann (Array (Python.stmt SourceRange)) SourceRange)
    (returns : Ann (Option (Python.expr SourceRange)) SourceRange) : (String × NameInfo) :=
  let params := extractParams args
  let defaults := extractDefaults args
  let retTy := extractReturnType returns
  let hasError := detectErrorOutput body.val
  let hasKw := hasKwargsArg args
  let sig : FuncSig := {
    name := name.val,
    params := params,
    defaults := defaults,
    effectType := if hasError then .error retTy (.TCore "Error") else .pure retTy,
    hasKwargs := hasKw
  }
  (name.val, .function sig)

/-- Process a top-level ClassDef and produce NameInfo entries for the class
    and its methods. Returns entries for the class name and for each method
    (qualified as ClassName@methodName). -/
private def resolveClassDef (name : Ann String SourceRange)
    (body : Ann (Array (Python.stmt SourceRange)) SourceRange)
    : List (String × NameInfo) × (String × List (String × HighType)) := Id.run do
  let mut fields : List (String × HighType) := []
  let mut methodEntries : List (String × NameInfo) := []
  for s in body.val do
    match s with
    | .AnnAssign _ target annotation _ _ =>
        let fieldName := match target with
          | .Name _ n _ => n.val
          | _ => "unknown"
        let fieldType := annotationToHighType annotation
        fields := fields ++ [(fieldName, fieldType)]
    | .FunctionDef _ methodName methodArgs methodBody _ methodReturns _ _ =>
        let qualName := s!"{name.val}@{methodName.val}"
        let allParams := extractParams methodArgs
        let allDefaults := extractDefaults methodArgs
        let params := match allParams with
          | _ :: rest => rest
          | [] => []
        let defaults := match allDefaults with
          | _ :: rest => rest
          | [] => []
        let retTy := extractReturnType methodReturns
        let hasError := detectErrorOutput methodBody.val
        let hasKw := hasKwargsArg methodArgs
        let sig : FuncSig := {
          name := qualName,
          params := params,
          defaults := defaults,
          effectType := if hasError then .error retTy (.TCore "Error") else .pure retTy,
          hasKwargs := hasKw
        }
        methodEntries := methodEntries ++ [(qualName, .function sig)]
    | _ => pure ()
  -- Also extract fields from __init__ body (self.x = ... patterns)
  for s in body.val do
    match s with
    | .FunctionDef _ initName _ initBody _ _ _ _ =>
        if initName.val == "__init__" then
          for bodyStmt in initBody.val do
            match bodyStmt with
            | .AnnAssign _ (.Attribute _ _ attr _) annotation _ _ =>
                let fieldName := attr.val
                let fieldType := annotationToHighType annotation
                -- Only add if not already declared at class level
                if !fields.any (fun (n, _) => n == fieldName) then
                  fields := fields ++ [(fieldName, fieldType)]
            | _ => pure ()
    | _ => pure ()
  let classEntry := (name.val, NameInfo.class_ name.val fields)
  let allEntries := [classEntry] ++ methodEntries
  (allEntries, (name.val, fields))

/-! ## Builtin Map

Python builtins → Laurel procedure names. Translation uses this to rewrite
`str(x)` → `StaticCall "to_string_any" [x]` etc. without guessing.
-/

/-- Default mapping of Python builtin function names to Laurel procedure names. -/
def defaultBuiltinMap : Std.HashMap String String :=
  let entries : List (String × String) := [
    ("str", "to_string_any"),
    ("int", "to_int_any"),
    ("float", "to_float_any"),
    ("bool", "Any_to_bool"),
    ("len", "Any_len_to_Any"),
    ("abs", "Any_abs_to_Any"),
    ("print", "print"),
    ("repr", "to_string_any"),
    ("type", "Any_type_to_Any"),
    ("isinstance", "Any_isinstance_to_bool"),
    ("hasattr", "Any_hasattr_to_bool"),
    ("getattr", "Any_getattr_to_Any"),
    ("setattr", "Any_setattr_to_Any"),
    ("sorted", "Any_sorted_to_Any"),
    ("reversed", "Any_reversed_to_Any"),
    ("enumerate", "Any_enumerate_to_Any"),
    ("zip", "Any_zip_to_Any"),
    ("range", "Any_range_to_Any"),
    ("list", "Any_list_to_Any"),
    ("dict", "Any_dict_to_Any"),
    ("set", "Any_set_to_Any"),
    ("tuple", "Any_tuple_to_Any"),
    ("min", "Any_min_to_Any"),
    ("max", "Any_max_to_Any"),
    ("sum", "Any_sum_to_Any"),
    ("any", "Any_any_to_bool"),
    ("all", "Any_all_to_bool"),
    ("ord", "Any_ord_to_Any"),
    ("chr", "Any_chr_to_Any"),
    ("map", "Any_map_to_Any"),
    ("filter", "Any_filter_to_Any"),
    ("timedelta", "timedelta_func")
  ]
  entries.foldl (fun m (k, v) => m.insert k v) {}

/-- Walk top-level statements once and build the TypeEnv.
    This is the primary entry point for Pass 1. -/
def buildTypeEnv (stmts : Array (Python.stmt SourceRange)) : TypeEnv := Id.run do
  let mut names : Std.HashMap String NameInfo := {}
  let mut classFields : Std.HashMap String (List (String × HighType)) := {}
  for stmt in stmts do
    match stmt with
    | .FunctionDef _ name args body _ returns _ _ =>
        let (n, info) := resolveFunctionDef name args body returns
        names := names.insert n info
    | .ClassDef _ name _ _ body _ _ =>
        let (entries, (className, fields)) := resolveClassDef name body
        for (n, info) in entries do
          names := names.insert n info
        classFields := classFields.insert className fields
    | .Assign _ targets value _ =>
        -- Module-level assignment: x = expr → variable with inferred type
        for target in targets.val do
          match target with
          | .Name _ n _ =>
              -- Without annotation, type is Any
              let ty := match value with
                | .Constant _ (.ConPos _ _) _ => HighType.TInt
                | .Constant _ (.ConNeg _ _) _ => HighType.TInt
                | .Constant _ (.ConString _ _) _ => HighType.TString
                | .Constant _ (.ConTrue _) _ => HighType.TBool
                | .Constant _ (.ConFalse _) _ => HighType.TBool
                | .Constant _ (.ConFloat _ _) _ => HighType.TFloat64
                | .Constant _ (.ConNone _) _ => HighType.TVoid
                | _ => .TCore "Any"
              names := names.insert n.val (.variable ty)
          | _ => pure ()
    | .AnnAssign _ target annotation _ _ =>
        -- Module-level annotated assignment: x: int = expr → variable with annotation type
        match target with
        | .Name _ n _ =>
            let ty := annotationToHighType annotation
            names := names.insert n.val (.variable ty)
        | _ => pure ()
    | .Import _ aliases =>
        -- `import re` → record "re" as a module name.
        -- `import foo.bar` → record "foo" as a module (Python uses the top-level name).
        for alias in aliases.val do
          match alias with
          | .mk_alias _ modName asName =>
              let registeredName := match asName.val with
                | some aliasName => aliasName.val
                | none =>
                    -- For dotted imports like `import os.path`, Python binds `os`
                    match modName.val.splitOn "." with
                    | first :: _ => first
                    | [] => modName.val
              names := names.insert registeredName (.module_ modName.val)
    | .ImportFrom _ modName imports _ =>
        -- `from re import fullmatch` → record "re" as module (for `re.X` patterns)
        -- Also record the imported names as functions (best effort)
        match modName.val with
        | some mn =>
            -- Record the module itself so that if user writes `re.fullmatch` it works
            let topLevel := match mn.val.splitOn "." with
              | first :: _ => first
              | [] => mn.val
            -- Only register if not already known as something more specific
            if !names.contains topLevel then
              names := names.insert topLevel (.module_ mn.val)
            -- For `from X import Y`, record Y as a function mapping to module_Y
            for imp in imports.val do
              match imp with
              | .mk_alias _ impName _asName =>
                  let funcName := s!"{mn.val.replace "." "_"}_{impName.val}"
                  -- Record as function if not already known
                  if !names.contains impName.val then
                    names := names.insert impName.val (.function {
                      name := funcName,
                      params := [],  -- Unknown params
                      defaults := [],
                      effectType := .pure (.TCore "Any"),
                      hasKwargs := false
                    })
        | none => pure ()
    | _ => pure ()
  return { names := names, classFields := classFields,
           overloadTable := {}, builtinMap := defaultBuiltinMap }

/-! ## Prelude Operations -/

/-- Prelude function signatures: arithmetic, coercions, builtins.
    These are the operations that Python's operators and builtins map to. -/
def preludeSignatures : List (String × FuncSig) := [
  -- Arithmetic operators
  ("PAdd", { name := "PAdd", params := [("left", .TCore "Any"), ("right", .TCore "Any")], defaults := [none, none], effectType := .pure (.TCore "Any"), hasKwargs := false }),
  ("PSub", { name := "PSub", params := [("left", .TCore "Any"), ("right", .TCore "Any")], defaults := [none, none], effectType := .pure (.TCore "Any"), hasKwargs := false }),
  ("PMul", { name := "PMul", params := [("left", .TCore "Any"), ("right", .TCore "Any")], defaults := [none, none], effectType := .pure (.TCore "Any"), hasKwargs := false }),
  ("PDiv", { name := "PDiv", params := [("left", .TCore "Any"), ("right", .TCore "Any")], defaults := [none, none], effectType := .pure (.TCore "Any"), hasKwargs := false }),
  ("PFloorDiv", { name := "PFloorDiv", params := [("left", .TCore "Any"), ("right", .TCore "Any")], defaults := [none, none], effectType := .pure (.TCore "Any"), hasKwargs := false }),
  ("PMod", { name := "PMod", params := [("left", .TCore "Any"), ("right", .TCore "Any")], defaults := [none, none], effectType := .pure (.TCore "Any"), hasKwargs := false }),
  ("PPow", { name := "PPow", params := [("left", .TCore "Any"), ("right", .TCore "Any")], defaults := [none, none], effectType := .pure (.TCore "Any"), hasKwargs := false }),
  -- Bitwise operators
  ("PBitAnd", { name := "PBitAnd", params := [("left", .TCore "Any"), ("right", .TCore "Any")], defaults := [none, none], effectType := .pure (.TCore "Any"), hasKwargs := false }),
  ("PBitOr", { name := "PBitOr", params := [("left", .TCore "Any"), ("right", .TCore "Any")], defaults := [none, none], effectType := .pure (.TCore "Any"), hasKwargs := false }),
  ("PBitXor", { name := "PBitXor", params := [("left", .TCore "Any"), ("right", .TCore "Any")], defaults := [none, none], effectType := .pure (.TCore "Any"), hasKwargs := false }),
  ("PLShift", { name := "PLShift", params := [("left", .TCore "Any"), ("right", .TCore "Any")], defaults := [none, none], effectType := .pure (.TCore "Any"), hasKwargs := false }),
  ("PRShift", { name := "PRShift", params := [("left", .TCore "Any"), ("right", .TCore "Any")], defaults := [none, none], effectType := .pure (.TCore "Any"), hasKwargs := false }),
  -- Comparison operators
  ("PEq", { name := "PEq", params := [("left", .TCore "Any"), ("right", .TCore "Any")], defaults := [none, none], effectType := .pure (.TCore "Any"), hasKwargs := false }),
  ("PNEq", { name := "PNEq", params := [("left", .TCore "Any"), ("right", .TCore "Any")], defaults := [none, none], effectType := .pure (.TCore "Any"), hasKwargs := false }),
  ("PLt", { name := "PLt", params := [("left", .TCore "Any"), ("right", .TCore "Any")], defaults := [none, none], effectType := .pure (.TCore "Any"), hasKwargs := false }),
  ("PLe", { name := "PLe", params := [("left", .TCore "Any"), ("right", .TCore "Any")], defaults := [none, none], effectType := .pure (.TCore "Any"), hasKwargs := false }),
  ("PGt", { name := "PGt", params := [("left", .TCore "Any"), ("right", .TCore "Any")], defaults := [none, none], effectType := .pure (.TCore "Any"), hasKwargs := false }),
  ("PGe", { name := "PGe", params := [("left", .TCore "Any"), ("right", .TCore "Any")], defaults := [none, none], effectType := .pure (.TCore "Any"), hasKwargs := false }),
  ("PIn", { name := "PIn", params := [("left", .TCore "Any"), ("right", .TCore "Any")], defaults := [none, none], effectType := .pure (.TCore "Any"), hasKwargs := false }),
  ("PNotIn", { name := "PNotIn", params := [("left", .TCore "Any"), ("right", .TCore "Any")], defaults := [none, none], effectType := .pure (.TCore "Any"), hasKwargs := false }),
  ("PIs", { name := "PIs", params := [("left", .TCore "Any"), ("right", .TCore "Any")], defaults := [none, none], effectType := .pure (.TCore "Any"), hasKwargs := false }),
  ("PIsNot", { name := "PIsNot", params := [("left", .TCore "Any"), ("right", .TCore "Any")], defaults := [none, none], effectType := .pure (.TCore "Any"), hasKwargs := false }),
  -- Logical/unary operators
  ("PAnd", { name := "PAnd", params := [("left", .TCore "Any"), ("right", .TCore "Any")], defaults := [none, none], effectType := .pure (.TCore "Any"), hasKwargs := false }),
  ("POr", { name := "POr", params := [("left", .TCore "Any"), ("right", .TCore "Any")], defaults := [none, none], effectType := .pure (.TCore "Any"), hasKwargs := false }),
  ("PNot", { name := "PNot", params := [("operand", .TCore "Any")], defaults := [none], effectType := .pure (.TCore "Any"), hasKwargs := false }),
  ("PNeg", { name := "PNeg", params := [("operand", .TCore "Any")], defaults := [none], effectType := .pure (.TCore "Any"), hasKwargs := false }),
  ("PPos", { name := "PPos", params := [("operand", .TCore "Any")], defaults := [none], effectType := .pure (.TCore "Any"), hasKwargs := false }),
  ("PInvert", { name := "PInvert", params := [("operand", .TCore "Any")], defaults := [none], effectType := .pure (.TCore "Any"), hasKwargs := false }),
  -- Coercion functions (elaboration inserts these)
  ("from_int", { name := "from_int", params := [("value", .TInt)], defaults := [none], effectType := .pure (.TCore "Any"), hasKwargs := false }),
  ("from_str", { name := "from_str", params := [("value", .TString)], defaults := [none], effectType := .pure (.TCore "Any"), hasKwargs := false }),
  ("from_bool", { name := "from_bool", params := [("value", .TBool)], defaults := [none], effectType := .pure (.TCore "Any"), hasKwargs := false }),
  ("from_float", { name := "from_float", params := [("value", .TFloat64)], defaults := [none], effectType := .pure (.TCore "Any"), hasKwargs := false }),
  ("from_Composite", { name := "from_Composite", params := [("value", .TCore "Any")], defaults := [none], effectType := .pure (.TCore "Any"), hasKwargs := false }),
  -- Downcast functions
  ("Any_to_bool", { name := "Any_to_bool", params := [("value", .TCore "Any")], defaults := [none], effectType := .pure (.TBool), hasKwargs := false }),
  ("Any..as_int!", { name := "Any..as_int!", params := [("value", .TCore "Any")], defaults := [none], effectType := .pure (.TInt), hasKwargs := false }),
  ("Any..as_string!", { name := "Any..as_string!", params := [("value", .TCore "Any")], defaults := [none], effectType := .pure (.TString), hasKwargs := false }),
  -- Collection constructors: use .TCore "ListAny"/.TCore "DictStrAny" for correct
  -- type annotations in ANF bindings. Elaboration's isSubtype treats same-named
  -- TCore types as equal, so no spurious coercions are inserted between ListAny values.
  ("ListAny_nil", { name := "ListAny_nil", params := [], defaults := [], effectType := .pure (.TCore "ListAny"), hasKwargs := false }),
  ("ListAny_cons", { name := "ListAny_cons", params := [("head", .TCore "Any"), ("tail", .TCore "ListAny")], defaults := [none, none], effectType := .pure (.TCore "ListAny"), hasKwargs := false }),
  ("DictStrAny_empty", { name := "DictStrAny_empty", params := [], defaults := [], effectType := .pure (.TCore "DictStrAny"), hasKwargs := false }),
  ("DictStrAny_cons", { name := "DictStrAny_cons", params := [("key", .TString), ("val", .TCore "Any"), ("tail", .TCore "DictStrAny")], defaults := [none, none, none], effectType := .pure (.TCore "DictStrAny"), hasKwargs := false }),
  ("from_ListAny", { name := "from_ListAny", params := [("list", .TCore "ListAny")], defaults := [none], effectType := .pure (.TCore "Any"), hasKwargs := false }),
  ("from_DictStrAny", { name := "from_DictStrAny", params := [("dict", .TCore "DictStrAny")], defaults := [none], effectType := .pure (.TCore "Any"), hasKwargs := false }),
  ("from_None", { name := "from_None", params := [], defaults := [], effectType := .pure (.TCore "Any"), hasKwargs := false }),
  -- Legacy collection constructors (for backward compatibility)
  ("List_new", { name := "List_new", params := [], defaults := [], effectType := .pure (.TCore "Any"), hasKwargs := false }),
  ("Dict_new", { name := "Dict_new", params := [], defaults := [], effectType := .pure (.TCore "Any"), hasKwargs := false }),
  ("Tuple_new", { name := "Tuple_new", params := [], defaults := [], effectType := .pure (.TCore "Any"), hasKwargs := false }),
  -- Subscript / slice
  ("Any_get", { name := "Any_get", params := [("collection", .TCore "Any"), ("key", .TCore "Any")], defaults := [none, none], effectType := .pure (.TCore "Any"), hasKwargs := false }),
  ("Get", { name := "Get", params := [("collection", .TCore "Any"), ("key", .TCore "Any")], defaults := [none, none], effectType := .pure (.TCore "Any"), hasKwargs := false }),
  ("Slice_new", { name := "Slice_new", params := [("start", .TCore "Any"), ("stop", .TCore "Any")], defaults := [none, none], effectType := .pure (.TCore "Any"), hasKwargs := false }),
  -- String operations
  ("StrConcat", { name := "StrConcat", params := [("left", .TCore "Any"), ("right", .TCore "Any")], defaults := [none, none], effectType := .pure (.TCore "Any"), hasKwargs := false }),
  ("ToString", { name := "ToString", params := [("value", .TCore "Any")], defaults := [none], effectType := .pure (.TCore "Any"), hasKwargs := false }),
  ("to_string_any", { name := "to_string_any", params := [("value", .TCore "Any")], defaults := [none], effectType := .pure (.TCore "Any"), hasKwargs := false }),
  -- Error handling: isError checks Error values, exception wraps Error into Any.
  -- Error constructors all take a string message and produce Error.
  ("isError", { name := "isError", params := [("e", .TCore "Error")], defaults := [none], effectType := .pure (.TBool), hasKwargs := false }),
  ("NoError", { name := "NoError", params := [], defaults := [], effectType := .pure (.TCore "Error"), hasKwargs := false }),
  ("exception", { name := "exception", params := [("e", .TCore "Error")], defaults := [none], effectType := .pure (.TCore "Any"), hasKwargs := false }),
  ("TypeError", { name := "TypeError", params := [("msg", .TString)], defaults := [none], effectType := .pure (.TCore "Error"), hasKwargs := false }),
  ("AttributeError", { name := "AttributeError", params := [("msg", .TString)], defaults := [none], effectType := .pure (.TCore "Error"), hasKwargs := false }),
  ("AssertionError", { name := "AssertionError", params := [("msg", .TString)], defaults := [none], effectType := .pure (.TCore "Error"), hasKwargs := false }),
  ("UnimplementedError", { name := "UnimplementedError", params := [("msg", .TString)], defaults := [none], effectType := .pure (.TCore "Error"), hasKwargs := false }),
  ("UndefinedError", { name := "UndefinedError", params := [("msg", .TString)], defaults := [none], effectType := .pure (.TCore "Error"), hasKwargs := false }),
  ("IndexError", { name := "IndexError", params := [("msg", .TString)], defaults := [none], effectType := .pure (.TCore "Error"), hasKwargs := false }),
  ("RePatternError", { name := "RePatternError", params := [("msg", .TString)], defaults := [none], effectType := .pure (.TCore "Error"), hasKwargs := false }),
  -- Special
  ("None", { name := "None", params := [], defaults := [], effectType := .pure (.TCore "Any"), hasKwargs := false }),
  ("hasNext", { name := "hasNext", params := [("iter", .TCore "Any")], defaults := [none], effectType := .pure (.TBool), hasKwargs := false }),
  ("next", { name := "next", params := [("iter", .TCore "Any")], defaults := [none], effectType := .pure (.TCore "Any"), hasKwargs := false }),
  ("__enter__", { name := "__enter__", params := [("ctx", .TCore "Any")], defaults := [none], effectType := .pure (.TCore "Any"), hasKwargs := false }),
  ("__exit__", { name := "__exit__", params := [("ctx", .TCore "Any")], defaults := [none], effectType := .pure (.TCore "Any"), hasKwargs := false }),
  ("call", { name := "call", params := [], defaults := [], effectType := .pure (.TCore "Any"), hasKwargs := false }),
  -- timedelta: both params are optional (default None per prelude requires)
  ("timedelta_func", { name := "timedelta_func", params := [("days", .TCore "Any"), ("hours", .TCore "Any")], defaults := [some ⟨.Hole, #[]⟩, some ⟨.Hole, #[]⟩], effectType := .error (.TCore "Any") (.TCore "Error"), hasKwargs := false })
]

/-- Build the prelude TypeEnv containing all builtin operation signatures. -/
def preludeTypeEnv : TypeEnv := Id.run do
  let mut names : Std.HashMap String NameInfo := {}
  for (n, sig) in preludeSignatures do
    names := names.insert n (.function sig)
  return { names := names, classFields := {}, overloadTable := {}, builtinMap := {} }

/-! ## Merging Environments -/

/-- Merge two TypeEnvs. Entries in `b` override entries in `a`. -/
def TypeEnv.merge (a b : TypeEnv) : TypeEnv := Id.run do
  let mut names := a.names
  for (k, v) in b.names.toList do
    names := names.insert k v
  let mut classFields := a.classFields
  for (k, v) in b.classFields.toList do
    classFields := classFields.insert k v
  let mut overloadTable := a.overloadTable
  for (k, v) in b.overloadTable.toList do
    overloadTable := overloadTable.insert k v
  let mut builtinMap := a.builtinMap
  for (k, v) in b.builtinMap.toList do
    builtinMap := builtinMap.insert k v
  return { names := names, classFields := classFields,
           overloadTable := overloadTable, builtinMap := builtinMap }

/-- Merge prelude signatures into a TypeEnv.
    Prelude entries do not override user-defined entries. -/
def TypeEnv.withPrelude (env : TypeEnv) : TypeEnv := Id.run do
  let mut names := env.names
  for (n, sig) in preludeSignatures do
    -- Only insert if not already defined by user code
    if !names.contains n then
      names := names.insert n (.function sig)
  return { env with names := names }

/-- Merge procedure signatures from a Laurel runtime program into a TypeEnv.
    Extracts FuncSig from each procedure's inputs/outputs.
    Does not override user-defined entries. -/
def TypeEnv.withRuntimeProgram (env : TypeEnv) (runtime : Laurel.Program) : TypeEnv := Id.run do
  let mut names := env.names
  for proc in runtime.staticProcedures do
    let procName := proc.name.text
    if !names.contains procName then
      let params := proc.inputs.map fun p => (p.name.text, p.type.val)
      let retTy := match proc.outputs with
        | [out] => out.type.val
        | _ => HighType.TCore "Any"
      let defaults := params.map fun _ => (none : Option StmtExprMd)
      let effectType := EffectType.pure retTy
      let sig : FuncSig := { name := procName, params, defaults, effectType, hasKwargs := false }
      names := names.insert procName (.function sig)
  return { env with names := names }

/-- Merge PySpec data into a TypeEnv.
    Takes parallel maps of procedure signatures and class definitions
    from the PySpec loader and inserts them as NameInfo entries. -/
def TypeEnv.mergeSpecs (env : TypeEnv)
    (procedures : Std.HashMap String (List (String × String) × String))
    (composites : Std.HashMap String (List (String × String)))
    : TypeEnv := Id.run do
  let mut names := env.names
  let mut classFields := env.classFields
  -- Insert procedures
  for (procName, (paramPairs, retTypeStr)) in procedures.toList do
    let params := paramPairs.map fun (pName, pType) => (pName, pythonTypeToHighType pType)
    let retTy := pythonTypeToHighType retTypeStr
    let defaults := params.map fun _ => (none : Option StmtExprMd)
    let sig : FuncSig := {
      name := procName,
      params := params,
      defaults := defaults,
      effectType := .pure retTy,
      hasKwargs := false
    }
    names := names.insert procName (.function sig)
  -- Insert composites (classes)
  for (className, fieldPairs) in composites.toList do
    let fields := fieldPairs.map fun (fName, fType) => (fName, pythonTypeToHighType fType)
    names := names.insert className (.class_ className fields)
    classFields := classFields.insert className fields
  return { names := names, classFields := classFields,
           overloadTable := env.overloadTable, builtinMap := env.builtinMap }

/-- Merge PySpec data with error output information into a TypeEnv.
    Like `mergeSpecs` but additionally marks procedures that have error outputs. -/
def TypeEnv.mergeSpecsWithErrors (env : TypeEnv)
    (procedures : Std.HashMap String (List (String × String) × String × Bool))
    (composites : Std.HashMap String (List (String × String)))
    : TypeEnv := Id.run do
  let mut names := env.names
  let mut classFields := env.classFields
  -- Insert procedures with error output info
  for (procName, (paramPairs, retTypeStr, hasError)) in procedures.toList do
    let params := paramPairs.map fun (pName, pType) => (pName, pythonTypeToHighType pType)
    let retTy := pythonTypeToHighType retTypeStr
    let defaults := params.map fun _ => (none : Option StmtExprMd)
    let sig : FuncSig := {
      name := procName,
      params := params,
      defaults := defaults,
      effectType := .pure retTy,
      hasKwargs := false
    }
    names := names.insert procName (.function sig)
  -- Insert composites (classes)
  for (className, fieldPairs) in composites.toList do
    let fields := fieldPairs.map fun (fName, fType) => (fName, pythonTypeToHighType fType)
    names := names.insert className (.class_ className fields)
    classFields := classFields.insert className fields
  return { names := names, classFields := classFields,
           overloadTable := env.overloadTable, builtinMap := env.builtinMap }

/-! ## Lookup -/

/-- Look up a name in the TypeEnv.
    Returns the NameInfo if found. Consumers pattern-match on the result. -/
def TypeEnv.lookup (env : TypeEnv) (name : String) : Option NameInfo :=
  env.names[name]?

/-- Look up a builtin mapping. Returns the Laurel procedure name for a Python builtin. -/
def TypeEnv.lookupBuiltin (env : TypeEnv) (name : String) : Option String :=
  env.builtinMap[name]?

/-- Look up an overload dispatch. Given a function name and a string argument,
    returns the resolved class name (e.g., "client" + "iam" → "IAMClient"). -/
def TypeEnv.lookupOverload (env : TypeEnv) (funcName : String) (arg : String) : Option String :=
  match env.overloadTable[funcName]? with
  | some inner => inner[arg]?
  | none => none

/-- Look up the fields of a class by name. -/
def TypeEnv.lookupClassFields (env : TypeEnv) (className : String)
    : Option (List (String × HighType)) :=
  env.classFields[className]?

/-- Get the function locals (scope-hoisted variables) for a function body.
    This is the primary scope-resolution entry point for translation. -/
def TypeEnv.getFunctionLocals (body : Array (Python.stmt SourceRange))
    (paramNames : List String) : List (String × HighType) :=
  collectFunctionLocals body paramNames

/-! ## Backward Compatibility -/

/-- Resolution environment compatible with existing translation code.
    Provides the same classification as the old `ResolvedEnv` but backed by TypeEnv. -/
structure ResolvedEnv where
  classNames : Std.HashSet String := {}
  funcNames : Std.HashSet String := {}
  deriving Inhabited

/-- A call expression after name resolution. Each variant determines exactly
    what Laurel node to emit — translation pattern-matches exhaustively. -/
inductive ResolvedCall where
  | classNew (className : String) (args : Array (Python.expr SourceRange))
      (kwargs : Array (Python.keyword SourceRange))
  | funcCall (funcName : String) (args : Array (Python.expr SourceRange))
      (kwargs : Array (Python.keyword SourceRange))
  | methodCall (receiver : Python.expr SourceRange) (methodName : String)
      (args : Array (Python.expr SourceRange))
      (kwargs : Array (Python.keyword SourceRange))

/-- Build a legacy ResolvedEnv from a TypeEnv (for backward compat with existing pipeline). -/
def TypeEnv.toResolvedEnv (env : TypeEnv) : ResolvedEnv := Id.run do
  let mut classes : Std.HashSet String := {}
  let mut funcs : Std.HashSet String := {}
  for (name, info) in env.names.toList do
    match info with
    | .class_ _ _ => classes := classes.insert name
    | .function _ => funcs := funcs.insert name
    | .variable _ => pure ()
    | .module_ _ => pure ()
  return { classNames := classes, funcNames := funcs }

/-- Build a ResolvedEnv directly from Python AST (legacy API, delegates to buildTypeEnv). -/
def buildResolvedEnv (stmts : Array (Python.stmt SourceRange)) : ResolvedEnv :=
  (buildTypeEnv stmts).toResolvedEnv

/-- Resolve a Call expression into a ResolvedCall.
    This is the single point where name classification is consulted. -/
def resolveCall (env : ResolvedEnv) (_sr : SourceRange)
    (func : Python.expr SourceRange)
    (args : Array (Python.expr SourceRange))
    (kwargs : Array (Python.keyword SourceRange))
    : ResolvedCall :=
  match func with
  | .Attribute _ receiver attr _ =>
      .methodCall receiver attr.val args kwargs
  | .Name _ name _ =>
      if env.classNames.contains name.val then
        .classNew name.val args kwargs
      else
        .funcCall name.val args kwargs
  | _ =>
      .funcCall "call" args kwargs

end -- public section
end Strata.Python.Resolution

/-! ## Re-export backward-compatible API under old namespace -/

namespace Strata.Python.New

public section

export Strata.Python.Resolution (
  ResolvedEnv ResolvedCall
  buildResolvedEnv resolveCall
)

end -- public section
end Strata.Python.New
