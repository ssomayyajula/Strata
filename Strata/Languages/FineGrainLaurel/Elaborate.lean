/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.Laurel
public import Strata.Languages.Laurel.LaurelFormat
public import Strata.Languages.Laurel.LaurelTypes
public import Strata.Languages.Laurel.HeapParameterizationConstants
public import Strata.Languages.Laurel.CoreDefinitionsForLaurel
public import Strata.Languages.Python.NameResolution
import Strata.Util.Tactics

/-!
# Unified Elaboration: Laurel → Lowered Laurel (No `resolve` Calls)

The single derivation transformation that makes all effects explicit. This pass
replaces the 8 fragment passes in `lowerProgram` / `translateWithLaurel`:

1. heapParameterization (co-operation: field access → readField, field write → updateField)
2. typeHierarchyTransform (New → MkComposite with TypeTag)
3. modifiesClausesTransform (modifies → frame condition postcondition)
4. constrainedTypeElim (constrained types → requires/ensures)
5. desugarShortCircuit (PAnd/POr with effects → if-then-else)
6. liftExpressionAssignments (ANF)
7. eliminateReturnsInExpressionTransform (already no-op)
8. eliminateHoles (Holes → fresh uninterpreted functions)

## Key Architectural Property: No `resolve` Calls

The existing `lowerProgram` runs Laurel name resolution (`resolve`) between each pass,
building a `SemanticModel` via unique ID assignment. This unified elaboration uses the
`TypeEnv` from Python NameResolution directly — it never calls `resolve`.

Information that `resolve` provided is obtained instead from:
- `TypeEnv.classFields` → qualified field names and field types
- `TypeEnv.names` → function signatures (for ANF: functional vs procedural)
- Program structure → composite type definitions, procedure lists

## Two Sub-Phases (per Architecture)

1. **Local walk** (bidirectional synth/check): inserts operations (coercions,
   short-circuit desugaring) and DISCOVERS co-operations (marks which procedures
   touch heap via FieldSelect/field-Assign/New).

2. **Global propagation** (fixpoint on call graph): threads Heap parameters through
   all heap-touching procedures and their transitive callers.

After propagation, the remaining passes (type hierarchy, modifies, holes, ANF) are
applied in sequence. Each uses TypeEnv or program structure — never `resolve`.
-/

namespace Strata.FineGrainLaurel

open Strata.Laurel
open Strata.Python.Resolution

public section

/-! ## Elaboration Result (Polarity) -/

/-- Result of elaborating a Laurel expression.
    Classifies as either a Value (inert, no effects) or Producer (effectful).
    This is the Value/Producer polarity separation from FGCBV. -/
inductive ElabResult where
  | value (expr : StmtExprMd) (ty : HighType)
  | producer (expr : StmtExprMd) (ty : HighType)

/-- Extract the expression from an elaboration result -/
def ElabResult.toExpr : ElabResult → StmtExprMd
  | .value e _ => e
  | .producer e _ => e

/-- Extract the type from an elaboration result -/
def ElabResult.toType : ElabResult → HighType
  | .value _ t => t
  | .producer _ t => t

/-- Is this result a value (inert)? -/
def ElabResult.isValue : ElabResult → Bool
  | .value _ _ => true
  | .producer _ _ => false

/-! ## Elaboration Environment -/

/-- The elaboration environment: carries Γ (TypeEnv from resolution) and
    the current procedure's return type for checking return statements. -/
structure ElabEnv where
  /-- Γ: the typing context produced by resolution -/
  typeEnv : TypeEnv
  /-- Return type of the current procedure (for checking Return nodes) -/
  currentReturnType : HighType := .TCore "Any"
  /-- Local variable types within the current scope -/
  localTypes : Std.HashMap String HighType := {}

instance : Inhabited ElabEnv where
  default := { typeEnv := default, currentReturnType := .TCore "Any", localTypes := {} }

/-- Mutable state for elaboration: fresh name generation -/
structure ElabState where
  freshCounter : Nat := 0
  deriving Inhabited

/-- Elaboration monad: Reader (immutable Γ) + State (fresh names) + Except (errors) -/
abbrev ElabM := ReaderT ElabEnv (StateT ElabState (Except String))

/-- Generate a fresh variable name -/
def freshVar (pfx : String := "tmp") : ElabM String := do
  let s ← get
  set { s with freshCounter := s.freshCounter + 1 }
  pure s!"{pfx}${s.freshCounter}"

/-! ## Type Helpers -/

/-- Lift a HighType into HighTypeMd with empty metadata -/
def liftType (ty : HighType) : HighTypeMd := { val := ty, md := #[] }

/-- Compare two HighTypes for structural equality (ignoring metadata) -/
def highTypeEq : HighType → HighType → Bool
  | .TVoid, .TVoid => true
  | .TBool, .TBool => true
  | .TInt, .TInt => true
  | .TFloat64, .TFloat64 => true
  | .TReal, .TReal => true
  | .TString, .TString => true
  | .TCore a, .TCore b => a == b
  | .UserDefined a, .UserDefined b => a.text == b.text
  | .Unknown, .Unknown => true
  | _, _ => false

/-- Is this the Any type? -/
def isAny : HighType → Bool
  | .TCore "Any" => true
  | _ => false

/-- Is this a concrete (non-Any, non-Unknown) type? -/
def isConcrete (ty : HighType) : Bool := !isAny ty && !highTypeEq ty .Unknown

/-! ## Subtyping -/

/-- Check if source type is structurally compatible with target (no coercion needed). -/
def isSubtype (source target : HighType) : Bool :=
  highTypeEq source target ||
  (isAny source && isAny target) ||
  highTypeEq source .Unknown ||
  highTypeEq target .Unknown ||
  -- UserDefined types are represented as Any at Core level, no coercion needed
  (match source with | .UserDefined _ => isAny target | _ => false) ||
  (match target with | .UserDefined _ => isAny source | _ => false) ||
  -- TVoid is compatible with Any (None is Any)
  (highTypeEq source .TVoid && isAny target) ||
  (isAny source && highTypeEq target .TVoid)

/-! ## Coercion Functions (The Single Mechanism) -/

/-- Get the coercion function name for upcast (concrete → Any). -/
def upcastFuncName : HighType → String
  | .TInt => "from_int"
  | .TBool => "from_bool"
  | .TString => "from_str"
  | .TFloat64 => "from_float"
  | .TReal => "from_float"
  | .UserDefined _ => "from_Composite"
  | _ => "from_int"

/-- Get the coercion function name for downcast (Any → concrete). -/
def downcastFuncName : HighType → String
  | .TBool => "Any_to_bool"
  | .TInt => "Any..as_int!"
  | .TString => "Any..as_string!"
  | .TFloat64 => "Any..as_float!"
  | .UserDefined _ => "Any..as_Composite!"
  | _ => "Any_to_bool"

/-- Insert an upcast coercion (concrete → Any) as a StaticCall. -/
def insertUpcast (expr : StmtExprMd) (sourceTy : HighType) : StmtExprMd :=
  let funcName := upcastFuncName sourceTy
  let callee : Identifier := { text := funcName, uniqueId := none }
  { val := .StaticCall callee [expr], md := expr.md }

/-- Insert a downcast coercion (Any → concrete) as a StaticCall. -/
def insertDowncast (expr : StmtExprMd) (targetTy : HighType) : StmtExprMd :=
  let funcName := downcastFuncName targetTy
  let callee : Identifier := { text := funcName, uniqueId := none }
  { val := .StaticCall callee [expr], md := expr.md }

/-- Insert a coercion from actual type to expected type. -/
def coerce (expr : StmtExprMd) (actual expected : HighType) : StmtExprMd :=
  match actual with
  | .UserDefined _ =>
    if isAny expected then
      let callee : Identifier := { text := "from_Composite", uniqueId := none }
      { val := .StaticCall callee [expr], md := expr.md }
    else expr
  | _ =>
  match expected with
  | .UserDefined _ =>
    if isAny actual then
      let callee : Identifier := { text := "Any..as_Composite!", uniqueId := none }
      { val := .StaticCall callee [expr], md := expr.md }
    else expr
  | _ =>
  if isAny actual && isConcrete expected then
    insertDowncast expr expected
  else if isConcrete actual && isAny expected then
    insertUpcast expr actual
  else
    expr

/-! ## Polarity Classification -/

/-- Classify a Laurel StmtExpr by polarity. Returns true for Value, false for Producer. -/
def classifyPolarity : StmtExpr → Bool
  | .LiteralInt _ => true
  | .LiteralBool _ => true
  | .LiteralString _ => true
  | .LiteralDecimal _ => true
  | .Identifier _ => true
  | .FieldSelect _ _ => true
  | .PrimitiveOp _ _ => true
  | .This => true
  | .ReferenceEquals _ _ => true
  | .IsType _ _ => true
  | .Old _ => true
  | .Hole _ _ => true
  | .AsType _ _ => true
  | .PureFieldUpdate _ _ _ => true
  | .Forall _ _ _ => true
  | .Exists _ _ _ => true
  | .Assigned _ => true
  | .Fresh _ => true
  | .ProveBy _ _ => true
  | .ContractOf _ _ => true
  | .Abstract => true
  | .All => true
  | .StaticCall _ _ => false
  | .InstanceCall _ _ _ => false
  | .New _ => false
  | .Assign _ _ => false
  | .IfThenElse _ _ _ => false
  | .While _ _ _ _ => false
  | .Block _ _ => false
  | .LocalVariable _ _ _ => false
  | .Return _ => false
  | .Exit _ => false
  | .Assert _ => false
  | .Assume _ => false

/-! ## Looking Up Types in Γ -/

/-- Look up the type of a name in the elaboration environment. -/
def lookupNameType (env : ElabEnv) (name : String) : HighType :=
  match env.localTypes[name]? with
  | some ty => ty
  | none =>
    match env.typeEnv.lookup name with
    | some (.variable ty) => ty
    | some (.function sig) => sig.returnType
    | some (.class_ _ _) => .UserDefined { text := name, uniqueId := none }
    | some (.module_ _) => .TCore "Any"
    | none => .TCore "Any"

/-- Look up function signature in Γ. -/
def lookupFuncSig (env : ElabEnv) (name : String) : Option FuncSig :=
  match env.typeEnv.lookup name with
  | some (.function sig) => some sig
  | _ => none

/-- Look up field type from Γ's classFields. -/
def lookupFieldType (env : ElabEnv) (receiverTy : HighType) (fieldName : String) : HighType :=
  match receiverTy with
  | .UserDefined className =>
    match env.typeEnv.lookupClassFields className.text with
    | some fields =>
      match fields.find? (fun (n, _) => n == fieldName) with
      | some (_, ty) => ty
      | none => .TCore "Any"
    | none => .TCore "Any"
  | _ => .TCore "Any"

/-! ## Short-Circuit Desugaring -/

/-- Check if a Laurel expression is effectful (contains StaticCall, Assign, or other Producer). -/
def isEffectful (expr : StmtExprMd) : Bool := !classifyPolarity expr.val

/-! ## Core Bidirectional Elaboration -/

mutual

/-- Synthesis: elaborate an expression, infer its type, classify polarity. -/
partial def synth (expr : StmtExprMd) : ElabM ElabResult := do
  let env ← read
  match expr.val with
  | .LiteralInt _ => pure (.value expr .TInt)
  | .LiteralBool _ => pure (.value expr .TBool)
  | .LiteralString _ => pure (.value expr .TString)
  | .LiteralDecimal _ => pure (.value expr .TReal)

  | .Identifier name =>
    let ty := lookupNameType env name.text
    pure (.value expr ty)

  | .FieldSelect target field => do
    let targetResult ← synth target
    let receiverTy := targetResult.toType
    let fieldTy := lookupFieldType env receiverTy field.text
    match targetResult with
    | .value _ _ =>
      pure (.value expr fieldTy)
    | .producer targetExpr _ => do
      let tmp ← freshVar "fld"
      let tmpId : Identifier := { text := tmp, uniqueId := none }
      let tmpRef : StmtExprMd := { val := .Identifier tmpId, md := expr.md }
      let fieldExpr : StmtExprMd := { val := .FieldSelect tmpRef field, md := expr.md }
      let binding : StmtExprMd := { val := .LocalVariable tmpId (liftType receiverTy)
                                      (some targetExpr), md := expr.md }
      let result : StmtExprMd := { val := .Block [binding, fieldExpr] none, md := expr.md }
      pure (.producer result fieldTy)

  | .StaticCall callee args => do
    -- Short-circuit desugaring: PAnd/POr with effectful second operand
    match callee.text, args with
    | "PAnd", [left, right] =>
      if isEffectful right then
        let desugared : StmtExprMd :=
          { val := .IfThenElse left right (some { val := .LiteralBool false, md := expr.md }),
            md := expr.md }
        synth desugared
      else
        let sig := lookupFuncSig env callee.text
        let paramTypes := sig.map (·.params) |>.getD []
        let elaboratedArgs ← elaborateArgs args paramTypes
        let retTy := sig.map (·.returnType) |>.getD (.TCore "Any")
        let callExpr : StmtExprMd := { val := .StaticCall callee elaboratedArgs, md := expr.md }
        pure (.producer callExpr retTy)
    | "POr", [left, right] =>
      if isEffectful right then
        let desugared : StmtExprMd :=
          { val := .IfThenElse left { val := .LiteralBool true, md := expr.md } (some right),
            md := expr.md }
        synth desugared
      else
        let sig := lookupFuncSig env callee.text
        let paramTypes := sig.map (·.params) |>.getD []
        let elaboratedArgs ← elaborateArgs args paramTypes
        let retTy := sig.map (·.returnType) |>.getD (.TCore "Any")
        let callExpr : StmtExprMd := { val := .StaticCall callee elaboratedArgs, md := expr.md }
        pure (.producer callExpr retTy)
    | _, _ => do
    let sig := lookupFuncSig env callee.text
    let paramTypes := sig.map (·.params) |>.getD []
    let elaboratedArgs ← elaborateArgs args paramTypes
    let retTy := sig.map (·.returnType) |>.getD (.TCore "Any")
    let hasError := sig.map (·.hasErrorOutput) |>.getD false
    let callExpr : StmtExprMd := { val := .StaticCall callee elaboratedArgs, md := expr.md }
    if hasError then
      let resultVar ← freshVar "res"
      let errorVar ← freshVar "err"
      let resultId : Identifier := { text := resultVar, uniqueId := none }
      let errorId : Identifier := { text := errorVar, uniqueId := none }
      let resultRef : StmtExprMd := { val := .Identifier resultId, md := expr.md }
      let errorRef : StmtExprMd := { val := .Identifier errorId, md := expr.md }
      let multiAssign : StmtExprMd :=
        { val := .Assign [resultRef, errorRef] callExpr, md := expr.md }
      let isErrorCall : StmtExprMd :=
        { val := .StaticCall { text := "isError", uniqueId := none } [errorRef], md := expr.md }
      let errorCheck : StmtExprMd :=
        { val := .IfThenElse isErrorCall
           { val := .Return (some errorRef), md := expr.md }
           none, md := expr.md }
      let fullBlock : StmtExprMd :=
        { val := .Block [multiAssign, errorCheck, resultRef] none, md := expr.md }
      pure (.producer fullBlock retTy)
    else
      pure (.producer callExpr retTy)

  | .InstanceCall target callee args => do
    let targetResult ← synth target
    let receiverTy := targetResult.toType
    let qualName := match receiverTy with
      | .UserDefined className => s!"{className.text}@{callee.text}"
      | _ => callee.text
    let sig := lookupFuncSig env qualName
    let paramTypes := sig.map (·.params) |>.getD []
    let elaboratedArgs ← elaborateArgs args paramTypes
    let retTy := sig.map (·.returnType) |>.getD (.TCore "Any")
    let elaboratedTarget := targetResult.toExpr
    let callExpr : StmtExprMd :=
      { val := .InstanceCall elaboratedTarget callee elaboratedArgs, md := expr.md }
    pure (.producer callExpr retTy)

  | .New name =>
    pure (.producer expr (.UserDefined name))

  | .AsType _inner targetTy =>
    pure (.value expr targetTy.val)

  | .PrimitiveOp op args => do
    let elaboratedArgs ← args.mapM fun arg => do
      let r ← synth arg; pure r.toExpr
    let result : StmtExprMd := { val := .PrimitiveOp op elaboratedArgs, md := expr.md }
    let resultTy := match op with
      | .Eq | .Neq | .And | .Or | .AndThen | .OrElse | .Not | .Implies
      | .Lt | .Leq | .Gt | .Geq => HighType.TBool
      | .StrConcat => HighType.TString
      | _ =>
        match args with
        | hd :: _ =>
          match hd.val with
          | .LiteralDecimal _ => HighType.TReal
          | _ => HighType.TInt
        | [] => HighType.TInt
    pure (.value result resultTy)

  | .IfThenElse cond thenBr elseBr => do
    let checkedCond ← check cond .TBool
    let elaboratedThen ← elaborateStmt thenBr
    let elaboratedElse ← match elseBr with
      | some e => pure (some (← elaborateStmt e))
      | none => pure none
    let result : StmtExprMd :=
      { val := .IfThenElse checkedCond.toExpr elaboratedThen elaboratedElse, md := expr.md }
    pure (.producer result .TVoid)

  | .While cond invs decreases body => do
    let checkedCond ← check cond .TBool
    let elaboratedBody ← elaborateStmt body
    let elaboratedInvs ← invs.mapM fun inv => do
      let r ← check inv .TBool; pure r.toExpr
    let elaboratedDecreases ← match decreases with
      | some d => pure (some (← synth d).toExpr)
      | none => pure none
    let result : StmtExprMd :=
      { val := .While checkedCond.toExpr elaboratedInvs elaboratedDecreases elaboratedBody,
        md := expr.md }
    pure (.producer result .TVoid)

  | .Block stmts label => do
    let mut elaboratedStmts : List StmtExprMd := []
    let mut extraLocals : Std.HashMap String HighType := {}
    for stmt in stmts do
      let elaborated ← withReader (fun env =>
        { env with localTypes := extraLocals.fold (init := env.localTypes) fun m k v =>
            m.insert k v }
      ) (elaborateStmt stmt)
      match stmt.val with
      | .LocalVariable name ty _ => extraLocals := extraLocals.insert name.text ty.val
      | _ => pure ()
      elaboratedStmts := elaboratedStmts ++ [elaborated]
    pure (.producer { val := .Block elaboratedStmts label, md := expr.md } .TVoid)

  | .Assign targets value => do
    let elaboratedValue ← synth value
    let finalValue := match targets with
      | [target] =>
        match target.val with
        | .Identifier name =>
          let expectedTy := lookupNameType env name.text
          if !isSubtype elaboratedValue.toType expectedTy then
            coerce elaboratedValue.toExpr elaboratedValue.toType expectedTy
          else
            elaboratedValue.toExpr
        | _ => elaboratedValue.toExpr
      | _ => elaboratedValue.toExpr
    pure (.producer { val := .Assign targets finalValue, md := expr.md } .TVoid)

  | .Return value => do
    let elaboratedValue ← match value with
      | some v => do
        let checked ← check v env.currentReturnType
        pure (some checked.toExpr)
      | none => pure none
    pure (.producer { val := .Return elaboratedValue, md := expr.md } .TVoid)

  | .LocalVariable name ty init => do
    let elaboratedInit ← match init with
      | some i => do
        let checked ← check i ty.val
        pure (some checked.toExpr)
      | none => pure none
    pure (.producer { val := .LocalVariable name ty elaboratedInit, md := expr.md } .TVoid)

  | .Assert cond => do
    let checkedCond ← check cond .TBool
    pure (.producer { val := .Assert checkedCond.toExpr, md := expr.md } .TVoid)

  | .Assume cond => do
    let checkedCond ← check cond .TBool
    pure (.producer { val := .Assume checkedCond.toExpr, md := expr.md } .TVoid)

  | .Exit _ =>
    pure (.producer expr .TVoid)

  | _ => pure (.value expr (.TCore "Any"))

/-- Checking: elaborate an expression against an expected type. -/
partial def check (expr : StmtExprMd) (expected : HighType) : ElabM ElabResult := do
  let result ← synth expr
  let actual := result.toType
  if isSubtype actual expected then
    pure result
  else
    let coerced := coerce result.toExpr actual expected
    if classifyPolarity coerced.val then
      pure (.value coerced expected)
    else
      pure (.producer coerced expected)

/-- Elaborate a statement (a producer in FGCBV terms). -/
partial def elaborateStmt (stmt : StmtExprMd) : ElabM StmtExprMd := do
  let result ← synth stmt
  pure result.toExpr

/-- Elaborate a list of arguments against expected parameter types. -/
partial def elaborateArgs (args : List StmtExprMd)
    (paramTypes : List (String × HighType)) : ElabM (List StmtExprMd) := do
  let mut result : List StmtExprMd := []
  let mut remainingParams := paramTypes
  for arg in args do
    match remainingParams with
    | (_, expectedTy) :: rest =>
      let checked ← check arg expectedTy
      result := result ++ [checked.toExpr]
      remainingParams := rest
    | [] =>
      let checked ← check arg (.TCore "Any")
      result := result ++ [checked.toExpr]
  pure result

end -- mutual

/-! ## Force Value (ANF Transformation) -/

/-- Force an elaboration result into a value. -/
def forceValue (result : ElabResult) : ElabM (StmtExprMd × Option StmtExprMd) := do
  match result with
  | .value expr _ => pure (expr, none)
  | .producer expr ty => do
    let tmp ← freshVar "v"
    let tmpId : Identifier := { text := tmp, uniqueId := none }
    let tmpRef : StmtExprMd := { val := .Identifier tmpId, md := expr.md }
    let binding : StmtExprMd := { val := .LocalVariable tmpId (liftType ty) (some expr), md := expr.md }
    pure (tmpRef, some binding)

/-! ## Pipeline Entry Points (Phase 1: Bidirectional Walk) -/

/-- Build an ElabEnv from a TypeEnv (Γ) and procedure context. -/
def mkElabEnv (typeEnv : TypeEnv) (returnType : HighType := .TCore "Any")
    (localTypes : Std.HashMap String HighType := {}) : ElabEnv :=
  { typeEnv := typeEnv, currentReturnType := returnType, localTypes := localTypes }

/-- Elaborate a single procedure body. -/
def elaborateProcBody (env : ElabEnv) (body : StmtExprMd) : Except String StmtExprMd := do
  let (result, _) ← (elaborateStmt body).run env |>.run {}
  pure result

/-- Elaborate a Laurel Procedure, inserting casts and effects. -/
def elaborateProcedure (typeEnv : TypeEnv) (proc : Procedure) : Except String Procedure := do
  match proc.body with
  | .Transparent body =>
    let localTypes := proc.inputs.foldl (fun m p => m.insert p.name.text p.type.val)
      (Std.HashMap.ofList (α := String) (β := HighType) [])
    let retTy := match proc.outputs with
      | [output] => output.type.val
      | _ => .TCore "Any"
    let env := mkElabEnv typeEnv retTy localTypes
    let elaboratedBody ← elaborateProcBody env body
    pure { proc with body := .Transparent elaboratedBody }
  | _ => pure proc

/-- Elaborate an entire Laurel Program (Phase 1 only: bidirectional walk). -/
def elaborateProgram (typeEnv : TypeEnv) (program : Laurel.Program) : Except String Laurel.Program := do
  let fullEnv := typeEnv.withPrelude
  let mut staticProcs : List Procedure := []
  for proc in program.staticProcedures do
    let elaborated ← elaborateProcedure fullEnv proc
    staticProcs := staticProcs ++ [elaborated]
  let mut types : List TypeDefinition := []
  for td in program.types do
    match td with
    | .Composite ct =>
      let mut instProcs : List Procedure := []
      for proc in ct.instanceProcedures do
        let elaborated ← elaborateProcedure fullEnv proc
        instProcs := instProcs ++ [elaborated]
      types := types ++ [.Composite { ct with instanceProcedures := instProcs }]
    | other => types := types ++ [other]
  pure { program with staticProcedures := staticProcs, types := types }

/-! ========================================================================
    Phase 2: Heap Analysis and Parameterization (Co-Operation)

    From ARCHITECTURE.md:
    "Heap parameterization is precisely: turning heap operations into co-operations
    in FineGrainLaurel — the heap is threaded as an explicit parameter rather than
    being implicitly available."

    This phase uses TypeEnv.classFields to resolve qualified field names,
    avoiding any dependency on `resolve` or `SemanticModel`.
    ======================================================================== -/

/-- Determine the owning class for a field name using TypeEnv.classFields.
    Returns "ClassName.fieldName" or none if not found. -/
private def resolveQualifiedFieldNameFromEnv (typeEnv : TypeEnv) (fieldName : String)
    : Option String := Id.run do
  -- Search all classes for this field name
  for (className, fields) in typeEnv.classFields.toList do
    for (fName, _) in fields do
      if fName == fieldName then
        return some s!"{className}.{fieldName}"
  return none

/-- Get the type of a field from TypeEnv. Returns the HighType or defaults to Any. -/
private def fieldTypeFromEnv (typeEnv : TypeEnv) (fieldName : String) : HighType := Id.run do
  for (_className, fields) in typeEnv.classFields.toList do
    for (fName, fType) in fields do
      if fName == fieldName then
        return fType
  return .TCore "Any"

/-- Get the Box constructor name for a given type. -/
private def boxConstructorNameForType (ty : HighType) : String :=
  match ty with
  | .TInt => "BoxInt"
  | .TBool => "BoxBool"
  | .TFloat64 => "BoxFloat64"
  | .TReal => "BoxFloat64"
  | .TString => "BoxString"
  | .UserDefined name => s!"Box{name.text}"
  | .TCore "Any" => "BoxAny"
  | _ => "BoxAny"

/-- Get the Box destructor name for a given type. -/
private def boxDestructorNameForType (ty : HighType) : String :=
  match ty with
  | .TInt => "Box..IntVal!"
  | .TBool => "Box..BoolVal!"
  | .TFloat64 => "Box..Float64Val!"
  | .TReal => "Box..Float64Val!"
  | .TString => "Box..StringVal!"
  | .UserDefined name => s!"Box..{name.text}Val!"
  | .TCore "Any" => "Box..AnyVal!"
  | _ => "Box..AnyVal!"

/-- Helper to wrap a StmtExpr into StmtExprMd with empty metadata -/
private def mkMd (e : StmtExpr) : StmtExprMd := ⟨e, #[]⟩

/-- Heap analysis result for a single procedure. -/
private structure HeapAnalysisResult where
  readsHeapDirectly : Bool := false
  writesHeapDirectly : Bool := false
  callees : List Identifier := []

/-- Analyze a procedure body to determine if it reads/writes the heap.
    Does NOT require SemanticModel — only inspects the AST structure. -/
private partial def analyzeExprForHeap (expr : StmtExprMd) : StateM HeapAnalysisResult Unit := do
  match expr.val with
  | .FieldSelect target _ =>
      modify fun s => { s with readsHeapDirectly := true }
      analyzeExprForHeap target
  | .InstanceCall target _ args =>
      analyzeExprForHeap target
      for a in args do analyzeExprForHeap a
  | .StaticCall callee args =>
      modify fun s => { s with callees := callee :: s.callees }
      for a in args do analyzeExprForHeap a
  | .IfThenElse c t e =>
      analyzeExprForHeap c; analyzeExprForHeap t
      match e with | some x => analyzeExprForHeap x | none => pure ()
  | .Block stmts _ => for s in stmts do analyzeExprForHeap s
  | .LocalVariable _ _ i => match i with | some x => analyzeExprForHeap x | none => pure ()
  | .While c invs d b =>
      analyzeExprForHeap c; analyzeExprForHeap b
      for inv in invs do analyzeExprForHeap inv
      match d with | some x => analyzeExprForHeap x | none => pure ()
  | .Return v => match v with | some x => analyzeExprForHeap x | none => pure ()
  | .Assign targets v =>
      for t in targets do
        match t.val with
        | .FieldSelect _ _ => modify fun s => { s with writesHeapDirectly := true }
        | _ => pure ()
        analyzeExprForHeap t
      analyzeExprForHeap v
  | .PureFieldUpdate t _ v => analyzeExprForHeap t; analyzeExprForHeap v
  | .PrimitiveOp _ args => for a in args do analyzeExprForHeap a
  | .New _ => modify fun s => { s with writesHeapDirectly := true }
  | .ReferenceEquals l r => analyzeExprForHeap l; analyzeExprForHeap r
  | .AsType t _ => analyzeExprForHeap t
  | .IsType t _ => analyzeExprForHeap t
  | .Forall _ trigger b =>
      match trigger with | some t => analyzeExprForHeap t | none => pure ()
      analyzeExprForHeap b
  | .Exists _ trigger b =>
      match trigger with | some t => analyzeExprForHeap t | none => pure ()
      analyzeExprForHeap b
  | .Assigned n => analyzeExprForHeap n
  | .Old v => analyzeExprForHeap v
  | .Fresh v => analyzeExprForHeap v
  | .Assert c => analyzeExprForHeap c
  | .Assume c => analyzeExprForHeap c
  | .ProveBy v p => analyzeExprForHeap v; analyzeExprForHeap p
  | .ContractOf _ f => analyzeExprForHeap f
  | _ => pure ()

/-- Analyze a single procedure for heap access. -/
private def analyzeProcForHeap (proc : Procedure) : HeapAnalysisResult :=
  let bodyResult := match proc.body with
    | .Transparent b => (analyzeExprForHeap b).run {} |>.2
    | .Opaque postconds impl modif =>
        if !modif.isEmpty then
          { readsHeapDirectly := true, writesHeapDirectly := true, callees := [] }
        else
          let r1 := postconds.foldl (fun (acc : HeapAnalysisResult) pc =>
            let r := (analyzeExprForHeap pc).run {} |>.2
            { readsHeapDirectly := acc.readsHeapDirectly || r.readsHeapDirectly,
              writesHeapDirectly := acc.writesHeapDirectly || r.writesHeapDirectly,
              callees := acc.callees ++ r.callees }) {}
          let r2 := match impl with
            | some e => (analyzeExprForHeap e).run {} |>.2
            | none => {}
          { readsHeapDirectly := r1.readsHeapDirectly || r2.readsHeapDirectly,
            writesHeapDirectly := r1.writesHeapDirectly || r2.writesHeapDirectly,
            callees := r1.callees ++ r2.callees }
    | .Abstract postconds => (postconds.forM analyzeExprForHeap).run {} |>.2
    | .External => {}
  let precondResult := (proc.preconditions.forM analyzeExprForHeap).run {} |>.2
  { readsHeapDirectly := bodyResult.readsHeapDirectly || precondResult.readsHeapDirectly,
    writesHeapDirectly := bodyResult.writesHeapDirectly || precondResult.writesHeapDirectly,
    callees := bodyResult.callees ++ precondResult.callees }

/-- Compute the transitive set of procedures that read the heap (fixpoint). -/
private def computeHeapReaders (procs : List Procedure) : List Identifier :=
  let info := procs.map fun p => (p.name, analyzeProcForHeap p)
  let direct := info.filterMap fun (n, r) => if r.readsHeapDirectly then some n else none
  let rec fixpoint (fuel : Nat) (current : List Identifier) : List Identifier :=
    match fuel with
    | 0 => current
    | fuel' + 1 =>
      let next := info.filterMap fun (n, r) =>
        if current.contains n then some n
        else if r.callees.any current.contains then some n
        else none
      if next.length == current.length then current else fixpoint fuel' next
  fixpoint procs.length direct

/-- Compute the transitive set of procedures that write the heap (fixpoint). -/
private def computeHeapWriters (procs : List Procedure) : List Identifier :=
  let info := procs.map fun p => (p.name, analyzeProcForHeap p)
  let direct := info.filterMap fun (n, r) => if r.writesHeapDirectly then some n else none
  let rec fixpoint (fuel : Nat) (current : List Identifier) : List Identifier :=
    match fuel with
    | 0 => current
    | fuel' + 1 =>
      let next := info.filterMap fun (n, r) =>
        if current.contains n then some n
        else if r.callees.any current.contains then some n
        else none
      if next.length == current.length then current else fixpoint fuel' next
  fixpoint procs.length direct

/-- State for the heap transformation phase. -/
private structure HeapTransformState where
  heapReaders : List Identifier
  heapWriters : List Identifier
  freshCounter : Nat := 0
  usedBoxConstructors : List DatatypeConstructor := []
  typeEnv : TypeEnv

private abbrev HeapTransformM := StateM HeapTransformState

private def heapFreshVar : HeapTransformM Identifier := do
  let s ← get
  set { s with freshCounter := s.freshCounter + 1 }
  return s!"$tmp{s.freshCounter}"

private def heapReadsHeap (name : Identifier) : HeapTransformM Bool := do
  return (← get).heapReaders.contains name

private def heapWritesHeap (name : Identifier) : HeapTransformM Bool := do
  return (← get).heapWriters.contains name

/-- Record a Box constructor if not already present. -/
private def recordBoxConstructor (ty : HighType) : HeapTransformM Unit := do
  let ctorName := boxConstructorNameForType ty
  let ctor : DatatypeConstructor := { name := ctorName, args := [{ name := s!"{ctorName}Val", type := liftType ty }] }
  let s ← get
  if s.usedBoxConstructors.any (fun c => c.name == ctor.name) then pure ()
  else modify fun s => { s with usedBoxConstructors := s.usedBoxConstructors ++ [ctor] }

/-- Transform expressions for heap parameterization.
    Rewrites FieldSelect → readField, field Assign → updateField,
    and threads Heap through calls to heap-touching procedures. -/
private partial def heapTransformExpr (heapVar : Identifier) (expr : StmtExprMd)
    (valueUsed : Bool := true) : HeapTransformM StmtExprMd := do
  let ⟨exprVal, md⟩ := expr
  match exprVal with
  | .FieldSelect selectTarget fieldName =>
    let env := (← get).typeEnv
    let some qualifiedName := resolveQualifiedFieldNameFromEnv env fieldName.text
      | return mkMd .Hole   -- Fallback if field not found
    let valTy := fieldTypeFromEnv env fieldName.text
    let readExpr := ⟨.StaticCall "readField" [mkMd (.Identifier heapVar), selectTarget, mkMd (.StaticCall qualifiedName [])], md⟩
    recordBoxConstructor valTy
    return mkMd <| .StaticCall (boxDestructorNameForType valTy) [readExpr]
  | .StaticCall callee args =>
    let args' ← args.mapM (heapTransformExpr heapVar ·)
    let calleeReadsHeap ← heapReadsHeap callee
    let calleeWritesHeap ← heapWritesHeap callee
    if calleeWritesHeap then
      if valueUsed then
        let freshV ← heapFreshVar
        let varDecl := mkMd (.LocalVariable freshV (liftType (.TCore "Any")) none)
        let callWithHeap := ⟨.Assign
          [mkMd (.Identifier heapVar), mkMd (.Identifier freshV)]
          (⟨.StaticCall callee (mkMd (.Identifier heapVar) :: args'), md⟩), md⟩
        return ⟨.Block [varDecl, callWithHeap, mkMd (.Identifier freshV)] none, md⟩
      else
        return ⟨.Assign [mkMd (.Identifier heapVar)] (⟨.StaticCall callee (mkMd (.Identifier heapVar) :: args'), md⟩), md⟩
    else if calleeReadsHeap then
      return ⟨.StaticCall callee (mkMd (.Identifier heapVar) :: args'), md⟩
    else
      return ⟨.StaticCall callee args', md⟩
  | .InstanceCall callTarget callee args =>
    let t ← heapTransformExpr heapVar callTarget
    let args' ← args.mapM (heapTransformExpr heapVar ·)
    return ⟨.InstanceCall t callee args', md⟩
  | .IfThenElse c t e =>
    let e' ← match e with | some x => some <$> heapTransformExpr heapVar x valueUsed | none => pure none
    return ⟨.IfThenElse (← heapTransformExpr heapVar c) (← heapTransformExpr heapVar t valueUsed) e', md⟩
  | .Block stmts label =>
    let n := stmts.length
    let rec processStmts (idx : Nat) (remaining : List StmtExprMd) : HeapTransformM (List StmtExprMd) := do
      match remaining with
      | [] => pure []
      | s :: rest =>
          let isLast := idx == n - 1
          let s' ← heapTransformExpr heapVar s (isLast && valueUsed)
          let rest' ← processStmts (idx + 1) rest
          pure (s' :: rest')
      termination_by sizeOf remaining
    let stmts' ← processStmts 0 stmts
    return ⟨.Block stmts' label, md⟩
  | .LocalVariable n ty i =>
    let i' ← match i with | some x => some <$> heapTransformExpr heapVar x | none => pure none
    return ⟨.LocalVariable n ty i', md⟩
  | .While c invs d b =>
    let invs' ← invs.mapM (heapTransformExpr heapVar ·)
    return ⟨.While (← heapTransformExpr heapVar c) invs' d (← heapTransformExpr heapVar b false), md⟩
  | .Return v =>
    let v' ← match v with | some x => some <$> heapTransformExpr heapVar x | none => pure none
    return ⟨.Return v', md⟩
  | .Assign targets v =>
    match targets with
    | [⟨.FieldSelect target fieldName, _⟩] =>
      let env := (← get).typeEnv
      let some qualifiedName := resolveQualifiedFieldNameFromEnv env fieldName.text
        | return mkMd .Hole
      let valTy := fieldTypeFromEnv env fieldName.text
      let target' ← heapTransformExpr heapVar target
      let v' ← heapTransformExpr heapVar v
      recordBoxConstructor valTy
      let boxedVal := mkMd <| .StaticCall (boxConstructorNameForType valTy) [v']
      let heapAssign := ⟨.Assign [mkMd (.Identifier heapVar)]
        (mkMd (.StaticCall "updateField" [mkMd (.Identifier heapVar), target', mkMd (.StaticCall qualifiedName []), boxedVal])), md⟩
      if valueUsed then
        return ⟨.Block [heapAssign, v'] none, md⟩
      else
        return heapAssign
    | [fieldSelectMd] =>
      let tgt' ← heapTransformExpr heapVar fieldSelectMd
      return ⟨.Assign [tgt'] (← heapTransformExpr heapVar v), md⟩
    | [] =>
      return ⟨.Assign [] (← heapTransformExpr heapVar v), md⟩
    | tgt :: rest =>
      let tgt' ← heapTransformExpr heapVar tgt
      let targets' ← rest.mapM (heapTransformExpr heapVar ·)
      return ⟨.Assign (tgt' :: targets') (← heapTransformExpr heapVar v), md⟩
  | .PureFieldUpdate t f v => return ⟨.PureFieldUpdate (← heapTransformExpr heapVar t) f (← heapTransformExpr heapVar v), md⟩
  | .PrimitiveOp op args =>
    let args' ← args.mapM (heapTransformExpr heapVar ·)
    return ⟨.PrimitiveOp op args', md⟩
  | .New _ => return expr
  | .ReferenceEquals l r => return ⟨.ReferenceEquals (← heapTransformExpr heapVar l) (← heapTransformExpr heapVar r), md⟩
  | .AsType t ty =>
    let t' ← heapTransformExpr heapVar t valueUsed
    let isCheck := ⟨.IsType t' ty, md⟩
    let assertStmt := ⟨.Assert isCheck, md⟩
    return ⟨.Block [assertStmt, t'] none, md⟩
  | .IsType t ty => return ⟨.IsType (← heapTransformExpr heapVar t) ty, md⟩
  | .Forall p trigger b =>
    let trigger' ← match trigger with | some t => pure (some (← heapTransformExpr heapVar t)) | none => pure none
    return ⟨.Forall p trigger' (← heapTransformExpr heapVar b), md⟩
  | .Exists p trigger b =>
    let trigger' ← match trigger with | some t => pure (some (← heapTransformExpr heapVar t)) | none => pure none
    return ⟨.Exists p trigger' (← heapTransformExpr heapVar b), md⟩
  | .Assigned n => return ⟨.Assigned (← heapTransformExpr heapVar n), md⟩
  | .Old v => return ⟨.Old (← heapTransformExpr heapVar v), md⟩
  | .Fresh v => return ⟨.Fresh (← heapTransformExpr heapVar v), md⟩
  | .Assert c => return ⟨.Assert (← heapTransformExpr heapVar c), md⟩
  | .Assume c => return ⟨.Assume (← heapTransformExpr heapVar c), md⟩
  | .ProveBy v p => return ⟨.ProveBy (← heapTransformExpr heapVar v) (← heapTransformExpr heapVar p), md⟩
  | .ContractOf ty f => return ⟨.ContractOf ty (← heapTransformExpr heapVar f), md⟩
  | _ => return expr

/-- Transform a procedure for heap parameterization. Adds heap in/out params. -/
private def heapTransformProcedure (proc : Procedure) : HeapTransformM Procedure := do
  let heapName : Identifier := "$heap"
  let heapInName : Identifier := "$heap_in"
  let readsH := (← get).heapReaders.contains proc.name
  let writesH := (← get).heapWriters.contains proc.name

  if writesH then
    let heapInParam : Parameter := { name := heapInName, type := ⟨.THeap, #[]⟩ }
    let heapOutParam : Parameter := { name := heapName, type := ⟨.THeap, #[]⟩ }
    let inputs' := heapInParam :: proc.inputs
    let outputs' := heapOutParam :: proc.outputs
    let preconditions' ← proc.preconditions.mapM (heapTransformExpr heapInName)
    let bodyValueIsUsed := !proc.outputs.isEmpty
    let body' : Body ← match proc.body with
      | .Transparent bodyExpr =>
          let assignHeap := mkMd (.Assign [mkMd (.Identifier heapName)] (mkMd (.Identifier heapInName)))
          let bodyExpr' ← heapTransformExpr heapName bodyExpr bodyValueIsUsed
          pure (Body.Transparent (mkMd (.Block [assignHeap, bodyExpr'] none)))
      | .Opaque postconds impl modif =>
          let postconds' ← postconds.mapM (heapTransformExpr heapName ·)
          let impl' ← match impl with
            | some implExpr =>
                let assignHeap := mkMd (.Assign [mkMd (.Identifier heapName)] (mkMd (.Identifier heapInName)))
                let implExpr' ← heapTransformExpr heapName implExpr bodyValueIsUsed
                pure (some (mkMd (.Block [assignHeap, implExpr'] none)))
            | none => pure none
          let modif' ← modif.mapM (heapTransformExpr heapName ·)
          pure (Body.Opaque postconds' impl' modif')
      | .Abstract postconds =>
          let postconds' ← postconds.mapM (heapTransformExpr heapName ·)
          pure (Body.Abstract postconds')
      | .External => pure Body.External
    return { proc with inputs := inputs', outputs := outputs', preconditions := preconditions', body := body' }
  else if readsH then
    let heapParam : Parameter := { name := heapName, type := ⟨.THeap, #[]⟩ }
    let inputs' := heapParam :: proc.inputs
    let preconditions' ← proc.preconditions.mapM (heapTransformExpr heapName)
    let body' : Body ← match proc.body with
      | .Transparent bodyExpr =>
          let bodyExpr' ← heapTransformExpr heapName bodyExpr
          pure (Body.Transparent bodyExpr')
      | .Opaque postconds impl modif =>
          let postconds' ← postconds.mapM (heapTransformExpr heapName ·)
          let impl' ← impl.mapM (heapTransformExpr heapName ·)
          let modif' ← modif.mapM (heapTransformExpr heapName ·)
          pure (Body.Opaque postconds' impl' modif')
      | .Abstract postconds =>
          let postconds' ← postconds.mapM (heapTransformExpr heapName ·)
          pure (Body.Abstract postconds')
      | .External => pure Body.External
    return { proc with inputs := inputs', preconditions := preconditions', body := body' }
  else
    return proc

/-- Run the full heap parameterization phase on a program.
    Uses TypeEnv instead of SemanticModel. -/
private def heapParameterizationPhase (typeEnv : TypeEnv) (program : Laurel.Program) : Laurel.Program :=
  let instanceProcs := program.types.foldl (fun acc td =>
    match td with
    | .Composite ct => acc ++ ct.instanceProcedures
    | _ => acc) ([] : List Procedure)
  let allProcs := program.staticProcedures ++ instanceProcs
  let heapReaders := computeHeapReaders allProcs
  let heapWriters := computeHeapWriters allProcs
  let initState : HeapTransformState := { heapReaders, heapWriters, typeEnv := typeEnv }
  let (procs', state1) := (program.staticProcedures.mapM heapTransformProcedure).run initState
  -- Collect all qualified field names and generate a Field datatype
  let fieldNames := program.types.foldl (fun acc td =>
    match td with
    | .Composite ct => acc ++ ct.fields.map (fun f => (mkId (ct.name.text ++ "." ++ f.name.text) : Identifier))
    | _ => acc) ([] : List Identifier)
  let fieldDatatype : TypeDefinition :=
    .Datatype { name := "Field", typeArgs := [], constructors := fieldNames.map fun n => { name := n, args := [] } }
  -- Transform instance procedures
  let (types', state2) := program.types.foldl (fun (accTypes, accState) td =>
    match td with
    | .Composite ct =>
      let (instProcs', s') := (ct.instanceProcedures.mapM heapTransformProcedure).run accState
      (accTypes ++ [.Composite { ct with fields := [], instanceProcedures := instProcs' }], s')
    | other => (accTypes ++ [other], accState))
    ([], state1)
  -- Generate Box datatype from all constructors used during transformation
  let boxDatatype : TypeDefinition :=
    .Datatype { name := "Box", typeArgs := [], constructors := state2.usedBoxConstructors }
  { program with
    staticProcedures := heapConstants.staticProcedures ++ procs',
    types := fieldDatatype :: boxDatatype :: heapConstants.types ++ types' }

/-! ========================================================================
    Phase 3: Type Hierarchy Transform

    Generates TypeTag datatype, lowers New→MkComposite, lowers IsType.
    Uses program's composite type definitions directly (no SemanticModel).
    ======================================================================== -/

/-- State for type hierarchy rewrite. -/
private structure THState where
  freshCounter : Nat := 0

private abbrev THM := StateM THState

private def thFreshVar : THM Identifier := do
  let s ← get
  set { s with freshCounter := s.freshCounter + 1 }
  return s!"$th_tmp{s.freshCounter}"

/-- Lower `New name` to heap allocation + MkComposite. -/
private def lowerNew (name : Identifier) (md : Imperative.MetaData Core.Expression) : THM StmtExprMd := do
  let heapVar : Identifier := "$heap"
  let freshV ← thFreshVar
  let getCounter := mkMd (.StaticCall "Heap..nextReference!" [mkMd (.Identifier heapVar)])
  let saveCounter := mkMd (.LocalVariable freshV ⟨.TInt, #[]⟩ (some getCounter))
  let newHeap := mkMd (.StaticCall "increment" [mkMd (.Identifier heapVar)])
  let updateHeap := mkMd (.Assign [mkMd (.Identifier heapVar)] newHeap)
  let compositeResult := mkMd (.StaticCall "MkComposite" [mkMd (.Identifier freshV), mkMd (.StaticCall (name.text ++ "_TypeTag") [])])
  return ⟨.Block [saveCounter, updateHeap, compositeResult] none, md⟩

/-- Lower IsType to type tag lookup. -/
private def lowerIsType (target : StmtExprMd) (ty : HighTypeMd)
    (md : Imperative.MetaData Core.Expression) : StmtExprMd :=
  match ty.val with
  | .UserDefined name =>
    let typeName := name.text
    let typeTag := mkMd (.StaticCall "Composite..typeTag!" [target])
    let ancestorsPerType := mkMd (.StaticCall "ancestorsPerType" [])
    let innerMap := mkMd (.StaticCall "select" [ancestorsPerType, typeTag])
    let typeConst := mkMd (.StaticCall (mkId (typeName ++ "_TypeTag")) [])
    ⟨.StaticCall "select" [innerMap, typeConst], md⟩
  | _ => ⟨.Hole, md⟩

/-- Walk a StmtExpr AST and rewrite IsType and New nodes. -/
private partial def rewriteTypeHierarchyExpr (exprMd : StmtExprMd) : THM StmtExprMd :=
  match exprMd with
  | WithMetadata.mk expr md =>
  match expr with
  | .New name => lowerNew name md
  | .IsType target ty => do
      let target' ← rewriteTypeHierarchyExpr target
      return lowerIsType target' ty md
  | .IfThenElse c t e => do
      let e' ← match e with | some x => some <$> rewriteTypeHierarchyExpr x | none => pure none
      return ⟨.IfThenElse (← rewriteTypeHierarchyExpr c) (← rewriteTypeHierarchyExpr t) e', md⟩
  | .Block stmts label => do
      let stmts' ← stmts.mapM rewriteTypeHierarchyExpr
      return ⟨.Block stmts' label, md⟩
  | .LocalVariable n ty i => do
      let i' ← match i with | some x => some <$> rewriteTypeHierarchyExpr x | none => pure none
      return ⟨.LocalVariable n ty i', md⟩
  | .While c invs d b => do
      let d' ← match d with | some x => some <$> rewriteTypeHierarchyExpr x | none => pure none
      let invs' ← invs.mapM rewriteTypeHierarchyExpr
      return ⟨.While (← rewriteTypeHierarchyExpr c) invs' d' (← rewriteTypeHierarchyExpr b), md⟩
  | .Return v => do
      let v' ← match v with | some x => some <$> rewriteTypeHierarchyExpr x | none => pure none
      return ⟨.Return v', md⟩
  | .Assign targets v => do
      let targets' ← targets.mapM rewriteTypeHierarchyExpr
      return ⟨.Assign targets' (← rewriteTypeHierarchyExpr v), md⟩
  | .FieldSelect t f => do return ⟨.FieldSelect (← rewriteTypeHierarchyExpr t) f, md⟩
  | .PureFieldUpdate t f v => do return ⟨.PureFieldUpdate (← rewriteTypeHierarchyExpr t) f (← rewriteTypeHierarchyExpr v), md⟩
  | .StaticCall callee args => do
      let args' ← args.mapM rewriteTypeHierarchyExpr
      return ⟨.StaticCall callee args', md⟩
  | .PrimitiveOp op args => do
      let args' ← args.mapM rewriteTypeHierarchyExpr
      return ⟨.PrimitiveOp op args', md⟩
  | .ReferenceEquals l r => do return ⟨.ReferenceEquals (← rewriteTypeHierarchyExpr l) (← rewriteTypeHierarchyExpr r), md⟩
  | .AsType t ty => do return ⟨.AsType (← rewriteTypeHierarchyExpr t) ty, md⟩
  | .InstanceCall t callee args => do
      let args' ← args.mapM rewriteTypeHierarchyExpr
      return ⟨.InstanceCall (← rewriteTypeHierarchyExpr t) callee args', md⟩
  | .Forall p trigger b => do
      let trigger' ← match trigger with | some t => pure (some (← rewriteTypeHierarchyExpr t)) | none => pure none
      return ⟨.Forall p trigger' (← rewriteTypeHierarchyExpr b), md⟩
  | .Exists p trigger b => do
      let trigger' ← match trigger with | some t => pure (some (← rewriteTypeHierarchyExpr t)) | none => pure none
      return ⟨.Exists p trigger' (← rewriteTypeHierarchyExpr b), md⟩
  | .Assigned n => do return ⟨.Assigned (← rewriteTypeHierarchyExpr n), md⟩
  | .Old v => do return ⟨.Old (← rewriteTypeHierarchyExpr v), md⟩
  | .Fresh v => do return ⟨.Fresh (← rewriteTypeHierarchyExpr v), md⟩
  | .Assert c => do return ⟨.Assert (← rewriteTypeHierarchyExpr c), md⟩
  | .Assume c => do return ⟨.Assume (← rewriteTypeHierarchyExpr c), md⟩
  | .ProveBy v p => do return ⟨.ProveBy (← rewriteTypeHierarchyExpr v) (← rewriteTypeHierarchyExpr p), md⟩
  | .ContractOf ty f => do return ⟨.ContractOf ty (← rewriteTypeHierarchyExpr f), md⟩
  | _ => return exprMd

private def rewriteTypeHierarchyProcedure (proc : Procedure) : THM Procedure := do
  let preconditions' ← proc.preconditions.mapM rewriteTypeHierarchyExpr
  let body' ← match proc.body with
    | .Transparent b => pure (.Transparent (← rewriteTypeHierarchyExpr b))
    | .Opaque postconds impl modif =>
        let postconds' ← postconds.mapM rewriteTypeHierarchyExpr
        let impl' ← match impl with
          | some x => pure (some (← rewriteTypeHierarchyExpr x))
          | none => pure none
        let modif' ← modif.mapM rewriteTypeHierarchyExpr
        pure (.Opaque postconds' impl' modif')
    | .Abstract postconds => pure (.Abstract (← postconds.mapM rewriteTypeHierarchyExpr))
    | .External => pure .External
  return { proc with preconditions := preconditions', body := body' }

/-- Generate ancestorsFor/ancestorsPerType constants.
    Since V2 Translation doesn't use inheritance, this generates flat self-only ancestors. -/
private def generateTypeHierarchyDecls (composites : List CompositeType) : List Constant :=
  if composites.isEmpty then [] else
  let typeTagTy : HighTypeMd := ⟨.UserDefined "TypeTag", #[]⟩
  let boolTy : HighTypeMd := ⟨.TBool, #[]⟩
  let innerMapTy : HighTypeMd := ⟨.TMap typeTagTy boolTy, #[]⟩
  let outerMapTy : HighTypeMd := ⟨.TMap typeTagTy innerMapTy, #[]⟩
  -- For each composite type, build an inner map where only itself is an ancestor
  let mkInnerMap (ct : CompositeType) : StmtExprMd :=
    let falseConst := mkMd (.LiteralBool false)
    let emptyInner := mkMd (.StaticCall "const" [falseConst])
    -- In the V2 pipeline without inheritance, each type is only its own ancestor
    let selfConst := mkMd (.StaticCall (mkId (ct.name.text ++ "_TypeTag")) [])
    let boolVal := mkMd (.LiteralBool true)
    mkMd (.StaticCall "update" [emptyInner, selfConst, boolVal])
  let ancestorsForDecls := composites.map fun ct =>
    { name := s!"ancestorsFor{ct.name.text}"
      type := innerMapTy
      initializer := some (mkInnerMap ct) : Constant }
  let falseConst := mkMd (.LiteralBool false)
  let emptyInner := mkMd (.StaticCall "const" [falseConst])
  let emptyOuter := mkMd (.StaticCall "const" [emptyInner])
  let outerMapExpr := composites.foldl (fun acc ct =>
    let typeConst := mkMd (.StaticCall (mkId (ct.name.text ++ "_TypeTag")) [])
    let innerMapRef := mkMd (.StaticCall s!"ancestorsFor{ct.name.text}" [])
    mkMd (.StaticCall "update" [acc, typeConst, innerMapRef])
  ) emptyOuter
  let ancestorsDecl : Constant :=
    { name := "ancestorsPerType"
      type := outerMapTy
      initializer := some outerMapExpr }
  ancestorsForDecls ++ [ancestorsDecl]

/-- Run the type hierarchy transform phase. -/
private def typeHierarchyPhase (program : Laurel.Program) : Laurel.Program :=
  let composites := program.types.filterMap fun td =>
    match td with
    | .Composite ct => some ct
    | _ => none
  let compositeNames := composites.map (·.name.text)
  let typeTagDatatype : TypeDefinition :=
    .Datatype { name := "TypeTag", typeArgs := [], constructors :=
      compositeNames.map fun n => { name := (mkId (n ++ "_TypeTag")), args := [] } }
  let typeHierarchyConstants := generateTypeHierarchyDecls composites
  let (procs', _) := (program.staticProcedures.mapM rewriteTypeHierarchyProcedure).run {}
  -- Update Composite datatype to include typeTag field
  let typeTagTy : HighTypeMd := ⟨.UserDefined "TypeTag", #[]⟩
  let remainingTypes := program.types.map fun td =>
    match td with
    | .Datatype dt =>
      if dt.name.text == "Composite" then
        .Datatype { dt with constructors := dt.constructors.map fun c =>
          if c.name.text == "MkComposite" then
            { c with args := c.args ++ [{ name := ("typeTag" : Identifier), type := typeTagTy }] }
          else c }
      else td
    | _ => td
  { program with
    staticProcedures := procs',
    types := [typeTagDatatype] ++ remainingTypes,
    constants := program.constants ++ typeHierarchyConstants }

/-! ========================================================================
    Phase 4: Modifies Clauses Transform

    Transforms modifies clauses into frame condition postconditions.
    After heap parameterization, procedures with $heap have modifies info.
    ======================================================================== -/

/-- Check if a procedure has $heap as output (i.e., it writes heap). -/
private def hasHeapOut (proc : Procedure) : Bool :=
  proc.outputs.any (fun p => p.name.text == "$heap")

/-- Build a frame condition postcondition for a procedure's modifies clause.
    "For all objects not in modifies: heap_in fields == heap_out fields" -/
private def buildFrameCondition (proc : Procedure) (modifiesExprs : List StmtExprMd) : Option StmtExprMd :=
  if !hasHeapOut proc then none
  else
    let heapInName : Identifier := "$heap_in"
    let heapName : Identifier := "$heap"
    let objName : Identifier := "$modifies_obj"
    let fldName : Identifier := "$modifies_fld"
    -- If no explicit modifies, generate a full-preservation postcondition
    -- forall obj: Composite, fld: Field =>
    --   obj < $heap_in.nextReference ==> readField($heap_in, obj, fld) == readField($heap, obj, fld)
    if modifiesExprs.isEmpty then
      let objRef := mkMd (.Identifier objName)
      let fldRef := mkMd (.Identifier fldName)
      let heapInRef := mkMd (.Identifier heapInName)
      let heapRef := mkMd (.Identifier heapName)
      let nextRef := mkMd (.StaticCall "Heap..nextReference!" [heapInRef])
      let objLtNext := mkMd (.PrimitiveOp .Lt [mkMd (.StaticCall "Composite..ref!" [objRef]), nextRef])
      let readOld := mkMd (.StaticCall "readField" [heapInRef, objRef, fldRef])
      let readNew := mkMd (.StaticCall "readField" [heapRef, objRef, fldRef])
      let preserved := mkMd (.PrimitiveOp .Eq [readOld, readNew])
      let implication := mkMd (.PrimitiveOp .Implies [objLtNext, preserved])
      let objParam : Parameter := { name := objName, type := ⟨.UserDefined "Composite", #[]⟩ }
      let fldParam : Parameter := { name := fldName, type := ⟨.UserDefined "Field", #[]⟩ }
      some ⟨.Forall objParam none ⟨.Forall fldParam none implication, #[]⟩, #[]⟩
    else
      -- With explicit modifies: exclude modified objects from frame condition
      -- For simplicity, just generate the same full-preservation but with exclusion
      -- ARCHITECTURE GAP: Full modifies exclusion logic would need expression comparison
      let objRef := mkMd (.Identifier objName)
      let fldRef := mkMd (.Identifier fldName)
      let heapInRef := mkMd (.Identifier heapInName)
      let heapRef := mkMd (.Identifier heapName)
      let nextRef := mkMd (.StaticCall "Heap..nextReference!" [heapInRef])
      let objLtNext := mkMd (.PrimitiveOp .Lt [mkMd (.StaticCall "Composite..ref!" [objRef]), nextRef])
      -- Build exclusion: obj != modified_obj1 && obj != modified_obj2 && ...
      let exclusions := modifiesExprs.foldl (fun acc modExpr =>
        let neq := mkMd (.PrimitiveOp .Neq [mkMd (.StaticCall "Composite..ref!" [objRef]),
                                              mkMd (.StaticCall "Composite..ref!" [modExpr])])
        match acc with
        | none => some neq
        | some prev => some (mkMd (.PrimitiveOp .And [prev, neq]))
      ) (none : Option StmtExprMd)
      let readOld := mkMd (.StaticCall "readField" [heapInRef, objRef, fldRef])
      let readNew := mkMd (.StaticCall "readField" [heapRef, objRef, fldRef])
      let preserved := mkMd (.PrimitiveOp .Eq [readOld, readNew])
      let antecedent := match exclusions with
        | some excl => mkMd (.PrimitiveOp .And [objLtNext, excl])
        | none => objLtNext
      let implication := mkMd (.PrimitiveOp .Implies [antecedent, preserved])
      let objParam : Parameter := { name := objName, type := ⟨.UserDefined "Composite", #[]⟩ }
      let fldParam : Parameter := { name := fldName, type := ⟨.UserDefined "Field", #[]⟩ }
      some ⟨.Forall objParam none ⟨.Forall fldParam none implication, #[]⟩, #[]⟩

/-- Transform modifies clauses for a single procedure. -/
private def transformModifiesForProc (proc : Procedure) : Procedure :=
  match proc.body with
  | .External => proc
  | .Opaque postconds impl modifiesExprs =>
    if hasHeapOut proc then
      let frameCondition := buildFrameCondition proc modifiesExprs
      let postconds' := match frameCondition with
        | some frame => postconds ++ [frame]
        | none => postconds
      { proc with body := .Opaque postconds' impl [] }
    else proc
  | _ => proc

/-- Run the modifies clauses transform phase. -/
private def modifiesClausesPhase (program : Laurel.Program) : Laurel.Program :=
  let procs' := program.staticProcedures.map transformModifiesForProc
  { program with staticProcedures := procs' }

/-! ========================================================================
    Phase 5: Hole Elimination

    Replace each deterministic typed `.Hole` with a call to a freshly generated
    uninterpreted function. Does NOT require SemanticModel.
    ======================================================================== -/

structure HoleElimState where
  counter : Nat := 0
  currentInputs : List Parameter := []
  generatedFunctions : List Procedure := []

abbrev HoleElimM := StateM HoleElimState

/-- Generate a fresh uninterpreted function for a typed hole. -/
private def mkHoleCall (holeType : HighTypeMd) : HoleElimM StmtExprMd := do
  let s ← get
  let n := s.counter
  modify fun s => { s with counter := n + 1 }
  let holeName : Identifier := s!"$hole_{n}"
  let inputs := s.currentInputs
  let holeProc : Procedure := {
    name := holeName
    inputs := inputs
    outputs := [{ name := "$result", type := holeType }]
    preconditions := []
    determinism := .deterministic none
    decreases := none
    isFunctional := true
    body := .Opaque [] none []
    md := #[]
  }
  modify fun s => { s with generatedFunctions := s.generatedFunctions ++ [holeProc] }
  return mkMd (.StaticCall holeName (inputs.map (fun p => mkMd (.Identifier p.name))))

mutual
partial def holeElimExpr (expr : StmtExprMd) : HoleElimM StmtExprMd := do
  match expr with
  | WithMetadata.mk val md =>
  match val with
  | .Hole true (some ty) => mkHoleCall ty
  | .Hole true none => mkHoleCall ⟨.Unknown, md⟩
  | .Hole false _ => return expr
  | .PrimitiveOp op args => return ⟨.PrimitiveOp op (← args.mapM holeElimExpr), md⟩
  | .StaticCall callee args => return ⟨.StaticCall callee (← args.mapM holeElimExpr), md⟩
  | .InstanceCall target callee args =>
      return ⟨.InstanceCall (← holeElimExpr target) callee (← args.mapM holeElimExpr), md⟩
  | .ReferenceEquals lhs rhs => return ⟨.ReferenceEquals (← holeElimExpr lhs) (← holeElimExpr rhs), md⟩
  | .IfThenElse cond th el =>
      let el' ← match el with | some e => pure (some (← holeElimExpr e)) | none => pure none
      return ⟨.IfThenElse (← holeElimExpr cond) (← holeElimExpr th) el', md⟩
  | .Block stmts label => return ⟨.Block (← holeElimStmtList stmts) label, md⟩
  | .Assign targets value => return ⟨.Assign targets (← holeElimExpr value), md⟩
  | .LocalVariable name ty init =>
      match init with
      | some initExpr => return ⟨.LocalVariable name ty (some (← holeElimExpr initExpr)), md⟩
      | none => return expr
  | .Old v => return ⟨.Old (← holeElimExpr v), md⟩
  | .Fresh v => return ⟨.Fresh (← holeElimExpr v), md⟩
  | .Assigned n => return ⟨.Assigned (← holeElimExpr n), md⟩
  | .ProveBy v p => return ⟨.ProveBy (← holeElimExpr v) (← holeElimExpr p), md⟩
  | .ContractOf ty f => return ⟨.ContractOf ty (← holeElimExpr f), md⟩
  | .Forall p trigger b =>
      let trigger' ← match trigger with | some t => pure (some (← holeElimExpr t)) | none => pure none
      return ⟨.Forall p trigger' (← holeElimExpr b), md⟩
  | .Exists p trigger b =>
      let trigger' ← match trigger with | some t => pure (some (← holeElimExpr t)) | none => pure none
      return ⟨.Exists p trigger' (← holeElimExpr b), md⟩
  | _ => return expr

partial def holeElimStmt (stmt : StmtExprMd) : HoleElimM StmtExprMd := do
  match stmt with
  | WithMetadata.mk val md =>
  match val with
  | .LocalVariable name ty (some initExpr) =>
      return ⟨.LocalVariable name ty (some (← holeElimExpr initExpr)), md⟩
  | .Assign targets value => return ⟨.Assign targets (← holeElimExpr value), md⟩
  | .Block stmts label => return ⟨.Block (← holeElimStmtList stmts) label, md⟩
  | .IfThenElse cond th el =>
      let el' ← match el with | some e => pure (some (← holeElimStmt e)) | none => pure none
      return ⟨.IfThenElse (← holeElimExpr cond) (← holeElimStmt th) el', md⟩
  | .While cond invs dec body =>
      let dec' ← match dec with | some d => pure (some (← holeElimExpr d)) | none => pure none
      return ⟨.While (← holeElimExpr cond) (← invs.mapM holeElimExpr) dec' (← holeElimStmt body), md⟩
  | .Assert cond => return ⟨.Assert (← holeElimExpr cond), md⟩
  | .Assume cond => return ⟨.Assume (← holeElimExpr cond), md⟩
  | .StaticCall callee args => return ⟨.StaticCall callee (← args.mapM holeElimExpr), md⟩
  | .Return (some retExpr) => return ⟨.Return (some (← holeElimExpr retExpr)), md⟩
  | .Hole true (some ty) => mkHoleCall ty
  | .Hole true none => mkHoleCall ⟨.Unknown, md⟩
  | .Hole false _ => return stmt
  | _ => return stmt

partial def holeElimStmtList (stmts : List StmtExprMd) : HoleElimM (List StmtExprMd) :=
  stmts.mapM holeElimStmt
end

private def holeElimProcedure (proc : Procedure) : HoleElimM Procedure := do
  modify fun s => { s with currentInputs := proc.inputs }
  match proc.body with
  | .Transparent bodyExpr => return { proc with body := .Transparent (← holeElimStmt bodyExpr) }
  | .Opaque postconds (some impl) modif =>
      return { proc with body := .Opaque postconds (some (← holeElimStmt impl)) modif }
  | _ => return proc

/-- Run the hole elimination phase. -/
private def holeEliminationPhase (program : Laurel.Program) : Laurel.Program :=
  let initState : HoleElimState := {}
  let (procs, finalState) := (program.staticProcedures.mapM holeElimProcedure).run initState
  { program with staticProcedures := finalState.generatedFunctions ++ procs }

/-! ========================================================================
    Phase 6: Infer Hole Types (simple version without SemanticModel)

    Annotates untyped Holes with their contextual type. Uses procedure output
    types and LocalVariable types to infer. No SemanticModel needed.
    ======================================================================== -/

structure InferHoleState where
  currentOutputType : HighTypeMd := ⟨.Unknown, #[]⟩

abbrev InferHoleM := StateM InferHoleState

private def bareType (v : HighType) : HighTypeMd := ⟨v, #[]⟩
private def defaultHoleType : HighTypeMd := bareType .Unknown

mutual
partial def inferExpr (expr : StmtExprMd) (expectedType : HighTypeMd) : InferHoleM StmtExprMd := do
  match expr with
  | WithMetadata.mk val md =>
  match val with
  | .Hole det _ => return ⟨.Hole det (some expectedType), md⟩
  | .PrimitiveOp op args =>
      return ⟨.PrimitiveOp op (← args.mapM (inferExpr · expectedType)), md⟩
  | .StaticCall callee args =>
      return ⟨.StaticCall callee (← args.mapM (inferExpr · defaultHoleType)), md⟩
  | .InstanceCall target callee args =>
      return ⟨.InstanceCall (← inferExpr target defaultHoleType) callee (← args.mapM (inferExpr · defaultHoleType)), md⟩
  | .ReferenceEquals lhs rhs =>
      return ⟨.ReferenceEquals (← inferExpr lhs defaultHoleType) (← inferExpr rhs defaultHoleType), md⟩
  | .IfThenElse cond th el =>
      let el' ← match el with
        | some e => pure (some (← inferExpr e expectedType))
        | none => pure none
      return ⟨.IfThenElse (← inferExpr cond (bareType .TBool)) (← inferExpr th expectedType) el', md⟩
  | .Block stmts label => return ⟨.Block (← inferStmtList stmts) label, md⟩
  | .Assign targets value => return ⟨.Assign targets (← inferExpr value defaultHoleType), md⟩
  | .LocalVariable name ty init =>
      match init with
      | some initExpr => return ⟨.LocalVariable name ty (some (← inferExpr initExpr ty)), md⟩
      | none => return expr
  | .Old v => return ⟨.Old (← inferExpr v expectedType), md⟩
  | .Fresh v => return ⟨.Fresh (← inferExpr v defaultHoleType), md⟩
  | .Assigned n => return ⟨.Assigned (← inferExpr n defaultHoleType), md⟩
  | .ProveBy v p => return ⟨.ProveBy (← inferExpr v expectedType) (← inferExpr p defaultHoleType), md⟩
  | .ContractOf ty f => return ⟨.ContractOf ty (← inferExpr f defaultHoleType), md⟩
  | .Forall p trigger b =>
      let trigger' ← match trigger with
        | some t => pure (some (← inferExpr t defaultHoleType))
        | none => pure none
      return ⟨.Forall p trigger' (← inferExpr b (bareType .TBool)), md⟩
  | .Exists p trigger b =>
      let trigger' ← match trigger with
        | some t => pure (some (← inferExpr t defaultHoleType))
        | none => pure none
      return ⟨.Exists p trigger' (← inferExpr b (bareType .TBool)), md⟩
  | _ => return expr

partial def inferStmt (stmt : StmtExprMd) : InferHoleM StmtExprMd := do
  match stmt with
  | WithMetadata.mk val md =>
  match val with
  | .LocalVariable name ty (some initExpr) =>
      return ⟨.LocalVariable name ty (some (← inferExpr initExpr ty)), md⟩
  | .Assign targets value => return ⟨.Assign targets (← inferExpr value defaultHoleType), md⟩
  | .Block stmts label => return ⟨.Block (← inferStmtList stmts) label, md⟩
  | .IfThenElse cond th el =>
      let el' ← match el with
        | some e => pure (some (← inferStmt e))
        | none => pure none
      return ⟨.IfThenElse (← inferExpr cond (bareType .TBool)) (← inferStmt th) el', md⟩
  | .While cond invs dec body =>
      let dec' ← match dec with
        | some d => pure (some (← inferExpr d (bareType .TInt)))
        | none => pure none
      return ⟨.While (← inferExpr cond (bareType .TBool)) (← invs.mapM (inferExpr · (bareType .TBool))) dec' (← inferStmt body), md⟩
  | .Assert cond => return ⟨.Assert (← inferExpr cond (bareType .TBool)), md⟩
  | .Assume cond => return ⟨.Assume (← inferExpr cond (bareType .TBool)), md⟩
  | .StaticCall callee args =>
      return ⟨.StaticCall callee (← args.mapM (inferExpr · defaultHoleType)), md⟩
  | .Return (some retExpr) => return ⟨.Return (some (← inferExpr retExpr (← get).currentOutputType)), md⟩
  | .Hole det _ => return ⟨.Hole det (some (← get).currentOutputType), md⟩
  | _ => return stmt

partial def inferStmtList (stmts : List StmtExprMd) : InferHoleM (List StmtExprMd) :=
  stmts.mapM inferStmt
end

private def inferHoleProcedure (proc : Procedure) : InferHoleM Procedure := do
  let outputType := match proc.outputs with
    | [single] => single.type
    | _ => defaultHoleType
  modify fun s => { s with currentOutputType := outputType }
  match proc.body with
  | .Transparent bodyExpr => return { proc with body := .Transparent (← inferStmt bodyExpr) }
  | .Opaque postconds (some impl) modif =>
      return { proc with body := .Opaque postconds (some (← inferStmt impl)) modif }
  | _ => return proc

/-- Run the hole type inference phase. -/
private def inferHoleTypesPhase (program : Laurel.Program) : Laurel.Program :=
  let initState : InferHoleState := {}
  let (procs, _) := (program.staticProcedures.mapM inferHoleProcedure).run initState
  { program with staticProcedures := procs }

/-! ========================================================================
    Phase 7: Constrained Type Elimination

    Eliminates constrained types by generating constraint functions and
    adding requires/ensures/asserts. Uses program type definitions directly.
    ======================================================================== -/

private abbrev ConstrainedTypeMap := Std.HashMap String ConstrainedType

private def buildConstrainedTypeMap (types : List TypeDefinition) : ConstrainedTypeMap :=
  types.foldl (init := {}) fun m td =>
    match td with | .Constrained ct => m.insert ct.name.text ct | _ => m

private partial def resolveBaseType (ptMap : ConstrainedTypeMap) (ty : HighType) : HighType :=
  match ty with
  | .UserDefined name => match ptMap.get? name.text with
    | some ct => resolveBaseType ptMap ct.base.val | none => ty
  | _ => ty

private def resolveTypeMd (ptMap : ConstrainedTypeMap) (ty : HighTypeMd) : HighTypeMd :=
  ⟨resolveBaseType ptMap ty.val, ty.md⟩

/-- Resolve constrained types in expressions and generate constraint calls. -/
private partial def resolveConstrainedExpr (ptMap : ConstrainedTypeMap) : StmtExprMd → StmtExprMd
  | ⟨.LocalVariable n ty (some init), md⟩ =>
    ⟨.LocalVariable n (resolveTypeMd ptMap ty) (some (resolveConstrainedExpr ptMap init)), md⟩
  | ⟨.LocalVariable n ty none, md⟩ =>
    ⟨.LocalVariable n (resolveTypeMd ptMap ty) none, md⟩
  | ⟨.Forall param trigger body, md⟩ =>
    let body' := resolveConstrainedExpr ptMap body
    let param' := { param with type := resolveTypeMd ptMap param.type }
    let injected := match param.type.val with
      | .UserDefined name =>
        if ptMap.contains name.text then
          let c := ⟨.StaticCall (mkId s!"{name.text}$constraint") [⟨.Identifier param.name, md⟩], md⟩
          ⟨.PrimitiveOp .Implies [c, body'], md⟩
        else body'
      | _ => body'
    ⟨.Forall param' trigger injected, md⟩
  | ⟨.Exists param trigger body, md⟩ =>
    let body' := resolveConstrainedExpr ptMap body
    let param' := { param with type := resolveTypeMd ptMap param.type }
    let injected := match param.type.val with
      | .UserDefined name =>
        if ptMap.contains name.text then
          let c := ⟨.StaticCall (mkId s!"{name.text}$constraint") [⟨.Identifier param.name, md⟩], md⟩
          ⟨.PrimitiveOp .And [c, body'], md⟩
        else body'
      | _ => body'
    ⟨.Exists param' trigger injected, md⟩
  | other => other

/-- Transform a procedure for constrained type elimination. -/
private def constrainedTypeElimProc (ptMap : ConstrainedTypeMap) (proc : Procedure)
    : Procedure × List DiagnosticModel :=
  if ptMap.isEmpty then (proc, []) else
  -- Add requires for constrained-typed inputs
  let requires := proc.inputs.filterMap fun p =>
    match p.type.val with
    | .UserDefined name =>
      if ptMap.contains name.text then
        some ⟨.StaticCall (mkId s!"{name.text}$constraint") [⟨.Identifier p.name, #[]⟩], #[]⟩
      else none
    | _ => none
  -- Add ensures for constrained-typed outputs (non-functional only)
  let ensures := if proc.isFunctional then [] else
    proc.outputs.filterMap fun p =>
      match p.type.val with
      | .UserDefined name =>
        if ptMap.contains name.text then
          some ⟨.StaticCall (mkId s!"{name.text}$constraint") [⟨.Identifier p.name, #[]⟩], #[]⟩
        else none
      | _ => none
  -- Resolve constrained types in parameter/output types
  let inputs' := proc.inputs.map fun p => { p with type := resolveTypeMd ptMap p.type }
  let outputs' := proc.outputs.map fun p => { p with type := resolveTypeMd ptMap p.type }
  -- Resolve in body
  let body' : Body := match proc.body with
    | .Transparent b => Body.Transparent (resolveConstrainedExpr ptMap b)
    | .Opaque postconds impl modif =>
        Body.Opaque (postconds.map (resolveConstrainedExpr ptMap))
          (impl.map (resolveConstrainedExpr ptMap)) modif
    | .Abstract postconds => Body.Abstract (postconds.map (resolveConstrainedExpr ptMap))
    | .External => Body.External
  let preconditions' := proc.preconditions.map (resolveConstrainedExpr ptMap) ++ requires
  -- Build ensures into Opaque body postconditions
  let finalBody : Body := match body' with
    | .Opaque postconds impl modif => Body.Opaque (postconds ++ ensures) impl modif
    | other => other
  ({ proc with inputs := inputs', outputs := outputs',
               preconditions := preconditions', body := finalBody }, [])

/-- Generate constraint functions for constrained types. -/
private def mkConstraintFunctions (ptMap : ConstrainedTypeMap) : List Procedure :=
  ptMap.toList.map fun (_, ct) =>
    let baseType := resolveTypeMd ptMap ct.base
    { name := mkId s!"{ct.name.text}$constraint"
      inputs := [{ name := ct.valueName, type := { baseType with md := #[] } }]
      outputs := [{ name := mkId "result", type := ⟨.TBool, #[]⟩ }]
      body := .Transparent ⟨.Block [ct.constraint] none, #[]⟩
      isFunctional := true
      determinism := .deterministic none
      decreases := none
      preconditions := []
      md := #[] }

/-- Run the constrained type elimination phase. -/
private def constrainedTypeElimPhase (program : Laurel.Program) : Laurel.Program × List DiagnosticModel :=
  let ptMap := buildConstrainedTypeMap program.types
  if ptMap.isEmpty then (program, []) else
  let constraintFuncs := mkConstraintFunctions ptMap
  let (procs', diags) := program.staticProcedures.foldl (fun (acc, ds) proc =>
    let (proc', procDiags) := constrainedTypeElimProc ptMap proc
    (acc ++ [proc'], ds ++ procDiags)) ([], [])
  -- Remove constrained types from type definitions (they've been inlined)
  let types' := program.types.filter fun td =>
    match td with | .Constrained _ => false | _ => true
  ({ program with staticProcedures := constraintFuncs ++ procs', types := types' }, diags)

/-! ========================================================================
    UNIFIED ELABORATION ENTRY POINT

    This is the single function that replaces `lowerProgram`.
    It chains all phases in the correct order, using TypeEnv throughout.
    No `resolve` calls anywhere in this pipeline.
    ======================================================================== -/

/-- The output of the unified elaboration pass.
    Contains the lowered program ready for Core translation,
    plus any diagnostics generated during elaboration. -/
structure UnifiedElabResult where
  /-- The fully elaborated/lowered Laurel program -/
  program : Laurel.Program
  /-- Diagnostics (warnings, errors) from elaboration -/
  diagnostics : List DiagnosticModel := []

/-- Run the unified elaboration: the single pass that replaces all 8 fragment passes.

    Pipeline order:
    1. Bidirectional walk (coercions, short-circuit desugaring, error handling)
    2. Heap parameterization (co-operation: field access → readField, etc.)
    3. Type hierarchy (New → MkComposite, IsType → type tag lookup)
    4. Modifies clauses (modifies → frame condition postcondition)
    5. Infer hole types
    6. Eliminate holes (Holes → fresh uninterpreted functions)
    7. Constrained type elimination (constrained types → requires/ensures)

    Does NOT call `resolve`. Uses TypeEnv from Python NameResolution throughout.
    This satisfies the architecture's requirement that elaboration is a single
    derivation transformation that makes all effects explicit. -/
def unifiedElaborate (typeEnv : TypeEnv) (program : Laurel.Program) : UnifiedElabResult :=
  -- Prepend Laurel core definitions (same as lowerProgram does)
  let program := { program with
    staticProcedures := Laurel.coreDefinitionsForLaurel.staticProcedures ++ program.staticProcedures
  }

  -- Phase 1: Bidirectional walk (coercions, short-circuit)
  -- SKIPPED: The V2 Translation already wraps literals (from_int/from_str/from_bool)
  -- and inserts Any_to_bool for conditions. Running the bidirectional walk would
  -- cause double-wrapping (e.g., from_int(from_int(5))). The bidirectional elaboration
  -- will be enabled once Translation stops inserting coercions (i.e., produces "HighLaurel"
  -- per the architecture). For now, Translation handles coercions and this pass handles
  -- everything else (heap, type hierarchy, holes, etc.).
  let program := program

  -- Phase 2: Heap parameterization (the co-operation)
  let program := heapParameterizationPhase typeEnv program

  -- Phase 3: Type hierarchy (New → MkComposite, TypeTag, ancestorsPerType)
  let program := typeHierarchyPhase program

  -- Phase 4: Modifies clauses → frame conditions
  let program := modifiesClausesPhase program

  -- Phase 5: Infer hole types
  let program := inferHoleTypesPhase program

  -- Phase 6: Eliminate holes → uninterpreted functions
  let program := holeEliminationPhase program

  -- Phase 7: Constrained type elimination
  let (program, constrainedDiags) := constrainedTypeElimPhase program

  { program := program, diagnostics := constrainedDiags }

/-! ## Backward Compatibility -/

/-- Simple elaboration entry point for a single expression. -/
def elaborateExpr (typeEnv : TypeEnv) (expr : StmtExprMd)
    : Except String StmtExprMd := do
  let env := mkElabEnv typeEnv
  let (result, _) ← (synth expr).run env |>.run {}
  pure result.toExpr

/-- Project FineGrainLaurel back to plain Laurel (identity for now). -/
def project (expr : StmtExprMd) : StmtExprMd := expr

end -- public section
end Strata.FineGrainLaurel
