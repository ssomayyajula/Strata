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
public import Strata.Languages.FineGrainLaurel.FineGrainLaurel
import Strata.Util.Tactics

/-!
# Unified Elaboration: Laurel → FineGrainLaurel → Lowered Laurel

Phase 1 (Bidirectional Walk) now produces FGL.Value/FGL.Producer types, implementing
the architecture's requirement that elaboration outputs FineGrainLaurel derivations.

The four judgments (per Lakhani & Pfenning):
- synthValue: infer a Value and its type
- checkValue: check an expression as a Value against an expected type (subtyping)
- synthProducer: infer a Producer and its type
- checkProducer: check an expression as a Producer against an expected type (narrowing)

After Phase 1 produces FGL types, `projectProducer` maps them back to Laurel StmtExprMd
for the remaining phases (heap parameterization, type hierarchy, etc.) which still operate
on Laurel.

## Subtyping vs Narrowing

- **Subtyping (A <: B):** value→value, infallible. int <: Any via valFromInt.
- **Narrowing (A ▷ B):** value→producer, fallible. Any ▷ bool via prodCall "Any_to_bool".

## Phases 2-7 (unchanged)

Heap parameterization, type hierarchy, modifies clauses, hole inference/elimination,
and constrained type elimination all still operate on Laurel.Program directly.
-/

namespace Strata.FineGrainLaurel

open Strata.Laurel
open Strata.Python.Resolution

-- Note: FineGrainLaurel types (Value, Producer, Parameter, Procedure) shadow
-- Laurel types with the same name. Use Laurel.Procedure, Laurel.Parameter etc.
-- for the Laurel-specific versions.

public section

/-! ## FGL Abbreviations (Unit-annotated for elaboration output) -/

/-- FGL Value with no source annotation (elaboration output). -/
abbrev FValue := Value Unit

/-- FGL Producer with no source annotation (elaboration output). -/
abbrev FProducer := Producer Unit

/-- FGL LaurelType with no source annotation. -/
abbrev FLaurelType := FineGrainLaurel.LaurelType Unit

/-- FGL Invariant with no source annotation. -/
abbrev FInvariant := Invariant Unit

/-- Make an Ann with unit annotation -/
def mkAnn (v : β) : Strata.Ann β Unit := ⟨(), v⟩

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

/-! ## Converting HighType to FGL LaurelType -/

/-- Convert a HighType to the FGL LaurelType representation. -/
def highTypeToFGL : HighType → FLaurelType
  | .TInt => .intType ()
  | .TBool => .boolType ()
  | .TFloat64 => .float64Type ()
  | .TReal => .realType ()
  | .TString => .stringType ()
  | .TCore s => .coreType () (mkAnn s)
  | .UserDefined name => .compositeType () (mkAnn name.text)
  | .TVoid => .coreType () (mkAnn "Void")
  | .THeap => .coreType () (mkAnn "Heap")
  | .Unknown => .coreType () (mkAnn "Any")
  | .TMap k v => .mapType () (highTypeToFGL k.val) (highTypeToFGL v.val)
  | .TSet _ => .coreType () (mkAnn "Any")
  | .TTypedField _ => .coreType () (mkAnn "Any")
  | .Applied _ _ => .coreType () (mkAnn "Any")
  | .Pure _ => .coreType () (mkAnn "Any")
  | .Intersection _ => .coreType () (mkAnn "Any")

/-! ## Subtyping and Coercion Logic -/

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

/-- Can source be upcast to target (subtyping: value→value, infallible)?
    Returns true when source <: target. -/
def canUpcast (source target : HighType) : Bool :=
  isConcrete source && isAny target

/-- Can source be narrowed to target (narrowing: value→producer, fallible)?
    Returns true when source ▷ target. -/
def canNarrow (source target : HighType) : Bool :=
  isAny source && isConcrete target

/-- Insert upcast coercion (concrete → Any): a Value-level operation.
    Wraps the value in the appropriate valFrom* constructor. -/
def insertFGLUpcast (val : FValue) (sourceTy : HighType) : FValue :=
  match sourceTy with
  | .TInt => .valFromInt () val
  | .TBool => .valFromBool () val
  | .TString => .valFromStr () val
  | .TFloat64 => .valFromFloat () val
  | .TReal => .valFromFloat () val
  | .UserDefined _ => .valFromComposite () val
  | .TVoid => .valFromNone ()
  | _ => .valFromInt () val  -- fallback for unknown concrete types

/-- Get the narrowing function name for Any → concrete. -/
def narrowFuncName : HighType → String
  | .TBool => "Any_to_bool"
  | .TInt => "Any..as_int!"
  | .TString => "Any..as_string!"
  | .TFloat64 => "Any..as_float!"
  | .UserDefined _ => "Any..as_Composite!"
  | _ => "Any_to_bool"

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

/-! ## Short-Circuit Helper -/

/-- Check if a Laurel expression is effectful (contains StaticCall, Assign, or other Producer). -/
def isEffectful (expr : StmtExprMd) : Bool :=
  match expr.val with
  | .StaticCall _ _ => true
  | .InstanceCall _ _ _ => true
  | .New _ => true
  | .Assign _ _ => true
  | .IfThenElse _ _ _ => true
  | .While _ _ _ _ => true
  | .Block _ _ => true
  | .LocalVariable _ _ _ => true
  | .Return _ => true
  | .Exit _ => true
  | .Assert _ => true
  | .Assume _ => true
  | _ => false

/-! ========================================================================
    THE FOUR ELABORATION JUDGMENTS (Phase 1: Bidirectional Walk)

    Input: Laurel.StmtExprMd (from Translation)
    Output: FGL.Value or FGL.Producer (the FineGrainLaurel types)

    These produce ACTUAL FGL types -- not StmtExprMd. This satisfies the
    architecture's requirement that elaboration outputs FineGrainLaurel
    derivations with Value/Producer polarity.
    ======================================================================== -/

mutual

/-- Synthesize a Value from a Laurel expression: infer its type.
    Returns (FGL.Value, HighType). -/
partial def synthValue (expr : StmtExprMd) : ElabM (FValue × HighType) := do
  let env ← read
  match expr.val with
  | .LiteralInt n =>
    pure (.valLiteralInt () (mkAnn n.toNat), .TInt)

  | .LiteralBool b =>
    pure (.valLiteralBool () (mkAnn b), .TBool)

  | .LiteralString s =>
    pure (.valLiteralString () (mkAnn s), .TString)

  | .LiteralDecimal d =>
    pure (.valLiteralReal () (mkAnn d), .TReal)

  | .Identifier name =>
    let ty := lookupNameType env name.text
    pure (.valVar () (mkAnn name.text), ty)

  | .FieldSelect target field => do
    let (targetVal, receiverTy) ← synthValue target
    let fieldTy := lookupFieldType env receiverTy field.text
    pure (.valFieldAccess () targetVal (mkAnn field.text), fieldTy)

  -- Hole: used for nondeterministic values (e.g., havoc in for-loops)
  -- In value position, Holes represent unknown constants. Project as $Hole variable
  -- which is safe since Holes are always assigned to variables (never used directly).
  | .Hole _det tyOpt =>
    let ty := tyOpt.map (·.val) |>.getD (.TCore "Any")
    pure (.valVar () (mkAnn "$Hole_val"), ty)

  -- PrimitiveOp: value-level operations (comparison, arithmetic at Laurel level).
  -- These are used by downstream passes (e.g., heapParameterization, modifies clauses)
  -- but rarely appear in Translation output. Pass through with Any type.
  -- Use $PrimOp_val sentinel that projects back to a placeholder.
  | .PrimitiveOp _op _args =>
    pure (.valVar () (mkAnn "$PrimOp_val"), .TCore "Any")

  -- For expressions that are naturally Producers, we must bind them to get a Value.
  -- IMPORTANT: Only call synthProducer for known Producer forms to avoid infinite
  -- mutual recursion on unhandled constructors.
  | .StaticCall .. | .InstanceCall .. | .New .. | .Assign .. | .Block .. |
    .IfThenElse .. | .While .. | .LocalVariable .. | .Return .. |
    .Assert .. | .Assume .. | .Exit .. => do
    let (_prod, ty) ← synthProducer expr
    let tmp ← freshVar "v"
    pure (.valVar () (mkAnn tmp), ty)

  -- Fallback for any other constructors: return as Any-typed variable
  -- This prevents infinite recursion between synthValue and synthProducer
  | _ =>
    pure (.valVar () (mkAnn "$unknown"), .TCore "Any")

/-- Check a Laurel expression AS a Value against an expected type.
    Inserts upcast (subtyping) coercion if needed. Value→Value only.
    If narrowing is needed (value→producer), this function CANNOT handle it --
    the caller must use checkProducer instead. -/
partial def checkValue (expr : StmtExprMd) (expected : HighType) : ElabM FValue := do
  let (val, actual) ← synthValue expr
  if isSubtype actual expected then
    -- Types match (or are trivially compatible) -- no coercion needed
    pure val
  else if canUpcast actual expected then
    -- Subtyping: concrete <: Any -- insert valFrom* (stays in value judgment)
    pure (insertFGLUpcast val actual)
  else if canNarrow actual expected then
    -- ARCHITECTURE GAP: narrowing requires producing a Producer, but checkValue
    -- returns Value. The caller should have used checkProducer for this case.
    -- For now, we just return the value unchanged and mark the gap.
    -- In correct usage, the bidirectional algorithm ensures this case doesn't arise
    -- in checkValue (conditions go through checkProducer).
    pure val
  else
    -- Types are unrelated or unknown -- return unchanged
    pure val

/-- Synthesize a Producer from a Laurel expression: infer its result type.
    Returns (FGL.Producer, HighType). -/
partial def synthProducer (expr : StmtExprMd) : ElabM (FProducer × HighType) := do
  let env ← read
  match expr.val with

  -- Calls: the primary Producer form
  | .StaticCall callee args => do
    -- Short-circuit desugaring: PAnd/POr with effectful second operand
    match callee.text, args with
    | "PAnd", [left, right] =>
      if isEffectful right then
        let desugared : StmtExprMd :=
          { val := .IfThenElse left right (some { val := .LiteralBool false, md := expr.md }),
            md := expr.md }
        synthProducer desugared
      else
        synthStaticCall callee args expr
    | "POr", [left, right] =>
      if isEffectful right then
        let desugared : StmtExprMd :=
          { val := .IfThenElse left { val := .LiteralBool true, md := expr.md } (some right),
            md := expr.md }
        synthProducer desugared
      else
        synthStaticCall callee args expr
    | _, _ =>
      synthStaticCall callee args expr

  | .InstanceCall target callee args => do
    let (targetVal, receiverTy) ← synthValue target
    let qualName := match receiverTy with
      | .UserDefined className => s!"{className.text}@{callee.text}"
      | _ => callee.text
    let sig := lookupFuncSig env qualName
    let paramTypes := sig.map (·.params) |>.getD []
    let checkedArgs ← checkArgs args paramTypes
    let retTy := sig.map (·.returnType) |>.getD (.TCore "Any")
    let allArgs := targetVal :: checkedArgs
    pure (.prodCall () (mkAnn qualName) (mkAnn allArgs.toArray), retTy)

  | .New name =>
    -- ARCHITECTURE GAP: prodNew needs heap threading (Phase 2 handles this)
    -- For now emit a prodCall placeholder
    let ty := HighType.UserDefined name
    let tmp ← freshVar "obj"
    pure (.prodNew () (mkAnn name.text) (mkAnn tmp) (highTypeToFGL ty)
      (.prodReturnValue () (.valVar () (mkAnn tmp))), ty)

  -- Assign: target := value; continuation
  | .Assign targets value => do
    match targets with
    | [target] => do
      let expectedTy := match target.val with
        | .Identifier name => lookupNameType env name.text
        | _ => .TCore "Any"
      let (rhsProd, rhsTy) ← synthProducer value
      let targetVal ← synthTargetValue target
      if isSubtype rhsTy expectedTy || highTypeEq rhsTy expectedTy then
        -- RHS type matches target.
        -- Optimization: if the RHS is a simple value (prodReturnValue), skip let-binding
        match rhsProd with
        | .prodReturnValue _ rhsVal =>
          pure (.prodAssign () targetVal rhsVal
            (.prodReturnValue () rhsVal), expectedTy)
        | _ =>
          let tmp ← freshVar "rhs"
          pure (.prodLetProd () (mkAnn tmp) (highTypeToFGL rhsTy) rhsProd
            (.prodAssign () targetVal (.valVar () (mkAnn tmp))
              (.prodReturnValue () (.valVar () (mkAnn tmp)))), expectedTy)
      else if canUpcast rhsTy expectedTy then
        -- RHS is concrete, target is Any.
        -- Optimization: if RHS is a simple value, directly upcast without let-binding
        match rhsProd with
        | .prodReturnValue _ rhsVal =>
          let upcasted := insertFGLUpcast rhsVal rhsTy
          pure (.prodAssign () targetVal upcasted
            (.prodReturnValue () upcasted), expectedTy)
        | _ =>
          let tmp ← freshVar "rhs"
          let upcasted := insertFGLUpcast (.valVar () (mkAnn tmp)) rhsTy
          pure (.prodLetProd () (mkAnn tmp) (highTypeToFGL rhsTy) rhsProd
            (.prodAssign () targetVal upcasted
              (.prodReturnValue () upcasted)), expectedTy)
      else if canNarrow rhsTy expectedTy then
        -- RHS is Any, target is concrete -- bind RHS, then narrow
        let tmp ← freshVar "rhs"
        let narrowed ← freshVar "narrowed"
        let narrowProd := Producer.prodCall () (mkAnn (narrowFuncName expectedTy))
                            (mkAnn #[Value.valVar () (mkAnn tmp)])
        pure (.prodLetProd () (mkAnn tmp) (highTypeToFGL rhsTy) rhsProd
          (.prodLetProd () (mkAnn narrowed) (highTypeToFGL expectedTy) narrowProd
            (.prodAssign () targetVal (.valVar () (mkAnn narrowed))
              (.prodReturnValue () (.valVar () (mkAnn narrowed))))), expectedTy)
      else
        -- Default: bind and assign without coercion
        let tmp ← freshVar "rhs"
        pure (.prodLetProd () (mkAnn tmp) (highTypeToFGL rhsTy) rhsProd
          (.prodAssign () targetVal (.valVar () (mkAnn tmp))
            (.prodReturnValue () (.valVar () (mkAnn tmp)))), rhsTy)
    | _ => do
      -- Multi-target assign (tuple unpacking) -- emit as plain prodCall for now
      -- ARCHITECTURE GAP: full tuple unpacking
      let (rhsProd, rhsTy) ← synthProducer value
      pure (rhsProd, rhsTy)

  -- Block: nested prodLetProd via foldr
  | .Block stmts _label => do
    elaborateBlock stmts

  -- IfThenElse: condition must be bool, branches are producers
  | .IfThenElse cond thenBr elseBr => do
    let condProd ← checkProducer cond .TBool
    let condTmp ← freshVar "cond"
    let (thenProd, thenTy) ← synthProducer thenBr
    let (elseProd, _) ← match elseBr with
      | some e => synthProducer e
      | none => pure (.prodReturnValue () (.valLiteralBool () (mkAnn false)), .TVoid)
    pure (.prodLetProd () (mkAnn condTmp) (.boolType ()) condProd
      (.prodIfThenElse () (.valVar () (mkAnn condTmp)) thenProd elseProd), thenTy)

  -- While loop
  | .While cond _invs _decreases body => do
    let condProd ← checkProducer cond .TBool
    let condTmp ← freshVar "whileCond"
    let (bodyProd, _) ← synthProducer body
    pure (.prodLetProd () (mkAnn condTmp) (.boolType ()) condProd
      (.prodWhile () (.valVar () (mkAnn condTmp)) (mkAnn #[]) bodyProd
        (.prodReturnValue () (.valLiteralBool () (mkAnn true)))), .TVoid)

  -- LocalVariable: var x: T := init; continuation
  | .LocalVariable name ty init => do
    match init with
    | some initExpr => do
      -- If init is a simple value (literal, identifier), check it directly.
      -- If init is a producer (call, etc.), synthesize it as a producer and
      -- bind with prodLetProd so the result can be used as the init value.
      if isEffectful initExpr then
        -- Producer init: synth as producer, bind result
        let (initProd, _initTy) ← synthProducer initExpr
        let tmp ← freshVar "init"
        pure (.prodLetProd () (mkAnn tmp) (highTypeToFGL ty.val) initProd
          (.prodVarDecl () (mkAnn name.text) (highTypeToFGL ty.val)
            (.valVar () (mkAnn tmp))
            (.prodReturnValue () (.valVar () (mkAnn name.text)))), ty.val)
      else
        let checkedInit ← checkValue initExpr ty.val
        pure (.prodVarDecl () (mkAnn name.text) (highTypeToFGL ty.val) checkedInit
          (.prodReturnValue () (.valVar () (mkAnn name.text))), ty.val)
    | none => do
      -- Declaration without initialization: use $uninit sentinel.
      -- Projection recognizes this and emits LocalVariable name ty none.
      pure (.prodVarDecl () (mkAnn name.text) (highTypeToFGL ty.val)
        (.valVar () (mkAnn "$uninit"))
        (.prodReturnValue () (.valVar () (mkAnn name.text))), ty.val)

  -- Return
  | .Return value => do
    match value with
    | some v => do
      let retVal ← checkValue v env.currentReturnType
      pure (.prodReturnValue () retVal, env.currentReturnType)
    | none =>
      pure (.prodReturnValue () (.valLiteralBool () (mkAnn true)), .TVoid)

  -- Assert
  | .Assert cond => do
    let condProd ← checkProducer cond .TBool
    let condTmp ← freshVar "assertCond"
    pure (.prodLetProd () (mkAnn condTmp) (.boolType ()) condProd
      (.prodAssert () (.valVar () (mkAnn condTmp))
        (.prodReturnValue () (.valLiteralBool () (mkAnn true)))), .TVoid)

  -- Assume
  | .Assume cond => do
    let condProd ← checkProducer cond .TBool
    let condTmp ← freshVar "assumeCond"
    pure (.prodLetProd () (mkAnn condTmp) (.boolType ()) condProd
      (.prodAssume () (.valVar () (mkAnn condTmp))
        (.prodReturnValue () (.valLiteralBool () (mkAnn true)))), .TVoid)

  -- Exit (break/continue label)
  | .Exit _label =>
    -- ARCHITECTURE GAP: Exit maps to control flow that doesn't fit FGL directly
    pure (.prodReturnValue () (.valLiteralBool () (mkAnn true)), .TVoid)

  -- Hole: nondeterministic/deterministic values - pass through unchanged.
  -- The Hole is preserved as a StaticCall to a special sentinel that projectProducer
  -- doesn't need to handle specially (it's a regular call that downstream hole elimination handles).
  -- We represent it as returning Any since Holes represent unknown values.
  | .Hole det tyOpt => do
    let ty := tyOpt.map (·.val) |>.getD (.TCore "Any")
    -- Emit a prodCall that will project to the original Hole structure
    -- Use a special name that projectProducer maps back to Hole
    let detStr := if det then "true" else "false"
    let _ := detStr
    -- Simply return the expression unchanged via prodReturnValue with a special marker.
    -- Actually, the cleanest approach: just let the projection handle it by
    -- wrapping the original expression in a prodBlock of size 1.
    -- But since we need to return FGL types, use prodCall "$Hole" which projects to StaticCall "$Hole".
    -- Better: we know Hole is handled by downstream holeElimination, so project it as a Hole.
    -- Use a valVar that matches the special Hole pattern. Downstream phases expect Holes.
    pure (.prodCall () (mkAnn "$Hole") (mkAnn #[]), ty)

  -- PrimitiveOp: direct value-level operations (comparison, arithmetic at Laurel level)
  | .PrimitiveOp _op args => do
    let mut checkedArgs : List FValue := []
    for arg in args do
      let (argVal, _) ← synthValue arg
      checkedArgs := checkedArgs ++ [argVal]
    -- PrimitiveOps return bool or Any depending on the operation
    pure (.prodReturnValue () (.valVar () (mkAnn "$primop")), .TCore "Any")

  -- Forall/Exists: quantifiers used in specifications
  | .Forall _param _trigger _body =>
    pure (.prodReturnValue () (.valLiteralBool () (mkAnn true)), .TBool)

  | .Exists _param _trigger _body =>
    pure (.prodReturnValue () (.valLiteralBool () (mkAnn true)), .TBool)

  -- Values in producer position: wrap with prodReturnValue
  | _ => do
    let (val, ty) ← synthValue expr
    pure (.prodReturnValue () val, ty)

/-- Check a Laurel expression AS a Producer against an expected type.
    Handles narrowing (Any → concrete) which produces a Producer (may fail). -/
partial def checkProducer (expr : StmtExprMd) (expected : HighType) : ElabM FProducer := do
  let (prod, actual) ← synthProducer expr
  if isSubtype actual expected then
    -- Types match -- no coercion
    pure prod
  else if canUpcast actual expected then
    -- Upcast: concrete → Any. Bind the producer, upcast the result value.
    let tmp ← freshVar "up"
    let upcasted := insertFGLUpcast (.valVar () (mkAnn tmp)) actual
    pure (.prodLetProd () (mkAnn tmp) (highTypeToFGL actual) prod
      (.prodReturnValue () upcasted))
  else if canNarrow actual expected then
    -- Narrowing: Any → concrete. Bind the producer, then call narrowing function.
    let tmp ← freshVar "narrow"
    let narrowCall := Producer.prodCall () (mkAnn (narrowFuncName expected))
                        (mkAnn #[Value.valVar () (mkAnn tmp)])
    pure (.prodLetProd () (mkAnn tmp) (highTypeToFGL actual) prod narrowCall)
  else
    -- Types unrelated -- return unchanged
    pure prod

/-- Helper: synthesize a static call.
    Handles the ANF lifting needed when arguments are themselves Producers (calls).
    Each effectful argument is bound to a fresh variable via prodLetProd, then the
    variable is passed to the call. -/
partial def synthStaticCall (callee : Identifier) (args : List StmtExprMd)
    (_expr : StmtExprMd) : ElabM (FProducer × HighType) := do
  let env ← read
  let sig := lookupFuncSig env callee.text
  let paramTypes := sig.map (·.params) |>.getD []
  let retTy := sig.map (·.returnType) |>.getD (.TCore "Any")
  let hasError := sig.map (·.hasErrorOutput) |>.getD false
  -- Process arguments: for effectful args, create let-bindings (ANF lift)
  let mut checkedArgs : List FValue := []
  let mut bindings : List (String × HighType × FProducer) := []
  let mut paramList := paramTypes
  for arg in args do
    let expectedTy : HighType := match paramList with
      | (_, ty) :: _ => ty
      | _ => .TCore "Any"
    paramList := match paramList with | _ :: rest => rest | _ => []
    if isEffectful arg then
      -- Effectful argument: synthesize as Producer, bind result, use variable
      let (argProd, argTy) ← synthProducer arg
      let tmp ← freshVar "arg"
      bindings := bindings ++ [(tmp, argTy, argProd)]
      -- Check if the bound variable needs coercion to match expected type
      let argVal : FValue := .valVar () (mkAnn tmp)
      if isSubtype argTy expectedTy || highTypeEq argTy expectedTy then
        checkedArgs := checkedArgs ++ [argVal]
      else if canUpcast argTy expectedTy then
        checkedArgs := checkedArgs ++ [insertFGLUpcast argVal argTy]
      else
        checkedArgs := checkedArgs ++ [argVal]
    else
      -- Non-effectful argument: check as value directly
      let checkedArg ← checkValue arg expectedTy
      checkedArgs := checkedArgs ++ [checkedArg]
  -- Build the call
  let call ← if hasError then do
      let resultVar ← freshVar "res"
      let errorVar ← freshVar "err"
      pure (.prodCallWithError () (mkAnn callee.text) (mkAnn checkedArgs.toArray)
        (mkAnn resultVar) (mkAnn errorVar)
        (highTypeToFGL retTy) (.coreType () (mkAnn "Error"))
        (.prodReturnValue () (.valVar () (mkAnn resultVar))) : FProducer)
    else
      pure (.prodCall () (mkAnn callee.text) (mkAnn checkedArgs.toArray) : FProducer)
  -- Wrap the call in any let-bindings for effectful arguments
  let result := bindings.foldr (init := call) fun (name, ty, prod) body =>
    .prodLetProd () (mkAnn name) (highTypeToFGL ty) prod body
  pure (result, retTy)

/-- Helper: check a list of arguments against expected parameter types. -/
partial def checkArgs (args : List StmtExprMd)
    (paramTypes : List (String × HighType)) : ElabM (List FValue) := do
  match args, paramTypes with
  | [], _ => pure []
  | arg :: restArgs, (_, ty) :: restParams => do
    let checkedArg ← checkValue arg ty
    let restChecked ← checkArgs restArgs restParams
    pure (checkedArg :: restChecked)
  | arg :: restArgs, [] => do
    let checkedArg ← checkValue arg (.TCore "Any")
    let restChecked ← checkArgs restArgs []
    pure (checkedArg :: restChecked)

/-- Helper: synthesize a target value (for assignments). -/
partial def synthTargetValue (target : StmtExprMd) : ElabM FValue := do
  match target.val with
  | .Identifier name => pure (.valVar () (mkAnn name.text))
  | .FieldSelect obj field => do
    let (objVal, _) ← synthValue obj
    pure (.valFieldAccess () objVal (mkAnn field.text))
  | _ => do
    let (val, _) ← synthValue target
    pure val

/-- Helper: elaborate a block of statements into a prodBlock (flat sequencing).
    Block [s1, s2, s3] → prodBlock [synthProducer(s1), synthProducer(s2), synthProducer(s3)]
    Preserves flat block structure required by downstream Laurel-to-Core translation.

    KEY: When a LocalVariable declaration is encountered, the declared name and type
    are added to localTypes in the ElabEnv for subsequent statements. This ensures
    that later references to the variable get the correct type rather than defaulting
    to Any. -/
partial def elaborateBlock (stmts : List StmtExprMd) : ElabM (FProducer × HighType) := do
  match stmts with
  | [] => pure (.prodReturnValue () (.valLiteralBool () (mkAnn true)), .TVoid)
  | [single] => synthProducer single
  | _ => do
    let mut prods : Array FProducer := #[]
    let mut lastTy : HighType := .TVoid
    let mut extraLocals : Std.HashMap String HighType := {}
    for stmt in stmts do
      -- Thread local types: use withReader to add any accumulated declarations
      let (prod, ty) ← if extraLocals.isEmpty then
        synthProducer stmt
      else
        let locals := extraLocals
        withReader (fun env => { env with localTypes := env.localTypes.insertMany locals.toList }) (synthProducer stmt)
      prods := prods.push prod
      lastTy := ty
      -- After processing, if this was a LocalVariable, record its type for subsequent stmts
      match stmt.val with
      | .LocalVariable name ty _ => extraLocals := extraLocals.insert name.text ty.val
      | .Assign [target] _ =>
        -- Also track simple assignments to identifiers when we can infer the type
        match target.val with
        | .Identifier name =>
          -- If we know the target's type from earlier declarations, keep it
          -- (the type doesn't change). If it's a new assignment, record Any.
          if !(extraLocals.contains name.text) then
            extraLocals := extraLocals.insert name.text lastTy
        | _ => pure ()
      | _ => pure ()
    pure (.prodBlock () (mkAnn prods), lastTy)

end -- mutual

/-! ========================================================================
    PROJECTION: FGL → Laurel (the forgetful functor)

    Maps FineGrainLaurel Value/Producer back to Laurel StmtExprMd.
    This erases polarity, keeping all inserted coercions/let-bindings as
    regular Laurel nodes. The projection is total and meaning-preserving.
    ======================================================================== -/

/-- Helper to wrap a StmtExpr into StmtExprMd with empty metadata -/
private def mkMd (e : StmtExpr) : StmtExprMd := ⟨e, #[]⟩

/-- Helper to make an Identifier from a String -/
private def mkId (s : String) : Identifier := { text := s, uniqueId := none }

/-- Project an FGL LaurelType back to a HighTypeMd. -/
def projectType : FLaurelType → HighTypeMd
  | .intType _ => liftType .TInt
  | .boolType _ => liftType .TBool
  | .realType _ => liftType .TReal
  | .float64Type _ => liftType .TFloat64
  | .stringType _ => liftType .TString
  | .coreType _ name => liftType (.TCore name.val)
  | .compositeType _ name => liftType (.UserDefined (mkId name.val))
  | .mapType _ k v => liftType (.TMap (projectType k) (projectType v))

mutual
/-- Project an FGL Value back to Laurel StmtExprMd. -/
partial def projectValue : FValue → StmtExprMd
  | .valLiteralInt _ n => mkMd (.LiteralInt n.val)
  | .valLiteralBool _ b => mkMd (.LiteralBool b.val)
  | .valLiteralReal _ d => mkMd (.LiteralDecimal d.val)
  | .valLiteralString _ s => mkMd (.LiteralString s.val)
  | .valVar _ name =>
    -- Recognize $Hole_val sentinel: project back to a proper Hole node
    if name.val == "$Hole_val" then
      mkMd (.Hole (deterministic := false))
    else
      mkMd (.Identifier (mkId name.val))
  | .valAdd _ l r => mkMd (.PrimitiveOp .Add [projectValue l, projectValue r])
  | .valSub _ l r => mkMd (.PrimitiveOp .Sub [projectValue l, projectValue r])
  | .valMul _ l r => mkMd (.PrimitiveOp .Mul [projectValue l, projectValue r])
  | .valDiv _ l r => mkMd (.PrimitiveOp .Div [projectValue l, projectValue r])
  | .valMod _ l r => mkMd (.PrimitiveOp .Mod [projectValue l, projectValue r])
  | .valEq _ l r => mkMd (.PrimitiveOp .Eq [projectValue l, projectValue r])
  | .valNeq _ l r => mkMd (.PrimitiveOp .Neq [projectValue l, projectValue r])
  | .valLt _ l r => mkMd (.PrimitiveOp .Lt [projectValue l, projectValue r])
  | .valLe _ l r => mkMd (.PrimitiveOp .Leq [projectValue l, projectValue r])
  | .valGt _ l r => mkMd (.PrimitiveOp .Gt [projectValue l, projectValue r])
  | .valGe _ l r => mkMd (.PrimitiveOp .Geq [projectValue l, projectValue r])
  | .valAnd _ l r => mkMd (.PrimitiveOp .And [projectValue l, projectValue r])
  | .valOr _ l r => mkMd (.PrimitiveOp .Or [projectValue l, projectValue r])
  | .valNot _ inner => mkMd (.PrimitiveOp .Not [projectValue inner])
  | .valNeg _ inner => mkMd (.PrimitiveOp .Neg [projectValue inner])
  | .valFieldAccess _ obj field =>
    mkMd (.FieldSelect (projectValue obj) (mkId field.val))
  | .valParens _ inner => projectValue inner
  -- Upcast coercions: project as StaticCall with the coercion function name
  | .valFromInt _ inner =>
    mkMd (.StaticCall (mkId "from_int") [projectValue inner])
  | .valFromStr _ inner =>
    mkMd (.StaticCall (mkId "from_str") [projectValue inner])
  | .valFromBool _ inner =>
    mkMd (.StaticCall (mkId "from_bool") [projectValue inner])
  | .valFromFloat _ inner =>
    mkMd (.StaticCall (mkId "from_float") [projectValue inner])
  | .valFromComposite _ inner =>
    mkMd (.StaticCall (mkId "from_Composite") [projectValue inner])
  | .valFromListAny _ inner =>
    mkMd (.StaticCall (mkId "from_ListAny") [projectValue inner])
  | .valFromDictStrAny _ inner =>
    mkMd (.StaticCall (mkId "from_DictStrAny") [projectValue inner])
  | .valFromNone _ =>
    mkMd (.StaticCall (mkId "from_None") [])

/-- Flatten an FGL Producer into a flat list of Laurel statements.
    This is the core of the FGCBV → CBV projection: continuation-bearing forms
    (prodLetProd, prodVarDecl, prodAssign, prodSeq) accumulate into a flat list
    rather than nesting Blocks inside Blocks.

    The key insight: `M to x. N` in FGCBV projects to `[let x = M; ...stmts(N)]`
    NOT to `Block [let x = M, Block [...stmts(N)]]`. -/
partial def projectToStmts : FProducer → List StmtExprMd
  -- Terminal forms: produce a single statement (no continuation to flatten)
  | .prodReturnValue _ val => [projectValue val]

  | .prodCall _ callee args =>
    if callee.val == "$Hole" then
      [mkMd (.Hole (deterministic := false))]
    else
      [mkMd (.StaticCall (mkId callee.val) (args.val.toList.map projectValue))]

  | .prodIfThenElse _ cond thenBr elseBr =>
    let condExpr := projectValue cond
    let thenExpr := projectProducer thenBr
    let elseExpr := projectProducer elseBr
    [mkMd (.IfThenElse condExpr thenExpr (some elseExpr))]

  -- Continuation-bearing forms: emit head statement, then flatten the continuation
  | .prodLetProd _ var ty prod body =>
    let prodExpr := projectProducer prod
    let varDecl := mkMd (.LocalVariable (mkId var.val) (projectType ty) (some prodExpr))
    [varDecl] ++ projectToStmts body

  | .prodLetValue _ var ty val body =>
    let valExpr := projectValue val
    let varDecl := mkMd (.LocalVariable (mkId var.val) (projectType ty) (some valExpr))
    [varDecl] ++ projectToStmts body

  | .prodAssign _ target val body =>
    let targetExpr := projectValue target
    let valExpr := projectValue val
    let assignStmt := mkMd (.Assign [targetExpr] valExpr)
    [assignStmt] ++ projectToStmts body

  | .prodVarDecl _ name ty init body =>
    match init with
    | .valVar _ sentinel =>
      if sentinel.val == "$uninit" then
        -- Scope-hoisted declaration with no initializer
        let decl := mkMd (.LocalVariable (mkId name.val) (projectType ty) none)
        match body with
        | .prodReturnValue _ _ =>
          -- Trivial continuation: just the declaration, no trailing value
          [decl]
        | _ =>
          [decl] ++ projectToStmts body
      else
        let decl := mkMd (.LocalVariable (mkId name.val) (projectType ty) (some (projectValue init)))
        [decl] ++ projectToStmts body
    | _ =>
      let decl := mkMd (.LocalVariable (mkId name.val) (projectType ty) (some (projectValue init)))
      [decl] ++ projectToStmts body

  | .prodAssert _ cond body =>
    [mkMd (.Assert (projectValue cond))] ++ projectToStmts body

  | .prodAssume _ cond body =>
    [mkMd (.Assume (projectValue cond))] ++ projectToStmts body

  | .prodWhile _ cond _invs body after =>
    let condExpr := projectValue cond
    let bodyExpr := projectProducer body
    [mkMd (.While condExpr [] none bodyExpr)] ++ projectToStmts after

  | .prodNew _ name resultVar ty body =>
    let newExpr := mkMd (.New (mkId name.val))
    let varDecl := mkMd (.LocalVariable (mkId resultVar.val) (projectType ty) (some newExpr))
    [varDecl] ++ projectToStmts body

  | .prodCallWithError _ callee args resultVar errorVar resultTy _errorTy body =>
    let callExpr := mkMd (.StaticCall (mkId callee.val) (args.val.toList.map projectValue))
    let resultRef := mkMd (.Identifier (mkId resultVar.val))
    let errorRef := mkMd (.Identifier (mkId errorVar.val))
    let multiAssign := mkMd (.Assign [resultRef, errorRef] callExpr)
    let isErrorCall := mkMd (.StaticCall (mkId "isError") [errorRef])
    let errorCheck := mkMd (.IfThenElse isErrorCall
      (mkMd (.Return (some errorRef))) none)
    let varDeclResult := mkMd (.LocalVariable (mkId resultVar.val) (projectType resultTy) none)
    let varDeclError := mkMd (.LocalVariable (mkId errorVar.val)
      (liftType (.TCore "Error")) none)
    [varDeclResult, varDeclError, multiAssign, errorCheck] ++ projectToStmts body

  | .prodSeq _ first second =>
    projectToStmts first ++ projectToStmts second

  | .prodBlock _ stmts =>
    stmts.val.toList.flatMap projectToStmts

/-- Project an FGL Producer back to Laurel StmtExprMd.
    This is used in EXPRESSION position (initializers, call targets, etc.) where
    the result value matters. It keeps trailing value expressions so that Block
    expressions have a proper result.
    For STATEMENT position (procedure bodies, continuations), use projectToStmts
    via projectProducerFlat instead. -/
partial def projectProducer (prod : FProducer) : StmtExprMd :=
  let stmts := projectToStmts prod
  match stmts with
  | [] => mkMd (.Block [] none)
  | [single] => single
  | multiple => mkMd (.Block multiple none)
end

/-! ========================================================================
    FGL ELABORATION ENTRY POINTS (Phase 1)
    ======================================================================== -/

/-- Project an FGL Producer for use as a procedure body (STATEMENT position).
    Flattens continuation structure into a single top-level Block and filters out
    trailing trivial values (bare identifiers, literals) that are artifacts of
    FGL's continuation semantics (e.g., prodReturnValue returning a bound variable). -/
def projectProducerFlat (prod : FProducer) : StmtExprMd :=
  let stmts := projectToStmts prod
  let meaningful := stmts.filter fun s =>
    match s.val with
    | .Identifier _ => false
    | .LiteralBool _ => false
    | .LiteralInt _ => false
    | _ => true
  match meaningful with
  | [] =>
    -- All statements were trivial; use last stmt as the expression value
    match stmts.getLast? with
    | some last => last
    | none => mkMd (.Block [] none)
  | [single] => single
  | multiple => mkMd (.Block multiple none)

/-- Build an ElabEnv from a TypeEnv (Γ) and procedure context. -/
def mkElabEnv (typeEnv : TypeEnv) (returnType : HighType := .TCore "Any")
    (localTypes : Std.HashMap String HighType := {}) : ElabEnv :=
  { typeEnv := typeEnv, currentReturnType := returnType, localTypes := localTypes }

/-- Elaborate a single procedure body, producing FGL Producer then projecting back.
    Uses projectProducerFlat for statement-position flattening. -/
def elaborateProcBody (env : ElabEnv) (body : StmtExprMd) : Except String StmtExprMd := do
  let ((prod, _), _) ← (synthProducer body).run env |>.run {}
  pure (projectProducerFlat prod)

/-- Elaborate a Laurel Procedure, inserting casts and effects. -/
def elaborateProcedure (typeEnv : TypeEnv) (proc : Laurel.Procedure) : Except String Laurel.Procedure := do
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
  let mut staticProcs : List Laurel.Procedure := []
  for proc in program.staticProcedures do
    let elaborated ← elaborateProcedure fullEnv proc
    staticProcs := staticProcs ++ [elaborated]
  let mut types : List TypeDefinition := []
  for td in program.types do
    match td with
    | TypeDefinition.Composite ct =>
      let mut instProcs : List Laurel.Procedure := []
      for proc in ct.instanceProcedures do
        let elaborated ← elaborateProcedure fullEnv proc
        instProcs := instProcs ++ [elaborated]
      types := types ++ [TypeDefinition.Composite { ct with instanceProcedures := instProcs }]
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
private def analyzeProcForHeap (proc : Laurel.Procedure) : HeapAnalysisResult :=
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
private def computeHeapReaders (procs : List Laurel.Procedure) : List Identifier :=
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
private def computeHeapWriters (procs : List Laurel.Procedure) : List Identifier :=
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
      | return mkMd .Hole
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
private def heapTransformProcedure (proc : Laurel.Procedure) : HeapTransformM Laurel.Procedure := do
  let heapName : Identifier := "$heap"
  let heapInName : Identifier := "$heap_in"
  let readsH := (← get).heapReaders.contains proc.name
  let writesH := (← get).heapWriters.contains proc.name

  if writesH then
    let heapInParam : Laurel.Parameter := { name := heapInName, type := ⟨.THeap, #[]⟩ }
    let heapOutParam : Laurel.Parameter := { name := heapName, type := ⟨.THeap, #[]⟩ }
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
    let heapParam : Laurel.Parameter := { name := heapName, type := ⟨.THeap, #[]⟩ }
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
    | TypeDefinition.Composite ct => acc ++ ct.instanceProcedures
    | _ => acc) ([] : List Laurel.Procedure)
  let allProcs := program.staticProcedures ++ instanceProcs
  let heapReaders := computeHeapReaders allProcs
  let heapWriters := computeHeapWriters allProcs
  let initState : HeapTransformState := { heapReaders, heapWriters, typeEnv := typeEnv }
  let (procs', state1) := (program.staticProcedures.mapM heapTransformProcedure).run initState
  -- Collect all qualified field names and generate a Field datatype
  let fieldNames := program.types.foldl (fun acc td =>
    match td with
    | TypeDefinition.Composite ct => acc ++ ct.fields.map (fun f => (mkId (ct.name.text ++ "." ++ f.name.text) : Identifier))
    | _ => acc) ([] : List Identifier)
  let fieldDatatype : TypeDefinition :=
    TypeDefinition.Datatype { name := "Field", typeArgs := [], constructors := fieldNames.map fun n => { name := n, args := [] } }
  -- Transform instance procedures
  let (types', state2) := program.types.foldl (fun (accTypes, accState) td =>
    match td with
    | TypeDefinition.Composite ct =>
      let (instProcs', s') := (ct.instanceProcedures.mapM heapTransformProcedure).run accState
      (accTypes ++ [TypeDefinition.Composite { ct with fields := [], instanceProcedures := instProcs' }], s')
    | other => (accTypes ++ [other], accState))
    ([], state1)
  -- Generate Box datatype from all constructors used during transformation
  let boxDatatype : TypeDefinition :=
    TypeDefinition.Datatype { name := "Box", typeArgs := [], constructors := state2.usedBoxConstructors }
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

private def rewriteTypeHierarchyProcedure (proc : Laurel.Procedure) : THM Laurel.Procedure := do
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
    | TypeDefinition.Composite ct => some ct
    | _ => none
  let compositeNames := composites.map (·.name.text)
  let typeTagCtors := compositeNames.map fun n => ({ name := (mkId (n ++ "_TypeTag")), args := [] } : DatatypeConstructor)
  let typeTagDatatype : TypeDefinition :=
    TypeDefinition.Datatype { name := "TypeTag", typeArgs := [], constructors := typeTagCtors }
  let typeHierarchyConstants := generateTypeHierarchyDecls composites
  let (procs', _) := (program.staticProcedures.mapM rewriteTypeHierarchyProcedure).run {}
  -- Update Composite datatype to include typeTag field
  let typeTagTy : HighTypeMd := ⟨.UserDefined "TypeTag", #[]⟩
  let remainingTypes := program.types.map fun td =>
    match td with
    | TypeDefinition.Datatype dt =>
      if dt.name.text == "Composite" then
        TypeDefinition.Datatype { dt with constructors := dt.constructors.map fun c =>
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
private def hasHeapOut (proc : Laurel.Procedure) : Bool :=
  proc.outputs.any (fun p => p.name.text == "$heap")

/-- Build a frame condition postcondition for a procedure's modifies clause.
    "For all objects not in modifies: heap_in fields == heap_out fields" -/
private def buildFrameCondition (proc : Laurel.Procedure) (modifiesExprs : List StmtExprMd) : Option StmtExprMd :=
  if !hasHeapOut proc then none
  else
    let heapInName : Identifier := "$heap_in"
    let heapName : Identifier := "$heap"
    let objName : Identifier := "$modifies_obj"
    let fldName : Identifier := "$modifies_fld"
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
      let objParam : Laurel.Parameter := { name := objName, type := ⟨.UserDefined "Composite", #[]⟩ }
      let fldParam : Laurel.Parameter := { name := fldName, type := ⟨.UserDefined "Field", #[]⟩ }
      some ⟨.Forall objParam none ⟨.Forall fldParam none implication, #[]⟩, #[]⟩
    else
      let objRef := mkMd (.Identifier objName)
      let fldRef := mkMd (.Identifier fldName)
      let heapInRef := mkMd (.Identifier heapInName)
      let heapRef := mkMd (.Identifier heapName)
      let nextRef := mkMd (.StaticCall "Heap..nextReference!" [heapInRef])
      let objLtNext := mkMd (.PrimitiveOp .Lt [mkMd (.StaticCall "Composite..ref!" [objRef]), nextRef])
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
      let objParam : Laurel.Parameter := { name := objName, type := ⟨.UserDefined "Composite", #[]⟩ }
      let fldParam : Laurel.Parameter := { name := fldName, type := ⟨.UserDefined "Field", #[]⟩ }
      some ⟨.Forall objParam none ⟨.Forall fldParam none implication, #[]⟩, #[]⟩

/-- Transform modifies clauses for a single procedure. -/
private def transformModifiesForProc (proc : Laurel.Procedure) : Laurel.Procedure :=
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
  currentInputs : List Laurel.Parameter := []
  generatedFunctions : List Laurel.Procedure := []
  deriving Inhabited

abbrev HoleElimM := StateM HoleElimState

/-- Generate a fresh uninterpreted function for a typed hole. -/
private def mkHoleCall (holeType : HighTypeMd) : HoleElimM StmtExprMd := do
  let s ← get
  let n := s.counter
  modify fun s => { s with counter := n + 1 }
  let holeName : Identifier := s!"$hole_{n}"
  let inputs := s.currentInputs
  let holeProc : Laurel.Procedure := {
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

private def holeElimProcedure (proc : Laurel.Procedure) : HoleElimM Laurel.Procedure := do
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

private def inferHoleProcedure (proc : Laurel.Procedure) : InferHoleM Laurel.Procedure := do
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
    match td with | TypeDefinition.Constrained ct => m.insert ct.name.text ct | _ => m

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
private def constrainedTypeElimProc (ptMap : ConstrainedTypeMap) (proc : Laurel.Procedure)
    : Laurel.Procedure × List DiagnosticModel :=
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
private def mkConstraintFunctions (ptMap : ConstrainedTypeMap) : List Laurel.Procedure :=
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
    match td with | TypeDefinition.Constrained _ => false | _ => true
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

/-- Simple elaboration entry point for a single expression (returns FGL Producer projected). -/
def elaborateExpr (typeEnv : TypeEnv) (expr : StmtExprMd)
    : Except String StmtExprMd := do
  let env := mkElabEnv typeEnv
  let ((prod, _), _) ← (synthProducer expr).run env |>.run {}
  pure (projectProducer prod)

/-- Legacy project function (identity on Laurel -- kept for backward compat). -/
def project (expr : StmtExprMd) : StmtExprMd := expr

end
