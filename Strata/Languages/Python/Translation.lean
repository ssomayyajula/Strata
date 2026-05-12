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
# Pass 2: Translation

Fold over the resolved Python AST. Reads annotations on each node,
emits corresponding Laurel constructs. No name resolution, no lookups.

Input:  Array (Python.stmt ResolvedAnn)
Output: Laurel.Program
-/

namespace Strata.Python.Translation

open Strata.Laurel hiding Identifier
open Strata.Python.Resolution

public section

-- ═══════════════════════════════════════════════════════════════════════════════
-- Python Name → Laurel Name mapping (builtins)
-- ═══════════════════════════════════════════════════════════════════════════════

def pythonNameToLaurel : String → String
  | "len" => "Any_len_to_Any"
  | "str" => "to_string_any"
  | "int" => "to_int_any"
  | "float" => "to_float_any"
  | "bool" => "Any_to_bool"
  | "abs" => "Any_abs_to_Any"
  | "print" => "print"
  | "repr" => "to_string_any"
  | "type" => "Any_type_to_Any"
  | "isinstance" => "Any_isinstance_to_bool"
  | "hasattr" => "Any_hasattr_to_bool"
  | "getattr" => "Any_getattr_to_Any"
  | "setattr" => "Any_setattr_to_Any"
  | "sorted" => "Any_sorted_to_Any"
  | "reversed" => "Any_reversed_to_Any"
  | "enumerate" => "Any_enumerate_to_Any"
  | "zip" => "Any_zip_to_Any"
  | "range" => "Any_range_to_Any"
  | "list" => "Any_list_to_Any"
  | "dict" => "Any_dict_to_Any"
  | "set" => "Any_set_to_Any"
  | "tuple" => "Any_tuple_to_Any"
  | "min" => "Any_min_to_Any"
  | "max" => "Any_max_to_Any"
  | "sum" => "Any_sum_to_Any"
  | "any" => "Any_any_to_bool"
  | "all" => "Any_all_to_bool"
  | "ord" => "Any_ord_to_Any"
  | "chr" => "Any_chr_to_Any"
  | "map" => "Any_map_to_Any"
  | "filter" => "Any_filter_to_Any"
  | "timedelta" => "timedelta_func"
  | other => other

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
-- Translation Errors
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
-- Translation State + Monad
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
def currentBreakLabel : TransM (Option Laurel.Identifier) := do
  pure ((← get).loopLabels.head?.map fun p => p.1)
def currentContinueLabel : TransM (Option Laurel.Identifier) := do
  pure ((← get).loopLabels.head?.map fun p => p.2)

-- ═══════════════════════════════════════════════════════════════════════════════
-- Arg Matching
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Match positional args + kwargs against FuncSig params. Returns args in param order. -/
def matchArgs (sig : FuncSig) (posArgs : List StmtExprMd)
    (kwargs : List (String × StmtExprMd)) : List StmtExprMd :=
  let paramNames := sig.params.map (·.1)
  let numPos := posArgs.length
  let remainingParams := paramNames.drop numPos
  let kwargMatched := remainingParams.filterMap fun pName =>
    kwargs.find? (fun (k, _) => k == pName) |>.map (·.2)
  posArgs ++ kwargMatched

-- ═══════════════════════════════════════════════════════════════════════════════
-- The Fold (stub — to be filled in)
-- ═══════════════════════════════════════════════════════════════════════════════

-- TODO: implement the full fold over resolved AST
-- For now, produce an empty program to unblock the build

def translateModule (stmts : ResolvedPythonProgram) : TransM Laurel.Program := do
  pure { staticProcedures := [], staticFields := [], types := [], constants := [] }

-- ═══════════════════════════════════════════════════════════════════════════════
-- Runner
-- ═══════════════════════════════════════════════════════════════════════════════

def runTranslation (stmts : ResolvedPythonProgram)
    (filePath : String := "")
    : Except TransError (Laurel.Program × TransState) :=
  (translateModule stmts).run { filePath := filePath }

end -- public section
end Strata.Python.Translation
