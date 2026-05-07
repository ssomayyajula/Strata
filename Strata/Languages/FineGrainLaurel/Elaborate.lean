/-
  Copyright Strata Contributors
  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.Languages.FineGrainLaurel.FineGrainLaurel
public import Strata.Languages.Laurel.Laurel
public import Strata.Languages.Laurel.HeapParameterizationConstants
public import Strata.Languages.Python.NameResolution

namespace Strata.FineGrainLaurel
open Strata.Laurel
open Strata.Python.Resolution
public section

def mkLaurel (md : Imperative.MetaData Core.Expression) (e : StmtExpr) : StmtExprMd :=
  { val := e, md := md }
def mkHighTypeMd (md : Imperative.MetaData Core.Expression) (ty : HighType) : HighTypeMd :=
  { val := ty, md := md }

-- Step 1: Grade Infrastructure (ARCHITECTURE_V2 §"The Grade Monoid")

inductive Grade where
  | pure | err | heap | heapErr
  deriving Inhabited, BEq, Repr

def Grade.mul : Grade → Grade → Grade
  | .pure, e => e
  | e, .pure => e
  | .err, .heap => .heapErr
  | .heap, .err => .heapErr
  | .err, .err => .err
  | .heap, .heap => .heap
  | .heapErr, _ => .heapErr
  | _, .heapErr => .heapErr

def Grade.le : Grade → Grade → Bool
  | .pure, _ => true
  | .err, .err => true
  | .err, .heapErr => true
  | .heap, .heap => true
  | .heap, .heapErr => true
  | .heapErr, .heapErr => true
  | _, _ => false

def Grade.residual : Grade → Grade → Option Grade
  | .pure, e => some e
  | .err, .err => some .pure
  | .err, .heapErr => some .heap
  | .heap, .heap => some .pure
  | .heap, .heapErr => some .err
  | .heapErr, .heapErr => some .pure
  | _, _ => none

inductive ConventionWitness where
  | pureCall | errorCall | heapCall | heapErrorCall
  deriving Inhabited, Repr

def subgrade : Grade → Grade → Option ConventionWitness
  | .pure, _ => some .pureCall
  | .err, .err => some .errorCall
  | .err, .heapErr => some .errorCall
  | .heap, .heap => some .heapCall
  | .heap, .heapErr => some .heapCall
  | .heapErr, .heapErr => some .heapErrorCall
  | _, _ => none

-- Placeholder: rest of elaborator will follow plan steps 2-7
-- For now, provide the minimal API that the pipeline expects.

inductive LowType where
  | TInt | TBool | TString | TFloat64 | TVoid | TCore (name : String)
  deriving Inhabited, Repr, BEq

def eraseType : HighType → LowType
  | .TInt => .TInt | .TBool => .TBool | .TString => .TString
  | .TFloat64 => .TFloat64 | .TVoid => .TVoid | .TCore n => .TCore n
  | .UserDefined _ => .TCore "Composite" | .THeap => .TCore "Heap"
  | .TReal => .TCore "real" | .TTypedField _ => .TCore "Field"
  | .TSet _ | .TMap _ _ | .Applied _ _ | .Intersection _ | .Unknown => .TCore "Any"
  | .Pure _ => .TCore "Composite"

def liftType : LowType → HighType
  | .TInt => .TInt | .TBool => .TBool | .TString => .TString
  | .TFloat64 => .TFloat64 | .TVoid => .TVoid | .TCore n => .TCore n

-- Minimal fullElaborate stub so the pipeline compiles.
-- Will be replaced by the real implementation in subsequent steps.

def fullElaborate (typeEnv : TypeEnv) (program : Laurel.Program) : Except String Laurel.Program := do
  pure program

end
end Strata.FineGrainLaurel
