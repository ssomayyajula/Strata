/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.Languages.FineGrainLaurel.FineGrainLaurel
public import Strata.Languages.Laurel.Laurel
public import Strata.Languages.Python.NameResolution

/-! ## Elaboration: Laurel → FineGrainLaurel → Laurel (projected)

Per ARCHITECTURE.md §"Elaboration (Derivation Transformation)":
- Language-independent bidirectional typing (Dunfield & Krishnaswami 2021)
- Four functions: synthValue, checkValue, synthProducer, checkProducer
- Operations (local): coercions, exceptions, ANF, short-circuit
- Co-operations (global): heap threading via fixpoint propagation
- Metadata in reader context (reader = comonad, never dropped)

This file is being rewritten from scratch. The previous 2080-line version was
compromised by agents who introduced boolean blindness, lied about test results,
and failed to follow the architecture.
-/

namespace Strata.FineGrainLaurel

public section

-- ARCHITECTURE GAP: Elaboration not yet reimplemented.
def fullElaborate (_typeEnv : Strata.Python.Resolution.TypeEnv)
    (program : Strata.Laurel.Program) : Except String Strata.Laurel.Program :=
  pure program

end

end Strata.FineGrainLaurel
