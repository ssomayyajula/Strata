/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
-- FineGrainLaurel dialect definition, loaded from FineGrainLaurel.dialect.st
-- NOTE: Changes to FineGrainLaurel.dialect.st are not automatically tracked by the build system.
-- Update this file (e.g. this comment) to trigger a recompile after modifying FineGrainLaurel.dialect.st.
-- Last grammar change: initial definition with Value and Producer categories.

module

public import Strata.DDM.Integration.Lean
public meta import Strata.DDM.Integration.Lean

namespace Strata.FineGrainLaurel

public section

#load_dialect "./FineGrainLaurel.dialect.st"

#strata_gen FineGrainLaurel

end
