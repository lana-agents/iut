/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Tripod.ClassicalAbc
import Iut.Tripod.GeneralPosition
import Iut.Tripod.Main

/-!
# The main theorem: the Corollary 3.12 variant implies the classical ABC conjecture
-/

namespace Iut

/-- **The Corollary 3.12 variant implies the classical ABC conjecture.** -/
theorem classicalABC_of_variant
    (h312 : Cor312VariantHolds) : ClassicalABC :=
  Tripod.classicalABC_of_statementI (Tripod.statementI_of_statementII (Tripod.abc_of_variant h312))

end Iut
