/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Tripod.ClassicalAbc
import Iut.Tripod.GeneralPosition

/-!
# The classical ABC conjecture from the Corollary 3.12 variant

`Iut.Tripod.classicalABC_of_variant_of_statementII_imp_I` derives the classical ABC conjecture
from the Corollary 3.12 variant, conditionally on the passage
`tripodTheory.StatementII → tripodTheory.StatementI` ([GenEll], Theorem 2.1 (ii) ⇒ (i) for the
tripod). That passage is now a theorem, `Iut.Tripod.statementI_of_statementII`, so the
condition disappears. The hypotheses `hcyc` and `h312` are unchanged: they are exactly those of
`Iut.Tripod.abc_of_variant`.
-/

namespace Iut.Tripod

section Variant

open Iut.EllipticCurveData Iut.Anabelian Iut.LocalConstruct

/-- **The Corollary 3.12 variant implies the classical ABC conjecture**, with the hypotheses
`hcyc` and `h312` of `Iut.Tripod.abc_of_variant` and no further condition: the passage from
compactly bounded subsets to all points of bounded degree is
`Iut.Tripod.statementI_of_statementII`. -/
theorem classicalABC_of_variant
    (Pi1 : EtalePi1Theory.{0}) (Tp : TemperedPi1Theory Pi1)
    (hcyc : ∀ (K : CompactlyBounded) (d : ℕ),
      ∃ TK : ℝ, CyclicGraphBoundHyp (tripodProviders) K d TK)
    (h312 : ∀ (D : InitialThetaData (modelAG Pi1) (modelTG Pi1 Tp)) (LT : LocalTheory.{0, 0} D.Kt)
      (TL : ThetaLocalData D LT) (QI : QPilotInputs D),
      Corollary312Variant (concreteVariantData.{0, 0} D LT TL QI)) :
    ClassicalABC :=
  classicalABC_of_variant_of_statementII_imp_I Pi1 Tp statementI_of_statementII hcyc h312

end Variant

end Iut.Tripod
