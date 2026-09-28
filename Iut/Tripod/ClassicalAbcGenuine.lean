/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Tripod.ClassicalAbcOfVariant
import Iut.Anabelian.GenuineEtale

/-!
# The classical ABC conjecture from the Corollary 3.12 variant, over the genuine anabelian theory

`Iut.Tripod.classicalABC_of_variant` for the genuine étale theory
`Iut.Anabelian.genuinePi1Theory` (genuine arithmetic étale fundamental groups and genuine
`k`-cores of the model orbicurves) and the tempered theory `Iut.Anabelian.temperedTheory` over
it. The remaining hypotheses are [CanLift], Proposition 2.7 (`AffOrbicurve.CanLift27`), the
compatibility of cores with base change ([CanLift], Proposition 2.3,
`Iut.Anabelian.GenuineCoreBaseChange`), and the Corollary 3.12 variant `h312` for the Θ-data over
these theories (exactly the hypothesis of `Iut.Tripod.classicalABC_of_variant`).
-/

namespace Iut.Tripod

open Iut.EllipticCurveData Iut.Anabelian Iut.LocalConstruct

/-- **The Corollary 3.12 variant implies the classical ABC conjecture**, over the genuine étale
and tempered fundamental groups of the model orbicurves. -/
theorem classicalABC_of_variant_genuine (h27 : AffOrbicurve.CanLift27.{0})
    (hbc : GenuineCoreBaseChange.{0})
    (h312 : ∀ (D : InitialThetaData (modelAG (genuinePi1Theory h27 hbc))
        (modelTG (genuinePi1Theory h27 hbc) (temperedTheory (genuineEtaleData h27 hbc))))
      (LT : LocalTheory.{0, 0} D.Kt) (TL : ThetaLocalData D LT) (QI : QPilotInputs D),
      Corollary312Variant (concreteVariantData.{0, 0} D LT TL QI)) :
    ClassicalABC :=
  classicalABC_of_variant (genuinePi1Theory h27 hbc) (temperedTheory (genuineEtaleData h27 hbc))
    h312

end Iut.Tripod
