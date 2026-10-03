/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Tripod.ClassicalAbcGenuine
import OrbicurveCores.U2.Assembly
import Pi1.Orbicurve.LefschetzMain

/-!
# [CanLift], Proposition 2.7, and the classical ABC conjecture from the Corollary 3.12 variant

* `Iut.Anabelian.canLift27`: [CanLift], Proposition 2.7 (`AffOrbicurve.CanLift27`) over every
  field of characteristic `0`: the statement over `ℂ` (`OrbicurveCores.U2.canLift27C`, from
  `lana-agents/orbicurve-cores`) transported by the Lefschetz principle
  (`AffOrbicurve.canLift27_of_complex`, from `lana-agents/pi1`). The two packages state the
  complex case separately (`OrbicurveCores.CanLift27C` and `AffOrbicurve.CanLift27Complex`);
  the statements agree definitionally.
* `Iut.Tripod.classicalABC_of_variant_genuine'`: `Iut.Tripod.classicalABC_of_variant_genuine`
  with `h27 := Iut.Anabelian.canLift27`. The Corollary 3.12 variant hypothesis `h312` is the one
  of `classicalABC_of_variant_genuine` for that instance of `h27`, unchanged.
-/

namespace Iut.Anabelian

/-- **[CanLift], Proposition 2.7**: for an elliptic curve `E` over a field of characteristic `0`
with non-exceptional `j`-invariant, `(E ∖ {0}) / {±1}` is the core of `E ∖ {0}`. -/
theorem canLift27 : AffOrbicurve.CanLift27.{0} :=
  AffOrbicurve.canLift27_of_complex OrbicurveCores.U2.canLift27C

end Iut.Anabelian

namespace Iut.Tripod

open Iut.EllipticCurveData Iut.Anabelian Iut.LocalConstruct

/-- **The Corollary 3.12 variant implies the classical ABC conjecture**, over the genuine étale
and tempered fundamental groups of the model orbicurves, with [CanLift], Proposition 2.7
discharged (`Iut.Anabelian.canLift27`). -/
theorem classicalABC_of_variant_genuine'
    (h312 : ∀ (D : InitialThetaData (modelAG (genuinePi1Theory canLift27))
        (modelTG (genuinePi1Theory canLift27) (temperedTheory (genuineEtaleData canLift27))))
      (LT : LocalTheory.{0, 0} D.Kt) (TL : ThetaLocalData D LT) (QI : QPilotInputs D),
      Corollary312Variant (concreteVariantData.{0, 0} D LT TL QI)) :
    ClassicalABC :=
  classicalABC_of_variant_genuine canLift27 h312

end Iut.Tripod
