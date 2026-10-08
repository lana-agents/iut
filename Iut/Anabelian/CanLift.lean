/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Anabelian.GenuineEtale
import OrbicurveCores.U2.Assembly
import Pi1.Orbicurve.LefschetzMain

/-!
# [CanLift], Proposition 2.7

`Iut.Anabelian.canLift27`: [CanLift], Proposition 2.7 (`AffOrbicurve.CanLift27`) over every
field of characteristic `0`: the statement over `ℂ` (`OrbicurveCores.U2.canLift27C`, from
`lana-agents/orbicurve-cores`) transported by the Lefschetz principle
(`AffOrbicurve.canLift27_of_complex`, from `lana-agents/pi1`). The two packages state the
complex case separately (`OrbicurveCores.CanLift27C` and `AffOrbicurve.CanLift27Complex`); the
statements agree definitionally.

`Iut.Anabelian.hasCore_oncePunctured` is the consequence for the genuine cores of the model
orbicurves: `E ∖ {0}` has the `k`-core `(E ∖ {0})/{±1}` unless `j(E) ∈ AffOrbicurve.excJ`.
-/

namespace Iut.Anabelian

/-- **[CanLift], Proposition 2.7**: for an elliptic curve `E` over a field of characteristic `0`
with non-exceptional `j`-invariant, `(E ∖ {0}) / {±1}` is the core of `E ∖ {0}`. -/
theorem canLift27 : AffOrbicurve.CanLift27.{0} :=
  AffOrbicurve.canLift27_of_complex OrbicurveCores.U2.canLift27C

/-- **[CanLift], Proposition 2.7 for the genuine cores of the model orbicurves**: the
once-punctured elliptic curve has the `k`-core `X/{±1}` unless `j(E)` is exceptional. -/
theorem hasCore_oncePunctured {k : Type} [Field k] [CharZero k] (E : WeierstrassCurve k)
    [E.IsElliptic] (hj : ∀ c ∈ AffOrbicurve.excJ, E.j ≠ (c : k)) :
    genuineHasCore (Orbicurve.oncePunctured E) (Orbicurve.pmQuotient (Orbicurve.oncePunctured E)) :=
  genuineHasCore_oncePunctured canLift27 E hj

end Iut.Anabelian
