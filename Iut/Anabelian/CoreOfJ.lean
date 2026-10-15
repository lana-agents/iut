/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Anabelian.CanLift
import Iut.Cor312.ThetaData.Orbicurve

/-!
# The core condition of initial Θ-data from [CanLift], Proposition 2.7 (MR1)

IUT I, Definition 3.1(d) requires that `C_K = X_K/{±1}` is the `K`-core of `X_K`. The existence
of Θ-data (`Iut.AdmissiblePrimeData.orbicurveData`) takes this in the form
`OrbicurveDataSection.HasCoreUniversally F E` (the core condition after every extension of the
base field of characteristic `0`). Here it is **derived** from [CanLift], Proposition 2.7
(`Iut.Anabelian.canLift27`, a theorem): it holds as soon as `j(E)` is not one of the four
exceptional values `AffOrbicurve.excJ` (`Iut.Anabelian.hasCoreUniversally_of_j`). So the only
input left is an elementary condition on the `j`-invariant.
-/

namespace Iut.Anabelian

open OrbicurveDataSection

/-- **The core condition of IUT I, Definition 3.1(d), from [CanLift], Proposition 2.7**: if `j(E)`
is not exceptional, then `C_K = X_K/{±1}` is the core of `X_K` over every field `K ⊇ F` of
characteristic `0`. -/
theorem hasCoreUniversally_of_j {F : Type} [Field F] [NumberField F] (E : WeierstrassCurve F)
    [E.IsElliptic] (hj : ∀ c ∈ AffOrbicurve.excJ, E.j ≠ (c : F)) :
    HasCoreUniversally F E := by
  intro K _ _ f
  have hjK : ∀ c ∈ AffOrbicurve.excJ, (E.map f).j ≠ (c : K) := by
    intro c hc h
    rw [WeierstrassCurve.map_j, ← map_ratCast f] at h
    exact hj c hc (f.injective h)
  have := hasCore_oncePunctured (E.map f) hjK
  change genuineHasCore ((Orbicurve.oncePunctured E).baseChange f)
    ((Orbicurve.pmQuotient (Orbicurve.oncePunctured E)).baseChange f)
  rw [Orbicurve.baseChange_pmQuotient, Orbicurve.baseChange_oncePunctured]
  exact this

/-- Contrapositive form: a curve without the universal core has an exceptional `j`-invariant. -/
theorem exists_excJ_of_not_hasCoreUniversally {F : Type} [Field F] [NumberField F]
    (E : WeierstrassCurve F) [E.IsElliptic] (h : ¬ HasCoreUniversally F E) :
    ∃ c ∈ AffOrbicurve.excJ, E.j = (c : F) := by
  by_contra hc
  push Not at hc
  exact h (hasCoreUniversally_of_j E hc)

end Iut.Anabelian
