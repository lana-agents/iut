/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Tripod.Providers
import Iut.Tripod.TwoTorsion
import Iut.Concrete.ThetaLocalConstruct.Data
import Iut.Implication.ChebyshevExplicit
import Iut.Concrete.Main
import Iut.Concrete.LocalConstruct.Theory
import Iut.Anabelian.Existence
import Iut.Tripod.Northcott
import Iut.Tripod.TorsionDegree
import Iut.Tripod.LogCond

/-!
# The ABC implication for the tripod, with propositional inputs

`Iut.Tripod.abc_of_variant`: the Corollary 3.12 variant implies ABC on the tripod
(`tripodTheory.StatementII`: for points of bounded degree in a compactly bounded subset of
`ℙ¹ ∖ {0,1,∞}`), where every object is constructed in this repository and every
hypothesis is a proposition about the constructed objects:

* `CurveProps`: the ℓ-torsion of the Legendre curves is a rank-two `ℤ/ℓ`-module, and
  `E_λ/F_λ` has stable reduction and the Galois-degree property;
* `CurveFactsProp`: the height comparison of Corollary 2.2(i), the cyclic-subgroup bound
  and the `SL₂`-image lemma ([GenEll] §3); the `2`-adic bound and the conductor comparisons
  are theorems (`Iut/Tripod/TwoAdic.lean`, `LogCond.lean`);
* `LocalTheoryFacts`: the three remaining facts of the local theory (the inclusion of the
  maximal order in the log-shell, least hull regions, IUT IV Prop. 1.4(iii)) and the tower
  arithmetic `TowerArithmetic` (IUT IV, §1), all about the constructed packets;
* the prime-counting bound (Prop. 1.6);
* `h312`, the variant itself.

The Chebyshev bounds, Northcott's theorem, the Tate parameters, the mod-`ℓ` representations,
the theta local data, and the anabelian existence are theorems or constructions.
-/

namespace Iut.Tripod

open Iut Iut.EllipticCurveData Iut.Anabelian NumberField Iut.LocalConstruct
open scoped Classical


variable (hp : CurveProps)

/-- **Existence of suitable initial Θ-data for the Legendre curves**, with the constructed
theta local data. -/
theorem concreteThetaDataExistence' {K : CompactlyBounded} {d : ℕ} {TK : ℝ}
    (CF : CurveFactsProp (providersOfProps hp) K d TK) (hN : NorthcottHyp)
    (hlocal : ∀ (K : Type) [Field K] [NumberField K], LocalTheoryFacts K)
    (TAp : ∀ (D : InitialThetaData modelAG modelTG) (htwo : TwoTorsionRational D)
      (QI : QPilotInputs D),
      TowerArithmetic D (concreteLocalTheory D.Kt (hlocal D.Kt))
        (thetaLocalData D (concreteLocalTheory D.Kt (hlocal D.Kt)) htwo QI)) :
    ConcreteThetaDataExistence.{0, 0} (AG := modelAG) (TG := modelTG)
      (curveInputs (providersOfProps hp) K d CF hN
        (fun l => torsionDegreeBound_three l (hp.torsion_basis l 3 (by norm_num)))
        (fun l => torsionDegreeBound_five l (hp.torsion_basis l 5 (by norm_num)))
        (twoAdicBound _ K) (logCondGe _) (logCondLe _)).toCorollary22Inputs := by
  set CI := curveInputs (providersOfProps hp) K d CF hN
    (fun l => torsionDegreeBound_three l (hp.torsion_basis l 3 (by norm_num)))
    (fun l => torsionDegreeBound_five l (hp.torsion_basis l 5 (by norm_num)))
    (twoAdicBound _ K) (logCondGe _) (logCondLe _) with hCI
  intro x hx ℓ hℓ h7 hP2 hP3 hP5 hsl
  have hP2' : ∀ w (hw : w ∈ (CI.curve x hx).badAll), ¬ ℓ ∣ (CI.tate x hx).qOrder w hw := by
    intro w hw
    have := hP2 w ((CI.arith x hx).badAll_finite.mem_toFinset.mpr hw)
    change ¬ ℓ ∣ (if h : w ∈ (CI.curve x hx).badAll then (CI.tate x hx).qOrder w h else 0)
      at this
    rwa [dif_pos hw] at this
  have hP5' : ∃ w ∈ (CI.curve x hx).badAll, residueChar w ≠ 2 ∧ residueChar w ≠ ℓ := by
    obtain ⟨w, hw, h⟩ := hP5
    exact ⟨w, (CI.arith x hx).badAll_finite.mem_toFinset.mp hw, h⟩
  let D := (CI.curve x hx).thetaData (CI.arith x hx) (CI.tate x hx) hℓ h7 (CI.modRep x hx ℓ hℓ)
    (hsl hx hℓ) hP2' hP5' anabelianExistence
  have htwo : TwoTorsionRational D :=
    two_torsion_curveOf x ((providersOfProps hp).torsionFinite3 x.1)
      ((providersOfProps hp).torsionFinite5 x.1)
  let QI : QPilotInputs D := (CI.curve x hx).qPilotInputs (CI.arith x hx) (CI.tate x hx) hℓ h7
    (CI.modRep x hx ℓ hℓ) (hsl hx hℓ) hP2' hP5' anabelianExistence
  refine ⟨D, concreteLocalTheory D.Kt (hlocal D.Kt),
    thetaLocalData D (concreteLocalTheory D.Kt (hlocal D.Kt)) htwo QI, QI, TAp D htwo QI, rfl,
    CI.dmod_le x hx, ?_, CI.logDiff_eq x hx, CI.logCond_ge x hx ℓ hℓ h7,
    CI.logCond_le x hx ℓ hℓ h7⟩
  exact (CI.curve x hx).logQ_eq (CI.arith x hx) (CI.tate x hx) hℓ h7 (CI.modRep x hx ℓ hℓ)
    (hsl hx hℓ) hP2' hP5' anabelianExistence _ _

/-- **The Corollary 3.12 variant implies ABC on the tripod**, with propositional inputs. -/
theorem abc_of_variant
    (hfacts : ∀ (K : CompactlyBounded) (d : ℕ),
      ∃ TK : ℝ, CurveFactsProp (providersOfProps hp) K d TK)
    (hlocal : ∀ (K : Type) [Field K] [NumberField K], LocalTheoryFacts K)
    (TAp : ∀ (D : InitialThetaData modelAG modelTG) (htwo : TwoTorsionRational D)
      (QI : QPilotInputs D),
      TowerArithmetic D (concreteLocalTheory D.Kt (hlocal D.Kt))
        (thetaLocalData D (concreteLocalTheory D.Kt (hlocal D.Kt)) htwo QI))
    (hprime : PrimeCountingHyp)
    (h312 : ∀ (D : InitialThetaData modelAG modelTG) (LT : LocalTheory.{0, 0} D.Kt)
      (TL : ThetaLocalData D LT) (QI : QPilotInputs D),
      Corollary312Variant (concreteVariantData.{0, 0} D LT TL QI)) :
    tripodTheory.StatementII := by
  choose TK CF using hfacts
  obtain ⟨pnt⟩ := primeCountingBound_of_exists hprime
  exact statementII_of_cor312
    (fun K d => (curveInputs (providersOfProps hp) K d (CF K d) northcottHyp
      (fun l => torsionDegreeBound_three l (hp.torsion_basis l 3 (by norm_num)))
      (fun l => torsionDegreeBound_five l (hp.torsion_basis l 5 (by norm_num)))
      (twoAdicBound _ K) (logCondGe _) (logCondLe _)).toCorollary22Inputs)
    (fun K d => (concreteThetaDataExistence' hp (CF K d) northcottHyp hlocal TAp).toThetaDataExistence)
    chebyshevBoundExplicit pnt (fun _ ⟨D, LT, TL, QI, hX⟩ => hX ▸ h312 D LT TL QI)

end Iut.Tripod
