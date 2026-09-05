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
import Iut.Tripod.Core
import Iut.Tripod.Height

/-!
# The ABC implication for the tripod, with propositional inputs

`Iut.Tripod.abc_of_variant`: the Corollary 3.12 variant implies ABC on the tripod
(`tripodTheory.StatementII`: for points of bounded degree in a compactly bounded subset of
`ℙ¹ ∖ {0,1,∞}`), where every object is constructed in this repository and every
hypothesis is a proposition about the constructed objects:

* `Pi1 : EtalePi1Theory`, `Tp : TemperedPi1Theory Pi1`: the étale and tempered fundamental
  groups of the model orbicurves with the core relation, **universally quantified** — the
  theorem holds for every such theory, in particular for the actual fundamental groups, so
  the variant `h312` is assumed on exactly the class of Θ-data of IUT I, Definition 3.1;
* `CurveProps`: the ℓ-torsion of the Legendre curves is a rank-two `ℤ/ℓ`-module, and
  `E_λ/F_λ` has stable reduction and the Galois-degree property;
* `CurveFactsProp`: the cyclic-subgroup bound and the `SL₂`-image lemma ([GenEll] §3); the
  height comparison of Corollary 2.2(i), the `2`-adic bound, the conductor comparisons and
  the finiteness of the points whose once-punctured curve has no core ([CanLift],
  Proposition 2.7, from the fields `excJ`, `hasCore_oncePunctured` of `Pi1`) are theorems
  (`Iut/Tripod/Height.lean`, `TwoAdic.lean`, `LogCond.lean`, `Core.lean`);
* the tower arithmetic `TowerArithmetic` (IUT IV, §1) for the constructed local theory
  (`concreteLocalTheory`, every field of which is now proved) and theta local data;
* `h312`, the variant itself.

The Chebyshev bounds, the prime-counting bound of IUT IV, Prop. 1.6 (with the factor `3/2`,
`primeCountingBoundExplicit`), Northcott's theorem, the Tate parameters, the mod-`ℓ`
representations, the theta local data, and the anabelian existence are theorems or
constructions.
-/

namespace Iut.Tripod

open Iut Iut.EllipticCurveData Iut.Anabelian NumberField Iut.LocalConstruct
open scoped Classical


variable (Pi1 : EtalePi1Theory.{0}) (Tp : TemperedPi1Theory Pi1) (hp : CurveProps)

/-- **Existence of suitable initial Θ-data for the Legendre curves**, with the constructed
theta local data. -/
theorem concreteThetaDataExistence' {K : CompactlyBounded} {d : ℕ} {TK : ℝ}
    (CF : CurveFactsProp (providersOfProps hp) K d TK) (hN : NorthcottHyp)
    (TAp : ∀ (D : InitialThetaData (modelAG Pi1) (modelTG Pi1 Tp)) (htwo : TwoTorsionRational D)
      (QI : QPilotInputs D),
      TowerArithmetic D (concreteLocalTheory D.Kt)
        (thetaLocalData D (concreteLocalTheory D.Kt) htwo QI)) :
    ConcreteThetaDataExistence.{0, 0} (AG := modelAG Pi1) (TG := modelTG Pi1 Tp)
      (curveInputs (providersOfProps hp) K d CF (coreFiniteness Pi1 _ K d) hN
        (fun l => torsionDegreeBound_three l (hp.torsion_basis l 3 (by norm_num)))
        (fun l => torsionDegreeBound_five l (hp.torsion_basis l 5 (by norm_num)))
        (legendreHeight _ K) (twoAdicBound _ K) (logCondGe _)
        (logCondLe _)).toCorollary22Inputs := by
  set CI := curveInputs (providersOfProps hp) K d CF (coreFiniteness Pi1 _ K d) hN
    (fun l => torsionDegreeBound_three l (hp.torsion_basis l 3 (by norm_num)))
    (fun l => torsionDegreeBound_five l (hp.torsion_basis l 5 (by norm_num)))
    (legendreHeight _ K) (twoAdicBound _ K) (logCondGe _) (logCondLe _) with hCI
  intro x hx hxe ℓ hℓ h7 hP2 hP3 hP5 hsl
  have hcore : (modelAG Pi1).HasCore ((modelAG Pi1).oncePunctured (CI.curve x hx).E)
      (OrbicurveDataSection.CF (modelAG Pi1) (CI.curve x hx).F (CI.curve x hx).E) := by
    by_contra h
    exact hxe ⟨hx, h⟩
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
    (hsl hx hℓ) hP2' hP5' (anabelianExistence Pi1 Tp) hcore
  have htwo : TwoTorsionRational D :=
    two_torsion_curveOf x ((providersOfProps hp).torsionFinite3 x.1)
      ((providersOfProps hp).torsionFinite5 x.1)
  let QI : QPilotInputs D := (CI.curve x hx).qPilotInputs (CI.arith x hx) (CI.tate x hx) hℓ h7
    (CI.modRep x hx ℓ hℓ) (hsl hx hℓ) hP2' hP5' (anabelianExistence Pi1 Tp) hcore
  refine ⟨D, concreteLocalTheory D.Kt,
    thetaLocalData D (concreteLocalTheory D.Kt) htwo QI, QI, TAp D htwo QI, rfl,
    CI.dmod_le x hx, ?_, CI.logDiff_eq x hx, CI.logCond_ge x hx ℓ hℓ h7,
    CI.logCond_le x hx ℓ hℓ h7⟩
  exact (CI.curve x hx).logQ_eq (CI.arith x hx) (CI.tate x hx) hℓ h7 (CI.modRep x hx ℓ hℓ)
    (hsl hx hℓ) hP2' hP5' (anabelianExistence Pi1 Tp) hcore _ _

/-- **The Corollary 3.12 variant implies ABC on the tripod**, with propositional inputs. -/
theorem abc_of_variant
    (hfacts : ∀ (K : CompactlyBounded) (d : ℕ),
      ∃ TK : ℝ, CurveFactsProp (providersOfProps hp) K d TK)
    (TAp : ∀ (D : InitialThetaData (modelAG Pi1) (modelTG Pi1 Tp)) (htwo : TwoTorsionRational D)
      (QI : QPilotInputs D),
      TowerArithmetic D (concreteLocalTheory D.Kt)
        (thetaLocalData D (concreteLocalTheory D.Kt) htwo QI))
    (h312 : ∀ (D : InitialThetaData (modelAG Pi1) (modelTG Pi1 Tp)) (LT : LocalTheory.{0, 0} D.Kt)
      (TL : ThetaLocalData D LT) (QI : QPilotInputs D),
      Corollary312Variant (concreteVariantData.{0, 0} D LT TL QI)) :
    tripodTheory.StatementII := by
  choose TK CF using hfacts
  exact statementII_of_cor312
    (fun K d => (curveInputs (providersOfProps hp) K d (CF K d) (coreFiniteness Pi1 _ K d)
      northcottHyp
      (fun l => torsionDegreeBound_three l (hp.torsion_basis l 3 (by norm_num)))
      (fun l => torsionDegreeBound_five l (hp.torsion_basis l 5 (by norm_num)))
      (legendreHeight _ K) (twoAdicBound _ K) (logCondGe _)
      (logCondLe _)).toCorollary22Inputs)
    (fun K d =>
      (concreteThetaDataExistence' Pi1 Tp hp (CF K d) northcottHyp TAp).toThetaDataExistence)
    chebyshevBoundExplicit primeCountingBoundExplicit
    (fun _ ⟨D, LT, TL, QI, hX⟩ => hX ▸ h312 D LT TL QI)

end Iut.Tripod
