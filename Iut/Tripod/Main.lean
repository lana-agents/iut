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
import Iut.Tripod.CyclicBound
import Iut.Tripod.Tower
import Iut.Tripod.TowerFacts

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
* the curve-level data of the Legendre curves (`Iut.Tripod.tripodProviders`, a closed
  term: the torsion bases `E_λ[ℓ] ≅ (ℤ/ℓ)²` from the division polynomials, `Iut/Torsion/`,
  the stable reduction of `E_λ/F_λ` at every finite place, `Iut.Tripod.stable_reduction`,
  and the Galois-degree property of `F_λ/ℚ(j)`, `Iut/Tripod/Galois.lean`, are theorems);
* `CurveFactsProp`: the cyclic-subgroup bound ([GenEll] Lemma 3.5), assumed in its residual
  form `CyclicGraphBoundHyp`; the height comparison of Corollary 2.2(i), the `2`-adic bound,
  the conductor comparisons, the `SL₂`-image lemma ([GenEll] Lemma 3.1(iii)) and the
  finiteness of the points whose once-punctured curve has no core ([CanLift],
  Proposition 2.7, from the fields `excJ`, `hasCore_oncePunctured` of `Pi1`) are theorems
  (`Iut/Tripod/Height.lean`, `TwoAdic.lean`, `LogCond.lean`, `CurveFacts.lean` with
  `Iut/Concrete/SL2Image.lean`, `Core.lean`);
* `TameTwoHyp`: **the residual tameness of `F_λ(E_λ[ℓ])/F_λ` at the places over `2`**
  (`2 ∤ e(v/w)` for the places `v` of residue characteristic `2`, IUT IV, Proposition 1.8).
  From it the local facts of the tower `ℚ(j) ⊆ ℚ(λ) ⊆ F_λ ⊆ F_λ(E_λ[ℓ])`, `TowerLocalHyp`,
  are a theorem (`Iut.Tripod.towerLocalHyp_of_tameTwo`, `Iut/Tripod/TowerFacts.lean`): the
  tameness away from `2·ℓ`, Néron–Ogg–Shafarevich (`Iut.Tripod.relRamIdx_eq_one_of_not_bad`)
  and the ramification bound `e(v/u) ≤ 30ℓ` away from `2·3·5·ℓ`
  (`Iut.Tripod.relRamIdx_le_thirty_mul`) are proved from the reduction theory of the
  Legendre model at the places of odd residue characteristic (`Iut/Tower/ReductionKernel.lean`,
  `MultiplicativeKernel.lean`, the inertia-group criterion `Iut/Tower/Inertia.lean`); the
  wild ramification bound `v_p(e(v/u)) ≤ c_p` follows
  (`Iut.Tripod.padicValNat_relRamIdx_le_of_tame`),
  the different bound of Proposition 1.3 is the theorem `Iut.TowerLocalFacts.ordAt_different_le`
  (Serre's bound) and the ramification bound `e(u/u₀) ≤ 2` of `ℚ(λ)/ℚ(j)` at the bad places is
  the theorem `Iut.Tripod.relRamIdx_tpd_le_two`; from the local facts the tower arithmetic
  `TowerArithmetic` (IUT IV, §1) for the constructed local theory (`concreteLocalTheory`,
  every field of which is proved) and theta local data is a theorem
  (`Iut.Tripod.towerArithmetic_of_towerLocalHyp`);
* `h312`, the variant itself.

The Chebyshev bounds, the prime-counting bound of IUT IV, Prop. 1.6 (with the factor `3/2`,
`primeCountingBoundExplicit`), Northcott's theorem, the Tate parameters, the mod-`ℓ`
representations, the theta local data, and the anabelian existence are theorems or
constructions.
-/

namespace Iut.Tripod

open Iut Iut.EllipticCurveData Iut.Anabelian NumberField Iut.LocalConstruct
open scoped Classical


variable (Pi1 : EtalePi1Theory.{0}) (Tp : TemperedPi1Theory Pi1)

/-- **Existence of suitable initial Θ-data for the Legendre curves**, with the constructed
theta local data. -/
theorem concreteThetaDataExistence' {K : CompactlyBounded} {d : ℕ} {TK : ℝ}
    (CF : CurveFactsProp (tripodProviders) K d TK) (hN : NorthcottHyp)
    (htame : TameTwoHyp tripodProviders) :
    ConcreteThetaDataExistence.{0, 0} (AG := modelAG Pi1) (TG := modelTG Pi1 Tp)
      (curveInputs tripodProviders K d CF (coreFiniteness Pi1 _ K d) hN
        torsionDegreeBound_three' torsionDegreeBound_five'
        (legendreHeight _ K) (twoAdicBound _ K) (logCondGe _)
        (logCondLe _)).toCorollary22Inputs := by
  set CI := curveInputs tripodProviders K d CF (coreFiniteness Pi1 _ K d) hN
    torsionDegreeBound_three' torsionDegreeBound_five'
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
    two_torsion_curveOf x ((tripodProviders).torsionFinite3 x.1)
      ((tripodProviders).torsionFinite5 x.1)
  let QI : QPilotInputs D := (CI.curve x hx).qPilotInputs (CI.arith x hx) (CI.tate x hx) hℓ h7
    (CI.modRep x hx ℓ hℓ) (hsl hx hℓ) hP2' hP5' (anabelianExistence Pi1 Tp) hcore
  refine ⟨D, concreteLocalTheory D.Kt,
    thetaLocalData D (concreteLocalTheory D.Kt) htwo QI, QI,
    towerArithmetic_of_towerLocalHyp (tripodProviders) x hℓ h7 (hsl hx hℓ) hP2' hP5'
      (anabelianExistence Pi1 Tp) hcore (towerLocalHyp_of_tameTwo _ htame)
      torsionDegreeBound_three' torsionDegreeBound_five'
      (concreteLocalTheory D.Kt) htwo, rfl,
    CI.dmod_le x hx, ?_, CI.logDiff_eq x hx, CI.logCond_ge x hx ℓ hℓ h7,
    CI.logCond_le x hx ℓ hℓ h7⟩
  exact (CI.curve x hx).logQ_eq (CI.arith x hx) (CI.tate x hx) hℓ h7 (CI.modRep x hx ℓ hℓ)
    (hsl hx hℓ) hP2' hP5' (anabelianExistence Pi1 Tp) hcore _ _

/-- **The Corollary 3.12 variant implies ABC on the tripod**, with propositional inputs. -/
theorem abc_of_variant
    (hcyc : ∀ (K : CompactlyBounded) (d : ℕ),
      ∃ TK : ℝ, CyclicGraphBoundHyp (tripodProviders) K d TK)
    (htame : TameTwoHyp tripodProviders)
    (h312 : ∀ (D : InitialThetaData (modelAG Pi1) (modelTG Pi1 Tp)) (LT : LocalTheory.{0, 0} D.Kt)
      (TL : ThetaLocalData D LT) (QI : QPilotInputs D),
      Corollary312Variant (concreteVariantData.{0, 0} D LT TL QI)) :
    tripodTheory.StatementII := by
  choose TK hc using hcyc
  let CF : ∀ K d, CurveFactsProp (tripodProviders) K d (TK K d) :=
    fun K d => ⟨cyclicBound_of _ K d (hc K d)⟩
  exact statementII_of_cor312
    (fun K d => (curveInputs tripodProviders K d (CF K d) (coreFiniteness Pi1 _ K d)
      northcottHyp torsionDegreeBound_three' torsionDegreeBound_five'
      (legendreHeight _ K) (twoAdicBound _ K) (logCondGe _)
      (logCondLe _)).toCorollary22Inputs)
    (fun K d =>
      (concreteThetaDataExistence' Pi1 Tp (CF K d) northcottHyp htame).toThetaDataExistence)
    chebyshevBoundExplicit primeCountingBoundExplicit
    (fun _ ⟨D, LT, TL, QI, hX⟩ => hX ▸ h312 D LT TL QI)

end Iut.Tripod
