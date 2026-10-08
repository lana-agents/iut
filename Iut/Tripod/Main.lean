/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Tripod.Providers
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
import Iut.Tripod.CyclicIsogeny
import Iut.Tripod.Tower
import Iut.Tripod.TowerFacts
import Iut.Tripod.TameTwo

/-!
# The ABC implication for the tripod, with propositional inputs

`Iut.Tripod.abc_of_variant`: the Corollary 3.12 variant implies ABC on the tripod
(`tripodTheory.StatementII`: for points of bounded degree in a compactly bounded subset of
`ℙ¹ ∖ {0,1,∞}`), where every object is constructed in this repository and every
hypothesis is a proposition about the constructed objects:

* the Θ-data `D : InitialThetaData` of IUT I, Definition 3.1, stated about the model
  orbicurves with their genuine étale fundamental groups (`Orbicurve.genuinePi1`, open
  immersions `genuinePi1Cover` for covers), their genuine `k`-cores (`genuineHasCore`) and
  their tempered fundamental groups (`Orbicurve.temperedPi1`, with the comparison
  `Orbicurve.tempToEtale`); the variant `h312 : Cor312VariantHolds` is assumed for the concrete
  variant data `concreteVariantData D` of every such `D`;
* the curve-level data of the Legendre curves (`Iut.Tripod.tripodProviders`, a closed
  term: the torsion bases `E_λ[ℓ] ≅ (ℤ/ℓ)²` from the division polynomials, `Iut/Torsion/`,
  the stable reduction of `E_λ/F_λ` at every finite place, `Iut.Tripod.stable_reduction`,
  and the Galois-degree property of `F_λ/ℚ(j)`, `Iut/Tripod/Galois.lean`, are theorems);
* `CurveFactsProp`: the cyclic-subgroup bound ([GenEll] Lemma 3.5) away from `2`
  (`CyclicBoundOddHyp`: the bound for `log q_∀ − log q₂`, which is what Corollary 2.2 uses) is
  a theorem (`Iut.Tripod.cyclicBoundOdd`, `Iut/Tripod/CyclicIsogeny.lean`: Lemma 3.2(i) at the
  odd multiplicative places and the product formula for the Vélu ratios of the points of
  order `2` and `4`, with the complex uniformization of `lana-agents/heights` at the
  archimedean places); the height comparison of Corollary 2.2(i), the `2`-adic bound,
  the conductor comparisons, the `SL₂`-image lemma ([GenEll] Lemma 3.1(iii)) and the
  finiteness of the points whose once-punctured curve has no core ([CanLift],
  Proposition 2.7, `Iut.Anabelian.canLift27`, `Iut.Anabelian.hasCore_oncePunctured`) are theorems
  (`Iut/Tripod/Height.lean`, `TwoAdic.lean`, `LogCond.lean`, `CurveFacts.lean` with
  `Iut/Concrete/SL2Image.lean`, `Core.lean`);
* the local facts of the tower `ℚ(j) ⊆ ℚ(λ) ⊆ F_λ ⊆ F_λ(E_λ[ℓ])`, `TowerLocalHyp`, are a
  theorem (`Iut.Tripod.towerLocalHyp`, `Iut/Tripod/TameTwo.lean`, `TowerFacts.lean`): the
  tameness away from `2·ℓ`, Néron–Ogg–Shafarevich (`Iut.Tripod.relRamIdx_eq_one_of_not_bad`)
  and the ramification bound `e(v/u) ≤ 30ℓ` away from `2·3·5·ℓ`
  (`Iut.Tripod.relRamIdx_le_thirty_mul`) are proved from the reduction theory of the
  Legendre model at the places of odd residue characteristic (`Iut/Tower/ReductionKernel.lean`,
  `MultiplicativeKernel.lean`, the inertia-group criterion `Iut/Tower/Inertia.lean`), the
  tameness of `F_λ(E_λ[ℓ])/F_λ` at the places over `2` (`2 ∤ e(v/w)`,
  `Iut.Tripod.tameTwoHyp`, IUT IV, Proposition 1.8) from the stable reduction of `E_λ` there
  and the involution argument of `Iut/Tower/InertiaInvolution.lean` (an element of order `2`
  of the inertia group would fix the `ℓ`-torsion of a stable model); the wild ramification
  bound `v_p(e(v/u)) ≤ c_p` follows (`Iut.Tripod.padicValNat_relRamIdx_le_of_tame`),
  the different bound of Proposition 1.3 is the theorem `Iut.TowerLocalFacts.ordAt_different_le`
  (Serre's bound) and the ramification bound `e(u/u₀) ≤ 2` of `ℚ(λ)/ℚ(j)` at the bad places is
  the theorem `Iut.Tripod.relRamIdx_tpd_le_two`; from the local facts the tower arithmetic
  `TowerArithmetic` (IUT IV, §1) of the Θ-data of the points is a theorem
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


/-- **Existence of suitable initial Θ-data for the Legendre curves**, with the constructed
theta local data. -/
theorem concreteThetaDataExistence' {K : CompactlyBounded} {d : ℕ} {TK : ℝ}
    (CF : CurveFactsProp (tripodProviders) K d TK) (hN : NorthcottHyp) :
    ConcreteThetaDataExistence.{0}
      (curveInputs tripodProviders K d CF (coreFiniteness _ K d) hN
        torsionDegreeBound_three' torsionDegreeBound_five'
        (legendreHeight _ K) (twoAdicBound _ K) (logCondGe _)
        (logCondLe _)).toCorollary22Inputs := by
  set CI := curveInputs tripodProviders K d CF (coreFiniteness _ K d) hN
    torsionDegreeBound_three' torsionDegreeBound_five'
    (legendreHeight _ K) (twoAdicBound _ K) (logCondGe _) (logCondLe _) with hCI
  intro x hx hxe ℓ hℓ h7 hP2 hP3 hP5 hsl
  have hcore : OrbicurveDataSection.HasCoreUniversally (CI.curve x hx).F (CI.curve x hx).E := by
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
    (hsl hx hℓ) hP2' hP5' hcore
  refine ⟨D,
    towerArithmetic_of_towerLocalHyp (tripodProviders) x hℓ h7 (hsl hx hℓ) hP2' hP5'
      hcore (towerLocalHyp _)
      torsionDegreeBound_three' torsionDegreeBound_five', rfl,
    CI.dmod_le x hx, ?_, CI.logDiff_eq x hx, CI.logCond_ge x hx ℓ hℓ h7,
    CI.logCond_le x hx ℓ hℓ h7⟩
  exact (CI.curve x hx).logQ_eq (CI.arith x hx) (CI.tate x hx) hℓ h7 (CI.modRep x hx ℓ hℓ)
    (hsl hx hℓ) hP2' hP5' hcore

/-- **The Corollary 3.12 variant implies ABC on the tripod**, with propositional inputs. -/
theorem abc_of_variant (h312 : Cor312VariantHolds) :
    tripodTheory.StatementII := by
  let CF : ∀ K d, CurveFactsProp (tripodProviders) K d (cyclicConst K) :=
    fun K d => ⟨cyclicBoundOdd _ K d⟩
  exact statementII_of_cor312
    (fun K d => (curveInputs tripodProviders K d (CF K d) (coreFiniteness _ K d)
      northcottHyp torsionDegreeBound_three' torsionDegreeBound_five'
      (legendreHeight _ K) (twoAdicBound _ K) (logCondGe _)
      (logCondLe _)).toCorollary22Inputs)
    (fun K d =>
      (concreteThetaDataExistence' (CF K d) northcottHyp).toThetaDataExistence)
    chebyshevBoundExplicit primeCountingBoundExplicit
    (fun _ ⟨D, hX⟩ => hX ▸ h312 D)

end Iut.Tripod
