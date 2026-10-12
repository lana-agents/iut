/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.EtaleTheta.Theta
import TateCurvesTheta.Kummer.ThetaGerm

/-!
# The étale theta class on points and germs ([EtTh], Prop. 1.3–1.5)

[EtTh], Prop. 1.3 constructs the étale theta class `η^Θ ∈ H¹(Π^tp_Ÿ, Δ_Θ)`, well defined up
to `O_K^×`-multiples, and Prop. 1.4(iii) identifies it with the Kummer class of `Θ̈`; its
restrictions to (decomposition groups of) points are the Kummer classes of the values of `Θ̈`.
Prop. 1.5(iii) computes the action of `a ∈ ℤ = Π^tp_X/Π^tp_Y`:
```
η^Θ ↦ η^Θ - 2a·log(Ü) - (a²/2)·log(q) + log(O^×).
```
The tempered group `Π^tp_Ÿ` is not available here (scope decision S2 of `README.md`); we
formalize the class through its restrictions to points (Kummer classes of values, in
`H¹_cont(Gal(Ω/K), μ_n)` and `H¹_cont(G_K, Ẑ(1))`, `continuous-kummer-theory`) and to germs
(`tate-curves-theta`'s `thetaGerm`).

## Main results

* `etaleThetaUnit_zpow_sqrt_mul`, `map_etaleThetaUnit_zpow_sqrt_mul`,
  `kummer_etaleTheta_zpow_sqrt_mul`, `kummerZHat_etaleTheta_zpow_sqrt_mul`: **[EtTh],
  Prop. 1.5(iii) on points**: `κ(Θ̈(s^a Ü)) = κ(-1)^a·κ(s)^{-a²}·κ(Ü)^{-2a}·κ(Θ̈(Ü))`
  (`s^{-a²} = q^{-a²/2}`; the sign `κ(-1)^a` is the `μ_2`-part of `log(O^×)`).
* `kummer_etaleTheta_inv`, `kummer_etaleTheta_neg`: the inversion and the deck involution
  change the class by `κ(-1)`.
* `kummer_smul_etaleTheta`: the scalar multiple `c·Θ̈` has class `κ(c)·κ(Θ̈)` — the
  `O^×`-indeterminacy of Prop. 1.3.
* `thetaUnit_neg_sq`, `decomposition_kummer_etaleThetaGerm`: **[EtTh], Prop. 1.4(iii) on germs**:
  the Kummer class of the germ at `U₀ = Ü₀²` of the function `Θ̈·Ü⁻¹ = θ(-U)` on `Y` (the
  function of the proof of Prop. 1.5) restricts, on the decomposition group of a valuation
  dominating the point, to the Kummer class of `Ü₀⁻¹·Θ̈(Ü₀)`.
-/

noncomputable section

namespace Iut.EtaleTheta

open TateCurvesTheta TateCurvesTheta.TateParameter KummerTheory PowerSeries IsLocalRing

variable {K : Type*} [NormedField K] (t : TateParameter K)

/-- A theta value `Θ̈(Ü) ≠ 0` as a unit. -/
def etaleThetaUnit (U : Kˣ) (hU : etaleTheta t U ≠ 0) : Kˣ := Units.mk0 _ hU

@[simp] lemma coe_etaleThetaUnit (U : Kˣ) (hU : etaleTheta t U ≠ 0) :
    (etaleThetaUnit t U hU : K) = etaleTheta t U := rfl

lemma etaleTheta_zpow_sqrt_mul_ne_zero {s : Kˣ} (hs : s ^ 2 = t.q) (a : ℤ) {U : Kˣ}
    (hU : etaleTheta t U ≠ 0) : etaleTheta t (s ^ a * U) ≠ 0 := by
  rw [etaleTheta_zpow_sqrt_mul t hs]
  exact mul_ne_zero (thetaFactor_ne_zero s a U) hU

/-- The automorphy factor as a unit: `(-1)^a·s^{-a²}·Ü^{-2a}`. -/
lemma coe_thetaFactorUnit (s : Kˣ) (a : ℤ) (U : Kˣ) :
    (((-1) ^ a * s ^ (-a ^ 2) * U ^ (-2 * a) : Kˣ) : K) = thetaFactor s a U := by
  simp [thetaFactor, Units.val_zpow_eq_zpow_val]

/-- Unit form of the `ℤ`-action: `Θ̈(s^a Ü) = (-1)^a s^{-a²} Ü^{-2a}·Θ̈(Ü)` in `Kˣ`. -/
theorem etaleThetaUnit_zpow_sqrt_mul {s : Kˣ} (hs : s ^ 2 = t.q) (a : ℤ) (U : Kˣ)
    (hU : etaleTheta t U ≠ 0) :
    etaleThetaUnit t (s ^ a * U) (etaleTheta_zpow_sqrt_mul_ne_zero t hs a hU) =
      (-1) ^ a * s ^ (-a ^ 2) * U ^ (-2 * a) * etaleThetaUnit t U hU := by
  ext
  rw [Units.val_mul, coe_thetaFactorUnit, coe_etaleThetaUnit, coe_etaleThetaUnit,
    etaleTheta_zpow_sqrt_mul t hs]

/-- **[EtTh], Prop. 1.5(iii), transported along any homomorphism to a commutative group**:
`φ(Θ̈(s^a Ü)) = φ(-1)^a·φ(s)^{-a²}·φ(Ü)^{-2a}·φ(Θ̈(Ü))`. -/
theorem map_etaleThetaUnit_zpow_sqrt_mul {G : Type*} [CommGroup G] (φ : Kˣ →* G) {s : Kˣ}
    (hs : s ^ 2 = t.q) (a : ℤ) (U : Kˣ) (hU : etaleTheta t U ≠ 0) :
    φ (etaleThetaUnit t (s ^ a * U) (etaleTheta_zpow_sqrt_mul_ne_zero t hs a hU)) =
      φ (-1) ^ a * φ s ^ (-a ^ 2) * φ U ^ (-2 * a) * φ (etaleThetaUnit t U hU) := by
  rw [etaleThetaUnit_zpow_sqrt_mul t hs, map_mul, map_mul, map_mul, map_zpow, map_zpow,
    map_zpow]

lemma etaleTheta_inv_ne_zero {U : Kˣ} (hU : etaleTheta t U ≠ 0) : etaleTheta t U⁻¹ ≠ 0 := by
  rw [etaleTheta_inv]; exact neg_ne_zero.2 hU

lemma etaleTheta_neg_ne_zero {U : Kˣ} (hU : etaleTheta t U ≠ 0) : etaleTheta t (-U) ≠ 0 := by
  rw [etaleTheta_neg]; exact neg_ne_zero.2 hU

/-- Inversion in `Kˣ`: `Θ̈(Ü⁻¹) = -1·Θ̈(Ü)`. -/
theorem etaleThetaUnit_inv (U : Kˣ) (hU : etaleTheta t U ≠ 0) :
    etaleThetaUnit t U⁻¹ (etaleTheta_inv_ne_zero t hU) = -1 * etaleThetaUnit t U hU := by
  ext; simp

/-- Oddness in `Kˣ`: `Θ̈(-Ü) = -1·Θ̈(Ü)`. -/
theorem etaleThetaUnit_neg (U : Kˣ) (hU : etaleTheta t U ≠ 0) :
    etaleThetaUnit t (-U) (etaleTheta_neg_ne_zero t hU) = -1 * etaleThetaUnit t U hU := by
  ext; simp only [coe_etaleThetaUnit, etaleTheta_neg, Units.val_neg, neg_mul, one_mul]

section Kummer

variable (n : ℕ) (Ω : Type*) [Field Ω] [Algebra K Ω] [Algebra.IsIntegral K Ω]
  [HasKummerRoots n K Ω]

/-- **[EtTh], Prop. 1.5(iii) on points**: in `H¹_cont(Gal(Ω/K), μ_n)`,
`κ(Θ̈(s^a Ü)) = κ(-1)^a·κ(s)^{-a²}·κ(Ü)^{-2a}·κ(Θ̈(Ü))`, i.e. (additively)
`η ↦ η - 2a·log(Ü) - (a²/2)·log(q) + a·log(-1)`. -/
theorem kummer_etaleTheta_zpow_sqrt_mul {s : Kˣ} (hs : s ^ 2 = t.q) (a : ℤ) (U : Kˣ)
    (hU : etaleTheta t U ≠ 0) :
    kummer n K Ω (etaleThetaUnit t (s ^ a * U) (etaleTheta_zpow_sqrt_mul_ne_zero t hs a hU)) =
      kummer n K Ω (-1) ^ a * kummer n K Ω s ^ (-a ^ 2) * kummer n K Ω U ^ (-2 * a) *
        kummer n K Ω (etaleThetaUnit t U hU) :=
  map_etaleThetaUnit_zpow_sqrt_mul t _ hs a U hU

/-- The inversion automorphism on Kummer classes: `κ(Θ̈(Ü⁻¹)) = κ(-1)·κ(Θ̈(Ü))`. -/
theorem kummer_etaleTheta_inv (U : Kˣ) (hU : etaleTheta t U ≠ 0) :
    kummer n K Ω (etaleThetaUnit t U⁻¹ (etaleTheta_inv_ne_zero t hU)) =
      kummer n K Ω (-1) * kummer n K Ω (etaleThetaUnit t U hU) := by
  rw [etaleThetaUnit_inv, map_mul]

/-- The deck involution of `Ÿ/Y` on Kummer classes: `κ(Θ̈(-Ü)) = κ(-1)·κ(Θ̈(Ü))`. -/
theorem kummer_etaleTheta_neg (U : Kˣ) (hU : etaleTheta t U ≠ 0) :
    kummer n K Ω (etaleThetaUnit t (-U) (etaleTheta_neg_ne_zero t hU)) =
      kummer n K Ω (-1) * kummer n K Ω (etaleThetaUnit t U hU) := by
  rw [etaleThetaUnit_neg, map_mul]

/-- **Scalar multiples** ([EtTh], Prop. 1.3): the class of `c·Θ̈(Ü)` is `κ(c)·κ(Θ̈(Ü))`; the
classes of the `O^×`-multiples of `Θ̈` form the coset `κ(O^×)·κ(Θ̈)`. -/
theorem kummer_smul_etaleTheta (c : Kˣ) (U : Kˣ) (hU : etaleTheta t U ≠ 0) :
    kummer n K Ω (c * etaleThetaUnit t U hU) =
      kummer n K Ω c * kummer n K Ω (etaleThetaUnit t U hU) :=
  map_mul _ _ _

end Kummer

/-- `Ẑ(1)`-form of `kummer_etaleTheta_zpow_sqrt_mul`, in `H¹_cont(G_K, Ẑ(1))`. -/
theorem kummerZHat_etaleTheta_zpow_sqrt_mul (Ω : Type*) [Field Ω] [Algebra K Ω] [IsGalois K Ω]
    [IsSepClosed Ω] {s : Kˣ} (hs : s ^ 2 = t.q) (a : ℤ) (U : Kˣ) (hU : etaleTheta t U ≠ 0) :
    kummerZHat K Ω (etaleThetaUnit t (s ^ a * U) (etaleTheta_zpow_sqrt_mul_ne_zero t hs a hU)) =
      kummerZHat K Ω (-1) ^ a * kummerZHat K Ω s ^ (-a ^ 2) * kummerZHat K Ω U ^ (-2 * a) *
        kummerZHat K Ω (etaleThetaUnit t U hU) :=
  map_etaleThetaUnit_zpow_sqrt_mul t _ hs a U hU

/-! ### Germs: [EtTh], Prop. 1.4(iii) -/

lemma theta_neg_sq_ne_zero {U : Kˣ} (hU : etaleTheta t U ≠ 0) : t.theta (-(U ^ 2)) ≠ 0 := by
  intro h
  exact hU (by rw [etaleTheta_def, h, mul_zero])

/-- The value at `U₀ = Ü₀²` of the function `Θ̈·Ü⁻¹ = θ(-U)` on `Y`: `θ(-Ü₀²) = Ü₀⁻¹·Θ̈(Ü₀)`. -/
theorem thetaUnit_neg_sq (U : Kˣ) (hU : etaleTheta t U ≠ 0) :
    t.thetaUnit (-(U ^ 2)) (theta_neg_sq_ne_zero t hU) = U⁻¹ * etaleThetaUnit t U hU := by
  ext
  simp only [coe_thetaUnit, Units.val_mul, coe_etaleThetaUnit, etaleTheta_def]
  rw [← mul_assoc, Units.val_inv_eq_inv_val, inv_mul_cancel₀ U.ne_zero, one_mul]

section Decomposition

variable (F : Type*) {Ω : Type*} [Field F] [Field Ω] [Algebra K F] [Algebra F Ω] [Algebra K Ω]
  [IsScalarTower K F Ω] [Algebra K⟦X⟧ F]
variable (hCF : ∀ c : K, algebraMap K⟦X⟧ F (C c) = algebraMap K F c)
variable (A : ValuationSubring Ω) (hk : ∀ c : K, algebraMap K Ω c ∈ A)
  [Algebra K (ResidueField A)]
  (hkres : ∀ c : K, residue A ⟨algebraMap K Ω c, hk c⟩ = algebraMap K (ResidueField A) c)
  (hA : ∀ r : K⟦X⟧, algebraMap F Ω (algebraMap K⟦X⟧ F r) ∈ A) (hX : residue A ⟨_, hA X⟩ = 0)
variable (n : ℕ) (hn : n ≠ 0) [Algebra.IsIntegral F Ω] [Algebra.IsIntegral K (ResidueField A)]
  [HasKummerRoots n F Ω] [HasKummerRoots n K (ResidueField A)]

include hCF hX in
/-- **[EtTh], Prop. 1.4(iii) on germs.** Let `A ⊆ Ω` be a valuation subring dominating the
completed local ring `K⟦X⟧` of `Y` at the non-cuspidal point `U₀ = Ü₀²` (coordinate
`U = U₀(1 + X)`), with decomposition group `D_A`. The restriction to `D_A` of the Kummer class of
the germ of `Θ̈·Ü⁻¹ = θ(-U)` (`thetaGerm (-U₀)`) is the inflation of the Kummer class of the value
`Ü₀⁻¹·Θ̈(Ü₀)`. -/
theorem decomposition_kummer_etaleThetaGerm (U : Kˣ) (hU : etaleTheta t U ≠ 0) :
    letI := Decomposition.muAction F A hk hkres n
    ContH1.map (A.decompositionSubgroup F).subtype continuous_subtype_val
        (Decomposition.reduceMu A n hn) continuous_of_discreteTopology
        (Decomposition.reduceMu_smul F A hk hkres n hn)
        (kummer n F Ω (Units.map (algebraMap K⟦X⟧ F : K⟦X⟧ →* F)
          (t.thetaGermUnit (-(U ^ 2)) (theta_neg_sq_ne_zero t hU)))) =
      ContH1.map (Decomposition.decompositionMap F A hk hkres)
        (Decomposition.continuous_decompositionMap F A hk hkres) (MonoidHom.id _) continuous_id
        (fun _ _ => rfl) (kummer n K (ResidueField A) (U⁻¹ * etaleThetaUnit t U hU)) := by
  rw [← thetaUnit_neg_sq]
  exact t.decomposition_kummer_thetaGerm F hCF A hk hkres hA hX n hn _ _

end Decomposition

end Iut.EtaleTheta
