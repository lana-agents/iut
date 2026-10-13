/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.LogLink.Arch
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Archimedean unit-inducedness (IUT III, Proposition 1.2(vii); [AbsTopIII], Proposition 5.8(v))

`Iut/LogLink/Galois.lean` shows that at `v ∈ V^non` the identifications of the log-shells
produced by the anabelian reconstruction are **unit-induced**: induced, through the `p`-adic
logarithm, by an automorphism of the units. This file treats `v ∈ V^arc`, where the local
field is `ℂ` (`Iut/LogLink/Arch.lean`).

## The archimedean situation

At `v ∈ V^arc` the multiplicative group splits as `ℂˣ = S¹ × ℝ_{>0}` (angular and radial
parts). The logarithm sends the **units** `S¹` (the elements of absolute value `1`) to the
imaginary axis `iℝ`, only modulo the deck group `2πiℤ` (`Arch.lean`, `log_mul_sub_mem`), and
the radial part `ℝ_{>0}` to the real axis. Since `log(S¹)` spans only the line `iℝ`, an
identification of `log(ℂˣ) = ℂ` induced by automorphisms of the multiplicative structure is
determined by two pieces of data, one for each direct factor:

* **angular**: an automorphism `α` of the abstract group `S¹` (`Circle`) with
  `ψ(log u) ≡ log(α u) mod 2πiℤ` for all `u ∈ S¹`;
* **radial**: a map `ρ : ℝ_{>0} → ℝ_{>0}` with `ψ(log r) = log(ρ r)`.

This is `ArchUnitInduced ψ`, for `ψ` an `ℝ`-linear automorphism of `ℂ` (the mono-analytic
structure: `log(D^⊢_v)` is a topological `ℝ`-module, IUT III, Proposition 1.2(vii)). This is
the construction of [AbsTopIII], Proposition 5.8(v): `k^∼(G)` is built from the universal
covering of the angular units and from the radial part.

## Results

* **`archUnitInduced_iff`**: `ψ` is unit-induced iff `ψ(1) ∈ ℝ` and `ψ(i) = ±i`. The angular
  datum forces `ψ(i) = ±i` without any continuity hypothesis on `α`: `α` is then
  `u ↦ u^n` with `n = ψ(i)/i ∈ ℤ` (`coe_apply_eq_zpow`), and injectivity forces `n = ±1`.
* **Unit-inducedness does not imply log-shell compatibility at `V^arc`** (contrast
  `image_logShell_of_unitInduced` at `V^non`): the radial datum allows `z ↦ λ·Re z + i·Im z`
  for every real `λ ≠ 0` (`radialScale`, `archUnitInduced_radialScale`), which preserves the
  log-shell (the closed disc of radius `π`) iff `|λ| = 1` (`radialScale_image_closedBall`).
* **Precise characterization** (`archPolyIso_iff_logShell`, `archPolyIso_iff_isometry`): a
  unit-induced `ψ` preserves the log-shell iff it is an isometry iff it belongs to the
  **poly-isomorphism of Proposition 1.2(vii)** (`ArchPolyIso`: the orbit of the identity
  under the independent actions of `{±1}` on the two direct factors `ℝ`, `iℝ`, i.e.
  `z ↦ ε₁·Re z + ε₂·i·Im z`). This matches IUT III, Remark 1.2.1(ii): a metric on `ℂ` is
  determined by its restriction to `S¹`, and it fixes the radial normalization.
* **Galois**: `archPolyIso_iff_sign_algEquiv`: the poly-isomorphism consists of the maps
  `ε·τ` with `ε = ±1` and `τ ∈ Gal(ℂ/ℝ) = {id, conj}` (the continuous ring automorphisms of
  `ℂ`, `archPolyIso_of_ringEquiv`); the inversion of the units induces `z ↦ −z`
  (`archUnitInduced_neg`), the conjugation of the units induces `z ↦ z̄`.
* Compatibility with the archimedean log-links: the poly-isomorphism carries the values of every
  archimedean log-link on the units into the log-shell (`ArchPolyIso.toFun_mem_closedBall`).
-/

namespace Iut

namespace LogLink

open Complex Metric
open scoped ComplexConjugate

noncomputable section

/-! ### Logarithms of units -/

/-- `log u = i·arg u` on the units. -/
theorem log_circle (u : Circle) : Complex.log u = (arg u : ℂ) * I := by
  rw [Complex.log, Circle.norm_coe, Real.log_one, ofReal_zero, zero_add]

theorem log_circleExp {t : ℝ} (h₁ : -Real.pi < t) (h₂ : t ≤ Real.pi) :
    Complex.log (Circle.exp t) = t * I := by
  rw [Circle.coe_exp, Complex.log_exp] <;> simpa

/-- An `ℝ`-linear map of `ℂ` is determined by `ψ 1` and `ψ i`. -/
theorem linear_apply (ψ : ℂ ≃ₗ[ℝ] ℂ) (z : ℂ) : ψ z = z.re * ψ 1 + z.im * ψ I := by
  have hz : z = z.re • (1 : ℂ) + z.im • I := by
    apply Complex.ext <;> simp
  conv_lhs => rw [hz]
  rw [map_add, map_smul, map_smul, real_smul, real_smul]

/-! ### Archimedean unit-inducedness -/

/-- **An identification of `log(ℂˣ) = ℂ` induced by the units** (archimedean analogue of
`LogLink.UnitInduced`): induced through the logarithm by an automorphism `α` of the angular
units `S¹` (modulo the deck group `2πiℤ` of the universal covering) and by a map `ρ` of the
radial part `ℝ_{>0}`. -/
def ArchUnitInduced (ψ : ℂ ≃ₗ[ℝ] ℂ) : Prop :=
  (∃ α : Circle ≃* Circle, ∀ u : Circle,
    ∃ n : ℤ, ψ (Complex.log u) = Complex.log (α u) + n * (2 * Real.pi * I)) ∧
  ∃ ρ : ℝ → ℝ, ∀ r : ℝ, 0 < r → 0 < ρ r ∧ ψ (Real.log r) = Real.log (ρ r)

/-- The angular datum: `α u = exp(ψ(log u))`. -/
theorem coe_apply_eq_exp {ψ : ℂ ≃ₗ[ℝ] ℂ} {α : Circle ≃* Circle}
    (hα : ∀ u : Circle, ∃ n : ℤ, ψ (Complex.log u) = Complex.log (α u) + n * (2 * Real.pi * I))
    (u : Circle) : ((α u : Circle) : ℂ) = Complex.exp (ψ (Complex.log u)) := by
  obtain ⟨n, hn⟩ := hα u
  rw [hn, Complex.exp_add, Complex.exp_log (Circle.coe_ne_zero _),
    Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- The angular datum forces `Re ψ(i) = 0`. -/
theorem re_apply_I_eq_zero {ψ : ℂ ≃ₗ[ℝ] ℂ} {α : Circle ≃* Circle}
    (hα : ∀ u : Circle, ∃ n : ℤ, ψ (Complex.log u) = Complex.log (α u) + n * (2 * Real.pi * I)) :
    (ψ I).re = 0 := by
  have h := coe_apply_eq_exp hα (Circle.exp 1)
  rw [log_circleExp (by linarith [Real.pi_pos]) (by linarith [Real.pi_gt_three])] at h
  have h1 := congrArg (‖·‖) h
  simp only [Circle.norm_coe, ofReal_one, one_mul, Complex.norm_exp] at h1
  have := Real.exp_eq_one_iff _ |>.1 h1.symm
  exact this

/-- The angular datum forces `ψ(i) = n·i` with `n ∈ ℤ`. -/
theorem exists_int_apply_I {ψ : ℂ ≃ₗ[ℝ] ℂ} {α : Circle ≃* Circle}
    (hα : ∀ u : Circle, ∃ n : ℤ, ψ (Complex.log u) = Complex.log (α u) + n * (2 * Real.pi * I)) :
    ∃ n : ℤ, ψ I = n * I := by
  have hre := re_apply_I_eq_zero hα
  have hI : ψ I = ((ψ I).im : ℂ) * I := by
    apply Complex.ext <;> simp [hre]
  have h := coe_apply_eq_exp hα (Circle.exp Real.pi)
  rw [log_circleExp (by linarith [Real.pi_pos]) le_rfl] at h
  have h2 : (Circle.exp Real.pi) ^ 2 = 1 := by
    rw [← Circle.exp_natCast_mul]
    push_cast
    exact Circle.exp_two_pi
  have h3 : ((α (Circle.exp Real.pi) : Circle) : ℂ) ^ 2 = 1 := by
    rw [← Circle.coe_pow, ← map_pow, h2, map_one, Circle.coe_one]
  rw [h, ← Complex.exp_nat_mul] at h3
  obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.1 h3
  refine ⟨m, ?_⟩
  rw [hI]
  congr 1
  have hψ : ψ ((Real.pi : ℂ) * I) = (Real.pi : ℂ) * ψ I := by
    rw [← real_smul, map_smul, real_smul]
  rw [hψ, hI] at hm
  have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  have : ((2 : ℕ) : ℂ) * ((Real.pi : ℂ) * (((ψ I).im : ℂ) * I)) =
      ((ψ I).im : ℂ) * (2 * Real.pi * I) := by push_cast; ring
  rw [this] at hm
  exact mul_right_cancel₀ (by simp [Real.pi_ne_zero]) hm

/-- **The angular automorphism is a power map**: `α u = u^n` with `ψ(i) = n·i`. -/
theorem coe_apply_eq_zpow {ψ : ℂ ≃ₗ[ℝ] ℂ} {α : Circle ≃* Circle}
    (hα : ∀ u : Circle, ∃ n : ℤ, ψ (Complex.log u) = Complex.log (α u) + n * (2 * Real.pi * I))
    {n : ℤ} (hn : ψ I = n * I) (u : Circle) : ((α u : Circle) : ℂ) = (u : ℂ) ^ n := by
  rw [coe_apply_eq_exp hα, log_circle, ← real_smul, map_smul, hn, real_smul,
    show ((arg u : ℝ) : ℂ) * ((n : ℂ) * I) = n * ((arg u : ℂ) * I) by ring,
    Complex.exp_int_mul]
  congr 1
  have := Complex.norm_mul_exp_arg_mul_I (u : ℂ)
  rwa [Circle.norm_coe, ofReal_one, one_mul] at this

/-- **The angular datum forces `ψ(i) = ±i`**: `u ↦ u^n` is injective on `S¹` only for
`n = ±1`. -/
theorem apply_I_eq_or {ψ : ℂ ≃ₗ[ℝ] ℂ} {α : Circle ≃* Circle}
    (hα : ∀ u : Circle, ∃ n : ℤ, ψ (Complex.log u) = Complex.log (α u) + n * (2 * Real.pi * I)) :
    ψ I = I ∨ ψ I = -I := by
  obtain ⟨n, hn⟩ := exists_int_apply_I hα
  have hpow := coe_apply_eq_zpow hα hn
  by_cases h0 : n = 0
  · subst h0
    exfalso
    have h1 : α (Circle.exp Real.pi) = α 1 := by
      apply Circle.ext
      rw [hpow, map_one, Circle.coe_one, zpow_zero]
    exact Circle.exp_pi_ne_one (α.injective h1)
  · have hζ : α (Circle.exp (2 * Real.pi / n)) = α 1 := by
      apply Circle.ext
      rw [hpow, map_one, Circle.coe_one, Circle.coe_exp, ← Complex.exp_int_mul]
      have : (n : ℂ) * (((2 * Real.pi / n : ℝ) : ℂ) * I) = 1 * (2 * Real.pi * I) := by
        have hn' : (n : ℂ) ≠ 0 := Int.cast_ne_zero.2 h0
        push_cast
        field_simp
      rw [this]
      exact_mod_cast Complex.exp_int_mul_two_pi_mul_I 1
    have h1 := congrArg (fun u : Circle => (u : ℂ)) (α.injective hζ)
    simp only [Circle.coe_exp, Circle.coe_one] at h1
    obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.1 h1
    have hk' : (1 : ℂ) = k * n := by
      have hn' : (n : ℂ) ≠ 0 := Int.cast_ne_zero.2 h0
      have h2 : ((2 * Real.pi / n : ℝ) : ℂ) * I * n = (k : ℂ) * (2 * Real.pi * I) * n := by
        rw [hk]
      push_cast at h2
      field_simp at h2
      rw [h2]
      ring
    have hk'' : k * n = 1 := by exact_mod_cast hk'.symm
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' hk'' with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · left
      rw [hn]
      simp
    · right
      rw [hn]
      simp

/-- **Characterization of archimedean unit-inducedness**: `ψ(1)` is real and `ψ(i) = ±i`. -/
theorem archUnitInduced_iff (ψ : ℂ ≃ₗ[ℝ] ℂ) :
    ArchUnitInduced ψ ↔ (ψ 1).im = 0 ∧ (ψ I = I ∨ ψ I = -I) := by
  constructor
  · rintro ⟨⟨α, hα⟩, ⟨ρ, hρ⟩⟩
    refine ⟨?_, apply_I_eq_or hα⟩
    obtain ⟨hpos, h⟩ := hρ (Real.exp 1) (Real.exp_pos 1)
    rw [Real.log_exp, ofReal_one] at h
    rw [h, ofReal_im]
  · rintro ⟨h1, hI⟩
    refine ⟨?_, ⟨fun r => r ^ (ψ 1).re, fun r hr => ⟨Real.rpow_pos_of_pos hr _, ?_⟩⟩⟩
    · rcases hI with hI | hI
      · refine ⟨MulEquiv.refl _, fun u => ⟨0, ?_⟩⟩
        rw [log_circle, ← real_smul, map_smul, hI, real_smul]
        simp [log_circle]
      · refine ⟨MulEquiv.inv _, fun u => ?_⟩
        have he : Complex.exp (ψ (Complex.log u)) =
            Complex.exp (Complex.log ((MulEquiv.inv Circle u : Circle) : ℂ)) := by
          rw [Complex.exp_log (Circle.coe_ne_zero _), log_circle, ← real_smul, map_smul, hI,
            smul_neg, Complex.exp_neg, real_smul]
          have := Complex.norm_mul_exp_arg_mul_I (u : ℂ)
          rw [Circle.norm_coe, ofReal_one, one_mul] at this
          rw [this]
          rfl
        exact Complex.exp_eq_exp_iff_exists_int.1 he
    · set l := (ψ 1).re with hl
      have h1' : ψ 1 = (l : ℂ) := by
        apply Complex.ext <;> simp [h1, hl]
      rw [Real.log_rpow hr]
      calc ψ (Real.log r) = ψ ((Real.log r) • (1 : ℂ)) := by rw [real_smul, mul_one]
        _ = Real.log r * ψ 1 := by rw [map_smul, real_smul]
        _ = _ := by rw [h1']; push_cast; ring

/-- **The inversion of the units induces `z ↦ −z`.** -/
theorem archUnitInduced_neg : ArchUnitInduced (LinearEquiv.neg ℝ) :=
  (archUnitInduced_iff _).2 ⟨by simp, Or.inr (by simp)⟩

/-- **The conjugation of the units induces `z ↦ z̄`.** -/
theorem archUnitInduced_conj : ArchUnitInduced conjAe.toLinearEquiv :=
  (archUnitInduced_iff _).2 ⟨by simp, Or.inr (by simp)⟩

theorem archUnitInduced_refl : ArchUnitInduced (LinearEquiv.refl ℝ ℂ) :=
  (archUnitInduced_iff _).2 ⟨by simp, Or.inl rfl⟩

/-! ### The radial scalings: unit-induced, but not log-shell compatible -/

/-- **The radial scaling** `z ↦ λ·Re z + i·Im z` (`λ ≠ 0`). -/
def radialScale {l : ℝ} (hl : l ≠ 0) : ℂ ≃ₗ[ℝ] ℂ where
  toFun z := ⟨l * z.re, z.im⟩
  invFun z := ⟨z.re / l, z.im⟩
  map_add' x y := by apply Complex.ext <;> simp [mul_add]
  map_smul' r x := by apply Complex.ext <;> simp; ring
  left_inv z := by apply Complex.ext <;> simp [hl]
  right_inv z := by apply Complex.ext <;> simp; field_simp

theorem radialScale_apply {l : ℝ} (hl : l ≠ 0) (z : ℂ) :
    radialScale hl z = ⟨l * z.re, z.im⟩ := rfl

/-- **Every radial scaling is unit-induced** (by the identity of `S¹` and `r ↦ r^λ`). -/
theorem archUnitInduced_radialScale {l : ℝ} (hl : l ≠ 0) : ArchUnitInduced (radialScale hl) :=
  (archUnitInduced_iff _).2 ⟨rfl, Or.inl (by apply Complex.ext <;> simp [radialScale_apply])⟩

/-- An `ℝ`-linear isometry of `ℂ` preserves the closed discs around `0`. -/
theorem image_closedBall_of_norm (ψ : ℂ ≃ₗ[ℝ] ℂ) (h : ∀ z, ‖ψ z‖ = ‖z‖) (r : ℝ) :
    ψ '' closedBall (0 : ℂ) r = closedBall 0 r := by
  ext y
  simp only [Set.mem_image, mem_closedBall, dist_zero_right]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rwa [h]
  · intro hy
    exact ⟨ψ.symm y, by rwa [← h, ψ.apply_symm_apply], ψ.apply_symm_apply y⟩

/-- If `Re ψ(z) = λ·Re z` and `ψ` preserves the log-shell, then `|λ| = 1`. -/
theorem abs_eq_one_of_image_closedBall (ψ : ℂ ≃ₗ[ℝ] ℂ) {l : ℝ}
    (hre : ∀ z, (ψ z).re = l * z.re)
    (h : ψ '' closedBall (0 : ℂ) Real.pi = closedBall 0 Real.pi) : |l| = 1 := by
  have hpi := Real.pi_pos
  have hmem : (Real.pi : ℂ) ∈ closedBall (0 : ℂ) Real.pi := by
    simp [abs_of_pos hpi]
  have h1 : ψ (Real.pi : ℂ) ∈ closedBall (0 : ℂ) Real.pi := by
    rw [← h]
    exact ⟨_, hmem, rfl⟩
  have h1' : |l| * Real.pi ≤ Real.pi := by
    rw [mem_closedBall, dist_zero_right] at h1
    have := (Complex.abs_re_le_norm _).trans h1
    rwa [hre, ofReal_re, abs_mul, abs_of_pos hpi] at this
  rw [← h] at hmem
  obtain ⟨z, hz, hz'⟩ := hmem
  have hre' : l * z.re = Real.pi := by
    rw [← hre, hz', ofReal_re]
  have hzre : |z.re| ≤ Real.pi := by
    rw [mem_closedBall, dist_zero_right] at hz
    exact (Complex.abs_re_le_norm z).trans hz
  have h2 : Real.pi ≤ |l| * Real.pi := by
    calc Real.pi = |l * z.re| := by rw [hre', abs_of_pos hpi]
      _ = |l| * |z.re| := abs_mul _ _
      _ ≤ |l| * Real.pi := mul_le_mul_of_nonneg_left hzre (abs_nonneg _)
  have h3 : |l| ≤ 1 := le_of_mul_le_mul_right (by linarith) hpi
  have h4 : 1 ≤ |l| := le_of_mul_le_mul_right (by linarith) hpi
  linarith

/-- **A radial scaling preserves the log-shell iff `|λ| = 1`.** -/
theorem radialScale_image_closedBall {l : ℝ} (hl : l ≠ 0) :
    radialScale hl '' closedBall (0 : ℂ) Real.pi = closedBall 0 Real.pi ↔ |l| = 1 := by
  refine ⟨abs_eq_one_of_image_closedBall _ fun z => rfl, fun h => ?_⟩
  refine image_closedBall_of_norm _ (fun z => ?_) _
  have hsq : l * l = 1 := by
    have := sq_abs l
    rw [h] at this
    nlinarith
  rw [radialScale_apply, Complex.norm_def, Complex.norm_def, Complex.normSq_mk,
    Complex.normSq_apply]
  congr 1
  calc l * z.re * (l * z.re) + z.im * z.im = (l * l) * (z.re * z.re) + z.im * z.im := by ring
    _ = _ := by rw [hsq, one_mul]

/-! ### The poly-isomorphism of Proposition 1.2(vii) -/

/-- **The archimedean Kummer poly-isomorphism** (IUT III, Proposition 1.2(vii)): the orbit of
the identity under the independent actions of `{±1}` on the direct factors `ℝ` and `iℝ`:
`z ↦ ε₁·Re z + ε₂·i·Im z`. -/
def ArchPolyIso (ψ : ℂ ≃ₗ[ℝ] ℂ) : Prop :=
  ∃ ε₁ ε₂ : ℤˣ, ∀ z : ℂ, ψ z = ((ε₁ : ℤ) : ℂ) * z.re + ((ε₂ : ℤ) : ℂ) * z.im * I

theorem norm_sign_mul_add (ε₁ ε₂ : ℤˣ) (z : ℂ) :
    ‖((ε₁ : ℤ) : ℂ) * z.re + ((ε₂ : ℤ) : ℂ) * z.im * I‖ = ‖z‖ := by
  rw [Complex.norm_def, Complex.norm_def]
  congr 1
  rcases Int.units_eq_one_or ε₁ with rfl | rfl <;> rcases Int.units_eq_one_or ε₂ with rfl | rfl <;>
    simp [Complex.normSq_apply]

theorem ArchPolyIso.norm_apply {ψ : ℂ ≃ₗ[ℝ] ℂ} (h : ArchPolyIso ψ) (z : ℂ) : ‖ψ z‖ = ‖z‖ := by
  obtain ⟨ε₁, ε₂, h⟩ := h
  rw [h, norm_sign_mul_add]

theorem ArchPolyIso.archUnitInduced {ψ : ℂ ≃ₗ[ℝ] ℂ} (h : ArchPolyIso ψ) : ArchUnitInduced ψ := by
  obtain ⟨ε₁, ε₂, h⟩ := h
  refine (archUnitInduced_iff ψ).2 ⟨?_, ?_⟩
  · rw [h]
    simp
  · rw [h]
    rcases Int.units_eq_one_or ε₂ with rfl | rfl
    · left
      simp
    · right
      simp

/-- **The poly-isomorphism preserves the log-shell.** -/
theorem ArchPolyIso.image_closedBall {ψ : ℂ ≃ₗ[ℝ] ℂ} (h : ArchPolyIso ψ) (r : ℝ) :
    ψ '' closedBall (0 : ℂ) r = closedBall 0 r :=
  image_closedBall_of_norm ψ h.norm_apply r

/-- A unit-induced `ψ` is `z ↦ λ·Re z ± i·Im z` with `λ = Re ψ(1)`. -/
theorem re_apply_of_archUnitInduced {ψ : ℂ ≃ₗ[ℝ] ℂ} (h : ArchUnitInduced ψ) (z : ℂ) :
    (ψ z).re = (ψ 1).re * z.re := by
  obtain ⟨-, hI⟩ := (archUnitInduced_iff ψ).1 h
  rw [linear_apply ψ z]
  rcases hI with hI | hI <;> simp [hI, mul_comm]

theorem archPolyIso_of_abs {ψ : ℂ ≃ₗ[ℝ] ℂ} (h : ArchUnitInduced ψ) (habs : |(ψ 1).re| = 1) :
    ArchPolyIso ψ := by
  obtain ⟨h1, hI⟩ := (archUnitInduced_iff ψ).1 h
  have hψ1 : ψ 1 = ((ψ 1).re : ℂ) := by
    apply Complex.ext <;> simp [h1]
  obtain ⟨ε₁, hε₁⟩ : ∃ ε₁ : ℤˣ, (ψ 1).re = ((ε₁ : ℤ) : ℝ) := by
    rcases abs_eq (zero_le_one' ℝ) |>.1 habs with h' | h'
    · exact ⟨1, by simp [h']⟩
    · exact ⟨-1, by simp [h']⟩
  obtain ⟨ε₂, hε₂⟩ : ∃ ε₂ : ℤˣ, ψ I = ((ε₂ : ℤ) : ℂ) * I := by
    rcases hI with h' | h'
    · exact ⟨1, by simp [h']⟩
    · exact ⟨-1, by simp [h']⟩
  refine ⟨ε₁, ε₂, fun z => ?_⟩
  rw [linear_apply ψ z, hψ1, hε₁, hε₂]
  push_cast
  ring

/-- **Precise characterization, log-shell form**: a unit-induced identification preserves the
archimedean log-shell iff it belongs to the poly-isomorphism of Proposition 1.2(vii). -/
theorem archPolyIso_iff_logShell (ψ : ℂ ≃ₗ[ℝ] ℂ) :
    ArchPolyIso ψ ↔
      ArchUnitInduced ψ ∧ ψ '' closedBall (0 : ℂ) Real.pi = closedBall 0 Real.pi :=
  ⟨fun h => ⟨h.archUnitInduced, h.image_closedBall _⟩, fun ⟨hu, hb⟩ =>
    archPolyIso_of_abs hu (abs_eq_one_of_image_closedBall ψ (re_apply_of_archUnitInduced hu) hb)⟩

/-- **Precise characterization, metric form** (IUT III, Remark 1.2.1(ii)): a unit-induced
identification is an isometry iff it belongs to the poly-isomorphism. -/
theorem archPolyIso_iff_isometry (ψ : ℂ ≃ₗ[ℝ] ℂ) :
    ArchPolyIso ψ ↔ ArchUnitInduced ψ ∧ ∀ z, ‖ψ z‖ = ‖z‖ :=
  ⟨fun h => ⟨h.archUnitInduced, h.norm_apply⟩, fun ⟨hu, hn⟩ =>
    (archPolyIso_iff_logShell ψ).2 ⟨hu, image_closedBall_of_norm ψ hn _⟩⟩

/-- **The poly-isomorphism is `{±1} × Gal(ℂ/ℝ)`**: `ψ = ε·τ` with `ε = ±1` and `τ` the
identity or the complex conjugation. -/
theorem archPolyIso_iff_sign_algEquiv (ψ : ℂ ≃ₗ[ℝ] ℂ) :
    ArchPolyIso ψ ↔ ∃ ε : ℤˣ, ∃ τ : ℂ ≃ₐ[ℝ] ℂ, ∀ z, ψ z = ((ε : ℤ) : ℂ) * τ z := by
  constructor
  · rintro ⟨ε₁, ε₂, h⟩
    rcases Int.units_eq_one_or ε₁ with rfl | rfl <;> rcases Int.units_eq_one_or ε₂ with rfl | rfl
    · refine ⟨1, AlgEquiv.refl, fun z => ?_⟩
      rw [h]
      conv_rhs => rw [← Complex.re_add_im z]
      simp
    · refine ⟨1, conjAe, fun z => ?_⟩
      rw [h]
      apply Complex.ext <;> simp
    · refine ⟨-1, conjAe, fun z => ?_⟩
      rw [h]
      apply Complex.ext <;> simp
    · refine ⟨-1, AlgEquiv.refl, fun z => ?_⟩
      rw [h]
      apply Complex.ext <;> simp
  · rintro ⟨ε, τ, h⟩
    rcases Complex.real_algHom_eq_id_or_conj τ.toAlgHom with hτ | hτ
    · refine ⟨ε, ε, fun z => ?_⟩
      have : τ z = z := by simpa using AlgHom.congr_fun hτ z
      rw [h, this]
      conv_lhs => rw [← Complex.re_add_im z]
      ring
    · refine ⟨ε, -ε, fun z => ?_⟩
      have : τ z = conj z := by simpa using AlgHom.congr_fun hτ z
      rw [h, this]
      apply Complex.ext <;> simp

theorem intCast_units_mul_self (ε : ℤˣ) : ((ε : ℤ) : ℂ) * ((ε : ℤ) : ℂ) = 1 := by
  rcases Int.units_eq_one_or ε with rfl | rfl <;> simp

/-- **The map `z ↦ ε·τ(z)`** for `ε = ±1` and `τ ∈ Gal(ℂ/ℝ)`. -/
def signAlgEquiv (ε : ℤˣ) (τ : ℂ ≃ₐ[ℝ] ℂ) : ℂ ≃ₗ[ℝ] ℂ where
  toFun z := ((ε : ℤ) : ℂ) * τ z
  invFun z := τ.symm (((ε : ℤ) : ℂ) * z)
  map_add' x y := by rw [map_add, mul_add]
  map_smul' r x := by
    have h : τ (r : ℂ) = r := τ.commutes r
    rw [RingHom.id_apply, real_smul, real_smul, map_mul, h]
    ring
  left_inv z := by
    simp only
    rw [← mul_assoc, intCast_units_mul_self, one_mul, AlgEquiv.symm_apply_apply]
  right_inv z := by
    simp only
    rw [AlgEquiv.apply_symm_apply, ← mul_assoc, intCast_units_mul_self, one_mul]

theorem signAlgEquiv_apply (ε : ℤˣ) (τ : ℂ ≃ₐ[ℝ] ℂ) (z : ℂ) :
    signAlgEquiv ε τ z = ((ε : ℤ) : ℂ) * τ z := rfl

theorem archPolyIso_signAlgEquiv (ε : ℤˣ) (τ : ℂ ≃ₐ[ℝ] ℂ) : ArchPolyIso (signAlgEquiv ε τ) :=
  (archPolyIso_iff_sign_algEquiv _).2 ⟨ε, τ, fun _ => rfl⟩

/-- **Galois-induced identifications**: every continuous ring automorphism of `ℂ` (the
identity or the complex conjugation) belongs to the poly-isomorphism. -/
theorem archPolyIso_of_ringEquiv (τ : ℂ ≃+* ℂ) (hτ : Continuous τ) :
    ∃ ψ : ℂ ≃ₗ[ℝ] ℂ, (∀ z, ψ z = τ z) ∧ ArchPolyIso ψ := by
  rcases Complex.ringHom_eq_id_or_conj_of_continuous (f := τ.toRingHom) hτ with e | e
  · refine ⟨LinearEquiv.refl ℝ ℂ, fun z => ?_, (archPolyIso_iff_sign_algEquiv _).2
      ⟨1, AlgEquiv.refl, fun z => by simp⟩⟩
    have := RingHom.congr_fun e z
    simpa using this.symm
  · refine ⟨conjAe.toLinearEquiv, fun z => ?_, (archPolyIso_iff_sign_algEquiv _).2
      ⟨1, conjAe, fun z => by simp⟩⟩
    have := RingHom.congr_fun e z
    simpa using this.symm

/-- The inversion of the units induces an element of the poly-isomorphism (`z ↦ −z`). -/
theorem archPolyIso_neg : ArchPolyIso (LinearEquiv.neg ℝ) :=
  (archPolyIso_iff_sign_algEquiv _).2 ⟨-1, AlgEquiv.refl, fun z => by simp⟩

/-- **Compatibility with the archimedean log-links**: the poly-isomorphism carries the values
of every archimedean log-link on the units into the log-shell. -/
theorem ArchPolyIso.toFun_mem_closedBall {ψ : ℂ ≃ₗ[ℝ] ℂ} (h : ArchPolyIso ψ)
    (L : ArchLogLink) {u : ℂ} (hu : ‖u‖ = 1) : ψ (L.toFun u) ∈ closedBall (0 : ℂ) Real.pi := by
  rw [← h.image_closedBall]
  exact ⟨_, L.toFun_mem_closedBall hu, rfl⟩

/-- **A radial scaling with `|λ| ≠ 1` is unit-induced but not in the poly-isomorphism.** -/
theorem not_archPolyIso_radialScale {l : ℝ} (hl : l ≠ 0) (h1 : |l| ≠ 1) :
    ¬ ArchPolyIso (radialScale hl) := fun h =>
  h1 ((radialScale_image_closedBall hl).1 (h.image_closedBall _))

end

end LogLink

end Iut
