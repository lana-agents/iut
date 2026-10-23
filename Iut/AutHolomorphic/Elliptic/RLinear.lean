/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Real-linear self-maps of `ℂ`: holomorphic, antiholomorphic, squares

Linear algebra behind [AbsTopIII] Corollary 2.7 (d), (e) (and Proposition 2.6 (a)) in the form
used by `Iut/AutHolomorphic/Elliptic/LinearHol.lean`:

* `eq_mul_of_differentiableAt`: an `ℝ`-linear map `ℂ → ℂ` that is complex differentiable at one
  point is multiplication by a fixed complex number;
* `eq_mul_or_eq_mul_conj`: an `ℝ`-linear automorphism `M` of `ℂ` such that `M ∘ (i ·) ∘ M⁻¹` is
  multiplication by a fixed complex number is `z ↦ a z` or `z ↦ a z̄` ("preserves orthogonal
  frames");
* `IsRC a ε`: the maps `z ↦ a z` (`ε = false`) and `z ↦ a z̄` (`ε = true`), `a ≠ 0`, i.e. the
  group `ℂ^× ⋊ Gal(ℂ/ℝ)`; `rc_sq`: the squares in this group are exactly the maps `z ↦ b z`,
  `b ≠ 0` (squares = orientation preserving).
-/

namespace Iut

namespace AutHol

namespace Ell

open Complex ComplexConjugate

/-- **An `ℝ`-linear map that is complex differentiable at a point is `ℂ`-linear.** -/
theorem eq_mul_of_differentiableAt (M : ℂ →ₗ[ℝ] ℂ) {z : ℂ} (h : DifferentiableAt ℂ M z) (w : ℂ) :
    M w = M 1 * w := by
  let Mc : ℂ →L[ℝ] ℂ := LinearMap.toContinuousLinearMap M
  have h1 : HasFDerivAt (M : ℂ → ℂ) Mc z := Mc.hasFDerivAt
  have h2 : HasFDerivAt (M : ℂ → ℂ) ((fderiv ℂ M z).restrictScalars ℝ) z :=
    h.hasFDerivAt.restrictScalars ℝ
  have h3 := h1.unique h2
  have hw : Mc w = (fderiv ℂ M z) w := by rw [h3]; rfl
  have h1' : Mc 1 = (fderiv ℂ M z) 1 := by rw [h3]; rfl
  change Mc w = Mc 1 * w
  rw [hw, h1', mul_comm]
  conv_lhs => rw [← mul_one w]
  rw [← smul_eq_mul, map_smul, smul_eq_mul]

/-- `M (x + i y) = x M 1 + y M i`. -/
theorem realLinear_apply (M : ℂ →ₗ[ℝ] ℂ) (w : ℂ) : M w = w.re * M 1 + w.im * M I := by
  have hw : w = (w.re : ℝ) • (1 : ℂ) + (w.im : ℝ) • I := by
    apply Complex.ext <;> simp
  conv_lhs => rw [hw]
  rw [map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]

/-- **An `ℝ`-linear automorphism `M` of `ℂ` with `M ∘ (i ·) ∘ M⁻¹` complex linear is `z ↦ a z` or
`z ↦ a z̄`.** -/
theorem eq_mul_or_eq_mul_conj (M : ℂ ≃ₗ[ℝ] ℂ) {c : ℂ} (hc : ∀ w, M (I * M.symm w) = c * w) :
    (∀ w, M w = M 1 * w) ∨ (∀ w, M w = M 1 * conj w) := by
  have hc' : ∀ u, M (I * u) = c * M u := fun u => by
    simpa using hc (M u)
  have hsq : c * c = -1 := by
    have h1 := hc' (I * M.symm 1)
    rw [hc' (M.symm 1), ← mul_assoc, I_mul_I, neg_one_mul, map_neg, M.apply_symm_apply] at h1
    -- h1 : -1 = c * (c * 1)
    linear_combination -h1
  have hc2 : c = I ∨ c = -I := by
    have : (c - I) * (c + I) = 0 := by linear_combination hsq - I_mul_I
    rcases mul_eq_zero.1 this with h | h
    · left; linear_combination h
    · right; linear_combination h
  have hMI : M I = c * M 1 := by simpa using hc' 1
  rcases hc2 with rfl | rfl
  · left
    intro w
    have hr := realLinear_apply M.toLinearMap w
    simp only [LinearEquiv.coe_coe] at hr
    rw [hr, hMI]
    conv_rhs => rw [← Complex.re_add_im w]
    ring
  · right
    intro w
    have hr := realLinear_apply M.toLinearMap w
    simp only [LinearEquiv.coe_coe] at hr
    rw [hr, hMI]
    conv_rhs => rw [← Complex.re_add_im w]
    simp only [map_add, conj_ofReal, map_mul, conj_I]
    ring

/-- The maps `z ↦ a z` (`ε = false`) and `z ↦ a z̄` (`ε = true`). -/
def rc (a : ℂ) (ε : Bool) (z : ℂ) : ℂ := if ε then a * conj z else a * z

theorem rc_false (a z : ℂ) : rc a false z = a * z := rfl

theorem rc_true (a z : ℂ) : rc a true z = a * conj z := rfl

theorem rc_comp (a b : ℂ) (ε δ : Bool) (z : ℂ) :
    rc a ε (rc b δ z) = rc (if ε then a * conj b else a * b) (xor ε δ) z := by
  cases ε <;> cases δ <;> simp [rc, mul_assoc]

/-- **Squares in `ℂ^× ⋊ Gal(ℂ/ℝ)` are the complex-linear maps.** A composite `g ∘ g` of a map of
the form `z ↦ a z` or `z ↦ a z̄` is `z ↦ b z`; conversely every `z ↦ b z`, `b ≠ 0`, is such a
square. -/
theorem rc_sq (a : ℂ) (ε : Bool) : ∃ b, (b ≠ 0 ∨ a = 0) ∧ ∀ z, rc a ε (rc a ε z) = b * z := by
  cases ε
  · refine ⟨a * a, ?_, fun z => by simp [rc, mul_assoc]⟩
    by_cases ha : a = 0
    · exact Or.inr ha
    · exact Or.inl (mul_ne_zero ha ha)
  · refine ⟨a * conj a, ?_, fun z => by simp [rc, mul_assoc]⟩
    by_cases ha : a = 0
    · exact Or.inr ha
    · exact Or.inl (mul_ne_zero ha ((map_ne_zero _).2 ha))

theorem exists_sq_eq (b : ℂ) : ∃ a, ∀ z, rc a false (rc a false z) = b * z := by
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq b two_pos
  exact ⟨a, fun z => by rw [rc_false, rc_false, ← mul_assoc, ← pow_two, ha]⟩

end Ell

end AutHol

end Iut
