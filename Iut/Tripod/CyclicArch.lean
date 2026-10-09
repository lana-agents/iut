/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Tripod.Legendre
import Heights.TorsionArchimedean

/-!
# Torsion points of Legendre curves over `ℂ` with a bounded parameter

For `λ ∈ ℂ ∖ {0, 1}` with `|log|λ||, |log|λ − 1|| ≤ c`, the `x`-coordinates of the `N`-torsion
points of `E_λ : y² = x(x − 1)(x − λ)` satisfy `|x| ≤ C₀(c) N²`
(`Iut.CyclicArch.legendre_torsion_x_le`), from the general bound
`Heights.exists_torsion_x_bound` of `lana-agents/heights` (complex uniformization): the
discriminant `16λ²(λ − 1)²`, the `j`-invariant `256(λ² − λ + 1)³/(λ²(λ − 1)²)` and
`b₂ = −4(1 + λ)` are bounded in terms of `c`.
-/

namespace Iut.CyclicArch

open WeierstrassCurve Iut.Tripod

set_option maxHeartbeats 2000000 in
-- the real-number bookkeeping (positivity and `nlinarith` on the bounds of `λ`) is heavy
/-- **Torsion `x`-coordinates on Legendre curves over `ℂ` with a bounded parameter.** -/
theorem legendre_torsion_x_le (c : ℝ) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ (l : ℂ), |Real.log ‖l‖| ≤ c → |Real.log ‖l - 1‖| ≤ c →
      ∀ (W : WeierstrassCurve ℂ) [W.IsElliptic], W = legendre l →
      ∀ {N : ℕ}, 1 ≤ N → ∀ {x y : ℂ} (h : W.toAffine.Nonsingular x y),
        N • (Affine.Point.some x y h : W.toAffine.Point) = 0 → ‖x‖ ≤ C₀ * N ^ 2 := by
  obtain ⟨A, B, hA, hB, hbound⟩ := Heights.exists_torsion_x_bound
  set E : ℝ := Real.exp c with hE
  have hE0 : 0 < E := Real.exp_pos c
  set J : ℝ := 256 * (E ^ 2 + E + 1) ^ 3 * E ^ 4 with hJ
  set M : ℝ := A * (16 * E ^ 4) * max J 1 with hM
  set Bj : ℝ := B * (Real.log (max J (Real.exp 1)) + 1) ^ 2 with hBj
  have hBj0 : 0 ≤ Bj := by positivity
  refine ⟨max 1 M * (2 + Bj) + (1 + E) / 3, by positivity, ?_⟩
  intro l hl hl1 W _ hW N hN x y h hP
  -- the bounds on `λ`
  subst hW
  haveI : NeZero (2 : ℂ) := ⟨two_ne_zero⟩
  have hl0 : l ≠ 0 := ne_zero_of_legendre_isElliptic
  have hl10 : l - 1 ≠ 0 := sub_ne_zero.mpr ne_one_of_legendre_isElliptic
  have hlpos : 0 < ‖l‖ := norm_pos_iff.mpr hl0
  have hl1pos : 0 < ‖l - 1‖ := norm_pos_iff.mpr hl10
  have hup : ‖l‖ ≤ E := by
    rw [hE, ← Real.exp_log hlpos]; exact Real.exp_le_exp.mpr (abs_le.mp hl).2
  have hup1 : ‖l - 1‖ ≤ E := by
    rw [hE, ← Real.exp_log hl1pos]; exact Real.exp_le_exp.mpr (abs_le.mp hl1).2
  have hlow : 1 ≤ E * ‖l‖ := by
    rw [hE, ← Real.exp_log hlpos, ← Real.exp_add]
    exact Real.one_le_exp (by linarith [(abs_le.mp hl).1])
  have hlow1 : 1 ≤ E * ‖l - 1‖ := by
    rw [hE, ← Real.exp_log hl1pos, ← Real.exp_add]
    exact Real.one_le_exp (by linarith [(abs_le.mp hl1).1])
  -- the invariants of `W`
  have hj : ‖(legendre l).j‖ ≤ J := by
    rw [legendre_j, norm_div, norm_mul, norm_pow, norm_mul, norm_pow, norm_pow]
    rw [div_le_iff₀ (by positivity)]
    have hq : ‖l ^ 2 - l + 1‖ ≤ E ^ 2 + E + 1 := by
      calc ‖l ^ 2 - l + 1‖ ≤ ‖l ^ 2‖ + ‖l‖ + ‖(1 : ℂ)‖ := by
            refine (norm_add_le _ _).trans ?_
            gcongr
            exact norm_sub_le _ _
        _ ≤ E ^ 2 + E + 1 := by rw [norm_pow, norm_one]; gcongr
    have h256 : ‖(256 : ℂ)‖ = 256 := by norm_num
    rw [h256]
    calc 256 * ‖l ^ 2 - l + 1‖ ^ 3 ≤ 256 * (E ^ 2 + E + 1) ^ 3 := by gcongr
      _ = J * (1 / E ^ 4) := by rw [hJ]; field_simp
      _ ≤ J * (‖l‖ ^ 2 * ‖l - 1‖ ^ 2) := by
          gcongr
          rw [div_le_iff₀ (by positivity)]
          nlinarith [mul_self_le_mul_self zero_le_one hlow, mul_self_le_mul_self zero_le_one hlow1]
  have hΔ : ‖(legendre l).Δ‖ ≤ 16 * E ^ 4 := by
    rw [legendre_Δ, norm_mul, norm_mul, norm_pow, norm_pow]
    have : ‖(16 : ℂ)‖ = 16 := by norm_num
    rw [this]
    calc 16 * ‖l‖ ^ 2 * ‖l - 1‖ ^ 2 ≤ 16 * E ^ 2 * E ^ 2 := by gcongr
      _ = 16 * E ^ 4 := by ring
  have hb₂ : ‖(legendre l).b₂ / 12‖ ≤ (1 + E) / 3 := by
    rw [legendre_b₂, norm_div, norm_mul, norm_neg]
    have h4 : ‖(4 : ℂ)‖ = 4 := by norm_num
    have h12 : ‖(12 : ℂ)‖ = 12 := by norm_num
    rw [h4, h12]
    have : ‖1 + l‖ ≤ 1 + E := (norm_add_le _ _).trans (by rw [norm_one]; gcongr)
    rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
    nlinarith
  -- the general bound
  have hmain := hbound (legendre l) hN h hP
  set Q : ℝ := 2 * N ^ 2 + Bj with hQ
  have hQ0 : 0 ≤ Q := by positivity
  have hlogj : Real.log (max ‖(legendre l).j‖ (Real.exp 1)) ≤ Real.log (max J (Real.exp 1)) :=
    Real.log_le_log (lt_max_of_lt_right (Real.exp_pos 1)) (max_le_max hj le_rfl)
  have hlogj0 : 0 ≤ Real.log (max ‖(legendre l).j‖ (Real.exp 1)) :=
    Real.log_nonneg (le_trans (Real.one_le_exp zero_le_one) (le_max_right _ _))
  have h6 : ‖x + (legendre l).b₂ / 12‖ ^ 6 ≤ M * Q ^ 6 := by
    refine hmain.trans ?_
    rw [hM, hQ, hBj]
    gcongr
  have hmM : M ≤ max 1 M ^ 6 := le_trans (le_max_right _ _)
    (le_self_pow₀ (le_max_left _ _) (by norm_num))
  have h1 : ‖x + (legendre l).b₂ / 12‖ ≤ max 1 M * Q := by
    refine le_of_pow_le_pow_left₀ (by norm_num : (6 : ℕ) ≠ 0) (by positivity) ?_
    calc ‖x + (legendre l).b₂ / 12‖ ^ 6 ≤ M * Q ^ 6 := h6
      _ ≤ max 1 M ^ 6 * Q ^ 6 := by gcongr
      _ = (max 1 M * Q) ^ 6 := by ring
  have hN1 : (1 : ℝ) ≤ N ^ 2 := by exact_mod_cast Nat.one_le_pow _ _ hN
  calc ‖x‖ = ‖(x + (legendre l).b₂ / 12) - (legendre l).b₂ / 12‖ := by ring_nf
    _ ≤ ‖x + (legendre l).b₂ / 12‖ + ‖(legendre l).b₂ / 12‖ := norm_sub_le _ _
    _ ≤ max 1 M * Q + (1 + E) / 3 := add_le_add h1 hb₂
    _ ≤ (max 1 M * (2 + Bj) + (1 + E) / 3) * N ^ 2 := by
        rw [hQ]
        have h1M : 0 ≤ max 1 M := le_trans zero_le_one (le_max_left _ _)
        nlinarith [mul_nonneg h1M hBj0]

end Iut.CyclicArch
