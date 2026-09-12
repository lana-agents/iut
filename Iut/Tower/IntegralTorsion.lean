/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Tower.ReductionKernel
import Iut.Tripod.StableTwo
import Iut.Torsion.EDS
import Iut.Cor312.ThetaData.VariableChangePoint

/-!
# The kernel of reduction of an integral model has no odd prime-to-`p` torsion

For a field `K` with a valuation `v` and a Weierstrass curve `W` with `v`-integral coefficients
(arbitrary `a₁`, `a₃`; in particular at residue characteristic `2`), an affine point `P = (x, y)`
with `v(x) > 1` has `n • P ≠ 0` for every odd `n` with `v(n) = 1`
(`Iut.IntegralTorsion.nsmul_ne_zero_of_one_lt`); hence the `n`-torsion points are integral
(`Iut.IntegralTorsion.valuation_le_one_of_nsmul_eq_zero`).

The argument of `Iut/Tower/ReductionKernel.lean` (the `n`-division polynomial `Ψₙ'` is a
polynomial in `x` with integral coefficients and leading coefficient `n`) is transported from
the model `y² = x³ + …` to the general model along the change of variables
`Iut.IntegralTorsion.completeSquare W = (1, 0, −a₁/2, −a₃/2)` (`y ↦ y − (a₁x + a₃)/2`), which
does not change the `x`-coordinate nor the `b`-invariants, hence not the division polynomials
`Ψ₂², Ψ₃, Ψ₄'` and `Ψₙ'` (`Iut.IntegralTorsion.completeSquare_preΨ'`); the description
`n • P = 0 ↔ ψₙ(P) = 0` of `Iut.Torsion.smul_eq_zero_iff_eds` applies to the transformed model
(over the field `K`, where `2` is invertible, the transformed model is not integral, but the
division polynomials are those of the integral model).
-/

namespace Iut.IntegralTorsion

open WeierstrassCurve WeierstrassCurve.Affine Polynomial

variable {K : Type*} [Field K]

/-! ### Completing the square -/

section CompleteSquare

variable (W : WeierstrassCurve K)

/-- The change of variables `(u, r, s, t) = (1, 0, −a₁/2, −a₃/2)`, `y ↦ y − (a₁x + a₃)/2`,
bringing `W` to the form `y² = x³ + a₂'x² + a₄'x + a₆'`. -/
def completeSquare : VariableChange K := ⟨1, 0, -W.a₁ / 2, -W.a₃ / 2⟩

lemma completeSquare_a₁ [NeZero (2 : K)] : (completeSquare W • W).a₁ = 0 := by
  rw [variableChange_a₁]
  simp only [completeSquare, inv_one, Units.val_one, one_mul]
  field_simp
  ring

lemma completeSquare_a₃ [NeZero (2 : K)] : (completeSquare W • W).a₃ = 0 := by
  rw [variableChange_a₃]
  simp only [completeSquare, inv_one, Units.val_one, one_pow, one_mul, zero_mul, add_zero]
  field_simp
  ring

lemma completeSquare_b₂ : (completeSquare W • W).b₂ = W.b₂ := by
  rw [variableChange_b₂]
  simp [completeSquare]

lemma completeSquare_b₄ : (completeSquare W • W).b₄ = W.b₄ := by
  rw [variableChange_b₄]
  simp [completeSquare]

lemma completeSquare_b₆ : (completeSquare W • W).b₆ = W.b₆ := by
  rw [variableChange_b₆]
  simp [completeSquare]

lemma completeSquare_b₈ : (completeSquare W • W).b₈ = W.b₈ := by
  rw [variableChange_b₈]
  simp [completeSquare]

lemma completeSquare_Ψ₂Sq : (completeSquare W • W).Ψ₂Sq = W.Ψ₂Sq := by
  simp only [Ψ₂Sq, completeSquare_b₂, completeSquare_b₄, completeSquare_b₆]

lemma completeSquare_Ψ₃ : (completeSquare W • W).Ψ₃ = W.Ψ₃ := by
  simp only [Ψ₃, completeSquare_b₂, completeSquare_b₄, completeSquare_b₆, completeSquare_b₈]

lemma completeSquare_preΨ₄ : (completeSquare W • W).preΨ₄ = W.preΨ₄ := by
  simp only [preΨ₄, completeSquare_b₂, completeSquare_b₄, completeSquare_b₆, completeSquare_b₈]

/-- **The division polynomials are unchanged by completing the square.** -/
lemma completeSquare_preΨ' (n : ℕ) : (completeSquare W • W).preΨ' n = W.preΨ' n := by
  simp only [preΨ', completeSquare_Ψ₂Sq, completeSquare_Ψ₃, completeSquare_preΨ₄]

/-- The `x`-coordinate is unchanged by completing the square. -/
lemma vcX_completeSquare (x : K) : Anabelian.vcX (completeSquare W) x = x := by
  simp [Anabelian.vcX, completeSquare]

end CompleteSquare

/-! ### The kernel of reduction -/

section Kernel

variable {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ)

open scoped Classical in
/-- **The kernel of reduction has no odd prime-to-`p` torsion**: for a `v`-integral model `W`,
an affine point `P = (x, y)` with `v(x) > 1` and an odd `n` with `v(n) = 1`, `n • P ≠ 0`. -/
theorem nsmul_ne_zero_of_one_lt [NeZero (2 : K)] [inst : DecidableEq K] {W : Affine K}
    (hW : IsIntegralModel v W) {n : ℕ} (hodd : Odd n) (hn : v (n : K) = 1) {x y : K}
    (h : W.Nonsingular x y) (hx : 1 < v x) : n • Point.some x y h ≠ 0 := by
  have hi : inst = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  subst hi
  intro h0
  set C := completeSquare W with hC
  have h0' : n • Anabelian.vcEquiv C W (Point.some x y h) = 0 := by
    rw [← map_nsmul, h0, map_zero]
  rw [Anabelian.vcEquiv_apply, Anabelian.vcPoint_some,
    Iut.Torsion.smul_eq_zero_iff_eds (completeSquare_a₁ W) (completeSquare_a₃ W), Iut.Torsion.eds,
    ReductionKernel.normEDS_eq_eval_preΨ' (completeSquare_a₁ W) (completeSquare_a₃ W)
      ((Anabelian.nonsingular_vc C W x y).mp h).1,
    if_neg (Nat.not_even_iff_odd.mpr hodd), mul_one, completeSquare_preΨ', vcX_completeSquare]
    at h0'
  have hn0 : (n : K) ≠ 0 := fun h => by rw [h, map_zero] at hn; exact zero_ne_one hn
  have hlead : v (W.preΨ' n).leadingCoeff = 1 := by
    rw [W.leadingCoeff_preΨ' hn0, if_neg (Nat.not_even_iff_odd.mpr hodd)]
    exact hn
  obtain ⟨h₁, h₂, h₃, h₄, h₆⟩ := hW
  have := ReductionKernel.valuation_eval_eq_pow v
    (ReductionKernel.valuation_coeff_preΨ'_le_one v h₁ h₂ h₃ h₄ h₆ n) hlead hx
  rw [h0', map_zero] at this
  exact pow_ne_zero _ (zero_lt_one.trans hx).ne' this.symm

/-- On an integral model, `v(y) ≤ 1` when `v(x) ≤ 1` (on the curve). -/
lemma valuation_y_le_one {W : Affine K} (hW : IsIntegralModel v W) {x y : K}
    (h : W.Equation x y) (hx : v x ≤ 1) : v y ≤ 1 := by
  obtain ⟨h₁, h₂, h₃, h₄, h₆⟩ := hW
  rw [equation_iff] at h
  refine valuation_le_one_of_quadratic v (a := W.a₁ * x + W.a₃)
    (b := -(x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)) (by linear_combination h) ?_ ?_
  · rw [← Valuation.mem_integer_iff] at *
    exact add_mem (mul_mem h₁ hx) h₃
  · rw [← Valuation.mem_integer_iff] at *
    exact neg_mem (add_mem (add_mem (add_mem (pow_mem hx 3) (mul_mem h₂ (pow_mem hx 2)))
      (mul_mem h₄ hx)) h₆)

/-- **Odd prime-to-`p` torsion points are integral** on an integral model. -/
theorem valuation_le_one_of_nsmul_eq_zero [NeZero (2 : K)] [DecidableEq K] {W : Affine K}
    (hW : IsIntegralModel v W) {n : ℕ} (hodd : Odd n) (hn : v (n : K) = 1) {x y : K}
    (h : W.Nonsingular x y) (hP : n • Point.some x y h = 0) : v x ≤ 1 ∧ v y ≤ 1 := by
  have hx : v x ≤ 1 := by
    by_contra hcon
    exact nsmul_ne_zero_of_one_lt v hW hodd hn h (not_le.mp hcon) hP
  exact ⟨hx, valuation_y_le_one v hW h.1 hx⟩

end Kernel

end Iut.IntegralTorsion
