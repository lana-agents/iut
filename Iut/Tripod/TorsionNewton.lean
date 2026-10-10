/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Torsion.Count
import Iut.Tripod.Legendre
import Heights.VariableChangePoint
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

/-!
# Torsion points on an integral model are almost integral

Let `W : y² = x³ + a₂x² + a₄x + a₆` be a Weierstrass curve over a number field `K` and `w` a
finite place of `K` at which `a₂, a₄, a₆` are integral. If `P = (x, y)` is an affine point with
`n • P = 0` (`n ≥ 1`), then `|n|_w² · |x|_w ≤ 1` (`Iut.TorsionNewton.apply_x_le`): the
`x`-coordinate is a root of the division polynomial `ΨSqₙ` (`Iut.Torsion.smul_eq_zero_iff_ΨSq`),
whose leading coefficient is `n²` and whose other coefficients are integral, and a dominant-term
(Newton polygon) argument bounds the root. In particular the `x`-coordinates of torsion points of
order prime to the residue characteristic are integral.
-/

namespace Iut.TorsionNewton

open WeierstrassCurve WeierstrassCurve.Affine Polynomial NumberField

variable {K : Type*} [Field K] [NumberField K] (w : FinitePlace K)

open scoped Classical in
/-- The ultrametric inequality for finite sums: if every term has `|·|_w ≤ B` and `B ≥ 0`,
so does the sum. -/
lemma apply_sum_le {ι : Type*} (s : Finset ι) (f : ι → K) {B : ℝ} (hB : 0 ≤ B)
    (hf : ∀ i ∈ s, w (f i) ≤ B) : w (∑ i ∈ s, f i) ≤ B := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hB]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (FinitePlace.add_le w _ _).trans (max_le (hf i (Finset.mem_insert_self _ _))
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj)))

open scoped Classical in
/-- The subring of `w`-integral elements. -/
def integers : Subring K where
  carrier := {z | w z ≤ 1}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, map_mul] at ha hb ⊢
    exact mul_le_one₀ ha (apply_nonneg w b) hb
  one_mem' := by simp
  add_mem' {a b} ha hb := (FinitePlace.add_le w a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' {a} ha := by simpa using ha

open scoped Classical in
lemma mem_integers {z : K} : z ∈ integers w ↔ w z ≤ 1 := Iff.rfl

open scoped Classical in
/-- The integral model of `W` over the `w`-integral elements. -/
def intModel (W : Affine K) (h₁ : w W.a₁ ≤ 1) (h₂ : w W.a₂ ≤ 1) (h₃ : w W.a₃ ≤ 1)
    (h₄ : w W.a₄ ≤ 1) (h₆ : w W.a₆ ≤ 1) : WeierstrassCurve (integers w) :=
  ⟨⟨W.a₁, h₁⟩, ⟨W.a₂, h₂⟩, ⟨W.a₃, h₃⟩, ⟨W.a₄, h₄⟩, ⟨W.a₆, h₆⟩⟩

open scoped Classical in
lemma intModel_map (W : Affine K) (h₁ : w W.a₁ ≤ 1) (h₂ : w W.a₂ ≤ 1) (h₃ : w W.a₃ ≤ 1)
    (h₄ : w W.a₄ ≤ 1) (h₆ : w W.a₆ ≤ 1) :
    (intModel w W h₁ h₂ h₃ h₄ h₆).map (integers w).subtype = W := rfl

open scoped Classical in
/-- The coefficients of the division polynomials of an integral model are integral. -/
lemma apply_coeff_ΨSq_le_one (W : Affine K) (h₁ : w W.a₁ ≤ 1) (h₂ : w W.a₂ ≤ 1)
    (h₃ : w W.a₃ ≤ 1) (h₄ : w W.a₄ ≤ 1) (h₆ : w W.a₆ ≤ 1) (n : ℤ) (k : ℕ) :
    w ((W.ΨSq n).coeff k) ≤ 1 := by
  rw [← intModel_map w W h₁ h₂ h₃ h₄ h₆, map_ΨSq, coeff_map]
  exact ((intModel w W h₁ h₂ h₃ h₄ h₆).ΨSq n).coeff k |>.2

open scoped Classical in
/-- **The Newton bound for torsion points**: on a model with `a₁ = a₃ = 0` and `w`-integral
`a₂, a₄, a₆`, an affine point `(x, y)` with `n • (x, y) = 0` (`n ≥ 1`) has `|n|_w² |x|_w ≤ 1`. -/
theorem apply_x_le {W : Affine K} (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0) (h₂ : w W.a₂ ≤ 1)
    (h₄ : w W.a₄ ≤ 1) (h₆ : w W.a₆ ≤ 1) {n : ℕ} (hn : 1 ≤ n) {x y : K}
    (h : W.Nonsingular x y) (hP : n • Point.some x y h = 0) :
    w (n : K) ^ 2 * w x ≤ 1 := by
  have h₁ : w W.a₁ ≤ 1 := by rw [ha₁, map_zero]; exact zero_le_one
  have h₃ : w W.a₃ ≤ 1 := by rw [ha₃, map_zero]; exact zero_le_one
  have hroot : (W.ΨSq n).eval x = 0 := (Iut.Torsion.smul_eq_zero_iff_ΨSq ha₁ ha₃ h n).mp hP
  have hn1 : (1 : ℝ) ≥ w (n : K) :=
    IsNonarchimedean.apply_natCast_le_one (f := w) (fun a b => FinitePlace.add_le w a b)
  by_cases hx : w x ≤ 1
  · exact mul_le_one₀ (pow_le_one₀ (n := 2) (apply_nonneg w _) hn1) (apply_nonneg w x) hx
  rw [not_le] at hx
  set D := n ^ 2 - 1 with hD
  have hdeg : (W.ΨSq n).natDegree ≤ D := by
    have := natDegree_ΨSq_le W (n : ℤ)
    simpa [hD] using this
  have hlead : (W.ΨSq n).coeff D = (n : K) ^ 2 := by
    have := coeff_ΨSq W (n : ℤ)
    simpa [hD] using this
  have hsum := (W.ΨSq n).eval_eq_sum_range' (Nat.lt_succ_of_le hdeg) x
  rw [hroot, Finset.sum_range_succ, hlead] at hsum
  -- the leading term equals minus the sum of the lower terms
  have hlt : (n : K) ^ 2 * x ^ D = -∑ i ∈ Finset.range D, (W.ΨSq n).coeff i * x ^ i := by
    linear_combination -hsum
  have hbound : w (∑ i ∈ Finset.range D, (W.ΨSq n).coeff i * x ^ i) ≤ w x ^ (D - 1) := by
    refine apply_sum_le w _ _ (by positivity) fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [map_mul, map_pow]
    calc w ((W.ΨSq n).coeff i) * w x ^ i ≤ 1 * w x ^ (D - 1) := by
          gcongr
          · exact apply_coeff_ΨSq_le_one w W h₁ h₂ h₃ h₄ h₆ n i
          · exact hx.le
          · omega
      _ = w x ^ (D - 1) := one_mul _
  have hD1 : 1 ≤ D := by
    by_contra hD0
    have hD0 : D = 0 := by omega
    rw [hD0, pow_zero, mul_one, Finset.range_zero, Finset.sum_empty, neg_zero] at hlt
    have hn0 : (n : K) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    exact pow_ne_zero 2 hn0 hlt
  have hkey : w (n : K) ^ 2 * w x ^ D ≤ w x ^ (D - 1) := by
    have := congrArg w hlt
    rw [map_mul, map_pow, map_pow, map_neg_eq_map] at this
    rw [this]
    exact hbound
  have hxpos : 0 < w x := lt_trans zero_lt_one hx
  have : w x ^ D = w x ^ (D - 1) * w x := by
    rw [← pow_succ]; congr 1; omega
  rw [this, ← mul_assoc, mul_comm _ (w x ^ (D - 1)), mul_assoc] at hkey
  have hp : 0 < w x ^ (D - 1) := pow_pos hxpos _
  have := le_of_mul_le_mul_left (by linarith : w x ^ (D - 1) * (w (n : K) ^ 2 * w x) ≤
    w x ^ (D - 1) * 1) hp
  exact this

end Iut.TorsionNewton

/-! ### Legendre curves with a non-integral parameter -/

namespace Iut.TorsionNewton

open WeierstrassCurve WeierstrassCurve.Affine NumberField Iut.Tripod

variable {K : Type*} [Field K] [NumberField K] (w : FinitePlace K)

open scoped Classical in
/-- **The Newton bound on a Legendre curve**: for `W = E_λ` and an affine point `(x, y)` with
`n • (x, y) = 0` (`n ≥ 1`), `|n|_w² |x|_w ≤ max(1, |λ|_w)²`. For `|λ|_w > 1` the model is
rescaled by `u = λ` (`x = λ² X`), which is integral. -/
theorem apply_x_le_legendre {W : WeierstrassCurve K} [W.IsElliptic] {l : K}
    (hW : W = legendre l) (hl0 : l ≠ 0) {n : ℕ} (hn : 1 ≤ n) {x y : K}
    (h : W.toAffine.Nonsingular x y) (hP : n • (Point.some x y h : W.toAffine.Point) = 0) :
    w (n : K) ^ 2 * w x ≤ max 1 (w l) ^ 2 := by
  have hW₁ : W.a₁ = 0 := by subst hW; rfl
  have hW₂ : W.a₂ = -(1 + l) := by subst hW; rfl
  have hW₃ : W.a₃ = 0 := by subst hW; rfl
  have hW₄ : W.a₄ = l := by subst hW; rfl
  have hW₆ : W.a₆ = 0 := by subst hW; rfl
  have hmax : 1 ≤ max 1 (w l) := le_max_left _ _
  by_cases hl : w l ≤ 1
  · have h₂ : w W.a₂ ≤ 1 := by
      rw [hW₂, map_neg_eq_map]
      exact (FinitePlace.add_le w _ _).trans (max_le (by simp) hl)
    have h₄ : w W.a₄ ≤ 1 := by rw [hW₄]; exact hl
    have h₆ : w W.a₆ ≤ 1 := by rw [hW₆, map_zero]; exact zero_le_one
    exact (apply_x_le w hW₁ hW₃ h₂ h₄ h₆ hn h hP).trans (one_le_pow₀ hmax)
  · rw [not_le] at hl
    have hlpos : 0 < w l := lt_trans zero_lt_one hl
    set C : VariableChange K := ⟨Units.mk0 l hl0, 0, 0, 0⟩ with hC
    have hCu : (C.u : K) = l := rfl
    set P' := (C.pointAddEquiv W).symm (Point.some x y h) with hP'
    have hP'eq : P' = C.inversePointMap W (Point.some x y h) := rfl
    rw [VariableChange.inversePointMap_some] at hP'eq
    have hP'0 : n • P' = 0 := by rw [hP', ← map_nsmul, hP, map_zero]
    rw [hP'eq] at hP'0
    have hr : C.r = 0 := rfl
    have hinv : C.inverseX x = x / l ^ 2 := by
      rw [VariableChange.inverseX, hCu, hr, sub_zero]
      field_simp
    -- the rescaled model is integral
    have hlinv : w l⁻¹ ≤ 1 := by rw [map_inv₀]; exact inv_le_one_of_one_le₀ hl.le
    have hC₁ : (C • W).a₁ = 0 := by simp [variableChange_a₁, hW₁, hC]
    have hC₃ : (C • W).a₃ = 0 := by simp [variableChange_a₃, hW₃, hW₁, hC]
    have hC₂ : w (C • W).a₂ ≤ 1 := by
      have : (C • W).a₂ = -(l⁻¹ ^ 2 + l⁻¹) := by
        simp only [variableChange_a₂, hW₂, hW₁, hC, Units.val_inv_eq_inv_val, Units.val_mk0]
        field_simp
        ring
      rw [this, map_neg_eq_map]
      refine (FinitePlace.add_le w _ _).trans (max_le ?_ hlinv)
      rw [map_pow]; exact pow_le_one₀ (apply_nonneg w _) hlinv
    have hC₄ : w (C • W).a₄ ≤ 1 := by
      have : (C • W).a₄ = l⁻¹ ^ 3 := by
        simp only [variableChange_a₄, hW₄, hW₃, hW₂, hW₁, hC, Units.val_inv_eq_inv_val,
          Units.val_mk0]
        field_simp
        ring
      rw [this, map_pow]; exact pow_le_one₀ (apply_nonneg w _) hlinv
    have hC₆ : w (C • W).a₆ ≤ 1 := by
      have : (C • W).a₆ = 0 := by
        simp [variableChange_a₆, hW₆, hW₄, hW₃, hW₂, hW₁, hC]
      rw [this, map_zero]; exact zero_le_one
    have hN := apply_x_le w hC₁ hC₃ hC₂ hC₄ hC₆ hn _ hP'0
    rw [hinv, map_div₀, map_pow] at hN
    rw [max_eq_right hl.le]
    have hl2 : 0 < w l ^ 2 := by positivity
    rw [← mul_div_assoc, div_le_iff₀ hl2, one_mul] at hN
    exact hN

end Iut.TorsionNewton
