/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Mathlib

/-!
# The kernel of reduction of an elliptic curve has no prime-to-`p` torsion

For a field `K` with a valuation `v` and a Weierstrass curve `W : y² = x³ + a₂x² + a₄x + a₆`
with `v`-integral coefficients (`a₁ = a₃ = 0`, `v(2) = 1`):

* `Iut.ReductionKernel.nsmul_ne_zero_of_one_lt`, **the kernel of reduction has no prime-to-`p`
  torsion**: an affine point `P = (x, y)` with `v(x) > 1` has `n • P ≠ 0` for every odd `n` with
  `v(n) = 1`. The `n`-division polynomial `ψₙ(P) = Ψₙ(x)` is a polynomial in `x` of degree
  `(n² − 1)/2` with integral coefficients and leading coefficient `n`, so
  `v(ψₙ(P)) = v(x)^{(n²−1)/2} ≠ 0` (`Iut.ReductionKernel.valuation_eval_eq_pow`). The
  description `n • P = 0 ↔ ψₙ(P) = 0` of the multiples by the division polynomials is the
  hypothesis `Iut.ReductionKernel.DivPolyHyp` (in the form of the normalized elliptic
  divisibility sequence `normEDS (2y) (Ψ₃(x)) (preΨ₄(x))`, proved in
  `Iut.Torsion.smul_eq_zero_iff_eds`).
* `Iut.ReductionKernel.sub_eq_zero_or_one_lt`, **congruent points differ by a point of the kernel
  of reduction**: if `P ≡ Q mod 𝔪` (integral coordinates, congruent) and the reduction of `P` is a
  nonsingular point of the reduced curve (`v(f'(x)) = 1` or `v(2y) = 1`), then `P − Q = 0` or
  `v(x(P − Q)) > 1`; at a good model the nonsingularity of the reduction is automatic
  (`Iut.ReductionKernel.nonsingular_reduction_of_Δ`, from the Bézout identity
  `A f + B f' = −disc f`, `Δ = 16 disc f`).
* `Iut.ReductionKernel.eq_of_nsmul_eq_zero_of_congr`: two congruent `n`-torsion points (`n` odd,
  `v(n) = 1`) with nonsingular reduction are equal (**the reduction map is injective on the
  prime-to-`p` torsion**).
-/

namespace Iut.ReductionKernel

open WeierstrassCurve WeierstrassCurve.Affine Polynomial

variable {K : Type*} [Field K] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
  (v : Valuation K Γ)

/-! ### Valuations of polynomial values -/

/-- Natural numbers are `v`-integral. -/
lemma valuation_natCast_le_one (n : ℕ) : v (n : K) ≤ 1 := by
  induction n with
  | zero => rw [Nat.cast_zero, map_zero]; exact zero_le_one
  | succ n ih =>
    rw [Nat.cast_succ]
    exact (Valuation.map_add _ _ _).trans (max_le ih (by rw [map_one]))

/-- `v(f(x)) = v(x)^{deg f}` for `v(x) > 1`, when the coefficients of `f` are integral and its
leading coefficient is a unit. -/
theorem valuation_eval_eq_pow {f : K[X]} (hf : ∀ i, v (f.coeff i) ≤ 1)
    (hlead : v f.leadingCoeff = 1) {x : K} (hx : 1 < v x) :
    v (f.eval x) = v x ^ f.natDegree := by
  have hx0 : v x ≠ 0 := (zero_lt_one.trans hx).ne'
  rw [eval_eq_sum_range, Finset.sum_range_succ]
  have htop : v (f.coeff f.natDegree * x ^ f.natDegree) = v x ^ f.natDegree := by
    rw [map_mul, map_pow, ← leadingCoeff, hlead, one_mul]
  rw [Valuation.map_add_eq_of_lt_right, htop]
  rw [htop]
  refine Valuation.map_sum_lt _ (pow_ne_zero _ hx0) fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [map_mul, map_pow]
  calc v (f.coeff i) * v x ^ i ≤ 1 * v x ^ i := mul_le_mul_left (hf i) _
    _ = v x ^ i := one_mul _
    _ < v x ^ f.natDegree := pow_lt_pow_right₀ hx hi

/-! ### The division polynomials at a point -/

variable (W : Affine K) [DecidableEq K]

/-- **The division-polynomial description of the multiples of a point**: `n • P = 0` iff the
`n`-th term of the normalized elliptic divisibility sequence with initial values
`2y, Ψ₃(x), preΨ₄(x)` vanishes (for `a₁ = a₃ = 0`; `Iut.Torsion.smul_eq_zero_iff_eds`). -/
def DivPolyHyp : Prop :=
  ∀ (x y : K) (h : W.Nonsingular x y) (n : ℕ),
    n • Point.some x y h = 0 ↔ normEDS (2 * y) (W.Ψ₃.eval x) (W.preΨ₄.eval x) n = 0

variable {W}

omit [DecidableEq K] in
/-- `Ψ₂Sq(x) = (2y)²` on the curve, for `a₁ = a₃ = 0`. -/
lemma Ψ₂Sq_eval_eq (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0) {x y : K} (h : W.Equation x y) :
    W.Ψ₂Sq.eval x = (2 * y) ^ 2 := by
  rw [equation_iff, ha₁, ha₃] at h
  simp only [Ψ₂Sq, b₂, b₄, b₆, ha₁, ha₃, eval_add, eval_mul, eval_C, eval_pow, eval_X]
  linear_combination 4 * h.symm

omit [DecidableEq K] in
/-- The normalized EDS at a point is `Ψₙ'(x)·(2y)^{[n even]}`. -/
lemma normEDS_eq_eval_preΨ' (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0) {x y : K} (h : W.Equation x y)
    (n : ℕ) :
    normEDS (2 * y) (W.Ψ₃.eval x) (W.preΨ₄.eval x) n =
      (W.preΨ' n).eval x * if Even n then 2 * y else 1 := by
  rw [normEDS, preNormEDS_ofNat, preΨ', ← coe_evalRingHom, map_preNormEDS', coe_evalRingHom,
    eval_pow, Ψ₂Sq_eval_eq ha₁ ha₃ h]
  simp only [Int.even_coe_nat]
  ring_nf

omit [DecidableEq K] in
/-- The coefficients of `Ψₙ'` are integral when the coefficients of `W` are. -/
lemma valuation_coeff_preΨ'_le_one (ha₁ : v W.a₁ ≤ 1) (ha₂ : v W.a₂ ≤ 1) (ha₃ : v W.a₃ ≤ 1)
    (ha₄ : v W.a₄ ≤ 1) (ha₆ : v W.a₆ ≤ 1) (n i : ℕ) : v ((W.preΨ' n).coeff i) ≤ 1 := by
  let W₀ : WeierstrassCurve v.integer :=
    ⟨⟨W.a₁, ha₁⟩, ⟨W.a₂, ha₂⟩, ⟨W.a₃, ha₃⟩, ⟨W.a₄, ha₄⟩, ⟨W.a₆, ha₆⟩⟩
  have hW : W = W₀.map (v.integer.subtype) := by
    ext <;> rfl
  rw [hW, map_preΨ', coeff_map]
  exact ((W₀.preΨ' n).coeff i).2

/-- **The kernel of reduction has no prime-to-`p` torsion**: for an affine point `P = (x, y)`
with `v(x) > 1` and an odd `n` with `v(n) = 1`, `n • P ≠ 0`. -/
theorem nsmul_ne_zero_of_one_lt (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0) (ha₂ : v W.a₂ ≤ 1)
    (ha₄ : v W.a₄ ≤ 1) (ha₆ : v W.a₆ ≤ 1) (hψ : DivPolyHyp W) {n : ℕ} (hodd : Odd n)
    (hn : v (n : K) = 1) {x y : K} (h : W.Nonsingular x y) (hx : 1 < v x) :
    n • Point.some x y h ≠ 0 := by
  rw [Ne, hψ, normEDS_eq_eval_preΨ' ha₁ ha₃ h.1, if_neg (Nat.not_even_iff_odd.mpr hodd), mul_one]
  intro h0
  have hn0 : (n : K) ≠ 0 := fun h => by rw [h, map_zero] at hn; exact zero_ne_one hn
  have hlead : v (W.preΨ' n).leadingCoeff = 1 := by
    rw [W.leadingCoeff_preΨ' hn0, if_neg (Nat.not_even_iff_odd.mpr hodd)]
    exact hn
  have := valuation_eval_eq_pow v
    (valuation_coeff_preΨ'_le_one v (by rw [ha₁, map_zero]; exact zero_le_one) ha₂
      (by rw [ha₃, map_zero]; exact zero_le_one) ha₄ ha₆ n) hlead hx
  rw [h0, map_zero] at this
  exact pow_ne_zero _ (zero_lt_one.trans hx).ne' this.symm

omit [DecidableEq K] in
/-- The coordinates of a point in the kernel of reduction of the coordinates: `v(y) ≤ 1` when
`v(x) ≤ 1` (on the curve). -/
lemma valuation_y_le_one (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0) (ha₂ : v W.a₂ ≤ 1)
    (ha₄ : v W.a₄ ≤ 1) (ha₆ : v W.a₆ ≤ 1) {x y : K} (h : W.Equation x y) (hx : v x ≤ 1) :
    v y ≤ 1 := by
  rw [equation_iff, ha₁, ha₃] at h
  simp only [zero_mul, add_zero] at h
  have hint : ∀ z : K, v z ≤ 1 ↔ z ∈ v.integer := fun z => (Valuation.mem_integer_iff v z).symm
  have hrhs : v (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) ≤ 1 := by
    rw [hint] at hx ha₂ ha₄ ha₆ ⊢
    exact add_mem (add_mem (add_mem (pow_mem hx 3) (mul_mem ha₂ (pow_mem hx 2)))
      (mul_mem ha₄ hx)) ha₆
  have hy2 : v y ^ 2 ≤ 1 := by
    rw [← map_pow, h]
    exact hrhs
  by_contra hcon
  exact absurd hy2 (not_le.mpr (one_lt_pow₀ (not_le.mp hcon) two_ne_zero))

/-- **Prime-to-`p` torsion points are integral**. -/
theorem valuation_le_one_of_nsmul_eq_zero (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0) (ha₂ : v W.a₂ ≤ 1)
    (ha₄ : v W.a₄ ≤ 1) (ha₆ : v W.a₆ ≤ 1) (hψ : DivPolyHyp W) {n : ℕ} (hodd : Odd n)
    (hn : v (n : K) = 1) {x y : K} (h : W.Nonsingular x y) (hP : n • Point.some x y h = 0) :
    v x ≤ 1 ∧ v y ≤ 1 := by
  have hx : v x ≤ 1 := by
    by_contra hcon
    exact nsmul_ne_zero_of_one_lt v ha₁ ha₃ ha₂ ha₄ ha₆ hψ hodd hn h (not_le.mp hcon) hP
  exact ⟨hx, valuation_y_le_one v ha₁ ha₃ ha₂ ha₄ ha₆ h.1 hx⟩

/-! ### Nonsingular reduction -/

omit [DecidableEq K] in
/-- The Bézout identity `A·f + B·f' = −disc(f)` for the cubic `f = X³ + aX² + bX + c`. -/
lemma cubic_bezout (a b c x : K) :
    ((6 * a ^ 2 - 18 * b) * x + (4 * a ^ 3 - 15 * a * b + 27 * c)) *
        (x ^ 3 + a * x ^ 2 + b * x + c) +
      ((6 * b - 2 * a ^ 2) * x ^ 2 + (7 * a * b - 2 * a ^ 3 - 9 * c) * x +
        (4 * b ^ 2 - a ^ 2 * b - 3 * a * c)) * (3 * x ^ 2 + 2 * a * x + b) =
      -(a ^ 2 * b ^ 2 - 4 * b ^ 3 - 4 * a ^ 3 * c + 18 * a * b * c - 27 * c ^ 2) := by
  ring

omit [DecidableEq K] in
/-- `Δ = 16·disc(f)` for `a₁ = a₃ = 0`. -/
lemma Δ_eq_of_a₁_a₃ (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0) :
    W.Δ = 16 * (W.a₂ ^ 2 * W.a₄ ^ 2 - 4 * W.a₄ ^ 3 - 4 * W.a₂ ^ 3 * W.a₆ +
      18 * W.a₂ * W.a₄ * W.a₆ - 27 * W.a₆ ^ 2) := by
  simp only [WeierstrassCurve.Δ, b₂, b₄, b₆, b₈, ha₁, ha₃]
  ring

omit [DecidableEq K] in
/-- **Nonsingular reduction at a good model**: for a point `(x, y)` with integral coordinates
on a model with `v(Δ) = 1` and `v(2) = 1`, `v(f'(x)) = 1` or `v(2y) = 1`. -/
theorem nonsingular_reduction_of_Δ (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0) (ha₂ : v W.a₂ ≤ 1)
    (ha₄ : v W.a₄ ≤ 1) (ha₆ : v W.a₆ ≤ 1) (hΔ : v W.Δ = 1) (h2 : v 2 = 1) {x y : K}
    (h : W.Equation x y) (hx : v x ≤ 1) :
    v (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) = 1 ∨ v (2 * y) = 1 := by
  by_contra hcon
  obtain ⟨hfx, hy⟩ := not_or.mp hcon
  have hint : ∀ z : K, v z ≤ 1 ↔ z ∈ v.integer := fun z => (Valuation.mem_integer_iff v z).symm
  have hy' : v y < 1 := by
    rw [map_mul, h2, one_mul] at hy
    exact lt_of_le_of_ne (valuation_y_le_one v ha₁ ha₃ ha₂ ha₄ ha₆ h hx) hy
  have hfx' : v (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) < 1 := by
    refine lt_of_le_of_ne ?_ hfx
    rw [hint] at hx ha₂ ha₄ ⊢
    have h3 : (3 : K) ∈ v.integer := by
      rw [← hint]; exact valuation_natCast_le_one v 3
    have h2' : (2 : K) ∈ v.integer := by
      rw [← hint]; exact valuation_natCast_le_one v 2
    exact add_mem (add_mem (mul_mem h3 (pow_mem hx 2)) (mul_mem (mul_mem h2' ha₂) hx)) ha₄
  have hD : v (W.a₂ ^ 2 * W.a₄ ^ 2 - 4 * W.a₄ ^ 3 - 4 * W.a₂ ^ 3 * W.a₆ +
      18 * W.a₂ * W.a₄ * W.a₆ - 27 * W.a₆ ^ 2) = 1 := by
    have h16 : v 16 = 1 := by
      have : (16 : K) = 2 ^ 4 := by norm_num
      rw [this, map_pow, h2, one_pow]
    rw [Δ_eq_of_a₁_a₃ ha₁ ha₃, map_mul, h16, one_mul] at hΔ
    exact hΔ
  have hf : x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ = y ^ 2 := by
    rw [equation_iff, ha₁, ha₃] at h
    linear_combination -h
  have hbez := cubic_bezout W.a₂ W.a₄ W.a₆ x
  rw [hf] at hbez
  have hA : v (((6 * W.a₂ ^ 2 - 18 * W.a₄) * x + (4 * W.a₂ ^ 3 - 15 * W.a₂ * W.a₄ +
      27 * W.a₆)) * y ^ 2) < 1 := by
    rw [map_mul, map_pow]
    have hAint : v ((6 * W.a₂ ^ 2 - 18 * W.a₄) * x + (4 * W.a₂ ^ 3 - 15 * W.a₂ * W.a₄ +
        27 * W.a₆)) ≤ 1 := by
      rw [hint] at hx ha₂ ha₄ ha₆ ⊢
      have hn : ∀ m : ℕ, (m : K) ∈ v.integer := fun m => by
        rw [← hint]; exact valuation_natCast_le_one v m
      have h6 := hn 6; have h18 := hn 18; have h4 := hn 4; have h15 := hn 15; have h27 := hn 27
      push_cast at h6 h18 h4 h15 h27
      exact add_mem (mul_mem (sub_mem (mul_mem h6 (pow_mem ha₂ 2)) (mul_mem h18 ha₄)) hx)
        (add_mem (sub_mem (mul_mem h4 (pow_mem ha₂ 3)) (mul_mem (mul_mem h15 ha₂) ha₄))
          (mul_mem h27 ha₆))
    calc _ ≤ 1 * v y ^ 2 := mul_le_mul_left hAint _
      _ = v y ^ 2 := one_mul _
      _ < 1 := pow_lt_one₀ zero_le hy' two_ne_zero
  have hB : v (((6 * W.a₄ - 2 * W.a₂ ^ 2) * x ^ 2 + (7 * W.a₂ * W.a₄ - 2 * W.a₂ ^ 3 -
      9 * W.a₆) * x + (4 * W.a₄ ^ 2 - W.a₂ ^ 2 * W.a₄ - 3 * W.a₂ * W.a₆)) *
      (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄)) < 1 := by
    rw [map_mul]
    have hBint : v ((6 * W.a₄ - 2 * W.a₂ ^ 2) * x ^ 2 + (7 * W.a₂ * W.a₄ - 2 * W.a₂ ^ 3 -
        9 * W.a₆) * x + (4 * W.a₄ ^ 2 - W.a₂ ^ 2 * W.a₄ - 3 * W.a₂ * W.a₆)) ≤ 1 := by
      rw [hint] at hx ha₂ ha₄ ha₆ ⊢
      have hn : ∀ m : ℕ, (m : K) ∈ v.integer := fun m => by
        rw [← hint]; exact valuation_natCast_le_one v m
      have h6 := hn 6; have h2' := hn 2; have h7 := hn 7; have h9 := hn 9; have h4 := hn 4
      have h3 := hn 3
      push_cast at h6 h2' h7 h9 h4 h3
      exact add_mem (add_mem (mul_mem (sub_mem (mul_mem h6 ha₄) (mul_mem h2' (pow_mem ha₂ 2)))
        (pow_mem hx 2)) (mul_mem (sub_mem (sub_mem (mul_mem (mul_mem h7 ha₂) ha₄)
          (mul_mem h2' (pow_mem ha₂ 3))) (mul_mem h9 ha₆)) hx))
        (sub_mem (sub_mem (mul_mem h4 (pow_mem ha₄ 2)) (mul_mem (pow_mem ha₂ 2) ha₄))
          (mul_mem (mul_mem h3 ha₂) ha₆))
    calc _ ≤ 1 * v (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) := mul_le_mul_left hBint _
      _ = _ := one_mul _
      _ < 1 := hfx'
  have := (Valuation.map_add _ _ _).trans_lt (max_lt hA hB)
  rw [hbez, Valuation.map_neg, hD] at this
  exact lt_irrefl _ this

/-! ### Congruent points -/

omit [DecidableEq K] in
/-- `-(x, y) = (x, -y)` for `a₁ = a₃ = 0`. -/
lemma negY_eq (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0) (x y : K) : W.negY x y = -y := by
  simp [negY, ha₁, ha₃]

omit [DecidableEq K] in
/-- The difference of two affine points: the identity `(y₁ − y₂)(y₁ + y₂) = (x₁ − x₂)·g`. -/
lemma sub_mul_add_eq (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0) {x₁ y₁ x₂ y₂ : K}
    (h₁ : W.Equation x₁ y₁) (h₂ : W.Equation x₂ y₂) :
    (y₁ - y₂) * (y₁ + y₂) =
      (x₁ - x₂) * (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + W.a₂ * (x₁ + x₂) + W.a₄) := by
  rw [equation_iff, ha₁, ha₃] at h₁ h₂
  linear_combination h₁ - h₂

/-- **Congruent points differ by a point of the kernel of reduction**: for two affine points
`P = (x₁, y₁)`, `Q = (x₂, y₂)` with integral coordinates and `P ≡ Q mod 𝔪`, whose reduction is a
nonsingular point of the reduced curve, `P − Q = 0` or `v(x(P − Q)) > 1`. -/
theorem sub_eq_zero_or_one_lt (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0) (ha₂ : v W.a₂ ≤ 1)
    (h2 : v 2 = 1) {x₁ y₁ x₂ y₂ : K} (h₁ : W.Nonsingular x₁ y₁)
    (h₂ : W.Nonsingular x₂ y₂) (hx₁ : v x₁ ≤ 1) (hy₁ : v y₁ ≤ 1) (hx₂ : v x₂ ≤ 1)
    (hy₂ : v y₂ ≤ 1) (hx : v (x₁ - x₂) < 1) (hy : v (y₁ - y₂) < 1)
    (hns : v (3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄) = 1 ∨ v (2 * y₁) = 1) :
    Point.some x₁ y₁ h₁ - Point.some x₂ y₂ h₂ = 0 ∨
      ∃ (x y : K) (h : W.Nonsingular x y),
        Point.some x₁ y₁ h₁ - Point.some x₂ y₂ h₂ = Point.some x y h ∧ 1 < v x := by
  have hint : ∀ z : K, v z ≤ 1 ↔ z ∈ v.integer := fun z => (Valuation.mem_integer_iff v z).symm
  have hneg : W.negY x₂ y₂ = -y₂ := negY_eq ha₁ ha₃ x₂ y₂
  have hneg' : W.negY x₂ (-y₂) = y₂ := by rw [negY_eq ha₁ ha₃, neg_neg]
  rw [sub_eq_add_neg, Point.neg_some]
  -- the key claim: the slope of the line through `P` and `-Q` has `v > 1`
  suffices key : ¬ (x₁ = x₂ ∧ y₁ = W.negY x₂ (W.negY x₂ y₂)) →
      1 < v (W.slope x₁ x₂ y₁ (W.negY x₂ y₂)) by
    by_cases hxy : x₁ = x₂ ∧ y₁ = W.negY x₂ (W.negY x₂ y₂)
    · left
      exact Point.add_of_Y_eq hxy.1 hxy.2
    · right
      refine ⟨_, _, _, Point.add_some hxy, ?_⟩
      have hL := key hxy
      have hL2 : 1 < v (W.slope x₁ x₂ y₁ (W.negY x₂ y₂)) ^ 2 := one_lt_pow₀ hL two_ne_zero
      have hrest : v (W.a₂ + x₁ + x₂) ≤ 1 := by
        rw [hint] at ha₂ hx₁ hx₂ ⊢
        exact add_mem (add_mem ha₂ hx₁) hx₂
      have : W.addX x₁ x₂ (W.slope x₁ x₂ y₁ (W.negY x₂ y₂)) =
          W.slope x₁ x₂ y₁ (W.negY x₂ y₂) ^ 2 - (W.a₂ + x₁ + x₂) := by
        simp only [addX, ha₁]; ring
      rw [this, Valuation.map_sub_eq_of_lt_left _ (by rw [map_pow]; exact hrest.trans_lt hL2),
        map_pow]
      exact hL2
  intro hxy
  rw [hneg, hneg'] at hxy
  by_cases hx12 : x₁ = x₂
  · -- `Q = ±P`; here `Q = -P` and `P - Q = 2P`
    subst hx12
    have hy12 : y₁ ≠ y₂ := fun h => hxy ⟨rfl, h⟩
    have hy12' : y₁ = -y₂ := by
      rcases Y_eq_of_X_eq h₁.1 h₂.1 rfl with h | h
      · exact absurd h hy12
      · rw [h, hneg]
    have hy₁ne : ¬ y₁ = -(-y₂) - W.a₁ * x₁ - W.a₃ := by
      rw [neg_neg, ha₁, ha₃, zero_mul, sub_zero, sub_zero]
      exact hy12
    rw [hneg, slope_of_Y_ne' hy₁ne, ha₁, ha₃, zero_mul, sub_zero, zero_mul, sub_zero, sub_zero,
      sub_neg_eq_add, map_div₀]
    have h2y : v (y₁ + y₁) < 1 := by
      have : y₁ + y₁ = y₁ - y₂ := by rw [hy12']; ring
      rw [this]; exact hy
    have h2y' : v (2 * y₁) < 1 := by rw [two_mul]; exact h2y
    have hfx : v (3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄) = 1 := by
      rcases hns with hns | hns
      · exact hns
      · exact absurd hns h2y'.ne
    have h2y0 : v (y₁ + y₁) ≠ 0 := by
      rw [Ne, Valuation.zero_iff]
      intro hcon
      have h2ne : (2 : K) ≠ 0 := fun h => by rw [h, map_zero] at h2; exact zero_ne_one h2
      have hy0 : y₁ = 0 := by
        have : 2 * y₁ = 0 := by rw [two_mul]; exact hcon
        exact (mul_eq_zero.mp this).resolve_left h2ne
      apply hy12
      rw [hy0] at hy12' ⊢
      rw [eq_comm, ← neg_eq_zero, ← hy12']
    rw [hfx, one_div, one_lt_inv₀ (lt_of_le_of_ne zero_le (Ne.symm h2y0))]
    exact h2y
  · -- `x₁ ≠ x₂`: the chord through `P` and `-Q` has slope `(y₁ + y₂)/(x₁ - x₂)`
    rw [hneg, slope_of_X_ne hx12, sub_neg_eq_add, map_div₀]
    have hx0 : v (x₁ - x₂) ≠ 0 := by
      rw [Ne, Valuation.zero_iff, sub_eq_zero]; exact hx12
    have hxpos : 0 < v (x₁ - x₂) := lt_of_le_of_ne zero_le (Ne.symm hx0)
    by_cases hsum : v (y₁ + y₂) = 1
    · rw [hsum, one_div, one_lt_inv₀ hxpos]
      exact hx
    · have hsum' : v (y₁ + y₂) < 1 := by
        refine lt_of_le_of_ne ?_ hsum
        rw [hint] at hy₁ hy₂ ⊢
        exact add_mem hy₁ hy₂
      have h2y : v (2 * y₁) < 1 := by
        have : 2 * y₁ = (y₁ + y₂) + (y₁ - y₂) := by ring
        rw [this]
        exact (Valuation.map_add _ _ _).trans_lt (max_lt hsum' hy)
      have hfx : v (3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄) = 1 := by
        rcases hns with hns | hns
        · exact hns
        · exact absurd hns h2y.ne
      set g := x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + W.a₂ * (x₁ + x₂) + W.a₄ with hg
      have hg1 : v g = 1 := by
        have hdiff : g - (3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄) =
            (x₂ - x₁) * (x₂ + 2 * x₁ + W.a₂) := by rw [hg]; ring
        have hd : v (g - (3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄)) < 1 := by
          rw [hdiff, map_mul, Valuation.map_sub_swap]
          have hr : v (x₂ + 2 * x₁ + W.a₂) ≤ 1 := by
            rw [hint] at hx₁ hx₂ ha₂ ⊢
            have h2' : (2 : K) ∈ v.integer := by rw [← hint]; exact valuation_natCast_le_one v 2
            exact add_mem (add_mem hx₂ (mul_mem h2' hx₁)) ha₂
          calc v (x₁ - x₂) * v (x₂ + 2 * x₁ + W.a₂) ≤ v (x₁ - x₂) * 1 :=
                mul_le_mul_right hr _
            _ < 1 := by rw [mul_one]; exact hx
        have : g = (3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄) +
            (g - (3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄)) := by ring
        rw [this, Valuation.map_add_eq_of_lt_left _ (by rw [hfx]; exact hd), hfx]
      have hid := sub_mul_add_eq ha₁ ha₃ h₁.1 h₂.1
      rw [← hg] at hid
      have hy12 : y₁ - y₂ ≠ 0 := by
        intro hcon
        rw [hcon, zero_mul, eq_comm, mul_eq_zero] at hid
        rcases hid with hid | hid
        · exact hx12 (sub_eq_zero.mp hid)
        · rw [hid, map_zero] at hg1; exact zero_ne_one hg1
      have hL : (y₁ + y₂) / (x₁ - x₂) = g / (y₁ - y₂) := by
        rw [div_eq_div_iff (sub_ne_zero.mpr hx12) hy12]
        linear_combination hid
      rw [← map_div₀, hL, map_div₀, hg1, one_div,
        one_lt_inv₀ (lt_of_le_of_ne zero_le (Ne.symm ((Valuation.ne_zero_iff _).mpr hy12)))]
      exact hy

/-- **The reduction map is injective on the prime-to-`p` torsion**: two congruent `n`-torsion
points (`n` odd, `v(n) = 1`) with nonsingular reduction are equal. -/
theorem eq_of_nsmul_eq_zero_of_congr (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0) (ha₂ : v W.a₂ ≤ 1)
    (ha₄ : v W.a₄ ≤ 1) (ha₆ : v W.a₆ ≤ 1) (h2 : v 2 = 1) (hψ : DivPolyHyp W) {n : ℕ}
    (hodd : Odd n) (hn : v (n : K) = 1) {x₁ y₁ x₂ y₂ : K} (h₁ : W.Nonsingular x₁ y₁)
    (h₂ : W.Nonsingular x₂ y₂) (hP : n • Point.some x₁ y₁ h₁ = 0)
    (hQ : n • Point.some x₂ y₂ h₂ = 0) (hx : v (x₁ - x₂) < 1) (hy : v (y₁ - y₂) < 1)
    (hns : v (3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄) = 1 ∨ v (2 * y₁) = 1) :
    Point.some x₁ y₁ h₁ = Point.some x₂ y₂ h₂ := by
  obtain ⟨hx₁, hy₁⟩ := valuation_le_one_of_nsmul_eq_zero v ha₁ ha₃ ha₂ ha₄ ha₆ hψ hodd hn h₁ hP
  obtain ⟨hx₂, hy₂⟩ := valuation_le_one_of_nsmul_eq_zero v ha₁ ha₃ ha₂ ha₄ ha₆ hψ hodd hn h₂ hQ
  rcases sub_eq_zero_or_one_lt v ha₁ ha₃ ha₂ h2 h₁ h₂ hx₁ hy₁ hx₂ hy₂ hx hy hns with
    h0 | ⟨x, y, h, hsub, hx'⟩
  · exact sub_eq_zero.mp h0
  · exfalso
    have hD : n • (Point.some x₁ y₁ h₁ - Point.some x₂ y₂ h₂) = 0 := by
      rw [nsmul_sub, hP, hQ, sub_zero]
    rw [hsub] at hD
    exact nsmul_ne_zero_of_one_lt v ha₁ ha₃ ha₂ ha₄ ha₆ hψ hodd hn h hx' hD

end Iut.ReductionKernel
