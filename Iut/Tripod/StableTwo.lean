/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Tripod.StableOdd

/-!
# Stable reduction from rational `3`-torsion (places of residue characteristic `≠ 3`)

**Theorem** (`Iut.hasStableReductionAt_of_three_torsion`). Let `E` be an elliptic curve over a
number field `F` whose `3`-torsion is rational: `E(F)` contains two points `P`, `Q` of order `3`
with `Q ∉ ⟨P⟩`. Then `E` has stable (good or multiplicative) reduction at every finite place
`w` of `F` of residue characteristic `≠ 3`. This is the case `n = 3` of Raynaud's criterion,
with an elementary proof:

1. **Flex points.** An affine point `P = (x, y)` with `3P = 0` satisfies `2P = −P`, so `P` is
   not `2`-torsion (`D := 2y + a₁x + a₃ ≠ 0`) and the tangent slope `λ = N/D`
   (`N := 3x² + 2a₂x + a₄ − a₁y`) satisfies `x(2P) = x`, i.e. `λ² + a₁λ − a₂ − 3x = 0`
   (`Iut.FlexData`, `Iut.FlexData.ofPoint`). Eliminating `λ` and `y` gives
   `ψ₃(x) = 3x⁴ + b₂x³ + 3b₄x² + 3b₆x + b₈ = 0` (`Iut.FlexData.psi3`). Flex data transports
   along changes of variables (`Iut.FlexData.variableChange`), so no transport of points
   along changes of variables is needed.
2. **Integrality.** On a `w`-integral model with `v(3) = 1`, a root of `ψ₃` is `w`-integral
   (the leading term `3x⁴` would dominate otherwise), and so are `y` and `λ`
   (`Iut.valuation_le_one_of_quartic`, `Iut.valuation_le_one_of_quadratic`).
3. **Normal form.** The integral change of variables `x = X + x(P)`, `y = Y + λX + y(P)`
   brings `E` to the form `N(A, B) : y² + Axy + By = x³` with `A`, `B` integral and `B ≠ 0`
   (`Iut.FlexData.variableChange_eq`), where `Δ = B³(A³ − 27B)` and `c₄ = A(A³ − 24B)`; the
   second point becomes a flex `(x, y)` with `x ≠ 0` and `g(x) = 0`,
   `g := 3x³ + A²x² + 3ABx + 3B²`.
4. **Descent** (`Iut.exists_isStableModel_normalForm`, by induction on `v(B)`): if `B` is a
   unit, `N(A, B)` is good or multiplicative; if `A` is a unit, it is multiplicative; if neither
   is a unit and `B ∈ 𝔪 ∖ 𝔪³`, the equation `g(x) = 0` with `x` integral is impossible by a
   dominant-term (Newton polygon) argument, using `v(3) = 1`; if `B ∈ 𝔪³`, rescale by a
   uniformizer, `(A, B, x) ↦ (A/π, B/π³, x/π²)`, and repeat.

Since `E_λ[3](ℚ̄) ≅ (ℤ/3)²` (`Iut.Tripod.legendre_torsionBasis`) and the
`3`-torsion of `E_λ` is rational over `F_λ`, the curve `E_λ/F_λ` of a point of the tripod has
stable reduction at every place of residue characteristic `≠ 3`
(`Iut.Tripod.stable_reduction_of_residueChar_ne_three`), and, with
`Iut.Tripod.stable_reduction_of_residueChar_ne_two`, at every finite place
(`Iut.Tripod.stable_reduction`).
-/

namespace Iut

open WeierstrassCurve WithZero
open scoped WithZero

/-! ## Flex points -/

section Flex

variable {K : Type*} [Field K]

/-- **Flex data** of a Weierstrass curve `W` over a field: an affine point `(x, y)` on `W` which
is not `2`-torsion (`D := 2y + a₁x + a₃ ≠ 0`), and the slope `λ = N/D` of the tangent line at
`(x, y)` (`N := 3x² + 2a₂x + a₄ − a₁y`), subject to `λ² + a₁λ − a₂ − 3x = 0`, which says
`x(2P) = x(P)`, i.e. `2P = −P`, i.e. `3P = 0`. -/
structure FlexData (W : WeierstrassCurve K) where
  /-- The `x`-coordinate. -/
  x : K
  /-- The `y`-coordinate. -/
  y : K
  /-- The tangent slope. -/
  lam : K
  /-- The point lies on `W`. -/
  equation : y ^ 2 + W.a₁ * x * y + W.a₃ * y = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆
  /-- The point is not `2`-torsion. -/
  ne : 2 * y + W.a₁ * x + W.a₃ ≠ 0
  /-- `λ · D = N`. -/
  lam_mul : lam * (2 * y + W.a₁ * x + W.a₃) = 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y
  /-- `x(2P) = x(P)`. -/
  lam_sq : lam ^ 2 + W.a₁ * lam - W.a₂ - 3 * x = 0

variable {W : WeierstrassCurve K}

/-- The `x`-coordinate of a flex point is a root of the `3`-division polynomial
`ψ₃ = 3x⁴ + b₂x³ + 3b₄x² + 3b₆x + b₈`. -/
lemma FlexData.psi3 (d : FlexData W) :
    3 * d.x ^ 4 + W.b₂ * d.x ^ 3 + 3 * W.b₄ * d.x ^ 2 + 3 * W.b₆ * d.x + W.b₈ = 0 := by
  have h1 := d.lam_mul
  have h2 := d.lam_sq
  have h3 := d.equation
  simp only [b₂, b₄, b₆, b₈]
  linear_combination (-(2 * d.y + W.a₁ * d.x + W.a₃) ^ 2) * h2 +
    (d.lam * (2 * d.y + W.a₁ * d.x + W.a₃) + (3 * d.x ^ 2 + 2 * W.a₂ * d.x + W.a₄ - W.a₁ * d.y) +
      W.a₁ * (2 * d.y + W.a₁ * d.x + W.a₃)) * h1 +
    (-(W.a₁ ^ 2 + 4 * W.a₂ + 12 * d.x)) * h3

section Point

variable [DecidableEq K]

/-- An affine point `P` with `3P = 0` is not `2`-torsion and satisfies `x(2P) = x(P)`. -/
lemma flex_of_three_nsmul {x y : K} (h : W.toAffine.Nonsingular x y)
    (hP : 3 • (Affine.Point.some x y h : W.toAffine.Point) = 0) :
    y ≠ W.toAffine.negY x y ∧ W.toAffine.addX x x (W.toAffine.slope x x y y) = x := by
  have h2 : 2 • (Affine.Point.some x y h : W.toAffine.Point) = -Affine.Point.some x y h := by
    rw [eq_neg_iff_add_eq_zero, ← succ_nsmul]
    exact hP
  have hy : y ≠ W.toAffine.negY x y := by
    intro hy
    rw [two_nsmul, Affine.Point.add_self_of_Y_eq hy] at h2
    exact Affine.Point.some_ne_zero h (neg_eq_zero.mp h2.symm)
  refine ⟨hy, ?_⟩
  rw [two_nsmul, Affine.Point.add_self_of_Y_ne hy, Affine.Point.neg_some,
    Affine.Point.some.injEq] at h2
  exact h2.1

/-- The flex data of an affine point of order `3`. -/
noncomputable def FlexData.ofPoint {x y : K} (h : W.toAffine.Nonsingular x y)
    (hP : 3 • (Affine.Point.some x y h : W.toAffine.Point) = 0) : FlexData W :=
  have hy := (flex_of_three_nsmul h hP).1
  have hD : 2 * y + W.a₁ * x + W.a₃ ≠ 0 := by
    intro hD
    apply hy
    simp only [Affine.negY]
    linear_combination hD
  { x := x
    y := y
    lam := W.toAffine.slope x x y y
    equation := (Affine.equation_iff _ _).mp h.1
    ne := hD
    lam_mul := by
      rw [Affine.slope_of_Y_ne rfl hy]
      have e : y - W.toAffine.negY x y = 2 * y + W.a₁ * x + W.a₃ := by
        simp only [Affine.negY]
        ring
      rw [e]
      exact div_mul_cancel₀ _ hD
    lam_sq := by
      have := (flex_of_three_nsmul h hP).2
      simp only [Affine.addX] at this
      linear_combination this }

@[simp] lemma FlexData.ofPoint_x {x y : K} (h : W.toAffine.Nonsingular x y)
    (hP : 3 • (Affine.Point.some x y h : W.toAffine.Point) = 0) : (FlexData.ofPoint h hP).x = x :=
  rfl

end Point

/-- **Transport of flex data along a change of variables** `x = u²X + r`, `y = u³Y + u²sX + t`:
the point `(X, Y) = (u⁻²(x − r), u⁻³(y − s(x − r) − t))` with tangent slope `u⁻¹(λ − s)`. -/
def FlexData.variableChange (d : FlexData W) (C : VariableChange K) : FlexData (C • W) where
  x := (C.u : K)⁻¹ ^ 2 * (d.x - C.r)
  y := (C.u : K)⁻¹ ^ 3 * (d.y - C.s * (d.x - C.r) - C.t)
  lam := (C.u : K)⁻¹ * (d.lam - C.s)
  equation := by
    simp only [variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄,
      variableChange_a₆, Units.val_inv_eq_inv_val]
    linear_combination (C.u : K)⁻¹ ^ 6 * d.equation
  ne := by
    simp only [variableChange_a₁, variableChange_a₃, Units.val_inv_eq_inv_val]
    have e : 2 * ((C.u : K)⁻¹ ^ 3 * (d.y - C.s * (d.x - C.r) - C.t)) +
        (C.u : K)⁻¹ * (W.a₁ + 2 * C.s) * ((C.u : K)⁻¹ ^ 2 * (d.x - C.r)) +
        (C.u : K)⁻¹ ^ 3 * (W.a₃ + C.r * W.a₁ + 2 * C.t) =
        (C.u : K)⁻¹ ^ 3 * (2 * d.y + W.a₁ * d.x + W.a₃) := by ring
    rw [e]
    exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero C.u.ne_zero)) d.ne
  lam_mul := by
    simp only [variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄,
      Units.val_inv_eq_inv_val]
    linear_combination (C.u : K)⁻¹ ^ 4 * d.lam_mul
  lam_sq := by
    simp only [variableChange_a₁, variableChange_a₂, Units.val_inv_eq_inv_val]
    linear_combination (C.u : K)⁻¹ ^ 2 * d.lam_sq

@[simp] lemma FlexData.variableChange_x (d : FlexData W) (C : VariableChange K) :
    (d.variableChange C).x = (C.u : K)⁻¹ ^ 2 * (d.x - C.r) := rfl

/-- **The normal form of a flex**: the change of variables `x = X + x(P)`, `y = Y + λX + y(P)`
moves the flex point to the origin with horizontal tangent, giving the model
`y² + (a₁ + 2λ)xy + (a₃ + a₁x(P) + 2y(P))y = x³`. -/
lemma FlexData.variableChange_eq (d : FlexData W) :
    (⟨1, d.x, d.lam, d.y⟩ : VariableChange K) • W =
      ⟨W.a₁ + 2 * d.lam, 0, W.a₃ + d.x * W.a₁ + 2 * d.y, 0, 0⟩ := by
  ext <;> simp only [variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄,
    variableChange_a₆, inv_one, Units.val_one]
  · ring
  · linear_combination -d.lam_sq
  · ring
  · linear_combination -d.lam_mul
  · linear_combination -d.equation

end Flex

/-! ## The normal form `y² + Axy + By = x³` -/

section NormalForm

variable {K : Type*} [Field K]

/-- The Weierstrass curve `y² + Axy + By = x³`. -/
def normalForm (A B : K) : WeierstrassCurve K := ⟨A, 0, B, 0, 0⟩

variable (A B : K)

@[simp] lemma normalForm_a₁ : (normalForm A B).a₁ = A := rfl
@[simp] lemma normalForm_a₂ : (normalForm A B).a₂ = 0 := rfl
@[simp] lemma normalForm_a₃ : (normalForm A B).a₃ = B := rfl
@[simp] lemma normalForm_a₄ : (normalForm A B).a₄ = 0 := rfl
@[simp] lemma normalForm_a₆ : (normalForm A B).a₆ = 0 := rfl

lemma normalForm_b₂ : (normalForm A B).b₂ = A ^ 2 := by
  simp only [b₂, normalForm_a₁, normalForm_a₂]; ring

lemma normalForm_b₄ : (normalForm A B).b₄ = A * B := by
  simp only [b₄, normalForm_a₁, normalForm_a₃, normalForm_a₄]; ring

lemma normalForm_b₆ : (normalForm A B).b₆ = B ^ 2 := by
  simp only [b₆, normalForm_a₃, normalForm_a₆]; ring

lemma normalForm_b₈ : (normalForm A B).b₈ = 0 := by
  simp only [b₈, normalForm_a₁, normalForm_a₂, normalForm_a₃, normalForm_a₄, normalForm_a₆]; ring

/-- `Δ(y² + Axy + By = x³) = B³(A³ − 27B)`. -/
lemma normalForm_Δ : (normalForm A B).Δ = B ^ 3 * (A ^ 3 - 27 * B) := by
  simp only [Δ, normalForm_b₂, normalForm_b₄, normalForm_b₆, normalForm_b₈]; ring

/-- `c₄(y² + Axy + By = x³) = A(A³ − 24B)`. -/
lemma normalForm_c₄ : (normalForm A B).c₄ = A * (A ^ 3 - 24 * B) := by
  simp only [c₄, normalForm_b₂, normalForm_b₄]; ring

/-- Rescaling the normal form by `u = π`: `(A, B) ↦ (A/π, B/π³)`. -/
lemma normalForm_scale {π : K} (hπ : π ≠ 0) :
    (⟨Units.mk0 π hπ, 0, 0, 0⟩ : VariableChange K) • normalForm A B =
      normalForm (π⁻¹ * A) (π⁻¹ ^ 3 * B) := by
  ext <;> simp only [variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄,
    variableChange_a₆, normalForm_a₁, normalForm_a₂, normalForm_a₃, normalForm_a₄, normalForm_a₆,
    Units.val_inv_eq_inv_val, Units.val_mk0] <;> ring

end NormalForm

/-! ## Integrality of roots -/

section Integrality

variable {K : Type*} [Field K] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ)

/-- A root of a monic quadratic with integral coefficients is integral. -/
lemma valuation_le_one_of_quadratic {x a b : K} (h : x ^ 2 + a * x + b = 0) (ha : v a ≤ 1)
    (hb : v b ≤ 1) : v x ≤ 1 := by
  by_contra hx
  rw [not_le] at hx
  have h1 : v (a * x + b) < v (x ^ 2) := by
    rw [map_pow]
    refine lt_of_le_of_lt (Valuation.map_add v _ _) (max_lt ?_ ?_)
    · rw [map_mul]
      exact (mul_le_of_le_one_left zero_le ha).trans_lt (lt_self_pow₀ hx (by norm_num))
    · exact hb.trans_lt (one_lt_pow₀ hx (by norm_num))
  have h2 := Valuation.map_add_eq_of_lt_left v h1
  rw [← add_assoc, h, map_zero, map_pow] at h2
  exact pow_ne_zero _ (ne_of_gt (zero_lt_one.trans hx)) h2.symm

/-- A root of `3x⁴ + c₃x³ + c₂x² + c₁x + c₀` with integral coefficients is integral when `3` is
a unit. -/
lemma valuation_le_one_of_quartic (h3 : v 3 = 1) {x c₃ c₂ c₁ c₀ : K}
    (h : 3 * x ^ 4 + c₃ * x ^ 3 + c₂ * x ^ 2 + c₁ * x + c₀ = 0) (hc₃ : v c₃ ≤ 1) (hc₂ : v c₂ ≤ 1)
    (hc₁ : v c₁ ≤ 1) (hc₀ : v c₀ ≤ 1) : v x ≤ 1 := by
  by_contra hx
  rw [not_le] at hx
  have hx1 : 1 ≤ v x := hx.le
  have key : ∀ (c : K) (n : ℕ), v c ≤ 1 → n ≤ 3 → v (c * x ^ n) ≤ v x ^ 3 := by
    intro c n hc hn
    rw [map_mul, map_pow]
    exact (mul_le_of_le_one_left zero_le hc).trans (pow_le_pow_right₀ hx1 hn)
  have h1 : v (c₃ * x ^ 3 + c₂ * x ^ 2 + c₁ * x + c₀) < v (3 * x ^ 4) := by
    rw [map_mul, h3, one_mul, map_pow]
    refine lt_of_le_of_lt ?_ (pow_lt_pow_right₀ hx (by norm_num : 3 < 4))
    refine v.map_add_le (v.map_add_le (v.map_add_le ?_ ?_) ?_) ?_
    · exact key c₃ 3 hc₃ le_rfl
    · exact key c₂ 2 hc₂ (by norm_num)
    · simpa using key c₁ 1 hc₁ (by norm_num)
    · simpa using key c₀ 0 hc₀ (by norm_num)
  have h2 := Valuation.map_add_eq_of_lt_left v h1
  have e : 3 * x ^ 4 + (c₃ * x ^ 3 + c₂ * x ^ 2 + c₁ * x + c₀) =
      3 * x ^ 4 + c₃ * x ^ 3 + c₂ * x ^ 2 + c₁ * x + c₀ := by ring
  rw [e, h, map_zero, map_mul, h3, one_mul, map_pow] at h2
  exact pow_ne_zero _ (ne_of_gt (zero_lt_one.trans hx)) h2.symm

/-- `v(n) ≤ 1` for a numeral `n`. -/
lemma valuation_ofNat_le_one (n : ℕ) [n.AtLeastTwo] : v (OfNat.ofNat n : K) ≤ 1 :=
  (Valuation.mem_integer_iff v _).1 (ofNat_mem v.integer n)

/-- On an integral model, the `x`-coordinate of a flex point is integral (for `v(3) = 1`). -/
lemma FlexData.valuation_x_le_one {W : WeierstrassCurve K} (d : FlexData W)
    (hW : IsIntegralModel v W) (h3 : v 3 = 1) : v d.x ≤ 1 :=
  valuation_le_one_of_quartic v h3 d.psi3 hW.b₂ (by rw [map_mul, h3, one_mul]; exact hW.b₄)
    (by rw [map_mul, h3, one_mul]; exact hW.b₆) hW.b₈

/-- On an integral model, the `y`-coordinate of a flex point with integral `x`-coordinate is
integral. -/
lemma FlexData.valuation_y_le_one {W : WeierstrassCurve K} (d : FlexData W)
    (hW : IsIntegralModel v W) (hx : v d.x ≤ 1) : v d.y ≤ 1 := by
  obtain ⟨h₁, h₂, h₃, h₄, h₆⟩ := hW
  refine valuation_le_one_of_quadratic v (a := W.a₁ * d.x + W.a₃)
    (b := -(d.x ^ 3 + W.a₂ * d.x ^ 2 + W.a₄ * d.x + W.a₆)) (by linear_combination d.equation) ?_ ?_
  · rw [← Valuation.mem_integer_iff] at *
    exact add_mem (mul_mem h₁ hx) h₃
  · rw [← Valuation.mem_integer_iff] at *
    exact neg_mem (add_mem (add_mem (add_mem (pow_mem hx 3) (mul_mem h₂ (pow_mem hx 2)))
      (mul_mem h₄ hx)) h₆)

/-- On an integral model, the tangent slope at a flex point with integral `x`-coordinate is
integral. -/
lemma FlexData.valuation_lam_le_one {W : WeierstrassCurve K} (d : FlexData W)
    (hW : IsIntegralModel v W) (hx : v d.x ≤ 1) : v d.lam ≤ 1 := by
  obtain ⟨h₁, h₂, -, -, -⟩ := hW
  refine valuation_le_one_of_quadratic v (a := W.a₁) (b := -W.a₂ - 3 * d.x)
    (by linear_combination d.lam_sq) h₁ ?_
  rw [← Valuation.mem_integer_iff] at *
  exact sub_mem (neg_mem h₂) (mul_mem (ofNat_mem _ 3) hx)

end Integrality

/-! ## Arithmetic in `ℤᵐ⁰` -/

section WithZero

/-- A nonzero element `a ≤ 1` of `ℤᵐ⁰` is `exp(−n)` for a natural number `n`. -/
lemma exists_nat_eq_exp_neg {a : ℤᵐ⁰} (h0 : a ≠ 0) (h1 : a ≤ 1) :
    ∃ n : ℕ, a = exp (-(n : ℤ)) := by
  refine ⟨(-log a).toNat, ?_⟩
  have hlog : log a ≤ 0 := by
    rw [← exp_le_exp, exp_log h0, exp_zero]
    exact h1
  rw [Int.toNat_of_nonneg (by omega), neg_neg, exp_log h0]

/-- `a < exp m` implies `a ≤ exp (m − 1)` in `ℤᵐ⁰`. -/
lemma le_exp_sub_one_of_lt_exp {a : ℤᵐ⁰} {m : ℤ} (h : a < exp m) : a ≤ exp (m - 1) := by
  rcases eq_or_ne a 0 with rfl | h0
  · exact zero_le
  · rw [← exp_log h0, exp_lt_exp] at h
    rw [← exp_log h0, exp_le_exp]
    omega

/-- `a < 1` implies `a ≤ exp (−1)` in `ℤᵐ⁰`. -/
lemma le_exp_neg_one_of_lt_one {a : ℤᵐ⁰} (h : a < 1) : a ≤ exp (-1) := by
  have := le_exp_sub_one_of_lt_exp (m := 0) (by rwa [exp_zero])
  rwa [zero_sub] at this

end WithZero

/-! ## Descent in the normal form -/

section Descent

variable {K : Type*} [Field K] (v : Valuation K ℤᵐ⁰)

/-- The normal form with integral `A`, `B` is an integral model. -/
lemma isIntegralModel_normalForm {A B : K} (hA : v A ≤ 1) (hB : v B ≤ 1) :
    IsIntegralModel v (normalForm A B) :=
  ⟨hA, by simp, hB, by simp, by simp⟩

/-- **The normal form with a unit `B`** is good or multiplicative (`v(3) = 1`): if `Δ` is not a
unit then `A³ ≡ 27B` is a unit and `c₄ = A(A³ − 24B) ≡ 3AB` is a unit. -/
lemma isStableModel_normalForm_of_unit (h3 : v 3 = 1) {A B : K} (hA : v A ≤ 1) (hB : v B = 1) :
    IsStableModel v (normalForm A B) := by
  have hint := isIntegralModel_normalForm v hA hB.le
  by_cases hΔ : v (normalForm A B).Δ = 1
  · exact Or.inl ⟨hint, hΔ⟩
  · right
    have hΔ' : v (normalForm A B).Δ < 1 := lt_of_le_of_ne hint.Δ hΔ
    refine ⟨hint, hΔ', ?_⟩
    rw [normalForm_Δ, map_mul, map_pow, hB, one_pow, one_mul] at hΔ'
    have h27 : v (27 * B) = 1 := by
      have : (27 : K) = 3 ^ 3 := by norm_num
      rw [map_mul, this, map_pow, h3, one_pow, one_mul, hB]
    have hA3 : v (A ^ 3) = 1 := by
      have e : A ^ 3 = (A ^ 3 - 27 * B) + 27 * B := by ring
      rw [e, Valuation.map_add_eq_of_lt_right v (by rw [h27]; exact hΔ'), h27]
    have hA1 : v A = 1 := by
      rw [map_pow] at hA3
      exact (pow_eq_one_iff_of_nonneg zero_le (by norm_num)).mp hA3
    have h3B : v (3 * B) = 1 := by rw [map_mul, h3, hB, one_mul]
    rw [normalForm_c₄, map_mul, hA1, one_mul]
    have e : A ^ 3 - 24 * B = (A ^ 3 - 27 * B) + 3 * B := by ring
    rw [e, Valuation.map_add_eq_of_lt_right v (by rw [h3B]; exact hΔ'), h3B]

/-- **The normal form with a unit `A` and a non-unit `B`** is multiplicative. -/
lemma isMultModel_normalForm_of_unit_left {A B : K} (hA : v A = 1) (hB : v B < 1) :
    IsMultModel v (normalForm A B) := by
  have hint := isIntegralModel_normalForm v hA.le hB.le
  have hA3 : v (A ^ 3) = 1 := by rw [map_pow, hA, one_pow]
  refine ⟨hint, ?_, ?_⟩
  · rw [normalForm_Δ, map_mul, map_pow]
    have h27 : v (27 * B) < 1 := by
      rw [map_mul]
      exact (mul_le_of_le_one_left zero_le (valuation_ofNat_le_one v 27)).trans_lt hB
    rw [Valuation.map_sub_eq_of_lt_left v (by rw [hA3]; exact h27), hA3, mul_one]
    exact pow_lt_one₀ zero_le hB (by norm_num)
  · rw [normalForm_c₄, map_mul, hA, one_mul]
    have h24 : v (24 * B) < 1 := by
      rw [map_mul]
      exact (mul_le_of_le_one_left zero_le (valuation_ofNat_le_one v 24)).trans_lt hB
    rw [Valuation.map_sub_eq_of_lt_left v (by rw [hA3]; exact h24), hA3]

/-- **The dominant-term argument**: if `A` is not a unit, `v(B) = exp(−n)` with `n ∈ {1, 2}`,
then `g(x) = 3x³ + A²x² + 3ABx + 3B²` has no nonzero integral root (`v(3) = 1`). -/
lemma normalForm_no_root (h3 : v 3 = 1) {A B x : K} {n : ℕ} (hn : n = 1 ∨ n = 2)
    (hA : v A ≤ exp (-1)) (hB : v B = exp (-(n : ℤ))) (hx0 : x ≠ 0) (hx1 : v x ≤ 1)
    (hg : 3 * x ^ 3 + A ^ 2 * x ^ 2 + 3 * A * B * x + 3 * B ^ 2 = 0) : False := by
  have hvx : v x ≠ 0 := (Valuation.ne_zero_iff v).2 hx0
  set m : ℤ := log (v x) with hm
  have hxm : v x = exp m := (exp_log hvx).symm
  have hm0 : m ≤ 0 := by
    rw [← exp_le_exp, ← hxm, exp_zero]
    exact hx1
  -- the valuations of the four terms
  have hT3 : v (3 * x ^ 3) = exp (3 * m) := by
    rw [map_mul, h3, one_mul, map_pow, hxm, ← exp_nsmul, nsmul_eq_mul, Nat.cast_ofNat]
  have hT2 : v (A ^ 2 * x ^ 2) ≤ exp (2 * m - 2) := by
    rw [map_mul, map_pow, map_pow, hxm]
    refine (mul_le_mul_left (pow_le_pow_left₀ zero_le hA 2) _).trans (le_of_eq ?_)
    rw [← exp_nsmul, ← exp_nsmul, ← exp_add, nsmul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat]
    congr 1
    ring
  have hT1 : v (3 * A * B * x) ≤ exp (m - 1 - n) := by
    rw [map_mul, map_mul, map_mul, h3, one_mul, hB, hxm]
    refine (mul_le_mul_left (mul_le_mul_left hA _) _).trans (le_of_eq ?_)
    rw [← exp_add, ← exp_add]
    congr 1
    ring
  have hT0 : v (3 * B ^ 2) = exp (-2 * (n : ℤ)) := by
    rw [map_mul, h3, one_mul, map_pow, hB, ← exp_nsmul, nsmul_eq_mul, Nat.cast_ofNat]
    congr 1
    ring
  by_cases hcase : -2 * (n : ℤ) < 3 * m
  · -- the term `3x³` dominates
    have hlt : v (A ^ 2 * x ^ 2 + 3 * A * B * x + 3 * B ^ 2) < v (3 * x ^ 3) := by
      rw [hT3]
      refine v.map_add_lt (v.map_add_lt ?_ ?_) ?_
      · exact hT2.trans_lt (exp_lt_exp.2 (by omega))
      · exact hT1.trans_lt (exp_lt_exp.2 (by omega))
      · exact hT0.trans_lt (exp_lt_exp.2 (by omega))
    have hS := Valuation.map_add_eq_of_lt_left v hlt
    have e : 3 * x ^ 3 + (A ^ 2 * x ^ 2 + 3 * A * B * x + 3 * B ^ 2) = 0 := by
      linear_combination hg
    rw [e, map_zero, hT3] at hS
    exact exp_ne_zero hS.symm
  · -- the term `3B²` dominates
    have hlt : v (3 * x ^ 3 + A ^ 2 * x ^ 2 + 3 * A * B * x) < v (3 * B ^ 2) := by
      rw [hT0]
      refine v.map_add_lt (v.map_add_lt ?_ ?_) ?_
      · exact hT3.le.trans_lt (exp_lt_exp.2 (by omega))
      · exact hT2.trans_lt (exp_lt_exp.2 (by omega))
      · exact hT1.trans_lt (exp_lt_exp.2 (by omega))
    have hS := Valuation.map_add_eq_of_lt_right v hlt
    rw [hg, map_zero, hT0] at hS
    exact exp_ne_zero hS.symm

/-- **Descent in the normal form**: for `v(3) = 1`, a uniformizer `π`, integral `A`, `B` with
`v(B) = exp(−n)` and a nonzero root `x` of `g = 3x³ + A²x² + 3ABx + 3B²` (the `x`-coordinate
of a second flex), some change of variables of `y² + Axy + By = x³` is a good or
multiplicative model. By strong induction on `n`: the cases of a unit `B` or a unit `A` are
settled directly, `n ∈ {1, 2}` with a non-unit `A` is impossible, and otherwise
`(A, B, x) ↦ (A/π, B/π³, x/π²)` lowers `n` by `3`. -/
theorem exists_isStableModel_normalForm (h3 : v 3 = 1) {π : K} (hπ : v π = exp (-1)) (n : ℕ) :
    ∀ A B x : K, v A ≤ 1 → v B = exp (-(n : ℤ)) → x ≠ 0 →
      3 * x ^ 3 + A ^ 2 * x ^ 2 + 3 * A * B * x + 3 * B ^ 2 = 0 →
      ∃ C : VariableChange K, IsStableModel v (C • normalForm A B) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro A B x hA hB hx0 hg
  have hB1 : v B ≤ 1 := by
    rw [hB, ← exp_zero, exp_le_exp]
    omega
  -- `x` is integral: it is a root of `ψ₃ = x · g(x)`
  have hx1 : v x ≤ 1 := by
    have hint := isIntegralModel_normalForm v hA hB1
    refine valuation_le_one_of_quartic v h3 (c₃ := A ^ 2) (c₂ := 3 * A * B) (c₁ := 3 * B ^ 2)
      (c₀ := 0) (by linear_combination x * hg) ?_ ?_ ?_ (by simp)
    · rw [map_pow]; exact pow_le_one₀ zero_le hA
    · rw [map_mul, map_mul, h3, one_mul]; exact mul_le_one' hA hB1
    · rw [map_mul, map_pow, h3, one_mul]; exact pow_le_one₀ zero_le hB1
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · -- `B` is a unit
    subst hn0
    refine ⟨1, ?_⟩
    rw [one_smul]
    exact isStableModel_normalForm_of_unit v h3 hA (by rw [hB]; simp)
  by_cases hA1 : v A = 1
  · -- `A` is a unit
    refine ⟨1, ?_⟩
    rw [one_smul]
    refine Or.inr (isMultModel_normalForm_of_unit_left v hA1 ?_)
    rw [hB, ← exp_zero, exp_lt_exp]
    omega
  have hA' : v A ≤ exp (-1) := le_exp_neg_one_of_lt_one (lt_of_le_of_ne hA hA1)
  rcases lt_or_ge n 3 with hn3 | hn3
  · -- `n ∈ {1, 2}`: impossible
    exact absurd hg (normalForm_no_root v h3 (by omega) hA' hB hx0 hx1 |> fun h => fun hg => h hg)
  · -- `n ≥ 3`: rescale
    have hπ0 : π ≠ 0 := by
      rintro rfl
      rw [map_zero] at hπ
      exact exp_ne_zero hπ.symm
    have hπinv : v π⁻¹ = exp 1 := by
      rw [map_inv₀, hπ, exp_neg, inv_inv]
    obtain ⟨C, hC⟩ := ih (n - 3) (by omega) (π⁻¹ * A) (π⁻¹ ^ 3 * B) (π⁻¹ ^ 2 * x)
      (by
        rw [map_mul, hπinv]
        refine (mul_le_mul_right hA' _).trans (le_of_eq ?_)
        rw [← exp_add]
        norm_num)
      (by
        rw [map_mul, map_pow, hπinv, hB, ← exp_nsmul, ← exp_add]
        congr 1
        push_cast [Nat.cast_sub hn3]
        ring)
      (mul_ne_zero (pow_ne_zero _ (inv_ne_zero hπ0)) hx0)
      (by linear_combination π⁻¹ ^ 6 * hg)
    refine ⟨C * ⟨Units.mk0 π hπ0, 0, 0, 0⟩, ?_⟩
    rw [mul_smul, normalForm_scale]
    exact hC

end Descent

/-! ## Stable models from two independent flexes -/

section Curve

variable {K : Type*} [Field K] (v : Valuation K ℤᵐ⁰)

/-- Every model has an integral change of variables (Mathlib's `exists_isIntegral` over the
valuation subring). -/
lemma exists_variableChange_isIntegralModel (E : WeierstrassCurve K) :
    ∃ C : VariableChange K, IsIntegralModel v (C • E) := by
  obtain ⟨C, hC⟩ := exists_isIntegral v.valuationSubring E
  refine ⟨C, ?_⟩
  obtain ⟨W₀, hW₀⟩ := hC.integral
  have key : ∀ r : v.valuationSubring, v (algebraMap v.valuationSubring K r) ≤ 1 := fun r => r.2
  rw [hW₀]
  exact ⟨key _, key _, key _, key _, key _⟩

/-- **A stable model from two flexes with distinct `x`-coordinates** on an integral model, for
`v(3) = 1` and a uniformizer `π`. -/
theorem exists_isStableModel_of_flex (h3 : v 3 = 1) {π : K} (hπ : v π = exp (-1))
    {W : WeierstrassCurve K} (hW : IsIntegralModel v W) (d₁ d₂ : FlexData W)
    (hx : d₁.x ≠ d₂.x) : ∃ C : VariableChange K, IsStableModel v (C • W) := by
  have hx₁ := d₁.valuation_x_le_one v hW h3
  have hy₁ := d₁.valuation_y_le_one v hW hx₁
  have hl₁ := d₁.valuation_lam_le_one v hW hx₁
  obtain ⟨h₁, h₂, h₃, h₄, h₆⟩ := hW
  set C₁ : VariableChange K := ⟨1, d₁.x, d₁.lam, d₁.y⟩ with hC₁
  set A : K := W.a₁ + 2 * d₁.lam with hA
  set B : K := W.a₃ + d₁.x * W.a₁ + 2 * d₁.y with hB
  have hN : C₁ • W = normalForm A B := d₁.variableChange_eq
  have hAv : v A ≤ 1 := by
    rw [hA, ← Valuation.mem_integer_iff] at *
    exact add_mem h₁ (mul_mem (ofNat_mem _ 2) hl₁)
  have hBv : v B ≤ 1 := by
    rw [hB, ← Valuation.mem_integer_iff] at *
    exact add_mem (add_mem h₃ (mul_mem hx₁ h₁)) (mul_mem (ofNat_mem _ 2) hy₁)
  have hB0 : B ≠ 0 := by
    intro h
    apply d₁.ne
    rw [← h, hB]
    ring
  obtain ⟨n, hn⟩ := exists_nat_eq_exp_neg ((Valuation.ne_zero_iff v).2 hB0) hBv
  -- the second flex in the normal form
  set d := d₂.variableChange C₁ with hd
  have hdx : d.x = d₂.x - d₁.x := by
    rw [hd, FlexData.variableChange_x, hC₁]
    simp
  have hdx0 : d.x ≠ 0 := by
    rw [hdx]
    exact sub_ne_zero.mpr (Ne.symm hx)
  have hψ := d.psi3
  have hb₂ : (C₁ • W).b₂ = A ^ 2 := by rw [hN, normalForm_b₂]
  have hb₄ : (C₁ • W).b₄ = A * B := by rw [hN, normalForm_b₄]
  have hb₆ : (C₁ • W).b₆ = B ^ 2 := by rw [hN, normalForm_b₆]
  have hb₈ : (C₁ • W).b₈ = 0 := by rw [hN, normalForm_b₈]
  rw [hb₂, hb₄, hb₆, hb₈] at hψ
  have hg : 3 * d.x ^ 3 + A ^ 2 * d.x ^ 2 + 3 * A * B * d.x + 3 * B ^ 2 = 0 := by
    have : d.x * (3 * d.x ^ 3 + A ^ 2 * d.x ^ 2 + 3 * A * B * d.x + 3 * B ^ 2) = 0 := by
      linear_combination hψ
    exact (mul_eq_zero.mp this).resolve_left hdx0
  obtain ⟨C, hC⟩ := exists_isStableModel_normalForm v h3 hπ n A B d.x hAv hn hdx0 hg
  refine ⟨C * C₁, ?_⟩
  rw [mul_smul, hN]
  exact hC

/-- **A stable model from two flexes with distinct `x`-coordinates** on an arbitrary model. -/
theorem exists_isStableModel_of_flex' (h3 : v 3 = 1) {π : K} (hπ : v π = exp (-1))
    (W : WeierstrassCurve K) (d₁ d₂ : FlexData W) (hx : d₁.x ≠ d₂.x) :
    ∃ C : VariableChange K, IsStableModel v (C • W) := by
  obtain ⟨C₀, hC₀⟩ := exists_variableChange_isIntegralModel v W
  have hx' : (d₁.variableChange C₀).x ≠ (d₂.variableChange C₀).x := by
    simp only [FlexData.variableChange_x]
    intro h
    apply hx
    have hu : (C₀.u : K)⁻¹ ^ 2 ≠ 0 := pow_ne_zero _ (inv_ne_zero C₀.u.ne_zero)
    have := mul_left_cancel₀ hu h
    linear_combination this
  obtain ⟨C, hC⟩ := exists_isStableModel_of_flex v h3 hπ hC₀ (d₁.variableChange C₀)
    (d₂.variableChange C₀) hx'
  exact ⟨C * C₀, by rw [mul_smul]; exact hC⟩

end Curve

/-! ## Stable reduction from rational `3`-torsion -/

section Place

open NumberField IsDedekindDomain.HeightOneSpectrum

variable {F : Type*} [Field F] [NumberField F] [DecidableEq F]

/-- **Raynaud's criterion for `n = 3`, away from `3`**: an elliptic curve `E/F` with two
rational points `P`, `Q` of order `3`, `Q ∉ ⟨P⟩`, has stable reduction at every finite place
of residue characteristic `≠ 3`. -/
theorem hasStableReductionAt_of_three_torsion (E : WeierstrassCurve F) (w : FinitePlace F)
    (hw : residueChar w ≠ 3) (P Q : E.toAffine.Point) (hP : 3 • P = 0) (hQ : 3 • Q = 0)
    (hP0 : P ≠ 0) (hQ0 : Q ≠ 0) (hQP : Q ≠ P) (hQP' : Q ≠ -P) : HasStableReductionAt E w := by
  have h3 := valuation_three_eq_one w hw
  obtain ⟨π, hπ⟩ := w.maximalIdeal.valuation_exists_uniformizer F
  cases P with
  | zero => exact absurd rfl hP0
  | some x₁ y₁ h₁ =>
  cases Q with
  | zero => exact absurd rfl hQ0
  | some x₂ y₂ h₂ =>
  have hx : x₁ ≠ x₂ := by
    intro hx
    rcases Affine.Point.X_eq_iff.mp hx with h | h
    · exact hQP h.symm
    · exact hQP' (by rw [h, neg_neg])
  obtain ⟨C, hC⟩ := exists_isStableModel_of_flex' (w.maximalIdeal.valuation F) h3 hπ E
    (FlexData.ofPoint h₁ hP) (FlexData.ofPoint h₂ hQ) (by simpa using hx)
  exact hasStableReductionAt_of_isStableModel E w C hC

end Place

end Iut

namespace Iut.Tripod

open NumberField WeierstrassCurve

variable (x : Pt) (h3 : TorsionFinite x.1 3) (h5 : TorsionFinite x.1 5)

open scoped Classical in
/-- **Stable reduction of `E_λ/F_λ` at the places of residue characteristic `≠ 3`**, from
`E_λ[3](ℚ̄) ≅ (ℤ/3)²`: the `3`-torsion of `E_λ` is rational over `F_λ`, so `E_λ(F_λ)` contains
two independent points of order `3`. -/
theorem stable_reduction_of_residueChar_ne_three
    (hb : Nonempty (AddSubgroup.torsionBy (legendre x.1).toAffine.Point 3 ≃+ (Fin 2 → ZMod 3)))
    (w : FinitePlace (curveOf x h3 h5).F) (hw : residueChar w ≠ 3) :
    HasStableReductionAt (curveOf x h3 h5).E w := by
  set e := hb.some
  -- two independent `3`-torsion points over `ℚ̄`
  set P₀ : AddSubgroup.torsionBy (legendre x.1).toAffine.Point 3 := e.symm ![1, 0] with hP₀
  set Q₀ : AddSubgroup.torsionBy (legendre x.1).toAffine.Point 3 := e.symm ![0, 1] with hQ₀
  have htors : ∀ R : AddSubgroup.torsionBy (legendre x.1).toAffine.Point 3,
      3 • (R : (legendre x.1).toAffine.Point) = 0 := by
    intro R
    rw [← natCast_zsmul]
    exact (Submodule.mem_torsionBy_iff _ _).mp R.2
  -- descent to `F_λ`
  obtain ⟨P, hP⟩ := three_torsion_mem_range x h3 h5 (P₀ : (legendre x.1).toAffine.Point) (htors P₀)
  obtain ⟨Q, hQ⟩ := three_torsion_mem_range x h3 h5 (Q₀ : (legendre x.1).toAffine.Point) (htors Q₀)
  have hinj := Affine.Point.map_injective (W' := (curveOf x h3 h5).E)
    (Algebra.ofId (curveOf x h3 h5).F (curveOf x h3 h5).Fbar)
  have hP3 : 3 • P = 0 := by
    apply hinj
    rw [map_nsmul, map_zero, hP]
    exact htors P₀
  have hQ3 : 3 • Q = 0 := by
    apply hinj
    rw [map_nsmul, map_zero, hQ]
    exact htors Q₀
  have hP0 : P ≠ 0 := by
    intro h
    rw [h, map_zero] at hP
    have : P₀ = 0 := Subtype.ext hP.symm
    rw [hP₀, AddEquiv.map_eq_zero_iff] at this
    exact absurd (congrFun this 0) (by decide)
  have hQ0 : Q ≠ 0 := by
    intro h
    rw [h, map_zero] at hQ
    have : Q₀ = 0 := Subtype.ext hQ.symm
    rw [hQ₀, AddEquiv.map_eq_zero_iff] at this
    exact absurd (congrFun this 1) (by decide)
  have hQP : Q ≠ P := by
    intro h
    rw [h, hP] at hQ
    have : P₀ = Q₀ := Subtype.ext hQ
    rw [hQ₀, hP₀, e.symm.injective.eq_iff] at this
    exact absurd (congrFun this 0) (by decide)
  have hQP' : Q ≠ -P := by
    intro h
    rw [h, map_neg, hP] at hQ
    have : -P₀ = Q₀ := Subtype.ext hQ
    rw [hQ₀, hP₀, ← map_neg, e.symm.injective.eq_iff] at this
    exact absurd (congrFun this 1) (by decide)
  exact hasStableReductionAt_of_three_torsion (curveOf x h3 h5).E w hw P Q hP3 hQ3 hP0 hQ0 hQP hQP'

open scoped Classical in
/-- **Stable reduction of `E_λ/F_λ` at every finite place** (Raynaud's criterion for the rational
`3`-torsion at the places over `2`, the Legendre model and its twist `E_{1/λ}` elsewhere). -/
theorem stable_reduction
    (hb : Nonempty (AddSubgroup.torsionBy (legendre x.1).toAffine.Point 3 ≃+ (Fin 2 → ZMod 3)))
    (w : FinitePlace (curveOf x h3 h5).F) : HasStableReductionAt (curveOf x h3 h5).E w := by
  by_cases hw : residueChar w = 2
  · exact stable_reduction_of_residueChar_ne_three x h3 h5 hb w (by rw [hw]; norm_num)
  · exact stable_reduction_of_residueChar_ne_two x h3 h5 w hw

end Iut.Tripod
