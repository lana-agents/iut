/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# The Legendre curve

The Legendre curve `E_λ : y² = x(x − 1)(x − λ) = x³ − (1 + λ)x² + λx` attached to a point
`λ ∉ {0, 1}` of the tripod `ℙ¹ ∖ {0, 1, ∞}` (`Iut.Tripod.legendre`), its invariants
`Δ = 16 λ²(λ − 1)²`, `c₄ = 16(λ² − λ + 1)`, `j = 256 (λ² − λ + 1)³ / (λ²(λ − 1)²)`, its
compatibility with ring homomorphisms, and its `2`-torsion points `(0, 0)`, `(1, 0)`,
`(λ, 0)`: in a field of characteristic `≠ 2`, the affine `2`-torsion points of `E_λ` are
exactly the points with `y = 0`, whose `x`-coordinate is then a root of `x(x − 1)(x − λ)`.
-/

namespace Iut.Tripod

open WeierstrassCurve

/-- **The Legendre curve** `y² = x³ − (1 + λ)x² + λx = x(x − 1)(x − λ)`. -/
def legendre {R : Type*} [CommRing R] (l : R) : WeierstrassCurve R := ⟨0, -(1 + l), 0, l, 0⟩

section Invariants

variable {R : Type*} [CommRing R] (l : R)

@[simp] lemma legendre_a₁ : (legendre l).a₁ = 0 := rfl
@[simp] lemma legendre_a₂ : (legendre l).a₂ = -(1 + l) := rfl
@[simp] lemma legendre_a₃ : (legendre l).a₃ = 0 := rfl
@[simp] lemma legendre_a₄ : (legendre l).a₄ = l := rfl
@[simp] lemma legendre_a₆ : (legendre l).a₆ = 0 := rfl

lemma legendre_b₂ : (legendre l).b₂ = -4 * (1 + l) := by
  simp only [b₂, legendre_a₁, legendre_a₂]; ring

lemma legendre_b₄ : (legendre l).b₄ = 2 * l := by
  simp only [b₄, legendre_a₁, legendre_a₃, legendre_a₄]; ring

lemma legendre_b₆ : (legendre l).b₆ = 0 := by
  simp only [b₆, legendre_a₃, legendre_a₆]; ring

lemma legendre_b₈ : (legendre l).b₈ = -l ^ 2 := by
  simp only [b₈, legendre_a₁, legendre_a₂, legendre_a₃, legendre_a₄, legendre_a₆]; ring

/-- `c₄(E_λ) = 16 (λ² − λ + 1)`. -/
lemma legendre_c₄ : (legendre l).c₄ = 16 * (l ^ 2 - l + 1) := by
  simp only [c₄, legendre_b₂, legendre_b₄]; ring

/-- `Δ(E_λ) = 16 λ² (λ − 1)²`. -/
lemma legendre_Δ : (legendre l).Δ = 16 * l ^ 2 * (l - 1) ^ 2 := by
  simp only [Δ, legendre_b₂, legendre_b₄, legendre_b₆, legendre_b₈]; ring

/-- The Legendre curve is compatible with ring homomorphisms. -/
lemma legendre_map {A : Type*} [CommRing A] (f : R →+* A) :
    (legendre l).map f = legendre (f l) := by
  ext <;> simp [legendre]

/-- The Legendre curve is compatible with base change. -/
lemma legendre_baseChange {A : Type*} [CommRing A] [Algebra R A] :
    (legendre l).baseChange A = legendre (algebraMap R A l) :=
  legendre_map l _

end Invariants

section Field

variable {K : Type*} [Field K]

/-- `E_λ` is an elliptic curve for `λ ∉ {0, 1}` in a field of characteristic `≠ 2`. -/
theorem legendre_isElliptic [NeZero (2 : K)] {l : K} (h0 : l ≠ 0) (h1 : l ≠ 1) :
    (legendre l).IsElliptic := by
  refine ⟨?_⟩
  rw [legendre_Δ, isUnit_iff_ne_zero]
  have h16 : (16 : K) ≠ 0 := by
    have : (16 : K) = 2 ^ 4 := by norm_num
    rw [this]
    exact pow_ne_zero _ (NeZero.ne 2)
  exact mul_ne_zero (mul_ne_zero h16 (pow_ne_zero _ h0)) (pow_ne_zero _ (sub_ne_zero.mpr h1))

/-- `λ ≠ 0` for the Legendre curve to be elliptic. -/
theorem ne_zero_of_legendre_isElliptic {l : K} [(legendre l).IsElliptic] : l ≠ 0 := by
  intro h
  have hΔ := (legendre l).isUnit_Δ.ne_zero
  rw [legendre_Δ, h] at hΔ
  simp at hΔ

/-- `λ ≠ 1` for the Legendre curve to be elliptic. -/
theorem ne_one_of_legendre_isElliptic {l : K} [(legendre l).IsElliptic] : l ≠ 1 := by
  intro h
  have hΔ := (legendre l).isUnit_Δ.ne_zero
  rw [legendre_Δ, h] at hΔ
  simp at hΔ

/-- `j(E_λ) = 256 (λ² − λ + 1)³ / (λ² (λ − 1)²)`. -/
theorem legendre_j [NeZero (2 : K)] {l : K} [(legendre l).IsElliptic] :
    (legendre l).j = 256 * (l ^ 2 - l + 1) ^ 3 / (l ^ 2 * (l - 1) ^ 2) := by
  have h0 : l ≠ 0 := ne_zero_of_legendre_isElliptic
  have h1 : l - 1 ≠ 0 := sub_ne_zero.mpr ne_one_of_legendre_isElliptic
  have h16 : (16 : K) ≠ 0 := by
    have : (16 : K) = 2 ^ 4 := by norm_num
    rw [this]
    exact pow_ne_zero _ (NeZero.ne 2)
  rw [j, Units.val_inv_eq_inv_val, coe_Δ', legendre_Δ, legendre_c₄]
  field_simp
  ring

/-! ### The `2`-torsion -/

variable (l : K)

/-- `(0, 0)` lies on `E_λ`. -/
theorem legendre_equation_zero : (legendre l).toAffine.Equation 0 0 := by
  rw [Affine.equation_iff]; simp

/-- `(1, 0)` lies on `E_λ`. -/
theorem legendre_equation_one : (legendre l).toAffine.Equation 1 0 := by
  rw [Affine.equation_iff]; simp

/-- `(λ, 0)` lies on `E_λ`. -/
theorem legendre_equation_self : (legendre l).toAffine.Equation l 0 := by
  rw [Affine.equation_iff]; simp; ring

/-- The affine points of `E_λ` with `y = 0` have `x ∈ {0, 1, λ}`. -/
theorem legendre_equation_y_zero {x : K} (h : (legendre l).toAffine.Equation x 0) :
    x = 0 ∨ x = 1 ∨ x = l := by
  rw [Affine.equation_iff] at h
  simp only [legendre_a₁, legendre_a₂, legendre_a₃, legendre_a₄, legendre_a₆] at h
  have : x * (x - 1) * (x - l) = 0 := by linear_combination -h
  rcases mul_eq_zero.mp this with h' | h'
  · rcases mul_eq_zero.mp h' with h'' | h''
    · exact Or.inl h''
    · exact Or.inr (Or.inl (sub_eq_zero.mp h''))
  · exact Or.inr (Or.inr (sub_eq_zero.mp h'))

/-- `(0, 0)` is a nonsingular point of `E_λ`. -/
theorem legendre_nonsingular_zero [(legendre l).IsElliptic] :
    (legendre l).toAffine.Nonsingular 0 0 :=
  Affine.equation_iff_nonsingular.mp (legendre_equation_zero l)

/-- `(1, 0)` is a nonsingular point of `E_λ`. -/
theorem legendre_nonsingular_one [(legendre l).IsElliptic] :
    (legendre l).toAffine.Nonsingular 1 0 :=
  Affine.equation_iff_nonsingular.mp (legendre_equation_one l)

/-- `(λ, 0)` is a nonsingular point of `E_λ`. -/
theorem legendre_nonsingular_self [(legendre l).IsElliptic] :
    (legendre l).toAffine.Nonsingular l 0 :=
  Affine.equation_iff_nonsingular.mp (legendre_equation_self l)

/-- `negY` of the Legendre curve is `y ↦ −y`. -/
lemma legendre_negY (x y : K) : (legendre l).toAffine.negY x y = -y := by
  simp [Affine.negY]

open scoped Classical in
/-- In characteristic `≠ 2`, an affine point of `E_λ` is `2`-torsion iff `y = 0`. -/
theorem two_nsmul_some_eq_zero_iff [NeZero (2 : K)] {x y : K}
    (h : (legendre l).toAffine.Nonsingular x y) :
    2 • Affine.Point.some x y h = 0 ↔ y = 0 := by
  rw [two_nsmul, ← eq_neg_iff_add_eq_zero, Affine.Point.neg_some, Affine.Point.some.injEq,
    legendre_negY]
  constructor
  · rintro ⟨-, hy⟩
    have : (2 : K) * y = 0 := by linear_combination hy
    exact (mul_eq_zero.mp this).resolve_left (NeZero.ne 2)
  · rintro rfl
    simp

open scoped Classical in
/-- The `2`-torsion points of `E_λ` in characteristic `≠ 2`: the affine ones have `y = 0`
and `x ∈ {0, 1, λ}`. -/
theorem legendre_two_torsion [NeZero (2 : K)] {P : (legendre l).toAffine.Point} (hP : 2 • P = 0) :
    P = 0 ∨ ∃ (x : K) (h : (legendre l).toAffine.Nonsingular x 0),
      P = Affine.Point.some x 0 h ∧ (x = 0 ∨ x = 1 ∨ x = l) := by
  cases P with
  | zero => exact Or.inl rfl
  | some x y h =>
    right
    have hy : y = 0 := (two_nsmul_some_eq_zero_iff l h).mp hP
    subst hy
    exact ⟨x, h, rfl, legendre_equation_y_zero l ((Affine.nonsingular_iff _ _).mp h).1⟩

open scoped Classical in
/-- The three points `(0, 0)`, `(1, 0)`, `(λ, 0)` are `2`-torsion. -/
theorem two_nsmul_some_zero [NeZero (2 : K)] {x : K} (h : (legendre l).toAffine.Nonsingular x 0) :
    2 • Affine.Point.some x 0 h = 0 :=
  (two_nsmul_some_eq_zero_iff l h).mpr rfl

end Field

end Iut.Tripod
