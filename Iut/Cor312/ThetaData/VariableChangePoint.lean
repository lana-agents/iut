/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Cor312.ThetaData.PointMap

/-!
# Points of Weierstrass curves along changes of variables

A change of variables `C = (u, r, s, t)` (Mathlib's `WeierstrassCurve.VariableChange`, with the
convention `X = u²X' + r`, `Y = u³Y' + u²sX' + t`) identifies the points of `W` with those of
`C • W`: the point `(x, y)` of `W` corresponds to the point
`(X', Y') = ((x - r)/u², (y - t - s(x - r))/u³)` of `C • W`. This identification respects the
group law (the addition formulas are equivariant under the affine substitution, the slope of a
line transforming as `ℓ ↦ (ℓ - s)/u`). We record it as the additive isomorphism
`Iut.Anabelian.vcEquiv C W : W(k) ≃+ (C • W)(k)`.
-/

namespace Iut.Anabelian

open WeierstrassCurve
open scoped Classical

noncomputable section

section Coordinates

variable {k : Type*} [Field k] (C : VariableChange k) (W : WeierstrassCurve k)

/-- The `X`-coordinate in the model `C • W` of a point with `x`-coordinate `x`. -/
def vcX (x : k) : k := (x - C.r) / (C.u : k) ^ 2

/-- The `Y`-coordinate in the model `C • W` of the point `(x, y)`. -/
def vcY (x y : k) : k := (y - C.t - C.s * (x - C.r)) / (C.u : k) ^ 3

lemma u_ne_zero : (C.u : k) ≠ 0 := C.u.ne_zero

lemma vcX_injective : Function.Injective (vcX C) := by
  intro a b h
  unfold vcX at h
  rw [div_left_inj' (pow_ne_zero _ (u_ne_zero C))] at h
  linear_combination h

lemma vcY_inj (x y y' : k) : vcY C x y = vcY C x y' ↔ y = y' := by
  unfold vcY
  rw [div_left_inj' (pow_ne_zero _ (u_ne_zero C))]
  constructor
  · intro h
    linear_combination h
  · intro h
    rw [h]

/-- `x = u²X' + r` recovers `x` from `X'`. -/
lemma vcX_of (x' : k) : vcX C ((C.u : k) ^ 2 * x' + C.r) = x' := by
  unfold vcX
  field_simp
  ring

/-- `y = u³Y' + u²sX' + t` recovers `y` from `(X', Y')`. -/
lemma vcY_of (x' y' : k) :
    vcY C ((C.u : k) ^ 2 * x' + C.r) ((C.u : k) ^ 3 * y' + (C.u : k) ^ 2 * C.s * x' + C.t) = y' := by
  unfold vcY
  field_simp
  ring

/-- The coefficients of `C • W`, in terms of the inverse of the unit `u`. -/
lemma variableChange_coeffs :
    (C • W).a₁ = (C.u : k)⁻¹ * (W.a₁ + 2 * C.s) ∧
    (C • W).a₂ = (C.u : k)⁻¹ ^ 2 * (W.a₂ - C.s * W.a₁ + 3 * C.r - C.s ^ 2) ∧
    (C • W).a₃ = (C.u : k)⁻¹ ^ 3 * (W.a₃ + C.r * W.a₁ + 2 * C.t) ∧
    (C • W).a₄ = (C.u : k)⁻¹ ^ 4 * (W.a₄ - C.s * W.a₃ + 2 * C.r * W.a₂ - (C.t + C.r * C.s) * W.a₁
      + 3 * C.r ^ 2 - 2 * C.s * C.t) ∧
    (C • W).a₆ = (C.u : k)⁻¹ ^ 6 * (W.a₆ + C.r * W.a₄ + C.r ^ 2 * W.a₂ + C.r ^ 3 - C.t * W.a₃
      - C.t ^ 2 - C.r * C.t * W.a₁) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄,
      variableChange_a₆, Units.val_inv_eq_inv_val]

/-- The Weierstrass polynomial of `C • W` at the transformed point. -/
lemma evalEval_polynomial_vc (x y : k) :
    (C • W).toAffine.polynomial.evalEval (vcX C x) (vcY C x y) =
      (C.u : k)⁻¹ ^ 6 * W.toAffine.polynomial.evalEval x y := by
  obtain ⟨h₁, h₂, h₃, h₄, h₆⟩ := variableChange_coeffs C W
  rw [Affine.evalEval_polynomial, Affine.evalEval_polynomial, h₁, h₂, h₃, h₄, h₆]
  unfold vcX vcY
  have hu := u_ne_zero C
  field_simp
  ring

/-- The equation of `W` at `(x, y)` is the equation of `C • W` at the transformed point. -/
lemma equation_vc (x y : k) :
    W.toAffine.Equation x y ↔ (C • W).toAffine.Equation (vcX C x) (vcY C x y) := by
  rw [Affine.Equation, Affine.Equation, evalEval_polynomial_vc, mul_eq_zero, or_iff_right]
  exact pow_ne_zero _ (inv_ne_zero (u_ne_zero C))

/-- The partial derivative in `X` transforms as `∂_X' = u⁻⁴(∂_x + s ∂_y)`. -/
lemma polynomialX_vc (x y : k) :
    (C • W).toAffine.polynomialX.evalEval (vcX C x) (vcY C x y) =
      (C.u : k)⁻¹ ^ 4 * (W.toAffine.polynomialX.evalEval x y
        + C.s * W.toAffine.polynomialY.evalEval x y) := by
  obtain ⟨h₁, h₂, h₃, h₄, h₆⟩ := variableChange_coeffs C W
  rw [Affine.evalEval_polynomialX, Affine.evalEval_polynomialX, Affine.evalEval_polynomialY,
    h₁, h₂, h₄]
  unfold vcX vcY
  have hu := u_ne_zero C
  field_simp
  ring

/-- The partial derivative in `Y` transforms as `∂_Y' = u⁻³ ∂_y`. -/
lemma polynomialY_vc (x y : k) :
    (C • W).toAffine.polynomialY.evalEval (vcX C x) (vcY C x y) =
      (C.u : k)⁻¹ ^ 3 * W.toAffine.polynomialY.evalEval x y := by
  obtain ⟨h₁, h₂, h₃, h₄, h₆⟩ := variableChange_coeffs C W
  rw [Affine.evalEval_polynomialY, Affine.evalEval_polynomialY, h₁, h₃]
  unfold vcX vcY
  have hu := u_ne_zero C
  field_simp
  ring

/-- Nonsingularity of `W` at `(x, y)` is nonsingularity of `C • W` at the transformed point. -/
lemma nonsingular_vc (x y : k) :
    W.toAffine.Nonsingular x y ↔ (C • W).toAffine.Nonsingular (vcX C x) (vcY C x y) := by
  rw [Affine.Nonsingular, Affine.Nonsingular, ← equation_vc, polynomialX_vc, polynomialY_vc]
  have hu4 : (C.u : k)⁻¹ ^ 4 ≠ 0 := pow_ne_zero _ (inv_ne_zero (u_ne_zero C))
  have hu3 : (C.u : k)⁻¹ ^ 3 ≠ 0 := pow_ne_zero _ (inv_ne_zero (u_ne_zero C))
  simp only [ne_eq, mul_eq_zero, hu4, hu3, false_or]
  refine and_congr_right fun _ => ?_
  constructor
  · rintro (h | h)
    · by_contra hc
      rw [not_or, not_not, not_not] at hc
      exact h (by linear_combination hc.1 - C.s * hc.2)
    · exact Or.inr h
  · rintro (h | h)
    · by_contra hc
      rw [not_or, not_not, not_not] at hc
      exact h (by linear_combination hc.1 + C.s * hc.2)
    · exact Or.inr h

/-- Negation commutes with the transformation of coordinates. -/
lemma vcY_negY (x y : k) :
    vcY C x (W.toAffine.negY x y) = (C • W).toAffine.negY (vcX C x) (vcY C x y) := by
  obtain ⟨h₁, h₂, h₃, h₄, h₆⟩ := variableChange_coeffs C W
  unfold Affine.negY
  rw [h₁, h₃]
  unfold vcX vcY
  have hu := u_ne_zero C
  field_simp
  ring

/-- The `X`-coordinate of a sum transforms compatibly, the slope transforming as
`ℓ ↦ (ℓ - s)/u`. -/
lemma vcX_addX (x₁ x₂ ℓ : k) :
    vcX C (W.toAffine.addX x₁ x₂ ℓ) =
      (C • W).toAffine.addX (vcX C x₁) (vcX C x₂) ((ℓ - C.s) / (C.u : k)) := by
  obtain ⟨h₁, h₂, h₃, h₄, h₆⟩ := variableChange_coeffs C W
  unfold Affine.addX
  rw [h₁, h₂]
  unfold vcX
  have hu := u_ne_zero C
  field_simp
  ring

/-- The `Y`-coordinate of a sum transforms compatibly. -/
lemma vcY_addY (x₁ x₂ y₁ ℓ : k) :
    vcY C (W.toAffine.addX x₁ x₂ ℓ) (W.toAffine.addY x₁ x₂ y₁ ℓ) =
      (C • W).toAffine.addY (vcX C x₁) (vcX C x₂) (vcY C x₁ y₁) ((ℓ - C.s) / (C.u : k)) := by
  obtain ⟨h₁, h₂, h₃, h₄, h₆⟩ := variableChange_coeffs C W
  unfold Affine.addY Affine.negAddY Affine.negY Affine.addX
  rw [h₁, h₂, h₃]
  unfold vcX vcY
  have hu := u_ne_zero C
  field_simp
  ring

/-- The slope of the line through two points transforms as `ℓ ↦ (ℓ - s)/u`. -/
lemma slope_vc {x₁ x₂ y₁ y₂ : k} (h₁ : W.toAffine.Equation x₁ y₁) (h₂ : W.toAffine.Equation x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂)) :
    (C • W).toAffine.slope (vcX C x₁) (vcX C x₂) (vcY C x₁ y₁) (vcY C x₂ y₂) =
      (W.toAffine.slope x₁ x₂ y₁ y₂ - C.s) / (C.u : k) := by
  obtain ⟨h₁', h₂', h₃', h₄', h₆'⟩ := variableChange_coeffs C W
  have hu := u_ne_zero C
  by_cases hx : x₁ = x₂
  · subst hx
    have hy : y₁ ≠ W.toAffine.negY x₁ y₂ := fun h => hxy ⟨rfl, h⟩
    have hd : y₁ - W.toAffine.negY x₁ y₁ ≠ 0 := by
      rw [sub_ne_zero]
      rcases Affine.Y_eq_of_X_eq h₁ h₂ rfl with h | h
      · rw [← h] at hy
        exact hy
      · exact absurd h hy
    have hy' : vcY C x₁ y₁ ≠ (C • W).toAffine.negY (vcX C x₁) (vcY C x₁ y₂) := by
      rw [← vcY_negY, Ne, vcY_inj]
      exact hy
    rw [Affine.slope_of_Y_ne rfl hy, Affine.slope_of_Y_ne rfl hy', ← vcY_negY]
    have hN' : 3 * vcX C x₁ ^ 2 + 2 * (C • W).toAffine.a₂ * vcX C x₁ + (C • W).toAffine.a₄
        - (C • W).toAffine.a₁ * vcY C x₁ y₁ =
        (C.u : k)⁻¹ ^ 4 * ((3 * x₁ ^ 2 + 2 * W.toAffine.a₂ * x₁ + W.toAffine.a₄
          - W.toAffine.a₁ * y₁) - C.s * (y₁ - W.toAffine.negY x₁ y₁)) := by
      rw [h₁', h₂', h₄']
      unfold vcX vcY Affine.negY
      field_simp
      ring
    have hD' : vcY C x₁ y₁ - vcY C x₁ (W.toAffine.negY x₁ y₁) =
        (C.u : k)⁻¹ ^ 3 * (y₁ - W.toAffine.negY x₁ y₁) := by
      unfold vcY
      field_simp
      ring
    rw [hN', hD']
    generalize y₁ - W.toAffine.negY x₁ y₁ = D at hd ⊢
    field_simp
  · have hx' : vcX C x₁ ≠ vcX C x₂ := fun h => hx (vcX_injective C h)
    rw [Affine.slope_of_X_ne hx, Affine.slope_of_X_ne hx']
    have hd : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
    have hnum : vcY C x₁ y₁ - vcY C x₂ y₂ =
        (C.u : k)⁻¹ ^ 3 * ((y₁ - y₂) - C.s * (x₁ - x₂)) := by
      unfold vcY
      field_simp
      ring
    have hden : vcX C x₁ - vcX C x₂ = (C.u : k)⁻¹ ^ 2 * (x₁ - x₂) := by
      unfold vcX
      field_simp
      ring
    rw [hnum, hden]
    generalize x₁ - x₂ = D at hd ⊢
    field_simp

end Coordinates

/-! ## The isomorphism on points -/

section Points

variable {k : Type*} [Field k] (C : VariableChange k) (W : WeierstrassCurve k)

/-- The point of `C • W` corresponding to a point of `W`. -/
def vcPoint : W.toAffine.Point → (C • W).toAffine.Point
  | .zero => .zero
  | .some x y h => .some (vcX C x) (vcY C x y) ((nonsingular_vc C W x y).mp h)

/-- Two affine points with the same coordinates are equal. -/
lemma some_ext {W : WeierstrassCurve k} {x y x' y' : k} {h : W.toAffine.Nonsingular x y}
    {h' : W.toAffine.Nonsingular x' y'} (hx : x = x') (hy : y = y') :
    Affine.Point.some x y h = Affine.Point.some x' y' h' := by
  subst hx hy
  rfl

@[simp] lemma vcPoint_zero : vcPoint C W 0 = 0 := rfl

lemma vcPoint_some {x y : k} (h : W.toAffine.Nonsingular x y) :
    vcPoint C W (.some x y h) = .some (vcX C x) (vcY C x y) ((nonsingular_vc C W x y).mp h) := rfl

lemma vcPoint_neg (P : W.toAffine.Point) : vcPoint C W (-P) = -vcPoint C W P := by
  cases P with
  | zero => rfl
  | some x y h =>
    rw [Affine.Point.neg_some, vcPoint_some, vcPoint_some, Affine.Point.neg_some]
    exact some_ext rfl (vcY_negY C W x y)

lemma vcPoint_add (P Q : W.toAffine.Point) :
    vcPoint C W (P + Q) = vcPoint C W P + vcPoint C W Q := by
  cases P with
  | zero =>
    change vcPoint C W (0 + Q) = 0 + vcPoint C W Q
    rw [zero_add, zero_add]
  | some x₁ y₁ h₁ =>
    cases Q with
    | zero =>
      change vcPoint C W (_ + 0) = _ + 0
      rw [add_zero, add_zero]
    | some x₂ y₂ h₂ =>
      by_cases hxy : x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂
      · rw [Affine.Point.add_of_Y_eq hxy.1 hxy.2, vcPoint_some, vcPoint_some,
          Affine.Point.add_of_Y_eq (congrArg (vcX C) hxy.1)]
        · rfl
        · rw [hxy.2, hxy.1, vcY_negY]
      · have hxy' : ¬(vcX C x₁ = vcX C x₂ ∧
            vcY C x₁ y₁ = (C • W).toAffine.negY (vcX C x₂) (vcY C x₂ y₂)) := by
          rintro ⟨hx, hy⟩
          have hx' := vcX_injective C hx
          subst hx'
          rw [← vcY_negY, vcY_inj] at hy
          exact hxy ⟨rfl, hy⟩
        rw [Affine.Point.add_some hxy, vcPoint_some, vcPoint_some, vcPoint_some,
          Affine.Point.add_some hxy']
        exact some_ext (by rw [vcX_addX, slope_vc C W h₁.1 h₂.1 hxy])
          (by rw [vcY_addY, slope_vc C W h₁.1 h₂.1 hxy])

/-- The additive homomorphism `W(k) → (C • W)(k)`. -/
def vcHom : W.toAffine.Point →+ (C • W).toAffine.Point where
  toFun := vcPoint C W
  map_zero' := rfl
  map_add' := vcPoint_add C W

@[simp] lemma vcHom_apply (P : W.toAffine.Point) : vcHom C W P = vcPoint C W P := rfl

lemma vcPoint_injective : Function.Injective (vcPoint C W) := by
  intro P Q h
  cases P with
  | zero =>
    cases Q with
    | zero => rfl
    | some x y hQ =>
      rw [vcPoint_some] at h
      change Affine.Point.zero = _ at h
      cases h
  | some x₁ y₁ h₁ =>
    cases Q with
    | zero =>
      rw [vcPoint_some] at h
      change _ = Affine.Point.zero at h
      cases h
    | some x₂ y₂ h₂ =>
      rw [vcPoint_some, vcPoint_some, Affine.Point.some.injEq] at h
      obtain ⟨hx, hy⟩ := h
      have hx' := vcX_injective C hx
      subst hx'
      rw [vcY_inj] at hy
      subst hy
      rfl

lemma vcPoint_surjective : Function.Surjective (vcPoint C W) := by
  intro P'
  cases P' with
  | zero => exact ⟨0, rfl⟩
  | some x' y' h' =>
    have hx := vcX_of C x'
    have hy := vcY_of C x' y'
    have hns : W.toAffine.Nonsingular ((C.u : k) ^ 2 * x' + C.r)
        ((C.u : k) ^ 3 * y' + (C.u : k) ^ 2 * C.s * x' + C.t) := by
      rw [nonsingular_vc C W, hx, hy]
      exact h'
    exact ⟨.some _ _ hns, some_ext hx hy⟩

/-- **The additive isomorphism `W(k) ≃+ (C • W)(k)`** induced by a change of variables. -/
def vcEquiv : W.toAffine.Point ≃+ (C • W).toAffine.Point :=
  AddEquiv.ofBijective (vcHom C W) ⟨vcPoint_injective C W, vcPoint_surjective C W⟩

@[simp] lemma vcEquiv_apply (P : W.toAffine.Point) : vcEquiv C W P = vcPoint C W P := rfl

lemma vcEquiv_symm_apply (P' : (C • W).toAffine.Point) :
    vcPoint C W ((vcEquiv C W).symm P') = P' :=
  (vcEquiv C W).apply_symm_apply P'

/-! ### Coordinates of points -/

/-- The `x`-coordinate of a point (`0` at infinity). -/
def ptX {W : WeierstrassCurve k} : W.toAffine.Point → k
  | .zero => 0
  | .some x _ _ => x

/-- The `y`-coordinate of a point (`0` at infinity). -/
def ptY {W : WeierstrassCurve k} : W.toAffine.Point → k
  | .zero => 0
  | .some _ y _ => y

/-- Transport of points along an equality of curves. -/
def pointCongr {W W' : WeierstrassCurve k} (h : W = W') :
    W.toAffine.Point ≃+ W'.toAffine.Point := by
  subst h
  exact AddEquiv.refl _

@[simp] lemma ptX_pointCongr {W W' : WeierstrassCurve k} (h : W = W') (P : W.toAffine.Point) :
    ptX (pointCongr h P) = ptX P := by
  subst h
  rfl

@[simp] lemma ptY_pointCongr {W W' : WeierstrassCurve k} (h : W = W') (P : W.toAffine.Point) :
    ptY (pointCongr h P) = ptY P := by
  subst h
  rfl

@[simp] lemma ptX_pointCongr_symm {W W' : WeierstrassCurve k} (h : W = W')
    (P : W'.toAffine.Point) : ptX ((pointCongr h).symm P) = ptX P := by
  subst h
  rfl

@[simp] lemma ptY_pointCongr_symm {W W' : WeierstrassCurve k} (h : W = W')
    (P : W'.toAffine.Point) : ptY ((pointCongr h).symm P) = ptY P := by
  subst h
  rfl

end Points

end

end Iut.Anabelian
