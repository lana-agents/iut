/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# Point maps of Weierstrass curves: ring homomorphisms and changes of variables

Two group homomorphisms on the nonsingular affine points of a Weierstrass curve `W` over a
field `F` that are not in Mathlib in the required generality:

* `Iut.Tripod.mapPoint f : W.Point →+ (W.map f).Point` for a ring homomorphism `f : F →+* K`,
  `(x, y) ↦ (f x, f y)` (Mathlib's `WeierstrassCurve.Affine.Point.map` requires `f` to be
  linear over a ring of definition of `W`; we need the case of a field automorphism moving the
  coefficients of `W`);
* `Iut.Tripod.vcPoint u r : (vc u r • W).Point →+ W.Point` for the change of variables
  `vc u r = ⟨u, r, 0, 0⟩`, `(x, y) ↦ (u²x + r, u³y)`.

Both are proved additive exactly as `WeierstrassCurve.Affine.Point.map`, from the
compatibility of the negation, slope and addition formulae with the coordinate change.
`Iut.Tripod.nsmul_some_eq_zero_of_eq` transports torsion along an equality of curves.
-/

namespace Iut.Tripod

open WeierstrassCurve WeierstrassCurve.Affine

open scoped Classical

/-! ### Transport along an equality of curves -/

/-- Two affine points with the same coordinates on equal curves are equal, up to the
transport of the nonsingularity proof. -/
theorem nsmul_some_eq_zero_of_eq {F : Type*} [Field F] {W W' : Affine F} (h : W = W')
    {x y : F} (hW : W.Nonsingular x y) (hW' : W'.Nonsingular x y) (n : ℕ)
    (hP : n • Point.some x y hW = 0) : n • Point.some x y hW' = 0 := by
  subst h
  exact hP

theorem some_congr {F : Type*} [Field F] {W : Affine F} {x x' y y' : F} (hx : x = x')
    (hy : y = y') {h : W.Nonsingular x y} {h' : W.Nonsingular x' y'} :
    Point.some x y h = Point.some x' y' h' := by
  subst hx
  subst hy
  rfl

/-! ### The map of points along a ring homomorphism -/

section RingHomMap

variable {F K : Type*} [Field F] [Field K] {W : Affine F} (f : F →+* K)

/-- **The map of points along a ring homomorphism** `f : F →+* K`: `(x, y) ↦ (f x, f y)`, from
the points of `W` to those of `W.map f`. -/
noncomputable def mapPoint : W.Point →+ (W.map f).Point where
  toFun P := match P with
    | 0 => 0
    | Point.some _ _ h => Point.some _ _ ((W.map_nonsingular f.injective ..).mpr h)
  map_zero' := rfl
  map_add' := by
    rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩)
    any_goals rfl
    by_cases hxy : x₁ = x₂ ∧ y₁ = W.negY x₂ y₂
    · rw [Point.add_of_Y_eq hxy.left hxy.right,
        Point.add_of_Y_eq (congr_arg _ hxy.left) <| by rw [hxy.right, map_negY]]
    · have hxy' : ¬(f x₁ = f x₂ ∧ f y₁ = (W.map f).negY (f x₂) (f y₂)) := fun h ↦
        hxy ⟨f.injective h.1, f.injective (W.map_negY f .. ▸ h).2⟩
      rw [Point.add_some hxy]
      change _ = Point.some _ _ _ + Point.some _ _ _
      rw [Point.add_some hxy']
      exact some_congr (by rw [map_slope, map_addX]) (by rw [map_slope, map_addY])

theorem mapPoint_some {x y : F} (h : W.Nonsingular x y) :
    mapPoint f (Point.some x y h) =
      Point.some (f x) (f y) ((W.map_nonsingular f.injective ..).mpr h) :=
  rfl

end RingHomMap

/-! ### The change of variables `(x, y) ↦ (u²x + r, u³y)` -/

section VariableChange

variable {F : Type*} [Field F]

/-- The change of variables `⟨u, r, 0, 0⟩`. -/
def vc (u : Fˣ) (r : F) : VariableChange F := ⟨u, r, 0, 0⟩

variable (W : Affine F) (u : Fˣ) (r : F)

theorem vc_a₁ : (vc u r • W).a₁ = (u : F)⁻¹ * W.a₁ := by
  simp [variableChange_a₁, vc, Units.val_inv_eq_inv_val]

theorem vc_a₂ : (vc u r • W).a₂ = (u : F)⁻¹ ^ 2 * (W.a₂ + 3 * r) := by
  simp only [variableChange_a₂, vc, Units.val_inv_eq_inv_val]
  ring

theorem vc_a₃ : (vc u r • W).a₃ = (u : F)⁻¹ ^ 3 * (W.a₃ + r * W.a₁) := by
  simp only [variableChange_a₃, vc, Units.val_inv_eq_inv_val]
  ring

theorem vc_a₄ : (vc u r • W).a₄ = (u : F)⁻¹ ^ 4 * (W.a₄ + 2 * r * W.a₂ + 3 * r ^ 2) := by
  simp only [variableChange_a₄, vc, Units.val_inv_eq_inv_val]
  ring

theorem vc_a₆ :
    (vc u r • W).a₆ = (u : F)⁻¹ ^ 6 * (W.a₆ + r * W.a₄ + r ^ 2 * W.a₂ + r ^ 3) := by
  simp only [variableChange_a₆, vc, Units.val_inv_eq_inv_val]
  ring

variable {W u r}

theorem vc_equation_iff (x y : F) :
    (vc u r • W).toAffine.Equation x y ↔ W.Equation (u ^ 2 * x + r) (u ^ 3 * y) := by
  have hu : (u : F) ≠ 0 := u.ne_zero
  rw [equation_iff', equation_iff', vc_a₁, vc_a₂, vc_a₃, vc_a₄, vc_a₆]
  have key : (u ^ 3 * y) ^ 2 + W.a₁ * (u ^ 2 * x + r) * (u ^ 3 * y) + W.a₃ * (u ^ 3 * y) -
      ((u ^ 2 * x + r) ^ 3 + W.a₂ * (u ^ 2 * x + r) ^ 2 + W.a₄ * (u ^ 2 * x + r) + W.a₆) =
      (u : F) ^ 6 * (y ^ 2 + (u : F)⁻¹ * W.a₁ * x * y + (u : F)⁻¹ ^ 3 * (W.a₃ + r * W.a₁) * y -
        (x ^ 3 + (u : F)⁻¹ ^ 2 * (W.a₂ + 3 * r) * x ^ 2 +
          (u : F)⁻¹ ^ 4 * (W.a₄ + 2 * r * W.a₂ + 3 * r ^ 2) * x +
          (u : F)⁻¹ ^ 6 * (W.a₆ + r * W.a₄ + r ^ 2 * W.a₂ + r ^ 3))) := by
    field_simp
    ring
  rw [key, mul_eq_zero, or_iff_right (pow_ne_zero _ hu)]

theorem vc_nonsingular_iff (x y : F) :
    (vc u r • W).toAffine.Nonsingular x y ↔ W.Nonsingular (u ^ 2 * x + r) (u ^ 3 * y) := by
  have hu : (u : F) ≠ 0 := u.ne_zero
  rw [nonsingular_iff', nonsingular_iff', ← vc_equation_iff, vc_a₁, vc_a₂, vc_a₃, vc_a₄]
  have kX : W.a₁ * (u ^ 3 * y) - (3 * (u ^ 2 * x + r) ^ 2 + 2 * W.a₂ * (u ^ 2 * x + r) + W.a₄) =
      (u : F) ^ 4 * ((u : F)⁻¹ * W.a₁ * y -
        (3 * x ^ 2 + 2 * ((u : F)⁻¹ ^ 2 * (W.a₂ + 3 * r)) * x +
          (u : F)⁻¹ ^ 4 * (W.a₄ + 2 * r * W.a₂ + 3 * r ^ 2))) := by
    field_simp
    ring
  have kY : 2 * (u ^ 3 * y) + W.a₁ * (u ^ 2 * x + r) + W.a₃ =
      (u : F) ^ 3 * (2 * y + (u : F)⁻¹ * W.a₁ * x + (u : F)⁻¹ ^ 3 * (W.a₃ + r * W.a₁)) := by
    field_simp
    ring
  rw [kX, kY, mul_ne_zero_iff, mul_ne_zero_iff, and_iff_right (pow_ne_zero _ hu),
    and_iff_right (pow_ne_zero _ hu)]

theorem vc_negY (x y : F) :
    W.negY (u ^ 2 * x + r) (u ^ 3 * y) = u ^ 3 * (vc u r • W).toAffine.negY x y := by
  have hu : (u : F) ≠ 0 := u.ne_zero
  simp only [negY, vc_a₁, vc_a₃]
  field_simp
  ring

theorem vc_addX (x₁ x₂ L : F) :
    W.addX (u ^ 2 * x₁ + r) (u ^ 2 * x₂ + r) (u * L) =
      u ^ 2 * (vc u r • W).toAffine.addX x₁ x₂ L + r := by
  have hu : (u : F) ≠ 0 := u.ne_zero
  simp only [addX, vc_a₁, vc_a₂]
  field_simp
  ring

theorem vc_negAddY (x₁ x₂ y₁ L : F) :
    W.negAddY (u ^ 2 * x₁ + r) (u ^ 2 * x₂ + r) (u ^ 3 * y₁) (u * L) =
      u ^ 3 * (vc u r • W).toAffine.negAddY x₁ x₂ y₁ L := by
  simp only [negAddY, vc_addX]
  ring

theorem vc_addY (x₁ x₂ y₁ L : F) :
    W.addY (u ^ 2 * x₁ + r) (u ^ 2 * x₂ + r) (u ^ 3 * y₁) (u * L) =
      u ^ 3 * (vc u r • W).toAffine.addY x₁ x₂ y₁ L := by
  rw [addY, addY, vc_addX, vc_negAddY, vc_negY]

theorem vc_slope (x₁ x₂ y₁ y₂ : F) :
    W.slope (u ^ 2 * x₁ + r) (u ^ 2 * x₂ + r) (u ^ 3 * y₁) (u ^ 3 * y₂) =
      u * (vc u r • W).toAffine.slope x₁ x₂ y₁ y₂ := by
  have hu : (u : F) ≠ 0 := u.ne_zero
  have hu2 : (u : F) ^ 2 ≠ 0 := pow_ne_zero _ hu
  have hu3 : (u : F) ^ 3 ≠ 0 := pow_ne_zero _ hu
  by_cases hx : x₁ = x₂
  · by_cases hy : y₁ = (vc u r • W).toAffine.negY x₂ y₂
    · rw [slope_of_Y_eq (by rw [hx]) (by rw [hy, vc_negY]), slope_of_Y_eq hx hy, mul_zero]
    · have hy' : u ^ 3 * y₁ ≠ W.negY (u ^ 2 * x₂ + r) (u ^ 3 * y₂) := by
        rw [vc_negY]
        exact fun h ↦ hy (mul_left_cancel₀ hu3 h)
      rw [slope_of_Y_ne (by rw [hx]) hy', slope_of_Y_ne hx hy]
      have hnum : 3 * (u ^ 2 * x₁ + r) ^ 2 + 2 * W.a₂ * (u ^ 2 * x₁ + r) + W.a₄ -
          W.a₁ * (u ^ 3 * y₁) =
          u ^ 4 * (3 * x₁ ^ 2 + 2 * (vc u r • W).a₂ * x₁ + (vc u r • W).a₄ -
            (vc u r • W).a₁ * y₁) := by
        rw [vc_a₁, vc_a₂, vc_a₄]
        field_simp
        ring
      have hden : u ^ 3 * y₁ - W.negY (u ^ 2 * x₁ + r) (u ^ 3 * y₁) =
          u ^ 3 * (y₁ - (vc u r • W).toAffine.negY x₁ y₁) := by
        rw [vc_negY]
        ring
      have h43 : (u : F) ^ 4 / u ^ 3 = u := by
        field_simp
      rw [hnum, hden, mul_div_mul_comm, h43]
  · have hx' : u ^ 2 * x₁ + r ≠ u ^ 2 * x₂ + r := fun h ↦
      hx (mul_left_cancel₀ hu2 (add_right_cancel h))
    rw [slope_of_X_ne hx', slope_of_X_ne hx]
    have hsub : u ^ 2 * x₁ + r - (u ^ 2 * x₂ + r) ≠ 0 := sub_ne_zero.mpr hx'
    have hsub' : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
    rw [div_eq_iff hsub, mul_div_assoc', div_mul_eq_mul_div, eq_div_iff hsub']
    ring

/-- **The map of points of the change of variables** `vc u r`: `(x, y) ↦ (u²x + r, u³y)`, from
the points of `vc u r • W` to those of `W`. -/
noncomputable def vcPoint (u : Fˣ) (r : F) : (vc u r • W).toAffine.Point →+ W.Point where
  toFun P := match P with
    | 0 => 0
    | Point.some _ _ h => Point.some _ _ ((vc_nonsingular_iff ..).mp h)
  map_zero' := rfl
  map_add' := by
    have hu : (u : F) ≠ 0 := u.ne_zero
    rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩)
    any_goals rfl
    by_cases hxy : x₁ = x₂ ∧ y₁ = (vc u r • W).toAffine.negY x₂ y₂
    · rw [Point.add_of_Y_eq hxy.left hxy.right,
        Point.add_of_Y_eq (by rw [hxy.left]) (by rw [hxy.right, vc_negY])]
    · have hxy' : ¬(u ^ 2 * x₁ + r = u ^ 2 * x₂ + r ∧
          u ^ 3 * y₁ = W.negY (u ^ 2 * x₂ + r) (u ^ 3 * y₂)) := by
        rintro ⟨h1, h2⟩
        rw [vc_negY] at h2
        exact hxy ⟨mul_left_cancel₀ (pow_ne_zero 2 hu) (add_right_cancel h1),
          mul_left_cancel₀ (pow_ne_zero 3 hu) h2⟩
      rw [Point.add_some hxy]
      change _ = Point.some _ _ _ + Point.some _ _ _
      rw [Point.add_some hxy']
      exact some_congr (by rw [vc_slope, vc_addX]) (by rw [vc_slope, vc_addY])

theorem vcPoint_some {x y : F} (h : (vc u r • W).toAffine.Nonsingular x y) :
    vcPoint (W := W) u r (Point.some x y h) =
      Point.some (u ^ 2 * x + r) (u ^ 3 * y) ((vc_nonsingular_iff ..).mp h) :=
  rfl

end VariableChange

end Iut.Tripod
