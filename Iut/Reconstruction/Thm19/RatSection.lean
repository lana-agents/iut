/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Thm19.EllipticNF

/-!
# `K`-rational sections of `Ē` from points of `E` (MR9)

Let `E` be an elliptic curve over a field `K` of characteristic zero and `Ē = curveE E` its
smooth projective model (the normalisation of `ℙ¹_K` in `E ∖ E[2] = Spec K[E][1/ψ]`,
curves-jacobian). A point `(x, y)` of the affine Weierstrass model with
`ψ(x, y) = 2y + a₁x + a₃ ≠ 0` gives a `K`-algebra map `K[E][1/ψ] → K` (evaluation at `(x, y)`),
hence a section `Spec K → E ∖ E[2] ⊆ Ē` of the structure morphism of `Ē`.

* `ratSection`, `ratSection_comp`: the section attached to `(x, y)` and the identity
  `σ₀ ≫ (Ē ↘ Spec K) = 𝟙`, stated in the form of the hypothesis `hσ₀` of `nfConstEquiv_fix_j`;
* `exists_ratSection`: a point `P` of `E` with `P ≠ 0` and `2 • P ≠ 0` gives such a section.
-/

open CategoryTheory AlgebraicGeometry CurvesJacobian.Cusp Polynomial

universe u

noncomputable section

namespace Iut.Reconstruction.Thm19

variable {K : Type u} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]

/-- Evaluation `K[E] → K` at a point `(x, y)` of the affine Weierstrass model. -/
def coordEval {x y : K} (h : E.toAffine.Equation x y) : E.toAffine.CoordinateRing →+* K :=
  AdjoinRoot.evalEval h

omit [CharZero K] [E.IsElliptic] in
/-- `ψ(x, y) = 2y + a₁x + a₃`. -/
lemma coordEval_psiE {x y : K} (h : E.toAffine.Equation x y) :
    coordEval E h (psiE E) = 2 * y + E.a₁ * x + E.a₃ := by
  rw [coordEval, psiE, AdjoinRoot.evalEval_mk, WeierstrassCurve.Affine.evalEval_polynomialY]

omit [CharZero K] [E.IsElliptic] in
/-- Evaluation at `(x, y)` is `K`-linear. -/
lemma coordEval_algebraMap {x y : K} (h : E.toAffine.Equation x y) (c : K) :
    coordEval E h (algebraMap K E.toAffine.CoordinateRing c) = c := by
  rw [IsScalarTower.algebraMap_apply K K[X] E.toAffine.CoordinateRing, AdjoinRoot.algebraMap_eq,
    coordEval, AdjoinRoot.evalEval, AdjoinRoot.lift_of]
  simp

/-- Evaluation `K[E][1/ψ] → K` at a point `(x, y)` with `ψ(x, y) ≠ 0`. -/
def coverEval {x y : K} (h : E.toAffine.Equation x y) (hψ : 2 * y + E.a₁ * x + E.a₃ ≠ 0) :
    coverRingE E →+* K :=
  IsLocalization.Away.lift (psiE E)
    (g := coordEval E h) ((coordEval_psiE E h).symm ▸ hψ.isUnit)

omit [CharZero K] [E.IsElliptic] in
/-- Evaluation at `(x, y)` on `K[E][1/ψ]` is a retraction of `K → K[E][1/ψ]`. -/
lemma coverEval_comp_algebraMap {x y : K} (h : E.toAffine.Equation x y)
    (hψ : 2 * y + E.a₁ * x + E.a₃ ≠ 0) :
    (coverEval E h hψ).comp (algebraMap K (coverRingE E)) = RingHom.id K := by
  ext c
  rw [RingHom.comp_apply,
    IsScalarTower.algebraMap_apply K E.toAffine.CoordinateRing (coverRingE E), coverEval,
    IsLocalization.Away.lift_eq, coordEval_algebraMap, RingHom.id_apply]

/-- **The `K`-rational point `(x, y)` of `E ∖ E[2] ⊆ Ē`** as a morphism `Spec K → Ē`
(for `(x, y)` on the affine Weierstrass model with `ψ(x, y) = 2y + a₁x + a₃ ≠ 0`). -/
def ratSection (x y : K) (h : E.toAffine.Equation x y) (hψ : 2 * y + E.a₁ * x + E.a₃ ≠ 0) :
    Spec (CommRingCat.of K) ⟶ (hypCurveE E).Xbar :=
  Spec.map (CommRingCat.ofHom (coverEval E h hψ)) ≫ toCurveE E

/-- The open immersion `E ∖ E[2] → Ē` lies over `Spec K`. -/
lemma toCurveE_over :
    toCurveE E ≫ ((hypCurveE E).Xbar ↘ Spec (CommRingCat.of K)) =
      Spec.map (CommRingCat.ofHom (algebraMap K (coverRingE E))) :=
  comp_over (toCurveE E) (Spec (CommRingCat.of K))

/-- **`ratSection` is a section** of the structure morphism `Ē ↘ Spec K` (in the form of the
hypothesis `hσ₀` of `nfConstEquiv_fix_j`). -/
theorem ratSection_comp (x y : K) (h : E.toAffine.Equation x y)
    (hψ : 2 * y + E.a₁ * x + E.a₃ ≠ 0) :
    ratSection E x y h hψ ≫ ((hypCurveE E).Xbar ↘ Spec (CommRingCat.of K)) =
      𝟙 (Spec (CommRingCat.of K)) := by
  rw [ratSection, Category.assoc, toCurveE_over, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    coverEval_comp_algebraMap]
  exact Spec.map_id _

omit [CharZero K] [E.IsElliptic] in
/-- A point `P` of `E` with `P ≠ 0` and `2 • P ≠ 0` is an affine point `(x, y)` with
`2y + a₁x + a₃ ≠ 0`. -/
lemma exists_affine_of_two_smul_ne [DecidableEq K] {P : E.toAffine.Point} (hP : P ≠ 0)
    (h2P : 2 • P ≠ 0) :
    ∃ x y : K, E.toAffine.Equation x y ∧ 2 * y + E.a₁ * x + E.a₃ ≠ 0 := by
  cases P with
  | zero => exact absurd rfl hP
  | some x y h =>
    refine ⟨x, y, h.1, fun hψ => h2P ?_⟩
    rw [two_smul]
    refine WeierstrassCurve.Affine.Point.add_self_of_Y_eq ?_
    rw [WeierstrassCurve.Affine.negY]
    linear_combination hψ

/-- **A `K`-rational section of `Ē ↘ Spec K`** from a point `P` of `E` with `P ≠ 0` and
`2 • P ≠ 0`. -/
theorem exists_ratSection [DecidableEq K] {P : E.toAffine.Point} (hP : P ≠ 0)
    (h2P : 2 • P ≠ 0) :
    ∃ σ₀ : Spec (CommRingCat.of K) ⟶ (hypCurveE E).Xbar,
      σ₀ ≫ ((hypCurveE E).Xbar ↘ Spec (CommRingCat.of K)) = 𝟙 (Spec (CommRingCat.of K)) := by
  obtain ⟨x, y, h, hψ⟩ := exists_affine_of_two_smul_ne E hP h2P
  exact ⟨ratSection E x y h hψ, ratSection_comp E x y h hψ⟩

end Iut.Reconstruction.Thm19
