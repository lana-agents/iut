/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Torsion.Count
import Iut.Tower.IntegralTorsion

/-!
# Divisibility of the points of an elliptic curve over an algebraically closed field

For an elliptic curve `W` over an algebraically closed field `K` of characteristic `0`, the
multiplication by `n ≠ 0` is surjective on `W(K)` (`Iut.Torsion.nsmul_surjective`): after
completing the square, a preimage of `Q = (x₀, y₀)` is a point whose `x`-coordinate is a root of
`Φₙ − x₀ ΨSqₙ` (of degree `n² ≥ 1`), up to sign.
-/

namespace Iut.Torsion

open WeierstrassCurve WeierstrassCurve.Affine Polynomial


variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

open scoped Classical in
/-- Surjectivity of `[n]` for a model `y² = x³ + a₂x² + a₄x + a₆`. -/
theorem nsmul_surjective_of_a₁_a₃ {W : Affine K} [W.IsElliptic] (ha₁ : W.a₁ = 0)
    (ha₃ : W.a₃ = 0) (n : ℕ) (hn : n ≠ 0) (Q : W.Point) : ∃ R : W.Point, n • R = Q := by
  rcases Q with _ | ⟨x₀, y₀, hQ⟩
  · exact ⟨0, smul_zero _⟩
  have hdeg : (fibrePoly W n x₀).degree ≠ 0 := by
    rw [degree_eq_natDegree (fibrePoly_ne_zero n hn x₀), natDegree_fibrePoly n hn x₀]
    exact_mod_cast (pow_pos (Nat.pos_of_ne_zero hn) 2).ne'
  obtain ⟨x₁, hx₁⟩ := IsAlgClosed.exists_root _ hdeg
  obtain ⟨y₁, h₁⟩ := exists_point ha₁ ha₃ x₁
  have hne := ΨSq_ne_zero_of_root ha₁ ha₃ n hn hx₁
  obtain ⟨X, Y, hXY, hnP, hX⟩ := smul_eq_of_ΨSq_ne_zero ha₁ ha₃ h₁ n hne
  have hXx : X = x₀ := by
    rw [IsRoot, eval_fibrePoly, ← hX] at hx₁
    exact mul_right_cancel₀ hne (by linear_combination hx₁)
  subst hXx
  have hY : Y = y₀ ∨ Y = -y₀ := by
    have e1 := (equation_iff₀ ha₁ ha₃ X Y).mp hXY.1
    have e2 := (equation_iff₀ ha₁ ha₃ X y₀).mp hQ.1
    have : (Y - y₀) * (Y + y₀) = 0 := by linear_combination e1 - e2
    rcases mul_eq_zero.mp this with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  rcases hY with rfl | rfl
  · exact ⟨_, hnP⟩
  · refine ⟨-Point.some x₁ y₁ h₁, ?_⟩
    rw [smul_neg, hnP, Point.neg_some]
    congr 1
    rw [negY_eq ha₁ ha₃, neg_neg]

open scoped Classical in
/-- **Divisibility**: over an algebraically closed field of characteristic `0`, the
multiplication by `n ≠ 0` is surjective on the points of an elliptic curve. -/
theorem nsmul_surjective (W : WeierstrassCurve K) [W.IsElliptic] (n : ℕ) (hn : n ≠ 0)
    (Q : W.toAffine.Point) : ∃ R : W.toAffine.Point, n • R = Q := by
  let C := IntegralTorsion.completeSquare W
  obtain ⟨R', hR'⟩ := nsmul_surjective_of_a₁_a₃ (W := (C • W).toAffine)
    (IntegralTorsion.completeSquare_a₁ W) (IntegralTorsion.completeSquare_a₃ W) n hn
    (Anabelian.vcEquiv C W Q)
  refine ⟨(Anabelian.vcEquiv C W).symm R', ?_⟩
  apply (Anabelian.vcEquiv C W).injective
  rw [map_nsmul, AddEquiv.apply_symm_apply, hR']

end Iut.Torsion
