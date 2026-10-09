/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib

/-!
# Integral, good and multiplicative Weierstrass models for a valuation

The predicates `Iut.IsIntegralModel v E`, `Iut.IsGoodModel v E`, `Iut.IsMultModel v E` and
`Iut.IsStableModel v E` for a valuation `v` on the base field, with the integrality of the
derived coefficients of an integral model, and the integrality of the roots of a monic
quadratic with integral coefficients (`Iut.valuation_le_one_of_quadratic`).
-/

namespace Iut

open WeierstrassCurve
open scoped WithZero

/-! ## Good and multiplicative models for a valuation -/

section Models

variable {K : Type*} [Field K] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
  (v : Valuation K Γ) (E : WeierstrassCurve K)

/-- The model `E` is integral for the valuation `v`: `v(aᵢ) ≤ 1`. -/
def IsIntegralModel : Prop :=
  v E.a₁ ≤ 1 ∧ v E.a₂ ≤ 1 ∧ v E.a₃ ≤ 1 ∧ v E.a₄ ≤ 1 ∧ v E.a₆ ≤ 1

/-- The model `E` is good for `v`: integral with a unit discriminant. -/
def IsGoodModel : Prop := IsIntegralModel v E ∧ v E.Δ = 1

/-- The model `E` is multiplicative for `v`: integral with a non-unit discriminant and a
unit `c₄`. -/
def IsMultModel : Prop := IsIntegralModel v E ∧ v E.Δ < 1 ∧ v E.c₄ = 1

/-- The model `E` is good or multiplicative for `v`. -/
def IsStableModel : Prop := IsGoodModel v E ∨ IsMultModel v E

variable {v E}

lemma IsIntegralModel.b₂ (h : IsIntegralModel v E) : v E.b₂ ≤ 1 := by
  obtain ⟨h₁, h₂, -, -, -⟩ := h
  rw [← Valuation.mem_integer_iff] at *
  exact add_mem (pow_mem h₁ 2) (mul_mem (ofNat_mem _ 4) h₂)

lemma IsIntegralModel.b₄ (h : IsIntegralModel v E) : v E.b₄ ≤ 1 := by
  obtain ⟨h₁, -, h₃, h₄, -⟩ := h
  rw [← Valuation.mem_integer_iff] at *
  exact add_mem (mul_mem (ofNat_mem _ 2) h₄) (mul_mem h₁ h₃)

lemma IsIntegralModel.b₆ (h : IsIntegralModel v E) : v E.b₆ ≤ 1 := by
  obtain ⟨-, -, h₃, -, h₆⟩ := h
  rw [← Valuation.mem_integer_iff] at *
  exact add_mem (pow_mem h₃ 2) (mul_mem (ofNat_mem _ 4) h₆)

lemma IsIntegralModel.b₈ (h : IsIntegralModel v E) : v E.b₈ ≤ 1 := by
  obtain ⟨h₁, h₂, h₃, h₄, h₆⟩ := h
  rw [← Valuation.mem_integer_iff] at *
  exact sub_mem (add_mem (sub_mem (add_mem (mul_mem (pow_mem h₁ 2) h₆)
    (mul_mem (mul_mem (ofNat_mem _ 4) h₂) h₆)) (mul_mem (mul_mem h₁ h₃) h₄))
    (mul_mem h₂ (pow_mem h₃ 2))) (pow_mem h₄ 2)

lemma IsIntegralModel.c₄ (h : IsIntegralModel v E) : v E.c₄ ≤ 1 := by
  have h₂ := h.b₂
  have h₄ := h.b₄
  rw [← Valuation.mem_integer_iff] at *
  exact sub_mem (pow_mem h₂ 2) (mul_mem (ofNat_mem _ 24) h₄)

lemma IsIntegralModel.Δ (h : IsIntegralModel v E) : v E.Δ ≤ 1 := by
  have h₂ := h.b₂
  have h₄ := h.b₄
  have h₆ := h.b₆
  have h₈ := h.b₈
  rw [← Valuation.mem_integer_iff] at *
  exact add_mem (sub_mem (sub_mem (mul_mem (neg_mem (pow_mem h₂ 2)) h₈)
    (mul_mem (ofNat_mem _ 8) (pow_mem h₄ 3))) (mul_mem (ofNat_mem _ 27) (pow_mem h₆ 2)))
    (mul_mem (mul_mem (mul_mem (ofNat_mem _ 9) h₂) h₄) h₆)

end Models

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

end Integrality

end Iut
