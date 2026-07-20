/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/

import Mathlib

/-!
# Arithmetic divisors over number fields

This file formalizes the finite-support model in Definition 1.9(i). Finite places
are weighted by the logarithm of the absolute norm of their maximal ideal, and
infinite places have weight one.
-/

namespace Iut4Sec1

abbrev ArithmeticPlace (K : Type*) [Field K] [NumberField K] :=
  NumberField.FinitePlace K ⊕ NumberField.InfinitePlace K

abbrev ArithmeticDivisor (K : Type*) [Field K] [NumberField K] :=
  ArithmeticPlace K →₀ ℝ

/-- The finite support of an arithmetic divisor. -/
def arithmeticDivisorSupport {K : Type*} [Field K] [NumberField K]
    (D : ArithmeticDivisor K) : Finset (ArithmeticPlace K) :=
  D.support

noncomputable def arithmeticPlaceWeight
    {K : Type*} [Field K] [NumberField K] : ArithmeticPlace K → ℝ
  | .inl v => Real.log (Ideal.absNorm v.maximalIdeal.asIdeal : ℝ)
  | .inr _ => 1

def ArithmeticDivisorEffective
    {K : Type*} [Field K] [NumberField K] (D : ArithmeticDivisor K) : Prop :=
  ∀ v, 0 ≤ (show ArithmeticPlace K →₀ ℝ from D) v

noncomputable def arithmeticDivisorDegree
    {K : Type*} [Field K] [NumberField K] (D : ArithmeticDivisor K) : ℝ :=
  D.sum fun v c => c * arithmeticPlaceWeight v

noncomputable def normalizedArithmeticDivisorDegree
    {K : Type*} [Field K] [NumberField K] (D : ArithmeticDivisor K) : ℝ :=
  arithmeticDivisorDegree D / Module.finrank ℚ K

@[simp]
lemma arithmeticDivisorDegree_zero {K : Type*} [Field K] [NumberField K] :
    arithmeticDivisorDegree (0 : ArithmeticDivisor K) = 0 := by
  simp [arithmeticDivisorDegree]

lemma arithmeticDivisorDegree_add {K : Type*} [Field K] [NumberField K]
    (D₁ D₂ : ArithmeticDivisor K) :
    arithmeticDivisorDegree (D₁ + D₂) =
      arithmeticDivisorDegree D₁ + arithmeticDivisorDegree D₂ := by
  change (D₁ + D₂).sum (fun v c => c * arithmeticPlaceWeight v) =
    D₁.sum (fun v c => c * arithmeticPlaceWeight v) +
      D₂.sum (fun v c => c * arithmeticPlaceWeight v)
  exact Finsupp.sum_add_index' (by simp) (by intros; ring)

/-- Raw arithmetic-divisor degree as an additive homomorphism. -/
noncomputable def arithmeticDivisorDegreeHom
    {K : Type*} [Field K] [NumberField K] : ArithmeticDivisor K →+ ℝ where
  toFun := arithmeticDivisorDegree
  map_zero' := arithmeticDivisorDegree_zero
  map_add' := arithmeticDivisorDegree_add

@[simp]
lemma arithmeticDivisorDegreeHom_apply {K : Type*} [Field K] [NumberField K]
    (D : ArithmeticDivisor K) : arithmeticDivisorDegreeHom D = arithmeticDivisorDegree D := rfl

/-- The part of a divisor supported on the places satisfying `p`. -/
noncomputable def arithmeticDivisorPart {K : Type*} [Field K] [NumberField K]
    (D : ArithmeticDivisor K) (p : ArithmeticPlace K → Prop) : ArithmeticDivisor K := by
  classical
  exact (show ArithmeticPlace K →₀ ℝ from D).filter p

lemma arithmeticDivisorPart_apply_of_mem {K : Type*} [Field K] [NumberField K]
    (D : ArithmeticDivisor K) (p : ArithmeticPlace K → Prop) (v : ArithmeticPlace K)
    (hv : p v) :
    (show ArithmeticPlace K →₀ ℝ from arithmeticDivisorPart D p) v =
      (show ArithmeticPlace K →₀ ℝ from D) v := by
  classical
  simp [arithmeticDivisorPart, hv]

lemma arithmeticDivisorPart_apply_of_not_mem {K : Type*} [Field K] [NumberField K]
    (D : ArithmeticDivisor K) (p : ArithmeticPlace K → Prop) (v : ArithmeticPlace K)
    (hv : ¬p v) :
    (show ArithmeticPlace K →₀ ℝ from arithmeticDivisorPart D p) v = 0 := by
  classical
  simp [arithmeticDivisorPart, hv]

lemma arithmeticPlaceWeight_nonneg {K : Type*} [Field K] [NumberField K]
    (v : ArithmeticPlace K) : 0 ≤ arithmeticPlaceWeight v := by
  cases v with
  | inl v => exact Real.log_natCast_nonneg _
  | inr v => simp [arithmeticPlaceWeight]

lemma arithmeticDivisorDegree_nonneg {K : Type*} [Field K] [NumberField K]
    (D : ArithmeticDivisor K) (hD : ArithmeticDivisorEffective D) :
    0 ≤ arithmeticDivisorDegree D := by
  rw [arithmeticDivisorDegree]
  apply Finsupp.sum_nonneg
  intro v _
  exact mul_nonneg (hD v) (arithmeticPlaceWeight_nonneg v)

/-- Effective arithmetic divisors have nonnegative normalized degree. -/
theorem normalizedArithmeticDivisorDegree_nonneg
    {K : Type*} [Field K] [NumberField K]
    (D : ArithmeticDivisor K)
    (hD : ArithmeticDivisorEffective D) :
    0 ≤ normalizedArithmeticDivisorDegree D := by
  rw [normalizedArithmeticDivisorDegree]
  exact div_nonneg (arithmeticDivisorDegree_nonneg D hD) (by positivity)

end Iut4Sec1
