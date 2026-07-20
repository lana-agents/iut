import Mathlib

/-!
# Comparator challenge: IUT IV Section 1

This mathlib-only module contains the ten standalone Section 1 targets selected
for the comparator suite. Auxiliary definitions provide their statement
vocabulary.
-/

open scoped ComplexConjugate TensorProduct

namespace Iut4Sec1

noncomputable def aParam (p e : ℕ) : ℝ :=
  if 2 < p then
    ((⌈(e : ℝ) / (p - 2 : ℕ)⌉ : ℤ) : ℝ) / e
  else 2

noncomputable def bParam (p e : ℕ) : ℝ :=
  ((⌊Real.log (((p : ℝ) * e) / (p - 1 : ℕ)) / Real.log p⌋ : ℤ) : ℝ) - 1 / e

theorem localParameters_eq_of_smallRamification
    (p e : ℕ) (hp : p.Prime) (hp2 : 2 < p)
    (he : 0 < e) (hsmall : e ≤ p - 2) :
    aParam p e = 1 / (e : ℝ) ∧ bParam p e = -1 / (e : ℝ) := by
  sorry

noncomputable def nonarchimedeanLogError (p e : ℕ) : ℝ :=
  ((⌈(e : ℝ) / (p - 2 : ℕ)⌉ : ℤ) : ℝ) / e - 1 / e

theorem nonarchimedean_logError_sum_le {ι : Type*} [DecidableEq ι]
    (p : ℕ) (I Istar : Finset ι) (e : ι → ℕ)
    (hp : p.Prime) (hp2 : 2 < p) (hIstar : Istar ⊆ I)
    (he : ∀ i ∈ I, 0 < e i)
    (hsmall : ∀ i ∈ I, i ∉ Istar → e i ≤ p - 2) :
    ∑ i ∈ I, nonarchimedeanLogError p (e i) ≤
      4 * (Istar.card : ℝ) / p := by
  sorry

theorem nonarchimedean_secondError_sum_le {ι : Type*} [DecidableEq ι]
    (p : ℕ) (I Istar : Finset ι) (e : ι → ℕ)
    (hp : p.Prime) (hIstar : Istar ⊆ I)
    (he : ∀ i ∈ I, 0 < e i)
    (hsmall : ∀ i ∈ I, i ∉ Istar → e i ≤ p - 2) :
    (∑ i ∈ I, (aParam p (e i) + bParam p (e i))) * Real.log p ≤
      ∑ i ∈ Istar, (3 + Real.log (e i)) := by
  sorry

noncomputable def complexTensorToProd : (ℂ ⊗[ℝ] ℂ) →ₗ[ℝ] ℂ × ℂ :=
  TensorProduct.lift <| LinearMap.mk₂ ℝ
    (fun z w : ℂ => (z * w, conj z * w))
    (by intros; ext <;> simp [add_mul])
    (by intros; ext <;> simp <;> ring)
    (by intros; ext <;> simp [mul_add])
    (by intros; ext <;> simp <;> ring)

theorem complexTensorToProd_bijective :
    Function.Bijective complexTensorToProd := by
  sorry

def complexPairNormSq (u : ℂ × ℂ) : ℝ :=
  Complex.normSq u.1 + Complex.normSq u.2

theorem complexTensorToProd_normSq (x : ℂ ⊗[ℝ] ℂ) :
    complexPairNormSq (complexTensorToProd x) = 2 * ‖x‖ ^ 2 := by
  sorry

theorem eventually_primeCounting_le_four_thirds :
    ∀ᶠ x : ℝ in Filter.atTop,
      (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤
        4 * x / (3 * Real.log x) := by
  sorry

noncomputable def tupleWeight {n : ℕ} {E : Type*}
    (weight : E → ℝ) (x : Fin n → E) : ℝ :=
  ∏ j, weight (x j)

noncomputable def tupleValue {n : ℕ} {E : Type*}
    (β : E → ℝ) (x : Fin n → E) : ℝ :=
  ∑ j, β (x j)

theorem weighted_average_eq {E : Type*} [Fintype E] [Nonempty E]
    {n : ℕ} [NeZero n] (weight β : E → ℝ)
    (hweight : ∀ e, 0 < weight e) (i : Fin n) :
    (∑ x : Fin n → E, tupleValue β x * tupleWeight weight x) /
          (∑ x : Fin n → E, tupleWeight weight x) =
        (∑ x : Fin n → E, n * β (x i) * tupleWeight weight x) /
          (∑ x : Fin n → E, tupleWeight weight x) ∧
      (∑ x : Fin n → E, n * β (x i) * tupleWeight weight x) /
          (∑ x : Fin n → E, tupleWeight weight x) =
        n * ((∑ e : E, β e * weight e) / (∑ e : E, weight e)) := by
  sorry

theorem average_range_sum (n : ℕ) (hn : 0 < n) :
    (1 / (n : ℝ)) * ∑ m ∈ Finset.range n, (m + 1 : ℝ) =
      ((n : ℝ) + 1) / 2 := by
  sorry

theorem average_range_sq_sum (n : ℕ) (hn : 0 < n) :
    (1 / (n : ℝ)) * ∑ m ∈ Finset.range n, (m + 1 : ℝ) ^ 2 =
      ((2 * (n : ℝ) + 1) * ((n : ℝ) + 1)) / 6 := by
  sorry

def ArithmeticPlace (K : Type*) [Field K] [NumberField K] :=
  NumberField.FinitePlace K ⊕ NumberField.InfinitePlace K

def ArithmeticDivisor (K : Type*) [Field K] [NumberField K] :=
  ArithmeticPlace K →₀ ℝ

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

theorem normalizedArithmeticDivisorDegree_nonneg
    {K : Type*} [Field K] [NumberField K]
    (D : ArithmeticDivisor K)
    (hD : ArithmeticDivisorEffective D) :
    0 ≤ normalizedArithmeticDivisorDegree D := by
  sorry

end Iut4Sec1
