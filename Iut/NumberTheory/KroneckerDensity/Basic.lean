/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.NumberTheory.KroneckerDensity.EulerProduct

/-!
# Kronecker density of primes of degree one

Let `K` be a number field. A nonzero prime ideal `𝔭` of `𝓞 K` is *of degree one* if its absolute
norm `N(𝔭)` is a rational prime. We prove **Kronecker's theorem**: as `s → 1⁺`,
`∑_{𝔭 of degree one} N(𝔭)^{-s} = log (1 / (s - 1)) + O(1)`; more precisely the difference is
bounded on `(1, 2]`.

## Main definitions and results

* `NumberField.degOnePrimes K`: the set of prime ideals of `𝓞 K` of degree one.
* `NumberField.summable_inv_absNorm_compl_degOnePrimes`: `∑_{𝔭 not of degree one} N(𝔭)⁻¹`
  converges.
* `NumberField.exists_abs_tsum_degOnePrimes_sub_log_le`: Kronecker's theorem.

In the notation of Mathlib's `NumberTheory/NumberField/DirichletDensity` (Mathlib master), the sum
`∑' P : degOnePrimes K, N(P)^{-s}` is `(degOnePrimes K).primeIdealZetaSum s`.

## Proof

By `NumberField.exists_abs_tsum_rpow_neg_absNorm_sub_log_le` it suffices to bound the sum over
the primes `𝔭` that are not of degree one. Such a `𝔭` lies over a rational prime `p` with
`N(𝔭) = p ^ f` and `f ≥ 2`, so `N(𝔭)⁻¹ ≤ p⁻²`, and there are at most `[K : ℚ]` primes over each
`p` (`Ideal.card_primesOverFinset_le_finrank`).
-/

noncomputable section

open IsDedekindDomain

namespace NumberField

variable (K : Type*) [Field K] [NumberField K]

/-- Primes of degree one: absolute norm a rational prime. -/
def degOnePrimes : Set (HeightOneSpectrum (𝓞 K)) := {P | (Ideal.absNorm P.asIdeal).Prime}

variable {K}

lemma absNorm_eq_pow_absNorm_under (P : HeightOneSpectrum (𝓞 K)) :
    Ideal.absNorm P.asIdeal = Ideal.absNorm (P.asIdeal.under ℤ) ^
      (Ideal.span {(Ideal.absNorm (P.asIdeal.under ℤ) : ℤ)}).inertiaDeg' P.asIdeal := by
  have : NeZero P.asIdeal := ⟨P.ne_bot⟩
  have : P.asIdeal.IsPrime := P.isPrime
  exact Ideal.absNorm_eq_pow_inertiaDeg' P.asIdeal (Nat.absNorm_under_prime P.asIdeal)

omit [NumberField K] in
lemma absNorm_under_prime (P : HeightOneSpectrum (𝓞 K)) :
    (Ideal.absNorm (P.asIdeal.under ℤ)).Prime := by
  have : NeZero P.asIdeal := ⟨P.ne_bot⟩
  have : P.asIdeal.IsPrime := P.isPrime
  exact Nat.absNorm_under_prime P.asIdeal

/-- A prime ideal which is not of degree one lying over `p` has norm at least `p ^ 2`. -/
lemma sq_absNorm_under_le (P : HeightOneSpectrum (𝓞 K)) (hP : P ∉ degOnePrimes K) :
    Ideal.absNorm (P.asIdeal.under ℤ) ^ 2 ≤ Ideal.absNorm P.asIdeal := by
  have hp := absNorm_under_prime P
  have h2 := two_le_absNorm_heightOneSpectrum P
  have hP' : ¬ (Ideal.absNorm P.asIdeal).Prime := hP
  rw [absNorm_eq_pow_absNorm_under P] at h2 hP' ⊢
  set f := (Ideal.span {(Ideal.absNorm (P.asIdeal.under ℤ) : ℤ)}).inertiaDeg' P.asIdeal
  rcases Nat.lt_or_ge f 2 with h | h
  · interval_cases f
    · simp at h2
    · exact absurd (by simpa using hp) hP'
  · exact Nat.pow_le_pow_right hp.pos h

/-- There are at most `[K : ℚ]` prime ideals of `𝓞 K` over a given rational prime. -/
lemma finite_and_card_le_finrank (n : ℕ) :
    Finite {P : HeightOneSpectrum (𝓞 K) // Ideal.absNorm (P.asIdeal.under ℤ) = n} ∧
      Nat.card {P : HeightOneSpectrum (𝓞 K) // Ideal.absNorm (P.asIdeal.under ℤ) = n} ≤
        Module.finrank ℚ K := by
  classical
  by_cases hn : n.Prime
  · have hne : Ideal.span {(n : ℤ)} ≠ ⊥ := by simp [hn.ne_zero]
    have : (Ideal.span {(n : ℤ)}).IsMaximal :=
      ((Ideal.span_singleton_prime (by exact_mod_cast hn.ne_zero)).mpr
        (Nat.prime_iff_prime_int.mp hn)).isMaximal hne
    let φ : {P : HeightOneSpectrum (𝓞 K) // Ideal.absNorm (P.asIdeal.under ℤ) = n} →
        IsDedekindDomain.primesOverFinset (Ideal.span {(n : ℤ)}) (𝓞 K) := fun P ↦
      ⟨P.1.asIdeal, (IsDedekindDomain.mem_primesOverFinset_iff hne _).mpr ⟨P.1.isPrime, by
        have h := Int.liesOver_span_absNorm P.1.asIdeal
        rwa [P.2] at h⟩⟩
    have hφ : Function.Injective φ := fun P Q h ↦ by
      have h' := congrArg Subtype.val h
      exact Subtype.ext (HeightOneSpectrum.ext h')
    refine ⟨Finite.of_injective φ hφ, ?_⟩
    calc _ ≤ Nat.card (IsDedekindDomain.primesOverFinset (Ideal.span {(n : ℤ)}) (𝓞 K)) :=
          Nat.card_le_card_of_injective φ hφ
      _ = (IsDedekindDomain.primesOverFinset (Ideal.span {(n : ℤ)}) (𝓞 K)).card :=
          Nat.card_eq_finsetCard _
      _ ≤ _ := Ideal.card_primesOverFinset_le_finrank (𝓞 K) ℚ K hne
  · have : IsEmpty {P : HeightOneSpectrum (𝓞 K) // Ideal.absNorm (P.asIdeal.under ℤ) = n} :=
      ⟨fun P ↦ hn (P.2 ▸ absNorm_under_prime P.1)⟩
    exact ⟨inferInstance, by simp⟩

variable (K)

/-- The sum of `N(𝔭)⁻¹` over the prime ideals `𝔭` of `𝓞 K` that are not of degree one
converges. -/
theorem summable_inv_absNorm_compl_degOnePrimes :
    Summable fun P : ↥(degOnePrimes K)ᶜ ↦ (Ideal.absNorm P.1.asIdeal : ℝ)⁻¹ := by
  set π : ↥(degOnePrimes K)ᶜ → ℕ := fun P ↦ Ideal.absNorm (P.1.asIdeal.under ℤ)
  rw [← (Equiv.sigmaFiberEquiv π).summable_iff]
  have hfin : ∀ n, Finite {P : ↥(degOnePrimes K)ᶜ // π P = n} := fun n ↦
    have := (finite_and_card_le_finrank (K := K) n).1
    Finite.of_injective (fun P ↦ (⟨P.1.1, P.2⟩ :
      {P : HeightOneSpectrum (𝓞 K) // Ideal.absNorm (P.asIdeal.under ℤ) = n}))
      fun P Q h ↦ by
        have h' := congrArg Subtype.val h
        exact Subtype.ext (Subtype.ext h')
  refine (summable_sigma_of_nonneg fun _ ↦ inv_nonneg.mpr (Nat.cast_nonneg _)).mpr
    ⟨fun n ↦ Summable.of_finite, ?_⟩
  refine Summable.of_nonneg_of_le (fun n ↦ tsum_nonneg fun _ ↦ inv_nonneg.mpr (Nat.cast_nonneg _))
    (fun n ↦ ?_)
    ((Real.summable_nat_pow_inv.mpr one_lt_two).mul_left (Module.finrank ℚ K : ℝ))
  simp only [Equiv.sigmaFiberEquiv_apply]
  calc ∑' P : {P : ↥(degOnePrimes K)ᶜ // π P = n}, (Ideal.absNorm P.1.1.asIdeal : ℝ)⁻¹
      ≤ ∑' _ : {P : ↥(degOnePrimes K)ᶜ // π P = n}, ((n : ℝ) ^ 2)⁻¹ := by
        refine Summable.tsum_le_tsum (fun P ↦ ?_) Summable.of_finite Summable.of_finite
        have hp := absNorm_under_prime P.1.1
        have hle := sq_absNorm_under_le P.1.1 P.1.2
        have hPn : Ideal.absNorm (P.1.1.asIdeal.under ℤ) = n := P.2
        rw [hPn] at hp hle
        exact inv_anti₀ (pow_pos (by exact_mod_cast hp.pos) 2) (by exact_mod_cast hle)
    _ = Nat.card {P : ↥(degOnePrimes K)ᶜ // π P = n} * ((n : ℝ) ^ 2)⁻¹ := by
        rw [tsum_const, nsmul_eq_mul]
    _ ≤ Module.finrank ℚ K * ((n : ℝ) ^ 2)⁻¹ := by
        gcongr
        have := (finite_and_card_le_finrank (K := K) n)
        have : Finite {P : HeightOneSpectrum (𝓞 K) // Ideal.absNorm (P.asIdeal.under ℤ) = n} :=
          this.1
        refine le_trans (Nat.card_le_card_of_injective (fun P ↦ (⟨P.1.1, P.2⟩ :
          {P : HeightOneSpectrum (𝓞 K) // Ideal.absNorm (P.asIdeal.under ℤ) = n}))
          fun P Q h ↦ by
            have h' := congrArg Subtype.val h
            exact Subtype.ext (Subtype.ext h')) ?_
        exact (finite_and_card_le_finrank n).2

/-- **Kronecker density** (KD2): `∑_{𝔭 of degree one} N(𝔭)^{-s} = log (1 / (s - 1)) + O(1)`
for `s ∈ (1, 2]`. -/
theorem exists_abs_tsum_degOnePrimes_sub_log_le : ∃ C : ℝ, ∀ s ∈ Set.Ioc (1 : ℝ) 2,
    |∑' P : degOnePrimes K, (Ideal.absNorm P.1.asIdeal : ℝ) ^ (-s) - Real.log (1 / (s - 1))| ≤
      C := by
  obtain ⟨C, hC⟩ := exists_abs_tsum_rpow_neg_absNorm_sub_log_le K
  set B := ∑' P : ↥(degOnePrimes K)ᶜ, (Ideal.absNorm P.1.asIdeal : ℝ)⁻¹
  refine ⟨C + B, fun s hs ↦ ?_⟩
  have hx := summable_rpow_neg_absNorm_heightOneSpectrum K hs.1
  have hsplit := hx.tsum_subtype_add_tsum_subtype_compl (degOnePrimes K)
  have h0 : 0 ≤ ∑' P : ↥(degOnePrimes K)ᶜ, (Ideal.absNorm P.1.asIdeal : ℝ) ^ (-s) :=
    tsum_nonneg fun P ↦ rpow_neg_absNorm_nonneg _ _
  have h1 : ∑' P : ↥(degOnePrimes K)ᶜ, (Ideal.absNorm P.1.asIdeal : ℝ) ^ (-s) ≤ B :=
    Summable.tsum_le_tsum
      (fun P ↦ rpow_neg_absNorm_heightOneSpectrum_le_inv P.1 hs.1.le)
      (hx.subtype _) (summable_inv_absNorm_compl_degOnePrimes K)
  have h2 := hC s hs
  rw [abs_le] at h2 ⊢
  constructor <;> linarith [h2.1, h2.2]

end NumberField
