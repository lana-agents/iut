/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib

/-!
# An upper bound for interpolation determinants of exponentials

We prove the analytic upper bound for the interpolation determinant `det (exp (l i * ξ j))`
that is used in the proof of the six exponentials theorem.

## Main results

* `Matrix.sum_perm_sign_mul_sum_pow_eq_zero`: (algebraic form of Waldschmidt's Lemma 2) for
  `m < L * (L - 1) / 2`, `∑ σ, sign σ * (∑ i, l i * ξ (σ i)) ^ m = 0`. Equivalently, the Taylor
  coefficients of order `< L * (L - 1) / 2` at the origin of `x ↦ det (exp (l i * ξ j * x))`
  vanish.
* `Real.abs_sum_mul_exp_le_of_sum_mul_pow_eq_zero`: (Waldschmidt's Lemma 3) if the first `M`
  Taylor coefficients of `x ↦ ∑ j, a j * exp (w j * x)` vanish, then for every `R ≥ 1`,
  `|∑ j, a j * exp (w j)| ≤ R ^ (-M) * ∑ j, |a j| * exp (R * |w j|)`.
* `Real.abs_det_exp_mul_le`: if `|l i * ξ j| ≤ b` for all `i, j`, then
  `|det (exp (l i * ξ j))| ≤ L! * exp (e * L * b - L * (L - 1) / 2)`.

## References

* M. Waldschmidt, *The six exponentials theorem*, Resonance (June 2021), Lemmas 2 and 3.
-/

open Finset Equiv

namespace Matrix

/-- A finite set of natural numbers with `k` elements has sum at least `k * (k - 1) / 2`;
we state it without division. -/
private lemma card_mul_card_sub_one_le_two_mul_sum (S : Finset ℕ) :
    S.card * (S.card - 1) ≤ 2 * ∑ x ∈ S, x := by
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert a S hlt ih =>
    have haS : a ∉ S := fun h => lt_irrefl a (hlt a h)
    have hcard : S.card ≤ a := by
      simpa using card_le_card (show S ⊆ range a from fun x hx => mem_range.2 (hlt x hx))
    rw [card_insert_of_notMem haS, sum_insert haS, Nat.add_sub_cancel]
    rcases Nat.eq_zero_or_pos S.card with h0 | hpos
    · rw [h0]
      exact Nat.zero_le _
    · obtain ⟨d, hd⟩ : ∃ d, S.card = d + 1 := ⟨S.card - 1, by omega⟩
      rw [hd, Nat.add_sub_cancel] at ih
      rw [hd] at hcard ⊢
      nlinarith

/-- If `k : Fin L → ℕ` is injective, then `L * (L - 1) / 2 ≤ ∑ i, k i`. -/
private lemma div_two_le_sum_of_injective {L : ℕ} {k : Fin L → ℕ} (hk : Function.Injective k) :
    L * (L - 1) / 2 ≤ ∑ i, k i := by
  have h := card_mul_card_sub_one_le_two_mul_sum (univ.image k)
  rw [card_image_of_injective _ hk, card_univ, Fintype.card_fin,
    sum_image fun i _ j _ hij => hk hij] at h
  generalize L * (L - 1) = t at *
  omega

/-- The inner alternating sum in Lemma 2: for an exponent vector `k` with
`∑ i, k i < L * (L - 1) / 2`, `∑ σ, sign σ * ∏ i, ξ (σ i) ^ k i = 0`. -/
private lemma sum_perm_sign_mul_prod_pow_eq_zero {R : Type*} [CommRing R] {L : ℕ}
    (ξ : Fin L → R) (k : Fin L → ℕ) (hk : ∑ i, k i < L * (L - 1) / 2) :
    ∑ σ : Perm (Fin L), (Perm.sign σ : R) * ∏ i, ξ (σ i) ^ k i = 0 := by
  have hdet : (Matrix.of fun a b => ξ a ^ k b).det =
      ∑ σ : Perm (Fin L), (Perm.sign σ : R) * ∏ i, ξ (σ i) ^ k i := by
    rw [det_apply]
    refine sum_congr rfl fun σ _ => ?_
    rw [Units.smul_def, zsmul_eq_mul]
    rfl
  rw [← hdet]
  by_cases hinj : Function.Injective k
  · exact absurd (div_two_le_sum_of_injective hinj) (not_le.2 hk)
  · simp only [Function.Injective, not_forall] at hinj
    obtain ⟨i, j, hij, hne⟩ := hinj
    exact det_zero_of_column_eq hne fun a => by simp [hij]

/-- **Waldschmidt, Lemma 2** (algebraic form). For `m < L * (L - 1) / 2`,
`∑ σ, sign σ * (∑ i, l i * ξ (σ i)) ^ m = 0`. This says that the Taylor coefficients of order
`< L * (L - 1) / 2` at the origin of `x ↦ det (exp (l i * ξ j * x))` vanish. -/
theorem sum_perm_sign_mul_sum_pow_eq_zero {R : Type*} [CommRing R] {L : ℕ}
    (l ξ : Fin L → R) {m : ℕ} (hm : m < L * (L - 1) / 2) :
    ∑ σ : Equiv.Perm (Fin L), (Equiv.Perm.sign σ : R) * (∑ i, l i * ξ (σ i)) ^ m = 0 := by
  simp_rw [sum_pow_eq_sum_piAntidiag, mul_sum]
  rw [sum_comm]
  refine sum_eq_zero fun k hk => ?_
  have hks : ∑ i, k i = m := (mem_piAntidiag.1 hk).1
  have h0 := sum_perm_sign_mul_prod_pow_eq_zero ξ k (hks ▸ hm)
  calc ∑ σ : Perm (Fin L), (Perm.sign σ : R) *
        ((Nat.multinomial univ k : R) * ∏ i, (l i * ξ (σ i)) ^ k i)
      = ((Nat.multinomial univ k : R) * ∏ i, l i ^ k i) *
          ∑ σ : Perm (Fin L), (Perm.sign σ : R) * ∏ i, ξ (σ i) ^ k i := by
        rw [mul_sum]
        refine sum_congr rfl fun σ _ => ?_
        simp_rw [mul_pow, prod_mul_distrib]
        ring
    _ = 0 := by rw [h0, mul_zero]

end Matrix

namespace Real

/-- **Waldschmidt, Lemma 3.** If `∑ j ∈ s, a j * w j ^ m = 0` for all `m < M` (i.e. the Taylor
coefficients of order `< M` at the origin of `x ↦ ∑ j ∈ s, a j * exp (w j * x)` vanish), then
for every `R ≥ 1`, `|∑ j ∈ s, a j * exp (w j)| ≤ (∑ j ∈ s, |a j| * exp (R * |w j|)) / R ^ M`. -/
theorem abs_sum_mul_exp_le_of_sum_mul_pow_eq_zero {ι : Type*} (s : Finset ι)
    (a w : ι → ℝ) (M : ℕ) (h : ∀ m < M, ∑ j ∈ s, a j * w j ^ m = 0) {R : ℝ} (hR : 1 ≤ R) :
    |∑ j ∈ s, a j * Real.exp (w j)| ≤ (∑ j ∈ s, |a j| * Real.exp (R * |w j|)) / R ^ M := by
  have hexp (x : ℝ) : HasSum (fun n => x ^ n / n.factorial) (exp x) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp x
  have h1 : HasSum (fun n => ∑ j ∈ s, a j * (w j ^ n / n.factorial))
      (∑ j ∈ s, a j * exp (w j)) :=
    hasSum_sum fun j _ => (hexp (w j)).mul_left (a j)
  have h2 : HasSum (fun n => (∑ j ∈ s, |a j| * ((R * |w j|) ^ n / n.factorial)) / R ^ M)
      ((∑ j ∈ s, |a j| * exp (R * |w j|)) / R ^ M) :=
    (hasSum_sum fun j _ => (hexp (R * |w j|)).mul_left |a j|).div_const (R ^ M)
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  refine h1.norm_le_of_bounded h2 fun n => ?_
  rw [Real.norm_eq_abs]
  rcases lt_or_ge n M with hn | hn
  · have h0 : ∑ j ∈ s, a j * (w j ^ n / n.factorial) = 0 := by
      simp_rw [mul_div_assoc']
      rw [← sum_div, h n hn, zero_div]
    rw [h0, abs_zero]
    positivity
  · have hRn : R ^ M ≤ R ^ n := pow_le_pow_right₀ hR hn
    calc |∑ j ∈ s, a j * (w j ^ n / n.factorial)|
        ≤ ∑ j ∈ s, |a j| * (|w j| ^ n / n.factorial) :=
          (abs_sum_le_sum_abs _ _).trans_eq (sum_congr rfl fun j _ => by
            rw [abs_mul, abs_div, abs_pow, Nat.abs_cast])
      _ ≤ (∑ j ∈ s, |a j| * ((R * |w j|) ^ n / n.factorial)) / R ^ M := by
          rw [le_div_iff₀ (pow_pos hR0 M), sum_mul]
          refine sum_le_sum fun j _ => ?_
          calc |a j| * (|w j| ^ n / n.factorial) * R ^ M
              ≤ |a j| * (|w j| ^ n / n.factorial) * R ^ n := by gcongr
            _ = |a j| * ((R * |w j|) ^ n / n.factorial) := by ring

/-- The interpolation determinant bound used in the six exponentials theorem (`R = e` in
Waldschmidt's Lemma 3): if `|l i * ξ j| ≤ b` for all `i, j`, then
`|det (exp (l i * ξ j))| ≤ L! * exp (e * (L * b) - L * (L - 1) / 2)`. -/
theorem abs_det_exp_mul_le {L : ℕ} (l ξ : Fin L → ℝ) {b : ℝ}
    (hb : ∀ i j, |l i * ξ j| ≤ b) :
    |(Matrix.of fun i j => Real.exp (l i * ξ j)).det| ≤
      L.factorial * Real.exp (Real.exp 1 * (L * b) - ((L * (L - 1) / 2 : ℕ) : ℝ)) := by
  set M := L * (L - 1) / 2
  have hdet : (Matrix.of fun i j => exp (l i * ξ j)).det =
      ∑ σ : Perm (Fin L), (Perm.sign σ : ℝ) * exp (∑ i, l i * ξ (σ i)) := by
    rw [← Matrix.det_transpose, Matrix.det_apply]
    refine sum_congr rfl fun σ _ => ?_
    rw [Units.smul_def, zsmul_eq_mul, Real.exp_sum]
    rfl
  have hw : ∀ σ : Perm (Fin L), |∑ i, l i * ξ (σ i)| ≤ L * b := fun σ =>
    (abs_sum_le_sum_abs _ _).trans <| (sum_le_sum fun i _ => hb i (σ i)).trans_eq (by simp)
  rw [hdet]
  refine (abs_sum_mul_exp_le_of_sum_mul_pow_eq_zero univ (fun σ => (Perm.sign σ : ℝ))
    (fun σ => ∑ i, l i * ξ (σ i)) M
    (fun m hm => Matrix.sum_perm_sign_mul_sum_pow_eq_zero l ξ hm)
    (one_le_exp zero_le_one)).trans ?_
  rw [exp_one_pow, div_le_iff₀ (exp_pos _), mul_assoc, ← exp_add, sub_add_cancel]
  calc ∑ σ : Perm (Fin L), |(Perm.sign σ : ℝ)| * exp (exp 1 * |∑ i, l i * ξ (σ i)|)
      ≤ ∑ _σ : Perm (Fin L), exp (exp 1 * (L * b)) :=
        sum_le_sum fun σ _ => by
          rw [abs_unit_intCast, one_mul]
          gcongr
          exact hw σ
    _ = L.factorial * exp (exp 1 * (L * b)) := by
        rw [sum_const, card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]

end Real
