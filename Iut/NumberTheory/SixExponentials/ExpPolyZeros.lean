/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib

/-!
# Real zeros of exponential polynomials

We show that a real exponential polynomial `x ↦ ∑ i ∈ s, a i * exp (w i * x)` with pairwise
distinct real frequencies `w i` and not all coefficients zero has fewer than `s.card` real zeros.

## Main results

* `exists_finset_deriv_eq_zero_of_eq_zero`: a counting form of Rolle's theorem. If a continuous
  function `f : ℝ → ℝ` vanishes on a finite set `Z`, then `deriv f` vanishes on a finite set `Z'`
  with `Z.card ≤ Z'.card + 1`.
* `Real.card_zeros_sum_mul_exp_lt`: an exponential polynomial with `n` distinct real frequencies,
  not identically zero, has at most `n - 1` real zeros.

## References

* M. Waldschmidt, *The six exponentials theorem*, Resonance (June 2021), Lemma 1.
  The proof follows the one given there: induction on the number of terms, multiplying by
  `exp (- w k * x)` and differentiating, combined with Rolle's theorem.
-/

open Finset

/-- A counting form of Rolle's theorem: if a continuous function `f : ℝ → ℝ` vanishes on a finite
set `Z`, then there is a finite set `Z'` on which `deriv f` vanishes, with
`Z.card ≤ Z'.card + 1`, and each point of `Z'` lies strictly below some point of `Z`. -/
theorem exists_finset_deriv_eq_zero_of_eq_zero {f : ℝ → ℝ} (hf : Continuous f) (Z : Finset ℝ)
    (hZ : ∀ x ∈ Z, f x = 0) :
    ∃ Z' : Finset ℝ, Z.card ≤ Z'.card + 1 ∧ (∀ x ∈ Z', deriv f x = 0) ∧
      ∀ x ∈ Z', ∃ y ∈ Z, x < y := by
  induction Z using Finset.induction_on_max with
  | empty => exact ⟨∅, by simp, by simp, by simp⟩
  | insert a S hlt ih =>
    obtain ⟨Z', hcard, hder, hlt'⟩ := ih fun x hx => hZ x (mem_insert_of_mem hx)
    have haS : a ∉ S := fun h => lt_irrefl a (hlt a h)
    rcases S.eq_empty_or_nonempty with rfl | hne
    · exact ⟨∅, by simp, by simp, by simp⟩
    · have hb : S.max' hne ∈ S := S.max'_mem hne
      obtain ⟨c, hc, hdc⟩ := exists_deriv_eq_zero (hlt _ hb) hf.continuousOn
        ((hZ _ (mem_insert_of_mem hb)).trans (hZ a (mem_insert_self a S)).symm)
      have hcZ' : c ∉ Z' := fun h => by
        obtain ⟨y, hy, hcy⟩ := hlt' c h
        exact lt_irrefl _ ((hc.1.trans hcy).trans_le (S.le_max' y hy))
      refine ⟨insert c Z', ?_, ?_, ?_⟩
      · rw [card_insert_of_notMem haS, card_insert_of_notMem hcZ']
        omega
      · intro x hx
        rcases mem_insert.1 hx with rfl | hx
        exacts [hdc, hder x hx]
      · intro x hx
        rcases mem_insert.1 hx with rfl | hx
        · exact ⟨a, mem_insert_self a S, hc.2⟩
        · obtain ⟨y, hy, hxy⟩ := hlt' x hx
          exact ⟨y, mem_insert_of_mem hy, hxy⟩

namespace Real

/-- The derivative of `x ↦ a * exp (c * x)`. -/
private lemma hasDerivAt_const_mul_exp_mul (a c x : ℝ) :
    HasDerivAt (fun y => a * exp (c * y)) (a * c * exp (c * x)) x := by
  have := (((hasDerivAt_id x).const_mul c).exp).const_mul a
  simp only [id, mul_one] at this
  exact this.congr_deriv (by ring)

/-- **Waldschmidt, Lemma 1.** Let `w i` (`i ∈ s`) be pairwise distinct real numbers and `a i`
real numbers, not all zero. Then the function `x ↦ ∑ i ∈ s, a i * exp (w i * x)` has fewer than
`s.card` real zeros. -/
theorem card_zeros_sum_mul_exp_lt {ι : Type*} (s : Finset ι) (w a : ι → ℝ)
    (hw : Set.InjOn w s) (ha : ∃ i ∈ s, a i ≠ 0) (Z : Finset ℝ)
    (hZ : ∀ x ∈ Z, ∑ i ∈ s, a i * Real.exp (w i * x) = 0) : Z.card < s.card := by
  classical
  obtain ⟨n, hn⟩ : ∃ n, s.card = n := ⟨_, rfl⟩
  induction n generalizing s w a Z with
  | zero =>
    obtain ⟨i, hi, -⟩ := ha
    simp [card_eq_zero.1 hn] at hi
  | succ n ih =>
    obtain ⟨k, hk, hak⟩ := ha
    by_cases hall : ∀ i ∈ s.erase k, a i = 0
    · -- Only the term `k` survives, and it does not vanish.
      have hZe : Z = ∅ := by
        refine eq_empty_of_forall_notMem fun x hx => ?_
        have h := hZ x hx
        rw [sum_eq_single_of_mem k hk fun i hi hik => by
          rw [hall i (mem_erase.2 ⟨hik, hi⟩), zero_mul]] at h
        exact mul_ne_zero hak (exp_pos _).ne' h
      rw [hZe, card_empty, hn]
      exact Nat.succ_pos n
    · push Not at hall
      obtain ⟨j, hj, haj⟩ := hall
      -- `g x = exp (-(w k * x)) * F x`.
      set g : ℝ → ℝ := fun x => ∑ i ∈ s, a i * exp ((w i - w k) * x) with hg
      have hgZ : ∀ x ∈ Z, g x = 0 := by
        intro x hx
        have : g x = exp (-(w k * x)) * ∑ i ∈ s, a i * exp (w i * x) := by
          rw [hg, mul_sum]
          refine sum_congr rfl fun i _ => ?_
          rw [sub_mul, sub_eq_add_neg, exp_add]
          ring
        rw [this, hZ x hx, mul_zero]
      have hgd : ∀ x, HasDerivAt g (∑ i ∈ s, a i * (w i - w k) * exp ((w i - w k) * x)) x :=
        fun x => HasDerivAt.fun_sum fun i _ => hasDerivAt_const_mul_exp_mul (a i) (w i - w k) x
      have hgc : Continuous g :=
        continuous_iff_continuousAt.2 fun x => (hgd x).continuousAt
      obtain ⟨Z', hcard, hder, -⟩ := exists_finset_deriv_eq_zero_of_eq_zero hgc Z hgZ
      have hZ' : ∀ x ∈ Z', ∑ i ∈ s.erase k,
          a i * (w i - w k) * exp ((w i - w k) * x) = 0 := by
        intro x hx
        rw [sum_erase _ (by simp), ← (hgd x).deriv]
        exact hder x hx
      have hjk : j ≠ k := (mem_erase.1 hj).1
      have hlt := ih (s.erase k) (fun i => w i - w k) (fun i => a i * (w i - w k))
        (fun i hi i' hi' h => hw (mem_of_mem_erase hi) (mem_of_mem_erase hi')
          (sub_left_injective h))
        ⟨j, hj, mul_ne_zero haj (sub_ne_zero.2 fun h =>
          hjk (hw (mem_of_mem_erase hj) hk h))⟩ Z' hZ'
        (by rw [card_erase_of_mem hk, hn, Nat.add_sub_cancel])
      rw [card_erase_of_mem hk, hn, Nat.add_sub_cancel] at hlt
      omega

end Real
