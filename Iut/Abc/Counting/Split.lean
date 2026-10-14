/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.GCD.BigOperators

/-!
# The `T`-split of a `k`-full discriminant

Let `n = |Δ_min(E)|` and `k ≥ 1`. Write `e_p = v_p(n)`. Call `n` *`k`-full off `6`* if
`e_p ≥ k` for every prime `p ∤ 6` dividing `n`. The proof of Theorem V6 (LANA note `V6.md`, §3)
splits the primes `p ∤ 6` of `n` into those with `k ∣ e_p` and the *`T`-primes* with `k ∤ e_p`,
and puts `T = ∏ (T-primes)`. This file proves the elementary facts about this split.

## Main definitions

* `Iut.Abc.Counting.rad6 n`: the product of the primes `p ∤ 6` dividing `n`, i.e. the radical of
  the prime-to-`6` part `Δ′` of `n`.
* `Iut.Abc.Counting.tPart k n`: the product `T` of the primes `p ∤ 6` with `p ∣ n`, `k ∤ e_p`.
* `Iut.Abc.Counting.KFullOffSix k n`: `e_p ≥ k` for every prime `p ∤ 6` dividing `n`.

## Main results

* `rad6_pow_mul_tPart_le`: if `n ≠ 0` is `k`-full off `6`, then `rad6 n ^ k * tPart k n ≤ n`
  (a `T`-prime has `e_p ≥ k + 1`, every other prime `p ∤ 6` has `e_p ≥ k`).
* `tPart_squarefree`, `tPart_coprime_six`, `tPart_pos`: `T` is squarefree, prime to `6`, positive.
* `dvd_factorization_of_not_dvd_six_mul_tPart`: `k ∣ e_p` for every prime `p ∤ 6 T`; this puts
  the curve into the family `𝒞_k(T)` of the uniform bound (Prop S3.2).
-/

namespace Iut.Abc.Counting

open Finset

/-- The primes `p ∤ 6` dividing `n`. -/
def primesOffSix (n : ℕ) : Finset ℕ := n.primeFactors.filter (fun p => ¬ p ∣ 6)

/-- The radical of the prime-to-`6` part of `n`: the product of the primes `p ∤ 6`, `p ∣ n`. -/
def rad6 (n : ℕ) : ℕ := ∏ p ∈ primesOffSix n, p

/-- The `T`-primes of `n` at level `k`: the primes `p ∤ 6` dividing `n` with `k ∤ v_p(n)`. -/
def tPrimes (k n : ℕ) : Finset ℕ := (primesOffSix n).filter (fun p => ¬ k ∣ n.factorization p)

/-- `T = tPart k n`, the product of the `T`-primes of `n` at level `k`. -/
def tPart (k n : ℕ) : ℕ := ∏ p ∈ tPrimes k n, p

/-- `n` is `k`-full off `6`: every prime `p ∤ 6` dividing `n` divides it at least `k` times. -/
def KFullOffSix (k n : ℕ) : Prop := ∀ p ∈ primesOffSix n, k ≤ n.factorization p

theorem mem_primesOffSix {n p : ℕ} :
    p ∈ primesOffSix n ↔ p.Prime ∧ p ∣ n ∧ n ≠ 0 ∧ ¬ p ∣ 6 := by
  simp [primesOffSix, and_assoc]

theorem prime_of_mem_primesOffSix {n p : ℕ} (hp : p ∈ primesOffSix n) : p.Prime :=
  (mem_primesOffSix.mp hp).1

theorem tPrimes_subset (k n : ℕ) : tPrimes k n ⊆ primesOffSix n := filter_subset _ _

theorem prime_of_mem_tPrimes {k n p : ℕ} (hp : p ∈ tPrimes k n) : p.Prime :=
  prime_of_mem_primesOffSix (tPrimes_subset k n hp)

theorem rad6_pos (n : ℕ) : 0 < rad6 n :=
  prod_pos fun _ hp => (prime_of_mem_primesOffSix hp).pos

theorem tPart_pos (k n : ℕ) : 0 < tPart k n :=
  prod_pos fun _ hp => (prime_of_mem_tPrimes hp).pos

/-- The split inequality `rad(Δ′) ^ k · T ≤ |Δ|` of `V6.md` §3, step 1. -/
theorem rad6_pow_mul_tPart_le {k n : ℕ} (hn : n ≠ 0) (hk : KFullOffSix k n) :
    rad6 n ^ k * tPart k n ≤ n := by
  have key : rad6 n ^ k * tPart k n =
      ∏ p ∈ primesOffSix n, p ^ k * (if ¬ k ∣ n.factorization p then p else 1) := by
    rw [rad6, tPart, tPrimes, prod_filter, ← prod_pow, ← prod_mul_distrib]
  rw [key]
  calc _ ≤ ∏ p ∈ primesOffSix n, p ^ n.factorization p := by
        apply prod_le_prod'
        intro p hp
        have hp1 : 0 < p := (prime_of_mem_primesOffSix hp).pos
        have hkp := hk p hp
        split_ifs with hdvd
        · rw [mul_one]
          exact Nat.pow_le_pow_right hp1 hkp
        · have hne : n.factorization p ≠ k := fun h => hdvd (h ▸ dvd_refl _)
          rw [← pow_succ]
          exact Nat.pow_le_pow_right hp1 (by omega)
    _ ≤ ∏ p ∈ n.primeFactors, p ^ n.factorization p := by
        apply prod_le_prod_of_subset_of_one_le' (filter_subset _ _)
        intro p hp _
        exact Nat.one_le_pow _ _ (Nat.prime_of_mem_primeFactors hp).pos
    _ = n := (Nat.prod_primeFactors_pow_factorization hn).symm

/-- `T` is squarefree. -/
theorem tPart_squarefree (k n : ℕ) : Squarefree (tPart k n) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    exact Nat.coprime_iff_isRelPrime.mp
      ((Nat.coprime_primes (prime_of_mem_tPrimes hp) (prime_of_mem_tPrimes hq)).mpr hpq)
  · intro p hp
    exact (prime_of_mem_tPrimes hp).prime.squarefree

/-- `T` is prime to `6`. -/
theorem tPart_coprime_six (k n : ℕ) : Nat.Coprime (tPart k n) 6 := by
  apply Nat.Coprime.prod_left
  intro p hp
  have hp' := mem_primesOffSix.mp (tPrimes_subset k n hp)
  exact (Nat.Prime.coprime_iff_not_dvd hp'.1).mpr hp'.2.2.2

/-- Every `p ∤ 6 T` (prime or not) has `k ∣ v_p(n)` (trivially if `p ∤ n`). -/
theorem dvd_factorization_of_not_dvd_six_mul_tPart {k n p : ℕ}
    (hpT : ¬ p ∣ 6 * tPart k n) : k ∣ n.factorization p := by
  by_cases hpn : p ∈ n.primeFactors
  · by_contra hk
    have h6 : ¬ p ∣ 6 := fun h => hpT (dvd_mul_of_dvd_left h _)
    have hmem : p ∈ tPrimes k n := by
      simp only [tPrimes, primesOffSix, mem_filter]
      exact ⟨⟨hpn, h6⟩, hk⟩
    exact hpT (dvd_mul_of_dvd_right (dvd_prod_of_mem _ hmem) _)
  · rw [← Nat.support_factorization, Finsupp.notMem_support_iff] at hpn
    rw [hpn]
    exact dvd_zero k

end Iut.Abc.Counting
