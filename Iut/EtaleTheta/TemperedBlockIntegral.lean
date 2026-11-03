/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib

/-!
# Integrality of block coordinates via valuations

Let `Ω` be a field and `A` a ring with an algebra structure `A → Ω`. Suppose points
`(x k, y k)`, `k : ι` (a finite index type), lie on the Weierstrass cubic
`y ^ 2 + x * y = x ^ 3 + a₄ * x + a₆` with `a₄ a₆ : A`, suppose that for every pair `k ≠ k'`
the points satisfy a bilinear relation in `(1, x k, y k)` and `(1, x k', y k')` with coefficients
in `A` whose `y y'` coefficient is one, and suppose that `∑ k, x k` is integral over `A`.
Then all `x k` and `y k` are integral over `A`.

The proof runs through the valuation subrings of `Ω` containing the integral closure of `A`
(`Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn`): for such a valuation `v`,
the cubic forces `v x < v y` whenever `1 < v x`, the pair relation then rules out two indices
with `1 < v x`, and a single such index would give `1 < v (∑ k, x k)`.
-/

namespace Iut.EtaleTheta

open Finset

section Valuation

variable {Ω Γ₀ : Type*} [Field Ω] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation Ω Γ₀)

/-- On the cubic `y ^ 2 + x y = x ^ 3 + a x + b` with `v a, v b ≤ 1`, a pole of `x` forces
`v x < v y`. -/
theorem val_lt_of_weierstrass {x y a b : Ω} (ha : v a ≤ 1) (hb : v b ≤ 1)
    (h : y ^ 2 + x * y = x ^ 3 + a * x + b) (hx : 1 < v x) : v x < v y := by
  by_contra hyx
  push Not at hyx
  have hx0 : 0 < v x := zero_lt_one.trans hx
  have hL : v (y ^ 2 + x * y) ≤ v x * v x := by
    refine v.map_add_le ?_ ?_
    · rw [map_pow, sq]; exact mul_le_mul' hyx hyx
    · rw [map_mul]; exact mul_le_mul' le_rfl hyx
  have hax : v (a * x + b) < v x ^ 3 := by
    have h1 : v x < v x ^ 3 := by
      calc v x = 1 * 1 * v x := by simp
        _ < v x * v x * v x := by
          apply mul_lt_mul_of_pos_right _ hx0
          exact mul_lt_mul'' hx hx zero_le_one zero_le_one
        _ = v x ^ 3 := (pow_three' _).symm
    refine v.map_add_lt ?_ ?_
    · rw [map_mul]
      exact lt_of_le_of_lt (by simpa using mul_le_mul' ha (le_refl (v x))) h1
    · exact lt_of_le_of_lt hb (hx.trans h1)
  have hR : v (x ^ 3 + a * x + b) = v x ^ 3 := by
    rw [add_assoc, v.map_add_eq_of_lt_left (by rwa [map_pow])]
    simp
  have : v x ^ 3 ≤ v x * v x := by rw [← hR, ← h]; exact hL
  have h2 : v x * v x < v x ^ 3 := by
    calc v x * v x = v x * v x * 1 := by simp
      _ < v x * v x * v x := mul_lt_mul_of_pos_left hx (mul_pos hx0 hx0)
      _ = v x ^ 3 := (pow_three' _).symm
  exact absurd this (not_le.mpr h2)

/-- On the cubic `y ^ 2 + x y = x ^ 3 + a x + b` with `v a, v b ≤ 1`, if `v x ≤ 1` then
`v y ≤ 1`. -/
theorem val_le_one_of_weierstrass {x y a b : Ω} (ha : v a ≤ 1) (hb : v b ≤ 1)
    (h : y ^ 2 + x * y = x ^ 3 + a * x + b) (hx : v x ≤ 1) : v y ≤ 1 := by
  by_contra hy
  push Not at hy
  have hy0 : 0 < v y := zero_lt_one.trans hy
  have hR : v (x ^ 3 + a * x + b) ≤ 1 := by
    refine v.map_add_le (v.map_add_le ?_ ?_) hb
    · rw [map_pow]; exact pow_le_one₀ zero_le hx
    · rw [map_mul]; exact mul_le_one' ha hx
  have hxy : v (x * y) < v (y ^ 2) := by
    rw [map_mul, map_pow, sq]
    exact mul_lt_mul_of_pos_right (hx.trans_lt hy) hy0
  have hL : v (y ^ 2 + x * y) = v y * v y := by
    rw [v.map_add_eq_of_lt_left hxy, map_pow, sq]
  have h1 : 1 < v y * v y := by
    calc (1 : Γ₀) = 1 * 1 := by simp
      _ < v y * v y := mul_lt_mul'' hy hy zero_le_one zero_le_one
  have : v y * v y ≤ 1 := by rw [← hL, h]; exact hR
  exact absurd this (not_le.mpr h1)

/-- Two poles `1 < v x < v y`, `1 < v x' < v y'` cannot satisfy a bilinear relation in
`(1, x, y)`, `(1, x', y')` with coefficients of valuation `≤ 1` and `y y'` coefficient one: the
monomial `y y'` has strictly the largest valuation. -/
theorem val_false_of_pair {x y x' y' : Ω} (c : Fin 3 → Fin 3 → Ω) (hc : ∀ a b, v (c a b) ≤ 1)
    (hc22 : c 2 2 = 1) (hx : 1 < v x) (hxy : v x < v y) (hx' : 1 < v x') (hxy' : v x' < v y')
    (h : ∑ a, ∑ b, c a b * ![1, x, y] a * ![1, x', y'] b = 0) : False := by
  have hy : 1 < v y := hx.trans hxy
  have hy' : 1 < v y' := hx'.trans hxy'
  have hy0 : 0 < v y := zero_lt_one.trans hy
  have hy0' : 0 < v y' := zero_lt_one.trans hy'
  have hcm : ∀ a b m, v m < v y * v y' → v (c a b * m) < v y * v y' := fun a b m hm => by
    rw [map_mul]
    exact lt_of_le_of_lt (by simpa using mul_le_mul' (hc a b) (le_refl (v m))) hm
  have hYg : v y < v y * v y' := by
    calc v y = v y * 1 := (mul_one _).symm
      _ < v y * v y' := mul_lt_mul_of_pos_left hy' hy0
  have hY'g : v y' < v y * v y' := by
    calc v y' = 1 * v y' := (one_mul _).symm
      _ < v y * v y' := mul_lt_mul_of_pos_right hy hy0'
  have h1 : v (1 : Ω) < v y * v y' := by
    rw [map_one]
    calc (1 : Γ₀) = 1 * 1 := (one_mul _).symm
      _ < v y * v y' := mul_lt_mul'' hy hy' zero_le zero_le
  have hxx : v (x * x') < v y * v y' := by
    rw [map_mul]; exact mul_lt_mul'' hxy hxy' zero_le zero_le
  have hxy'' : v (x * y') < v y * v y' := by
    rw [map_mul]; exact mul_lt_mul_of_pos_right hxy hy0'
  have hyx : v (y * x') < v y * v y' := by
    rw [map_mul]; exact mul_lt_mul_of_pos_left hxy' hy0
  have e : ∑ a, ∑ b, c a b * ![1, x, y] a * ![1, x', y'] b = y * y' +
      (c 0 0 * 1 + c 0 1 * x' + c 0 2 * y' + c 1 0 * x + c 1 1 * (x * x') + c 1 2 * (x * y') +
        c 2 0 * y + c 2 1 * (y * x')) := by
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, hc22]
    ring
  have hR : v (c 0 0 * 1 + c 0 1 * x' + c 0 2 * y' + c 1 0 * x + c 1 1 * (x * x') +
      c 1 2 * (x * y') + c 2 0 * y + c 2 1 * (y * x')) < v y * v y' := by
    refine v.map_add_lt (v.map_add_lt (v.map_add_lt (v.map_add_lt (v.map_add_lt (v.map_add_lt
      (v.map_add_lt (hcm _ _ _ h1) (hcm _ _ _ (hxy'.trans hY'g))) (hcm _ _ _ hY'g))
      (hcm _ _ _ (hxy.trans hYg))) (hcm _ _ _ hxx)) (hcm _ _ _ hxy'')) (hcm _ _ _ hYg))
      (hcm _ _ _ hyx)
  rw [e, add_eq_zero_iff_eq_neg] at h
  have := congrArg v h
  rw [map_mul, v.map_neg] at this
  exact absurd (this ▸ hR) (lt_irrefl _)

end Valuation

section Blocks

variable {Ω : Type*} [Field Ω]

/-- **Block coordinates in a valuation subring.** Points `(x k, y k)` of the cubic
`y ^ 2 + x y = x ^ 3 + a₄ x + a₆` (`a₄, a₆ ∈ V`), pairwise satisfying bilinear relations with
coefficients in `V` and `y y'` coefficient one, with `∑ k, x k ∈ V`, have all coordinates in `V`. -/
theorem mem_of_blocks {ι : Type*} [Fintype ι] (V : ValuationSubring Ω)
    (x y : ι → Ω) {a₄ a₆ : Ω} (ha₄ : a₄ ∈ V) (ha₆ : a₆ ∈ V)
    (hcub : ∀ k, y k ^ 2 + x k * y k = x k ^ 3 + a₄ * x k + a₆) (hsum : ∑ k, x k ∈ V)
    (hpair : ∀ k k', k ≠ k' → ∃ c : Fin 3 → Fin 3 → Ω, (∀ a b, c a b ∈ V) ∧ c 2 2 = 1 ∧
      ∑ a, ∑ b, c a b * ![1, x k, y k] a * ![1, x k', y k'] b = 0) :
    ∀ k, x k ∈ V ∧ y k ∈ V := by
  classical
  set v := V.valuation
  have ha₄' : v a₄ ≤ 1 := (V.valuation_le_one_iff _).2 ha₄
  have ha₆' : v a₆ ≤ 1 := (V.valuation_le_one_iff _).2 ha₆
  have hx : ∀ k, v (x k) ≤ 1 := by
    by_contra hne
    push Not at hne
    obtain ⟨k, hk⟩ := hne
    have hj : ∀ j ∈ Finset.univ.erase k, v (x j) ≤ 1 := by
      intro j hj
      by_contra hj'
      push Not at hj'
      obtain ⟨c, hcV, hc22, hc⟩ := hpair k j (Finset.ne_of_mem_erase hj).symm
      exact val_false_of_pair v c (fun a b => (V.valuation_le_one_iff _).2 (hcV a b)) hc22 hk
        (val_lt_of_weierstrass v ha₄' ha₆' (hcub k) hk) hj'
        (val_lt_of_weierstrass v ha₄' ha₆' (hcub j) hj') hc
    have hrest : v (∑ j ∈ Finset.univ.erase k, x j) < v (x k) :=
      lt_of_le_of_lt (v.map_sum_le hj) hk
    have hs : v (∑ j, x j) = v (x k) := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k), v.map_add_eq_of_lt_left hrest]
    exact absurd ((V.valuation_le_one_iff _).2 hsum) (by rw [hs]; exact not_le.mpr hk)
  intro k
  exact ⟨(V.valuation_le_one_iff _).1 (hx k),
    (V.valuation_le_one_iff _).1 (val_le_one_of_weierstrass v ha₄' ha₆' (hcub k) (hx k))⟩

/-- **Integrality of block coordinates** (general finite index type): see `isIntegral_blocks`. -/
theorem isIntegral_blocks_of_fintype {A : Type*} [CommRing A] [Algebra A Ω] {ι : Type*}
    [Fintype ι] (x y : ι → Ω) (a₄ a₆ : A)
    (hcub : ∀ k, y k ^ 2 + x k * y k =
      x k ^ 3 + algebraMap A Ω a₄ * x k + algebraMap A Ω a₆)
    (hsum : IsIntegral A (∑ k, x k))
    (hpair : ∀ k k', k ≠ k' → ∃ c : Fin 3 → Fin 3 → A, c 2 2 = 1 ∧
      ∑ a, ∑ b, algebraMap A Ω (c a b) * ![1, x k, y k] a * ![1, x k', y k'] b = 0) :
    ∀ k, IsIntegral A (x k) ∧ IsIntegral A (y k) := by
  have key : ∀ V : ValuationSubring Ω, (integralClosure A Ω).toSubring ≤ V.toSubring →
      ∀ k, x k ∈ V ∧ y k ∈ V := by
    intro V hV
    have hA : ∀ a : A, algebraMap A Ω a ∈ V := fun a =>
      hV (show algebraMap A Ω a ∈ integralClosure A Ω from isIntegral_algebraMap)
    refine mem_of_blocks V x y (hA a₄) (hA a₆) hcub (hV hsum) fun k k' hkk' => ?_
    obtain ⟨c, hc22, hc⟩ := hpair k k' hkk'
    exact ⟨fun a b => algebraMap A Ω (c a b), fun a b => hA _,
      show algebraMap A Ω (c 2 2) = 1 by rw [hc22, map_one], hc⟩
  have hmem : ∀ z : Ω, (∀ V : ValuationSubring Ω, (integralClosure A Ω).toSubring ≤ V.toSubring →
      z ∈ V) → IsIntegral A z := by
    intro z hz
    by_contra hnot
    obtain ⟨V, hV, hzV⟩ := Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn
      (R := (integralClosure A Ω).toSubring) (x := z) hnot
    exact hzV (hz V hV)
  intro k
  exact ⟨hmem _ fun V hV => (key V hV k).1, hmem _ fun V hV => (key V hV k).2⟩

/-- **Integrality of block coordinates.** Let `(x k, y k)`, `k : ZMod n`, be points of
`y ^ 2 + x y = x ^ 3 + a₄ x + a₆` (`a₄ a₆ : A`) in a field `Ω` such that every pair `k ≠ k'`
satisfies a bilinear relation in `(1, x k, y k)`, `(1, x k', y k')` with coefficients in `A` and
`y y'` coefficient one. If `∑ k, x k` is integral over `A`, then so are all `x k` and `y k`. -/
theorem isIntegral_blocks {A : Type*} [CommRing A] [Algebra A Ω] {n : ℕ} [NeZero n]
    (x y : ZMod n → Ω) (a₄ a₆ : A)
    (hcub : ∀ k, y k ^ 2 + x k * y k =
      x k ^ 3 + algebraMap A Ω a₄ * x k + algebraMap A Ω a₆)
    (hsum : IsIntegral A (∑ k, x k))
    (hpair : ∀ k k', k ≠ k' → ∃ c : Fin 3 → Fin 3 → A, c 2 2 = 1 ∧
      ∑ a, ∑ b, algebraMap A Ω (c a b) * ![1, x k, y k] a * ![1, x k', y k'] b = 0) :
    ∀ k, IsIntegral A (x k) ∧ IsIntegral A (y k) :=
  isIntegral_blocks_of_fintype x y a₄ a₆ hcub hsum hpair

end Blocks

end Iut.EtaleTheta
