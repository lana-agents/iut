/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.NumberTheory.FLT.MasonStothers
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.FieldTheory.Finite.Basic

/-!
# Szpiro's inequality over `k[X]`, and its failure for Frobenius twists

This file proves the polynomial (function-field) analogue of the Szpiro inequality from
Mathlib's Mason–Stothers theorem `Polynomial.abc`, and records, as a theorem, that the
separability (derivative) hypothesis of Mason–Stothers cannot be dropped in characteristic
`p`: Frobenius twists violate every Szpiro-type bound.

## Main results

* `Polynomial.szpiro_six`: let `c₄, c₆ ∈ k[X]` be coprime over a field `k`, with
  `D = c₄ ^ 3 - c₆ ^ 2`, and assume that `c₄ ^ 3`, `c₆ ^ 2`, `D` do not all have zero
  derivative. Then `deg D + 6 ≤ 6 · deg rad D`. In characteristic not `2, 3` the Weierstrass
  model with invariants `c₄, c₆` has discriminant `D / 1728`; coprimality makes it semistable,
  with conductor `rad D`, so this is Szpiro's inequality with exponent `6`.
* `Polynomial.szpiro_six_of_charZero`: the same in characteristic zero, for `D` of positive degree.
* `Polynomial.szpiro_frey`: for coprime `a + b = c` (not all derivatives zero),
  `deg (a b c)² + 6 ≤ 6 · deg rad (a b c)`. Up to the factor `16`, `(a b c)²` is the
  discriminant of the Frey–Legendre curve `y² = x (x - a) (x + b)`.
* `Polynomial.szpiro_fails_charP` (the no-go O1): over `ZMod p`, the Frobenius twists
  `c₄ = X ^ (2 p ^ n)`, `c₆ = 1` have `D = (X ^ 6 - 1) ^ (p ^ n)`, so `deg D = 6 p ^ n` while
  `deg rad D ≤ 6`; for every `C` there is a coprime pair with `C · deg rad D < deg D`, and all
  three derivatives vanish.
* `Polynomial.not_szpiro_six_charP`: consequently the derivative hypothesis cannot be removed
  from `Polynomial.szpiro_six` over `ZMod p`.

This is the classical function-field Szpiro inequality; it says nothing about the arithmetic
Szpiro conjecture over `ℚ`.
-/

open Polynomial UniqueFactorizationMonoid UniqueFactorizationDomain

namespace Polynomial

variable {k : Type*} [Field k] [DecidableEq k]

/-- The degree of the radical of a product is at most the sum of the degrees of the radicals. -/
lemma natDegree_radical_mul_le (a b : k[X]) :
    (radical (a * b)).natDegree ≤ (radical a).natDegree + (radical b).natDegree := by
  have h := natDegree_le_of_dvd (radical_mul_dvd (a := a) (b := b))
    (mul_ne_zero radical_ne_zero radical_ne_zero)
  rwa [natDegree_mul radical_ne_zero radical_ne_zero] at h

omit [DecidableEq k] in
/-- A unit of `k[X]` has zero derivative. -/
lemma derivative_eq_zero_of_isUnit {u : k[X]} (hu : IsUnit u) : derivative u = 0 := by
  rw [eq_C_of_natDegree_eq_zero (natDegree_eq_zero_of_isUnit hu), derivative_C]

/-- Mason–Stothers in the Weierstrass form used below, with `D` an explicit variable. -/
private lemma szpiro_six_aux {c₄ c₆ D : k[X]} (hD : D = c₄ ^ 3 - c₆ ^ 2)
    (hcop : IsCoprime c₄ c₆)
    (hder : ¬ (derivative (c₄ ^ 3) = 0 ∧ derivative (c₆ ^ 2) = 0 ∧ derivative D = 0)) :
    D.natDegree + 6 ≤ 6 * (radical D).natDegree := by
  -- nondegeneracy: a vanishing input forces all derivatives to vanish
  have hc₄ : c₄ ≠ 0 := by
    rintro rfl
    have hu := (isCoprime_zero_left.mp hcop).pow 2
    refine hder ⟨by simp, derivative_eq_zero_of_isUnit hu, ?_⟩
    rw [hD, zero_pow (by norm_num), zero_sub, derivative_neg,
      derivative_eq_zero_of_isUnit hu, neg_zero]
  have hc₆ : c₆ ≠ 0 := by
    rintro rfl
    have hu := (isCoprime_zero_right.mp hcop).pow 3
    refine hder ⟨derivative_eq_zero_of_isUnit hu, by simp, ?_⟩
    rw [hD, zero_pow (by norm_num), sub_zero, derivative_eq_zero_of_isUnit hu]
  have hD0 : D ≠ 0 := by
    intro h0
    have h1 : c₄ ^ 3 = c₆ ^ 2 := sub_eq_zero.mp (hD ▸ h0)
    have hc : IsCoprime (c₄ ^ 3) (c₆ ^ 2) := hcop.pow
    rw [h1] at hc
    have hu := isCoprime_self.mp hc
    exact hder ⟨by rw [h1]; exact derivative_eq_zero_of_isUnit hu, derivative_eq_zero_of_isUnit hu,
      by rw [h0, derivative_zero]⟩
  -- Mason–Stothers for `c₄ ^ 3 + (-c₆ ^ 2) + (-D) = 0`
  have habc := Polynomial.abc (a := c₄ ^ 3) (b := -c₆ ^ 2) (c := -D)
    (pow_ne_zero 3 hc₄) (neg_ne_zero.mpr (pow_ne_zero 2 hc₆)) (neg_ne_zero.mpr hD0)
    (IsCoprime.neg_right (hcop.pow (m := 3) (n := 2))) (by rw [hD]; abel)
  rcases habc with ⟨h₁, h₂, h₃⟩ | ⟨h₁, h₂, h₃⟩
  swap
  · exact absurd ⟨h₁, by simpa using h₂, by simpa using h₃⟩ hder
  -- the radical of `c₄ ^ 3 · (-c₆ ^ 2) · (-D)` has degree at most `deg c₄ + deg c₆ + deg rad D`
  have hR := (natDegree_radical_mul_le (c₄ ^ 3 * -c₆ ^ 2) (-D)).trans
    (Nat.add_le_add_right (natDegree_radical_mul_le (c₄ ^ 3) (-c₆ ^ 2)) _)
  rw [radical_neg, radical_neg, radical_pow _ (by norm_num), radical_pow _ (by norm_num)] at hR
  rw [natDegree_neg] at h₂ h₃
  rw [natDegree_pow] at h₁ h₂
  have h4 := natDegree_radical_le (a := c₄)
  have h6 := natDegree_radical_le (a := c₆)
  have hDdeg : D.natDegree ≤ max (3 * c₄.natDegree) (2 * c₆.natDegree) := by
    rw [hD]
    refine (natDegree_sub_le _ _).trans ?_
    rw [natDegree_pow, natDegree_pow]
  omega

/-- **Szpiro's inequality over `k[X]`** (exponent `6`). For coprime `c₄, c₆` with
`D = c₄ ^ 3 - c₆ ^ 2`, unless `c₄ ^ 3`, `c₆ ^ 2` and `D` all have zero derivative,
`deg D + 6 ≤ 6 · deg rad D`. -/
theorem szpiro_six {c₄ c₆ : k[X]} (hcop : IsCoprime c₄ c₆)
    (hder : ¬ (derivative (c₄ ^ 3) = 0 ∧ derivative (c₆ ^ 2) = 0 ∧
      derivative (c₄ ^ 3 - c₆ ^ 2) = 0)) :
    (c₄ ^ 3 - c₆ ^ 2).natDegree + 6 ≤ 6 * (radical (c₄ ^ 3 - c₆ ^ 2)).natDegree :=
  szpiro_six_aux rfl hcop hder

/-- **Szpiro's inequality over `k[X]` in characteristic zero.** For coprime `c₄, c₆` with
`D = c₄ ^ 3 - c₆ ^ 2` of positive degree, `deg D + 6 ≤ 6 · deg rad D`. -/
theorem szpiro_six_of_charZero [CharZero k] {c₄ c₆ : k[X]} (hcop : IsCoprime c₄ c₆)
    (hD : 0 < (c₄ ^ 3 - c₆ ^ 2).natDegree) :
    (c₄ ^ 3 - c₆ ^ 2).natDegree + 6 ≤ 6 * (radical (c₄ ^ 3 - c₆ ^ 2)).natDegree :=
  szpiro_six hcop fun h ↦ by
    have := derivative_eq_zero.mp h.2.2
    omega

/-- **Szpiro's inequality for the Frey–Legendre family over `k[X]`.** For coprime `a, b` with
`a + b = c`, unless `a`, `b`, `c` all have zero derivative,
`deg (a b c)² + 6 ≤ 6 · deg rad (a b c)`. Up to the factor `16`, `(a b c)²` is the
discriminant of `y² = x (x - a) (x + b)`. -/
theorem szpiro_frey {a b c : k[X]} (hab : IsCoprime a b) (hsum : a + b = c)
    (hder : ¬ (derivative a = 0 ∧ derivative b = 0 ∧ derivative c = 0)) :
    ((a * b * c) ^ 2).natDegree + 6 ≤ 6 * (radical (a * b * c)).natDegree := by
  subst hsum
  have ha : a ≠ 0 := by
    rintro rfl
    have hu := isCoprime_zero_left.mp hab
    exact hder ⟨derivative_zero, derivative_eq_zero_of_isUnit hu,
      by rw [zero_add]; exact derivative_eq_zero_of_isUnit hu⟩
  have hb : b ≠ 0 := by
    rintro rfl
    have hu := isCoprime_zero_right.mp hab
    exact hder ⟨derivative_eq_zero_of_isUnit hu, derivative_zero,
      by rw [add_zero]; exact derivative_eq_zero_of_isUnit hu⟩
  have hc : a + b ≠ 0 := by
    intro h0
    have hba : b = -a := eq_neg_of_add_eq_zero_right h0
    rw [hba, IsCoprime.neg_right_iff] at hab
    have hu := isCoprime_self.mp hab
    exact hder ⟨derivative_eq_zero_of_isUnit hu,
      by rw [hba, derivative_neg, derivative_eq_zero_of_isUnit hu, neg_zero],
      by rw [h0, derivative_zero]⟩
  rcases Polynomial.abc ha hb (neg_ne_zero.mpr hc) hab (by abel) with ⟨h₁, h₂, h₃⟩ | h
  · rw [mul_neg, radical_neg, natDegree_neg] at *
    rw [natDegree_pow, natDegree_mul (mul_ne_zero ha hb) hc, natDegree_mul ha hb]
    omega
  · have h₃ := h.2.2
    rw [derivative_neg, neg_eq_zero] at h₃
    exact absurd ⟨h.1, h.2.1, h₃⟩ hder

/-! ### The no-go over `𝔽_p` (O1): Frobenius twists -/

section CharP

variable (p : ℕ) [Fact p.Prime]

/-- The Frobenius twist `c₄ = X ^ (2 p ^ n)`, `c₆ = 1` over `ZMod p` has
`D = c₄ ^ 3 - c₆ ^ 2 = (X ^ 6 - 1) ^ (p ^ n)`. -/
lemma frobeniusTwist_disc (n : ℕ) :
    ((X : (ZMod p)[X]) ^ (2 * p ^ n)) ^ 3 - 1 ^ 2 = (X ^ 6 - 1) ^ (p ^ n) := by
  rw [sub_pow_char_pow, one_pow, one_pow, ← pow_mul, ← pow_mul]
  ring_nf

/-- The Frobenius twist has `deg D = 6 p ^ n` and `deg rad D ≤ 6`. -/
lemma frobeniusTwist_natDegree (n : ℕ) :
    (((X : (ZMod p)[X]) ^ (2 * p ^ n)) ^ 3 - 1 ^ 2).natDegree = 6 * p ^ n ∧
      (radical (((X : (ZMod p)[X]) ^ (2 * p ^ n)) ^ 3 - 1 ^ 2)).natDegree ≤ 6 := by
  constructor
  · rw [← pow_mul, one_pow, ← C_1, natDegree_X_pow_sub_C]
    ring
  · rw [frobeniusTwist_disc, radical_pow _ (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)]
    refine natDegree_radical_le.trans ?_
    rw [← C_1, natDegree_X_pow_sub_C]

/-- For `n ≥ 1` the three derivatives of the Frobenius twist vanish. -/
lemma frobeniusTwist_derivative {n : ℕ} (hn : n ≠ 0) :
    derivative (((X : (ZMod p)[X]) ^ (2 * p ^ n)) ^ 3) = 0 ∧
      derivative ((1 : (ZMod p)[X]) ^ 2) = 0 ∧
      derivative (((X : (ZMod p)[X]) ^ (2 * p ^ n)) ^ 3 - 1 ^ 2) = 0 := by
  have h : derivative (((X : (ZMod p)[X]) ^ (2 * p ^ n)) ^ 3) = 0 := by
    rw [← pow_mul, derivative_X_pow]
    simp [hn, CharP.cast_eq_zero]
  exact ⟨h, by simp, by rw [derivative_sub, h]; simp⟩

/-- **O1 over `𝔽_p`.** For every `C` there are coprime `c₄, c₆ ∈ (ZMod p)[X]` with
`D = c₄ ^ 3 - c₆ ^ 2` of positive degree and `C · deg rad D < deg D`; in these examples (Frobenius
twists `c₄ = X ^ (2 p ^ n)`, `c₆ = 1`) all three derivatives vanish. -/
theorem szpiro_fails_charP (C : ℕ) :
    ∃ c₄ c₆ : (ZMod p)[X], IsCoprime c₄ c₆ ∧ 0 < (c₄ ^ 3 - c₆ ^ 2).natDegree ∧
      C * (radical (c₄ ^ 3 - c₆ ^ 2)).natDegree < (c₄ ^ 3 - c₆ ^ 2).natDegree ∧
      derivative (c₄ ^ 3) = 0 ∧ derivative (c₆ ^ 2) = 0 ∧
      derivative (c₄ ^ 3 - c₆ ^ 2) = 0 := by
  obtain ⟨hdeg, hrad⟩ := frobeniusTwist_natDegree p (C + 1)
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hpow : C + 1 < p ^ (C + 1) := Nat.lt_pow_self (by omega)
  refine ⟨X ^ (2 * p ^ (C + 1)), 1, isCoprime_one_right, ?_, ?_,
    frobeniusTwist_derivative p (Nat.succ_ne_zero C)⟩
  · rw [hdeg]
    positivity
  · rw [hdeg]
    have := Nat.mul_le_mul_left C hrad
    omega

/-- The derivative hypothesis of `Polynomial.szpiro_six` cannot be removed over `ZMod p`:
the characteristic-zero statement `Polynomial.szpiro_six_of_charZero` is false there. -/
theorem not_szpiro_six_charP :
    ¬ ∀ c₄ c₆ : (ZMod p)[X], IsCoprime c₄ c₆ → 0 < (c₄ ^ 3 - c₆ ^ 2).natDegree →
      (c₄ ^ 3 - c₆ ^ 2).natDegree + 6 ≤ 6 * (radical (c₄ ^ 3 - c₆ ^ 2)).natDegree := by
  intro h
  obtain ⟨c₄, c₆, hcop, hpos, hlt, -⟩ := szpiro_fails_charP p 6
  have := h c₄ c₆ hcop hpos
  omega

end CharP

end Polynomial
