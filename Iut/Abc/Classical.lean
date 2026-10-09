/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The classical ABC conjecture

The ABC conjecture of Masser and Oesterlé, in its classical Diophantine form:

> for every `ε > 0` there is a real number `C` such that for all coprime positive integers
> `a`, `b`, `c` with `a + b = c`, `c ≤ C · rad(abc)^{1 + ε}`,

where `rad(n)` is the product of the distinct prime factors of `n`
(`UniqueFactorizationMonoid.radical`, `Nat.radical_eq_prod_primeFactors`).

We state it over `ℕ` (`Iut.ClassicalABC`) and in the symmetric form over `ℤ`
(`Iut.ClassicalABCInt`: nonzero integers `a + b + c = 0` with `a`, `b` coprime, bounding
`max(|a|, |b|, |c|)`), and prove that the two forms are equivalent
(`Iut.classicalABC_iff_int`).

The height-theoretic form of the conjecture, [GenEll] Theorem 2.1(i) for the tripod
(`Iut.Tripod.tripodTheory.StatementI`), implies the classical form:
`Iut.Tripod.classicalABC_of_statementI` in `Iut/Tripod/ClassicalAbc.lean`.
-/

namespace Iut

open UniqueFactorizationMonoid

/-- **The classical ABC conjecture** (Masser–Oesterlé): for every `ε > 0` there is a
real `C` such that `c ≤ C · rad(abc)^{1+ε}` for all coprime positive integers `a`, `b`
and `c = a + b`. (Coprimality of `a` and `b` is equivalent to the pairwise coprimality of
`a`, `b`, `c` when `a + b = c`.) -/
def ClassicalABC : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ a b c : ℕ, 0 < a → 0 < b → Nat.Coprime a b → a + b = c →
    (c : ℝ) ≤ C * ((radical (a * b * c) : ℕ) : ℝ) ^ (1 + ε)

/-- **The classical ABC conjecture, symmetric form over `ℤ`**: for every `ε > 0` there is a
real `C` such that `max(|a|, |b|, |c|) ≤ C · rad(abc)^{1+ε}` for all nonzero integers
with `a + b + c = 0` and `a`, `b` coprime. -/
def ClassicalABCInt : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ a b c : ℤ, a ≠ 0 → b ≠ 0 → c ≠ 0 → IsCoprime a b →
    a + b + c = 0 →
      ((max |a| (max |b| |c|) : ℤ) : ℝ) ≤ C * ((radical (a * b * c) : ℤ) : ℝ) ^ (1 + ε)

/-- The form over `ℤ` implies the form over `ℕ` (apply it to `(a, b, −c)`). -/
theorem classicalABC_of_int (h : ClassicalABCInt) : ClassicalABC := by
  intro ε hε
  obtain ⟨C, hC⟩ := h ε hε
  refine ⟨C, fun a b c ha hb hab habc => ?_⟩
  have key := hC a b (-c) (by exact_mod_cast ha.ne') (by exact_mod_cast hb.ne')
    (by rw [neg_ne_zero]; exact_mod_cast (show 0 < c by omega).ne')
    (Int.isCoprime_iff_gcd_eq_one.mpr (by simpa [Int.gcd_natCast_natCast] using hab))
    (by rw [← habc]; push_cast; ring)
  have hmax : (max |(a : ℤ)| (max |(b : ℤ)| |-(c : ℤ)|)) = c := by
    rw [abs_neg]
    simp only [Nat.abs_cast]
    omega
  have hrad : (radical ((a : ℤ) * b * -(c : ℤ)) : ℤ) = (radical (a * b * c) : ℕ) := by
    rw [← Int.radical_natAbs_eq_radical]
    congr 2
    rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_neg]
    simp
  rw [hmax, hrad] at key
  exact_mod_cast key

/-- `rad` of an integer is invariant under negation. -/
private lemma radical_neg_int (z : ℤ) : radical (-z) = radical z := by
  rw [← Int.radical_natAbs_eq_radical, Int.natAbs_neg, Int.radical_natAbs_eq_radical]

/-- The key case of `classicalABC_int_of_nat`: `a, b > 0`. -/
private lemma int_bound_of_pos {ε C : ℝ}
    (hC : ∀ a b c : ℕ, 0 < a → 0 < b → Nat.Coprime a b → a + b = c →
      (c : ℝ) ≤ C * ((radical (a * b * c) : ℕ) : ℝ) ^ (1 + ε))
    {a b c : ℤ} (ha : 0 < a) (hb : 0 < b) (hab : IsCoprime a b) (habc : a + b + c = 0) :
    ((max |a| (max |b| |c|) : ℤ) : ℝ) ≤ C * ((radical (a * b * c) : ℤ) : ℝ) ^ (1 + ε) := by
  lift a to ℕ using ha.le
  lift b to ℕ using hb.le
  have hc : c = -((a + b : ℕ) : ℤ) := by push_cast; omega
  subst hc
  have key := hC a b (a + b) (by exact_mod_cast ha) (by exact_mod_cast hb)
    (by simpa [Int.gcd_natCast_natCast] using Int.isCoprime_iff_gcd_eq_one.mp hab) rfl
  have hmax : (max |(a : ℤ)| (max |(b : ℤ)| |-((a + b : ℕ) : ℤ)|)) = ((a + b : ℕ) : ℤ) := by
    rw [abs_neg]
    simp only [Nat.abs_cast]
    omega
  have hrad : (radical ((a : ℤ) * b * -((a + b : ℕ) : ℤ)) : ℤ) =
      (radical (a * b * (a + b)) : ℕ) := by
    rw [mul_neg, radical_neg_int, ← Int.radical_natCast]
    push_cast
    rfl
  rw [hmax, hrad]
  exact_mod_cast key

/-- The bound of `ClassicalABCInt` is symmetric in `a`, `b`, `c` and invariant under
`(a, b, c) ↦ (−a, −b, −c)`. -/
private lemma bound_swap12 {C e : ℝ} {a b c : ℤ}
    (h : ((max |b| (max |a| |c|) : ℤ) : ℝ) ≤ C * ((radical (b * a * c) : ℤ) : ℝ) ^ e) :
    ((max |a| (max |b| |c|) : ℤ) : ℝ) ≤ C * ((radical (a * b * c) : ℤ) : ℝ) ^ e := by
  rwa [max_left_comm, mul_comm b a] at h

private lemma bound_swap23 {C e : ℝ} {a b c : ℤ}
    (h : ((max |a| (max |c| |b|) : ℤ) : ℝ) ≤ C * ((radical (a * c * b) : ℤ) : ℝ) ^ e) :
    ((max |a| (max |b| |c|) : ℤ) : ℝ) ≤ C * ((radical (a * b * c) : ℤ) : ℝ) ^ e := by
  rwa [max_comm |c| |b|, mul_right_comm a c b] at h

private lemma bound_neg {C e : ℝ} {a b c : ℤ}
    (h : ((max |-a| (max |-b| |-c|) : ℤ) : ℝ) ≤ C * ((radical (-a * -b * -c) : ℤ) : ℝ) ^ e) :
    ((max |a| (max |b| |c|) : ℤ) : ℝ) ≤ C * ((radical (a * b * c) : ℤ) : ℝ) ^ e := by
  rwa [abs_neg, abs_neg, abs_neg, show -a * -b * -c = -(a * b * c) by ring,
    radical_neg_int] at h

/-- The form over `ℕ` implies the symmetric form over `ℤ`: up to a common sign and a
permutation, a solution of `a + b + c = 0` in nonzero integers is `(a, b, −(a + b))` with
`a, b > 0`. -/
theorem classicalABCInt_of_nat (h : ClassicalABC) : ClassicalABCInt := by
  intro ε hε
  obtain ⟨C, hC⟩ := h ε hε
  refine ⟨C, fun a b c ha hb hc hab habc => ?_⟩
  have hac : IsCoprime a c := by
    have := hab.neg_right.add_mul_left_right (-1)
    rwa [show -b + a * -1 = c by omega] at this
  have hbc : IsCoprime b c := by
    have := hab.symm.neg_right.add_mul_left_right (-1)
    rwa [show -a + b * -1 = c by omega] at this
  rcases ha.lt_or_gt with ha | ha <;> rcases hb.lt_or_gt with hb | hb
  · -- a, b < 0
    exact bound_neg (int_bound_of_pos hC (neg_pos.mpr ha) (neg_pos.mpr hb) hab.neg_neg (by omega))
  · -- a < 0 < b
    rcases hc.lt_or_gt with hc | hc
    · exact bound_swap23 (bound_neg
        (int_bound_of_pos hC (neg_pos.mpr ha) (neg_pos.mpr hc) hac.neg_neg (by omega)))
    · exact bound_swap12 (bound_swap23 (int_bound_of_pos hC hb hc hbc (by omega)))
  · -- b < 0 < a
    rcases hc.lt_or_gt with hc | hc
    · exact bound_swap12 (bound_swap23 (bound_neg
        (int_bound_of_pos hC (neg_pos.mpr hb) (neg_pos.mpr hc) hbc.neg_neg (by omega))))
    · exact bound_swap23 (int_bound_of_pos hC ha hc hac (by omega))
  · exact int_bound_of_pos hC ha hb hab habc

/-- **The two forms of the classical ABC conjecture are equivalent.** -/
theorem classicalABC_iff_int : ClassicalABC ↔ ClassicalABCInt :=
  ⟨classicalABCInt_of_nat, classicalABC_of_int⟩

end Iut
