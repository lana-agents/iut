/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Abc.Classical
import Iut.MainTheorem

/-!
# Our ABC statement is equivalent to formal-conjectures' `ABC.abc`

google-deepmind/formal-conjectures states the ABC conjecture in
`FormalConjectures/Wikipedia/ABC.lean`, namespace `ABC`, at commit
`1646ca16afd6cc7a693d3bdc9f066c4d3cc01a89`:
<https://github.com/google-deepmind/formal-conjectures/blob/1646ca16afd6cc7a693d3bdc9f066c4d3cc01a89/FormalConjectures/Wikipedia/ABC.lean>.

In the namespace `FormalConjecturesABC` we copy **verbatim** their definitions `radical` and
`quality` and the statements of their (open, unproved) theorems `abc`,
`abc.variants.lt_constant_mul` and `abc.variants.quality`; each theorem statement becomes a
`Prop` definition (`abc`, `ltConstantMul`, `qualityVariant`) whose body is the theorem's
statement with the theorem's arguments `(ε : ℝ) (hε : 0 < ε)` written as
`∀ ε : ℝ, 0 < ε →`. Everything else (binders, set-builders, coercions) is theirs,
unchanged. Their docstrings are copied as well, except that in the docstring of
`ltConstantMul` their word before `K_ε` is replaced by "real" (the same meaning), because
`scripts/audit_trust.sh` rejects that word anywhere in a Lean source.

The copied code is
"Copyright 2025 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file
except in compliance with the License. You may obtain a copy of the License at
<https://www.apache.org/licenses/LICENSE-2.0>. Unless required by applicable law or agreed to
in writing, software distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for
the specific language governing permissions and limitations under the License."

## Results

* `FormalConjecturesABC.radical_eq`: their `radical` is `UniqueFactorizationMonoid.radical`.
* `Iut.classicalABC_iff_ltConstantMul : Iut.ClassicalABC ↔ FormalConjecturesABC.ltConstantMul`.
* `Iut.classicalABC_iff_abc : Iut.ClassicalABC ↔ FormalConjecturesABC.abc`. Given the bound
  `C` for `ε / 2`, an exceptional triple for `ε` has `rad(abc)^{ε/2} < C`, so its radical,
  hence `c ≤ C · rad(abc)^{1 + ε/2}`, hence `a`, `b`, `c` are bounded; conversely the
  bound `max(1, max c)` over the finitely many exceptions works.
* `Iut.classicalABC_iff_qualityVariant`: the quality form is the same set (for `a + b = c`
  with `a, b > 0` the radical of `abc` is at least `2`).
* `Iut.formalConjecturesABC_of_variant : Iut.Cor312VariantHolds → FormalConjecturesABC.abc`.
-/

namespace FormalConjecturesABC

/-! ### Verbatim copies from formal-conjectures (`FormalConjectures/Wikipedia/ABC.lean`) -/

/--
The radical of `n` denoted is the product of the distinct prime factors of `n`.
-/
def radical (n : ℕ) : ℕ := n.primeFactors.prod id

set_option linter.style.longLine false in
/--
Quality `q(a, b, c)` of the triple `(a, b, c)` is defined as `q(a,b,c) = log (c) / log (rad(abc))`.
-/
noncomputable def quality (a b c : ℕ) : ℝ := (c : ℝ).log / (radical <| a * b * c : ℝ).log

-- `theorem ABC.abc (ε : ℝ) (hε : 0 < ε)`
set_option linter.style.longLine false in
/--
For every positive real number `ε`, there exist only finitely many triples `(a, b, c)` of coprime positive integers, with `a + b = c`, such that `c > rad(abc)^(1+ε)`
-/
def abc : Prop := ∀ ε : ℝ, 0 < ε →
    {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ ({a, b, c} : Set ℕ).Pairwise Nat.Coprime ∧
    a + b = c ∧ (radical <| a * b * c : ℝ)^(1 + ε) < c}.Finite

-- `theorem ABC.abc.variants.lt_constant_mul (ε : ℝ) (hε : 0 < ε)`
set_option linter.style.longLine false in
/--
For every positive real number ε, there exists a real `K_ε` such that for all triples (a, b, c) of coprime positive integers, with a + b = c we have `c < K_ε rad(abc)^(1+ε)`.
-/
def ltConstantMul : Prop := ∀ ε : ℝ, 0 < ε → ∃ K,
    ∀ (a b c : ℕ), 0 < a → 0 < b → 0 < c → ({a, b, c} : Set ℕ).Pairwise Nat.Coprime → a + b = c →
    c < K * (radical <| a * b * c : ℝ)^(1 + ε)

-- `theorem ABC.abc.variants.quality (ε : ℝ) (hε : 0 < ε)`
set_option linter.style.longLine false in
/--
For every positive real number ε, there exist only finitely many triples `(a, b, c)` of coprime positive integers with `a + b = c` such that `q(a, b, c) > 1 + ε`.
-/
def qualityVariant : Prop := ∀ ε : ℝ, 0 < ε →
    {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ ({a, b, c} : Set ℕ).Pairwise Nat.Coprime ∧
    a + b = c ∧ quality a b c > (1 + ε)}.Finite

/-! ### Comparison -/

/-- Their radical is `UniqueFactorizationMonoid.radical` on `ℕ`. -/
theorem radical_eq (n : ℕ) : radical n = UniqueFactorizationMonoid.radical n := by
  rw [Nat.radical_eq_prod_primeFactors, radical]
  rfl

/-- For `a + b = c` with `a, b > 0`, the pairwise coprimality of `{a, b, c}` is the
coprimality of `a` and `b`. -/
theorem pairwise_coprime_iff {a b c : ℕ} (hb : 0 < b) (habc : a + b = c) :
    ({a, b, c} : Set ℕ).Pairwise Nat.Coprime ↔ Nat.Coprime a b := by
  subst habc
  constructor
  · intro h
    exact Nat.coprime_self_add_right.mp (h (by simp) (by simp) (by omega))
  · intro h x hx y hy hne
    have h1 : Nat.Coprime a (a + b) := Nat.coprime_self_add_right.mpr h
    have h2 : Nat.Coprime b (a + b) := Nat.coprime_add_self_right.mpr h.symm
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
      first
        | exact absurd rfl hne
        | exact h
        | exact h.symm
        | exact h1
        | exact h1.symm
        | exact h2
        | exact h2.symm

/-- The radical of a natural number is positive. -/
theorem one_le_radical (n : ℕ) : 1 ≤ radical n := by
  rw [radical_eq]
  exact Nat.one_le_iff_ne_zero.mpr UniqueFactorizationMonoid.radical_ne_zero

/-- The radical of a natural number `n ≥ 2` is at least `2`. -/
theorem two_le_radical {n : ℕ} (hn : 2 ≤ n) : 2 ≤ radical n := by
  obtain ⟨p, hp⟩ := Nat.nonempty_primeFactors.mpr hn
  calc 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
    _ = id p := rfl
    _ ≤ radical n := Finset.single_le_prod' (fun q hq => (Nat.prime_of_mem_primeFactors hq).one_le)
        hp

end FormalConjecturesABC

namespace Iut

open FormalConjecturesABC

/-- The bound of `ClassicalABC` is the bound of `ltConstantMul`, for the radical of
formal-conjectures. -/
private lemma radical_cast (n : ℕ) :
    ((UniqueFactorizationMonoid.radical n : ℕ) : ℝ) = (FormalConjecturesABC.radical n : ℝ) := by
  rw [radical_eq]

/-- **Our classical ABC conjecture is formal-conjectures' `abc.variants.lt_constant_mul`.** -/
theorem classicalABC_iff_ltConstantMul : ClassicalABC ↔ FormalConjecturesABC.ltConstantMul := by
  constructor
  · intro h ε hε
    obtain ⟨C, hC⟩ := h ε hε
    refine ⟨C + 1, fun a b c ha hb hc hcop habc => ?_⟩
    have key := hC a b c ha hb ((pairwise_coprime_iff hb habc).mp hcop) habc
    rw [radical_cast] at key
    have hpos : (0 : ℝ) < (FormalConjecturesABC.radical (a * b * c) : ℝ) ^ (1 + ε) :=
      Real.rpow_pos_of_pos
        (by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one (one_le_radical _)) _
    linarith
  · intro h ε hε
    obtain ⟨K, hK⟩ := h ε hε
    refine ⟨K, fun a b c ha hb hab habc => ?_⟩
    rw [radical_cast]
    exact (hK a b c ha hb (by omega) ((pairwise_coprime_iff hb habc).mpr hab) habc).le

/-- **Our classical ABC conjecture is formal-conjectures' `ABC.abc`.** -/
theorem classicalABC_iff_abc : ClassicalABC ↔ FormalConjecturesABC.abc := by
  constructor
  · intro h ε hε
    obtain ⟨C, hC⟩ := h (ε / 2) (by positivity)
    -- an exceptional triple has `rad^{ε/2} < C`, hence `rad ≤ C^{2/ε}` and `c ≤ B`
    set B : ℝ := C * (C ^ (2 / ε)) ^ (1 + ε / 2)
    refine (((Set.finite_Iic ⌈B⌉₊).prod ((Set.finite_Iic ⌈B⌉₊).prod
      (Set.finite_Iic ⌈B⌉₊)))).subset ?_
    rintro ⟨a, b, c⟩ ⟨ha, hb, hc, hcop, habc, hlt⟩
    have key := hC a b c ha hb ((pairwise_coprime_iff hb habc).mp hcop) habc
    rw [radical_cast] at key
    have hr1 : (1 : ℝ) ≤ (FormalConjecturesABC.radical (a * b * c) : ℝ) := by
      exact_mod_cast one_le_radical _
    set r : ℝ := (FormalConjecturesABC.radical (a * b * c) : ℝ)
    have hr0 : 0 < r := by linarith
    have hsplit : r ^ (1 + ε) = r ^ (1 + ε / 2) * r ^ (ε / 2) := by
      rw [← Real.rpow_add hr0]; ring_nf
    have hpow : 0 < r ^ (1 + ε / 2) := Real.rpow_pos_of_pos hr0 _
    have hrC : r ^ (ε / 2) < C := by
      by_contra hcon
      replace hcon := not_lt.mp hcon
      have : C * r ^ (1 + ε / 2) ≤ r ^ (1 + ε) := by
        rw [hsplit, mul_comm (r ^ (1 + ε / 2))]
        exact mul_le_mul_of_nonneg_right hcon hpow.le
      linarith
    have hC0 : 0 < C := lt_of_le_of_lt (Real.rpow_nonneg hr0.le _) hrC
    have hrle : r ≤ C ^ (2 / ε) := by
      have h1 : r = (r ^ (ε / 2)) ^ (2 / ε) := by
        rw [← Real.rpow_mul hr0.le, show ε / 2 * (2 / ε) = 1 by field_simp, Real.rpow_one]
      rw [h1]
      exact Real.rpow_le_rpow (Real.rpow_nonneg hr0.le _) hrC.le (by positivity)
    have hcB : (c : ℝ) ≤ B :=
      key.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hr0.le hrle (by positivity)) hC0.le)
    have hcN : c ≤ ⌈B⌉₊ := by exact_mod_cast hcB.trans (Nat.le_ceil B)
    simp only [Set.mem_prod, Set.mem_Iic]
    omega
  · intro h ε hε
    obtain ⟨M, hM⟩ := ((h ε hε).image (fun x : ℕ × ℕ × ℕ => x.2.2)).bddAbove
    refine ⟨max 1 (M : ℝ), fun a b c ha hb hab habc => ?_⟩
    rw [radical_cast]
    have hr1 : (1 : ℝ) ≤ (FormalConjecturesABC.radical (a * b * c) : ℝ) := by
      exact_mod_cast one_le_radical _
    have hp1 : 1 ≤ (FormalConjecturesABC.radical (a * b * c) : ℝ) ^ (1 + ε) :=
      Real.one_le_rpow hr1 (by linarith)
    by_cases hexc : (FormalConjecturesABC.radical (a * b * c) : ℝ) ^ (1 + ε) < c
    · have hcM : c ≤ M := hM ⟨(a, b, c),
        ⟨ha, hb, by omega, (pairwise_coprime_iff hb habc).mpr hab, habc, hexc⟩, rfl⟩
      calc (c : ℝ) ≤ max 1 (M : ℝ) := le_max_of_le_right (by exact_mod_cast hcM)
        _ = max 1 (M : ℝ) * 1 := (mul_one _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_left hp1 (by positivity)
    · replace hexc := not_lt.mp hexc
      calc (c : ℝ) ≤ 1 * _ := by rw [one_mul]; exact hexc
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)

/-- **Our classical ABC conjecture is formal-conjectures' `abc.variants.quality`**: for
`a + b = c` with `a, b > 0` the radical of `abc` is at least `2`, so `q(a, b, c) > 1 + ε`
is `rad(abc)^{1+ε} < c`. -/
theorem classicalABC_iff_qualityVariant :
    ClassicalABC ↔ FormalConjecturesABC.qualityVariant := by
  rw [classicalABC_iff_abc]
  refine forall₂_congr fun ε hε => ?_
  refine iff_of_eq (congrArg _ (Set.ext fun ⟨a, b, c⟩ => ?_))
  simp only [Set.mem_setOf_eq]
  refine and_congr_right fun ha => and_congr_right fun hb => and_congr_right fun hc =>
    and_congr_right fun _ => and_congr_right fun habc => ?_
  have hr2 : (2 : ℝ) ≤ (FormalConjecturesABC.radical (a * b * c) : ℝ) := by
    exact_mod_cast two_le_radical (n := a * b * c)
      (le_trans (by omega : 2 ≤ c) (Nat.le_mul_of_pos_left c (by positivity)))
  have hr0 : 0 < (FormalConjecturesABC.radical (a * b * c) : ℝ) := by linarith
  have hlog : 0 < Real.log (FormalConjecturesABC.radical (a * b * c) : ℝ) :=
    Real.log_pos (by linarith)
  rw [quality, gt_iff_lt, lt_div_iff₀ hlog, ← Real.log_rpow hr0,
    Real.log_lt_log_iff (Real.rpow_pos_of_pos hr0 _) (by exact_mod_cast hc)]

/-- The Corollary 3.12 variant implies formal-conjectures' statement of the ABC conjecture. -/
theorem formalConjecturesABC_of_variant (h312 : Cor312VariantHolds) : FormalConjecturesABC.abc :=
  classicalABC_iff_abc.mp (classicalABC_of_variant h312)

end Iut
