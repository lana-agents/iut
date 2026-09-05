/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Mathlib

/-!
# The `p`-adic logarithm and the log-shell of a local field

Let `k` be a complete field with a rank-one valuation in `ℤᵐ⁰` (the setting of
`Iut/Cor312/ThetaData/TateStructure.lean`), of characteristic `0`, and let `p` be a prime with
`‖(p : k)‖ < 1` (the residue characteristic). Everything below is phrased in terms of the norm
`‖·‖` of `Valued.toNormedField` and the prime `p`; no uniformizer or ramification index is used.

* `Iut.padicLog x = ∑' n, (-1)^n (x - 1)^(n+1)/(n+1)` — the `p`-adic logarithm, summable for
  `‖x - 1‖ < 1` (`Iut.summable_logTerm`, `Iut.hasSum_padicLog`).
* `Iut.tendsto_pow_sub_one_div`: the limit formula `log x = lim_m (x^{p^m} - 1)/p^m`, proved by
  Tannery's theorem from the binomial expansion; it gives the **homomorphism property**
  `Iut.padicLog_mul : log (x y) = log x + log y` on the principal units, and its consequences
  `padicLog_pow`, `padicLog_inv`, and the vanishing on roots of unity.
* `Iut.exists_padicLog_eq`: **surjectivity** of `a ↦ log (1 + a)` from the closed ball of radius
  `‖2p‖` onto itself, by a contraction argument (Banach's fixed point theorem), based on the
  estimate `‖log (1 + a) - a - (log (1 + b) - b)‖ ≤ ‖p‖ ‖a - b‖` for `‖a‖, ‖b‖ ≤ ‖2p‖`.
* `Iut.logShell k p = {(2p)⁻¹ log u | ‖u - 1‖ < 1}` — the **log-shell** (IUT III, Prop. 3.2;
  IUT IV, Prop. 1.2): bounded (`logShell_isBounded`), relatively compact when `k` is proper
  (`isCompact_closure_logShell`), containing the ring of integers `{‖y‖ ≤ 1}`
  (`closedBall_subset_logShell`), and equal to it when `p` is odd and `p` is a uniformizer
  (`logShell_eq_closedBall`).

The discreteness of the value group is used only once, to bound `‖log u‖` uniformly over the
principal units (`exists_forall_norm_padicLog_le`).
-/

namespace Iut

open Filter Topology
open scoped Valued

universe u

noncomputable section

variable {k : Type u} [Field k] [Valued k (WithZero (Multiplicative ℤ))]
  [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))]

/-! ### Norms of integers -/

section NatNorm

variable {p : ℕ}

/-- An integer prime to the residue characteristic has norm `1`. -/
theorem norm_natCast_eq_one_of_not_dvd (hp : p.Prime) (hpk : ‖(p : k)‖ < 1) {m : ℕ}
    (hm : ¬ p ∣ m) : ‖(m : k)‖ = 1 := by
  have hcop : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).2 hm
  have hb := Nat.gcd_eq_gcd_ab p m
  rw [hcop.gcd_eq_one] at hb
  have hk : (1 : k) = (p : k) * ((Nat.gcdA p m : ℤ) : k) + (m : k) * ((Nat.gcdB p m : ℤ) : k) := by
    have := congrArg (Int.cast : ℤ → k) hb
    push_cast at this
    exact this
  refine le_antisymm (IsUltrametricDist.norm_natCast_le_one k m) ?_
  by_contra! h
  have h1 : ‖(1 : k)‖ ≤ max ‖(p : k) * ((Nat.gcdA p m : ℤ) : k)‖
      ‖(m : k) * ((Nat.gcdB p m : ℤ) : k)‖ := by
    conv_lhs => rw [hk]
    exact IsUltrametricDist.norm_add_le_max _ _
  rw [norm_one, norm_mul, norm_mul] at h1
  have hA := IsUltrametricDist.norm_intCast_le_one k (Nat.gcdA p m)
  have hB := IsUltrametricDist.norm_intCast_le_one k (Nat.gcdB p m)
  have h2 : ‖(p : k)‖ * ‖((Nat.gcdA p m : ℤ) : k)‖ < 1 :=
    mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hpk hA
  have h3 : ‖(m : k)‖ * ‖((Nat.gcdB p m : ℤ) : k)‖ < 1 :=
    mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) h hB
  exact absurd h1 (not_le.2 (max_lt h2 h3))

/-- `‖m‖ = ‖p‖ ^ v_p(m)` for a nonzero integer `m`. -/
theorem norm_natCast_eq_pow (hp : p.Prime) (hpk : ‖(p : k)‖ < 1) {m : ℕ} (hm : m ≠ 0) :
    ‖(m : k)‖ = ‖(p : k)‖ ^ m.factorization p := by
  conv_lhs => rw [← Nat.ordProj_mul_ordCompl_eq_self m p]
  rw [Nat.cast_mul, norm_mul, Nat.cast_pow, norm_pow,
    norm_natCast_eq_one_of_not_dvd hp hpk (Nat.not_dvd_ordCompl hp hm), mul_one]

/-- `v_p(m) < m` for `m ≠ 0`. -/
theorem factorization_lt_self (hp : p.Prime) {m : ℕ} (hm : m ≠ 0) : m.factorization p < m :=
  (Nat.lt_pow_self hp.one_lt).trans_le (Nat.ordProj_le p hm)

/-- The polynomial bound `‖m‖⁻¹ ≤ m ^ N` on the inverse norms of integers, for a suitable `N`
(any `N` with `‖p‖⁻¹ ≤ p ^ N`). -/
theorem exists_norm_natCast_inv_le [CharZero k] (hp : p.Prime) (hpk : ‖(p : k)‖ < 1) :
    ∃ N : ℕ, ∀ m : ℕ, ‖(m : k)‖⁻¹ ≤ (m : ℝ) ^ N := by
  have hp0 : (0 : ℝ) < ‖(p : k)‖ := norm_pos_iff.2 (Nat.cast_ne_zero.2 hp.ne_zero)
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (‖(p : k)‖⁻¹)
    (by exact_mod_cast hp.one_lt : (1 : ℝ) < p)
  refine ⟨N, fun m => ?_⟩
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  rw [norm_natCast_eq_pow hp hpk hm, ← inv_pow]
  calc (‖(p : k)‖⁻¹) ^ (m.factorization p) ≤ ((p : ℝ) ^ N) ^ (m.factorization p) :=
        pow_le_pow_left₀ (by positivity) hN.le _
    _ = ((p : ℝ) ^ m.factorization p) ^ N := by rw [← pow_mul, ← pow_mul, mul_comm]
    _ ≤ (m : ℝ) ^ N :=
        pow_le_pow_left₀ (by positivity) (by exact_mod_cast Nat.ordProj_le p hm) _

/-- `‖2‖ ≤ 1`. -/
theorem norm_two_le_one : ‖(2 : k)‖ ≤ 1 := by
  simpa using IsUltrametricDist.norm_natCast_le_one k 2

/-- `‖2‖ = 1` when `p` is odd. -/
theorem norm_two_eq_one (hp : p.Prime) (hpk : ‖(p : k)‖ < 1) (hodd : Odd p) : ‖(2 : k)‖ = 1 := by
  have : ¬ p ∣ 2 := fun h => by
    have := (Nat.le_of_dvd two_pos h).antisymm hp.two_le
    subst this
    exact absurd hodd (by decide)
  simpa using norm_natCast_eq_one_of_not_dvd hp hpk this

/-- `‖2p‖ < 1`. -/
theorem norm_two_mul_lt_one (hpk : ‖(p : k)‖ < 1) : ‖2 * (p : k)‖ < 1 := by
  rw [norm_mul]
  exact mul_lt_one_of_nonneg_of_lt_one_right norm_two_le_one (norm_nonneg _) hpk

/-- The key numeric estimate for the contraction argument: `‖2p‖ ^ (m - 1) ≤ ‖p‖ ‖m‖` for
`m ≥ 2`. -/
theorem norm_two_mul_pow_le (hp : p.Prime) (hpk : ‖(p : k)‖ < 1) {m : ℕ} (hm : 2 ≤ m) :
    ‖2 * (p : k)‖ ^ (m - 1) ≤ ‖(p : k)‖ * ‖(m : k)‖ := by
  have hm0 : m ≠ 0 := by omega
  rw [norm_natCast_eq_pow hp hpk hm0, ← pow_succ']
  set v := m.factorization p with hv
  have hpv : p ^ v ≤ m := Nat.ordProj_le p hm0
  have hp1 : ‖(p : k)‖ ≤ 1 := hpk.le
  rcases eq_or_ne p 2 with rfl | h2
  · -- `p = 2`: `‖4‖ ^ (m-1) = ‖2‖ ^ (2 (m - 1)) ≤ ‖2‖ ^ (v + 1)` since `v + 1 ≤ 2 (m - 1)`.
    have : (2 : k) * ((2 : ℕ) : k) = ((2 : ℕ) : k) ^ 2 := by push_cast; ring
    rw [this, norm_pow, ← pow_mul]
    refine pow_le_pow_of_le_one (norm_nonneg _) hp1 ?_
    have : v < m := factorization_lt_self hp hm0
    omega
  · -- `p` odd: `‖2p‖ ^ (m-1) ≤ ‖p‖ ^ (m-1) ≤ ‖p‖ ^ (v + 1)` since `v + 1 ≤ m - 1`.
    have h2p : ‖2 * (p : k)‖ ≤ ‖(p : k)‖ := by
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) norm_two_le_one
    refine (pow_le_pow_left₀ (norm_nonneg _) h2p _).trans
      (pow_le_pow_of_le_one (norm_nonneg _) hp1 ?_)
    have hp3 : 3 ≤ p := by
      have := hp.two_le
      omega
    rcases Nat.eq_zero_or_pos v with hv0 | hv0
    · omega
    · -- `v + 2 ≤ 2 v + 1 ≤ 3 ^ v ≤ p ^ v ≤ m`
      have h3 : 1 + v * 2 ≤ 3 ^ v := by
        have := one_add_mul_le_pow (a := (2 : ℤ)) (by norm_num) v
        exact_mod_cast this
      have h4 : 3 ^ v ≤ p ^ v := Nat.pow_le_pow_left hp3 v
      omega

end NatNorm

/-! ### The logarithm series -/

section Series

variable {p : ℕ}

/-- The `n`-th term `(-1)^n (x - 1)^(n+1) / (n+1)` of the logarithm series at `x`. -/
def logTerm (x : k) (n : ℕ) : k := (-1) ^ n * (x - 1) ^ (n + 1) / (n + 1)

/-- The `p`-adic logarithm `log x = ∑ (-1)^n (x - 1)^(n+1)/(n+1)`; the series converges for
`‖x - 1‖ < 1` (and the definition is only meaningful there). -/
def padicLog (x : k) : k := ∑' n, logTerm x n

omit [Valued k (WithZero (Multiplicative ℤ))]
  [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))] in
@[simp] theorem logTerm_one (n : ℕ) : logTerm (1 : k) n = 0 := by simp [logTerm]

omit [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))] in
@[simp] theorem padicLog_one : padicLog (1 : k) = 0 := by simp [padicLog]

omit [Valued k (WithZero (Multiplicative ℤ))]
  [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))] in
theorem logTerm_zero (x : k) : logTerm x 0 = x - 1 := by simp [logTerm]

theorem norm_logTerm [CharZero k] (x : k) (n : ℕ) :
    ‖logTerm x n‖ = ‖x - 1‖ ^ (n + 1) * ‖((n + 1 : ℕ) : k)‖⁻¹ := by
  unfold logTerm
  rw [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_pow,
    div_eq_mul_inv]
  push_cast
  rfl

theorem norm_logTerm_le [CharZero k] {N : ℕ} (hN : ∀ m : ℕ, ‖(m : k)‖⁻¹ ≤ (m : ℝ) ^ N) (x : k)
    (n : ℕ) : ‖logTerm x n‖ ≤ ((n + 1 : ℕ) : ℝ) ^ N * ‖x - 1‖ ^ (n + 1) := by
  rw [norm_logTerm, mul_comm]
  exact mul_le_mul_of_nonneg_right (hN _) (by positivity)

/-- The terms of the logarithm series tend to `0` for `‖x - 1‖ < 1`. -/
theorem tendsto_logTerm [CharZero k] (hp : p.Prime) (hpk : ‖(p : k)‖ < 1) {x : k}
    (hx : ‖x - 1‖ < 1) : Tendsto (logTerm x) atTop (𝓝 0) := by
  obtain ⟨N, hN⟩ := exists_norm_natCast_inv_le hp hpk
  have h := tendsto_pow_const_mul_const_pow_of_abs_lt_one N
    (abs_lt.2 ⟨by linarith [norm_nonneg (x - 1)], hx⟩)
  have h' := h.comp (tendsto_add_atTop_nat 1)
  exact squeeze_zero_norm (fun n => norm_logTerm_le hN x n) h'

/-- The ultrametric bound `‖log x‖ ≤ C` from a uniform bound on the terms (no summability
needed). -/
theorem norm_padicLog_le_of_forall_le {x : k} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ n, ‖logTerm x n‖ ≤ C) : ‖padicLog x‖ ≤ C :=
  IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg hC h

/-- For `‖x - 1‖ ≤ ‖p‖` every term of the series has norm `≤ ‖p‖`. -/
theorem norm_logTerm_le_norm_p [CharZero k] (hp : p.Prime) (hpk : ‖(p : k)‖ < 1) {x : k}
    (hx : ‖x - 1‖ ≤ ‖(p : k)‖) (n : ℕ) : ‖logTerm x n‖ ≤ ‖(p : k)‖ := by
  have hp0 : (0 : ℝ) < ‖(p : k)‖ := norm_pos_iff.2 (Nat.cast_ne_zero.2 hp.ne_zero)
  rw [norm_logTerm, norm_natCast_eq_pow hp hpk (Nat.succ_ne_zero n)]
  set v := (n + 1).factorization p
  have hv : v < n + 1 := factorization_lt_self hp (Nat.succ_ne_zero n)
  calc ‖x - 1‖ ^ (n + 1) * (‖(p : k)‖ ^ v)⁻¹
      ≤ ‖(p : k)‖ ^ (n + 1) * (‖(p : k)‖ ^ v)⁻¹ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hx _) (by positivity)
    _ = ‖(p : k)‖ ^ (n + 1 - v) := by
        rw [← pow_sub₀ _ hp0.ne' hv.le]
    _ ≤ ‖(p : k)‖ ^ 1 := pow_le_pow_of_le_one (norm_nonneg _) hpk.le (by omega)
    _ = ‖(p : k)‖ := pow_one _

/-- For `‖x - 1‖ ≤ ‖p‖` one has `‖log x‖ ≤ ‖p‖`. -/
theorem norm_padicLog_le_norm_p [CharZero k] (hp : p.Prime) (hpk : ‖(p : k)‖ < 1) {x : k}
    (hx : ‖x - 1‖ ≤ ‖(p : k)‖) : ‖padicLog x‖ ≤ ‖(p : k)‖ :=
  norm_padicLog_le_of_forall_le (norm_nonneg _) (norm_logTerm_le_norm_p hp hpk hx)

variable [CompleteSpace k]

/-- The logarithm series is summable for `‖x - 1‖ < 1`. -/
theorem summable_logTerm [CharZero k] (hp : p.Prime) (hpk : ‖(p : k)‖ < 1) {x : k}
    (hx : ‖x - 1‖ < 1) : Summable (logTerm x) :=
  NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
    (Nat.cofinite_eq_atTop ▸ tendsto_logTerm hp hpk hx)

theorem hasSum_padicLog [CharZero k] (hp : p.Prime) (hpk : ‖(p : k)‖ < 1) {x : k}
    (hx : ‖x - 1‖ < 1) : HasSum (logTerm x) (padicLog x) :=
  (summable_logTerm hp hpk hx).hasSum

end Series

/-! ### The limit formula `log x = lim (x^{p^m} - 1)/p^m` and the homomorphism property -/

section Limit

variable {p : ℕ}

omit [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))] in
/-- The binomial expansion of `(x^N - 1)/N` as a series in `x - 1`, with coefficients
`C(N-1, n)/(n+1)`. -/
theorem pow_sub_one_div_eq_tsum [CharZero k] (x : k) {N : ℕ} (hN : N ≠ 0) :
    (x ^ N - 1) / N = ∑' n : ℕ, ((N - 1).choose n : k) / (n + 1) * (x - 1) ^ (n + 1) := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have hx : x = (x - 1) + 1 := by ring
  rw [tsum_eq_sum (s := Finset.range (M + 1)) (fun n hn => ?_)]
  · conv_lhs => rw [hx, add_pow, Finset.sum_range_succ']
    simp only [Nat.add_sub_cancel, one_pow, mul_one, pow_zero, Nat.choose_zero_right,
      Nat.cast_one, add_sub_cancel_right]
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun n _ => ?_
    have h : ((M : k) + 1) * (M.choose n : k) = ((M + 1).choose (n + 1) : k) * ((n : k) + 1) := by
      exact_mod_cast Nat.add_one_mul_choose_eq M n
    have hM : ((M : k) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero M
    have hn : ((n : k) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    have hc : ((M + 1).choose (n + 1) : k) / ((M : k) + 1) = (M.choose n : k) / ((n : k) + 1) := by
      rw [div_eq_div_iff hM hn]
      linear_combination -h
    push_cast
    rw [mul_div_assoc, hc]
    ring
  · rw [Finset.mem_range, not_lt] at hn
    rw [Nat.add_sub_cancel, Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_div, zero_mul]

omit [Valued k (WithZero (Multiplicative ℤ))]
  [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))] in
/-- The binomial coefficient `C(N, n)` as a polynomial in `N`: `(descPochhammer n)(N) / n!`. -/
theorem cast_choose_eq_descPochhammer_div [CharZero k] (N n : ℕ) :
    (N.choose n : k) = (descPochhammer k n).eval (N : k) / (n.factorial : k) := by
  rw [descPochhammer_eval_eq_descFactorial, Nat.descFactorial_eq_factorial_mul_choose]
  have : (n.factorial : k) ≠ 0 := Nat.cast_ne_zero.2 n.factorial_ne_zero
  push_cast
  field_simp

omit [Valued k (WithZero (Multiplicative ℤ))]
  [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))] in
theorem descPochhammer_eval_neg_one (n : ℕ) :
    (descPochhammer k n).eval (-1 : k) = (-1) ^ n * (n.factorial : k) := by
  rw [descPochhammer_eval_eq_prod_range]
  have : ∀ j ∈ Finset.range n, (-1 : k) - j = -((j : k) + 1) := fun j _ => by ring
  rw [Finset.prod_congr rfl this, Finset.prod_neg, Finset.card_range]
  congr 1
  rw [← Finset.prod_range_add_one_eq_factorial, Nat.cast_prod]
  simp

/-- The principal units form a group: `‖xy - 1‖ < 1` for `‖x - 1‖, ‖y - 1‖ < 1`. -/
theorem norm_mul_sub_one_lt {x y : k} (hx : ‖x - 1‖ < 1) (hy : ‖y - 1‖ < 1) :
    ‖x * y - 1‖ < 1 := by
  have : x * y - 1 = (x - 1) * (y - 1) + (x - 1) + (y - 1) := by ring
  rw [this]
  calc ‖(x - 1) * (y - 1) + (x - 1) + (y - 1)‖
      ≤ max (max ‖(x - 1) * (y - 1)‖ ‖x - 1‖) ‖y - 1‖ :=
        (IsUltrametricDist.norm_add_le_max _ _).trans
          (max_le_max_right _ (IsUltrametricDist.norm_add_le_max _ _))
    _ < 1 := by
        rw [norm_mul]
        exact max_lt (max_lt (mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hx hy.le) hx) hy

theorem norm_eq_one_of_norm_sub_one_lt {x : k} (hx : ‖x - 1‖ < 1) : ‖x‖ = 1 := by
  have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x := x - 1) (y := 1)
    (by rw [norm_one]; exact hx.ne)
  rw [sub_add_cancel, norm_one, max_eq_right hx.le] at this
  exact this

theorem ne_zero_of_norm_sub_one_lt {x : k} (hx : ‖x - 1‖ < 1) : x ≠ 0 := by
  rintro rfl
  simp at hx

theorem norm_inv_sub_one_lt {x : k} (hx : ‖x - 1‖ < 1) : ‖x⁻¹ - 1‖ < 1 := by
  have hx0 : x ≠ 0 := ne_zero_of_norm_sub_one_lt hx
  have : x⁻¹ - 1 = -(x - 1) * x⁻¹ := by rw [neg_sub, sub_mul, one_mul, mul_inv_cancel₀ hx0]
  rw [this, norm_mul, norm_neg, norm_inv, norm_eq_one_of_norm_sub_one_lt hx, inv_one, mul_one]
  exact hx

theorem norm_pow_sub_one_lt {x : k} (hx : ‖x - 1‖ < 1) (n : ℕ) : ‖x ^ n - 1‖ < 1 := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ]; exact norm_mul_sub_one_lt ih hx

variable [CompleteSpace k]

/-- **The limit formula**: `log x = lim_{m → ∞} (x^{p^m} - 1)/p^m` for `‖x - 1‖ < 1`. -/
theorem tendsto_pow_sub_one_div [CharZero k] (hp : p.Prime) (hpk : ‖(p : k)‖ < 1) {x : k}
    (hx : ‖x - 1‖ < 1) :
    Tendsto (fun m : ℕ => (x ^ (p ^ m) - 1) / ((p : k) ^ m)) atTop (𝓝 (padicLog x)) := by
  obtain ⟨N, hN⟩ := exists_norm_natCast_inv_le hp hpk
  have heq : ∀ m : ℕ, (x ^ (p ^ m) - 1) / ((p : k) ^ m) =
      ∑' n : ℕ, ((p ^ m - 1).choose n : k) / (n + 1) * (x - 1) ^ (n + 1) := fun m => by
    have := pow_sub_one_div_eq_tsum x (N := p ^ m) (pow_ne_zero _ hp.ne_zero)
    rw [Nat.cast_pow] at this
    exact this
  refine (Tendsto.congr (fun m => (heq m).symm)) ?_
  unfold padicLog
  refine tendsto_tsum_of_dominated_convergence
    (bound := fun n => ((n + 1 : ℕ) : ℝ) ^ N * ‖x - 1‖ ^ (n + 1)) ?_ ?_
    (Eventually.of_forall fun m n => ?_)
  · refine (summable_nat_add_iff 1).2
      (summable_pow_mul_geometric_of_norm_lt_one N (r := ‖x - 1‖) ?_)
    rwa [Real.norm_of_nonneg (norm_nonneg _)]
  · intro n
    have hlim : Tendsto (fun m : ℕ => ((p ^ m - 1 : ℕ) : k)) atTop (𝓝 (-1)) := by
      have : ∀ m, ((p ^ m - 1 : ℕ) : k) = (p : k) ^ m - 1 := fun m => by
        rw [Nat.cast_sub (Nat.one_le_pow _ _ hp.pos), Nat.cast_pow, Nat.cast_one]
      simp_rw [this]
      simpa using (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hpk).sub_const 1
    have h1 := ((descPochhammer k n).continuous.tendsto (-1 : k)).comp hlim
    rw [descPochhammer_eval_neg_one] at h1
    have h2 := ((h1.div_const (n.factorial : k)).div_const ((n : k) + 1)).mul_const
      ((x - 1) ^ (n + 1))
    convert h2 using 1
    · funext m
      simp only [Function.comp]
      rw [cast_choose_eq_descPochhammer_div]
    · have : (n.factorial : k) ≠ 0 := Nat.cast_ne_zero.2 n.factorial_ne_zero
      unfold logTerm
      field_simp
  · rw [norm_mul, norm_div, norm_pow]
    have hC : ‖((p ^ m - 1).choose n : k)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one k _
    have hn : ‖(n : k) + 1‖⁻¹ ≤ ((n : ℝ) + 1) ^ N := by
      have := hN (n + 1)
      push_cast at this
      exact this
    push_cast
    calc ‖((p ^ m - 1).choose n : k)‖ / ‖(n : k) + 1‖ * ‖x - 1‖ ^ (n + 1)
        ≤ (1 * ((n : ℝ) + 1) ^ N) * ‖x - 1‖ ^ (n + 1) := by
          rw [div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul hC hn (by positivity) zero_le_one) (by positivity)
      _ = ((n : ℝ) + 1) ^ N * ‖x - 1‖ ^ (n + 1) := by rw [one_mul]

/-- **The homomorphism property** of the `p`-adic logarithm on the principal units. -/
theorem padicLog_mul [CharZero k] (hp : p.Prime) (hpk : ‖(p : k)‖ < 1) {x y : k}
    (hx : ‖x - 1‖ < 1) (hy : ‖y - 1‖ < 1) : padicLog (x * y) = padicLog x + padicLog y := by
  have hp0 : (p : k) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have h1 := tendsto_pow_sub_one_div hp hpk hx
  have h2 := tendsto_pow_sub_one_div hp hpk hy
  have h3 := tendsto_pow_sub_one_div hp hpk (norm_mul_sub_one_lt hx hy)
  have hp0' : Tendsto (fun m : ℕ => (p : k) ^ m) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one hpk
  have h4 := (h1.add h2).add (hp0'.mul (h1.mul h2))
  rw [zero_mul, add_zero] at h4
  refine tendsto_nhds_unique h3 (h4.congr fun m => ?_)
  have : (p : k) ^ m ≠ 0 := pow_ne_zero _ hp0
  field_simp
  ring

theorem padicLog_pow [CharZero k] (hp : p.Prime) (hpk : ‖(p : k)‖ < 1) {x : k}
    (hx : ‖x - 1‖ < 1) (n : ℕ) : padicLog (x ^ n) = n * padicLog x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, padicLog_mul hp hpk (norm_pow_sub_one_lt hx n) hx, ih]
    push_cast
    ring

theorem padicLog_inv [CharZero k] (hp : p.Prime) (hpk : ‖(p : k)‖ < 1) {x : k}
    (hx : ‖x - 1‖ < 1) : padicLog x⁻¹ = - padicLog x := by
  have := padicLog_mul hp hpk hx (norm_inv_sub_one_lt hx)
  rw [mul_inv_cancel₀ (ne_zero_of_norm_sub_one_lt hx), padicLog_one] at this
  linear_combination -this

/-- The logarithm kills the roots of unity among the principal units. -/
theorem padicLog_eq_zero_of_pow_eq_one [CharZero k] (hp : p.Prime) (hpk : ‖(p : k)‖ < 1) {x : k}
    (hx : ‖x - 1‖ < 1) {n : ℕ} (hn : n ≠ 0) (h : x ^ n = 1) : padicLog x = 0 := by
  have := padicLog_pow hp hpk hx n
  rw [h, padicLog_one] at this
  exact (mul_eq_zero.1 this.symm).resolve_left (Nat.cast_ne_zero.2 hn)

end Limit

/-! ### Surjectivity of `a ↦ log (1 + a)` on the ball of radius `‖2p‖` -/

section Surjective

variable {p : ℕ}

/-- The remainder `log (1 + a) - a = ∑_{n ≥ 1} (-1)^n a^(n+1)/(n+1)`. -/
def logRem (a : k) : k := ∑' n, logTerm (1 + a) (n + 1)

omit [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))] in
@[simp] theorem logRem_zero : logRem (0 : k) = 0 := by simp [logRem]

variable [CompleteSpace k]

theorem padicLog_one_add [CharZero k] (hp : p.Prime) (hpk : ‖(p : k)‖ < 1) {a : k}
    (ha : ‖a‖ < 1) : padicLog (1 + a) = a + logRem a := by
  unfold padicLog logRem
  rw [(summable_logTerm hp hpk (by simpa using ha)).tsum_eq_zero_add, logTerm_zero,
    add_sub_cancel_left]

omit [CompleteSpace k] in
/-- The termwise Lipschitz estimate for the remainder on the ball of radius `‖2p‖`. -/
theorem norm_logTerm_sub_le [CharZero k] (hp : p.Prime) (hpk : ‖(p : k)‖ < 1) {a b : k}
    (ha : ‖a‖ ≤ ‖2 * (p : k)‖) (hb : ‖b‖ ≤ ‖2 * (p : k)‖) (n : ℕ) :
    ‖logTerm (1 + a) (n + 1) - logTerm (1 + b) (n + 1)‖ ≤ ‖(p : k)‖ * ‖a - b‖ := by
  have hmn : (0 : ℝ) < ‖((n + 2 : ℕ) : k)‖ :=
    norm_pos_iff.2 (Nat.cast_ne_zero.2 (Nat.succ_ne_zero _))
  have key : logTerm (1 + a) (n + 1) - logTerm (1 + b) (n + 1) = (-1) ^ (n + 1) *
      ((∑ i ∈ Finset.range (n + 2), a ^ i * b ^ (n + 2 - 1 - i)) * (a - b)) /
        ((n + 2 : ℕ) : k) := by
    unfold logTerm
    rw [geom_sum₂_mul]
    push_cast
    ring
  rw [key, norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_mul,
    div_le_iff₀ hmn]
  have hsum : ‖∑ i ∈ Finset.range (n + 2), a ^ i * b ^ (n + 2 - 1 - i)‖ ≤
      ‖2 * (p : k)‖ ^ (n + 2 - 1) := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [norm_mul, norm_pow, norm_pow]
    calc ‖a‖ ^ i * ‖b‖ ^ (n + 2 - 1 - i)
        ≤ ‖2 * (p : k)‖ ^ i * ‖2 * (p : k)‖ ^ (n + 2 - 1 - i) :=
          mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) ha _)
            (pow_le_pow_left₀ (norm_nonneg _) hb _) (by positivity) (by positivity)
      _ = ‖2 * (p : k)‖ ^ (n + 2 - 1) := by
          rw [← pow_add]
          congr 1
          omega
  calc ‖∑ i ∈ Finset.range (n + 2), a ^ i * b ^ (n + 2 - 1 - i)‖ * ‖a - b‖
      ≤ ‖2 * (p : k)‖ ^ (n + 2 - 1) * ‖a - b‖ := mul_le_mul_of_nonneg_right hsum (norm_nonneg _)
    _ ≤ (‖(p : k)‖ * ‖((n + 2 : ℕ) : k)‖) * ‖a - b‖ :=
        mul_le_mul_of_nonneg_right (norm_two_mul_pow_le hp hpk (by omega)) (norm_nonneg _)
    _ = ‖(p : k)‖ * ‖a - b‖ * ‖((n + 2 : ℕ) : k)‖ := by ring

/-- The remainder `a ↦ log (1 + a) - a` is a contraction with contraction factor `‖p‖` on the ball of
radius `‖2p‖`. -/
theorem norm_logRem_sub_le [CharZero k] (hp : p.Prime) (hpk : ‖(p : k)‖ < 1) {a b : k}
    (ha : ‖a‖ ≤ ‖2 * (p : k)‖) (hb : ‖b‖ ≤ ‖2 * (p : k)‖) :
    ‖logRem a - logRem b‖ ≤ ‖(p : k)‖ * ‖a - b‖ := by
  have h2 := norm_two_mul_lt_one (k := k) hpk
  have ha' : ‖(1 + a) - 1‖ < 1 := by simpa using ha.trans_lt h2
  have hb' : ‖(1 + b) - 1‖ < 1 := by simpa using hb.trans_lt h2
  unfold logRem
  rw [← Summable.tsum_sub ((summable_nat_add_iff 1).2 (summable_logTerm hp hpk ha'))
    ((summable_nat_add_iff 1).2 (summable_logTerm hp hpk hb'))]
  exact IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity)
    (norm_logTerm_sub_le hp hpk ha hb)

theorem norm_logRem_le [CharZero k] (hp : p.Prime) (hpk : ‖(p : k)‖ < 1) {a : k}
    (ha : ‖a‖ ≤ ‖2 * (p : k)‖) : ‖logRem a‖ ≤ ‖(p : k)‖ * ‖a‖ := by
  simpa using norm_logRem_sub_le hp hpk ha (b := 0) (by simp)

/-- **Surjectivity of the logarithm**: every `y` with `‖y‖ ≤ ‖2p‖` is `log (1 + a)` for some
`a` with `‖a‖ ≤ ‖2p‖` (Banach's fixed point theorem for `a ↦ y - (log (1 + a) - a)`). -/
theorem exists_padicLog_eq [CharZero k] (hp : p.Prime) (hpk : ‖(p : k)‖ < 1) {y : k}
    (hy : ‖y‖ ≤ ‖2 * (p : k)‖) : ∃ a : k, ‖a‖ ≤ ‖2 * (p : k)‖ ∧ padicLog (1 + a) = y := by
  set R := ‖2 * (p : k)‖ with hR
  let T : k → k := fun a => y - logRem a
  have hT : Set.MapsTo T (Metric.closedBall 0 R) (Metric.closedBall 0 R) := by
    intro a ha
    rw [Metric.mem_closedBall, dist_zero_right] at ha ⊢
    calc ‖y - logRem a‖ ≤ max ‖y‖ ‖logRem a‖ := by
          rw [sub_eq_add_neg]
          simpa using IsUltrametricDist.norm_add_le_max y (-logRem a)
      _ ≤ R := max_le hy ((norm_logRem_le hp hpk ha).trans
          ((mul_le_of_le_one_left (norm_nonneg _) hpk.le).trans ha))
  have hc : ContractingWith ‖(p : k)‖₊ (hT.restrict T _ _) := by
    refine ⟨by simpa [← NNReal.coe_lt_one] using hpk, LipschitzWith.of_dist_le_mul fun a b => ?_⟩
    rw [Subtype.dist_eq, Subtype.dist_eq, dist_eq_norm, dist_eq_norm]
    have ha : ‖(a : k)‖ ≤ R := by
      have := a.2
      rwa [Metric.mem_closedBall, dist_zero_right] at this
    have hb : ‖(b : k)‖ ≤ R := by
      have := b.2
      rwa [Metric.mem_closedBall, dist_zero_right] at this
    change ‖(y - logRem (a : k)) - (y - logRem (b : k))‖ ≤ ‖(p : k)‖ * ‖(a : k) - (b : k)‖
    rw [sub_sub_sub_cancel_left, norm_sub_rev]
    exact norm_logRem_sub_le hp hpk ha hb
  obtain ⟨a, ha, hfix, -, -⟩ := ContractingWith.exists_fixedPoint'
    Metric.isClosed_closedBall.isComplete hT hc (x := 0)
    (Metric.mem_closedBall_self (norm_nonneg _)) (edist_ne_top _ _)
  rw [Metric.mem_closedBall, dist_zero_right] at ha
  refine ⟨a, ha, ?_⟩
  have hfix' : y - logRem a = a := hfix
  rw [padicLog_one_add hp hpk (ha.trans_lt (norm_two_mul_lt_one hpk))]
  linear_combination -hfix'

end Surjective

/-! ### The log-shell -/

section LogShell

variable (k) (p : ℕ)

/-- The **log-shell** `𝓘_k = (2p)⁻¹ · log (1 + 𝔪_k)`, the image of the principal units under
`(2p)⁻¹ log` (IUT III, Proposition 3.2; IUT IV, Proposition 1.2). -/
def logShell : Set k := {y | ∃ u : k, ‖u - 1‖ < 1 ∧ y = (2 * (p : k))⁻¹ * padicLog u}

variable {k p}

theorem mem_logShell {y : k} :
    y ∈ logShell k p ↔ ∃ u : k, ‖u - 1‖ < 1 ∧ y = (2 * (p : k))⁻¹ * padicLog u := Iff.rfl

/-- **Discreteness**: there is `ρ < 1` with `‖a‖ ≤ ρ` for every `a` with `‖a‖ < 1` (the norm
of a uniformizer, when one exists; in general `‖p‖^{1/e}` with `v(p) = ofAdd (-e)`). -/
theorem exists_lt_one_forall_norm_le [CharZero k] (hp : p.Prime) (hpk : ‖(p : k)‖ < 1) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ a : k, ‖a‖ < 1 → ‖a‖ ≤ ρ := by
  have hp0 : (p : k) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hvp : Valued.v (p : k) ≠ 0 := (Valuation.ne_zero_iff _).2 hp0
  have hvp1 : Valued.v (p : k) < 1 := Valued.toNormedField.norm_lt_one_iff.1 hpk
  obtain ⟨γ, hγ⟩ : ∃ γ : Multiplicative ℤ, Valued.v (p : k) = γ :=
    ⟨WithZero.unzero hvp, (WithZero.coe_unzero hvp).symm⟩
  have hγ1 : γ < 1 := by
    rw [← WithZero.coe_lt_coe, ← hγ, WithZero.coe_one]
    exact hvp1
  have hγ2 : Multiplicative.toAdd γ < 0 := by
    rwa [← Multiplicative.toAdd_lt, toAdd_one] at hγ1
  set e : ℕ := (-Multiplicative.toAdd γ).toNat with he
  have he' : (e : ℤ) = -Multiplicative.toAdd γ := Int.toNat_of_nonneg (by omega)
  have he0 : 0 < e := by omega
  have hepos : (0 : ℝ) < e := by exact_mod_cast he0
  have hp0' : 0 ≤ ‖(p : k)‖ := norm_nonneg _
  refine ⟨‖(p : k)‖ ^ ((e : ℝ)⁻¹), Real.rpow_nonneg hp0' _,
    Real.rpow_lt_one hp0' hpk (by positivity), fun a ha => ?_⟩
  rw [Real.le_rpow_inv_iff_of_pos (norm_nonneg _) hp0' hepos, Real.rpow_natCast, ← norm_pow,
    Valued.toNormedField.norm_le_iff, Valuation.map_pow]
  rcases eq_or_ne a 0 with rfl | ha0
  · rw [map_zero, zero_pow he0.ne']
    exact zero_le
  · have h0 : Valued.v a ≠ 0 := (Valuation.ne_zero_iff _).2 ha0
    have hva : Valued.v a < 1 := Valued.toNormedField.norm_lt_one_iff.1 ha
    obtain ⟨δ, hδ⟩ : ∃ δ : Multiplicative ℤ, Valued.v a = δ :=
      ⟨WithZero.unzero h0, (WithZero.coe_unzero h0).symm⟩
    have hδ1 : Multiplicative.toAdd δ < 0 := by
      have : δ < 1 := by
        rw [← WithZero.coe_lt_coe, ← hδ, WithZero.coe_one]
        exact hva
      rwa [← Multiplicative.toAdd_lt, toAdd_one] at this
    rw [hδ, hγ, ← WithZero.coe_pow, WithZero.coe_le_coe, ← Multiplicative.toAdd_le, toAdd_pow,
      nsmul_eq_mul, he']
    nlinarith

/-- The logarithm is uniformly bounded on the principal units. -/
theorem exists_forall_norm_padicLog_le [CharZero k] (hp : p.Prime) (hpk : ‖(p : k)‖ < 1) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x : k, ‖x - 1‖ < 1 → ‖padicLog x‖ ≤ M := by
  obtain ⟨N, hN⟩ := exists_norm_natCast_inv_le hp hpk
  obtain ⟨ρ, hρ0, hρ1, hρ⟩ := exists_lt_one_forall_norm_le hp hpk
  have ht : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ N * ρ ^ (n + 1)) atTop (𝓝 0) :=
    (tendsto_pow_const_mul_const_pow_of_abs_lt_one N (abs_lt.2 ⟨by linarith, hρ1⟩)).comp
      (tendsto_add_atTop_nat 1)
  obtain ⟨M, hM⟩ := ht.bddAbove_range
  refine ⟨max M 0, le_max_right _ _, fun x hx =>
    norm_padicLog_le_of_forall_le (le_max_right _ _) fun n => ?_⟩
  calc ‖logTerm x n‖ ≤ ((n + 1 : ℕ) : ℝ) ^ N * ‖x - 1‖ ^ (n + 1) := norm_logTerm_le hN x n
    _ ≤ ((n + 1 : ℕ) : ℝ) ^ N * ρ ^ (n + 1) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hρ _ hx) _) (by positivity)
    _ ≤ M := hM ⟨n, rfl⟩
    _ ≤ max M 0 := le_max_left _ _

/-- The log-shell is bounded. -/
theorem logShell_isBounded [CharZero k] (hp : p.Prime) (hpk : ‖(p : k)‖ < 1) :
    Bornology.IsBounded (logShell k p) := by
  obtain ⟨M, hM0, hM⟩ := exists_forall_norm_padicLog_le hp hpk
  refine isBounded_iff_forall_norm_le.2 ⟨‖(2 * (p : k))⁻¹‖ * M, ?_⟩
  rintro y ⟨u, hu, rfl⟩
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hM u hu) (norm_nonneg _)

/-- The log-shell is relatively compact (when `k` is proper, e.g. a finite extension of
`ℚ_p`). -/
theorem isCompact_closure_logShell [CharZero k] [ProperSpace k] (hp : p.Prime)
    (hpk : ‖(p : k)‖ < 1) : IsCompact (closure (logShell k p)) :=
  (logShell_isBounded hp hpk).isCompact_closure

/-- When `p` is odd and `p` is a uniformizer (`‖a‖ < 1 → ‖a‖ ≤ ‖p‖`, i.e. `k/ℚ_p` is
unramified), the log-shell is contained in the ring of integers. -/
theorem logShell_subset_closedBall [CharZero k] (hp : p.Prime) (hpk : ‖(p : k)‖ < 1)
    (hodd : Odd p) (hur : ∀ a : k, ‖a‖ < 1 → ‖a‖ ≤ ‖(p : k)‖) :
    logShell k p ⊆ Metric.closedBall (0 : k) 1 := by
  rintro y ⟨u, hu, rfl⟩
  rw [Metric.mem_closedBall, dist_zero_right, norm_mul, norm_inv, norm_mul,
    norm_two_eq_one hp hpk hodd, one_mul]
  have hp0 : 0 < ‖(p : k)‖ := norm_pos_iff.2 (Nat.cast_ne_zero.2 hp.ne_zero)
  rw [← div_eq_inv_mul, div_le_one hp0]
  exact norm_padicLog_le_norm_p hp hpk (hur _ hu)

variable [CompleteSpace k]

/-- The log-shell contains the ring of integers `{‖y‖ ≤ 1}` (IUT III, Proposition 1.2). -/
theorem closedBall_subset_logShell [CharZero k] (hp : p.Prime) (hpk : ‖(p : k)‖ < 1) :
    Metric.closedBall (0 : k) 1 ⊆ logShell k p := by
  intro y hy
  rw [Metric.mem_closedBall, dist_zero_right] at hy
  have h2p : (2 * (p : k)) ≠ 0 := mul_ne_zero two_ne_zero (Nat.cast_ne_zero.2 hp.ne_zero)
  obtain ⟨a, ha, hlog⟩ := exists_padicLog_eq hp hpk (y := 2 * (p : k) * y)
    (by rw [norm_mul]; exact mul_le_of_le_one_right (norm_nonneg _) hy)
  refine ⟨1 + a, by simpa using ha.trans_lt (norm_two_mul_lt_one hpk), ?_⟩
  rw [hlog, inv_mul_cancel_left₀ h2p]

/-- The log-shell contains the valuation ring `𝓞_k`. -/
theorem integer_subset_logShell [CharZero k] (hp : p.Prime) (hpk : ‖(p : k)‖ < 1) :
    ((Valued.v.integer : Subring k) : Set k) ⊆ logShell k p := fun y hy =>
  closedBall_subset_logShell hp hpk
    (by rw [← Valued.toNormedField.setOf_mem_integer_eq_closedBall]; exact hy)

/-- At an odd prime `p` which is a uniformizer, the log-shell **is** the ring of integers
(IUT I, Definition 5.4.5; IUT IV, Proposition 1.4(iv)). -/
theorem logShell_eq_closedBall [CharZero k] (hp : p.Prime) (hpk : ‖(p : k)‖ < 1)
    (hodd : Odd p) (hur : ∀ a : k, ‖a‖ < 1 → ‖a‖ ≤ ‖(p : k)‖) :
    logShell k p = Metric.closedBall (0 : k) 1 :=
  (logShell_subset_closedBall hp hpk hodd hur).antisymm (closedBall_subset_logShell hp hpk)

theorem logShell_eq_integer [CharZero k] (hp : p.Prime) (hpk : ‖(p : k)‖ < 1)
    (hodd : Odd p) (hur : ∀ a : k, ‖a‖ < 1 → ‖a‖ ≤ ‖(p : k)‖) :
    logShell k p = ((Valued.v.integer : Subring k) : Set k) := by
  rw [logShell_eq_closedBall hp hpk hodd hur]
  ext y
  simp only [Metric.mem_closedBall, dist_zero_right, SetLike.mem_coe, Valuation.mem_integer_iff,
    Valued.toNormedField.norm_le_one_iff]

end LogShell

end

end Iut
