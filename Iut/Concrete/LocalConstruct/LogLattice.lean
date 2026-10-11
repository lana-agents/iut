/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Concrete.LocalConstruct.LocalLogShell

/-!
# The log-shell between two lattices (IUT IV, Proposition 1.2(i))

Let `k` be a complete discretely valued field of characteristic `0` with residue
characteristic `p` (`‖p‖ < 1`) and ramification index `e`. Write `ord x = log ‖x‖ / log ‖p‖`
(so `ord p = 1`). Mochizuki's constants (IUT IV, Proposition 1.2(i); cf. Koblitz, p. 81) are

* `a = (1/e) ⌈e/(p - 2)⌉` for `p > 2`, `a = 2` for `p = 2` (`Iut.logLatticeA`);
* `b = ⌊log (p e/(p - 1)) / log p⌋ - 1/e` (`Iut.logLatticeB`).

This file proves:

* **(L)** `Iut.mem_padicLog_image_of_norm_le`: every `y` with `‖y‖ ≤ ‖p‖ ^ a` (i.e.
  `ord y ≥ a`) lies in `log (1 + 𝔪_k)`; equivalently `(2p)⁻¹ y ∈ logShell k p`
  (`Iut.mem_logShell_of_norm_le`). This is a generalization of the contraction argument
  of `Iut.exists_padicLog_eq_KEEP` from the radius `‖2p‖` to any radius `‖p‖ ^ t` with `t >
  1/(p - 1)` (`Iut.exists_padicLog_eq_of_norm_le_rpow`), and it needs **no**
  discreteness hypothesis.
* **(U)** `Iut.norm_padicLog_le_logLatticeB`: `‖log u‖ ≤ ‖p‖ ^ (-b)` for every principal
  unit `u` (i.e. `ord (log u) ≥ -b`), under the discreteness hypothesis
  `∀ x, ‖x‖ < 1 → ‖x‖ ≤ ‖p‖ ^ (1/e)` (every element of the maximal ideal has `ord ≥ 1/e`);
  equivalently `‖2p‖ ‖y‖ ≤ ‖p‖ ^ (-b)` on the log-shell (`Iut.norm_le_of_mem_logShell`).
* **(A)** the arithmetic of `a`, `b`: `a + b = 0` when `p` is odd and `e ≤ p - 2`
  (`Iut.logLatticeA_add_B_eq_zero`), and `(a + b) log p ≤ 3 + log e` in general
  (`Iut.logLatticeA_add_B_le`; IUT IV states it for `p - 2 < e`, the other case being
  covered by `a + b = 0`).

The hypotheses are norm-level, so a caller with a concrete local field (an adic completion of a
number field) only has to supply `‖p‖ < 1`, completeness, and the discreteness bound.
-/

namespace Iut

open Filter Topology
open scoped Valued
open PadicLogVolume

universe u

noncomputable section

/-! ### Mochizuki's constants `a` and `b` -/

/-- Mochizuki's lower exponent `a` (IUT IV, Proposition 1.2(i)): `a = (1/e) ⌈e/(p - 2)⌉` if
`p ≠ 2`, and `a = 2` if `p = 2`. -/
def logLatticeA (p e : ℕ) : ℝ :=
  if p = 2 then 2 else (e : ℝ)⁻¹ * (⌈(e : ℝ) / ((p : ℝ) - 2)⌉ : ℝ)

/-- Mochizuki's upper exponent `b` (IUT IV, Proposition 1.2(i)):
`b = ⌊log (p e/(p - 1)) / log p⌋ - 1/e`. -/
def logLatticeB (p e : ℕ) : ℝ :=
  (⌊Real.log ((p : ℝ) * e / ((p : ℝ) - 1)) / Real.log p⌋ : ℝ) - (e : ℝ)⁻¹

/-- Bernoulli's inequality over `ℕ`: `1 + s (p - 1) ≤ p ^ s`. -/
theorem one_add_mul_sub_one_le_pow {p : ℕ} (hp : 1 ≤ p) (s : ℕ) : 1 + s * (p - 1) ≤ p ^ s := by
  have h := one_add_mul_le_pow (a := ((p : ℤ) - 1))
    (by have : (1 : ℤ) ≤ p := by exact_mod_cast hp
        linarith) s
  rw [add_sub_cancel] at h
  zify [hp]
  exact h

/-- `a > 1/(p - 1)`, the condition for the contraction argument. -/
theorem one_div_sub_one_lt_logLatticeA {p e : ℕ} (hp : 2 ≤ p) (he : 0 < e) :
    1 / ((p : ℝ) - 1) < logLatticeA p e := by
  unfold logLatticeA
  split_ifs with h2
  · subst h2
    norm_num
  · have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast (show 3 ≤ p by omega)
    have he0 : (0 : ℝ) < e := by exact_mod_cast he
    have hc := Int.le_ceil ((e : ℝ) / ((p : ℝ) - 2))
    calc 1 / ((p : ℝ) - 1) < 1 / ((p : ℝ) - 2) :=
          one_div_lt_one_div_of_lt (by linarith) (by linarith)
      _ = (e : ℝ)⁻¹ * ((e : ℝ) / ((p : ℝ) - 2)) := by field_simp
      _ ≤ (e : ℝ)⁻¹ * (⌈(e : ℝ) / ((p : ℝ) - 2)⌉ : ℝ) :=
          mul_le_mul_of_nonneg_left hc (by positivity)

/-- The integer part `N = ⌊log (p e/(p - 1)) / log p⌋` of `b` is a natural number with
`e < p ^ N (p - 1)`. -/
theorem exists_floor_logLattice_eq {p e : ℕ} (hp : 2 ≤ p) (he : 0 < e) :
    ∃ N : ℕ, ⌊Real.log ((p : ℝ) * e / ((p : ℝ) - 1)) / Real.log p⌋ = N ∧ e < p ^ N * (p - 1) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have he1 : (1 : ℝ) ≤ e := by exact_mod_cast he
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hlogp : 0 < Real.log p := Real.log_pos (by linarith)
  set X : ℝ := (p : ℝ) * e / ((p : ℝ) - 1) with hX
  have hX1 : 1 ≤ X := by
    rw [hX, le_div_iff₀ hp1]
    nlinarith
  have hL : 0 ≤ Real.log X / Real.log p := div_nonneg (Real.log_nonneg hX1) hlogp.le
  obtain ⟨N, hN⟩ := Int.eq_ofNat_of_zero_le (Int.floor_nonneg.2 hL)
  refine ⟨N, hN, ?_⟩
  have hlt := Int.lt_floor_add_one (Real.log X / Real.log p)
  rw [hN, div_lt_iff₀ hlogp] at hlt
  have hlt' : Real.log X < Real.log ((p : ℝ) ^ (N + 1)) := by
    rw [Real.log_pow]
    push_cast at hlt ⊢
    linarith
  rw [Real.log_lt_log_iff (by linarith) (by positivity), hX, div_lt_iff₀ hp1, pow_succ] at hlt'
  have hlt'' : (e : ℝ) < (p : ℝ) ^ N * ((p : ℝ) - 1) := by
    have hp0 : (0 : ℝ) < p := by linarith
    nlinarith
  have : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  exact_mod_cast (show (e : ℝ) < ((p ^ N * (p - 1) : ℕ) : ℝ) by push_cast [this]; exact hlt'')

/-- The exponent estimate behind (U): `n/e - v_p(n) ≥ 1/e - N` for `n ≥ 1`, in the integral form
`e v_p(n) + 1 ≤ n + e N`. -/
theorem mul_factorization_add_one_le {p e N n : ℕ} (hp : p.Prime) (heN : e < p ^ N * (p - 1))
    (hn : n ≠ 0) : e * n.factorization p + 1 ≤ n + e * N := by
  set v := n.factorization p
  have hpv : p ^ v ≤ n := Nat.ordProj_le p hn
  rcases le_or_gt v N with hvN | hvN
  · have := Nat.mul_le_mul_left e hvN
    omega
  · obtain ⟨s, hs⟩ : ∃ s, v = N + s := ⟨v - N, by omega⟩
    rw [hs] at hpv ⊢
    have hB := one_add_mul_sub_one_le_pow hp.one_le s
    have hpN : 1 ≤ p ^ N := Nat.one_le_pow _ _ hp.pos
    -- `n ≥ p ^ N p ^ s ≥ p ^ N (1 + s (p - 1)) ≥ 1 + s (e + 1)`
    have h1 : p ^ N * (1 + s * (p - 1)) ≤ n := by
      calc p ^ N * (1 + s * (p - 1)) ≤ p ^ N * p ^ s := Nat.mul_le_mul_left _ hB
        _ = p ^ (N + s) := (pow_add _ _ _).symm
        _ ≤ n := hpv
    have h2 : s * (e + 1) ≤ s * (p ^ N * (p - 1)) := Nat.mul_le_mul_left s heN
    have h3 : p ^ N * (1 + s * (p - 1)) = p ^ N + s * (p ^ N * (p - 1)) := by ring
    rw [h3] at h1
    have h4 : e * (N + s) = e * N + s * e := by ring
    rw [h4]
    nlinarith

/-! ### (A) The arithmetic of `a` and `b` -/

/-- **IUT IV, Proposition 1.2(i), the case `p` odd, `e ≤ p - 2`**: `a = 1/e = -b`, so
`a + b = 0`. -/
theorem logLatticeA_add_B_eq_zero {p e : ℕ} (hp : p ≠ 2) (he : 0 < e) (hep : e ≤ p - 2) :
    logLatticeA p e + logLatticeB p e = 0 := by
  have hp3 : 3 ≤ p := by omega
  have hp3' : (3 : ℝ) ≤ p := by exact_mod_cast hp3
  have he1 : (1 : ℝ) ≤ e := by exact_mod_cast he
  have hep' : (e : ℝ) ≤ (p : ℝ) - 2 := by
    have : ((p - 2 : ℕ) : ℝ) = (p : ℝ) - 2 := by rw [Nat.cast_sub (by omega)]; norm_num
    rw [← this]
    exact_mod_cast hep
  have hceil : ⌈(e : ℝ) / ((p : ℝ) - 2)⌉ = 1 := by
    rw [Int.ceil_eq_iff]
    constructor
    · rw [Int.cast_one, sub_self]
      exact div_pos (by linarith) (by linarith)
    · rw [Int.cast_one, div_le_one (by linarith)]
      exact hep'
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hfloor : ⌊Real.log ((p : ℝ) * e / ((p : ℝ) - 1)) / Real.log p⌋ = 0 := by
    have hlogp : 0 < Real.log p := Real.log_pos (by linarith)
    rw [Int.floor_eq_zero_iff, Set.mem_Ico]
    have hX0 : 0 < (p : ℝ) * e / ((p : ℝ) - 1) := by positivity
    constructor
    · refine div_nonneg (Real.log_nonneg ?_) hlogp.le
      rw [le_div_iff₀ hp1]
      nlinarith
    · rw [div_lt_one hlogp, Real.log_lt_log_iff hX0 (by linarith), div_lt_iff₀ hp1]
      nlinarith
  unfold logLatticeA logLatticeB
  rw [if_neg hp, hceil, hfloor]
  simp

/-- **IUT IV, Proposition 1.2(i), the estimate `(a + b) log p ≤ 3 + log e`.** Mochizuki states it
for `p - 2 < e`; it holds for every prime `p` and every `e ≥ 1` (for `p` odd and `e ≤ p - 2` one
has `a + b = 0`, `logLatticeA_add_B_eq_zero`). Proof: for `p > 2`, `a - 1/e ≤ 1/(p - 2)` and
`log p/(p - 2) ≤ (p - 1)/(p - 2) ≤ 2`; `(b + 1/e) log p ≤ log (p e/(p - 1)) ≤ log (2e)`
`≤ 1 + log e`. For `p = 2`, `(a + b) log 2 ≤ 2 log 2 + log (2e) = 3 log 2 + log e`. -/
theorem logLatticeA_add_B_le {p e : ℕ} (hp : 2 ≤ p) (he : 0 < e) :
    (logLatticeA p e + logLatticeB p e) * Real.log p ≤ 3 + Real.log e := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have he1 : (1 : ℝ) ≤ e := by exact_mod_cast he
  have he0 : (0 : ℝ) < e := by linarith
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hlogp : 0 < Real.log p := Real.log_pos (by linarith)
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_two_lt_d9
    norm_num at this
    linarith
  set X : ℝ := (p : ℝ) * e / ((p : ℝ) - 1) with hX
  have hX0 : 0 < X := by positivity
  have hX2 : X ≤ 2 * e := by
    rw [hX, div_le_iff₀ hp1]
    nlinarith
  have hlogX : Real.log X ≤ Real.log 2 + Real.log e := by
    rw [← Real.log_mul (by norm_num) he0.ne']
    exact Real.log_le_log hX0 hX2
  -- `⌊L⌋ log p ≤ log X`
  have hfl : (⌊Real.log X / Real.log p⌋ : ℝ) * Real.log p ≤ Real.log X := by
    have := Int.floor_le (Real.log X / Real.log p)
    rw [le_div_iff₀ hlogp] at this
    exact this
  have hinv : 0 ≤ (e : ℝ)⁻¹ * Real.log p := by positivity
  unfold logLatticeA logLatticeB
  rw [← hX]
  split_ifs with h2
  · subst h2
    have : ((2 : ℕ) : ℝ) = 2 := by norm_num
    rw [this] at hfl hinv ⊢
    nlinarith
  · have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast (show 3 ≤ p by omega)
    -- `a ≤ 1/(p - 2) + 1/e`
    have hc := Int.ceil_lt_add_one ((e : ℝ) / ((p : ℝ) - 2))
    have ha : (e : ℝ)⁻¹ * (⌈(e : ℝ) / ((p : ℝ) - 2)⌉ : ℝ) ≤ 1 / ((p : ℝ) - 2) + (e : ℝ)⁻¹ := by
      calc (e : ℝ)⁻¹ * (⌈(e : ℝ) / ((p : ℝ) - 2)⌉ : ℝ)
          ≤ (e : ℝ)⁻¹ * ((e : ℝ) / ((p : ℝ) - 2) + 1) :=
            mul_le_mul_of_nonneg_left hc.le (by positivity)
        _ = 1 / ((p : ℝ) - 2) + (e : ℝ)⁻¹ := by field_simp
    -- `log p / (p - 2) ≤ 2`
    have hlp : 1 / ((p : ℝ) - 2) * Real.log p ≤ 2 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < p by linarith)
      rw [one_div_mul_eq_div, div_le_iff₀ (by linarith)]
      linarith
    have := mul_le_mul_of_nonneg_right ha hlogp.le
    nlinarith

/-! ### (L) The lower lattice: `p ^ a 𝓞 ⊆ log (1 + 𝔪)` -/

variable {k : Type u} [Field k] [Valued k (WithZero (Multiplicative ℤ))]
  [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))]

section Lower

variable {p : ℕ}

/-- The termwise Lipschitz estimate for the remainder `log (1 + a) - a` on a ball of radius `r`,
given `r ^ (m - 1) ≤ c ‖m‖` for all `m ≥ 2` (generalizing `norm_logTerm_sub_le`). -/
theorem norm_logTerm_sub_le_of_pow_le [CharZero k] {r c : ℝ} (hr0 : 0 ≤ r)
    (hrc : ∀ m : ℕ, 2 ≤ m → r ^ (m - 1) ≤ c * ‖(m : k)‖) {a b : k} (ha : ‖a‖ ≤ r)
    (hb : ‖b‖ ≤ r) (n : ℕ) :
    ‖logTerm (1 + a) (n + 1) - logTerm (1 + b) (n + 1)‖ ≤ c * ‖a - b‖ := by
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
  have hsum : ‖∑ i ∈ Finset.range (n + 2), a ^ i * b ^ (n + 2 - 1 - i)‖ ≤ r ^ (n + 2 - 1) := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (pow_nonneg hr0 _) fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [norm_mul, norm_pow, norm_pow]
    calc ‖a‖ ^ i * ‖b‖ ^ (n + 2 - 1 - i)
        ≤ r ^ i * r ^ (n + 2 - 1 - i) :=
          mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) ha _)
            (pow_le_pow_left₀ (norm_nonneg _) hb _) (by positivity) (pow_nonneg hr0 _)
      _ = r ^ (n + 2 - 1) := by
          rw [← pow_add]
          congr 1
          omega
  calc ‖∑ i ∈ Finset.range (n + 2), a ^ i * b ^ (n + 2 - 1 - i)‖ * ‖a - b‖
      ≤ r ^ (n + 2 - 1) * ‖a - b‖ := mul_le_mul_of_nonneg_right hsum (norm_nonneg _)
    _ ≤ (c * ‖((n + 2 : ℕ) : k)‖) * ‖a - b‖ :=
        mul_le_mul_of_nonneg_right (hrc _ (by omega)) (norm_nonneg _)
    _ = c * ‖a - b‖ * ‖((n + 2 : ℕ) : k)‖ := by ring

variable [CompleteSpace k]

/-- The remainder `a ↦ log (1 + a) - a` is `c`-Lipschitz on the ball of radius `r < 1`, given
`r ^ (m - 1) ≤ c ‖m‖` for all `m ≥ 2`. -/
theorem norm_logRem_sub_le_of_pow_le [CharZero k] (hp : p.Prime) (hpk : ‖(p : k)‖ < 1)
    {r c : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (hc0 : 0 ≤ c)
    (hrc : ∀ m : ℕ, 2 ≤ m → r ^ (m - 1) ≤ c * ‖(m : k)‖) {a b : k} (ha : ‖a‖ ≤ r)
    (hb : ‖b‖ ≤ r) : ‖logRem a - logRem b‖ ≤ c * ‖a - b‖ := by
  have ha' : ‖(1 + a) - 1‖ < 1 := by simpa using ha.trans_lt hr1
  have hb' : ‖(1 + b) - 1‖ < 1 := by simpa using hb.trans_lt hr1
  unfold logRem
  rw [← Summable.tsum_sub ((summable_nat_add_iff 1).2 (summable_logTerm hp hpk ha'))
    ((summable_nat_add_iff 1).2 (summable_logTerm hp hpk hb'))]
  exact IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (mul_nonneg hc0 (norm_nonneg _))
    (norm_logTerm_sub_le_of_pow_le hr0 hrc ha hb)

/-- **Surjectivity of the logarithm on a ball of radius `r`** (generalizing
`exists_padicLog_eq`): if `r < 1` and `r ^ (m - 1) ≤ c ‖m‖` for all `m ≥ 2` with `c < 1`, every
`y` with `‖y‖ ≤ r` is `log (1 + a)` for some `a` with `‖a‖ ≤ r`. -/
theorem exists_padicLog_eq_of_pow_le [CharZero k] (hp : p.Prime) (hpk : ‖(p : k)‖ < 1)
    {r c : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hrc : ∀ m : ℕ, 2 ≤ m → r ^ (m - 1) ≤ c * ‖(m : k)‖) {y : k} (hy : ‖y‖ ≤ r) :
    ∃ a : k, ‖a‖ ≤ r ∧ padicLog (1 + a) = y := by
  let T : k → k := fun a => y - logRem a
  have hT : Set.MapsTo T (Metric.closedBall 0 r) (Metric.closedBall 0 r) := by
    intro a ha
    rw [Metric.mem_closedBall, dist_zero_right] at ha ⊢
    have hrem : ‖logRem a‖ ≤ c * ‖a‖ := by
      simpa using norm_logRem_sub_le_of_pow_le hp hpk hr0 hr1 hc0 hrc ha (b := 0)
        (by simpa using hr0)
    calc ‖y - logRem a‖ ≤ max ‖y‖ ‖logRem a‖ := by
          rw [sub_eq_add_neg]
          simpa using IsUltrametricDist.norm_add_le_max y (-logRem a)
      _ ≤ r := max_le hy (hrem.trans ((mul_le_of_le_one_left (norm_nonneg _) hc1.le).trans ha))
  have hc : ContractingWith (⟨c, hc0⟩ : NNReal) (hT.restrict T _ _) := by
    refine ⟨by rw [← NNReal.coe_lt_coe, NNReal.coe_one]; exact hc1,
      LipschitzWith.of_dist_le_mul fun a b => ?_⟩
    rw [Subtype.dist_eq, Subtype.dist_eq, dist_eq_norm, dist_eq_norm]
    have ha : ‖(a : k)‖ ≤ r := by
      have := a.2
      rwa [Metric.mem_closedBall, dist_zero_right] at this
    have hb : ‖(b : k)‖ ≤ r := by
      have := b.2
      rwa [Metric.mem_closedBall, dist_zero_right] at this
    change ‖(y - logRem (a : k)) - (y - logRem (b : k))‖ ≤ c * ‖(a : k) - (b : k)‖
    rw [sub_sub_sub_cancel_left, norm_sub_rev]
    exact norm_logRem_sub_le_of_pow_le hp hpk hr0 hr1 hc0 hrc ha hb
  obtain ⟨a, ha, hfix, -, -⟩ := ContractingWith.exists_fixedPoint'
    Metric.isClosed_closedBall.isComplete hT hc (x := 0)
    (Metric.mem_closedBall_self hr0) (edist_ne_top _ _)
  rw [Metric.mem_closedBall, dist_zero_right] at ha
  refine ⟨a, ha, ?_⟩
  have hfix' : y - logRem a = a := hfix
  rw [padicLog_one_add hp hpk (ha.trans_lt hr1)]
  linear_combination -hfix'

omit [CompleteSpace k] in
/-- The numeric estimate for the radius `‖p‖ ^ t` with `t ≥ 1/(p - 1)`:
`(‖p‖ ^ t) ^ (m - 1) ≤ ‖p‖ ^ (t - 1/(p - 1)) ‖m‖` for `m ≥ 2` (using
`v_p(m) ≤ (m - 1)/(p - 1)`). -/
theorem rpow_pow_le_mul_norm_natCast [CharZero k] (hp : p.Prime) (hpk : ‖(p : k)‖ < 1)
    {t : ℝ} (ht : 1 / ((p : ℝ) - 1) ≤ t) {m : ℕ} (hm : 2 ≤ m) :
    (‖(p : k)‖ ^ t) ^ (m - 1) ≤ ‖(p : k)‖ ^ (t - 1 / ((p : ℝ) - 1)) * ‖(m : k)‖ := by
  have hp0 : (0 : ℝ) < ‖(p : k)‖ := norm_pos_iff.2 (Nat.cast_ne_zero.2 hp.ne_zero)
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hm0 : m ≠ 0 := by omega
  rw [norm_natCast_eq_pow hp hpk hm0]
  set v := m.factorization p
  have hpv : ((p : ℝ) ^ v) ≤ m := by exact_mod_cast Nat.ordProj_le p hm0
  have hbern := one_add_mul_le_pow (a := ((p : ℝ) - 1)) (by linarith) v
  rw [add_sub_cancel] at hbern
  have hv : (v : ℝ) ≤ ((m : ℝ) - 1) / ((p : ℝ) - 1) := by
    rw [le_div_iff₀ hp1]
    linarith
  set q : ℝ := 1 / ((p : ℝ) - 1) with hq
  have hvq : (v : ℝ) ≤ ((m : ℝ) - 1) * q := by rwa [hq, ← div_eq_mul_one_div]
  have e1 : (‖(p : k)‖ ^ t) ^ (m - 1) = ‖(p : k)‖ ^ (t * ((m : ℝ) - 1)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), Nat.cast_sub (by omega),
      Nat.cast_one]
  have e2 : ‖(p : k)‖ ^ (t - q) * ‖(p : k)‖ ^ v = ‖(p : k)‖ ^ (t - q + v) := by
    rw [Real.rpow_add hp0, Real.rpow_natCast]
  rw [e1, e2]
  refine Real.rpow_le_rpow_of_exponent_ge hp0 hpk.le ?_
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  nlinarith [mul_nonneg (sub_nonneg.2 ht) (sub_nonneg.2 hm2)]

/-- **Surjectivity of the logarithm on the ball of radius `‖p‖ ^ t`, `t > 1/(p - 1)`**: every
`y` with `‖y‖ ≤ ‖p‖ ^ t` is `log (1 + a)` for some `a` with `‖a‖ ≤ ‖p‖ ^ t`. -/
theorem exists_padicLog_eq_of_norm_le_rpow [CharZero k] (hp : p.Prime) (hpk : ‖(p : k)‖ < 1)
    {t : ℝ} (ht : 1 / ((p : ℝ) - 1) < t) {y : k} (hy : ‖y‖ ≤ ‖(p : k)‖ ^ t) :
    ∃ a : k, ‖a‖ ≤ ‖(p : k)‖ ^ t ∧ padicLog (1 + a) = y := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hq : 0 < 1 / ((p : ℝ) - 1) := one_div_pos.2 (by linarith)
  exact exists_padicLog_eq_of_pow_le hp hpk (Real.rpow_nonneg (norm_nonneg _) _)
    (Real.rpow_lt_one (norm_nonneg _) hpk (hq.trans ht)) (Real.rpow_nonneg (norm_nonneg _) _)
    (Real.rpow_lt_one (norm_nonneg _) hpk (sub_pos.2 ht))
    (fun m hm => rpow_pow_le_mul_norm_natCast hp hpk ht.le hm) hy

/-- **(L) IUT IV, Proposition 1.2(i), lower bound**: every `y` with `ord y ≥ a`, i.e.
`‖y‖ ≤ ‖p‖ ^ a`, is the logarithm of a principal unit `u = 1 + x` with `‖x‖ ≤ ‖p‖ ^ a`.
No discreteness hypothesis is needed. -/
theorem mem_padicLog_image_of_norm_le [CharZero k] (hp : p.Prime) (hpk : ‖(p : k)‖ < 1)
    {e : ℕ} (he : 0 < e) {y : k} (hy : ‖y‖ ≤ ‖(p : k)‖ ^ logLatticeA p e) :
    ∃ u : k, ‖u - 1‖ < 1 ∧ padicLog u = y := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have ht := one_div_sub_one_lt_logLatticeA hp.two_le he
  obtain ⟨a, ha, hlog⟩ := exists_padicLog_eq_of_norm_le_rpow hp hpk ht hy
  have hq : 0 < 1 / ((p : ℝ) - 1) := one_div_pos.2 (by linarith)
  refine ⟨1 + a, ?_, hlog⟩
  simpa using ha.trans_lt (Real.rpow_lt_one (norm_nonneg _) hpk (hq.trans ht))

/-- **(L), log-shell form**: `(2p)⁻¹ · p ^ a 𝓞 ⊆ 𝓘`, i.e. `(2p)⁻¹ y ∈ logShell k p` whenever
`‖y‖ ≤ ‖p‖ ^ a`. -/
theorem mem_logShell_of_norm_le [CharZero k] (hp : p.Prime) (hpk : ‖(p : k)‖ < 1)
    {e : ℕ} (he : 0 < e) {y : k} (hy : ‖y‖ ≤ ‖(p : k)‖ ^ logLatticeA p e) :
    (2 * (p : k))⁻¹ * y ∈ logShell k p := by
  obtain ⟨u, hu, hlog⟩ := mem_padicLog_image_of_norm_le hp hpk he hy
  exact ⟨u, hu, by rw [hlog]⟩

end Lower

/-! ### (U) The upper lattice: `log (1 + 𝔪) ⊆ p ^ (-b) 𝓞` -/

section Upper

variable {p : ℕ}

/-- The termwise bound behind (U): under the discreteness hypothesis
`‖x‖ < 1 → ‖x‖ ≤ ‖p‖ ^ (1/e)`, every term of the logarithm series of a principal unit has norm
`≤ ‖p‖ ^ (-b)`. -/
theorem norm_logTerm_le_logLatticeB [CharZero k] (hp : p.Prime) (hpk : ‖(p : k)‖ < 1)
    {e : ℕ} (he : 0 < e) (hdisc : ∀ x : k, ‖x‖ < 1 → ‖x‖ ≤ ‖(p : k)‖ ^ ((e : ℝ)⁻¹))
    {u : k} (hu : ‖u - 1‖ < 1) (n : ℕ) :
    ‖logTerm u n‖ ≤ ‖(p : k)‖ ^ (-logLatticeB p e) := by
  have hp0 : (0 : ℝ) < ‖(p : k)‖ := norm_pos_iff.2 (Nat.cast_ne_zero.2 hp.ne_zero)
  have he0 : (0 : ℝ) < e := by exact_mod_cast he
  obtain ⟨N, hN, heN⟩ := exists_floor_logLattice_eq hp.two_le he
  have hb : -logLatticeB p e = (e : ℝ)⁻¹ - N := by
    unfold logLatticeB
    rw [hN]
    push_cast
    ring
  rw [hb, norm_logTerm, norm_natCast_eq_pow hp hpk (Nat.succ_ne_zero n)]
  set v := (n + 1).factorization p
  have hkey := mul_factorization_add_one_le hp heN (Nat.succ_ne_zero n)
  have hkey' : (e : ℝ) * v + 1 ≤ ((n + 1 : ℕ) : ℝ) + e * N := by exact_mod_cast hkey
  have h1 : ‖u - 1‖ ^ (n + 1) ≤ ‖(p : k)‖ ^ (((n + 1 : ℕ) : ℝ) * (e : ℝ)⁻¹) := by
    rw [mul_comm, Real.rpow_mul (norm_nonneg _), Real.rpow_natCast]
    exact pow_le_pow_left₀ (norm_nonneg _) (hdisc _ hu) _
  have h2 : (‖(p : k)‖ ^ v)⁻¹ = ‖(p : k)‖ ^ (-(v : ℝ)) := by
    rw [Real.rpow_neg (norm_nonneg _), Real.rpow_natCast]
  rw [h2]
  calc ‖u - 1‖ ^ (n + 1) * ‖(p : k)‖ ^ (-(v : ℝ))
      ≤ ‖(p : k)‖ ^ (((n + 1 : ℕ) : ℝ) * (e : ℝ)⁻¹) * ‖(p : k)‖ ^ (-(v : ℝ)) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = ‖(p : k)‖ ^ (((n + 1 : ℕ) : ℝ) * (e : ℝ)⁻¹ - v) := by
        rw [← Real.rpow_add hp0, sub_eq_add_neg]
    _ ≤ ‖(p : k)‖ ^ ((e : ℝ)⁻¹ - N) := by
        refine Real.rpow_le_rpow_of_exponent_ge hp0 hpk.le ?_
        rw [sub_le_sub_iff, ← sub_nonneg]
        have : ((n + 1 : ℕ) : ℝ) * (e : ℝ)⁻¹ + N - ((e : ℝ)⁻¹ + v) =
            (((n + 1 : ℕ) : ℝ) + e * N - (e * v + 1)) * (e : ℝ)⁻¹ := by
          field_simp
          ring
        rw [this]
        exact mul_nonneg (by linarith) (by positivity)

/-- **(U) IUT IV, Proposition 1.2(i), upper bound**: under the discreteness hypothesis
`hdisc : ∀ x, ‖x‖ < 1 → ‖x‖ ≤ ‖p‖ ^ (1/e)` (every element of the maximal ideal has
`ord ≥ 1/e`; e.g. `e` the ramification index), every principal unit `u` satisfies
`‖log u‖ ≤ ‖p‖ ^ (-b)`, i.e. `ord (log u) ≥ -b`. -/
theorem norm_padicLog_le_logLatticeB [CharZero k] (hp : p.Prime) (hpk : ‖(p : k)‖ < 1)
    {e : ℕ} (he : 0 < e) (hdisc : ∀ x : k, ‖x‖ < 1 → ‖x‖ ≤ ‖(p : k)‖ ^ ((e : ℝ)⁻¹))
    {u : k} (hu : ‖u - 1‖ < 1) : ‖padicLog u‖ ≤ ‖(p : k)‖ ^ (-logLatticeB p e) :=
  norm_padicLog_le_of_forall_le (Real.rpow_nonneg (norm_nonneg _) _)
    (norm_logTerm_le_logLatticeB hp hpk he hdisc hu)

/-- **(U), log-shell form**: `𝓘 ⊆ (2p)⁻¹ · p ^ (-b) 𝓞`, i.e. `‖2p‖ ‖y‖ ≤ ‖p‖ ^ (-b)` for
`y ∈ logShell k p`. -/
theorem norm_le_of_mem_logShell [CharZero k] (hp : p.Prime) (hpk : ‖(p : k)‖ < 1)
    {e : ℕ} (he : 0 < e) (hdisc : ∀ x : k, ‖x‖ < 1 → ‖x‖ ≤ ‖(p : k)‖ ^ ((e : ℝ)⁻¹))
    {y : k} (hy : y ∈ logShell k p) : ‖2 * (p : k)‖ * ‖y‖ ≤ ‖(p : k)‖ ^ (-logLatticeB p e) := by
  obtain ⟨u, hu, rfl⟩ := hy
  have h2p : (2 * (p : k)) ≠ 0 := mul_ne_zero two_ne_zero (Nat.cast_ne_zero.2 hp.ne_zero)
  rw [← norm_mul, mul_inv_cancel_left₀ h2p]
  exact norm_padicLog_le_logLatticeB hp hpk he hdisc hu

end Upper

end

end Iut
