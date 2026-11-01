/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.Tempered.RatFunTheta
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Zeros of entire Laurent series: the Newton polygon (MR18 T8, route B-an)

Over a complete ultrametric **algebraically closed** field `K` (e.g. `ℂ_p`), an entire Laurent
series `f ∈ E(K)` has a zero on every circle `|U| = ‖u₀‖` on which its Newton polygon has an edge,
i.e. on which the lowest and the highest dominant index differ (`exists_zero_of_lo_lt_hi`).
Consequently a zero-free `f ∈ E(K)` is a monomial `a·Uᵏ` (`eq_smul_mono_of_ne_zero`): the
divisor of zeros of an entire Laurent series sees all of `f` up to `a·Uᵏ`. This is the analytic
input of [EtTh] Proposition 3.2(ii),(iii), Proposition 3.4(ii) on `𝔾_m^an` that [EtTh] takes from
the special fibre of the stable model.

The proof avoids Weierstrass preparation: the truncations `Q_M = U^M ∑_{|n| ≤ M} cₙ Uⁿ` are
polynomials that split over `K`; by the Gauss lemma (`RatFunGauss.lean`) the number of their roots
on the unit circle equals the width `hi - lo` of the Newton polygon of `f` there (for `M` large),
and `|Q_M(β)| = |Q_M|₁ · ∏_{|γ| = 1} |β - γ|`. Starting from a root of `Q_{M₀}`, each root of
`Q_{M_k}` is close to a root of `Q_{M_{k+1}}`; the roots form a Cauchy sequence, whose limit is a
zero of `f` (`f` is `|f|₁`-Lipschitz on the unit circle).

## Main results

* `polyE` (polynomials as entire series), `width_prod_lin`, `norm_eval_prod_lin`,
  `exists_unit_root_close`.
* `exists_zero_of_lo_lt_hi_one`, `exists_zero_of_lo_lt_hi` (**Newton polygon zero existence**).
* `lo_eq_hi_of_no_zero`, `exists_lo_const`, `eq_smul_mono_of_ne_zero` (**zero-free ⇒ `a·Uᵏ`**).
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace Iut.Frobenioid.BAn

open Polynomial Filter Topology

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]

/-! ### Polynomials as entire Laurent series -/

/-- The Laurent coefficient family of a polynomial. -/
def polyCoeff (p : K[X]) (n : ℤ) : K := if 0 ≤ n then p.coeff n.toNat else 0

lemma polyCoeff_natCast (p : K[X]) (i : ℕ) : polyCoeff p i = p.coeff i := by
  simp [polyCoeff]

lemma polyCoeff_of_neg (p : K[X]) {n : ℤ} (hn : n < 0) : polyCoeff p n = 0 := by
  simp [polyCoeff, not_le.mpr hn]

lemma hasSum_polyCoeff (p : K[X]) (u : Kˣ) :
    HasSum (fun n : ℤ => polyCoeff p n * (u : K) ^ n) (p.eval (u : K)) := by
  rw [eval_eq_sum_range]
  have h : HasSum (fun n : ℤ => polyCoeff p n * (u : K) ^ n)
      (∑ n ∈ (Finset.range (p.natDegree + 1)).map Nat.castEmbedding,
        polyCoeff p n * (u : K) ^ n) := hasSum_sum_of_ne_finset_zero (fun n hn => by
      rcases lt_or_ge n 0 with hn0 | hn0
      · simp [polyCoeff_of_neg p hn0]
      · obtain ⟨i, rfl⟩ := Int.eq_ofNat_of_zero_le hn0
        have hi : p.natDegree < i := by
          by_contra hi
          exact hn (Finset.mem_map.mpr ⟨i, Finset.mem_range.mpr (by omega), rfl⟩)
        simp [polyCoeff_natCast, coeff_eq_zero_of_natDegree_lt hi])
  convert h using 1
  rw [Finset.sum_map]
  exact Finset.sum_congr rfl fun i _ => by simp [polyCoeff_natCast]

/-- A polynomial as an element of `E(K)`. -/
def polyE (p : K[X]) : Entire K :=
  Entire.ofCoeff (polyCoeff p) fun u => (hasSum_polyCoeff p u).summable

lemma coeff_polyE (p : K[X]) : Entire.coeff (polyE p) = polyCoeff p := Entire.coeff_ofCoeff _ _

lemma coe_polyE (p : K[X]) : ((polyE p : Entire K) : Kˣ → K) = fun u : Kˣ => p.eval (u : K) :=
  funext fun u => (hasSum_polyCoeff p u).tsum_eq

lemma polyE_mul (p q : K[X]) : polyE (p * q) = polyE p * polyE q :=
  Subtype.ext (by rw [Entire.coe_mul, coe_polyE, coe_polyE, coe_polyE]; funext u; simp)

lemma polyE_C (a : K) : polyE (C a) = algebraMap K (Entire K) a :=
  Subtype.ext (by rw [coe_polyE, Entire.coe_algebraMap]; funext u; simp)

lemma polyE_ne_zero {p : K[X]} (hp : p ≠ 0) : polyE p ≠ 0 := by
  intro h
  apply hp
  ext i
  have := congrFun (congrArg Entire.coeff h) i
  rw [coeff_polyE, Entire.coeff_zero, polyCoeff_natCast] at this
  simpa using this

/-! ### Linear factors -/

/-- The linear factor `X - γ`. -/
abbrev lin (γ : K) : K[X] := X - C γ

lemma tnorm_lin (γ : K) (n : ℤ) :
    tnorm (polyCoeff (lin γ)) 1 n = if n = 0 then ‖γ‖ else if n = 1 then 1 else 0 := by
  rcases lt_or_ge n 0 with hn | hn
  · rw [tnorm, polyCoeff_of_neg _ hn, if_neg (by omega), if_neg (by omega)]; simp
  · obtain ⟨i, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    rw [tnorm, polyCoeff_natCast, one_zpow, mul_one]
    rcases i with _ | _ | i
    · simp
    · simp
    · rw [if_neg (by omega), if_neg (by omega)]
      simp [coeff_X]

lemma isEntire_lin (γ : K) : IsEntire (polyCoeff (lin γ)) := by
  rw [← coeff_polyE]; exact Entire.isEntire_coeff _

lemma lin_ne_zero (γ : K) : polyCoeff (lin γ) ≠ 0 := by
  intro h
  have := congrFun h 1
  rw [show (1 : ℤ) = ((1 : ℕ) : ℤ) by rfl, polyCoeff_natCast] at this
  simp [coeff_X] at this

lemma gnorm_lin (γ : K) : gnorm (polyCoeff (lin γ)) 1 = max 1 ‖γ‖ := by
  refine le_antisymm (gnorm_le fun n => ?_) (max_le ?_ ?_)
  · rw [tnorm_lin]
    split_ifs
    · exact le_max_right _ _
    · exact le_max_left _ _
    · exact (zero_le_one).trans (le_max_left _ _)
  · have := le_gnorm (isEntire_lin γ) one_pos 1
    rwa [tnorm_lin, if_neg one_ne_zero, if_pos rfl] at this
  · have := le_gnorm (isEntire_lin γ) one_pos 0
    rwa [tnorm_lin, if_pos rfl] at this

lemma lo_hi_lin (γ : K) :
    hi (polyCoeff (lin γ)) 1 - lo (polyCoeff (lin γ)) 1 = if ‖γ‖ = 1 then 1 else 0 := by
  have hc := isEntire_lin γ
  have hc0 := lin_ne_zero γ
  have hg := gnorm_lin γ
  rcases lt_trichotomy ‖γ‖ 1 with h | h | h
  · rw [max_eq_left h.le] at hg
    have hlo : lo (polyCoeff (lin γ)) 1 = 1 := lo_eq_of hc hc0 one_pos
      (by rw [tnorm_lin, hg]; simp) fun m hm => by
        rw [tnorm_lin, hg]
        split_ifs with h0 h1
        · exact h
        · exact absurd h1 (by omega)
        · exact zero_lt_one
    have hhi : hi (polyCoeff (lin γ)) 1 = 1 := hi_eq_of hc hc0 one_pos
      (by rw [tnorm_lin, hg]; simp) fun m hm => by
        rw [tnorm_lin, hg, if_neg (by omega), if_neg (by omega)]; exact zero_lt_one
    rw [hlo, hhi, if_neg h.ne]; rfl
  · rw [h, max_self] at hg
    have hlo : lo (polyCoeff (lin γ)) 1 = 0 := lo_eq_of hc hc0 one_pos
      (by rw [tnorm_lin, hg, if_pos rfl, h]) fun m hm => by
        rw [tnorm_lin, hg, if_neg (by omega), if_neg (by omega)]; exact zero_lt_one
    have hhi : hi (polyCoeff (lin γ)) 1 = 1 := hi_eq_of hc hc0 one_pos
      (by rw [tnorm_lin, hg]; simp) fun m hm => by
        rw [tnorm_lin, hg, if_neg (by omega), if_neg (by omega)]; exact zero_lt_one
    rw [hlo, hhi, if_pos h]; rfl
  · rw [max_eq_right h.le] at hg
    have hlo : lo (polyCoeff (lin γ)) 1 = 0 := lo_eq_of hc hc0 one_pos
      (by rw [tnorm_lin, hg, if_pos rfl]) fun m hm => by
        rw [tnorm_lin, hg, if_neg (by omega), if_neg (by omega)]; exact one_pos.trans h
    have hhi : hi (polyCoeff (lin γ)) 1 = 0 := hi_eq_of hc hc0 one_pos
      (by rw [tnorm_lin, hg, if_pos rfl]) fun m hm => by
        rw [tnorm_lin, hg, if_neg (by omega)]
        split_ifs
        · exact h
        · exact one_pos.trans h
    rw [hlo, hhi, if_neg h.ne']; rfl

/-! ### Products of linear factors -/

/-- `∏_{γ ∈ s} (X - γ)`. -/
abbrev prodLin (s : Multiset K) : K[X] := (s.map lin).prod

lemma prodLin_cons (a : K) (s : Multiset K) : prodLin (a ::ₘ s) = lin a * prodLin s := by
  simp [prodLin]

lemma prodLin_ne_zero (s : Multiset K) : prodLin s ≠ 0 := by
  induction s using Multiset.induction_on with
  | empty => simp [prodLin]
  | cons a s ih => rw [prodLin_cons]; exact mul_ne_zero (X_sub_C_ne_zero a) ih

/-- The width `hi - lo` at radius `1` of a coefficient family. -/
def width (c : ℤ → K) : ℤ := hi c 1 - lo c 1

/-- **The width of `∏ (X - γ)` is the number of `γ` on the unit circle.** -/
theorem width_prod_lin (s : Multiset K) :
    width (polyCoeff (prodLin s)) = (s.filter fun γ => ‖γ‖ = 1).card := by
  induction s using Multiset.induction_on with
  | empty =>
    have h : polyCoeff (prodLin (0 : Multiset K)) = Pi.single 0 1 := by
      rw [← coeff_polyE, show prodLin (0 : Multiset K) = C 1 by simp [prodLin], polyE_C, map_one,
        Entire.coeff_one]
    rw [width, h, Entire.lo_single 0 1 one_ne_zero one_pos,
      Entire.hi_single 0 1 one_ne_zero one_pos]
    simp
  | cons a s ih =>
    rw [prodLin_cons, width, ← coeff_polyE, polyE_mul,
      Entire.hi_mul (polyE_ne_zero (X_sub_C_ne_zero a)) (polyE_ne_zero (prodLin_ne_zero s)) one_pos,
      Entire.lo_mul (polyE_ne_zero (X_sub_C_ne_zero a)) (polyE_ne_zero (prodLin_ne_zero s)) one_pos,
      coeff_polyE, coeff_polyE]
    have hl := lo_hi_lin a
    rw [width] at ih
    rw [Multiset.filter_cons]
    split_ifs at hl ⊢ with ha
    · rw [Multiset.singleton_add, Multiset.card_cons]; push_cast; linarith
    · rw [zero_add]; linarith

lemma gn_lin (γ : K) : Entire.gn (polyE (lin γ)) 1 = max 1 ‖γ‖ := by
  rw [Entire.gn, coeff_polyE, gnorm_lin]

/-- **Product formula on the unit circle**: for `‖β‖ = 1`,
`‖∏(β - γ)‖ = |∏ (X - γ)|₁ · ∏_{‖γ‖ = 1} ‖β - γ‖`. -/
theorem norm_eval_prod_lin (s : Multiset K) {β : K} (hβ : ‖β‖ = 1) :
    ‖(prodLin s).eval β‖ = Entire.gn (polyE (prodLin s)) 1 *
      ((s.filter fun γ => ‖γ‖ = 1).map fun γ => ‖β - γ‖).prod := by
  induction s using Multiset.induction_on with
  | empty =>
    simp only [prodLin, Multiset.map_zero, Multiset.prod_zero, eval_one, norm_one,
      Multiset.filter_zero, mul_one]
    rw [← map_one C, polyE_C, map_one, ← Entire.mono_zero, Entire.gn_mono 0 one_pos, zpow_zero]
  | cons a s ih =>
    rw [prodLin_cons, eval_mul, norm_mul, ih, polyE_mul, Entire.gn_mul _ _ one_pos, gn_lin,
      Multiset.filter_cons]
    simp only [lin, eval_sub, eval_X, eval_C]
    split_ifs with ha
    · rw [ha, max_self, Multiset.singleton_add, Multiset.map_cons, Multiset.prod_cons]; ring
    · have hne : ‖β‖ ≠ ‖-a‖ := by rw [hβ, norm_neg]; exact Ne.symm ha
      have : ‖β - a‖ = max 1 ‖a‖ := by
        rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, hβ, norm_neg]
      rw [this, zero_add]; ring

/-- A nonempty multiset of nonnegative reals has an element whose `card`-th power is below the
product. -/
lemma exists_pow_card_le_prod (t : Multiset ℝ) (ht : ∀ x ∈ t, 0 ≤ x) (hne : t ≠ 0) :
    ∃ x ∈ t, x ^ t.card ≤ t.prod := by
  induction t using Multiset.induction_on with
  | empty => exact absurd rfl hne
  | cons a t ih =>
    have ha : 0 ≤ a := ht a (Multiset.mem_cons_self a t)
    by_cases ht0 : t = 0
    · subst ht0; exact ⟨a, Multiset.mem_cons_self a 0, by simp⟩
    obtain ⟨x, hx, hxp⟩ := ih (fun y hy => ht y (Multiset.mem_cons_of_mem hy)) ht0
    have hx0 : 0 ≤ x := ht x (Multiset.mem_cons_of_mem hx)
    refine ⟨min a x, ?_, ?_⟩
    · rcases min_choice a x with h | h <;> rw [h]
      · exact Multiset.mem_cons_self a t
      · exact Multiset.mem_cons_of_mem hx
    · rw [Multiset.card_cons, pow_succ, Multiset.prod_cons, mul_comm]
      exact mul_le_mul (min_le_left _ _)
        ((pow_le_pow_left₀ (le_min ha hx0) (min_le_right _ _) _).trans hxp)
        (pow_nonneg (le_min ha hx0) _) ha

section AlgClosed

variable [IsAlgClosed K]

lemma prodLin_roots (p : K[X]) : C p.leadingCoeff * prodLin p.roots = p :=
  C_leadingCoeff_mul_prod_multiset_X_sub_C IsAlgClosed.card_roots_eq_natDegree

lemma width_poly {p : K[X]} (hp : p ≠ 0) :
    width (polyCoeff p) = (p.roots.filter fun γ => ‖γ‖ = 1).card := by
  have ha : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp
  have e : polyE p = p.leadingCoeff • (Entire.mono 0 * polyE (prodLin p.roots)) := by
    conv_lhs => rw [← prodLin_roots p]
    rw [polyE_mul, polyE_C, Entire.mono_zero, one_mul, Algebra.smul_def]
  rw [← width_prod_lin, width, width, ← coeff_polyE, e,
    Entire.hi_smul_mono_mul ha 0 (polyE_ne_zero (prodLin_ne_zero _)) one_pos,
    Entire.lo_smul_mono_mul ha 0 (polyE_ne_zero (prodLin_ne_zero _)) one_pos, coeff_polyE]
  ring

lemma norm_eval_poly {p : K[X]} {β : K} (hβ : ‖β‖ = 1) :
    ‖p.eval β‖ = Entire.gn (polyE p) 1 *
      ((p.roots.filter fun γ => ‖γ‖ = 1).map fun γ => ‖β - γ‖).prod := by
  have e : Entire.gn (polyE p) 1 = ‖p.leadingCoeff‖ * Entire.gn (polyE (prodLin p.roots)) 1 := by
    conv_lhs => rw [← prodLin_roots p]
    rw [polyE_mul, polyE_C, Entire.gn_mul _ _ one_pos, Entire.gn_algebraMap _ one_pos]
  have e2 : p.eval β = p.leadingCoeff * (prodLin p.roots).eval β := by
    conv_lhs => rw [← prodLin_roots p]
    rw [eval_mul, eval_C]
  rw [e2, e, norm_mul, norm_eval_prod_lin _ hβ, mul_assoc]

/-- **A unit-circle root of a polynomial near any point of the unit circle.** -/
theorem exists_unit_root_close {p : K[X]} (hp : p ≠ 0) (hw : 0 < width (polyCoeff p))
    {β : K} (hβ : ‖β‖ = 1) :
    ∃ γ, p.eval γ = 0 ∧ ‖γ‖ = 1 ∧
      ‖β - γ‖ ^ (width (polyCoeff p)).toNat * Entire.gn (polyE p) 1 ≤ ‖p.eval β‖ := by
  set t := (p.roots.filter fun γ => ‖γ‖ = 1).map fun γ => ‖β - γ‖
  have hcard : t.card = (width (polyCoeff p)).toNat := by
    rw [Multiset.card_map, width_poly hp, Int.toNat_natCast]
  have hne : t ≠ 0 := by
    intro h
    have := congrArg Multiset.card h
    rw [hcard, Multiset.card_zero] at this
    omega
  obtain ⟨x, hx, hxp⟩ := exists_pow_card_le_prod t (fun y hy => by
    obtain ⟨γ, -, rfl⟩ := Multiset.mem_map.mp hy; exact norm_nonneg _) hne
  obtain ⟨γ, hγ, rfl⟩ := Multiset.mem_map.mp hx
  obtain ⟨hγr, hγ1⟩ := Multiset.mem_filter.mp hγ
  refine ⟨γ, (mem_roots hp).mp hγr, hγ1, ?_⟩
  rw [norm_eval_poly hβ, ← hcard, mul_comm]
  exact mul_le_mul_of_nonneg_left hxp (gnorm_nonneg (Entire.isEntire_coeff _) one_pos)

end AlgClosed

/-! ### Truncations -/

section Trunc

variable (c : ℤ → K)

/-- The truncation `Q_M = ∑_{0 ≤ i ≤ 2M} c_{i-M} Xⁱ = U^M ∑_{|n| ≤ M} cₙ Uⁿ`. -/
def trunc (M : ℕ) : K[X] := ∑ i ∈ Finset.range (2 * M + 1), C (c ((i : ℤ) - M)) * X ^ i

lemma polyCoeff_trunc (M : ℕ) (n : ℤ) :
    polyCoeff (trunc c M) n = if 0 ≤ n ∧ n ≤ 2 * M then c (n - M) else 0 := by
  rcases lt_or_ge n 0 with hn | hn
  · rw [polyCoeff_of_neg _ hn, if_neg (by omega)]
  · obtain ⟨i, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    rw [polyCoeff_natCast, trunc, finsetSum_coeff]
    simp only [coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_range]
    by_cases hi : i < 2 * M + 1
    · rw [if_pos hi, if_pos ⟨by omega, by omega⟩]
    · rw [if_neg hi, if_neg (by omega)]

lemma tnorm_trunc (M : ℕ) (n : ℤ) :
    tnorm (polyCoeff (trunc c M)) 1 n = if 0 ≤ n ∧ n ≤ 2 * M then tnorm c 1 (n - M) else 0 := by
  rw [tnorm, polyCoeff_trunc]
  split_ifs <;> simp [tnorm]

variable {c}

lemma trunc_dom (hc : IsEntire c) (hc0 : c ≠ 0) {M : ℕ} (hlo : -(M : ℤ) ≤ lo c 1)
    (hhi : hi c 1 ≤ M) :
    gnorm (polyCoeff (trunc c M)) 1 = gnorm c 1 ∧
      lo (polyCoeff (trunc c M)) 1 = lo c 1 + M ∧ hi (polyCoeff (trunc c M)) 1 = hi c 1 + M ∧
      polyCoeff (trunc c M) ≠ 0 := by
  have hT : IsEntire (polyCoeff (trunc c M)) := by
    rw [← coeff_polyE]; exact Entire.isEntire_coeff _
  have hle := lo_le_hi hc hc0 one_pos
  have hG := gnorm_pos hc hc0 one_pos
  have h1 : tnorm (polyCoeff (trunc c M)) 1 (lo c 1 + M) = gnorm c 1 := by
    rw [tnorm_trunc, if_pos ⟨by omega, by omega⟩, add_sub_cancel_right, tnorm_lo hc hc0 one_pos]
  have h2 : tnorm (polyCoeff (trunc c M)) 1 (hi c 1 + M) = gnorm c 1 := by
    rw [tnorm_trunc, if_pos ⟨by omega, by omega⟩, add_sub_cancel_right, tnorm_hi hc hc0 one_pos]
  have hg : gnorm (polyCoeff (trunc c M)) 1 = gnorm c 1 := by
    refine le_antisymm (gnorm_le fun n => ?_) (h1.symm.le.trans (le_gnorm hT one_pos _))
    rw [tnorm_trunc]; split_ifs
    · exact le_gnorm hc one_pos _
    · exact hG.le
  have hne : polyCoeff (trunc c M) ≠ 0 := by
    intro h
    rw [h] at h1
    simp only [tnorm, Pi.zero_apply, norm_zero, zero_mul] at h1
    exact hG.ne h1
  refine ⟨hg, ?_, ?_, hne⟩
  · refine lo_eq_of hT hne one_pos (by rw [hg, h1]) fun m hm => ?_
    rw [hg, tnorm_trunc]; split_ifs
    · exact tnorm_lt_of_lt_lo hc hc0 one_pos (by omega)
    · exact hG
  · refine hi_eq_of hT hne one_pos (by rw [hg, h2]) fun m hm => ?_
    rw [hg, tnorm_trunc]; split_ifs
    · exact tnorm_lt_of_hi_lt hc hc0 one_pos (by omega)
    · exact hG

/-- `Q_M(β)` is `β^M f(β)` up to the tail `sup_{|n| > M} ‖cₙ‖`. -/
lemma norm_trunc_sub_le (hc : IsEntire c) (M : ℕ) (β : Kˣ) (hβ : ‖(β : K)‖ = 1) {ε : ℝ}
    (hε : 0 ≤ ε) (htail : ∀ n : ℤ, (M : ℤ) < |n| → ‖c n‖ ≤ ε) :
    ‖(trunc c M).eval (β : K) - (β : K) ^ M * lsum c β‖ ≤ ε := by
  have hβ0 : (β : K) ≠ 0 := β.ne_zero
  have h1 := hasSum_polyCoeff (trunc c M) β
  have h2 : HasSum (fun n : ℤ => c (n - M) * (β : K) ^ n) ((β : K) ^ M * lsum c β) := by
    have := ((Equiv.subRight (M : ℤ)).hasSum_iff.mpr (hc.hasSum β)).mul_left ((β : K) ^ M)
    refine this.congr_fun fun n => ?_
    simp only [Function.comp_apply, Equiv.subRight_apply]
    rw [mul_left_comm, ← zpow_natCast, ← zpow_add₀ hβ0, add_sub_cancel]
  rw [← (h1.sub h2).tsum_eq]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg hε fun n => ?_
  rw [← sub_mul, norm_mul, norm_zpow, hβ, one_zpow, mul_one, polyCoeff_trunc]
  split_ifs with h
  · simpa using hε
  · rw [zero_sub, norm_neg]
    exact htail _ (by rcases not_and_or.mp h with h | h <;> rw [lt_abs] <;> omega)

end Trunc

/-! ### Lipschitz bound on the unit circle -/

lemma norm_zpow_sub_zpow_le {x y : K} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (n : ℤ) :
    ‖x ^ n - y ^ n‖ ≤ ‖x - y‖ := by
  have hnat : ∀ m : ℕ, ‖x ^ m - y ^ m‖ ≤ ‖x - y‖ := fun m => by
    induction m with
    | zero => simp
    | succ m ih =>
      have e : x ^ (m + 1) - y ^ (m + 1) = x * (x ^ m - y ^ m) + (x - y) * y ^ m := by ring
      rw [e]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · rw [norm_mul, hx, one_mul]; exact ih
      · rw [norm_mul, norm_pow, hy, one_pow, mul_one]
  have hx0 : x ≠ 0 := by rw [← norm_ne_zero_iff, hx]; exact one_ne_zero
  have hy0 : y ≠ 0 := by rw [← norm_ne_zero_iff, hy]; exact one_ne_zero
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · simpa using hnat m
  · have e : x ^ (-(m : ℤ)) - y ^ (-(m : ℤ)) = -((x ^ m - y ^ m) * (x ^ m)⁻¹ * (y ^ m)⁻¹) := by
      simp only [zpow_neg, zpow_natCast]
      field_simp
      ring
    rw [e, norm_neg, norm_mul, norm_mul, norm_inv, norm_inv, norm_pow, norm_pow, hx, hy, one_pow,
      inv_one, mul_one, mul_one]
    exact hnat m

lemma norm_lsum_sub_le {c : ℤ → K} (hc : IsEntire c) {x y : Kˣ} (hx : ‖(x : K)‖ = 1)
    (hy : ‖(y : K)‖ = 1) : ‖lsum c x - lsum c y‖ ≤ gnorm c 1 * ‖(x : K) - y‖ := by
  rw [← ((hc.hasSum x).sub (hc.hasSum y)).tsum_eq]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg
    (mul_nonneg (gnorm_nonneg hc one_pos) (norm_nonneg _)) fun n => ?_
  rw [← mul_sub, norm_mul]
  refine mul_le_mul ?_ (norm_zpow_sub_zpow_le hx hy n) (norm_nonneg _) (gnorm_nonneg hc one_pos)
  have := le_gnorm hc one_pos n
  rwa [tnorm, one_zpow, mul_one] at this

/-! ### Zero existence -/

lemma exists_tail {c : ℤ → K} (hc : IsEntire c) {ε : ℝ} (hε : 0 < ε) :
    ∃ M₀ : ℕ, ∀ n : ℤ, (M₀ : ℤ) < |n| → ‖c n‖ < ε := by
  have hfin : {n : ℤ | ¬ tnorm c 1 n < ε}.Finite :=
    Filter.eventually_cofinite.mp ((hc.tendsto_tnorm one_pos).eventually (gt_mem_nhds hε))
  obtain ⟨B, hB⟩ := (hfin.image Int.natAbs).bddAbove
  refine ⟨B, fun n hn => ?_⟩
  by_contra h
  have hmem : n.natAbs ∈ Int.natAbs '' {n : ℤ | ¬ tnorm c 1 n < ε} :=
    ⟨n, by simpa [tnorm] using h, rfl⟩
  have := hB hmem
  have : |n| ≤ (B : ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast this
  omega


variable [IsAlgClosed K]

/-- **Newton polygon zero existence on the unit circle.** -/
theorem exists_zero_of_lo_lt_hi_one {c : ℤ → K} (hc : IsEntire c) (hc0 : c ≠ 0)
    (hw : lo c 1 < hi c 1) : ∃ u : Kˣ, ‖(u : K)‖ = 1 ∧ lsum c u = 0 := by
  set G := gnorm c 1
  have hG : 0 < G := gnorm_pos hc hc0 one_pos
  set w := width c
  have hw0 : 0 < w := by simp only [w, width]; omega
  set Mb : ℕ := (lo c 1).natAbs + (hi c 1).natAbs
  have hMlo : ∀ M : ℕ, Mb ≤ M → -(M : ℤ) ≤ lo c 1 := fun M hM => by
    have : ((lo c 1).natAbs : ℤ) ≤ M := by exact_mod_cast (Nat.le_add_right _ _).trans hM
    rw [← Int.abs_eq_natAbs] at this; rw [abs_le] at this; omega
  have hMhi : ∀ M : ℕ, Mb ≤ M → hi c 1 ≤ M := fun M hM => by
    have : ((hi c 1).natAbs : ℤ) ≤ M := by exact_mod_cast (Nat.le_add_left _ _).trans hM
    rw [← Int.abs_eq_natAbs] at this; rw [abs_le] at this; omega
  set δ : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hδ0 : ∀ k, 0 < δ k := fun k => by positivity
  have hδ1 : ∀ k, δ k ≤ 1 := fun k => by
    simp only [δ]; rw [div_le_one (by positivity)]; linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]
  have hδanti : ∀ k, δ (k + 1) ≤ δ k := fun k => by
    simp only [δ]; push_cast
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  -- the truncation levels
  have hlev : ∀ k : ℕ, ∃ M : ℕ, Mb ≤ M ∧ ∀ n : ℤ, (M : ℤ) < |n| →
      ‖c n‖ ≤ G * δ k ^ w.toNat := fun k => by
    obtain ⟨M₀, hM₀⟩ := exists_tail hc (mul_pos hG (pow_pos (hδ0 k) w.toNat))
    exact ⟨max Mb M₀, le_max_left _ _, fun n hn => (hM₀ n (by
      have := le_max_right Mb M₀; omega)).le⟩
  choose M hMb hMtail using hlev
  have hdom : ∀ k, gnorm (polyCoeff (trunc c (M k))) 1 = G ∧
      width (polyCoeff (trunc c (M k))) = w ∧ trunc c (M k) ≠ 0 := fun k => by
    obtain ⟨h1, h2, h3, h4⟩ := trunc_dom hc hc0 (hMlo _ (hMb k)) (hMhi _ (hMb k))
    refine ⟨h1, by simp only [width, w, h2, h3]; ring, fun h => h4 ?_⟩
    rw [h]; funext n; rcases lt_or_ge n 0 with hn | hn
    · exact polyCoeff_of_neg _ hn
    · obtain ⟨i, rfl⟩ := Int.eq_ofNat_of_zero_le hn; simp [polyCoeff_natCast]
  -- one step
  have hstep : ∀ (k : ℕ) (β : K), ‖β‖ = 1 → ∃ γ : K, (trunc c (M k)).eval γ = 0 ∧ ‖γ‖ = 1 ∧
      ‖β - γ‖ ^ w.toNat * G ≤ ‖(trunc c (M k)).eval β‖ := fun k β hβ => by
    obtain ⟨h1, h2, h3⟩ := hdom k
    have := exists_unit_root_close h3 (by rw [h2]; exact hw0) hβ
    rwa [h2, Entire.gn, coeff_polyE, h1] at this
  let step : ℕ → K → K := fun k β => if h : ‖β‖ = 1 then (hstep k β h).choose else 1
  have hstep1 : ∀ k β, ‖β‖ = 1 → ‖step k β‖ = 1 := fun k β h => by
    simp only [step, dif_pos h]; exact (hstep k β h).choose_spec.2.1
  let seq : ℕ → K := fun k => Nat.rec (step 0 1) (fun j β => step (j + 1) β) k
  have hseq0 : seq 0 = step 0 1 := rfl
  have hseqs : ∀ k, seq (k + 1) = step (k + 1) (seq k) := fun k => rfl
  have hnorm : ∀ k, ‖seq k‖ = 1 := fun k => by
    induction k with
    | zero => rw [hseq0]; exact hstep1 0 1 (by simp)
    | succ k ih => rw [hseqs]; exact hstep1 _ _ ih
  have hroot : ∀ k, (trunc c (M k)).eval (seq k) = 0 := fun k => by
    cases k with
    | zero =>
      rw [hseq0]; simp only [step, dif_pos (norm_one : ‖(1 : K)‖ = 1)]
      exact (hstep 0 1 norm_one).choose_spec.1
    | succ k =>
      rw [hseqs]; simp only [step, dif_pos (hnorm k)]
      exact (hstep _ _ (hnorm k)).choose_spec.1
  let unit : ℕ → Kˣ := fun k => Units.mk0 (seq k) (by
    rw [← norm_ne_zero_iff, hnorm k]; exact one_ne_zero)
  have hunit : ∀ k, ((unit k : Kˣ) : K) = seq k := fun k => rfl
  have hunorm : ∀ k, ‖((unit k : Kˣ) : K)‖ = 1 := fun k => hnorm k
  -- `|f(β_k)| ≤ G δ_k^w`
  have hval : ∀ k, ‖lsum c (unit k)‖ ≤ G * δ k ^ w.toNat := fun k => by
    have h := norm_trunc_sub_le hc (M k) (unit k) (hunorm k)
      (mul_nonneg hG.le (pow_nonneg (hδ0 k).le _)) (hMtail k)
    have hr : (trunc c (M k)).eval ((unit k : Kˣ) : K) = 0 := hroot k
    rw [hr, zero_sub, norm_neg, norm_mul, norm_pow, hunorm k, one_pow, one_mul] at h
    exact h
  have hδw : ∀ k, δ k ^ w.toNat ≤ δ k := fun k =>
    pow_le_of_le_one (hδ0 k).le (hδ1 k) (by omega)
  -- the distance of consecutive roots
  have hdist : ∀ k, ‖seq k - seq (k + 1)‖ ≤ δ k := fun k => by
    have hspec := (hstep (k + 1) (seq k) (hnorm k)).choose_spec.2.2
    have hseq : seq (k + 1) = (hstep (k + 1) (seq k) (hnorm k)).choose := by
      rw [hseqs]; simp only [step, dif_pos (hnorm k)]
    rw [← hseq] at hspec
    have hbound : ‖(trunc c (M (k + 1))).eval (seq k)‖ ≤ G * δ k ^ w.toNat := by
      have h1 := norm_trunc_sub_le hc (M (k + 1)) (unit k) (hunorm k)
        (mul_nonneg hG.le (pow_nonneg (hδ0 _).le _)) (hMtail (k + 1))
      have h2 : ‖(unit k : K) ^ M (k + 1) * lsum c (unit k)‖ ≤ G * δ k ^ w.toNat := by
        rw [norm_mul, norm_pow, hunorm k, one_pow, one_mul]; exact hval k
      have h3 : G * δ (k + 1) ^ w.toNat ≤ G * δ k ^ w.toNat :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hδ0 _).le (hδanti k) _) hG.le
      have e : (trunc c (M (k + 1))).eval (seq k) =
          ((trunc c (M (k + 1))).eval (unit k : K) - (unit k : K) ^ M (k + 1) * lsum c (unit k))
            + (unit k : K) ^ M (k + 1) * lsum c (unit k) := by rw [hunit]; ring
      rw [e]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (h1.trans h3) h2)
    have h4 : ‖seq k - seq (k + 1)‖ ^ w.toNat ≤ δ k ^ w.toNat := by
      have := hspec.trans hbound
      rw [mul_comm G] at this
      exact le_of_mul_le_mul_right this hG
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (hδ0 k).le (by omega)).mp h4
  -- Cauchy
  have hcauchy : ∀ k j, ‖seq k - seq (k + j)‖ ≤ δ k := fun k j => by
    induction j with
    | zero => simp [(hδ0 k).le]
    | succ j ih =>
      have e : seq k - seq (k + (j + 1)) = (seq k - seq (k + j)) + (seq (k + j) - seq (k + j + 1))
        := by ring_nf
      rw [e]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ih ?_)
      refine (hdist (k + j)).trans ?_
      have : ∀ i, δ (k + i) ≤ δ k := fun i => by
        induction i with
        | zero => rfl
        | succ i ihi => exact (hδanti _).trans ihi
      exact this j
  have hδlim : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hcs : CauchySeq seq := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨N, hN⟩ := (hδlim.eventually (gt_mem_nhds hε)).exists_forall_of_atTop
    refine ⟨N, fun n hn => ?_⟩
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [dist_eq_norm, norm_sub_rev]
    exact (hcauchy N j).trans_lt (hN N le_rfl)
  obtain ⟨b, hb⟩ := cauchySeq_tendsto_of_complete hcs
  have hb1 : ‖b‖ = 1 := tendsto_nhds_unique ((continuous_norm.tendsto b).comp hb)
    (by simp only [Function.comp_def, hnorm]; exact tendsto_const_nhds)
  have hb0 : b ≠ 0 := by rw [← norm_ne_zero_iff, hb1]; exact one_ne_zero
  refine ⟨Units.mk0 b hb0, hb1, ?_⟩
  have hdb : ∀ k, ‖seq k - b‖ ≤ δ k := fun k => by
    have : Tendsto (fun j => ‖seq k - seq (j + k)‖) atTop (𝓝 ‖seq k - b‖) :=
      ((continuous_const.sub continuous_id : Continuous fun x : K => seq k - x).norm.tendsto b).comp
        (hb.comp (tendsto_add_atTop_nat k))
    exact le_of_tendsto' this fun j => by rw [add_comm]; exact hcauchy k j
  have hfb : ∀ k, ‖lsum c (Units.mk0 b hb0)‖ ≤ G * δ k := fun k => by
    have h1 := norm_lsum_sub_le hc (x := Units.mk0 b hb0) (y := unit k) hb1 (hunorm k)
    have e : lsum c (Units.mk0 b hb0) = (lsum c (Units.mk0 b hb0) - lsum c (unit k)) +
        lsum c (unit k) := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · refine h1.trans (mul_le_mul_of_nonneg_left ?_ hG.le)
      change ‖b - seq k‖ ≤ δ k
      rw [norm_sub_rev]; exact hdb k
    · exact (hval k).trans (mul_le_mul_of_nonneg_left (hδw k) hG.le)
  have hlim : Tendsto (fun k => G * δ k) atTop (𝓝 0) := by simpa using hδlim.const_mul G
  exact norm_eq_zero.mp (le_antisymm (ge_of_tendsto' hlim hfb) (norm_nonneg _))

/-- **Newton polygon zero existence**: if the lowest and highest dominant index of `f ∈ E(K)`
differ on the circle `|U| = ‖u₀‖`, then `f` has a zero on that circle. -/
theorem exists_zero_of_lo_lt_hi {f : Entire K} (hf : f ≠ 0) (u₀ : Kˣ)
    (h : lo (Entire.coeff f) ‖(u₀ : K)‖ < hi (Entire.coeff f) ‖(u₀ : K)‖) :
    ∃ u : Kˣ, ‖(u : K)‖ = ‖(u₀ : K)‖ ∧ (f : Kˣ → K) u = 0 := by
  have hg : Entire.scale u₀ f ≠ 0 := by
    intro h0
    apply hf
    refine Entire.ext_coeff (funext fun n => ?_)
    have := congrFun (congrArg Entire.coeff h0) n
    rw [Entire.coeff_scale, Entire.coeff_zero, Pi.zero_apply] at this
    rw [Entire.coeff_zero, Pi.zero_apply]
    exact (mul_eq_zero.mp this).resolve_right (zpow_ne_zero _ u₀.ne_zero)
  have h1 : lo (Entire.coeff (Entire.scale u₀ f)) 1 < hi (Entire.coeff (Entire.scale u₀ f)) 1 := by
    rw [Entire.lo_scale, Entire.hi_scale, mul_one]; exact h
  obtain ⟨v, hv, hv0⟩ := exists_zero_of_lo_lt_hi_one (Entire.isEntire_coeff _)
    (Entire.coeff_ne_zero hg) h1
  refine ⟨u₀ * v, by rw [Units.val_mul, norm_mul, hv, mul_one], ?_⟩
  rw [← Entire.coe_scale, Entire.coe_eq_lsum]
  exact hv0

/-! ### Zero-free entire series are monomials -/

/-- Strict domination of the index `k` over `n` on radii accumulating at `0` and `∞` forces
`cₙ = 0`. -/
lemma eq_zero_of_strict_on {c : ℤ → K} {k n : ℤ} (hn : n ≠ k) (hck : c k ≠ 0) (R : Set ℝ)
    (hR : ∀ r ∈ R, 0 < r) (hbig : ∀ C : ℝ, ∃ r ∈ R, C ≤ r)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ r ∈ R, r ≤ ε)
    (hlt : ∀ r ∈ R, ‖c n‖ * r ^ n < ‖c k‖ * r ^ k) : c n = 0 := by
  by_contra hcn
  set ε := ‖c n‖ / ‖c k‖ with hε
  have hck' : 0 < ‖c k‖ := norm_pos_iff.mpr hck
  have hε0 : 0 < ε := div_pos (norm_pos_iff.mpr hcn) hck'
  have key : ∀ r ∈ R, ε < r ^ (k - n) := fun r hr => by
    have hr0 := hR r hr
    have h := hlt r hr
    rw [hε, div_lt_iff₀ hck', zpow_sub₀ hr0.ne', div_mul_eq_mul_div,
      lt_div_iff₀ (zpow_pos hr0 n)]
    linarith
  rcases lt_or_gt_of_ne (sub_ne_zero.mpr hn.symm) with hneg | hpos
  · obtain ⟨r, hr, hrC⟩ := hbig (max 1 ε⁻¹)
    have hr1 : 1 ≤ r := (le_max_left _ _).trans hrC
    have hr0 : 0 < r := one_pos.trans_le hr1
    have h1 : r ^ (k - n) ≤ r ^ (-1 : ℤ) := zpow_le_zpow_right₀ hr1 (by omega)
    have h2 : r⁻¹ ≤ ε := by
      rw [inv_le_comm₀ hr0 hε0]; exact (le_max_right _ _).trans hrC
    have := key r hr
    simp only [zpow_neg, zpow_one] at h1
    linarith
  · obtain ⟨r, hr, hrε⟩ := hsmall (min 1 ε) (lt_min one_pos hε0)
    have hr0 := hR r hr
    have hr1 : r ≤ 1 := hrε.trans (min_le_left _ _)
    have h1 : r ^ (k - n) ≤ r ^ (1 : ℤ) := zpow_le_zpow_right_of_le_one₀ hr0 hr1 (by omega)
    have h2 : r ≤ ε := hrε.trans (min_le_right _ _)
    have := key r hr
    simp only [zpow_one] at h1
    linarith

/-- On a circle without zeros the Newton polygon has no edge. -/
theorem lo_eq_hi_of_no_zero {f : Entire K} (hf : f ≠ 0) (hz : ∀ u : Kˣ, (f : Kˣ → K) u ≠ 0)
    (u₀ : Kˣ) : lo (Entire.coeff f) ‖(u₀ : K)‖ = hi (Entire.coeff f) ‖(u₀ : K)‖ := by
  by_contra h
  obtain ⟨u, -, hu⟩ := exists_zero_of_lo_lt_hi hf u₀ (lt_of_le_of_ne
    (lo_le_hi (Entire.isEntire_coeff f) (Entire.coeff_ne_zero hf) (norm_pos_iff.mpr u₀.ne_zero)) h)
  exact hz u hu

/-- **No edges on the value-group radii ⇒ one dominant index.** (Uses that the value group of
the algebraically closed `K` is divisible, to place a tie radius between two radii with different
dominant indices.) -/
theorem exists_lo_const {c : ℤ → K} (hc : IsEntire c) (hc0 : c ≠ 0)
    (h : ∀ u : Kˣ, lo c ‖(u : K)‖ = hi c ‖(u : K)‖) (u v : Kˣ) :
    lo c ‖(u : K)‖ = lo c ‖(v : K)‖ := by
  have hpos : ∀ u : Kˣ, 0 < ‖(u : K)‖ := fun u => norm_pos_iff.mpr u.ne_zero
  -- the unique dominant index at a value-group radius
  have hdom : ∀ (u : Kˣ) n, n ≠ lo c ‖(u : K)‖ →
      tnorm c ‖(u : K)‖ n < tnorm c ‖(u : K)‖ (lo c ‖(u : K)‖) := fun u n hn => by
    rw [tnorm_lo hc hc0 (hpos u)]
    refine tnorm_lt_of_notMem hc hc0 (hpos u) fun hm => hn (le_antisymm ?_
      (le_lo_of_mem hc hc0 (hpos u) hm))
    rw [h u]; exact le_hi_of_mem hc hc0 (hpos u) hm
  have hmono : ∀ u v : Kˣ, ‖(u : K)‖ < ‖(v : K)‖ → lo c ‖(u : K)‖ ≤ lo c ‖(v : K)‖ :=
    fun u v huv => by rw [h u]; exact hi_le_lo hc hc0 (hpos u) huv
  have key : ∀ d : ℕ, ∀ u v : Kˣ, ‖(u : K)‖ < ‖(v : K)‖ →
      lo c ‖(v : K)‖ - lo c ‖(u : K)‖ = d → d = 0 := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro u v huv hd
      by_contra hd0
      have hr₁ := hpos u
      have hr₂ := hpos v
      have hca : c (lo c ‖(u : K)‖) ≠ 0 := coeff_lo_ne_zero hc hc0 hr₁
      have hcb : c (lo c ‖(v : K)‖) ≠ 0 := coeff_lo_ne_zero hc hc0 hr₂
      obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq
        (c (lo c ‖(u : K)‖) / c (lo c ‖(v : K)‖)) (Nat.pos_of_ne_zero hd0)
      have hx0 : x ≠ 0 := by
        rintro rfl; rw [zero_pow hd0] at hx; exact div_ne_zero hca hcb hx.symm
      set xu := Units.mk0 x hx0
      have hρ0 : 0 < ‖(xu : K)‖ := hpos xu
      set a := lo c ‖(u : K)‖ with ha
      set b := lo c ‖(v : K)‖ with hb
      set r₁ := ‖(u : K)‖ with hr₁def
      set r₂ := ‖(v : K)‖ with hr₂def
      set ρ := ‖(xu : K)‖ with hρdef
      have hρd : ρ ^ d = ‖c a‖ / ‖c b‖ := by
        rw [hρdef, show ((xu : Kˣ) : K) = x from rfl, ← norm_pow, hx, norm_div]
      have hca' : 0 < ‖c a‖ := norm_pos_iff.mpr hca
      have hcb' : 0 < ‖c b‖ := norm_pos_iff.mpr hcb
      have hab : b = a + d := by omega
      have hpow : ∀ r : ℝ, 0 < r → r ^ b = r ^ a * r ^ d := fun r hr => by
        rw [hab, zpow_add₀ hr.ne', zpow_natCast]
      have hba : b ≠ a := by omega
      have e1 : ‖c b‖ * r₁ ^ d < ‖c a‖ := by
        have this : tnorm c r₁ b < tnorm c r₁ a := hdom u b hba
        simp only [tnorm] at this
        rw [hpow r₁ hr₁] at this
        have hpa := zpow_pos hr₁ a
        exact lt_of_mul_lt_mul_right (by linarith) hpa.le
      have e2 : ‖c a‖ < ‖c b‖ * r₂ ^ d := by
        have this : tnorm c r₂ a < tnorm c r₂ b := hdom v a hba.symm
        simp only [tnorm] at this
        rw [hpow r₂ hr₂] at this
        have hpa := zpow_pos hr₂ a
        exact lt_of_mul_lt_mul_right (by linarith) hpa.le
      have hr₁ρ : r₁ < ρ := by
        refine (pow_lt_pow_iff_left₀ hr₁.le hρ0.le hd0).mp ?_
        rw [hρd, lt_div_iff₀ hcb']; linarith
      have hρr₂ : ρ < r₂ := by
        refine (pow_lt_pow_iff_left₀ hρ0.le hr₂.le hd0).mp ?_
        rw [hρd, div_lt_iff₀ hcb']; linarith
      have htie : tnorm c ρ b = tnorm c ρ a := by
        simp only [tnorm]
        rw [hpow ρ hρ0, hρd]
        field_simp
      have ham : a ≤ lo c ρ := hmono u xu hr₁ρ
      have hmb : lo c ρ ≤ b := hmono xu v hρr₂
      have hma : lo c ρ ≠ a := by
        intro hma
        have hmem : b ∈ domSet c ρ := by
          change tnorm c ρ b = gnorm c ρ; rw [htie, ← hma]; exact tnorm_lo hc hc0 hρ0
        have h1 := le_hi_of_mem hc hc0 hρ0 hmem
        have h2 : hi c ρ = lo c ρ := (h xu).symm
        omega
      have hmb' : lo c ρ ≠ b := by
        intro hmb'
        have hmem : a ∈ domSet c ρ := by
          change tnorm c ρ a = gnorm c ρ; rw [← htie, ← hmb']; exact tnorm_lo hc hc0 hρ0
        have := le_lo_of_mem hc hc0 hρ0 hmem
        omega
      have hlt : (lo c ρ - a).toNat < d := by omega
      have := ih _ hlt u xu hr₁ρ (by change lo c ρ - a = _; omega)
      omega
  rcases lt_trichotomy ‖(u : K)‖ ‖(v : K)‖ with huv | huv | huv
  · have h2 := hmono u v huv
    have h4 := Int.toNat_of_nonneg (sub_nonneg.mpr h2)
    have h3 := key _ u v huv h4.symm
    rw [h3] at h4
    omega
  · rw [huv]
  · have h2 := hmono v u huv
    have h4 := Int.toNat_of_nonneg (sub_nonneg.mpr h2)
    have h3 := key _ v u huv h4.symm
    rw [h3] at h4
    omega

/-- **A zero-free entire Laurent series over an algebraically closed field is `a·Uᵏ`.** -/
theorem eq_smul_mono_of_ne_zero {f : Entire K} (hf : f ≠ 0)
    (hz : ∀ u : Kˣ, (f : Kˣ → K) u ≠ 0) :
    ∃ a : K, a ≠ 0 ∧ ∃ k : ℤ, f = a • Entire.mono k := by
  have hc := Entire.isEntire_coeff f
  have hc0 := Entire.coeff_ne_zero hf
  have hlh := lo_eq_hi_of_no_zero hf hz
  set k := lo (Entire.coeff f) ‖((1 : Kˣ) : K)‖
  have hk : ∀ u : Kˣ, lo (Entire.coeff f) ‖(u : K)‖ = k := fun u =>
    exists_lo_const hc hc0 hlh u 1
  have hpos : ∀ u : Kˣ, 0 < ‖(u : K)‖ := fun u => norm_pos_iff.mpr u.ne_zero
  have hck : Entire.coeff f k ≠ 0 := coeff_lo_ne_zero hc hc0 (hpos 1)
  refine ⟨Entire.coeff f k, hck, k, Entire.ext_coeff (funext fun n => ?_)⟩
  rw [Entire.coeff_smul, Entire.coeff_mono]
  by_cases hn : n = k
  · subst hn; simp
  · rw [Pi.smul_apply, Pi.single_apply, if_neg hn, smul_zero]
    refine eq_zero_of_strict_on hn hck (Set.range fun u : Kˣ => ‖(u : K)‖)
      (by rintro _ ⟨u, rfl⟩; exact hpos u) (fun C => ?_) (fun ε hε => ?_) ?_
    · obtain ⟨u, hu⟩ := exists_unit_le_norm (K := K) C
      exact ⟨_, ⟨u, rfl⟩, hu⟩
    · obtain ⟨x, hx0, hx⟩ := NormedField.exists_norm_lt K hε
      exact ⟨_, ⟨Units.mk0 x (norm_pos_iff.mp hx0), rfl⟩, hx.le⟩
    · rintro _ ⟨u, rfl⟩
      have h1 := tnorm_lt_of_notMem hc hc0 (hpos u) (n := n) fun hm => hn (le_antisymm
        (by have := le_hi_of_mem hc hc0 (hpos u) hm; rw [← hlh u, hk u] at this; exact this)
        (by have := le_lo_of_mem hc hc0 (hpos u) hm; rw [hk u] at this; exact this))
      rw [← tnorm_lo hc hc0 (hpos u), hk u] at h1
      exact h1

/-- **The zero-free part of [EtTh] Proposition 3.4(ii) on `𝔾_m^an`**: a zero-free entire
Laurent series of Gauss norm `1` on the component circles `|U| = ‖q‖^a` (trivial non-cuspidal
divisor) is an element of `O_K^×`. -/
theorem eq_algebraMap_of_no_zero {f : Entire K} (hf : f ≠ 0)
    (hz : ∀ u : Kˣ, (f : Kˣ → K) u ≠ 0) {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)
    (hgn : ∀ a : ℤ, Entire.gn f (‖q‖ ^ a) = 1) :
    ∃ a : K, ‖a‖ = 1 ∧ f = algebraMap K (Entire K) a := by
  obtain ⟨a, ha, k, rfl⟩ := eq_smul_mono_of_ne_zero hf hz
  have hg : ∀ r : ℝ, 0 < r → Entire.gn (a • Entire.mono k) r = ‖a‖ * r ^ k := fun r hr => by
    have := Entire.gn_smul_mono_mul a k 1 hr
    rwa [mul_one, ← Entire.mono_zero, Entire.gn_mono 0 hr, zpow_zero, mul_one] at this
  have h0 := hgn 0
  rw [zpow_zero, hg 1 one_pos, one_zpow, mul_one] at h0
  have h1 := hgn 1
  rw [zpow_one, hg _ hq0, h0, one_mul] at h1
  have hk : k = 0 := by
    by_contra hk
    rcases lt_or_gt_of_ne hk with hk | hk
    · have := one_lt_zpow_of_neg₀ hq0 hq1 hk; linarith
    · have := zpow_lt_one₀ hq0 hq1 hk; linarith
  refine ⟨a, h0, ?_⟩
  rw [hk, Entire.mono_zero, Algebra.smul_def, mul_one]

end Iut.Frobenioid.BAn
