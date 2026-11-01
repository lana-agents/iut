/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.Tempered.RatFunEntire

/-!
# Gauss norms of entire Laurent series (MR18 T8, route B-an)

For an entire Laurent series `f = ∑ cₙ Uⁿ` (`RatFunEntire.lean`) and a real radius `r > 0`, the
**Gauss norm** `|f|_r = maxₙ ‖cₙ‖ rⁿ` is the norm of `f` on the circle `|U| = r`; on the circles
`|U| = ‖q‖^a` that correspond to the irreducible components of the special fibre of the
universal combinatorial covering of the Tate curve ([EtTh] §1, before Proposition 1.1), its
logarithm is the order of `f` along that component, i.e. the non-cuspidal part of the divisor of
[EtTh] Definition 3.1.

## Main results

* `tnorm`, `gnorm`, `lo`, `hi`: term norms, Gauss norm, lowest / highest dominant index.
* `gnorm_conv`, `lo_conv`, `hi_conv` (**Gauss lemma**, with additivity of the extreme dominant
  indices), hence `Entire.gnorm_mul`, `Entire.lo_mul`, `Entire.hi_mul` and `IsDomain (Entire K)`.
* `hi_le_lo` (`r < s ⇒ hi_r ≤ lo_s`: the Newton polygon is convex).
* `Entire.isUnit_iff`: **the units of `E(K)` are the `a·Uᵏ`** (no zero existence needed).
* `Entire.eq_algebraMap_of_gnorm_le`: **[EtTh] Proposition 3.2(ii) on `𝔾_m^an`**: an entire
  series bounded by `1` on circles whose radii accumulate at `0` and at `∞` (e.g. the component
  circles `|U| = ‖q‖^a`, `a ∈ ℤ`, `Entire.eq_algebraMap_of_gnorm_qpow_le`) lies in `O_K`.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace Iut.Frobenioid.BAn

open TateCurvesTheta Filter Topology

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]

/-! ### Elementary facts on real families -/

/-- A nonnegative family tending to `0` that is pointwise below `A > 0` is uniformly below some
`C < A`. -/
lemma exists_lt_bound {f : ℤ → ℝ} (hf : Tendsto f cofinite (𝓝 0)) {A : ℝ} (hA : 0 < A)
    (h : ∀ n, f n < A) : ∃ C < A, ∀ n, f n ≤ C := by
  have hfin : {n | ¬ f n < A / 2}.Finite :=
    Filter.eventually_cofinite.mp (hf.eventually (gt_mem_nhds (half_pos hA)))
  rcases (Set.eq_empty_or_nonempty {n | ¬ f n < A / 2}) with he | hne
  · refine ⟨A / 2, half_lt_self hA, fun n => ?_⟩
    have : n ∉ {n | ¬ f n < A / 2} := by rw [he]; exact Set.notMem_empty n
    simp only [Set.mem_setOf_eq, not_not] at this
    exact this.le
  · obtain ⟨a, ha, hmax⟩ := Set.exists_max_image _ f hfin hne
    refine ⟨max (A / 2) (f a), max_lt (half_lt_self hA) (h a), fun n => ?_⟩
    by_cases hn : f n < A / 2
    · exact (hn.le).trans (le_max_left _ _)
    · exact (hmax n hn).trans (le_max_right _ _)

/-- A family tending to `0` with a positive term attains its maximum. -/
lemma exists_max_of_tendsto {f : ℤ → ℝ} (hf : Tendsto f cofinite (𝓝 0)) {n₀ : ℤ}
    (hn₀ : 0 < f n₀) : ∃ n, ∀ m, f m ≤ f n := by
  have hfin : {n | ¬ f n < f n₀}.Finite :=
    Filter.eventually_cofinite.mp (hf.eventually (gt_mem_nhds hn₀))
  obtain ⟨a, ha, hmax⟩ := Set.exists_max_image _ f hfin ⟨n₀, by simp⟩
  refine ⟨a, fun m => ?_⟩
  by_cases hm : f m < f n₀
  · exact hm.le.trans (by simpa using ha)
  · exact hmax m hm

/-! ### Term norms and the Gauss norm -/

/-- The term norms `‖cₙ‖ rⁿ` at radius `r`. -/
def tnorm (c : ℤ → K) (r : ℝ) (n : ℤ) : ℝ := ‖c n‖ * r ^ n

lemma tnorm_nonneg (c : ℤ → K) {r : ℝ} (hr : 0 < r) (n : ℤ) : 0 ≤ tnorm c r n :=
  mul_nonneg (norm_nonneg _) (zpow_nonneg hr.le n)

lemma tnorm_pos {c : ℤ → K} {r : ℝ} (hr : 0 < r) {n : ℤ} (hn : c n ≠ 0) : 0 < tnorm c r n :=
  mul_pos (norm_pos_iff.mpr hn) (zpow_pos hr n)

lemma exists_unit_le_norm (R : ℝ) : ∃ u : Kˣ, R ≤ ‖(u : K)‖ := by
  obtain ⟨x, hx⟩ := NormedField.exists_lt_norm K (max R 0)
  have hx0 : x ≠ 0 := norm_pos_iff.mp ((le_max_right R 0).trans_lt hx)
  exact ⟨Units.mk0 x hx0, ((le_max_left R 0).trans hx.le)⟩

lemma zpow_le_add {r R : ℝ} (hr : 0 < r) (h1 : r ≤ R) (h2 : r⁻¹ ≤ R) (n : ℤ) :
    r ^ n ≤ R ^ n + R ^ (-n) := by
  have hR : 0 < R := hr.trans_le h1
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · have h : r ^ m ≤ R ^ m := pow_le_pow_left₀ hr.le h1 m
    have : 0 ≤ R ^ (-(m : ℤ)) := (zpow_pos hR _).le
    simp only [zpow_natCast]
    linarith
  · have h : r⁻¹ ^ m ≤ R ^ m := pow_le_pow_left₀ (inv_nonneg.mpr hr.le) h2 m
    have : 0 ≤ R ^ (-(m : ℤ)) := (zpow_pos hR _).le
    simp only [zpow_neg, zpow_natCast, inv_pow, neg_neg] at h this ⊢
    linarith

lemma IsEntire.tendsto_tnorm {c : ℤ → K} (hc : IsEntire c) {r : ℝ} (hr : 0 < r) :
    Tendsto (tnorm c r) cofinite (𝓝 0) := by
  obtain ⟨u, hu⟩ := exists_unit_le_norm (K := K) (max r r⁻¹)
  have hR : 0 < ‖(u : K)‖ := norm_pos_iff.mpr u.ne_zero
  have t1 := (hc u).tendsto_cofinite_zero.norm
  have t2 := (hc u⁻¹).tendsto_cofinite_zero.norm
  rw [norm_zero] at t1 t2
  have hlim : Tendsto (fun n => ‖c n * (u : K) ^ n‖ + ‖c n * ((u⁻¹ : Kˣ) : K) ^ n‖) cofinite
      (𝓝 0) := by
    have := t1.add t2; rwa [add_zero] at this
  refine squeeze_zero (fun n => tnorm_nonneg c hr n) (fun n => ?_) hlim
  have h := zpow_le_add hr ((le_max_left _ _).trans hu) ((le_max_right _ _).trans hu) n
  rw [norm_mul, norm_mul, norm_zpow, norm_zpow, Units.val_inv_eq_inv_val, norm_inv, inv_zpow,
    ← zpow_neg, tnorm]
  nlinarith [norm_nonneg (c n)]

lemma IsEntire.bddAbove {c : ℤ → K} (hc : IsEntire c) {r : ℝ} (hr : 0 < r) :
    BddAbove (Set.range (tnorm c r)) :=
  (hc.tendsto_tnorm hr).bddAbove_range_of_cofinite

/-- **The Gauss norm** `|f|_r = supₙ ‖cₙ‖ rⁿ`. -/
def gnorm (c : ℤ → K) (r : ℝ) : ℝ := ⨆ n, tnorm c r n

lemma le_gnorm {c : ℤ → K} (hc : IsEntire c) {r : ℝ} (hr : 0 < r) (n : ℤ) :
    tnorm c r n ≤ gnorm c r :=
  le_ciSup (hc.bddAbove hr) n

lemma gnorm_le {c : ℤ → K} {r : ℝ} {C : ℝ} (h : ∀ n, tnorm c r n ≤ C) : gnorm c r ≤ C :=
  ciSup_le h

lemma gnorm_nonneg {c : ℤ → K} (hc : IsEntire c) {r : ℝ} (hr : 0 < r) : 0 ≤ gnorm c r :=
  (tnorm_nonneg c hr 0).trans (le_gnorm hc hr 0)

lemma gnorm_pos {c : ℤ → K} (hc : IsEntire c) (hc0 : c ≠ 0) {r : ℝ} (hr : 0 < r) :
    0 < gnorm c r := by
  obtain ⟨n, hn⟩ := Function.ne_iff.mp hc0
  exact (tnorm_pos hr hn).trans_le (le_gnorm hc hr n)

lemma exists_tnorm_eq_gnorm {c : ℤ → K} (hc : IsEntire c) (hc0 : c ≠ 0) {r : ℝ} (hr : 0 < r) :
    ∃ n, tnorm c r n = gnorm c r := by
  obtain ⟨n₀, hn₀⟩ := Function.ne_iff.mp hc0
  obtain ⟨n, hn⟩ := exists_max_of_tendsto (hc.tendsto_tnorm hr) (tnorm_pos hr hn₀)
  exact ⟨n, le_antisymm (le_gnorm hc hr n) (gnorm_le hn)⟩

/-! ### Dominant indices -/

/-- The set of dominant indices at radius `r`. -/
def domSet (c : ℤ → K) (r : ℝ) : Set ℤ := {n | tnorm c r n = gnorm c r}

lemma domSet_finite {c : ℤ → K} (hc : IsEntire c) (hc0 : c ≠ 0) {r : ℝ} (hr : 0 < r) :
    (domSet c r).Finite := by
  refine (Filter.eventually_cofinite.mp ((hc.tendsto_tnorm hr).eventually
    (gt_mem_nhds (gnorm_pos hc hc0 hr)))).subset fun n hn => ?_
  simp only [domSet, Set.mem_setOf_eq] at hn ⊢
  exact not_lt.mpr hn.ge

lemma domSet_nonempty {c : ℤ → K} (hc : IsEntire c) (hc0 : c ≠ 0) {r : ℝ} (hr : 0 < r) :
    (domSet c r).Nonempty :=
  exists_tnorm_eq_gnorm hc hc0 hr

/-- The **lowest dominant index** at radius `r`. -/
def lo (c : ℤ → K) (r : ℝ) : ℤ := sInf (domSet c r)

/-- The **highest dominant index** at radius `r`. -/
def hi (c : ℤ → K) (r : ℝ) : ℤ := sSup (domSet c r)

section Dom

variable {c : ℤ → K} (hc : IsEntire c) (hc0 : c ≠ 0) {r : ℝ} (hr : 0 < r)
include hc hc0 hr

lemma lo_mem : lo c r ∈ domSet c r :=
  Int.csInf_mem (domSet_nonempty hc hc0 hr) (domSet_finite hc hc0 hr).bddBelow

lemma hi_mem : hi c r ∈ domSet c r :=
  Int.csSup_mem (domSet_nonempty hc hc0 hr) (domSet_finite hc hc0 hr).bddAbove

lemma tnorm_lo : tnorm c r (lo c r) = gnorm c r := lo_mem hc hc0 hr

lemma tnorm_hi : tnorm c r (hi c r) = gnorm c r := hi_mem hc hc0 hr

lemma le_lo_of_mem {n : ℤ} (hn : n ∈ domSet c r) : lo c r ≤ n :=
  csInf_le (domSet_finite hc hc0 hr).bddBelow hn

lemma le_hi_of_mem {n : ℤ} (hn : n ∈ domSet c r) : n ≤ hi c r :=
  le_csSup (domSet_finite hc hc0 hr).bddAbove hn

lemma tnorm_lt_of_notMem {n : ℤ} (hn : n ∉ domSet c r) : tnorm c r n < gnorm c r :=
  lt_of_le_of_ne (le_gnorm hc hr n) hn

lemma tnorm_lt_of_lt_lo {n : ℤ} (hn : n < lo c r) : tnorm c r n < gnorm c r :=
  tnorm_lt_of_notMem hc hc0 hr fun h => (le_lo_of_mem hc hc0 hr h).not_gt hn

lemma tnorm_lt_of_hi_lt {n : ℤ} (hn : hi c r < n) : tnorm c r n < gnorm c r :=
  tnorm_lt_of_notMem hc hc0 hr fun h => (le_hi_of_mem hc hc0 hr h).not_gt hn

lemma lo_le_hi : lo c r ≤ hi c r := le_lo_of_mem hc hc0 hr (hi_mem hc hc0 hr)

lemma coeff_lo_ne_zero : c (lo c r) ≠ 0 := by
  intro h
  have := tnorm_lo hc hc0 hr
  rw [tnorm, h, norm_zero, zero_mul] at this
  exact (gnorm_pos hc hc0 hr).ne this

lemma coeff_hi_ne_zero : c (hi c r) ≠ 0 := by
  intro h
  have := tnorm_hi hc hc0 hr
  rw [tnorm, h, norm_zero, zero_mul] at this
  exact (gnorm_pos hc hc0 hr).ne this

/-- Characterisation of the lowest dominant index. -/
lemma lo_eq_of {n : ℤ} (hn : tnorm c r n = gnorm c r)
    (hlt : ∀ m < n, tnorm c r m < gnorm c r) : lo c r = n := by
  refine le_antisymm (le_lo_of_mem hc hc0 hr hn) ?_
  by_contra h
  exact (hlt _ (not_le.mp h)).ne (tnorm_lo hc hc0 hr)

/-- Characterisation of the highest dominant index. -/
lemma hi_eq_of {n : ℤ} (hn : tnorm c r n = gnorm c r)
    (hlt : ∀ m, n < m → tnorm c r m < gnorm c r) : hi c r = n := by
  refine le_antisymm ?_ (le_hi_of_mem hc hc0 hr hn)
  by_contra h
  exact (hlt _ (not_le.mp h)).ne (tnorm_hi hc hc0 hr)

end Dom

/-! ### Convexity: `r < s ⇒ hi_r ≤ lo_s` -/

lemma tnorm_mul_ratio (c : ℤ → K) {r s : ℝ} (hr : 0 < r) (n : ℤ) :
    tnorm c s n = tnorm c r n * (s / r) ^ n := by
  rw [tnorm, tnorm, div_zpow, mul_assoc, mul_div_cancel₀ _ (zpow_ne_zero n hr.ne')]

/-- **Convexity of the Newton polygon.** -/
theorem hi_le_lo {c : ℤ → K} (hc : IsEntire c) (hc0 : c ≠ 0) {r s : ℝ} (hr : 0 < r)
    (hrs : r < s) : hi c r ≤ lo c s := by
  have hs : 0 < s := hr.trans hrs
  have hq : 1 < s / r := (one_lt_div hr).mpr hrs
  refine le_csInf (domSet_nonempty hc hc0 hs) fun m hm => ?_
  by_contra hlt
  push Not at hlt
  have hpos := tnorm_pos hr (coeff_hi_ne_zero hc hc0 hr)
  have h1 : tnorm c s m < tnorm c s (hi c r) := by
    rw [tnorm_mul_ratio c hr m, tnorm_mul_ratio c hr (hi c r)]
    calc tnorm c r m * (s / r) ^ m ≤ tnorm c r (hi c r) * (s / r) ^ m := by
          refine mul_le_mul_of_nonneg_right ?_ (zpow_pos (by linarith) _).le
          rw [tnorm_hi hc hc0 hr]; exact le_gnorm hc hr m
      _ < tnorm c r (hi c r) * (s / r) ^ (hi c r) :=
          mul_lt_mul_of_pos_left (zpow_lt_zpow_right₀ hq hlt) hpos
  exact (h1.trans_le (le_gnorm hc hs _)).ne hm

/-! ### The Gauss lemma -/

section Gauss

variable {c d : ℤ → K}

lemma tnorm_mul_tnorm (r : ℝ) (hr : 0 < r) (l m : ℤ) :
    tnorm c r (l - m) * tnorm d r m = ‖c (l - m) * d m‖ * r ^ l := by
  rw [tnorm, tnorm, norm_mul]
  have : r ^ l = r ^ (l - m) * r ^ m := by rw [← zpow_add₀ hr.ne', sub_add_cancel]
  rw [this]; ring

lemma tendsto_conv_family (hc : IsEntire c) (hd : IsEntire d) {r : ℝ} (hr : 0 < r) (l : ℤ) :
    Tendsto (fun m => tnorm c r (l - m) * tnorm d r m) cofinite (𝓝 0) := by
  obtain ⟨B, hB⟩ := hc.bddAbove hr
  have hB' : ∀ n, tnorm c r n ≤ B := fun n => hB ⟨n, rfl⟩
  have hB0 : 0 ≤ B := (tnorm_nonneg c hr 0).trans (hB' 0)
  refine squeeze_zero (fun m => mul_nonneg (tnorm_nonneg c hr _) (tnorm_nonneg d hr m))
    (fun m => mul_le_mul_of_nonneg_right (hB' _) (tnorm_nonneg d hr m)) ?_
  simpa using (hd.tendsto_tnorm hr).const_mul B

lemma summable_conv_family (hc : IsEntire c) (hd : IsEntire d) (l : ℤ) :
    Summable fun m => c (l - m) * d m := by
  refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine (tendsto_conv_family hc hd one_pos l).congr fun m => ?_
  rw [tnorm_mul_tnorm 1 one_pos, one_zpow, mul_one]

lemma tnorm_conv_le (hc : IsEntire c) (hd : IsEntire d) {r : ℝ} (hr : 0 < r) (l : ℤ) :
    tnorm (conv c d) r l ≤ gnorm c r * gnorm d r := by
  have hrl : 0 < r ^ l := zpow_pos hr l
  have hC : 0 ≤ gnorm c r * gnorm d r / r ^ l :=
    div_nonneg (mul_nonneg (gnorm_nonneg hc hr) (gnorm_nonneg hd hr)) hrl.le
  have h : ‖conv c d l‖ ≤ gnorm c r * gnorm d r / r ^ l := by
    refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg hC fun m => ?_
    rw [le_div_iff₀ hrl, ← tnorm_mul_tnorm r hr]
    exact mul_le_mul (le_gnorm hc hr _) (le_gnorm hd hr m) (tnorm_nonneg d hr m)
      (gnorm_nonneg hc hr)
  rw [tnorm]
  exact (le_div_iff₀ hrl).mp h

/-- Strict bound below the lowest (or above the highest) index of a product. -/
lemma tnorm_conv_lt (hc : IsEntire c) (hd : IsEntire d) (hc0 : c ≠ 0) (hd0 : d ≠ 0)
    {r : ℝ} (hr : 0 < r) (l : ℤ)
    (hl : ∀ m, tnorm c r (l - m) < gnorm c r ∨ tnorm d r m < gnorm d r) :
    tnorm (conv c d) r l < gnorm c r * gnorm d r := by
  have hA := gnorm_pos hc hc0 hr
  have hB := gnorm_pos hd hd0 hr
  have hrl : 0 < r ^ l := zpow_pos hr l
  have hpt : ∀ m, tnorm c r (l - m) * tnorm d r m < gnorm c r * gnorm d r := fun m => by
    rcases hl m with h | h
    · exact mul_lt_mul_of_lt_of_le_of_nonneg_of_pos h (le_gnorm hd hr m) (tnorm_nonneg c hr _) hB
    · exact mul_lt_mul_of_le_of_lt_of_nonneg_of_pos (le_gnorm hc hr _) h (tnorm_nonneg d hr m)
        hA
  obtain ⟨C, hCA, hC⟩ := exists_lt_bound (tendsto_conv_family hc hd hr l) (mul_pos hA hB) hpt
  have hC0 : 0 ≤ C := (mul_nonneg (tnorm_nonneg c hr _) (tnorm_nonneg d hr 0)).trans (hC 0)
  have h : ‖conv c d l‖ ≤ C / r ^ l := by
    refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (div_nonneg hC0 hrl.le)
      fun m => ?_
    rw [le_div_iff₀ hrl, ← tnorm_mul_tnorm r hr]
    exact hC m
  rw [tnorm]
  exact ((le_div_iff₀ hrl).mp h).trans_lt hCA

/-- The dominant term of a product. -/
lemma tnorm_conv_eq (hc : IsEntire c) (hd : IsEntire d) {r : ℝ} (hr : 0 < r) (a b : ℤ)
    (ha : tnorm c r a = gnorm c r) (hb : tnorm d r b = gnorm d r)
    (hl : ∀ m, m ≠ b → tnorm c r (a + b - m) < gnorm c r ∨ tnorm d r m < gnorm d r)
    (hA : 0 < gnorm c r) (hB : 0 < gnorm d r) :
    tnorm (conv c d) r (a + b) = gnorm c r * gnorm d r := by
  have hrl : 0 < r ^ (a + b) := zpow_pos hr _
  have hdom : ∀ m, m ≠ b → ‖c (a + b - m) * d m‖ < ‖c (a + b - b) * d b‖ := fun m hm => by
    rw [← mul_lt_mul_iff_of_pos_right hrl, ← tnorm_mul_tnorm r hr, ← tnorm_mul_tnorm r hr,
      add_sub_cancel_right, ha, hb]
    rcases hl m hm with h | h
    · exact mul_lt_mul_of_lt_of_le_of_nonneg_of_pos h (le_gnorm hd hr m) (tnorm_nonneg c hr _) hB
    · exact mul_lt_mul_of_le_of_lt_of_nonneg_of_pos (le_gnorm hc hr _) h (tnorm_nonneg d hr m)
        hA
  have h := IsUltrametricDist.norm_tsum_eq_of_dominant (summable_conv_family hc hd (a + b)) hdom
  rw [tnorm, conv, h, ← tnorm_mul_tnorm r hr, add_sub_cancel_right, ha, hb]

variable (hc : IsEntire c) (hd : IsEntire d) (hc0 : c ≠ 0) (hd0 : d ≠ 0) {r : ℝ} (hr : 0 < r)
include hc hd hc0 hd0 hr

lemma tnorm_conv_lo :
    tnorm (conv c d) r (lo c r + lo d r) = gnorm c r * gnorm d r := by
  refine tnorm_conv_eq hc hd hr _ _ (tnorm_lo hc hc0 hr) (tnorm_lo hd hd0 hr) (fun m hm => ?_)
    (gnorm_pos hc hc0 hr) (gnorm_pos hd hd0 hr)
  rcases lt_or_gt_of_ne hm with h | h
  · exact Or.inr (tnorm_lt_of_lt_lo hd hd0 hr h)
  · exact Or.inl (tnorm_lt_of_lt_lo hc hc0 hr (by omega))

lemma tnorm_conv_hi :
    tnorm (conv c d) r (hi c r + hi d r) = gnorm c r * gnorm d r := by
  refine tnorm_conv_eq hc hd hr _ _ (tnorm_hi hc hc0 hr) (tnorm_hi hd hd0 hr) (fun m hm => ?_)
    (gnorm_pos hc hc0 hr) (gnorm_pos hd hd0 hr)
  rcases lt_or_gt_of_ne hm with h | h
  · exact Or.inl (tnorm_lt_of_hi_lt hc hc0 hr (by omega))
  · exact Or.inr (tnorm_lt_of_hi_lt hd hd0 hr h)

/-- **Gauss lemma**: `|fg|_r = |f|_r |g|_r`. -/
theorem gnorm_conv : gnorm (conv c d) r = gnorm c r * gnorm d r :=
  le_antisymm (gnorm_le (tnorm_conv_le hc hd hr))
    ((tnorm_conv_lo hc hd hc0 hd0 hr).symm.le.trans (le_gnorm (hc.conv hd) hr _))

theorem conv_ne_zero : conv c d ≠ 0 := by
  intro h
  have := tnorm_conv_lo hc hd hc0 hd0 hr
  rw [h, tnorm, Pi.zero_apply, norm_zero, zero_mul] at this
  exact (mul_pos (gnorm_pos hc hc0 hr) (gnorm_pos hd hd0 hr)).ne this

/-- The lowest dominant index is additive. -/
theorem lo_conv : lo (conv c d) r = lo c r + lo d r := by
  refine lo_eq_of (hc.conv hd) (conv_ne_zero hc hd hc0 hd0 hr) hr ?_ fun m hm => ?_
  · rw [tnorm_conv_lo hc hd hc0 hd0 hr, gnorm_conv hc hd hc0 hd0 hr]
  · rw [gnorm_conv hc hd hc0 hd0 hr]
    refine tnorm_conv_lt hc hd hc0 hd0 hr m fun k => ?_
    by_cases hk : k < lo d r
    · exact Or.inr (tnorm_lt_of_lt_lo hd hd0 hr hk)
    · exact Or.inl (tnorm_lt_of_lt_lo hc hc0 hr (by omega))

/-- The highest dominant index is additive. -/
theorem hi_conv : hi (conv c d) r = hi c r + hi d r := by
  refine hi_eq_of (hc.conv hd) (conv_ne_zero hc hd hc0 hd0 hr) hr ?_ fun m hm => ?_
  · rw [tnorm_conv_hi hc hd hc0 hd0 hr, gnorm_conv hc hd hc0 hd0 hr]
  · rw [gnorm_conv hc hd hc0 hd0 hr]
    refine tnorm_conv_lt hc hd hc0 hd0 hr m fun k => ?_
    by_cases hk : hi d r < k
    · exact Or.inr (tnorm_lt_of_hi_lt hd hd0 hr hk)
    · exact Or.inl (tnorm_lt_of_hi_lt hc hc0 hr (by omega))

end Gauss

/-! ### A family with one dominant index at every radius is a monomial -/

/-- If `k` is the unique dominant index at every radius, then `c` is supported at `k`. -/
theorem eq_zero_of_dom_eq {c : ℤ → K} (hc : IsEntire c) (hc0 : c ≠ 0) {k : ℤ}
    (hk : ∀ r : ℝ, 0 < r → lo c r = k ∧ hi c r = k) {n : ℤ} (hn : n ≠ k) : c n = 0 := by
  by_contra hcn
  have hck : c k ≠ 0 := by
    have := coeff_lo_ne_zero hc hc0 one_pos; rwa [(hk 1 one_pos).1] at this
  have hlt : ∀ r : ℝ, 0 < r → ‖c n‖ * r ^ n < ‖c k‖ * r ^ k := fun r hr => by
    have h1 := tnorm_lt_of_notMem hc hc0 hr (n := n) fun hmem => by
      have h2 := le_lo_of_mem hc hc0 hr hmem
      have h3 := le_hi_of_mem hc hc0 hr hmem
      rw [(hk r hr).1] at h2; rw [(hk r hr).2] at h3
      exact hn (le_antisymm h3 h2)
    have h4 := tnorm_lo hc hc0 hr
    rw [(hk r hr).1] at h4
    rw [← h4] at h1
    exact h1
  set ε := ‖c n‖ / ‖c k‖ with hε
  have hε0 : 0 < ε := div_pos (norm_pos_iff.mpr hcn) (norm_pos_iff.mpr hck)
  have key : ∀ r : ℝ, 0 < r → ε < r ^ (k - n) := fun r hr => by
    have h := hlt r hr
    rw [hε, div_lt_iff₀ (norm_pos_iff.mpr hck), zpow_sub₀ hr.ne']
    rw [← lt_div_iff₀ (zpow_pos hr n)] at h
    calc ‖c n‖ < ‖c k‖ * r ^ k / r ^ n := h
      _ = r ^ k / r ^ n * ‖c k‖ := by ring
  rcases lt_or_gt_of_ne (sub_ne_zero.mpr hn.symm) with hneg | hpos
  · -- `k - n < 0`: take `r = max 1 ε⁻¹`.
    set r := max 1 ε⁻¹
    have hr1 : 1 ≤ r := le_max_left _ _
    have hr0 : 0 < r := one_pos.trans_le hr1
    have h := key r hr0
    have : r ^ (k - n) ≤ r⁻¹ := by
      have : r ^ (k - n) ≤ r ^ (-1 : ℤ) := zpow_le_zpow_right₀ hr1 (by omega)
      simpa using this
    have : r⁻¹ ≤ ε := by
      rw [inv_le_comm₀ hr0 hε0]; exact le_max_right _ _
    linarith
  · -- `k - n > 0`: take `r = min 1 ε`.
    set r := min 1 ε
    have hr0 : 0 < r := lt_min one_pos hε0
    have hr1 : r ≤ 1 := min_le_left _ _
    have h := key r hr0
    have : r ^ (k - n) ≤ r ^ (1 : ℤ) := zpow_le_zpow_right_of_le_one₀ hr0 hr1 (by omega)
    have : r ≤ ε := min_le_right _ _
    simp only [zpow_one] at *
    linarith

/-! ### Transfer to `E(K)` -/

namespace Entire

lemma coeff_ne_zero {f : Entire K} (hf : f ≠ 0) : coeff f ≠ 0 :=
  fun h => hf (ext_coeff (h.trans coeff_zero.symm))

instance : NoZeroDivisors (Entire K) where
  eq_zero_or_eq_zero_of_mul_eq_zero {f g} h := by
    by_contra hfg
    push Not at hfg
    have := conv_ne_zero (isEntire_coeff f) (isEntire_coeff g) (coeff_ne_zero hfg.1)
      (coeff_ne_zero hfg.2) one_pos
    rw [← coeff_mul, h, coeff_zero] at this
    exact this rfl

instance : Nontrivial (Entire K) :=
  ⟨⟨0, 1, fun h => by
    have := congrFun (congrArg coeff h) 0
    rw [coeff_zero, coeff_one] at this
    simp at this⟩⟩

instance : IsDomain (Entire K) := NoZeroDivisors.to_isDomain _

/-- Gauss norm of an element. -/
abbrev gn (f : Entire K) (r : ℝ) : ℝ := gnorm (coeff f) r

theorem gn_mul (f g : Entire K) {r : ℝ} (hr : 0 < r) : gn (f * g) r = gn f r * gn g r := by
  by_cases hf : f = 0
  · subst hf
    simp only [zero_mul, gn, coeff_zero, gnorm, tnorm, Pi.zero_apply, norm_zero, zero_mul,
      ciSup_const]
  by_cases hg : g = 0
  · subst hg
    simp only [mul_zero, gn, coeff_zero, gnorm, tnorm, Pi.zero_apply, norm_zero, zero_mul,
      ciSup_const]
  rw [gn, coeff_mul]
  exact gnorm_conv (isEntire_coeff f) (isEntire_coeff g) (coeff_ne_zero hf) (coeff_ne_zero hg) hr

theorem lo_mul {f g : Entire K} (hf : f ≠ 0) (hg : g ≠ 0) {r : ℝ} (hr : 0 < r) :
    lo (coeff (f * g)) r = lo (coeff f) r + lo (coeff g) r := by
  rw [coeff_mul]
  exact lo_conv (isEntire_coeff f) (isEntire_coeff g) (coeff_ne_zero hf) (coeff_ne_zero hg) hr

theorem hi_mul {f g : Entire K} (hf : f ≠ 0) (hg : g ≠ 0) {r : ℝ} (hr : 0 < r) :
    hi (coeff (f * g)) r = hi (coeff f) r + hi (coeff g) r := by
  rw [coeff_mul]
  exact hi_conv (isEntire_coeff f) (isEntire_coeff g) (coeff_ne_zero hf) (coeff_ne_zero hg) hr

lemma domSet_single (k : ℤ) (a : K) (ha : a ≠ 0) {r : ℝ} (hr : 0 < r) :
    domSet (Pi.single k a) r = {k} := by
  have hpos : 0 < tnorm (Pi.single k a) r k := tnorm_pos hr (by simpa using ha)
  have hz : ∀ n, n ≠ k → tnorm (Pi.single k a) r n = 0 := fun n hn => by
    simp [tnorm, hn]
  have hg : gnorm (Pi.single k a) r = tnorm (Pi.single k a) r k := by
    refine le_antisymm (gnorm_le fun n => ?_) (le_gnorm (isEntire_single k a) hr k)
    by_cases hn : n = k
    · rw [hn]
    · rw [hz n hn]; exact hpos.le
  ext n
  simp only [domSet, Set.mem_setOf_eq, Set.mem_singleton_iff, hg]
  constructor
  · intro h; by_contra hn; rw [hz n hn] at h; exact hpos.ne h
  · rintro rfl; rfl

lemma lo_single (k : ℤ) (a : K) (ha : a ≠ 0) {r : ℝ} (hr : 0 < r) :
    lo (Pi.single k a) r = k := by
  rw [lo, domSet_single k a ha hr, csInf_singleton]

lemma hi_single (k : ℤ) (a : K) (ha : a ≠ 0) {r : ℝ} (hr : 0 < r) :
    hi (Pi.single k a) r = k := by
  rw [hi, domSet_single k a ha hr, csSup_singleton]

/-- If `lo = hi = k` at every radius, then `f = a • Uᵏ`. -/
theorem eq_smul_mono_of_dom {f : Entire K} (hf : f ≠ 0) {k : ℤ}
    (hk : ∀ r : ℝ, 0 < r → lo (coeff f) r = k ∧ hi (coeff f) r = k) :
    f = coeff f k • mono k := by
  refine ext_coeff (funext fun n => ?_)
  rw [coeff_smul, coeff_mono]
  by_cases hn : n = k
  · subst hn; simp
  · rw [eq_zero_of_dom_eq (isEntire_coeff f) (coeff_ne_zero hf) hk hn]
    simp [hn]

/-- **The units of `E(K)` are the monomials `a·Uᵏ`, `a ≠ 0`.** -/
theorem isUnit_iff {f : Entire K} :
    IsUnit f ↔ ∃ a : K, a ≠ 0 ∧ ∃ k : ℤ, f = a • mono k := by
  constructor
  · rintro ⟨u, rfl⟩
    set f := (u : Entire K)
    set g := ((u⁻¹ : (Entire K)ˣ) : Entire K)
    have hfg : f * g = 1 := u.mul_inv
    have hf : f ≠ 0 := u.ne_zero
    have hg : g ≠ 0 := (u⁻¹).ne_zero
    have h1 : ∀ r : ℝ, 0 < r → lo (coeff f) r + lo (coeff g) r = 0 := fun r hr => by
      rw [← lo_mul hf hg hr, hfg, coeff_one, lo_single 0 1 one_ne_zero hr]
    have h2 : ∀ r : ℝ, 0 < r → hi (coeff f) r + hi (coeff g) r = 0 := fun r hr => by
      rw [← hi_mul hf hg hr, hfg, coeff_one, hi_single 0 1 one_ne_zero hr]
    have hf' := isEntire_coeff f
    have hg' := isEntire_coeff g
    have hf0 := coeff_ne_zero hf
    have hg0 := coeff_ne_zero hg
    -- `hi_f r = lo_f s` for `r < s`.
    have key : ∀ r s : ℝ, 0 < r → r < s → hi (coeff f) r = lo (coeff f) s := fun r s hr hrs => by
      have hs : 0 < s := hr.trans hrs
      have a1 := hi_le_lo hf' hf0 hr hrs
      have a2 := hi_le_lo hg' hg0 hr hrs
      have a3 := h1 s hs
      have a4 := h2 r hr
      omega
    have hdom : ∀ r : ℝ, 0 < r → lo (coeff f) r = hi (coeff f) 1 ∧
        hi (coeff f) r = hi (coeff f) 1 := fun r hr => by
      have e1 : hi (coeff f) r = lo (coeff f) (r + 1 + 1) := key r _ hr (by linarith)
      have e2 : hi (coeff f) 1 = lo (coeff f) (r + 1 + 1) := key 1 _ one_pos (by linarith)
      have e3 : hi (coeff f) (r / 2) = lo (coeff f) r := key (r / 2) r (by linarith) (by linarith)
      have e4 : hi (coeff f) (r / 2) = lo (coeff f) (r + 1 + 1) :=
        key (r / 2) _ (by linarith) (by linarith)
      omega
    exact ⟨coeff f (hi (coeff f) 1), by
      have := coeff_lo_ne_zero hf' hf0 one_pos
      rwa [(hdom 1 one_pos).1] at this, _, eq_smul_mono_of_dom hf hdom⟩
  · rintro ⟨a, ha, k, rfl⟩
    rw [Algebra.smul_def]
    exact ((Ne.isUnit ha).map (algebraMap K (Entire K))).mul (isUnit_mono k)

/-- **[EtTh] Proposition 3.2(ii) on `𝔾_m^an`.** An entire Laurent series whose Gauss norm is at
most `1` on circles with radii accumulating at `∞` and at `0` is an element of `O_K`. (The proof
of [EtTh] uses the special fibre; on `𝔾_m^an` the Gauss norms do it directly.) -/
theorem eq_algebraMap_of_gnorm_le (f : Entire K) (R : Set ℝ) (hRpos : ∀ r ∈ R, 0 < r)
    (hbig : ∀ C : ℝ, ∃ r ∈ R, C ≤ r) (hsmall : ∀ ε : ℝ, 0 < ε → ∃ r ∈ R, r ≤ ε)
    (hle : ∀ r ∈ R, gn f r ≤ 1) :
    ∃ a : K, ‖a‖ ≤ 1 ∧ f = algebraMap K (Entire K) a := by
  have hf' := isEntire_coeff f
  have hcoeff : ∀ n, n ≠ 0 → coeff f n = 0 := fun n hn => by
    by_contra hcn
    have hpos : 0 < ‖coeff f n‖ := norm_pos_iff.mpr hcn
    have hb : ∀ r ∈ R, ‖coeff f n‖ * r ^ n ≤ 1 := fun r hr =>
      (le_gnorm hf' (hRpos r hr) n).trans (hle r hr)
    rcases lt_or_gt_of_ne hn with hneg | hposn
    · -- `n < 0`: small radii.
      obtain ⟨r, hr, hrε⟩ := hsmall (min 1 (‖coeff f n‖ / 2)) (lt_min one_pos (half_pos hpos))
      have hr0 := hRpos r hr
      have hr1 : r ≤ 1 := hrε.trans (min_le_left _ _)
      have h1 := hb r hr
      have h2 : r ^ (-1 : ℤ) ≤ r ^ n := zpow_le_zpow_right_of_le_one₀ hr0 hr1 (by omega)
      have h3 : ‖coeff f n‖ * r⁻¹ ≤ 1 := by
        have := mul_le_mul_of_nonneg_left h2 hpos.le; simp only [zpow_neg, zpow_one] at this
        linarith
      rw [mul_inv_le_iff₀ hr0, one_mul] at h3
      linarith [hrε.trans (min_le_right _ _)]
    · -- `n > 0`: large radii.
      obtain ⟨r, hr, hrC⟩ := hbig (max 1 (2 / ‖coeff f n‖))
      have hr0 := hRpos r hr
      have hr1 : 1 ≤ r := (le_max_left _ _).trans hrC
      have h1 := hb r hr
      have h2 : r ^ (1 : ℤ) ≤ r ^ n := zpow_le_zpow_right₀ hr1 (by omega)
      have h3 : ‖coeff f n‖ * r ≤ 1 := by
        have := mul_le_mul_of_nonneg_left h2 hpos.le; simp only [zpow_one] at this
        linarith
      have h4 : 2 / ‖coeff f n‖ ≤ r := (le_max_right _ _).trans hrC
      rw [div_le_iff₀ hpos] at h4
      linarith
  obtain ⟨r, hr⟩ := hbig 0
  refine ⟨coeff f 0, ?_, ext_coeff (funext fun n => ?_)⟩
  · have := (le_gnorm hf' (hRpos r hr.1) 0).trans (hle r hr.1)
    simpa [tnorm] using this
  · rw [coeff_algebraMap]
    by_cases hn : n = 0
    · subst hn; simp
    · rw [hcoeff n hn]; simp [hn]

/-- [EtTh] Proposition 3.2(ii) for the component circles `|U| = ‖q‖^a`, `a ∈ ℤ`, of the
special fibre of the universal combinatorial covering of the Tate curve. -/
theorem eq_algebraMap_of_gnorm_qpow_le (f : Entire K) {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)
    (hle : ∀ a : ℤ, gn f (‖q‖ ^ a) ≤ 1) :
    ∃ a : K, ‖a‖ ≤ 1 ∧ f = algebraMap K (Entire K) a := by
  refine eq_algebraMap_of_gnorm_le f (Set.range fun a : ℤ => ‖q‖ ^ a)
    (by rintro _ ⟨a, rfl⟩; exact zpow_pos hq0 a) (fun C => ?_) (fun ε hε => ?_)
    (by rintro _ ⟨a, rfl⟩; exact hle a)
  · obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C ((one_lt_inv₀ hq0).mpr hq1)
    exact ⟨_, ⟨-(n : ℤ), rfl⟩, by
      change C ≤ ‖q‖ ^ (-(n : ℤ)); rw [zpow_neg, zpow_natCast, ← inv_pow]; exact hn.le⟩
  · obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hq1
    exact ⟨_, ⟨(n : ℤ), rfl⟩, by change ‖q‖ ^ (n : ℤ) ≤ ε; rw [zpow_natCast]; exact hn.le⟩

end Entire

end Iut.Frobenioid.BAn
