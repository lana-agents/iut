/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.Tempered.RatFunGauss
import Mathlib.Analysis.Normed.Field.UnitBall
import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Infinitely divisible functions on `𝔾_m^an` ([EtTh] Proposition 3.2(iii), MR18 T8, route B-an)

[EtTh] Proposition 3.2(iii): a nonzero meromorphic function `f` on the universal combinatorial
covering `Z_∞` (over a finite extension `L` of `ℚ_p`) that has an `N`-th root `g_N` for every
`N ≥ 1` is `1`. The proof there: the divisor of `f` is zero, so `f ∈ O_L^×` by Proposition
3.2(ii), and `⋂_N (O_L^×)^N = {1}` "from the well-known structure of `O_L^×`".

This file proves

* `eq_one_of_forall_pow_eq`: **`⋂_N (O_L^×)^N = {1}`** — more precisely, a nonzero `x` in a locally
  compact (`ProperSpace`) ultrametric nontrivially normed field `L` with an `N`-th root in `L` for
  every `N ≥ 1` is `1` (first `‖x‖ = 1`, since norms `< 1` are bounded away from `1`, then the
  open subgroups `{‖y - 1‖ < ε}` of the compact group `{‖y‖ = 1}` have finite index);
* `Entire.eq_one_of_forall_pow`: **Proposition 3.2(iii) for regular functions on `𝔾_m^an`**: a
  nonzero `f ∈ E(L)` with `N`-th roots in `E(L)` for all `N ≥ 1` is `1` (the Gauss lemma forces
  the dominant index to be `0` on every circle, so `f ∈ L^×`, and then the statement above).

The version for *meromorphic* `f` needs the cancellation of common zeros (Weierstrass
factorisation on annuli); recorded in the MR18 plan as the next B-an step.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace Iut.Frobenioid.BAn

open Filter Topology Metric

section Field

variable {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L] [ProperSpace L]

/-- In a locally compact ultrametric field, the norms `< 1` are bounded away from `1`. -/
lemma exists_norm_le_of_norm_lt_one : ∃ ρ < 1, ∀ y : L, ‖y‖ < 1 → ‖y‖ ≤ ρ := by
  by_contra h
  push Not at h
  have hρ : ∀ n : ℕ, 1 - 1 / ((n : ℝ) + 1) < 1 := fun n => by
    have : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  choose y hy using fun n : ℕ => h (1 - 1 / ((n : ℝ) + 1)) (hρ n)
  obtain ⟨a, -, φ, hφ, hlim⟩ := (isCompact_closedBall (0 : L) 1).tendsto_subseq
    (fun n => mem_closedBall_zero_iff.mpr (hy n).1.le)
  have hn1 : Tendsto (fun n => ‖y (φ n)‖) atTop (𝓝 1) := by
    have hlow : Tendsto (fun n : ℕ => 1 - 1 / ((φ n : ℝ) + 1)) atTop (𝓝 1) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hφ.tendsto_atTop
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds
      (fun n => (hy (φ n)).2.le) (fun n => (hy (φ n)).1.le)
  have ha : ‖a‖ = 1 := tendsto_nhds_unique ((continuous_norm.tendsto a).comp hlim) hn1
  have hev : ∀ᶠ n in atTop, ‖y (φ n) - a‖ < 1 := by
    have := (tendsto_iff_norm_sub_tendsto_zero.mp hlim).eventually (gt_mem_nhds one_pos)
    simpa using this
  obtain ⟨n, hn⟩ := hev.exists
  have hne : ‖a‖ ≠ ‖y (φ n) - a‖ := by rw [ha]; exact hn.ne'
  have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne
  rw [add_sub_cancel, ha, max_eq_left hn.le] at this
  exact (hy (φ n)).1.ne this

lemma not_norm_lt_one_of_forall_pow_eq {x : L} (hx : x ≠ 0)
    (h : ∀ N : ℕ, 0 < N → ∃ b : L, b ^ N = x) : ¬ ‖x‖ < 1 := by
  intro hx1
  obtain ⟨ρ, hρ1, hρ⟩ := exists_norm_le_of_norm_lt_one (L := L)
  have hρ0 : 0 ≤ ρ := by simpa using hρ 0 (by simp)
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hbound : ∀ N : ℕ, 0 < N → ‖x‖ ≤ ρ ^ N := fun N hN => by
    obtain ⟨b, hb⟩ := h N hN
    have hb1 : ‖b‖ < 1 := by
      by_contra hb1
      push Not at hb1
      have : 1 ≤ ‖b‖ ^ N := one_le_pow₀ hb1
      rw [← norm_pow, hb] at this
      linarith
    rw [← hb, norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg b) (hρ b hb1) N
  obtain ⟨N, hN⟩ := ((tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).eventually
    (gt_mem_nhds hxpos)).exists_forall_of_atTop
  have := hbound (N + 1) (Nat.succ_pos N)
  linarith [hN (N + 1) (Nat.le_succ N)]

lemma norm_eq_one_of_forall_pow_eq {x : L} (hx : x ≠ 0)
    (h : ∀ N : ℕ, 0 < N → ∃ b : L, b ^ N = x) : ‖x‖ = 1 := by
  refine le_antisymm ?_ (not_lt.mp (not_norm_lt_one_of_forall_pow_eq hx h))
  have hinv := not_norm_lt_one_of_forall_pow_eq (inv_ne_zero hx) fun N hN => by
    obtain ⟨b, hb⟩ := h N hN
    exact ⟨b⁻¹, by rw [inv_pow, hb]⟩
  rw [norm_inv, not_lt, one_le_inv₀ (norm_pos_iff.mpr hx)] at hinv
  exact hinv

/-- The subgroup `{‖y - 1‖ < ε}` of the unit sphere (`0 < ε ≤ 1`). -/
def nearOne (ε : ℝ) (hε : 0 < ε) (_hε1 : ε ≤ 1) : Subgroup (sphere (0 : L) 1) where
  carrier := {y | ‖(y : L) - 1‖ < ε}
  one_mem' := by simp [Metric.unitSphere.coe_one, hε]
  mul_mem' := by
    intro y z hy hz
    simp only [Set.mem_setOf_eq, Metric.unitSphere.coe_mul] at hy hz ⊢
    have hy1 : ‖(y : L)‖ = 1 := by simp
    have e : (y : L) * z - 1 = (y : L) * (z - 1) + (y - 1) := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ hy)
    rw [norm_mul, hy1, one_mul]; exact hz
  inv_mem' := by
    intro y hy
    simp only [Set.mem_setOf_eq, Metric.unitSphere.coe_inv] at hy ⊢
    have hy1 : ‖(y : L)‖ = 1 := by simp
    have hy0 : (y : L) ≠ 0 := by rw [← norm_ne_zero_iff, hy1]; exact one_ne_zero
    have e : (y : L)⁻¹ - 1 = -((y : L)⁻¹ * ((y : L) - 1)) := by field_simp; ring
    rw [e, norm_neg, norm_mul, norm_inv, hy1, inv_one, one_mul]; exact hy

lemma isOpen_nearOne (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    IsOpen ((nearOne (L := L) ε hε hε1 : Subgroup _) : Set (sphere (0 : L) 1)) :=
  isOpen_lt ((continuous_subtype_val.sub continuous_const).norm) continuous_const

/-- **`⋂_N (O_L^×)^N = {1}`** for a locally compact ultrametric field `L` (the last step of
[EtTh] Proposition 3.2(iii)). -/
theorem eq_one_of_forall_pow_eq {x : L} (hx : x ≠ 0)
    (h : ∀ N : ℕ, 0 < N → ∃ b : L, b ^ N = x) : x = 1 := by
  have hx1 := norm_eq_one_of_forall_pow_eq hx h
  have : CompactSpace (sphere (0 : L) 1) := isCompact_iff_compactSpace.mp (isCompact_sphere 0 1)
  by_contra hne
  have hd : 0 < ‖x - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  set ε := min 1 ‖x - 1‖
  have hε : 0 < ε := lt_min one_pos hd
  let U := nearOne (L := L) ε hε (min_le_left _ _)
  have hfin : Finite (sphere (0 : L) 1 ⧸ U) :=
    Subgroup.quotient_finite_of_isOpen U (isOpen_nearOne ε hε _)
  have hN : 0 < U.index := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
  obtain ⟨b, hb⟩ := h U.index hN
  have hb1 : ‖b‖ = 1 := by
    have : ‖b‖ ^ U.index = 1 := by rw [← norm_pow, hb, hx1]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg b) hN.ne').mp this
  let bs : sphere (0 : L) 1 := ⟨b, by simp [hb1]⟩
  have hmem := U.pow_index_mem bs
  change ‖((bs ^ U.index : sphere (0 : L) 1) : L) - 1‖ < ε at hmem
  rw [Metric.unitSphere.coe_pow] at hmem
  change ‖b ^ U.index - 1‖ < ε at hmem
  rw [hb] at hmem
  exact (hmem.trans_le (min_le_right _ _)).false

end Field

/-! ### [EtTh] Proposition 3.2(iii) on `𝔾_m^an` -/

namespace Entire

variable {L : Type*} [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L]

lemma lo_pow {g : Entire L} (hg : g ≠ 0) {r : ℝ} (hr : 0 < r) (N : ℕ) :
    lo (coeff (g ^ N)) r = N * lo (coeff g) r := by
  induction N with
  | zero => rw [pow_zero, coeff_one, lo_single 0 1 one_ne_zero hr]; simp
  | succ n ih =>
    rw [pow_succ, lo_mul (pow_ne_zero n hg) hg hr, ih]; push_cast; ring

lemma hi_pow {g : Entire L} (hg : g ≠ 0) {r : ℝ} (hr : 0 < r) (N : ℕ) :
    hi (coeff (g ^ N)) r = N * hi (coeff g) r := by
  induction N with
  | zero => rw [pow_zero, coeff_one, hi_single 0 1 one_ne_zero hr]; simp
  | succ n ih =>
    rw [pow_succ, hi_mul (pow_ne_zero n hg) hg hr, ih]; push_cast; ring

/-- If `f ≠ 0` has an `N`-th root in `E(L)` for some `N` exceeding `|lo|` and `hi - lo` at every
radius, both dominant indices of the root and of `f` vanish there. -/
lemma dom_zero_of_root {f g : Entire L} (hf : f ≠ 0) {N : ℕ} (hgN : g ^ N = f) {r : ℝ}
    (hr : 0 < r) (hN1 : |lo (coeff f) r| < N) (hN2 : hi (coeff f) r - lo (coeff f) r < N) :
    lo (coeff g) r = 0 ∧ hi (coeff g) r = 0 := by
  have habs := abs_nonneg (lo (coeff f) r)
  have hN0 : N ≠ 0 := by rintro rfl; push_cast at hN1; omega
  have hg : g ≠ 0 := by rintro rfl; rw [zero_pow hN0] at hgN; exact hf hgN.symm
  have h1 := lo_pow hg hr N
  have h2 := hi_pow hg hr N
  rw [hgN] at h1 h2
  have hle := lo_le_hi (isEntire_coeff g) (coeff_ne_zero hg) hr
  have hNpos : (0 : ℤ) < N := lt_of_le_of_lt (abs_nonneg _) hN1
  have hlo : lo (coeff g) r = 0 := by
    by_contra h0
    have : (N : ℤ) ≤ |lo (coeff f) r| := by
      rw [h1, abs_mul, abs_of_pos hNpos]
      exact le_mul_of_one_le_right hNpos.le (Int.one_le_abs h0)
    omega
  refine ⟨hlo, ?_⟩
  rw [hlo, mul_zero] at h1
  rw [h1, sub_zero, h2] at hN2
  have : hi (coeff g) r < 1 := by
    by_contra h3; push Not at h3
    have := mul_le_mul_of_nonneg_left h3 hNpos.le
    omega
  omega

/-- If `f ≠ 0` has `N`-th roots in `E(L)` for all `N ≥ 1`, then `f ∈ L^×` and each root lies in
`L^×`. -/
lemma eq_algebraMap_of_forall_pow {f : Entire L} (hf : f ≠ 0)
    (h : ∀ N : ℕ, 0 < N → ∃ g : Entire L, g ^ N = f) {g : Entire L} {N : ℕ} (hN : 0 < N)
    (hgN : g ^ N = f) : g = algebraMap L (Entire L) (coeff g 0) := by
  have hg : g ≠ 0 := by rintro rfl; rw [zero_pow hN.ne'] at hgN; exact hf hgN.symm
  -- `f` has dominant index `0` everywhere.
  have hdomf : ∀ r : ℝ, 0 < r → lo (coeff f) r = 0 ∧ hi (coeff f) r = 0 := fun r hr => by
    set M := (|lo (coeff f) r| + (hi (coeff f) r - lo (coeff f) r)).toNat + 1
    have hM : 0 < M := Nat.succ_pos _
    obtain ⟨g', hg'⟩ := h M hM
    have hle := lo_le_hi (isEntire_coeff f) (coeff_ne_zero hf) hr
    have hM' : (|lo (coeff f) r| + (hi (coeff f) r - lo (coeff f) r)) < M := by
      have := Int.self_le_toNat (|lo (coeff f) r| + (hi (coeff f) r - lo (coeff f) r))
      omega
    have habs := abs_nonneg (lo (coeff f) r)
    obtain ⟨h1, h2⟩ := dom_zero_of_root hf hg' hr (by omega) (by omega)
    have hg'0 : g' ≠ 0 := by rintro rfl; rw [zero_pow hM.ne'] at hg'; exact hf hg'.symm
    rw [← hg', lo_pow hg'0 hr, hi_pow hg'0 hr, h1, h2]
    simp
  -- hence so does `g`.
  have hdomg : ∀ r : ℝ, 0 < r → lo (coeff g) r = 0 ∧ hi (coeff g) r = 0 := fun r hr => by
    have h1 := lo_pow hg hr N
    have h2 := hi_pow hg hr N
    rw [hgN, (hdomf r hr).1] at h1
    rw [hgN, (hdomf r hr).2] at h2
    have hN' : (N : ℤ) ≠ 0 := by exact_mod_cast hN.ne'
    exact ⟨(mul_eq_zero.mp h1.symm).resolve_left hN', (mul_eq_zero.mp h2.symm).resolve_left hN'⟩
  conv_lhs => rw [eq_smul_mono_of_dom hg hdomg]
  rw [mono_zero, Algebra.smul_def, mul_one]

/-- **[EtTh] Proposition 3.2(iii) for regular functions on `𝔾_m^an`.** Over a locally compact
ultrametric field `L`, a nonzero entire Laurent series with an `N`-th root in `E(L)` for every
`N ≥ 1` is `1`. -/
theorem eq_one_of_forall_pow [ProperSpace L] {f : Entire L} (hf : f ≠ 0)
    (h : ∀ N : ℕ, 0 < N → ∃ g : Entire L, g ^ N = f) : f = 1 := by
  have hf' := eq_algebraMap_of_forall_pow hf h one_pos (pow_one f)
  have hx : coeff f 0 ≠ 0 := by
    intro h0; rw [h0, map_zero] at hf'; exact hf hf'
  have hroot : ∀ N : ℕ, 0 < N → ∃ b : L, b ^ N = coeff f 0 := fun N hN => by
    obtain ⟨g, hg⟩ := h N hN
    refine ⟨coeff g 0, (algebraMap L (Entire L)).injective ?_⟩
    rw [map_pow, ← eq_algebraMap_of_forall_pow hf h hN hg, hg, ← hf']
  rw [hf', eq_one_of_forall_pow_eq hx hroot, map_one]

end Entire

end Iut.Frobenioid.BAn
