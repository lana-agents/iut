/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.Tempered.RatFunZero

/-!
# Division by `U - α` in `E(K)` and the simple zeros of `Θ̈` (MR18 T8, route B-an)

* `exists_eq_lin_mul`: **Weierstrass division in `E(K)`**: if `f(α) = 0` (`α ∈ Kˣ`), then
  `f = (U - α)·g` with `g ∈ E(K)`. On the unit circle this is tate-curves-theta's `wCoeff`
  (with its forward and backward bounds); the quotient is entire by those bounds, and the general
  case follows by scaling.
* `lsum_ne_zero_of_lo_eq_hi`: a series with a single dominant index on `|U| = r` has no zero
  there.
* `thetaDd_simple_zero`: **[EtTh] Proposition 1.4(i), "each zero has multiplicity 1"**: for
  each cusp `α = ±q^{a/2}` (`2 ≠ 0` in `K`), `Θ̈ = (U - α)·h` with `h(α) ≠ 0`. (The width of the
  Newton polygon of `Θ̈` on that circle is `2`, and both `±q^{a/2}` are zeros.)
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace Iut.Frobenioid.BAn

open Polynomial TateCurvesTheta TateParameter Filter Topology

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]

/-! ### Single dominant index ⇒ no zero on the circle -/

theorem lsum_ne_zero_of_lo_eq_hi {c : ℤ → K} (hc : IsEntire c) (hc0 : c ≠ 0) (u : Kˣ)
    (h : lo c ‖(u : K)‖ = hi c ‖(u : K)‖) : lsum c u ≠ 0 := by
  have hr : 0 < ‖(u : K)‖ := norm_pos_iff.mpr u.ne_zero
  refine IsUltrametricDist.tsum_ne_zero_of_dominant (hc u) (i₀ := lo c ‖(u : K)‖)
    (mul_ne_zero (coeff_lo_ne_zero hc hc0 hr) (zpow_ne_zero _ u.ne_zero)) fun n hn => ?_
  have e : ∀ m, ‖c m * (u : K) ^ m‖ = tnorm c ‖(u : K)‖ m := fun m => by
    rw [norm_mul, norm_zpow, tnorm]
  rw [e, e, tnorm_lo hc hc0 hr]
  refine tnorm_lt_of_notMem hc hc0 hr fun hm => hn (le_antisymm ?_ (le_lo_of_mem hc hc0 hr hm))
  rw [h]; exact le_hi_of_mem hc hc0 hr hm

/-! ### Weierstrass division by `U - α` -/

lemma isEntire_wCoeff {c : ℤ → K} (hc : IsEntire c) {α : K} (hα1 : ‖α‖ = 1)
    (hroot : (∑' n : ℤ, c n * α ^ n) = 0) : IsEntire (StrassmannSphere.wCoeff c α) := by
  intro u
  have hc1 : Summable c := by simpa using hc 1
  set r := ‖(u : K)‖
  have hr : 0 < r := norm_pos_iff.mpr u.ne_zero
  set R := max 1 r
  set ρ := min 1 r
  have hR : 0 < R := one_pos.trans_le (le_max_left _ _)
  have hρ : 0 < ρ := lt_min one_pos hr
  refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_
  rw [tendsto_zero_iff_norm_tendsto_zero]
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε2 : 0 < ε / 2 := half_pos hε
  -- the finitely many large term norms of `c` at radii `R` and `ρ`
  have hfin1 : {n : ℤ | ¬ tnorm c R n < ε / 2}.Finite :=
    Filter.eventually_cofinite.mp ((hc.tendsto_tnorm hR).eventually (gt_mem_nhds hε2))
  have hfin2 : {n : ℤ | ¬ tnorm c ρ n < ε / 2}.Finite :=
    Filter.eventually_cofinite.mp ((hc.tendsto_tnorm hρ).eventually (gt_mem_nhds hε2))
  obtain ⟨B, hB⟩ := ((hfin1.union hfin2).image Int.natAbs).bddAbove
  have hsmall : ∀ m : ℤ, (B : ℤ) < |m| → tnorm c R m < ε / 2 ∧ tnorm c ρ m < ε / 2 :=
    fun m hm => by
      by_contra hcon
      have hmem : m.natAbs ∈ Int.natAbs '' ({n : ℤ | ¬ tnorm c R n < ε / 2} ∪
          {n : ℤ | ¬ tnorm c ρ n < ε / 2}) := ⟨m, by
        rcases not_and_or.mp hcon with h | h
        · exact Or.inl h
        · exact Or.inr h, rfl⟩
      have := hB hmem
      have : |m| ≤ (B : ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast this
      omega
  refine Filter.eventually_cofinite.mpr ((Set.finite_Icc (-(B : ℤ)) B).subset fun n hn => ?_)
  simp only [Set.mem_setOf_eq, Real.dist_eq, sub_zero, abs_norm, not_lt] at hn
  simp only [Set.mem_Icc]
  by_contra hout
  have hnB : (B : ℤ) < |n| := by rw [lt_abs]; omega
  rw [norm_mul, norm_zpow] at hn
  rcases le_or_gt 0 n with hn0 | hn0
  · -- forward bound
    have hb : ‖StrassmannSphere.wCoeff c α n‖ ≤ ε / 2 * (R ^ n)⁻¹ := by
      refine StrassmannSphere.wCoeff_norm_le_above hα1.le n (by positivity) fun m hm => ?_
      have hm' : (B : ℤ) < |m| := by rw [abs_of_pos (by omega : (0 : ℤ) < m)]; omega
      have h1 := (hsmall m hm').1
      rw [tnorm] at h1
      have hRm : R ^ n ≤ R ^ m := zpow_le_zpow_right₀ (le_max_left _ _) hm.le
      rw [le_mul_inv_iff₀ (zpow_pos hR n)]
      calc ‖c m‖ * R ^ n ≤ ‖c m‖ * R ^ m := mul_le_mul_of_nonneg_left hRm (norm_nonneg _)
        _ ≤ ε / 2 := h1.le
    have hrR : r ^ n ≤ R ^ n := by
      obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn0
      rw [zpow_natCast, zpow_natCast]
      exact pow_le_pow_left₀ hr.le (le_max_right 1 r) k
    have : ‖StrassmannSphere.wCoeff c α n‖ * r ^ n ≤ ε / 2 := by
      calc ‖StrassmannSphere.wCoeff c α n‖ * r ^ n ≤ ε / 2 * (R ^ n)⁻¹ * R ^ n :=
            mul_le_mul hb hrR (zpow_nonneg hr.le _) (by positivity)
        _ = ε / 2 := by rw [inv_mul_cancel_right₀ (zpow_pos hR n).ne']
    linarith
  · -- backward bound
    have hb : ‖StrassmannSphere.wCoeff c α n‖ ≤ ε / 2 * (ρ ^ n)⁻¹ := by
      refine StrassmannSphere.wCoeff_norm_le_below hc1 hα1 hroot n (by positivity) fun m hm => ?_
      have hm' : (B : ℤ) < |m| := by rw [abs_of_neg (by omega : m < 0)]; omega
      have h1 := (hsmall m hm').2
      rw [tnorm] at h1
      have hρm : ρ ^ n ≤ ρ ^ m := zpow_le_zpow_right_of_le_one₀ hρ (min_le_left _ _) hm
      rw [le_mul_inv_iff₀ (zpow_pos hρ n)]
      calc ‖c m‖ * ρ ^ n ≤ ‖c m‖ * ρ ^ m := mul_le_mul_of_nonneg_left hρm (norm_nonneg _)
        _ ≤ ε / 2 := h1.le
    have hrρ : r ^ n ≤ ρ ^ n := by
      obtain ⟨k, hk⟩ := Int.exists_eq_neg_ofNat hn0.le
      rw [hk, zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
      exact inv_anti₀ (pow_pos hρ k) (pow_le_pow_left₀ hρ.le (min_le_right 1 r) k)
    have : ‖StrassmannSphere.wCoeff c α n‖ * r ^ n ≤ ε / 2 := by
      calc ‖StrassmannSphere.wCoeff c α n‖ * r ^ n ≤ ε / 2 * (ρ ^ n)⁻¹ * ρ ^ n :=
            mul_le_mul hb hrρ (zpow_nonneg hr.le _) (by positivity)
        _ = ε / 2 := by rw [inv_mul_cancel_right₀ (zpow_pos hρ n).ne']
    linarith

lemma polyE_lin (α : K) :
    polyE (lin α) = Entire.mono 1 - algebraMap K (Entire K) α := by
  refine Subtype.ext ?_
  rw [coe_polyE]
  funext u
  change (X - C α).eval (u : K) = ((Entire.mono 1 : Entire K) : Kˣ → K) u - α
  rw [Entire.coe_mono]
  simp

/-- Division on the unit circle. -/
lemma exists_eq_lin_mul_one {f : Entire K} {α : Kˣ} (hα1 : ‖(α : K)‖ = 1)
    (hf : (f : Kˣ → K) α = 0) : ∃ g : Entire K, f = polyE (lin (α : K)) * g := by
  have hc := Entire.isEntire_coeff f
  have hroot : (∑' n : ℤ, Entire.coeff f n * (α : K) ^ n) = 0 := by
    rw [← hf, Entire.coe_eq_lsum]; rfl
  refine ⟨Entire.ofCoeff _ (isEntire_wCoeff hc hα1 hroot), Entire.ext_coeff (funext fun n => ?_)⟩
  rw [polyE_lin, sub_mul, sub_eq_add_neg, Entire.coeff_add, Pi.add_apply, Entire.coeff_neg,
    Pi.neg_apply,
    Entire.coeff_mono_mul, ← Algebra.smul_def, Entire.coeff_smul, Pi.smul_apply, smul_eq_mul,
    Entire.coeff_ofCoeff]
  have := StrassmannSphere.wCoeff_rec' (by simpa using hc 1) hα1.le n
  rw [← this]; ring

/-- **Weierstrass division in `E(K)`**: a zero `α` of `f` splits off the factor `U - α`. -/
theorem exists_eq_lin_mul {f : Entire K} {α : Kˣ} (hf : (f : Kˣ → K) α = 0) :
    ∃ g : Entire K, f = polyE (lin (α : K)) * g := by
  -- scale the zero to `1`
  have hf' : ((Entire.scale α f : Entire K) : Kˣ → K) 1 = 0 := by
    rw [Entire.coe_scale, mul_one]; exact hf
  obtain ⟨g, hg⟩ := exists_eq_lin_mul_one (f := Entire.scale α f) (α := 1) (by simp) hf'
  refine ⟨((α : K)⁻¹) • Entire.scale α⁻¹ g, Subtype.ext (funext fun u => ?_)⟩
  have hu := congrFun (congrArg Subtype.val hg) (α⁻¹ * u)
  change ((Entire.scale α f : Entire K) : Kˣ → K) (α⁻¹ * u) =
    ((polyE (lin ((1 : Kˣ) : K)) : Entire K) : Kˣ → K) (α⁻¹ * u) *
      ((g : Entire K) : Kˣ → K) (α⁻¹ * u) at hu
  rw [Entire.coe_scale, mul_inv_cancel_left, coe_polyE] at hu
  change (f : Kˣ → K) u = ((polyE (lin (α : K)) : Entire K) : Kˣ → K) u *
    ((α : K)⁻¹ * ((Entire.scale α⁻¹ g : Entire K) : Kˣ → K) u)
  rw [hu, coe_polyE, Entire.coe_scale]
  simp only [lin, eval_sub, eval_X, eval_C, Units.val_mul, Units.val_inv_eq_inv_val,
    Units.val_one]
  have hα0 : (α : K) ≠ 0 := α.ne_zero
  field_simp

/-! ### The factor `U - α` on its own circle -/

lemma lo_hi_lin_at (α : Kˣ) :
    lo (polyCoeff (lin (α : K))) ‖(α : K)‖ = 0 ∧ hi (polyCoeff (lin (α : K))) ‖(α : K)‖ = 1 := by
  set r := ‖(α : K)‖
  have hr : 0 < r := norm_pos_iff.mpr α.ne_zero
  have hc := isEntire_lin (α : K)
  have hc0 := lin_ne_zero (α : K)
  have hcoef : ∀ n : ℤ, ‖polyCoeff (lin (α : K)) n‖ =
      if n = 0 then ‖(α : K)‖ else if n = 1 then 1 else 0 := fun n => by
    have := tnorm_lin (α : K) n
    rwa [tnorm, one_zpow, mul_one] at this
  have ht : ∀ n : ℤ, tnorm (polyCoeff (lin (α : K))) r n =
      if n = 0 then r else if n = 1 then r else 0 := fun n => by
    rw [tnorm, hcoef]
    split_ifs with h0 h1
    · subst h0; simp [r]
    · subst h1; simp
    · simp
  have hg : gnorm (polyCoeff (lin (α : K))) r = r := by
    refine le_antisymm (gnorm_le fun n => ?_) ?_
    · rw [ht]; split_ifs
      · exact le_rfl
      · exact le_rfl
      · exact hr.le
    · have := le_gnorm hc hr 0; rwa [ht, if_pos rfl] at this
  refine ⟨lo_eq_of hc hc0 hr (by rw [ht, if_pos rfl, hg]) fun m hm => ?_,
    hi_eq_of hc hc0 hr (by rw [ht, if_neg one_ne_zero, if_pos rfl, hg]) fun m hm => ?_⟩
  · rw [ht, hg, if_neg (by omega), if_neg (by omega)]; exact hr
  · rw [ht, hg, if_neg (by omega), if_neg (by omega)]; exact hr

/-- Splitting off `U - α` lowers the width on `|U| = ‖α‖` by one. -/
lemma width_lin_mul {α : Kˣ} {g : Entire K} (hg : g ≠ 0) :
    hi (Entire.coeff (polyE (lin (α : K)) * g)) ‖(α : K)‖ -
        lo (Entire.coeff (polyE (lin (α : K)) * g)) ‖(α : K)‖ =
      hi (Entire.coeff g) ‖(α : K)‖ - lo (Entire.coeff g) ‖(α : K)‖ + 1 := by
  have hr : 0 < ‖(α : K)‖ := norm_pos_iff.mpr α.ne_zero
  have hl := polyE_ne_zero (X_sub_C_ne_zero (α : K))
  rw [Entire.hi_mul hl hg hr, Entire.lo_mul hl hg hr, coeff_polyE, (lo_hi_lin_at α).1,
    (lo_hi_lin_at α).2]
  ring

/-! ### The zeros of `Θ̈` are simple -/

variable (t : TateParameter K)

/-- **[EtTh] Proposition 1.4(i): each zero of `Θ̈` has multiplicity `1`.** For a square root `s`
of `q` and a cusp `α = ±s^a` (`= ±q^{a/2}`), `Θ̈ = (U - α)·h` with `h(α) ≠ 0` (`2 ≠ 0` in `K`). -/
theorem thetaDd_simple_zero (h2 : (2 : K) ≠ 0) {s : Kˣ} (hs : (s : K) ^ 2 = t.q) (a : ℤ)
    {α : Kˣ} (hα : α = s ^ a ∨ α = -(s ^ a)) :
    ∃ h : Entire K, thetaDd t = polyE (lin (α : K)) * h ∧ (h : Kˣ → K) α ≠ 0 := by
  have hnorm : ‖(α : K)‖ = ‖(s : K)‖ ^ a := by
    rcases hα with rfl | rfl <;> simp [Units.val_zpow_eq_zpow_val, norm_zpow]
  have hzero : ∀ β : Kˣ, (β = s ^ a ∨ β = -(s ^ a)) → ((thetaDd t : Entire K) : Kˣ → K) β = 0 :=
    fun β hβ => by
      rw [thetaDd_eq_zero_iff]
      refine ⟨a, ?_⟩
      have key : ((s : K) ^ a) ^ 2 = ((s : K) ^ 2) ^ a := by
        rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]
      have : (β : K) ^ 2 = ((s : K) ^ 2) ^ a := by
        rcases hβ with rfl | rfl
        · rw [Units.val_zpow_eq_zpow_val]; exact key
        · rw [Units.val_neg, Units.val_zpow_eq_zpow_val, neg_sq]; exact key
      rw [this, hs]
  obtain ⟨h, hh⟩ := exists_eq_lin_mul (hzero α hα)
  refine ⟨h, hh, fun hhα => ?_⟩
  have hβ : (-α = s ^ a ∨ -α = -(s ^ a)) := by
    rcases hα with rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl (neg_neg _)
  -- `h(-α) = 0`
  have hα0 : (α : K) ≠ 0 := α.ne_zero
  have hhβ : (h : Kˣ → K) (-α) = 0 := by
    have := hzero (-α) hβ
    rw [hh, Entire.coe_mul, Pi.mul_apply, coe_polyE] at this
    simp only [lin, eval_sub, eval_X, eval_C, Units.val_neg] at this
    rcases mul_eq_zero.mp this with h1 | h1
    · exact absurd (by linear_combination -h1 : (2 : K) * α = 0) (mul_ne_zero h2 hα0)
    · exact h1
  obtain ⟨h₂, hh₂⟩ := exists_eq_lin_mul hhβ
  have hT0 := thetaDd_ne_zero t
  have hh0 : h ≠ 0 := by rintro rfl; rw [mul_zero] at hh; exact hT0 hh
  have hh₂0 : h₂ ≠ 0 := by rintro rfl; rw [mul_zero] at hh₂; exact hh0 hh₂
  -- widths on the circle `|U| = ‖α‖`
  have hw := width_lin_mul (α := α) hh0
  rw [← hh, coeff_thetaDd, hnorm, lo_thetaDd hs, hi_thetaDd hs, ← hnorm] at hw
  have hw2 := width_lin_mul (α := -α) hh₂0
  rw [← hh₂, show ‖((-α : Kˣ) : K)‖ = ‖(α : K)‖ by simp] at hw2
  have hlh : lo (Entire.coeff h₂) ‖(α : K)‖ = hi (Entire.coeff h₂) ‖(α : K)‖ := by omega
  have hne := lsum_ne_zero_of_lo_eq_hi (Entire.isEntire_coeff h₂) (Entire.coeff_ne_zero hh₂0)
    α hlh
  apply hne
  rw [← Entire.coe_eq_lsum]
  have := hhα
  rw [hh₂, Entire.coe_mul, Pi.mul_apply, coe_polyE] at this
  simp only [lin, eval_sub, eval_X, eval_C, Units.val_neg, sub_neg_eq_add] at this
  rcases mul_eq_zero.mp this with h1 | h1
  · exact absurd (by linear_combination h1 : (2 : K) * α = 0) (mul_ne_zero h2 hα0)
  · exact h1

end Iut.Frobenioid.BAn
