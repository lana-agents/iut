/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.AutHolomorphic.Disc.Basic
import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Explicit hyperbolic geometry of the disc

Computations used in the proof of [AbsTopIII] Proposition 2.2 (i) (`Disc/Normalizer.lean`):

* `tanhD u = tanh u` as a point of the disc; `mid_tanh`: **the midpoint of `tanh a` and `tanh b` is
  `tanh ((a + b) / 2)`**;
* `Icc_subset_of_mid`: a closed set of reals containing `0`, `v` and closed under midpoints contains
  `[0, v]` (dyadic subdivision);
* `OnRay w z` (`z w̄ ≥ 0`): `z` lies on the ray from `0` through `w`; `mid_onRay`: midpoints of
  points of a ray lie on the ray;
* `qN z = (1 + |z|²) / (1 - |z|²)` (`= cosh d(0, z)`); `qN_half_I`: for real `a`, `y`,
  `qN (half a (i y)) = qN (half a 0) · qN (i y)` (hyperbolic Pythagoras); `qN_half_d0`:
  `qN (half a 0) = 2 qN(a)² - 1`;
* `half_real`: for real `a`, `half a z = mob A (-z)`, `A = half a 0`; `exists_real_mob_imag`: every
  point of the disc is `mob A (i y)` with `A`, `y` real.
-/

namespace Iut

namespace AutHol

namespace Disc

open Complex Metric Set Filter Topology Uniformization

open scoped ComplexConjugate

/-! ### Real points -/

theorem ofReal_mem_Dk {r : ℝ} (hr : |r| < 1) : (r : ℂ) ∈ Dk := by
  rw [mem_Dk, Complex.norm_real, Real.norm_eq_abs]; exact hr

theorem abs_tanh_lt_one (u : ℝ) : |Real.tanh u| < 1 := by
  have := Real.tanh_bijOn.mapsTo (mem_univ u)
  rw [mem_Ioo] at this
  exact abs_lt.2 this

/-- `tanh u` as a point of the disc. -/
noncomputable def tanhD (u : ℝ) : Dk := ⟨(Real.tanh u : ℂ), ofReal_mem_Dk (abs_tanh_lt_one u)⟩

@[simp] theorem coe_tanhD (u : ℝ) : (tanhD u : ℂ) = Real.tanh u := rfl

theorem tanhD_zero : tanhD 0 = d0 := Subtype.ext (by simp)

theorem continuous_tanh' : Continuous Real.tanh := by
  have : Real.tanh = fun x => Real.sinh x / Real.cosh x := funext Real.tanh_eq_sinh_div_cosh
  rw [this]
  exact Real.continuous_sinh.div Real.continuous_cosh fun x => (Real.cosh_pos x).ne'

theorem continuous_tanhD : Continuous tanhD :=
  (Complex.continuous_ofReal.comp continuous_tanh').subtype_mk _

theorem tanh_add' (a b : ℝ) :
    (Real.tanh b + Real.tanh a) / (1 + Real.tanh a * Real.tanh b) = Real.tanh (a + b) := by
  have ha := Real.cosh_pos a
  have hb := Real.cosh_pos b
  simp only [Real.tanh_eq_sinh_div_cosh, Real.sinh_add, Real.cosh_add]
  have h1 : Real.cosh a * Real.cosh b + Real.sinh a * Real.sinh b ≠ 0 := by
    rw [← Real.cosh_add]; exact (Real.cosh_pos _).ne'
  field_simp
  ring

theorem mob_tanh (a b : ℝ) : mob (Real.tanh a) (Real.tanh b) = (Real.tanh (a + b) : ℂ) := by
  rw [mob, Complex.conj_ofReal, ← tanh_add' a b]
  push_cast
  rfl

theorem mid0_tanh (v : ℝ) : mid0 (Real.tanh v) = (Real.tanh (v / 2) : ℂ) := by
  rw [mid0, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hc := Real.cosh_pos v
  have h1 : 1 - Real.tanh v ^ 2 = (1 / Real.cosh v) ^ 2 := by
    rw [Real.tanh_eq_sinh_div_cosh]
    field_simp
    have := Real.cosh_sq_sub_sinh_sq v
    linarith
  rw [h1, Real.sqrt_sq (by positivity)]
  have hv : v = 2 * (v / 2) := by ring
  have hc2 := Real.cosh_pos (v / 2)
  have e : Real.tanh v / (1 + 1 / Real.cosh v) = Real.tanh (v / 2) := by
    conv_lhs => rw [hv]
    rw [Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh, Real.sinh_two_mul,
      Real.cosh_two_mul]
    have hs := Real.cosh_sq_sub_sinh_sq (v / 2)
    have hpos : 0 < Real.cosh (v / 2) ^ 2 + Real.sinh (v / 2) ^ 2 := by positivity
    field_simp
    linear_combination (Real.sinh (v / 2)) * hs
  rw [← e]
  push_cast
  rfl

/-- **Midpoints of real points**: `mid (tanh a) (tanh b) = tanh ((a + b) / 2)`. -/
theorem mid_tanh (a b : ℝ) : mid (tanhD a) (tanhD b) = tanhD ((a + b) / 2) := by
  apply Subtype.ext
  have e1 : (((mobH (tanhD a)).symm (tanhD b) : Dk) : ℂ) = (Real.tanh (-a + b) : ℂ) := by
    rw [coe_mobH_symm, coe_tanhD, coe_tanhD, ← Complex.ofReal_neg, ← Real.tanh_neg, mob_tanh]
  simp only [mid, coe_mobH]
  rw [e1, mid0_tanh, coe_tanhD, mob_tanh]
  congr 2
  ring

/-! ### Dyadic subdivision -/

/-- **A closed set of reals containing `0`, `v` and closed under midpoints of its points in
`[0, v]` contains `[0, v]`.** -/
theorem Icc_subset_of_mid {S : Set ℝ} (hS : IsClosed S) {v : ℝ} (hv : 0 ≤ v) (h0 : 0 ∈ S)
    (h1 : v ∈ S) (hm : ∀ a ∈ S, ∀ b ∈ S, a ∈ Icc 0 v → b ∈ Icc 0 v → (a + b) / 2 ∈ S) :
    Icc 0 v ⊆ S := by
  -- the dyadic points `k v / 2 ^ n`
  have hdy : ∀ n : ℕ, ∀ k : ℕ, k ≤ 2 ^ n → (k : ℝ) * v / 2 ^ n ∈ S := by
    intro n
    induction n with
    | zero =>
      intro k hk
      interval_cases k
      · simpa using h0
      · simpa using h1
    | succ n ih =>
      intro k hk
      obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' k
      · have hj : j ≤ 2 ^ n := by rw [pow_succ] at hk; omega
        have := ih j hj
        convert this using 1
        push_cast
        rw [pow_succ]
        field_simp
      · have hj : j + 1 ≤ 2 ^ n := by rw [pow_succ] at hk; omega
        have hj' : j ≤ 2 ^ n := by omega
        have hmem : ∀ i : ℕ, i ≤ 2 ^ n → (i : ℝ) * v / 2 ^ n ∈ Icc 0 v := by
          intro i hi
          refine ⟨by positivity, ?_⟩
          rw [div_le_iff₀ (by positivity)]
          have : (i : ℝ) ≤ 2 ^ n := by exact_mod_cast hi
          nlinarith
        have := hm _ (ih j hj') _ (ih (j + 1) hj) (hmem j hj') (hmem (j + 1) hj)
        convert this using 1
        push_cast
        rw [pow_succ]
        field_simp
        ring
  intro u hu
  rcases hv.lt_or_eq with hv | rfl
  · rw [← hS.closure_eq, Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hε hv) (by norm_num : (1 / 2 : ℝ) < 1)
    set k := ⌊u * 2 ^ n / v⌋₊ with hk
    have h2n : (0 : ℝ) < 2 ^ n := by positivity
    have hk1 : (k : ℝ) ≤ u * 2 ^ n / v := Nat.floor_le (by have := hu.1; positivity)
    have hk2 : u * 2 ^ n / v < k + 1 := Nat.lt_floor_add_one _
    have hkn : k ≤ 2 ^ n := by
      have : u * 2 ^ n / v ≤ 2 ^ n := by
        rw [div_le_iff₀ hv]; nlinarith [hu.2]
      have := hk1.trans this
      exact_mod_cast this
    refine ⟨_, hdy n k hkn, ?_⟩
    rw [Real.dist_eq, abs_lt]
    have hpow : ((1 : ℝ) / 2) ^ n = 1 / 2 ^ n := by rw [div_pow, one_pow]
    rw [hpow, lt_div_iff₀ hv, one_div, inv_mul_eq_div] at hn
    rw [le_div_iff₀ hv] at hk1
    rw [div_lt_iff₀ hv] at hk2
    constructor
    · have : (k : ℝ) * v / 2 ^ n ≤ u := by
        rw [div_le_iff₀ h2n]; linarith
      linarith
    · have : u - (k : ℝ) * v / 2 ^ n < v / 2 ^ n := by
        rw [sub_lt_iff_lt_add, ← add_div, lt_div_iff₀ h2n]; linarith
      linarith
  · obtain rfl : u = 0 := le_antisymm hu.2 hu.1
    exact h0

/-! ### Rays from the centre -/

/-- `z` lies on the ray from `0` through `w`: `z w̄` is a nonnegative real. -/
def OnRay (w z : ℂ) : Prop := (z * conj w).im = 0 ∧ 0 ≤ (z * conj w).re

theorem isClosed_onRay (w : ℂ) : IsClosed {z | OnRay w z} := by
  have hc : Continuous fun z : ℂ => z * conj w := continuous_id.mul continuous_const
  exact (isClosed_eq (Complex.continuous_im.comp hc) continuous_const).inter
    (isClosed_le continuous_const (Complex.continuous_re.comp hc))

theorem onRay_self (w : ℂ) : OnRay w w := by
  rw [OnRay, Complex.mul_conj]
  simp [Complex.normSq_nonneg]

theorem onRay_zero (w : ℂ) : OnRay w 0 := by simp [OnRay]

theorem OnRay.symm {w z : ℂ} (h : OnRay w z) : OnRay z w := by
  have e : w * conj z = conj (z * conj w) := by simp [mul_comm]
  rw [OnRay, e, Complex.conj_im, Complex.conj_re, neg_eq_zero]
  exact h

/-- Equivariance of midpoints under automorphisms. -/
theorem mid_holAut {k : Dk ≃ₜ Dk} (hk : k ∈ holAut) (x y : Dk) :
    k (mid x y) = mid (k x) (k y) := by
  apply eq_mid
  have h := conj_half hk (mid x y)
  have := congrArg (fun g : Dk ≃ₜ Dk => g (k x)) h
  simp only [Homeomorph.trans_apply, Homeomorph.symm_apply_apply] at this
  rw [← this, half_mid]

theorem tanh_nonneg {u : ℝ} (hu : 0 ≤ u) : 0 ≤ Real.tanh u := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_nonneg (Real.sinh_nonneg_iff.2 hu) (Real.cosh_pos u).le

/-- The midpoint of two nonnegative real points is a nonnegative real point. -/
theorem mid_real_nonneg {r s : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (hs : 0 ≤ s) (hs1 : s < 1)
    (hr' : (r : ℂ) ∈ Dk) (hs' : (s : ℂ) ∈ Dk) :
    ∃ m : ℝ, 0 ≤ m ∧ (mid ⟨r, hr'⟩ ⟨s, hs'⟩ : ℂ) = m := by
  have er : (⟨r, hr'⟩ : Dk) = tanhD (Real.artanh r) :=
    Subtype.ext (by rw [coe_tanhD, Real.tanh_artanh ⟨by linarith, hr1⟩])
  have es : (⟨s, hs'⟩ : Dk) = tanhD (Real.artanh s) :=
    Subtype.ext (by rw [coe_tanhD, Real.tanh_artanh ⟨by linarith, hs1⟩])
  refine ⟨Real.tanh ((Real.artanh r + Real.artanh s) / 2), tanh_nonneg ?_, ?_⟩
  · have := Real.artanh_nonneg hr
    have := Real.artanh_nonneg hs
    positivity
  · rw [er, es, mid_tanh, coe_tanhD]

/-- **Midpoints of points on a ray lie on the ray.** -/
theorem mid_onRay {w : ℂ} {x y : Dk} (hx : OnRay w x) (hy : OnRay w y) : OnRay w (mid x y) := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp [OnRay]
  have hnw : 0 < ‖w‖ := norm_pos_iff.2 hw
  set u : ℂ := w / ‖w‖ with hu_def
  have hu : ‖u‖ = 1 := by
    rw [hu_def, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm, div_self hnw.ne']
  -- `x = u r` with `r = re (x w̄) / ‖w‖ ≥ 0`
  have decomp : ∀ z : Dk, OnRay w z → ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧ (z : ℂ) = u * r := by
    intro z hz
    refine ⟨((z : ℂ) * conj w).re / ‖w‖, div_nonneg hz.2 hnw.le, ?_, ?_⟩
    · have hre : ((z : ℂ) * conj w).re ≤ ‖(z : ℂ) * conj w‖ := Complex.re_le_norm _
      rw [norm_mul, Complex.norm_conj] at hre
      rw [div_lt_one hnw]
      have := mem_Dk.1 z.2
      nlinarith
    · set c : ℝ := ((z : ℂ) * conj w).re with hc
      have hzw : (z : ℂ) * conj w = (c : ℂ) := by
        apply Complex.ext <;> simp [hc, hz.1]
      have hww : w * conj w = ((‖w‖ ^ 2 : ℝ) : ℂ) := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      have hw' : (‖w‖ : ℂ) ≠ 0 := by exact_mod_cast hnw.ne'
      have hcw : conj w ≠ 0 := by simpa using hw
      have key : (z : ℂ) = c * w / ((‖w‖ ^ 2 : ℝ) : ℂ) := by
        rw [← hww, ← hzw]
        field_simp
      rw [key, hu_def]
      push_cast
      field_simp
  obtain ⟨r, hr0, hr1, hxr⟩ := decomp x hx
  obtain ⟨s, hs0, hs1, hys⟩ := decomp y hy
  have hr' : (r : ℂ) ∈ Dk := ofReal_mem_Dk (by rw [abs_of_nonneg hr0]; exact hr1)
  have hs' : (s : ℂ) ∈ Dk := ofReal_mem_Dk (by rw [abs_of_nonneg hs0]; exact hs1)
  have ex : x = rotH u hu ⟨r, hr'⟩ := Subtype.ext (by rw [coe_rotH, hxr])
  have ey : y = rotH u hu ⟨s, hs'⟩ := Subtype.ext (by rw [coe_rotH, hys])
  obtain ⟨m, hm0, hm⟩ := mid_real_nonneg hr0 hr1 hs0 hs1 hr' hs'
  rw [ex, ey, ← mid_holAut (rotH_mem u hu), coe_rotH, hm]
  have : u * (m : ℂ) * conj w = ((m * ‖w‖ : ℝ) : ℂ) := by
    have hww : w * conj w = ((‖w‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    have hw' : (‖w‖ : ℂ) ≠ 0 := by exact_mod_cast hnw.ne'
    rw [hu_def, div_mul_eq_mul_div, div_mul_eq_mul_div, mul_assoc, mul_comm (m : ℂ),
      ← mul_assoc, hww]
    push_cast
    field_simp
  rw [OnRay, this, Complex.ofReal_im, Complex.ofReal_re]
  exact ⟨rfl, by positivity⟩

/-! ### `cosh` of the distance from the centre -/

/-- `qN z = (1 + |z|²) / (1 - |z|²)`, i.e. `cosh d(0, z)`. -/
noncomputable def qN (z : ℂ) : ℝ := (1 + normSq z) / (1 - normSq z)

theorem normSq_lt_one_of_mem {z : ℂ} (hz : z ∈ Dk) : normSq z < 1 := normSq_lt_one hz

theorem one_le_qN {z : ℂ} (hz : z ∈ Dk) : 1 ≤ qN z := by
  have h := normSq_lt_one_of_mem hz
  have h0 := normSq_nonneg z
  rw [qN, le_div_iff₀ (by linarith)]
  linarith

theorem one_lt_qN {z : ℂ} (hz : z ∈ Dk) (hz0 : z ≠ 0) : 1 < qN z := by
  have h := normSq_lt_one_of_mem hz
  have h0 := normSq_pos.2 hz0
  rw [qN, lt_div_iff₀ (by linarith)]
  linarith

theorem normSq_eq_of_qN_eq {z w : ℂ} (hz : z ∈ Dk) (hw : w ∈ Dk) (h : qN z = qN w) :
    normSq z = normSq w := by
  have h1 := normSq_lt_one_of_mem hz
  have h2 := normSq_lt_one_of_mem hw
  rw [qN, qN, div_eq_div_iff (by linarith) (by linarith)] at h
  linarith

theorem qN_mul_unit {u z : ℂ} (hu : ‖u‖ = 1) : qN (u * z) = qN z := by
  have : normSq u = 1 := by rw [Complex.normSq_eq_norm_sq, hu, one_pow]
  rw [qN, qN, Complex.normSq_mul, this, one_mul]

theorem qN_neg (z : ℂ) : qN (-z) = qN z := by rw [qN, qN, Complex.normSq_neg]

/-! ### Half-turns about real points -/

theorem one_sub_mul_ne_zero {a : ℝ} (ha : |a| < 1) {z : ℂ} (hz : z ∈ Dk) : 1 - a * z ≠ 0 := by
  intro h
  have hlt : ‖(a : ℂ) * z‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have := mem_Dk.1 hz
    have := abs_nonneg a
    nlinarith [norm_nonneg z]
  have e : (a : ℂ) * z = 1 := by linear_combination -h
  rw [e, norm_one] at hlt
  exact lt_irrefl _ hlt

/-- `half a 0 = 2 a / (1 + a²)` for real `a`. -/
theorem coe_half_d0_real {a : ℝ} (ha : (a : ℂ) ∈ Dk) :
    (half ⟨a, ha⟩ d0 : ℂ) = ((2 * a / (1 + a ^ 2) : ℝ) : ℂ) := by
  rw [coe_half_d0]
  simp only [Complex.conj_ofReal]
  push_cast
  ring

theorem abs_double_lt' {b : ℝ} (hb : |b| < 1) : |2 * b / (1 + b ^ 2)| < 1 := by
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 1 + b ^ 2), div_lt_one (by positivity),
    abs_mul, abs_two]
  nlinarith [abs_nonneg b, sq_abs b]

/-- **For real `a`, `half a z = mob A (-z)` with `A = 2 a / (1 + a²)`.** -/
theorem half_real {a : ℝ} (ha : (a : ℂ) ∈ Dk) (z : Dk) :
    (half ⟨a, ha⟩ z : ℂ) = mob ((2 * a / (1 + a ^ 2) : ℝ) : ℂ) (-z) := by
  have ha1 : |a| < 1 := by
    have := mem_Dk.1 ha; rwa [Complex.norm_real, Real.norm_eq_abs] at this
  set A : ℝ := 2 * a / (1 + a ^ 2) with hA
  have hAD : (A : ℂ) ∈ Dk := ofReal_mem_Dk (abs_double_lt' ha1)
  set g := (rotH (-1) (by simp)).trans (mobH ⟨A, hAD⟩) with hg
  have hgz : ∀ w : Dk, (g w : ℂ) = mob A (-w) := by intro w; simp [hg]
  have hneg : ∀ w : ℂ, -mob A (-w) = mob (-A) w := by
    intro w; simp only [mob, map_neg, Complex.conj_ofReal]; ring
  suffices h : g = half ⟨a, ha⟩ by rw [← h, hgz]
  refine eq_half (g := g) (x := ⟨a, ha⟩)
    (show g ∈ holAut from holAut.mul_mem (mobH_mem _) (rotH_mem _ _)) ?_ ?_ ?_
  · apply Subtype.ext
    rw [hgz]
    change mob (A : ℂ) (-(a : ℂ)) = a
    have h1 : (1 : ℝ) - A * a ≠ 0 := by
      have := abs_lt.1 (abs_double_lt' ha1)
      have := abs_lt.1 ha1
      rw [hA]
      have hpos : (0 : ℝ) < 1 + a ^ 2 := by positivity
      rw [show (1 : ℝ) - 2 * a / (1 + a ^ 2) * a = (1 - a ^ 2) / (1 + a ^ 2) by field_simp; ring]
      exact div_ne_zero (by nlinarith) hpos.ne'
    have e : mob (A : ℂ) (-(a : ℂ)) = (((-a + A) / (1 - A * a) : ℝ) : ℂ) := by
      simp only [mob, Complex.conj_ofReal]
      push_cast
      ring_nf
    rw [e]
    congr 1
    rw [div_eq_iff h1, hA]
    field_simp
    ring
  · intro w
    apply Subtype.ext
    rw [hgz, hgz, hneg, mob_mob_neg hAD w.2]
  · intro h
    have h0 := congrArg (fun k : Dk ≃ₜ Dk => (k d0 : ℂ)) h
    simp only [hgz, coe_d0, neg_zero, mob_zero] at h0
    have hA0 : (A : ℂ) = 0 := h0
    have hh : ((1 / 2 : ℝ) : ℂ) ∈ Dk := ofReal_mem_Dk (by norm_num [abs_of_pos])
    have h2 := congrArg (fun k : Dk ≃ₜ Dk => (k ⟨_, hh⟩ : ℂ)) h
    simp only [hgz, hA0, mob, map_zero, zero_mul, add_zero, div_one] at h2
    change -(((1 / 2 : ℝ)) : ℂ) = ((1 / 2 : ℝ) : ℂ) at h2
    have := congrArg Complex.re h2
    norm_num at this

/-- **Doubling**: `qN (2 a / (1 + a²)) = 2 qN(a)² - 1` for real `a`, `|a| < 1`. -/
theorem qN_double {a : ℝ} (ha : |a| < 1) :
    qN ((2 * a / (1 + a ^ 2) : ℝ) : ℂ) = 2 * qN (a : ℂ) ^ 2 - 1 := by
  have ha2 : a ^ 2 < 1 := by rw [← sq_abs]; nlinarith [abs_nonneg a]
  have h1 : (1 : ℝ) - a ^ 2 ≠ 0 := by linarith
  have h2 : (0 : ℝ) < 1 + a ^ 2 := by positivity
  have h3 : (1 + a ^ 2) ^ 2 - (2 * a) ^ 2 = (1 - a ^ 2) ^ 2 := by ring
  have h4 : (1 + a ^ 2) ^ 2 - (2 * a) ^ 2 ≠ 0 := by rw [h3]; positivity
  simp only [qN, Complex.normSq_ofReal]
  have e1 : 1 - 2 * a / (1 + a ^ 2) * (2 * a / (1 + a ^ 2)) =
      ((1 + a ^ 2) ^ 2 - (2 * a) ^ 2) / (1 + a ^ 2) ^ 2 := by field_simp
  have e2 : 1 + 2 * a / (1 + a ^ 2) * (2 * a / (1 + a ^ 2)) =
      ((1 + a ^ 2) ^ 2 + (2 * a) ^ 2) / (1 + a ^ 2) ^ 2 := by field_simp
  rw [e1, e2, div_div_div_cancel_right₀ (by positivity), h3]
  have h1' : 1 - a * a ≠ 0 := by rw [← sq]; exact h1
  field_simp
  ring

/-- **Hyperbolic Pythagoras**: `qN (mob A (i y)) = qN A · qN (i y)` for real `A`, `y`. -/
theorem qN_mob_I {A y : ℝ} (hA : |A| < 1) (hy : |y| < 1) :
    qN (mob A (I * y)) = qN (A : ℂ) * qN (I * y) := by
  have hA2 : A ^ 2 < 1 := by rw [← sq_abs]; nlinarith [abs_nonneg A]
  have hy2 : y ^ 2 < 1 := by rw [← sq_abs]; nlinarith [abs_nonneg y]
  have hn1 : normSq (I * y + A) = A ^ 2 + y ^ 2 := by
    rw [Complex.normSq_apply]; simp; ring
  have hn2 : normSq (1 + conj (A : ℂ) * (I * y)) = 1 + A ^ 2 * y ^ 2 := by
    rw [Complex.normSq_apply, Complex.conj_ofReal]; simp; ring
  have hn3 : normSq (I * y) = y ^ 2 := by rw [Complex.normSq_apply]; simp; ring
  have hpos : (0 : ℝ) < 1 + A ^ 2 * y ^ 2 := by positivity
  simp only [qN, mob, Complex.normSq_div, hn1, hn2, hn3, Complex.normSq_ofReal]
  have e1 : 1 - (A ^ 2 + y ^ 2) / (1 + A ^ 2 * y ^ 2) =
      (1 - A ^ 2) * (1 - y ^ 2) / (1 + A ^ 2 * y ^ 2) := by field_simp; ring
  have e2 : 1 + (A ^ 2 + y ^ 2) / (1 + A ^ 2 * y ^ 2) =
      (1 + A ^ 2) * (1 + y ^ 2) / (1 + A ^ 2 * y ^ 2) := by field_simp; ring
  rw [e1, e2, div_div_div_cancel_right₀ hpos.ne']
  have h1 : 1 - A * A ≠ 0 := by nlinarith
  have h2 : 1 - y ^ 2 ≠ 0 := by linarith
  field_simp

/-- **Every point of the disc is `mob A (i y)` with `A`, `y` real**: the geodesic through `z`
perpendicular to the real diameter meets it (intermediate value theorem). -/
theorem exists_real_mob_imag (z : Dk) :
    ∃ A y : ℝ, |A| < 1 ∧ |y| < 1 ∧ (z : ℂ) = mob A (I * y) := by
  set x := (z : ℂ).re
  have hz := z.2
  have hnz : normSq (z : ℂ) < 1 := normSq_lt_one_of_mem hz
  have hxn : x ^ 2 ≤ normSq (z : ℂ) := by
    rw [Complex.normSq_apply]; nlinarith [sq_nonneg (z : ℂ).im]
  have hx1 : |x| < 1 := by
    rw [← sq_lt_one_iff_abs_lt_one]; linarith
  set g : ℝ → ℝ := fun A => x * (1 + A ^ 2) - A * (1 + normSq (z : ℂ)) with hg
  have hgc : ContinuousOn g (Icc (-1) 1) := by fun_prop
  have hg1 : g 1 < 0 := by
    simp only [hg]; nlinarith [abs_lt.1 hx1, sq_nonneg (1 - x)]
  have hgm1 : 0 < g (-1) := by
    simp only [hg]; nlinarith [abs_lt.1 hx1, sq_nonneg (1 + x)]
  obtain ⟨A, hA, hgA⟩ := intermediate_value_Ioo' (by norm_num : (-1 : ℝ) ≤ 1) hgc ⟨hg1, hgm1⟩
  have hA1 : |A| < 1 := abs_lt.2 hA
  set w := mob (-(A : ℂ)) z with hw
  have hwD : w ∈ Dk := mob_mem_ball (neg_mem_Dk (ofReal_mem_Dk hA1)) hz
  have hden : 1 - (A : ℂ) * z ≠ 0 := one_sub_mul_ne_zero hA1 hz
  have hwre : w.re = 0 := by
    rw [hw, mob, map_neg, Complex.conj_ofReal, Complex.div_re]
    have hq : normSq (1 + -(A : ℂ) * z) ≠ 0 := by
      rw [Ne, Complex.normSq_eq_zero, neg_mul, ← sub_eq_add_neg]; exact hden
    rw [← add_div, div_eq_zero_iff]
    left
    have : g A = 0 := hgA
    simp only [hg, Complex.normSq_apply] at this
    simp only [Complex.add_re, Complex.add_im, Complex.neg_re, Complex.neg_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im]
    linear_combination this
  have hwI : w = I * (w.im : ℂ) := by
    apply Complex.ext <;> simp [hwre]
  have hwim : |w.im| < 1 := by
    have h1 := Complex.abs_im_le_norm w
    exact h1.trans_lt (mem_Dk.1 hwD)
  refine ⟨A, w.im, hA1, hwim, ?_⟩
  rw [← hwI, hw, mob_mob_neg (ofReal_mem_Dk hA1) hz]

end Disc

end AutHol

end Iut
