/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Algebra.Group.Pointwise

/-!
# Connected open subsets of the circle ([FrdII], Definition 3.1(iii), Lemma 3.2)

The angular part of an angular region of `ℂ^×` ([FrdII], Definition 3.1(iii)) is a nonempty
connected open subset `B ⊆ S¹ = O_ℂ^×` (`IsAngular B`). This file proves the facts about such
subsets used by the archimedean Frobenioid of [FrdII], Example 3.3:

* `IsAngular.mul`, `IsAngular.pow`, `IsAngular.singleton_mul`: products `B₁·B₂`, powers
  `B^{⊗d} = B·…·B` and rotations `u·B` of angular parts are angular parts (this is the
  assertion "`A₁ ⊗_K A₂` is an angular region" of Definition 3.1(iii));
* `exists_isAngular_subset`: every open subset contains an angular part through any of its
  points (small arcs);
* `IsAngular.pow_eq_univ`: **[FrdII], Lemma 3.2(v)**, in the form used in Example 3.3(ii):
  `B^{⊗d} = S¹` for all sufficiently large `d`;
* `IsAngular.rigid`, `IsAngular.eq_of_subset`: **[FrdII], Lemma 3.2(iv)**, in the form used in
  Example 3.3(ii) (with a rotation `v`, as needed for endomorphisms of angular regions): if
  `v·z^d ∈ B` for all `z ∈ B` and `B ≠ S¹`, then `d = 1` and `v = 1`; consequently
  `{v}·B^{⊗d} ⊆ B` implies `{v}·B^{⊗d} = B`.

The proof of the rigidity statement follows the length argument of [FrdII]: relative to a point
`p ∉ B`, the argument `θ(z) = arg(−z/p)` is continuous on `B`, the map `z ↦ v·z^d` satisfies
`θ(v z^d) = d·θ(z) + k` on the connected set `B` (a continuous function with values in a coset of
`2πℤ` does not vary), and iterating multiplies differences of angles by `d^n` (resp. translates by
`n·k`), which is impossible inside the bounded range `[−π, π]` unless `d = 1`, `k = 0`.
-/

namespace Iut

namespace Frobenioid

namespace Angular

open Set Pointwise Real

/-- **Angular parts** ([FrdII], Definition 3.1(iii), `K = ℂ`): nonempty connected open subsets of
`S¹ = O_ℂ^×`. -/
def IsAngular (B : Set Circle) : Prop := IsOpen B ∧ IsPreconnected B ∧ B.Nonempty

lemma isAngular_univ : IsAngular (univ : Set Circle) :=
  ⟨isOpen_univ, isPreconnected_univ, univ_nonempty⟩

lemma isPreconnected_mul {B C : Set Circle} (hB : IsPreconnected B) (hC : IsPreconnected C) :
    IsPreconnected (B * C) := by
  rw [← image2_mul, ← image_prod]
  exact (hB.prod hC).image _ continuous_mul.continuousOn

lemma IsAngular.mul {B C : Set Circle} (hB : IsAngular B) (hC : IsAngular C) :
    IsAngular (B * C) :=
  ⟨hC.1.mul_left, isPreconnected_mul hB.2.1 hC.2.1, hB.2.2.mul hC.2.2⟩

lemma IsAngular.pow {B : Set Circle} (hB : IsAngular B) : ∀ {n : ℕ}, n ≠ 0 → IsAngular (B ^ n)
  | 1, _ => by simpa using hB
  | n + 2, _ => by
    rw [pow_succ]
    exact (hB.pow n.succ_ne_zero).mul hB

lemma IsAngular.singleton_mul (u : Circle) {B : Set Circle} (hB : IsAngular B) :
    IsAngular ({u} * B) :=
  ⟨hB.1.mul_left, isPreconnected_mul isPreconnected_singleton hB.2.1,
    (singleton_nonempty u).mul hB.2.2⟩

lemma singleton_mul_univ (u : Circle) : ({u} : Set Circle) * univ = univ :=
  eq_univ_of_forall fun y => mem_mul.mpr ⟨u, rfl, u⁻¹ * y, trivial, by group⟩

lemma singleton_mul_univ_pow (u : Circle) {d : ℕ} (hd : d ≠ 0) :
    ({u} : Set Circle) * univ ^ d = univ := by
  rw [univ_pow hd, singleton_mul_univ]

lemma isAngular_centeredArc {r : ℝ} (hr : 0 < r) : IsAngular (Circle.centeredArc r) := by
  have hI : {x : ℝ | |x| < r} = Ioo (-r) r := by ext; simp [abs_lt]
  refine ⟨Circle.isCoveringMap_exp.isOpenMap _ ?_, ?_, ⟨1, 0, by simpa using hr, ?_⟩⟩
  · rw [hI]; exact isOpen_Ioo
  · rw [Circle.centeredArc, hI]
    exact isPreconnected_Ioo.image _ Circle.exp.continuous.continuousOn
  · exact Circle.exp_zero

/-- Small arcs: every open `W ∋ z` contains an arc `z·exp(i(−r, r))`, `0 < r ≤ π`. -/
lemma exists_arc_subset {W : Set Circle} (hW : IsOpen W) {z : Circle} (hz : z ∈ W) :
    ∃ r : ℝ, 0 < r ∧ r ≤ π ∧ {z} * Circle.centeredArc r ⊆ W := by
  have h : (z * ·) ⁻¹' W ∈ nhds (1 : Circle) :=
    (continuous_const_mul z).continuousAt.preimage_mem_nhds (by simpa using hW.mem_nhds hz)
  obtain ⟨n, -, hn⟩ := Circle.hasBasis_centeredArc_div_two_pow.mem_iff.mp h
  refine ⟨π / 2 ^ (n + 1), by positivity, div_le_self pi_pos.le (one_le_pow₀ (by norm_num)), ?_⟩
  rintro _ ⟨_, rfl, a, ha, rfl⟩
  exact hn ha

/-- Every open subset contains an angular part through any of its points. -/
lemma exists_isAngular_subset {W : Set Circle} (hW : IsOpen W) {z : Circle} (hz : z ∈ W) :
    ∃ B, IsAngular B ∧ B ⊆ W ∧ z ∈ B := by
  obtain ⟨r, hr, -, h⟩ := exists_arc_subset hW hz
  exact ⟨_, (isAngular_centeredArc hr).singleton_mul z, h,
    ⟨z, rfl, 1, ⟨0, by simpa using hr, Circle.exp_zero⟩, mul_one z⟩⟩

/-- An angular part has a second point (`S¹` has no isolated points). -/
lemma IsAngular.exists_ne {B : Set Circle} (hB : IsAngular B) {z : Circle} (hz : z ∈ B) :
    ∃ z' ∈ B, z' ≠ z := by
  obtain ⟨r, hr, hrπ, h⟩ := exists_arc_subset hB.1 hz
  have hr2 : |r / 2| < r := by rw [abs_of_pos (by positivity)]; linarith
  refine ⟨z * Circle.exp (r / 2), h (mul_mem_mul rfl ⟨r / 2, hr2, rfl⟩), fun he => ?_⟩
  have h1 : Circle.exp (r / 2) = 1 := by simpa using he
  obtain ⟨m, hm⟩ := Circle.exp_eq_one.mp h1
  have h0 : (0 : ℝ) < m := by
    by_contra hc
    push Not at hc
    nlinarith [pi_pos]
  have h1' : (m : ℝ) < 1 := by nlinarith [pi_pos]
  have : (0 : ℤ) < m := by exact_mod_cast h0
  have : m < (1 : ℤ) := by exact_mod_cast h1'
  omega

/-- **[FrdII], Lemma 3.2(v)** (as used in Example 3.3(ii)): `B^{⊗d} = S¹` for `d ≫ 0`. -/
theorem IsAngular.pow_eq_univ {B : Set Circle} (hB : IsAngular B) :
    ∃ N : ℕ, ∀ d, N ≤ d → B ^ d = univ := by
  obtain ⟨z, hz⟩ := hB.2.2
  obtain ⟨r, hr, -, h⟩ := exists_arc_subset hB.1 hz
  obtain ⟨N, hN⟩ := exists_nat_gt (π / r)
  refine ⟨N, fun d hd => eq_univ_of_forall fun y => ?_⟩
  have hdr : π < d * r := by
    have := (div_lt_iff₀ hr).mp hN
    have : (N : ℝ) ≤ d := by exact_mod_cast hd
    nlinarith
  have hd0 : (0 : ℝ) < d := by
    by_contra hc
    push Not at hc
    nlinarith [pi_pos]
  set x := Complex.arg ((y * (z ^ d)⁻¹ : Circle) : ℂ)
  have hx : |x| ≤ π := Complex.abs_arg_le_pi _
  have hmem : z * Circle.exp (x / d) ∈ B := by
    refine h (mul_mem_mul rfl ⟨x / d, ?_, rfl⟩)
    change |x / d| < r
    rw [abs_div, abs_of_pos hd0, div_lt_iff₀ hd0]
    linarith
  have : (z * Circle.exp (x / d)) ^ d = y := by
    rw [mul_pow, ← Circle.exp_natCast_mul, mul_div_cancel₀ _ hd0.ne', Circle.exp_arg, mul_comm y,
      mul_inv_cancel_left]
  rw [← this]
  exact pow_mem_pow hmem

/-! ### Rigidity ([FrdII], Lemma 3.2(iv)) -/

/-- A continuous function on a preconnected set whose values have a common image under
`Circle.exp` takes a single value. -/
lemma eq_of_exp_eq {S : Set Circle} (hS : IsPreconnected S) {F : Circle → ℝ}
    (hF : ContinuousOn F S) (h : ∀ x ∈ S, ∀ y ∈ S, Circle.exp (F x) = Circle.exp (F y))
    {x y : Circle} (hx : x ∈ S) (hy : y ∈ S) : F x = F y := by
  by_contra hne
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp (h x hx y hy)
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hne (by simpa using hm)
  have hoc : (F '' S).OrdConnected := (hS.image F hF).ordConnected
  have hsub := hoc.uIcc_subset (mem_image_of_mem F hy) (mem_image_of_mem F hx)
  -- the point `F y ± π` lies between `F y` and `F x`, and is not in `F y + 2πℤ`
  have key : ∀ e : ℝ, (e = 1 ∨ e = -1) → F y + e * π ∈ uIcc (F y) (F x) → False := by
    intro e he hc
    obtain ⟨w, hw, hwc⟩ := hsub hc
    obtain ⟨k, hk⟩ := Circle.exp_eq_exp.mp (h w hw y hy)
    rw [hwc] at hk
    have h2 : (2 * k - e) * π = 0 := by linarith
    rcases mul_eq_zero.mp h2 with h0 | h0
    · rcases he with rfl | rfl
      · have : (2 * k - 1 : ℤ) = 0 := by exact_mod_cast h0
        omega
      · have h1 : ((2 * k + 1 : ℤ) : ℝ) = 0 := by push_cast; linarith
        have : (2 * k + 1 : ℤ) = 0 := by exact_mod_cast h1
        omega
    · exact pi_ne_zero h0
  rcases lt_or_gt_of_ne hm0 with hneg | hpos
  · have : (m : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hneg
    refine key (-1) (Or.inr rfl) (mem_uIcc.mpr (Or.inr ⟨?_, ?_⟩)) <;>
      nlinarith [pi_pos, hm]
  · have : (1 : ℝ) ≤ m := by exact_mod_cast hpos
    refine key 1 (Or.inl rfl) (mem_uIcc.mpr (Or.inl ⟨?_, ?_⟩)) <;>
      nlinarith [pi_pos, hm]

/-- The argument relative to a cut: `cutArg q z = arg(z·q) ∈ (−π, π]`. -/
noncomputable def cutArg (q z : Circle) : ℝ := Complex.arg ((z * q : Circle) : ℂ)

lemma exp_cutArg (q z : Circle) : Circle.exp (cutArg q z) = z * q := Circle.exp_arg _

lemma abs_cutArg_le (q z : Circle) : |cutArg q z| ≤ π := Complex.abs_arg_le_pi _

lemma cutArg_injective (q : Circle) : Function.Injective (cutArg q) := fun z w hzw => by
  have := congrArg Circle.exp hzw
  rw [exp_cutArg, exp_cutArg] at this
  exact mul_right_cancel this

lemma continuousAt_cutArg {q z : Circle} (hz : z * q ≠ -1) : ContinuousAt (cutArg q) z := by
  have hsl : (((z * q : Circle)) : ℂ) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff_arg]
    refine ⟨fun hπ => hz ?_, Circle.coe_ne_zero _⟩
    have h1 : Complex.arg ((z * q : Circle) : ℂ) = Complex.arg ((-1 : Circle) : ℂ) := by
      rw [hπ, Circle.coe_neg, Circle.coe_one, Complex.arg_neg_one]
    exact Circle.arg_eq_arg.mp h1
  have hc : Continuous fun y : Circle => ((y * q : Circle) : ℂ) :=
    continuous_subtype_val.comp (continuous_mul_const q)
  exact ContinuousAt.comp (g := Complex.arg) (Complex.continuousAt_arg hsl) hc.continuousAt

/-- The map `z ↦ v·z^d`. -/
noncomputable def rotPow (v : Circle) (d : ℕ) (z : Circle) : Circle := v * z ^ d

lemma continuous_rotPow (v : Circle) (d : ℕ) : Continuous (rotPow v d) :=
  continuous_const.mul (continuous_pow d)

/-- `F(z) = θ(v z^d) − d·θ(z)` for the cut argument `θ`. -/
noncomputable def defect (q v : Circle) (d : ℕ) (z : Circle) : ℝ :=
  cutArg q (rotPow v d z) - d * cutArg q z

lemma exp_defect (q v : Circle) (d : ℕ) (z : Circle) :
    Circle.exp (defect q v d z) * q ^ d = v * q := by
  have e : Circle.exp (defect q v d z) * (z * q) ^ d = v * z ^ d * q := by
    simp only [defect, Circle.exp_sub, Circle.exp_natCast_mul, exp_cutArg, rotPow]
    rw [div_mul_cancel]
  have e' : z ^ d * (Circle.exp (defect q v d z) * q ^ d) = z ^ d * (v * q) := by
    calc z ^ d * (Circle.exp (defect q v d z) * q ^ d)
        = Circle.exp (defect q v d z) * (z * q) ^ d := by rw [mul_pow]; ac_rfl
      _ = v * z ^ d * q := e
      _ = z ^ d * (v * q) := by ac_rfl
  exact mul_left_cancel e'

/-- **[FrdII], Lemma 3.2(iv)** (with a rotation, as used in Example 3.3(ii)): if `B ≠ S¹` is an
angular part and `v·z^d ∈ B` for all `z ∈ B`, then `d = 1` and `v = 1`. -/
theorem IsAngular.rigid {B : Set Circle} (hB : IsAngular B) (hne : B ≠ univ) {v : Circle}
    {d : ℕ} (hd : d ≠ 0) (h : ∀ z ∈ B, v * z ^ d ∈ B) : d = 1 ∧ v = 1 := by
  obtain ⟨p, hp⟩ := (ne_univ_iff_exists_notMem B).mp hne
  have hcut : ∀ z ∈ B, z * -p⁻¹ ≠ -1 := fun z hz he => by
    have h1 : -(z * p⁻¹) = -1 := by rw [← mul_neg]; exact he
    have : z * p⁻¹ = 1 := neg_inj.mp h1
    rw [mul_inv_eq_one.mp this] at hz
    exact hp hz
  set q : Circle := -p⁻¹
  have hθbd := abs_cutArg_le q
  have hFcont : ContinuousOn (defect q v d) B := fun z hz =>
    ContinuousAt.continuousWithinAt (ContinuousAt.sub
      ((continuousAt_cutArg (z := rotPow v d z) (hcut _ (h z hz))).comp
        (continuous_rotPow v d).continuousAt)
      (continuousAt_const.mul (continuousAt_cutArg (hcut z hz))))
  obtain ⟨z₀, hz₀⟩ := hB.2.2
  have hF : ∀ z ∈ B, defect q v d z = defect q v d z₀ := fun z hz =>
    eq_of_exp_eq hB.2.1 hFcont
      (fun x _ y _ => mul_right_cancel ((exp_defect q v d x).trans (exp_defect q v d y).symm))
      hz hz₀
  set k := defect q v d z₀
  have hT : ∀ z ∈ B, cutArg q (rotPow v d z) = d * cutArg q z + k := fun z hz => by
    have := hF z hz
    simp only [defect] at this
    linarith
  have hTB : ∀ n, ∀ z ∈ B, (rotPow v d)^[n] z ∈ B := fun n => by
    induction n with
    | zero => exact fun z hz => hz
    | succ n ih =>
      intro z hz
      rw [Function.iterate_succ_apply']
      exact h _ (ih z hz)
  -- the Frobenius degree is `1`
  have hd1 : d = 1 := by
    by_contra hd1
    have hd2 : 2 ≤ d := by omega
    obtain ⟨z₁, hz₁, hne₁⟩ := hB.exists_ne hz₀
    set δ := cutArg q z₁ - cutArg q z₀
    have hδ : δ ≠ 0 := fun h0 => hne₁ (cutArg_injective q (by simp only [δ] at h0; linarith))
    have hdiff : ∀ n : ℕ, cutArg q ((rotPow v d)^[n] z₁) - cutArg q ((rotPow v d)^[n] z₀) =
        (d : ℝ) ^ n * δ := fun n => by
      induction n with
      | zero => simp [δ]
      | succ n ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
          hT _ (hTB n z₁ hz₁), hT _ (hTB n z₀ hz₀), pow_succ]
        linear_combination (d : ℝ) * ih
    obtain ⟨n, hn⟩ := exists_nat_gt (2 * π / |δ|)
    have hδpos : 0 < |δ| := abs_pos.mpr hδ
    have h1 : (n : ℝ) * |δ| > 2 * π := by rwa [div_lt_iff₀ hδpos] at hn
    have h2 : (n : ℝ) ≤ (d : ℝ) ^ n := by
      have : n < 2 ^ n := Nat.lt_two_pow_self
      have : 2 ^ n ≤ d ^ n := Nat.pow_le_pow_left hd2 n
      exact_mod_cast (by omega : n ≤ d ^ n)
    have h3 : |cutArg q ((rotPow v d)^[n] z₁) - cutArg q ((rotPow v d)^[n] z₀)| ≤ 2 * π := by
      have := hθbd ((rotPow v d)^[n] z₁); have := hθbd ((rotPow v d)^[n] z₀)
      rw [abs_le] at *; constructor <;> linarith
    rw [hdiff, abs_mul, abs_of_nonneg (by positivity)] at h3
    nlinarith
  subst hd1
  -- the rotation is trivial
  have hiter : ∀ n : ℕ, cutArg q ((rotPow v 1)^[n] z₀) = cutArg q z₀ + n * k := fun n => by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply', hT _ (hTB n z₀ hz₀), ih]
      push_cast; ring
  have hk : k = 0 := by
    by_contra hk
    obtain ⟨n, hn⟩ := exists_nat_gt (2 * π / |k|)
    have hkpos : 0 < |k| := abs_pos.mpr hk
    have h1 : (n : ℝ) * |k| > 2 * π := by rwa [div_lt_iff₀ hkpos] at hn
    have h3 : |(n : ℝ) * k| ≤ 2 * π := by
      have h4 := hθbd ((rotPow v 1)^[n] z₀); have h5 := hθbd z₀
      rw [hiter] at h4
      rw [abs_le] at *; constructor <;> linarith
    rw [abs_mul, Nat.abs_cast] at h3
    linarith
  refine ⟨rfl, ?_⟩
  have e : cutArg q (rotPow v 1 z₀) = cutArg q z₀ := by rw [hT z₀ hz₀, hk]; simp
  have := cutArg_injective q e
  simpa [rotPow] using this

/-- Consequence of `IsAngular.rigid`: `{v}·B^{⊗d} ⊆ B` forces `{v}·B^{⊗d} = B`, and, for
`B ≠ S¹`, `d = 1` and `v = 1`. -/
theorem IsAngular.eq_of_subset {B : Set Circle} (hB : IsAngular B) {v : Circle} {d : ℕ}
    (hd : d ≠ 0) (h : {v} * B ^ d ⊆ B) :
    {v} * B ^ d = B ∧ (B ≠ univ → d = 1 ∧ v = 1) := by
  by_cases hu : B = univ
  · subst hu
    exact ⟨singleton_mul_univ_pow v hd, fun h => (h rfl).elim⟩
  · obtain ⟨rfl, rfl⟩ := hB.rigid hu hd fun z hz => h (mul_mem_mul rfl (pow_mem_pow hz))
    exact ⟨by simp, fun _ => ⟨rfl, rfl⟩⟩

end Angular

end Frobenioid

end Iut
