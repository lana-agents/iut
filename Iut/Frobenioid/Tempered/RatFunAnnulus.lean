/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.Tempered.RatFunOrd

/-!
# Laurent series on closed annuli and division in `E(K)` (MR18 T8, route B-an)

[EtTh] Proposition 3.2(ii),(iii) and Proposition 3.4(ii) concern *meromorphic* functions on the
universal combinatorial covering `Z_∞`; on `𝔾_m^an` these are quotients `g/h` of entire Laurent
series (`RatFunEntire.lean`), and the statements need the **cancellation of the (in general
infinitely many) common zeros** of `g` and `h`: if `ord_α h ≤ ord_α g` at every point `α`, then
`h ∣ g` in `E(K)` (`Entire.dvd_of_ord_le`, over an algebraically closed `K`).

The proof is local on closed annuli `A = {r₁ ≤ |U| ≤ r₂}`. A Laurent series on `A` is a coefficient
family converging at both boundary radii (`ConvAt c r₁ ∧ ConvAt c r₂`, `RatFunGauss.lean`; it then
converges on all of `A`, `ConvAt.of_le_of_le`). The Gauss norm theory of `RatFunGauss.lean` holds
for such families at every radius of `A`.

1. **Local factorisation** `h = P·h'`: dividing `h` by `U - α` for its zeros `α ∈ A`
   (`exists_eq_lin_mul`) lowers the measure `hi_{r₂} h - lo_{r₁} h` by one; when it reaches `0`,
   `h'` has a single dominant index on `A` (here the Newton polygon zero existence of
   `RatFunZero.lean` is used, via `lo_const_of_no_zero`).
2. **Inversion on `A`**: if `h'` has a single dominant index `k` at both boundary radii, then
   `h' = a·Uᵏ·(1 - e)` with `|e|_{r₁}, |e|_{r₂} < 1`, and `∑ⱼ G·eʲ` converges on `A`; its
   coefficient family `S` satisfies `S · h' = g'` (`exists_conv_eq_of_dom`). The powers `eʲ` are
   taken in the ring `E(K)`, so only one interchange of summations is needed (`conv_tsum`).
3. The local quotients on the annuli `‖v‖⁻¹ ≤ |U| ≤ ‖v‖` agree (the Gauss lemma on the unit
   circle), so they define one entire series `u` with `u·h = g`.

## Main results

* `ConvAt.conv_add_right`, `conv_shiftF_right`, `conv_smul_right`, `conv_comm`,
  `conv_polyCoeff_lin`: convolution identities for families on an annulus.
* `exists_conv_eq_of_dom`: inversion of a series with one dominant index on an annulus.
* `exists_conv_eq_on_annulus`: the local quotient `g/h` on a closed annulus.
* `Entire.dvd_of_ord_le`: **`ord h ≤ ord g` everywhere ⇒ `h ∣ g` in `E(K)`**.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace Iut.Frobenioid.BAn

open Polynomial TateCurvesTheta Filter Topology

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]

/-! ### Convolution identities -/

/-- The shift `(shiftF k c) n = c (n - k)`: the coefficients of `Uᵏ · ∑ cₙ Uⁿ`. -/
def shiftF (k : ℤ) (c : ℤ → K) (n : ℤ) : K := c (n - k)

lemma shiftF_shiftF (j k : ℤ) (c : ℤ → K) : shiftF j (shiftF k c) = shiftF (j + k) c := by
  funext n; simp only [shiftF]; congr 1; ring

lemma shiftF_zero (c : ℤ → K) : shiftF 0 c = c := by funext n; simp [shiftF]

lemma shiftF_injective (k : ℤ) : Function.Injective (shiftF (K := K) k) := fun c d h => by
  have := congrArg (shiftF (-k)) h
  rwa [shiftF_shiftF, neg_add_cancel, shiftF_zero, shiftF_shiftF, neg_add_cancel,
    shiftF_zero] at this

lemma shiftF_smul (k : ℤ) (a : K) (c : ℤ → K) : shiftF k (a • c) = a • shiftF k c := rfl

lemma Entire.coeff_mono_mul_eq (k : ℤ) (f : Entire K) :
    Entire.coeff (Entire.mono k * f) = shiftF k (Entire.coeff f) :=
  funext fun l => Entire.coeff_mono_mul k f l

lemma conv_comm (c d : ℤ → K) : conv c d = conv d c := by
  funext l
  have := (Equiv.subLeft l).tsum_eq (fun m => c (l - m) * d m)
  rw [conv, conv, ← this]
  congr 1; funext m
  simp only [Equiv.subLeft_apply, sub_sub_cancel]; ring

lemma conv_shiftF_right (c d : ℤ → K) (k : ℤ) : conv c (shiftF k d) = shiftF k (conv c d) := by
  funext l
  have := (Equiv.addRight k).tsum_eq (fun m => c (l - m) * d (m - k))
  simp only [shiftF, conv]
  rw [← this]
  congr 1; funext m
  simp only [Equiv.coe_addRight, add_sub_cancel_right]
  congr 2; ring

lemma conv_smul_right (c d : ℤ → K) (a : K) : conv c (a • d) = a • conv c d := by
  funext l
  simp only [conv, Pi.smul_apply, smul_eq_mul]
  rw [← tsum_mul_left]; congr 1; funext m; ring

lemma conv_single_zero (c : ℤ → K) : conv c (Pi.single 0 1) = c := by
  funext l
  rw [conv, tsum_eq_single 0 fun m hm => by simp [hm]]
  simp

lemma ConvAt.conv_add_right {c d e : ℤ → K} {r : ℝ} (hc : ConvAt c r) (hd : ConvAt d r)
    (he : ConvAt e r) (hr : 0 < r) : BAn.conv c (d + e) = BAn.conv c d + BAn.conv c e := by
  funext l
  simp only [BAn.conv, Pi.add_apply, mul_add]
  exact ((hc.summable_conv_family hd hr l).hasSum.add
    (hc.summable_conv_family he hr l).hasSum).tsum_eq

lemma ConvAt.neg {c : ℤ → K} {r : ℝ} (hc : ConvAt c r) : ConvAt (-c) r := by
  refine hc.congr fun n => ?_
  simp [tnorm]

lemma ConvAt.smul {c : ℤ → K} {r : ℝ} (hc : ConvAt c r) (a : K) : ConvAt (a • c) r := by
  have h := hc.const_mul ‖a‖
  rw [mul_zero] at h
  refine h.congr fun n => ?_
  simp [tnorm, norm_mul, mul_assoc]

lemma ConvAt.add {c d : ℤ → K} {r : ℝ} (hc : ConvAt c r) (hd : ConvAt d r) (hr : 0 < r) :
    ConvAt (c + d) r := by
  have h := Filter.Tendsto.add hc hd
  rw [add_zero] at h
  refine squeeze_zero (fun n => tnorm_nonneg _ hr n) (fun n => ?_) h
  simp only [tnorm, Pi.add_apply]
  have := norm_add_le (c n) (d n)
  nlinarith [zpow_pos hr n]

lemma ConvAt.sub {c d : ℤ → K} {r : ℝ} (hc : ConvAt c r) (hd : ConvAt d r) (hr : 0 < r) :
    ConvAt (c - d) r := by
  simpa [sub_eq_add_neg] using hc.add hd.neg hr

lemma ConvAt.conv_sub_right {c d e : ℤ → K} {r : ℝ} (hc : ConvAt c r) (hd : ConvAt d r)
    (he : ConvAt e r) (hr : 0 < r) : BAn.conv c (d - e) = BAn.conv c d - BAn.conv c e := by
  have h := hc.conv_add_right hd he.neg hr
  rw [← sub_eq_add_neg] at h
  rw [h, show -e = (-1 : K) • e by simp, conv_smul_right]
  simp [sub_eq_add_neg]

lemma polyCoeff_lin (α : K) (m : ℤ) :
    polyCoeff (lin α) m = if m = 0 then -α else if m = 1 then 1 else 0 := by
  rcases lt_or_ge m 0 with hm | hm
  · rw [polyCoeff_of_neg _ hm, if_neg (by omega), if_neg (by omega)]
  · obtain ⟨i, rfl⟩ := Int.eq_ofNat_of_zero_le hm
    rw [polyCoeff_natCast]
    rcases i with _ | _ | i
    · simp
    · simp
    · rw [if_neg (by omega), if_neg (by omega)]
      simp [coeff_X]

/-- Multiplication by `U - α` on coefficients. -/
lemma conv_polyCoeff_lin (c : ℤ → K) (α : K) :
    conv c (polyCoeff (lin α)) = shiftF 1 c - α • c := by
  funext l
  rw [conv, tsum_eq_sum (s := {0, 1}) fun m hm => by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hm
    rw [polyCoeff_lin, if_neg hm.1, if_neg hm.2, mul_zero]]
  rw [Finset.sum_pair zero_ne_one]
  simp [polyCoeff_lin, shiftF]
  ring

lemma ConvAt.shiftF {c : ℤ → K} {r : ℝ} (hc : ConvAt c r) (hr : 0 < r) (k : ℤ) :
    ConvAt (BAn.shiftF k c) r := by
  have h := (hc.comp (Function.Injective.tendsto_cofinite
    (sub_left_injective (b := k)))).mul_const (r ^ k)
  rw [zero_mul] at h
  refine h.congr fun n => ?_
  simp only [Function.comp, tnorm, BAn.shiftF]
  rw [mul_assoc, ← zpow_add₀ hr.ne', sub_add_cancel]

lemma ConvAt.of_isEntire_coeff (f : Entire K) {r : ℝ} (hr : 0 < r) : ConvAt (Entire.coeff f) r :=
  (Entire.isEntire_coeff f).convAt hr

/-- `U - α` times `g`, on coefficients. -/
lemma coeff_lin_mul (α : K) (g : Entire K) :
    Entire.coeff (polyE (lin α) * g) = shiftF 1 (Entire.coeff g) - α • Entire.coeff g := by
  rw [Entire.coeff_mul, coeff_polyE, conv_comm, conv_polyCoeff_lin]

/-- A family that converges at every radius is entire. -/
lemma isEntire_of_convAt {c : ℤ → K} (h : ∀ r : ℝ, 0 < r → ConvAt c r) : IsEntire c := by
  intro u
  refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine (h _ (norm_pos_iff.mpr u.ne_zero)).congr fun n => ?_
  rw [tnorm, norm_mul, norm_zpow]

/-- A nonnegative function that is eventually `≤ ε` for every `ε > 0` tends to `0`. -/
lemma tendsto_zero_of_eventually_le {ι : Type*} {l : Filter ι} {f : ι → ℝ} (h0 : ∀ i, 0 ≤ f i)
    (h : ∀ ε > 0, ∀ᶠ i in l, f i ≤ ε) : Tendsto f l (𝓝 0) := by
  refine tendsto_order.2 ⟨fun a ha => Eventually.of_forall fun i => ha.trans_le (h0 i),
    fun a ha => ?_⟩
  exact (h (a / 2) (half_pos ha)).mono fun i hi => hi.trans_lt (half_lt_self ha)

/-! ### Geometric series of families -/

section Geom

variable {A : ℕ → ℤ → K} {r C θ : ℝ}

lemma norm_le_of_tnorm_le {c : ℤ → K} (hr : 0 < r) {n : ℤ} {B : ℝ} (h : tnorm c r n ≤ B) :
    ‖c n‖ ≤ B / r ^ n := by
  rw [le_div_iff₀ (zpow_pos hr n)]; exact h

lemma summable_of_geom (hr : 0 < r) (hθ0 : 0 ≤ θ) (hθ : θ < 1)
    (hA : ∀ j n, tnorm (A j) r n ≤ C * θ ^ j) (n : ℤ) : Summable fun j => A j n := by
  refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_
  rw [tendsto_zero_iff_norm_tendsto_zero, Nat.cofinite_eq_atTop]
  have hlim : Tendsto (fun j : ℕ => C * θ ^ j / r ^ n) atTop (𝓝 0) := by
    have h := ((tendsto_pow_atTop_nhds_zero_of_lt_one hθ0 hθ).const_mul C).div_const (r ^ n)
    rwa [mul_zero, zero_div] at h
  exact squeeze_zero (fun j => norm_nonneg _) (fun j => norm_le_of_tnorm_le hr (hA j n)) hlim

lemma exists_geom_lt (hθ0 : 0 ≤ θ) (hθ : θ < 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ J : ℕ, C * θ ^ J < ε := by
  have h := ((tendsto_pow_atTop_nhds_zero_of_lt_one hθ0 hθ).const_mul C)
  rw [mul_zero] at h
  exact (h.eventually (gt_mem_nhds hε)).exists

/-- The sum of families with geometrically decaying term norms converges at `r`. -/
lemma convAt_tsum (hr : 0 < r) (hθ0 : 0 ≤ θ) (hθ : θ < 1)
    (hA : ∀ j n, tnorm (A j) r n ≤ C * θ ^ j) (hconv : ∀ j, ConvAt (A j) r) :
    ConvAt (fun n => ∑' j, A j n) r := by
  refine tendsto_zero_of_eventually_le (fun n => tnorm_nonneg _ hr n) fun ε hε => ?_
  obtain ⟨J, hJ⟩ := exists_geom_lt (C := C) hθ0 hθ hε
  have hev : ∀ᶠ n in cofinite, ∀ j ∈ Finset.range J, tnorm (A j) r n < ε :=
    (Filter.eventually_all_finset _).mpr fun j _ => (hconv j).eventually (gt_mem_nhds hε)
  refine hev.mono fun n hn => ?_
  have hrn := zpow_pos hr n
  have hb : ‖∑' j, A j n‖ ≤ ε / r ^ n := by
    refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (div_nonneg hε.le hrn.le)
      fun j => norm_le_of_tnorm_le hr ?_
    by_cases hj : j < J
    · exact (hn j (Finset.mem_range.mpr hj)).le
    · refine (hA j n).trans (le_trans ?_ hJ.le)
      have hC : 0 ≤ C := by
        have := (tnorm_nonneg (A 0) hr 0).trans (hA 0 0); simpa using this
      exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hθ0 hθ.le (not_lt.mp hj)) hC
  rw [tnorm]
  exact (le_div_iff₀ hrn).mp hb

/-- **Interchange of a geometric sum with a convolution.** -/
lemma conv_tsum (hr : 0 < r) (hθ0 : 0 ≤ θ) (hθ : θ < 1)
    (hA : ∀ j n, tnorm (A j) r n ≤ C * θ ^ j) (hconv : ∀ j, ConvAt (A j) r) {b : ℤ → K}
    (hb : ConvAt b r) (l : ℤ) :
    conv (fun n => ∑' j, A j n) b l = ∑' j, conv (A j) b l := by
  set F : ℕ → ℤ → K := fun j m => A j (l - m) * b m
  have hC : 0 ≤ C := by
    have := (tnorm_nonneg (A 0) hr 0).trans (hA 0 0); simpa using this
  obtain ⟨B, hB⟩ := hb.bddAbove
  have hbB : ∀ m, tnorm b r m ≤ B := fun m => hB ⟨m, rfl⟩
  have hB0 : 0 ≤ B := (tnorm_nonneg b hr 0).trans (hbB 0)
  have hrl := zpow_pos hr l
  have hnF : ∀ j m, ‖F j m‖ = tnorm (A j) r (l - m) * tnorm b r m / r ^ l := fun j m => by
    rw [tnorm_mul_tnorm r hr, mul_div_cancel_right₀ _ hrl.ne']
  -- summability of the double family
  have hsum : Summable (Function.uncurry F) := by
    refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine tendsto_zero_of_eventually_le (fun _ => norm_nonneg _) fun ε hε => ?_
    obtain ⟨J, hJ⟩ := exists_geom_lt (C := C * (B + 1)) hθ0 hθ (mul_pos hε hrl)
    have hfin : ∀ j, {m | ¬ tnorm (A j) r (l - m) * tnorm b r m < ε * r ^ l}.Finite := fun j =>
      Filter.eventually_cofinite.mp (((hconv j).tendsto_conv_family hb hr l).eventually
        (gt_mem_nhds (mul_pos hε hrl)))
    have hfin' : {p : ℕ × ℤ | ¬ ‖Function.uncurry F p‖ ≤ ε}.Finite := by
      refine (Set.Finite.biUnion (Finset.range J).finite_toSet fun j _ =>
        (hfin j).image fun m => (j, m)).subset fun p hp => ?_
      have hp' : ε * r ^ l < tnorm (A p.1) r (l - p.2) * tnorm b r p.2 := by
        have : ε < ‖F p.1 p.2‖ := not_le.mp hp
        rwa [hnF, lt_div_iff₀ hrl] at this
      have hj : p.1 < J := by
        by_contra hj
        push Not at hj
        have h1 : tnorm (A p.1) r (l - p.2) * tnorm b r p.2 ≤ C * θ ^ p.1 * (B + 1) :=
          mul_le_mul (hA _ _) ((hbB _).trans (by linarith)) (tnorm_nonneg b hr _)
            (mul_nonneg hC (pow_nonneg hθ0 _))
        have h2 : C * θ ^ p.1 * (B + 1) ≤ C * (B + 1) * θ ^ J := by
          rw [mul_right_comm]
          exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hθ0 hθ.le hj)
            (mul_nonneg hC (by linarith))
        linarith
      exact Set.mem_biUnion (Finset.mem_coe.mpr (Finset.mem_range.mpr hj))
        ⟨p.2, not_lt.mpr hp'.le, rfl⟩
    exact Filter.eventually_cofinite.mpr hfin'
  have h₁ : ∀ j, Summable (F j) := fun j => (hconv j).summable_conv_family hb hr l
  have h₂ : ∀ m, Summable fun j => F j m := fun m =>
    ((summable_of_geom hr hθ0 hθ hA (l - m)).mul_right (b m))
  calc conv (fun n => ∑' j, A j n) b l = ∑' m, ∑' j, F j m := by
        rw [conv]; congr 1; funext m; exact tsum_mul_right.symm
    _ = ∑' j, ∑' m, F j m := hsum.tsum_comm' h₁ h₂
    _ = ∑' j, conv (A j) b l := rfl

end Geom

/-! ### Inversion on an annulus -/

lemma Entire.gn_pow (e : Entire K) {r : ℝ} (hr : 0 < r) (j : ℕ) :
    Entire.gn (e ^ j) r = Entire.gn e r ^ j := by
  induction j with
  | zero =>
    rw [pow_zero, pow_zero, ← map_one (algebraMap K (Entire K)), Entire.gn_algebraMap 1 hr,
      norm_one]
  | succ j ih => rw [pow_succ, Entire.gn_mul _ _ hr, ih, pow_succ]

/-- **Inversion on an annulus.** If `k` is the unique dominant index of `h ∈ E(K)` at the radii
`r₁ ≤ r₂`, then for every `g ∈ E(K)` there is a Laurent series `S` on the annulus
`r₁ ≤ |U| ≤ r₂` with `S · h = g`. -/
theorem exists_conv_eq_of_dom {h : Entire K} {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) {k : ℤ}
    (hk₁ : ∀ n, n ≠ k → tnorm (Entire.coeff h) r₁ n < tnorm (Entire.coeff h) r₁ k)
    (hk₂ : ∀ n, n ≠ k → tnorm (Entire.coeff h) r₂ n < tnorm (Entire.coeff h) r₂ k)
    (g : Entire K) :
    ∃ S : ℤ → K, ConvAt S r₁ ∧ ConvAt S r₂ ∧ conv S (Entire.coeff h) = Entire.coeff g := by
  set a := Entire.coeff h k with ha_def
  have ha : a ≠ 0 := by
    intro h0
    have := hk₁ (k + 1) (by omega)
    simp only [tnorm] at this
    rw [← ha_def, h0, norm_zero, zero_mul] at this
    exact (mul_nonneg (norm_nonneg _) (zpow_nonneg hr₁.le _)).not_gt this
  set h₀ : Entire K := a⁻¹ • (Entire.mono (-k) * h) with hh₀
  set e : Entire K := 1 - h₀ with he
  have hcoeff_h₀ : Entire.coeff h₀ = a⁻¹ • shiftF (-k) (Entire.coeff h) := by
    rw [hh₀, Entire.coeff_smul, Entire.coeff_mono_mul_eq]
  have hcoeff_e : Entire.coeff e = Pi.single 0 1 - Entire.coeff h₀ := by
    rw [he, sub_eq_add_neg, Entire.coeff_add, Entire.coeff_neg, Entire.coeff_one, ← sub_eq_add_neg]
  -- the term norms of `e` are `< 1` at both radii
  have hte : ∀ {r : ℝ}, 0 < r → (∀ n, n ≠ k → tnorm (Entire.coeff h) r n <
      tnorm (Entire.coeff h) r k) → ∀ n, tnorm (Entire.coeff e) r n < 1 := by
    intro r hr hk n
    have hpos : 0 < tnorm (Entire.coeff h) r k := tnorm_pos hr ha
    rw [hcoeff_e, hcoeff_h₀]
    by_cases hn : n = 0
    · subst hn
      simp [tnorm, shiftF, ← ha_def, ha]
    · have hval : (Pi.single 0 1 - a⁻¹ • shiftF (-k) (Entire.coeff h) : ℤ → K) n =
          -(a⁻¹ * Entire.coeff h (n + k)) := by
        simp [shiftF, hn]
      have e1 : tnorm (Pi.single 0 1 - a⁻¹ • shiftF (-k) (Entire.coeff h) : ℤ → K) r n =
          tnorm (Entire.coeff h) r (n + k) / tnorm (Entire.coeff h) r k := by
        rw [tnorm, hval, norm_neg, norm_mul, norm_inv, tnorm, tnorm, ← ha_def,
          zpow_add₀ hr.ne']
        field_simp
      rw [e1, div_lt_one hpos]
      exact hk _ (by omega)
  have hge : ∀ {r : ℝ}, 0 < r → (∀ n, n ≠ k → tnorm (Entire.coeff h) r n <
      tnorm (Entire.coeff h) r k) → Entire.gn e r < 1 := by
    intro r hr hk
    obtain ⟨C, hC1, hC⟩ := exists_lt_bound ((Entire.isEntire_coeff e).tendsto_tnorm hr) one_pos
      (hte hr hk)
    exact (gnorm_le hC).trans_lt hC1
  set θ := max (Entire.gn e r₁) (Entire.gn e r₂)
  have hθ : θ < 1 := max_lt (hge hr₁ hk₁) (hge hr₂ hk₂)
  have hθ0 : 0 ≤ θ := (gnorm_nonneg (Entire.isEntire_coeff e) hr₁).trans (le_max_left _ _)
  set G : Entire K := a⁻¹ • (Entire.mono (-k) * g)
  set C := max (Entire.gn G r₁) (Entire.gn G r₂)
  set A : ℕ → ℤ → K := fun j => Entire.coeff (G * e ^ j)
  have hA : ∀ {r : ℝ}, 0 < r → Entire.gn G r ≤ C → Entire.gn e r ≤ θ →
      ∀ j n, tnorm (A j) r n ≤ C * θ ^ j := by
    intro r hr hG hE j n
    refine (le_gnorm (Entire.isEntire_coeff _) hr n).trans ?_
    change Entire.gn (G * e ^ j) r ≤ _
    rw [Entire.gn_mul _ _ hr, Entire.gn_pow _ hr]
    exact mul_le_mul hG (pow_le_pow_left₀ (gnorm_nonneg (Entire.isEntire_coeff e) hr) hE j)
      (pow_nonneg (gnorm_nonneg (Entire.isEntire_coeff e) hr) j)
      ((gnorm_nonneg (Entire.isEntire_coeff G) hr).trans hG)
  have hA₁ := hA hr₁ (le_max_left _ _) (le_max_left _ _)
  have hA₂ := hA hr₂ (le_max_right _ _) (le_max_right _ _)
  have hconv : ∀ {r : ℝ}, 0 < r → ∀ j, ConvAt (A j) r := fun hr j =>
    ConvAt.of_isEntire_coeff _ hr
  obtain ⟨S, hSdef⟩ : ∃ S : ℤ → K, S = fun n => ∑' j, A j n := ⟨_, rfl⟩
  have hS₁ : ConvAt S r₁ := hSdef ▸ convAt_tsum hr₁ hθ0 hθ hA₁ (hconv hr₁)
  have hS₂ : ConvAt S r₂ := hSdef ▸ convAt_tsum hr₂ hθ0 hθ hA₂ (hconv hr₂)
  refine ⟨S, hS₁, hS₂, ?_⟩
  -- `S = coeff G + S * e`
  have hfix : S = Entire.coeff G + conv S (Entire.coeff e) := by
    funext n
    rw [Pi.add_apply, hSdef,
      conv_tsum hr₁ hθ0 hθ hA₁ (hconv hr₁) (ConvAt.of_isEntire_coeff e hr₁) n]
    dsimp only
    rw [(summable_of_geom hr₁ hθ0 hθ hA₁ n).tsum_eq_zero_add]
    congr 1
    · simp [A]
    · congr 1; funext j
      simp only [A]
      rw [pow_succ, ← mul_assoc, Entire.coeff_mul (G * e ^ j) e]
  -- hence `S * h₀ = G`
  have hSh₀ : conv S (Entire.coeff h₀) = Entire.coeff G := by
    have h1 : Entire.coeff h₀ = Pi.single 0 1 - Entire.coeff e := by rw [hcoeff_e, sub_sub_cancel]
    have hδ : ConvAt (Pi.single 0 1 : ℤ → K) r₁ := by
      rw [← Entire.coeff_one]; exact ConvAt.of_isEntire_coeff 1 hr₁
    rw [h1, hS₁.conv_sub_right hδ (ConvAt.of_isEntire_coeff e hr₁) hr₁, conv_single_zero]
    nth_rewrite 1 [hfix]
    rw [add_sub_cancel_right]
  rw [hcoeff_h₀, conv_smul_right, conv_shiftF_right] at hSh₀
  have hG : Entire.coeff G = a⁻¹ • shiftF (-k) (Entire.coeff g) := by
    rw [Entire.coeff_smul, Entire.coeff_mono_mul_eq]
  rw [hG, ← shiftF_smul, ← shiftF_smul] at hSh₀
  have := shiftF_injective _ hSh₀
  exact smul_right_injective _ (inv_ne_zero ha) this

/-! ### Local factorisation and the quotient on an annulus -/

lemma conv_zero_left (d : ℤ → K) : conv 0 d = 0 := by funext l; simp [conv]

lemma convAt_zero {r : ℝ} : ConvAt (0 : ℤ → K) r := by
  have : tnorm (0 : ℤ → K) r = fun _ => 0 := by funext n; simp [tnorm]
  rw [ConvAt, this]; exact tendsto_const_nhds

lemma tnorm_polyCoeff_lin (α : K) (r : ℝ) (n : ℤ) :
    tnorm (polyCoeff (lin α)) r n = if n = 0 then ‖α‖ else if n = 1 then r else 0 := by
  rw [tnorm, polyCoeff_lin]
  split_ifs with h0 h1
  · subst h0; simp
  · subst h1; simp
  · simp

lemma gnorm_polyCoeff_lin (α : K) {r : ℝ} (hr : 0 < r) :
    gnorm (polyCoeff (lin α)) r = max ‖α‖ r := by
  refine le_antisymm (gnorm_le fun n => ?_) (max_le ?_ ?_)
  · rw [tnorm_polyCoeff_lin]
    split_ifs
    · exact le_max_left _ _
    · exact le_max_right _ _
    · exact (norm_nonneg α).trans (le_max_left _ _)
  · have := le_gnorm (isEntire_lin α) hr 0
    rwa [tnorm_polyCoeff_lin, if_pos rfl] at this
  · have := le_gnorm (isEntire_lin α) hr 1
    rwa [tnorm_polyCoeff_lin, if_neg one_ne_zero, if_pos rfl] at this

lemma lo_lin_of_le {α : K} {r : ℝ} (hr : 0 < r) (h : r ≤ ‖α‖) :
    lo (polyCoeff (lin α)) r = 0 := by
  have hg := gnorm_polyCoeff_lin α hr
  refine lo_eq_of (isEntire_lin α) (lin_ne_zero α) hr ?_ fun m hm => ?_
  · rw [tnorm_polyCoeff_lin, if_pos rfl, hg, max_eq_left h]
  · rw [tnorm_polyCoeff_lin, if_neg (by omega), if_neg (by omega), hg]
    exact hr.trans_le (le_max_right _ _)

lemma hi_lin_of_le {α : K} {r : ℝ} (hr : 0 < r) (h : ‖α‖ ≤ r) :
    hi (polyCoeff (lin α)) r = 1 := by
  have hg := gnorm_polyCoeff_lin α hr
  refine hi_eq_of (isEntire_lin α) (lin_ne_zero α) hr ?_ fun m hm => ?_
  · rw [tnorm_polyCoeff_lin, if_neg one_ne_zero, if_pos rfl, hg, max_eq_right h]
  · rw [tnorm_polyCoeff_lin, if_neg (by omega), if_neg (by omega), hg]
    exact hr.trans_le (le_max_right _ _)

lemma lo_le_hi_of_le {c : ℤ → K} (hc : IsEntire c) (hc0 : c ≠ 0) {r s : ℝ} (hr : 0 < r)
    (hrs : r ≤ s) : lo c r ≤ hi c s := by
  rcases hrs.lt_or_eq with hrs | rfl
  · exact (lo_le_hi hc hc0 hr).trans ((hi_le_lo hc hc0 hr hrs).trans
      (lo_le_hi hc hc0 (hr.trans hrs)))
  · exact lo_le_hi hc hc0 hr

section AlgClosed

variable [IsAlgClosed K]

/-- **Inversion of a series without zeros on a closed annulus.** -/
theorem exists_conv_eq_of_no_zero {h : Entire K} (hh : h ≠ 0) {v₁ v₂ : Kˣ}
    (h12 : ‖(v₁ : K)‖ ≤ ‖(v₂ : K)‖)
    (hz : ∀ α : Kˣ, ‖(v₁ : K)‖ ≤ ‖(α : K)‖ → ‖(α : K)‖ ≤ ‖(v₂ : K)‖ → (h : Kˣ → K) α ≠ 0)
    (g : Entire K) :
    ∃ S : ℤ → K, ConvAt S ‖(v₁ : K)‖ ∧ ConvAt S ‖(v₂ : K)‖ ∧
      conv S (Entire.coeff h) = Entire.coeff g := by
  have hc := Entire.isEntire_coeff h
  have hc0 := Entire.coeff_ne_zero hh
  have hpos : ∀ u : Kˣ, 0 < ‖(u : K)‖ := fun u => norm_pos_iff.mpr u.ne_zero
  have hedge : ∀ w : Kˣ, ‖(v₁ : K)‖ ≤ ‖(w : K)‖ → ‖(w : K)‖ ≤ ‖(v₂ : K)‖ →
      lo (Entire.coeff h) ‖(w : K)‖ = hi (Entire.coeff h) ‖(w : K)‖ := fun w h1 h2 => by
    by_contra hne
    obtain ⟨u, hu, hu0⟩ := exists_zero_of_lo_lt_hi hh w
      (lt_of_le_of_ne (lo_le_hi hc hc0 (hpos w)) hne)
    exact hz u (by rw [hu]; exact h1) (by rw [hu]; exact h2) hu0
  have hk := lo_eq_of_no_edge hc hc0 h12 hedge
  set k := lo (Entire.coeff h) ‖(v₁ : K)‖
  have hdom : ∀ w : Kˣ, ‖(v₁ : K)‖ ≤ ‖(w : K)‖ → ‖(w : K)‖ ≤ ‖(v₂ : K)‖ →
      lo (Entire.coeff h) ‖(w : K)‖ = k → ∀ n, n ≠ k →
        tnorm (Entire.coeff h) ‖(w : K)‖ n < tnorm (Entire.coeff h) ‖(w : K)‖ k :=
    fun w h1 h2 hw n hn => by
      rw [← hw, tnorm_lo hc hc0 (hpos w)]
      refine tnorm_lt_of_notMem hc hc0 (hpos w) fun hm => hn (le_antisymm ?_ ?_)
      · have := le_hi_of_mem hc hc0 (hpos w) hm; rwa [← hedge w h1 h2, hw] at this
      · have := le_lo_of_mem hc hc0 (hpos w) hm; rwa [hw] at this
  exact exists_conv_eq_of_dom (hpos v₁) (hpos v₂) (hdom v₁ le_rfl h12 rfl)
    (hdom v₂ h12 le_rfl hk.symm) g

/-- **The quotient `g/h` on a closed annulus** (`ord h ≤ ord g` everywhere): local factorisation
`h = P·h'` with the zeros of `h` on the annulus, then inversion of `h'`. -/
theorem exists_conv_eq_on_annulus {v₁ v₂ : Kˣ} (h12 : ‖(v₁ : K)‖ ≤ ‖(v₂ : K)‖) (n : ℕ) :
    ∀ g h : Entire K, h ≠ 0 →
      hi (Entire.coeff h) ‖(v₂ : K)‖ - lo (Entire.coeff h) ‖(v₁ : K)‖ ≤ n →
      (∀ α, ord h α ≤ ord g α) →
      ∃ S : ℤ → K, ConvAt S ‖(v₁ : K)‖ ∧ ConvAt S ‖(v₂ : K)‖ ∧
        conv S (Entire.coeff h) = Entire.coeff g := by
  have hpos : ∀ u : Kˣ, 0 < ‖(u : K)‖ := fun u => norm_pos_iff.mpr u.ne_zero
  induction n with
  | zero =>
    intro g h hh hn hord
    by_cases hz : ∃ α : Kˣ, ‖(v₁ : K)‖ ≤ ‖(α : K)‖ ∧ ‖(α : K)‖ ≤ ‖(v₂ : K)‖ ∧ (h : Kˣ → K) α = 0
    · exfalso
      obtain ⟨α, h1, h2, h0⟩ := hz
      obtain ⟨h₁, rfl⟩ := exists_eq_lin_mul h0
      have hh₁ : h₁ ≠ 0 := by rintro rfl; exact hh (mul_zero _)
      have hl := polyE_lin_ne_zero (α : K)
      rw [Entire.hi_mul hl hh₁ (hpos v₂), Entire.lo_mul hl hh₁ (hpos v₁), coeff_polyE,
        hi_lin_of_le (hpos v₂) h2, lo_lin_of_le (hpos v₁) h1] at hn
      have := lo_le_hi_of_le (Entire.isEntire_coeff h₁) (Entire.coeff_ne_zero hh₁) (hpos v₁) h12
      push_cast at hn
      omega
    · push Not at hz
      exact exists_conv_eq_of_no_zero hh h12 hz g
  | succ n ih =>
    intro g h hh hn hord
    by_cases hz : ∃ α : Kˣ, ‖(v₁ : K)‖ ≤ ‖(α : K)‖ ∧ ‖(α : K)‖ ≤ ‖(v₂ : K)‖ ∧ (h : Kˣ → K) α = 0
    · obtain ⟨α, h1, h2, h0⟩ := hz
      by_cases hg : g = 0
      · subst hg
        exact ⟨0, convAt_zero, convAt_zero, by rw [conv_zero_left, Entire.coeff_zero]⟩
      have hordh : ord h α ≠ 0 := fun h' => (ord_eq_zero_iff hh α).mp h' h0
      have hg0 : (g : Kˣ → K) α = 0 := by
        by_contra hne
        exact hordh (Nat.eq_zero_of_le_zero ((hord α).trans ((ord_eq_zero_iff hg α).mpr hne).le))
      obtain ⟨h₁, rfl⟩ := exists_eq_lin_mul h0
      obtain ⟨g₁, rfl⟩ := exists_eq_lin_mul hg0
      have hh₁ : h₁ ≠ 0 := by rintro rfl; exact hh (mul_zero _)
      have hg₁ : g₁ ≠ 0 := by rintro rfl; exact hg (mul_zero _)
      have hl := polyE_lin_ne_zero (α : K)
      have hn₁ : hi (Entire.coeff h₁) ‖(v₂ : K)‖ - lo (Entire.coeff h₁) ‖(v₁ : K)‖ ≤ n := by
        rw [Entire.hi_mul hl hh₁ (hpos v₂), Entire.lo_mul hl hh₁ (hpos v₁), coeff_polyE,
          hi_lin_of_le (hpos v₂) h2, lo_lin_of_le (hpos v₁) h1] at hn
        push_cast at hn
        omega
      have hord₁ : ∀ β, ord h₁ β ≤ ord g₁ β := fun β => by
        have := hord β
        rw [ord_mul hl hh₁, ord_mul hl hg₁] at this
        omega
      obtain ⟨S, hS₁, hS₂, hS⟩ := ih g₁ h₁ hh₁ hn₁ hord₁
      refine ⟨S, hS₁, hS₂, ?_⟩
      have hr := hpos v₁
      have hc₁ := ConvAt.of_isEntire_coeff h₁ hr
      rw [coeff_lin_mul, coeff_lin_mul, hS₁.conv_sub_right (hc₁.shiftF hr 1) (hc₁.smul _) hr,
        conv_shiftF_right, conv_smul_right, hS]
    · push Not at hz
      exact exists_conv_eq_of_no_zero hh h12 hz g

/-- **Cancellation of common zeros in `E(K)`**: if `ord_α h ≤ ord_α g` at every point `α ∈ Kˣ`,
then `h` divides `g` (over an algebraically closed complete ultrametric `K`). -/
theorem Entire.dvd_of_ord_le {g h : Entire K} (hh : h ≠ 0) (hord : ∀ α, ord h α ≤ ord g α) :
    h ∣ g := by
  have hpos : ∀ u : Kˣ, 0 < ‖(u : K)‖ := fun u => norm_pos_iff.mpr u.ne_zero
  have hloc : ∀ v : Kˣ, 1 ≤ ‖(v : K)‖ → ∃ S : ℤ → K, ConvAt S ‖((v⁻¹ : Kˣ) : K)‖ ∧
      ConvAt S ‖(v : K)‖ ∧ conv S (Entire.coeff h) = Entire.coeff g := fun v hv => by
    have h12 : ‖((v⁻¹ : Kˣ) : K)‖ ≤ ‖(v : K)‖ := by
      rw [Units.val_inv_eq_inv_val, norm_inv]
      exact (inv_le_one_of_one_le₀ hv).trans hv
    exact exists_conv_eq_on_annulus h12 _ g h hh (Int.self_le_toNat _) hord
  have hinv1 : ∀ v : Kˣ, 1 ≤ ‖(v : K)‖ → ‖((v⁻¹ : Kˣ) : K)‖ ≤ 1 := fun v hv => by
    rw [Units.val_inv_eq_inv_val, norm_inv]; exact inv_le_one_of_one_le₀ hv
  obtain ⟨v₀, hv₀⟩ := exists_unit_le_norm (K := K) 1
  obtain ⟨S, hS₁, hS₂, hS⟩ := hloc v₀ hv₀
  have hS1 : ConvAt S 1 := ConvAt.of_le_of_le hS₁ hS₂ (hpos _) (hinv1 v₀ hv₀) hv₀
  have hh1 := ConvAt.of_isEntire_coeff h one_pos
  have huniq : ∀ v : Kˣ, 1 ≤ ‖(v : K)‖ → ∀ T : ℤ → K, ConvAt T ‖((v⁻¹ : Kˣ) : K)‖ →
      ConvAt T ‖(v : K)‖ → conv T (Entire.coeff h) = Entire.coeff g → T = S := by
    intro v hv T hT₁ hT₂ hT
    have hT1 : ConvAt T 1 := ConvAt.of_le_of_le hT₁ hT₂ (hpos _) (hinv1 v hv) hv
    by_contra hne
    have h0 : conv (T - S) (Entire.coeff h) = 0 := by
      rw [conv_comm, hh1.conv_sub_right hT1 hS1 one_pos, conv_comm, hT, conv_comm, hS, sub_self]
    exact ConvAt.conv_ne_zero (hT1.sub hS1 one_pos) hh1 (sub_ne_zero.mpr hne)
      (Entire.coeff_ne_zero hh) one_pos h0
  have hconv : ∀ r : ℝ, 0 < r → ConvAt S r := fun r hr => by
    obtain ⟨v, hv⟩ := exists_unit_le_norm (K := K) (max 1 (max r r⁻¹))
    have hv1 : 1 ≤ ‖(v : K)‖ := (le_max_left _ _).trans hv
    obtain ⟨T, hT₁, hT₂, hT⟩ := hloc v hv1
    have hTS := huniq v hv1 T hT₁ hT₂ hT
    subst hTS
    refine ConvAt.of_le_of_le hT₁ hT₂ (hpos _) ?_ ((le_max_left _ _).trans
      ((le_max_right _ _).trans hv))
    rw [Units.val_inv_eq_inv_val, norm_inv]
    exact inv_le_of_inv_le₀ hr ((le_max_right _ _).trans ((le_max_right _ _).trans hv))
  refine ⟨Entire.ofCoeff S (isEntire_of_convAt hconv), Entire.ext_coeff ?_⟩
  rw [mul_comm, Entire.coeff_mul, Entire.coeff_ofCoeff, hS]

end AlgClosed

end Iut.Frobenioid.BAn
