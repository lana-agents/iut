/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.Tempered.RatFunGauss
import TateCurvesTheta.Theta.Inversion

/-!
# The theta function `Θ̈` as an entire Laurent series (MR18 T8, route B-an)

[EtTh] Proposition 1.4 defines
`Θ̈(Ü) = q^{-1/8} ∑_{n ∈ ℤ} (-1)ⁿ q^{(n+1/2)²/2} Ü^{2n+1}`. Since `(n + 1/2)²/2 = e(n) + 1/8` with
`e(n) = n(n+1)/2` (tate-curves-theta `thetaExp`), this is `∑ₙ (-1)ⁿ q^{e(n)} Ü^{2n+1} = Ü·θ(-Ü²)`,
i.e. **exactly tate-curves-theta's `thetaOdd`** (no root of `q` is needed).

Here `Θ̈` becomes an element `thetaDd t` of the ring `E(K)` of entire Laurent series in the
coordinate `Ü` of the universal combinatorial covering of `Ÿ` (`RatFunEntire.lean`).

## Main results

* `thetaDdCoeff`, `thetaDd`, `coe_thetaDd` (`Θ̈ = thetaOdd` as functions on `Kˣ`).
* [EtTh] Proposition 1.4(ii): `thetaDd_inv` (`Θ̈(Ü⁻¹) = -Θ̈(Ü)`), `thetaDd_neg` (`Θ̈(-Ü) = -Θ̈(Ü)`),
  and the translation formula as an identity in `E(K)`: `scale_thetaDd`
  (`Θ̈(q^{a/2}Ü) = (-1)^a q^{-a²/2} Ü^{-2a} Θ̈(Ü)` for a square root `s` of `q`, `q^{a/2} := s^a`).
* [EtTh] Proposition 1.4(i), zeros: `thetaDd_eq_zero_iff` (the zeros are the cusps `Ü² ∈ q^ℤ`).
* [EtTh] Proposition 1.4(i), special fibre: `gn_thetaDd` (`|Θ̈|_{‖q‖^{a/2}} = ‖q‖^{-a²/2}`, the
  pole order `a²/2·ord(q)` of `Θ̈` along the component labelled `a`) and `lo_thetaDd`, `hi_thetaDd`
  (dominant indices `-2a ∓ 1`: two zeros `±q^{a/2}` on that circle).
* `scale s f` (`f(s·Ü)`), `coeff_scale`, `gn_scale`, `lo_scale`, `hi_scale`; `gn_algebraMap`,
  `gn_mono`, `gn_smul_mono_mul`, `lo_smul_mono_mul`, `hi_smul_mono_mul`.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace Iut.Frobenioid.BAn

open TateCurvesTheta TateParameter Filter Topology

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]

/-! ### Scaling `Ü ↦ s·Ü` -/

lemma IsEntire.scale {c : ℤ → K} (hc : IsEntire c) (s : Kˣ) :
    IsEntire fun n => c n * (s : K) ^ n := fun u => by
  refine (hc (s * u)).congr fun n => ?_
  rw [Units.val_mul, mul_zpow, mul_assoc]

namespace Entire

/-- The function `Ü ↦ f(s·Ü)`. -/
def scale (s : Kˣ) (f : Entire K) : Entire K :=
  ofCoeff (fun n => coeff f n * (s : K) ^ n) ((isEntire_coeff f).scale s)

lemma coeff_scale (s : Kˣ) (f : Entire K) (n : ℤ) :
    coeff (scale s f) n = coeff f n * (s : K) ^ n := by
  rw [scale, coeff_ofCoeff]

lemma coe_scale (s : Kˣ) (f : Entire K) (u : Kˣ) :
    ((scale s f : Entire K) : Kˣ → K) u = (f : Kˣ → K) (s * u) := by
  rw [scale, ofCoeff]
  change lsum _ u = _
  rw [lsum, ((coeff_spec f (s * u)).congr_fun fun n => ?_).tsum_eq]
  rw [Units.val_mul, mul_zpow, mul_assoc]

lemma tnorm_scale (s : Kˣ) (f : Entire K) (r : ℝ) (n : ℤ) :
    tnorm (coeff (scale s f)) r n = tnorm (coeff f) (‖(s : K)‖ * r) n := by
  rw [tnorm, tnorm, coeff_scale, norm_mul, norm_zpow, mul_zpow, mul_assoc]

lemma gn_scale (s : Kˣ) (f : Entire K) (r : ℝ) : gn (scale s f) r = gn f (‖(s : K)‖ * r) := by
  simp only [gn, gnorm, tnorm_scale]

lemma domSet_scale (s : Kˣ) (f : Entire K) (r : ℝ) :
    domSet (coeff (scale s f)) r = domSet (coeff f) (‖(s : K)‖ * r) := by
  ext n
  simp only [domSet, Set.mem_setOf_eq, tnorm_scale]
  rw [show gnorm (coeff (scale s f)) r = gnorm (coeff f) (‖(s : K)‖ * r) from gn_scale s f r]

lemma lo_scale (s : Kˣ) (f : Entire K) (r : ℝ) :
    lo (coeff (scale s f)) r = lo (coeff f) (‖(s : K)‖ * r) := by
  rw [lo, lo, domSet_scale]

lemma hi_scale (s : Kˣ) (f : Entire K) (r : ℝ) :
    hi (coeff (scale s f)) r = hi (coeff f) (‖(s : K)‖ * r) := by
  rw [hi, hi, domSet_scale]

/-! ### Gauss norms and dominant indices of `a·Uᵏ·f` -/

lemma gnorm_single (k : ℤ) (a : K) {r : ℝ} (hr : 0 < r) :
    gnorm (Pi.single k a) r = ‖a‖ * r ^ k := by
  refine le_antisymm (gnorm_le fun n => ?_) ?_
  · by_cases hn : n = k
    · subst hn; simp [tnorm]
    · simp only [tnorm, Pi.single_apply, hn, if_false, norm_zero, zero_mul]
      exact mul_nonneg (norm_nonneg a) (zpow_nonneg hr.le k)
  · have := le_gnorm (isEntire_single k a) hr k
    simpa [tnorm] using this

lemma gn_algebraMap (a : K) {r : ℝ} (hr : 0 < r) : gn (algebraMap K (Entire K) a) r = ‖a‖ := by
  rw [gn, coeff_algebraMap, gnorm_single 0 a hr, zpow_zero, mul_one]

lemma gn_mono (k : ℤ) {r : ℝ} (hr : 0 < r) : gn (mono k : Entire K) r = r ^ k := by
  rw [gn, coeff_mono, gnorm_single k 1 hr, norm_one, one_mul]

lemma gn_smul_mono_mul (a : K) (k : ℤ) (f : Entire K) {r : ℝ} (hr : 0 < r) :
    gn (a • (mono k * f)) r = ‖a‖ * r ^ k * gn f r := by
  rw [Algebra.smul_def, gn_mul _ _ hr, gn_mul _ _ hr, gn_algebraMap a hr, gn_mono k hr, mul_assoc]

lemma ne_zero_smul_mono_mul {a : K} (ha : a ≠ 0) (k : ℤ) {f : Entire K} (hf : f ≠ 0) :
    a • (mono k * f) ≠ 0 := by
  rw [Algebra.smul_def]
  refine mul_ne_zero (fun h => ha ?_) (mul_ne_zero (isUnit_mono k).ne_zero hf)
  exact (algebraMap K (Entire K)).injective (by rw [h, map_zero])

lemma lo_smul_mono_mul {a : K} (ha : a ≠ 0) (k : ℤ) {f : Entire K} (hf : f ≠ 0) {r : ℝ}
    (hr : 0 < r) : lo (coeff (a • (mono k * f))) r = k + lo (coeff f) r := by
  have h0 : algebraMap K (Entire K) a ≠ 0 := fun h => ha
    ((algebraMap K (Entire K)).injective (by rw [h, map_zero]))
  rw [Algebra.smul_def, lo_mul h0 (mul_ne_zero (isUnit_mono k).ne_zero hf) hr,
    lo_mul (isUnit_mono k).ne_zero hf hr, coeff_algebraMap, coeff_mono,
    lo_single 0 a ha hr, lo_single k 1 one_ne_zero hr, zero_add]

lemma hi_smul_mono_mul {a : K} (ha : a ≠ 0) (k : ℤ) {f : Entire K} (hf : f ≠ 0) {r : ℝ}
    (hr : 0 < r) : hi (coeff (a • (mono k * f))) r = k + hi (coeff f) r := by
  have h0 : algebraMap K (Entire K) a ≠ 0 := fun h => ha
    ((algebraMap K (Entire K)).injective (by rw [h, map_zero]))
  rw [Algebra.smul_def, hi_mul h0 (mul_ne_zero (isUnit_mono k).ne_zero hf) hr,
    hi_mul (isUnit_mono k).ne_zero hf hr, coeff_algebraMap, coeff_mono,
    hi_single 0 a ha hr, hi_single k 1 one_ne_zero hr, zero_add]

end Entire

/-! ### The coefficients of `Θ̈` -/

section Theta

variable (t : TateParameter K)

/-- The odd embedding `m ↦ 2m + 1`. -/
def oddEmb (m : ℤ) : ℤ := 2 * m + 1

lemma oddEmb_injective : Function.Injective oddEmb := fun a b h => by
  simp only [oddEmb] at h; omega

/-- The coefficient `(-1)^m q^{e(m)}` of `Ü^{2m+1}` in `Θ̈`. -/
def thetaDdOdd (m : ℤ) : K := (-1 : K) ^ m * (t.q : K) ^ thetaExp m

/-- **The coefficients of `Θ̈`**: `(-1)^m q^{e(m)}` at `2m + 1`, zero at even indices. -/
def thetaDdCoeff : ℤ → K := Function.extend oddEmb (thetaDdOdd t) 0

lemma thetaDdCoeff_odd (m : ℤ) : thetaDdCoeff t (2 * m + 1) = thetaDdOdd t m :=
  oddEmb_injective.extend_apply _ _ m

lemma thetaDdCoeff_of_notMem {n : ℤ} (hn : ¬ ∃ m, oddEmb m = n) : thetaDdCoeff t n = 0 := by
  rw [thetaDdCoeff, Function.extend_apply' _ _ _ hn, Pi.zero_apply]

lemma hasSum_thetaDd (u : Kˣ) :
    HasSum (fun n : ℤ => thetaDdCoeff t n * (u : K) ^ n) (t.thetaOdd u) := by
  have hu : (u : K) ≠ 0 := u.ne_zero
  have h := ((t.thetaTerm_summable (-(u ^ 2))).hasSum).mul_left (u : K)
  rw [← Function.Injective.hasSum_iff oddEmb_injective (fun n hn => by
    rw [thetaDdCoeff_of_notMem t (by simpa using hn), zero_mul])]
  rw [thetaOdd, theta]
  refine h.congr_fun fun m => ?_
  simp only [Function.comp_apply, oddEmb, thetaDdCoeff_odd, thetaDdOdd, thetaTerm,
    Units.val_neg, Units.val_pow_eq_pow_val]
  have key : ((-((u : K) ^ 2)) ^ m : K) = (-1 : K) ^ m * (u : K) ^ (2 * m) := by
    rw [neg_eq_neg_one_mul, mul_zpow, ← zpow_natCast (u : K) 2, ← zpow_mul]; norm_num
  rw [key, zpow_add_one₀ hu]
  ring

lemma isEntire_thetaDdCoeff : IsEntire (thetaDdCoeff t) := fun u => (hasSum_thetaDd t u).summable

/-- **`Θ̈ ∈ E(K)`** ([EtTh] Proposition 1.4). -/
def thetaDd : Entire K := Entire.ofCoeff (thetaDdCoeff t) (isEntire_thetaDdCoeff t)

lemma coeff_thetaDd : Entire.coeff (thetaDd t) = thetaDdCoeff t := Entire.coeff_ofCoeff _ _

/-- `Θ̈` is tate-curves-theta's odd theta function. -/
lemma coe_thetaDd : ((thetaDd t : Entire K) : Kˣ → K) = t.thetaOdd := by
  funext u
  exact (hasSum_thetaDd t u).tsum_eq

lemma thetaDd_ne_zero : thetaDd t ≠ 0 := by
  intro h
  have := congrFun (congrArg Entire.coeff h) 1
  rw [coeff_thetaDd, Entire.coeff_zero, show (1 : ℤ) = 2 * 0 + 1 by norm_num,
    thetaDdCoeff_odd] at this
  simp [thetaDdOdd, thetaExp] at this

/-- [EtTh] Proposition 1.4(ii): `Θ̈(Ü⁻¹) = -Θ̈(Ü)`. -/
theorem thetaDd_inv (u : Kˣ) :
    ((thetaDd t : Entire K) : Kˣ → K) u⁻¹ = -((thetaDd t : Entire K) : Kˣ → K) u := by
  rw [coe_thetaDd, t.thetaOdd_inv]

/-- [EtTh] Proposition 1.4(ii): `Θ̈(-Ü) = -Θ̈(Ü)`. -/
theorem thetaDd_neg (u : Kˣ) :
    ((thetaDd t : Entire K) : Kˣ → K) (-u) = -((thetaDd t : Entire K) : Kˣ → K) u := by
  rw [coe_thetaDd, thetaOdd, thetaOdd, neg_sq, Units.val_neg, neg_mul]

/-- [EtTh] Proposition 1.4(i), zeros: the zeros of `Θ̈` on `Kˣ` are the cusps `Ü² ∈ q^ℤ`. -/
theorem thetaDd_eq_zero_iff (u : Kˣ) :
    ((thetaDd t : Entire K) : Kˣ → K) u = 0 ↔ ∃ k : ℤ, (u : K) ^ 2 = (t.q : K) ^ k := by
  rw [coe_thetaDd, t.thetaOdd_eq_zero_iff]

/-- The coefficient identity behind the translation formula. -/
lemma thetaDdCoeff_translate {s : Kˣ} (hs : (s : K) ^ 2 = t.q) (a n : ℤ) :
    thetaDdCoeff t n * ((s : K) ^ a) ^ n =
      (-1 : K) ^ a * (s : K) ^ (-(a ^ 2)) * thetaDdCoeff t (n + 2 * a) := by
  by_cases hn : ∃ m, oddEmb m = n
  · obtain ⟨m, rfl⟩ := hn
    have e : 2 * m + 1 + 2 * a = 2 * (m + a) + 1 := by ring
    rw [oddEmb, e, thetaDdCoeff_odd, thetaDdCoeff_odd, thetaDdOdd, thetaDdOdd]
    have hs0 : (s : K) ≠ 0 := s.ne_zero
    have hq : (t.q : K) = (s : K) ^ (2 : ℤ) := by rw [← hs, zpow_ofNat]
    have h1 := two_mul_thetaExp m
    have h2 := two_mul_thetaExp (m + a)
    have hsign : (-1 : K) ^ a * (-1 : K) ^ (m + a) = (-1 : K) ^ m := by
      rw [← zpow_add₀ (by norm_num : (-1 : K) ≠ 0),
        show a + (m + a) = m + 2 * a by ring, zpow_add₀ (by norm_num : (-1 : K) ≠ 0),
        zpow_mul, show ((-1 : K) ^ (2 : ℤ)) = 1 by norm_num, one_zpow, mul_one]
    have hexp : (s : K) ^ (2 * thetaExp m) * (s : K) ^ (a * (2 * m + 1)) =
        (s : K) ^ (-(a ^ 2)) * (s : K) ^ (2 * thetaExp (m + a)) := by
      rw [← zpow_add₀ hs0, ← zpow_add₀ hs0]
      congr 1
      rw [h1, h2]; ring
    rw [hq, ← zpow_mul, ← zpow_mul, ← zpow_mul]
    calc (-1 : K) ^ m * (s : K) ^ (2 * thetaExp m) * (s : K) ^ (a * (2 * m + 1))
        = (-1 : K) ^ m * ((s : K) ^ (2 * thetaExp m) * (s : K) ^ (a * (2 * m + 1))) := by ring
      _ = (-1 : K) ^ a * (-1 : K) ^ (m + a) *
            ((s : K) ^ (-(a ^ 2)) * (s : K) ^ (2 * thetaExp (m + a))) := by rw [hexp, hsign]
      _ = _ := by ring
  · have hn' : ¬ ∃ m, oddEmb m = n + 2 * a := by
      rintro ⟨m, hm⟩
      exact hn ⟨m - a, by simp only [oddEmb] at hm ⊢; omega⟩
    rw [thetaDdCoeff_of_notMem t hn, thetaDdCoeff_of_notMem t hn']
    ring

/-- **[EtTh] Proposition 1.4(ii), translation formula, as an identity in `E(K)`**: for `s² = q`,
`Θ̈(s^a·Ü) = (-1)^a s^{-a²} Ü^{-2a} Θ̈(Ü)` (`s^a = q^{a/2}`, `s^{-a²} = q^{-a²/2}`). -/
theorem scale_thetaDd {s : Kˣ} (hs : (s : K) ^ 2 = t.q) (a : ℤ) :
    Entire.scale (s ^ a) (thetaDd t) =
      ((-1 : K) ^ a * (s : K) ^ (-(a ^ 2))) • (Entire.mono (-(2 * a)) * thetaDd t) := by
  refine Entire.ext_coeff (funext fun n => ?_)
  rw [Entire.coeff_scale, Entire.coeff_smul, Pi.smul_apply, smul_eq_mul,
    Entire.coeff_mono_mul, coeff_thetaDd, Units.val_zpow_eq_zpow_val, sub_neg_eq_add,
    thetaDdCoeff_translate t hs]

/-! ### Gauss norms of `Θ̈`: the special-fibre part of its divisor -/

lemma norm_thetaDdOdd (m : ℤ) : ‖thetaDdOdd t m‖ = ‖(t.q : K)‖ ^ thetaExp m := by
  rw [thetaDdOdd, norm_mul, norm_zpow, norm_neg, norm_one, one_zpow, one_mul, norm_zpow]

lemma thetaExp_eq_zero_iff (m : ℤ) : thetaExp m = 0 ↔ m = 0 ∨ m = -1 := by
  have h := two_mul_thetaExp m
  constructor
  · intro h0
    rw [h0, mul_zero] at h
    rcases mul_eq_zero.mp h.symm with h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
  · rintro (rfl | rfl) <;> decide

lemma tnorm_thetaDd_one (n : ℤ) :
    tnorm (thetaDdCoeff t) 1 n = if n = 1 ∨ n = -1 then 1 else
      tnorm (thetaDdCoeff t) 1 n := by
  split_ifs with h
  · rcases h with rfl | rfl
    · rw [show (1 : ℤ) = 2 * 0 + 1 by norm_num, tnorm, thetaDdCoeff_odd, norm_thetaDdOdd]
      simp [thetaExp]
    · rw [show (-1 : ℤ) = 2 * (-1) + 1 by norm_num, tnorm, thetaDdCoeff_odd, norm_thetaDdOdd]
      simp [thetaExp]
  · rfl

lemma tnorm_thetaDd_one_lt {n : ℤ} (hn : n ≠ 1 ∧ n ≠ -1) : tnorm (thetaDdCoeff t) 1 n < 1 := by
  by_cases h : ∃ m, oddEmb m = n
  · obtain ⟨m, rfl⟩ := h
    rw [tnorm, oddEmb, thetaDdCoeff_odd, norm_thetaDdOdd, one_zpow, mul_one]
    have hm : thetaExp m ≠ 0 := fun h0 => by
      rcases (thetaExp_eq_zero_iff m).mp h0 with rfl | rfl
      · exact hn.1 (by simp [oddEmb])
      · exact hn.2 (by simp [oddEmb])
    have hpos : 0 < thetaExp m := lt_of_le_of_ne (thetaExp_nonneg m) (Ne.symm hm)
    exact zpow_lt_one₀ t.norm_q_pos t.norm_lt_one hpos
  · rw [tnorm, thetaDdCoeff_of_notMem t h]
    simp

lemma gn_thetaDd_one : Entire.gn (thetaDd t) 1 = 1 := by
  rw [Entire.gn, coeff_thetaDd]
  refine le_antisymm (gnorm_le fun n => ?_) ?_
  · by_cases hn : n = 1 ∨ n = -1
    · rw [tnorm_thetaDd_one t n, if_pos hn]
    · push Not at hn; exact (tnorm_thetaDd_one_lt t hn).le
  · have := le_gnorm (isEntire_thetaDdCoeff t) one_pos 1
    rwa [tnorm_thetaDd_one t 1, if_pos (Or.inl rfl)] at this

lemma domSet_thetaDd_one : domSet (thetaDdCoeff t) 1 = {-1, 1} := by
  have hg : gnorm (thetaDdCoeff t) 1 = 1 := by rw [← coeff_thetaDd]; exact gn_thetaDd_one t
  ext n
  simp only [domSet, Set.mem_setOf_eq, hg, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro h
    by_contra hn
    push Not at hn
    exact (tnorm_thetaDd_one_lt t ⟨hn.2, hn.1⟩).ne h
  · intro h
    rw [tnorm_thetaDd_one t n, if_pos (h.elim Or.inr Or.inl)]

lemma lo_thetaDd_one : lo (thetaDdCoeff t) 1 = -1 := by
  rw [lo, domSet_thetaDd_one]
  exact le_antisymm (csInf_le (Set.toFinite _).bddBelow (by simp))
    (le_csInf ⟨-1, by simp⟩ (by rintro b (rfl | rfl) <;> norm_num))

lemma hi_thetaDd_one : hi (thetaDdCoeff t) 1 = 1 := by
  rw [hi, domSet_thetaDd_one]
  exact le_antisymm (csSup_le ⟨-1, by simp⟩ (by rintro b (rfl | rfl) <;> norm_num))
    (le_csSup (Set.toFinite _).bddAbove (by simp))

variable {t}

/-- **[EtTh] Proposition 1.4(i), special fibre**: on the circle `|Ü| = ‖q‖^{a/2}` (the
irreducible component labelled `a` of the special fibre of `Ÿ`), `|Θ̈| = ‖q‖^{-a²/2}`; for
`a ≠ 0` this is the pole of order `(a²/2)·ord(q)` of `Θ̈` along that component (the divisor
`D1` of [EtTh] Proposition 1.4(i)). Here `‖q‖^{a/2} = ‖s‖^a` for `s² = q`. -/
theorem gn_thetaDd {s : Kˣ} (hs : (s : K) ^ 2 = t.q) (a : ℤ) :
    Entire.gn (thetaDd t) (‖(s : K)‖ ^ a) = ‖(s : K)‖ ^ (-(a ^ 2)) := by
  have h := Entire.gn_scale (s ^ a) (thetaDd t) 1
  rw [mul_one, Units.val_zpow_eq_zpow_val, norm_zpow, scale_thetaDd t hs,
    Entire.gn_smul_mono_mul _ _ _ one_pos, gn_thetaDd_one, one_zpow, mul_one, mul_one,
    norm_mul, norm_zpow, norm_neg, norm_one, one_zpow, one_mul, norm_zpow] at h
  exact h.symm

/-- The lowest dominant index of `Θ̈` on the circle `|Ü| = ‖q‖^{a/2}` is `-2a - 1`. -/
theorem lo_thetaDd {s : Kˣ} (hs : (s : K) ^ 2 = t.q) (a : ℤ) :
    lo (thetaDdCoeff t) (‖(s : K)‖ ^ a) = -2 * a - 1 := by
  have hc : (-1 : K) ^ a * (s : K) ^ (-(a ^ 2)) ≠ 0 :=
    mul_ne_zero (zpow_ne_zero _ (by norm_num)) (zpow_ne_zero _ s.ne_zero)
  have h := Entire.lo_scale (s ^ a) (thetaDd t) 1
  rw [mul_one, Units.val_zpow_eq_zpow_val, norm_zpow, scale_thetaDd t hs,
    Entire.lo_smul_mono_mul hc _ (thetaDd_ne_zero t) one_pos, coeff_thetaDd,
    lo_thetaDd_one] at h
  omega

/-- The highest dominant index of `Θ̈` on the circle `|Ü| = ‖q‖^{a/2}` is `-2a + 1`: the circle
carries two zeros (the cusps `±q^{a/2}`). -/
theorem hi_thetaDd {s : Kˣ} (hs : (s : K) ^ 2 = t.q) (a : ℤ) :
    hi (thetaDdCoeff t) (‖(s : K)‖ ^ a) = -2 * a + 1 := by
  have hc : (-1 : K) ^ a * (s : K) ^ (-(a ^ 2)) ≠ 0 :=
    mul_ne_zero (zpow_ne_zero _ (by norm_num)) (zpow_ne_zero _ s.ne_zero)
  have h := Entire.hi_scale (s ^ a) (thetaDd t) 1
  rw [mul_one, Units.val_zpow_eq_zpow_val, norm_zpow, scale_thetaDd t hs,
    Entire.hi_smul_mono_mul hc _ (thetaDd_ne_zero t) one_pos, coeff_thetaDd,
    hi_thetaDd_one] at h
  omega

end Theta

end Iut.Frobenioid.BAn
