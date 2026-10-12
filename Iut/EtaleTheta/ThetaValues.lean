/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.EtaleTheta.Theta
import TateCurvesTheta.Kummer.ThetaValues

/-!
# Theta values at the torsion points and IUT's normalization ([EtTh], §1; IUT I, Ex. 3.2)

Let `s² = q` and `i² = -1` in `K`. The evaluation points of IUT are the points `Ü = i·s^j`
(`j ∈ ℤ`, the labels; `i·s = √-q` in IUT I, Example 3.2(iv)). By the `ℤ`-action formula of
[EtTh], Prop. 1.4(ii) (`etaleTheta_zpow_sqrt_mul`) the theta values at these points are a
Gaussian:
```
Θ̈(i·s^j) = s^{-j²}·Θ̈(i)      (i.e. Θ̈(√-1·q^{j/2}) = q^{-j²/2}·Θ̈(√-1)).
```
IUT I, Example 3.2(ii), (iv) uses the reciprocal of `Θ̈` normalized to the value `1` at `√-1`,
`Θ_v(Ü) = Θ̈(i)/Θ̈(Ü)`, and its `ℓ`-th root: `Θ_v(i·s^j) = s^{j²}`, whose `ℓ`-th roots are the
`μ_ℓ`-orbit of `r^{j²}` for `r^ℓ = s`, i.e. of `q_v^{j²}` with `q_v = r = q^{1/2ℓ}` (IUT II,
Remark 2.5.1: "the `μ_{2ℓ}`-orbit of the theta value `q_v^{j²}`").

## Main results

* `etaleTheta_sqrtNeg_zpow`: `Θ̈(s^j·i) = s^{-j²}·Θ̈(i)`.
* `thetaRatio`, `thetaRatio_eq`, `etaleTheta_ratio`: the `i`-free form
  `s^j θ(q^j)/θ(1) = s^{-j²}`, equal to `Θ̈(s^j i)/Θ̈(i)`.
* `etaleTheta_halfPeriod`: the same Gaussian at the other half-period points, via
  `tate-curves-theta`'s `theta_sqrt_zpow` (`θ(s^{2j-1}) = s^{-j²} θ(s⁻¹)`).
* `thetaV_value`, `pow_eq_thetaV_iff`, `pow_two_mul_eq_thetaV_sq_iff`: IUT's normalized theta
  values and their `ℓ`-th (`2ℓ`-th) roots.
* `kummer_thetaRatio`: the Kummer classes of the normalized theta values are `κ(s)^{-j²}`.
* `normalized_iff`, `normalized_value`: the algebraic core of rigidity of scalar multiples — the
  normalization at `√-1` fixes the scalar multiple up to roots of unity, and then the values
  at all labels are determined up to the same roots of unity.
-/

noncomputable section

namespace Iut.EtaleTheta

open TateCurvesTheta TateCurvesTheta.TateParameter KummerTheory

variable {K : Type*} [NormedField K] (t : TateParameter K)

section Values

variable {s i : Kˣ} (hs : s ^ 2 = t.q) (hi : i ^ 2 = -1)
include hs hi

/-- **The theta values at the evaluation points** ([EtTh], Prop. 1.4(ii); IUT I,
Example 3.2(iv)): `Θ̈(s^j·i) = s^{-j²}·Θ̈(i)`. -/
theorem etaleTheta_sqrtNeg_zpow (j : ℤ) :
    etaleTheta t (s ^ j * i) = (s : K) ^ (-j ^ 2) * etaleTheta t i := by
  rw [etaleTheta_zpow_sqrt_mul t hs, thetaFactor]
  congr 1
  have hi' : (i : K) ^ 2 = -1 := by rw [← Units.val_pow_eq_pow_val, hi, Units.val_neg,
    Units.val_one]
  rw [show (-2 * j : ℤ) = 2 * -j by ring, zpow_mul, zpow_ofNat, hi', mul_right_comm,
    ← zpow_add₀ (neg_ne_zero.2 one_ne_zero), add_neg_cancel, zpow_zero, one_mul]

end Values

/-- The normalized theta value at the label `j`, in a form free of `√-1`:
`s^j·θ(q^j)/θ(1)` (`= Θ̈(s^j i)/Θ̈(i)`, `etaleTheta_ratio`). -/
def thetaRatio (s : Kˣ) (j : ℤ) : K := (s : K) ^ j * t.theta (t.q ^ j) / t.theta 1

/-- `θ(1) ≠ 0` away from characteristic `2`. -/
theorem theta_one_ne_zero [CompleteSpace K] [IsUltrametricDist K] (h2 : (2 : K) ≠ 0) :
    t.theta 1 ≠ 0 := by
  rw [Ne, t.theta_eq_zero_iff]
  rintro ⟨k, hk⟩
  have hk' : (t.q : K) ^ k = -1 := by rw [Units.val_one] at hk; linear_combination hk
  have h2k : (t.q : K) ^ (2 * k) = 1 := by rw [mul_comm, zpow_mul, hk']; norm_num
  by_cases hk0 : k = 0
  · rw [hk0, zpow_zero] at hk'
    exact h2 (by linear_combination hk')
  · exact t.zpow_ne_one (by omega) h2k

/-- **The Gaussian**: `s^j·θ(q^j)/θ(1) = s^{-j²}` for `s² = q`. -/
theorem thetaRatio_eq {s : Kˣ} (hs : s ^ 2 = t.q) (h1 : t.theta 1 ≠ 0) (j : ℤ) :
    thetaRatio t s j = (s : K) ^ (-j ^ 2) := by
  have hs0 : (s : K) ≠ 0 := s.ne_zero
  have hq : t.q ^ j * 1 = t.q ^ j := mul_one _
  have h := t.theta_zpow_q_smul 1 j
  rw [hq] at h
  rw [thetaRatio, h, Units.val_one, one_zpow, mul_one, ← hs, Units.val_pow_eq_pow_val,
    ← zpow_natCast, ← zpow_mul, mul_div_assoc, mul_div_cancel_right₀ _ h1, ← zpow_neg,
    ← zpow_add₀ hs0]
  congr 1
  have := two_mul_thetaExp j
  push_cast
  linear_combination -this

/-- The ratio of theta values at the labels `j` and `0` is the `i`-free `thetaRatio`. -/
theorem etaleTheta_ratio {s i : Kˣ} (hs : s ^ 2 = t.q) (hi : i ^ 2 = -1) (h1 : t.theta 1 ≠ 0)
    (j : ℤ) : etaleTheta t (s ^ j * i) = thetaRatio t s j * etaleTheta t i := by
  have hU : -((s ^ j * i) ^ 2) = t.q ^ j := by
    rw [mul_pow, hi, ← zpow_natCast (s ^ j), ← zpow_mul, mul_comm j, zpow_mul, zpow_natCast,
      hs]
    simp
  have hi1 : -(i ^ 2) = 1 := by rw [hi, neg_neg]
  rw [etaleTheta_def, etaleTheta_def, hU, hi1, thetaRatio]
  field_simp
  simp only [Units.val_mul, Units.val_zpow_eq_zpow_val]
  ring

/-- **The half-period points** (`tate-curves-theta`'s `theta_sqrt_zpow`): for `w² = -s⁻¹`,
`Θ̈(s^j·w) = s^{j-j²}·Θ̈(w)`; here `-(s^j w)² = s^{2j-1}` are the points `√q^{2j-1}`. -/
theorem etaleTheta_halfPeriod {s w : Kˣ} (hs : s ^ 2 = t.q) (hw : w ^ 2 = -s⁻¹) (j : ℤ) :
    etaleTheta t (s ^ j * w) = (s : K) ^ (j - j ^ 2) * etaleTheta t w := by
  have hs0 : (s : K) ≠ 0 := s.ne_zero
  have hU : -((s ^ j * w) ^ 2) = s ^ (2 * j - 1) := by
    rw [mul_pow, hw, ← zpow_natCast (s ^ j), ← zpow_mul, mul_neg, neg_neg, mul_comm j,
      zpow_sub, zpow_one]
    simp
  have hw' : -(w ^ 2) = s⁻¹ := by rw [hw, neg_neg]
  rw [etaleTheta_def, etaleTheta_def, hU, hw', t.theta_sqrt_zpow hs j, zpow_sub₀ hs0]
  simp only [Units.val_mul, Units.val_zpow_eq_zpow_val]
  rw [zpow_neg]
  field_simp

/-! ### IUT's normalized theta function -/

/-- IUT's normalized theta function `Θ_v(Ü) = Θ̈(i)/Θ̈(Ü)` (IUT I, Example 3.2(ii): the
reciprocal of `Θ̈` normalized to `1` at `√-1`). -/
def thetaV (i U : Kˣ) : K := etaleTheta t i / etaleTheta t U

section Normalized

variable {s i : Kˣ} (hs : s ^ 2 = t.q) (hi : i ^ 2 = -1)
include hs hi

/-- `Θ_v(s^j·i) = s^{j²}` (IUT I, Example 3.2(iv): the value at `√-q` is `q^{1/2}`, before
taking `ℓ`-th roots). -/
theorem thetaV_value (hi0 : etaleTheta t i ≠ 0) (j : ℤ) :
    thetaV t i (s ^ j * i) = (s : K) ^ (j ^ 2) := by
  rw [thetaV, etaleTheta_sqrtNeg_zpow t hs hi, zpow_neg]
  have : (s : K) ^ (j ^ 2) ≠ 0 := zpow_ne_zero _ s.ne_zero
  field_simp

/-- **The `ℓ`-th roots of the normalized theta values** (IUT I, Example 3.2(iv); IUT II,
Remark 2.5.1): if `r^ℓ = s` (so `r^{2ℓ} = q`), then `x^ℓ = Θ_v(i·s^j)` iff `x = ζ·r^{j²}` with
`ζ^ℓ = 1`. -/
theorem pow_eq_thetaV_iff (hi0 : etaleTheta t i ≠ 0) {r : Kˣ} {ℓ : ℕ} (hr : r ^ ℓ = s) (j : ℤ)
    (x : K) :
    x ^ ℓ = thetaV t i (s ^ j * i) ↔ ∃ ζ : K, ζ ^ ℓ = 1 ∧ x = ζ * (r : K) ^ (j ^ 2) := by
  have hr0 : (r : K) ^ (j ^ 2) ≠ 0 := zpow_ne_zero _ r.ne_zero
  have hval : thetaV t i (s ^ j * i) = ((r : K) ^ (j ^ 2)) ^ ℓ := by
    rw [thetaV_value t hs hi hi0, ← hr, Units.val_pow_eq_pow_val, ← zpow_natCast, ← zpow_mul,
      ← zpow_natCast, ← zpow_mul, mul_comm]
  rw [hval]
  constructor
  · intro h
    refine ⟨x / (r : K) ^ (j ^ 2), ?_, by field_simp⟩
    rw [div_pow, h, div_self (pow_ne_zero _ hr0)]
  · rintro ⟨ζ, hζ, rfl⟩
    rw [mul_pow, hζ, one_mul]

/-- The `2ℓ`-th root version: `x^{2ℓ} = Θ_v(i·s^j)²` iff `x = ζ·r^{j²}` with `ζ^{2ℓ} = 1` — the
`μ_{2ℓ}`-orbit of `q_v^{j²}` of IUT II, Remark 2.5.1. -/
theorem pow_two_mul_eq_thetaV_sq_iff (hi0 : etaleTheta t i ≠ 0) {r : Kˣ} {ℓ : ℕ}
    (hr : r ^ ℓ = s) (j : ℤ) (x : K) :
    x ^ (2 * ℓ) = thetaV t i (s ^ j * i) ^ 2 ↔
      ∃ ζ : K, ζ ^ (2 * ℓ) = 1 ∧ x = ζ * (r : K) ^ (j ^ 2) := by
  have hr0 : (r : K) ^ (j ^ 2) ≠ 0 := zpow_ne_zero _ r.ne_zero
  have hval : thetaV t i (s ^ j * i) ^ 2 = ((r : K) ^ (j ^ 2)) ^ (2 * ℓ) := by
    rw [thetaV_value t hs hi hi0, ← hr, Units.val_pow_eq_pow_val, ← zpow_natCast, ← zpow_mul,
      ← zpow_natCast, ← zpow_mul, ← zpow_natCast, ← zpow_mul]
    congr 1
    push_cast
    ring
  rw [hval]
  constructor
  · intro h
    refine ⟨x / (r : K) ^ (j ^ 2), ?_, by field_simp⟩
    rw [div_pow, h, div_self (pow_ne_zero _ hr0)]
  · rintro ⟨ζ, hζ, rfl⟩
    rw [mul_pow, hζ, one_mul]

end Normalized

/-! ### Kummer classes of the normalized theta values -/

/-- **Kummer classes of the theta values at the labels**: for a unit `u` with
`u = s^j θ(q^j)/θ(1)` (the normalized value `Θ̈(s^j i)/Θ̈(i)`), `κ(u) = κ(s)^{-j²}` in
`H¹_cont(Gal(Ω/K), μ_n)`, for every `n` — the class of `q^{-j²/2}`. -/
theorem kummer_thetaRatio (n : ℕ) (Ω : Type*) [Field Ω] [Algebra K Ω] [Algebra.IsIntegral K Ω]
    [HasKummerRoots n K Ω] {s : Kˣ} (hs : s ^ 2 = t.q) (h1 : t.theta 1 ≠ 0) (j : ℤ) (u : Kˣ)
    (hu : (u : K) = thetaRatio t s j) :
    kummer n K Ω u = kummer n K Ω s ^ (-j ^ 2) := by
  have : u = s ^ (-j ^ 2) := by
    ext
    rw [hu, thetaRatio_eq t hs h1, Units.val_zpow_eq_zpow_val]
  rw [this, map_zpow]

/-! ### Scalar multiples: the algebraic core of rigidity of scalar multiples -/

/-- The scalar multiples `c·Θ̈` whose value at `√-1` is an `m`-th root of unity are exactly
the `c ∈ μ_m·Θ̈(i)⁻¹` ([EtTh], Def. 1.9, Thm. 1.10: classes of standard type). -/
theorem normalized_iff {i : Kˣ} (hi0 : etaleTheta t i ≠ 0) (m : ℕ) (c : K) :
    (c * etaleTheta t i) ^ m = 1 ↔ ∃ ζ : K, ζ ^ m = 1 ∧ c = ζ * (etaleTheta t i)⁻¹ := by
  constructor
  · intro h
    exact ⟨c * etaleTheta t i, h, by field_simp⟩
  · rintro ⟨ζ, hζ, rfl⟩
    rw [mul_assoc, inv_mul_cancel₀ hi0, mul_one, hζ]

/-- For a normalized scalar multiple (`(c·Θ̈(i))^m = 1`), the values at all labels are
determined up to `μ_m`: `(c·Θ̈(s^j i))^m = (s^{-j²})^m`. -/
theorem normalized_value {s i : Kˣ} (hs : s ^ 2 = t.q) (hi : i ^ 2 = -1) {m : ℕ} {c : K}
    (hc : (c * etaleTheta t i) ^ m = 1) (j : ℤ) :
    (c * etaleTheta t (s ^ j * i)) ^ m = ((s : K) ^ (-j ^ 2)) ^ m := by
  rw [etaleTheta_sqrtNeg_zpow t hs hi, mul_left_comm, mul_pow, hc, mul_one]

end Iut.EtaleTheta
