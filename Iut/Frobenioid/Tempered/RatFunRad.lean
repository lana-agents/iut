/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.Tempered.RatFunMero
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# The radical layer: coverings ramified at the cusps (MR18 T8, route B-an)

In [EtTh] Example 3.9(iii) the divisor monoid `Φ_W` is the *perfection* of `Φ₀` over all tempered
coverings, including those ramified at the cusps (e.g. the coverings on which the `l`-th roots
of the theta function of I1 Example 3.2(ii) / [EtTh] Theorem 5.7 live). Up to constants, the
functions on such coverings are **radicals** `y`, `yⁿ = x ∈ Frac E(K)`, of meromorphic functions on
the elliptic universal combinatorial covering `𝔾_m^an`. This file models them inside an algebraic
closure of `Mero K = Frac E(K)` and extends the divisor `ℚ`-linearly:

* `Mero.IsRad K y`: `y ∈ R ⊇ Mero K` has a power `yⁿ` (`n ≥ 1`) in `Mero K`;
* `Mero.rord y α = ord_α(yⁿ)/n ∈ ℚ` and `Mero.rgn K y r = |yⁿ|_r^{1/n}` (independent of `n`:
  `rord_eq`, `rgn_eq`), multiplicative (`rord_mul`, `rgn_mul`), extending `ord`, `gn`.

## Main results (over an algebraically closed complete ultrametric `K`)

* `Mero.rad_ker_iff`: **[EtTh] Proposition 3.4(ii) on the radical layer**: a radical with trivial
  divisor is a scalar in `O_K^×` (roots of unity of `R` lie in `K`,
  `exists_eq_of_pow_eq_one`); `Mero.rad_eff_iff`: effective divisor iff scalar in `O_K ∖ {0}`.
* `Mero.exists_rad_root`: every `x ≠ 0` has `n`-th roots in the radical layer, with divisor
  `div(x)/n`; `Mero.exists_thetaDd_root`: an `l`-th root of `Θ̈` has order `1/l` at each cusp
  `±q^{a/2}` and Gauss norm `|Θ̈|_r^{1/l}` (I1 Example 3.2(ii) at the level of divisors).
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace Iut.Frobenioid.BAn

open Polynomial TateCurvesTheta

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]

namespace Mero

lemma gn_pow (x : Mero K) {r : ℝ} (hr : 0 < r) (N : ℕ) : gn (x ^ N) r = gn x r ^ N := by
  induction N with
  | zero =>
    rw [pow_zero, pow_zero, ← map_one (algebraMap (Entire K) (Mero K)), gn_ofE _ hr,
      ← map_one (algebraMap K (Entire K)), Entire.gn_algebraMap 1 hr, norm_one]
  | succ N ih => rw [pow_succ, gn_mul _ _ hr, ih, pow_succ]

lemma gn_pos {x : Mero K} (hx : x ≠ 0) {r : ℝ} (hr : 0 < r) : 0 < gn x r :=
  div_pos (gnorm_pos (Entire.isEntire_coeff _) (Entire.coeff_ne_zero (num_ne_zero hx)) hr)
    (gnorm_pos (Entire.isEntire_coeff _) (Entire.coeff_ne_zero (den_ne_zero x)) hr)

/-! The radical layer lives in any field `R` containing `Mero K` (algebraically closed where
roots are taken, e.g. `AlgebraicClosure (Mero K)`). -/

variable {R : Type*} [Field R] [Algebra (Mero K) R]

variable (R) in
/-- The embedding `Mero K → R` (a plain function, to keep coercions out of the statements). -/
def ι (x : Mero K) : R := algebraMap (Mero K) R x

lemma ι_injective : Function.Injective (ι (K := K) R) := (algebraMap (Mero K) R).injective

lemma ι_zero : ι R (0 : Mero K) = 0 := map_zero (algebraMap (Mero K) R)

lemma ι_mul (x y : Mero K) : ι R (x * y) = ι R x * ι R y := map_mul (algebraMap (Mero K) R) x y

lemma ι_pow (x : Mero K) (n : ℕ) : ι R (x ^ n) = ι R x ^ n :=
  map_pow (algebraMap (Mero K) R) x n

lemma ι_ne_zero {x : Mero K} (hx : x ≠ 0) : ι R x ≠ 0 := fun h =>
  hx (ι_injective (R := R) (h.trans ι_zero.symm))

variable (K) in
/-- `y` is a **radical**: some power `yⁿ`, `n ≥ 1`, lies in `Mero K`. -/
abbrev IsRad (y : R) : Prop := ∃ n : ℕ, 0 < n ∧ ∃ x : Mero K, ι R x = y ^ n

open Classical in
/-- The **order of a radical** at `α`: `ord_α(yⁿ)/n ∈ ℚ`. -/
def rord (y : R) (α : Kˣ) : ℚ :=
  if h : IsRad K y then (ord h.choose_spec.2.choose α : ℚ) / h.choose else 0

open Classical in
variable (K) in
/-- The **Gauss norm of a radical** on `|U| = r`: `|yⁿ|_r^{1/n}`. -/
def rgn (y : R) (r : ℝ) : ℝ :=
  if h : IsRad K y then gn h.choose_spec.2.choose r ^ ((1 : ℝ) / h.choose) else 0

lemma ne_zero_of_ι_eq {y : R} (hy : y ≠ 0) {n : ℕ} {x : Mero K} (hx : ι R x = y ^ n) :
    x ≠ 0 := by
  rintro rfl; rw [ι_zero] at hx; exact pow_ne_zero n hy hx.symm

/-- Two representations of a radical are compatible: `x^m = x'^n`. -/
lemma pow_eq_pow_of_ι_eq {y : R} {n m : ℕ} {x x' : Mero K} (hx : ι R x = y ^ n)
    (hx' : ι R x' = y ^ m) : x ^ m = x' ^ n :=
  (ι_injective (K := K) (R := R)) (by rw [ι_pow, ι_pow, hx, hx', ← pow_mul, ← pow_mul, mul_comm])

lemma rord_eq {y : R} (hy : y ≠ 0) {n : ℕ} (hn : 0 < n) {x : Mero K} (hx : ι R x = y ^ n)
    (α : Kˣ) : rord y α = (ord x α : ℚ) / n := by
  have h : IsRad K y := ⟨n, hn, x, hx⟩
  rw [rord, dif_pos h]
  have hm := h.choose_spec.1
  have hx' := h.choose_spec.2.choose_spec
  have e := pow_eq_pow_of_ι_eq hx hx'
  have h1 := congrArg (fun z => ord z α) e
  rw [ord_pow (ne_zero_of_ι_eq hy hx), ord_pow (ne_zero_of_ι_eq hy hx')] at h1
  have hm0 : ((h.choose : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [div_eq_div_iff hm0 hn0]
  have : ((h.choose * ord x α : ℤ) : ℚ) = ((n * ord h.choose_spec.2.choose α : ℤ) : ℚ) := by
    rw [h1]
  push_cast at this
  linarith

/-- `a^m = b^n` with `a, b > 0` gives `a^{1/n} = b^{1/m}`. -/
lemma rpow_inv_eq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (h : a ^ m = b ^ n) : a ^ ((1 : ℝ) / n) = b ^ ((1 : ℝ) / m) := by
  have hk : n * m ≠ 0 := Nat.mul_ne_zero hn.ne' hm.ne'
  refine (pow_left_inj₀ (Real.rpow_nonneg ha.le _) (Real.rpow_nonneg hb.le _) hk).mp ?_
  rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul ha.le, ← Real.rpow_mul hb.le]
  have e1 : (1 : ℝ) / n * ((n * m : ℕ) : ℝ) = m := by
    push_cast; field_simp
  have e2 : (1 : ℝ) / m * ((n * m : ℕ) : ℝ) = n := by
    push_cast; field_simp
  rw [e1, e2, Real.rpow_natCast, Real.rpow_natCast, h]

lemma rgn_eq {y : R} (hy : y ≠ 0) {n : ℕ} (hn : 0 < n) {x : Mero K} (hx : ι R x = y ^ n)
    {r : ℝ} (hr : 0 < r) : rgn K y r = gn x r ^ ((1 : ℝ) / n) := by
  have h : IsRad K y := ⟨n, hn, x, hx⟩
  rw [rgn, dif_pos h]
  have hm := h.choose_spec.1
  have hx' := h.choose_spec.2.choose_spec
  have e := pow_eq_pow_of_ι_eq hx hx'
  have h1 := congrArg (fun z => gn z r) e
  rw [gn_pow _ hr, gn_pow _ hr] at h1
  exact (rpow_inv_eq (gn_pos (ne_zero_of_ι_eq hy hx) hr)
    (gn_pos (ne_zero_of_ι_eq hy hx') hr) hn hm h1).symm

lemma isRad_ι (x : Mero K) : IsRad K (ι R x) := ⟨1, one_pos, x, (pow_one _).symm⟩

lemma rord_ι {x : Mero K} (hx : x ≠ 0) (α : Kˣ) : rord (ι R x) α = ord x α := by
  rw [rord_eq (ι_ne_zero hx) one_pos (pow_one _).symm]; simp

lemma rgn_ι {x : Mero K} (hx : x ≠ 0) {r : ℝ} (hr : 0 < r) : rgn K (ι R x) r = gn x r := by
  rw [rgn_eq (ι_ne_zero hx) one_pos (pow_one _).symm hr]; simp

lemma IsRad.mul {y z : R} (hy : IsRad K y) (hz : IsRad K z) : IsRad K (y * z) := by
  obtain ⟨n, hn, x, hx⟩ := hy
  obtain ⟨m, hm, x', hx'⟩ := hz
  exact ⟨n * m, Nat.mul_pos hn hm, x ^ m * x' ^ n, by
    rw [ι_mul, ι_pow, ι_pow, hx, hx', mul_pow, ← pow_mul, ← pow_mul, mul_comm m n]⟩

/-- The order of radicals is additive. -/
theorem rord_mul {y z : R} (hy0 : y ≠ 0) (hz0 : z ≠ 0) (hy : IsRad K y) (hz : IsRad K z)
    (α : Kˣ) : rord (y * z) α = rord y α + rord z α := by
  obtain ⟨n, hn, x, hx⟩ := hy
  obtain ⟨m, hm, x', hx'⟩ := hz
  have hx0 := ne_zero_of_ι_eq hy0 hx
  have hx0' := ne_zero_of_ι_eq hz0 hx'
  have e : ι R (x ^ m * x' ^ n) = (y * z) ^ (n * m) := by
    rw [ι_mul, ι_pow, ι_pow, hx, hx', mul_pow, ← pow_mul, ← pow_mul, mul_comm m n]
  rw [rord_eq (mul_ne_zero hy0 hz0) (Nat.mul_pos hn hm) e, rord_eq hy0 hn hx, rord_eq hz0 hm hx',
    ord_mul (pow_ne_zero _ hx0) (pow_ne_zero _ hx0'), ord_pow hx0, ord_pow hx0']
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  push_cast
  field_simp

/-- The Gauss norm of radicals is multiplicative. -/
theorem rgn_mul {y z : R} (hy0 : y ≠ 0) (hz0 : z ≠ 0) (hy : IsRad K y) (hz : IsRad K z)
    {r : ℝ} (hr : 0 < r) : rgn K (y * z) r = rgn K y r * rgn K z r := by
  obtain ⟨n, hn, x, hx⟩ := hy
  obtain ⟨m, hm, x', hx'⟩ := hz
  have hx0 := ne_zero_of_ι_eq hy0 hx
  have hx0' := ne_zero_of_ι_eq hz0 hx'
  have e : ι R (x ^ m * x' ^ n) = (y * z) ^ (n * m) := by
    rw [ι_mul, ι_pow, ι_pow, hx, hx', mul_pow, ← pow_mul, ← pow_mul, mul_comm m n]
  have ha := gn_pos hx0 hr
  have hb := gn_pos hx0' hr
  rw [rgn_eq (mul_ne_zero hy0 hz0) (Nat.mul_pos hn hm) e hr, rgn_eq hy0 hn hx hr,
    rgn_eq hz0 hm hx' hr, gn_mul _ _ hr, gn_pow _ hr, gn_pow _ hr,
    Real.mul_rpow (pow_nonneg ha.le _) (pow_nonneg hb.le _), ← Real.rpow_natCast,
    ← Real.rpow_natCast, ← Real.rpow_mul ha.le, ← Real.rpow_mul hb.le]
  congr 2
  · push_cast; field_simp
  · push_cast; field_simp

section AlgClosed

variable [IsAlgClosed K]

/-- **Roots of unity of `R` are scalars**: they lie in the algebraically closed `K`. -/
theorem exists_eq_of_pow_eq_one {ζ : R} {n : ℕ} (hn : 0 < n) (hζ : ζ ^ n = 1) :
    ∃ z : K, z ^ n = 1 ∧ ι R (const z) = ζ := by
  obtain ⟨f, hfdef⟩ : ∃ f : K →+* R,
      f = (algebraMap (Mero K) R).comp
        ((algebraMap (Entire K) (Mero K)).comp (algebraMap K (Entire K))) := ⟨_, rfl⟩
  have hf : Function.Injective f := by
    rw [hfdef]
    exact (ι_injective (K := K) (R := R)).comp
      (ofE_injective.comp (algebraMap K (Entire K)).injective)
  obtain ⟨p, hpdef⟩ : ∃ p : K[X], p = X ^ n - 1 := ⟨_, rfl⟩
  have hp : p ≠ 0 := by
    rw [hpdef, ← C_1]; exact X_pow_sub_C_ne_zero hn (1 : K)
  have hroots := roots_map_of_injective_of_card_eq_natDegree hf
    (IsAlgClosed.splits p).natDegree_eq_card_roots.symm
  have hmem : ζ ∈ (p.map f).roots := by
    rw [mem_roots_map hp, hpdef]
    simp [hζ]
  rw [← hroots, Multiset.mem_map] at hmem
  obtain ⟨z, hz, hzζ⟩ := hmem
  refine ⟨z, ?_, by rw [← hzζ, hfdef]; rfl⟩
  rw [mem_roots hp, hpdef] at hz
  simpa [sub_eq_zero] using hz

lemma norm_eq_one_of_pow_eq_one {z : K} {n : ℕ} (hn : 0 < n) (hz : z ^ n = 1) : ‖z‖ = 1 := by
  have h : ‖z‖ ^ n = 1 := by rw [← norm_pow, hz, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg z) hn.ne').mp h

/-- A radical whose `n`-th power is a scalar `c = dⁿ` is the scalar `ζ·d`. -/
lemma eq_const_of_pow_eq_const {y : R} {n : ℕ} (hn : 0 < n) {c : K}
    (hy : ι R (const c) = y ^ n) (hc : c ≠ 0) :
    ∃ e : K, e ^ n = c ∧ y = ι R (const e) := by
  obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq c hn
  have hd0 : d ≠ 0 := by rintro rfl; rw [zero_pow hn.ne'] at hd; exact hc hd.symm
  have hD : ι R (const d) ≠ 0 := ι_ne_zero (const_ne_zero hd0)
  have hC : ι R (const c) ≠ 0 := ι_ne_zero (const_ne_zero hc)
  have hDn : ι R (const d) ^ n = ι R (const c) := by
    rw [← ι_pow, ← const_pow, hd]
  have hζ : (y / ι R (const d)) ^ n = 1 := by
    rw [div_pow, ← hy, hDn, div_self hC]
  obtain ⟨z, hz, hzζ⟩ := exists_eq_of_pow_eq_one (K := K) hn hζ
  refine ⟨z * d, by rw [mul_pow, hz, one_mul, hd], ?_⟩
  rw [const_mul, ι_mul, hzζ,
    div_mul_cancel₀ _ hD]

/-- **[EtTh] Proposition 3.4(ii) on the radical layer, the kernel**: a radical with trivial
divisor (order `0` at every point, Gauss norm `1` on the component circles `|U| = ‖q‖^a`) is a
scalar of norm `1`, and conversely. -/
theorem rad_ker_iff {y : R} (hy0 : y ≠ 0) (hy : IsRad K y) {q : K} (hq0 : 0 < ‖q‖)
    (hq1 : ‖q‖ < 1) :
    ((∀ α : Kˣ, rord y α = 0) ∧ ∀ a : ℤ, rgn K y (‖q‖ ^ a) = 1) ↔
      ∃ c : K, ‖c‖ = 1 ∧ y = ι R (const c) := by
  obtain ⟨n, hn, x, hx⟩ := hy
  have hx0 := ne_zero_of_ι_eq hy0 hx
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  constructor
  · rintro ⟨hord, hgn⟩
    have hordx : ∀ α, ord x α = 0 := fun α => by
      have := hord α
      rw [rord_eq hy0 hn hx, div_eq_zero_iff, or_iff_left hn0] at this
      exact_mod_cast this
    have hgnx : ∀ a : ℤ, gn x (‖q‖ ^ a) = 1 := fun a => by
      have := hgn a
      rw [rgn_eq hy0 hn hx (zpow_pos hq0 a)] at this
      have hpos := gn_pos hx0 (zpow_pos hq0 a)
      have h1 := congrArg (fun t : ℝ => t ^ (n : ℝ)) this
      simp only [Real.one_rpow] at h1
      rwa [← Real.rpow_mul hpos.le, one_div, inv_mul_cancel₀ (by exact_mod_cast hn.ne'),
        Real.rpow_one] at h1
    obtain ⟨c, hc, rfl⟩ := (ker_iff hx0 hq0 hq1).mp ⟨hordx, hgnx⟩
    have hc0 : c ≠ 0 := fun h => by rw [h, norm_zero] at hc; exact zero_ne_one hc
    obtain ⟨e, he, rfl⟩ := eq_const_of_pow_eq_const hn hx hc0
    refine ⟨e, ?_, rfl⟩
    rw [← he, norm_pow] at hc
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg e) hn.ne').mp hc
  · rintro ⟨c, hc, rfl⟩
    have hc0 : c ≠ 0 := fun h => by rw [h, norm_zero] at hc; exact zero_ne_one hc
    have hC : const c ≠ 0 := const_ne_zero hc0
    exact ⟨fun α => by rw [rord_ι (R := R) hC, ord_const hc0, Int.cast_zero],
      fun a => by rw [rgn_ι (R := R) hC (zpow_pos hq0 a), gn_const c (zpow_pos hq0 a), hc]⟩

/-- **[EtTh] Proposition 3.4(ii) on the radical layer, the effective part**: a radical with
effective divisor is a nonzero scalar in `O_K`, and conversely. -/
theorem rad_eff_iff {y : R} (hy0 : y ≠ 0) (hy : IsRad K y) {q : K} (hq0 : 0 < ‖q‖)
    (hq1 : ‖q‖ < 1) :
    ((∀ α : Kˣ, 0 ≤ rord y α) ∧ ∀ a : ℤ, rgn K y (‖q‖ ^ a) ≤ 1) ↔
      ∃ c : K, c ≠ 0 ∧ ‖c‖ ≤ 1 ∧ y = ι R (const c) := by
  obtain ⟨n, hn, x, hx⟩ := hy
  have hx0 := ne_zero_of_ι_eq hy0 hx
  have hnpos : (0 : ℚ) < n := by exact_mod_cast hn
  constructor
  · rintro ⟨hord, hgn⟩
    have hordx : ∀ α, 0 ≤ ord x α := fun α => by
      have := hord α
      rw [rord_eq hy0 hn hx, div_nonneg_iff] at this
      rcases this with ⟨h1, -⟩ | ⟨-, h2⟩
      · exact_mod_cast h1
      · exact absurd h2 (not_le.mpr hnpos)
    have hgnx : ∀ a : ℤ, gn x (‖q‖ ^ a) ≤ 1 := fun a => by
      have := hgn a
      rw [rgn_eq hy0 hn hx (zpow_pos hq0 a)] at this
      have hpos := gn_pos hx0 (zpow_pos hq0 a)
      by_contra hlt
      push Not at hlt
      have := Real.one_lt_rpow hlt (by positivity : (0 : ℝ) < 1 / n)
      linarith
    obtain ⟨c, hc0, hc, rfl⟩ := (eff_iff hx0 hq0 hq1).mp ⟨hordx, hgnx⟩
    obtain ⟨e, he, rfl⟩ := eq_const_of_pow_eq_const hn hx hc0
    refine ⟨e, fun h0 => hc0 (by rw [← he, h0, zero_pow hn.ne']), ?_, rfl⟩
    rw [← he, norm_pow] at hc
    exact (pow_le_one_iff_of_nonneg (norm_nonneg e) hn.ne').mp hc
  · rintro ⟨c, hc0, hc, rfl⟩
    have hC : const c ≠ 0 := const_ne_zero hc0
    exact ⟨fun α => by rw [rord_ι (R := R) hC, ord_const hc0, Int.cast_zero],
      fun a => by rw [rgn_ι (R := R) hC (zpow_pos hq0 a), gn_const c (zpow_pos hq0 a)]; exact hc⟩

/-- **Roots in the radical layer**: every `x ≠ 0` has an `n`-th root `y` with divisor
`div(x)/n`. -/
theorem exists_rad_root [IsAlgClosed R] {x : Mero K} (hx : x ≠ 0) {n : ℕ} (hn : 0 < n) :
    ∃ y : R, y ≠ 0 ∧ IsRad K y ∧ y ^ n = ι R x ∧ (∀ α, rord y α = (ord x α : ℚ) / n) ∧
      ∀ r : ℝ, 0 < r → rgn K y r = gn x r ^ ((1 : ℝ) / n) := by
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (ι R x) hn
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [zero_pow hn.ne'] at hy
    exact hx ((ι_injective (K := K) (R := R)) (hy.symm.trans ι_zero.symm))
  exact ⟨y, hy0, ⟨n, hn, x, hy.symm⟩, hy, fun α => rord_eq hy0 hn hy.symm α,
    fun r hr => rgn_eq hy0 hn hy.symm hr⟩

variable (t : TateParameter K)

/-- **An `l`-th root of `Θ̈`** (I1 Example 3.2(ii), on a covering ramified at the cusps): it has
order `1/l` at each cusp `±q^{a/2}`, order `0` elsewhere, and Gauss norm `|Θ̈|_r^{1/l}`. -/
theorem exists_thetaDd_root [IsAlgClosed R] (h2 : (2 : K) ≠ 0) {s : Kˣ} (hs : (s : K) ^ 2 = t.q)
    {l : ℕ} (hl : 0 < l) :
    ∃ y : R, y ≠ 0 ∧ IsRad K y ∧ y ^ l = ι R (ofE (thetaDd t)) ∧
      (∀ a : ℤ, ∀ α : Kˣ, (α = s ^ a ∨ α = -(s ^ a)) → rord y α = 1 / l) ∧
      (∀ α : Kˣ, (¬ ∃ k : ℤ, (α : K) ^ 2 = (t.q : K) ^ k) → rord y α = 0) ∧
      ∀ a : ℤ, rgn K y (‖(s : K)‖ ^ a) = (‖(s : K)‖ ^ (-(a ^ 2))) ^ ((1 : ℝ) / l) := by
  have hθ := ofE_ne_zero (thetaDd_ne_zero t)
  obtain ⟨y, hy0, hyr, hy, hord, hgn⟩ := exists_rad_root (R := R) hθ hl
  have hs0 : 0 < ‖(s : K)‖ := norm_pos_iff.mpr s.ne_zero
  refine ⟨y, hy0, hyr, hy, fun a α hα => ?_, fun α hα => ?_, fun a => ?_⟩
  · rw [hord, ord_ofE (thetaDd_ne_zero t), ord_thetaDd_cusp t h2 hs a hα]; simp
  · rw [hord, ord_ofE (thetaDd_ne_zero t), ord_thetaDd_of_not_cusp t hα]; simp
  · rw [hgn _ (zpow_pos hs0 a), gn_ofE _ (zpow_pos hs0 a), gn_thetaDd hs a]

end AlgClosed

end Mero

end Iut.Frobenioid.BAn
