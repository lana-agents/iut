/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.Tempered.RatFunAnnulus

/-!
# Meromorphic functions on `𝔾_m^an` and their divisors (MR18 T8, route B-an)

The meromorphic functions on the universal combinatorial covering `𝔾_m^an` of [EtTh] §3 (for the
coverings of Example 3.9 unramified over the cusps) are modelled by the fraction field
`Mero K = Frac E(K)` of the ring of entire Laurent series. The divisor of `x = g/h` has two parts:

* the **orders at points** `Mero.ord x α = ord_α g - ord_α h ∈ ℤ` (the cusps are among the points);
* the **Gauss norms** `Mero.gn x r = |g|_r / |h|_r` on the circles `|U| = r`; on the component
  circles `|U| = ‖q‖^a` these are the orders along the irreducible components of the special
  fibre (the non-cuspidal part of the log-divisor of [EtTh] Definition 3.1).

Both are independent of the representation (`Mero.ord_div`, `Mero.gn_div`) and multiplicative.

## Main results (over an algebraically closed complete ultrametric `K`)

* `Mero.exists_entire_of_ord_nonneg`: a meromorphic function without poles at points is entire
  (cancellation of common zeros, `Entire.dvd_of_ord_le`).
* `Mero.ker_iff`: **[EtTh] Proposition 3.4(ii), `O^× ≅ Ker(B → Φ^gp)`**: the divisor of
  `x ≠ 0` is trivial (no zeros or poles, Gauss norm `1` on all component circles) iff `x ∈ O_K^×`.
* `Mero.eff_iff`: **[EtTh] Proposition 3.4(ii), `O^⊿ ≅ B ×_{Φ^gp} Φ`**: the divisor of `x ≠ 0` is
  effective iff `x ∈ O_K ∖ {0}` (the meromorphic form of Proposition 3.2(ii)).
* `Mero.const_injective`: **`K^× ≅ F₀`**, the constants embed.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace Iut.Frobenioid.BAn

open Polynomial TateCurvesTheta

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]

variable (K) in
/-- **Meromorphic functions on `𝔾_m^an`**: the fraction field of `E(K)`. -/
abbrev Mero := FractionRing (Entire K)

lemma Entire.mono_pow (j : ℤ) (N : ℕ) : (Entire.mono j : Entire K) ^ N = Entire.mono (N * j) := by
  induction N with
  | zero => simp [Entire.mono_zero]
  | succ N ih => rw [pow_succ, ih, ← Entire.mono_add]; congr 1; push_cast; ring

namespace Mero

/-- The image of an entire series. -/
abbrev ofE (f : Entire K) : Mero K := algebraMap (Entire K) (Mero K) f

/-- The scalar meromorphic function `c`. -/
abbrev const (c : K) : Mero K := ofE (algebraMap K (Entire K) c)

lemma ofE_injective : Function.Injective (ofE (K := K)) := IsFractionRing.injective _ _

lemma ofE_zero : ofE (0 : Entire K) = 0 := map_zero _

lemma ofE_one : ofE (1 : Entire K) = 1 := map_one _

lemma ofE_mul (f g : Entire K) : ofE (f * g) = ofE f * ofE g := map_mul _ _ _

lemma ofE_pow (f : Entire K) (n : ℕ) : ofE (f ^ n) = ofE f ^ n := map_pow _ _ _

lemma const_mul (a b : K) : const (a * b) = const a * const b := by
  change ofE (algebraMap K (Entire K) (a * b)) = ofE (algebraMap K (Entire K) a) *
    ofE (algebraMap K (Entire K) b)
  rw [map_mul, ofE_mul]

lemma const_pow (a : K) (n : ℕ) : const (a ^ n) = const a ^ n := by
  change ofE (algebraMap K (Entire K) (a ^ n)) = ofE (algebraMap K (Entire K) a) ^ n
  rw [map_pow, ofE_pow]

lemma ofE_ne_zero {f : Entire K} (hf : f ≠ 0) : ofE f ≠ 0 :=
  fun h => hf (ofE_injective (h.trans (map_zero _).symm))

/-- **The constants embed** (`K^× ≅ F₀`). -/
lemma const_injective : Function.Injective (const (K := K)) :=
  ofE_injective.comp (algebraMap K (Entire K)).injective

lemma const_ne_zero {c : K} (hc : c ≠ 0) : const c ≠ 0 :=
  ofE_ne_zero ((map_ne_zero_iff _ (algebraMap K (Entire K)).injective).mpr hc)

lemma exists_rep (x : Mero K) : ∃ g h : Entire K, h ≠ 0 ∧ x = ofE g / ofE h := by
  obtain ⟨g, h, hh, rfl⟩ := IsFractionRing.div_surjective (A := Entire K) x
  exact ⟨g, h, nonZeroDivisors.ne_zero hh, rfl⟩

/-- A chosen numerator. -/
def num (x : Mero K) : Entire K := (exists_rep x).choose

/-- A chosen denominator. -/
def den (x : Mero K) : Entire K := (exists_rep x).choose_spec.choose

lemma den_ne_zero (x : Mero K) : den x ≠ 0 := (exists_rep x).choose_spec.choose_spec.1

lemma eq_num_div_den (x : Mero K) : x = ofE (num x) / ofE (den x) :=
  (exists_rep x).choose_spec.choose_spec.2

/-- Two representations of the same function are cross-equal. -/
lemma mul_eq_mul_of_div_eq {g h g' h' : Entire K} (hh : h ≠ 0) (hh' : h' ≠ 0)
    (e : ofE g / ofE h = ofE g' / ofE h') : g * h' = g' * h := by
  rw [div_eq_div_iff (ofE_ne_zero hh) (ofE_ne_zero hh')] at e
  exact ofE_injective (by rw [ofE_mul, ofE_mul]; exact e)

lemma num_ne_zero {x : Mero K} (hx : x ≠ 0) : num x ≠ 0 := by
  intro h; apply hx; rw [eq_num_div_den x, h, ofE_zero, zero_div]

/-- **The order of `x` at the point `α`.** -/
def ord (x : Mero K) (α : Kˣ) : ℤ := (BAn.ord (num x) α : ℤ) - BAn.ord (den x) α

/-- **The Gauss norm of `x` on the circle `|U| = r`.** -/
def gn (x : Mero K) (r : ℝ) : ℝ := Entire.gn (num x) r / Entire.gn (den x) r

lemma ord_div {g h : Entire K} (hg : g ≠ 0) (hh : h ≠ 0) (α : Kˣ) :
    ord (ofE g / ofE h) α = (BAn.ord g α : ℤ) - BAn.ord h α := by
  set x := ofE g / ofE h
  have hx : x ≠ 0 := div_ne_zero (ofE_ne_zero hg) (ofE_ne_zero hh)
  have e := mul_eq_mul_of_div_eq (den_ne_zero x) hh (eq_num_div_den x).symm
  have := congrArg (fun f => BAn.ord f α) e
  rw [BAn.ord_mul (num_ne_zero hx) hh, BAn.ord_mul hg (den_ne_zero x)] at this
  rw [ord]
  omega

lemma gn_div {g h : Entire K} (hh : h ≠ 0) {r : ℝ} (hr : 0 < r) :
    gn (ofE g / ofE h) r = Entire.gn g r / Entire.gn h r := by
  set x := ofE g / ofE h
  have e := mul_eq_mul_of_div_eq (den_ne_zero x) hh (eq_num_div_den x).symm
  have := congrArg (fun f => Entire.gn f r) e
  rw [Entire.gn_mul _ _ hr, Entire.gn_mul _ _ hr] at this
  have h1 := gnorm_pos (Entire.isEntire_coeff h) (Entire.coeff_ne_zero hh) hr
  have h2 := gnorm_pos (Entire.isEntire_coeff _) (Entire.coeff_ne_zero (den_ne_zero x)) hr
  rw [gn, div_eq_div_iff h2.ne' h1.ne']
  exact this

lemma ofE_eq_div (f : Entire K) : ofE f = ofE f / ofE 1 := by rw [ofE_one, div_one]

lemma ord_ofE {f : Entire K} (hf : f ≠ 0) (α : Kˣ) : ord (ofE f) α = BAn.ord f α := by
  rw [ofE_eq_div, ord_div hf one_ne_zero]
  have : BAn.ord (1 : Entire K) α = 0 :=
    (ord_eq_zero_iff one_ne_zero α).mpr (by simp)
  rw [this]; simp

lemma gn_ofE (f : Entire K) {r : ℝ} (hr : 0 < r) : gn (ofE f) r = Entire.gn f r := by
  rw [ofE_eq_div, gn_div one_ne_zero hr, ← map_one (algebraMap K (Entire K)),
    Entire.gn_algebraMap 1 hr, norm_one, div_one]

lemma ord_mul {x y : Mero K} (hx : x ≠ 0) (hy : y ≠ 0) (α : Kˣ) :
    ord (x * y) α = ord x α + ord y α := by
  have hx' := num_ne_zero hx
  have hy' := num_ne_zero hy
  have e : x * y = ofE (num x * num y) / ofE (den x * den y) := by
    conv_lhs => rw [eq_num_div_den x, eq_num_div_den y]
    rw [ofE_mul, ofE_mul, div_mul_div_comm]
  rw [e, ord_div (mul_ne_zero hx' hy') (mul_ne_zero (den_ne_zero x) (den_ne_zero y)),
    BAn.ord_mul hx' hy', BAn.ord_mul (den_ne_zero x) (den_ne_zero y), ord, ord]
  push_cast; ring

lemma gn_mul (x y : Mero K) {r : ℝ} (hr : 0 < r) : gn (x * y) r = gn x r * gn y r := by
  have e : x * y = ofE (num x * num y) / ofE (den x * den y) := by
    conv_lhs => rw [eq_num_div_den x, eq_num_div_den y]
    rw [ofE_mul, ofE_mul, div_mul_div_comm]
  rw [e, gn_div (mul_ne_zero (den_ne_zero x) (den_ne_zero y)) hr, Entire.gn_mul _ _ hr,
    Entire.gn_mul _ _ hr, gn, gn, mul_div_mul_comm]

lemma ord_one (α : Kˣ) : ord (1 : Mero K) α = 0 := by
  rw [← map_one (algebraMap (Entire K) (Mero K)), ord_ofE one_ne_zero,
    (ord_eq_zero_iff one_ne_zero α).mpr (by simp)]
  rfl

lemma ord_pow {x : Mero K} (hx : x ≠ 0) (N : ℕ) (α : Kˣ) : ord (x ^ N) α = N * ord x α := by
  induction N with
  | zero => simp [ord_one]
  | succ N ih => rw [pow_succ, ord_mul (pow_ne_zero _ hx) hx, ih]; push_cast; ring

lemma ord_const {c : K} (hc : c ≠ 0) (α : Kˣ) : ord (const c) α = 0 := by
  have hc' : algebraMap K (Entire K) c ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap K (Entire K)).injective).mpr hc
  rw [ord_ofE hc', Nat.cast_eq_zero, ord_eq_zero_iff hc' α]
  exact hc

lemma gn_const (c : K) {r : ℝ} (hr : 0 < r) : gn (const c) r = ‖c‖ := by
  rw [gn_ofE _ hr, Entire.gn_algebraMap c hr]

section AlgClosed

variable [IsAlgClosed K]

/-- **No poles at points ⇒ entire** (cancellation of the common zeros of numerator and
denominator). -/
theorem exists_entire_of_ord_nonneg {x : Mero K} (hx : x ≠ 0) (h : ∀ α, 0 ≤ ord x α) :
    ∃ f : Entire K, f ≠ 0 ∧ x = ofE f := by
  have hn := num_ne_zero hx
  have hd := den_ne_zero x
  have hord : ∀ α, BAn.ord (den x) α ≤ BAn.ord (num x) α := fun α => by
    have := h α; rw [ord] at this; omega
  obtain ⟨u, hu⟩ := Entire.dvd_of_ord_le hd hord
  refine ⟨u, fun h0 => hn (by rw [hu, h0, mul_zero]), ?_⟩
  rw [eq_num_div_den x, hu, ofE_mul, mul_div_cancel_left₀ _ (ofE_ne_zero hd)]

/-- **[EtTh] Proposition 3.4(ii), `O^⊿ ≅ B ×_{Φ^gp} Φ`** (and the meromorphic form of
Proposition 3.2(ii)): the divisor of `x ≠ 0` is effective (no poles at points, Gauss norm `≤ 1` on
the component circles `|U| = ‖q‖^a`) iff `x` is a nonzero scalar in `O_K`. -/
theorem eff_iff {x : Mero K} (hx : x ≠ 0) {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    ((∀ α, 0 ≤ ord x α) ∧ ∀ a : ℤ, gn x (‖q‖ ^ a) ≤ 1) ↔
      ∃ c : K, c ≠ 0 ∧ ‖c‖ ≤ 1 ∧ x = const c := by
  constructor
  · rintro ⟨hord, hgn⟩
    obtain ⟨f, hf, rfl⟩ := exists_entire_of_ord_nonneg hx hord
    obtain ⟨c, hc, rfl⟩ := Entire.eq_algebraMap_of_gnorm_qpow_le f hq0 hq1 fun a => by
      rw [← gn_ofE f (zpow_pos hq0 a)]; exact hgn a
    exact ⟨c, fun h0 => hf (by rw [h0, map_zero]), hc, rfl⟩
  · rintro ⟨c, hc0, hc, rfl⟩
    exact ⟨fun α => (ord_const hc0 α).symm.le, fun a => by
      rw [gn_const c (zpow_pos hq0 a)]; exact hc⟩

/-- **[EtTh] Proposition 3.4(ii), the kernel of the divisor map**: a meromorphic function on
`𝔾_m^an` with trivial divisor (no zeros or poles at points, Gauss norm `1` on all component
circles) is a scalar of norm `1`, i.e. an element of `O_K^×`, and conversely. -/
theorem ker_iff {x : Mero K} (hx : x ≠ 0) {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    ((∀ α, ord x α = 0) ∧ ∀ a : ℤ, gn x (‖q‖ ^ a) = 1) ↔
      ∃ c : K, ‖c‖ = 1 ∧ x = const c := by
  constructor
  · rintro ⟨hord, hgn⟩
    obtain ⟨f, hf, rfl⟩ := exists_entire_of_ord_nonneg hx fun α => (hord α).symm.le
    have hz : ∀ u : Kˣ, (f : Kˣ → K) u ≠ 0 := fun u => by
      have := hord u
      rw [ord_ofE hf, Nat.cast_eq_zero] at this
      exact (ord_eq_zero_iff hf u).mp this
    obtain ⟨c, hc, rfl⟩ := eq_algebraMap_of_no_zero hf hz hq0 hq1 fun a => by
      rw [← gn_ofE f (zpow_pos hq0 a)]; exact hgn a
    exact ⟨c, hc, rfl⟩
  · rintro ⟨c, hc, rfl⟩
    have hc0 : c ≠ 0 := fun h => by rw [h, norm_zero] at hc; exact zero_ne_one hc
    exact ⟨fun α => ord_const hc0 α, fun a => by rw [gn_const c (zpow_pos hq0 a), hc]⟩

end AlgClosed

end Mero

end Iut.Frobenioid.BAn
