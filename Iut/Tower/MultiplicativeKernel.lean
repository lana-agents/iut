/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Tower.TorsionRigid

/-!
# The Legendre curve at a place of multiplicative reduction: inertia acts unipotently

For the Legendre curve `E_μ : y² = x(x − 1)(x − μ)` over a field `K` with a valuation `v` with
`v(μ) < 1` and `v(2) = 1` (multiplicative reduction, the node of `ȳ² = x̄²(x̄ − 1)` at `(0, 0)`),
the affine points reducing to the node are those with `v(x) < 1`; the others form, with `0`, the
subgroup `E₀` of points with nonsingular reduction. For `σ : K →+* K` satisfying the inertia
condition `v(σ z − z) < 1` for all `v`-integral `z`, preserving `v` and fixing `μ`:

* `Iut.MultKernel.sub_eq_zero_or_one_le`: for `Q` reducing to the node, `σ Q − Q = 0` or
  `σ Q − Q` reduces to a nonsingular point (`1 ≤ v(x(σ Q − Q))`). Two regimes: `v(μ) < v(x)`,
  where `t = y/x` is a unit with `t² ≡ −1` selecting the branch at the node, and `v(x) ≤ v(μ)`
  (the middle component), where `c = x/μ`, `t = y/μ` are integral with `t² ≡ −c(c − 1)`; in
  both, the chord through `σ Q` and `−Q` has a non-integral slope, or an integral slope `L` with
  `L̄² ≠ −1`, so `x(σ Q − Q) ≡ L² + 1 ≢ 0`.
* `Iut.MultKernel.map_eq_self_of_unit`: an `n`-torsion point (`n` odd, `v(n) = 1`) with
  `v(x) = 1` is fixed by `σ` (reduction is injective on the prime-to-`p` torsion of `E₀`,
  `Iut.ReductionKernel.eq_of_nsmul_eq_zero_of_congr`).
* `Iut.MultKernel.map_sub_map_eq_self`, **unipotence**: `σ(σ Q − Q) = σ Q − Q` for every
  `n`-torsion point `Q`; hence `σ^k Q = Q + k(σ Q − Q)` and `σ^n Q = Q`
  (`Iut.MultKernel.map_pow_eq_self`).
-/

namespace Iut.MultKernel

open WeierstrassCurve WeierstrassCurve.Affine Iut.Tripod

variable {K : Type*} [Field K] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
  (v : Valuation K Γ) {μ : K}

/-! ### The Legendre equation and integrality -/

section Curve

-- a model `W` of the Legendre curve `y² = x(x − 1)(x − μ)`: the coefficient hypotheses
variable {W : Affine K} (hW₁ : W.a₁ = 0) (hW₂ : W.a₂ = -(1 + μ)) (hW₃ : W.a₃ = 0)
  (hW₄ : W.a₄ = μ) (hW₆ : W.a₆ = 0)
include hW₁ hW₂ hW₃ hW₄ hW₆

omit [LinearOrderedCommGroupWithZero Γ] in
/-- The Legendre equation `y² = x(x − 1)(x − μ)`. -/
lemma legendre_eq {x y : K} (h : W.Equation x y) :
    y ^ 2 = x * (x - 1) * (x - μ) := by
  rw [equation_iff, hW₁, hW₂, hW₃, hW₄, hW₆] at h
  linear_combination h

omit hW₁ hW₂ hW₃ hW₄ hW₆ in
/-- `v(x − 1) = 1` for `v(x) < 1`. -/
lemma valuation_sub_one_eq_one {x : K} (hx : v x < 1) : v (x - 1) = 1 := by
  rw [Valuation.map_sub_eq_of_lt_right _ (by rw [map_one]; exact hx), map_one]

omit hW₁ hW₂ hW₃ hW₄ hW₆ in
/-- `v(x − μ) ≤ max (v x) (v μ)`. -/
lemma valuation_sub_le_max (x : K) : v (x - μ) ≤ max (v x) (v μ) := Valuation.map_sub _ _ _

/-- The `y`-coordinate of a point of the node: `v(y)² = v(x)·v(x − μ)` for `v(x) < 1`. -/
lemma valuation_y_sq {x y : K} (h : W.Equation x y) (hx : v x < 1) :
    v y ^ 2 = v x * v (x - μ) := by
  rw [← map_pow, legendre_eq hW₁ hW₂ hW₃ hW₄ hW₆ h, map_mul, map_mul,
    valuation_sub_one_eq_one v hx, mul_one]

/-- In the regime `v(μ) < v(x) < 1`, `v(y) = v(x)`. -/
lemma valuation_y_eq {x y : K} (h : W.Equation x y) (hx : v x < 1)
    (hμx : v μ < v x) : v y = v x := by
  have h1 := valuation_y_sq v hW₁ hW₂ hW₃ hW₄ hW₆ h hx
  rw [Valuation.map_sub_eq_of_lt_left _ hμx, ← sq] at h1
  exact (pow_left_inj₀ zero_le zero_le two_ne_zero).mp h1

/-- In the regime `v(x) ≤ v(μ)`, `v(y) ≤ v(μ)`. -/
lemma valuation_y_le {x y : K} (h : W.Equation x y) (hx : v x < 1) (hxμ : v x ≤ v μ) :
    v y ≤ v μ := by
  have h1 := valuation_y_sq v hW₁ hW₂ hW₃ hW₄ hW₆ h hx
  have h2 : v y ^ 2 ≤ v μ ^ 2 := by
    rw [h1, sq]
    exact mul_le_mul' hxμ ((valuation_sub_le_max v x).trans (max_le hxμ le_rfl))
  exact (pow_le_pow_iff_left₀ zero_le zero_le two_ne_zero).mp h2

/-- A point of the node with `v(x) < 1` has `v(y) < 1`. -/
lemma valuation_y_lt_one {x y : K} (h : W.Equation x y) (hx : v x < 1)
    (hμ : v μ < 1) : v y < 1 := by
  have h1 := valuation_y_sq v hW₁ hW₂ hW₃ hW₄ hW₆ h hx
  have : v y ^ 2 < 1 := by
    rw [h1]
    calc v x * v (x - μ) ≤ v x * 1 := mul_le_mul_right ((valuation_sub_le_max v x).trans
          (max_le hx.le hμ.le)) _
      _ < 1 := by rw [mul_one]; exact hx
  by_contra hcon
  exact absurd this (not_lt.mpr (one_le_pow₀ (not_lt.mp hcon)))

/-! ### The middle component: `c = x/μ`, `t = y/μ` -/

omit hW₁ hW₂ hW₃ hW₄ hW₆ in
/-- On the middle component, `t̄ = 0` forces `c̄(c̄ − 1) = 0`: `v(c(c − 1)) < 1` when `v(t) < 1`,
for `t² = c(c − 1)(μc − 1)` with `c` integral and `v(μ) < 1`. -/
lemma valuation_c_mul_sub_one_lt (hμ : v μ < 1) {c t : K} (hc : v c ≤ 1)
    (htsq : t ^ 2 = c * (c - 1) * (μ * c - 1)) (ht : v t < 1) : v (c * (c - 1)) < 1 := by
  have e : c * (c - 1) = μ * c ^ 2 * (c - 1) - t ^ 2 := by
    rw [htsq]; ring
  rw [e]
  refine (Valuation.map_sub _ _ _).trans_lt (max_lt ?_ ?_)
  · rw [map_mul, map_mul, map_pow]
    calc v μ * v c ^ 2 * v (c - 1) ≤ v μ * 1 * 1 := by
          gcongr
          · exact pow_le_one₀ zero_le hc
          · exact (Valuation.map_sub _ _ _).trans (max_le hc (by rw [map_one]))
      _ < 1 := by rw [mul_one, mul_one]; exact hμ
  · rw [map_pow]; exact pow_lt_one₀ zero_le ht two_ne_zero

omit hW₁ hW₂ hW₃ hW₄ hW₆ in
/-- `v(1 − 2c) = 1` when `v(c(c − 1)) < 1` and `v(2) = 1`: `(1 − 2c)² = 1 − 4c(c − 1)`. -/
lemma valuation_one_sub_two_mul_eq_one (h2 : v 2 = 1) {c : K} (hg : v (c * (c - 1)) < 1) :
    v (1 - 2 * c) = 1 := by
  have hsq : (1 - 2 * c) ^ 2 = 1 + 4 * (c * (c - 1)) := by ring
  have h4 : v 4 = 1 := by
    have : (4 : K) = 2 ^ 2 := by norm_num
    rw [this, map_pow, h2, one_pow]
  have : v ((1 - 2 * c) ^ 2) = 1 := by
    rw [hsq, Valuation.map_add_eq_of_lt_left, map_one]
    rw [map_one, map_mul, h4, one_mul]
    exact hg
  exact Iut.valuation_eq_one_of_sq v this

/-! ### The chord through `σ Q` and `−Q` at the node -/

section Node

variable (σ : K →+* K) (hμ : v μ < 1) (h2 : v 2 = 1) (hσμ : σ μ = μ)
  (hσ : ∀ z, v z ≤ 1 → v (σ z - z) < 1) (hvσ : ∀ z, v (σ z) = v z)
include hμ h2 hσμ hσ hvσ

omit hσμ in
/-- **Regime `v(μ) < v(x)`**: the slope `L = (σ y + y)/(σ x − x)` of the chord through `σ Q` and
`−Q` has `v(L) > 1`, or is integral with `v(L² + 1) = 1`. -/
lemma slope_branch {x y : K} (h : W.Equation x y) (hx : v x < 1)
    (hμx : v μ < v x) (hne : σ x ≠ x) :
    1 < v ((σ y + y) / (σ x - x)) ∨
      (v ((σ y + y) / (σ x - x)) ≤ 1 ∧ v (((σ y + y) / (σ x - x)) ^ 2 + 1) = 1) := by
  have hvx0 : v x ≠ 0 := (lt_of_le_of_lt zero_le hμx).ne'
  have hx0 : x ≠ 0 := (Valuation.ne_zero_iff _).mp hvx0
  have hσx0 : σ x ≠ 0 := fun h0 => hx0 ((map_eq_zero σ).mp h0)
  -- the branch invariant `t = y/x`, a unit with `t² ≡ −1`
  set t := y / x with ht
  have hty : y = t * x := by rw [ht]; field_simp
  have ht1 : v t = 1 := by
    rw [ht, map_div₀, valuation_y_eq v hW₁ hW₂ hW₃ hW₄ hW₆ h hx hμx, div_self hvx0]
  have htsq : v (t ^ 2 + 1) < 1 := by
    have e : t ^ 2 + 1 = (x - μ) + μ / x := by
      rw [ht]; field_simp
      linear_combination legendre_eq hW₁ hW₂ hW₃ hW₄ hW₆ h
    rw [e]
    refine (Valuation.map_add _ _ _).trans_lt (max_lt ?_ ?_)
    · exact (valuation_sub_le_max v x).trans_lt (max_lt hx hμ)
    · rw [map_div₀, div_lt_one₀ (lt_of_le_of_lt zero_le hμx)]; exact hμx
  have hσt : v (σ t - t) < 1 := hσ t ht1.le
  have hσt1 : v (σ t) = 1 := by rw [hvσ]; exact ht1
  have hσy : σ y = σ t * σ x := by rw [hty, map_mul]
  -- `c = σ x / x`, a unit
  set c := σ x / x with hc
  have hc1 : v c = 1 := by
    rw [hc, map_div₀, hvσ, div_self hvx0]
  have hcne : c - 1 ≠ 0 := by
    rw [sub_ne_zero]; intro hcon
    exact hne (by rw [← div_eq_one_iff_eq hx0]; exact hcon)
  have hL : (σ y + y) / (σ x - x) = (c * σ t + t) / (c - 1) := by
    rw [hσy, hty, hc]
    have hc1' : σ x / x - 1 ≠ 0 := hcne
    field_simp
  rw [hL]
  have hc1le : v (c + 1) ≤ 1 := (Valuation.map_add _ _ _).trans (max_le hc1.le (by rw [map_one]))
  have hnum_le : v (c * σ t + t) ≤ 1 :=
    (Valuation.map_add _ _ _).trans (max_le (by rw [map_mul, hc1, one_mul, hσt1]) ht1.le)
  by_cases hc' : v (c - 1) < 1
  · left
    have hnum : v (c * σ t + t) = 1 := by
      have e : c * σ t + t = 2 * t + ((c - 1) * t + c * (σ t - t)) := by ring
      have h1 : v ((c - 1) * t + c * (σ t - t)) < 1 := by
        refine (Valuation.map_add _ _ _).trans_lt (max_lt ?_ ?_)
        · rw [map_mul, ht1, mul_one]; exact hc'
        · rw [map_mul, hc1, one_mul]; exact hσt
      have h2t : v (2 * t) = 1 := by rw [map_mul, h2, ht1, mul_one]
      rw [e, Valuation.map_add_eq_of_lt_left _ (by rw [h2t]; exact h1), h2t]
    rw [map_div₀, hnum, one_div, one_lt_inv₀ (lt_of_le_of_ne zero_le
      (Ne.symm ((Valuation.ne_zero_iff _).mpr hcne)))]
    exact hc'
  · right
    have hc1' : v (c - 1) = 1 := by
      refine le_antisymm ((Valuation.map_sub _ _ _).trans (max_le hc1.le (by rw [map_one]))) ?_
      exact not_lt.mp hc'
    have hLint : v ((c * σ t + t) / (c - 1)) ≤ 1 := by
      rw [map_div₀, hc1', div_one]
      exact hnum_le
    refine ⟨hLint, ?_⟩
    -- `L² + 1 = (−4c + A + B)/(c − 1)²` with `A ≡ 0 ≡ B`
    set A := (c * σ t + t) ^ 2 - (c + 1) ^ 2 * t ^ 2 with hA
    set B := (c + 1) ^ 2 * (t ^ 2 + 1) with hB
    have e : ((c * σ t + t) / (c - 1)) ^ 2 + 1 = (-4 * c + (A + B)) / (c - 1) ^ 2 := by
      rw [hA, hB]
      field_simp
      ring
    have h4c : v (-4 * c) = 1 := by
      rw [map_mul, Valuation.map_neg, hc1, mul_one]
      have : (4 : K) = 2 ^ 2 := by norm_num
      rw [this, map_pow, h2, one_pow]
    have hAv : v A < 1 := by
      have e2 : A = c * (σ t - t) * ((c * σ t + t) + (c + 1) * t) := by rw [hA]; ring
      rw [e2, map_mul, map_mul, hc1, one_mul]
      calc v (σ t - t) * v ((c * σ t + t) + (c + 1) * t) ≤ v (σ t - t) * 1 := by
            refine mul_le_mul_right ((Valuation.map_add _ _ _).trans (max_le hnum_le ?_)) _
            rw [map_mul, ht1, mul_one]; exact hc1le
        _ < 1 := by rw [mul_one]; exact hσt
    have hBv : v B < 1 := by
      rw [hB, map_mul, map_pow]
      calc v (c + 1) ^ 2 * v (t ^ 2 + 1) ≤ 1 * v (t ^ 2 + 1) :=
            mul_le_mul_left (pow_le_one₀ zero_le hc1le) _
        _ < 1 := by rw [one_mul]; exact htsq
    have hAB : v (A + B) < 1 := (Valuation.map_add _ _ _).trans_lt (max_lt hAv hBv)
    rw [e, map_div₀, map_pow, hc1', one_pow, div_one,
      Valuation.map_add_eq_of_lt_left _ (by rw [h4c]; exact hAB), h4c]

/-- **Regime `v(x) ≤ v(μ)`** (the middle component): the slope `L = (σ y + y)/(σ x − x)` has
`v(L) > 1`. -/
lemma slope_middle {x y : K} (h : W.Equation x y) (hx : v x < 1)
    (hxμ : v x ≤ v μ) (hne : σ x ≠ x) : 1 < v ((σ y + y) / (σ x - x)) := by
  have hμ0 : μ ≠ 0 := fun h0 => by
    rw [h0, map_zero] at hxμ
    exact hne (by rw [(Valuation.zero_iff _).mp (le_antisymm hxμ zero_le), map_zero])
  -- `c = x/μ`, `t = y/μ`, integral, with `t² = c(c − 1)(μc − 1)`
  set c := x / μ with hc
  set t := y / μ with ht
  have hxc : x = μ * c := by rw [hc]; field_simp
  have hyt : y = μ * t := by rw [ht]; field_simp
  have hc1 : v c ≤ 1 := by
    rw [hc, map_div₀, div_le_one₀ (lt_of_le_of_ne zero_le (Ne.symm ((Valuation.ne_zero_iff _).mpr
      hμ0)))]
    exact hxμ
  have ht1 : v t ≤ 1 := by
    rw [ht, map_div₀, div_le_one₀ (lt_of_le_of_ne zero_le (Ne.symm ((Valuation.ne_zero_iff _).mpr
      hμ0)))]
    exact valuation_y_le v hW₁ hW₂ hW₃ hW₄ hW₆ h hx hxμ
  have htsq : t ^ 2 = c * (c - 1) * (μ * c - 1) := by
    have := legendre_eq hW₁ hW₂ hW₃ hW₄ hW₆ h
    rw [hxc, hyt] at this
    have hμ2 : μ ^ 2 ≠ 0 := pow_ne_zero 2 hμ0
    apply mul_left_cancel₀ hμ2
    linear_combination this
  have hσc : v (σ c - c) < 1 := hσ c hc1
  have hσt : v (σ t - t) < 1 := hσ t ht1
  have hσx : σ x = μ * σ c := by rw [hxc, map_mul, hσμ]
  have hσy : σ y = μ * σ t := by rw [hyt, map_mul, hσμ]
  have hcne : σ c - c ≠ 0 := by
    intro h0
    exact hne (by rw [hσx, hxc, sub_eq_zero.mp h0])
  have hL : (σ y + y) / (σ x - x) = (σ t + t) / (σ c - c) := by
    rw [hσy, hyt, hσx, hxc]
    field_simp
  rw [hL]
  by_cases ht0 : v t = 1
  · have hnum : v (σ t + t) = 1 := by
      have e : σ t + t = 2 * t + (σ t - t) := by ring
      rw [e, Valuation.map_add_eq_of_lt_left, map_mul, h2, ht0, mul_one]
      rw [map_mul, h2, ht0, mul_one]; exact hσt
    rw [map_div₀, hnum, one_div, one_lt_inv₀ (lt_of_le_of_ne zero_le
      (Ne.symm ((Valuation.ne_zero_iff _).mpr hcne)))]
    exact hσc
  · have ht0' : v t < 1 := lt_of_le_of_ne ht1 ht0
    -- `t̄ = 0`, so `c̄ ∈ {0, 1}` and `g(c) = t²` has `g'(c̄) = ±1`
    have hg : v (c * (c - 1)) < 1 := valuation_c_mul_sub_one_lt v hμ hc1 htsq ht0'
    -- the identity `(σt − t)(σt + t) = (σc − c)·h` with `v(h) = 1`
    set hh := μ * (σ c ^ 2 + σ c * c + c ^ 2) - (1 + μ) * (σ c + c) + 1 with hhh
    have hid : (σ t - t) * (σ t + t) = (σ c - c) * hh := by
      have hσsq : σ t ^ 2 = σ c * (σ c - 1) * (μ * σ c - 1) := by
        rw [← map_pow, htsq]
        simp only [map_mul, map_sub, map_one, hσμ]
      rw [hhh]
      linear_combination hσsq - htsq
    have hh1 : v hh = 1 := by
      -- `hh ≡ 1 − 2c ≡ ±1` since `c(c − 1) ≡ 0`
      have e : hh = (1 - 2 * c) + (μ * (σ c ^ 2 + σ c * c + c ^ 2) - μ * (σ c + c) -
          (σ c - c)) := by rw [hhh]; ring
      have h12c : v (1 - 2 * c) = 1 := valuation_one_sub_two_mul_eq_one v h2 hg
      rw [e, Valuation.map_add_eq_of_lt_left, h12c]
      rw [h12c]
      refine (Valuation.map_sub _ _ _).trans_lt (max_lt ((Valuation.map_sub _ _ _).trans_lt
        (max_lt ?_ ?_)) hσc)
      · rw [map_mul]
        calc v μ * v (σ c ^ 2 + σ c * c + c ^ 2) ≤ v μ * 1 := by
              refine mul_le_mul_right ((Valuation.map_add _ _ _).trans (max_le
                ((Valuation.map_add _ _ _).trans (max_le ?_ ?_)) ?_)) _
              · rw [map_pow, hvσ]; exact pow_le_one₀ zero_le hc1
              · rw [map_mul, hvσ]; exact mul_le_one' hc1 hc1
              · rw [map_pow]; exact pow_le_one₀ zero_le hc1
          _ < 1 := by rw [mul_one]; exact hμ
      · rw [map_mul]
        calc v μ * v (σ c + c) ≤ v μ * 1 := by
              refine mul_le_mul_right ((Valuation.map_add _ _ _).trans (max_le ?_ hc1)) _
              rw [hvσ]; exact hc1
          _ < 1 := by rw [mul_one]; exact hμ
    have htne : σ t - t ≠ 0 := by
      intro h0
      rw [h0, zero_mul, eq_comm, mul_eq_zero] at hid
      rcases hid with hid | hid
      · exact hcne hid
      · rw [hid, map_zero] at hh1; exact zero_ne_one hh1
    have hL' : (σ t + t) / (σ c - c) = hh / (σ t - t) := by
      rw [div_eq_div_iff hcne htne]
      linear_combination hid
    rw [hL', map_div₀, hh1, one_div, one_lt_inv₀ (lt_of_le_of_ne zero_le
      (Ne.symm ((Valuation.ne_zero_iff _).mpr htne)))]
    exact hσt

end Node

/-! ### The difference `σ Q − Q` at the node -/

section Difference

variable [DecidableEq K]
variable (σ : K →+* K) (hμ : v μ < 1) (h2 : v 2 = 1) (hσμ : σ μ = μ)
  (hσ : ∀ z, v z ≤ 1 → v (σ z - z) < 1) (hvσ : ∀ z, v (σ z) = v z)
include hμ h2 hσμ hσ hvσ

/-- **`σ Q − Q` has nonsingular reduction** for a point `Q = (x, y)` reducing to the node
(`v(x) < 1`): it is `0`, or an affine point with `1 ≤ v(x)`. -/
theorem sub_eq_zero_or_one_le {x y : K} (h : W.Nonsingular x y)
    (h' : W.Nonsingular (σ x) (σ y)) (hx : v x < 1) :
    Point.some (σ x) (σ y) h' - Point.some x y h = 0 ∨
      ∃ (x' y' : K) (h'' : W.Nonsingular x' y'),
        Point.some (σ x) (σ y) h' - Point.some x y h = Point.some x' y' h'' ∧ 1 ≤ v x' := by
  have hneg : ∀ a b : K, W.negY a b = -b := fun a b => by
    simp [negY, hW₁, hW₃]
  have hy1 : v y < 1 := valuation_y_lt_one v hW₁ hW₂ hW₃ hW₄ hW₆ h.1 hx hμ
  rw [sub_eq_add_neg, Point.neg_some]
  by_cases hxy : σ x = x ∧ σ y = W.negY x (W.negY x y)
  · left
    exact Point.add_of_Y_eq hxy.1 hxy.2
  · right
    refine ⟨_, _, _, Point.add_some hxy, ?_⟩
    rw [hneg, hneg, neg_neg] at hxy
    -- the slope of the chord
    set L := W.slope (σ x) x (σ y) (W.negY x y) with hL
    have haddX : W.addX (σ x) x L = (L ^ 2 + 1) + (μ - σ x - x) := by
      simp only [addX, hW₁, hW₂]; ring
    have hrest : v (μ - σ x - x) < 1 :=
      (Valuation.map_sub _ _ _).trans_lt (max_lt ((Valuation.map_sub _ _ _).trans_lt
        (max_lt hμ (by rw [hvσ]; exact hx))) hx)
    suffices key : 1 < v L ∨ (v L ≤ 1 ∧ v (L ^ 2 + 1) = 1) by
      rw [haddX]
      rcases key with hL1 | ⟨hL1, hL2⟩
      · have hL2 : 1 < v (L ^ 2 + 1) := by
          rw [Valuation.map_add_eq_of_lt_left, map_pow]
          · exact one_lt_pow₀ hL1 two_ne_zero
          · rw [map_pow, map_one]; exact one_lt_pow₀ hL1 two_ne_zero
        rw [Valuation.map_add_eq_of_lt_left _ (hrest.trans hL2)]
        exact hL2.le
      · rw [Valuation.map_add_eq_of_lt_left _ (by rw [hL2]; exact hrest), hL2]
    -- compute the slope
    by_cases hxx : σ x = x
    · -- `σ Q = −Q`, `σ Q − Q = −2Q`
      have hyy : σ y = -y := by
        rcases Y_eq_of_X_eq h'.1 h.1 hxx with hh | hh
        · exact absurd ⟨hxx, hh⟩ hxy
        · rw [hh, hneg]
      have hy0 : y ≠ 0 := by
        intro h0
        exact hxy ⟨hxx, by rw [hyy, h0, neg_zero]⟩
      -- the branch invariants are moved to their negatives, contradiction or middle component
      by_cases hμx : v μ < v x
      · exfalso
        -- `t = y/x` is a unit with `σ t = −t`, so `v(2t) < 1`
        have hvx0 : v x ≠ 0 := (lt_of_le_of_lt zero_le hμx).ne'
        have ht1 : v (y / x) = 1 := by
          rw [map_div₀, valuation_y_eq v hW₁ hW₂ hW₃ hW₄ hW₆ h.1 hx hμx, div_self hvx0]
        have hσt := hσ (y / x) ht1.le
        rw [map_div₀, hyy, hxx, neg_div] at hσt
        have e : -(y / x) - y / x = -(2 * (y / x)) := by ring
        rw [e, Valuation.map_neg, map_mul, h2, one_mul, ht1] at hσt
        exact lt_irrefl _ hσt
      · -- middle component: the tangent slope `f'(x)/(−2y)` is non-integral
        left
        have hxμ : v x ≤ v μ := not_lt.mp hμx
        have hμ0 : μ ≠ 0 := fun h0 => by
          rw [h0, map_zero] at hxμ
          have hx0 : x = 0 := (Valuation.zero_iff _).mp (le_antisymm hxμ zero_le)
          have := legendre_eq hW₁ hW₂ hW₃ hW₄ hW₆ h.1
          rw [hx0, zero_mul, zero_mul, pow_eq_zero_iff two_ne_zero] at this
          exact hy0 this
        have hyne : ¬ (-y = y) := by
          intro hcon
          have h2ne : (2 : K) ≠ 0 := fun h0 => by rw [h0, map_zero] at h2; exact zero_ne_one h2
          exact hy0 ((mul_eq_zero.mp (show 2 * y = 0 by linear_combination -hcon)).resolve_left
            h2ne)
        have hLeq : L = (3 * x ^ 2 + 2 * -(1 + μ) * x + μ) / (-y - y) := by
          rw [hL, hxx, hyy, Affine.slope, if_pos rfl]
          simp only [hneg, neg_neg, if_neg hyne, hW₁, hW₂, hW₄, zero_mul, sub_zero]
        set c := x / μ with hc
        set t := y / μ with ht
        have hxc : x = μ * c := by rw [hc]; field_simp
        have hyt : y = μ * t := by rw [ht]; field_simp
        have hμpos : 0 < v μ := lt_of_le_of_ne zero_le (Ne.symm ((Valuation.ne_zero_iff _).mpr hμ0))
        have hc1 : v c ≤ 1 := by
          rw [hc, map_div₀, div_le_one₀ hμpos]; exact hxμ
        have ht1 : v t ≤ 1 := by
          rw [ht, map_div₀, div_le_one₀ hμpos]
          exact valuation_y_le v hW₁ hW₂ hW₃ hW₄ hW₆ h.1 hx hxμ
        have htsq : t ^ 2 = c * (c - 1) * (μ * c - 1) := by
          have := legendre_eq hW₁ hW₂ hW₃ hW₄ hW₆ h.1
          rw [hxc, hyt] at this
          apply mul_left_cancel₀ (pow_ne_zero 2 hμ0)
          linear_combination this
        have hσt : σ t = -t := by
          rw [ht, map_div₀, hyy, hσμ, neg_div]
        have ht0 : v t < 1 := by
          have := hσ t ht1
          have e : -t - t = -(2 * t) := by ring
          rw [hσt, e, Valuation.map_neg, map_mul, h2, one_mul] at this
          exact this
        have ht0' : t ≠ 0 := by
          intro h0
          apply hy0
          rw [hyt, h0, mul_zero]
        have hg := valuation_c_mul_sub_one_lt v hμ hc1 htsq ht0
        have h2ne : (2 : K) ≠ 0 := fun h0 => by rw [h0, map_zero] at h2; exact zero_ne_one h2
        have hLc : L = (3 * μ * c ^ 2 - 2 * (1 + μ) * c + 1) / (-(2 * t)) := by
          rw [hLeq, hxc, hyt, div_eq_div_iff]
          · ring
          · have e : -(μ * t) - μ * t = -(2 * (μ * t)) := by ring
            rw [e]
            exact neg_ne_zero.mpr (mul_ne_zero h2ne (mul_ne_zero hμ0 ht0'))
          · exact neg_ne_zero.mpr (mul_ne_zero h2ne ht0')
        have hnum : v (3 * μ * c ^ 2 - 2 * (1 + μ) * c + 1) = 1 := by
          have e : 3 * μ * c ^ 2 - 2 * (1 + μ) * c + 1 = (1 - 2 * c) + μ * c * (3 * c - 2) := by
            ring
          rw [e, Valuation.map_add_eq_of_lt_left, valuation_one_sub_two_mul_eq_one v h2 hg]
          rw [valuation_one_sub_two_mul_eq_one v h2 hg, map_mul, map_mul]
          calc v μ * v c * v (3 * c - 2) ≤ v μ * 1 * 1 := by
                gcongr
                · exact (Valuation.map_sub _ _ _).trans (max_le
                    (by rw [map_mul]; exact mul_le_one' (ReductionKernel.valuation_natCast_le_one v
                      3) hc1) (ReductionKernel.valuation_natCast_le_one v 2))
            _ < 1 := by rw [mul_one, mul_one]; exact hμ
        rw [hLc, map_div₀, hnum, Valuation.map_neg, map_mul, h2, one_mul, one_div,
          one_lt_inv₀ (lt_of_le_of_ne zero_le (Ne.symm ((Valuation.ne_zero_iff _).mpr ht0')))]
        exact ht0
    · -- `σ x ≠ x`: the chord
      rw [hL, hneg, slope_of_X_ne hxx, sub_neg_eq_add]
      by_cases hμx : v μ < v x
      · exact slope_branch v hW₁ hW₂ hW₃ hW₄ hW₆ σ hμ h2 hσ hvσ h.1 hx hμx hxx
      · exact Or.inl (slope_middle v hW₁ hW₂ hW₃ hW₄ hW₆ σ hμ h2 hσμ hσ hvσ h.1 hx
          (not_lt.mp hμx) hxx)

end Difference

/-! ### Rigidity on `E₀` and unipotence -/

section Unipotent

variable [DecidableEq K]
variable (σ : K →+* K) (hμ : v μ < 1) (h2 : v 2 = 1) (hσμ : σ μ = μ)
  (hσ : ∀ z, v z ≤ 1 → v (σ z - z) < 1) (hvσ : ∀ z, v (σ z) = v z)
  (hψ : ReductionKernel.DivPolyHyp W) {n : ℕ} (hodd : Odd n) (hn : v (n : K) = 1)
  (φ : W.Point →+ W.Point)
  (hφ : ∀ (x y : K) (h : W.Nonsingular x y),
    ∃ h' : W.Nonsingular (σ x) (σ y), φ (Point.some x y h) = Point.some (σ x) (σ y) h')
include hμ h2 hσμ hσ hvσ hψ hodd hn hφ

omit hσμ hvσ in
/-- **Inertia fixes the prime-to-`p` torsion of `E₀`**: an `n`-torsion point `(x, y)` with
`1 ≤ v(x)` is fixed by `φ`. -/
theorem map_eq_self_of_one_le {x y : K} (h : W.Nonsingular x y)
    (hQ : n • Point.some x y h = 0) (hx : 1 ≤ v x) : φ (Point.some x y h) = Point.some x y h := by
  obtain ⟨h', hφ'⟩ := hφ x y h
  rw [hφ']
  have hW2 : v W.a₂ ≤ 1 := by
    rw [hW₂, Valuation.map_neg]
    exact (Valuation.map_add _ _ _).trans (max_le (by rw [map_one]) hμ.le)
  have hW4 : v W.a₄ ≤ 1 := by rw [hW₄]; exact hμ.le
  have hW6 : v W.a₆ ≤ 1 := by rw [hW₆, map_zero]; exact zero_le_one
  obtain ⟨hx1, hy1⟩ := ReductionKernel.valuation_le_one_of_nsmul_eq_zero v hW₁ hW₃ hW2 hW4 hW6
    hψ hodd hn h hQ
  have hxu : v x = 1 := le_antisymm hx1 hx
  -- nonsingular reduction: `x̄ ≠ 0`
  have hns : v (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) = 1 ∨ v (2 * y) = 1 := by
    by_cases hy : v (2 * y) = 1
    · exact Or.inr hy
    · left
      have hy' : v y < 1 := by
        rw [map_mul, h2, one_mul] at hy
        exact lt_of_le_of_ne hy1 hy
      -- `y² = x(x − 1)(x − μ)` with `v x = 1`, `v(x − μ) = 1`, so `v(x − 1) < 1`
      have hxμ : v (x - μ) = 1 := by
        rw [Valuation.map_sub_eq_of_lt_left _ (by rw [hxu]; exact hμ), hxu]
      have hx1' : v (x - 1) < 1 := by
        have e := legendre_eq hW₁ hW₂ hW₃ hW₄ hW₆ h.1
        have : v (y ^ 2) = v (x - 1) := by
          rw [e, map_mul, map_mul, hxu, hxμ, one_mul, mul_one]
        rw [map_pow] at this
        rw [← this]
        exact pow_lt_one₀ zero_le hy' two_ne_zero
      -- `f'(x) = 1 + (3(x² − 1) − 2(x − 1) − 2μx + μ)`
      have e : 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ =
          1 + (3 * ((x - 1) * (x + 1)) - 2 * (x - 1) - 2 * (μ * x) + μ) := by
        rw [hW₂, hW₄]; ring
      rw [e, Valuation.map_add_eq_of_lt_left, map_one]
      rw [map_one]
      have h3 : v (3 : K) ≤ 1 := ReductionKernel.valuation_natCast_le_one v 3
      have hx1le : v (x + 1) ≤ 1 :=
        (Valuation.map_add _ _ _).trans (max_le hx1 (by rw [map_one]))
      refine (Valuation.map_add _ _ _).trans_lt (max_lt ((Valuation.map_sub _ _ _).trans_lt
        (max_lt ((Valuation.map_sub _ _ _).trans_lt (max_lt ?_ ?_)) ?_)) hμ)
      · rw [map_mul, map_mul]
        calc v 3 * (v (x - 1) * v (x + 1)) ≤ 1 * (v (x - 1) * 1) := by gcongr
          _ < 1 := by rw [one_mul, mul_one]; exact hx1'
      · rw [map_mul, h2, one_mul]; exact hx1'
      · rw [map_mul, map_mul, h2, one_mul, hxu, mul_one]; exact hμ
  have hσx : v (σ x) ≤ 1 := by
    have : σ x = (σ x - x) + x := by ring
    rw [this]
    exact (Valuation.map_add _ _ _).trans (max_le (hσ x hx1).le hx1)
  have hσy : v (σ y) ≤ 1 := by
    have : σ y = (σ y - y) + y := by ring
    rw [this]
    exact (Valuation.map_add _ _ _).trans (max_le (hσ y hy1).le hy1)
  have hQ' : n • Point.some (σ x) (σ y) h' = 0 := by
    rw [← hφ', ← map_nsmul, hQ, map_zero]
  exact (ReductionKernel.eq_of_nsmul_eq_zero_of_congr v hW₁ hW₃ hW2 hW4 hW6 h2 hψ hodd hn h h'
    hQ hQ' (by rw [Valuation.map_sub_swap]; exact hσ x hx1)
    (by rw [Valuation.map_sub_swap]; exact hσ y hy1) hns).symm

/-- **Unipotence**: `φ(φ Q − Q) = φ Q − Q` for every `n`-torsion point `Q`. -/
theorem map_sub_map_eq_self (Q : W.Point) (hQ : n • Q = 0) : φ (φ Q - Q) = φ Q - Q := by
  cases Q with
  | zero =>
    change φ (φ 0 - 0) = φ 0 - 0
    rw [map_zero, sub_zero, map_zero]
  | some x y h =>
    by_cases hx : v x < 1
    · obtain ⟨h', hφ'⟩ := hφ x y h
      rw [hφ']
      rcases sub_eq_zero_or_one_le v hW₁ hW₂ hW₃ hW₄ hW₆ σ hμ h2 hσμ hσ hvσ h h' hx with
        h0 | ⟨x', y', h'', hsub, hx'⟩
      · rw [h0, map_zero]
      · rw [hsub]
        have hR : n • Point.some x' y' h'' = 0 := by
          rw [← hsub, nsmul_sub, hQ, ← hφ', ← map_nsmul, hQ, map_zero, sub_zero]
        exact map_eq_self_of_one_le v hW₁ hW₂ hW₃ hW₄ hW₆ σ hμ h2 hσ hψ hodd hn φ hφ h'' hR hx'
    · have := map_eq_self_of_one_le v hW₁ hW₂ hW₃ hW₄ hW₆ σ hμ h2 hσ hψ hodd hn φ hφ h hQ
        (not_lt.mp hx)
      rw [this, sub_self, map_zero]

omit hW₁ hW₂ hW₃ hW₄ hW₆ hμ h2 hσμ hσ hvσ hψ hodd hn hφ in
/-- `φ^k Q = Q + k(φ Q − Q)` when `φ` fixes `φ Q − Q`. -/
lemma iterate_eq_add_nsmul {G : Type*} [AddCommGroup G] (ψ : G →+ G) {Q : G}
    (hQ : ψ (ψ Q - Q) = ψ Q - Q) (k : ℕ) : ψ^[k] Q = Q + k • (ψ Q - Q) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, map_add, map_nsmul, hQ, succ_nsmul]
    abel

/-- **`φ^n Q = Q`** for every `n`-torsion point `Q`. -/
theorem iterate_map_eq_self (Q : W.Point) (hQ : n • Q = 0) : (⇑φ)^[n] Q = Q := by
  rw [iterate_eq_add_nsmul φ (map_sub_map_eq_self v hW₁ hW₂ hW₃ hW₄ hW₆ σ hμ h2 hσμ hσ hvσ hψ hodd
    hn φ hφ Q hQ), nsmul_sub, ← map_nsmul, hQ, map_zero, sub_zero, add_zero]

end Unipotent

end Curve

end Iut.MultKernel
