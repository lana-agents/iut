/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Mathlib.NumberTheory.Chebyshev
import Iut.Implication.PrimeSelection
import Iut.Implication.Invariants

/-!
# Explicit Chebyshev bounds and the prime-number-theorem certificates

This file relates the two prime-number-theorem-strength certificates of the repository,
`ChebyshevBound` (IUT IV, Proposition 2.1(ii)) and `PrimeCountingBound` (IUT IV,
Proposition 1.6), to what Mathlib proves about Chebyshev's function `θ` and the
prime-counting function `π`.

## What is proved unconditionally

* `two_thirds_mul_le_theta`: the **lower** Chebyshev bound `(2/3)·x ≤ θ(x)` for all
  `x ≥ 10^12`, from Mathlib's `Chebyshev.theta_ge'` and `log 2 > 2/3`.
* `chebyshevBoundWeak_nonempty`: the certificate `ChebyshevBoundWeak`, which is
  `ChebyshevBound` with the upper factor `2` replaced by `log 4 ≈ 1.386` (Mathlib's
  `Chebyshev.theta_le_log4_mul_x`), is inhabited with threshold `ξ = 10^12`; hence
  `chebyshevBoundExplicit : ChebyshevBound`.
* `primeCountingHyp_of_theta_le`: any upper bound `θ(x) ≤ c·x` (large `x`) with `c < 3/2`
  implies `PrimeCountingHyp`, i.e. `π(x) ≤ 3x/(2 log x)` for all large `x`, by Mathlib's
  Abel-summation identity for `π` and the `o(x/log x)` estimate of its integral term.
* `primeCountingBoundExplicit : PrimeCountingBound`: the certificate of IUT IV,
  Proposition 1.6 with the factor `3/2`, from the previous item with `c = log 4 < 1.39`.
  Its threshold `η_prm` is the one extracted from Mathlib's `∀ᶠ` statement and is not
  explicit; only its existence enters the constants of Theorem 1.10 and Corollary 2.2.

## Remarks

The printed Propositions 2.1(ii) and 1.6 have the upper factors `4/3` and `4/3`; Mathlib's
`θ(x) ≤ (log 4)·x` has `log 4 = 1.386… > 4/3`, so the certificates carry the round factors
`2` (`ChebyshevBound`) and `3/2` (`PrimeCountingBound`) instead, which suffice for
`exists_prime_selection` and for Theorem 1.10 with the printed constants. The
existential propositions `ChebyshevUpperHyp`, `ChebyshevHyp` and `PrimeCountingHyp`
record the contents of the certificates, with the repackaging lemmas
`chebyshevBound_of_exists`, `chebyshevBound_of_upper` and `primeCountingBound_of_exists`;
all three propositions are proved (`chebyshevHyp_holds`, `primeCountingHyp_holds`).
-/

namespace Iut

open Real Filter Asymptotics

/-! ### The delegated hypotheses as propositions -/

/-- The content of `ChebyshevBound` as a proposition. -/
def ChebyshevHyp : Prop :=
  ∃ ξ : ℝ, 5 ≤ ξ ∧ (∀ x : ℝ, ξ ≤ x → 2 / 3 * x ≤ Chebyshev.theta x) ∧
    ∀ x : ℝ, ξ ≤ x → Chebyshev.theta x ≤ 2 * x

/-- The upper half of `ChebyshevHyp`: `θ(x) ≤ 2·x` for all large `x`. This is the only
part of `ChebyshevBound` not provable from Mathlib (`chebyshevBound_of_upper`). -/
def ChebyshevUpperHyp : Prop :=
  ∃ ξ : ℝ, ∀ x : ℝ, ξ ≤ x → Chebyshev.theta x ≤ 2 * x

/-- The content of `PrimeCountingBound` as a proposition: `π(x) ≤ 3x/(2 log x)` for all
large `x`. Proved from Mathlib in `primeCountingHyp_holds`. -/
def PrimeCountingHyp : Prop :=
  ∃ η : ℝ, 1 < η ∧ ∀ x : ℝ, η ≤ x → (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ 3 * x / (2 * Real.log x)

theorem chebyshevBound_of_exists (h : ChebyshevHyp) : Nonempty ChebyshevBound :=
  let ⟨ξ, h5, hl, hu⟩ := h
  ⟨⟨ξ, h5, hl, hu⟩⟩

theorem chebyshevHyp_of_nonempty (h : Nonempty ChebyshevBound) : ChebyshevHyp :=
  let ⟨c⟩ := h
  ⟨c.ξ, c.five_le, c.lower, c.upper⟩

theorem chebyshevHyp_iff : ChebyshevHyp ↔ Nonempty ChebyshevBound :=
  ⟨chebyshevBound_of_exists, chebyshevHyp_of_nonempty⟩

theorem primeCountingBound_of_exists (h : PrimeCountingHyp) : Nonempty PrimeCountingBound :=
  let ⟨η, h1, hb⟩ := h
  ⟨⟨η, h1, hb⟩⟩

theorem primeCountingHyp_of_nonempty (h : Nonempty PrimeCountingBound) : PrimeCountingHyp :=
  let ⟨c⟩ := h
  ⟨c.η, c.one_lt_η, c.bound⟩

theorem primeCountingHyp_iff : PrimeCountingHyp ↔ Nonempty PrimeCountingBound :=
  ⟨primeCountingBound_of_exists, primeCountingHyp_of_nonempty⟩

/-! ### The explicit lower Chebyshev bound -/

/-- **Explicit lower Chebyshev bound**: `(2/3)·x ≤ θ(x)` for all `x ≥ 10^12`, from
Mathlib's `Chebyshev.theta_ge'` (`(x - 1)·log 2 - log (x + 2) - 2√x·log x ≤ θ(x)`) and
`log 2 > 0.693 > 2/3`. The threshold is far from optimal. -/
theorem two_thirds_mul_le_theta {x : ℝ} (hx : (10 : ℝ) ^ 12 ≤ x) :
    2 / 3 * x ≤ Chebyshev.theta x := by
  have hx1 : 1 ≤ x := by linarith [show (1 : ℝ) ≤ 10 ^ 12 by norm_num]
  have hx0 : 0 < x := by linarith
  -- `t = x^(1/4)`
  set t : ℝ := Real.sqrt (Real.sqrt x) with ht
  have hs0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have htt : t * t = Real.sqrt x := Real.mul_self_sqrt hs0
  have hss : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
  have hx4 : x = t ^ 4 := by rw [show t ^ 4 = (t * t) * (t * t) by ring, htt, hss]
  have hsq : Real.sqrt x = t ^ 2 := by rw [← htt]; ring
  have ht1000 : 1000 ≤ t := by
    by_contra h
    push Not at h
    have h2 : t ^ 2 < 1000 ^ 2 := by nlinarith
    have h4 : t ^ 4 < 1000 ^ 4 := by
      have : (0 : ℝ) < 1000 ^ 2 + t ^ 2 := by positivity
      nlinarith [mul_pos (show (0 : ℝ) < 1000 ^ 2 - t ^ 2 by linarith) this]
    rw [← hx4] at h4
    norm_num at h4
    linarith
  have hlogx : Real.log x ≤ 4 * t := by
    rw [hx4, Real.log_pow]
    have := Real.log_le_sub_one_of_pos (show 0 < t by linarith)
    push_cast
    linarith
  have hlogx2 : Real.log (x + 2) ≤ 8 * t := by
    have h1 : x + 2 ≤ x ^ 2 := by
      nlinarith [mul_nonneg (show 0 ≤ x - 2 by linarith [show (2 : ℝ) ≤ 10 ^ 12 by norm_num])
        (show 0 ≤ x + 1 by linarith)]
    calc Real.log (x + 2) ≤ Real.log (x ^ 2) := Real.log_le_log (by linarith) h1
      _ = 2 * Real.log x := by rw [Real.log_pow]; push_cast; ring
      _ ≤ 8 * t := by linarith
  have hlog2 := Real.log_two_gt_d9
  have hge := Chebyshev.theta_ge' hx1
  rw [hsq] at hge
  have h3 : 2 * t ^ 2 * Real.log x ≤ 8 * t ^ 3 := by
    have : t ^ 2 * Real.log x ≤ t ^ 2 * (4 * t) :=
      mul_le_mul_of_nonneg_left hlogx (by positivity)
    nlinarith
  -- the main term: `(log 2 - 2/3)·x ≥ 0.0264·x`
  have hkey : 0.0264 * x ≤ (Real.log 2 - 2 / 3) * x :=
    mul_le_mul_of_nonneg_right (by norm_num at hlog2 ⊢; linarith) hx0.le
  -- the error terms are dominated for `t ≥ 1000`
  have h5 : 8 * t + 1 ≤ 8 * t ^ 3 := by nlinarith [pow_nonneg ht0 2]
  have h6 : 16 * t ^ 3 ≤ 0.0264 * t ^ 4 := by
    have := mul_nonneg (pow_nonneg ht0 3) (show 0 ≤ 0.0264 * t - 16 by linarith)
    nlinarith
  have hlog2' : Real.log 2 ≤ 1 := by
    have := Real.log_two_lt_d9
    linarith
  nlinarith

/-! ### The weak certificate reachable from Mathlib -/

/-- `ChebyshevBound` with Mathlib's upper factor `log 4 ≈ 1.386` in place of `2`.
Inhabited unconditionally (`chebyshevBoundWeak_nonempty`). -/
structure ChebyshevBoundWeak where
  /-- The threshold. -/
  ξ : ℝ
  /-- `ξ ≥ 5`. -/
  five_le : 5 ≤ ξ
  /-- The lower Chebyshev bound, with the factor `2/3` of `ChebyshevBound`. -/
  lower : ∀ x : ℝ, ξ ≤ x → 2 / 3 * x ≤ Chebyshev.theta x
  /-- The upper Chebyshev bound with Mathlib's factor `log 4`. -/
  upper : ∀ x : ℝ, ξ ≤ x → Chebyshev.theta x ≤ Real.log 4 * x

/-- `log 4 < 1.39`. -/
theorem log_four_lt : Real.log 4 < 1.39 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  have := Real.log_two_lt_d9
  push_cast
  linarith

namespace ChebyshevBoundWeak

/-- The upper bound with the round factor `2` (enough for `exists_prime_selection`). -/
theorem upper_two (c : ChebyshevBoundWeak) (x : ℝ) (hx : c.ξ ≤ x) :
    Chebyshev.theta x ≤ 2 * x := by
  have h0 : 0 ≤ x := by linarith [c.five_le]
  have := c.upper x hx
  nlinarith [log_four_lt]

/-- The upper bound with the factor `1.39`. -/
theorem upper_d2 (c : ChebyshevBoundWeak) (x : ℝ) (hx : c.ξ ≤ x) :
    Chebyshev.theta x ≤ 1.39 * x := by
  have h0 : 0 ≤ x := by linarith [c.five_le]
  have := c.upper x hx
  nlinarith [log_four_lt]

end ChebyshevBoundWeak

/-- The explicit weak certificate with threshold `10^12`. -/
noncomputable def chebyshevBoundWeak : ChebyshevBoundWeak where
  ξ := 10 ^ 12
  five_le := by norm_num
  lower _ hx := two_thirds_mul_le_theta hx
  upper _ hx := Chebyshev.theta_le_log4_mul_x (by linarith [show (0 : ℝ) ≤ 10 ^ 12 by norm_num])

theorem chebyshevBoundWeak_nonempty : Nonempty ChebyshevBoundWeak := ⟨chebyshevBoundWeak⟩

/-- `ChebyshevBound` from `ChebyshevBoundWeak` and the upper bound `θ(x) ≤ 2·x` for
large `x`. -/
theorem chebyshevBound_of_upper (h : ChebyshevUpperHyp) : Nonempty ChebyshevBound := by
  obtain ⟨ξ, hξ⟩ := h
  refine ⟨⟨max ξ (10 ^ 12), ?_, fun x hx => ?_, fun x hx => ?_⟩⟩
  · exact le_trans (by norm_num) (le_max_right _ _)
  · exact two_thirds_mul_le_theta (le_trans (le_max_right _ _) hx)
  · exact hξ x (le_trans (le_max_left _ _) hx)

/-- **The explicit Chebyshev certificate** (threshold `10^12`, upper factor `2`): the
`ChebyshevBound` input is unconditional. -/
noncomputable def chebyshevBoundExplicit : ChebyshevBound where
  ξ := 10 ^ 12
  five_le := by norm_num
  lower _ hx := two_thirds_mul_le_theta hx
  upper x hx := chebyshevBoundWeak.upper_two x hx

theorem chebyshevBound_nonempty : Nonempty ChebyshevBound := ⟨chebyshevBoundExplicit⟩

/-- The Chebyshev hypothesis is exactly its upper half. -/
theorem chebyshevHyp_iff_upper : ChebyshevHyp ↔ ChebyshevUpperHyp :=
  ⟨fun ⟨ξ, _, _, hu⟩ => ⟨ξ, hu⟩, fun h => chebyshevHyp_of_nonempty (chebyshevBound_of_upper h)⟩

/-- The Chebyshev hypothesis holds. -/
theorem chebyshevHyp_holds : ChebyshevHyp := chebyshevHyp_of_nonempty chebyshevBound_nonempty

/-! ### `PrimeCountingHyp` from an upper Chebyshev bound -/

/-- **`PrimeCountingHyp` from a Chebyshev upper bound with factor `< 3/2`**: if
`θ(x) ≤ c·x` for all `x ≥ ξ` with `c < 3/2`, then `π(x) ≤ 3x/(2 log x)` for all large `x`.
This follows Mathlib's proof of `Chebyshev.eventually_primeCounting_le`: the Abel-summation
identity `π(x) = θ(x)/log x + ∫₂ˣ θ(t)/(t log² t) dt` and the estimate `o(x / log x)` for
the integral. -/
theorem primeCountingHyp_of_theta_le {c ξ : ℝ} (hc : c < 3 / 2)
    (h : ∀ x : ℝ, ξ ≤ x → Chebyshev.theta x ≤ c * x) : PrimeCountingHyp := by
  have hε : 0 < 3 / 2 - c := by linarith
  have hev := (Chebyshev.integral_theta_div_log_sq_isLittleO.bound hε).and (eventually_ge_atTop 2)
  obtain ⟨η₀, hη₀⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max η₀ (max ξ 2), lt_of_lt_of_le (by norm_num) (le_trans (le_max_right _ _)
    (le_max_right _ _)), fun x hx => ?_⟩
  have hxη : η₀ ≤ x := le_trans (le_max_left _ _) hx
  have hxξ : ξ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx2 : 2 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  obtain ⟨hI, -⟩ := hη₀ x hxη
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hxlog : 0 ≤ x / Real.log x := div_nonneg (by linarith) hlog.le
  rw [Real.norm_eq_abs, Real.norm_of_nonneg hxlog] at hI
  have hI' : (∫ t in (2 : ℝ)..x, Chebyshev.theta t / (t * Real.log t ^ 2)) ≤
      (3 / 2 - c) * (x / Real.log x) := (le_abs_self _).trans hI
  rw [Chebyshev.primeCounting_eq_theta_div_log_add_integral hx2]
  have hθ : Chebyshev.theta x / Real.log x ≤ c * x / Real.log x :=
    div_le_div_of_nonneg_right (h x hxξ) hlog.le
  calc Chebyshev.theta x / Real.log x +
        ∫ t in (2 : ℝ)..x, Chebyshev.theta t / (t * Real.log t ^ 2)
      ≤ c * x / Real.log x + (3 / 2 - c) * (x / Real.log x) := add_le_add hθ hI'
    _ = 3 * x / (2 * Real.log x) := by field_simp; ring

/-- **The prime-counting hypothesis holds**: `π(x) ≤ 3x/(2 log x)` for all large `x`, from
Mathlib's `θ(x) ≤ (log 4)·x` and `log 4 < 1.39 < 3/2`. -/
theorem primeCountingHyp_holds : PrimeCountingHyp :=
  primeCountingHyp_of_theta_le (ξ := 0) (by linarith [log_four_lt])
    fun _ hx => Chebyshev.theta_le_log4_mul_x hx

/-- **The explicit prime-counting certificate** (IUT IV, Proposition 1.6 with the factor
`3/2`): the `PrimeCountingBound` input is unconditional. The threshold is the one
extracted from Mathlib's asymptotic statement. -/
noncomputable def primeCountingBoundExplicit : PrimeCountingBound :=
  Classical.choice (primeCountingBound_of_exists primeCountingHyp_holds)

theorem primeCountingBound_nonempty : Nonempty PrimeCountingBound :=
  ⟨primeCountingBoundExplicit⟩

end Iut
