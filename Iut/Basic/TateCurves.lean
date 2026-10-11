/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TateCurvesTheta

/-!
# General facts on Tate parameters: the parameter of a `j`-invariant, uniformizer independence

TO MOVE: lana-agents/tate-curves-theta

Facts about Tate parameters over a normed field `K` that are not specific to IUT:

* `TateCurvesTheta.IsUniformizer.norm_eq`: any two uniformizers have the same norm, hence
  `TateParameter.orderZ_eq_orderZ`, `TateParameter.toOrdered_orderNat_eq`: the discrete
  normalized order of a Tate parameter does not depend on the uniformizer;
* `TateCurvesTheta.TateParameter.ofJ`: **the** Tate parameter with prescribed `j`-invariant
  `j` (`1 < ‖j‖`, `12 ≠ 0`), defined through
  `TateCurvesTheta.TateParameter.existsUnique_tateParameter_tateJ_eq`, with its characterizing
  property `ofJ_tateJ` and uniqueness `eq_ofJ`;
* `TateCurvesTheta.TateParameter.norm_q_ofJ`: `‖q‖ = ‖j‖⁻¹`.
-/

namespace TateCurvesTheta

variable {K : Type*} [NormedField K]

namespace IsUniformizer

/-- **Any two uniformizers have the same norm**: `‖π'‖ = ‖π‖ⁿ` and `‖π‖ = ‖π'‖ᵐ` with
`‖π‖, ‖π'‖ ∈ (0, 1)` force `n = m = 1`. -/
theorem norm_eq {π π' : K} (hπ : IsUniformizer π) (hπ' : IsUniformizer π') : ‖π‖ = ‖π'‖ := by
  obtain ⟨n, hn⟩ := hπ.generates (Units.mk0 π' hπ'.ne_zero)
  obtain ⟨m, hm⟩ := hπ'.generates (Units.mk0 π hπ.ne_zero)
  simp only [Units.val_mk0] at hn hm
  have hl := hπ.log_norm_neg
  have hl' := hπ'.log_norm_neg
  have hn' : Real.log ‖π'‖ = n * Real.log ‖π‖ := by rw [hn, Real.log_zpow]
  have hm' : Real.log ‖π‖ = m * Real.log ‖π'‖ := by rw [hm, Real.log_zpow]
  -- `n` is positive, and `n * m = 1`
  have hnpos : (0 : ℝ) < n := by
    by_contra h
    have h' := not_lt.mp h
    nlinarith
  have hnm : (n : ℝ) * m = 1 := by
    have h := hm'
    rw [hn'] at h
    have : Real.log ‖π‖ * (1 - (n : ℝ) * m) = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hl.ne
    · linarith
  have hnm' : n * m = 1 := by exact_mod_cast hnm
  have hn1 : n = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hnm' with h | h
    · exact h
    · exfalso
      have : (n : ℝ) = -1 := by exact_mod_cast h
      linarith
  rw [hn, hn1, zpow_one]

end IsUniformizer

namespace TateParameter

variable (t : TateParameter K)

/-- **The discrete order does not depend on the uniformizer.** -/
theorem orderZ_eq_orderZ {π π' : K} (hπ : IsUniformizer π) (hπ' : IsUniformizer π') :
    t.orderZ hπ = t.orderZ hπ' :=
  t.orderZ_eq_of_norm hπ (by rw [hπ.norm_eq hπ']; exact t.norm_q_eq_zpow hπ')

/-- **The natural-number order does not depend on the uniformizer.** -/
theorem toOrdered_orderNat_eq {π π' : K} (hπ : IsUniformizer π) (hπ' : IsUniformizer π') :
    (t.toOrdered hπ).orderNat = (t.toOrdered hπ').orderNat := by
  rw [toOrdered_orderNat, toOrdered_orderNat, t.orderZ_eq_orderZ hπ hπ']

/-- `ℓ` being prime to the order of a Tate parameter does not depend on the uniformizer. -/
theorem toOrdered_primeToOrder_congr {π π' : K} (hπ : IsUniformizer π)
    (hπ' : IsUniformizer π') (ℓ : ℕ) :
    (t.toOrdered hπ).PrimeToOrder ℓ ↔ (t.toOrdered hπ').PrimeToOrder ℓ := by
  rw [toOrdered_primeToOrder_iff, toOrdered_primeToOrder_iff, t.orderZ_eq_orderZ hπ hπ']

section OfJ

variable [IsUltrametricDist K] [CompleteSpace K]

/-- **The Tate parameter with `j`-invariant `j`**, for `1 < ‖j‖` (and `12 ≠ 0` in `K`): the
unique `q` with `j(E_q) = j` (`existsUnique_tateParameter_tateJ_eq`). -/
noncomputable def ofJ (h12 : (12 : K) ≠ 0) {j : K} (hj : 1 < ‖j‖) : TateParameter K :=
  (existsUnique_tateParameter_tateJ_eq h12 hj).exists.choose

/-- The `j`-invariant of the Tate curve of `ofJ j` is `j`. -/
theorem ofJ_tateJ (h12 : (12 : K) ≠ 0) {j : K} (hj : 1 < ‖j‖) : (ofJ h12 hj).tateJ = j :=
  (existsUnique_tateParameter_tateJ_eq h12 hj).exists.choose_spec

/-- **Uniqueness**: a Tate parameter whose Tate curve has `j`-invariant `j` is `ofJ j`. -/
theorem eq_ofJ (h12 : (12 : K) ≠ 0) {j : K} (hj : 1 < ‖j‖) {t : TateParameter K}
    (ht : t.tateJ = j) : t = ofJ h12 hj :=
  (existsUnique_tateParameter_tateJ_eq h12 hj).unique ht (ofJ_tateJ h12 hj)

/-- `‖q‖ = ‖j‖⁻¹` for the Tate parameter of `j`. -/
theorem norm_q_ofJ (h12 : (12 : K) ≠ 0) {j : K} (hj : 1 < ‖j‖) :
    ‖((ofJ h12 hj).q : K)‖ = ‖j‖⁻¹ := by
  conv_rhs => rw [← ofJ_tateJ h12 hj]
  rw [norm_tateJ _ h12, inv_inv]

end OfJ

end TateParameter

end TateCurvesTheta
