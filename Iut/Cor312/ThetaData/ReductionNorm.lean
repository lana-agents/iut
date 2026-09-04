/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Cor312.ThetaData.AdmissiblePrime

/-!
# Reduction predicates in terms of the norm of the completed local field

Mathlib's reduction theory (`WeierstrassCurve.HasMultiplicativeReduction`,
`WeierstrassCurve.HasSplitMultiplicativeReduction`, …) over a discrete valuation ring `R`
with fraction field `k` is phrased through the `maximalIdeal`-adic valuation
`IsDedekindDomain.HeightOneSpectrum.valuation k (IsDiscreteValuationRing.maximalIdeal R)`.
For the completed local fields `F_w = localCompletion w` of a number field, the repo
works instead with the norm `‖·‖` induced by the valuation `Valued.v` of the completion.

This file bridges the two:

* in general, for a DVR `R ⊆ k` whose image is the set `{x | v x ≤ 1}` of some valuation
  `v` of `k`, the `maximalIdeal`-adic valuation of `R` is *equivalent* to `v`
  (`Iut.valuation_isEquiv_of_range`), so the conditions `≤ 1`, `< 1`, `= 1` may be
  transported freely;
* for `k = F_w` and `R = 𝒪_w = adicCompletionIntegers`, this gives
  `Iut.valuation_le_one_iff`, `Iut.valuation_lt_one_iff`, `Iut.valuation_eq_one_iff` in
  terms of `‖x‖`;
* for a curve `W` over `F_w` with multiplicative reduction over `𝒪_w`:
  `‖W.c₄‖ = 1`, `‖W.Δ‖ < 1`, and integrality `‖W.aᵢ‖ ≤ 1`;
* for split multiplicative reduction: a tangent root `r` with `‖r‖ ≤ 1` at which the
  splitting quadratic `c₄ T² + a₁c₄ T − (54 b₆ − 3 b₂ b₄ + a₂ c₄)` has norm `< 1`
  (`Iut.exists_tangent_root`).
-/

namespace Iut

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsDiscreteValuationRing
  IsLocalRing WeierstrassCurve NumberField
open scoped WithZero

/-! ## Equivalence of the DVR valuation with a valuation having the same integers -/

section General

variable {k : Type*} [Field k] (R : Type*) [CommRing R] [IsDomain R]
  [IsDiscreteValuationRing R] [Algebra R k] [IsFractionRing R k]
  {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (v : Valuation k Γ)

/-- For a DVR `R` with fraction field `k`, an element of `k` has `maximalIdeal`-adic valuation
`≤ 1` if and only if it lies in the image of `R`. -/
lemma valuation_maximalIdeal_le_one_iff (x : k) :
    valuation k (maximalIdeal R) x ≤ 1 ↔ ∃ r : R, algebraMap R k r = x :=
  ⟨fun hx => exists_lift_of_le_one hx, fun ⟨r, hr⟩ => hr ▸ valuation_le_one _ r⟩

/-- If the valuation ring of `v` is (the image of) `R`, then the `maximalIdeal`-adic valuation
of `R` is equivalent to `v`. -/
lemma valuation_isEquiv_of_range (h : ∀ x : k, v x ≤ 1 ↔ ∃ r : R, algebraMap R k r = x) :
    (valuation k (maximalIdeal R)).IsEquiv v := by
  rw [Valuation.isEquiv_iff_val_le_one]
  intro x
  rw [valuation_maximalIdeal_le_one_iff, h]

end General

/-! ## The completed local field at a finite place -/

section Local

variable {F : Type*} [Field F] [NumberField F] (w : FinitePlace F)

/-- The valuation ring of `Valued.v` on `F_w` is `𝒪_w = adicCompletionIntegers`, as the range
of the inclusion. -/
lemma valued_le_one_iff_range (x : localCompletion w) :
    Valued.v x ≤ 1 ↔
      ∃ r : w.maximalIdeal.adicCompletionIntegers F,
        algebraMap (w.maximalIdeal.adicCompletionIntegers F) (localCompletion w) r = x := by
  rw [← mem_adicCompletionIntegers]
  exact ⟨fun hx => ⟨⟨x, hx⟩, rfl⟩, fun ⟨r, hr⟩ => hr ▸ r.2⟩

/-- The `maximalIdeal`-adic valuation of `𝒪_w` on `F_w` is equivalent to the valuation
`Valued.v` of the completion. -/
lemma valuation_isEquiv_valued :
    (valuation (localCompletion w) (maximalIdeal (w.maximalIdeal.adicCompletionIntegers F))).IsEquiv
      (Valued.v : Valuation (localCompletion w) ℤᵐ⁰) :=
  valuation_isEquiv_of_range _ _ (valued_le_one_iff_range w)

/-- The norm on `F_w` and the valuation `Valued.v` agree on the condition `≤ 1`. -/
lemma norm_le_one_iff_valued (x : localCompletion w) : ‖x‖ ≤ 1 ↔ Valued.v x ≤ 1 :=
  Valued.toNormedField.norm_le_one_iff

/-- The norm on `F_w` and the valuation `Valued.v` agree on the condition `< 1`. -/
lemma norm_lt_one_iff_valued (x : localCompletion w) : ‖x‖ < 1 ↔ Valued.v x < 1 :=
  Valued.toNormedField.norm_lt_one_iff

/-- The norm on `F_w` and the valuation `Valued.v` agree on the condition `= 1`. -/
lemma norm_eq_one_iff_valued (x : localCompletion w) : ‖x‖ = 1 ↔ Valued.v x = 1 := by
  simp only [le_antisymm_iff, norm_le_one_iff_valued, Valued.toNormedField.one_le_norm_iff]

/-- `v_w(x) ≤ 1 ↔ ‖x‖ ≤ 1` on `F_w`, for the `maximalIdeal`-adic valuation of `𝒪_w` used by
Mathlib's reduction theory. -/
lemma valuation_le_one_iff (x : localCompletion w) :
    valuation (localCompletion w) (maximalIdeal (w.maximalIdeal.adicCompletionIntegers F)) x ≤ 1 ↔
      ‖x‖ ≤ 1 := by
  rw [norm_le_one_iff_valued]
  exact (valuation_isEquiv_valued w).le_one_iff_le_one

/-- `v_w(x) < 1 ↔ ‖x‖ < 1` on `F_w`. -/
lemma valuation_lt_one_iff (x : localCompletion w) :
    valuation (localCompletion w) (maximalIdeal (w.maximalIdeal.adicCompletionIntegers F)) x < 1 ↔
      ‖x‖ < 1 := by
  rw [norm_lt_one_iff_valued]
  exact (valuation_isEquiv_valued w).lt_one_iff_lt_one

/-- `v_w(x) = 1 ↔ ‖x‖ = 1` on `F_w`. -/
lemma valuation_eq_one_iff (x : localCompletion w) :
    valuation (localCompletion w) (maximalIdeal (w.maximalIdeal.adicCompletionIntegers F)) x = 1 ↔
      ‖x‖ = 1 := by
  rw [norm_eq_one_iff_valued]
  exact (valuation_isEquiv_valued w).eq_one_iff_eq_one

/-- Elements of `𝒪_w` have norm `≤ 1` in `F_w`. -/
lemma norm_algebraMap_le_one (r : w.maximalIdeal.adicCompletionIntegers F) :
    ‖algebraMap (w.maximalIdeal.adicCompletionIntegers F) (localCompletion w) r‖ ≤ 1 :=
  (norm_le_one_iff_valued w _).2 r.2

end Local

/-! ## Multiplicative reduction in terms of the norm -/

section Multiplicative

variable {F : Type*} [Field F] [NumberField F] {w : FinitePlace F}
  (W : WeierstrassCurve (localCompletion w))

section Integral

variable [W.IsIntegral (w.maximalIdeal.adicCompletionIntegers F)]

lemma norm_a₁_le_one : ‖W.a₁‖ ≤ 1 := by
  rw [← integralModel_a₁_eq (w.maximalIdeal.adicCompletionIntegers F) W]
  exact norm_algebraMap_le_one w _

lemma norm_a₂_le_one : ‖W.a₂‖ ≤ 1 := by
  rw [← integralModel_a₂_eq (w.maximalIdeal.adicCompletionIntegers F) W]
  exact norm_algebraMap_le_one w _

lemma norm_a₃_le_one : ‖W.a₃‖ ≤ 1 := by
  rw [← integralModel_a₃_eq (w.maximalIdeal.adicCompletionIntegers F) W]
  exact norm_algebraMap_le_one w _

lemma norm_a₄_le_one : ‖W.a₄‖ ≤ 1 := by
  rw [← integralModel_a₄_eq (w.maximalIdeal.adicCompletionIntegers F) W]
  exact norm_algebraMap_le_one w _

lemma norm_a₆_le_one : ‖W.a₆‖ ≤ 1 := by
  rw [← integralModel_a₆_eq (w.maximalIdeal.adicCompletionIntegers F) W]
  exact norm_algebraMap_le_one w _

lemma norm_Δ_le_one : ‖W.Δ‖ ≤ 1 := by
  rw [← integralModel_Δ_eq (w.maximalIdeal.adicCompletionIntegers F) W]
  exact norm_algebraMap_le_one w _

lemma norm_c₄_le_one : ‖W.c₄‖ ≤ 1 := by
  rw [← integralModel_c₄_eq (w.maximalIdeal.adicCompletionIntegers F) W]
  exact norm_algebraMap_le_one w _

end Integral

section MultReduction

variable [W.HasMultiplicativeReduction (w.maximalIdeal.adicCompletionIntegers F)]

/-- Multiplicative reduction: `‖c₄‖ = 1`. -/
lemma norm_c₄_eq_one : ‖W.c₄‖ = 1 :=
  (valuation_eq_one_iff w _).1 HasMultiplicativeReduction.multiplicativeReduction

/-- Bad reduction: `‖Δ‖ < 1`. -/
lemma norm_Δ_lt_one : ‖W.Δ‖ < 1 :=
  (valuation_lt_one_iff w _).1 HasMultiplicativeReduction.badReduction

end MultReduction

/-! ## Split multiplicative reduction: a tangent root -/

section Split

open Polynomial

variable [W.HasSplitMultiplicativeReduction (w.maximalIdeal.adicCompletionIntegers F)]

/-- Split multiplicative reduction: the quadratic `c₄ T² + a₁c₄ T − (54 b₆ − 3 b₂ b₄ + a₂ c₄)`
(whose reduction defines the tangent directions at the node) has an integral root modulo the
maximal ideal, i.e. an `r` with `‖r‖ ≤ 1` at which it takes a value of norm `< 1`. -/
lemma exists_tangent_root :
    ∃ r : localCompletion w, ‖r‖ ≤ 1 ∧
      ‖W.c₄ * r ^ 2 + W.a₁ * W.c₄ * r - (54 * W.b₆ - 3 * W.b₂ * W.b₄ + W.a₂ * W.c₄)‖ < 1 := by
  set R := w.maximalIdeal.adicCompletionIntegers F with hR
  set p : R[X] := C (W.integralModel R).c₄ * X ^ 2 +
    C ((W.integralModel R).a₁ * (W.integralModel R).c₄) * X -
    C (54 * (W.integralModel R).b₆ - 3 * (W.integralModel R).b₂ * (W.integralModel R).b₄ +
      (W.integralModel R).a₂ * (W.integralModel R).c₄) with hp
  have hs : Splits (p.map (algebraMap R (ResidueField R))) :=
    HasSplitMultiplicativeReduction.splitMultiplicativeReduction (R := R) (W := W)
  -- the leading coefficient `c₄` is a unit of `R`
  have hc₄ : (W.integralModel R).c₄ ∉ IsLocalRing.maximalIdeal R := by
    change (W.integralModel R).c₄ ∉ (IsDiscreteValuationRing.maximalIdeal R).asIdeal
    rw [← valuation_lt_one_iff_mem (K := localCompletion w) (maximalIdeal R), not_lt]
    change 1 ≤ valuation (localCompletion w) (maximalIdeal R)
      (algebraMap R (localCompletion w) (W.integralModel R).c₄)
    rw [integralModel_c₄_eq R W]
    exact HasMultiplicativeReduction.multiplicativeReduction.ge
  have hlead : algebraMap R (ResidueField R) (W.integralModel R).c₄ ≠ 0 := by
    rw [ResidueField.algebraMap_eq, ne_eq, residue_eq_zero_iff]
    exact hc₄
  have hdeg : (p.map (algebraMap R (ResidueField R))).degree ≠ 0 := by
    have : p.map (algebraMap R (ResidueField R)) =
        C (algebraMap R (ResidueField R) (W.integralModel R).c₄) * X ^ 2 +
          C (algebraMap R (ResidueField R) ((W.integralModel R).a₁ * (W.integralModel R).c₄)) * X +
          C (- algebraMap R (ResidueField R) (54 * (W.integralModel R).b₆ -
            3 * (W.integralModel R).b₂ * (W.integralModel R).b₄ +
            (W.integralModel R).a₂ * (W.integralModel R).c₄)) := by
      rw [hp, sub_eq_add_neg]
      simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C,
        Polynomial.map_X, Polynomial.map_neg, _root_.map_neg]
    rw [this, degree_quadratic hlead]
    decide
  obtain ⟨a, ha⟩ := hs.exists_eval_eq_zero hdeg
  obtain ⟨r, rfl⟩ := residue_surjective (R := R) a
  -- `p(r)` lies in the maximal ideal
  have hpr : p.eval r ∈ IsLocalRing.maximalIdeal R := by
    rw [← residue_eq_zero_iff, ← ha, eval_map, ResidueField.algebraMap_eq, eval₂_hom]
  have hval : valuation (localCompletion w) (maximalIdeal R) (algebraMap R (localCompletion w)
      (p.eval r)) < 1 :=
    (valuation_lt_one_iff_mem (K := localCompletion w) (maximalIdeal R) _).2 hpr
  refine ⟨algebraMap R (localCompletion w) r, norm_algebraMap_le_one w r, ?_⟩
  rw [← valuation_lt_one_iff]
  convert hval using 2
  rw [hp]
  simp only [eval_sub, eval_add, eval_mul, eval_C, eval_X, eval_pow, eval_ofNat, map_sub, map_add,
    map_mul, map_pow, map_ofNat, integralModel_c₄_eq, integralModel_a₁_eq, integralModel_a₂_eq,
    integralModel_b₂_eq, integralModel_b₄_eq, integralModel_b₆_eq]

end Split

end Multiplicative

end Iut
