/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Cor312.ThetaData.ReductionNorm
import Iut.Cor312.ThetaData.GlobalField
import Iut.Cor312.ThetaData.PlacesOver

/-!
# The place below a place, and the global valuation conditions at a multiplicative place

* `Iut.placeUnder w`: the finite place of `k` below a finite place `w` of `K ⊇ k`
  (the contraction of the prime), with `FinitePlace.LiesOver w (placeUnder w)`.
* At a place `w` of multiplicative reduction of `E/F` (`Iut.HasMultiplicativeReductionAt`:
  Mathlib's class over the completed integers for some global change of variables `C • E`),
  the `w`-adic valuations of the invariants of the model `C • E` satisfy `v_w(c₄) = 1`,
  `v_w(Δ) < 1` (`Iut.exists_variableChange_of_mult`), and consequently the invariant
  `j`-invariant satisfies `v_w(j) > 1` (`Iut.one_lt_valuation_j_of_mult`).
-/

namespace Iut

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WeierstrassCurve

section Under

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

/-- The prime of `𝓞 k` below a finite place of `K`. -/
noncomputable def primeUnder (w : FinitePlace K) : HeightOneSpectrum (𝓞 k) where
  asIdeal := w.maximalIdeal.asIdeal.comap (algebraMap (𝓞 k) (𝓞 K))
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot w.maximalIdeal.ne_bot
    exact Ideal.comap_ne_bot_of_integral_mem hx0 hx (Algebra.IsIntegral.isIntegral x)

/-- The finite place of `k` below a finite place of `K`. -/
noncomputable def placeUnder (w : FinitePlace K) : FinitePlace k :=
  FinitePlace.mk (primeUnder w)

lemma placeUnder_maximalIdeal (w : FinitePlace K) :
    (placeUnder (k := k) w).maximalIdeal.asIdeal =
      w.maximalIdeal.asIdeal.comap (algebraMap (𝓞 k) (𝓞 K)) := by
  rw [placeUnder, FinitePlace.maximalIdeal_mk]
  rfl

/-- `w` lies over the place below it. -/
lemma liesOver_placeUnder (w : FinitePlace K) : FinitePlace.LiesOver w (placeUnder (k := k) w) :=
  ⟨by rw [placeUnder_maximalIdeal]⟩

end Under

section Mult

variable {F : Type*} [Field F] [NumberField F] (E : WeierstrassCurve F) (w : FinitePlace F)

lemma baseChange_adicCompletion_eq :
    E.baseChange (w.maximalIdeal.adicCompletion F) = E.map (FinitePlace.embedding w.maximalIdeal) :=
  rfl

section Model

variable [(E.baseChange (w.maximalIdeal.adicCompletion F)).HasMultiplicativeReduction
  (w.maximalIdeal.adicCompletionIntegers F)]

/-- `v_w(c₄(E)) = 1` for a model `E` whose base change has multiplicative reduction. -/
lemma valuation_c₄_eq_one_of_baseChange : w.maximalIdeal.valuation F E.c₄ = 1 := by
  have h := norm_c₄_eq_one (E.baseChange (w.maximalIdeal.adicCompletion F))
  rw [baseChange_adicCompletion_eq, map_c₄, norm_eq_one_iff_valued, FinitePlace.embedding_apply,
    valuedAdicCompletion_eq_valuation'] at h
  exact h

/-- `v_w(Δ(E)) < 1` for a model `E` whose base change has multiplicative reduction. -/
lemma valuation_Δ_lt_one_of_baseChange : w.maximalIdeal.valuation F E.Δ < 1 := by
  have h := norm_Δ_lt_one (E.baseChange (w.maximalIdeal.adicCompletion F))
  rw [baseChange_adicCompletion_eq, map_Δ, norm_lt_one_iff_valued, FinitePlace.embedding_apply,
    valuedAdicCompletion_eq_valuation'] at h
  exact h

end Model

/-- At a place of multiplicative reduction there is a global change of variables `C` such that
the model `C • E` has multiplicative reduction over the completed integers (Mathlib's class),
with `v_w(c₄(C • E)) = 1` and `v_w(Δ(C • E)) < 1`. -/
lemma exists_variableChange_of_mult (hw : HasMultiplicativeReductionAt E w) :
    ∃ C : VariableChange F,
      ((C • E).baseChange (w.maximalIdeal.adicCompletion F)).HasMultiplicativeReduction
        (w.maximalIdeal.adicCompletionIntegers F) ∧
      w.maximalIdeal.valuation F (C • E).c₄ = 1 ∧ w.maximalIdeal.valuation F (C • E).Δ < 1 := by
  obtain ⟨C, hC⟩ := hw
  exact ⟨C, hC, valuation_c₄_eq_one_of_baseChange (C • E) w,
    valuation_Δ_lt_one_of_baseChange (C • E) w⟩

omit [NumberField F] in
lemma j_eq_inv_Δ_mul [E.IsElliptic] : E.j = E.Δ⁻¹ * E.c₄ ^ 3 := by
  rw [WeierstrassCurve.j, Units.val_inv_eq_inv_val, coe_Δ']

/-- `v_w(j(E)) > 1` at a place of multiplicative reduction (the `j`-invariant is invariant
under changes of variables). -/
lemma one_lt_valuation_j_of_mult [E.IsElliptic] (hw : HasMultiplicativeReductionAt E w) :
    1 < w.maximalIdeal.valuation F E.j := by
  obtain ⟨C, -, hc₄, hΔ⟩ := exists_variableChange_of_mult E w hw
  have hΔ0 : (C • E).Δ ≠ 0 := by rw [← coe_Δ']; exact (C • E).Δ'.ne_zero
  have hpos : 0 < w.maximalIdeal.valuation F (C • E).Δ := by
    rw [pos_iff_ne_zero]
    exact (Valuation.ne_zero_iff _).2 hΔ0
  rw [← variableChange_j E C, j_eq_inv_Δ_mul, map_mul, map_inv₀, map_pow, hc₄, one_pow, mul_one]
  exact (one_lt_inv₀ hpos).2 hΔ

end Mult

end Iut
