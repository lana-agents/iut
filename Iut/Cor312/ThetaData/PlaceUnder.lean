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
* At a place `w` of multiplicative reduction of `E/F` (Mathlib's class over the completed
  integers), the `w`-adic valuations of the global invariants satisfy `v_w(c₄) = 1`,
  `v_w(Δ) < 1` (`Iut.valuation_c₄_eq_one_of_mult`, `valuation_Δ_lt_one_of_mult`).
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

/-- `v_w(c₄(E)) = 1` at a place of multiplicative reduction. -/
lemma valuation_c₄_eq_one_of_mult (hw : HasMultiplicativeReductionAt E w) :
    w.maximalIdeal.valuation F E.c₄ = 1 := by
  haveI : (E.baseChange (w.maximalIdeal.adicCompletion F)).HasMultiplicativeReduction
    (w.maximalIdeal.adicCompletionIntegers F) := hw
  have h := norm_c₄_eq_one (E.baseChange (w.maximalIdeal.adicCompletion F))
  rw [baseChange_adicCompletion_eq, map_c₄, norm_eq_one_iff_valued, FinitePlace.embedding_apply,
    valuedAdicCompletion_eq_valuation'] at h
  exact h

/-- `v_w(Δ(E)) < 1` at a place of multiplicative reduction. -/
lemma valuation_Δ_lt_one_of_mult (hw : HasMultiplicativeReductionAt E w) :
    w.maximalIdeal.valuation F E.Δ < 1 := by
  haveI : (E.baseChange (w.maximalIdeal.adicCompletion F)).HasMultiplicativeReduction
    (w.maximalIdeal.adicCompletionIntegers F) := hw
  have h := norm_Δ_lt_one (E.baseChange (w.maximalIdeal.adicCompletion F))
  rw [baseChange_adicCompletion_eq, map_Δ, norm_lt_one_iff_valued, FinitePlace.embedding_apply,
    valuedAdicCompletion_eq_valuation'] at h
  exact h

end Mult

end Iut
