/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Concrete.Existence
import Iut.Cor312.ThetaData.PlaceUnder
import Iut.Cor312.ThetaData.BadPlaceNorm

/-!
# Construction of the Tate inputs of an elliptic curve

For an elliptic curve `E/F` over a number field (`Iut.EllipticCurveData`), the Tate
inputs `EllipticCurveData.TateInputs` — a Tate parameter of `E` at every place of
multiplicative reduction, and a uniformizer of every such completion — exist
unconditionally:

* at a place `w` of multiplicative reduction, `‖c₄‖ = 1` and `‖Δ‖ < 1` on `F_w`, hence
  `‖j(E)‖ > 1` (`Iut.EllipticCurveData.one_lt_norm_j`), and the `j`-parametrization of Tate
  curves (`TateCurvesTheta.TateParameter.exists_tateParameter_tateJ_eq`) yields a Tate
  parameter `q_w` with `j(E_{q_w}) = j(E)`;
* the image in `F_w` of a uniformizer of the `w`-adic valuation of `F` is a uniformizer of
  the norm of `F_w` in the sense of `TateCurvesTheta.IsUniformizer`
  (`Iut.exists_isUniformizer`).

The resulting inputs are `EllipticCurveData.tateInputs`.
-/

namespace Iut

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WeierstrassCurve
  TateCurvesTheta

/-! ## Uniformizers of the completions -/

section Uniformizer

variable {F : Type*} [Field F] [NumberField F] (w : FinitePlace F)

/-- The image in `F_w` of an element of `F` of valuation `exp (-1)` is a uniformizer of the
normed field `F_w`. -/
lemma isUniformizer_of_valuation_eq {π : F}
    (hπ : w.maximalIdeal.valuation F π = WithZero.exp (-1 : ℤ)) :
    IsUniformizer (FinitePlace.embedding w.maximalIdeal π) := by
  have hv : Valued.v (FinitePlace.embedding w.maximalIdeal π) = WithZero.exp (-1 : ℤ) := by
    rw [FinitePlace.embedding_apply, valuedAdicCompletion_eq_valuation', hπ]
  have hne : FinitePlace.embedding w.maximalIdeal π ≠ 0 := by
    rw [← (Valued.v).ne_zero_iff, hv]
    exact WithZero.exp_ne_zero
  refine ⟨hne, ?_, ?_⟩
  · rw [norm_lt_one_iff_valued, hv, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  · intro x
    set π' := FinitePlace.embedding w.maximalIdeal π with hπ'
    have hx0 : Valued.v (x : localCompletion w) ≠ 0 := (Valued.v).ne_zero_iff.mpr x.ne_zero
    refine ⟨-WithZero.log (Valued.v (x : localCompletion w)), ?_⟩
    -- the quotient `x / π ^ n` has valuation `1`, hence norm `1`
    have hunit : ‖(x : localCompletion w) / π' ^ (-WithZero.log (Valued.v (x : localCompletion w)))‖
        = 1 := by
      rw [norm_eq_one_iff_valued, map_div₀, map_zpow₀, hv, ← WithZero.exp_zsmul, smul_neg,
        smul_eq_mul, mul_one, neg_neg, WithZero.exp_log hx0, div_self hx0]
    rw [norm_div, norm_zpow] at hunit
    have hπpos : 0 < ‖π'‖ := norm_pos_iff.mpr hne
    have hpow : 0 < ‖π'‖ ^ (-WithZero.log (Valued.v (x : localCompletion w))) := zpow_pos hπpos _
    rw [div_eq_one_iff_eq hpow.ne'] at hunit
    exact hunit

/-- Every completion `F_w` has a uniformizer in the sense of `TateCurvesTheta.IsUniformizer`. -/
lemma exists_isUniformizer : ∃ π : localCompletion w, IsUniformizer π := by
  obtain ⟨π, hπ⟩ := w.maximalIdeal.valuation_exists_uniformizer F
  exact ⟨_, isUniformizer_of_valuation_eq w hπ⟩

end Uniformizer

/-! ## The Tate inputs of an elliptic curve -/

namespace EllipticCurveData

variable (C : EllipticCurveData.{u})

/-- At a place of multiplicative reduction, the `j`-invariant has norm `> 1` in `F_w`. -/
lemma one_lt_norm_j {w : FinitePlace C.F} (hw : w ∈ C.badAll) :
    1 < ‖FinitePlace.embedding w.maximalIdeal C.E.j‖ := by
  haveI : (C.E.map (FinitePlace.embedding w.maximalIdeal)).HasMultiplicativeReduction
    (w.maximalIdeal.adicCompletionIntegers C.F) := hw
  have hc₄ := norm_c₄_eq_one (C.E.map (FinitePlace.embedding w.maximalIdeal))
  have hΔ := norm_Δ_lt_one (C.E.map (FinitePlace.embedding w.maximalIdeal))
  have hΔ0 : (C.E.map (FinitePlace.embedding w.maximalIdeal)).Δ ≠ 0 := by
    rw [← coe_Δ']; exact (C.E.map (FinitePlace.embedding w.maximalIdeal)).Δ'.ne_zero
  have hΔpos : 0 < ‖(C.E.map (FinitePlace.embedding w.maximalIdeal)).Δ‖ := norm_pos_iff.mpr hΔ0
  have hj : 1 < ‖(C.E.map (FinitePlace.embedding w.maximalIdeal)).j‖ := by
    have : (C.E.map (FinitePlace.embedding w.maximalIdeal)).j =
        (C.E.map (FinitePlace.embedding w.maximalIdeal)).Δ⁻¹ *
          (C.E.map (FinitePlace.embedding w.maximalIdeal)).c₄ ^ 3 := by
      rw [j, Units.val_inv_eq_inv_val, coe_Δ']
    rw [this, norm_mul, norm_inv, norm_pow, hc₄, one_pow, mul_one]
    exact (one_lt_inv₀ hΔpos).mpr hΔ
  rwa [map_j] at hj

/-- The Tate parameter of `E` at a place of multiplicative reduction: the unique Tate
parameter of `F_w` whose Tate curve has `j`-invariant `j(E)`. -/
noncomputable def tateParameter {w : FinitePlace C.F} (hw : w ∈ C.badAll) :
    TateParameter (localCompletion w) :=
  (TateParameter.exists_tateParameter_tateJ_eq (twelve_ne_zero w) (C.one_lt_norm_j hw)).choose

lemma tateParameter_tateJ {w : FinitePlace C.F} (hw : w ∈ C.badAll) :
    (C.tateParameter hw).tateJ = FinitePlace.embedding w.maximalIdeal C.E.j :=
  (TateParameter.exists_tateParameter_tateJ_eq (twelve_ne_zero w)
    (C.one_lt_norm_j hw)).choose_spec

/-- **The Tate inputs** of an elliptic curve over a number field: Tate parameters at the
multiplicative places, via the `j`-parametrization of Tate curves, and uniformizers of the
completions. -/
noncomputable def tateInputs : C.TateInputs where
  tate _ hw := C.tateParameter hw
  tateJ_eq _ hw := C.tateParameter_tateJ hw
  unif w _ := (exists_isUniformizer w).choose
  unif_isUniformizer w _ := (exists_isUniformizer w).choose_spec

end EllipticCurveData

end Iut
