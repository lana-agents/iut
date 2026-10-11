/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Basic.TateCurves
import Iut.Cor312.ThetaData.PlaceUnder
import Iut.Cor312.ThetaData.ValuationTransfer
import Iut.Cor312.ThetaData.BadPlaceNorm

/-!
# The Tate parameter of `E` at a place of multiplicative reduction (derived)

For an elliptic curve `E` over a number field `F` and a finite place `w` at which `E` has
multiplicative reduction (`Iut.HasMultiplicativeReductionAt`), the image of `j(E)` in the
completion `F_w` has norm `> 1` (`Iut.one_lt_norm_j_of_mult`), so the `j`-parametrization of
Tate curves gives **the** Tate parameter `q_w` of `E` at `w`: the unique `q` with
`j(E_q) = j(E)` (`Iut.tateParameterAt`, `Iut.tateParameterAt_tateJ`,
`Iut.eq_tateParameterAt`). Its normalized integer order `ord_w(q_w)` (`Iut.qOrderAt`) is
computed with respect to a uniformizer of `F_w` (`Iut.exists_isUniformizer`), and does not
depend on that choice (`Iut.orderNat_eq_qOrderAt`). These are the derived local `q`-parameters
of initial Θ-data (IUT I, Definition 3.1(c)); nothing here is chosen data.
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

/-- A uniformizer of `F_w` (a choice; every statement made with it is independent of it, see
`Iut.orderNat_eq_qOrderAt`). -/
noncomputable def unifAt : localCompletion w := (exists_isUniformizer w).choose

lemma isUniformizer_unifAt : IsUniformizer (unifAt w) := (exists_isUniformizer w).choose_spec

end Uniformizer

/-! ## The Tate parameter at a place of multiplicative reduction -/

section TateParameterAt

variable {F : Type*} [Field F] [NumberField F] (E : WeierstrassCurve F) [E.IsElliptic]
  {w : FinitePlace F}

/-- At a place of multiplicative reduction, the `j`-invariant has norm `> 1` in `F_w`
(`Iut.one_lt_valuation_j_of_mult`, via a minimal model `C • E`). -/
theorem one_lt_norm_j_of_mult (hw : HasMultiplicativeReductionAt E w) :
    1 < ‖FinitePlace.embedding w.maximalIdeal E.j‖ :=
  not_le.1 fun h => not_le.2 (one_lt_valuation_j_of_mult E w hw) ((norm_emb_le_one_iff _).1 h)

/-- **The Tate parameter `q_w` of `E` at a place of multiplicative reduction** (derived): the
unique Tate parameter of `F_w` whose Tate curve has `j`-invariant the image of `j(E)`. -/
noncomputable def tateParameterAt (hw : HasMultiplicativeReductionAt E w) :
    TateParameter (localCompletion w) :=
  TateParameter.ofJ (twelve_ne_zero w) (one_lt_norm_j_of_mult E hw)

/-- The Tate curve of `q_w` has `j`-invariant `j(E)`. -/
theorem tateParameterAt_tateJ (hw : HasMultiplicativeReductionAt E w) :
    (tateParameterAt E hw).tateJ = FinitePlace.embedding w.maximalIdeal E.j :=
  TateParameter.ofJ_tateJ _ _

/-- **Uniqueness of `q_w`**: every Tate parameter of `F_w` whose Tate curve has `j`-invariant
`j(E)` is `q_w`. -/
theorem eq_tateParameterAt (hw : HasMultiplicativeReductionAt E w)
    {t : TateParameter (localCompletion w)}
    (ht : t.tateJ = FinitePlace.embedding w.maximalIdeal E.j) : t = tateParameterAt E hw :=
  TateParameter.eq_ofJ _ _ ht

/-- **The normalized order `ord_w(q_w)`** of the Tate parameter, a positive integer (computed
with the uniformizer `Iut.unifAt w`; independent of it by `Iut.orderNat_eq_qOrderAt`). -/
noncomputable def qOrderAt (hw : HasMultiplicativeReductionAt E w) : ℕ :=
  ((tateParameterAt E hw).toOrdered (isUniformizer_unifAt w)).orderNat

theorem qOrderAt_pos (hw : HasMultiplicativeReductionAt E w) : 0 < qOrderAt E hw :=
  ((tateParameterAt E hw).toOrdered (isUniformizer_unifAt w)).orderNat_pos

/-- **`ord_w(q_w)` is intrinsic**: for every Tate parameter `t` of `E` at `w` (necessarily
`q_w`) and every uniformizer `π` of `F_w`, the order of `t` with respect to `π` is
`qOrderAt`. -/
theorem orderNat_eq_qOrderAt (hw : HasMultiplicativeReductionAt E w)
    {t : TateParameter (localCompletion w)}
    (ht : t.tateJ = FinitePlace.embedding w.maximalIdeal E.j) {π : localCompletion w}
    (hπ : IsUniformizer π) : (t.toOrdered hπ).orderNat = qOrderAt E hw := by
  rw [eq_tateParameterAt E hw ht, qOrderAt, TateParameter.toOrdered_orderNat_eq]

end TateParameterAt

end Iut
