/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Concrete.ThetaLocalConstruct.EmbedCompletion
import Iut.Cor312.ThetaData.TateFamily
import Iut.Cor312.ThetaData.BadPlaceNorm

/-!
# Compatibility of the Tate parameters of `F_w` and `K_v`

The initial Θ-data carry two kinds of Tate parameters at a bad place: the parameter
`q_w ∈ F_w^×` of `E` over the completion of `F` (`AdmissiblePrimeData.tate`, pinned by
`j(E_{q_w}) = j(E)`), and the Tate structures of `E` over the completions `K_v` of the
`ℓ`-torsion field (`TateFamily.S`, pinned by the coordinates of the Tate parametrization).
Both parameters are determined by the `j`-invariant of `E` (uniqueness of the Tate parameter
with a given `j`-invariant, `TateCurvesTheta.TateParameter.tateJ_injective`), and the
comparison map `F_w → K_v` carries `j(E_{q_w})` to `j(E_{q'})` for `q'` the image of `q_w`
(`Iut.TateParameter.tateJ_embed`, naturality of the Eisenstein series under the continuous
ring homomorphism). Hence the Tate parameter of the Tate structure at `v` is the image of
`q_w` (`Iut.TateStructure.t_q_eq_embedCompletion`).
-/

namespace Iut

open NumberField WeierstrassCurve TateCurvesTheta
open scoped Valued

noncomputable section

section Embed

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  {v : FinitePlace K} {w : FinitePlace k} (hvw : FinitePlace.LiesOver v w)

/-- The image of a Tate parameter of `k_w` in `K_v`. -/
def embedTateParameter (t : TateParameter (localCompletion w)) :
    TateParameter (localCompletion v) where
  q := Units.map (embedCompletion hvw).toMonoidHom t.q
  norm_lt_one := by
    rw [Units.coe_map]
    change ‖embedCompletion hvw (t.q : localCompletion w)‖ < 1
    rw [norm_embedCompletion_lt_one_iff]
    exact t.norm_lt_one

variable (t : TateParameter (localCompletion w))

@[simp] lemma embedTateParameter_q_coe :
    ((embedTateParameter hvw t).q : localCompletion v) =
      embedCompletion hvw (t.q : localCompletion w) :=
  Units.coe_map _ _

/-- Naturality of the Eisenstein series under the comparison map. -/
lemma eisenstein_embed (n : ℕ) :
    embedCompletion hvw (t.eisenstein n) = (embedTateParameter hvw t).eisenstein n := by
  unfold TateParameter.eisenstein
  rw [(t.eisenstein_summand_summable n).map_tsum (embedCompletion hvw)
    (continuous_embedCompletion hvw)]
  refine tsum_congr fun m => ?_
  simp only [map_div₀, map_mul, map_pow, map_natCast, map_sub, map_one,
    embedTateParameter_q_coe]

/-- The Tate curve of the image is the image of the Tate curve. -/
lemma tateCurve_embed :
    t.tateCurve.map (embedCompletion hvw) = (embedTateParameter hvw t).tateCurve := by
  ext <;> simp [WeierstrassCurve.map, TateParameter.tateCurve, TateParameter.a₄,
    TateParameter.a₆, eisenstein_embed, map_ofNat]

/-- The `j`-invariant of the Tate curve is natural under the comparison map. -/
lemma tateJ_embed : embedCompletion hvw t.tateJ = (embedTateParameter hvw t).tateJ := by
  rw [TateParameter.tateJ_def, TateParameter.tateJ_def, map_div₀, map_pow,
    ← WeierstrassCurve.map_c₄, ← WeierstrassCurve.map_Δ, tateCurve_embed]

end Embed

/-! ### The Tate parameter of a Tate structure is determined by `j` -/

section Structure

variable {k : Type*} [Field k] [Valued k (WithZero (Multiplicative ℤ))]
  [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))] [CompleteSpace k]

omit [CompleteSpace k] in
/-- The `j`-invariant of the Tate parameter of a Tate structure on `E` is `c₄(E)³/Δ(E)`. -/
lemma TateStructure.tateJ_eq {E : WeierstrassCurve k} (S : TateStructure E) :
    S.t.tateJ = E.c₄ ^ 3 / E.Δ := by
  rw [TateParameter.tateJ_def, ← S.hC, WeierstrassCurve.variableChange_c₄,
    WeierstrassCurve.variableChange_Δ]
  have hu : ((S.C.u⁻¹ : kˣ) : k) ≠ 0 := Units.ne_zero _
  rw [mul_pow, ← pow_mul, show 4 * 3 = 12 from rfl]
  exact mul_div_mul_left _ _ (pow_ne_zero _ hu)

end Structure

/-! ### The Θ-data setting -/

section ThetaData

universe u

variable {F : Type u} [Field F] [NumberField F] (E : WeierstrassCurve F) [E.IsElliptic]
variable {Fbar : Type u} [Field Fbar] [Algebra F Fbar]
variable (K : IntermediateField F Fbar) [NumberField ↥K]

omit [NumberField F] in
/-- The `j`-invariant of an elliptic curve as `c₄³/Δ`. -/
lemma j_eq_div : E.j = E.c₄ ^ 3 / E.Δ := by
  rw [WeierstrassCurve.j, div_eq_inv_mul]
  congr 1
  rw [← WeierstrassCurve.coe_Δ', ← Units.val_inv_eq_inv_val]

variable {E K}

/-- **The Tate parameter of the Tate structure at `v` is the image of the Tate parameter at
`w`**, for `v ∣ w` and `t` a Tate parameter of `F_w` whose Tate curve has `j`-invariant
`j(E)`. -/
theorem TateStructure.t_q_eq_embedCompletion {v : FinitePlace ↥K} {w : FinitePlace F}
    (hvw : FinitePlace.LiesOver v w) (S : TateStructure (curveKw E K v))
    (t : TateParameter (localCompletion w))
    (ht : t.tateJ = FinitePlace.embedding w.maximalIdeal E.j) :
    (S.t.q : localCompletion v) = embedCompletion hvw (t.q : localCompletion w) := by
  have h12 : (12 : localCompletion v) ≠ 0 := twelve_ne_zero v
  have hJ : (embedTateParameter hvw t).tateJ = S.t.tateJ := by
    rw [← tateJ_embed, ht, embedCompletion_embedding, S.tateJ_eq, j_eq_div]
    simp only [curveKw, curveK, WeierstrassCurve.map_c₄, WeierstrassCurve.map_Δ, map_div₀,
      map_pow]
  have := TateParameter.tateJ_injective (embedTateParameter hvw t) S.t h12 hJ
  rw [← this, embedTateParameter_q_coe]

end ThetaData

end

end Iut
