/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Cor312.ThetaData.GalCompletion
import Iut.Cor312.ThetaData.TateFamilyGalois

/-!
# The local automorphism at a Galois-fixed place, and the curve over the completion

For a Galois automorphism `σ ∈ Gal(K'/k)` fixing a finite place `w` of `K'`, the isometry
`K'_w ≃ K'_{σw}` of `Iut.galCompletion` becomes an automorphism `Iut.localAut σ w hfix` of
`K'_w` extending `σ`. For an elliptic curve `E` over a subfield `F` of `k`, the curve
`Iut.curveLoc E K' w = E ×_F K'_w` is fixed by this automorphism, and the points of `E(k)`
map to fixed points of `E(K'_w)`.
-/

namespace Iut

open NumberField WeierstrassCurve Iut.Anabelian
open scoped Classical Valued

universe u

noncomputable section

section Cast

variable {k : Type*} [Field k] [NumberField k]

/-- Transport along an equality of places. -/
def placeCast {w₁ w₂ : FinitePlace k} (h : w₁ = w₂) :
    localCompletion w₁ ≃+* localCompletion w₂ := by
  subst h
  exact RingEquiv.refl _

@[simp] lemma norm_placeCast {w₁ w₂ : FinitePlace k} (h : w₁ = w₂) (x : localCompletion w₁) :
    ‖placeCast h x‖ = ‖x‖ := by
  subst h
  rfl

lemma placeCast_embedding {w₁ w₂ : FinitePlace k} (h : w₁ = w₂) (x : k) :
    placeCast h (FinitePlace.embedding w₁.maximalIdeal x) =
      FinitePlace.embedding w₂.maximalIdeal x := by
  subst h
  rfl

end Cast

section LocalCurve

variable {F : Type u} [Field F] [NumberField F] (E : WeierstrassCurve F)
variable (K' : Type u) [Field K'] [NumberField K'] [Algebra F K'] (w : FinitePlace K')

/-- `E` over the completion `K'_w` of a number field `K' ⊇ F`. -/
abbrev curveLoc : WeierstrassCurve (localCompletion w) :=
  (E.map (algebraMap F K')).map (FinitePlace.embedding w.maximalIdeal)

end LocalCurve

section Aut

variable {k : Type u} [Field k] [NumberField k] {K' : Type u} [Field K'] [NumberField K']
  [Algebra k K'] (σ : K' ≃ₐ[k] K') (w : FinitePlace K') (hfix : galPlace σ w = w)

/-- The automorphism of `K'_w` extending `σ`, at a place fixed by `σ`. -/
def localAut : localCompletion w ≃+* localCompletion w :=
  (galCompletion σ w).trans (placeCast hfix)

lemma norm_localAut (x : localCompletion w) : ‖localAut σ w hfix x‖ = ‖x‖ := by
  rw [localAut, RingEquiv.trans_apply, norm_placeCast, norm_galCompletion]

lemma localAut_embedding (x : K') :
    localAut σ w hfix (FinitePlace.embedding w.maximalIdeal x) =
      FinitePlace.embedding w.maximalIdeal (σ x) := by
  rw [localAut, RingEquiv.trans_apply, galCompletion_embedding, placeCast_embedding]

variable {F : Type u} [Field F] [NumberField F] (E : WeierstrassCurve F) [Algebra F k]
  [Algebra F K'] [IsScalarTower F k K']

omit [NumberField k] [NumberField K'] [NumberField F] in
lemma σ_algebraMap (a : F) : σ (algebraMap F K' a) = algebraMap F K' a := by
  rw [IsScalarTower.algebraMap_apply F k K', AlgEquiv.commutes]

/-- The curve `E ×_F K'_w` is fixed by the local automorphism. -/
lemma map_curveLoc_localAut :
    (curveLoc E K' w).map (localAut σ w hfix : localCompletion w →+* localCompletion w) =
      curveLoc E K' w := by
  rw [curveLoc, map_map, map_map]
  ext <;> simp [map, localAut_embedding, σ_algebraMap]

omit [NumberField k] [NumberField K'] [NumberField F] in
/-- The curve identity `E ×_F k ×_k K' = E ×_F K'`. -/
lemma map_algebraMap_eq :
    (E.map (algebraMap F k)).map (algebraMap k K') = E.map (algebraMap F K') := by
  rw [map_map, ← IsScalarTower.algebraMap_eq]

/-- The points of `E(k)` in `E(K'_w)`. -/
def toLoc (R : (E.map (algebraMap F k)).toAffine.Point) : (curveLoc E K' w).toAffine.Point :=
  pointMap (E.map (algebraMap F K')) (FinitePlace.embedding w.maximalIdeal)
    (pointCongr (map_algebraMap_eq E (k := k) (K' := K'))
      (pointMap (E.map (algebraMap F k)) (algebraMap k K') R))

lemma toLoc_zero : toLoc w E (k := k) 0 = 0 := by
  simp only [toLoc, map_zero]

lemma toLoc_add (R R' : (E.map (algebraMap F k)).toAffine.Point) :
    toLoc w E (R + R') = toLoc w E R + toLoc w E R' := by
  simp only [toLoc, map_add]

lemma toLoc_nsmul (n : ℕ) (R : (E.map (algebraMap F k)).toAffine.Point) :
    toLoc w E (n • R) = n • toLoc w E R := by
  simp only [toLoc, map_nsmul]

lemma toLoc_injective : Function.Injective (toLoc w E (k := k)) := by
  unfold toLoc
  exact (pointMap_injective _ _).comp ((pointCongr _).injective.comp (pointMap_injective _ _))

/-- The points of `E(k)` are fixed by the local automorphism. -/
lemma pointMap_localAut_toLoc (R : (E.map (algebraMap F k)).toAffine.Point) :
    pointMap (curveLoc E K' w) (localAut σ w hfix : localCompletion w →+* localCompletion w)
        (toLoc w E R) =
      pointCongr (map_curveLoc_localAut σ w hfix E).symm (toLoc w E R) := by
  cases R with
  | zero =>
    change (pointMap _ _) (toLoc w E 0) = (pointCongr _) (toLoc w E 0)
    rw [toLoc_zero, map_zero, map_zero]
  | some x y h =>
    simp only [toLoc, pointMap_some, pointCongr_some]
    exact some_ext (by rw [RingEquiv.coe_toRingHom, localAut_embedding, AlgEquiv.commutes])
      (by rw [RingEquiv.coe_toRingHom, localAut_embedding, AlgEquiv.commutes])

end Aut

end

end Iut
