/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Cor312.ThetaData.GalCompletion
import Iut.Cor312.ThetaData.TateStructureTransport
import Iut.Cor312.ThetaData.TateStructureUnique

/-!
# Galois equivariance of an arbitrary family of Tate structures

The Galois-equivariance fields of `Iut.TateFamily` hold for **any** choice of Tate structures
`S w` at the bad places `w` of `K`: by the uniqueness of Tate structures up to sign
(`Iut.TateStructure.graphLine_eq`, `isCanonical_congr`), the graph line and the canonical
generators at `σ·w` may be computed from the transport of `S w` along the isometric
isomorphism `σ_w : K_w ≃ K_{σ·w}` (`Iut.galCompletion`, `Iut.TateStructure.baseChange`), and
the transported structure lives on `E ×_F K_{σ·w}` because `σ_w` extends `σ`
(`Iut.map_curveKw`). Reading everything on `E(K)`, this is the equivariance
(`Iut.graphLine_galPlace_of_forall`, `Iut.isCanonical_galPlace_of_forall`), and any family of
Tate structures gives a `TateFamily` (`Iut.TateFamily.ofStructures`).
-/

namespace Iut

open WeierstrassCurve NumberField Iut.Anabelian
open scoped Classical Valued

universe u

noncomputable section

/-! ### Transport of Tate structures along an equality of curves -/

section Congr

variable {k : Type u} [Field k]

/-- Transport of a point of `.some` form along an equality of curves. -/
lemma pointCongr_some {W W' : WeierstrassCurve k} (h : W = W') {x y : k}
    (hxy : W.toAffine.Nonsingular x y) :
    pointCongr h (.some x y hxy) = .some x y (h ▸ hxy) := by
  subst h
  rfl

variable [Valued k (WithZero (Multiplicative ℤ))]
  [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))] [CompleteSpace k]

namespace TateStructure

/-- Transport of a Tate structure along an equality of curves. -/
def congr {W W' : WeierstrassCurve k} (h : W = W') (S : TateStructure W) : TateStructure W' := by
  subst h
  exact S

/-- The graph line of the transported structure. -/
theorem graphLine_congr {W W' : WeierstrassCurve k} (h : W = W') (S : TateStructure W) (ℓ : ℕ) :
    (S.congr h).graphLine ℓ = (S.graphLine ℓ).map (pointCongr h).toAddMonoidHom := by
  subst h
  ext P
  rw [AddSubgroup.mem_map_equiv]
  rfl

omit [CompleteSpace k] in
/-- The canonical generators of the transported structure. -/
theorem isCanonical_congr' {W W' : WeierstrassCurve k} (h : W = W') (S : TateStructure W) (ℓ : ℕ)
    (P : W.toAffine.Point) : (S.congr h).IsCanonical ℓ (pointCongr h P) ↔ S.IsCanonical ℓ P := by
  subst h
  exact Iff.rfl

end TateStructure

end Congr

/-! ### The transport along `σ_w : K_w ≃ K_{σ·w}` -/

section Galois

variable {F : Type u} [Field F] [NumberField F] (E : WeierstrassCurve F) [E.IsElliptic]
variable {Fbar : Type u} [Field Fbar] [Algebra F Fbar]
variable (K : IntermediateField F Fbar) [NumberField ↥K]

attribute [local instance 1100] instDecidableEqIntermediateField

/-- `12 ≠ 0` in the completions of `K`. -/
lemma twelve_ne_zero_localCompletion (w : FinitePlace ↥K) : (12 : localCompletion w) ≠ 0 := by
  rw [← map_ofNat (emb K w) 12]
  exact (map_ne_zero (emb K w)).mpr (by norm_num)

variable (σ : ↥K ≃ₐ[F] ↥K) (w : FinitePlace ↥K)

/-- `K_{σ·w}` is a normed `K_w`-algebra through the isometry `σ_w`. -/
@[reducible] def galNormedAlgebra :
    NormedAlgebra (localCompletion w) (localCompletion (galPlace σ w)) :=
  @NormedAlgebra.mk _ _ _ _
    (galCompletion σ w : localCompletion w →+* localCompletion (galPlace σ w)).toAlgebra
    fun r x => by
      letI := (galCompletion σ w : localCompletion w →+* localCompletion (galPlace σ w)).toAlgebra
      rw [Algebra.smul_def, norm_mul]
      change ‖galCompletion σ w r‖ * ‖x‖ ≤ ‖r‖ * ‖x‖
      rw [norm_galCompletion]

attribute [local instance] galNormedAlgebra

/-- `σ_w` as the structure map of the `K_w`-algebra `K_{σ·w}`. -/
abbrev galCompletionHom : localCompletion w →+* localCompletion (galPlace σ w) :=
  algebraMap (localCompletion w) (localCompletion (galPlace σ w))

lemma galCompletionHom_apply (x : localCompletion w) :
    galCompletionHom K σ w x = galCompletion σ w x := rfl

lemma galCompletionHom_bijective : Function.Bijective (galCompletionHom K σ w) :=
  (galCompletion σ w).bijective

omit [E.IsElliptic] in
/-- **`σ_w` carries `E ×_F K_w` to `E ×_F K_{σ·w}`.** -/
theorem map_curveKw : (curveKw E K w).map (galCompletionHom K σ w) = curveKw E K (galPlace σ w) := by
  unfold curveKw curveK
  rw [WeierstrassCurve.map_map, WeierstrassCurve.map_map, WeierstrassCurve.map_map]
  congr 1
  ext a
  simp only [RingHom.comp_apply]
  rw [galCompletionHom_apply, galCompletion_emb, AlgEquiv.commutes]

omit [E.IsElliptic] in
/-- **The point map of `σ_w` on `E(K_w)`, through `σ`**: on `E(K)`, the action of `σ` followed by
the inclusion into `E(K_{σ·w})` is the inclusion into `E(K_w)` followed by `σ_w`. -/
theorem pointMap_emb_galK (R : (curveK E K).toAffine.Point) :
    pointMap (curveK E K) (emb K (galPlace σ w)) (galK E K σ R) =
      pointCongr (map_curveKw E K σ w)
        (pointMap (curveKw E K w) (galCompletionHom K σ w) (pointMap (curveK E K) (emb K w) R)) := by
  cases R with
  | zero =>
    change pointMap _ _ (galK E K σ 0) = pointCongr _ (pointMap _ _ (pointMap _ _ 0))
    simp only [map_zero]
  | some x y h =>
    rw [pointMap_some, pointMap_some, pointCongr_some]
    exact some_ext ((galCompletionHom_apply K σ w _).trans (galCompletion_emb K σ w x)).symm
      ((galCompletionHom_apply K σ w _).trans (galCompletion_emb K σ w y)).symm

/-- **The graph lines at `w` and `σ·w` correspond under `σ_w`**, for arbitrary Tate structures. -/
theorem mem_graphLine_galCompletion (S : TateStructure (curveKw E K w))
    (S' : TateStructure (curveKw E K (galPlace σ w))) (ℓ : ℕ) (P : (curveKw E K w).toAffine.Point) :
    pointCongr (map_curveKw E K σ w) (pointMap (curveKw E K w) (galCompletionHom K σ w) P) ∈
        S'.graphLine ℓ ↔ P ∈ S.graphLine ℓ := by
  have hbij := galCompletionHom_bijective K σ w
  rw [TateStructure.graphLine_eq ((S.baseChange hbij).congr (map_curveKw E K σ w)) S'
    (twelve_ne_zero_localCompletion K _) ℓ, TateStructure.graphLine_congr,
    AddSubgroup.mem_map_equiv, AddEquiv.symm_apply_apply, TateStructure.graphLine_baseChange]
  exact AddSubgroup.mem_map_iff_mem (pointMap_injective _ _)

/-- **The canonical generators at `w` and `σ·w` correspond under `σ_w`**, for arbitrary Tate
structures. -/
theorem isCanonical_galCompletion (S : TateStructure (curveKw E K w))
    (S' : TateStructure (curveKw E K (galPlace σ w))) (ℓ : ℕ) (P : (curveKw E K w).toAffine.Point) :
    S'.IsCanonical ℓ
        (pointCongr (map_curveKw E K σ w) (pointMap (curveKw E K w) (galCompletionHom K σ w) P)) ↔
      S.IsCanonical ℓ P := by
  have hbij := galCompletionHom_bijective K σ w
  rw [TateStructure.isCanonical_congr ((S.baseChange hbij).congr (map_curveKw E K σ w)) S'
    (twelve_ne_zero_localCompletion K _) ℓ, TateStructure.isCanonical_congr']
  exact TateStructure.isCanonical_baseChange hbij S ℓ P

/-! ### The action of `Gal(K/F)` on `E(K)` is bijective -/

omit [NumberField F] [E.IsElliptic] [NumberField ↥K] in
lemma galK_inv_galK (R : (curveK E K).toAffine.Point) : galK E K σ⁻¹ (galK E K σ R) = R := by
  cases R with
  | zero => rfl
  | some x y h =>
    refine some_ext ?_ ?_
    · change σ⁻¹ (σ x) = x
      rw [AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
    · change σ⁻¹ (σ y) = y
      rw [AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]

omit [NumberField F] [E.IsElliptic] [NumberField ↥K] in
lemma galK_injective : Function.Injective (galK E K σ) := fun R R' h => by
  rw [← galK_inv_galK E K σ R, h, galK_inv_galK]

omit [NumberField F] [E.IsElliptic] [NumberField ↥K] in
lemma galK_surjective : Function.Surjective (galK E K σ) := fun R => by
  refine ⟨galK E K σ⁻¹ R, ?_⟩
  conv_lhs => rw [← inv_inv σ]
  exact galK_inv_galK E K σ⁻¹ R

/-! ### The equivariance fields of `TateFamily` for an arbitrary family -/

variable (ℓ : ℕ) (VBad : Set (FinitePlace ↥(fieldOfModuli F E)))

/-- **Galois equivariance of the graph line for an arbitrary family of Tate structures.** -/
theorem graphLine_galPlace_of_forall
    (S : ∀ w : FinitePlace ↥K, IsBadPlace E K VBad w → TateStructure (curveKw E K w))
    (w : FinitePlace ↥K) (hw : IsBadPlace E K VBad w) (σ : ↥K ≃ₐ[F] ↥K) :
    ((S (galPlace σ w) (isBadPlace_galPlace E K VBad hw σ)).graphLine ℓ).comap
        (pointMap (curveK E K) (emb K (galPlace σ w))) =
      (((S w hw).graphLine ℓ).comap (pointMap (curveK E K) (emb K w))).map (galK E K σ) := by
  have key : ∀ R : (curveK E K).toAffine.Point,
      galK E K σ R ∈ ((S (galPlace σ w) (isBadPlace_galPlace E K VBad hw σ)).graphLine ℓ).comap
        (pointMap (curveK E K) (emb K (galPlace σ w))) ↔
      R ∈ ((S w hw).graphLine ℓ).comap (pointMap (curveK E K) (emb K w)) := by
    intro R
    rw [AddSubgroup.mem_comap, AddSubgroup.mem_comap, pointMap_emb_galK,
      mem_graphLine_galCompletion]
  ext R
  obtain ⟨R₀, rfl⟩ := galK_surjective E K σ R
  rw [AddSubgroup.mem_map, key]
  constructor
  · intro h
    exact ⟨R₀, h, rfl⟩
  · rintro ⟨R₁, h₁, hR⟩
    rw [← galK_injective E K σ hR]
    exact h₁

/-- **Galois equivariance of the canonical generators for an arbitrary family of Tate
structures.** -/
theorem isCanonical_galPlace_of_forall
    (S : ∀ w : FinitePlace ↥K, IsBadPlace E K VBad w → TateStructure (curveKw E K w))
    (w : FinitePlace ↥K) (hw : IsBadPlace E K VBad w) (σ : ↥K ≃ₐ[F] ↥K)
    (R : (curveK E K).toAffine.Point) :
    (S (galPlace σ w) (isBadPlace_galPlace E K VBad hw σ)).IsCanonical ℓ
        (pointMap (curveK E K) (emb K (galPlace σ w)) (galK E K σ R)) ↔
      (S w hw).IsCanonical ℓ (pointMap (curveK E K) (emb K w) R) := by
  rw [pointMap_emb_galK, isCanonical_galCompletion]

/-- **Any family of Tate structures at the bad places is a `TateFamily`**: the equivariance
fields are theorems. -/
def TateFamily.ofStructures
    (S : ∀ w : FinitePlace ↥K, IsBadPlace E K VBad w → TateStructure (curveKw E K w)) :
    TateFamily E K ℓ VBad where
  S := S
  graphLine_galPlace := graphLine_galPlace_of_forall E K ℓ VBad S
  isCanonical_galPlace := isCanonical_galPlace_of_forall E K ℓ VBad S

@[simp] lemma TateFamily.ofStructures_S
    (S : ∀ w : FinitePlace ↥K, IsBadPlace E K VBad w → TateStructure (curveKw E K w)) :
    (TateFamily.ofStructures E K ℓ VBad S).S = S := rfl

end Galois

end

end Iut
