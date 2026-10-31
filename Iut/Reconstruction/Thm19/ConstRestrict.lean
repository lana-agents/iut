/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Thm19.StageGeom
import ContinuousKummerTheory.Curve.ConstantsZHat
import Mathlib.FieldTheory.Galois.Profinite

/-!
# Isomorphisms of Galois models restricted to extensions of the field of constants

The stages of [AbsTopIII] Thm 1.9 (d) (`Topics in Absolute Anabelian Geometry III.txt`
l.2158–2178) are opens of `Z ×_{k_Z} k′`, `k′` a finite extension of `k_Z`; in the Galois model
`Π_{U_{K}} = pr⁻¹(G_K) ⊆ Π_U` (curves-jacobian `piRes`, `mem_range_piRes_iff`). An isomorphism
`e : Π_U ≃ₜ* Π_{U'}` lying over `ψ : G_k ≃* G_{k'}` therefore restricts to the
extensions of the field of constants, `K ↦ K'` with `G_{K'} = ψ(G_K)`. Here:

* `gkFix K = G_K ⊆ G_k` (the elements of `Gal(k̄/k)` fixing `K`), `mem_gkFix_iff`, closed and of
  finite index for finite `K`;
* `fieldOf H ⊆ Ω` the fixed field of a subgroup `H ⊆ G_k`, with **`gkFix_fieldOf`**
  (`G_{fieldOf H} = H` for closed `H`, infinite Galois theory) and `finiteDimensional_fieldOf`
  (`H` open);
* `isClosed_map_gkFix`: `ψ(G_K)` is closed (the image of the compact `e(pr⁻¹(G_K))`; no continuity
  of `ψ` is needed), hence open;
* **`constField e ψ K`** (`= K'`, finite over `k'`) and **`constIso e ψ K :
  Π_{U_K} ≃ₜ* Π_{U'_{K'}}`** with `piRes ∘ constIso = e ∘ piRes` (`piRes_constIso`).
-/

open KummerTheory KummerTheory.Curve AffOrbicurve CurvesJacobian CurvesJacobian.Kummer

universe u

noncomputable section

namespace Iut.Reconstruction.Thm19

set_option linter.unusedSectionVars false

/-! ### `G_K ⊆ G_k` and fixed fields -/

section Fix

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] [CharZero k] [IsAlgClosed Ω]

/-- **`G_K ⊆ G_k`**: the elements of `Gal(k̄/k)` fixing `K ⊆ Ω` (pointwise on `K ∩ k̄`). -/
def gkFix (K : IntermediateField k Ω) : Subgroup (Gk k Ω) :=
  (K.comap (kbar k Ω).val).fixingSubgroup

lemma mem_gkFix_iff (K : IntermediateField k Ω) [Algebra.IsAlgebraic k K] (g : Gk k Ω) :
    g ∈ gkFix K ↔ ∀ c : K, g ⟨algebraMap K Ω c, algebraMap_mem_kbar c⟩ =
      ⟨algebraMap K Ω c, algebraMap_mem_kbar c⟩ := by
  rw [gkFix, IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h c
    exact h _ c.2
  · intro h x hx
    exact h ⟨(x : Ω), hx⟩

lemma isClosed_gkFix (K : IntermediateField k Ω) :
    IsClosed (gkFix K : Set (Gk k Ω)) :=
  InfiniteGalois.fixingSubgroup_isClosed _

lemma finiteDimensional_comap_kbar (K : IntermediateField k Ω) [FiniteDimensional k K] :
    FiniteDimensional k (K.comap (kbar k Ω).val) := by
  let f : K.comap (kbar k Ω).val →ₗ[k] K :=
    { toFun := fun x => ⟨((x : kbar k Ω) : Ω), x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine Module.Finite.of_injective f fun x y h => ?_
  exact Subtype.ext (Subtype.ext (congrArg Subtype.val h :))

lemma isOpen_gkFix (K : IntermediateField k Ω) [FiniteDimensional k K] :
    IsOpen (gkFix K : Set (Gk k Ω)) := by
  haveI := finiteDimensional_comap_kbar K
  exact IntermediateField.fixingSubgroup_isOpen _

instance finiteIndex_gkFix (K : IntermediateField k Ω) [FiniteDimensional k K] :
    (gkFix K).FiniteIndex :=
  @Subgroup.finiteIndex_of_finite_quotient _ _ _
    (Subgroup.quotient_finite_of_isOpen _ (isOpen_gkFix K))

/-- **The fixed field `Ω^H ∩ k̄` of a subgroup `H ⊆ G_k`.** -/
def fieldOf (H : Subgroup (Gk k Ω)) : IntermediateField k Ω :=
  (IntermediateField.fixedField H).map (kbar k Ω).val

lemma mem_comap_fieldOf_iff (H : Subgroup (Gk k Ω)) (x : kbar k Ω) :
    x ∈ (fieldOf H).comap (kbar k Ω).val ↔ x ∈ IntermediateField.fixedField H := by
  constructor
  · rintro ⟨y, hy, hxy⟩
    rwa [show y = x from Subtype.ext hxy] at hy
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- **`G_{Ω^H} = H` for closed `H`** (infinite Galois theory for `k̄ / k`). -/
theorem gkFix_fieldOf {H : Subgroup (Gk k Ω)} (hH : IsClosed (H : Set (Gk k Ω))) :
    gkFix (fieldOf H) = H := by
  have e : (fieldOf H).comap (kbar k Ω).val = IntermediateField.fixedField H := by
    ext x
    exact mem_comap_fieldOf_iff H x
  rw [gkFix, e]
  exact InfiniteGalois.fixingSubgroup_fixedField ⟨H, hH⟩

theorem finiteDimensional_fieldOf {H : Subgroup (Gk k Ω)}
    (hH : IsOpen (H : Set (Gk k Ω))) : FiniteDimensional k (fieldOf H) := by
  have hcl : IsClosed (H : Set (Gk k Ω)) := Subgroup.isClosed_of_isOpen _ hH
  have h1 : FiniteDimensional k (IntermediateField.fixedField H) := by
    rw [← InfiniteGalois.isOpen_iff_finite]
    have := InfiniteGalois.fixingSubgroup_fixedField (⟨H, hcl⟩ : ClosedSubgroup (Gk k Ω))
    change IsOpen ((IntermediateField.fixedField H).fixingSubgroup : Set (Gk k Ω))
    rw [this]
    exact hH
  exact LinearEquiv.finiteDimensional
    (IntermediateField.equivMap (IntermediateField.fixedField H) (kbar k Ω).val).toLinearEquiv

end Fix

/-! ### Restriction of isomorphisms over `ψ` to extensions of the field of constants -/

section Restrict

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  {D : Pi1.Orbifold.GaloisData k t} [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω]
  {k' Ω' : Type u} [Field k'] [Field Ω'] [Algebra k' Ω'] {t' : Ω'}
  {D' : Pi1.Orbifold.GaloisData k' t'} [CharZero k'] [IsGalois (K₀ k' t') Ω'] [IsAlgClosed Ω']
  (e : Pi D ≃ₜ* Pi D') (ψ : Gk k Ω ≃* Gk k' Ω')
  (he : ∀ p, piToGk D' (e p) = ψ (piToGk D p)) (hs : Function.Surjective (piToGk D))

lemma compactSpace_pi : CompactSpace (Pi D) := by
  haveI : CompactSpace D.H := GaloisPi1.compactSpace_of_isClosed _ D.isClosed_H
  exact Quotient.compactSpace

include he hs in
/-- `ψ(G_K) = pr'(e(pr⁻¹(G_K)))`. -/
lemma map_gkFix_eq (K : IntermediateField k Ω) :
    ((gkFix K).map ψ.toMonoidHom : Set (Gk k' Ω')) =
      piToGk D' '' (e '' (piToGk D ⁻¹' (gkFix K : Set (Gk k Ω)))) := by
  ext g
  constructor
  · rintro ⟨h, hh, rfl⟩
    obtain ⟨p, rfl⟩ := hs h
    exact ⟨e p, ⟨p, hh, rfl⟩, he p⟩
  · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    exact ⟨piToGk D p, hp, (he p).symm⟩

include he hs in
/-- **`ψ(G_K)` is closed**: the image of the compact set `e(pr⁻¹(G_K))` (no continuity of `ψ`
is used). -/
lemma isClosed_map_gkFix (K : IntermediateField k Ω) :
    IsClosed ((gkFix K).map ψ.toMonoidHom : Set (Gk k' Ω')) := by
  haveI := compactSpace_pi (D := D)
  rw [map_gkFix_eq e ψ he hs K]
  have hc : IsCompact (piToGk D ⁻¹' (gkFix K : Set (Gk k Ω))) :=
    ((isClosed_gkFix K).preimage (continuous_piToGk D)).isCompact
  exact ((hc.image e.continuous).image (continuous_piToGk D')).isClosed

include he hs in
lemma isOpen_map_gkFix (K : IntermediateField k Ω) [FiniteDimensional k K] :
    IsOpen ((gkFix K).map ψ.toMonoidHom : Set (Gk k' Ω')) := by
  haveI : ((gkFix K).map ψ.toMonoidHom).FiniteIndex :=
    ⟨by rw [Subgroup.index_map_of_bijective ψ.bijective]; exact Subgroup.FiniteIndex.index_ne_zero⟩
  exact Subgroup.isOpen_of_isClosed_of_finiteIndex _ (isClosed_map_gkFix e ψ he hs K)

/-- **The field of constants `K'` corresponding to `K`**: `G_{K'} = ψ(G_K)`. -/
def constField (K : IntermediateField k Ω) : IntermediateField k' Ω' :=
  fieldOf ((gkFix K).map ψ.toMonoidHom)

include he hs in
lemma gkFix_constField (K : IntermediateField k Ω) :
    gkFix (constField ψ K) = (gkFix K).map ψ.toMonoidHom :=
  gkFix_fieldOf (isClosed_map_gkFix e ψ he hs K)

include he hs in
lemma finiteDimensional_constField (K : IntermediateField k Ω) [FiniteDimensional k K] :
    FiniteDimensional k' (constField ψ K) :=
  finiteDimensional_fieldOf (isOpen_map_gkFix e ψ he hs K)

variable (K : IntermediateField k Ω) [FiniteDimensional k K]
  [FiniteDimensional k' (constField ψ K)]

lemma mem_range_piRes_iff_gkFix (p : Pi D) :
    p ∈ (piRes K D).range ↔ piToGk D p ∈ gkFix K := by
  rw [mem_range_piRes_iff, mem_gkFix_iff]

include he hs in
/-- **`e` maps `Π_{U_K}` onto `Π_{U'_{K'}}`.** -/
lemma mem_range_piRes_iff_map (p : Pi D) :
    e p ∈ (piRes (constField ψ K) D').range ↔ p ∈ (piRes K D).range := by
  rw [mem_range_piRes_iff_gkFix, mem_range_piRes_iff_gkFix, he, gkFix_constField e ψ he hs,
    Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]

include he hs in
lemma map_range_piRes :
    (piRes K D).range.map e.toMulEquiv.toMonoidHom = (piRes (constField ψ K) D').range := by
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact (mem_range_piRes_iff_map e ψ he hs K p).2 hp
  · intro hq
    refine ⟨e.symm q, (mem_range_piRes_iff_map e ψ he hs K _).1 ?_, e.apply_symm_apply q⟩
    rwa [e.apply_symm_apply]

include e he hs in
/-- **`Π_{U_K} ≃* Π_{U'_{K'}}`** (as groups), through the images of `piRes`. -/
def constMulEquiv : Pi (constExt K D) ≃* Pi (constExt (constField ψ K) D') :=
  ((MonoidHom.ofInjective (piRes_injective (K := K) D)).trans
    ((e.toMulEquiv.subgroupMap (piRes K D).range).trans
      (MulEquiv.subgroupCongr (map_range_piRes e ψ he hs K)))).trans
    (MonoidHom.ofInjective (piRes_injective (K := constField ψ K) D')).symm

lemma piRes_constMulEquiv (q : Pi (constExt K D)) :
    piRes (constField ψ K) D' (constMulEquiv e ψ he hs K q) = e (piRes K D q) := by
  have h := MonoidHom.ofInjective_apply (piRes_injective (K := constField ψ K) D')
    (x := constMulEquiv e ψ he hs K q)
  rw [← h]
  simp only [constMulEquiv, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  rfl

lemma piRes_constMulEquiv_symm (q : Pi (constExt (constField ψ K) D')) :
    piRes K D ((constMulEquiv e ψ he hs K).symm q) = e.symm (piRes (constField ψ K) D' q) := by
  rw [eq_comm, ContinuousMulEquiv.symm_apply_eq, ← piRes_constMulEquiv e ψ he hs K,
    MulEquiv.apply_symm_apply]

include e he hs in
/-- **`Π_{U_K} ≃ₜ* Π_{U'_{K'}}`** restricting `e` (`piRes_constIso`). -/
def constIso : Pi (constExt K D) ≃ₜ* Pi (constExt (constField ψ K) D') where
  toMulEquiv := constMulEquiv e ψ he hs K
  continuous_toFun := by
    rw [(isClosedEmbedding_piRes (K := constField ψ K) D').isEmbedding.continuous_iff]
    change Continuous fun q => piRes (constField ψ K) D' (constMulEquiv e ψ he hs K q)
    simp_rw [piRes_constMulEquiv]
    exact e.continuous.comp (continuous_piRes D)
  continuous_invFun := by
    rw [(isClosedEmbedding_piRes (K := K) D).isEmbedding.continuous_iff]
    change Continuous fun q => piRes K D ((constMulEquiv e ψ he hs K).symm q)
    simp_rw [piRes_constMulEquiv_symm]
    exact e.symm.continuous.comp (continuous_piRes D')

@[simp] lemma piRes_constIso (q : Pi (constExt K D)) :
    piRes (constField ψ K) D' (constIso e ψ he hs K q) = e (piRes K D q) :=
  piRes_constMulEquiv e ψ he hs K q

end Restrict

end Iut.Reconstruction.Thm19
