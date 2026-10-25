/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Cusp.HemiCoreRing
import Iut.Reconstruction.Cusp.HemiInvConj
import Iut.Reconstruction.Cusp.CoverIsoDGC
import CurvesJacobian.Cusp.HemiCoreChain

/-!
# `Π_C` is self-commensurating: [AbsTopII] Cor. 3.3 (i) for the hemi-elliptic orbicurve (MR8, D-c)

Let `E` be an elliptic curve over a number field `K` with `j(E) ∉ excJ`, `X = E ∖ {O}` and
`C = [X / ±1]` the hemi-elliptic orbicurve, with `Π_X ⊆ Π_C` (curves-jacobian
`CurvesJacobian.Cusp.hemiCoreChain`, `hemiCObj`, `hemiCoreEmb₄`). We prove the debt D-c of the
MR8 plan:

* **`hemi_selfComm`**: `ChainObj.SelfComm` for `Π_C` — every two open injections `P ↪ Π_C` over
  `G_K` (up to conjugation by `g ∈ G_K`) differ by an inner automorphism of `Π_C`;
* **`hemi_cor33i_terminal`**: the `⋎`-chain `Π_X ⇝ Π_C` is terminal in `ÉtLoc` (the case
  `G′ = G` of [AbsTopII] Cor. 3.3 (i), with the lead decision on `ÉtLoc` morphisms implemented
  in curves-jacobian `EtLocTerminal`).

Proof (for injections with image in `Π_X`, which suffices by `hemi_cor33i_of_selfCommX`): after
conjugating by a lift of `g` the two images `Q₁, Q₂ ⊆ Π_X` are isomorphic over `G_K`; by the
rel-isom-DGC they are the fundamental groups of connected finite étale covers `Y₁, Y₂ → X` and the
isomorphism is induced by an isomorphism `F : Y₁ ≅ Y₂` (`exists_ringIso_of_openSubgroup_iso`).
By the core property of `C` ([CanLift] Prop. 2.7, `hemiCore_eq_or_eq_neg_sections`) `F ≫ p₂` is
`p₁` or `p₁ ≫ [−1]`; in the first case the isomorphism is inner in `Π_X`, in the second it is the
conjugation by an element of `Π_C ∖ Π_X` (`hemiInv_conj`) up to an inner automorphism of `Π_X`.

**Input:** `hDGC`, the existence half of the rel-isom-DGC over number fields (whitelist; recorded
debt of MR7), as in curves-jacobian `cor34_dup₃`, `belyiCusp_spec`. The core property is the theorem
`Iut.Anabelian.canLift27`, so everything lives in `Type`.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale Topology Belyi
  Belyi.Anabelian CurvesJacobian CurvesJacobian.Cusp WeierstrassCurve.Affine.CoordinateRing
  PreGaloisCategory

noncomputable section

namespace Iut.Reconstruction.HemiCore

section TopAux

variable {P G H : Type*} [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [CompactSpace P]
  [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [T2Space H]

omit [IsTopologicalGroup P] [IsTopologicalGroup H] in
/-- A compact group injected into `H` with image inside the image of an open embedding
`e : G → H` is isomorphic (as a topological group) to the preimage of its image. -/
theorem exists_equiv_comap (e : G →ₜ* H) (he : IsOpenEmbedding e) (f : P →ₜ* H)
    (hf : Function.Injective f) (hr : Set.range f ⊆ Set.range e) :
    ∃ θ : P ≃ₜ* (f.toMonoidHom.range.comap e.toMonoidHom),
      ∀ p, e (θ p : G) = f p := by
  haveI : T2Space G := he.isEmbedding.t2Space
  have hlift : ∀ p, ∃ g, e g = f p := fun p => hr ⟨p, rfl⟩
  let g : P → G := fun p => (hlift p).choose
  have hg : ∀ p, e (g p) = f p := fun p => (hlift p).choose_spec
  have hgm : ∀ p q, g (p * q) = g p * g q := fun p q =>
    he.injective (by rw [map_mul, hg, hg, hg, map_mul])
  have hg1 : g 1 = 1 := he.injective (by rw [hg, map_one, map_one])
  let φ : P →* (f.toMonoidHom.range.comap e.toMonoidHom) :=
    { toFun := fun p => ⟨g p, ⟨p, (hg p).symm⟩⟩
      map_one' := Subtype.ext hg1
      map_mul' := fun p q => Subtype.ext (hgm p q) }
  have hcont : Continuous φ := by
    refine Continuous.subtype_mk ?_ _
    refine he.isEmbedding.continuous_iff.2 ?_
    have : (e ∘ g) = f := funext hg
    rw [this]
    exact f.continuous
  have hbij : Function.Bijective φ := by
    refine ⟨fun p q hpq => hf ?_, fun y => ?_⟩
    · have h := congrArg (fun z : (f.toMonoidHom.range.comap e.toMonoidHom) => e (z : G)) hpq
      change e (g p) = e (g q) at h
      rwa [hg, hg] at h
    · obtain ⟨p, hp⟩ := y.2
      exact ⟨p, Subtype.ext (he.injective ((hg p).trans hp))⟩
  let hom : P ≃ₜ (f.toMonoidHom.range.comap e.toMonoidHom) :=
    hcont.homeoOfEquivCompactToT2 (f := Equiv.ofBijective φ hbij)
  refine ⟨{ MulEquiv.ofBijective φ hbij with
    continuous_toFun := hom.continuous_toFun
    continuous_invFun := hom.continuous_invFun }, fun p => hg p⟩

end TopAux

/-- The change of base point along the identity of a fibre functor is the identity. -/
lemma autContinuousMulEquivOfIso_refl_apply₅ {X : Scheme.{0}} {Ω : Type} [Field Ω]
    [IsSepClosed Ω] {x : Spec (.of Ω) ⟶ X} (τ : π₁ᵉᵗ(x)) :
    autContinuousMulEquivOfIso (Iso.refl (fiber x)) τ = τ := by
  change (Iso.refl _).conjAut τ = τ
  rw [Iso.conjAut_apply]
  ext
  simp

section Neg

variable {K : Type*} [Field K] (E : WeierstrassCurve K)

/-- The two descriptions of `[−1]` on `K[E]` agree: `negCoordAlgEquiv` (`HemiCoreRing`) and
elliptic-curves' `negYCoordEquiv` (used by `hemiNegSections`). -/
theorem negCoordAlgEquiv_eq_negY :
    negCoordAlgEquiv E = (negYCoordEquiv E.toAffine).restrictScalars K := by
  refine AlgEquiv.coe_toAlgHom_injective (algHom_ext₃ E ?_ ?_)
  · exact (negCoordAlgEquiv_x E).trans ((negYCoordEquiv E.toAffine).commutes Polynomial.X).symm
  · exact (negCoordHom₃_root E).trans (negYCoordHom_root E.toAffine).symm

end Neg

section Main

variable {K : Type} [Field K] [NumberField K] (E : WeierstrassCurve K) [E.IsElliptic]
  (Ω' : Type) [Field Ω'] [Algebra K Ω'] [IsAlgClosed Ω'] [Algebra.IsAlgebraic K Ω']
  [CharZero Ω']

/-- The `[−1]`-automorphism of `Γ(E ∖ {O})` of `HemiCoreRing` is `hemiNegSections`. -/
theorem negSections_eq :
    ((sectionsXEAlgEquiv E).trans ((negCoordAlgEquiv E).trans (sectionsXEAlgEquiv E).symm)) =
      hemiNegSections E := by
  rw [negCoordAlgEquiv_eq_negY]
  rfl

set_option maxHeartbeats 1600000 in
-- the subgroups `Q_i` of `Π_X = (arithmeticExt …).Pi` are unified with subgroups of `π₁ᵉᵗ(…)`
/-- **D-c with `g = 1`**: two open injections `P ↪ Π_C` with images in `Π_X` and the same
composite to `G_K` differ by an inner automorphism of `Π_C`. -/
theorem hemi_selfComm_one
    (hDGC : ∀ (k : Type) [Field k] [NumberField k], RelIsomDGC.Exists k)
    (hj : ∀ c ∈ AffOrbicurve.excJ, E.j ≠ (c : K))
    (P : Type 1) [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [CompactSpace P]
    (f₁ f₂ : P →ₜ* hemiCoreGrp₄ E) (hi₁ : Function.Injective f₁) (ho₁ : IsOpen (Set.range f₁))
    (hi₂ : Function.Injective f₂) (ho₂ : IsOpen (Set.range f₂))
    (hr₁ : Set.range f₁ ⊆ Set.range (hemiCoreEmb₄ E Ω'))
    (hr₂ : Set.range f₂ ⊆ Set.range (hemiCoreEmb₄ E Ω'))
    (hg : ∀ x, hemiCorePr₄ E Ω' (f₂ x) = hemiCorePr₄ E Ω' (f₁ x)) :
    ∃ γ : hemiCoreGrp₄ E, ∀ x, f₂ x = γ * f₁ x * γ⁻¹ := by
  have he := isOpenEmbedding_hemiCoreEmb₄ E Ω'
  obtain ⟨θ₁, hθ₁⟩ := exists_equiv_comap (hemiCoreEmb₄ E Ω') he f₁ hi₁ hr₁
  obtain ⟨θ₂, hθ₂⟩ := exists_equiv_comap (hemiCoreEmb₄ E Ω') he f₂ hi₂ hr₂
  let Q₁ : OpenSubgroup (arithmeticExt Ω' (hypCurveX E) (compl_XE_nonempty E)).Pi :=
    ⟨f₁.toMonoidHom.range.comap (hemiCoreEmb₄ E Ω').toMonoidHom,
      ho₁.preimage (hemiCoreEmb₄ E Ω').continuous⟩
  let Q₂ : OpenSubgroup (arithmeticExt Ω' (hypCurveX E) (compl_XE_nonempty E)).Pi :=
    ⟨f₂.toMonoidHom.range.comap (hemiCoreEmb₄ E Ω').toMonoidHom,
      ho₂.preimage (hemiCoreEmb₄ E Ω').continuous⟩
  let ψ : (Q₁ : Subgroup (arithmeticExt Ω' (hypCurveX E) (compl_XE_nonempty E)).Pi) ≃ₜ*
      (Q₂ : Subgroup (arithmeticExt Ω' (hypCurveX E) (compl_XE_nonempty E)).Pi) :=
    θ₁.symm.trans θ₂
  have hψe : ∀ p, (ψ (θ₁ p) : (arithmeticExt Ω' (hypCurveX E) (compl_XE_nonempty E)).Pi) =
      θ₂ p := fun p => by
    change ((θ₂ (θ₁.symm (θ₁ p)) : _) : (arithmeticExt Ω' (hypCurveX E) (compl_XE_nonempty E)).Pi) =
      θ₂ p
    rw [ContinuousMulEquiv.symm_apply_apply]
  have hψ : ∀ q, projGk Ω' (hypCurveX E) (compl_XE_nonempty E) (ψ q).1 =
      projGk Ω' (hypCurveX E) (compl_XE_nonempty E) q.1 := fun q => by
    obtain ⟨p, rfl⟩ := θ₁.surjective q
    rw [hψe]
    have h₁ := hemiCorePr₄_hemiCoreEmb₄ E Ω' (θ₁ p : _)
    have h₂ := hemiCorePr₄_hemiCoreEmb₄ E Ω' (θ₂ p : _)
    rw [hθ₁] at h₁
    rw [hθ₂] at h₂
    exact h₂.symm.trans ((hg p).trans h₁)
  obtain ⟨B₁, B₂, r₁, r₂, Eiso, hd₁, hd₂, hfe₁, hfe₂, hK, H⟩ :=
    exists_ringIso_of_openSubgroup_iso (C := hypCurveX E) (hc := compl_XE_nonempty E) (Ω := Ω')
      hDGC Q₁ Q₂ ψ hψ
  -- the two maps `Γ(E ∖ {O}) → B₁`
  letI : Algebra K B₁ :=
    ((r₁.hom).comp (algebraMap K Γ((hypCurveX E).Xbar, (hypCurveX E).U))).toAlgebra
  have hK' : ∀ c : K, (r₂ ≫ Eiso.hom).hom (algebraMap K Γ((hypCurveX E).Xbar, (hypCurveX E).U) c) =
      algebraMap K B₁ c := fun c => by
    have h := congrArg (fun φ : CommRingCat.of K ⟶ B₁ => φ.hom c) hK
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
    exact h
  let a : Γ((hypCurveX E).Xbar, (hypCurveX E).U) →ₐ[K] B₁ :=
    { r₁.hom with commutes' := fun _ => rfl }
  let b : Γ((hypCurveX E).Xbar, (hypCurveX E).U) →ₐ[K] B₁ :=
    { (r₂ ≫ Eiso.hom).hom with commutes' := hK' }
  have ha : IsFiniteEtale (Spec.map (CommRingCat.ofHom a.toRingHom)) := hfe₁
  have hb : IsFiniteEtale (Spec.map (CommRingCat.ofHom b.toRingHom)) := by
    change IsFiniteEtale (Spec.map (r₂ ≫ Eiso.hom))
    rw [Spec.map_comp]
    haveI := hfe₂
    haveI : IsFiniteEtale (Spec.map Eiso.hom) :=
      MorphismProperty.of_isIso @IsFiniteEtale (Spec.map Eiso.hom)
    infer_instance
  -- the conclusion from a map `φ` induced by `Spec ρ`
  have key : ∀ ρ : Γ(curveE E, XE E) ⟶ Γ(curveE E, XE E),
      (CommRingCat.ofHom b.toRingHom = ρ ≫ r₁) →
      ∀ φ : (arithmeticExt Ω' (hypCurveX E) (compl_XE_nonempty E)).Pi →
          (arithmeticExt Ω' (hypCurveX E) (compl_XE_nonempty E)).Pi,
        IsConjInduced (Spec.map ρ) φ → ∃ δ, ∀ p : P,
          (θ₂ p : (arithmeticExt Ω' (hypCurveX E) (compl_XE_nonempty E)).Pi) =
            δ * φ (θ₁ p) * δ⁻¹ := by
    intro ρ hρ φ hφ
    obtain ⟨δ, hδ⟩ := H ρ hρ.symm φ hφ
    exact ⟨δ, fun p => (hψe p).symm.trans (hδ (θ₁ p))⟩
  haveI : IsDomain B₁ := hd₁
  rcases hemiCore_eq_or_eq_neg_sections E hj a b ha hb with hab | hab
  · -- `F ≫ p₂ = p₁`: the isomorphism is inner in `Π_X`
    have hρ : CommRingCat.ofHom b.toRingHom = 𝟙 _ ≫ r₁ := by
      rw [Category.id_comp, hab]
      rfl
    have hid : IsConjInduced (Spec.map (𝟙 Γ(curveE E, XE E)))
        (autContinuousMulEquivOfIso
          (Iso.refl (fiber (basePoint Ω' (hypCurveX E) (compl_XE_nonempty E) ≫
            baseChangeSpec K Ω' Γ((hypCurveX E).Xbar, (hypCurveX E).U))))) :=
      (isConjInduced_id_autIso _).congr_hom (Spec.map_id _).symm
    obtain ⟨δ, hδ⟩ := key (𝟙 _) hρ _ hid
    refine ⟨hemiCoreEmb₄ E Ω' δ, fun p => ?_⟩
    have h := congrArg (hemiCoreEmb₄ E Ω') (hδ p)
    rw [hθ₂, map_mul, map_mul, map_inv] at h
    rw [h]
    congr 2
    exact (congrArg (hemiCoreEmb₄ E Ω') (autContinuousMulEquivOfIso_refl_apply₅ _)).trans (hθ₁ p)
  · -- `F ≫ p₂ = p₁ ≫ [−1]`: conjugation by an element of `Π_C ∖ Π_X`
    have hν := negSections_eq E
    let ν : Γ(curveE E, XE E) ⟶ Γ(curveE E, XE E) :=
      CommRingCat.ofHom (hemiNegSections E).toRingEquiv.toRingHom
    have hρ : CommRingCat.ofHom b.toRingHom = ν ≫ r₁ := by
      rw [hab, hν]
      rfl
    obtain ⟨c⟩ : Nonempty (fiber ((basePoint Ω' (hypCurveX E) (compl_XE_nonempty E) ≫
        baseChangeSpec K Ω' Γ((hypCurveX E).Xbar, (hypCurveX E).U)) ≫ Spec.map ν) ≅
        fiber (basePoint Ω' (hypCurveX E) (compl_XE_nonempty E) ≫
        baseChangeSpec K Ω' Γ((hypCurveX E).Xbar, (hypCurveX E).U))) :=
      PreGaloisCategory.nonempty_iso_of_fiberFunctor _ _
    let φ := fun σ => autContinuousMulEquivOfIso c (fundamentalGroupMap (Spec.map ν) rfl σ)
    have hφ : IsConjInduced (Spec.map ν) φ := ⟨c, fun _ => rfl⟩
    obtain ⟨δ, hδ⟩ := key ν hρ φ hφ
    obtain ⟨τ, -, hτ⟩ := hemiInv_conj E Ω' hφ
    refine ⟨hemiCoreEmb₄ E Ω' δ * hemiCoreEquiv₄ E τ, fun p => ?_⟩
    have h := congrArg (hemiCoreEmb₄ E Ω') (hδ p)
    rw [hθ₂, map_mul, map_mul, map_inv] at h
    have h' : hemiCoreEmb₄ E Ω' (φ (θ₁ p).1) =
        hemiCoreEquiv₄ E τ * f₁ p * (hemiCoreEquiv₄ E τ)⁻¹ := by
      change hemiCoreEquiv₄ E (hemiPiXEmb E Ω' (φ (θ₁ p).1)) = _
      rw [hτ, map_mul, map_mul, map_inv]
      change _ * hemiCoreEmb₄ E Ω' (θ₁ p).1 * _ = _
      rw [hθ₁]
    rw [h, h', mul_inv_rev]
    group

/-- **[AbsTopII] Cor. 3.3 (i), the core property of `Π_C` (debt D-c)**: `Π_C` is
self-commensurating — every two open injections `P ↪ Π_C` lying over `G_K` up to conjugation by
some `g ∈ G_K` differ by an inner automorphism of `Π_C`. -/
theorem hemi_selfComm
    (hDGC : ∀ (k : Type) [Field k] [NumberField k], RelIsomDGC.Exists k)
    (hj : ∀ c ∈ AffOrbicurve.excJ, E.j ≠ (c : K)) :
    (hemiCoreChain E Ω').last.SelfComm := by
  refine ChainObj.selfComm_of_open (hemiCObj E Ω')
    (hemiCoreEmb₄ E Ω').toMonoidHom.range (isOpenEmbedding_hemiCoreEmb₄ E Ω').isOpen_range
    fun P _ _ _ _ f₁ f₂ hi₁ ho₁ hi₂ ho₂ hr₁ hr₂ g hg => ?_
  change P →ₜ* hemiCoreGrp₄ E at f₁ f₂
  replace hg : ∀ x, hemiCorePr₄ E Ω' (f₂ x) = g * hemiCorePr₄ E Ω' (f₁ x) * g⁻¹ := hg
  change ∃ γ : hemiCoreGrp₄ E, ∀ x, f₂ x = γ * f₁ x * γ⁻¹
  obtain ⟨s, hs⟩ := (arithmeticExt Ω' (hypCurveX E) (compl_XE_nonempty E)).pr_surjective g
  set t := hemiCoreEmb₄ E Ω' s
  let c : hemiCoreGrp₄ E →ₜ* hemiCoreGrp₄ E :=
    { toFun := fun y => t⁻¹ * y * t
      map_one' := by group
      map_mul' := fun y z => by group
      continuous_toFun := by fun_prop }
  let f₂' := c.comp f₂
  have hc_inj : Function.Injective c := fun y z h => by
    have h' : t⁻¹ * y * t = t⁻¹ * z * t := h
    simpa using h'
  have hrange : Set.range f₂' = (fun y => t⁻¹ * y * t) '' Set.range f₂ :=
    Set.range_comp (fun y => t⁻¹ * y * t) f₂
  have hc_open : IsOpenMap (fun y : hemiCoreGrp₄ E => t⁻¹ * y * t) :=
    (Homeomorph.mulRight t).isOpenMap.comp (Homeomorph.mulLeft t⁻¹).isOpenMap
  have hr₂' : Set.range f₂' ⊆ Set.range (hemiCoreEmb₄ E Ω') := by
    rw [hrange]
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨w, hw⟩ := hr₂ hy
    have hw' : hemiCoreEmb₄ E Ω' w = y := hw
    exact ⟨s⁻¹ * w * s, by rw [map_mul, map_mul, map_inv, hw']⟩
  have hpr : ∀ x, hemiCorePr₄ E Ω' (f₂' x) = hemiCorePr₄ E Ω' (f₁ x) := fun x => by
    have h1 : hemiCorePr₄ E Ω' t = g := (hemiCorePr₄_hemiCoreEmb₄ E Ω' s).trans hs
    change hemiCorePr₄ E Ω' (t⁻¹ * f₂ x * t) = _
    rw [map_mul, map_mul, map_inv, h1, hg x]
    group
  obtain ⟨γ, hγ⟩ := hemi_selfComm_one E Ω' hDGC hj P f₁ f₂' hi₁ ho₁ (hc_inj.comp hi₂)
    (by rw [hrange]; exact hc_open _ ho₂) hr₁ hr₂' hpr
  refine ⟨t * γ, fun x => ?_⟩
  have h := hγ x
  change t⁻¹ * f₂ x * t = _ at h
  calc f₂ x = t * (t⁻¹ * f₂ x * t) * t⁻¹ := by group
    _ = _ := by rw [h]; group

/-- **[AbsTopII] Cor. 3.3 (i) for the hemi-elliptic orbicurve, unconditionally on D-c**: the
`⋎`-chain `Π_X ⇝ Π_C` is terminal in `ÉtLoc(Π_X)`. -/
theorem hemi_cor33i_terminal
    (hDGC : ∀ (k : Type) [Field k] [NumberField k], RelIsomDGC.Exists k)
    (hj : ∀ c ∈ AffOrbicurve.excJ, E.j ≠ (c : K)) :
    (hemiCoreChain E Ω').IsTerminalEtLoc :=
  hemi_cor33i E Ω' (hemi_selfComm E Ω' hDGC hj)

end Main

end Iut.Reconstruction.HemiCore
