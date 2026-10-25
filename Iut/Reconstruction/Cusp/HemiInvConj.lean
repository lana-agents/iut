/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.HemiArith
import CurvesJacobian.Cusp.HemiPuncturedArith
import CurvesJacobian.Cusp.FieldChange

/-!
# `π₁([−1])` is conjugation by an element of `Π_C` (MR8, hemi-elliptic core)

Let `E` be an elliptic curve over a number field `K`, `X = E ∖ {O}` (`hypCurveX E`),
`Π_X` its arithmetic fundamental group (`arithmeticExt`), `C = [X / ±1]` the hemi-elliptic
orbicurve in Galois form (`CurvesJacobian.Cusp.hemiData E`, `Π_C = etalePi1 R A Ω`) and
`hemiPiXEmb : Π_X ↪ Π_C` (`CurvesJacobian.Cusp.HemiArith`).

* `hemiNegSections E : Γ(E ∖ {O}) ≃ₐ[K] Γ(E ∖ {O})`, the automorphism `[−1]`: under
  `sectionsXEAlgEquiv : Γ(E ∖ {O}) ≃ₐ[K] K[E]` it is `negYCoordEquiv` (`x ↦ x`,
  `y ↦ −y − a₁x − a₃`; `sectionsXEAlgEquiv_hemiNegSections`), and under
  `sectionsXEHemiAlgEquiv : Γ(E ∖ {O}) ≃ₐ[K] R` it is the action of the nontrivial element of
  `A ≅ ℤ/2` (`sectionsXEHemiAlgEquiv_hemiNegSections`).
* Generic (any Galois data `D`, `h₀ ∈ H`): `Spec(h₀ •) : Spec R ⟶ Spec R` moves the base point
  `Spec Ω ⟶ Spec R` by `Spec h₀` (`specPoint_comp_galSmul₃`); after the change of field
  `fieldChangeIso`, `π₁ᵉᵗ(Spec(h₀ •))` maps the Galois action of `σ ∈ H_L` to that of
  `h₀⁻¹ σ h₀` (`fieldChange_galoisHomL_galSmul₃`, from the generic
  `galoisAction_fieldChange_twist₃`). Hence (`exists_conj_of_isConjInduced_galSmul₃`) every map
  induced by `Spec(h₀ •)` up to a change of base point becomes, inside `H ⧸ ⟨⟨S⟩⟩`, conjugation
  by an element `x` with `x · [h₀] ∈ H_L ⧸ ⟨⟨S⟩⟩`.
* **`hemiInv_conj`**: every `φ : Π_X → Π_X` induced by `Spec [−1]` up to a change of base point
  (`IsConjInduced`) is the restriction of an inner automorphism of `Π_C`, by an element
  `τ ∉ Π_X`: `hemiPiXEmb (φ γ) = τ · hemiPiXEmb γ · τ⁻¹`.

No hypotheses beyond the data; no DGC input.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale Pi1.Orbifold AffOrbicurve
open PreGaloisCategory Topology CurvesJacobian CurvesJacobian.Cusp Belyi Belyi.P1 Belyi.Anabelian
open WeierstrassCurve.Affine.CoordinateRing

universe u

noncomputable section

namespace Iut.Reconstruction.HemiCore

section GroupAux

/-- If `Q b = c⁻¹ q c`, then `Q (a b a⁻¹)` is `q` conjugated by `Q a · c⁻¹`. -/
lemma map_conj_aux₃ {P C : Type*} [Group P] [Group C] (Q : P →* C) (a b : P) (c q : C)
    (hb : Q b = c⁻¹ * q * c) : Q (a * b * a⁻¹) = (Q a * c⁻¹) * q * (Q a * c⁻¹)⁻¹ := by
  rw [map_mul, map_mul, map_inv, hb]
  group

/-- A continuous isomorphism maps conjugates to conjugates. -/
lemma map_conj₃ {G H : Type*} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]
    (f : G ≃ₜ* H) (a b : G) : f (a * b * a⁻¹) = f a * f b * (f a)⁻¹ := by
  rw [map_mul, map_mul, map_inv]

end GroupAux

section Twist

variable {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]

/-- **The Galois action under a twisted change of field**: if `j : Spec F ⟶ X` lies over
`Spec σ ≫ η` and `j'` over `η`, then conjugation by `fieldChangeIso σ η` carries the action of
`g` through `j` to the action of `g' = σ⁻¹ g σ` through `j'`. -/
lemma galoisAction_fieldChange_twist₃ (σ : Ω ≃+* Ω) (η : Spec (.of Ω) ⟶ X)
    (F : Type u) [Field F] [Algebra F Ω] [_root_.IsGalois F Ω] (j j' : Spec (.of F) ⟶ X)
    (h : Spec.map (CommRingCat.ofHom (algebraMap F Ω)) ≫ j = specIso σ ≫ η)
    (h' : Spec.map (CommRingCat.ofHom (algebraMap F Ω)) ≫ j' = η)
    (g g' : Ω ≃ₐ[F] Ω) (hg : ∀ x, g' x = σ.symm (g (σ x))) :
    autContinuousMulEquivOfIso (fieldChangeIso σ η) (galoisAction F j h g) =
      galoisAction F j' h' g' := by
  refine ext_of_hom_app_left fun A x ↦ ?_
  rw [galoisAction_hom_app_left]
  change (fiberObjEquivHom η A ((fieldChangeIso σ η).hom.app A
    ((galoisAction F j h g).hom.app A ((fieldChangeIso σ η).inv.app A x)))).left = _
  rw [fieldChangeIso_hom_app]
  change specIso σ.symm ≫ (fiberObjEquivHom _ A ((galoisAction F j h g).hom.app A
    ((fieldChangeIso σ η).inv.app A x))).left = _
  rw [galoisAction_hom_app_left, fieldChangeIso_inv_app]
  change specIso σ.symm ≫ Spec.map (CommRingCat.ofHom (g : Ω →+* Ω)) ≫ specIso σ ≫
    (fiberObjEquivHom η A x).left = _
  have hs : specIso σ.symm ≫ Spec.map (CommRingCat.ofHom (g : Ω →+* Ω)) ≫ specIso σ =
      Spec.map (CommRingCat.ofHom (g' : Ω →+* Ω)) := by
    rw [specIso, specIso, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp]
    exact congrArg (fun ψ => Spec.map (CommRingCat.ofHom ψ)) (RingHom.ext fun y => (hg y).symm)
  rw [← hs]
  simp only [Category.assoc]

end Twist

section GenericConj

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω} (D : GaloisData k t)

/-- The action of `h₀ ∈ H` on `R` (through `A = H ⧸ H_L`), as a ring endomorphism. -/
abbrev galSmulRingHom₃ (h₀ : D.H) : D.R →+* D.R :=
  MulSemiringAction.toRingHom D.A D.R (h₀ : D.A)

lemma algebraMap_galSmulRingHom₃ (h₀ : D.H) (r : D.R) :
    algebraMap D.R Ω (galSmulRingHom₃ D h₀ r) =
      (h₀ : Ω ≃ₐ[K₀ k t] Ω) (algebraMap D.R Ω r) :=
  D.algebraMap_smul h₀ r

/-- `Spec(h₀ •)` moves the base point `Spec Ω ⟶ Spec R` by `Spec h₀`. -/
lemma specPoint_comp_galSmul₃ (h₀ : D.H) [IsSepClosed Ω] :
    specPoint D.R Ω ≫ Spec.map (CommRingCat.ofHom (galSmulRingHom₃ D h₀)) =
      specIso (h₀ : Ω ≃ₐ[K₀ k t] Ω).toRingEquiv ≫ specPoint D.R Ω := by
  rw [specIso, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp]
  exact congrArg (fun ψ => Spec.map (CommRingCat.ofHom ψ))
    (RingHom.ext fun r => (algebraMap_galSmulRingHom₃ D h₀ r).symm)

variable [IsAlgClosed Ω] [_root_.IsGalois (K₀ k t) Ω]

/-- The class of `h ∈ H` in `Π_C = H ⧸ ⟨⟨S⟩⟩`. -/
abbrev galClass₃ (h : D.H) : GaloisPi1.pi1 D.H D.S D.isClosed_H :=
  (QuotientGroup.mk h : D.H ⧸ GaloisPi1.kernel D.H D.S)

/-- **`π₁ᵉᵗ(Spec(h₀ •))` is conjugation by `h₀`**: after the change of field `fieldChangeIso`
along `h₀`, the Galois action of `σ ∈ H_L` goes to the Galois action of `h₀⁻¹ σ h₀`. -/
lemma fieldChange_galoisHomL_galSmul₃ (h₀ : D.H) (σ : D.HL) :
    autContinuousMulEquivOfIso
        (fieldChangeIso (h₀ : Ω ≃ₐ[K₀ k t] Ω).toRingEquiv (specPoint D.R Ω))
        (fundamentalGroupMap (Spec.map (CommRingCat.ofHom (galSmulRingHom₃ D h₀)))
          (specPoint_comp_galSmul₃ D h₀) (D.galoisHomL σ)) =
      D.galoisHomL ⟨(h₀ : Ω ≃ₐ[K₀ k t] Ω)⁻¹ * σ * h₀, D.conj_mem' h₀.2 σ.2⟩ := by
  have h : Spec.map (CommRingCat.ofHom (algebraMap D.L Ω)) ≫ D.genericPoint ≫
      Spec.map (CommRingCat.ofHom (galSmulRingHom₃ D h₀)) =
      specIso (h₀ : Ω ≃ₐ[K₀ k t] Ω).toRingEquiv ≫ specPoint D.R Ω := by
    rw [← Category.assoc, D.genericPoint_comp]
    exact specPoint_comp_galSmul₃ D h₀
  have e1 := fundamentalGroupMap_galoisAction D.L D.genericPoint
    (Spec.map (CommRingCat.ofHom (galSmulRingHom₃ D h₀))) D.genericPoint_comp
    (specPoint_comp_galSmul₃ D h₀) h (D.toGalL σ)
  rw [GaloisData.galoisHomL_eq, e1, GaloisData.galoisHomL_eq]
  exact galoisAction_fieldChange_twist₃ _ _ D.L _ _ h D.genericPoint_comp _ _ fun _ => rfl

variable [CharZero k]

/-- The class of `σ ∈ H_L` in `π₁ᵉᵗ(Spec R) ≅ H_L ⧸ ⟨⟨S⟩⟩`, pushed to `H ⧸ ⟨⟨S⟩⟩`. -/
lemma orbiIncl_galoisHomL₃ (σ : D.HL) :
    orbiIncl D ((galoisDataHL D).equivPi1Spec (galoisDataHL_H_le D) (D.galoisHomL σ)) =
      (QuotientGroup.mk (Subgroup.inclusion D.le σ) : D.H ⧸ GaloisPi1.kernel D.H D.S) := by
  have h : (galoisDataHL D).equivPi1Spec (galoisDataHL_H_le D) (D.galoisHomL σ) =
      (QuotientGroup.mk σ : D.HL ⧸ GaloisPi1.kernel D.HL D.S) := by
    rw [ContinuousMulEquiv.apply_eq_iff_symm_apply]
    exact ((galoisDataHL D).equivPi1Spec_symm_mk (galoisDataHL_H_le D) σ).symm
  rw [h, orbiIncl_mk]

/-- **`π₁ᵉᵗ(Spec(h₀ •))` in `H ⧸ ⟨⟨S⟩⟩`**: after the change of field, it is conjugation by
`[h₀]⁻¹`. -/
lemma orbiIncl_fieldChange_galSmul₃ (h₀ : D.H) (z : π₁ᵉᵗ(specPoint D.R Ω)) :
    orbiIncl D ((galoisDataHL D).equivPi1Spec (galoisDataHL_H_le D)
      (autContinuousMulEquivOfIso
        (fieldChangeIso (h₀ : Ω ≃ₐ[K₀ k t] Ω).toRingEquiv (specPoint D.R Ω))
        (fundamentalGroupMap (Spec.map (CommRingCat.ofHom (galSmulRingHom₃ D h₀)))
          (specPoint_comp_galSmul₃ D h₀) z))) =
      (galClass₃ D h₀)⁻¹ *
        orbiIncl D ((galoisDataHL D).equivPi1Spec (galoisDataHL_H_le D) z) * galClass₃ D h₀ := by
  obtain ⟨σ, rfl⟩ := D.galoisHomL_surjective z
  rw [fieldChange_galoisHomL_galSmul₃, orbiIncl_galoisHomL₃, orbiIncl_galoisHomL₃]
  change QuotientGroup.mk' (GaloisPi1.kernel D.H D.S) _ =
    (QuotientGroup.mk' (GaloisPi1.kernel D.H D.S) h₀)⁻¹ *
      QuotientGroup.mk' (GaloisPi1.kernel D.H D.S) _ *
      QuotientGroup.mk' (GaloisPi1.kernel D.H D.S) h₀
  rw [← map_inv, ← map_mul, ← map_mul]
  rfl

/-- **Generic form.** Let `i : Spec R ≅ Y`, `F` a change of base point, `g : Y ⟶ Y` with
`i ≫ g = Spec(h₀ •) ≫ i`. Every `φ` induced by `g` up to a change of base point is, inside
`H ⧸ ⟨⟨S⟩⟩`, conjugation by an element `x` with `x · [h₀] ∈ range ι`. -/
theorem exists_conj_of_isConjInduced_galSmul₃ {Y : Scheme.{u}} (i : Spec (.of D.R) ≅ Y)
    {Ω' : Type u} [Field Ω'] {y : Spec (.of Ω') ⟶ Y}
    (F : fiber y ≅ fiber (specPoint D.R Ω ≫ i.hom)) (g : Y ⟶ Y) (h₀ : D.H)
    (hsq : i.hom ≫ g = Spec.map (CommRingCat.ofHom (galSmulRingHom₃ D h₀)) ≫ i.hom)
    {φ : π₁ᵉᵗ(y) → π₁ᵉᵗ(y)} (hφ : IsConjInduced g φ) :
    ∃ x : GaloisPi1.pi1 D.H D.S D.isClosed_H,
      x * galClass₃ D h₀ ∈
        (orbiIncl D).toMonoidHom.range ∧
      ∀ γ, orbiIncl D ((galoisDataHL D).equivPi1Spec (galoisDataHL_H_le D)
          ((fundamentalGroupEquivOfIso i (specPoint D.R Ω)).symm
            (autContinuousMulEquivOfIso F (φ γ)))) =
        x * orbiIncl D ((galoisDataHL D).equivPi1Spec (galoisDataHL_H_le D)
          ((fundamentalGroupEquivOfIso i (specPoint D.R Ω)).symm
            (autContinuousMulEquivOfIso F γ))) * x⁻¹ := by
  have hx := specPoint_comp_galSmul₃ D h₀
  obtain ⟨t₀, ht₀⟩ := exists_conj_of_isConjInduced_iso₃ i i
    (Spec.map (CommRingCat.ofHom (galSmulRingHom₃ D h₀))) g hsq hx F
    (F ≪≫ fiberIsoMap i.hom rfl rfl
      (fieldChangeIso (h₀ : Ω ≃ₐ[K₀ k t] Ω).toRingEquiv (specPoint D.R Ω)).symm) hφ
  have hP : ∀ γ, (fundamentalGroupEquivOfIso i
      (specIso (h₀ : Ω ≃ₐ[K₀ k t] Ω).toRingEquiv ≫ specPoint D.R Ω)).symm
        (autContinuousMulEquivOfIso (F ≪≫ fiberIsoMap i.hom rfl rfl
          (fieldChangeIso (h₀ : Ω ≃ₐ[K₀ k t] Ω).toRingEquiv (specPoint D.R Ω)).symm) (φ γ)) =
      autContinuousMulEquivOfIso
        (fieldChangeIso (h₀ : Ω ≃ₐ[K₀ k t] Ω).toRingEquiv (specPoint D.R Ω)).symm
        ((fundamentalGroupEquivOfIso i (specPoint D.R Ω)).symm
          (autContinuousMulEquivOfIso F (φ γ))) := by
    intro γ
    rw [ContinuousMulEquiv.symm_apply_eq]
    have e1 := fundamentalGroupMap_autContinuousMulEquivOfIso i.hom
      (rfl : specPoint D.R Ω ≫ i.hom = _)
      (rfl : (specIso (h₀ : Ω ≃ₐ[K₀ k t] Ω).toRingEquiv ≫ specPoint D.R Ω) ≫ i.hom = _)
      (fieldChangeIso (h₀ : Ω ≃ₐ[K₀ k t] Ω).toRingEquiv (specPoint D.R Ω)).symm
      ((fundamentalGroupEquivOfIso i (specPoint D.R Ω)).symm
        (autContinuousMulEquivOfIso F (φ γ)))
    have e2 : fundamentalGroupMap i.hom rfl ((fundamentalGroupEquivOfIso i
        (specPoint D.R Ω)).symm (autContinuousMulEquivOfIso F (φ γ))) =
        autContinuousMulEquivOfIso F (φ γ) :=
      (fundamentalGroupEquivOfIso i (specPoint D.R Ω)).apply_symm_apply _
    rw [e2] at e1
    exact (e1.trans (Iso.trans_conjAut _ _ _).symm).symm
  have hWc : ∀ z : π₁ᵉᵗ(specPoint D.R Ω), autContinuousMulEquivOfIso
      (fieldChangeIso (h₀ : Ω ≃ₐ[K₀ k t] Ω).toRingEquiv (specPoint D.R Ω))
      (autContinuousMulEquivOfIso
        (fieldChangeIso (h₀ : Ω ≃ₐ[K₀ k t] Ω).toRingEquiv (specPoint D.R Ω)).symm z) = z := by
    intro z
    change (fieldChangeIso (h₀ : Ω ≃ₐ[K₀ k t] Ω).toRingEquiv (specPoint D.R Ω)).conjAut
      ((fieldChangeIso (h₀ : Ω ≃ₐ[K₀ k t] Ω).toRingEquiv (specPoint D.R Ω)).symm.conjAut z) = z
    rw [← Iso.trans_conjAut, Iso.symm_self_id, Iso.conjAut_apply]
    simp
  have key : ∀ γ, (fundamentalGroupEquivOfIso i (specPoint D.R Ω)).symm
      (autContinuousMulEquivOfIso F (φ γ)) =
      autContinuousMulEquivOfIso
        (fieldChangeIso (h₀ : Ω ≃ₐ[K₀ k t] Ω).toRingEquiv (specPoint D.R Ω)) t₀ *
      autContinuousMulEquivOfIso
        (fieldChangeIso (h₀ : Ω ≃ₐ[K₀ k t] Ω).toRingEquiv (specPoint D.R Ω))
        (fundamentalGroupMap (Spec.map (CommRingCat.ofHom (galSmulRingHom₃ D h₀))) hx
          ((fundamentalGroupEquivOfIso i (specPoint D.R Ω)).symm
            (autContinuousMulEquivOfIso F γ))) *
      (autContinuousMulEquivOfIso
        (fieldChangeIso (h₀ : Ω ≃ₐ[K₀ k t] Ω).toRingEquiv (specPoint D.R Ω)) t₀)⁻¹ := by
    intro γ
    rw [← map_inv, ← map_mul, ← map_mul, ← ht₀ γ, hP γ, hWc]
  refine ⟨orbiIncl D ((galoisDataHL D).equivPi1Spec (galoisDataHL_H_le D)
      (autContinuousMulEquivOfIso
        (fieldChangeIso (h₀ : Ω ≃ₐ[K₀ k t] Ω).toRingEquiv (specPoint D.R Ω)) t₀)) *
      (galClass₃ D h₀)⁻¹,
    ⟨_, (inv_mul_cancel_right _ _).symm⟩, fun γ => ?_⟩
  rw [key γ]
  exact map_conj_aux₃ ((orbiIncl D).toMonoidHom.comp
    ((galoisDataHL D).equivPi1Spec (galoisDataHL_H_le D)).toMulEquiv.toMonoidHom) _ _ _ _
    (orbiIncl_fieldChange_galSmul₃ D h₀ _)

end GenericConj

section HemiNeg

variable {K : Type u} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]

/-- **`[−1]` on `Γ(E ∖ {O})`**: `negYCoordEquiv` (`x ↦ x`, `y ↦ −y − a₁x − a₃`) on `K[E]`,
transported along `sectionsXEAlgEquiv : Γ(E ∖ {O}) ≃ₐ[K] K[E]`. -/
def hemiNegSections : Γ(curveE E, XE E) ≃ₐ[K] Γ(curveE E, XE E) :=
  (sectionsXEAlgEquiv E).trans
    (((negYCoordEquiv E.toAffine).restrictScalars K).trans (sectionsXEAlgEquiv E).symm)

lemma hemiNegSections_apply (s : Γ(curveE E, XE E)) :
    hemiNegSections E s =
      (sectionsXEAlgEquiv E).symm (negYCoordEquiv E.toAffine (sectionsXEAlgEquiv E s)) := rfl

/-- `[−1]` under `Γ(E ∖ {O}) ≃ K[E]` is `negYCoordEquiv`. -/
lemma sectionsXEAlgEquiv_hemiNegSections (s : Γ(curveE E, XE E)) :
    sectionsXEAlgEquiv E (hemiNegSections E s) =
      negYCoordEquiv E.toAffine (sectionsXEAlgEquiv E s) :=
  (sectionsXEAlgEquiv E).apply_symm_apply _

/-- `[−1]` under `Γ(E ∖ {O}) ≃ R` is the action of the nontrivial element of `A ≅ ℤ/2`. -/
lemma sectionsXEHemiAlgEquiv_hemiNegSections (h : (hemiData E).H)
    (hh : (h : (hemiData E).A) ≠ 1) (s : Γ(curveE E, XE E)) :
    sectionsXEHemiAlgEquiv E (hemiNegSections E s) =
      (h : (hemiData E).A) • sectionsXEHemiAlgEquiv E s := by
  have key := hemi_smul_hemiREquiv E h hh (sectionsXEAlgEquiv E s)
  have h1 : hemiREquiv E (sectionsXEAlgEquiv E s) = sectionsXEHemiAlgEquiv E s :=
    congrArg (sectionsXEHemiAlgEquiv E) ((sectionsXEAlgEquiv E).symm_apply_apply s)
  have h2 : hemiREquiv E (negYCoordEquiv E.toAffine (sectionsXEAlgEquiv E s)) =
      sectionsXEHemiAlgEquiv E (hemiNegSections E s) := rfl
  rw [h1, h2] at key
  exact key.symm

/-- `A = H ⧸ H_L` has a nontrivial element (`|A| = 2`). -/
lemma exists_hemiA_ne_one₃ : ∃ h : (hemiData E).H, (h : (hemiData E).A) ≠ 1 := by
  obtain ⟨a, b, hab, -⟩ := Nat.card_eq_two_iff.1 (card_hemiA E)
  have hne : ∃ c : (hemiData E).A, c ≠ 1 := by
    by_cases ha : a = 1
    · exact ⟨b, fun hb => hab (ha.trans hb.symm)⟩
    · exact ⟨a, ha⟩
  obtain ⟨c, hc⟩ := hne
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective c
  exact ⟨h, hc⟩

end HemiNeg

section Hemi

variable {K : Type u} [Field K] [NumberField K] (E : WeierstrassCurve K) [E.IsElliptic]
  (Ω' : Type u) [Field Ω'] [Algebra K Ω'] [IsAlgClosed Ω'] [Algebra.IsAlgebraic K Ω']
  [CharZero Ω']

/-- `Spec R ≅ Spec Γ(E ∖ {O})` intertwines `Spec(h •)` and `Spec [−1]`. -/
lemma hemiSpecIso_hom_neg₃ (h : (hemiData E).H) (hh : (h : (hemiData E).A) ≠ 1) :
    (hemiSpecIso E).hom ≫ Spec.map (CommRingCat.ofHom
      (hemiNegSections E).toRingEquiv.toRingHom) =
      Spec.map (CommRingCat.ofHom (galSmulRingHom₃ (hemiData E) h)) ≫ (hemiSpecIso E).hom := by
  have hr : CommRingCat.ofHom (hemiNegSections E).toRingEquiv.toRingHom ≫
      CommRingCat.ofHom (sectionsXEHemiAlgEquiv E).toRingEquiv.toRingHom =
      CommRingCat.ofHom (sectionsXEHemiAlgEquiv E).toRingEquiv.toRingHom ≫
        CommRingCat.ofHom (galSmulRingHom₃ (hemiData E) h) := by
    ext s
    exact sectionsXEHemiAlgEquiv_hemiNegSections E h hh s
  exact (Spec.map_comp _ _).symm.trans ((congrArg Spec.map hr).trans (Spec.map_comp _ _))

/-- **`π₁([−1])` is conjugation by an element of `Π_C`** ([AbsTopII] Cor. 3.3, IUT I §1: the
hemi-elliptic orbicurve `C = [(E ∖ {O}) / ±1]`): every `φ : Π_X → Π_X` induced by
`Spec [−1] : Spec Γ(E ∖ {O}) ⟶ Spec Γ(E ∖ {O})` up to a change of base point is the restriction
of the inner automorphism of `Π_C` by some `τ ∉ Π_X`. -/
theorem hemiInv_conj
    {φ : (arithmeticExt Ω' (hypCurveX E) (compl_XE_nonempty E)).Pi →
      (arithmeticExt Ω' (hypCurveX E) (compl_XE_nonempty E)).Pi}
    (hφ : IsConjInduced (Spec.map (CommRingCat.ofHom
      (hemiNegSections E).toRingEquiv.toRingHom)) φ) :
    ∃ τ : etalePi1 (hemiData E).R (hemiData E).A (FFClosure (curveE E)),
      τ ∉ (hemiPiXEmb E Ω').toMonoidHom.range ∧
      ∀ γ, hemiPiXEmb E Ω' (φ γ) = τ * hemiPiXEmb E Ω' γ * τ⁻¹ := by
  obtain ⟨h₀, hh₀⟩ := exists_hemiA_ne_one₃ E
  obtain ⟨x, hxr, hx⟩ := exists_conj_of_isConjInduced_galSmul₃ (hemiData E) (hemiSpecIso E)
    (hemiFiberIso E Ω') _ h₀ (hemiSpecIso_hom_neg₃ E h₀ hh₀) hφ
  have e1 : ∀ γ, hemiPiXEmb E Ω' γ = (hemiData E).equivPi1.symm
      (orbiIncl (hemiData E) ((galoisDataHL (hemiData E)).equivPi1Spec
        (galoisDataHL_H_le (hemiData E)) ((fundamentalGroupEquivOfIso (hemiSpecIso E)
          (specPoint (hemiData E).R (FFClosure (curveE E)))).symm
            (autContinuousMulEquivOfIso (hemiFiberIso E Ω') γ)))) := fun _ => rfl
  refine ⟨(hemiData E).equivPi1.symm x, ?_, fun γ => ?_⟩
  · rintro ⟨γ, hγ⟩
    have h2 : (hemiData E).equivPi1.symm
        (orbiIncl (hemiData E) ((galoisDataHL (hemiData E)).equivPi1Spec
          (galoisDataHL_H_le (hemiData E)) ((fundamentalGroupEquivOfIso (hemiSpecIso E)
            (specPoint (hemiData E).R (FFClosure (curveE E)))).symm
              (autContinuousMulEquivOfIso (hemiFiberIso E Ω') γ)))) =
        (hemiData E).equivPi1.symm x := (e1 γ).symm.trans hγ
    have h3 : x ∈ (orbiIncl (hemiData E)).toMonoidHom.range :=
      ⟨_, (hemiData E).equivPi1.symm.injective h2⟩
    have h4 := (orbiIncl (hemiData E)).toMonoidHom.range.mul_mem
      ((orbiIncl (hemiData E)).toMonoidHom.range.inv_mem h3) hxr
    rw [inv_mul_cancel_left, ← ker_orbiProj, MonoidHom.mem_ker] at h4
    exact hh₀ ((orbiProj_mk (hemiData E) h₀).symm.trans h4)
  · rw [e1, e1, hx γ]
    exact map_conj₃ _ _ _

end Hemi

end Iut.Reconstruction.HemiCore
