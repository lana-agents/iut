/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.CoverInstance
import CurvesJacobian.Cusp.CoverRangeOpen
import CurvesJacobian.Cusp.FieldTwistDGC

/-!
# Isomorphic open subgroups of `Π_X` over `G_K` come from isomorphic covers

Let `C` be a hyperbolic curve over a number field `K` with a cusp, `X = Spec Γ(X̄, U)` and
`Π_X = π₁ᵉᵗ(X, x)` at the base point `x = basePoint ≫ baseChangeSpec` of
`CurvesJacobian.Cusp.arithmeticExt`. For open subgroups `Q₁, Q₂ ⊆ Π_X` and a continuous
isomorphism `ψ : Q₁ ≃ₜ* Q₂` over `G_K` (`pr ∘ ψ = pr`), there are connected finite étale covers
`p_i : V_i ⟶ X` with `π₁ᵉᵗ(V_i) = Q_i` and an isomorphism `F : V₁ ≅ V₂` over `Spec K` such that
`ψ` is, up to an inner automorphism of `Π_X`, the restriction of every map `φ : Π_X → Π_X`
induced (up to a change of base point) by an endomorphism `h` of `X` with `F ≫ p₂ = p₁ ≫ h`
(`Iut.Reconstruction.exists_coverIso_of_openSubgroup_iso`; ring form
`Iut.Reconstruction.exists_ringIso_of_openSubgroup_iso`).

Proof: `Q_i` is the image of `π₁ᵉᵗ` of a connected finite étale cover `p_i : V_i ⟶ X`
(`CurvesJacobian.Cusp.exists_isFiniteEtale_range_eq_of_open`, Stacks 0BN4); `V_i ≅ Spec Γ(Y_i)`
for the hyperbolic curve `Y_i = CurvesJacobian.Cusp.coverCurve` over its field of constants `k_i`
(a number field). `Π_{Y_i} ≃ₜ* Q_i` (`Iut.Reconstruction.exists_coverTheta`) lies over
`res : G_{k_i} → G_K` up to conjugation, so `ψ` transports to `Φ : Π_{Y₁} ≃ₜ* Π_{Y₂}` lying over
conjugation in `G_K`; the rel-isom-DGC across two fields
(`CurvesJacobian.Cusp.exists_isConjInduced_of_relIsomDGC_field`, existence half `hDGC` for `k₁`
only, the recorded whitelist input) gives a `K`-semilinear `F' : Spec Γ(Y₁) ≅ Spec Γ(Y₂)`
inducing `Φ`, and `F = e₁⁻¹ ≫ F' ≫ e₂`. Two maps induced by the same morphism differ by an inner
automorphism (`Iut.Reconstruction.exists_conj_of_isConjInduced_same`).
-/

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.FiniteEtale Belyi
  Belyi.Anabelian PreGaloisCategory CurvesJacobian.Cusp

universe u

noncomputable section

namespace Iut.Reconstruction

section ConjInduced

variable {X Y : Scheme.{u}} {Ω : Type u} [Field Ω]

/-- **Two maps induced by the same morphism differ by an inner automorphism** of the target. -/
lemma exists_conj_of_isConjInduced_same {h : X ⟶ Y} {x : Spec (.of Ω) ⟶ X}
    {y : Spec (.of Ω) ⟶ Y} {φ₁ φ₂ : π₁ᵉᵗ(x) → π₁ᵉᵗ(y)} (H₁ : IsConjInduced h φ₁)
    (H₂ : IsConjInduced h φ₂) : ∃ t : π₁ᵉᵗ(y), ∀ σ, φ₁ σ = t * φ₂ σ * t⁻¹ := by
  obtain ⟨γ₀, h₀⟩ := H₂
  obtain ⟨t, ht⟩ := (isConjInduced_iff_exists_conj h γ₀ φ₁).1 H₁
  exact ⟨t, fun σ ↦ (ht σ).trans (by rw [h₀])⟩

/-- `π₁ᵉᵗ(p)` with a prescribed target point is induced by `p`. -/
lemma isConjInduced_fundamentalGroupMap_of_eq (p : X ⟶ Y) {ζ : Spec (.of Ω) ⟶ X}
    {x : Spec (.of Ω) ⟶ Y} (hζ : ζ ≫ p = x) : IsConjInduced p (fundamentalGroupMap p hζ) := by
  subst hζ
  exact isConjInduced_fundamentalGroupMap p ζ

end ConjInduced

/-- Equal subgroups are isomorphic topological groups (with `↑(e g) = ↑g` definitionally). -/
def continuousSubgroupCongrVal {G : Type*} [Group G] [TopologicalSpace G] {H H' : Subgroup G}
    (h : H = H') : H ≃ₜ* H' :=
  { MulEquiv.subgroupCongr h with
    continuous_toFun := continuous_subtype_val.subtype_mk _
    continuous_invFun := continuous_subtype_val.subtype_mk _ }

section Cover

variable {K : Type u} [Field K] [NumberField K] {Ω : Type u} [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] {C : HypCurve K}
  {hc : (C.U : Set C.Xbar)ᶜ.Nonempty}

omit [Algebra.IsAlgebraic K Ω] in
/-- **`Π_Y ≃ₜ* Q` for a cover curve**: if `Q ⊆ Π_X` is the image of `π₁ᵉᵗ` of a connected finite
étale `p : V ⟶ X` at `ζ`, and `e : Spec Γ(Y) ≅ V` for a hyperbolic curve `Y` over `M ⊇ K`
compatibly with the structure maps, then there is `θ : Π_Y ≃ₜ* Q` induced by `e ≫ p` and lying
over `res : G_M → G_K` up to conjugation. -/
lemma exists_coverTheta {M : Type u} [Field M] [NumberField M] [Algebra K M] [Algebra M Ω]
    [IsScalarTower K M Ω] (Y : HypCurve M) (hY : (Y.U : Set Y.Xbar)ᶜ.Nonempty) {V : Scheme.{u}}
    (p : V ⟶ Spec Γ(C.Xbar, C.U)) [IsFiniteEtale p] [ConnectedSpace V] (ζ : Spec (.of Ω) ⟶ V)
    (hζ : ζ ≫ p = basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U))
    (e : Spec Γ(Y.Xbar, Y.U) ≅ V)
    (he : e.hom ≫ p ≫ sKU C = sKU Y ≫ Spec.map (CommRingCat.ofHom (algebraMap K M)))
    (Q : Subgroup π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U)))
    (hQ : (fundamentalGroupMap p hζ).toMonoidHom.range = Q) :
    ∃ (θ : π₁ᵉᵗ(basePoint Ω Y hY ≫ baseChangeSpec M Ω Γ(Y.Xbar, Y.U)) ≃ₜ* Q)
      (c : π₁ᵉᵗ(Spec.map (CommRingCat.ofHom (algebraMap K Ω)))),
      IsConjInduced (e.hom ≫ p)
          (fun σ ↦ (θ σ : π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U)))) ∧
        ∀ σ, projGk Ω C hc (θ σ) = c * galoisMap K M Ω (projGk Ω Y hY σ) * c⁻¹ := by
  have hQ' : (coverSubgroup p ζ hζ : Subgroup _) = Q :=
    (range_fundamentalGroupMap_eq_coverSubgroup p ζ hζ).symm.trans hQ
  let γ : fiber ((basePoint Ω Y hY ≫ baseChangeSpec M Ω Γ(Y.Xbar, Y.U)) ≫ e.hom) ≅ fiber ζ :=
    (nonempty_iso_of_fiberFunctor _ _).some
  let θ : π₁ᵉᵗ(basePoint Ω Y hY ≫ baseChangeSpec M Ω Γ(Y.Xbar, Y.U)) ≃ₜ* Q :=
    ((CurvesJacobian.fundamentalGroupEquivOfIso e _).trans (autContinuousMulEquivOfIso γ)).trans
      ((coverEquiv p ζ hζ).trans (continuousSubgroupCongrVal hQ'))
  have H0 : IsConjInduced e.hom
      (fun σ ↦ autContinuousMulEquivOfIso γ (fundamentalGroupMap e.hom rfl σ)) :=
    ⟨γ, fun _ ↦ rfl⟩
  have H1 : IsConjInduced (e.hom ≫ p)
      (fun σ ↦ (θ σ : π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U)))) :=
    (H0.comp (isConjInduced_fundamentalGroupMap_of_eq p hζ)).congr_fun fun _ ↦ rfl
  have H2 : IsConjInduced ((e.hom ≫ p) ≫ sKU C) (fun σ ↦ projGk Ω C hc (θ σ)) :=
    (H1.comp (isConjInduced_fundamentalGroupMap_of_eq (sKU C) (basePoint_spec₂ Ω C hc))).congr_fun
      fun _ ↦ rfl
  have H3 : IsConjInduced (sKU Y ≫ Spec.map (CommRingCat.ofHom (algebraMap K M)))
      (fun σ ↦ galoisMap K M Ω (projGk Ω Y hY σ)) :=
    ((isConjInduced_fundamentalGroupMap_of_eq (sKU Y) (basePoint_spec₂ Ω Y hY)).comp
      (isConjInduced_fundamentalGroupMap_of_eq _ (specMap_algebraMap_tower K M Ω))).congr_fun
      fun _ ↦ rfl
  have hmor : (e.hom ≫ p) ≫ sKU C = sKU Y ≫ Spec.map (CommRingCat.ofHom (algebraMap K M)) := by
    rw [Category.assoc, he]
  obtain ⟨c, hc'⟩ := exists_conj_of_isConjInduced_same (H2.congr_hom hmor) H3
  exact ⟨θ, c, H1, hc'⟩

attribute [local instance] isAlgClosure_of_isAlgebraic

/-- **Covers with isomorphic groups over `G_K` are isomorphic** (generic form, two covers
`p_i : V_i ⟶ X` with given cover curves `Y_i` over number fields `M_i ⊇ K`): for
`ψ : Q₁ ≃ₜ* Q₂` over `G_K`, where `Q_i` is the image of `π₁ᵉᵗ(V_i)`, there is `F : V₁ ≅ V₂`
over `Spec K` such that `ψ` is conjugate to the restriction of every map induced by an
endomorphism `h` of `X` with `F ≫ p₂ = p₁ ≫ h`. -/
theorem exists_iso_isConjInduced_of_covers {M₁ M₂ : Type u} [Field M₁] [NumberField M₁]
    [Algebra K M₁] [Algebra M₁ Ω] [IsScalarTower K M₁ Ω] [Algebra.IsAlgebraic M₁ Ω]
    [Field M₂] [NumberField M₂] [Algebra K M₂] [Algebra M₂ Ω] [IsScalarTower K M₂ Ω]
    [Algebra.IsAlgebraic M₂ Ω] (hDGC : RelIsomDGC.Exists M₁)
    (Y₁ : HypCurve M₁) (hY₁ : (Y₁.U : Set Y₁.Xbar)ᶜ.Nonempty)
    (Y₂ : HypCurve M₂) (hY₂ : (Y₂.U : Set Y₂.Xbar)ᶜ.Nonempty) {V₁ V₂ : Scheme.{u}}
    (p₁ : V₁ ⟶ Spec Γ(C.Xbar, C.U)) [IsFiniteEtale p₁] [ConnectedSpace V₁]
    (p₂ : V₂ ⟶ Spec Γ(C.Xbar, C.U)) [IsFiniteEtale p₂] [ConnectedSpace V₂]
    (ζ₁ : Spec (.of Ω) ⟶ V₁) (ζ₂ : Spec (.of Ω) ⟶ V₂)
    (hζ₁ : ζ₁ ≫ p₁ = basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U))
    (hζ₂ : ζ₂ ≫ p₂ = basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U))
    (e₁ : Spec Γ(Y₁.Xbar, Y₁.U) ≅ V₁) (e₂ : Spec Γ(Y₂.Xbar, Y₂.U) ≅ V₂)
    (he₁ : e₁.hom ≫ p₁ ≫ sKU C = sKU Y₁ ≫ Spec.map (CommRingCat.ofHom (algebraMap K M₁)))
    (he₂ : e₂.hom ≫ p₂ ≫ sKU C = sKU Y₂ ≫ Spec.map (CommRingCat.ofHom (algebraMap K M₂)))
    (Q₁ Q₂ : Subgroup π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U)))
    (hQ₁ : (fundamentalGroupMap p₁ hζ₁).toMonoidHom.range = Q₁)
    (hQ₂ : (fundamentalGroupMap p₂ hζ₂).toMonoidHom.range = Q₂) (ψ : Q₁ ≃ₜ* Q₂)
    (hψ : ∀ q, projGk Ω C hc (ψ q) = projGk Ω C hc q) :
    ∃ F : V₁ ≅ V₂, F.hom ≫ p₂ ≫ sKU C = p₁ ≫ sKU C ∧
      ∀ h : Spec Γ(C.Xbar, C.U) ⟶ Spec Γ(C.Xbar, C.U), F.hom ≫ p₂ = p₁ ≫ h →
        ∀ φ : π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U)) →
            π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U)),
          IsConjInduced h φ → ∃ δ, ∀ q : Q₁,
            (ψ q : π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U))) =
              δ * φ q * δ⁻¹ := by
  obtain ⟨θ₁, c₁, H₁, hθ₁⟩ := exists_coverTheta Y₁ hY₁ p₁ ζ₁ hζ₁ e₁ he₁ Q₁ hQ₁
  obtain ⟨θ₂, c₂, H₂, hθ₂⟩ := exists_coverTheta Y₂ hY₂ p₂ ζ₂ hζ₂ e₂ he₂ Q₂ hQ₂
  let Φ := θ₁.trans (ψ.trans θ₂.symm)
  have hΦ : ∀ σ, (θ₂ (Φ σ) : π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U))) =
      ψ (θ₁ σ) := fun σ ↦ congrArg Subtype.val (θ₂.apply_symm_apply _)
  have hres : ∀ σ, resGal K Ω M₂ (projGk Ω Y₂ hY₂ (Φ σ)) =
      (c₂⁻¹ * c₁) * resGal K Ω M₁ (projGk Ω Y₁ hY₁ σ) * (c₂⁻¹ * c₁)⁻¹ := by
    intro σ
    have h1 := hθ₂ (Φ σ)
    rw [hΦ, hψ, hθ₁] at h1
    change galoisMap K M₂ Ω (projGk Ω Y₂ hY₂ (Φ σ)) =
      (c₂⁻¹ * c₁) * galoisMap K M₁ Ω (projGk Ω Y₁ hY₁ σ) * (c₂⁻¹ * c₁)⁻¹
    calc galoisMap K M₂ Ω (projGk Ω Y₂ hY₂ (Φ σ))
        = c₂⁻¹ * (c₂ * galoisMap K M₂ Ω (projGk Ω Y₂ hY₂ (Φ σ)) * c₂⁻¹) * c₂ := by group
      _ = c₂⁻¹ * (c₁ * galoisMap K M₁ Ω (projGk Ω Y₁ hY₁ σ) * c₁⁻¹) * c₂ := by rw [h1]
      _ = _ := by group
  haveI : FiniteDimensional K M₁ := Module.Finite.of_restrictScalars_finite ℚ K M₁
  haveI : FiniteDimensional K M₂ := Module.Finite.of_restrictScalars_finite ℚ K M₂
  obtain ⟨α, F', hF', HF'⟩ := exists_isConjInduced_of_relIsomDGC_field hDGC Φ (c₂⁻¹ * c₁) hres
  refine ⟨e₁.symm ≪≫ F' ≪≫ e₂, ?_, ?_⟩
  · have hα : specRingEquiv₂ α.toRingEquiv ≫ Spec.map (CommRingCat.ofHom (algebraMap K M₂)) =
        Spec.map (CommRingCat.ofHom (algebraMap K M₁)) := specRingEquiv₂_sKM α
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
    rw [he₂, reassoc_of% hF', hα, ← he₁, Iso.inv_hom_id_assoc]
  · intro h hh φ Hφ
    have hh' : e₁.inv ≫ F'.hom ≫ e₂.hom ≫ p₂ = p₁ ≫ h := by
      simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc] using hh
    have heq : F'.hom ≫ e₂.hom ≫ p₂ = (e₁.hom ≫ p₁) ≫ h := by
      rw [Category.assoc, ← hh', Iso.hom_inv_id_assoc]
    have HA : IsConjInduced (F'.hom ≫ e₂.hom ≫ p₂)
        (fun σ ↦ (θ₂ (Φ σ) : π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U)))) :=
      (HF'.comp H₂).congr_fun fun _ ↦ rfl
    have HB : IsConjInduced ((e₁.hom ≫ p₁) ≫ h) (fun σ ↦ φ (θ₁ σ)) :=
      (H₁.comp Hφ).congr_fun fun _ ↦ rfl
    obtain ⟨δ, hδ⟩ := exists_conj_of_isConjInduced_same (HA.congr_hom heq) HB
    refine ⟨δ, fun q ↦ ?_⟩
    obtain ⟨σ, rfl⟩ := θ₁.surjective q
    rw [← hΦ]
    exact hδ σ

/-- **Lemma G: open subgroups of `Π_X` isomorphic over `G_K` come from isomorphic covers.**
For open subgroups `Q₁, Q₂ ⊆ Π_X` and a continuous isomorphism `ψ : Q₁ ≃ₜ* Q₂` with
`pr ∘ ψ = pr`, there are connected finite étale `p_i : V_i ⟶ Spec Γ(X̄, U)` (`V_i` integral and
affine) and `F : V₁ ≅ V₂` over `Spec K` such that for every endomorphism `h` of `Spec Γ(X̄, U)`
with `F ≫ p₂ = p₁ ≫ h` and every `φ : Π_X → Π_X` induced by `h` (up to a change of base point),
`ψ = conj(δ) ∘ φ` on `Q₁` for some `δ ∈ Π_X`. The existence half of the rel-isom-DGC enters
only as the explicit hypothesis `hDGC` (whitelist input). -/
theorem exists_coverIso_of_openSubgroup_iso
    (hDGC : ∀ (k : Type u) [Field k] [NumberField k], RelIsomDGC.Exists k)
    (Q₁ Q₂ : OpenSubgroup π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U)))
    (ψ : (Q₁ : Subgroup π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U))) ≃ₜ*
      (Q₂ : Subgroup π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U))))
    (hψ : ∀ q, projGk Ω C hc (ψ q) = projGk Ω C hc q) :
    ∃ (V₁ V₂ : Scheme.{u}) (p₁ : V₁ ⟶ Spec Γ(C.Xbar, C.U)) (p₂ : V₂ ⟶ Spec Γ(C.Xbar, C.U))
      (F : V₁ ≅ V₂), IsFiniteEtale p₁ ∧ IsFiniteEtale p₂ ∧ IsIntegral V₁ ∧ IsIntegral V₂ ∧
        IsAffine V₁ ∧ IsAffine V₂ ∧ F.hom ≫ p₂ ≫ sKU C = p₁ ≫ sKU C ∧
        ∀ h : Spec Γ(C.Xbar, C.U) ⟶ Spec Γ(C.Xbar, C.U), F.hom ≫ p₂ = p₁ ≫ h →
          ∀ φ : π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U)) →
              π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U)),
            IsConjInduced h φ → ∃ δ, ∀ q : Q₁,
              (ψ q : π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U))) =
                δ * φ q * δ⁻¹ := by
  haveI := isIntegral_specSections C hc
  obtain ⟨V₁, p₁, hp₁, ζ₁, hζ₁, hV₁, hQ₁⟩ :=
    exists_isFiniteEtale_range_eq_of_open (basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U))
      Q₁
  obtain ⟨V₂, p₂, hp₂, ζ₂, hζ₂, hV₂, hQ₂⟩ :=
    exists_isFiniteEtale_range_eq_of_open (basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U))
      Q₂
  haveI := hp₁
  haveI := hp₂
  haveI := hV₁
  haveI := hV₂
  letI := coverAlgebra Ω C hc p₁ ζ₁
  letI := coverAlgebra Ω C hc p₂ ζ₂
  haveI := isScalarTower_coverAlgebra Ω C hc p₁ ζ₁ hζ₁
  haveI := isScalarTower_coverAlgebra Ω C hc p₂ ζ₂ hζ₂
  haveI := isAlgebraic_coverAlgebra Ω C hc p₁ ζ₁ hζ₁
  haveI := isAlgebraic_coverAlgebra Ω C hc p₂ ζ₂ hζ₂
  obtain ⟨F, hF, HF⟩ := exists_iso_isConjInduced_of_covers (hDGC (coverField C hc p₁))
    (coverCurve C hc p₁) (coverCurve_cusp C hc p₁) (coverCurve C hc p₂) (coverCurve_cusp C hc p₂)
    p₁ p₂ ζ₁ ζ₂ hζ₁ hζ₂ (coverIso C hc p₁) (coverIso C hc p₂) (coverIso_spec C hc p₁)
    (coverIso_spec C hc p₂) _ _ hQ₁ hQ₂ ψ hψ
  exact ⟨V₁, V₂, p₁, p₂, F, hp₁, hp₂, isIntegral_cover C hc p₁, isIntegral_cover C hc p₂,
    isAffine_of_isAffineHom p₁, isAffine_of_isAffineHom p₂, hF, HF⟩

/-- **Lemma G, ring form**: `exists_coverIso_of_openSubgroup_iso` with `V_i = Spec B_i` for
domains `B_i`, `p_i = Spec r_i` for `r_i : Γ(X̄, U) ⟶ B_i` (finite étale), and `F = Spec E` for a
ring isomorphism `E : B₂ ≅ B₁` over `K`. For every ring endomorphism `ρ` of `Γ(X̄, U)` with
`ρ ≫ r₁ = r₂ ≫ E` and every `φ` induced by `Spec ρ`, `ψ = conj(δ) ∘ φ` on `Q₁`. -/
theorem exists_ringIso_of_openSubgroup_iso
    (hDGC : ∀ (k : Type u) [Field k] [NumberField k], RelIsomDGC.Exists k)
    (Q₁ Q₂ : OpenSubgroup π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U)))
    (ψ : (Q₁ : Subgroup π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U))) ≃ₜ*
      (Q₂ : Subgroup π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U))))
    (hψ : ∀ q, projGk Ω C hc (ψ q) = projGk Ω C hc q) :
    ∃ (B₁ B₂ : CommRingCat.{u}) (r₁ : Γ(C.Xbar, C.U) ⟶ B₁) (r₂ : Γ(C.Xbar, C.U) ⟶ B₂)
      (E : B₂ ≅ B₁), IsDomain B₁ ∧ IsDomain B₂ ∧ IsFiniteEtale (Spec.map r₁) ∧
        IsFiniteEtale (Spec.map r₂) ∧
        CommRingCat.ofHom (algebraMap K Γ(C.Xbar, C.U)) ≫ r₂ ≫ E.hom =
          CommRingCat.ofHom (algebraMap K Γ(C.Xbar, C.U)) ≫ r₁ ∧
        ∀ ρ : Γ(C.Xbar, C.U) ⟶ Γ(C.Xbar, C.U), ρ ≫ r₁ = r₂ ≫ E.hom →
          ∀ φ : π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U)) →
              π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U)),
            IsConjInduced (Spec.map ρ) φ → ∃ δ, ∀ q : Q₁,
              (ψ q : π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U))) =
                δ * φ q * δ⁻¹ := by
  obtain ⟨V₁, V₂, p₁, p₂, F, hp₁, hp₂, hI₁, hI₂, hA₁, hA₂, hF, HF⟩ :=
    exists_coverIso_of_openSubgroup_iso hDGC Q₁ Q₂ ψ hψ
  haveI := hp₁
  haveI := hp₂
  haveI := hI₁
  haveI := hI₂
  haveI := hA₁
  haveI := hA₂
  have hF' : F.hom ≫ p₂ ≫ Spec.map (CommRingCat.ofHom (algebraMap K Γ(C.Xbar, C.U))) =
      p₁ ≫ Spec.map (CommRingCat.ofHom (algebraMap K Γ(C.Xbar, C.U))) := hF
  haveI : IsFiniteEtale V₁.isoSpec.inv := MorphismProperty.of_isIso @IsFiniteEtale _
  haveI : IsFiniteEtale V₂.isoSpec.inv := MorphismProperty.of_isIso @IsFiniteEtale _
  have h₁ : Spec.map (Spec.preimage (V₁.isoSpec.inv ≫ p₁)) = V₁.isoSpec.inv ≫ p₁ :=
    Spec.map_preimage _
  have h₂ : Spec.map (Spec.preimage (V₂.isoSpec.inv ≫ p₂)) = V₂.isoSpec.inv ≫ p₂ :=
    Spec.map_preimage _
  have hG : Spec.map (Spec.preimage (V₁.isoSpec.inv ≫ F.hom ≫ V₂.isoSpec.hom)) =
      V₁.isoSpec.inv ≫ F.hom ≫ V₂.isoSpec.hom := Spec.map_preimage _
  have hG' : Spec.map (Spec.preimage (V₂.isoSpec.inv ≫ F.inv ≫ V₁.isoSpec.hom)) =
      V₂.isoSpec.inv ≫ F.inv ≫ V₁.isoSpec.hom := Spec.map_preimage _
  let E : Γ(V₂, ⊤) ≅ Γ(V₁, ⊤) :=
    { hom := Spec.preimage (V₁.isoSpec.inv ≫ F.hom ≫ V₂.isoSpec.hom)
      inv := Spec.preimage (V₂.isoSpec.inv ≫ F.inv ≫ V₁.isoSpec.hom)
      hom_inv_id := Spec.map_injective (by
        rw [Spec.map_comp, hG, hG', Spec.map_id]
        simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc,
          Iso.inv_hom_id])
      inv_hom_id := Spec.map_injective (by
        rw [Spec.map_comp, hG, hG', Spec.map_id]
        simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id]) }
  have hE : Spec.map E.hom = V₁.isoSpec.inv ≫ F.hom ≫ V₂.isoSpec.hom := hG
  refine ⟨Γ(V₁, ⊤), Γ(V₂, ⊤), Spec.preimage (V₁.isoSpec.inv ≫ p₁),
    Spec.preimage (V₂.isoSpec.inv ≫ p₂), E, inferInstance, inferInstance, ?_, ?_, ?_, ?_⟩
  · rw [h₁]
    infer_instance
  · rw [h₂]
    infer_instance
  · refine Spec.map_injective ?_
    rw [Spec.map_comp, Spec.map_comp, Spec.map_comp, h₁, h₂, hE]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [hF']
  · intro ρ hρ φ Hφ
    have e := congrArg Spec.map hρ
    rw [Spec.map_comp, Spec.map_comp, h₁, h₂, hE] at e
    simp only [Category.assoc, Iso.hom_inv_id_assoc] at e
    exact HF _ ((cancel_epi V₁.isoSpec.inv).1 e).symm φ Hφ

end Cover

end Iut.Reconstruction
