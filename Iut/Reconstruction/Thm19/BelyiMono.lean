/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Thm19.BelyiLift
import Iut.Reconstruction.Thm19.CycloIso
import CurvesJacobian.LocAn.SectionBridgeCusp

/-!
# Cor 3.8 lifts: monotonicity, composition of fillings, compatibility (MR9 item 3, L0–L3)

For an isomorphism `Φ : Π_U ≃ Π_{U'}` of the arithmetic fundamental groups of two affine
hyperbolic curves over number fields and the lifts of `Φ` to opens `V ⊆ U` given by [AbsTopII]
Cor 3.8 (`IsCor38Lift`, `BelyiLift.lean`):

* **`IsCor38Lift.le_of_le`**: lifts are monotone in the open (`V ⊆ V♮` ⇒ `V₂ ⊆ V₂♮`), via
  [GalSect] Thm 1.3 (i) (`samePt_of_arithDecomp_conj`) and curves-jacobian
  `LocAn.exists_isCuspPlace_comap_eq`;
* **`exists_cor38Fill_comp`** (L0): filling `V ⊆ V♮` and then `V♮ ⊆ U` is the filling of `V`
  up to an inner automorphism of `Π_U`;
* **`IsCor38Lift.exists_conj`** (L3): for lifts `φ` on `V` and `φ♮` on `V♮ ⊇ V`,
  `f₂ ∘ φ = conj m ∘ φ♮ ∘ f` for the fillings `f`, `f₂`; uses the uniqueness of
  [AbsTopII] Cor 3.7 (b) (`cor37b_lift_unique`), hence the named hypothesis `hDGC`
  (rel-isom-DGC, [LocAn] Thm A; MR7 debt, also carried by `belyiCuspSpec`).
-/

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale PreGaloisCategory
  Belyi Belyi.Anabelian CurvesJacobian.Cusp

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Iut.Reconstruction

section Mono

open Thm19 Pi1 Pi1.Orbifold KummerTheory KummerTheory.Curve AffOrbicurve CurvesJacobian
  CurvesJacobian.Kummer

variable {K : Type u} [Field K] [NumberField K] {Ω : Type u} [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] {C : HypCurve K}
  {hc : (C.U : Set C.Xbar)ᶜ.Nonempty}
  {K₂ : Type u} [Field K₂] [NumberField K₂] {Ω₂ : Type u} [Field Ω₂] [Algebra K₂ Ω₂]
  [IsAlgClosed Ω₂] [Algebra.IsAlgebraic K₂ Ω₂] [CharZero Ω₂] {C₂ : HypCurve K₂}
  [hc₂ : Fact (C₂.U : Set C₂.Xbar)ᶜ.Nonempty]

attribute [local instance] isIntegral_Xbar nonempty_U algFF isAlgClosure_of_isAlgebraic

variable {τ₂ : C₂.Xbar.functionField} (hτ₂ : Transcendental K₂ τ₂)
  [IsGalois (K₀ K₂ (coordT τ₂)) (FFClosure C₂.Xbar)] (hU₂ : C₂.U = chartOne K₂ C₂.Xbar τ₂)
  [CharZero (FFClosure C₂.Xbar)]

include hτ₂ hU₂ in
/-- **Cor 3.8 lifts are monotone in the open**: if `φ` lifts `Φ` on `V`, `φB` lifts `Φ` on
`VB ⊇ V`, with images `V₂`, `V₂B`, then `V₂ ⊆ V₂B`. A point `x ∈ V₂ ∖ V₂B` would carry a cusp
`W'` of `V₂B` centred on `U'`; through `φB⁻¹` it comes from a cusp `W` of `VB` centred on `U`,
hence a cusp of `V`, which `φ` sends to a cusp `W₂` of `V₂`; the decomposition groups of `W'`
and `W₂` are conjugate in `Π_{U'}`, so both lie over the same point
(`samePt_of_arithDecomp_conj`, [GalSect] Thm 1.3 (i)), and `W'` is centred on `V₂` while `W₂`
is not. -/
theorem IsCor38Lift.le_of_le (σ₀ : Spec (CommRingCat.of K₂) ⟶ C₂.Xbar)
    (hσ₀ : σ₀ ≫ (C₂.Xbar ↘ Spec (CommRingCat.of K₂)) = 𝟙 (Spec (CommRingCat.of K₂)))
    (hg : CurvesJacobian.curveGenus K₂ C₂.Xbar ≠ 0)
    (Φ : (arithmeticExt Ω C hc).Iso (arithmeticExt Ω₂ C₂ hc₂.out))
    {V VB : C.Xbar.Opens} {hV : V ≤ C.U} {hne : (V : Set C.Xbar).Nonempty}
    {hVB : VB ≤ C.U} {hneB : (VB : Set C.Xbar).Nonempty}
    {V₂ V₂B : C₂.Xbar.Opens} {hV₂ : V₂ ≤ C₂.U} {hne₂ : (V₂ : Set C₂.Xbar).Nonempty}
    {hV₂B : V₂B ≤ C₂.U} {hne₂B : (V₂B : Set C₂.Xbar).Nonempty}
    {φ : (arithmeticExt Ω (subCurve C V hV hne) (compl_nonempty_of_le hV hc)).Pi ≃ₜ*
      (arithmeticExt Ω₂ (subCurve C₂ V₂ hV₂ hne₂) (compl_nonempty_of_le hV₂ hc₂.out)).Pi}
    {φB : (arithmeticExt Ω (subCurve C VB hVB hneB) (compl_nonempty_of_le hVB hc)).Pi ≃ₜ*
      (arithmeticExt Ω₂ (subCurve C₂ V₂B hV₂B hne₂B) (compl_nonempty_of_le hV₂B hc₂.out)).Pi}
    (h : IsCor38Lift Φ.pi.toMulEquiv hV hne hV₂ hne₂ φ)
    (hB : IsCor38Lift Φ.pi.toMulEquiv hVB hneB hV₂B hne₂B φB) (hVV : V ≤ VB) : V₂ ≤ V₂B := by
  intro x hx
  by_contra hxB
  haveI : Nonempty V₂ := hne₂.to_subtype
  obtain ⟨W', hW', hW'x⟩ := LocAn.exists_isCuspPlace_comap_eq Ω₂ (subCurve C₂ V₂B hV₂B hne₂B)
    (compl_nonempty_of_le hV₂B hc₂.out) (x := x) hxB
  have hW'x' : W'.comap (ffEmb Ω₂ C₂ hc₂.out) = CurvesJacobian.stalkVS K₂ x := by
    rw [← hW'x]
    ext y
    simp only [ValuationSubring.mem_comap]
    exact Iff.of_eq (congrArg (fun z => z ∈ W')
      (ffEmb_subCurve Ω₂ C₂ hc₂.out V₂B hV₂B hne₂B y).symm)
  have hW'U : IsCentredOnU Ω₂ C₂ W' :=
    isCentredOnU_of_comap_eq Ω₂ C₂ hc₂.out C₂.U le_rfl C₂.nonempty (hV₂ hx) hW'.1 hW'x'
  have hW'V₂ : IsCentredOnU Ω₂ (subCurve C₂ V₂ hV₂ hne₂) W' :=
    isCentredOnU_of_comap_eq Ω₂ C₂ hc₂.out V₂ hV₂ hne₂ hx hW'.1 hW'x'
  have hpr' : ∀ y, (arithmeticExt Ω C hc).pr (Φ.pi.toMulEquiv.symm y) =
      Φ.g.symm ((arithmeticExt Ω₂ C₂ hc₂.out).pr y) := fun y => by
    rw [ContinuousMulEquiv.eq_symm_apply, ← Φ.pr_comm]
    congr 1
    exact Φ.pi.toMulEquiv.apply_symm_apply y
  obtain ⟨W, hW, -, hcW, hdW⟩ := hB.symm.exists_cusp Φ.g.symm hpr' hW'
  have hWU : IsCentredOnU Ω C W := hcW.1 hW'U
  have hWV : ¬ IsCentredOnU Ω (subCurve C V hV hne) W := fun h' =>
    IsCuspPlace.not_isCentredOnU (hc := hc) hW (isCentredOnU_mono hVV h')
  have hWc : IsCuspPlace Ω (subCurve C V hV hne) (compl_nonempty_of_le hV hc) W :=
    isCuspPlace_of_not_isCentredOnU (hc := hc) hV hne hW.1 hWV
  obtain ⟨W₂, hW₂, -, hcW₂, hdW₂⟩ := h.exists_cusp Φ.g Φ.pr_comm hWc
  obtain ⟨g₁, hg₁⟩ := hdW hW'U 1
  obtain ⟨g₂, hg₂⟩ := hdW₂ hWU g₁
  have hD : (arithDecomp Ω₂ C₂ hc₂.out W').map (MulAut.conj 1).toMonoidHom =
      (arithDecomp Ω₂ C₂ hc₂.out W₂).map (MulAut.conj g₂).toMonoidHom := by
    rw [← hg₂, ← hg₁]
    exact (CuspData.map_map_symm Φ.pi.toMulEquiv _).symm
  have hsame := samePt_of_arithDecomp_conj hτ₂ hU₂ σ₀ hσ₀ hg hW' hW₂ hW'U (hcW₂.1 hWU) hD
  exact IsCuspPlace.not_isCentredOnU (hc := hc₂.out) hW₂
    ((hsame.isCentredOnU_iff hW'.1 hW₂.1 V₂ hV₂ hne₂).1 hW'V₂)

end Mono

section FillComp

open Pi1

variable {K : Type u} [Field K] [NumberField K] (Ω : Type u) [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] (C : HypCurve K)
  (hc : (C.U : Set C.Xbar)ᶜ.Nonempty)

attribute [local instance] isAlgClosure_of_isAlgebraic

omit [NumberField K] [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] in
lemma specMap_resAlg_comp {U₁ U₂ U₃ : C.Xbar.Opens} (h₁ : U₁ ≤ U₂) (h₂ : U₂ ≤ U₃) :
    Spec.map (CommRingCat.ofHom (resAlg K h₁).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (resAlg K h₂).toRingHom) =
      Spec.map (CommRingCat.ofHom (resAlg K (h₁.trans h₂)).toRingHom) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext a
  change (Scheme.Hom.appLE (𝟙 C.Xbar) U₃ U₂ h₂ ≫ Scheme.Hom.appLE (𝟙 C.Xbar) U₂ U₁ h₁) a =
    Scheme.Hom.appLE (𝟙 C.Xbar) U₃ U₁ (h₁.trans h₂) a
  rw [Scheme.Hom.appLE_comp_appLE]
  rfl

lemma autContinuousMulEquivOfIso_symm_apply {C' : Type*} [Category C'] {F G : C' ⥤ FintypeCat.{u}}
    (e : F ≅ G) (σ : Aut G) :
    (autContinuousMulEquivOfIso e).symm σ = autContinuousMulEquivOfIso e.symm σ := by
  apply (autContinuousMulEquivOfIso e).injective
  rw [ContinuousMulEquiv.apply_symm_apply]
  change σ = e.conjAut (e.symm.conjAut σ)
  refine Iso.ext ?_
  simp

lemma autContinuousMulEquivOfIso_trans_apply {C' : Type*} [Category C']
    {F G H : C' ⥤ FintypeCat.{u}} (e : F ≅ G) (e' : G ≅ H) (σ : Aut F) :
    autContinuousMulEquivOfIso e' (autContinuousMulEquivOfIso e σ) =
      autContinuousMulEquivOfIso (e ≪≫ e') σ :=
  (Iso.trans_conjAut e e' σ).symm

/-- **Composition of fillings (L0)**: for `V ⊆ V♮ ⊆ U`, filling the cusps of `V` in `V♮` and
then those of `V♮` in `U` is the filling of `V` in `U`, up to an inner automorphism of `Π_U` (the
changes of base point differ by an automorphism of the fibre functor). The curve
`subCurve (subCurve C V♮) V` is `subCurve C V` definitionally. -/
theorem exists_cor38Fill_comp {V VB : C.Xbar.Opens} (hV : V ≤ C.U)
    (hne : (V : Set C.Xbar).Nonempty) (hVB : VB ≤ C.U) (hneB : (VB : Set C.Xbar).Nonempty)
    (hVV : V ≤ VB)
    (α₀ : fiber (basePoint Ω C hc) ≅
      fiber (fillPoint Ω (subCurve C V hV hne) (compl_nonempty_of_le hV hc) hV))
    (αB : fiber (basePoint Ω C hc) ≅
      fiber (fillPoint Ω (subCurve C VB hVB hneB) (compl_nonempty_of_le hVB hc) hVB))
    (α₁ : fiber (basePoint Ω (subCurve C VB hVB hneB) (compl_nonempty_of_le hVB hc)) ≅
      fiber (fillPoint Ω (subCurve (subCurve C VB hVB hneB) V hVV hne)
        (compl_nonempty_of_le hVV (compl_nonempty_of_le hVB hc)) hVV)) :
    ∃ c : (arithmeticExt Ω C hc).Pi, ∀ x,
      cor38Fill Ω C hc VB hVB hneB αB (cor38Fill Ω (subCurve C VB hVB hneB)
          (compl_nonempty_of_le hVB hc) V hVV hne α₁ x) =
        c * cor38Fill Ω C hc V hV hne α₀ x * c⁻¹ := by
  set f₁ := Spec.map (CommRingCat.ofHom (resAlg K hVV).toRingHom) with hf₁
  set f₂ := Spec.map (CommRingCat.ofHom (resAlg K hVB).toRingHom) with hf₂
  set f₃ := Spec.map (CommRingCat.ofHom (resAlg K hV).toRingHom) with hf₃
  have h₁ : (basePoint Ω (subCurve C V hV hne) (compl_nonempty_of_le hV hc) ≫
      baseChangeSpec K Ω Γ(C.Xbar, V)) ≫ f₁ =
      fillPoint Ω (subCurve (subCurve C VB hVB hneB) V hVV hne)
        (compl_nonempty_of_le hVV (compl_nonempty_of_le hVB hc)) hVV ≫
          baseChangeSpec K Ω Γ(C.Xbar, VB) :=
    fillPoint_spec Ω (subCurve (subCurve C VB hVB hneB) V hVV hne)
      (compl_nonempty_of_le hVV (compl_nonempty_of_le hVB hc)) hVV
  have h₂ : (basePoint Ω (subCurve C VB hVB hneB) (compl_nonempty_of_le hVB hc) ≫
      baseChangeSpec K Ω Γ(C.Xbar, VB)) ≫ f₂ =
      fillPoint Ω (subCurve C VB hVB hneB) (compl_nonempty_of_le hVB hc) hVB ≫
        baseChangeSpec K Ω Γ(C.Xbar, C.U) :=
    fillPoint_spec Ω (subCurve C VB hVB hneB) (compl_nonempty_of_le hVB hc) hVB
  have h₃ : (basePoint Ω (subCurve C V hV hne) (compl_nonempty_of_le hV hc) ≫
      baseChangeSpec K Ω Γ(C.Xbar, V)) ≫ f₃ =
      fillPoint Ω (subCurve C V hV hne) (compl_nonempty_of_le hV hc) hV ≫
        baseChangeSpec K Ω Γ(C.Xbar, C.U) :=
    fillPoint_spec Ω (subCurve C V hV hne) (compl_nonempty_of_le hV hc) hV
  have h₃' : (fillPoint Ω (subCurve (subCurve C VB hVB hneB) V hVV hne)
      (compl_nonempty_of_le hVV (compl_nonempty_of_le hVB hc)) hVV ≫
        baseChangeSpec K Ω Γ(C.Xbar, VB)) ≫ f₂ =
      fillPoint Ω (subCurve C V hV hne) (compl_nonempty_of_le hV hc) hV ≫
        baseChangeSpec K Ω Γ(C.Xbar, C.U) := by
    rw [← h₁, ← h₃]
    simp only [hf₁, hf₂, hf₃, Category.assoc, specMap_resAlg_comp]
  set a := fiberIsoMap (baseChangeSpec K Ω Γ(C.Xbar, VB)) rfl rfl α₁
  set a' := fiberIsoMap f₂ h₂ h₃' a
  set b := fiberIsoMap (baseChangeSpec K Ω Γ(C.Xbar, C.U)) rfl rfl αB
  set c₀ := fiberIsoMap (baseChangeSpec K Ω Γ(C.Xbar, C.U)) rfl rfl α₀
  refine ⟨c₀ ≪≫ a'.symm ≪≫ b.symm, fun x => ?_⟩
  have hcomp : fundamentalGroupMap f₂ h₃' (fundamentalGroupMap f₁ h₁ x) =
      fundamentalGroupMap f₃ h₃ x := by
    have hh : (basePoint Ω (subCurve C V hV hne) (compl_nonempty_of_le hV hc) ≫
        baseChangeSpec K Ω Γ(C.Xbar, V)) ≫ f₁ ≫ f₂ =
        fillPoint Ω (subCurve C V hV hne) (compl_nonempty_of_le hV hc) hV ≫
          baseChangeSpec K Ω Γ(C.Xbar, C.U) := by
      rw [← Category.assoc, h₁]; exact h₃'
    have e := fundamentalGroupMap_comp f₁ f₂ h₁ h₃' hh
    have e' := fundamentalGroupMap_congr (specMap_resAlg_comp C hVV hVB) hh h₃
    rw [e] at e'
    exact congrArg (fun φ => φ x) e'
  have hnat := fundamentalGroupMap_autContinuousMulEquivOfIso f₂ h₂ h₃' a
    ((autContinuousMulEquivOfIso a).symm (fundamentalGroupMap f₁ h₁ x))
  rw [ContinuousMulEquiv.apply_symm_apply, hcomp] at hnat
  have e3 : fundamentalGroupMap f₃ h₃ x =
      autContinuousMulEquivOfIso c₀ (cor38Fill Ω C hc V hV hne α₀ x) :=
    ((autContinuousMulEquivOfIso c₀).apply_symm_apply _).symm
  change (autContinuousMulEquivOfIso b).symm (fundamentalGroupMap f₂ h₂
    ((autContinuousMulEquivOfIso a).symm (fundamentalGroupMap f₁ h₁ x))) = _
  have e2 : fundamentalGroupMap f₂ h₂
      ((autContinuousMulEquivOfIso a).symm (fundamentalGroupMap f₁ h₁ x)) =
      (autContinuousMulEquivOfIso a').symm (fundamentalGroupMap f₃ h₃ x) := by
    rw [hnat, ContinuousMulEquiv.symm_apply_apply]
  rw [e2, e3, autContinuousMulEquivOfIso_symm_apply, autContinuousMulEquivOfIso_symm_apply,
    autContinuousMulEquivOfIso_trans_apply, autContinuousMulEquivOfIso_trans_apply,
    CurvesJacobian.Cusp.autContinuousMulEquivOfIso_self]

end FillComp

section Generic

variable {P P' Q Q' R : Type*} [Group P] [Group P'] [Group Q] [Group Q'] [Group R]
  [TopologicalSpace P] [TopologicalSpace P'] [TopologicalSpace Q] [TopologicalSpace Q']
  [CompactSpace P] [CompactSpace P'] [T2Space Q] [T2Space Q']

/-- The group theory of L3: if `φ : P ≃ₜ* P'` matches the kernels of `f : P ↠ Q`,
`f₂ : P' ↠ Q'`, and `φ♮ : Q ≃ₜ* Q'` is such that `F ∘ f₂ ∘ φ = conj d ∘ F ∘ φ♮ ∘ f`, and every
automorphism `θ` of `Q'` with `F ∘ θ = conj d ∘ F` is inner, then `f₂ ∘ φ = conj m ∘ φ♮ ∘ f`. -/
theorem exists_conj_of_fill (f : P →* Q) (f₂ : P' →* Q') (hf : Continuous f)
    (hf₂ : Continuous f₂) (hfs : Function.Surjective f) (hf₂s : Function.Surjective f₂)
    (φ : P ≃ₜ* P') (φB : Q ≃ₜ* Q') (hker : ∀ x, f₂ (φ x) = 1 ↔ f x = 1) (F : Q' →* R) (d : R)
    (hrel : ∀ x, F (f₂ (φ x)) = d * F (φB (f x)) * d⁻¹)
    (hinner : ∀ θ : Q' ≃ₜ* Q', (∀ σ, F (θ σ) = d * F σ * d⁻¹) → ∃ n, ∀ σ, θ σ = n * σ * n⁻¹) :
    ∃ m, ∀ x, f₂ (φ x) = m * φB (f x) * m⁻¹ := by
  let θ₀ := Thm19.descendCongr f f₂ hf hf₂ hfs hf₂s φ hker
  have hθ₀ : ∀ x, θ₀ (f x) = f₂ (φ x) := Thm19.descendCongr_apply f f₂ hf hf₂ hfs hf₂s φ hker
  let θ := φB.symm.trans θ₀
  have hθ : ∀ x, θ (φB (f x)) = f₂ (φ x) := fun x => by
    change θ₀ (φB.symm (φB (f x))) = _
    rw [ContinuousMulEquiv.symm_apply_apply, hθ₀]
  obtain ⟨n, hn⟩ := hinner θ fun σ => by
    obtain ⟨x, hx⟩ := hfs (φB.symm σ)
    have hσ : σ = φB (f x) := by rw [hx, ContinuousMulEquiv.apply_symm_apply]
    rw [hσ, hθ, hrel]
  exact ⟨n, fun x => by rw [← hθ, hn]⟩

end Generic

section Compat

open Thm19 Pi1 Pi1.Orbifold KummerTheory KummerTheory.Curve AffOrbicurve CurvesJacobian
  CurvesJacobian.Kummer

variable {K : Type u} [Field K] [NumberField K] {Ω : Type u} [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] {C : HypCurve K}
  [hc : Fact (C.U : Set C.Xbar)ᶜ.Nonempty]
  {K₂ : Type u} [Field K₂] [NumberField K₂] {Ω₂ : Type u} [Field Ω₂] [Algebra K₂ Ω₂]
  [IsAlgClosed Ω₂] [Algebra.IsAlgebraic K₂ Ω₂] [CharZero Ω₂] {C₂ : HypCurve K₂}
  [hc₂ : Fact (C₂.U : Set C₂.Xbar)ᶜ.Nonempty]

attribute [local instance] isIntegral_Xbar nonempty_U algFF isAlgClosure_of_isAlgebraic

variable {τ : C.Xbar.functionField} (hτ : Transcendental K τ)
  [IsGalois (K₀ K (coordT τ)) (FFClosure C.Xbar)] (hU : C.U = chartOne K C.Xbar τ)
  [CharZero (FFClosure C.Xbar)]

variable {Φ : (arithmeticExt Ω C hc.out).Pi ≃* (arithmeticExt Ω₂ C₂ hc₂.out).Pi}
  {ψ : (arithmeticExt Ω C hc.out).G ≃ₜ* (arithmeticExt Ω₂ C₂ hc₂.out).G}
  {V VB : C.Xbar.Opens} {hV : V ≤ C.U} {hne : (V : Set C.Xbar).Nonempty}
  {hVB : VB ≤ C.U} {hneB : (VB : Set C.Xbar).Nonempty}
  {V₂ V₂B : C₂.Xbar.Opens} {hV₂ : V₂ ≤ C₂.U} {hne₂ : (V₂ : Set C₂.Xbar).Nonempty}
  {hV₂B : V₂B ≤ C₂.U} {hne₂B : (V₂B : Set C₂.Xbar).Nonempty}
  {φ : (arithmeticExt Ω (subCurve C V hV hne) (compl_nonempty_of_le hV hc.out)).Pi ≃ₜ*
    (arithmeticExt Ω₂ (subCurve C₂ V₂ hV₂ hne₂) (compl_nonempty_of_le hV₂ hc₂.out)).Pi}
  {φB : (arithmeticExt Ω (subCurve C VB hVB hneB) (compl_nonempty_of_le hVB hc.out)).Pi ≃ₜ*
    (arithmeticExt Ω₂ (subCurve C₂ V₂B hV₂B hne₂B) (compl_nonempty_of_le hV₂B hc₂.out)).Pi}

omit [CharZero (FFClosure C.Xbar)] in
lemma pr_symm_of_pr
    (hpr : ∀ x, (arithmeticExt Ω₂ C₂ hc₂.out).pr (Φ x) = ψ ((arithmeticExt Ω C hc.out).pr x))
    (y) : (arithmeticExt Ω C hc.out).pr (Φ.symm y) =
      ψ.symm ((arithmeticExt Ω₂ C₂ hc₂.out).pr y) := by
  rw [ContinuousMulEquiv.eq_symm_apply, ← hpr, MulEquiv.apply_symm_apply]

include hτ hU in
/-- **Killed cusps go to killed cusps (L3 (i))**: for lifts `φ` on `V ⊆ V♮` and `φ♮` on `V♮`, a
cuspidal subgroup of `Π_V` killed by the filling `Π_V ↠ Π_{V♮}` is mapped by `φ` into the kernel
of `Π_{V₂} ↠ Π_{V₂♮}`. A cusp `W` of `V` centred on `V♮` goes to a cusp `W₂` of `V₂`; if `W₂`
were not centred on `V₂♮` it would be a cusp of `V₂♮`, which `φ♮⁻¹` sends to a cusp `W'` of
`V♮`, and `D_W`, `D_{W'}` would be conjugate in `Π_U`, so `W'` would be centred on `V♮` like `W`
([GalSect] Thm 1.3 (i), `samePt_of_arithDecomp_conj`). -/
theorem IsCor38Lift.map_le_ker (σ₀ : Spec (CommRingCat.of K) ⟶ C.Xbar)
    (hσ₀ : σ₀ ≫ (C.Xbar ↘ Spec (CommRingCat.of K)) = 𝟙 (Spec (CommRingCat.of K)))
    (hg : CurvesJacobian.curveGenus K C.Xbar ≠ 0)
    (hpr : ∀ x, (arithmeticExt Ω₂ C₂ hc₂.out).pr (Φ x) = ψ ((arithmeticExt Ω C hc.out).pr x))
    (h : IsCor38Lift Φ hV hne hV₂ hne₂ φ) (hB : IsCor38Lift Φ hVB hneB hV₂B hne₂B φB)
    (hVV : V ≤ VB) (hVV₂ : V₂ ≤ V₂B)
    (α₁ : fiber (basePoint Ω (subCurve C VB hVB hneB) (compl_nonempty_of_le hVB hc.out)) ≅
      fiber (fillPoint Ω (subCurve (subCurve C VB hVB hneB) V hVV hne)
        (compl_nonempty_of_le hVV (compl_nonempty_of_le hVB hc.out)) hVV))
    (α₂ : fiber (basePoint Ω₂ (subCurve C₂ V₂B hV₂B hne₂B) (compl_nonempty_of_le hV₂B hc₂.out)) ≅
      fiber (fillPoint Ω₂ (subCurve (subCurve C₂ V₂B hV₂B hne₂B) V₂ hVV₂ hne₂)
        (compl_nonempty_of_le hVV₂ (compl_nonempty_of_le hV₂B hc₂.out)) hVV₂))
    {J : Subgroup (arithmeticExt Ω (subCurve C V hV hne) (compl_nonempty_of_le hV hc.out)).Pi}
    (hJ : J ∈ arithCusps Ω (subCurve C V hV hne) (compl_nonempty_of_le hV hc.out))
    (hJk : J ≤ (cor38Fill Ω (subCurve C VB hVB hneB) (compl_nonempty_of_le hVB hc.out) V hVV hne
      α₁).ker) :
    J.map φ.toMulEquiv.toMonoidHom ≤ (cor38Fill Ω₂ (subCurve C₂ V₂B hV₂B hne₂B)
      (compl_nonempty_of_le hV₂B hc₂.out) V₂ hVV₂ hne₂ α₂).ker := by
  obtain ⟨W, hW, rfl⟩ := (mem_arithCusps_iff Ω _ _).1 hJ
  obtain ⟨W₂, hW₂, hI, hcent, hdec⟩ := h.exists_cusp ψ hpr hW
  rw [hI]
  replace hJk : IsCentredOnU Ω (subCurve C VB hVB hneB) W :=
    (arithInertia_le_ker_cor38Fill_iff Ω (subCurve C VB hVB hneB)
      (compl_nonempty_of_le hVB hc.out) V hVV hne α₁ hW).1 hJk
  refine (arithInertia_le_ker_cor38Fill_iff Ω₂ (subCurve C₂ V₂B hV₂B hne₂B)
    (compl_nonempty_of_le hV₂B hc₂.out) V₂ hVV₂ hne₂ α₂ hW₂).2 ?_
  by_contra hn
  have hW₂c : IsCuspPlace Ω₂ (subCurve C₂ V₂B hV₂B hne₂B) (compl_nonempty_of_le hV₂B hc₂.out)
      W₂ := isCuspPlace_of_not_isCentredOnU (hc := hc₂.out) hV₂B hne₂B hW₂.1 hn
  have hWU : IsCentredOnU Ω C W :=
    isCentredOnU_mono (V' := C.U) (hV' := le_rfl) (hne' := C.nonempty) hVB hJk
  have hW₂U : IsCentredOnU Ω₂ C₂ W₂ := hcent.1 hWU
  obtain ⟨W', hW', -, hcW', hdW'⟩ := hB.symm.exists_cusp ψ.symm (pr_symm_of_pr hpr) hW₂c
  obtain ⟨g₁, hg₁⟩ := hdec hWU 1
  obtain ⟨g₂, hg₂⟩ := hdW' hW₂U g₁
  have hD : (arithDecomp Ω C hc.out W).map (MulAut.conj 1).toMonoidHom =
      (arithDecomp Ω C hc.out W').map (MulAut.conj g₂).toMonoidHom := by
    rw [← hg₂, ← hg₁]
    exact (CuspData.map_map_symm Φ.symm _).symm
  have hsame := samePt_of_arithDecomp_conj hτ hU σ₀ hσ₀ hg hW hW' hWU (hcW'.1 hW₂U) hD
  haveI : Nonempty VB := hneB.to_subtype
  exact IsCuspPlace.not_isCentredOnU (hc := hc.out) hW'
    ((hsame.isCentredOnU_iff hW.1 hW'.1 VB hVB hneB).1 hJk)

include hτ hU in
/-- **L3 (ii)**: `φ` maps the kernel of `Π_V ↠ Π_{V♮}` into that of `Π_{V₂} ↠ Π_{V₂♮}` (the
kernel is the closed normal subgroup generated by the killed cusps,
`ker_fillMap_eq_closure_killedCusps₂`, and `map_le_ker`). -/
theorem IsCor38Lift.ker_le_comap (σ₀ : Spec (CommRingCat.of K) ⟶ C.Xbar)
    (hσ₀ : σ₀ ≫ (C.Xbar ↘ Spec (CommRingCat.of K)) = 𝟙 (Spec (CommRingCat.of K)))
    (hg : CurvesJacobian.curveGenus K C.Xbar ≠ 0)
    (hpr : ∀ x, (arithmeticExt Ω₂ C₂ hc₂.out).pr (Φ x) = ψ ((arithmeticExt Ω C hc.out).pr x))
    (h : IsCor38Lift Φ hV hne hV₂ hne₂ φ) (hB : IsCor38Lift Φ hVB hneB hV₂B hne₂B φB)
    (hVV : V ≤ VB) (hVV₂ : V₂ ≤ V₂B)
    (α₁ : fiber (basePoint Ω (subCurve C VB hVB hneB) (compl_nonempty_of_le hVB hc.out)) ≅
      fiber (fillPoint Ω (subCurve (subCurve C VB hVB hneB) V hVV hne)
        (compl_nonempty_of_le hVV (compl_nonempty_of_le hVB hc.out)) hVV))
    (α₂ : fiber (basePoint Ω₂ (subCurve C₂ V₂B hV₂B hne₂B) (compl_nonempty_of_le hV₂B hc₂.out)) ≅
      fiber (fillPoint Ω₂ (subCurve (subCurve C₂ V₂B hV₂B hne₂B) V₂ hVV₂ hne₂)
        (compl_nonempty_of_le hVV₂ (compl_nonempty_of_le hV₂B hc₂.out)) hVV₂)) :
    (cor38Fill Ω (subCurve C VB hVB hneB) (compl_nonempty_of_le hVB hc.out) V hVV hne α₁).ker ≤
      (cor38Fill Ω₂ (subCurve C₂ V₂B hV₂B hne₂B) (compl_nonempty_of_le hV₂B hc₂.out) V₂ hVV₂
        hne₂ α₂).ker.comap φ.toMulEquiv.toMonoidHom := by
  haveI : Nonempty (baseChangeOpen K Ω VB) :=
    inferInstanceAs (Nonempty (geomOpen Ω (subCurve C VB hVB hneB)))
  haveI : Nonempty (baseChangeOpen K Ω (X := (subCurve C V hV hne).Xbar) VB) :=
    inferInstanceAs (Nonempty (geomOpen Ω (subCurve C VB hVB hneB)))
  have h1 : IsClosed ((cor38Fill Ω₂ (subCurve C₂ V₂B hV₂B hne₂B)
      (compl_nonempty_of_le hV₂B hc₂.out) V₂ hVV₂ hne₂ α₂) ⁻¹'
        {(1 : (arithmeticExt Ω₂ (subCurve C₂ V₂B hV₂B hne₂B)
          (compl_nonempty_of_le hV₂B hc₂.out)).Pi)}) :=
    isClosed_singleton.preimage (continuous_cor38Fill₂ Ω₂ (subCurve C₂ V₂B hV₂B hne₂B)
      (compl_nonempty_of_le hV₂B hc₂.out) V₂ hVV₂ hne₂ α₂)
  have hcl : IsClosed ((cor38Fill Ω₂ (subCurve C₂ V₂B hV₂B hne₂B)
      (compl_nonempty_of_le hV₂B hc₂.out) V₂ hVV₂ hne₂ α₂).ker.comap
        φ.toMulEquiv.toMonoidHom : Set (arithmeticExt Ω (subCurve C V hV hne)
          (compl_nonempty_of_le hV hc.out)).Pi) :=
    h1.preimage φ.continuous
  haveI : Nonempty (baseChangeOpen K Ω
      (X := (subCurve (subCurve C VB hVB hneB) V hVV hne).Xbar) VB) :=
    inferInstanceAs (Nonempty (geomOpen Ω (subCurve C VB hVB hneB)))
  rw [ker_cor38Fill₂, ker_fillMap_eq_closure_killedCusps₂ Ω
    (subCurve (subCurve C VB hVB hneB) V hVV hne)
    (compl_nonempty_of_le hVV (compl_nonempty_of_le hVB hc.out)) hVV
    (compl_nonempty_of_le hVB hc.out)]
  refine Subgroup.topologicalClosure_minimal _ ?_ hcl
  refine Subgroup.normalClosure_le_normal ?_
  refine Set.iUnion₂_subset fun J hJ => ?_
  intro x hx
  have hJk : J ≤ (cor38Fill Ω (subCurve C VB hVB hneB) (compl_nonempty_of_le hVB hc.out) V hVV
      hne α₁).ker := by
    rw [ker_cor38Fill₂]
    exact hJ.2
  exact h.map_le_ker hτ hU σ₀ hσ₀ hg hpr hB hVV hVV₂ α₁ α₂ hJ.1 hJk ⟨x, hx, rfl⟩

include hτ hU in
/-- **L3 (ii′)**: `φ` matches the kernels of the fillings `Π_V ↠ Π_{V♮}`, `Π_{V₂} ↠ Π_{V₂♮}`
(`ker_le_comap` for `φ` and for `φ⁻¹`). -/
theorem IsCor38Lift.fill_ker_iff (σ₀ : Spec (CommRingCat.of K) ⟶ C.Xbar)
    (hσ₀ : σ₀ ≫ (C.Xbar ↘ Spec (CommRingCat.of K)) = 𝟙 (Spec (CommRingCat.of K)))
    (hg : CurvesJacobian.curveGenus K C.Xbar ≠ 0)
    {τ₂ : C₂.Xbar.functionField} (hτ₂ : Transcendental K₂ τ₂)
    [IsGalois (K₀ K₂ (coordT τ₂)) (FFClosure C₂.Xbar)] (hU₂ : C₂.U = chartOne K₂ C₂.Xbar τ₂)
    [CharZero (FFClosure C₂.Xbar)] (σ₂ : Spec (CommRingCat.of K₂) ⟶ C₂.Xbar)
    (hσ₂ : σ₂ ≫ (C₂.Xbar ↘ Spec (CommRingCat.of K₂)) = 𝟙 (Spec (CommRingCat.of K₂)))
    (hg₂ : CurvesJacobian.curveGenus K₂ C₂.Xbar ≠ 0)
    (hpr : ∀ x, (arithmeticExt Ω₂ C₂ hc₂.out).pr (Φ x) = ψ ((arithmeticExt Ω C hc.out).pr x))
    (h : IsCor38Lift Φ hV hne hV₂ hne₂ φ) (hB : IsCor38Lift Φ hVB hneB hV₂B hne₂B φB)
    (hVV : V ≤ VB) (hVV₂ : V₂ ≤ V₂B)
    (α₁ : fiber (basePoint Ω (subCurve C VB hVB hneB) (compl_nonempty_of_le hVB hc.out)) ≅
      fiber (fillPoint Ω (subCurve (subCurve C VB hVB hneB) V hVV hne)
        (compl_nonempty_of_le hVV (compl_nonempty_of_le hVB hc.out)) hVV))
    (α₂ : fiber (basePoint Ω₂ (subCurve C₂ V₂B hV₂B hne₂B) (compl_nonempty_of_le hV₂B hc₂.out)) ≅
      fiber (fillPoint Ω₂ (subCurve (subCurve C₂ V₂B hV₂B hne₂B) V₂ hVV₂ hne₂)
        (compl_nonempty_of_le hVV₂ (compl_nonempty_of_le hV₂B hc₂.out)) hVV₂)) (x) :
    cor38Fill Ω₂ (subCurve C₂ V₂B hV₂B hne₂B) (compl_nonempty_of_le hV₂B hc₂.out) V₂
        hVV₂ hne₂ α₂ (φ x) = 1 ↔
      cor38Fill Ω (subCurve C VB hVB hneB) (compl_nonempty_of_le hVB hc.out) V hVV hne α₁ x =
        1 := by
  have k₁ := h.ker_le_comap hτ hU σ₀ hσ₀ hg hpr hB hVV hVV₂ α₁ α₂
  have k₂ := h.symm.ker_le_comap hτ₂ hU₂ σ₂ hσ₂ hg₂ (pr_symm_of_pr hpr) hB.symm hVV₂ hVV α₂ α₁
  constructor
  · intro hx
    have := k₂ (MonoidHom.mem_ker.2 hx)
    rw [Subgroup.mem_comap, MonoidHom.mem_ker] at this
    change cor38Fill Ω (subCurve C VB hVB hneB) (compl_nonempty_of_le hVB hc.out) V hVV hne α₁
      (φ.symm (φ x)) = 1 at this
    rwa [ContinuousMulEquiv.symm_apply_apply] at this
  · intro hx
    exact k₁ (MonoidHom.mem_ker.2 hx)

omit [CharZero (FFClosure C.Xbar)] in
/-- **L3 (iv)**: the lift equations and the composition of fillings give
`F₂♮ ∘ f₂ ∘ φ = conj d ∘ F₂♮ ∘ φ♮ ∘ f` for the filling `F₂♮ : Π_{V₂♮} ↠ Π_{U'}` of the
lift `φ♮`. -/
theorem IsCor38Lift.exists_fill_rel
    (h : IsCor38Lift Φ hV hne hV₂ hne₂ φ) (hB : IsCor38Lift Φ hVB hneB hV₂B hne₂B φB)
    (hVV : V ≤ VB) (hVV₂ : V₂ ≤ V₂B)
    (α₁ : fiber (basePoint Ω (subCurve C VB hVB hneB) (compl_nonempty_of_le hVB hc.out)) ≅
      fiber (fillPoint Ω (subCurve (subCurve C VB hVB hneB) V hVV hne)
        (compl_nonempty_of_le hVV (compl_nonempty_of_le hVB hc.out)) hVV))
    (α₂ : fiber (basePoint Ω₂ (subCurve C₂ V₂B hV₂B hne₂B) (compl_nonempty_of_le hV₂B hc₂.out)) ≅
      fiber (fillPoint Ω₂ (subCurve (subCurve C₂ V₂B hV₂B hne₂B) V₂ hVV₂ hne₂)
        (compl_nonempty_of_le hVV₂ (compl_nonempty_of_le hV₂B hc₂.out)) hVV₂)) :
    ∃ (αB₂ : fiber (basePoint Ω₂ C₂ hc₂.out) ≅ fiber (fillPoint Ω₂ (subCurve C₂ V₂B hV₂B hne₂B)
        (compl_nonempty_of_le hV₂B hc₂.out) hV₂B)) (d : (arithmeticExt Ω₂ C₂ hc₂.out).Pi),
      ∀ x, cor38Fill Ω₂ C₂ hc₂.out V₂B hV₂B hne₂B αB₂ (cor38Fill Ω₂ (subCurve C₂ V₂B hV₂B hne₂B)
          (compl_nonempty_of_le hV₂B hc₂.out) V₂ hVV₂ hne₂ α₂ (φ x)) =
        d * cor38Fill Ω₂ C₂ hc₂.out V₂B hV₂B hne₂B αB₂ (φB (cor38Fill Ω (subCurve C VB hVB hneB)
          (compl_nonempty_of_le hVB hc.out) V hVV hne α₁ x)) * d⁻¹ := by
  obtain ⟨α₀, α₀₂, hφ⟩ := h
  obtain ⟨αB, αB₂, hφB⟩ := hB
  obtain ⟨c, hcc⟩ := exists_cor38Fill_comp Ω C hc.out hV hne hVB hneB hVV α₀ αB α₁
  obtain ⟨c₂, hcc₂⟩ := exists_cor38Fill_comp Ω₂ C₂ hc₂.out hV₂ hne₂ hV₂B hne₂B hVV₂ α₀₂ αB₂ α₂
  refine ⟨αB₂, c₂ * (Φ c)⁻¹, fun x => ?_⟩
  have hFx : cor38Fill Ω C hc.out V hV hne α₀ x =
      c⁻¹ * cor38Fill Ω C hc.out VB hVB hneB αB (cor38Fill Ω (subCurve C VB hVB hneB)
        (compl_nonempty_of_le hVB hc.out) V hVV hne α₁ x) * c := by
    rw [hcc x]; group
  rw [hcc₂, hφ, hFx, hφB, map_mul, map_mul, map_inv]
  group

include hτ hU in
/-- **Compatibility of lifts with the fillings (L3)**: for Cor 3.8 lifts `φ` of `Φ` on `V` and
`φ♮` on `V♮ ⊇ V` (images `V₂ ⊆ V₂♮`, `IsCor38Lift.le_of_le`) and any fillings
`f : Π_V ↠ Π_{V♮}`, `f₂ : Π_{V₂} ↠ Π_{V₂♮}`, there is `m ∈ Π_{V₂♮}` with
`f₂ ∘ φ = conj m ∘ φ♮ ∘ f`. Proof: `φ` matches the kernels (`ker_le_comap` both ways), so
`f₂ ∘ φ = θ ∘ φ♮ ∘ f` for a continuous automorphism `θ` of `Π_{V₂♮}` (`descendCongr`); by the
composition of fillings (`exists_cor38Fill_comp`) and the lift equations, `θ` lifts an inner
automorphism of `Π_{U'}`, hence is inner ([AbsTopII] Cor 3.7 (b), uniqueness,
`cor37b_lift_unique`; rel-isom-DGC `hDGC`). -/
theorem IsCor38Lift.exists_conj (σ₀ : Spec (CommRingCat.of K) ⟶ C.Xbar)
    (hσ₀ : σ₀ ≫ (C.Xbar ↘ Spec (CommRingCat.of K)) = 𝟙 (Spec (CommRingCat.of K)))
    (hg : CurvesJacobian.curveGenus K C.Xbar ≠ 0)
    {τ₂ : C₂.Xbar.functionField} (hτ₂ : Transcendental K₂ τ₂)
    [IsGalois (K₀ K₂ (coordT τ₂)) (FFClosure C₂.Xbar)] (hU₂ : C₂.U = chartOne K₂ C₂.Xbar τ₂)
    [CharZero (FFClosure C₂.Xbar)] (σ₂ : Spec (CommRingCat.of K₂) ⟶ C₂.Xbar)
    (hσ₂ : σ₂ ≫ (C₂.Xbar ↘ Spec (CommRingCat.of K₂)) = 𝟙 (Spec (CommRingCat.of K₂)))
    (hg₂ : CurvesJacobian.curveGenus K₂ C₂.Xbar ≠ 0) (hDGC : RelIsomDGC.Exists K₂)
    (hpr : ∀ x, (arithmeticExt Ω₂ C₂ hc₂.out).pr (Φ x) = ψ ((arithmeticExt Ω C hc.out).pr x))
    (h : IsCor38Lift Φ hV hne hV₂ hne₂ φ) (hB : IsCor38Lift Φ hVB hneB hV₂B hne₂B φB)
    (hVV : V ≤ VB) (hVV₂ : V₂ ≤ V₂B)
    (α₁ : fiber (basePoint Ω (subCurve C VB hVB hneB) (compl_nonempty_of_le hVB hc.out)) ≅
      fiber (fillPoint Ω (subCurve (subCurve C VB hVB hneB) V hVV hne)
        (compl_nonempty_of_le hVV (compl_nonempty_of_le hVB hc.out)) hVV))
    (α₂ : fiber (basePoint Ω₂ (subCurve C₂ V₂B hV₂B hne₂B) (compl_nonempty_of_le hV₂B hc₂.out)) ≅
      fiber (fillPoint Ω₂ (subCurve (subCurve C₂ V₂B hV₂B hne₂B) V₂ hVV₂ hne₂)
        (compl_nonempty_of_le hVV₂ (compl_nonempty_of_le hV₂B hc₂.out)) hVV₂)) :
    ∃ m, ∀ x, cor38Fill Ω₂ (subCurve C₂ V₂B hV₂B hne₂B) (compl_nonempty_of_le hV₂B hc₂.out) V₂
        hVV₂ hne₂ α₂ (φ x) =
      m * φB (cor38Fill Ω (subCurve C VB hVB hneB) (compl_nonempty_of_le hVB hc.out) V hVV hne
        α₁ x) * m⁻¹ := by
  obtain ⟨αB₂, d, hrel⟩ := h.exists_fill_rel hB hVV hVV₂ α₁ α₂
  refine exists_conj_of_fill
    (cor38Fill Ω (subCurve C VB hVB hneB) (compl_nonempty_of_le hVB hc.out) V hVV hne α₁)
    (cor38Fill Ω₂ (subCurve C₂ V₂B hV₂B hne₂B) (compl_nonempty_of_le hV₂B hc₂.out) V₂ hVV₂ hne₂
      α₂)
    (continuous_cor38Fill₂ Ω (subCurve C VB hVB hneB) (compl_nonempty_of_le hVB hc.out) V hVV
      hne α₁)
    (continuous_cor38Fill₂ Ω₂ (subCurve C₂ V₂B hV₂B hne₂B) (compl_nonempty_of_le hV₂B hc₂.out) V₂
      hVV₂ hne₂ α₂)
    (cor38Fill_surjective₂ Ω (subCurve C VB hVB hneB) (compl_nonempty_of_le hVB hc.out) V hVV
      hne α₁)
    (cor38Fill_surjective₂ Ω₂ (subCurve C₂ V₂B hV₂B hne₂B) (compl_nonempty_of_le hV₂B hc₂.out)
      V₂ hVV₂ hne₂ α₂) φ φB
    (h.fill_ker_iff hτ hU σ₀ hσ₀ hg hτ₂ hU₂ σ₂ hσ₂ hg₂ hpr hB hVV hVV₂ α₁ α₂)
    (cor38Fill Ω₂ C₂ hc₂.out V₂B hV₂B hne₂B αB₂) d hrel fun θ hθ => ?_
  obtain ⟨n, -, hn⟩ := cor37b_lift_unique Ω₂ C₂ hc₂.out V₂B hV₂B hne₂B αB₂ hDGC
    (ContinuousMulEquiv.refl _) θ d hθ
  exact ⟨n, hn⟩

end Compat

end Iut.Reconstruction
