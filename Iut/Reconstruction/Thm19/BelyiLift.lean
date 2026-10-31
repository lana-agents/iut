/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Thm19.ClosedPointDecomp

/-!
# [AbsTopII] Cor 3.8 lifts and their action on cusps

For an isomorphism `Φ : Π_U ≃ Π_{U'}` of the arithmetic fundamental groups of two affine
hyperbolic curves over number fields, [AbsTopII] Cor 3.8 (`BelyiCuspSpec` (d),
`Topics in Absolute Anabelian Geometry II.txt` l.4794–4842) lifts `Φ` to `Π_{U_X} ≃ Π_{U'_{X₂}}`
for every nonempty open `U_X ⊆ U` and some nonempty open `U'_{X₂} ⊆ U'`. These lifts are the
stagewise isomorphisms of item 3 of `Plans/MR9Plan.md` (the colimit of [AbsTopIII] Thm 1.9 (d),
`Topics in Absolute Anabelian Geometry III.txt` l.2158–2178). Here:

* `IsCor38Lift Φ φ`: `φ : Π_V ≃ₜ* Π_{V₂}` lies over `Φ` through `cor38Fill` (for some changes
  of base point); `exists_isCor38Lift` (from `BelyiCuspSpec` (d)), `IsCor38Lift.symm`;
* `IsCor38Lift.exists_pr`: a lift lies over `G_K ≃ G_{K'}` up to conjugation, so it is an
  isomorphism of cuspidal extensions (`IsCor38Lift.iso`, [AbsTopI] Lemma 4.5 (v));
* `arithInertia_le_ker_cor38Fill_iff`: a cusp of `V` is killed in `Π_U` iff its place is centred
  on `U_Ω`;
* **`IsCor38Lift.exists_cusp`**: `φ` maps the inertia group `I_W` of each cusp of `V` onto the
  inertia group `I_{W₂}` of a cusp of `V₂`, `W` is centred on `U_Ω` iff `W₂` is centred on
  `U'_Ω`, and then `Φ` maps the decomposition groups `D_W ⊆ Π_U` to conjugates of `D_{W₂}`
  (the argument of `map_mem_ptDecomps`);
* `ffEmb_subCurve`, `isCentredOnU_subCurve_iff`: `ι : K(X̄) → K(X̄_Ω)^alg` does not depend on the
  open, and centredness on `V_Ω` is `ι(Γ(V)) ⊆ W`; `SamePt` (same restriction to `ι(K(X̄))`, i.e.
  over the same point of `X̄`) and `SamePt.isCentredOnU_iff`; `isCentredOnU_of_comap_eq`;
* `IsCuspPlace.not_isCentredOnU`, `isCuspPlace_of_not_isCentredOnU`, `isCentredOnU_mono`;
* **`samePt_of_arithDecomp_conj`**: places of `ptDecomps` with conjugate decomposition groups
  lie over the same point ([GalSect] Thm 1.3 (i), `mem_iff_of_ptPlace_arithDecomp_le_conj`).
-/

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale PreGaloisCategory
  Belyi Belyi.Anabelian CurvesJacobian.Cusp

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Iut.Reconstruction

section Lift

variable {K : Type u} [Field K] [NumberField K] {Ω : Type u} [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] {C : HypCurve K}
  {hc : (C.U : Set C.Xbar)ᶜ.Nonempty}
  {K₂ : Type u} [Field K₂] [NumberField K₂] {Ω₂ : Type u} [Field Ω₂] [Algebra K₂ Ω₂]
  [IsAlgClosed Ω₂] [Algebra.IsAlgebraic K₂ Ω₂] [CharZero Ω₂] {C₂ : HypCurve K₂}
  {hc₂ : (C₂.U : Set C₂.Xbar)ᶜ.Nonempty}

attribute [local instance] isAlgClosure_of_isAlgebraic

/-- **`φ : Π_V ≃ₜ* Π_{V₂}` is a Cor 3.8 lift of `Φ : Π_U ≃* Π_{U'}`**: for some changes of base
point `α₀`, `α₂`, `cor38Fill ∘ φ = Φ ∘ cor38Fill` ([AbsTopII] Cor 3.8). -/
def IsCor38Lift (Φ : (arithmeticExt Ω C hc).Pi ≃* (arithmeticExt Ω₂ C₂ hc₂).Pi)
    {V : C.Xbar.Opens} (hV : V ≤ C.U) (hne : (V : Set C.Xbar).Nonempty)
    {V₂ : C₂.Xbar.Opens} (hV₂ : V₂ ≤ C₂.U) (hne₂ : (V₂ : Set C₂.Xbar).Nonempty)
    (φ : (arithmeticExt Ω (subCurve C V hV hne) (compl_nonempty_of_le hV hc)).Pi ≃ₜ*
      (arithmeticExt Ω₂ (subCurve C₂ V₂ hV₂ hne₂) (compl_nonempty_of_le hV₂ hc₂)).Pi) : Prop :=
  ∃ (α₀ : fiber (basePoint Ω C hc) ≅
      fiber (fillPoint Ω (subCurve C V hV hne) (compl_nonempty_of_le hV hc) hV))
    (α₂ : fiber (basePoint Ω₂ C₂ hc₂) ≅
      fiber (fillPoint Ω₂ (subCurve C₂ V₂ hV₂ hne₂) (compl_nonempty_of_le hV₂ hc₂) hV₂)),
    ∀ e, cor38Fill Ω₂ C₂ hc₂ V₂ hV₂ hne₂ α₂ (φ e) = Φ (cor38Fill Ω C hc V hV hne α₀ e)

variable {Φ : (arithmeticExt Ω C hc).Pi ≃* (arithmeticExt Ω₂ C₂ hc₂).Pi}
  {V : C.Xbar.Opens} {hV : V ≤ C.U} {hne : (V : Set C.Xbar).Nonempty}
  {V₂ : C₂.Xbar.Opens} {hV₂ : V₂ ≤ C₂.U} {hne₂ : (V₂ : Set C₂.Xbar).Nonempty}
  {φ : (arithmeticExt Ω (subCurve C V hV hne) (compl_nonempty_of_le hV hc)).Pi ≃ₜ*
      (arithmeticExt Ω₂ (subCurve C₂ V₂ hV₂ hne₂) (compl_nonempty_of_le hV₂ hc₂)).Pi}

/-- **Existence of Cor 3.8 lifts** (`BelyiCuspSpec` (d)). -/
theorem exists_isCor38Lift (hS : BelyiCuspSpec Ω C hc)
    (Φ : (arithmeticExt Ω C hc).Iso (arithmeticExt Ω₂ C₂ hc₂))
    (V : C.Xbar.Opens) (hV : V ≤ C.U) (hne : (V : Set C.Xbar).Nonempty) :
    ∃ (V₂ : C₂.Xbar.Opens) (hV₂ : V₂ ≤ C₂.U) (hne₂ : (V₂ : Set C₂.Xbar).Nonempty)
      (φ : (arithmeticExt Ω (subCurve C V hV hne) (compl_nonempty_of_le hV hc)).Pi ≃ₜ*
        (arithmeticExt Ω₂ (subCurve C₂ V₂ hV₂ hne₂) (compl_nonempty_of_le hV₂ hc₂)).Pi),
      IsCor38Lift Φ.pi.toMulEquiv hV hne hV₂ hne₂ φ := by
  obtain ⟨α₀⟩ : Nonempty (fiber (basePoint Ω C hc) ≅
      fiber (fillPoint Ω (subCurve C V hV hne) (compl_nonempty_of_le hV hc) hV)) := by
    haveI := isIntegral_specTensor Ω C hc
    exact nonempty_iso_of_fiberFunctor _ _
  obtain ⟨V₂, hV₂, hne₂, hlift⟩ := hS.2.2.2.1 Ω₂ C₂ hc₂ Φ V hV hne α₀
  obtain ⟨α₂⟩ : Nonempty (fiber (basePoint Ω₂ C₂ hc₂) ≅
      fiber (fillPoint Ω₂ (subCurve C₂ V₂ hV₂ hne₂) (compl_nonempty_of_le hV₂ hc₂) hV₂)) := by
    haveI := isIntegral_specTensor Ω₂ C₂ hc₂
    exact nonempty_iso_of_fiberFunctor _ _
  obtain ⟨φ, hφ⟩ := hlift α₂
  exact ⟨V₂, hV₂, hne₂, φ, α₀, α₂, hφ⟩

/-- **The inverse of a lift of `Φ` is a lift of `Φ⁻¹`.** -/
theorem IsCor38Lift.symm (h : IsCor38Lift Φ hV hne hV₂ hne₂ φ) :
    IsCor38Lift Φ.symm hV₂ hne₂ hV hne φ.symm := by
  obtain ⟨α₀, α₂, hφ⟩ := h
  refine ⟨α₂, α₀, fun e => ?_⟩
  rw [MulEquiv.eq_symm_apply, ← hφ, ContinuousMulEquiv.apply_symm_apply]

/-- **A lift lies over `G_K ≃ G_{K'}` up to conjugation** (`exists_pr_cor38Fill₃`). -/
theorem IsCor38Lift.exists_pr (h : IsCor38Lift Φ hV hne hV₂ hne₂ φ)
    (ψ : (arithmeticExt Ω C hc).G ≃ₜ* (arithmeticExt Ω₂ C₂ hc₂).G)
    (hpr : ∀ x, (arithmeticExt Ω₂ C₂ hc₂).pr (Φ x) = ψ ((arithmeticExt Ω C hc).pr x)) :
    ∃ ψU : (arithmeticExt Ω (subCurve C V hV hne) (compl_nonempty_of_le hV hc)).G ≃ₜ*
        (arithmeticExt Ω₂ (subCurve C₂ V₂ hV₂ hne₂) (compl_nonempty_of_le hV₂ hc₂)).G,
      ∀ e, (arithmeticExt Ω₂ (subCurve C₂ V₂ hV₂ hne₂) (compl_nonempty_of_le hV₂ hc₂)).pr
        (φ e) = ψU ((arithmeticExt Ω (subCurve C V hV hne) (compl_nonempty_of_le hV hc)).pr e) := by
  obtain ⟨α₀, α₂, hφ⟩ := h
  obtain ⟨t, ht⟩ := exists_pr_cor38Fill₃ Ω C hc V hV hne α₀
  obtain ⟨t₂, ht₂⟩ := exists_pr_cor38Fill₃ Ω₂ C₂ hc₂ V₂ hV₂ hne₂ α₂
  let g' : π₁ᵉᵗ(Spec.map (CommRingCat.ofHom (algebraMap K Ω))) ≃ₜ*
      π₁ᵉᵗ(Spec.map (CommRingCat.ofHom (algebraMap K₂ Ω₂))) := ψ
  refine ⟨((conjCME t).trans g').trans (conjCME t₂⁻¹), fun e => ?_⟩
  have a1 := ht₂ (φ e)
  have a2 := ht e
  have a3 : projGk Ω₂ C₂ hc₂ (Φ (cor38Fill Ω C hc V hV hne α₀ e)) =
      g' (projGk Ω C hc (cor38Fill Ω C hc V hV hne α₀ e)) := hpr _
  rw [hφ e, a3, a2] at a1
  change projGk Ω₂ (subCurve C₂ V₂ hV₂ hne₂) (compl_nonempty_of_le hV₂ hc₂) (φ e) =
    t₂⁻¹ * g' (t * projGk Ω (subCurve C V hV hne) (compl_nonempty_of_le hV hc) e * t⁻¹) *
      t₂⁻¹⁻¹
  rw [a1]
  group

/-- **A lift is an isomorphism of cuspidal extensions** ([AbsTopI] Lemma 4.5 (v),
`arithmeticExtIso'`). -/
def IsCor38Lift.iso (h : IsCor38Lift Φ hV hne hV₂ hne₂ φ)
    (ψ : (arithmeticExt Ω C hc).G ≃ₜ* (arithmeticExt Ω₂ C₂ hc₂).G)
    (hpr : ∀ x, (arithmeticExt Ω₂ C₂ hc₂).pr (Φ x) = ψ ((arithmeticExt Ω C hc).pr x)) :
    (arithmeticExt Ω (subCurve C V hV hne) (compl_nonempty_of_le hV hc)).Iso
      (arithmeticExt Ω₂ (subCurve C₂ V₂ hV₂ hne₂) (compl_nonempty_of_le hV₂ hc₂)) :=
  CurvesJacobian.CuspChar.arithmeticExtIso' φ (h.exists_pr ψ hpr).choose
    (h.exists_pr ψ hpr).choose_spec

@[simp] lemma IsCor38Lift.iso_pi (h : IsCor38Lift Φ hV hne hV₂ hne₂ φ)
    (ψ : (arithmeticExt Ω C hc).G ≃ₜ* (arithmeticExt Ω₂ C₂ hc₂).G)
    (hpr : ∀ x, (arithmeticExt Ω₂ C₂ hc₂).pr (Φ x) = ψ ((arithmeticExt Ω C hc).pr x)) (e) :
    (h.iso ψ hpr).pi e = φ e := rfl

end Lift

section Killed

variable {K : Type u} [Field K] [NumberField K] (Ω : Type u) [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] (C : HypCurve K)
  (hc : (C.U : Set C.Xbar)ᶜ.Nonempty)

attribute [local instance] isAlgClosure_of_isAlgebraic

/-- **A cusp of `V ⊆ U` is killed in `Π_U` iff its place is centred on `U_Ω`.** -/
theorem arithInertia_le_ker_cor38Fill_iff (V : C.Xbar.Opens) (hV : V ≤ C.U)
    (hne : (V : Set C.Xbar).Nonempty)
    (α₀ : fiber (basePoint Ω C hc) ≅
      fiber (fillPoint Ω (subCurve C V hV hne) (compl_nonempty_of_le hV hc) hV))
    {W : ValuationSubring (FFClosure (geomCurve Ω C))}
    (hW : IsCuspPlace Ω (subCurve C V hV hne) (compl_nonempty_of_le hV hc) W) :
    arithInertia Ω (subCurve C V hV hne) (compl_nonempty_of_le hV hc) W ≤
        (cor38Fill Ω C hc V hV hne α₀).ker ↔ IsCentredOnU Ω C W := by
  haveI : Nonempty (baseChangeOpen K Ω C.U) := inferInstanceAs (Nonempty (geomOpen Ω C))
  rw [ker_cor38Fill₂]
  constructor
  · intro hker
    by_contra hnc
    have hhyp := isHyperbolic_baseChange Ω (fillCurve (subCurve C V hV hne) hV C.hyperbolic)
    have e : (geomCuspInertia Ω (subCurve C V hV hne) W).map
        (geomToPi Ω (subCurve C V hV hne) (compl_nonempty_of_le hV hc)) =
        arithInertia Ω (subCurve C V hV hne) (compl_nonempty_of_le hV hc) W :=
      map_geomCuspInertia Ω _ _ hW.1
    have hle' : (geomCuspInertia Ω (subCurve C V hV hne) W).map
        (geomToPi Ω (subCurve C V hV hne) (compl_nonempty_of_le hV hc)) ≤
        (fillMap Ω (subCurve C V hV hne) (compl_nonempty_of_le hV hc) hV).toMonoidHom.ker := by
      rw [e]
      exact hker
    exact false_of_le_ker Ω (subCurve C V hV hne) (compl_nonempty_of_le hV hc) hV
      hc hhyp hW.1 hnc 1 (by rw [Subgroup.relIndex_self]; exact one_ne_zero)
      (map_conj_le_of_le_normal 1 hle')
  · intro hWU
    exact arithInertia_le_ker_fillMap_of_isCentredOn₂ Ω (subCurve C V hV hne)
      (compl_nonempty_of_le hV hc) hV hc hW hWU

end Killed

section Transfer

variable {K : Type u} [Field K] [NumberField K] {Ω : Type u} [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] {C : HypCurve K}
  {hc : (C.U : Set C.Xbar)ᶜ.Nonempty}
  {K₂ : Type u} [Field K₂] [NumberField K₂] {Ω₂ : Type u} [Field Ω₂] [Algebra K₂ Ω₂]
  [IsAlgClosed Ω₂] [Algebra.IsAlgebraic K₂ Ω₂] [CharZero Ω₂] {C₂ : HypCurve K₂}
  {hc₂ : (C₂.U : Set C₂.Xbar)ᶜ.Nonempty}
  {Φ : (arithmeticExt Ω C hc).Pi ≃* (arithmeticExt Ω₂ C₂ hc₂).Pi}
  {V : C.Xbar.Opens} {hV : V ≤ C.U} {hne : (V : Set C.Xbar).Nonempty}
  {V₂ : C₂.Xbar.Opens} {hV₂ : V₂ ≤ C₂.U} {hne₂ : (V₂ : Set C₂.Xbar).Nonempty}
  {φ : (arithmeticExt Ω (subCurve C V hV hne) (compl_nonempty_of_le hV hc)).Pi ≃ₜ*
      (arithmeticExt Ω₂ (subCurve C₂ V₂ hV₂ hne₂) (compl_nonempty_of_le hV₂ hc₂)).Pi}

attribute [local instance] isAlgClosure_of_isAlgebraic

/-- **Cusps under a Cor 3.8 lift**: `φ` maps the inertia group `I_W` of a cusp `W` of `V` onto
the inertia group `I_{W₂}` of a cusp `W₂` of `V₂`; `W` is centred on `U_Ω` iff `W₂` is centred on
`U'_Ω` (killed cusps go to killed cusps); and then `Φ` maps every conjugate of `D_W ⊆ Π_U` to a
conjugate of `D_{W₂} ⊆ Π_{U'}` ([AbsTopII] Cor 3.7 (c) on both sides). -/
theorem IsCor38Lift.exists_cusp (h : IsCor38Lift Φ hV hne hV₂ hne₂ φ)
    (ψ : (arithmeticExt Ω C hc).G ≃ₜ* (arithmeticExt Ω₂ C₂ hc₂).G)
    (hpr : ∀ x, (arithmeticExt Ω₂ C₂ hc₂).pr (Φ x) = ψ ((arithmeticExt Ω C hc).pr x))
    {W : ValuationSubring (FFClosure (geomCurve Ω C))}
    (hW : IsCuspPlace Ω (subCurve C V hV hne) (compl_nonempty_of_le hV hc) W) :
    ∃ W₂ : ValuationSubring (FFClosure (geomCurve Ω₂ C₂)),
      IsCuspPlace Ω₂ (subCurve C₂ V₂ hV₂ hne₂) (compl_nonempty_of_le hV₂ hc₂) W₂ ∧
      (arithInertia Ω (subCurve C V hV hne) (compl_nonempty_of_le hV hc) W).map
          φ.toMulEquiv.toMonoidHom =
        arithInertia Ω₂ (subCurve C₂ V₂ hV₂ hne₂) (compl_nonempty_of_le hV₂ hc₂) W₂ ∧
      (IsCentredOnU Ω C W ↔ IsCentredOnU Ω₂ C₂ W₂) ∧
      (IsCentredOnU Ω C W → ∀ g, ∃ g₂,
        ((arithDecomp Ω C hc W).map (MulAut.conj g).toMonoidHom).map Φ.toMonoidHom =
          (arithDecomp Ω₂ C₂ hc₂ W₂).map (MulAut.conj g₂).toMonoidHom) := by
  have hI : arithInertia Ω (subCurve C V hV hne) (compl_nonempty_of_le hV hc) W ∈
      arithCusps Ω (subCurve C V hV hne) (compl_nonempty_of_le hV hc) :=
    (mem_arithCusps_iff Ω _ _).2 ⟨W, hW, rfl⟩
  have hI₂ := ((h.iso ψ hpr).cusps_map _).1 hI
  obtain ⟨W₂, hW₂, hIW₂⟩ := (mem_arithCusps_iff Ω₂ _ _).1 hI₂
  obtain ⟨α₀, α₂, hφ⟩ := h
  have hIW₂' : (arithInertia Ω (subCurve C V hV hne) (compl_nonempty_of_le hV hc) W).map
      φ.toMulEquiv.toMonoidHom =
      arithInertia Ω₂ (subCurve C₂ V₂ hV₂ hne₂) (compl_nonempty_of_le hV₂ hc₂) W₂ := hIW₂
  -- killed iff killed
  have hkill : arithInertia Ω (subCurve C V hV hne) (compl_nonempty_of_le hV hc) W ≤
        (cor38Fill Ω C hc V hV hne α₀).ker ↔
      arithInertia Ω₂ (subCurve C₂ V₂ hV₂ hne₂) (compl_nonempty_of_le hV₂ hc₂) W₂ ≤
        (cor38Fill Ω₂ C₂ hc₂ V₂ hV₂ hne₂ α₂).ker := by
    rw [← hIW₂']
    constructor
    · rintro hle _ ⟨e, he, rfl⟩
      rw [MonoidHom.mem_ker]
      change cor38Fill Ω₂ C₂ hc₂ V₂ hV₂ hne₂ α₂ (φ e) = 1
      rw [hφ e]
      exact (congrArg Φ (hle he)).trans (map_one Φ)
    · intro hle e he
      rw [MonoidHom.mem_ker]
      have := MonoidHom.mem_ker.1 (hle ⟨e, he, rfl⟩)
      change cor38Fill Ω₂ C₂ hc₂ V₂ hV₂ hne₂ α₂ (φ e) = 1 at this
      rw [hφ e] at this
      exact (map_eq_one_iff Φ Φ.injective).1 this
  have hcent : IsCentredOnU Ω C W ↔ IsCentredOnU Ω₂ C₂ W₂ := by
    rw [← arithInertia_le_ker_cor38Fill_iff Ω C hc V hV hne α₀ hW,
      ← arithInertia_le_ker_cor38Fill_iff Ω₂ C₂ hc₂ V₂ hV₂ hne₂ α₂ hW₂]
    exact hkill
  refine ⟨W₂, hW₂, hIW₂', hcent, fun _ g => ?_⟩
  obtain ⟨s, hs⟩ := exists_map_cor38Fill_commensurator Ω C hc V hV hne α₀
  obtain ⟨s₂, hs₂⟩ := exists_map_cor38Fill_commensurator Ω₂ C₂ hc₂ V₂ hV₂ hne₂ α₂
  exact ⟨Φ g * Φ s⁻¹ * s₂, map_conj_eq_of_commensurator (cor38Fill Ω C hc V hV hne α₀)
    (cor38Fill Ω₂ C₂ hc₂ V₂ hV₂ hne₂ α₂) φ.toMulEquiv Φ hφ hIW₂' (hs W hW) (hs₂ W₂ hW₂) g⟩

end Transfer

section Points

variable {K : Type u} [Field K] [NumberField K] (Ω : Type u) [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] (C : HypCurve K)
  (hc : (C.U : Set C.Xbar)ᶜ.Nonempty)

attribute [local instance] isAlgClosure_of_isAlgebraic

/-- The embedding `ι : K(X̄) → K(X̄_Ω)^alg` does not depend on the open `V`. -/
lemma ffEmb_subCurve (V : C.Xbar.Opens) (hV : V ≤ C.U) (hne : (V : Set C.Xbar).Nonempty)
    (y : C.Xbar.functionField) :
    ffEmb Ω (subCurve C V hV hne) (compl_nonempty_of_le hV hc) y = ffEmb Ω C hc y :=
  (ffEmb_fillCurve_apply Ω (subCurve C V hV hne) (compl_nonempty_of_le hV hc) hV hc
    C.hyperbolic y).symm

/-- **Centred on `V_Ω`**, in terms of `ι`: `W ⊇ Ω` and `ι(Γ(V)) ⊆ W`. -/
lemma isCentredOnU_subCurve_iff (V : C.Xbar.Opens) (hV : V ≤ C.U)
    (hne : (V : Set C.Xbar).Nonempty) [Nonempty V]
    (W : ValuationSubring (FFClosure (geomCurve Ω C))) :
    IsCentredOnU Ω (subCurve C V hV hne) W ↔
      (∀ c : Ω, algebraMap Ω (FFClosure (geomCurve Ω C)) c ∈ W) ∧
        ∀ a : Γ(C.Xbar, V), ffEmb Ω C hc (C.Xbar.germToFunctionField V a) ∈ W := by
  haveI := IsCurveOver.isIntegral K C.Xbar
  refine (isCentredOn_geomOpen_iff Ω (subCurve C V hV hne) (compl_nonempty_of_le hV hc) W).trans ?_
  refine and_congr Iff.rfl (forall_congr' fun a => ?_)
  rw [← ffEmb_germ Ω (subCurve C V hV hne) (compl_nonempty_of_le hV hc) a,
    ffEmb_subCurve Ω C hc V hV hne]
  exact Iff.rfl

/-- Two places of `K(X̄_Ω)^alg` **over the same point of `X̄`**: the same restriction to
`ι(K(X̄))`. -/
def SamePt (W₁ W₂ : ValuationSubring (FFClosure (geomCurve Ω C))) : Prop :=
  ∀ y : C.Xbar.functionField, ffEmb Ω C hc y ∈ W₁ ↔ ffEmb Ω C hc y ∈ W₂

variable {Ω C hc} in
/-- Centredness on an open depends only on the point under the place. -/
lemma SamePt.isCentredOnU_iff {W₁ W₂ : ValuationSubring (FFClosure (geomCurve Ω C))}
    (h : SamePt Ω C hc W₁ W₂) (h₁ : ∀ c : Ω, algebraMap Ω (FFClosure (geomCurve Ω C)) c ∈ W₁)
    (h₂ : ∀ c : Ω, algebraMap Ω (FFClosure (geomCurve Ω C)) c ∈ W₂) (V : C.Xbar.Opens)
    (hV : V ≤ C.U) (hne : (V : Set C.Xbar).Nonempty) [Nonempty V] :
    IsCentredOnU Ω (subCurve C V hV hne) W₁ ↔ IsCentredOnU Ω (subCurve C V hV hne) W₂ := by
  rw [isCentredOnU_subCurve_iff Ω C hc, isCentredOnU_subCurve_iff Ω C hc]
  exact ⟨fun h' => ⟨h₂, fun a => (h _).1 (h'.2 a)⟩, fun h' => ⟨h₁, fun a => (h _).2 (h'.2 a)⟩⟩

/-- A place over a point `x ∈ V` is centred on `V_Ω`. -/
lemma isCentredOnU_of_comap_eq (V : C.Xbar.Opens) (hV : V ≤ C.U)
    (hne : (V : Set C.Xbar).Nonempty) [Nonempty V] {x : C.Xbar} (hx : x ∈ V)
    {W : ValuationSubring (FFClosure (geomCurve Ω C))}
    (hΩ : ∀ c : Ω, algebraMap Ω (FFClosure (geomCurve Ω C)) c ∈ W)
    (hWx : haveI := IsCurveOver.isIntegral K C.Xbar
      W.comap (ffEmb Ω C hc) = CurvesJacobian.stalkVS K x) :
    IsCentredOnU Ω (subCurve C V hV hne) W := by
  haveI := IsCurveOver.isIntegral K C.Xbar
  rw [isCentredOnU_subCurve_iff Ω C hc]
  refine ⟨hΩ, fun a => ?_⟩
  change C.Xbar.germToFunctionField V a ∈ W.comap (ffEmb Ω C hc)
  rw [hWx]
  exact ⟨C.Xbar.presheaf.germ V x hx a, by rw [Scheme.algebraMap_germ_eq_germToFunctionField]⟩

end Points

section Cusp

variable {K : Type u} [Field K] [NumberField K] {Ω : Type u} [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] {C : HypCurve K}
  {hc : (C.U : Set C.Xbar)ᶜ.Nonempty}

attribute [local instance] isAlgClosure_of_isAlgebraic

/-- A cusp place of `V` is not centred on `V_Ω`. -/
lemma IsCuspPlace.not_isCentredOnU {V : C.Xbar.Opens} {hV : V ≤ C.U}
    {hne : (V : Set C.Xbar).Nonempty} {W : ValuationSubring (FFClosure (geomCurve Ω C))}
    (hW : IsCuspPlace Ω (subCurve C V hV hne) (compl_nonempty_of_le hV hc) W) :
    ¬ IsCentredOnU Ω (subCurve C V hV hne) W := fun h =>
  hW.2 ((isCentredOn_geomOpen_iff Ω (subCurve C V hV hne) (compl_nonempty_of_le hV hc) W).1 h).2

/-- A place `W ⊇ Ω` not centred on `V_Ω` is a cusp place of `V`. -/
lemma isCuspPlace_of_not_isCentredOnU {V : C.Xbar.Opens} (hV : V ≤ C.U)
    (hne : (V : Set C.Xbar).Nonempty) {W : ValuationSubring (FFClosure (geomCurve Ω C))}
    (hΩ : ∀ c : Ω, algebraMap Ω (FFClosure (geomCurve Ω C)) c ∈ W)
    (hn : ¬ IsCentredOnU Ω (subCurve C V hV hne) W) :
    IsCuspPlace Ω (subCurve C V hV hne) (compl_nonempty_of_le hV hc) W :=
  ⟨hΩ, fun hall => hn ((isCentredOn_geomOpen_iff Ω (subCurve C V hV hne)
    (compl_nonempty_of_le hV hc) W).2 ⟨hΩ, hall⟩)⟩

omit [Algebra.IsAlgebraic K Ω] in
/-- Centred on `V_Ω` implies centred on `V'_Ω` for `V ⊆ V'`. -/
lemma isCentredOnU_mono {V V' : C.Xbar.Opens} {hV : V ≤ C.U} {hV' : V' ≤ C.U}
    {hne : (V : Set C.Xbar).Nonempty} {hne' : (V' : Set C.Xbar).Nonempty} (h : V ≤ V')
    {W : ValuationSubring (FFClosure (geomCurve Ω C))}
    (hW : IsCentredOnU Ω (subCurve C V hV hne) W) : IsCentredOnU Ω (subCurve C V' hV' hne') W := by
  haveI : Nonempty (baseChangeOpen K Ω V) :=
    inferInstanceAs (Nonempty (geomOpen Ω (subCurve C V hV hne)))
  haveI : Nonempty (baseChangeOpen K Ω V') :=
    inferInstanceAs (Nonempty (geomOpen Ω (subCurve C V' hV' hne')))
  exact isCentredOn_mono Ω C (baseChangeOpen_mono K Ω h) hW

end Cusp

section ItemOne

open Thm19 Pi1 Pi1.Orbifold KummerTheory KummerTheory.Curve AffOrbicurve CurvesJacobian
  CurvesJacobian.Kummer

variable {K : Type u} [Field K] [NumberField K] {Ω : Type u} [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] {C : HypCurve K}
  [hc : Fact (C.U : Set C.Xbar)ᶜ.Nonempty]

attribute [local instance] isIntegral_Xbar nonempty_U algFF

variable {τ : C.Xbar.functionField} (hτ : Transcendental K τ)
  [IsGalois (K₀ K (coordT τ)) (FFClosure C.Xbar)] (hU : C.U = chartOne K C.Xbar τ)
  [CharZero (FFClosure C.Xbar)]

include hτ hU in
/-- **[GalSect] Thm 1.3 (i) for the places of `ptDecomps`, as `SamePt`**: places whose
decomposition groups are conjugate lie over the same closed point of `U`
(`mem_iff_of_ptPlace_arithDecomp_le_conj`; rational point `σ₀` on `X̄`, genus `≠ 0`). -/
theorem samePt_of_arithDecomp_conj (σ₀ : Spec (CommRingCat.of K) ⟶ C.Xbar)
    (hσ₀ : σ₀ ≫ (C.Xbar ↘ Spec (CommRingCat.of K)) = 𝟙 (Spec (CommRingCat.of K)))
    (hg : CurvesJacobian.curveGenus K C.Xbar ≠ 0)
    {U₁ : C.Xbar.Opens} {hU₁ : U₁ ≤ C.U} {hne₁ : (U₁ : Set C.Xbar).Nonempty}
    {U₂ : C.Xbar.Opens} {hU₂ : U₂ ≤ C.U} {hne₂ : (U₂ : Set C.Xbar).Nonempty}
    {W₁ W₂ : ValuationSubring (FFClosure (geomCurve Ω C))}
    (hW₁ : IsCuspPlace Ω (subCurve C U₁ hU₁ hne₁) (compl_nonempty_of_le hU₁ hc.out) W₁)
    (hW₂ : IsCuspPlace Ω (subCurve C U₂ hU₂ hne₂) (compl_nonempty_of_le hU₂ hc.out) W₂)
    (hW₁U : IsCentredOnU Ω C W₁) (hW₂U : IsCentredOnU Ω C W₂)
    {g₁ g₂ : (arithmeticExt Ω C hc.out).Pi}
    (h : (arithDecomp Ω C hc.out W₁).map (MulAut.conj g₁).toMonoidHom =
      (arithDecomp Ω C hc.out W₂).map (MulAut.conj g₂).toMonoidHom) :
    SamePt Ω C hc.out W₁ W₂ := by
  intro y
  have hy : algebraMap C.Xbar.functionField (FFClosure C.Xbar) y ∈ F (curveGaloisData K hτ) :=
    mem_F_curveGaloisData_of_mem_L hτ (by
      rw [curveGaloisData_L]
      exact (mem_imageL_iff _).2 ⟨y, rfl⟩)
  have key := mem_iff_of_ptPlace_arithDecomp_le_conj hτ hU σ₀ hσ₀ hg U₁ hU₁ hne₁ U₂ hU₂ hne₂
    hW₁ hW₂ hW₁U hW₂U (g₂⁻¹ * g₁) (fun e he => by
      have hmem : g₂ * e * g₂⁻¹ ∈ (arithDecomp Ω C hc.out W₂).map (MulAut.conj g₂).toMonoidHom :=
        ⟨e, he, rfl⟩
      rw [← h] at hmem
      obtain ⟨e', he', hee⟩ := hmem
      refine ⟨e', he', ?_⟩
      change g₁ * e' * g₁⁻¹ = g₂ * e * g₂⁻¹ at hee
      calc e = g₂⁻¹ * (g₂ * e * g₂⁻¹) * g₂ := by group
        _ = g₂⁻¹ * g₁ * e' * (g₂⁻¹ * g₁)⁻¹ := by rw [← hee]; group) ⟨_, hy⟩
  change σc (Ω := Ω) (C := C) (algebraMap C.Xbar.functionField (FFClosure C.Xbar) y) ∈ W₁ ↔
    σc (Ω := Ω) (C := C) (algebraMap C.Xbar.functionField (FFClosure C.Xbar) y) ∈ W₂ at key
  rwa [σc_algebraMap] at key

end ItemOne

end Iut.Reconstruction
