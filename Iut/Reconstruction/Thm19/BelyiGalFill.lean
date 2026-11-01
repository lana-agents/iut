/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Thm19.BelyiMono

/-!
# The Cor 3.8 filling on arithmetic Galois actions (MR9 item 3, L5)

For a nonempty open `V ⊆ U` of an affine hyperbolic curve `C = (X̄, U)` over a number field, the
filling `cor38Fill : Π_V ↠ Π_U` of [AbsTopII] Cor 3.8 sends the arithmetic Galois action of
`τ ∈ Gal(K(X̄_Ω)^alg / K(X̄))` (curves-jacobian `arithAction`) for `V` to that of the same `τ`
(`castFill`) for `U`, up to one inner automorphism of `Π_U` independent of `τ`
(**`exists_cor38Fill_arithAction`**, L5 (a)): both are the Galois action at the generic point of
`Spec Γ(U)` reached through `Spec Γ(V)`, moved to the respective base points
(`fillMap_arithAction`, `arithAction_fillCurve`). In the Galois models (`piBridge`), the two
transports `σc_V h σc_V⁻¹`, `σc_U h σc_U⁻¹` of `h ∈ Gal(K(X̄)^alg / K(X̄))` differ by the
element `closureCmp = σc_V σc_U⁻¹` of `Gal(K(X̄_Ω)^alg / L₀)` (`castFill_arithAut`, L5 (b)), so
**`exists_cor38Fill_piBridge`**: `cor38Fill ∘ piBridge_V = conj c ∘ piBridge_U ∘ piT` for the
Galois-model filling `piT`.
-/

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale PreGaloisCategory
  Belyi Belyi.Anabelian CurvesJacobian.Cusp

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Iut.Reconstruction

section GalFill

variable {K : Type u} [Field K] [NumberField K] (Ω : Type u) [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] (C : HypCurve K)
  (hc : (C.U : Set C.Xbar)ᶜ.Nonempty)

attribute [local instance] isAlgClosure_of_isAlgebraic

/-- **L5 (a): the filling on arithmetic Galois actions.** There is `c ∈ Π_U` with
`cor38Fill (arithAction_V τ) = c · arithAction_U (castFill τ) · c⁻¹` for every
`τ ∈ Gal(K(X̄_Ω)^alg / K(X̄))`. -/
theorem exists_cor38Fill_arithAction {V : C.Xbar.Opens} (hV : V ≤ C.U)
    (hne : (V : Set C.Xbar).Nonempty)
    (α₀ : fiber (basePoint Ω C hc) ≅
      fiber (fillPoint Ω (subCurve C V hV hne) (compl_nonempty_of_le hV hc) hV)) :
    ∃ c : (arithmeticExt Ω C hc).Pi, ∀ τ,
      cor38Fill Ω C hc V hV hne α₀ (arithAction Ω (subCurve C V hV hne)
          (compl_nonempty_of_le hV hc) τ) =
        c * @id (arithmeticExt Ω C hc).Pi (arithAction Ω C hc (castFill Ω (subCurve C V hV hne)
          (compl_nonempty_of_le hV hc) hV hc C.hyperbolic τ)) * c⁻¹ := by
  set b := fiberIsoMap (baseChangeSpec K Ω Γ(C.Xbar, C.U)) rfl rfl α₀
  set A := fiberIsoMap (Spec.map (CommRingCat.ofHom (resAlg K hV).toRingHom)) rfl
    (fillPoint_spec Ω (subCurve C V hV hne) (compl_nonempty_of_le hV hc) hV)
    (arithFiberIso Ω (subCurve C V hV hne) (compl_nonempty_of_le hV hc))
  set G := fillGenIso Ω (subCurve C V hV hne) (compl_nonempty_of_le hV hc) hV hc C.hyperbolic
  refine ⟨@id (arithmeticExt Ω C hc).Pi (G.symm ≪≫ A ≪≫ b.symm : Aut _), fun τ => ?_⟩
  simp only [id_eq]
  have e1 := fillMap_arithAction Ω (subCurve C V hV hne) (compl_nonempty_of_le hV hc) hV τ
  have e2 : arithAction Ω C hc (castFill Ω (subCurve C V hV hne) (compl_nonempty_of_le hV hc) hV
      hc C.hyperbolic τ) = autContinuousMulEquivOfIso G (galoisAction
        (arithFF Ω (subCurve C V hV hne) (compl_nonempty_of_le hV hc))
        (arithGenPt Ω (subCurve C V hV hne) (compl_nonempty_of_le hV hc) ≫
          Spec.map (CommRingCat.ofHom (resAlg K hV).toRingHom))
        (fillGen_spec Ω (subCurve C V hV hne) (compl_nonempty_of_le hV hc) hV) τ) :=
    arithAction_fillCurve Ω (subCurve C V hV hne) (compl_nonempty_of_le hV hc) hV hc
      C.hyperbolic τ
  change (autContinuousMulEquivOfIso b).symm (fillMap Ω (subCurve C V hV hne)
    (compl_nonempty_of_le hV hc) hV (arithAction Ω (subCurve C V hV hne)
      (compl_nonempty_of_le hV hc) τ)) = _
  rw [e1, e2, ← CurvesJacobian.Cusp.autContinuousMulEquivOfIso_self,
    autContinuousMulEquivOfIso_symm_apply, autContinuousMulEquivOfIso_trans_apply]
  rw [show G ≪≫ G.symm ≪≫ A ≪≫ b.symm = A ≪≫ b.symm by simp]
  exact autContinuousMulEquivOfIso_trans_apply _ _ _

end GalFill

section GalFillB

open Thm19 Pi1 Pi1.Orbifold KummerTheory KummerTheory.Curve AffOrbicurve CurvesJacobian

variable {K : Type u} [Field K] [NumberField K] (Ω : Type u) [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] (C : HypCurve K)
  [hc : Fact (C.U : Set C.Xbar)ᶜ.Nonempty]
  (V : C.Xbar.Opens) (hV : V ≤ C.U) (hne : (V : Set C.Xbar).Nonempty)
  [hcV : Fact ((subCurve C V hV hne).U : Set (subCurve C V hV hne).Xbar)ᶜ.Nonempty]

attribute [local instance] isIntegral_Xbar nonempty_U algFF isAlgClosure_of_isAlgebraic

/-- The Galois instance of a coordinate, read on `(X̄, V)` (the same scheme `X̄`). -/
instance isGalois_subCurve {τ₀ : C.Xbar.functionField}
    [h : IsGalois (K₀ K (coordT τ₀)) (FFClosure C.Xbar)] :
    IsGalois (K₀ K (coordT (X := (subCurve C V hV hne).Xbar) τ₀))
      (FFClosure (subCurve C V hV hne).Xbar) := h

/-- The comparison `σc_V ∘ σc_U⁻¹ ∈ Gal(K(X̄_Ω)^alg / L₀)` of the two identifications
`K(X̄)^alg ≃ K(X̄_Ω)^alg` over `K(X̄)` (`closureEquiv` for the curves `(X̄, V)` and `(X̄, U)`; both
are `K(X̄)`-linear because `ι` does not depend on the open, `ffEmb_subCurve`). -/
def closureCmp : FFClosure (geomCurve Ω C) ≃ₐ[arithFF Ω C hc.out] FFClosure (geomCurve Ω C) :=
  AlgEquiv.ofRingEquiv
    (f := (σc (Ω := Ω) (C := C)).symm.trans (σc (Ω := Ω) (C := subCurve C V hV hne)))
    fun y => by
      obtain ⟨x, rfl⟩ := (ffEquiv Ω C).surjective y
      change σc (Ω := Ω) (C := subCurve C V hV hne) ((σc (Ω := Ω) (C := C)).symm
        (ffEmb Ω C hc.out x)) = ffEmb Ω C hc.out x
      have e : (σc (Ω := Ω) (C := C)).symm (ffEmb Ω C hc.out x) =
          algebraMap C.Xbar.functionField (FFClosure C.Xbar) x := by
        rw [RingEquiv.symm_apply_eq]
        exact (σc_algebraMap (Ω := Ω) (C := C) x).symm
      rw [e]
      exact (σc_algebraMap (Ω := Ω) (C := subCurve C V hV hne) x).trans
        (ffEmb_subCurve Ω C hc.out V hV hne x)

lemma closureCmp_apply (y : FFClosure (geomCurve Ω C)) :
    closureCmp Ω C V hV hne y =
      σc (Ω := Ω) (C := subCurve C V hV hne) ((σc (Ω := Ω) (C := C)).symm y) := rfl

lemma closureCmp_inv_apply (y : FFClosure (geomCurve Ω C)) :
    (closureCmp Ω C V hV hne)⁻¹ y =
      σc (Ω := Ω) (C := C) ((σc (Ω := Ω) (C := subCurve C V hV hne)).symm y) := rfl

variable {Ω C V hV hne}

/-- **L5 (b): the transports of `h ∈ H` for `V` and for `U` differ by `closureCmp`.** For
`h ∈ H_V = Gal(K(X̄)^alg / K(X̄))` (Galois model of `(X̄, V)`, coordinate `τ₀`) and its image
in `H_U` (`hT`, the same automorphism over `K(τ)`):
`castFill (σc_V h σc_V⁻¹) = g · σc_U h σc_U⁻¹ · g⁻¹` with `g = closureCmp`. -/
theorem castFill_arithAut {τ₀ : C.Xbar.functionField} (hτ₀ : Transcendental K τ₀)
    [IsGalois (K₀ K (coordT τ₀)) (FFClosure C.Xbar)] {τ : C.Xbar.functionField}
    (hτ : Transcendental K τ) [IsGalois (K₀ K (coordT τ)) (FFClosure C.Xbar)]
    (hF : ∀ x ∈ F (curveGaloisData K hτ), x ∈ F (curveGaloisData K hτ₀))
    (h : (curveGaloisData K hτ₀).H) :
    @Eq (FFClosure (geomCurve Ω C) ≃ₐ[arithFF Ω C hc.out] FFClosure (geomCurve Ω C))
      (castFill Ω (subCurve C V hV hne) hcV.out hV hc.out C.hyperbolic
        (arithAut (Ω := Ω) (C := subCurve C V hV hne) hτ₀ h))
      (closureCmp Ω C V hV hne *
        arithAut (Ω := Ω) (C := C) hτ (hT (curveGaloisData K hτ) (curveGaloisData K hτ₀) hF h) *
        (closureCmp Ω C V hV hne)⁻¹) := by
  refine AlgEquiv.ext fun y => ?_
  change σc (Ω := Ω) (C := subCurve C V hV hne)
      ((h : FFClosure C.Xbar ≃ₐ[K₀ K (coordT τ₀)] FFClosure C.Xbar)
        ((σc (Ω := Ω) (C := subCurve C V hV hne)).symm y)) =
    σc (Ω := Ω) (C := subCurve C V hV hne) ((σc (Ω := Ω) (C := C)).symm
      (σc (Ω := Ω) (C := C) ((h : FFClosure C.Xbar ≃ₐ[K₀ K (coordT τ₀)] FFClosure C.Xbar)
        ((σc (Ω := Ω) (C := C)).symm (σc (Ω := Ω) (C := C)
          ((σc (Ω := Ω) (C := subCurve C V hV hne)).symm y))))))
  rw [RingEquiv.symm_apply_apply, RingEquiv.symm_apply_apply]

/-- **L5: the Cor 3.8 filling in the Galois models.** For `V = chartOne τ₀ ⊆ U = chartOne τ`,
there is `c ∈ Π_U` with `cor38Fill (piBridge_V x) = c · piBridge_U (piT x) · c⁻¹` for all
`x ∈ Π_V` (Galois model), where `piT : Π_V → Π_U` is the Galois-model filling (`σ ↦ σ`).
From `exists_cor38Fill_arithAction` (L5 (a)), `castFill_arithAut` (L5 (b)) and `piBridge_mk`. -/
theorem exists_cor38Fill_piBridge {τ₀ : C.Xbar.functionField} (hτ₀ : Transcendental K τ₀)
    [IsGalois (K₀ K (coordT τ₀)) (FFClosure C.Xbar)] (hU₀ : V = chartOne K C.Xbar τ₀)
    {τ : C.Xbar.functionField} (hτ : Transcendental K τ)
    [IsGalois (K₀ K (coordT τ)) (FFClosure C.Xbar)] (hU : C.U = chartOne K C.Xbar τ)
    (hF : ∀ x ∈ F (curveGaloisData K hτ), x ∈ F (curveGaloisData K hτ₀))
    (hW : ∀ W : ValuationSubring (FFClosure C.Xbar),
      (∀ c : K, algebraMap K (FFClosure C.Xbar) c ∈ W) → coordT τ₀ ∈ W →
        (∀ c : K, algebraMap K (FFClosure C.Xbar) c ∈ W) ∧ coordT τ ∈ W)
    (α₀ : fiber (basePoint Ω C hc.out) ≅
      fiber (fillPoint Ω (subCurve C V hV hne) hcV.out hV)) :
    ∃ c : (arithmeticExt Ω C hc.out).Pi, ∀ x,
      cor38Fill Ω C hc.out V hV hne α₀
          (piBridge (Ω := Ω) (C := subCurve C V hV hne) hτ₀ hU₀ x) =
        c * piBridge (Ω := Ω) (C := C) hτ hU (piT (curveGaloisData K hτ) (curveGaloisData K hτ₀)
          hF hW (curveGaloisData_H_le K hτ) x) * c⁻¹ := by
  obtain ⟨c, hcc⟩ := exists_cor38Fill_arithAction Ω C hc.out hV hne α₀
  refine ⟨c * @id (arithmeticExt Ω C hc.out).Pi (arithAction Ω C hc.out (closureCmp Ω C V hV hne)),
    fun x => ?_⟩
  induction x using QuotientGroup.induction_on with
  | H h =>
    rw [piBridge_mk, hcc, castFill_arithAut hτ₀ hτ hF h, map_mul, map_mul, map_inv, piT_mk,
      piBridge_mk]
    simp only [id_eq]
    group

end GalFillB

end Iut.Reconstruction
