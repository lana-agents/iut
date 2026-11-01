/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Thm19.BelyiGalFill
import Iut.Reconstruction.Thm19.StageIso
import Iut.Reconstruction.Thm19.CycloBridge

/-!
# Cor 3.8 lifts in the Galois models, normalised over `ψ` (MR9 item 3, step 5)

For an isomorphism `Φ` of the `arithmeticExt` of two affine hyperbolic curves `U = chartOne τ`,
`U' = chartOne τ₂` over number fields and a Cor 3.8 lift `φ : Π_V ≃ₜ* Π_{V₂}` of `Φ`
(`IsCor38Lift`, [AbsTopII] Cor 3.8) with `V = chartOne τ₀`, `V₂ = chartOne υ`:

* `galLift`: `φ` in the Galois models (`piBridge` on both sides);
* `piT_surjective_curve`: the Galois-model filling `Π_V ↠ Π_U` is surjective (from L5 and
  `cor38Fill_surjective₂`);
* **`IsCor38Lift.exists_galLift_rel`**: `piT' ∘ galLift = conj d ∘ bridgeIso ∘ piT` (L5 on both
  sides and the lift equation);
* **`IsCor38Lift.exists_galNormal`**: after composing with an inner automorphism, the lift
  satisfies `piT' ∘ e = bridgeIso ∘ piT` **exactly**; in particular it lies over `gkIso Φ`
  exactly (`piToGk_of_piT_eq`).
-/

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale PreGaloisCategory
  Belyi Belyi.Anabelian CurvesJacobian.Cusp

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Iut.Reconstruction

open Thm19 Pi1 Pi1.Orbifold KummerTheory KummerTheory.Curve AffOrbicurve CurvesJacobian
  CurvesJacobian.Kummer

section Surj

variable {K : Type u} [Field K] [NumberField K] {C : HypCurve K}
  [hc : Fact (C.U : Set C.Xbar)ᶜ.Nonempty]
  {V : C.Xbar.Opens} {hV : V ≤ C.U} {hne : (V : Set C.Xbar).Nonempty}
  [hcV : Fact ((subCurve C V hV hne).U : Set (subCurve C V hV hne).Xbar)ᶜ.Nonempty]

attribute [local instance] isIntegral_Xbar nonempty_U

include hcV in
/-- **The Galois-model filling `Π_V ↠ Π_U` is surjective** (through `Π_V ↠ Π_U` of
`arithmeticExt`, `cor38Fill_surjective₂`, and L5). -/
theorem piT_surjective_curve (Ω : Type u) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]
    [Algebra.IsAlgebraic K Ω] [CharZero Ω]
    {τ₀ : C.Xbar.functionField} (hτ₀ : Transcendental K τ₀)
    [IsGalois (K₀ K (coordT τ₀)) (FFClosure C.Xbar)] (hU₀ : V = chartOne K C.Xbar τ₀)
    {τ : C.Xbar.functionField} (hτ : Transcendental K τ)
    [IsGalois (K₀ K (coordT τ)) (FFClosure C.Xbar)] (hU : C.U = chartOne K C.Xbar τ)
    (hF : ∀ x ∈ F (curveGaloisData K hτ), x ∈ F (curveGaloisData K hτ₀))
    (hW : ∀ W : ValuationSubring (FFClosure C.Xbar),
      (∀ c : K, algebraMap K (FFClosure C.Xbar) c ∈ W) → coordT τ₀ ∈ W →
        (∀ c : K, algebraMap K (FFClosure C.Xbar) c ∈ W) ∧ coordT τ ∈ W) :
    Function.Surjective (piT (curveGaloisData K hτ) (curveGaloisData K hτ₀) hF hW
      (curveGaloisData_H_le K hτ)) := by
  haveI := isAlgClosure_of_isAlgebraic (K := K) (Ω := Ω)
  obtain ⟨α₀⟩ : Nonempty (fiber (basePoint Ω C hc.out) ≅
      fiber (fillPoint Ω (subCurve C V hV hne) hcV.out hV)) := by
    haveI := isIntegral_specTensor Ω C hc.out
    exact nonempty_iso_of_fiberFunctor _ _
  obtain ⟨c, hcc⟩ := exists_cor38Fill_piBridge hτ₀ hU₀ hτ hU hF hW α₀
  intro y
  obtain ⟨w, hw⟩ := cor38Fill_surjective₂ Ω C hc.out V hV hne α₀
    (c * piBridge (Ω := Ω) hτ hU y * c⁻¹)
  refine ⟨(piBridge (Ω := Ω) (C := subCurve C V hV hne) hτ₀ hU₀).symm w, ?_⟩
  apply (piBridge (Ω := Ω) hτ hU).injective
  have e := hcc ((piBridge (Ω := Ω) (C := subCurve C V hV hne) hτ₀ hU₀).symm w)
  rw [ContinuousMulEquiv.apply_symm_apply, hw] at e
  exact (mul_left_cancel (mul_right_cancel e)).symm

end Surj

section GalLift

variable {K : Type u} [Field K] [NumberField K] {Ω : Type u} [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] {C : HypCurve K}
  [hc : Fact (C.U : Set C.Xbar)ᶜ.Nonempty]
  {K₂ : Type u} [Field K₂] [NumberField K₂] {Ω₂ : Type u} [Field Ω₂] [Algebra K₂ Ω₂]
  [IsAlgClosed Ω₂] [Algebra.IsAlgebraic K₂ Ω₂] [CharZero Ω₂] {C₂ : HypCurve K₂}
  [hc₂ : Fact (C₂.U : Set C₂.Xbar)ᶜ.Nonempty]

attribute [local instance] isIntegral_Xbar nonempty_U algFF isAlgClosure_of_isAlgebraic

variable {τ : C.Xbar.functionField} (hτ : Transcendental K τ)
  [IsGalois (K₀ K (coordT τ)) (FFClosure C.Xbar)] (hU : C.U = chartOne K C.Xbar τ)
  {τ₂ : C₂.Xbar.functionField} (hτ₂ : Transcendental K₂ τ₂)
  [IsGalois (K₀ K₂ (coordT τ₂)) (FFClosure C₂.Xbar)] (hU₂ : C₂.U = chartOne K₂ C₂.Xbar τ₂)
  (Φ : (arithmeticExt Ω C hc.out).Iso (arithmeticExt Ω₂ C₂ hc₂.out))
  {V : C.Xbar.Opens} {hV : V ≤ C.U} {hne : (V : Set C.Xbar).Nonempty}
  [hcV : Fact ((subCurve C V hV hne).U : Set (subCurve C V hV hne).Xbar)ᶜ.Nonempty]
  {V₂ : C₂.Xbar.Opens} {hV₂ : V₂ ≤ C₂.U} {hne₂ : (V₂ : Set C₂.Xbar).Nonempty}
  [hcV₂ : Fact ((subCurve C₂ V₂ hV₂ hne₂).U : Set (subCurve C₂ V₂ hV₂ hne₂).Xbar)ᶜ.Nonempty]
  {τ₀ : C.Xbar.functionField} (hτ₀ : Transcendental K τ₀)
  [IsGalois (K₀ K (coordT τ₀)) (FFClosure C.Xbar)] (hU₀ : V = chartOne K C.Xbar τ₀)
  {υ : C₂.Xbar.functionField} (hυ : Transcendental K₂ υ)
  [IsGalois (K₀ K₂ (coordT υ)) (FFClosure C₂.Xbar)] (hUυ : V₂ = chartOne K₂ C₂.Xbar υ)
  (hF : ∀ x ∈ F (curveGaloisData K hτ), x ∈ F (curveGaloisData K hτ₀))
  (hW : ∀ W : ValuationSubring (FFClosure C.Xbar),
    (∀ c : K, algebraMap K (FFClosure C.Xbar) c ∈ W) → coordT τ₀ ∈ W →
      (∀ c : K, algebraMap K (FFClosure C.Xbar) c ∈ W) ∧ coordT τ ∈ W)
  (hF₂ : ∀ x ∈ F (curveGaloisData K₂ hτ₂), x ∈ F (curveGaloisData K₂ hυ))
  (hW₂ : ∀ W : ValuationSubring (FFClosure C₂.Xbar),
    (∀ c : K₂, algebraMap K₂ (FFClosure C₂.Xbar) c ∈ W) → coordT υ ∈ W →
      (∀ c : K₂, algebraMap K₂ (FFClosure C₂.Xbar) c ∈ W) ∧ coordT τ₂ ∈ W)
  (φ : (arithmeticExt Ω (subCurve C V hV hne) hcV.out).Pi ≃ₜ*
    (arithmeticExt Ω₂ (subCurve C₂ V₂ hV₂ hne₂) hcV₂.out).Pi)

/-- A lift `φ : Π_V ≃ₜ* Π_{V₂}` in the Galois models (`piBridge` on both sides). -/
def galLift : Pi (curveGaloisData K hτ₀) ≃ₜ* Pi (curveGaloisData K₂ hυ) :=
  (piBridge (Ω := Ω) (C := subCurve C V hV hne) hτ₀ hU₀).trans
    (φ.trans (piBridge (Ω := Ω₂) (C := subCurve C₂ V₂ hV₂ hne₂) hυ hUυ).symm)

omit hc hc₂ in
lemma piBridge_galLift (x : Pi (curveGaloisData K hτ₀)) :
    piBridge (Ω := Ω₂) (C := subCurve C₂ V₂ hV₂ hne₂) hυ hUυ (galLift hτ₀ hU₀ hυ hUυ φ x) =
      φ (piBridge (Ω := Ω) (C := subCurve C V hV hne) hτ₀ hU₀ x) :=
  ContinuousMulEquiv.apply_symm_apply _ _

variable {Φ φ}

set_option maxHeartbeats 1600000 in
-- the quotients `Π_U`, `Π_V` are slow for unification
set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_V` are found slowly
/-- **The lift equation in the Galois models**: for a Cor 3.8 lift `φ` of `Φ`,
`piT' ∘ galLift φ = conj d ∘ bridgeIso Φ ∘ piT` (L5 on both sides). -/
theorem IsCor38Lift.exists_galLift_rel
    (h : IsCor38Lift Φ.pi.toMulEquiv hV hne hV₂ hne₂ φ) :
    ∃ d, ∀ x, piT (curveGaloisData K₂ hτ₂) (curveGaloisData K₂ hυ) hF₂ hW₂
        (curveGaloisData_H_le K₂ hτ₂) (galLift hτ₀ hU₀ hυ hUυ φ x) =
      d * bridgeIso hτ hU hτ₂ hU₂ Φ (piT (curveGaloisData K hτ) (curveGaloisData K hτ₀) hF hW
        (curveGaloisData_H_le K hτ) x) * d⁻¹ := by
  obtain ⟨α₀, α₂, hφ⟩ := h
  obtain ⟨c, hcc⟩ := exists_cor38Fill_piBridge hτ₀ hU₀ hτ hU hF hW α₀
  obtain ⟨c₂, hcc₂⟩ := exists_cor38Fill_piBridge hυ hUυ hτ₂ hU₂ hF₂ hW₂ α₂
  refine ⟨(piBridge (Ω := Ω₂) hτ₂ hU₂).symm (c₂⁻¹ * Φ.pi c), fun x => ?_⟩
  apply (piBridge (Ω := Ω₂) hτ₂ hU₂).injective
  have k1 : piBridge (Ω := Ω₂) hτ₂ hU₂ (piT (curveGaloisData K₂ hτ₂) (curveGaloisData K₂ hυ) hF₂
      hW₂ (curveGaloisData_H_le K₂ hτ₂) (galLift hτ₀ hU₀ hυ hUυ φ x)) =
      c₂⁻¹ * cor38Fill Ω₂ C₂ hc₂.out V₂ hV₂ hne₂ α₂
        (piBridge (Ω := Ω₂) (C := subCurve C₂ V₂ hV₂ hne₂) hυ hUυ
          (galLift hτ₀ hU₀ hυ hUυ φ x)) * c₂ := by
    rw [hcc₂]; group
  have k2 : cor38Fill Ω₂ C₂ hc₂.out V₂ hV₂ hne₂ α₂
      (piBridge (Ω := Ω₂) (C := subCurve C₂ V₂ hV₂ hne₂) hυ hUυ
        (galLift hτ₀ hU₀ hυ hUυ φ x)) =
      Φ.pi (c * piBridge (Ω := Ω) hτ hU (piT (curveGaloisData K hτ) (curveGaloisData K hτ₀) hF hW
        (curveGaloisData_H_le K hτ) x) * c⁻¹) := by
    rw [piBridge_galLift, hφ, hcc]
    rfl
  rw [k1, k2]
  simp only [map_mul, map_inv, piBridge_bridgeIso, ContinuousMulEquiv.apply_symm_apply]
  group

set_option maxHeartbeats 1600000 in
-- the quotients `Π_U`, `Π_V` are slow for unification
set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_V` are found slowly
/-- **Normalised lifts**: a Cor 3.8 lift of `Φ`, composed with an inner automorphism, satisfies
`piT' ∘ e = bridgeIso Φ ∘ piT` exactly. -/
theorem IsCor38Lift.exists_galNormal
    (h : IsCor38Lift Φ.pi.toMulEquiv hV hne hV₂ hne₂ φ) :
    ∃ e : Pi (curveGaloisData K hτ₀) ≃ₜ* Pi (curveGaloisData K₂ hυ),
      (∀ x, piT (curveGaloisData K₂ hτ₂) (curveGaloisData K₂ hυ) hF₂ hW₂
          (curveGaloisData_H_le K₂ hτ₂) (e x) =
        bridgeIso hτ hU hτ₂ hU₂ Φ (piT (curveGaloisData K hτ) (curveGaloisData K hτ₀) hF hW
          (curveGaloisData_H_le K hτ) x)) ∧
      ∃ b, ∀ x, e x = b * galLift hτ₀ hU₀ hυ hUυ φ x * b⁻¹ := by
  obtain ⟨d, hd⟩ := h.exists_galLift_rel hτ hU hτ₂ hU₂ hτ₀ hU₀ hυ hUυ hF hW hF₂ hW₂
  obtain ⟨d', hd'⟩ := piT_surjective_curve Ω₂ hυ hUυ hτ₂ hU₂ hF₂ hW₂ d
  refine ⟨(galLift hτ₀ hU₀ hυ hUυ φ).trans (conjCME d'⁻¹), fun x => ?_, d'⁻¹, fun x => rfl⟩
  change piT (curveGaloisData K₂ hτ₂) (curveGaloisData K₂ hυ) hF₂ hW₂
    (curveGaloisData_H_le K₂ hτ₂) (d'⁻¹ * galLift hτ₀ hU₀ hυ hUυ φ x * d'⁻¹⁻¹) = _
  rw [map_mul, map_mul, inv_inv, map_inv, hd', hd]
  group

set_option maxHeartbeats 1600000 in
-- the quotients `Π_U`, `Π_V` are slow for unification
set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_V` are found slowly
/-- **Normalised lifts lie over `gkIso Φ` exactly.** -/
theorem piToGk_of_piT_eq {e : Pi (curveGaloisData K hτ₀) ≃ₜ* Pi (curveGaloisData K₂ hυ)}
    (he : ∀ x, piT (curveGaloisData K₂ hτ₂) (curveGaloisData K₂ hυ) hF₂ hW₂
          (curveGaloisData_H_le K₂ hτ₂) (e x) =
        bridgeIso hτ hU hτ₂ hU₂ Φ (piT (curveGaloisData K hτ) (curveGaloisData K hτ₀) hF hW
          (curveGaloisData_H_le K hτ) x)) (x : Pi (curveGaloisData K hτ₀)) :
    piToGk (curveGaloisData K₂ hυ) (e x) =
      gkIso hτ hU hτ₂ hU₂ Φ (piToGk (curveGaloisData K hτ₀) x) := by
  rw [← piToGk_piT (curveGaloisData K₂ hτ₂) (curveGaloisData K₂ hυ) hF₂ hW₂
    (curveGaloisData_H_le K₂ hτ₂), he, bridgeIso_gk, piToGk_piT]

section Cyclo

variable [Fact (0 < (CurvesJacobian.curveGenus K C.Xbar).toNat)]
  [Fact (0 < (CurvesJacobian.curveGenus K₂ C₂.Xbar).toNat)]

/-- **The cyclotome at `V`**: `Ẑ(1)_{F_V} ≃ₜ* Ẑ(1)_{F_{V₂}}`, `cycloIso Φ` of `U` read through the
identifications `zT` of `Ẑ(1)` along `V ⊆ U`, `V₂ ⊆ U'` ([AbsTopIII] Thm 1.9 (b): the cyclotome
`μ_Ẑ(Π_U)` is the same for all opens; genus `≥ 1`). -/
def cycloV : ZHatOne (F (curveGaloisData K hτ₀)) (FFClosure C.Xbar) ≃ₜ*
    ZHatOne (F (curveGaloisData K₂ hυ)) (FFClosure C₂.Xbar) :=
  (zHatResEquiv (FFClosure C.Xbar) (F (curveGaloisData K hτ))
      (F (curveGaloisData K hτ₀))).symm.trans
    ((cycloIso hτ hU hτ₂ hU₂ Φ).trans
      (zHatResEquiv (FFClosure C₂.Xbar) (F (curveGaloisData K₂ hτ₂)) (F (curveGaloisData K₂ hυ))))

set_option maxHeartbeats 1600000 in
-- the quotients `Π_U`, `Π_V` are slow for unification
set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_V` are found slowly
/-- **`cycloV` is equivariant along a normalised lift.** -/
theorem cycloV_smul {e : Pi (curveGaloisData K hτ₀) ≃ₜ* Pi (curveGaloisData K₂ hυ)}
    (he : ∀ x, piT (curveGaloisData K₂ hτ₂) (curveGaloisData K₂ hυ) hF₂ hW₂
          (curveGaloisData_H_le K₂ hτ₂) (e x) =
        bridgeIso hτ hU hτ₂ hU₂ Φ (piT (curveGaloisData K hτ) (curveGaloisData K hτ₀) hF hW
          (curveGaloisData_H_le K hτ) x))
    (p : Pi (curveGaloisData K hτ₀)) (z : ZHatOne (F (curveGaloisData K hτ₀)) (FFClosure C.Xbar)) :
    cycloV (Φ := Φ) hτ hU hτ₂ hU₂ hτ₀ hυ (p • z) =
      e p • cycloV (Φ := Φ) hτ hU hτ₂ hU₂ hτ₀ hυ z := by
  obtain ⟨w, rfl⟩ := (zHatResEquiv (FFClosure C.Xbar) (F (curveGaloisData K hτ))
    (F (curveGaloisData K hτ₀))).surjective z
  have h1 : ∀ y, (zHatResEquiv (FFClosure C.Xbar) (F (curveGaloisData K hτ))
      (F (curveGaloisData K hτ₀))).symm (zHatResEquiv (FFClosure C.Xbar)
        (F (curveGaloisData K hτ)) (F (curveGaloisData K hτ₀)) y) = y :=
    fun y => ContinuousMulEquiv.symm_apply_apply _ y
  have h2 : p • zHatResEquiv (FFClosure C.Xbar) (F (curveGaloisData K hτ))
      (F (curveGaloisData K hτ₀)) w =
      zHatResEquiv (FFClosure C.Xbar) (F (curveGaloisData K hτ)) (F (curveGaloisData K hτ₀))
        (piT (curveGaloisData K hτ) (curveGaloisData K hτ₀) hF hW (curveGaloisData_H_le K hτ) p •
          w) :=
    (zT_piT_smul (curveGaloisData K hτ) (curveGaloisData K hτ₀) hF hW
      (curveGaloisData_H_le K hτ) p w).symm
  change zT (curveGaloisData K₂ hτ₂) (curveGaloisData K₂ hυ) (cycloIso hτ hU hτ₂ hU₂ Φ
      ((zHatResEquiv (FFClosure C.Xbar) (F (curveGaloisData K hτ))
        (F (curveGaloisData K hτ₀))).symm (p • _))) =
    e p • zT (curveGaloisData K₂ hτ₂) (curveGaloisData K₂ hυ) (cycloIso hτ hU hτ₂ hU₂ Φ
      ((zHatResEquiv (FFClosure C.Xbar) (F (curveGaloisData K hτ))
        (F (curveGaloisData K hτ₀))).symm _))
  rw [h2, h1, h1, cycloIso_smul, ← he, zT_piT_smul]

set_option maxHeartbeats 1600000 in
-- the quotients `Π_U`, `Π_V` are slow for unification
set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_V` are found slowly
/-- **The stage isomorphism at a geometric stage `V_{K₁}`** ([AbsTopIII] Thm 1.9 (d) over `Φ`):
`H¹(Π_{V_{K₁}}, Ẑ(1)) ≃* H¹(Π_{V₂,K₁'}, Ẑ(1))` from a normalised lift `e` (`constH1Iso` with
`ψ = gkIso Φ`, `G_{K₁'} = ψ(G_{K₁})`, coefficients `cycloV`). -/
def stageH1Iso {e : Pi (curveGaloisData K hτ₀) ≃ₜ* Pi (curveGaloisData K₂ hυ)}
    (he : ∀ x, piT (curveGaloisData K₂ hτ₂) (curveGaloisData K₂ hυ) hF₂ hW₂
          (curveGaloisData_H_le K₂ hτ₂) (e x) =
        bridgeIso hτ hU hτ₂ hU₂ Φ (piT (curveGaloisData K hτ) (curveGaloisData K hτ₀) hF hW
          (curveGaloisData_H_le K hτ) x))
    (K₁ : IntermediateField K (FFClosure C.Xbar)) [FiniteDimensional K K₁]
    [FiniteDimensional K₂ (constField (gkIso hτ hU hτ₂ hU₂ Φ) K₁)] :
    ContH1 (Pi (constExt K₁ (curveGaloisData K hτ₀)))
        (ZHatOne (F (constExt K₁ (curveGaloisData K hτ₀))) (FFClosure C.Xbar)) ≃*
      ContH1 (Pi (constExt (constField (gkIso hτ hU hτ₂ hU₂ Φ) K₁) (curveGaloisData K₂ hυ)))
        (ZHatOne (F (constExt (constField (gkIso hτ hU hτ₂ hU₂ Φ) K₁) (curveGaloisData K₂ hυ)))
          (FFClosure C₂.Xbar)) :=
  constH1Iso e (gkIso hτ hU hτ₂ hU₂ Φ)
    (piToGk_of_piT_eq hτ hU hτ₂ hU₂ hτ₀ hυ hF hW hF₂ hW₂ he)
    (piToGk_surjective_curve hτ₀) (cycloV (Φ := Φ) hτ hU hτ₂ hU₂ hτ₀ hυ)
    (cycloV_smul (Φ := Φ) hτ hU hτ₂ hU₂ hτ₀ hυ hF hW hF₂ hW₂ he) K₁

end Cyclo

end GalLift

section GalConj

variable {K : Type u} [Field K] [NumberField K] {Ω : Type u} [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] {C : HypCurve K}
  {K₂ : Type u} [Field K₂] [NumberField K₂] {Ω₂ : Type u} [Field Ω₂] [Algebra K₂ Ω₂]
  [IsAlgClosed Ω₂] [Algebra.IsAlgebraic K₂ Ω₂] [CharZero Ω₂] {C₂ : HypCurve K₂}

attribute [local instance] isIntegral_Xbar nonempty_U algFF isAlgClosure_of_isAlgebraic

set_option maxHeartbeats 1600000 in
-- the quotients `Π_U`, `Π_V` are slow for unification
set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_V` are found slowly
/-- **L3 in the Galois models**: if the lifts `φ` on `V` and `φ♮` on `V♮ ⊇ V` satisfy
`f₂ ∘ φ = conj m₀ ∘ φ♮ ∘ f` for Cor 3.8 fillings `f : Π_V ↠ Π_{V♮}`, `f₂`
(`IsCor38Lift.exists_conj`), then `piT' ∘ galLift φ = conj m ∘ galLift φ♮ ∘ piT` for the
Galois-model fillings (L5 for the curves `(X̄, V♮)`, `(X̄₂, V₂♮)`). -/
theorem exists_galLift_conj
    {VB : C.Xbar.Opens} {hVB : VB ≤ C.U} {hneB : (VB : Set C.Xbar).Nonempty}
    [hcVB : Fact ((subCurve C VB hVB hneB).U : Set (subCurve C VB hVB hneB).Xbar)ᶜ.Nonempty]
    {V : C.Xbar.Opens} {hV : V ≤ C.U} {hne : (V : Set C.Xbar).Nonempty} (hVV : V ≤ VB)
    [hcV : Fact ((subCurve C V hV hne).U : Set (subCurve C V hV hne).Xbar)ᶜ.Nonempty]
    {V₂B : C₂.Xbar.Opens} {hV₂B : V₂B ≤ C₂.U} {hne₂B : (V₂B : Set C₂.Xbar).Nonempty}
    [hcV₂B : Fact ((subCurve C₂ V₂B hV₂B hne₂B).U :
        Set (subCurve C₂ V₂B hV₂B hne₂B).Xbar)ᶜ.Nonempty]
    {V₂ : C₂.Xbar.Opens} {hV₂ : V₂ ≤ C₂.U} {hne₂ : (V₂ : Set C₂.Xbar).Nonempty} (hVV₂ : V₂ ≤ V₂B)
    [hcV₂ : Fact ((subCurve C₂ V₂ hV₂ hne₂).U : Set (subCurve C₂ V₂ hV₂ hne₂).Xbar)ᶜ.Nonempty]
    {τB : C.Xbar.functionField} (hτB : Transcendental K τB)
    [IsGalois (K₀ K (coordT τB)) (FFClosure C.Xbar)] (hUB : VB = chartOne K C.Xbar τB)
    {τ₀ : C.Xbar.functionField} (hτ₀ : Transcendental K τ₀)
    [IsGalois (K₀ K (coordT τ₀)) (FFClosure C.Xbar)] (hU₀ : V = chartOne K C.Xbar τ₀)
    {υB : C₂.Xbar.functionField} (hυB : Transcendental K₂ υB)
    [IsGalois (K₀ K₂ (coordT υB)) (FFClosure C₂.Xbar)] (hUυB : V₂B = chartOne K₂ C₂.Xbar υB)
    {υ : C₂.Xbar.functionField} (hυ : Transcendental K₂ υ)
    [IsGalois (K₀ K₂ (coordT υ)) (FFClosure C₂.Xbar)] (hUυ : V₂ = chartOne K₂ C₂.Xbar υ)
    (hF : ∀ x ∈ F (curveGaloisData K hτB), x ∈ F (curveGaloisData K hτ₀))
    (hW : ∀ W : ValuationSubring (FFClosure C.Xbar),
      (∀ c : K, algebraMap K (FFClosure C.Xbar) c ∈ W) → coordT τ₀ ∈ W →
        (∀ c : K, algebraMap K (FFClosure C.Xbar) c ∈ W) ∧ coordT τB ∈ W)
    (hF₂ : ∀ x ∈ F (curveGaloisData K₂ hυB), x ∈ F (curveGaloisData K₂ hυ))
    (hW₂ : ∀ W : ValuationSubring (FFClosure C₂.Xbar),
      (∀ c : K₂, algebraMap K₂ (FFClosure C₂.Xbar) c ∈ W) → coordT υ ∈ W →
        (∀ c : K₂, algebraMap K₂ (FFClosure C₂.Xbar) c ∈ W) ∧ coordT υB ∈ W)
    (φ : (arithmeticExt Ω (subCurve C V hV hne) hcV.out).Pi ≃ₜ*
      (arithmeticExt Ω₂ (subCurve C₂ V₂ hV₂ hne₂) hcV₂.out).Pi)
    (φB : (arithmeticExt Ω (subCurve C VB hVB hneB) hcVB.out).Pi ≃ₜ*
      (arithmeticExt Ω₂ (subCurve C₂ V₂B hV₂B hne₂B) hcV₂B.out).Pi)
    (α₁ : fiber (basePoint Ω (subCurve C VB hVB hneB) hcVB.out) ≅
      fiber (fillPoint Ω (subCurve (subCurve C VB hVB hneB) V hVV hne) hcV.out hVV))
    (α₂ : fiber (basePoint Ω₂ (subCurve C₂ V₂B hV₂B hne₂B) hcV₂B.out) ≅
      fiber (fillPoint Ω₂ (subCurve (subCurve C₂ V₂B hV₂B hne₂B) V₂ hVV₂ hne₂) hcV₂.out hVV₂))
    (hL3 : ∃ m₀, ∀ y, cor38Fill Ω₂ (subCurve C₂ V₂B hV₂B hne₂B) hcV₂B.out V₂ hVV₂ hne₂ α₂ (φ y) =
      m₀ * φB (cor38Fill Ω (subCurve C VB hVB hneB) hcVB.out V hVV hne α₁ y) * m₀⁻¹) :
    ∃ m, ∀ x, piT (curveGaloisData K₂ hυB) (curveGaloisData K₂ hυ) hF₂ hW₂
        (curveGaloisData_H_le K₂ hυB) (galLift hτ₀ hU₀ hυ hUυ φ x) =
      m * galLift hτB hUB hυB hUυB φB (piT (curveGaloisData K hτB) (curveGaloisData K hτ₀) hF hW
        (curveGaloisData_H_le K hτB) x) * m⁻¹ := by
  obtain ⟨c, hcc⟩ := exists_cor38Fill_piBridge (C := subCurve C VB hVB hneB) (hc := hcVB)
    (hV := hVV) (hcV := hcV) hτ₀ hU₀ hτB hUB hF hW α₁
  obtain ⟨c₂, hcc₂⟩ := exists_cor38Fill_piBridge (C := subCurve C₂ V₂B hV₂B hne₂B) (hc := hcV₂B)
    (hV := hVV₂) (hcV := hcV₂) hυ hUυ hυB hUυB hF₂ hW₂ α₂
  obtain ⟨m₀, hm₀⟩ := hL3
  refine ⟨(piBridge (Ω := Ω₂) (C := subCurve C₂ V₂B hV₂B hne₂B) hυB hUυB).symm
    (c₂⁻¹ * m₀ * φB c), fun x => ?_⟩
  apply (piBridge (Ω := Ω₂) (C := subCurve C₂ V₂B hV₂B hne₂B) hυB hUυB).injective
  have k1 := hcc₂ (galLift hτ₀ hU₀ hυ hUυ φ x)
  have k2 : piBridge (Ω := Ω₂) (C := subCurve C₂ V₂ hV₂ hne₂) hυ hUυ
      (galLift hτ₀ hU₀ hυ hUυ φ x) = φ (piBridge (Ω := Ω) (C := subCurve C V hV hne) hτ₀ hU₀ x) :=
    piBridge_galLift hτ₀ hU₀ hυ hUυ φ x
  have k3 := hcc x
  have k4 := hm₀ (piBridge (Ω := Ω) (C := subCurve C V hV hne) hτ₀ hU₀ x)
  change cor38Fill Ω₂ (subCurve C₂ V₂B hV₂B hne₂B) hcV₂B.out V₂ hVV₂ hne₂ α₂
      (piBridge (Ω := Ω₂) (C := subCurve C₂ V₂ hV₂ hne₂) hυ hUυ (galLift hτ₀ hU₀ hυ hUυ φ x)) =
    c₂ * _ * c₂⁻¹ at k1
  change cor38Fill Ω (subCurve C VB hVB hneB) hcVB.out V hVV hne α₁
      (piBridge (Ω := Ω) (C := subCurve C V hV hne) hτ₀ hU₀ x) = c * _ * c⁻¹ at k3
  rw [k2, k4, k3] at k1
  have k5 : piBridge (Ω := Ω₂) (C := subCurve C₂ V₂B hV₂B hne₂B) hυB hUυB
      (piT (curveGaloisData K₂ hυB) (curveGaloisData K₂ hυ) hF₂ hW₂
        (curveGaloisData_H_le K₂ hυB) (galLift hτ₀ hU₀ hυ hUυ φ x)) =
      c₂⁻¹ * (m₀ * φB (c * piBridge (Ω := Ω) (C := subCurve C VB hVB hneB) hτB hUB
        (piT (curveGaloisData K hτB) (curveGaloisData K hτ₀) hF hW (curveGaloisData_H_le K hτB) x) *
          c⁻¹) * m₀⁻¹) * c₂ := by
    rw [show m₀ * φB (c * piBridge (Ω := Ω) (C := subCurve C VB hVB hneB) hτB hUB
        (piT (curveGaloisData K hτB) (curveGaloisData K hτ₀) hF hW (curveGaloisData_H_le K hτB) x) *
          c⁻¹) * m₀⁻¹ = c₂ * piBridge (Ω := Ω₂) (C := subCurve C₂ V₂B hV₂B hne₂B) hυB hUυB
        (piT (curveGaloisData K₂ hυB) (curveGaloisData K₂ hυ) hF₂ hW₂
          (curveGaloisData_H_le K₂ hυB) (galLift hτ₀ hU₀ hυ hUυ φ x)) * c₂⁻¹ from k1]
    group
  rw [k5]
  simp only [map_mul, map_inv, ContinuousMulEquiv.apply_symm_apply, piBridge_galLift]
  group

end GalConj

section Central

variable {K : Type u} [Field K] [NumberField K] {Ω : Type u} [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] {C : HypCurve K}
  [hc : Fact (C.U : Set C.Xbar)ᶜ.Nonempty]
  {K₂ : Type u} [Field K₂] [NumberField K₂] {Ω₂ : Type u} [Field Ω₂] [Algebra K₂ Ω₂]
  [IsAlgClosed Ω₂] [Algebra.IsAlgebraic K₂ Ω₂] [CharZero Ω₂] {C₂ : HypCurve K₂}
  [hc₂ : Fact (C₂.U : Set C₂.Xbar)ᶜ.Nonempty]

attribute [local instance] isIntegral_Xbar nonempty_U algFF isAlgClosure_of_isAlgebraic

variable {τ : C.Xbar.functionField} (hτ : Transcendental K τ)
  [IsGalois (K₀ K (coordT τ)) (FFClosure C.Xbar)] (hU : C.U = chartOne K C.Xbar τ)
  {τ₂ : C₂.Xbar.functionField} (hτ₂ : Transcendental K₂ τ₂)
  [IsGalois (K₀ K₂ (coordT τ₂)) (FFClosure C₂.Xbar)] (hU₂ : C₂.U = chartOne K₂ C₂.Xbar τ₂)
  (Φ : (arithmeticExt Ω C hc.out).Iso (arithmeticExt Ω₂ C₂ hc₂.out))
  {V : C.Xbar.Opens} {hV : V ≤ C.U} {hne : (V : Set C.Xbar).Nonempty}
  [hcV : Fact ((subCurve C V hV hne).U : Set (subCurve C V hV hne).Xbar)ᶜ.Nonempty]
  {τB : C.Xbar.functionField} (hτB : Transcendental K τB)
  [IsGalois (K₀ K (coordT τB)) (FFClosure C.Xbar)]
  {τ₀ : C.Xbar.functionField} (hτ₀ : Transcendental K τ₀)
  [IsGalois (K₀ K (coordT τ₀)) (FFClosure C.Xbar)] (hU₀ : V = chartOne K C.Xbar τ₀)
  {υB : C₂.Xbar.functionField} (hυB : Transcendental K₂ υB)
  [IsGalois (K₀ K₂ (coordT υB)) (FFClosure C₂.Xbar)]
  {υ : C₂.Xbar.functionField} (hυ : Transcendental K₂ υ)
  [IsGalois (K₀ K₂ (coordT υ)) (FFClosure C₂.Xbar)]
  (hFU0 : ∀ x ∈ F (curveGaloisData K hτ), x ∈ F (curveGaloisData K hτ₀))
  (hWU0 : ∀ W : ValuationSubring (FFClosure C.Xbar),
    (∀ c : K, algebraMap K (FFClosure C.Xbar) c ∈ W) → coordT τ₀ ∈ W →
      (∀ c : K, algebraMap K (FFClosure C.Xbar) c ∈ W) ∧ coordT τ ∈ W)
  (hFUB : ∀ x ∈ F (curveGaloisData K hτ), x ∈ F (curveGaloisData K hτB))
  (hWUB : ∀ W : ValuationSubring (FFClosure C.Xbar),
    (∀ c : K, algebraMap K (FFClosure C.Xbar) c ∈ W) → coordT τB ∈ W →
      (∀ c : K, algebraMap K (FFClosure C.Xbar) c ∈ W) ∧ coordT τ ∈ W)
  (hFB0 : ∀ x ∈ F (curveGaloisData K hτB), x ∈ F (curveGaloisData K hτ₀))
  (hWB0 : ∀ W : ValuationSubring (FFClosure C.Xbar),
    (∀ c : K, algebraMap K (FFClosure C.Xbar) c ∈ W) → coordT τ₀ ∈ W →
      (∀ c : K, algebraMap K (FFClosure C.Xbar) c ∈ W) ∧ coordT τB ∈ W)
  (hFU0₂ : ∀ x ∈ F (curveGaloisData K₂ hτ₂), x ∈ F (curveGaloisData K₂ hυ))
  (hWU0₂ : ∀ W : ValuationSubring (FFClosure C₂.Xbar),
    (∀ c : K₂, algebraMap K₂ (FFClosure C₂.Xbar) c ∈ W) → coordT υ ∈ W →
      (∀ c : K₂, algebraMap K₂ (FFClosure C₂.Xbar) c ∈ W) ∧ coordT τ₂ ∈ W)
  (hFUB₂ : ∀ x ∈ F (curveGaloisData K₂ hτ₂), x ∈ F (curveGaloisData K₂ hυB))
  (hWUB₂ : ∀ W : ValuationSubring (FFClosure C₂.Xbar),
    (∀ c : K₂, algebraMap K₂ (FFClosure C₂.Xbar) c ∈ W) → coordT υB ∈ W →
      (∀ c : K₂, algebraMap K₂ (FFClosure C₂.Xbar) c ∈ W) ∧ coordT τ₂ ∈ W)
  (hFB0₂ : ∀ x ∈ F (curveGaloisData K₂ hυB), x ∈ F (curveGaloisData K₂ hυ))
  (hWB0₂ : ∀ W : ValuationSubring (FFClosure C₂.Xbar),
    (∀ c : K₂, algebraMap K₂ (FFClosure C₂.Xbar) c ∈ W) → coordT υ ∈ W →
      (∀ c : K₂, algebraMap K₂ (FFClosure C₂.Xbar) c ∈ W) ∧ coordT υB ∈ W)

set_option maxHeartbeats 1600000 in
-- the quotients `Π_U`, `Π_V` are slow for unification
set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_V` are found slowly
include hτ₀ hU₀ hFU0 hWU0 hcV in
/-- **The comparison element is geometric**: if normalised lifts `e` on `V ⊆ V♮` and `e♮` on `V♮`
(`piT' ∘ e = bridgeIso Φ ∘ piT`) satisfy `piT' ∘ e = conj m ∘ e♮ ∘ piT`, then the image of `m` in
`Π_{U'}` is central, so `pr(m) = 1` (`G_{K'}` is slim, curves-jacobian `isSlim_Gk`). -/
theorem piToGk_eq_one_of_conj
    {e : Pi (curveGaloisData K hτ₀) ≃ₜ* Pi (curveGaloisData K₂ hυ)}
    {eB : Pi (curveGaloisData K hτB) ≃ₜ* Pi (curveGaloisData K₂ hυB)}
    (he : ∀ x, piT (curveGaloisData K₂ hτ₂) (curveGaloisData K₂ hυ) hFU0₂ hWU0₂
          (curveGaloisData_H_le K₂ hτ₂) (e x) =
        bridgeIso hτ hU hτ₂ hU₂ Φ (piT (curveGaloisData K hτ) (curveGaloisData K hτ₀) hFU0 hWU0
          (curveGaloisData_H_le K hτ) x))
    (heB : ∀ x, piT (curveGaloisData K₂ hτ₂) (curveGaloisData K₂ hυB) hFUB₂ hWUB₂
          (curveGaloisData_H_le K₂ hτ₂) (eB x) =
        bridgeIso hτ hU hτ₂ hU₂ Φ (piT (curveGaloisData K hτ) (curveGaloisData K hτB) hFUB hWUB
          (curveGaloisData_H_le K hτ) x))
    {m : Pi (curveGaloisData K₂ hυB)}
    (hm : ∀ x, piT (curveGaloisData K₂ hυB) (curveGaloisData K₂ hυ) hFB0₂ hWB0₂
          (curveGaloisData_H_le K₂ hυB) (e x) =
        m * eB (piT (curveGaloisData K hτB) (curveGaloisData K hτ₀) hFB0 hWB0
          (curveGaloisData_H_le K hτB) x) * m⁻¹) :
    piToGk (curveGaloisData K₂ hυB) m = 1 := by
  obtain ⟨n, hn_def⟩ : ∃ n, n = piT (curveGaloisData K₂ hτ₂) (curveGaloisData K₂ hυB) hFUB₂
      hWUB₂ (curveGaloisData_H_le K₂ hτ₂) m := ⟨_, rfl⟩
  have hn : ∀ y, n * y = y * n := by
    intro y
    obtain ⟨z, rfl⟩ := (bridgeIso hτ hU hτ₂ hU₂ Φ).surjective y
    obtain ⟨x, rfl⟩ := piT_surjective_curve Ω hτ₀ hU₀ hτ hU hFU0 hWU0 z
    have h1 := congrArg (piT (curveGaloisData K₂ hτ₂) (curveGaloisData K₂ hυB) hFUB₂ hWUB₂
      (curveGaloisData_H_le K₂ hτ₂)) (hm x)
    rw [piT_piT (hF₁₃ := hFU0₂) (hW₁₃ := hWU0₂), he, map_mul, map_mul, map_inv, heB,
      piT_piT (hF₁₃ := hFU0) (hW₁₃ := hWU0), ← hn_def] at h1
    calc n * _ = (n * bridgeIso hτ hU hτ₂ hU₂ Φ (piT (curveGaloisData K hτ)
          (curveGaloisData K hτ₀) hFU0 hWU0 (curveGaloisData_H_le K hτ) x) * n⁻¹) * n := by
          group
      _ = _ := by rw [← h1]
  have hg : ∀ g, piToGk (curveGaloisData K₂ hτ₂) n * g = g * piToGk (curveGaloisData K₂ hτ₂) n := by
    intro g
    obtain ⟨y, rfl⟩ := piToGk_surjective_curve hτ₂ g
    rw [← map_mul, ← map_mul, hn]
  have hz : gkBridge (Ω := Ω₂) hτ₂ hU₂ (piToGk (curveGaloisData K₂ hτ₂) n) = 1 := by
    have hcen := (isSlim_Gk (K := K₂) (Ω := Ω₂)).center_eq_bot
    have hmem : gkBridge (Ω := Ω₂) hτ₂ hU₂ (piToGk (curveGaloisData K₂ hτ₂) n) ∈
        Subgroup.center _ := Subgroup.mem_center_iff.2 fun g => by
      obtain ⟨g', rfl⟩ := (gkBridge (Ω := Ω₂) hτ₂ hU₂).surjective g
      rw [← map_mul, ← map_mul, hg]
    rw [hcen] at hmem
    exact Subgroup.mem_bot.1 hmem
  have hz' : piToGk (curveGaloisData K₂ hτ₂) n = 1 := by
    rw [← map_one (gkBridge (Ω := Ω₂) hτ₂ hU₂)] at hz
    exact (gkBridge (Ω := Ω₂) hτ₂ hU₂).injective hz
  rw [← piToGk_piT (curveGaloisData K₂ hτ₂) (curveGaloisData K₂ hυB) hFUB₂ hWUB₂
    (curveGaloisData_H_le K₂ hτ₂), ← hn_def, hz']

end Central

end Iut.Reconstruction
