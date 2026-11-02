/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Thm19.MatchPoint

/-!
# Points of `Z_NF` with the same valuations along `Φ` (MR9 item 4, step 5)

* `kummerNFRangeEquiv`: the restriction of `h1LimCycloEquiv` to `kummerNFRange`
  (`map_kummerNFRange_h1LimCycloEquiv`);
* **`exists_val_kummerNFRangeEquiv`**: for every point `x` of `Z_NF` there is a point `x''` of
  `Z'_NF` with `ord_{x''} ∘ φ = ord_x` (`exists_ratCusp_nfPlace`, `exists_map_inertiaH_constIso`,
  `val_eq_of_matched`); **`exists_val_kummerNFRangeEquiv_symm`**: the same for `φ⁻¹` (lift data of
  `Φ.symm`, `(cycloIso Φ).symm`, `tameBridge_cycloIso_symm`).
-/

open CategoryTheory AlgebraicGeometry Pi1 Pi1.Orbifold KummerTheory KummerTheory.Curve
  AffOrbicurve WeilCurves.FunctionField CurvesJacobian CurvesJacobian.Kummer CurvesJacobian.Cusp
  CurvesJacobian.LocAn Belyi Belyi.Anabelian

universe u

noncomputable section

namespace Iut.Reconstruction

open Thm19

set_option linter.unusedSectionVars false

section Lift

variable {K : Type u} [Field K] [NumberField K] {Ω : Type u} [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] {C : HypCurve K}
  [hc : Fact (C.U : Set C.Xbar)ᶜ.Nonempty]
  {K₂ : Type u} [Field K₂] [NumberField K₂] {Ω₂ : Type u} [Field Ω₂] [Algebra K₂ Ω₂]
  [IsAlgClosed Ω₂] [Algebra.IsAlgebraic K₂ Ω₂] [CharZero Ω₂] {C₂ : HypCurve K₂}
  [hc₂ : Fact (C₂.U : Set C₂.Xbar)ᶜ.Nonempty]

attribute [local instance] isIntegral_Xbar nonempty_U algFF isAlgClosure_of_isAlgebraic

variable {τ : C.Xbar.functionField} {hτ : Transcendental K τ}
  [IsGalois (K₀ K (coordT τ)) (FFClosure C.Xbar)] {hU : C.U = chartOne K C.Xbar τ}
  {τ₂ : C₂.Xbar.functionField} {hτ₂ : Transcendental K₂ τ₂}
  [IsGalois (K₀ K₂ (coordT τ₂)) (FFClosure C₂.Xbar)] {hU₂ : C₂.U = chartOne K₂ C₂.Xbar τ₂}
  {Φ : (arithmeticExt Ω C hc.out).Iso (arithmeticExt Ω₂ C₂ hc₂.out)}

variable [Fact (0 < (CurvesJacobian.curveGenus K C.Xbar).toNat)]
  [Fact (0 < (CurvesJacobian.curveGenus K₂ C₂.Xbar).toNat)]
  [CharZero (FFClosure C.Xbar)] [CharZero (FFClosure C₂.Xbar)]


attribute [local instance] Thm19.isAlgClosed_algebraicClosure Thm19.isFunctionField_fnf

variable (hS : BelyiCuspSpec Ω C hc.out) (hS₂ : BelyiCuspSpec Ω₂ C₂ hc₂.out)
  (σ₀ : Spec (CommRingCat.of K) ⟶ C.Xbar)
  (hσ₀ : σ₀ ≫ (C.Xbar ↘ Spec (CommRingCat.of K)) = 𝟙 (Spec (CommRingCat.of K)))
  (hg : CurvesJacobian.curveGenus K C.Xbar ≠ 0)
  (σ₂ : Spec (CommRingCat.of K₂) ⟶ C₂.Xbar)
  (hσ₂ : σ₂ ≫ (C₂.Xbar ↘ Spec (CommRingCat.of K₂)) = 𝟙 (Spec (CommRingCat.of K₂)))
  (hg₂ : CurvesJacobian.curveGenus K₂ C₂.Xbar ≠ 0)
  (hDGC : RelIsomDGC.Exists K₂) (hDGC₁ : RelIsomDGC.Exists K)
  (N : NFModel (curveGaloisData K hτ)) (N₂ : NFModel (curveGaloisData K₂ hτ₂))

variable (hτ hU hτ₂ hU₂ Φ) in
/-- **The restriction of `h1LimCycloEquiv` to the Kummer classes** `K^×_{Z_NF} ≅ K'^×_{Z'_NF}`
(`map_kummerNFRange_h1LimCycloEquiv`). -/
def kummerNFRangeEquiv :
    kummerNFRange N (mem_range_of_isAlgebraic_F K hτ) ≃*
      kummerNFRange N₂ (mem_range_of_isAlgebraic_F K₂ hτ₂) :=
  ((h1LimCycloEquiv hτ hU hτ₂ hU₂ Φ hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hDGC₁).subgroupMap
    (kummerNFRange N (mem_range_of_isAlgebraic_F K hτ))).trans
    (MulEquiv.subgroupCongr
      (map_kummerNFRange_h1LimCycloEquiv hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hDGC₁ N N₂))

lemma coe_kummerNFRangeEquiv (ξ : kummerNFRange N (mem_range_of_isAlgebraic_F K hτ)) :
    ((kummerNFRangeEquiv hτ hU hτ₂ hU₂ Φ hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hDGC₁ N N₂ ξ :
      kummerNFRange N₂ (mem_range_of_isAlgebraic_F K₂ hτ₂)) : H1Lim (curveGaloisData K₂ hτ₂)) =
      h1LimCycloEquiv hτ hU hτ₂ hU₂ Φ hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hDGC₁ ξ := rfl

set_option maxHeartbeats 1600000 in
-- the quotients `Π_V` and the classes at several stages unify slowly
set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_V` and their actions are found slowly
/-- **Every point of `Z_NF` has a partner in `Z'_NF` with the same valuations along `φ`**
(`exists_ratCusp_nfPlace`, the matched cusp `exists_map_inertiaH_constIso`, `val_eq_of_matched` for
`h1LimCycloEquiv`). -/
theorem exists_val_kummerNFRangeEquiv
    (P : Place (algebraicClosure ℚ (FFClosure C.Xbar)) (fnf N)) :
    ∃ P₂ : Place (algebraicClosure ℚ (FFClosure C₂.Xbar)) (fnf N₂),
      ∀ ξ : (recTriple N (mem_range_of_isAlgebraic_F K hτ)).G,
        (recTriple N₂ (mem_range_of_isAlgebraic_F K₂ hτ₂)).val P₂
          (kummerNFRangeEquiv hτ hU hτ₂ hU₂ Φ hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hDGC₁ N N₂ ξ) =
        (recTriple N (mem_range_of_isAlgebraic_F K hτ)).val P ξ := by
  obtain ⟨g₀, x, hx, hk, hW, rfl⟩ := exists_ratCusp_nfPlace N P
  obtain ⟨L₀⟩ := LiftData.nonempty (hτ₂ := hτ₂) (hU₂ := hU₂) (Φ := Φ) (hU := hU) hS g₀
  obtain ⟨W'', hW'', hI⟩ := L₀.exists_map_inertiaH_constIso x.A hx
  have hk'' : ∀ c : K₂, algebraMap K₂ (FFClosure C₂.Xbar) c ∈ W'' := fun c => by
    rw [IsScalarTower.algebraMap_apply K₂ L₀.tgt.K (FFClosure C₂.Xbar)]
    exact hW''.1 _
  have hW''N : N₂.IsNFPoint W'' :=
    ⟨coordT L₀.υ, (NFModel.mem_FNF_iff_numberField N₂ _).2
      (mem_F_baseChange_of_stage L₀.tgt.toStage (GStage.F_toStage _ _ (tF L₀.tgt.data).2)),
      hW''.2⟩
  exact ⟨nfPlace hk'' hW''N, fun ξ => val_eq_of_matched (cycloIso hτ hU hτ₂ hU₂ Φ)
    (cycloIso_smul hτ hU hτ₂ hU₂ Φ) σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC N N₂ hS
    (fun _ L => L.tameCompat_cycloIso)
    (h1LimCycloEquiv hτ hU hτ₂ hU₂ Φ hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hDGC₁).toMonoidHom
    (fun g y => h1LimCycloEquiv_ofG hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hDGC₁ g y) L₀ x hx hk hW
    W'' hW'' hI hk'' hW''N ξ
    (kummerNFRangeEquiv hτ hU hτ₂ hU₂ Φ hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hDGC₁ N N₂ ξ).2⟩

lemma coe_kummerNFRangeEquiv_symm (ξ₂ : kummerNFRange N₂ (mem_range_of_isAlgebraic_F K₂ hτ₂)) :
    (((kummerNFRangeEquiv hτ hU hτ₂ hU₂ Φ hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hDGC₁ N N₂).symm ξ₂ :
      kummerNFRange N (mem_range_of_isAlgebraic_F K hτ)) : H1Lim (curveGaloisData K hτ)) =
      (h1LimCycloEquiv hτ hU hτ₂ hU₂ Φ hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hDGC₁).symm ξ₂.1 := by
  apply (h1LimCycloEquiv hτ hU hτ₂ hU₂ Φ hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hDGC₁).injective
  rw [MulEquiv.apply_symm_apply, ← coe_kummerNFRangeEquiv, MulEquiv.apply_symm_apply]

set_option maxHeartbeats 1600000 in
-- the quotients `Π_V` and the classes at several stages unify slowly
set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_V` and their actions are found slowly
/-- **Every point of `Z'_NF` has a partner in `Z_NF` with the same valuations along `φ⁻¹`**
(`val_eq_of_matched` for the inverse of `h1LimCycloEquiv`: lift data of `Φ.symm`,
`(cycloIso Φ).symm`, `tameBridge_cycloIso_symm`). -/
theorem exists_val_kummerNFRangeEquiv_symm
    (P₂ : Place (algebraicClosure ℚ (FFClosure C₂.Xbar)) (fnf N₂)) :
    ∃ P : Place (algebraicClosure ℚ (FFClosure C.Xbar)) (fnf N),
      ∀ ξ₂ : (recTriple N₂ (mem_range_of_isAlgebraic_F K₂ hτ₂)).G,
        (recTriple N (mem_range_of_isAlgebraic_F K hτ)).val P
          ((kummerNFRangeEquiv hτ hU hτ₂ hU₂ Φ hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hDGC₁ N
            N₂).symm ξ₂) =
        (recTriple N₂ (mem_range_of_isAlgebraic_F K₂ hτ₂)).val P₂ ξ₂ := by
  obtain ⟨g₀, x, hx, hk, hW, rfl⟩ := exists_ratCusp_nfPlace N₂ P₂
  obtain ⟨L₀⟩ := LiftData.nonempty (hτ := hτ₂) (hU := hU₂) (hτ₂ := hτ) (hU₂ := hU)
    (Φ := Φ.symm) hS₂ g₀
  obtain ⟨W'', hW'', hI⟩ := L₀.exists_map_inertiaH_constIso x.A hx
  have hk'' : ∀ c : K, algebraMap K (FFClosure C.Xbar) c ∈ W'' := fun c => by
    rw [IsScalarTower.algebraMap_apply K L₀.tgt.K (FFClosure C.Xbar)]
    exact hW''.1 _
  have hW''N : N.IsNFPoint W'' :=
    ⟨coordT L₀.υ, (NFModel.mem_FNF_iff_numberField N _).2
      (mem_F_baseChange_of_stage L₀.tgt.toStage (GStage.F_toStage _ _ (tF L₀.tgt.data).2)),
      hW''.2⟩
  refine ⟨nfPlace hk'' hW''N, fun ξ₂ => ?_⟩
  have hmem : (h1LimCycloEquiv hτ hU hτ₂ hU₂ Φ hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hDGC₁).symm ξ₂.1 ∈
      kummerNFRange N (mem_range_of_isAlgebraic_F K hτ) :=
    coe_kummerNFRangeEquiv_symm hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hDGC₁ N N₂ ξ₂ ▸
      ((kummerNFRangeEquiv hτ hU hτ₂ hU₂ Φ hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hDGC₁ N N₂).symm ξ₂).2
  have h := val_eq_of_matched (cycloIso hτ hU hτ₂ hU₂ Φ).symm
    (symm_smul_of_smul _ (cycloIso_smul hτ hU hτ₂ hU₂ Φ)) σ₂ hσ₂ hg₂ σ₀ hσ₀ hg hDGC₁ N₂ N hS₂
    (fun _ L => L.tameCompat_of_tameBridge _ (tameBridge_cycloIso_symm hτ hU hτ₂ hU₂ Φ))
    (h1LimCycloEquiv hτ hU hτ₂ hU₂ Φ hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hDGC₁).symm.toMonoidHom
    (fun g y => h1LimEquiv_symm_ofG (cycloIso hτ hU hτ₂ hU₂ Φ) (cycloIso_smul hτ hU hτ₂ hU₂ Φ) hS
      σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hS₂ hDGC hDGC₁ g y) L₀ x hx hk hW W'' hW'' hI hk'' hW''N ξ₂ hmem
  exact (congrArg ((recTriple N (mem_range_of_isAlgebraic_F K hτ)).val (nfPlace hk'' hW''N))
    (Subtype.ext (coe_kummerNFRangeEquiv_symm hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hDGC₁ N N₂
      ξ₂))).trans h

end Lift

end Iut.Reconstruction
