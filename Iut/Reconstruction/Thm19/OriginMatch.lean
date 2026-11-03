/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Thm19.NFConstEquiv
import Iut.Reconstruction.Thm19.EllipticNF
import Iut.Reconstruction.Thm19.PlaceConj
import Iut.Reconstruction.Thm19.SyncStage
import CurvesJacobian.CuspChar.TwoCusps
import CurvesJacobian.Cusp.FillElemOp
import CurvesJacobian.Cusp.EllipticGenusOne

/-!
# The bijection of points of Thm 1.9 maps cusps to cusps (MR9, `CKSemiAbsConj` item 5 (a))

The bijection `nfPlaceEquiv` of the points of `Z_NF` and `Z'_NF` underlying `nfRingEquiv`
([AbsTopIII] Thm 1.9, `Topics in Absolute Anabelian Geometry III.txt` l.2109–2199) sends a point
`x` (a rational cusp `W` of a stage `V ⊆ U`) to the cusp `W''` of the target stage `V''` whose
inertia group is the image of that of `W` (`exists_val_kummerNFRangeEquiv`). If `x` is a cusp of
`U` (`t ∉ W`), its inertia group in `Π_U` is a cuspidal inertia group of curves-jacobian's
`arithmeticExt` (`mem_cusps_iff_piBridge`); if these are nontrivial, the lift data square
`piT₂ ∘ e = bridgeIso Φ ∘ piT` (`LiftData.he`) shows that the inertia group of `W''` in `Π_{U'}`
is nontrivial, so `W''` is a cusp of `U'` (`inertiaPi_eq_bot_of_mem`):

* `geomCusps_ne_bot_of_card_eq_one`, `arithCusps_ne_bot_of_card_eq_one`,
  **`cusps_ne_bot_hypCurveE`**: for one cusp and genus `≥ 1` the cuspidal inertia groups are
  nontrivial (curves-jacobian `cuspInertia_ne_bot_of_card_eq_one`), e.g. for `E ∖ {O}`;
* `tNF`: the coordinate `t` as an NF-rational function;
* **`not_mem_nfPlaceEquiv`**: if `t ∉ P`, then `t' ∉ nfPlaceEquiv P`.
-/

open CategoryTheory AlgebraicGeometry Pi1 Pi1.Orbifold KummerTheory KummerTheory.Curve
  AffOrbicurve WeilCurves.FunctionField CurvesJacobian CurvesJacobian.Kummer CurvesJacobian.Cusp
  CurvesJacobian.LocAn Belyi Belyi.Anabelian

universe u

noncomputable section

namespace Iut.Reconstruction.Thm19

/-! ### One cusp: `E ∖ {O}` -/

section OneCusp

variable {K : Type u} [Field K] [CharZero K] (Ω : Type u) [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] (C : HypCurve K)
  (hc : (C.U : Set C.Xbar)ᶜ.Nonempty)

attribute [local instance] isAlgClosure_of_isAlgebraic

omit [Algebra.IsAlgebraic K Ω] [CharZero K] in
/-- **The cuspidal inertia groups of `π₁ᵉᵗ(U_Ω)` are nontrivial** if `U_Ω` has one cusp and
genus `≥ 1` (curves-jacobian `cuspInertia_ne_bot_of_card_eq_one`). -/
lemma geomCusps_ne_bot_of_card_eq_one
    (h1 : Nat.card ((geomOpen Ω C : Set (geomCurve Ω C))ᶜ : Set (geomCurve Ω C)) = 1)
    (hg : 0 < (CurvesJacobian.curveGenus Ω (geomCurve Ω C)).toNat)
    {I₀} (hI₀ : I₀ ∈ geomCusps Ω C) : I₀ ≠ ⊥ := by
  obtain ⟨W, hkW, hWU, rfl⟩ := hI₀
  exact CuspChar.cuspInertia_ne_bot_of_card_eq_one (geomData Ω C) (geomCurve Ω C)
    (curveEquivL Ω (transcendental_geomCoord Ω C)) (curveGaloisData_H_le Ω _)
    (curveEquivL_algebraMap Ω _) (curveEquivL_τ Ω _)
    (compl_finite_baseChangeOpen K Ω C.nonempty) h1 hg hkW hWU

/-- **The cuspidal inertia groups of `Π_U` are nontrivial** if `U_Ω` has one cusp and genus
`≥ 1`. -/
theorem arithCusps_ne_bot_of_card_eq_one
    (h1 : Nat.card ((geomOpen Ω C : Set (geomCurve Ω C))ᶜ : Set (geomCurve Ω C)) = 1)
    (hg : 0 < (CurvesJacobian.curveGenus Ω (geomCurve Ω C)).toNat)
    {I} (hI : I ∈ arithCusps Ω C hc) : I ≠ ⊥ := by
  obtain ⟨I₀, hI₀, g, rfl⟩ := hI
  have hψ : Function.Injective ((MulAut.conj g).toMonoidHom.comp (geomToPi Ω C hc)) :=
    (MulAut.conj g).injective.comp (geomToPi_injective Ω C hc)
  rw [Subgroup.map_map, Ne, Subgroup.map_eq_bot_iff_of_injective _ hψ]
  exact geomCusps_ne_bot_of_card_eq_one Ω C h1 hg hI₀

/-- **The cuspidal inertia group of `Π_{E ∖ {O}}` is nontrivial.** -/
theorem cusps_ne_bot_hypCurveE [NumberField K] (E : WeierstrassCurve K) [E.IsElliptic]
    (hc : ((hypCurveE E).U : Set (hypCurveE E).Xbar)ᶜ.Nonempty)
    {I} (hI : I ∈ (arithmeticExt Ω (hypCurveE E) hc).cusps) : I ≠ ⊥ := by
  refine arithCusps_ne_bot_of_card_eq_one Ω (hypCurveE E) hc
    (card_compl_baseChangeOpen_XE E Ω) ?_ hI
  have := curveGenus_baseChange_curveE E Ω
  change 0 < (CurvesJacobian.curveGenus Ω (baseChange K Ω (curveE E))).toNat
  omega

end OneCusp

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

variable (hτ) in
/-- The coordinate `t = τ` as an NF-rational function. -/
def tNF (M : NFModel (curveGaloisData K hτ)) : fnf M :=
  ⟨coordT τ, (NFModel.mem_FNF_iff_numberField M _).2
    (tF (baseChange (curveGaloisData K hτ))).2⟩

set_option maxHeartbeats 3200000 in
-- the lift data, the stages and the colimits unify slowly
set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_V` are found slowly
/-- **The bijection of points maps cusps of `U` to cusps of `U'`**, provided the cuspidal inertia
groups of `Π_U` are nontrivial (`hcusp`). -/
theorem not_mem_nfPlaceEquiv
    (hcusp : ∀ I ∈ (arithmeticExt Ω C hc.out).cusps, I ≠ ⊥)
    (P : Place (algebraicClosure ℚ (FFClosure C.Xbar)) (fnf N)) (hP : tNF hτ N ∉ P.1) :
    tNF hτ₂ N₂ ∉ (nfPlaceEquiv hτ hU hτ₂ hU₂ Φ hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hDGC₁ N N₂
      P).1 := by
  obtain ⟨g₀, x, hx, hk, hW, rfl⟩ := exists_ratCusp_nfPlace N P
  obtain ⟨L₀⟩ := LiftData.nonempty (hτ₂ := hτ₂) (hU₂ := hU₂) (Φ := Φ) (hU := hU) hS g₀
  have hx₀ := mem_CuspW_of_constExt g₀.K hx
  obtain ⟨W'', hW''c, hEq⟩ := L₀.exists_map_inertiaH_e x.A hx₀
  have hI := L₀.map_inertiaH_constIso_of_e x.A hx₀ W'' hW''c hEq
  have hW''C : W'' ∈ CuspW (k := L₀.tgt.K) (t := coordT L₀.υ) := mem_CuspW_constExt _ hW''c
  have hk'' : ∀ c : K₂, algebraMap K₂ (FFClosure C₂.Xbar) c ∈ W'' := hW''c.1
  have hW''N : N₂.IsNFPoint W'' :=
    ⟨coordT L₀.υ, (NFModel.mem_FNF_iff_numberField N₂ _).2
      (mem_F_baseChange_of_stage L₀.tgt.toStage (GStage.F_toStage _ _ (tF L₀.tgt.data).2)),
      hW''C.2⟩
  have hval : ∀ ξ, (recTriple N₂ (mem_range_of_isAlgebraic_F K₂ hτ₂)).val (nfPlace hk'' hW''N)
      (kummerNFRangeEquiv hτ hU hτ₂ hU₂ Φ hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hDGC₁ N N₂ ξ) =
      (recTriple N (mem_range_of_isAlgebraic_F K hτ)).val (nfPlace hk hW) ξ := fun ξ =>
    val_eq_of_matched (cycloIso hτ hU hτ₂ hU₂ Φ)
      (cycloIso_smul hτ hU hτ₂ hU₂ Φ) σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC N N₂ hS
      (fun _ L => L.tameCompat_cycloIso)
      (h1LimCycloEquiv hτ hU hτ₂ hU₂ Φ hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hDGC₁).toMonoidHom
      (fun g y => h1LimCycloEquiv_ofG hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hDGC₁ g y) L₀ x hx hk hW
      W'' hW''C hI hk'' hW''N ξ
      (kummerNFRangeEquiv hτ hU hτ₂ hU₂ Φ hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hDGC₁ N N₂ ξ).2
  have hσ : nfPlaceEquiv hτ hU hτ₂ hU₂ Φ hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hDGC₁ N N₂
      (nfPlace hk hW) = nfPlace hk'' hW''N := by
    refine recTriple_valInjective N₂ (mem_range_of_isAlgebraic_F K₂ hτ₂) _ _ fun ξ₂ => ?_
    obtain ⟨ξ, rfl⟩ := (kummerNFRangeEquiv hτ hU hτ₂ hU₂ Φ hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC
      hDGC₁ N N₂).surjective ξ₂
    rw [hval ξ]
    exact (recTripleIso hτ hU hτ₂ hU₂ Φ hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hDGC₁ N N₂).val_eq
      (nfPlace hk hW) ξ
  rw [hσ]
  intro hmem
  have ht₂ : coordT τ₂ ∈ W'' := hmem
  have htx : coordT τ ∉ x.A := fun h => hP h
  -- the inertia group of `W''` dies in `Π_{U'}`
  have hbot₂ : inertiaPi (curveGaloisData K₂ hτ₂) W'' = ⊥ :=
    inertiaPi_eq_bot_of_mem (curveGaloisData_H_le K₂ hτ₂) hk'' ht₂
  have h₂ := map_piT_inertiaPi (F_cGD hτ₂ L₀.hυ) (F_cGD L₀.hυ hτ₂) (hW_chart L₀.htV)
    (curveGaloisData_H_le K₂ hτ₂) W''
  have h₁ := map_piT_inertiaPi (F_cGD hτ g₀.hτ₀) (F_cGD g₀.hτ₀ hτ) (hW_chart g₀.htV)
    (curveGaloisData_H_le K hτ) x.A
  -- the square `piT₂ ∘ e = bridgeIso ∘ piT`
  have hsq : ((inertiaPi (curveGaloisData K g₀.hτ₀) x.A).map
      (piT (curveGaloisData K hτ) (curveGaloisData K g₀.hτ₀) (F_cGD hτ g₀.hτ₀)
        (hW_chart g₀.htV) (curveGaloisData_H_le K hτ))).map
      (bridgeIso hτ hU hτ₂ hU₂ Φ).toMulEquiv.toMonoidHom =
      ((inertiaPi (curveGaloisData K g₀.hτ₀) x.A).map L₀.e.toMulEquiv.toMonoidHom).map
      (piT (curveGaloisData K₂ hτ₂) (curveGaloisData K₂ L₀.hυ) (F_cGD hτ₂ L₀.hυ)
        (hW_chart L₀.htV) (curveGaloisData_H_le K₂ hτ₂)) := by
    have hcomp : (bridgeIso hτ hU hτ₂ hU₂ Φ).toMulEquiv.toMonoidHom.comp
        (piT (curveGaloisData K hτ) (curveGaloisData K g₀.hτ₀) (F_cGD hτ g₀.hτ₀)
          (hW_chart g₀.htV) (curveGaloisData_H_le K hτ)) =
        (piT (curveGaloisData K₂ hτ₂) (curveGaloisData K₂ L₀.hυ) (F_cGD hτ₂ L₀.hυ)
          (hW_chart L₀.htV) (curveGaloisData_H_le K₂ hτ₂)).comp L₀.e.toMulEquiv.toMonoidHom :=
      MonoidHom.ext fun y => (L₀.he y).symm
    exact (Subgroup.map_map _ _ _).trans ((congrArg
      (fun φ => Subgroup.map φ (inertiaPi (curveGaloisData K g₀.hτ₀) x.A)) hcomp).trans
      (Subgroup.map_map _ _ _).symm)
  rw [h₁, hEq, h₂, hbot₂, Subgroup.map_eq_bot_iff_of_injective _
    (bridgeIso hτ hU hτ₂ hU₂ Φ).injective] at hsq
  -- but it is a cuspidal inertia group of `Π_U`
  have hcu := (mem_cusps_iff_piBridge (Ω := Ω) hτ hU _).2
    ⟨x.A, (isCuspPlace_comap_iff (Ω := Ω) hτ hU x.A).2 ⟨hk, htx⟩, rfl⟩
  refine hcusp _ hcu ?_
  change (inertiaPi (curveGaloisData K hτ) x.A).map _ = ⊥
  rw [hsq, Subgroup.map_bot]

end Lift

end Iut.Reconstruction.Thm19
